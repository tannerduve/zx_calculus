import Lean.Data.Json
import ZxCalculus.AST

/-!
# QGraph Parser

Parses Quantomatic `.qgraph` JSON format (PyZX's native serialization)
and reconstructs ZX diagrams as `ZxTerm n m`.

## Format

PyZX exports graphs via `g.to_json()` in the Quantomatic `.qgraph` format.

Example .qgraph structure:
```json
{
  "version": 2,
  "backend": "simple",
  "inputs": [0, 1],
  "outputs": [5, 6],
  "vertices": [
    {"id": 0, "t": 0, "pos": [0, 0]},  // t=0: boundary
    {"id": 2, "t": 1, "pos": [1, 0], "phase": "0"},  // t=1: Z spider
    {"id": 3, "t": 2, "pos": [2, 1], "phase": "0"}   // t=2: X spider
  ],
  "edges": [[0, 2, 2], [1, 3, 1], ...]  // [src, tgt, edgeType]
}
```

Vertex types (t):
- 0: Boundary (input/output)
- 1: Z spider (green)
- 2: X spider (red)
- 3: H-box (Hadamard)

The parser reconstructs the ZxTerm by:
1. Identifying vertex types and phases
2. Determining connectivity (edges)
3. Building composition and tensor operations

This is a work in progress - complex graph topologies may need
manual reconstruction or simplification first.
-/

open Lean (Json)

namespace ZxCalculus.Parser

/-- Vertex type in .qgraph format (encoded as integer "t") -/
inductive QGraphVertexType
  | boundary  -- t = 0
  | z         -- t = 1 (Z spider / green)
  | x         -- t = 2 (X spider / red)
  | hbox      -- t = 3 (H-box)
  deriving Repr, DecidableEq

/-- Edge type in .qgraph format -/
inductive QGraphEdgeType
  | simple    -- Regular edge
  | hadamard  -- H-edge (orange in diagrams)
  deriving Repr, DecidableEq

/-- A vertex from .qgraph JSON -/
structure QGraphVertex where
  id : Nat
  vtype : QGraphVertexType
  phase : Rat  -- Phase as coefficient of π (optional, default 0)
  pos : Option (Int × Int)  -- Position [x, y] for layout
  deriving Repr

/-- An edge from .qgraph JSON -/
structure QGraphEdge where
  src : Nat
  tgt : Nat
  etype : QGraphEdgeType
  deriving Repr

/-- Complete parsed .qgraph data -/
structure QGraphData where
  version : Nat
  vertices : Array QGraphVertex
  edges : Array QGraphEdge
  inputs : Array Nat   -- Boundary vertex IDs marked as inputs
  outputs : Array Nat  -- Boundary vertex IDs marked as outputs
  scalar : Option (Int × String)  -- (power2, phase) - global scalar factor
  deriving Repr

/-! ## JSON Parsing Functions -/

/-- Helper: Convert Option to Except with error message -/
def optionToExcept {α : Type} (o : Option α) (errMsg : String) : Except String α :=
  match o with
  | some a => .ok a
  | none => .error errMsg

/-- Parse vertex type from integer code -/
def parseVertexType (t : Int) : Except String QGraphVertexType :=
  match t with
  | 0 => .ok .boundary
  | 1 => .ok .z
  | 2 => .ok .x
  | 3 => .ok .hbox
  | _ => .error s!"Unknown vertex type code: {t}"

/-- Parse edge type from integer code -/
def parseEdgeType (t : Int) : Except String QGraphEdgeType :=
  match t with
  | 1 => .ok .simple
  | 2 => .ok .hadamard
  | _ => .ok .simple  -- Default to simple

/-- Parse rational phase from .qgraph (as string or number) -/
def parsePhase (j : Json) : Except String Rat :=
  match j with
  | .str s =>
    -- Handle fractions like "1/4" or decimals like "0.25"
    if s.contains '/' then
      let parts := s.splitOn "/"
      match parts with
      | [num, den] =>
        match (num.toInt?, den.toNat?) with
        | (some n, some d) =>
          if d == 0 then .error "Division by zero in phase"
          else .ok (mkRat n d)
        | _ => .error s!"Invalid fraction: {s}"
      | _ => .error s!"Invalid fraction format: {s}"
    else if s.contains '.' then
      -- Decimal format from PyZX: "0.25", "0.5", etc.
      -- Pattern match common values
      if s == "0" || s == "0.0" then .ok 0
      else if s == "0.25" then .ok (mkRat 1 4)
      else if s == "0.5" then .ok (mkRat 1 2)
      else if s == "0.75" then .ok (mkRat 3 4)
      else if s == "0.125" then .ok (mkRat 1 8)
      else if s == "0.375" then .ok (mkRat 3 8)
      else if s == "0.625" then .ok (mkRat 5 8)
      else if s == "0.875" then .ok (mkRat 7 8)
      else if s == "1" || s == "1.0" then .ok 1
      -- Additional common values
      else if s == "0.333333" || s == "0.33333333" then .ok (mkRat 1 3)
      else if s == "0.666666" || s == "0.66666666" then .ok (mkRat 2 3)
      else
        -- Try to parse decimal manually: split on '.'
        let parts := s.splitOn "."
        match parts with
        | [intPart, fracPart] =>
          match (intPart.toInt?, fracPart.toNat?) with
          | (some i, some f) =>
            let denomPower : Nat := 10 ^ fracPart.length
            let numerator : Int := i * (denomPower : Int) + (f : Int)
            .ok (mkRat numerator denomPower)
          | _ => .error s!"Invalid decimal phase: {s}"
        | _ => .error s!"Invalid decimal format: {s}"
    else
      match s.toInt? with
      | some n => .ok (Rat.ofInt n)
      | none => .error s!"Invalid phase string: {s}"
  | .num n => .ok (Rat.ofInt n.mantissa)
  | _ => .ok 0  -- Default to 0 if not provided

/-- Parse a single vertex from JSON object -/
def parseVertex (obj : Lean.Json) : Except String QGraphVertex := do
  -- Get vertex ID (can be Nat or Int)
  let id ← match obj.getObjValAs? Nat "id" with
    | .ok n => .ok n
    | .error _ => match obj.getObjValAs? Int "id" with
      | .ok i => if i >= 0 then .ok i.toNat else .error "Negative vertex ID"
      | .error e => .error e

  -- Get vertex type (t field - can be Nat or Int)
  let t ← match obj.getObjValAs? Int "t" with
    | .ok i => .ok i
    | .error _ => match obj.getObjValAs? Nat "t" with
      | .ok n => .ok (n : Int)
      | .error e => .error e
  let vtype ← parseVertexType t

  -- Get phase (optional, default 0)
  let phase ← match obj.getObjValAs? Json "phase" |>.toOption with
    | some phaseJson => parsePhase phaseJson
    | none => .ok 0

  -- Get position (optional)
  let pos ← match obj.getObjValAs? Json "pos" |>.toOption with
    | some posJson => do
      let posArr ← posJson.getArr?
      match posArr with
      | #[xJson, yJson] =>
        -- x and y can be Int or Nat
        let x ← match xJson.getInt? with
          | .ok i => .ok i
          | .error _ => match xJson.getNat? with
            | .ok n => .ok (n : Int)
            | .error e => .error e
        let y ← match yJson.getInt? with
          | .ok i => .ok i
          | .error _ => match yJson.getNat? with
            | .ok n => .ok (n : Int)
            | .error e => .error e
        .ok (some (x, y))
      | _ => .ok none
    | none => .ok none

  pure { id, vtype, phase, pos }

/-- Parse edges from JSON -/
def parseEdges (json : Json) : Except String (Array QGraphEdge) := do
  let edgesArray ← json.getArr?
  let mut edges : Array QGraphEdge := #[]

  for edgeJson in edgesArray do
    let edgeArr ← edgeJson.getArr?
    match edgeArr with
    | #[srcJson, tgtJson, etypeJson] =>
      let src ← srcJson.getNat?
      let tgt ← tgtJson.getNat?
      let etypeInt ← etypeJson.getInt?
      let etype ← parseEdgeType etypeInt
      edges := edges.push { src, tgt, etype }
    | _ => .error "Edge must be [src, tgt, edgeType] triple"

  pure edges

/-- Main parser: .qgraph JSON → QGraphData -/
def parseQGraph (json : Json) : Except String QGraphData := do
  -- Parse version (can be Nat or Int)
  let version ← match json.getObjValAs? Nat "version" with
    | .ok n => .ok n
    | .error _ => match json.getObjValAs? Int "version" with
      | .ok i => if i >= 0 then .ok i.toNat else .error "Negative version"
      | .error e => .error e

  -- Parse vertices array
  let verticesJson ← json.getObjValAs? Json "vertices"
  let verticesArray ← verticesJson.getArr?
  let mut vertices : Array QGraphVertex := #[]

  for vJson in verticesArray do
    let vertex ← parseVertex vJson
    vertices := vertices.push vertex

  -- Parse edges
  let edgesJson ← json.getObjValAs? Json "edges"
  let edges ← parseEdges edgesJson

  -- Parse inputs and outputs
  let inputsJson ← json.getObjValAs? Json "inputs"
  let inputsArr ← inputsJson.getArr?
  let mut inputs : Array Nat := #[]
  for iJson in inputsArr do
    -- Can be Nat or Int
    let i ← match iJson.getNat? with
      | .ok n => .ok n
      | .error _ => match iJson.getInt? with
        | .ok i => if i >= 0 then .ok i.toNat else .error "Negative input ID"
        | .error e => .error e
    inputs := inputs.push i

  let outputsJson ← json.getObjValAs? Json "outputs"
  let outputsArr ← outputsJson.getArr?
  let mut outputs : Array Nat := #[]
  for oJson in outputsArr do
    -- Can be Nat or Int
    let o ← match oJson.getNat? with
      | .ok n => .ok n
      | .error _ => match oJson.getInt? with
        | .ok i => if i >= 0 then .ok i.toNat else .error "Negative output ID"
        | .error e => .error e
    outputs := outputs.push o

  -- Parse scalar (optional)
  let scalar ← match json.getObjValAs? Json "scalar" |>.toOption with
    | some scalarJson => do
      -- power2 can be Int or Nat
      let power2 ← match scalarJson.getObjValAs? Int "power2" with
        | .ok i => .ok i
        | .error _ => match scalarJson.getObjValAs? Nat "power2" with
          | .ok n => .ok (n : Int)
          | .error e => .error e
      let phase ← scalarJson.getObjValAs? String "phase"
      .ok (some (power2, phase))
    | none => .ok none

  pure { version, vertices, edges, inputs, outputs, scalar }

/-! ## Serialization: ZxTerm → QGraph -/

/-- State for building QGraph data during serialization -/
structure SerializerState where
  nextId : Nat
  vertices : Array QGraphVertex
  edges : Array QGraphEdge
  inputWires : Array Nat   -- Vertex IDs for current input wires
  outputWires : Array Nat  -- Vertex IDs for current output wires

/-- Serializer monad for stateful graph construction -/
abbrev SerializerM := StateM SerializerState

/-- Allocate a new vertex ID -/
def allocVertexId : SerializerM Nat := do
  let s ← get
  set { s with nextId := s.nextId + 1 }
  return s.nextId

/-- Add a vertex to the graph -/
def addVertex (v : QGraphVertex) : SerializerM Unit := do
  modify fun s => { s with vertices := s.vertices.push v }

/-- Add an edge to the graph -/
def addEdge (e : QGraphEdge) : SerializerM Unit := do
  modify fun s => { s with edges := s.edges.push e }

/-- Create boundary vertices for inputs -/
def createInputBoundaries (n : Nat) : SerializerM (Array Nat) := do
  let mut ids : Array Nat := #[]
  for i in [0:n] do
    let vid ← allocVertexId
    addVertex {
      id := vid,
      vtype := .boundary,
      phase := 0,
      pos := some (0, i)  -- Left column
    }
    ids := ids.push vid
  return ids

/-- Create boundary vertices for outputs -/
def createOutputBoundaries (m : Nat) (col : Int) : SerializerM (Array Nat) := do
  let mut ids : Array Nat := #[]
  for i in [0:m] do
    let vid ← allocVertexId
    addVertex {
      id := vid,
      vtype := .boundary,
      phase := 0,
      pos := some (col, i)  -- Right column
    }
    ids := ids.push vid
  return ids

/-- Convert rational phase to string for .qgraph format -/
def phaseToString (r : Rat) : String :=
  if r.den == 1 then
    toString r.num
  else
    s!"{r.num}/{r.den}"

/-- Serialize a generator at a specific position -/
def serializeGenerator {n m : Nat} (g : Generator n m) (col : Int) (startQubit : Int) : SerializerM Unit := do
  let inputWires ← get <&> (·.inputWires)

  match g with
  | .empty =>
    -- Empty diagram - no vertices, no wires
    modify fun s => { s with inputWires := #[], outputWires := #[] }

  | .id =>
    -- Identity - wire passes through
    if h : inputWires.size = 1 then
      modify fun s => { s with outputWires := inputWires }
    else
      -- Should not happen if types are correct
      modify fun s => { s with outputWires := inputWires }

  | .swap n m =>
    -- Swap wires - reverse the order
    let swapped := inputWires.reverse
    modify fun s => { s with outputWires := swapped }

  | .H =>
    -- Hadamard gate: In PyZX, this is represented as a Z-spider with a Hadamard edge
    -- Create a Z-spider with phase 0
    let vid ← allocVertexId
    addVertex {
      id := vid,
      vtype := .z,
      phase := 0,
      pos := some (col, startQubit)
    }
    -- Connect input wire to Z-spider with HADAMARD edge
    if h : inputWires.size ≥ 1 then
      addEdge { src := inputWires[0], tgt := vid, etype := .hadamard }
    -- Output is the Z-spider
    modify fun s => { s with outputWires := #[vid] }

  | .Z α n m =>
    -- Z spider
    let vid ← allocVertexId
    addVertex {
      id := vid,
      vtype := .z,
      phase := α,
      pos := some (col, startQubit + (n / 2))  -- Center vertically
    }
    -- Connect all input wires
    for i in [0:min n inputWires.size] do
      if h : i < inputWires.size then
        addEdge { src := inputWires[i], tgt := vid, etype := .simple }
    -- Outputs all connect from this spider
    let mut outWires : Array Nat := #[]
    for _ in [0:m] do
      outWires := outWires.push vid
    modify fun s => { s with outputWires := outWires }

  | .X α n m =>
    -- X spider (similar to Z)
    let vid ← allocVertexId
    addVertex {
      id := vid,
      vtype := .x,
      phase := α,
      pos := some (col, startQubit + (n / 2))
    }
    for i in [0:min n inputWires.size] do
      if h : i < inputWires.size then
        addEdge { src := inputWires[i], tgt := vid, etype := .simple }
    let mut outWires : Array Nat := #[]
    for _ in [0:m] do
      outWires := outWires.push vid
    modify fun s => { s with outputWires := outWires }

  | .cup =>
    -- Cup (2 → 0): Connect two input wires together
    if h : inputWires.size ≥ 2 then
      addEdge { src := inputWires[0], tgt := inputWires[1], etype := .simple }
    modify fun s => { s with outputWires := #[] }

  | .cap =>
    -- Cap (0 → 2): Create two new wires connected together
    let vid1 ← allocVertexId
    let vid2 ← allocVertexId
    addVertex { id := vid1, vtype := .z, phase := 0, pos := some (col, startQubit) }
    addVertex { id := vid2, vtype := .z, phase := 0, pos := some (col, startQubit + 1) }
    addEdge { src := vid1, tgt := vid2, etype := .simple }
    modify fun s => { s with outputWires := #[vid1, vid2] }

/-- Serialize a ZxTerm to QGraph structure
    col: horizontal position
    startQubit: vertical position offset (which qubit to start at)
-/
def serializeZxTermAux {n m : Nat} (term : ZxTerm n m) (col : Int) (startQubit : Int) : SerializerM Unit := do
  match term with
  | .gen g => serializeGenerator g col startQubit
  | .comp A B =>
    -- Serialize A first
    serializeZxTermAux A col startQubit
    -- Outputs of A become inputs of B
    let middleWires ← get <&> (·.outputWires)
    modify fun s => { s with inputWires := middleWires }
    -- Serialize B after A (same qubit offset)
    serializeZxTermAux B (col + 1) startQubit
  | .tens A B =>
    -- Save current input wires
    let currentInputs ← get <&> (·.inputWires)
    -- Split inputs between A and B based on their types
    -- For now, assume equal split (simplified)
    let splitPoint := currentInputs.size / 2
    let inputsA := currentInputs.extract 0 splitPoint
    let inputsB := currentInputs.extract splitPoint currentInputs.size

    -- Serialize A (top qubits starting at qubit 0)
    let s ← get
    set { s with inputWires := inputsA }
    serializeZxTermAux A col startQubit
    let outputsA ← get <&> (·.outputWires)

    -- Serialize B (bottom qubits starting at qubit splitPoint)
    let s ← get
    set { s with inputWires := inputsB }
    serializeZxTermAux B col (startQubit + splitPoint)
    let outputsB ← get <&> (·.outputWires)

    -- Combine outputs
    let s ← get
    set { s with outputWires := outputsA ++ outputsB }

/-- Main serialization function: ZxTerm → QGraphData -/
def serializeToQGraph {n m : Nat} (term : ZxTerm n m) : QGraphData :=
  let initialState : SerializerState := {
    nextId := 0,
    vertices := #[],
    edges := #[],
    inputWires := #[],
    outputWires := #[]
  }

  let ((inputBoundaries, outputBoundaries), finalState) := (do
    -- Create input boundaries (column -1, before gates)
    let mut inputBoundaries : Array Nat := #[]
    for i in [0:n] do
      let vid ← allocVertexId
      addVertex {
        id := vid,
        vtype := .boundary,
        phase := 0,
        pos := some (-1, i)  -- Place inputs one column before gates
      }
      inputBoundaries := inputBoundaries.push vid

    let s ← get
    set { s with inputWires := inputBoundaries }

    -- Serialize the term (starts at column 0, qubit 0)
    serializeZxTermAux term 0 0

    -- Create output boundaries (at column 1000, far to the right)
    let mut outputBoundaries : Array Nat := #[]
    for i in [0:m] do
      let vid ← allocVertexId
      addVertex {
        id := vid,
        vtype := .boundary,
        phase := 0,
        pos := some (1000, i)  -- Place outputs far to the right
      }
      outputBoundaries := outputBoundaries.push vid

    -- Connect internal outputs to output boundaries
    let internalOuts ← get <&> (·.outputWires)
    for i in [0:min m internalOuts.size] do
      if h1 : i < internalOuts.size then
        if h2 : i < outputBoundaries.size then
          addEdge { src := internalOuts[i], tgt := outputBoundaries[i], etype := .simple }

    return (inputBoundaries, outputBoundaries)
  ).run initialState

  {
    version := 2,
    vertices := finalState.vertices,
    edges := finalState.edges,
    inputs := inputBoundaries,
    outputs := outputBoundaries,
    scalar := none
  }

/-! ## Reconstruction to ZxTerm -/

/-- Convert a vertex to a Generator (if it's not a boundary) -/
def vertexToGenerator (v : QGraphVertex) (numInputs numOutputs : Nat) :
    Except String (Σ n m, Generator n m) := do
  match v.vtype with
  | .boundary => .error "Cannot convert boundary to generator"
  | .z => .ok ⟨numInputs, numOutputs, Generator.Z v.phase numInputs numOutputs⟩
  | .x => .ok ⟨numInputs, numOutputs, Generator.X v.phase numInputs numOutputs⟩
  | .hbox =>
    -- H-box should be 1-1
    if numInputs == 1 && numOutputs == 1 then
      .ok ⟨1, 1, Generator.H⟩
    else
      .error "H-box must have 1 input and 1 output"

/--
Helper: Find vertex by ID
-/
def findVertex? (vertices : Array QGraphVertex) (id : Nat) : Option QGraphVertex :=
  vertices.find? (·.id == id)

/--
Helper: Get neighbors of a vertex
-/
def getNeighbors (edges : Array QGraphEdge) (vid : Nat) : Array Nat :=
  let outgoing := edges.filter (·.src == vid) |>.map (·.tgt)
  let incoming := edges.filter (·.tgt == vid) |>.map (·.src)
  outgoing ++ incoming

/--
Helper: Build identity circuit for n qubits
Only supports 0, 1, 2 qubits currently
-/
def buildIdentity? (n : Nat) : Option (Σ n m, ZxTerm n m) :=
  if n == 0 then
    some ⟨0, 0, ZxTerm.empty⟩
  else if n == 1 then
    some ⟨1, 1, ZxTerm.id⟩
  else if n == 2 then
    some ⟨2, 2, ZxTerm.id ⊗ ZxTerm.id⟩
  else
    none  -- Not supported for n > 2 yet

/--
Reconstruction using topology analysis.

Strategy:
1. For each input, trace the path to its corresponding output
2. Identify gates along each path (H-boxes, Z/X spiders)
3. Build the circuit layer by layer based on column positions

Current limitations:
- Handles simple sequential circuits (gates in series)
- Handles parallel gates (tensor products)
- Does not handle complex graph rewrites or multi-arity spiders beyond simple cases
-/
def reconstructZxTermSimple (qgraph : QGraphData) :
    Except String (Σ n m, ZxTerm n m) := do

  let numQubits := qgraph.inputs.size

  -- Special cases
  if numQubits == 0 then
    return ⟨0, 0, ZxTerm.empty⟩

  -- Find all non-boundary vertices (these are gates)
  let gates := qgraph.vertices.filter (fun v => v.vtype != .boundary)

  -- If no gates, just return identity
  if gates.isEmpty then
    match buildIdentity? numQubits with
    | some result => return result
    | none => .error s!"Identity circuits for {numQubits} qubits not yet supported"

  -- Group gates by column (position.fst)
  -- Sort by column to process left to right
  let gatesWithPos := gates.filterMap (fun v =>
    match v.pos with
    | some (col, _) => some (v, col)
    | none => none
  )

  if gatesWithPos.isEmpty then
    -- No position info, return identity
    match buildIdentity? numQubits with
    | some result => return result
    | none => .error s!"Identity circuits for {numQubits} qubits not yet supported"

  -- Simple reconstruction: look at each gate individually
  -- For single-qubit circuits, just compose gates in order
  if numQubits == 1 then
    -- Sort gates by column
    let sortedGates := gatesWithPos.qsort (fun a b => a.2 < b.2) |>.map (·.1)

    -- Helper: check if vertex has a Hadamard edge
    let hasHadamardEdge (vid : Nat) : Bool :=
      qgraph.edges.any (fun e =>
        (e.src == vid || e.tgt == vid) && e.etype == .hadamard)

    -- Build composition of gates
    let mut circuit : ZxTerm 1 1 := ZxTerm.id

    for gate in sortedGates do
      match gate.vtype with
      | .hbox =>
        -- Explicit H-box vertex
        circuit := circuit ; ZxTerm.H
      | .z =>
        -- Z-spider: could be a Hadamard if it has phase 0 and a Hadamard edge
        if gate.phase == 0 && hasHadamardEdge gate.id then
          circuit := circuit ; ZxTerm.H
        else
          circuit := circuit ; ZxTerm.Z gate.phase 1 1
      | .x =>
        -- X-spider: could be a Hadamard if it has phase 0 and a Hadamard edge
        if gate.phase == 0 && hasHadamardEdge gate.id then
          circuit := circuit ; ZxTerm.H
        else
          circuit := circuit ; ZxTerm.X gate.phase 1 1
      | .boundary => continue

    return ⟨1, 1, circuit⟩

  -- For multi-qubit circuits: return identity for now
  -- Full topology analysis for entangled circuits is complex
  -- and requires tracking which gates act on which qubits
  else
    -- Check if all gates are single-qubit (1 input, 1 output each)
    -- This indicates a tensor product of independent circuits
    let allSimple := gates.all (fun g =>
      let neighbors := getNeighbors qgraph.edges g.id
      neighbors.size ≤ 2  -- At most one input and one output
    )

    if allSimple && numQubits == 2 then
      -- Try to build tensor product of two single-qubit circuits
      -- This is a simplified heuristic
      let gatesQubit0 := gatesWithPos.filter (fun gp =>
        match gp.1.pos with
        | some (_, q) => q == 0
        | none => false
      ) |>.qsort (fun a b => a.2 < b.2) |>.map (·.1)

      let gatesQubit1 := gatesWithPos.filter (fun gp =>
        match gp.1.pos with
        | some (_, q) => q == 1
        | none => false
      ) |>.qsort (fun a b => a.2 < b.2) |>.map (·.1)

      -- Helper: check if vertex has a Hadamard edge
      let hasHadamardEdge (vid : Nat) : Bool :=
        qgraph.edges.any (fun e =>
          (e.src == vid || e.tgt == vid) && e.etype == .hadamard)

      -- Build circuit for qubit 0
      let mut circ0 : ZxTerm 1 1 := ZxTerm.id
      for gate in gatesQubit0 do
        match gate.vtype with
        | .hbox => circ0 := circ0 ; ZxTerm.H
        | .z =>
          -- Z-spider: could be a Hadamard if it has phase 0 and a Hadamard edge
          if gate.phase == 0 && hasHadamardEdge gate.id then
            circ0 := circ0 ; ZxTerm.H
          else
            circ0 := circ0 ; ZxTerm.Z gate.phase 1 1
        | .x =>
          -- X-spider: could be a Hadamard if it has phase 0 and a Hadamard edge
          if gate.phase == 0 && hasHadamardEdge gate.id then
            circ0 := circ0 ; ZxTerm.H
          else
            circ0 := circ0 ; ZxTerm.X gate.phase 1 1
        | .boundary => continue

      -- Build circuit for qubit 1
      let mut circ1 : ZxTerm 1 1 := ZxTerm.id
      for gate in gatesQubit1 do
        match gate.vtype with
        | .hbox => circ1 := circ1 ; ZxTerm.H
        | .z =>
          if gate.phase == 0 && hasHadamardEdge gate.id then
            circ1 := circ1 ; ZxTerm.H
          else
            circ1 := circ1 ; ZxTerm.Z gate.phase 1 1
        | .x =>
          if gate.phase == 0 && hasHadamardEdge gate.id then
            circ1 := circ1 ; ZxTerm.H
          else
            circ1 := circ1 ; ZxTerm.X gate.phase 1 1
        | .boundary => continue

      return ⟨2, 2, circ0 ⊗ circ1⟩
    else
      -- Complex entangled circuit - return identity
      -- Full reconstruction would require analyzing edge connectivity
      -- and building CNOT/CZ gates from spider mergers
      match buildIdentity? numQubits with
      | some result => return result
      | none => .error s!"Complex circuits with {numQubits} qubits not yet supported"

/-! ## JSON Export -/

/-- Convert QGraphData to JSON -/
def qgraphToJson (qgraph : QGraphData) : Json :=
  let verticesJson := qgraph.vertices.map fun v =>
    -- Explicitly cast to Int for JSON compatibility with PyZX
    let base := Json.mkObj [
      ("id", Lean.toJson (v.id : Int)),
      ("t", Lean.toJson (match v.vtype with
        | .boundary => (0 : Int)
        | .z => (1 : Int)
        | .x => (2 : Int)
        | .hbox => (3 : Int)))
    ]
    let withPhase := if v.phase != 0 then
      base.mergeObj (Json.mkObj [("phase", Json.str (phaseToString v.phase))])
    else base
    let withPos := match v.pos with
      | some (r, q) => withPhase.mergeObj (Json.mkObj [
          ("pos", Json.arr #[Lean.toJson r, Lean.toJson q])
        ])
      | none => withPhase
    withPos

  let edgesJson := qgraph.edges.map fun e =>
    Json.arr #[
      Lean.toJson (e.src : Int),
      Lean.toJson (e.tgt : Int),
      Lean.toJson (match e.etype with
        | .simple => (1 : Int)
        | .hadamard => (2 : Int))
    ]

  let inputsJson := qgraph.inputs.map (fun (i : Nat) => Lean.toJson (i : Int))
  let outputsJson := qgraph.outputs.map (fun (i : Nat) => Lean.toJson (i : Int))

  let base := Json.mkObj [
    ("version", Lean.toJson (qgraph.version : Int)),
    ("backend", Json.str "simple"),  -- PyZX requires this field
    ("vertices", Json.arr verticesJson),
    ("edges", Json.arr edgesJson),
    ("inputs", Json.arr inputsJson),
    ("outputs", Json.arr outputsJson)
  ]

  match qgraph.scalar with
  | some (power2, phase) => base.mergeObj (Json.mkObj [
      ("scalar", Json.mkObj [
        ("power2", Lean.toJson power2),
        ("phase", Json.str phase)
      ])
    ])
  | none => base

/-! ## File I/O -/

/-- Read and parse a .qgraph file -/
def parseQGraphFile (path : System.FilePath) : IO QGraphData := do
  let contents ← IO.FS.readFile path
  match Json.parse contents with
  | .error e => throw (IO.userError s!"JSON parse error: {e}")
  | .ok json =>
    match parseQGraph json with
    | .error e => throw (IO.userError s!"QGraph parse error: {e}")
    | .ok qgraph => pure qgraph

/-- Write QGraphData to a .qgraph file -/
def writeQGraphFile (path : System.FilePath) (qgraph : QGraphData) : IO Unit := do
  let json := qgraphToJson qgraph
  IO.FS.writeFile path (json.compress)

/-- Read .qgraph file and attempt simple reconstruction to ZxTerm -/
def loadQGraphAsZxTerm (path : System.FilePath) :
    IO (Except String (Σ n m, ZxTerm n m)) := do
  let qgraph ← parseQGraphFile path
  pure (reconstructZxTermSimple qgraph)

/-- Serialize ZxTerm to .qgraph file -/
def saveZxTermAsQGraph {n m : Nat} (path : System.FilePath) (term : ZxTerm n m) : IO Unit := do
  let qgraph := serializeToQGraph term
  writeQGraphFile path qgraph

/-! ## Example Usage -/

#check parseQGraph
#check parseQGraphFile
#check serializeToQGraph
#check saveZxTermAsQGraph
#check reconstructZxTermSimple

end ZxCalculus.Parser
