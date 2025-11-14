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
    -- Handle fractions like "1/4" or decimals
    if s.contains '/' then
      let parts := s.splitOn "/"
      match parts with
      | [num, den] =>
        match (num.toNat?, den.toNat?) with
        | (some n, some d) =>
          if d == 0 then .error "Division by zero in phase"
          else .ok (mkRat n d)
        | _ => .error s!"Invalid fraction: {s}"
      | _ => .error s!"Invalid fraction format: {s}"
    else
      match s.toInt? with
      | some n => .ok (Rat.ofInt n)
      | none => .error s!"Invalid phase string: {s}"
  | .num n => .ok (Rat.ofInt n.mantissa)
  | _ => .ok 0  -- Default to 0 if not provided

/-- Parse a single vertex from JSON object -/
def parseVertex (obj : Lean.Json) : Except String QGraphVertex := do
  -- Get vertex ID
  let id ← obj.getObjValAs? Nat "id"

  -- Get vertex type (t field)
  let t ← obj.getObjValAs? Int "t"
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
        let x ← xJson.getInt?
        let y ← yJson.getInt?
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
  -- Parse version
  let version ← json.getObjValAs? Nat "version"

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
    let i ← iJson.getNat?
    inputs := inputs.push i

  let outputsJson ← json.getObjValAs? Json "outputs"
  let outputsArr ← outputsJson.getArr?
  let mut outputs : Array Nat := #[]
  for oJson in outputsArr do
    let o ← oJson.getNat?
    outputs := outputs.push o

  -- Parse scalar (optional)
  let scalar ← match json.getObjValAs? Json "scalar" |>.toOption with
    | some scalarJson => do
      let power2 ← scalarJson.getObjValAs? Int "power2"
      let phase ← scalarJson.getObjValAs? String "phase"
      .ok (some (power2, phase))
    | none => .ok none

  pure { version, vertices, edges, inputs, outputs, scalar }

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
Simplified reconstruction for linear circuits.

This works for circuits where vertices are arranged in layers (by row),
and we can compose layers sequentially.

Limitations:
- Only handles simple circuit topologies
- May not work for arbitrary ZX diagrams with complex connectivity
- Use this as a starting point; complex diagrams may need manual construction
-/
def reconstructZxTermSimple (qgraph : QGraphData) :
    Except String (Σ n m, ZxTerm n m) := do

  let numQubits := qgraph.inputs.size

  -- For now, just create a simple identity circuit as proof of concept
  -- TODO: Implement full reconstruction by analyzing graph structure

  -- Build identity for each qubit
  if numQubits == 0 then
    .ok ⟨0, 0, ZxTerm.empty⟩
  else if numQubits == 1 then
    .ok ⟨1, 1, ZxTerm.id⟩
  else if numQubits == 2 then
    -- 2-qubit case
    .ok ⟨2, 2, ZxTerm.id ⊗ ZxTerm.id⟩
  else
    -- For now, reject circuits with > 2 qubits
    -- Full implementation would analyze graph topology
    .error s!"Reconstruction for {numQubits} qubits not yet implemented"

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

/-- Read .qgraph file and attempt simple reconstruction to ZxTerm -/
def loadQGraphAsZxTerm (path : System.FilePath) :
    IO (Except String (Σ n m, ZxTerm n m)) := do
  let qgraph ← parseQGraphFile path
  pure (reconstructZxTermSimple qgraph)

/-! ## Example Usage -/

#check parseQGraph
#check parseQGraphFile
#check reconstructZxTermSimple

end ZxCalculus.Parser
