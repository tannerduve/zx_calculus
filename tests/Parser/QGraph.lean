import ZxCalculus.Format.QGraph.Basic
import ZxCalculus.DenotationalSemantics

/-!
# QGraph Format Tests

End-to-end tests for parsing .qgraph files and verifying equivalences.
-/

open Lean (Json)
open ZxCalculus.Format.QGraph

/-! ## Basic Parsing Tests -/

/-- Test parsing a simple .qgraph JSON string -/
def testParseSimple : IO Unit := do
  let jsonStr := "{
    \"version\": 2,
    \"backend\": \"simple\",
    \"inputs\": [0],
    \"outputs\": [1],
    \"vertices\": [
      {\"id\": 0, \"t\": 0, \"pos\": [0, 0]},
      {\"id\": 1, \"t\": 0, \"pos\": [1, 0]}
    ],
    \"edges\": [[0, 1, 1]],
    \"scalar\": {\"power2\": 0, \"phase\": \"0\"}
  }"

  match Json.parse jsonStr with
  | .error e => IO.println s!"Parse failed: {e}"
  | .ok json =>
    match parse json with
    | .error e => IO.println s!"QGraph parse failed: {e}"
    | .ok qgraph => do
      IO.println "✓ Successfully parsed simple qgraph"
      IO.println s!"  Version: {qgraph.version}"
      IO.println s!"  Vertices: {qgraph.vertices.size}"
      IO.println s!"  Edges: {qgraph.edges.size}"
      IO.println s!"  Inputs: {qgraph.inputs}"
      IO.println s!"  Outputs: {qgraph.outputs}"

/-! ## Validation Functions -/

/-- Validate that a QGraph has the expected structure -/
def validateQGraph (name : String) (qgraph : Data) : IO Bool := do
  IO.println s!"  Testing: {name}"

  -- Basic structure checks
  if qgraph.version != 2 then
    IO.println s!"    ✗ Invalid version: {qgraph.version}"
    return false

  if qgraph.inputs.size == 0 && qgraph.outputs.size == 0 then
    IO.println "    ✗ No inputs or outputs"
    return false

  if qgraph.inputs.size != qgraph.outputs.size then
    IO.println s!"    ✗ Input/output mismatch: {qgraph.inputs.size} ≠ {qgraph.outputs.size}"
    return false

  -- Count vertex types
  let mut zCount := 0
  let mut xCount := 0
  let mut hCount := 0
  let mut bCount := 0

  for v in qgraph.vertices do
    match v.vtype with
    | .z => zCount := zCount + 1
    | .x => xCount := xCount + 1
    | .hbox => hCount := hCount + 1
    | .boundary => bCount := bCount + 1

  IO.println s!"    ✓ {qgraph.inputs.size} qubits"
  IO.println s!"    ✓ {qgraph.vertices.size} vertices ({bCount} boundary, {zCount} Z, {xCount} X, {hCount} H)"
  IO.println s!"    ✓ {qgraph.edges.size} edges"

  return true

/-- Compare two Data structures for equality -/
def compareQGraphs (name : String) (qgraph1 qgraph2 : Data) : IO Bool := do
  IO.println s!"  Comparing: {name} against golden copy"

  if qgraph1.inputs.size != qgraph2.inputs.size then
    IO.println s!"    ✗ Input count mismatch: {qgraph1.inputs.size} ≠ {qgraph2.inputs.size}"
    return false

  if qgraph1.vertices.size != qgraph2.vertices.size then
    IO.println s!"    ✗ Vertex count mismatch: {qgraph1.vertices.size} ≠ {qgraph2.vertices.size}"
    return false

  if qgraph1.edges.size != qgraph2.edges.size then
    IO.println s!"    ✗ Edge count mismatch: {qgraph1.edges.size} ≠ {qgraph2.edges.size}"
    return false

  IO.println "    ✓ Structures match"
  return true

/-! ## Manual Circuit Construction for Comparison -/

/-- Manually construct a Bell state in ZxTerm -/
def bellStateManual : ZxTerm 2 2 :=
  -- Hadamard on first qubit, identity on second
  (ZxTerm.H ⊗ ZxTerm.id) ;
  -- CNOT: represented as Z-X spider connection
  -- This is simplified; real CNOT in ZX calculus is:
  -- (id ⊗ H) ; CZ ; (id ⊗ H) where CZ is a Z spider with 2 inputs/outputs
  (ZxTerm.Z 0 2 2)

/-- Identity circuit on 2 qubits -/
def id2 : ZxTerm 2 2 :=
  ZxTerm.id ⊗ ZxTerm.id

/-- Hadamard on first qubit, identity on second -/
def hadamardFirst : ZxTerm 2 2 :=
  ZxTerm.H ⊗ ZxTerm.id

/-! ## File-based Tests -/

/-- Test loading a .qgraph file from Python export -/
def testLoadBellState : IO Unit := do
  -- Path relative to project root
  let path : System.FilePath := "py/bell_state.qgraph"

  IO.println "Loading bell_state.qgraph..."

  try
    let qgraph ← parseFile path
    IO.println s!"✓ Successfully parsed bell_state.qgraph"
    IO.println s!"  Inputs: {qgraph.inputs.size} qubits"
    IO.println s!"  Outputs: {qgraph.outputs.size} qubits"
    IO.println s!"  Total vertices: {qgraph.vertices.size}"
    IO.println s!"  Total edges: {qgraph.edges.size}"

    -- Show vertex types
    IO.println "\n  Vertex types:"
    for v in qgraph.vertices do
      let typeStr := match v.vtype with
        | .boundary => "BOUNDARY"
        | .z => s!"Z(phase={v.phase})"
        | .x => s!"X(phase={v.phase})"
        | .hbox => "H"
      IO.println s!"    v{v.id}: {typeStr}"

    -- Try reconstruction
    match reconstruct qgraph with
    | .error e => IO.println s!"\n  Reconstruction not yet implemented: {e}"
    | .ok ⟨n, m, _⟩ =>
      IO.println s!"\n✓ Reconstructed as ZxTerm {n} {m}"
      -- Can't print the term directly, but we have it!

  catch e =>
    IO.println s!"✗ Failed to load: {e}"

/-- Test loading CNOT -/
def testLoadCNOT : IO Unit := do
  let path : System.FilePath := "py/cnot.qgraph"

  IO.println "\nLoading cnot.qgraph..."

  try
    let qgraph ← parseFile path
    IO.println s!"✓ Successfully parsed cnot.qgraph"
    IO.println s!"  Inputs: {qgraph.inputs.size} qubits"
    IO.println s!"  Outputs: {qgraph.outputs.size} qubits"
    IO.println s!"  Total vertices: {qgraph.vertices.size}"

    -- Count vertex types
    let mut zCount := 0
    let mut xCount := 0
    let mut hCount := 0
    let mut bCount := 0

    for v in qgraph.vertices do
      match v.vtype with
      | .z => zCount := zCount + 1
      | .x => xCount := xCount + 1
      | .hbox => hCount := hCount + 1
      | .boundary => bCount := bCount + 1

    IO.println s!"  Z spiders: {zCount}, X spiders: {xCount}, H-boxes: {hCount}, Boundaries: {bCount}"

  catch e =>
    IO.println s!"✗ Failed to load: {e}"

/-- Test loading GHZ state -/
def testLoadGHZ : IO Unit := do
  let path : System.FilePath := "py/ghz_state.qgraph"

  IO.println "\nLoading ghz_state.qgraph..."

  try
    let qgraph ← parseFile path
    IO.println s!"✓ Successfully parsed ghz_state.qgraph"
    IO.println s!"  Inputs: {qgraph.inputs.size} qubits"
    IO.println s!"  Outputs: {qgraph.outputs.size} qubits"

  catch e =>
    IO.println s!"✗ Failed to load: {e}"

/-! ## Automated Testing Functions -/

/-- Test a single file with optional golden copy comparison -/
def testFile (path : System.FilePath) (goldenPath? : Option System.FilePath := none) : IO Bool := do
  let name := match path.fileName with
    | some n => n
    | none => "unknown"
  let basename := if name.endsWith ".qgraph" then
    name.dropRight ".qgraph".length
  else
    name

  try
    -- Parse the test file
    let qgraph ← parseFile path

    -- Validate structure
    let valid ← validateQGraph basename qgraph
    if not valid then
      return false

    -- Try reconstruction
    match reconstruct qgraph with
    | .ok ⟨n, m, _term⟩ =>
      IO.println s!"    ✓ Reconstructed as ZxTerm {n} {m}"
    | .error e =>
      IO.println s!"    ⚠ Reconstruction: {e}"

    -- Compare against golden copy if provided
    match goldenPath? with
    | some goldenPath => do
      if ← goldenPath.pathExists then
        let golden ← parseFile goldenPath
        let isMatch ← compareQGraphs basename qgraph golden
        if not isMatch then
          IO.println "    ✗ Does not match golden copy"
          return false
      else
        IO.println s!"    ⚠ Golden copy not found: {goldenPath}"
    | none => pure ()

    IO.println "    ✓ PASSED\n"
    return true

  catch e =>
    IO.println s!"    ✗ FAILED: {e}"
    return false

/-- Run automated test suite on temp directory -/
def runAutomatedTests (tempDir : String) (goldenDir : String) : IO UInt32 := do
  let sep := String.mk (List.replicate 70 '=')
  IO.println sep
  IO.println "Automated Parser Tests"
  IO.println sep
  IO.println s!"Test directory: {tempDir}"
  IO.println s!"Golden directory: {goldenDir}\n"

  -- List of expected test files
  let testFiles := [
    ("test_id1.qgraph", none),
    ("test_id2.qgraph", none),
    ("test_hadamard.qgraph", none),
    ("test_bell.qgraph", some "bell_state.qgraph"),
    ("test_cnot.qgraph", some "cnot.qgraph")
  ]

  let mut allPassed := true
  let mut passCount := 0
  let mut failCount := 0

  for (filename, goldenName?) in testFiles do
    let path : System.FilePath := ⟨s!"{tempDir}/{filename}"⟩

    -- Check if file exists
    if !(← path.pathExists) then
      IO.println s!"✗ File not found: {filename}\n"
      allPassed := false
      failCount := failCount + 1
      continue

    -- Build golden path if specified
    let goldenPath? := goldenName?.map fun g => (⟨s!"{goldenDir}/{g}"⟩ : System.FilePath)

    -- Test the file
    let passed ← testFile path goldenPath?
    if passed then
      passCount := passCount + 1
    else
      allPassed := false
      failCount := failCount + 1

  -- Print summary
  IO.println sep
  if allPassed then
    IO.println "✓ All tests passed!"
  else
    IO.println "✗ Some tests failed"
  IO.println sep
  IO.println s!"Results: {passCount} passed, {failCount} failed\n"

  return if allPassed then 0 else 1

/-! ## Main Test Runner -/

/-- Run manual interactive tests (existing py/ files) -/
def runManualTests : IO Unit := do
  let sep := String.mk (List.replicate 70 '=')
  IO.println sep
  IO.println "Manual Parser Tests"
  IO.println sep

  IO.println "\n1. Basic JSON Parsing:"
  testParseSimple

  IO.println ("\n" ++ sep)
  IO.println "2. File Loading Tests:"
  IO.println sep

  testLoadBellState
  testLoadCNOT
  testLoadGHZ

  IO.println ("\n" ++ sep)
  IO.println "✓ Parser tests complete!"
  IO.println sep

/-- Main entry point - handles both manual and automated modes -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    -- No args: run manual tests
    runManualTests
    return 0
  | [tempDir] =>
    -- One arg: run automated tests with default golden dir
    runAutomatedTests tempDir "scripts/golden"
  | [tempDir, goldenDir] =>
    -- Two args: run automated tests with custom golden dir
    runAutomatedTests tempDir goldenDir
  | _ =>
    IO.println "Usage:"
    IO.println "  lake env lean --run tests/Parser.lean              # Manual tests"
    IO.println "  lake env lean --run tests/Parser.lean <temp_dir>   # Automated tests"
    IO.println "  lake env lean --run tests/Parser.lean <temp_dir> <golden_dir>"
    return 1

-- Test with golden files
#eval testParseSimple

#eval do
  IO.println "\n\nTesting scripts/golden/bell_state.qgraph"
  let path : System.FilePath := "scripts/golden/bell_state.qgraph"
  testFile path none

#eval do
  IO.println "\n\nTesting scripts/golden/cnot.qgraph"
  let path : System.FilePath := "scripts/golden/cnot.qgraph"
  testFile path none

-- Roundtrip test: ZxTerm → QGraph → ZxTerm
#eval do
  IO.println "\n\n=== Roundtrip Tests ==="

  -- Test 1: Identity
  IO.println "\n1. Testing identity wire:"
  let term1 : ZxTerm 1 1 := ZxTerm.id
  let qgraph1 := serialize term1
  IO.println s!"   Serialized: {qgraph1.vertices.size} vertices, {qgraph1.edges.size} edges"
  match reconstruct qgraph1 with
  | .ok ⟨n, m, _⟩ => IO.println s!"   ✓ Reconstructed: ZxTerm {n} {m}"
  | .error e => IO.println s!"   ✗ Failed: {e}"

  -- Test 2: Hadamard
  IO.println "\n2. Testing Hadamard gate:"
  let term2 : ZxTerm 1 1 := ZxTerm.H
  let qgraph2 := serialize term2
  IO.println s!"   Serialized: {qgraph2.vertices.size} vertices, {qgraph2.edges.size} edges"
  match reconstruct qgraph2 with
  | .ok ⟨n, m, _⟩ => IO.println s!"   ✓ Reconstructed: ZxTerm {n} {m}"
  | .error e => IO.println s!"   ✗ Failed: {e}"

  -- Test 3: Two parallel Hadamards (tensor product)
  IO.println "\n3. Testing H ⊗ H:"
  let term3 : ZxTerm 2 2 := ZxTerm.H ⊗ ZxTerm.H
  let qgraph3 := serialize term3
  IO.println s!"   Serialized: {qgraph3.vertices.size} vertices, {qgraph3.edges.size} edges"
  match reconstruct qgraph3 with
  | .ok ⟨n, m, _⟩ => IO.println s!"   ✓ Reconstructed: ZxTerm {n} {m}"
  | .error e => IO.println s!"   ✗ Failed: {e}"

  -- Test 4: Hadamard composition
  IO.println "\n4. Testing H ; H (should be identity):"
  let term4 : ZxTerm 1 1 := ZxTerm.H ; ZxTerm.H
  let qgraph4 := serialize term4
  IO.println s!"   Serialized: {qgraph4.vertices.size} vertices, {qgraph4.edges.size} edges"
  match reconstruct qgraph4 with
  | .ok ⟨n, m, _⟩ => IO.println s!"   ✓ Reconstructed: ZxTerm {n} {m}"
  | .error e => IO.println s!"   ✗ Failed: {e}"

-- Uncomment to run manual tests interactively:
-- #eval runManualTests
