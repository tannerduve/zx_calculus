#!/usr/bin/env python3
"""
Roundtrip Test: PyZX → Lean → PyZX

Tests the full pipeline:
1. Create circuits in PyZX
2. Export to .qgraph
3. Load in Lean, parse to ZxTerm
4. Serialize back to .qgraph
5. Load back in PyZX
6. Check equivalence using PyZX tensor comparison
"""

import sys
import subprocess
from pathlib import Path
from typing import Tuple, Optional
import tempfile

try:
    import pyzx as zx
except ImportError:
    print("Error: pyzx not installed. Install with: pip install pyzx")
    sys.exit(1)

# Color codes
GREEN = '\033[92m'
RED = '\033[91m'
YELLOW = '\033[93m'
BLUE = '\033[94m'
RESET = '\033[0m'


class RoundtripTester:
    """Test roundtrip conversion: PyZX → Lean → PyZX"""
    
    def __init__(self, lean_script: str = "scripts/RoundtripLean.lean"):
        self.lean_script = Path(lean_script)
        self.test_dir = Path(tempfile.mkdtemp(prefix="roundtrip_"))
        self.results = []
        
    # ========================================================================
    # Individual Circuit Builders
    # ========================================================================
    
    def circuit_identity(self):
        """Identity: just a wire (1→1)"""
        c = zx.Circuit(1)
        return c
    
    def circuit_hadamard(self):
        """Single Hadamard gate"""
        c = zx.Circuit(1)
        c.add_gate("HAD", 0)
        return c
    
    def circuit_z_phase(self):
        """Z-phase gate (π/4)"""
        c = zx.Circuit(1)
        c.add_gate("ZPhase", 0, 0.25)  # π/4
        return c
    
    def circuit_x_phase(self):
        """X-phase gate (π/2)"""
        c = zx.Circuit(1)
        c.add_gate("XPhase", 0, 0.5)  # π/2
        return c
    
    def circuit_h_z_comp(self):
        """Composition: H ; Z(π/2)"""
        c = zx.Circuit(1)
        c.add_gate("HAD", 0)
        c.add_gate("ZPhase", 0, 0.5)
        return c
    
    def circuit_three_hadamards(self):
        """Three Hadamards in sequence (should equal H)"""
        c = zx.Circuit(1)
        c.add_gate("HAD", 0)
        c.add_gate("HAD", 0)
        c.add_gate("HAD", 0)
        return c
    
    def circuit_two_qubit_parallel(self):
        """Two qubits: H ⊗ Z(π/4)"""
        c = zx.Circuit(2)
        c.add_gate("HAD", 0)
        c.add_gate("ZPhase", 1, 0.25)
        return c
    
    def circuit_cnot(self):
        """CNOT gate (entangling)"""
        c = zx.Circuit(2)
        c.add_gate("CNOT", 0, 1)
        return c
    
    def circuit_bell_state(self):
        """Bell state preparation: H ; CNOT"""
        c = zx.Circuit(2)
        c.add_gate("HAD", 0)
        c.add_gate("CNOT", 0, 1)
        return c
    
    def circuit_simple_z_spider(self):
        """Simple Z spider (2-ary, custom graph)"""
        g = zx.Graph()
        v0 = g.add_vertex(0, 0, 0)  # Input boundary
        v1 = g.add_vertex(1, 1, 0)  # Z spider
        v2 = g.add_vertex(0, 2, 0)  # Output boundary
        g.add_edge((v0, v1))
        g.add_edge((v1, v2))
        g.set_inputs([v0])
        g.set_outputs([v2])
        return g
    
    def get_all_circuits(self):
        """Get all test circuits as a dictionary"""
        return {
            "identity": self.circuit_identity(),
            "hadamard": self.circuit_hadamard(),
            "z_phase": self.circuit_z_phase(),
            "x_phase": self.circuit_x_phase(),
            "h_z_comp": self.circuit_h_z_comp(),
            "three_hadamards": self.circuit_three_hadamards(),
            "two_qubit_parallel": self.circuit_two_qubit_parallel(),
            "cnot": self.circuit_cnot(),
            "bell_state": self.circuit_bell_state(),
            "simple_z_spider": self.circuit_simple_z_spider(),
        }
    
    def export_pyzx_circuit(self, circuit, name: str) -> Path:
        """Export PyZX circuit/graph to .qgraph file"""
        if isinstance(circuit, zx.Circuit):
            g = circuit.to_graph()
        else:
            g = circuit
            
        filepath = self.test_dir / f"{name}_original.qgraph"
        
        # Use PyZX's native serialization
        with open(filepath, 'w') as f:
            f.write(g.to_json())
        
        return filepath
    
    def run_lean_roundtrip(self, input_file: Path, output_file: Path) -> Tuple[bool, str]:
        """
        Run Lean script to parse and serialize back.
        Returns (success, error_message)
        """
        try:
            # Use absolute path to lake
            lake_path = Path.home() / ".elan" / "bin" / "lake"
            result = subprocess.run(
                [str(lake_path), "env", "lean", "--run", str(self.lean_script), 
                 str(input_file), str(output_file)],
                capture_output=True,
                text=True,
                timeout=30,
                cwd=Path.cwd()  # Ensure we're in project root
            )
            
            if result.returncode != 0:
                return False, f"Lean failed: {result.stderr}"
            
            if not output_file.exists():
                return False, f"Output file not created: {output_file}"
            
            return True, ""
            
        except subprocess.TimeoutExpired:
            return False, "Lean script timed out"
        except Exception as e:
            return False, f"Exception: {str(e)}"
    
    def load_qgraph(self, filepath: Path) -> Optional[zx.Graph]:
        """Load .qgraph file into PyZX"""
        try:
            with open(filepath, 'r') as f:
                g = zx.Graph.from_json(f.read())
                # Auto-detect inputs/outputs from boundary vertices
                g.auto_detect_io()
                return g
        except Exception as e:
            print(f"  {RED}✗{RESET} Failed to load {filepath.name}: {e}")
            return None
    
    def compare_graphs(self, g1: zx.Graph, g2: zx.Graph, name: str) -> Tuple[bool, str]:
        """
        Compare two PyZX graphs for equivalence.
        Returns (equivalent, details)
        """
        try:
            # Basic structural checks (inputs() and outputs() are methods)
            if len(g1.inputs()) != len(g2.inputs()):
                return False, f"Input count mismatch: {len(g1.inputs())} vs {len(g2.inputs())}"
            
            if len(g1.outputs()) != len(g2.outputs()):
                return False, f"Output count mismatch: {len(g1.outputs())} vs {len(g2.outputs())}"
            
            # Compare tensor representations
            # This is the gold standard - checks if circuits are equivalent
            t1 = g1.to_tensor()
            t2 = g2.to_tensor()
            
            if not zx.compare_tensors(t1, t2, preserve_scalar=False):
                return False, "Tensor representations differ"
            
            return True, "Graphs are equivalent"
            
        except Exception as e:
            # If tensor comparison fails, try simpler checks
            return False, f"Comparison error: {str(e)}"
    
    def test_circuit(self, name: str, circuit) -> dict:
        """Test a single circuit through the roundtrip"""
        print(f"\n{BLUE}Testing:{RESET} {name}")
        print("  " + "─" * 60)
        
        result = {
            "name": name,
            "passed": False,
            "error": None,
            "details": {}
        }
        
        # Step 1: Export original from PyZX
        print(f"  {YELLOW}[1/4]{RESET} Exporting from PyZX...")
        original_file = self.export_pyzx_circuit(circuit, name)
        print(f"        → {original_file.name}")
        
        # Step 2: Run Lean roundtrip
        print(f"  {YELLOW}[2/4]{RESET} Running Lean roundtrip...")
        output_file = self.test_dir / f"{name}_roundtrip.qgraph"
        success, error = self.run_lean_roundtrip(original_file, output_file)
        
        if not success:
            result["error"] = error
            print(f"        {RED}✗{RESET} {error}")
            return result
        
        print(f"        → {output_file.name}")
        
        # Step 3: Load both graphs
        print(f"  {YELLOW}[3/4]{RESET} Loading graphs...")
        g_original = self.load_qgraph(original_file)
        g_roundtrip = self.load_qgraph(output_file)
        
        if g_original is None or g_roundtrip is None:
            result["error"] = "Failed to load graphs"
            return result
        
        result["details"]["original_vertices"] = len(g_original.vertices())
        result["details"]["original_edges"] = len(list(g_original.edges()))
        result["details"]["roundtrip_vertices"] = len(g_roundtrip.vertices())
        result["details"]["roundtrip_edges"] = len(list(g_roundtrip.edges()))
        
        print(f"        Original:  {result['details']['original_vertices']} vertices, "
              f"{result['details']['original_edges']} edges")
        print(f"        Roundtrip: {result['details']['roundtrip_vertices']} vertices, "
              f"{result['details']['roundtrip_edges']} edges")
        
        # Step 4: Compare equivalence
        print(f"  {YELLOW}[4/4]{RESET} Checking equivalence...")
        equivalent, details = self.compare_graphs(g_original, g_roundtrip, name)
        
        result["passed"] = equivalent
        result["details"]["comparison"] = details
        
        if equivalent:
            print(f"        {GREEN}✓{RESET} {details}")
        else:
            print(f"        {RED}✗{RESET} {details}")
            result["error"] = details
        
        return result
    
    def run_all_tests(self):
        """Run all roundtrip tests"""
        print(f"{BLUE}{'=' * 70}{RESET}")
        print(f"{BLUE}PyZX → Lean → PyZX Roundtrip Tests{RESET}")
        print(f"{BLUE}{'=' * 70}{RESET}")
        
        print(f"\nTest directory: {self.test_dir}")
        print(f"Lean script: {self.lean_script}")
        
        if not self.lean_script.exists():
            print(f"\n{RED}Error:{RESET} Lean script not found: {self.lean_script}")
            print("Creating it now...")
            self.create_lean_script()
        
        circuits = self.get_all_circuits()
        print(f"\nRunning {len(circuits)} tests...")
        
        for name, circuit in circuits.items():
            result = self.test_circuit(name, circuit)
            self.results.append(result)
        
        self.print_summary()
        
        return all(r["passed"] for r in self.results)
    
    def run_single_test(self, circuit_name: str):
        """Run a single circuit test by name"""
        print(f"{BLUE}{'=' * 70}{RESET}")
        print(f"{BLUE}Testing Single Circuit: {circuit_name}{RESET}")
        print(f"{BLUE}{'=' * 70}{RESET}")
        
        print(f"\nTest directory: {self.test_dir}")
        print(f"Lean script: {self.lean_script}")
        
        if not self.lean_script.exists():
            print(f"\n{RED}Error:{RESET} Lean script not found: {self.lean_script}")
            return False
        
        # Get the circuit builder method
        method_name = f"circuit_{circuit_name}"
        if not hasattr(self, method_name):
            print(f"\n{RED}Error:{RESET} Unknown circuit: {circuit_name}")
            print(f"Available circuits: {', '.join(self.get_all_circuits().keys())}")
            return False
        
        circuit = getattr(self, method_name)()
        result = self.test_circuit(circuit_name, circuit)
        self.results.append(result)
        
        # Print result
        print(f"\n{BLUE}{'=' * 70}{RESET}")
        if result["passed"]:
            print(f"{GREEN}✓ Test passed!{RESET}")
        else:
            print(f"{RED}✗ Test failed: {result['error']}{RESET}")
        print(f"{BLUE}{'=' * 70}{RESET}\n")
        
        return result["passed"]
    
    def print_summary(self):
        """Print test summary"""
        print(f"\n{BLUE}{'=' * 70}{RESET}")
        print(f"{BLUE}Test Summary{RESET}")
        print(f"{BLUE}{'=' * 70}{RESET}\n")
        
        passed = sum(1 for r in self.results if r["passed"])
        failed = len(self.results) - passed
        
        print(f"Total:  {len(self.results)} tests")
        print(f"Passed: {GREEN}{passed}{RESET}")
        print(f"Failed: {RED}{failed}{RESET}")
        
        if failed > 0:
            print(f"\n{RED}Failed tests:{RESET}")
            for r in self.results:
                if not r["passed"]:
                    print(f"  • {r['name']}: {r['error']}")
        
        print(f"\n{BLUE}{'=' * 70}{RESET}")
        
        if failed == 0:
            print(f"{GREEN}✓ All roundtrip tests passed!{RESET}")
            print(f"{GREEN}The serializer is working correctly.{RESET}")
        else:
            print(f"{RED}✗ Some tests failed. Check details above.{RESET}")
        
        print(f"{BLUE}{'=' * 70}{RESET}\n")
    
    def create_lean_script(self):
        """Create the Lean roundtrip script if it doesn't exist"""
        content = """import ZxCalculus.Parser.QGraph

open ZxCalculus.Parser

def main (args : List String) : IO UInt32 := do
  match args with
  | [inputPath, outputPath] =>
    try
      -- Parse input .qgraph file
      let qgraph ← parseQGraphFile ⟨inputPath⟩
      
      -- Attempt to reconstruct ZxTerm
      match reconstructZxTermSimple qgraph with
      | .error e =>
        IO.eprintln s!"Failed to reconstruct: {e}"
        return 1
      | .ok ⟨n, m, term⟩ =>
        -- Serialize back to .qgraph
        saveZxTermAsQGraph ⟨outputPath⟩ term
        return 0
    catch e =>
      IO.eprintln s!"Error: {e}"
      return 1
  | _ =>
    IO.eprintln "Usage: RoundtripLean <input.qgraph> <output.qgraph>"
    return 1
"""
        self.lean_script.parent.mkdir(parents=True, exist_ok=True)
        with open(self.lean_script, 'w') as f:
            f.write(content)
        print(f"Created {self.lean_script}")


def main():
    import argparse
    
    parser = argparse.ArgumentParser(description="PyZX → Lean → PyZX roundtrip tests")
    parser.add_argument('circuit', nargs='?', help='Test a specific circuit (e.g., hadamard, identity)')
    parser.add_argument('--list', action='store_true', help='List available circuits')
    
    args = parser.parse_args()
    
    tester = RoundtripTester()
    
    if args.list:
        print("Available circuits:")
        for name in tester.get_all_circuits().keys():
            print(f"  - {name}")
        sys.exit(0)
    
    if args.circuit:
        # Test single circuit
        success = tester.run_single_test(args.circuit)
    else:
        # Test all circuits
        success = tester.run_all_tests()
    
    sys.exit(0 if success else 1)


if __name__ == "__main__":
    main()

