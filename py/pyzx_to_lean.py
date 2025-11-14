#!/usr/bin/env python3
"""
PyZX to .qgraph Serializer

Uses PyZX's native Quantomatic .qgraph JSON format for export to Lean.

The .qgraph format is PyZX's standard serialization via:
  - g.to_json() -> JSON string in .qgraph format
  - g.to_dict() -> Python dict (same structure)
  
Lean will parse this JSON and reconstruct ZxTerm AST.

=============================================================================
LEAN AST REFERENCE (from ZxCalculus/AST.lean)
=============================================================================

GENERATORS (Generator : ℕ → ℕ → Type):
  | empty : Generator 0 0
      -- The empty diagram with no wires
  
  | id : Generator 1 1
      -- Identity wire (does nothing)
  
  | swap (n m : ℕ) : Generator (n + m) (m + n)
      -- Swap/permutation: exchanges n wires with m wires
  
  | H : Generator 1 1
      -- Hadamard gate: rotates between Z and X bases
  
  | Z (α : ℚ) (n m : ℕ) : Generator n m
      -- Green spider (Z-basis) with phase α*π, n inputs, m outputs
  
  | X (α : ℚ) (n m : ℕ) : Generator n m
      -- Red spider (X-basis) with phase α*π, n inputs, m outputs
  
  | cup : Generator 0 2
      -- Cup (creates Bell state): 0 → 2
  
  | cap : Generator 2 0
      -- Cap (Bell measurement): 2 → 0

ZX TERMS (ZxTerm : ℕ → ℕ → Type):
  | gen {n m : ℕ} (g : Generator n m) : ZxTerm n m
      -- Lift a generator to a diagram
  
  | comp {n k m : ℕ} (A : ZxTerm n k) (B : ZxTerm k m) : ZxTerm n m
      -- Sequential composition: connect outputs of A to inputs of B
      -- Notation: A ; B
  
  | tens {n₁ m₁ n₂ m₂ : ℕ} (A : ZxTerm n₁ m₁) (B : ZxTerm n₂ m₂) : ZxTerm (n₁ + n₂) (m₁ + m₂)
      -- Parallel composition (tensor): place A and B side by side
      -- Notation: A ⊗ B

DAGGER (adjoint/transpose):
  dagger : ZxTerm n m → ZxTerm m n
  Notation: A†
  
  Rules:
    - Swaps inputs and outputs
    - Negates phases on spiders: (Z α n m)† = Z (-α) m n
    - Swaps cup ↔ cap
    - Reverses composition: (A ; B)† = B† ; A†
    - Preserves tensor: (A ⊗ B)† = A† ⊗ B†

PHASES:
  - Represented as rational coefficients α where actual phase is α*π
  - Example: α = 1/4 means phase is π/4

=============================================================================
"""
from typing import Dict, List, Tuple, Set, Any
from fractions import Fraction
import json
import pyzx as zx


class PyZXToQGraphConverter:
    """
    Minimal wrapper around PyZX's native .qgraph serialization.
    
    PyZX already has:
      - g.to_json() -> .qgraph JSON string
      - g.to_dict() -> .qgraph as Python dict
    
    This class just provides convenient save/load helpers.
    """
    
    def __init__(self):
        pass
    
    def graph_to_qgraph(self, g: zx.Graph) -> Dict[str, Any]:
        """
        Use PyZX's native .qgraph serialization.
        Just calls g.to_dict().
        """
        return g.to_dict()
    
    def circuit_to_qgraph(self, circuit: zx.Circuit, simplify: bool = False) -> Dict[str, Any]:
        """
        Convert circuit to .qgraph format.
        
        Args:
            circuit: PyZX circuit
            simplify: Whether to apply ZX simplification rules first
        """
        g = circuit.to_graph()
        if simplify:
            zx.simplify.full_reduce(g)
        return g.to_dict()
    
    def save_qgraph(self, g: zx.Graph, filename: str):
        """Save PyZX graph as .qgraph JSON file."""
        with open(filename, 'w') as f:
            f.write(g.to_json())
        print(f"Saved .qgraph to {filename}")
    
    def save_circuit_to_file(self, circuit: zx.Circuit, filename: str, simplify: bool = False):
        """Save PyZX circuit as .qgraph JSON file."""
        g = circuit.to_graph()
        if simplify:
            zx.simplify.full_reduce(g)
        self.save_qgraph(g, filename)


# Helper functions for common quantum circuits

def create_hadamard() -> zx.Graph:
    """Create a Hadamard gate graph."""
    g = zx.Graph()
    v_in = g.add_vertex(zx.VertexType.BOUNDARY, 0, 0)
    v_h = g.add_vertex(zx.VertexType.Z, 0, 1, phase=0)  # H box
    v_out = g.add_vertex(zx.VertexType.BOUNDARY, 0, 2)
    g.add_edge((v_in, v_h))
    g.add_edge((v_h, v_out))
    return g

def create_cnot() -> zx.Circuit:
    """Create a CNOT circuit."""
    c = zx.Circuit(2)
    c.add_gate("CNOT", 0, 1)
    return c

def create_bell_state() -> zx.Circuit:
    """Create a Bell state preparation circuit."""
    c = zx.Circuit(2)
    c.add_gate("HAD", 0)
    c.add_gate("CNOT", 0, 1)
    return c

def create_ghz_state(n_qubits: int = 3) -> zx.Circuit:
    """Create a GHZ state preparation circuit."""
    c = zx.Circuit(n_qubits)
    c.add_gate("HAD", 0)
    for i in range(1, n_qubits):
        c.add_gate("CNOT", 0, i)
    return c


def main():
    """Example: Export PyZX circuits to .qgraph format."""
    converter = PyZXToQGraphConverter()
    
    print("="*70)
    print("PyZX Native .qgraph Export Examples")
    print("="*70)
    
    # Example 1: Bell State
    print("\n1. Bell State Circuit:")
    bell = create_bell_state()
    converter.save_circuit_to_file(bell, "bell_state.qgraph")
    print("   Saved to bell_state.qgraph")
    
    # Example 2: CNOT
    print("\n2. CNOT Gate:")
    cnot = create_cnot()
    converter.save_circuit_to_file(cnot, "cnot.qgraph")
    print("   Saved to cnot.qgraph")
    
    # Example 3: GHZ State
    print("\n3. GHZ State (3 qubits):")
    ghz = create_ghz_state(3)
    converter.save_circuit_to_file(ghz, "ghz_state.qgraph")
    print("   Saved to ghz_state.qgraph")
    
    # Show one example of the JSON structure
    print("\n4. Example .qgraph structure (Bell state):")
    bell_g = bell.to_graph()
    print(bell_g.to_json()[:500] + "...")
    
    print("\n" + "="*70)
    print("✓ .qgraph files ready for Lean parser!")
    print("  These use PyZX's native Quantomatic .qgraph format.")
    print("  Parse in Lean with: ZxCalculus/Parser/QGraph.lean")
    print("="*70)


if __name__ == "__main__":
    main()

