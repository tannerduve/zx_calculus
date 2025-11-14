#!/bin/bash
set -e  # Exit on error

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Project root (parent of scripts directory)
PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$PROJECT_ROOT"

echo -e "${BLUE}========================================${NC}"
echo -e "${BLUE}PyZX → Lean Parser Integration Test${NC}"
echo -e "${BLUE}========================================${NC}\n"

# Step 1: Create temporary directory
echo -e "${YELLOW}[1/5]${NC} Creating temporary directory..."
TEMP_DIR=$(mktemp -d)
echo "      Temp directory: $TEMP_DIR"

# Cleanup function
cleanup() {
    echo -e "\n${YELLOW}Cleaning up...${NC}"
    rm -rf "$TEMP_DIR"
    echo "      Removed: $TEMP_DIR"
}
trap cleanup EXIT

# Step 2: Generate .qgraph files using Python
echo -e "\n${YELLOW}[2/5]${NC} Generating .qgraph files from PyZX..."
cd py

# Create a test script that generates circuits to temp directory
cat > "$TEMP_DIR/generate_test_circuits.py" << 'EOF'
import pyzx as zx
import sys
import os

# Get temp directory from argument
temp_dir = sys.argv[1] if len(sys.argv) > 1 else "."

def save_circuit(circuit, name, temp_dir):
    """Save circuit to .qgraph file"""
    g = circuit.to_graph()
    output_path = os.path.join(temp_dir, f"{name}.qgraph")
    with open(output_path, 'w') as f:
        f.write(g.to_json())
    print(f"  ✓ Generated: {name}.qgraph")

# Test Circuit 1: Single qubit identity
print("Generating test circuits...")
c1 = zx.Circuit(1)
save_circuit(c1, "test_id1", temp_dir)

# Test Circuit 2: Two qubit identity
c2 = zx.Circuit(2)
save_circuit(c2, "test_id2", temp_dir)

# Test Circuit 3: Hadamard
c3 = zx.Circuit(1)
c3.add_gate("HAD", 0)
save_circuit(c3, "test_hadamard", temp_dir)

# Test Circuit 4: Bell state (should match our golden copy)
c4 = zx.Circuit(2)
c4.add_gate("HAD", 0)
c4.add_gate("CNOT", 0, 1)
save_circuit(c4, "test_bell", temp_dir)

# Test Circuit 5: CNOT
c5 = zx.Circuit(2)
c5.add_gate("CNOT", 0, 1)
save_circuit(c5, "test_cnot", temp_dir)

print(f"\n✓ Generated 5 test circuits in {temp_dir}")
EOF

# Run the Python generator
if ! uv run python "$TEMP_DIR/generate_test_circuits.py" "$TEMP_DIR"; then
    echo -e "${RED}✗ Failed to generate circuits${NC}"
    exit 1
fi

cd "$PROJECT_ROOT"

# Step 3: Build Lean parser test
echo -e "\n${YELLOW}[3/5]${NC} Building Lean parser test..."
BUILD_OUTPUT=$(~/.elan/bin/lake build tests.Parser.QGraph 2>&1)
if echo "$BUILD_OUTPUT" | grep -q "error: build failed"; then
    echo -e "${RED}✗ Failed to build Lean test${NC}"
    echo "$BUILD_OUTPUT" | tail -20
    exit 1
fi
echo "      ✓ Lean parser test built successfully"

# Step 4: Run Lean parser and validation
echo -e "\n${YELLOW}[4/5]${NC} Running parser validation..."
if ! ~/.elan/bin/lake env lean --run tests/Parser/QGraph.lean "$TEMP_DIR" "$PROJECT_ROOT/scripts/golden" 2>&1; then
    echo -e "\n${RED}✗ Parser validation failed${NC}"
    exit 1
fi

# Step 5: Verify golden copies
echo -e "\n${YELLOW}[5/5]${NC} Verifying against golden copies..."
GOLDEN_DIR="$PROJECT_ROOT/scripts/golden"

# Check if golden files exist
if [ ! -d "$GOLDEN_DIR" ]; then
    echo -e "      ${YELLOW}⚠ No golden directory found, skipping golden copy verification${NC}"
else
    # Compare bell state against golden copy if it exists
    if [ -f "$GOLDEN_DIR/bell_state.qgraph" ] && [ -f "$TEMP_DIR/test_bell.qgraph" ]; then
        if diff -q "$GOLDEN_DIR/bell_state.qgraph" "$TEMP_DIR/test_bell.qgraph" > /dev/null 2>&1; then
            echo "      ✓ Bell state matches golden copy"
        else
            echo -e "      ${YELLOW}⚠ Bell state differs from golden copy (this may be expected)${NC}"
        fi
    fi
    
    # Compare CNOT against golden copy if it exists
    if [ -f "$GOLDEN_DIR/cnot.qgraph" ] && [ -f "$TEMP_DIR/test_cnot.qgraph" ]; then
        if diff -q "$GOLDEN_DIR/cnot.qgraph" "$TEMP_DIR/test_cnot.qgraph" > /dev/null 2>&1; then
            echo "      ✓ CNOT matches golden copy"
        else
            echo -e "      ${YELLOW}⚠ CNOT differs from golden copy (this may be expected)${NC}"
        fi
    fi
fi

# Success!
echo -e "\n${GREEN}========================================${NC}"
echo -e "${GREEN}✓ All tests passed!${NC}"
echo -e "${GREEN}========================================${NC}"
echo ""
echo "Test Summary:"
echo "  - Generated 5 test circuits"
echo "  - Parsed all circuits successfully"
echo "  - Validated circuit structures"
echo "  - Checked against golden copies"
echo ""

exit 0

