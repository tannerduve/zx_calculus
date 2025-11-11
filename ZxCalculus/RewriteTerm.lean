/-
# ZX-Calculus Rewrite Rules

This file defines the equational theory of the ZX-calculus, a graphical language
for reasoning about quantum circuits and linear maps.

## Main Definitions

- `tensor_pow`: Helper function to tensor a diagram with itself k times
- `ZxEquiv`: Inductive type encoding the ZX-calculus rewrite rules as an equivalence relation

## Axioms

The ZX-calculus equivalence includes:
1. **Equivalence structure**: reflexivity, symmetry, transitivity
2. **Congruence**: compatibility with sequential and parallel composition
3. **Structural axioms**: monoidal category laws (associativity, units, interchange)
4. **ZX-specific rules**: spider fusion, color change (Hadamard conjugation), π-copy rules
-/

import ZxCalculus.AST
import Mathlib.Logic.Relation
open Real Relation ZxTerm

/--
Tensor a diagram with itself k times.
For a diagram `d : ZxTerm n m`, `tensor_pow d k` produces a diagram of type `ZxTerm (k*n) (k*m)`.
Uses `simpa` to handle definitional equality issues with natural number arithmetic.
-/
def tensor_pow {n m : ℕ} (d : ZxTerm n m) : (k : ℕ) → ZxTerm (k * n) (k * m)
| 0 => by
    simpa [Nat.zero_mul] using (empty : ZxTerm 0 0)
| 1 => by
    simpa [Nat.one_mul] using d
| k + 1 => by
    simpa [Nat.succ_eq_add_one, Nat.succ_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (d.tens (tensor_pow d k))

/--
ZX-calculus equivalence relation.

This inductive type defines when two ZX diagrams are equivalent under the ZX-calculus rewrite rules.
The relation combines:
- Standard equivalence relation structure (reflexivity, symmetry, transitivity)
- Congruence with respect to sequential (`;`) and parallel (`⊗`) composition
- Structural axioms from symmetric monoidal categories ("only topology matters")
- ZX-calculus specific rewrite rules (spider fusion, color change, etc.)

Many constructors use `simpa` to resolve type equalities arising from non-definitional
equalities of natural number arithmetic (e.g., `(n₁+n₂)+n₃` vs `n₁+(n₂+n₃)`).
-/
inductive ZxEquiv : {n m : ℕ} → ZxTerm n m → ZxTerm n m → Prop
-- Equivalence relation structure
| refl : ∀ {n m} (f : ZxTerm n m), ZxEquiv f f
| symm : ∀ {n m} {f g : ZxTerm n m}, ZxEquiv f g → ZxEquiv g f
| trans : ∀ {n m} {f g h : ZxTerm n m}, ZxEquiv f g → ZxEquiv g h → ZxEquiv f h

-- Congruence rules: equivalence respects composition
| seq_cong : ∀ {n k m} {f f' : ZxTerm n k} {g g' : ZxTerm k m},
    ZxEquiv f f' → ZxEquiv g g' → ZxEquiv (f.comp g) (f'.comp g')
| tens_cong : ∀ {n₁ m₁ n₂ m₂} {f f' : ZxTerm n₁ m₁} {g g' : ZxTerm n₂ m₂},
    ZxEquiv f f' → ZxEquiv g g' → ZxEquiv (f.tens g) (f'.tens g')

-- Structural axioms: symmetric monoidal category (SMC) laws
/-- Sequential composition is associative: `(f ; g) ; h = f ; (g ; h)` -/
| assoc_comp : ∀ {n k l m} (f : ZxTerm n k) (g : ZxTerm k l) (h : ZxTerm l m),
    ZxEquiv ((f.comp g).comp h) (f.comp (g.comp h))

/-- Tensor product is associative: `(f ⊗ g) ⊗ h = f ⊗ (g ⊗ h)` -/
| assoc_tens : ∀ {n₁ m₁ n₂ m₂ n₃ m₃}
    (f : ZxTerm n₁ m₁) (g : ZxTerm n₂ m₂) (h : ZxTerm n₃ m₃),
    ZxEquiv
      (by simpa [Nat.add_assoc] using ((f.tens g).tens h))
      (by simpa [Nat.add_assoc] using (f.tens (g.tens h)))

/-- Identity is left unit for composition: `id ; f = f` -/
| unit_comp_l : ∀ (f : ZxTerm 1 1), ZxEquiv (id.comp f) f

/-- Identity is right unit for composition: `f ; id = f` -/
| unit_comp_r : ∀ (f : ZxTerm 1 1), ZxEquiv (f.comp id) f

/-- Empty diagram is left unit for tensor: `empty ⊗ f = f` -/
| unit_tens_l : ∀ {n m} (f : ZxTerm n m), ZxEquiv
    (by simpa [Nat.zero_add] using (empty.tens f))
    f

/-- Empty diagram is right unit for tensor: `f ⊗ empty = f` -/
| unit_tens_r : ∀ {n m} (f : ZxTerm n m), ZxEquiv
    (by simpa [Nat.add_zero] using (f.tens empty))
    f

/-- Interchange law: `(f ⊗ g) ; (f' ⊗ g') = (f ; f') ⊗ (g ; g')` -/
| interchange : ∀ {n₁ k₁ m₁ n₂ k₂ m₂}
    (f : ZxTerm n₁ k₁) (f' : ZxTerm k₁ m₁) (g : ZxTerm n₂ k₂) (g' : ZxTerm k₂ m₂),
    ZxEquiv ((f.tens g).comp (f'.tens g')) ((f.comp f').tens (g.comp g'))

-- ZX-calculus specific rewrite rules

/-- Spider fusion for Z spiders: composing Z spiders adds their phases -/
| z_fus : ∀ {n m k} (α β : ℚ), ZxEquiv
    ((Z α n m).comp (Z β m k))
    (Z (α + β) n k)

/-- Spider fusion for X spiders: composing X spiders adds their phases -/
| x_fus : ∀ {n m k} (α β : ℚ), ZxEquiv
    ((X α n m).comp (X β m k))
    (X (α + β) n k)

/-- A Z spider with phase 0 and arity (1,1) is the identity -/
| z_id : ZxEquiv (Z 0 1 1) id

/-- An X spider with phase 0 and arity (1,1) is the identity -/
| x_id : ZxEquiv (X 0 1 1) id

/-- Color change: Hadamard conjugation converts Z spiders to X spiders -/
| color_change_Z : ∀ (α : ℚ) (n m : ℕ), ZxEquiv
    (((tensor_pow H n).comp (by simpa [Nat.add_zero] using (Z α n m))).comp (tensor_pow H m))
    (by simpa [Nat.add_zero] using (X α n m))

/-- Color change: Hadamard conjugation converts X spiders to Z spiders -/
| color_change_X : ∀ (α : ℚ) (n m : ℕ), ZxEquiv
    (((tensor_pow H n).comp (by simpa [Nat.add_zero] using (X α n m))).comp (tensor_pow H m))
    (by simpa [Nat.add_zero] using (Z α n m))

-- π-copy rules: spiders with phase π can "copy through" opposite-color spiders with phase negation
/-- π-copy for X through Z: an X-π spider commutes with a Z spider, negating the phase -/
| z_pi_copy_simple : ∀ {α}, ZxEquiv
    ((X 1 1 1).comp (Z α 1 1))
    ((Z (-α) 1 1).comp (X 1 1 1))

/-- π-copy for Z through X: a Z-π spider commutes with an X spider, negating the phase -/
| x_pi_copy_simple : ∀ {α}, ZxEquiv
    ((Z 1 1 1).comp (X α 1 1))
    ((X (-α) 1 1).comp (Z 1 1 1))

-- TODO: Additional rules to implement
-- - Bialgebra rule: (Z⊗Z) ; swap ; (X⊗X) = (X⊗X) ; swap ; (Z⊗Z)
-- - Euler decomposition: H = Z(π/2) ; X(π/2) ; Z(π/2)
-- - Hopf algebra rules (cup/cap interactions with spiders)
