import ZxCalculus.AST
import Mathlib.Logic.Relation
open Real

open ZxTerm'

/-- Diagram tensored with itself n times. -/
def pow (n : ℕ) (zx : ZxTerm') : ZxTerm' :=
match n with
| 0     => idn 0
| n+1   => pow n zx ⊗ zx

def midSwap4 : ZxTerm' :=
  ((idn 1 ⊗ swap 1 1) ⊗ idn 1)

noncomputable def multPi (a : ℤ) : Real.Angle := a • π

-- Rewrite system for non dependent AST
inductive rewrites : ZxTerm' → ZxTerm' → Prop
-- Composing two Z spiders fuses them and adds their phases
| z_fus {α β n m k} : rewrites (Z α n m ; Z β m k) (Z (α + β) n k)
-- Composing two X spiders fuses them and adds their phases
| x_fus {α β n m k} : rewrites (X α n m ; X β m k) (X (α + β) n k)
-- A phaseless arity 2 Z- or X-spider is equal to the identity
| z_id : rewrites (Z 0 1 1) (idn 1)
| x_id : rewrites (X 0 1 1) (idn 1)
-- The Hadamard-gate changes the color of spiders
| Z_color_change {α n m} : rewrites ((pow n H); Z α n m; (pow m H)) (X α n m)
| X_color_change {α n m} : rewrites ((pow n H); X α n m; (pow m H)) (Z α n m)
-- Copy rules: Z-spider copies X-spiders, X-spider copies Z-spiders
| Z_copy {α n} {a : ℤ} :
  rewrites
    ((X ((a : ℝ) * (π : ℝ)) 0 1); (Z α 1 n))
    (pow n (X ((a : ℝ) * (π : ℝ)) 0 1))
| X_copy {α n} {a : ℤ} :
  rewrites
    ((Z ((a : ℝ) * (π : ℝ)) 0 1); (X α 1 n))
    (pow n (Z ((a : ℝ) * (π : ℝ)) 0 1))
-- A 2-cycle of Z- and X-spiders simplifies
| bialgebra
    : rewrites
        ( (Z 0 1 2 ⊗ Z 0 1 2) ; midSwap4 ; (X 0 2 1 ⊗ X 0 2 1) )
        ( (X 0 1 2 ⊗ X 0 1 2) ; midSwap4 ; (Z 0 2 1 ⊗ Z 0 2 1) )
-- π-copy: NOT-gate copies through and flips phase (both color combinations)
| Z_pi_copy {α n} : rewrites ((X π 1 1); (Z α 1 n)) ((Z (-α) 1 n); (pow n (X π 1 1)))
| X_pi_copy {α n} : rewrites ((Z π 1 1); (X α 1 n)) ((X (-α) 1 n); (pow n (Z π 1 1)))
-- A Hadamard-gate can be expanded into three rotations around the Bloch sphere.
| euler_decomp : rewrites H (Z (π / (2 : ℝ)) 0 1 ; X (π / (2 : ℝ)) 1 1 ; Z (π / (2 : ℝ)) 1 0)
-- -- Z-comult followed by X-mult deletes the pair of wires
-- | hopf_ZX : rewrites (Z 0 1 2 ; X 0 2 1) (idn 1)
-- -- Symmetric version (colors swapped)
-- | hopf_XZ : rewrites (X 0 1 2 ; Z 0 2 1) (idn 1)

/-- Structural equality: diagrams are equal up to SMC + compact-closure laws. -/
inductive Struc₀ : ZxTerm' → ZxTerm' → Prop
| refl  : ∀ f, Struc₀ f f
| symm  : ∀ {f g}, Struc₀ f g → Struc₀ g f
| trans : ∀ {f g h}, Struc₀ f g → Struc₀ g h → Struc₀ f h
-- congruence
| comp  : ∀ {f f' g g'}, Struc₀ f f' → Struc₀ g g' → Struc₀ (f ; g) (f' ; g')
| tens  : ∀ {f f' g g'}, Struc₀ f f' → Struc₀ g g' → Struc₀ (f ⊗ g) (f' ⊗ g')
-- strict associativity (choose a normalization)
| assoc_comp : ∀ f g h, Struc₀ ((f ; g) ; h) (f ; (g ; h))
| assoc_tens : ∀ f g h, Struc₀ ((f ⊗ g) ⊗ h) (f ⊗ (g ⊗ h))
-- tensor unit (0 wires, i.e. `idn 0`)
| unit_tens_l : ∀ f, Struc₀ (idn 0 ⊗ f) f
| unit_tens_r : ∀ f, Struc₀ (f ⊗ idn 0) f
-- symmetry (braiding) : naturality + involutivity
| swap_nat
    {m n f g} :
    hasType f m m → hasType g n n →
    Struc₀ ((f ⊗ g) ; swap m n) (swap m n ; (g ⊗ f))
| swap_inv {m n} : Struc₀ (swap m n ; swap n m) (idn (m + n))
-- compact-closure (yanking/snake); here for one wire each side
| snake_L : Struc₀ ((idn 1 ⊗ cap) ; (cup ⊗ idn 1)) (idn 1)
| snake_R : Struc₀ ((cap ⊗ idn 1) ; (idn 1 ⊗ cup)) (idn 1)
| interchange {f f' g g'} :
    Struc₀ ((f ⊗ g) ; (f' ⊗ g')) ((f ; f') ⊗ (g ; g'))

-- smallest *equivalence* containing Struc₀ (refl/symm/trans)
def Struc : ZxTerm' → ZxTerm' → Prop := Relation.EqvGen Struc₀

def rcomp {α : Type*} (r s : α → α → Prop) : α → α → Prop :=
  fun x z => ∃ y, r x y ∧ s y z

infixr:60 " ⨾ " => rcomp

-- The final rewrite relation encoding the rewrite rules as well as "only topology matters"
def Step : ZxTerm' → ZxTerm' → Prop :=
  (Struc) ⨾ (rewrites) ⨾ (Struc)
