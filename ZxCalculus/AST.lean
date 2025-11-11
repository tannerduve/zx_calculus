import Mathlib.Data.Rat.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
open Real

/--
Syntax for the generators of the zx-calculus, represented as an inductive (aka enum) type indexed by
the number of input and output wires.
-/
-- Currently we use real numbers for phases
-- To be more mathematically precise we would use `Real.Angle` but this is noncomputable
-- (ie. usable for proofs but can't execute the code)
inductive Generator : ℕ → ℕ → Type
| empty : Generator 0 0 -- the empty diagram
| id    :  Generator 1 1 -- the identity generator
| swap  : (n m : ℕ) → Generator (n + m) (m + n) -- the swap generator (type (n + m) -> (m + n))
| H     : Generator 1 1 -- the hadamard generator (type 1 → 1)
| Z     : (α : ℚ) → (n m : ℕ) → Generator n m -- Z spider with angle α*π (type n → m)
| X     : (α : ℚ) → (n m : ℕ) → Generator n m -- X spider with angle α*π (type n → m)
| cup   : Generator 0 2 -- bell state (cup) (type 0 → 2)
| cap   : Generator 2 0 -- bell effect (cap) (type 2 → 0)

/--
Recursive syntax for ZX diagrams/terms
- Generators are ZX diagrams
- If A, B are ZX diagrams, then A ⊗ B is a ZX diagram
- If A, B are ZX diagrams, then A ; B is a ZX diagram
-/
inductive ZxTerm : ℕ → ℕ → Type
| gen {n m : ℕ} (g : Generator n m) : ZxTerm n m
| comp {n k m : ℕ} (A : ZxTerm n k) (B : ZxTerm k m) : ZxTerm n m
| tens {n₁ m₁ n₂ m₂ : ℕ} (A : ZxTerm n₁ m₁) (B : ZxTerm n₂ m₂) : ZxTerm (n₁ + n₂) (m₁ + m₂)

-- Notation for ZX diagrams
infixl:90 " ; " => ZxTerm.comp   -- Sequential composition
infixl:80 " ⊗ " => ZxTerm.tens  -- Tensor product

namespace ZxTerm

-- Smart constructors

def empty : ZxTerm 0 0 := ZxTerm.gen Generator.empty

def id : ZxTerm 1 1 := ZxTerm.gen Generator.id

def swap (n m : ℕ) : ZxTerm (n + m) (m + n) := ZxTerm.gen (Generator.swap n m)

def H : ZxTerm 1 1 := ZxTerm.gen Generator.H

def Z (α : ℚ) (n m : ℕ) : ZxTerm n m := ZxTerm.gen (Generator.Z α n m)

def X (α : ℚ) (n m : ℕ) : ZxTerm n m := ZxTerm.gen (Generator.X α n m)

def cup : ZxTerm 0 2 := ZxTerm.gen Generator.cup

def cap : ZxTerm 2 0 := ZxTerm.gen Generator.cap

end ZxTerm

open ZxTerm

-- Define the dagger (adjoint) of a ZX term
def dagger {n m : ℕ} : ZxTerm n m → ZxTerm m n
| .gen g => match g with
  | .empty         => ZxTerm.gen Generator.empty
  | .id            => ZxTerm.gen Generator.id
  | .swap n' m'    => ZxTerm.gen (Generator.swap m' n')
  | .H             => ZxTerm.gen Generator.H
  | .Z α n' m'     => ZxTerm.gen (Generator.Z (-α) m' n')
  | .X α n' m'     => ZxTerm.gen (Generator.X (-α) m' n')
  | .cup           => ZxTerm.gen Generator.cap
  | .cap           => ZxTerm.gen Generator.cup
| f ; g   => dagger g ; dagger f
| f ⊗ g  => dagger f ⊗ dagger g


-- Trying non-dependent AST with separate type system. Will prob deprecate

inductive Generator' : Type
| empty : Generator'
| id : Generator'
| swap : ℕ → ℕ → Generator'
| H : Generator'
| Z : Real.Angle → ℕ → ℕ → Generator'
| X : Real.Angle → ℕ → ℕ → Generator'
| cup : Generator'
| cap : Generator'

inductive ZxTerm' : Type
| gen : Generator' → ZxTerm'
| comp' : ZxTerm' → ZxTerm' → ZxTerm'
| tens' : ZxTerm' → ZxTerm' → ZxTerm'

namespace ZxTerm'

def empty : ZxTerm' := ZxTerm'.gen Generator'.empty

def id : ZxTerm' := ZxTerm'.gen Generator'.id

def swap (n m : ℕ) : ZxTerm' := ZxTerm'.gen (Generator'.swap n m)

def H : ZxTerm' := ZxTerm'.gen Generator'.H

def Z (α : Real.Angle) (n m : ℕ) : ZxTerm' := ZxTerm'.gen (Generator'.Z α n m)

def X (α : Real.Angle) (n m : ℕ) : ZxTerm' := ZxTerm'.gen (Generator'.X α n m)

def cup : ZxTerm' := ZxTerm'.gen Generator'.cup

def cap : ZxTerm' := ZxTerm'.gen Generator'.cap

end ZxTerm'

open ZxTerm'
