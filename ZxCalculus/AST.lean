import Mathlib.Data.Rat.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
open Real

inductive Generator : ℕ → ℕ → Type
| empty : Generator 0 0 -- the empty diagram
| id : {n : ℕ} → Generator n n -- the identity generator on n wires (type n → n)
| swap : (n m : ℕ) → Generator (n + m) (m + n) -- the swap generator (type (n + m) -> (m + n))
| H : Generator 1 1 -- the hadamard generator (type 1 → 1)
| Z     : (α : Real.Angle) → (n m : ℕ) → Generator n m -- Z spider with angle α*π (type n → m)
| X     : (α : Real.Angle) → (n m : ℕ) → Generator n m -- X spider with angle α*π (type n → m)
| cup   : Generator 0 2 -- bell state (cup) (type 0 → 2)
| cap   : Generator 2 0 -- bell effect (cap) (type 2 → 0)

/--
Recursive syntax for ZX diagrams/terms
- Generators are ZX diagrams
- If A, B are ZX diagrams, then A ⊗ B is a ZX diagram
- If A, B are ZX diagrams, then A ; B is a ZX diagram
-/
inductive ZxTerm : ℕ → ℕ → Type
| gen : {n m : ℕ} → Generator n m → ZxTerm n m
| seq   : {n k m : ℕ} → ZxTerm n k → ZxTerm k m → ZxTerm n m
| tens  : {n₁ m₁ n₂ m₂ : ℕ} → ZxTerm n₁ m₁ → ZxTerm n₂ m₂ → ZxTerm (n₁ + n₂) (m₁ + m₂)

-- Notation for ZX diagrams
infixl:90 " ; " => ZxTerm.seq   -- Sequential composition
infixl:80 " ⊗ " => ZxTerm.tens  -- Tensor product

-- Define the dagger (adjoint) of a ZX term
-- Marked noncomputable because Real.Angle arithmetic isnt computable
-- This function can be used in proofs but can not evaluate as a program
-- If we need to compute with this later we can replace Real.Angle with ℝ or ℚ
-- and lose some mathematical precision
noncomputable def dagger {n m : ℕ} : ZxTerm n m → ZxTerm m n
| .gen g => match g with
  | .empty         => ZxTerm.gen Generator.empty
  | .id            => ZxTerm.gen Generator.id
  | .swap n' m'    => ZxTerm.gen (Generator.swap m' n')
  | .H             => ZxTerm.gen Generator.H
  | .Z α n' m'     => ZxTerm.gen (Generator.Z (-α) m' n')
  | .X α n' m'     => ZxTerm.gen (Generator.X (-α) m' n')
  | .cup           => ZxTerm.gen Generator.cap
  | .cap           => ZxTerm.gen Generator.cup
| .seq f g   => dagger g ; dagger f
| .tens f g  => dagger f ⊗ dagger g


-- Trying non-dependent AST with separate type system

inductive Generator' : Type
| empty : Generator'
| id : ℕ → Generator'
| swap : ℕ → ℕ → Generator'
| H : Generator'
| Z : Real.Angle → ℕ → ℕ → Generator'
| X : Real.Angle → ℕ → ℕ → Generator'
| cup : Generator'
| cap : Generator'

inductive ZxTerm' : Type
| gen : Generator' → ZxTerm'
| comp : ZxTerm' → ZxTerm' → ZxTerm'
| tens : ZxTerm' → ZxTerm' → ZxTerm'

namespace ZxTerm'

def empty : ZxTerm' := ZxTerm'.gen Generator'.empty

def idn (n : ℕ) : ZxTerm' := ZxTerm'.gen (Generator'.id n)

def swap (n m : ℕ) : ZxTerm' := ZxTerm'.gen (Generator'.swap n m)

def H : ZxTerm' := ZxTerm'.gen Generator'.H

def Z (α : Real.Angle) (n m : ℕ) : ZxTerm' := ZxTerm'.gen (Generator'.Z α n m)

def X (α : Real.Angle) (n m : ℕ) : ZxTerm' := ZxTerm'.gen (Generator'.X α n m)

def cup : ZxTerm' := ZxTerm'.gen Generator'.cup

def cap : ZxTerm' := ZxTerm'.gen Generator'.cap

end ZxTerm'

open ZxTerm'

infixl:90 " ; " => comp
infixl:80 " ⊗ " => tens

noncomputable def dagger' : ZxTerm' → ZxTerm'
| .gen g => match g with
  | .empty         => empty
  | .id n          => idn n
  | .swap n m      => swap m n
  | .H             => H
  | .Z α n m       => Z (- α) m n
  | .X α n m       => X (- α) m n
  | .cup           => cap
  | .cap           => cup
| f ; g  => dagger' g ; dagger' f
| f ⊗ g  => dagger' f ⊗ dagger' g

inductive hasType : ZxTerm' → ℕ → ℕ → Prop where
| empty : hasType empty 0 0
| idn : ∀ n, hasType (idn n) n n
| swap : ∀ n m, hasType (swap n m) m n
| hadamard : hasType H 1 1
| Zspider : ∀ α n m, hasType (Z α n m) n m
| Xspider : ∀ α n m, hasType (X α n m) n m
| bellState : hasType cup 0 2
| bellEffect : hasType cap 2 0
