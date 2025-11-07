import ZxCalculus.AST
open Real

/-- n-wire identity as a term (handy shorthands). -/
def idn (n : ℕ) : ZxTerm n n := ZxTerm.gen Generator.id

/-- H tensored n times. -/
def Hpow : (n : ℕ) → ZxTerm n n
| 0     => idn 0
| n+1   => Hpow n ⊗ ZxTerm.gen Generator.H

/-- Transport a `ZxTerm` across equal domain/codomain indices. -/
def castZx {n n' m m'} (hn : n = n') (hm : m = m') :
    ZxTerm n m → ZxTerm n' m'
| t =>
  match hn, hm with
  | rfl, rfl => t


/-- Primitive ZX axioms (schematic, arity-indexed). -/
inductive ZXAx : ∀ {n m}, ZxTerm n m → ZxTerm n m → Prop
| z_fuse {n k m} (α β) :
    ZXAx (ZxTerm.gen (Generator.Z α n k) ; ZxTerm.gen (Generator.Z β k m))
         (ZxTerm.gen (Generator.Z (α + β) n m))
| x_fuse {n k m} (α β) :
    ZXAx (ZxTerm.gen (Generator.X α n k) ; ZxTerm.gen (Generator.X β k m))
         (ZxTerm.gen (Generator.X (α + β) n m))
| z_id :
    ZXAx (ZxTerm.gen (Generator.Z 0 1 1)) (idn 1)
| x_id :
    ZXAx (ZxTerm.gen (Generator.X 0 1 1)) (idn 1)
| color_change {n m} (α) :
    -- H on every incident leg
    ZXAx (Hpow n ; ZxTerm.gen (Generator.Z α n m) ; Hpow m)
         (ZxTerm.gen (Generator.X α n m))
/-- Compact-closure “yanking” (snake) equations. -/
| snake_right (n : ℕ) :
    ZXAx
      ( ((ZxTerm.gen (Generator.cup : Generator 0 2)) ⊗ idn n)
        ;
        ZxTerm.gen (Generator.swap 2 n)          -- (2+n) ⟶ (n+2)
        ;
        (idn n ⊗ ZxTerm.gen (Generator.cap : Generator 2 0)) )
      ( castZx (by simp) (by simp) (idn n) )

| snake_left (n : ℕ) :
    ZXAx
      ( (idn n ⊗ ZxTerm.gen (Generator.cup : Generator 0 2))
        ;
        ZxTerm.gen (Generator.swap n 2)           -- (n+2) ⟶ (2+n)
        ;
        (ZxTerm.gen (Generator.cap : Generator 2 0) ⊗ idn n) )
      ( castZx (by simp) (by simp) (idn n) )
/-- Bialgebra (small-arity interaction) — as you had. -/
| bialgebra :
    ZXAx
      (ZxTerm.gen (Generator.Z 0 2 1) ; ZxTerm.gen (Generator.X 0 1 2))
      (ZxTerm.gen (Generator.X 0 2 1) ; ZxTerm.gen (Generator.Z 0 1 2))
/-- Copy rule (arity-1 X copies through Z-copy). -/
| copy (α) :
    ZXAx
      (ZxTerm.gen (Generator.X α 1 1) ; ZxTerm.gen (Generator.Z 0 1 2))
      (ZxTerm.gen (Generator.Z 0 1 2) ;
       (ZxTerm.gen (Generator.X α 1 1) ⊗ ZxTerm.gen (Generator.X α 1 1)))
/-- π-copy: NOT gate (X_π) copies through Z-spider and flips its phase. -/
| pi_copy (α : Real.Angle) :
    ZXAx
      (ZxTerm.gen (Generator.X (π : ℝ) 1 1) ; ZxTerm.gen (Generator.Z α 1 1))
      (ZxTerm.gen (Generator.Z (-α) 1 1) ; ZxTerm.gen (Generator.X (π : Real.Angle) 1 1))

/-- Contextual closure. -/
inductive ZXStep : ∀ {n m}, ZxTerm n m → ZxTerm n m → Prop
| ax   {n m : ℕ} {t u} (h : ZXAx t u) : ZXStep t u
| seqL {n k m} {f f' : ZxTerm n k} {g : ZxTerm k m} :
    ZXStep f f' → ZXStep (f ; g) (f' ; g)
| seqR {n k m} {f : ZxTerm n k} {g g' : ZxTerm k m} :
    ZXStep g g' → ZXStep (f ; g) (f ; g')
| tensL {n₁ m₁ n₂ m₂} {f f' : ZxTerm n₁ m₁} {g : ZxTerm n₂ m₂} :
    ZXStep f f' → ZXStep (f ⊗ g) (f' ⊗ g)
| tensR {n₁ m₁ n₂ m₂} {f : ZxTerm n₁ m₁} {g g' : ZxTerm n₂ m₂} :
    ZXStep g g' → ZXStep (f ⊗ g) (f ⊗ g')
