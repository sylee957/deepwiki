import DeepWiki.ReactiveSystems.HennessyMilner
import Mathlib.Order.FixedPoints

/-! # Mutually recursive HML systems, and mixing fixed points
§6.5 generalises HML-with-recursion to a system of mutually recursive equations
over a variable set `V`, interpreted by simultaneous greatest/least fixed points
on the product complete lattice `V → 2^Proc`. §6.7 mixes largest and least fixed
points — the livelock property (a `ν`-fixed point of `⟨τ⟩`) and the empty `μ`
solution. -/

namespace DeepWiki.ReactiveSystems

/-- HML with recursion over a variable set `V` (for mutually recursive systems). -/
inductive HMLV (V Act : Type*)
  | var : V → HMLV V Act
  | tt : HMLV V Act
  | ff : HMLV V Act
  | and : HMLV V Act → HMLV V Act → HMLV V Act
  | or : HMLV V Act → HMLV V Act → HMLV V Act
  | dia : Act → HMLV V Act → HMLV V Act
  | box : Act → HMLV V Act → HMLV V Act

/-- The kind of a recursive equation: a largest (`ν`, `max`) or least (`μ`, `min`)
fixed point. -/
inductive FpKind | max | min

namespace LTS

variable {Proc V Act : Type*}

/-- `O_F(ρ)` (Definition 6.1 over a variable set, §6.5): the states satisfying
`F` under the environment `ρ` interpreting each variable as a set of states. -/
def denotV (L : LTS Proc Act) (ρ : V → Set Proc) : HMLV V Act → Set Proc
  | .var X => ρ X
  | .tt => Set.univ
  | .ff => ∅
  | .and F G => denotV L ρ F ∩ denotV L ρ G
  | .or F G => denotV L ρ F ∪ denotV L ρ G
  | .dia a F => {p | ∃ p', L.step p a p' ∧ p' ∈ denotV L ρ F}
  | .box a F => {p | ∀ p', L.step p a p' → p' ∈ denotV L ρ F}

/-- `O_F` is monotone in the environment (the multivariable Exercise 6.5). -/
theorem denotV_mono (L : LTS Proc Act) (F : HMLV V Act) :
    Monotone (fun ρ : V → Set Proc => denotV L ρ F) := by
  intro ρ σ hρσ
  induction F with
  | var X => exact hρσ X
  | tt => exact le_refl _
  | ff => exact le_refl _
  | and F G ihF ihG => exact Set.inter_subset_inter ihF ihG
  | or F G ihF ihG => exact Set.union_subset_union ihF ihG
  | dia a F ihF => exact fun p ⟨p', h, hp'⟩ => ⟨p', h, ihF hp'⟩
  | box a F ihF => exact fun p hp p' hstep => ihF (hp p' hstep)

/-- `⟦D⟧` (Equation 6.9, §6.5): the semantic function of a declaration `D` on the
product complete lattice `V → 2^Proc`, applying `O` to each variable's formula. -/
def sysFun (L : LTS Proc Act) (D : V → HMLV V Act) : (V → Set Proc) →o (V → Set Proc) where
  toFun ρ := fun X => denotV L ρ (D X)
  monotone' := fun _ _ hρσ X => denotV_mono L (D X) hρσ

/-- The largest solution of the equational system `D` (§6.5): the greatest fixed
point of `⟦D⟧`. -/
def sysMax (L : LTS Proc Act) (D : V → HMLV V Act) : V → Set Proc := (sysFun L D).gfp

/-- The least solution of the equational system `D` (§6.5): the least fixed point
of `⟦D⟧`. -/
def sysMin (L : LTS Proc Act) (D : V → HMLV V Act) : V → Set Proc := (sysFun L D).lfp

/-- The solution selected by a fixed-point kind. -/
def sysSolution (L : LTS Proc Act) (D : V → HMLV V Act) : FpKind → (V → Set Proc)
  | .max => sysMax L D
  | .min => sysMin L D

/-- **Exercise 6.8(1)** (§6.5, p.124). The product domain (here `V → 2^Proc`),
ordered componentwise, is a complete lattice. -/
theorem ex_6_8_completeLattice : Nonempty (CompleteLattice (V → Set Proc)) := ⟨inferInstance⟩

/-- **Exercise 6.8(2)** (§6.5, p.124). `⟦D⟧` is monotone. -/
theorem ex_6_8_mono (L : LTS Proc Act) (D : V → HMLV V Act) : Monotone (sysFun L D) :=
  (sysFun L D).monotone

/-! ## §6.7 Mixing fixed points: the livelock property -/

/-- The modal functional `S ↦ ⟨τ⟩S` of the livelock equation `X = ⟨τ⟩X`. -/
def livelockFun (L : LTS Proc Act) (tau : Act) : Set Proc →o Set Proc where
  toFun S := {p | ∃ p', L.step p tau p' ∧ p' ∈ S}
  monotone' := fun _ _ hST _ ⟨p', hstep, hp'⟩ => ⟨p', hstep, hST hp'⟩

/-- `LivelockNow` (§6.7): the largest solution of `X =ν ⟨τ⟩X` — the states that
afford an infinite sequence of `τ`-steps. -/
def LivelockNow (L : LTS Proc Act) (tau : Act) : Set Proc := (livelockFun L tau).gfp

/-- **Exercise 6.15** (§6.7, p.135). The *least* solution of `X = ⟨τ⟩X` is empty
(only the largest fixed point captures livelock). -/
theorem ex_6_15 (L : LTS Proc Act) (tau : Act) : (livelockFun L tau).lfp = ∅ := by
  refine le_antisymm ((livelockFun L tau).lfp_le ?_) (Set.empty_subset _)
  rintro p ⟨_, _, hp'⟩; exact hp'.elim

end LTS

end DeepWiki.ReactiveSystems
