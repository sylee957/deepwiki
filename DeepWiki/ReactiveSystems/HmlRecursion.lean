import DeepWiki.ReactiveSystems.Hml
import Mathlib.Order.FixedPoints

/-! # Hennessy–Milner logic with recursion
Extending HML with a recursion variable lets formulae express ongoing properties
(safety, liveness). A formula `F` with one variable `X` induces a monotone
semantic function `O_F` on the powerset lattice of states; the meaning of a
recursive definition `X =ν F` (resp. `X =μ F`) is the greatest (resp. least)
fixed point of `O_F`, which exists by Tarski. The invariant `Inv(F)` (always `F`)
is the canonical largest-fixed-point example. -/

namespace DeepWiki.ReactiveSystems

/-- HML with a single recursion variable `X` (the constructor `var`). -/
inductive HMLR (Act : Type*)
  | var : HMLR Act
  | tt : HMLR Act
  | ff : HMLR Act
  | and : HMLR Act → HMLR Act → HMLR Act
  | or : HMLR Act → HMLR Act → HMLR Act
  | dia : Act → HMLR Act → HMLR Act
  | box : Act → HMLR Act → HMLR Act

namespace LTS

variable {Proc Act : Type*}

/-- `O_F(S)`: the states satisfying `F` when the recursion
variable `X` is interpreted as the set `S`. -/
def denotR (L : LTS Proc Act) : HMLR Act → Set Proc → Set Proc
  | .var => fun S => S
  | .tt => fun _ => Set.univ
  | .ff => fun _ => ∅
  | .and F G => fun S => denotR L F S ∩ denotR L G S
  | .or F G => fun S => denotR L F S ∪ denotR L G S
  | .dia a F => fun S => {p | ∃ p', L.step p a p' ∧ p' ∈ denotR L F S}
  | .box a F => fun S => {p | ∀ p', L.step p a p' → p' ∈ denotR L F S}

/-- `O_F` is monotone in `S`, so its least and
greatest fixed points exist (Tarski). (Negation would break monotonicity.) -/
theorem denotR_mono (L : LTS Proc Act) (F : HMLR Act) : Monotone (denotR L F) := by
  intro S T hST
  induction F with
  | var => exact hST
  | tt => exact le_refl _
  | ff => exact le_refl _
  | and F G ihF ihG => exact Set.inter_subset_inter ihF ihG
  | or F G ihF ihG => exact Set.union_subset_union ihF ihG
  | dia a F ihF => exact fun p ⟨p', hstep, hp'⟩ => ⟨p', hstep, ihF hp'⟩
  | box a F ihF => exact fun p hp p' hstep => ihF (hp p' hstep)

/-- `O_F` bundled as a monotone map on the powerset lattice. -/
def denotRHom (L : LTS Proc Act) (F : HMLR Act) : Set Proc →o Set Proc :=
  ⟨denotR L F, denotR_mono L F⟩

/-- Meaning of the recursive definition `X =ν F`: the greatest fixed point of
`O_F`. -/
def recMax (L : LTS Proc Act) (F : HMLR Act) : Set Proc := (denotRHom L F).gfp

/-- Meaning of the recursive definition `X =μ F`: the least fixed point of
`O_F`. -/
def recMin (L : LTS Proc Act) (F : HMLR Act) : Set Proc := (denotRHom L F).lfp

/-- `X =ν F` is a fixed point: `O_F(⟦X⟧) = ⟦X⟧`. -/
theorem denotR_recMax (L : LTS Proc Act) (F : HMLR Act) :
    denotR L F (recMax L F) = recMax L F := (denotRHom L F).map_gfp

/-- `X =μ F` is a fixed point: `O_F(⟦X⟧) = ⟦X⟧`. -/
theorem denotR_recMin (L : LTS Proc Act) (F : HMLR Act) :
    denotR L F (recMin L F) = recMin L F := (denotRHom L F).map_lfp

/-! ## Largest fixed points and invariant properties -/

/-- The semantic function of `Inv(F) = νX. (F ∧ [Act]X)`: `F` holds now and `X`
holds at every one-step successor. -/
def invFun (L : LTS Proc Act) (F : HML Act) : Set Proc →o Set Proc where
  toFun S := denot L F ∩ {p | ∀ a p', L.step p a p' → p' ∈ S}
  monotone' := fun _ _ hST _ hp => ⟨hp.1, fun a p' hstep => hST (hp.2 a p' hstep)⟩

/-- `Inv(F)`: the greatest fixed point of the invariant functional. -/
def Inv (L : LTS Proc Act) (F : HML Act) : Set Proc := (invFun L F).gfp

/-- Fixed-point unfolding of `Inv(F)`: a state is invariant for `F` iff it
satisfies `F` now and all its successors are invariant for `F`. -/
theorem Inv_unfold (L : LTS Proc Act) (F : HML Act) (x : Proc) :
    x ∈ Inv L F ↔ x ∈ denot L F ∧ ∀ a p', L.step x a p' → p' ∈ Inv L F := by
  show x ∈ (invFun L F).gfp ↔
    x ∈ denot L F ∧ ∀ a p', L.step x a p' → p' ∈ (invFun L F).gfp
  conv_lhs => rw [← OrderHom.map_gfp (invFun L F)]
  exact Iff.rfl

/-- `Inv(F)` is exactly the set of states from
which every reachable state satisfies `F`. -/
theorem Inv_eq (L : LTS Proc Act) (F : HML Act) :
    Inv L F = {p | ∀ p', L.Reachable p p' → p' ∈ denot L F} := by
  have hclosed : ∀ {p p'}, p ∈ Inv L F → L.Reachable p p' → p' ∈ Inv L F := by
    intro p p' hp hreach
    induction hreach with
    | refl => exact hp
    | @tail b c _ hbc ih => obtain ⟨a, hstep⟩ := hbc; exact ((Inv_unfold L F b).mp ih).2 a c hstep
  apply Set.eq_of_subset_of_subset
  · intro p hp p' hreach; exact ((Inv_unfold L F p').mp (hclosed hp hreach)).1
  · refine (invFun L F).le_gfp ?_
    intro p hp
    exact ⟨hp p (reachable_refl L p),
      fun a p' hstep p'' hreach => hp p'' (Relation.ReflTransGen.head ⟨a, hstep⟩ hreach)⟩

end LTS

end DeepWiki.ReactiveSystems
