import DeepWiki.NetworkCalculus.FunctionDioids

/-! # Non-decreasing closure
The least monotone majorant `ndClosure f = (t ↦ ⨆_{s ≤ t} f s)`: its
generic theory over a `ConditionallyCompleteLattice` (domination,
monotonicity, least-majorant) and the `R∪{±∞}` specializations
(`ClosureBddAbove` is automatic, `IsNonneg` is preserved). -/

namespace DeepWiki

open Algebra
open scoped Classical NNReal ENNReal Algebra.Bridge

/-- The set `{s // s ≤ t}` is nonempty (contains `⊥`). -/
instance subLeNonempty {D : Type*} [Preorder D]
    [OrderBot D] (t : D) :
    Nonempty {s : D // s ≤ t} :=
  ⟨⟨⊥, bot_le⟩⟩

/-- Non-decreasing closure: `t ↦ ⨆_{s ≤ t} f s`. -/
noncomputable def ndClosure {D T : Type*}
    [Preorder D] [OrderBot D]
    [ConditionallyCompleteLattice T]
    (f : D → T) : D → T :=
  fun t => ⨆ s : {s : D // s ≤ t}, f s

/-- Each prefix `{f s // s ≤ t}` of `f` is bounded above. -/
def ClosureBddAbove {D T : Type*} [Preorder D]
    [Preorder T] (f : D → T) : Prop :=
  ∀ t, BddAbove
    (Set.range (fun s : {s : D // s ≤ t} => f s))

/-- `f t ≤ ndClosure f t` (the closure dominates `f`). -/
theorem le_ndClosure {D T : Type*}
    [Preorder D] [OrderBot D]
    [ConditionallyCompleteLattice T] (f : D → T)
    (hbdd : ClosureBddAbove f) (t : D) :
    f t ≤ ndClosure f t := by
  unfold ndClosure
  exact le_ciSup (hbdd t)
    (⟨t, le_refl t⟩ : {s // s ≤ t})

/-- `ndClosure f` is monotone. -/
theorem ndClosure_mono {D T : Type*}
    [Preorder D] [OrderBot D]
    [ConditionallyCompleteLattice T] (f : D → T)
    (hbdd : ClosureBddAbove f) :
    Monotone (ndClosure f) := by
  intro x y hxy
  unfold ndClosure
  refine ciSup_le (fun s => ?_)
  exact le_ciSup (hbdd y) ⟨s.1, s.2.trans hxy⟩

/-- `ndClosure f` is the least monotone majorant of `f`. -/
theorem ndClosure_le {D T : Type*}
    [Preorder D] [OrderBot D]
    [ConditionallyCompleteLattice T]
    {f g : D → T} (hg : Monotone g)
    (hfg : ∀ t, f t ≤ g t) (t : D) :
    ndClosure f t ≤ g t := by
  unfold ndClosure
  refine ciSup_le (fun s => ?_)
  exact (hfg s.1).trans (hg s.2)

/-- The non-decreasing closure of a monotone curve is itself. -/
theorem ndClosure_eq_self {D T : Type*}
    [Preorder D] [OrderBot D]
    [ConditionallyCompleteLattice T] {f : D → T}
    (hmono : Monotone f) :
    ndClosure f = f := by
  funext t
  refine le_antisymm (ndClosure_le hmono (fun _ => le_rfl) t) ?_
  exact le_ndClosure f
    (fun u => ⟨f u, by rintro x ⟨v, rfl⟩; exact hmono v.2⟩) t

/-- Over `R∪{±∞}` every `f` satisfies `ClosureBddAbove`. -/
theorem ndClosure_ext_bdd
    (f : ℝ≥0 → WithTop (WithBot ℝ)) :
    ClosureBddAbove f :=
  fun _ => OrderTop.bddAbove _

/-- `le_ndClosure` specialized to `R∪{±∞}`. -/
theorem le_ndClosure_ext (f : ℝ≥0 → WithTop (WithBot ℝ))
    (t : ℝ≥0) : f t ≤ ndClosure f t :=
  le_ndClosure f (ndClosure_ext_bdd f) t

/-- `ndClosure_mono` specialized to `R∪{±∞}`. -/
theorem monotone_ndClosure_ext
    (f : ℝ≥0 → WithTop (WithBot ℝ)) :
    Monotone (ndClosure f) :=
  fun _ _ hxy => ndClosure_mono f (ndClosure_ext_bdd f) hxy

/-- `ndClosure_le` specialized to `R∪{±∞}`. -/
theorem ndClosure_ext_le {f g : ℝ≥0 → WithTop (WithBot ℝ)}
    (hg : Monotone g) (hfg : ∀ t, f t ≤ g t)
    (t : ℝ≥0) : ndClosure f t ≤ g t :=
  ndClosure_le hg hfg t

/-- `ndClosure` preserves `IsNonneg` over `R∪{±∞}`. -/
theorem ndClosure_ext_isNonneg
    {f : ℝ≥0 → WithTop (WithBot ℝ)}
    (hf : IsNonneg f) : IsNonneg (ndClosure f) :=
  fun t => (hf t).trans (le_ndClosure_ext f t)
end DeepWiki
