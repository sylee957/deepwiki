import Mathlib.Order.FixedPoints

/-! # Fix-point characterization of stability
The Knaster–Tarski kernel of the fix-point sufficient condition (Theorem 12.1):
the candidate arrival-curve assignment `α̂ = sSup {α | α ≤ F α}` of a monotone
propagation operator `F` is a fixed point of `F` and the greatest consistent
(post-fixed) assignment. `V` is the complete lattice of arrival-curve
assignments and `F` the operator sending an assignment to the arrival curves it
induces at the servers' inputs. (That a *finite* `α̂` makes the network globally
stable and gives each flow an arrival curve is the network-model instantiation,
which builds on this kernel and is not formalized here.) -/

namespace DeepWiki

/-- The **canonical arrival-curve assignment** `α̂` of a feed-back network
(Theorem 12.1): the supremum of all post-fixed points of the monotone
propagation operator `F`, `α̂ = sSup {α | α ≤ F α}` (Knaster–Tarski's greatest
post-fixed point). -/
noncomputable def canonicalArrivalAssignment {V : Type*} [CompleteLattice V]
    (F : V →o V) : V := F.gfp

/-- `α̂` is the supremum of the post-fixed points `{α | α ≤ F α}`. -/
theorem canonicalArrivalAssignment_eq_sSup {V : Type*} [CompleteLattice V]
    (F : V →o V) : canonicalArrivalAssignment F = sSup {α | α ≤ F α} := rfl

/-- **`α̂` is a fixed point of the propagation operator** (Theorem 12.1): it is a
consistent arrival-curve assignment, `F α̂ = α̂`. -/
theorem map_canonicalArrivalAssignment {V : Type*} [CompleteLattice V]
    (F : V →o V) :
    F (canonicalArrivalAssignment F) = canonicalArrivalAssignment F := F.map_gfp

/-- **`α̂` is the greatest consistent assignment** (Theorem 12.1): it is itself
post-fixed (`α̂ ≤ F α̂`) and dominates every post-fixed point. -/
theorem isGreatest_canonicalArrivalAssignment {V : Type*} [CompleteLattice V]
    (F : V →o V) :
    IsGreatest {α | α ≤ F α} (canonicalArrivalAssignment F) := F.isGreatest_gfp_le

/-- Every consistent (post-fixed) assignment is dominated by `α̂`
(Theorem 12.1): `α ≤ F α → α ≤ α̂`. -/
theorem le_canonicalArrivalAssignment {V : Type*} [CompleteLattice V]
    {F : V →o V} {α : V} (h : α ≤ F α) : α ≤ canonicalArrivalAssignment F :=
  F.le_gfp h

end DeepWiki
