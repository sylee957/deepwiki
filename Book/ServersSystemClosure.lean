import Book.Servers

/-! # The closure of a system (§9.3)
The book's §9.3 introduces the *closure* `S̄` of a system `S` — the pairs reachable
as left limits of pairs in `S` — to discuss the (non-)existence of an intermediate
type of service curve. A pair `(A, D')` is in `S̄` when it is causal and, for every
`ε > 0`, some `(A, D) ∈ S` (same input `A`) approximates `D'` from below up to the
`ε`-shift: `D(· − ε) ≤ D'`. This file defines the operator and its basic
properties (containment of `S`, monotonicity); the dilution `⋃ₙ (S_strict(δ_{T/n}))ⁿ`
closure `= S_mp(δ_T)` (Lemma 9.5) and Theorem 9.7 build on it. -/

namespace DeepWiki

open scoped Classical NNReal

/-- The closure `S̄` of a system `S`: causal pairs `(A, D')` such that for every
`ε > 0` some `(A, D) ∈ S` `ε`-approximates `D'` from below, `D(· − ε) ≤ D'`. -/
def systemClosure (S : Curve → Curve → Prop) : Curve → Curve → Prop :=
  fun A D' => D' ≤ A ∧ ∀ ε : ℝ≥0, 0 < ε → ∃ D : Curve, S A D ∧ ∀ t, D (t - ε) ≤ D' t

/-- `systemClosure S A D'` unfolds to causality plus the `ε`-approximation from
below. -/
theorem mem_systemClosure_iff {S : Curve → Curve → Prop} {A D' : Curve} :
    systemClosure S A D' ↔
      D' ≤ A ∧ ∀ ε : ℝ≥0, 0 < ε → ∃ D : Curve, S A D ∧ ∀ t, D (t - ε) ≤ D' t :=
  Iff.rfl

/-- A causal system is contained in its closure: each pair `ε`-approximates
itself from below (`D'(· − ε) ≤ D'` by monotonicity). -/
theorem subset_systemClosure {S : Curve → Curve → Prop} (hc : IsCausal S) :
    S ≤ systemClosure S :=
  fun A D' hp =>
    ⟨hc A D' hp, fun _ _ => ⟨D', hp, fun _ => D'.mono tsub_le_self⟩⟩

/-- The closure is monotone in the system: `S ≤ S'` gives `S̄ ≤ S̄'`. -/
theorem systemClosure_mono {S S' : Curve → Curve → Prop} (h : S ≤ S') :
    systemClosure S ≤ systemClosure S' :=
  fun _ _ hp =>
    ⟨hp.1, fun ε hε => (hp.2 ε hε).imp fun _ hD => ⟨h _ _ hD.1, hD.2⟩⟩

/-- The closure is causal: every closure pair `(A, D')` has `D' ≤ A`. -/
theorem isCausal_systemClosure (S : Curve → Curve → Prop) :
    IsCausal (systemClosure S) :=
  fun _ _ hp => hp.1

end DeepWiki
