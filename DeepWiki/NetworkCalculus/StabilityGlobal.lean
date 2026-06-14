import DeepWiki.NetworkCalculus.Stability
import DeepWiki.NetworkCalculus.ServiceCurveStrict

/-! # Global stability of a server
The per-server global-stability predicate (bounded maximal backlogged period),
the implication that a finite first crossing makes a server globally stable
(Lemma 12.4, via the Theorem 5.5 bound `maxBackloggedLength ≤ firstCrossing`),
and the local ⟹ global corollary obtained by feeding it the analytic Lemma 12.1
(`firstCrossing_lt_top_of_isLocallyStableServer`). (The network-wide global
stability of Definition 12.3 quantifies this over every server.) -/

namespace DeepWiki

open scoped NNReal ENNReal

/-- A single server is **globally stable** when its maximal backlogged period
is finite, `maxBackloggedLength A D < ⊤` (Definition 12.3, per-server form). -/
def IsGloballyStableServer (A D : ℝ≥0 → ℝ≥0) : Prop :=
  maxBackloggedLength A D < ⊤

/-- **Lemma 12.4** (finite first crossing ⟹ global stability), per-server form:
a causal server with strict minimal service curve `beta`, carrying a pair
`(A, D)` whose arrival admits maximal arrival curve `alpha`, is globally stable
whenever the first crossing `ℓmax = firstCrossing alpha beta` is finite. Its
maximal backlogged period is bounded by that first crossing (Theorem 5.5). -/
theorem isGloballyStableServer_of_firstCrossing_lt_top
    {S : Curve → Curve → Prop} {beta alpha : ℝ≥0 → ℝ≥0}
    (hc : IsCausal S) (hβ : IsStrictMinimalServiceCurve beta S)
    {A D : Curve} (hp : S A D)
    (harr : IsMaximalArrivalBound (⇑A) alpha)
    (hfin : firstCrossing alpha beta < ⊤) :
    IsGloballyStableServer ⇑A ⇑D :=
  lt_of_le_of_lt (maxBackloggedLength_le_firstCrossing hc hβ hp harr) hfin

/-- **Local stability ⟹ global stability** for one server (Definition 12.2 +
Lemma 12.1 + Lemma 12.4): a causal server with strict minimal service curve
`beta`, carrying a pair `(A, D)` whose arrival admits maximal arrival curve
`alpha`, is globally stable as soon as it is locally stable
(`longTermArrivalRate alpha < longTermServiceRate beta`). Local stability makes
the first crossing finite (Lemma 12.1), which bounds the backlogged period. -/
theorem isGloballyStableServer_of_isLocallyStableServer
    {S : Curve → Curve → Prop} {beta alpha : ℝ≥0 → ℝ≥0}
    (hc : IsCausal S) (hβ : IsStrictMinimalServiceCurve beta S)
    {A D : Curve} (hp : S A D)
    (harr : IsMaximalArrivalBound (⇑A) alpha)
    (hstab : IsLocallyStableServer alpha beta) :
    IsGloballyStableServer ⇑A ⇑D :=
  isGloballyStableServer_of_firstCrossing_lt_top hc hβ hp harr
    (firstCrossing_lt_top_of_isLocallyStableServer hstab)

end DeepWiki
