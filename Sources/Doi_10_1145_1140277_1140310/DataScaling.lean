import DeepWiki.NetworkCalculus.ScalingFunction
import Sources.Doi_10_1145_1140277_1140310.Source

/-! # Fidler–Schmitt — network calculus with data scaling — catalog
Paper-side ("double reference") pointers to the `DeepWiki.NetworkCalculus` theorems formalizing this
paper, complementing the DNC book catalog's `Chapter12` (§12.4.2 defers its data-scaling calculus + the
constant-scaling instability trajectory here). The achievable core — the scaling operator, the maximal
scaling curve, the scaled arrival-curve propagation, and the gain-identity grounding the §12.4.2
divergence in genuine scaling operations — is formalized; the explicit adversarial piecewise-linear
backlog-growing trajectory (Fig. 12.5) stays `[deferred]`. -/

namespace DeepWiki.Fs

open DeepWiki

/-- **Definition 3.1** (p.290): a scaling function `S ∈ ℱ` — `S 0 = 0` and monotone — applied to a
flow's cumulative `scale S F = S ∘ F`. The library's `DeepWiki.IsScalingFunction` / `DeepWiki.scale`. -/
abbrev def_3_1 := @IsScalingFunction

/-- **Definition 3.2** (p.290): a maximal scaling curve `S̄` for `S` — the additive bound
`S(b+a) ≤ S̄ b + S a` (equivalently `S̄ ≥ S ⊘ S`). The library's `DeepWiki.IsMaximalScalingCurve`. -/
abbrev def_3_2 := @IsMaximalScalingCurve

/-- **Corollary 3.4** (p.292): the scaled output of an `α`-constrained flow has arrival curve
`α_S = S̄ ∘ α` — `scale S F` is `(S̄ ∘ α)`-arrival-bounded. The library's
`DeepWiki.IsMaximalScalingCurve.isMaximalArrivalBound_scale`. -/
alias cor_3_4 := IsMaximalScalingCurve.isMaximalArrivalBound_scale

/-- **§12.4.2 gain grounding** (Lemma 12.6 link): the cyclic-network instability gain
`m₂m₄/((1−m₂)(1−m₄))` factors per-hop, and its numerator `m₂·m₄` is the composed cross-flow linear
scaling `(linearScale m₄ ∘ linearScale m₂) 1` — connecting the formalized `scalingIterate_unbounded`
divergence to genuine data-scaling operations. The library's
`DeepWiki.scaling_gain_eq_perHop_prod` / `DeepWiki.scaling_gain_numerator_eq_comp`. -/
alias gain_grounding := scaling_gain_numerator_eq_comp

end DeepWiki.Fs
