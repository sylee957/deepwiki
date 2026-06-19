import DeepWiki.NetworkCalculus.UltimatelyPseudoPeriodic
import DeepWiki.NetworkCalculus.UppSequence
import Sources.Doi_10_1007_s10626_007_0028_x.Source

/-! # Bouillard–Thierry — stability of the UPP class under the (min,plus) operators — catalog
Pointers to the `DeepWiki.NetworkCalculus` theorems formalizing this paper's **Proposition 4**: the
ultimately-pseudo-periodic function class is stable under `⊓ / ⊔ / + / ∗`, each with an explicit
period and increment. The Deterministic Network Calculus book defers its Chapter-4 Lemmas 4.2–4.4 to
this paper; these are the paper-side ("double reference") pointers complementing the book catalog's
`Chapter4`. -/

namespace DeepWiki.Bt

open DeepWiki

/-- **Definition** (§3.1, p.13): a function is *ultimately pseudo-periodic* if `∃ T d c, ∀ t > T,
f(t+d) = f(t) + c` (the asymptotic behaviour that makes the class finitely representable). The
library's `DeepWiki.IsUPP` (`IsUPPWith` carries the explicit witness `(T, d, c)`). -/
abbrev ultimatelyPseudoPeriodic := @IsUPP

/-- **Proposition 4, item 3** (§3.1.3, p.15): the **sum** of two ultimately pseudo-periodic functions
is ultimately pseudo-periodic from `max(T₁,T₂)`, period `lcm(d₁,d₂)`, increment `(c₁/d₁ + c₂/d₂)·d`.
The library's `DeepWiki.IsUPPWith.add_of_commonPeriod` (the `lcm` cofactors give the book's formula). -/
alias prop_4_add := IsUPPWith.add_of_commonPeriod

/-- **Proposition 4, item 1** (§3.1.3, p.15), **minimum**: `min(f₁,f₂)` is ultimately pseudo-periodic;
for distinct slopes (`c₁/d₁ < c₂/d₂`) it agrees with the slower function past the crossover, otherwise
period `lcm(d₁,d₂)` and increment the smaller slope. The library's
`DeepWiki.UppSeq.min_evalNat_add_lcm` — the crossover is exactly the paper's `T = (M₁−m₂)/(ρ₂−ρ₁)`
(window `sup`/`inf` over the slope gap, the Archimedean `evalNat_eventually_le`). -/
alias prop_4_min := UppSeq.min_evalNat_add_lcm

/-- **Proposition 4, item 2** (§3.1.3, p.15), **maximum**: dual of `prop_4_min` (the increment is the
larger slope). The library's `DeepWiki.UppSeq.max_evalNat_add_lcm`. -/
alias prop_4_max := UppSeq.max_evalNat_add_lcm

/-- **Proposition 4, item 5** (§3.1.3, p.15): the (min,plus) **convolution** `f₁ ∗ f₂` is ultimately
pseudo-periodic with period `d = lcm(d₁,d₂)` and increment `min(c₁/d₁, c₂/d₂)·d` — the *smaller*
asymptotic slope. The library's `DeepWiki.UppSeq.convNat_add_lcm` (general non-balanced closed form,
via the minimizer-region lemma `convNat_minimizer_periodic`; the paper proves it by the same
transient/pseudo-periodic decomposition `f = f' ⊕ f''`). -/
alias prop_4_conv := UppSeq.convNat_add_lcm

/-! **Proposition 4, item 6** (§3.1.3, p.15): the **deconvolution** `f₁ ⊘ f₂` is ultimately
pseudo-periodic from `T₁` with period `d₁` and increment `c₁`. Not yet formalized in the library. -/

end DeepWiki.Bt
