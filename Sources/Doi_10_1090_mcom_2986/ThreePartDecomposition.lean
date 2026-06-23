import DeepWiki.NetworkCalculus.ConvexConcaveThreePart
import Sources.Doi_10_1090_mcom_2986.Source

/-! # Bouillard–Faou–Zavidovique — convex–concave–convex three-part decomposition — catalog
Paper-side ("double reference") pointers to the `DeepWiki.NetworkCalculus` theorems formalizing this
paper's Theorem 4.6, complementing the DNC book catalog's `Chapter4` (§4.2 Theorem 4.2 defers its formal
proof here). The achievable core — the faithful statement predicate, the convolution engines the proof
rests on (Lemma 4.3 distribution, convex∗convex, concave∗concave), and a concrete witness exhibiting all
three genuine parts — is formalized; the full weak-KAM/Lax–Oleinik induction (Lemmas 4.4/4.5 slope
surgery + bounded-support arithmetic) stays `[external]`/`[infra]`. -/

namespace DeepWiki.Bfz

open DeepWiki

/-- **Theorem 4.6** (p.18) = DNC Theorem 4.2: a `convex ∗ concave` convolution decomposes into three
(possibly trivial) parts — convex, concave, convex. The structural conclusion predicate
`h = g¹ ⊓ gᶜ ⊓ g²` (convex `g¹,g²`, concave `gᶜ`). The library's `DeepWiki.IsThreePartCvxCcvCvx`; the
faithful real-interval form (Mathlib `ConvexOn`/`ConcaveOn` on `Icc`, matching the paper's `[a,b]→ℝ`
setting) is `DeepWiki.IsThreePartOnIcc`. -/
abbrev thm_4_6 := @IsThreePartCvxCcvCvx

/-- **Lemma 4.3** (p.15), the induction engine: convolution distributes over the meet —
`f ∗ (g ⊓ h) = (f ∗ g) ⊓ (f ∗ h)`. The library's `DeepWiki.minConv_distrib_inf`. -/
alias lemma_4_3 := minConv_distrib_inf

/-- **Theorem 4.2 (paper, convex∗convex)**: the convolution of two convex functions is convex (the
`g¹`/`g²` parts). The library's `DeepWiki.isConvexEReal_minConv_convex`. -/
alias thm_4_2_paper := isConvexEReal_minConv_convex

/-- **The concave part** `gᶜ`: the convolution of two concave functions is concave. The library's
`DeepWiki.isConcaveEReal_minConv_concave`. -/
alias concave_part := isConcaveEReal_minConv_concave

/-- **Theorem 4.6 witness** (paper Figure 2): a concrete three-part function on `[0,4]` — `(t−1)²` /
`−(t−2)²+1` / `(t−3)²` — satisfying `IsThreePartOnIcc`, with all three parts genuine (the concave bump
and both convex dips are strictly off their chord midpoints). The library's
`DeepWiki.isThreePartOnIcc_witnessThree`. -/
alias thm_4_6_witness := isThreePartOnIcc_witnessThree

end DeepWiki.Bfz
