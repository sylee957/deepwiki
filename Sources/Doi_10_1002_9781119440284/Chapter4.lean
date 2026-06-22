import DeepWiki.NetworkCalculus.ConcaveDioid
import DeepWiki.NetworkCalculus.ConcaveProps
import DeepWiki.NetworkCalculus.ConvexConvolutionLegendre
import DeepWiki.NetworkCalculus.ConcavePWLNormalForm
import DeepWiki.NetworkCalculus.ClosuresEReal
import DeepWiki.NetworkCalculus.FunctionDioids
import DeepWiki.NetworkCalculus.UltimatelyPseudoPeriodic
import DeepWiki.NetworkCalculus.UppSequence
import Sources.Doi_10_1002_9781119440284.Source

/-! # DNC catalog — Chapter 4: Efficient Computations for (min,plus) Operators
Book-numbered catalog entries for this chapter, each linked to the
`DeepWiki` library declaration that formalizes it (`alias`/`abbrev`),
or recorded as a note / unformalized item.

## NOT YET FORMALIZED (subtractive — delete each item once it is formalized)
§4.2: Proposition 4.1 — items 3–4 only `[infra]` (the intersection-point sequence `tᵢ` increasing, and the explicit per-interval `γ` formula need the intersection-point layer; item 1 concavity = `prop_4_1_concave`, item 2 bursts-increasing = `prop_4_1_burst`); Theorem 4.1, the explicit *segment-merge-by-slope algorithm* on a PWL data structure `[infra]` (its transform-domain *principle* `f∗g = 𝓛(𝓛f+𝓛g)` IS formalized — `thm_4_1_legendre`; what remains is only the concrete piecewise-affine representation realizing the merge); Lemma 4.1 (segment placement of the min) `[infra]`; Theorem 4.2 (convex-by-concave convolution, segment-wise — the concave-convolution core is `IsConcaveEReal.minConv`) `[infra]`.
§4.3: Lemma 4.6 (closed-form deconvolution of two segments) `[infra]`; Lemma 4.7 (sub-additive-closure factorization) `[research]`; Lemma 4.8 (closure of a spot is UPP) `[infra]`; Lemma 4.9 (closure of an open segment is UPP) `[infra]`.
§4.4 containers: Definition 4.2; Definition 4.3; Definition 4.4; Definition 4.5; Proposition 4.2; Proposition 4.3; Proposition 4.4; Lemma 4.10; Theorem 4.4; Remark 4.1 — all `[research]`. -/

namespace DeepWiki.Dnc

open DeepWiki
open scoped NNReal ENNReal

/-- **Definition** (§4.3.2, p.74): the class of **ultimately pseudo-periodic** functions — beyond a
rank `T`, advancing time by a period `d` raises the value by an increment `c`. The library's
`DeepWiki.IsUPP` (`IsUPPWith` carries the explicit `(T, d, c)`). The basis of finite representation
and the algorithmic (min,plus) calculus. -/
abbrev def_4_upp := @IsUPP

/-- **Theorem 4.3** (§4.3.2.2, p.74): the class of plain ultimately pseudo-periodic functions of
`F[ℚ,ℚ]` is stable under min, max, +, −, convolution, deconvolution and sub-additive closure. The
library formalizes the UPP class (`def_4_upp`) and its stability under `+` (`lemma_4_2`, all common
periods), `⊓`/`⊔` (`lemma_4_3_min`/`lemma_4_3_max`, **all slope cases** via the Archimedean crossover),
and convolution `∗` (`lemma_4_4`, the **general** closed form including the non-balanced case via the
minimizer-region lemma), deconvolution (`lemma_4_5`, the deconvolution sequence is UPP), and the
sub-additive-closure **approximant** (`UppSeq.closureApproxNat`, idempotent closed form `f* = δ₀ ⊓ f`
in `UppSeq.closureApproxNat_idem`). The segment-merge / container parts are in the chapter's
`## NOT YET FORMALIZED` block. -/
theorem thm_4_3_add {V : Type*} [AddCommMonoid V] {f g : ℝ≥0 → V} {T₁ T₂ d c₁ c₂}
    (hf : IsUPPWith f T₁ d c₁) (hg : IsUPPWith g T₂ d c₂) :
    IsUPPWith (fun t => f t + g t) (max T₁ T₂) d (c₁ + c₂) := hf.add hg

/-- **Lemma 4.2** (§4.3.2.2, p.75): the sum of two ultimately pseudo-periodic functions is
ultimately pseudo-periodic from `max(T_f,T_g)` with period `lcm(d_f,d_g)` and increment
`(d_g c_f + d_f c_g)/gcd(d_f,d_g)`. The library's `DeepWiki.IsUPPWith.add_of_commonPeriod` (general
commensurable-period form — a common multiple `m•d₁ = n•d₂` with increment `m•c₁ + n•c₂`; the `lcm`
cofactors give exactly the book's formula). The shared-period special case is `IsUPPWith.add`. -/
alias lemma_4_2 := IsUPPWith.add_of_commonPeriod

/-- **Lemma 4.3** (§4.3.2.2, p.75), **minimum** — general case (all slope relations): the pointwise
minimum of two UPP sequences is ultimately pseudo-periodic, `min(f,g)(n+d) = min(f,g)(n) + min(c_f',c_g')`
with `d = lcm` and the increment the *smaller* per-`d` slope. The library's
`DeepWiki.UppSeq.min_evalNat_add_lcm` — the dominant-slope cases close via the Archimedean crossover
`evalNat_eventually_le` (the slower function is the min past the crossover), the balanced case via
`min`-distributes-over-`+`. (The balanced common-period form over any ordered monoid is
`IsUPPWith.min_of_commonPeriod`.) Requires `V` an Archimedean ordered group. -/
alias lemma_4_3_min := UppSeq.min_evalNat_add_lcm

/-- **Lemma 4.3** (§4.3.2.2, p.75), **maximum** — general case. Dual of `lemma_4_3_min`: the increment
is the *larger* slope (past the crossover the faster function is the max). The library's
`DeepWiki.UppSeq.max_evalNat_add_lcm` (balanced common-period form: `IsUPPWith.max_of_commonPeriod`). -/
alias lemma_4_3_max := UppSeq.max_evalNat_add_lcm

/-- **Lemma 4.4** (§4.3.2.2, p.76): `f ∗ g` is ultimately pseudo-periodic with period `d = lcm(d_f,d_g)`
from rank `T_f + T_g + d`, increment `min((d/d_f)c_f, (d/d_g)c_g)` (the *smaller* asymptotic slope).
The library's `DeepWiki.UppSeq.convNat_add_lcm` proves the **general** pseudo-period step
`(f⊗g)(n+d) = (f⊗g)(n) + min(c_f',c_g')` for nondecreasing `f,g` of distinct slope — via the
minimizer-region lemma `convNat_minimizer_periodic` (the minimizer of `(f⊗g)(n)` eventually lies in
the slower operand's periodic région, so the `+d` shift pushes into it). The `≥` half is
`convNat_add_lcm_ge`, the `≤` half `convNat_add_lcm_le`. The balanced case (equal slopes, no
monotonicity needed) is `convNat_add_lcm_of_balanced`; the no-transient case
`convNat_add_lcm_of_noTransient`. The pointwise convolution is `DeepWiki.UppSeq.convNat`
(`convNat_le`/`convNat_eq`); the `minplus` CLI's `conv` samples it. -/
alias lemma_4_4 := UppSeq.convNat_add_lcm

/-- **Lemma 4.5** (§4.3.2.2, p.77): if `f,g` are ultimately pseudo-periodic, the deconvolution `f ⊘ g`
is ultimately pseudo-periodic from `T_f` with period `d_f` and increment `c_f`. The library's
`DeepWiki.UppSeq.deconvNat_add_period`: the deconvolution sequence advances by `c_f` each period `d_f`
(the `minplus` CLI's `deconvupp` builds the UPP quadruplet from it). -/
alias lemma_4_5 := UppSeq.deconvNat_add_period

/-- **Definition 4.1** (§4.2.1, p.63): a concave piecewise-linear function in *normal form* —
`f = ⋀ᵢ γ_{rᵢ,bᵢ}` (an infimum of token-buckets, `concaveNFEval`) where the rates are strictly
decreasing along the list (`i<j ⟹ rᵢ>rⱼ`, eq. [4.2]) and no token-bucket is redundant (each is the
strict minimum at some positive time, eq. [4.3]). The library's `DeepWiki.IsConcaveNormalForm`
(over a `List (ℝ≥0 × ℝ≥0)` of `(rate, burst)` parameters). -/
abbrev def_4_1 := @IsConcaveNormalForm

/-- **Definition 4.1** (§4.2.1, p.63), the evaluation: `⋀ᵢ γ_{rᵢ,bᵢ}` as an `EReal` curve, the
pointwise infimum of the token-bucket curves `γ_{r,b} = (r·t + b) ⊓ convUnit` (`DeepWiki.tbEReal`).
The library's `DeepWiki.concaveNFEval`. -/
noncomputable def def_4_1_eval := @concaveNFEval

/-- **Proposition 4.1, item 1** (§4.2.1, p.63): a concave piecewise-linear function in normal
form *is concave*. The library's `DeepWiki.isConcaveEReal_concaveNFEval` (the infimum of the
concave token-buckets is concave; items 2–4 — `bᵢ`/`tᵢ` increasing and the per-interval formula —
need the intersection-point layer, see the chapter's `## NOT YET FORMALIZED` block). -/
theorem prop_4_1_concave (l : List (ℝ≥0 × ℝ≥0)) : IsConcaveEReal (concaveNFEval l) :=
  isConcaveEReal_concaveNFEval l

/-- **Proposition 4.1, item 2** (§4.2.1, p.63): in a concave normal form the bursts are strictly
increasing along the list (`bᵢ < bⱼ` for `i < j`). If `bᵢ ≥ bⱼ` while the rates decrease
(`rᵢ > rⱼ`), then `γ_{rᵢ,bᵢ} ≥ γ_{rⱼ,bⱼ}` pointwise, so `γᵢ` is redundant — contradicting the
irredundancy clause of Definition 4.1. The library's `DeepWiki.IsConcaveNormalForm.burst_strictMono`. -/
theorem prop_4_1_burst {l : List (ℝ≥0 × ℝ≥0)} (h : IsConcaveNormalForm l) :
    l.Pairwise (fun a b => a.2 < b.2) :=
  h.burst_strictMono

/-- **Theorem 4.1** (§4.2.2, p.65), the transform-domain computation principle. For finite,
convex, non-decreasing, non-negative curves `f, g`, the `(min,plus)` convolution is computed by
**adding the Legendre–Fenchel transforms and inverting**: `f ∗ g = 𝓛(𝓛 f + 𝓛 g)`. Because `𝓛 h(s)`
is indexed by the *slope* `s`, pointwise addition of the transforms is exactly the book's "merge the
segments in increasing order of slope" rule (Theorem 4.1, Figure 4.4). This is the mathematical
content justifying the segment-merge algorithm; the explicit piecewise-affine data structure that
performs the merge is the chapter's `[infra]` item. The library's
`DeepWiki.minConv_eq_legendre_add_legendre` (composing the Fenchel–Moreau involution with
`𝓛(f ∗ g) = 𝓛 f + 𝓛 g`). -/
theorem thm_4_1_legendre {f g : ℝ≥0 → EReal}
    (hf : IsConvexEReal f) (hg : IsConvexEReal g) (hmf : Monotone f) (hmg : Monotone g)
    (hfin_f : ∀ x, f x ≠ ⊤ ∧ f x ≠ ⊥) (hfin_g : ∀ x, g x ≠ ⊤ ∧ g x ≠ ⊥)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    minConv f g = legendre (legendre f + legendre g) :=
  DeepWiki.minConv_eq_legendre_add_legendre hf hg hmf hmg hfin_f hfin_g hf0 hg0

/-! **Remark** (§4.3.3, p.80): On the discrete domain ℕ, (F_ℕ, ∧, ∗_ℕ) is a dioid; the library's function complete-dioid (FPlus over the ℝ≥0 domain) carries the same (min,conv) dioid algebra. Library: FPlus, isSubCompleteDioid_FPlus. -/

end DeepWiki.Dnc
