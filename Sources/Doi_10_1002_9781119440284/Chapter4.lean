import DeepWiki.NetworkCalculus.ConcaveDioid
import DeepWiki.NetworkCalculus.ConcaveProps
import DeepWiki.NetworkCalculus.ConvexConvolutionLegendre
import DeepWiki.NetworkCalculus.ConcavePWLNormalForm
import DeepWiki.NetworkCalculus.ConvexPWLNormalForm
import DeepWiki.NetworkCalculus.ConvexSegmentMerge
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
§4.2: Theorem 4.1, the explicit *segment-merge-by-slope algorithm* `[infra]` — data layer defined (`convexSegEval`/`mergeBySlope`); base case `thm_4_1_base` (affine ∗ affine = min-slope), flat case `thm_4_1_flat` (flatter line ∗ convex = shift), and the **balanced case `thm_4_1_balanced`** (`ρf=ρg`: the full `mergeBySlope` IS the convolution, by the slope-peel induction) are proved. What remains is only the *unbalanced* `ρf≠ρg` case, where the merge must **truncate** at `min(ρf,ρg)` (segments steeper than the slower asymptote are absorbed) — the peel machinery (`minConv_peel_leadSeg`/`minConv_leadSeg_le`) is reusable but the truncating merge + its bookkeeping are a separate effort (the transform-domain *principle* `f∗g = 𝓛(𝓛f+𝓛g)` IS formalized — `thm_4_1_legendre`); Lemma 4.1 (segment placement of the min) `[infra]`; Theorem 4.2 (convex-by-concave convolution, segment-wise — the concave-convolution core is `IsConcaveEReal.minConv`) `[infra]`.
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

/-- **Definition 4.1** (§4.2.1, p.63), the intersection point `tᵢ`. The crossing time of two
adjacent token-buckets `γ_{r,b}` and `γ_{r',b'}` is `tᵢ = (b'−b)/(r−r')` (the book's eq. for
`tᵢ`, `2 ≤ i ≤ n`). The two buckets are equal there (`tbEReal_eq_at_cross`) and `γ_{r,b}` is the
strict minimum exactly before it (`tb_lt_iff_lt_cross`); it is positive when rates decrease and
bursts increase (`tbCross_pos`). The library's `DeepWiki.tbCross`. -/
noncomputable def def_4_1_cross := @tbCross

/-- **Proposition 4.1, item 2** (§4.2.1, p.63): in a concave normal form the bursts are strictly
increasing along the list (`bᵢ < bⱼ` for `i < j`). If `bᵢ ≥ bⱼ` while the rates decrease
(`rᵢ > rⱼ`), then `γ_{rᵢ,bᵢ} ≥ γ_{rⱼ,bⱼ}` pointwise, so `γᵢ` is redundant — contradicting the
irredundancy clause of Definition 4.1. The library's `DeepWiki.IsConcaveNormalForm.burst_strictMono`. -/
theorem prop_4_1_burst {l : List (ℝ≥0 × ℝ≥0)} (h : IsConcaveNormalForm l) :
    l.Pairwise (fun a b => a.2 < b.2) :=
  h.burst_strictMono

/-- **Proposition 4.1, item 3** (§4.2.1, p.63): in a concave normal form the intersection points
`tᵢ` are strictly increasing. The consecutive crossings satisfy `tbCross γᵢ γᵢ₊₁ < tbCross γᵢ₊₁ γᵢ₊₂`
for every `i` with `i+2 < n` — the middle bucket's irredundancy witness sandwiches a time strictly
between the two crossings. The library's `DeepWiki.IsConcaveNormalForm.cross_strictMono`. -/
theorem prop_4_1_cross_mono {l : List (ℝ≥0 × ℝ≥0)} (h : IsConcaveNormalForm l)
    {i : ℕ} (hi : i + 2 < l.length) :
    tbCross (l.get ⟨i, by omega⟩).1 (l.get ⟨i, by omega⟩).2
            (l.get ⟨i + 1, by omega⟩).1 (l.get ⟨i + 1, by omega⟩).2 <
    tbCross (l.get ⟨i + 1, by omega⟩).1 (l.get ⟨i + 1, by omega⟩).2
            (l.get ⟨i + 2, by omega⟩).1 (l.get ⟨i + 2, by omega⟩).2 :=
  h.cross_strictMono hi

/-- **Proposition 4.1, item 4** (§4.2.1, p.63), general piecewise form: a non-empty concave PWL
function equals *one of its token-buckets* `γⱼ` at every time (the finite minimum is always
attained) — the book's "the function is piecewise linear". Identifying *which* `γⱼ` on `[tᵢ,tᵢ₊₁]`
is the remaining ordering claim. The library's `DeepWiki.exists_mem_concaveNFEval_eq`. -/
theorem prop_4_1_piecewise {l : List (ℝ≥0 × ℝ≥0)} (hne : l ≠ []) (t : ℝ≥0) :
    ∃ s ∈ l, concaveNFEval l t = tbEReal s.1 s.2 t :=
  exists_mem_concaveNFEval_eq hne t

/-- **Proposition 4.1, item 4** (§4.2.1, p.63), the per-interval formula — fully closed. On the
`i`-th inter-crossing interval `[tᵢ, tᵢ₊₁]` (bounding crossings, with the conventions `t₁ = 0` and
`tₙ₊₁ = ∞` made vacuous by the conditional hypotheses), the concave PWL function `⋀ⱼ γⱼ` coincides
with its `i`-th token-bucket `γ_{rᵢ,bᵢ}`. Proof: transitive minimality of `γᵢ` on the interval
(chaining the crossing orderings up and down the slope-sorted list) feeds `concaveNFEval_eq_of_isMin`.
The library's `DeepWiki.IsConcaveNormalForm.concaveNFEval_eq_get_of_mem_interval`. -/
theorem prop_4_1_interval {l : List (ℝ≥0 × ℝ≥0)} (h : IsConcaveNormalForm l) {t : ℝ≥0}
    (i : Fin l.length)
    (hlo : ∀ hi : 1 ≤ i.val, tbCross (l.get ⟨i.val - 1, by omega⟩).1 (l.get ⟨i.val - 1, by omega⟩).2
                                      (l.get i).1 (l.get i).2 ≤ t)
    (hhi : ∀ hi : i.val + 1 < l.length, t ≤ tbCross (l.get i).1 (l.get i).2
                                          (l.get ⟨i.val + 1, hi⟩).1 (l.get ⟨i.val + 1, hi⟩).2) :
    concaveNFEval l t = tbEReal (l.get i).1 (l.get i).2 t :=
  h.concaveNFEval_eq_get_of_mem_interval i hlo hhi

/-- **Proposition 4.1, item 4** (§4.2.1, p.63), pointwise envelope form: at any time where a
token-bucket of the list attains the minimum, the concave PWL function equals it,
`⋀ⱼ γⱼ(t) = γᵢ(t)`. With the crossing ordering (`def_4_1_cross`) this gives the book's
per-interval statement on `[tᵢ,tᵢ₊₁]` once `γᵢ` is shown minimal there. The library's
`DeepWiki.concaveNFEval_eq_of_isMin`. -/
theorem prop_4_1_envelope {l : List (ℝ≥0 × ℝ≥0)} {s : ℝ≥0 × ℝ≥0} (hs : s ∈ l) {t : ℝ≥0}
    (hmin : ∀ s' ∈ l, tbEReal s.1 s.2 t ≤ tbEReal s'.1 s'.2 t) :
    concaveNFEval l t = tbEReal s.1 s.2 t :=
  concaveNFEval_eq_of_isMin hs hmin

/-- **§4.2.1** (p.63), the convex representation (dual of Definition 4.1): a convex
piecewise-linear function is the pointwise *supremum* of rate-latency curves `β_{Rᵢ,Tᵢ}`
(`⨆ᵢ β_{Rᵢ,Tᵢ}`), the dual of the concave "minimum of token-buckets". The library's
`DeepWiki.convexNFEval`; each `β_{R,T}` is convex (`DeepWiki.isConvexEReal_rateLatencyEReal`, the
dual of `isConcaveEReal_tbEReal`) and so is the supremum (`DeepWiki.isConvexEReal_convexNFEval`). -/
noncomputable def def_4_1_convex := @convexNFEval

/-- **§4.2.1** (p.63): the convex representation is convex (dual of `prop_4_1_concave`). The
library's `DeepWiki.isConvexEReal_convexNFEval`. -/
theorem prop_4_1_convex (l : List (ℝ≥0 × ℝ≥0)) : IsConvexEReal (convexNFEval l) :=
  isConvexEReal_convexNFEval l

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

/-- **Theorem 4.1** (§4.2.2, p.65), the algorithm's data layer: a convex PWL is given by a base
value, an asymptotic slope, and a list of `(slope, length)` finite segments; `convexSegEval`
evaluates it. The library's `DeepWiki.convexSegEval`. -/
noncomputable def thm_4_1_segEval := @convexSegEval

/-- **Theorem 4.1** (§4.2.2, p.65), the algorithm's merge step: the `(min,plus)` convolution of two
convex PWL functions concatenates all segments by increasing slope; `mergeBySlope` slope-merges two
sorted segment lists. (Convolution-correctness `convexSegEval (mergeBySlope …) = minConv …` is the
remaining step; its transform-domain principle is `thm_4_1_legendre`.) The library's
`DeepWiki.mergeBySlope`. -/
noncomputable def thm_4_1_merge := @mergeBySlope

/-- **Theorem 4.1, base case** (§4.2.2, p.65): the `(min,plus)` convolution of two affine curves
`u ↦ a + p·u` and `u ↦ b + q·u` is the affine curve `a + b + min(p,q)·t` — the slower slope wins
and the bursts add. This is the single-semi-infinite-segment case (`mergeBySlope [] [] = []`), the
base of the slope-merge induction. The library's `DeepWiki.minConv_affine`. -/
theorem thm_4_1_base (a p b q t : ℝ≥0) :
    minConv (fun u => (((a + p * u : ℝ≥0) : ℝ) : EReal))
            (fun u => (((b + q * u : ℝ≥0) : ℝ) : EReal)) t
      = (((a + b + min p q * t : ℝ≥0) : ℝ) : EReal) :=
  DeepWiki.minConv_affine a p b q t

/-- **Theorem 4.1, the flat case** (§4.2.2, p.66): convolution by a flatter line. If a line
`u ↦ a + p·u` is flatter than the convex PWL `g` (every slope of `g` is `≥ p`), then
`(a + p·u) ∗ g = a + g(0) + p·t` — the flatter operand absorbs all the mass (the book's
`f ∗ g = f + g(0)` when each slope of `f` is `≤` each slope of `g`). The library's
`DeepWiki.minConv_flatLine_convexSegEval`. -/
theorem thm_4_1_flat (a p g0 sg : ℝ≥0) (l : List (ℝ≥0 × ℝ≥0))
    (hl : ∀ seg ∈ l, p ≤ seg.1) (hsg : p ≤ sg) (t : ℝ≥0) :
    minConv (fun u => (((a + p * u : ℝ≥0) : ℝ) : EReal))
            (fun v => (((convexSegEval g0 sg l v : ℝ≥0) : ℝ) : EReal)) t
      = (((a + g0 + p * t : ℝ≥0) : ℝ) : EReal) :=
  DeepWiki.minConv_flatLine_convexSegEval a p g0 sg l hl hsg t

/-- **Theorem 4.1, the balanced case** (§4.2.2, p.65): the full segment-merge *is* the `(min,plus)`
convolution when both convex PWLs share the asymptotic slope `s`. For slope-sorted segment lists
(`List.Pairwise (·.1 ≤ ·.1)`) with all finite slopes `≤ s`,
`(convexSegEval f0 s fsegs) ∗ (convexSegEval g0 s gsegs) = convexSegEval (f0+g0) s (mergeBySlope
fsegs gsegs)` — no truncation needed, since every finite slope is `< s = min(ρf,ρg)`. Proved by the
slope-peel induction (peel the globally flattest leading segment; base case `thm_4_1_base`). The
library's `DeepWiki.minConv_convexSegEval_eq_merge`. The remaining general case is the *unbalanced*
`ρf ≠ ρg`, where the merge must truncate at `min(ρf,ρg)`. -/
theorem thm_4_1_balanced (s f0 g0 : ℝ≥0) (fsegs gsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a b => a.1 ≤ b.1) fsegs)
    (hgsort : List.Pairwise (fun a b => a.1 ≤ b.1) gsegs)
    (hfs : ∀ seg ∈ fsegs, seg.1 ≤ s) (hgs : ∀ seg ∈ gsegs, seg.1 ≤ s) (t : ℝ≥0) :
    minConv (fun u => (((convexSegEval f0 s fsegs u : ℝ≥0) : ℝ) : EReal))
            (fun v => (((convexSegEval g0 s gsegs v : ℝ≥0) : ℝ) : EReal)) t
      = (((convexSegEval (f0 + g0) s (mergeBySlope fsegs gsegs) t : ℝ≥0) : ℝ) : EReal) :=
  DeepWiki.minConv_convexSegEval_eq_merge s f0 g0 fsegs gsegs hfsort hgsort hfs hgs t

/-! **Remark** (§4.3.3, p.80): On the discrete domain ℕ, (F_ℕ, ∧, ∗_ℕ) is a dioid; the library's function complete-dioid (FPlus over the ℝ≥0 domain) carries the same (min,conv) dioid algebra. Library: FPlus, isSubCompleteDioid_FPlus. -/

end DeepWiki.Dnc
