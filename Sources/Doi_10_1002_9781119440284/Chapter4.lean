import DeepWiki.NetworkCalculus.ConcaveDioid
import DeepWiki.NetworkCalculus.ConcaveProps
import DeepWiki.NetworkCalculus.ConvexConvolutionLegendre
import DeepWiki.NetworkCalculus.ConcavePWLNormalForm
import DeepWiki.NetworkCalculus.ConvexPWLNormalForm
import DeepWiki.NetworkCalculus.ConvexSegmentMerge
import DeepWiki.NetworkCalculus.ConvexSegmentMergeTrunc
import DeepWiki.NetworkCalculus.ConcaveSegmentMerge
import DeepWiki.NetworkCalculus.ConvexConvByLine
import DeepWiki.NetworkCalculus.ConvexConcaveReadback
import DeepWiki.NetworkCalculus.ConvexSegEvalSplit
import DeepWiki.NetworkCalculus.ConvexConcaveCrossingPoint
import DeepWiki.NetworkCalculus.ConvexConcaveCrossingCoord
import DeepWiki.NetworkCalculus.ConvexConcaveCrossingMulti
import DeepWiki.NetworkCalculus.ConvexConcaveCollapse
import DeepWiki.NetworkCalculus.ConvexConcaveRender
import DeepWiki.NetworkCalculus.PwlLowerEnvelope
import DeepWiki.NetworkCalculus.PwlMerge
import DeepWiki.NetworkCalculus.PwlMergeOutput
import DeepWiki.NetworkCalculus.SegmentDeconv
import DeepWiki.NetworkCalculus.SegmentDeconvTwo
import DeepWiki.NetworkCalculus.SegmentDeconvComposite
import DeepWiki.NetworkCalculus.SegmentDeconvCurve
import DeepWiki.NetworkCalculus.SegmentDeconvConcat
import DeepWiki.NetworkCalculus.SegmentConvolution
import DeepWiki.NetworkCalculus.SpotClosureUPP
import DeepWiki.NetworkCalculus.SegmentClosureUPP
import DeepWiki.NetworkCalculus.Containers
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
§4.2: Theorem 4.2, the general (finite-support) form — the three-part `convex–concave–convex`
decomposition `[external]`: the book itself defers the formal proof to [BOU 16a]; the final convex
part appears only for *bounded*-support functions, which the infinite-support `convexSegEval` /
token-bucket model does not represent. (The infinite-support case — `convex-then-concave` per the
book's own §4.2 note — is fully formalized with explicit single-`Pwl` output, the cataloged
`thm_4_2_output_pwl` and its supporting `thm_4_2_*`; Lemma 4.1's per-line engine + ordering are
`lemma_4_1_line` / `thm_4_2_ordering_*` / `thm_4_2_crossing_*`.)
§4.3: Lemma 4.7 (sub-additive-closure factorization, Lagrange's trick `(f∧g∗h*) = f*∗(δ₀∧g∗(g∧h)*)`)
`[research]`; Lemma 4.9 (closure of an open segment is UPP) `[infra]` — the per-segment geometry is done
(`lemma_4_9_powers`: the `n`-fold power is the open segment of the same slope `s` on `(n·a, n·b)`);
what remains is the order-theoretic infimum-selection over `⨅ₙ σⁿ` (which `n` wins per `t`, the rank,
the `closure(t+a) = closure t + s·a` period step).
§4.4 containers: Definition 4.2 (container = curve-interval `[f̲,f̄]`) DONE (`def_4_2`/`Container`);
Proposition 4.2 (same Legendre–Fenchel transform ↔ equal convex biconjugates) DONE (`prop_4_2`, both
directions); Proposition 4.3 congruence is an equivalence relation DONE (`prop_4_3_setoid`), but its
**quotient dioid `F↑/L` operations [4.7]–[4.9]** (`⊓`/`∗`/`⋆` well-defined on the quotient) remain
`[infra]`; Definition 4.3 (canonical representation); Definition 4.4 (maximal uncertainty); Definition
4.5 (inclusion functions); Proposition 4.4 (canonical upper bound); Lemma 4.10; Theorem 4.4 — all
`[research]` (need the `F_acv` almost-concave class + asymptotic-slope `ρ` typing, not yet built);
Remark 4.1. -/

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

/-- **Theorem 4.1, the concave case** (§4.2.1, p.62): for *concave* PWL functions the `(min,plus)`
convolution is the pointwise *minimum* — realized on the token-bucket-list representation as plain
**concatenation**: `(⋀ᵢ γ_{r¹ᵢ,b¹ᵢ}) ∗ (⋀ⱼ γ_{r²ⱼ,b²ⱼ}) = ⋀ over (l₁ ++ l₂)` (for non-empty lists,
both null at the origin). The dual of the convex segment-merge — far simpler, since concave
convolution needs no slope sort, only list append. The library's
`DeepWiki.minConv_concaveNFEval_eq_concaveNFEval_append`. -/
theorem thm_4_1_concave {l₁ l₂ : List (ℝ≥0 × ℝ≥0)} (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) :
    minConv (concaveNFEval l₁) (concaveNFEval l₂) = concaveNFEval (l₁ ++ l₂) :=
  DeepWiki.minConv_concaveNFEval_eq_concaveNFEval_append h₁ h₂

/-- **Theorem 4.2** (§4.2.2, p.68), the distribution step: convolution by a concave PWL distributes
over its token-bucket meet, `f ∗ (⊓ⱼ γⱼ) = ⊓ⱼ (f ∗ γⱼ)`. In the foldr representation
`concaveNFEval l = foldr (γ ⊓ ·) ⊤`, convolution pushes inside termwise (`minConv_inf` — the general
fact that `(min,plus)` convolution distributes over `⊓`). For a *convex* `f` each `f ∗ γⱼ` is then the
convex-by-line value (`lemma_4_1_line`), making the convex-by-concave convolution computable; this is
the engine of Theorem 4.2's algorithm. The library's `DeepWiki.minConv_concaveNFEval_foldr`
(and the underlying `DeepWiki.minConv_inf`). -/
theorem thm_4_2_distrib (f : ℝ≥0 → EReal) (l : List (ℝ≥0 × ℝ≥0)) :
    minConv f (concaveNFEval l)
      = l.foldr (fun rb acc => minConv f (tbEReal rb.1 rb.2) ⊓ acc) (minConv f topCurve) :=
  DeepWiki.minConv_concaveNFEval_foldr f l

/-- **Theorem 4.2** (§4.2.2, p.68), structural bound: convolution by a (non-empty) concave PWL only
lowers the curve, `f ∗ concaveNFEval l ≤ f` — the whole-list version of `f ∗ γⱼ ≤ f`, since a
non-empty concave PWL is null at the origin. The library's `DeepWiki.minConv_concaveNFEval_le_self`. -/
theorem thm_4_2_le_self (f : ℝ≥0 → EReal) {l : List (ℝ≥0 × ℝ≥0)} (hne : l ≠ []) (t : ℝ≥0) :
    minConv f (concaveNFEval l) t ≤ f t :=
  DeepWiki.minConv_concaveNFEval_le_self f hne t

/-- **Theorem 4.2** (§4.2.2, p.68), the readback step. Each per-bucket convolution reads back as a
meet, `f ∗ γ_{r,b} = (f ∗ lineᵣᵦ) ⊓ f`, where `lineᵣᵦ = convexSegEval b r []`, so the Lemma 4.1
engine computes the line factor. Concretely, for a convex PWL `f = convexSegEval f0 fs fsegs`
(`r ≤ fs`), *below the bucket's breakpoint* `u* = segLenSum (truncSegs r fsegs)` the token bucket is
inactive and `f ∗ γ_{r,b} = f` (the line factor `f + b ≥ f` loses the meet). The library's
`DeepWiki.minConv_tbEReal_eq_line_inf` / `DeepWiki.minConv_tbEReal_convexSegEval_below`. -/
theorem thm_4_2_readback_below (f0 fs r b : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs)
    (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs) (hrf : r ≤ fs)
    {t : ℝ≥0} (ht : t ≤ segLenSum (truncSegs r fsegs)) :
    minConv (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) (tbEReal r b) t
      = (((convexSegEval f0 fs fsegs t : ℝ≥0) : ℝ) : EReal) :=
  DeepWiki.minConv_tbEReal_convexSegEval_below f0 fs r b fsegs hfsort hfs hrf ht

/-- **Theorem 4.2** (§4.2.2, p.68), the readback step *above* the breakpoint. For a convex PWL
`f = convexSegEval f0 fs fsegs` (`r ≤ fs`), at or beyond `u* = segLenSum (truncSegs r fsegs)` the
token bucket convolution is the meet of the line continuation `f(u*) + b + r·(t − u*)` and `f` — in
general neither term dominates (the line starts above by `b`, then `f` overtakes it; *which* term
wins on which sub-interval is the global simplification still open). The library's
`DeepWiki.minConv_tbEReal_convexSegEval_above`. -/
theorem thm_4_2_readback_above (f0 fs r b : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs)
    (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs) (hrf : r ≤ fs)
    {t : ℝ≥0} (ht : segLenSum (truncSegs r fsegs) ≤ t) :
    minConv (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) (tbEReal r b) t
      = (((convexSegEval f0 fs fsegs (segLenSum (truncSegs r fsegs)) + b
            + r * (t - segLenSum (truncSegs r fsegs)) : ℝ≥0) : ℝ) : EReal)
          ⊓ (((convexSegEval f0 fs fsegs t : ℝ≥0) : ℝ) : EReal) :=
  DeepWiki.minConv_tbEReal_convexSegEval_above f0 fs r b fsegs hfsort hfs hrf ht

/-- **Lemma 4.1 / Theorem 4.2** (§4.2.2, p.68), the ordering — first (tie) region. The breakpoint
`u*(r) = segLenSum (truncSegs r fsegs)` is monotone in the rate (`segLenSum_truncSegs_mono`: a
lower-rate bucket activates earlier). Hence below the *lower*-rate bucket's breakpoint (`r ≤ r'`,
`t ≤ u*(r) ≤ u*(r')`) *both* buckets are inactive and convolve to `f`, so `f ∗ γ_{r,b} = f ∗ γ_{r',b'}`
— they tie. This is the first of the outer Lemma 4.1's domination regions; the nontrivial direction
(which bucket strictly wins on the active region) remains. The library's
`DeepWiki.minConv_tbEReal_convexSegEval_eq_below`. -/
theorem thm_4_2_ordering_below_tie (f0 fs r r' b b' : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs)
    (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs) (hrf : r ≤ fs) (hr'f : r' ≤ fs) (hrr' : r ≤ r')
    {t : ℝ≥0} (ht : t ≤ segLenSum (truncSegs r fsegs)) :
    minConv (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) (tbEReal r b) t
      = minConv (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) (tbEReal r' b') t :=
  DeepWiki.minConv_tbEReal_convexSegEval_eq_below f0 fs r r' b b' fsegs hfsort hfs hrf hr'f hrr' ht

/-- **Lemma 4.1 / Theorem 4.2** (§4.2.2, p.68), the ordering — domination up to the higher
breakpoint. Convolving by a token bucket can only lower a curve (`f ∗ γ ≤ f`), so up to the
*higher*-rate bucket's breakpoint `u*(r')` — where the higher bucket is still inactive
(`f ∗ γ_{r',b'} = f`) — the lower-rate bucket's convolution dominates: `f ∗ γ_{r,b} ≤ f ∗ γ_{r',b'}`
for `t ≤ u*(r')`. So on `[0, u*(r')]` the lower-rate bucket is the one appearing in the min (the
higher bucket is redundant there). The library's `DeepWiki.minConv_tbEReal_convexSegEval_le_below`
(and the general `DeepWiki.minConv_tbEReal_le_self`). -/
theorem thm_4_2_ordering_le_below (f0 fs r r' b b' : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs)
    (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs) (hr'f : r' ≤ fs)
    {t : ℝ≥0} (ht' : t ≤ segLenSum (truncSegs r' fsegs)) :
    minConv (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) (tbEReal r b) t
      ≤ minConv (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) (tbEReal r' b') t :=
  DeepWiki.minConv_tbEReal_convexSegEval_le_below f0 fs r r' b b' fsegs hfsort hfs hr'f ht'

/-- **Theorem 4.2** (§4.2.2, p.68), the crossing — base case (`f` a single rate, `fsegs = []`). The
convolution is the meet of two affines `(f0 + b + r·t) ⊓ (f0 + fs·t)` for all `t`, and the crossing
`t = b/(fs−r)` splits it: left of it (`fs·t ≤ r·t + b`) the bucket is inactive, `f ∗ γ_{r,b} = f`;
right of it (`r·t + b ≤ fs·t`) the bucket's rate takes over, `f ∗ γ_{r,b} = f0 + b + r·t`. The
general piecewise-`f` crossing (locating the crossing within `f`'s segments) remains. The library's
`DeepWiki.minConv_tbEReal_line` / `_eq_f` / `_eq_line`. -/
theorem thm_4_2_crossing_single_rate (f0 fs r b : ℝ≥0) (hrf : r ≤ fs) (t : ℝ≥0) :
    (minConv (fun v => (((convexSegEval f0 fs [] v : ℝ≥0) : ℝ) : EReal)) (tbEReal r b) t
        = (((f0 + b + r * t : ℝ≥0) : ℝ) : EReal) ⊓ (((f0 + fs * t : ℝ≥0) : ℝ) : EReal)) ∧
    (fs * t ≤ r * t + b →
      minConv (fun v => (((convexSegEval f0 fs [] v : ℝ≥0) : ℝ) : EReal)) (tbEReal r b) t
        = (((f0 + fs * t : ℝ≥0) : ℝ) : EReal)) ∧
    (r * t + b ≤ fs * t →
      minConv (fun v => (((convexSegEval f0 fs [] v : ℝ≥0) : ℝ) : EReal)) (tbEReal r b) t
        = (((f0 + b + r * t : ℝ≥0) : ℝ) : EReal)) :=
  ⟨DeepWiki.minConv_tbEReal_line f0 fs r b hrf t,
   fun h => DeepWiki.minConv_tbEReal_line_eq_f f0 fs r b hrf h,
   fun h => DeepWiki.minConv_tbEReal_line_eq_line f0 fs r b hrf h⟩

/-- **Theorem 4.2** (§4.2.2, p.68), the crossing — general convex `f` (unified meet form). For *any*
convex PWL `f = convexSegEval f0 fs fsegs` (`r ≤ fs`), the bucket convolution is, for all `t`, the
pointwise meet of `f` and the truncated line through the breakpoint `u* = segLenSum (truncSegs r
fsegs)`: `f ∗ γ_{r,b} t = f(t) ⊓ (f(u*) + b + r·(t − u*))`. Generalizes `thm_4_2_crossing_single_rate`
(the `fsegs = []` case) to arbitrary segments — the crossing is the implicit pointwise `min`.
Locating *which* term wins (the single crossing point within `f`'s segments) needs `f`'s
minimum-growth-rate beyond `u*` (a `convexSegEval` decomposition-at-the-breakpoint), still open. The
library's `DeepWiki.minConv_tbEReal_convexSegEval_eq`. -/
theorem thm_4_2_crossing_general (f0 fs r b : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs)
    (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs) (hrf : r ≤ fs) (t : ℝ≥0) :
    minConv (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) (tbEReal r b) t
      = (((convexSegEval f0 fs fsegs t : ℝ≥0) : ℝ) : EReal)
        ⊓ (((convexSegEval f0 fs fsegs (segLenSum (truncSegs r fsegs)) + b
              + r * (t - segLenSum (truncSegs r fsegs)) : ℝ≥0) : ℝ) : EReal) :=
  DeepWiki.minConv_tbEReal_convexSegEval_eq f0 fs r b fsegs hfsort hfs hrf t

/-- **Theorem 4.2** (§4.2.2, p.68), the crossing engine — minimum growth rate beyond the breakpoint.
A convex PWL grows at least at rate `r` past `u* = segLenSum (truncSegs r fsegs)` (`r ≤ fs`):
`f(u*) + r·(t − u*) ≤ f(t)` for `t ≥ u*`. Proved by splitting `f` at `u*` (the prefix `truncSegs r
fsegs` fixes `[0,u*]`, the dropped steep tail — all slopes `> r` — runs beyond) and applying the
all-slopes-`≥ r` growth bound to the tail. This is what makes the crossing a *single* switch (the
excess `f(t) − f(u*) − r·(t−u*)` is monotone). The library's
`DeepWiki.convexSegEval_rate_past_breakpoint`. -/
theorem thm_4_2_growth_past_breakpoint (f0 fs r : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs) (hrf : r ≤ fs)
    {t : ℝ≥0} (ht : segLenSum (truncSegs r fsegs) ≤ t) :
    convexSegEval f0 fs fsegs (segLenSum (truncSegs r fsegs))
        + r * (t - segLenSum (truncSegs r fsegs))
      ≤ convexSegEval f0 fs fsegs t :=
  DeepWiki.convexSegEval_rate_past_breakpoint f0 fs r fsegs hfsort hrf ht

/-- **Theorem 4.2** (§4.2.2, p.68), the crossing — both regimes resolved (general convex `f`).
Off the meet form `f ∗ γ_{r,b} t = f(t) ⊓ (f(u*) + b + r·(t − u*))`, each side is pinned down by the
comparison: where `f ≤` the line continuation the bucket is slack and `f ∗ γ_{r,b} = f`; where the
line `≤ f` the bucket binds and `f ∗ γ_{r,b} = f(u*) + b + r·(t − u*)` (slope `r`). With
`thm_4_2_growth_past_breakpoint` the "`f ≤ line`" set is a down-set, so this is a single switch from
`f` to the bucket line. The library's `DeepWiki.minConv_tbEReal_convexSegEval_eq_f` /
`DeepWiki.minConv_tbEReal_convexSegEval_eq_line`. -/
theorem thm_4_2_crossing_resolved (f0 fs r b : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs)
    (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs) (hrf : r ≤ fs) (t : ℝ≥0) :
    (convexSegEval f0 fs fsegs t
        ≤ convexSegEval f0 fs fsegs (segLenSum (truncSegs r fsegs)) + b
            + r * (t - segLenSum (truncSegs r fsegs)) →
      minConv (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) (tbEReal r b) t
        = (((convexSegEval f0 fs fsegs t : ℝ≥0) : ℝ) : EReal)) ∧
    (convexSegEval f0 fs fsegs (segLenSum (truncSegs r fsegs)) + b
            + r * (t - segLenSum (truncSegs r fsegs))
        ≤ convexSegEval f0 fs fsegs t →
      minConv (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) (tbEReal r b) t
        = (((convexSegEval f0 fs fsegs (segLenSum (truncSegs r fsegs)) + b
              + r * (t - segLenSum (truncSegs r fsegs)) : ℝ≥0) : ℝ) : EReal)) :=
  ⟨fun h => DeepWiki.minConv_tbEReal_convexSegEval_eq_f f0 fs r b fsegs hfsort hfs hrf h,
   fun h => DeepWiki.minConv_tbEReal_convexSegEval_eq_line f0 fs r b fsegs hfsort hfs hrf h⟩

/-- **Theorem 4.2** (§4.2.2, p.68), the crossing as a single switch (contiguous regimes). The
slack region is an *initial* interval and the binding region a *final* interval, so `f ∗ γ_{r,b}`
switches once from `f` to the bucket line: (i) if it equals `f` at some `t₂ ≥ u*`, it equals `f` at
every `u* ≤ t₁ ≤ t₂` (down-set); (ii) if it equals the line at some `t₁ ≥ u*`, it equals the line at
every `t₂ ≥ t₁` (up-set, via the min-growth-rate `thm_4_2_growth_past_breakpoint`). No explicit
crossing coordinate is presumed. The library's `DeepWiki.minConv_tbEReal_convexSegEval_eq_f_of_le` /
`DeepWiki.minConv_tbEReal_convexSegEval_eq_line_of_le`. -/
theorem thm_4_2_crossing_single_switch (f0 fs r b : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs)
    (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs) (hrf : r ≤ fs)
    {t₁ t₂ : ℝ≥0} (h1 : segLenSum (truncSegs r fsegs) ≤ t₁) (h12 : t₁ ≤ t₂) :
    (convexSegEval f0 fs fsegs t₂ ≤ lineCont f0 fs r b fsegs t₂ →
      minConv (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) (tbEReal r b) t₁
        = (((convexSegEval f0 fs fsegs t₁ : ℝ≥0) : ℝ) : EReal)) ∧
    (lineCont f0 fs r b fsegs t₁ ≤ convexSegEval f0 fs fsegs t₁ →
      minConv (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) (tbEReal r b) t₂
        = (((lineCont f0 fs r b fsegs t₂ : ℝ≥0) : ℝ) : EReal)) :=
  ⟨fun h => DeepWiki.minConv_tbEReal_convexSegEval_eq_f_of_le f0 fs r b fsegs hfsort hfs hrf h1 h12 h,
   fun h => DeepWiki.minConv_tbEReal_convexSegEval_eq_line_of_le f0 fs r b fsegs hfsort hfs hrf h1 h12 h⟩

/-- **Theorem 4.2** (§4.2.2, p.68), the `r = fs` edge case: when the bucket rate equals `f`'s
asymptotic slope, the bucket is *slack forever* — `f ∗ γ_{fs,b} = f` for all `t` (past `u*` the
growth is capped at `fs = r`, so `f` never reaches the line `f(u*)+b+r·(t−u*)`; below `u*` by
monotonicity). The crossing's infinite-threshold case (no binding region). The library's
`DeepWiki.minConv_tbEReal_convexSegEval_eq_f_of_rate_eq`. -/
theorem thm_4_2_crossing_slack_forever (f0 fs b : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs)
    (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs) (t : ℝ≥0) :
    minConv (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) (tbEReal fs b) t
      = (((convexSegEval f0 fs fsegs t : ℝ≥0) : ℝ) : EReal) :=
  DeepWiki.minConv_tbEReal_convexSegEval_eq_f_of_rate_eq f0 fs b fsegs hfsort hfs t

/-- **Theorem 4.2** (§4.2.2, p.68), the explicit crossing coordinate `u**` (single steep-tail case).
Beyond `u*` the excess `E(d) = f(u*+d) − f(u*) − r·d` is monotone (`DeepWiki.excess_mono`) and `0` at
`d = 0`. When the steep tail is a single segment `dropSegs r fsegs = [(s,ℓ)]` with `r < s` and `b`
reachable (`b ≤ (s−r)·ℓ`), the crossing offset is **explicit**, `δ = b/(s−r)`, with `E(δ) = b`; so
with `u** = u* + δ` the convolution is `f` for `u* ≤ t ≤ u**` and the bucket line `f(u*)+b+r·(t−u*)`
for `t ≥ u**`. The library's `DeepWiki.minConv_tbEReal_eq_f_below_crossing` /
`DeepWiki.minConv_tbEReal_eq_line_above_crossing` (offset `DeepWiki.crossingOffset_singleTail`). -/
theorem thm_4_2_crossing_coord (f0 fs r s ℓ b : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs)
    (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs) (hrf : r ≤ fs)
    (htail : dropSegs r fsegs = (s, ℓ) :: []) (hrs : r < s) (hb : b ≤ (s - r) * ℓ) :
    (∀ {t : ℝ≥0}, segLenSum (truncSegs r fsegs) ≤ t →
        t ≤ segLenSum (truncSegs r fsegs) + crossingOffset_singleTail r s b →
      minConv (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) (tbEReal r b) t
        = (((convexSegEval f0 fs fsegs t : ℝ≥0) : ℝ) : EReal)) ∧
    (∀ {t : ℝ≥0}, segLenSum (truncSegs r fsegs) + crossingOffset_singleTail r s b ≤ t →
      minConv (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) (tbEReal r b) t
        = (((convexSegEval f0 fs fsegs (segLenSum (truncSegs r fsegs)) + b
              + r * (t - segLenSum (truncSegs r fsegs)) : ℝ≥0) : ℝ) : EReal)) :=
  ⟨fun ht htu => DeepWiki.minConv_tbEReal_eq_f_below_crossing f0 fs r s ℓ b fsegs hfsort hfs hrf
      htail hrs hb ht htu,
   fun htu => DeepWiki.minConv_tbEReal_eq_line_above_crossing f0 fs r s ℓ b fsegs hfsort hfs hrf
      htail hrs hb htu⟩

/-- **Theorem 4.2** (§4.2.2, p.68), the explicit crossing coordinate `u**` — *full multi-segment
tail*. The single-tail case generalizes: over the whole steep tail `dropSegs r fsegs` the excess
`E(d)` is a ramp with slopes `(sₖ − r)` summing to `tailExcess r (dropSegs r fsegs)`; the crossing
offset `d* = crossingOffset r (dropSegs r fsegs) b` walks the tail subtracting each segment's excess
`(sₖ−r)·ℓₖ` until a segment saturates, then `b_rem/(sₖ−r)` inside it, with `E(d*) = b` whenever `b`
is reachable (`b ≤ tailExcess`). So with `u** = u* + d*`, `f ∗ γ_{r,b} = f` for `u* ≤ t ≤ u**` and the
bucket line for `t ≥ u**`. This completes the Theorem 4.2 single-bucket crossing for an arbitrary
convex PWL `f`. The library's `DeepWiki.minConv_tbEReal_eq_f_below_crossing_multi` /
`DeepWiki.minConv_tbEReal_eq_line_above_crossing_multi` (offset `DeepWiki.crossingOffset`, ramp
`DeepWiki.tailExcess`). -/
theorem thm_4_2_crossing_coord_multi (f0 fs r b : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs)
    (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs) (hrf : r ≤ fs)
    (hb : b ≤ tailExcess r (dropSegs r fsegs)) :
    (∀ {t : ℝ≥0}, segLenSum (truncSegs r fsegs) ≤ t →
        t ≤ segLenSum (truncSegs r fsegs) + crossingOffset r (dropSegs r fsegs) b →
      minConv (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) (tbEReal r b) t
        = (((convexSegEval f0 fs fsegs t : ℝ≥0) : ℝ) : EReal)) ∧
    (∀ {t : ℝ≥0}, segLenSum (truncSegs r fsegs) + crossingOffset r (dropSegs r fsegs) b ≤ t →
      minConv (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) (tbEReal r b) t
        = (((convexSegEval f0 fs fsegs (segLenSum (truncSegs r fsegs)) + b
              + r * (t - segLenSum (truncSegs r fsegs)) : ℝ≥0) : ℝ) : EReal)) :=
  ⟨fun ht htu => DeepWiki.minConv_tbEReal_eq_f_below_crossing_multi f0 fs r b fsegs hfsort hfs hrf
      hb ht htu,
   fun htu => DeepWiki.minConv_tbEReal_eq_line_above_crossing_multi f0 fs r b fsegs hfsort hfs hrf
      hb htu⟩

/-- **Theorem 4.2** (§4.2.2, p.68), the collapse: convolving (`IsNeverBot`) `f` by a non-empty
concave PWL is the bucket-line lower envelope capped by `f` **once**,
`f ∗ concaveNFEval l = lineMeet f l ⊓ f`, i.e. `f ∗ (⊓ⱼ γⱼ) = (⊓ⱼ f ∗ lineⱼ) ⊓ f`. The per-bucket
readback gives a repeated `⊓ f`; this pulls the single `f`-cap out of the meet, leaving the meet of
the line-convolutions (each computed by Lemma 4.1 / the crossing). The structural form of Theorem
4.2's output. The library's `DeepWiki.minConv_concaveNFEval_eq_lineMeet_inf` (envelope
`DeepWiki.lineMeet`). -/
theorem thm_4_2_collapse {f : ℝ≥0 → EReal} (hf : IsNeverBot f) {l : List (ℝ≥0 × ℝ≥0)} (hne : l ≠ []) :
    minConv f (concaveNFEval l) = lineMeet f l ⊓ f :=
  minConv_concaveNFEval_eq_lineMeet_inf hf hne

/-- **Theorem 4.2, rendered output** (§4.2.2, p.68). For a convex PWL `f = convexSegEval f0 fs fsegs`
and a non-empty token-bucket list `l` whose every rate is `≤ fs`, the convex-by-concave convolution
is an explicit **finite meet of concrete convex PWL curves**:
`f ∗ concaveNFEval l = (⊓ⱼ convexSegEval (bⱼ+f0) rⱼ (truncSegs rⱼ fsegs)) ⊓ convexSegEval f0 fs fsegs`.
Each bucket `(rⱼ,bⱼ)` contributes `f`'s segments truncated at its rate `rⱼ` and lifted by its burst
`bⱼ` (`minConv_line_render` / `minConv_line_convexSegEval`), met together (`renderedLineMeet`) and
capped by `f` (the collapse `thm_4_2_collapse`). This is Theorem 4.2's output curve as a lower
envelope of explicit pieces — the remaining lower-envelope *merge* into a single segment list is the
presentation/algorithmic step. The library's `DeepWiki.minConv_concaveNFEval_render`
(envelope `DeepWiki.renderedLineMeet`). -/
theorem thm_4_2_render (f0 fs : ℝ≥0) (fsegs l : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs) (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs)
    (hl : ∀ rb ∈ l, rb.1 ≤ fs) (hne : l ≠ []) :
    minConv (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) (concaveNFEval l)
      = renderedLineMeet f0 fsegs l
          ⊓ (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) :=
  minConv_concaveNFEval_render f0 fs fsegs l hfsort hfs hl hne

/-- **Theorem 4.2, output well-formedness** (§4.2.2). The rendered convex-by-concave output is a
genuine **monotone** curve — the meet of the monotone rendered envelope and the monotone `f`. (The
output is in general *convex-then-concave* — a convex head `f`, then decreasing-rate bucket lines —
so collapsing it to a single PWL *segment list* needs a general arbitrary-slope PWL datatype, the
remaining `[infra]` step; the result is fully pinned down here as a finite meet of explicit pieces.)
The library's `DeepWiki.monotone_minConv_concaveNFEval_render`. -/
theorem thm_4_2_render_monotone (f0 fs : ℝ≥0) (fsegs l : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs) (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs)
    (hl : ∀ rb ∈ l, rb.1 ≤ fs) (hne : l ≠ []) :
    Monotone (minConv (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal))
      (concaveNFEval l)) :=
  monotone_minConv_concaveNFEval_render f0 fs fsegs l hfsort hfs hl hne

/-- **Theorem 4.2, the lower-envelope merge primitive** (§4.2.2). The pointwise minimum of two
general PWL curves is itself computed as a single PWL: `lowerEnvEval … t = min (convexSegEval f0 fs
fsegs t) (convexSegEval g0 gs gsegs t)` (`lowerEnvEval_eq_min'`), with the affine base case
`affineMin a p b q t = min (a+p·t) (b+q·t)` (`affineMin_eq_min`, crossing `affineCross`). This is the
general arbitrary-slope PWL merge the convex-then-concave Theorem 4.2 output needs: iterating it over
the rendered meet pieces (`thm_4_2_render`) collapses them into one PWL. The library's
`DeepWiki.lowerEnvEval_eq_min'` / `DeepWiki.affineMin_eq_min` (datatype `DeepWiki.Pwl`). -/
theorem thm_4_2_lower_envelope (f0 fs g0 gs : ℝ≥0) (fsegs gsegs : List (ℝ≥0 × ℝ≥0)) (t : ℝ≥0) :
    lowerEnvEval f0 fs g0 gs fsegs gsegs t
      = min (convexSegEval f0 fs fsegs t) (convexSegEval g0 gs gsegs t) :=
  lowerEnvEval_eq_min' f0 fs g0 gs fsegs gsegs t

/-- **Theorem 4.2, list-producing merge** (§4.2.2). The lower envelope is realized as an explicit
single `Pwl` segment list: `lowerEnvMerge p q : Pwl` with `(lowerEnvMerge p q).eval = min p.eval
q.eval` (`lowerEnvMerge_eval` — emits the merged segments via `affineMinPwl`/`segsTrunc`, correctness
mirroring `lowerEnvEval`), folded by `mergeAll p0 ps : Pwl` over finitely many curves
(`mergeAll_eval`: the running pointwise min). So the **pointwise minimum of finitely many PWLs is one
explicit `Pwl`** — the representation the convex-then-concave Theorem 4.2 output needs (its meet of
`thm_4_2_render` pieces folds to a single `Pwl`). The library's `DeepWiki.lowerEnvMerge_eval` /
`DeepWiki.mergeAll_eval` (datatype `DeepWiki.Pwl`). -/
theorem thm_4_2_merge_pwl (p q : Pwl) (t : ℝ≥0) :
    (lowerEnvMerge p q).eval t = min (p.eval t) (q.eval t) :=
  lowerEnvMerge_eval p q t

/-- **Theorem 4.2, single-`Pwl` output** (§4.2.2, p.68) — the capstone. The convex-by-concave
convolution is the `EReal` coe of **one** explicit `Pwl`'s evaluation:
`f ∗ concaveNFEval l = ⇑(mergeAll ⟨f0,fsegs,fs⟩ (l.map (fun (r,b) => ⟨b+f0, truncSegs r fsegs, r⟩)))`,
for a convex `f = convexSegEval f0 fs fsegs` and a non-empty bucket list `l` with rates `≤ fs`. The
rendered meet of explicit pieces (`thm_4_2_render`) folds, via the list-producing `mergeAll`
(`thm_4_2_merge_pwl`), into a single arbitrary-slope `Pwl` segment list. This is the **infinite-support**
case of Theorem 4.2 (both operands have infinite support; the book's §4.2 note says the result is then
`convex-then-concave`, here pinned down as one explicit curve); the general finite-support three-part
decomposition is `[external]` (deferred to [BOU 16a], see the chapter's `NOT YET FORMALIZED` block).
The library's `DeepWiki.minConv_concaveNFEval_eq_mergeAll`. -/
theorem thm_4_2_output_pwl (f0 fs : ℝ≥0) (fsegs l : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs) (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs)
    (hl : ∀ rb ∈ l, rb.1 ≤ fs) (hne : l ≠ []) :
    minConv (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) (concaveNFEval l)
      = fun t => ((((mergeAll ⟨f0, fsegs, fs⟩
            (l.map (fun rb => (⟨rb.2 + f0, truncSegs rb.1 fsegs, rb.1⟩ : Pwl)))).eval t : ℝ≥0)
            : ℝ) : EReal) :=
  minConv_concaveNFEval_eq_mergeAll f0 fs fsegs l hfsort hfs hl hne

/-- **Theorem 4.1, the unbalanced case** (§4.2.2, p.65) — completing Theorem 4.1. When the two
convex PWLs have *different* asymptotic slopes (`ρf = sf ≤ sg = ρg`), the merge must **truncate**:
`g`'s segments steeper than `sf` are absorbed into the flatter asymptote. With `truncSegs sf gsegs`
(= `gsegs.takeWhile (·.1 ≤ sf)`),
`(convexSegEval f0 sf fsegs) ∗ (convexSegEval g0 sg gsegs) = convexSegEval (f0+g0) sf (mergeBySlope
fsegs (truncSegs sf gsegs))`. Proved by reduction to the balanced case (`thm_4_1_balanced`) via
"the convolution ignores `g`'s steep part" (`minConv_convexSegEval_truncSegs`, using the
`sf`-Lipschitz-from-above bound). With `thm_4_1_base`/`_flat`/`_balanced` this closes Theorem 4.1.
The library's `DeepWiki.minConv_convexSegEval_unbalanced`. -/
theorem thm_4_1_unbalanced (sf sg f0 g0 : ℝ≥0) (fsegs gsegs : List (ℝ≥0 × ℝ≥0)) (hsfg : sf ≤ sg)
    (hfsort : List.Pairwise (fun a b => a.1 ≤ b.1) fsegs)
    (hgsort : List.Pairwise (fun a b => a.1 ≤ b.1) gsegs)
    (hfs : ∀ seg ∈ fsegs, seg.1 ≤ sf) (hgs : ∀ seg ∈ gsegs, seg.1 ≤ sg) (t : ℝ≥0) :
    minConv (fun u => (((convexSegEval f0 sf fsegs u : ℝ≥0) : ℝ) : EReal))
            (fun v => (((convexSegEval g0 sg gsegs v : ℝ≥0) : ℝ) : EReal)) t
      = (((convexSegEval (f0 + g0) sf (mergeBySlope fsegs (truncSegs sf gsegs)) t : ℝ≥0)
            : ℝ) : EReal) :=
  DeepWiki.minConv_convexSegEval_unbalanced sf sg f0 g0 fsegs gsegs hsfg hfsort hgsort hfs hgs t

/-- **Lemma 4.1** (§4.2.2, p.68), the per-line engine: the `(min,plus)` convolution of a convex PWL
`f = convexSegEval f0 fs fsegs` by a single line `ℓ(u) = c + q·u` (with `q ≤ fs`). Let `u* =
segLenSum (truncSegs q fsegs)` be the breakpoint where `f`'s slope first reaches `q`. Then below the
breakpoint the convex part wins (`f + c`), and above it the line's slope takes over
(`f(u*) + c + q·(t−u*)`). This is the engine of Lemma 4.1 (the concave operand's `j`-th piece `gⱼ`
is such a line); the library's `DeepWiki.minConv_line_convexSegEval_below` /
`DeepWiki.minConv_line_convexSegEval_above` (and `minConv_convexSegEval_steepLine` for `fs ≤ q`). -/
theorem lemma_4_1_line (f0 fs c q : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a b => a.1 ≤ b.1) fsegs)
    (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs) (hqf : q ≤ fs) (t : ℝ≥0) :
    (t ≤ segLenSum (truncSegs q fsegs) →
        minConv (fun u => (((convexSegEval c q [] u : ℝ≥0) : ℝ) : EReal))
                (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) t
          = (((convexSegEval f0 fs fsegs t + c : ℝ≥0) : ℝ) : EReal)) ∧
    (segLenSum (truncSegs q fsegs) ≤ t →
        minConv (fun u => (((convexSegEval c q [] u : ℝ≥0) : ℝ) : EReal))
                (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) t
          = (((convexSegEval f0 fs fsegs (segLenSum (truncSegs q fsegs)) + c
                + q * (t - segLenSum (truncSegs q fsegs)) : ℝ≥0) : ℝ) : EReal)) :=
  ⟨fun ht => minConv_line_convexSegEval_below f0 fs c q fsegs hfsort hfs hqf ht,
   fun ht => minConv_line_convexSegEval_above f0 fs c q fsegs hfsort hfs hqf ht⟩

/-- **Lemma 4.6** (§4.3, p.77), the affine base case. The `(min,plus)` deconvolution of two affine
curves `u ↦ a + p·u` and `u ↦ b + q·u` is, in closed form, `a + p·t − b` when `p ≤ q` (the sup
`⨆ₛ g(t+s) − h(s)` is attained at `s = 0`, since the `s`-coefficient `p − q ≤ 0`), and `⊤` when
`q < p` (unbounded). The reusable building block for Lemma 4.6's two-segment deconvolution. The
library's `DeepWiki.minDeconv_affine_le` / `DeepWiki.minDeconv_affine_top`. -/
theorem lemma_4_6_affine (a p b q t : ℝ≥0) :
    (p ≤ q → minDeconv (affineE a p) (affineE b q) t
        = (((a + p * t : ℝ≥0) : ℝ) : EReal) - (((b : ℝ≥0) : ℝ) : EReal)) ∧
    (q < p → minDeconv (affineE a p) (affineE b q) t = ⊤) :=
  ⟨minDeconv_affine_le a p b q t, minDeconv_affine_top a p b q t⟩

/-- **Lemma 4.6** (§4.3, p.77), the rate-latency case. The `(min,plus)` deconvolution of two
rate-latency curves `β_{R,T}(u) = R·(u−T)₊` is, for the rate-ordering case `R₁ ≤ R₂`, in closed form
`R₁·(t + T₂ − T₁)₊` — the sup `⨆ₛ β₁(t+s) − β₂(s)` is attained at the shift `s = T₂` (where the
divisor vanishes). The rate-latency block of Lemma 4.6's two-segment deconvolution. The library's
`DeepWiki.minDeconv_rl_le` (rate-latency `DeepWiki.rlE`). -/
theorem lemma_4_6_rateLatency (R₁ T₁ R₂ T₂ t : ℝ≥0) (hR : R₁ ≤ R₂) :
    minDeconv (rlE R₁ T₁) (rlE R₂ T₂) t = (((R₁ * (t + T₂ - T₁) : ℝ≥0) : ℝ) : EReal) :=
  minDeconv_rl_le R₁ T₁ R₂ T₂ t hR

/-- **Lemma 4.6** (§4.3), the divisor-distribution engine: deconvolution distributes over a meet in
its *divisor* as a join, `g ⊘ (h₁ ⊓ h₂) = (g ⊘ h₁) ⊔ (g ⊘ h₂)` (since `−` is antitone in the divisor
and `⨆` of a `⊔` is the `⊔` of `⨆`s). This composes the affine/rate-latency blocks over a curve's
min-of-segments representation — the mechanism for the full two-segment Lemma 4.6. The library's
`DeepWiki.minDeconv_inf_right`. -/
theorem lemma_4_6_distrib {D : Type*} [Add D] (g h₁ h₂ : D → EReal) (t : D) :
    minDeconv g (h₁ ⊓ h₂) t = minDeconv g h₁ t ⊔ minDeconv g h₂ t :=
  minDeconv_inf_right g h₁ h₂ t

/-- **Lemma 4.6** (§4.3, p.77), the fast-divisor rate-latency case. When the divisor's rate is
*smaller* (`R₂ < R₁`), the deconvolution diverges: `β_{R₁,T₁} ⊘ β_{R₂,T₂} = ⊤` (for `s` past both
latencies both curves are affine with net slope `R₁ − R₂ > 0`, so the sup is unbounded). Completes
the rate-latency case alongside `lemma_4_6_rateLatency`. The library's `DeepWiki.minDeconv_rl_top`. -/
theorem lemma_4_6_rateLatency_top (R₁ T₁ R₂ T₂ t : ℝ≥0) (hR : R₂ < R₁) :
    minDeconv (rlE R₁ T₁) (rlE R₂ T₂) t = ⊤ :=
  minDeconv_rl_top R₁ T₁ R₂ T₂ t hR

/-- **Lemma 4.6** (§4.3), deconvolution by a min of two rate-latencies (a concave/2-segment divisor):
`β_{R₁,T₁} ⊘ (β_{R₂,T₂} ⊓ β_{R₃,T₃}) = term₂ ⊔ term₃`, each `termᵢ = R₁·(t+Tᵢ−T₁)₊` if `R₁ ≤ Rᵢ` else
`⊤` (`rlDeconvTerm`) — the rate-latency blocks composed through `lemma_4_6_distrib`. The library's
`DeepWiki.minDeconv_rl_inf_two`. -/
theorem lemma_4_6_inf_two (R₁ T₁ R₂ T₂ R₃ T₃ t : ℝ≥0) :
    minDeconv (rlE R₁ T₁) (rlE R₂ T₂ ⊓ rlE R₃ T₃) t
      = rlDeconvTerm R₁ T₁ R₂ T₂ t ⊔ rlDeconvTerm R₁ T₁ R₃ T₃ t :=
  minDeconv_rl_inf_two R₁ T₁ R₂ T₂ R₃ T₃ t

/-- **Lemma 4.6** (§4.3), deconvolution distributes over a list-meet of divisors as a join:
`g ⊘ (⊓ over l) = ⨆ h ∈ l, g ⊘ h` (the divisor-side analog of the convolution distribution
`thm_4_2_distrib`). Lets a deconvolution by a curve given as a `minInfList` of segment pieces be
read off termwise. The library's `DeepWiki.minDeconv_inf_list_right`. -/
theorem lemma_4_6_inf_list {D : Type*} [Add D] [Nonempty D] (g : D → EReal)
    (l : List (D → EReal)) (t : D) :
    minDeconv g (minInfList l) t = ⨆ h ∈ l, minDeconv g h t :=
  minDeconv_inf_list_right g l t

/-- **Lemma 4.6** (§4.3, p.77), the headline: deconvolution of a rate-latency by a *concave* PWL
divisor (a meet of rate-latency pieces) in closed form — the **join over the pieces** of the
single-piece terms: `β_{R₁,T₁} ⊘ (⊓ₚ β_{p}) = ⨆ p, rlDeconvTerm R₁ T₁ p.1 p.2 t`. Composes the
per-piece results (`minDeconv_rl_eq_term`) through the list distribution (`lemma_4_6_inf_list`).
The library's `DeepWiki.minDeconv_rl_minInfList` (affine/token-bucket variant
`DeepWiki.minDeconv_affine_minInfList`). -/
theorem lemma_4_6_concaveCurve (R₁ T₁ : ℝ≥0) (divisors : List (ℝ≥0 × ℝ≥0)) (t : ℝ≥0) :
    minDeconv (rlE R₁ T₁) (minInfList (divisors.map (fun p => rlE p.1 p.2))) t
      = ⨆ p ∈ divisors, rlDeconvTerm R₁ T₁ p.1 p.2 t :=
  minDeconv_rl_minInfList R₁ T₁ divisors t

/-- **Lemma 4.6** (§4.3), the dividend-side asymmetry. Deconvolution only *sub*-distributes over a
meet in the *dividend*: `(g₁ ⊓ g₂) ⊘ h ≤ (g₁ ⊘ h) ⊓ (g₂ ⊘ h)`, and equality FAILS in general (the
optimal shift `s` may differ between `g₁` and `g₂`) — in contrast to the *equality* `lemma_4_6_distrib`
on the divisor side. The library's `DeepWiki.minDeconv_inf_left_le`. -/
theorem lemma_4_6_inf_left_le {D : Type*} [Add D] (g₁ g₂ h : D → EReal) (t : D) :
    minDeconv (g₁ ⊓ g₂) h t ≤ minDeconv g₁ h t ⊓ minDeconv g₂ h t :=
  minDeconv_inf_left_le g₁ g₂ h t

/-- **Lemma 4.6** (§4.3), the dividend asymmetry is strict — a citable NON-THEOREM. The reverse of
`lemma_4_6_inf_left_le` is FALSE: `¬ ∀ g₁ g₂ h t, (g₁ ⊓ g₂) ⊘ h t = (g₁ ⊘ h t) ⊓ (g₂ ⊘ h t)`,
witnessed by elementary step curves where the optimal deconvolution shift differs between `g₁` and
`g₂` (`(g₁⊓g₂)⊘h = 0` but each `gᵢ⊘h = 1`, gap `0 < 1`). So deconvolution distributes over `⊓` in the
divisor (`lemma_4_6_distrib`, equality) but only sub-distributes in the dividend. The library's
`DeepWiki.not_forall_minDeconv_inf_left_eq` (strict witness `DeepWiki.minDeconv_inf_left_lt_witness`). -/
theorem lemma_4_6_inf_left_not_forall_eq :
    ¬ ∀ (g₁ g₂ h : ℝ≥0 → EReal) (t : ℝ≥0),
        minDeconv (g₁ ⊓ g₂) h t = minDeconv g₁ h t ⊓ minDeconv g₂ h t :=
  not_forall_minDeconv_inf_left_eq

/-- **Lemma 4.6** (§4.3, p.77), the LITERAL two-bounded-segment deconvolution. For two segments
`f = segBotE a b va sf` (bot-padded: `−∞` outside `[a,b]`, the book's "outside `J` set `g = −∞`") and
`g = segE c d vc sg` (top-padded), `f ⊘ g` on `(I−J)∩ℝ₊` is the two segments concatenated, **larger
slope first**, with the four regimes (`u` maximized when `sg ≤ sf`, minimized when `sf ≤ sg`; inner
vs. boundary optimum split at `t = b−d` / `t = a−c`). Anchored at `t = a−d` to `f(a⁺) − g(d⁻)`
(`minDeconv_segBotE_segE_anchor_of_slope_ge`). The library's four regime equalities
`DeepWiki.minDeconv_segBotE_segE_eq_of_slope_ge`(`_right`) / `_of_slope_lt`(`_left`). -/
theorem lemma_4_6_segments (a b va sf c d vc sg t : ℝ≥0) :
    (sg ≤ sf → a ≤ t + d → t + d ≤ b → c ≤ d →
        minDeconv (segBotE a b va sf) (segE c d vc sg) t
          = segBotE a b va sf (t + d) - segE c d vc sg d) ∧
    (sg ≤ sf → a ≤ b → t ≤ b → c ≤ b - t → b - t ≤ d →
        minDeconv (segBotE a b va sf) (segE c d vc sg) t
          = segBotE a b va sf b - segE c d vc sg (b - t)) ∧
    (sf ≤ sg → a ≤ b → t ≤ a → c ≤ a - t → a - t ≤ d →
        minDeconv (segBotE a b va sf) (segE c d vc sg) t
          = segBotE a b va sf a - segE c d vc sg (a - t)) ∧
    (sf ≤ sg → a ≤ t + c → t + c ≤ b → c ≤ d →
        minDeconv (segBotE a b va sf) (segE c d vc sg) t
          = segBotE a b va sf (t + c) - segE c d vc sg c) :=
  ⟨minDeconv_segBotE_segE_eq_of_slope_ge a b va sf c d vc sg t,
   minDeconv_segBotE_segE_eq_of_slope_ge_right a b va sf c d vc sg t,
   minDeconv_segBotE_segE_eq_of_slope_lt_left a b va sf c d vc sg t,
   minDeconv_segBotE_segE_eq_of_slope_lt a b va sf c d vc sg t⟩

/-- **Theorem 4.2 building block** (§4.3, p.77): the convolution of two bounded segments. It is
supported on `[a₁+a₂, b₁+b₂]` (`⊤` outside — `minConv_segE_segE_of_lt_left`/`_of_gt_right`), has corner
values `v₁+v₂` at `a₁+a₂` and `(v₁+s₁(b₁−a₁))+(v₂+s₂(b₂−a₂))` at `b₁+b₂`, and is **convex** (the split
objective is affine in `u`, so its inf is at an endpoint — `segPairObj_endpoints_le_minConv` plus the
per-split upper bound pin it between the endpoint-min and any admissible split). This is the per-piece
engine for computing convex∗concave as a min over segment-pair convolutions (the book's Theorem 4.2
algorithm). The library's `DeepWiki.minConv_segE_segE_left`/`_right`/`_of_lt_left` etc. -/
theorem thm_4_2_segConv_corners (a₁ b₁ v₁ s₁ a₂ b₂ v₂ s₂ : ℝ≥0) (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) :
    minConv (segE a₁ b₁ v₁ s₁) (segE a₂ b₂ v₂ s₂) (a₁ + a₂)
      = (((v₁ : ℝ≥0) : ℝ) : EReal) + (((v₂ : ℝ≥0) : ℝ) : EReal) :=
  minConv_segE_segE_left a₁ b₁ v₁ s₁ a₂ b₂ v₂ s₂ h₁ h₂

/-- **Lemma 4.8** (§4.3, p.78): the **sub-additive closure of a spot is ultimately pseudo-periodic**.
A spot `spotNN d c` (value `c` at `d`, `+∞` elsewhere, over `ℝ≥0∞`) has `n`-fold convolution power the
spot `spotNN (n•d) (n•c)`, so its closure `σ⋆ = ⨅ₙ σⁿ` is the arithmetic-progression staircase
`{(n·d, n·c)}` — which is `IsUPP` with rank `0`, period `d`, increment `c` (`0 < d`). The library's
`DeepWiki.spotClosure_isUPP` (powers `DeepWiki.minConvPow_spotNN`, periodicity
`DeepWiki.subadditiveClosureENN_spotNN_shift`). -/
theorem lemma_4_8 (d : ℝ≥0) (c : ℝ≥0∞) (hd : 0 < d) :
    IsUPP (subadditiveClosureENN (spotNN d c)) :=
  spotClosure_isUPP d c hd

/-- **Lemma 4.9** (§4.3, p.78), the per-segment geometry (toward "closure of an open segment is UPP").
The `n`-fold `(min,+)` convolution power of an open segment `segNN a b va s` is, on its `n`-fold open
support `(n·a, n·b)`, the open segment of the **same slope** `s`: `(σⁿ)(t) = n·va + s·(t − n·a)` (and
`= ⊤` off `(n·a, n·b)` for `n ≥ 1`). This is the first sentence of Lemma 4.9 — the building block of
the closure's pseudo-periodicity (`σ⋆ = ⨅ₙ σⁿ`). The order-theoretic infimum-selection step (which `n`
wins per `t`, the rank, the `closure(t+a) = closure t + s·a` period) is the remaining `[infra]` part.
The library's `DeepWiki.minConvPow_segNN_eq_affine` (support `_eq_top_of_le`/`_of_ge`). -/
theorem lemma_4_9_powers (a b va s : ℝ≥0) {n : ℕ} (hn : 1 ≤ n)
    {t : ℝ≥0} (htl : (n : ℝ≥0) * a < t) (htr : t < (n : ℝ≥0) * b) :
    minConvPow (segNN a b va s) n t
      = (((n : ℝ≥0) * va + s * (t - (n : ℝ≥0) * a) : ℝ≥0) : ℝ≥0∞) :=
  minConvPow_segNN_eq_affine a b va s hn htl htr

/-- **Definition 4.2** (§4.4, p.81): the set `F` of **containers** — a container is a function-lattice
interval `[f̲, f̄]` of `(min,plus)` curves (`lo ≤ hi`), the uncertainty between a lower and an upper
function. The library's `DeepWiki.Container` (membership `Container.Mem`, `singleton`, `univ = [⊥,⊤]`,
subset order; the Legendre-refined `[f̲,f̄]_𝓛` is `Container.MemL`). -/
abbrev def_4_2 := @DeepWiki.Container

/-- **Proposition 4.2** (§4.4, p.82): two `(min,plus)` functions have the same Legendre–Fenchel
transform iff their convex biconjugates `𝓛∘𝓛` (the convex hull `Cvx`) coincide:
`𝓛 f = 𝓛 g ↔ Cvx f = Cvx g`. Both directions; `𝓛` is injective on convex representatives
(`eq_of_sameLegendre_of_isConvex`) and `Cvx f` is the least element of `[f]_𝓛`
(`biconj_le_of_sameLegendre`). The library's `DeepWiki.Container.sameLegendre_iff_biconj_eq`. -/
theorem prop_4_2 (f g : ℝ≥0 → EReal) :
    legendre f = legendre g ↔ (legendre ∘ legendre) f = (legendre ∘ legendre) g :=
  DeepWiki.Container.sameLegendre_iff_biconj_eq f g

/-- **Proposition 4.3** (§4.4, p.83), the congruence (scaffolding). Same-Legendre-transform is an
equivalence relation `SameLegendre` (the dioid `F↑/L` is its quotient); the quotient `(⊓, ∗, ⋆)`
operations [4.7]–[4.9] are the remaining part. The library's `DeepWiki.Container.equivalence_sameLegendre` /
`DeepWiki.Container.legendreSetoid`. -/
theorem prop_4_3_setoid : Equivalence DeepWiki.Container.SameLegendre :=
  DeepWiki.Container.equivalence_sameLegendre

/-! **Remark** (§4.3.3, p.80): On the discrete domain ℕ, (F_ℕ, ∧, ∗_ℕ) is a dioid; the library's function complete-dioid (FPlus over the ℝ≥0 domain) carries the same (min,conv) dioid algebra. Library: FPlus, isSubCompleteDioid_FPlus. -/

end DeepWiki.Dnc
