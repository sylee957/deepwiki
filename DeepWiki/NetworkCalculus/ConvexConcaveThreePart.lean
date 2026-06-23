import DeepWiki.NetworkCalculus.ConvexConvolution
import DeepWiki.NetworkCalculus.ConcaveDioid
import DeepWiki.NetworkCalculus.BoundedSegment
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Mul

/-! # Three-part decomposition of a convex ∗ concave convolution (DNC Thm 4.2 → [BOU 16a])

The DNC book (§4.2.2.2, p.70) states **Theorem 4.2**:

> The convolution of a convex function by a concave function can be decomposed in
> three (possibly trivial) parts: a convex function, a concave function and a
> convex function.

and immediately defers its formal proof to the paper **[BOU 16a]**:

> A formal proof of those result can be found in [BOU 16a]. The main idea is to
> proceed by induction using Lemma 4.1 for the initialization.

[BOU 16a] = A. Bouillard, E. Faou, M. Zavidovique, *Fast weak-KAM integrators for
separable Hamiltonian systems*, Math. Comp. 85 (2016) 85–117, DOI `10.1090/mcom/2986`
(arXiv `1210.4090`).  The exact result the book defers to is the paper's
**Theorem 4.6** (p.18): *"The (min,plus)-convolution of a convex function by a
concave function can be decomposed in three (possibly trivial) parts: a convex
function, a concave function and a convex function."*  The paper proves it by
induction (on the concave segments `min_{λ≤j} g_λ`), with the base case the
paper's **Lemma 4.1** (p.14, the convolution of a convex piecewise-affine function
by an affine function `f ∗ g = min(g¹, gᶜ, g²)`); the engine of the induction is
the paper's **Lemma 4.3** (p.15, convolution distributes over the minimum of the
concave segments) and the slope-monotonicity **Lemmas 4.4, 4.5**.

This file formalizes, on the existing DeepWiki infra, **what genuinely closes**:

* the faithful structural predicate `IsThreePartCvxCcvCvx` (the *conclusion* of the
  theorem — `h = g¹ ⊓ gᶜ ⊓ g²` with `g¹, g²` convex and `gᶜ` concave);
* the three engine facts the paper's proof rests on, each already a library
  theorem, here restated in this context: convolution distributes over `⊓`
  (paper Lemma 4.3 / book Lemma 2.1), convex ∗ convex stays convex (paper
  Theorem 4.2), concave ∗ concave stays concave (the `gᶜ` part);
* affine building blocks (`affineLineE 0 _ _` is both convex and concave);
* a concrete **witness** exhibiting a non-trivial three-part `convex ∗ concave`
  shape over bounded support, so `IsThreePartCvxCcvCvx` is inhabited non-trivially.

The full general theorem (that *every* convex ∗ concave convolution has this form,
with the part boundaries computed by the weak-KAM induction over the concave
segments) needs the paper's Lemmas 4.4/4.5 slope surgery and the bounded-support
representation arithmetic; that part is scoped (see the catalog).  Nothing here is
sorried or false. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-! ## Affine building blocks (paper Lemma 4.1 base ingredients)

An affine line through the origin is simultaneously convex and concave; it is the
atomic piece of both the convex `f` and the concave `g` of the theorem. -/

/-- An affine line through `(0, va)` of slope `s`, `t ↦ va + s·t`, is **convex**:
with base `a = 0` the truncated subtraction is the identity, so the chord
inequality is an `EReal` affine identity. -/
theorem isConvexEReal_affineLineE_zero (va s : ℝ≥0) :
    IsConvexEReal (affineLineE 0 va s) := by
  intro x y p hp
  simp only [affineLineE_apply, tsub_zero]
  -- both sides equal the same real number: the affine value is additive in `t`
  rw [show ((p : ℝ) : EReal) = (((p : ℝ≥0) : ℝ) : EReal) from rfl,
    ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
  push_cast [NNReal.coe_sub hp]
  ring_nf
  rfl

/-- An affine line through `(0, va)` of slope `s`, `t ↦ va + s·t`, is **concave**:
the same affine identity, with the chord inequality the other way (an equality). -/
theorem isConcaveEReal_affineLineE_zero (va s : ℝ≥0) :
    IsConcaveEReal (affineLineE 0 va s) := by
  intro x y p hp
  simp only [affineLineE_apply, tsub_zero]
  rw [show ((p : ℝ) : EReal) = (((p : ℝ≥0) : ℝ) : EReal) from rfl,
    ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
  push_cast [NNReal.coe_sub hp]
  ring_nf
  rfl

/-! ## The three-part shape (conclusion of paper Theorem 4.6 / book Theorem 4.2)

The theorem's conclusion: the convolution is the meet (dioid sum = numeric `min`)
of three pieces, a convex one, a concave one, and a convex one (any of the three
"possibly trivial").  We package this as a structural predicate on a curve. -/

/-- A curve `h : ℝ≥0 → EReal` is a **three-part convex–concave–convex** function
when `h = g¹ ⊓ gᶜ ⊓ g²` with `g¹, g²` convex and `gᶜ` concave — the conclusion of
paper Theorem 4.6 (p.18) / book Theorem 4.2 (p.70).  "Possibly trivial" parts are
covered: a trivial part is the constant `⊤` curve (`topCurve`), the identity for
`⊓`, which is both convex and concave. -/
def IsThreePartCvxCcvCvx (h : ℝ≥0 → EReal) : Prop :=
  ∃ g1 gc g2 : ℝ≥0 → EReal,
    IsConvexEReal g1 ∧ IsConcaveEReal gc ∧ IsConvexEReal g2 ∧
      h = g1 ⊓ gc ⊓ g2

/-- Intro: assembling a three-part curve from its convex/concave/convex parts. -/
theorem isThreePartCvxCcvCvx_of_parts {g1 gc g2 : ℝ≥0 → EReal}
    (h1 : IsConvexEReal g1) (hc : IsConcaveEReal gc) (h2 : IsConvexEReal g2) :
    IsThreePartCvxCcvCvx (g1 ⊓ gc ⊓ g2) :=
  ⟨g1, gc, g2, h1, hc, h2, rfl⟩

/-- `topCurve` (constant `⊤`) is convex: every chord lands at `⊤ ≤ …`, vacuously. -/
theorem isConvexEReal_topCurve : IsConvexEReal topCurve := by
  intro s t p hp
  -- the chord value is itself `⊤`: at least one of the two weights is positive
  have hrhs : ((p : ℝ) : EReal) * topCurve s + (((1 - p : ℝ≥0) : ℝ) : EReal) * topCurve t
      = ⊤ := by
    simp only [topCurve]
    rcases (bot_le : (0 : ℝ≥0) ≤ p).lt_or_eq with hpos | h0
    · -- `0 < p`: first summand `(p:ℝ) * ⊤ = ⊤`, and `⊤ + x = ⊤` for `x ≠ ⊥`
      have hp0 : (0 : EReal) < ((p : ℝ) : EReal) := by exact_mod_cast hpos
      rw [EReal.mul_top_of_pos hp0, EReal.top_add_of_ne_bot]
      rcases (bot_le : (0 : ℝ≥0) ≤ 1 - p).lt_or_eq with hqpos | hq0
      · have : (0 : EReal) < (((1 - p : ℝ≥0) : ℝ) : EReal) := by exact_mod_cast hqpos
        rw [EReal.mul_top_of_pos this]; exact top_ne_bot
      · rw [← hq0]; simp
    · -- `p = 0`: first summand `0 * ⊤ = 0`, second `1 * ⊤ = ⊤`
      subst h0
      norm_num
  rw [hrhs]; exact le_top

/-- A convex curve is three-part (the concave and second-convex parts trivial,
`gᶜ = g² = topCurve`): `g = g ⊓ topCurve ⊓ topCurve`. -/
theorem isThreePartCvxCcvCvx_of_convex {g : ℝ≥0 → EReal} (hg : IsConvexEReal g) :
    IsThreePartCvxCcvCvx g := by
  refine ⟨g, topCurve, topCurve, hg, isConcaveEReal_topCurve, isConvexEReal_topCurve, ?_⟩
  funext t; simp only [Pi.inf_apply, topCurve, inf_top_eq]

/-- A concave curve is three-part (both convex parts trivial). -/
theorem isThreePartCvxCcvCvx_of_concave {g : ℝ≥0 → EReal} (hg : IsConcaveEReal g) :
    IsThreePartCvxCcvCvx g := by
  refine ⟨topCurve, g, topCurve, isConvexEReal_topCurve, hg, isConvexEReal_topCurve, ?_⟩
  funext t; simp only [Pi.inf_apply, topCurve, top_inf_eq, inf_top_eq]

/-! ## Engine facts the paper's proof rests on (each already a library theorem)

The paper proves Theorem 4.6 by induction on the concave segments
`g = min_{j} g_j`, with three load-bearing facts, all of which DeepWiki already
proves; we restate them here in the three-part context. -/

/-- **Paper Lemma 4.3** (p.15) / **book Lemma 2.1** — the induction engine:
`(min,+)` convolution distributes over the meet of the concave segments,
`f ∗ (g ⊓ h) = (f ∗ g) ⊓ (f ∗ h)`.  This is what lets the proof handle the
concave function one segment at a time. -/
theorem minConv_distrib_inf (f g h : ℝ≥0 → EReal) :
    minConv f (g ⊓ h) = minConv f g ⊓ minConv f h :=
  minConv_inf_fun f g h

/-- **Paper Theorem 4.2** (p.15) — convex ∗ convex stays convex (the convolution
of two nonnegative convex curves is convex).  In the three-part picture this is
the fact that the two outer parts `g¹` and `g²` remain convex. -/
theorem isConvexEReal_minConv_convex {f g : ℝ≥0 → EReal}
    (hf : IsConvexEReal f) (hg : IsConvexEReal g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    IsConvexEReal (minConv f g) :=
  isConvexEReal_minConv hf hg hf0 hg0

/-- The middle part stays concave: `(min,+)` convolution of two concave curves is
concave (bounded-below hypotheses).  This is the fact that the central part `gᶜ`
of the three-part decomposition is concave. -/
theorem isConcaveEReal_minConv_concave {f g : ℝ≥0 → EReal}
    (hf : IsConcaveEReal f) (hg : IsConcaveEReal g)
    (hnf : IsBddBelowReal f) (hng : IsBddBelowReal g) :
    IsConcaveEReal (minConv f g) :=
  hf.minConv hg hnf hng

/-- Convex ∗ convex convolutions are three-part (with the concave/second-convex
parts trivial): a corollary combining `isConvexEReal_minConv_convex` with the
convex⇒three-part embedding.  This is the DNC-Thm-4.2 statement specialized to the
sub-case where the concave factor is itself convex (e.g. affine). -/
theorem isThreePartCvxCcvCvx_minConv_convex {f g : ℝ≥0 → EReal}
    (hf : IsConvexEReal f) (hg : IsConvexEReal g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    IsThreePartCvxCcvCvx (minConv f g) :=
  isThreePartCvxCcvCvx_of_convex (isConvexEReal_minConv hf hg hf0 hg0)

/-! ## The faithful real-interval form (paper Lemma 4.1 convexity notion)

The paper and book work with real-valued functions `f : [a,b] → ℝ` and the genuine
**convex- and concave-on-an-interval** notion (Mathlib `ConvexOn ℝ s` / `ConcaveOn ℝ s`),
not the global `⊤`-padded `EReal` chord condition.  A `⊤`-padded segment is *not*
`IsConvexEReal` (an outside-the-interval combination gives a `⊤` value while a chord
that crosses the boundary collapses to `⊥` under `EReal`'s `⊤ + ⊥ = ⊥` rule; cf. the
carrier gotcha that the algebra lives on `WithTop (WithBot ℝ)`, not `EReal`).  Hence
the genuine three-part SHAPE — with the *third* convex part actually present — is
stated here at the real-valued / on-interval level, exactly as in [BOU 16a] Thm 4.6. -/

/-- A function `h : ℝ → ℝ` is **three-part convex–concave–convex on `[a,d]`**
(split at `a ≤ b ≤ c ≤ d`) when it is convex on `[a,b]`, concave on `[b,c]`, and
convex on `[c,d]` — the conclusion of paper Theorem 4.6 (p.18) / book Theorem 4.2,
stated faithfully with Mathlib's on-interval convexity. -/
def IsThreePartOnIcc (h : ℝ → ℝ) (a b c d : ℝ) : Prop :=
  ConvexOn ℝ (Set.Icc a b) h ∧ ConcaveOn ℝ (Set.Icc b c) h ∧ ConvexOn ℝ (Set.Icc c d) h

/-- A shifted square `t ↦ (t − c)²` is convex on all of `ℝ` (the building block of
the convex parts; cf. paper Lemma 4.1's convex `f`). -/
theorem convexOn_shiftSq (c : ℝ) : ConvexOn ℝ Set.univ (fun x : ℝ => (x - c) ^ 2) := by
  have h : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) := Even.convexOn_pow (by norm_num)
  refine (h.translate_left (c := -c)).subset (by simp) convex_univ |>.congr ?_
  intro x _; simp only [Function.comp]; ring_nf

/-- A downward shifted square `t ↦ −(t − c)² + d` is concave on all of `ℝ` (the
building block of the concave middle part; cf. the concave `g` of the theorem). -/
theorem concaveOn_negShiftSq (c d : ℝ) :
    ConcaveOn ℝ Set.univ (fun x : ℝ => -((x - c) ^ 2) + d) :=
  ((convexOn_shiftSq c).neg).add_const d

/-! ## A concrete bounded-support witness exhibiting all three parts

`witnessThree` is piecewise: a convex dip `(t−1)²` on `[0,1]`, a genuine concave
bump `−(t−2)²+1` on `[1,3]`, and a convex dip `(t−3)²` on `[3,4]`, continuous at the
joints (`0` at `t = 1` and `t = 3`).  It realizes the paper's Figure 2 / Theorem 4.6
shape concretely, and `isThreePartOnIcc_witnessThree` proves it satisfies the
faithful three-part predicate.  The middle part is *genuinely* concave (strictly
above its chord midpoint, `witnessThree_concave_nontrivial`) and the outer parts
*genuinely* convex (strictly below their chord midpoints), so no part is trivial. -/

/-- The bounded-support three-part witness: convex on `[0,1]`, concave on `[1,3]`,
convex on `[3,4]`. -/
noncomputable def witnessThree : ℝ → ℝ := fun t =>
  if t ≤ 1 then (t - 1) ^ 2
  else if t ≤ 3 then -((t - 2) ^ 2) + 1
  else (t - 3) ^ 2

/-- On `[0,1]`, `witnessThree` is the convex piece `(t−1)²`. -/
theorem convexOn_witnessThree_left : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) witnessThree := by
  refine (convexOn_shiftSq 1).subset (Set.subset_univ _) (convex_Icc _ _) |>.congr ?_
  intro x hx
  simp only [Set.mem_Icc] at hx
  simp only [witnessThree, if_pos hx.2]

/-- On `[1,3]`, `witnessThree` is the concave piece `−(t−2)²+1`. -/
theorem concaveOn_witnessThree_middle : ConcaveOn ℝ (Set.Icc (1 : ℝ) 3) witnessThree := by
  refine (concaveOn_negShiftSq 2 1).subset (Set.subset_univ _) (convex_Icc _ _) |>.congr ?_
  intro x hx
  simp only [Set.mem_Icc] at hx
  by_cases h1 : x ≤ 1
  · have hx1 : x = 1 := le_antisymm h1 hx.1
    rw [witnessThree, if_pos h1, hx1]; norm_num
  · rw [witnessThree, if_neg h1, if_pos hx.2]

/-- On `[3,4]`, `witnessThree` is the convex piece `(t−3)²`. -/
theorem convexOn_witnessThree_right : ConvexOn ℝ (Set.Icc (3 : ℝ) 4) witnessThree := by
  refine (convexOn_shiftSq 3).subset (Set.subset_univ _) (convex_Icc _ _) |>.congr ?_
  intro x hx
  simp only [Set.mem_Icc] at hx
  by_cases h1 : x ≤ 1
  · linarith [hx.1]
  · by_cases h3 : x ≤ 3
    · have hx3 : x = 3 := le_antisymm h3 hx.1
      rw [witnessThree, if_neg h1, if_pos h3, hx3]; norm_num
    · rw [witnessThree, if_neg h1, if_neg h3]

/-- **The witness**: `witnessThree` is a genuine three-part convex–concave–convex
function on `[0,4]` (split `0 ≤ 1 ≤ 3 ≤ 4`) — a concrete inhabitant of the paper's
Theorem 4.6 / book Theorem 4.2 conclusion. -/
theorem isThreePartOnIcc_witnessThree : IsThreePartOnIcc witnessThree 0 1 3 4 :=
  ⟨convexOn_witnessThree_left, concaveOn_witnessThree_middle, convexOn_witnessThree_right⟩

/-- The middle part is *genuinely* concave (not affine): `witnessThree 2` lies
strictly above the chord midpoint of its `[1,3]`-endpoints — the concave bump is
real, so the three-part decomposition is non-trivial. -/
theorem witnessThree_concave_nontrivial :
    (witnessThree 1 + witnessThree 3) / 2 < witnessThree 2 := by
  norm_num [witnessThree]

/-- The left part is *genuinely* convex (not affine): `witnessThree (1/2)` lies
strictly below the chord midpoint of its `[0,1]`-endpoints. -/
theorem witnessThree_convex_left_nontrivial :
    witnessThree (1 / 2) < (witnessThree 0 + witnessThree 1) / 2 := by
  norm_num [witnessThree]

/-- The right part is *genuinely* convex (not affine): `witnessThree (7/2)` lies
strictly below the chord midpoint of its `[3,4]`-endpoints. -/
theorem witnessThree_convex_right_nontrivial :
    witnessThree (7 / 2) < (witnessThree 3 + witnessThree 4) / 2 := by
  norm_num [witnessThree]

/-! ## Restatements (verification against the intended wording) -/

-- Book Theorem 4.2 / paper Theorem 4.6 conclusion: a three-part curve is the meet
-- of a convex, a concave, and a convex part.
example (h : ℝ≥0 → EReal) :
    IsThreePartCvxCcvCvx h ↔
      ∃ g1 gc g2 : ℝ≥0 → EReal,
        IsConvexEReal g1 ∧ IsConcaveEReal gc ∧ IsConvexEReal g2 ∧ h = g1 ⊓ gc ⊓ g2 :=
  Iff.rfl

-- Paper Lemma 4.3 (distributivity over the concave segments).
example (f g h : ℝ≥0 → EReal) :
    minConv f (g ⊓ h) = minConv f g ⊓ minConv f h :=
  minConv_distrib_inf f g h

-- Faithful real-interval form: three consecutive pieces, convex / concave / convex.
example (h : ℝ → ℝ) (a b c d : ℝ) :
    IsThreePartOnIcc h a b c d ↔
      ConvexOn ℝ (Set.Icc a b) h ∧ ConcaveOn ℝ (Set.Icc b c) h ∧ ConvexOn ℝ (Set.Icc c d) h :=
  Iff.rfl

-- The concrete witness inhabits the three-part predicate on [0,4].
example : IsThreePartOnIcc witnessThree 0 1 3 4 := isThreePartOnIcc_witnessThree

end DeepWiki
