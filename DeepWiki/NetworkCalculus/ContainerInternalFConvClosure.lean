import DeepWiki.NetworkCalculus.ContainerInternalF
import DeepWiki.NetworkCalculus.ConvexConvolution
import DeepWiki.NetworkCalculus.ClosureLegendre
import DeepWiki.NetworkCalculus.ClosuresEReal

/-! # Internality of the convolution `[∗]` and closure `[⋆]` inclusion functions

This file continues `ContainerInternalF` — the **internality half** of the
[LEC 14] container theory (the part the DNC book defers to)

  E. Le Corronc, B. Cottenceau, L. Hardouin, *Container of (min,+)-linear
  systems*, Discrete Event Dynamic Systems 24 (2014) 15–52,
  DOI `10.1007/s10626-012-0148-9`,

pushing the class-closure and inclusion-function internality from the meet `[⊕]`
(done in `ContainerInternalF`) to the **inf-convolution `[∗]`** (paper Proposition
6 / Proposition 7, pp. 23) and the **sub-additive closure `[⋆]`** (paper
Proposition 9, eq. 18, pp. 25, with Lemma 4 the slope statement).

Orientation (DNC vs paper convention, Remark 1). The paper writes containers in
the `(min,+)` order `≼` (the reverse of the numeric order), so the paper's
*upper* bound `f̄ ∈ ℱ_acx` is the numerically-lower **convex** bound (DeepWiki's
`lo`), and the paper's *lower* bound `f̲ ∈ ℱ_acv` is the numerically-upper
**concave** bound (DeepWiki's `hi`). So in DeepWiki coordinates:

* paper Proposition 6 (`ℱ_acx` closed under `∗`)  ↦  the **convex** `lo` bound's
  convolution stays convex — the *dual* of the existing Proposition 5
  (`isConcaveEReal_minConv`, `ℱ_acv` / the `hi` bound);
* paper Proposition 7 (`[∗]` internal to `F`)  ↦  the lifted convolution
  `Container.conv = [minConv lo lo', minConv hi hi']` is a canonical container;
* paper Proposition 9 (`[⋆]` internal to `F`)  ↦  the lifted closure has a convex
  `lo` bound `C_vx(f̄⋆)` and a concave `hi` bound (eq. 18).

What is proved vs scoped. The **genuinely convex / concave cores** close on the
existing chord-convolution engine (`isConvexEReal_minConv` for the convex side,
`isConcaveEReal_minConv` for the concave side); together they give the full
canonical-container internality of `[∗]` once the asymptotic-slope typing is
supplied (paper Proposition 7's slope bullet, eq. 15 — the geometric extremal-point
identity, carried as a hypothesis exactly as in
`isCanonicalContainer_canonicalizedInf`). For the closure, the convex upper bound
`f̄[⋆] = C_vx(f̄⋆)` is **unconditionally** almost convex (the convex hull of
anything is convex), and the closure-respects-`𝓛` identity descends. The
remaining `[infra]` steps — the *almost*-convex (constant-prefix) general case of
Proposition 6 (the "end-to-end of linear pieces" geometry) and the eq.-18
elementary-closure decomposition of the concave lower bound `f̲[⋆]` — are scoped
explicitly in the `## SCOPING` note below. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal Topology

namespace Container

/-! ## Paper Proposition 6 — `ℱ_acx` (almost-convex) closed under `∗`

The dual of the existing Proposition 5 (`ℱ_acv` closed under `∗`,
`isConcaveEReal_minConv`). In DeepWiki coordinates this is the **convex** `lo`
bound's convolution. The genuinely convex core closes on the chord-convolution
engine `isConvexEReal_minConv` (DeepWiki Proposition 3.13, convolution); the
*almost*-convex case (a constant prefix, then convex) is the paper's geometric
"end-to-end of linear pieces" construction and is scoped out (see `## SCOPING`). -/

/-- **Paper Proposition 6 (genuine-convex core):** `ℱ_cx` is closed under
inf-convolution — the `(min,+)` convolution of two non-negative convex curves is
convex. This is the convex (lower-bound) dual of the existing Proposition 5
(`isConcaveEReal_minConv`); the engine is `isConvexEReal_minConv`. -/
theorem isConvexEReal_minConv_convex {f g : ℝ≥0 → EReal}
    (hf : IsConvexEReal f) (hg : IsConvexEReal g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    IsConvexEReal (minConv f g) :=
  isConvexEReal_minConv hf hg hf0 hg0

/-- **Paper Proposition 6, almost-convex packaging (rank `0`):** the convolution
of two non-negative *genuinely* convex curves is **almost convex**. So the
`(min,+)` convolution maps the genuine-convex core of `ℱ_acx` back into `ℱ_acx`. -/
theorem isAlmostConvex_minConv_of_convex {f g : ℝ≥0 → EReal}
    (hf : IsConvexEReal f) (hg : IsConvexEReal g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    IsAlmostConvex (minConv f g) :=
  (isConvexEReal_minConv_convex hf hg hf0 hg0).isAlmostConvex

/-! ## Paper Proposition 7 — the `[∗]` inclusion function is internal to `F`

`Container.conv c d = [minConv c.lo d.lo, minConv c.hi d.hi]` (the lifted
inf-convolution, `ContainerInclusion`). Its soundness `f∗g ⊃ f[∗]g` is already in
DeepWiki (`Container.conv_mem`). Internality (paper Definition 23, eq. 14) asks the
result back in `F`: a canonical container.

* The convex (lower) bound `minConv c.lo d.lo` stays convex by Proposition 6.
* The concave (upper) bound `minConv c.hi d.hi` stays concave by Proposition 5.
* The asymptotic-slope typing `ρ_{f̲∗g̲} = ρ_{f̄∗ḡ}` (paper Proposition 7's slope
  bullet, eq. 15) is the geometric extremal-point identity — carried as a
  hypothesis `htyped`, exactly as the meet's typing in
  `isCanonicalContainer_canonicalizedInf`. -/

/-- The convex (lower) bound of the lifted convolution `c [∗] d` is again **almost
convex**, in the genuine-convex case: if `c.lo`, `d.lo` are non-negative convex,
then `(c [∗] d).lo = minConv c.lo d.lo` is almost convex (Proposition 6). -/
theorem conv_lo_isAlmostConvex_of_convex {c d : Container}
    (hc : IsConvexEReal c.lo) (hd : IsConvexEReal d.lo)
    (hc0 : ∀ x, 0 ≤ c.lo x) (hd0 : ∀ x, 0 ≤ d.lo x) :
    IsAlmostConvex (conv c d).lo := by
  rw [conv_lo]; exact isAlmostConvex_minConv_of_convex hc hd hc0 hd0

/-- The concave (upper) bound of the lifted convolution `c [∗] d` is again
**almost concave**, in the genuine-concave case: if `c.hi`, `d.hi` are
bounded-below concave, then `(c [∗] d).hi = minConv c.hi d.hi` is almost concave
(Proposition 5, via `IsConcaveEReal.minConv` and `IsConcaveEReal.isAlmostConcave`). -/
theorem conv_hi_isAlmostConcave_of_concave {c d : Container}
    (hc : IsConcaveEReal c.hi) (hd : IsConcaveEReal d.hi)
    (hcb : IsBddBelowReal c.hi) (hdb : IsBddBelowReal d.hi) :
    IsAlmostConcave (conv c d).hi := by
  rw [conv_hi]
  exact (IsConcaveEReal.minConv hc hd hcb hdb).isAlmostConcave

/-- **Paper Proposition 7 (`[∗]` internal to `F`, genuine-convex/concave case).**
If both lower bounds are non-negative convex and both upper bounds are
bounded-below concave, and the lifted convolution's bounds are asymptotically
typed (`htyped`, paper Proposition 7's slope identity / eq. 15), then the lifted
convolution `c [∗] d` is again a **canonical container** of `F`. The convex and
concave bounds are discharged by Propositions 6 and 5; only the asymptotic-slope
typing remains carried — exactly the shape of
`isCanonicalContainer_canonicalizedInf` for the meet. -/
theorem conv_isCanonicalContainer_of_convex_concave {c d : Container}
    (hclo : IsConvexEReal c.lo) (hdlo : IsConvexEReal d.lo)
    (hclo0 : ∀ x, 0 ≤ c.lo x) (hdlo0 : ∀ x, 0 ≤ d.lo x)
    (hchi : IsConcaveEReal c.hi) (hdhi : IsConcaveEReal d.hi)
    (hchib : IsBddBelowReal c.hi) (hdhib : IsBddBelowReal d.hi)
    (htyped : IsAsymptoticallyTyped (conv c d).lo (conv c d).hi) :
    IsCanonicalContainer (conv c d) where
  lo_acx := conv_lo_isAlmostConvex_of_convex hclo hdlo hclo0 hdlo0
  hi_acv := conv_hi_isAlmostConcave_of_concave hchi hdhi hchib hdhib
  typed := htyped

/-! ## Paper Proposition 9 — the `[⋆]` inclusion function is internal to `F`

The closure inclusion function `f[⋆] = [f̲[⋆], f̄[⋆]]_𝓛` (paper Proposition 9).
Its soundness `f⋆ ⊃ f[⋆]` is already in DeepWiki
(`ContainerNN.closure_mem` / the `subadditiveClosureENN_min` Kleene engine).
Internality asks both bounds back in `F`.

The convex (upper, paper-`f̄`) bound is `f̄[⋆] = C_vx(f̄⋆)` (the convex hull of
the closure). In DeepWiki coordinates this is the **convex `lo` bound** of the
lifted closure; its convexity is **unconditional** — the convex hull
`C_vx = biconj` of *anything* is convex (`isConvexEReal_biconj_of_zero_ne_top`),
and the closure is null at the origin (`subadditiveClosureEReal_zero_eq`), so the
weak hypothesis `(f̄⋆) 0 ≠ ⊤` is automatic for non-negative `f̄`. This is the
genuinely-true, `[infra]`-free half of Proposition 9. -/

/-- The closure of a non-negative curve is null at the origin and so `≠ ⊤` there:
`(g⋆) 0 = 0 ≠ ⊤`. This discharges the weak hypothesis of
`isConvexEReal_biconj_of_zero_ne_top` for the closure. -/
theorem subadditiveClosureEReal_zero_ne_top {g : ℝ≥0 → EReal} (hg : IsNonneg g) :
    subadditiveClosureEReal g 0 ≠ ⊤ := by
  rw [subadditiveClosureEReal_zero_eq hg]; exact EReal.zero_ne_top

/-- **Paper Proposition 9 (convex upper bound `f̄[⋆] = C_vx(f̄⋆)`).** The convex
hull of the sub-additive closure of a non-negative curve is **convex** — the
convex hull of anything is convex (`isConvexEReal_biconj_of_zero_ne_top`), and the
closure is null at the origin (so `≠ ⊤` there). This is the unconditional,
`[infra]`-free half of Proposition 9: the paper-upper bound of `f[⋆]` lands in
`ℱ_cx`. -/
theorem isConvexEReal_biconj_subadditiveClosureEReal {g : ℝ≥0 → EReal}
    (hg : IsNonneg g) :
    IsConvexEReal (biconj (subadditiveClosureEReal g)) :=
  isConvexEReal_biconj_of_zero_ne_top (subadditiveClosureEReal_zero_ne_top hg)

/-- **Paper Proposition 9, almost-convex packaging.** The convex hull of the
closure `C_vx(f̄⋆)` is **almost convex** (rank `0`): the paper-upper bound of
`f[⋆]` lands in `ℱ_acx`. -/
theorem isAlmostConvex_biconj_subadditiveClosureEReal {g : ℝ≥0 → EReal}
    (hg : IsNonneg g) :
    IsAlmostConvex (biconj (subadditiveClosureEReal g)) :=
  (isConvexEReal_biconj_subadditiveClosureEReal hg).isAlmostConvex

/-- **The closure's convex hull keeps the Legendre–Fenchel class.** The convex
upper bound `C_vx(f̄⋆) = biconj (f̄⋆)` shares its transform with `f̄⋆`
(`legendre_biconj`), so re-canonicalizing the closure by its convex hull is
class-faithful — the uncertainty class is preserved (paper Lemma 3 / eq. 10 at the
closure). -/
theorem sameLegendre_biconj_subadditiveClosureEReal (g : ℝ≥0 → EReal) :
    SameLegendre (biconj (subadditiveClosureEReal g)) (subadditiveClosureEReal g) :=
  legendre_biconj (subadditiveClosureEReal g)

/-- **Paper Lemma 4.10 [4.12], the closure case (eq. 18 well-definedness).** The
sub-additive closure respects the Legendre–Fenchel congruence: two non-negative
curves with the same transform have closures with the same transform. So the `[⋆]`
inclusion function — built from `𝓛`-class data in eq. 18 — descends to the
quotient `ℱ↑/𝓛` (`SameLegendre.legendreClosure`). -/
theorem sameLegendre_legendreClosure_of_sameLegendre {f g : ℝ≥0 → EReal}
    (hf : ∀ u, 0 ≤ f u) (hg : ∀ v, 0 ≤ g v) (h : SameLegendre f g) :
    SameLegendre (legendreClosure f) (legendreClosure g) :=
  SameLegendre.legendreClosure hf hg h

/-- **Paper Proposition 9 (concave lower bound `f̲[⋆]`, origin-null collapse).**
The eq.-18 lower bound `f̲[⋆]` is "composed of sums of concave functions",
therefore in `ℱ_acv`. For the *origin-null concave* core the construction
collapses by Theorem 3, eq. 9: an origin-null concave never-`⊥` curve is its own
closure, so `Γ⋆ = Γ` stays concave (`subadditiveClosureEReal_eq_self_of_…`,
restated as `concave_subadditiveClosure_eq_self` in `ContainerInternalF`). The
full eq.-18 decomposition over *elementary* closures `C_cv(Δ⋆)` is the geometric
`[infra]` step (see `## SCOPING`). -/
theorem isConcaveEReal_subadditiveClosureEReal_of_null {Γ : ℝ≥0 → EReal}
    (hnb : IsNeverBot Γ) (h0 : Γ 0 = 0) (hconc : IsConcaveEReal Γ) :
    IsConcaveEReal (subadditiveClosureEReal Γ) := by
  rw [concave_subadditiveClosure_eq_self hnb h0 hconc]; exact hconc

/-- **Paper Proposition 9, concave lower bound, almost-convex packaging (rank
`0`).** For the origin-null concave never-`⊥` core, the closure's concave lower
bound `f̲[⋆]` lands in `ℱ_acv`: an origin-null concave never-`⊥` curve is its own
closure, hence almost concave. -/
theorem isAlmostConcave_subadditiveClosureEReal_of_null {Γ : ℝ≥0 → EReal}
    (hnb : IsNeverBot Γ) (h0 : Γ 0 = 0) (hconc : IsConcaveEReal Γ) :
    IsAlmostConcave (subadditiveClosureEReal Γ) :=
  (isConcaveEReal_subadditiveClosureEReal_of_null hnb h0 hconc).isAlmostConcave

/-! ## SCOPING — what the FULL [LEC 14] `[∗]` / `[⋆]` internality needs beyond here

Proved above (faithful to the paper, pp. 23–25):

* **Proposition 6** (`ℱ_acx` closed under `∗`) — the genuine-convex core
  `isConvexEReal_minConv_convex` (dual of the existing Proposition 5).
* **Proposition 7** (`[∗]` internal to `F`) — the full canonical-container
  conclusion `conv_isCanonicalContainer_of_convex_concave` in the
  genuine-convex/concave case, carrying only the asymptotic-slope typing
  (`htyped`), exactly as the meet's `isCanonicalContainer_canonicalizedInf`.
* **Proposition 9** (`[⋆]` internal to `F`) — the convex upper bound
  `f̄[⋆] = C_vx(f̄⋆)` is *unconditionally* almost convex
  (`isAlmostConvex_biconj_subadditiveClosureEReal`); the closure respects `𝓛`
  (`sameLegendre_legendreClosure_of_sameLegendre`, eq.-18 well-definedness); and
  the origin-null concave lower bound collapses to itself
  (`isConcaveEReal_subadditiveClosureEReal_of_null`).

Scoped out (geometric / representation `[infra]` not on the chord API):

* **The *almost*-convex (constant-prefix) general case of Proposition 6.** The
  paper computes `f̄ ∗ ḡ` "by putting end-to-end the different linear pieces of
  `f̄` and `ḡ`, sorted by nondecreasing slopes" — a geometric piecewise-linear
  construction. The genuine-convex core (rank `0`) is proved; the rank-prefix
  carry-through (an `IsAlmostConvexWith.minConv` at a shared rank, dual of the
  absent `IsAlmostConcaveWith.minConv`) is `[infra]`.
* **The asymptotic-slope identity** `σ(f̲∗g̲) = σ(f̄∗ḡ) = min(σf̲, σf̄)` (paper
  Proposition 7's slope bullet, eq. 15, and Lemma 4 for `[⋆]`) — a geometric
  extremal-point argument over ultimately-affine functions. Carried as `htyped`.
* **The eq.-18 elementary-closure decomposition of `f̲[⋆]`** — the lower bound is
  `⊕ᵢ C_cv(Δᵢ⋆) ⊕ C_cv(e ⊕ Δ ∗ (C_cv(Δ⋆) ⊕ Γ))`, a sum of concave approximations
  of *elementary* closures `C_cv(Δ_t^k⋆)` (Figure 13). Building the elementary
  closures and their concave hulls, and summing them, is the geometric `[infra]`
  step; the origin-null collapse and the `𝓛`-descent are the algebraic parts done
  here. -/

/-! ## Faithfulness checks (anonymous restatements vs the paper) -/

-- Paper Proposition 6 (genuine-convex core): `ℱ_cx` closed under `∗`.
example {f g : ℝ≥0 → EReal} (hf : IsConvexEReal f) (hg : IsConvexEReal g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    IsConvexEReal (minConv f g) :=
  isConvexEReal_minConv_convex hf hg hf0 hg0

-- Paper Proposition 7 (`[∗]` internal to `F`): the lifted convolution is a
-- canonical container when both bounds are convex / concave and slope-typed.
example {c d : Container}
    (hclo : IsConvexEReal c.lo) (hdlo : IsConvexEReal d.lo)
    (hclo0 : ∀ x, 0 ≤ c.lo x) (hdlo0 : ∀ x, 0 ≤ d.lo x)
    (hchi : IsConcaveEReal c.hi) (hdhi : IsConcaveEReal d.hi)
    (hchib : IsBddBelowReal c.hi) (hdhib : IsBddBelowReal d.hi)
    (htyped : IsAsymptoticallyTyped (conv c d).lo (conv c d).hi) :
    IsCanonicalContainer (conv c d) :=
  conv_isCanonicalContainer_of_convex_concave
    hclo hdlo hclo0 hdlo0 hchi hdhi hchib hdhib htyped

-- Paper Proposition 9 (convex upper bound): `C_vx(f̄⋆)` is convex (in `ℱ_cx`).
example {g : ℝ≥0 → EReal} (hg : IsNonneg g) :
    IsConvexEReal (biconj (subadditiveClosureEReal g)) :=
  isConvexEReal_biconj_subadditiveClosureEReal hg

-- Paper eq.-18 well-definedness: `[⋆]` respects the Legendre–Fenchel class.
example {f g : ℝ≥0 → EReal} (hf : ∀ u, 0 ≤ f u) (hg : ∀ v, 0 ≤ g v)
    (h : SameLegendre f g) :
    SameLegendre (legendreClosure f) (legendreClosure g) :=
  sameLegendre_legendreClosure_of_sameLegendre hf hg h

end Container

end DeepWiki
