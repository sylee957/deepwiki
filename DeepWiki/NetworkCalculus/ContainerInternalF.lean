import DeepWiki.NetworkCalculus.AlmostConcave
import DeepWiki.NetworkCalculus.ConcaveProps
import DeepWiki.NetworkCalculus.ConcaveDioid
import DeepWiki.NetworkCalculus.ClosuresEReal
import DeepWiki.NetworkCalculus.ContainerCanonical
import DeepWiki.NetworkCalculus.ContainerInclusion

/-! # Internality of the container operations to the set `F`

This file formalizes the **internality half** of the [LEC 14] container theory —
the part the DNC book (Bouillard, Boyer, Le Corronc) defers to the paper

  E. Le Corronc, B. Cottenceau, L. Hardouin, *Container of (min,+)-linear
  systems*, Discrete Event Dynamic Systems 24 (2014) 15–52,
  DOI `10.1007/s10626-012-0148-9`.

The paper's **Definition 23** (inclusion functions of `{⊕, *, *}`) asks an
inclusion function `[⋄]` to satisfy *two* conditions (eq. 14):

* **soundness** `f[⋄]g ⊃ f⋄g` — already in DeepWiki
  (`Container.inf_mem`, `Container.conv_mem`, `ContainerNN.closure_mem`); and
* **internality** `f[⋄]g ∈ F` — the result is again a *canonical* container.

The internality rests on the paper's **Theorem 3** (Le Boudec–Thiran), the
algebraic engine: for `Γ₁, Γ₂ ∈ ℱ_acv` *null at the origin*,

  `Γ₁ * Γ₂ = Γ₁ ⊕ Γ₂`        (eq. 8)     and     `Γ₁ = Γ₁⋆`   (eq. 9),

i.e. the inf-convolution of origin-null concave functions collapses to their
meet, and such a function is its own sub-additive closure. These already live in
`ConcaveProps` (`minConv_eq_inf_of_null`, `subadditiveClosureEReal_eq_self_of_isConcaveEReal`);
here they are restated in the paper's Theorem-3 shape and used to prove the
**class-closure facts** (paper Propositions 5/6 for `ℱ_acv` / `ℱ_acx`) and the
**internality of the lifted meet** `[∧]`/`[⊕]` on the concave (upper) bound of a
canonical container.

Orientation (DNC vs paper convention). In DeepWiki a `Container` is read in the
*numeric* order: `lo ≤ hi` pointwise, with `lo` the **almost-convex** bound
(`C_vx`, the convex hull `biconj`) and `hi` the **almost-concave** bound
(`C_cv`). The paper writes containers in the `(min,+)` order `≼` (the reverse of
the numeric order, Remark 1), so the paper's *upper* bound `f̄ ∈ ℱ_acx` is the
numerically-lower convex bound (DeepWiki's `lo`), and the paper's *lower* bound
`f̲ ∈ ℱ_acv` is the numerically-upper concave bound (DeepWiki's `hi`). The two
presentations agree.

What is proved vs scoped. The meet `Container.inf` lifts `⊓` to both bounds.
Because `⊕ = min` in `(min,+)`, the lifted meet *is* the inclusion function of
the sum `[⊕]`. Its concave (upper) bound is preserved by `IsAlmostConcaveWith.inf`
(proved here at a shared rank). Its convex (lower) bound is **not** preserved by a
raw `⊓` — two almost-convex curves' meet is generally not convex — which is
exactly why the paper canonicalizes with the convex hull `C_vx` (Proposition 3).
The convex-hull re-canonicalization step and the full asymptotic-slope identity
`σ(f⊓g) = min(σf, σg)` (paper Proposition 3, a geometric extremal-point argument)
are scoped out; see the `## SCOPING` note below. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal Topology
open Filter

namespace Container

/-! ## Paper Theorem 3 (Le Boudec–Thiran), eq. (8)/(9) — the algebraic engine -/

/-- **Paper Theorem 3, eq. (8):** the inf-convolution of two origin-null concave
functions is their pointwise meet, `Γ₁ ∗ Γ₂ = Γ₁ ⊕ Γ₂` (`⊕ = min`). This is the
collapse that makes the concave side of `F` closed under `∗`. -/
theorem concave_minConv_eq_inf {Γ₁ Γ₂ : ℝ≥0 → EReal}
    (h₁ : IsConcaveEReal Γ₁) (h₂ : IsConcaveEReal Γ₂)
    (h₁0 : Γ₁ 0 = 0) (h₂0 : Γ₂ 0 = 0) :
    minConv Γ₁ Γ₂ = Γ₁ ⊓ Γ₂ :=
  minConv_eq_inf_of_null Γ₁ Γ₂ h₁ h₂ h₁0 h₂0

/-- **Paper Theorem 3, eq. (9):** an origin-null concave function that never takes
`−∞` is its own sub-additive closure, `Γ⋆ = Γ`. So the concave side of `F` is
fixed by the closure operation. -/
theorem concave_subadditiveClosure_eq_self {Γ : ℝ≥0 → EReal}
    (hnb : IsNeverBot Γ) (h0 : Γ 0 = 0) (hconc : IsConcaveEReal Γ) :
    subadditiveClosureEReal Γ = Γ :=
  subadditiveClosureEReal_eq_self_of_isConcaveEReal Γ hnb h0 hconc

/-! ## Paper Proposition 5 — `ℱ_acv` is closed under inf-convolution `∗`

For genuinely concave bounds null at the origin (the `Γ`-cores of Proposition 1),
the inf-convolution stays concave: by eq. (8) it equals the meet, and the meet of
two concave curves is concave (`IsConcaveEReal.inf`). For the general
almost-concave bounds (a constant prefix, then concave) the same holds via
`IsConcaveEReal.minConv`, which carries the constant prefix through. -/

/-- **Paper Proposition 5 (origin-null case):** the inf-convolution of two
origin-null concave curves is concave — by eq. (8) it is their meet, and the meet
of concave curves is concave. -/
theorem isConcaveEReal_minConv_of_null {Γ₁ Γ₂ : ℝ≥0 → EReal}
    (h₁ : IsConcaveEReal Γ₁) (h₂ : IsConcaveEReal Γ₂)
    (h₁0 : Γ₁ 0 = 0) (h₂0 : Γ₂ 0 = 0) :
    IsConcaveEReal (minConv Γ₁ Γ₂) := by
  rw [concave_minConv_eq_inf h₁ h₂ h₁0 h₂0]
  exact IsConcaveEReal.inf Γ₁ Γ₂ h₁ h₂

/-- **Paper Proposition 5 (general case):** `ℱ_cv` is closed under
inf-convolution: the inf-convolution of two bounded-below concave curves is
concave (`IsConcaveEReal.minConv`). -/
theorem isConcaveEReal_minConv {f g : ℝ≥0 → EReal}
    (hf : IsConcaveEReal f) (hg : IsConcaveEReal g)
    (hnf : IsBddBelowReal f) (hng : IsBddBelowReal g) :
    IsConcaveEReal (minConv f g) :=
  IsConcaveEReal.minConv hf hg hnf hng

/-- **The origin-null concave class is closed under `∗` and stays origin-null.**
The convolution of two origin-null concave curves is origin-null and concave —
the fixed shape of the `Γ`-cores under both `∗` and `⊕` (eq. 8). -/
theorem isConcaveEReal_minConv_null_and_zero {Γ₁ Γ₂ : ℝ≥0 → EReal}
    (h₁ : IsConcaveEReal Γ₁) (h₂ : IsConcaveEReal Γ₂)
    (h₁0 : Γ₁ 0 = 0) (h₂0 : Γ₂ 0 = 0) :
    IsConcaveEReal (minConv Γ₁ Γ₂) ∧ minConv Γ₁ Γ₂ 0 = 0 := by
  refine ⟨isConcaveEReal_minConv_of_null h₁ h₂ h₁0 h₂0, ?_⟩
  rw [concave_minConv_eq_inf h₁ h₂ h₁0 h₂0]
  show Γ₁ 0 ⊓ Γ₂ 0 = 0
  rw [h₁0, h₂0, inf_idem]

/-! ## The asymptotic slope under the meet (paper Proposition 3, provable half)

The paper's internality argument needs `σ(f⊓g) = min(σf, σg)` (Proposition 3).
Only the easy half — `σ(f⊓g) ≤ min(σf, σg)` — is provable from the slope's
monotonicity (`rho_mono`); the reverse inequality is the geometric extremal-point
argument and is scoped out (see `## SCOPING`). -/

/-- The asymptotic slope of a meet is bounded by both slopes:
`ρ_{f⊓g} ≤ ρ_f` and `ρ_{f⊓g} ≤ ρ_g`, hence `ρ_{f⊓g} ≤ min(ρ_f, ρ_g)`. The
provable half of the paper's `σ(f⊓g) = min(σf, σg)` (Proposition 3). -/
theorem rho_inf_le_min (f g : ℝ≥0 → EReal) :
    rho (f ⊓ g) ≤ rho f ⊓ rho g :=
  le_inf (rho_mono fun _ => inf_le_left) (rho_mono fun _ => inf_le_right)

/-- If both meet operands have the *same* asymptotic slope `ρ`, the meet's slope
is `≤ ρ` (the provable bound at the typed common slope). -/
theorem rho_inf_le_of_eq {f g : ℝ≥0 → EReal} {ρ : EReal}
    (hf : rho f = ρ) (hg : rho g = ρ) : rho (f ⊓ g) ≤ ρ := by
  have := rho_inf_le_min f g
  rwa [hf, hg, inf_idem] at this

/-! ## Internality of the lifted meet `[∧]` / `[⊕]` on the concave bound

`Container.inf` lifts `⊓` to both bounds: `[f̲ ⊓ g̲, f̄ ⊓ ḡ]`. Since `⊕ = min`
in `(min,+)`, this lifted meet is the **inclusion function of the sum** `[⊕]`.
Its concave (numerically-upper) bound `hi ⊓ hi'` stays almost concave at a shared
rank (`IsAlmostConcaveWith.inf`) — the genuinely-true, unconditional part of the
internality. -/

/-- **The concave (upper) bound of the lifted meet is again almost concave**, at a
shared rank `τ`. If `c.hi` and `d.hi` are almost concave with the same rank, then
the lifted meet's upper bound `(c [∧] d).hi = c.hi ⊓ d.hi` is almost concave with
that rank (`IsAlmostConcaveWith.inf`). This is the concave half of the sum's
inclusion-function internality (paper Definition 23 / Proposition 3). -/
theorem inf_hi_isAlmostConcaveWith {c d : Container} {τ : ℝ≥0}
    (hc : IsAlmostConcaveWith c.hi τ) (hd : IsAlmostConcaveWith d.hi τ) :
    IsAlmostConcaveWith (inf c d).hi τ := by
  rw [inf_hi]; exact hc.inf hd

/-- **The concave (upper) bound of the lifted meet is almost concave** (rank
existentially quantified), provided the two upper bounds share a rank `τ`. -/
theorem inf_hi_isAlmostConcave_of_sharedRank {c d : Container} {τ : ℝ≥0}
    (hc : IsAlmostConcaveWith c.hi τ) (hd : IsAlmostConcaveWith d.hi τ) :
    IsAlmostConcave (inf c d).hi :=
  ⟨τ, inf_hi_isAlmostConcaveWith hc hd⟩

/-- **Internality of `[∧]` / `[⊕]` to `F`, modulo the convex-bound hull.** If two
containers' almost-concave upper bounds share a rank `τ` (`hcτ`, `hdτ`), the
lifted meet's lower bound is still almost convex after the meet (`hlo`, the
canonicalization step the paper performs with `C_vx`), and the result is
asymptotically typed (`htyped`, the slope identity of Proposition 3), then the
lifted meet `c [∧] d` is again a canonical container of `F`.

The carried hypotheses `hlo` and `htyped` are exactly the parts the paper
discharges by the convex-hull re-canonicalization (`C_vx`) and the geometric
slope identity (Proposition 3); the concave-bound and structural parts are proved
here. See `## SCOPING`. -/
theorem inf_isCanonicalContainer_of_sharedRank {c d : Container} {τ : ℝ≥0}
    (hcτ : IsAlmostConcaveWith c.hi τ) (hdτ : IsAlmostConcaveWith d.hi τ)
    (hlo : IsAlmostConvex (inf c d).lo)
    (htyped : IsAsymptoticallyTyped (inf c d).lo (inf c d).hi) :
    IsCanonicalContainer (inf c d) where
  lo_acx := hlo
  hi_acv := inf_hi_isAlmostConcave_of_sharedRank hcτ hdτ
  typed := htyped

/-! ## The convex-hull (`C_vx`) lower bound is unconditionally convex

The paper restores convexity of the lower bound after a meet with the convex hull
`C_vx = biconj` (Definition 17). The hull is *always* convex: `legendre` lands in
the convex class (`legendre_convex`), so the biconjugate `biconj = 𝓛 ∘ 𝓛` is
convex whenever the inner transform `legendre f` is proper — which holds under the
weak hypothesis `f 0 ≠ ⊤` (the `u = 0` slice `−f 0` is then a finite lower bound
of `legendre f`). This discharges the `hlo` carried in
`inf_isCanonicalContainer_of_sharedRank`: the *canonicalized* meet lower bound
`C_vx (f̲ ⊓ g̲)` is genuinely almost convex. -/

/-- The Legendre–Fenchel transform `𝓛 f` is **proper** (never `⊥`) when
`f 0 ≠ ⊤`: the `u = 0` slice `−f 0` is a finite (≠ `⊥`) lower bound of the
defining supremum. -/
theorem legendre_neverBot_of_zero_ne_top {f : ℝ≥0 → EReal} (h0 : f 0 ≠ ⊤) :
    IsNeverBot (legendre f) := by
  intro t
  have hslice : ((((t * 0 : ℝ≥0) : ℝ) : EReal)) - f 0 ≤ legendre f t := le_legendre f t 0
  have hne : (((t * 0 : ℝ≥0) : ℝ) : EReal) - f 0 ≠ ⊥ := by
    rw [mul_zero]
    show ((0 : ℝ) : EReal) - f 0 ≠ ⊥
    rw [EReal.coe_zero, sub_eq_add_neg, zero_add]
    rw [Ne, EReal.neg_eq_bot_iff]
    exact h0
  exact fun hbot => hne (le_bot_iff.mp (hbot ▸ hslice))

/-- **The biconjugate (convex hull) `C_vx f = 𝓛(𝓛 f)` is convex** whenever
`f 0 ≠ ⊤`. So the canonical lower bound of a container is always in `ℱ_cx`
(`legendre_convex` applied to the proper transform `legendre f`). -/
theorem isConvexEReal_biconj_of_zero_ne_top {f : ℝ≥0 → EReal} (h0 : f 0 ≠ ⊤) :
    IsConvexEReal (biconj f) :=
  legendre_convex (legendre_neverBot_of_zero_ne_top h0)

/-- **The convex hull is almost convex** (rank `0`) whenever `f 0 ≠ ⊤`: a genuine
convex curve is almost convex. The canonicalized lower bound `C_vx (f̲ ⊓ g̲)` of
the lifted meet is therefore in `ℱ_acx`. -/
theorem isAlmostConvex_biconj_of_zero_ne_top {f : ℝ≥0 → EReal} (h0 : f 0 ≠ ⊤) :
    IsAlmostConvex (biconj f) :=
  (isConvexEReal_biconj_of_zero_ne_top h0).isAlmostConvex

/-- **The convex hull preserves the Legendre–Fenchel class**: `C_vx f ≡_𝓛 f`
(`legendre_biconj`). So replacing the meet lower bound by its convex hull keeps
the same uncertainty class — the canonicalization is class-faithful. -/
theorem sameLegendre_biconj (f : ℝ≥0 → EReal) : SameLegendre (biconj f) f :=
  legendre_biconj f

/-- **Canonicalized lifted-meet internality, convex side discharged.** If the two
upper bounds share a rank `τ` and the canonicalized lower bound
`C_vx (c.lo ⊓ d.lo)` is asymptotically typed against the concave upper bound
`c.hi ⊓ d.hi` (`htyped`, the slope identity of Proposition 3), then the container
`[C_vx (c.lo ⊓ d.lo), c.hi ⊓ d.hi]` is a canonical container of `F`. The convex
(lower) bound is convex unconditionally (`isAlmostConvex_biconj_of_zero_ne_top`,
needing only `(c.lo ⊓ d.lo) 0 ≠ ⊤`); only the slope identity remains carried. -/
theorem isCanonicalContainer_canonicalizedInf {c d : Container} {τ : ℝ≥0}
    (hcτ : IsAlmostConcaveWith c.hi τ) (hdτ : IsAlmostConcaveWith d.hi τ)
    (h0 : (c.lo ⊓ d.lo) 0 ≠ ⊤)
    (hle : biconj (c.lo ⊓ d.lo) ≤ c.hi ⊓ d.hi)
    (htyped : IsAsymptoticallyTyped (biconj (c.lo ⊓ d.lo)) (c.hi ⊓ d.hi)) :
    IsCanonicalContainer
      { lo := biconj (c.lo ⊓ d.lo), hi := c.hi ⊓ d.hi, le := hle } where
  lo_acx := isAlmostConvex_biconj_of_zero_ne_top h0
  hi_acv := ⟨τ, hcτ.inf hdτ⟩
  typed := htyped

/-! ## SCOPING — what the FULL [LEC 14] internality needs beyond this file

The paper's Definition 23 (eq. 14) asks each inclusion function `[⋄]` to land
back in `F`. What is *proved* above:

* The algebraic engine (paper Theorem 3, eq. 8/9) — restated faithfully.
* Paper Proposition 5 — `ℱ_acv` closed under `∗` (origin-null and general).
* The concave (upper) bound of the lifted meet stays almost concave at a shared
  rank — the unconditional, structural part of `[⊕]` internality.
* The provable half of the slope identity, `ρ_{f⊓g} ≤ min(ρ_f, ρ_g)`.

What the FULL result additionally needs, scoped here as explicit hypotheses
(`hlo`, `htyped`) or deferred:

* **Convex-bound re-canonicalization `C_vx`** (paper Definition 17 / Proposition
  3). The raw meet of two almost-convex lower bounds is *not* almost convex; the
  paper restores convexity with the convex hull `C_vx = biconj` and renormalizes
  the rank via the lower-bound `Ω` of Definition 20. The hull `biconj` and its
  least-representative theory are in `ContainerCanonical` /
  `ContainerCanonicalBound`; assembling them into the rank-renormalized canonical
  form of `[⊕]g` (paper Proposition 3's `[C_vx(f[⊕]g ⊕ Ω), f̄[⊕]ḡ]_𝓛`) is the
  `[infra]` step left open.
* **The reverse slope inequality** `min(ρ_f, ρ_g) ≤ ρ_{f⊓g}` (paper Proposition 3)
  is a geometric extremal-point argument over ultimately-affine functions; only
  `rho_inf_le_min` (the easy half) is proved. Carried as `htyped`.
* **The convolution inclusion function `[∗]`** (paper Proposition 7): needs `ℱ_acx`
  closed under `∗` (paper Proposition 6, the "end-to-end of linear pieces"
  geometric construction) in addition to Proposition 5; the convolution-of-convex
  half is not on the chord API and is `[infra]`.
* **The closure inclusion function `[⋆]`** (paper Proposition 9): the canonical
  lower bound `f[⋆]` of eq. (18) and the slope lemma 4; built on
  `subadditiveClosureENN_min` / `_eq_self` (present) plus `C_vx` of the closure
  (`[infra]`).

The soundness half of all three (`f[⋄]g ⊃ f⋄g`) is already in DeepWiki
(`Container.inf_mem` / `conv_mem` / `ContainerNN.closure_mem`). -/

/-! ## Faithfulness checks (anonymous restatements vs the paper) -/

-- Paper Theorem 3, eq. (8): `Γ₁ ∗ Γ₂ = Γ₁ ⊕ Γ₂` for origin-null concave curves.
example {Γ₁ Γ₂ : ℝ≥0 → EReal}
    (h₁ : IsConcaveEReal Γ₁) (h₂ : IsConcaveEReal Γ₂)
    (h₁0 : Γ₁ 0 = 0) (h₂0 : Γ₂ 0 = 0) :
    minConv Γ₁ Γ₂ = Γ₁ ⊓ Γ₂ :=
  concave_minConv_eq_inf h₁ h₂ h₁0 h₂0

-- Paper Theorem 3, eq. (9): `Γ⋆ = Γ` for origin-null concave (never-`⊥`) curves.
example {Γ : ℝ≥0 → EReal}
    (hnb : IsNeverBot Γ) (h0 : Γ 0 = 0) (hconc : IsConcaveEReal Γ) :
    subadditiveClosureEReal Γ = Γ :=
  concave_subadditiveClosure_eq_self hnb h0 hconc

-- Paper Proposition 5: `ℱ_acv` closed under `∗` (origin-null concave case).
example {Γ₁ Γ₂ : ℝ≥0 → EReal}
    (h₁ : IsConcaveEReal Γ₁) (h₂ : IsConcaveEReal Γ₂)
    (h₁0 : Γ₁ 0 = 0) (h₂0 : Γ₂ 0 = 0) :
    IsConcaveEReal (minConv Γ₁ Γ₂) :=
  isConcaveEReal_minConv_of_null h₁ h₂ h₁0 h₂0

-- Paper Proposition 3 (provable half): `ρ_{f⊓g} ≤ min(ρ_f, ρ_g)`.
example (f g : ℝ≥0 → EReal) : rho (f ⊓ g) ≤ rho f ⊓ rho g :=
  rho_inf_le_min f g

-- Concave (upper) bound preserved by the lifted meet at a shared rank.
example {c d : Container} {τ : ℝ≥0}
    (hc : IsAlmostConcaveWith c.hi τ) (hd : IsAlmostConcaveWith d.hi τ) :
    IsAlmostConcaveWith (inf c d).hi τ :=
  inf_hi_isAlmostConcaveWith hc hd

-- Paper Definition 17 / Proposition 3: the convex hull `C_vx f = biconj f` is
-- convex (in `ℱ_cx`) under the weak hypothesis `f 0 ≠ ⊤`.
example {f : ℝ≥0 → EReal} (h0 : f 0 ≠ ⊤) : IsConvexEReal (biconj f) :=
  isConvexEReal_biconj_of_zero_ne_top h0

-- Paper Lemma 3 / eq.(10): the convex hull keeps the Legendre–Fenchel class.
example (f : ℝ≥0 → EReal) : SameLegendre (biconj f) f :=
  sameLegendre_biconj f

end Container

end DeepWiki
