import DeepWiki.NetworkCalculus.AlmostConcave
import DeepWiki.NetworkCalculus.Containers
import DeepWiki.NetworkCalculus.FunctionDioids
import DeepWiki.NetworkCalculus.BoundedSpot
import Mathlib.Data.EReal.Operations

/-! # Canonical representation of a container (Definition 4.3)
The §4.4.1–§4.4.2 building blocks of the canonical representation of a container.

A function `f` of `ℱ_acx` (`IsAlmostConvex`) or `ℱ_acv` (`IsAlmostConcave`)
decomposes as the `(min,+)` convolution `f = Θ^κ_τ ∗ g` (eq. [4.4]), with the
**elementary function**

  `Θ^κ_τ(t) = κ + δ_τ = κ`  if `t ≤ τ`,  `+∞`  otherwise         (eq. [4.5])

and `g` the piecewise-linear "core", null at the origin and shifted into the
plane by `Θ^κ_τ`. Here `κ = f(0⁺)` is the constant value on the prefix `[0, τ]`
and `τ = max{t | f(t) = κ}` its rank.

This file defines `Theta κ τ` (the book's `Θ^κ_τ`) with its satellites, computes
the convolution `Θ^κ_τ ∗ g` (recovering the constant-prefix-then-core shape when
`g` is non-decreasing), states the decomposition predicate `IsCanonicalDecomp`
(eq. [4.4]), and types the canonical representation of a container (Definition
4.3): a container `[f̲, f̄]_𝓛` whose lower bound is almost convex, upper bound
almost concave, and bounds asymptotically typed (`ρ_{f̲} = ρ_{f̄}`,
`IsAsymptoticallyTyped`). Built over `BoundedSpot`'s pattern for `EReal`-valued
singleton-support pieces. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-! ## The elementary function `Θ^κ_τ` (eq. [4.5]) -/

/-- The **elementary function** `Θ^κ_τ` (eq. [4.5]): value `κ` on the prefix
`[0, τ]`, `⊤ = +∞` afterwards. The `(min,+)` building block that shifts the
core `g` of the canonical decomposition `f = Θ^κ_τ ∗ g` (eq. [4.4]) into the
plane. -/
noncomputable def Theta (κ : EReal) (τ : ℝ≥0) : ℝ≥0 → EReal :=
  fun t => if t ≤ τ then κ else ⊤

/-- Pointwise reading of `Theta`: `κ` on `[0, τ]`, `⊤` off it. -/
@[simp]
theorem Theta_apply (κ : EReal) (τ : ℝ≥0) (t : ℝ≥0) :
    Theta κ τ t = if t ≤ τ then κ else ⊤ := rfl

/-- On the prefix `t ≤ τ`, the elementary function takes value `κ`. -/
theorem Theta_of_le {κ : EReal} {τ t : ℝ≥0} (h : t ≤ τ) : Theta κ τ t = κ := by
  simp [Theta, h]

/-- Off the prefix `τ < t`, the elementary function is `⊤ = +∞`. -/
theorem Theta_of_lt {κ : EReal} {τ t : ℝ≥0} (h : τ < t) : Theta κ τ t = ⊤ := by
  simp [Theta, not_le.mpr h]

/-- At the origin the elementary function takes value `κ`: `Θ^κ_τ(0) = κ`. -/
@[simp]
theorem Theta_zero (κ : EReal) (τ : ℝ≥0) : Theta κ τ 0 = κ :=
  Theta_of_le (bot_le : (0 : ℝ≥0) ≤ τ)

/-- At the rank `τ` the elementary function still takes value `κ`:
`Θ^κ_τ(τ) = κ`. -/
@[simp]
theorem Theta_self (κ : EReal) (τ : ℝ≥0) : Theta κ τ τ = κ :=
  Theta_of_le le_rfl

/-- With finite value `κ ≠ ⊥`, the elementary function is never `⊥ = −∞`
(so `EReal`'s bot-absorbing `+` behaves under convolution). -/
theorem Theta_neverBot {κ : EReal} (hκ : κ ≠ ⊥) (τ : ℝ≥0) :
    SpotNeverBot (Theta κ τ) := by
  intro t
  rcases le_or_gt t τ with h | h
  · rwa [Theta_of_le h]
  · rw [Theta_of_lt h]; exact top_ne_bot

/-- The elementary function is non-decreasing (`κ ≤ ⊤` is the only jump). -/
theorem Theta_mono (κ : EReal) (τ : ℝ≥0) : Monotone (Theta κ τ) := by
  intro a b hab
  rcases le_or_gt b τ with hb | hb
  · rw [Theta_of_le (hab.trans hb), Theta_of_le hb]
  · rw [Theta_of_lt hb]; exact le_top

/-- `Θ^κ_τ` is constant on its prefix `[0, τ]` (the book's `IsConstantOnPrefix`),
hence the prefix part of an almost-convex or -concave shape. -/
theorem Theta_isConstantOnPrefix (κ : EReal) (τ : ℝ≥0) :
    IsConstantOnPrefix (Theta κ τ) τ := fun t ht => by
  rw [Theta_of_le ht, Theta_zero]

/-! ## The convolution `Θ^κ_τ ∗ g` (eq. [4.4])

Convolving with the elementary function recovers the constant-prefix-then-core
shape: on `[0, τ]` the result is `κ + g(0)`, and beyond `τ` it is the core
shifted right by `τ` and lifted by `κ`, `κ + g(t − τ)`. The lower bounds use
that `g` is non-decreasing (`Monotone g`), the book's `g ∈ ℱ↑` hypothesis. -/

/-- Below/at the rank, `Θ^κ_τ ∗ g` is the lifted base value `κ + g(0)` (for
non-decreasing `g`): every split `(u, s)` with `u ≤ τ` has `g s ≥ g 0`, and
the `(t, 0)` split attains `κ + g(0)`. -/
theorem minConv_Theta_apply_of_le {κ : EReal} {τ : ℝ≥0}
    {g : ℝ≥0 → EReal} (hg : SpotNeverBot g) (hmono : Monotone g) {t : ℝ≥0}
    (ht : t ≤ τ) :
    minConv (Theta κ τ) g t = κ + g 0 := by
  apply le_antisymm
  · refine le_of_le_of_eq (minConv_le_add (Theta κ τ) g (add_zero t)) ?_
    rw [Theta_of_le ht]
  · refine le_minConv fun u s hus => ?_
    rcases le_or_gt u τ with hu | hu
    · rw [Theta_of_le hu]
      gcongr
      exact hmono (bot_le : (0 : ℝ≥0) ≤ s)
    · rw [Theta_of_lt hu, EReal.top_add_of_ne_bot (hg s)]
      exact le_top

/-- Beyond the rank `τ < t`, `Θ^κ_τ ∗ g` is the core shifted right by `τ` and
lifted by `κ`: `κ + g(t − τ)` (for non-decreasing `g`). The minimizing split is
`(τ, t − τ)`; any split with `u ≤ τ` has `s ≥ t − τ`, so `g s ≥ g(t − τ)`. -/
theorem minConv_Theta_apply_of_lt {κ : EReal} {τ : ℝ≥0}
    {g : ℝ≥0 → EReal} (hg : SpotNeverBot g) (hmono : Monotone g) {t : ℝ≥0}
    (ht : τ < t) :
    minConv (Theta κ τ) g t = κ + g (t - τ) := by
  apply le_antisymm
  · refine le_of_le_of_eq
      (minConv_le_add (Theta κ τ) g (add_tsub_cancel_of_le ht.le)) ?_
    rw [Theta_self]
  · refine le_minConv fun u s hus => ?_
    rcases le_or_gt u τ with hu | hu
    · rw [Theta_of_le hu]
      gcongr
      -- `u + s = t` and `u ≤ τ` give `t - τ ≤ s`, so `g (t - τ) ≤ g s`
      refine hmono ?_
      have hsu : s = t - u := by rw [← hus, add_tsub_cancel_left]
      have : t - τ ≤ t - u := tsub_le_tsub_left hu t
      rwa [← hsu] at this
    · rw [Theta_of_lt hu, EReal.top_add_of_ne_bot (hg s)]
      exact le_top

/-- The origin value of the convolution: `(Θ^κ_τ ∗ g)(0) = κ + g(0)`. -/
@[simp]
theorem minConv_Theta_apply_zero {κ : EReal} {τ : ℝ≥0} {g : ℝ≥0 → EReal} :
    minConv (Theta κ τ) g 0 = κ + g 0 := by
  rw [minConv_apply_zero, Theta_zero]

/-- The convolution is constant `= κ + g(0)` on the prefix `[0, τ]`: convolving
with `Θ^κ_τ` reproduces the constant prefix of an almost-convex or -concave shape. -/
theorem minConv_Theta_isConstantOnPrefix {κ : EReal} {τ : ℝ≥0}
    {g : ℝ≥0 → EReal} (hg : SpotNeverBot g) (hmono : Monotone g) :
    IsConstantOnPrefix (minConv (Theta κ τ) g) τ := fun t ht => by
  rw [minConv_Theta_apply_of_le hg hmono ht, minConv_Theta_apply_zero]

/-! ## The canonical decomposition `f = Θ^κ_τ ∗ g` (eq. [4.4]) -/

/-- The **canonical decomposition** `f = Θ^κ_τ ∗ g` (eq. [4.4]): a curve `f`
splits as the convolution of its elementary function `Θ^κ_τ` with a core `g`
that is null at the origin (`g(0) = 0`). Here `κ` is the prefix value and `τ`
its rank. -/
def IsCanonicalDecomp (f : ℝ≥0 → EReal) (τ : ℝ≥0) (κ : EReal)
    (g : ℝ≥0 → EReal) : Prop :=
  g 0 = 0 ∧ f = minConv (Theta κ τ) g

/-- Unfolds the canonical decomposition. -/
theorem isCanonicalDecomp_iff (f : ℝ≥0 → EReal) (τ : ℝ≥0) (κ : EReal)
    (g : ℝ≥0 → EReal) :
    IsCanonicalDecomp f τ κ g ↔ g 0 = 0 ∧ f = minConv (Theta κ τ) g := Iff.rfl

/-- The canonical decomposition pins the prefix value `f(0) = κ` (with `g(0) = 0`,
`κ` finite): the constant part of `f` on `[0, τ]` is exactly `κ`. -/
theorem IsCanonicalDecomp.apply_zero {f : ℝ≥0 → EReal} {τ : ℝ≥0} {κ : EReal}
    {g : ℝ≥0 → EReal} (h : IsCanonicalDecomp f τ κ g) : f 0 = κ := by
  rw [h.2, minConv_Theta_apply_zero, h.1, add_zero]

/-- The canonical decomposition reproduces `f`'s constant prefix on `[0, τ]`:
`f` is constant `= κ` there (for non-decreasing, never-`⊥` core `g`). -/
theorem IsCanonicalDecomp.isConstantOnPrefix {f : ℝ≥0 → EReal} {τ : ℝ≥0}
    {κ : EReal} {g : ℝ≥0 → EReal} (hg : SpotNeverBot g)
    (hmono : Monotone g) (h : IsCanonicalDecomp f τ κ g) :
    IsConstantOnPrefix f τ := by
  rw [h.2]; exact minConv_Theta_isConstantOnPrefix hg hmono

/-- Beyond the rank, a canonical decomposition reads `f(t) = κ + g(t − τ)`
(`τ < t`, non-decreasing, never-`⊥` core `g`): the core shifted into the
plane by the elementary function. -/
theorem IsCanonicalDecomp.apply_of_lt {f : ℝ≥0 → EReal} {τ : ℝ≥0} {κ : EReal}
    {g : ℝ≥0 → EReal} (hg : SpotNeverBot g) (hmono : Monotone g)
    (h : IsCanonicalDecomp f τ κ g) {t : ℝ≥0} (ht : τ < t) :
    f t = κ + g (t - τ) := by
  rw [h.2]; exact minConv_Theta_apply_of_lt hg hmono ht

/-- **Existence of the canonical decomposition for a constant-prefix curve.**
Any `f` constant `= κ` on `[0, τ]` with a finite real prefix value `κ : ℝ`,
non-decreasing and never `⊥`, decomposes as `f = Θ^κ_τ ∗ g` with the core
`g(t) = f(t + τ) − κ` (eq. [4.4]). This is the §4.4.1 reduction "every
almost-convex or -concave function is an elementary function convolved with a
piecewise-linear core, null at the origin"; the prefix value `κ = f(0⁺)` is the
book's finite `κ_f`. -/
theorem isCanonicalDecomp_core_of_isConstantOnPrefix {f : ℝ≥0 → EReal}
    {τ : ℝ≥0} {κ : ℝ} (hf : SpotNeverBot f) (hfmono : Monotone f)
    (hprefix : ∀ t : ℝ≥0, t ≤ τ → f t = (κ : EReal)) :
    IsCanonicalDecomp f τ (κ : EReal) (fun t => f (t + τ) - (κ : EReal)) := by
  refine ⟨?_, ?_⟩
  · -- `g(0) = f(τ) − κ = κ − κ = 0`
    simp only [zero_add, hprefix τ le_rfl]
    exact EReal.sub_self (EReal.coe_ne_top κ) (EReal.coe_ne_bot κ)
  · funext t
    -- the core `g` is non-decreasing and never `⊥`
    have hgmono : Monotone (fun t => f (t + τ) - (κ : EReal)) := fun a b hab => by
      simp only [sub_eq_add_neg]
      gcongr
      exact hfmono (by gcongr)
    have hgnb : SpotNeverBot (fun t => f (t + τ) - (κ : EReal)) := fun s => by
      simp only
      rw [sub_eq_add_neg, ← EReal.coe_neg, EReal.add_ne_bot_iff]
      exact ⟨hf (s + τ), EReal.coe_ne_bot _⟩
    rcases le_or_gt t τ with ht | ht
    · rw [minConv_Theta_apply_of_le hgnb hgmono ht, hprefix t ht]
      -- `κ + (f τ − κ) = κ + (κ − κ) = κ + 0 = κ`
      simp only [zero_add, hprefix τ le_rfl,
        EReal.sub_self (EReal.coe_ne_top κ) (EReal.coe_ne_bot κ), add_zero]
    · rw [minConv_Theta_apply_of_lt hgnb hgmono ht]
      -- `κ + (f((t−τ)+τ) − κ) = κ + (f t − κ) = f t`
      rw [tsub_add_cancel_of_le ht.le, add_comm (κ : EReal), EReal.sub_add_cancel]

/-! ## Definition 4.3 — the canonical representation of a container

The set `F` of containers is `{[f̲, f̄]_𝓛 | f̲ ∈ ℱ_acx, f̄ ∈ ℱ_acv, ρ_{f̲} = ρ_{f̄}}`:
the lower bound is **almost convex**, the upper bound **almost concave**, and the
two bounds are **asymptotically typed** (share the asymptotic slope). The
canonical representative inside is the least representative `f̲` of `[f̲]_𝓛`
(the biconjugate convex hull). -/

/-- A `Container` is a **canonical-representation container** (a member of the
book's set `F`, Definition 4.3) when its lower bound is almost convex
(`f̲ ∈ ℱ_acx`), its upper bound almost concave (`f̄ ∈ ℱ_acv`), and the two are
asymptotically typed (`ρ_{f̲} = ρ_{f̄}`). -/
structure IsCanonicalContainer (c : Container) : Prop where
  /-- The lower bound is almost convex (the book's `ℱ_acx`). -/
  lo_acx : IsAlmostConvex c.lo
  /-- The upper bound is almost concave (the book's `ℱ_acv`). -/
  hi_acv : IsAlmostConcave c.hi
  /-- The bounds are asymptotically typed: `ρ_{f̲} = ρ_{f̄}`. -/
  typed : IsAsymptoticallyTyped c.lo c.hi

/-- Unfolds `IsCanonicalContainer` to its three book conditions. -/
theorem isCanonicalContainer_iff (c : Container) :
    IsCanonicalContainer c ↔
      IsAlmostConvex c.lo ∧ IsAlmostConcave c.hi ∧
        IsAsymptoticallyTyped c.lo c.hi :=
  ⟨fun h => ⟨h.lo_acx, h.hi_acv, h.typed⟩, fun ⟨a, b, c⟩ => ⟨a, b, c⟩⟩

/-- A canonical container's bounds share their asymptotic slope `ρ`: the common
growth rate `ρ_{f̲} = ρ_{f̄}` (the book's `ρ`). -/
theorem IsCanonicalContainer.rho_eq {c : Container} (h : IsCanonicalContainer c) :
    rho c.lo = rho c.hi := h.typed

/-- The **canonical representative** of a canonical container is its lower bound
`f̲` — the least representative of the Legendre–Fenchel class `[f̲]_𝓛` (the
biconjugate convex hull is `≤` every LF-member, `biconj_le_of_sameLegendre`),
playing the role of the book's `𝒞_vx(f̲) = f̲`. -/
def Container.canonicalRep (c : Container) : ℝ≥0 → EReal := c.lo

/-- The canonical representative is the lower bound. -/
@[simp]
theorem Container.canonicalRep_eq (c : Container) : c.canonicalRep = c.lo := rfl

/-- The canonical representative is a member of the container. -/
theorem Container.canonicalRep_mem (c : Container) : c.canonicalRep ∈ c := c.lo_mem

/-- The canonical representative is an LF-member (it shares its own transform). -/
theorem Container.canonicalRep_memL (c : Container) : c.MemL c.canonicalRep :=
  c.lo_memL

/-- **The canonical representative is the least LF-member.** Any LF-member `f`
of the container dominates the biconjugate of the canonical representative,
`biconj (canonicalRep c) ≤ f` — the book's "`𝒞_vx(f̲)` is the least
representative" (Proposition 4.2 / Figure 4.13). -/
theorem Container.biconj_canonicalRep_le_of_memL {c : Container}
    {f : ℝ≥0 → EReal} (h : c.MemL f) (u : ℝ≥0) :
    biconj c.canonicalRep u ≤ f u :=
  biconj_le_of_sameLegendre h.2 u

/-! ## Faithfulness checks (against §4.4, book pp. 82–85) -/

/-- Eq. [4.5]: `Θ^κ_τ(t) = κ` if `t ≤ τ`, else `+∞`. -/
example (κ : EReal) (τ t : ℝ≥0) :
    Theta κ τ t = if t ≤ τ then κ else ⊤ := rfl

/-- Eq. [4.4]: `f = Θ^κ_τ ∗ g` with `g(0) = 0`. -/
example (f : ℝ≥0 → EReal) (τ : ℝ≥0) (κ : EReal) (g : ℝ≥0 → EReal) :
    IsCanonicalDecomp f τ κ g ↔ g 0 = 0 ∧ f = minConv (Theta κ τ) g := Iff.rfl

/-- Eq. [4.4] beyond the rank: `f(t) = κ + g(t − τ)` for `τ < t`. -/
example {f : ℝ≥0 → EReal} {τ : ℝ≥0} {κ : EReal} {g : ℝ≥0 → EReal}
    (hg : SpotNeverBot g) (hmono : Monotone g) (h : IsCanonicalDecomp f τ κ g)
    {t : ℝ≥0} (ht : τ < t) : f t = κ + g (t - τ) :=
  h.apply_of_lt hg hmono ht

/-- Definition 4.3: a container of `F` has `f̲ ∈ ℱ_acx`, `f̄ ∈ ℱ_acv`,
`ρ_{f̲} = ρ_{f̄}`. -/
example (c : Container) :
    IsCanonicalContainer c ↔
      IsAlmostConvex c.lo ∧ IsAlmostConcave c.hi ∧
        IsAsymptoticallyTyped c.lo c.hi :=
  isCanonicalContainer_iff c

end DeepWiki
