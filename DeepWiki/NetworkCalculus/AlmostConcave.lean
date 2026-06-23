import DeepWiki.NetworkCalculus.Concave
import DeepWiki.NetworkCalculus.Convex
import DeepWiki.NetworkCalculus.FunctionDioids
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Order.LiminfLimsup

/-! # Almost-concave / almost-convex curves and the asymptotic slope
The §4.4 foundation of the *container* theory. The bounds of a container of
`(min,plus)` functions are *piecewise linear, ultimately linear* functions that
fall into two classes:

* `IsAlmostConvex` (the book's `ℱ_acx`): convex curves with a constant part on
  `[0, τ_f]`;
* `IsAlmostConcave` (the book's `ℱ_acv`): "almost" concave — constant on
  `[0, τ_f]` and concave on `(τ_f, +∞)`.

The **asymptotic slope** `rho f` (the book's `ρ_f`) is the slope of the last
semi-infinite segment, `limsup_{t→∞} f(t)/t`; for an ultimately linear function
it is the rate of that final segment (possibly `+∞`). A container's lower and
upper bounds always share this slope (`IsAsymptoticallyTyped`).

Built over `f : ℝ≥0 → EReal` on top of the chord predicates `IsConcaveEReal`
(`DeepWiki.NetworkCalculus.Concave`) and `IsConvexEReal`
(`DeepWiki.NetworkCalculus.Convex`). -/

namespace DeepWiki

open scoped NNReal Topology
open Filter

/-! ## The asymptotic slope `ρ_f` -/

/-- The **asymptotic slope** of a curve `f : ℝ≥0 → EReal`, the book's `ρ_f`:
`limsup_{t→∞} f(t)/t`, the slope of the last semi-infinite segment (possibly
`+∞`). For an ultimately linear function this is the rate of its final
segment. -/
noncomputable def rho (f : ℝ≥0 → EReal) : EReal :=
  limsup (fun t : ℝ≥0 => f t / ((t : ℝ) : EReal)) atTop

/-- `rho` is monotone: a pointwise-dominated curve has no larger asymptotic
slope (`f ≤ g ⟹ rho f ≤ rho g`). -/
theorem rho_mono {f g : ℝ≥0 → EReal} (h : ∀ t, f t ≤ g t) : rho f ≤ rho g := by
  refine limsup_le_limsup (Eventually.of_forall fun t => ?_)
  exact EReal.div_le_div_right_of_nonneg (by exact_mod_cast (t : ℝ≥0).coe_nonneg) (h t)

/-- A constant curve has asymptotic slope `0`: `↑c / ↑t → 0`, so the `limsup`
is `0`. -/
theorem rho_const (c : ℝ) :
    rho (fun _ : ℝ≥0 => (c : EReal)) = 0 := by
  have hcoe : Tendsto (fun t : ℝ≥0 => (t : ℝ)) atTop atTop :=
    NNReal.tendsto_coe_atTop.mpr tendsto_id
  have hcr : Tendsto (fun x : ℝ => (c : ℝ) / x) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul c
    simpa [div_eq_mul_inv, mul_comm] using this
  have hE : Tendsto (fun t : ℝ≥0 => (c : EReal) / ((t : ℝ) : EReal)) atTop (𝓝 (0 : EReal)) := by
    have hcast : Tendsto (fun t : ℝ≥0 => (((c : ℝ) / (t : ℝ) : ℝ) : EReal)) atTop
        (𝓝 (0 : EReal)) := by
      have h0 : ((0 : ℝ) : EReal) = (0 : EReal) := rfl
      rw [← h0]; exact EReal.tendsto_coe.mpr (hcr.comp hcoe)
    refine hcast.congr fun t => ?_
    rw [EReal.coe_div]
  rw [rho]; exact hE.limsup_eq

/-- The asymptotic slope of a curve that is eventually affine with rate `r`,
`f(t) = r·t + b`, is `r`: the burst `b` washes out under division by `t`. The
real shadow `(r·t + b)/t → r`, so the `EReal` quotient tends to `↑r` and the
`limsup` is `↑r`. -/
theorem rho_affine (r b : ℝ≥0) :
    rho (fun t : ℝ≥0 => (((r * t + b : ℝ≥0) : ℝ) : EReal)) = ((r : ℝ) : EReal) := by
  -- `b/x → 0` along `ℝ`'s `atTop` (constant times `x⁻¹`)
  have hbr : Tendsto (fun x : ℝ => (b : ℝ) / x) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (b : ℝ)
    simpa [div_eq_mul_inv, mul_comm] using this
  -- pull back along `(↑) : ℝ≥0 → ℝ`, which pushes `atTop` to `atTop`
  have hcoe : Tendsto (fun t : ℝ≥0 => (t : ℝ)) atTop atTop :=
    NNReal.tendsto_coe_atTop.mpr tendsto_id
  have hb : Tendsto (fun t : ℝ≥0 => (b : ℝ) / (t : ℝ)) atTop (𝓝 0) := hbr.comp hcoe
  -- the real shadow `(r·t + b)/t = r + b/t → r`
  have hreal : Tendsto (fun t : ℝ≥0 => ((r : ℝ) * (t : ℝ) + (b : ℝ)) / (t : ℝ))
      atTop (𝓝 ((r : ℝ))) := by
    have hsum : Tendsto (fun t : ℝ≥0 => (r : ℝ) + (b : ℝ) / (t : ℝ)) atTop (𝓝 ((r : ℝ))) := by
      simpa using (tendsto_const_nhds (x := (r : ℝ))).add hb
    refine hsum.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
    field_simp
  -- lift to `EReal` and identify the `limsup`
  have hE : Tendsto (fun t : ℝ≥0 => (((r * t + b : ℝ≥0) : ℝ) : EReal) / ((t : ℝ) : EReal))
      atTop (𝓝 (((r : ℝ) : EReal))) := by
    have hcast : Tendsto (fun t : ℝ≥0 =>
        ((((r : ℝ) * (t : ℝ) + (b : ℝ)) / (t : ℝ) : ℝ) : EReal)) atTop (𝓝 (((r : ℝ) : EReal))) :=
      EReal.tendsto_coe.mpr hreal
    refine hcast.congr fun t => ?_
    rw [EReal.coe_div]
    norm_cast
  exact hE.limsup_eq

/-! ## The almost-concave / almost-convex classes -/

/-- `f` is constant `= f 0` on the closed prefix `[0, τ]`. -/
def IsConstantOnPrefix (f : ℝ≥0 → EReal) (τ : ℝ≥0) : Prop :=
  ∀ t : ℝ≥0, t ≤ τ → f t = f 0

/-- A curve `f : ℝ≥0 → EReal` is **almost concave** (the book's `ℱ_acv`) for a
rank `τ`: constant on `[0, τ]` and concave on `(τ, +∞)` (chord inequality for
domain points `> τ`). -/
def IsAlmostConcaveWith (f : ℝ≥0 → EReal) (τ : ℝ≥0) : Prop :=
  IsConstantOnPrefix f τ ∧
    ∀ s t : ℝ≥0, τ < s → τ < t → ∀ p : ℝ≥0, p ≤ 1 →
      ((p : ℝ) : EReal) * f s + (((1 - p : ℝ≥0) : ℝ) : EReal) * f t
        ≤ f (p * s + (1 - p) * t)

/-- A curve is **almost concave** when it is almost concave for some rank `τ`. -/
def IsAlmostConcave (f : ℝ≥0 → EReal) : Prop := ∃ τ : ℝ≥0, IsAlmostConcaveWith f τ

/-- A curve `f : ℝ≥0 → EReal` is **almost convex** (the book's `ℱ_acx`) for a
rank `τ`: constant on `[0, τ]` and convex on `(τ, +∞)`. -/
def IsAlmostConvexWith (f : ℝ≥0 → EReal) (τ : ℝ≥0) : Prop :=
  IsConstantOnPrefix f τ ∧
    ∀ s t : ℝ≥0, τ < s → τ < t → ∀ p : ℝ≥0, p ≤ 1 →
      f (p * s + (1 - p) * t)
        ≤ ((p : ℝ) : EReal) * f s + (((1 - p : ℝ≥0) : ℝ) : EReal) * f t

/-- A curve is **almost convex** when it is almost convex for some rank `τ`. -/
def IsAlmostConvex (f : ℝ≥0 → EReal) : Prop := ∃ τ : ℝ≥0, IsAlmostConvexWith f τ

/-- A genuinely concave curve is almost concave (rank `0`): the chord inequality
holds for all domain points, in particular those `> 0`. -/
theorem IsConcaveEReal.isAlmostConcave {f : ℝ≥0 → EReal} (hf : IsConcaveEReal f) :
    IsAlmostConcave f :=
  ⟨0, fun t ht => by rw [le_zero_iff.mp ht],
    fun s t _ _ p hp => hf s t p hp⟩

/-- A genuinely convex curve is almost convex (rank `0`). -/
theorem IsConvexEReal.isAlmostConvex {f : ℝ≥0 → EReal} (hf : IsConvexEReal f) :
    IsAlmostConvex f :=
  ⟨0, fun t ht => by rw [le_zero_iff.mp ht],
    fun s t _ _ p hp => hf s t p hp⟩

/-! ## Closure of the classes

`ℱ_acv` is closed under `∧` (`⊓`) and `ℱ_acx` under `∨` (`⊔`) and `+` *when the
two curves share a common rank `τ`* — the meet/join of two curves concave/convex
on the common tail `(τ, +∞)` is again concave/convex there, and the common
constant prefix `[0, τ]` is preserved. (For *distinct* ranks the meet's rank
must be renormalized — that is the book's canonical-representation step, deferred
here.) -/

/-- The constant-prefix property is preserved by pointwise `⊓` at a shared rank. -/
theorem IsConstantOnPrefix.inf {f g : ℝ≥0 → EReal} {τ : ℝ≥0}
    (hf : IsConstantOnPrefix f τ) (hg : IsConstantOnPrefix g τ) :
    IsConstantOnPrefix (f ⊓ g) τ := fun t ht => by
  simp only [Pi.inf_apply]; rw [hf t ht, hg t ht]

/-- The constant-prefix property is preserved by pointwise `⊔` at a shared rank. -/
theorem IsConstantOnPrefix.sup {f g : ℝ≥0 → EReal} {τ : ℝ≥0}
    (hf : IsConstantOnPrefix f τ) (hg : IsConstantOnPrefix g τ) :
    IsConstantOnPrefix (f ⊔ g) τ := fun t ht => by
  simp only [Pi.sup_apply]; rw [hf t ht, hg t ht]

/-- The constant-prefix property is preserved by pointwise `+` at a shared rank. -/
theorem IsConstantOnPrefix.add {f g : ℝ≥0 → EReal} {τ : ℝ≥0}
    (hf : IsConstantOnPrefix f τ) (hg : IsConstantOnPrefix g τ) :
    IsConstantOnPrefix (f + g) τ := fun t ht => by
  simp only [Pi.add_apply]; rw [hf t ht, hg t ht]

/-- **`ℱ_acv` is closed under `∧` at a shared rank**: the pointwise meet of two
almost-concave curves of the same rank `τ` is almost concave with rank `τ`. The
common constant prefix survives, and the meet of two curves concave on the tail
`(τ, +∞)` is concave there (each chord of `f` and of `g` lies below the meet's
value, so their meet on the left lies below it). -/
theorem IsAlmostConcaveWith.inf {f g : ℝ≥0 → EReal} {τ : ℝ≥0}
    (hf : IsAlmostConcaveWith f τ) (hg : IsAlmostConcaveWith g τ) :
    IsAlmostConcaveWith (f ⊓ g) τ := by
  refine ⟨hf.1.inf hg.1, fun s t hs ht p hp => ?_⟩
  simp only [Pi.inf_apply]
  refine le_inf ?_ ?_
  · refine le_trans ?_ (hf.2 s t hs ht p hp)
    exact add_le_add
      (mul_le_mul_of_nonneg_left inf_le_left (EReal.coe_nonneg.2 p.coe_nonneg))
      (mul_le_mul_of_nonneg_left inf_le_left (EReal.coe_nonneg.2 (1 - p : ℝ≥0).coe_nonneg))
  · refine le_trans ?_ (hg.2 s t hs ht p hp)
    exact add_le_add
      (mul_le_mul_of_nonneg_left inf_le_right (EReal.coe_nonneg.2 p.coe_nonneg))
      (mul_le_mul_of_nonneg_left inf_le_right (EReal.coe_nonneg.2 (1 - p : ℝ≥0).coe_nonneg))

/-- **`ℱ_acx` is closed under `∨` at a shared rank**: the pointwise join of two
almost-convex curves of the same rank `τ` is almost convex with rank `τ` (dual of
`IsAlmostConcaveWith.inf`). -/
theorem IsAlmostConvexWith.sup {f g : ℝ≥0 → EReal} {τ : ℝ≥0}
    (hf : IsAlmostConvexWith f τ) (hg : IsAlmostConvexWith g τ) :
    IsAlmostConvexWith (f ⊔ g) τ := by
  refine ⟨hf.1.sup hg.1, fun s t hs ht p hp => ?_⟩
  simp only [Pi.sup_apply]
  refine sup_le ?_ ?_
  · refine le_trans (hf.2 s t hs ht p hp) ?_
    exact add_le_add
      (mul_le_mul_of_nonneg_left le_sup_left (EReal.coe_nonneg.2 p.coe_nonneg))
      (mul_le_mul_of_nonneg_left le_sup_left (EReal.coe_nonneg.2 (1 - p : ℝ≥0).coe_nonneg))
  · refine le_trans (hg.2 s t hs ht p hp) ?_
    exact add_le_add
      (mul_le_mul_of_nonneg_left le_sup_right (EReal.coe_nonneg.2 p.coe_nonneg))
      (mul_le_mul_of_nonneg_left le_sup_right (EReal.coe_nonneg.2 (1 - p : ℝ≥0).coe_nonneg))

/-! ## The asymptotic typing of a container

A *container* is an interval `[f̲, f̄]` of curves; its lower and upper bounds
always share the asymptotic slope (`ρ_{f̲} = ρ_{f̄}`), the asymptotic-typing
condition used to define the canonical representation (Definition 4.3) and
maximal uncertainty (Definition 4.4). -/

/-- A pair of curves is **asymptotically typed** when its lower and upper bounds
share an asymptotic slope, `ρ_{fLow} = ρ_{fUp}` (the book's `ρ_{f̲} = ρ_{f̄}`).
This is the well-typedness condition on a container `[fLow, fUp]`. -/
def IsAsymptoticallyTyped (fLow fUp : ℝ≥0 → EReal) : Prop := rho fLow = rho fUp

/-- A container `[fLow, fUp]` (i.e. `fLow ≤ fUp` pointwise) forces
`ρ_{fLow} ≤ ρ_{fUp}`: the asymptotic slope is monotone, so equality (asymptotic
typing) is the natural closure condition. -/
theorem rho_le_rho_of_le {fLow fUp : ℝ≥0 → EReal} (h : ∀ t, fLow t ≤ fUp t) :
    rho fLow ≤ rho fUp := rho_mono h

/-! ## Faithfulness checks (against §4.4, book pp. 82–83) -/

/-- `ρ_f` is `limsup_{t→∞} f(t)/t` (the slope of the last semi-infinite segment). -/
example (f : ℝ≥0 → EReal) :
    rho f = limsup (fun t : ℝ≥0 => f t / ((t : ℝ) : EReal)) atTop := rfl

/-- The asymptotic slope of the affine curve `t ↦ r·t + b` is `r`. -/
example (r b : ℝ≥0) :
    rho (fun t : ℝ≥0 => (((r * t + b : ℝ≥0) : ℝ) : EReal)) = ((r : ℝ) : EReal) :=
  rho_affine r b

/-- `ℱ_acv ∋ f`: `f` is constant on `[0, τ]` and concave on `(τ, +∞)`. -/
example (f : ℝ≥0 → EReal) (τ : ℝ≥0) :
    IsAlmostConcaveWith f τ ↔
      (∀ t : ℝ≥0, t ≤ τ → f t = f 0) ∧
      (∀ s t : ℝ≥0, τ < s → τ < t → ∀ p : ℝ≥0, p ≤ 1 →
        ((p : ℝ) : EReal) * f s + (((1 - p : ℝ≥0) : ℝ) : EReal) * f t
          ≤ f (p * s + (1 - p) * t)) := Iff.rfl

/-- Concave ⟹ almost concave, the basic inclusion `ℱ_cv ⊆ ℱ_acv`. -/
example (f : ℝ≥0 → EReal) (hf : IsConcaveEReal f) : IsAlmostConcave f :=
  hf.isAlmostConcave

end DeepWiki
