import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Data.EReal.Basic

/-! # Curve definitions
The concrete service/arrival curves of network calculus, as plain definitions
(regularity proofs live in `RealCurvesRegularity`). The pure-delay curve `delay`
is defined once over any ordered domain/value type, and the rate / rate-latency /
token-bucket bases `rate`/`rateLatency`/`tokenBucket` once over a semiring value
type. Each specializes to the `ℝ≥0 → ℝ≥0∞` real curves (`delayNN`, `rateNN`,
`rateLatencyNN`, `tokenBucketNN`, plus `staircase`/`staircaseFloor`/`unitStep`
and the `ℝ≥0`-valued cumulative staircase `staircaseFun`)
and the
complete-domain `ℝ≥0∞ → ℝ≥0∞` variants (`delayENN`,
`rateENN`/`rateLatencyENN`/`tokenBucketENN`) used by the pseudo-inverse catalog;
the `EReal`-valued variants for the service-curve stack are `delayEReal` and
`rateEReal` (its own def — it multiplies in `ℝ≥0` and embeds through `ℝ`, not
the base at `EReal`). Plus the `*_zero_eq` base values and `*_coe` real/complete
agreements. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal
open Set

/-! ## Pure delay

`delay d` is `0` for `t ≤ d` and `⊤` afterwards, defined once over any ordered
domain `D` and value type `V` with `0`/`⊤`; specialized by the result type. -/

/-- Pure-delay curve, defined once over any ordered domain `D` and value type
`V` with `0`/`⊤`: `0` for `t ≤ d`, `⊤` afterwards. Specialize by the result
type — e.g. `delay d : ℝ≥0 → ℝ≥0∞` or `delay d : ℝ≥0∞ → ℝ≥0∞`. -/
noncomputable def delay {D V : Type*} [Preorder D] [Zero V] [Top V]
    (d : D) : D → V :=
  fun t => if t ≤ d then 0 else ⊤

/-- `delay d t = if t ≤ d then 0 else ⊤`. -/
@[simp] theorem delay_apply {D V : Type*} [Preorder D] [Zero V] [Top V]
    (d t : D) : (delay d : D → V) t = if t ≤ d then 0 else ⊤ := rfl

/-- `delay d` vanishes at any `t ≤ d`. -/
theorem delay_eq_zero {D V : Type*} [Preorder D] [Zero V] [Top V]
    (d : D) {t : D} (ht : t ≤ d) : (delay d : D → V) t = 0 := by
  rw [delay_apply, if_pos ht]

/-- `delay d` is `⊤` past `d`. -/
theorem delay_eq_top {D V : Type*} [Preorder D] [Zero V] [Top V]
    (d : D) {t : D} (ht : d < t) : (delay d : D → V) t = ⊤ := by
  rw [delay_apply, if_neg (not_le_of_gt ht)]

/-- First-crossing: for `0 < x`, `x ≤ delay d t ↔ d < t`. -/
theorem le_delay_iff {D V : Type*} [LinearOrder D]
    [PartialOrder V] [Zero V] [OrderTop V]
    (d : D) {x : V} (hx : 0 < x) (t : D) :
    x ≤ (delay d : D → V) t ↔ d < t := by
  rcases le_or_gt t d with ht | ht
  · rw [delay_eq_zero d ht]
    exact ⟨fun h => absurd (le_antisymm h hx.le) hx.ne',
      fun h => absurd ht (not_le.mpr h)⟩
  · rw [delay_eq_top d ht]
    exact ⟨fun _ => ht, fun _ => le_top⟩

/-- Pure-delay curve over `ℝ≥0 → ℝ≥0∞`. -/
noncomputable abbrev delayNN (d : ℝ≥0) : ℝ≥0 → ℝ≥0∞ := delay d

/-- Pure-delay curve over `ℝ≥0∞ → ℝ≥0∞`. -/
noncomputable abbrev delayENN (d : ℝ≥0∞) : ℝ≥0∞ → ℝ≥0∞ := delay d

/-- Pure-delay curve over `ℝ≥0 → EReal`: `0` up to `d`, `⊤` after (the
`delayNN`/`delayENN` sibling for `EReal` values). -/
noncomputable abbrev delayEReal (d : ℝ≥0) : ℝ≥0 → EReal := delay d

/-- `delayNN d 0 = 0`. -/
theorem delayNN_zero_eq (d : ℝ≥0) : delayNN d 0 = 0 := by
  simp [delayNN]

/-- `delayENN d 0 = 0`. -/
theorem delayENN_zero_eq (d : ℝ≥0∞) : delayENN d 0 = 0 := by
  simp [delayENN]

/-- `delayEReal d 0 = 0`. -/
theorem delayEReal_zero_eq (d : ℝ≥0) : delayEReal d 0 = 0 :=
  delay_eq_zero d zero_le'

/-- On finite arguments, `delayENN ↑d` agrees with `delayNN d`. -/
theorem delayENN_coe (d t : ℝ≥0) :
    delayENN (d : ℝ≥0∞) (t : ℝ≥0∞) = delayNN d t := by
  simp only [delayENN, delayNN, delay_apply, ENNReal.coe_le_coe]; convert rfl

/-! ## Polymorphic curve bases

Each curve is defined once over a value type `V` — a `Semiring` (for `·`, `+`,
`0`), plus `Sub` and a `CompleteLinearOrder` (for `-`, `⊓`, `⊤`) where the shape
needs them — then specialized below. -/

/-- Constant-rate curve `t ↦ R · t`, over a semiring value type. -/
def rate {V : Type*} [Semiring V] (R : V) : V → V := fun t => R * t

/-- `rate R t = R * t`. -/
@[simp] theorem rate_apply {V : Type*} [Semiring V] (R t : V) :
    rate R t = R * t := rfl

/-- `rate R 0 = 0`. -/
theorem rate_zero_eq {V : Type*} [Semiring V] (R : V) :
    rate R 0 = 0 := mul_zero R

/-- `rate R` is monotone (`ℝ≥0`). -/
theorem rate_mono (R : ℝ≥0) : Monotone (rate R) := by
  intro a b hab
  rw [rate_apply, rate_apply]
  exact mul_le_mul' le_rfl hab

/-- `rate R` is continuous (`ℝ≥0`). -/
theorem rate_continuous (R : ℝ≥0) : Continuous (rate R) := by
  show Continuous fun t : ℝ≥0 => R * t
  exact continuous_const.mul continuous_id

/-- The rate curve `λ_g` is `R`-Lipschitz once `g ≤ R`. -/
theorem rate_lipschitz {g R : ℝ≥0} (hg : g ≤ R) :
    ∀ v w : ℝ≥0, w ≤ v → rate g v ≤ rate g w + R * (v - w) := by
  intro v w hwv
  have he : rate g v = rate g w + g * (v - w) := by
    rw [rate_apply, rate_apply, ← mul_add, add_tsub_cancel_of_le hwv]
  rw [he]
  exact add_le_add le_rfl (mul_le_mul' hg le_rfl)

/-- Rate-latency curve `t ↦ R · (t - T)`, over a semiring with subtraction. -/
def rateLatency {V : Type*} [Semiring V] [Sub V] (R T : V) : V → V :=
  fun t => R * (t - T)

/-- `rateLatency R T` is monotone (`ℝ≥0`). -/
theorem rateLatency_mono (R T : ℝ≥0) : Monotone (rateLatency R T) := by
  intro a b hab
  show R * (a - T) ≤ R * (b - T)
  exact mul_le_mul' le_rfl (tsub_le_tsub_right hab T)

/-- `rateLatency R T` is continuous (`ℝ≥0`). -/
theorem rateLatency_continuous (R T : ℝ≥0) :
    Continuous (rateLatency R T) := by
  show Continuous fun t : ℝ≥0 => R * (t - T)
  exact continuous_const.mul (continuous_sub_right T)


/-- Token-bucket curve `(r · t + b) ⊓ delay 0` (`0` at `t = 0`), over a semiring
that is a complete linear order. -/
noncomputable def tokenBucket {V : Type*} [Semiring V] [CompleteLinearOrder V]
    (r b : V) : V → V :=
  (fun t => r * t + b) ⊓ delay (0 : V)

/-! ## Real curves `ℝ≥0 → ℝ≥0∞`

`rateNN` is `rate` on coerced inputs (defeq). `rateLatencyNN` subtracts in `ℝ≥0`
*before* coercing (the `(t - T)₊` semantics) — not the post-coercion
`rateLatency` form, so it is its own definition (`rateLatencyENN_coe` bridges
them). `tokenBucketNN` takes the `⊓ delayNN 0` meet pointwise on `ℝ≥0`. -/

/-- Constant-rate curve over `ℝ≥0 → ℝ≥0∞`. -/
noncomputable abbrev rateNN (R : ℝ≥0) : ℝ≥0 → ℝ≥0∞ :=
  fun t => rate (R : ℝ≥0∞) (t : ℝ≥0∞)

/-- `rateNN R t = R * t` (the `ℝ≥0 → ℝ≥0∞` coerced product). -/
@[simp] theorem rateNN_apply (R t : ℝ≥0) :
    rateNN R t = (R : ℝ≥0∞) * (t : ℝ≥0∞) := rfl

/-- Rate-latency curve over `ℝ≥0 → ℝ≥0∞`: `t ↦ R * (t - T)₊` (subtraction in
`ℝ≥0`, then coerced). -/
noncomputable def rateLatencyNN (R T : ℝ≥0) : ℝ≥0 → ℝ≥0∞ :=
  fun t => (R : ℝ≥0∞) * ((t - T : ℝ≥0) : ℝ≥0∞)

/-- Token-bucket curve over `ℝ≥0 → ℝ≥0∞`: `(r * t + b) ⊓ delayNN 0` (`0` at
`t = 0`). -/
noncomputable abbrev tokenBucketNN (r b : ℝ≥0) : ℝ≥0 → ℝ≥0∞ :=
  fun t => tokenBucket (r : ℝ≥0∞) (b : ℝ≥0∞) (t : ℝ≥0∞)

/-- `tokenBucketNN r b t = (r * t + b) ⊓ delayNN 0 t` (pointwise on `ℝ≥0`). -/
@[simp] theorem tokenBucketNN_apply (r b t : ℝ≥0) :
    tokenBucketNN r b t = ((r : ℝ≥0∞) * t + b) ⊓ delayNN 0 t := by
  show ((r : ℝ≥0∞) * t + b) ⊓ delay (0 : ℝ≥0∞) (t : ℝ≥0∞)
      = ((r : ℝ≥0∞) * t + b) ⊓ delayNN 0 t
  congr 1
  rw [delay_apply, delayNN, delay_apply]
  congr 1
  simp [← ENNReal.coe_zero, ENNReal.coe_le_coe]

/-- Staircase curve of step `P`, height `h`, offset `J`, clamped at `0`. -/
noncomputable def staircase (P h : ℝ≥0) (J : ℝ) :
    ℝ≥0 → ℝ≥0∞ :=
  fun t =>
    min (ENNReal.ofReal
      (max (h * ⌈((t : ℝ) + J) / P⌉) 0)) (delayNN 0 t)

/-- Floor staircase of step `P`, height `h`, offset `J`:
`t ↦ h·⌊(t − J)/P⌋`, clamped at `0` by the `ENNReal.ofReal` truncation. -/
noncomputable def staircaseFloor (P h : ℝ≥0) (J : ℝ) :
    ℝ≥0 → ℝ≥0∞ :=
  fun t => ENNReal.ofReal ((h : ℝ) * ⌊((t : ℝ) - J) / (P : ℝ)⌋)

/-- `staircaseFloor P h J t` unfolds to its closed form. -/
@[simp] theorem staircaseFloor_apply (P h : ℝ≥0) (J : ℝ) (t : ℝ≥0) :
    staircaseFloor P h J t
      = ENNReal.ofReal ((h : ℝ) * ⌊((t : ℝ) - J) / (P : ℝ)⌋) := rfl

/-- `staircaseFloor P h J` is monotone (for `0 < P`). -/
theorem staircaseFloor_mono (P h : ℝ≥0) (hP : (0:ℝ) < P) (J : ℝ) :
    Monotone (staircaseFloor P h J) := by
  intro a b hab
  refine ENNReal.ofReal_le_ofReal ?_
  refine mul_le_mul_of_nonneg_left ?_ h.coe_nonneg
  refine Int.cast_le.mpr (Int.floor_mono ?_)
  refine (div_le_div_iff_of_pos_right hP).mpr ?_
  exact sub_le_sub_right (NNReal.coe_le_coe.mpr hab) J

/-! ## The `ℝ≥0`-valued staircase (the cumulative staircase process) -/

/-- The staircase cumulative process `ν_{T,b}` delayed by `d`:
`t ↦ b·⌈(t − d)/T⌉₊`, i.e. `k·b` on `(d + (k−1)·T, d + k·T]`, `0` up to `d`. -/
noncomputable def staircaseFun (T b d : ℝ≥0) : ℝ≥0 → ℝ≥0 :=
  fun t => b * (⌈((t : ℝ) - d) / T⌉₊ : ℝ≥0)

/-- `staircaseFun T b d t` unfolds to its ceiling form. -/
@[simp] theorem staircaseFun_apply (T b d t : ℝ≥0) :
    staircaseFun T b d t = b * (⌈((t : ℝ) - d) / T⌉₊ : ℝ≥0) := rfl

/-- `staircaseFun T b d` vanishes at or before the delay `d`. -/
theorem staircaseFun_eq_zero_of_le {T b d t : ℝ≥0} (h : t ≤ d) :
    staircaseFun T b d t = 0 := by
  unfold staircaseFun
  rw [Nat.ceil_eq_zero.mpr, Nat.cast_zero, mul_zero]
  exact div_nonpos_iff.mpr (Or.inr ⟨by
    simpa using (NNReal.coe_le_coe.mpr h), T.coe_nonneg⟩)

/-- `staircaseFun T b d 0 = 0`. -/
theorem staircaseFun_zero_eq (T b d : ℝ≥0) : staircaseFun T b d 0 = 0 :=
  staircaseFun_eq_zero_of_le zero_le'

/-- `staircaseFun T b d` is nondecreasing. -/
theorem staircaseFun_mono (T b d : ℝ≥0) : Monotone (staircaseFun T b d) := by
  intro u v huv
  unfold staircaseFun
  refine mul_le_mul_right ?_ b
  have h : ((u : ℝ) - d) / T ≤ ((v : ℝ) - d) / T := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have hc : (u : ℝ) ≤ v := NNReal.coe_le_coe.mpr huv
    exact mul_le_mul_of_nonneg_right (by linarith)
      (inv_nonneg.mpr T.coe_nonneg)
  exact_mod_cast Nat.ceil_mono h

/-- The burst curve at level `c`: `0` at the origin, `c` at every
positive time — the finite stand-in for `δ₀`-shaped inputs. -/
noncomputable def burstFun (c : ℝ≥0) : ℝ≥0 → ℝ≥0 :=
  fun t => if t = 0 then 0 else c

/-- `burstFun c 0 = 0`. -/
theorem burstFun_zero_eq (c : ℝ≥0) : burstFun c 0 = 0 := if_pos rfl

/-- `burstFun c t = c` away from the origin. -/
theorem burstFun_apply_of_ne (c : ℝ≥0) {t : ℝ≥0} (ht : t ≠ 0) :
    burstFun c t = c := if_neg ht

/-- `burstFun c` never exceeds its level `c`. -/
theorem burstFun_le (c t : ℝ≥0) : burstFun c t ≤ c := by
  rcases eq_or_ne t 0 with rfl | ht
  · rw [burstFun_zero_eq]
    exact zero_le'
  · rw [burstFun_apply_of_ne c ht]

/-- `burstFun c` is monotone. -/
theorem burstFun_mono (c : ℝ≥0) : Monotone (burstFun c) := by
  intro a b hab
  rcases eq_or_ne a 0 with rfl | ha
  · rw [burstFun_zero_eq]
    exact zero_le'
  · have hb : b ≠ 0 := fun hb => ha (le_antisymm (hb ▸ hab) zero_le')
    rw [burstFun_apply_of_ne c ha, burstFun_apply_of_ne c hb]

/-- Larger delay, smaller process: `staircaseFun T b d' ≤ staircaseFun T b d`
for `d ≤ d'`. -/
theorem staircaseFun_anti (T b : ℝ≥0) {d d' : ℝ≥0} (h : d ≤ d') (t : ℝ≥0) :
    staircaseFun T b d' t ≤ staircaseFun T b d t := by
  unfold staircaseFun
  refine mul_le_mul_right ?_ b
  have h' : ((t : ℝ) - d') / T ≤ ((t : ℝ) - d) / T := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have hc : (d : ℝ) ≤ d' := NNReal.coe_le_coe.mpr h
    exact mul_le_mul_of_nonneg_right (by linarith)
      (inv_nonneg.mpr T.coe_nonneg)
  exact_mod_cast Nat.ceil_mono h'

/-- Translation: a delay bump moves the staircase rigidly,
`staircaseFun T b (d + e) (t + e) = staircaseFun T b d t`. -/
theorem staircaseFun_shift (T b d e t : ℝ≥0) :
    staircaseFun T b (d + e) (t + e) = staircaseFun T b d t := by
  unfold staircaseFun
  have h : (((t + e : ℝ≥0) : ℝ) - ((d + e : ℝ≥0) : ℝ)) / T
      = ((t : ℝ) - d) / T := by
    push_cast
    ring_nf
  rw [h]

/-- Ceiling elim: `staircaseFun T b d t ≤ b·k` once `t ≤ d + k·T` —
within the delay plus `k` periods, at most `k` steps have fired. -/
theorem staircaseFun_le {T b d t : ℝ≥0} {k : ℕ}
    (h : t ≤ d + (k : ℝ≥0) * T) :
    staircaseFun T b d t ≤ b * k := by
  unfold staircaseFun
  have hceil : ⌈((t : ℝ) - d) / T⌉₊ ≤ k := by
    rcases eq_zero_or_pos T with rfl | hT
    · simp
    · refine Nat.ceil_le.mpr ?_
      rw [div_le_iff₀ (by exact_mod_cast hT : (0 : ℝ) < (T : ℝ))]
      have hc := NNReal.coe_le_coe.mpr h
      push_cast at hc
      linarith
  exact mul_le_mul_right (by exact_mod_cast hceil) b

/-- The undelayed staircase obeys its affine constraint `γ_{b,b/T}`:
`ν_{T,b} t ≤ (b/T)·t + b`. -/
theorem staircaseFun_le_affine {T : ℝ≥0} (hT : 0 < T) (b t : ℝ≥0) :
    staircaseFun T b 0 t ≤ b / T * t + b := by
  have hT' : (0 : ℝ) < (T : ℝ) := NNReal.coe_pos.mpr hT
  rw [← NNReal.coe_le_coe]
  unfold staircaseFun
  push_cast
  rw [sub_zero]
  have hceil : (⌈(t : ℝ) / T⌉₊ : ℝ) < (t : ℝ) / T + 1 :=
    Nat.ceil_lt_add_one (div_nonneg t.coe_nonneg hT'.le)
  have hb := mul_le_mul_of_nonneg_left hceil.le b.coe_nonneg
  calc (b : ℝ) * (⌈(t : ℝ) / T⌉₊ : ℝ)
      ≤ (b : ℝ) * ((t : ℝ) / T + 1) := hb
    _ = (b : ℝ) / T * t + b := by ring

/-- Degenerate period: `staircaseFun 0 b d` is constantly `0`. -/
theorem staircaseFun_period_zero (b d : ℝ≥0) :
    staircaseFun 0 b d = fun _ => 0 := by
  funext t
  unfold staircaseFun
  rw [NNReal.coe_zero, div_zero, Nat.ceil_zero, Nat.cast_zero, mul_zero]

/-- Unit step at `T`: `0` for `t ≤ T`, `1` afterwards. -/
noncomputable def unitStep (T : ℝ≥0) : ℝ≥0 → ℝ≥0∞ :=
  fun t => if t ≤ T then 0 else 1

/-- Window curve `ω_w`: `w` at the origin and `⊤` afterwards — the
feedback controller of window flow control. -/
noncomputable def window (w : ℝ≥0∞) : ℝ≥0 → ℝ≥0∞ :=
  fun t => if t = 0 then w else ⊤

/-- `window w t` unfolds to its closed form. -/
@[simp] theorem window_apply (w : ℝ≥0∞) (t : ℝ≥0) :
    window w t = if t = 0 then w else ⊤ := rfl

/-- `window w 0 = w`. -/
theorem window_zero_eq (w : ℝ≥0∞) : window w 0 = w := if_pos rfl

/-- `window w` is monotone (it only steps up to `⊤`). -/
theorem window_mono (w : ℝ≥0∞) : Monotone (window w) := by
  intro a b hab
  by_cases ha : a = 0
  · by_cases hb : b = 0
    · rw [ha, hb]
    · rw [ha, window_zero_eq, show window w b = ⊤ from if_neg hb]
      exact le_top
  · have hb : b ≠ 0 := fun hb0 => ha (le_antisymm (hb0 ▸ hab) zero_le')
    rw [show window w a = ⊤ from if_neg ha,
      show window w b = ⊤ from if_neg hb]

/-! ## Complete-domain variants `ℝ≥0∞ → ℝ≥0∞` (for the pseudo-inverse catalog) -/

/-- Constant-rate curve over `ℝ≥0∞ → ℝ≥0∞`. -/
noncomputable abbrev rateENN (R : ℝ≥0∞) : ℝ≥0∞ → ℝ≥0∞ := rate R

/-- Rate-latency curve over `ℝ≥0∞ → ℝ≥0∞`. -/
noncomputable abbrev rateLatencyENN (R T : ℝ≥0∞) : ℝ≥0∞ → ℝ≥0∞ := rateLatency R T

/-- Token-bucket curve over `ℝ≥0∞ → ℝ≥0∞`. -/
noncomputable abbrev tokenBucketENN (r b : ℝ≥0∞) : ℝ≥0∞ → ℝ≥0∞ := tokenBucket r b

/-! ## `EReal`-valued variants (for the service-curve stack) -/

/-- The `EReal`-valued constant-rate curve `u ↦ C·u`, for min-plus service
statements. -/
noncomputable def rateEReal (C : ℝ≥0) : ℝ≥0 → EReal :=
  fun u => ((C * u : ℝ≥0) : ℝ)

/-- `rateEReal C u = C * u` (the `ℝ≥0` product, embedded through `ℝ` into
`EReal`). -/
@[simp] theorem rateEReal_apply (C u : ℝ≥0) :
    rateEReal C u = (((C * u : ℝ≥0) : ℝ) : EReal) := rfl

/-! ## Agreements and base values -/

/-- `rateLatencyNN` is `rateLatencyENN` on coerced inputs (subtraction commutes with
the `ℝ≥0 → ℝ≥0∞` coercion via `ENNReal.coe_sub`). -/
theorem rateLatencyENN_coe (R T t : ℝ≥0) :
    rateLatencyENN (R : ℝ≥0∞) (T : ℝ≥0∞) (t : ℝ≥0∞) = rateLatencyNN R T t := by
  rw [rateLatencyNN, rateLatencyENN, rateLatency, ENNReal.coe_sub]

/-- `rateLatencyNN R T u = ↑(R * (u - T))`. -/
theorem rateLatencyNN_coe (R T u : ℝ≥0) :
    rateLatencyNN R T u = ((R*(u-T):ℝ≥0):ℝ≥0∞) := by
  simp only [rateLatencyNN]; push_cast; ring

/-- `tokenBucketNN` as the pointwise `(r·t + b) ⊓ delayNN 0` over `ℝ≥0`. -/
theorem tokenBucketNN_eq (r b : ℝ≥0) :
    tokenBucketNN r b = (fun t : ℝ≥0 => (r : ℝ≥0∞) * t + b) ⊓ delayNN 0 := by
  funext t; exact tokenBucketNN_apply r b t

/-- `rateNN R 0 = 0`. -/
theorem rateNN_zero_eq (R : ℝ≥0) : rateNN R 0 = 0 := by
  simp

/-- `rateLatencyNN R T 0 = 0`. -/
theorem rateLatencyNN_zero_eq (R T : ℝ≥0) :
    rateLatencyNN R T 0 = 0 := by
  simp [rateLatencyNN]

/-- `tokenBucketNN r b 0 = 0`. -/
theorem tokenBucketNN_zero_eq (r b : ℝ≥0) :
    tokenBucketNN r b 0 = 0 := by
  simp [delayNN]

/-- `staircase P h J 0 = 0`. -/
theorem staircase_zero_eq (P h : ℝ≥0) (J : ℝ) :
    staircase P h J 0 = 0 := by
  simp [staircase, delayNN]

/-- `staircaseFloor P h J 0 = 0` (for `J ≥ 0`). -/
theorem staircaseFloor_zero_eq (P h : ℝ≥0) {J : ℝ} (hJ : 0 ≤ J) :
    staircaseFloor P h J 0 = 0 := by
  refine ENNReal.ofReal_eq_zero.mpr ?_
  refine mul_nonpos_iff.mpr (Or.inl ⟨h.coe_nonneg, ?_⟩)
  refine Int.cast_nonpos.mpr (Int.floor_nonpos ?_)
  rw [NNReal.coe_zero, zero_sub]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hJ) P.coe_nonneg

/-- `unitStep T 0 = 0`. -/
theorem unitStep_zero_eq (T : ℝ≥0) : unitStep T 0 = 0 := by
  simp [unitStep]

/-- `rateEReal C` is monotone. -/
theorem rateEReal_mono (C : ℝ≥0) : Monotone (rateEReal C) := by
  intro u v huv
  rw [rateEReal_apply, rateEReal_apply]
  exact_mod_cast mul_le_mul_right huv C

/-- `rateEReal C 0 = 0`. -/
theorem rateEReal_zero_eq (C : ℝ≥0) : rateEReal C 0 = 0 := by
  simp [rateEReal]

end DeepWiki
