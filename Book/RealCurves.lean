import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Data.EReal.Basic

/-! # Curve definitions
The concrete service/arrival curves of network calculus, as plain definitions
(regularity proofs live in `RealCurvesRegularity`). The pure-delay curve `delay`
is defined once over any ordered domain/value type, and the rate / rate-latency /
token-bucket bases `rate`/`rateLatency`/`tokenBucket` once over a semiring value
type. Each specializes to the `ℝ≥0 → ℝ≥0∞` real curves (`delayNN`, `rateNN`,
`rateLatencyNN`, `tokenBucketNN`, plus `staircase`/`unitStep`) and the
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

/-- Rate-latency curve `t ↦ R · (t - T)`, over a semiring with subtraction. -/
def rateLatency {V : Type*} [Semiring V] [Sub V] (R T : V) : V → V :=
  fun t => R * (t - T)

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

/-- `unitStep T 0 = 0`. -/
theorem unitStep_zero_eq (T : ℝ≥0) : unitStep T 0 = 0 := by
  simp [unitStep]

/-- `rateEReal C 0 = 0`. -/
theorem rateEReal_zero_eq (C : ℝ≥0) : rateEReal C 0 = 0 := by
  simp [rateEReal]

end DeepWiki
