import DeepWiki.NetworkCalculus.WorstCaseBoundX3CReductionNetwork
import DeepWiki.NetworkCalculus.ServersBacklog
import DeepWiki.NetworkCalculus.Deviations

/-! # Continuous-time rate integration of the X3C worst-case backlog (DNC Theorem 10.2)
The network file (`WorstCaseBoundX3CReductionNetwork`) computes the worst-case backlog
`backlogAtW` from the *served rates* of the Figure-10.7 construction. This file connects
those rates to an actual cumulative `Curve`-style trajectory: on `[0,1]` the greedy
adversary holds every served rate **constant**, so the cumulative arrivals/departures are
piecewise-linear ramps `c · min(t,1)`, frozen after time `1`. Integrating the constant net
backlog rate over `[0,1)` gives the time-`1⁻` backlog, which equals the rate-based
`backlogAtW`.

The reusable analysis core is `rampCapped c t = c · min(t,1)`: a monotone, null-at-origin,
**continuous** (hence left- and right-continuous) cumulative whose left limit at `1` is `c`.
For arrival ramp rate `a` and departure ramp rate `d` with `d ≤ a`, the backlog
`backlog (rampCapped a) (rampCapped d) = a − d` (the vertical deviation, attained from time
`1` on), and the left limit of the instantaneous backlog at `1⁻` is also `a − d`. Choosing
the net rate `a − d = backlogAtW` realizes the rate-based backlog as a genuine cumulative
trajectory: `backlog A_W D_W = backlogAtW` and `(A_W − D_W)(1⁻) = backlogAtW`.

What is **proved**: the ramp's regularity and left-limit (`rampCapped_*`); the backlog
identity over a ramp pair (`backlog_rampCapped`, `backlogAt_rampCapped`); the left limit of
the instantaneous backlog at `1⁻` (`leftLim_backlogAt_rampCapped_one`); and the realization
of `backlogAtW` by the ramp trajectory (`backlog_trajectory_eq_backlogAtW`). -/

namespace DeepWiki

open Function Set Topology Filter
open scoped NNReal ENNReal

/-! ## The capped-ramp cumulative
`rampCapped c t = c · min(t,1)`: the cumulative of a constant rate `c` held on `[0,1]` and
frozen afterwards. This is the piecewise-linear fluid trajectory the greedy adversary
produces on the unit interval. -/

/-- The **capped ramp** `rampCapped c t = c · min(t,1)`: cumulative of a constant rate `c`
on `[0,1]`, frozen at `c` for `t ≥ 1`. The fluid trajectory of a flow served at rate `c`
until time `1`. -/
noncomputable def rampCapped (c : ℝ≥0) : ℝ≥0 → ℝ≥0 := fun t => c * min t 1

/-- `rampCapped c t = c * min t 1`. -/
theorem rampCapped_apply (c t : ℝ≥0) : rampCapped c t = c * min t 1 := rfl

/-- `rampCapped c 0 = 0`: the trajectory starts at the origin. -/
theorem rampCapped_zero (c : ℝ≥0) : rampCapped c 0 = 0 := by
  simp [rampCapped]

/-- On `[1, ∞)` the ramp is frozen at `c`: `rampCapped c t = c` for `1 ≤ t`. -/
theorem rampCapped_of_one_le {c t : ℝ≥0} (ht : 1 ≤ t) : rampCapped c t = c := by
  simp [rampCapped, min_eq_right ht]

/-- Below `1` the ramp is linear: `rampCapped c t = c * t` for `t ≤ 1`. -/
theorem rampCapped_of_le_one {c t : ℝ≥0} (ht : t ≤ 1) : rampCapped c t = c * t := by
  simp [rampCapped, min_eq_left ht]

/-- The ramp is **monotone** (a cumulative function). -/
theorem rampCapped_mono (c : ℝ≥0) : Monotone (rampCapped c) := fun _ _ h =>
  mul_le_mul_right (min_le_min h le_rfl) c

/-- The ramp is **continuous** (`c · min(t,1)` is a product/min of continuous maps). -/
theorem rampCapped_continuous (c : ℝ≥0) : Continuous (rampCapped c) :=
  continuous_const.mul (continuous_id.min continuous_const)

/-- The ramp is **left-continuous**. -/
theorem rampCapped_isLeftContinuous (c : ℝ≥0) : IsLeftContinuous (rampCapped c) :=
  isLeftContinuous_of_continuous _ (rampCapped_continuous c)

/-- The ramp's **left limit at `1` is `c`** (it is continuous, so the left limit is the
value `rampCapped c 1 = c`). -/
theorem rampCapped_tendsto_nhdsWithin_one (c : ℝ≥0) :
    Tendsto (rampCapped c) (𝓝[<] 1) (𝓝 c) := by
  have hval : rampCapped c 1 = c := rampCapped_of_one_le le_rfl
  have hcont : Tendsto (rampCapped c) (𝓝[<] (1 : ℝ≥0)) (𝓝 (rampCapped c 1)) :=
    ((rampCapped_continuous c).continuousAt.continuousWithinAt :
      ContinuousWithinAt (rampCapped c) (Iio 1) 1)
  rwa [hval] at hcont

/-! ## The backlog of a ramp pair
For arrival ramp rate `a` and departure ramp rate `d` with `d ≤ a`, the instantaneous
backlog is `(a − d) · min(t,1)` and the (sup) backlog is `a − d`, attained from time `1`
on. The net backlog rate `a − d` integrated over the unit interval is the time-`1⁻`
backlog. -/

/-- The **instantaneous backlog** of the ramp pair is the net-rate ramp:
`backlogAt (rampCapped a) (rampCapped d) t = (a − d) · min(t,1)` (when `d ≤ a`). -/
theorem backlogAt_rampCapped {a d : ℝ≥0} (_hda : d ≤ a) (t : ℝ≥0) :
    Deviation.backlogAt (rampCapped a) (rampCapped d) t = (a - d) * min t 1 := by
  rw [Deviation.backlogAt_eq, rampCapped_apply, rampCapped_apply, ← tsub_mul]

/-- The instantaneous ramp backlog is **frozen at `a − d`** from time `1` on. -/
theorem backlogAt_rampCapped_of_one_le {a d : ℝ≥0} (hda : d ≤ a) {t : ℝ≥0} (ht : 1 ≤ t) :
    Deviation.backlogAt (rampCapped a) (rampCapped d) t = a - d := by
  rw [backlogAt_rampCapped hda, min_eq_right ht, mul_one]

/-- The instantaneous ramp backlog is **bounded by `a − d`** everywhere. -/
theorem backlogAt_rampCapped_le {a d : ℝ≥0} (hda : d ≤ a) (t : ℝ≥0) :
    Deviation.backlogAt (rampCapped a) (rampCapped d) t ≤ a - d := by
  rw [backlogAt_rampCapped hda]
  calc (a - d) * min t 1 ≤ (a - d) * 1 := mul_le_mul_right (min_le_right _ _) _
    _ = a - d := mul_one _

/-- **The backlog of the ramp pair is `a − d`**: the vertical deviation
`⨆ t, [rampCapped a − rampCapped d](t)`, attained (and frozen) from time `1` on. -/
theorem backlog_rampCapped {a d : ℝ≥0} (hda : d ≤ a) :
    Deviation.backlog (rampCapped a) (rampCapped d) = ((a - d : ℝ≥0) : ℝ≥0∞) := by
  rw [Deviation.backlog]
  apply le_antisymm
  · refine iSup_le fun t => ?_
    exact_mod_cast backlogAt_rampCapped_le hda t
  · refine le_iSup_of_le 1 ?_
    rw [backlogAt_rampCapped_of_one_le hda (le_refl 1)]

/-- **The left limit of the instantaneous ramp backlog at `1⁻` is `a − d`**: the
instantaneous backlog `(a − d)·min(t,1)` is continuous, so its left limit at `1` is its
value there. This is the "time-`1⁻`" reading of the integrated net backlog rate. -/
theorem tendsto_backlogAt_rampCapped_nhdsWithin_one {a d : ℝ≥0} (hda : d ≤ a) :
    Tendsto (Deviation.backlogAt (rampCapped a) (rampCapped d)) (𝓝[<] 1) (𝓝 (a - d)) := by
  have hfun : Deviation.backlogAt (rampCapped a) (rampCapped d)
      = fun t => (a - d) * min t 1 := by
    funext t; exact backlogAt_rampCapped hda t
  rw [hfun]
  have hval : (a - d) * min (1 : ℝ≥0) 1 = a - d := by rw [min_self, mul_one]
  have hcont : Tendsto (fun t : ℝ≥0 => (a - d) * min t 1) (𝓝[<] (1 : ℝ≥0))
      (𝓝 ((a - d) * min (1 : ℝ≥0) 1)) :=
    ((continuous_const.mul (continuous_id.min continuous_const)).continuousAt.continuousWithinAt :
      ContinuousWithinAt (fun t : ℝ≥0 => (a - d) * min t 1) (Iio 1) 1)
  rwa [hval] at hcont

/-! ## Realization of the rate-based `W`-backlog as a ramp trajectory
Choosing the arrival ramp rate `a` and the departure ramp rate `d` so that the net rate
`a − d` equals the rate-based `backlogAtW`, the cumulative ramp trajectory
`A_W = rampCapped a`, `D_W = rampCapped d` realizes the worst-case backlog: the (sup)
backlog and the time-`1⁻` instantaneous backlog both equal `backlogAtW`. -/

variable {ι αT : Type*} [Fintype ι] [Fintype αT] [DecidableEq αT] [DecidableEq ι]

/-- **The ramp trajectory realizes the rate-based `W`-backlog**: if the net backlog rate
`a − d` equals `(backlogAtW assign : ℝ≥0)`, the cumulative ramp pair
`A_W = rampCapped a`, `D_W = rampCapped d` has backlog `backlogAtW` — the served-rate
quantity is realized by a genuine continuous-time cumulative trajectory. -/
theorem X3CInstance.backlog_trajectory_eq_backlogAtW (I : X3CInstance ι αT)
    {assign : αT → ι} {a d : ℝ≥0} (hda : d ≤ a)
    (hrate : a - d = (I.backlogAtW assign : ℝ≥0)) :
    Deviation.backlog (rampCapped a) (rampCapped d) = ((I.backlogAtW assign : ℝ≥0) : ℝ≥0∞) := by
  rw [backlog_rampCapped hda, hrate]

/-- **The time-`1⁻` instantaneous `W`-backlog of the ramp trajectory is `backlogAtW`**: the
left limit at `1` of `A_W − D_W` equals the rate-based worst-case backlog. This is the
continuous-time "value at `1⁻`" reading the network file's served-rate computation refers
to. -/
theorem X3CInstance.tendsto_backlogAt_trajectory_backlogAtW (I : X3CInstance ι αT)
    {assign : αT → ι} {a d : ℝ≥0} (hda : d ≤ a)
    (hrate : a - d = (I.backlogAtW assign : ℝ≥0)) :
    Tendsto (Deviation.backlogAt (rampCapped a) (rampCapped d)) (𝓝[<] 1)
      (𝓝 ((I.backlogAtW assign : ℝ≥0))) := by
  rw [← hrate]
  exact tendsto_backlogAt_rampCapped_nhdsWithin_one hda

/-! ## Book restatement (Theorem 10.2, continuous-time rate integration)
On the unit interval the greedy adversary holds the served rates constant, so the cumulative
trajectories are capped-ramp cumulatives `rampCapped c t = c · min(t,1)` — monotone,
null-at-origin, left-continuous, with left limit `c` at time `1`. The bottom-server backlog
of the arrival/departure ramp pair `A_W = rampCapped a`, `D_W = rampCapped d` (net rate
`a − d`) is `a − d`, attained from time `1` on, and its left limit at `1⁻` is `a − d`.
Choosing the net rate to be the rate-based `backlogAtW` realizes the worst-case backlog as a
genuine continuous-time cumulative trajectory. -/
example (c : ℝ≥0) :
    -- the ramp is a regular cumulative with left limit `c` at `1`
    rampCapped c 0 = 0 ∧ Monotone (rampCapped c) ∧ IsLeftContinuous (rampCapped c) ∧
    Tendsto (rampCapped c) (𝓝[<] 1) (𝓝 c) :=
  ⟨rampCapped_zero c, rampCapped_mono c, rampCapped_isLeftContinuous c,
   rampCapped_tendsto_nhdsWithin_one c⟩

example {a d : ℝ≥0} (hda : d ≤ a) :
    -- the ramp-pair backlog is the net rate `a − d`, with that left limit at `1⁻`
    Deviation.backlog (rampCapped a) (rampCapped d) = ((a - d : ℝ≥0) : ℝ≥0∞) ∧
    Tendsto (Deviation.backlogAt (rampCapped a) (rampCapped d)) (𝓝[<] 1) (𝓝 (a - d)) :=
  ⟨backlog_rampCapped hda, tendsto_backlogAt_rampCapped_nhdsWithin_one hda⟩

example (I : X3CInstance ι αT) {assign : αT → ι} {a d : ℝ≥0} (hda : d ≤ a)
    (hrate : a - d = (I.backlogAtW assign : ℝ≥0)) :
    -- the ramp trajectory realizes the rate-based worst-case `W`-backlog
    Deviation.backlog (rampCapped a) (rampCapped d) = ((I.backlogAtW assign : ℝ≥0) : ℝ≥0∞) :=
  I.backlog_trajectory_eq_backlogAtW hda hrate

end DeepWiki
