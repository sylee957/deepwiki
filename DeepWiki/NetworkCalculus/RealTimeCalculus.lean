import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # Real-time calculus: the bivariate Chasles framework
Real-time calculus describes a flow by a *bivariate* cumulative function
`f : ℝ≥0 → ℝ≥0 → ℝ`, the amount `f s t` over an interval `[s, t]`, which is
additive over consecutive intervals — the **Chasles relation**
`f s t = f s u + f u t`. The univariate network-calculus reading is
`Â(t) = f 0 t`, and conversely a univariate `g` induces the Chasles bivariate
`(s,t) ↦ g t − g s` (the RTC↔NC conversion). Coherence (Lemma 9.2): in the RTC
greedy-processor equations, if the arrival is Chasles then so is the departure
— the backlog telescopes. (The greedy-processor / variable-capacity
equivalence and the sufficiently-strict type build further on this.) -/

namespace DeepWiki

open scoped NNReal

/-- A bivariate cumulative function `f s t` (the amount over `[s, t]`) satisfies
the **Chasles relation** when it is additive over consecutive intervals:
`f s t = f s u + f u t` for `s ≤ u ≤ t`. This is the bivariate notation
underlying real-time calculus. -/
def IsChasles (f : ℝ≥0 → ℝ≥0 → ℝ) : Prop :=
  ∀ s u t : ℝ≥0, s ≤ u → u ≤ t → f s t = f s u + f u t

/-- The bivariate function `(s, t) ↦ g t − g s` built from a univariate
cumulative function `g` — the network-calculus → real-time-calculus
conversion. -/
def ofUnivariate (g : ℝ≥0 → ℝ) : ℝ≥0 → ℝ≥0 → ℝ := fun s t => g t - g s

/-- `ofUnivariate g` satisfies the Chasles relation (the differences
telescope). -/
theorem isChasles_ofUnivariate (g : ℝ≥0 → ℝ) : IsChasles (ofUnivariate g) := by
  intro s u t _ _
  show g t - g s = (g u - g s) + (g t - g u)
  ring

/-- A Chasles bivariate function is the difference of its univariate reading
`t ↦ f 0 t` — the real-time-calculus → network-calculus conversion:
`f s t = f 0 t − f 0 s` for `s ≤ t`. -/
theorem IsChasles.eq_univariate_sub {f : ℝ≥0 → ℝ≥0 → ℝ} (hf : IsChasles f)
    {s t : ℝ≥0} (hst : s ≤ t) : f s t = f 0 t - f 0 s := by
  have h : f 0 t = f 0 s + f s t := hf 0 s t zero_le hst
  linarith

/-- **Lemma 9.2** (coherence of the RTC equations): if the arrival `A` is
Chasles and the departure satisfies the backlog relation
`D s t = A s t − (b t − b s)` (equation [9.6]), then `D` is Chasles too — the
backlog `b` telescopes across the intermediate point. -/
theorem isChasles_departure {A : ℝ≥0 → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}
    (hA : IsChasles A) {D : ℝ≥0 → ℝ≥0 → ℝ}
    (hD : ∀ s t, D s t = A s t - (b t - b s)) : IsChasles D := by
  intro s u t hsu hut
  rw [hD, hD, hD, hA s u t hsu hut]
  ring

end DeepWiki
