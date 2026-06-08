import Book.FunctionDioids
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Algebra.Order.Monoid.Defs

/-! # Deviations, backlog, and delay
Generalized vertical and horizontal deviations between two functions, and the
backlog/delay of a pair of arrival/departure curves defined from them.

The **vertical** deviation `vDevAt f g t = f t - g t` (and its sup `vDev`) lives
over any domain with a `Sub` codomain. The **horizontal** deviation
`hDevAt ι f g t` is the least admissible shift `d` with `f t ≤ g (t + d)`,
measured through an embedding `ι` of shifts into a complete lattice (so a missing
shift reads as `⊤`); `hDev` is its sup over `t`.

The cumulative-curve **backlog** `b(A, D)` is the vertical deviation and the
**delay** `d(A, D)` is the horizontal one (`namespace Deviation`). -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-! ## Definitions -/

/-- Vertical deviation of `f` from `g` at `t`: `f t - g t`. -/
def vDevAt {D T : Type*} [Sub T] (f g : D → T) (t : D) : T :=
  f t - g t

/-- Vertical deviation `vDev f g = ⨆ t, f t - g t`. -/
noncomputable def vDev {D T : Type*} [SupSet T] [Sub T]
    (f g : D → T) : T :=
  ⨆ t : D, vDevAt f g t

/-- Horizontal deviation of `f` from `g` at `t`, measured through `ι`: the least
shift `d` with `f t ≤ g (t + d)`, measured in `R` via the coercion `D → R`
(a missing shift reads as `⊤`). -/
noncomputable def hDevAt {D V R : Type*}
    [Add D] [Preorder V] [CompleteLattice R] [CoeTC D R]
    (f g : D → V) (t : D) : R :=
  ⨅ d : {d : D // f t ≤ g (t + d)}, (↑d.1 : R)

/-- Horizontal deviation `hDev f g = ⨆ t, hDevAt f g t`. -/
noncomputable def hDev {D V R : Type*}
    [Add D] [Preorder V] [CompleteLattice R] [CoeTC D R]
    (f g : D → V) : R :=
  ⨆ t : D, hDevAt f g t

/-! ## Basic lemmas -/

/-- `vDev f g = ⨆ t, f t - g t` unfolds the pointwise vertical deviation. -/
theorem vDev_eq_iSup {D T : Type*} [SupSet T] [Sub T]
    (f g : D → T) : vDev f g = ⨆ t : D, f t - g t := rfl

/-- `vDev f g = (f ⊘ g) 0`. -/
theorem vDev_eq_deconv_zero {D T : Type*}
    [_root_.AddZeroClass D] [SupSet T] [Sub T]
    (f g : D → T) :
    vDev f g = deconv f g 0 := by
  unfold vDev vDevAt deconv
  simp only [zero_add]

/-- `hDevAt f g t = ⊤` when no admissible shift exists. -/
theorem hDevAt_eq_top {D V : Type*} (R : Type*)
    [Add D] [Preorder V] [CompleteLattice R] [CoeTC D R]
    (f g : D → V) (t : D)
    (h : ∀ d : D, ¬ f t ≤ g (t + d)) :
    (hDevAt f g t : R) = ⊤ := by
  unfold hDevAt
  rw [iInf_eq_top]
  rintro ⟨d, hd⟩
  exact absurd hd (h d)

/-! ## Backlog and delay of cumulative curves
For arrival/departure curves `A, D : ℝ≥0 → ℝ≥0`, the **backlog** is the vertical
deviation and the **delay** the horizontal one, the latter valued in `ℝ≥0∞` via
the embedding `(↑· : ℝ≥0 → ℝ≥0∞)`. -/

namespace Deviation

/-- Backlog of departure `D` behind arrival `A` at `t`: `A t - D t`. -/
def backlogAt (A D : ℝ≥0 → ℝ≥0) (t : ℝ≥0) : ℝ≥0 :=
  vDevAt A D t

/-- Backlog `b(A, D) = ⨆ t, A t - D t`, the vertical deviation. -/
noncomputable def backlog (A D : ℝ≥0 → ℝ≥0) : ℝ≥0 :=
  vDev A D

/-- Delay of `D` behind `A` at `t`: least shift `d` with `A t ≤ D (t + d)`. -/
noncomputable def delayAt (A D : ℝ≥0 → ℝ≥0) (t : ℝ≥0) : ℝ≥0∞ :=
  hDevAt A D t

/-- Delay `d(A, D) = ⨆ t, delayAt A D t`, the horizontal deviation. -/
noncomputable def delay (A D : ℝ≥0 → ℝ≥0) : ℝ≥0∞ :=
  hDev A D

/-- `backlogAt A D t = A t - D t`. -/
theorem backlogAt_eq (A D : ℝ≥0 → ℝ≥0) (t : ℝ≥0) :
    backlogAt A D t = A t - D t := rfl

/-- `backlog A D = ⨆ t, A t - D t`. -/
theorem backlog_eq_iSup (A D : ℝ≥0 → ℝ≥0) :
    backlog A D = ⨆ t : ℝ≥0, A t - D t := rfl

/-- `delayAt A D t` is the least shift `d` with `A t ≤ D (t + d)`. -/
theorem delayAt_eq (A D : ℝ≥0 → ℝ≥0) (t : ℝ≥0) :
    delayAt A D t
      = ⨅ d : {d : ℝ≥0 // A t ≤ D (t + d)}, (d.1 : ℝ≥0∞) := rfl

/-- `delay A D = ⨆ t, delayAt A D t`. -/
theorem delay_eq_iSup (A D : ℝ≥0 → ℝ≥0) :
    delay A D = ⨆ t : ℝ≥0, delayAt A D t := rfl

end Deviation

end DeepWiki
