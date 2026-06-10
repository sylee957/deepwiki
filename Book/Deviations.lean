import Book.FunctionDioids
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Algebra.Order.Monoid.Defs

/-! # Deviations, backlog, and delay
Generalized vertical and horizontal deviations between two functions, and the
backlog/delay of a pair of arrival/departure curves defined from them.

The **vertical** deviation `vDevAt f g t = f t - g t` (and its sup `vDev`) lives
over any domain with a `Sub` codomain. The **horizontal** deviation
`hDevAt f g t` is the least admissible shift `d` with `f t ≤ g (t + d)`, read
into a complete lattice `R` via a `CoeTC D R` coercion on shifts (so a missing
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

/-- Horizontal deviation of `f` from `g` at `t`: the least shift `d` with
`f t ≤ g (t + d)`, read into `R` via the `CoeTC D R` coercion
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
    vDev f g = minDeconv f g 0 := by
  unfold vDev vDevAt minDeconv
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

/-! ## Monotony of deviations -/

/-- Monotony of the vertical deviation: `f' ≤ f` and `g ≤ g'` give
`vDev f' g' ≤ vDev f g`. -/
theorem vDev_mono {D T : Type*} [CompleteLattice T] [AddCommSemigroup T]
    [Sub T] [OrderedSub T] [CovariantClass T T (· + ·) (· ≤ ·)]
    {f f' g g' : D → T} (hf : f' ≤ f) (hg : g ≤ g') :
    vDev f' g' ≤ vDev f g :=
  iSup_le fun t => le_iSup_of_le t (tsub_le_tsub (hf t) (hg t))

/-- Monotony of the horizontal deviation at `t`: `f' ≤ f` and `g ≤ g'` give
`hDevAt f' g' t ≤ hDevAt f g t` (an admissible shift stays admissible). -/
theorem hDevAt_mono {D V R : Type*} [Add D] [Preorder V] [CompleteLattice R]
    [CoeTC D R] {f f' g g' : D → V} (hf : f' ≤ f) (hg : g ≤ g') (t : D) :
    (hDevAt f' g' t : R) ≤ hDevAt f g t :=
  le_iInf fun d => iInf_le _
    (⟨d.1, le_trans (hf t) (le_trans d.2 (hg (t + d.1)))⟩ :
      {e : D // f' t ≤ g' (t + e)})

/-- Monotony of the horizontal deviation: `f' ≤ f` and `g ≤ g'` give
`hDev f' g' ≤ hDev f g`. -/
theorem hDev_mono {D V R : Type*} [Add D] [Preorder V] [CompleteLattice R]
    [CoeTC D R] {f f' g g' : D → V} (hf : f' ≤ f) (hg : g ≤ g') :
    (hDev f' g' : R) ≤ hDev f g :=
  iSup_le fun t => le_iSup_of_le t (hDevAt_mono hf hg t)

/-! ## Sup-based form of the horizontal deviation -/

/-- For nondecreasing `g`, `hDevAt f g t` — an infimum of admissible shifts —
is also the supremum of the inadmissible ones, `⨆ {d | g (t + d) < f t}`. -/
theorem hDevAt_eq_iSup_lt {V : Type*} [LinearOrder V] {f g : ℝ≥0 → V}
    (hg : Monotone g) (t : ℝ≥0) :
    (hDevAt f g t : ℝ≥0∞) =
      ⨆ d : {d : ℝ≥0 // g (t + d) < f t}, (d.1 : ℝ≥0∞) := by
  apply le_antisymm
  · by_contra hcon
    rw [not_le] at hcon
    obtain ⟨c, hc1, hc2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hcon
    rcases le_or_gt (f t) (g (t + c)) with hadm | hbad
    · exact absurd
        (iInf_le _ (⟨c, hadm⟩ : {d : ℝ≥0 // f t ≤ g (t + d)}))
        (not_le.mpr hc2)
    · exact absurd
        (le_iSup (fun d : {d : ℝ≥0 // g (t + d) < f t} => (d.1 : ℝ≥0∞))
          ⟨c, hbad⟩)
        (not_le.mpr hc1)
  · refine iSup_le ?_
    rintro ⟨d', hd'⟩
    refine le_iInf ?_
    rintro ⟨d, hd⟩
    show (d' : ℝ≥0∞) ≤ (d : ℝ≥0∞)
    by_contra hdd
    rw [not_le] at hdd
    have hlt : d < d' := by exact_mod_cast hdd
    exact absurd
      (lt_of_le_of_lt (le_trans hd (hg (add_le_add le_rfl hlt.le))) hd')
      (lt_irrefl _)

/-! ## Backlog and delay of cumulative curves
For arrival/departure curves `A, D : ℝ≥0 → ℝ≥0`, the **backlog** is the vertical
deviation and the **delay** the horizontal one, the latter valued in `ℝ≥0∞` via
the coercion `(↑· : ℝ≥0 → ℝ≥0∞)`. -/

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
