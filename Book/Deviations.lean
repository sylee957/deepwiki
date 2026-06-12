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

/-- Elim: each pointwise deviation bounds the vertical deviation from below,
`vDevAt f g t ≤ vDev f g`. -/
theorem vDevAt_le_vDev {D T : Type*} [CompleteLattice T] [Sub T]
    (f g : D → T) (t : D) : vDevAt f g t ≤ vDev f g :=
  le_iSup (vDevAt f g) t

/-- Elim: each pointwise deviation bounds the horizontal deviation from
below, `hDevAt f g t ≤ hDev f g`. -/
theorem hDevAt_le_hDev {D V R : Type*}
    [Add D] [Preorder V] [CompleteLattice R] [CoeTC D R]
    (f g : D → V) (t : D) : (hDevAt f g t : R) ≤ hDev f g :=
  le_iSup (fun t => (hDevAt f g t : R)) t

/-- Intro: a uniform bound on the pointwise deviations bounds the vertical
deviation, `vDev f g ≤ x`. -/
theorem vDev_le {D T : Type*} [CompleteLattice T] [Sub T]
    {f g : D → T} {x : T} (h : ∀ t, vDevAt f g t ≤ x) :
    vDev f g ≤ x :=
  iSup_le h

/-- Intro: a uniform bound on the pointwise deviations bounds the horizontal
deviation, `hDev f g ≤ x`. -/
theorem hDev_le {D V R : Type*} [Add D] [Preorder V] [CompleteLattice R]
    [CoeTC D R] {f g : D → V} {x : R}
    (h : ∀ t, (hDevAt f g t : R) ≤ x) :
    (hDev f g : R) ≤ x :=
  iSup_le h

/-- Elim: an admissible shift bounds the pointwise horizontal deviation,
`hDevAt f g t ≤ d` when `f t ≤ g (t + d)`. -/
theorem hDevAt_le {D V R : Type*} [Add D] [Preorder V] [CompleteLattice R]
    [CoeTC D R] {f g : D → V} {t d : D} (h : f t ≤ g (t + d)) :
    (hDevAt f g t : R) ≤ (d : R) :=
  iInf_le (fun e : {e : D // f t ≤ g (t + e)} => (↑e.1 : R)) ⟨d, h⟩

/-- Lower-bounding the pointwise deviation: when every admissible shift `d`
(`f t ≤ g (t + d)`) satisfies `c ≤ d`, also `c ≤ hDevAt f g t`. -/
theorem le_hDevAt {D V R : Type*} [Add D] [Preorder V] [CompleteLattice R]
    [CoeTC D R] {f g : D → V} {t : D} {c : R}
    (h : ∀ d : D, f t ≤ g (t + d) → c ≤ (d : R)) :
    c ≤ (hDevAt f g t : R) :=
  le_iInf fun d => h d.1 d.2

/-- Intro for a right-added deviation: `x ≤ ↑d + y` over all admissible
shifts `d` gives `x ≤ hDevAt f g t + y`. -/
theorem le_hDevAt_add {D V : Type*} [Add D] [Preorder V] [CoeTC D ℝ≥0∞]
    {f g : D → V} {x y : ℝ≥0∞} {t : D}
    (h : ∀ d : D, f t ≤ g (t + d) → x ≤ (d : ℝ≥0∞) + y) :
    x ≤ (hDevAt f g t : ℝ≥0∞) + y := by
  rw [show (hDevAt f g t : ℝ≥0∞)
        = ⨅ d : {d : D // f t ≤ g (t + d)}, (d.1 : ℝ≥0∞) from rfl,
    ENNReal.iInf_add]
  exact le_iInf fun d => h d.1 d.2

/-- Intro for a left-shifted deviation: `x ≤ ↑(c + d)` over all admissible
shifts `d` gives `x ≤ ↑c + hDevAt f g t`. -/
theorem le_add_hDevAt {V : Type*} [Preorder V] {f g : ℝ≥0 → V}
    {x : ℝ≥0∞} {c t : ℝ≥0}
    (h : ∀ d : ℝ≥0, f t ≤ g (t + d) → x ≤ ((c + d : ℝ≥0) : ℝ≥0∞)) :
    x ≤ (c : ℝ≥0∞) + (hDevAt f g t : ℝ≥0∞) := by
  rw [show (hDevAt f g t : ℝ≥0∞)
        = ⨅ d : {d : ℝ≥0 // f t ≤ g (t + d)}, (d.1 : ℝ≥0∞) from rfl,
    ENNReal.add_iInf]
  exact le_iInf fun d => (h d.1 d.2).trans_eq (ENNReal.coe_add c d.1)

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

/-- Monotony of the vertical deviation at `t`: `f' ≤ f` and `g ≤ g'` give
`vDevAt f' g' t ≤ vDevAt f g t`. -/
theorem vDevAt_mono {D T : Type*} [Preorder T] [AddCommSemigroup T]
    [Sub T] [OrderedSub T] [CovariantClass T T (· + ·) (· ≤ ·)]
    {f f' g g' : D → T} (hf : f' ≤ f) (hg : g ≤ g') (t : D) :
    vDevAt f' g' t ≤ vDevAt f g t :=
  tsub_le_tsub (hf t) (hg t)

/-- Monotony of the vertical deviation: `f' ≤ f` and `g ≤ g'` give
`vDev f' g' ≤ vDev f g`. -/
theorem vDev_mono {D T : Type*} [CompleteLattice T] [AddCommSemigroup T]
    [Sub T] [OrderedSub T] [CovariantClass T T (· + ·) (· ≤ ·)]
    {f f' g g' : D → T} (hf : f' ≤ f) (hg : g ≤ g') :
    vDev f' g' ≤ vDev f g :=
  iSup_le fun t => le_iSup_of_le t (vDevAt_mono hf hg t)

/-- Monotony of the horizontal deviation at `t`: `f' ≤ f` and `g ≤ g'` give
`hDevAt f' g' t ≤ hDevAt f g t` (an admissible shift stays admissible). -/
theorem hDevAt_mono {D V R : Type*} [Add D] [Preorder V] [CompleteLattice R]
    [CoeTC D R] {f f' g g' : D → V} (hf : f' ≤ f) (hg : g ≤ g') (t : D) :
    (hDevAt f' g' t : R) ≤ hDevAt f g t :=
  le_iInf fun d =>
    hDevAt_le (le_trans (hf t) (le_trans d.2 (hg (t + d.1))))

/-- Monotony of the horizontal deviation: `f' ≤ f` and `g ≤ g'` give
`hDev f' g' ≤ hDev f g`. -/
theorem hDev_mono {D V R : Type*} [Add D] [Preorder V] [CompleteLattice R]
    [CoeTC D R] {f f' g g' : D → V} (hf : f' ≤ f) (hg : g ≤ g') :
    (hDev f' g' : R) ≤ hDev f g :=
  iSup_le fun t => le_iSup_of_le t (hDevAt_mono hf hg t)

/-- An `⊓` with the reference function drops from the horizontal deviation:
for monotone `f`, `hDevAt f (f ⊓ g) t = hDevAt f g t` — the `f`-component of
the shift constraint holds automatically. -/
theorem hDevAt_inf_self {V R : Type*} [SemilatticeInf V] [CompleteLattice R]
    [CoeTC ℝ≥0 R] {f g : ℝ≥0 → V} (hmono : Monotone f) (t : ℝ≥0) :
    (hDevAt f (f ⊓ g) t : R) = hDevAt f g t :=
  le_antisymm
    (le_iInf fun d => hDevAt_le (le_inf (hmono le_self_add) d.2))
    (le_iInf fun d => hDevAt_le (le_trans d.2 inf_le_right))

/-- An `⊓` with the reference function drops from the horizontal deviation,
sup form: for monotone `f`, `hDev f (f ⊓ g) = hDev f g`. -/
theorem hDev_inf_self {V R : Type*} [SemilatticeInf V] [CompleteLattice R]
    [CoeTC ℝ≥0 R] {f g : ℝ≥0 → V} (hmono : Monotone f) :
    (hDev f (f ⊓ g) : R) = hDev f g :=
  iSup_congr fun t => hDevAt_inf_self hmono t

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

/-- For non-decreasing `g`, any shift strictly above the pointwise
horizontal deviation is admissible: `hDevAt f g x < d` gives
`f x ≤ g (x + d)`. -/
theorem le_of_hDevAt_lt {V : Type*} [Preorder V] {f g : ℝ≥0 → V}
    (hg : Monotone g) {x d : ℝ≥0}
    (hd : (hDevAt f g x : ℝ≥0∞) < d) :
    f x ≤ g (x + d) := by
  obtain ⟨⟨e, he⟩, hed⟩ := iInf_lt_iff.mp hd
  have hed' : (e : ℝ≥0∞) < (d : ℝ≥0∞) := hed
  exact le_trans he (hg (add_le_add le_rfl (by exact_mod_cast hed'.le)))

/-- For non-decreasing `g`, any shift strictly above the horizontal
deviation is uniformly admissible: `hDev f g < d` gives `f x ≤ g (x + d)`
at every `x`. -/
theorem le_of_hDev_lt {V : Type*} [Preorder V] {f g : ℝ≥0 → V}
    (hg : Monotone g) {d : ℝ≥0}
    (hd : (hDev f g : ℝ≥0∞) < (d : ℝ≥0∞)) (x : ℝ≥0) :
    f x ≤ g (x + d) :=
  le_of_hDevAt_lt hg ((hDevAt_le_hDev f g x).trans_lt hd)

/-! ## Backlog and delay of cumulative curves
For arrival/departure curves `A, D : ℝ≥0 → ℝ≥0`, the **backlog** is the vertical
deviation and the **delay** the horizontal one, both valued in `ℝ≥0∞` via the
coercion `(↑· : ℝ≥0 → ℝ≥0∞)`, so unbounded deviations read `⊤` (not the junk
`ℝ≥0` supremum). -/

namespace Deviation

/-- Backlog of departure `D` behind arrival `A` at `t`: `A t - D t`. -/
def backlogAt (A D : ℝ≥0 → ℝ≥0) (t : ℝ≥0) : ℝ≥0 :=
  vDevAt A D t

/-- Backlog `b(A, D) = ⨆ t, A t - D t`, the vertical deviation, valued in
`ℝ≥0∞` (like `delay`) so an unbounded backlog reads `⊤`. -/
noncomputable def backlog (A D : ℝ≥0 → ℝ≥0) : ℝ≥0∞ :=
  ⨆ t : ℝ≥0, (backlogAt A D t : ℝ≥0∞)

/-- Delay of `D` behind `A` at `t`: least shift `d` with `A t ≤ D (t + d)`. -/
noncomputable def delayAt (A D : ℝ≥0 → ℝ≥0) (t : ℝ≥0) : ℝ≥0∞ :=
  hDevAt A D t

/-- Delay `d(A, D) = ⨆ t, delayAt A D t`, the horizontal deviation. -/
noncomputable def delay (A D : ℝ≥0 → ℝ≥0) : ℝ≥0∞ :=
  hDev A D

/-- `backlogAt A D t = A t - D t`. -/
theorem backlogAt_eq (A D : ℝ≥0 → ℝ≥0) (t : ℝ≥0) :
    backlogAt A D t = A t - D t := rfl

/-- `backlog A D = ⨆ t, ↑(A t - D t)`. -/
theorem backlog_eq_iSup (A D : ℝ≥0 → ℝ≥0) :
    backlog A D = ⨆ t : ℝ≥0, ((A t - D t : ℝ≥0) : ℝ≥0∞) := rfl

/-- `delayAt A D t` is the least shift `d` with `A t ≤ D (t + d)`. -/
theorem delayAt_eq (A D : ℝ≥0 → ℝ≥0) (t : ℝ≥0) :
    delayAt A D t
      = ⨅ d : {d : ℝ≥0 // A t ≤ D (t + d)}, (d.1 : ℝ≥0∞) := rfl

/-- `delay A D = ⨆ t, delayAt A D t`. -/
theorem delay_eq_iSup (A D : ℝ≥0 → ℝ≥0) :
    delay A D = ⨆ t : ℝ≥0, delayAt A D t := rfl

end Deviation

end DeepWiki
