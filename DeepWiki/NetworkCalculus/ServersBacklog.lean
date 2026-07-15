import DeepWiki.NetworkCalculus.Servers
import Mathlib.Topology.Order.LeftRightLim

/-! # Backlogged periods and start of backlog
The backlogged set `IsBacklogged A D I` (`D < A` on `I`) and the start of
the backlogged period `start A D t` (last `u ≤ t` with `A u = D u`), stated
for plain cumulative functions so both continuity conventions are covered:
at the start, `A = D` for left-continuous pairs (`apply_start_eq`), and
whenever the values disagree — as happens under the right-continuous
convention — the left limits agree instead (`leftLim_start_eq_of_ne`). -/

namespace DeepWiki

open Function Set Topology Filter
open scoped Classical NNReal ENNReal

/-- `A`/`D` is backlogged on `I`: `D t < A t` for all `t ∈ I`. -/
def IsBacklogged (A D : ℝ≥0 → ℝ≥0) (I : Set ℝ≥0) : Prop :=
  ∀ t ∈ I, D t < A t

/-- start of the backlogged period of `t`: last `u ≤ t` with `A u = D u`. -/
noncomputable def start (A D : ℝ≥0 → ℝ≥0) (t : ℝ≥0) : ℝ≥0 :=
  sSup { u | u ≤ t ∧ A u = D u }

/-- Two curves agree at the origin: `A 0 = D 0` (both vanish). -/
theorem Curve.zero_eq (A D : Curve) : A 0 = D 0 := by
  have hA : A 0 = 0 := A.zero
  have hD : D 0 = 0 := D.zero
  rw [hA, hD]

/-- The set defining `start` is nonempty (`0` belongs when `A 0 = D 0`). -/
theorem start_set_nonempty {A D : ℝ≥0 → ℝ≥0} (h0 : A 0 = D 0) (t : ℝ≥0) :
    { u | u ≤ t ∧ A u = D u }.Nonempty :=
  ⟨0, zero_le, h0⟩

/-- `start A D t ≤ t` (`sSup ∅ = 0` covers an empty equality set). -/
theorem start_le (A D : ℝ≥0 → ℝ≥0) (t : ℝ≥0) :
    start A D t ≤ t :=
  csSup_le' (fun _ hx => hx.1)

/-- The start is constant across its own backlogged window: for
`start A D t ≤ w ≤ t` the equality points below `w` and below `t`
coincide. -/
theorem start_eq_start_of_le {A D : ℝ≥0 → ℝ≥0} (h0 : A 0 = D 0)
    {w t : ℝ≥0} (hsw : start A D t ≤ w) (hwt : w ≤ t) :
    start A D w = start A D t := by
  have hbt : BddAbove { u | u ≤ t ∧ A u = D u } :=
    ⟨t, fun x hx => hx.1⟩
  have hbw : BddAbove { u | u ≤ w ∧ A u = D u } :=
    ⟨w, fun x hx => hx.1⟩
  refine le_antisymm ?_ ?_
  · refine csSup_le ⟨0, zero_le, h0⟩ fun v hv => ?_
    exact le_csSup hbt ⟨hv.1.trans hwt, hv.2⟩
  · refine csSup_le ⟨0, zero_le, h0⟩ fun v hv => ?_
    have hvw : v ≤ w := le_trans (le_csSup hbt hv) hsw
    exact le_csSup hbw ⟨hvw, hv.2⟩

/-- Against itself every instant is an equality point: `start A A t = t`. -/
theorem start_self (A : ℝ≥0 → ℝ≥0) (t : ℝ≥0) : start A A t = t := by
  unfold start
  simp only [and_true]
  exact csSup_Iic

/-- An equality point at `t` itself anchors the start at `t`. -/
theorem start_eq_of_apply_eq {A D : ℝ≥0 → ℝ≥0} {t : ℝ≥0}
    (h : A t = D t) : start A D t = t :=
  le_antisymm (start_le A D t)
    (le_csSup ⟨t, fun _ hx => hx.1⟩ ⟨le_rfl, h⟩)

/-- `start A D` is monotone in `t`. -/
theorem start_mono (A D : ℝ≥0 → ℝ≥0) {t t' : ℝ≥0}
    (h : t ≤ t') : start A D t ≤ start A D t' :=
  csSup_le'
    (fun _ hx =>
      le_csSup ⟨t', fun _ hy => hy.1⟩
        ⟨le_trans hx.1 h, hx.2⟩)

/-- Backlog restricts to subsets of the interval. -/
theorem IsBacklogged.subset {A D : ℝ≥0 → ℝ≥0}
    {I I' : Set ℝ≥0} (h : IsBacklogged A D I)
    (hsub : I' ⊆ I) : IsBacklogged A D I' :=
  fun t ht => h t (hsub ht)

/-- Backlog over a union of intervals: both parts backlogged. -/
theorem IsBacklogged.union {A D : ℝ≥0 → ℝ≥0} {I I' : Set ℝ≥0}
    (h : IsBacklogged A D I) (h' : IsBacklogged A D I') :
    IsBacklogged A D (I ∪ I') :=
  fun u hu => hu.elim (h u) (h' u)

/-- When `(t, t']` is backlogged, the start of the period of `t'` lies at or
before `t`: equality points avoid the backlog. -/
theorem start_le_of_isBacklogged {A D : ℝ≥0 → ℝ≥0}
    {t t' : ℝ≥0} (hbl : IsBacklogged A D (Set.Ioc t t')) :
    start A D t' ≤ t := by
  refine csSup_le' ?_
  intro u hu
  by_contra hut
  rw [not_le] at hut
  exact absurd hu.2 (ne_of_gt (hbl u ⟨hut, hu.1⟩))

/-- `(start A D t, t]` is a backlogged period when `D ≤ A`. -/
theorem isBacklogged_Ioc_start {A D : ℝ≥0 → ℝ≥0}
    (hc : ∀ x, D x ≤ A x) (t : ℝ≥0) :
    IsBacklogged A D (Set.Ioc (start A D t) t) := by
  intro u hu
  have hbdd : BddAbove { u | u ≤ t ∧ A u = D u } :=
    ⟨t, fun x hx => hx.1⟩
  rcases (hc u).lt_or_eq with h | h
  · exact h
  · exact absurd (le_csSup hbdd ⟨hu.2, h.symm⟩)
      (not_le.mpr hu.1)

/-- At the start of a backlogged period, `A = D`: the value relation of the
left-continuous convention. -/
theorem apply_start_eq {A D : ℝ≥0 → ℝ≥0}
    (hAlc : IsLeftContinuous A) (hDlc : IsLeftContinuous D)
    (h0 : A 0 = D 0) (hc : ∀ x, D x ≤ A x) (t : ℝ≥0) :
    A (start A D t) = D (start A D t) := by
  set s := start A D t with hs
  rcases (hc s).lt_or_eq with hlt | heq
  · exfalso
    have hbdd : BddAbove { u | u ≤ t ∧ A u = D u } :=
      ⟨t, fun x hx => hx.1⟩
    have hs0 : 0 < s := by
      rcases eq_zero_or_pos s with h | h
      · rw [h, h0] at hlt
        exact absurd hlt (lt_irrefl _)
      · exact h
    have hev : ∀ᶠ u in 𝓝[<] s, D u < A u :=
      (hDlc s).eventually_lt (hAlc s) hlt
    have hbasis :
        (𝓝[<] s).HasBasis (· < s) (Ioo · s) :=
      nhdsLT_basis_of_exists_lt ⟨0, hs0⟩
    rw [hbasis.eventually_iff] at hev
    obtain ⟨l, hls, hl⟩ := hev
    have hub : ∀ x ∈ { u | u ≤ t ∧ A u = D u },
        x ≤ l := by
      intro x hx
      by_contra hxl
      rw [not_le] at hxl
      rcases (le_csSup hbdd hx).lt_or_eq with hxlt | hxeq
      · have := hl ⟨hxl, hxlt⟩
        rw [hx.2] at this; exact absurd this (lt_irrefl _)
      · -- x = sSup = s with A x = D x, vs D s < A s
        subst hxeq
        exact absurd hx.2 (ne_of_gt hlt)
    exact absurd
      (csSup_le (start_set_nonempty h0 t) hub)
      (not_le.mpr hls)
  · exact heq.symm

/-- At the start of a backlogged period of a `Curve` pair, `A = D` (curves
are left-continuous; stated in the `⇑` spelling for rewriting). -/
theorem Curve.apply_start_eq (A D : Curve) (hc : ∀ x, D x ≤ A x)
    (t : ℝ≥0) :
    A (start ⇑A ⇑D t) = D (start ⇑A ⇑D t) :=
  DeepWiki.apply_start_eq A.leftCont D.leftCont (A.zero_eq D) hc t

/-- When the values at the start disagree, the left limits agree:
`A (start−) = D (start−)`. Under the right-continuous convention the value
relation `A (start) = D (start)` can fail (a burst arrival exactly at the
start); the equality points then accumulate at the start from below, and
the left limits coincide — no continuity hypothesis is needed. -/
theorem leftLim_start_eq_of_ne {A D : ℝ≥0 → ℝ≥0}
    (hAmono : Monotone A) (hDmono : Monotone D)
    (h0 : A 0 = D 0) (hc : ∀ x, D x ≤ A x) {t : ℝ≥0}
    (hne : A (start A D t) ≠ D (start A D t)) :
    leftLim A (start A D t) = leftLim D (start A D t) := by
  have hsup : start A D t = sSup { u | u ≤ t ∧ A u = D u } := rfl
  set s := start A D t with hs
  have hsE : s ∉ { u | u ≤ t ∧ A u = D u } := fun hmem => hne hmem.2
  have hbdd : BddAbove { u | u ≤ t ∧ A u = D u } :=
    ⟨t, fun x hx => hx.1⟩
  have hs0 : 0 < s := by
    rcases eq_zero_or_pos s with h | h
    · refine absurd ?_ hsE
      rw [h]
      exact ⟨zero_le, h0⟩
    · exact h
  letI : (𝓝[<] s).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hs0⟩
  rw [hAmono.leftLim_eq_sSup, hDmono.leftLim_eq_sSup]
  apply le_antisymm
  · -- each `A y`, `y < s`, sits below `D u` at an equality point `y < u < s`
    refine csSup_le ((show (Iio s).Nonempty from ⟨0, hs0⟩).image A) ?_
    rintro x ⟨y, (hy : y < s), rfl⟩
    obtain ⟨u, huE, hyu⟩ :=
      exists_lt_of_lt_csSup (start_set_nonempty h0 t) (hsup ▸ hy)
    have hus : u < s :=
      lt_of_le_of_ne (hsup ▸ le_csSup hbdd huE) (fun h => hsE (h ▸ huE))
    calc A y ≤ A u := hAmono hyu.le
      _ = D u := huE.2
      _ ≤ sSup (D '' Iio s) :=
          le_csSup (hDmono.map_bddAbove bddAbove_Iio) ⟨u, hus, rfl⟩
  · -- `D ≤ A` pointwise below `s`
    refine csSup_le ((show (Iio s).Nonempty from ⟨0, hs0⟩).image D) ?_
    rintro x ⟨y, (hy : y < s), rfl⟩
    exact le_trans (hc y)
      (le_csSup (hAmono.map_bddAbove bddAbove_Iio) ⟨y, hy, rfl⟩)

/-- At the start of a backlogged period, the values agree or the left
limits agree — the convention-independent start relation. -/
theorem apply_start_eq_or_leftLim_start_eq {A D : ℝ≥0 → ℝ≥0}
    (hAmono : Monotone A) (hDmono : Monotone D)
    (h0 : A 0 = D 0) (hc : ∀ x, D x ≤ A x) (t : ℝ≥0) :
    A (start A D t) = D (start A D t) ∨
      leftLim A (start A D t) = leftLim D (start A D t) := by
  rcases eq_or_ne (A (start A D t)) (D (start A D t)) with h | h
  · exact Or.inl h
  · exact Or.inr (leftLim_start_eq_of_ne hAmono hDmono h0 hc h)

/-- Age of the backlogged period at `t`: the time since the last equality
point, `t - start A D t`. -/
noncomputable def backloggedAgeAt (A D : ℝ≥0 → ℝ≥0) (t : ℝ≥0) : ℝ≥0 :=
  t - start A D t

/-- Maximal length of a backlogged period: `⨆ t, backloggedAgeAt A D t`,
valued in `ℝ≥0∞` (unbounded periods read `⊤`). -/
noncomputable def maxBackloggedLength (A D : ℝ≥0 → ℝ≥0) : ℝ≥0∞ :=
  ⨆ t : ℝ≥0, (backloggedAgeAt A D t : ℝ≥0∞)

/-- Every backlogged period's length is dominated by the maximal one: on a
backlogged `(t, t + d]` the start of the period of `t + d` lies at or
before `t`, so the age at `t + d` is at least `d`. -/
theorem le_maxBackloggedLength_of_isBacklogged {A D : ℝ≥0 → ℝ≥0}
    {t d : ℝ≥0}
    (hbl : IsBacklogged A D (Set.Ioc t (t + d))) :
    (d : ℝ≥0∞) ≤ maxBackloggedLength A D := by
  refine le_trans ?_
    (le_iSup (fun u => ((backloggedAgeAt A D u : ℝ≥0) : ℝ≥0∞)) (t + d))
  have hage : d ≤ backloggedAgeAt A D (t + d) := by
    calc d = (t + d) - t := (add_tsub_cancel_left t d).symm
      _ ≤ (t + d) - start A D (t + d) :=
        tsub_le_tsub_left (start_le_of_isBacklogged hbl) _
  exact_mod_cast hage

/-- `start` is constant across an order-connected backlogged set. -/
theorem start_const_of_backlogged {A D : ℝ≥0 → ℝ≥0}
    (hAlc : IsLeftContinuous A) (hDlc : IsLeftContinuous D)
    (h0 : A 0 = D 0) (hc : ∀ x, D x ≤ A x)
    {I : Set ℝ≥0} (hI : IsBacklogged A D I)
    (hoc : I.OrdConnected)
    {t t' : ℝ≥0} (ht : t ∈ I) (ht' : t' ∈ I) :
    start A D t = start A D t' := by
  wlog hle : t ≤ t' generalizing t t'
  · exact (this ht' ht (not_le.mp hle).le).symm
  refine le_antisymm (start_mono A D hle) ?_
  have hst : start A D t' ≤ t := by
    by_contra h
    rw [not_le] at h
    have hmem : start A D t' ∈ I :=
      hoc.out ht ht' ⟨h.le, start_le A D t'⟩
    have := hI _ hmem
    rw [apply_start_eq hAlc hDlc h0 hc t'] at this
    exact absurd this (lt_irrefl _)
  exact le_csSup ⟨t, fun y hy => hy.1⟩
    ⟨hst, apply_start_eq hAlc hDlc h0 hc t'⟩

/-! ## Book restatement (start of backlog under either convention)
With left-continuous cumulative functions, `A (Start t) = D (Start t)`.
With right-continuous cumulative functions the value relation can fail and
is replaced by the left-limit relation `A (Start t −) = D (Start t −)` —
formalized sharply: the replacement is needed exactly when the values
disagree, and there it holds with no continuity hypothesis at all (the
right-continuity context binders are unused). The two cases combine into
the convention-independent disjunction. -/
example (A D : Curve) (hc : ∀ x, D x ≤ A x) (t : ℝ≥0) :
    A (start ⇑A ⇑D t) = D (start ⇑A ⇑D t) :=
  A.apply_start_eq D hc t

example {A D : ℝ≥0 → ℝ≥0} (hAmono : Monotone A) (hDmono : Monotone D)
    (_hArc : IsRightContinuous A) (_hDrc : IsRightContinuous D)
    (h0 : A 0 = D 0) (hc : ∀ x, D x ≤ A x) {t : ℝ≥0}
    (hne : A (start A D t) ≠ D (start A D t)) :
    leftLim A (start A D t) = leftLim D (start A D t) :=
  leftLim_start_eq_of_ne hAmono hDmono h0 hc hne

example {A D : ℝ≥0 → ℝ≥0} (hAmono : Monotone A) (hDmono : Monotone D)
    (h0 : A 0 = D 0) (hc : ∀ x, D x ≤ A x) (t : ℝ≥0) :
    A (start A D t) = D (start A D t) ∨
      leftLim A (start A D t) = leftLim D (start A D t) :=
  apply_start_eq_or_leftLim_start_eq hAmono hDmono h0 hc t

/-- `sSup (Iio a) = a` on `ℝ≥0` for positive `a`: density supplies
approximants despite the bottom element. -/
theorem csSup_Iio_of_pos {a : ℝ≥0} (ha : 0 < a) :
    sSup (Set.Iio a) = a := by
  refine le_antisymm
    (csSup_le ⟨0, Set.mem_Iio.mpr ha⟩ fun x hx => le_of_lt hx) ?_
  refine (le_csSup_iff ⟨a, fun x hx => le_of_lt hx⟩
    ⟨0, Set.mem_Iio.mpr ha⟩).mpr ?_
  intro b hb
  by_contra hb1
  rw [not_le] at hb1
  obtain ⟨c, hbc, hc1⟩ := exists_between hb1
  exact absurd (hb (Set.mem_Iio.mpr hc1)) (not_le.mpr hbc)

/-- The step output `1_{[1,∞)}` is monotone. -/
private theorem stepOut_mono :
    Monotone (fun y : ℝ≥0 => if y < 1 then (0 : ℝ≥0) else 1) := by
  intro a b hab
  show (if a < 1 then (0 : ℝ≥0) else 1) ≤ if b < 1 then 0 else 1
  by_cases ha : a < 1
  · rw [if_pos ha]
    exact zero_le
  · rw [if_neg ha, if_neg fun hb => ha (lt_of_le_of_lt hab hb)]

/-- The step output `1_{[1,∞)}` is right-continuous. -/
private theorem stepOut_rightCont :
    IsRightContinuous (fun y : ℝ≥0 => if y < 1 then (0 : ℝ≥0) else 1) := by
  intro t
  rcases lt_or_ge t 1 with ht | ht
  · refine continuousWithinAt_const.congr_of_eventuallyEq ?_ (if_pos ht)
    filter_upwards [Ioo_mem_nhdsGT ht] with v hv
    exact if_pos hv.2
  · refine continuousWithinAt_const.congr_of_eventuallyEq ?_
      (if_neg (not_lt.mpr ht))
    filter_upwards [self_mem_nhdsWithin] with v (hv : t < v)
    exact if_neg (not_lt.mpr (le_trans ht (le_of_lt hv)))

/-- The step's left image below `1` is `{0}`. -/
private theorem stepOut_image_Iio :
    (fun y : ℝ≥0 => if y < 1 then (0 : ℝ≥0) else 1) '' Set.Iio 1
      = {0} := by
  refine Set.eq_singleton_iff_unique_mem.mpr
    ⟨⟨0, Set.mem_Iio.mpr zero_lt_one, if_pos zero_lt_one⟩, ?_⟩
  rintro x ⟨y, hy, rfl⟩
  exact if_pos hy

/-- **The left-limit side of the start disjunction is sharp**: a
right-continuous departure burst exactly at an attained start makes
the values agree while the left limits differ — the blanket
left-limit replacement is false. Witness: identity arrivals against
the step output `1_{[1,∞)}`; the start of the period of `2` is
attained at `1` with both values `1` and `(1, 2]` backlogged, yet
`A(1−) = 1 ≠ 0 = D(1−)`. -/
theorem exists_rightContinuous_apply_start_eq_not_leftLim_start_eq :
    ∃ A D : ℝ≥0 → ℝ≥0, Monotone A ∧ Monotone D
      ∧ IsRightContinuous A ∧ IsRightContinuous D
      ∧ A 0 = D 0 ∧ (∀ x, D x ≤ A x)
      ∧ start A D 2 = 1
      ∧ A (start A D 2) = D (start A D 2)
      ∧ IsBacklogged A D (Set.Ioc 1 2)
      ∧ leftLim A (start A D 2) ≠ leftLim D (start A D 2) := by
  have hstart : start id (fun y : ℝ≥0 => if y < 1 then (0 : ℝ≥0) else 1) 2
      = 1 := by
    refine le_antisymm (csSup_le ⟨0, zero_le, ?_⟩ fun u hu => ?_) ?_
    · show (0 : ℝ≥0) = if (0 : ℝ≥0) < 1 then 0 else 1
      rw [if_pos zero_lt_one]
    · by_contra h1u
      rw [not_le] at h1u
      have heq : u = if u < 1 then (0 : ℝ≥0) else 1 := hu.2
      rw [if_neg (not_lt.mpr h1u.le)] at heq
      exact absurd heq.symm (ne_of_lt h1u)
    · refine le_csSup ⟨2, fun x hx => hx.1⟩ ⟨one_le_two, ?_⟩
      show (1 : ℝ≥0) = if (1 : ℝ≥0) < 1 then 0 else 1
      rw [if_neg (lt_irrefl 1)]
  refine ⟨id, fun y => if y < 1 then (0 : ℝ≥0) else 1, monotone_id,
    stepOut_mono, isRightContinuous_of_continuous _ continuous_id,
    stepOut_rightCont, ?_, ?_, hstart, ?_, ?_, ?_⟩
  · show (0 : ℝ≥0) = if (0 : ℝ≥0) < 1 then 0 else 1
    rw [if_pos zero_lt_one]
  · intro x
    show (if x < 1 then (0 : ℝ≥0) else 1) ≤ id x
    by_cases hx : x < 1
    · rw [if_pos hx]
      exact zero_le
    · rw [if_neg hx]
      exact not_lt.mp hx
  · rw [hstart]
    show (1 : ℝ≥0) = if (1 : ℝ≥0) < 1 then 0 else 1
    rw [if_neg (lt_irrefl 1)]
  · intro u hu
    show (if u < 1 then (0 : ℝ≥0) else 1) < id u
    rw [if_neg (not_lt.mpr (le_of_lt hu.1))]
    exact hu.1
  · rw [hstart]
    letI : (𝓝[<] (1 : ℝ≥0)).NeBot :=
      nhdsLT_neBot_of_exists_lt ⟨0, zero_lt_one⟩
    rw [monotone_id.leftLim_eq_sSup,
      stepOut_mono.leftLim_eq_sSup, Set.image_id,
      stepOut_image_Iio, csSup_singleton, csSup_Iio_of_pos zero_lt_one]
    exact one_ne_zero

/-- **The value side of the start disjunction is sharp**: a
right-continuous arrival burst exactly at an unattained start makes
the values disagree (the left limits then agree, per the
disjunction). Witness: the step arrivals `1_{[1,∞)}` against the
zero output; the equality points of the period of `2` accumulate at
`1` without reaching it, `A(1) = 1 ≠ 0 = D(1)`. -/
theorem exists_rightContinuous_not_apply_start_eq :
    ∃ A D : ℝ≥0 → ℝ≥0, Monotone A ∧ Monotone D
      ∧ IsRightContinuous A ∧ IsRightContinuous D
      ∧ A 0 = D 0 ∧ (∀ x, D x ≤ A x)
      ∧ start A D 2 = 1
      ∧ A (start A D 2) ≠ D (start A D 2)
      ∧ IsBacklogged A D (Set.Ioc 1 2)
      ∧ leftLim A (start A D 2) = leftLim D (start A D 2) := by
  have hstart : start (fun y : ℝ≥0 => if y < 1 then (0 : ℝ≥0) else 1)
      (fun _ : ℝ≥0 => 0) 2 = 1 := by
    have hset : { u : ℝ≥0 | u ≤ 2
        ∧ (if u < 1 then (0 : ℝ≥0) else 1) = 0 } = Set.Iio 1 := by
      ext u
      constructor
      · rintro ⟨hu2, hueq⟩
        by_contra h1u
        rw [Set.mem_Iio, not_lt] at h1u
        rw [if_neg (not_lt.mpr h1u)] at hueq
        exact one_ne_zero hueq
      · intro hu
        exact ⟨le_trans (le_of_lt hu) one_le_two, if_pos hu⟩
    show sSup { u : ℝ≥0 | u ≤ 2
        ∧ (if u < 1 then (0 : ℝ≥0) else 1) = 0 } = 1
    rw [hset, csSup_Iio_of_pos zero_lt_one]
  refine ⟨fun y => if y < 1 then (0 : ℝ≥0) else 1, fun _ => 0,
    stepOut_mono, monotone_const, stepOut_rightCont,
    isRightContinuous_of_continuous _ continuous_const, ?_, ?_,
    hstart, ?_, ?_, ?_⟩
  · show (if (0 : ℝ≥0) < 1 then (0 : ℝ≥0) else 1) = 0
    rw [if_pos zero_lt_one]
  · intro x
    exact zero_le
  · rw [hstart]
    show (if (1 : ℝ≥0) < 1 then (0 : ℝ≥0) else 1) ≠ 0
    rw [if_neg (lt_irrefl 1)]
    exact one_ne_zero
  · intro u hu
    show (0 : ℝ≥0) < if u < 1 then (0 : ℝ≥0) else 1
    rw [if_neg (not_lt.mpr (le_of_lt hu.1))]
    exact zero_lt_one
  · rw [hstart]
    letI : (𝓝[<] (1 : ℝ≥0)).NeBot :=
      nhdsLT_neBot_of_exists_lt ⟨0, zero_lt_one⟩
    have himg : (fun _ : ℝ≥0 => (0 : ℝ≥0)) '' Set.Iio 1 = {0} :=
      Set.Nonempty.image_const ⟨0, Set.mem_Iio.mpr zero_lt_one⟩ 0
    rw [stepOut_mono.leftLim_eq_sSup,
      monotone_const.leftLim_eq_sSup, stepOut_image_Iio, himg]

end DeepWiki
