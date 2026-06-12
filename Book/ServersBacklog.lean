import Book.Servers
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
  ⟨0, zero_le', h0⟩

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
  · refine csSup_le ⟨0, zero_le', h0⟩ fun v hv => ?_
    exact le_csSup hbt ⟨hv.1.trans hwt, hv.2⟩
  · refine csSup_le ⟨0, zero_le', h0⟩ fun v hv => ?_
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
      exact ⟨zero_le', h0⟩
    · exact h
  have hbot : 𝓝[<] s ≠ ⊥ := (nhdsLT_neBot_of_exists_lt ⟨0, hs0⟩).ne
  rw [hAmono.leftLim_eq_sSup hbot, hDmono.leftLim_eq_sSup hbot]
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

end DeepWiki
