import Book.Servers

/-! # Backlogged periods and start of backlog
The backlogged set `IsBacklogged A D I` (`D < A` on `I`) and the start of the
backlogged period `start A D t` (last `u ≤ t` with `A u = D u`), with its basic
order properties used by strict service-curve theory. -/

namespace DeepWiki

open Set Topology Filter
open scoped Classical NNReal ENNReal

/-- `A`/`D` is backlogged on `I`: `D t < A t` for all `t ∈ I`. -/
def IsBacklogged (A D : Curve) (I : Set ℝ≥0) : Prop :=
  ∀ t ∈ I, D t < A t

/-- start of the backlogged period of `t`: last `u ≤ t` with `A u = D u`. -/
noncomputable def start (A D : Curve) (t : ℝ≥0) : ℝ≥0 :=
  sSup { u | u ≤ t ∧ A u = D u }

/-- The set defining `start` is nonempty (`0` belongs). -/
theorem start_set_nonempty (A D : Curve) (t : ℝ≥0) :
    { u | u ≤ t ∧ A u = D u }.Nonempty :=
  ⟨0, by simp, by
    have hA : A 0 = 0 := A.zero
    have hD : D 0 = 0 := D.zero
    rw [hA, hD]⟩

/-- `start A D t ≤ t`. -/
theorem start_le (A D : Curve) (t : ℝ≥0) :
    start A D t ≤ t :=
  csSup_le (start_set_nonempty A D t) (fun _ hx => hx.1)

/-- `start A D` is monotone in `t`. -/
theorem start_mono (A D : Curve) {t t' : ℝ≥0}
    (h : t ≤ t') : start A D t ≤ start A D t' :=
  csSup_le (start_set_nonempty A D t)
    (fun _ hx =>
      le_csSup ⟨t', fun _ hy => hy.1⟩
        ⟨le_trans hx.1 h, hx.2⟩)

/-- Backlog restricts to subsets of the interval. -/
theorem IsBacklogged.subset {A D : Curve}
    {I I' : Set ℝ≥0} (h : IsBacklogged A D I)
    (hsub : I' ⊆ I) : IsBacklogged A D I' :=
  fun t ht => h t (hsub ht)

/-- When `(t, t']` is backlogged, the start of the period of `t'` lies at or
before `t`: equality points avoid the backlog. -/
theorem start_le_of_isBacklogged (A D : Curve) {t t' : ℝ≥0}
    (hbl : IsBacklogged A D (Set.Ioc t t')) :
    start A D t' ≤ t := by
  refine csSup_le (start_set_nonempty A D t') ?_
  intro u hu
  by_contra hut
  rw [not_le] at hut
  exact absurd hu.2 (ne_of_gt (hbl u ⟨hut, hu.1⟩))

/-- `(start A D t, t]` is a backlogged period when `D ≤ A`. -/
theorem isBacklogged_Ioc_start (A D : Curve)
    (hc : ∀ x, D x ≤ A x) (t : ℝ≥0) :
    IsBacklogged A D (Set.Ioc (start A D t) t) := by
  intro u hu
  have hbdd : BddAbove { u | u ≤ t ∧ A u = D u } :=
    ⟨t, fun x hx => hx.1⟩
  rcases (hc u).lt_or_eq with h | h
  · exact h
  · exact absurd (le_csSup hbdd ⟨hu.2, h.symm⟩)
      (not_le.mpr hu.1)

/-- At the start of a backlogged period, `A = D` (uses left continuity). -/
theorem A_start_eq_D_start (A D : Curve)
    (hc : ∀ x, D x ≤ A x) (t : ℝ≥0) :
    A (start A D t) = D (start A D t) := by
  set s := start A D t with hs
  rcases (hc s).lt_or_eq with hlt | heq
  · exfalso
    have hbdd : BddAbove { u | u ≤ t ∧ A u = D u } :=
      ⟨t, fun x hx => hx.1⟩
    have hs0 : 0 < s := by
      rcases eq_zero_or_pos s with h | h
      · have hA : A 0 = 0 := A.zero
        have hD : D 0 = 0 := D.zero
        rw [h, hA, hD] at hlt
        exact absurd hlt (lt_irrefl 0)
      · exact h
    have hev : ∀ᶠ u in 𝓝[<] s, D u < A u :=
      (D.leftCont s).eventually_lt (A.leftCont s) hlt
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
      (csSup_le (start_set_nonempty A D t) hub)
      (not_le.mpr hls)
  · exact heq.symm

/-- Age of the backlogged period at `t`: the time since the last equality
point, `t - start A D t`. -/
noncomputable def backloggedAgeAt (A D : Curve) (t : ℝ≥0) : ℝ≥0 :=
  t - start A D t

/-- Maximal length of a backlogged period: `⨆ t, backloggedAgeAt A D t`,
valued in `ℝ≥0∞` (unbounded periods read `⊤`). -/
noncomputable def maxBackloggedLength (A D : Curve) : ℝ≥0∞ :=
  ⨆ t : ℝ≥0, (backloggedAgeAt A D t : ℝ≥0∞)

/-- Every backlogged period's length is dominated by the maximal one: on a
backlogged `(t, t + d]` the start of the period of `t + d` lies at or
before `t`, so the age at `t + d` is at least `d`. -/
theorem le_maxBackloggedLength_of_isBacklogged (A D : Curve) {t d : ℝ≥0}
    (hbl : IsBacklogged A D (Set.Ioc t (t + d))) :
    (d : ℝ≥0∞) ≤ maxBackloggedLength A D := by
  refine le_trans ?_
    (le_iSup (fun u => ((backloggedAgeAt A D u : ℝ≥0) : ℝ≥0∞)) (t + d))
  have hage : d ≤ backloggedAgeAt A D (t + d) := by
    calc d = (t + d) - t := (add_tsub_cancel_left t d).symm
      _ ≤ (t + d) - start A D (t + d) :=
        tsub_le_tsub_left (start_le_of_isBacklogged A D hbl) _
  exact_mod_cast hage

/-- `start` is constant across an order-connected backlogged set. -/
theorem start_const_of_backlogged (A D : Curve)
    (hc : ∀ x, D x ≤ A x)
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
    rw [A_start_eq_D_start A D hc t'] at this
    exact absurd this (lt_irrefl _)
  exact le_csSup ⟨t, fun y hy => hy.1⟩
    ⟨hst, A_start_eq_D_start A D hc t'⟩

end DeepWiki
