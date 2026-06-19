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

/-! ## The RTC greedy processor and the variable-capacity node (Thm 9.2 framework) -/

/-- **The RTC greedy-processor equations [9.4]–[9.6]** for bivariate arrival `A`,
service `C`, departure `D`, residual `C'` and (univariate) backlog `b`:
`D = C − C'`, `C' s t = (⨆_{s≤u≤t} (C s u − A s u − b s)) ⊔ 0`, and
`b t − b s = A s t − D s t`. -/
def IsRtcGreedy (A C D C' : ℝ≥0 → ℝ≥0 → ℝ) (b : ℝ≥0 → ℝ) : Prop :=
  (∀ s t, s ≤ t → D s t = C s t - C' s t) ∧
  (∀ s t, s ≤ t → C' s t
      = (⨆ u : {u : ℝ≥0 // s ≤ u ∧ u ≤ t}, (C s u.1 - A s u.1 - b s)) ⊔ 0) ∧
  (∀ s t, s ≤ t → b t - b s = A s t - D s t)

/-- **The variable-capacity node equations [9.7]–[9.9]** for univariate cumulative
functions `A, C, D, C'` (the readings `Â, Ĉ, D̂, Ĉ'`) and backlog `b`:
`D t = ⨅_{u≤t} (C t − C u + A u)` (the variable-capacity output), `C' = C − D`
(residual service), and `b = A − D` (backlog). -/
def IsVarCapacityEqns (A C D C' b : ℝ≥0 → ℝ) : Prop :=
  (∀ t, D t = ⨅ u : {u : ℝ≥0 // u ≤ t}, (C t - C u.1 + A u.1)) ∧
  (∀ t, C' t = C t - D t) ∧
  (∀ t, b t = A t - D t)

/-- **Theorem 9.2** (RTC→NC, residual half [9.8]): the univariate reading of the
RTC residual `C'` is the variable-capacity residual `Ĉ' = Ĉ − D̂`, directly from
equation [9.4] at `s = 0`. -/
theorem eq_residual_of_isRtcGreedy {A C D C' : ℝ≥0 → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}
    (hg : IsRtcGreedy A C D C' b) (t : ℝ≥0) :
    C' 0 t = C 0 t - D 0 t := by
  have := hg.1 0 t zero_le; linarith

/-- **Theorem 9.2** (RTC→NC, backlog half [9.9]): with `b 0 = 0`, the backlog is
the univariate gap `b = Â − D̂`, directly from equation [9.6] at `s = 0`. -/
theorem eq_backlog_of_isRtcGreedy {A C D C' : ℝ≥0 → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}
    (hg : IsRtcGreedy A C D C' b) (hb0 : b 0 = 0) (t : ℝ≥0) :
    b t = A 0 t - D 0 t := by
  have := hg.2.2 0 t zero_le; rw [hb0] at this; linarith

/-- A constant minus a bounded supremum is the infimum of the constant minus each
term (the antitone map `x ↦ c − x` turns `⨆` into `⨅`), over `ℝ`. -/
theorem real_sub_ciSup {ι : Type*} [Nonempty ι] (c : ℝ) (g : ι → ℝ)
    (hbdd : BddAbove (Set.range g)) :
    c - ⨆ i, g i = ⨅ i, (c - g i) := by
  have hbb : BddBelow (Set.range fun i => c - g i) := by
    obtain ⟨M, hM⟩ := hbdd
    exact ⟨c - M, by rintro _ ⟨i, rfl⟩; exact sub_le_sub_left (hM ⟨i, rfl⟩) c⟩
  refine le_antisymm (le_ciInf fun i => sub_le_sub_left (le_ciSup hbdd i) c) ?_
  rw [le_sub_comm]
  refine ciSup_le fun i => ?_
  rw [le_sub_comm]
  exact ciInf_le hbb i

/-- **Theorem 9.2** (RTC→NC, forward direction): the univariate readings of an RTC
greedy processor (Chasles, `b 0 = 0`, with the residual sets bounded above) satisfy
the variable-capacity node equations [9.7]–[9.9]. The output half [9.7] is the
`⨆`-to-`⨅` step (`real_sub_ciSup`) after absorbing the `⊔ 0` (the `u = 0` split
contributes `0`). -/
theorem isVarCapacityEqns_of_isRtcGreedy
    {A C D C' : ℝ≥0 → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}
    (hA : IsChasles A) (hC : IsChasles C) (hb0 : b 0 = 0) (hg : IsRtcGreedy A C D C' b)
    (hbdd : ∀ t : ℝ≥0,
      BddAbove (Set.range fun u : {u : ℝ≥0 // u ≤ t} => C 0 u.1 - A 0 u.1)) :
    IsVarCapacityEqns (fun t => A 0 t) (fun t => C 0 t) (fun t => D 0 t)
      (fun t => C' 0 t) b := by
  refine ⟨fun t => ?_, fun t => eq_residual_of_isRtcGreedy hg t,
    fun t => eq_backlog_of_isRtcGreedy hg hb0 t⟩
  haveI : Nonempty {u : ℝ≥0 // u ≤ t} := ⟨⟨t, le_rfl⟩⟩
  have hC00 : C 0 0 = 0 := by have := hC 0 0 0 le_rfl le_rfl; linarith
  have hA00 : A 0 0 = 0 := by have := hA 0 0 0 le_rfl le_rfl; linarith
  have hequiv : (⨆ u : {u : ℝ≥0 // 0 ≤ u ∧ u ≤ t}, (C 0 u.1 - A 0 u.1 - b 0))
      = ⨆ u : {u : ℝ≥0 // u ≤ t}, (C 0 u.1 - A 0 u.1) := by
    rw [hb0]
    exact Equiv.iSup_congr
      (Equiv.subtypeEquivRight fun u => ⟨And.right, fun h => ⟨zero_le, h⟩⟩) (fun u => by simp)
  have hg0mem : (0 : ℝ) ≤ ⨆ u : {u : ℝ≥0 // u ≤ t}, (C 0 u.1 - A 0 u.1) :=
    le_ciSup_of_le (hbdd t) ⟨0, zero_le⟩ (by simp [hC00, hA00])
  have hC' : C' 0 t = ⨆ u : {u : ℝ≥0 // u ≤ t}, (C 0 u.1 - A 0 u.1) := by
    rw [hg.2.1 0 t zero_le, hequiv, sup_eq_left.mpr hg0mem]
  show D 0 t = ⨅ u : {u : ℝ≥0 // u ≤ t}, (C 0 t - C 0 u.1 + A 0 u.1)
  rw [hg.1 0 t zero_le, hC', real_sub_ciSup (C 0 t) _ (hbdd t)]
  exact iInf_congr fun u => by ring

/-- A bounded supremum minus a constant is the supremum of each term minus the
constant (the monotone map `x ↦ x − c` commutes with `⨆`), over `ℝ`. -/
theorem real_ciSup_sub {ι : Type*} [Nonempty ι] (g : ι → ℝ) (c : ℝ)
    (hbdd : BddAbove (Set.range g)) :
    (⨆ i, g i) - c = ⨆ i, (g i - c) := by
  have hbb : BddAbove (Set.range fun i => g i - c) := by
    obtain ⟨M, hM⟩ := hbdd
    exact ⟨M - c, by rintro _ ⟨i, rfl⟩; exact sub_le_sub_right (hM ⟨i, rfl⟩) c⟩
  refine le_antisymm ?_ (ciSup_le fun i => sub_le_sub_right (le_ciSup hbdd i) c)
  rw [sub_le_iff_le_add]
  refine ciSup_le fun i => ?_
  rw [← sub_le_iff_le_add]
  exact le_ciSup hbb i

/-- **Theorem 9.2** (NC→RTC, reverse direction): if the univariate readings of
Chasles bivariate functions (with `b 0 = 0` and the residual sets bounded above)
satisfy the variable-capacity node equations [9.7]–[9.9], then the bivariate
functions satisfy the RTC greedy-processor equations [9.4]–[9.6]. The residual
[9.5] is the delicate half: the `[0,t]` supremum splits as
`⨆_{[0,t]} = ⨆_{[0,s]} ⊔ ⨆_{[s,t]}`, and `(a ⊔ b) − c` distributes. (Unlike the
forward direction, `b 0 = 0` is not needed — the node equations already pin `b`.) -/
theorem isRtcGreedy_of_isVarCapacityEqns
    {A C D C' : ℝ≥0 → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}
    (hA : IsChasles A) (hC : IsChasles C) (hD : IsChasles D) (hC' : IsChasles C')
    (hv : IsVarCapacityEqns (fun t => A 0 t) (fun t => C 0 t) (fun t => D 0 t)
      (fun t => C' 0 t) b)
    (hbdd : ∀ t : ℝ≥0,
      BddAbove (Set.range fun u : {u : ℝ≥0 // u ≤ t} => C 0 u.1 - A 0 u.1)) :
    IsRtcGreedy A C D C' b := by
  have max_sub : ∀ a b c : ℝ, (a ⊔ b) - c = (a - c) ⊔ (b - c) := fun a b c => by
    rcases le_total a b with h | h
    · rw [max_eq_right h, max_eq_right (sub_le_sub_right h c)]
    · rw [max_eq_left h, max_eq_left (sub_le_sub_right h c)]
  have hC'eq : ∀ t : ℝ≥0, C' 0 t = ⨆ u : {u : ℝ≥0 // u ≤ t}, (C 0 u.1 - A 0 u.1) := by
    intro t
    haveI : Nonempty {u : ℝ≥0 // u ≤ t} := ⟨⟨t, le_rfl⟩⟩
    have hDt : D 0 t = ⨅ u : {u : ℝ≥0 // u ≤ t}, (C 0 t - C 0 u.1 + A 0 u.1) := hv.1 t
    have hC'D : C' 0 t = C 0 t - D 0 t := hv.2.1 t
    rw [hC'D, hDt,
      show (⨅ u : {u : ℝ≥0 // u ≤ t}, (C 0 t - C 0 u.1 + A 0 u.1))
          = ⨅ u : {u : ℝ≥0 // u ≤ t}, (C 0 t - (C 0 u.1 - A 0 u.1)) from
        iInf_congr fun u => by ring,
      ← real_sub_ciSup (C 0 t) _ (hbdd t)]
    ring
  refine ⟨fun s t hst => ?_, fun s t hst => ?_, fun s t hst => ?_⟩
  · -- [9.4]
    have e1 : C' 0 t = C 0 t - D 0 t := hv.2.1 t
    have e2 : C' 0 s = C 0 s - D 0 s := hv.2.1 s
    rw [hD.eq_univariate_sub hst, hC.eq_univariate_sub hst, hC'.eq_univariate_sub hst, e1, e2]
    ring
  · -- [9.5]
    haveI : Nonempty {u : ℝ≥0 // s ≤ u ∧ u ≤ t} := ⟨⟨s, le_rfl, hst⟩⟩
    haveI : Nonempty {u : ℝ≥0 // u ≤ s} := ⟨⟨s, le_rfl⟩⟩
    haveI : Nonempty {u : ℝ≥0 // u ≤ t} := ⟨⟨t, le_rfl⟩⟩
    have hbddst : BddAbove
        (Set.range fun u : {u : ℝ≥0 // s ≤ u ∧ u ≤ t} => C 0 u.1 - A 0 u.1) := by
      obtain ⟨M, hM⟩ := hbdd t
      exact ⟨M, by rintro _ ⟨u, rfl⟩; exact hM ⟨⟨u.1, u.2.2⟩, rfl⟩⟩
    have hbody : ∀ u : {u : ℝ≥0 // s ≤ u ∧ u ≤ t},
        C s u.1 - A s u.1 - b s = (C 0 u.1 - A 0 u.1) - C' 0 s := by
      intro u
      have ebs : b s = A 0 s - D 0 s := hv.2.2 s
      have eC's : C' 0 s = C 0 s - D 0 s := hv.2.1 s
      rw [hC.eq_univariate_sub u.2.1, hA.eq_univariate_sub u.2.1, ebs, eC's]
      ring
    have hsupsplit : (⨆ u : {u : ℝ≥0 // u ≤ t}, (C 0 u.1 - A 0 u.1))
        = (⨆ u : {u : ℝ≥0 // u ≤ s}, (C 0 u.1 - A 0 u.1))
          ⊔ (⨆ u : {u : ℝ≥0 // s ≤ u ∧ u ≤ t}, (C 0 u.1 - A 0 u.1)) := by
      apply le_antisymm
      · refine ciSup_le fun u => ?_
        rcases le_total u.1 s with h | h
        · exact le_sup_of_le_left (le_ciSup_of_le (hbdd s) ⟨u.1, h⟩ le_rfl)
        · exact le_sup_of_le_right (le_ciSup_of_le hbddst ⟨u.1, h, u.2⟩ le_rfl)
      · exact sup_le (ciSup_le fun u => le_ciSup_of_le (hbdd t) ⟨u.1, u.2.trans hst⟩ le_rfl)
          (ciSup_le fun u => le_ciSup_of_le (hbdd t) ⟨u.1, u.2.2⟩ le_rfl)
    rw [iSup_congr hbody, ← real_ciSup_sub _ (C' 0 s) hbddst,
      hC'.eq_univariate_sub hst, hC'eq t, hC'eq s, hsupsplit, max_sub, sub_self]
    exact sup_comm 0 _
  · -- [9.6]
    have e1 : b t = A 0 t - D 0 t := hv.2.2 t
    have e2 : b s = A 0 s - D 0 s := hv.2.2 s
    rw [hA.eq_univariate_sub hst, hD.eq_univariate_sub hst, e1, e2]
    ring

/-- **Theorem 9.2** (Equivalence RTC–NC): for Chasles bivariate `A, C, D, C'` with
`b 0 = 0` and the residual sets bounded above, the RTC greedy-processor equations
[9.4]–[9.6] hold iff the univariate readings satisfy the variable-capacity node
equations [9.7]–[9.9]. -/
theorem isRtcGreedy_iff_isVarCapacityEqns
    {A C D C' : ℝ≥0 → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}
    (hA : IsChasles A) (hC : IsChasles C) (hD : IsChasles D) (hC' : IsChasles C')
    (hb0 : b 0 = 0)
    (hbdd : ∀ t : ℝ≥0,
      BddAbove (Set.range fun u : {u : ℝ≥0 // u ≤ t} => C 0 u.1 - A 0 u.1)) :
    IsRtcGreedy A C D C' b ↔
      IsVarCapacityEqns (fun t => A 0 t) (fun t => C 0 t) (fun t => D 0 t)
        (fun t => C' 0 t) b :=
  ⟨fun hg => isVarCapacityEqns_of_isRtcGreedy hA hC hb0 hg hbdd,
   fun hv => isRtcGreedy_of_isVarCapacityEqns hA hC hD hC' hv hbdd⟩

end DeepWiki
