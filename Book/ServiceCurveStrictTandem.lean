import Book.ServiceCurveStrict
import Book.ServiceCurveStrictEReal
import Book.ServersConcatenation
import Book.RealCurvesConv
import Book.RealCurvesRegularity

/-! # Composition of strict service curves
Strict service curves do not compose: when `β₁` and `β₂` vanish at some
positive `T₁`, `T₂`, the only strict service curve offered by every
concatenation `S_strict(β₂) ∘ S_strict(β₁)` is `0` — witnessed by the staircase
arrival `ν_{T,b}` (period `max(T₁,T₂) < T < T₁ + T₂`) and its delayed copies,
which keep the tandem backlogged forever while `C ≤ A ≤ γ_{b,b/T}` for every
burst `b > 0`. For constant rates the loss is repaired exactly:
`S_strict(λ_{R₂}) ∘ S_strict(λ_{R₁}) = S_strict(λ_{R₁} ∗ λ_{R₂})`, with
`λ_{R₁} ∗ λ_{R₂} = λ_{R₁ ⊓ R₂}` — unlike the min-plus inclusion, which can
be strict. -/

namespace DeepWiki

open Set Topology Filter
open scoped Classical NNReal ENNReal

/-! ## The staircase arrival process -/

/-- The staircase arrival process `ν_{T,b}` delayed by `d`, as a `Curve`. -/
noncomputable def staircaseCurve (T b d : ℝ≥0) : Curve :=
  ⟨staircaseFun T b d, staircaseFun_mono T b d, staircaseFun_zero_eq T b d,
    staircaseFun_pwc T b d, staircaseFun_leftCont T b d⟩

/-- `staircaseCurve T b d t = b·⌈(t − d)/T⌉₊`. -/
@[simp] theorem staircaseCurve_apply (T b d t : ℝ≥0) :
    staircaseCurve T b d t = staircaseFun T b d t := rfl

/-! ## Backlogged periods of delayed staircases -/

/-- A backlogged period of two staircases offset by `δ < T` has length at
most `δ`: backlog only holds on the windows `(d + k·T, d + k·T + δ]`. -/
theorem staircaseFun_length_le_of_isBacklogged
    {T b d δ : ℝ≥0} (hδT : δ < T) {s t : ℝ≥0} (hst : s ≤ t)
    (hbl : IsBacklogged (staircaseFun T b d) (staircaseFun T b (d + δ))
      (Set.Ioc s t)) :
    t - s ≤ δ := by
  rcases eq_or_lt_of_le hst with rfl | hlt
  · rw [tsub_self]; exact zero_le'
  have hT : 0 < T := lt_of_le_of_lt zero_le' hδT
  have hT' : (0 : ℝ) < (T : ℝ) := NNReal.coe_pos.mpr hT
  have hδT' : (δ : ℝ) < (T : ℝ) := NNReal.coe_lt_coe.mpr hδT
  -- the endpoint is backlogged: the delayed ceiling falls strictly below
  have hbt := hbl t ⟨hlt, le_rfl⟩
  have hceil : ⌈((t : ℝ) - ((d + δ : ℝ≥0) : ℝ)) / T⌉₊
      < ⌈((t : ℝ) - d) / T⌉₊ := by
    by_contra hcon
    rw [not_lt] at hcon
    refine absurd hbt (not_lt.mpr ?_)
    exact mul_le_mul_right (by exact_mod_cast hcon) b
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ⌈((t : ℝ) - d) / T⌉₊ = m + 1 :=
    ⟨⌈((t : ℝ) - d) / T⌉₊ - 1, (Nat.succ_pred_eq_of_pos
      (lt_of_le_of_lt (Nat.zero_le _) hceil)).symm⟩
  -- upper bound: `t ≤ d + m·T + δ`
  have hub : (t : ℝ) ≤ (d : ℝ) + m * T + δ := by
    have h1 : ((t : ℝ) - ((d + δ : ℝ≥0) : ℝ)) / T ≤ (m : ℝ) :=
      Nat.ceil_le.mp (by omega)
    have h2 := (div_le_iff₀ hT').mp h1
    push_cast at h2
    linarith
  -- lower bound: the jump `d + m·T` lies strictly before `t`
  have hlb : (d : ℝ) + m * T < t := by
    have h1 : (m : ℝ) < ((t : ℝ) - d) / T := Nat.lt_ceil.mp (by omega)
    have h2 := (lt_div_iff₀ hT').mp h1
    linarith
  -- the start `s` lies at or after the jump `d + m·T`
  have hs : (d : ℝ) + m * T ≤ s := by
    by_contra hcon
    push Not at hcon
    set τ₀ : ℝ≥0 := d + (m : ℝ≥0) * T with hτ₀
    have hτ₀R : ((τ₀ : ℝ≥0) : ℝ) = (d : ℝ) + m * T := by
      rw [hτ₀]; push_cast; ring
    have hsτ₀ : s < τ₀ := by rw [← NNReal.coe_lt_coe, hτ₀R]; exact hcon
    have hτ₀t : τ₀ ≤ t := by rw [← NNReal.coe_le_coe, hτ₀R]; exact hlb.le
    have hbτ₀ := hbl τ₀ ⟨hsτ₀, hτ₀t⟩
    -- the undelayed staircase sits exactly at level `m` at its jump
    have hv₁ : ⌈((τ₀ : ℝ) - d) / T⌉₊ = m := by
      rw [hτ₀R, show (d : ℝ) + m * T - d = m * T by ring,
        mul_div_cancel_right₀ _ hT'.ne', Nat.ceil_natCast]
    -- backlog at the jump forces the delayed ceiling strictly below `m`
    have hc₂ : ⌈((τ₀ : ℝ) - ((d + δ : ℝ≥0) : ℝ)) / T⌉₊ < m := by
      by_contra hcon'
      rw [not_lt] at hcon'
      refine absurd hbτ₀ (not_lt.mpr ?_)
      refine mul_le_mul_right ?_ b
      rw [hv₁] at *
      exact_mod_cast hcon'
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 :=
      ⟨m - 1, (Nat.succ_pred_eq_of_pos
        (lt_of_le_of_lt (Nat.zero_le _) hc₂)).symm⟩
    -- which would give `T ≤ δ`, contradicting `δ < T`
    have h1 : ((τ₀ : ℝ) - ((d + δ : ℝ≥0) : ℝ)) / T ≤ (m' : ℝ) :=
      Nat.ceil_le.mp (by omega)
    have h2 := (div_le_iff₀ hT').mp h1
    rw [hτ₀R] at h2
    push_cast at h2
    linarith
  -- conclude
  have hts : t ≤ s + δ := by
    rw [← NNReal.coe_le_coe]
    push_cast
    linarith
  rw [tsub_le_iff_right, add_comm]
  exact hts

/-- A staircase against its copy delayed by `δ < T` more is served with any
strict curve vanishing at `δ`:
`(ν_{T,b,d}, ν_{T,b,d+δ}) ∈ S_strict(β)` for monotone `β` with `β δ = 0`. -/
theorem staircaseCurve_strictServiceRel
    {β : ℝ≥0 → ℝ≥0} {T δ : ℝ≥0} (hδT : δ < T)
    (hβmono : Monotone β) (hβδ : β δ = 0) (b d : ℝ≥0) :
    strictServiceRel β (staircaseCurve T b d) (staircaseCurve T b (d + δ)) := by
  refine ⟨fun τ => staircaseFun_anti T b le_self_add τ, ?_⟩
  intro s t hst hbl
  have hlen : t - s ≤ δ :=
    staircaseFun_length_le_of_isBacklogged hδT hst hbl
  have hβ0 : β (t - s) = 0 :=
    le_antisymm (hβδ ▸ hβmono hlen) zero_le'
  show staircaseFun T b (d + δ) s + β (t - s) ≤ staircaseFun T b (d + δ) t
  rw [hβ0, add_zero]
  exact staircaseFun_mono T b (d + δ) hst

/-- The same staircase delay-pair realizes the `EReal` pure-delay curve `δ_δ`
*directly*: its backlogged periods have length at most `δ`
(`staircaseFun_length_le_of_isBacklogged`), which is exactly the delay-bound
reading `mem_strictServiceRelEReal_delay_iff`. Composing with
`strictServiceRelEReal_delay_le_strictServiceRel` recovers the finite
`staircaseCurve_strictServiceRel` for any `β` vanishing at `δ` — the book's
`βᵢ ≤ δ_Tᵢ` route through `δ_T`. -/
theorem staircaseCurve_strictServiceRelEReal_delay {T δ : ℝ≥0} (hδT : δ < T)
    (b d : ℝ≥0) :
    strictServiceRelEReal (delayEReal δ)
      (staircaseCurve T b d) (staircaseCurve T b (d + δ)) :=
  mem_strictServiceRelEReal_delay_iff.mpr
    ⟨fun τ => staircaseFun_anti T b le_self_add τ,
      fun _ _ hst hbl => staircaseFun_length_le_of_isBacklogged hδT hst hbl⟩

/-- Delaying the staircase by at least one period keeps the pair backlogged
at every positive time. -/
theorem staircaseFun_isBacklogged_Ioc_zero
    {T b δ : ℝ≥0} (hT : 0 < T) (hb : 0 < b) (hTδ : T ≤ δ) (t : ℝ≥0) :
    IsBacklogged (staircaseFun T b 0) (staircaseFun T b δ) (Set.Ioc 0 t) := by
  intro τ hτ
  have hT' : (0 : ℝ) < (T : ℝ) := NNReal.coe_pos.mpr hT
  have hτ' : (0 : ℝ) < (τ : ℝ) := NNReal.coe_pos.mpr hτ.1
  have hTδ' : (T : ℝ) ≤ (δ : ℝ) := NNReal.coe_le_coe.mpr hTδ
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ⌈((τ : ℝ) - ((0 : ℝ≥0) : ℝ)) / T⌉₊ = m + 1 := by
    refine ⟨⌈((τ : ℝ) - ((0 : ℝ≥0) : ℝ)) / T⌉₊ - 1,
      (Nat.succ_pred_eq_of_pos (Nat.ceil_pos.mpr ?_)).symm⟩
    rw [NNReal.coe_zero, sub_zero]
    exact div_pos hτ' hT'
  have h2 : ⌈((τ : ℝ) - δ) / T⌉₊ ≤ m := by
    rw [Nat.ceil_le, div_le_iff₀ hT']
    have h3 : ((τ : ℝ) - ((0 : ℝ≥0) : ℝ)) / T ≤ ((m + 1 : ℕ) : ℝ) :=
      hm ▸ Nat.le_ceil _
    have h4 := (div_le_iff₀ hT').mp h3
    rw [NNReal.coe_zero, sub_zero] at h4
    push_cast at h4 ⊢
    linarith
  show staircaseFun T b δ τ < staircaseFun T b 0 τ
  unfold staircaseFun
  rw [hm]
  refine mul_lt_mul_of_pos_left ?_ hb
  exact_mod_cast Nat.lt_succ_of_le h2

/-! ## No strict service curve for the tandem -/

/-- **Composition of strict service curves offers only the zero curve**: if
`β₁`, `β₂` vanish at some positive `T₁`, `T₂` and the concatenation
`S_strict(β₂) ∘ S_strict(β₁)` offers the strict service curve `β`, then
`β = 0`. -/
theorem IsStrictMinimalServiceCurve.eq_zero_of_comp
    {β₁ β₂ β : ℝ≥0 → ℝ≥0} {T₁ T₂ : ℝ≥0} (hT₁ : 0 < T₁) (hT₂ : 0 < T₂)
    (hβ₁mono : Monotone β₁) (hβ₂mono : Monotone β₂)
    (hβ₁ : β₁ T₁ = 0) (hβ₂ : β₂ T₂ = 0)
    (hβ : IsStrictMinimalServiceCurve β
      (Relation.Comp (strictServiceRel β₁) (strictServiceRel β₂))) :
    β = 0 := by
  -- an intermediate period `max(T₁,T₂) < T < T₁ + T₂`
  set T : ℝ≥0 := max T₁ T₂ + min T₁ T₂ / 2 with hTdef
  have hmin : 0 < min T₁ T₂ := lt_min hT₁ hT₂
  have hT₁T : T₁ < T :=
    lt_add_of_le_of_pos (le_max_left T₁ T₂) (half_pos hmin)
  have hT₂T : T₂ < T :=
    lt_add_of_le_of_pos (le_max_right T₁ T₂) (half_pos hmin)
  have hTpos : 0 < T := hT₁.trans hT₁T
  have hTsum : T < T₁ + T₂ := by
    rw [hTdef, ← max_add_min T₁ T₂]
    exact add_lt_add_right (NNReal.half_lt_self hmin.ne') _
  funext t
  show β t = 0
  -- for every positive burst `b`, the output is below `γ_{b,b/T}`
  have hkey : ∀ b : ℝ≥0, 0 < b → β t ≤ b / T * t + b := by
    intro b hb
    have hAB : strictServiceRel β₁
        (staircaseCurve T b 0) (staircaseCurve T b T₁) := by
      have h := staircaseCurve_strictServiceRel hT₁T hβ₁mono hβ₁ b 0
      rwa [zero_add] at h
    have hBC : strictServiceRel β₂
        (staircaseCurve T b T₁) (staircaseCurve T b (T₁ + T₂)) :=
      staircaseCurve_strictServiceRel hT₂T hβ₂mono hβ₂ b T₁
    have hbl : IsBacklogged (⇑(staircaseCurve T b 0))
        (⇑(staircaseCurve T b (T₁ + T₂))) (Set.Ioc 0 t) :=
      staircaseFun_isBacklogged_Ioc_zero hTpos hb hTsum.le t
    have hbound := hβ _ _ ⟨staircaseCurve T b T₁, hAB, hBC⟩ 0 t zero_le' hbl
    simp only [staircaseCurve_apply] at hbound
    rw [staircaseFun_zero_eq, zero_add, tsub_zero] at hbound
    calc β t ≤ staircaseFun T b (T₁ + T₂) t := hbound
      _ ≤ staircaseFun T b 0 t := staircaseFun_anti T b zero_le' t
      _ ≤ b / T * t + b := staircaseFun_le_affine hTpos b t
  -- in the real reading: `β t ≤ b·(t/T + 1)` for every `b > 0`
  have hT0 : (0 : ℝ) < (T : ℝ) := NNReal.coe_pos.mpr hTpos
  have hkeyR : ∀ b : ℝ≥0, 0 < b → (β t : ℝ) ≤ (b : ℝ) * ((t : ℝ) / T + 1) := by
    intro b hb
    have h := NNReal.coe_le_coe.mpr (hkey b hb)
    push_cast at h
    have heq : (b : ℝ) / T * t + b = (b : ℝ) * ((t : ℝ) / T + 1) := by ring
    linarith
  -- let the burst go to `0`
  by_contra hβt
  have hβpos : 0 < β t := pos_iff_ne_zero.mpr hβt
  set b₀ : ℝ≥0 := β t / (2 * (t / T + 1)) with hb₀
  have hden : 0 < t / T + 1 := lt_of_lt_of_le one_pos le_add_self
  have hb₀pos : 0 < b₀ := div_pos hβpos (mul_pos two_pos hden)
  have h := hkeyR b₀ hb₀pos
  have hval : (b₀ : ℝ) * ((t : ℝ) / T + 1) = (β t : ℝ) / 2 := by
    rw [hb₀]
    have hden' : (0 : ℝ) < (t : ℝ) / T + 1 := by positivity
    push_cast
    field_simp
  rw [hval] at h
  have hpos : (0 : ℝ) < (β t : ℝ) := NNReal.coe_pos.mpr hβpos
  linarith

/-- Relation form of the impossibility: if
`S_strict(β₂) ∘ S_strict(β₁) ⊆ S_strict(β)` with `β₁`, `β₂` vanishing at
positive points, then `β = 0`. -/
theorem eq_zero_of_comp_strictServiceRel_le
    {β₁ β₂ β : ℝ≥0 → ℝ≥0} {T₁ T₂ : ℝ≥0} (hT₁ : 0 < T₁) (hT₂ : 0 < T₂)
    (hβ₁mono : Monotone β₁) (hβ₂mono : Monotone β₂)
    (hβ₁ : β₁ T₁ = 0) (hβ₂ : β₂ T₂ = 0)
    (h : Relation.Comp (strictServiceRel β₁) (strictServiceRel β₂)
      ≤ strictServiceRel β) :
    β = 0 :=
  IsStrictMinimalServiceCurve.eq_zero_of_comp hT₁ hT₂ hβ₁mono hβ₂mono hβ₁ hβ₂
    (fun A D hp => (h A D hp).2)

/-! ## Constant-rate strict service curves compose -/

/-- **Strict chain rate bound.** Through a chain `C ≤ B ≤ A` where `(A, B)`
has strict rate `R₁` and `(B, C)` strict rate `R₂` (left-continuous stages),
a backlogged period of the composed pair `(A, C)` serves at rate at least
`R₁ ⊓ R₂`: `C s + (R₁ ⊓ R₂)·(t − s) ≤ C t`. -/
theorem strict_chain_rate_bound
    {A B C : ℝ≥0 → ℝ≥0} {R₁ R₂ : ℝ≥0}
    (hAmono : Monotone A) (hBmono : Monotone B) (hCmono : Monotone C)
    (hBlc : IsLeftContinuous B) (hClc : IsLeftContinuous C)
    (h0 : B 0 = C 0) (hc₂ : ∀ x, C x ≤ B x)
    (h₁ : ∀ x y, x ≤ y → IsBacklogged A B (Set.Ioc x y) →
      B x + R₁ * (y - x) ≤ B y)
    (h₂ : ∀ x y, x ≤ y → IsBacklogged B C (Set.Ioc x y) →
      C x + R₂ * (y - x) ≤ C y)
    {s t : ℝ≥0} (hst : s ≤ t) (hbl : IsBacklogged A C (Set.Ioc s t)) :
    C s + (R₁ ⊓ R₂) * (t - s) ≤ C t := by
  set r : ℝ≥0 := R₁ ⊓ R₂ with hr
  rcases eq_zero_or_pos r with hr0 | hrpos
  · rw [hr0, zero_mul, add_zero]
    exact hCmono hst
  -- the bound up to an arbitrary slack `ε`
  have key : ∀ ε : ℝ≥0, 0 < ε → C s + r * (t - s) ≤ C t + ε := by
    intro ε hε
    set Sε : Set ℝ≥0 :=
      {τ | τ ∈ Set.Icc s t ∧ C s + r * (τ - s) ≤ C τ + ε} with hSε
    have hsmem : s ∈ Sε :=
      ⟨⟨le_rfl, hst⟩, by rw [tsub_self, mul_zero, add_zero]; exact le_self_add⟩
    have hne : Sε.Nonempty := ⟨s, hsmem⟩
    have hbdd : BddAbove Sε := ⟨t, fun τ hτ => hτ.1.2⟩
    set σ : ℝ≥0 := sSup Sε with hσdef
    have hsσ : s ≤ σ := le_csSup hbdd hsmem
    have hσt : σ ≤ t := csSup_le hne fun τ hτ => hτ.1.2
    -- the supremum still satisfies the slack bound
    have hσmem : C s + r * (σ - s) ≤ C σ + ε := by
      rcases eq_or_lt_of_le hsσ with heq | hsσlt
      · rw [← heq, tsub_self, mul_zero, add_zero]
        exact le_self_add
      by_contra hcon
      rw [not_le] at hcon
      set w : ℝ≥0 := (C s + r * (σ - s) - (C σ + ε)) / 2 with hw
      have hwpos : 0 < w := half_pos (tsub_pos_of_lt hcon)
      have h2w : (C σ + ε) + (w + w) = C s + r * (σ - s) := by
        rw [hw, add_halves]
        exact add_tsub_cancel_of_le hcon.le
      have hσpos : 0 < σ := lt_of_le_of_lt zero_le' hsσlt
      have hwr : 0 < w / r := div_pos hwpos hrpos
      obtain ⟨τ', hτ'mem, hττ'⟩ :=
        exists_lt_of_lt_csSup hne (tsub_lt_self hσpos hwr)
      have hστ' : σ < τ' + w / r := by
        rcases le_total (w / r) σ with hh | hh
        · exact (tsub_lt_iff_right hh).mp hττ'
        · have hτ'pos : 0 < τ' := by rwa [tsub_eq_zero_of_le hh] at hττ'
          exact lt_of_le_of_lt hh (lt_add_of_pos_left _ hτ'pos)
      have hsτ' : s ≤ τ' := hτ'mem.1.1
      have hτ'σ : τ' ≤ σ := le_csSup hbdd hτ'mem
      have hgrow : r * (σ - s) ≤ r * (τ' - s) + w := by
        have hsub : σ - s ≤ (τ' - s) + w / r := by
          calc σ - s ≤ (τ' + w / r) - s := tsub_le_tsub_right hστ'.le s
            _ = (τ' - s) + w / r := (tsub_add_eq_add_tsub hsτ').symm
        calc r * (σ - s) ≤ r * ((τ' - s) + w / r) := mul_le_mul_right hsub r
          _ = r * (τ' - s) + r * (w / r) := mul_add r _ _
          _ = r * (τ' - s) + w := by
              rw [mul_comm r (w / r), div_mul_cancel₀ w hrpos.ne']
      have hchain : C s + r * (σ - s) ≤ (C σ + ε) + w :=
        calc C s + r * (σ - s) ≤ C s + (r * (τ' - s) + w) :=
              add_le_add_right hgrow _
          _ = (C s + r * (τ' - s)) + w := (add_assoc _ _ _).symm
          _ ≤ (C τ' + ε) + w := add_le_add_left hτ'mem.2 w
          _ ≤ (C σ + ε) + w :=
              add_le_add_left (add_le_add_left (hCmono hτ'σ) ε) w
      have hww : w + w ≤ w := le_of_add_le_add_left (h2w.le.trans hchain)
      exact absurd hww (not_le.mpr (lt_add_of_pos_left w hwpos))
    -- the supremum is `t`
    have hσeq : σ = t := by
      by_contra hne'
      have hσlt : σ < t := lt_of_le_of_ne hσt hne'
      rcases eq_or_lt_of_le hsσ with heq | hsσlt
      · -- `σ = s`: within the slack `ε`, the next moments join `Sε`
        set ρ : ℝ≥0 := min t (s + ε / r) with hρ
        have hsρ : s < ρ :=
          lt_min (heq ▸ hσlt) (lt_add_of_pos_right s (div_pos hε hrpos))
        have hρmem : ρ ∈ Sε := by
          refine ⟨⟨hsρ.le, min_le_left _ _⟩, ?_⟩
          have hρs : ρ - s ≤ ε / r :=
            tsub_le_iff_left.mpr (min_le_right _ _)
          calc C s + r * (ρ - s) ≤ C s + r * (ε / r) :=
                add_le_add_right (mul_le_mul_right hρs r) _
            _ = C s + ε := by
                rw [mul_comm r (ε / r), div_mul_cancel₀ ε hrpos.ne']
            _ ≤ C ρ + ε := add_le_add_left (hCmono hsρ.le) ε
        exact absurd (le_csSup hbdd hρmem)
          (not_le.mpr (lt_of_le_of_lt heq.symm.le hsρ))
      · -- `s < σ < t`: backlog at `σ` gives the gap `g = A σ − C σ`
        have hgap : C σ < A σ := hbl σ ⟨hsσlt, hσt⟩
        set g : ℝ≥0 := A σ - C σ with hg
        have hgpos : 0 < g := tsub_pos_of_lt hgap
        set h : ℝ≥0 := min (t - σ) (g / (2 * r)) with hh
        have hhpos : 0 < h :=
          lt_min (tsub_pos_of_lt hσlt) (div_pos hgpos (mul_pos two_pos hrpos))
        set ρ : ℝ≥0 := σ + h with hρ
        have hσρ : σ < ρ := lt_add_of_pos_right σ hhpos
        have hρt : ρ ≤ t := by
          calc σ + h ≤ σ + (t - σ) := add_le_add_right (min_le_left _ _) σ
            _ = t := add_tsub_cancel_of_le hσlt.le
        -- the composed output grows at rate `r` over `(σ, ρ]`
        have hgrow : C σ + r * h ≤ C ρ := by
          by_cases hP : ∃ τ' ∈ Set.Ioc σ ρ, B τ' = C τ'
          · -- the second stage empties inside `(σ, ρ]`: split at the last
            -- emptying point `start B C ρ`
            obtain ⟨τ', hτ'Ioc, hτ'eq⟩ := hP
            set σP : ℝ≥0 := start B C ρ with hσP
            have hbddP : BddAbove {u | u ≤ ρ ∧ B u = C u} :=
              ⟨ρ, fun x hx => hx.1⟩
            have hτ'σP : τ' ≤ σP := le_csSup hbddP ⟨hτ'Ioc.2, hτ'eq⟩
            have hσσP : σ < σP := lt_of_lt_of_le hτ'Ioc.1 hτ'σP
            have hσPρ : σP ≤ ρ := start_le B C ρ
            have hσPeq : B σP = C σP := apply_start_eq hBlc hClc h0 hc₂ ρ
            by_contra hcon
            rw [not_le] at hcon
            -- everything `C` reaches by `ρ` stays below `A σ`
            have hrh : r * h ≤ g / 2 := by
              calc r * h ≤ r * (g / (2 * r)) :=
                    mul_le_mul_right (min_le_right _ _) r
                _ = g / 2 := by
                    rw [← mul_div_assoc, mul_comm 2 r,
                      mul_div_mul_left g 2 hrpos.ne']
            have hCρlt : C ρ < A σ := by
              calc C ρ < C σ + r * h := hcon
                _ ≤ C σ + g / 2 := add_le_add_right hrh _
                _ < C σ + g :=
                    add_lt_add_right (NNReal.half_lt_self hgpos.ne') _
                _ = A σ := add_tsub_cancel_of_le hgap.le
            -- so the first stage is backlogged on `(σ, σP]`
            have hbl₁ : IsBacklogged A B (Set.Ioc σ σP) := by
              intro τ'' hτ''
              calc B τ'' ≤ B σP := hBmono hτ''.2
                _ = C σP := hσPeq
                _ ≤ C ρ := hCmono hσPρ
                _ < A σ := hCρlt
                _ ≤ A τ'' := hAmono hτ''.1.le
            -- and the second stage is backlogged on `(σP, ρ]`
            have hbl₂ : IsBacklogged B C (Set.Ioc σP ρ) := by
              intro τ'' hτ''
              rcases (hc₂ τ'').lt_or_eq with hlt' | heq'
              · exact hlt'
              · exact absurd (le_csSup hbddP ⟨hτ''.2, heq'.symm⟩)
                  (not_le.mpr hτ''.1)
            have hB₁ := h₁ σ σP hσσP.le hbl₁
            have hB₂ := h₂ σP ρ hσPρ hbl₂
            have hsplit : (σP - σ) + (ρ - σP) = h := by
              rw [add_comm, tsub_add_tsub_cancel hσPρ hσσP.le, hρ,
                add_tsub_cancel_left]
            have hfinal : C σ + r * h ≤ C ρ :=
              calc C σ + r * h
                  = (C σ + r * (σP - σ)) + r * (ρ - σP) := by
                    rw [← hsplit, mul_add, add_assoc]
                _ ≤ (B σ + R₁ * (σP - σ)) + r * (ρ - σP) :=
                    add_le_add_left
                      (add_le_add (hc₂ σ)
                        (mul_le_mul_left inf_le_left _)) _
                _ ≤ B σP + r * (ρ - σP) := add_le_add_left hB₁ _
                _ = C σP + r * (ρ - σP) := by rw [hσPeq]
                _ ≤ C σP + R₂ * (ρ - σP) :=
                    add_le_add_right (mul_le_mul_left inf_le_right _) _
                _ ≤ C ρ := hB₂
            exact absurd hfinal (not_le.mpr hcon)
          · -- the second stage stays backlogged on all of `(σ, ρ]`
            push Not at hP
            have hbl₂ : IsBacklogged B C (Set.Ioc σ ρ) := fun τ'' hτ'' =>
              lt_of_le_of_ne (hc₂ τ'') fun heq' => hP τ'' hτ'' heq'.symm
            have hB₂ := h₂ σ ρ hσρ.le hbl₂
            calc C σ + r * h ≤ C σ + R₂ * h :=
                  add_le_add_right (mul_le_mul_left inf_le_right _) _
              _ = C σ + R₂ * (ρ - σ) := by rw [hρ, add_tsub_cancel_left]
              _ ≤ C ρ := hB₂
        -- `ρ` joins `Sε`, beyond the supremum
        have hρmem : ρ ∈ Sε := by
          refine ⟨⟨hsσ.trans hσρ.le, hρt⟩, ?_⟩
          have hρs : ρ - s = (σ - s) + h := by
            rw [hρ, tsub_add_eq_add_tsub hsσ]
          calc C s + r * (ρ - s)
              = (C s + r * (σ - s)) + r * h := by
                rw [hρs, mul_add, add_assoc]
            _ ≤ (C σ + ε) + r * h := add_le_add_left hσmem _
            _ = (C σ + r * h) + ε := by ring
            _ ≤ C ρ + ε := add_le_add_left hgrow ε
        exact absurd (le_csSup hbdd hρmem) (not_le.mpr hσρ)
    rw [hσeq] at hσmem
    exact hσmem
  -- discharge the slack
  by_contra hcon
  rw [not_le] at hcon
  set w : ℝ≥0 := (C s + r * (t - s)) - C t with hw
  have hwpos : 0 < w := tsub_pos_of_lt hcon
  have hhalf := key (w / 2) (half_pos hwpos)
  have hwc : C t + w = C s + r * (t - s) := add_tsub_cancel_of_le hcon.le
  have hle : C t + w ≤ C t + w / 2 := hwc.le.trans hhalf
  exact absurd (le_of_add_le_add_left hle)
    (not_le.mpr (NNReal.half_lt_self hwpos.ne'))

/-- **Strict service curves of constant rate compose**: if causal `S₁`, `S₂`
offer strict `λ_{R₁}`, `λ_{R₂}`, the concatenation offers strict
`λ_{R₁ ⊓ R₂}` (`= λ_{R₁} ∗ λ_{R₂}`). -/
theorem IsStrictMinimalServiceCurve.comp_rate
    {S₁ S₂ : Curve → Curve → Prop} {R₁ R₂ : ℝ≥0}
    (hc₂ : IsCausal S₂)
    (h₁ : IsStrictMinimalServiceCurve (rate R₁) S₁)
    (h₂ : IsStrictMinimalServiceCurve (rate R₂) S₂) :
    IsStrictMinimalServiceCurve (rate (R₁ ⊓ R₂)) (Relation.Comp S₁ S₂) := by
  rintro A C ⟨B, hAB, hBC⟩ s t hst hbl
  exact strict_chain_rate_bound A.mono B.mono C.mono B.leftCont C.leftCont
    (B.zero_eq C) (fun x => hc₂ B C hBC x)
    (fun x y hxy hb => h₁ A B hAB x y hxy hb)
    (fun x y hxy hb => h₂ B C hBC x y hxy hb) hst hbl

/-- Relation form of the rate composition:
`S_strict(λ_{R₂}) ∘ S_strict(λ_{R₁}) ⊆ S_strict(λ_{R₁ ⊓ R₂})`. -/
theorem comp_strictServiceRel_rate_le (R₁ R₂ : ℝ≥0) :
    Relation.Comp (strictServiceRel (rate R₁)) (strictServiceRel (rate R₂))
      ≤ strictServiceRel (rate (R₁ ⊓ R₂)) := by
  intro A C hp
  refine ⟨IsCausal.comp (S₁ := strictServiceRel (rate R₁))
    (S₂ := strictServiceRel (rate R₂))
    (fun _ _ h => h.1) (fun _ _ h => h.1) A C hp, ?_⟩
  exact IsStrictMinimalServiceCurve.comp_rate
    (fun _ _ h => h.1)
    (isStrictMinimalServiceCurve_strictServiceRel (rate R₁))
    (isStrictMinimalServiceCurve_strictServiceRel (rate R₂)) A C hp

/-- The reverse containment also holds for constant rates: a pair served at
strict rate `R₁ ⊓ R₂` factors through the tandem by routing it through the
identity server on the faster stage (`B = A` when `R₂ ≤ R₁`, else `B = C`),
whose backlogged periods are empty. -/
theorem strictServiceRel_rate_le_comp (R₁ R₂ : ℝ≥0) :
    strictServiceRel (rate (R₁ ⊓ R₂))
      ≤ Relation.Comp (strictServiceRel (rate R₁))
          (strictServiceRel (rate R₂)) := by
  intro A C hp
  rcases le_total R₂ R₁ with h | h
  · exact ⟨A, strictServiceRel_self (mul_zero R₁) A,
      by rwa [inf_eq_right.mpr h] at hp⟩
  · exact ⟨C, by rwa [inf_eq_left.mpr h] at hp,
      strictServiceRel_self (mul_zero R₂) C⟩

/-- **For constant rates the composition is exactly the convolution**:
`S_strict(λ_{R₂}) ∘ S_strict(λ_{R₁}) = S_strict(λ_{R₁ ⊓ R₂})`. -/
theorem comp_strictServiceRel_rate_eq (R₁ R₂ : ℝ≥0) :
    Relation.Comp (strictServiceRel (rate R₁)) (strictServiceRel (rate R₂))
      = strictServiceRel (rate (R₁ ⊓ R₂)) :=
  le_antisymm (comp_strictServiceRel_rate_le R₁ R₂)
    (strictServiceRel_rate_le_comp R₁ R₂)

/-! ## Book restatement (composition of strict service curves)
Let `β₁` and `β₂` be two (non-decreasing) functions such that there exist
`T₁, T₂ > 0` with `β₁ T₁ = 0` and `β₂ T₂ = 0`. Then there is no `β ≠ 0` such
that `S_strict(β₂) ∘ S_strict(β₁) ⊆ S_strict(β)`. -/
example {β₁ β₂ : ℝ≥0 → ℝ≥0} {T₁ T₂ : ℝ≥0} (hT₁ : 0 < T₁) (hT₂ : 0 < T₂)
    (hβ₁mono : Monotone β₁) (hβ₂mono : Monotone β₂)
    (hβ₁ : β₁ T₁ = 0) (hβ₂ : β₂ T₂ = 0) :
    ¬ ∃ β : ℝ≥0 → ℝ≥0, β ≠ 0 ∧
      Relation.Comp (strictServiceRel β₁) (strictServiceRel β₂)
        ≤ strictServiceRel β :=
  fun ⟨_, hβne, hle⟩ => hβne
    (eq_zero_of_comp_strictServiceRel_le hT₁ hT₂ hβ₁mono hβ₂mono hβ₁ hβ₂ hle)

/-! The arrival witness `ν_{T,b}` is constrained by the token bucket
`γ_{b,b/T}`. -/
example {T : ℝ≥0} (hT : 0 < T) (b t : ℝ≥0) :
    (staircaseFun T b 0 t : ℝ≥0∞) ≤ tokenBucketNN (b / T) b t := by
  rcases eq_zero_or_pos t with rfl | ht
  · rw [staircaseFun_zero_eq, tokenBucketNN_zero_eq]
    exact le_rfl
  · rw [tokenBucketNN_apply,
      show delayNN (0 : ℝ≥0) t = ⊤ from delay_eq_top 0 ht, inf_top_eq,
      show ((b / T : ℝ≥0) : ℝ≥0∞) * t + b = ((b / T * t + b : ℝ≥0) : ℝ≥0∞) by
        push_cast; rfl]
    exact_mod_cast staircaseFun_le_affine hT b t

/-! ## Book restatement (constant rates: the loss is repaired)
When `β₁ = λ_{R₁}` and `β₂ = λ_{R₂}`,
`S_strict(β₂) ∘ S_strict(β₁) ⊆ S_strict(β₁ ∗ β₂)`: over a backlogged period the
service offered is at least `min(R₁,R₂)·(t − s)`, and
`λ_{R₁} ∗ λ_{R₂} = λ_{R₁ ⊓ R₂}`. -/
example (R₁ R₂ : ℝ≥0) :
    Relation.Comp (strictServiceRel (rate R₁)) (strictServiceRel (rate R₂))
        ≤ strictServiceRel (rate (R₁ ⊓ R₂))
      ∧ minConv (rateNN R₁) (rateNN R₂) = rateNN (R₁ ⊓ R₂) :=
  ⟨comp_strictServiceRel_rate_le R₁ R₂, conv_rateNN_rateNN R₁ R₂⟩

/-! The formalization sharpens the inclusion to an equality: for constant
rates the composition is *exactly* the convolution — in contrast with the
min-plus relations, where the concatenation inclusion can be strict. -/
example (R₁ R₂ : ℝ≥0) :
    Relation.Comp (strictServiceRel (rate R₁)) (strictServiceRel (rate R₂))
      = strictServiceRel (rate (R₁ ⊓ R₂)) :=
  comp_strictServiceRel_rate_eq R₁ R₂

/-! ## Delay tandems dilute to min-plus (§9.3, towards Lemma 9.5)
An `n`-tandem of strict pure-delay servers is min-plus served by the delay of the
sum: `(S_strict(δ_d))ⁿ ⊆ S_mp(δ_{n·d})`. This is Lemma 9.5's `⊆` direction
without the closure (with `d = T/n` it gives `(S_strict(δ_{T/n}))ⁿ ⊆ S_mp(δ_T)`,
since `δ_{T/n}∗ⁿ = δ_T`): each strict server is min-plus
(`strictServiceRelEReal_le_minimalServiceRel`), the min-plus concatenation
convolves the curves (`comp_minimalServiceRel_le`), and pure delays add
(`conv_delayEReal_delayEReal`). Note each tandem is *not* a strict server
(Prop 6.2 above) — it only achieves the min-plus delay, which is exactly the
dilution Lemma 9.5 turns into a limit. -/

/-- **Two strict delay servers in tandem** are min-plus served by the delay of
the sum: `S_strict(δ_a) ∘ S_strict(δ_b) ⊆ S_mp(δ_{a+b})`. -/
theorem comp_strictServiceRelEReal_delay_le (a b : ℝ≥0) :
    Relation.Comp (strictServiceRelEReal (delayEReal a))
        (strictServiceRelEReal (delayEReal b))
      ≤ minimalServiceRel (delayEReal (a + b)) := by
  rw [← conv_delayEReal_delayEReal a b]
  rintro A C ⟨B, hAB, hBC⟩
  have hmp : Relation.Comp (minimalServiceRel (delayEReal a))
      (minimalServiceRel (delayEReal b)) A C :=
    ⟨B, strictServiceRelEReal_le_minimalServiceRel A B hAB,
      strictServiceRelEReal_le_minimalServiceRel B C hBC⟩
  exact comp_minimalServiceRel_le (isNonneg_delayEReal a).isBddBelowReal
    (isNonneg_delayEReal b).isBddBelowReal A C hmp

/-- **The `n`-tandem of strict delay servers is min-plus**:
`(S_strict(δ_d))ⁿ ⊆ S_mp(δ_{n·d})`. By induction — the base is the unit
(`δ_0` shifts by `0`), each step peels one server through the binary tandem
above. -/
theorem compPow_strictServiceRelEReal_delay_le (d : ℝ≥0) (n : ℕ) :
    compPow (strictServiceRelEReal (delayEReal d)) n
      ≤ minimalServiceRel (delayEReal (n • d)) := by
  induction n with
  | zero =>
    rw [compPow_zero, zero_nsmul]
    rintro A C rfl
    refine mem_minimalServiceRel_iff.mpr ⟨fun _ => le_refl _, ?_⟩
    rw [conv_delayEReal (curveEReal A) (monotone_curveEReal A) (isNeverBot_curveEReal A)]
    intro t
    show curveEReal A (t - 0) ≤ curveEReal A t
    rw [tsub_zero]
  | succ n ih =>
    rw [compPow_succ, succ_nsmul]
    rintro A C ⟨B, hAB, hBC⟩
    have hcomp : Relation.Comp (minimalServiceRel (delayEReal (n • d)))
        (minimalServiceRel (delayEReal d)) A C :=
      ⟨B, ih A B hAB, strictServiceRelEReal_le_minimalServiceRel B C hBC⟩
    have hcat := comp_minimalServiceRel_le (isNonneg_delayEReal (n • d)).isBddBelowReal
      (isNonneg_delayEReal d).isBddBelowReal A C hcomp
    rwa [conv_delayEReal_delayEReal (n • d) d] at hcat

/-- **Lemma 9.5, `⊆` (per-`n`, before the closure)**: `n` strict `δ_{T/n}`
servers in tandem are min-plus served by `δ_T` (for `n ≥ 1`, where
`n · (T/n) = T`). The closure and the reverse dilution remain. -/
theorem compPow_strictServiceRelEReal_delayDiv_le (T : ℝ≥0) {n : ℕ} (hn : 0 < n) :
    compPow (strictServiceRelEReal (delayEReal (T / n))) n
      ≤ minimalServiceRel (delayEReal T) := by
  have hcast : (n : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hTn : n • (T / n) = T := by
    rw [nsmul_eq_mul]; field_simp
  rw [show delayEReal T = delayEReal (n • (T / n)) from by rw [hTn]]
  exact compPow_strictServiceRelEReal_delay_le (T / n) n

end DeepWiki
