import Book.Additivity
import Book.ArrivalCurvesMaximal
import Book.DeviationsBoundsServer

/-! # Deviations on a restricted domain
At a positive crossing point `τ` of a sub-additive `α` and a super-additive
`β` (`α τ ≤ β τ`), the global vertical and horizontal deviations can already
be computed on `[0, τ]`: the pointwise deviation at `t = q • τ + r` is
dominated by the one at `r ≤ τ`. Backlog and delay of a served pair are thus
bounded by deviations computed on a bounded interval. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- Euclidean decomposition of a time by a positive period: every `t : ℝ≥0`
is `q • τ + r` with `r < τ`. -/
theorem exists_eq_nsmul_add_lt_of_pos {τ : ℝ≥0} (hτ : 0 < τ) (t : ℝ≥0) :
    ∃ (q : ℕ) (r : ℝ≥0), t = q • τ + r ∧ r < τ := by
  have hle : (⌊t / τ⌋₊ : ℝ≥0) * τ ≤ t :=
    (le_div_iff₀ hτ).mp (Nat.floor_le zero_le')
  refine ⟨⌊t / τ⌋₊, t - (⌊t / τ⌋₊ : ℝ≥0) * τ, ?_, ?_⟩
  · rw [nsmul_eq_mul, add_tsub_cancel_of_le hle]
  · rw [tsub_lt_iff_left hle]
    have h1 : t / τ < ⌊t / τ⌋₊ + 1 := Nat.lt_floor_add_one _
    rw [div_lt_iff₀ hτ] at h1
    calc t < ((⌊t / τ⌋₊ : ℝ≥0) + 1) * τ := h1
      _ = (⌊t / τ⌋₊ : ℝ≥0) * τ + τ := by rw [add_one_mul]

/-- Crossing-point domination (vertical): for sub-additive `α`,
super-additive `β`, and `α τ ≤ β τ`, the pointwise vertical deviation at
`q • τ + r` is dominated by the one at `r`. -/
theorem vDevAt_nsmul_add_le {α β : ℝ≥0 → ℝ≥0∞}
    (hsub : IsSubadditive α) (hsup : IsSuperadditive β)
    {τ : ℝ≥0} (hcross : α τ ≤ β τ) (q : ℕ) (r : ℝ≥0) :
    vDevAt α β (q • τ + r) ≤ vDevAt α β r := by
  show α (q • τ + r) - β (q • τ + r) ≤ α r - β r
  calc α (q • τ + r) - β (q • τ + r)
      ≤ (q • α τ + α r) - β (q • τ + r) :=
        tsub_le_tsub_right (hsub.apply_nsmul_add_le q τ r) _
    _ ≤ (q • α τ + α r) - (q • β τ + β r) :=
        tsub_le_tsub_left (hsup.le_apply_nsmul_add q τ r) _
    _ ≤ (q • β τ + α r) - (q • β τ + β r) :=
        tsub_le_tsub_right
          (add_le_add (nsmul_le_nsmul_right hcross q) le_rfl) _
    _ ≤ α r - β r := by
        rw [tsub_le_iff_right, add_comm (α r - β r) (q • β τ + β r),
          add_assoc]
        exact add_le_add le_rfl le_add_tsub

/-- A pointwise family dominated under period shifts computes its supremum
on `[0, τ]`: `F (q • τ + r) ≤ F r` gives `⨆ t, F t = ⨆ t ≤ τ, F t`. -/
theorem iSup_eq_biSup_of_nsmul_add_le {F : ℝ≥0 → ℝ≥0∞} {τ : ℝ≥0}
    (hτ : 0 < τ) (hdom : ∀ (q : ℕ) (r : ℝ≥0), F (q • τ + r) ≤ F r) :
    (⨆ t, F t) = ⨆ t ≤ τ, F t := by
  apply le_antisymm
  · refine iSup_le fun t => ?_
    obtain ⟨q, r, rfl, hrτ⟩ := exists_eq_nsmul_add_lt_of_pos hτ t
    exact le_trans (hdom q r)
      (le_iSup₂ (f := fun t (_ : t ≤ τ) => F t) r hrτ.le)
  · exact iSup₂_le fun t _ => le_iSup F t

/-- **Restricting the vertical-deviation domain.** At a positive crossing
point `τ` of sub-additive `α` against super-additive `β`, the vertical
deviation can be computed on `[0, τ]`: `vDev α β = ⨆ t ≤ τ, vDevAt α β t`. -/
theorem vDev_eq_biSup_of_crossing {α β : ℝ≥0 → ℝ≥0∞}
    (hsub : IsSubadditive α) (hsup : IsSuperadditive β)
    {τ : ℝ≥0} (hτ : 0 < τ) (hcross : α τ ≤ β τ) :
    vDev α β = ⨆ t ≤ τ, vDevAt α β t :=
  iSup_eq_biSup_of_nsmul_add_le hτ
    (vDevAt_nsmul_add_le hsub hsup hcross)

/-- Crossing-point domination (horizontal): admissible shifts at `r`
transfer to `q • τ + r`, so the pointwise horizontal deviation at
`q • τ + r` is dominated by the one at `r`. -/
theorem hDevAt_nsmul_add_le {α β : ℝ≥0 → ℝ≥0∞}
    (hsub : IsSubadditive α) (hsup : IsSuperadditive β)
    {τ : ℝ≥0} (hcross : α τ ≤ β τ) (q : ℕ) (r : ℝ≥0) :
    (hDevAt α β (q • τ + r) : ℝ≥0∞) ≤ hDevAt α β r := by
  refine le_iInf fun d => hDevAt_le ?_
  calc α (q • τ + r)
      ≤ q • α τ + α r := hsub.apply_nsmul_add_le q τ r
    _ ≤ q • β τ + β (r + d.1) :=
        add_le_add (nsmul_le_nsmul_right hcross q) d.2
    _ ≤ β (q • τ + (r + d.1)) := hsup.le_apply_nsmul_add q τ (r + d.1)
    _ = β (q • τ + r + d.1) := by rw [add_assoc]

/-- **Restricting the horizontal-deviation domain.** At a positive crossing
point `τ`, the horizontal deviation can be computed on `[0, τ]`:
`hDev α β = ⨆ t ≤ τ, hDevAt α β t`. -/
theorem hDev_eq_biSup_of_crossing {α β : ℝ≥0 → ℝ≥0∞}
    (hsub : IsSubadditive α) (hsup : IsSuperadditive β)
    {τ : ℝ≥0} (hτ : 0 < τ) (hcross : α τ ≤ β τ) :
    (hDev α β : ℝ≥0∞) = ⨆ t ≤ τ, (hDevAt α β t : ℝ≥0∞) :=
  iSup_eq_biSup_of_nsmul_add_le hτ
    (hDevAt_nsmul_add_le hsub hsup hcross)

/-! ## The first crossing without attainment
At `ℓ = sInf (crossingSet α β)` the restriction holds even when the infimum
is not attained, for monotone curves: crossing points exist arbitrarily
close above `ℓ`, and the deviations on the gap `(ℓ, τ]` vanish along the
crossing set — no continuity needed. -/

/-- A family computing on `[0, τ]` at every point of `S` also computes on
`[0, sInf S]`, provided it is dominated on the gap `(sInf S, τ]` by a bound
`C τ` that vanishes along `S`. -/
theorem iSup_eq_biSup_sInf_of_vanishing_gap {F : ℝ≥0 → ℝ≥0∞} {S : Set ℝ≥0}
    (hat : ∀ τ ∈ S, (⨆ t, F t) = ⨆ t ≤ τ, F t)
    {C : ℝ≥0 → ℝ≥0∞}
    (hspike : ∀ τ ∈ S, ∀ t, sInf S < t → t ≤ τ → F t ≤ C τ)
    (hvanish : ∀ x : ℝ≥0∞, (∀ τ ∈ S, x ≤ C τ) → x = 0) :
    (⨆ t, F t) = ⨆ t ≤ sInf S, F t := by
  refine le_antisymm ?_ (iSup₂_le fun t _ => le_iSup F t)
  rcases le_or_gt (⨆ t, F t) (⨆ t ≤ sInf S, F t) with h | h
  · exact h
  · have hsplit : ∀ τ ∈ S, (⨆ t, F t) ≤ (⨆ t ≤ sInf S, F t) ⊔ C τ := by
      intro τ hτ
      rw [hat τ hτ]
      refine iSup₂_le fun t htτ => ?_
      rcases le_or_gt t (sInf S) with htℓ | htℓ
      · exact le_sup_of_le_left
          (le_iSup₂ (f := fun t (_ : t ≤ sInf S) => F t) t htℓ)
      · exact le_sup_of_le_right (hspike τ hτ t htℓ htτ)
    have hC : ∀ τ ∈ S, (⨆ t, F t) ≤ C τ := fun τ hτ =>
      (le_sup_iff.mp (hsplit τ hτ)).resolve_left (not_le.mpr h)
    rw [hvanish _ hC]
    exact zero_le'

/-- **Restricting the vertical-deviation domain at the first crossing.**
For monotone sub-additive `α` against super-additive `β` with a nonempty
crossing set, the vertical deviation is computed on
`[0, sInf (crossingSet α β)]` — whether or not the infimum is attained
(contrast `vDev_eq_biSup_of_crossing`: any crossing point, no
monotonicity). -/
theorem vDev_eq_biSup_sInf_crossingSet {α β : ℝ≥0 → ℝ≥0∞}
    (hsub : IsSubadditive α) (hsup : IsSuperadditive β)
    (hαmono : Monotone α)
    (hne : (crossingSet α β).Nonempty) :
    vDev α β = ⨆ t ≤ sInf (crossingSet α β), vDevAt α β t := by
  refine iSup_eq_biSup_sInf_of_vanishing_gap
    (fun τ hτ => vDev_eq_biSup_of_crossing hsub hsup hτ.1 hτ.2)
    (C := fun τ => α τ - ⨅ σ ∈ crossingSet α β, β σ) ?_ ?_
  · -- the gap bound: a crossing `σ < t` exists, so `β t ≥ ⨅ β` over crossings
    intro τ hτ t htℓ htτ
    obtain ⟨σ, hσS, hσt⟩ := exists_lt_of_csInf_lt hne htℓ
    show vDevAt α β t ≤ α τ - ⨅ σ ∈ crossingSet α β, β σ
    calc vDevAt α β t = α t - β t := rfl
      _ ≤ α τ - β t := tsub_le_tsub_right (hαmono htτ) _
      _ ≤ α τ - ⨅ σ ∈ crossingSet α β, β σ :=
          tsub_le_tsub_left
            ((iInf₂_le σ hσS).trans (hsup.monotone hσt.le)) _
  · -- vanishing: `⨅ α ≤ α σ ≤ β σ` over crossings forces the bound to `0`
    intro x hx
    have hx' : ∀ τ ∈ crossingSet α β,
        x ≤ α τ - ⨅ σ ∈ crossingSet α β, β σ := hx
    set c := ⨅ σ ∈ crossingSet α β, β σ with hc
    rcases eq_or_ne c ⊤ with hctop | hcne
    · obtain ⟨τ, hτ⟩ := hne
      have hxτ := hx' τ hτ
      rw [hctop, ENNReal.sub_top] at hxτ
      exact le_antisymm hxτ zero_le'
    · by_contra hx0
      have hadd : ∀ τ ∈ crossingSet α β, x + c ≤ α τ := by
        intro τ hτ
        have hCτ := hx' τ hτ
        have hcα : c ≤ α τ := by
          by_contra hcon
          rw [not_le] at hcon
          rw [tsub_eq_zero_of_le hcon.le] at hCτ
          exact hx0 (le_antisymm hCτ zero_le')
        exact ((ENNReal.cancel_of_ne hcne).le_tsub_iff_right hcα).mp hCτ
      have hαc : (⨅ τ ∈ crossingSet α β, α τ) ≤ c :=
        le_iInf₂ fun σ hσ => (iInf₂_le σ hσ).trans hσ.2
      have hxc : x + c ≤ 0 + c := by
        rw [zero_add]
        exact (le_iInf₂ hadd).trans hαc
      exact hx0 (le_antisymm
        ((ENNReal.cancel_of_ne hcne).add_le_add_iff_right.mp hxc)
        zero_le')

/-- **Restricting the horizontal-deviation domain at the first crossing.**
Same as the vertical side: with a nonempty crossing set and monotone `α`,
the horizontal deviation is computed on `[0, sInf (crossingSet α β)]` —
the gap shifts `τ - t` vanish along the crossing set (contrast
`hDev_eq_biSup_of_crossing`: any crossing point, no monotonicity). -/
theorem hDev_eq_biSup_sInf_crossingSet {α β : ℝ≥0 → ℝ≥0∞}
    (hsub : IsSubadditive α) (hsup : IsSuperadditive β)
    (hαmono : Monotone α)
    (hne : (crossingSet α β).Nonempty) :
    (hDev α β : ℝ≥0∞)
      = ⨆ t ≤ sInf (crossingSet α β), (hDevAt α β t : ℝ≥0∞) := by
  refine iSup_eq_biSup_sInf_of_vanishing_gap
    (fun τ hτ => hDev_eq_biSup_of_crossing hsub hsup hτ.1 hτ.2)
    (C := fun τ => ((τ - sInf (crossingSet α β) : ℝ≥0) : ℝ≥0∞)) ?_ ?_
  · -- the gap bound: the shift `τ - t` is admissible and at most `τ - ℓ`
    intro τ hτ t htℓ htτ
    show (hDevAt α β t : ℝ≥0∞)
      ≤ ((τ - sInf (crossingSet α β) : ℝ≥0) : ℝ≥0∞)
    refine le_trans (hDevAt_le (d := τ - t) ?_) ?_
    · rw [add_tsub_cancel_of_le htτ]
      exact (hαmono htτ).trans hτ.2
    · show ((τ - t : ℝ≥0) : ℝ≥0∞)
        ≤ ((τ - sInf (crossingSet α β) : ℝ≥0) : ℝ≥0∞)
      exact_mod_cast tsub_le_tsub_left htℓ.le τ
  · -- vanishing: crossings sit arbitrarily close above the infimum
    intro x hx
    have hx' : ∀ τ ∈ crossingSet α β,
        x ≤ ((τ - sInf (crossingSet α β) : ℝ≥0) : ℝ≥0∞) := hx
    by_contra hx0
    obtain ⟨τ₀, hτ₀⟩ := hne
    have hadd : ∀ τ ∈ crossingSet α β,
        x + ((sInf (crossingSet α β) : ℝ≥0) : ℝ≥0∞) ≤ (τ : ℝ≥0∞) := by
      intro τ hτ
      have hxτ := hx' τ hτ
      rw [ENNReal.coe_sub] at hxτ
      have hℓτ : ((sInf (crossingSet α β) : ℝ≥0) : ℝ≥0∞) ≤ (τ : ℝ≥0∞) :=
        ENNReal.coe_le_coe.mpr (csInf_le (OrderBot.bddBelow _) hτ)
      calc x + ((sInf (crossingSet α β) : ℝ≥0) : ℝ≥0∞)
          ≤ ((τ : ℝ≥0∞) - ((sInf (crossingSet α β) : ℝ≥0) : ℝ≥0∞))
              + ((sInf (crossingSet α β) : ℝ≥0) : ℝ≥0∞) :=
            add_le_add hxτ le_rfl
        _ = (τ : ℝ≥0∞) := tsub_add_cancel_of_le hℓτ
    have hfin : x + ((sInf (crossingSet α β) : ℝ≥0) : ℝ≥0∞) ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.coe_ne_top (r := τ₀)) (hadd τ₀ hτ₀)
    have hlb : ∀ τ ∈ crossingSet α β,
        (x + ((sInf (crossingSet α β) : ℝ≥0) : ℝ≥0∞)).toNNReal ≤ τ :=
      fun τ hτ => by
        have h := ENNReal.toNNReal_mono ENNReal.coe_ne_top (hadd τ hτ)
        rwa [ENNReal.toNNReal_coe] at h
    have hxle : x + ((sInf (crossingSet α β) : ℝ≥0) : ℝ≥0∞)
        ≤ (0 : ℝ≥0∞) + ((sInf (crossingSet α β) : ℝ≥0) : ℝ≥0∞) := by
      rw [zero_add, ← ENNReal.coe_toNNReal hfin]
      exact ENNReal.coe_le_coe.mpr (le_csInf ⟨τ₀, hτ₀⟩ hlb)
    exact hx0 (le_antisymm
      ((ENNReal.cancel_of_ne ENNReal.coe_ne_top).add_le_add_iff_right.mp hxle)
      zero_le')

/-- Sub-additivity transports through the `ℝ≥0∞` reading: `toENN sigma` is
sub-additive when `sigma` is. -/
theorem IsSubadditive.toENN {sigma : ℝ≥0 → EReal}
    (hsub : IsSubadditive sigma) : IsSubadditive (Deviation.toENN sigma) :=
  fun u s =>
    (EReal.toENNReal_le_toENNReal (hsub u s)).trans EReal.toENNReal_add_le

/-- Super-additivity transports through the `ℝ≥0∞` reading for nonnegative
curves: `toENN beta` is super-additive when `beta` is. -/
theorem IsSuperadditive.toENN {beta : ℝ≥0 → EReal}
    (hsup : IsSuperadditive beta) (hnn : IsNonneg beta) :
    IsSuperadditive (Deviation.toENN beta) := fun u s => by
  show (beta u).toENNReal + (beta s).toENNReal ≤ (beta (u + s)).toENNReal
  rw [← EReal.toENNReal_add (hnn u) (hnn s)]
  exact EReal.toENNReal_le_toENNReal (hsup u s)

/-- Super-additivity transports through the `EReal` lift: `liftEReal g` is
super-additive when `g` is. -/
theorem IsSuperadditive.liftEReal {g : ℝ≥0 → ℝ≥0}
    (hsup : IsSuperadditive g) : IsSuperadditive (liftEReal g) :=
  fun u s => by exact_mod_cast hsup u s

namespace Deviation

/-- **Backlog from a restricted domain.** A pair served with a nonnegative
super-additive minimal service curve `beta`, the arrival allowing `α`, has
backlog bounded by the vertical deviations on `[0, τ]`, for any positive
crossing point `α τ ≤ toENN beta τ`: the sub-additive closure of `α` is
still an arrival curve, crosses no later, and its deviations are below
`α`'s. -/
theorem backlog_le_biSup_vDevAt_of_isMinimalServiceCurve
    {S : Curve → Curve → Prop} {beta : ℝ≥0 → EReal} {α : ℝ≥0 → ℝ≥0∞}
    {A D : Curve} (hβ : IsMinimalServiceCurve beta S) (hp : S A D)
    (hnn : IsNonneg beta) (harr : IsMaximalArrivalBound (liftENN ⇑A) α)
    (hsup : IsSuperadditive beta)
    {τ : ℝ≥0} (hτ : 0 < τ) (hcross : α τ ≤ toENN beta τ) :
    backlog ⇑A ⇑D ≤ ⨆ t ≤ τ, vDevAt α (toENN beta) t := by
  have hmain :=
    (backlog_le_vDev_of_isMinimalServiceCurve hβ hp hnn
        harr.subadditiveClosureE).trans_eq
      (vDev_eq_biSup_of_crossing (subadditiveClosureE_subadditive α)
        (hsup.toENN hnn) hτ ((subadditiveClosureE_le α τ).trans hcross))
  refine hmain.trans (iSup₂_mono fun t _ => ?_)
  exact vDevAt_mono (fun t' => subadditiveClosureE_le α t') le_rfl t

/-- **Delay from a restricted domain.** Under the same hypotheses, with
nondecreasing `beta`, the delay is bounded by the horizontal deviations on
`[0, τ]`. -/
theorem delay_le_biSup_hDevAt_of_isMinimalServiceCurve
    {S : Curve → Curve → Prop} {beta : ℝ≥0 → EReal} {α : ℝ≥0 → ℝ≥0∞}
    {A D : Curve} (hβ : IsMinimalServiceCurve beta S) (hp : S A D)
    (hnn : IsNonneg beta) (hmono : Monotone beta)
    (harr : IsMaximalArrivalBound (liftENN ⇑A) α)
    (hsup : IsSuperadditive beta)
    {τ : ℝ≥0} (hτ : 0 < τ) (hcross : α τ ≤ toENN beta τ) :
    delay ⇑A ⇑D ≤ ⨆ t ≤ τ, (hDevAt α (toENN beta) t : ℝ≥0∞) := by
  have hmain :=
    (delay_le_hDev_of_isMinimalServiceCurve hβ hp hnn hmono
        harr.subadditiveClosureE).trans_eq
      (hDev_eq_biSup_of_crossing (subadditiveClosureE_subadditive α)
        (hsup.toENN hnn) hτ ((subadditiveClosureE_le α τ).trans hcross))
  refine hmain.trans (iSup₂_mono fun t _ => ?_)
  exact hDevAt_mono (fun t' => subadditiveClosureE_le α t') le_rfl t

/-- **Backlog from the first crossing.** Without attainment: for monotone
`α` with a nonempty crossing set against the nonnegative monotone
super-additive `beta`, the backlog is bounded by the vertical deviations on
`[0, ℓmax]`, `ℓmax = sInf (crossingSet α (toENN beta))` — the sub-additive
closure of `α` crosses no later and its deviations sit below `α`'s. -/
theorem backlog_le_biSup_vDevAt_sInf_of_isMinimalServiceCurve
    {S : Curve → Curve → Prop} {beta : ℝ≥0 → EReal} {α : ℝ≥0 → ℝ≥0∞}
    {A D : Curve} (hβ : IsMinimalServiceCurve beta S) (hp : S A D)
    (hnn : IsNonneg beta)
    (harr : IsMaximalArrivalCurve (liftENN ⇑A) α)
    (hsup : IsSuperadditive beta)
    (hne : (crossingSet α (toENN beta)).Nonempty) :
    backlog ⇑A ⇑D
      ≤ ⨆ t ≤ sInf (crossingSet α (toENN beta)),
          vDevAt α (toENN beta) t := by
  have hle := subadditiveClosureE_le α
  have hsubset := crossingSet_anti_left (β := toENN beta) hle
  have hℓ : sInf (crossingSet (subadditiveClosureE α) (toENN beta))
      ≤ sInf (crossingSet α (toENN beta)) :=
    csInf_le_csInf (OrderBot.bddBelow _) hne hsubset
  have hclo := harr.subadditiveClosureE
  have hmain :=
    (backlog_le_vDev_of_isMinimalServiceCurve hβ hp hnn hclo.2).trans_eq
      (vDev_eq_biSup_sInf_crossingSet (subadditiveClosureE_subadditive α)
        (hsup.toENN hnn) hclo.1
        (hne.mono hsubset))
  exact hmain.trans
    (le_trans
      (iSup₂_mono fun t _ => vDevAt_mono (fun t' => hle t') le_rfl t)
      (biSup_mono fun _ ht => ht.trans hℓ))

/-- **Delay from the first crossing.** Without attainment: under the same
hypotheses, the delay is bounded by the horizontal deviations on
`[0, ℓmax]`. -/
theorem delay_le_biSup_hDevAt_sInf_of_isMinimalServiceCurve
    {S : Curve → Curve → Prop} {beta : ℝ≥0 → EReal} {α : ℝ≥0 → ℝ≥0∞}
    {A D : Curve} (hβ : IsMinimalServiceCurve beta S) (hp : S A D)
    (hnn : IsNonneg beta) (hmono : Monotone beta)
    (harr : IsMaximalArrivalCurve (liftENN ⇑A) α)
    (hsup : IsSuperadditive beta)
    (hne : (crossingSet α (toENN beta)).Nonempty) :
    delay ⇑A ⇑D
      ≤ ⨆ t ≤ sInf (crossingSet α (toENN beta)),
          (hDevAt α (toENN beta) t : ℝ≥0∞) := by
  have hle := subadditiveClosureE_le α
  have hsubset := crossingSet_anti_left (β := toENN beta) hle
  have hℓ : sInf (crossingSet (subadditiveClosureE α) (toENN beta))
      ≤ sInf (crossingSet α (toENN beta)) :=
    csInf_le_csInf (OrderBot.bddBelow _) hne hsubset
  have hclo := harr.subadditiveClosureE
  have hmain :=
    (delay_le_hDev_of_isMinimalServiceCurve hβ hp hnn hmono hclo.2).trans_eq
      (hDev_eq_biSup_sInf_crossingSet (subadditiveClosureE_subadditive α)
        (hsup.toENN hnn) hclo.1
        (hne.mono hsubset))
  exact hmain.trans
    (le_trans
      (iSup₂_mono fun t _ => hDevAt_mono (fun t' => hle t') le_rfl t)
      (biSup_mono fun _ ht => ht.trans hℓ))

/-! ## Book restatement (restricting the deviation domain)
With `ℓmax = inf {t > 0 | α t ≤ β t}` — the curves do cross, but the
infimum need not be attained — the backlog and delay of a served pair with
monotone arrival curve `α` are bounded by the deviations computed on
`[0, ℓmax]`. The strict branch — the book's reduction through the
super-additive closure and the strict-to-min-plus inclusion — is
`backlog_le_biSup_vDevAt_of_isStrictMinimalServiceCurve` and its delay
sibling in `ServiceCurveStrictMinimal`, under an affine rate bound. -/
example {S : Curve → Curve → Prop} {beta : ℝ≥0 → EReal} {α : ℝ≥0 → ℝ≥0∞}
    {A D : Curve}
    (hβ : IsMinimalServiceCurve beta S) (hp : S A D)
    (hnn : IsNonneg beta) (hmono : Monotone beta)
    (harr : IsMaximalArrivalCurve (liftENN ⇑A) α)
    (hsup : IsSuperadditive beta)
    (hne : (crossingSet α (toENN beta)).Nonempty) :
    backlog ⇑A ⇑D
        ≤ (⨆ t ≤ sInf (crossingSet α (toENN beta)),
            vDevAt α (toENN beta) t) ∧
      delay ⇑A ⇑D
        ≤ ⨆ t ≤ sInf (crossingSet α (toENN beta)),
            (hDevAt α (toENN beta) t : ℝ≥0∞) :=
  ⟨backlog_le_biSup_vDevAt_sInf_of_isMinimalServiceCurve hβ hp hnn
      harr hsup hne,
    delay_le_biSup_hDevAt_sInf_of_isMinimalServiceCurve hβ hp hnn hmono
      harr hsup hne⟩

end Deviation

end DeepWiki
