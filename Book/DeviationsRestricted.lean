import Book.Additivity
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

/-- **Restricting the vertical-deviation domain.** At a positive crossing
point `τ` of sub-additive `α` against super-additive `β`, the vertical
deviation can be computed on `[0, τ]`: `vDev α β = ⨆ t ≤ τ, vDevAt α β t`. -/
theorem vDev_eq_biSup_of_crossing {α β : ℝ≥0 → ℝ≥0∞}
    (hsub : IsSubadditive α) (hsup : IsSuperadditive β)
    {τ : ℝ≥0} (hτ : 0 < τ) (hcross : α τ ≤ β τ) :
    vDev α β = ⨆ t ≤ τ, vDevAt α β t := by
  apply le_antisymm
  · refine iSup_le fun t => ?_
    obtain ⟨q, r, rfl, hrτ⟩ := exists_eq_nsmul_add_lt_of_pos hτ t
    exact le_trans (vDevAt_nsmul_add_le hsub hsup hcross q r)
      (le_iSup₂ (f := fun t (_ : t ≤ τ) => vDevAt α β t) r hrτ.le)
  · exact iSup₂_le fun t _ => vDevAt_le_vDev α β t

/-- Crossing-point domination (horizontal): admissible shifts at `r`
transfer to `q • τ + r`, so the pointwise horizontal deviation at
`q • τ + r` is dominated by the one at `r`. -/
theorem hDevAt_nsmul_add_le {α β : ℝ≥0 → ℝ≥0∞}
    (hsub : IsSubadditive α) (hsup : IsSuperadditive β)
    {τ : ℝ≥0} (hcross : α τ ≤ β τ) (q : ℕ) (r : ℝ≥0) :
    (hDevAt α β (q • τ + r) : ℝ≥0∞) ≤ hDevAt α β r := by
  refine le_iInf fun d => ?_
  refine iInf_le_of_le ⟨d.1, ?_⟩ le_rfl
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
    (hDev α β : ℝ≥0∞) = ⨆ t ≤ τ, (hDevAt α β t : ℝ≥0∞) := by
  apply le_antisymm
  · refine iSup_le fun t => ?_
    obtain ⟨q, r, rfl, hrτ⟩ := exists_eq_nsmul_add_lt_of_pos hτ t
    exact le_trans (hDevAt_nsmul_add_le hsub hsup hcross q r)
      (le_iSup₂ (f := fun t (_ : t ≤ τ) => (hDevAt α β t : ℝ≥0∞)) r hrτ.le)
  · exact iSup₂_le fun t _ => hDevAt_le_hDev α β t

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
  fun u s => by
    show ((g u : ℝ) : EReal) + ((g s : ℝ) : EReal) ≤ ((g (u + s) : ℝ) : EReal)
    rw [← EReal.coe_add]
    exact_mod_cast hsup u s

namespace Deviation

/-- **Backlog from a restricted domain.** A pair served with a nonnegative
super-additive minimal service curve `beta`, the arrival allowing a
sub-additive `α`, has backlog bounded by the vertical deviations on `[0, τ]`,
for any positive crossing point `α τ ≤ toENN beta τ`. -/
theorem backlog_le_biSup_vDevAt_of_isMinimalServiceCurve
    {S : Curve → Curve → Prop} {beta : ℝ≥0 → EReal} {α : ℝ≥0 → ℝ≥0∞}
    {A D : Curve} (hβ : IsMinimalServiceCurve beta S) (hp : S A D)
    (hnn : IsNonneg beta) (harr : IsMaximalArrivalCurve (liftENN ⇑A) α)
    (hsub : IsSubadditive α) (hsup : IsSuperadditive beta)
    {τ : ℝ≥0} (hτ : 0 < τ) (hcross : α τ ≤ toENN beta τ) :
    backlog ⇑A ⇑D ≤ ⨆ t ≤ τ, vDevAt α (toENN beta) t :=
  (backlog_le_vDev_of_isMinimalServiceCurve hβ hp hnn harr).trans_eq
    (vDev_eq_biSup_of_crossing hsub (hsup.toENN hnn) hτ hcross)

/-- **Delay from a restricted domain.** Under the same hypotheses, with
nondecreasing `beta`, the delay is bounded by the horizontal deviations on
`[0, τ]`. -/
theorem delay_le_biSup_hDevAt_of_isMinimalServiceCurve
    {S : Curve → Curve → Prop} {beta : ℝ≥0 → EReal} {α : ℝ≥0 → ℝ≥0∞}
    {A D : Curve} (hβ : IsMinimalServiceCurve beta S) (hp : S A D)
    (hnn : IsNonneg beta) (hmono : Monotone beta)
    (harr : IsMaximalArrivalCurve (liftENN ⇑A) α)
    (hsub : IsSubadditive α) (hsup : IsSuperadditive beta)
    {τ : ℝ≥0} (hτ : 0 < τ) (hcross : α τ ≤ toENN beta τ) :
    delay ⇑A ⇑D ≤ ⨆ t ≤ τ, (hDevAt α (toENN beta) t : ℝ≥0∞) :=
  (delay_le_hDev_of_isMinimalServiceCurve hβ hp hnn hmono harr).trans_eq
    (hDev_eq_biSup_of_crossing hsub (hsup.toENN hnn) hτ hcross)

/-! ## Book restatement (restricting the deviation domain)
With `ℓmax = inf {t > 0 | α t ≤ β t}` itself a positive crossing point (the
infimum attained), the backlog and delay of a served pair are bounded by the
deviations computed on `[0, ℓmax]`. Two narrowings against the book: `α`
is assumed sub-additive outright (the book reduces to this via the
sub-additive closure, not yet transported to the `ℝ≥0∞` carrier); and at a
non-attained infimum the book's bound needs a further limiting argument
(recoverable for monotone `α`, `β`). The strict branch — the book's
reduction through the super-additive closure and the strict-to-min-plus
inclusion — is `backlog_le_biSup_vDevAt_of_isStrictMinimalServiceCurve` and
its delay sibling in `ServiceCurveStrictMinimal`, under an affine rate
bound. -/
example {S : Curve → Curve → Prop} {beta : ℝ≥0 → EReal} {α : ℝ≥0 → ℝ≥0∞}
    {A D : Curve}
    (hβ : IsMinimalServiceCurve beta S) (hp : S A D)
    (hnn : IsNonneg beta) (hmono : Monotone beta)
    (harr : IsMaximalArrivalCurve (liftENN ⇑A) α)
    (hsub : IsSubadditive α) (hsup : IsSuperadditive beta)
    {ℓmax : ℝ≥0}
    (_hℓ : ℓmax = sInf {t : ℝ≥0 | 0 < t ∧ α t ≤ toENN beta t})
    (hτ : 0 < ℓmax) (hcross : α ℓmax ≤ toENN beta ℓmax) :
    backlog ⇑A ⇑D ≤ (⨆ t ≤ ℓmax, vDevAt α (toENN beta) t) ∧
      delay ⇑A ⇑D ≤ ⨆ t ≤ ℓmax, (hDevAt α (toENN beta) t : ℝ≥0∞) :=
  ⟨backlog_le_biSup_vDevAt_of_isMinimalServiceCurve hβ hp hnn harr hsub
      hsup hτ hcross,
    delay_le_biSup_hDevAt_of_isMinimalServiceCurve hβ hp hnn hmono harr hsub
      hsup hτ hcross⟩

end Deviation

end DeepWiki
