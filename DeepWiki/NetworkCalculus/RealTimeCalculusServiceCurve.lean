import DeepWiki.NetworkCalculus.RealTimeCalculusService
import DeepWiki.NetworkCalculus.ServiceCurveMinimal

/-! # Real-time calculus: lifting the RTC guarantee to a minimal service curve
The greedy-processor guarantee `Â ∗ βᵐ ≤ D̂` is proved over the real carrier `ℝ`
(`minConvReal`, `RealTimeCalculusService`); the library's service-curve theory
lives at the `EReal` level (`IsMinimalServiceCurve`, `minimalServiceRel`,
`ServiceCurveMinimal`). This file builds the carrier-crossing bridge
`((minConvReal f g t : ℝ) : EReal) = minConv (coe ∘ f) (coe ∘ g) t` for
nonnegative `f, g` (the real `ciInf` is a genuine `IsGLB`, mapped through the
continuous monotone `ℝ → EReal` coercion), then packages the readings as
`Curve`s and concludes `minimalServiceRel βᵐ_E A D` / `IsMinimalServiceCurve`
for the RTC greedy server. -/

namespace DeepWiki

open scoped NNReal

/-! ## The `minConvReal` (ℝ) ↔ `minConv` (EReal) carrier bridge -/

/-- The `EReal` coercion of a nonnegative real `minConvReal` is the `EReal`
min-plus convolution of the coerced operands:
`((minConvReal f g t : ℝ) : EReal) = minConv (coe ∘ f) (coe ∘ g) t`. The real
`ciInf` is a genuine greatest lower bound (nonnegative ⇒ bounded below),
transported through the continuous monotone coercion `ℝ → EReal`. -/
theorem coe_minConvReal_eq_minConv {f g : ℝ≥0 → ℝ}
    (hf : ∀ u, 0 ≤ f u) (hg : ∀ u, 0 ≤ g u) (t : ℝ≥0) :
    ((minConvReal f g t : ℝ) : EReal)
      = minConv (fun s => ((f s : ℝ) : EReal)) (fun s => ((g s : ℝ) : EReal)) t := by
  haveI : Nonempty {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t} := splitNonempty t
  -- the real split-sum family and its boundedness
  set F : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t} → ℝ := fun p => f p.1.1 + g p.1.2 with hF
  have hbb : BddBelow (Set.range F) :=
    bddBelow_minConvReal_of_nonneg hf hg t
  -- `minConvReal` realises the GLB of the real family
  have hglbR : IsGLB (Set.range F) (minConvReal f g t) := isGLB_ciInf hbb
  -- transport the GLB through the continuous monotone coercion `ℝ → EReal`
  have hcoeMono : Monotone ((↑) : ℝ → EReal) := fun _ _ h => EReal.coe_le_coe h
  have hglbE : IsGLB (((↑) : ℝ → EReal) '' Set.range F)
      ((minConvReal f g t : ℝ) : EReal) :=
    hglbR.isGLB_of_tendsto (hcoeMono.monotoneOn _) (Set.range_nonempty F)
      (continuous_coe_real_ereal.continuousWithinAt)
  -- the image of the real family is exactly the `EReal` split-sum family
  have himg : ((↑) : ℝ → EReal) '' Set.range F
      = Set.range fun p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t} =>
          ((f p.1.1 : ℝ) : EReal) + ((g p.1.2 : ℝ) : EReal) := by
    rw [← Set.range_comp]
    refine congrArg Set.range ?_
    funext p
    show ((f p.1.1 + g p.1.2 : ℝ) : EReal)
      = ((f p.1.1 : ℝ) : EReal) + ((g p.1.2 : ℝ) : EReal)
    exact EReal.coe_add _ _
  rw [himg] at hglbE
  exact (hglbE.ciInf_eq).symm

/-! ## Lifting the RTC guarantee to `minimalServiceRel` / `IsMinimalServiceCurve` -/

/-- The `EReal`-valued RTC minimal service curve: the pointwise coercion of the
real `βᵐ`, `t ↦ ((βᵐ t : ℝ) : EReal)`. -/
noncomputable def betaMEReal (betaM : ℝ≥0 → ℝ) : ℝ≥0 → EReal :=
  fun t => ((betaM t : ℝ) : EReal)

/-- `betaMEReal betaM t = ((betaM t : ℝ) : EReal)`: the pointwise value. -/
@[simp] theorem betaMEReal_apply (betaM : ℝ≥0 → ℝ) (t : ℝ≥0) :
    betaMEReal betaM t = ((betaM t : ℝ) : EReal) := rfl

/-- `betaMEReal betaM` is nonnegative when `betaM` is. -/
theorem betaMEReal_nonneg {betaM : ℝ≥0 → ℝ} (hβnn : ∀ u, 0 ≤ betaM u) (t : ℝ≥0) :
    (0 : EReal) ≤ betaMEReal betaM t :=
  EReal.coe_nonneg.mpr (hβnn t)

/-- **The RTC greedy server's arrival/departure pair lies in
`minimalServiceRel βᵐ_E`.** Given `Curve`s `A, D` whose `EReal` views are the
RTC readings `Â = Areal 0 ·` and `D̂ = Dreal 0 ·` (the `hAval`/`hDval`
hypotheses), an RTC greedy processor (Chasles, `b 0 = 0`, residuals bounded
above, monotone capacity) that guarantees `βᵐ` (Definition 9.1) with `βᵐ ≥ 0`
yields the `EReal`-level min-plus service pair `A ≥ D ≥ A ∗ βᵐ_E`. The real
guarantee `A ∗ βᵐ ≤ D ≤ A` is crossed to `EReal` through
`coe_minConvReal_eq_minConv`. -/
theorem minimalServiceRel_of_isRtcGreedy
    {Areal C Dreal C' : ℝ≥0 → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {betaM : ℝ≥0 → ℝ}
    {A D : Curve}
    (hAval : ∀ t, ((A t : ℝ≥0) : ℝ) = Areal 0 t)
    (hDval : ∀ t, ((D t : ℝ≥0) : ℝ) = Dreal 0 t)
    (hA : IsChasles Areal) (hC : IsChasles C) (hb0 : b 0 = 0)
    (hg : IsRtcGreedy Areal C Dreal C' b)
    (hbdd : ∀ t : ℝ≥0,
      BddAbove (Set.range fun u : {u : ℝ≥0 // u ≤ t} => C 0 u.1 - Areal 0 u.1))
    (hCmono : Monotone (fun u => C 0 u)) (hβnn : ∀ u, 0 ≤ betaM u)
    (hguar : GuaranteesRtcMinService C betaM) :
    minimalServiceRel (betaMEReal betaM) A D := by
  have hAnn : ∀ u, 0 ≤ Areal 0 u := fun u => by rw [← hAval u]; exact (A u).coe_nonneg
  refine mem_minimalServiceRel_iff.mpr ⟨?_, ?_⟩
  · -- causality `D ≤ A` from `D̂ ≤ Â`
    intro t
    have hle : Dreal 0 t ≤ Areal 0 t :=
      departure_le_arrival_of_isRtcGreedy hA hC hb0 hg hbdd hCmono hAnn t
    have : ((D t : ℝ≥0) : ℝ) ≤ ((A t : ℝ≥0) : ℝ) := by rw [hAval t, hDval t]; exact hle
    exact_mod_cast this
  · -- service bound `A ∗ βᵐ_E ≤ D` from `A ∗ βᵐ ≤ D̂`, crossed to `EReal`
    intro t
    -- `curveEReal A` is the coerced reading `Areal 0 ·`
    have hAeq : curveEReal A = fun u => ((Areal 0 u : ℝ) : EReal) := by
      funext u; rw [curveEReal_apply, hAval u]
    have hbridge :
        minConv (curveEReal A) (betaMEReal betaM) t
          = ((minConvReal (fun u => Areal 0 u) betaM t : ℝ) : EReal) := by
      rw [hAeq]; exact (coe_minConvReal_eq_minConv hAnn hβnn t).symm
    rw [hbridge]
    have hreal : minConvReal (fun u => Areal 0 u) betaM t ≤ Dreal 0 t :=
      minConvReal_le_departure_of_isRtcGreedy hA hC hb0 hg hbdd hAnn hβnn hguar t
    have : ((minConvReal (fun u => Areal 0 u) betaM t : ℝ) : EReal)
        ≤ ((Dreal 0 t : ℝ) : EReal) := EReal.coe_le_coe hreal
    rw [curveEReal_apply, hDval t]; exact this

/-- **`IsMinimalServiceCurve` for the RTC greedy server (singleton relation).**
The RTC greedy server, presented as the singleton served-pair relation
`S = fun A' D' => A' = A ∧ D' = D`, offers the `EReal` minimal service curve
`βᵐ_E`: end-to-end, the greedy-processor equations + Chasles + capacity
domination (Definition 9.1) + `Curve` regularity yield `A ∗ βᵐ_E ≤ D`. -/
theorem isMinimalServiceCurve_of_isRtcGreedy
    {Areal C Dreal C' : ℝ≥0 → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {betaM : ℝ≥0 → ℝ}
    {A D : Curve}
    (hAval : ∀ t, ((A t : ℝ≥0) : ℝ) = Areal 0 t)
    (hDval : ∀ t, ((D t : ℝ≥0) : ℝ) = Dreal 0 t)
    (hA : IsChasles Areal) (hC : IsChasles C) (hb0 : b 0 = 0)
    (hg : IsRtcGreedy Areal C Dreal C' b)
    (hbdd : ∀ t : ℝ≥0,
      BddAbove (Set.range fun u : {u : ℝ≥0 // u ≤ t} => C 0 u.1 - Areal 0 u.1))
    (hCmono : Monotone (fun u => C 0 u)) (hβnn : ∀ u, 0 ≤ betaM u)
    (hguar : GuaranteesRtcMinService C betaM) :
    IsMinimalServiceCurve (betaMEReal betaM) (fun A' D' => A' = A ∧ D' = D) := by
  rintro A' D' ⟨rfl, rfl⟩
  exact (mem_minimalServiceRel_iff.mp
    (minimalServiceRel_of_isRtcGreedy hAval hDval hA hC hb0 hg hbdd hCmono hβnn hguar)).2

end DeepWiki
