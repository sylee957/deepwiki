import DeepWiki.SymbolicIntegration.Engine.RischTowerLrt
import DeepWiki.SymbolicIntegration.Engine.LimitedIntegrateSingle
import DeepWiki.SymbolicIntegration.Engine.RecursiveCoefficient
import DeepWiki.SymbolicIntegration.Engine.RecursiveMonomialCase

/-! # Recursive LRT Risch tower step

The tower step of the recursive LRT Risch solver (`instCRischLevelLrtTower`, paired with the base
`instCRischLevelLrtPrimitive`). Given an LRT operation and contract for the coefficient field, build one
for `(DenseFrac β)(t)`. The polynomial part's coefficient integration recurses into `CRischLevelLrt β`'s
log-free integrator `integrateRationalLrt` (descent-free `K`-level, by the ∀E ⇒ K bridge
`integrateRationalLrt_sound`) — so the whole tower stays on the LRT track (its reduced frontier
is `PrimitiveFrontierLrt`, not the undischargeable rational `PrimitiveFrontier`).

Everything reuses the *generic* degree-raising coefficient recursion (`cIntegratePrimPolyDegRaise`,
`cIntegratePrimPolyDegRaiseG_sound` — result-type-agnostic, telescoping soundness): only the coefficient
integrator `limInt` changes to `CRischLevelLrt.integrateRationalLrt` (wrapped `b ↦ (b, 0)`; the
degree-raising `c` is used when the base level supplies a `(b,c)` limited integrator). The special-part
soundness `towerPrimitiveCaseLrt_specialSound` and the log-tower special identity `tower_special_identityLrt`
close the polynomial part; the reduced part goes through the root-free assembler `cIntegrateCaseLrt`. -/

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac Polynomial
open scoped Differential

universe u v

variable {β : Type u} [CField β] [CFieldSpec.{u,v} β] [CDiffField β] [CDiffFieldSpec.{u,v} β]
  [CFieldDomain β DensePoly] [CPolyGcd DensePoly β] [CPolySplitFactor DensePoly β]
  [CPolySquarefree DensePoly β] [CPolyResultant DensePoly] [CPolySubresultant DensePoly]
  [Algebra ℚ (CFieldSpec.K β)] [CharZero (CFieldSpec.K β)]
  [CRischLevelLrt β]

/-- Integrate a coefficient `c ∈ DenseFrac β = β(s)` by recursing into
`CRischLevelLrt β.integrateRationalLrt` (the log-free LRT integrator, whose soundness is descent-free
`K`-level via the ∀E ⇒ K bridge) with the carrier derivation `Ds = [1]`, reassembling via `DenseFrac β` field
division. The coefficient integrator the LRT tower step feeds (wrapped) to `cIntegratePrimPolyDegRaise`,
staying on the LRT track. -/
def towerCoeffIntegrateLrt (c : DenseFrac β) : Option (DenseFrac β) :=
  ((inferInstance : CRischLevelLrt β).integrateRationalLrt [CCommRing.one]
    (CFrac.num c) (CFrac.den c)).map fun bd =>
    CField.div (CFrac.ofPoly bd.1) (CFrac.ofPoly bd.2)

/-- The LRT tower's recursive coefficient operation. -/
private def towerCoeffLimitedIntegrateLrt (η c : DenseFrac β) : Option (DenseFrac β × DenseFrac β) :=
  match (inferInstance : CRischLevelLrt β).limitedIntegrateSingle (CFrac.num c) (CFrac.den c)
      (CFrac.num η) (CFrac.den η) with
  | some ((bn, bd), cc) => some (CField.div (CFrac.ofPoly bn) (CFrac.ofPoly bd), CFrac.ofPoly [cc])
  | none => (towerCoeffIntegrateLrt (β := β) c).map fun b => (b, CCommRing.zero)

/-- The LRT tower's recursive coefficient operation, including its optional single-`w` reduction. -/
def towerCoefficientIntegratorLrt : CRecursiveCoefficientIntegrator (DenseFrac β) where
  integrate := towerCoeffIntegrateLrt
  limitedIntegrate := towerCoeffLimitedIntegrateLrt

/-- LRT coefficient-recursion soundness: `toK (cderiv b) = toK c` in
`RatFunc (CFieldSpec.K β)`, reassembling `integrateRationalLrt_sound` (descent-free `K`-level) through the
`DenseFrac β` field division that `towerCoeffIntegrateLrt` performs. -/
theorem towerCoeffIntegrateLrt_sound [LawfulCRischLevelLrt (inferInstance : CRischLevelLrt β)]
    (c b : DenseFrac β) (h : towerCoeffIntegrateLrt c = some b) :
    CFieldSpec.toK (CDiffField.cderiv b) = CFieldSpec.toK c := by
  unfold towerCoeffIntegrateLrt at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨⟨bn, bd⟩, hint, rfl⟩ := h
  have hsound := CRischLevelLrt.integrateRationalLrt_sound
    (inferInstance : CRischLevelLrt β) [CCommRing.one]
    (CFrac.num c) (CFrac.den c) bn bd hint
  have hcd : CFieldSpec.toK (CDiffField.cderiv
      (CField.div (CFrac.ofPoly (F := DenseFrac) bn) (CFrac.ofPoly (F := DenseFrac) bd)))
      = towerFractionFieldDeriv [CCommRing.one]
          (CFieldSpec.toK
            (CField.div (CFrac.ofPoly (F := DenseFrac) bn) (CFrac.ofPoly (F := DenseFrac) bd))) := by
    rw [CDiffFieldSpec.toK_cderiv]
    change extendDeriv (Differential.implicitDeriv
        (CPoly.toPoly (CPoly.one : DensePoly β))) _ =
      towerFractionFieldDeriv [CCommRing.one] _
    rw [towerFractionFieldDeriv]
    rw [CPoly.toPoly_one]
    have hone : DensePoly.toPoly ([CCommRing.one] : DensePoly β) = 1 := by
      simp only [denote]
      simp
    rw [hone]
  have htoK_embed : ∀ num : DensePoly β,
      CFieldSpec.toK (CFrac.ofPoly (F := DenseFrac) num) = CFrac.am β (toPoly num) := by
    intro num
    simpa only [toPoly_list_eq] using
      (CFrac.toK_ofPoly (F := DenseFrac) (P := DensePoly) num)
  have htoK_c : CFieldSpec.toK c
      = CFrac.am β (toPoly (CFrac.num c)) / CFrac.am β (toPoly (CFrac.den c)) := by
    change CFrac.toRatFunc c = _
    rw [CFrac.toRatFunc_eq_div]
    simp only [toPoly_list_eq]
  rw [hcd, CFieldSpec.toK_div, htoK_embed bn, htoK_embed bd, htoK_c]
  exact hsound

/-- The LRT recursive coefficient operation satisfies the generic soundness contract. -/
instance instLawfulCRecursiveCoefficientIntegratorLrt
    [LawfulCRischLevelLrt (inferInstance : CRischLevelLrt β)] :
    LawfulCRecursiveCoefficientIntegrator (towerCoefficientIntegratorLrt (β := β)) where
  sound c b h := towerCoeffIntegrateLrt_sound c b h

/-- The tower primitive-polynomial stage driven by an explicit recursive coefficient operation. -/
def recursiveTowerPolyIntegrateLrt {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    (I : CRecursiveCoefficientIntegrator (DenseFrac β))
    (η : DenseFrac β) (p : P (DenseFrac β)) : Option (P (DenseFrac β)) :=
  cIntegratePrimPolyDegRaise η (fun c => I.limitedIntegrate η c) (CPolyEngine.cdeg p + 2) p

omit [CPolyGcd DensePoly β] [CPolySplitFactor DensePoly β] [CPolySquarefree DensePoly β]
  [CPolyResultant DensePoly] [CPolySubresultant DensePoly] [CharZero (CFieldSpec.K β)]
  [CRischLevelLrt β] in
theorem recursiveTowerPolyIntegrateLrt_sound {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    [LawfulCPolyEngine.{u,v} P] (I : CRecursiveCoefficientIntegrator (DenseFrac β))
    (η : DenseFrac β) (p q : P (DenseFrac β))
    (h : recursiveTowerPolyIntegrateLrt I η p = some q) :
    Differential.implicitDeriv (Polynomial.C (CFieldSpec.toK η)) (CPoly.toPoly q) =
      CPoly.toPoly p :=
  cIntegratePrimPolyDegRaiseG_sound η
    (fun c => I.limitedIntegrate η c)
    (CPolyEngine.cdeg p + 2) p q h

/-- The LRT tower's polynomial-stage specialization of `recursiveTowerPolyIntegrateLrt`. -/
def towerPolyIntegrateLrt {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    (η : DenseFrac β) (p : P (DenseFrac β)) : Option (P (DenseFrac β)) :=
  recursiveTowerPolyIntegrateLrt (towerCoefficientIntegratorLrt (β := β)) η p

/-- The LRT tower step's polynomial-part soundness. -/
theorem towerPolyIntegrateLrt_sound {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    [LawfulCPolyEngine.{u,v} P] (η : DenseFrac β) (p q : P (DenseFrac β))
    (h : towerPolyIntegrateLrt η p = some q) :
    Differential.implicitDeriv (Polynomial.C (CFieldSpec.toK η)) (CPoly.toPoly q) =
      CPoly.toPoly p :=
  recursiveTowerPolyIntegrateLrt_sound (towerCoefficientIntegratorLrt (β := β)) η p q h

omit [CPolyGcd DensePoly β] [CPolySplitFactor DensePoly β] [CPolySquarefree DensePoly β]
  [CPolyResultant DensePoly] [CPolySubresultant DensePoly] [CharZero (CFieldSpec.K β)]
  [CRischLevelLrt β] in
private theorem recursiveTowerSpecialIdentityLrt (I : CRecursiveCoefficientIntegrator (DenseFrac β))
    (Dt fp qp : DensePoly (DenseFrac β)) (hDt : toPoly Dt = 1)
    (h : recursiveTowerPolyIntegrateLrt I CCommRing.one fp = some qp) :
    towerFractionFieldDeriv Dt (fieldFrac qp [CCommRing.one]) = fieldFrac fp [CCommRing.one] := by
  have hpoly : Differential.implicitDeriv (Polynomial.C (CFieldSpec.toK CCommRing.one))
      (toPoly qp) = toPoly fp := by
    simpa only [toPoly_list_eq] using recursiveTowerPolyIntegrateLrt_sound I CCommRing.one fp qp h
  rw [CFieldSpec.toK_one, Polynomial.C_1] at hpoly
  have hone : toPoly ([CCommRing.one] : DensePoly (DenseFrac β)) = 1 := by
    simp only [denote, map_one, mul_zero, add_zero]
  have hbridge : towerFractionFieldDeriv Dt (CFrac.am (DenseFrac β) (toPoly qp))
      = CFrac.am (DenseFrac β) (Differential.implicitDeriv (toPoly Dt) (toPoly qp)) := by
    have hd := towerFractionFieldDerivG_div Dt (toPoly qp) 1
    simp only [map_one, div_one, one_pow, Derivation.map_one_eq_zero, map_zero, mul_zero, sub_zero,
      mul_one] at hd
    exact hd
  simp only [fieldFrac, hone, map_one, div_one]
  rw [hbridge, hDt, hpoly]

variable [CRischField (DenseFrac β)]
  [CPolyGcd DensePoly (DenseFrac β)]
  [CPolySplitFactor DensePoly (DenseFrac β)]
  [LawfulCPolySplitFactor DensePoly (DenseFrac β)] [CPolySquarefree DensePoly (DenseFrac β)]

/-- The primitive tower monomial stage parameterized by its recursive coefficient operation. -/
def towerPrimitiveRecursiveMonomialCaseLrt :
    CRecursiveMonomialCase DensePoly (DenseFrac β) where
  integrateSpecial I Dt fp b _ds :=
    if cisZero b && cisZero (csub Dt [CCommRing.one]) then
      match recursiveTowerPolyIntegrateLrt I CCommRing.one fp with
      | none => none
      | some qp => some (qp, [CCommRing.one])
    else none
  postprocessNormal := (primitiveGuardedCase (α := DenseFrac β)).postprocessNormal

/-- The LRT tower primitive monomial case, supplied with its recursive coefficient operation. -/
def towerPrimitiveCaseLrt : CMonomialCase DensePoly (DenseFrac β) :=
  (towerPrimitiveRecursiveMonomialCaseLrt (β := β)).withCoefficient
    (towerCoefficientIntegratorLrt (β := β))

omit [CPolyGcd DensePoly (DenseFrac β)] [CPolySquarefree DensePoly (DenseFrac β)] in
/-- LRT tower primitive special-part soundness, the tower-recursion analogue of `primitiveGuardedCase_specialSound`.
Under the guard (`b = 0`, `Dθ = 1`) the LRT polynomial recursion `towerPolyIntegrateLrt` yields `qp` with
`D_tower(⟦qp⟧) = ⟦fp⟧` (`tower_special_identityLrt`), and `canonicalReconstruction_of_charZero` (special term
vanishing, `b = 0`) closes; off the guard the hook returns `none`. This is the `specialSound` field of the LRT
tower instance. -/
theorem towerPrimitiveCaseLrt_specialSound
    (Dt a d snum sden : DensePoly (DenseFrac β)) (hd0 : toPoly d ≠ 0)
    (hhook : (towerPrimitiveCaseLrt (β := β)).integrateSpecial Dt (crPoly Dt a d) (crSpecNum Dt a d)
      (crSpecDen Dt a d) = some (snum, sden)) :
    toPoly sden ≠ 0 ∧ ∃ v : RatFunc (CFieldSpec.K (DenseFrac β)),
      towerFractionFieldDeriv Dt (fieldFrac snum sden) = v ∧
      v + fieldFrac (crNormNum Dt a d) (crNormDen Dt a d) = fieldFrac a d := by
  simp only [towerPrimitiveCaseLrt, CRecursiveMonomialCase.withCoefficient,
    towerPrimitiveRecursiveMonomialCaseLrt] at hhook
  by_cases hguard : (cisZero (crSpecNum Dt a d) && cisZero (csub Dt [CCommRing.one])) = true
  · rw [if_pos hguard] at hhook
    rw [Bool.and_eq_true] at hguard
    obtain ⟨hb, hDt1g⟩ := hguard
    change (match towerPolyIntegrateLrt CCommRing.one (crPoly Dt a d) with
      | none => none
      | some qp => some (qp, [CCommRing.one])) = some (snum, sden) at hhook
    rcases hqp : towerPolyIntegrateLrt CCommRing.one (crPoly Dt a d) with _ | qp
    · rw [hqp] at hhook; simp at hhook
    · rw [hqp] at hhook
      simp only [Option.some.injEq, Prod.mk.injEq] at hhook
      obtain ⟨rfl, rfl⟩ := hhook
      have hDt1 : toPoly Dt = 1 := by
        have hh := (cisZeroG_iff (csub Dt [CCommRing.one])).mp hDt1g
        simpa only [denote, map_one, mul_zero, add_zero, sub_eq_zero] using hh
      exact primitiveSpecialSoundCore Dt a d qp hd0 hb
        (recursiveTowerSpecialIdentityLrt (towerCoefficientIntegratorLrt (β := β))
          Dt (crPoly Dt a d) qp hDt1 (by simpa [towerPolyIntegrateLrt] using hqp))
  · rw [if_neg hguard] at hhook; simp at hhook

/- A recursive primitive tower case has the ordinary monomial-stage special-part identity. -/
omit [CPolyGcd DensePoly β] [CPolySplitFactor DensePoly β] [CPolySquarefree DensePoly β]
  [CPolyResultant DensePoly] [CPolySubresultant DensePoly] [CharZero (CFieldSpec.K β)]
  [CRischLevelLrt β] [CPolyGcd DensePoly (DenseFrac β)] [CPolySplitFactor DensePoly (DenseFrac β)]
  [LawfulCPolySplitFactor DensePoly (DenseFrac β)] [CPolySquarefree DensePoly (DenseFrac β)] in
theorem towerPrimitiveRecursiveMonomialCaseLrt_special_sound
    (I : CRecursiveCoefficientIntegrator (DenseFrac β))
    (Dt fp b ds snum sden : DensePoly (DenseFrac β))
    (hhook : (towerPrimitiveRecursiveMonomialCaseLrt (β := β)).integrateSpecial I Dt fp b ds =
      some (snum, sden)) :
    toPoly sden ≠ 0 ∧
      towerFractionFieldDerivP Dt (fieldFracP snum sden) =
        fieldFracP fp CPoly.one + fieldFracP b ds := by
  simp only [towerPrimitiveRecursiveMonomialCaseLrt] at hhook
  by_cases hguard : (cisZero b && cisZero (csub Dt [CCommRing.one])) = true
  · rw [if_pos hguard] at hhook
    rw [Bool.and_eq_true] at hguard
    obtain ⟨hb, hDt1g⟩ := hguard
    rcases hqp : recursiveTowerPolyIntegrateLrt I CCommRing.one fp with _ | qp
    · rw [hqp] at hhook
      simp at hhook
    · rw [hqp] at hhook
      simp only [Option.some.injEq, Prod.mk.injEq] at hhook
      obtain ⟨rfl, rfl⟩ := hhook
      have hDt1 : toPoly Dt = 1 := by
        have hh := (cisZeroG_iff (csub Dt [CCommRing.one])).mp hDt1g
        simpa only [denote, map_one, mul_zero, add_zero, sub_eq_zero] using hh
      have hpoly := recursiveTowerSpecialIdentityLrt I Dt fp qp hDt1 hqp
      constructor
      · have hone : toPoly ([CCommRing.one] : DensePoly (DenseFrac β)) = 1 := by
          simp only [denote, map_one, mul_zero, add_zero]
        rw [hone]
        exact one_ne_zero
      · simp only [fieldFracP, towerFractionFieldDerivP, toPoly_list_eq]
        rw [show (CPoly.one : DensePoly (DenseFrac β)) = [CCommRing.one] from rfl]
        have hb0 : toPoly b = 0 := (cisZeroG_iff b).mp hb
        rw [hb0, map_zero, zero_div, add_zero]
        simpa only [towerFractionFieldDeriv] using hpoly
  · rw [if_neg hguard] at hhook
    simp at hhook

/-- The primitive LRT tower case realizes the generic recursive monomial-stage contract. -/
instance instLawfulCRecursiveMonomialCaseTowerPrimitiveLrt :
    LawfulCRecursiveMonomialCase (towerPrimitiveRecursiveMonomialCaseLrt (β := β)) where
  lawful I _ := by
    constructor
    · intro Dt fp b ds snum sden hrun
      simpa only [toPoly_list_eq] using
        towerPrimitiveRecursiveMonomialCaseLrt_special_sound I Dt fp b ds snum sden hrun
    · intro Dt cn dn before after hbefore hrun
      change (primitiveGuardedCase (α := DenseFrac β)).postprocessNormal Dt before = some after at hrun
      exact LawfulCMonomialCase.postprocessNormal_sound (C := primitiveGuardedCase) Dt cn dn
        before after hbefore hrun
    · intro Dt before after hden hrun
      change (primitiveGuardedCase (α := DenseFrac β)).postprocessNormal Dt before = some after at hrun
      exact LawfulCMonomialCase.postprocessNormal_den_nonzero (C := primitiveGuardedCase) Dt
        before after hden hrun

/-- The LRT tower step operation: `CRischLevelLrt (DenseFrac β)` from a below-level operation and contract
and this level's reduced LRT frontier `[PrimitiveFrontierLrt (DenseFrac β)]`.
With the base (`instCRischLevelLrtPrimitive`) the LRT solver resolves at every tower depth by recursion:
the re-based recursion, now with a dischargeable frontier at every level. `specialSound` is the LRT coefficient
recursion (`towerPrimitiveCaseLrt_specialSound`); `reducedSoundLrt` is `PrimitiveFrontierLrt.hreducedLrt`. -/
instance instCRischLevelLrtTower [PrimitiveFrontierLrt (DenseFrac β)] :
    CRischLevelLrt (DenseFrac β) where
  case := towerPrimitiveCaseLrt
  limitedIntegrateSingle := fun _ _ _ _ => none

/-- The recursive LRT tower operation satisfies its algebraic-residue contract. -/
instance instLawfulCRischLevelLrtTower [PrimitiveFrontierLrt (DenseFrac β)] :
    LawfulCRischLevelLrt (inferInstance : CRischLevelLrt (DenseFrac β)) where
  specialSound := fun Dt a d snum sden hd0 hhook =>
    towerPrimitiveCaseLrt_specialSound Dt a d snum sden hd0 hhook
  reducedSoundLrt := fun Dt a d hd0 hDt0 => PrimitiveFrontierLrt.hreducedLrt Dt a d hd0 hDt0
  reducedDenNonzero := fun Dt a d hd0 hDt0 =>
    PrimitiveFrontierLrt.hreducedDenNonzero Dt a d hd0 hDt0

-- The LRT tower solver resolves at depth 2 by recursion; the step instance chains on itself.
noncomputable example [PrimitiveFrontierLrt (DenseFrac β)]
    [CPolyGcd DensePoly (DenseFrac (DenseFrac β))]
    [CPolySplitFactor DensePoly (DenseFrac (DenseFrac β))]
    [LawfulCPolySplitFactor DensePoly (DenseFrac (DenseFrac β))]
    [CPolySquarefree DensePoly (DenseFrac (DenseFrac β))]
    [CRischField (DenseFrac (DenseFrac β))]
    [PrimitiveFrontierLrt (DenseFrac (DenseFrac β))] :
    LawfulCRischLevelLrt (inferInstance : CRischLevelLrt (DenseFrac (DenseFrac β))) := inferInstance

end DeepWiki.SymbolicIntegration
