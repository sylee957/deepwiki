import DeepWiki.SymbolicIntegration.Engine.RischTowerLrt
import DeepWiki.SymbolicIntegration.Engine.RischFieldSpec
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
soundness `towerPrimitiveCaseLrt_specialSound` and the log-tower special identity `recursiveTowerSpecialIdentityLrt`
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
private def towerCoeffLimitedIntegrateLrt [L : CLimitedIntegrateSingleLrt β]
    (η c : DenseFrac β) : Option (DenseFrac β × DenseFrac β) :=
  match L.run (CFrac.num c) (CFrac.den c)
      (CFrac.num η) (CFrac.den η) with
  | some ((bn, bd), cc) => some (CField.div (CFrac.ofPoly bn) (CFrac.ofPoly bd), CFrac.ofPoly [cc])
  | none => (towerCoeffIntegrateLrt (β := β) c).map fun b => (b, CCommRing.zero)

/-- The LRT tower's recursive coefficient operation, including its optional single-`w` reduction. -/
def towerCoefficientIntegratorLrt [CLimitedIntegrateSingleLrt β] : CRecursiveCoefficientIntegrator (DenseFrac β) where
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
    [L : CLimitedIntegrateSingleLrt β]
    [LawfulCRischLevelLrt (inferInstance : CRischLevelLrt β)] :
    LawfulCRecursiveCoefficientIntegrator (towerCoefficientIntegratorLrt (β := β)) where
  sound c b h := towerCoeffIntegrateLrt_sound c b h

/-- Domain where ordinary tower coefficient integration descends to a complete log-free lower-level problem. -/
def towerRecursiveCoefficientDomain (domain : RationalLrtDomain β) :
    RecursiveCoefficientDomain (α := DenseFrac β) := fun c =>
  domain [CCommRing.one] (CFrac.num c) (CFrac.den c) ∧
    IsRationallyIntegrableLrt [CCommRing.one] (CFrac.num c) (CFrac.den c)

/-- Log-free lower-level completeness lifts through `DenseFrac` to ordinary coefficient completeness. -/
instance instCompleteCRecursiveCoefficientIntegratorLrt
    [L : CLimitedIntegrateSingleLrt β]
    [LawfulCRischLevelLrt (inferInstance : CRischLevelLrt β)]
    (domain : RationalLrtDomain β)
    [CompleteCRischLevelRationalLrt (inferInstance : CRischLevelLrt β) domain] :
    CompleteCRecursiveCoefficientIntegrator (towerCoefficientIntegratorLrt (β := β))
      (towerRecursiveCoefficientDomain domain) where
  complete c hdomain _ := by
    have hcden : toPoly (CFrac.den c) ≠ 0 := by
      simpa only [toPoly_list_eq] using CFrac.toPoly_den_ne_zero_generic c
    obtain ⟨bn, bd, hrun⟩ := CompleteCRischLevelRationalLrt.relative_complete
      (C := (inferInstance : CRischLevelLrt β)) (domain := domain)
      [CCommRing.one] (CFrac.num c) (CFrac.den c) hdomain.1 hcden hdomain.2
    let b : DenseFrac β := CField.div (CFrac.ofPoly bn) (CFrac.ofPoly bd)
    refine ⟨b, ?_⟩
    simp only [towerCoefficientIntegratorLrt, towerCoeffIntegrateLrt, hrun, Option.map_some, b]

/-- LRT limited coefficient recursion returns `c = D b + r·η` with constant `r`. -/
theorem towerCoeffLimitedIntegrateLrt_sound
    [L : CLimitedIntegrateSingleLrt β] [LawfulCLimitedIntegrateSingleLrt L]
    [LawfulCRischLevelLrt (inferInstance : CRischLevelLrt β)]
    (η c b r : DenseFrac β) (h : towerCoeffLimitedIntegrateLrt η c = some (b, r)) :
    IsLimitedCoefficientResult η c b r := by
  have hcden : toPoly (CFrac.den c) ≠ 0 := by
    simpa only [toPoly_list_eq] using CFrac.toPoly_den_ne_zero_generic c
  have hηden : toPoly (CFrac.den η) ≠ 0 := by
    simpa only [toPoly_list_eq] using CFrac.toPoly_den_ne_zero_generic η
  have htoK_frac : ∀ x : DenseFrac β,
      CFieldSpec.toK x = fieldFrac (CFrac.num x) (CFrac.den x) := by
    intro x
    change CFrac.toRatFunc x = _
    rw [CFrac.toRatFunc_eq_div]
    simp only [fieldFrac, toPoly_list_eq]
  have hderiv : ∀ x : DenseFrac β,
      CFieldSpec.toK (CDiffField.cderiv x) =
        towerFractionFieldDeriv ([CCommRing.one] : DensePoly β) (CFieldSpec.toK x) := by
    intro x
    rw [CDiffFieldSpec.toK_cderiv]
    change extendDeriv (Differential.implicitDeriv
        (CPoly.toPoly (CPoly.one : DensePoly β))) _ =
      towerFractionFieldDeriv ([CCommRing.one] : DensePoly β) _
    rw [towerFractionFieldDeriv, CPoly.toPoly_one]
    have hone : toPoly ([CCommRing.one] : DensePoly β) = 1 := by
      simp only [denote]
      simp
    rw [hone]
  unfold towerCoeffLimitedIntegrateLrt at h
  generalize hrun : L.run (CFrac.num c) (CFrac.den c)
      (CFrac.num η) (CFrac.den η) = attempt at h
  cases attempt with
  | none =>
      rw [Option.map_eq_some_iff] at h
      obtain ⟨b₀, hb₀, hout⟩ := h
      simp only [Prod.mk.injEq] at hout
      obtain ⟨rfl, rfl⟩ := hout
      rw [IsLimitedCoefficientResult, CFieldSpec.toK_zero, zero_mul, add_zero]
      exact ⟨(towerCoeffIntegrateLrt_sound c b₀ hb₀).symm, by
        rw [CDiffFieldSpec.toK_cderiv, CFieldSpec.toK_zero, map_zero]⟩
  | some value =>
      obtain ⟨⟨bn, bd⟩, cc⟩ := value
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hlimited := LawfulCLimitedIntegrateSingleLrt.sound (C := L)
        (CFrac.num c) (CFrac.den c) (CFrac.num η) (CFrac.den η) bn bd cc
        hcden hηden hrun
      have htoK_b :
          CFieldSpec.toK (CField.div (CFrac.ofPoly (F := DenseFrac) bn)
            (CFrac.ofPoly (F := DenseFrac) bd)) = fieldFrac bn bd := by
        rw [CFieldSpec.toK_div]
        simp only [fieldFrac, CFrac.toK_ofPoly, toPoly_list_eq]
      have htoK_cc :
          CFieldSpec.toK (CFrac.ofPoly (F := DenseFrac) ([cc] : DensePoly β)) =
            algebraMap (CFieldSpec.K β) (RatFunc (CFieldSpec.K β)) (CFieldSpec.toK cc) := by
        rw [CFrac.toK_ofPoly]
        simp only [toPoly_list_eq, denote, mul_zero, add_zero]
        rw [CFrac.am, ← Polynomial.algebraMap_eq]
        exact (IsScalarTower.algebraMap_apply (CFieldSpec.K β)
          (CFieldSpec.K β)[X] (RatFunc (CFieldSpec.K β)) (CFieldSpec.toK cc)).symm
      have htoK_cc_am :
          CFieldSpec.toK (CFrac.ofPoly (F := DenseFrac) ([cc] : DensePoly β)) =
            CFrac.am β (Polynomial.C (CFieldSpec.toK cc)) := by
        rw [CFrac.toK_ofPoly]
        simp only [toPoly_list_eq, denote, mul_zero, add_zero]
      rw [IsLimitedCoefficientResult, htoK_frac c, hderiv, htoK_b, htoK_cc, htoK_frac η]
      constructor
      · exact hlimited.2.1.symm
      · rw [hderiv, htoK_cc_am, towerFractionFieldDerivG_amG_C]
        rw [← CDiffFieldSpec.toK_cderiv, hlimited.2.2]
        simp

/-- The LRT tower coefficient operation satisfies limited-integration soundness. -/
instance instLawfulCLimitedCoefficientIntegratorLrt
    [L : CLimitedIntegrateSingleLrt β] [LawfulCLimitedIntegrateSingleLrt L]
    [LawfulCRischLevelLrt (inferInstance : CRischLevelLrt β)] :
    LawfulCLimitedCoefficientIntegrator (towerCoefficientIntegratorLrt (β := β)) where
  limited_sound η c b r h := towerCoeffLimitedIntegrateLrt_sound η c b r h

/-- Domain where tower limited integration descends to the selected coefficient-field capability. -/
def towerLimitedCoefficientDomain (domain : LimitedIntegrateSingleDomain β) :
    LimitedCoefficientDomain (α := DenseFrac β) := fun η c =>
  domain (CFrac.num c) (CFrac.den c) (CFrac.num η) (CFrac.den η) ∧
    IsLimitedIntegrateSingleIntegrable
      (CFrac.num c) (CFrac.den c) (CFrac.num η) (CFrac.den η)

/-- Coefficient-field limited completeness lifts through `DenseFrac` on the descended domain. -/
instance instCompleteCLimitedCoefficientIntegratorLrt
    [L : CLimitedIntegrateSingleLrt β] [LawfulCLimitedIntegrateSingleLrt L]
    (domain : LimitedIntegrateSingleDomain β)
    [CompleteCLimitedIntegrateSingleLrt L domain]
    [LawfulCRischLevelLrt (inferInstance : CRischLevelLrt β)] :
    CompleteCLimitedCoefficientIntegrator (towerCoefficientIntegratorLrt (β := β))
      (towerLimitedCoefficientDomain domain) where
  limited_complete η c hdomain _ := by
    obtain ⟨hdomain, hintegrable⟩ := hdomain
    obtain ⟨bn, bd, cc, hrun, _hresult⟩ :=
      CompleteCLimitedIntegrateSingleLrt.complete (C := L) (domain := domain)
        (CFrac.num c) (CFrac.den c) (CFrac.num η) (CFrac.den η)
        hdomain hintegrable
    let b : DenseFrac β := CField.div (CFrac.ofPoly bn) (CFrac.ofPoly bd)
    let r : DenseFrac β := CFrac.ofPoly [cc]
    have hout : towerCoeffLimitedIntegrateLrt η c = some (b, r) := by
      simp only [towerCoeffLimitedIntegrateLrt, hrun, b, r]
    exact ⟨b, r, hout, towerCoeffLimitedIntegrateLrt_sound η c b r hout⟩

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
    [CLimitedIntegrateSingleLrt β]
    (η : DenseFrac β) (p : P (DenseFrac β)) : Option (P (DenseFrac β)) :=
  recursiveTowerPolyIntegrateLrt (towerCoefficientIntegratorLrt (β := β)) η p

/-- The LRT tower step's polynomial-part soundness. -/
theorem towerPolyIntegrateLrt_sound {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    [LawfulCPolyEngine.{u,v} P] [CLimitedIntegrateSingleLrt β]
    (η : DenseFrac β) (p q : P (DenseFrac β))
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

/-- The LRT tower primitive monomial case, supplied with its selected recursive coefficient operation. -/
def towerPrimitiveCaseLrt [CLimitedIntegrateSingleLrt β] :
    CMonomialCase DensePoly (DenseFrac β) :=
  (towerPrimitiveRecursiveMonomialCaseLrt (β := β)).withCoefficient
    (towerCoefficientIntegratorLrt (β := β))

omit [CPolyGcd DensePoly (DenseFrac β)] [CPolySquarefree DensePoly (DenseFrac β)] in
/-- LRT tower primitive special-part soundness, the tower-recursion analogue of `primitiveGuardedCase_specialSound`.
Under the guard (`b = 0`, `Dθ = 1`) the LRT polynomial recursion `towerPolyIntegrateLrt` yields `qp` with
`D_tower(⟦qp⟧) = ⟦fp⟧` (`tower_special_identityLrt`), and `canonicalReconstruction_of_charZero` (special term
vanishing, `b = 0`) closes; off the guard the hook returns `none`. This is the `specialSound` field of the LRT
tower instance. -/
theorem towerPrimitiveCaseLrt_specialSound
    [L : CLimitedIntegrateSingleLrt β]
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

/-- Domain where the recursive primitive special stage's guards hold and degree raising is closed. -/
def towerPrimitiveRecursiveSpecialDomainLrt
    (limitedDomain : LimitedCoefficientDomain (α := DenseFrac β)) :
    MonomialSpecialDomain DensePoly (DenseFrac β) :=
  fun Dt fp b _ds => cisZero b = true ∧ cisZero (csub Dt [CCommRing.one]) = true ∧
    PrimitivePolynomialDomain CCommRing.one limitedDomain (cdeg fp + 2) fp

/-- The recursive primitive monomial stage is complete on its explicit degree-raising closure domain. -/
instance instCompleteCRecursiveMonomialCaseTowerPrimitiveLrt
    (recursiveDomain : RecursiveCoefficientDomain (α := DenseFrac β))
    (limitedDomain : LimitedCoefficientDomain (α := DenseFrac β)) :
    CompleteCRecursiveMonomialCase (towerPrimitiveRecursiveMonomialCaseLrt (β := β))
      recursiveDomain limitedDomain (towerPrimitiveRecursiveSpecialDomainLrt limitedDomain) where
  complete I := by
    intro _ _ _
    constructor
    · intro Dt fp b ds snum sden hdomain _hsden _hderiv
      obtain ⟨hb, hDt, hpoly⟩ := hdomain
      obtain ⟨qp, hqp⟩ := cIntegratePrimPolyDegRaise_complete
        CCommRing.one I limitedDomain (cdeg fp + 2) fp hpoly
      refine ⟨(qp, [CCommRing.one]), ?_⟩
      simp only [CRecursiveMonomialCase.withCoefficient, towerPrimitiveRecursiveMonomialCaseLrt]
      rw [hb, hDt]
      simp only [Bool.true_and, if_true]
      change (match recursiveTowerPolyIntegrateLrt I CCommRing.one fp with
        | none => none
        | some qp => some (qp, [CCommRing.one])) = some (qp, [CCommRing.one])
      rw [recursiveTowerPolyIntegrateLrt,
        show CPolyEngine.cdeg fp = cdeg fp from rfl, hqp]
    · intro Dt cn dn before hbefore
      refine ⟨before, ?_⟩
      simp only [CRecursiveMonomialCase.withCoefficient, towerPrimitiveRecursiveMonomialCaseLrt,
        primitiveGuardedCase]
      rw [if_pos]
      exact List.all_eq_true.mpr fun cv hcv => by
        rw [cisZeroG_iff]
        simp only [denote, mul_zero, add_zero]
        rw [hbefore.coefficients_constant cv hcv, map_zero]

omit [CPolyGcd DensePoly (DenseFrac β)] [CPolySplitFactor DensePoly (DenseFrac β)]
  [LawfulCPolySplitFactor DensePoly (DenseFrac β)]
  [CPolySquarefree DensePoly (DenseFrac β)] in
/-- Lower-level log-free and limited completeness compose into tower primitive monomial completeness. -/
theorem completeTowerPrimitiveCaseLrt
    [L : CLimitedIntegrateSingleLrt β] [LawfulCLimitedIntegrateSingleLrt L]
    [LawfulCRischLevelLrt (inferInstance : CRischLevelLrt β)]
    (rationalDomain : RationalLrtDomain β)
    [CompleteCRischLevelRationalLrt (inferInstance : CRischLevelLrt β) rationalDomain]
    (limitedSingleDomain : LimitedIntegrateSingleDomain β)
    [CompleteCLimitedIntegrateSingleLrt L limitedSingleDomain] :
    CompleteCMonomialCase (towerPrimitiveCaseLrt (β := β))
      (towerPrimitiveRecursiveSpecialDomainLrt
        (towerLimitedCoefficientDomain limitedSingleDomain)) := by
  change CompleteCMonomialCase
    ((towerPrimitiveRecursiveMonomialCaseLrt (β := β)).withCoefficient
      (towerCoefficientIntegratorLrt (β := β))) _
  exact completeCMonomialCaseWithRecursiveCoefficient
    (towerPrimitiveRecursiveMonomialCaseLrt (β := β))
    (towerRecursiveCoefficientDomain rationalDomain)
    (towerLimitedCoefficientDomain limitedSingleDomain)
    (towerPrimitiveRecursiveSpecialDomainLrt
      (towerLimitedCoefficientDomain limitedSingleDomain))
    (towerCoefficientIntegratorLrt (β := β))

/-- The LRT tower step operation: `CRischLevelLrt (DenseFrac β)` from a below-level operation and contract
and this level's reduced LRT frontier `[PrimitiveFrontierLrt (DenseFrac β)]`.
With the base (`instCRischLevelLrtPrimitive`) the LRT solver resolves at every tower depth by recursion:
the re-based recursion, now with a dischargeable frontier at every level. `specialSound` is the LRT coefficient
recursion (`towerPrimitiveCaseLrt_specialSound`); `reducedSoundLrt` is `PrimitiveFrontierLrt.hreducedLrt`. -/
instance instCRischLevelLrtTower [CLimitedIntegrateSingleLrt β]
    [PrimitiveFrontierLrt (DenseFrac β)] :
    CRischLevelLrt (DenseFrac β) where
  case := towerPrimitiveCaseLrt

/-- The recursive LRT tower operation satisfies its algebraic-residue contract. -/
instance instLawfulCRischLevelLrtTower [CLimitedIntegrateSingleLrt β]
    [PrimitiveFrontierLrt (DenseFrac β)] :
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
