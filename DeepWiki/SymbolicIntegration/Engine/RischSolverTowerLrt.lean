import DeepWiki.SymbolicIntegration.Engine.RischTowerLrt
import DeepWiki.SymbolicIntegration.Engine.LimitedIntegrateSingle

/-! # Recursive LRT Risch tower step

The tower step of the recursive LRT Risch solver (`instLawfulRischLevelLrtTower`, paired with the base
`instLawfulRischLevelLrtPrimitive`). Given an LRT solver for the coefficient field `[LawfulRischLevelLrt β]`, build one
for `(DenseFrac β)(t)`. The polynomial part's coefficient integration recurses into `LawfulRischLevelLrt β`'s
log-free integrator `integrateRationalLrt` (descent-free `K`-level, by the ∀E ⇒ K bridge
`integrateRationalLrt_sound`) — so the whole tower stays on the LRT track (its reduced frontier
is `PrimitiveFrontierLrt`, not the undischargeable rational `PrimitiveFrontier`).

Everything reuses the *generic* degree-raising coefficient recursion (`cIntegratePrimPolyDegRaise`,
`cIntegratePrimPolyDegRaiseG_sound` — result-type-agnostic, telescoping soundness): only the coefficient
integrator `limInt` changes to `LawfulRischLevelLrt.integrateRationalLrt` (wrapped `b ↦ (b, 0)`; the
degree-raising `c` is used when the base level supplies a `(b,c)` limited integrator). The special-part
soundness `towerPrimitiveCaseLrt_specialSound` and the log-tower special identity `tower_special_identityLrt`
close the polynomial part; the reduced part goes through the root-free assembler `cIntegrateCaseLrt`. -/

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac Polynomial
open scoped Differential

universe u v

variable {β : Type u} [CField β] [CFieldSpec.{u,v} β] [CDiffField β] [CDiffFieldSpec.{u,v} β]
  [CFieldDomain β DensePoly] [CRischField β] [CFracGcdCoreWf β] [Algebra ℚ (CFieldSpec.K β)]
  [CharZero (CFieldSpec.K β)] [Fact (CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := β)))]
  [LawfulCPolyGcd.{u,v} DensePoly β] [LawfulCPolyGcd.{u,v} DensePoly (DenseFrac β)]
  [LawfulRischLevelLrt β]

/-- Integrate a coefficient `c ∈ DenseFrac β = β(s)` by recursing into
`LawfulRischLevelLrt β.integrateRationalLrt` (the log-free LRT integrator, whose soundness is descent-free
`K`-level via the ∀E ⇒ K bridge) with the carrier derivation `Ds = [1]`, reassembling via `DenseFrac β` field
division. The coefficient integrator the LRT tower step feeds (wrapped) to `cIntegratePrimPolyDegRaise`,
staying on the LRT track. -/
def towerCoeffIntegrateLrt (c : DenseFrac β) : Option (DenseFrac β) :=
  (LawfulRischLevelLrt.integrateRationalLrt [CCommRing.one] (CFrac.num c) (CFrac.den c)).map fun bd =>
    CField.div (CFrac.ofPoly bd.1) (CFrac.ofPoly bd.2)

omit [CRischField β] [LawfulCPolyGcd DensePoly β] [LawfulCPolyGcd DensePoly (DenseFrac β)] in
/-- LRT coefficient-recursion soundness: `toK (cderiv b) = toK c` in
`RatFunc (CFieldSpec.K β)`, reassembling `integrateRationalLrt_sound` (descent-free `K`-level) through the
`DenseFrac β` field division that `towerCoeffIntegrateLrt` performs. -/
theorem towerCoeffIntegrateLrt_sound (c b : DenseFrac β) (h : towerCoeffIntegrateLrt c = some b) :
    CFieldSpec.toK (CDiffField.cderiv b) = CFieldSpec.toK c := by
  unfold towerCoeffIntegrateLrt at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨⟨bn, bd⟩, hint, rfl⟩ := h
  have hsound := LawfulRischLevelLrt.integrateRationalLrt_sound [CCommRing.one]
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

/-- The single-`w` LRT coefficient integrator `(b, c)` tries the optional
`LawfulRischLevelLrt.limitedIntegrateSingle` (reconstructing `b = bnum/bden` and the constant `c` as
`DenseFrac β` elements), falling back to the log-free `towerCoeffIntegrateLrt` (`c = 0`) when the class supplies no
single-`w` integrator (the default). This is the `limInt` that flips on the degree-raising `c·tᵐ⁺¹/(m+1)` term
once a base `(b,c)` integrator (`CFrac.limitedIntegrateSingleBase`) is present. -/
def towerCoeffIntegrateSingleLrt (η c : DenseFrac β) : Option (DenseFrac β × DenseFrac β) :=
  match LawfulRischLevelLrt.limitedIntegrateSingle (CFrac.num c) (CFrac.den c)
      (CFrac.num η) (CFrac.den η) with
  | some ((bn, bd), cc) => some (CField.div (CFrac.ofPoly bn) (CFrac.ofPoly bd), CFrac.ofPoly [cc])
  | none => (towerCoeffIntegrateLrt c).map fun b => (b, CCommRing.zero)

/-- The LRT tower step's polynomial-part integrator: the degree-raising primitive-polynomial recursion
`cIntegratePrimPolyDegRaise` with `towerCoeffIntegrateSingleLrt` as the single-`w` `limInt` (real `(b,c)` when
the class provides `limitedIntegrateSingle`, else log-free `c = 0`). Soundness `D_tower(q) = p` is the
telescoping `cIntegratePrimPolyDegRaiseG_sound` with no `limInt` correctness hypothesis. -/
def towerPolyIntegrateLrt {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    (η : DenseFrac β) (p : P (DenseFrac β)) : Option (P (DenseFrac β)) :=
  cIntegratePrimPolyDegRaise η (towerCoeffIntegrateSingleLrt η) (CPolyEngine.cdeg p + 2) p

omit [CRischField β] [LawfulCPolyGcd DensePoly β]
    [LawfulCPolyGcd DensePoly (DenseFrac β)] in
/-- The LRT tower step's polynomial-part soundness: `D_tower(q) = p`, the telescoping
`cIntegratePrimPolyDegRaiseG_sound` (each step's `q₀` is subtracted then added back, so the identity holds for
*any* coefficient integrator — no `towerCoeffIntegrateLrt_sound` needed). -/
theorem towerPolyIntegrateLrt_sound {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    [LawfulCPolyEngine.{u,v} P] (η : DenseFrac β) (p q : P (DenseFrac β))
    (h : towerPolyIntegrateLrt η p = some q) :
    Differential.implicitDeriv (Polynomial.C (CFieldSpec.toK η)) (CPoly.toPoly q) =
      CPoly.toPoly p :=
  cIntegratePrimPolyDegRaiseG_sound η _ (CPolyEngine.cdeg p + 2) p q h

omit [CRischField β] [LawfulCPolyGcd DensePoly β]
    [LawfulCPolyGcd DensePoly (DenseFrac β)] in
/-- The LRT tower step's special-part field identity (`Dθ = 1`): from `towerPolyIntegrateLrt_sound`, the
polynomial antiderivative `qp` of `fp` gives `D_tower(⟦qp/1⟧) = ⟦fp/1⟧`. The `Dt` + `toPoly Dt = 1`
special identity for the tower step, with GENERAL coefficients via the LRT recursion. -/
theorem tower_special_identityLrt (Dt fp qp : DensePoly (DenseFrac β)) (hDt : toPoly Dt = 1)
    (h : towerPolyIntegrateLrt CCommRing.one fp = some qp) :
    towerFractionFieldDeriv Dt (fieldFrac qp [CCommRing.one]) = fieldFrac fp [CCommRing.one] := by
  have hpoly : Differential.implicitDeriv (Polynomial.C (CFieldSpec.toK CCommRing.one))
      (toPoly qp) = toPoly fp := by
    simpa only [toPoly_list_eq] using towerPolyIntegrateLrt_sound CCommRing.one fp qp h
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

/-- The LRT tower primitive monomial case: the `Dθ = 1` log-tower case with the polynomial part integrated
by the LRT coefficient RECURSION `towerPolyIntegrateLrt`. Guard: `b = 0` and `Dt = [1]`. The `reducedCorrect`
field is inert here (`cIntegrateCaseLrt` never calls it — the reduced part goes through the direct root-free
`cIntegrateReducedLrt`), so it reuses the shared guarded hook. -/
def towerPrimitiveCaseLrt : MonomialCase (DenseFrac β) where
  integrateSpecial Dt fp b _ds :=
    if cisZero b && cisZero (csub Dt [CCommRing.one]) then
      match towerPolyIntegrateLrt CCommRing.one fp with
      | none => none
      | some qp => some (qp, [CCommRing.one])
    else none
  reducedCorrect := (primitiveGuardedCase (α := DenseFrac β)).reducedCorrect

omit [LawfulCPolyGcd DensePoly β] in
omit [LawfulCPolyGcd DensePoly β] in
/-- LRT tower primitive special-part soundness, the tower-recursion analogue of `primitiveGuardedCase_specialSound`.
Under the guard (`b = 0`, `Dθ = 1`) the LRT polynomial recursion `towerPolyIntegrateLrt` yields `qp` with
`D_tower(⟦qp⟧) = ⟦fp⟧` (`tower_special_identityLrt`), and `canonicalReconstruction_of_charZero` (special term
vanishing, `b = 0`) closes; off the guard the hook returns `none`. This is the `specialSound` field of the LRT
tower instance. -/
theorem towerPrimitiveCaseLrt_specialSound [Fact (CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := DenseFrac β)))]
    (Dt a d snum sden : DensePoly (DenseFrac β)) (hd0 : toPoly d ≠ 0)
    (hhook : (towerPrimitiveCaseLrt (β := β)).integrateSpecial Dt (crPoly Dt a d) (crSpecNum Dt a d)
      (crSpecDen Dt a d) = some (snum, sden)) :
    toPoly sden ≠ 0 ∧ ∃ v : RatFunc (CFieldSpec.K (DenseFrac β)),
      towerFractionFieldDeriv Dt (fieldFrac snum sden) = v ∧
      v + fieldFrac (crNormNum Dt a d) (crNormDen Dt a d) = fieldFrac a d := by
  simp only [towerPrimitiveCaseLrt] at hhook
  by_cases hguard : (cisZero (crSpecNum Dt a d) && cisZero (csub Dt [CCommRing.one])) = true
  · rw [if_pos hguard] at hhook
    rw [Bool.and_eq_true] at hguard
    obtain ⟨hb, hDt1g⟩ := hguard
    rcases hqp : towerPolyIntegrateLrt CCommRing.one (crPoly Dt a d) with _ | qp
    · rw [hqp] at hhook; simp at hhook
    · rw [hqp] at hhook
      simp only [Option.some.injEq, Prod.mk.injEq] at hhook
      obtain ⟨rfl, rfl⟩ := hhook
      have hDt1 : toPoly Dt = 1 := by
        have hh := (cisZeroG_iff (csub Dt [CCommRing.one])).mp hDt1g
        simpa only [denote, map_one, mul_zero, add_zero, sub_eq_zero] using hh
      exact primitiveSpecialSoundCore Dt a d qp hd0 hb
        (tower_special_identityLrt Dt (crPoly Dt a d) qp hDt1 hqp)
  · rw [if_neg hguard] at hhook; simp at hhook

/-- The LRT tower step instance: `LawfulRischLevelLrt (DenseFrac β)` from a below-level LRT solver
`[LawfulRischLevelLrt β]` and this level's reduced LRT frontier `[PrimitiveFrontierLrt (DenseFrac β)]`.
With the base (`instLawfulRischLevelLrtPrimitive`) the LRT solver resolves at every tower depth by recursion:
the re-based recursion, now with a dischargeable frontier at every level. `specialSound` is the LRT coefficient
recursion (`towerPrimitiveCaseLrt_specialSound`); `reducedSoundLrt` is `PrimitiveFrontierLrt.hreducedLrt`. -/
instance instLawfulRischLevelLrtTower [Fact (CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := DenseFrac β)))]
    [PrimitiveFrontierLrt (DenseFrac β)] : LawfulRischLevelLrt (DenseFrac β) where
  case := towerPrimitiveCaseLrt
  specialSound := fun Dt a d snum sden hd0 hhook =>
    towerPrimitiveCaseLrt_specialSound Dt a d snum sden hd0 hhook
  reducedSoundLrt := fun Dt a d hd0 hDt0 => PrimitiveFrontierLrt.hreducedLrt Dt a d hd0 hDt0
  reducedDenNonzero := fun Dt a d hd0 hDt0 =>
    PrimitiveFrontierLrt.hreducedDenNonzero Dt a d hd0 hDt0

-- The LRT tower solver resolves at depth 2 by recursion; the step instance chains on itself.
noncomputable example [Fact (CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := DenseFrac β)))] [PrimitiveFrontierLrt (DenseFrac β)]
    [Fact (CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := DenseFrac (DenseFrac β))))]
    [LawfulCPolyGcd.{u,v} DensePoly (DenseFrac (DenseFrac β))]
    [PrimitiveFrontierLrt (DenseFrac (DenseFrac β))] :
    LawfulRischLevelLrt (DenseFrac (DenseFrac β)) := inferInstance

end DeepWiki.SymbolicIntegration
