import DeepWiki.SymbolicIntegration.Engine.RischTowerLrt
import DeepWiki.SymbolicIntegration.Engine.LimitedIntegrateSingle

/-! # Recursive LRT Risch tower step

The tower step of the recursive LRT Risch solver (`instLawfulRischLevelLrtTower`, paired with the base
`instLawfulRischLevelLrtPrimitive`). Given an LRT solver for the coefficient field `[LawfulRischLevelLrt β]`, build one
for `(CFrac β)(t)`. The polynomial part's coefficient integration recurses into `LawfulRischLevelLrt β`'s
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

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β]
  [CFieldDomain β] [CRischField β] [CFracGcdCoreWf β] [Algebra ℚ (CFieldSpec.K β)]
  [CharZero (CFieldSpec.K β)] [Fact (GcdFFCorrect (α := β))] [LawfulRischLevelLrt β]

/-- Embed a polynomial as a fraction `num/1 ∈ CFrac β`. -/
def qEmbedNum {β : Type*} [CField β] [CFieldDomain β] (num : DensePoly β) : CFrac β :=
  ⟨(num, [CCommRing.one]), CFrac.cisZeroG_one_singleton⟩

/-- Integrate a coefficient `c ∈ CFrac β = β(s)` by recursing into
`LawfulRischLevelLrt β.integrateRationalLrt` (the log-free LRT integrator, whose soundness is descent-free
`K`-level via the ∀E ⇒ K bridge) with the carrier derivation `Ds = [1]`, reassembling via `CFrac β` field
division. The coefficient integrator the LRT tower step feeds (wrapped) to `cIntegratePrimPolyDegRaise`,
staying on the LRT track. -/
def towerCoeffIntegrateLrt (c : CFrac β) : Option (CFrac β) :=
  (LawfulRischLevelLrt.integrateRationalLrt [CCommRing.one] (qnumCoeffCore c) (qdenCoeffCore c)).map fun bd =>
    CField.div (qEmbedNum bd.1) (qEmbedNum bd.2)

omit [CRischField β] in
/-- LRT coefficient-recursion soundness: `toK (cderiv b) = toK c` in
`RatFunc (CFieldSpec.K β)`, reassembling `integrateRationalLrt_sound` (descent-free `K`-level) through the
`CFrac β` field division that `towerCoeffIntegrateLrt` performs. -/
theorem towerCoeffIntegrateLrt_sound (c b : CFrac β) (h : towerCoeffIntegrateLrt c = some b) :
    CFieldSpec.toK (CDiffField.cderiv b) = CFieldSpec.toK c := by
  unfold towerCoeffIntegrateLrt at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨⟨bn, bd⟩, hint, rfl⟩ := h
  have hsound := LawfulRischLevelLrt.integrateRationalLrt_sound [CCommRing.one]
    (qnumCoeffCore c) (qdenCoeffCore c) bn bd hint
  have hcd : CFieldSpec.toK (CDiffField.cderiv (CField.div (qEmbedNum bn) (qEmbedNum bd)))
      = towerFractionFieldDeriv [CCommRing.one]
          (CFieldSpec.toK (CField.div (qEmbedNum bn) (qEmbedNum bd))) := by
    rw [CDiffFieldSpec.toK_cderiv]
    rfl
  have htoK_embed : ∀ num : DensePoly β, CFieldSpec.toK (qEmbedNum num) = CFrac.am β (toPoly num) := by
    intro num
    show CFrac.am β (toPoly num) / CFrac.am β (toPoly ([CCommRing.one] : DensePoly β))
      = CFrac.am β (toPoly num)
    simp only [denote, map_one, mul_zero, add_zero, div_one]
  have htoK_c : CFieldSpec.toK c
      = CFrac.am β (toPoly (qnumCoeffCore c)) / CFrac.am β (toPoly (qdenCoeffCore c)) := rfl
  rw [hcd, CFieldSpec.toK_div, htoK_embed bn, htoK_embed bd, htoK_c]
  exact hsound

/-- The single-`w` LRT coefficient integrator `(b, c)` tries the optional
`LawfulRischLevelLrt.limitedIntegrateSingle` (reconstructing `b = bnum/bden` and the constant `c` as
`CFrac β` elements), falling back to the log-free `towerCoeffIntegrateLrt` (`c = 0`) when the class supplies no
single-`w` integrator (the default). This is the `limInt` that flips on the degree-raising `c·tᵐ⁺¹/(m+1)` term
once a base `(b,c)` integrator (`cLimitedIntegrateSingleBase`) is present. -/
def towerCoeffIntegrateSingleLrt (η c : CFrac β) : Option (CFrac β × CFrac β) :=
  match LawfulRischLevelLrt.limitedIntegrateSingle (qnumCoeffCore c) (qdenCoeffCore c)
      (qnumCoeffCore η) (qdenCoeffCore η) with
  | some ((bn, bd), cc) => some (CField.div (qEmbedNum bn) (qEmbedNum bd), qEmbedNum [cc])
  | none => (towerCoeffIntegrateLrt c).map fun b => (b, CCommRing.zero)

/-- The LRT tower step's polynomial-part integrator: the degree-raising primitive-polynomial recursion
`cIntegratePrimPolyDegRaise` with `towerCoeffIntegrateSingleLrt` as the single-`w` `limInt` (real `(b,c)` when
the class provides `limitedIntegrateSingle`, else log-free `c = 0`). Soundness `D_tower(q) = p` is the
telescoping `cIntegratePrimPolyDegRaiseG_sound` with no `limInt` correctness hypothesis. -/
def towerPolyIntegrateLrt (η : CFrac β) (p : DensePoly (CFrac β)) : Option (DensePoly (CFrac β)) :=
  cIntegratePrimPolyDegRaise η (towerCoeffIntegrateSingleLrt η) (cdeg p + 2) p

omit [CRischField β] in
/-- The LRT tower step's polynomial-part soundness: `D_tower(q) = p`, the telescoping
`cIntegratePrimPolyDegRaiseG_sound` (each step's `q₀` is subtracted then added back, so the identity holds for
*any* coefficient integrator — no `towerCoeffIntegrateLrt_sound` needed). -/
theorem towerPolyIntegrateLrt_sound (η : CFrac β) (p q : DensePoly (CFrac β))
    (h : towerPolyIntegrateLrt η p = some q) :
    Differential.implicitDeriv (Polynomial.C (CFieldSpec.toK η)) (toPoly q) = toPoly p :=
  cIntegratePrimPolyDegRaiseG_sound η _ (cdeg p + 2) p q h

omit [CRischField β] in
/-- The LRT tower step's special-part field identity (`Dθ = 1`): from `towerPolyIntegrateLrt_sound`, the
polynomial antiderivative `qp` of `fp` gives `D_tower(⟦qp/1⟧) = ⟦fp/1⟧`. The `Dt` + `toPoly Dt = 1`
special identity for the tower step, with GENERAL coefficients via the LRT recursion. -/
theorem tower_special_identityLrt (Dt fp qp : DensePoly (CFrac β)) (hDt : toPoly Dt = 1)
    (h : towerPolyIntegrateLrt CCommRing.one fp = some qp) :
    towerFractionFieldDeriv Dt (fieldFrac qp [CCommRing.one]) = fieldFrac fp [CCommRing.one] := by
  have hpoly := towerPolyIntegrateLrt_sound CCommRing.one fp qp h
  rw [CFieldSpec.toK_one, Polynomial.C_1] at hpoly
  have hone : toPoly ([CCommRing.one] : DensePoly (CFrac β)) = 1 := by
    simp only [denote, map_one, mul_zero, add_zero]
  have hbridge : towerFractionFieldDeriv Dt (CFrac.am (CFrac β) (toPoly qp))
      = CFrac.am (CFrac β) (Differential.implicitDeriv (toPoly Dt) (toPoly qp)) := by
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
def towerPrimitiveCaseLrt : MonomialCase (CFrac β) where
  integrateSpecial Dt fp b _ds :=
    if cisZero b && cisZero (csub Dt [CCommRing.one]) then
      match towerPolyIntegrateLrt CCommRing.one fp with
      | none => none
      | some qp => some (qp, [CCommRing.one])
    else none
  reducedCorrect := (primitiveGuardedCase (α := CFrac β)).reducedCorrect

/-- LRT tower primitive special-part soundness, the tower-recursion analogue of `primitiveGuardedCase_specialSound`.
Under the guard (`b = 0`, `Dθ = 1`) the LRT polynomial recursion `towerPolyIntegrateLrt` yields `qp` with
`D_tower(⟦qp⟧) = ⟦fp⟧` (`tower_special_identityLrt`), and `canonicalReconstruction_of_charZero` (special term
vanishing, `b = 0`) closes; off the guard the hook returns `none`. This is the `specialSound` field of the LRT
tower instance. -/
theorem towerPrimitiveCaseLrt_specialSound [Fact (GcdFFCorrect (α := CFrac β))]
    (Dt a d snum sden : DensePoly (CFrac β)) (hd0 : toPoly d ≠ 0)
    (hhook : (towerPrimitiveCaseLrt (β := β)).integrateSpecial Dt (crPoly Dt a d) (crSpecNum Dt a d)
      (crSpecDen Dt a d) = some (snum, sden)) :
    toPoly sden ≠ 0 ∧ ∃ v : RatFunc (CFieldSpec.K (CFrac β)),
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

/-- The LRT tower step instance: `LawfulRischLevelLrt (CFrac β)` from a below-level LRT solver
`[LawfulRischLevelLrt β]` and this level's reduced LRT frontier `[PrimitiveFrontierLrt (CFrac β)]`.
With the base (`instLawfulRischLevelLrtPrimitive`) the LRT solver resolves at every tower depth by recursion:
the re-based recursion, now with a dischargeable frontier at every level. `specialSound` is the LRT coefficient
recursion (`towerPrimitiveCaseLrt_specialSound`); `reducedSoundLrt` is `PrimitiveFrontierLrt.hreducedLrt`. -/
instance instLawfulRischLevelLrtTower [Fact (GcdFFCorrect (α := CFrac β))]
    [PrimitiveFrontierLrt (CFrac β)] : LawfulRischLevelLrt (CFrac β) where
  case := towerPrimitiveCaseLrt
  specialSound := fun Dt a d snum sden hd0 hhook =>
    towerPrimitiveCaseLrt_specialSound Dt a d snum sden hd0 hhook
  reducedSoundLrt := fun Dt a d hd0 hDt0 => PrimitiveFrontierLrt.hreducedLrt Dt a d hd0 hDt0

-- The LRT tower solver resolves at depth 2 by recursion; the step instance chains on itself.
noncomputable example [Fact (GcdFFCorrect (α := CFrac β))] [PrimitiveFrontierLrt (CFrac β)]
    [Fact (GcdFFCorrect (α := CFrac (CFrac β)))] [PrimitiveFrontierLrt (CFrac (CFrac β))] :
    LawfulRischLevelLrt (CFrac (CFrac β)) := inferInstance

end DeepWiki.SymbolicIntegration
