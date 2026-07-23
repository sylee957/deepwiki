import DeepWiki.SymbolicIntegration.Engine.Tower.Lvl2
import DeepWiki.SymbolicIntegration.Engine.MonomialDeriv
import DeepWiki.SymbolicIntegration.DifferentialAlgebra.RationalFunctionExtension
import DeepWiki.ComputableAlgebra.FracReprSparse

/-! # A computable derivation on represented fraction towers
`towerDerivCFracWith Dt` is the quotient-rule derivation for any `CFrac F P`, and
`instCDiffFieldCFrac` makes `CDiffField` iterate up the tower with the new monomial as an independent
variable (`Dt = [1]`). Both are computable (no `CFieldSpec`), and `toRatFunc_towerDerivCFracWith` bridges to
Mathlib's abstract `extendDeriv` on `RatFunc (CFieldSpec.K α)`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

universe u v

open scoped Differential

namespace CFrac

/-! ### The computable tower derivation -/

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P]
variable {F : (α : Type u) → [CField α] → Type u} [CFrac F P] [LawfulCFrac F P]

/-- The quotient-rule tower derivation selected by an explicit coefficient derivation. -/
def towerDerivCFracWithDerivation {α : Type u} [CField α] [CFieldDomain α P]
    (derivation : CFieldDerivation α) (Dt : P α) (x : F α) : F α :=
  CFrac.ofFraction
    (CPolyEngine.sub
      (CPolyEngine.mul (CPolyEngine.monomialDerivWith derivation Dt (CFrac.num x)) (CFrac.den x))
      (CPolyEngine.mul (CFrac.num x)
        (CPolyEngine.monomialDerivWith derivation Dt (CFrac.den x))))
    (CPolyEngine.mul (CFrac.den x) (CFrac.den x))
    (CFrac.cmulG_ne_zero_of (CFrac.cisZeroG_den x) (CFrac.cisZeroG_den x))

/-- The quotient-rule tower derivation on any represented fraction `F` over polynomial representation `P`. -/
def towerDerivCFracWith {α : Type u} [CField α] [CDiffField α] [CFieldDomain α P]
    (Dt : P α) (x : F α) : F α :=
  towerDerivCFracWithDerivation (CFieldDerivation.ofCDiffField α) Dt x

/-- Dense specialization of the representation-independent quotient-rule tower derivation. -/
def towerDerivCFrac {α : Type u} [CField α] [CDiffField α] [CFieldDomain α DensePoly]
    (Dt : DensePoly α) (x : DenseFrac α) : DenseFrac α :=
  towerDerivCFracWith Dt x

/-- The generic tower derivative numerator is `D n · d − n · D d`. -/
@[simp] theorem towerDerivCFracWith_num {α : Type u} [CField α] [CDiffField α]
    [CFieldDomain α P] (Dt : P α) (x : F α) :
    CFrac.num (towerDerivCFracWith Dt x) =
      CPolyEngine.sub (CPolyEngine.mul (CPolyEngine.monomialDeriv Dt (CFrac.num x)) (CFrac.den x))
      (CPolyEngine.mul (CFrac.num x) (CPolyEngine.monomialDeriv Dt (CFrac.den x))) := by
  simp [towerDerivCFracWith, towerDerivCFracWithDerivation]

/-- The generic tower derivative denominator is the square of the input denominator. -/
@[simp] theorem towerDerivCFracWith_den {α : Type u} [CField α] [CDiffField α]
    [CFieldDomain α P] (Dt : P α) (x : F α) :
    CFrac.den (towerDerivCFracWith Dt x) = CPolyEngine.mul (CFrac.den x) (CFrac.den x) := by
  simp [towerDerivCFracWith, towerDerivCFracWithDerivation]

end CFrac

/-! ### The iterating instance `CDiffField (DenseFrac α)` -/

section
variable {P : Type u → Type u} [CPoly P] [CPolyEngine P]
variable {F : (α : Type u) → [CField α] → Type u} [CFrac F P] [LawfulCFrac F P]
variable {α : Type u} [CField α] [CDiffField α] [CFieldDomain α P]

/-- Any `CFrac F P` inherits the quotient-rule derivation with the new monomial independent. -/
instance instCDiffFieldCFrac : CDiffField (F α) where
  cderiv := CFrac.towerDerivCFracWith (CPoly.one : P α)

end

/-! ### The level-2 derivation computes (`ccompute`) -/

/-- A level-2 scalar `c ∈ Lvl2 = DenseFrac (DenseFrac ℚ) = ℚ(x)(t₁)` from a numerator/denominator pair of
`DensePoly (DenseFrac ℚ)`s, with denominator a nonzero singleton `[d]`. -/
def lvl2OfList (num : DensePoly (DenseFrac ℚ)) (d : DenseFrac ℚ)
    (h : DensePoly.cisZero ([d] : DensePoly (DenseFrac ℚ)) = false) : Lvl2 :=
  CFrac.ofFraction num [d] h

/-- The level-2 scalar `t₁ ∈ ℚ(x)(t₁)` (numerator `[0, 1]` over ℚ(x): `t₁ = 0 + 1·t₁`, denominator
`[1]`). -/
def lvl2T1 : Lvl2 :=
  lvl2OfList [(CCommRing.zero : DenseFrac ℚ), CCommRing.one] (CCommRing.one : DenseFrac ℚ) (by cfrac_nonzero)

/-! #### The level-2 scalar derivation `towerDerivCFrac` reduces -/

/-- `D(t₁) = 1` at level 2: the level-2 derivation applied to `t₁` is `1` (checked via `CCommRing.isZero` of
the difference). -/
theorem lvl2_deriv_t1_eq_one :
    CCommRing.isZero
      (CField.sub (CDiffField.cderiv lvl2T1) (CCommRing.one : Lvl2)) = true := by ccompute

-- `D(1) = 0` at level 2: the derivation annihilates the constant `1`.
example :
    CCommRing.isZero (CDiffField.cderiv (CCommRing.one : Lvl2)) = true := by ccompute

-- `D(0) = 0` at level 2: the derivation annihilates `0`.
example :
    CCommRing.isZero (CDiffField.cderiv (CCommRing.zero : Lvl2)) = true := by ccompute

/-! #### The level-2 monomial derivation `CPolyEngine.monomialDeriv` reduces over `ℚ(x)(t₁)[t₂]` -/

/-- `Dt₂ = [1]` over `DensePoly Lvl2`: the new level-2 monomial `t₂` is an independent variable
(`Dt₂ = 1`). -/
def lvl2Dt2 : DensePoly Lvl2 := [CCommRing.one]

/-- The level-2 polynomial `t₂² ∈ ℚ(x)(t₁)[t₂]` (`[0, 0, 1]`). -/
def lvl2T2sq : DensePoly Lvl2 := [CCommRing.zero, CCommRing.zero, CCommRing.one]

/-- The level-2 polynomial `2·t₂ ∈ ℚ(x)(t₁)[t₂]` (`[0, 2]`, with `2 = 1 + 1`). -/
def lvl2TwoT2 : DensePoly Lvl2 := [CCommRing.zero, CCommRing.add CCommRing.one CCommRing.one]

/-- `D(t₂²) = 2·t₂` over `ℚ(x)(t₁)[t₂]`: `CPolyEngine.monomialDeriv lvl2Dt2` computes the derivative of `t₂²` to
`2·t₂` (checked via `cisZero` of the difference). -/
theorem lvl2_monomialDeriv_t2sq_eq_two_t2 :
    DensePoly.cisZero (DensePoly.csub (CPolyEngine.monomialDeriv lvl2Dt2 lvl2T2sq) lvl2TwoT2) = true := by
  ccompute

-- `D(t₂) = 1` over `ℚ(x)(t₁)[t₂]`: `CPolyEngine.monomialDeriv` of the monomial `t₂` is the constant `1`.
example :
    DensePoly.cisZero (DensePoly.csub
      (CPolyEngine.monomialDeriv lvl2Dt2 [(CCommRing.zero : Lvl2), CCommRing.one]) [CCommRing.one]) = true := by
  ccompute

-- `D(t₁·t₂)` over `ℚ(x)(t₁)[t₂]` is nonzero (`cisZero = false`): `CPolyEngine.monomialDeriv`
-- differentiates the `t₂`-coefficients too, not just the `d/dt₂` part.
example :
    DensePoly.cisZero (CPolyEngine.monomialDeriv lvl2Dt2 [(CCommRing.zero : Lvl2), lvl2T1]) = false := by
  ccompute

-- `D(t₁·t₂) = t₁ + t₂` over `ℚ(x)(t₁)[t₂]` (checked via `cisZero` of the difference
-- against `[t₁, 1]`).
example :
    DensePoly.cisZero (DensePoly.csub
      (CPolyEngine.monomialDeriv lvl2Dt2 [(CCommRing.zero : Lvl2), lvl2T1])
      [lvl2T1, (CCommRing.one : Lvl2)]) = true := by ccompute

/-- The independent sparse tower monomial `t`. -/
def sparseTowerT : SparseFrac ℚ :=
  CFrac.ofPoly (CPoly.SparsePoly.ofList [(1, 1)])

/-- The generic iterated derivation computes `D(t) = 1` for `SparseFrac`. -/
theorem sparseTowerT_deriv_eq_one :
    CCommRing.isZero
      (CField.sub (CDiffField.cderiv sparseTowerT) (CCommRing.one : SparseFrac ℚ)) = true := by ccompute

/-! ### The abstract bridge `toRatFunc (towerDerivCFrac Dt x) = extendDeriv …` -/

namespace CFrac

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P] [LawfulCPolyEngine.{u,v} P]
variable {F : (α : Type u) → [CField α] → Type u} [CFrac F P] [LawfulCFrac F P]
variable {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CFieldDomain α P]
variable [Algebra ℚ (CFieldSpec.K α)]

/-- An explicit represented quotient-rule derivation realizes the corresponding function-field extension. -/
theorem toRatFunc_towerDerivCFracWithDerivation (derivation : CFieldDerivation α)
    (diffK : Differential (CFieldSpec.K α)) [LawfulCFieldDerivation α derivation diffK]
    (Dt : P α) (x : F α) :
    letI : Differential (CFieldSpec.K α) :=
      diffK
    toRatFunc (towerDerivCFracWithDerivation derivation Dt x) =
      extendDeriv (Differential.implicitDeriv (CPoly.toPoly Dt)) (toRatFunc x) := by
  letI : Differential (CFieldSpec.K α) :=
    diffK
  letI : Differential (CRingSpec.R α) :=
    diffK
  have hxmk : toRatFunc x = RatFunc.mk (CPoly.toPoly (CFrac.num x)) (CPoly.toPoly (CFrac.den x)) := by
    rw [toRatFunc_eq_div, RatFunc.mk_eq_div]
    rfl
  rw [towerDerivCFracWithDerivation, toRatFunc_ofFraction, hxmk, extendDeriv_mk, RatFunc.mk_eq_div,
    CPolyEngine.toPoly_sub, LawfulCPolyEngine.toPoly_mul, LawfulCPolyEngine.toPoly_mul,
    LawfulCPolyEngine.toPoly_mul]
  rw [CPolyEngine.toPoly_monomialDerivWith derivation diffK,
    CPolyEngine.toPoly_monomialDerivWith derivation diffK,
    map_sub, map_mul, map_mul, map_pow]
  conv_rhs =>
    rw [map_sub, map_mul, map_mul]
  simp only [map_mul, pow_two]
  cases ‹CFieldSpec α›
  rfl

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P] [LawfulCPolyEngine.{u,v} P]
variable {F : (α : Type u) → [CField α] → Type u} [CFrac F P] [LawfulCFrac F P]
variable {α : Type u} [CField α] [CDiffField α] [CFieldSpec.{u,v} α]
  [CDiffFieldSpec.{u,v} α] [CFieldDomain α P]
variable [Algebra ℚ (CFieldSpec.K α)]

/-- The generic represented quotient-rule derivation realizes `extendDeriv` on `RatFunc`. -/
theorem toRatFunc_towerDerivCFracWith (Dt : P α) (x : F α) :
    toRatFunc (towerDerivCFracWith Dt x) =
      extendDeriv (Differential.implicitDeriv (CPoly.toPoly Dt)) (toRatFunc x) := by
  have hxmk : toRatFunc x = RatFunc.mk (CPoly.toPoly (CFrac.num x)) (CPoly.toPoly (CFrac.den x)) := by
    rw [toRatFunc_eq_div, RatFunc.mk_eq_div]
    rfl
  rw [towerDerivCFracWith, towerDerivCFracWithDerivation, toRatFunc_ofFraction, hxmk,
    extendDeriv_mk, RatFunc.mk_eq_div,
    CPolyEngine.toPoly_sub, LawfulCPolyEngine.toPoly_mul, LawfulCPolyEngine.toPoly_mul,
    LawfulCPolyEngine.toPoly_mul]
  simp only [CPolyEngine.monomialDerivWith_ofCDiffField]
  rw [CPolyEngine.toPoly_monomialDeriv, CPolyEngine.toPoly_monomialDeriv,
    map_sub, map_mul, map_mul, map_pow]
  conv_rhs =>
    rw [map_sub, map_mul, map_mul]
  simp only [map_mul, pow_two]
  cases ‹CFieldSpec α›
  rfl


end CFrac
end DeepWiki.SymbolicIntegration
