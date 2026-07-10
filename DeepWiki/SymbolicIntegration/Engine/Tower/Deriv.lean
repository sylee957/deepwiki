import DeepWiki.SymbolicIntegration.Engine.Tower.Lvl2
import DeepWiki.SymbolicIntegration.Engine.MonomialDeriv
import DeepWiki.SymbolicIntegration.Core.Differential.FractionFieldDeriv

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
variable {F : (α : Type u) → [CField α] → Type u} [CFrac F P]

/-- The quotient-rule tower derivation on any represented fraction `F` over polynomial representation `P`. -/
def towerDerivCFracWith {α : Type u} [CField α] [CDiffField α] [CFieldDomain α P]
    (Dt : P α) (x : F α) : F α :=
  CFrac.ofFraction
    (CPolyEngine.sub (CPolyEngine.mul (DensePoly.cmonomialDeriv Dt (CFrac.num x)) (CFrac.den x))
      (CPolyEngine.mul (CFrac.num x) (DensePoly.cmonomialDeriv Dt (CFrac.den x))))
    (CPolyEngine.mul (CFrac.den x) (CFrac.den x))
    (CFrac.cmulG_ne_zero_of (CFrac.cisZeroG_den x) (CFrac.cisZeroG_den x))

/-- Dense specialization of the representation-independent quotient-rule tower derivation. -/
def towerDerivCFrac {α : Type u} [CField α] [CDiffField α] [CFieldDomain α]
    (Dt : DensePoly α) (x : DenseFrac α) : DenseFrac α :=
  towerDerivCFracWith Dt x

/-- The generic tower derivative numerator is `D n · d − n · D d`. -/
@[simp] theorem towerDerivCFracWith_num {α : Type u} [CField α] [CDiffField α]
    [CFieldDomain α P] (Dt : P α) (x : F α) :
    CFrac.num (towerDerivCFracWith Dt x) =
      CPolyEngine.sub (CPolyEngine.mul (DensePoly.cmonomialDeriv Dt (CFrac.num x)) (CFrac.den x))
        (CPolyEngine.mul (CFrac.num x) (DensePoly.cmonomialDeriv Dt (CFrac.den x))) := by
  simp [towerDerivCFracWith]

/-- The generic tower derivative denominator is the square of the input denominator. -/
@[simp] theorem towerDerivCFracWith_den {α : Type u} [CField α] [CDiffField α]
    [CFieldDomain α P] (Dt : P α) (x : F α) :
    CFrac.den (towerDerivCFracWith Dt x) = CPolyEngine.mul (CFrac.den x) (CFrac.den x) := by
  simp [towerDerivCFracWith]

/-- The numerator of `towerDerivCFrac Dt x` is `D n · d − n · D d` (with `D = cmonomialDeriv Dt`). -/
theorem towerDerivCFracG_num {α : Type u} [CField α] [CDiffField α] [CFieldDomain α]
    (Dt : DensePoly α) (x : DenseFrac α) :
    (towerDerivCFrac Dt x).num
      = DensePoly.csub (DensePoly.cmul (DensePoly.cmonomialDeriv Dt x.num) x.den)
          (DensePoly.cmul x.num (DensePoly.cmonomialDeriv Dt x.den)) := rfl

/-- The denominator of `towerDerivCFrac Dt x` is `d·d`. -/
theorem towerDerivCFracG_den {α : Type u} [CField α] [CDiffField α] [CFieldDomain α]
    (Dt : DensePoly α) (x : DenseFrac α) :
    (towerDerivCFrac Dt x).den = DensePoly.cmul x.den x.den := rfl

end CFrac

/-! ### The iterating instance `CDiffField (DenseFrac α)` -/

section
variable {P : Type u → Type u} [CPoly P] [CPolyEngine P]
variable {F : (α : Type u) → [CField α] → Type u} [CFrac F P]
variable {α : Type u} [CField α] [CDiffField α] [CFieldDomain α P]

/-- Any `CFrac F P` inherits the quotient-rule derivation with the new monomial independent. -/
instance instCDiffFieldCFrac : CDiffField (F α) where
  cderiv := CFrac.towerDerivCFracWith (CPoly.one : P α)

end

/-! ### The level-2 derivation computes (`native_decide`) -/

/-- A level-2 scalar `c ∈ Lvl2 = DenseFrac (DenseFrac ℚ) = ℚ(x)(t₁)` from a numerator/denominator pair of
`DensePoly (DenseFrac ℚ)`s, with denominator a nonzero singleton `[d]`. -/
def lvl2OfList (num : DensePoly (DenseFrac ℚ)) (d : DenseFrac ℚ)
    (h : DensePoly.cisZero ([d] : DensePoly (DenseFrac ℚ)) = false) : Lvl2 :=
  CFrac.ofFraction num [d] h

/-- The level-2 scalar `t₁ ∈ ℚ(x)(t₁)` (numerator `[0, 1]` over ℚ(x): `t₁ = 0 + 1·t₁`, denominator
`[1]`). -/
def lvl2T1 : Lvl2 :=
  lvl2OfList [(CCommRing.zero : DenseFrac ℚ), CCommRing.one] (CCommRing.one : DenseFrac ℚ) (by native_decide)

/-! #### The level-2 scalar derivation `towerDerivCFrac` reduces -/

/-- `D(t₁) = 1` at level 2: the level-2 derivation applied to `t₁` is `1` (checked via `CCommRing.isZero` of
the difference). -/
theorem lvl2_deriv_t1_eq_one :
    CCommRing.isZero
      (CField.sub (CDiffField.cderiv lvl2T1) (CCommRing.one : Lvl2)) = true := by native_decide

-- `D(1) = 0` at level 2: the derivation annihilates the constant `1`.
example :
    CCommRing.isZero (CDiffField.cderiv (CCommRing.one : Lvl2)) = true := by native_decide

-- `D(0) = 0` at level 2: the derivation annihilates `0`.
example :
    CCommRing.isZero (CDiffField.cderiv (CCommRing.zero : Lvl2)) = true := by native_decide

/-! #### The level-2 monomial derivation `cmonomialDeriv` reduces over `ℚ(x)(t₁)[t₂]` -/

/-- `Dt₂ = [1]` over `DensePoly Lvl2`: the new level-2 monomial `t₂` is an independent variable
(`Dt₂ = 1`). -/
def lvl2Dt2 : DensePoly Lvl2 := [CCommRing.one]

/-- The level-2 polynomial `t₂² ∈ ℚ(x)(t₁)[t₂]` (`[0, 0, 1]`). -/
def lvl2T2sq : DensePoly Lvl2 := [CCommRing.zero, CCommRing.zero, CCommRing.one]

/-- The level-2 polynomial `2·t₂ ∈ ℚ(x)(t₁)[t₂]` (`[0, 2]`, with `2 = 1 + 1`). -/
def lvl2TwoT2 : DensePoly Lvl2 := [CCommRing.zero, CCommRing.add CCommRing.one CCommRing.one]

/-- `D(t₂²) = 2·t₂` over `ℚ(x)(t₁)[t₂]`: `cmonomialDeriv lvl2Dt2` computes the derivative of `t₂²` to
`2·t₂` (checked via `cisZero` of the difference). -/
theorem lvl2_monomialDeriv_t2sq_eq_two_t2 :
    DensePoly.cisZero (DensePoly.csub (DensePoly.cmonomialDeriv lvl2Dt2 lvl2T2sq) lvl2TwoT2) = true := by
  native_decide

-- `D(t₂) = 1` over `ℚ(x)(t₁)[t₂]`: `cmonomialDeriv` of the monomial `t₂` is the constant `1`.
example :
    DensePoly.cisZero (DensePoly.csub
      (DensePoly.cmonomialDeriv lvl2Dt2 [(CCommRing.zero : Lvl2), CCommRing.one]) [CCommRing.one]) = true := by
  native_decide

-- `D(t₁·t₂)` over `ℚ(x)(t₁)[t₂]` is nonzero (`cisZero = false`): `cmonomialDeriv`
-- differentiates the `t₂`-coefficients too, not just the `d/dt₂` part.
example :
    DensePoly.cisZero (DensePoly.cmonomialDeriv lvl2Dt2 [(CCommRing.zero : Lvl2), lvl2T1]) = false := by
  native_decide

-- `D(t₁·t₂) = t₁ + t₂` over `ℚ(x)(t₁)[t₂]` (checked via `cisZero` of the difference
-- against `[t₁, 1]`).
example :
    DensePoly.cisZero (DensePoly.csub
      (DensePoly.cmonomialDeriv lvl2Dt2 [(CCommRing.zero : Lvl2), lvl2T1])
      [lvl2T1, (CCommRing.one : Lvl2)]) = true := by native_decide

/-- The independent sparse tower monomial `t`. -/
def sparseTowerT : SparseFrac ℚ :=
  CFrac.ofPoly (CPoly.SparsePoly.ofList [(1, 1)])

/-- The generic iterated derivation computes `D(t) = 1` for `SparseFrac`. -/
theorem sparseTowerT_deriv_eq_one :
    CCommRing.isZero
      (CField.sub (CDiffField.cderiv sparseTowerT) (CCommRing.one : SparseFrac ℚ)) = true := by
  native_decide

/-! ### The abstract bridge `toRatFunc (towerDerivCFrac Dt x) = extendDeriv …` -/

namespace CFrac

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P] [LawfulCPolyEngine.{u,v} P]
variable {F : (α : Type u) → [CField α] → Type u} [CFrac F P]
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
  rw [towerDerivCFracWith, toRatFunc_ofFraction, hxmk, extendDeriv_mk, RatFunc.mk_eq_div,
    CPolyEngine.toPoly_sub, LawfulCPolyEngine.toPoly_mul, LawfulCPolyEngine.toPoly_mul,
    LawfulCPolyEngine.toPoly_mul, CPolyEngine.toPoly_cmonomialDeriv,
    CPolyEngine.toPoly_cmonomialDeriv, map_sub, map_mul, map_mul, map_pow]
  conv_rhs =>
    rw [map_sub, map_mul, map_mul]
  simp only [map_mul, pow_two]
  cases ‹CFieldSpec α›
  rfl


end CFrac

/-! ### Axiom audit -/

-- The level-2 scalar derivation `D(t₁) = 1` (`native_decide`):
-- `[propext, Classical.choice, Quot.sound, lvl2T1._native…, lvl2_deriv_t1_eq_one._native…]`.
#print axioms lvl2_deriv_t1_eq_one

-- The level-2 monomial derivation `D(t₂²) = 2·t₂` (`native_decide`):
-- `[propext, Classical.choice, Quot.sound, lvl2_monomialDeriv_t2sq_eq_two_t2._native…]`.
#print axioms lvl2_monomialDeriv_t2sq_eq_two_t2

-- The abstract bridge (computable tower derivation vs `extendDeriv`):
-- `[propext, Classical.choice, Quot.sound]` (no native axiom — it is a proof, not a computation).
#print axioms CFrac.toRatFunc_towerDerivCFracWith

end DeepWiki.SymbolicIntegration
