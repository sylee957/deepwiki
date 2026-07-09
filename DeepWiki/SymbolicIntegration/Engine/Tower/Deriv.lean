import DeepWiki.SymbolicIntegration.Engine.Tower.Field
import DeepWiki.SymbolicIntegration.Engine.MonomialDeriv
import DeepWiki.SymbolicIntegration.Core.Differential.FractionFieldDeriv

/-! # A computable derivation on the tower carrier `CFrac α`
`towerDerivCFrac Dt` is the fraction-field quotient-rule derivation on `CFrac α`, and
`instCDiffFieldCFrac` makes `CDiffField` iterate up the tower with the new monomial as an independent
variable (`Dt = [1]`). Both are computable (no `CFieldSpec`), and `toCFracG_towerDerivCFracG` bridges to
Mathlib's abstract `extendDeriv` on `RatFunc (CFieldSpec.K α)`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open scoped Differential

namespace CFrac

/-! ### The computable tower derivation `towerDerivCFrac Dt` -/

variable {α : Type*} [CField α] [CDiffField α] [CFieldDomain α]

/-- The tower derivation `towerDerivCFrac Dt (n/d) = (D n · d − n · D d)/(d·d)` on `CFrac α`, with
`D = cmonomialDeriv Dt`; the fraction-field quotient rule, computable (no `CFieldSpec`). -/
def towerDerivCFrac (Dt : CPoly α) (x : CFrac α) : CFrac α :=
  ⟨(CPoly.csub (CPoly.cmul (CPoly.cmonomialDeriv Dt x.1.1) x.1.2)
      (CPoly.cmul x.1.1 (CPoly.cmonomialDeriv Dt x.1.2)),
    CPoly.cmul x.1.2 x.1.2),
    cmulG_ne_zero_of x.2 x.2⟩

/-- The numerator of `towerDerivCFrac Dt x` is `D n · d − n · D d` (with `D = cmonomialDeriv Dt`). -/
theorem towerDerivCFracG_num (Dt : CPoly α) (x : CFrac α) :
    (towerDerivCFrac Dt x).1.1
      = CPoly.csub (CPoly.cmul (CPoly.cmonomialDeriv Dt x.1.1) x.1.2)
          (CPoly.cmul x.1.1 (CPoly.cmonomialDeriv Dt x.1.2)) := rfl

/-- The denominator of `towerDerivCFrac Dt x` is `d·d`. -/
theorem towerDerivCFracG_den (Dt : CPoly α) (x : CFrac α) :
    (towerDerivCFrac Dt x).1.2 = CPoly.cmul x.1.2 x.1.2 := rfl

end CFrac

/-! ### The iterating instance `CDiffField (CFrac α)` -/

section
variable {α : Type*} [CField α] [CDiffField α] [CFieldDomain α]

/-- `CDiffField (CFrac α)` with `cderiv := towerDerivCFrac [CField.one]`: the new monomial is an
independent variable (`Dt = 1`), so `CDiffField` iterates up the tower. Computable (no `CFieldSpec`). -/
instance instCDiffFieldCFrac : CDiffField (CFrac α) where
  cderiv := CFrac.towerDerivCFrac [CField.one]

end

/-! ### The level-2 derivation computes (`native_decide`) -/

/-- A level-2 scalar `c ∈ Lvl2 = CFrac (CFrac ℚ) = ℚ(x)(t₁)` from a numerator/denominator pair of
`CPoly (CFrac ℚ)`s, with denominator a nonzero singleton `[d]`. -/
def lvl2OfList (num : CPoly (CFrac ℚ)) (d : CFrac ℚ)
    (h : CPoly.cisZero ([d] : CPoly (CFrac ℚ)) = false) : Lvl2 := ⟨(num, [d]), h⟩

/-- The level-2 scalar `t₁ ∈ ℚ(x)(t₁)` (numerator `[0, 1]` over ℚ(x): `t₁ = 0 + 1·t₁`, denominator
`[1]`). -/
def lvl2T1 : Lvl2 :=
  lvl2OfList [(CField.zero : CFrac ℚ), CField.one] (CField.one : CFrac ℚ) (by native_decide)

/-! #### The level-2 scalar derivation `towerDerivCFrac` reduces -/

/-- `D(t₁) = 1` at level 2: the level-2 derivation applied to `t₁` is `1` (checked via `CField.isZero` of
the difference). -/
theorem lvl2_deriv_t1_eq_one :
    CField.isZero
      (CField.sub (CDiffField.cderiv lvl2T1) (CField.one : Lvl2)) = true := by native_decide

-- `D(1) = 0` at level 2: the derivation annihilates the constant `1`.
example :
    CField.isZero (CDiffField.cderiv (CField.one : Lvl2)) = true := by native_decide

-- `D(0) = 0` at level 2: the derivation annihilates `0`.
example :
    CField.isZero (CDiffField.cderiv (CField.zero : Lvl2)) = true := by native_decide

/-! #### The level-2 monomial derivation `cmonomialDeriv` reduces over `ℚ(x)(t₁)[t₂]` -/

/-- `Dt₂ = [1]` over `CPoly Lvl2`: the new level-2 monomial `t₂` is an independent variable
(`Dt₂ = 1`). -/
def lvl2Dt2 : CPoly Lvl2 := [CField.one]

/-- The level-2 polynomial `t₂² ∈ ℚ(x)(t₁)[t₂]` (`[0, 0, 1]`). -/
def lvl2T2sq : CPoly Lvl2 := [CField.zero, CField.zero, CField.one]

/-- The level-2 polynomial `2·t₂ ∈ ℚ(x)(t₁)[t₂]` (`[0, 2]`, with `2 = 1 + 1`). -/
def lvl2TwoT2 : CPoly Lvl2 := [CField.zero, CField.add CField.one CField.one]

/-- `D(t₂²) = 2·t₂` over `ℚ(x)(t₁)[t₂]`: `cmonomialDeriv lvl2Dt2` computes the derivative of `t₂²` to
`2·t₂` (checked via `cisZero` of the difference). -/
theorem lvl2_monomialDeriv_t2sq_eq_two_t2 :
    CPoly.cisZero (CPoly.csub (CPoly.cmonomialDeriv lvl2Dt2 lvl2T2sq) lvl2TwoT2) = true := by
  native_decide

-- `D(t₂) = 1` over `ℚ(x)(t₁)[t₂]`: `cmonomialDeriv` of the monomial `t₂` is the constant `1`.
example :
    CPoly.cisZero (CPoly.csub
      (CPoly.cmonomialDeriv lvl2Dt2 [(CField.zero : Lvl2), CField.one]) [CField.one]) = true := by
  native_decide

-- `D(t₁·t₂)` over `ℚ(x)(t₁)[t₂]` is nonzero (`cisZero = false`): `cmonomialDeriv`
-- differentiates the `t₂`-coefficients too, not just the `d/dt₂` part.
example :
    CPoly.cisZero (CPoly.cmonomialDeriv lvl2Dt2 [(CField.zero : Lvl2), lvl2T1]) = false := by
  native_decide

-- `D(t₁·t₂) = t₁ + t₂` over `ℚ(x)(t₁)[t₂]` (checked via `cisZero` of the difference
-- against `[t₁, 1]`).
example :
    CPoly.cisZero (CPoly.csub
      (CPoly.cmonomialDeriv lvl2Dt2 [(CField.zero : Lvl2), lvl2T1])
      [lvl2T1, (CField.one : Lvl2)]) = true := by native_decide

/-! ### The abstract bridge `toCFrac (towerDerivCFrac Dt x) = extendDeriv …` -/

namespace CFrac

variable {α : Type*} [CField α] [CDiffField α] [CFieldSpec α] [CDiffFieldSpec α] [CFieldDomain α]
variable [Algebra ℚ (CFieldSpec.K α)]

/-- `toCFrac (towerDerivCFrac Dt x) = extendDeriv (implicitDeriv (toPoly Dt)) (toCFrac x)` in
`RatFunc (CFieldSpec.K α)`: the computable tower derivation realizes Mathlib's `extendDeriv`. -/
theorem toCFracG_towerDerivCFracG (Dt : CPoly α) (x : CFrac α) :
    toCFrac (towerDerivCFrac Dt x)
      = extendDeriv (Differential.implicitDeriv (CPoly.toPoly Dt)) (toCFrac x) := by
  obtain ⟨⟨n, d⟩, hd⟩ := x
  -- read `toCFrac x` as `RatFunc.mk (toPoly n) (toPoly d)`, apply the quotient rule `extendDeriv_mk`.
  have hxmk : toCFrac (⟨(n, d), hd⟩ : CFrac α)
      = RatFunc.mk (CPoly.toPoly n) (CPoly.toPoly d) := by
    rw [toCFrac, RatFunc.mk_eq_div]
  rw [hxmk, extendDeriv_mk, RatFunc.mk_eq_div, map_sub, map_mul, map_mul, map_pow]
  -- the LHS numerator/denominator, read through `toPoly`, with `toPolyG_cmonomialDeriv` identifying
  -- the computable monomial derivation as `implicitDeriv (toPoly Dt)`.
  show am α (CPoly.toPoly (CPoly.csub
        (CPoly.cmul (CPoly.cmonomialDeriv Dt n) d) (CPoly.cmul n (CPoly.cmonomialDeriv Dt d))))
      / am α (CPoly.toPoly (CPoly.cmul d d)) = _
  simp [CPoly.toPolyG_cmonomialDeriv, map_sub, map_mul, pow_two]

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
#print axioms CFrac.toCFracG_towerDerivCFracG

end DeepWiki.SymbolicIntegration
