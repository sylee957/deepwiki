import DeepWiki.SymbolicIntegration.Computable.Tower.Field
import DeepWiki.SymbolicIntegration.Computable.MonomialDeriv
import DeepWiki.SymbolicIntegration.Computable.FractionFieldDeriv

/-! # A computable derivation on the tower carrier `QFunNZG α`
`towerDerivQFunNZG Dt` is the fraction-field quotient-rule derivation on `QFunNZG α`, and
`instCDiffFieldQFunNZG` makes `CDiffField` iterate up the tower with the new monomial as an independent
variable (`Dt = [1]`). Both are computable (no `CFieldSpec`), and `toQFunNZG_towerDerivQFunNZG` bridges to
Mathlib's abstract `extendDeriv` on `RatFunc (CFieldSpec.K α)`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open scoped Differential

namespace QFunNZG

/-! ### The computable tower derivation `towerDerivQFunNZG Dt` -/

variable {α : Type*} [CField α] [CDiffField α] [CFieldDomain α]

/-- The tower derivation `towerDerivQFunNZG Dt (n/d) = (D n · d − n · D d)/(d·d)` on `QFunNZG α`, with
`D = cmonomialDeriv Dt`; the fraction-field quotient rule, computable (no `CFieldSpec`). -/
def towerDerivQFunNZG (Dt : CPolyG α) (x : QFunNZG α) : QFunNZG α :=
  ⟨(CPolyG.csubG (CPolyG.cmulG (CPolyG.cmonomialDeriv Dt x.1.1) x.1.2)
      (CPolyG.cmulG x.1.1 (CPolyG.cmonomialDeriv Dt x.1.2)),
    CPolyG.cmulG x.1.2 x.1.2),
    cmulG_ne_zero_of x.2 x.2⟩

/-- The numerator of `towerDerivQFunNZG Dt x` is `D n · d − n · D d` (with `D = cmonomialDeriv Dt`). -/
theorem towerDerivQFunNZG_num (Dt : CPolyG α) (x : QFunNZG α) :
    (towerDerivQFunNZG Dt x).1.1
      = CPolyG.csubG (CPolyG.cmulG (CPolyG.cmonomialDeriv Dt x.1.1) x.1.2)
          (CPolyG.cmulG x.1.1 (CPolyG.cmonomialDeriv Dt x.1.2)) := rfl

/-- The denominator of `towerDerivQFunNZG Dt x` is `d·d`. -/
theorem towerDerivQFunNZG_den (Dt : CPolyG α) (x : QFunNZG α) :
    (towerDerivQFunNZG Dt x).1.2 = CPolyG.cmulG x.1.2 x.1.2 := rfl

end QFunNZG

/-! ### The iterating instance `CDiffField (QFunNZG α)` -/

section
variable {α : Type*} [CField α] [CDiffField α] [CFieldDomain α]

/-- `CDiffField (QFunNZG α)` with `cderiv := towerDerivQFunNZG [CField.one]`: the new monomial is an
independent variable (`Dt = 1`), so `CDiffField` iterates up the tower. Computable (no `CFieldSpec`). -/
instance instCDiffFieldQFunNZG : CDiffField (QFunNZG α) where
  cderiv := QFunNZG.towerDerivQFunNZG [CField.one]

end

/-! ### The level-2 derivation computes (`native_decide`) -/

/-- A level-2 scalar `c ∈ Lvl2 = QFunNZG (QFunNZG ℚ) = ℚ(x)(t₁)` from a numerator/denominator pair of
`CPolyG (QFunNZG ℚ)`s, with denominator a nonzero singleton `[d]`. -/
def lvl2OfList (num : CPolyG (QFunNZG ℚ)) (d : QFunNZG ℚ)
    (h : CPolyG.cisZeroG ([d] : CPolyG (QFunNZG ℚ)) = false) : Lvl2 := ⟨(num, [d]), h⟩

/-- The level-2 scalar `t₁ ∈ ℚ(x)(t₁)` (numerator `[0, 1]` over ℚ(x): `t₁ = 0 + 1·t₁`, denominator
`[1]`). -/
def lvl2T1 : Lvl2 :=
  lvl2OfList [(CField.zero : QFunNZG ℚ), CField.one] (CField.one : QFunNZG ℚ) (by native_decide)

/-! #### The level-2 scalar derivation `towerDerivQFunNZG` reduces -/

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

/-- `Dt₂ = [1]` over `CPolyG Lvl2`: the new level-2 monomial `t₂` is an independent variable
(`Dt₂ = 1`). -/
def lvl2Dt2 : CPolyG Lvl2 := [CField.one]

/-- The level-2 polynomial `t₂² ∈ ℚ(x)(t₁)[t₂]` (`[0, 0, 1]`). -/
def lvl2T2sq : CPolyG Lvl2 := [CField.zero, CField.zero, CField.one]

/-- The level-2 polynomial `2·t₂ ∈ ℚ(x)(t₁)[t₂]` (`[0, 2]`, with `2 = 1 + 1`). -/
def lvl2TwoT2 : CPolyG Lvl2 := [CField.zero, CField.add CField.one CField.one]

/-- `D(t₂²) = 2·t₂` over `ℚ(x)(t₁)[t₂]`: `cmonomialDeriv lvl2Dt2` computes the derivative of `t₂²` to
`2·t₂` (checked via `cisZeroG` of the difference). -/
theorem lvl2_monomialDeriv_t2sq_eq_two_t2 :
    CPolyG.cisZeroG (CPolyG.csubG (CPolyG.cmonomialDeriv lvl2Dt2 lvl2T2sq) lvl2TwoT2) = true := by
  native_decide

-- `D(t₂) = 1` over `ℚ(x)(t₁)[t₂]`: `cmonomialDeriv` of the monomial `t₂` is the constant `1`.
example :
    CPolyG.cisZeroG (CPolyG.csubG
      (CPolyG.cmonomialDeriv lvl2Dt2 [(CField.zero : Lvl2), CField.one]) [CField.one]) = true := by
  native_decide

-- `D(t₁·t₂)` over `ℚ(x)(t₁)[t₂]` is nonzero (`cisZeroG = false`): `cmonomialDeriv`
-- differentiates the `t₂`-coefficients too, not just the `d/dt₂` part.
example :
    CPolyG.cisZeroG (CPolyG.cmonomialDeriv lvl2Dt2 [(CField.zero : Lvl2), lvl2T1]) = false := by
  native_decide

-- `D(t₁·t₂) = t₁ + t₂` over `ℚ(x)(t₁)[t₂]` (checked via `cisZeroG` of the difference
-- against `[t₁, 1]`).
example :
    CPolyG.cisZeroG (CPolyG.csubG
      (CPolyG.cmonomialDeriv lvl2Dt2 [(CField.zero : Lvl2), lvl2T1])
      [lvl2T1, (CField.one : Lvl2)]) = true := by native_decide

/-! ### The abstract bridge `toQFunNZG (towerDerivQFunNZG Dt x) = extendDeriv …` -/

namespace QFunNZG

variable {α : Type*} [CField α] [CDiffField α] [CFieldSpec α] [CDiffFieldSpec α] [CFieldDomain α]
variable [Algebra ℚ (CFieldSpec.K α)]

/-- `toQFunNZG (towerDerivQFunNZG Dt x) = extendDeriv (implicitDeriv (toPolyG Dt)) (toQFunNZG x)` in
`RatFunc (CFieldSpec.K α)`: the computable tower derivation realizes Mathlib's `extendDeriv`. -/
theorem toQFunNZG_towerDerivQFunNZG (Dt : CPolyG α) (x : QFunNZG α) :
    toQFunNZG (towerDerivQFunNZG Dt x)
      = extendDeriv (Differential.implicitDeriv (CPolyG.toPolyG Dt)) (toQFunNZG x) := by
  obtain ⟨⟨n, d⟩, hd⟩ := x
  -- read `toQFunNZG x` as `RatFunc.mk (toPolyG n) (toPolyG d)`, apply the quotient rule `extendDeriv_mk`.
  have hxmk : toQFunNZG (⟨(n, d), hd⟩ : QFunNZG α)
      = RatFunc.mk (CPolyG.toPolyG n) (CPolyG.toPolyG d) := by
    rw [toQFunNZG, RatFunc.mk_eq_div]
  rw [hxmk, extendDeriv_mk, RatFunc.mk_eq_div, map_sub, map_mul, map_mul, map_pow]
  -- the LHS numerator/denominator, read through `toPolyG`, with `toPolyG_cmonomialDeriv` identifying
  -- the computable monomial derivation as `implicitDeriv (toPolyG Dt)`.
  show amG α (CPolyG.toPolyG (CPolyG.csubG
        (CPolyG.cmulG (CPolyG.cmonomialDeriv Dt n) d) (CPolyG.cmulG n (CPolyG.cmonomialDeriv Dt d))))
      / amG α (CPolyG.toPolyG (CPolyG.cmulG d d)) = _
  simp [CPolyG.toPolyG_cmonomialDeriv, map_sub, map_mul, pow_two]

end QFunNZG

/-! ### The construction's axioms -/

-- The headline level-2 scalar derivation `D(t₁) = 1` (`native_decide`):
-- `[propext, Classical.choice, Quot.sound, lvl2T1._native…, lvl2_deriv_t1_eq_one._native…]`.
#print axioms lvl2_deriv_t1_eq_one

-- The headline level-2 monomial derivation `D(t₂²) = 2·t₂` (`native_decide`):
-- `[propext, Classical.choice, Quot.sound, lvl2_monomialDeriv_t2sq_eq_two_t2._native…]`.
#print axioms lvl2_monomialDeriv_t2sq_eq_two_t2

-- The abstract bridge (computable tower derivation vs `extendDeriv`):
-- `[propext, Classical.choice, Quot.sound]` (no native axiom — it is a proof, not a computation).
#print axioms QFunNZG.toQFunNZG_towerDerivQFunNZG

end DeepWiki.SymbolicIntegration
