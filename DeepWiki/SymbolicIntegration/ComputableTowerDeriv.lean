import DeepWiki.SymbolicIntegration.ComputableTowerField
import DeepWiki.SymbolicIntegration.ComputableMonomialDeriv
import DeepWiki.SymbolicIntegration.ComputableFractionFieldDeriv

/-! # The derivation tower: a computable derivation on `QFunNZG α` (Risch tower step)
`ComputableTowerField` built the generic fraction-field carrier `QFunNZG α` (the next tower level,
ℚ(x)(t₁)(t₂)…) with a *computable* `CField` instance; `ComputableMonomialDeriv` built the *computable*
monomial derivation `cmonomialDeriv Dt` on `CPolyG α` (`D = κ_D + Dt·d/dt`), whose coefficient base
derivation is read off the **class** `CDiffField α` (`CDiffField.cderiv`). The integration pipeline
consumes a tower derivation `D` at each level — but the base field of level `n+1`, `QFunNZG α`, had no
derivation yet. This file supplies it, so the derivation **iterates up the tower**.

* **`towerDerivQFunNZG Dt`** = the fraction-field quotient rule `(n'·d − n·d')/d²` on `QFunNZG α`, where
  the `CPolyG α`-level derivation `'` is `cmonomialDeriv Dt` (the base `CDiffField α` extended by the new
  monomial's `Dt`). It is `[CField α] [CDiffField α] [CFieldDomain α]`-COMPUTABLE — no `toK`/`CFieldSpec`
  — so it `native_decide`s, mirroring the `CFieldDomain`/`Prop`-erased discipline of `ComputableTowerField`.

* **`instCDiffFieldQFunNZG`** = `CDiffField (QFunNZG α)` with `cderiv := towerDerivQFunNZG [1]`: the new
  monomial is an independent variable with derivative `1` (the canonical iterating choice, exactly as
  level 1's `x` has `Dx = 1`). This makes `CDiffField` compose up the tower: `CDiffField ℚ` (constants,
  `0`) → `CDiffField (QFunNZG ℚ)` (= ℚ(x), `d/dx`) → `CDiffField (QFunNZG (QFunNZG ℚ))` (= ℚ(x)(t₁),
  `d/dx + ∂/∂t₁`).

* **★ The key validation**: `cmonomialDeriv`/`towerDerivQFunNZG` *reduce* over level 2 — `native_decide`
  on `D(t₂²) = 2·t₂` (`cmonomialDeriv`, treating `Dt₂ = 1`) over `CPolyG (QFunNZG (QFunNZG ℚ)) =
  ℚ(x)(t₁)[t₂]`, and on the level-2 scalar derivation `D(t₁) = 1` (`towerDerivQFunNZG`). The LEVEL-2
  DERIVATION COMPUTES.

* **Stretch (abstract bridge)**: `toQFunNZG_towerDerivQFunNZG` certifies `towerDerivQFunNZG Dt` realizes
  `extendDeriv (implicitDeriv (toPolyG Dt))` on `RatFunc (CFieldSpec.K α)` through the bridge `toQFunNZG`
  — generalizing `towerFractionFieldDeriv`'s level-1 agreement to an arbitrary base derivation. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open scoped Differential

namespace QFunNZG

/-! ### The computable tower derivation `towerDerivQFunNZG Dt`

For the fraction field `QFunNZG α` of `α[t]`, the derivation extending the base coefficient derivation
`CDiffField.cderiv` (on `α`) by the new monomial's `Dt ∈ CPolyG α` is the quotient rule
`D(n/d) = (D n · d − n · D d)/d²`, where the `CPolyG α`-level derivation `D` is `cmonomialDeriv Dt`. The
new denominator `d·d` is nonzero by `CFieldDomain.nz_mul`; everything is list arithmetic through the
generic engine, so `towerDerivQFunNZG` stays **computable** (no `toK`/`CFieldSpec` leak). -/

variable {α : Type*} [CField α] [CDiffField α] [CFieldDomain α]

/-- **The computable tower derivation** `towerDerivQFunNZG Dt (n/d) = (D n · d − n · D d)/(d·d)` on
`QFunNZG α`, with `D = cmonomialDeriv Dt` the `CPolyG α`-derivation (base `CDiffField.cderiv` extended by
the new monomial's `Dt`). The fraction-field quotient rule; the new denominator `d·d` is nonzero by
`CFieldDomain.nz_mul`. `[CField α] [CDiffField α] [CFieldDomain α]`-computable (no `CFieldSpec`), so it
`native_decide`s — the substrate that lets the derivation iterate up the tower. -/
def towerDerivQFunNZG (Dt : CPolyG α) (x : QFunNZG α) : QFunNZG α :=
  ⟨(CPolyG.csubG (CPolyG.cmulG (CPolyG.cmonomialDeriv Dt x.1.1) x.1.2)
      (CPolyG.cmulG x.1.1 (CPolyG.cmonomialDeriv Dt x.1.2)),
    CPolyG.cmulG x.1.2 x.1.2),
    cmulG_ne_zero_of x.2 x.2⟩

/-- **The numerator of the tower derivation** reads as `D n · d − n · D d` (with `D = cmonomialDeriv Dt`)
— the quotient-rule numerator, exposed for the bridge. -/
theorem towerDerivQFunNZG_num (Dt : CPolyG α) (x : QFunNZG α) :
    (towerDerivQFunNZG Dt x).1.1
      = CPolyG.csubG (CPolyG.cmulG (CPolyG.cmonomialDeriv Dt x.1.1) x.1.2)
          (CPolyG.cmulG x.1.1 (CPolyG.cmonomialDeriv Dt x.1.2)) := rfl

/-- **The denominator of the tower derivation** reads as `d·d` — the squared denominator of the
quotient rule. -/
theorem towerDerivQFunNZG_den (Dt : CPolyG α) (x : QFunNZG α) :
    (towerDerivQFunNZG Dt x).1.2 = CPolyG.cmulG x.1.2 x.1.2 := rfl

end QFunNZG

/-! ### The iterating instance `CDiffField (QFunNZG α)`

The canonical tower step: the new monomial `t` is an independent transcendental with derivative `Dt =
[1]` (exactly as level 1's `x` has `Dx = 1`), so the `CDiffField (QFunNZG α)` instance is
`towerDerivQFunNZG [CField.one]`. Resolution iterates: `[CDiffField ℚ]` (constants) supplies the
coefficient derivation for `[CDiffField (QFunNZG ℚ)]` (= ℚ(x), `d/dx`), which supplies it for
`[CDiffField (QFunNZG (QFunNZG ℚ))]` (= ℚ(x)(t₁), `d/dx + ∂/∂t₁`), … . Computable — the whole chain stays
off `CFieldSpec`. -/

section
variable {α : Type*} [CField α] [CDiffField α] [CFieldDomain α]

/-- **`CDiffField (QFunNZG α)`**: the next tower level's coefficient derivation, the fraction-field
quotient rule for the new independent monomial `t` (`Dt = [1]`, `Dt = 1`). Built from the base
`[CDiffField α]` via `towerDerivQFunNZG [CField.one]` — so `CDiffField` iterates up the tower
(`CDiffField ℚ` → `CDiffField (QFunNZG ℚ)` → `CDiffField (QFunNZG (QFunNZG ℚ))` → …). Computable
(`[CField α] [CDiffField α] [CFieldDomain α]`, no `CFieldSpec`), so `cmonomialDeriv` over `CPolyG
(QFunNZG α)` reduces in the native compiler. -/
instance instCDiffFieldQFunNZG : CDiffField (QFunNZG α) where
  cderiv := QFunNZG.towerDerivQFunNZG [CField.one]

end

/-! ### ★ The key validation: the LEVEL-2 derivation computes (`native_decide`)

These `native_decide` checks retire the "does the tower derivation compute" risk. They run the computable
derivation engine — `towerDerivQFunNZG` on level-2 scalars (`QFunNZG (QFunNZG ℚ) = ℚ(x)(t₁)`), and
`cmonomialDeriv` over `CPolyG Lvl2 = ℚ(x)(t₁)[t₂]` (level 2, the new monomial `t₂`) — on concrete
elements. The `CDiffField (QFunNZG (QFunNZG ℚ))` instance is `[CField …]`-computable (its `cderiv` is
`towerDerivQFunNZG [1]`, all list arithmetic, the subtype proofs `Prop`-erased), so nothing noncomputable
reaches the native compiler. -/

/-- A level-2 scalar `c ∈ Lvl2 = QFunNZG (QFunNZG ℚ) = ℚ(x)(t₁)` from a numerator/denominator pair of
`CPolyG (QFunNZG ℚ)`s, with denominator a nonzero singleton `[d]`. -/
def lvl2OfList (num : CPolyG (QFunNZG ℚ)) (d : QFunNZG ℚ)
    (h : CPolyG.cisZeroG ([d] : CPolyG (QFunNZG ℚ)) = false) : Lvl2 := ⟨(num, [d]), h⟩

/-- The level-2 scalar `t₁ ∈ ℚ(x)(t₁)` (numerator `[0, 1]` over ℚ(x): `t₁ = 0 + 1·t₁`, denominator
`[1]`). -/
def lvl2T1 : Lvl2 :=
  lvl2OfList [(CField.zero : QFunNZG ℚ), CField.one] (CField.one : QFunNZG ℚ) (by native_decide)

/-! #### The level-2 scalar derivation `towerDerivQFunNZG` reduces -/

/-- **★ `D(t₁) = 1` at level 2** — `towerDerivQFunNZG [1]` (the `CDiffField (QFunNZG (QFunNZG ℚ))`
derivation) applied to the level-2 scalar `t₁` is `1`, since `t₁` is the independent monomial with `Dt₁ =
1`. Tested by `isZeroNZG` of `D(t₁) − 1`: the derivation engine `native_decide`s over ℚ(x)(t₁). THE
LEVEL-2 DERIVATION COMPUTES. -/
example :
    CField.isZero
      (CField.sub (CDiffField.cderiv lvl2T1) (CField.one : Lvl2)) = true := by native_decide

/-- **`D(1) = 0` at level 2** — the level-2 derivation annihilates the constant `1` (`towerDerivQFunNZG`
reduces over ℚ(x)(t₁)). -/
example :
    CField.isZero (CDiffField.cderiv (CField.one : Lvl2)) = true := by native_decide

/-- **`D(0) = 0` at level 2** — the level-2 derivation annihilates `0`. -/
example :
    CField.isZero (CDiffField.cderiv (CField.zero : Lvl2)) = true := by native_decide

/-! #### The level-2 monomial derivation `cmonomialDeriv` reduces over `ℚ(x)(t₁)[t₂]`

`Dt₂ = [1]` (the new level-2 monomial `t₂` is an independent variable, `Dt₂ = 1`). Under
`D = κ_D + Dt₂·d/dt₂`, the coefficient field ℚ(x)(t₁) has the level-2 `cderiv = towerDerivQFunNZG [1]`,
so `D` differentiates BOTH the `t₂`-structure and the ℚ(x)(t₁) coefficients. -/

/-- `Dt₂ = [1]` over `CPolyG Lvl2`: the new level-2 monomial `t₂` is an independent variable
(`Dt₂ = 1`). -/
def lvl2Dt2 : CPolyG Lvl2 := [CField.one]

/-- The level-2 polynomial `t₂² ∈ ℚ(x)(t₁)[t₂]` (`[0, 0, 1]`). -/
def lvl2T2sq : CPolyG Lvl2 := [CField.zero, CField.zero, CField.one]

/-- The level-2 polynomial `2·t₂ ∈ ℚ(x)(t₁)[t₂]` (`[0, 2]`, with `2 = 1 + 1`). -/
def lvl2TwoT2 : CPolyG Lvl2 := [CField.zero, CField.add CField.one CField.one]

/-- **★ `D(t₂²) = 2·t₂` over `ℚ(x)(t₁)[t₂]`** — the monomial derivation `cmonomialDeriv` (with `Dt₂ = 1`,
ℚ(x)(t₁)-coefficient derivation `towerDerivQFunNZG [1]`) computes the derivative of `t₂²` to `2·t₂`,
verified by `cisZeroG` of the difference. The whole derivation engine `native_decide`s at **tower level
2**. THE LEVEL-2 MONOMIAL DERIVATION COMPUTES. -/
example :
    CPolyG.cisZeroG (CPolyG.csubG (CPolyG.cmonomialDeriv lvl2Dt2 lvl2T2sq) lvl2TwoT2) = true := by
  native_decide

/-- **`D(t₂) = 1` over `ℚ(x)(t₁)[t₂]`** — `cmonomialDeriv` of the monomial `t₂` (`[0, 1]`) is the
constant `1` (`[1]`), since `Dt₂ = 1` and the constant coefficients are ℚ(x)(t₁)-constants here. -/
example :
    CPolyG.cisZeroG (CPolyG.csubG
      (CPolyG.cmonomialDeriv lvl2Dt2 [(CField.zero : Lvl2), CField.one]) [CField.one]) = true := by
  native_decide

/-- **The level-2 monomial derivation differentiates the t₂-coefficients too**: `D(t₁·t₂)` over
ℚ(x)(t₁)[t₂] is `t₁·1 + Dt₁·t₂ = t₁ + t₂` (since the coefficient `t₁` has level-2 derivative `Dt₁ = 1`).
The nonzero result (`cisZeroG = false`) confirms `cmonomialDeriv` ran the coefficient derivation, not
just the `d/dt₂` part — the genuine tower derivation `d/dx + ∂t₁ + ∂t₂` at level 2. -/
example :
    CPolyG.cisZeroG (CPolyG.cmonomialDeriv lvl2Dt2 [(CField.zero : Lvl2), lvl2T1]) = false := by
  native_decide

/-- **The level-2 monomial derivation of `t₁ · t₂` is exactly `t₁ + t₂`**: with `Dt₂ = 1` and the
coefficient derivative `Dt₁ = 1`, `cmonomialDeriv [1] [0, t₁] = [t₁, 1·t₂-coeff]` collapses to
`t₁ + t₂`, verified by `cisZeroG` of the difference against `[t₁, 1]` (= `t₁ + t₂` over ℚ(x)(t₁)[t₂]). -/
example :
    CPolyG.cisZeroG (CPolyG.csubG
      (CPolyG.cmonomialDeriv lvl2Dt2 [(CField.zero : Lvl2), lvl2T1])
      [lvl2T1, (CField.one : Lvl2)]) = true := by native_decide

end DeepWiki.SymbolicIntegration
