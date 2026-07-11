import DeepWiki.SymbolicIntegration.Engine.Tower.RischDEWellFounded

/-! # The tower RDE instance `CRischField (DenseFrac β)`

The `CRischField (DenseFrac β)` instance tying the tower recursion, running `cRischDE`. Solving an RDE at
level `n+1` runs the pipeline at level `n` and recurses into the level-`n` `crischDESolve`, bottoming at
`CRischField ℚ`. -/

open Polynomial Classical

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac

section
variable {β : Type*} [CField β] [CDiffField β] [CFieldDomain β DensePoly]
  [CPolyGcd DensePoly β] [CPolySplitFactor DensePoly β] [CRischField β]

/-- `CRischField (DenseFrac β)` — the gated, sound RDE over `β(s) = DenseFrac β`, running `cRischDE` over
`DensePoly β = β[s]` (`Ds = [1]`) with selected gcd and differential split operations and
`[CRischField β]` for the base solve, behind the gate `CFrac.denomNormalGate`. Bottoms at
`CRischField ℚ`. -/
instance instCRischFieldCFrac : CRischField (DenseFrac β) where
  crischDESolve f g :=
    if CFrac.denomNormalGate f then
      match DensePoly.cRischDE ([CCommRing.one] : DensePoly β) (CFrac.num f) (CFrac.den f)
          (CFrac.num g) (CFrac.den g) with
      | none => none
      | some (ynum, yden) =>
        if h : DensePoly.cisZero yden = false then some (CFrac.ofFraction ynum yden h) else none
    else none

end

/-! ## Validation: the tower RDE computes over `DenseFrac ℚ` -/

open DensePoly in
/-- The level-1 monomial derivative `Dt₁ = 1` over `DensePoly (DenseFrac ℚ) = ℚ(x)[t₁]` (`t₁` primitive). -/
def towerRdeGDt : DensePoly (DenseFrac ℚ) := [CCommRing.one]

open DensePoly in
/-- The generic RDE oracle `cRischDE` solves `Dy = 1` over ℚ(x)(t₁). -/
theorem towerRdeG_solves_Dy_eq_one :
    (match cRischDE towerRdeGDt ([] : DensePoly (DenseFrac ℚ)) [CCommRing.one] [CCommRing.one] [CCommRing.one] with
      | some (ynum, yden) =>
          let Dyn := CPolyEngine.monomialDeriv towerRdeGDt ynum
          let Dyd := CPolyEngine.monomialDeriv towerRdeGDt yden
          let fnum : DensePoly (DenseFrac ℚ) := []
          let fden : DensePoly (DenseFrac ℚ) := [CCommRing.one]
          let gnum : DensePoly (DenseFrac ℚ) := [CCommRing.one]
          let gden : DensePoly (DenseFrac ℚ) := [CCommRing.one]
          let lhs := cadd
            (cmul (cmul gden fden) (csub (cmul Dyn yden) (cmul ynum Dyd)))
            (cmul (cmul (cmul gden fnum) ynum) yden)
          let rhs := cmul (cmul gnum fden) (cmul yden yden)
          cisZero (csub lhs rhs)
      | none => false) = true := by native_decide

open DensePoly in
/-- The generic RDE oracle solves `Dy + y = t₁ + 1` over ℚ(x)(t₁): the primitive-cancellation branch
with nonzero coefficient `f = 1`. -/
theorem towerRdeG_solves_Dy_plus_y_eq_t1_plus_one :
    (match cRischDE towerRdeGDt [CCommRing.one] [CCommRing.one]
        [CCommRing.one, CCommRing.one] [CCommRing.one] with
      | some (ynum, yden) =>
          let Dyn := CPolyEngine.monomialDeriv towerRdeGDt ynum
          let Dyd := CPolyEngine.monomialDeriv towerRdeGDt yden
          let fnum : DensePoly (DenseFrac ℚ) := [CCommRing.one]
          let fden : DensePoly (DenseFrac ℚ) := [CCommRing.one]
          let gnum : DensePoly (DenseFrac ℚ) := [CCommRing.one, CCommRing.one]
          let gden : DensePoly (DenseFrac ℚ) := [CCommRing.one]
          let lhs := cadd
            (cmul (cmul gden fden) (csub (cmul Dyn yden) (cmul ynum Dyd)))
            (cmul (cmul (cmul gden fnum) ynum) yden)
          let rhs := cmul (cmul gnum fden) (cmul yden yden)
          cisZero (csub lhs rhs)
      | none => false) = true := by native_decide

end DeepWiki.SymbolicIntegration
