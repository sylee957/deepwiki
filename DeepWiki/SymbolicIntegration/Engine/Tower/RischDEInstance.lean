import DeepWiki.SymbolicIntegration.Engine.Tower.RischDEWellFounded

/-! # The tower RDE instance `CRischField (QFunNZG β)`

The `CRischField (QFunNZG β)` instance tying the tower recursion, running `cRischDEG`. Solving an RDE at
level `n+1` runs the pipeline at level `n` and recurses into the level-`n` `crischDESolve`, bottoming at
`CRischField ℚ`. -/

open Polynomial Classical

namespace DeepWiki.SymbolicIntegration

open CPolyG QFunNZG

section
variable {β : Type*} [CField β] [CDiffField β] [CFieldDomain β] [CFracGcdCoreWf β] [CRischField β]

/-- `CRischField (QFunNZG β)` — the gated, sound RDE over `β(s) = QFunNZG β`, running `cRischDEG` over
`CPolyG β = β[s]` (`Ds = [1]`) with `[CRischField β]` for the base solve, behind the gate
`cdenomNormalGateG`. Bottoms at `CRischField ℚ`. -/
instance instCRischFieldQFunNZG : CRischField (QFunNZG β) where
  crischDESolve f g :=
    if cdenomNormalGateG f then
      match CPolyG.cRischDEG ([CField.one] : CPolyG β) f.1.1 f.1.2 g.1.1 g.1.2 with
      | none => none
      | some (ynum, yden) =>
        if h : CPolyG.cisZeroG yden = false then some ⟨(ynum, yden), h⟩ else none
    else none

/-- The gated oracle reduces to the raw solve when the gate passes: if `cdenomNormalGateG f = true`
then `crischDESolve f g` is the bare `cRischDEG [1]`-then-`cisZeroG`-guard match. -/
theorem crischDESolveWf_eq_solve_of_normal (f g : QFunNZG β) (hgate : cdenomNormalGateG f = true) :
    CRischField.crischDESolve f g
      = (match CPolyG.cRischDEG ([CField.one] : CPolyG β) f.1.1 f.1.2 g.1.1 g.1.2 with
         | none => none
         | some (ynum, yden) =>
           if h : CPolyG.cisZeroG yden = false then some ⟨(ynum, yden), h⟩ else none) := by
  rw [show CRischField.crischDESolve f g
      = (if cdenomNormalGateG f then
           match CPolyG.cRischDEG ([CField.one] : CPolyG β) f.1.1 f.1.2 g.1.1 g.1.2 with
           | none => none
           | some (ynum, yden) =>
             if h : CPolyG.cisZeroG yden = false then some ⟨(ynum, yden), h⟩ else none
         else none) from rfl, if_pos hgate]

/-- A successful gated solve passed the gate: if `crischDESolve f g = some y` then
`cdenomNormalGateG f = true`. -/
theorem cdenomNormalGateG_of_crischDESolve_isSome (f g y : QFunNZG β)
    (hsolve : CRischField.crischDESolve f g = some y) : cdenomNormalGateG f = true := by
  by_cases hgate : cdenomNormalGateG f = true
  · exact hgate
  · rw [show CRischField.crischDESolve f g
        = (if cdenomNormalGateG f then
             match CPolyG.cRischDEG ([CField.one] : CPolyG β) f.1.1 f.1.2 g.1.1 g.1.2 with
             | none => none
             | some (ynum, yden) =>
               if h : CPolyG.cisZeroG yden = false then some ⟨(ynum, yden), h⟩ else none
           else none) from rfl, if_neg hgate] at hsolve
    exact absurd hsolve (by simp)

end

/-! ## Validation: the tower RDE computes over `QFunNZG ℚ` -/

open CPolyG in
/-- The level-1 monomial derivative `Dt₁ = 1` over `CPolyG (QFunNZG ℚ) = ℚ(x)[t₁]` (`t₁` primitive). -/
def towerRdeGDt : CPolyG (QFunNZG ℚ) := [CField.one]

open CPolyG in
/-- The generic RDE oracle `cRischDEG` solves `Dy = 1` over ℚ(x)(t₁). -/
theorem towerRdeG_solves_Dy_eq_one :
    (match cRischDEG towerRdeGDt ([] : CPolyG (QFunNZG ℚ)) [CField.one] [CField.one] [CField.one] with
      | some (ynum, yden) =>
          let Dyn := cmonomialDeriv towerRdeGDt ynum
          let Dyd := cmonomialDeriv towerRdeGDt yden
          let fnum : CPolyG (QFunNZG ℚ) := []
          let fden : CPolyG (QFunNZG ℚ) := [CField.one]
          let gnum : CPolyG (QFunNZG ℚ) := [CField.one]
          let gden : CPolyG (QFunNZG ℚ) := [CField.one]
          let lhs := caddG
            (cmulG (cmulG gden fden) (csubG (cmulG Dyn yden) (cmulG ynum Dyd)))
            (cmulG (cmulG (cmulG gden fnum) ynum) yden)
          let rhs := cmulG (cmulG gnum fden) (cmulG yden yden)
          cisZeroG (csubG lhs rhs)
      | none => false) = true := by native_decide

open CPolyG in
/-- The generic RDE oracle solves `Dy + y = t₁ + 1` over ℚ(x)(t₁): the primitive-cancellation branch
with nonzero coefficient `f = 1`. -/
theorem towerRdeG_solves_Dy_plus_y_eq_t1_plus_one :
    (match cRischDEG towerRdeGDt [CField.one] [CField.one]
        [CField.one, CField.one] [CField.one] with
      | some (ynum, yden) =>
          let Dyn := cmonomialDeriv towerRdeGDt ynum
          let Dyd := cmonomialDeriv towerRdeGDt yden
          let fnum : CPolyG (QFunNZG ℚ) := [CField.one]
          let fden : CPolyG (QFunNZG ℚ) := [CField.one]
          let gnum : CPolyG (QFunNZG ℚ) := [CField.one, CField.one]
          let gden : CPolyG (QFunNZG ℚ) := [CField.one]
          let lhs := caddG
            (cmulG (cmulG gden fden) (csubG (cmulG Dyn yden) (cmulG ynum Dyd)))
            (cmulG (cmulG (cmulG gden fnum) ynum) yden)
          let rhs := cmulG (cmulG gnum fden) (cmulG yden yden)
          cisZeroG (csubG lhs rhs)
      | none => false) = true := by native_decide

end DeepWiki.SymbolicIntegration
