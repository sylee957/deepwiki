import DeepWiki.SymbolicIntegration.Engine.Tower.RischDEWellFounded

/-! # The tower RDE instance `CRischField (QFunNZ β)`

The `CRischField (QFunNZ β)` instance tying the tower recursion, running `cRischDE`. Solving an RDE at
level `n+1` runs the pipeline at level `n` and recurses into the level-`n` `crischDESolve`, bottoming at
`CRischField ℚ`. -/

open Polynomial Classical

namespace DeepWiki.SymbolicIntegration

open CPoly QFunNZ

section
variable {β : Type*} [CField β] [CDiffField β] [CFieldDomain β] [CFracGcdCoreWf β] [CRischField β]

/-- `CRischField (QFunNZ β)` — the gated, sound RDE over `β(s) = QFunNZ β`, running `cRischDE` over
`CPoly β = β[s]` (`Ds = [1]`) with `[CRischField β]` for the base solve, behind the gate
`cdenomNormalGate`. Bottoms at `CRischField ℚ`. -/
instance instCRischFieldQFunNZ : CRischField (QFunNZ β) where
  crischDESolve f g :=
    if cdenomNormalGate f then
      match CPoly.cRischDE ([CField.one] : CPoly β) f.1.1 f.1.2 g.1.1 g.1.2 with
      | none => none
      | some (ynum, yden) =>
        if h : CPoly.cisZero yden = false then some ⟨(ynum, yden), h⟩ else none
    else none

/-- The gated oracle reduces to the raw solve when the gate passes: if `cdenomNormalGate f = true`
then `crischDESolve f g` is the bare `cRischDE [1]`-then-`cisZero`-guard match. -/
theorem crischDESolveWf_eq_solve_of_normal (f g : QFunNZ β) (hgate : cdenomNormalGate f = true) :
    CRischField.crischDESolve f g
      = (match CPoly.cRischDE ([CField.one] : CPoly β) f.1.1 f.1.2 g.1.1 g.1.2 with
         | none => none
         | some (ynum, yden) =>
           if h : CPoly.cisZero yden = false then some ⟨(ynum, yden), h⟩ else none) := by
  rw [show CRischField.crischDESolve f g
      = (if cdenomNormalGate f then
           match CPoly.cRischDE ([CField.one] : CPoly β) f.1.1 f.1.2 g.1.1 g.1.2 with
           | none => none
           | some (ynum, yden) =>
             if h : CPoly.cisZero yden = false then some ⟨(ynum, yden), h⟩ else none
         else none) from rfl, if_pos hgate]

/-- A successful gated solve passed the gate: if `crischDESolve f g = some y` then
`cdenomNormalGate f = true`. -/
theorem cdenomNormalGateG_of_crischDESolve_isSome (f g y : QFunNZ β)
    (hsolve : CRischField.crischDESolve f g = some y) : cdenomNormalGate f = true := by
  by_cases hgate : cdenomNormalGate f = true
  · exact hgate
  · rw [show CRischField.crischDESolve f g
        = (if cdenomNormalGate f then
             match CPoly.cRischDE ([CField.one] : CPoly β) f.1.1 f.1.2 g.1.1 g.1.2 with
             | none => none
             | some (ynum, yden) =>
               if h : CPoly.cisZero yden = false then some ⟨(ynum, yden), h⟩ else none
           else none) from rfl, if_neg hgate] at hsolve
    exact absurd hsolve (by simp)

end

/-! ## Validation: the tower RDE computes over `QFunNZ ℚ` -/

open CPoly in
/-- The level-1 monomial derivative `Dt₁ = 1` over `CPoly (QFunNZ ℚ) = ℚ(x)[t₁]` (`t₁` primitive). -/
def towerRdeGDt : CPoly (QFunNZ ℚ) := [CField.one]

open CPoly in
/-- The generic RDE oracle `cRischDE` solves `Dy = 1` over ℚ(x)(t₁). -/
theorem towerRdeG_solves_Dy_eq_one :
    (match cRischDE towerRdeGDt ([] : CPoly (QFunNZ ℚ)) [CField.one] [CField.one] [CField.one] with
      | some (ynum, yden) =>
          let Dyn := cmonomialDeriv towerRdeGDt ynum
          let Dyd := cmonomialDeriv towerRdeGDt yden
          let fnum : CPoly (QFunNZ ℚ) := []
          let fden : CPoly (QFunNZ ℚ) := [CField.one]
          let gnum : CPoly (QFunNZ ℚ) := [CField.one]
          let gden : CPoly (QFunNZ ℚ) := [CField.one]
          let lhs := cadd
            (cmul (cmul gden fden) (csub (cmul Dyn yden) (cmul ynum Dyd)))
            (cmul (cmul (cmul gden fnum) ynum) yden)
          let rhs := cmul (cmul gnum fden) (cmul yden yden)
          cisZero (csub lhs rhs)
      | none => false) = true := by native_decide

open CPoly in
/-- The generic RDE oracle solves `Dy + y = t₁ + 1` over ℚ(x)(t₁): the primitive-cancellation branch
with nonzero coefficient `f = 1`. -/
theorem towerRdeG_solves_Dy_plus_y_eq_t1_plus_one :
    (match cRischDE towerRdeGDt [CField.one] [CField.one]
        [CField.one, CField.one] [CField.one] with
      | some (ynum, yden) =>
          let Dyn := cmonomialDeriv towerRdeGDt ynum
          let Dyd := cmonomialDeriv towerRdeGDt yden
          let fnum : CPoly (QFunNZ ℚ) := [CField.one]
          let fden : CPoly (QFunNZ ℚ) := [CField.one]
          let gnum : CPoly (QFunNZ ℚ) := [CField.one, CField.one]
          let gden : CPoly (QFunNZ ℚ) := [CField.one]
          let lhs := cadd
            (cmul (cmul gden fden) (csub (cmul Dyn yden) (cmul ynum Dyd)))
            (cmul (cmul (cmul gden fnum) ynum) yden)
          let rhs := cmul (cmul gnum fden) (cmul yden yden)
          cisZero (csub lhs rhs)
      | none => false) = true := by native_decide

end DeepWiki.SymbolicIntegration
