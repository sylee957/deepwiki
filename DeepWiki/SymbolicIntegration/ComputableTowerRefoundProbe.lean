import DeepWiki.SymbolicIntegration.ComputableTowerRischDE

/-! # Re-founding feasibility probe: the generic engine STANDALONE at `α = QFunNZG ℚ`
The generic engine `cRischDEG`/`cIntegrateG`/`cIntegrateGFull` (`ComputableTowerRischDE`,
`ComputableTowerIntegrate`) is currently run at `α = QFunNZ` by the catalog
(`alg_6_rischDE := cRischDEG (α := QFunNZ)`), which pulls in the **QFunNZ-specific** instances
(`CField/CFieldSpec/CDiffField QFunNZ`, `CFracGcdCore QFunNZ := cgcdFF`, `CRischField QFunNZ`),
tying the engine to the hand-built QFunNZ engine.

This file is the **feasibility gate** for *re-founding* the engine STANDALONE on the **generic**
ℚ(x) = `QFunNZG ℚ = Frac(ℚ[x])` carrier, whose every instance recurses to ℚ with NO QFunNZ-specific
piece: `CField (QFunNZG ℚ)` (computable, `instCFieldQFunNZG` over `CFieldDomain ℚ`),
`CFieldSpec (QFunNZG ℚ)` (`instCFieldSpecQFunNZG`), `CDiffField (QFunNZG ℚ)` (`d/dx`),
`CFieldDomain (QFunNZG ℚ)`, `CFracGcdCore (QFunNZG ℚ)` (the recursive `instCFracGcdCoreQFunNZG`
bottoming at `CFracGcdCore ℚ`), and `CRischField (QFunNZG ℚ)` (the recursive `instCRischFieldQFunNZG`
bottoming at `CRischField ℚ`).

We call the generic engine **directly at `α = QFunNZG ℚ`** — `cRischDEG (α := QFunNZG ℚ)` and
`cIntegrateGFull (α := QFunNZG ℚ)` over `CPolyG (QFunNZG ℚ) = ℚ(x)[t₁]` (the primitive monomial
`t₁`, `Dt₁ = [1]`) — and certify the result by `native_decide`. If every instance resolves and the
engine reduces, **re-founding onto `QFunNZG ℚ` is VIABLE** (the catalog can switch
`α := QFunNZ → QFunNZG ℚ`, dropping the QFunNZ engine entirely). The inputs are built one level down
from the level-2 `towerInt*` examples: a `QFunNZG ℚ` element is a fraction over `CPolyG ℚ = List ℚ`,
so the engine inputs `CPolyG (QFunNZG ℚ)` are lists of such fractions (`CField.zero`/`CField.one`
scalars suffice for `Dy = 1` and `∫ t₁`). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

/-! ### The level-1 monomial `t₁` over the generic ℚ(x) = `QFunNZG ℚ` (primitive, `Dt₁ = 1`)

The engine runs over `CPolyG (QFunNZG ℚ) = (ℚ(x))[t₁]`. The monomial `t₁` is primitive — its
derivative `Dt₁ = [1]` (the constant `1 ∈ ℚ(x)`), exactly the choice the recursive `CDiffField`
tower uses (`towerDerivQFunNZG [1]`). All scalars here are `0`/`1 ∈ ℚ(x)` (`CField.zero`/`CField.one`
at `QFunNZG ℚ`), so the inputs need no genuine ℚ(x)-fraction — but the carrier, instances and
derivation are the *generic* `QFunNZG ℚ` ones, NOT QFunNZ. -/

/-- The primitive monomial derivative `Dt₁ = 1` over `CPolyG (QFunNZG ℚ) = ℚ(x)[t₁]`. -/
def refoundDt : CPolyG (QFunNZG ℚ) := [CField.one]

/-- The level-1 polynomial `t₁ + 1 ∈ ℚ(x)[t₁]` (low→high: `[1, 1]`), the RHS for the non-trivial-`f`
probe `Dy + y = t₁ + 1`. -/
def refoundGPlusOne : CPolyG (QFunNZG ℚ) := [CField.one, CField.one]

/-! ### ★ TASK 1 — the FEASIBILITY GATE: `cRischDEG (α := QFunNZG ℚ)` computes (`native_decide`)

The decisive milestone. We call the GENERIC §6 Risch-DE solver `cRischDEG` **directly at
`α = QFunNZG ℚ`** (the generic ℚ(x), NOT QFunNZ) over `ℚ(x)[t₁]`, solving the RDE `Dy + f·y = g`.
For this to even typecheck-and-reduce, ALL of `CField`/`CFieldSpec`/`CDiffField`/`CFieldDomain`/
`CFracGcdCore`/`CRischField` must resolve at `QFunNZG ℚ` through the *recursive* instances
bottoming at ℚ — the QFunNZ-specific ones (`cgcdFF`-keyed `CFracGcdCore QFunNZ`, `cRischDEBase`-keyed
`CRischField QFunNZ`) are NOT in play. The result `(ynum, yden)` is read back as the solution
`y = ynum/yden ∈ ℚ(x)(t₁)` and certified to solve the RDE by the cleared identity over `ℚ(x)[t₁]`. -/

/-- **★ FEASIBILITY GATE (a): `cRischDEG (α := QFunNZG ℚ)` solves `Dy = 1` over ℚ(x)(t₁)**
(`native_decide`). The generic engine, run STANDALONE on the generic ℚ(x) = `QFunNZG ℚ` carrier
(every instance recursing to ℚ, no QFunNZ piece), reduces `Dy = 1` (`f = 0`, `g = 1`) over the
primitive monomial `t₁` to `y = t₁`. We pin that the solver returns `some (ynum, yden)` with
`yden ≠ 0`, and the returned `y = ynum/yden` solves `Dy = 1` — checked, cleared of denominators over
ℚ(x)[t₁], as `(D(ynum)·yden − ynum·D(yden))·1 = 1·yden²` via `cisZeroG` of the difference (`D = Dt₁`
the level-1 monomial derivation). **This is the verdict: the engine COMPUTES at `α = QFunNZG ℚ`, so
re-founding is VIABLE.** -/
theorem refound_rischDEG_solves_Dy_eq_one :
    (match CPolyG.cRischDEG refoundDt 60 ([] : CPolyG (QFunNZG ℚ)) [CField.one]
        [CField.one] [CField.one] with
      | some (ynum, yden) =>
          -- `yden ≠ 0` and `D(y) = 1`, cleared: `(D(ynum)·yden − ynum·D(yden)) = yden²`.
          let Dynum := CPolyG.cmonomialDeriv refoundDt ynum
          let Dyden := CPolyG.cmonomialDeriv refoundDt yden
          let gprimeNum := CPolyG.csubG (CPolyG.cmulG Dynum yden) (CPolyG.cmulG ynum Dyden)
          let yden2 := CPolyG.cmulG yden yden
          (!CPolyG.cisZeroG yden) && CPolyG.cisZeroG (CPolyG.csubG gprimeNum yden2)
      | none => false) = true := by native_decide

/-- **★ FEASIBILITY GATE (b): `cRischDEG (α := QFunNZG ℚ)` solves `Dy + y = t₁ + 1`** with a
NON-TRIVIAL `f = 1` (`native_decide`). Over `ℚ(x)[t₁]` (primitive `t₁`), the generic engine solves
`Dy + 1·y = t₁ + 1` to `y = t₁`, exercising the §6.6 primitive-cancellation degree-recursion (which
recurses into `CRischField.crischDESolve` over ℚ(x) — the *generic* `QFunNZG ℚ` oracle, bottoming at
the ℚ constant solve), not just the integration branch. The returned `y = ynum/yden` is certified to
solve `Dy + y = t₁ + 1`, cleared of denominators over ℚ(x)[t₁]:
`(D(ynum)·yden − ynum·D(yden) + ynum·yden)·1 = (t₁+1)·yden²`. Confirms the *cancellation* path of the
generic engine resolves and reduces at `α = QFunNZG ℚ`. -/
theorem refound_rischDEG_solves_Dy_plus_y_eq_t1_plus_one :
    (match CPolyG.cRischDEG refoundDt 60 [CField.one] [CField.one]
        refoundGPlusOne [CField.one] with
      | some (ynum, yden) =>
          let Dynum := CPolyG.cmonomialDeriv refoundDt ynum
          let Dyden := CPolyG.cmonomialDeriv refoundDt yden
          let gprimeNum := CPolyG.csubG (CPolyG.cmulG Dynum yden) (CPolyG.cmulG ynum Dyden)
          let yden2 := CPolyG.cmulG yden yden
          -- `D(y) + y` numerator over `yden²`: `gprimeNum·1 + ynum·yden`  (since `f = 1/1`).
          let lhsNum := CPolyG.caddG gprimeNum (CPolyG.cmulG ynum yden)
          let rhsNum := CPolyG.cmulG refoundGPlusOne yden2
          (!CPolyG.cisZeroG yden) && CPolyG.cisZeroG (CPolyG.csubG lhsNum rhsNum)
      | none => false) = true := by native_decide

/-! ### ★ TASK 1 — the integration driver `cIntegrateGFull (α := QFunNZG ℚ)` computes (`native_decide`)

The companion gate on the integration side. We run the full poly/special integration driver
`cIntegrateGFull` **directly at `α = QFunNZG ℚ`** over `ℚ(x)[t₁]`, integrating `f = t₁` (a pure
polynomial part). The driver's polynomial-part step solves `Dqₚ = t₁` by the RDE oracle (recursing
into the generic ℚ(x) `crischDESolve`), giving `qₚ = (1/2)t₁²`. The reduced driver `cIntegrateG`
returns `none` on this (nonzero polynomial part), so this exercises the part the RDE oracle unlocks —
all at `α = QFunNZG ℚ`, with the `CRischField (QFunNZG ℚ)` instance bottoming at ℚ. -/

/-- The level-1 integrand `f = t₁` over `CPolyG (QFunNZG ℚ) = ℚ(x)[t₁]` (numerator `t₁ = [0, 1]`,
denominator `1`), a pure polynomial part on which the reduced `cIntegrateG` returns `none`. -/
def refoundIntA : CPolyG (QFunNZG ℚ) := [CField.zero, CField.one]

/-- The level-1 integrand denominator `d = 1` over `CPolyG (QFunNZG ℚ)`. -/
def refoundIntD : CPolyG (QFunNZG ℚ) := [CField.one]

/-- The level-1 residue candidate set (`f = t₁` has no logarithmic part). -/
def refoundIntCands : List (QFunNZG ℚ) := [CField.zero, CField.one]

/-- **The reduced driver `cIntegrateG (α := QFunNZG ℚ)` returns `none` on `f = t₁`** (`native_decide`):
its polynomial part `fₚ = t₁` is nonzero, so the conservative reduced driver cannot dispose of it —
confirming the gap the full driver closes, here at `α = QFunNZG ℚ`. -/
theorem refound_integrateG_reduced_none :
    (CPolyG.cIntegrateG refoundDt 30 refoundIntA refoundIntD refoundIntCands).isNone = true := by
  native_decide

/-- **★ FEASIBILITY GATE (c): `cIntegrateGFull (α := QFunNZG ℚ)` lands `∫ t₁ = (1/2)t₁²`, `D(∫f) = f`**
(`native_decide`). On `f = t₁` over the generic ℚ(x)[t₁] (`= CPolyG (QFunNZG ℚ)`, `Dt₁ = 1`, primitive)
— a pure polynomial part the reduced `cIntegrateG` returns `none` on — the full driver
`cIntegrateGFull` (canonical split + RDE-oracle polynomial-part solve `Dqₚ = t₁` + recombination)
returns `some res`, and `res` satisfies the antiderivative identity `D(res) = f` (`checkIdentityG`,
cleared of denominators over ℚ(x)[t₁]). The whole driver — including the `CRischField (QFunNZG ℚ)`
recursion bottoming at ℚ — *computes* over the generic ℚ(x) carrier. **Confirms the integration side
of the engine runs STANDALONE at `α = QFunNZG ℚ`.** -/
theorem refound_integrateGFull_landsPolynomialPart :
    (match CPolyG.cIntegrateGFull refoundDt 30 refoundIntA refoundIntD refoundIntCands with
      | some res => CPolyG.checkIdentityG refoundDt res refoundIntA refoundIntD
      | none => false) = true := by native_decide

/-! ### Axiom audit (the probe rests only on the standard kernel axioms + native compilation) -/

#print axioms refound_rischDEG_solves_Dy_eq_one
#print axioms refound_rischDEG_solves_Dy_plus_y_eq_t1_plus_one
#print axioms refound_integrateGFull_landsPolynomialPart

end DeepWiki.SymbolicIntegration
