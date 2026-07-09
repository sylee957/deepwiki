import DeepWiki.SymbolicIntegration.Engine.TranscendentalOverAlgebraic
import DeepWiki.SymbolicIntegration.Engine.UnifiedFuelFree
import DeepWiki.SymbolicIntegration.Engine.Hyperexp.Special

/-! # Transcendental integrals over an algebraic base (the mixed tower)

Equips the radical field `RadX3 = ℚ(x)[√(x³+1)]` with `CFracGcdCoreWf` and `CRischField`, then runs the
full tower integrator `cIntegrateGFullWf` at `α = RadX3`. The validation examples cover polynomial parts,
the normal-part route, a nonconstant algebraic-coefficient boundary, a multi-level RDE descent, and
hyperexponential Laurent integrals descending through `crischDESolve` over `RadX3`. -/

namespace DeepWiki.SymbolicIntegration

open CPolyG

/-! ### Base typeclasses for the radical field `RadX3` -/

/-- `CFracGcdCoreWf RadX3`: the fuel-free raw fraction-free gcd over `RadX3[t]` is `(cgcdWf p q).1`. -/
instance instCFracGcdCoreWfRadX3 : CFracGcdCoreWf RadX3 where
  cgcdFFRawCoreWf p q := (CPolyG.cgcdWf p q).1

/-! ### Shared integrand data over `RadX3[t]` -/

/-- The primitive monomial derivative `Dt = 1` over `CPolyG RadX3` (`t` primitive, `t' = 1`). -/
def mixedDt : CPolyG RadX3 := [CField.one]

/-- The integrand denominator `d = 1` over `CPolyG RadX3` (for the pure polynomial parts). -/
def mixedD : CPolyG RadX3 := [CField.one]

/-- The residue candidate set over `RadX3` (`0`, `1` — the log integrand `1/t` has residue `1`). -/
def mixedCands : List RadX3 := [CField.zero, CField.one]

/-! ### `∫ t dt = t²/2` over `RadX3[t]` -/

/-- The integrand `f = t` over `CPolyG RadX3` (`[0, 1]`): a pure polynomial part. -/
def mixedTa : CPolyG RadX3 := [CField.zero, CField.one]

/-- `∫ t dt = t²/2` over `RadX3[t]`, validated `D(∫f) = f` via `checkIdentityG`. -/
theorem mixedT_integral_eq :
    (match CPolyG.cIntegrateGFullWf mixedDt mixedTa mixedD mixedCands with
      | some res => CPolyG.checkIdentityG mixedDt res mixedTa mixedD
      | none => false) = true := by native_decide

/-! ### `∫ t² dt = t³/3` and `∫ (2t+1) dt = t²+t` over `RadX3[t]` -/

/-- The integrand `f = t²` over `CPolyG RadX3` (`[0,0,1]`). -/
def mixedT2a : CPolyG RadX3 := [CField.zero, CField.zero, CField.one]

/-- `∫ t² dt = t³/3` over `RadX3[t]`, validated `D(∫f) = f`. -/
theorem mixedT2_integral_eq :
    (match CPolyG.cIntegrateGFullWf mixedDt mixedT2a mixedD mixedCands with
      | some res => CPolyG.checkIdentityG mixedDt res mixedT2a mixedD
      | none => false) = true := by native_decide

/-- The integrand `f = 2t + 1` over `CPolyG RadX3` (`[1,2]`). -/
def mixedLina : CPolyG RadX3 := [CField.one, CField.add CField.one CField.one]

/-- `∫ (2t+1) dt = t²+t` over `RadX3[t]`, validated `D(∫f) = f`. -/
theorem mixedLin_integral_eq :
    (match CPolyG.cIntegrateGFullWf mixedDt mixedLina mixedD mixedCands with
      | some res => CPolyG.checkIdentityG mixedDt res mixedLina mixedD
      | none => false) = true := by native_decide

/-! ### `∫ dt/t = log t` over `RadX3[t]` — the normal-part / Rothstein–Trager log route -/

/-- The integrand `f = 1/t` over `RadX3[t]` as `a/d` with `a = 1`, `d = t` (a pure normal part). -/
def mixedRecipNum : CPolyG RadX3 := [CField.one]

/-- The denominator `d = t = [0,1]` over `CPolyG RadX3`. -/
def mixedRecipDen : CPolyG RadX3 := [CField.zero, CField.one]

/-- `∫ dt/t = log t` over `RadX3[t]`, validated `D(log t) = 1/t` via the residue-log route. -/
theorem mixedRecip_integral_eq :
    (match CPolyG.cIntegrateGFullWf mixedDt mixedRecipNum mixedRecipDen mixedCands with
      | some res => CPolyG.checkIdentityG mixedDt res mixedRecipNum mixedRecipDen
      | none => false) = true := by native_decide

/-! ### The algebraic-coefficient boundary: `∫ y dt` does not validate

`y = √(x³+1)` is not a `D`-constant (`D(y) = ℓ·y ≠ 0`), so the would-be antiderivative `y·t` is not a
genuine antiderivative and `checkIdentityG` is false. -/

/-- The integrand `f = y = √(x³+1)` over `CPolyG RadX3` (`[radX3Gen]`; `y` is not a `D`-constant). -/
def mixedYa : CPolyG RadX3 := [radX3Gen]

/-- `∫ y dt` does not satisfy `D(∫f) = f`: the driver returns `some (y·t)` but `checkIdentityG` is
false, since `y` is not a `D`-constant. -/
theorem mixedY_not_validated :
    (match CPolyG.cIntegrateGFullWf mixedDt mixedYa mixedD mixedCands with
      | some res => CPolyG.checkIdentityG mixedDt res mixedYa mixedD
      | none => false) = false := by native_decide

/-! ### A multi-level RDE descent through the algebraic solver

An RDE over `RadX3[t]` with nonzero coefficient `f = 1` routes through the primitive-cancellation branch,
recursing into `crischDESolve` over `RadX3`, which decouples to ℚ(x).  Solves `Dy + 1·y = t + 1`
(solution `y = t`). -/

/-- The RDE coefficient `f = 1 ∈ RadX3[t]` (nonzero), forcing the primitive-cancellation branch. -/
def mixedRdeF : CPolyG RadX3 := [CField.one]

/-- The RDE coefficient denominator `fden = 1 ∈ RadX3[t]`. -/
def mixedRdeFden : CPolyG RadX3 := [CField.one]

/-- The RDE right-hand side `g = t + 1 ∈ RadX3[t]` for `Dy + 1·y = t + 1`. -/
def mixedRdeG : CPolyG RadX3 := [CField.one, CField.one]

/-- The RDE right-hand side denominator `gden = 1 ∈ RadX3[t]`. -/
def mixedRdeGden : CPolyG RadX3 := [CField.one]

/-- The RDE `Dy + 1·y = t + 1` over `RadX3[t]` is solved (`cRischDEG` returns `some`). -/
theorem mixedRde_radx3_isSome :
    (CPolyG.cRischDEG ([CField.one] : CPolyG RadX3)
      mixedRdeF mixedRdeFden mixedRdeG mixedRdeGden).isSome = true := by native_decide

/-- A multi-level RDE descent: `Dy + 1·y = t + 1` solved over `RadX3[t]` with solution `y = t`, the
RDE identity checked via `cisZeroG`; the solve recurses into `crischDESolve` over `RadX3`. -/
theorem mixedRde_radx3_descends :
    (match CPolyG.cRischDEG ([CField.one] : CPolyG RadX3)
        mixedRdeF mixedRdeFden mixedRdeG mixedRdeGden with
      | some (ynum, yden) =>
          CPolyG.cisZeroG (CPolyG.csubG
            (CPolyG.caddG (CPolyG.cmonomialDeriv ([CField.one] : CPolyG RadX3) ynum)
              (CPolyG.cmulG mixedRdeF ynum))
            (CPolyG.cmulG mixedRdeG yden))
      | none => false) = true := by native_decide

/-! ### A hyperexponential Laurent integral whose special-part step descends through the algebraic solver

For a hyperexponential `t` (`Dt = η·t`), the Laurent integrator `cIntegrateHyperexpLaurentG` integrates
`∫ ∑ⱼ aⱼ tʲ` term by term, each `∫ aⱼ tʲ` solved as `crischDESolve (j·η) aⱼ`.  At `α = RadX3` the
negative-index term calls `crischDESolve` with a nonzero scalar, descending to ℚ(x).  Integrates
`t = exp` (`η = 1`). -/

/-- The hyperexponential monomial derivative `Dt = η·t = [0, 1]` over `RadX3[t]` (`t = exp`, `η = 1`). -/
def mixedHyperexpDt : CPolyG RadX3 := [CField.zero, CField.one]

/-- `η = Dt/t = 1` over `RadX3`: `cExpEtaG` reads `η = 1` off `Dt = [0, 1]`. -/
theorem mixedHyperexp_eta_eq_one :
    CField.isZero (CField.sub (cExpEtaG mixedHyperexpDt) (CField.one : RadX3)) = true := by
  native_decide

/-- The per-term coefficient `(−1)·η = −1 ∈ RadX3` for the `t⁻¹` Laurent term (`cLaurentShiftG η (−1)`). -/
def mixedLaurentShiftNeg1 : RadX3 := CPolyG.cLaurentShiftG (CField.one : RadX3) (-1)

/-- The per-term coefficient `(−1)·η` is a nonzero scalar over `RadX3`:
`RadExt.isScalar` is `true` and `CField.isZero` is `false`. -/
theorem mixedLaurentShiftNeg1_nonzero_scalar :
    RadExt.isScalar mixedLaurentShiftNeg1 = true ∧
    CField.isZero mixedLaurentShiftNeg1 = false := by
  constructor <;> native_decide

/-- The `∫ t⁻¹` term's base RDE `crischDESolve ((−1)·η) (1 : RadX3)` returns `some`, descending
through the algebraic solver. -/
theorem mixedLaurentTerm_descends :
    (CRischField.crischDESolve mixedLaurentShiftNeg1 (CField.one : RadX3)).isSome = true := by
  native_decide

/-- `∫ t⁻¹ = −t⁻¹` over `RadX3[t]` via the Laurent integrator, the special-part step descending
through the algebraic solver, validated `D(∫f) = f`. -/
theorem mixedHyperexpRecip_integral_descends :
    (match CPolyG.cIntegrateHyperexpLaurentG (CField.one : RadX3) [] [CField.one] with
      | some (num, den) =>
          CPolyG.checkIdentityG mixedHyperexpDt ⟨(num, den), []⟩ [CField.one] [CField.zero, CField.one]
      | none => false) = true := by native_decide

/-- `∫ (t + t⁻¹) = t − t⁻¹` over `RadX3[t]` via the Laurent integrator (polynomial part plus a
descending special part), validated `D(∫f) = f`. -/
theorem mixedHyperexpPolySpec_integral_descends :
    (match CPolyG.cIntegrateHyperexpLaurentG (CField.one : RadX3) [CField.zero, CField.one]
        [CField.one] with
      | some (num, den) =>
          CPolyG.checkIdentityG mixedHyperexpDt ⟨(num, den), []⟩
            [CField.one, CField.zero, CField.one] [CField.zero, CField.one]
      | none => false) = true := by native_decide

/-! ### The full `cIntegrateHyperexpG` top entry over `RadX3` -/

/-- `cIntegrateHyperexpG`'s top entry validates over `RadX3`: on `f = (t²+1)/t = t + t⁻¹` it returns
`some res` with `checkIdentityG` confirming `D(res) = f`. -/
theorem mixedHyperexpG_topEntry_validates :
    (match CPolyG.cIntegrateHyperexpG mixedHyperexpDt [CField.one, CField.zero, CField.one]
        [CField.zero, CField.one] [CField.zero, CField.one] with
      | some res =>
          CPolyG.checkIdentityG mixedHyperexpDt res [CField.one, CField.zero, CField.one]
            [CField.zero, CField.one]
      | none => false) = true := by native_decide

/-! ### Axiom audit -/

#print axioms mixedT_integral_eq
#print axioms mixedT2_integral_eq
#print axioms mixedLin_integral_eq
#print axioms mixedRecip_integral_eq
#print axioms mixedY_not_validated
#print axioms mixedRde_radx3_descends
#print axioms mixedHyperexpRecip_integral_descends
#print axioms mixedHyperexpPolySpec_integral_descends
#print axioms mixedHyperexpG_topEntry_validates

end DeepWiki.SymbolicIntegration
