import DeepWiki.SymbolicIntegration.Engine.TranscendentalOverAlgebraic
import DeepWiki.SymbolicIntegration.Engine.Hyperexp.Special

/-! # Transcendental integrals over an algebraic base (the mixed tower)

Equips the radical field `RadX3 = ℚ(x)[√(x³+1)]` with the capabilities used by
multi-level Risch-DE descent and hyperexponential Laurent integration. -/

namespace DeepWiki.SymbolicIntegration

open DensePoly

/-! ### Base typeclasses for the radical field `RadX3` -/

/-- `CFracGcdCoreWf RadX3` selects the fuel-free extended-gcd component over `RadX3[t]`. -/
instance instCFracGcdCoreWfRadX3 : CFracGcdCoreWf RadX3 where
  cgcdFFRawCoreWf p q := (CPolyEuclidean.gcdExt p q).1

/-! ### A multi-level RDE descent through the algebraic solver

An RDE over `RadX3[t]` with nonzero coefficient `f = 1` routes through the primitive-cancellation branch,
recursing into `crischDESolve` over `RadX3`, which decouples to ℚ(x).  Solves `Dy + 1·y = t + 1`
(solution `y = t`). -/

/-- The RDE coefficient `f = 1 ∈ RadX3[t]` (nonzero), forcing the primitive-cancellation branch. -/
def mixedRdeF : DensePoly RadX3 := [CCommRing.one]

/-- The RDE coefficient denominator `fden = 1 ∈ RadX3[t]`. -/
def mixedRdeFden : DensePoly RadX3 := [CCommRing.one]

/-- The RDE right-hand side `g = t + 1 ∈ RadX3[t]` for `Dy + 1·y = t + 1`. -/
def mixedRde : DensePoly RadX3 := [CCommRing.one, CCommRing.one]

/-- The RDE right-hand side denominator `gden = 1 ∈ RadX3[t]`. -/
def mixedRdeGden : DensePoly RadX3 := [CCommRing.one]

/-- The RDE `Dy + 1·y = t + 1` over `RadX3[t]` is solved (`cRischDE` returns `some`). -/
theorem mixedRde_radx3_isSome :
    (DensePoly.cRischDE ([CCommRing.one] : DensePoly RadX3)
      mixedRdeF mixedRdeFden mixedRde mixedRdeGden).isSome = true := by native_decide

/-- A multi-level RDE descent: `Dy + 1·y = t + 1` solved over `RadX3[t]` with solution `y = t`, the
RDE identity checked via `cisZero`; the solve recurses into `crischDESolve` over `RadX3`. -/
theorem mixedRde_radx3_descends :
    (match DensePoly.cRischDE ([CCommRing.one] : DensePoly RadX3)
        mixedRdeF mixedRdeFden mixedRde mixedRdeGden with
      | some (ynum, yden) =>
          DensePoly.cisZero (DensePoly.csub
            (DensePoly.cadd (CPolyEngine.monomialDeriv ([CCommRing.one] : DensePoly RadX3) ynum)
              (DensePoly.cmul mixedRdeF ynum))
            (DensePoly.cmul mixedRde yden))
      | none => false) = true := by native_decide

/-! ### A hyperexponential Laurent integral whose special-part step descends through the algebraic solver

For a hyperexponential `t` (`Dt = η·t`), the Laurent integrator `cIntegrateHyperexpLaurent` integrates
`∫ ∑ⱼ aⱼ tʲ` term by term, each `∫ aⱼ tʲ` solved as `crischDESolve (j·η) aⱼ`.  At `α = RadX3` the
negative-index term calls `crischDESolve` with a nonzero scalar, descending to ℚ(x).  Integrates
`t = exp` (`η = 1`). -/

/-- The hyperexponential monomial derivative `Dt = η·t = [0, 1]` over `RadX3[t]` (`t = exp`, `η = 1`). -/
def mixedHyperexpDt : DensePoly RadX3 := [CCommRing.zero, CCommRing.one]

/-- `η = Dt/t = 1` over `RadX3`: `cExpEta` reads `η = 1` off `Dt = [0, 1]`. -/
theorem mixedHyperexp_eta_eq_one :
    CCommRing.isZero (CField.sub (cExpEta mixedHyperexpDt) (CCommRing.one : RadX3)) = true := by
  native_decide

/-- The per-term coefficient `(−1)·η = −1 ∈ RadX3` for the `t⁻¹` Laurent term (`cLaurentShift η (−1)`). -/
def mixedLaurentShiftNeg1 : RadX3 := DensePoly.cLaurentShift (CCommRing.one : RadX3) (-1)

/-- The per-term coefficient `(−1)·η` is a nonzero scalar over `RadX3`:
`RadExt.isScalar` is `true` and `CCommRing.isZero` is `false`. -/
theorem mixedLaurentShiftNeg1_nonzero_scalar :
    RadExt.isScalar mixedLaurentShiftNeg1 = true ∧
    CCommRing.isZero mixedLaurentShiftNeg1 = false := by
  constructor <;> native_decide

/-- The `∫ t⁻¹` term's base RDE `crischDESolve ((−1)·η) (1 : RadX3)` returns `some`, descending
through the algebraic solver. -/
theorem mixedLaurentTerm_descends :
    (CRischField.crischDESolve mixedLaurentShiftNeg1 (CCommRing.one : RadX3)).isSome = true := by
  native_decide

/-- `∫ t⁻¹ = −t⁻¹` over `RadX3[t]` via the Laurent integrator, the special-part step descending
through the algebraic solver, validated `D(∫f) = f`. -/
theorem mixedHyperexpRecip_integral_descends :
    (match DensePoly.cIntegrateHyperexpLaurent (CCommRing.one : RadX3) [] [CCommRing.one] with
      | some (num, den) =>
          CPoly.checkIdentity mixedHyperexpDt ⟨(num, den), []⟩ [CCommRing.one] [CCommRing.zero, CCommRing.one]
      | none => false) = true := by native_decide

/-- `∫ (t + t⁻¹) = t − t⁻¹` over `RadX3[t]` via the Laurent integrator (polynomial part plus a
descending special part), validated `D(∫f) = f`. -/
theorem mixedHyperexpPolySpec_integral_descends :
    (match DensePoly.cIntegrateHyperexpLaurent (CCommRing.one : RadX3) [CCommRing.zero, CCommRing.one]
        [CCommRing.one] with
      | some (num, den) =>
          CPoly.checkIdentity mixedHyperexpDt ⟨(num, den), []⟩
            [CCommRing.one, CCommRing.zero, CCommRing.one] [CCommRing.zero, CCommRing.one]
      | none => false) = true := by native_decide

/-! ### The full `cIntegrateHyperexp` top entry over `RadX3` -/

/-- `cIntegrateHyperexp`'s top entry validates over `RadX3`: on `f = (t²+1)/t = t + t⁻¹` it returns
`some res` with `checkIdentity` confirming `D(res) = f`. -/
theorem mixedHyperexpG_topEntry_validates :
    (match DensePoly.cIntegrateHyperexp mixedHyperexpDt [CCommRing.one, CCommRing.zero, CCommRing.one]
        [CCommRing.zero, CCommRing.one] [CCommRing.zero, CCommRing.one] with
      | some res =>
          CPoly.checkIdentity mixedHyperexpDt res [CCommRing.one, CCommRing.zero, CCommRing.one]
            [CCommRing.zero, CCommRing.one]
      | none => false) = true := by native_decide

end DeepWiki.SymbolicIntegration
