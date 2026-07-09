import DeepWiki.SymbolicIntegration.Engine.LimitedIntegrateSingle

/-! # Base limited-integration examples

Executable checks for the single-generator limited integrator over `ℚ(x)`. -/

namespace DeepWiki.SymbolicIntegration

open CPolyG Polynomial

/-! ### Base limited integration -/

/-- `a = 1 + 1/x = (x+1)/x ∈ ℚ(x)`. -/
def limIntSingleExampleA : QFunNZG ℚ := ⟨([1, 1], [0, 1]), by decide⟩

/-- `η = 1/x ∈ ℚ(x)` (the primitive derivative `Dt = 1/x`). -/
def limIntSingleExampleEta : QFunNZG ℚ := ⟨([1], [0, 1]), by decide⟩

-- Sanity print: `cLimitedIntegrateSingleBase (1+1/x) (1/x)` returns `b = x`, `c = 1`.
#eval (cLimitedIntegrateSingleBase limIntSingleExampleA limIntSingleExampleEta).map
  (fun bc => (CPolyG.qnormPairG bc.1.1.1 bc.1.1.2, bc.2))

/-- The base single-`w` limited integrator finds the degree-raising constant. -/
theorem cLimitedIntegrateSingleBase_example :
    (match cLimitedIntegrateSingleBase limIntSingleExampleA limIntSingleExampleEta with
      | some (b, c) =>
          CField.isZero (CField.sub limIntSingleExampleA
            (CField.add (CDiffField.cderiv b)
              (CField.mul (CPolyG.qConstParamG c) limIntSingleExampleEta)))
            && decide (c ≠ 0)
      | none => false) = true := by native_decide

-- Sanity print: the num/den adapter on `(1+1/x, 1/x)`.
#eval (limitedIntegrateSingleBaseNumDen [1, 1] [0, 1] [1] [0, 1]).map
  (fun r => (CPolyG.qnormPairG r.1.1 r.1.2, r.2))

/-- The num/den adapter matches `cLimitedIntegrateSingleBase` on `1+1/x` and `1/x`. -/
theorem limitedIntegrateSingleBaseNumDen_example :
    (limitedIntegrateSingleBaseNumDen [1, 1] [0, 1] [1] [0, 1]).map
      (fun r => (CPolyG.qnormPairG r.1.1 r.1.2, r.2)) = some (([0, 1], [1]), 1) := by native_decide

/-! ### Degree-raising primitive polynomial integration -/

/-- The base single-`w` limited integrator wrapped with constants embedded in `ℚ(x)`. -/
def limIntBaseWrap (η a : QFunNZG ℚ) : Option (QFunNZG ℚ × QFunNZG ℚ) :=
  (cLimitedIntegrateSingleBase a η).map (fun bc => (bc.1, CPolyG.qConstParamG bc.2))

/-- `p = 1 + (1 + 1/x)·t ∈ ℚ(x)[t]`. -/
def prim2ExampleP : CPolyG (QFunNZG ℚ) := [qConstParamG 1, limIntSingleExampleA]

-- Sanity print: `∫p = x·t + (1/2)·t²`.
#eval (cIntegratePrimPolyDegRaiseG limIntSingleExampleEta (limIntBaseWrap limIntSingleExampleEta) 3
    prim2ExampleP).map (fun q => q.map (fun c => CPolyG.qnormPairG c.1.1 c.1.2))

/-- The degree-raising primitive-polynomial integrator is correct on the two-level example. -/
theorem cIntegratePrimPolyDegRaiseG_example :
    (match cIntegratePrimPolyDegRaiseG limIntSingleExampleEta (limIntBaseWrap limIntSingleExampleEta) 3
        prim2ExampleP with
      | some q =>
          cisZeroG (csubG (cmonomialDeriv [limIntSingleExampleEta] q) prim2ExampleP)
            && decide (cdegG q = 2)
      | none => false) = true := by native_decide

end DeepWiki.SymbolicIntegration
