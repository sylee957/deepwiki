import DeepWiki.SymbolicIntegration.Computable.Parametric
import DeepWiki.SymbolicIntegration.Computable.Tower.CarrierRec

/-! # Base single-`w` limited integration (Phase 1 of `docs/tower-limited-integration.md`)

The operation the recursive primitive-polynomial case needs but currently lacks: **`LimitedIntegrate(a, η)`**
(Bronstein §5.8/§5.12) — find `b ∈ k` and a constant `c` with

```
a = D(b) + c·η
```

for a **raw** generator `η = Dt` (the primitive's derivative — the `c·t` degree-raiser), over the base field
`k = ℚ(x)`. This is `cParamRischDE`'s two-generator kernel `{(c₀,c₁) : c₀·a + c₁·η = Dp}`: take the `c₀ ≠ 0`
vector, normalize `c₀ = 1` (so `a = Dp + (−c₁)·η`), and recover `b = p` by integrating the (polynomial) cleared
residual. Scope = the **polynomial-`b`** regime (matches `cParamRischDE`); rational `b` (a Hermite pre-pass) is
Phase 1b. -/

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

namespace CPolyG

/-- **Base polynomial antiderivative over ℚ** `cAntiderivBaseQ p = ∫ p dt`: for `p = Σ aᵢ tⁱ`, returns
`Σ aᵢ/(i+1)·t^(i+1)` (constant of integration `0`). The `D = d/dt` inverse on `ℚ[t]`. -/
def cAntiderivBaseQ (p : CPolyG ℚ) : CPolyG ℚ :=
  (0 : ℚ) :: ((p : List ℚ).zipIdx.map (fun ai => ai.1 / (ai.2 + 1)))

/-- **Base single-`w` limited integration** `cLimitedIntegrateSingleBase a η` (Bronstein §5.8's
`LimitedIntegrate(a, Dt)`, `k = ℚ(x)`, polynomial-`b` regime): returns `some (b, c)` with `a = D(b) + c·η`
(`b ∈ ℚ[x] ⊂ ℚ(x)`, `c ∈ ℚ`), or `none` if no such pair exists in this regime. Builds the two-generator
constraint system `[a, η]` (`cLinearConstraintsQ`), takes the `c₀ ≠ 0` kernel vector (`cNullspaceBasisQ`),
normalizes `c₀ = 1`, and recovers `b` by antidifferentiating the cleared polynomial residual `q₀ + c₁·q₁`. -/
def cLimitedIntegrateSingleBase (a η : QFunNZG ℚ) : Option (QFunNZG ℚ × ℚ) :=
  let gnums := [a.1.1, η.1.1]
  let gdens := [a.1.2, η.1.2]
  let (qs, M) := cLinearConstraintsQ gnums gdens
  let kernel := cNullspaceBasisQ M 2
  match kernel.find? (fun v => v.getD 0 0 ≠ 0) with
  | none => none
  | some v =>
    let c0 := v.getD 0 0
    let c1 := (v.getD 1 0) / c0                                   -- normalized `c₁` (`c₀ = 1`)
    let integrand := caddG (qs.getD 0 []) (cscaleG c1 (qs.getD 1 []))
    let bpoly := cAntiderivBaseQ integrand
    some (⟨(bpoly, [(1 : ℚ)]), QFunNZG.cisZeroG_one_singleton⟩, -c1)

end CPolyG

/-! ### Validation — the degree-raising example

`a = 1 + 1/x`, `η = 1/x` (so `t` is the primitive with `Dt = 1/x`, i.e. `t = log x`): the antiderivative
`∫(1 + 1/x) dx = x + log x = x + t`, i.e. `a = D(x) + 1·η`. So `LimitedIntegrate(a, η) = (x, 1)` — the constant
`c = 1` is exactly the degree-raiser the current log-free discharge cannot produce. -/

open CPolyG

/-- `a = 1 + 1/x = (x+1)/x ∈ ℚ(x)`. -/
def limIntSingleExampleA : QFunNZG ℚ := ⟨([1, 1], [0, 1]), by decide⟩
/-- `η = 1/x ∈ ℚ(x)` (the primitive derivative `Dt = 1/x`). -/
def limIntSingleExampleEta : QFunNZG ℚ := ⟨([1], [0, 1]), by decide⟩

-- **Sanity print.** `cLimitedIntegrateSingleBase (1+1/x) (1/x)` should give `(b, c)` with `b = x`, `c = 1`.
#eval (cLimitedIntegrateSingleBase limIntSingleExampleA limIntSingleExampleEta).map
  (fun bc => (CPolyG.qnormPairG bc.1.1.1 bc.1.1.2, bc.2))

/-- **The base single-`w` limited integration finds the degree-raising constant.** For `a = 1 + 1/x`,
`η = 1/x`, `cLimitedIntegrateSingleBase` returns `(b, c)` satisfying the defining identity `a = D(b) + c·η`
(with `D` the base derivation on `ℚ(x)`), i.e. `a − D(b) − c·η = 0`. The witness has `c = 1` (nonzero — the
degree-raiser). -/
theorem cLimitedIntegrateSingleBase_example :
    (match cLimitedIntegrateSingleBase limIntSingleExampleA limIntSingleExampleEta with
      | some (b, c) =>
          CField.isZero (CField.sub limIntSingleExampleA
            (CField.add (CDiffField.cderiv b)
              (CField.mul (CPolyG.qConstParamG c) limIntSingleExampleEta)))
            && decide (c ≠ 0)
      | none => false) = true := by native_decide

end DeepWiki.SymbolicIntegration
