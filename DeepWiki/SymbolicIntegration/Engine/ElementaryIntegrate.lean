import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalAssembly
import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalLogArgGeneric

/-! # Unified elementary integration over a transcendental tower.

The driver `cIntegrateElementary` over a tower base `α = DenseFrac β`, assembling the carrier
`AlgIntegralResult` (`∫ = v + Σ cᵢ log uᵢ`, defined with its derivative `algDeriv` in
`Engine.Algebraic.RadicalAssembly`). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem DensePoly

/-! ### `cIntegrateElementary` — the driver over a tower base `α = DenseFrac β` -/

/-- Elementary integrator `cIntegrateElementary ρ v residual c D degBound` over `α = DenseFrac β`,
`y² = ρ`: supplied rational part `v`, log argument from `radLogArgSolve ρ residual D degBound`.
On `some N` packs the log term `(c, N/D)`; on `none` returns `⟨v, []⟩`. -/
def cIntegrateElementary {β : Type*} [CField β] [CLinearSolve β]
    [CFieldDomain β DensePoly] [CDiffField (DenseFrac β)]
    (ρ : DenseFrac β) (v : RadElem (DenseFrac β)) (residual : RadElem (DenseFrac β)) (c : DenseFrac β)
    (D : DensePoly β) (degBound : ℕ) : AlgIntegralResult (DenseFrac β) :=
  match radLogArgSolve ρ residual D degBound with
  | none => ⟨v, []⟩
  | some N =>
    let Dq : DenseFrac β := CFrac.ofPoly D
    let u : RadElem (DenseFrac β) := N.map (fun z => CField.div z Dq)   -- u = N/D
    ⟨v, [(c, u)]⟩

end DeepWiki.SymbolicIntegration
