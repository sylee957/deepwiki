import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalAssembly
import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalLogArgGeneric

/-! # Unified elementary integration over a transcendental tower.

The driver `cIntegrateElementary` over a tower base `α = CFrac β`, assembling the carrier
`AlgIntegralResult` (`∫ = v + Σ cᵢ log uᵢ`, defined with its derivative `algDeriv` in
`Engine.Algebraic.RadicalAssembly`). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem CPoly

/-! ### `cIntegrateElementary` — the driver over a tower base `α = CFrac β` -/

/-- Elementary integrator `cIntegrateElementary ρ v residual c D degBound` over `α = CFrac β`,
`y² = ρ`: supplied rational part `v`, log argument from `radLogArgSolve ρ residual D degBound`.
On `some N` packs the log term `(c, N/D)`; on `none` returns `⟨v, []⟩`. -/
def cIntegrateElementary {β : Type*} [CField β] [CFieldDomain β] [CDiffField (CFrac β)]
    (ρ : CFrac β) (v : RadElem (CFrac β)) (residual : RadElem (CFrac β)) (c : CFrac β)
    (D : CPoly β) (degBound : ℕ) : AlgIntegralResult (CFrac β) :=
  match radLogArgSolve ρ residual D degBound with
  | none => ⟨v, []⟩
  | some N =>
    let Dq : CFrac β := qOfNum D
    let u : RadElem (CFrac β) := N.map (fun z => CField.div z Dq)   -- u = N/D
    ⟨v, [(c, u)]⟩

end DeepWiki.SymbolicIntegration
