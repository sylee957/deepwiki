import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalAssembly
import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalLogArgGeneric

/-! # Unified elementary integration over a transcendental tower

The driver `cIntegrateElementary` over a represented fraction base `α = F β`, assembling the carrier
`AlgIntegralResult` (`∫ = v + Σ cᵢ log uᵢ`, defined with its derivative `algDeriv` in
`Engine.Algebraic.RadicalAssembly`). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem DensePoly

universe u

/-! ### `cIntegrateElementary` — the driver over a represented fraction base -/

/-- Elementary integrator `cIntegrateElementary ρ v residual c D degBound` over `α = F β`,
`y² = ρ`: supplied rational part `v`, log argument from `radLogArgSolve ρ residual D degBound`.
On `some N` packs the log term `(c, N/D)`; on `none` returns `⟨v, []⟩`. -/
def cIntegrateElementary {β : Type u} [CField β] [CLinearSolve β]
    {F : (α : Type u) → [CField α] → Type u} {P : Type u → Type u}
    [CPoly P] [CPolyEngine P] [CFrac F P] [LawfulCFrac F P]
    [CFieldDomain β P] [CDiffField (F β)]
    (ρ : F β) (v residual : RadElem (F β)) (c : F β)
    (D : P β) (degBound : ℕ) : AlgIntegralResult (F β) :=
  match radLogArgSolve ρ residual D degBound with
  | none => ⟨v, []⟩
  | some N =>
    let Dq : F β := CFrac.ofPoly D
    let u : RadElem (F β) := N.map (fun z => CField.div z Dq)   -- u = N/D
    ⟨v, [(c, u)]⟩

end DeepWiki.SymbolicIntegration
