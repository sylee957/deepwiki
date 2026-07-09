import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalAssembly
import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalLogArgGeneric

/-! # Unified elementary integration over a transcendental tower.

The driver `cIntegrateElementary` over a tower base `α = QFunNZG β`, assembling the carrier
`AlgIntegralResultG` (`∫ = v + Σ cᵢ log uᵢ`, defined with its derivative `algDerivG` in
`Engine.Algebraic.RadicalAssembly`). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem CPoly

/-! ### `cIntegrateElementary` — the driver over a tower base `α = QFunNZG β` -/

/-- Elementary integrator `cIntegrateElementary ρ v residual c D degBound` over `α = QFunNZG β`,
`y² = ρ`: supplied rational part `v`, log argument from `radLogArgSolveG ρ residual D degBound`.
On `some N` packs the log term `(c, N/D)`; on `none` returns `⟨v, []⟩`. -/
def cIntegrateElementary {β : Type*} [CField β] [CFieldDomain β] [CDiffField (QFunNZG β)]
    (ρ : QFunNZG β) (v : RadElem (QFunNZG β)) (residual : RadElem (QFunNZG β)) (c : QFunNZG β)
    (D : CPoly β) (degBound : ℕ) : AlgIntegralResultG (QFunNZG β) :=
  match radLogArgSolveG ρ residual D degBound with
  | none => ⟨v, []⟩
  | some N =>
    let Dq : QFunNZG β := qOfNumG D
    let u : RadElem (QFunNZG β) := N.map (fun z => CField.div z Dq)   -- u = N/D
    ⟨v, [(c, u)]⟩

end DeepWiki.SymbolicIntegration
