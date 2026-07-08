import DeepWiki.SymbolicIntegration.Computable.Algebraic.RadicalAssembly
import DeepWiki.SymbolicIntegration.Computable.Algebraic.RadicalLogArgGeneric

/-! # Unified elementary integration over a transcendental tower.

The carrier `AlgIntegralResultG` (`∫ = v + Σ cᵢ log uᵢ`), its derivative `algDerivG`, and
the driver `cIntegrateElementaryG` over a tower base `α = QFunNZG β`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem CPolyG

/-! ### `AlgIntegralResultG` and its derivative -/

/-- Tower-generic elementary integral `∫ = v + Σ cᵢ log uᵢ`: rational part `v : RadElem α` plus
log terms `[(cᵢ, uᵢ)]` (`cᵢ ∈ α`, `uᵢ ∈ α[y]/(y² − ρ)`). -/
structure AlgIntegralResultG (α : Type*) [CField α] where
  /-- The rational part `v` of `∫ = v + Σ cᵢ log uᵢ` (a `RadElem α`). -/
  ratPart : RadElem α
  /-- The log terms `[(cᵢ, uᵢ)]` (`cᵢ ∈ α`, `uᵢ : RadElem α`). -/
  logTerms : List (α × RadElem α)

/-- Derivative `algDerivG ρ F = radDeriv v + Σ cᵢ · radLogDeriv uᵢ` in `α[y]/(y² − ρ)`, using the
tower's `CDiffField.cderiv` as base derivation. -/
def algDerivG {α : Type*} [CField α] [CDiffField α] (ρ : α) (F : AlgIntegralResultG α) : RadElem α :=
  F.logTerms.foldl
    (fun acc (c, u) => radAdd acc (radScale c (radLogDeriv ρ u)))
    (radDeriv 2 ρ F.ratPart)

/-! ### `cIntegrateElementaryG` — the driver over a tower base `α = QFunNZG β` -/

/-- Elementary integrator `cIntegrateElementaryG ρ v residual c D degBound` over `α = QFunNZG β`,
`y² = ρ`: supplied rational part `v`, log argument from `radLogArgSolveG ρ residual D degBound`.
On `some N` packs the log term `(c, N/D)`; on `none` returns `⟨v, []⟩`. -/
def cIntegrateElementaryG {β : Type*} [CField β] [CFieldDomain β] [CDiffField (QFunNZG β)]
    (ρ : QFunNZG β) (v : RadElem (QFunNZG β)) (residual : RadElem (QFunNZG β)) (c : QFunNZG β)
    (D : CPolyG β) (degBound : ℕ) : AlgIntegralResultG (QFunNZG β) :=
  match radLogArgSolveG ρ residual D degBound with
  | none => ⟨v, []⟩
  | some N =>
    let Dq : QFunNZG β := qOfNumG D
    let u : RadElem (QFunNZG β) := N.map (fun z => CField.div z Dq)   -- u = N/D
    ⟨v, [(c, u)]⟩

end DeepWiki.SymbolicIntegration
