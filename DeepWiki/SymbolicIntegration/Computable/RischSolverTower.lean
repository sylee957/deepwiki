import DeepWiki.SymbolicIntegration.Computable.RischTowerLrt

/-! # `RischSolver` — the recursive Risch tower solver (base + step)

The genuine, root-free Risch integrator, structured **recursively** over the monomial tower. Where
`LawfulRischLevelLrt` is a *one-level* solver (it handles the reduced part via LRT and the special part
only in the constant-coefficient regime), `RischSolver` is the recursion: integrating `a/d ∈ α(t)`
decomposes into the polynomial part, the reduced part (root-free LRT — reused verbatim), and the special
part, and the **polynomial part's coefficient integration recurses into `RischSolver` for the coefficient
field**. That coefficient recursion is the heart of the transcendental algorithm (Bronstein §5.3–5.9) and
is exactly what the one-level solver was missing — its `integrateSpecial` fires only when the polynomial
part has constant coefficients (`D(fp) = 0`).

- **`integrate`** — integrate `a/d ∈ α(t)` (monomial derivative `Dt`) to a root-free `LrtResultG`, or `none`.
- **`sound`** — a successful run is a **genuine** antiderivative (`IsGenuineIntegralResultLrtG`: the LRT
  identity + all residues constant).

The **base** instance reuses the genuine one-level LRT solver (`integrateLrt`/`soundLrt`) — correct for the
constant-coefficient regime (`ℚ(x)` and any level whose polynomial part is constant). The **step**
(`RischSolverStep.lean`) adds the coefficient recursion `[RischSolver β] → RischSolver (QFunNZG β)` via the
generic-tower limited integration. See `docs/recursive-risch-tower.md`. -/

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG Polynomial
open scoped Differential

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)]

/-- **The recursive Risch tower solver, as a class.** `integrate Dt a d` integrates `a/d ∈ α(t)` (with
monomial derivative `Dt`) to a root-free `LrtResultG α`, or declines; `sound` certifies a successful run is a
*genuine* antiderivative (`IsGenuineIntegralResultLrtG`). One instance at each tower level (base + step)
assembles a solver at every depth by resolution. -/
class RischSolver (α : Type*) [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)]
    [Fact (GcdFFCorrect (α := α))] where
  /-- Integrate `a/d ∈ α(t)` (monomial derivative `Dt`) to a root-free LRT result, or `none`. -/
  integrate : CPolyG α → CPolyG α → CPolyG α → Option (LrtResultG α)
  /-- **Genuine soundness**: a successful run is a true antiderivative of `a/d` with constant residues. -/
  sound : ∀ (Dt a d : CPolyG α) (r : LrtResultG α), toPolyG d ≠ 0 →
    integrate Dt a d = some r → IsGenuineIntegralResultLrtG Dt a d r

/-- **The base Risch solver** — the genuine one-level LRT solver *is* a Risch solver: it handles the reduced
part (root-free LRT) and the special part in the constant-coefficient regime, which is complete at the tower
base (`ℚ(x)`, where the polynomial-part coefficients are constants). Reuses `integrateLrt` / `soundLrt`
verbatim; the coefficient recursion is added by the step instance. Low priority so the step wins at
`QFunNZG` levels. -/
instance (priority := 100) instRischSolverOfLawfulLrt [Fact (GcdFFCorrect (α := α))]
    [LawfulRischLevelLrt α] : RischSolver α where
  integrate := LawfulRischLevelLrt.integrateLrt
  sound Dt a d r _ h := LawfulRischLevelLrt.soundLrt Dt a d r h

/-- The base solver's `integrate` is exactly `integrateLrt` (the reduced part is genuine LRT, so this
transports the guard + soundness of the one-level solver). -/
theorem RischSolver.integrate_base_eq [Fact (GcdFFCorrect (α := α))] [LawfulRischLevelLrt α]
    (Dt a d : CPolyG α) :
    (instRischSolverOfLawfulLrt).integrate Dt a d = LawfulRischLevelLrt.integrateLrt Dt a d := rfl

end DeepWiki.SymbolicIntegration
