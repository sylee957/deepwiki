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

/-! ## Limited integration — the primitive the coefficient recursion calls

The polynomial-part recursion needs, at each degree, a **rational** antiderivative of a coefficient
(an element of the coefficient field itself — introducing a logarithm there would leave the field).
`integrateRational` is `integrate` restricted to log-free results. -/

/-- **Limited integration**: integrate `a/d ∈ α(t)` demanding a **rational** antiderivative (no new
logarithms) — `some (num, den)` with `D(num/den) = a/d`, or `none`. This is the primitive the
polynomial-part coefficient recursion calls: each polynomial coefficient must integrate to an element of
the coefficient field, not introduce a log. -/
def RischSolver.integrateRational [Fact (GcdFFCorrect (α := α))] [RischSolver α]
    (Dt a d : CPolyG α) : Option (CPolyG α × CPolyG α) :=
  (RischSolver.integrate Dt a d).bind fun r => if r.logs.isEmpty then some r.rational else none

/-- **Limited-integration soundness.** A successful `integrateRational` is a genuine *rational*
antiderivative: the log-free `LrtResultG ⟨(num, den), []⟩` satisfies the LRT identity, i.e. over every
splitting extension the tower derivative of `⟦num/den⟧` equals `a/d`. -/
theorem RischSolver.integrateRational_sound [Fact (GcdFFCorrect (α := α))] [RischSolver α]
    (Dt a d num den : CPolyG α) (hd0 : toPolyG d ≠ 0)
    (h : RischSolver.integrateRational Dt a d = some (num, den)) :
    IsIntegralResultLrtG Dt a d ⟨(num, den), []⟩ := by
  unfold RischSolver.integrateRational at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨r, hint, hguard⟩ := h
  split at hguard
  · rename_i hemp
    have hrat : r.rational = (num, den) := (Option.some.injEq _ _).mp hguard
    have hlogs : r.logs = [] := List.isEmpty_iff.mp hemp
    have hgen := (RischSolver.sound Dt a d r hd0 hint).1
    obtain ⟨rr, rl⟩ := r
    simp only at hrat hlogs
    subst hrat; subst hlogs
    exact hgen
  · exact absurd hguard (by simp)

/-! ## The coefficient recursion — generic-tower polynomial-part limited integration

The polynomial part `p = Σ aᵢ tⁱ ∈ α(t)` (primitive case `Dθ = η ∈ α`) integrates to `q = Σ bᵢ tⁱ` with
`D_tower(q) = p`, where `D_tower(q) = Σᵢ (D(bᵢ) + (i+1)·η·bᵢ₊₁) tⁱ`. Matching coefficients gives the
**top-down** system `D(bᵢ) = aᵢ − (i+1)·η·bᵢ₊₁`, each a limited integration of an `α`-coefficient — the
recursion into the coefficient field's solver. This is what the one-level solver skipped (it fires only for
`D(fp) = 0`). -/

/-- **Generic-tower polynomial-part limited integration** (primitive case, `Dθ = η ∈ α`). Solves the
coefficient system `D(bᵢ) = aᵢ − (i+1)·η·bᵢ₊₁` top-down (from the leading coefficient down), each step a
limited integration `intR` of an `α`-coefficient — the recursion into the coefficient field. Returns the
antiderivative's coefficient list `[b₀, …, bₙ]`, or `none` if any coefficient fails to integrate rationally.
Parameterized by `intR : α → Option α` so the tower step plugs in `RischSolver β.integrateRational`. -/
def cLimitedIntegratePolyRatG {α : Type*} [CField α] (η : α) (intR : α → Option α)
    (p : List α) : Option (List α) :=
  p.zipIdx.reverse.foldl (fun acc x =>
    acc.bind fun bs =>
      let rhs := CField.sub x.1 (CField.mul (CField.mul (cnatCastG (x.2 + 1)) η) (bs.headD CField.zero))
      (intR rhs).map (fun bi => bi :: bs))
    (some [])

end DeepWiki.SymbolicIntegration
