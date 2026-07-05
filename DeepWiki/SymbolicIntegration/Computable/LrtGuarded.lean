import DeepWiki.SymbolicIntegration.Computable.LrtIntegrate
import DeepWiki.SymbolicIntegration.Computable.LrtSoundness

/-! # The primitive-case integrability guard for the root-free LRT integrator

`cIntegrateReducedLrtG` is *total* — it emits symbolic log terms for any input, including non-elementary
reduced parts (e.g. `∫1/log x`), where those terms do **not** differentiate back. The reason: the residue sum
`logResidueSumLrtG = Σ c·D(Sᵢ)/Sᵢ` multiplies each residue `c` in as a constant, so `D(g) + logResidueSumLrtG`
equals the genuine derivative `D(g + Σ c·log Sᵢ)` *exactly when every residue `c` is a constant* — otherwise the
real derivative carries an extra `Σ D(c)·log(Sᵢ)`.

Bronstein's primitive-case criterion (§5.6) is **decidable and root-free**: the residues (roots of the
Rothstein–Trager residue resultant `R`) are all constants iff `R` has constant coefficients, i.e. `D(R) = 0`.
This file adds that guard, turning the integrator into an `Option` that declines non-elementary inputs. -/

namespace DeepWiki.SymbolicIntegration

open Compute

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCoreWf α]

/-- **The primitive-case integrability guard** (Bronstein §5.6, root-free): the residues (roots of the
Rothstein–Trager residue resultant `R = cResidueResultantTowerGWf Dt hNum Dstar`, `hNum/Dstar` the Hermite
residual) are all **constants** iff `R` has constant coefficients, i.e. `D(R) = 0` — checked coefficient-wise
by `cmapDeriv`. Decidable, no root-finding. -/
def cResidueConstantGuardG (Dt a d : CPolyG α) : Bool :=
  let H := cHermiteReduceTowerGWf Dt a d
  cisZeroG (cmapDeriv (cResidueResultantTowerGWf Dt H.2.1 H.2.2))

/-- **The guarded root-free LRT reduced integrator.** Returns the LRT reduced result only when the
integrability guard passes (residues are constants); `none` otherwise — correctly declining non-elementary
reduced parts (e.g. `∫1/log x`, whose residue `x` is non-constant). -/
def cIntegrateReducedLrtGuardedG (Dt a d : CPolyG α) : Option (LrtResultG α) :=
  if cResidueConstantGuardG Dt a d then some (cIntegrateReducedLrtG Dt a d) else none

/-- The guard passes iff `cResidueConstantGuardG` is `true` (definitional unfolding of the `if`). -/
theorem cIntegrateReducedLrtGuardedG_eq_some_iff (Dt a d : CPolyG α) :
    cIntegrateReducedLrtGuardedG Dt a d = some (cIntegrateReducedLrtG Dt a d)
      ↔ cResidueConstantGuardG Dt a d = true := by
  unfold cIntegrateReducedLrtGuardedG
  cases h : cResidueConstantGuardG Dt a d <;> simp_all

/-- **Extraction from a successful guarded run.** If the guarded integrator returns `res`, then the guard
passed *and* `res` is exactly the unguarded LRT result — the bridge from the `Option`-valued integrator to the
underlying soundness. -/
theorem cIntegrateReducedLrtGuardedG_some (Dt a d : CPolyG α) (res : LrtResultG α)
    (h : cIntegrateReducedLrtGuardedG Dt a d = some res) :
    cResidueConstantGuardG Dt a d = true ∧ res = cIntegrateReducedLrtG Dt a d := by
  unfold cIntegrateReducedLrtGuardedG at h
  split at h
  · rename_i hg
    injection h with h'
    exact ⟨hg, h'.symm⟩
  · exact absurd h (by simp)

end CPolyG

open CPolyG in
/-- **Guarded LRT reduced soundness.** A successful *guarded* run is sound: it returns the unguarded LRT
result (`cIntegrateReducedLrtGuardedG_some`), whose soundness `hsound` — supplied by
`isIntegralResultLrtG_cIntegrateReducedLrtG_of_setup` under the genuine Bronstein setup conditions — transfers
verbatim. The guard makes the integrator *correctly partial* (declining non-elementary inputs, where the
unconditional claim is false); this is the shape a real Risch soundness theorem takes — `= some res ⇒ correct`
— now with a **real** guard instead of the no-op `some nrm`. -/
theorem cIntegrateReducedLrtGuardedG_sound {α : Type*} [CField α] [CFieldSpec α] [CDiffField α]
    [CDiffFieldSpec α] [CFracGcdCoreWf α] (Dt a d : CPolyG α) (res : LrtResultG α)
    (hguarded : cIntegrateReducedLrtGuardedG Dt a d = some res)
    (hsound : IsIntegralResultLrtG Dt a d (cIntegrateReducedLrtG Dt a d)) :
    IsIntegralResultLrtG Dt a d res :=
  (cIntegrateReducedLrtGuardedG_some Dt a d res hguarded).2 ▸ hsound

/-! ### Validation (`native_decide`) -/

namespace CPolyG

/-- Over `ℚ` (a field of constants, `D ≡ 0`) every reduced part is integrable, so the guard passes:
`∫1/(t²−1)` is accepted (residues `±1/2` are constants). -/
theorem cResidueConstantGuardG_invT2m1 :
    cResidueConstantGuardG ([1] : CPolyG ℚ) [1] [-1, 0, 1] = true := by native_decide

/-- The guarded integrator accepts `∫1/(t²−1)` over `ℚ`, returning the same result as the unguarded one
(derived from the guard passing + the `= some` characterization, no `DecidableEq` on `LrtResultG` needed). -/
theorem cIntegrateReducedLrtGuardedG_invT2m1 :
    cIntegrateReducedLrtGuardedG ([1] : CPolyG ℚ) [1] [-1, 0, 1]
      = some (cIntegrateReducedLrtG ([1] : CPolyG ℚ) [1] [-1, 0, 1]) :=
  (cIntegrateReducedLrtGuardedG_eq_some_iff _ _ _).mpr cResidueConstantGuardG_invT2m1

end CPolyG

end DeepWiki.SymbolicIntegration
