import DeepWiki.SymbolicIntegration.Engine.LrtIntegrate
import DeepWiki.SymbolicIntegration.Engine.LrtSoundness

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


namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCoreWf α]

/-- **The primitive-case integrability guard** (Bronstein §5.6, root-free): the residues (**roots** of the
Rothstein–Trager residue resultant `R = cResidueResultantTowerG Dt hNum Dstar`, `hNum/Dstar` the Hermite
residual) are all **constants** iff the **monic** `R` has constant coefficients (its elementary symmetric
functions in the roots are constant), i.e. `D(cmonicG R) = 0` — checked coefficient-wise by `cmapDeriv`.
Monic-normalizing is essential: the raw `R` may carry a non-constant leading factor (e.g. `1/x`) that is a
resultant-scaling artifact, not residue non-constancy. Decidable, no root-finding. -/
def cResidueConstantGuardG (Dt a d : CPolyG α) : Bool :=
  let H := cHermiteReduceTowerG Dt a d
  cisZeroG (cmapDeriv (cmonicG (cResidueResultantTowerG Dt H.2.1 H.2.2)))

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

open CPolyG in
/-- **All LRT residues are constant** (result-level, `Bool`). Every residue minimal polynomial `Rᵢ` in
`res.logs` has constant coefficients after monic normalization (`D(monic Rᵢ) = 0`, coefficient-wise
`cmapDeriv`) — i.e. its roots, the algebraic residues, are constants. Monic normalization strips the
resultant-scaling artifact (as in `cResidueConstantGuardG`). The `Bool` guard the genuine integrator checks. -/
def allResiduesConstantLrtG {α : Type*} [CField α] [CDiffField α] (res : LrtResultG α) : Bool :=
  res.logs.all (fun RS => cisZeroG (cmapDeriv (cmonicG RS.1)))

/-- **All LRT residues are constant** (`Prop`). The LRT analogue of `AllResiduesConstantG`; the residues here
are **roots of `Rᵢ`** (not explicit `α`), so constancy is `D(monic Rᵢ) = 0` rather than `D(cᵢ) = 0`. -/
def AllResiduesConstantLrtG {α : Type*} [CField α] [CDiffField α] (res : LrtResultG α) : Prop :=
  allResiduesConstantLrtG res = true

/-- **Genuine LRT integral result**: the formal LRT identity `IsIntegralResultLrtG` **and** all residues
constant (`AllResiduesConstantLrtG`). The conjunction certifies a *true* antiderivative
`⟦g⟧ + Σᵢ Σ_{Rᵢ(c)=0} c·log Sᵢ(c,t)` with constant algebraic residues — the LRT analogue of
`IsGenuineIntegralResultG`; `IsIntegralResultLrtG` alone is the formal (constant-treated) identity. -/
def IsGenuineIntegralResultLrtG {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    (Dt anum aden : CPolyG α) (res : LrtResultG α) : Prop :=
  IsIntegralResultLrtG Dt anum aden res ∧ AllResiduesConstantLrtG res

/-- **Genuine (broad) elementary integrability** — the well-posed LRT completeness target: there is an
`LrtResultG` that is a *genuine* integral result (LRT identity **and** constant residues). Unlike the formal
`IsElementaryIntegrableLrtG` (which holds whenever the poles lie over `K`, regardless of residue-constancy),
its negation is a meaningful non-integrability statement. The algebraic-residue analogue of
`IsElementaryIntegrableGenuineG`. -/
def IsElementaryIntegrableGenuineLrtG {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    (Dt a d : CPolyG α) : Prop :=
  ∃ res : LrtResultG α, IsGenuineIntegralResultLrtG Dt a d res

/-- Any genuine LRT witness makes `a/d` genuinely (broadly) elementary integrable. -/
theorem IsElementaryIntegrableGenuineLrtG.of_genuine {α : Type*} [CField α] [CFieldSpec α] [CDiffField α]
    [CDiffFieldSpec α] {Dt a d : CPolyG α} {res : LrtResultG α}
    (h : IsGenuineIntegralResultLrtG Dt a d res) : IsElementaryIntegrableGenuineLrtG Dt a d :=
  ⟨res, h⟩

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
