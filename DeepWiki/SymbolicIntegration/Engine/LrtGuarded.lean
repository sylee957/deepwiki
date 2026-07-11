import DeepWiki.SymbolicIntegration.Engine.LrtIntegrate
import DeepWiki.SymbolicIntegration.Engine.LrtSoundness

/-! # The primitive-case integrability guard for the root-free LRT integrator

`cIntegrateReducedLrt` is *total* — it emits symbolic log terms for any input, including non-elementary
reduced parts (e.g. `∫1/log x`), where those terms do **not** differentiate back. The reason: the residue sum
`logResidueSumLrt = Σ c·D(Sᵢ)/Sᵢ` multiplies each residue `c` in as a constant, so `D(g) + logResidueSumLrt`
equals the genuine derivative `D(g + Σ c·log Sᵢ)` *exactly when every residue `c` is a constant* — otherwise the
real derivative carries an extra `Σ D(c)·log(Sᵢ)`.

Bronstein's primitive-case criterion (§5.6) is **decidable and root-free**: the residues (roots of the
Rothstein–Trager residue resultant `R`) are all constants iff `R` has constant coefficients, i.e. `D(R) = 0`.
This file adds that guard, turning the integrator into an `Option` that declines non-elementary inputs. -/

namespace DeepWiki.SymbolicIntegration

universe u

namespace DensePoly

variable {α : Type*} [CField α] [CDiffField α] [CPolySquarefree DensePoly α]
  [CPolyResultant DensePoly] [CPolySubresultant DensePoly]

/-- **The primitive-case integrability guard** (Bronstein §5.6, root-free): the residues (**roots** of the
Rothstein–Trager residue resultant `R = cResidueResultantTower Dt hNum Dstar`, `hNum/Dstar` the Hermite
residual) are all **constants** iff the **monic** `R` has constant coefficients (its elementary symmetric
functions in the roots are constant), i.e. `D(cmonic R) = 0` — checked coefficient-wise by `CPolyEngine.mapDeriv`.
Monic-normalizing is essential: the raw `R` may carry a non-constant leading factor (e.g. `1/x`) that is a
resultant-scaling artifact, not residue non-constancy. Decidable, no root-finding. -/
def cResidueConstantGuard (Dt a d : DensePoly α) : Bool :=
  let H := cHermiteReduceTower Dt a d
  cisZero (CPolyEngine.mapDeriv (cmonic (cResidueResultantTower Dt H.2.1 H.2.2)))

/-- **The guarded root-free LRT reduced integrator.** Returns the LRT reduced result only when the
integrability guard passes (residues are constants); `none` otherwise — correctly declining non-elementary
reduced parts (e.g. `∫1/log x`, whose residue `x` is non-constant). -/
def cIntegrateReducedLrtGuarded (Dt a d : DensePoly α) : Option (LrtResult α) :=
  if cResidueConstantGuard Dt a d then some (cIntegrateReducedLrt Dt a d) else none

/-- The guard passes iff `cResidueConstantGuard` is `true` (definitional unfolding of the `if`). -/
theorem cIntegrateReducedLrtGuardedG_eq_some_iff (Dt a d : DensePoly α) :
    cIntegrateReducedLrtGuarded Dt a d = some (cIntegrateReducedLrt Dt a d)
      ↔ cResidueConstantGuard Dt a d = true := by
  unfold cIntegrateReducedLrtGuarded
  cases h : cResidueConstantGuard Dt a d <;> simp_all

/-- **Extraction from a successful guarded run.** If the guarded integrator returns `res`, then the guard
passed *and* `res` is exactly the unguarded LRT result — the bridge from the `Option`-valued integrator to the
underlying soundness. -/
theorem cIntegrateReducedLrtGuardedG_some (Dt a d : DensePoly α) (res : LrtResult α)
    (h : cIntegrateReducedLrtGuarded Dt a d = some res) :
    cResidueConstantGuard Dt a d = true ∧ res = cIntegrateReducedLrt Dt a d := by
  unfold cIntegrateReducedLrtGuarded at h
  split at h
  · rename_i hg
    injection h with h'
    exact ⟨hg, h'.symm⟩
  · exact absurd h (by simp)

end DensePoly

open DensePoly in
/-- **Guarded LRT reduced soundness.** A successful *guarded* run is sound: it returns the unguarded LRT
result (`cIntegrateReducedLrtGuardedG_some`), whose soundness `hsound` — supplied by
`isIntegralResultLrtG_cIntegrateReducedLrtG_of_setup` under the genuine Bronstein setup conditions — transfers
verbatim. The guard makes the integrator *correctly partial* (declining non-elementary inputs, where the
unconditional claim is false); this is the shape a real Risch soundness theorem takes — `= some res ⇒ correct`
— now with a **real** guard instead of the no-op `some nrm`. -/
theorem cIntegrateReducedLrtGuardedG_sound {α : Type*} [CField α] [CFieldSpec α] [CDiffField α]
    [CDiffFieldSpec α] [CPolySquarefree DensePoly α] [CPolyResultant DensePoly]
    [CPolySubresultant DensePoly] (Dt a d : DensePoly α) (res : LrtResult α)
    (hguarded : cIntegrateReducedLrtGuarded Dt a d = some res)
    (hsound : IsIntegralResultLrt Dt a d (cIntegrateReducedLrt Dt a d)) :
    IsIntegralResultLrt Dt a d res :=
  (cIntegrateReducedLrtGuardedG_some Dt a d res hguarded).2 ▸ hsound

/-- **All LRT residues are constant** (result-level, `Bool`). Every residue minimal polynomial `Rᵢ` in
`res.logs` has constant coefficients after monic normalization (`D(monic Rᵢ) = 0`, coefficient-wise
`CPolyEngine.mapDeriv`) — i.e. its roots, the algebraic residues, are constants. Monic normalization strips the
resultant-scaling artifact (as in `cResidueConstantGuard`). The `Bool` guard the genuine integrator checks. -/
def allResiduesConstantLrt {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] [CDiffField α] (res : LrtResult α P) : Bool :=
  res.logs.all (fun RS =>
    CPolyEngine.cisZero (CPolyEngine.mapDeriv (CPolyEngine.cmonic RS.1)))

/-- **All LRT residues are constant** (`Prop`). The LRT analogue of `AllResiduesConstant`; the residues here
are **roots of `Rᵢ`** (not explicit `α`), so constancy is `D(monic Rᵢ) = 0` rather than `D(cᵢ) = 0`. -/
def AllResiduesConstantLrt {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] [CDiffField α] (res : LrtResult α P) : Prop :=
  allResiduesConstantLrt res = true

/-- **Genuine LRT integral result**: the formal LRT identity `IsIntegralResultLrt` **and** all residues
constant (`AllResiduesConstantLrt`). The conjunction certifies a *true* antiderivative
`⟦g⟧ + Σᵢ Σ_{Rᵢ(c)=0} c·log Sᵢ(c,t)` with constant algebraic residues — the LRT analogue of
`IsGenuineIntegralResult`; `IsIntegralResultLrt` alone is the formal (constant-treated) identity. -/
def IsGenuineIntegralResultLrt {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    (Dt anum aden : DensePoly α) (res : LrtResult α) : Prop :=
  IsIntegralResultLrt Dt anum aden res ∧ AllResiduesConstantLrt res

/-- **Genuine (broad) elementary integrability** — the well-posed LRT completeness target: there is an
`LrtResult` that is a *genuine* integral result (LRT identity **and** constant residues). Unlike the formal
`IsElementaryIntegrableLrt` (which holds whenever the poles lie over `K`, regardless of residue-constancy),
its negation is a meaningful non-integrability statement. The algebraic-residue analogue of
`IsElementaryIntegrableGenuine`. -/
def IsElementaryIntegrableGenuineLrt {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    (Dt a d : DensePoly α) : Prop :=
  ∃ res : LrtResult α, IsGenuineIntegralResultLrt Dt a d res

/-- Any genuine LRT witness makes `a/d` genuinely (broadly) elementary integrable. -/
theorem IsElementaryIntegrableGenuineLrt.of_genuine {α : Type*} [CField α] [CFieldSpec α] [CDiffField α]
    [CDiffFieldSpec α] {Dt a d : DensePoly α} {res : LrtResult α}
    (h : IsGenuineIntegralResultLrt Dt a d res) : IsElementaryIntegrableGenuineLrt Dt a d :=
  ⟨res, h⟩

/-! ### Validation (`native_decide`) -/

namespace DensePoly

/-- The result-level constant-residue guard executes on sparse symbolic residue polynomials. -/
example :
    let ofList : List ℚ → CPoly.SparsePoly ℚ := CPolyEngine.ofCoeffList
    let res : LrtResult ℚ CPoly.SparsePoly := ⟨(ofList [0], ofList [1]), [(ofList [2, 4], [])]⟩
    allResiduesConstantLrt res = true := by
  native_decide

/-- Over `ℚ` (a field of constants, `D ≡ 0`) every reduced part is integrable, so the guard passes:
`∫1/(t²−1)` is accepted (residues `±1/2` are constants). -/
theorem cResidueConstantGuardG_invT2m1 :
    cResidueConstantGuard ([1] : DensePoly ℚ) [1] [-1, 0, 1] = true := by native_decide

/-- The guarded integrator accepts `∫1/(t²−1)` over `ℚ`, returning the same result as the unguarded one
(derived from the guard passing + the `= some` characterization, no `DecidableEq` on `LrtResult` needed). -/
theorem cIntegrateReducedLrtGuardedG_invT2m1 :
    cIntegrateReducedLrtGuarded ([1] : DensePoly ℚ) [1] [-1, 0, 1]
      = some (cIntegrateReducedLrt ([1] : DensePoly ℚ) [1] [-1, 0, 1]) :=
  (cIntegrateReducedLrtGuardedG_eq_some_iff _ _ _).mpr cResidueConstantGuardG_invT2m1

end DensePoly

end DeepWiki.SymbolicIntegration
