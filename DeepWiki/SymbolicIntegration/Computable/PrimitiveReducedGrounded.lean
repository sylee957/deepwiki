import DeepWiki.SymbolicIntegration.Computable.IntegratorCases
import DeepWiki.SymbolicIntegration.Computable.SplitFactorWfCorrect

/-! # Grounding the primitive reduced-part soundness (`hgcdread`/`hDt` are free)

`cIntegrateReducedGWf_primitive_of_splitData`: the reduced-part `IsIntegralResultG` from the
`via_interfaces` theorem, with two of its conditions **discharged**:
* `hgcdread` — the log-argument reads as a gcd — is *exactly* `GcdFFCorrect` (`cLogArgTowerGWf = cgcdFFCoreWf`),
  so it comes free from `[Fact (GcdFFCorrect α)]`;
* `hDt : toPolyG Dt = C w` — free in the guarded primitive regime (`toPolyG Dt = 1 = C 1`, `w = 1`).

So the remaining P3 obligation is only the genuine *rational-residue split data* (`s`, `residueCand`, `hden`
Dstar-splits, `hres` candidates, `hcand` residue-formula, `hnorm`/`hA`/`hDd`/`hdist`/`hcopgcd`/`hproper`),
not the gcd-read or the derivation shape. -/

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG Polynomial Classical
open scoped Differential

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CRischField α]
  [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)]
  [Fact (GcdFFCorrect (α := α))]

omit [CRischField α] in
/-- **Primitive reduced-part soundness, `hgcdread`/`hDt` discharged.** From `[Fact (GcdFFCorrect α)]` and the
guarded-regime `toPolyG Dt = 1`, only the rational-residue split data remains. -/
theorem cIntegrateReducedGWf_primitive_of_splitData
    (Dt a d : CPolyG α) (cands : List α) (s : Finset (CFieldSpec.K α)) (residueCand : CFieldSpec.K α → α)
    (hDt1 : toPolyG Dt = 1)
    (hd0 : toPolyG d ≠ 0) (hpp : (toPolyG d).primPart ≠ 0)
    (hcopgcd : ∀ x ∈ (cSqfreeYunFFGWf d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)),
      (toPolyG (cgcdWf (cmulG (cdivWf d (cpowG x.1 (x.2 + 1)))
          (cmonomialDeriv Dt x.1)) x.1).1).natDegree = 0
      ∧ toPolyG (cgcdWf (cmulG (cdivWf d (cpowG x.1 (x.2 + 1)))
          (cmonomialDeriv Dt x.1)) x.1).1 ≠ 0)
    (hproper : (toPolyG (cHermiteReduceTowerGWf Dt a d).2.1).degree
      < (toPolyG (cHermiteReduceTowerGWf Dt a d).2.2).degree)
    (hden : toPolyG (cHermiteReduceTowerGWf Dt a d).2.2 = Lagrange.nodal s id)
    (hA : (toPolyG (cHermiteReduceTowerGWf Dt a d).2.1).degree < s.card)
    (hnorm : ∀ β ∈ s, (1 : CFieldSpec.K α) ≠ β′)
    (hres : cRationalResiduesGWf Dt (cHermiteReduceTowerGWf Dt a d).2.1
        (cHermiteReduceTowerGWf Dt a d).2.2 cands = s.toList.map residueCand)
    (hDd : ∀ β ∈ s,
      (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β ≠ 0)
    (hdist : ∀ γ ∈ s, ∀ δ ∈ s, γ ≠ δ →
      (toPolyG (cHermiteReduceTowerGWf Dt a d).2.1).eval γ
          / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval γ
        ≠ (toPolyG (cHermiteReduceTowerGWf Dt a d).2.1).eval δ
          / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval δ)
    (hcand : ∀ β ∈ s, CFieldSpec.toK (residueCand β)
      = (toPolyG (cHermiteReduceTowerGWf Dt a d).2.1).eval β
        / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β) :
    IsIntegralResultG Dt a d (cIntegrateReducedGWf Dt a d cands) :=
  cIntegrateReducedGWf_primitive_isIntegralResult_via_interfaces
    (Fact.out : GcdFFCorrect (α := α)) Dt a d cands s 1 residueCand hd0 hpp hcopgcd hproper
    (hDt1.trans (Polynomial.C_1).symm) hden hA hnorm hres hDd hdist hcand
    (fun β _ => (Fact.out : GcdFFCorrect (α := α)) (cHermiteReduceTowerGWf Dt a d).2.2
      (cAmcDdG Dt (cHermiteReduceTowerGWf Dt a d).2.1 (cHermiteReduceTowerGWf Dt a d).2.2
        (residueCand β)))

end DeepWiki.SymbolicIntegration
