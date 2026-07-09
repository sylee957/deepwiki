import DeepWiki.SymbolicIntegration.Engine.IntegratorCases.Defs

/-! # Reduced-stage soundness for concrete integrator cases

Stage-1 reduced-part soundness lemmas assembled from the Hermite and
Rothstein-Trager residue interfaces.
-/

namespace DeepWiki.SymbolicIntegration

open Compute
open CPolyG
open QFunNZG Polynomial
open scoped Differential

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CRischField α]
  [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)]

omit [CRischField α] in
/-- **The reduced normal part is an integral result**, modulo the reduced-stage frontier: from the Hermite
half (`hherm`) and the Rothstein–Trager residue match (`hmatch`), `cIntegrateReducedG Dt a d cands`
satisfies the antiderivative predicate. A restatement of
`field_identity_of_cIntegrateReducedG_of_residueMatch` as `IsIntegralResultG`; `hherm`/`hmatch` are the
`cHermiteReduceTowerG` / RT-residue `native_decide` frontier. It discharges `hNrmField`. -/
theorem cIntegrateReducedG_isIntegralResult (Dt a d : CPolyG α) (cands : List α)
    (hherm : towerFractionFieldDerivG Dt
            (amG α (toPolyG (cIntegrateReducedG Dt a d cands).rational.1)
              / amG α (toPolyG (cIntegrateReducedG Dt a d cands).rational.2))
          + amG α (toPolyG (cHermiteReduceTowerG Dt a d).2.1)
            / amG α (toPolyG (cHermiteReduceTowerG Dt a d).2.2)
        = amG α (toPolyG a) / amG α (toPolyG d))
    (hmatch : ((cIntegrateReducedG Dt a d cands).logs.map (fun cv =>
          amG α (Polynomial.C (CFieldSpec.toK cv.1))
            * (towerFractionFieldDerivG Dt (amG α (toPolyG cv.2)) / amG α (toPolyG cv.2)))).sum
        = amG α (toPolyG (cHermiteReduceTowerG Dt a d).2.1)
          / amG α (toPolyG (cHermiteReduceTowerG Dt a d).2.2)) :
    IsIntegralResultG Dt a d (cIntegrateReducedG Dt a d cands) := by
  simp only [IsIntegralResultG]
  exact field_identity_of_cIntegrateReducedG_of_residueMatch Dt a d cands hherm hmatch

omit [CRischField α] in
/-- **Reduced-part soundness, consuming the interfaces (Stage-1).** From `LawfulHermiteReduction` (the
cleared Hermite identity) and `LawfulResidueLogPart` (the RT residue match) — the two *abstract* stage
laws — the reduced normal part integrates correctly. This is the assembler consuming its interfaces: the
composition `Hermite ∘ ResidueLogPart = reduced-part soundness`, with no concrete algorithm re-derived. -/
theorem cIntegrateReducedG_isIntegralResult_of_lawful (Dt a d : CPolyG α) (cands : List α)
    (hherm : LawfulHermiteReduction Dt a d (CPolyG.cHermiteReduceTowerG Dt a d).1.1
      (CPolyG.cHermiteReduceTowerG Dt a d).1.2 (CPolyG.cHermiteReduceTowerG Dt a d).2.1
      (CPolyG.cHermiteReduceTowerG Dt a d).2.2)
    (hres : LawfulResidueLogPart Dt (CPolyG.cHermiteReduceTowerG Dt a d).2.1
      (CPolyG.cHermiteReduceTowerG Dt a d).2.2 (CPolyG.cIntegrateReducedG Dt a d cands).logs) :
    IsIntegralResultG Dt a d (CPolyG.cIntegrateReducedG Dt a d cands) :=
  cIntegrateReducedG_isIntegralResult Dt a d cands hherm.field_identity hres.residue_match

open Classical in
omit [CRischField α] in
/-- **Primitive reduced-part soundness, assembled from the two realizations through the interfaces.** The
end-to-end payoff of the two-stage discipline: `cHermiteReduceTowerG_lawfulHermiteReduction` (Stage 2) and
`cIntegrateReducedG_lawfulResidueLogPart` (Stage 2) fed through `cIntegrateReducedG_isIntegralResult_of_lawful`
(Stage 1) — the reduced normal part integrates correctly with NO concrete algorithm re-derived in the
composition, only the two realization theorems and the abstract law. -/
theorem cIntegrateReducedG_primitive_isIntegralResult_via_interfaces [CharZero (CFieldSpec.K α)]
    (hgcd : GcdFFCorrect (α := α)) (Dt a d : CPolyG α) (cands : List α) (s : Finset (CFieldSpec.K α))
    (w : CFieldSpec.K α) (residueCand : CFieldSpec.K α → α)
    (hd0 : toPolyG d ≠ 0) (hpp : (toPolyG d).primPart ≠ 0)
    (hcopgcd : ∀ x ∈ (CPolyG.cSqfreeYunFFG d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)),
      (toPolyG (CPolyG.cgcdWf (CPolyG.cmulG (CPolyG.cdivWf d (CPolyG.cpowG x.1 (x.2 + 1)))
          (CPolyG.cmonomialDeriv Dt x.1)) x.1).1).natDegree = 0
      ∧ toPolyG (CPolyG.cgcdWf (CPolyG.cmulG (CPolyG.cdivWf d (CPolyG.cpowG x.1 (x.2 + 1)))
          (CPolyG.cmonomialDeriv Dt x.1)) x.1).1 ≠ 0)
    (hproper : (toPolyG (CPolyG.cHermiteReduceTowerG Dt a d).2.1).degree
      < (toPolyG (CPolyG.cHermiteReduceTowerG Dt a d).2.2).degree)
    (hDt : toPolyG Dt = Polynomial.C w)
    (hden : toPolyG (CPolyG.cHermiteReduceTowerG Dt a d).2.2 = Lagrange.nodal s id)
    (hA : (toPolyG (CPolyG.cHermiteReduceTowerG Dt a d).2.1).degree < s.card)
    (hnorm : ∀ β ∈ s, w ≠ β′)
    (hres : CPolyG.cRationalResiduesG Dt (CPolyG.cHermiteReduceTowerG Dt a d).2.1
        (CPolyG.cHermiteReduceTowerG Dt a d).2.2 cands = s.toList.map residueCand)
    (hDd : ∀ β ∈ s,
      (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β ≠ 0)
    (hdist : ∀ γ ∈ s, ∀ δ ∈ s, γ ≠ δ →
      (toPolyG (CPolyG.cHermiteReduceTowerG Dt a d).2.1).eval γ
          / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval γ
        ≠ (toPolyG (CPolyG.cHermiteReduceTowerG Dt a d).2.1).eval δ
          / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval δ)
    (hcand : ∀ β ∈ s, CFieldSpec.toK (residueCand β)
      = (toPolyG (CPolyG.cHermiteReduceTowerG Dt a d).2.1).eval β
        / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β)
    (hgcdread : ∀ β ∈ s, Associated
      (toPolyG (CPolyG.cLogArgTowerG Dt (CPolyG.cHermiteReduceTowerG Dt a d).2.1
          (CPolyG.cHermiteReduceTowerG Dt a d).2.2 (residueCand β)))
      (gcd (toPolyG (CPolyG.cHermiteReduceTowerG Dt a d).2.2)
          (toPolyG (CPolyG.cAmcDdG Dt (CPolyG.cHermiteReduceTowerG Dt a d).2.1
            (CPolyG.cHermiteReduceTowerG Dt a d).2.2 (residueCand β))))) :
    IsIntegralResultG Dt a d (CPolyG.cIntegrateReducedG Dt a d cands) :=
  cIntegrateReducedG_isIntegralResult_of_lawful Dt a d cands
    (cHermiteReduceTowerG_lawfulHermiteReduction hgcd Dt a d hd0 hpp hcopgcd hproper)
    (cIntegrateReducedG_lawfulResidueLogPart Dt a d cands s w residueCand hDt hden hA hnorm hres
      hDd hdist hcand hgcdread)

open Classical in
omit [CRischField α] in
/-- **Hyperexp reduced-part soundness, assembled from the two realizations through the interfaces.** The
hyperexponential analogue of `…primitive_isIntegralResult_via_interfaces` — same Stage-1 composition, with
the hyperexp `ResidueLogPart` realization (integrability witness `hsum : ∑ c = 0`). -/
theorem cIntegrateReducedG_hyperexp_isIntegralResult_via_interfaces [CharZero (CFieldSpec.K α)]
    (hgcd : GcdFFCorrect (α := α)) (Dt a d : CPolyG α) (cands : List α) (s : Finset (CFieldSpec.K α))
    (b : CFieldSpec.K α) (residueCand : CFieldSpec.K α → α)
    (hd0 : toPolyG d ≠ 0) (hpp : (toPolyG d).primPart ≠ 0)
    (hcopgcd : ∀ x ∈ (CPolyG.cSqfreeYunFFG d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)),
      (toPolyG (CPolyG.cgcdWf (CPolyG.cmulG (CPolyG.cdivWf d (CPolyG.cpowG x.1 (x.2 + 1)))
          (CPolyG.cmonomialDeriv Dt x.1)) x.1).1).natDegree = 0
      ∧ toPolyG (CPolyG.cgcdWf (CPolyG.cmulG (CPolyG.cdivWf d (CPolyG.cpowG x.1 (x.2 + 1)))
          (CPolyG.cmonomialDeriv Dt x.1)) x.1).1 ≠ 0)
    (hproper : (toPolyG (CPolyG.cHermiteReduceTowerG Dt a d).2.1).degree
      < (toPolyG (CPolyG.cHermiteReduceTowerG Dt a d).2.2).degree)
    (hb : b ≠ 0) (hDt : toPolyG Dt = Polynomial.C b * X)
    (hden : toPolyG (CPolyG.cHermiteReduceTowerG Dt a d).2.2 = Lagrange.nodal s id)
    (hA : (toPolyG (CPolyG.cHermiteReduceTowerG Dt a d).2.1).degree < s.card)
    (hnorm : ∀ β ∈ s, (Polynomial.C b * X).eval β ≠ β′)
    (hsum : ∑ β ∈ s, (toPolyG (CPolyG.cHermiteReduceTowerG Dt a d).2.1).eval β
        / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β = 0)
    (hres : CPolyG.cRationalResiduesG Dt (CPolyG.cHermiteReduceTowerG Dt a d).2.1
        (CPolyG.cHermiteReduceTowerG Dt a d).2.2 cands = s.toList.map residueCand)
    (hDd : ∀ β ∈ s,
      (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β ≠ 0)
    (hdist : ∀ γ ∈ s, ∀ δ ∈ s, γ ≠ δ →
      (toPolyG (CPolyG.cHermiteReduceTowerG Dt a d).2.1).eval γ
          / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval γ
        ≠ (toPolyG (CPolyG.cHermiteReduceTowerG Dt a d).2.1).eval δ
          / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval δ)
    (hcand : ∀ β ∈ s, CFieldSpec.toK (residueCand β)
      = (toPolyG (CPolyG.cHermiteReduceTowerG Dt a d).2.1).eval β
        / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β)
    (hgcdread : ∀ β ∈ s, Associated
      (toPolyG (CPolyG.cLogArgTowerG Dt (CPolyG.cHermiteReduceTowerG Dt a d).2.1
          (CPolyG.cHermiteReduceTowerG Dt a d).2.2 (residueCand β)))
      (gcd (toPolyG (CPolyG.cHermiteReduceTowerG Dt a d).2.2)
          (toPolyG (CPolyG.cAmcDdG Dt (CPolyG.cHermiteReduceTowerG Dt a d).2.1
            (CPolyG.cHermiteReduceTowerG Dt a d).2.2 (residueCand β))))) :
    IsIntegralResultG Dt a d (CPolyG.cIntegrateReducedG Dt a d cands) :=
  cIntegrateReducedG_isIntegralResult_of_lawful Dt a d cands
    (cHermiteReduceTowerG_lawfulHermiteReduction hgcd Dt a d hd0 hpp hcopgcd hproper)
    (cIntegrateReducedG_lawfulResidueLogPart_hyperexp Dt a d cands s b residueCand hb hDt hden hA
      hnorm hsum hres hDd hdist hcand hgcdread)

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)]

open QFunNZG in
/-- **Reduced-part soundness, Hermite half discharged.** Given the exact-division relation for the
`cHermiteReduceTowerG` output (`hexact`) and the RT residue match (`hmatch`), the reduced normal part
integrates correctly: `D(⟦reduced.rational⟧) + logResidueSum reduced.logs = ⟦a/d⟧`. The Hermite `hherm`
is discharged by `hermiteTowerStep_field_identity`. -/
theorem field_identity_of_cIntegrateReducedG_of_residueMatch_of_exact (Dt a d : CPolyG α)
    (cands : List α)
    (hd : amG α (toPolyG d) ≠ 0)
    (hgden : amG α (toPolyG (CPolyG.cHermiteReduceTowerG Dt a d).1.2) ≠ 0)
    (hDstar : amG α (toPolyG (CPolyG.cHermiteReduceTowerG Dt a d).2.2) ≠ 0)
    (hexact : amG α (toPolyG (CPolyG.cHermiteReduceTowerG Dt a d).2.1)
          * amG α (toPolyG (CPolyG.cmulG d
              (CPolyG.cmulG (CPolyG.cHermiteReduceTowerG Dt a d).1.2
                (CPolyG.cHermiteReduceTowerG Dt a d).1.2)))
        = amG α (toPolyG (CPolyG.csubG
            (CPolyG.cmulG a (CPolyG.cmulG (CPolyG.cHermiteReduceTowerG Dt a d).1.2
              (CPolyG.cHermiteReduceTowerG Dt a d).1.2))
            (CPolyG.cmulG d (CPolyG.csubG
              (CPolyG.cmulG (CPolyG.cmonomialDeriv Dt (CPolyG.cHermiteReduceTowerG Dt a d).1.1)
                (CPolyG.cHermiteReduceTowerG Dt a d).1.2)
              (CPolyG.cmulG (CPolyG.cHermiteReduceTowerG Dt a d).1.1
                (CPolyG.cmonomialDeriv Dt (CPolyG.cHermiteReduceTowerG Dt a d).1.2))))))
          * amG α (toPolyG (CPolyG.cHermiteReduceTowerG Dt a d).2.2))
    (hmatch : ((CPolyG.cIntegrateReducedG Dt a d cands).logs.map (fun cv =>
          amG α (Polynomial.C (CFieldSpec.toK cv.1))
            * (towerFractionFieldDerivG Dt (amG α (toPolyG cv.2)) / amG α (toPolyG cv.2)))).sum
        = amG α (toPolyG (CPolyG.cHermiteReduceTowerG Dt a d).2.1)
          / amG α (toPolyG (CPolyG.cHermiteReduceTowerG Dt a d).2.2)) :
    towerFractionFieldDerivG Dt
        (amG α (toPolyG (CPolyG.cIntegrateReducedG Dt a d cands).rational.1)
          / amG α (toPolyG (CPolyG.cIntegrateReducedG Dt a d cands).rational.2))
        + logResidueSumG Dt (CPolyG.cIntegrateReducedG Dt a d cands).logs
      = amG α (toPolyG a) / amG α (toPolyG d) :=
  field_identity_of_cIntegrateReducedG_of_residueMatch Dt a d cands
    (hermiteTowerStep_field_identity Dt (CPolyG.cHermiteReduceTowerG Dt a d).1.1
      (CPolyG.cHermiteReduceTowerG Dt a d).1.2 a d (CPolyG.cHermiteReduceTowerG Dt a d).2.1
      (CPolyG.cHermiteReduceTowerG Dt a d).2.2 hd hgden hDstar hexact)
    hmatch

end DeepWiki.SymbolicIntegration
