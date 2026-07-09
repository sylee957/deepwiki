import DeepWiki.SymbolicIntegration.Engine.IntegratorCases.Defs

/-! # Reduced-stage soundness for concrete integrator cases

Stage-1 reduced-part soundness lemmas assembled from the Hermite and
Rothstein-Trager residue interfaces.
-/

namespace DeepWiki.SymbolicIntegration

open CPoly
open QFunNZG Polynomial
open scoped Differential

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CRischField α]
  [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)]

omit [CRischField α] in
/-- **The reduced normal part is an integral result**, modulo the reduced-stage frontier: from the Hermite
half (`hherm`) and the Rothstein–Trager residue match (`hmatch`), `cIntegrateReduced Dt a d cands`
satisfies the antiderivative predicate. A restatement of
`field_identity_of_cIntegrateReducedG_of_residueMatch` as `IsIntegralResultG`; `hherm`/`hmatch` are the
`cHermiteReduceTower` / RT-residue `native_decide` frontier. It discharges `hNrmField`. -/
theorem cIntegrateReducedG_isIntegralResult (Dt a d : CPoly α) (cands : List α)
    (hherm : towerFractionFieldDerivG Dt
            (amG α (toPoly (cIntegrateReduced Dt a d cands).rational.1)
              / amG α (toPoly (cIntegrateReduced Dt a d cands).rational.2))
          + amG α (toPoly (cHermiteReduceTower Dt a d).2.1)
            / amG α (toPoly (cHermiteReduceTower Dt a d).2.2)
        = amG α (toPoly a) / amG α (toPoly d))
    (hmatch : ((cIntegrateReduced Dt a d cands).logs.map (fun cv =>
          amG α (Polynomial.C (CFieldSpec.toK cv.1))
            * (towerFractionFieldDerivG Dt (amG α (toPoly cv.2)) / amG α (toPoly cv.2)))).sum
        = amG α (toPoly (cHermiteReduceTower Dt a d).2.1)
          / amG α (toPoly (cHermiteReduceTower Dt a d).2.2)) :
    IsIntegralResultG Dt a d (cIntegrateReduced Dt a d cands) := by
  simp only [IsIntegralResultG]
  exact field_identity_of_cIntegrateReducedG_of_residueMatch Dt a d cands hherm hmatch

omit [CRischField α] in
/-- **Reduced-part soundness, consuming the interfaces (Stage-1).** From `LawfulHermiteReduction` (the
cleared Hermite identity) and `LawfulResidueLogPart` (the RT residue match) — the two *abstract* stage
laws — the reduced normal part integrates correctly. This is the assembler consuming its interfaces: the
composition `Hermite ∘ ResidueLogPart = reduced-part soundness`, with no concrete algorithm re-derived. -/
theorem cIntegrateReducedG_isIntegralResult_of_lawful (Dt a d : CPoly α) (cands : List α)
    (hherm : LawfulHermiteReduction Dt a d (CPoly.cHermiteReduceTower Dt a d).1.1
      (CPoly.cHermiteReduceTower Dt a d).1.2 (CPoly.cHermiteReduceTower Dt a d).2.1
      (CPoly.cHermiteReduceTower Dt a d).2.2)
    (hres : LawfulResidueLogPart Dt (CPoly.cHermiteReduceTower Dt a d).2.1
      (CPoly.cHermiteReduceTower Dt a d).2.2 (CPoly.cIntegrateReduced Dt a d cands).logs) :
    IsIntegralResultG Dt a d (CPoly.cIntegrateReduced Dt a d cands) :=
  cIntegrateReducedG_isIntegralResult Dt a d cands hherm.field_identity hres.residue_match

open Classical in
omit [CRischField α] in
/-- **Primitive reduced-part soundness, assembled from the two realizations through the interfaces.** The
end-to-end payoff of the two-stage discipline: `cHermiteReduceTowerG_lawfulHermiteReduction` (Stage 2) and
`cIntegrateReducedG_lawfulResidueLogPart` (Stage 2) fed through `cIntegrateReducedG_isIntegralResult_of_lawful`
(Stage 1) — the reduced normal part integrates correctly with NO concrete algorithm re-derived in the
composition, only the two realization theorems and the abstract law. -/
theorem cIntegrateReducedG_primitive_isIntegralResult_via_interfaces [CharZero (CFieldSpec.K α)]
    (hgcd : GcdFFCorrect (α := α)) (Dt a d : CPoly α) (cands : List α) (s : Finset (CFieldSpec.K α))
    (w : CFieldSpec.K α) (residueCand : CFieldSpec.K α → α)
    (hd0 : toPoly d ≠ 0) (hpp : (toPoly d).primPart ≠ 0)
    (hcopgcd : ∀ x ∈ (CPoly.cSqfreeYunFF d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)),
      (toPoly (CPoly.cgcdWf (CPoly.cmul (CPoly.cdivWf d (CPoly.cpow x.1 (x.2 + 1)))
          (CPoly.cmonomialDeriv Dt x.1)) x.1).1).natDegree = 0
      ∧ toPoly (CPoly.cgcdWf (CPoly.cmul (CPoly.cdivWf d (CPoly.cpow x.1 (x.2 + 1)))
          (CPoly.cmonomialDeriv Dt x.1)) x.1).1 ≠ 0)
    (hproper : (toPoly (CPoly.cHermiteReduceTower Dt a d).2.1).degree
      < (toPoly (CPoly.cHermiteReduceTower Dt a d).2.2).degree)
    (hDt : toPoly Dt = Polynomial.C w)
    (hden : toPoly (CPoly.cHermiteReduceTower Dt a d).2.2 = Lagrange.nodal s id)
    (hA : (toPoly (CPoly.cHermiteReduceTower Dt a d).2.1).degree < s.card)
    (hnorm : ∀ β ∈ s, w ≠ β′)
    (hres : CPoly.cRationalResidues Dt (CPoly.cHermiteReduceTower Dt a d).2.1
        (CPoly.cHermiteReduceTower Dt a d).2.2 cands = s.toList.map residueCand)
    (hDd : ∀ β ∈ s,
      (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β ≠ 0)
    (hdist : ∀ γ ∈ s, ∀ δ ∈ s, γ ≠ δ →
      (toPoly (CPoly.cHermiteReduceTower Dt a d).2.1).eval γ
          / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval γ
        ≠ (toPoly (CPoly.cHermiteReduceTower Dt a d).2.1).eval δ
          / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval δ)
    (hcand : ∀ β ∈ s, CFieldSpec.toK (residueCand β)
      = (toPoly (CPoly.cHermiteReduceTower Dt a d).2.1).eval β
        / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β)
    (hgcdread : ∀ β ∈ s, Associated
      (toPoly (CPoly.cLogArgTower Dt (CPoly.cHermiteReduceTower Dt a d).2.1
          (CPoly.cHermiteReduceTower Dt a d).2.2 (residueCand β)))
      (gcd (toPoly (CPoly.cHermiteReduceTower Dt a d).2.2)
          (toPoly (CPoly.cAmcDd Dt (CPoly.cHermiteReduceTower Dt a d).2.1
            (CPoly.cHermiteReduceTower Dt a d).2.2 (residueCand β))))) :
    IsIntegralResultG Dt a d (CPoly.cIntegrateReduced Dt a d cands) :=
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
    (hgcd : GcdFFCorrect (α := α)) (Dt a d : CPoly α) (cands : List α) (s : Finset (CFieldSpec.K α))
    (b : CFieldSpec.K α) (residueCand : CFieldSpec.K α → α)
    (hd0 : toPoly d ≠ 0) (hpp : (toPoly d).primPart ≠ 0)
    (hcopgcd : ∀ x ∈ (CPoly.cSqfreeYunFF d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)),
      (toPoly (CPoly.cgcdWf (CPoly.cmul (CPoly.cdivWf d (CPoly.cpow x.1 (x.2 + 1)))
          (CPoly.cmonomialDeriv Dt x.1)) x.1).1).natDegree = 0
      ∧ toPoly (CPoly.cgcdWf (CPoly.cmul (CPoly.cdivWf d (CPoly.cpow x.1 (x.2 + 1)))
          (CPoly.cmonomialDeriv Dt x.1)) x.1).1 ≠ 0)
    (hproper : (toPoly (CPoly.cHermiteReduceTower Dt a d).2.1).degree
      < (toPoly (CPoly.cHermiteReduceTower Dt a d).2.2).degree)
    (hb : b ≠ 0) (hDt : toPoly Dt = Polynomial.C b * X)
    (hden : toPoly (CPoly.cHermiteReduceTower Dt a d).2.2 = Lagrange.nodal s id)
    (hA : (toPoly (CPoly.cHermiteReduceTower Dt a d).2.1).degree < s.card)
    (hnorm : ∀ β ∈ s, (Polynomial.C b * X).eval β ≠ β′)
    (hsum : ∑ β ∈ s, (toPoly (CPoly.cHermiteReduceTower Dt a d).2.1).eval β
        / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β = 0)
    (hres : CPoly.cRationalResidues Dt (CPoly.cHermiteReduceTower Dt a d).2.1
        (CPoly.cHermiteReduceTower Dt a d).2.2 cands = s.toList.map residueCand)
    (hDd : ∀ β ∈ s,
      (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β ≠ 0)
    (hdist : ∀ γ ∈ s, ∀ δ ∈ s, γ ≠ δ →
      (toPoly (CPoly.cHermiteReduceTower Dt a d).2.1).eval γ
          / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval γ
        ≠ (toPoly (CPoly.cHermiteReduceTower Dt a d).2.1).eval δ
          / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval δ)
    (hcand : ∀ β ∈ s, CFieldSpec.toK (residueCand β)
      = (toPoly (CPoly.cHermiteReduceTower Dt a d).2.1).eval β
        / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β)
    (hgcdread : ∀ β ∈ s, Associated
      (toPoly (CPoly.cLogArgTower Dt (CPoly.cHermiteReduceTower Dt a d).2.1
          (CPoly.cHermiteReduceTower Dt a d).2.2 (residueCand β)))
      (gcd (toPoly (CPoly.cHermiteReduceTower Dt a d).2.2)
          (toPoly (CPoly.cAmcDd Dt (CPoly.cHermiteReduceTower Dt a d).2.1
            (CPoly.cHermiteReduceTower Dt a d).2.2 (residueCand β))))) :
    IsIntegralResultG Dt a d (CPoly.cIntegrateReduced Dt a d cands) :=
  cIntegrateReducedG_isIntegralResult_of_lawful Dt a d cands
    (cHermiteReduceTowerG_lawfulHermiteReduction hgcd Dt a d hd0 hpp hcopgcd hproper)
    (cIntegrateReducedG_lawfulResidueLogPart_hyperexp Dt a d cands s b residueCand hb hDt hden hA
      hnorm hsum hres hDd hdist hcand hgcdread)

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)]

open QFunNZG in
/-- **Reduced-part soundness, Hermite half discharged.** Given the exact-division relation for the
`cHermiteReduceTower` output (`hexact`) and the RT residue match (`hmatch`), the reduced normal part
integrates correctly: `D(⟦reduced.rational⟧) + logResidueSum reduced.logs = ⟦a/d⟧`. The Hermite `hherm`
is discharged by `hermiteTowerStep_field_identity`. -/
theorem field_identity_of_cIntegrateReducedG_of_residueMatch_of_exact (Dt a d : CPoly α)
    (cands : List α)
    (hd : amG α (toPoly d) ≠ 0)
    (hgden : amG α (toPoly (CPoly.cHermiteReduceTower Dt a d).1.2) ≠ 0)
    (hDstar : amG α (toPoly (CPoly.cHermiteReduceTower Dt a d).2.2) ≠ 0)
    (hexact : amG α (toPoly (CPoly.cHermiteReduceTower Dt a d).2.1)
          * amG α (toPoly (CPoly.cmul d
              (CPoly.cmul (CPoly.cHermiteReduceTower Dt a d).1.2
                (CPoly.cHermiteReduceTower Dt a d).1.2)))
        = amG α (toPoly (CPoly.csub
            (CPoly.cmul a (CPoly.cmul (CPoly.cHermiteReduceTower Dt a d).1.2
              (CPoly.cHermiteReduceTower Dt a d).1.2))
            (CPoly.cmul d (CPoly.csub
              (CPoly.cmul (CPoly.cmonomialDeriv Dt (CPoly.cHermiteReduceTower Dt a d).1.1)
                (CPoly.cHermiteReduceTower Dt a d).1.2)
              (CPoly.cmul (CPoly.cHermiteReduceTower Dt a d).1.1
                (CPoly.cmonomialDeriv Dt (CPoly.cHermiteReduceTower Dt a d).1.2))))))
          * amG α (toPoly (CPoly.cHermiteReduceTower Dt a d).2.2))
    (hmatch : ((CPoly.cIntegrateReduced Dt a d cands).logs.map (fun cv =>
          amG α (Polynomial.C (CFieldSpec.toK cv.1))
            * (towerFractionFieldDerivG Dt (amG α (toPoly cv.2)) / amG α (toPoly cv.2)))).sum
        = amG α (toPoly (CPoly.cHermiteReduceTower Dt a d).2.1)
          / amG α (toPoly (CPoly.cHermiteReduceTower Dt a d).2.2)) :
    towerFractionFieldDerivG Dt
        (amG α (toPoly (CPoly.cIntegrateReduced Dt a d cands).rational.1)
          / amG α (toPoly (CPoly.cIntegrateReduced Dt a d cands).rational.2))
        + logResidueSumG Dt (CPoly.cIntegrateReduced Dt a d cands).logs
      = amG α (toPoly a) / amG α (toPoly d) :=
  field_identity_of_cIntegrateReducedG_of_residueMatch Dt a d cands
    (hermiteTowerStep_field_identity Dt (CPoly.cHermiteReduceTower Dt a d).1.1
      (CPoly.cHermiteReduceTower Dt a d).1.2 a d (CPoly.cHermiteReduceTower Dt a d).2.1
      (CPoly.cHermiteReduceTower Dt a d).2.2 hd hgden hDstar hexact)
    hmatch

end DeepWiki.SymbolicIntegration
