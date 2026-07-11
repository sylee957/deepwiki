import DeepWiki.SymbolicIntegration.Engine.IntegratorCases.Defs

/-! # Reduced-stage soundness for concrete integrator cases

Stage-1 reduced-part soundness lemmas assembled from the Hermite and
Rothstein-Trager residue interfaces.
-/

namespace DeepWiki.SymbolicIntegration

open DensePoly
open CFrac Polynomial
open scoped Differential

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CRischField α]
  [Algebra ℚ (CFieldSpec.K α)]

omit [CRischField α] in
/-- **The reduced normal part is an integral result**, modulo the reduced-stage frontier: from the Hermite
half (`hherm`) and the Rothstein–Trager residue match (`hmatch`), `cIntegrateReduced Dt a d cands`
satisfies the antiderivative predicate. A restatement of
`field_identity_of_cIntegrateReducedG_of_residueMatch` as `IsIntegralResult`; `hherm`/`hmatch` are the
`cHermiteReduceTower` / RT-residue `native_decide` frontier. It discharges `hNrmField`. -/
private theorem cIntegrateReducedG_isIntegralResult [CPolySquarefree DensePoly α]
    [CPolyGcd DensePoly α] [CPolyResultant DensePoly]
    (Dt a d : DensePoly α) (cands : List α)
    (hherm : towerFractionFieldDeriv Dt
            (am α (toPoly (cIntegrateReduced Dt a d cands).rational.1)
              / am α (toPoly (cIntegrateReduced Dt a d cands).rational.2))
          + am α (toPoly (cHermiteReduceTower Dt a d).2.1)
            / am α (toPoly (cHermiteReduceTower Dt a d).2.2)
        = am α (toPoly a) / am α (toPoly d))
    (hmatch : ((cIntegrateReduced Dt a d cands).logs.map (fun cv =>
          am α (Polynomial.C (CFieldSpec.toK cv.1))
            * (towerFractionFieldDeriv Dt (am α (toPoly cv.2)) / am α (toPoly cv.2)))).sum
        = am α (toPoly (cHermiteReduceTower Dt a d).2.1)
          / am α (toPoly (cHermiteReduceTower Dt a d).2.2)) :
    IsIntegralResult Dt a d (cIntegrateReduced Dt a d cands) := by
  simp only [IsIntegralResult]
  exact field_identity_of_cIntegrateReducedG_of_residueMatch Dt a d cands hherm hmatch

omit [CRischField α] in
/-- **Reduced-part soundness, consuming the interfaces (Stage-1).** From `LawfulHermiteReduction` (the
cleared Hermite identity) and `LawfulResidueLogPart` (the RT residue match) — the two *abstract* stage
laws — the reduced normal part integrates correctly. This is the assembler consuming its interfaces: the
composition `Hermite ∘ ResidueLogPart = reduced-part soundness`, with no concrete algorithm re-derived. -/
private theorem cIntegrateReducedG_isIntegralResult_of_lawful [CPolySquarefree DensePoly α]
    [CPolyGcd DensePoly α] [CPolyResultant DensePoly]
    (Dt a d : DensePoly α) (cands : List α)
    (hherm : LawfulHermiteReduction Dt a d (DensePoly.cHermiteReduceTower Dt a d).1.1
      (DensePoly.cHermiteReduceTower Dt a d).1.2 (DensePoly.cHermiteReduceTower Dt a d).2.1
      (DensePoly.cHermiteReduceTower Dt a d).2.2)
    (hres : LawfulResidueLogPart Dt (DensePoly.cHermiteReduceTower Dt a d).2.1
      (DensePoly.cHermiteReduceTower Dt a d).2.2 (DensePoly.cIntegrateReduced Dt a d cands).logs) :
    IsIntegralResult Dt a d (DensePoly.cIntegrateReduced Dt a d cands) :=
  cIntegrateReducedG_isIntegralResult Dt a d cands
    (by simpa only [cIntegrateReduced, towerFractionFieldDerivP, towerFractionFieldDeriv, toPoly_list_eq] using
      hherm.field_identity)
    (by simpa only [towerFractionFieldDerivP, towerFractionFieldDeriv, toPoly_list_eq] using
      hres.residue_match)

open Classical in
omit [CRischField α] in
/-- **Primitive reduced-part soundness, assembled from the two realizations through the interfaces.** The
end-to-end payoff of the two-stage discipline: `cHermiteReduceTowerG_lawfulHermiteReduction` (Stage 2) and
`cIntegrateReducedG_lawfulResidueLogPart` (Stage 2) fed through `cIntegrateReducedG_isIntegralResult_of_lawful`
(Stage 1) — the reduced normal part integrates correctly with NO concrete algorithm re-derived in the
composition, only the two realization theorems and the abstract law. -/
theorem cIntegrateReducedG_primitive_isIntegralResult_via_interfaces [CharZero (CFieldSpec.K α)]
    [CFracGcdCoreWf α]
    (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) (Dt a d : DensePoly α) (cands : List α) (s : Finset (CFieldSpec.K α))
    (w : CFieldSpec.K α) (residueCand : CFieldSpec.K α → α)
    (hd0 : toPoly d ≠ 0) (hpp : (toPoly d).primPart ≠ 0)
    (hcopgcd : ∀ x ∈ (DensePoly.cSqfreeYunFF d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)),
      (toPoly (CPolyEuclidean.gcdExt (DensePoly.cmul (CPolyEuclidean.div d (DensePoly.cpow x.1 (x.2 + 1)))
          (CPolyEngine.monomialDeriv Dt x.1)) x.1).1).natDegree = 0
      ∧ toPoly (CPolyEuclidean.gcdExt (DensePoly.cmul (CPolyEuclidean.div d (DensePoly.cpow x.1 (x.2 + 1)))
          (CPolyEngine.monomialDeriv Dt x.1)) x.1).1 ≠ 0)
    (hproper : (toPoly (DensePoly.cHermiteReduceTower Dt a d).2.1).degree
      < (toPoly (DensePoly.cHermiteReduceTower Dt a d).2.2).degree)
    (hDt : toPoly Dt = Polynomial.C w)
    (hden : toPoly (DensePoly.cHermiteReduceTower Dt a d).2.2 = Lagrange.nodal s id)
    (hA : (toPoly (DensePoly.cHermiteReduceTower Dt a d).2.1).degree < s.card)
    (hnorm : ∀ β ∈ s, w ≠ β′)
    (hres : DensePoly.cRationalResidues Dt (DensePoly.cHermiteReduceTower Dt a d).2.1
        (DensePoly.cHermiteReduceTower Dt a d).2.2 cands = s.toList.map residueCand)
    (hDd : ∀ β ∈ s,
      (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β ≠ 0)
    (hdist : ∀ γ ∈ s, ∀ δ ∈ s, γ ≠ δ →
      (toPoly (DensePoly.cHermiteReduceTower Dt a d).2.1).eval γ
          / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval γ
        ≠ (toPoly (DensePoly.cHermiteReduceTower Dt a d).2.1).eval δ
          / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval δ)
    (hcand : ∀ β ∈ s, CFieldSpec.toK (residueCand β)
      = (toPoly (DensePoly.cHermiteReduceTower Dt a d).2.1).eval β
        / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β)
    (hgcdread : ∀ β ∈ s, Associated
      (toPoly (DensePoly.cLogArgTower Dt (DensePoly.cHermiteReduceTower Dt a d).2.1
          (DensePoly.cHermiteReduceTower Dt a d).2.2 (residueCand β)))
      (gcd (toPoly (DensePoly.cHermiteReduceTower Dt a d).2.2)
          (toPoly (DensePoly.cAmcDd Dt (DensePoly.cHermiteReduceTower Dt a d).2.1
            (DensePoly.cHermiteReduceTower Dt a d).2.2 (residueCand β))))) :
    IsIntegralResult Dt a d (DensePoly.cIntegrateReduced Dt a d cands) :=
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
    [CFracGcdCoreWf α]
    (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) (Dt a d : DensePoly α) (cands : List α) (s : Finset (CFieldSpec.K α))
    (b : CFieldSpec.K α) (residueCand : CFieldSpec.K α → α)
    (hd0 : toPoly d ≠ 0) (hpp : (toPoly d).primPart ≠ 0)
    (hcopgcd : ∀ x ∈ (DensePoly.cSqfreeYunFF d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)),
      (toPoly (CPolyEuclidean.gcdExt (DensePoly.cmul (CPolyEuclidean.div d (DensePoly.cpow x.1 (x.2 + 1)))
          (CPolyEngine.monomialDeriv Dt x.1)) x.1).1).natDegree = 0
      ∧ toPoly (CPolyEuclidean.gcdExt (DensePoly.cmul (CPolyEuclidean.div d (DensePoly.cpow x.1 (x.2 + 1)))
          (CPolyEngine.monomialDeriv Dt x.1)) x.1).1 ≠ 0)
    (hproper : (toPoly (DensePoly.cHermiteReduceTower Dt a d).2.1).degree
      < (toPoly (DensePoly.cHermiteReduceTower Dt a d).2.2).degree)
    (hb : b ≠ 0) (hDt : toPoly Dt = Polynomial.C b * X)
    (hden : toPoly (DensePoly.cHermiteReduceTower Dt a d).2.2 = Lagrange.nodal s id)
    (hA : (toPoly (DensePoly.cHermiteReduceTower Dt a d).2.1).degree < s.card)
    (hnorm : ∀ β ∈ s, (Polynomial.C b * X).eval β ≠ β′)
    (hsum : ∑ β ∈ s, (toPoly (DensePoly.cHermiteReduceTower Dt a d).2.1).eval β
        / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β = 0)
    (hres : DensePoly.cRationalResidues Dt (DensePoly.cHermiteReduceTower Dt a d).2.1
        (DensePoly.cHermiteReduceTower Dt a d).2.2 cands = s.toList.map residueCand)
    (hDd : ∀ β ∈ s,
      (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β ≠ 0)
    (hdist : ∀ γ ∈ s, ∀ δ ∈ s, γ ≠ δ →
      (toPoly (DensePoly.cHermiteReduceTower Dt a d).2.1).eval γ
          / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval γ
        ≠ (toPoly (DensePoly.cHermiteReduceTower Dt a d).2.1).eval δ
          / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval δ)
    (hcand : ∀ β ∈ s, CFieldSpec.toK (residueCand β)
      = (toPoly (DensePoly.cHermiteReduceTower Dt a d).2.1).eval β
        / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β)
    (hgcdread : ∀ β ∈ s, Associated
      (toPoly (DensePoly.cLogArgTower Dt (DensePoly.cHermiteReduceTower Dt a d).2.1
          (DensePoly.cHermiteReduceTower Dt a d).2.2 (residueCand β)))
      (gcd (toPoly (DensePoly.cHermiteReduceTower Dt a d).2.2)
          (toPoly (DensePoly.cAmcDd Dt (DensePoly.cHermiteReduceTower Dt a d).2.1
            (DensePoly.cHermiteReduceTower Dt a d).2.2 (residueCand β))))) :
    IsIntegralResult Dt a d (DensePoly.cIntegrateReduced Dt a d cands) :=
  cIntegrateReducedG_isIntegralResult_of_lawful Dt a d cands
    (cHermiteReduceTowerG_lawfulHermiteReduction hgcd Dt a d hd0 hpp hcopgcd hproper)
    (cIntegrateReducedG_lawfulResidueLogPart_hyperexp Dt a d cands s b residueCand hb hDt hden hA
      hnorm hsum hres hDd hdist hcand hgcdread)

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)]

open CFrac in
/-- **Reduced-part soundness, Hermite half discharged.** Given the exact-division relation for the
`cHermiteReduceTower` output (`hexact`) and the RT residue match (`hmatch`), the reduced normal part
integrates correctly: `D(⟦reduced.rational⟧) + logResidueSum reduced.logs = ⟦a/d⟧`. The Hermite `hherm`
is discharged by `hermiteTowerStep_field_identity`. -/
theorem field_identity_of_cIntegrateReducedG_of_residueMatch_of_exact (Dt a d : DensePoly α)
    (cands : List α)
    (hd : am α (toPoly d) ≠ 0)
    (hgden : am α (toPoly (DensePoly.cHermiteReduceTower Dt a d).1.2) ≠ 0)
    (hDstar : am α (toPoly (DensePoly.cHermiteReduceTower Dt a d).2.2) ≠ 0)
    (hexact : am α (toPoly (DensePoly.cHermiteReduceTower Dt a d).2.1)
          * am α (toPoly (DensePoly.cmul d
              (DensePoly.cmul (DensePoly.cHermiteReduceTower Dt a d).1.2
                (DensePoly.cHermiteReduceTower Dt a d).1.2)))
        = am α (toPoly (DensePoly.csub
            (DensePoly.cmul a (DensePoly.cmul (DensePoly.cHermiteReduceTower Dt a d).1.2
              (DensePoly.cHermiteReduceTower Dt a d).1.2))
            (DensePoly.cmul d (DensePoly.csub
              (DensePoly.cmul (CPolyEngine.monomialDeriv Dt (DensePoly.cHermiteReduceTower Dt a d).1.1)
                (DensePoly.cHermiteReduceTower Dt a d).1.2)
              (DensePoly.cmul (DensePoly.cHermiteReduceTower Dt a d).1.1
                (CPolyEngine.monomialDeriv Dt (DensePoly.cHermiteReduceTower Dt a d).1.2))))))
          * am α (toPoly (DensePoly.cHermiteReduceTower Dt a d).2.2))
    (hmatch : ((DensePoly.cIntegrateReduced Dt a d cands).logs.map (fun cv =>
          am α (Polynomial.C (CFieldSpec.toK cv.1))
            * (towerFractionFieldDeriv Dt (am α (toPoly cv.2)) / am α (toPoly cv.2)))).sum
        = am α (toPoly (DensePoly.cHermiteReduceTower Dt a d).2.1)
          / am α (toPoly (DensePoly.cHermiteReduceTower Dt a d).2.2)) :
    towerFractionFieldDeriv Dt
        (am α (toPoly (DensePoly.cIntegrateReduced Dt a d cands).rational.1)
          / am α (toPoly (DensePoly.cIntegrateReduced Dt a d cands).rational.2))
        + logResidueSum Dt (DensePoly.cIntegrateReduced Dt a d cands).logs
      = am α (toPoly a) / am α (toPoly d) :=
  field_identity_of_cIntegrateReducedG_of_residueMatch Dt a d cands
    (hermiteTowerStep_field_identity Dt (DensePoly.cHermiteReduceTower Dt a d).1.1
      (DensePoly.cHermiteReduceTower Dt a d).1.2 a d (DensePoly.cHermiteReduceTower Dt a d).2.1
      (DensePoly.cHermiteReduceTower Dt a d).2.2 hd hgden hDstar hexact)
    hmatch

end DeepWiki.SymbolicIntegration
