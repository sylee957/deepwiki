import DeepWiki.SymbolicIntegration.Engine.NormalPartSoundness
import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.RothsteinTrager.LogResidueTower

/-! # The Rothstein–Trager residue identity over the transcendental tower

Transports the algebraic Rothstein–Trager residue identity to the transcendental tower with the
monomial derivation `D = cmonomialDeriv Dt`.  Delivers: the residue resultant's roots are the residues
(`roots_residueResultantTowerG_eq_residues`); the log-argument gcd is the residue's linear factor
(`residue_gcd_eq_linear_factor`); the `logResidueSumG` reading as a monomial log-derivative sum; and,
given the residue match, `logResidueSumG = a/d`, assembled with the Hermite half into the fuel-free
reduced-case field identity `D(g) + logResidueSumG = a/d` with no engine certificate. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open CPoly QFunNZG

/-! ### The `logResidueSumG` reading as a monomial log-derivative sum -/

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

omit [Algebra ℚ (CFieldSpec.K α)] in
/-- `toPoly (cAmcDd Dt a d c) = toPoly a − C(toK c)·implicitDeriv (toPoly Dt) (toPoly d)`. -/
@[denote] theorem toPolyG_cAmcDdG (Dt a d : CPoly α) (c : α) :
    toPoly (cAmcDd Dt a d c)
      = toPoly a - Polynomial.C (CFieldSpec.toK c)
          * Differential.implicitDeriv (toPoly Dt) (toPoly d) := by
  rw [cAmcDd]
  simp only [denote]

/-! ### The RT residue identity: `logResidueSumG = a/d` from the residue match -/

/-- `logResidueSumG = a/d` from the residue match: given the log-derivative sum equals `amG a/amG d`,
so does `logResidueSumG Dt logs`. -/
theorem logResidueSumG_eq_of_residue_match (Dt : CPoly α) (a d : CPoly α)
    (logs : List (α × CPoly α))
    (hmatch : (logs.map (fun cv =>
          amG α (Polynomial.C (CFieldSpec.toK cv.1))
            * (towerFractionFieldDerivG Dt (amG α (toPoly cv.2)) / amG α (toPoly cv.2)))).sum
        = amG α (toPoly a) / amG α (toPoly d)) :
    logResidueSumG Dt logs = amG α (toPoly a) / amG α (toPoly d) := by
  rw [logResidueSumG_eq_logDeriv_sum Dt logs]
  exact hmatch

/-! ### Assembly: the reduced-case field identity from the Hermite half + the RT residue match -/

/-- The reduced-case field identity: given the Hermite half `D(g) + h = a/d` and the RT residue match
(the residue logs' log-derivative sum equals `h`), `D(g) + logResidueSumG = a/d`. -/
theorem field_identity_of_reducedG_of_residueMatch (Dt : CPoly α)
    (gnum gden hNum hDen anum aden : CPoly α) (logs : List (α × CPoly α))
    (hherm : towerFractionFieldDerivG Dt (amG α (toPoly gnum) / amG α (toPoly gden))
          + amG α (toPoly hNum) / amG α (toPoly hDen)
        = amG α (toPoly anum) / amG α (toPoly aden))
    (hmatch : (logs.map (fun cv =>
          amG α (Polynomial.C (CFieldSpec.toK cv.1))
            * (towerFractionFieldDerivG Dt (amG α (toPoly cv.2)) / amG α (toPoly cv.2)))).sum
        = amG α (toPoly hNum) / amG α (toPoly hDen)) :
    towerFractionFieldDerivG Dt (amG α (toPoly gnum) / amG α (toPoly gden))
        + logResidueSumG Dt logs
      = amG α (toPoly anum) / amG α (toPoly aden) := by
  rw [logResidueSumG_eq_of_residue_match Dt hNum hDen logs hmatch, hherm]

/-! ### The fuel-free reduced-case one-shot for `cIntegrateReduced`

Reads `cIntegrateReduced`'s fields into `field_identity_of_reducedG_of_residueMatch`. -/

variable [CFracGcdCoreWf α]

/-- The fuel-free reduced-case one-shot: for `res = cIntegrateReduced Dt a d cands`, given the
Hermite half and the RT residue match, `D(g) + logResidueSumG Dt res.logs = a/d`. -/
theorem field_identity_of_cIntegrateReducedG_of_residueMatch (Dt : CPoly α)
    (a d : CPoly α) (cands : List α)
    (hherm : towerFractionFieldDerivG Dt
            (amG α (toPoly (CPoly.cIntegrateReduced Dt a d cands).rational.1)
              / amG α (toPoly (CPoly.cIntegrateReduced Dt a d cands).rational.2))
          + amG α (toPoly (cHermiteReduceTower Dt a d).2.1)
            / amG α (toPoly (cHermiteReduceTower Dt a d).2.2)
        = amG α (toPoly a) / amG α (toPoly d))
    (hmatch : ((CPoly.cIntegrateReduced Dt a d cands).logs.map (fun cv =>
          amG α (Polynomial.C (CFieldSpec.toK cv.1))
            * (towerFractionFieldDerivG Dt (amG α (toPoly cv.2)) / amG α (toPoly cv.2)))).sum
        = amG α (toPoly (cHermiteReduceTower Dt a d).2.1)
          / amG α (toPoly (cHermiteReduceTower Dt a d).2.2)) :
    towerFractionFieldDerivG Dt
        (amG α (toPoly (CPoly.cIntegrateReduced Dt a d cands).rational.1)
          / amG α (toPoly (CPoly.cIntegrateReduced Dt a d cands).rational.2))
        + logResidueSumG Dt (CPoly.cIntegrateReduced Dt a d cands).logs
      = amG α (toPoly a) / amG α (toPoly d) :=
  field_identity_of_reducedG_of_residueMatch Dt
    (CPoly.cIntegrateReduced Dt a d cands).rational.1
    (CPoly.cIntegrateReduced Dt a d cands).rational.2
    (cHermiteReduceTower Dt a d).2.1 (cHermiteReduceTower Dt a d).2.2
    a d (CPoly.cIntegrateReduced Dt a d cands).logs hherm hmatch

/-! ### The deliverables at the level-1 carrier `α = QFunNZG ℚ` -/

/-- `Algebra ℚ (CFieldSpec.K (QFunNZG ℚ))` via `CFieldSpec.K (QFunNZG ℚ) = RatFunc ℚ`. -/
noncomputable local instance : Algebra ℚ (CFieldSpec.K (QFunNZG ℚ)) :=
  inferInstanceAs (Algebra ℚ (RatFunc ℚ))

/-- The tower residue resultant's roots are the residues over `ℚ(x)`
(`roots_residueResultantTowerG_eq_residues` at `K = RatFunc ℚ`). -/
theorem roots_residueResultantTowerG_eq_residues_qfunNZG (lc : CFieldSpec.K (QFunNZG ℚ)) (N : ℕ)
    (droots : Multiset (CFieldSpec.K (QFunNZG ℚ))) (aval ddval : CFieldSpec.K (QFunNZG ℚ) → CFieldSpec.K (QFunNZG ℚ))
    (hlc : lc ≠ 0) (hDd : ∀ α ∈ droots, ddval α ≠ 0) (R : (CFieldSpec.K (QFunNZG ℚ))[X])
    (hR : R = Polynomial.C lc ^ N
      * (droots.map (fun α =>
          Polynomial.C (aval α) - Polynomial.X * Polynomial.C (ddval α))).prod) :
    R.roots = droots.map (fun α => aval α / ddval α) :=
  LogResidueTower.roots_residueResultantTowerG_eq_residues lc N droots aval ddval hlc hDd R hR

/-- The fuel-free reduced-case RT one-shot over `ℚ(x)(t)`: for `res = cIntegrateReduced Dt a d
cands`, given the Hermite half and the RT residue match, `D(g) + logResidueSumG Dt res.logs = amG a/amG d`. -/
theorem field_identity_of_cIntegrateReducedG_of_residueMatch_qfunNZG (Dt : CPoly (QFunNZG ℚ))
    (a d : CPoly (QFunNZG ℚ)) (cands : List (QFunNZG ℚ))
    (hherm : towerFractionFieldDerivG Dt
            (amG (QFunNZG ℚ) (toPoly (CPoly.cIntegrateReduced Dt a d cands).rational.1)
              / amG (QFunNZG ℚ) (toPoly (CPoly.cIntegrateReduced Dt a d cands).rational.2))
          + amG (QFunNZG ℚ) (toPoly (cHermiteReduceTower Dt a d).2.1)
            / amG (QFunNZG ℚ) (toPoly (cHermiteReduceTower Dt a d).2.2)
        = amG (QFunNZG ℚ) (toPoly a) / amG (QFunNZG ℚ) (toPoly d))
    (hmatch : ((CPoly.cIntegrateReduced Dt a d cands).logs.map (fun cv =>
          amG (QFunNZG ℚ) (Polynomial.C (CFieldSpec.toK cv.1))
            * (towerFractionFieldDerivG Dt (amG (QFunNZG ℚ) (toPoly cv.2))
                / amG (QFunNZG ℚ) (toPoly cv.2)))).sum
        = amG (QFunNZG ℚ) (toPoly (cHermiteReduceTower Dt a d).2.1)
          / amG (QFunNZG ℚ) (toPoly (cHermiteReduceTower Dt a d).2.2)) :
    towerFractionFieldDerivG Dt
        (amG (QFunNZG ℚ) (toPoly (CPoly.cIntegrateReduced Dt a d cands).rational.1)
          / amG (QFunNZG ℚ) (toPoly (CPoly.cIntegrateReduced Dt a d cands).rational.2))
        + logResidueSumG Dt (CPoly.cIntegrateReduced Dt a d cands).logs
      = amG (QFunNZG ℚ) (toPoly a) / amG (QFunNZG ℚ) (toPoly d) :=
  field_identity_of_cIntegrateReducedG_of_residueMatch Dt a d cands hherm hmatch

/-! ### Restatements -/

-- ★ THE MILESTONE (abstract, axiom-clean, no native_decide): the tower residue resultant's roots ARE the
-- residues `a(α)/Dd(α)` — the transcendental `roots_rtResultant`, monomial-derivative general.
example {K : Type*} [Field K] (lc : K) (N : ℕ) (droots : Multiset K) (aval ddval : K → K)
    (hlc : lc ≠ 0) (hDd : ∀ α ∈ droots, ddval α ≠ 0) (R : K[X])
    (hR : R = Polynomial.C lc ^ N
      * (droots.map (fun α =>
          Polynomial.C (aval α) - Polynomial.X * Polynomial.C (ddval α))).prod) :
    R.roots = droots.map (fun α => aval α / ddval α) :=
  LogResidueTower.roots_residueResultantTowerG_eq_residues lc N droots aval ddval hlc hDd R hR

-- ★ THE KEYSTONE (Task 1, abstract, no native_decide): the Rothstein–Trager log argument `gcd(d, a − c·Dd)`
-- IS the residue's linear factor `X − β`, for `d = ∏_{α∈s}(X − α)` squarefree with distinct residues.
example {K : Type*} [Field K] [DecidableEq K] (s : Finset K) (a Dd : K[X])
    (hDd : ∀ α ∈ s, Dd.eval α ≠ 0)
    (hdist : ∀ α ∈ s, ∀ β ∈ s, α ≠ β → a.eval α / Dd.eval α ≠ a.eval β / Dd.eval β)
    (β : K) (hβ : β ∈ s) :
    gcd (Lagrange.nodal s id) (a - Polynomial.C (a.eval β / Dd.eval β) * Dd)
      = Polynomial.X - Polynomial.C β :=
  LogResidueTower.residue_gcd_eq_linear_factor s a Dd hDd hdist β hβ

-- ★★ THE RT HALF (abstract, checker-free, no native_decide): the residue sum differentiates to the Hermite
-- leftover, so `D(g) + logResidueSumG = a/d` — given the abstract Hermite telescoping + the residue match.
example (Dt : CPoly α) (gnum gden hNum hDen anum aden : CPoly α) (logs : List (α × CPoly α))
    (hherm : towerFractionFieldDerivG Dt (amG α (toPoly gnum) / amG α (toPoly gden))
          + amG α (toPoly hNum) / amG α (toPoly hDen)
        = amG α (toPoly anum) / amG α (toPoly aden))
    (hmatch : (logs.map (fun cv =>
          amG α (Polynomial.C (CFieldSpec.toK cv.1))
            * (towerFractionFieldDerivG Dt (amG α (toPoly cv.2)) / amG α (toPoly cv.2)))).sum
        = amG α (toPoly hNum) / amG α (toPoly hDen)) :
    towerFractionFieldDerivG Dt (amG α (toPoly gnum) / amG α (toPoly gden))
        + logResidueSumG Dt logs
      = amG α (toPoly anum) / amG α (toPoly aden) :=
  field_identity_of_reducedG_of_residueMatch Dt gnum gden hNum hDen anum aden logs hherm hmatch

/-! ### Axiom audit -/

#print axioms LogResidueTower.residueLinearFactor_eq
#print axioms LogResidueTower.roots_residueResultantTowerG_eq_residues
#print axioms LogResidueTower.residue_gcd_associated_linear_factor
#print axioms LogResidueTower.residue_gcd_eq_linear_factor
#print axioms monic_toPolyG_cmonicG
#print axioms toPolyG_cAmcDdG
#print axioms towerFractionFieldDerivG_logDeriv
#print axioms logResidueSumG_eq_logDeriv_sum
#print axioms logResidueSumG_eq_of_residue_match
#print axioms field_identity_of_reducedG_of_residueMatch
#print axioms field_identity_of_cIntegrateReducedG_of_residueMatch
#print axioms roots_residueResultantTowerG_eq_residues_qfunNZG
#print axioms field_identity_of_cIntegrateReducedG_of_residueMatch_qfunNZG

end DeepWiki.SymbolicIntegration
