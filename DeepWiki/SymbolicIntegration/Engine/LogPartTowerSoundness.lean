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

open Compute CPolyG QFunNZG

/-! ### The `logResidueSumG` reading as a monomial log-derivative sum -/

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

omit [Algebra ℚ (CFieldSpec.K α)] in
/-- `toPolyG (cAmcDdG Dt a d c) = toPolyG a − C(toK c)·implicitDeriv (toPolyG Dt) (toPolyG d)`. -/
@[denote] theorem toPolyG_cAmcDdG (Dt a d : CPolyG α) (c : α) :
    toPolyG (cAmcDdG Dt a d c)
      = toPolyG a - Polynomial.C (CFieldSpec.toK c)
          * Differential.implicitDeriv (toPolyG Dt) (toPolyG d) := by
  rw [cAmcDdG]
  simp only [denote]

/-! ### The RT residue identity: `logResidueSumG = a/d` from the residue match -/

/-- `logResidueSumG = a/d` from the residue match: given the log-derivative sum equals `amG a/amG d`,
so does `logResidueSumG Dt logs`. -/
theorem logResidueSumG_eq_of_residue_match (Dt : CPolyG α) (a d : CPolyG α)
    (logs : List (α × CPolyG α))
    (hmatch : (logs.map (fun cv =>
          amG α (Polynomial.C (CFieldSpec.toK cv.1))
            * (towerFractionFieldDerivG Dt (amG α (toPolyG cv.2)) / amG α (toPolyG cv.2)))).sum
        = amG α (toPolyG a) / amG α (toPolyG d)) :
    logResidueSumG Dt logs = amG α (toPolyG a) / amG α (toPolyG d) := by
  rw [logResidueSumG_eq_logDeriv_sum Dt logs]
  exact hmatch

/-! ### Assembly: the reduced-case field identity from the Hermite half + the RT residue match -/

/-- The reduced-case field identity: given the Hermite half `D(g) + h = a/d` and the RT residue match
(the residue logs' log-derivative sum equals `h`), `D(g) + logResidueSumG = a/d`. -/
theorem field_identity_of_reducedG_of_residueMatch (Dt : CPolyG α)
    (gnum gden hNum hDen anum aden : CPolyG α) (logs : List (α × CPolyG α))
    (hherm : towerFractionFieldDerivG Dt (amG α (toPolyG gnum) / amG α (toPolyG gden))
          + amG α (toPolyG hNum) / amG α (toPolyG hDen)
        = amG α (toPolyG anum) / amG α (toPolyG aden))
    (hmatch : (logs.map (fun cv =>
          amG α (Polynomial.C (CFieldSpec.toK cv.1))
            * (towerFractionFieldDerivG Dt (amG α (toPolyG cv.2)) / amG α (toPolyG cv.2)))).sum
        = amG α (toPolyG hNum) / amG α (toPolyG hDen)) :
    towerFractionFieldDerivG Dt (amG α (toPolyG gnum) / amG α (toPolyG gden))
        + logResidueSumG Dt logs
      = amG α (toPolyG anum) / amG α (toPolyG aden) := by
  rw [logResidueSumG_eq_of_residue_match Dt hNum hDen logs hmatch, hherm]

/-! ### The fuel-free reduced-case one-shot for `cIntegrateReducedG`

Reads `cIntegrateReducedG`'s fields into `field_identity_of_reducedG_of_residueMatch`. -/

variable [CFracGcdCoreWf α]

/-- The fuel-free reduced-case one-shot: for `res = cIntegrateReducedG Dt a d cands`, given the
Hermite half and the RT residue match, `D(g) + logResidueSumG Dt res.logs = a/d`. -/
theorem field_identity_of_cIntegrateReducedG_of_residueMatch (Dt : CPolyG α)
    (a d : CPolyG α) (cands : List α)
    (hherm : towerFractionFieldDerivG Dt
            (amG α (toPolyG (CPolyG.cIntegrateReducedG Dt a d cands).rational.1)
              / amG α (toPolyG (CPolyG.cIntegrateReducedG Dt a d cands).rational.2))
          + amG α (toPolyG (cHermiteReduceTowerG Dt a d).2.1)
            / amG α (toPolyG (cHermiteReduceTowerG Dt a d).2.2)
        = amG α (toPolyG a) / amG α (toPolyG d))
    (hmatch : ((CPolyG.cIntegrateReducedG Dt a d cands).logs.map (fun cv =>
          amG α (Polynomial.C (CFieldSpec.toK cv.1))
            * (towerFractionFieldDerivG Dt (amG α (toPolyG cv.2)) / amG α (toPolyG cv.2)))).sum
        = amG α (toPolyG (cHermiteReduceTowerG Dt a d).2.1)
          / amG α (toPolyG (cHermiteReduceTowerG Dt a d).2.2)) :
    towerFractionFieldDerivG Dt
        (amG α (toPolyG (CPolyG.cIntegrateReducedG Dt a d cands).rational.1)
          / amG α (toPolyG (CPolyG.cIntegrateReducedG Dt a d cands).rational.2))
        + logResidueSumG Dt (CPolyG.cIntegrateReducedG Dt a d cands).logs
      = amG α (toPolyG a) / amG α (toPolyG d) :=
  field_identity_of_reducedG_of_residueMatch Dt
    (CPolyG.cIntegrateReducedG Dt a d cands).rational.1
    (CPolyG.cIntegrateReducedG Dt a d cands).rational.2
    (cHermiteReduceTowerG Dt a d).2.1 (cHermiteReduceTowerG Dt a d).2.2
    a d (CPolyG.cIntegrateReducedG Dt a d cands).logs hherm hmatch

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

/-- The fuel-free reduced-case RT one-shot over `ℚ(x)(t)`: for `res = cIntegrateReducedG Dt a d
cands`, given the Hermite half and the RT residue match, `D(g) + logResidueSumG Dt res.logs = amG a/amG d`. -/
theorem field_identity_of_cIntegrateReducedG_of_residueMatch_qfunNZG (Dt : CPolyG (QFunNZG ℚ))
    (a d : CPolyG (QFunNZG ℚ)) (cands : List (QFunNZG ℚ))
    (hherm : towerFractionFieldDerivG Dt
            (amG (QFunNZG ℚ) (toPolyG (CPolyG.cIntegrateReducedG Dt a d cands).rational.1)
              / amG (QFunNZG ℚ) (toPolyG (CPolyG.cIntegrateReducedG Dt a d cands).rational.2))
          + amG (QFunNZG ℚ) (toPolyG (cHermiteReduceTowerG Dt a d).2.1)
            / amG (QFunNZG ℚ) (toPolyG (cHermiteReduceTowerG Dt a d).2.2)
        = amG (QFunNZG ℚ) (toPolyG a) / amG (QFunNZG ℚ) (toPolyG d))
    (hmatch : ((CPolyG.cIntegrateReducedG Dt a d cands).logs.map (fun cv =>
          amG (QFunNZG ℚ) (Polynomial.C (CFieldSpec.toK cv.1))
            * (towerFractionFieldDerivG Dt (amG (QFunNZG ℚ) (toPolyG cv.2))
                / amG (QFunNZG ℚ) (toPolyG cv.2)))).sum
        = amG (QFunNZG ℚ) (toPolyG (cHermiteReduceTowerG Dt a d).2.1)
          / amG (QFunNZG ℚ) (toPolyG (cHermiteReduceTowerG Dt a d).2.2)) :
    towerFractionFieldDerivG Dt
        (amG (QFunNZG ℚ) (toPolyG (CPolyG.cIntegrateReducedG Dt a d cands).rational.1)
          / amG (QFunNZG ℚ) (toPolyG (CPolyG.cIntegrateReducedG Dt a d cands).rational.2))
        + logResidueSumG Dt (CPolyG.cIntegrateReducedG Dt a d cands).logs
      = amG (QFunNZG ℚ) (toPolyG a) / amG (QFunNZG ℚ) (toPolyG d) :=
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
example (Dt : CPolyG α) (gnum gden hNum hDen anum aden : CPolyG α) (logs : List (α × CPolyG α))
    (hherm : towerFractionFieldDerivG Dt (amG α (toPolyG gnum) / amG α (toPolyG gden))
          + amG α (toPolyG hNum) / amG α (toPolyG hDen)
        = amG α (toPolyG anum) / amG α (toPolyG aden))
    (hmatch : (logs.map (fun cv =>
          amG α (Polynomial.C (CFieldSpec.toK cv.1))
            * (towerFractionFieldDerivG Dt (amG α (toPolyG cv.2)) / amG α (toPolyG cv.2)))).sum
        = amG α (toPolyG hNum) / amG α (toPolyG hDen)) :
    towerFractionFieldDerivG Dt (amG α (toPolyG gnum) / amG α (toPolyG gden))
        + logResidueSumG Dt logs
      = amG α (toPolyG anum) / amG α (toPolyG aden) :=
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
