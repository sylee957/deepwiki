import DeepWiki.SymbolicIntegration.Engine.OneShotAssembly
import DeepWiki.SymbolicIntegration.Engine.Hyperexp.NormalCore

/-! # Soundness of the hyperexponential normal-part driver

`D(∫fₙ) = fₙ` for the residual-feedback hyperexponential normal-part driver, unconditional in the
residue sum `∑c`, reduced to the base-RDE oracle's residual soundness `D(∫R) = R`. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

/-! ### The overshoot identity `D(logPart) = a/d + R` for the hyperexponential monomial

The Rothstein–Trager log part of a hyperexponential normal part `fₙ = a/d` differentiates to `a/d + R`
with residual `R = b·∑c`, carried unconditionally in `∑c`. -/

namespace ResidueMatchTower

variable {K : Type*} [Field K] [Differential K] [Algebra ℚ K]

/-- Hyperexponential overshoot identity: the Rothstein–Trager residue sum equals
`algebraMap(C(b·∑c)) + a/d` over `RatFunc K`, for a monomial `v = C b·X`, squarefree
`d = ∏_{α∈s}(t−α)`, `deg a < #s`, every root normal — unconditional in `∑c`. -/
theorem hyperexp_residue_sum_eq_overshoot_add (s : Finset K) (a : K[X]) (b : K)
    (hA : a.degree < s.card) (hnorm : ∀ α ∈ s, (C b * X).eval α ≠ α′) :
    ∑ α ∈ s, algebraMap K[X] (RatFunc K)
          (C (a.eval α / (Differential.implicitDeriv (C b * X) (Lagrange.nodal s id)).eval α))
        * (extendDeriv (Differential.implicitDeriv (C b * X))
              (algebraMap K[X] (RatFunc K) (X - C α))
            / algebraMap K[X] (RatFunc K) (X - C α))
      = algebraMap K[X] (RatFunc K)
            (C (b * ∑ α ∈ s,
              a.eval α / (Differential.implicitDeriv (C b * X) (Lagrange.nodal s id)).eval α))
        + algebraMap K[X] (RatFunc K) a / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id) := by
  -- residue sum = (cancel sum) + a/d (unconditional), then cancel sum = algebraMap(C(b·∑c)) (hyperexp)
  rw [monomial_residue_sum_eq_cancel_add s a (C b * X) hA hnorm,
    hyperexp_cancel_sum_eq s b
      (fun α => a.eval α / (Differential.implicitDeriv (C b * X) (Lagrange.nodal s id)).eval α)]

end ResidueMatchTower

/-! ### The overshoot residue match over `K = CFieldSpec.K α` (engine vocabulary)

The overshoot identity restated on the engine's per-root `List` sum, transported through `amG = algebraMap`
and the `towerFractionFieldDerivG` unfolding. -/

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

/-- Engine-vocabulary overshoot: the per-root `List` sum equals `amG(C(b·∑c)) + a/d` over
`RatFunc (CFieldSpec.K α)`, with `D = towerFractionFieldDerivG Dt`, unconditional in `∑c`. -/
theorem hyperexp_overshoot_list_engine (Dt : CPolyG α) (s : Finset (CFieldSpec.K α))
    (a : (CFieldSpec.K α)[X]) (b : CFieldSpec.K α) (hDt : toPolyG Dt = C b * X)
    (hA : a.degree < s.card) (hnorm : ∀ β ∈ s, (C b * X).eval β ≠ β′) :
    ((s.toList.map (fun β =>
          (a.eval β / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β,
            X - C β))).map
        (fun cv =>
          amG α (C cv.1)
            * (towerFractionFieldDerivG Dt (amG α cv.2) / amG α cv.2))).sum
      = amG α (C (b * ∑ β ∈ s,
            a.eval β / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β))
        + amG α a / amG α (Lagrange.nodal s id) := by
  show ((s.toList.map (fun β =>
          (a.eval β / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β,
            X - C β))).map
        (fun cv =>
          algebraMap (CFieldSpec.K α)[X] (RatFunc (CFieldSpec.K α)) (C cv.1)
            * (extendDeriv (Differential.implicitDeriv (toPolyG Dt))
                  (algebraMap _ (RatFunc (CFieldSpec.K α)) cv.2)
                / algebraMap _ (RatFunc (CFieldSpec.K α)) cv.2))).sum = _
  rw [hDt]
  -- collapse `(s.toList.map f).map g`, then to the `Finset.sum` over `s`, then the K[X]-level overshoot
  rw [List.map_map, Finset.sum_map_toList]
  exact ResidueMatchTower.hyperexp_residue_sum_eq_overshoot_add s a b hA hnorm

/-- Engine residue-match overshoot: the log sum `∑_{(c,v)∈logs} amG(C(toK c))·D(log v)` equals
`amG(C(b·∑c)) + amG(hNum)/amG(hDen)` over `RatFunc (CFieldSpec.K α)`, given the per-root form `hform`,
unconditional in `∑c`. -/
theorem hyperexp_engine_overshoot (Dt : CPolyG α) (s : Finset (CFieldSpec.K α))
    (hNum hDen : CPolyG α) (b : CFieldSpec.K α) (logs : List (α × CPolyG α))
    (hDt : toPolyG Dt = C b * X)
    (hden : toPolyG hDen = Lagrange.nodal s id)
    (hA : (toPolyG hNum).degree < s.card) (hnorm : ∀ β ∈ s, (C b * X).eval β ≠ β′)
    (hform : logs.map (fun cv => (CFieldSpec.toK cv.1, toPolyG cv.2))
      = s.toList.map (fun β =>
          ((toPolyG hNum).eval β
              / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β,
            X - C β))) :
    (logs.map (fun cv =>
          amG α (Polynomial.C (CFieldSpec.toK cv.1))
            * (towerFractionFieldDerivG Dt (amG α (toPolyG cv.2)) / amG α (toPolyG cv.2)))).sum
      = amG α (C (b * ∑ β ∈ s,
            (toPolyG hNum).eval β
              / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β))
        + amG α (toPolyG hNum) / amG α (toPolyG hDen) := by
  -- the engine summand factors through `(toK cv.1, toPolyG cv.2)`: rewrite the mapped list by `hform`
  have hsummand : (logs.map (fun cv =>
        amG α (Polynomial.C (CFieldSpec.toK cv.1))
          * (towerFractionFieldDerivG Dt (amG α (toPolyG cv.2)) / amG α (toPolyG cv.2))))
      = (logs.map (fun cv => (CFieldSpec.toK cv.1, toPolyG cv.2))).map
          (fun p => amG α (Polynomial.C p.1)
            * (towerFractionFieldDerivG Dt (amG α p.2) / amG α p.2)) := by
    rw [List.map_map]; rfl
  rw [hsummand, hform, hden, List.map_map]
  -- now the per-root form of the bridge `hyperexp_overshoot_list_engine`
  have hbridge := hyperexp_overshoot_list_engine Dt s (toPolyG hNum) b hDt hA hnorm
  rw [List.map_map] at hbridge
  exact hbridge

/-! ### The reduced-case overshoot field identity `D(g) + logResidueSumG = a/d + R`

Composing the Hermite half with the overshoot residue sum. -/

/-- Reduced-case overshoot field identity: for `res = cIntegrateReducedGWf Dt a d cands` and the Hermite
half/per-root hypotheses, `D(g) + logResidueSumG Dt res.logs = amG a/amG d + amG(C(b·∑c))` over
`RatFunc (CFieldSpec.K α)`, unconditional in `∑c`. -/
theorem field_identity_of_cIntegrateReducedGWf_hyperexp_overshoot [CFracGcdCoreWf α]
    (Dt : CPolyG α) (a d : CPolyG α) (cands : List α) (s : Finset (CFieldSpec.K α))
    (b : CFieldSpec.K α)
    (hDt : toPolyG Dt = C b * X)
    (hherm : towerFractionFieldDerivG Dt
            (amG α (toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.1)
              / amG α (toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.2))
          + amG α (toPolyG (cHermiteReduceTowerGWf Dt a d).2.1)
            / amG α (toPolyG (cHermiteReduceTowerGWf Dt a d).2.2)
        = amG α (toPolyG a) / amG α (toPolyG d))
    (hden : toPolyG (cHermiteReduceTowerGWf Dt a d).2.2 = Lagrange.nodal s id)
    (hA : (toPolyG (cHermiteReduceTowerGWf Dt a d).2.1).degree < s.card)
    (hnorm : ∀ β ∈ s, (C b * X).eval β ≠ β′)
    (hform : (CPolyG.cIntegrateReducedGWf Dt a d cands).logs.map
          (fun cv => (CFieldSpec.toK cv.1, toPolyG cv.2))
        = s.toList.map (fun β =>
            ((toPolyG (cHermiteReduceTowerGWf Dt a d).2.1).eval β
                / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β,
              X - C β))) :
    towerFractionFieldDerivG Dt
        (amG α (toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.1)
          / amG α (toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.2))
        + logResidueSumG Dt (CPolyG.cIntegrateReducedGWf Dt a d cands).logs
      = amG α (toPolyG a) / amG α (toPolyG d)
        + amG α (C (b * ∑ β ∈ s,
            (toPolyG (cHermiteReduceTowerGWf Dt a d).2.1).eval β
              / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β)) := by
  rw [logResidueSumG_eq_logDeriv_sum Dt (CPolyG.cIntegrateReducedGWf Dt a d cands).logs,
    hyperexp_engine_overshoot Dt s (cHermiteReduceTowerGWf Dt a d).2.1
      (cHermiteReduceTowerGWf Dt a d).2.2 b
      (CPolyG.cIntegrateReducedGWf Dt a d cands).logs hDt hden hA hnorm hform]
  set Dg := towerFractionFieldDerivG Dt
    (amG α (toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.1)
      / amG α (toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.2)) with hDg
  set h := amG α (toPolyG (cHermiteReduceTowerGWf Dt a d).2.1)
    / amG α (toPolyG (cHermiteReduceTowerGWf Dt a d).2.2) with hh
  set R := amG α (C (b * ∑ β ∈ s,
    (toPolyG (cHermiteReduceTowerGWf Dt a d).2.1).eval β
      / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β)) with hR
  rw [show Dg + (R + h) = (Dg + h) + R by ring, hherm]

/-! ### The normal-part driver soundness `cIntegrateHyperexpNormalGWf_sound`

`cIntegrateHyperexpNormalGWf` runs the reduced capstone, reads `R = cHyperexpResidualG η red.logs`,
integrates `∫R` by the base-RDE oracle, and subtracts it; the new rational part `g − ∫R` differentiates to
`(a/d + R) − R = a/d`. The residual `hintR : D(∫R) = R` and the residual-read bridge `hRval : toK R = b·∑c`
are carried as hypotheses. -/

variable [CRischField α]

omit [CFieldSpec α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- Output shape of `cIntegrateHyperexpNormalGWf`: when it returns `some res` and the base oracle succeeds
on `R`, `res` has the same logs and rational part `g − ∫R`. -/
theorem cIntegrateHyperexpNormalGWf_shape [CFracGcdCoreWf α] (Dt : CPolyG α)
    (a d : CPolyG α) (cands : List α) (res : IntegralResultG α) (intR : α)
    (hintRsome : CRischField.crischDESolve (CField.zero : α)
        (cHyperexpResidualG (cExpEtaG Dt) (CPolyG.cIntegrateReducedGWf Dt a d cands).logs)
      = some intR)
    (hsome : CPolyG.cIntegrateHyperexpNormalGWf Dt a d cands = some res) :
    res = ⟨(csubG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.1
              (cmulG [intR] (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.2),
            (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.2),
          (CPolyG.cIntegrateReducedGWf Dt a d cands).logs⟩ := by
  rw [CPolyG.cIntegrateHyperexpNormalGWf] at hsome
  simp only [hintRsome] at hsome
  exact (Option.some.injEq _ _ ▸ hsome).symm

/-- Normal-part driver soundness `D(∫fₙ) = fₙ` for `cIntegrateHyperexpNormalGWf`, unconditional in `∑c`,
given the base-oracle residual `hintR` and the residual-read bridge `hRval`. -/
theorem cIntegrateHyperexpNormalGWf_sound [CFracGcdCoreWf α] (Dt : CPolyG α) (a d : CPolyG α)
    (cands : List α) (res : IntegralResultG α) (intR : α) (s : Finset (CFieldSpec.K α))
    (b : CFieldSpec.K α)
    (hDt : toPolyG Dt = C b * X)
    (hgden : toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.2 ≠ 0)
    (hintRsome : CRischField.crischDESolve (CField.zero : α)
        (cHyperexpResidualG (cExpEtaG Dt) (CPolyG.cIntegrateReducedGWf Dt a d cands).logs)
      = some intR)
    (hsome : CPolyG.cIntegrateHyperexpNormalGWf Dt a d cands = some res)
    (hherm : towerFractionFieldDerivG Dt
            (amG α (toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.1)
              / amG α (toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.2))
          + amG α (toPolyG (cHermiteReduceTowerGWf Dt a d).2.1)
            / amG α (toPolyG (cHermiteReduceTowerGWf Dt a d).2.2)
        = amG α (toPolyG a) / amG α (toPolyG d))
    (hden : toPolyG (cHermiteReduceTowerGWf Dt a d).2.2 = Lagrange.nodal s id)
    (hA : (toPolyG (cHermiteReduceTowerGWf Dt a d).2.1).degree < s.card)
    (hnorm : ∀ β ∈ s, (C b * X).eval β ≠ β′)
    (hform : (CPolyG.cIntegrateReducedGWf Dt a d cands).logs.map
          (fun cv => (CFieldSpec.toK cv.1, toPolyG cv.2))
        = s.toList.map (fun β =>
            ((toPolyG (cHermiteReduceTowerGWf Dt a d).2.1).eval β
                / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β,
              X - C β)))
    (hintR : towerFractionFieldDerivG Dt (amG α (Polynomial.C (CFieldSpec.toK intR)))
        = amG α (Polynomial.C (CFieldSpec.toK
            (cHyperexpResidualG (cExpEtaG Dt)
              (CPolyG.cIntegrateReducedGWf Dt a d cands).logs))))
    (hRval : amG α (Polynomial.C (CFieldSpec.toK
            (cHyperexpResidualG (cExpEtaG Dt)
              (CPolyG.cIntegrateReducedGWf Dt a d cands).logs)))
        = amG α (C (b * ∑ β ∈ s,
            (toPolyG (cHermiteReduceTowerGWf Dt a d).2.1).eval β
              / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β))) :
    towerFractionFieldDerivG Dt (amG α (toPolyG res.rational.1) / amG α (toPolyG res.rational.2))
        + logResidueSumG Dt res.logs
      = amG α (toPolyG a) / amG α (toPolyG d) := by
  rw [cIntegrateHyperexpNormalGWf_shape Dt a d cands res intR hintRsome hsome]
  set gnum := (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.1 with hgnum
  set gden := (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.2 with hgdenE
  have hAgden : amG α (toPolyG gden) ≠ 0 := amG_toPolyG_ne_zero hgden
  have hnewrat : amG α (toPolyG (csubG gnum (cmulG [intR] gden))) / amG α (toPolyG gden)
      = amG α (toPolyG gnum) / amG α (toPolyG gden) - amG α (Polynomial.C (CFieldSpec.toK intR)) := by
    simp only [denote, map_sub, map_mul, mul_zero, add_zero]
    rw [sub_div, mul_div_assoc, div_self hAgden, mul_one]
  rw [hnewrat, map_sub, hintR, hRval]
  have hover := field_identity_of_cIntegrateReducedGWf_hyperexp_overshoot Dt a d cands s b
    hDt hherm hden hA hnorm hform
  set Dg := towerFractionFieldDerivG Dt (amG α (toPolyG gnum) / amG α (toPolyG gden)) with hDg
  set L := logResidueSumG Dt (CPolyG.cIntegrateReducedGWf Dt a d cands).logs with hL
  set R := amG α (C (b * ∑ β ∈ s,
    (toPolyG (cHermiteReduceTowerGWf Dt a d).2.1).eval β
      / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β)) with hR
  rw [show Dg - R + L = (Dg + L) - R by ring, hover, add_sub_cancel_right]

/-! ### The driver soundness at the level-1 carrier `α = QFunNZG ℚ = ℚ(x)`

The normal-part driver soundness instantiated at `α = QFunNZG ℚ` (`CFieldSpec.K (QFunNZG ℚ) = RatFunc ℚ`),
unconditional in `∑c`. -/

/-- Local instance: the engine carrier `CFieldSpec.K (QFunNZG ℚ)` is `RatFunc ℚ` as a `ℚ`-algebra, matching
the `Algebra ℚ` the bridge `towerFractionFieldDerivG` uses. -/
noncomputable local instance : Algebra ℚ (CFieldSpec.K (QFunNZG ℚ)) :=
  inferInstanceAs (Algebra ℚ (RatFunc ℚ))

/-- Normal-part driver soundness over `ℚ(x)(t)`, unconditional in `∑c` — the `QFunNZG ℚ` instance of
`cIntegrateHyperexpNormalGWf_sound`. -/
theorem cIntegrateHyperexpNormalGWf_sound_qfunNZG (Dt : CPolyG (QFunNZG ℚ))
    (a d : CPolyG (QFunNZG ℚ)) (cands : List (QFunNZG ℚ)) (res : IntegralResultG (QFunNZG ℚ))
    (intR : QFunNZG ℚ) (s : Finset (CFieldSpec.K (QFunNZG ℚ))) (b : CFieldSpec.K (QFunNZG ℚ))
    (hDt : toPolyG Dt = C b * X)
    (hgden : toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.2 ≠ 0)
    (hintRsome : CRischField.crischDESolve (CField.zero : QFunNZG ℚ)
        (cHyperexpResidualG (cExpEtaG Dt) (CPolyG.cIntegrateReducedGWf Dt a d cands).logs)
      = some intR)
    (hsome : CPolyG.cIntegrateHyperexpNormalGWf Dt a d cands = some res)
    (hherm : towerFractionFieldDerivG Dt
            (amG (QFunNZG ℚ) (toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.1)
              / amG (QFunNZG ℚ) (toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.2))
          + amG (QFunNZG ℚ) (toPolyG (cHermiteReduceTowerGWf Dt a d).2.1)
            / amG (QFunNZG ℚ) (toPolyG (cHermiteReduceTowerGWf Dt a d).2.2)
        = amG (QFunNZG ℚ) (toPolyG a) / amG (QFunNZG ℚ) (toPolyG d))
    (hden : toPolyG (cHermiteReduceTowerGWf Dt a d).2.2 = Lagrange.nodal s id)
    (hA : (toPolyG (cHermiteReduceTowerGWf Dt a d).2.1).degree < s.card)
    (hnorm : ∀ β ∈ s, (C b * X).eval β ≠ β′)
    (hform : (CPolyG.cIntegrateReducedGWf Dt a d cands).logs.map
          (fun cv => (CFieldSpec.toK cv.1, toPolyG cv.2))
        = s.toList.map (fun β =>
            ((toPolyG (cHermiteReduceTowerGWf Dt a d).2.1).eval β
                / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β,
              X - C β)))
    (hintR : towerFractionFieldDerivG Dt (amG (QFunNZG ℚ) (Polynomial.C (CFieldSpec.toK intR)))
        = amG (QFunNZG ℚ) (Polynomial.C (CFieldSpec.toK
            (cHyperexpResidualG (cExpEtaG Dt)
              (CPolyG.cIntegrateReducedGWf Dt a d cands).logs))))
    (hRval : amG (QFunNZG ℚ) (Polynomial.C (CFieldSpec.toK
            (cHyperexpResidualG (cExpEtaG Dt)
              (CPolyG.cIntegrateReducedGWf Dt a d cands).logs)))
        = amG (QFunNZG ℚ) (C (b * ∑ β ∈ s,
            (toPolyG (cHermiteReduceTowerGWf Dt a d).2.1).eval β
              / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β))) :
    towerFractionFieldDerivG Dt
        (amG (QFunNZG ℚ) (toPolyG res.rational.1) / amG (QFunNZG ℚ) (toPolyG res.rational.2))
        + logResidueSumG Dt res.logs
      = amG (QFunNZG ℚ) (toPolyG a) / amG (QFunNZG ℚ) (toPolyG d) :=
  cIntegrateHyperexpNormalGWf_sound Dt a d cands res intR s b hDt hgden hintRsome hsome hherm hden
    hA hnorm hform hintR hRval

/-! ### The full driver soundness `cIntegrateHyperexpFullGWf_sound`

`cIntegrateHyperexpFullGWf` combines the Laurent special part with the normal part. Soundness composes the
Laurent field identity `hLaurField`, the normal-part soundness, and the canonical reconstruction `hrecon`,
giving `D(res) + logResidueSumG = a/d`, unconditional in `∑c`. -/

omit [CFieldSpec α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- Output shape of `cIntegrateHyperexpFullGWf`: when it returns `some res` and both the Laurent and normal
parts succeed, `res` is the combined rational part with the normal logs. -/
theorem cIntegrateHyperexpFullGWf_shape [CFracGcdCoreWf α] (Dt : CPolyG α)
    (a d : CPolyG α) (cands : List α) (res : IntegralResultG α) (lnum lden : CPolyG α)
    (nrm : IntegralResultG α)
    (hLaur : cIntegrateHyperexpLaurentG (cExpEtaG Dt)
        (canonicalRepresentationFastGWf Dt a d).1
        (cHyperexpSpecialNegG (canonicalRepresentationFastGWf Dt a d).2.1.1
          (canonicalRepresentationFastGWf Dt a d).2.1.2)
      = some (lnum, lden))
    (hNrm : CPolyG.cIntegrateHyperexpNormalGWf Dt
        (canonicalRepresentationFastGWf Dt a d).2.2.1
        (canonicalRepresentationFastGWf Dt a d).2.2.2 cands = some nrm)
    (hsome : CPolyG.cIntegrateHyperexpFullGWf Dt a d cands = some res) :
    res = ⟨(caddG (cmulG lnum nrm.rational.2) (cmulG nrm.rational.1 lden), cmulG lden nrm.rational.2),
          nrm.logs⟩ := by
  rw [CPolyG.cIntegrateHyperexpFullGWf] at hsome
  rcases hcrep : canonicalRepresentationFastGWf Dt a d with ⟨fp, ⟨b, ds⟩, ⟨cn, dn⟩⟩
  rw [hcrep] at hsome hLaur hNrm
  simp only [hLaur, hNrm] at hsome
  exact (Option.some.injEq _ _ ▸ hsome).symm

/-- Full hyperexponential driver soundness `D(∫f) = f` for `cIntegrateHyperexpFullGWf`, unconditional in
`∑c` — composes the Laurent field identity, the normal-part field identity, and the canonical
reconstruction. -/
theorem cIntegrateHyperexpFullGWf_sound [CFracGcdCoreWf α] (Dt : CPolyG α) (a d : CPolyG α)
    (cands : List α) (res : IntegralResultG α) (lnum lden : CPolyG α) (nrm : IntegralResultG α)
    (fpPart : CPolyG α) (hlden : toPolyG lden ≠ 0) (hgden : toPolyG nrm.rational.2 ≠ 0)
    (hLaur : cIntegrateHyperexpLaurentG (cExpEtaG Dt)
        (canonicalRepresentationFastGWf Dt a d).1
        (cHyperexpSpecialNegG (canonicalRepresentationFastGWf Dt a d).2.1.1
          (canonicalRepresentationFastGWf Dt a d).2.1.2)
      = some (lnum, lden))
    (hNrm : CPolyG.cIntegrateHyperexpNormalGWf Dt
        (canonicalRepresentationFastGWf Dt a d).2.2.1
        (canonicalRepresentationFastGWf Dt a d).2.2.2 cands = some nrm)
    (hsome : CPolyG.cIntegrateHyperexpFullGWf Dt a d cands = some res)
    (hLaurField : towerFractionFieldDerivG Dt (amG α (toPolyG lnum) / amG α (toPolyG lden))
        = amG α (toPolyG fpPart))
    (hNrmField : towerFractionFieldDerivG Dt
            (amG α (toPolyG nrm.rational.1) / amG α (toPolyG nrm.rational.2))
          + logResidueSumG Dt nrm.logs
        = amG α (toPolyG (canonicalRepresentationFastGWf Dt a d).2.2.1)
          / amG α (toPolyG (canonicalRepresentationFastGWf Dt a d).2.2.2))
    (hrecon : amG α (toPolyG fpPart)
          + amG α (toPolyG (canonicalRepresentationFastGWf Dt a d).2.2.1)
            / amG α (toPolyG (canonicalRepresentationFastGWf Dt a d).2.2.2)
        = amG α (toPolyG a) / amG α (toPolyG d)) :
    towerFractionFieldDerivG Dt (amG α (toPolyG res.rational.1) / amG α (toPolyG res.rational.2))
        + logResidueSumG Dt res.logs
      = amG α (toPolyG a) / amG α (toPolyG d) := by
  rw [cIntegrateHyperexpFullGWf_shape Dt a d cands res lnum lden nrm hLaur hNrm hsome]
  have hAlden : amG α (toPolyG lden) ≠ 0 := amG_toPolyG_ne_zero hlden
  have hAgden : amG α (toPolyG nrm.rational.2) ≠ 0 := amG_toPolyG_ne_zero hgden
  have hcombine : amG α (toPolyG (caddG (cmulG lnum nrm.rational.2) (cmulG nrm.rational.1 lden)))
        / amG α (toPolyG (cmulG lden nrm.rational.2))
      = amG α (toPolyG lnum) / amG α (toPolyG lden)
        + amG α (toPolyG nrm.rational.1) / amG α (toPolyG nrm.rational.2) := by
    simp only [denote, map_add, map_mul]
    field_simp
  rw [hcombine, map_add, hLaurField]
  rw [add_assoc, hNrmField]
  exact hrecon

/-! ### Restatements against the intended wording (anonymous `example`s) -/

-- The overshoot identity: the Rothstein–Trager log part of a hyperexp normal part differentiates
-- to `a/d + R`, not `a/d`, with residual `R = b·∑c`, unconditional in `∑c`.
example {K : Type*} [Field K] [Differential K] [Algebra ℚ K] (s : Finset K) (a : K[X]) (b : K)
    (hA : a.degree < s.card) (hnorm : ∀ α ∈ s, (C b * X).eval α ≠ α′) :
    ∑ α ∈ s, algebraMap K[X] (RatFunc K)
          (C (a.eval α / (Differential.implicitDeriv (C b * X) (Lagrange.nodal s id)).eval α))
        * (extendDeriv (Differential.implicitDeriv (C b * X))
              (algebraMap K[X] (RatFunc K) (X - C α))
            / algebraMap K[X] (RatFunc K) (X - C α))
      = algebraMap K[X] (RatFunc K)
            (C (b * ∑ α ∈ s,
              a.eval α / (Differential.implicitDeriv (C b * X) (Lagrange.nodal s id)).eval α))
        + algebraMap K[X] (RatFunc K) a / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id) :=
  ResidueMatchTower.hyperexp_residue_sum_eq_overshoot_add s a b hA hnorm

-- The reduced-capstone overshoot identity: `cIntegrateReducedGWf` has the same hyperexp overshoot
-- statement.
example [CFracGcdCoreWf α] (Dt : CPolyG α) (a d : CPolyG α) (cands : List α)
    (s : Finset (CFieldSpec.K α)) (b : CFieldSpec.K α) (hDt : toPolyG Dt = C b * X)
    (hherm : towerFractionFieldDerivG Dt
            (amG α (toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.1)
              / amG α (toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.2))
          + amG α (toPolyG (cHermiteReduceTowerGWf Dt a d).2.1)
            / amG α (toPolyG (cHermiteReduceTowerGWf Dt a d).2.2)
        = amG α (toPolyG a) / amG α (toPolyG d))
    (hden : toPolyG (cHermiteReduceTowerGWf Dt a d).2.2 = Lagrange.nodal s id)
    (hA : (toPolyG (cHermiteReduceTowerGWf Dt a d).2.1).degree < s.card)
    (hnorm : ∀ β ∈ s, (C b * X).eval β ≠ β′)
    (hform : (CPolyG.cIntegrateReducedGWf Dt a d cands).logs.map
          (fun cv => (CFieldSpec.toK cv.1, toPolyG cv.2))
        = s.toList.map (fun β =>
            ((toPolyG (cHermiteReduceTowerGWf Dt a d).2.1).eval β
                / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β,
              X - C β))) :
    towerFractionFieldDerivG Dt
        (amG α (toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.1)
          / amG α (toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.2))
        + logResidueSumG Dt (CPolyG.cIntegrateReducedGWf Dt a d cands).logs
      = amG α (toPolyG a) / amG α (toPolyG d)
        + amG α (C (b * ∑ β ∈ s,
            (toPolyG (cHermiteReduceTowerGWf Dt a d).2.1).eval β
              / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β)) :=
  field_identity_of_cIntegrateReducedGWf_hyperexp_overshoot Dt a d cands s b
    hDt hherm hden hA hnorm hform

-- The §5.9 normal-part driver soundness: `cIntegrateHyperexpNormalGWf = some res ⟹ D(res) = a/d` under
-- the same residual-oracle hypothesis.
example [CFracGcdCoreWf α] (Dt : CPolyG α) (a d : CPolyG α) (cands : List α)
    (res : IntegralResultG α) (intR : α) (s : Finset (CFieldSpec.K α)) (b : CFieldSpec.K α)
    (hDt : toPolyG Dt = C b * X)
    (hgden : toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.2 ≠ 0)
    (hintRsome : CRischField.crischDESolve (CField.zero : α)
        (cHyperexpResidualG (cExpEtaG Dt) (CPolyG.cIntegrateReducedGWf Dt a d cands).logs)
      = some intR)
    (hsome : CPolyG.cIntegrateHyperexpNormalGWf Dt a d cands = some res)
    (hherm : towerFractionFieldDerivG Dt
            (amG α (toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.1)
              / amG α (toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.2))
          + amG α (toPolyG (cHermiteReduceTowerGWf Dt a d).2.1)
            / amG α (toPolyG (cHermiteReduceTowerGWf Dt a d).2.2)
        = amG α (toPolyG a) / amG α (toPolyG d))
    (hden : toPolyG (cHermiteReduceTowerGWf Dt a d).2.2 = Lagrange.nodal s id)
    (hA : (toPolyG (cHermiteReduceTowerGWf Dt a d).2.1).degree < s.card)
    (hnorm : ∀ β ∈ s, (C b * X).eval β ≠ β′)
    (hform : (CPolyG.cIntegrateReducedGWf Dt a d cands).logs.map
          (fun cv => (CFieldSpec.toK cv.1, toPolyG cv.2))
        = s.toList.map (fun β =>
            ((toPolyG (cHermiteReduceTowerGWf Dt a d).2.1).eval β
                / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β,
              X - C β)))
    (hintR : towerFractionFieldDerivG Dt (amG α (Polynomial.C (CFieldSpec.toK intR)))
        = amG α (Polynomial.C (CFieldSpec.toK
            (cHyperexpResidualG (cExpEtaG Dt)
              (CPolyG.cIntegrateReducedGWf Dt a d cands).logs))))
    (hRval : amG α (Polynomial.C (CFieldSpec.toK
            (cHyperexpResidualG (cExpEtaG Dt)
              (CPolyG.cIntegrateReducedGWf Dt a d cands).logs)))
        = amG α (C (b * ∑ β ∈ s,
            (toPolyG (cHermiteReduceTowerGWf Dt a d).2.1).eval β
              / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β))) :
    towerFractionFieldDerivG Dt (amG α (toPolyG res.rational.1) / amG α (toPolyG res.rational.2))
        + logResidueSumG Dt res.logs
      = amG α (toPolyG a) / amG α (toPolyG d) :=
  cIntegrateHyperexpNormalGWf_sound Dt a d cands res intR s b hDt hgden hintRsome hsome hherm hden
    hA hnorm hform hintR hRval

-- The full hyperexp driver soundness: `cIntegrateHyperexpFullGWf = some res ⟹ D(res) = a/d`, combining
-- the canonical and normal parts.
example [CFracGcdCoreWf α] (Dt : CPolyG α) (a d : CPolyG α) (cands : List α)
    (res : IntegralResultG α) (lnum lden : CPolyG α) (nrm : IntegralResultG α) (fpPart : CPolyG α)
    (hlden : toPolyG lden ≠ 0) (hgden : toPolyG nrm.rational.2 ≠ 0)
    (hLaur : cIntegrateHyperexpLaurentG (cExpEtaG Dt)
        (canonicalRepresentationFastGWf Dt a d).1
        (cHyperexpSpecialNegG (canonicalRepresentationFastGWf Dt a d).2.1.1
          (canonicalRepresentationFastGWf Dt a d).2.1.2)
      = some (lnum, lden))
    (hNrm : CPolyG.cIntegrateHyperexpNormalGWf Dt
        (canonicalRepresentationFastGWf Dt a d).2.2.1
        (canonicalRepresentationFastGWf Dt a d).2.2.2 cands = some nrm)
    (hsome : CPolyG.cIntegrateHyperexpFullGWf Dt a d cands = some res)
    (hLaurField : towerFractionFieldDerivG Dt (amG α (toPolyG lnum) / amG α (toPolyG lden))
        = amG α (toPolyG fpPart))
    (hNrmField : towerFractionFieldDerivG Dt
            (amG α (toPolyG nrm.rational.1) / amG α (toPolyG nrm.rational.2))
          + logResidueSumG Dt nrm.logs
        = amG α (toPolyG (canonicalRepresentationFastGWf Dt a d).2.2.1)
          / amG α (toPolyG (canonicalRepresentationFastGWf Dt a d).2.2.2))
    (hrecon : amG α (toPolyG fpPart)
          + amG α (toPolyG (canonicalRepresentationFastGWf Dt a d).2.2.1)
            / amG α (toPolyG (canonicalRepresentationFastGWf Dt a d).2.2.2)
        = amG α (toPolyG a) / amG α (toPolyG d)) :
    towerFractionFieldDerivG Dt (amG α (toPolyG res.rational.1) / amG α (toPolyG res.rational.2))
        + logResidueSumG Dt res.logs
      = amG α (toPolyG a) / amG α (toPolyG d) :=
  cIntegrateHyperexpFullGWf_sound Dt a d cands res lnum lden nrm fpPart hlden hgden
    hLaur hNrm hsome hLaurField hNrmField hrecon

end DeepWiki.SymbolicIntegration
