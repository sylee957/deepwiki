import DeepWiki.SymbolicIntegration.Engine.Hyperexp.NormalCore
import DeepWiki.SymbolicIntegration.Engine.ResidueMatchBridge

/-! # Soundness of the hyperexponential normal-part driver

`D(∫fₙ) = fₙ` for the residual-feedback hyperexponential normal-part driver, unconditional in the
residue sum `∑c`, reduced to the base-RDE oracle's residual soundness `D(∫R) = R`. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac

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

The overshoot identity restated on the engine's per-root `List` sum, transported through `am = algebraMap`
and the `towerFractionFieldDeriv` unfolding. -/

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

/-- Engine-vocabulary overshoot: the per-root `List` sum equals `am(C(b·∑c)) + a/d` over
`RatFunc (CFieldSpec.K α)`, with `D = towerFractionFieldDeriv Dt`, unconditional in `∑c`. -/
theorem hyperexp_overshoot_list_engine (Dt : DensePoly α) (s : Finset (CFieldSpec.K α))
    (a : (CFieldSpec.K α)[X]) (b : CFieldSpec.K α) (hDt : toPoly Dt = C b * X)
    (hA : a.degree < s.card) (hnorm : ∀ β ∈ s, (C b * X).eval β ≠ β′) :
    ((s.toList.map (fun β =>
          (a.eval β / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β,
            X - C β))).map
        (fun cv =>
          am α (C cv.1)
            * (towerFractionFieldDeriv Dt (am α cv.2) / am α cv.2))).sum
      = am α (C (b * ∑ β ∈ s,
            a.eval β / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β))
        + am α a / am α (Lagrange.nodal s id) := by
  show ((s.toList.map (fun β =>
          (a.eval β / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β,
            X - C β))).map
        (fun cv =>
          algebraMap (CFieldSpec.K α)[X] (RatFunc (CFieldSpec.K α)) (C cv.1)
            * (extendDeriv (Differential.implicitDeriv (toPoly Dt))
                  (algebraMap _ (RatFunc (CFieldSpec.K α)) cv.2)
                / algebraMap _ (RatFunc (CFieldSpec.K α)) cv.2))).sum = _
  rw [hDt]
  -- collapse `(s.toList.map f).map g`, then to the `Finset.sum` over `s`, then the K[X]-level overshoot
  rw [List.map_map, Finset.sum_map_toList]
  exact ResidueMatchTower.hyperexp_residue_sum_eq_overshoot_add s a b hA hnorm

/-- Engine residue-match overshoot: the log sum `∑_{(c,v)∈logs} am(C(toK c))·D(log v)` equals
`am(C(b·∑c)) + am(hNum)/am(hDen)` over `RatFunc (CFieldSpec.K α)`, given the per-root form `hform`,
unconditional in `∑c`. -/
theorem hyperexp_engine_overshoot (Dt : DensePoly α) (s : Finset (CFieldSpec.K α))
    (hNum hDen : DensePoly α) (b : CFieldSpec.K α) (logs : List (α × DensePoly α))
    (hDt : toPoly Dt = C b * X)
    (hden : toPoly hDen = Lagrange.nodal s id)
    (hA : (toPoly hNum).degree < s.card) (hnorm : ∀ β ∈ s, (C b * X).eval β ≠ β′)
    (hform : logs.map (fun cv => (CFieldSpec.toK cv.1, toPoly cv.2))
      = s.toList.map (fun β =>
          ((toPoly hNum).eval β
              / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β,
            X - C β))) :
    (logs.map (fun cv =>
          am α (Polynomial.C (CFieldSpec.toK cv.1))
            * (towerFractionFieldDeriv Dt (am α (toPoly cv.2)) / am α (toPoly cv.2)))).sum
      = am α (C (b * ∑ β ∈ s,
            (toPoly hNum).eval β
              / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β))
        + am α (toPoly hNum) / am α (toPoly hDen) := by
  -- the engine summand factors through `(toK cv.1, toPoly cv.2)`: rewrite the mapped list by `hform`
  have hsummand : (logs.map (fun cv =>
        am α (Polynomial.C (CFieldSpec.toK cv.1))
          * (towerFractionFieldDeriv Dt (am α (toPoly cv.2)) / am α (toPoly cv.2))))
      = (logs.map (fun cv => (CFieldSpec.toK cv.1, toPoly cv.2))).map
          (fun p => am α (Polynomial.C p.1)
            * (towerFractionFieldDeriv Dt (am α p.2) / am α p.2)) := by
    rw [List.map_map]; rfl
  rw [hsummand, hform, hden, List.map_map]
  -- now the per-root form of the bridge `hyperexp_overshoot_list_engine`
  have hbridge := hyperexp_overshoot_list_engine Dt s (toPoly hNum) b hDt hA hnorm
  rw [List.map_map] at hbridge
  exact hbridge

/-! ### The reduced-case overshoot field identity `D(g) + logResidueSum = a/d + R`

Composing the Hermite half with the overshoot residue sum. -/

/-- Reduced-case overshoot field identity: for `res = cIntegrateReduced Dt a d cands` and the Hermite
half/per-root hypotheses, `D(g) + logResidueSum Dt res.logs = am a/am d + am(C(b·∑c))` over
`RatFunc (CFieldSpec.K α)`, unconditional in `∑c`. -/
theorem field_identity_of_cIntegrateReducedG_hyperexp_overshoot [CPolyGcd DensePoly α]
    [CPolySquarefree DensePoly α] [CPolyResultant DensePoly]
    (Dt : DensePoly α) (a d : DensePoly α) (cands : List α) (s : Finset (CFieldSpec.K α))
    (b : CFieldSpec.K α)
    (hDt : toPoly Dt = C b * X)
    (hherm : towerFractionFieldDeriv Dt
            (am α (toPoly (DensePoly.cIntegrateReduced Dt a d cands).rational.1)
              / am α (toPoly (DensePoly.cIntegrateReduced Dt a d cands).rational.2))
          + am α (toPoly (cHermiteReduceTower Dt a d).2.1)
            / am α (toPoly (cHermiteReduceTower Dt a d).2.2)
        = am α (toPoly a) / am α (toPoly d))
    (hden : toPoly (cHermiteReduceTower Dt a d).2.2 = Lagrange.nodal s id)
    (hA : (toPoly (cHermiteReduceTower Dt a d).2.1).degree < s.card)
    (hnorm : ∀ β ∈ s, (C b * X).eval β ≠ β′)
    (hform : (DensePoly.cIntegrateReduced Dt a d cands).logs.map
          (fun cv => (CFieldSpec.toK cv.1, toPoly cv.2))
        = s.toList.map (fun β =>
            ((toPoly (cHermiteReduceTower Dt a d).2.1).eval β
                / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β,
              X - C β))) :
    towerFractionFieldDeriv Dt
        (am α (toPoly (DensePoly.cIntegrateReduced Dt a d cands).rational.1)
          / am α (toPoly (DensePoly.cIntegrateReduced Dt a d cands).rational.2))
        + logResidueSum Dt (DensePoly.cIntegrateReduced Dt a d cands).logs
      = am α (toPoly a) / am α (toPoly d)
        + am α (C (b * ∑ β ∈ s,
            (toPoly (cHermiteReduceTower Dt a d).2.1).eval β
              / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β)) := by
  rw [logResidueSumG_eq_logDeriv_sum Dt (DensePoly.cIntegrateReduced Dt a d cands).logs,
    hyperexp_engine_overshoot Dt s (cHermiteReduceTower Dt a d).2.1
      (cHermiteReduceTower Dt a d).2.2 b
      (DensePoly.cIntegrateReduced Dt a d cands).logs hDt hden hA hnorm hform]
  set Dg := towerFractionFieldDeriv Dt
    (am α (toPoly (DensePoly.cIntegrateReduced Dt a d cands).rational.1)
      / am α (toPoly (DensePoly.cIntegrateReduced Dt a d cands).rational.2)) with hDg
  set h := am α (toPoly (cHermiteReduceTower Dt a d).2.1)
    / am α (toPoly (cHermiteReduceTower Dt a d).2.2) with hh
  set R := am α (C (b * ∑ β ∈ s,
    (toPoly (cHermiteReduceTower Dt a d).2.1).eval β
      / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β)) with hR
  rw [show Dg + (R + h) = (Dg + h) + R by ring, hherm]

/-! ### The normal-part driver soundness `cIntegrateHyperexpNormalG_sound`

`cIntegrateHyperexpNormal` runs the reduced capstone, reads `R = cHyperexpResidual η red.logs`,
integrates `∫R` by the base-RDE oracle, and subtracts it; the new rational part `g − ∫R` differentiates to
`(a/d + R) − R = a/d`. The residual `hintR : D(∫R) = R` and the residual-read bridge `hRval : toK R = b·∑c`
are carried as hypotheses. -/

variable [CRischField α]

omit [CFieldSpec α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- Output shape of `cIntegrateHyperexpNormal`: when it returns `some res` and the base oracle succeeds
on `R`, `res` has the same logs and rational part `g − ∫R`. -/
private theorem cIntegrateHyperexpNormalG_shape [CPolyGcd DensePoly α]
    [CPolySquarefree DensePoly α] [CPolyResultant DensePoly] (Dt : DensePoly α)
    (a d : DensePoly α) (cands : List α) (res : IntegralResult α) (intR : α)
    (hintRsome : CRischField.crischDESolve (CCommRing.zero : α)
        (cHyperexpResidual (cExpEta Dt) (DensePoly.cIntegrateReduced Dt a d cands).logs)
      = some intR)
    (hsome : DensePoly.cIntegrateHyperexpNormal Dt a d cands = some res) :
    res = ⟨(csub (DensePoly.cIntegrateReduced Dt a d cands).rational.1
              (cmul [intR] (DensePoly.cIntegrateReduced Dt a d cands).rational.2),
            (DensePoly.cIntegrateReduced Dt a d cands).rational.2),
          (DensePoly.cIntegrateReduced Dt a d cands).logs⟩ := by
  rw [DensePoly.cIntegrateHyperexpNormal, DensePoly.cCorrectHyperexpNormal] at hsome
  simp only [hintRsome, CPolyEngine.ofCoeffList_dense_eq, CPolyEngine.mul_dense_eq,
    CPolyEngine.sub_dense_eq] at hsome
  exact (Option.some.injEq _ _ ▸ hsome).symm

/-- Normal-part driver soundness `D(∫fₙ) = fₙ` for `cIntegrateHyperexpNormal`, unconditional in `∑c`,
given the base-oracle residual `hintR` and the residual-read bridge `hRval`. -/
theorem cIntegrateHyperexpNormalG_sound [CPolyGcd DensePoly α]
    [CPolySquarefree DensePoly α] [CPolyResultant DensePoly]
    (Dt : DensePoly α) (a d : DensePoly α)
    (cands : List α) (res : IntegralResult α) (intR : α) (s : Finset (CFieldSpec.K α))
    (b : CFieldSpec.K α)
    (hDt : toPoly Dt = C b * X)
    (hgden : toPoly (DensePoly.cIntegrateReduced Dt a d cands).rational.2 ≠ 0)
    (hintRsome : CRischField.crischDESolve (CCommRing.zero : α)
        (cHyperexpResidual (cExpEta Dt) (DensePoly.cIntegrateReduced Dt a d cands).logs)
      = some intR)
    (hsome : DensePoly.cIntegrateHyperexpNormal Dt a d cands = some res)
    (hherm : towerFractionFieldDeriv Dt
            (am α (toPoly (DensePoly.cIntegrateReduced Dt a d cands).rational.1)
              / am α (toPoly (DensePoly.cIntegrateReduced Dt a d cands).rational.2))
          + am α (toPoly (cHermiteReduceTower Dt a d).2.1)
            / am α (toPoly (cHermiteReduceTower Dt a d).2.2)
        = am α (toPoly a) / am α (toPoly d))
    (hden : toPoly (cHermiteReduceTower Dt a d).2.2 = Lagrange.nodal s id)
    (hA : (toPoly (cHermiteReduceTower Dt a d).2.1).degree < s.card)
    (hnorm : ∀ β ∈ s, (C b * X).eval β ≠ β′)
    (hform : (DensePoly.cIntegrateReduced Dt a d cands).logs.map
          (fun cv => (CFieldSpec.toK cv.1, toPoly cv.2))
        = s.toList.map (fun β =>
            ((toPoly (cHermiteReduceTower Dt a d).2.1).eval β
                / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β,
              X - C β)))
    (hintR : towerFractionFieldDeriv Dt (am α (Polynomial.C (CFieldSpec.toK intR)))
        = am α (Polynomial.C (CFieldSpec.toK
            (cHyperexpResidual (cExpEta Dt)
              (DensePoly.cIntegrateReduced Dt a d cands).logs))))
    (hRval : am α (Polynomial.C (CFieldSpec.toK
            (cHyperexpResidual (cExpEta Dt)
              (DensePoly.cIntegrateReduced Dt a d cands).logs)))
        = am α (C (b * ∑ β ∈ s,
            (toPoly (cHermiteReduceTower Dt a d).2.1).eval β
              / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β))) :
    towerFractionFieldDeriv Dt (am α (toPoly res.rational.1) / am α (toPoly res.rational.2))
        + logResidueSum Dt res.logs
      = am α (toPoly a) / am α (toPoly d) := by
  rw [cIntegrateHyperexpNormalG_shape Dt a d cands res intR hintRsome hsome]
  set gnum := (DensePoly.cIntegrateReduced Dt a d cands).rational.1 with hgnum
  set gden := (DensePoly.cIntegrateReduced Dt a d cands).rational.2 with hgdenE
  have hAgden : am α (toPoly gden) ≠ 0 := am_ne_zero hgden
  have hnewrat : am α (toPoly (csub gnum (cmul [intR] gden))) / am α (toPoly gden)
      = am α (toPoly gnum) / am α (toPoly gden) - am α (Polynomial.C (CFieldSpec.toK intR)) := by
    simp only [denote, map_sub, map_mul, mul_zero, add_zero]
    rw [sub_div, mul_div_assoc, div_self hAgden, mul_one]
  rw [hnewrat, map_sub, hintR, hRval]
  have hover := field_identity_of_cIntegrateReducedG_hyperexp_overshoot Dt a d cands s b
    hDt hherm hden hA hnorm hform
  set Dg := towerFractionFieldDeriv Dt (am α (toPoly gnum) / am α (toPoly gden)) with hDg
  set L := logResidueSum Dt (DensePoly.cIntegrateReduced Dt a d cands).logs with hL
  set R := am α (C (b * ∑ β ∈ s,
    (toPoly (cHermiteReduceTower Dt a d).2.1).eval β
      / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β)) with hR
  rw [show Dg - R + L = (Dg + L) - R by ring, hover, add_sub_cancel_right]

/-! ### The driver soundness at the level-1 carrier `α = DenseFrac ℚ = ℚ(x)`

The normal-part driver soundness instantiated at `α = DenseFrac ℚ` (`CFieldSpec.K (DenseFrac ℚ) = RatFunc ℚ`),
unconditional in `∑c`. -/

/-- Local instance: the engine carrier `CFieldSpec.K (DenseFrac ℚ)` is `RatFunc ℚ` as a `ℚ`-algebra, matching
the `Algebra ℚ` the bridge `towerFractionFieldDeriv` uses. -/
noncomputable local instance : Algebra ℚ (CFieldSpec.K (DenseFrac ℚ)) :=
  inferInstanceAs (Algebra ℚ (RatFunc ℚ))

/-- Normal-part driver soundness over `ℚ(x)(t)`, unconditional in `∑c` — the `DenseFrac ℚ` instance of
`cIntegrateHyperexpNormalG_sound`. -/
theorem cIntegrateHyperexpNormalG_sound_qfunNZG (Dt : DensePoly (DenseFrac ℚ))
    (a d : DensePoly (DenseFrac ℚ)) (cands : List (DenseFrac ℚ)) (res : IntegralResult (DenseFrac ℚ))
    (intR : DenseFrac ℚ) (s : Finset (CFieldSpec.K (DenseFrac ℚ))) (b : CFieldSpec.K (DenseFrac ℚ))
    (hDt : toPoly Dt = C b * X)
    (hgden : toPoly (DensePoly.cIntegrateReduced Dt a d cands).rational.2 ≠ 0)
    (hintRsome : CRischField.crischDESolve (CCommRing.zero : DenseFrac ℚ)
        (cHyperexpResidual (cExpEta Dt) (DensePoly.cIntegrateReduced Dt a d cands).logs)
      = some intR)
    (hsome : DensePoly.cIntegrateHyperexpNormal Dt a d cands = some res)
    (hherm : towerFractionFieldDeriv Dt
            (am (DenseFrac ℚ) (toPoly (DensePoly.cIntegrateReduced Dt a d cands).rational.1)
              / am (DenseFrac ℚ) (toPoly (DensePoly.cIntegrateReduced Dt a d cands).rational.2))
          + am (DenseFrac ℚ) (toPoly (cHermiteReduceTower Dt a d).2.1)
            / am (DenseFrac ℚ) (toPoly (cHermiteReduceTower Dt a d).2.2)
        = am (DenseFrac ℚ) (toPoly a) / am (DenseFrac ℚ) (toPoly d))
    (hden : toPoly (cHermiteReduceTower Dt a d).2.2 = Lagrange.nodal s id)
    (hA : (toPoly (cHermiteReduceTower Dt a d).2.1).degree < s.card)
    (hnorm : ∀ β ∈ s, (C b * X).eval β ≠ β′)
    (hform : (DensePoly.cIntegrateReduced Dt a d cands).logs.map
          (fun cv => (CFieldSpec.toK cv.1, toPoly cv.2))
        = s.toList.map (fun β =>
            ((toPoly (cHermiteReduceTower Dt a d).2.1).eval β
                / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β,
              X - C β)))
    (hintR : towerFractionFieldDeriv Dt (am (DenseFrac ℚ) (Polynomial.C (CFieldSpec.toK intR)))
        = am (DenseFrac ℚ) (Polynomial.C (CFieldSpec.toK
            (cHyperexpResidual (cExpEta Dt)
              (DensePoly.cIntegrateReduced Dt a d cands).logs))))
    (hRval : am (DenseFrac ℚ) (Polynomial.C (CFieldSpec.toK
            (cHyperexpResidual (cExpEta Dt)
              (DensePoly.cIntegrateReduced Dt a d cands).logs)))
        = am (DenseFrac ℚ) (C (b * ∑ β ∈ s,
            (toPoly (cHermiteReduceTower Dt a d).2.1).eval β
              / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β))) :
    towerFractionFieldDeriv Dt
        (am (DenseFrac ℚ) (toPoly res.rational.1) / am (DenseFrac ℚ) (toPoly res.rational.2))
        + logResidueSum Dt res.logs
      = am (DenseFrac ℚ) (toPoly a) / am (DenseFrac ℚ) (toPoly d) :=
  cIntegrateHyperexpNormalG_sound Dt a d cands res intR s b hDt hgden hintRsome hsome hherm hden
    hA hnorm hform hintR hRval

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

-- The reduced-capstone overshoot identity: `cIntegrateReduced` has the same hyperexp overshoot
-- statement.
example [CPolyGcd DensePoly α] [CPolySquarefree DensePoly α] [CPolyResultant DensePoly]
    (Dt : DensePoly α) (a d : DensePoly α) (cands : List α)
    (s : Finset (CFieldSpec.K α)) (b : CFieldSpec.K α) (hDt : toPoly Dt = C b * X)
    (hherm : towerFractionFieldDeriv Dt
            (am α (toPoly (DensePoly.cIntegrateReduced Dt a d cands).rational.1)
              / am α (toPoly (DensePoly.cIntegrateReduced Dt a d cands).rational.2))
          + am α (toPoly (cHermiteReduceTower Dt a d).2.1)
            / am α (toPoly (cHermiteReduceTower Dt a d).2.2)
        = am α (toPoly a) / am α (toPoly d))
    (hden : toPoly (cHermiteReduceTower Dt a d).2.2 = Lagrange.nodal s id)
    (hA : (toPoly (cHermiteReduceTower Dt a d).2.1).degree < s.card)
    (hnorm : ∀ β ∈ s, (C b * X).eval β ≠ β′)
    (hform : (DensePoly.cIntegrateReduced Dt a d cands).logs.map
          (fun cv => (CFieldSpec.toK cv.1, toPoly cv.2))
        = s.toList.map (fun β =>
            ((toPoly (cHermiteReduceTower Dt a d).2.1).eval β
                / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β,
              X - C β))) :
    towerFractionFieldDeriv Dt
        (am α (toPoly (DensePoly.cIntegrateReduced Dt a d cands).rational.1)
          / am α (toPoly (DensePoly.cIntegrateReduced Dt a d cands).rational.2))
        + logResidueSum Dt (DensePoly.cIntegrateReduced Dt a d cands).logs
      = am α (toPoly a) / am α (toPoly d)
        + am α (C (b * ∑ β ∈ s,
            (toPoly (cHermiteReduceTower Dt a d).2.1).eval β
              / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β)) :=
  field_identity_of_cIntegrateReducedG_hyperexp_overshoot Dt a d cands s b
    hDt hherm hden hA hnorm hform

-- The §5.9 normal-part driver soundness: `cIntegrateHyperexpNormal = some res ⟹ D(res) = a/d` under
-- the same residual-oracle hypothesis.
example [CPolyGcd DensePoly α] [CPolySquarefree DensePoly α] [CPolyResultant DensePoly]
    (Dt : DensePoly α) (a d : DensePoly α) (cands : List α)
    (res : IntegralResult α) (intR : α) (s : Finset (CFieldSpec.K α)) (b : CFieldSpec.K α)
    (hDt : toPoly Dt = C b * X)
    (hgden : toPoly (DensePoly.cIntegrateReduced Dt a d cands).rational.2 ≠ 0)
    (hintRsome : CRischField.crischDESolve (CCommRing.zero : α)
        (cHyperexpResidual (cExpEta Dt) (DensePoly.cIntegrateReduced Dt a d cands).logs)
      = some intR)
    (hsome : DensePoly.cIntegrateHyperexpNormal Dt a d cands = some res)
    (hherm : towerFractionFieldDeriv Dt
            (am α (toPoly (DensePoly.cIntegrateReduced Dt a d cands).rational.1)
              / am α (toPoly (DensePoly.cIntegrateReduced Dt a d cands).rational.2))
          + am α (toPoly (cHermiteReduceTower Dt a d).2.1)
            / am α (toPoly (cHermiteReduceTower Dt a d).2.2)
        = am α (toPoly a) / am α (toPoly d))
    (hden : toPoly (cHermiteReduceTower Dt a d).2.2 = Lagrange.nodal s id)
    (hA : (toPoly (cHermiteReduceTower Dt a d).2.1).degree < s.card)
    (hnorm : ∀ β ∈ s, (C b * X).eval β ≠ β′)
    (hform : (DensePoly.cIntegrateReduced Dt a d cands).logs.map
          (fun cv => (CFieldSpec.toK cv.1, toPoly cv.2))
        = s.toList.map (fun β =>
            ((toPoly (cHermiteReduceTower Dt a d).2.1).eval β
                / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β,
              X - C β)))
    (hintR : towerFractionFieldDeriv Dt (am α (Polynomial.C (CFieldSpec.toK intR)))
        = am α (Polynomial.C (CFieldSpec.toK
            (cHyperexpResidual (cExpEta Dt)
              (DensePoly.cIntegrateReduced Dt a d cands).logs))))
    (hRval : am α (Polynomial.C (CFieldSpec.toK
            (cHyperexpResidual (cExpEta Dt)
              (DensePoly.cIntegrateReduced Dt a d cands).logs)))
        = am α (C (b * ∑ β ∈ s,
            (toPoly (cHermiteReduceTower Dt a d).2.1).eval β
              / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β))) :
    towerFractionFieldDeriv Dt (am α (toPoly res.rational.1) / am α (toPoly res.rational.2))
        + logResidueSum Dt res.logs
      = am α (toPoly a) / am α (toPoly d) :=
  cIntegrateHyperexpNormalG_sound Dt a d cands res intR s b hDt hgden hintRsome hsome hherm hden
    hA hnorm hform hintR hRval

end DeepWiki.SymbolicIntegration
