import DeepWiki.SymbolicIntegration.Computable.OneShotAssembly
import DeepWiki.SymbolicIntegration.Computable.Hyperexp.NormalCore

/-! # Unconditional soundness of the §5.9 hyperexponential normal-part driver (Bronstein §5.9)

`ComputableOneShotAssembly` proved the hyperexp one-shot for the raw driver `cIntegrateGFullWf` gated on
the integrability witness `∑c = 0`. The obstruction: `cIntegrateGFull`'s pure-normal branch emits the raw
§5.6 Rothstein–Trager logs, which overshoot a hyperexponential normal part by `R = η·∑c` (the
`extendDeriv_logPart_eq_div_add_residual` leftover); the §5.9 residual-feedback driver
`cIntegrateHyperexpNormalG` corrects the overshoot — `∫fₙ = logPart − ∫R`, absorbing `R` into a base
integral `∫R = crischDESolve 0 R`. This file proves that driver sound, unconditionally in `∑c` (no
`∑c = 0` side condition), modulo the base-RDE-oracle's `∫R`-soundness.

Two ingredients:

* The overshoot identity `hyperexp_residue_sum_eq_overshoot_add`: for a hyperexponential monomial
  `v = C b·X` (`Dt = η′·t`), squarefree `d = ∏_{α∈s}(t−α)`, `deg a < #s`, every root normal, the §5.6
  Rothstein–Trager residue sum `∑_α C(c_α)·D(log(t−α))` equals `algebraMap(C(b·∑c)) + a/d` over
  `RatFunc K` — unconditionally, no `∑c = 0`. Composes the unconditional decomposition
  `monomial_residue_sum_eq_cancel_add` (residue sum = cancel sum + a/d) with `hyperexp_cancel_sum_eq` (the
  hyperexp cancel sum is `algebraMap(C(b·∑c))`).
* The base residual `∫R`-soundness: the §5.9 feedback integrates `R ∈ α` by `crischDESolve 0 R` (the
  pure-integration `Dy = R`, one tower level down). The base oracle `CRischField.crischDESolve` has no
  abstract spec layer (`CRischFieldSpec` does not exist — see `ComputableTranscendentalOverAlgebraic`), so
  its soundness is only `native_decide`-validated today (e.g. `nNormInv_baseIntegral_eq_x`); we carry the
  conclusion `D(∫R) = R` as the explicit hypothesis `hintR`.

The driver soundness theorems (`cIntegrateHyperexpNormalGWf_sound` / `cIntegrateHyperexpFullGWf_sound`)
compose these two: the new rational part `g − ∫R` differentiates to `(a/d + R) − R = a/d`, the overshoot
`R` cancelling.

## Scope

The overshoot identity is fully proven, axiom-clean (`[propext, Classical.choice, Quot.sound]`, no
`native_decide`). The driver soundness is proven gated on two documented inputs: (a) the same abstract
engine bridges (`hherm`, `hform`, …) the primitive/hyperexp one-shots in `ComputableOneShotAssembly`
already take, and (b) the base-RDE-oracle residual `hintR : D(∫R) = R`, which is not abstractly available
because `crischDESolve` has no spec layer. So the unconditional-in-`∑c` hyperexp soundness reduces to the
base oracle's `∫R`-soundness — the opposite condition to `∑c = 0` (absorbing `∑c ≠ 0`, not requiring its
vanishing). -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

/-! ### The overshoot identity `D(logPart) = a/d + R` for the hyperexponential monomial

The raw §5.6 Rothstein–Trager log part `∑_α c_α·log(t−α)` of a hyperexponential normal part `fₙ = a/d`
overshoots: its derivative is `a/d + R`, not `a/d`, with the residual `R = b·∑c` (`b = η′`). This is the
`extendDeriv_logPart_eq_div_add_residual` claim, made precise and proven from two unconditional pieces in
`ComputableOneShotAssembly`'s `ResidueMatchTower`:

* `monomial_residue_sum_eq_cancel_add` — residue sum = (polynomial-part cancel sum) + a/d, for ANY monomial.
* `hyperexp_cancel_sum_eq` — for the hyperexp monomial `v = C b·X`, the cancel sum is `algebraMap(C(b·∑c))`.

So residue sum = `algebraMap(C(b·∑c)) + a/d`. No integrability witness — `∑c` is whatever it is, and the
overshoot `R = b·∑c` is carried, not killed. (When `∑c = 0` the overshoot vanishes and this collapses to
the residue match `= a/d`, the `hyperexp_residue_match_iff_sum_zero` regime.) -/

namespace ResidueMatchTower

variable {K : Type*} [Field K] [Differential K] [Algebra ℚ K]

/-- The hyperexponential overshoot identity `residue sum = algebraMap(C(b·∑c)) + a/d` (Bronstein §5.9, the
raw-log overshoot) — for the hyperexponential monomial `v = C b·X` (`Dt = η′·t`, `b = η′`), a squarefree
`d = ∏_{α∈s}(t−α)`, `deg a < #s`, every root normal (`(C b·X).eval α ≠ α′`), the §5.6 Rothstein–Trager
residue sum `∑_{α∈s} C(c_α)·(D(t−α)/(t−α))` (`c_α = a(α)/(Dd)(α)`, `D = extendDeriv
(implicitDeriv (C b·X))`) equals `algebraMap(C(b·∑_α c_α)) + a/d` over `RatFunc K` — unconditionally, no
`∑c = 0`. Composes `monomial_residue_sum_eq_cancel_add` (residue sum = cancel sum + a/d) with
`hyperexp_cancel_sum_eq` (the hyperexp cancel sum is `algebraMap(C(b·∑c))`). -/
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

/-! ### Task 1 (engine vocabulary): the overshoot residue match over `K = CFieldSpec.K α`

The hyperexp analog of `hyperexp_residue_match_list_engine`, **without** the `∑c = 0` witness: the
engine-shaped `List` sum over the per-root list equals `algebraMap(C(b·∑c)) + a/d` — the overshoot, not the
match. Transports `hyperexp_residue_sum_eq_overshoot_add` through the definitional `amG = algebraMap` and the
`towerFractionFieldDerivG` unfolding. -/

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

/-- The overshoot list↔Finset bridge in the engine's vocabulary — for a hyperexponential monomial
`toPolyG Dt = C b·X` (`b = η′`), a squarefree `d = ∏_{β∈s}(t−β)`, `deg a < #s`, every root normal, the
engine-shaped `List` sum over the per-root list of `(c_β, X − C β)` pairs equals `algebraMap(C(b·∑c)) + a/d`
over `RatFunc (CFieldSpec.K α)`, with `D = towerFractionFieldDerivG Dt` — unconditionally, no `∑c = 0`.
Transports `hyperexp_residue_sum_eq_overshoot_add` through `amG = algebraMap` and the
`towerFractionFieldDerivG` unfolding. -/
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

/-- The hyperexp engine overshoot residue sum — for a hyperexponential monomial `toPolyG Dt = C b·X`, a
squarefree `hDen` factored as `∏_{β∈s}(t−β)`, `deg (toPolyG hNum) < #s`, every root normal, and the engine
residue logs `logs` whose `(toK cv.1, toPolyG cv.2)`-images are the per-root list `s.toList.map (fun β =>
(residue β, X − C β))` (`hform`), the engine residue-match sum `∑_{(c,v)∈logs} amG(C(toK c))·(D(log v))`
equals `amG(C(b·∑c)) + amG(hNum)/amG(hDen)` over `RatFunc (CFieldSpec.K α)` — unconditionally, no
`∑c = 0`. Rewrites the engine sum through `hform` into the bridge's per-root form, which
`hyperexp_overshoot_list_engine` sends to `algebraMap(C(b·∑c)) + hNum/hDen`. -/
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

/-! ### Assembly: the reduced-case overshoot field identity `D(g) + logResidueSumG = a/d + R`

Composing the Hermite half `hherm` (`D(g) + h = a/d`) with the overshoot residue sum
`hyperexp_engine_overshoot` (`residue sum = R + h`, `R = algebraMap(C(b·∑c))`) gives the reduced-case
identity `D(g) + logResidueSumG = a/d + R`, unconditionally in `∑c`, gated only on the abstract Hermite
telescoping + per-root reassembly. -/

/-- The reduced-case overshoot field identity for the hyperexp case — for `res = cIntegrateReducedGWf Dt a
d cands`, a hyperexponential monomial `toPolyG Dt = C b·X`, and the Hermite half/per-root reassembly
hypotheses, the reduced-case identity `D(g) + logResidueSumG Dt res.logs = amG a/amG d + amG(C(b·∑c))`
holds over `RatFunc (CFieldSpec.K α)`, unconditionally in `∑c`. -/
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

/-! ### The §5.9 driver soundness `cIntegrateHyperexpNormalGWf_sound`

`cIntegrateHyperexpNormalGWf Dt a d cands` runs the reduced capstone `red = cIntegrateReducedGWf`, reads
`R = cHyperexpResidualG η red.logs`, integrates `∫R = crischDESolve 0 R` (the base-RDE oracle), and returns
`⟨(gnum − ∫R·gden, gden), red.logs⟩` — the rational part `g − ∫R`, same logs. The §5.9 feedback
`∫fₙ = logPart − ∫R`. Soundness: the new rational part differentiates to `D(g) − D(∫R) = (a/d + R) − R =
a/d` (the overshoot `R` cancels `D(∫R)` from the base oracle).

The two inputs beyond the abstract engine bridges (Hermite half `hherm`, per-root reassembly `hform`):
* `hintR` — the base-RDE-oracle residual: `D(∫R) = amG(C(toK R))` over the tower fraction field. The
  documented residual (the base oracle `crischDESolve` has no abstract spec layer — it is only
  `native_decide`-validated, e.g. `nNormInv_baseIntegral_eq_x`).
* `hRval` — the residual-read bridge `toK R = b·∑c` (the engine residual `R = η·∑(log coeffs)` reads to the
  abstract overshoot `b·∑_β c_β` of Task 1, via `cExpEtaG`'s `η = b` and `hform`'s fold↔Finset sum). Carried
  here as the field-level `amG(C(toK R)) = amG(C(b·∑c))`; the precise engine-internal bridge. -/

variable [CRischField α]

omit [CFieldSpec α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- The §5.9 driver's output shape — when `cIntegrateHyperexpNormalGWf Dt a d cands = some res`, with
`red = cIntegrateReducedGWf Dt a d cands` and the base oracle succeeding on
`R = cHyperexpResidualG (cExpEtaG Dt) red.logs`, the result is the same logs and rational part `g − ∫R`. -/
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

/-- The §5.9 driver soundness `D(∫fₙ) = fₙ`, unconditional in `∑c` — the soundness theorem for
`cIntegrateHyperexpNormalGWf`. The only non-abstract input is the base-oracle residual `hintR`, plus the
residual-read bridge `hRval`. -/
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
    rw [toPolyG_csubG, toPolyG_cmulG, map_sub, map_mul]
    have hsingle : toPolyG ([intR] : CPolyG α) = Polynomial.C (CFieldSpec.toK intR) := by
      rw [toPolyG_cons, toPolyG_nil, mul_zero, add_zero]
    rw [hsingle, sub_div, mul_div_assoc, div_self hAgden, mul_one]
  rw [hnewrat, map_sub, hintR, hRval]
  have hover := field_identity_of_cIntegrateReducedGWf_hyperexp_overshoot Dt a d cands s b
    hDt hherm hden hA hnorm hform
  set Dg := towerFractionFieldDerivG Dt (amG α (toPolyG gnum) / amG α (toPolyG gden)) with hDg
  set L := logResidueSumG Dt (CPolyG.cIntegrateReducedGWf Dt a d cands).logs with hL
  set R := amG α (C (b * ∑ β ∈ s,
    (toPolyG (cHermiteReduceTowerGWf Dt a d).2.1).eval β
      / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β)) with hR
  rw [show Dg - R + L = (Dg + L) - R by ring, hover, add_sub_cancel_right]

/-! ### The §5.9 driver soundness at the level-1 carrier `α = QFunNZG ℚ = ℚ(x)`

Instantiating the unconditional §5.9 driver soundness at `α = QFunNZG ℚ` (`CFieldSpec.K (QFunNZG ℚ) =
RatFunc ℚ`). The concrete `cIntegrateHyperexpNormalG = some res ⟹ D(res) = a/d` for a hyperexponential
monomial over `ℚ(x)(t)`, unconditional in `∑c`, reduced to the documented base-oracle residual. The local
instance bridges the carrier abbreviation to `RatFunc ℚ`. -/

/-- The engine carrier `CFieldSpec.K (QFunNZG ℚ)` is `RatFunc ℚ`, a `ℚ`-algebra. Local instance so the
`QFunNZG ℚ` deliverable synthesizes the **same** `Algebra ℚ` the bridge `towerFractionFieldDerivG` uses. -/
noncomputable local instance : Algebra ℚ (CFieldSpec.K (QFunNZG ℚ)) :=
  inferInstanceAs (Algebra ℚ (RatFunc ℚ))

/-- The §5.9 driver soundness over `ℚ(x)(t)`, unconditional in `∑c` — the `QFunNZG ℚ` instance of
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

/-! ### The full driver: `cIntegrateHyperexpFullGWf_sound` (§5.4 + §5.10 + §5.9)

`cIntegrateHyperexpFullGWf Dt a d cands` combines the §5.10 Laurent special part `fp + b/dₛ` (via
`cIntegrateHyperexpLaurentG η`) with the §5.9 normal part `cₙ/dₙ` (via `cIntegrateHyperexpNormalGWf`), returning
the rational part `(lnum/lden) + (gnum/gden)` with the normal logs. Soundness composes:
* the Laurent field identity `hLaurField : D(lnum/lden) = amG(fpPart)` — the §5.10 special-part correctness
  (a documented input; the Laurent special-part soundness is a separate piece, not in scope here);
* the §5.9 normal-part soundness `cIntegrateHyperexpNormalGWf_sound` for `D(gnum/gden) + logResidueSumG = cₙ/dₙ`;
* the canonical reconstruction `hrecon : amG(fpPart) + cₙ/dₙ = a/d` (the `canonicalRepresentationFastGWf`
  recombination, documented).
Then `D(res) + logResidueSumG = D(lnum/lden) + D(gnum/gden) + logResidueSumG = amG(fpPart) + cₙ/dₙ = a/d`.
The §5.10-special + §5.9-normal hyperexp integral, unconditional in `∑c`, reduced to the Laurent
special-part identity + the canonical reconstruction + the base-oracle residual. -/

omit [CFieldSpec α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- The full §5.10 + §5.9 driver's output shape — when `cIntegrateHyperexpFullGWf Dt a d cands = some
res`, with the Laurent part succeeding on the canonical split and the normal part succeeding, the result is
the combined rational part and the normal logs. -/
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

/-- The full §5.10 + §5.9 hyperexp driver soundness `D(∫f) = f`, unconditional in `∑c` — composes the
Laurent special-part field identity, the normal-part field identity, and the canonical reconstruction. -/
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
    rw [toPolyG_caddG, toPolyG_cmulG, toPolyG_cmulG, toPolyG_cmulG, map_add, map_mul, map_mul,
      map_mul]
    field_simp
  rw [hcombine, map_add, hLaurField]
  rw [add_assoc, hNrmField]
  exact hrecon

/-! ### Restatements against the intended wording (anonymous `example`s) -/

-- The overshoot identity: the raw §5.6 Rothstein–Trager log part of a hyperexp normal part differentiates
-- to `a/d + R`, not `a/d`, with residual `R = b·∑c` — `extendDeriv_logPart_eq_div_add_residual`, no
-- `∑c = 0`.
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

/-! ### Status — the §5.9 hyperexponential driver soundness, unconditional in `∑c`

The overshoot identity (`hyperexp_residue_sum_eq_overshoot_add` / `hyperexp_overshoot_list_engine` /
`hyperexp_engine_overshoot` / `field_identity_of_cIntegrateReducedGWf_hyperexp_overshoot`) is proven
axiom-clean (`[propext, Classical.choice, Quot.sound]`, no `native_decide`, no `sorry`), unconditionally in
`∑c`. The driver soundness theorems (`cIntegrateHyperexpNormalGWf_sound`/`…_qfunNZG`,
`cIntegrateHyperexpFullGWf_sound`) are proven gated on the abstract engine bridges (`hherm`, `hform`) plus
the base-RDE-oracle residual `hintR : D(∫R) = R` (`R ∈ α` a base element, e.g. `R = 1 ↦ ∫R = x`) — the
opposite condition to `∑c = 0` (absorbing `∑c ≠ 0`, not requiring its vanishing). `hintR` is not abstractly
available because `CRischField.crischDESolve` has no spec layer (`CRischFieldSpec` does not exist;
`crischDESolve 0 R` over `ℚ(x)` runs the §6 pipeline one tower level down, recursing to `ℚ`), so its
soundness is only `native_decide`-validated today (`nNormInv_baseIntegral_eq_x`,
`nVarNorm_baseIntegral_eq_xSq`). Building the abstract `crischDESolve` spec (the bridge
`instCRischFieldQFunNZG`-unfold → `cRischDEG` field-level soundness → reuse
`field_identity_of_cPolyRischDEGWf`) would close this residual. -/

end DeepWiki.SymbolicIntegration
