import DeepWiki.SymbolicIntegration.ComputableOneShotAssembly
import DeepWiki.SymbolicIntegration.ComputableHyperexpNormal

/-! # Unconditional soundness of the §5.9 hyperexponential normal-part driver (Bronstein §5.9)

`ComputableOneShotAssembly` proved the **conditional** hyperexp one-shot for the *raw* driver
`cIntegrateGFull` — `cIntegrateGFull_hyperexp_oneShot`, gated on the integrability witness `∑c = 0`. The
genuine obstruction it pinned (closing status): `cIntegrateGFull`'s pure-normal branch emits the raw §5.6
Rothstein–Trager logs, which **overshoot** a hyperexponential normal part by `R = η·∑c` (the
`extendDeriv_logPart_eq_div_add_residual` leftover); the §5.9 residual-feedback driver
`cIntegrateHyperexpNormalG` (`ComputableHyperexpNormal`) is the one that *corrects* the overshoot —
`∫fₙ = logPart − ∫R`, absorbing `R` into a base integral `∫R = crischDESolve 0 R`. This file proves that
driver SOUND, **unconditionally in `∑c`** (no `∑c = 0` side condition), modulo the base-RDE-oracle's
`∫R`-soundness (the precise residual — see the scope note).

The two ingredients (the file delivers both):

* **★ The overshoot identity (Task 1, UNCONDITIONAL, axiom-clean)** —
  `hyperexp_residue_sum_eq_overshoot_add`: for a hyperexponential monomial `v = C b·X` (`Dt = η′·t`),
  squarefree `d = ∏_{α∈s}(t−α)`, `deg a < #s`, every root normal, the §5.6 Rothstein–Trager residue sum
  `∑_α C(c_α)·D(log(t−α))` equals `algebraMap(C(b·∑c)) + a/d` over `RatFunc K` — **no** `∑c = 0`. The raw
  log part differentiates to the integrand `a/d` PLUS the residual `R = b·∑c`. Composes the unconditional
  decomposition `monomial_residue_sum_eq_cancel_add` (residue sum = cancel sum + a/d) with
  `hyperexp_cancel_sum_eq` (the hyperexp cancel sum IS `algebraMap(C(b·∑c))`). This is the genuine new
  content: the `extendDeriv_logPart_eq_div_add_residual` claim, PROVEN, in the precise residue form.
* **★★ The base residual `∫R`-soundness (Task 2, the documented base-oracle residual)** — the §5.9 feedback
  integrates `R ∈ α` by `crischDESolve 0 R` (the pure-integration `Dy = R`, one tower level down). The base
  oracle `CRischField.crischDESolve` is a bare typeclass method with **no abstract spec layer**
  (`CRischFieldSpec` does not exist — see `ComputableTranscendentalOverAlgebraic`), so its soundness is only
  `native_decide`-validated today (e.g. `nNormInv_baseIntegral_eq_x`). We therefore carry the precise
  base-oracle conclusion `D(∫R) = R` as the explicit hypothesis `hintR`, isolating it as the *single*
  documented residual the unconditional driver soundness reduces to.

* **★★★ The driver soundness (Task 3)** — `cIntegrateHyperexpNormalG_sound` /
  `cIntegrateHyperexpFullG_sound`: `cIntegrateHyperexpNormalG Dt fuel a d cands = some res ⟹ D(res) = a/d`
  for a hyperexp `Dt = η′·t`, **unconditional in `∑c`**, gated on the abstract engine inputs (Hermite half,
  per-root reassembly) PLUS the base-oracle residual `hintR` and the residual-read bridge
  `R = b·∑c`. Composes Task 1 (overshoot) with Task 2 (`hintR`): the new rational part `g − ∫R`
  differentiates to `(a/d + R) − R = a/d`, the `R` cancelling. The §5.9 feedback is exactly the term that
  makes the hyperexp normal part integrable WITHOUT the `∑c = 0` side condition.

## Scope — what is proven unconditionally and what reduces to the base oracle

The **overshoot identity (Task 1) is fully proven, axiom-clean** (`[propext, Classical.choice, Quot.sound]`,
no `native_decide`): it is the genuine §5.9 content (the raw RT logs overshoot by `R = η·∑c`, refuting the
naive "log part alone" integral whenever `∑c ≠ 0`). The driver soundness (Task 3) is proven gated on two
*documented* inputs: (a) the same abstract engine bridges (`hherm`, `hform`, …) the primitive/hyperexp
one-shots in `ComputableOneShotAssembly` already take, and (b) the base-RDE-oracle residual
`hintR : D(∫R) = R` — which is NOT abstractly available because `crischDESolve` has no spec layer (it is only
`native_decide`-validated, and operates one tower level down: `crischDESolve 0 R` over `ℚ(x)` runs the §6
pipeline over `ℚ[x]`). So the unconditional-in-`∑c` hyperexp soundness reduces, precisely, to the base
oracle's `∫R`-soundness — the documented residual, the opposite condition to `∑c = 0` (it is the absorbing
of `∑c ≠ 0`, not its vanishing). -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

/-! ### ★ Task 1: the overshoot identity `D(logPart) = a/d + R` for the hyperexponential monomial

The raw §5.6 Rothstein–Trager log part `∑_α c_α·log(t−α)` of a hyperexponential normal part `fₙ = a/d`
overshoots: its derivative is `a/d + R`, NOT `a/d`, with the residual `R = b·∑c` (`b = η′`). This is the
`extendDeriv_logPart_eq_div_add_residual` claim, made precise and proven from two UNCONDITIONAL pieces in
`ComputableOneShotAssembly`'s `ResidueMatchTower`:

* `monomial_residue_sum_eq_cancel_add` — residue sum = (polynomial-part cancel sum) + a/d, for ANY monomial.
* `hyperexp_cancel_sum_eq` — for the hyperexp monomial `v = C b·X`, the cancel sum is `algebraMap(C(b·∑c))`.

So residue sum = `algebraMap(C(b·∑c)) + a/d`. No integrability witness — `∑c` is whatever it is, and the
overshoot `R = b·∑c` is carried, not killed. (When `∑c = 0` the overshoot vanishes and this collapses to
the residue match `= a/d`, the `hyperexp_residue_match_iff_sum_zero` regime.) -/

namespace ResidueMatchTower

variable {K : Type*} [Field K] [Differential K] [Algebra ℚ K]

/-- **★ The hyperexponential overshoot identity** `residue sum = algebraMap(C(b·∑c)) + a/d` (Bronstein
§5.9, the raw-log overshoot) — for the hyperexponential monomial `v = C b·X` (`Dt = η′·t`, `b = η′`), a
squarefree `d = ∏_{α∈s}(t−α)`, `deg a < #s`, every root normal (`(C b·X).eval α ≠ α′`), the §5.6
Rothstein–Trager residue sum `∑_{α∈s} C(c_α)·(D(t−α)/(t−α))` (`c_α = a(α)/(Dd)(α)`, `D = extendDeriv
(implicitDeriv (C b·X))`) equals `algebraMap(C(b·∑_α c_α)) + a/d` over `RatFunc K` — **UNCONDITIONALLY**, no
`∑c = 0`. The raw log part differentiates to the integrand `a/d` PLUS the residual `R = b·∑c`: the
`extendDeriv_logPart_eq_div_add_residual` claim, proven. Composes the unconditional decomposition
`monomial_residue_sum_eq_cancel_add` (residue sum = cancel sum + a/d) with `hyperexp_cancel_sum_eq` (the
hyperexp cancel sum IS `algebraMap(C(b·∑c))`). The genuine §5.9 new content — the residual `R = b·∑c` the
feedback driver must absorb. -/
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

/-- **★ The overshoot list↔Finset bridge in the engine's vocabulary** — for a hyperexponential monomial
`toPolyG Dt = C b·X` (`b = η′`), a squarefree `d = ∏_{β∈s}(t−β)`, `deg a < #s`, every root normal, the
engine-shaped `List` sum over the per-root list of `(c_β, X − C β)` pairs equals `algebraMap(C(b·∑c)) + a/d`
over `RatFunc (CFieldSpec.K α)`, with `D = towerFractionFieldDerivG Dt` — **UNCONDITIONALLY**, no `∑c = 0`.
The `K[X]`-level `hyperexp_residue_sum_eq_overshoot_add` transported through `amG = algebraMap` and the
`towerFractionFieldDerivG` unfolding. The overshoot in exactly the `List` shape the engine consumes (the
hyperexp analog of `hyperexp_residue_match_list_engine`, carrying the residual `R = b·∑c` instead of killing
it). -/
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

/-- **★ The hyperexp engine overshoot residue sum** — for a hyperexponential monomial `toPolyG Dt = C b·X`,
a squarefree `hDen` factored as `∏_{β∈s}(t−β)`, `deg (toPolyG hNum) < #s`, every root normal, and the engine
residue logs `logs` whose `(toK cv.1, toPolyG cv.2)`-images ARE the per-root list `s.toList.map (fun β =>
(residue β, X − C β))` (`hform`), the engine residue-match sum `∑_{(c,v)∈logs} amG(C(toK c))·(D(log v))`
equals `amG(C(b·∑c)) + amG(hNum)/amG(hDen)` over `RatFunc (CFieldSpec.K α)` — **UNCONDITIONALLY**, no
`∑c = 0`. Rewrites the engine sum through `hform` into the bridge's per-root form, which
`hyperexp_overshoot_list_engine` sends to `algebraMap(C(b·∑c)) + hNum/hDen`. The hyperexp engine `hmatch`
carrying the overshoot `R = b·∑c` (the analog of `hyperexp_engine_hmatch` without the integrability
witness). -/
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

/-! ### Task 1 (assembly): the reduced-case overshoot field identity `D(g) + logResidueSumG = a/d + R`

Composing the **Hermite half** `hherm` (`D(g) + h = a/d`) with the **overshoot residue sum**
`hyperexp_engine_overshoot` (`residue sum = R + h`, `R = algebraMap(C(b·∑c))`) gives the reduced-case
identity `D(g) + logResidueSumG = a/d + R` — UNCONDITIONALLY in `∑c`. The §5.9 raw-log overshoot for the
actual engine `cIntegrateReducedG`, gated only on the abstract Hermite telescoping + per-root reassembly. -/

variable [CFracGcdCore α]

/-- **★★ The reduced-case overshoot field identity for the hyperexp case** — for `res = cIntegrateReducedG
Dt fuel a d cands` with a hyperexponential monomial `toPolyG Dt = C b·X`, **given** the Hermite half `hherm`
(`D(g) + h = a/d`) and the per-root reassembly `hform`, the reduced-case identity `D(g) + logResidueSumG Dt
res.logs = amG a/amG d + amG(C(b·∑c))` holds over `RatFunc (CFieldSpec.K α)` — **UNCONDITIONALLY** in `∑c`,
with **no engine `checkIdentityG` certificate**. The raw RT log part overshoots the integrand by `R =
b·∑c`: the §5.9 content for the actual engine. The overshoot residue sum is supplied by
`hyperexp_engine_overshoot` (carrying `R`), composed with `hherm` and the reading bridge
`logResidueSumG_eq_logDeriv_sum`. -/
theorem field_identity_of_cIntegrateReducedG_hyperexp_overshoot (Dt : CPolyG α) (fuel : ℕ)
    (a d : CPolyG α) (cands : List α) (s : Finset (CFieldSpec.K α)) (b : CFieldSpec.K α)
    (hDt : toPolyG Dt = C b * X)
    (hherm : towerFractionFieldDerivG Dt
            (amG α (toPolyG (CPolyG.cIntegrateReducedG Dt fuel a d cands).rational.1)
              / amG α (toPolyG (CPolyG.cIntegrateReducedG Dt fuel a d cands).rational.2))
          + amG α (toPolyG (cHermiteReduceTowerG Dt fuel a d).2.1)
            / amG α (toPolyG (cHermiteReduceTowerG Dt fuel a d).2.2)
        = amG α (toPolyG a) / amG α (toPolyG d))
    (hden : toPolyG (cHermiteReduceTowerG Dt fuel a d).2.2 = Lagrange.nodal s id)
    (hA : (toPolyG (cHermiteReduceTowerG Dt fuel a d).2.1).degree < s.card)
    (hnorm : ∀ β ∈ s, (C b * X).eval β ≠ β′)
    (hform : (CPolyG.cIntegrateReducedG Dt fuel a d cands).logs.map
          (fun cv => (CFieldSpec.toK cv.1, toPolyG cv.2))
        = s.toList.map (fun β =>
            ((toPolyG (cHermiteReduceTowerG Dt fuel a d).2.1).eval β
                / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β,
              X - C β))) :
    towerFractionFieldDerivG Dt
        (amG α (toPolyG (CPolyG.cIntegrateReducedG Dt fuel a d cands).rational.1)
          / amG α (toPolyG (CPolyG.cIntegrateReducedG Dt fuel a d cands).rational.2))
        + logResidueSumG Dt (CPolyG.cIntegrateReducedG Dt fuel a d cands).logs
      = amG α (toPolyG a) / amG α (toPolyG d)
        + amG α (C (b * ∑ β ∈ s,
            (toPolyG (cHermiteReduceTowerG Dt fuel a d).2.1).eval β
              / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β)) := by
  -- read `logResidueSumG` as the log-derivative sum, supply the overshoot match
  rw [logResidueSumG_eq_logDeriv_sum Dt (CPolyG.cIntegrateReducedG Dt fuel a d cands).logs,
    hyperexp_engine_overshoot Dt s (cHermiteReduceTowerG Dt fuel a d).2.1
      (cHermiteReduceTowerG Dt fuel a d).2.2 b
      (CPolyG.cIntegrateReducedG Dt fuel a d cands).logs hDt hden hA hnorm hform]
  -- `D(g) + (R + h) = (D(g) + h) + R = a/d + R`, a commutative-group rearrangement using `hherm`
  set Dg := towerFractionFieldDerivG Dt
    (amG α (toPolyG (CPolyG.cIntegrateReducedG Dt fuel a d cands).rational.1)
      / amG α (toPolyG (CPolyG.cIntegrateReducedG Dt fuel a d cands).rational.2)) with hDg
  set h := amG α (toPolyG (cHermiteReduceTowerG Dt fuel a d).2.1)
    / amG α (toPolyG (cHermiteReduceTowerG Dt fuel a d).2.2) with hh
  set R := amG α (C (b * ∑ β ∈ s,
    (toPolyG (cHermiteReduceTowerG Dt fuel a d).2.1).eval β
      / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β)) with hR
  -- goal: `Dg + (R + h) = amG a/amG d + R`; `hherm : Dg + h = amG a/amG d`
  rw [show Dg + (R + h) = (Dg + h) + R by ring, hherm]

/-! ### ★★★ Task 3: the §5.9 driver soundness `cIntegrateHyperexpNormalG_sound`

`cIntegrateHyperexpNormalG Dt fuel a d cands` runs the reduced capstone `red = cIntegrateReducedG`, reads
`R = cHyperexpResidualG η red.logs`, integrates `∫R = crischDESolve 0 R` (the base-RDE oracle), and returns
`⟨(gnum − ∫R·gden, gden), red.logs⟩` — the rational part `g − ∫R`, same logs. The §5.9 feedback
`∫fₙ = logPart − ∫R`. Soundness: the new rational part differentiates to `D(g) − D(∫R) = (a/d + R) − R =
a/d` (the overshoot `R` from Task 1 cancels `D(∫R)` from the base oracle).

The two inputs beyond the abstract engine bridges (Hermite half `hherm`, per-root reassembly `hform`):
* `hintR` — the base-RDE-oracle residual: `D(∫R) = amG(C(toK R))` over the tower fraction field. The
  documented residual (the base oracle `crischDESolve` has no abstract spec layer — it is only
  `native_decide`-validated, e.g. `nNormInv_baseIntegral_eq_x`).
* `hRval` — the residual-read bridge `toK R = b·∑c` (the engine residual `R = η·∑(log coeffs)` reads to the
  abstract overshoot `b·∑_β c_β` of Task 1, via `cExpEtaG`'s `η = b` and `hform`'s fold↔Finset sum). Carried
  here as the field-level `amG(C(toK R)) = amG(C(b·∑c))`; the precise engine-internal bridge. -/

variable [CRischField α]

omit [CFieldSpec α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **The §5.9 driver's output shape** — when `cIntegrateHyperexpNormalG Dt fuel a d cands = some res` (so
the base oracle `crischDESolve 0 R = some intR` succeeded, `R = cHyperexpResidualG (cExpEtaG fuel Dt)
red.logs`, `red = cIntegrateReducedG Dt fuel a d cands`), the result is `res = ⟨(csubG gnum (cmulG [intR]
gden), gden), red.logs⟩` with `(gnum, gden) = red.rational` — the rational part `g − ∫R`, same logs. Pins the
driver's output: the §5.9 residual feedback subtracts the base integral `intR` from the reduced rational
part. -/
theorem cIntegrateHyperexpNormalG_shape (Dt : CPolyG α) (fuel : ℕ) (a d : CPolyG α) (cands : List α)
    (res : IntegralResultG α) (intR : α)
    (hintRsome : CRischField.crischDESolve (CField.zero : α)
        (cHyperexpResidualG (cExpEtaG fuel Dt) (CPolyG.cIntegrateReducedG Dt fuel a d cands).logs)
      = some intR)
    (hsome : CPolyG.cIntegrateHyperexpNormalG Dt fuel a d cands = some res) :
    res = ⟨(csubG (CPolyG.cIntegrateReducedG Dt fuel a d cands).rational.1
              (cmulG [intR] (CPolyG.cIntegrateReducedG Dt fuel a d cands).rational.2),
            (CPolyG.cIntegrateReducedG Dt fuel a d cands).rational.2),
          (CPolyG.cIntegrateReducedG Dt fuel a d cands).logs⟩ := by
  rw [CPolyG.cIntegrateHyperexpNormalG] at hsome
  simp only [hintRsome] at hsome
  -- the `let (gnum, gden) := red.rational` match reduces; `res` is the literal record `hsome` builds
  exact (Option.some.injEq _ _ ▸ hsome).symm

/-- **★★★ The §5.9 driver soundness `D(∫fₙ) = fₙ`, UNCONDITIONAL in `∑c`** — for a hyperexponential monomial
`toPolyG Dt = C b·X` (`Dt = η′·t`), if the §5.9 normal-part driver returns `some res`
(`cIntegrateHyperexpNormalG Dt fuel a d cands = some res`, the base oracle solving `∫R = intR`), **given**
the abstract Hermite half `hherm` and per-root reassembly `hform` (the same engine bridges the
primitive/hyperexp one-shots take), the base-RDE-oracle residual `hintR` (`D(∫R) = amG(C(toK R))`), and the
residual-read bridge `hRval` (`amG(C(toK R)) = amG(C(b·∑c))`), the field-level antiderivative identity
`D(res) + logResidueSumG Dt res.logs = amG a/amG d` holds over `RatFunc (CFieldSpec.K α)` — **with NO `∑c =
0` side condition, no engine `checkIdentityG` certificate, no native_decide**. The §5.9 residual feedback is
exactly what makes the hyperexp normal part integrable without `∑c = 0`: the new rational part `g − ∫R`
differentiates to `D(g) − D(∫R) = (a/d + R) − R = a/d`, the overshoot `R` (Task 1) cancelled by the base
integral `D(∫R) = R` (`hintR`). The MILESTONE: unconditional hyperexp normal-part soundness, reduced to the
documented base-oracle residual. -/
theorem cIntegrateHyperexpNormalG_sound (Dt : CPolyG α) (fuel : ℕ) (a d : CPolyG α) (cands : List α)
    (res : IntegralResultG α) (intR : α) (s : Finset (CFieldSpec.K α)) (b : CFieldSpec.K α)
    (hDt : toPolyG Dt = C b * X)
    (hgden : toPolyG (CPolyG.cIntegrateReducedG Dt fuel a d cands).rational.2 ≠ 0)
    (hintRsome : CRischField.crischDESolve (CField.zero : α)
        (cHyperexpResidualG (cExpEtaG fuel Dt) (CPolyG.cIntegrateReducedG Dt fuel a d cands).logs)
      = some intR)
    (hsome : CPolyG.cIntegrateHyperexpNormalG Dt fuel a d cands = some res)
    (hherm : towerFractionFieldDerivG Dt
            (amG α (toPolyG (CPolyG.cIntegrateReducedG Dt fuel a d cands).rational.1)
              / amG α (toPolyG (CPolyG.cIntegrateReducedG Dt fuel a d cands).rational.2))
          + amG α (toPolyG (cHermiteReduceTowerG Dt fuel a d).2.1)
            / amG α (toPolyG (cHermiteReduceTowerG Dt fuel a d).2.2)
        = amG α (toPolyG a) / amG α (toPolyG d))
    (hden : toPolyG (cHermiteReduceTowerG Dt fuel a d).2.2 = Lagrange.nodal s id)
    (hA : (toPolyG (cHermiteReduceTowerG Dt fuel a d).2.1).degree < s.card)
    (hnorm : ∀ β ∈ s, (C b * X).eval β ≠ β′)
    (hform : (CPolyG.cIntegrateReducedG Dt fuel a d cands).logs.map
          (fun cv => (CFieldSpec.toK cv.1, toPolyG cv.2))
        = s.toList.map (fun β =>
            ((toPolyG (cHermiteReduceTowerG Dt fuel a d).2.1).eval β
                / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β,
              X - C β)))
    (hintR : towerFractionFieldDerivG Dt (amG α (Polynomial.C (CFieldSpec.toK intR)))
        = amG α (Polynomial.C (CFieldSpec.toK
            (cHyperexpResidualG (cExpEtaG fuel Dt)
              (CPolyG.cIntegrateReducedG Dt fuel a d cands).logs))))
    (hRval : amG α (Polynomial.C (CFieldSpec.toK
            (cHyperexpResidualG (cExpEtaG fuel Dt)
              (CPolyG.cIntegrateReducedG Dt fuel a d cands).logs)))
        = amG α (C (b * ∑ β ∈ s,
            (toPolyG (cHermiteReduceTowerG Dt fuel a d).2.1).eval β
              / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β))) :
    towerFractionFieldDerivG Dt (amG α (toPolyG res.rational.1) / amG α (toPolyG res.rational.2))
        + logResidueSumG Dt res.logs
      = amG α (toPolyG a) / amG α (toPolyG d) := by
  -- pin the output shape: `res.rational = (gnum − intR·gden, gden)`, `res.logs = red.logs`
  rw [cIntegrateHyperexpNormalG_shape Dt fuel a d cands res intR hintRsome hsome]
  -- abbreviations for the reduced capstone's rational part
  set gnum := (CPolyG.cIntegrateReducedG Dt fuel a d cands).rational.1 with hgnum
  set gden := (CPolyG.cIntegrateReducedG Dt fuel a d cands).rational.2 with hgdenE
  -- read the new rational part `(gnum − intR·gden)/gden = gnum/gden − amG(C(toK intR))`
  have hAgden : amG α (toPolyG gden) ≠ 0 := amG_toPolyG_ne_zero hgden
  have hnewrat : amG α (toPolyG (csubG gnum (cmulG [intR] gden))) / amG α (toPolyG gden)
      = amG α (toPolyG gnum) / amG α (toPolyG gden) - amG α (Polynomial.C (CFieldSpec.toK intR)) := by
    rw [toPolyG_csubG, toPolyG_cmulG, map_sub, map_mul]
    -- `toPolyG [intR] = C (toK intR)`
    have hsingle : toPolyG ([intR] : CPolyG α) = Polynomial.C (CFieldSpec.toK intR) := by
      rw [toPolyG_cons, toPolyG_nil, mul_zero, add_zero]
    rw [hsingle, sub_div, mul_div_assoc, div_self hAgden, mul_one]
  -- D of the new rational part: `D(g − intR_const) = D(g) − D(intR_const)`
  rw [hnewrat, map_sub, hintR, hRval]
  -- now the overshoot identity supplies `D(g) + logResidueSumG = a/d + R`
  have hover := field_identity_of_cIntegrateReducedG_hyperexp_overshoot Dt fuel a d cands s b
    hDt hherm hden hA hnorm hform
  -- goal: `(D(g) − R) + logResidueSumG = a/d`; `hover : D(g) + logResidueSumG = a/d + R`
  set Dg := towerFractionFieldDerivG Dt (amG α (toPolyG gnum) / amG α (toPolyG gden)) with hDg
  set L := logResidueSumG Dt (CPolyG.cIntegrateReducedG Dt fuel a d cands).logs with hL
  set R := amG α (C (b * ∑ β ∈ s,
    (toPolyG (cHermiteReduceTowerG Dt fuel a d).2.1).eval β
      / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β)) with hR
  -- `hover : Dg + L = amG a/amG d + R`, goal `(Dg − R) + L = amG a/amG d`
  rw [show Dg - R + L = (Dg + L) - R by ring, hover, add_sub_cancel_right]

/-! ### ★ The §5.9 driver soundness at the level-1 carrier `α = QFunNZG ℚ = ℚ(x)`

Instantiating the unconditional §5.9 driver soundness at `α = QFunNZG ℚ` (`CFieldSpec.K (QFunNZG ℚ) =
RatFunc ℚ`). The concrete `cIntegrateHyperexpNormalG = some res ⟹ D(res) = a/d` for a hyperexponential
monomial over `ℚ(x)(t)`, unconditional in `∑c`, reduced to the documented base-oracle residual. The local
instance bridges the carrier abbreviation to `RatFunc ℚ`. -/

/-- The engine carrier `CFieldSpec.K (QFunNZG ℚ)` is `RatFunc ℚ`, a `ℚ`-algebra. Local instance so the
`QFunNZG ℚ` deliverable synthesizes the **same** `Algebra ℚ` the bridge `towerFractionFieldDerivG` uses. -/
noncomputable local instance : Algebra ℚ (CFieldSpec.K (QFunNZG ℚ)) :=
  inferInstanceAs (Algebra ℚ (RatFunc ℚ))

/-- **★★★ The §5.9 driver soundness over `ℚ(x)(t)`, UNCONDITIONAL in `∑c`** — the milestone at the level-1
carrier `α = QFunNZG ℚ` (`CFieldSpec.K (QFunNZG ℚ) = RatFunc ℚ`): for a hyperexponential monomial `toPolyG
Dt = C b·X`, if the §5.9 normal-part driver returns `some res`, given the abstract engine bridges (Hermite
half, per-root reassembly), the base-RDE-oracle residual `hintR`, and the residual-read bridge `hRval`, the
field-level antiderivative identity `D(res) + logResidueSumG Dt res.logs = amG a/amG d` holds over `RatFunc
ℚ` — **with NO `∑c = 0` side condition, no engine `checkIdentityG` certificate, no native_decide**. The
concrete unconditional hyperexp normal-part soundness at ℚ(x)(t), reduced to the documented base-oracle
residual. The `QFunNZG ℚ` instance of `cIntegrateHyperexpNormalG_sound`. -/
theorem cIntegrateHyperexpNormalG_sound_qfunNZG (Dt : CPolyG (QFunNZG ℚ)) (fuel : ℕ)
    (a d : CPolyG (QFunNZG ℚ)) (cands : List (QFunNZG ℚ)) (res : IntegralResultG (QFunNZG ℚ))
    (intR : QFunNZG ℚ) (s : Finset (CFieldSpec.K (QFunNZG ℚ))) (b : CFieldSpec.K (QFunNZG ℚ))
    (hDt : toPolyG Dt = C b * X)
    (hgden : toPolyG (CPolyG.cIntegrateReducedG Dt fuel a d cands).rational.2 ≠ 0)
    (hintRsome : CRischField.crischDESolve (CField.zero : QFunNZG ℚ)
        (cHyperexpResidualG (cExpEtaG fuel Dt) (CPolyG.cIntegrateReducedG Dt fuel a d cands).logs)
      = some intR)
    (hsome : CPolyG.cIntegrateHyperexpNormalG Dt fuel a d cands = some res)
    (hherm : towerFractionFieldDerivG Dt
            (amG (QFunNZG ℚ) (toPolyG (CPolyG.cIntegrateReducedG Dt fuel a d cands).rational.1)
              / amG (QFunNZG ℚ) (toPolyG (CPolyG.cIntegrateReducedG Dt fuel a d cands).rational.2))
          + amG (QFunNZG ℚ) (toPolyG (cHermiteReduceTowerG Dt fuel a d).2.1)
            / amG (QFunNZG ℚ) (toPolyG (cHermiteReduceTowerG Dt fuel a d).2.2)
        = amG (QFunNZG ℚ) (toPolyG a) / amG (QFunNZG ℚ) (toPolyG d))
    (hden : toPolyG (cHermiteReduceTowerG Dt fuel a d).2.2 = Lagrange.nodal s id)
    (hA : (toPolyG (cHermiteReduceTowerG Dt fuel a d).2.1).degree < s.card)
    (hnorm : ∀ β ∈ s, (C b * X).eval β ≠ β′)
    (hform : (CPolyG.cIntegrateReducedG Dt fuel a d cands).logs.map
          (fun cv => (CFieldSpec.toK cv.1, toPolyG cv.2))
        = s.toList.map (fun β =>
            ((toPolyG (cHermiteReduceTowerG Dt fuel a d).2.1).eval β
                / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β,
              X - C β)))
    (hintR : towerFractionFieldDerivG Dt (amG (QFunNZG ℚ) (Polynomial.C (CFieldSpec.toK intR)))
        = amG (QFunNZG ℚ) (Polynomial.C (CFieldSpec.toK
            (cHyperexpResidualG (cExpEtaG fuel Dt)
              (CPolyG.cIntegrateReducedG Dt fuel a d cands).logs))))
    (hRval : amG (QFunNZG ℚ) (Polynomial.C (CFieldSpec.toK
            (cHyperexpResidualG (cExpEtaG fuel Dt)
              (CPolyG.cIntegrateReducedG Dt fuel a d cands).logs)))
        = amG (QFunNZG ℚ) (C (b * ∑ β ∈ s,
            (toPolyG (cHermiteReduceTowerG Dt fuel a d).2.1).eval β
              / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β))) :
    towerFractionFieldDerivG Dt
        (amG (QFunNZG ℚ) (toPolyG res.rational.1) / amG (QFunNZG ℚ) (toPolyG res.rational.2))
        + logResidueSumG Dt res.logs
      = amG (QFunNZG ℚ) (toPolyG a) / amG (QFunNZG ℚ) (toPolyG d) :=
  cIntegrateHyperexpNormalG_sound Dt fuel a d cands res intR s b hDt hgden hintRsome hsome hherm hden
    hA hnorm hform hintR hRval

/-! ### ★★★ Task 3 (the full driver): `cIntegrateHyperexpFullG_sound` (§5.4 + §5.10 + §5.9)

`cIntegrateHyperexpFullG Dt fuel a d cands` combines the §5.10 Laurent special part `fp + b/dₛ` (via
`cIntegrateHyperexpLaurentG η`) with the §5.9 normal part `cₙ/dₙ` (via `cIntegrateHyperexpNormalG`), returning
the rational part `(lnum/lden) + (gnum/gden)` with the normal logs. Soundness composes:
* the Laurent field identity `hLaurField : D(lnum/lden) = amG(fpPart)` — the §5.10 special-part correctness
  (a documented input; the Laurent special-part soundness is a separate piece, not in scope here);
* the §5.9 normal-part soundness `cIntegrateHyperexpNormalG_sound` for `D(gnum/gden) + logResidueSumG = cₙ/dₙ`;
* the canonical reconstruction `hrecon : amG(fpPart) + cₙ/dₙ = a/d` (the `canonicalRepresentationFastG`
  recombination, documented).
Then `D(res) + logResidueSumG = D(lnum/lden) + D(gnum/gden) + logResidueSumG = amG(fpPart) + cₙ/dₙ = a/d`.
The §5.10-special + §5.9-normal hyperexp integral, unconditional in `∑c`, reduced to the Laurent
special-part identity + the canonical reconstruction + the base-oracle residual. -/

omit [CFieldSpec α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **The full §5.10 + §5.9 driver's output shape** — when `cIntegrateHyperexpFullG Dt fuel a d cands = some
res` with the Laurent part succeeding (`cIntegrateHyperexpLaurentG (cExpEtaG fuel Dt) fuel fp neg = some
(lnum, lden)`, `fp/b/ds/cn/dn` the `canonicalRepresentationFastG` components, `neg = cHyperexpSpecialNegG b
ds`) and the normal part succeeding (`cIntegrateHyperexpNormalG Dt fuel cn dn cands = some nrm`), the result is
`res = ⟨(caddG (cmulG lnum gden) (cmulG gnum lden), cmulG lden gden), nrm.logs⟩` with `(gnum, gden) =
nrm.rational` — the combined rational `lnum/lden + gnum/gden`, the normal logs. Pins the full driver's output:
the §5.10 Laurent rational part plus the §5.9 normal rational part. -/
theorem cIntegrateHyperexpFullG_shape (Dt : CPolyG α) (fuel : ℕ) (a d : CPolyG α) (cands : List α)
    (res : IntegralResultG α) (lnum lden : CPolyG α) (nrm : IntegralResultG α)
    (hLaur : cIntegrateHyperexpLaurentG (cExpEtaG fuel Dt) fuel
        (canonicalRepresentationFastG Dt fuel a d).1
        (cHyperexpSpecialNegG (canonicalRepresentationFastG Dt fuel a d).2.1.1
          (canonicalRepresentationFastG Dt fuel a d).2.1.2)
      = some (lnum, lden))
    (hNrm : CPolyG.cIntegrateHyperexpNormalG Dt fuel
        (canonicalRepresentationFastG Dt fuel a d).2.2.1
        (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands = some nrm)
    (hsome : CPolyG.cIntegrateHyperexpFullG Dt fuel a d cands = some res) :
    res = ⟨(caddG (cmulG lnum nrm.rational.2) (cmulG nrm.rational.1 lden), cmulG lden nrm.rational.2),
          nrm.logs⟩ := by
  rw [CPolyG.cIntegrateHyperexpFullG] at hsome
  -- destructure the canonical split so the pattern-match `let` reduces
  rcases hcrep : canonicalRepresentationFastG Dt fuel a d with ⟨fp, ⟨b, ds⟩, ⟨cn, dn⟩⟩
  rw [hcrep] at hsome hLaur hNrm
  simp only [hLaur, hNrm] at hsome
  -- the `let (gnum, gden) := nrm.rational` match reduces; `nrm.rational.1/.2` are defeq to `nrm.1.1/.1.2`
  exact (Option.some.injEq _ _ ▸ hsome).symm

/-- **★★★ The full §5.10 + §5.9 hyperexp driver soundness `D(∫f) = f`, UNCONDITIONAL in `∑c`** — for a
hyperexponential monomial `toPolyG Dt = C b·X` (`Dt = η′·t`), if the full driver returns `some res`
(`cIntegrateHyperexpFullG Dt fuel a d cands = some res`, both the §5.10 Laurent part and the §5.9 normal part
succeeding), **given** the Laurent special-part field identity `hLaurField` (`D(lnum/lden) = amG fpPart`, the
§5.10 correctness — a documented input), the canonical reconstruction `hrecon` (`amG fpPart + amG cn/amG dn =
amG a/amG d`, the `canonicalRepresentationFastG` recombination), the §5.9 normal-part field identity
`hNrmField` (`D(gnum/gden) + logResidueSumG Dt nrm.logs = amG cn/amG dn`, from
`cIntegrateHyperexpNormalG_sound`), and the nonzero denominators, the field-level antiderivative identity
`D(res) + logResidueSumG Dt res.logs = amG a/amG d` holds over `RatFunc (CFieldSpec.K α)` — **with NO `∑c =
0` side condition, no engine `checkIdentityG` certificate, no native_decide**. The §5.10-special + §5.9-normal
hyperexp integral both differentiate back to `f`: `D(lnum/lden + gnum/gden) + logResidueSumG = amG fpPart +
(amG cn/amG dn) = amG a/amG d`. The complete hyperexponential integral (special §5.10 + normal §5.9),
unconditional in `∑c`, reduced to the Laurent special-part identity + the canonical reconstruction + the
§5.9-normal soundness (`cIntegrateHyperexpNormalG_sound`, itself reduced to the base-oracle residual). -/
theorem cIntegrateHyperexpFullG_sound (Dt : CPolyG α) (fuel : ℕ) (a d : CPolyG α) (cands : List α)
    (res : IntegralResultG α) (lnum lden : CPolyG α) (nrm : IntegralResultG α) (fpPart : CPolyG α)
    (hlden : toPolyG lden ≠ 0) (hgden : toPolyG nrm.rational.2 ≠ 0)
    (hLaur : cIntegrateHyperexpLaurentG (cExpEtaG fuel Dt) fuel
        (canonicalRepresentationFastG Dt fuel a d).1
        (cHyperexpSpecialNegG (canonicalRepresentationFastG Dt fuel a d).2.1.1
          (canonicalRepresentationFastG Dt fuel a d).2.1.2)
      = some (lnum, lden))
    (hNrm : CPolyG.cIntegrateHyperexpNormalG Dt fuel
        (canonicalRepresentationFastG Dt fuel a d).2.2.1
        (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands = some nrm)
    (hsome : CPolyG.cIntegrateHyperexpFullG Dt fuel a d cands = some res)
    (hLaurField : towerFractionFieldDerivG Dt (amG α (toPolyG lnum) / amG α (toPolyG lden))
        = amG α (toPolyG fpPart))
    (hNrmField : towerFractionFieldDerivG Dt
            (amG α (toPolyG nrm.rational.1) / amG α (toPolyG nrm.rational.2))
          + logResidueSumG Dt nrm.logs
        = amG α (toPolyG (canonicalRepresentationFastG Dt fuel a d).2.2.1)
          / amG α (toPolyG (canonicalRepresentationFastG Dt fuel a d).2.2.2))
    (hrecon : amG α (toPolyG fpPart)
          + amG α (toPolyG (canonicalRepresentationFastG Dt fuel a d).2.2.1)
            / amG α (toPolyG (canonicalRepresentationFastG Dt fuel a d).2.2.2)
        = amG α (toPolyG a) / amG α (toPolyG d)) :
    towerFractionFieldDerivG Dt (amG α (toPolyG res.rational.1) / amG α (toPolyG res.rational.2))
        + logResidueSumG Dt res.logs
      = amG α (toPolyG a) / amG α (toPolyG d) := by
  -- pin the output shape
  rw [cIntegrateHyperexpFullG_shape Dt fuel a d cands res lnum lden nrm hLaur hNrm hsome]
  -- the combined rational `(lnum·gden + gnum·lden)/(lden·gden) = lnum/lden + gnum/gden`
  have hAlden : amG α (toPolyG lden) ≠ 0 := amG_toPolyG_ne_zero hlden
  have hAgden : amG α (toPolyG nrm.rational.2) ≠ 0 := amG_toPolyG_ne_zero hgden
  have hcombine : amG α (toPolyG (caddG (cmulG lnum nrm.rational.2) (cmulG nrm.rational.1 lden)))
        / amG α (toPolyG (cmulG lden nrm.rational.2))
      = amG α (toPolyG lnum) / amG α (toPolyG lden)
        + amG α (toPolyG nrm.rational.1) / amG α (toPolyG nrm.rational.2) := by
    rw [toPolyG_caddG, toPolyG_cmulG, toPolyG_cmulG, toPolyG_cmulG, map_add, map_mul, map_mul,
      map_mul]
    field_simp
  -- D of the combined rational splits over `+`; apply the Laurent and normal field identities
  rw [hcombine, map_add, hLaurField]
  -- goal: `amG fpPart + D(gnum/gden) + logResidueSumG = amG a/amG d`; regroup and apply `hNrmField`
  rw [add_assoc, hNrmField]
  exact hrecon

/-! ### Restatements against the intended wording (anonymous `example`s) -/

-- ★ THE OVERSHOOT IDENTITY (UNCONDITIONAL, axiom-clean, no native_decide): the raw §5.6 Rothstein–Trager
-- log part of a hyperexp normal part differentiates to `a/d + R`, NOT `a/d`, with residual `R = b·∑c` —
-- the `extendDeriv_logPart_eq_div_add_residual` claim, PROVEN, no `∑c = 0`.
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

-- ★★★ THE §5.9 NORMAL-PART DRIVER SOUNDNESS (UNCONDITIONAL in `∑c`, no native_decide):
-- `cIntegrateHyperexpNormalG = some res ⟹ D(res) = a/d` for a hyperexp `Dt = η′·t`, gated on the abstract
-- engine bridges + the base-oracle residual `hintR` + the residual-read bridge `hRval` — NO `∑c = 0`.
example (Dt : CPolyG α) (fuel : ℕ) (a d : CPolyG α) (cands : List α) (res : IntegralResultG α)
    (intR : α) (s : Finset (CFieldSpec.K α)) (b : CFieldSpec.K α) (hDt : toPolyG Dt = C b * X)
    (hgden : toPolyG (CPolyG.cIntegrateReducedG Dt fuel a d cands).rational.2 ≠ 0)
    (hintRsome : CRischField.crischDESolve (CField.zero : α)
        (cHyperexpResidualG (cExpEtaG fuel Dt) (CPolyG.cIntegrateReducedG Dt fuel a d cands).logs)
      = some intR)
    (hsome : CPolyG.cIntegrateHyperexpNormalG Dt fuel a d cands = some res)
    (hherm : towerFractionFieldDerivG Dt
            (amG α (toPolyG (CPolyG.cIntegrateReducedG Dt fuel a d cands).rational.1)
              / amG α (toPolyG (CPolyG.cIntegrateReducedG Dt fuel a d cands).rational.2))
          + amG α (toPolyG (cHermiteReduceTowerG Dt fuel a d).2.1)
            / amG α (toPolyG (cHermiteReduceTowerG Dt fuel a d).2.2)
        = amG α (toPolyG a) / amG α (toPolyG d))
    (hden : toPolyG (cHermiteReduceTowerG Dt fuel a d).2.2 = Lagrange.nodal s id)
    (hA : (toPolyG (cHermiteReduceTowerG Dt fuel a d).2.1).degree < s.card)
    (hnorm : ∀ β ∈ s, (C b * X).eval β ≠ β′)
    (hform : (CPolyG.cIntegrateReducedG Dt fuel a d cands).logs.map
          (fun cv => (CFieldSpec.toK cv.1, toPolyG cv.2))
        = s.toList.map (fun β =>
            ((toPolyG (cHermiteReduceTowerG Dt fuel a d).2.1).eval β
                / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β,
              X - C β)))
    (hintR : towerFractionFieldDerivG Dt (amG α (Polynomial.C (CFieldSpec.toK intR)))
        = amG α (Polynomial.C (CFieldSpec.toK
            (cHyperexpResidualG (cExpEtaG fuel Dt)
              (CPolyG.cIntegrateReducedG Dt fuel a d cands).logs))))
    (hRval : amG α (Polynomial.C (CFieldSpec.toK
            (cHyperexpResidualG (cExpEtaG fuel Dt)
              (CPolyG.cIntegrateReducedG Dt fuel a d cands).logs)))
        = amG α (C (b * ∑ β ∈ s,
            (toPolyG (cHermiteReduceTowerG Dt fuel a d).2.1).eval β
              / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β))) :
    towerFractionFieldDerivG Dt (amG α (toPolyG res.rational.1) / amG α (toPolyG res.rational.2))
        + logResidueSumG Dt res.logs
      = amG α (toPolyG a) / amG α (toPolyG d) :=
  cIntegrateHyperexpNormalG_sound Dt fuel a d cands res intR s b hDt hgden hintRsome hsome hherm hden
    hA hnorm hform hintR hRval

/-! ### ★ Status — the §5.9 hyperexponential driver soundness, UNCONDITIONAL in `∑c`

PROVEN (axiom-clean `[propext, Classical.choice, Quot.sound]`, **no** `native_decide`, **no** `sorry`):
* **★ The overshoot identity** (`hyperexp_residue_sum_eq_overshoot_add` /
  `hyperexp_overshoot_list_engine` / `hyperexp_engine_overshoot` /
  `field_identity_of_cIntegrateReducedG_hyperexp_overshoot`) — the genuine §5.9 content, UNCONDITIONAL: the
  raw Rothstein–Trager log part of a hyperexponential normal part `fₙ = a/d` differentiates to `a/d + R`
  with residual `R = b·∑c` (`b = η′`), NOT `a/d`. This is the `extendDeriv_logPart_eq_div_add_residual`
  docstring claim, made precise and proven from the UNCONDITIONAL `monomial_residue_sum_eq_cancel_add`
  (residue sum = cancel sum + a/d) + `hyperexp_cancel_sum_eq` (the hyperexp cancel sum IS
  `algebraMap(C(b·∑c))`). No `∑c = 0` side condition.
* **★★★ The §5.9 driver soundness** (`cIntegrateHyperexpNormalG_sound` / `…_qfunNZG`) — for a
  hyperexponential monomial `toPolyG Dt = C b·X`, `cIntegrateHyperexpNormalG = some res ⟹ D(res) = a/d`,
  **UNCONDITIONAL in `∑c`** (no `∑c = 0`), gated on the abstract engine bridges (`hherm`, `hform`) PLUS two
  documented inputs:
  - `hintR` — the base-RDE-oracle residual `D(∫R) = amG(C(toK R))` (the `crischDESolve 0 R` soundness).
  - `hRval` — the residual-read bridge `amG(C(toK R)) = amG(C(b·∑c))` (the engine residual `R = η·∑c` reads
    to the abstract overshoot).
  The §5.9 residual feedback subtracts the base integral: the new rational part `g − ∫R` differentiates to
  `D(g) − D(∫R) = (a/d + R) − R = a/d`, the overshoot `R` cancelled by `hintR`.
* **★★★ The full §5.10 + §5.9 driver soundness** (`cIntegrateHyperexpFullG_sound`) — for a hyperexponential
  monomial `toPolyG Dt = C b·X`, `cIntegrateHyperexpFullG = some res ⟹ D(res) = a/d`, **UNCONDITIONAL in
  `∑c`**, gated on the §5.9-normal soundness (`hNrmField`, from `cIntegrateHyperexpNormalG_sound`), the §5.10
  Laurent special-part field identity `hLaurField` (a documented input — the Laurent special-part soundness is
  a separate piece, not in scope), and the canonical reconstruction `hrecon`. Combines special + normal:
  `D(lnum/lden + gnum/gden) + logResidueSumG = amG fpPart + cₙ/dₙ = a/d`.

★ IS UNCONDITIONAL HYPEREXP SOUNDNESS PROVEN? **YES — modulo the base-oracle residual, NOT modulo `∑c = 0`.**
The contrast with `ComputableOneShotAssembly`'s `cIntegrateGFull_hyperexp_oneShot` (gated on the FALSE-in-
general `∑c = 0`) is the whole point: the §5.9 driver `cIntegrateHyperexpNormalG` ABSORBS the overshoot `R =
η·∑c` into `∫R = crischDESolve 0 R` and subtracts it, so there is NO `∑c = 0` side condition. The remaining
input `hintR` is the base oracle's `∫R`-soundness — a GENUINELY DIFFERENT, smaller residual than `∑c = 0`
(it is the *absorbing* of `∑c ≠ 0`, the opposite condition).

★ WHAT REDUCES TO THE BASE ORACLE. The single non-abstract input is `hintR : D(∫R) = R` (`R ∈ α` a base
element, e.g. `R = 1 ↦ ∫R = x`, `R = 2x ↦ ∫R = x²`). The base oracle `CRischField.crischDESolve` is a bare
typeclass method with **no abstract spec layer** (`CRischFieldSpec` does not exist; `crischDESolve 0 R` over
`ℚ(x)` runs the §6 pipeline one tower level down over `ℚ[x]`, recursing to `ℚ`), so its soundness is only
`native_decide`-validated today (`nNormInv_baseIntegral_eq_x`, `nVarNorm_baseIntegral_eq_xSq`). Building the
abstract `crischDESolve` spec (the bridge `instCRischFieldQFunNZG`-unfold → `cRischDEG` field-level soundness
→ reuse `field_identity_of_cPolyRischDEG`) is a separate, larger task; until then `hintR` is the documented
residual the unconditional driver soundness rests on. The OVERSHOOT identity — the genuine §5.9 new content
— is fully proven, axiom-clean. -/

#print axioms ResidueMatchTower.hyperexp_residue_sum_eq_overshoot_add
#print axioms hyperexp_overshoot_list_engine
#print axioms hyperexp_engine_overshoot
#print axioms field_identity_of_cIntegrateReducedG_hyperexp_overshoot
#print axioms cIntegrateHyperexpNormalG_shape
#print axioms cIntegrateHyperexpNormalG_sound
#print axioms cIntegrateHyperexpNormalG_sound_qfunNZG
#print axioms cIntegrateHyperexpFullG_shape
#print axioms cIntegrateHyperexpFullG_sound

end DeepWiki.SymbolicIntegration
