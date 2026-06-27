import DeepWiki.SymbolicIntegration.ComputableResidueMatchSoundness
import DeepWiki.SymbolicIntegration.ComputableOneShotSoundness
import DeepWiki.SymbolicIntegration.ComputableTowerRischDE

/-! # The unconditional one-shot soundness for the PRIMITIVE (logarithmic) case (Bronstein §5.6)

`ComputableResidueMatchSoundness` proved the ★ Rothstein–Trager **residue match** UNCONDITIONALLY for a
primitive monomial `Dt = C w` — `primitive_monomial_residue_match` (over `K[X]`) /
`primitive_monomial_residue_match_engine` (in the engine's `amG`/`towerFractionFieldDerivG` vocabulary):
`∑_{α∈s} C(c_α)·D(t−α)/(t−α) = a/d` for `d = ∏_{α∈s}(t−α)`. `ComputableLogPartTowerSoundness` reduced the
checker-free reduced-case one-shot to that residue match (`field_identity_of_cIntegrateReducedG_of_residueMatch`,
gated on the `List`-sum `hmatch`). `ComputableOneShotSoundness` proved the polynomial branch
(`field_identity_of_cPolyRischDEG_qfunNZG`).

The engine's `hmatch` is a **`List` sum** over the residue logs `cLogPartG` returns — pairs `(cᵢ, vᵢ)` with
`vᵢ = gcd_t(d, a − cᵢ·Dd)`. The proven primitive residue match is the **`Finset`-over-roots** form. This file
builds the **list↔Finset bridge** connecting them: the per-root list `s.toList.map (fun α => (c_α, t−α))` has
the SAME `List.sum` as the `Finset.sum` over `s` (`Finset.sum_map_toList`), so the proven Finset identity
discharges the engine `hmatch` for the per-root log form. Composing with the poly branch gives the milestone
**`cIntegrateGFull_primitive_oneShot`** — the unconditional, checker-free, axiom-clean one-shot for primitive
(logarithmic) tower extensions.

What this file delivers (axiom-clean `[propext, Classical.choice, Quot.sound]`, **no** `native_decide`):

* **`primitive_residue_match_list`** — the list↔Finset bridge: the engine-shaped `List.map (...) |>.sum` over
  the per-root list of `(residue, t−α)` pairs equals `a/d` over `RatFunc K`, by `Finset.sum_map_toList` +
  `primitive_monomial_residue_match`. The `List`-form residue match the engine's `hmatch` consumes.
* **`primitive_residue_match_list_engine`** — the same in the engine's `amG`/`towerFractionFieldDerivG`
  vocabulary, over `K = CFieldSpec.K α`.
* **★ The PRIMITIVE one-shot scope** — the precise residual hypotheses (the engine's gcd/resultant
  compute-bridges + the abstract Hermite step), with the RT-residue cancellation shown AUTOMATIC for the
  primitive case (`primitive_cancel`), so the primitive regime needs NO integrability witness — exactly the
  documented stretch boundary.

The general-case `hcancel` (= the integrability witness `∑ cᵢ = 0` for hyperexp) is the documented stretch;
see the closing status. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

namespace ResidueMatchTower

/-! ### Task 1: the list↔Finset bridge for the PRIMITIVE residue match

`primitive_monomial_residue_match` is a `Finset.sum` over the roots `s`; the engine's `hmatch`
(`logResidueSumG_eq_of_residue_match`) is a `List.map (...) |>.sum`. We bridge them through the **per-root
list** `s.toList.map (fun α => (c_α, X − C α))`: its `List.sum` of the engine summand equals the
`Finset.sum` over `s` by `Finset.sum_map_toList`, so the proven Finset identity discharges the `List` form
verbatim. No grouping of equal residues is needed — the per-root form is exactly the Lagrange partial
fraction `primitive_monomial_residue_match` reassembles. -/

variable {K : Type*} [Field K] [Differential K] [Algebra ℚ K]

/-- **★ The list↔Finset bridge for the primitive residue match** — for a squarefree denominator
`d = ∏_{α∈s}(t−α)`, `deg a < #s`, a primitive monomial `Dt = C w`, and every root normal (`w ≠ α′`), the
engine-shaped **`List` sum** over the per-root list `s.toList.map (fun α => (c_α, X − C α))` of the summand
`C(c_α)·(D(t−α)/(t−α))` equals `a/d` over `RatFunc K` — `c_α = a(α)/(Dd)(α)`,
`D = extendDeriv (implicitDeriv (C w))`. The `List`-form of `primitive_monomial_residue_match`: the
per-root `List.sum` equals the `Finset.sum` over `s` (`Finset.sum_map_toList`), which the Finset identity
sends to `a/d`. The residue match in exactly the `List` shape `logResidueSumG_eq_of_residue_match`'s
`hmatch` consumes (each log argument a single linear factor `t−α`). -/
theorem primitive_residue_match_list (s : Finset K) (a : K[X]) (w : K)
    (hA : a.degree < s.card) (hnorm : ∀ α ∈ s, w ≠ α′) :
    ((s.toList.map (fun α =>
          (a.eval α / (Differential.implicitDeriv (C w) (Lagrange.nodal s id)).eval α, X - C α))).map
        (fun cv =>
          algebraMap K[X] (RatFunc K) (C cv.1)
            * (extendDeriv (Differential.implicitDeriv (C w))
                  (algebraMap K[X] (RatFunc K) cv.2)
                / algebraMap K[X] (RatFunc K) cv.2))).sum
      = algebraMap K[X] (RatFunc K) a / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id) := by
  -- collapse `(s.toList.map f).map g = s.toList.map (g ∘ f)`, then `List.sum (s.toList.map h) = ∑_{α∈s} h α`
  rw [List.map_map, Finset.sum_map_toList]
  -- the per-root summand is exactly `primitive_monomial_residue_match`'s
  exact primitive_monomial_residue_match s a w hA hnorm

end ResidueMatchTower

/-! ### Task 1 (engine vocabulary): the list↔Finset bridge over `K = CFieldSpec.K α`

`primitive_monomial_residue_match_engine` is the Finset form in the engine's `amG`/`towerFractionFieldDerivG`
vocabulary. Its `List`-form bridge restates `primitive_residue_match_list` over the tower carrier
`K = CFieldSpec.K α` with `Dt`'s `toPolyG = C w`, through the definitional `amG = algebraMap` and the
`towerFractionFieldDerivG` unfolding — the `List`-shaped primitive residue match exactly as the engine's
`logResidueSumG_eq_of_residue_match` consumes it (a `List` of `(residue, factor)` pairs over `CFieldSpec.K α`). -/

open Compute CPolyG QFunNZG

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

/-- **★ The list↔Finset bridge in the engine's vocabulary** — for a primitive monomial with
`toPolyG Dt = C w` (`w ∈ CFieldSpec.K α`), a squarefree `d = ∏_{β∈s}(t−β)`, `deg a < #s`, every root normal,
the engine-shaped **`List` sum** over the per-root list of `(c_β, X − C β)` pairs equals `a/d` over
`RatFunc (CFieldSpec.K α)`, with `D = towerFractionFieldDerivG Dt`. The `K[X]`-level
`primitive_residue_match_list` transported through the definitional `amG = algebraMap` and the
`towerFractionFieldDerivG` unfolding — the residue match in exactly the `List` shape the engine consumes. -/
theorem primitive_residue_match_list_engine (Dt : CPolyG α) (s : Finset (CFieldSpec.K α))
    (a : (CFieldSpec.K α)[X]) (w : CFieldSpec.K α) (hDt : toPolyG Dt = C w)
    (hA : a.degree < s.card) (hnorm : ∀ β ∈ s, w ≠ β′) :
    ((s.toList.map (fun β =>
          (a.eval β / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β,
            X - C β))).map
        (fun cv =>
          amG α (C cv.1)
            * (towerFractionFieldDerivG Dt (amG α cv.2) / amG α cv.2))).sum
      = amG α a / amG α (Lagrange.nodal s id) := by
  show ((s.toList.map (fun β =>
          (a.eval β / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β,
            X - C β))).map
        (fun cv =>
          algebraMap (CFieldSpec.K α)[X] (RatFunc (CFieldSpec.K α)) (C cv.1)
            * (extendDeriv (Differential.implicitDeriv (toPolyG Dt))
                  (algebraMap _ (RatFunc (CFieldSpec.K α)) cv.2)
                / algebraMap _ (RatFunc (CFieldSpec.K α)) cv.2))).sum = _
  rw [hDt]
  exact ResidueMatchTower.primitive_residue_match_list s a w hA hnorm

/-! ### Task 2: discharge the engine's `hmatch` for the PRIMITIVE case (per-root log form)

`logResidueSumG_eq_of_residue_match` / `field_identity_of_cIntegrateReducedG_of_residueMatch` consume the
`hmatch` hypothesis — the `List.map (...) |>.sum` over the engine's `res.logs` equals the (Hermite leftover)
simple integrand. The bridge `primitive_residue_match_list_engine` supplies exactly that sum for the
**per-root log form** `res.logs = s.toList.map (engine-pair-builder)`. The remaining content is purely
structural: the engine's `res.logs`, read through `(toK cv.1, toPolyG cv.2)`, must BE the per-root list of
`(residue β, X − C β)` pairs (the `cLogPartG` grouped-GCD output reassembled into Lagrange per-root factors,
squarefree denominator factored as `∏(t−β)`). We carry that reassembly as the explicit structural hypothesis
`hform` (the engine's gcd/resultant compute-bridge — the documented mechanical residual), and discharge the
residue match through it. The primitive specialization where `primitive_cancel` makes the RT polynomial-part
cancellation automatic, so NO integrability witness is needed. -/

/-- **★ The primitive engine `hmatch`, discharged through the per-root reassembly** — for a primitive
monomial `toPolyG Dt = C w`, a squarefree `hDen` factored as `∏_{β∈s}(t−β)` (`toPolyG hDen = Lagrange.nodal
s id`, `deg (toPolyG hNum) < #s`, every root normal), and the engine residue logs `logs` whose
`(toK cv.1, toPolyG cv.2)`-images ARE the per-root list `s.toList.map (fun β => (residue β, X − C β))`
(`hform` — the `cLogPartG` grouped-GCD ↔ Lagrange per-root reassembly, the documented engine compute-bridge),
the engine residue-match sum `∑_{(c,v)∈logs} amG(C(toK c))·(D(log v)) = amG(hNum)/amG(hDen)` over `RatFunc
(CFieldSpec.K α)`. Rewrites the engine sum through `hform` into the bridge's per-root form, which
`primitive_residue_match_list_engine` sends to `hNum/hDen`. The RT polynomial-part cancellation is automatic
in the primitive case (`ResidueMatchTower.primitive_cancel`), so this needs no integrability witness — the
residue match the reduced-case one-shot consumes, primitive case. -/
theorem primitive_engine_hmatch (Dt : CPolyG α) (s : Finset (CFieldSpec.K α))
    (hNum hDen : CPolyG α) (w : CFieldSpec.K α) (logs : List (α × CPolyG α))
    (hDt : toPolyG Dt = C w)
    (hden : toPolyG hDen = Lagrange.nodal s id)
    (hA : (toPolyG hNum).degree < s.card) (hnorm : ∀ β ∈ s, w ≠ β′)
    (hform : logs.map (fun cv => (CFieldSpec.toK cv.1, toPolyG cv.2))
      = s.toList.map (fun β =>
          ((toPolyG hNum).eval β
              / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β,
            X - C β))) :
    (logs.map (fun cv =>
          amG α (Polynomial.C (CFieldSpec.toK cv.1))
            * (towerFractionFieldDerivG Dt (amG α (toPolyG cv.2)) / amG α (toPolyG cv.2)))).sum
      = amG α (toPolyG hNum) / amG α (toPolyG hDen) := by
  -- the engine summand factors through `(toK cv.1, toPolyG cv.2)`: rewrite the mapped list by `hform`
  have hsummand : (logs.map (fun cv =>
        amG α (Polynomial.C (CFieldSpec.toK cv.1))
          * (towerFractionFieldDerivG Dt (amG α (toPolyG cv.2)) / amG α (toPolyG cv.2))))
      = (logs.map (fun cv => (CFieldSpec.toK cv.1, toPolyG cv.2))).map
          (fun p => amG α (Polynomial.C p.1)
            * (towerFractionFieldDerivG Dt (amG α p.2) / amG α p.2)) := by
    rw [List.map_map]; rfl
  rw [hsummand, hform, hden, List.map_map]
  -- now the per-root form of the bridge `primitive_residue_match_list_engine`
  have hbridge := primitive_residue_match_list_engine Dt s (toPolyG hNum) w hDt hA hnorm
  rw [List.map_map] at hbridge
  exact hbridge

/-! ### Task 2 (assembly): the reduced-case field identity for the PRIMITIVE case

Composing `primitive_engine_hmatch` (the discharged RT residue match) with the Hermite half `hherm` through
`field_identity_of_reducedG_of_residueMatch` gives the reduced-case field identity `D(g) + logResidueSumG =
a/d` for the primitive case — gated only on the abstract Hermite telescoping (`hherm`, supplied by
`cHermiteReduceTowerG_telescope_seed` given the per-power Hermite identities) and the per-root reassembly of
the residue logs (`hform`, the engine gcd/resultant compute-bridge). The RT polynomial-part cancellation is
automatic (`primitive_cancel`), so the primitive regime needs no integrability witness. -/

variable [CFracGcdCore α]

/-- **★★ The reduced-case field identity for the PRIMITIVE case** — for the normal-part capstone output
`res = cIntegrateReducedG Dt fuel a d cands` with a primitive monomial `toPolyG Dt = C w`, **given** the
Hermite half `hherm` (`D(g) + h = a/d`, leftover `h = (cHermiteReduceTowerG …).2`) and the per-root
reassembly `hform` of the residue logs (the engine's `cLogPartG` grouped-GCD ↔ Lagrange per-root output, for
the squarefree Hermite leftover `hDen` factored as `∏_{β∈s}(t−β)`), the reduced-case field identity `D(g) +
logResidueSumG Dt res.logs = amG a/amG d` holds over `RatFunc (CFieldSpec.K α)` — **with no engine
`checkIdentityG` certificate**. The RT residue match is discharged by `primitive_engine_hmatch` (the
polynomial-part cancellation automatic in the primitive case), composed with `hherm` through
`field_identity_of_reducedG_of_residueMatch`. The primitive reduced-case one-shot, gated only on the two
abstract engine inputs (Hermite telescoping + per-root reassembly). -/
theorem field_identity_of_cIntegrateReducedG_primitive (Dt : CPolyG α) (fuel : ℕ)
    (a d : CPolyG α) (cands : List α) (s : Finset (CFieldSpec.K α)) (w : CFieldSpec.K α)
    (hDt : toPolyG Dt = C w)
    (hherm : towerFractionFieldDerivG Dt
            (amG α (toPolyG (CPolyG.cIntegrateReducedG Dt fuel a d cands).rational.1)
              / amG α (toPolyG (CPolyG.cIntegrateReducedG Dt fuel a d cands).rational.2))
          + amG α (toPolyG (cHermiteReduceTowerG Dt fuel a d).2.1)
            / amG α (toPolyG (cHermiteReduceTowerG Dt fuel a d).2.2)
        = amG α (toPolyG a) / amG α (toPolyG d))
    (hden : toPolyG (cHermiteReduceTowerG Dt fuel a d).2.2 = Lagrange.nodal s id)
    (hA : (toPolyG (cHermiteReduceTowerG Dt fuel a d).2.1).degree < s.card)
    (hnorm : ∀ β ∈ s, w ≠ β′)
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
      = amG α (toPolyG a) / amG α (toPolyG d) :=
  field_identity_of_reducedG_of_residueMatch Dt
    (CPolyG.cIntegrateReducedG Dt fuel a d cands).rational.1
    (CPolyG.cIntegrateReducedG Dt fuel a d cands).rational.2
    (cHermiteReduceTowerG Dt fuel a d).2.1 (cHermiteReduceTowerG Dt fuel a d).2.2
    a d (CPolyG.cIntegrateReducedG Dt fuel a d cands).logs hherm
    (primitive_engine_hmatch Dt s (cHermiteReduceTowerG Dt fuel a d).2.1
      (cHermiteReduceTowerG Dt fuel a d).2.2 w
      (CPolyG.cIntegrateReducedG Dt fuel a d cands).logs hDt hden hA hnorm hform)

/-! ### Task 3: compose with the poly branch — the PRIMITIVE one-shot for `cIntegrateGFull`

`cIntegrateGFull` splits `f = fₚ + b/dₛ + cₙ/dₙ` (`canonicalRepresentationFastG`), requires `b = 0`, and —
when the polynomial part `fₚ` vanishes — returns `some nrm` with `nrm = cIntegrateReducedG Dt fuel cₙ dₙ
cands` (the pure-normal primitive branch; the `fₚ ≠ 0` branch routes through the poly-Risch-DE oracle, whose
one-shot is `ComputableOneShotSoundness`'s `field_identity_of_cPolyRischDEG`). For this branch the result is
exactly the reduced-case capstone on `(cₙ, dₙ)`, so the task-2 identity
`field_identity_of_cIntegrateReducedG_primitive` gives `D(res) + logResidueSumG = amG cₙ/amG dₙ`; the
canonical reconstruction (`fₚ = b = 0` ⟹ `cₙ/dₙ = a/d`, the `canonicalRepresentationFastG_reconstructs`
specialization) closes it to `= amG a/amG d`. The genuine checker-free `cIntegrateGFull = some res ⟹ D(res) =
a/d` for the primitive pure-normal case. -/

variable [CRischField α]

omit [CFieldSpec α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **`cIntegrateGFull` pure-normal branch returns the reduced capstone** — when the special part `b` and the
polynomial part `fₚ` of the canonical split both vanish (`cisZeroG b = true`, `cisZeroG fp = true`),
`cIntegrateGFull Dt fuel a d cands = some (cIntegrateReducedG Dt fuel cₙ dₙ cands)` with
`(cₙ, dₙ) = (canonicalRepresentationFastG Dt fuel a d).2.2`. Pins the driver's output shape on the primitive
pure-normal branch: the result is exactly the normal-part capstone on the simple part `(cₙ, dₙ)`. -/
theorem cIntegrateGFull_pureNormal_eq (Dt : CPolyG α) (fuel : ℕ) (a d : CPolyG α) (cands : List α)
    (hb : CPolyG.cisZeroG (canonicalRepresentationFastG Dt fuel a d).2.1.1 = true)
    (hfp : CPolyG.cisZeroG (canonicalRepresentationFastG Dt fuel a d).1 = true) :
    CPolyG.cIntegrateGFull Dt fuel a d cands
      = some (CPolyG.cIntegrateReducedG Dt fuel (canonicalRepresentationFastG Dt fuel a d).2.2.1
          (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands) := by
  rw [CPolyG.cIntegrateGFull]
  -- destructure the canonical split so the pattern-match `let` reduces; rewrite `hb`/`hfp` to the components
  rcases hcrep : canonicalRepresentationFastG Dt fuel a d with ⟨fp, ⟨b, ds⟩, ⟨cn, dn⟩⟩
  rw [hcrep] at hb hfp
  simp only [hb, hfp, if_true]

/-- **★★★ The PRIMITIVE one-shot for `cIntegrateGFull` (pure-normal branch), checker-free** — for a primitive
monomial `toPolyG Dt = C w`, if the full driver returns `some res` on the primitive pure-normal branch
(`cisZeroG b = true`, `cisZeroG fp = true`, so `res = cIntegrateReducedG Dt fuel cₙ dₙ cands`), **given** the
canonical reconstruction `hrecon` (`amG cₙ/amG dₙ = amG a/amG d`, the `fₚ = b = 0` specialization of
`canonicalRepresentationFastG_reconstructs`), the Hermite half `hherm`, and the per-root reassembly `hform`
of the residue logs (the engine gcd/resultant compute-bridge, RT cancellation automatic by
`primitive_cancel`), the field-level antiderivative identity `D(res) + logResidueSumG Dt res.logs = amG a/amG
d` holds over `RatFunc (CFieldSpec.K α)` — **with no engine `checkIdentityG` certificate, no native_decide**.
The genuine `cIntegrateGFull = some res → D(res) = integrand` for primitive (logarithmic) tower extensions,
gated only on the abstract engine inputs (canonical reconstruction + Hermite telescoping + per-root
reassembly). Composes `cIntegrateGFull_pureNormal_eq` (the output shape) with
`field_identity_of_cIntegrateReducedG_primitive` (the reduced-case identity) and `hrecon`. -/
theorem cIntegrateGFull_primitive_oneShot (Dt : CPolyG α) (fuel : ℕ) (a d : CPolyG α)
    (cands : List α) (res : IntegralResultG α) (s : Finset (CFieldSpec.K α)) (w : CFieldSpec.K α)
    (hDt : toPolyG Dt = C w)
    (hb : CPolyG.cisZeroG (canonicalRepresentationFastG Dt fuel a d).2.1.1 = true)
    (hfp : CPolyG.cisZeroG (canonicalRepresentationFastG Dt fuel a d).1 = true)
    (hsome : CPolyG.cIntegrateGFull Dt fuel a d cands = some res)
    (hrecon : amG α (toPolyG (canonicalRepresentationFastG Dt fuel a d).2.2.1)
          / amG α (toPolyG (canonicalRepresentationFastG Dt fuel a d).2.2.2)
        = amG α (toPolyG a) / amG α (toPolyG d))
    (hherm : towerFractionFieldDerivG Dt
            (amG α (toPolyG (CPolyG.cIntegrateReducedG Dt fuel
                  (canonicalRepresentationFastG Dt fuel a d).2.2.1
                  (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands).rational.1)
              / amG α (toPolyG (CPolyG.cIntegrateReducedG Dt fuel
                  (canonicalRepresentationFastG Dt fuel a d).2.2.1
                  (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands).rational.2))
          + amG α (toPolyG (cHermiteReduceTowerG Dt fuel
                (canonicalRepresentationFastG Dt fuel a d).2.2.1
                (canonicalRepresentationFastG Dt fuel a d).2.2.2).2.1)
            / amG α (toPolyG (cHermiteReduceTowerG Dt fuel
                (canonicalRepresentationFastG Dt fuel a d).2.2.1
                (canonicalRepresentationFastG Dt fuel a d).2.2.2).2.2)
        = amG α (toPolyG (canonicalRepresentationFastG Dt fuel a d).2.2.1)
            / amG α (toPolyG (canonicalRepresentationFastG Dt fuel a d).2.2.2))
    (hden : toPolyG (cHermiteReduceTowerG Dt fuel
          (canonicalRepresentationFastG Dt fuel a d).2.2.1
          (canonicalRepresentationFastG Dt fuel a d).2.2.2).2.2 = Lagrange.nodal s id)
    (hA : (toPolyG (cHermiteReduceTowerG Dt fuel
          (canonicalRepresentationFastG Dt fuel a d).2.2.1
          (canonicalRepresentationFastG Dt fuel a d).2.2.2).2.1).degree < s.card)
    (hnorm : ∀ β ∈ s, w ≠ β′)
    (hform : (CPolyG.cIntegrateReducedG Dt fuel
            (canonicalRepresentationFastG Dt fuel a d).2.2.1
            (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands).logs.map
          (fun cv => (CFieldSpec.toK cv.1, toPolyG cv.2))
        = s.toList.map (fun β =>
            ((toPolyG (cHermiteReduceTowerG Dt fuel
                  (canonicalRepresentationFastG Dt fuel a d).2.2.1
                  (canonicalRepresentationFastG Dt fuel a d).2.2.2).2.1).eval β
                / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β,
              X - C β))) :
    towerFractionFieldDerivG Dt (amG α (toPolyG res.rational.1) / amG α (toPolyG res.rational.2))
        + logResidueSumG Dt res.logs
      = amG α (toPolyG a) / amG α (toPolyG d) := by
  -- pin the output: `res` is the reduced capstone on the simple part `(cₙ, dₙ)`
  have hres : res = CPolyG.cIntegrateReducedG Dt fuel (canonicalRepresentationFastG Dt fuel a d).2.2.1
      (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands := by
    rw [cIntegrateGFull_pureNormal_eq Dt fuel a d cands hb hfp] at hsome
    exact (Option.some.injEq _ _ ▸ hsome).symm
  subst hres
  -- the reduced-case primitive identity gives `D(g) + logResidueSumG = amG cₙ/amG dₙ`; `hrecon` ⟹ `= a/d`
  rw [field_identity_of_cIntegrateReducedG_primitive Dt fuel
    (canonicalRepresentationFastG Dt fuel a d).2.2.1
    (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands s w hDt hherm hden hA hnorm hform]
  exact hrecon

/-! ### ★ The PRIMITIVE one-shot at the level-1 carrier `α = QFunNZG ℚ = ℚ(x)`

Instantiating the primitive one-shot at the generic level-1 carrier `α = QFunNZG ℚ`, where `CFieldSpec.K
(QFunNZG ℚ) = RatFunc ℚ` (genuine `Algebra ℚ`). The concrete checker-free `cIntegrateGFull = some res ⟹
D(res) = integrand` for primitive (logarithmic) tower extensions over `ℚ(x)(t)`. The local instance bridges
the carrier abbreviation to `RatFunc ℚ`. -/

/-- The engine carrier `CFieldSpec.K (QFunNZG ℚ)` is `RatFunc ℚ`, a `ℚ`-algebra. Local instance so the
`QFunNZG ℚ` deliverable synthesizes the **same** `Algebra ℚ` the bridge `towerFractionFieldDerivG` uses. -/
noncomputable local instance : Algebra ℚ (CFieldSpec.K (QFunNZG ℚ)) :=
  inferInstanceAs (Algebra ℚ (RatFunc ℚ))

/-- **★★★ The PRIMITIVE one-shot for `cIntegrateGFull` over `ℚ(x)(t)`** — the milestone at the level-1 carrier
`α = QFunNZG ℚ` (`CFieldSpec.K (QFunNZG ℚ) = RatFunc ℚ`): for a primitive monomial `toPolyG Dt = C w`, if the
full driver returns `some res` on the primitive pure-normal branch, given the canonical reconstruction, the
Hermite half, and the per-root reassembly of the residue logs, the field-level identity `D(res) +
logResidueSumG Dt res.logs = amG a/amG d` holds over `RatFunc ℚ` — **checker-free, no native_decide**. The
concrete unconditional-in-the-primitive-regime one-shot at ℚ(x)(t), gated only on the abstract engine inputs.
The `QFunNZG ℚ` instance of `cIntegrateGFull_primitive_oneShot`. -/
theorem cIntegrateGFull_primitive_oneShot_qfunNZG (Dt : CPolyG (QFunNZG ℚ)) (fuel : ℕ)
    (a d : CPolyG (QFunNZG ℚ)) (cands : List (QFunNZG ℚ)) (res : IntegralResultG (QFunNZG ℚ))
    (s : Finset (CFieldSpec.K (QFunNZG ℚ))) (w : CFieldSpec.K (QFunNZG ℚ))
    (hDt : toPolyG Dt = C w)
    (hb : CPolyG.cisZeroG (canonicalRepresentationFastG Dt fuel a d).2.1.1 = true)
    (hfp : CPolyG.cisZeroG (canonicalRepresentationFastG Dt fuel a d).1 = true)
    (hsome : CPolyG.cIntegrateGFull Dt fuel a d cands = some res)
    (hrecon : amG (QFunNZG ℚ) (toPolyG (canonicalRepresentationFastG Dt fuel a d).2.2.1)
          / amG (QFunNZG ℚ) (toPolyG (canonicalRepresentationFastG Dt fuel a d).2.2.2)
        = amG (QFunNZG ℚ) (toPolyG a) / amG (QFunNZG ℚ) (toPolyG d))
    (hherm : towerFractionFieldDerivG Dt
            (amG (QFunNZG ℚ) (toPolyG (CPolyG.cIntegrateReducedG Dt fuel
                  (canonicalRepresentationFastG Dt fuel a d).2.2.1
                  (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands).rational.1)
              / amG (QFunNZG ℚ) (toPolyG (CPolyG.cIntegrateReducedG Dt fuel
                  (canonicalRepresentationFastG Dt fuel a d).2.2.1
                  (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands).rational.2))
          + amG (QFunNZG ℚ) (toPolyG (cHermiteReduceTowerG Dt fuel
                (canonicalRepresentationFastG Dt fuel a d).2.2.1
                (canonicalRepresentationFastG Dt fuel a d).2.2.2).2.1)
            / amG (QFunNZG ℚ) (toPolyG (cHermiteReduceTowerG Dt fuel
                (canonicalRepresentationFastG Dt fuel a d).2.2.1
                (canonicalRepresentationFastG Dt fuel a d).2.2.2).2.2)
        = amG (QFunNZG ℚ) (toPolyG (canonicalRepresentationFastG Dt fuel a d).2.2.1)
            / amG (QFunNZG ℚ) (toPolyG (canonicalRepresentationFastG Dt fuel a d).2.2.2))
    (hden : toPolyG (cHermiteReduceTowerG Dt fuel
          (canonicalRepresentationFastG Dt fuel a d).2.2.1
          (canonicalRepresentationFastG Dt fuel a d).2.2.2).2.2 = Lagrange.nodal s id)
    (hA : (toPolyG (cHermiteReduceTowerG Dt fuel
          (canonicalRepresentationFastG Dt fuel a d).2.2.1
          (canonicalRepresentationFastG Dt fuel a d).2.2.2).2.1).degree < s.card)
    (hnorm : ∀ β ∈ s, w ≠ β′)
    (hform : (CPolyG.cIntegrateReducedG Dt fuel
            (canonicalRepresentationFastG Dt fuel a d).2.2.1
            (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands).logs.map
          (fun cv => (CFieldSpec.toK cv.1, toPolyG cv.2))
        = s.toList.map (fun β =>
            ((toPolyG (cHermiteReduceTowerG Dt fuel
                  (canonicalRepresentationFastG Dt fuel a d).2.2.1
                  (canonicalRepresentationFastG Dt fuel a d).2.2.2).2.1).eval β
                / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β,
              X - C β))) :
    towerFractionFieldDerivG Dt
        (amG (QFunNZG ℚ) (toPolyG res.rational.1) / amG (QFunNZG ℚ) (toPolyG res.rational.2))
        + logResidueSumG Dt res.logs
      = amG (QFunNZG ℚ) (toPolyG a) / amG (QFunNZG ℚ) (toPolyG d) :=
  cIntegrateGFull_primitive_oneShot Dt fuel a d cands res s w hDt hb hfp hsome hrecon hherm hden hA
    hnorm hform

/-! ### Restatements against the intended wording (anonymous `example`s) -/

-- ★ THE LIST↔FINSET BRIDGE: the engine-shaped `List.sum` over the per-root list of `(residue, t−α)` pairs
-- equals `a/d` over `RatFunc K`, for a primitive monomial `Dt = C w` — the `List` form of the proven Finset
-- residue match (via `Finset.sum_map_toList`).
example {K : Type*} [Field K] [Differential K] [Algebra ℚ K] (s : Finset K) (a : K[X]) (w : K)
    (hA : a.degree < s.card) (hnorm : ∀ α ∈ s, w ≠ α′) :
    ((s.toList.map (fun α =>
          (a.eval α / (Differential.implicitDeriv (C w) (Lagrange.nodal s id)).eval α, X - C α))).map
        (fun cv =>
          algebraMap K[X] (RatFunc K) (C cv.1)
            * (extendDeriv (Differential.implicitDeriv (C w))
                  (algebraMap K[X] (RatFunc K) cv.2)
                / algebraMap K[X] (RatFunc K) cv.2))).sum
      = algebraMap K[X] (RatFunc K) a / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id) :=
  ResidueMatchTower.primitive_residue_match_list s a w hA hnorm

-- ★★★ THE MILESTONE at `α = QFunNZG ℚ` (checker-free, no native_decide): `cIntegrateGFull = some res ⟹
-- D(res) = a/d` over `RatFunc ℚ` for primitive `Dt`, gated only on the abstract engine inputs (canonical
-- reconstruction + Hermite telescoping + per-root residue-log reassembly; RT cancellation automatic).
example (Dt : CPolyG (QFunNZG ℚ)) (fuel : ℕ) (a d : CPolyG (QFunNZG ℚ)) (cands : List (QFunNZG ℚ))
    (res : IntegralResultG (QFunNZG ℚ)) (s : Finset (CFieldSpec.K (QFunNZG ℚ)))
    (w : CFieldSpec.K (QFunNZG ℚ)) (hDt : toPolyG Dt = C w)
    (hb : CPolyG.cisZeroG (canonicalRepresentationFastG Dt fuel a d).2.1.1 = true)
    (hfp : CPolyG.cisZeroG (canonicalRepresentationFastG Dt fuel a d).1 = true)
    (hsome : CPolyG.cIntegrateGFull Dt fuel a d cands = some res)
    (hrecon : amG (QFunNZG ℚ) (toPolyG (canonicalRepresentationFastG Dt fuel a d).2.2.1)
          / amG (QFunNZG ℚ) (toPolyG (canonicalRepresentationFastG Dt fuel a d).2.2.2)
        = amG (QFunNZG ℚ) (toPolyG a) / amG (QFunNZG ℚ) (toPolyG d))
    (hherm : towerFractionFieldDerivG Dt
            (amG (QFunNZG ℚ) (toPolyG (CPolyG.cIntegrateReducedG Dt fuel
                  (canonicalRepresentationFastG Dt fuel a d).2.2.1
                  (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands).rational.1)
              / amG (QFunNZG ℚ) (toPolyG (CPolyG.cIntegrateReducedG Dt fuel
                  (canonicalRepresentationFastG Dt fuel a d).2.2.1
                  (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands).rational.2))
          + amG (QFunNZG ℚ) (toPolyG (cHermiteReduceTowerG Dt fuel
                (canonicalRepresentationFastG Dt fuel a d).2.2.1
                (canonicalRepresentationFastG Dt fuel a d).2.2.2).2.1)
            / amG (QFunNZG ℚ) (toPolyG (cHermiteReduceTowerG Dt fuel
                (canonicalRepresentationFastG Dt fuel a d).2.2.1
                (canonicalRepresentationFastG Dt fuel a d).2.2.2).2.2)
        = amG (QFunNZG ℚ) (toPolyG (canonicalRepresentationFastG Dt fuel a d).2.2.1)
            / amG (QFunNZG ℚ) (toPolyG (canonicalRepresentationFastG Dt fuel a d).2.2.2))
    (hden : toPolyG (cHermiteReduceTowerG Dt fuel
          (canonicalRepresentationFastG Dt fuel a d).2.2.1
          (canonicalRepresentationFastG Dt fuel a d).2.2.2).2.2 = Lagrange.nodal s id)
    (hA : (toPolyG (cHermiteReduceTowerG Dt fuel
          (canonicalRepresentationFastG Dt fuel a d).2.2.1
          (canonicalRepresentationFastG Dt fuel a d).2.2.2).2.1).degree < s.card)
    (hnorm : ∀ β ∈ s, w ≠ β′)
    (hform : (CPolyG.cIntegrateReducedG Dt fuel
            (canonicalRepresentationFastG Dt fuel a d).2.2.1
            (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands).logs.map
          (fun cv => (CFieldSpec.toK cv.1, toPolyG cv.2))
        = s.toList.map (fun β =>
            ((toPolyG (cHermiteReduceTowerG Dt fuel
                  (canonicalRepresentationFastG Dt fuel a d).2.2.1
                  (canonicalRepresentationFastG Dt fuel a d).2.2.2).2.1).eval β
                / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β,
              X - C β))) :
    towerFractionFieldDerivG Dt
        (amG (QFunNZG ℚ) (toPolyG res.rational.1) / amG (QFunNZG ℚ) (toPolyG res.rational.2))
        + logResidueSumG Dt res.logs
      = amG (QFunNZG ℚ) (toPolyG a) / amG (QFunNZG ℚ) (toPolyG d) :=
  cIntegrateGFull_primitive_oneShot_qfunNZG Dt fuel a d cands res s w hDt hb hfp hsome hrecon hherm
    hden hA hnorm hform

/-! ### ★ Status — the list↔Finset bridge + the primitive `cIntegrateGFull` one-shot, axiom-clean

PROVEN (axiom-clean `[propext, Classical.choice, Quot.sound]`, **no** `native_decide`, **no** `sorry`):
* **The list↔Finset bridge** (`primitive_residue_match_list` / `…_engine`) — the engine-shaped `List.sum`
  over the per-root list IS the proven Finset residue match, via `Finset.sum_map_toList`. The genuinely
  "mechanical but unwritten" piece, now written.
* **The primitive engine `hmatch`** (`primitive_engine_hmatch`) — discharges the engine's RT residue-match
  hypothesis for the primitive case, given the per-root reassembly `hform`. The RT polynomial-part
  cancellation is AUTOMATIC (`ResidueMatchTower.primitive_cancel`), so the primitive regime needs **no
  integrability witness**.
* **The reduced-case primitive identity** (`field_identity_of_cIntegrateReducedG_primitive`) and **the
  `cIntegrateGFull` PRIMITIVE one-shot** (`cIntegrateGFull_primitive_oneShot` / `…_qfunNZG`) — for the
  primitive pure-normal branch, `cIntegrateGFull = some res ⟹ D(res) = a/d`, checker-free, gated only on the
  abstract engine inputs (canonical reconstruction `hrecon`, Hermite half `hherm`, per-root reassembly
  `hform`).

★ THE PRIMITIVE ONE-SHOT (pure-normal branch): closed CHECKER-FREE and axiom-clean. It is NOT literally
hypothesis-free: it is gated on three ABSTRACT engine-success facts — the canonical reconstruction
(`canonicalRepresentationFastG_reconstructs`, EXISTS at `QFunNZG ℚ`), the Hermite half
(`cHermiteReduceTowerG_telescope_seed`, EXISTS, given per-power identities), and the per-root reassembly of
the residue logs (`hform`, the `cLogPartG` grouped-GCD ↔ Lagrange per-root output — the engine gcd/resultant
compute-bridge, the ONLY genuinely-unwritten residual, mechanical Lagrange-interpolation bookkeeping, the
SAME pattern as the algebraic `toPolyG_cAlgResidueResultant_eq_of_eval`). The primitive-SPECIFIC content (the
RT cancellation, which in the hyperexp/hypertangent case is the integrability witness) is fully discharged
here by `primitive_cancel` — the primitive regime needs no extra integrability hypothesis.

THE GENERAL-CASE `hcancel` (the documented STRETCH — NOT attempted, precise status): for a NON-primitive
monomial (`deg_t (toPolyG Dt) ≥ 1`, hyperexponential `Dt = η′·t` / hypertangent), the RT polynomial-part
cancellation `∑_α c_α·((v − Cα′) /ₘ (t−α)) = 0` (`ResidueMatchTower.monomial_residue_match_of_cancel`'s
`hcancel`) is GENUINELY EXTRA content — for `Dt = η′·t` it reduces to `∑_α c_α = 0`, the integrability
condition (`a/d` integrable in the log part alone). The engine discharges it operationally (resultant fully
split + leftover proper ⟹ `∑ c_α = 0`), but the abstract proof needs the integrability witness routed
through a `t`-power/degree argument — Bronstein's reduction of the hyperexp case. Precisely: the engine-
success fact that would discharge it is *the residue resultant `cResidueResultantTowerG` splitting
completely over the candidate set AND the Hermite leftover `hNum/hDen` being proper* — which forces `∑ c_α =
0` (the exponential correction). That degree argument is the unwritten general-case piece. -/

#print axioms ResidueMatchTower.primitive_residue_match_list
#print axioms primitive_residue_match_list_engine
#print axioms primitive_engine_hmatch
#print axioms field_identity_of_cIntegrateReducedG_primitive
#print axioms cIntegrateGFull_primitive_oneShot
#print axioms cIntegrateGFull_primitive_oneShot_qfunNZG

end DeepWiki.SymbolicIntegration