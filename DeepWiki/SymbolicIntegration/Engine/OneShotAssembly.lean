import DeepWiki.SymbolicIntegration.Engine.ResidueMatchSoundness
import DeepWiki.SymbolicIntegration.Core.Differential.FractionFieldDerivLinearFactor
import DeepWiki.SymbolicIntegration.Engine.OneShotSoundness
import DeepWiki.SymbolicIntegration.Engine.UnifiedFuelFree
import DeepWiki.SymbolicIntegration.Engine.ResidueLogPart
import DeepWiki.SymbolicIntegration.Engine.OneShotAssembly.ResidueMatch

/-! # The unconditional one-shot soundness for the PRIMITIVE (logarithmic) case (Bronstein §5.6)

`ComputableResidueMatchSoundness` proved the ★ Rothstein–Trager **residue match** UNCONDITIONALLY for a
primitive monomial `Dt = C w` — `primitive_monomial_residue_match` (over `K[X]`) /
`primitive_monomial_residue_match_engine` (in the engine's `am`/`towerFractionFieldDeriv` vocabulary):
`∑_{α∈s} C(c_α)·D(t−α)/(t−α) = a/d` for `d = ∏_{α∈s}(t−α)`. `ComputableLogPartTowerSoundness` reduced the
checker-free reduced-case one-shot to that residue match
(`field_identity_of_cIntegrateReducedG_of_residueMatch`, gated on the `List`-sum `hmatch`).
`ComputableOneShotSoundness` proved the polynomial branch
(`field_identity_of_cPolyRischDEG_qfunNZG`).

The engine's `hmatch` is a **`List` sum** over the residue logs `cLogPart` returns — pairs `(cᵢ, vᵢ)` with
`vᵢ = gcd_t(d, a − cᵢ·Dd)`. The proven primitive residue match is the **`Finset`-over-roots** form. This file
builds the **list↔Finset bridge** connecting them: the per-root list `s.toList.map (fun α => (c_α, t−α))` has
the SAME `List.sum` as the `Finset.sum` over `s` (`Finset.sum_map_toList`), so the proven Finset identity
discharges the engine `hmatch` for the per-root log form. Composing with the fuel-free pure-normal driver
branch gives **`cIntegrateGFullWf_primitive_oneShot`** — the checker-free one-shot for primitive
(logarithmic) tower extensions.

What this file delivers (axiom-clean `[propext, Classical.choice, Quot.sound]`, **no** `native_decide`):

* **`primitive_residue_match_list`** — the list↔Finset bridge: the engine-shaped `List.map (...) |>.sum` over
  the per-root list of `(residue, t−α)` pairs equals `a/d` over `RatFunc K`, by `Finset.sum_map_toList` +
  `primitive_monomial_residue_match`. The `List`-form residue match the engine's `hmatch` consumes.
* **`primitive_residue_match_list_engine`** — the same in the engine's `am`/`towerFractionFieldDeriv`
  vocabulary, over `K = CFieldSpec.K α`.
* **★ The PRIMITIVE one-shot scope** — the precise residual hypotheses (the engine's gcd/resultant
  compute-bridges + the abstract Hermite step), with the RT-residue cancellation shown AUTOMATIC for the
  primitive case (`primitive_cancel`), so the primitive regime needs NO integrability witness.
* **★★ The fuel-free HYPEREXPONENTIAL one-shot** (`cIntegrateGFullWf_hyperexp_oneShot` / `…_qfunNZG`) — the
  raw fuel-free full driver gives `D(res) = a/d` for a hyperexp `Dt = η′·t` (`toPoly Dt = C b·X`,
  `b ≠ 0`), gated on the same abstract engine inputs PLUS the integrability witness `hsum : ∑c = 0`. Built on
  the UNCONDITIONAL
  decomposition `monomial_residue_sum_eq_cancel_add` (residue sum = cancel sum + a/d) and the iff
  `hyperexp_residue_match_iff_sum_zero` (residue match `= a/d` ⟺ `∑c = 0`), threaded through the engine via
  `hyperexp_engine_hmatch`. So the checker-free one-shot now covers the PRIMITIVE and EXPONENTIAL cases.

★ The hyperexp one-shot is GENUINELY CONDITIONAL on `hsum : ∑c = 0`, NOT unconditional: `cIntegrateGFullWf`'s
pure-normal branch returns `some` even when `∑c ≠ 0` (it emits the §5.6 RT logs that OVERSHOOT a hyperexp
normal part by `R = η·∑c`; the §5.9 residual feedback that fixes this lives in the SEPARATE driver
`cIntegrateHyperexpFull`). So "engine success ⟹ `∑c = 0`" is FALSE for this driver — `∑c = 0` is a true side
condition on the integrand, not an algorithm-termination consequence. See the closing status for the full
obstruction analysis. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac

/-! ### Task 1 (engine vocabulary): the list↔Finset bridge over `K = CFieldSpec.K α`

`primitive_monomial_residue_match_engine` is the Finset form in the engine's `am`/`towerFractionFieldDeriv`
vocabulary. Its `List`-form bridge restates `primitive_residue_match_list` over the tower carrier
`K = CFieldSpec.K α` with `Dt`'s `toPoly = C w`, through the definitional `am = algebraMap` and the
`towerFractionFieldDeriv` unfolding — the `List`-shaped primitive residue match exactly as the engine's
`logResidueSumG_eq_of_residue_match` consumes it (a `List` of `(residue, factor)` pairs over `CFieldSpec.K α`). -/

open DensePoly CFrac

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

omit [CFieldSpec α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
variable [CPolyGcd DensePoly α] [CPolySplitFactor DensePoly α] in
/-- `canonicalRepresentationFast` is in the pure-normal branch. -/
structure IsPureNormalBranch (Dt a d : DensePoly α) : Prop where
  /-- The special part vanishes. -/
  special_zero : DensePoly.cisZero (canonicalRepresentationFast Dt a d).2.1.1 = true
  /-- The polynomial part vanishes. -/
  poly_zero : DensePoly.cisZero (canonicalRepresentationFast Dt a d).1 = true

omit [CFieldSpec α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
variable [CPolyGcd DensePoly α] [CPolySplitFactor DensePoly α] in
/-- `canonicalRepresentationFast` is in the polynomial branch. -/
structure IsPolynomialBranch (Dt a d : DensePoly α) : Prop where
  /-- The special part vanishes. -/
  special_zero : DensePoly.cisZero (canonicalRepresentationFast Dt a d).2.1.1 = true
  /-- The polynomial part is nonzero. -/
  poly_nonzero : DensePoly.cisZero (canonicalRepresentationFast Dt a d).1 = false

/-- **★ The list↔Finset bridge in the engine's vocabulary** — for a primitive monomial with
`toPoly Dt = C w` (`w ∈ CFieldSpec.K α`), a squarefree `d = ∏_{β∈s}(t−β)`, `deg a < #s`, every root normal,
the engine-shaped **`List` sum** over the per-root list of `(c_β, X − C β)` pairs equals `a/d` over
`RatFunc (CFieldSpec.K α)`, with `D = towerFractionFieldDeriv Dt`. The `K[X]`-level
`primitive_residue_match_list` transported through the definitional `am = algebraMap` and the
`towerFractionFieldDeriv` unfolding — the residue match in exactly the `List` shape the engine consumes. -/
theorem primitive_residue_match_list_engine (Dt : DensePoly α) (s : Finset (CFieldSpec.K α))
    (a : (CFieldSpec.K α)[X]) (w : CFieldSpec.K α) (hDt : toPoly Dt = C w)
    (hA : a.degree < s.card) (hnorm : ∀ β ∈ s, w ≠ β′) :
    ((s.toList.map (fun β =>
          (a.eval β / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β,
            X - C β))).map
        (fun cv =>
          am α (C cv.1)
            * (towerFractionFieldDeriv Dt (am α cv.2) / am α cv.2))).sum
      = am α a / am α (Lagrange.nodal s id) := by
  show ((s.toList.map (fun β =>
          (a.eval β / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β,
            X - C β))).map
        (fun cv =>
          algebraMap (CFieldSpec.K α)[X] (RatFunc (CFieldSpec.K α)) (C cv.1)
            * (extendDeriv (Differential.implicitDeriv (toPoly Dt))
                  (algebraMap _ (RatFunc (CFieldSpec.K α)) cv.2)
                / algebraMap _ (RatFunc (CFieldSpec.K α)) cv.2))).sum = _
  rw [hDt]
  exact ResidueMatchTower.primitive_residue_match_list s a w hA hnorm

/-! ### Task 2: discharge the engine's `hmatch` for the PRIMITIVE case (per-root log form)

`logResidueSumG_eq_of_residue_match` / `field_identity_of_cIntegrateReducedG_of_residueMatch` consume the
`hmatch` hypothesis — the `List.map (...) |>.sum` over the engine's `res.logs` equals the (Hermite leftover)
simple integrand. The bridge `primitive_residue_match_list_engine` supplies exactly that sum for the
**per-root log form** `res.logs = s.toList.map (engine-pair-builder)`. The remaining content is purely
structural: the engine's `res.logs`, read through `(toK cv.1, toPoly cv.2)`, must BE the per-root list of
`(residue β, X − C β)` pairs (the `cLogPart` grouped-GCD output reassembled into Lagrange per-root factors,
squarefree denominator factored as `∏(t−β)`). We carry that reassembly as the explicit structural hypothesis
`hform` (the engine's gcd/resultant compute-bridge — the documented mechanical residual), and discharge the
residue match through it. The primitive specialization where `primitive_cancel` makes the RT polynomial-part
cancellation automatic, so NO integrability witness is needed. -/

/-- **★ The primitive engine `hmatch`, discharged through the per-root reassembly** — for a primitive
monomial `toPoly Dt = C w`, a squarefree `hDen` factored as `∏_{β∈s}(t−β)` (`toPoly hDen = Lagrange.nodal
s id`, `deg (toPoly hNum) < #s`, every root normal), and the engine residue logs `logs` whose
`(toK cv.1, toPoly cv.2)`-images ARE the per-root list `s.toList.map (fun β => (residue β, X − C β))`
(`hform` — the `cLogPart` grouped-GCD ↔ Lagrange per-root reassembly, the documented engine compute-bridge),
the engine residue-match sum `∑_{(c,v)∈logs} am(C(toK c))·(D(log v)) = am(hNum)/am(hDen)` over `RatFunc
(CFieldSpec.K α)`. Rewrites the engine sum through `hform` into the bridge's per-root form, which
`primitive_residue_match_list_engine` sends to `hNum/hDen`. The RT polynomial-part cancellation is automatic
in the primitive case (`ResidueMatchTower.primitive_cancel`), so this needs no integrability witness — the
residue match the reduced-case one-shot consumes, primitive case. -/
theorem primitive_engine_hmatch (Dt : DensePoly α) (s : Finset (CFieldSpec.K α))
    (hNum hDen : DensePoly α) (w : CFieldSpec.K α) (logs : List (α × DensePoly α))
    (hDt : toPoly Dt = C w)
    (hden : toPoly hDen = Lagrange.nodal s id)
    (hA : (toPoly hNum).degree < s.card) (hnorm : ∀ β ∈ s, w ≠ β′)
    (hform : logs.map (fun cv => (CFieldSpec.toK cv.1, toPoly cv.2))
      = s.toList.map (fun β =>
          ((toPoly hNum).eval β
              / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β,
            X - C β))) :
    (logs.map (fun cv =>
          am α (Polynomial.C (CFieldSpec.toK cv.1))
            * (towerFractionFieldDeriv Dt (am α (toPoly cv.2)) / am α (toPoly cv.2)))).sum
      = am α (toPoly hNum) / am α (toPoly hDen) := by
  -- the engine summand factors through `(toK cv.1, toPoly cv.2)`: rewrite the mapped list by `hform`
  have hsummand : (logs.map (fun cv =>
        am α (Polynomial.C (CFieldSpec.toK cv.1))
          * (towerFractionFieldDeriv Dt (am α (toPoly cv.2)) / am α (toPoly cv.2))))
      = (logs.map (fun cv => (CFieldSpec.toK cv.1, toPoly cv.2))).map
          (fun p => am α (Polynomial.C p.1)
            * (towerFractionFieldDeriv Dt (am α p.2) / am α p.2)) := by
    rw [List.map_map]; rfl
  rw [hsummand, hform, hden, List.map_map]
  -- now the per-root form of the bridge `primitive_residue_match_list_engine`
  have hbridge := primitive_residue_match_list_engine Dt s (toPoly hNum) w hDt hA hnorm
  rw [List.map_map] at hbridge
  exact hbridge

/-! ### The PRIMITIVE normality side condition `hnorm`, for constant resolvent roots

`primitive_engine_hmatch`/`field_identity_of_cIntegrateReducedG_primitive` take the RT normality side
condition `hnorm : ∀ β ∈ s, w ≠ β′` — every resolvent root `β` is *normal* for the monomial `t′ = w`.
Here `β′` is the **field derivation** `Differential.deriv β` of the root *element* `β ∈ CFieldSpec.K α`
(`CDiffFieldSpec.diffK`), NOT the polynomial derivative of `C w` (which is `0`): so `β′` is genuinely an
arbitrary field element and `hnorm` is a true side condition, not a tautology — it is exactly Bronstein's
normality hypothesis (Thm 5.6.1) and is *not* abstractly dischargeable in general (see the closing status).

The one regime where it discharges cheaply: when every resolvent root is a **constant** (`β′ = 0` — the
generic primitive case, where the RT logarithm coefficients are constants), `hnorm` collapses to `w ≠ 0`,
the genuine new-monomial condition `t′ = w ≠ 0`. We isolate that reduction. -/

omit [Algebra ℚ (CFieldSpec.K α)] in
/-- **The primitive normality side condition from constant resolvent roots** — for a primitive monomial
`t′ = w` with `w ≠ 0`, if every resolvent root `β ∈ s` is a *constant* (`β′ = 0`, the field derivation of
the root element vanishing), then every root is normal: `∀ β ∈ s, w ≠ β′`. The dischargeable core of the
RT normality hypothesis `hnorm` — `β′ = 0` makes `w = β′` say `w = 0`, contradicting `w ≠ 0`. The genuine
remaining content is root-constancy `β′ = 0` (Bronstein §5.6: the primitive log coefficients are constants),
stated honestly as the hypothesis; `β′` is the field derivation of `β ∈ CFieldSpec.K α`, not a polynomial
derivative. -/
theorem primitive_monomial_norm_of_const_roots (s : Finset (CFieldSpec.K α)) (w : CFieldSpec.K α)
    (hw : w ≠ 0) (hconst : ∀ β ∈ s, β′ = 0) : ∀ β ∈ s, w ≠ β′ := by
  intro β hβ heq
  exact hw (heq.trans (hconst β hβ))

-- The constant-root normality reduction, against its expected wording.
example (s : Finset (CFieldSpec.K α)) (w : CFieldSpec.K α)
    (hw : w ≠ 0) (hconst : ∀ β ∈ s, β′ = 0) : ∀ β ∈ s, w ≠ β′ :=
  primitive_monomial_norm_of_const_roots s w hw hconst

/-! ### The PRIMITIVE `hDd` — the resolvent derivative is nonzero at each (simple, constant) root

`primitive_engine_hmatch`'s per-root assembly (`cIntegrateReducedG_logs_eq_per_root`) takes
`hDd : ∀ β ∈ s, (implicitDeriv Dt (nodal s id)).eval β ≠ 0`. For a primitive monomial `t′ = w` with
`w ≠ 0` and **constant** resolvent roots (`β′ = 0`), this discharges: `implicitDeriv (C w) p =
mapCoeffs p + C w · p′`, the horizontal `mapCoeffs (nodal) = 0` for constant roots, so it is `C w · nodal′`,
and `nodal′` is nonzero at each node (distinct roots, `Lagrange.nodalWeight`). -/

/-- The `nodal` derivative is nonzero at each of its (distinct) nodes: `nodal′(β) ≠ 0` for `β ∈ s`. -/
theorem eval_derivative_nodal_ne_zero {K : Type*} [Field K] [DecidableEq K] (s : Finset K) (β : K)
    (hβ : β ∈ s) : (derivative (Lagrange.nodal s id)).eval β ≠ 0 := by
  have hne := Lagrange.nodalWeight_ne_zero (v := (id : K → K)) (Set.injOn_id _) hβ
  rw [Lagrange.nodalWeight_eq_eval_derivative_nodal (v := (id : K → K)) hβ] at hne
  simp only [id_eq] at hne
  exact fun h0 => hne (by rw [h0]; simp)

/-- The horizontal derivation vanishes on a `nodal` with constant roots: `mapCoeffs (nodal s id) = 0`
when every `β ∈ s` is a constant (`β′ = 0`). -/
theorem mapCoeffs_nodal_eq_zero {K : Type*} [Field K] [Differential K] [DecidableEq K] (s : Finset K)
    (hconst : ∀ β ∈ s, (Differential.deriv : Derivation ℤ K K) β = 0) :
    Differential.mapCoeffs (Lagrange.nodal s id) = 0 := by
  rw [Lagrange.nodal]
  induction s using Finset.induction with
  | empty => simp
  | @insert a t ha ih =>
    rw [Finset.prod_insert ha, Derivation.leibniz]
    have hfa : Differential.mapCoeffs (X - C (id a)) = 0 := by
      rw [map_sub, Differential.mapCoeffs_X, Differential.mapCoeffs_C, id_eq,
        hconst a (Finset.mem_insert_self a t), map_zero, sub_zero]
    rw [hfa, ih (fun β hβ => hconst β (Finset.mem_insert_of_mem hβ))]; simp

/-- **The primitive `hDd` discharge**: for `t′ = C w` (`w ≠ 0`) with constant resolvent roots, the
resolvent derivative `implicitDeriv (C w) (nodal s id)` is nonzero at every node. -/
theorem implicitDeriv_C_nodal_eval_ne_zero {K : Type*} [Field K] [Differential K] [DecidableEq K]
    (w : K) (hw : w ≠ 0) (s : Finset K)
    (hconst : ∀ β ∈ s, (Differential.deriv : Derivation ℤ K K) β = 0) (β : K) (hβ : β ∈ s) :
    (Differential.implicitDeriv (C w) (Lagrange.nodal s id)).eval β ≠ 0 := by
  have hform : Differential.implicitDeriv (C w) (Lagrange.nodal s id)
      = Differential.mapCoeffs (Lagrange.nodal s id) + C w * derivative (Lagrange.nodal s id) := by
    simp [Differential.implicitDeriv, derivative']
  rw [hform, mapCoeffs_nodal_eq_zero s hconst, zero_add, eval_mul, eval_C]
  exact mul_ne_zero hw (eval_derivative_nodal_ne_zero s β hβ)

/-! ### Task 2 (hyperexp): the list↔Finset bridge + the engine `hmatch`, GATED on `∑c = 0`

The hyperexponential analog of `primitive_residue_match_list_engine` / `primitive_engine_hmatch`. The ONLY
difference from the primitive case is that the RT polynomial-part cancellation is NOT automatic: it is the
integrability witness `∑c = 0` (`hsum`), supplied here as an explicit hypothesis (see the closing status for
why `cIntegrateGFullWf`'s success cannot supply it). Given `hsum`, the residue match is discharged exactly as in
the primitive case, through `hyperexp_residue_match_list`. -/

/-- **★ The hyperexp list↔Finset bridge in the engine's vocabulary (given `∑c = 0`)** — for a
hyperexponential monomial `toPoly Dt = C b·X` (`b = η′ ≠ 0`), a squarefree `d = ∏_{β∈s}(t−β)`, `deg a < #s`,
every root normal, **and** the integrability witness `hsum : ∑_β c_β = 0`, the engine-shaped **`List` sum**
over the per-root list of `(c_β, X − C β)` pairs equals `a/d` over `RatFunc (CFieldSpec.K α)`, with
`D = towerFractionFieldDeriv Dt`. The `K[X]`-level `hyperexp_residue_match_list` transported through the
definitional `am = algebraMap` and the `towerFractionFieldDeriv` unfolding — the residue match in exactly
the `List` shape the engine consumes, hyperexp case (the integrability witness is the only extra content over
the primitive `primitive_residue_match_list_engine`). -/
theorem hyperexp_residue_match_list_engine (Dt : DensePoly α) (s : Finset (CFieldSpec.K α))
    (a : (CFieldSpec.K α)[X]) (b : CFieldSpec.K α) (hb : b ≠ 0) (hDt : toPoly Dt = C b * X)
    (hA : a.degree < s.card) (hnorm : ∀ β ∈ s, (C b * X).eval β ≠ β′)
    (hsum : ∑ β ∈ s, a.eval β / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β
      = 0) :
    ((s.toList.map (fun β =>
          (a.eval β / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β,
            X - C β))).map
        (fun cv =>
          am α (C cv.1)
            * (towerFractionFieldDeriv Dt (am α cv.2) / am α cv.2))).sum
      = am α a / am α (Lagrange.nodal s id) := by
  show ((s.toList.map (fun β =>
          (a.eval β / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β,
            X - C β))).map
        (fun cv =>
          algebraMap (CFieldSpec.K α)[X] (RatFunc (CFieldSpec.K α)) (C cv.1)
            * (extendDeriv (Differential.implicitDeriv (toPoly Dt))
                  (algebraMap _ (RatFunc (CFieldSpec.K α)) cv.2)
                / algebraMap _ (RatFunc (CFieldSpec.K α)) cv.2))).sum = _
  rw [hDt] at hsum ⊢
  exact ResidueMatchTower.hyperexp_residue_match_list s a b hb hA hnorm hsum

/-- **★ The hyperexp engine `hmatch`, discharged through the per-root reassembly (given `∑c = 0`)** — for a
hyperexponential monomial `toPoly Dt = C b·X` (`b = η′ ≠ 0`), a squarefree `hDen` factored as
`∏_{β∈s}(t−β)`, `deg (toPoly hNum) < #s`, every root normal, the integrability witness
`hsum : ∑_β c_β = 0`, and the engine residue logs `logs` whose `(toK cv.1, toPoly cv.2)`-images ARE the
per-root list `s.toList.map (fun β => (residue β, X − C β))` (`hform`), the engine residue-match sum
`∑_{(c,v)∈logs} am(C(toK c))·(D(log v)) = am(hNum)/am(hDen)` over `RatFunc (CFieldSpec.K α)`. Rewrites the
engine sum through `hform` into the bridge's per-root form, which `hyperexp_residue_match_list_engine` (with
`hsum`) sends to `hNum/hDen`. The hyperexp analog of `primitive_engine_hmatch`: identical structure, with the
integrability witness `∑c = 0` the only extra hypothesis (the RT cancellation `primitive_cancel` gives the
primitive case for free is, for hyperexp, exactly `hsum`). -/
theorem hyperexp_engine_hmatch (Dt : DensePoly α) (s : Finset (CFieldSpec.K α))
    (hNum hDen : DensePoly α) (b : CFieldSpec.K α) (hb : b ≠ 0) (logs : List (α × DensePoly α))
    (hDt : toPoly Dt = C b * X)
    (hden : toPoly hDen = Lagrange.nodal s id)
    (hA : (toPoly hNum).degree < s.card) (hnorm : ∀ β ∈ s, (C b * X).eval β ≠ β′)
    (hsum : ∑ β ∈ s,
        (toPoly hNum).eval β / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β
      = 0)
    (hform : logs.map (fun cv => (CFieldSpec.toK cv.1, toPoly cv.2))
      = s.toList.map (fun β =>
          ((toPoly hNum).eval β
              / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β,
            X - C β))) :
    (logs.map (fun cv =>
          am α (Polynomial.C (CFieldSpec.toK cv.1))
            * (towerFractionFieldDeriv Dt (am α (toPoly cv.2)) / am α (toPoly cv.2)))).sum
      = am α (toPoly hNum) / am α (toPoly hDen) := by
  -- the engine summand factors through `(toK cv.1, toPoly cv.2)`: rewrite the mapped list by `hform`
  have hsummand : (logs.map (fun cv =>
        am α (Polynomial.C (CFieldSpec.toK cv.1))
          * (towerFractionFieldDeriv Dt (am α (toPoly cv.2)) / am α (toPoly cv.2))))
      = (logs.map (fun cv => (CFieldSpec.toK cv.1, toPoly cv.2))).map
          (fun p => am α (Polynomial.C p.1)
            * (towerFractionFieldDeriv Dt (am α p.2) / am α p.2)) := by
    rw [List.map_map]; rfl
  rw [hsummand, hform, hden, List.map_map]
  -- now the per-root form of the bridge `hyperexp_residue_match_list_engine` (with the witness `hsum`)
  have hbridge := hyperexp_residue_match_list_engine Dt s (toPoly hNum) b hb hDt hA hnorm hsum
  rw [List.map_map] at hbridge
  exact hbridge

/-! ### Task 2 (assembly): the reduced-case field identity for the PRIMITIVE case

Composing `primitive_engine_hmatch` (the discharged RT residue match) with the Hermite half `hherm` through
`field_identity_of_reducedG_of_residueMatch` gives the reduced-case field identity `D(g) + logResidueSum =
a/d` for the primitive case — gated only on the abstract Hermite telescoping (`hherm`, supplied by
`cHermiteReduceTowerG_telescope_seed` given the per-power Hermite identities) and the per-root reassembly of
the residue logs (`hform`, the engine gcd/resultant compute-bridge). The RT polynomial-part cancellation is
automatic (`primitive_cancel`), so the primitive regime needs no integrability witness. -/

/-! ### ★ Discharging `hform`: the fuel-free `cLogPart` ↔ per-root reassembly

`hform` asks the fuel-free residue logs `cIntegrateReduced.logs = cLogPart Dt hNum hDen cands` to
equal, under the `(toK ·, toPoly ·)` projection, the per-root list
`s.toList.map (β ↦ (residue β, X − β))`. The residual left explicit is the candidate enumeration
`cRationalResidues Dt hNum hDen cands = s.toList.map residueCand`; the literal log-argument shape is
discharged by `cLogArgTowerG_eq_linear_factor`. -/
omit [Algebra ℚ (CFieldSpec.K α)] in
/-- The canonical selected log argument is literally the residue's linear factor. -/
theorem cLogArgTowerG_eq_linear_factor [CPolyGcd DensePoly α] [DecidableEq (CFieldSpec.K α)]
    (Dt a d : DensePoly α) (c : α) (s : Finset (CFieldSpec.K α)) (β : CFieldSpec.K α)
    (hread : Associated (toPoly (cLogArgTower Dt a d c))
      (gcd (toPoly d) (toPoly (cAmcDd Dt a d c))))
    (hden : toPoly d = Lagrange.nodal s id)
    (hDd : ∀ γ ∈ s, (Differential.implicitDeriv (toPoly Dt) (toPoly d)).eval γ ≠ 0)
    (hdist : ∀ γ ∈ s, ∀ δ ∈ s, γ ≠ δ →
      (toPoly a).eval γ / (Differential.implicitDeriv (toPoly Dt) (toPoly d)).eval γ
        ≠ (toPoly a).eval δ / (Differential.implicitDeriv (toPoly Dt) (toPoly d)).eval δ)
    (hβ : β ∈ s)
    (hc : CFieldSpec.toK c
      = (toPoly a).eval β / (Differential.implicitDeriv (toPoly Dt) (toPoly d)).eval β) :
    toPoly (cLogArgTower Dt a d c) = Polynomial.X - Polynomial.C β := by
  have hassoc : Associated (toPoly (cLogArgTower Dt a d c)) (Polynomial.X - Polynomial.C β) := by
    refine hread.trans ?_
    rw [toPolyG_cAmcDdG, hc]
    nth_rewrite 1 [hden]
    exact Associated.of_eq
      (LogResidueTower.residue_gcd_eq_linear_factor s (toPoly a)
        (Differential.implicitDeriv (toPoly Dt) (toPoly d)) hDd hdist β hβ)
  have hne : toPoly (cLogArgTower Dt a d c) ≠ 0 := by
    intro h
    rw [h] at hassoc
    exact (Polynomial.X_sub_C_ne_zero β) ((associated_zero_iff_eq_zero _).mp hassoc.symm)
  have hmonic : (toPoly (cLogArgTower Dt a d c)).Monic := by
    rw [cLogArgTower]
    have hraw : ¬ CPoly.cisZero (CPolyGcd.compute d (cAmcDd Dt a d c)) = true := by
      intro hzero
      apply hne
      have hzero' : CPoly.toPoly (CPoly.cmonic (CPolyGcd.compute d (cAmcDd Dt a d c))) = 0 := by
        rw [CPoly.toPoly_cmonic, (CPoly.cisZero_iff _).mp hzero, mul_zero]
      simpa only [cLogArgTower, toPoly_list_eq] using hzero'
    simpa only [toPoly_list_eq] using
      CPoly.cmonic_monic (CPolyGcd.compute d (cAmcDd Dt a d c)) hraw
  exact eq_of_monic_of_associated hmonic (Polynomial.monic_X_sub_C β) hassoc

omit [Algebra ℚ (CFieldSpec.K α)] in
/-- The fuel-free reduced logs reassemble into the per-root Lagrange log form. -/
theorem cIntegrateReducedG_logs_eq_per_root [CPolySquarefree DensePoly α] [CPolyGcd DensePoly α]
    [CPolyResultant DensePoly] [DecidableEq (CFieldSpec.K α)]
    (Dt : DensePoly α) (a d : DensePoly α) (cands : List α)
    (s : Finset (CFieldSpec.K α)) (residueCand : CFieldSpec.K α → α)
    (hden : toPoly (cHermiteReduceTower Dt a d).2.2 = Lagrange.nodal s id)
    (hres : DensePoly.cRationalResidues Dt (cHermiteReduceTower Dt a d).2.1
        (cHermiteReduceTower Dt a d).2.2 cands
      = s.toList.map residueCand)
    (hDd : ∀ β ∈ s,
      (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β ≠ 0)
    (hdist : ∀ γ ∈ s, ∀ δ ∈ s, γ ≠ δ →
      (toPoly (cHermiteReduceTower Dt a d).2.1).eval γ
          / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval γ
        ≠ (toPoly (cHermiteReduceTower Dt a d).2.1).eval δ
          / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval δ)
    (hcand : ∀ β ∈ s, CFieldSpec.toK (residueCand β)
      = (toPoly (cHermiteReduceTower Dt a d).2.1).eval β
        / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β)
    (hgcdread : ∀ β ∈ s, Associated
      (toPoly (cLogArgTower Dt (cHermiteReduceTower Dt a d).2.1
          (cHermiteReduceTower Dt a d).2.2 (residueCand β)))
      (gcd (toPoly (cHermiteReduceTower Dt a d).2.2)
          (toPoly (cAmcDd Dt (cHermiteReduceTower Dt a d).2.1
            (cHermiteReduceTower Dt a d).2.2 (residueCand β))))) :
    (DensePoly.cIntegrateReduced Dt a d cands).logs.map
        (fun cv => (CFieldSpec.toK cv.1, toPoly cv.2))
      = s.toList.map (fun β =>
          ((toPoly (cHermiteReduceTower Dt a d).2.1).eval β
              / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β,
            Polynomial.X - Polynomial.C β)) := by
  set hNum := (cHermiteReduceTower Dt a d).2.1 with hNumdef
  set hDen := (cHermiteReduceTower Dt a d).2.2 with hDendef
  show ((DensePoly.cRationalResidues Dt hNum hDen cands).map
      (fun c => (c, cLogArgTower Dt hNum hDen c))).map
      (fun cv => (CFieldSpec.toK cv.1, toPoly cv.2)) = _
  rw [hres, List.map_map, List.map_map]
  refine List.map_congr_left (fun β hβmem => ?_)
  have hβ : β ∈ s := Finset.mem_toList.mp hβmem
  simp only [Function.comp_apply]
  rw [hcand β hβ]
  congr 1
  exact cLogArgTowerG_eq_linear_factor Dt hNum hDen (residueCand β) s β
    (hgcdread β hβ) hden (by rw [hden]; exact hDd)
    (by rw [hden]; exact hdist) hβ
    (by rw [hden]; exact hcand β hβ)

/-- **Realization (Stage 2, primitive): `cIntegrateReduced.logs` is a lawful residue-log part.** The
single `LawfulResidueLogPart` realization for the primitive monomial (`t′ = w`) — `primitive_engine_hmatch`
fed by the per-root reassembly. Under the residue-data contract (`hden`/`hA`/`hnorm`/`hres`/`hDd`/`hdist`/
`hcand`/`hgcdread`). -/
theorem cIntegrateReducedG_lawfulResidueLogPart [CPolySquarefree DensePoly α] [CPolyGcd DensePoly α]
    [CPolyResultant DensePoly] [DecidableEq (CFieldSpec.K α)]
    (Dt : DensePoly α) (a d : DensePoly α) (cands : List α) (s : Finset (CFieldSpec.K α))
    (w : CFieldSpec.K α) (residueCand : CFieldSpec.K α → α)
    (hDt : toPoly Dt = C w)
    (hden : toPoly (cHermiteReduceTower Dt a d).2.2 = Lagrange.nodal s id)
    (hA : (toPoly (cHermiteReduceTower Dt a d).2.1).degree < s.card)
    (hnorm : ∀ β ∈ s, w ≠ β′)
    (hres : DensePoly.cRationalResidues Dt (cHermiteReduceTower Dt a d).2.1
        (cHermiteReduceTower Dt a d).2.2 cands
      = s.toList.map residueCand)
    (hDd : ∀ β ∈ s,
      (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β ≠ 0)
    (hdist : ∀ γ ∈ s, ∀ δ ∈ s, γ ≠ δ →
      (toPoly (cHermiteReduceTower Dt a d).2.1).eval γ
          / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval γ
        ≠ (toPoly (cHermiteReduceTower Dt a d).2.1).eval δ
          / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval δ)
    (hcand : ∀ β ∈ s, CFieldSpec.toK (residueCand β)
      = (toPoly (cHermiteReduceTower Dt a d).2.1).eval β
        / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β)
    (hgcdread : ∀ β ∈ s, Associated
      (toPoly (cLogArgTower Dt (cHermiteReduceTower Dt a d).2.1
          (cHermiteReduceTower Dt a d).2.2 (residueCand β)))
      (gcd (toPoly (cHermiteReduceTower Dt a d).2.2)
          (toPoly (cAmcDd Dt (cHermiteReduceTower Dt a d).2.1
            (cHermiteReduceTower Dt a d).2.2 (residueCand β))))) :
    LawfulResidueLogPart Dt (cHermiteReduceTower Dt a d).2.1 (cHermiteReduceTower Dt a d).2.2
      (DensePoly.cIntegrateReduced Dt a d cands).logs where
  residue_match := primitive_engine_hmatch Dt s (cHermiteReduceTower Dt a d).2.1
    (cHermiteReduceTower Dt a d).2.2 w (DensePoly.cIntegrateReduced Dt a d cands).logs hDt hden hA
    hnorm (cIntegrateReducedG_logs_eq_per_root Dt a d cands s residueCand hden hres hDd hdist hcand
      hgcdread)

/-- **Realization (Stage 2, hyperexp): `cIntegrateReduced.logs` is a lawful residue-log part.** The
`LawfulResidueLogPart` realization for the hyperexponential monomial (`t′ = b·t`, `b ≠ 0`) — identical to
the primitive realization but through `hyperexp_engine_hmatch`, which additionally consumes the
integrability witness `hsum : ∑ c = 0` (the RT polynomial-part cancellation is not automatic here). -/
theorem cIntegrateReducedG_lawfulResidueLogPart_hyperexp [CPolySquarefree DensePoly α]
    [CPolyGcd DensePoly α] [CPolyResultant DensePoly] [DecidableEq (CFieldSpec.K α)]
    (Dt : DensePoly α) (a d : DensePoly α) (cands : List α) (s : Finset (CFieldSpec.K α))
    (b : CFieldSpec.K α) (residueCand : CFieldSpec.K α → α)
    (hb : b ≠ 0) (hDt : toPoly Dt = C b * X)
    (hden : toPoly (cHermiteReduceTower Dt a d).2.2 = Lagrange.nodal s id)
    (hA : (toPoly (cHermiteReduceTower Dt a d).2.1).degree < s.card)
    (hnorm : ∀ β ∈ s, (C b * X).eval β ≠ β′)
    (hsum : ∑ β ∈ s, (toPoly (cHermiteReduceTower Dt a d).2.1).eval β
        / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β = 0)
    (hres : DensePoly.cRationalResidues Dt (cHermiteReduceTower Dt a d).2.1
        (cHermiteReduceTower Dt a d).2.2 cands = s.toList.map residueCand)
    (hDd : ∀ β ∈ s,
      (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β ≠ 0)
    (hdist : ∀ γ ∈ s, ∀ δ ∈ s, γ ≠ δ →
      (toPoly (cHermiteReduceTower Dt a d).2.1).eval γ
          / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval γ
        ≠ (toPoly (cHermiteReduceTower Dt a d).2.1).eval δ
          / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval δ)
    (hcand : ∀ β ∈ s, CFieldSpec.toK (residueCand β)
      = (toPoly (cHermiteReduceTower Dt a d).2.1).eval β
        / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β)
    (hgcdread : ∀ β ∈ s, Associated
      (toPoly (cLogArgTower Dt (cHermiteReduceTower Dt a d).2.1
          (cHermiteReduceTower Dt a d).2.2 (residueCand β)))
      (gcd (toPoly (cHermiteReduceTower Dt a d).2.2)
          (toPoly (cAmcDd Dt (cHermiteReduceTower Dt a d).2.1
            (cHermiteReduceTower Dt a d).2.2 (residueCand β))))) :
    LawfulResidueLogPart Dt (cHermiteReduceTower Dt a d).2.1 (cHermiteReduceTower Dt a d).2.2
      (DensePoly.cIntegrateReduced Dt a d cands).logs where
  residue_match := hyperexp_engine_hmatch Dt s (cHermiteReduceTower Dt a d).2.1
    (cHermiteReduceTower Dt a d).2.2 b hb (DensePoly.cIntegrateReduced Dt a d cands).logs hDt hden
    hA hnorm hsum (cIntegrateReducedG_logs_eq_per_root Dt a d cands s residueCand hden hres hDd hdist
      hcand hgcdread)

/-! ### ★ The `hA` discharge — the Hermite leftover is a PROPER fraction (numer degree < denom degree)

The fuel-free reduced-case one-shots (`field_identity_of_cIntegrateReducedG_primitive` below and its
hyperexp analogue) take the degree side condition

  `hA : (toPoly (cHermiteReduceTower Dt a d).2.1).degree < s.card`

i.e. the Hermite leftover numerator `h_num` has degree `< s.card`, where `s.card` enters as the degree of
the leftover denominator through the squarefree spelling `hden : toPoly (…).2.2 = Lagrange.nodal s id` (the
RT residue factoring). Since `Lagrange.degree_nodal : (nodal s id).degree = #s` over the field
`CFieldSpec.K α`, `hA` is **exactly** the proper-fraction property `deg h_num < deg h_den`. The lemma below
turns that equivalence into a one-step bridge: it discharges `hA` from `hden` plus the intrinsic
proper-fraction property `hproper` (which no longer mentions `s`).

**Status: DISCHARGED for `deg Dt ≤ 1`** (primitive / exp / log — the whole transcendental base regime), by
`cHermiteReduceTowerG_numer_degree_lt_of_degree_le_one` below: the `deg Dt ≤ 1` derivative-degree step
(`toPolyG_residualFraction_proper_of_degree_le_one`) + `g`-properness (`cHermiteReduceTowerG_g_proper`) +
the exact-division degree cancellation (`cHermiteReduceTowerG_leftover_proper_of_residual`). So the
inputs are `haProper` (input properness `deg a < deg d`), the per-factor keystone `hb`/`hv`, and the
exact-division connectors `hdvd`/`hresDen` — engine-regularity facts, not free side conditions. The
`deg Dt ≥ 2` (hypertangent) case genuinely fails generic Hermite (the `b/v¹` summand breaks the margin —
that is a characterized different-algorithm boundary, not a gap). The `hproper` bridge below connects the
residual-properness to the `s.card` form the one-shots consume. -/

omit [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- The fuel-free reduced one-shot degree side condition follows from leftover properness. -/
private theorem cHermiteReduceTowerG_numer_degree_lt [CPolySquarefree DensePoly α] (Dt : DensePoly α)
    (a d : DensePoly α) (s : Finset (CFieldSpec.K α))
    (hden : toPoly (cHermiteReduceTower Dt a d).2.2 = Lagrange.nodal s id)
    (hproper : (toPoly (cHermiteReduceTower Dt a d).2.1).degree
      < (toPoly (cHermiteReduceTower Dt a d).2.2).degree) :
    (toPoly (cHermiteReduceTower Dt a d).2.1).degree < s.card := by
  rwa [hden, Lagrange.degree_nodal] at hproper

omit [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- The fuel-free reduced one-shot degree side condition from residual properness. -/
private theorem cHermiteReduceTowerG_numer_degree_lt_of_residual [CPolySquarefree DensePoly α]
    (Dt : DensePoly α) (a d : DensePoly α) (s : Finset (CFieldSpec.K α))
    (resNum resDen Dstar : DensePoly α)
    (hnumeq : toPoly (cHermiteReduceTower Dt a d).2.1
      = toPoly (CPolyEuclidean.div (cmul resNum Dstar) resDen))
    (hdeneq : toPoly (cHermiteReduceTower Dt a d).2.2 = toPoly Dstar)
    (hden : toPoly (cHermiteReduceTower Dt a d).2.2 = Lagrange.nodal s id)
    (hdvd : toPoly resDen ∣ toPoly (cmul resNum Dstar))
    (hresDen : cnorm resDen ≠ [])
    (hresProper : (toPoly resNum).degree < (toPoly resDen).degree) :
    (toPoly (cHermiteReduceTower Dt a d).2.1).degree < s.card := by
  have hDstar : toPoly Dstar ≠ 0 := by
    rw [← hdeneq, hden]; exact Lagrange.nodal_ne_zero
  exact cHermiteReduceTowerG_numer_degree_lt Dt a d s hden
    (cHermiteReduceTowerG_leftover_proper_of_residual Dt a d resNum resDen Dstar
      hnumeq hdeneq hdvd hresDen hDstar hresProper)

/-- **★★ The fuel-free reduced-case field identity for the PRIMITIVE case** — for the normal-part capstone
output `res = cIntegrateReduced Dt a d cands` with a primitive monomial `toPoly Dt = C w`, the Hermite
telescoping and per-root residue-log reassembly hypotheses prove the field-level antiderivative identity
with no runtime fuel. -/
theorem field_identity_of_cIntegrateReducedG_primitive [CPolySquarefree DensePoly α] [CPolyGcd DensePoly α]
    [CPolyResultant DensePoly] (Dt : DensePoly α)
    (a d : DensePoly α) (cands : List α) (s : Finset (CFieldSpec.K α)) (w : CFieldSpec.K α)
    (hDt : toPoly Dt = C w)
    (hherm : towerFractionFieldDeriv Dt
            (am α (toPoly (DensePoly.cIntegrateReduced Dt a d cands).rational.1)
              / am α (toPoly (DensePoly.cIntegrateReduced Dt a d cands).rational.2))
          + am α (toPoly (cHermiteReduceTower Dt a d).2.1)
            / am α (toPoly (cHermiteReduceTower Dt a d).2.2)
        = am α (toPoly a) / am α (toPoly d))
    (hden : toPoly (cHermiteReduceTower Dt a d).2.2 = Lagrange.nodal s id)
    (hA : (toPoly (cHermiteReduceTower Dt a d).2.1).degree < s.card)
    (hnorm : ∀ β ∈ s, w ≠ β′)
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
      = am α (toPoly a) / am α (toPoly d) :=
  field_identity_of_reducedG_of_residueMatch Dt
    (DensePoly.cIntegrateReduced Dt a d cands).rational.1
    (DensePoly.cIntegrateReduced Dt a d cands).rational.2
    (cHermiteReduceTower Dt a d).2.1 (cHermiteReduceTower Dt a d).2.2
    a d (DensePoly.cIntegrateReduced Dt a d cands).logs hherm
    (primitive_engine_hmatch Dt s (cHermiteReduceTower Dt a d).2.1
      (cHermiteReduceTower Dt a d).2.2 w
      (DensePoly.cIntegrateReduced Dt a d cands).logs hDt hden hA hnorm hform)

example [CPolySquarefree DensePoly α] [CPolyGcd DensePoly α] [CPolyResultant DensePoly]
    (Dt : DensePoly α) (a d : DensePoly α) (cands : List α)
    (s : Finset (CFieldSpec.K α)) (w : CFieldSpec.K α)
    (hDt : toPoly Dt = C w)
    (hherm : towerFractionFieldDeriv Dt
            (am α (toPoly (DensePoly.cIntegrateReduced Dt a d cands).rational.1)
              / am α (toPoly (DensePoly.cIntegrateReduced Dt a d cands).rational.2))
          + am α (toPoly (cHermiteReduceTower Dt a d).2.1)
            / am α (toPoly (cHermiteReduceTower Dt a d).2.2)
        = am α (toPoly a) / am α (toPoly d))
    (hden : toPoly (cHermiteReduceTower Dt a d).2.2 = Lagrange.nodal s id)
    (hA : (toPoly (cHermiteReduceTower Dt a d).2.1).degree < s.card)
    (hnorm : ∀ β ∈ s, w ≠ β′)
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
      = am α (toPoly a) / am α (toPoly d) :=
  field_identity_of_cIntegrateReducedG_primitive Dt a d cands s w hDt hherm hden hA hnorm hform

/-- **The fuel-free primitive reduced identity with `hform` discharged from residue data.** -/
theorem field_identity_of_cIntegrateReducedG_primitive_of_residueData
    [CPolySquarefree DensePoly α] [CPolyGcd DensePoly α] [CPolyResultant DensePoly]
    [DecidableEq (CFieldSpec.K α)] (Dt : DensePoly α)
    (a d : DensePoly α) (cands : List α) (s : Finset (CFieldSpec.K α)) (w : CFieldSpec.K α)
    (residueCand : CFieldSpec.K α → α)
    (hDt : toPoly Dt = C w)
    (hherm : towerFractionFieldDeriv Dt
            (am α (toPoly (DensePoly.cIntegrateReduced Dt a d cands).rational.1)
              / am α (toPoly (DensePoly.cIntegrateReduced Dt a d cands).rational.2))
          + am α (toPoly (cHermiteReduceTower Dt a d).2.1)
            / am α (toPoly (cHermiteReduceTower Dt a d).2.2)
        = am α (toPoly a) / am α (toPoly d))
    (hden : toPoly (cHermiteReduceTower Dt a d).2.2 = Lagrange.nodal s id)
    (hA : (toPoly (cHermiteReduceTower Dt a d).2.1).degree < s.card)
    (hnorm : ∀ β ∈ s, w ≠ β′)
    (hres : DensePoly.cRationalResidues Dt (cHermiteReduceTower Dt a d).2.1
        (cHermiteReduceTower Dt a d).2.2 cands
      = s.toList.map residueCand)
    (hDd : ∀ β ∈ s,
      (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β ≠ 0)
    (hdist : ∀ γ ∈ s, ∀ δ ∈ s, γ ≠ δ →
      (toPoly (cHermiteReduceTower Dt a d).2.1).eval γ
          / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval γ
        ≠ (toPoly (cHermiteReduceTower Dt a d).2.1).eval δ
          / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval δ)
    (hcand : ∀ β ∈ s, CFieldSpec.toK (residueCand β)
      = (toPoly (cHermiteReduceTower Dt a d).2.1).eval β
        / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β)
    (hgcdread : ∀ β ∈ s, Associated
      (toPoly (cLogArgTower Dt (cHermiteReduceTower Dt a d).2.1
          (cHermiteReduceTower Dt a d).2.2 (residueCand β)))
      (gcd (toPoly (cHermiteReduceTower Dt a d).2.2)
          (toPoly (cAmcDd Dt (cHermiteReduceTower Dt a d).2.1
            (cHermiteReduceTower Dt a d).2.2 (residueCand β))))) :
    towerFractionFieldDeriv Dt
        (am α (toPoly (DensePoly.cIntegrateReduced Dt a d cands).rational.1)
          / am α (toPoly (DensePoly.cIntegrateReduced Dt a d cands).rational.2))
        + logResidueSum Dt (DensePoly.cIntegrateReduced Dt a d cands).logs
      = am α (toPoly a) / am α (toPoly d) :=
  field_identity_of_cIntegrateReducedG_primitive Dt a d cands s w hDt hherm hden hA hnorm
    (cIntegrateReducedG_logs_eq_per_root Dt a d cands s residueCand hden hres hDd hdist hcand
      hgcdread)

/-! ### Task 3 (hyperexp): the fuel-free reduced-case field identity, GATED on `∑c = 0`

The hyperexponential analog of `field_identity_of_cIntegrateReducedG_primitive`: identical assembly, with
the RT residue match supplied by `hyperexp_engine_hmatch` (which needs `hb : b ≠ 0` and the integrability
witness `hsum : ∑c = 0`) instead of `primitive_engine_hmatch` (which discharges the cancellation
automatically). -/

/-- **★★ The fuel-free reduced-case field identity for the HYPEREXPONENTIAL case (given `∑c = 0`)** —
for `res = cIntegrateReduced Dt a d cands`, a hyperexponential monomial `toPoly Dt = C b·X`, the Hermite
half, the per-root reassembly, and the integrability witness `hsum : ∑c = 0` prove the reduced-case field
identity with no runtime fuel. -/
theorem field_identity_of_cIntegrateReducedG_hyperexp [CPolySquarefree DensePoly α] [CPolyGcd DensePoly α]
    [CPolyResultant DensePoly] (Dt : DensePoly α)
    (a d : DensePoly α) (cands : List α) (s : Finset (CFieldSpec.K α)) (b : CFieldSpec.K α) (hb : b ≠ 0)
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
    (hsum : ∑ β ∈ s, (toPoly (cHermiteReduceTower Dt a d).2.1).eval β
          / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β = 0)
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
      = am α (toPoly a) / am α (toPoly d) :=
  field_identity_of_reducedG_of_residueMatch Dt
    (DensePoly.cIntegrateReduced Dt a d cands).rational.1
    (DensePoly.cIntegrateReduced Dt a d cands).rational.2
    (cHermiteReduceTower Dt a d).2.1 (cHermiteReduceTower Dt a d).2.2
    a d (DensePoly.cIntegrateReduced Dt a d cands).logs hherm
    (hyperexp_engine_hmatch Dt s (cHermiteReduceTower Dt a d).2.1
      (cHermiteReduceTower Dt a d).2.2 b hb
      (DensePoly.cIntegrateReduced Dt a d cands).logs hDt hden hA hnorm hsum hform)

example [CPolySquarefree DensePoly α] [CPolyGcd DensePoly α] [CPolyResultant DensePoly]
    (Dt : DensePoly α) (a d : DensePoly α) (cands : List α)
    (s : Finset (CFieldSpec.K α)) (b : CFieldSpec.K α) (hb : b ≠ 0)
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
    (hsum : ∑ β ∈ s, (toPoly (cHermiteReduceTower Dt a d).2.1).eval β
          / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β = 0)
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
      = am α (toPoly a) / am α (toPoly d) :=
  field_identity_of_cIntegrateReducedG_hyperexp Dt a d cands s b hb hDt hherm hden hA hnorm
    hsum hform

/-! ### Task 3: compose with the poly branch — the PRIMITIVE one-shot for `cIntegrateGFullWf`

`cIntegrateGFullWf` splits `f = fₚ + b/dₛ + cₙ/dₙ` (`canonicalRepresentationFast`), requires `b = 0`,
and — when the polynomial part `fₚ` vanishes — returns `some nrm` with
`nrm = cIntegrateReduced Dt cₙ dₙ cands`. For this branch the result is exactly the fuel-free reduced-case
capstone on `(cₙ, dₙ)`, so the task-2 identity `field_identity_of_cIntegrateReducedG_primitive` gives
`D(res) + logResidueSum = am cₙ/am dₙ`; the fuel-free canonical reconstruction (`fₚ = b = 0` ⟹
`cₙ/dₙ = a/d`) closes it to `= am a/am d`. -/

variable [CRischField α]

omit [CFieldSpec α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **`cIntegrateGFullWf` pure-normal branch returns the fuel-free reduced capstone** — when the special
part `b` and polynomial part `fₚ` of the fuel-free canonical split both vanish, the fuel-free full driver
returns exactly `cIntegrateReduced` on the simple part `(cₙ, dₙ)`. -/
theorem cIntegrateGFullWf_pureNormal_eq [CPolyGcd DensePoly α]
    [CPolySplitFactor DensePoly α] [CPolySquarefree DensePoly α]
    [CPolyResultant DensePoly] (Dt : DensePoly α)
    (a d : DensePoly α) (cands : List α)
    (hbranch : IsPureNormalBranch Dt a d) :
    DensePoly.cIntegrateGFullWf Dt a d cands
      = some (DensePoly.cIntegrateReduced Dt (canonicalRepresentationFast Dt a d).2.2.1
          (canonicalRepresentationFast Dt a d).2.2.2 cands) := by
  rw [DensePoly.cIntegrateGFullWf]
  rcases hcrep : canonicalRepresentationFast Dt a d with ⟨fp, ⟨b, ds⟩, ⟨cn, dn⟩⟩
  have hspecial := hbranch.special_zero
  have hpoly := hbranch.poly_zero
  rw [hcrep] at hspecial hpoly
  simp only [hspecial, hpoly, if_true]

example [CPolyGcd DensePoly α] [CPolySplitFactor DensePoly α]
    [CPolySquarefree DensePoly α] [CPolyResultant DensePoly]
    (Dt : DensePoly α) (a d : DensePoly α) (cands : List α)
    (hb : DensePoly.cisZero (canonicalRepresentationFast Dt a d).2.1.1 = true)
    (hfp : DensePoly.cisZero (canonicalRepresentationFast Dt a d).1 = true) :
    DensePoly.cIntegrateGFullWf Dt a d cands
      = some (DensePoly.cIntegrateReduced Dt (canonicalRepresentationFast Dt a d).2.2.1
          (canonicalRepresentationFast Dt a d).2.2.2 cands) :=
  cIntegrateGFullWf_pureNormal_eq Dt a d cands ⟨hb, hfp⟩

/-- **★★★ The fuel-free PRIMITIVE one-shot for `cIntegrateGFullWf` (pure-normal branch), checker-free** —
for a primitive monomial, if the fuel-free full driver returns `some res` on the pure-normal branch, then the
reduced fuel-free primitive identity and the fuel-free canonical reconstruction prove
`D(res) + logResidueSum Dt res.logs = a/d` with no engine `checkIdentity` certificate and no runtime fuel. -/
theorem cIntegrateGFullWf_primitive_oneShot [CPolyGcd DensePoly α] [CPolySplitFactor DensePoly α]
    [CPolySquarefree DensePoly α] [CPolyResultant DensePoly] (Dt : DensePoly α) (a d : DensePoly α)
    (cands : List α) (res : IntegralResult α) (s : Finset (CFieldSpec.K α)) (w : CFieldSpec.K α)
    (hDt : toPoly Dt = C w)
    (hbranch : IsPureNormalBranch Dt a d)
    (hsome : DensePoly.cIntegrateGFullWf Dt a d cands = some res)
    (hrecon : am α (toPoly (canonicalRepresentationFast Dt a d).2.2.1)
          / am α (toPoly (canonicalRepresentationFast Dt a d).2.2.2)
        = am α (toPoly a) / am α (toPoly d))
    (hherm : towerFractionFieldDeriv Dt
            (am α (toPoly (DensePoly.cIntegrateReduced Dt
                  (canonicalRepresentationFast Dt a d).2.2.1
                  (canonicalRepresentationFast Dt a d).2.2.2 cands).rational.1)
              / am α (toPoly (DensePoly.cIntegrateReduced Dt
                  (canonicalRepresentationFast Dt a d).2.2.1
                  (canonicalRepresentationFast Dt a d).2.2.2 cands).rational.2))
          + am α (toPoly (cHermiteReduceTower Dt
                (canonicalRepresentationFast Dt a d).2.2.1
                (canonicalRepresentationFast Dt a d).2.2.2).2.1)
            / am α (toPoly (cHermiteReduceTower Dt
                (canonicalRepresentationFast Dt a d).2.2.1
                (canonicalRepresentationFast Dt a d).2.2.2).2.2)
        = am α (toPoly (canonicalRepresentationFast Dt a d).2.2.1)
            / am α (toPoly (canonicalRepresentationFast Dt a d).2.2.2))
    (hden : toPoly (cHermiteReduceTower Dt
          (canonicalRepresentationFast Dt a d).2.2.1
          (canonicalRepresentationFast Dt a d).2.2.2).2.2 = Lagrange.nodal s id)
    (hA : (toPoly (cHermiteReduceTower Dt
          (canonicalRepresentationFast Dt a d).2.2.1
          (canonicalRepresentationFast Dt a d).2.2.2).2.1).degree < s.card)
    (hnorm : ∀ β ∈ s, w ≠ β′)
    (hform : (DensePoly.cIntegrateReduced Dt
            (canonicalRepresentationFast Dt a d).2.2.1
            (canonicalRepresentationFast Dt a d).2.2.2 cands).logs.map
          (fun cv => (CFieldSpec.toK cv.1, toPoly cv.2))
        = s.toList.map (fun β =>
            ((toPoly (cHermiteReduceTower Dt
                  (canonicalRepresentationFast Dt a d).2.2.1
                  (canonicalRepresentationFast Dt a d).2.2.2).2.1).eval β
                / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β,
              X - C β))) :
    towerFractionFieldDeriv Dt (am α (toPoly res.rational.1) / am α (toPoly res.rational.2))
        + logResidueSum Dt res.logs
      = am α (toPoly a) / am α (toPoly d) := by
  have hres : res = DensePoly.cIntegrateReduced Dt (canonicalRepresentationFast Dt a d).2.2.1
      (canonicalRepresentationFast Dt a d).2.2.2 cands := by
    rw [cIntegrateGFullWf_pureNormal_eq Dt a d cands hbranch] at hsome
    exact (Option.some.injEq _ _ ▸ hsome).symm
  subst hres
  rw [field_identity_of_cIntegrateReducedG_primitive Dt
    (canonicalRepresentationFast Dt a d).2.2.1
    (canonicalRepresentationFast Dt a d).2.2.2 cands s w hDt hherm hden hA hnorm hform]
  exact hrecon

example [CPolyGcd DensePoly α] [CPolySplitFactor DensePoly α] [CPolySquarefree DensePoly α]
    [CPolyResultant DensePoly] (Dt : DensePoly α) (a d : DensePoly α) (cands : List α)
    (res : IntegralResult α) (s : Finset (CFieldSpec.K α)) (w : CFieldSpec.K α)
    (hDt : toPoly Dt = C w)
    (hb : DensePoly.cisZero (canonicalRepresentationFast Dt a d).2.1.1 = true)
    (hfp : DensePoly.cisZero (canonicalRepresentationFast Dt a d).1 = true)
    (hsome : DensePoly.cIntegrateGFullWf Dt a d cands = some res)
    (hrecon : am α (toPoly (canonicalRepresentationFast Dt a d).2.2.1)
          / am α (toPoly (canonicalRepresentationFast Dt a d).2.2.2)
        = am α (toPoly a) / am α (toPoly d))
    (hherm : towerFractionFieldDeriv Dt
            (am α (toPoly (DensePoly.cIntegrateReduced Dt
                  (canonicalRepresentationFast Dt a d).2.2.1
                  (canonicalRepresentationFast Dt a d).2.2.2 cands).rational.1)
              / am α (toPoly (DensePoly.cIntegrateReduced Dt
                  (canonicalRepresentationFast Dt a d).2.2.1
                  (canonicalRepresentationFast Dt a d).2.2.2 cands).rational.2))
          + am α (toPoly (cHermiteReduceTower Dt
                (canonicalRepresentationFast Dt a d).2.2.1
                (canonicalRepresentationFast Dt a d).2.2.2).2.1)
            / am α (toPoly (cHermiteReduceTower Dt
                (canonicalRepresentationFast Dt a d).2.2.1
                (canonicalRepresentationFast Dt a d).2.2.2).2.2)
        = am α (toPoly (canonicalRepresentationFast Dt a d).2.2.1)
            / am α (toPoly (canonicalRepresentationFast Dt a d).2.2.2))
    (hden : toPoly (cHermiteReduceTower Dt
          (canonicalRepresentationFast Dt a d).2.2.1
          (canonicalRepresentationFast Dt a d).2.2.2).2.2 = Lagrange.nodal s id)
    (hA : (toPoly (cHermiteReduceTower Dt
          (canonicalRepresentationFast Dt a d).2.2.1
          (canonicalRepresentationFast Dt a d).2.2.2).2.1).degree < s.card)
    (hnorm : ∀ β ∈ s, w ≠ β′)
    (hform : (DensePoly.cIntegrateReduced Dt
            (canonicalRepresentationFast Dt a d).2.2.1
            (canonicalRepresentationFast Dt a d).2.2.2 cands).logs.map
          (fun cv => (CFieldSpec.toK cv.1, toPoly cv.2))
        = s.toList.map (fun β =>
            ((toPoly (cHermiteReduceTower Dt
                  (canonicalRepresentationFast Dt a d).2.2.1
                  (canonicalRepresentationFast Dt a d).2.2.2).2.1).eval β
                / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β,
              X - C β))) :
    towerFractionFieldDeriv Dt (am α (toPoly res.rational.1) / am α (toPoly res.rational.2))
        + logResidueSum Dt res.logs
      = am α (toPoly a) / am α (toPoly d) :=
  cIntegrateGFullWf_primitive_oneShot Dt a d cands res s w hDt ⟨hb, hfp⟩ hsome hrecon
    hherm hden hA hnorm hform

/-! ### ★ The fuel-free POLYNOMIAL branch of `cIntegrateGFullWf`: output pin + one-shot

`cIntegrateGFullWf` splits `f = fₚ + b/dₛ + cₙ/dₙ`, requires `b = 0`, and — when the polynomial part `fₚ` is
**nonzero** — solves `Dqₚ = fₚ` by the fuel-free poly-Risch-DE oracle `cPolyRischDE`, then recombines the
polynomial solution `qₚ` with the normal-part rational `gₙ/gₙd` into `(qₚ·gₙd + gₙ)/gₙd`. This is the Wf poly
branch, the companion to the pure-normal branch (`cisZero fp = true`) the milestones above cover. We pin its
output shape (`cIntegrateGFullWf_poly_eq`) and assemble the a-priori soundness one-shot
(`cIntegrateGFullWf_poly_oneShot`), gated on the poly-Risch-DE frontier `D(qₚ) = fₚ` (`hpoly`), the normal-part
one-shot (`hnormal`), and the canonical split (`hrecon`). -/

omit [CFieldSpec α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **`cIntegrateGFullWf` polynomial branch returns the recombined result** — using
`canonicalRepresentationFast`, `cIntegrateReduced`, and `cPolyRischDE`. -/
theorem cIntegrateGFullWf_poly_eq [CPolyGcd DensePoly α]
    [CPolySplitFactor DensePoly α] [CPolySquarefree DensePoly α]
    [CPolyResultant DensePoly] (Dt : DensePoly α) (a d : DensePoly α)
    (cands : List α) (qp : DensePoly α)
    (hbranch : IsPolynomialBranch Dt a d)
    (hqp : DensePoly.cPolyRischDE Dt [] (canonicalRepresentationFast Dt a d).1
        ((DensePoly.cdeg (canonicalRepresentationFast Dt a d).1 : ℤ) + 1) = some qp) :
    DensePoly.cIntegrateGFullWf Dt a d cands
      = some ⟨(DensePoly.cadd (DensePoly.cmul qp
              (DensePoly.cIntegrateReduced Dt (canonicalRepresentationFast Dt a d).2.2.1
                (canonicalRepresentationFast Dt a d).2.2.2 cands).rational.2)
            (DensePoly.cIntegrateReduced Dt (canonicalRepresentationFast Dt a d).2.2.1
                (canonicalRepresentationFast Dt a d).2.2.2 cands).rational.1,
          (DensePoly.cIntegrateReduced Dt (canonicalRepresentationFast Dt a d).2.2.1
              (canonicalRepresentationFast Dt a d).2.2.2 cands).rational.2),
        (DensePoly.cIntegrateReduced Dt (canonicalRepresentationFast Dt a d).2.2.1
            (canonicalRepresentationFast Dt a d).2.2.2 cands).logs⟩ := by
  rw [DensePoly.cIntegrateGFullWf]
  rcases hcrep : canonicalRepresentationFast Dt a d with ⟨fp, ⟨b, ds⟩, ⟨cn, dn⟩⟩
  have hspecial := hbranch.special_zero
  have hpoly := hbranch.poly_nonzero
  rw [hcrep] at hspecial hpoly hqp
  simp only [hspecial, hpoly, hqp, if_true, if_neg (by decide : ¬ (false = true))]

example [CPolyGcd DensePoly α] [CPolySplitFactor DensePoly α]
    [CPolySquarefree DensePoly α] [CPolyResultant DensePoly]
    (Dt : DensePoly α) (a d : DensePoly α) (cands : List α) (qp : DensePoly α)
    (hb : DensePoly.cisZero (canonicalRepresentationFast Dt a d).2.1.1 = true)
    (hfp : DensePoly.cisZero (canonicalRepresentationFast Dt a d).1 = false)
    (hqp : DensePoly.cPolyRischDE Dt [] (canonicalRepresentationFast Dt a d).1
        ((DensePoly.cdeg (canonicalRepresentationFast Dt a d).1 : ℤ) + 1) = some qp) :
    DensePoly.cIntegrateGFullWf Dt a d cands
      = some ⟨(DensePoly.cadd (DensePoly.cmul qp
              (DensePoly.cIntegrateReduced Dt (canonicalRepresentationFast Dt a d).2.2.1
                (canonicalRepresentationFast Dt a d).2.2.2 cands).rational.2)
            (DensePoly.cIntegrateReduced Dt (canonicalRepresentationFast Dt a d).2.2.1
                (canonicalRepresentationFast Dt a d).2.2.2 cands).rational.1,
          (DensePoly.cIntegrateReduced Dt (canonicalRepresentationFast Dt a d).2.2.1
              (canonicalRepresentationFast Dt a d).2.2.2 cands).rational.2),
        (DensePoly.cIntegrateReduced Dt (canonicalRepresentationFast Dt a d).2.2.1
            (canonicalRepresentationFast Dt a d).2.2.2 cands).logs⟩ :=
  cIntegrateGFullWf_poly_eq Dt a d cands qp ⟨hb, hfp⟩ hqp

/-- **★★★ The fuel-free POLYNOMIAL one-shot for `cIntegrateGFullWf`, a-priori soundness** — the `…Wf`
one-shot using the fuel-free poly-RDE oracle, reduced capstone, and canonical split. -/
theorem cIntegrateGFullWf_poly_oneShot [CPolyGcd DensePoly α] [CPolySplitFactor DensePoly α]
    [CPolySquarefree DensePoly α] [CPolyResultant DensePoly] (Dt : DensePoly α) (a d : DensePoly α)
    (cands : List α) (res : IntegralResult α) (qp : DensePoly α)
    (hbranch : IsPolynomialBranch Dt a d)
    (hsome : DensePoly.cIntegrateGFullWf Dt a d cands = some res)
    (hqp : DensePoly.cPolyRischDE Dt [] (canonicalRepresentationFast Dt a d).1
        ((DensePoly.cdeg (canonicalRepresentationFast Dt a d).1 : ℤ) + 1) = some qp)
    (hgden : am α (toPoly (DensePoly.cIntegrateReduced Dt
          (canonicalRepresentationFast Dt a d).2.2.1
          (canonicalRepresentationFast Dt a d).2.2.2 cands).rational.2) ≠ 0)
    (hpoly : towerFractionFieldDeriv Dt (am α (toPoly qp)) = am α (toPoly
        (canonicalRepresentationFast Dt a d).1))
    (hnormal : towerFractionFieldDeriv Dt
            (am α (toPoly (DensePoly.cIntegrateReduced Dt
                  (canonicalRepresentationFast Dt a d).2.2.1
                  (canonicalRepresentationFast Dt a d).2.2.2 cands).rational.1)
              / am α (toPoly (DensePoly.cIntegrateReduced Dt
                  (canonicalRepresentationFast Dt a d).2.2.1
                  (canonicalRepresentationFast Dt a d).2.2.2 cands).rational.2))
          + logResidueSum Dt (DensePoly.cIntegrateReduced Dt
              (canonicalRepresentationFast Dt a d).2.2.1
              (canonicalRepresentationFast Dt a d).2.2.2 cands).logs
        = am α (toPoly (canonicalRepresentationFast Dt a d).2.2.1)
            / am α (toPoly (canonicalRepresentationFast Dt a d).2.2.2))
    (hrecon : am α (toPoly (canonicalRepresentationFast Dt a d).1)
          + am α (toPoly (canonicalRepresentationFast Dt a d).2.2.1)
            / am α (toPoly (canonicalRepresentationFast Dt a d).2.2.2)
        = am α (toPoly a) / am α (toPoly d)) :
    towerFractionFieldDeriv Dt (am α (toPoly res.rational.1) / am α (toPoly res.rational.2))
        + logResidueSum Dt res.logs
      = am α (toPoly a) / am α (toPoly d) := by
  have hres : res = ⟨(DensePoly.cadd (DensePoly.cmul qp
            (DensePoly.cIntegrateReduced Dt (canonicalRepresentationFast Dt a d).2.2.1
              (canonicalRepresentationFast Dt a d).2.2.2 cands).rational.2)
          (DensePoly.cIntegrateReduced Dt (canonicalRepresentationFast Dt a d).2.2.1
              (canonicalRepresentationFast Dt a d).2.2.2 cands).rational.1,
        (DensePoly.cIntegrateReduced Dt (canonicalRepresentationFast Dt a d).2.2.1
            (canonicalRepresentationFast Dt a d).2.2.2 cands).rational.2),
      (DensePoly.cIntegrateReduced Dt (canonicalRepresentationFast Dt a d).2.2.1
          (canonicalRepresentationFast Dt a d).2.2.2 cands).logs⟩ := by
    rw [cIntegrateGFullWf_poly_eq Dt a d cands qp hbranch hqp] at hsome
    exact (Option.some.injEq _ _ ▸ hsome).symm
  subst hres
  set gnum := (DensePoly.cIntegrateReduced Dt (canonicalRepresentationFast Dt a d).2.2.1
      (canonicalRepresentationFast Dt a d).2.2.2 cands).rational.1 with hgnumE
  set gden := (DensePoly.cIntegrateReduced Dt (canonicalRepresentationFast Dt a d).2.2.1
      (canonicalRepresentationFast Dt a d).2.2.2 cands).rational.2 with hgdenE
  have hnewrat : am α (toPoly (DensePoly.cadd (DensePoly.cmul qp gden) gnum)) / am α (toPoly gden)
      = am α (toPoly qp) + am α (toPoly gnum) / am α (toPoly gden) := by
    simp [map_add, map_mul, add_div, mul_div_assoc, div_self hgden]
  rw [hnewrat, map_add, hpoly]
  rw [add_assoc, hnormal, hrecon]

example [CPolyGcd DensePoly α] [CPolySplitFactor DensePoly α] [CPolySquarefree DensePoly α]
    [CPolyResultant DensePoly] (Dt : DensePoly α) (a d : DensePoly α) (cands : List α)
    (res : IntegralResult α) (qp : DensePoly α)
    (hb : DensePoly.cisZero (canonicalRepresentationFast Dt a d).2.1.1 = true)
    (hfp : DensePoly.cisZero (canonicalRepresentationFast Dt a d).1 = false)
    (hsome : DensePoly.cIntegrateGFullWf Dt a d cands = some res)
    (hqp : DensePoly.cPolyRischDE Dt [] (canonicalRepresentationFast Dt a d).1
        ((DensePoly.cdeg (canonicalRepresentationFast Dt a d).1 : ℤ) + 1) = some qp)
    (hgden : am α (toPoly (DensePoly.cIntegrateReduced Dt
          (canonicalRepresentationFast Dt a d).2.2.1
          (canonicalRepresentationFast Dt a d).2.2.2 cands).rational.2) ≠ 0)
    (hpoly : towerFractionFieldDeriv Dt (am α (toPoly qp)) = am α (toPoly
        (canonicalRepresentationFast Dt a d).1))
    (hnormal : towerFractionFieldDeriv Dt
            (am α (toPoly (DensePoly.cIntegrateReduced Dt
                  (canonicalRepresentationFast Dt a d).2.2.1
                  (canonicalRepresentationFast Dt a d).2.2.2 cands).rational.1)
              / am α (toPoly (DensePoly.cIntegrateReduced Dt
                  (canonicalRepresentationFast Dt a d).2.2.1
                  (canonicalRepresentationFast Dt a d).2.2.2 cands).rational.2))
          + logResidueSum Dt (DensePoly.cIntegrateReduced Dt
              (canonicalRepresentationFast Dt a d).2.2.1
              (canonicalRepresentationFast Dt a d).2.2.2 cands).logs
        = am α (toPoly (canonicalRepresentationFast Dt a d).2.2.1)
            / am α (toPoly (canonicalRepresentationFast Dt a d).2.2.2))
    (hrecon : am α (toPoly (canonicalRepresentationFast Dt a d).1)
          + am α (toPoly (canonicalRepresentationFast Dt a d).2.2.1)
            / am α (toPoly (canonicalRepresentationFast Dt a d).2.2.2)
        = am α (toPoly a) / am α (toPoly d)) :
    towerFractionFieldDeriv Dt (am α (toPoly res.rational.1) / am α (toPoly res.rational.2))
        + logResidueSum Dt res.logs
      = am α (toPoly a) / am α (toPoly d) :=
  cIntegrateGFullWf_poly_oneShot Dt a d cands res qp ⟨hb, hfp⟩ hsome hqp hgden hpoly hnormal
    hrecon

/-! ### ★★★ The fuel-free POLYNOMIAL one-shot with `hpoly` discharged (primitive base)

`cIntegrateGFullWf_poly_oneShot` is gated on `hpoly` (`D(am qₚ) = am fₚ`). For the primitive base
`Dt = [CCommRing.one]`, the `b = []` branch integrates `fₚ` term by term and the Wf dispatcher pins
`qₚ = CPoly.antiderivative fₚ`, so the existing constant-coefficient field identity discharges `hpoly`. -/

/-- **★★★ The fuel-free POLYNOMIAL one-shot for `cIntegrateGFullWf` with `hpoly` discharged
(primitive base).** -/
theorem cIntegrateGFullWf_poly_oneShot_base [CharZero (CFieldSpec.K α)] [CPolyGcd DensePoly α]
    [CPolySplitFactor DensePoly α] [CPolySquarefree DensePoly α] [CPolyResultant DensePoly]
    (a d : DensePoly α) (cands : List α) (res : IntegralResult α) (qp : DensePoly α)
    (hbranch : IsPolynomialBranch ([CCommRing.one] : DensePoly α) a d)
    (hsome : DensePoly.cIntegrateGFullWf ([CCommRing.one] : DensePoly α) a d cands = some res)
    (hqp : DensePoly.cPolyRischDE ([CCommRing.one] : DensePoly α) []
        (canonicalRepresentationFast ([CCommRing.one] : DensePoly α) a d).1
        ((DensePoly.cdeg (canonicalRepresentationFast ([CCommRing.one] : DensePoly α) a d).1 : ℤ) + 1)
        = some qp)
    (hgden : am α (toPoly (DensePoly.cIntegrateReduced ([CCommRing.one] : DensePoly α)
          (canonicalRepresentationFast ([CCommRing.one] : DensePoly α) a d).2.2.1
          (canonicalRepresentationFast ([CCommRing.one] : DensePoly α) a d).2.2.2 cands).rational.2)
        ≠ 0)
    (hconst : Differential.mapCoeffs
        (toPoly (canonicalRepresentationFast ([CCommRing.one] : DensePoly α) a d).1) = 0)
    (hnormal : towerFractionFieldDeriv ([CCommRing.one] : DensePoly α)
            (am α (toPoly (DensePoly.cIntegrateReduced ([CCommRing.one] : DensePoly α)
                  (canonicalRepresentationFast ([CCommRing.one] : DensePoly α) a d).2.2.1
                  (canonicalRepresentationFast ([CCommRing.one] : DensePoly α) a d).2.2.2 cands).rational.1)
              / am α (toPoly (DensePoly.cIntegrateReduced ([CCommRing.one] : DensePoly α)
                  (canonicalRepresentationFast ([CCommRing.one] : DensePoly α) a d).2.2.1
                  (canonicalRepresentationFast ([CCommRing.one] : DensePoly α) a d).2.2.2 cands).rational.2))
          + logResidueSum ([CCommRing.one] : DensePoly α) (DensePoly.cIntegrateReduced
              ([CCommRing.one] : DensePoly α)
              (canonicalRepresentationFast ([CCommRing.one] : DensePoly α) a d).2.2.1
              (canonicalRepresentationFast ([CCommRing.one] : DensePoly α) a d).2.2.2 cands).logs
        = am α (toPoly (canonicalRepresentationFast ([CCommRing.one] : DensePoly α) a d).2.2.1)
            / am α (toPoly (canonicalRepresentationFast ([CCommRing.one] : DensePoly α) a d).2.2.2))
    (hrecon : am α (toPoly (canonicalRepresentationFast ([CCommRing.one] : DensePoly α) a d).1)
          + am α (toPoly (canonicalRepresentationFast ([CCommRing.one] : DensePoly α) a d).2.2.1)
            / am α (toPoly (canonicalRepresentationFast ([CCommRing.one] : DensePoly α) a d).2.2.2)
        = am α (toPoly a) / am α (toPoly d)) :
    towerFractionFieldDeriv ([CCommRing.one] : DensePoly α)
        (am α (toPoly res.rational.1) / am α (toPoly res.rational.2))
        + logResidueSum ([CCommRing.one] : DensePoly α) res.logs
      = am α (toPoly a) / am α (toPoly d) := by
  set fp := (canonicalRepresentationFast ([CCommRing.one] : DensePoly α) a d).1 with hfpE
  have hfp := hbranch.poly_nonzero
  rw [← hfpE] at hfp
  have hqp_eq : qp = CPoly.antiderivative fp := by
    rw [cPolyRischDEG_nil_eq ([CCommRing.one] : DensePoly α) fp ((DensePoly.cdeg fp : ℤ) + 1) hfp
      (le_refl _)] at hqp
    exact (Option.some.injEq _ _ ▸ hqp).symm
  have hpoly : towerFractionFieldDeriv ([CCommRing.one] : DensePoly α) (am α (toPoly qp))
      = am α (toPoly fp) := by
    rw [hqp_eq]
    exact towerFractionFieldDerivG_amG_antiderivative_const fp
      (mapCoeffs_antiderivative_eq_zero fp hconst)
  exact cIntegrateGFullWf_poly_oneShot ([CCommRing.one] : DensePoly α) a d cands res qp hbranch hsome
    hqp hgden hpoly hnormal hrecon

/-! ### ★★★ Task 3 milestone: the HYPEREXPONENTIAL one-shot for `cIntegrateGFullWf`, GATED on `∑c = 0`

The fuel-free hyperexponential pure-normal one-shot follows the same pattern:
`cIntegrateGFullWf = some res` on the pure-normal branch ⟹ `D(res) = a/d`, for a hyperexponential monomial `Dt = η′·t`. The ONLY extra hypothesis
over the primitive milestone is the integrability witness `hsum : ∑c = 0` — discharging the general-case
`hcancel` for hyperexp via `hyperexp_residue_match_iff_sum_zero` inside `hyperexp_engine_hmatch`.

★ WHY `hsum` IS NEEDED (the precise obstruction). `cIntegrateGFullWf`'s pure-normal branch returns `some nrm`
**UNCONDITIONALLY** (`cIntegrateGFullWf_pureNormal_eq` — no `none` exit, no integrability check). It does NOT do
the Bronstein §5.9 residual feedback (that lives in the SEPARATE driver `cIntegrateHyperexpFull`, which
overshoots by `R = η·∑c` and absorbs it into `∫R`). So for `cIntegrateGFullWf` on a hyperexp input, `D(res) =
a/d` holds **iff** `∑c = 0` (`hyperexp_residue_match_iff_sum_zero`), and when `∑c ≠ 0` the driver STILL returns
`some res` but `D(res) ≠ a/d` (`checkIdentity = false`, witnessed by `ComputableHyperexpNormal`'s
`nNormInv_reduced_overshoots`). Hence "engine returns `some` ⟹ `∑c = 0`" is **FALSE** for `cIntegrateGFullWf`,
and the hyperexp one-shot is GENUINELY conditional on the integrability witness `hsum` — not derivable from
engine success. The full unconditional story requires routing through `cIntegrateHyperexpFull` (a different,
larger soundness task), whose success encodes `∫R` solvability, NOT `∑c = 0`. -/

/-- **★★★ The fuel-free HYPEREXPONENTIAL one-shot for `cIntegrateGFullWf` (pure-normal branch), checker-free,
GATED on `∑c = 0`** — it pins the fuel-free driver output to `cIntegrateReduced`, applies
`field_identity_of_cIntegrateReducedG_hyperexp`, and closes
with the fuel-free canonical reconstruction. -/
theorem cIntegrateGFullWf_hyperexp_oneShot [CPolyGcd DensePoly α] [CPolySplitFactor DensePoly α]
    [CPolySquarefree DensePoly α] [CPolyResultant DensePoly] (Dt : DensePoly α) (a d : DensePoly α)
    (cands : List α) (res : IntegralResult α) (s : Finset (CFieldSpec.K α)) (b : CFieldSpec.K α)
    (hb : b ≠ 0) (hDt : toPoly Dt = C b * X)
    (hbranch : IsPureNormalBranch Dt a d)
    (hsome : DensePoly.cIntegrateGFullWf Dt a d cands = some res)
    (hrecon : am α (toPoly (canonicalRepresentationFast Dt a d).2.2.1)
          / am α (toPoly (canonicalRepresentationFast Dt a d).2.2.2)
        = am α (toPoly a) / am α (toPoly d))
    (hherm : towerFractionFieldDeriv Dt
            (am α (toPoly (DensePoly.cIntegrateReduced Dt
                  (canonicalRepresentationFast Dt a d).2.2.1
                  (canonicalRepresentationFast Dt a d).2.2.2 cands).rational.1)
              / am α (toPoly (DensePoly.cIntegrateReduced Dt
                  (canonicalRepresentationFast Dt a d).2.2.1
                  (canonicalRepresentationFast Dt a d).2.2.2 cands).rational.2))
          + am α (toPoly (cHermiteReduceTower Dt
                (canonicalRepresentationFast Dt a d).2.2.1
                (canonicalRepresentationFast Dt a d).2.2.2).2.1)
            / am α (toPoly (cHermiteReduceTower Dt
                (canonicalRepresentationFast Dt a d).2.2.1
                (canonicalRepresentationFast Dt a d).2.2.2).2.2)
        = am α (toPoly (canonicalRepresentationFast Dt a d).2.2.1)
            / am α (toPoly (canonicalRepresentationFast Dt a d).2.2.2))
    (hden : toPoly (cHermiteReduceTower Dt
          (canonicalRepresentationFast Dt a d).2.2.1
          (canonicalRepresentationFast Dt a d).2.2.2).2.2 = Lagrange.nodal s id)
    (hA : (toPoly (cHermiteReduceTower Dt
          (canonicalRepresentationFast Dt a d).2.2.1
          (canonicalRepresentationFast Dt a d).2.2.2).2.1).degree < s.card)
    (hnorm : ∀ β ∈ s, (C b * X).eval β ≠ β′)
    (hsum : ∑ β ∈ s, (toPoly (cHermiteReduceTower Dt
            (canonicalRepresentationFast Dt a d).2.2.1
            (canonicalRepresentationFast Dt a d).2.2.2).2.1).eval β
          / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β = 0)
    (hform : (DensePoly.cIntegrateReduced Dt
            (canonicalRepresentationFast Dt a d).2.2.1
            (canonicalRepresentationFast Dt a d).2.2.2 cands).logs.map
          (fun cv => (CFieldSpec.toK cv.1, toPoly cv.2))
        = s.toList.map (fun β =>
            ((toPoly (cHermiteReduceTower Dt
                  (canonicalRepresentationFast Dt a d).2.2.1
                  (canonicalRepresentationFast Dt a d).2.2.2).2.1).eval β
                / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β,
              X - C β))) :
    towerFractionFieldDeriv Dt (am α (toPoly res.rational.1) / am α (toPoly res.rational.2))
        + logResidueSum Dt res.logs
      = am α (toPoly a) / am α (toPoly d) := by
  have hres : res = DensePoly.cIntegrateReduced Dt (canonicalRepresentationFast Dt a d).2.2.1
      (canonicalRepresentationFast Dt a d).2.2.2 cands := by
    rw [cIntegrateGFullWf_pureNormal_eq Dt a d cands hbranch] at hsome
    exact (Option.some.injEq _ _ ▸ hsome).symm
  subst hres
  rw [field_identity_of_cIntegrateReducedG_hyperexp Dt
    (canonicalRepresentationFast Dt a d).2.2.1
    (canonicalRepresentationFast Dt a d).2.2.2 cands s b hb hDt hherm hden hA hnorm hsum hform]
  exact hrecon

example [CPolyGcd DensePoly α] [CPolySplitFactor DensePoly α] [CPolySquarefree DensePoly α]
    [CPolyResultant DensePoly] (Dt : DensePoly α) (a d : DensePoly α) (cands : List α)
    (res : IntegralResult α) (s : Finset (CFieldSpec.K α)) (b : CFieldSpec.K α)
    (hb : b ≠ 0) (hDt : toPoly Dt = C b * X)
    (hbz : DensePoly.cisZero (canonicalRepresentationFast Dt a d).2.1.1 = true)
    (hfp : DensePoly.cisZero (canonicalRepresentationFast Dt a d).1 = true)
    (hsome : DensePoly.cIntegrateGFullWf Dt a d cands = some res)
    (hrecon : am α (toPoly (canonicalRepresentationFast Dt a d).2.2.1)
          / am α (toPoly (canonicalRepresentationFast Dt a d).2.2.2)
        = am α (toPoly a) / am α (toPoly d))
    (hherm : towerFractionFieldDeriv Dt
            (am α (toPoly (DensePoly.cIntegrateReduced Dt
                  (canonicalRepresentationFast Dt a d).2.2.1
                  (canonicalRepresentationFast Dt a d).2.2.2 cands).rational.1)
              / am α (toPoly (DensePoly.cIntegrateReduced Dt
                  (canonicalRepresentationFast Dt a d).2.2.1
                  (canonicalRepresentationFast Dt a d).2.2.2 cands).rational.2))
          + am α (toPoly (cHermiteReduceTower Dt
                (canonicalRepresentationFast Dt a d).2.2.1
                (canonicalRepresentationFast Dt a d).2.2.2).2.1)
            / am α (toPoly (cHermiteReduceTower Dt
                (canonicalRepresentationFast Dt a d).2.2.1
                (canonicalRepresentationFast Dt a d).2.2.2).2.2)
        = am α (toPoly (canonicalRepresentationFast Dt a d).2.2.1)
            / am α (toPoly (canonicalRepresentationFast Dt a d).2.2.2))
    (hden : toPoly (cHermiteReduceTower Dt
          (canonicalRepresentationFast Dt a d).2.2.1
          (canonicalRepresentationFast Dt a d).2.2.2).2.2 = Lagrange.nodal s id)
    (hA : (toPoly (cHermiteReduceTower Dt
          (canonicalRepresentationFast Dt a d).2.2.1
          (canonicalRepresentationFast Dt a d).2.2.2).2.1).degree < s.card)
    (hnorm : ∀ β ∈ s, (C b * X).eval β ≠ β′)
    (hsum : ∑ β ∈ s, (toPoly (cHermiteReduceTower Dt
            (canonicalRepresentationFast Dt a d).2.2.1
            (canonicalRepresentationFast Dt a d).2.2.2).2.1).eval β
          / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β = 0)
    (hform : (DensePoly.cIntegrateReduced Dt
            (canonicalRepresentationFast Dt a d).2.2.1
            (canonicalRepresentationFast Dt a d).2.2.2 cands).logs.map
          (fun cv => (CFieldSpec.toK cv.1, toPoly cv.2))
        = s.toList.map (fun β =>
            ((toPoly (cHermiteReduceTower Dt
                  (canonicalRepresentationFast Dt a d).2.2.1
                  (canonicalRepresentationFast Dt a d).2.2.2).2.1).eval β
                / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β,
              X - C β))) :
    towerFractionFieldDeriv Dt (am α (toPoly res.rational.1) / am α (toPoly res.rational.2))
        + logResidueSum Dt res.logs
      = am α (toPoly a) / am α (toPoly d) :=
  cIntegrateGFullWf_hyperexp_oneShot Dt a d cands res s b hb hDt ⟨hbz, hfp⟩ hsome hrecon
    hherm hden hA hnorm hsum hform

/-! ### ★ The PRIMITIVE one-shot at the level-1 carrier `α = DenseFrac ℚ = ℚ(x)`

Instantiating the primitive one-shot at the generic level-1 carrier `α = DenseFrac ℚ`, where `CFieldSpec.K
(DenseFrac ℚ) = RatFunc ℚ` (genuine `Algebra ℚ`). The concrete checker-free fueled and fuel-free drivers
differentiate back to the integrand for primitive (logarithmic) tower extensions over `ℚ(x)(t)`. The local
instance bridges the carrier abbreviation to `RatFunc ℚ`. -/

/-- The engine carrier `CFieldSpec.K (DenseFrac ℚ)` is `RatFunc ℚ`, a `ℚ`-algebra. Local instance so the
`DenseFrac ℚ` deliverable synthesizes the **same** `Algebra ℚ` the bridge `towerFractionFieldDeriv` uses. -/
noncomputable local instance : Algebra ℚ (CFieldSpec.K (DenseFrac ℚ)) :=
  inferInstanceAs (Algebra ℚ (RatFunc ℚ))

/-- `CharZero (CFieldSpec.K (DenseFrac ℚ)) = CharZero (RatFunc ℚ)`: local instance so the poly-branch capstone
synthesizes the `CharZero` that `cIntegrateGFullWf_poly_oneShot_base`'s `hpoly` discharge needs over the carrier
abbreviation. -/
noncomputable local instance : CharZero (CFieldSpec.K (DenseFrac ℚ)) :=
  inferInstanceAs (CharZero (RatFunc ℚ))

/-- **★★★ The fuel-free PRIMITIVE one-shot for `cIntegrateGFullWf` over `ℚ(x)(t)`** — the `DenseFrac ℚ`
instance of `cIntegrateGFullWf_primitive_oneShot`. -/
theorem cIntegrateGFullWf_primitive_oneShot_qfunNZG (Dt : DensePoly (DenseFrac ℚ))
    (a d : DensePoly (DenseFrac ℚ)) (cands : List (DenseFrac ℚ)) (res : IntegralResult (DenseFrac ℚ))
    (s : Finset (CFieldSpec.K (DenseFrac ℚ))) (w : CFieldSpec.K (DenseFrac ℚ))
    (hDt : toPoly Dt = C w)
    (hbranch : IsPureNormalBranch Dt a d)
    (hsome : DensePoly.cIntegrateGFullWf Dt a d cands = some res)
    (hrecon : am (DenseFrac ℚ) (toPoly (canonicalRepresentationFast Dt a d).2.2.1)
          / am (DenseFrac ℚ) (toPoly (canonicalRepresentationFast Dt a d).2.2.2)
        = am (DenseFrac ℚ) (toPoly a) / am (DenseFrac ℚ) (toPoly d))
    (hherm : towerFractionFieldDeriv Dt
            (am (DenseFrac ℚ) (toPoly (DensePoly.cIntegrateReduced Dt
                  (canonicalRepresentationFast Dt a d).2.2.1
                  (canonicalRepresentationFast Dt a d).2.2.2 cands).rational.1)
              / am (DenseFrac ℚ) (toPoly (DensePoly.cIntegrateReduced Dt
                  (canonicalRepresentationFast Dt a d).2.2.1
                  (canonicalRepresentationFast Dt a d).2.2.2 cands).rational.2))
          + am (DenseFrac ℚ) (toPoly (cHermiteReduceTower Dt
                (canonicalRepresentationFast Dt a d).2.2.1
                (canonicalRepresentationFast Dt a d).2.2.2).2.1)
            / am (DenseFrac ℚ) (toPoly (cHermiteReduceTower Dt
                (canonicalRepresentationFast Dt a d).2.2.1
                (canonicalRepresentationFast Dt a d).2.2.2).2.2)
        = am (DenseFrac ℚ) (toPoly (canonicalRepresentationFast Dt a d).2.2.1)
            / am (DenseFrac ℚ) (toPoly (canonicalRepresentationFast Dt a d).2.2.2))
    (hden : toPoly (cHermiteReduceTower Dt
          (canonicalRepresentationFast Dt a d).2.2.1
          (canonicalRepresentationFast Dt a d).2.2.2).2.2 = Lagrange.nodal s id)
    (hA : (toPoly (cHermiteReduceTower Dt
          (canonicalRepresentationFast Dt a d).2.2.1
          (canonicalRepresentationFast Dt a d).2.2.2).2.1).degree < s.card)
    (hnorm : ∀ β ∈ s, w ≠ β′)
    (hform : (DensePoly.cIntegrateReduced Dt
            (canonicalRepresentationFast Dt a d).2.2.1
            (canonicalRepresentationFast Dt a d).2.2.2 cands).logs.map
          (fun cv => (CFieldSpec.toK cv.1, toPoly cv.2))
        = s.toList.map (fun β =>
            ((toPoly (cHermiteReduceTower Dt
                  (canonicalRepresentationFast Dt a d).2.2.1
                  (canonicalRepresentationFast Dt a d).2.2.2).2.1).eval β
                / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β,
              X - C β))) :
    towerFractionFieldDeriv Dt
        (am (DenseFrac ℚ) (toPoly res.rational.1) / am (DenseFrac ℚ) (toPoly res.rational.2))
        + logResidueSum Dt res.logs
      = am (DenseFrac ℚ) (toPoly a) / am (DenseFrac ℚ) (toPoly d) :=
  cIntegrateGFullWf_primitive_oneShot Dt a d cands res s w hDt hbranch hsome hrecon hherm hden hA
    hnorm hform

/-- **★★★ The fuel-free HYPEREXPONENTIAL one-shot for `cIntegrateGFullWf` over `ℚ(x)(t)`, gated on
`∑c = 0`** — the `DenseFrac ℚ` instance of `cIntegrateGFullWf_hyperexp_oneShot`. -/
theorem cIntegrateGFullWf_hyperexp_oneShot_qfunNZG (Dt : DensePoly (DenseFrac ℚ))
    (a d : DensePoly (DenseFrac ℚ)) (cands : List (DenseFrac ℚ)) (res : IntegralResult (DenseFrac ℚ))
    (s : Finset (CFieldSpec.K (DenseFrac ℚ))) (b : CFieldSpec.K (DenseFrac ℚ))
    (hb : b ≠ 0) (hDt : toPoly Dt = C b * X)
    (hbranch : IsPureNormalBranch Dt a d)
    (hsome : DensePoly.cIntegrateGFullWf Dt a d cands = some res)
    (hrecon : am (DenseFrac ℚ) (toPoly (canonicalRepresentationFast Dt a d).2.2.1)
          / am (DenseFrac ℚ) (toPoly (canonicalRepresentationFast Dt a d).2.2.2)
        = am (DenseFrac ℚ) (toPoly a) / am (DenseFrac ℚ) (toPoly d))
    (hherm : towerFractionFieldDeriv Dt
            (am (DenseFrac ℚ) (toPoly (DensePoly.cIntegrateReduced Dt
                  (canonicalRepresentationFast Dt a d).2.2.1
                  (canonicalRepresentationFast Dt a d).2.2.2 cands).rational.1)
              / am (DenseFrac ℚ) (toPoly (DensePoly.cIntegrateReduced Dt
                  (canonicalRepresentationFast Dt a d).2.2.1
                  (canonicalRepresentationFast Dt a d).2.2.2 cands).rational.2))
          + am (DenseFrac ℚ) (toPoly (cHermiteReduceTower Dt
                (canonicalRepresentationFast Dt a d).2.2.1
                (canonicalRepresentationFast Dt a d).2.2.2).2.1)
            / am (DenseFrac ℚ) (toPoly (cHermiteReduceTower Dt
                (canonicalRepresentationFast Dt a d).2.2.1
                (canonicalRepresentationFast Dt a d).2.2.2).2.2)
        = am (DenseFrac ℚ) (toPoly (canonicalRepresentationFast Dt a d).2.2.1)
            / am (DenseFrac ℚ) (toPoly (canonicalRepresentationFast Dt a d).2.2.2))
    (hden : toPoly (cHermiteReduceTower Dt
          (canonicalRepresentationFast Dt a d).2.2.1
          (canonicalRepresentationFast Dt a d).2.2.2).2.2 = Lagrange.nodal s id)
    (hA : (toPoly (cHermiteReduceTower Dt
          (canonicalRepresentationFast Dt a d).2.2.1
          (canonicalRepresentationFast Dt a d).2.2.2).2.1).degree < s.card)
    (hnorm : ∀ β ∈ s, (C b * X).eval β ≠ β′)
    (hsum : ∑ β ∈ s, (toPoly (cHermiteReduceTower Dt
            (canonicalRepresentationFast Dt a d).2.2.1
            (canonicalRepresentationFast Dt a d).2.2.2).2.1).eval β
          / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β = 0)
    (hform : (DensePoly.cIntegrateReduced Dt
            (canonicalRepresentationFast Dt a d).2.2.1
            (canonicalRepresentationFast Dt a d).2.2.2 cands).logs.map
          (fun cv => (CFieldSpec.toK cv.1, toPoly cv.2))
        = s.toList.map (fun β =>
            ((toPoly (cHermiteReduceTower Dt
                  (canonicalRepresentationFast Dt a d).2.2.1
                  (canonicalRepresentationFast Dt a d).2.2.2).2.1).eval β
                / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β,
              X - C β))) :
    towerFractionFieldDeriv Dt
        (am (DenseFrac ℚ) (toPoly res.rational.1) / am (DenseFrac ℚ) (toPoly res.rational.2))
        + logResidueSum Dt res.logs
      = am (DenseFrac ℚ) (toPoly a) / am (DenseFrac ℚ) (toPoly d) :=
  cIntegrateGFullWf_hyperexp_oneShot Dt a d cands res s b hb hDt hbranch hsome hrecon hherm hden hA
    hnorm hsum hform

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

-- ★★ THE GENERAL-CASE STRETCH (hyperexp reduction, PROVEN): for `v = C b·X` (`Dt = η′·t`, `b ≠ 0`) the
-- `monomial_residue_match_of_cancel` cancellation `hcancel` holds ⟺ `∑ c_α = 0` — the integrability witness,
-- FALSE in general; the precise general-case obstruction, pinned as a theorem.
example {K : Type*} [Field K] [Differential K] (s : Finset K) (b : K) (hb : b ≠ 0) (c : K → K) :
    (∑ α ∈ s, algebraMap K[X] (RatFunc K) (C (c α) * ((C b * X - C (α′)) /ₘ (X - C α))) = 0)
      ↔ ∑ α ∈ s, c α = 0 :=
  ResidueMatchTower.hyperexp_cancel_iff_sum_zero s b hb c

/-! ### ★ Status — the PRIMITIVE and HYPEREXPONENTIAL `cIntegrateGFullWf` one-shots, axiom-clean

PROVEN (axiom-clean `[propext, Classical.choice, Quot.sound]`, **no** `native_decide`, **no** `sorry`):
* **The list↔Finset bridge** (`primitive_residue_match_list` / `…_engine`) — the engine-shaped `List.sum`
  over the per-root list IS the proven Finset residue match, via `Finset.sum_map_toList`.
* **The primitive engine `hmatch`** (`primitive_engine_hmatch`) — discharges the engine's RT residue-match
  hypothesis for the primitive case, given the per-root reassembly `hform`. The RT polynomial-part
  cancellation is AUTOMATIC (`ResidueMatchTower.primitive_cancel`), so the primitive regime needs **no
  integrability witness**.
* **The PRIMITIVE one-shot** (`field_identity_of_cIntegrateReducedG_primitive`,
  `field_identity_of_cIntegrateReducedG_primitive_of_residueData`, `cIntegrateGFullWf_primitive_oneShot` plus the Wf
  `…_qfunNZG` specialization) — for the primitive pure-normal branch,
  `cIntegrateGFullWf = some res ⟹ D(res) = a/d`, checker-free, gated only on
  the abstract engine inputs (canonical reconstruction `hrecon`, Hermite half `hherm`, per-root reassembly
  `hform`).
* **★★ NEW — the fuel-free HYPEREXPONENTIAL one-shot** (`field_identity_of_cIntegrateReducedG_hyperexp`,
  `cIntegrateGFullWf_hyperexp_oneShot` plus the Wf
  `…_qfunNZG` specialization), built on:
  - **`monomial_residue_sum_eq_cancel_add`** — the UNCONDITIONAL decomposition `residue sum = (cancel sum) +
    a/d` for any monomial (the body of `monomial_residue_match_of_cancel` before its `hcancel` rewrite).
  - **`hyperexp_residue_match_iff_sum_zero`** — for `v = C b·X` (`b = η′ ≠ 0`) the residue match `= a/d`
    holds **iff** `∑c_α = 0` (decomposition + `hyperexp_cancel_iff_sum_zero`).
  - **`hyperexp_engine_hmatch`** / **`hyperexp_residue_match_list_engine`** — the engine `hmatch`, hyperexp
    case, discharged given `hform` AND the integrability witness `hsum : ∑c = 0`.

  So `cIntegrateGFullWf = some res ⟹ D(res) = a/d` for a hyperexp `Dt = η′·t` (`toPoly Dt = C b·X`),
  checker-free, gated on the abstract engine inputs PLUS `hsum`. **The checker-free one-shot now covers the
  PRIMITIVE and EXPONENTIAL cases — the two main transcendental monomial kinds — modulo the integrability
  witness for the exponential case.**

★ IS THE HYPEREXP ONE-SHOT UNCONDITIONAL? **NO — and this is a genuine mathematical obstruction, not a missing
lemma.** The task hoped "engine returns `some` on a hyperexp input ⟹ `∑c = 0` (discharging `hcancel`
unconditionally)". That implication is **FALSE for `cIntegrateGFullWf`**, for a precise reason:

  `cIntegrateGFullWf`'s pure-normal branch returns `some nrm = some (cIntegrateReduced …)`
  **UNCONDITIONALLY** (`cIntegrateGFullWf_pureNormal_eq` — no `none` exit, no integrability test). It does
  **not** perform the
  Bronstein §5.9 residual feedback: it emits the raw §5.6 Rothstein–Trager logs, which **overshoot** a
  hyperexp normal part by `R = η·∑c` (the `extendDeriv_logPart_eq_div_add_residual` leftover). Hence for
  `cIntegrateGFullWf` on a hyperexp input, `D(res) = a/d` ⟺ the overshoot vanishes ⟺ `∑c = 0`
  (`hyperexp_residue_match_iff_sum_zero`); when `∑c ≠ 0` the driver STILL returns `some res` but `D(res) ≠
  a/d`. This is not hypothetical — `ComputableHyperexpNormal`'s `nNormInv_reduced_overshoots` is a
  `native_decide` witness: on `f = 1/(exp x − 1)` the plain reduced driver returns a result with
  `checkIdentity = false`. Therefore "success ⟹ `∑c = 0`" cannot hold, and the hyperexp one-shot for
  `cIntegrateGFullWf` is **genuinely conditional on the integrability witness `hsum`** — it is the strongest
  TRUE statement of this form for this driver.

  Where does the §5.9 correction live? In the SEPARATE driver `cIntegrateHyperexpFull`
  (`ComputableHyperexpNormal`/`…Special`), which integrates the overshoot `∫R` and subtracts it
  (`∫fₙ = logPart − ∫R`). Its success condition is `∫R` SOLVABLE — the OPPOSITE of `∑c = 0` (it succeeds
  precisely when `∑c ≠ 0` is *absorbable*). So no engine-success fact, on EITHER driver, supplies `∑c = 0`:
  the integrability-in-the-log-part-alone condition `∑c = 0` is a genuine SIDE CONDITION on the integrand, not
  a consequence of the algorithm terminating. The fully unconditional hyperexp soundness is the SEPARATE
  result `cIntegrateHyperexpFull = some res ⟹ D(res) = a/d` (whose abstract proof needs the §5.9 residual
  identity `extendDeriv_logPart_eq_div_add_residual` — currently a docstring claim, not a lemma — plus the
  base-RDE-oracle soundness for `∫R`); a larger task, NOT a discharge of `hcancel`.

The hypertangent case is analogous with `v = C b·X² + …` (the polynomial parts are no longer α-independent, so
the cancel sum is a different — still integrability-equivalent — condition).

★★ NEW — the fuel-free POLYNOMIAL branch a-priori soundness (`cIntegrateGFullWf_poly_eq`,
`cIntegrateGFullWf_poly_oneShot`), axiom-clean `[propext, choice, Quot.sound]`, **no** `native_decide`. The
companion to the pure-normal branch: when the polynomial part `fₚ ≠ 0`, the driver solves `Dqₚ = fₚ` by the
fuel-free poly-Risch-DE oracle and recombines `qₚ + gₙ/gₙd`. The shape lemma pins the recombined output
`((qₚ·gₙd + gₙ, gₙd), nrm.logs)` for the fuel-free driver; the one-shot gives
`cIntegrateGFullWf = some res ⟹ D(res) = a/d`, gated on the poly-Risch-DE FRONTIER `hpoly`
(`D(am qₚ) = am fₚ`), the normal-part one-shot `hnormal`, and the split reconstruction `hrecon`. The proof
reads the recombined rational `(qₚ·gₙd + gₙ)/gₙd = am qₚ + gₙ/gₙd`, splits `D` by `Derivation.map_add`,
then chains `hpoly`/`hnormal`/`hrecon`.
The primitive-base `hpoly` discharge now lives only in the fuel-free theorem
`cIntegrateGFullWf_poly_oneShot_base`.

★ THE GENERAL ONE-SHOT (Target 3, deferred — shape only). A single full-driver theorem
(`cIntegrateGFullWf = some res ⟹ D(res) = a/d`) covering BOTH branches is a `cisZero fp`
case split: `true` → `cIntegrateGFullWf_primitive_oneShot` for the fuel-free driver (or the corresponding
hyperexp sibling), `false` → `cIntegrateGFullWf_poly_oneShot`. It is NOT a clean additive theorem: the two
branches consume structurally DIFFERENT hypothesis bundles (the pure-normal milestones fold the normal
one-shot into Hermite `hherm` + per-root reassembly `hform` + reconstruction `hrecon`; the poly branch takes
the normal one-shot `hnormal` directly with a different split `hrecon`), so a combined statement must carry the
UNION of both bundles while each branch uses only its half — heavy plumbing for no new mathematical content.
Both per-branch one-shots are the citable facts; the general form is mechanical given a caller's chosen
hypotheses. -/

-- ★ Composed into the PRIMITIVE one-shot: with `hA` produced by the bridge from leftover properness, the
-- reduced-case identity `D(g) + logResidueSum = a/d` holds — `hA` is no longer a free hypothesis but the
-- proper-fraction property of the Hermite leftover.
example (Dt : DensePoly (DenseFrac ℚ)) (a d : DensePoly (DenseFrac ℚ))
    (cands : List (DenseFrac ℚ)) (s : Finset (CFieldSpec.K (DenseFrac ℚ))) (w : CFieldSpec.K (DenseFrac ℚ))
    (hDt : toPoly Dt = C w)
    (hherm : towerFractionFieldDeriv Dt
            (am (DenseFrac ℚ) (toPoly (DensePoly.cIntegrateReduced Dt a d cands).rational.1)
              / am (DenseFrac ℚ) (toPoly (DensePoly.cIntegrateReduced Dt a d cands).rational.2))
          + am (DenseFrac ℚ) (toPoly (cHermiteReduceTower Dt a d).2.1)
            / am (DenseFrac ℚ) (toPoly (cHermiteReduceTower Dt a d).2.2)
        = am (DenseFrac ℚ) (toPoly a) / am (DenseFrac ℚ) (toPoly d))
    (hden : toPoly (cHermiteReduceTower Dt a d).2.2 = Lagrange.nodal s id)
    (hproper : (toPoly (cHermiteReduceTower Dt a d).2.1).degree
      < (toPoly (cHermiteReduceTower Dt a d).2.2).degree)
    (hnorm : ∀ β ∈ s, w ≠ β′)
    (hform : (DensePoly.cIntegrateReduced Dt a d cands).logs.map
          (fun cv => (CFieldSpec.toK cv.1, toPoly cv.2))
        = s.toList.map (fun β =>
            ((toPoly (cHermiteReduceTower Dt a d).2.1).eval β
                / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β,
              X - C β))) :
    towerFractionFieldDeriv Dt
        (am (DenseFrac ℚ) (toPoly (DensePoly.cIntegrateReduced Dt a d cands).rational.1)
          / am (DenseFrac ℚ) (toPoly (DensePoly.cIntegrateReduced Dt a d cands).rational.2))
        + logResidueSum Dt (DensePoly.cIntegrateReduced Dt a d cands).logs
      = am (DenseFrac ℚ) (toPoly a) / am (DenseFrac ℚ) (toPoly d) :=
  field_identity_of_cIntegrateReducedG_primitive Dt a d cands s w hDt hherm hden
    (cHermiteReduceTowerG_numer_degree_lt Dt a d s hden hproper) hnorm hform

/-! ### ★★★ The `hA` discharge for `deg Dt ≤ 1`: reduced to exact-division connectors + input properness

`cIntegrateGFullWf_primitive_oneShot` / `…_qfunNZG` carries the degree side condition `hA :
(cHermiteReduceTower …).2.1.degree < s.card` as a **free** hypothesis. For `deg Dt ≤ 1` (the primitive /
exponential / log regimes) it is no longer free: the §5.3 chain
`cHermiteReduceTowerG_residual_proper_of_degree_le_one` (residual `a/d − D(g)` proper from input properness
`deg a < deg d`, `deg Dt ≤ 1`, the per-factor keystone `hb`/`hv`) →
`cHermiteReduceTowerG_leftover_proper_of_residual` (exact-division degree cancellation) →
`cHermiteReduceTowerG_numer_degree_lt` (squarefree-spelling rewrite) proves it. The remaining inputs are
the per-factor keystone `hb` (`= diophantineReduced_fst_degree_lt`), nonzero `hv`, and the **exact-division
connectors** `hdvd`/`hresDen` (the residual·radical exactly divides `resDen`, and `resDen ≠ 0`) — engine
regularity facts, **not** free side conditions. The fold accumulator is exposed as `g`/`hgeq` so the residual
`resNum/resDen` projections reduce by `rfl` (`simp [cHermiteReduceTower, toPolyG_cnormG]`). -/

/-- **`hA` discharged for the fuel-free Hermite reducer when `deg Dt ≤ 1`.** -/
theorem cHermiteReduceTowerG_numer_degree_lt_of_degree_le_one
    (Dt : DensePoly (DenseFrac ℚ)) (a d : DensePoly (DenseFrac ℚ))
    (s : Finset (CFieldSpec.K (DenseFrac ℚ)))
    (hDtdeg : (toPoly Dt).natDegree ≤ 1)
    (haProper : (toPoly a).degree < (toPoly d).degree)
    (hv : ∀ p ∈ (cSqfreeYunFF d).zipIdx, ¬ (p.2 + 1 ≤ 1) → toPoly p.1 ≠ 0)
    (hb : ∀ p ∈ (cSqfreeYunFF d).zipIdx, ¬ (p.2 + 1 ≤ 1) → ∀ (rhs : DensePoly (DenseFrac ℚ)),
        (toPoly (CPoly.diophantineReduced
            (cmul (CPolyEuclidean.div d (cpow p.1 (p.2 + 1))) (CPolyEngine.monomialDeriv Dt p.1)) p.1 rhs).1).degree
          < (toPoly p.1).degree)
    (hden : toPoly (cHermiteReduceTower Dt a d).2.2 = Lagrange.nodal s id)
    (g : DensePoly (DenseFrac ℚ) × DensePoly (DenseFrac ℚ))
    (hgeq : g = (cSqfreeYunFF d).zipIdx.foldl
      (fun (gAcc : DensePoly (DenseFrac ℚ) × DensePoly (DenseFrac ℚ)) (vi, idx) =>
          let i := idx + 1
          if i ≤ 1 then gAcc
          else
            let Vi_pow := cpow vi i
            let u := CPolyEuclidean.div d Vi_pow
            let gloc := (cHermiteReduceTowerInnerWf Dt vi u (i - 1) a ([CCommRing.zero], [CCommRing.one])).1
            (cadd (cmul gAcc.1 gloc.2) (cmul gloc.1 gAcc.2), cmul gAcc.2 gloc.2))
      ([CCommRing.zero], [CCommRing.one]))
    (hdvd : toPoly (cmul d (cmul g.2 g.2))
      ∣ toPoly (cmul (csub (cmul a (cmul g.2 g.2))
          (cmul d (csub (cmul (CPolyEngine.monomialDeriv Dt g.1) g.2) (cmul g.1 (CPolyEngine.monomialDeriv Dt g.2)))))
        ((cSqfreeYunFF d).foldl (fun acc vi => cmul acc vi) [CCommRing.one])))
    (hresDen : cnorm (cmul d (cmul g.2 g.2)) ≠ ([] : DensePoly (DenseFrac ℚ))) :
    (toPoly (cHermiteReduceTower Dt a d).2.1).degree < s.card := by
  have hresProper := cHermiteReduceTowerG_residual_proper_of_degree_le_one Dt a d
    (cSqfreeYunFF d) hDtdeg haProper
    (fun p hp hskip => ⟨hv p hp hskip, hb p hp hskip⟩)
  simp only at hresProper
  subst hgeq
  have hDstar : toPoly ((cSqfreeYunFF d).foldl (fun acc vi => cmul acc vi) [CCommRing.one])
      ≠ 0 := by
    have hd2 : toPoly (cHermiteReduceTower Dt a d).2.2
        = toPoly ((cSqfreeYunFF d).foldl (fun acc vi => cmul acc vi) [CCommRing.one]) := by
      simp only [cHermiteReduceTower, squarefreeYun_dense_wf_eq, denote]
    rw [← hd2, hden]; exact Lagrange.nodal_ne_zero
  have hproper := cHermiteReduceTowerG_leftover_proper_of_residual Dt a d
    (csub (cmul a (cmul _ _))
      (cmul d (csub (cmul (CPolyEngine.monomialDeriv Dt _) _) (cmul _ (CPolyEngine.monomialDeriv Dt _)))))
    (cmul d (cmul _ _))
    ((cSqfreeYunFF d).foldl (fun acc vi => cmul acc vi) [CCommRing.one])
    (by simp only [cHermiteReduceTower, squarefreeYun_dense_wf_eq, denote])
    (by simp only [cHermiteReduceTower, squarefreeYun_dense_wf_eq, denote])
    hdvd hresDen hDstar hresProper
  exact cHermiteReduceTowerG_numer_degree_lt Dt a d s hden hproper

/-! ### ★★★ The CAPSTONE: the fuel-free primitive one-shot at `ℚ(x)(t)` with `hA` DISCHARGED

`cIntegrateGFullWf_primitive_oneShot_qfunNZG` carries `hA` (`deg h_num < s.card`) as a free hypothesis. For a
primitive monomial `toPoly Dt = C w` (so `deg Dt = 0 ≤ 1`) the capstone below discharges it from Wf canonical
simple-part properness and the Wf Hermite degree bridge, leaving only the genuine Bronstein side conditions
and exact-division connectors. -/

/-- **The fuel-free primitive one-shot at `ℚ(x)(t)` with `hA` discharged from simple properness.** -/
theorem cIntegrateGFullWf_primitive_oneShot_inputProper_qfunNZG (Dt : DensePoly (DenseFrac ℚ))
    (a d : DensePoly (DenseFrac ℚ)) (cands : List (DenseFrac ℚ)) (res : IntegralResult (DenseFrac ℚ))
    (s : Finset (CFieldSpec.K (DenseFrac ℚ))) (w : CFieldSpec.K (DenseFrac ℚ))
    (hDt : toPoly Dt = C w)
    (hbranch : IsPureNormalBranch Dt a d)
    (hsome : DensePoly.cIntegrateGFullWf Dt a d cands = some res)
    (hrecon : am (DenseFrac ℚ) (toPoly (canonicalRepresentationFast Dt a d).2.2.1)
          / am (DenseFrac ℚ) (toPoly (canonicalRepresentationFast Dt a d).2.2.2)
        = am (DenseFrac ℚ) (toPoly a) / am (DenseFrac ℚ) (toPoly d))
    (hherm : towerFractionFieldDeriv Dt
            (am (DenseFrac ℚ) (toPoly (DensePoly.cIntegrateReduced Dt
                  (canonicalRepresentationFast Dt a d).2.2.1
                  (canonicalRepresentationFast Dt a d).2.2.2 cands).rational.1)
              / am (DenseFrac ℚ) (toPoly (DensePoly.cIntegrateReduced Dt
                  (canonicalRepresentationFast Dt a d).2.2.1
                  (canonicalRepresentationFast Dt a d).2.2.2 cands).rational.2))
          + am (DenseFrac ℚ) (toPoly (cHermiteReduceTower Dt
                (canonicalRepresentationFast Dt a d).2.2.1
                (canonicalRepresentationFast Dt a d).2.2.2).2.1)
            / am (DenseFrac ℚ) (toPoly (cHermiteReduceTower Dt
                (canonicalRepresentationFast Dt a d).2.2.1
                (canonicalRepresentationFast Dt a d).2.2.2).2.2)
        = am (DenseFrac ℚ) (toPoly (canonicalRepresentationFast Dt a d).2.2.1)
            / am (DenseFrac ℚ) (toPoly (canonicalRepresentationFast Dt a d).2.2.2))
    (hden : toPoly (cHermiteReduceTower Dt
          (canonicalRepresentationFast Dt a d).2.2.1
          (canonicalRepresentationFast Dt a d).2.2.2).2.2 = Lagrange.nodal s id)
    (hnorm : ∀ β ∈ s, w ≠ β′)
    (hform : (DensePoly.cIntegrateReduced Dt
            (canonicalRepresentationFast Dt a d).2.2.1
            (canonicalRepresentationFast Dt a d).2.2.2 cands).logs.map
          (fun cv => (CFieldSpec.toK cv.1, toPoly cv.2))
        = s.toList.map (fun β =>
            ((toPoly (cHermiteReduceTower Dt
                  (canonicalRepresentationFast Dt a d).2.2.1
                  (canonicalRepresentationFast Dt a d).2.2.2).2.1).eval β
                / (Differential.implicitDeriv (toPoly Dt) (Lagrange.nodal s id)).eval β,
              X - C β)))
    (haProper : (toPoly (canonicalRepresentationFast Dt a d).2.2.1).degree
      < (toPoly (canonicalRepresentationFast Dt a d).2.2.2).degree)
    (hv : ∀ p ∈ (cSqfreeYunFF (canonicalRepresentationFast Dt a d).2.2.2).zipIdx,
        ¬ (p.2 + 1 ≤ 1) → toPoly p.1 ≠ 0)
    (hbk : ∀ p ∈ (cSqfreeYunFF (canonicalRepresentationFast Dt a d).2.2.2).zipIdx,
        ¬ (p.2 + 1 ≤ 1) → ∀ (rhs : DensePoly (DenseFrac ℚ)),
        (toPoly (CPoly.diophantineReduced
            (cmul (CPolyEuclidean.div (canonicalRepresentationFast Dt a d).2.2.2
              (cpow p.1 (p.2 + 1))) (CPolyEngine.monomialDeriv Dt p.1)) p.1 rhs).1).degree
          < (toPoly p.1).degree)
    (g : DensePoly (DenseFrac ℚ) × DensePoly (DenseFrac ℚ))
    (hgeq : g = (cSqfreeYunFF (canonicalRepresentationFast Dt a d).2.2.2).zipIdx.foldl
      (fun (gAcc : DensePoly (DenseFrac ℚ) × DensePoly (DenseFrac ℚ)) (vi, idx) =>
        let i := idx + 1
        if i ≤ 1 then gAcc
        else
          let Vi_pow := cpow vi i
          let u := CPolyEuclidean.div (canonicalRepresentationFast Dt a d).2.2.2 Vi_pow
          let gloc := (cHermiteReduceTowerInnerWf Dt vi u (i - 1)
            (canonicalRepresentationFast Dt a d).2.2.1 ([CCommRing.zero], [CCommRing.one])).1
          (cadd (cmul gAcc.1 gloc.2) (cmul gloc.1 gAcc.2), cmul gAcc.2 gloc.2))
      ([CCommRing.zero], [CCommRing.one]))
    (hdvd : toPoly (cmul (canonicalRepresentationFast Dt a d).2.2.2 (cmul g.2 g.2))
      ∣ toPoly (cmul (csub (cmul (canonicalRepresentationFast Dt a d).2.2.1 (cmul g.2 g.2))
          (cmul (canonicalRepresentationFast Dt a d).2.2.2
            (csub (cmul (CPolyEngine.monomialDeriv Dt g.1) g.2) (cmul g.1 (CPolyEngine.monomialDeriv Dt g.2)))))
        ((cSqfreeYunFF (canonicalRepresentationFast Dt a d).2.2.2).foldl
          (fun acc vi => cmul acc vi) [CCommRing.one])))
    (hresDen : cnorm (cmul (canonicalRepresentationFast Dt a d).2.2.2 (cmul g.2 g.2))
      ≠ ([] : DensePoly (DenseFrac ℚ))) :
    towerFractionFieldDeriv Dt
        (am (DenseFrac ℚ) (toPoly res.rational.1) / am (DenseFrac ℚ) (toPoly res.rational.2))
        + logResidueSum Dt res.logs
      = am (DenseFrac ℚ) (toPoly a) / am (DenseFrac ℚ) (toPoly d) := by
  have hDtdeg : (toPoly Dt).natDegree ≤ 1 := by
    rw [hDt, Polynomial.natDegree_C]; exact Nat.zero_le 1
  have hA := cHermiteReduceTowerG_numer_degree_lt_of_degree_le_one Dt
    (canonicalRepresentationFast Dt a d).2.2.1
    (canonicalRepresentationFast Dt a d).2.2.2 s hDtdeg haProper hv hbk hden g hgeq
    hdvd hresDen
  exact cIntegrateGFullWf_primitive_oneShot Dt a d cands res s w hDt hbranch hsome hrecon
    hherm hden hA hnorm hform

/-! ### ★★★ The fuel-free POLY-BRANCH CAPSTONE at `ℚ(x)(t)`

The polynomial-branch analogue of the primitive normal-part capstone, now over the fuel-free full driver.
The primitive-base restriction remains essential: the termwise polynomial antiderivative proves `Dqₚ = fₚ`
only for `Dt = [CCommRing.one]`. The Wf theorem takes simple-part properness directly; the separate Wf canonical
simple-proper bridge is still a later cleanup target. -/

/-- **The fuel-free primitive-base poly one-shot at `ℚ(x)(t)` with `hpoly` and `hA` discharged from simple
properness.** -/
theorem cIntegrateGFullWf_poly_oneShot_simpleProper_qfunNZG
    (a d : DensePoly (DenseFrac ℚ)) (cands : List (DenseFrac ℚ)) (res : IntegralResult (DenseFrac ℚ))
    (qp : DensePoly (DenseFrac ℚ)) (s : Finset (CFieldSpec.K (DenseFrac ℚ)))
    (hbranch : IsPolynomialBranch ([CCommRing.one] : DensePoly (DenseFrac ℚ)) a d)
    (hsome : DensePoly.cIntegrateGFullWf ([CCommRing.one] : DensePoly (DenseFrac ℚ)) a d cands = some res)
    (hqp : DensePoly.cPolyRischDE ([CCommRing.one] : DensePoly (DenseFrac ℚ)) []
        (canonicalRepresentationFast ([CCommRing.one] : DensePoly (DenseFrac ℚ)) a d).1
        ((DensePoly.cdeg (canonicalRepresentationFast ([CCommRing.one] : DensePoly (DenseFrac ℚ)) a d).1 : ℤ) + 1)
        = some qp)
    (hgden : am (DenseFrac ℚ) (toPoly (DensePoly.cIntegrateReduced ([CCommRing.one] : DensePoly (DenseFrac ℚ))
          (canonicalRepresentationFast ([CCommRing.one] : DensePoly (DenseFrac ℚ)) a d).2.2.1
          (canonicalRepresentationFast ([CCommRing.one] : DensePoly (DenseFrac ℚ)) a d).2.2.2 cands).rational.2)
        ≠ 0)
    (hconst : Differential.mapCoeffs
        (toPoly (canonicalRepresentationFast ([CCommRing.one] : DensePoly (DenseFrac ℚ)) a d).1) = 0)
    (hherm : towerFractionFieldDeriv ([CCommRing.one] : DensePoly (DenseFrac ℚ))
            (am (DenseFrac ℚ) (toPoly (DensePoly.cIntegrateReduced ([CCommRing.one] : DensePoly (DenseFrac ℚ))
                  (canonicalRepresentationFast ([CCommRing.one] : DensePoly (DenseFrac ℚ)) a d).2.2.1
                  (canonicalRepresentationFast ([CCommRing.one] : DensePoly (DenseFrac ℚ)) a d).2.2.2 cands).rational.1)
              / am (DenseFrac ℚ) (toPoly (DensePoly.cIntegrateReduced ([CCommRing.one] : DensePoly (DenseFrac ℚ))
                  (canonicalRepresentationFast ([CCommRing.one] : DensePoly (DenseFrac ℚ)) a d).2.2.1
                  (canonicalRepresentationFast ([CCommRing.one] : DensePoly (DenseFrac ℚ)) a d).2.2.2 cands).rational.2))
          + am (DenseFrac ℚ) (toPoly (cHermiteReduceTower ([CCommRing.one] : DensePoly (DenseFrac ℚ))
                (canonicalRepresentationFast ([CCommRing.one] : DensePoly (DenseFrac ℚ)) a d).2.2.1
                (canonicalRepresentationFast ([CCommRing.one] : DensePoly (DenseFrac ℚ)) a d).2.2.2).2.1)
            / am (DenseFrac ℚ) (toPoly (cHermiteReduceTower ([CCommRing.one] : DensePoly (DenseFrac ℚ))
                (canonicalRepresentationFast ([CCommRing.one] : DensePoly (DenseFrac ℚ)) a d).2.2.1
                (canonicalRepresentationFast ([CCommRing.one] : DensePoly (DenseFrac ℚ)) a d).2.2.2).2.2)
        = am (DenseFrac ℚ)
            (toPoly (canonicalRepresentationFast ([CCommRing.one] : DensePoly (DenseFrac ℚ)) a d).2.2.1)
          / am (DenseFrac ℚ)
            (toPoly (canonicalRepresentationFast ([CCommRing.one] : DensePoly (DenseFrac ℚ)) a d).2.2.2))
    (hden : toPoly (cHermiteReduceTower ([CCommRing.one] : DensePoly (DenseFrac ℚ))
          (canonicalRepresentationFast ([CCommRing.one] : DensePoly (DenseFrac ℚ)) a d).2.2.1
          (canonicalRepresentationFast ([CCommRing.one] : DensePoly (DenseFrac ℚ)) a d).2.2.2).2.2
        = Lagrange.nodal s id)
    (hnorm : ∀ β ∈ s, (1 : CFieldSpec.K (DenseFrac ℚ)) ≠ β′)
    (hform : (DensePoly.cIntegrateReduced ([CCommRing.one] : DensePoly (DenseFrac ℚ))
            (canonicalRepresentationFast ([CCommRing.one] : DensePoly (DenseFrac ℚ)) a d).2.2.1
            (canonicalRepresentationFast ([CCommRing.one] : DensePoly (DenseFrac ℚ)) a d).2.2.2 cands).logs.map
          (fun cv => (CFieldSpec.toK cv.1, toPoly cv.2))
        = s.toList.map (fun β =>
            ((toPoly (cHermiteReduceTower ([CCommRing.one] : DensePoly (DenseFrac ℚ))
                  (canonicalRepresentationFast ([CCommRing.one] : DensePoly (DenseFrac ℚ)) a d).2.2.1
                  (canonicalRepresentationFast ([CCommRing.one] : DensePoly (DenseFrac ℚ)) a d).2.2.2).2.1).eval β
                / (Differential.implicitDeriv (toPoly ([CCommRing.one] : DensePoly (DenseFrac ℚ)))
                    (Lagrange.nodal s id)).eval β,
              X - C β)))
    (haProper : (toPoly (canonicalRepresentationFast ([CCommRing.one] : DensePoly (DenseFrac ℚ)) a d).2.2.1).degree
      < (toPoly (canonicalRepresentationFast ([CCommRing.one] : DensePoly (DenseFrac ℚ)) a d).2.2.2).degree)
    (hv : ∀ p ∈ (cSqfreeYunFF (canonicalRepresentationFast
          ([CCommRing.one] : DensePoly (DenseFrac ℚ)) a d).2.2.2).zipIdx,
        ¬ (p.2 + 1 ≤ 1) → toPoly p.1 ≠ 0)
    (hbk : ∀ p ∈ (cSqfreeYunFF (canonicalRepresentationFast
          ([CCommRing.one] : DensePoly (DenseFrac ℚ)) a d).2.2.2).zipIdx,
        ¬ (p.2 + 1 ≤ 1) → ∀ (rhs : DensePoly (DenseFrac ℚ)),
        (toPoly (CPoly.diophantineReduced
            (cmul (CPolyEuclidean.div (canonicalRepresentationFast
              ([CCommRing.one] : DensePoly (DenseFrac ℚ)) a d).2.2.2 (cpow p.1 (p.2 + 1)))
              (CPolyEngine.monomialDeriv ([CCommRing.one] : DensePoly (DenseFrac ℚ)) p.1)) p.1 rhs).1).degree
          < (toPoly p.1).degree)
    (g : DensePoly (DenseFrac ℚ) × DensePoly (DenseFrac ℚ))
    (hgeq : g = (cSqfreeYunFF (canonicalRepresentationFast
        ([CCommRing.one] : DensePoly (DenseFrac ℚ)) a d).2.2.2).zipIdx.foldl
      (fun (gAcc : DensePoly (DenseFrac ℚ) × DensePoly (DenseFrac ℚ)) (vi, idx) =>
        let i := idx + 1
        if i ≤ 1 then gAcc
        else
          let Vi_pow := cpow vi i
          let u := CPolyEuclidean.div (canonicalRepresentationFast
            ([CCommRing.one] : DensePoly (DenseFrac ℚ)) a d).2.2.2 Vi_pow
          let gloc := (cHermiteReduceTowerInnerWf ([CCommRing.one] : DensePoly (DenseFrac ℚ)) vi u (i - 1)
            (canonicalRepresentationFast ([CCommRing.one] : DensePoly (DenseFrac ℚ)) a d).2.2.1
            ([CCommRing.zero], [CCommRing.one])).1
          (cadd (cmul gAcc.1 gloc.2) (cmul gloc.1 gAcc.2), cmul gAcc.2 gloc.2))
      ([CCommRing.zero], [CCommRing.one]))
    (hdvd : toPoly (cmul (canonicalRepresentationFast
          ([CCommRing.one] : DensePoly (DenseFrac ℚ)) a d).2.2.2 (cmul g.2 g.2))
      ∣ toPoly (cmul (csub (cmul (canonicalRepresentationFast
            ([CCommRing.one] : DensePoly (DenseFrac ℚ)) a d).2.2.1 (cmul g.2 g.2))
          (cmul (canonicalRepresentationFast ([CCommRing.one] : DensePoly (DenseFrac ℚ)) a d).2.2.2
            (csub (cmul (CPolyEngine.monomialDeriv ([CCommRing.one] : DensePoly (DenseFrac ℚ)) g.1) g.2)
              (cmul g.1 (CPolyEngine.monomialDeriv ([CCommRing.one] : DensePoly (DenseFrac ℚ)) g.2)))))
        ((cSqfreeYunFF (canonicalRepresentationFast
          ([CCommRing.one] : DensePoly (DenseFrac ℚ)) a d).2.2.2).foldl (fun acc vi => cmul acc vi) [CCommRing.one])))
    (hresDen : cnorm (cmul (canonicalRepresentationFast
      ([CCommRing.one] : DensePoly (DenseFrac ℚ)) a d).2.2.2 (cmul g.2 g.2)) ≠ ([] : DensePoly (DenseFrac ℚ)))
    (hrecon : am (DenseFrac ℚ)
          (toPoly (canonicalRepresentationFast ([CCommRing.one] : DensePoly (DenseFrac ℚ)) a d).1)
        + am (DenseFrac ℚ)
            (toPoly (canonicalRepresentationFast ([CCommRing.one] : DensePoly (DenseFrac ℚ)) a d).2.2.1)
          / am (DenseFrac ℚ)
            (toPoly (canonicalRepresentationFast ([CCommRing.one] : DensePoly (DenseFrac ℚ)) a d).2.2.2)
        = am (DenseFrac ℚ) (toPoly a) / am (DenseFrac ℚ) (toPoly d)) :
    towerFractionFieldDeriv ([CCommRing.one] : DensePoly (DenseFrac ℚ))
        (am (DenseFrac ℚ) (toPoly res.rational.1) / am (DenseFrac ℚ) (toPoly res.rational.2))
        + logResidueSum ([CCommRing.one] : DensePoly (DenseFrac ℚ)) res.logs
      = am (DenseFrac ℚ) (toPoly a) / am (DenseFrac ℚ) (toPoly d) := by
  have hDt : toPoly ([CCommRing.one] : DensePoly (DenseFrac ℚ)) = C (1 : CFieldSpec.K (DenseFrac ℚ)) := by
    simp only [denote, map_one, mul_zero, add_zero]
  have hDtdeg : (toPoly ([CCommRing.one] : DensePoly (DenseFrac ℚ))).natDegree ≤ 1 := by
    rw [hDt, Polynomial.natDegree_C]; exact Nat.zero_le 1
  have hA := cHermiteReduceTowerG_numer_degree_lt_of_degree_le_one
    ([CCommRing.one] : DensePoly (DenseFrac ℚ))
    (canonicalRepresentationFast ([CCommRing.one] : DensePoly (DenseFrac ℚ)) a d).2.2.1
    (canonicalRepresentationFast ([CCommRing.one] : DensePoly (DenseFrac ℚ)) a d).2.2.2 s hDtdeg
    haProper hv hbk hden g hgeq hdvd hresDen
  have hnormal := field_identity_of_cIntegrateReducedG_primitive
    ([CCommRing.one] : DensePoly (DenseFrac ℚ))
    (canonicalRepresentationFast ([CCommRing.one] : DensePoly (DenseFrac ℚ)) a d).2.2.1
    (canonicalRepresentationFast ([CCommRing.one] : DensePoly (DenseFrac ℚ)) a d).2.2.2 cands s
    (1 : CFieldSpec.K (DenseFrac ℚ)) hDt hherm hden hA hnorm hform
  exact cIntegrateGFullWf_poly_oneShot_base a d cands res qp hbranch hsome hqp hgden hconst hnormal
    hrecon

end DeepWiki.SymbolicIntegration
