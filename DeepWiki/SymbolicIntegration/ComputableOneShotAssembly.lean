import DeepWiki.SymbolicIntegration.ComputableResidueMatchSoundness
import DeepWiki.SymbolicIntegration.ComputableOneShotSoundness

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

/-! ### ★ Status — the list↔Finset bridge, axiom-clean -/

#print axioms ResidueMatchTower.primitive_residue_match_list
#print axioms primitive_residue_match_list_engine

end DeepWiki.SymbolicIntegration
