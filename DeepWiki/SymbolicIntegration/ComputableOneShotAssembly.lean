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
  primitive case (`primitive_cancel`), so the primitive regime needs NO integrability witness.
* **★★ The HYPEREXPONENTIAL one-shot** (`cIntegrateGFull_hyperexp_oneShot` / `…_qfunNZG`) — `cIntegrateGFull =
  some res ⟹ D(res) = a/d` for a hyperexp `Dt = η′·t` (`toPolyG Dt = C b·X`, `b ≠ 0`), gated on the same
  abstract engine inputs PLUS the integrability witness `hsum : ∑c = 0`. Built on the UNCONDITIONAL
  decomposition `monomial_residue_sum_eq_cancel_add` (residue sum = cancel sum + a/d) and the iff
  `hyperexp_residue_match_iff_sum_zero` (residue match `= a/d` ⟺ `∑c = 0`), threaded through the engine via
  `hyperexp_engine_hmatch`. So the checker-free one-shot now covers the PRIMITIVE and EXPONENTIAL cases.

★ The hyperexp one-shot is GENUINELY CONDITIONAL on `hsum : ∑c = 0`, NOT unconditional: `cIntegrateGFull`'s
pure-normal branch returns `some` even when `∑c ≠ 0` (it emits the §5.6 RT logs that OVERSHOOT a hyperexp
normal part by `R = η·∑c`; the §5.9 residual feedback that fixes this lives in the SEPARATE driver
`cIntegrateHyperexpFullG`). So "engine success ⟹ `∑c = 0`" is FALSE for this driver — `∑c = 0` is a true side
condition on the integrand, not an algorithm-termination consequence. See the closing status for the full
obstruction analysis. -/

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

/-! ### ★ Task 4 (STRETCH): the general-case `hcancel` for the HYPEREXPONENTIAL monomial reduces to `∑ c_α = 0`

For a NON-primitive monomial the residue match needs `monomial_residue_match_of_cancel`'s extra hypothesis
`hcancel : ∑_α C(c_α)·((v − Cα′) /ₘ (t−α)) = 0`. The cleanest non-primitive case is the **hyperexponential**
`Dt = η′·t`, i.e. `v = C b · X` (`b = η′`): then each polynomial part `(C b·X − C α′) /ₘ (X − C α)` is the
*constant* `C b` (degree-1-over-degree-1 quotient), **independent of α**, so `hcancel` collapses to
`C b·∑_α C(c_α) = 0`, i.e. (over `RatFunc K`) `b·(∑_α c_α) = 0` — and with `b = η′ ≠ 0` this is exactly the
integrability condition `∑_α c_α = 0` (the exponential-case correction: `a/d` integrable in the log part
alone). We prove this reduction, pinning the precise general-case obstruction the engine's integrability
witness must supply. -/

omit [Differential K] [Algebra ℚ K] in
/-- **The hyperexp polynomial part is the constant `C b`** — `(C b·X − C e) /ₘ (X − C a) = C b` over a field:
the degree-1-over-degree-1 quotient of `C b·X − C e` by the monic `X − C a` is the leading coefficient `C b`
(remainder `C(b·a − e)`, degree `0 < 1`). By `divByMonic` uniqueness from `modByMonic_add_div` (`C b·X − C e
= (X − C a)·C b + C(b·a − e)`). The per-term polynomial part of the hyperexponential monomial `Dt = η′·t`
(`v = C b·X`), which is α-independent — the source of the `hcancel` collapse to `∑ c_α = 0`. -/
theorem divByMonic_C_mul_X_sub_C (b e a : K) :
    (C b * X - C e) /ₘ (X - C a) = C b := by
  -- the unique `(quot, rem)` with `f = (X−Ca)·quot + rem`, `deg rem < 1`: `quot = C b`, `rem = C(b·a − e)`
  refine (div_modByMonic_unique (C b) (C (b * a - e)) (monic_X_sub_C a) ⟨?_, ?_⟩).1
  · -- `C(b·a − e) + (X − C a)·C b = C b·X − C e`
    rw [map_sub, map_mul]; ring
  · -- the remainder `C(b·a − e)` has degree `0 < 1 = deg (X − C a)`
    rw [degree_X_sub_C]
    exact lt_of_le_of_lt degree_C_le (by decide)

omit [Algebra ℚ K] in
/-- **★ The hyperexponential `hcancel` sum is `algebraMap(C(b·∑c_α))`** — for the hyperexponential monomial
`v = C b·X` (`b = η′`), the `monomial_residue_match_of_cancel` polynomial-part sum
`∑_{α∈s} algebraMap(C(c_α)·((v − Cα′) /ₘ (t−α)))` equals `algebraMap(C(b·∑_{α∈s} c_α))` over `RatFunc K` —
each polynomial part is the α-independent constant `C b` (`divByMonic_C_mul_X_sub_C`), so the sum is
`algebraMap(C(∑_α c_α·b)) = algebraMap(C(b·∑c_α))`. The reduction of the general-case `hcancel` to a single
scalar `b·∑c_α`. -/
theorem hyperexp_cancel_sum_eq (s : Finset K) (b : K) (c : K → K) :
    ∑ α ∈ s, algebraMap K[X] (RatFunc K) (C (c α) * ((C b * X - C (α′)) /ₘ (X - C α)))
      = algebraMap K[X] (RatFunc K) (C (b * ∑ α ∈ s, c α)) := by
  -- each polynomial part is the constant `C b`; fold the residue and sum the constants
  have hterm : ∀ α ∈ s,
      algebraMap K[X] (RatFunc K) (C (c α) * ((C b * X - C (α′)) /ₘ (X - C α)))
        = algebraMap K[X] (RatFunc K) (C (c α * b)) := by
    intro α _
    rw [divByMonic_C_mul_X_sub_C, ← C_mul]
  rw [Finset.sum_congr rfl hterm, ← map_sum]
  -- `∑_α C(c_α·b) = C(∑_α c_α·b) = C(b·∑c_α)`, then the single `algebraMap` of equal polynomials
  congr 1
  rw [← map_sum, Finset.mul_sum]
  exact congrArg C (Finset.sum_congr rfl fun α _ => mul_comm (c α) b)

omit [Algebra ℚ K] in
/-- **★★ The general-case `hcancel` ⟺ `∑ c_α = 0` for the hyperexponential monomial** (the STRETCH
obstruction, pinned) — for `v = C b·X` (hyperexponential `Dt = η′·t`, `b = η′ ≠ 0`), the
`monomial_residue_match_of_cancel` polynomial-part cancellation
`∑_{α∈s} algebraMap(C(c_α)·((v − Cα′) /ₘ (t−α))) = 0` holds **iff** `∑_{α∈s} c_α = 0` — the integrability
condition (`a/d` integrable in the log part alone, the exponential-case correction). So for the
hyperexponential case the general `hcancel` is GENUINELY EXTRA content equivalent to `∑ c_α = 0`, NOT a free
identity. By `hyperexp_cancel_sum_eq` (the sum is `algebraMap(C(b·∑c_α))`) and `algebraMap`-injectivity:
`algebraMap(C(b·∑c_α)) = 0 ↔ b·∑c_α = 0 ↔ ∑c_α = 0` (`b ≠ 0`). The precise general-case obstruction the
engine's integrability witness must discharge. -/
theorem hyperexp_cancel_iff_sum_zero (s : Finset K) (b : K) (hb : b ≠ 0) (c : K → K) :
    (∑ α ∈ s, algebraMap K[X] (RatFunc K) (C (c α) * ((C b * X - C (α′)) /ₘ (X - C α))) = 0)
      ↔ ∑ α ∈ s, c α = 0 := by
  rw [hyperexp_cancel_sum_eq s b c]
  -- `algebraMap (C x) = 0 ↔ x = 0` (algebraMap `K[X] → RatFunc K` and `C` both injective)
  rw [(map_eq_zero_iff _ (RatFunc.algebraMap_injective K)), Polynomial.C_eq_zero,
    mul_eq_zero, or_iff_right hb]

/-! ### ★ Task 2 (the decomposition): the monomial RT residue sum = `(cancel sum) + a/d` UNCONDITIONALLY

`monomial_residue_match_of_cancel` proves the residue sum `= a/d` *given* `hcancel`. Its proof first rewrites
the sum into `(∑_α c_α·(v − Cα′) /ₘ (t−α)) + a/d` (`Finset.sum_add_distrib` after the per-term euclidean
split), then *kills* the first summand with `hcancel`. We expose that intermediate **unconditional**
decomposition — `residue sum = (cancel sum) + a/d` for ANY monomial `v` — which is the engine-success
analysis's pivot: the residue match `residue sum = a/d` holds **iff** the cancel sum vanishes. Re-derived in
this file from the public helpers `extendDeriv_implicitDeriv_logDeriv_X_sub_C`, `algebraMap_div_X_sub_C_split`,
`residue_mul_eval_sub_eq`, `ratFunc_eq_sum_residue_div` (the same steps as `monomial_residue_match_of_cancel`,
minus the final `hcancel` rewrite). -/

/-- **★ The unconditional monomial RT decomposition** `residue sum = (cancel sum) + a/d` — for a squarefree
`d = ∏_{α∈s}(t−α)`, `deg a < #s`, an arbitrary monomial `Dt = v`, every root normal (`v(α) ≠ α′`), the
monomial RT residue sum `∑_{α∈s} C(c_α)·(D(t−α)/(t−α))` (`c_α = a(α)/(Dd)(α)`, `D = extendDeriv (implicitDeriv
v)`) equals the **polynomial-part cancel sum** `∑_{α∈s} C(c_α)·((v − Cα′) /ₘ (t−α))` PLUS `a/d`, with **no**
`hcancel` hypothesis. The proof of `monomial_residue_match_of_cancel` before it applies `hcancel`: each
summand splits (`algebraMap_div_X_sub_C_split`) into its polynomial part `C(c_α)·((v−Cα′) /ₘ (t−α))` and its
residue `C(a(α)/d′(α))/(t−α)`; `Finset.sum_add_distrib` separates the two, the residue half reassembles `a/d`
(`ratFunc_eq_sum_residue_div`). The pivot for the engine-success ⟺ integrability analysis: the residue match
`= a/d` is equivalent to the cancel sum vanishing. -/
theorem monomial_residue_sum_eq_cancel_add (s : Finset K) (a v : K[X])
    (hA : a.degree < s.card) (hnorm : ∀ α ∈ s, v.eval α ≠ α′) :
    ∑ α ∈ s, algebraMap K[X] (RatFunc K)
          (C (a.eval α / (Differential.implicitDeriv v (Lagrange.nodal s id)).eval α))
        * (extendDeriv (Differential.implicitDeriv v)
              (algebraMap K[X] (RatFunc K) (X - C α))
            / algebraMap K[X] (RatFunc K) (X - C α))
      = (∑ α ∈ s, algebraMap K[X] (RatFunc K)
            (C (a.eval α / (Differential.implicitDeriv v (Lagrange.nodal s id)).eval α)
              * ((v - C (α′)) /ₘ (X - C α))))
        + algebraMap K[X] (RatFunc K) a / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id) := by
  -- abbreviation for the RT residue at `α`
  set c : K → K := fun α => a.eval α / (Differential.implicitDeriv v (Lagrange.nodal s id)).eval α
    with hc
  -- rewrite each summand: monomial log-derivative, then euclidean split (verbatim `monomial_residue_match_of_cancel`)
  have hterm : ∀ α ∈ s,
      algebraMap K[X] (RatFunc K) (C (c α))
          * (extendDeriv (Differential.implicitDeriv v) (algebraMap K[X] (RatFunc K) (X - C α))
              / algebraMap K[X] (RatFunc K) (X - C α))
        = algebraMap K[X] (RatFunc K) (C (c α) * ((v - C (α′)) /ₘ (X - C α)))
          + algebraMap K[X] (RatFunc K) (C (a.eval α / (derivative (Lagrange.nodal s id)).eval α))
              / algebraMap K[X] (RatFunc K) (X - C α) := by
    intro α hα
    rw [extendDeriv_implicitDeriv_logDeriv_X_sub_C, algebraMap_div_X_sub_C_split (v - C (α′)) α,
      mul_add, ← map_mul]
    congr 1
    rw [eval_sub, eval_C, ← mul_div_assoc, ← map_mul, ← C_mul]
    have hroot : (Lagrange.nodal s id).eval α = 0 := by
      simpa using Lagrange.eval_nodal_at_node (s := s) (v := (id : K → K)) hα
    rw [hc]
    rw [residue_mul_eval_sub_eq a v (Lagrange.nodal s id) α hroot (hnorm α hα)]
  -- separate the polynomial-part sum from the residue sum; the residue sum reassembles `a/d`
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  rw [← ratFunc_eq_sum_residue_div s a hA]

/-- **★★ The hyperexp residue match ⟺ `∑ c_α = 0`** — for the hyperexponential monomial `v = C b·X`
(`Dt = η′·t`, `b = η′ ≠ 0`), the monomial RT residue sum equals `a/d` (the residue match `hmatch` the engine
consumes) **iff** `∑_{α∈s} c_α = 0` — the integrability condition (`a/d` integrable in the log part alone).
Composes the unconditional decomposition `monomial_residue_sum_eq_cancel_add` (residue sum = cancel sum + a/d)
with `hyperexp_cancel_iff_sum_zero` (cancel sum = 0 ⟺ ∑c = 0): `residue sum = a/d ⟺ cancel sum = 0 ⟺ ∑c = 0`.
The cleanest pin of the hyperexp integrability obstruction — the residue match the §5.6/`cIntegrateGFull`
log-part needs is GENUINELY EQUIVALENT to the side condition `∑c = 0`, not an engine-success consequence
(see the closing status: `cIntegrateGFull`'s pure-normal branch returns `some` even when `∑c ≠ 0`). -/
theorem hyperexp_residue_match_iff_sum_zero (s : Finset K) (a : K[X]) (b : K) (hb : b ≠ 0)
    (hA : a.degree < s.card) (hnorm : ∀ α ∈ s, (C b * X).eval α ≠ α′) :
    (∑ α ∈ s, algebraMap K[X] (RatFunc K)
          (C (a.eval α / (Differential.implicitDeriv (C b * X) (Lagrange.nodal s id)).eval α))
        * (extendDeriv (Differential.implicitDeriv (C b * X))
              (algebraMap K[X] (RatFunc K) (X - C α))
            / algebraMap K[X] (RatFunc K) (X - C α))
        = algebraMap K[X] (RatFunc K) a / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id))
      ↔ ∑ α ∈ s, a.eval α / (Differential.implicitDeriv (C b * X) (Lagrange.nodal s id)).eval α = 0 := by
  -- residue sum = (cancel sum) + a/d, so `residue sum = a/d ↔ cancel sum = 0`
  rw [monomial_residue_sum_eq_cancel_add s a (C b * X) hA hnorm]
  -- `cancelSum + a/d = a/d ↔ cancelSum = 0` (additive cancellation in the field `RatFunc K`)
  have hcancel_iff : ∀ x y : RatFunc K, (x + y = y) ↔ (x = 0) := fun x y =>
    ⟨fun h => add_right_cancel (b := y) (by rw [h, zero_add]), fun h => by rw [h, zero_add]⟩
  rw [hcancel_iff]
  -- the cancel sum vanishes ⟺ `∑ c_α = 0` (`hyperexp_cancel_iff_sum_zero`, `c_α` the RT residue)
  exact hyperexp_cancel_iff_sum_zero s b hb
    (fun α => a.eval α / (Differential.implicitDeriv (C b * X) (Lagrange.nodal s id)).eval α)

/-- **★ The list↔Finset bridge for the hyperexp residue match (given `∑c = 0`)** — for a squarefree
`d = ∏_{α∈s}(t−α)`, `deg a < #s`, a hyperexponential monomial `Dt = C b·X` (`b = η′ ≠ 0`), every root normal,
**and** the integrability witness `hsum : ∑_α c_α = 0`, the engine-shaped **`List` sum** over the per-root
list `s.toList.map (fun α => (c_α, X − C α))` of `C(c_α)·(D(t−α)/(t−α))` equals `a/d` over `RatFunc K`. The
`List`-form of `hyperexp_residue_match_iff_sum_zero.mpr`: the per-root `List.sum` equals the `Finset.sum` over
`s` (`Finset.sum_map_toList`), which the iff (with `hsum`) sends to `a/d`. The residue match in exactly the
`List` shape `logResidueSumG_eq_of_residue_match`'s `hmatch` consumes — for the hyperexp case, GATED on the
integrability witness `∑c = 0` (the precise extra content the primitive case `primitive_residue_match_list`
gets for free). -/
theorem hyperexp_residue_match_list (s : Finset K) (a : K[X]) (b : K) (hb : b ≠ 0)
    (hA : a.degree < s.card) (hnorm : ∀ α ∈ s, (C b * X).eval α ≠ α′)
    (hsum : ∑ α ∈ s, a.eval α / (Differential.implicitDeriv (C b * X) (Lagrange.nodal s id)).eval α
      = 0) :
    ((s.toList.map (fun α =>
          (a.eval α / (Differential.implicitDeriv (C b * X) (Lagrange.nodal s id)).eval α,
            X - C α))).map
        (fun cv =>
          algebraMap K[X] (RatFunc K) (C cv.1)
            * (extendDeriv (Differential.implicitDeriv (C b * X))
                  (algebraMap K[X] (RatFunc K) cv.2)
                / algebraMap K[X] (RatFunc K) cv.2))).sum
      = algebraMap K[X] (RatFunc K) a / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id) := by
  -- collapse `(s.toList.map f).map g = s.toList.map (g ∘ f)`, then to the `Finset.sum` over `s`
  rw [List.map_map, Finset.sum_map_toList]
  -- the per-root summand is exactly the Finset residue sum, sent to `a/d` by the iff with `hsum`
  exact (hyperexp_residue_match_iff_sum_zero s a b hb hA hnorm).mpr hsum

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

/-! ### Task 2 (hyperexp): the list↔Finset bridge + the engine `hmatch`, GATED on `∑c = 0`

The hyperexponential analog of `primitive_residue_match_list_engine` / `primitive_engine_hmatch`. The ONLY
difference from the primitive case is that the RT polynomial-part cancellation is NOT automatic: it is the
integrability witness `∑c = 0` (`hsum`), supplied here as an explicit hypothesis (see the closing status for
why `cIntegrateGFull`'s success cannot supply it). Given `hsum`, the residue match is discharged exactly as in
the primitive case, through `hyperexp_residue_match_list`. -/

/-- **★ The hyperexp list↔Finset bridge in the engine's vocabulary (given `∑c = 0`)** — for a
hyperexponential monomial `toPolyG Dt = C b·X` (`b = η′ ≠ 0`), a squarefree `d = ∏_{β∈s}(t−β)`, `deg a < #s`,
every root normal, **and** the integrability witness `hsum : ∑_β c_β = 0`, the engine-shaped **`List` sum**
over the per-root list of `(c_β, X − C β)` pairs equals `a/d` over `RatFunc (CFieldSpec.K α)`, with
`D = towerFractionFieldDerivG Dt`. The `K[X]`-level `hyperexp_residue_match_list` transported through the
definitional `amG = algebraMap` and the `towerFractionFieldDerivG` unfolding — the residue match in exactly
the `List` shape the engine consumes, hyperexp case (the integrability witness is the only extra content over
the primitive `primitive_residue_match_list_engine`). -/
theorem hyperexp_residue_match_list_engine (Dt : CPolyG α) (s : Finset (CFieldSpec.K α))
    (a : (CFieldSpec.K α)[X]) (b : CFieldSpec.K α) (hb : b ≠ 0) (hDt : toPolyG Dt = C b * X)
    (hA : a.degree < s.card) (hnorm : ∀ β ∈ s, (C b * X).eval β ≠ β′)
    (hsum : ∑ β ∈ s, a.eval β / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β
      = 0) :
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
  rw [hDt] at hsum ⊢
  exact ResidueMatchTower.hyperexp_residue_match_list s a b hb hA hnorm hsum

/-- **★ The hyperexp engine `hmatch`, discharged through the per-root reassembly (given `∑c = 0`)** — for a
hyperexponential monomial `toPolyG Dt = C b·X` (`b = η′ ≠ 0`), a squarefree `hDen` factored as
`∏_{β∈s}(t−β)`, `deg (toPolyG hNum) < #s`, every root normal, the integrability witness
`hsum : ∑_β c_β = 0`, and the engine residue logs `logs` whose `(toK cv.1, toPolyG cv.2)`-images ARE the
per-root list `s.toList.map (fun β => (residue β, X − C β))` (`hform`), the engine residue-match sum
`∑_{(c,v)∈logs} amG(C(toK c))·(D(log v)) = amG(hNum)/amG(hDen)` over `RatFunc (CFieldSpec.K α)`. Rewrites the
engine sum through `hform` into the bridge's per-root form, which `hyperexp_residue_match_list_engine` (with
`hsum`) sends to `hNum/hDen`. The hyperexp analog of `primitive_engine_hmatch`: identical structure, with the
integrability witness `∑c = 0` the only extra hypothesis (the RT cancellation `primitive_cancel` gives the
primitive case for free is, for hyperexp, exactly `hsum`). -/
theorem hyperexp_engine_hmatch (Dt : CPolyG α) (s : Finset (CFieldSpec.K α))
    (hNum hDen : CPolyG α) (b : CFieldSpec.K α) (hb : b ≠ 0) (logs : List (α × CPolyG α))
    (hDt : toPolyG Dt = C b * X)
    (hden : toPolyG hDen = Lagrange.nodal s id)
    (hA : (toPolyG hNum).degree < s.card) (hnorm : ∀ β ∈ s, (C b * X).eval β ≠ β′)
    (hsum : ∑ β ∈ s,
        (toPolyG hNum).eval β / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β
      = 0)
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
  -- now the per-root form of the bridge `hyperexp_residue_match_list_engine` (with the witness `hsum`)
  have hbridge := hyperexp_residue_match_list_engine Dt s (toPolyG hNum) b hb hDt hA hnorm hsum
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

/-! ### Task 3 (hyperexp): the reduced-case field identity for the HYPEREXPONENTIAL case, GATED on `∑c = 0`

The hyperexponential analog of `field_identity_of_cIntegrateReducedG_primitive`: identical assembly, with the
RT residue match supplied by `hyperexp_engine_hmatch` (which needs `hb : b ≠ 0` and the integrability witness
`hsum : ∑c = 0`) instead of `primitive_engine_hmatch` (which discharges the cancellation automatically). -/

/-- **★★ The reduced-case field identity for the HYPEREXPONENTIAL case (given `∑c = 0`)** — for the normal-part
capstone `res = cIntegrateReducedG Dt fuel a d cands` with a hyperexponential monomial `toPolyG Dt = C b·X`
(`b = η′ ≠ 0`), **given** the Hermite half `hherm`, the per-root reassembly `hform` of the residue logs, AND
the integrability witness `hsum` (`∑_β c_β = 0`, the residues of the Hermite leftover summing to zero), the
reduced-case field identity `D(g) + logResidueSumG Dt res.logs = amG a/amG d` holds over `RatFunc
(CFieldSpec.K α)` — **with no engine `checkIdentityG` certificate**. The RT residue match is discharged by
`hyperexp_engine_hmatch` (the polynomial-part cancellation `⟺ ∑c = 0` by `hyperexp_residue_match_iff_sum_zero`,
supplied by `hsum`), composed with `hherm` through `field_identity_of_reducedG_of_residueMatch`. The hyperexp
reduced-case one-shot, gated on the abstract engine inputs PLUS the integrability witness — exactly the extra
content over the primitive case (Bronstein §5.9: a hyperexp normal part is integrable in the log part alone
**iff** `∑c = 0`). -/
theorem field_identity_of_cIntegrateReducedG_hyperexp (Dt : CPolyG α) (fuel : ℕ)
    (a d : CPolyG α) (cands : List α) (s : Finset (CFieldSpec.K α)) (b : CFieldSpec.K α) (hb : b ≠ 0)
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
    (hsum : ∑ β ∈ s, (toPolyG (cHermiteReduceTowerG Dt fuel a d).2.1).eval β
          / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β = 0)
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
    (hyperexp_engine_hmatch Dt s (cHermiteReduceTowerG Dt fuel a d).2.1
      (cHermiteReduceTowerG Dt fuel a d).2.2 b hb
      (CPolyG.cIntegrateReducedG Dt fuel a d cands).logs hDt hden hA hnorm hsum hform)

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

/-! ### ★ The POLYNOMIAL branch of `cIntegrateGFull`: output pin + one-shot

`cIntegrateGFull` splits `f = fₚ + b/dₛ + cₙ/dₙ`, requires `b = 0`, and — when the polynomial part `fₚ` is
**nonzero** — solves `Dqₚ = fₚ` by the poly-Risch-DE oracle `cPolyRischDEG`, then recombines the polynomial
solution `qₚ` with the normal-part rational `gₙ/gₙd` into `(qₚ·gₙd + gₙ)/gₙd`. This is the poly branch, the
companion to the pure-normal branch (`cisZeroG fp = true`) the milestones above cover. We pin its output shape
(`cIntegrateGFull_poly_eq`) and assemble the a-priori soundness one-shot (`cIntegrateGFull_poly_oneShot`),
extending the checker-free `cIntegrateGFull = some res ⟹ D(res) = a/d` from the pure-normal to the polynomial
branch — gated on the poly-Risch-DE frontier `D(qₚ) = fₚ` (`hpoly`, the abstract soundness of the oracle, the
documented residual), the normal-part one-shot (`hnormal`), and the canonical split (`hrecon`). -/

omit [CFieldSpec α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **`cIntegrateGFull` polynomial branch returns the recombined result** — when the special part `b`
vanishes (`cisZeroG b = true`) but the polynomial part `fₚ` does NOT (`cisZeroG fp = false`), and the poly-
Risch-DE oracle succeeds (`cPolyRischDEG Dt fuel [] fp (deg fp + 1) = some qp`), `cIntegrateGFull Dt fuel a d
cands = some ⟨(qₚ·gₙd + gₙ, gₙd), nrm.logs⟩` with `nrm = cIntegrateReducedG Dt fuel cₙ dₙ cands` and
`(gₙ, gₙd) = nrm.rational`. Pins the driver's output shape on the poly branch: the rational part recombines
the oracle solution `qₚ` with the normal-part rational over the shared denominator `gₙd`. -/
theorem cIntegrateGFull_poly_eq (Dt : CPolyG α) (fuel : ℕ) (a d : CPolyG α) (cands : List α)
    (qp : CPolyG α)
    (hb : CPolyG.cisZeroG (canonicalRepresentationFastG Dt fuel a d).2.1.1 = true)
    (hfp : CPolyG.cisZeroG (canonicalRepresentationFastG Dt fuel a d).1 = false)
    (hqp : CPolyG.cPolyRischDEG Dt fuel [] (canonicalRepresentationFastG Dt fuel a d).1
        ((CPolyG.cdegG (canonicalRepresentationFastG Dt fuel a d).1 : ℤ) + 1) = some qp) :
    CPolyG.cIntegrateGFull Dt fuel a d cands
      = some ⟨(CPolyG.caddG (CPolyG.cmulG qp
              (CPolyG.cIntegrateReducedG Dt fuel (canonicalRepresentationFastG Dt fuel a d).2.2.1
                (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands).rational.2)
            (CPolyG.cIntegrateReducedG Dt fuel (canonicalRepresentationFastG Dt fuel a d).2.2.1
                (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands).rational.1,
          (CPolyG.cIntegrateReducedG Dt fuel (canonicalRepresentationFastG Dt fuel a d).2.2.1
              (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands).rational.2),
        (CPolyG.cIntegrateReducedG Dt fuel (canonicalRepresentationFastG Dt fuel a d).2.2.1
            (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands).logs⟩ := by
  rw [CPolyG.cIntegrateGFull]
  -- destructure the canonical split so the pattern-match `let`s reduce; rewrite the field facts to components
  rcases hcrep : canonicalRepresentationFastG Dt fuel a d with ⟨fp, ⟨b, ds⟩, ⟨cn, dn⟩⟩
  rw [hcrep] at hb hfp hqp
  simp only [hb, hfp, hqp, if_true, if_neg (by decide : ¬ (false = true))]

/-- **★★★ The POLYNOMIAL one-shot for `cIntegrateGFull`, a-priori soundness** — when the driver returns
`some res` on the polynomial branch (`cisZeroG b = true`, `cisZeroG fp = false`, the poly-Risch-DE oracle
returning `some qp`), the field-level antiderivative identity `D(res) + logResidueSumG Dt res.logs = amG
a/amG d` holds over `RatFunc (CFieldSpec.K α)`, **given**: the poly-Risch-DE frontier `hpoly` (`D(amG qₚ) =
amG fₚ`, the abstract soundness of `cPolyRischDEG`), the normal-part one-shot `hnormal` (`D(gₙ/gₙd) +
logResidueSumG nrm.logs = amG cₙ/amG dₙ`), the split reconstruction `hrecon` (`amG fₚ + amG cₙ/amG dₙ = amG
a/amG d`, the `b = fs = 0` case of `canonicalRepresentationFastG_reconstructs`), and `hgden : amG gₙd ≠ 0`.
Pins `res` via `cIntegrateGFull_poly_eq`, reads the recombined rational `(qₚ·gₙd + gₙ)/gₙd = amG qₚ + gₙ/gₙd`
(field algebra), splits `D` (`Derivation.map_add`), and chains `hpoly`/`hnormal`/`hrecon`. The checker-free
`cIntegrateGFull = some res ⟹ D(res) = a/d` for the poly branch, gated on the documented poly-Risch-DE
residual `hpoly`. -/
theorem cIntegrateGFull_poly_oneShot (Dt : CPolyG α) (fuel : ℕ) (a d : CPolyG α) (cands : List α)
    (res : IntegralResultG α) (qp : CPolyG α)
    (hb : CPolyG.cisZeroG (canonicalRepresentationFastG Dt fuel a d).2.1.1 = true)
    (hfp : CPolyG.cisZeroG (canonicalRepresentationFastG Dt fuel a d).1 = false)
    (hsome : CPolyG.cIntegrateGFull Dt fuel a d cands = some res)
    (hqp : CPolyG.cPolyRischDEG Dt fuel [] (canonicalRepresentationFastG Dt fuel a d).1
        ((CPolyG.cdegG (canonicalRepresentationFastG Dt fuel a d).1 : ℤ) + 1) = some qp)
    (hgden : amG α (toPolyG (CPolyG.cIntegrateReducedG Dt fuel
          (canonicalRepresentationFastG Dt fuel a d).2.2.1
          (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands).rational.2) ≠ 0)
    (hpoly : towerFractionFieldDerivG Dt (amG α (toPolyG qp)) = amG α (toPolyG
        (canonicalRepresentationFastG Dt fuel a d).1))
    (hnormal : towerFractionFieldDerivG Dt
            (amG α (toPolyG (CPolyG.cIntegrateReducedG Dt fuel
                  (canonicalRepresentationFastG Dt fuel a d).2.2.1
                  (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands).rational.1)
              / amG α (toPolyG (CPolyG.cIntegrateReducedG Dt fuel
                  (canonicalRepresentationFastG Dt fuel a d).2.2.1
                  (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands).rational.2))
          + logResidueSumG Dt (CPolyG.cIntegrateReducedG Dt fuel
              (canonicalRepresentationFastG Dt fuel a d).2.2.1
              (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands).logs
        = amG α (toPolyG (canonicalRepresentationFastG Dt fuel a d).2.2.1)
            / amG α (toPolyG (canonicalRepresentationFastG Dt fuel a d).2.2.2))
    (hrecon : amG α (toPolyG (canonicalRepresentationFastG Dt fuel a d).1)
          + amG α (toPolyG (canonicalRepresentationFastG Dt fuel a d).2.2.1)
            / amG α (toPolyG (canonicalRepresentationFastG Dt fuel a d).2.2.2)
        = amG α (toPolyG a) / amG α (toPolyG d)) :
    towerFractionFieldDerivG Dt (amG α (toPolyG res.rational.1) / amG α (toPolyG res.rational.2))
        + logResidueSumG Dt res.logs
      = amG α (toPolyG a) / amG α (toPolyG d) := by
  -- pin the output: `res` is the recombined poly-branch result
  have hres : res = ⟨(CPolyG.caddG (CPolyG.cmulG qp
            (CPolyG.cIntegrateReducedG Dt fuel (canonicalRepresentationFastG Dt fuel a d).2.2.1
              (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands).rational.2)
          (CPolyG.cIntegrateReducedG Dt fuel (canonicalRepresentationFastG Dt fuel a d).2.2.1
              (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands).rational.1,
        (CPolyG.cIntegrateReducedG Dt fuel (canonicalRepresentationFastG Dt fuel a d).2.2.1
            (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands).rational.2),
      (CPolyG.cIntegrateReducedG Dt fuel (canonicalRepresentationFastG Dt fuel a d).2.2.1
          (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands).logs⟩ := by
    rw [cIntegrateGFull_poly_eq Dt fuel a d cands qp hb hfp hqp] at hsome
    exact (Option.some.injEq _ _ ▸ hsome).symm
  subst hres
  -- abbreviations for the normal-part capstone's rational part
  set gnum := (CPolyG.cIntegrateReducedG Dt fuel (canonicalRepresentationFastG Dt fuel a d).2.2.1
      (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands).rational.1 with hgnumE
  set gden := (CPolyG.cIntegrateReducedG Dt fuel (canonicalRepresentationFastG Dt fuel a d).2.2.1
      (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands).rational.2 with hgdenE
  -- read the recombined rational `(qₚ·gden + gnum)/gden = amG qₚ + gnum/gden` (field algebra)
  have hnewrat : amG α (toPolyG (CPolyG.caddG (CPolyG.cmulG qp gden) gnum)) / amG α (toPolyG gden)
      = amG α (toPolyG qp) + amG α (toPolyG gnum) / amG α (toPolyG gden) := by
    rw [toPolyG_caddG, toPolyG_cmulG, map_add, map_mul, add_div, mul_div_assoc, div_self hgden,
      mul_one]
  -- D of the recombined rational, split by the derivation: `D(amG qₚ + gnum/gden) = D(amG qₚ) + D(gnum/gden)`
  rw [hnewrat, map_add, hpoly]
  -- regroup and chain `hnormal` (normal one-shot) then `hrecon` (split)
  rw [add_assoc, hnormal, hrecon]

/-! ### ★★★ The POLYNOMIAL one-shot with the poly-RDE frontier `hpoly` DISCHARGED (primitive base)

`cIntegrateGFull_poly_oneShot` is gated on `hpoly` (`D(amG qₚ) = amG fₚ`, the poly-Risch-DE oracle
soundness). For the **primitive base** `Dt = [CField.one]` that gate is now a *theorem*, not a hypothesis:
the `b = []` branch integrates `fₚ` by the term-by-term `cIntegratePolyG`
(`cPolyRischDEG_nil_eq` ⟹ `qₚ = cIntegratePolyG fₚ`), whose field-level antiderivative identity is
`towerFractionFieldDerivG_amG_cIntegratePolyG_const` over a constant base. The remaining condition is
exactly `mapCoeffs (toPolyG fₚ) = 0` (the integrand's coefficients differential-constant), supplied by
the integrand-keyed `cPolyRischDEG_nil_field_identity` route (`cIntegratePolyG_const_coeff`). The other
gates (`hnormal`, `hrecon`, `hgden`) are the separate engine-bridge / canonical-split frontier and stay
as hypotheses. **Boundary**: only `Dt = [CField.one]` — for a general monomial the `b = []` branch is
unreachable (term-by-term integration inverts `D(tⁱ) = i·tⁱ⁻¹` only when `D(t) = 1`). -/

/-- **★★★ The POLYNOMIAL one-shot for `cIntegrateGFull` with `hpoly` discharged (primitive base)** —
over the primitive monomial `Dt = [CField.one]`, if the driver returns `some res` on the polynomial
branch (`cisZeroG b = true`, `cisZeroG fp = false`, the poly-Risch-DE oracle returning `some qp`) and the
polynomial part is over a **constant base** (`hconst : mapCoeffs (toPolyG fp) = 0`), then the field-level
antiderivative identity `D(res) + logResidueSumG res.logs = amG a/amG d` holds — the poly-Risch-DE gate
`hpoly` of `cIntegrateGFull_poly_oneShot` is now **proven**, not assumed. Discharges `hpoly` by pinning
`qp = cIntegratePolyG fp` (`cPolyRischDEG_nil_eq`) and applying the abstract polynomial field one-shot
`towerFractionFieldDerivG_amG_cIntegratePolyG_const` (with the constant-base transport
`cIntegratePolyG_const_coeff`). The engine-bridge / split gates (`hnormal`, `hrecon`, `hgden`) remain as
the separate frontier. Checker-free, no `native_decide`. -/
theorem cIntegrateGFull_poly_oneShot_base [CharZero (CFieldSpec.K α)]
    (fuel : ℕ) (a d : CPolyG α) (cands : List α)
    (res : IntegralResultG α) (qp : CPolyG α)
    (hb : CPolyG.cisZeroG (canonicalRepresentationFastG ([CField.one] : CPolyG α) fuel a d).2.1.1
        = true)
    (hfp : CPolyG.cisZeroG (canonicalRepresentationFastG ([CField.one] : CPolyG α) fuel a d).1
        = false)
    (hsome : CPolyG.cIntegrateGFull ([CField.one] : CPolyG α) fuel a d cands = some res)
    (hqp : CPolyG.cPolyRischDEG ([CField.one] : CPolyG α) fuel []
        (canonicalRepresentationFastG ([CField.one] : CPolyG α) fuel a d).1
        ((CPolyG.cdegG (canonicalRepresentationFastG ([CField.one] : CPolyG α) fuel a d).1 : ℤ) + 1)
        = some qp)
    (hgden : amG α (toPolyG (CPolyG.cIntegrateReducedG ([CField.one] : CPolyG α) fuel
          (canonicalRepresentationFastG ([CField.one] : CPolyG α) fuel a d).2.2.1
          (canonicalRepresentationFastG ([CField.one] : CPolyG α) fuel a d).2.2.2 cands).rational.2)
        ≠ 0)
    (hconst : Differential.mapCoeffs
        (toPolyG (canonicalRepresentationFastG ([CField.one] : CPolyG α) fuel a d).1) = 0)
    (hnormal : towerFractionFieldDerivG ([CField.one] : CPolyG α)
            (amG α (toPolyG (CPolyG.cIntegrateReducedG ([CField.one] : CPolyG α) fuel
                  (canonicalRepresentationFastG ([CField.one] : CPolyG α) fuel a d).2.2.1
                  (canonicalRepresentationFastG ([CField.one] : CPolyG α) fuel a d).2.2.2
                  cands).rational.1)
              / amG α (toPolyG (CPolyG.cIntegrateReducedG ([CField.one] : CPolyG α) fuel
                  (canonicalRepresentationFastG ([CField.one] : CPolyG α) fuel a d).2.2.1
                  (canonicalRepresentationFastG ([CField.one] : CPolyG α) fuel a d).2.2.2
                  cands).rational.2))
          + logResidueSumG ([CField.one] : CPolyG α) (CPolyG.cIntegrateReducedG
              ([CField.one] : CPolyG α) fuel
              (canonicalRepresentationFastG ([CField.one] : CPolyG α) fuel a d).2.2.1
              (canonicalRepresentationFastG ([CField.one] : CPolyG α) fuel a d).2.2.2 cands).logs
        = amG α (toPolyG (canonicalRepresentationFastG ([CField.one] : CPolyG α) fuel a d).2.2.1)
            / amG α (toPolyG (canonicalRepresentationFastG ([CField.one] : CPolyG α) fuel a d).2.2.2))
    (hrecon : amG α (toPolyG (canonicalRepresentationFastG ([CField.one] : CPolyG α) fuel a d).1)
          + amG α (toPolyG (canonicalRepresentationFastG ([CField.one] : CPolyG α) fuel a d).2.2.1)
            / amG α (toPolyG (canonicalRepresentationFastG ([CField.one] : CPolyG α) fuel a d).2.2.2)
        = amG α (toPolyG a) / amG α (toPolyG d)) :
    towerFractionFieldDerivG ([CField.one] : CPolyG α)
        (amG α (toPolyG res.rational.1) / amG α (toPolyG res.rational.2))
        + logResidueSumG ([CField.one] : CPolyG α) res.logs
      = amG α (toPolyG a) / amG α (toPolyG d) := by
  -- the oracle output is exactly `cIntegratePolyG fp` (the `b = []` integration branch)
  set fp := (canonicalRepresentationFastG ([CField.one] : CPolyG α) fuel a d).1 with hfpE
  have hqp_eq : qp = CPolyG.cIntegratePolyG fp := by
    rw [cPolyRischDEG_nil_eq ([CField.one] : CPolyG α) fuel fp ((CPolyG.cdegG fp : ℤ) + 1) hfp
      (le_refl _)] at hqp
    exact (Option.some.injEq _ _ ▸ hqp).symm
  -- discharge `hpoly` via the abstract polynomial field one-shot over the constant base
  have hpoly : towerFractionFieldDerivG ([CField.one] : CPolyG α) (amG α (toPolyG qp))
      = amG α (toPolyG fp) := by
    rw [hqp_eq]
    exact towerFractionFieldDerivG_amG_cIntegratePolyG_const fp
      (cIntegratePolyG_const_coeff fp hconst)
  exact cIntegrateGFull_poly_oneShot ([CField.one] : CPolyG α) fuel a d cands res qp hb hfp hsome
    hqp hgden hpoly hnormal hrecon

/-! ### ★★★ Task 3 milestone: the HYPEREXPONENTIAL one-shot for `cIntegrateGFull`, GATED on `∑c = 0`

The hyperexponential analog of `cIntegrateGFull_primitive_oneShot`: `cIntegrateGFull = some res` on the
pure-normal branch ⟹ `D(res) = a/d`, for a hyperexponential monomial `Dt = η′·t`. The ONLY extra hypothesis
over the primitive milestone is the integrability witness `hsum : ∑c = 0` — discharging the general-case
`hcancel` for hyperexp via `hyperexp_residue_match_iff_sum_zero` inside `hyperexp_engine_hmatch`.

★ WHY `hsum` IS NEEDED (the precise obstruction). `cIntegrateGFull`'s pure-normal branch returns `some nrm`
**UNCONDITIONALLY** (`cIntegrateGFull_pureNormal_eq` — no `none` exit, no integrability check). It does NOT do
the Bronstein §5.9 residual feedback (that lives in the SEPARATE driver `cIntegrateHyperexpFullG`, which
overshoots by `R = η·∑c` and absorbs it into `∫R`). So for `cIntegrateGFull` on a hyperexp input, `D(res) =
a/d` holds **iff** `∑c = 0` (`hyperexp_residue_match_iff_sum_zero`), and when `∑c ≠ 0` the driver STILL returns
`some res` but `D(res) ≠ a/d` (`checkIdentityG = false`, witnessed by `ComputableHyperexpNormal`'s
`nNormInv_reduced_overshoots`). Hence "engine returns `some` ⟹ `∑c = 0`" is **FALSE** for `cIntegrateGFull`,
and the hyperexp one-shot is GENUINELY conditional on the integrability witness `hsum` — not derivable from
engine success. The full unconditional story requires routing through `cIntegrateHyperexpFullG` (a different,
larger soundness task), whose success encodes `∫R` solvability, NOT `∑c = 0`. -/

/-- **★★★ The HYPEREXPONENTIAL one-shot for `cIntegrateGFull` (pure-normal branch), checker-free, GATED on
`∑c = 0`** — for a hyperexponential monomial `toPolyG Dt = C b·X` (`b = η′ ≠ 0`), if the driver returns
`some res` on the pure-normal branch (`cisZeroG b = true`, `cisZeroG fp = true`), **given** the canonical
reconstruction `hrecon`, the Hermite half `hherm`, the per-root reassembly `hform`, AND the integrability
witness `hsum` (`∑c = 0`, the residues of the Hermite leftover summing to zero), the field-level
antiderivative identity `D(res) + logResidueSumG Dt res.logs = amG a/amG d` holds over `RatFunc (CFieldSpec.K
α)` — **with no engine `checkIdentityG` certificate, no native_decide**. The hyperexp analog of
`cIntegrateGFull_primitive_oneShot`: identical assembly through `cIntegrateGFull_pureNormal_eq` +
`field_identity_of_cIntegrateReducedG_hyperexp` + `hrecon`, with `hsum` the only extra input. The integrability
witness is NOT a free identity nor an engine-success consequence (see the section docstring): the hyperexp
one-shot for `cIntegrateGFull` is GENUINELY conditional on `∑c = 0`. The milestone extending the checker-free
one-shot from the primitive to the exponential case — the two main transcendental monomial kinds — modulo the
documented integrability witness. -/
theorem cIntegrateGFull_hyperexp_oneShot (Dt : CPolyG α) (fuel : ℕ) (a d : CPolyG α)
    (cands : List α) (res : IntegralResultG α) (s : Finset (CFieldSpec.K α)) (b : CFieldSpec.K α)
    (hb : b ≠ 0) (hDt : toPolyG Dt = C b * X)
    (hbz : CPolyG.cisZeroG (canonicalRepresentationFastG Dt fuel a d).2.1.1 = true)
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
    (hnorm : ∀ β ∈ s, (C b * X).eval β ≠ β′)
    (hsum : ∑ β ∈ s, (toPolyG (cHermiteReduceTowerG Dt fuel
            (canonicalRepresentationFastG Dt fuel a d).2.2.1
            (canonicalRepresentationFastG Dt fuel a d).2.2.2).2.1).eval β
          / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β = 0)
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
  -- pin the output: `res` is the reduced capstone on the simple part `(cₙ, dₙ)` (same as the primitive case)
  have hres : res = CPolyG.cIntegrateReducedG Dt fuel (canonicalRepresentationFastG Dt fuel a d).2.2.1
      (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands := by
    rw [cIntegrateGFull_pureNormal_eq Dt fuel a d cands hbz hfp] at hsome
    exact (Option.some.injEq _ _ ▸ hsome).symm
  subst hres
  -- the hyperexp reduced-case identity (with `hsum`) gives `D(g) + logResidueSumG = amG cₙ/amG dₙ`; `hrecon` closes
  rw [field_identity_of_cIntegrateReducedG_hyperexp Dt fuel
    (canonicalRepresentationFastG Dt fuel a d).2.2.1
    (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands s b hb hDt hherm hden hA hnorm hsum hform]
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

/-- **★★★ The HYPEREXPONENTIAL one-shot for `cIntegrateGFull` over `ℚ(x)(t)` (GATED on `∑c = 0`)** — the
milestone at the level-1 carrier `α = QFunNZG ℚ` (`CFieldSpec.K (QFunNZG ℚ) = RatFunc ℚ`): for a
hyperexponential monomial `toPolyG Dt = C b·X` (`b = η′ ≠ 0`), if the driver returns `some res` on the
pure-normal branch, given the canonical reconstruction, the Hermite half, the per-root reassembly, AND the
integrability witness `hsum` (`∑c = 0`), the field-level identity `D(res) + logResidueSumG Dt res.logs = amG
a/amG d` holds over `RatFunc ℚ` — **checker-free, no native_decide**. The concrete hyperexp one-shot at
ℚ(x)(t), gated on the abstract engine inputs PLUS the integrability witness (which `cIntegrateGFull`'s success
does NOT supply — see the section docstring). The `QFunNZG ℚ` instance of `cIntegrateGFull_hyperexp_oneShot`. -/
theorem cIntegrateGFull_hyperexp_oneShot_qfunNZG (Dt : CPolyG (QFunNZG ℚ)) (fuel : ℕ)
    (a d : CPolyG (QFunNZG ℚ)) (cands : List (QFunNZG ℚ)) (res : IntegralResultG (QFunNZG ℚ))
    (s : Finset (CFieldSpec.K (QFunNZG ℚ))) (b : CFieldSpec.K (QFunNZG ℚ))
    (hb : b ≠ 0) (hDt : toPolyG Dt = C b * X)
    (hbz : CPolyG.cisZeroG (canonicalRepresentationFastG Dt fuel a d).2.1.1 = true)
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
    (hnorm : ∀ β ∈ s, (C b * X).eval β ≠ β′)
    (hsum : ∑ β ∈ s, (toPolyG (cHermiteReduceTowerG Dt fuel
            (canonicalRepresentationFastG Dt fuel a d).2.2.1
            (canonicalRepresentationFastG Dt fuel a d).2.2.2).2.1).eval β
          / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β = 0)
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
  cIntegrateGFull_hyperexp_oneShot Dt fuel a d cands res s b hb hDt hbz hfp hsome hrecon hherm hden hA
    hnorm hsum hform

/-! ### Restatements against the intended wording (anonymous `example`s) -/

-- ★ THE POLY-BRANCH OUTPUT PIN: on the poly branch (`b = 0`, `fp ≠ 0`, oracle returns `some qp`),
-- `cIntegrateGFull` returns the recombined `((qₚ·gₙd + gₙ, gₙd), nrm.logs)`.
example (Dt : CPolyG α) (fuel : ℕ) (a d : CPolyG α) (cands : List α) (qp : CPolyG α)
    (hb : CPolyG.cisZeroG (canonicalRepresentationFastG Dt fuel a d).2.1.1 = true)
    (hfp : CPolyG.cisZeroG (canonicalRepresentationFastG Dt fuel a d).1 = false)
    (hqp : CPolyG.cPolyRischDEG Dt fuel [] (canonicalRepresentationFastG Dt fuel a d).1
        ((CPolyG.cdegG (canonicalRepresentationFastG Dt fuel a d).1 : ℤ) + 1) = some qp) :
    CPolyG.cIntegrateGFull Dt fuel a d cands
      = some ⟨(CPolyG.caddG (CPolyG.cmulG qp
              (CPolyG.cIntegrateReducedG Dt fuel (canonicalRepresentationFastG Dt fuel a d).2.2.1
                (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands).rational.2)
            (CPolyG.cIntegrateReducedG Dt fuel (canonicalRepresentationFastG Dt fuel a d).2.2.1
                (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands).rational.1,
          (CPolyG.cIntegrateReducedG Dt fuel (canonicalRepresentationFastG Dt fuel a d).2.2.1
              (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands).rational.2),
        (CPolyG.cIntegrateReducedG Dt fuel (canonicalRepresentationFastG Dt fuel a d).2.2.1
            (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands).logs⟩ :=
  cIntegrateGFull_poly_eq Dt fuel a d cands qp hb hfp hqp

-- ★★★ THE POLY-BRANCH ONE-SHOT (a-priori soundness, checker-free, no native_decide): on the poly branch,
-- `cIntegrateGFull = some res ⟹ D(res) = a/d`, given the poly-Risch-DE frontier `hpoly` (`D(qₚ) = fₚ`), the
-- normal one-shot `hnormal`, the split `hrecon`, and `hgden`.
example (Dt : CPolyG α) (fuel : ℕ) (a d : CPolyG α) (cands : List α) (res : IntegralResultG α)
    (qp : CPolyG α)
    (hb : CPolyG.cisZeroG (canonicalRepresentationFastG Dt fuel a d).2.1.1 = true)
    (hfp : CPolyG.cisZeroG (canonicalRepresentationFastG Dt fuel a d).1 = false)
    (hsome : CPolyG.cIntegrateGFull Dt fuel a d cands = some res)
    (hqp : CPolyG.cPolyRischDEG Dt fuel [] (canonicalRepresentationFastG Dt fuel a d).1
        ((CPolyG.cdegG (canonicalRepresentationFastG Dt fuel a d).1 : ℤ) + 1) = some qp)
    (hgden : amG α (toPolyG (CPolyG.cIntegrateReducedG Dt fuel
          (canonicalRepresentationFastG Dt fuel a d).2.2.1
          (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands).rational.2) ≠ 0)
    (hpoly : towerFractionFieldDerivG Dt (amG α (toPolyG qp)) = amG α (toPolyG
        (canonicalRepresentationFastG Dt fuel a d).1))
    (hnormal : towerFractionFieldDerivG Dt
            (amG α (toPolyG (CPolyG.cIntegrateReducedG Dt fuel
                  (canonicalRepresentationFastG Dt fuel a d).2.2.1
                  (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands).rational.1)
              / amG α (toPolyG (CPolyG.cIntegrateReducedG Dt fuel
                  (canonicalRepresentationFastG Dt fuel a d).2.2.1
                  (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands).rational.2))
          + logResidueSumG Dt (CPolyG.cIntegrateReducedG Dt fuel
              (canonicalRepresentationFastG Dt fuel a d).2.2.1
              (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands).logs
        = amG α (toPolyG (canonicalRepresentationFastG Dt fuel a d).2.2.1)
            / amG α (toPolyG (canonicalRepresentationFastG Dt fuel a d).2.2.2))
    (hrecon : amG α (toPolyG (canonicalRepresentationFastG Dt fuel a d).1)
          + amG α (toPolyG (canonicalRepresentationFastG Dt fuel a d).2.2.1)
            / amG α (toPolyG (canonicalRepresentationFastG Dt fuel a d).2.2.2)
        = amG α (toPolyG a) / amG α (toPolyG d)) :
    towerFractionFieldDerivG Dt (amG α (toPolyG res.rational.1) / amG α (toPolyG res.rational.2))
        + logResidueSumG Dt res.logs
      = amG α (toPolyG a) / amG α (toPolyG d) :=
  cIntegrateGFull_poly_oneShot Dt fuel a d cands res qp hb hfp hsome hqp hgden hpoly hnormal hrecon

-- ★★★ THE POLY-BRANCH ONE-SHOT WITH `hpoly` DISCHARGED (primitive base `Dt = [1]`, constant base): the
-- poly-Risch-DE gate is now PROVEN from `mapCoeffs (toPolyG fp) = 0`, so the only remaining inputs are the
-- separate engine-bridge / split frontier (`hnormal`, `hrecon`, `hgden`). Checker-free, no native_decide.
example [CharZero (CFieldSpec.K α)]
    (fuel : ℕ) (a d : CPolyG α) (cands : List α) (res : IntegralResultG α) (qp : CPolyG α)
    (hb : CPolyG.cisZeroG (canonicalRepresentationFastG ([CField.one] : CPolyG α) fuel a d).2.1.1
        = true)
    (hfp : CPolyG.cisZeroG (canonicalRepresentationFastG ([CField.one] : CPolyG α) fuel a d).1
        = false)
    (hsome : CPolyG.cIntegrateGFull ([CField.one] : CPolyG α) fuel a d cands = some res)
    (hqp : CPolyG.cPolyRischDEG ([CField.one] : CPolyG α) fuel []
        (canonicalRepresentationFastG ([CField.one] : CPolyG α) fuel a d).1
        ((CPolyG.cdegG (canonicalRepresentationFastG ([CField.one] : CPolyG α) fuel a d).1 : ℤ) + 1)
        = some qp)
    (hgden : amG α (toPolyG (CPolyG.cIntegrateReducedG ([CField.one] : CPolyG α) fuel
          (canonicalRepresentationFastG ([CField.one] : CPolyG α) fuel a d).2.2.1
          (canonicalRepresentationFastG ([CField.one] : CPolyG α) fuel a d).2.2.2 cands).rational.2)
        ≠ 0)
    (hconst : Differential.mapCoeffs
        (toPolyG (canonicalRepresentationFastG ([CField.one] : CPolyG α) fuel a d).1) = 0)
    (hnormal : towerFractionFieldDerivG ([CField.one] : CPolyG α)
            (amG α (toPolyG (CPolyG.cIntegrateReducedG ([CField.one] : CPolyG α) fuel
                  (canonicalRepresentationFastG ([CField.one] : CPolyG α) fuel a d).2.2.1
                  (canonicalRepresentationFastG ([CField.one] : CPolyG α) fuel a d).2.2.2
                  cands).rational.1)
              / amG α (toPolyG (CPolyG.cIntegrateReducedG ([CField.one] : CPolyG α) fuel
                  (canonicalRepresentationFastG ([CField.one] : CPolyG α) fuel a d).2.2.1
                  (canonicalRepresentationFastG ([CField.one] : CPolyG α) fuel a d).2.2.2
                  cands).rational.2))
          + logResidueSumG ([CField.one] : CPolyG α) (CPolyG.cIntegrateReducedG
              ([CField.one] : CPolyG α) fuel
              (canonicalRepresentationFastG ([CField.one] : CPolyG α) fuel a d).2.2.1
              (canonicalRepresentationFastG ([CField.one] : CPolyG α) fuel a d).2.2.2 cands).logs
        = amG α (toPolyG (canonicalRepresentationFastG ([CField.one] : CPolyG α) fuel a d).2.2.1)
            / amG α (toPolyG (canonicalRepresentationFastG ([CField.one] : CPolyG α) fuel a d).2.2.2))
    (hrecon : amG α (toPolyG (canonicalRepresentationFastG ([CField.one] : CPolyG α) fuel a d).1)
          + amG α (toPolyG (canonicalRepresentationFastG ([CField.one] : CPolyG α) fuel a d).2.2.1)
            / amG α (toPolyG (canonicalRepresentationFastG ([CField.one] : CPolyG α) fuel a d).2.2.2)
        = amG α (toPolyG a) / amG α (toPolyG d)) :
    towerFractionFieldDerivG ([CField.one] : CPolyG α)
        (amG α (toPolyG res.rational.1) / amG α (toPolyG res.rational.2))
        + logResidueSumG ([CField.one] : CPolyG α) res.logs
      = amG α (toPolyG a) / amG α (toPolyG d) :=
  cIntegrateGFull_poly_oneShot_base fuel a d cands res qp hb hfp hsome hqp hgden hconst hnormal hrecon

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

-- ★★★ THE HYPEREXP MILESTONE at `α = QFunNZG ℚ` (checker-free, no native_decide, GATED on `∑c = 0`):
-- `cIntegrateGFull = some res ⟹ D(res) = a/d` over `RatFunc ℚ` for a hyperexp `Dt = η′·t` (`toPolyG Dt =
-- C b·X`, `b ≠ 0`), given the abstract engine inputs PLUS the integrability witness `hsum` (`∑c = 0`). The
-- one-shot now covers PRIMITIVE and EXPONENTIAL — modulo the witness, which `cIntegrateGFull`'s success does
-- NOT supply (it returns `some` even when `∑c ≠ 0`; the §5.9 feedback lives in `cIntegrateHyperexpFullG`).
example (Dt : CPolyG (QFunNZG ℚ)) (fuel : ℕ) (a d : CPolyG (QFunNZG ℚ)) (cands : List (QFunNZG ℚ))
    (res : IntegralResultG (QFunNZG ℚ)) (s : Finset (CFieldSpec.K (QFunNZG ℚ)))
    (b : CFieldSpec.K (QFunNZG ℚ)) (hb : b ≠ 0) (hDt : toPolyG Dt = C b * X)
    (hbz : CPolyG.cisZeroG (canonicalRepresentationFastG Dt fuel a d).2.1.1 = true)
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
    (hnorm : ∀ β ∈ s, (C b * X).eval β ≠ β′)
    (hsum : ∑ β ∈ s, (toPolyG (cHermiteReduceTowerG Dt fuel
            (canonicalRepresentationFastG Dt fuel a d).2.2.1
            (canonicalRepresentationFastG Dt fuel a d).2.2.2).2.1).eval β
          / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β = 0)
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
  cIntegrateGFull_hyperexp_oneShot_qfunNZG Dt fuel a d cands res s b hb hDt hbz hfp hsome hrecon hherm
    hden hA hnorm hsum hform

/-! ### ★ Status — the PRIMITIVE and HYPEREXPONENTIAL `cIntegrateGFull` one-shots, axiom-clean

PROVEN (axiom-clean `[propext, Classical.choice, Quot.sound]`, **no** `native_decide`, **no** `sorry`):
* **The list↔Finset bridge** (`primitive_residue_match_list` / `…_engine`) — the engine-shaped `List.sum`
  over the per-root list IS the proven Finset residue match, via `Finset.sum_map_toList`.
* **The primitive engine `hmatch`** (`primitive_engine_hmatch`) — discharges the engine's RT residue-match
  hypothesis for the primitive case, given the per-root reassembly `hform`. The RT polynomial-part
  cancellation is AUTOMATIC (`ResidueMatchTower.primitive_cancel`), so the primitive regime needs **no
  integrability witness**.
* **The PRIMITIVE one-shot** (`field_identity_of_cIntegrateReducedG_primitive`,
  `cIntegrateGFull_primitive_oneShot` / `…_qfunNZG`) — for the primitive pure-normal branch,
  `cIntegrateGFull = some res ⟹ D(res) = a/d`, checker-free, gated only on the abstract engine inputs
  (canonical reconstruction `hrecon`, Hermite half `hherm`, per-root reassembly `hform`).
* **★★ NEW — the HYPEREXPONENTIAL one-shot** (`field_identity_of_cIntegrateReducedG_hyperexp`,
  `cIntegrateGFull_hyperexp_oneShot` / `…_qfunNZG`), built on:
  - **`monomial_residue_sum_eq_cancel_add`** — the UNCONDITIONAL decomposition `residue sum = (cancel sum) +
    a/d` for any monomial (the body of `monomial_residue_match_of_cancel` before its `hcancel` rewrite).
  - **`hyperexp_residue_match_iff_sum_zero`** — for `v = C b·X` (`b = η′ ≠ 0`) the residue match `= a/d`
    holds **iff** `∑c_α = 0` (decomposition + `hyperexp_cancel_iff_sum_zero`).
  - **`hyperexp_engine_hmatch`** / **`hyperexp_residue_match_list_engine`** — the engine `hmatch`, hyperexp
    case, discharged given `hform` AND the integrability witness `hsum : ∑c = 0`.

  So `cIntegrateGFull = some res ⟹ D(res) = a/d` for a hyperexp `Dt = η′·t` (`toPolyG Dt = C b·X`),
  checker-free, gated on the abstract engine inputs PLUS `hsum`. **The checker-free one-shot now covers the
  PRIMITIVE and EXPONENTIAL cases — the two main transcendental monomial kinds — modulo the integrability
  witness for the exponential case.**

★ IS THE HYPEREXP ONE-SHOT UNCONDITIONAL? **NO — and this is a genuine mathematical obstruction, not a missing
lemma.** The task hoped "engine returns `some` on a hyperexp input ⟹ `∑c = 0` (discharging `hcancel`
unconditionally)". That implication is **FALSE for `cIntegrateGFull`**, for a precise reason:

  `cIntegrateGFull`'s pure-normal branch returns `some nrm = some (cIntegrateReducedG …)` **UNCONDITIONALLY**
  (`cIntegrateGFull_pureNormal_eq` — no `none` exit, no integrability test). It does **not** perform the
  Bronstein §5.9 residual feedback: it emits the raw §5.6 Rothstein–Trager logs, which **overshoot** a
  hyperexp normal part by `R = η·∑c` (the `extendDeriv_logPart_eq_div_add_residual` leftover). Hence for
  `cIntegrateGFull` on a hyperexp input, `D(res) = a/d` ⟺ the overshoot vanishes ⟺ `∑c = 0`
  (`hyperexp_residue_match_iff_sum_zero`); when `∑c ≠ 0` the driver STILL returns `some res` but `D(res) ≠
  a/d`. This is not hypothetical — `ComputableHyperexpNormal`'s `nNormInv_reduced_overshoots` is a
  `native_decide` witness: on `f = 1/(exp x − 1)` the plain reduced driver returns a result with
  `checkIdentityG = false`. Therefore "success ⟹ `∑c = 0`" cannot hold, and the hyperexp one-shot for
  `cIntegrateGFull` is **genuinely conditional on the integrability witness `hsum`** — it is the strongest
  TRUE statement of this form for this driver.

  Where does the §5.9 correction live? In the SEPARATE driver `cIntegrateHyperexpFullG`
  (`ComputableHyperexpNormal`/`…Special`), which integrates the overshoot `∫R` and subtracts it
  (`∫fₙ = logPart − ∫R`). Its success condition is `∫R` SOLVABLE — the OPPOSITE of `∑c = 0` (it succeeds
  precisely when `∑c ≠ 0` is *absorbable*). So no engine-success fact, on EITHER driver, supplies `∑c = 0`:
  the integrability-in-the-log-part-alone condition `∑c = 0` is a genuine SIDE CONDITION on the integrand, not
  a consequence of the algorithm terminating. The fully unconditional hyperexp soundness is the SEPARATE
  result `cIntegrateHyperexpFullG = some res ⟹ D(res) = a/d` (whose abstract proof needs the §5.9 residual
  identity `extendDeriv_logPart_eq_div_add_residual` — currently a docstring claim, not a lemma — plus the
  base-RDE-oracle soundness for `∫R`); a larger task, NOT a discharge of `hcancel`.

The hypertangent case is analogous with `v = C b·X² + …` (the polynomial parts are no longer α-independent, so
the cancel sum is a different — still integrability-equivalent — condition).

★★ NEW — the POLYNOMIAL branch a-priori soundness (`cIntegrateGFull_poly_eq`, `cIntegrateGFull_poly_oneShot`,
axiom-clean `[propext, choice, Quot.sound]`, **no** `native_decide`). The companion to the pure-normal branch:
when the polynomial part `fₚ ≠ 0`, the driver solves `Dqₚ = fₚ` by the poly-Risch-DE oracle and recombines
`qₚ + gₙ/gₙd`. `cIntegrateGFull_poly_eq` pins the recombined output `((qₚ·gₙd + gₙ, gₙd), nrm.logs)`;
`cIntegrateGFull_poly_oneShot` gives `cIntegrateGFull = some res ⟹ D(res) = a/d`, gated on the poly-Risch-DE
FRONTIER `hpoly` (`D(amG qₚ) = amG fₚ`, the abstract soundness of `cPolyRischDEG` — the documented residual,
NOT yet a lemma; its concrete forms live in `ComputableOneShotSoundness`'s `field_identity_of_cPolyRischDEG`),
the normal-part one-shot `hnormal`, and the split reconstruction `hrecon`. The proof reads the recombined
rational `(qₚ·gₙd + gₙ)/gₙd = amG qₚ + gₙ/gₙd` (field algebra via `toPolyG_caddG`/`toPolyG_cmulG` + `(x·z +
y)/z = x + y/z`), splits `D` by `Derivation.map_add`, then chains `hpoly`/`hnormal`/`hrecon`.

★ THE GENERAL ONE-SHOT (Target 3, deferred — shape only). A single `cIntegrateGFull = some res ⟹ D(res) =
a/d` covering BOTH branches is a `cisZeroG fp` case split: `true` → `cIntegrateGFull_primitive_oneShot` (or its
hyperexp sibling), `false` → `cIntegrateGFull_poly_oneShot`. It is NOT a clean additive theorem: the two
branches consume structurally DIFFERENT hypothesis bundles (the pure-normal milestones fold the normal
one-shot into Hermite `hherm` + per-root reassembly `hform` + reconstruction `hrecon`; the poly branch takes
the normal one-shot `hnormal` directly with a different split `hrecon`), so a combined statement must carry the
UNION of both bundles while each branch uses only its half — heavy plumbing for no new mathematical content.
Both per-branch one-shots are the citable facts; the general form is mechanical given a caller's chosen
hypotheses. -/

#print axioms ResidueMatchTower.primitive_residue_match_list
#print axioms primitive_residue_match_list_engine
#print axioms primitive_engine_hmatch
#print axioms field_identity_of_cIntegrateReducedG_primitive
#print axioms cIntegrateGFull_primitive_oneShot
#print axioms cIntegrateGFull_primitive_oneShot_qfunNZG
#print axioms ResidueMatchTower.hyperexp_cancel_iff_sum_zero
#print axioms ResidueMatchTower.monomial_residue_sum_eq_cancel_add
#print axioms ResidueMatchTower.hyperexp_residue_match_iff_sum_zero
#print axioms hyperexp_engine_hmatch
#print axioms field_identity_of_cIntegrateReducedG_hyperexp
#print axioms cIntegrateGFull_hyperexp_oneShot
#print axioms cIntegrateGFull_hyperexp_oneShot_qfunNZG
#print axioms cIntegrateGFull_poly_eq
#print axioms cIntegrateGFull_poly_oneShot
#print axioms cIntegrateGFull_poly_oneShot_base

end DeepWiki.SymbolicIntegration