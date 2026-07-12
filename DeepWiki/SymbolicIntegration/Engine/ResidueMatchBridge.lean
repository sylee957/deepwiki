import DeepWiki.SymbolicIntegration.Engine.ResidueMatchSoundness
import DeepWiki.SymbolicIntegration.Core.Differential.FractionFieldDerivLinearFactor
import DeepWiki.SymbolicIntegration.Engine.ResidueLogPart

/-! # Residue-match bridges

List-to-`Finset` residue-match bridges and the hyperexponential cancellation obstruction.
-/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac

namespace ResidueMatchTower

/-! ### Primitive list-to-`Finset` bridge

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

/-! ### Hyperexponential cancellation criterion

For a NON-primitive monomial the residue match needs `monomial_residue_match_of_cancel`'s extra hypothesis
`hcancel : ∑_α C(c_α)·((v − Cα′) /ₘ (t−α)) = 0`. The cleanest non-primitive case is the **hyperexponential**
`Dt = η′·t`, i.e. `v = C b · X` (`b = η′`): then each polynomial part `(C b·X − C α′) /ₘ (X − C α)` is the
*constant* `C b` (degree-1-over-degree-1 quotient), **independent of α**, so `hcancel` collapses to
`C b·∑_α C(c_α) = 0`, i.e. (over `RatFunc K`) `b·(∑_α c_α) = 0` — and with `b = η′ ≠ 0` this is exactly the
integrability condition `∑_α c_α = 0` (the exponential-case correction: `a/d` integrable in the log part
alone). We prove this reduction, pinning the precise general-case obstruction the engine's integrability
witness must supply. -/

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
integration witness must discharge. -/
theorem hyperexp_cancel_iff_sum_zero (s : Finset K) (b : K) (hb : b ≠ 0) (c : K → K) :
    (∑ α ∈ s, algebraMap K[X] (RatFunc K) (C (c α) * ((C b * X - C (α′)) /ₘ (X - C α))) = 0)
      ↔ ∑ α ∈ s, c α = 0 := by
  rw [hyperexp_cancel_sum_eq s b c]
  -- `algebraMap (C x) = 0 ↔ x = 0` (algebraMap `K[X] → RatFunc K` and `C` both injective)
  rw [(map_eq_zero_iff _ (RatFunc.algebraMap_injective K)), Polynomial.C_eq_zero,
    mul_eq_zero, or_iff_right hb]

/-! ### Unconditional monomial residue decomposition

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
The cleanest pin of the hyperexp integrability obstruction — the residue match log-part needs is GENUINELY EQUIVALENT to the side condition `∑c = 0`, not an engine-success consequence
(see the closing status: `cIntegrateGFullWf`'s pure-normal branch returns `some` even when `∑c ≠ 0`). -/
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

end DeepWiki.SymbolicIntegration
