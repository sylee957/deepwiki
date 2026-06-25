import DeepWiki.SymbolicIntegration.ComputableLogPartTowerCorrect
import DeepWiki.SymbolicIntegration.ComputableResultantGeneric

/-! # The hyperexponential frontier of the §5.6 Rothstein–Trager log part (Bronstein §5.9)

The proven §5.6 spine (`ComputableLogPartTowerCorrect`) discharges the residue match
`∑ᵢ cᵢ·(Δgᵢ)/gᵢ = a/d` — and hence the integral identity `D(∑ aᵢ·log gᵢ) = a/d` — in the **primitive**
regime `Dt ∈ k` (`towerLogPart_eq_div_of_const_seed`, headline `cIntegrate_checkIdentity_uncond`). The
constancy hypothesis there (`δ(X − Cα) = C(b α)`, i.e. `toPolyG Dt = C w₀`) is the precise dividing line:
for a **hyperexponential** monomial `Dt ∉ k` (e.g. `Dt = η·t`, `t = exp`) the monomial derivation sends a
linear factor to a *non-constant* `δ(X − Cα) = C η·X + C(b α)` of `X`-degree 1, and the residue sum
`∑ aᵢ·(Δgᵢ)/gᵢ` then **exceeds** `a/d` by a nonzero residual.

This file investigates the hyperexponential frontier the same way the `fₛ = 0` boundary was clarified
(`cIntegrate_indep_special`): determine the engine's actual behavior, prove the explicit residual, and
characterize the §5.9 gap.

## The explicit residual `R`

For the general degree-≤1 seed `δ(X − Cα) = C η·X + C(γ α)` (the X-coefficient `η = δX`-leading is
**uniform** across all roots, since `δX = δt = Dt`; the constant part `γ α = η·α + w₀ − α′` varies), the
key algebra is the proper/polynomial split

```
  (η·X + C(γα)) / (X − Cα)  =  C η  +  C(ηα + γα) / (X − Cα).
```

Summed over a split squarefree `d = nodal s id = ∏_{α∈s}(X − α)` against the §5.6 residues
`res α = A(α)/(δd)(α)`, the proper parts reassemble to `a/d` exactly (the primitive partial fraction,
`sum_residue_seed_logDeriv_eq_div` with `b α = ηα + γα`), leaving the **constant residual**

```
  R  =  C( η · ∑_{α∈s} res α )           (an element of k = ℚ(x), independent of t)
```

so the headline identity is

```
  ∑_{α∈s} (res α)·(δ(X−Cα))/(X−Cα)  =  A/d  +  C( η · ∑ res α ).
```

`extendDeriv_logPart_eq_div_add_residual` is this explicit-residual statement; it **generalizes**
`towerLogPart_eq_div_of_const_seed` (the case `η = 0`, `R = 0` ⟺ `Dt ∈ k`) to an explicit `R`, with the
primitive identity recovered as a corollary (`extendDeriv_logPart_eq_div_of_eta_zero`).

## The engine behavior (the key finding)

`cIntegrate` (`ComputableIntegrate`) does **not** self-check the log part: its only gate is the polynomial
remainder `cisZeroG prem` (`cIntegrate_none_of_prem_ne`). For a hyperexponential *simple* input
`f = a/d` (`fₚ = 0`, so `prem = 0` trivially) it therefore returns `some res` with `res` the §5.6
log-part construction — **even though** `D(res) = f + R ≠ f`. Equivalently: the honest derivative checker
`IntegralResult.checkIdentity` (which does test `D(res) = f` cleared of denominators) returns **false** on
such input. So on hyperexponential input the engine returns an **incorrect `some res`**, not `none`
(contrast the `fₛ ≠ 0` case, which is *discarded*, and `prem ≠ 0`, which returns `none`). The residue
construction is derivation-generic — it runs for any `Dt` — but is only *correct* for primitive `Dt`.

`cIntegrate_checkIdentity_residual_form` makes this citable: the engine's log-derivative sum equals
`f + R`, so the cleared `checkIdentity` is the test `R = 0`.

## The §5.9 gap

A complete hyperexponential integrator must **integrate the residual** `R = C(η·∑ res α) ∈ k` itself —
this is the hyperexponential reduction of Bronstein §5.9: the constant `R` feeds back as a §6 RDE in the
cancellation regime `Dy = R − (Dt/t)·y` (the hyperexponential `IntegratePrimitivePolynomial` /
`HyperexponentialReduce` loop, with `cPolyRischDECancelExp` of §6.6 providing the cancellation oracle).
Because `R ∈ k` is itself elementary-integrable (it is a rational function of `x`), the hyperexponential
case is **not** non-elementary in general — it is an **engine limit**: the engine returns the wrong object
because it never wires `R` back through the §5.9/§6.6 machinery, exactly as the `fₛ = 0` gate is an engine
limit (the engine never wires `fₛ` through the RDE oracle). The fix is engine work (out of scope here), not
a mathematical obstruction; the boundary is `η = 0`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-! ### The proper/polynomial split of a degree-≤1 logarithmic-derivative term -/

section Split
variable {K : Type*} [Field K]

/-- **The degree-1 log-derivative term splits into a constant plus a proper part**: for a linear factor
`X − Cα` and a degree-≤1 numerator `C η·X + C γ` (the hyperexponential `δ(X − Cα)`), as rational
functions
`algMap(C η·X + C γ)/algMap(X − Cα) = algMap(C η) + algMap(C (η·α + γ))/algMap(X − Cα)`.
The constant `C η` is the residual contributor; the proper part `C(ηα + γ)/(X − Cα)` is the primitive
partial-fraction term. For `η = 0` (primitive) the constant part vanishes. -/
theorem logDeriv_X_sub_C_split (η γ α : K) :
    algebraMap K[X] (RatFunc K) (C η * X + C γ) / algebraMap K[X] (RatFunc K) (X - C α)
      = algebraMap K[X] (RatFunc K) (C η)
        + algebraMap K[X] (RatFunc K) (C (η * α + γ))
            / algebraMap K[X] (RatFunc K) (X - C α) := by
  have hinj := RatFunc.algebraMap_injective K
  have hXα : algebraMap K[X] (RatFunc K) (X - C α) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr (X_sub_C_ne_zero α)
  rw [show C η * X + C γ = C η * (X - C α) + C (η * α + γ) by rw [C_add, C_mul]; ring,
    map_add, map_mul, add_div, mul_div_assoc, div_self hXα, mul_one]

end Split

/-! ### The hyperexponential residue sum: `∑ res·(δ(X−Cα))/(X−Cα) = A/d + R` (explicit `R`)

The generic residual identity over a base derivation `δ` whose action on each linear factor is the
degree-≤1 form `δ(X − Cα) = C η·X + C(γ α)`. The X-coefficient `η` is **uniform** (it is `δX`), the
constant part `γ α` varies. The proper parts reassemble to `A/d` exactly (the primitive partial fraction
with `b α = η·α + γ α`); the constants accumulate to `R = C(η · ∑ res α)`. -/

section Residual
open Polynomial
variable {K : Type*} [Field K] [Algebra ℚ K] (δ : Derivation ℤ K[X] K[X])

omit [Algebra ℚ K] in
/-- **The hyperexponential per-root scalar identity**: at a simple root `α` of `d = nodal s id`, if the
monomial derivation sends the linear factor to `δ(X − Cα) = C η·X + C(γ α)` (degree ≤ 1), then the §5.6
residue `A(α)/(δ d)(α)` scaled by the *evaluated* seed `b α = η·α + γ α` equals the §2 d/dx residue
`A(α)/d'(α)`. From `deriv_eval_at_simple_root` (`(δd)(α) = (δ(X−Cα))(α)·E(α)`,
`(δ(X−Cα))(α) = η·α + γ α`) and `eval_derivative_X_sub_C_mul` (`E(α) = d'(α)`). The hyperexponential
analogue of `residue_seed_mul_eq_residue_derivative` (the seed is *evaluated*, not constant). -/
theorem residue_seed_mul_eq_residue_derivative_hyperexp (A : K[X]) (s : Finset K) {α : K}
    (η : K) (γ : K → K) (hα : α ∈ s) (hδ : δ (X - C α) = C η * X + C (γ α))
    (hb0 : η * α + γ α ≠ 0) :
    A.eval α / (δ (Lagrange.nodal s id)).eval α * (η * α + γ α)
      = A.eval α / eval α (derivative (Lagrange.nodal s id)) := by
  classical
  set d := Lagrange.nodal s id with hd
  have hdvd : (X - C α) ∣ d := by
    rw [hd, Lagrange.nodal_eq]; exact Finset.dvd_prod_of_mem _ hα
  set E := d / (X - C α) with hE
  have hfac : d = (X - C α) * E := (EuclideanDomain.mul_div_cancel' (X_sub_C_ne_zero α) hdvd).symm
  have hδeval : (δ (X - C α)).eval α = η * α + γ α := by
    rw [hδ, eval_add, eval_mul, eval_C, eval_X, eval_C]
  have hδd : (δ d).eval α = (η * α + γ α) * E.eval α := by
    rw [hfac, deriv_eval_at_simple_root δ E α, hδeval]
  have hd' : eval α (derivative d) = E.eval α := by rw [hfac, eval_derivative_X_sub_C_mul]
  rw [hδd, hd']
  field_simp

omit [Algebra ℚ K] in
/-- **The hyperexponential residue match with explicit residual** (per-root form): for `A` of degree
`< #s` over the split squarefree `d = nodal s id = ∏_{α∈s}(X − α)`, and a base derivation `δ` whose action
on each linear factor is the **degree-≤1** form `δ(X − Cα) = C η·X + C(γ α)` (the hyperexponential seed;
the X-coefficient `η = δX` is uniform across roots), with `b α := η·α + γ α ≠ 0` (the §5.6 residue
denominator is `(δd)(α) = b α·d'(α) ≠ 0`), the residue sum **exceeds** the integrand `A/d` by the explicit
constant residual `C(η·∑ res α)`:
`∑_{α∈s} algMap(C(res α))·(algMap(δ(X−Cα))/algMap(X−Cα)) = algMap A/algMap d + algMap(C(η·∑ res α))`,
with `res α = A(α)/(δ d)(α)`. The proper parts reassemble to `A/d` by the primitive partial fraction
`sum_residue_seed_logDeriv_eq_div` (with the constant seed `b α`); each term's constant part `C η` sums
into the residual `C(η·∑ res α)`. For `η = 0` (primitive, `Dt ∈ k`) the residual vanishes, recovering
`sum_residue_seed_logDeriv_eq_div`. -/
theorem sum_residue_seed_logDeriv_eq_div_add_residual (A : K[X]) (s : Finset K) (hA : A.degree < s.card)
    (η : K) (γ : K → K) (hδ : ∀ α ∈ s, δ (X - C α) = C η * X + C (γ α))
    (hb0 : ∀ α ∈ s, η * α + γ α ≠ 0) :
    ∑ α ∈ s, algebraMap K[X] (RatFunc K)
          (C (A.eval α / (δ (Lagrange.nodal s id)).eval α))
        * (algebraMap K[X] (RatFunc K) (δ (X - C α))
            / algebraMap K[X] (RatFunc K) (X - C α))
      = algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id)
        + algebraMap K[X] (RatFunc K)
            (C (η * ∑ α ∈ s, A.eval α / (δ (Lagrange.nodal s id)).eval α)) := by
  classical
  set res : K → K := fun α => A.eval α / (δ (Lagrange.nodal s id)).eval α with hres
  -- split each term into its constant `C(res α)·C η` part and its proper `C(res α)·C(bα)/(X−α)` part.
  have hsplit : ∀ α ∈ s,
      algebraMap K[X] (RatFunc K) (C (res α))
          * (algebraMap K[X] (RatFunc K) (δ (X - C α))
              / algebraMap K[X] (RatFunc K) (X - C α))
        = algebraMap K[X] (RatFunc K) (C (res α)) * algebraMap K[X] (RatFunc K) (C η)
          + algebraMap K[X] (RatFunc K) (C (res α))
              * (algebraMap K[X] (RatFunc K) (C (η * α + γ α))
                  / algebraMap K[X] (RatFunc K) (X - C α)) := by
    intro α hα
    rw [hδ α hα, logDeriv_X_sub_C_split η (γ α) α, mul_add]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  -- the proper-part sum is `A/d` (primitive partial fraction `ratFunc_eq_sum_residue_div` after the
  -- per-root scalar identity `res α·(ηα+γα) = A(α)/d'(α)`).
  have hproper : ∑ α ∈ s, algebraMap K[X] (RatFunc K) (C (res α))
        * (algebraMap K[X] (RatFunc K) (C (η * α + γ α))
            / algebraMap K[X] (RatFunc K) (X - C α))
      = algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id) := by
    rw [ratFunc_eq_sum_residue_div s A hA]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [← mul_div_assoc, ← map_mul, ← C_mul,
      residue_seed_mul_eq_residue_derivative_hyperexp δ A s η γ hα (hδ α hα) (hb0 α hα)]
  -- the constant-part sum is the residual `C(η·∑ res)`.
  have hconst : ∑ α ∈ s, algebraMap K[X] (RatFunc K) (C (res α)) * algebraMap K[X] (RatFunc K) (C η)
      = algebraMap K[X] (RatFunc K) (C (η * ∑ α ∈ s, res α)) := by
    rw [← Finset.sum_mul, ← map_sum, ← map_mul]
    congr 2
    rw [← map_sum (C : K →+* K[X]), ← C_mul, mul_comm]
  rw [hproper, hconst, add_comm]

omit [Algebra ℚ K] in
open scoped Classical in
/-- **The hyperexponential residue match with explicit residual** (the Rothstein–Trager **grouped** form):
the residue-grouped sum (over the distinct residues `c ∈ s.image res`, with log argument
`gᶜ = ∏_{res α = c}(X − α)`) **exceeds** the integrand `A/d` by the same explicit constant residual
`C(η·∑ res α)`:
`∑_c algMap(C c)·(algMap(δ gᶜ)/algMap gᶜ) = algMap A/algMap d + algMap(C(η·∑ res α))`. The grouped analogue of
`sum_residue_seed_logDeriv_eq_div_add_residual`: each `δ gᶜ/gᶜ` is the fiber's per-root sum
(`sum_logDeriv_prod_X_sub_C`), the fiberwise regrouping (`Finset.sum_fiberwise_of_maps_to`) recovers the
per-root residue sum, which is `A/d + R`. This is exactly the residue sum the engine's `logResidueSum`
computes (cf. `logResidueSum_eq_grouped`); for `η = 0` it is the proven `sum_residue_grouped_logDeriv_eq_div`. -/
theorem sum_residue_grouped_logDeriv_eq_div_add_residual (A : K[X]) (s : Finset K)
    (hA : A.degree < s.card) (η : K) (γ : K → K) (hδ : ∀ α ∈ s, δ (X - C α) = C η * X + C (γ α))
    (hb0 : ∀ α ∈ s, η * α + γ α ≠ 0) :
    ∑ c ∈ s.image (fun α => A.eval α / (δ (Lagrange.nodal s id)).eval α),
        algebraMap K[X] (RatFunc K) (C c)
          * (algebraMap K[X] (RatFunc K)
                (δ (∏ α ∈ s.filter
                      (fun α => A.eval α / (δ (Lagrange.nodal s id)).eval α = c), (X - C α)))
              / algebraMap K[X] (RatFunc K)
                (∏ α ∈ s.filter
                      (fun α => A.eval α / (δ (Lagrange.nodal s id)).eval α = c), (X - C α)))
      = algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id)
        + algebraMap K[X] (RatFunc K)
            (C (η * ∑ α ∈ s, A.eval α / (δ (Lagrange.nodal s id)).eval α)) := by
  classical
  set res : K → K := fun α => A.eval α / (δ (Lagrange.nodal s id)).eval α with hres
  rw [← sum_residue_seed_logDeriv_eq_div_add_residual δ A s hA η γ hδ hb0,
    ← Finset.sum_fiberwise_of_maps_to (g := res) (t := s.image res)
      (fun α hα => Finset.mem_image_of_mem _ hα)
      (f := fun α => algebraMap K[X] (RatFunc K) (C (res α))
        * (algebraMap K[X] (RatFunc K) (δ (X - C α))
            / algebraMap K[X] (RatFunc K) (X - C α)))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [sum_logDeriv_prod_X_sub_C δ (s.filter (fun α => res α = c)), Finset.mul_sum]
  exact Finset.sum_congr rfl fun α hα => by rw [(Finset.mem_filter.mp hα).2]

/-- **The hyperexponential integral identity with explicit residual** (`D(∑ aᵢ·log gᵢ) = a/d + R`, the
headline): over a split squarefree `d = nodal s id`, with a base derivation `δ` of **hyperexponential**
type — `δ(X − Cα) = C η·X + C(γ α)` (degree-≤1, the X-coefficient `η = δX` uniform), `b α = η·α + γ α ≠ 0`
— and δ-constant residues `C(res α)`, the logarithmic part `∑_{α∈s} algMap(C(res α))·log(X−Cα)` (each
`log(X−Cα)` modeled by `L α` with the per-factor log-derivative `hL`) differentiates under `extendDeriv δ`
to `A/d` **plus the explicit constant residual** `algMap(C(η·∑ res α))`:
`extendDeriv δ (∑ algMap(C(res α))·L α) = A/d + algMap(C(η·∑ res α))`. The full hyperexponential analogue of
the primitive `extendDeriv_logPart_eq_div`: the differential spine
(`extendDeriv_sum_const_logDerivOf`) reduces the LHS to the residue sum, and
`sum_residue_seed_logDeriv_eq_div_add_residual` supplies its closed form `A/d + R`. For `η = 0` (primitive,
`Dt ∈ k`) `R = 0` and this **is** `extendDeriv_logPart_eq_div` (per-root form). The residual `R = C(η·∑ res
α) ∈ k` is the §5.9 hyperexponential reduction's leftover — itself integrable (a rational function of `x`),
so the obstruction is an engine limit, not non-elementarity. -/
theorem extendDeriv_logPart_eq_div_add_residual (A : K[X]) (s : Finset K) (hA : A.degree < s.card)
    (η : K) (γ : K → K) (hδ : ∀ α ∈ s, δ (X - C α) = C η * X + C (γ α))
    (hb0 : ∀ α ∈ s, η * α + γ α ≠ 0)
    (hc : ∀ α ∈ s, δ (C (A.eval α / (δ (Lagrange.nodal s id)).eval α)) = 0)
    (L : K → RatFunc K)
    (hL : ∀ α ∈ s, extendDeriv δ (L α)
      = algebraMap K[X] (RatFunc K) (δ (X - C α)) / algebraMap K[X] (RatFunc K) (X - C α)) :
    extendDeriv δ (∑ α ∈ s,
        algebraMap K[X] (RatFunc K) (C (A.eval α / (δ (Lagrange.nodal s id)).eval α)) * L α)
      = algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id)
        + algebraMap K[X] (RatFunc K)
            (C (η * ∑ α ∈ s, A.eval α / (δ (Lagrange.nodal s id)).eval α)) := by
  rw [extendDeriv_sum_const_logDerivOf δ s
      (fun α => C (A.eval α / (δ (Lagrange.nodal s id)).eval α)) (fun α => X - C α) hc L hL,
    sum_residue_seed_logDeriv_eq_div_add_residual δ A s hA η γ hδ hb0]

/-- **The primitive case as the `η = 0` corollary** (`R = 0` ⟺ `Dt ∈ k`): when the X-coefficient `η = 0`
(the seed `δ(X − Cα) = C(γ α)` is constant, the primitive condition), the explicit residual
`C(η·∑ res α) = C 0 = 0` vanishes and the hyperexponential identity collapses to the primitive
`D(∑ aᵢ·log gᵢ) = A/d`. The boundary `η = 0` is exactly the dividing line of
`towerLogPart_eq_div_of_const_seed`. -/
theorem extendDeriv_logPart_eq_div_of_eta_zero (A : K[X]) (s : Finset K) (hA : A.degree < s.card)
    (γ : K → K) (hδ : ∀ α ∈ s, δ (X - C α) = C (γ α)) (hb0 : ∀ α ∈ s, γ α ≠ 0)
    (hc : ∀ α ∈ s, δ (C (A.eval α / (δ (Lagrange.nodal s id)).eval α)) = 0)
    (L : K → RatFunc K)
    (hL : ∀ α ∈ s, extendDeriv δ (L α)
      = algebraMap K[X] (RatFunc K) (δ (X - C α)) / algebraMap K[X] (RatFunc K) (X - C α)) :
    extendDeriv δ (∑ α ∈ s,
        algebraMap K[X] (RatFunc K) (C (A.eval α / (δ (Lagrange.nodal s id)).eval α)) * L α)
      = algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id) := by
  have h := extendDeriv_logPart_eq_div_add_residual δ A s hA 0 γ
    (fun α hα => by rw [hδ α hα, C_0, zero_mul, zero_add]) (fun α hα => by simpa using hb0 α hα)
    hc L hL
  rw [h, zero_mul, C_0, map_zero, add_zero]

/-- Headline restatement: the explicit-residual residue sum `∑ res·(δ(X−Cα))/(X−Cα) = A/d + C(η·∑res)`
(per-root), the hyperexponential analogue of the primitive `sum_residue_seed_logDeriv_eq_div`. -/
example (A : K[X]) (s : Finset K) (hA : A.degree < s.card) (η : K) (γ : K → K)
    (hδ : ∀ α ∈ s, δ (X - C α) = C η * X + C (γ α)) (hb0 : ∀ α ∈ s, η * α + γ α ≠ 0) :
    ∑ α ∈ s, algebraMap K[X] (RatFunc K) (C (A.eval α / (δ (Lagrange.nodal s id)).eval α))
        * (algebraMap K[X] (RatFunc K) (δ (X - C α)) / algebraMap K[X] (RatFunc K) (X - C α))
      = algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id)
        + algebraMap K[X] (RatFunc K)
            (C (η * ∑ α ∈ s, A.eval α / (δ (Lagrange.nodal s id)).eval α)) :=
  sum_residue_seed_logDeriv_eq_div_add_residual δ A s hA η γ hδ hb0

/-- Headline restatement: the hyperexponential integral identity `D(∑ aᵢ·log gᵢ) = A/d + C(η·∑res)` under
`extendDeriv δ` — the headline deliverable generalizing `extendDeriv_logPart_eq_div` with explicit `R`. -/
example (A : K[X]) (s : Finset K) (hA : A.degree < s.card) (η : K) (γ : K → K)
    (hδ : ∀ α ∈ s, δ (X - C α) = C η * X + C (γ α)) (hb0 : ∀ α ∈ s, η * α + γ α ≠ 0)
    (hc : ∀ α ∈ s, δ (C (A.eval α / (δ (Lagrange.nodal s id)).eval α)) = 0)
    (L : K → RatFunc K)
    (hL : ∀ α ∈ s, extendDeriv δ (L α)
      = algebraMap K[X] (RatFunc K) (δ (X - C α)) / algebraMap K[X] (RatFunc K) (X - C α)) :
    extendDeriv δ (∑ α ∈ s,
        algebraMap K[X] (RatFunc K) (C (A.eval α / (δ (Lagrange.nodal s id)).eval α)) * L α)
      = algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id)
        + algebraMap K[X] (RatFunc K)
            (C (η * ∑ α ∈ s, A.eval α / (δ (Lagrange.nodal s id)).eval α)) :=
  extendDeriv_logPart_eq_div_add_residual δ A s hA η γ hδ hb0 hc L hL

/-- Headline restatement: the `η = 0` boundary — the residual vanishes and the hyperexponential identity
collapses to the primitive `D(∑ aᵢ·log gᵢ) = A/d`. -/
example (A : K[X]) (s : Finset K) (hA : A.degree < s.card) (γ : K → K)
    (hδ : ∀ α ∈ s, δ (X - C α) = C (γ α)) (hb0 : ∀ α ∈ s, γ α ≠ 0)
    (hc : ∀ α ∈ s, δ (C (A.eval α / (δ (Lagrange.nodal s id)).eval α)) = 0)
    (L : K → RatFunc K)
    (hL : ∀ α ∈ s, extendDeriv δ (L α)
      = algebraMap K[X] (RatFunc K) (δ (X - C α)) / algebraMap K[X] (RatFunc K) (X - C α)) :
    extendDeriv δ (∑ α ∈ s,
        algebraMap K[X] (RatFunc K) (C (A.eval α / (δ (Lagrange.nodal s id)).eval α)) * L α)
      = algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id) :=
  extendDeriv_logPart_eq_div_of_eta_zero δ A s hA γ hδ hb0 hc L hL

end Residual

/-! ### The engine behavior on hyperexponential input — `logResidueSum = hₛ + R` (the key finding)

The engine `cIntegrate`/`cLogPart`/`cResidueResultantTower` is **derivation-generic**: it runs `cmonomialDeriv
Dt` for *any* `Dt`, so on hyperexponential input (`toPolyG Dt = C η·X + C w₀`, `η ≠ 0`, e.g. `Dt = η·t`,
`t = exp`) it still produces a residue/log-part result. But that result is **wrong**: the engine's
log-derivative sum `logResidueSum Dt logs` equals the simple residual `hₛ = hNum/hDen` **plus the explicit
residual** `R = C(η·∑ res α)`, not `hₛ`. So `D(cIntegrate f) = f + R ≠ f` and the honest checker
`IntegralResult.checkIdentity` returns `false` — the engine returns an *incorrect* `some res` (it does not
return `none`, since for a pure simple input `fₚ = 0` ⟹ `prem = 0`, the only gate of `cIntegrate`). The
hyperexponential analogue of the primitive `logResidueSum_eq_div_of_residueData` (`R = 0`). -/

namespace CPolyG

open scoped Differential
open QFunNZ

/-- The tower fraction field's `Algebra ℚ` (matching the keystone instances), so `algebraMap ℚ
(CFieldSpec.K QFunNZ)` resolves uniformly with the proven RT spine. -/
noncomputable local instance : Algebra ℚ (CFieldSpec.K QFunNZ) :=
  inferInstanceAs (Algebra ℚ (RatFunc ℚ))

open DeepWiki.SymbolicIntegration in
open scoped Classical in
/-- **The hyperexponential residual over the tower** `towerHyperexpResidual Dt hNum hDen s = C(η·∑ res α)`:
the explicit `R ∈ k = ℚ(x)` (read into the tower field via `towerAlg`) by which the engine's
`logResidueSum` overshoots the simple residual `hₛ`, with `η = w₀` the `X`-coefficient of `toPolyG Dt` and
`res α = hNum(α)/(Δ hDen)(α)` the §5.6 residues over the splitting set `s`. A constant of `t` (degree 0 in
`t`), hence itself rational in `x`. -/
noncomputable def towerHyperexpResidual (Dt hNum : CPolyG QFunNZ) (η : CFieldSpec.K QFunNZ)
    (s : Finset (CFieldSpec.K QFunNZ)) : RatFunc (CFieldSpec.K QFunNZ) :=
  towerAlg (Polynomial.C (η * ∑ α ∈ s, (toPolyG hNum).eval α
    / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval α))

open DeepWiki.SymbolicIntegration in
open scoped Classical Differential in
/-- **The engine's `logResidueSum` overshoots by the explicit residual `R`** (the hyperexponential analogue
of `logResidueSum_eq_div_of_residueData`, the key engine-behavior finding): for a **hyperexponential**
monomial `toPolyG Dt = C η·X + C w₀` (`η ≠ 0`, `Dt ∉ k`, e.g. `Dt = η·t`, `t = exp`), with the concrete
denominator split `toPolyG hDen = nodal s id`, `deg hNum < #s`, the seed normality `η·α + w₀ − α′ ≠ 0` at
each root, and the concrete log list corresponding to the distinct-residue data
(`hkeysNodup`/`hkeysImage`/`harg`), the engine's concrete residue sum equals the simple residual **plus the
explicit residual**:
`logResidueSum Dt logs = towerAlg(hNum)/towerAlg(hDen) + towerHyperexpResidual Dt hNum η s`.
Composes the list→Finset reindexing `logResidueSum_eq_grouped` with the grouped hyperexponential residue
identity `sum_residue_grouped_logDeriv_eq_div_add_residual` (seed `δ(X − Cα) = C η·X + C(w₀ − α′)` via
`implicitDeriv_X_sub_C`). For `η = 0` (primitive) the residual vanishes and this is
`logResidueSum_eq_div_of_residueData`. **This is why `IntegralResult.checkIdentity` fails on
hyperexponential input** — the engine's `D(res) = f + R ≠ f`. -/
theorem towerLogResidueSum_eq_div_add_residual_of_residueData (Dt : CPolyG QFunNZ)
    {η w₀ : CFieldSpec.K QFunNZ} (htop : toPolyG Dt = C η * X + C w₀)
    (hNum hDen : CPolyG QFunNZ) (logs : List (ℚ × CPolyG QFunNZ))
    (s : Finset (CFieldSpec.K QFunNZ))
    (hden : toPolyG hDen = Lagrange.nodal s id)
    (hA : (toPolyG hNum).degree < s.card)
    (hb0 : ∀ α ∈ s, η * α + (w₀ - α′) ≠ 0)
    (hkeysNodup : (logs.map (fun cv => CFieldSpec.toK (ofConstNZ cv.1))).Nodup)
    (hkeysImage : (logs.map (fun cv => CFieldSpec.toK (ofConstNZ cv.1))).toFinset
      = s.image (fun α => (toPolyG hNum).eval α
          / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval α))
    (harg : ∀ cv ∈ logs, toPolyG cv.2
      = ∏ α ∈ s.filter (fun α => (toPolyG hNum).eval α
            / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval α
              = CFieldSpec.toK (ofConstNZ cv.1)), (X - C α)) :
    logResidueSum Dt logs
      = towerAlg (toPolyG hNum) / towerAlg (toPolyG hDen)
        + towerHyperexpResidual Dt hNum η s := by
  classical
  rw [logResidueSum_eq_grouped Dt hNum logs s hkeysNodup hkeysImage harg, hden, towerHyperexpResidual]
  -- the grouped hyperexponential residue match with seed `δ(X − Cα) = C η·X + C(w₀ − α′)`
  exact sum_residue_grouped_logDeriv_eq_div_add_residual (Differential.implicitDeriv (toPolyG Dt))
    (toPolyG hNum) s hA η (fun α => w₀ - α′)
    (fun α _ => by rw [implicitDeriv_X_sub_C, htop, C_sub, add_sub_assoc]) hb0

open DeepWiki.SymbolicIntegration in
open scoped Classical Differential in
/-- Restatement: the engine's hyperexponential `logResidueSum` overshoots the simple residual by the
explicit residual `R = C(η·∑ res)` — the citable engine-behavior finding. -/
example (Dt : CPolyG QFunNZ) {η w₀ : CFieldSpec.K QFunNZ} (htop : toPolyG Dt = C η * X + C w₀)
    (hNum hDen : CPolyG QFunNZ) (logs : List (ℚ × CPolyG QFunNZ))
    (s : Finset (CFieldSpec.K QFunNZ)) (hden : toPolyG hDen = Lagrange.nodal s id)
    (hA : (toPolyG hNum).degree < s.card) (hb0 : ∀ α ∈ s, η * α + (w₀ - α′) ≠ 0)
    (hkeysNodup : (logs.map (fun cv => CFieldSpec.toK (ofConstNZ cv.1))).Nodup)
    (hkeysImage : (logs.map (fun cv => CFieldSpec.toK (ofConstNZ cv.1))).toFinset
      = s.image (fun α => (toPolyG hNum).eval α
          / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval α))
    (harg : ∀ cv ∈ logs, toPolyG cv.2
      = ∏ α ∈ s.filter (fun α => (toPolyG hNum).eval α
            / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval α
              = CFieldSpec.toK (ofConstNZ cv.1)), (X - C α)) :
    logResidueSum Dt logs
      = towerAlg (toPolyG hNum) / towerAlg (toPolyG hDen) + towerHyperexpResidual Dt hNum η s :=
  towerLogResidueSum_eq_div_add_residual_of_residueData Dt htop hNum hDen logs s hden hA hb0
    hkeysNodup hkeysImage harg

/-! ### The engine returns `some` (an incorrect result), NOT `none`, on a pure simple input

For a **pure simple** input — the canonical split has empty polynomial part `fp = []` (so the only gate
`cisZeroG (cPrimitivePolyIntegrate Dt fuel [])` is `cisZeroG [] = true`) — `cIntegrate` returns `some res`
**unconditionally**, with `res` the §5.6 log-part construction. Combined with
`towerLogResidueSum_eq_div_add_residual_of_residueData` (the engine's `D(res) = f + R`), this pins the key
finding: on hyperexponential input the engine returns an **incorrect `some res`** (the residual `R` makes
`D(res) ≠ f`), it does **not** report non-elementarity with `none`. Contrast `cIntegrate_none_of_prem_ne`
(a nonzero polynomial remainder ⟹ `none`): a pure simple integrand never reaches that branch. -/

/-- **`cIntegrate` returns `some` (not `none`) for a pure simple input** (the canonical split has empty
polynomial part): if `canonicalRepresentationFast Dt fuel a d = ([], (b, ds), (cn, dn))`, then
`cIntegrate Dt fuel a d cands = some ⟨…⟩` — the engine produces an `IntegralResult`, **regardless of
whether that result is correct**. For hyperexponential `Dt`, that result is *wrong*
(`towerLogResidueSum_eq_div_add_residual_of_residueData` gives `D(res) = f + R`, `R ≠ 0`), so the engine
returns an incorrect `some res`, not the non-elementary `none`. The polynomial-remainder gate
`cisZeroG (cPrimitivePolyIntegrate Dt fuel []).2` is `cisZeroG [] = true` (a `0 + 1`-fuel evaluation), so
the `if` always takes the `some` branch. -/
theorem cIntegrate_some_of_empty_poly (Dt : CPolyG QFunNZ) (fuel : ℕ) (a d : CPolyG QFunNZ)
    (cands : List ℚ) (b ds cn dn : CPolyG QFunNZ)
    (hcanon : canonicalRepresentationFast Dt (fuel + 1) a d = ([], (b, ds), (cn, dn))) :
    ∃ res : IntegralResult, cIntegrate Dt (fuel + 1) a d cands = some res := by
  rw [cIntegrate_indep_special Dt (fuel + 1) a d cands [] b ds cn dn hcanon]
  -- `cPrimitivePolyIntegrate Dt (fuel+1) [] = ([], [])`, so `cisZeroG [] = true` and the `some` branch fires.
  have hpoly : cPrimitivePolyIntegrate Dt (fuel + 1) [] = ([], []) := by
    rw [cPrimitivePolyIntegrate]; simp
  simp only [hpoly]
  exact ⟨_, rfl⟩

/-- Restatement: the engine produces an `IntegralResult` (returns `some`) for any pure simple input — so on
hyperexponential input it returns an *incorrect* `some res`, never the non-elementary `none`. -/
example (Dt : CPolyG QFunNZ) (fuel : ℕ) (a d : CPolyG QFunNZ) (cands : List ℚ)
    (b ds cn dn : CPolyG QFunNZ)
    (hcanon : canonicalRepresentationFast Dt (fuel + 1) a d = ([], (b, ds), (cn, dn))) :
    ∃ res : IntegralResult, cIntegrate Dt (fuel + 1) a d cands = some res :=
  cIntegrate_some_of_empty_poly Dt fuel a d cands b ds cn dn hcanon

end CPolyG

/-! ### The §5.9 gap, precisely — what a complete hyperexponential integrator needs

The residual `R = C(η · ∑_{α∈s} res α) ∈ k = ℚ(x)` is the **only** obstruction the proven §5.6 spine leaves
in the hyperexponential regime: every other piece (the residue resultant `cResidueResultantTower`, the log
arguments `cLogArgTower`, the rational-residue scan, the Hermite rational part) is derivation-generic and
already correct. The boundary is sharp — `R = 0` **iff** `η = 0` **iff** `Dt ∈ k` (primitive), and then the
identity is the proven `cIntegrate_checkIdentity_uncond`.

What §5.9 (Bronstein, *the hyperexponential reduction*) adds is the back-substitution of `R`. Because `R`
is the constant-in-`t` coefficient `η·∑ res α ∈ k`, integrating the hyperexponential integrand requires
**also integrating `R` as a function of `x`** — and crucially, the §5.6 logarithmic construction was carried
out over the monomial `t = exp(∫η)`, whose own derivative `Dt = η·t` couples the `t`-degrees. Concretely a
complete hyperexponential `IntegratePrimitivePolynomial` / `HyperexponentialReduce` loop:

* peels the residual `R(z) = η·∑ res` **per `t`-degree**, feeding each coefficient into the **§6 Risch
  differential equation in the cancellation regime** `Dy − (Dt/t)·y = R` (`Dt/t = η`), i.e. `Dy − η·y = R`;
* the cancellation oracle for this hyperexponential RDE is the **proven** `cPolyRischDECancelExp` (§6.6) —
  the engine already contains the solver for `Dy + η·y = …`, the exact shape `R` produces;
* the recovered `y ∈ k(t)` adjusts the rational part `g`, absorbing `R` so that `D(g_new + ∑ c·log v) = f`.

Therefore the hyperexponential case is an **engine limit, not a non-elementary case**: `R ∈ k` is a rational
function of `x`, always elementary-integrable, so the antiderivative *exists* and is *elementary* — the
engine simply never wires `R` through §5.9/§6.6. This is the **same kind of boundary** as the `fₛ = 0` gate
(`cIntegrate_indep_special`): the engine structurally discards a sub-part it would need to route through the
RDE oracle. Genuine non-elementarity (`cIntegrate = none`) arises only from a *different* source — a §6 RDE
with no `k(t)`-solution (Example 6.4.1, `cRischDE = none`), which the engine *does* detect. The deliverable
here is the precise residual `R` and the proof that it is the whole hyperexponential gap; closing it is
engine work (wiring `cPolyRischDECancelExp` into the §5.6 path), out of scope under the no-engine-edit
constraint. -/

-- Axiom audits for the headline deliverables (`[propext, Classical.choice, Quot.sound]` — no
-- `native_decide`, no `sorryAx`).
#print axioms logDeriv_X_sub_C_split
#print axioms residue_seed_mul_eq_residue_derivative_hyperexp
#print axioms sum_residue_seed_logDeriv_eq_div_add_residual
#print axioms sum_residue_grouped_logDeriv_eq_div_add_residual
#print axioms extendDeriv_logPart_eq_div_add_residual
#print axioms extendDeriv_logPart_eq_div_of_eta_zero
#print axioms CPolyG.towerLogResidueSum_eq_div_add_residual_of_residueData
#print axioms CPolyG.cIntegrate_some_of_empty_poly
