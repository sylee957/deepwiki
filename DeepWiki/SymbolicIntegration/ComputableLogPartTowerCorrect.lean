import DeepWiki.SymbolicIntegration.ComputableLogPartTower
import DeepWiki.SymbolicIntegration.ComputableFractionFieldDeriv
import DeepWiki.SymbolicIntegration.RationalIntegrationGcdLogForm

/-! # Abstract correctness of the §5.6 residue-criterion log part over the tower `ℚ(x)(t)`
The computable engine `ComputableLogPartTower` *computes* the §5.6 Rothstein–Trager–Lazard
logarithmic part — the residue resultant `cResidueResultantTower` and the per-residue log arguments
`cLogArgTower` — and `logPartTower_example` validates it (`native_decide`) on Bronstein's Example
5.6.2. This file proves the **abstract correctness** of the underlying *integral identity*, the
all-inputs generalization of the example: the logarithmic part
`∑ aᵢ·log gᵢ` differentiates back to the simple integrand `a/d` over the genuine tower fraction field
`RatFunc (RatFunc ℚ)`, using the keystone derivation `extendDeriv (implicitDeriv (toPolyG Dt))`
(= `towerFractionFieldDeriv Dt`) of `ComputableFractionFieldDeriv`.

The §2 *rational* Rothstein–Trager theory (`PartialFraction`, `RationalIntegrationGcdLogForm`) is the
template: there `D = d/dx`, `D' = derivative D`, and `A/D = ∑_a a·logDeriv(gcd(D, A − a·D'))` with
`∫ A/D = ∑_a a·log(gcd(…))`. The §5.6 case differs in exactly one place — the base derivation: `d/dx`
is replaced by the *monomial* derivation `Δ = implicitDeriv (toPolyG Dt)` on `k[t]` (`k = ℚ(x)`), and
the fraction-field derivation `d/dx` on `K(x)` by `extendDeriv Δ` on `k(t)`. The residue criterion
uses `Δd = implicitDeriv Dt d` in place of `derivative D`.

This file establishes, **derivation-generically** (over any base `δ : Derivation ℤ K[X] K[X]` with
`[Algebra ℚ K]`, then specialized to the tower):

* **Per-factor logarithmic-derivative identity** (`extendDeriv_logDerivOf`): the log-derivative
  `extendDeriv δ g / g` of a polynomial factor `g` (as a rational function) is `(δ g)/g` — the
  building block of every `log gᵢ` term. The all-inputs lift of the example's individual log-argument
  checks. Direct from the keystone `extendDeriv_logDeriv_mk`.
* **Generic log-sum Leibniz reduction** (`extendDeriv_sum_const_logDerivOf`): for δ-constant
  coefficients `cᵢ` and factors `gᵢ`, `extendDeriv δ (∑ᵢ cᵢ·log gᵢ) = ∑ᵢ cᵢ·(δgᵢ)/gᵢ` — the
  differential half of the integral identity, reducing `D(∑ aᵢ log gᵢ)` to the residue sum
  `∑ aᵢ·(Δgᵢ)/gᵢ`, by additivity + the constant-multiple rule + the per-factor identity. This is the
  exact analogue of §2's `deriv_sum_residue_log`, generalized to `extendDeriv δ`.
* **Specialization to the tower** (`towerLogPart_*`): the same two identities over
  `RatFunc (RatFunc ℚ)` with `δ = implicitDeriv (toPolyG Dt)`, i.e. the actual carrier of
  `cResidueResultantTower`/`cLogArgTower`.

**The residue match is now discharged** (`extendDeriv_logPart_eq_div`, and its tower form
`towerLogPart_eq_div_of_const_seed`) in the **primitive** regime: that the residue sum `∑ aᵢ·(Δgᵢ)/gᵢ`
equals the integrand `a/d`. Over a split squarefree `d = ∏(t−αⱼ)`, this is the partial-fraction
`a/d = ∑ⱼ (a(αⱼ)/d'(αⱼ))/(t−αⱼ)` matched against `∑ⱼ cⱼ·Δ(t−αⱼ)/(t−αⱼ)`. In §2 (`d/dx`) the match is
immediate because `Δ(t−αⱼ) = 1`. In §5.6 `Δ(t−αⱼ) = Δt − Δαⱼ`: the assembly works **iff `Δt = Dt` is a
constant of `t`** (`Dt ∈ k`, the primitive/Liouvillian monomial condition — Bronstein Example 5.6.2 has
`Dt = 1/x ∈ ℚ(x)`), since then `Δ(t−αⱼ) = C(Dt − αⱼ′)` is a constant and the §2 partial fraction applies
after the per-root scalar identity `cⱼ·(Dt − αⱼ′) = a(αⱼ)/d'(αⱼ)` (`residue_seed_mul_eq_residue_derivative`
from `deriv_eval_at_simple_root` + `eval_derivative_X_sub_C_mul`). For a **non-constant** `Δt` (e.g.
`Δt = t`, the hyperexponential case) the residue sum exceeds `a/d` by a nonzero **polynomial part** — so
the unqualified `hmatch` is FALSE there, and the constancy hypothesis is the precise dividing line.
The assembly: `sum_residue_seed_logDeriv_eq_div` (per-root partial fraction) → `sum_logDeriv_prod_X_sub_C`
(log-deriv of a product = sum) + fiberwise regrouping → `sum_residue_grouped_logDeriv_eq_div` (the
Rothstein–Trager grouped `hmatch`) → fed into the spine `extendDeriv_logPart_eq_of_residue_match` to give
the **unconditional** `D(∑ c·log gᶜ) = a/d`. The hyperexponential / general non-primitive residue match
remains open (a genuine residual-polynomial-part obstruction, not just plumbing). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-! ### The §5.6 residue criterion with a general derivation seed `Dd` (the RT structure)
`Residues.lean` proves the §2 residue criterion with the *d/dx* derivative `derivative D` as the seed.
The §5.6 residue construction (`cResidueResultantTower`/`cLogArgTower`) uses instead the **monomial
derivative** `Dd = Δd` (`= implicitDeriv Dt d`). These lemmas restate the residue criterion with `Dd`
an *arbitrary* polynomial seed (the §2 proofs used `derivative D` only as an opaque polynomial), so
they apply verbatim to the §5.6 seed: the residue `a(α)/Dd(α)` equals `c` iff `α` is a root of
`a − c·Dd`, and the roots of `gcd(d, a − c·Dd)` are exactly the residue-`c` roots of `d`. This is the
polynomial-level structure underlying `cLogArgTower … c = gcd_t(d, a − c·Dd)`. -/

section ResidueCriterion
variable {F : Type*} [Field F]

/-- **§5.6 residue criterion at a simple root** (seed `Dd` arbitrary): at a root `α` of `d` with
`Dd(α) ≠ 0`, the residue `a(α)/Dd(α)` equals `c` iff `α` is a root of `a − c·Dd`. Generalizes
`residue_eq_iff_isRoot_sub` (which fixes `Dd = derivative d`) to the §5.6 monomial seed
`Dd = Δd`. -/
theorem residue_eq_iff_isRoot_sub_seed (a Dd : F[X]) (c α : F) (hα : Dd.eval α ≠ 0) :
    a.eval α / Dd.eval α = c ↔ (a - C c * Dd).IsRoot α := by
  rw [IsRoot.def, div_eq_iff hα, eval_sub, eval_mul, eval_C, sub_eq_zero]

open scoped Classical in
/-- **§5.6 residue criterion, the gcd characterization** (seed `Dd` arbitrary): the roots of
`gcd(d, a − c·Dd)` are exactly the roots `α` of `d` whose residue `a(α)/Dd(α)` is `c`. Generalizes
`isRoot_gcd_iff_residue` to the §5.6 monomial seed; this is the polynomial structure realized by
`cLogArgTower … c = gcd_t(d, a − c·Dd)`. -/
theorem isRoot_gcd_iff_residue_seed (a d Dd : F[X]) (c α : F) (hα : Dd.eval α ≠ 0) :
    (gcd d (a - C c * Dd)).IsRoot α ↔ (d.IsRoot α ∧ a.eval α / Dd.eval α = c) := by
  rw [← dvd_iff_isRoot, dvd_gcd_iff, dvd_iff_isRoot, dvd_iff_isRoot,
    residue_eq_iff_isRoot_sub_seed a Dd c α hα]

/-- **The monomial-seed residue denominator at a simple root** (the §5.6 ↔ §2 bridge): for a base
derivation `δ` and `d = (X − α)·E`, the §5.6 residue denominator `(δ d)(α)` factors as
`(δ(X − α)).eval(α) · E(α)`. Since `E(α) = d'(α)` (the d/dx residue denominator,
`eval_derivative_X_sub_C_mul`), this is `(δ d)(α) = (δ(X − α)).eval(α) · d'(α)`: the §5.6 residue
`a(α)/(δ d)(α)` and the §2 d/dx residue `a(α)/d'(α)` differ by the factor `(δ(X − α)).eval(α)`,
the eval of the local log-derivative numerator. Pinpoints exactly where the splitting-field residue
match must account for the monomial derivation (the deferred step). For `δ = derivative` this factor is
`1` (`δ(X − α) = 1`), recovering §2. -/
theorem deriv_eval_at_simple_root (δ : Derivation ℤ F[X] F[X]) (E : F[X]) (α : F) :
    (δ ((X - C α) * E)).eval α = (δ (X - C α)).eval α * E.eval α := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, eval_add, eval_mul, eval_mul, eval_sub, eval_X,
    eval_C, sub_self, zero_mul, zero_add, mul_comm]

end ResidueCriterion

/-! ### Per-factor logarithmic-derivative identity (generic base derivation) -/

section Generic
variable {K : Type*} [Field K] [Algebra ℚ K] (δ : Derivation ℤ K[X] K[X])

/-- **Per-factor logarithmic derivative** under the extended derivation `extendDeriv δ`: for a
polynomial factor `g`, the log-derivative `extendDeriv δ (algMap g) / algMap g` is the rational
function `(δ g)/g`. This is the §5.6 building block `D(log gᵢ) = (Δ gᵢ)/gᵢ` — the all-inputs
generalization of the example's per-residue log argument. Restatement of the keystone
`extendDeriv_logDeriv_mk` in residue-criterion phrasing. -/
theorem extendDeriv_logDerivOf (g : K[X]) :
    extendDeriv δ (algebraMap K[X] (RatFunc K) g) / algebraMap K[X] (RatFunc K) g
      = RatFunc.mk (δ g) g :=
  extendDeriv_logDeriv_mk δ g

/-- `extendDeriv δ` kills the image of a δ-constant polynomial: if `δ c = 0` then
`extendDeriv δ (algMap c) = 0`. Used to pull the constant residue coefficients `aᵢ` out of the
log-sum derivative. -/
theorem extendDeriv_algebraMap_of_deriv_eq_zero {c : K[X]} (hc : δ c = 0) :
    extendDeriv δ (algebraMap K[X] (RatFunc K) c) = 0 := by
  rw [extendDeriv_algebraMap, hc, map_zero]

/-- **Constant-multiple rule** for `extendDeriv δ`: if `δ c = 0` (a residue coefficient is a
δ-constant), then `extendDeriv δ (algMap c · y) = algMap c · extendDeriv δ y` — the residue scalar
passes through the derivation. From the Leibniz rule with the constant factor annihilated. -/
theorem extendDeriv_const_mul {c : K[X]} (hc : δ c = 0) (y : RatFunc K) :
    extendDeriv δ (algebraMap K[X] (RatFunc K) c * y)
      = algebraMap K[X] (RatFunc K) c * extendDeriv δ y := by
  rw [Derivation.leibniz, extendDeriv_algebraMap_of_deriv_eq_zero δ hc, smul_zero, add_zero,
    smul_eq_mul]

/-! ### Generic log-sum Leibniz reduction (the differential half of the integral identity)

The §2 `deriv_sum_residue_log` template, generalized to `extendDeriv δ`: modeling each `log gᵢ` by an
abstract `L i` whose log-derivative is `(δ gᵢ)/gᵢ`, the derivative of `∑ᵢ cᵢ·log gᵢ` (δ-constant
coefficients `cᵢ`) is the residue sum `∑ᵢ cᵢ·(δ gᵢ)/gᵢ`. -/

/-- **Log-sum Leibniz reduction** (the §5.6 differential identity, all inputs): for δ-constant residue
coefficients `c i` (`δ (c i) = 0`) and an abstract `log` model `L` with
`extendDeriv δ (L i) = algMap (δ (g i)) / algMap (g i)` (the §5.6 per-factor log-derivative
`extendDeriv_logDerivOf`), the derivative of the logarithmic part `∑ᵢ algMap(cᵢ)·L i` is the residue
sum `∑ᵢ algMap(cᵢ)·algMap(δ gᵢ)/algMap(gᵢ)`. This is `D(∑ aᵢ log gᵢ) = ∑ aᵢ·(Δgᵢ)/gᵢ`, the exact
analogue of §2's `deriv_sum_residue_log` over the tower derivation `extendDeriv δ`; it reduces the
integral identity to matching the residue sum against the integrand `a/d` (the deferred
splitting-field step). -/
theorem extendDeriv_sum_const_logDerivOf {ι : Type*} (s : Finset ι) (c g : ι → K[X])
    (hc : ∀ i ∈ s, δ (c i) = 0) (L : ι → RatFunc K)
    (hL : ∀ i ∈ s, extendDeriv δ (L i)
      = algebraMap K[X] (RatFunc K) (δ (g i)) / algebraMap K[X] (RatFunc K) (g i)) :
    extendDeriv δ (∑ i ∈ s, algebraMap K[X] (RatFunc K) (c i) * L i)
      = ∑ i ∈ s, algebraMap K[X] (RatFunc K) (c i)
          * (algebraMap K[X] (RatFunc K) (δ (g i)) / algebraMap K[X] (RatFunc K) (g i)) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [extendDeriv_const_mul δ (hc i hi), hL i hi]

/-- **Log-sum Leibniz reduction, `RatFunc.mk` form**: the same as `extendDeriv_sum_const_logDerivOf`
but with each residue term written as the rational function `RatFunc.mk (δ gᵢ) gᵢ = (δ gᵢ)/gᵢ` (the
form delivered by the keystone `extendDeriv_logDeriv_mk`), so the right side is literally
`∑ᵢ algMap(cᵢ)·mk (δ gᵢ) gᵢ` — the §5.6 residue sum exactly as `cLogArgTower` produces its factors. -/
theorem extendDeriv_sum_const_logDerivOf_mk {ι : Type*} (s : Finset ι) (c g : ι → K[X])
    (hc : ∀ i ∈ s, δ (c i) = 0) (L : ι → RatFunc K)
    (hL : ∀ i ∈ s, extendDeriv δ (L i)
      = algebraMap K[X] (RatFunc K) (δ (g i)) / algebraMap K[X] (RatFunc K) (g i)) :
    extendDeriv δ (∑ i ∈ s, algebraMap K[X] (RatFunc K) (c i) * L i)
      = ∑ i ∈ s, algebraMap K[X] (RatFunc K) (c i) * RatFunc.mk (δ (g i)) (g i) := by
  rw [extendDeriv_sum_const_logDerivOf δ s c g hc L hL]
  exact Finset.sum_congr rfl fun i _ => by rw [RatFunc.mk_eq_div]

/-- **The §5.6 integral identity, reduced to the residue match** (`D(∑ aᵢ·log gᵢ) = a/d`): for
δ-constant residue coefficients `cᵢ`, log arguments `gᵢ` modeled by `L` (per-factor log-derivative
`hL`), and the **residue-match hypothesis** `hmatch` that the residue sum `∑ᵢ cᵢ·(δ gᵢ)/gᵢ` equals the
integrand `f`, the logarithmic part `∑ᵢ algMap(cᵢ)·log gᵢ` differentiates back to `f` under
`extendDeriv δ`. This is the *complete* §5.6 integral identity once `hmatch` is supplied; the
differential spine (`extendDeriv_sum_const_logDerivOf`) is proved here, and `hmatch` is the single
deferred ingredient — the splitting-field residue match (the tower analogue of §2's partial fraction
`ratFunc_eq_sum_residue_div`), where the residues `cᵢ` and factors `gᵢ` come from the residue
resultant `cResidueResultantTower` and `cLogArgTower`. For `δ = derivative`, `hmatch` is exactly §2's
`ratFunc_eq_sum_residue_gcd`/`ratFunc_eq_sum_residue_div`, so the identity is then unconditional. -/
theorem extendDeriv_logPart_eq_of_residue_match {ι : Type*} (s : Finset ι) (c g : ι → K[X])
    (f : RatFunc K) (hc : ∀ i ∈ s, δ (c i) = 0) (L : ι → RatFunc K)
    (hL : ∀ i ∈ s, extendDeriv δ (L i)
      = algebraMap K[X] (RatFunc K) (δ (g i)) / algebraMap K[X] (RatFunc K) (g i))
    (hmatch : ∑ i ∈ s, algebraMap K[X] (RatFunc K) (c i)
        * (algebraMap K[X] (RatFunc K) (δ (g i)) / algebraMap K[X] (RatFunc K) (g i)) = f) :
    extendDeriv δ (∑ i ∈ s, algebraMap K[X] (RatFunc K) (c i) * L i) = f := by
  rw [extendDeriv_sum_const_logDerivOf δ s c g hc L hL, hmatch]

end Generic

/-! ### The residue match in the primitive (`δt ∈ k`) case (discharging `hmatch`)

The residue sum `∑ᵢ cᵢ·(δ gᵢ)/gᵢ` equals the integrand `a/d` **only when** `δ` sends each linear
factor `X − α` (over the splitting field) to a *constant* — equivalently `δX = δt` is a constant of
`t`, the **primitive/Liouvillian monomial condition** `Dt ∈ k`. This is exactly Bronstein's §5.6
regime (Example 5.6.2 has `Dt = 1/x ∈ k = ℚ(x)`): then `δ(X − Cα) = C(b α)` is a genuine constant, so
`cᵢ·(δ gᵢ)/gᵢ` is *proper* and the §2 partial fraction `ratFunc_eq_sum_residue_div` applies after the
per-root scalar identity `res(α)·b α = A(α)/d'(α)` (from `deriv_eval_at_simple_root` +
`eval_derivative_X_sub_C_mul`). For a *non-constant* `δt` (e.g. `δt = t`, the hyperexponential case)
the residue sum exceeds `a/d` by a nonzero **polynomial part**, so the unqualified `hmatch` is **false**
there — the constancy hypothesis `hb` below is the precise dividing line. -/

section ResidueMatch
open Polynomial
variable {K : Type*} [Field K] [Algebra ℚ K] (δ : Derivation ℤ K[X] K[X])

omit [Algebra ℚ K] in
/-- **The per-root scalar identity** (steps 3+4 of the residue match): at a simple root `α` of
`d = nodal s id`, if the monomial derivation sends the linear factor to the *constant* `δ(X − Cα) = C b`
with `b ≠ 0` (the primitive condition `δt ∈ k`, normality), then the §5.6 residue `A(α)/(δ d)(α)` scaled
by `b` equals the §2 d/dx residue `A(α)/d'(α)`: `(A(α)/(δ d)(α))·b = A(α)/d'(α)`. From
`deriv_eval_at_simple_root` (`(δ d)(α) = (δ(X−Cα))(α)·E(α)`) and `eval_derivative_X_sub_C_mul`
(`E(α) = d'(α)`), so `(δ d)(α) = b·d'(α)` and the `b` cancels. -/
theorem residue_seed_mul_eq_residue_derivative (A : K[X]) (s : Finset K) {α b : K} (hα : α ∈ s)
    (hb : δ (X - C α) = C b) (hb0 : b ≠ 0) :
    A.eval α / (δ (Lagrange.nodal s id)).eval α * b
      = A.eval α / eval α (derivative (Lagrange.nodal s id)) := by
  classical
  set d := Lagrange.nodal s id with hd
  -- `d = (X − α)·E` where `E = d / (X − α) = ∏_{j≠α}(X − j)`
  have hdvd : (X - C α) ∣ d := by
    rw [hd, Lagrange.nodal_eq]; exact Finset.dvd_prod_of_mem _ hα
  set E := d / (X - C α) with hE
  have hfac : d = (X - C α) * E := (EuclideanDomain.mul_div_cancel' (X_sub_C_ne_zero α) hdvd).symm
  -- `(δ d)(α) = b·E(α)` via the simple-root bridge `deriv_eval_at_simple_root` and `hb`
  have hδd : (δ d).eval α = b * E.eval α := by
    rw [hfac, deriv_eval_at_simple_root δ E α, hb, eval_C]
  -- `d'(α) = E(α)` (the d/dx residue denominator)
  have hd' : eval α (derivative d) = E.eval α := by rw [hfac, eval_derivative_X_sub_C_mul]
  rw [hδd, hd']
  field_simp

omit [Algebra ℚ K] in
/-- **The §5.6 residue match over individual roots** (the discharged `hmatch`, primitive case): for
`A` of degree `< #s` over the split squarefree `d = nodal s id = ∏_{α∈s}(X−α)`, and a base derivation
`δ` sending each linear factor to a *constant* `δ(X − Cα) = C (b α)` with `b α ≠ 0` (the primitive
condition `δt ∈ k`), the residue sum equals the integrand:
`∑_{α∈s} algMap(C(res α))·(algMap(δ(X−Cα))/algMap(X−Cα)) = algMap(A)/algMap(d)`, with the §5.6 residue
`res α = A(α)/(δ d)(α)`. Assembled from the §2 partial fraction `ratFunc_eq_sum_residue_div`
(`a/d = ∑ (A(α)/d'(α))/(X−α)`) and the per-root scalar identity
`residue_seed_mul_eq_residue_derivative` (`res α·b α = A(α)/d'(α)`), which fold each tower term
`C(res α)·C(b α)/(X−α)` into the §2 term `C(A(α)/d'(α))/(X−α)`. This is the precise tower analogue of
`deriv_sum_residue_log`'s partial fraction; its constancy hypothesis `hb` is exactly where a
non-primitive (`δt ∉ k`) derivation would leave a residual polynomial part. -/
theorem sum_residue_seed_logDeriv_eq_div (A : K[X]) (s : Finset K) (hA : A.degree < s.card)
    (b : K → K) (hb : ∀ α ∈ s, δ (X - C α) = C (b α)) (hb0 : ∀ α ∈ s, b α ≠ 0) :
    ∑ α ∈ s, algebraMap K[X] (RatFunc K)
          (C (A.eval α / (δ (Lagrange.nodal s id)).eval α))
        * (algebraMap K[X] (RatFunc K) (δ (X - C α))
            / algebraMap K[X] (RatFunc K) (X - C α))
      = algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id) := by
  classical
  rw [ratFunc_eq_sum_residue_div s A hA]
  refine Finset.sum_congr rfl fun α hα => ?_
  -- fold the tower term `C(res α)·(C(b α)/(X−α))` into the §2 term `C(A(α)/d'(α))/(X−α)`
  rw [hb α hα, ← mul_div_assoc, ← map_mul, ← C_mul,
    residue_seed_mul_eq_residue_derivative δ A s hα (hb α hα) (hb0 α hα)]

omit [Algebra ℚ K] in
/-- **Log-derivative of a product of linear factors** (as a ratio of `δ`-images): for a finite set `t`
of *distinct* points, `algMap(δ(∏_{α∈t}(X−Cα)))/algMap(∏_{α∈t}(X−Cα)) = ∑_{α∈t} algMap(δ(X−Cα))/algMap(X−Cα)`
— the log-derivative of a product is the sum of log-derivatives. The bridge between a grouped
Rothstein–Trager argument `gᵢ = ∏_{res=cᵢ}(X−α)` and the per-root residue sum. Proved by
`Finset.cons_induction`, the base `Derivation.leibniz` rule, and that each `X − Cα` (and the product)
is nonzero. -/
theorem sum_logDeriv_prod_X_sub_C (t : Finset K) :
    algebraMap K[X] (RatFunc K) (δ (∏ α ∈ t, (X - C α)))
        / algebraMap K[X] (RatFunc K) (∏ α ∈ t, (X - C α))
      = ∑ α ∈ t, algebraMap K[X] (RatFunc K) (δ (X - C α))
          / algebraMap K[X] (RatFunc K) (X - C α) := by
  classical
  induction t using Finset.cons_induction with
  | empty => simp
  | cons a t ha ih =>
    have hinj := RatFunc.algebraMap_injective K
    -- abbreviations: `P = ∏_{α∈t}(X−Cα)`, both `X−Ca` and `P` are nonzero in `RatFunc K`
    set P : K[X] := ∏ α ∈ t, (X - C α) with hP
    have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.mpr fun α _ => X_sub_C_ne_zero α
    have haP : algebraMap K[X] (RatFunc K) (X - C a) ≠ 0 :=
      (map_ne_zero_iff _ hinj).mpr (X_sub_C_ne_zero a)
    have hPP : algebraMap K[X] (RatFunc K) P ≠ 0 := (map_ne_zero_iff _ hinj).mpr hP0
    -- expand `δ((X−Ca)·P) = δ(X−Ca)·P + (X−Ca)·δP` (Leibniz on the base derivation), push through algMap
    rw [Finset.prod_cons, Finset.sum_cons, ← ih, ← hP, Derivation.leibniz, smul_eq_mul,
      smul_eq_mul, map_add, map_mul, map_mul, map_mul]
    field_simp
    ring

omit [Algebra ℚ K] in
open scoped Classical in
/-- **The §5.6 grouped residue match** (the discharged `hmatch`, the Rothstein–Trager headline form):
for `A` of degree `< #s` over the split squarefree `d = nodal s id = ∏_{α∈s}(X−α)`, and a base
derivation `δ` sending each linear factor to a *constant* `δ(X − Cα) = C (b α)` with `b α ≠ 0` (the
primitive condition `δt ∈ k`), the **residue-grouped** sum equals the integrand:
`∑_{c ∈ residues} algMap(C c)·(algMap(δ gᶜ)/algMap(gᶜ)) = algMap(A)/algMap(d)`, where `c` ranges over
the distinct residues `s.image res` (`res α = A(α)/(δ d)(α)`) and `gᶜ = ∏_{α: res α = c}(X−α)` is the
Rothstein–Trager log argument. This is exactly the `hmatch` of `extendDeriv_logPart_eq_of_residue_match`
with `c = C c` and `g = gᶜ`. Assembled from `sum_logDeriv_prod_X_sub_C` (each `δ gᶜ/gᶜ` is the per-root
sum), the fiberwise regrouping `Finset.sum_fiberwise_of_maps_to`, and `sum_residue_seed_logDeriv_eq_div`.
The §5.6 analogue of §2's `ratFunc_eq_sum_residue_gcd`. -/
theorem sum_residue_grouped_logDeriv_eq_div (A : K[X]) (s : Finset K) (hA : A.degree < s.card)
    (b : K → K) (hb : ∀ α ∈ s, δ (X - C α) = C (b α)) (hb0 : ∀ α ∈ s, b α ≠ 0) :
    ∑ c ∈ s.image (fun α => A.eval α / (δ (Lagrange.nodal s id)).eval α),
        algebraMap K[X] (RatFunc K) (C c)
          * (algebraMap K[X] (RatFunc K)
                (δ (∏ α ∈ s.filter
                      (fun α => A.eval α / (δ (Lagrange.nodal s id)).eval α = c), (X - C α)))
              / algebraMap K[X] (RatFunc K)
                (∏ α ∈ s.filter
                      (fun α => A.eval α / (δ (Lagrange.nodal s id)).eval α = c), (X - C α)))
      = algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id) := by
  classical
  set res : K → K := fun α => A.eval α / (δ (Lagrange.nodal s id)).eval α with hres
  -- the residue match over individual roots is the target after regrouping
  rw [← sum_residue_seed_logDeriv_eq_div δ A s hA b hb hb0,
    ← Finset.sum_fiberwise_of_maps_to (g := res) (t := s.image res)
      (fun α hα => Finset.mem_image_of_mem _ hα)
      (f := fun α => algebraMap K[X] (RatFunc K) (C (res α))
        * (algebraMap K[X] (RatFunc K) (δ (X - C α))
            / algebraMap K[X] (RatFunc K) (X - C α)))]
  -- per residue value `c`: the product log-derivative splits into the fiber's per-root sum
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [sum_logDeriv_prod_X_sub_C δ (s.filter (fun α => res α = c)), Finset.mul_sum]
  exact Finset.sum_congr rfl fun α hα => by rw [(Finset.mem_filter.mp hα).2]

open scoped Classical in
/-- **The §5.6 integral identity, unconditional in the primitive case** (`D(∑ c·log gᶜ) = a/d`, the
discharged Rothstein–Trager headline): for `A` of degree `< #s` over the split squarefree
`d = nodal s id = ∏_{α∈s}(X−α)`, with a base derivation `δ` whose action on each linear factor is a
*constant* `δ(X − Cα) = C (b α)`, `b α ≠ 0` (the primitive condition `δt ∈ k`) and whose residues
`c ∈ s.image res` are δ-constants (`δ (C c) = 0`), the logarithmic part `∑_c algMap(C c)·log gᶜ` —
with `gᶜ = ∏_{α: res α = c}(X−α)` the Rothstein–Trager log argument and each `log gᶜ` modeled by `L c`
with the per-factor log-derivative `hL` — differentiates back to the integrand `A/d` under
`extendDeriv δ`, **with no residue-match hypothesis**: the residue match is supplied internally by
`sum_residue_grouped_logDeriv_eq_div`. This is `extendDeriv_logPart_eq_of_residue_match` with the
deferred `hmatch` discharged. -/
theorem extendDeriv_logPart_eq_div (A : K[X]) (s : Finset K) (hA : A.degree < s.card)
    (b : K → K) (hb : ∀ α ∈ s, δ (X - C α) = C (b α)) (hb0 : ∀ α ∈ s, b α ≠ 0)
    (hc : ∀ c ∈ s.image (fun α => A.eval α / (δ (Lagrange.nodal s id)).eval α), δ (C c) = 0)
    (L : K → RatFunc K)
    (hL : ∀ c ∈ s.image (fun α => A.eval α / (δ (Lagrange.nodal s id)).eval α),
      extendDeriv δ (L c)
        = algebraMap K[X] (RatFunc K)
              (δ (∏ α ∈ s.filter
                    (fun α => A.eval α / (δ (Lagrange.nodal s id)).eval α = c), (X - C α)))
            / algebraMap K[X] (RatFunc K)
              (∏ α ∈ s.filter
                    (fun α => A.eval α / (δ (Lagrange.nodal s id)).eval α = c), (X - C α))) :
    extendDeriv δ (∑ c ∈ s.image (fun α => A.eval α / (δ (Lagrange.nodal s id)).eval α),
        algebraMap K[X] (RatFunc K) (C c) * L c)
      = algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id) :=
  extendDeriv_logPart_eq_of_residue_match δ
    (s.image (fun α => A.eval α / (δ (Lagrange.nodal s id)).eval α))
    (fun c => C c)
    (fun c => ∏ α ∈ s.filter
        (fun α => A.eval α / (δ (Lagrange.nodal s id)).eval α = c), (X - C α))
    _ hc L hL (sum_residue_grouped_logDeriv_eq_div δ A s hA b hb hb0)

end ResidueMatch

/-! ### The d/dx specialization: the generic spine recovers §2's full integral identity
Taking the base derivation `δ = derivative'` (Mathlib's `Polynomial.derivative` as a `Derivation`),
`extendDeriv derivative'` is the d/dx derivation on `RatFunc K` — equal to the repo's `ratFuncDeriv`
(both extend `derivative` on `K[X]`, so they coincide by `derivation_ext_fractionRing`). This lets the
§2 *rational* Rothstein–Trager integral identity (`ratFunc_eq_sum_residue_gcd`,
`deriv_sum_residue_log`) compose with the generic spine above: the **complete** integral identity
`D(∑ a·log gₐ) = A/D` holds for d/dx, with the residue match supplied by §2's partial fraction. This
is the end-to-end anchor; the tower case (§5.6) reuses the *same* spine (`extendDeriv δ`,
`extendDeriv_sum_const_logDerivOf`) with `δ` the monomial derivation, the only missing piece being the
tower analogue of the §2 residue match (the deferred splitting-field step). -/

section Ddx
variable {K : Type*} [Field K] [Algebra ℚ K]

/-- `Polynomial.derivative` packaged as a `Derivation ℤ K[X] K[X]` (Mathlib's `K`-derivation
`derivative'` restricted to the base `ℤ`). The d/dx base derivation, so
`extendDeriv derivativeDerivation` is d/dx on `RatFunc K`. -/
noncomputable def derivativeDerivation : Derivation ℤ K[X] K[X] :=
  (Polynomial.derivative' (R := K)).restrictScalars ℤ

omit [Algebra ℚ K] in
@[simp] theorem derivativeDerivation_apply (p : K[X]) :
    derivativeDerivation p = derivative p := rfl

omit [Algebra ℚ K] in
/-- **`extendDeriv derivativeDerivation` is d/dx on `RatFunc K`**, at the function level: it computes
the repo's `ratFuncDeriv` (the §2 d/dx derivation) on every rational function. Both are the quotient
rule with `derivative` as the base (`extendDerivFun_mk`/`ratFuncDeriv_mk`), so they agree on each
`RatFunc.mk p q` by `RatFunc.induction_on'`. (Stated at the function level to side-step the field
`Module ℤ` diamond on the bundled `Derivation`.) -/
theorem extendDerivFun_derivativeDerivation (x : RatFunc K) :
    extendDerivFun (derivativeDerivation (K := K)) x = ratFuncDeriv x := by
  induction x using RatFunc.induction_on' with | _ p q hq =>
  rw [extendDerivFun_mk, ratFuncDeriv_mk, derivativeDerivation_apply, derivativeDerivation_apply]

/-- **`extendDeriv derivativeDerivation` is d/dx**, applied form: `extendDeriv derivativeDerivation x`
equals `ratFuncDeriv x` (the d/dx derivation underlying the §2 `Differential (RatFunc K)` instance). -/
theorem extendDeriv_derivativeDerivation_apply (x : RatFunc K) :
    extendDeriv (derivativeDerivation (K := K)) x = ratFuncDeriv x := by
  rw [extendDeriv_apply, extendDerivFun_derivativeDerivation]

end Ddx

/-- Headline restatement: the §5.6 per-factor log-derivative `D(log gᵢ) = (Δ gᵢ)/gᵢ` over the tower
derivation `extendDeriv δ`. -/
example {K : Type*} [Field K] [Algebra ℚ K] (δ : Derivation ℤ K[X] K[X]) (g : K[X]) :
    extendDeriv δ (algebraMap K[X] (RatFunc K) g) / algebraMap K[X] (RatFunc K) g
      = RatFunc.mk (δ g) g :=
  extendDeriv_logDerivOf δ g

/-- Headline restatement: the §5.6 log-sum Leibniz reduction `D(∑ aᵢ·log gᵢ) = ∑ aᵢ·(Δ gᵢ)/gᵢ` for
δ-constant residue coefficients `aᵢ`, over the tower derivation `extendDeriv δ`. -/
example {K : Type*} [Field K] [Algebra ℚ K] (δ : Derivation ℤ K[X] K[X]) {ι : Type*} (s : Finset ι)
    (c g : ι → K[X]) (hc : ∀ i ∈ s, δ (c i) = 0) (L : ι → RatFunc K)
    (hL : ∀ i ∈ s, extendDeriv δ (L i)
      = algebraMap K[X] (RatFunc K) (δ (g i)) / algebraMap K[X] (RatFunc K) (g i)) :
    extendDeriv δ (∑ i ∈ s, algebraMap K[X] (RatFunc K) (c i) * L i)
      = ∑ i ∈ s, algebraMap K[X] (RatFunc K) (c i)
          * (algebraMap K[X] (RatFunc K) (δ (g i)) / algebraMap K[X] (RatFunc K) (g i)) :=
  extendDeriv_sum_const_logDerivOf δ s c g hc L hL

/-! ### Specialization to the genuine tower fraction field `RatFunc (RatFunc ℚ)`
The §5.6 identities on the *actual* carrier of `cResidueResultantTower`/`cLogArgTower`: the tower
derivation `towerFractionFieldDeriv Dt = extendDeriv (implicitDeriv (toPolyG Dt))` on
`RatFunc (RatFunc ℚ)`, with the monomial base `Δ = implicitDeriv (toPolyG Dt)`. -/

open CPolyG

/-- The engine carrier `CFieldSpec.K QFunNZ` is `RatFunc ℚ`, a `ℚ`-algebra. Re-declared as a local
instance (matching the keystone's) so the tower specialization synthesizes the **same** `Algebra ℚ`
as `towerFractionFieldDeriv`, avoiding an instance-mismatch detour. -/
noncomputable local instance : Algebra ℚ (CFieldSpec.K QFunNZ) :=
  inferInstanceAs (Algebra ℚ (RatFunc ℚ))

/-- **The §5.6 per-factor log-derivative on the tower**: for a log argument `g ∈ (RatFunc ℚ)[X]` (e.g.
the `gcd_t(d, a − c·Dd)` produced by `cLogArgTower`), the log-derivative of `g` under the tower
derivation `towerFractionFieldDeriv Dt` is `(Δ g)/g` with `Δ = implicitDeriv (toPolyG Dt)` the monomial
derivation. The all-inputs generalization of `logPartTower_example`'s per-residue log-argument check,
on the genuine tower fraction field. The keystone `towerFractionFieldDeriv_logDeriv`, restated in
residue-criterion phrasing. -/
theorem towerLogPart_logDerivOf (Dt : CPolyG QFunNZ) (g : (CFieldSpec.K QFunNZ)[X]) :
    towerFractionFieldDeriv Dt (algebraMap _ (RatFunc (CFieldSpec.K QFunNZ)) g)
        / algebraMap _ (RatFunc (CFieldSpec.K QFunNZ)) g
      = RatFunc.mk (Differential.implicitDeriv (toPolyG Dt) g) g :=
  towerFractionFieldDeriv_logDeriv Dt g

/-- **The §5.6 log-sum Leibniz reduction on the tower** (`D(∑ aᵢ·log gᵢ) = ∑ aᵢ·(Δ gᵢ)/gᵢ`): for the
monomial-derivation tower `RatFunc (RatFunc ℚ)`, with δ-constant residue coefficients `cᵢ` and log
arguments `gᵢ ∈ (RatFunc ℚ)[X]` modeled by `L`, the derivative of the logarithmic part
`∑ᵢ algMap(cᵢ)·log gᵢ` is the residue sum `∑ᵢ algMap(cᵢ)·(Δ gᵢ)/gᵢ` under `towerFractionFieldDeriv Dt`.
The differential half of the §5.6 integral identity over the genuine tower fraction field — the
all-inputs generalization of `logPartTower_example` to the integral form `D(∑ aᵢ log gᵢ) = a/d` (the
residue match against `a/d` being the deferred splitting-field step). Proved by `map_sum` + the
constant-multiple rule (`Derivation.leibniz` with the δ-constant factor killed via
`towerFractionFieldDeriv_algebraMap`) + the per-factor `hL`. -/
theorem towerLogPart_sum_const_logDerivOf (Dt : CPolyG QFunNZ) {ι : Type*} (s : Finset ι)
    (c g : ι → (CFieldSpec.K QFunNZ)[X])
    (hc : ∀ i ∈ s, Differential.implicitDeriv (toPolyG Dt) (c i) = 0)
    (L : ι → RatFunc (CFieldSpec.K QFunNZ))
    (hL : ∀ i ∈ s, towerFractionFieldDeriv Dt (L i)
      = algebraMap _ (RatFunc (CFieldSpec.K QFunNZ)) (Differential.implicitDeriv (toPolyG Dt) (g i))
          / algebraMap _ (RatFunc (CFieldSpec.K QFunNZ)) (g i)) :
    towerFractionFieldDeriv Dt (∑ i ∈ s, algebraMap _ (RatFunc (CFieldSpec.K QFunNZ)) (c i) * L i)
      = ∑ i ∈ s, algebraMap _ (RatFunc (CFieldSpec.K QFunNZ)) (c i)
          * (algebraMap _ (RatFunc (CFieldSpec.K QFunNZ)) (Differential.implicitDeriv (toPolyG Dt) (g i))
              / algebraMap _ (RatFunc (CFieldSpec.K QFunNZ)) (g i)) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Derivation.leibniz, towerFractionFieldDeriv_algebraMap, hc i hi, map_zero, smul_zero,
    add_zero, smul_eq_mul, hL i hi]

/-- **The §5.6 integral identity on the tower, reduced to the residue match**
(`D(∑ aᵢ·log gᵢ) = f`): on the genuine tower fraction field `RatFunc (RatFunc ℚ)`, given δ-constant
residue coefficients `cᵢ`, log arguments `gᵢ` modeled by `L`, and the **residue-match hypothesis**
`hmatch : ∑ᵢ cᵢ·(Δ gᵢ)/gᵢ = f`, the logarithmic part differentiates back to `f` under
`towerFractionFieldDeriv Dt`. The complete §5.6 integral identity on the tower modulo `hmatch` (the
deferred splitting-field residue match), with the residues/arguments those of
`cResidueResultantTower`/`cLogArgTower`. -/
theorem towerLogPart_eq_of_residue_match (Dt : CPolyG QFunNZ) {ι : Type*} (s : Finset ι)
    (c g : ι → (CFieldSpec.K QFunNZ)[X]) (f : RatFunc (CFieldSpec.K QFunNZ))
    (hc : ∀ i ∈ s, Differential.implicitDeriv (toPolyG Dt) (c i) = 0)
    (L : ι → RatFunc (CFieldSpec.K QFunNZ))
    (hL : ∀ i ∈ s, towerFractionFieldDeriv Dt (L i)
      = algebraMap _ (RatFunc (CFieldSpec.K QFunNZ)) (Differential.implicitDeriv (toPolyG Dt) (g i))
          / algebraMap _ (RatFunc (CFieldSpec.K QFunNZ)) (g i))
    (hmatch : ∑ i ∈ s, algebraMap _ (RatFunc (CFieldSpec.K QFunNZ)) (c i)
        * (algebraMap _ (RatFunc (CFieldSpec.K QFunNZ)) (Differential.implicitDeriv (toPolyG Dt) (g i))
            / algebraMap _ (RatFunc (CFieldSpec.K QFunNZ)) (g i)) = f) :
    towerFractionFieldDeriv Dt (∑ i ∈ s, algebraMap _ (RatFunc (CFieldSpec.K QFunNZ)) (c i) * L i)
      = f := by
  rw [towerLogPart_sum_const_logDerivOf Dt s c g hc L hL, hmatch]

open scoped Classical Differential in
/-- **The §5.6 integral identity on the tower, unconditional in the primitive case**
(`D(∑ c·log gᶜ) = a/d`): on the genuine tower fraction field `RatFunc (RatFunc ℚ)`, when the monomial
derivative seed is a *constant* `toPolyG Dt = C w₀` (the primitive condition `Dt ∈ k = ℚ(x)`, e.g.
Bronstein Example 5.6.2 with `Dt = 1/x`), for `A` of degree `< #s` over the split squarefree
`d = nodal s id`, with residues `c ∈ s.image res` δ-constant and normality `w₀ ≠ α′` at each root, the
logarithmic part `∑_c algMap(C c)·log gᶜ` (`gᶜ = ∏_{res α = c}(X−α)` the Rothstein–Trager log argument,
each `log gᶜ` modeled by `L c` with the per-factor `hL`) differentiates back to the integrand `A/d`
under `towerFractionFieldDeriv Dt`, **with no residue-match hypothesis** — `hmatch` discharged via the
generic `extendDeriv_logPart_eq_div` with the primitive constancy `δ(X − Cα) = C(w₀ − α′)`
(`implicitDeriv_X_sub_C`). The unconditional discharge of `towerLogPart_eq_of_residue_match` in the
primitive regime, on the actual carrier of `cResidueResultantTower`/`cLogArgTower`. -/
theorem towerLogPart_eq_div_of_const_seed (Dt : CPolyG QFunNZ) {w₀ : CFieldSpec.K QFunNZ}
    (htop : toPolyG Dt = C w₀) (A : (CFieldSpec.K QFunNZ)[X]) (s : Finset (CFieldSpec.K QFunNZ))
    (hA : A.degree < s.card)
    (hb0 : ∀ α ∈ s, w₀ - α′ ≠ 0)
    (hc : ∀ c ∈ s.image
            (fun α => A.eval α / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval α),
          Differential.implicitDeriv (toPolyG Dt) (C c) = 0)
    (L : CFieldSpec.K QFunNZ → RatFunc (CFieldSpec.K QFunNZ))
    (hL : ∀ c ∈ s.image
            (fun α => A.eval α / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval α),
          towerFractionFieldDeriv Dt (L c)
            = algebraMap _ (RatFunc (CFieldSpec.K QFunNZ))
                  (Differential.implicitDeriv (toPolyG Dt)
                    (∏ α ∈ s.filter (fun α => A.eval α
                        / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval α = c),
                      (X - C α)))
              / algebraMap _ (RatFunc (CFieldSpec.K QFunNZ))
                  (∏ α ∈ s.filter (fun α => A.eval α
                      / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval α = c),
                    (X - C α))) :
    towerFractionFieldDeriv Dt (∑ c ∈ s.image
          (fun α => A.eval α / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval α),
        algebraMap _ (RatFunc (CFieldSpec.K QFunNZ)) (C c) * L c)
      = algebraMap _ (RatFunc (CFieldSpec.K QFunNZ)) A
          / algebraMap _ (RatFunc (CFieldSpec.K QFunNZ)) (Lagrange.nodal s id) :=
  extendDeriv_logPart_eq_div (Differential.implicitDeriv (toPolyG Dt)) A s hA
    (fun α => w₀ - α′)
    (fun α _ => by rw [implicitDeriv_X_sub_C, htop, ← C_sub]) hb0 hc L hL

/-- Headline restatement: the §5.6 per-factor log-derivative on the genuine tower carrier. -/
example (Dt : CPolyG QFunNZ) (g : (CFieldSpec.K QFunNZ)[X]) :
    towerFractionFieldDeriv Dt (algebraMap _ (RatFunc (CFieldSpec.K QFunNZ)) g)
        / algebraMap _ (RatFunc (CFieldSpec.K QFunNZ)) g
      = RatFunc.mk (Differential.implicitDeriv (toPolyG Dt) g) g :=
  towerLogPart_logDerivOf Dt g

open scoped Classical in
/-- Headline restatement: the §5.6 residue criterion `roots(gcd(d, a−c·Dd)) = residue-c roots of d`,
with the seed `Dd` arbitrary (so it covers the monomial seed `Δd` of `cLogArgTower`). -/
example {F : Type*} [Field F] (a d Dd : F[X]) (c α : F) (hα : Dd.eval α ≠ 0) :
    (gcd d (a - C c * Dd)).IsRoot α ↔ (d.IsRoot α ∧ a.eval α / Dd.eval α = c) :=
  isRoot_gcd_iff_residue_seed a d Dd c α hα

open scoped Classical in
/-- Headline restatement: the §5.6 **discharged** residue match (the integrand `A/d` is exactly the
residue-grouped sum) for a base derivation primitive on every linear factor. -/
example {K : Type*} [Field K] [Algebra ℚ K] (δ : Derivation ℤ K[X] K[X]) (A : K[X]) (s : Finset K)
    (hA : A.degree < s.card) (b : K → K) (hb : ∀ α ∈ s, δ (X - C α) = C (b α))
    (hb0 : ∀ α ∈ s, b α ≠ 0) :
    ∑ c ∈ s.image (fun α => A.eval α / (δ (Lagrange.nodal s id)).eval α),
        algebraMap K[X] (RatFunc K) (C c)
          * (algebraMap K[X] (RatFunc K)
                (δ (∏ α ∈ s.filter
                      (fun α => A.eval α / (δ (Lagrange.nodal s id)).eval α = c), (X - C α)))
              / algebraMap K[X] (RatFunc K)
                (∏ α ∈ s.filter
                      (fun α => A.eval α / (δ (Lagrange.nodal s id)).eval α = c), (X - C α)))
      = algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id) :=
  sum_residue_grouped_logDeriv_eq_div δ A s hA b hb hb0

open scoped Classical Differential in
/-- Headline restatement: the §5.6 unconditional log-part integral identity on the genuine tower
carrier `RatFunc (RatFunc ℚ)` for a constant (primitive) seed `toPolyG Dt = C w₀`. -/
example (Dt : CPolyG QFunNZ) {w₀ : CFieldSpec.K QFunNZ} (htop : toPolyG Dt = C w₀)
    (A : (CFieldSpec.K QFunNZ)[X]) (s : Finset (CFieldSpec.K QFunNZ)) (hA : A.degree < s.card)
    (hb0 : ∀ α ∈ s, w₀ - α′ ≠ 0)
    (hc : ∀ c ∈ s.image
            (fun α => A.eval α / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval α),
          Differential.implicitDeriv (toPolyG Dt) (C c) = 0)
    (L : CFieldSpec.K QFunNZ → RatFunc (CFieldSpec.K QFunNZ))
    (hL : ∀ c ∈ s.image
            (fun α => A.eval α / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval α),
          towerFractionFieldDeriv Dt (L c)
            = algebraMap _ (RatFunc (CFieldSpec.K QFunNZ))
                  (Differential.implicitDeriv (toPolyG Dt)
                    (∏ α ∈ s.filter (fun α => A.eval α
                        / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval α = c),
                      (X - C α)))
              / algebraMap _ (RatFunc (CFieldSpec.K QFunNZ))
                  (∏ α ∈ s.filter (fun α => A.eval α
                      / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval α = c),
                    (X - C α))) :
    towerFractionFieldDeriv Dt (∑ c ∈ s.image
          (fun α => A.eval α / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval α),
        algebraMap _ (RatFunc (CFieldSpec.K QFunNZ)) (C c) * L c)
      = algebraMap _ (RatFunc (CFieldSpec.K QFunNZ)) A
          / algebraMap _ (RatFunc (CFieldSpec.K QFunNZ)) (Lagrange.nodal s id) :=
  towerLogPart_eq_div_of_const_seed Dt htop A s hA hb0 hc L hL

#print axioms residue_eq_iff_isRoot_sub_seed
#print axioms isRoot_gcd_iff_residue_seed
#print axioms residue_seed_mul_eq_residue_derivative
#print axioms sum_residue_seed_logDeriv_eq_div
#print axioms sum_logDeriv_prod_X_sub_C
#print axioms sum_residue_grouped_logDeriv_eq_div
#print axioms extendDeriv_logPart_eq_div
#print axioms towerLogPart_eq_div_of_const_seed
#print axioms deriv_eval_at_simple_root
#print axioms extendDeriv_logDerivOf
#print axioms extendDeriv_sum_const_logDerivOf
#print axioms extendDeriv_sum_const_logDerivOf_mk
#print axioms extendDeriv_derivativeDerivation_apply
#print axioms extendDeriv_logPart_eq_of_residue_match
#print axioms towerLogPart_logDerivOf
#print axioms towerLogPart_sum_const_logDerivOf
#print axioms towerLogPart_eq_of_residue_match

end DeepWiki.SymbolicIntegration
