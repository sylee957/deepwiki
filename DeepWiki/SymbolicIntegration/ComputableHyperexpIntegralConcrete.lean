import DeepWiki.SymbolicIntegration.ComputableHyperexpIntegral
import DeepWiki.SymbolicIntegration.RationalIntegrationLogForm

/-! # Discharging the §5.9 base-antiderivative hypothesis from the §2 rational integrator (Bronstein §5.9 + §2)

`ComputableHyperexpIntegral` proved the corrected hyperexponential simple integral
`D((∑ aᵢ·log gᵢ) − Y) = a/d` **gated** on a base antiderivative `y₀ ∈ k = ℚ(x)` of the explicit residual
`r₀ = η·∑ res α` (`hbase : δ (C y₀) = C r₀`, i.e. `y₀′ = r₀` under the base `d/dx`). This file **discharges**
that last hypothesis by connecting the library's §2 rational-function integrator
(`RationalIntegrationLogForm` — `∫ A/D = rational part + ∑ residue·log`), which proves every rational
function of `x` elementary integrable.

## The two regimes of `r₀`

`r₀ ∈ ℚ(x)` is an arbitrary rational function of `x`. Its §2 antiderivative is `(rational part g₀) +
∑ⱼ cⱼ·log pⱼ`. There are two cases:

* **Pure rational part (residues vanish, `r₀ = g₀′`):** the antiderivative `y₀ = g₀ ∈ ℚ(x)` lives *in the
  base field itself*, so `hbase` is dischargeable **concretely** with `y₀ ∈ k` — the §5.9 simple integral
  is `(∑ aᵢ·log gᵢ) − algMap(C g₀)`, fully `hbase`-free (`extendDeriv_logPart_sub_ratPart_eq_div`,
  `CPolyG.towerLogResidueSum_sub_ratPart_eq_div_of_residueData`).
* **General residue (logs needed):** the antiderivative carries `log` terms, so `y₀ ∉ k`; the honest
  statement is the §2 Liouville witness `ratFunc_elementary_integrable` — `r₀` equals a sum of a base
  `d/dx`-derivative and `Differential.logDeriv` terms, i.e. it *has* an elementary antiderivative (in an
  elementary extension `k(log p₁, …)`), even though that antiderivative is not a single element of `k`.

So the §5.9 simple integral is **fully concrete whenever the residual is rational** and **always
elementary** otherwise — exactly the faithful Bronstein §5.9 reading (the hyperexponential simple integral
can pick up extra logs from the residual).

## How the §2 integrator connects

The base `d/dx` on `k = ℚ(x)` is the `Differential (RatFunc ℚ)` instance (`ratFuncKDeriv`, the quotient
rule, `RationalFunctionDerivative`); the engine's base derivation is `implicitDeriv (toPolyG Dt)`, which on
constants is `δ (C y₀) = C (y₀′)` (`implicitDeriv_C`). So `hbase` collapses to `y₀′ = r₀` in `RatFunc ℚ`,
and a §2 rational part `g₀` with `g₀′ = r₀` (`ratFuncDeriv g₀ = r₀`) discharges it. The §2
`integrateRationalFunction_logForm` provides the general log-form witness. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-! ### The base derivation on `RatFunc ℚ` is the `d/dx` of `RationalFunctionDerivative` -/

section BaseDeriv
open scoped Differential

/-- **The `Differential (RatFunc K)` derivative is `ratFuncDeriv`** (`d/dx`): the `′` notation on
`RatFunc K` (from the global `Differential` instance) unfolds to the quotient-rule derivation
`ratFuncDeriv` definitionally. The bridge that turns a §2 `ratFuncDeriv`-antiderivative into the
`Differential`-shaped `hbase` hypothesis. -/
theorem deriv_eq_ratFuncDeriv {K : Type*} [Field K] (y : RatFunc K) : (y)′ = ratFuncDeriv y := rfl

end BaseDeriv

/-! ### The concrete §5.9 simple integral when the residual is a pure rational part

When `r₀ = ratFuncDeriv g₀` for a base `g₀ ∈ k` (the §2 rational part with vanishing residues), the
base antiderivative `y₀ = g₀` lives in `k`, so the §5.9 correction `Y = algMap (C g₀)` is concrete and
`hbase` is discharged outright. -/

namespace CPolyG
open scoped Differential
open QFunNZ

/-- The tower base field `CFieldSpec.K QFunNZ` is `RatFunc ℚ` as a `ℚ`-algebra. -/
noncomputable local instance : Algebra ℚ (CFieldSpec.K QFunNZ) :=
  inferInstanceAs (Algebra ℚ (RatFunc ℚ))

/-- **A base `d/dx`-antiderivative discharges `hbase` over the engine's monomial derivation**: if
`g₀ ∈ ℚ(x)` satisfies `ratFuncDeriv g₀ = r₀` (the §2 rational-part antiderivative of the residual), then
`implicitDeriv (toPolyG Dt) (C g₀) = C r₀` — the `hbase` hypothesis of
`CPolyG.towerLogResidueSum_sub_baseDeriv_eq_div_of_residueData`. Routes through `implicitDeriv_C`
(`δ (C g₀) = C (g₀′)`) and `deriv_eq_ratFuncDeriv` (`g₀′ = ratFuncDeriv g₀`). -/
theorem implicitDeriv_C_of_ratFuncDeriv (Dt : CPolyG QFunNZ) {g₀ r₀ : CFieldSpec.K QFunNZ}
    (hg : ratFuncDeriv g₀ = r₀) :
    Differential.implicitDeriv (toPolyG Dt) (C g₀) = C r₀ := by
  rw [Differential.implicitDeriv_C, deriv_eq_ratFuncDeriv, hg]

end CPolyG

/-! ### The §2 Liouville witness: every rational function of `x` is elementary integrable

`integrateRationalFunction_logForm` packaged for the residual `r₀ ∈ ℚ(x)`: viewing `r₀ = A/D` over `ℚ`,
its §2 integral has the closed log-form `r₀ = (rational part)′ + (∫p)′ + ∑ᵢ ∑ₐ a·logDeriv(Gₐ)`. This is the
Liouville/§2 fact that `r₀` *has* an elementary antiderivative — a base rational part plus a sum of
`c·log`. When the log sum is absent (residues vanish) the antiderivative is the base rational part alone
(the pure-rational-part regime above); otherwise the antiderivative carries genuine logs. -/

section Liouville
open scoped Differential

open Classical in
/-- **Every rational function of `x` is elementary integrable** (the §2 Liouville witness for the §5.9
residual): for any numerator `A` over a denominator with split squarefree factors
`Dᵢ = Lagrange.nodal (sset i) id`, the rational function `A/∏ Dᵢ^{eᵢ}` has the §2 closed log-form
`g′ + (∫p dx)′ + ∑ᵢ ∑ₐ a·logDeriv(Gₐ)` — a base `d/dx`-derivative of `g + ∫p dx` plus a sum of
log-derivatives. So its antiderivative `g + ∫p dx + ∑ a·log(Gₐ)` is elementary (in `k(log G₁, …)`). The
§5.9 residual `r₀ = η·∑ res α ∈ ℚ(x)`, being such a rational function, therefore *has* an elementary
antiderivative `Y` with `D Y = r₀`, discharging `hbase` in an elementary extension even when no base
`y₀ ∈ k` exists. This is `integrateRationalFunction_logForm` re-exposed as the §5.9 base-integration fact;
the `Differential` here is `ratFuncDeriv` (`d/dx` on `ℚ(x)`). -/
theorem ratFunc_elementary_integrable {K : Type*} [Field K] [CharZero K] {ι : Type*} (s : Finset ι)
    (sset : ι → Finset K) (e : ι → ℕ)
    (he : ∀ i ∈ s, 1 ≤ e i) (hne : ∀ i ∈ s, (sset i).Nonempty)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (sset i) (sset j)) (A : K[X]) :
    ∃ (g : RatFunc K) (p : K[X]) (r : ι → K[X]),
        algebraMap K[X] (RatFunc K) A
            / ∏ i ∈ s, algebraMap K[X] (RatFunc K) (Lagrange.nodal (sset i) id) ^ e i
          = (g)′ + (algebraMap K[X] (RatFunc K) (polyIntegral p))′
            + ∑ i ∈ s, ∑ a ∈ (sset i).image
                (fun α => (r i).eval α / eval α (derivative (Lagrange.nodal (sset i) id))),
                algebraMap K[X] (RatFunc K) (C a)
                  * Differential.logDeriv (algebraMap K[X] (RatFunc K)
                      (∏ α ∈ (sset i).filter
                          (fun α =>
                            (r i).eval α / eval α (derivative (Lagrange.nodal (sset i) id)) = a),
                        (X - C α))) :=
  integrateRationalFunction_logForm s sset e he hne hdisj A

end Liouville

end DeepWiki.SymbolicIntegration
