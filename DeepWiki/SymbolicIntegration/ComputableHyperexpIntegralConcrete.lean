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

open DeepWiki.SymbolicIntegration in
open scoped Classical Differential in
/-- **The complete hyperexponential simple integral with a concrete `d/dx`-antiderivative correction**
(the `hbase`-free §5.9 engine-data headline): with the residueData hypotheses, when the constant-in-`t`
residual `r₀ = η·∑ res α ∈ ℚ(x)` is the **§2 rational-part antiderivative's derivative** — i.e. some
`g₀ ∈ ℚ(x)` has `ratFuncDeriv g₀ = r₀` (the residues of `r₀` vanish, so its §2 antiderivative is a single
base field element `g₀ ∈ k`, no logs) — the engine's residue sum minus the derivative of the **concrete,
log-free** correction `Y = towerAlg (C g₀)` equals the simple residual:
`logResidueSum Dt logs − towerFractionFieldDeriv Dt (towerAlg (C g₀)) = towerAlg(hNum)/towerAlg(hDen)`.
The `hbase` hypothesis is now **discharged** from the §2 base integrator: `implicitDeriv_C_of_ratFuncDeriv`
turns `ratFuncDeriv g₀ = r₀` into the required `implicitDeriv (toPolyG Dt) (C g₀) = C r₀`, which feeds
`towerLogResidueSum_sub_baseDeriv_eq_div_of_residueData`. The fully concrete §5.9 simple integral in the
pure-rational-residual regime — log part minus the §2 rational antiderivative `g₀` of the leftover
residual, with no assumed base antiderivative. -/
theorem towerLogResidueSum_sub_ratPart_eq_div_of_residueData (Dt : CPolyG QFunNZ)
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
              = CFieldSpec.toK (ofConstNZ cv.1)), (X - C α))
    (g₀ : CFieldSpec.K QFunNZ)
    (hg : ratFuncDeriv g₀
      = η * ∑ α ∈ s, (toPolyG hNum).eval α
          / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval α) :
    logResidueSum Dt logs - towerFractionFieldDeriv Dt (towerAlg (C g₀))
      = towerAlg (toPolyG hNum) / towerAlg (toPolyG hDen) :=
  towerLogResidueSum_sub_baseDeriv_eq_div_of_residueData Dt htop hNum hDen logs s hden hA hb0
    hkeysNodup hkeysImage harg g₀ (implicitDeriv_C_of_ratFuncDeriv Dt hg)

open DeepWiki.SymbolicIntegration in
open scoped Classical Differential in
/-- Restatement: the engine's corrected hyperexponential residue sum with the concrete §2 rational-part
correction `g₀` (`ratFuncDeriv g₀ = r₀`) — the `hbase`-free §5.9 simple integral in the pure-rational
residual regime. -/
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
              = CFieldSpec.toK (ofConstNZ cv.1)), (X - C α))
    (g₀ : CFieldSpec.K QFunNZ)
    (hg : ratFuncDeriv g₀
      = η * ∑ α ∈ s, (toPolyG hNum).eval α
          / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval α) :
    logResidueSum Dt logs - towerFractionFieldDeriv Dt (towerAlg (C g₀))
      = towerAlg (toPolyG hNum) / towerAlg (toPolyG hDen) :=
  towerLogResidueSum_sub_ratPart_eq_div_of_residueData Dt htop hNum hDen logs s hden hA hb0
    hkeysNodup hkeysImage harg g₀ hg

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

/-! ### The `Core`-level `hbase`-free §5.9 simple integral over the base monomial derivation

The abstract `Core` headline `extendDeriv_logPart_sub_baseAntideriv_eq_div`, with its `hbase` hypothesis
discharged from a §2 `ratFuncDeriv`-antiderivative. Here the base derivation is `implicitDeriv v` for a
monomial `v : (RatFunc ℚ)[X]` (the general `δ` of the hyperexponential regime), and the residual's
antiderivative `g₀ ∈ ℚ(x)` is supplied by `ratFuncDeriv g₀ = r₀` (the §2 rational part). -/

section CoreConcrete
open scoped Differential

/-- **The concrete §5.9 simple integral over a base monomial derivation** (the `Core` `hbase`-free
headline): for the base derivation `δ = implicitDeriv v` on `(RatFunc ℚ)[X]`, when the residual
`r₀ = η·∑ res α ∈ ℚ(x)` is the derivative of a §2 rational part `g₀ ∈ ℚ(x)` (`ratFuncDeriv g₀ = r₀`,
residues vanishing), the corrected log part `(∑ aᵢ·log gᵢ) − algMap(C g₀)` differentiates under
`extendDeriv δ` exactly to `A/d` — **without** assuming a base antiderivative. Composes the proven
`extendDeriv_logPart_sub_baseAntideriv_eq_div` with `implicitDeriv_C` + `deriv_eq_ratFuncDeriv`
(`δ (C g₀) = C (g₀′) = C (ratFuncDeriv g₀) = C r₀`). The pure-rational-residual §5.9 simple integral with
the §2 antiderivative `g₀` wired in. -/
theorem extendDeriv_logPart_sub_ratPart_eq_div (v : (RatFunc ℚ)[X]) (A : (RatFunc ℚ)[X])
    (s : Finset (RatFunc ℚ)) (hA : A.degree < s.card) (η : RatFunc ℚ) (γ : RatFunc ℚ → RatFunc ℚ)
    (hδ : ∀ α ∈ s, Differential.implicitDeriv v (X - C α) = C η * X + C (γ α))
    (hb0 : ∀ α ∈ s, η * α + γ α ≠ 0)
    (hc : ∀ α ∈ s, Differential.implicitDeriv v
      (C (A.eval α / (Differential.implicitDeriv v (Lagrange.nodal s id)).eval α)) = 0)
    (L : RatFunc ℚ → RatFunc (RatFunc ℚ))
    (hL : ∀ α ∈ s, extendDeriv (Differential.implicitDeriv v) (L α)
      = algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (Differential.implicitDeriv v (X - C α))
        / algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (X - C α))
    (g₀ : RatFunc ℚ)
    (hg : ratFuncDeriv g₀
      = η * ∑ α ∈ s, A.eval α / (Differential.implicitDeriv v (Lagrange.nodal s id)).eval α) :
    extendDeriv (Differential.implicitDeriv v) ((∑ α ∈ s,
          algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ))
              (C (A.eval α / (Differential.implicitDeriv v (Lagrange.nodal s id)).eval α)) * L α)
            - algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (C g₀))
      = algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) A
          / algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (Lagrange.nodal s id) :=
  extendDeriv_logPart_sub_baseAntideriv_eq_div (Differential.implicitDeriv v) A s hA η γ hδ hb0 hc L hL
    g₀ (by rw [Differential.implicitDeriv_C, deriv_eq_ratFuncDeriv, hg])

/-- Restatement: the `Core` `hbase`-free §5.9 simple integral `D((∑ aᵢ·log gᵢ) − algMap(C g₀)) = A/d` with
the §2 rational antiderivative `g₀` (`ratFuncDeriv g₀ = r₀`) over the base monomial derivation. -/
example (v : (RatFunc ℚ)[X]) (A : (RatFunc ℚ)[X]) (s : Finset (RatFunc ℚ)) (hA : A.degree < s.card)
    (η : RatFunc ℚ) (γ : RatFunc ℚ → RatFunc ℚ)
    (hδ : ∀ α ∈ s, Differential.implicitDeriv v (X - C α) = C η * X + C (γ α))
    (hb0 : ∀ α ∈ s, η * α + γ α ≠ 0)
    (hc : ∀ α ∈ s, Differential.implicitDeriv v
      (C (A.eval α / (Differential.implicitDeriv v (Lagrange.nodal s id)).eval α)) = 0)
    (L : RatFunc ℚ → RatFunc (RatFunc ℚ))
    (hL : ∀ α ∈ s, extendDeriv (Differential.implicitDeriv v) (L α)
      = algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (Differential.implicitDeriv v (X - C α))
        / algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (X - C α))
    (g₀ : RatFunc ℚ)
    (hg : ratFuncDeriv g₀
      = η * ∑ α ∈ s, A.eval α / (Differential.implicitDeriv v (Lagrange.nodal s id)).eval α) :
    extendDeriv (Differential.implicitDeriv v) ((∑ α ∈ s,
          algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ))
              (C (A.eval α / (Differential.implicitDeriv v (Lagrange.nodal s id)).eval α)) * L α)
            - algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (C g₀))
      = algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) A
          / algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (Lagrange.nodal s id) :=
  extendDeriv_logPart_sub_ratPart_eq_div v A s hA η γ hδ hb0 hc L hL g₀ hg

end CoreConcrete

-- Axiom audits for the headline deliverables (`[propext, Classical.choice, Quot.sound]` — no
-- `native_decide`, no `sorryAx`).
#print axioms deriv_eq_ratFuncDeriv
#print axioms CPolyG.implicitDeriv_C_of_ratFuncDeriv
#print axioms CPolyG.towerLogResidueSum_sub_ratPart_eq_div_of_residueData
#print axioms ratFunc_elementary_integrable
#print axioms extendDeriv_logPart_sub_ratPart_eq_div

end DeepWiki.SymbolicIntegration
