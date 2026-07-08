import DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner.ReductionStep
import DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner.BivariateSorting
import DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner.BoundedReduction.Representation

/-! # Bounded Lazard descent step

The assembled divisibility step for Lazard descent from bounded Gröbner representations.
-/

open MvPolynomial MonomialOrder

namespace DeepWiki.SymbolicIntegration

/-- **`C(g_i) ∣ C q · lazardView fj` from `g_j ∣ fj` and `g_j·q = g_i`** (the higher-index transfer,
the satisfiable form of the descent step's first hypothesis). Since `g_i = g_j·q`, divisibility of
`q · (coeff)` by `g_i = g_j·q` is divisibility of `coeff` by `g_j`; so from `C(g_j) ∣ lazardView fj`
(`= P(j)` at the higher index) one gets `C(g_i) ∣ C q · lazardView fj`. -/
theorem C_dvd_C_mul_lazardView_of_dvd {K : Type*} [Field K] {fj : MvPolynomial (Fin 2) K}
    {gi gj q : MvPolynomial (Fin 1) K} (hq : gj * q = gi)
    (hfj : Polynomial.C gj ∣ lazardView fj) :
    Polynomial.C gi ∣ Polynomial.C q * lazardView fj := by
  rw [← hq, Polynomial.C_mul, mul_comm (Polynomial.C gj)]
  exact mul_dvd_mul_left _ hfj

/-- **Lazard descent, the assembled single step.** For sorted basis
elements `fi := sortedByYDegree hB i`, `fj := sortedByYDegree hB j` and `q : K[x]`, the reduction
element `R := yConst q · fj − y^{shift}·fi ∈ I`. Given (1) `C(g_i) ∣ C q · lazardView fj` (which, with
`q = g_i/g_j`, follows from the higher-index `C(g_j) ∣ lazardView fj` via `C_dvd_C_mul_lazardView_of_dvd`)
and (2) `C(g_i) ∣ lazardView b` for every basis element of `y`-degree `≤ degreeOf 0 R` (the lower
contributors of `R`'s GB-reduction), one obtains `C(g_i) ∣ lazardView fi`. (Assembles
`C_dvd_lazardView_of_mem_of_dvd_bounded`, `lazard_lemma3_reductionStep_mem`, and
`C_dvd_lazardView_of_reductionStep_mul`.) Intended use: `q := g_i/g_j`
(`leadingYCoeff_sortedByYDegree_dvd_of_lt`) with `i < j`, where `R` has `y`-degree `< d(j)`
(`lazard_lemma3_reductionStep`). Closing the full induction also requires the no-common-factor
divide-out step to eliminate the self-reference of (2) at `b = fi`
(`y`-degree `d(i) ≤ degreeOf 0 R`). -/
theorem C_dvd_lazardView_descentStep {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    {i j : Fin B.card} {q : MvPolynomial (Fin 1) K}
    (hfj : Polynomial.C (leadingYCoeff (sortedByYDegree hB i))
        ∣ Polynomial.C q * lazardView (sortedByYDegree hB j))
    (hR0 : yConst q * sortedByYDegree hB j
        - X 0 ^ (degreeOf 0 (sortedByYDegree hB j) - degreeOf 0 (sortedByYDegree hB i))
            * sortedByYDegree hB i ≠ 0)
    (hbounded : ∀ b ∈ B,
        degreeOf 0 b ≤ degreeOf 0 (yConst q * sortedByYDegree hB j
          - X 0 ^ (degreeOf 0 (sortedByYDegree hB j) - degreeOf 0 (sortedByYDegree hB i))
              * sortedByYDegree hB i) →
        Polynomial.C (leadingYCoeff (sortedByYDegree hB i)) ∣ lazardView b) :
    Polynomial.C (leadingYCoeff (sortedByYDegree hB i)) ∣ lazardView (sortedByYDegree hB i) := by
  set fi := sortedByYDegree hB i with hfi_def
  set fj := sortedByYDegree hB j with hfj_def
  have hRmem : yConst q * fj - X 0 ^ (degreeOf 0 fj - degreeOf 0 fi) * fi ∈ I :=
    lazard_lemma3_reductionStep_mem (hB.isGroebnerBasis.1 fi (sortedByYDegree_mem hB i))
      (hB.isGroebnerBasis.1 fj (sortedByYDegree_mem hB j))
  have hRdvd : Polynomial.C (leadingYCoeff fi)
      ∣ lazardView (yConst q * fj - X 0 ^ (degreeOf 0 fj - degreeOf 0 fi) * fi) :=
    C_dvd_lazardView_of_mem_of_dvd_bounded hB hRmem hR0 hbounded
  exact C_dvd_lazardView_of_reductionStep_mul (q := q) hfj hRdvd

end DeepWiki.SymbolicIntegration
