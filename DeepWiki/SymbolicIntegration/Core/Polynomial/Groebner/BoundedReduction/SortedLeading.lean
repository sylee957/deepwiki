import DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner.LeadingYCoeffGcd
import DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner.BivariateSorting

/-! # Sorted leading-coefficient divisibility

Leading-`y`-coefficient divisibility along bases sorted by `y`-degree.
-/

open MvPolynomial MonomialOrder

namespace DeepWiki.SymbolicIntegration

/-- **Leading-`y`-coefficient divisibility along the sorted basis** (Lemma 2, one step on the
enumeration): for `i < j`, the higher-`y`-degree `leadingYCoeff (sortedByYDegree hB j)` divides the
lower one `leadingYCoeff (sortedByYDegree hB i)` (`lazard_lemma2` at the strictly increasing
`y`-degrees `degreeOf 0`). -/
theorem leadingYCoeff_sortedByYDegree_dvd_of_lt {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    {i j : Fin B.card} (hij : i < j) :
    leadingYCoeff (sortedByYDegree hB j) ∣ leadingYCoeff (sortedByYDegree hB i) :=
  lazard_lemma2 hB (sortedByYDegree_mem hB i) (sortedByYDegree_mem hB j)
    (degreeOf_sortedByYDegree_strictMono hB hij)

/-- **Leading-`y`-coefficient divisibility chain** (`≤` form): for `i ≤ j` along the sorted basis,
`leadingYCoeff (sortedByYDegree hB j) ∣ leadingYCoeff (sortedByYDegree hB i)` — the higher
`y`-degree's `gⱼ` divides every lower `gᵢ` (one-step `leadingYCoeff_sortedByYDegree_dvd_of_lt`, plus
reflexivity). This is the chain the descent uses to push `gᵢ ∣ g_j` onto the lower combination. -/
theorem leadingYCoeff_sortedByYDegree_dvd_of_le {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    {i j : Fin B.card} (hij : i ≤ j) :
    leadingYCoeff (sortedByYDegree hB j) ∣ leadingYCoeff (sortedByYDegree hB i) := by
  rcases lt_or_eq_of_le hij with h | h
  · exact leadingYCoeff_sortedByYDegree_dvd_of_lt hB h
  · rw [h]

end DeepWiki.SymbolicIntegration
