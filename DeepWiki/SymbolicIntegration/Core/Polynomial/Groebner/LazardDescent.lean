import Mathlib.RingTheory.MvPolynomial.Groebner
import DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner.BivariateView
import DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner.BivariateSorting
import DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner.BoundedReduction
import DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner.LazardBaseObstruction
import DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner.LazardStep

/-! # Lazard descent from the base condition

The base condition for diagonal Lazard divisibility and the descent over the sorted basis. -/

open MvPolynomial MonomialOrder

namespace DeepWiki.SymbolicIntegration

/-! ## Base conditions and diagonal descent

The weaker base condition is the actual divisibility needed at the minimal sorted
`y`-degree. A degree-zero base is a convenient sufficient hypothesis. -/

/-- Lazard's base divisibility at the minimal sorted `y`-degree. -/
abbrev HasLazardBaseDvd {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K))) : Prop :=
  ∀ i0 : Fin B.card, i0.val = 0 →
    Polynomial.C (leadingYCoeff (sortedByYDegree hB i0)) ∣ lazardView (sortedByYDegree hB i0)

/-- Lazard's stronger degree-zero base at the minimal sorted `y`-degree. -/
abbrev HasLazardBaseDegreeZero {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K))) : Prop :=
  ∀ i0 : Fin B.card, i0.val = 0 → degreeOf 0 (sortedByYDegree hB i0) = 0

/-- Lazard diagonal descent, strengthened induction. Assuming the base divisibility
`C(g₀) ∣ lazardView f₀` at the minimal `y`-degree index, the divisibility
`C(gᵢ) ∣ lazardView (sorted j)` holds for all `j ≤ i`. -/
theorem C_dvd_lazardView_sortedByYDegree_of_le {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hbase : HasLazardBaseDvd hB)
    (i : Fin B.card) :
    ∀ j : Fin B.card, j ≤ i →
      Polynomial.C (leadingYCoeff (sortedByYDegree hB i)) ∣ lazardView (sortedByYDegree hB j) := by
  induction hi : i.val using Nat.strong_induction_on generalizing i with
  | _ n ih =>
    subst hi
    rcases Nat.eq_zero_or_pos i.val with h0 | hpos
    · intro j hji
      have hji0 : j.val = 0 := Nat.le_zero.mp (h0 ▸ (Fin.le_def.mp hji))
      have hji_eq : j = i := Fin.ext (by rw [hji0, h0])
      rw [hji_eq]
      exact hbase i h0
    · set i' : Fin B.card := ⟨i.val - 1, by omega⟩ with hi'_def
      have hi'val : i'.val = i.val - 1 := by rw [hi'_def]
      have hi'lt : i' < i := by rw [Fin.lt_def, hi'val]; omega
      have hsucc : ∀ k : Fin B.card, k < i → k ≤ i' := by
        intro k hk; rw [Fin.le_def, hi'val]; rw [Fin.lt_def] at hk; omega
      have hIH' : ∀ k : Fin B.card, k ≤ i' →
          Polynomial.C (leadingYCoeff (sortedByYDegree hB i'))
            ∣ lazardView (sortedByYDegree hB k) := ih i'.val (by rw [hi'val]; omega) i' rfl
      have hsuccdvd : Polynomial.C (leadingYCoeff (sortedByYDegree hB i))
          ∣ lazardView (sortedByYDegree hB i) :=
        C_dvd_lazardView_succ hB hi'lt hsucc hIH'
      intro j hji
      rcases eq_or_lt_of_le hji with hje | hjl
      · rw [hje]; exact hsuccdvd
      · have hji' : j ≤ i' := hsucc j hjl
        have hchain : leadingYCoeff (sortedByYDegree hB i)
            ∣ leadingYCoeff (sortedByYDegree hB i') :=
          leadingYCoeff_sortedByYDegree_dvd_of_le hB (le_of_lt hi'lt)
        exact dvd_trans (map_dvd Polynomial.C hchain) (hIH' j hji')

/-- The base divisibility from `f₀ ∈ K[x]`: the `degreeOf 0 (sorted 0) = 0`
base implies the weaker base divisibility. -/
theorem baseDvd_of_degreeOf_zero {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hbase : HasLazardBaseDegreeZero hB)
    (i0 : Fin B.card) (hi0 : i0.val = 0) :
    Polynomial.C (leadingYCoeff (sortedByYDegree hB i0)) ∣ lazardView (sortedByYDegree hB i0) :=
  C_dvd_lazardView_of_degreeOf_zero (hbase i0 hi0)

/-- Under the base divisibility,
each sorted basis element satisfies `C(leadingYCoeff (sorted i)) ∣ lazardView (sorted i)`. -/
theorem C_dvd_lazardView_sortedByYDegree {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hbase : HasLazardBaseDvd hB)
    (i : Fin B.card) :
    Polynomial.C (leadingYCoeff (sortedByYDegree hB i)) ∣ lazardView (sortedByYDegree hB i) :=
  C_dvd_lazardView_sortedByYDegree_of_le hB hbase i i le_rfl

/-- The degree-zero base condition gives sorted-basis divisibility by each leading `y`-coefficient. -/
theorem C_dvd_lazardView_sortedByYDegree_of_degreeOf_zero {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hbase : HasLazardBaseDegreeZero hB)
    (i : Fin B.card) :
    Polynomial.C (leadingYCoeff (sortedByYDegree hB i)) ∣ lazardView (sortedByYDegree hB i) :=
  C_dvd_lazardView_sortedByYDegree hB (baseDvd_of_degreeOf_zero hB hbase) i

end DeepWiki.SymbolicIntegration
