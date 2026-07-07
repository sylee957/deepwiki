import Mathlib.RingTheory.MvPolynomial.Groebner
import DeepWiki.SymbolicIntegration.Core.Polynomial.GroebnerBivariateView
import DeepWiki.SymbolicIntegration.Core.Polynomial.GroebnerBivariateSorting
import DeepWiki.SymbolicIntegration.Core.Polynomial.GroebnerBoundedReduction
import DeepWiki.SymbolicIntegration.Core.Polynomial.GroebnerLazardStep

/-! # Lazard descent from the base condition

The base condition for diagonal Lazard divisibility, an explicit obstruction
showing it is not automatic, and the descent over the sorted basis. -/

open MvPolynomial MonomialOrder

namespace DeepWiki.SymbolicIntegration

/-! ## The base obstruction

The descent base `C(g₀) ∣ lazardView f₀` cannot be discharged for free: the
polynomial `xy + 1` has leading `y`-coefficient `x`, but `C(x)` does not divide
its `K[x][y]` view. -/

/-- `xy + 1`'s leading-`y`-coefficient `x = X 0` does not divide `1` in `K[x]`
(`= MvPolynomial (Fin 1) K`). -/
theorem leadingYCoeff_xyAddOne_not_dvd_one {K : Type*} [Field K] :
    ¬ (X (0 : Fin 1) : MvPolynomial (Fin 1) K) ∣ 1 := by
  intro h
  have he : (MvPolynomial.eval (fun _ => (0 : K))) (X (0 : Fin 1))
      ∣ (MvPolynomial.eval (fun _ => (0 : K))) 1 := map_dvd _ h
  rw [MvPolynomial.eval_X, map_one, zero_dvd_iff] at he
  exact one_ne_zero he

/-- The `K[x][y]` view of `xy + 1` is `C(x)·Y + 1` (`x = X 0`, `y = X 1`). -/
theorem lazardView_xyAddOne {K : Type*} [Field K] :
    lazardView (X 1 * X 0 + 1 : MvPolynomial (Fin 2) K)
      = Polynomial.C (X 0) * Polynomial.X + 1 := by
  have h1 : (X (1 : Fin 2) : MvPolynomial (Fin 2) K) = X (0 : Fin 1).succ := by congr 1
  rw [lazardView, map_add, map_mul, map_one, finSuccEquiv_X_zero, h1, finSuccEquiv_X_succ]

/-- `leadingYCoeff (xy + 1) = x` (`= X 0`): the coefficient of `Y¹` in `C(x)·Y + 1`. -/
theorem leadingYCoeff_xyAddOne {K : Type*} [Field K] :
    leadingYCoeff (X 1 * X 0 + 1 : MvPolynomial (Fin 2) K) = X 0 := by
  rw [leadingYCoeff, lazardView_xyAddOne]
  have hCX : (Polynomial.C (X (0 : Fin 1) : MvPolynomial (Fin 1) K) * Polynomial.X).natDegree = 1 :=
    Polynomial.natDegree_C_mul_X _ (MvPolynomial.X_ne_zero _)
  have hd : (Polynomial.C (X (0 : Fin 1) : MvPolynomial (Fin 1) K) * Polynomial.X + 1).natDegree = 1 := by
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt
      (by rw [hCX, Polynomial.natDegree_one]; decide), hCX]
  rw [Polynomial.leadingCoeff, hd, Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_one, mul_one, Polynomial.coeff_one, if_neg (by decide), add_zero]

/-- **`leadingYCoeff f₀` need not be a unit**: `xy + 1` has `leadingYCoeff = x`, not a unit of `K[x]`. -/
theorem not_isUnit_leadingYCoeff_xyAddOne {K : Type*} [Field K] :
    ¬ IsUnit (leadingYCoeff (X 1 * X 0 + 1 : MvPolynomial (Fin 2) K)) := by
  rw [leadingYCoeff_xyAddOne]
  exact fun h => leadingYCoeff_xyAddOne_not_dvd_one (isUnit_iff_dvd_one.mp h)

/-- **The base divisibility `C(g₀) ∣ lazardView f₀` genuinely fails**: for `f = xy + 1`,
`C(leadingYCoeff f) = C(x)` does not divide `lazardView f = C(x)·Y + 1`. -/
theorem not_C_leadingYCoeff_dvd_lazardView_xyAddOne {K : Type*} [Field K] :
    ¬ Polynomial.C (leadingYCoeff (X 1 * X 0 + 1 : MvPolynomial (Fin 2) K))
        ∣ lazardView (X 1 * X 0 + 1 : MvPolynomial (Fin 2) K) := by
  rw [leadingYCoeff_xyAddOne, lazardView_xyAddOne, Polynomial.C_dvd_iff_dvd_coeff]
  intro h
  have h0 := h 0
  simp only [Polynomial.coeff_add, Polynomial.mul_coeff_zero, Polynomial.coeff_C,
    Polynomial.coeff_X_zero, mul_zero, Polynomial.coeff_one_zero, zero_add] at h0
  exact leadingYCoeff_xyAddOne_not_dvd_one h0

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

/-- **Lazard diagonal descent, strengthened induction**. Assuming the base divisibility
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

/-- **The base divisibility from `f₀ ∈ K[x]`**: the `degreeOf 0 (sorted 0) = 0`
base implies the weaker base divisibility. -/
theorem baseDvd_of_degreeOf_zero {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hbase : HasLazardBaseDegreeZero hB)
    (i0 : Fin B.card) (hi0 : i0.val = 0) :
    Polynomial.C (leadingYCoeff (sortedByYDegree hB i0)) ∣ lazardView (sortedByYDegree hB i0) :=
  C_dvd_lazardView_of_degreeOf_zero (hbase i0 hi0)

/-- **Lazard diagonal descent**. Under the base divisibility,
each sorted basis element satisfies `C(leadingYCoeff (sorted i)) ∣ lazardView (sorted i)`. -/
theorem lazard_lemma3_dvd {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hbase : HasLazardBaseDvd hB)
    (i : Fin B.card) :
    Polynomial.C (leadingYCoeff (sortedByYDegree hB i)) ∣ lazardView (sortedByYDegree hB i) :=
  C_dvd_lazardView_sortedByYDegree_of_le hB hbase i i le_rfl

/-- **Lazard diagonal descent from `f₀ ∈ K[x]`**. -/
theorem lazard_lemma3_dvd_of_degreeOf_zero {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hbase : HasLazardBaseDegreeZero hB)
    (i : Fin B.card) :
    Polynomial.C (leadingYCoeff (sortedByYDegree hB i)) ∣ lazardView (sortedByYDegree hB i) :=
  lazard_lemma3_dvd hB (baseDvd_of_degreeOf_zero hB hbase) i

end DeepWiki.SymbolicIntegration
