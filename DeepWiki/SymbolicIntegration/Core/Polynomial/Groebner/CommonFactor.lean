import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.Data.Finsupp.MonomialOrder
import DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner.ReducedBasis
import DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner.BivariateSorting
import DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner.BoundedReduction

/-! # Common factors in bivariate Gröbner bases

The `K[x]` common-content layer of a sorted bivariate Gröbner basis, together with
leading-monomial shift lemmas for dividing every basis element by a common factor. -/

open MvPolynomial MonomialOrder

namespace DeepWiki.SymbolicIntegration

variable {σ : Type*} {m : MonomialOrder σ}

/-! ## Common leading `y`-coefficient content

The top sorted basis element contributes a `K[x]` divisor of every leading
`y`-coefficient. This captures only the `K[x]` content layer, not the possible
common `K[x][y]` factor. -/

/-- The `K[x]`-content common divisor of the leading `y`-coefficients. -/
noncomputable def gbCommonContent {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (htop : Fin B.card) : MvPolynomial (Fin 1) K :=
  leadingYCoeff (sortedByYDegree hB htop)

/-- `gbCommonContent` divides every leading `y`-coefficient below a maximal sorted index. -/
theorem gbCommonContent_dvd {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    {htop : Fin B.card} (hmax : ∀ i : Fin B.card, i ≤ htop) (i : Fin B.card) :
    gbCommonContent hB htop ∣ leadingYCoeff (sortedByYDegree hB i) :=
  leadingYCoeff_sortedByYDegree_dvd_of_le hB (hmax i)

/-- The `K[x]`-content common divisor is a unit for the chosen top element. -/
def gbLeadingCoeffIsUnit {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (htop : Fin B.card) : Prop :=
  IsUnit (gbCommonContent hB htop)

/-! ## Leading-monomial shifts by a common factor

If each basis element is written as `h * q`, the leading monomial of `h` shifts
every quotient by the same degree. Divisibility comparisons among leading
monomials are therefore preserved after dividing out `h`. -/

/-- If `h` and `q` are nonzero, `m.degree q = m.degree (h * q) - m.degree h`. -/
theorem degree_cofactor {K : Type*} [Field K] (m : MonomialOrder σ)
    {h q : MvPolynomial σ K} (hh : h ≠ 0) (hq : q ≠ 0) :
    m.degree q = m.degree (h * q) - m.degree h := by
  rw [degree_mul hh hq, add_comm, add_tsub_cancel_right]

/-- The leading coefficient of `h * q` is the product of the leading coefficients. -/
theorem leadingCoeff_cofactor {K : Type*} [Field K] (m : MonomialOrder σ)
    (h q : MvPolynomial σ K) :
    m.leadingCoeff (h * q) = m.leadingCoeff h * m.leadingCoeff q :=
  MonomialOrder.leadingCoeff_mul

/-- The leading monomial of a common multiple dominates that of the cofactor. -/
theorem degree_cofactor_le {K : Type*} [Field K] (m : MonomialOrder σ)
    {h q : MvPolynomial σ K} (hh : h ≠ 0) (hq : q ≠ 0) :
    m.degree q ≤ m.degree (h * q) := by
  rw [degree_mul hh hq]; exact le_add_self

/-- Leading-monomial divisibility is preserved by adding a common shift. -/
theorem degree_add_le_add_iff {s c d : σ →₀ ℕ} : s + c ≤ s + d ↔ c ≤ d :=
  add_le_add_iff_left s

/-- Multiplying by a common nonzero factor preserves leading-monomial divisibility comparisons. -/
theorem degree_mul_le_mul_iff {K : Type*} [Field K] (m : MonomialOrder σ)
    {h q q' : MvPolynomial σ K} (hh : h ≠ 0) (hq : q ≠ 0) (hq' : q' ≠ 0) :
    m.degree (h * q) ≤ m.degree (h * q') ↔ m.degree q ≤ m.degree q' := by
  rw [degree_mul hh hq, degree_mul hh hq', degree_add_le_add_iff]

/-- Minimal leading-monomial comparisons are preserved after dividing out a common factor. -/
theorem leadingMonomial_cofactor_not_le {K : Type*} [Field K]
    {I : Ideal (MvPolynomial σ K)} {B : Set (MvPolynomial σ K)}
    (hB : IsReducedGroebnerBasis m I B) {h q q' : MvPolynomial σ K} (hh : h ≠ 0)
    (hq : q ≠ 0) (hq' : q' ≠ 0) (hb : h * q ∈ B) (hb' : h * q' ∈ B) (hne : h * q ≠ h * q') :
    ¬ (m.degree q' ≤ m.degree q) := by
  rw [← degree_mul_le_mul_iff m hh hq' hq]
  exact hB.leadingMonomial_not_le hb hb' hne

end DeepWiki.SymbolicIntegration
