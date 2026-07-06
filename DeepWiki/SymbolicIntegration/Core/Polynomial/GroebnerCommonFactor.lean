import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.Data.Finsupp.MonomialOrder
import DeepWiki.SymbolicIntegration.Core.Polynomial.GroebnerReducedBasis
import DeepWiki.SymbolicIntegration.Core.Polynomial.GroebnerBivariateSorting
import DeepWiki.SymbolicIntegration.Core.Polynomial.GroebnerBoundedReduction

/-! # Common factors in bivariate Gröbner bases

The `K[x]` common-content layer of a sorted bivariate Gröbner basis, together with
leading-monomial shift lemmas for dividing every basis element by a common factor. -/

open MvPolynomial MonomialOrder

namespace DeepWiki.SymbolicIntegration

variable {σ : Type*} {m : MonomialOrder σ}

/-! ## Common leading y-coefficient content

The top sorted basis element contributes a `K[x]` divisor of every leading
`y`-coefficient. This captures only the `K[x]` content layer, not the possible
common `K[x][y]` factor. -/

/-- **The `K[x]`-content common divisor of the leading `y`-coefficients** (Lazard's `Gₖ₊₁`, closed
form): the leading `y`-coefficient `gₖ` of the **top** (`y`-degree-maximal) sorted basis element. By
`leadingYCoeff_sortedByYDegree_dvd_of_le` it divides `leadingYCoeff (sorted i)` for every `i`. (Only
the `K[x]`-layer; the `y`-primitive part `P` of the gcd is a separate factor.) -/
noncomputable def gbCommonContent {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (htop : Fin B.card) : MvPolynomial (Fin 1) K :=
  leadingYCoeff (sortedByYDegree hB htop)

/-- **`gbCommonContent` divides every leading `y`-coefficient**: with `htop` the `y`-degree-maximal
index (`∀ i, i ≤ htop`), `gₖ = gbCommonContent` divides `leadingYCoeff (sorted i)` for all `i`. -/
theorem gbCommonContent_dvd {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    {htop : Fin B.card} (hmax : ∀ i : Fin B.card, i ≤ htop) (i : Fin B.card) :
    gbCommonContent hB htop ∣ leadingYCoeff (sortedByYDegree hB i) :=
  leadingYCoeff_sortedByYDegree_dvd_of_le hB (hmax i)

/-- **The `K[x]`-content-unit condition** (Lazard's `Gₖ₊₁ = 1`): `IsUnit gₖ` for the top element.
This records only the `K[x]`-layer of Lazard's `P·Gₖ₊₁` divide-out; it does not rule out a common
`K[x][y]` factor. -/
def gbLeadingCoeffIsUnit {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (htop : Fin B.card) : Prop :=
  IsUnit (gbCommonContent hB htop)

/-! ## Leading-monomial shifts by a common factor

If each basis element is written as `h * q`, the leading monomial of `h` shifts
every quotient by the same degree. Divisibility comparisons among leading
monomials are therefore preserved after dividing out `h`. -/

/-- **Degree of a cofactor** (leading-monomial shift): if `b = h * q` with `h, q ≠ 0`, then
`m.degree q = m.degree b - m.degree h` (`MonomialOrder.degree_mul`, over a domain). -/
theorem degree_cofactor {K : Type*} [Field K] (m : MonomialOrder σ)
    {h q : MvPolynomial σ K} (hh : h ≠ 0) (hq : q ≠ 0) :
    m.degree q = m.degree (h * q) - m.degree h := by
  rw [degree_mul hh hq, add_comm, add_tsub_cancel_right]

/-- **Leading coefficient of a cofactor**: `m.leadingCoeff (h * q) = m.leadingCoeff h *
m.leadingCoeff q` (`MonomialOrder.leadingCoeff_mul`, over a domain). -/
theorem leadingCoeff_cofactor {K : Type*} [Field K] (m : MonomialOrder σ)
    (h q : MvPolynomial σ K) :
    m.leadingCoeff (h * q) = m.leadingCoeff h * m.leadingCoeff q :=
  MonomialOrder.leadingCoeff_mul

/-- **The leading monomial of a common multiple dominates that of the cofactor**: `m.degree q ≤
m.degree (h * q)` (the divided-out factor `h` only adds to the degree). -/
theorem degree_cofactor_le {K : Type*} [Field K] (m : MonomialOrder σ)
    {h q : MvPolynomial σ K} (hh : h ≠ 0) (hq : q ≠ 0) :
    m.degree q ≤ m.degree (h * q) := by
  rw [degree_mul hh hq]; exact le_add_self

/-- **Leading-monomial divisibility is preserved by a common shift**. For a fixed
shift `s`, `s + c ≤ s + d ↔ c ≤ d`. -/
theorem degree_add_le_add_iff {s c d : σ →₀ ℕ} : s + c ≤ s + d ↔ c ≤ d :=
  add_le_add_iff_left s

/-- **Leading-monomial shift, equation form**: with `b = h * q`, `b' = h * q'` (`h, q, q' ≠ 0`),
`m.degree b ≤ m.degree b' ↔ m.degree q ≤ m.degree q'`. -/
theorem degree_mul_le_mul_iff {K : Type*} [Field K] (m : MonomialOrder σ)
    {h q q' : MvPolynomial σ K} (hh : h ≠ 0) (hq : q ≠ 0) (hq' : q' ≠ 0) :
    m.degree (h * q) ≤ m.degree (h * q') ↔ m.degree q ≤ m.degree q' := by
  rw [degree_mul hh hq, degree_mul hh hq', degree_add_le_add_iff]

/-- **Minimality is preserved by dividing out a common factor**. If `b' = h·q'` does not
lead-monomial-divide a distinct `b = h·q` in the reduced GB, then `q'` does not
lead-monomial-divide `q` after the divide-out. -/
theorem leadingMonomial_cofactor_not_le {K : Type*} [Field K]
    {I : Ideal (MvPolynomial σ K)} {B : Set (MvPolynomial σ K)}
    (hB : IsReducedGroebnerBasis m I B) {h q q' : MvPolynomial σ K} (hh : h ≠ 0)
    (hq : q ≠ 0) (hq' : q' ≠ 0) (hb : h * q ∈ B) (hb' : h * q' ∈ B) (hne : h * q ≠ h * q') :
    ¬ (m.degree q' ≤ m.degree q) := by
  rw [← degree_mul_le_mul_iff m hh hq' hq]
  exact hB.leadingMonomial_not_le hb hb' hne

end DeepWiki.SymbolicIntegration
