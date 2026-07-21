import DeepWiki.CAlgebra.Poly.DivisionPseudo
import DeepWiki.CAlgebra.Gcd.Dense
import DeepWiki.CAlgebra.Resultant.Euclidean

/-! # The primitive pseudo-remainder sequence over `K[z]`

Bivariate `K[z][x]` machinery (`x` outermost): constant lifts, `z`-contents, and the
primitive pseudo-remainder sequence — pseudo-divide, strip the `z`-content, recurse. Its
elements differ from the true subresultants only by `z`-contents, which specialize to
constants; the Lazard–Rioboo–Trager log arguments are read off this sequence. -/

namespace DeepWiki.CAlgebra

universe u

namespace DensePoly

/-! ### Generic content over a Euclidean coefficient domain -/

section Content

variable {S : Type u} [EuclideanDomain S] [DecidableEq S]

/-- The content: the Euclidean gcd of the coefficients. -/
def polyContent (r : DensePoly S) : S := r.coeffs.foldr EuclideanDomain.gcd 0

/-- The primitive part: divide every coefficient by the content. -/
def polyPrimitive (r : DensePoly S) : DensePoly S :=
  ofList (r.coeffs.map (· / polyContent r))

private theorem foldr_gcd_dvd (l : List S) : ∀ x ∈ l, l.foldr EuclideanDomain.gcd 0 ∣ x := by
  induction l with
  | nil => intro x hx; exact absurd hx (List.not_mem_nil)
  | cons a t ih =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact EuclideanDomain.gcd_dvd_left _ _
      · exact (EuclideanDomain.gcd_dvd_right _ _).trans (ih x hx)

/-- The content divides every coefficient. -/
theorem polyContent_dvd_coeff (r : DensePoly S) (i : ℕ) : polyContent r ∣ r.coeff i := by
  rw [coeff]
  by_cases h : i < r.coeffs.length
  · exact foldr_gcd_dvd r.coeffs _ (by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
      exact List.getElem_mem h)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    exact dvd_zero _

/-- Content–primitive reconstruction: `C (content r) * primitive r = r`. -/
theorem C_polyContent_mul_polyPrimitive (r : DensePoly S) :
    C (polyContent r) * polyPrimitive r = r := by
  apply toPolynomial_injective
  ext i
  rw [toPolynomial_mul, toPolynomial_C, Polynomial.coeff_C_mul, coeff_toPolynomial,
    coeff_toPolynomial, polyPrimitive, coeff_ofList, List.getD_eq_getElem?_getD,
    List.getElem?_map]
  by_cases h : i < r.coeffs.length
  · rw [List.getElem?_eq_getElem h]
    show polyContent r * (r.coeffs[i] / polyContent r) = r.coeff i
    rcases eq_or_ne (polyContent r) 0 with hc0 | hc0
    · have hz : r.coeffs[i] = 0 := by
        have := polyContent_dvd_coeff r i
        rw [hc0, zero_dvd_iff, coeff, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem h] at this
        simpa using this
      rw [hz, hc0, EuclideanDomain.zero_div, mul_zero, coeff,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
      simp [hz]
    · rw [EuclideanDomain.mul_div_cancel' hc0 (by
        have := polyContent_dvd_coeff r i
        rwa [coeff, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h] at this)]
      rw [coeff, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
      rfl
  · rw [List.getElem?_eq_none (by omega)]
    show polyContent r * 0 = r.coeff i
    rw [mul_zero, coeff_eq_zero_of_size_le r (by
      show r.coeffs.length ≤ i
      omega)]

/-- The primitive part is no larger. -/
theorem polyPrimitive_size_le (r : DensePoly S) : (polyPrimitive r).size ≤ r.size := by
  rw [polyPrimitive]
  set l := r.coeffs.map (· / polyContent r) with hl
  have h1 : (ofList l).size ≤ l.length := trimTrailingZeros_length_le l
  have h2 : l.length = r.size := by rw [hl, List.length_map]; rfl
  omega

/-- **Resultant by the primitive pseudo-remainder sequence**: the content-stripping
instantiation of the descent — coefficients stay small along the way. -/
def resultantPRSPrimitive (f g : DensePoly S) : S :=
  resultantDescent (fun r => (polyContent r, polyPrimitive r))
    (fun r => polyPrimitive_size_le r) f g (f.size - 1) (g.size - 1)

/-- The primitive-PRS resultant agrees with the Sylvester-determinant resultant at the
canonical degrees — hypothesis-free. -/
theorem resultantPRSPrimitive_eq (f g : DensePoly S) :
    resultantPRSPrimitive f g = (toPolynomial f).resultant (toPolynomial g)
      (toPolynomial f).natDegree (toPolynomial g).natDegree := by
  rw [resultantPRSPrimitive, natDegree_toPolynomial_eq_size_sub_one,
    natDegree_toPolynomial_eq_size_sub_one]
  exact resultantDescent_eq (fun r => (polyContent r, polyPrimitive r))
    (fun r => polyPrimitive_size_le r) (fun r => C_polyContent_mul_polyPrimitive r) f g _ _
    (le_of_eq (natDegree_toPolynomial_eq_size_sub_one f))
    (le_of_eq (natDegree_toPolynomial_eq_size_sub_one g))

end Content

/-! ### The bivariate sequence for the log part -/

variable {R : Type u} [Field R] [DecidableEq R] [DensePolyGcd R]

/-- Lift an `x`-polynomial into `K[z][x]`: coefficients become `z`-constants. -/
def liftX (p : DensePoly R) : DensePoly (DensePoly R) := ofList (p.coeffs.map C)

/-- The indeterminate `z`, as a constant of `K[z][x]`. -/
def zC : DensePoly (DensePoly R) := C (ofList [0, 1])

/-- The `z`-content: the gcd of the `x`-coefficients. -/
def zContent (p : DensePoly (DensePoly R)) : DensePoly R :=
  p.coeffs.foldr (fun c acc => DensePolyGcd.gcd c acc) 0

/-- The `z`-primitive part: divide each `x`-coefficient by the content. -/
def zPrimitive (p : DensePoly (DensePoly R)) : DensePoly (DensePoly R) :=
  ofList (p.coeffs.map fun c => div c (zContent p))

/-- The primitive pseudo-remainder sequence in `x` over `K[z]`, starting from the second
input: pseudo-divide, take the `z`-primitive part, recurse. -/
def prsPrimitive : ℕ → DensePoly (DensePoly R) → DensePoly (DensePoly R) →
    List (DensePoly (DensePoly R))
  | 0, _, _ => []
  | fuel + 1, A, B =>
      if B = 0 then []
      else B :: prsPrimitive fuel B (zPrimitive (pseudoMod A B))

end DensePoly

end DeepWiki.CAlgebra
