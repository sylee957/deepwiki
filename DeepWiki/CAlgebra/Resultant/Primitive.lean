import DeepWiki.CAlgebra.Poly.Bivariate
import DeepWiki.CAlgebra.Diff.Derivative
import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.RothsteinTrager.LrtSubresultant
import DeepWiki.CAlgebra.Poly.DivisionPseudo
import DeepWiki.CAlgebra.Gcd.Dense
import DeepWiki.CAlgebra.Resultant.Descent
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
  resultantDescent (σ := PUnit.{1}) (fun _ _ _ r => (polyContent r, polyPrimitive r, PUnit.unit))
    (fun _ _ _ r => polyPrimitive_size_le r) PUnit.unit f g (f.size - 1) (g.size - 1)

/-- The primitive-PRS resultant agrees with the Sylvester-determinant resultant at the
canonical degrees — hypothesis-free. -/
theorem resultantPRSPrimitive_eq (f g : DensePoly S) :
    resultantPRSPrimitive f g = (toPolynomial f).resultant (toPolynomial g)
      (toPolynomial f).natDegree (toPolynomial g).natDegree := by
  rw [resultantPRSPrimitive, natDegree_toPolynomial_eq_size_sub_one,
    natDegree_toPolynomial_eq_size_sub_one]
  exact resultantDescent_eq (σ := PUnit.{1})
    (fun _ _ _ r => (polyContent r, polyPrimitive r, PUnit.unit))
    (fun _ _ _ r => polyPrimitive_size_le r)
    (fun _ _ _ r => C_polyContent_mul_polyPrimitive r) PUnit.unit f g _ _
    (le_of_eq (natDegree_toPolynomial_eq_size_sub_one f))
    (le_of_eq (natDegree_toPolynomial_eq_size_sub_one g))

end Content

/-! ### The bivariate sequence for the log part -/

variable {R : Type u} [Field R] [DecidableEq R] [DensePolyGcd R]

/-- Lift an `x`-polynomial into `K[z][x]`: coefficients become `z`-constants. -/
def liftX (p : DensePoly R) : DensePoly (DensePoly R) := ofList (p.coeffs.map C)

/-- The indeterminate `z`, as a constant of `K[z][x]`. -/
def zC : DensePoly (DensePoly R) := C (ofList [0, 1])

omit [DensePolyGcd R] in
/-- The `x`-lift bridges to the coefficient-constant lift: `toPolynomial₂ (liftX p)
= (toPolynomial p).map C`. -/
theorem toPolynomial₂_liftX (p : DensePoly R) :
    toPolynomial₂ (liftX p) = (toPolynomial p).map Polynomial.C := by
  refine Polynomial.ext fun i => ?_
  rw [toPolynomial₂_coeff, Polynomial.coeff_map, coeff_toPolynomial]
  rw [liftX, coeff_ofList, List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : i < p.coeffs.length
  · rw [List.getElem?_eq_getElem h]
    show toPolynomial (C p.coeffs[i]) = Polynomial.C (p.coeff i)
    rw [toPolynomial_C, coeff, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
    rfl
  · rw [List.getElem?_eq_none (by omega)]
    show toPolynomial 0 = Polynomial.C (p.coeff i)
    rw [toPolynomial_zero,
      coeff_eq_zero_of_size_le p (by show p.coeffs.length ≤ i; omega), map_zero]

omit [DensePolyGcd R] in
/-- The `z`-constant variable bridges to `C X`: `toPolynomial₂ zC = C X`. -/
theorem toPolynomial₂_zC : toPolynomial₂ (zC (R := R)) = Polynomial.C Polynomial.X := by
  rw [zC, toPolynomial₂_C]
  congr 1
  refine Polynomial.ext fun i => ?_
  rw [coeff_toPolynomial]
  rcases i with _ | _ | i <;>
    simp [coeff_ofList, Polynomial.coeff_X]

omit [DensePolyGcd R] in
/-- The `x`-lift of a nonzero polynomial is nonzero. -/
theorem liftX_ne_zero {d : DensePoly R} (hd0 : d ≠ 0) : liftX d ≠ 0 := fun h0 => by
  have h1 := toPolynomial₂_liftX d
  rw [h0, toPolynomial₂_zero] at h1
  have h2 := (Polynomial.map_eq_zero_iff Polynomial.C_injective).mp h1.symm
  exact hd0 (toPolynomial_injective (by rw [h2, toPolynomial_zero]))

omit [DensePolyGcd R] in
/-- The `x`-lift preserves the size. -/
theorem liftX_size (d : DensePoly R) : (liftX d).size = d.size := by
  rcases eq_or_ne d 0 with rfl | hd0
  · rfl
  · have h1 : (toPolynomial₂ (liftX d)).natDegree = (toPolynomial d).natDegree := by
      rw [toPolynomial₂_liftX,
        Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective]
    rw [natDegree₂_eq_size_sub_one, natDegree_toPolynomial_eq_size_sub_one] at h1
    have h2 : (liftX d).size ≠ 0 := fun h0 => liftX_ne_zero hd0 (eq_zero_of_size_zero h0)
    have h3 : d.size ≠ 0 := fun h0 => hd0 (eq_zero_of_size_zero h0)
    omega

omit [DensePolyGcd R] in
/-- Degree corollary of `liftX_size`. -/
theorem liftX_natDegree₂ (d : DensePoly R) :
    (toPolynomial₂ (liftX d)).natDegree = (toPolynomial d).natDegree := by
  rw [natDegree₂_eq_size_sub_one, liftX_size, natDegree_toPolynomial_eq_size_sub_one]

/-- The `z`-content: the gcd of the `x`-coefficients. -/
def zContent (p : DensePoly (DensePoly R)) : DensePoly R :=
  p.coeffs.foldr (fun c acc => DensePolyGcd.gcd c acc) 0

/-- The `z`-primitive part: divide each `x`-coefficient by the content. -/
def zPrimitive (p : DensePoly (DensePoly R)) : DensePoly (DensePoly R) :=
  ofList (p.coeffs.map (· / zContent p))

/-- The `z`-primitive part is no larger. -/
theorem zPrimitive_size_le (p : DensePoly (DensePoly R)) : (zPrimitive p).size ≤ p.size := by
  rw [zPrimitive]
  set l := p.coeffs.map (· / zContent p) with hl
  have h1 : (ofList l).size ≤ l.length := trimTrailingZeros_length_le l
  have h2 : l.length = p.size := by rw [hl, List.length_map]; rfl
  omega

private theorem foldr_zgcd_dvd (l : List (DensePoly R)) :
    ∀ x ∈ l, l.foldr (fun c acc => DensePolyGcd.gcd c acc) 0 ∣ x := by
  induction l with
  | nil => intro x hx; exact absurd hx (List.not_mem_nil)
  | cons a t ih =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact DensePolyGcd.gcd_dvd_left _ _
      · exact (DensePolyGcd.gcd_dvd_right _ _).trans (ih x hx)

/-- The `z`-content divides every `x`-coefficient. -/
theorem zContent_dvd_coeff (p : DensePoly (DensePoly R)) (i : ℕ) :
    zContent p ∣ p.coeff i := by
  rw [coeff]
  by_cases h : i < p.coeffs.length
  · exact foldr_zgcd_dvd p.coeffs _ (by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
      exact List.getElem_mem h)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    exact dvd_zero _

/-- The `z`-primitive part of zero is zero. -/
@[simp] theorem zPrimitive_zero : zPrimitive (0 : DensePoly (DensePoly R)) = 0 := rfl

/-- Nonzero bivariate polynomials have nonzero `z`-content. -/
theorem zContent_ne_zero {p : DensePoly (DensePoly R)} (hp : p ≠ 0) : zContent p ≠ 0 := by
  intro h0
  apply hp
  apply toPolynomial_injective
  refine Polynomial.ext fun i => ?_
  rw [coeff_toPolynomial, toPolynomial_zero, Polynomial.coeff_zero]
  have hdvd := zContent_dvd_coeff p i
  rw [h0, zero_dvd_iff] at hdvd
  exact hdvd

/-- `z`-content–primitive reconstruction: `C (zContent p) * zPrimitive p = p`. -/
theorem C_zContent_mul_zPrimitive (p : DensePoly (DensePoly R)) :
    C (zContent p) * zPrimitive p = p := by
  apply toPolynomial_injective
  refine Polynomial.ext fun i => ?_
  rw [toPolynomial_mul, toPolynomial_C, Polynomial.coeff_C_mul, coeff_toPolynomial,
    coeff_toPolynomial, zPrimitive, coeff_ofList, List.getD_eq_getElem?_getD,
    List.getElem?_map]
  by_cases h : i < p.coeffs.length
  · rw [List.getElem?_eq_getElem h]
    show zContent p * (p.coeffs[i] / zContent p) = p.coeff i
    rcases eq_or_ne (zContent p) 0 with hc0 | hc0
    · have hz : p.coeffs[i] = 0 := by
        have := zContent_dvd_coeff p i
        rw [hc0, zero_dvd_iff, coeff, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem h] at this
        simpa using this
      rw [hz, hc0, EuclideanDomain.zero_div, mul_zero, coeff,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
      simp [hz]
    · rw [EuclideanDomain.mul_div_cancel' hc0 (by
        have := zContent_dvd_coeff p i
        rwa [coeff, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h] at this)]
      rw [coeff, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
      rfl
  · rw [List.getElem?_eq_none (by omega)]
    show zContent p * 0 = p.coeff i
    rw [mul_zero, coeff_eq_zero_of_size_le p (by
      show p.coeffs.length ≤ i
      omega)]

/-- Any common divisor of the `x`-coefficients divides the `z`-content. -/
theorem dvd_zContent {d : DensePoly R} (p : DensePoly (DensePoly R))
    (hd : ∀ i, d ∣ p.coeff i) : d ∣ zContent p := by
  rw [zContent]
  have hmem : ∀ x ∈ p.coeffs, d ∣ x := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := List.getElem_of_mem hx
    have := hd i
    rwa [coeff, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, hxi] at this
  revert hmem
  generalize p.coeffs = l
  intro hmem
  induction l with
  | nil => exact dvd_zero d
  | cons a t ih =>
      exact DensePolyGcd.dvd_gcd _ _ (hmem a List.mem_cons_self)
        (ih fun x hx => hmem x (List.mem_cons_of_mem _ hx))

/-- The `x`-coefficients of the reconstruction: `p.coeff i = zContent p * (zPrimitive p).coeff i`. -/
theorem coeff_eq_zContent_mul (p : DensePoly (DensePoly R)) (i : ℕ) :
    p.coeff i = zContent p * (zPrimitive p).coeff i := by
  have h := congrArg (fun q => (toPolynomial q).coeff i) (C_zContent_mul_zPrimitive p).symm
  simpa only [toPolynomial_mul, toPolynomial_C, Polynomial.coeff_C_mul, coeff_toPolynomial]
    using h

/-- The `z`-primitive part has unit content: any common divisor of its coefficients is a
unit. -/
theorem zContent_zPrimitive_isUnit {p : DensePoly (DensePoly R)} (hp : p ≠ 0) :
    IsUnit (zContent (zPrimitive p)) := by
  have hzc : zContent p ≠ 0 := zContent_ne_zero hp
  have hdvd : zContent p * zContent (zPrimitive p) ∣ zContent p := by
    refine dvd_zContent p fun i => ?_
    rw [coeff_eq_zContent_mul p i]
    exact mul_dvd_mul_left _ (zContent_dvd_coeff _ i)
  have h1 : zContent (zPrimitive p) ∣ 1 := by
    rcases hdvd with ⟨w, hw⟩
    refine ⟨w, mul_left_cancel₀ hzc ?_⟩
    rw [mul_one, ← mul_assoc]
    exact hw
  exact isUnit_of_dvd_one h1

/-! ### The Rothstein–Trager operand -/

section RtOperand

open scoped Differential FormalDiff

variable [CharZero R]

omit [DensePolyGcd R] [CharZero R] in
/-- The bridged second operand. -/
theorem operand_bridge (b d : DensePoly R) :
    toPolynomial₂ (liftX b - zC * liftX (d′))
      = (toPolynomial b).map Polynomial.C
        - Polynomial.C Polynomial.X
          * (Polynomial.derivative (toPolynomial d)).map Polynomial.C := by
  rw [toPolynomial₂_sub, toPolynomial₂_mul, toPolynomial₂_liftX, toPolynomial₂_liftX,
    toPolynomial₂_zC, toPolynomial_deriv]

omit [DensePolyGcd R] in
/-- The second operand is nonzero. -/
theorem operand_ne_zero (b d : DensePoly R) (hd2 : 2 ≤ d.size) (hbd : b.size < d.size) :
    (liftX b - zC * liftX (d′)) ≠ 0 := by
  intro h0
  refine SymbolicIntegration.rtResultant_operand_coeff_ne_zero (toPolynomial b)
    (toPolynomial d) ?_ ?_
  · rw [natDegree_toPolynomial_eq_size_sub_one, natDegree_toPolynomial_eq_size_sub_one]
    omega
  · rw [← operand_bridge, h0, toPolynomial₂_zero, Polynomial.coeff_zero]

omit [DensePolyGcd R] in
/-- Bridged corollary of `operand_ne_zero`. -/
theorem operand_ne_zero₂ (b d : DensePoly R) (hd2 : 2 ≤ d.size) (hbd : b.size < d.size) :
    toPolynomial₂ (liftX b - zC * liftX (d′)) ≠ 0 :=
  toPolynomial₂_ne_zero (operand_ne_zero b d hd2 hbd)

omit [DensePolyGcd R] in
/-- The second operand's size is `d.size − 1`. -/
theorem operand_size (b d : DensePoly R) (hd2 : 2 ≤ d.size) (hbd : b.size < d.size) :
    (liftX b - zC * liftX (d′)).size = d.size - 1 := by
  have h1 : (toPolynomial₂ (liftX b - zC * liftX (d′))).natDegree
      = (toPolynomial d).natDegree - 1 := by
    rw [operand_bridge]
    refine SymbolicIntegration.natDegree_rtResultant_operand _ _ ?_
    rw [natDegree_toPolynomial_eq_size_sub_one, natDegree_toPolynomial_eq_size_sub_one]
    omega
  rw [natDegree₂_eq_size_sub_one, natDegree_toPolynomial_eq_size_sub_one] at h1
  have h2 : (liftX b - zC * liftX (d′)).size ≠ 0 := fun h0 =>
    operand_ne_zero b d hd2 hbd (eq_zero_of_size_zero h0)
  omega

omit [DensePolyGcd R] in
/-- Degree corollary of `operand_size`. -/
theorem operand_natDegree₂ (b d : DensePoly R) (hd2 : 2 ≤ d.size) (hbd : b.size < d.size) :
    (toPolynomial₂ (liftX b - zC * liftX (d′))).natDegree
      = (toPolynomial d).natDegree - 1 := by
  rw [natDegree₂_eq_size_sub_one, operand_size b d hd2 hbd,
    natDegree_toPolynomial_eq_size_sub_one]

omit [DensePolyGcd R] in
open DeepWiki.SymbolicIntegration in
/-- The entry-pair subresultant at any index is the LRT subresultant. -/
theorem entry_subresultant_eq_lrt (b d : DensePoly R) (hd2 : 2 ≤ d.size)
    (hbd : b.size < d.size) (i : ℕ) :
    subresultant (toPolynomial₂ (liftX d))
      (toPolynomial₂ (liftX b - zC * liftX (d′)))
      (toPolynomial₂ (liftX d)).natDegree
      (toPolynomial₂ (liftX b - zC * liftX (d′))).natDegree i
      = lrtSubresultant (toPolynomial b) (toPolynomial d) i := by
  rw [liftX_natDegree₂, operand_natDegree₂ b d hd2 hbd, toPolynomial₂_liftX,
    operand_bridge, lrtSubresultant]

end RtOperand

end DensePoly

end DeepWiki.CAlgebra
