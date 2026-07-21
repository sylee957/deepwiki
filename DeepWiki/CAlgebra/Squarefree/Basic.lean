import DeepWiki.CAlgebra.Poly.Derivative
import DeepWiki.CAlgebra.Gcd
import Mathlib.FieldTheory.Perfect
import DeepWiki.Algebra.SquarefreeGcd

/-! # Squarefreeness of dense polynomials — shared kernel

The bridge transports for unit/squarefree/coprimality predicates, the derivative criterion
`Squarefree p ↔ IsCoprime p (deriv p)` with **decidability of `Squarefree`** (a gcd size test),
the squarefree part `sqfreePart p = p / gcd(p, deriv p)` with its satellites and squarefreeness
(transported from the characteristic-zero keystone), the gcd glue lemma, and the staircase
product `powProd` — everything the decomposition algorithms (`Squarefree/Musser`,
`Squarefree/Yun`) and the dispatch interface (`Squarefree/Dense`) build on. -/

namespace DeepWiki.CAlgebra

universe u

namespace DensePoly

variable {R : Type u} [Field R] [DecidableEq R]

/-! ### Bridge transports for unit, squarefree, and coprimality predicates -/

/-- Units correspond across the bridge. -/
theorem isUnit_toPolynomial_iff {p : DensePoly R} : IsUnit (toPolynomial p) ↔ IsUnit p := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ := h.exists_right_inv
    refine ⟨⟨p, ofPolynomial y, ?_, ?_⟩, rfl⟩
    · exact toPolynomial_injective (by
        rw [toPolynomial_mul, toPolynomial_ofPolynomial, toPolynomial_one, hy])
    · exact toPolynomial_injective (by
        rw [toPolynomial_mul, toPolynomial_ofPolynomial, toPolynomial_one, mul_comm]
        exact hy)
  · exact fun h => h.map (equiv (R := R)).toRingHom

/-- Squarefreeness corresponds across the bridge. -/
theorem squarefree_toPolynomial_iff {p : DensePoly R} :
    Squarefree (toPolynomial p) ↔ Squarefree p := by
  constructor
  · intro h x hx
    exact isUnit_toPolynomial_iff.mp
      (h (toPolynomial x) (by rw [← toPolynomial_mul]; exact toPolynomial_dvd hx))
  · intro h X hX
    rw [← toPolynomial_ofPolynomial X] at hX ⊢
    exact isUnit_toPolynomial_iff.mpr
      (h (ofPolynomial X) (dvd_of_toPolynomial_dvd (by rwa [toPolynomial_mul])))

/-- Coprimality corresponds across the bridge. -/
theorem isCoprime_toPolynomial_iff {p q : DensePoly R} :
    IsCoprime (toPolynomial p) (toPolynomial q) ↔ IsCoprime p q := by
  constructor
  · rintro ⟨a, b, hab⟩
    refine ⟨ofPolynomial a, ofPolynomial b, toPolynomial_injective ?_⟩
    rw [toPolynomial_add, toPolynomial_mul, toPolynomial_mul, toPolynomial_ofPolynomial,
      toPolynomial_ofPolynomial, toPolynomial_one]
    exact hab
  · exact fun h => h.map (equiv (R := R)).toRingHom

/-- Derivative criterion for squarefreeness over a perfect field (e.g. characteristic zero):
`p` is squarefree iff it is coprime to its derivative. Hypothesis-free: at `p = 0` both sides
fail. -/
theorem squarefree_iff_isCoprime_deriv [PerfectField R] {p : DensePoly R} :
    Squarefree p ↔ IsCoprime p (deriv p) := by
  rw [← squarefree_toPolynomial_iff, ← PerfectField.separable_iff_squarefree,
    Polynomial.separable_def, ← toPolynomial_deriv, isCoprime_toPolynomial_iff]

/-- Squarefreeness is a gcd size test: `p` is squarefree iff `gcd(p, deriv p)` is a constant. -/
theorem squarefree_iff_gcd_deriv_size [PerfectField R] [DensePolyGcd R] {p : DensePoly R} :
    Squarefree p ↔ (DensePolyGcd.gcd p (deriv p)).size = 1 := by
  rw [squarefree_iff_isCoprime_deriv, DensePolyGcd.isCoprime_iff_isUnit_gcd,
    isUnit_iff_size_eq_one]

/-- Squarefreeness of dense polynomials is decidable (compute the gcd, test its size). -/
instance [PerfectField R] [DensePolyGcd R] :
    DecidablePred (Squarefree : DensePoly R → Prop) := fun _ =>
  decidable_of_iff _ squarefree_iff_gcd_deriv_size.symm

/-- `powProd [f₁, …, fₖ] n = f₁^n · f₂^(n+1) ⋯ fₖ^(n+k-1)` — the exponent-staircase product
of a squarefree decomposition. -/
def powProd : List (DensePoly R) → ℕ → DensePoly R
  | [], _ => 1
  | f :: L, n => f ^ n * powProd L (n + 1)

/-- Shifting the staircase start multiplies in one plain product. -/
theorem powProd_succ (L : List (DensePoly R)) (n : ℕ) :
    powProd L (n + 1) = powProd L n * L.prod := by
  induction L generalizing n with
  | nil => simp [powProd]
  | cons f L ih => rw [powProd, powProd, ih (n + 1), List.prod_cons, pow_succ]; ring

/-- **The associate certificate**: over a field, the cross-scaled equality
`p · C (lc q) = q · C (lc p)` with `q ≠ 0` certifies `Associated p q` — the decidable check
behind checker-validated decomposition algorithms. -/
theorem associated_of_cross_mul_C {p q : DensePoly R} (hp : p ≠ 0) (hq : q ≠ 0)
    (h : p * C q.leadingCoeff = q * C p.leadingCoeff) : Associated p q := by
  have hlcq : q.leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero (fun h0 => hq (eq_zero_of_size_zero h0))
  have hlcp : p.leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero (fun h0 => hp (eq_zero_of_size_zero h0))
  have hpq : p = q * (C p.leadingCoeff * C q.leadingCoeff⁻¹) := by
    apply mul_right_cancel₀ (C_ne_zero hlcq)
    rw [h, mul_assoc, mul_assoc, ← C_mul, inv_mul_cancel₀ hlcq, ← one_def, mul_one]
  have hC : IsUnit (C (p.leadingCoeff * q.leadingCoeff⁻¹) : DensePoly R) :=
    isUnit_C (mul_ne_zero hlcp (inv_ne_zero hlcq))
  refine Associated.symm ⟨hC.unit, ?_⟩
  rw [IsUnit.unit_spec, C_mul]
  exact hpq.symm

variable [DensePolyGcd R]

/-- The squarefree part: `p` divided by `gcd(p, deriv p)`. -/
def sqfreePart (p : DensePoly R) : DensePoly R := div p (DensePolyGcd.gcd p (deriv p))

/-- The gcd with the derivative reconstructs `p` against the squarefree part (exact division). -/
theorem gcd_deriv_mul_sqfreePart {p : DensePoly R} (hp : p ≠ 0) :
    DensePolyGcd.gcd p (deriv p) * sqfreePart p = p :=
  EuclideanDomain.mul_div_cancel' (DensePolyGcd.gcd_ne_zero_of_left hp _)
    (DensePolyGcd.gcd_dvd_left p (deriv p))

/-- The squarefree part divides `p`. -/
theorem sqfreePart_dvd (p : DensePoly R) : sqfreePart p ∣ p := by
  rcases eq_or_ne p 0 with rfl | hp
  · exact dvd_zero _
  · exact ⟨DensePolyGcd.gcd p (deriv p),
      (gcd_deriv_mul_sqfreePart hp).symm.trans (mul_comm _ _)⟩

/-- The squarefree part of a nonzero polynomial is nonzero. -/
theorem sqfreePart_ne_zero {p : DensePoly R} (hp : p ≠ 0) : sqfreePart p ≠ 0 := fun h0 =>
  hp (by rw [← gcd_deriv_mul_sqfreePart hp, h0, mul_zero])

omit [DensePolyGcd R] in
/-- The derivative of a nonconstant polynomial is nonzero in characteristic zero. -/
theorem deriv_ne_zero [CharZero R] {p : DensePoly R} (hp : 1 < p.size) : deriv p ≠ 0 := by
  intro h0
  have hcoeff := coeff_deriv p (p.size - 2)
  rw [h0, coeff_zero] at hcoeff
  have hlast : p.coeff (p.size - 1) ≠ 0 := coeff_last_ne_zero_of_pos_size p (by omega)
  rw [show p.size - 2 + 1 = p.size - 1 by omega] at hcoeff
  exact mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) hlast hcoeff.symm

end DensePoly

namespace DensePoly

/-- Squarefreeness transfers along `Associated`. -/
private theorem squarefree_of_associated {α : Type u} [CommMonoid α] {a b : α}
    (h : Associated a b) (ha : Squarefree a) : Squarefree b := fun x hx =>
  ha x (hx.trans h.symm.dvd)

variable {R : Type u} [Field R] [DecidableEq R] [DensePolyGcd R]

/-- Across the bridge, the squarefree part is associated to Mathlib's `p / gcd(p, p′)` —
our gcd is associated to Mathlib's, so the exact quotients are associated too. -/
theorem toPolynomial_sqfreePart_associated {p : DensePoly R} (hp : p ≠ 0) :
    Associated (toPolynomial (sqfreePart p))
      (toPolynomial p / EuclideanDomain.gcd (toPolynomial p)
        (Polynomial.derivative (toPolynomial p))) := by
  have hassoc := toPolynomial_gcd_associated p (deriv p)
  rw [toPolynomial_deriv] at hassoc
  set G := EuclideanDomain.gcd (toPolynomial p) (Polynomial.derivative (toPolynomial p))
    with hGdef
  have hp' : toPolynomial p ≠ 0 := toPolynomial_ne_zero hp
  have hG0 : G ≠ 0 := fun h => hp' (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  have hGs : G * (toPolynomial p / G) = toPolynomial p :=
    EuclideanDomain.mul_div_cancel' hG0 (EuclideanDomain.gcd_dvd_left _ _)
  have hours : toPolynomial (DensePolyGcd.gcd p (deriv p)) * toPolynomial (sqfreePart p)
      = toPolynomial p := by
    rw [← toPolynomial_mul, gcd_deriv_mul_sqfreePart hp]
  obtain ⟨u, hu⟩ := hassoc
  have hcancel : toPolynomial (sqfreePart p) = ↑u * (toPolynomial p / G) := by
    have hg0 : toPolynomial (DensePolyGcd.gcd p (deriv p)) ≠ 0 :=
      toPolynomial_ne_zero (DensePolyGcd.gcd_ne_zero_of_left hp _)
    apply mul_left_cancel₀ hg0
    rw [hours, show toPolynomial (DensePolyGcd.gcd p (deriv p)) * (↑u * (toPolynomial p / G))
        = (toPolynomial (DensePolyGcd.gcd p (deriv p)) * ↑u) * (toPolynomial p / G) by ring,
      hu, hGs]
  exact Associated.symm
    (⟨u, by rw [hcancel]; ring⟩ : Associated (toPolynomial p / G) (toPolynomial (sqfreePart p)))

/-- **The squarefree part is squarefree** (characteristic zero): transported from the
Mathlib-side multiplicity keystone across the bridge and the gcd agreement. -/
theorem squarefree_sqfreePart [CharZero R] {p : DensePoly R} (hp : p ≠ 0) :
    Squarefree (sqfreePart p) := by
  rw [← squarefree_toPolynomial_iff]
  exact squarefree_of_associated (toPolynomial_sqfreePart_associated hp).symm
    (Polynomial.squarefree_div_gcd_derivative (toPolynomial_ne_zero hp))

/-- **The gcd glue**: the gcd of `g := gcd(p, p′)` with the squarefree part of `p` is the
squarefree part of `g` — both are the radical of `g`, via the coverage keystone. -/
theorem gcd_deriv_gcd_sqfreePart_associated [CharZero R] {p : DensePoly R} (hp : p ≠ 0) :
    Associated (DensePolyGcd.gcd (DensePolyGcd.gcd p (deriv p)) (sqfreePart p))
      (sqfreePart (DensePolyGcd.gcd p (deriv p))) := by
  set g := DensePolyGcd.gcd p (deriv p) with hgdef
  have hg0 : g ≠ 0 := DensePolyGcd.gcd_ne_zero_of_left hp _
  have hs0 : sqfreePart p ≠ 0 := sqfreePart_ne_zero hp
  apply associated_of_dvd_dvd
  · have hXsq : Squarefree (DensePolyGcd.gcd g (sqfreePart p)) :=
      (squarefree_sqfreePart hp).squarefree_of_dvd
        (DensePolyGcd.gcd_dvd_right g (sqfreePart p))
    have h1 := Polynomial.squarefree_dvd_div_gcd_derivative
      (squarefree_toPolynomial_iff.mpr hXsq) (toPolynomial_ne_zero hg0)
      (toPolynomial_dvd (DensePolyGcd.gcd_dvd_left g (sqfreePart p)))
    exact dvd_of_toPolynomial_dvd
      (h1.trans (toPolynomial_sqfreePart_associated hg0).symm.dvd)
  · refine DensePolyGcd.dvd_gcd g (sqfreePart p) (sqfreePart_dvd g) ?_
    have h1 := Polynomial.squarefree_dvd_div_gcd_derivative
      (squarefree_toPolynomial_iff.mpr (squarefree_sqfreePart hg0))
      (toPolynomial_ne_zero hp)
      (toPolynomial_dvd ((sqfreePart_dvd g).trans (DensePolyGcd.gcd_dvd_left p (deriv p))))
    exact dvd_of_toPolynomial_dvd
      (h1.trans (toPolynomial_sqfreePart_associated hp).symm.dvd)

end DensePoly

end DeepWiki.CAlgebra
