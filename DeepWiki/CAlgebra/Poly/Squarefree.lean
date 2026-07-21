import DeepWiki.CAlgebra.Poly.Derivative
import DeepWiki.CAlgebra.Gcd
import Mathlib.FieldTheory.Perfect
import DeepWiki.Algebra.SquarefreeGcd

/-! # Squarefreeness of dense polynomials

The squarefree kernel over a perfect field (in particular any field of characteristic zero):
the derivative criterion `Squarefree p ↔ IsCoprime p (deriv p)` by transport through the bridge
and Mathlib's `separable_iff_squarefree`, the resulting **decidability of `Squarefree`** (a gcd
size test, hypothesis-free), and the squarefree part `sqfreePart p = p / gcd(p, deriv p)` with its
exact-division satellites. -/

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

/-! ### Musser's squarefree decomposition -/

/-- Musser's squarefree decomposition: the output list `[p₁, p₂, …]` collects the squarefree
factors so that `p` is a constant multiple of `∏ pᵢ^i`. The recursion descends along
`gcd(p, deriv p)`, whose size strictly drops in characteristic zero — no fuel needed. All
divisions are exact by gcd divisibility. -/
def sqfDecomp [CharZero R] (p : DensePoly R) : List (DensePoly R) :=
  if p.size ≤ 1 then []
  else
    if (DensePolyGcd.gcd p (deriv p)).size ≤ 1 then [p]
    else
      div (sqfreePart p) (DensePolyGcd.gcd (DensePolyGcd.gcd p (deriv p)) (sqfreePart p)) ::
        sqfDecomp (DensePolyGcd.gcd p (deriv p))
  termination_by p.size
  decreasing_by
    rename_i h1 _
    have hd0 : deriv p ≠ 0 := deriv_ne_zero (by omega)
    calc (DensePolyGcd.gcd p (deriv p)).size
        ≤ (deriv p).size := size_le_size_of_dvd hd0 (DensePolyGcd.gcd_dvd_right p (deriv p))
      _ ≤ p.size - 1 := size_deriv_le p
      _ < p.size := by omega

/-- Every factor produced by the squarefree decomposition is squarefree. -/
theorem squarefree_of_mem_sqfDecomp [CharZero R] {p f : DensePoly R} (hf : f ∈ sqfDecomp p) :
    Squarefree f := by
  induction p using sqfDecomp.induct with
  | case1 p h1 =>
      rw [sqfDecomp, if_pos h1] at hf
      exact absurd hf (List.not_mem_nil)
  | case2 p h1 h2 =>
      rw [sqfDecomp, if_neg h1, if_pos h2] at hf
      have hp0 : p ≠ 0 := fun h0 => h1 (by rw [h0]; simp [size_zero])
      have hg1 : (DensePolyGcd.gcd p (deriv p)).size = 1 := by
        have := DensePolyGcd.gcd_ne_zero_of_left hp0 (deriv p)
        have hpos : 0 < (DensePolyGcd.gcd p (deriv p)).size :=
          Nat.pos_of_ne_zero (fun h0 => this (eq_zero_of_size_zero h0))
        omega
      rw [List.mem_singleton] at hf
      subst hf
      exact squarefree_iff_gcd_deriv_size.mpr hg1
  | case3 p h1 h2 ih =>
      rw [sqfDecomp, if_neg h1, if_neg h2, List.mem_cons] at hf
      rcases hf with rfl | hf
      · have hp0 : p ≠ 0 := fun h0 => h1 (by rw [h0]; simp [size_zero])
        have hs0 : sqfreePart p ≠ 0 := sqfreePart_ne_zero hp0
        have hdvd : div (sqfreePart p)
            (DensePolyGcd.gcd (DensePolyGcd.gcd p (deriv p)) (sqfreePart p))
            ∣ sqfreePart p := by
          refine ⟨DensePolyGcd.gcd (DensePolyGcd.gcd p (deriv p)) (sqfreePart p), ?_⟩
          have hg0 : DensePolyGcd.gcd (DensePolyGcd.gcd p (deriv p)) (sqfreePart p) ≠ 0 :=
            DensePolyGcd.gcd_ne_zero_of_right hs0 _
          have hmd : DensePolyGcd.gcd (DensePolyGcd.gcd p (deriv p)) (sqfreePart p) *
              div (sqfreePart p) (DensePolyGcd.gcd (DensePolyGcd.gcd p (deriv p)) (sqfreePart p))
              = sqfreePart p :=
            EuclideanDomain.mul_div_cancel' hg0
              (DensePolyGcd.gcd_dvd_right (DensePolyGcd.gcd p (deriv p)) (sqfreePart p))
          exact hmd.symm.trans (mul_comm _ _)
        exact (squarefree_sqfreePart hp0).squarefree_of_dvd hdvd
      · exact ih hf

/-- **Exponent-exact reconstruction**: `p` is a constant multiple of `∏ᵢ pᵢ^i` over its
squarefree decomposition (staircase exponents starting at `1`), and the plain product of the
factors is the squarefree part. -/
theorem sqfDecomp_spec [CharZero R] {p : DensePoly R} (hp : p ≠ 0) :
    Associated p (powProd (sqfDecomp p) 1) ∧
      Associated (sqfreePart p) (sqfDecomp p).prod := by
  induction p using sqfDecomp.induct with
  | case1 p h1 =>
      rw [sqfDecomp, if_pos h1]
      have hs1 : p.size = 1 := by
        have : p.size ≠ 0 := fun h0 => hp (eq_zero_of_size_zero h0)
        omega
      have hd0 : deriv p = 0 :=
        eq_zero_of_size_zero (by have := size_deriv_le p; omega)
      have hgp : Associated (DensePolyGcd.gcd p (deriv p)) p :=
        associated_of_dvd_dvd (DensePolyGcd.gcd_dvd_left p (deriv p))
          (DensePolyGcd.dvd_gcd p (deriv p) (dvd_refl p) (by rw [hd0]; exact dvd_zero p))
      obtain ⟨u, hu⟩ := hgp
      have hcancel : sqfreePart p = ↑u :=
        mul_left_cancel₀ (DensePolyGcd.gcd_ne_zero_of_left hp _)
          ((gcd_deriv_mul_sqfreePart hp).trans hu.symm)
      constructor
      · exact associated_one_iff_isUnit.mpr (isUnit_iff_size_eq_one.mpr hs1)
      · rw [List.prod_nil, hcancel]
        exact associated_one_iff_isUnit.mpr u.isUnit
  | case2 p h1 h2 =>
      rw [sqfDecomp, if_neg h1, if_pos h2]
      have hp0 : p ≠ 0 := fun h0 => h1 (by rw [h0]; simp [size_zero])
      have hs := gcd_deriv_mul_sqfreePart hp0
      have hg1 : (DensePolyGcd.gcd p (deriv p)).size = 1 := by
        have hne := DensePolyGcd.gcd_ne_zero_of_left hp0 (deriv p)
        have hpos : 0 < (DensePolyGcd.gcd p (deriv p)).size :=
          Nat.pos_of_ne_zero (fun h0 => hne (eq_zero_of_size_zero h0))
        omega
      obtain ⟨ug, hug⟩ := isUnit_iff_size_eq_one.mpr hg1
      constructor
      · show Associated p (p ^ 1 * powProd [] 2)
        simp only [powProd, pow_one, mul_one]
        exact Associated.refl p
      · rw [List.prod_cons, List.prod_nil, mul_one]
        exact ⟨ug, by rw [mul_comm, hug]; exact hs⟩
  | case3 p h1 h2 ih =>
      have hp0 : p ≠ 0 := fun h0 => h1 (by rw [h0]; simp [size_zero])
      have hg0 : DensePolyGcd.gcd p (deriv p) ≠ 0 :=
        DensePolyGcd.gcd_ne_zero_of_left hp0 _
      obtain ⟨ih1, ih2⟩ := ih hg0
      rw [sqfDecomp, if_neg h1, if_neg h2]
      set g := DensePolyGcd.gcd p (deriv p) with hgdef
      set s' := sqfreePart p with hsdef
      set X := DensePolyGcd.gcd g s' with hXdef
      set p₁ := div s' X with hp₁def
      have hs : g * s' = p := gcd_deriv_mul_sqfreePart hp0
      have hs0 : s' ≠ 0 := sqfreePart_ne_zero hp0
      have hX0 : X ≠ 0 := DensePolyGcd.gcd_ne_zero_of_right hs0 _
      have hXs : X * p₁ = s' :=
        EuclideanDomain.mul_div_cancel' hX0 (DensePolyGcd.gcd_dvd_right g s')
      have hXL : Associated X (sqfDecomp g).prod :=
        (gcd_deriv_gcd_sqfreePart_associated hp0).trans ih2
      constructor
      · show Associated p (p₁ ^ 1 * powProd (sqfDecomp g) 2)
        rw [pow_one, show (2 : ℕ) = 1 + 1 from rfl, powProd_succ]
        have hkey : p = p₁ * (g * X) := by rw [← hs, ← hXs]; ring
        rw [hkey]
        exact (Associated.refl _).mul_mul (ih1.mul_mul hXL)
      · rw [List.prod_cons, ← hXs, mul_comm X p₁]
        exact (Associated.refl _).mul_mul hXL

end DensePoly

end DeepWiki.CAlgebra
