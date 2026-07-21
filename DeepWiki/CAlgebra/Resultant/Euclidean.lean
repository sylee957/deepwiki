import DeepWiki.CAlgebra.Resultant.Sylvester
import DeepWiki.CAlgebra.Poly.DivisionPseudo

/-! # Resultant via the pseudo-remainder sequence

The Euclidean-descent resultant over a computable Euclidean domain of coefficients: reduce
the larger argument by pseudo-division, correct by leading-coefficient powers and signs, pad
slack degree bounds down. Each algorithm branch mirrors one Mathlib resultant identity
(`resultant_add_mul_right`, `resultant_C_mul_right`, `resultant_add_left_deg`,
`resultant_add_right_deg`, `resultant_comm`, and the constant/zero base cases), so the
equivalence `resultantPRSEuclidean_eq` with the Sylvester-determinant resultant is a functional
induction gluing those identities — polynomial-time where the determinant is factorial. -/

open Polynomial

namespace DeepWiki.CAlgebra

universe u

namespace DensePoly

variable {S : Type u} [EuclideanDomain S] [DecidableEq S]

/-! ### Bridges (any coefficient ring) -/

private theorem natDeg_bridge {f : DensePoly S} (hf : f ≠ 0) :
    (toPolynomial f).natDegree = f.size - 1 := by
  rw [natDegree_toPolynomial, degree?, if_neg (fun h0 => hf (eq_zero_of_size_zero h0))]
  rfl

private theorem lc_bridge {f : DensePoly S} (hf : f ≠ 0) :
    (toPolynomial f).leadingCoeff = f.leadingCoeff := by
  rw [Polynomial.leadingCoeff, natDeg_bridge hf, coeff_toPolynomial, leadingCoeff]

omit [DecidableEq S] in
private theorem ed_mul_div_cancel_left {a b : S} (ha : a ≠ 0) : a * b / a = b :=
  mul_left_cancel₀ ha (EuclideanDomain.mul_div_cancel' ha (Dvd.intro b rfl))

/-- The transported pseudo-division identity. -/
private theorem pseudo_identity {f g : DensePoly S} (hg : g.size ≠ 0) :
    toPolynomial (pseudoDiv f g) * toPolynomial g + toPolynomial (pseudoMod f g)
      = Polynomial.C (g.leadingCoeff ^ (f.size + 1 - g.size)) * toPolynomial f := by
  have h := congrArg toPolynomial (pseudoDivMod_spec hg f)
  simp only [toPolynomial_mul, toPolynomial_add, toPolynomial_C] at h
  rw [pseudoDiv, pseudoMod]
  exact h

/-- The pseudo-quotient's degree bound, derived from the identity (no implementation facts). -/
private theorem pseudoDiv_natDegree_le {f g : DensePoly S} (hg : g ≠ 0) (hfg : g.size ≤ f.size)
    (hq0 : pseudoDiv f g ≠ 0) :
    (toPolynomial (pseudoDiv f g)).natDegree + (g.size - 1) ≤ f.size - 1 := by
  have hgz : g.size ≠ 0 := fun h0 => hg (eq_zero_of_size_zero h0)
  have hf0 : f ≠ 0 := fun h0 => by rw [h0, size_zero] at hfg; omega
  have hid := pseudo_identity (f := f) hgz
  have hgne : toPolynomial g ≠ 0 := toPolynomial_ne_zero hg
  have hqne : toPolynomial (pseudoDiv f g) ≠ 0 := toPolynomial_ne_zero hq0
  have hprod : (toPolynomial (pseudoDiv f g) * toPolynomial g).natDegree
      = (toPolynomial (pseudoDiv f g)).natDegree + (g.size - 1) := by
    rw [Polynomial.natDegree_mul hqne hgne, natDeg_bridge hg]
  have h1 : toPolynomial (pseudoDiv f g) * toPolynomial g
      = Polynomial.C (g.leadingCoeff ^ (f.size + 1 - g.size)) * toPolynomial f
        - toPolynomial (pseudoMod f g) := by rw [← hid]; ring
  have hle : (toPolynomial (pseudoDiv f g) * toPolynomial g).natDegree ≤ f.size - 1 := by
    rw [h1]
    refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
    · exact le_trans (Polynomial.natDegree_C_mul_le _ _) (le_of_eq (natDeg_bridge hf0))
    · rcases eq_or_ne (pseudoMod f g) 0 with hr0 | hr0
      · simp [hr0]
      · have := pseudoMod_size_lt hgz f
        rw [natDeg_bridge hr0]
        omega
  omega

/-! ### The algorithm -/

/-- **The parametrized descent engine**: pseudo-divide the larger argument, strip a factor
from the remainder through `clean` (trivially nothing, or the content — each strip costs one
`resultant_C_mul_right` in the equivalence proof), correct by signs and leading-coefficient
powers (exact divisions), pad slack bounds down. `hsize` feeds termination; the bound
parameters are internal recursion state — public entries fix them at the canonical
degrees. -/
def resultantDescent (clean : DensePoly S → S × DensePoly S)
    (hsize : ∀ r, (clean r).2.size ≤ r.size) (f g : DensePoly S) (m n : ℕ) : S :=
  if hf0 : f = 0 then 0 ^ n * g.coeff 0 ^ m
  else if hg0 : g = 0 then 0 ^ m * f.coeff 0 ^ n
  else if m + 1 < f.size then 0
  else if n + 1 < g.size then 0
  else if _ : f.size ≤ m then
    (-1 : S) ^ (n * (m - (f.size - 1))) * g.coeff n ^ (m - (f.size - 1))
      * resultantDescent clean hsize f g (f.size - 1) n
  else if _ : g.size ≤ n then
    f.coeff m ^ (n - (g.size - 1)) * resultantDescent clean hsize f g m (g.size - 1)
  else if n = 0 then g.coeff 0 ^ m
  else if m = 0 then f.coeff 0 ^ n
  else if _ : g.size ≤ f.size then
    (-1 : S) ^ (m * n) *
      ((clean (pseudoMod f g)).1 ^ n
          * resultantDescent clean hsize g (clean (pseudoMod f g)).2 n m
        / g.leadingCoeff ^ ((f.size + 1 - g.size) * n))
  else
    (clean (pseudoMod g f)).1 ^ m
        * resultantDescent clean hsize f (clean (pseudoMod g f)).2 m n
      / f.leadingCoeff ^ ((g.size + 1 - f.size) * m)
  termination_by (f.size + g.size, m + n)
  decreasing_by
    · apply Prod.Lex.right
      have h1 : f.size ≠ 0 := fun h0 => hf0 (eq_zero_of_size_zero h0)
      omega
    · apply Prod.Lex.right
      have h1 : g.size ≠ 0 := fun h0 => hg0 (eq_zero_of_size_zero h0)
      omega
    · apply Prod.Lex.left
      have h1 : (pseudoMod f g).size < g.size :=
        pseudoMod_size_lt (fun h0 => hg0 (eq_zero_of_size_zero h0)) f
      have h2 := hsize (pseudoMod f g)
      omega
    · apply Prod.Lex.left
      have h1 : (pseudoMod g f).size < f.size :=
        pseudoMod_size_lt (fun h0 => hf0 (eq_zero_of_size_zero h0)) g
      have h2 := hsize (pseudoMod g f)
      omega

/-! ### Equivalence with the Sylvester determinant -/

/-- **The descent computes the Sylvester-determinant resultant** on valid bounds, for any
`clean` satisfying the reconstruction identity: each branch is one Mathlib resultant
identity, the strip costing one `resultant_C_mul_right`. -/
theorem resultantDescent_eq (clean : DensePoly S → S × DensePoly S)
    (hsize : ∀ r, (clean r).2.size ≤ r.size)
    (hclean : ∀ r, C (clean r).1 * (clean r).2 = r) (f g : DensePoly S) (m n : ℕ) :
    (toPolynomial f).natDegree ≤ m → (toPolynomial g).natDegree ≤ n →
    resultantDescent clean hsize f g m n
      = (toPolynomial f).resultant (toPolynomial g) m n := by
  induction f, g, m, n using resultantDescent.induct (clean := clean) (hsize := hsize) with
  | case1 g m n =>
      intro hm hn
      rw [resultantDescent, dif_pos rfl, toPolynomial_zero, Polynomial.resultant_zero_left,
        coeff_toPolynomial]
  | case2 f m n hf0 =>
      intro hm hn
      rw [resultantDescent, dif_neg hf0, dif_pos rfl, toPolynomial_zero,
        Polynomial.resultant_zero_right, coeff_toPolynomial]
  | case3 f g m n hf0 hg0 hm1 =>
      intro hm hn
      rw [natDeg_bridge hf0] at hm
      exact absurd hm1 (by omega)
  | case4 f g m n hf0 hg0 hm1 hn1 =>
      intro hm hn
      rw [natDeg_bridge hg0] at hn
      exact absurd hn1 (by omega)
  | case5 f g m n hf0 hg0 hm1 hn1 hmd ih =>
      intro hm hn
      rw [resultantDescent, dif_neg hf0, dif_neg hg0, if_neg hm1, if_neg hn1, dif_pos hmd]
      rw [ih (le_of_eq (natDeg_bridge hf0)) hn]
      have hkey := Polynomial.resultant_add_left_deg (f := toPolynomial f)
        (g := toPolynomial g) (m := f.size - 1) (n := n) (k := m - (f.size - 1))
        (le_of_eq (natDeg_bridge hf0))
      rw [show f.size - 1 + (m - (f.size - 1)) = m from by
        have : f.size ≠ 0 := fun h0 => hf0 (eq_zero_of_size_zero h0)
        omega] at hkey
      rw [hkey, coeff_toPolynomial]
  | case6 f g m n hf0 hg0 hm1 hn1 hmd hnd ih =>
      intro hm hn
      rw [resultantDescent, dif_neg hf0, dif_neg hg0, if_neg hm1, if_neg hn1, dif_neg hmd,
        dif_pos hnd]
      rw [ih hm (le_of_eq (natDeg_bridge hg0))]
      have hkey := Polynomial.resultant_add_right_deg (f := toPolynomial f)
        (g := toPolynomial g) (m := m) (n := g.size - 1) (n - (g.size - 1))
        (le_of_eq (natDeg_bridge hg0))
      rw [show g.size - 1 + (n - (g.size - 1)) = n from by
        have : g.size ≠ 0 := fun h0 => hg0 (eq_zero_of_size_zero h0)
        omega] at hkey
      rw [hkey, coeff_toPolynomial]
  | case7 f g m hf0 hg0 hm1 hmd hn1 hnd =>
      intro hm hn
      rw [resultantDescent, dif_neg hf0, dif_neg hg0, if_neg hm1, if_neg hn1, dif_neg hmd,
        dif_neg hnd, if_pos rfl]
      have hg1 : g.size = 1 := by
        have : g.size ≠ 0 := fun h0 => hg0 (eq_zero_of_size_zero h0)
        omega
      rw [show toPolynomial g = Polynomial.C (g.coeff 0) from by
        conv_lhs => rw [eq_C_of_size_eq_one hg1]
        rw [toPolynomial_C]]
      rw [Polynomial.resultant_C_zero_right]
  | case8 f g n hf0 hg0 hn1 hnd hn0 hm1 hmd =>
      intro hm hn
      rw [resultantDescent, dif_neg hf0, dif_neg hg0, if_neg hm1, if_neg hn1, dif_neg hmd,
        dif_neg hnd, if_neg hn0, if_pos rfl]
      have hf1 : f.size = 1 := by
        have : f.size ≠ 0 := fun h0 => hf0 (eq_zero_of_size_zero h0)
        omega
      rw [show toPolynomial f = Polynomial.C (f.coeff 0) from by
        conv_lhs => rw [eq_C_of_size_eq_one hf1]
        rw [toPolynomial_C]]
      rw [Polynomial.resultant_C_zero_left]
  | case9 f g m n hf0 hg0 hm1 hn1 hmd hnd hn0 hm0 hfg ih =>
      intro hm hn
      have hgz : g.size ≠ 0 := fun h0 => hg0 (eq_zero_of_size_zero h0)
      have hlc : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero hgz
      have hlcp : g.leadingCoeff ^ ((f.size + 1 - g.size) * n) ≠ 0 := pow_ne_zero _ hlc
      have hr_deg : (toPolynomial (clean (pseudoMod f g)).2).natDegree ≤ m := by
        rcases eq_or_ne (clean (pseudoMod f g)).2 0 with hr0 | hr0
        · simp [hr0]
        · have h1 := pseudoMod_size_lt hgz f
          have h2 := hsize (pseudoMod f g)
          rw [natDeg_bridge hr0]
          rw [natDeg_bridge hf0] at hm
          omega
      rw [resultantDescent, dif_neg hf0, dif_neg hg0, if_neg hm1, if_neg hn1, dif_neg hmd,
        dif_neg hnd, if_neg hn0, if_neg hm0, dif_pos hfg]
      rw [ih (by rw [natDeg_bridge hg0]; omega) hr_deg]
      have hcr : Polynomial.C (clean (pseudoMod f g)).1
            * toPolynomial (clean (pseudoMod f g)).2
          = toPolynomial (pseudoMod f g) := by
        have h := congrArg toPolynomial (hclean (pseudoMod f g))
        simpa [toPolynomial_mul, toPolynomial_C] using h
      have hchain : (clean (pseudoMod f g)).1 ^ n
            * (toPolynomial g).resultant (toPolynomial (clean (pseudoMod f g)).2) n m
          = g.leadingCoeff ^ ((f.size + 1 - g.size) * n)
            * (toPolynomial g).resultant (toPolynomial f) n m := by
        rw [← Polynomial.resultant_C_mul_right, hcr]
        have hCf : Polynomial.C (g.leadingCoeff ^ (f.size + 1 - g.size)) * toPolynomial f
            = toPolynomial (pseudoMod f g)
              + toPolynomial g * toPolynomial (pseudoDiv f g) := by
          rw [← pseudo_identity hgz]
          ring
        calc (toPolynomial g).resultant (toPolynomial (pseudoMod f g)) n m
            = (toPolynomial g).resultant
                (toPolynomial (pseudoMod f g)
                  + toPolynomial g * toPolynomial (pseudoDiv f g)) n m := by
              rcases eq_or_ne (pseudoDiv f g) 0 with hq0 | hq0
              · rw [hq0, toPolynomial_zero, mul_zero, add_zero]
              · rw [Polynomial.resultant_add_mul_right _ _ _ _ _
                  (by
                    have h1 := pseudoDiv_natDegree_le hg0 hfg hq0
                    rw [natDeg_bridge hg0] at hn
                    rw [natDeg_bridge hf0] at hm
                    omega)
                  (by rw [natDeg_bridge hg0]; omega)]
          _ = (toPolynomial g).resultant
                (Polynomial.C (g.leadingCoeff ^ (f.size + 1 - g.size)) * toPolynomial f)
                n m := by rw [hCf]
          _ = g.leadingCoeff ^ ((f.size + 1 - g.size) * n)
              * (toPolynomial g).resultant (toPolynomial f) n m := by
              rw [Polynomial.resultant_C_mul_right, ← pow_mul]
      rw [hchain, ed_mul_div_cancel_left hlcp]
      rw [Polynomial.resultant_comm, mul_comm n m, ← mul_assoc, ← pow_add, ← two_mul,
        pow_mul]
      simp
  | case10 f g m n hf0 hg0 hm1 hn1 hmd hnd hn0 hm0 hfg ih =>
      intro hm hn
      have hfz : f.size ≠ 0 := fun h0 => hf0 (eq_zero_of_size_zero h0)
      have hlc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero hfz
      have hlcp : f.leadingCoeff ^ ((g.size + 1 - f.size) * m) ≠ 0 := pow_ne_zero _ hlc
      have hr_deg : (toPolynomial (clean (pseudoMod g f)).2).natDegree ≤ n := by
        rcases eq_or_ne (clean (pseudoMod g f)).2 0 with hr0 | hr0
        · simp [hr0]
        · have h1 := pseudoMod_size_lt hfz g
          have h2 := hsize (pseudoMod g f)
          rw [natDeg_bridge hr0]
          rw [natDeg_bridge hg0] at hn
          omega
      rw [resultantDescent, dif_neg hf0, dif_neg hg0, if_neg hm1, if_neg hn1, dif_neg hmd,
        dif_neg hnd, if_neg hn0, if_neg hm0, dif_neg hfg]
      rw [ih hm hr_deg]
      have hcr : Polynomial.C (clean (pseudoMod g f)).1
            * toPolynomial (clean (pseudoMod g f)).2
          = toPolynomial (pseudoMod g f) := by
        have h := congrArg toPolynomial (hclean (pseudoMod g f))
        simpa [toPolynomial_mul, toPolynomial_C] using h
      have hchain : (clean (pseudoMod g f)).1 ^ m
            * (toPolynomial f).resultant (toPolynomial (clean (pseudoMod g f)).2) m n
          = f.leadingCoeff ^ ((g.size + 1 - f.size) * m)
            * (toPolynomial f).resultant (toPolynomial g) m n := by
        rw [← Polynomial.resultant_C_mul_right, hcr]
        have hCf : Polynomial.C (f.leadingCoeff ^ (g.size + 1 - f.size)) * toPolynomial g
            = toPolynomial (pseudoMod g f)
              + toPolynomial f * toPolynomial (pseudoDiv g f) := by
          rw [← pseudo_identity hfz]
          ring
        calc (toPolynomial f).resultant (toPolynomial (pseudoMod g f)) m n
            = (toPolynomial f).resultant
                (toPolynomial (pseudoMod g f)
                  + toPolynomial f * toPolynomial (pseudoDiv g f)) m n := by
              rcases eq_or_ne (pseudoDiv g f) 0 with hq0 | hq0
              · rw [hq0, toPolynomial_zero, mul_zero, add_zero]
              · rw [Polynomial.resultant_add_mul_right _ _ _ _ _
                  (by
                    have h1 := pseudoDiv_natDegree_le hf0 (by omega) hq0
                    rw [natDeg_bridge hf0] at hm
                    rw [natDeg_bridge hg0] at hn
                    omega)
                  (by rw [natDeg_bridge hf0]; omega)]
          _ = (toPolynomial f).resultant
                (Polynomial.C (f.leadingCoeff ^ (g.size + 1 - f.size)) * toPolynomial g)
                m n := by rw [hCf]
          _ = f.leadingCoeff ^ ((g.size + 1 - f.size) * m)
              * (toPolynomial f).resultant (toPolynomial g) m n := by
              rw [Polynomial.resultant_C_mul_right, ← pow_mul]
      rw [hchain, ed_mul_div_cancel_left hlcp]

/-- **Resultant by the pseudo-remainder sequence** at the canonical degrees — the trivial
instantiation of the descent (no stripping). -/
def resultantPRSEuclidean (f g : DensePoly S) : S :=
  resultantDescent (fun r => (1, r)) (fun _ => le_refl _) f g (f.size - 1) (g.size - 1)

/-- **The PRS resultant agrees with the Sylvester-determinant resultant** at the canonical
degrees — hypothesis-free: functional induction over the descent, each branch discharged by
the matching Mathlib identity. -/
theorem resultantPRSEuclidean_eq (f g : DensePoly S) :
    resultantPRSEuclidean f g = (toPolynomial f).resultant (toPolynomial g)
      (toPolynomial f).natDegree (toPolynomial g).natDegree := by
  rw [resultantPRSEuclidean, natDegree_toPolynomial_eq_size_sub_one,
    natDegree_toPolynomial_eq_size_sub_one]
  exact resultantDescent_eq _ _ (fun r => by rw [← one_def, one_mul]) f g _ _
    (le_of_eq (natDegree_toPolynomial_eq_size_sub_one f))
    (le_of_eq (natDegree_toPolynomial_eq_size_sub_one g))

end DensePoly

end DeepWiki.CAlgebra
