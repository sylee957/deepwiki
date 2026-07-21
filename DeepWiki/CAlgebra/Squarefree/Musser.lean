import DeepWiki.CAlgebra.Squarefree.Basic

/-! # Musser's squarefree decomposition

The reference decomposition algorithm: recursion on `gcd(p, deriv p)` whose size strictly drops
in characteristic zero (no fuel), every division exact by gcd divisibility. Factors are
squarefree (`squarefree_of_mem_sqfDecompMusser`) and reconstruct `p` with staircase exponents
(`sqfDecompMusser_spec`). -/

namespace DeepWiki.CAlgebra

universe u

namespace DensePoly

variable {R : Type u} [Field R] [DecidableEq R] [DensePolyGcd R]

/-- Musser's squarefree decomposition: the output list `[p₁, p₂, …]` collects the squarefree
factors so that `p` is a constant multiple of `∏ pᵢ^i`. The recursion descends along
`gcd(p, deriv p)`, whose size strictly drops in characteristic zero — no fuel needed. All
divisions are exact by gcd divisibility. -/
def sqfDecompMusser [CharZero R] (p : DensePoly R) : List (DensePoly R) :=
  if p.size ≤ 1 then []
  else
    if (DensePolyGcd.gcd p (deriv p)).size ≤ 1 then [p]
    else
      div (sqfreePart p) (DensePolyGcd.gcd (DensePolyGcd.gcd p (deriv p)) (sqfreePart p)) ::
        sqfDecompMusser (DensePolyGcd.gcd p (deriv p))
  termination_by p.size
  decreasing_by
    rename_i h1 _
    have hd0 : deriv p ≠ 0 := deriv_ne_zero (by omega)
    calc (DensePolyGcd.gcd p (deriv p)).size
        ≤ (deriv p).size := size_le_size_of_dvd hd0 (DensePolyGcd.gcd_dvd_right p (deriv p))
      _ ≤ p.size - 1 := size_deriv_le p
      _ < p.size := by omega

/-- Every factor produced by the squarefree decomposition is squarefree. -/
theorem squarefree_of_mem_sqfDecompMusser [CharZero R] {p f : DensePoly R} (hf : f ∈ sqfDecompMusser p) :
    Squarefree f := by
  induction p using sqfDecompMusser.induct with
  | case1 p h1 =>
      rw [sqfDecompMusser, if_pos h1] at hf
      exact absurd hf (List.not_mem_nil)
  | case2 p h1 h2 =>
      rw [sqfDecompMusser, if_neg h1, if_pos h2] at hf
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
      rw [sqfDecompMusser, if_neg h1, if_neg h2, List.mem_cons] at hf
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
theorem sqfDecompMusser_spec [CharZero R] {p : DensePoly R} (hp : p ≠ 0) :
    Associated p (powProd (sqfDecompMusser p) 1) ∧
      Associated (sqfreePart p) (sqfDecompMusser p).prod := by
  induction p using sqfDecompMusser.induct with
  | case1 p h1 =>
      rw [sqfDecompMusser, if_pos h1]
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
      rw [sqfDecompMusser, if_neg h1, if_pos h2]
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
      rw [sqfDecompMusser, if_neg h1, if_neg h2]
      set g := DensePolyGcd.gcd p (deriv p) with hgdef
      set s' := sqfreePart p with hsdef
      set X := DensePolyGcd.gcd g s' with hXdef
      set p₁ := div s' X with hp₁def
      have hs : g * s' = p := gcd_deriv_mul_sqfreePart hp0
      have hs0 : s' ≠ 0 := sqfreePart_ne_zero hp0
      have hX0 : X ≠ 0 := DensePolyGcd.gcd_ne_zero_of_right hs0 _
      have hXs : X * p₁ = s' :=
        EuclideanDomain.mul_div_cancel' hX0 (DensePolyGcd.gcd_dvd_right g s')
      have hXL : Associated X (sqfDecompMusser g).prod :=
        (gcd_deriv_gcd_sqfreePart_associated hp0).trans ih2
      constructor
      · show Associated p (p₁ ^ 1 * powProd (sqfDecompMusser g) 2)
        rw [pow_one, show (2 : ℕ) = 1 + 1 from rfl, powProd_succ]
        have hkey : p = p₁ * (g * X) := by rw [← hs, ← hXs]; ring
        rw [hkey]
        exact (Associated.refl _).mul_mul (ih1.mul_mul hXL)
      · rw [List.prod_cons, ← hXs, mul_comm X p₁]
        exact (Associated.refl _).mul_mul hXL

end DensePoly

end DeepWiki.CAlgebra
