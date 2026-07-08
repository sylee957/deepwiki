import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.MvPolynomial.Ideal
import DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner.ReducedBasis
import DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner.BivariateView

/-! # Bounded Gröbner representations

Lexicographic Gröbner reduction of ideal members with bounded `y`-degree contributors.
-/

open MvPolynomial MonomialOrder

namespace DeepWiki.SymbolicIntegration

variable {σ : Type*} {m : MonomialOrder σ}

open scoped Classical in
/-- **GB-reduction of an ideal member with `y`-degree control** (the combinatorial input to the
descent). For a reduced Gröbner basis over lex and `R ∈ I`, `R = ∑ b ∈ B, (g b) · b` where every
contributing basis element has `y`-degree `degreeOf 0 b ≤ degreeOf 0 R` — the lex division-algorithm
remainder is `0` (GB) and each quotient summand's `y`-degree is dominated by `R`'s. -/
theorem exists_yDegree_bounded_representation {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    {R : MvPolynomial (Fin 2) K} (hRI : R ∈ I) (hR0 : R ≠ 0) :
    ∃ g : MvPolynomial (Fin 2) K → MvPolynomial (Fin 2) K,
      R = ∑ b ∈ B, g b * b ∧
        ∀ b ∈ B, g b * b ≠ 0 → degreeOf 0 b ≤ degreeOf 0 R := by
  classical
  obtain ⟨c, r, hcr, hcdeg, hrem⟩ := MonomialOrder.div_set hB.isGroebnerBasis.2.1 R
  have hr0 : r = 0 := (hB.isGroebnerBasis.mem_iff_div_remainder_eq_zero R hcr hrem).mp hRI
  -- the `div_set` combination as a `B`-indexed sum, extended by `0` off `B`.
  refine ⟨fun b => if hb : b ∈ B then c ⟨b, Finset.mem_coe.mpr hb⟩ else 0, ?_, ?_⟩
  · rw [hcr, hr0, add_zero, Finsupp.linearCombination_apply,
      Finsupp.sum_fintype _ _ (fun b => by rw [zero_smul])]
    -- `∑ b : B, (c b) • ↑b = ∑ b ∈ B.attach, (c b) • ↑b = ∑ b ∈ B, g b * b`.
    rw [← Finset.sum_attach B (fun b => (if hb : b ∈ B then c ⟨b, Finset.mem_coe.mpr hb⟩ else 0) * b)]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    have hbB : (b : MvPolynomial (Fin 2) K) ∈ B := Finset.mem_coe.mp b.2
    rw [smul_eq_mul, dif_pos hbB, mul_comm]
  · intro b hb hbne
    have hbg : c ⟨b, Finset.mem_coe.mpr hb⟩ * b ≠ 0 := by
      simpa [hb] using hbne
    have hcdeg' : MonomialOrder.lex.degree ((b : MvPolynomial (Fin 2) K) * c ⟨b, Finset.mem_coe.mpr hb⟩)
        ≼[MonomialOrder.lex] MonomialOrder.lex.degree R := hcdeg ⟨b, Finset.mem_coe.mpr hb⟩
    have hbg' : (b : MvPolynomial (Fin 2) K) * c ⟨b, Finset.mem_coe.mpr hb⟩ ≠ 0 := by
      rwa [mul_comm] at hbg
    have hle : degreeOf 0 ((b : MvPolynomial (Fin 2) K) * c ⟨b, Finset.mem_coe.mpr hb⟩)
        ≤ degreeOf 0 R := degreeOf_le_of_lex_degree_le hbg' hR0 hcdeg'
    rw [mul_comm] at hle
    exact le_trans (degreeOf_le_degreeOf_mul hbg) hle

/-- A divisor of all bounded basis contributors divides the `lazardView` of the represented element. -/
theorem dvd_lazardView_of_mem_of_dvd_bounded {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    {P : Polynomial (MvPolynomial (Fin 1) K)} {R : MvPolynomial (Fin 2) K}
    (hRI : R ∈ I) (hR0 : R ≠ 0)
    (hdvd : ∀ b ∈ B, degreeOf 0 b ≤ degreeOf 0 R → P ∣ lazardView b) :
    P ∣ lazardView R := by
  obtain ⟨g, hgsum, hgdeg⟩ := exists_yDegree_bounded_representation hB hRI hR0
  rw [hgsum, lazardView, map_sum]
  refine Finset.dvd_sum (fun b hb => ?_)
  by_cases hbne : g b * b = 0
  · rw [hbne, map_zero]; exact dvd_zero _
  · rw [map_mul]
    exact Dvd.dvd.mul_left (hdvd b hb (hgdeg b hb hbne)) _

/-- **`C d` divides the `K[x][y]` view of any `y`-degree-bounded ideal member** (the bounded-rep +
sum half of the descent). If `R ∈ I`, `R ≠ 0`, and `C d ∣ lazardView b` for every basis element `b`
of `y`-degree `≤ degreeOf 0 R`, then `C d ∣ lazardView R`: GB-reduce `R = ∑ b ∈ B, g b · b` with each
contributing `b` of bounded `y`-degree (`exists_yDegree_bounded_representation`), then aggregate by
`dvd_lazardView_of_mem_of_dvd_bounded`. -/
theorem C_dvd_lazardView_of_mem_of_dvd_bounded {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    {d : MvPolynomial (Fin 1) K} {R : MvPolynomial (Fin 2) K} (hRI : R ∈ I) (hR0 : R ≠ 0)
    (hdvd : ∀ b ∈ B, degreeOf 0 b ≤ degreeOf 0 R → Polynomial.C d ∣ lazardView b) :
    Polynomial.C d ∣ lazardView R :=
  dvd_lazardView_of_mem_of_dvd_bounded hB hRI hR0 hdvd

end DeepWiki.SymbolicIntegration
