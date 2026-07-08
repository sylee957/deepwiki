import DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner.BivariateView

/-! # Divisibility through Lazard-view combinations

Divisibility aggregation for finite `K[x][y]` combinations after applying `lazardView`.
-/

open MvPolynomial MonomialOrder

namespace DeepWiki.SymbolicIntegration

/-- **Divisibility propagates through a `K[x][y]` combination** (Part B core, IH-aggregation half).
If `P ∣ lazardView b` for every `b` in the support of a finite combination `R = ∑ b ∈ s, h b · b`,
then `P ∣ lazardView R` — `lazardView` is a ring hom, so the divisor of every factor divides the
sum. This is the step that turns a per-element induction hypothesis into divisibility of `R`. -/
theorem dvd_lazardView_sum {K : Type*} [Field K] {P : Polynomial (MvPolynomial (Fin 1) K)}
    {s : Finset (MvPolynomial (Fin 2) K)} {h : MvPolynomial (Fin 2) K → MvPolynomial (Fin 2) K}
    (hdvd : ∀ b ∈ s, P ∣ lazardView b) :
    P ∣ lazardView (∑ b ∈ s, h b * b) := by
  rw [lazardView, map_sum]
  refine Finset.dvd_sum (fun b hb => ?_)
  rw [map_mul]
  exact Dvd.dvd.mul_left ((hdvd b hb)) _

/-- The `Polynomial.C d` specialization of `dvd_lazardView_sum`. -/
theorem C_dvd_lazardView_sum {K : Type*} [Field K] {d : MvPolynomial (Fin 1) K}
    {s : Finset (MvPolynomial (Fin 2) K)} {h : MvPolynomial (Fin 2) K → MvPolynomial (Fin 2) K}
    (hdvd : ∀ b ∈ s, Polynomial.C d ∣ lazardView b) :
    Polynomial.C d ∣ lazardView (∑ b ∈ s, h b * b) :=
  dvd_lazardView_sum hdvd

end DeepWiki.SymbolicIntegration
