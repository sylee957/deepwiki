import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.MvPolynomial.Equiv
import DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner.BivariateView

/-! # Bivariate Gröbner reduction steps

The basic `K[x][y]` reduction step used in Lazard descent, together with
divisibility transport through the cancelled top `y`-term. -/

open MvPolynomial MonomialOrder

namespace DeepWiki.SymbolicIntegration

/-! ## The reduction-step polynomial

The element `yConst q · fi1 - y^shift · fi` is the local cancellation used to lower
`y`-degree in the bivariate Lazard argument. -/

/-- The `y`-constant lift `r ↦ (finSuccEquiv K 1).symm (C r)` of `r : K[x]` into
`MvPolynomial (Fin 2) K`. -/
noncomputable def yConst {K : Type*} [Field K] (r : MvPolynomial (Fin 1) K) :
    MvPolynomial (Fin 2) K :=
  (finSuccEquiv K 1).symm (Polynomial.C r)

/-- `lazardView (yConst r) = C r`. -/
@[simp] theorem lazardView_yConst {K : Type*} [Field K] (r : MvPolynomial (Fin 1) K) :
    lazardView (yConst r) = Polynomial.C r := by
  rw [lazardView, yConst, AlgEquiv.apply_symm_apply]

/-- The reduction step: with `leadingYCoeff fi1 * q = leadingYCoeff fi` and `degreeOf 0 fi <
degreeOf 0 fi1`, the element `yConst q · fi1 − y^{shift}·fi` has `y`-degree `< degreeOf 0 fi1` (the
matching top terms cancel). -/
theorem lazard_lemma3_reductionStep {K : Type*} [Field K] {fi fi1 : MvPolynomial (Fin 2) K}
    (hfi : fi ≠ 0) (hd : degreeOf 0 fi < degreeOf 0 fi1)
    {q : MvPolynomial (Fin 1) K} (hq : leadingYCoeff fi1 * q = leadingYCoeff fi) :
    degreeOf 0 (yConst q * fi1 - X 0 ^ (degreeOf 0 fi1 - degreeOf 0 fi) * fi)
      < degreeOf 0 fi1 := by
  set d := degreeOf 0 fi1 with hd_def
  set sh := degreeOf 0 fi1 - degreeOf 0 fi with hsh
  -- the two `K[x][y]`-views `p := C q · lazardView f_{i+1}` and `r := X^sh · lazardView fᵢ`.
  set p := Polynomial.C q * lazardView fi1 with hp_def
  set r := Polynomial.X ^ sh * lazardView fi with hr_def
  have hview : lazardView (yConst q * fi1 - X 0 ^ sh * fi) = p - r := by
    rw [lazardView, map_sub, map_mul, map_mul, map_pow, finSuccEquiv_X_zero, ← lazardView,
      ← lazardView, ← lazardView, lazardView_yConst, hp_def, hr_def]
  -- both have `natDegree ≤ d`.
  have hpdeg : p.natDegree ≤ d := by
    rw [hp_def]
    exact (Polynomial.natDegree_C_mul_le _ _).trans (by rw [natDegree_lazardView])
  have hrdeg : r.natDegree ≤ d := by
    rw [hr_def, Polynomial.natDegree_X_pow_mul sh (lazardView_eq_zero_iff.not.mpr hfi),
      natDegree_lazardView, hsh, Nat.add_sub_cancel' (le_of_lt hd)]
  -- their `d`-coefficients agree, both `= gᵢ`.
  have hpcoeff : p.coeff d = leadingYCoeff fi := by
    rw [hp_def, Polynomial.coeff_C_mul, hd_def, ← natDegree_lazardView, Polynomial.coeff_natDegree,
      ← leadingYCoeff, mul_comm, hq]
  have hrcoeff : r.coeff d = leadingYCoeff fi := by
    have hdeq : d = degreeOf 0 fi + sh := by rw [hd_def, hsh, Nat.add_sub_cancel' (le_of_lt hd)]
    rw [hr_def, hdeq, Polynomial.coeff_X_pow_mul, ← natDegree_lazardView, Polynomial.coeff_natDegree,
      ← leadingYCoeff]
  -- the difference's `d`-coefficient vanishes, so `natDegree < d` (`d > 0`).
  have hdiff0 : (p - r).coeff d = 0 := by rw [Polynomial.coeff_sub, hpcoeff, hrcoeff, sub_self]
  have hle : (p - r).natDegree ≤ d := (Polynomial.natDegree_sub_le p r).trans (max_le hpdeg hrdeg)
  have hdpos : 0 < d := lt_of_le_of_lt (Nat.zero_le _) hd
  rw [← natDegree_lazardView, hview]
  refine lt_of_le_of_ne hle (fun heq => ?_)
  rw [← heq, Polynomial.coeff_natDegree, Polynomial.leadingCoeff_eq_zero] at hdiff0
  rw [hdiff0, Polynomial.natDegree_zero] at heq
  exact hdpos.ne' heq.symm

/-- The reduction-step element `yConst q · fi1 − y^{shift}·fi` lies in `I` when `fi, fi1 ∈ I`. -/
theorem lazard_lemma3_reductionStep_mem {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {fi fi1 : MvPolynomial (Fin 2) K} (hfiI : fi ∈ I) (hfi1I : fi1 ∈ I)
    {q : MvPolynomial (Fin 1) K} :
    yConst q * fi1 - X 0 ^ (degreeOf 0 fi1 - degreeOf 0 fi) * fi ∈ I :=
  I.sub_mem (Ideal.mul_mem_left _ _ hfi1I) (Ideal.mul_mem_left _ _ hfiI)

/-- The `K[x][y]` view of the reduction step:
`lazardView (yConst q · fi1 − X 0 ^ sh · fi) = C q · lazardView fi1 − X^sh · lazardView fi`. -/
theorem lazardView_reductionStep {K : Type*} [Field K] (fi fi1 : MvPolynomial (Fin 2) K)
    (q : MvPolynomial (Fin 1) K) (sh : ℕ) :
    lazardView (yConst q * fi1 - X 0 ^ sh * fi)
      = Polynomial.C q * lazardView fi1 - Polynomial.X ^ sh * lazardView fi := by
  rw [lazardView, map_sub, map_mul, map_mul, map_pow, finSuccEquiv_X_zero, ← lazardView,
    ← lazardView, ← lazardView, lazardView_yConst]

/-- The reduction equation solved for `y^{shift}·fi`:
`X^sh·lazardView fi = C q · lazardView fi1 − lazardView (yConst q · fi1 − X 0 ^ sh · fi)`. -/
theorem lazardView_yShift_eq_reductionStep {K : Type*} [Field K]
    (fi fi1 : MvPolynomial (Fin 2) K) (q : MvPolynomial (Fin 1) K) (sh : ℕ) :
    Polynomial.X ^ sh * lazardView fi
      = Polynomial.C q * lazardView fi1 - lazardView (yConst q * fi1 - X 0 ^ sh * fi) := by
  rw [lazardView_reductionStep]; ring

/-- Over any commutative ring, `Polynomial.C d ∣ X^sh · p ⟹ Polynomial.C d ∣ p`. -/
theorem C_dvd_of_C_dvd_X_pow_mul {S : Type*} [CommRing S] {d : S} {p : Polynomial S} {sh : ℕ}
    (h : Polynomial.C d ∣ Polynomial.X ^ sh * p) : Polynomial.C d ∣ p := by
  rw [Polynomial.C_dvd_iff_dvd_coeff] at h ⊢
  intro i
  have := h (i + sh)
  rwa [Polynomial.coeff_X_pow_mul] at this

/-- If `C d ∣ C q · lazardView fi1` and `C d ∣ lazardView (yConst q · fi1 − X 0 ^ sh · fi)`, then
`C d ∣ lazardView fi`. -/
theorem C_dvd_lazardView_of_reductionStep_mul {K : Type*} [Field K]
    {fi fi1 : MvPolynomial (Fin 2) K} {q : MvPolynomial (Fin 1) K} {d : MvPolynomial (Fin 1) K}
    {sh : ℕ} (hfi1 : Polynomial.C d ∣ Polynomial.C q * lazardView fi1)
    (hR : Polynomial.C d ∣ lazardView (yConst q * fi1 - X 0 ^ sh * fi)) :
    Polynomial.C d ∣ lazardView fi := by
  refine C_dvd_of_C_dvd_X_pow_mul (sh := sh) ?_
  rw [lazardView_yShift_eq_reductionStep]
  exact dvd_sub hfi1 hR

/-- If `C d ∣ lazardView fi1` and `C d ∣ lazardView (yConst q · fi1 − X 0 ^ sh · fi)`, then
`C d ∣ lazardView fi`. -/
theorem C_dvd_lazardView_of_reductionStep {K : Type*} [Field K]
    {fi fi1 : MvPolynomial (Fin 2) K} {q : MvPolynomial (Fin 1) K} {d : MvPolynomial (Fin 1) K}
    {sh : ℕ} (hfi1 : Polynomial.C d ∣ lazardView fi1)
    (hR : Polynomial.C d ∣ lazardView (yConst q * fi1 - X 0 ^ sh * fi)) :
    Polynomial.C d ∣ lazardView fi :=
  C_dvd_lazardView_of_reductionStep_mul (Dvd.dvd.mul_left hfi1 _) hR

end DeepWiki.SymbolicIntegration
