import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.Data.Finsupp.MonomialOrder
import DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner.ReducedBasis
import DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner.BivariateView
import DeepWiki.Algebra.OneVariableGcd

/-! # Leading y-coefficient gcds

The gcd construction for leading y-coefficients in a reduced bivariate Gröbner
basis over lex order, culminating in Lazard's divisibility lemma. -/

open MvPolynomial MonomialOrder

namespace DeepWiki.SymbolicIntegration

variable {σ : Type*} {m : MonomialOrder σ}

/-! ## The leading-`y`-coefficient gcd construction

Along a minimal bivariate Gröbner basis sorted by increasing `y`-degree, the higher
`R_{i+1} = leadingYCoeff f_{i+1}` divides the lower `Rᵢ = leadingYCoeff fᵢ`. The algebraic core is a
Bézout combination producing `P ∈ I` of `y`-degree `d_{i+1}` with `leadingYCoeff P = gcd(Rᵢ,
R_{i+1})`, plus the `x`-degree bridge under lex. -/

/-- If `p, q : S[Y]` have `natDegree ≤ d` and `p.coeff d + q.coeff d ≠ 0`, then `p + q` has
`natDegree = d` and `leadingCoeff (p + q) = p.coeff d + q.coeff d`. -/
theorem natDegree_leadingCoeff_add {S : Type*} [CommRing S] {p q : Polynomial S} {d : ℕ}
    (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d) (hne : p.coeff d + q.coeff d ≠ 0) :
    (p + q).natDegree = d ∧ (p + q).leadingCoeff = p.coeff d + q.coeff d := by
  have hcoeff : (p + q).coeff d = p.coeff d + q.coeff d := Polynomial.coeff_add p q d
  have hdle : (p + q).natDegree ≤ d := (Polynomial.natDegree_add_le p q).trans (max_le hp hq)
  have hdeg : (p + q).natDegree = d := by
    refine le_antisymm hdle ?_
    by_contra hlt
    rw [not_le] at hlt
    exact hne (by rw [← hcoeff]; exact Polynomial.coeff_eq_zero_of_natDegree_lt hlt)
  exact ⟨hdeg, by rw [Polynomial.leadingCoeff, hdeg, hcoeff]⟩

/-- Every nonzero `f ∈ I` has its leading monomial dominated by that of some nonzero basis element:
`∃ b ∈ B, b ≠ 0 ∧ m.degree b ≤ m.degree f`. -/
theorem IsGroebnerBasis.exists_degree_le {K : Type*} [Field K]
    {I : Ideal (MvPolynomial σ K)} {B : Set (MvPolynomial σ K)} (hB : IsGroebnerBasis m I B)
    {f : MvPolynomial σ K} (hfI : f ∈ I) (hf0 : f ≠ 0) :
    ∃ b ∈ B, b ≠ 0 ∧ m.degree b ≤ m.degree f := by
  classical
  obtain ⟨_, hlc, hinit⟩ := hB
  have hgen : monomial (m.degree f) (1 : K) ∈ initialIdeal m I :=
    Ideal.subset_span ⟨f, ⟨hfI, hf0⟩, rfl⟩
  rw [← hinit] at hgen
  have himg : (fun b => monomial (m.degree b) (1 : K)) '' B
      = (fun s => monomial s (1 : K)) '' (m.degree '' B) := by rw [Set.image_image]
  rw [himg, mem_ideal_span_monomial_image] at hgen
  obtain ⟨_, ⟨b, hbB, hb⟩, hsi⟩ := hgen (m.degree f) (by
    rw [mem_support_iff, coeff_monomial, if_pos rfl]; exact one_ne_zero)
  rw [← hb] at hsi
  refine ⟨b, hbB, ?_, hsi⟩
  intro hb0
  exact (hlc b hbB).ne_zero (by rw [hb0, MonomialOrder.leadingCoeff, degree_zero, coeff_zero])

open scoped Classical in
/-- The gcd construction: for ideal members `fi, fi1` with `degreeOf 0 fi ≤ degreeOf 0 fi1`, there
is `P ∈ I` of `y`-degree `degreeOf 0 fi1` with `leadingYCoeff P = gcd(leadingYCoeff fi,
leadingYCoeff fi1)`. -/
theorem lazard_gcd_construction {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {fi fi1 : MvPolynomial (Fin 2) K} (hfiI : fi ∈ I) (hfi1I : fi1 ∈ I)
    (hfi : fi ≠ 0) (hd : degreeOf 0 fi ≤ degreeOf 0 fi1) :
    ∃ P ∈ I, degreeOf 0 P = degreeOf 0 fi1 ∧
      leadingYCoeff P = @gcd _ _ (gcdMonoidMvPolynomialFinOne K)
        (leadingYCoeff fi) (leadingYCoeff fi1) := by
  letI := gcdMonoidMvPolynomialFinOne K
  set gi := leadingYCoeff fi with hgi
  set gi1 := leadingYCoeff fi1 with hgi1
  set k := degreeOf 0 fi1 - degreeOf 0 fi with hk
  obtain ⟨a, b, hab⟩ := exists_mul_add_mul_eq_gcd gi gi1
  set fs := X 0 ^ k * fi with hfs
  have hfsI : fs ∈ I := Ideal.mul_mem_left _ _ hfiI
  have hfsdeg : degreeOf 0 fs = degreeOf 0 fi1 := by
    rw [hfs, degreeOf_X_pow_mul _ hfi, hk, Nat.add_sub_cancel' hd]
  have hfslc : leadingYCoeff fs = gi := by rw [hfs, leadingYCoeff_X_pow_mul]
  -- lift the `K[x]`-Bézout coefficients `a, b` to `y`-constants `ã, b̃`.
  set atil := (finSuccEquiv K 1).symm (Polynomial.C a) with hatil
  set btil := (finSuccEquiv K 1).symm (Polynomial.C b) with hbtil
  set P := atil * fs + btil * fi1 with hP
  have hPI : P ∈ I := I.add_mem (Ideal.mul_mem_left _ _ hfsI) (Ideal.mul_mem_left _ _ hfi1I)
  have hlazP : lazardView P = Polynomial.C a * lazardView fs + Polynomial.C b * lazardView fi1 := by
    rw [hP, hatil, hbtil]
    simp only [lazardView, map_add, map_mul, AlgEquiv.apply_symm_apply]
  -- `gcd(gᵢ, g_{i+1}) ≠ 0` (since `gᵢ ≠ 0`).
  have hgcd_ne : @gcd _ _ (gcdMonoidMvPolynomialFinOne K) gi gi1 ≠ 0 := by
    rw [Ne, gcd_eq_zero_iff, not_and_or]
    exact Or.inl (by rw [hgi]; exact leadingYCoeff_ne_zero.mpr hfi)
  -- the two `y`-degree-`d` summands `p := C a · (lazardView fs)`, `q := C b · (lazardView f_{i+1})`.
  set d := degreeOf 0 fi1 with hd_def
  set p := Polynomial.C a * lazardView fs with hp_def
  set q := Polynomial.C b * lazardView fi1 with hq_def
  have hpdeg : p.natDegree ≤ d := by
    rw [hp_def]
    exact (Polynomial.natDegree_C_mul_le _ _).trans (by rw [natDegree_lazardView, hfsdeg])
  have hqdeg : q.natDegree ≤ d := by
    rw [hq_def]
    exact (Polynomial.natDegree_C_mul_le _ _).trans (by rw [natDegree_lazardView])
  -- their `d`-coefficients are `a·gᵢ` and `b·g_{i+1}`.
  have hpcoeff : p.coeff d = a * gi := by
    rw [hp_def, Polynomial.coeff_C_mul]
    refine congrArg (fun r : MvPolynomial (Fin 1) K => a * r) ?_
    rw [← hfsdeg, ← natDegree_lazardView, Polynomial.coeff_natDegree, ← hfslc]; rfl
  have hqcoeff : q.coeff d = b * gi1 := by
    rw [hq_def, Polynomial.coeff_C_mul]
    refine congrArg (fun r : MvPolynomial (Fin 1) K => b * r) ?_
    rw [hd_def, ← natDegree_lazardView, Polynomial.coeff_natDegree]; rfl
  have hsum_ne : p.coeff d + q.coeff d ≠ 0 := by rw [hpcoeff, hqcoeff, hab]; exact hgcd_ne
  obtain ⟨hPdeg, hPlc⟩ := natDegree_leadingCoeff_add hpdeg hqdeg hsum_ne
  rw [← hlazP] at hPdeg hPlc
  exact ⟨P, hPI, by rw [← natDegree_lazardView, hPdeg],
    by rw [leadingYCoeff, hPlc, hpcoeff, hqcoeff, hab]⟩

/-- Along a reduced bivariate Gröbner basis over `lex`, the higher-`y`-degree
`leadingYCoeff fi1` divides the lower `leadingYCoeff fi` (`degreeOf 0 fi < degreeOf 0 fi1`). -/
theorem lazard_lemma2 {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    {fi fi1 : MvPolynomial (Fin 2) K} (hfi : fi ∈ B) (hfi1 : fi1 ∈ B)
    (hd : degreeOf 0 fi < degreeOf 0 fi1) :
    leadingYCoeff fi1 ∣ leadingYCoeff fi := by
  letI := gcdMonoidMvPolynomialFinOne K
  set m := MonomialOrder.lex (σ := Fin 2)
  have hfi0 : fi ≠ 0 := hB.ne_zero hfi
  have hfi10 : fi1 ≠ 0 := hB.ne_zero hfi1
  set gi := leadingYCoeff fi with hgi
  set gi1 := leadingYCoeff fi1 with hgi1
  set g := @gcd _ _ (gcdMonoidMvPolynomialFinOne K) gi gi1 with hg
  have hg_gi : g ∣ gi := gcd_dvd_left_mvPolynomialFinOne gi gi1
  have hg_gi1 : g ∣ gi1 := gcd_dvd_right_mvPolynomialFinOne gi gi1
  obtain ⟨P, hPI, hPdeg, hPlc⟩ :=
    lazard_gcd_construction (hB.isGroebnerBasis.1 fi hfi) (hB.isGroebnerBasis.1 fi1 hfi1)
      hfi0 (le_of_lt hd)
  rw [← hgi, ← hgi1, ← hg] at hPlc
  have hg_ne : g ≠ 0 := by
    rw [hg, Ne, gcd_eq_zero_iff, not_and_or]
    exact Or.inl (by rw [hgi]; exact leadingYCoeff_ne_zero.mpr hfi0)
  have hP0 : P ≠ 0 := leadingYCoeff_ne_zero.mp (by rw [hPlc]; exact hg_ne)
  -- It suffices to show `R_{i+1} ∣ gcd` (then `R_{i+1} ∣ gcd ∣ Rᵢ`).
  suffices hgi1g : gi1 ∣ g by exact hgi1g.trans hg_gi
  refine dvd_of_dvd_of_degreeOf_le hg_gi1 (by rw [hgi1]; exact leadingYCoeff_ne_zero.mpr hfi10) ?_
  -- the leading monomials: `m.degree P = (d_{i+1}, deg_x gcd)`, `m.degree f_{i+1} = (d_{i+1}, deg_x R_{i+1})`.
  have hPdeg0 : (m.degree P) 0 = degreeOf 0 fi1 := by rw [lex_degree_apply_zero hP0, hPdeg]
  have hPdeg1 : (m.degree P) 1 = degreeOf 0 g := by rw [lex_degree_apply_one hP0, hPlc]
  have hfi1deg0 : (m.degree fi1) 0 = degreeOf 0 fi1 := lex_degree_apply_zero hfi10
  have hfi1deg1 : (m.degree fi1) 1 = degreeOf 0 gi1 := lex_degree_apply_one hfi10
  have hgdeg_le : degreeOf 0 g ≤ degreeOf 0 gi1 :=
    degreeOf_le_of_dvd hg_gi1 (by rw [hgi1]; exact leadingYCoeff_ne_zero.mpr hfi10)
  obtain ⟨b, hbB, _, hble⟩ := hB.isGroebnerBasis.exists_degree_le hPI hP0
  -- `b = f_{i+1}`: else `m.degree b ≤ m.degree f_{i+1}` (both coords), contradicting minimality.
  have hbfi1 : b = fi1 := by
    by_contra hne
    have hb0' : (m.degree b) 0 ≤ (m.degree fi1) 0 := by
      have := (Finsupp.le_def.mp hble) 0
      rw [hfi1deg0, ← hPdeg0]; exact this
    have hb1' : (m.degree b) 1 ≤ (m.degree fi1) 1 := by
      have hbP := (Finsupp.le_def.mp hble) 1
      rw [hPdeg1] at hbP
      rw [hfi1deg1]; exact hbP.trans hgdeg_le
    have hble_fi1 : m.degree b ≤ m.degree fi1 := by
      rw [Finsupp.le_def]; intro i; fin_cases i
      · exact hb0'
      · exact hb1'
    exact hB.leadingMonomial_not_le (Finset.mem_coe.mpr hfi1) (Finset.mem_coe.mpr hbB)
      (fun h => hne h.symm) hble_fi1
  -- with `b = f_{i+1}`: `m.degree f_{i+1} ≤ m.degree P`, so `deg_x R_{i+1} ≤ deg_x gcd`.
  rw [hbfi1] at hble
  have hfin := (Finsupp.le_def.mp hble) 1
  rw [hfi1deg1, hPdeg1] at hfin
  exact hfin

-- Restatements against the intended wording.
example {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    {fi fi1 : MvPolynomial (Fin 2) K} (hfi : fi ∈ B) (hfi1 : fi1 ∈ B)
    (hd : degreeOf 0 fi < degreeOf 0 fi1) :
    leadingYCoeff fi1 ∣ leadingYCoeff fi :=
  lazard_lemma2 hB hfi hfi1 hd

end DeepWiki.SymbolicIntegration
