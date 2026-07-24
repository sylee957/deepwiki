import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Data.Finsupp.MonomialOrder
import DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner.ReducedBasis

/-! # Bivariate Gröbner views

Bivariate Gröbner-basis helpers for the `MvPolynomial (Fin 2) K` view as
`K[x][y]`, including leading y-degrees, leading y-coefficients, and y-shifts. -/

open MvPolynomial MonomialOrder

namespace DeepWiki.SymbolicIntegration

variable {σ : Type*} {m : MonomialOrder σ} {R : Type*} [CommRing R]
variable {I : Ideal (MvPolynomial σ R)} {B : Set (MvPolynomial σ R)}

/-! ## Distinct leading y-degrees in a minimal bivariate Gröbner basis

Over `MvPolynomial (Fin 2) K` the leading y-degree of `b` is `(m.degree b) 1`; distinct elements of
a reduced Gröbner basis have distinct leading y-degrees. -/

/-- In `Fin 2 →₀ ℕ`, two exponent vectors agreeing at index `1` are comparable. -/
theorem finsupp_fin_two_le_or_le_of_apply_eq {d d' : Fin 2 →₀ ℕ} (h : d 1 = d' 1) :
    d ≤ d' ∨ d' ≤ d := by
  rcases le_total (d 0) (d' 0) with h0 | h0
  · refine Or.inl ?_
    rw [Finsupp.le_def]
    intro i
    fin_cases i
    · exact h0
    · exact h.le
  · refine Or.inr ?_
    rw [Finsupp.le_def]
    intro i
    fin_cases i
    · exact h0
    · exact h.ge

/-- A reduced Gröbner basis element is nonzero: its leading coefficient is `1 ≠ 0`. -/
theorem IsReducedGroebnerBasis.ne_zero {K : Type*} [Field K] {I : Ideal (MvPolynomial σ K)}
    {B : Set (MvPolynomial σ K)} (hB : IsReducedGroebnerBasis m I B) {b : MvPolynomial σ K}
    (hb : b ∈ B) : b ≠ 0 :=
  m.leadingCoeff_ne_zero_iff.mp (by rw [hB.2.1 b hb]; exact one_ne_zero)

/-- In a reduced Gröbner basis, the leading monomial of `b'` does not divide that of a distinct
`b`. -/
theorem IsReducedGroebnerBasis.leadingMonomial_not_le {K : Type*} [Field K]
    {I : Ideal (MvPolynomial σ K)} {B : Set (MvPolynomial σ K)}
    (hB : IsReducedGroebnerBasis m I B) {b b' : MvPolynomial σ K} (hb : b ∈ B) (hb' : b' ∈ B)
    (hne : b ≠ b') : ¬ (m.degree b' ≤ m.degree b) :=
  hB.2.2 b hb b' hb' hne (m.degree b) (degree_mem_support (hB.ne_zero hb))

/-- In a reduced Gröbner basis `B` of a two-variable ideal, distinct elements have distinct leading
y-degrees `(m.degree ·) 1`. -/
theorem distinct_leadingYDegree_of_isReducedGroebnerBasis {K : Type*} [Field K] {m : MonomialOrder (Fin 2)}
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis m I (↑B : Set (MvPolynomial (Fin 2) K))) :
    ∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → (m.degree b) 1 ≠ (m.degree b') 1 := by
  intro b hb b' hb' hne hy
  rcases finsupp_fin_two_le_or_le_of_apply_eq hy with hle | hle
  · exact hB.leadingMonomial_not_le (Finset.mem_coe.mpr hb') (Finset.mem_coe.mpr hb)
      (Ne.symm hne) hle
  · exact hB.leadingMonomial_not_le (Finset.mem_coe.mpr hb) (Finset.mem_coe.mpr hb') hne hle

/-- The leading-y-degree map `b ↦ (m.degree b) 1` is injective on a reduced Gröbner basis of a
two-variable ideal. -/
theorem injOn_leadingYDegree_of_isReducedGroebnerBasis {K : Type*} [Field K] {m : MonomialOrder (Fin 2)}
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis m I (↑B : Set (MvPolynomial (Fin 2) K))) :
    Set.InjOn (fun b => (m.degree b) 1) (↑B : Set (MvPolynomial (Fin 2) K)) := by
  intro b hb b' hb' hyeq
  by_contra hne
  exact distinct_leadingYDegree_of_isReducedGroebnerBasis hB b hb b' hb' hne hyeq

/-! ## The `MvPolynomial (Fin 2) K ↔ K[x][y]` representation bridge

Views a bivariate `f : MvPolynomial (Fin 2) K` as a univariate polynomial in `y` with coefficients
in `K[x]` via `finSuccEquiv K 1`, under the convention `y = variable 0`, `x = variable 1`. The
`y`-degree is the dominant coordinate of the monomial order, packaged as a hypothesis `hdom` and
proved for `MonomialOrder.lex`. -/

/-- For lex on `Fin 2`, `toLex s ≤ toLex t → s 0 ≤ t 0` (index `0` is most significant). -/
theorem apply_zero_le_of_toLex_le {s t : Fin 2 →₀ ℕ} (h : toLex s ≤ toLex t) : s 0 ≤ t 0 := by
  rcases h.lt_or_eq with hlt | heq
  · obtain ⟨i, hbelow, hi⟩ := Finsupp.Lex.lt_iff.mp hlt
    fin_cases i
    · exact hi.le
    · exact (hbelow 0 (by decide)).le
  · exact (congrArg (fun u => (ofLex u) 0) heq).le

/-- For lex on `Fin 2`, `toLex s ≤ toLex t → s 0 = t 0 → s 1 ≤ t 1` (tie at index `0` broken at
index `1`). -/
theorem apply_one_le_of_toLex_le_of_apply_zero_eq {s t : Fin 2 →₀ ℕ}
    (h : toLex s ≤ toLex t) (h0 : s 0 = t 0) : s 1 ≤ t 1 := by
  rcases h.lt_or_eq with hlt | heq
  · obtain ⟨i, _, hi⟩ := Finsupp.Lex.lt_iff.mp hlt
    fin_cases i
    · exact absurd h0 (ne_of_lt hi)
    · exact hi.le
  · exact (congrArg (fun u => (ofLex u) 1) heq).le

/-- Under `MonomialOrder.lex` on `Fin 2` with `f ≠ 0`, the index-`0` exponent of the leading
monomial equals the `y`-degree `degreeOf 0 f`. -/
theorem lex_degree_apply_zero {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K} (hf : f ≠ 0) :
    (MonomialOrder.lex.degree f) 0 = degreeOf 0 f := by
  apply le_antisymm
  · exact monomial_le_degreeOf 0 (MonomialOrder.degree_mem_support hf)
  · rw [degreeOf_le_iff]
    intro s hs
    have hle : s ≼[MonomialOrder.lex] MonomialOrder.lex.degree f :=
      MonomialOrder.le_degree hs
    rw [MonomialOrder.lex_le_iff] at hle
    exact apply_zero_le_of_toLex_le hle

/-- Under lex, an order bound on leading monomials gives a bound on `y`-degrees. -/
theorem degreeOf_le_of_lex_degree_le {K : Type*} [Field K] {bg R : MvPolynomial (Fin 2) K}
    (hbg : bg ≠ 0) (hR : R ≠ 0)
    (hle : MonomialOrder.lex.degree bg ≼[MonomialOrder.lex] MonomialOrder.lex.degree R) :
    degreeOf 0 bg ≤ degreeOf 0 R := by
  rw [MonomialOrder.lex_le_iff] at hle
  have := apply_zero_le_of_toLex_le hle
  rwa [lex_degree_apply_zero hbg, lex_degree_apply_zero hR] at this

/-- The `K[x][y]` view of a bivariate polynomial (`y = variable 0`): `finSuccEquiv K 1 f`. -/
noncomputable def lazardView {K : Type*} [Field K] (f : MvPolynomial (Fin 2) K) :
    Polynomial (MvPolynomial (Fin 1) K) :=
  finSuccEquiv K 1 f

/-- The leading-`y`-coefficient of `f`: the `K[x]`-coefficient of its top `y`-power,
`(lazardView f).leadingCoeff`. -/
noncomputable def leadingYCoeff {K : Type*} [Field K] (f : MvPolynomial (Fin 2) K) :
    MvPolynomial (Fin 1) K :=
  (lazardView f).leadingCoeff

/-- `lazardView` is injective (it is the bijection `finSuccEquiv`). -/
theorem lazardView_injective {K : Type*} [Field K] :
    Function.Injective (lazardView (K := K)) :=
  (finSuccEquiv K 1).injective

/-- `lazardView f = 0 ↔ f = 0`. -/
@[simp] theorem lazardView_eq_zero_iff {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K} :
    lazardView f = 0 ↔ f = 0 := by
  rw [lazardView, map_eq_zero_iff _ (finSuccEquiv K 1).injective]

/-- The `natDegree` of the `K[x][y]` view is the `y`-degree `degreeOf 0 f`. -/
theorem natDegree_lazardView {K : Type*} [Field K] (f : MvPolynomial (Fin 2) K) :
    (lazardView f).natDegree = degreeOf 0 f :=
  natDegree_finSuccEquiv f

/-- A `y`-degree-`0` polynomial has `lazardView` divisible by its constant leading coefficient. -/
theorem C_dvd_lazardView_of_degreeOf_zero {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    (hf0 : degreeOf 0 f = 0) :
    Polynomial.C (leadingYCoeff f) ∣ lazardView f := by
  have hdeg : (lazardView f).natDegree = 0 := by rw [natDegree_lazardView, hf0]
  have hC : lazardView f = Polynomial.C ((lazardView f).coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero hdeg
  have hlc : leadingYCoeff f = (lazardView f).coeff 0 := by
    rw [leadingYCoeff, Polynomial.leadingCoeff, hdeg]
  rw [hlc, ← hC]

/-- **Divisibility propagates through a `K[x][y]` combination**. If `P ∣ lazardView b` for every
`b` in the support of a finite combination `R = ∑ b ∈ s, h b · b`, then `P ∣ lazardView R`. -/
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

/-- Under a dominant order (`hdom`), the index-`0` component of `m.degree f` is the `K[x][y]`
`natDegree` of `f`. -/
theorem degree_apply_zero_eq_natDegree_lazardView {K : Type*} [Field K] {m : MonomialOrder (Fin 2)}
    (hdom : ∀ f : MvPolynomial (Fin 2) K, f ≠ 0 → (m.degree f) 0 = degreeOf 0 f)
    {f : MvPolynomial (Fin 2) K} (hf : f ≠ 0) :
    (m.degree f) 0 = (lazardView f).natDegree := by
  rw [hdom f hf, natDegree_lazardView]

/-- `leadingYCoeff f ≠ 0 ↔ f ≠ 0`. -/
@[simp] theorem leadingYCoeff_ne_zero {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K} :
    leadingYCoeff f ≠ 0 ↔ f ≠ 0 := by
  rw [ne_eq, ne_eq, leadingYCoeff, Polynomial.leadingCoeff_eq_zero, lazardView_eq_zero_iff]

/-- `leadingYCoeff f = 0 ↔ f = 0`. -/
@[simp] theorem leadingYCoeff_eq_zero {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K} :
    leadingYCoeff f = 0 ↔ f = 0 := by
  rw [leadingYCoeff, Polynomial.leadingCoeff_eq_zero, lazardView_eq_zero_iff]

/-- `leadingYCoeff (f * g) = leadingYCoeff f * leadingYCoeff g`. -/
theorem leadingYCoeff_mul {K : Type*} [Field K] (f g : MvPolynomial (Fin 2) K) :
    leadingYCoeff (f * g) = leadingYCoeff f * leadingYCoeff g := by
  rw [leadingYCoeff, leadingYCoeff, leadingYCoeff, lazardView, lazardView, lazardView, map_mul,
    Polynomial.leadingCoeff_mul]

/-- A factor's `y`-degree is dominated by the product's `y`-degree. -/
theorem degreeOf_le_degreeOf_mul {K : Type*} [Field K] {g b : MvPolynomial (Fin 2) K}
    (hne : g * b ≠ 0) : degreeOf 0 b ≤ degreeOf 0 (g * b) := by
  have hg : g ≠ 0 := fun h0 => hne (by rw [h0, zero_mul])
  have hb : b ≠ 0 := fun h0 => hne (by rw [h0, mul_zero])
  rw [← natDegree_lazardView, ← natDegree_lazardView, lazardView, lazardView, map_mul,
    Polynomial.natDegree_mul (by rwa [← lazardView, Ne, lazardView_eq_zero_iff])
      (by rwa [← lazardView, Ne, lazardView_eq_zero_iff])]
  exact Nat.le_add_left _ _

/-- Under lex, the index-`1` exponent of the leading monomial is the `x`-degree of
`leadingYCoeff f`. -/
theorem lex_degree_apply_one {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K} (hf : f ≠ 0) :
    (MonomialOrder.lex.degree f) 1 = degreeOf 0 (leadingYCoeff f) := by
  classical
  set δ := MonomialOrder.lex.degree f with hδ
  have hδ0 : δ 0 = degreeOf 0 f := lex_degree_apply_zero hf
  have hlyc : leadingYCoeff f = (lazardView f).coeff (degreeOf 0 f) := by
    rw [leadingYCoeff, Polynomial.leadingCoeff, natDegree_lazardView]
  have hsucc : (1 : Fin 2) = (0 : Fin 1).succ := rfl
  apply le_antisymm
  · have hδmem : δ ∈ f.support := MonomialOrder.degree_mem_support hf
    set mon' : Fin 1 →₀ ℕ := Finsupp.tail δ with hmon'
    have hcons : Finsupp.cons (δ 0) mon' = δ := by rw [hmon', Finsupp.cons_tail]
    have hmem' : mon' ∈ (leadingYCoeff f).support := by
      rw [hlyc, lazardView, mem_support_coeff_finSuccEquiv, ← hδ0, hcons]
      exact hδmem
    have hval : mon' 0 = δ 1 := by rw [hmon', Finsupp.tail_apply, hsucc]
    rw [← hval, degreeOf_eq_sup]
    exact Finset.le_sup (f := fun s : Fin 1 →₀ ℕ => s 0) hmem'
  · rw [degreeOf_eq_sup]
    apply Finset.sup_le
    intro mon hmon
    rw [hlyc, lazardView, mem_support_coeff_finSuccEquiv, ← hδ0] at hmon
    have hle : (Finsupp.cons (δ 0) mon) ≼[MonomialOrder.lex] δ :=
      MonomialOrder.le_degree hmon
    rw [MonomialOrder.lex_le_iff] at hle
    have h0eq : (Finsupp.cons (δ 0) mon) 0 = δ 0 := Finsupp.cons_zero _ _
    have hmain := apply_one_le_of_toLex_le_of_apply_zero_eq hle h0eq
    have hcons1 : (Finsupp.cons (δ 0) mon) 1 = mon 0 := by rw [hsucc, Finsupp.cons_succ]
    rwa [hcons1] at hmain

/-! ## The `y`-shift toolbox

The `y`-shift `f ↦ y^k·f` aligns `y`-degrees: under the `K[x][y]` view it multiplies `lazardView`
by `Polynomial.X ^ k`, adding `k` to the `y`-degree and leaving the leading-`y`-coefficient
unchanged. -/

/-- The `K[x][y]` view of a `y`-shift: `lazardView (X 0 ^ k * f) = Polynomial.X ^ k * lazardView f`
(`finSuccEquiv (X 0) = Polynomial.X`). -/
theorem lazardView_X_pow_mul {K : Type*} [Field K] (k : ℕ) (f : MvPolynomial (Fin 2) K) :
    lazardView (X 0 ^ k * f) = Polynomial.X ^ k * lazardView f := by
  rw [lazardView, lazardView, map_mul, map_pow, finSuccEquiv_X_zero]

/-- `degreeOf 0 (X 0 ^ k * f) = degreeOf 0 f + k` for `f ≠ 0`: the `y`-shift adds `k` to the
`y`-degree. -/
theorem degreeOf_X_pow_mul {K : Type*} [Field K] (k : ℕ) {f : MvPolynomial (Fin 2) K} (hf : f ≠ 0) :
    degreeOf 0 (X 0 ^ k * f) = degreeOf 0 f + k := by
  have hne : lazardView f ≠ 0 := lazardView_eq_zero_iff.not.mpr hf
  rw [← natDegree_lazardView, ← natDegree_lazardView, lazardView_X_pow_mul,
    Polynomial.natDegree_X_pow_mul k hne]

/-- `leadingYCoeff (X 0 ^ k * f) = leadingYCoeff f`: the `y`-shift fixes the leading-`y`-coefficient. -/
theorem leadingYCoeff_X_pow_mul {K : Type*} [Field K] (k : ℕ) (f : MvPolynomial (Fin 2) K) :
    leadingYCoeff (X 0 ^ k * f) = leadingYCoeff f := by
  rw [leadingYCoeff, leadingYCoeff, lazardView_X_pow_mul, mul_comm, Polynomial.leadingCoeff_mul_X_pow]

/-- If `fi ≠ 0` and `degreeOf 0 fi ≤ degreeOf 0 fi1`, the `y`-shifted `y^{d₁−d₀}·fi` matches the
`y`-degree of `fi1` while keeping the leading-`y`-coefficient of `fi`. -/
theorem leadingYCoeff_yShift_eq {K : Type*} [Field K] {fi fi1 : MvPolynomial (Fin 2) K}
    (hfi : fi ≠ 0) (hd : degreeOf 0 fi ≤ degreeOf 0 fi1) :
    degreeOf 0 (X 0 ^ (degreeOf 0 fi1 - degreeOf 0 fi) * fi) = degreeOf 0 fi1 ∧
      leadingYCoeff (X 0 ^ (degreeOf 0 fi1 - degreeOf 0 fi) * fi) = leadingYCoeff fi :=
  ⟨by rw [degreeOf_X_pow_mul _ hfi, Nat.add_sub_cancel' hd],
    leadingYCoeff_X_pow_mul _ fi⟩

end DeepWiki.SymbolicIntegration
