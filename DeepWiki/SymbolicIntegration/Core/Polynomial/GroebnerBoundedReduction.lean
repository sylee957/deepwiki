import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.MvPolynomial.Ideal
import DeepWiki.SymbolicIntegration.Core.Polynomial.GroebnerReducedBasis
import DeepWiki.SymbolicIntegration.Core.Polynomial.GroebnerBivariateView
import DeepWiki.SymbolicIntegration.Core.Polynomial.GroebnerLeadingYCoeffGcd
import DeepWiki.SymbolicIntegration.Core.Polynomial.GroebnerBivariateSorting
import DeepWiki.SymbolicIntegration.Core.Polynomial.GroebnerReductionStep

/-! # Bounded reductions for bivariate Gröbner bases

Lexicographic Gröbner reduction of a bivariate ideal member can be represented using
only basis elements with bounded `y`-degree, and divisibility hypotheses propagate
through such bounded representations. -/

open MvPolynomial MonomialOrder

namespace DeepWiki.SymbolicIntegration

variable {σ : Type*} {m : MonomialOrder σ}

/-- **Divisibility propagates through a `K[x][y]` combination** (Part B core, IH-aggregation half).
If `C d ∣ lazardView b` for every `b` in the support of a finite combination `R = ∑ b ∈ s, h b · b`,
then `C d ∣ lazardView R` — `lazardView` is a ring hom, so the divisor of every factor divides the
sum. This is the step that turns the per-element induction hypothesis `gᵢ ∣ f_j` into `gᵢ ∣ R`. -/
theorem C_dvd_lazardView_sum {K : Type*} [Field K] {d : MvPolynomial (Fin 1) K}
    {s : Finset (MvPolynomial (Fin 2) K)} {h : MvPolynomial (Fin 2) K → MvPolynomial (Fin 2) K}
    (hdvd : ∀ b ∈ s, Polynomial.C d ∣ lazardView b) :
    Polynomial.C d ∣ lazardView (∑ b ∈ s, h b * b) := by
  rw [lazardView, map_sum]
  refine Finset.dvd_sum (fun b hb => ?_)
  rw [map_mul]
  exact Dvd.dvd.mul_left ((hdvd b hb)) _

/-- **Leading-`y`-coefficient divisibility along the sorted basis** (Lemma 2, one step on the
enumeration): for `i < j`, the higher-`y`-degree `leadingYCoeff (sortedByYDegree hB j)` divides the
lower one `leadingYCoeff (sortedByYDegree hB i)` (`lazard_lemma2` at the strictly increasing
`y`-degrees `degreeOf 0`). -/
theorem leadingYCoeff_sortedByYDegree_dvd_of_lt {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    {i j : Fin B.card} (hij : i < j) :
    leadingYCoeff (sortedByYDegree hB j) ∣ leadingYCoeff (sortedByYDegree hB i) :=
  lazard_lemma2 hB (sortedByYDegree_mem hB i) (sortedByYDegree_mem hB j)
    (degreeOf_sortedByYDegree_strictMono hB hij)

/-- **Leading-`y`-coefficient divisibility chain** (`≤` form): for `i ≤ j` along the sorted basis,
`leadingYCoeff (sortedByYDegree hB j) ∣ leadingYCoeff (sortedByYDegree hB i)` — the higher
`y`-degree's `gⱼ` divides every lower `gᵢ` (one-step `leadingYCoeff_sortedByYDegree_dvd_of_lt`, plus
reflexivity). This is the chain the descent uses to push `gᵢ ∣ g_j` onto the lower combination. -/
theorem leadingYCoeff_sortedByYDegree_dvd_of_le {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    {i j : Fin B.card} (hij : i ≤ j) :
    leadingYCoeff (sortedByYDegree hB j) ∣ leadingYCoeff (sortedByYDegree hB i) := by
  rcases lt_or_eq_of_le hij with h | h
  · exact leadingYCoeff_sortedByYDegree_dvd_of_lt hB h
  · rw [h]

/-- **Lazard's Lemma 3, the base case** (Lazard 1985, p.263, "`f₀ ∈ K[x]`"). A `y`-degree-`0` element
has `lazardView f = C (leadingYCoeff f)` (a constant in `K[x][y]`), so trivially `gᵢ ∣ fᵢ` in the form
`C (leadingYCoeff f) ∣ lazardView f`. This is the bottom of the descent. -/
theorem C_dvd_lazardView_of_degreeOf_zero {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    (hf0 : degreeOf 0 f = 0) :
    Polynomial.C (leadingYCoeff f) ∣ lazardView f := by
  have hdeg : (lazardView f).natDegree = 0 := by rw [natDegree_lazardView, hf0]
  have hC : lazardView f = Polynomial.C ((lazardView f).coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero hdeg
  have hlc : leadingYCoeff f = (lazardView f).coeff 0 := by
    rw [leadingYCoeff, Polynomial.leadingCoeff, hdeg]
  rw [hlc, ← hC]

/-- **A factor's `y`-degree is dominated by the product's**: `degreeOf 0 b ≤ degreeOf 0 (g * b)` for
`g * b ≠ 0` (`natDegree` of the `K[x][y]` product adds, both factors nonzero). -/
theorem degreeOf_le_degreeOf_mul {K : Type*} [Field K] {g b : MvPolynomial (Fin 2) K}
    (hne : g * b ≠ 0) : degreeOf 0 b ≤ degreeOf 0 (g * b) := by
  have hg : g ≠ 0 := fun h0 => hne (by rw [h0, zero_mul])
  have hb : b ≠ 0 := fun h0 => hne (by rw [h0, mul_zero])
  rw [← natDegree_lazardView, ← natDegree_lazardView, lazardView, lazardView, map_mul,
    Polynomial.natDegree_mul (by rwa [← lazardView, Ne, lazardView_eq_zero_iff])
      (by rwa [← lazardView, Ne, lazardView_eq_zero_iff])]
  exact Nat.le_add_left _ _

/-- **Under lex, the division-algorithm degree bound becomes a `y`-degree bound**: from
`m.degree bg ≼[lex] m.degree R` (a `div_set` summand bound) with `bg, R ≠ 0`, the `y`-degree
`degreeOf 0 bg ≤ degreeOf 0 R`. -/
theorem degreeOf_le_of_lex_degree_le {K : Type*} [Field K] {bg R : MvPolynomial (Fin 2) K}
    (hbg : bg ≠ 0) (hR : R ≠ 0)
    (hle : MonomialOrder.lex.degree bg ≼[MonomialOrder.lex] MonomialOrder.lex.degree R) :
    degreeOf 0 bg ≤ degreeOf 0 R := by
  rw [MonomialOrder.lex_le_iff] at hle
  have := apply_zero_le_of_toLex_le hle
  rwa [lex_degree_apply_zero hbg, lex_degree_apply_zero hR] at this

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

/-- **`C d` divides the `K[x][y]` view of any `y`-degree-bounded ideal member** (the bounded-rep +
sum half of the descent). If `R ∈ I`, `R ≠ 0`, and `C d ∣ lazardView b` for every basis element `b`
of `y`-degree `≤ degreeOf 0 R`, then `C d ∣ lazardView R`: GB-reduce `R = ∑ b ∈ B, g b · b` with each
contributing `b` of bounded `y`-degree (`exists_yDegree_bounded_representation`), then aggregate by
`C_dvd_lazardView_sum`. -/
theorem C_dvd_lazardView_of_mem_of_dvd_bounded {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    {d : MvPolynomial (Fin 1) K} {R : MvPolynomial (Fin 2) K} (hRI : R ∈ I) (hR0 : R ≠ 0)
    (hdvd : ∀ b ∈ B, degreeOf 0 b ≤ degreeOf 0 R → Polynomial.C d ∣ lazardView b) :
    Polynomial.C d ∣ lazardView R := by
  obtain ⟨g, hgsum, hgdeg⟩ := exists_yDegree_bounded_representation hB hRI hR0
  rw [hgsum, lazardView, map_sum]
  refine Finset.dvd_sum (fun b hb => ?_)
  by_cases hbne : g b * b = 0
  · rw [hbne, map_zero]; exact dvd_zero _
  · rw [map_mul]
    exact Dvd.dvd.mul_left (hdvd b hb (hgdeg b hb hbne)) _

/-- **`C(g_i) ∣ C q · lazardView fj` from `g_j ∣ fj` and `g_j·q = g_i`** (the higher-index transfer,
the satisfiable form of the descent step's first hypothesis). Since `g_i = g_j·q`, divisibility of
`q · (coeff)` by `g_i = g_j·q` is divisibility of `coeff` by `g_j`; so from `C(g_j) ∣ lazardView fj`
(`= P(j)` at the higher index) one gets `C(g_i) ∣ C q · lazardView fj`. -/
theorem C_dvd_C_mul_lazardView_of_dvd {K : Type*} [Field K] {fj : MvPolynomial (Fin 2) K}
    {gi gj q : MvPolynomial (Fin 1) K} (hq : gj * q = gi)
    (hfj : Polynomial.C gj ∣ lazardView fj) :
    Polynomial.C gi ∣ Polynomial.C q * lazardView fj := by
  rw [← hq, Polynomial.C_mul, mul_comm (Polynomial.C gj)]
  exact mul_dvd_mul_left _ hfj

/-- **Lazard's Lemma 3, the assembled single descent step** (Lazard 1985, p.263). For sorted basis
elements `fi := sortedByYDegree hB i`, `fj := sortedByYDegree hB j` and `q : K[x]`, the reduction
element `R := yConst q · fj − y^{shift}·fi ∈ I`. Given (1) `C(g_i) ∣ C q · lazardView fj` (which, with
`q = g_i/g_j`, follows from the higher-index `C(g_j) ∣ lazardView fj` via `C_dvd_C_mul_lazardView_of_dvd`)
and (2) `C(g_i) ∣ lazardView b` for every basis element of `y`-degree `≤ degreeOf 0 R` (the lower
contributors of `R`'s GB-reduction), one obtains `C(g_i) ∣ lazardView fi`. (Assembles
`C_dvd_lazardView_of_mem_of_dvd_bounded`, `lazard_lemma3_reductionStep_mem`, and
`C_dvd_lazardView_of_reductionStep_mul`.) Intended use: `q := g_i/g_j`
(`leadingYCoeff_sortedByYDegree_dvd_of_lt`) with `i < j`, where `R` has `y`-degree `< d(j)`
(`lazard_lemma3_reductionStep`). The remaining obstruction to closing the full induction is the
self-reference of (2) at `b = fi` (`y`-degree `d(i) ≤ degreeOf 0 R`), Lazard's no-common-factor
`÷q` step. -/
theorem C_dvd_lazardView_descentStep {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    {i j : Fin B.card} {q : MvPolynomial (Fin 1) K}
    (hfj : Polynomial.C (leadingYCoeff (sortedByYDegree hB i))
        ∣ Polynomial.C q * lazardView (sortedByYDegree hB j))
    (hR0 : yConst q * sortedByYDegree hB j
        - X 0 ^ (degreeOf 0 (sortedByYDegree hB j) - degreeOf 0 (sortedByYDegree hB i))
            * sortedByYDegree hB i ≠ 0)
    (hbounded : ∀ b ∈ B,
        degreeOf 0 b ≤ degreeOf 0 (yConst q * sortedByYDegree hB j
          - X 0 ^ (degreeOf 0 (sortedByYDegree hB j) - degreeOf 0 (sortedByYDegree hB i))
              * sortedByYDegree hB i) →
        Polynomial.C (leadingYCoeff (sortedByYDegree hB i)) ∣ lazardView b) :
    Polynomial.C (leadingYCoeff (sortedByYDegree hB i)) ∣ lazardView (sortedByYDegree hB i) := by
  set fi := sortedByYDegree hB i with hfi_def
  set fj := sortedByYDegree hB j with hfj_def
  have hRmem : yConst q * fj - X 0 ^ (degreeOf 0 fj - degreeOf 0 fi) * fi ∈ I :=
    lazard_lemma3_reductionStep_mem (hB.isGroebnerBasis.1 fi (sortedByYDegree_mem hB i))
      (hB.isGroebnerBasis.1 fj (sortedByYDegree_mem hB j))
  have hRdvd : Polynomial.C (leadingYCoeff fi)
      ∣ lazardView (yConst q * fj - X 0 ^ (degreeOf 0 fj - degreeOf 0 fi) * fi) :=
    C_dvd_lazardView_of_mem_of_dvd_bounded hB hRmem hR0 hbounded
  exact C_dvd_lazardView_of_reductionStep_mul (q := q) hfj hRdvd

end DeepWiki.SymbolicIntegration
