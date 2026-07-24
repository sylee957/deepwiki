import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.Data.Finsupp.MonomialOrder
import DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner.ReducedBasis
import DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner.BivariateView

/-! # Sorting bivariate Gröbner bases by y-degree

A reduced bivariate Gröbner basis over lex has distinct `y`-degrees, so it admits a
canonical enumeration by strictly increasing `degreeOf 0`. -/

open MvPolynomial MonomialOrder

namespace DeepWiki.SymbolicIntegration

variable {σ : Type*} {m : MonomialOrder σ}

/-! ## Sorting a minimal bivariate Gröbner basis by `y`-degree

The `y`-degrees `degreeOf 0` are distinct on a reduced basis, so `sortedByYDegree` enumerates `B`
by strictly increasing `y`-degree (via `Finset.orderEmbOfFin` on the injective `y`-degree image). -/

/-- In `Fin 2 →₀ ℕ`, two exponent vectors agreeing at index `0` are comparable. -/
theorem finsupp_fin_two_le_or_le_of_apply_zero_eq {d d' : Fin 2 →₀ ℕ} (h : d 0 = d' 0) :
    d ≤ d' ∨ d' ≤ d := by
  rcases le_total (d 1) (d' 1) with h1 | h1
  · refine Or.inl ?_
    rw [Finsupp.le_def]; intro i; fin_cases i
    · exact h.le
    · exact h1
  · refine Or.inr ?_
    rw [Finsupp.le_def]; intro i; fin_cases i
    · exact h.ge
    · exact h1

/-- Under `lex`, distinct elements of a reduced bivariate Gröbner basis have distinct `y`-degrees
`degreeOf 0`. -/
theorem lazard_degreeOf_ne {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K))) :
    ∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → degreeOf 0 b ≠ degreeOf 0 b' := by
  intro b hb b' hb' hne hdeg
  have hb0 : b ≠ 0 := hB.ne_zero (Finset.mem_coe.mpr hb)
  have hb'0 : b' ≠ 0 := hB.ne_zero (Finset.mem_coe.mpr hb')
  have hdeg' : (MonomialOrder.lex.degree b) 0 = (MonomialOrder.lex.degree b') 0 := by
    rw [lex_degree_apply_zero hb0, lex_degree_apply_zero hb'0, hdeg]
  rcases finsupp_fin_two_le_or_le_of_apply_zero_eq hdeg' with hle | hle
  · exact hB.leadingMonomial_not_le (Finset.mem_coe.mpr hb') (Finset.mem_coe.mpr hb)
      (Ne.symm hne) hle
  · exact hB.leadingMonomial_not_le (Finset.mem_coe.mpr hb) (Finset.mem_coe.mpr hb') hne hle

/-- The `y`-degree key is injective on a reduced Gröbner basis. -/
theorem lazard_degreeOf_injOn {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K))) :
    Set.InjOn (fun b => degreeOf 0 b) (↑B : Set (MvPolynomial (Fin 2) K)) := by
  intro b hb b' hb' hdeg
  by_contra hne
  exact lazard_degreeOf_ne hB b hb b' hb' hne hdeg

/-- The image finset of `y`-degrees of the basis `B`. -/
noncomputable def yDegreeImage {K : Type*} [Field K] (B : Finset (MvPolynomial (Fin 2) K)) :
    Finset ℕ :=
  B.image (fun b => degreeOf 0 b)

/-- `(yDegreeImage B).card = B.card` for a reduced Gröbner basis. -/
theorem card_yDegreeImage {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K))) :
    (yDegreeImage B).card = B.card :=
  Finset.card_image_of_injOn (lazard_degreeOf_injOn hB)

/-- A unique basis element of any prescribed `y`-degree occurring in `B`. -/
theorem existsUnique_mem_degreeOf_eq {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    {d : ℕ} (hd : d ∈ yDegreeImage B) :
    ∃! b, b ∈ B ∧ degreeOf 0 b = d := by
  rw [yDegreeImage, Finset.mem_image] at hd
  obtain ⟨b, hbB, hbeq⟩ := hd
  refine ⟨b, ⟨hbB, hbeq⟩, ?_⟩
  rintro b' ⟨hb'B, hb'eq⟩
  exact lazard_degreeOf_injOn hB (Finset.mem_coe.mpr hb'B) (Finset.mem_coe.mpr hbB)
    (show degreeOf 0 b' = degreeOf 0 b by rw [hb'eq, hbeq])

open scoped Classical in
/-- The enumeration `Fin B.card → MvPolynomial (Fin 2) K` of `B` with strictly increasing `y`-degree
`degreeOf 0`. -/
noncomputable def sortedByYDegree {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (i : Fin B.card) : MvPolynomial (Fin 2) K :=
  B.choose (fun b => degreeOf 0 b = (yDegreeImage B).orderEmbOfFin (card_yDegreeImage hB) i)
    (existsUnique_mem_degreeOf_eq hB (Finset.orderEmbOfFin_mem _ _ _))

/-- `sortedByYDegree hB i ∈ B`: the sorted enumeration lands in the basis. -/
theorem sortedByYDegree_mem {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (i : Fin B.card) : sortedByYDegree hB i ∈ B := by
  classical
  exact Finset.choose_mem
    (fun b => degreeOf 0 b = (yDegreeImage B).orderEmbOfFin (card_yDegreeImage hB) i) B _

/-- `degreeOf 0 (sortedByYDegree hB i)` is the `i`-th value of the increasing `y`-degree
enumeration. -/
theorem degreeOf_sortedByYDegree {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (i : Fin B.card) :
    degreeOf 0 (sortedByYDegree hB i)
      = (yDegreeImage B).orderEmbOfFin (card_yDegreeImage hB) i := by
  classical
  exact Finset.choose_property
    (fun b => degreeOf 0 b = (yDegreeImage B).orderEmbOfFin (card_yDegreeImage hB) i) B _

/-- `i < j ⟹ degreeOf 0 (sortedByYDegree hB i) < degreeOf 0 (sortedByYDegree hB j)`. -/
theorem degreeOf_sortedByYDegree_strictMono {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K))) :
    StrictMono (fun i => degreeOf 0 (sortedByYDegree hB i)) := by
  intro i j hij
  simp only [degreeOf_sortedByYDegree]
  exact (Finset.orderEmbOfFin (yDegreeImage B) (card_yDegreeImage hB)).strictMono hij

/-- The sorted enumeration is injective. -/
theorem sortedByYDegree_injective {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K))) :
    Function.Injective (sortedByYDegree hB) := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact absurd (congrArg (fun b => degreeOf 0 b) hij)
      (ne_of_lt (degreeOf_sortedByYDegree_strictMono hB h))
  · exact absurd (congrArg (fun b => degreeOf 0 b) hij.symm)
      (ne_of_lt (degreeOf_sortedByYDegree_strictMono hB h))

/-- The range of the sorted enumeration is exactly `↑B`. -/
theorem range_sortedByYDegree {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K))) :
    Set.range (sortedByYDegree hB) = (↑B : Set (MvPolynomial (Fin 2) K)) := by
  classical
  refine Set.eq_of_subset_of_ncard_le ?_ ?_ (B.finite_toSet)
  · rintro _ ⟨i, rfl⟩; exact sortedByYDegree_mem hB i
  · rw [Set.ncard_coe_finset, Set.ncard_range_of_injective (sortedByYDegree_injective hB)]
    simp [Nat.card_eq_fintype_card]

/-- **A bounded `y`-degree basis element is a lower sorted index.** If `b ∈ B` has
`degreeOf 0 b ≤ degreeOf 0 (sortedByYDegree hB i)`, then `b = sortedByYDegree hB j` for some `j ≤ i`
(the sort is a `y`-degree bijection onto `B`, strictly increasing). -/
theorem exists_sortedIndex_le_of_degreeOf_le {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    {i : Fin B.card} {b : MvPolynomial (Fin 2) K} (hbB : b ∈ B)
    (hdeg : degreeOf 0 b ≤ degreeOf 0 (sortedByYDegree hB i)) :
    ∃ j : Fin B.card, j ≤ i ∧ b = sortedByYDegree hB j := by
  have hmem : b ∈ Set.range (sortedByYDegree hB) := by
    rw [range_sortedByYDegree hB]; exact Finset.mem_coe.mpr hbB
  obtain ⟨j, hj⟩ := hmem
  refine ⟨j, ?_, hj.symm⟩
  by_contra hlt
  rw [not_le] at hlt
  have hmono := degreeOf_sortedByYDegree_strictMono hB hlt
  simp only at hmono
  rw [← hj] at hdeg
  exact absurd hdeg (not_le.mpr hmono)

end DeepWiki.SymbolicIntegration
