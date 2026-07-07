import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.MvPolynomial.Ideal
import DeepWiki.SymbolicIntegration.Core.Polynomial.GroebnerReducedBasis
import DeepWiki.SymbolicIntegration.Core.Polynomial.GroebnerBivariateView
import DeepWiki.SymbolicIntegration.Core.Polynomial.GroebnerBivariateSorting
import DeepWiki.SymbolicIntegration.Core.Polynomial.GroebnerReductionStep
import DeepWiki.SymbolicIntegration.Core.Polynomial.GroebnerBoundedReduction

/-! # The one-step Lazard descent

The successor step in Lazard's bivariate descent: a divisibility invariant for all
lower sorted basis elements transfers from one `y`-degree index to the next. -/

open MvPolynomial MonomialOrder

namespace DeepWiki.SymbolicIntegration

/-! ## Lazard successor step

The step uses the sorted basis, the leading-`y`-coefficient divisibility chain,
and bounded Gröbner reduction of the cancellation polynomial. -/

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

/-- **The non-circular Lazard descent step.** Let
`fi = sorted i`, `fj = sorted i1` with `i < i1` *immediate* (every `j < i1` has `j ≤ i`, `hsucc`).
Given the induction hypothesis `C(gᵢ) ∣ lazardView (sorted j)` for **all** `j ≤ i` (`hIH`, which in
particular covers `fi`), one obtains `C(g_{i1}) ∣ lazardView f_{i1}`. Mechanism: with `q = gᵢ/g_{i1}`
(from `g_{i1} ∣ gᵢ`, `lazard_lemma2`) the reduction `R = yConst q · f_{i1} − y^{shift}·fi ∈ I` has
`y`-degree `< d(i1)`; its GB-reduction contributors are lower indices (`≤ i`, `hsucc`), so the IH
gives `C(gᵢ) ∣ lazardView R`. With `C(gᵢ) ∣ lazardView fi` (IH at `i`), the reduction equation gives
`C(gᵢ) ∣ C q · lazardView f_{i1}`; since `C(gᵢ) = C(g_{i1})·C q`, cancelling `C q` gives the goal —
**no** use of `g_{i1} ∣ f_{i1}` on the diagonal. -/
theorem C_dvd_lazardView_succ {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    {i i1 : Fin B.card} (hii1 : i < i1)
    (hsucc : ∀ j : Fin B.card, j < i1 → j ≤ i)
    (hIH : ∀ j : Fin B.card, j ≤ i →
      Polynomial.C (leadingYCoeff (sortedByYDegree hB i)) ∣ lazardView (sortedByYDegree hB j)) :
    Polynomial.C (leadingYCoeff (sortedByYDegree hB i1))
      ∣ lazardView (sortedByYDegree hB i1) := by
  set fi := sortedByYDegree hB i with hfi_def
  set fj := sortedByYDegree hB i1 with hfj_def
  set gi := leadingYCoeff fi with hgi
  set gj := leadingYCoeff fj with hgj
  have hfi0 : fi ≠ 0 := hB.ne_zero (Finset.mem_coe.mpr (sortedByYDegree_mem hB i))
  have hfj0 : fj ≠ 0 := hB.ne_zero (Finset.mem_coe.mpr (sortedByYDegree_mem hB i1))
  have hdlt : degreeOf 0 fi < degreeOf 0 fj := degreeOf_sortedByYDegree_strictMono hB hii1
  -- `q = gᵢ/g_{i1}` from `g_{i1} ∣ gᵢ` (Lemma 2).
  obtain ⟨q, hq⟩ := leadingYCoeff_sortedByYDegree_dvd_of_lt hB hii1
  -- the reduction element `R`.
  set sh := degreeOf 0 fj - degreeOf 0 fi with hsh
  set R := yConst q * fj - X 0 ^ sh * fi with hR_def
  have hRmem : R ∈ I :=
    lazard_lemma3_reductionStep_mem (hB.isGroebnerBasis.1 fi (sortedByYDegree_mem hB i))
      (hB.isGroebnerBasis.1 fj (sortedByYDegree_mem hB i1))
  have hRdeg : degreeOf 0 R < degreeOf 0 fj :=
    lazard_lemma3_reductionStep hfi0 hdlt hq.symm
  -- `C(gᵢ) ∣ lazardView R`: every GB-reduction contributor has `y`-degree `< d(i1)`, so index `≤ i`.
  have hRdvd : Polynomial.C gi ∣ lazardView R := by
    by_cases hR0 : R = 0
    · rw [hR0, lazardView_eq_zero_iff.mpr rfl]; exact dvd_zero _
    refine C_dvd_lazardView_of_mem_of_dvd_bounded hB hRmem hR0 (fun b hb hbdeg => ?_)
    -- `R`'s `y`-degree is `< d(i1)`, hence `degreeOf 0 b ≤ degreeOf 0 R < d(i1)`, so `b = sorted j, j ≤ i`.
    have hbi1 : degreeOf 0 b < degreeOf 0 fj := lt_of_le_of_lt hbdeg hRdeg
    obtain ⟨j, hji1, hbj⟩ := exists_sortedIndex_le_of_degreeOf_le (i := i1) hB hb (le_of_lt hbi1)
    have hjlt : j < i1 := by
      by_contra hge
      rw [not_lt] at hge
      have hle : degreeOf 0 fj ≤ degreeOf 0 (sortedByYDegree hB j) := by
        rcases lt_or_eq_of_le hge with h | h
        · exact le_of_lt (degreeOf_sortedByYDegree_strictMono hB h)
        · rw [hfj_def, h]
      rw [hbj] at hbi1
      exact absurd hbi1 (not_lt.mpr hle)
    rw [hbj]
    exact hIH j (hsucc j hjlt)
  -- `C(gᵢ) ∣ C q · lazardView f_{i1}` from the reduction equation (IH at `i` gives `C(gᵢ) ∣ lazardView fi`).
  have hfi_dvd : Polynomial.C gi ∣ lazardView fi := hIH i le_rfl
  have hCq : Polynomial.C gi ∣ Polynomial.C q * lazardView fj := by
    have heq : Polynomial.C q * lazardView fj
        = lazardView R + Polynomial.X ^ sh * lazardView fi := by
      rw [hR_def, lazardView_reductionStep]; ring
    rw [heq]
    exact dvd_add hRdvd (Dvd.dvd.mul_left hfi_dvd _)
  -- cancel `C q`: `C(gᵢ) = C(g_{i1})·C q`, so `C(g_{i1}) ∣ lazardView f_{i1}`.
  have hgi_eq : gi = gj * q := hq
  have hq0 : (q : MvPolynomial (Fin 1) K) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hgi_eq
    exact (leadingYCoeff_ne_zero.mpr hfi0) hgi_eq
  rw [hgi_eq, Polynomial.C_mul] at hCq
  -- `C(g_{i1}) · C q ∣ C q · lazardView f_{i1}` ⟹ `C(g_{i1}) ∣ lazardView f_{i1}`.
  rw [mul_comm (Polynomial.C gj)] at hCq
  exact (mul_dvd_mul_iff_left (by rwa [Ne, Polynomial.C_eq_zero])).mp hCq

end DeepWiki.SymbolicIntegration
