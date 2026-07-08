import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
import Mathlib.RingTheory.Bezout
import Mathlib.Data.Finsupp.PWO
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Data.Finsupp.MonomialOrder
import DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner.BasisBasic
import DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner.SPolynomial
import DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner.BuchbergerCriterion
import DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner.BuchbergerAlgorithm
import DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner.AutoReduction

/-! # Monicizing Gröbner bases

Normalizes leading coefficients of a finite Gröbner basis while preserving the
span and leading-term ideal.
-/

open MvPolynomial MonomialOrder

namespace DeepWiki.SymbolicIntegration

variable {σ : Type*} {m : MonomialOrder σ} {R : Type*} [CommRing R]

/-- `initialIdeal m I` equals the leading-term ideal of any Gröbner basis `B` of `I`
(`leadTermIdeal m B`). -/
theorem IsGroebnerBasis.initialIdeal_eq_leadTermIdeal {K : Type*} [Field K]
    {I : Ideal (MvPolynomial σ K)} {B : Finset (MvPolynomial σ K)}
    (hB : IsGroebnerBasis m I (↑B : Set (MvPolynomial σ K))) :
    initialIdeal m I = leadTermIdeal m B :=
  hB.2.2.symm

/-- A finite `B ⊆ I` with unit leading coefficients is a Gröbner basis of `I` iff its leading-term
ideal equals the initial ideal of `I`. -/
theorem isGroebnerBasis_iff_leadTermIdeal_eq {K : Type*} [Field K]
    {I : Ideal (MvPolynomial σ K)} {B : Finset (MvPolynomial σ K)}
    (hBI : ∀ b ∈ (↑B : Set (MvPolynomial σ K)), b ∈ I)
    (hlc : ∀ b ∈ (↑B : Set (MvPolynomial σ K)), IsUnit (m.leadingCoeff b)) :
    IsGroebnerBasis m I (↑B : Set (MvPolynomial σ K)) ↔ leadTermIdeal m B = initialIdeal m I :=
  ⟨fun hB => hB.2.2, fun h => ⟨hBI, hlc, h⟩⟩

open Classical in
/-- Monic rescaling of a basis: replace each `g ∈ B` by `C (m.leadingCoeff g)⁻¹ * g`, normalizing
the leading coefficient to `1`. -/
noncomputable def monicize {K : Type*} [Field K] (m : MonomialOrder σ)
    (B : Finset (MvPolynomial σ K)) : Finset (MvPolynomial σ K) :=
  B.image (fun g => C (m.leadingCoeff g)⁻¹ * g)

/-- The rescaling `C (lc g)⁻¹ * g` of nonzero `g` is monic, degree-preserving, and nonzero. -/
theorem leadingCoeff_C_inv_mul {K : Type*} [Field K] (m : MonomialOrder σ)
    {g : MvPolynomial σ K} (hg : g ≠ 0) :
    m.leadingCoeff (C (m.leadingCoeff g)⁻¹ * g) = 1 ∧
      m.degree (C (m.leadingCoeff g)⁻¹ * g) = m.degree g ∧ C (m.leadingCoeff g)⁻¹ * g ≠ 0 := by
  have hlcg : m.leadingCoeff g ≠ 0 := m.leadingCoeff_ne_zero_iff.mpr hg
  have hinv : (m.leadingCoeff g)⁻¹ ≠ 0 := inv_ne_zero hlcg
  refine ⟨?_, degree_C_mul m hinv g, ?_⟩
  · rw [leadingCoeff_C_mul m hinv g, inv_mul_cancel₀ hlcg]
  · rw [← m.leadingCoeff_ne_zero_iff, leadingCoeff_C_mul m hinv g, inv_mul_cancel₀ hlcg]
    exact one_ne_zero

open Classical in
/-- Membership in `monicize m B`: `x ∈ monicize m B` iff `x = C (lc g)⁻¹ * g` for some `g ∈ B`. -/
theorem mem_monicize {K : Type*} [Field K] (m : MonomialOrder σ)
    {B : Finset (MvPolynomial σ K)} {x : MvPolynomial σ K} :
    x ∈ monicize m B ↔ ∃ g ∈ B, C (m.leadingCoeff g)⁻¹ * g = x := by
  unfold monicize; rw [Finset.mem_image]

/-- Every element of `monicize m B` has leading coefficient `1` (given `B` has unit leading
coefficients). -/
theorem leadingCoeff_eq_one_of_mem_monicize {K : Type*} [Field K] (m : MonomialOrder σ)
    {B : Finset (MvPolynomial σ K)} (hB : ∀ g ∈ B, IsUnit (m.leadingCoeff g))
    {x : MvPolynomial σ K} (hx : x ∈ monicize m B) : m.leadingCoeff x = 1 := by
  obtain ⟨g, hg, rfl⟩ := (mem_monicize m).mp hx
  exact (leadingCoeff_C_inv_mul m (m.leadingCoeff_ne_zero_iff.mp (hB g hg).ne_zero)).1

/-- Monicize preserves the span: `Ideal.span ↑(monicize m B) = Ideal.span ↑B`. -/
theorem span_monicize {K : Type*} [Field K] (m : MonomialOrder σ)
    {B : Finset (MvPolynomial σ K)} (hB : ∀ g ∈ B, IsUnit (m.leadingCoeff g)) :
    Ideal.span (↑(monicize m B) : Set (MvPolynomial σ K)) = Ideal.span (↑B : Set (MvPolynomial σ K)) := by
  classical
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro x hx
    obtain ⟨g, hg, rfl⟩ := (mem_monicize m).mp (Finset.mem_coe.mp hx)
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span hg)
  · rw [Ideal.span_le]
    intro g hg
    have hg' : g ∈ B := Finset.mem_coe.mp hg
    have hlcg : m.leadingCoeff g ≠ 0 := (hB g hg').ne_zero
    -- `g = C (lc g) * (C (lc g)⁻¹ * g)`, and `C (lc g)⁻¹ * g ∈ monicize m B`.
    have hmem : C (m.leadingCoeff g)⁻¹ * g ∈ monicize m B :=
      (mem_monicize m).mpr ⟨g, hg', rfl⟩
    have : g = C (m.leadingCoeff g) * (C (m.leadingCoeff g)⁻¹ * g) := by
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hlcg, map_one, one_mul]
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Finset.mem_coe.mpr hmem))

/-- The leading-monomial-degree set is preserved by `monicize`:
`m.degree '' ↑(monicize m B) = m.degree '' ↑B`. -/
theorem degree_image_monicize {K : Type*} [Field K] (m : MonomialOrder σ)
    {B : Finset (MvPolynomial σ K)} (hB : ∀ g ∈ B, IsUnit (m.leadingCoeff g)) :
    m.degree '' (↑(monicize m B) : Set (MvPolynomial σ K)) = m.degree '' (↑B : Set (MvPolynomial σ K)) := by
  classical
  ext s
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨g, hg, rfl⟩ := (mem_monicize m).mp (Finset.mem_coe.mp hx)
    exact ⟨g, Finset.mem_coe.mpr hg,
      (leadingCoeff_C_inv_mul m (m.leadingCoeff_ne_zero_iff.mp (hB g hg).ne_zero)).2.1.symm⟩
  · rintro ⟨g, hg, rfl⟩
    refine ⟨C (m.leadingCoeff g)⁻¹ * g, Finset.mem_coe.mpr ((mem_monicize m).mpr
      ⟨g, Finset.mem_coe.mp hg, rfl⟩), ?_⟩
    exact (leadingCoeff_C_inv_mul m
      (m.leadingCoeff_ne_zero_iff.mp (hB g (Finset.mem_coe.mp hg)).ne_zero)).2.1

/-- Monicize preserves the leading-term ideal. -/
theorem leadTermIdeal_monicize {K : Type*} [Field K] (m : MonomialOrder σ)
    {B : Finset (MvPolynomial σ K)} (hB : ∀ g ∈ B, IsUnit (m.leadingCoeff g)) :
    leadTermIdeal m (monicize m B) = leadTermIdeal m B := by
  unfold leadTermIdeal
  rw [show (fun b => monomial (m.degree b) (1 : K)) '' (↑(monicize m B) : Set (MvPolynomial σ K))
      = (fun s => monomial s (1 : K)) '' (m.degree '' (↑(monicize m B) : Set (MvPolynomial σ K))) by
    rw [Set.image_image],
    show (fun b => monomial (m.degree b) (1 : K)) '' (↑B : Set (MvPolynomial σ K))
      = (fun s => monomial s (1 : K)) '' (m.degree '' (↑B : Set (MvPolynomial σ K))) by
    rw [Set.image_image],
    degree_image_monicize m hB]

/-- Monicizing a Gröbner basis gives a monic Gröbner basis of the same ideal. -/
theorem isGroebnerBasis_monicize {K : Type*} [Field K]
    {I : Ideal (MvPolynomial σ K)} {B : Finset (MvPolynomial σ K)}
    (hB : IsGroebnerBasis m I (↑B : Set (MvPolynomial σ K))) :
    IsGroebnerBasis m I (↑(monicize m B) : Set (MvPolynomial σ K)) ∧
      (∀ b ∈ (↑(monicize m B) : Set (MvPolynomial σ K)), m.leadingCoeff b = 1) := by
  classical
  have hBunit : ∀ g ∈ B, IsUnit (m.leadingCoeff g) := fun g hg => hB.2.1 g (Finset.mem_coe.mpr hg)
  have hmonic : ∀ b ∈ (↑(monicize m B) : Set (MvPolynomial σ K)), m.leadingCoeff b = 1 :=
    fun b hb => leadingCoeff_eq_one_of_mem_monicize m hBunit (Finset.mem_coe.mp hb)
  refine ⟨?_, hmonic⟩
  -- membership in `I`: each `C (lc g)⁻¹ * g` with `g ∈ B ⊆ I`.
  have hsub : ∀ b ∈ (↑(monicize m B) : Set (MvPolynomial σ K)), b ∈ I := by
    intro b hb
    obtain ⟨g, hg, rfl⟩ := (mem_monicize m).mp (Finset.mem_coe.mp hb)
    exact Ideal.mul_mem_left _ _ (hB.1 g (Finset.mem_coe.mpr hg))
  have hlc : ∀ b ∈ (↑(monicize m B) : Set (MvPolynomial σ K)), IsUnit (m.leadingCoeff b) :=
    fun b hb => by rw [hmonic b hb]; exact isUnit_one
  rw [isGroebnerBasis_iff_leadTermIdeal_eq hsub hlc, leadTermIdeal_monicize m hBunit,
    ← hB.initialIdeal_eq_leadTermIdeal]

end DeepWiki.SymbolicIntegration
