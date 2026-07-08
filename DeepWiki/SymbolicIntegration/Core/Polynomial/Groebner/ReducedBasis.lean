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
import DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner.BasisExistence

/-! # Reduced Gröbner bases

Monicization, minimal leading-monomial representatives, auto-reduction, and
existence of finite reduced Gröbner bases. -/

open MvPolynomial MonomialOrder

namespace DeepWiki.SymbolicIntegration

variable {σ : Type*} {m : MonomialOrder σ} {R : Type*} [CommRing R]
/-! ## Existence of a reduced Gröbner basis (one-pass inter-reduction)

Monicizing, minimizing (deleting redundant elements), and auto-reducing a finite Gröbner basis
produces a reduced one; each step preserves `Ideal.span` and the leading-monomial set. -/

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

/-- A chosen element of `B` realizing a given leading-monomial degree `s ∈ B.image m.degree`. -/
noncomputable def degreeRepr {K : Type*} [Field K] (m : MonomialOrder σ)
    (B : Finset (MvPolynomial σ K)) (s : σ →₀ ℕ) : MvPolynomial σ K := by
  classical
  exact if h : ∃ g ∈ B, m.degree g = s then h.choose else 0

/-- `degreeRepr m B s ∈ B` and `m.degree (degreeRepr m B s) = s` when `s` is a realized degree. -/
theorem degreeRepr_spec {K : Type*} [Field K] (m : MonomialOrder σ)
    (B : Finset (MvPolynomial σ K)) {s : σ →₀ ℕ} (hs : ∃ g ∈ B, m.degree g = s) :
    degreeRepr m B s ∈ B ∧ m.degree (degreeRepr m B s) = s := by
  classical
  unfold degreeRepr
  rw [dif_pos hs]
  exact ⟨hs.choose_spec.1, hs.choose_spec.2⟩

open Classical in
/-- The leading-monomial degrees of `B` that are minimal under `≤`. -/
noncomputable def minimalDegrees {K : Type*} [Field K] (m : MonomialOrder σ)
    (B : Finset (MvPolynomial σ K)) : Finset (σ →₀ ℕ) :=
  (B.image m.degree).filter (fun s => ∀ t ∈ B.image m.degree, t ≤ s → t = s)

open Classical in
/-- Minimal reduction of a basis: keep one representative element per minimal leading-monomial
degree of `B`. -/
noncomputable def minimize {K : Type*} [Field K] (m : MonomialOrder σ)
    (B : Finset (MvPolynomial σ K)) : Finset (MvPolynomial σ K) :=
  (minimalDegrees m B).image (degreeRepr m B)

open Classical in
/-- Membership in `minimalDegrees`: `s` is a realized degree, minimal among realized degrees. -/
theorem mem_minimalDegrees {K : Type*} [Field K] (m : MonomialOrder σ)
    {B : Finset (MvPolynomial σ K)} {s : σ →₀ ℕ} :
    s ∈ minimalDegrees m B ↔
      (∃ g ∈ B, m.degree g = s) ∧ ∀ t ∈ B.image m.degree, t ≤ s → t = s := by
  classical
  unfold minimalDegrees
  rw [Finset.mem_filter, Finset.mem_image]

open Classical in
/-- Every realized degree of `B` dominates a minimal one. -/
theorem exists_minimalDegree_le {K : Type*} [Field K] [Finite σ] (m : MonomialOrder σ)
    {B : Finset (MvPolynomial σ K)} {s : σ →₀ ℕ} (hs : s ∈ B.image m.degree) :
    ∃ t ∈ minimalDegrees m B, t ≤ s := by
  classical
  -- the realized-degree set is partially well-ordered, so it has a minimal element below `s`.
  set S : Set (σ →₀ ℕ) := (↑(B.image m.degree) : Set (σ →₀ ℕ)) with hS
  have hSpwo : S.IsPWO := (B.image m.degree).finite_toSet.isPWO
  obtain ⟨t, htle, htmin⟩ := hSpwo.exists_le_minimal (Finset.mem_coe.mpr hs)
  refine ⟨t, ?_, htle⟩
  rw [mem_minimalDegrees]
  refine ⟨?_, fun u hu hule => ?_⟩
  · obtain ⟨g, hg, hgd⟩ := Finset.mem_image.mp htmin.1
    exact ⟨g, hg, hgd⟩
  · exact le_antisymm hule (htmin.2 (Finset.mem_coe.mpr hu) hule)

open Classical in
/-- Membership in `minimize m B`: `x` is the chosen representative of some minimal degree. -/
theorem mem_minimize {K : Type*} [Field K] (m : MonomialOrder σ)
    {B : Finset (MvPolynomial σ K)} {x : MvPolynomial σ K} :
    x ∈ minimize m B ↔ ∃ s ∈ minimalDegrees m B, degreeRepr m B s = x := by
  classical
  unfold minimize
  rw [Finset.mem_image]

/-- `minimize m B ⊆ B`: every representative is an element of `B`. -/
theorem minimize_subset {K : Type*} [Field K] (m : MonomialOrder σ)
    {B : Finset (MvPolynomial σ K)} :
    (↑(minimize m B) : Set (MvPolynomial σ K)) ⊆ (↑B : Set (MvPolynomial σ K)) := by
  classical
  intro x hx
  obtain ⟨s, hs, rfl⟩ := (mem_minimize m).mp (Finset.mem_coe.mp hx)
  exact Finset.mem_coe.mpr (degreeRepr_spec m B (mem_minimalDegrees m |>.mp hs).1).1

/-- The leading-monomial-degree set of `minimize m B` is exactly `minimalDegrees m B`. -/
theorem degree_image_minimize {K : Type*} [Field K] (m : MonomialOrder σ)
    {B : Finset (MvPolynomial σ K)} :
    m.degree '' (↑(minimize m B) : Set (MvPolynomial σ K)) = (↑(minimalDegrees m B) : Set (σ →₀ ℕ)) := by
  classical
  ext s
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨t, ht, rfl⟩ := (mem_minimize m).mp (Finset.mem_coe.mp hx)
    rw [(degreeRepr_spec m B (mem_minimalDegrees m |>.mp ht).1).2]
    exact Finset.mem_coe.mpr ht
  · intro hs
    refine ⟨degreeRepr m B s, Finset.mem_coe.mpr ((mem_minimize m).mpr
      ⟨s, Finset.mem_coe.mp hs, rfl⟩), ?_⟩
    exact (degreeRepr_spec m B (mem_minimalDegrees m |>.mp (Finset.mem_coe.mp hs)).1).2

/-- Minimize preserves the leading-term ideal: `leadTermIdeal m (minimize m B) = leadTermIdeal m B`. -/
theorem leadTermIdeal_minimize {K : Type*} [Field K] [Finite σ] (m : MonomialOrder σ)
    {B : Finset (MvPolynomial σ K)} :
    leadTermIdeal m (minimize m B) = leadTermIdeal m B := by
  classical
  unfold leadTermIdeal
  rw [show (fun b => monomial (m.degree b) (1 : K)) '' (↑(minimize m B) : Set (MvPolynomial σ K))
      = (fun s => monomial s (1 : K)) '' (m.degree '' (↑(minimize m B) : Set (MvPolynomial σ K))) by
    rw [Set.image_image],
    show (fun b => monomial (m.degree b) (1 : K)) '' (↑B : Set (MvPolynomial σ K))
      = (fun s => monomial s (1 : K)) '' (m.degree '' (↑B : Set (MvPolynomial σ K))) by
    rw [Set.image_image],
    degree_image_minimize]
  apply le_antisymm
  · -- minimal monomials ⊆ all monomials (minimalDegrees ⊆ degree-image of B)
    apply Ideal.span_mono
    apply Set.image_mono
    intro s hs
    obtain ⟨g, hg, hgd⟩ := (mem_minimalDegrees m |>.mp (Finset.mem_coe.mp hs)).1
    exact ⟨g, Finset.mem_coe.mpr hg, hgd⟩
  · -- every degree of `B` dominates a minimal one
    rw [Ideal.span_le]
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨g, hg, rfl⟩ := hs
    rw [SetLike.mem_coe, mem_ideal_span_monomial_image]
    intro xi hxi
    have hxi' : xi = m.degree g := by
      rw [mem_support_iff, coeff_monomial, ne_eq, ite_eq_right_iff,
        Classical.not_imp, eq_comm] at hxi
      exact hxi.1
    obtain ⟨t, ht, htle⟩ := exists_minimalDegree_le m (Finset.mem_image.mpr ⟨g, hg, rfl⟩)
    exact ⟨t, Finset.mem_coe.mpr ht, hxi' ▸ htle⟩

/-- Minimizing a monic Gröbner basis gives a monic Gröbner basis of the same ideal with pairwise
non-dividing leading monomials. -/
theorem isGroebnerBasis_minimize {K : Type*} [Field K] [Finite σ]
    {I : Ideal (MvPolynomial σ K)} {B : Finset (MvPolynomial σ K)}
    (hB : IsGroebnerBasis m I (↑B : Set (MvPolynomial σ K)))
    (hmonic : ∀ b ∈ (↑B : Set (MvPolynomial σ K)), m.leadingCoeff b = 1) :
    IsGroebnerBasis m I (↑(minimize m B) : Set (MvPolynomial σ K)) ∧
      (∀ b ∈ (↑(minimize m B) : Set (MvPolynomial σ K)), m.leadingCoeff b = 1) ∧
      (∀ b ∈ (↑(minimize m B) : Set (MvPolynomial σ K)),
        ∀ b' ∈ (↑(minimize m B) : Set (MvPolynomial σ K)), b ≠ b' →
          ¬ (m.degree b' ≤ m.degree b)) := by
  classical
  have hsub := minimize_subset (m := m) (B := B)
  have hmonic' : ∀ b ∈ (↑(minimize m B) : Set (MvPolynomial σ K)), m.leadingCoeff b = 1 :=
    fun b hb => hmonic b (hsub hb)
  have hBI : ∀ b ∈ (↑(minimize m B) : Set (MvPolynomial σ K)), b ∈ I :=
    fun b hb => hB.1 b (hsub hb)
  have hlc : ∀ b ∈ (↑(minimize m B) : Set (MvPolynomial σ K)), IsUnit (m.leadingCoeff b) :=
    fun b hb => by rw [hmonic' b hb]; exact isUnit_one
  have hgb : IsGroebnerBasis m I (↑(minimize m B) : Set (MvPolynomial σ K)) := by
    rw [isGroebnerBasis_iff_leadTermIdeal_eq hBI hlc, leadTermIdeal_minimize,
      ← hB.initialIdeal_eq_leadTermIdeal]
  refine ⟨hgb, hmonic', fun b hb b' hb' hne hle => hne ?_⟩
  -- distinct elements have distinct degrees: `degreeRepr` is injective on `minimalDegrees`.
  obtain ⟨s, hs, rfl⟩ := (mem_minimize m).mp (Finset.mem_coe.mp hb)
  obtain ⟨s', hs', rfl⟩ := (mem_minimize m).mp (Finset.mem_coe.mp hb')
  have hsd : m.degree (degreeRepr m B s) = s := (degreeRepr_spec m B (mem_minimalDegrees m |>.mp hs).1).2
  have hs'd : m.degree (degreeRepr m B s') = s' := (degreeRepr_spec m B (mem_minimalDegrees m |>.mp hs').1).2
  -- `m.degree b' ≤ m.degree b` becomes `s' ≤ s`; `s` minimal forces `s' = s`.
  rw [hsd, hs'd] at hle
  have hs'mem : s' ∈ B.image m.degree := by
    obtain ⟨g, hg, hgd⟩ := (mem_minimalDegrees m |>.mp hs').1
    exact Finset.mem_image.mpr ⟨g, hg, hgd⟩
  have hseq : s' = s := (mem_minimalDegrees m |>.mp hs).2 s' hs'mem hle
  rw [hseq]

/-- Over a field with finitely many variables, every ideal `I` has a finite reduced Gröbner basis. -/
theorem exists_isReducedGroebnerBasis {σ K : Type*} [Finite σ] [Field K] (m : MonomialOrder σ)
    (I : Ideal (MvPolynomial σ K)) :
    ∃ B : Finset (MvPolynomial σ K), IsReducedGroebnerBasis m I (↑B : Set (MvPolynomial σ K)) := by
  classical
  -- Step 0: a Gröbner basis exists.
  obtain ⟨B₀, hB₀⟩ := exists_isGroebnerBasis m I
  -- Step 1: monicize it.
  obtain ⟨hB₁, hmonic₁⟩ := isGroebnerBasis_monicize hB₀
  -- Step 2: minimize it (monic GB with pairwise non-dividing leading monomials).
  obtain ⟨hB₂, hmonic₂, hpair₂⟩ := isGroebnerBasis_minimize hB₁ hmonic₁
  -- Step 3: auto-reduce, yielding a reduced Gröbner basis.
  have hBu₂ : ∀ b ∈ minimize m (monicize m B₀), IsUnit (m.leadingCoeff b) :=
    fun b hb => by rw [hmonic₂ b (Finset.mem_coe.mpr hb)]; exact isUnit_one
  exact ⟨autoReduce m hBu₂, isReducedGroebnerBasis_autoReduce hBu₂ hB₂ hmonic₂ hpair₂⟩

end DeepWiki.SymbolicIntegration
