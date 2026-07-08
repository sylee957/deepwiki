import DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner.ReducedBasis.Monicize

/-! # Minimizing Gröbner bases

Keeps one representative for each minimal leading-monomial degree while
preserving the leading-term ideal.
-/

open MvPolynomial MonomialOrder

namespace DeepWiki.SymbolicIntegration

variable {σ : Type*} {m : MonomialOrder σ} {R : Type*} [CommRing R]

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

end DeepWiki.SymbolicIntegration
