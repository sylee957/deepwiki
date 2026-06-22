import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.Data.Finsupp.PWO

/-! # Gröbner bases over a monomial order

A Gröbner-basis predicate built on Mathlib's monomial-order division algorithm
(`MonomialOrder.div_set`) and monomial-ideal membership: `IsGroebnerBasis m I B`
says the leading monomials of `B ⊆ I` generate the *initial ideal* of `I`. The
characteristic property `f ∈ I ↔` the division remainder of `f` by `B` is `0`
follows. This is the reusable foundation for the Czichowski Gröbner-basis
construction (Bronstein §2.6). -/

open MvPolynomial MonomialOrder

namespace DeepWiki.SymbolicIntegration

variable {σ : Type*} {m : MonomialOrder σ} {R : Type*} [CommRing R]

/-- The initial (leading-monomial) ideal of `I`: spanned by the leading monomials
`monomial (m.degree f) 1` of the nonzero `f ∈ I`. -/
noncomputable def initialIdeal (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ R)) :
    Ideal (MvPolynomial σ R) :=
  Ideal.span ((fun f => monomial (m.degree f) (1 : R)) '' {f | f ∈ I ∧ f ≠ 0})

/-- `B` is a Gröbner basis of `I`: `B ⊆ I`, the leading coefficients of `B` are
units, and the leading monomials of `B` generate the initial ideal of `I`. -/
def IsGroebnerBasis (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ R))
    (B : Set (MvPolynomial σ R)) : Prop :=
  (∀ b ∈ B, b ∈ I) ∧ (∀ b ∈ B, IsUnit (m.leadingCoeff b)) ∧
    Ideal.span ((fun b => monomial (m.degree b) (1 : R)) '' B) = initialIdeal m I

/-- The `div_set` linear combination `∑ b * g b` lies in any ideal `I` containing
every `b ∈ B`. -/
theorem linearCombination_mem_of_subset {B : Set (MvPolynomial σ R)}
    {I : Ideal (MvPolynomial σ R)} (hBI : ∀ b ∈ B, b ∈ I)
    (g : B →₀ MvPolynomial σ R) :
    Finsupp.linearCombination _ (fun b : B => (b : MvPolynomial σ R)) g ∈ I := by
  rw [Finsupp.linearCombination_apply]
  refine Submodule.sum_mem _ ?_
  intro b _
  simp only [smul_eq_mul]
  exact Ideal.mul_mem_left _ _ (hBI b b.2)

variable {I : Ideal (MvPolynomial σ R)} {B : Set (MvPolynomial σ R)}

/-- **Characteristic property of a Gröbner basis.** For a Gröbner basis `B` of `I`
and the quotient `g`/remainder `r` from dividing `f` by `B`, one has `f ∈ I ↔ r = 0`. -/
theorem IsGroebnerBasis.mem_iff_div_remainder_eq_zero (hB : IsGroebnerBasis m I B)
    (f : MvPolynomial σ R) {g : B →₀ MvPolynomial σ R} {r : MvPolynomial σ R}
    (hgr : f = Finsupp.linearCombination _ (fun b : B => (b : MvPolynomial σ R)) g + r)
    (hrem : ∀ c ∈ r.support, ∀ b ∈ B, ¬ (m.degree b ≤ c)) :
    f ∈ I ↔ r = 0 := by
  obtain ⟨hBI, _, hinit⟩ := hB
  have hcomb : Finsupp.linearCombination _ (fun b : B => (b : MvPolynomial σ R)) g ∈ I :=
    linearCombination_mem_of_subset hBI g
  constructor
  · -- `f ∈ I ⟹ r = 0`
    intro hfI
    -- `r = f - ∑ b·g b ∈ I`
    have hrI : r ∈ I := by
      have : r = f - Finsupp.linearCombination _ (fun b : B => (b : MvPolynomial σ R)) g := by
        rw [hgr]; ring
      rw [this]; exact I.sub_mem hfI hcomb
    by_contra hr0
    -- the leading monomial of `r` is in its support
    have hmem : m.degree r ∈ r.support := degree_mem_support hr0
    -- and `monomial (m.degree r) 1` lies in the initial ideal of `I`
    have hgen : monomial (m.degree r) (1 : R) ∈ initialIdeal m I :=
      Ideal.subset_span ⟨r, ⟨hrI, hr0⟩, rfl⟩
    rw [← hinit] at hgen
    -- rewrite the generating set as `monomial · 1` of `m.degree '' B`
    have himg : (fun b => monomial (m.degree b) (1 : R)) '' B
        = (fun s => monomial s (1 : R)) '' (m.degree '' B) := by
      rw [Set.image_image]
    rw [himg, mem_ideal_span_monomial_image] at hgen
    -- its support is `{m.degree r}` (as `1 ≠ 0`), so we get a divisor among the `degree b`
    have hne : (1 : R) ≠ 0 := by
      rcases subsingleton_or_nontrivial R with hs | _
      · exact absurd (Subsingleton.elim r 0) hr0
      · exact one_ne_zero
    obtain ⟨si, ⟨b, hbB, hb⟩, hsi⟩ := hgen (m.degree r) (by
      classical
      rw [mem_support_iff, coeff_monomial, if_pos rfl]
      exact hne)
    rw [← hb] at hsi
    exact hrem (m.degree r) hmem b hbB hsi
  · -- `r = 0 ⟹ f = ∑ b·g b ∈ I`
    intro hr0
    rw [hgr, hr0, add_zero]
    exact hcomb

/-- A *reduced* Gröbner basis: a Gröbner basis that is monic (every leading coefficient
is `1`) and reduced (no support monomial of any `b` is divisible by the leading monomial
of a different `b'`). -/
def IsReducedGroebnerBasis (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ R))
    (B : Set (MvPolynomial σ R)) : Prop :=
  IsGroebnerBasis m I B ∧ (∀ b ∈ B, m.leadingCoeff b = 1) ∧
    (∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → ∀ c ∈ b.support, ¬ (m.degree b' ≤ c))

/-- A reduced Gröbner basis is a Gröbner basis. -/
theorem IsReducedGroebnerBasis.isGroebnerBasis (hB : IsReducedGroebnerBasis m I B) :
    IsGroebnerBasis m I B := hB.1

/-- A Gröbner basis of `I` generates `I`. -/
theorem IsGroebnerBasis.span_eq (hB : IsGroebnerBasis m I B) : Ideal.span B = I := by
  apply le_antisymm
  · rw [Ideal.span_le]; exact hB.1
  · intro f hfI
    obtain ⟨g, r, hgr, _, hrem⟩ := MonomialOrder.div_set hB.2.1 f
    have hr0 : r = 0 :=
      (hB.mem_iff_div_remainder_eq_zero f hgr hrem).mp hfI
    rw [hgr, hr0, add_zero, Finsupp.linearCombination_apply]
    refine Submodule.sum_mem _ ?_
    intro b _
    simp only [smul_eq_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span b.2)

/-- **Existence of a Gröbner basis** (Dickson's lemma). Over a field, with finitely many
variables, every ideal `I` has a finite Gröbner basis `B`. The leading monomials of `I`
form a monomial ideal whose minimal generators are finite (Dickson: `σ →₀ ℕ` is a
well-quasi-order); a representative polynomial for each minimal degree is a Gröbner basis. -/
theorem exists_isGroebnerBasis {σ K : Type*} [Finite σ] [Field K] (m : MonomialOrder σ)
    (I : Ideal (MvPolynomial σ K)) :
    ∃ B : Finset (MvPolynomial σ K), IsGroebnerBasis m I (↑B : Set (MvPolynomial σ K)) := by
  classical
  -- The set of leading-monomial degrees of nonzero `f ∈ I`.
  set S : Set (σ →₀ ℕ) := {s | ∃ f, f ∈ I ∧ f ≠ 0 ∧ m.degree f = s} with hS
  -- Dickson's lemma: `σ →₀ ℕ` is a WQO when `σ` is finite, so `S` is partially well-ordered.
  have hSpwo : S.IsPWO := Set.isPWO_of_wellQuasiOrderedLE S
  -- The minimal degrees form an antichain in `S`, hence a finite set.
  set M : Set (σ →₀ ℕ) := {s | Minimal (· ∈ S) s} with hM
  have hMS : M ⊆ S := fun s hs => hs.1
  have hMac : IsAntichain (· ≤ ·) M := by
    intro a ha b hb hab hle
    exact hab (hle.antisymm (hb.2 ha.1 hle))
  have hMfin : M.Finite := hMac.finite_of_partiallyWellOrderedOn (hSpwo.mono hMS)
  -- A total representative: a chosen nonzero `f ∈ I` of each degree in `S`, else `0`.
  have hrepr : ∀ s ∈ S, ∃ f, f ∈ I ∧ f ≠ 0 ∧ m.degree f = s := fun s hs => hs
  choose! repr hreprI hrepr0 hreprdeg using hrepr
  refine ⟨hMfin.toFinset.image repr, ?_, ?_, ?_⟩
  · -- `B ⊆ I`
    intro b hb
    simp only [Finset.coe_image, Set.mem_image, Set.Finite.coe_toFinset] at hb
    obtain ⟨s, hsM, rfl⟩ := hb
    exact hreprI s (hMS hsM)
  · -- leading coefficients are units (field, nonzero)
    intro b hb
    simp only [Finset.coe_image, Set.mem_image, Set.Finite.coe_toFinset] at hb
    obtain ⟨s, hsM, rfl⟩ := hb
    exact m.isUnit_leadingCoeff.mpr (hrepr0 s (hMS hsM))
  · -- the leading monomials of `B` generate the initial ideal
    -- rewrite both leading-monomial images as `monomial · 1` of the degree-image
    have himgB : (fun b => monomial (m.degree b) (1 : K)) ''
          (↑(hMfin.toFinset.image repr) : Set (MvPolynomial σ K))
        = (fun t => monomial t (1 : K)) ''
          (m.degree '' (↑(hMfin.toFinset.image repr) : Set (MvPolynomial σ K))) := by
      rw [Set.image_image]
    apply le_antisymm
    · -- `span (leading monomials of B) ⊆ initialIdeal m I`
      rw [Ideal.span_le]
      rintro _ ⟨b, hb, rfl⟩
      simp only [Finset.coe_image, Set.mem_image, Set.Finite.coe_toFinset] at hb
      obtain ⟨s, hsM, rfl⟩ := hb
      exact Ideal.subset_span
        ⟨repr s, ⟨hreprI s (hMS hsM), hrepr0 s (hMS hsM)⟩, rfl⟩
    · -- `initialIdeal m I ⊆ span (leading monomials of B)`
      rw [initialIdeal, Ideal.span_le]
      rintro _ ⟨f, ⟨hfI, hf0⟩, rfl⟩
      -- `m.degree f ∈ S`, so it dominates a minimal degree `s ∈ M`
      have hfS : m.degree f ∈ S := ⟨f, hfI, hf0, rfl⟩
      obtain ⟨s, hsle, hsmin⟩ := hSpwo.exists_le_minimal hfS
      have hsM : s ∈ M := hsmin
      rw [SetLike.mem_coe, himgB, mem_ideal_span_monomial_image]
      -- `monomial (m.degree f) 1` has support `{m.degree f}`; `s ≤ m.degree f`
      intro xi hxi
      have hxi' : xi = m.degree f := by
        rw [mem_support_iff, coeff_monomial, ne_eq, ite_eq_right_iff,
          Classical.not_imp, eq_comm] at hxi
        exact hxi.1
      refine ⟨s, ?_, hxi' ▸ hsle⟩
      -- `s = m.degree (repr s)` is a degree of an element of `B`
      refine ⟨repr s, ?_, hreprdeg s (hMS hsM)⟩
      simp only [Finset.coe_image, Set.mem_image, Set.Finite.coe_toFinset]
      exact ⟨s, hsM, rfl⟩

-- Restatements against the intended wording.
example (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ R))
    (B : Set (MvPolynomial σ R)) : Prop := IsGroebnerBasis m I B

example (hB : IsGroebnerBasis m I B) (f : MvPolynomial σ R)
    {g : B →₀ MvPolynomial σ R} {r : MvPolynomial σ R}
    (hgr : f = Finsupp.linearCombination _ (fun b : B => (b : MvPolynomial σ R)) g + r)
    (hrem : ∀ c ∈ r.support, ∀ b ∈ B, ¬ (m.degree b ≤ c)) :
    f ∈ I ↔ r = 0 :=
  hB.mem_iff_div_remainder_eq_zero f hgr hrem

example (hB : IsGroebnerBasis m I B) : Ideal.span B = I := hB.span_eq

example (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ R))
    (B : Set (MvPolynomial σ R)) : Prop :=
  IsGroebnerBasis m I B ∧ (∀ b ∈ B, m.leadingCoeff b = 1) ∧
    (∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → ∀ c ∈ b.support, ¬ (m.degree b' ≤ c))

example (hB : IsReducedGroebnerBasis m I B) : IsGroebnerBasis m I B := hB.isGroebnerBasis

example {σ K : Type*} [Finite σ] [Field K] (m : MonomialOrder σ)
    (I : Ideal (MvPolynomial σ K)) :
    ∃ B : Finset (MvPolynomial σ K), IsGroebnerBasis m I (↑B : Set (MvPolynomial σ K)) :=
  exists_isGroebnerBasis m I

end DeepWiki.SymbolicIntegration
