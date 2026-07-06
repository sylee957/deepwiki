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
import DeepWiki.SymbolicIntegration.Core.Polynomial.GroebnerBasisBasic
import DeepWiki.SymbolicIntegration.Core.Polynomial.GroebnerSPolynomial

/-! # Gröbner bases over a monomial order

A Gröbner-basis predicate over Mathlib's monomial-order division algorithm:
`IsGroebnerBasis m I B` says the leading monomials of `B ⊆ I` generate the initial
ideal of `I`, with the characteristic property `f ∈ I ↔` remainder `= 0`. -/

open MvPolynomial MonomialOrder

namespace DeepWiki.SymbolicIntegration

variable {σ : Type*} {m : MonomialOrder σ} {R : Type*} [CommRing R]
variable {I : Ideal (MvPolynomial σ R)} {B : Set (MvPolynomial σ R)}

/-- Over a field with finitely many variables, every ideal `I` has a finite Gröbner basis. -/
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

/-- If `B ⊆ I` has unit leading coefficients, generates `I`, and every nonzero `f ∈ I` has its
leading monomial divisible by `m.degree b` for some `b ∈ B`, then `B` is a Gröbner basis of `I`. -/
theorem isGroebnerBasis_of_exists_leadingMonomial_le {K : Type*} [Field K]
    {I : Ideal (MvPolynomial σ K)} {B : Set (MvPolynomial σ K)}
    (hBI : ∀ b ∈ B, b ∈ I) (hlc : ∀ b ∈ B, IsUnit (m.leadingCoeff b))
    (hdvd : ∀ f ∈ I, f ≠ 0 → ∃ b ∈ B, m.degree b ≤ m.degree f) :
    IsGroebnerBasis m I B := by
  classical
  refine ⟨hBI, hlc, ?_⟩
  -- rewrite both leading-monomial images as `monomial · 1` of the degree-image
  have himgB : (fun b => monomial (m.degree b) (1 : K)) '' B
      = (fun s => monomial s (1 : K)) '' (m.degree '' B) := by
    rw [Set.image_image]
  apply le_antisymm
  · -- `span (leading monomials of B) ⊆ initialIdeal m I`
    rw [Ideal.span_le]
    rintro _ ⟨b, hb, rfl⟩
    have hb0 : b ≠ 0 := by
      intro h0
      simpa [h0] using hlc b hb
    exact Ideal.subset_span ⟨b, ⟨hBI b hb, hb0⟩, rfl⟩
  · -- `initialIdeal m I ⊆ span (leading monomials of B)`
    rw [initialIdeal, Ideal.span_le]
    rintro _ ⟨f, ⟨hfI, hf0⟩, rfl⟩
    rw [SetLike.mem_coe, himgB, mem_ideal_span_monomial_image]
    -- `monomial (m.degree f) 1` has support `{m.degree f}`
    intro xi hxi
    have hxi' : xi = m.degree f := by
      rw [mem_support_iff, coeff_monomial, ne_eq, ite_eq_right_iff,
        Classical.not_imp, eq_comm] at hxi
      exact hxi.1
    obtain ⟨b, hbB, hble⟩ := hdvd f hfI hf0
    exact ⟨m.degree b, ⟨b, hbB, rfl⟩, hxi' ▸ hble⟩

/-- For a representation `f = ∑ b, c b` over a finite index set, the bound
`m.degree f ≼[m] Finset.univ.sup (fun b => m.degree (c b))` (a summand of maximal degree
dominates the degree of `f`). -/
theorem degree_le_sup_of_eq_sum {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    {f : MvPolynomial σ K} {c : ι → MvPolynomial σ K}
    (hf : f = ∑ b, c b) :
    m.toSyn (m.degree f) ≤ Finset.univ.sup (fun b => m.toSyn (m.degree (c b))) := by
  rw [hf]; exact degree_sum_le

/-- `m.degree g ≤ m.degree (h * g)` over a field for `h * g ≠ 0`: a factor's exponent vector is
dominated coordinatewise by the product's (degrees add, all exponents nonnegative). -/
theorem degree_le_degree_mul {K : Type*} [Field K] {h g : MvPolynomial σ K}
    (hne : h * g ≠ 0) : m.degree g ≤ m.degree (h * g) := by
  have hh : h ≠ 0 := fun h0 => hne (by rw [h0, zero_mul])
  have hg : g ≠ 0 := fun h0 => hne (by rw [h0, mul_zero])
  rw [degree_mul hh hg]
  exact le_add_self

/-- If `B` generates `I` and every S-polynomial `S(b,b')` has a standard representation `∑ q c · c`
with summand degrees `≼[m] m.degree (S(b,b'))`, then every nonzero `f ∈ I` has its leading monomial
divisible by `m.degree b` for some `b ∈ B`. -/
theorem exists_leadingMonomial_le {K : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (B : Finset (MvPolynomial σ K))
    (hspan : Ideal.span (↑B : Set (MvPolynomial σ K)) = I)
    (hS : ∀ b ∈ B, ∀ b' ∈ B, ∃ q : B → MvPolynomial σ K,
      sPolynomial m b b' = ∑ c ∈ B.attach, q c * (c : MvPolynomial σ K) ∧
        ∀ c, m.degree (q c * (c : MvPolynomial σ K)) ≼[m] m.degree (sPolynomial m b b')) :
    ∀ f ∈ I, f ≠ 0 → ∃ b ∈ B, m.degree b ≤ m.degree f := by
  classical
  -- For a representation `h : B → MvPolynomial`, its `δ` is the max summand degree.
  set deltaOf : (B → MvPolynomial σ K) → m.syn :=
    fun h => Finset.univ.sup (fun b : B => m.toSyn (m.degree (h b * (b : MvPolynomial σ K))))
    with hdeltaOf
  intro f hfI hf0
  -- `f ∈ span B`, so it has at least one representation.
  have hfspan : f ∈ Ideal.span (↑B : Set (MvPolynomial σ K)) := hspan ▸ hfI
  have hrep0 : ∃ h : B → MvPolynomial σ K,
      f = ∑ b : B, h b * (b : MvPolynomial σ K) := by
    rw [Submodule.mem_span_finset'] at hfspan
    obtain ⟨h, hh⟩ := hfspan
    exact ⟨h, by rw [← hh]; exact Finset.sum_congr rfl (fun b _ => by rw [smul_eq_mul])⟩
  -- The set of achievable `δ`-values, with its well-founded minimum.
  set D : Set m.syn := {d | ∃ h : B → MvPolynomial σ K,
    f = ∑ b : B, h b * (b : MvPolynomial σ K) ∧ deltaOf h = d} with hD
  have hDne : D.Nonempty := by
    obtain ⟨h, hh⟩ := hrep0
    exact ⟨deltaOf h, h, hh, rfl⟩
  have hwf : WellFounded ((· < ·) : m.syn → m.syn → Prop) := wellFounded_lt
  set δ := hwf.min D hDne with hδdef
  have hδmem : δ ∈ D := hwf.min_mem D hDne
  obtain ⟨h, hfh, hδeq⟩ := hδmem
  -- Always `m.degree f ≼[m] δ`.
  have hfδ : m.toSyn (m.degree f) ≤ δ := by
    rw [← hδeq, hdeltaOf]; exact degree_le_sup_of_eq_sum hfh
  -- `B` is nonempty: an empty `B` would give `f = 0`.
  have hBne : (Finset.univ : Finset B).Nonempty := by
    rw [Finset.univ_nonempty_iff]
    rcases isEmpty_or_nonempty B with he | hne
    · exfalso; apply hf0; rw [hfh, Finset.univ_eq_empty, Finset.sum_empty]
    · exact hne
  -- Dichotomy on `m.degree f = δ` vs `m.degree f ≺[m] δ`.
  rcases eq_or_lt_of_le hfδ with heq | hlt
  · -- Equality case: a *nonzero* summand of maximal degree has `m.degree (h b · b) = δ`,
    -- so its base `b` has `m.degree b ≤ m.degree (h b · b) = m.degree f`.
    -- Work over the nonempty Finset of nonzero summands.
    set NZ : Finset B := Finset.univ.filter
      (fun b : B => h b * (b : MvPolynomial σ K) ≠ 0) with hNZ
    have hNZne : NZ.Nonempty := by
      rw [Finset.filter_nonempty_iff]
      by_contra hcon
      push Not at hcon
      exact hf0 (by rw [hfh]; exact Finset.sum_eq_zero (fun b _ => hcon b (Finset.mem_univ b)))
    -- `δ` is the sup over all summands, equal to the sup over nonzero summands.
    have hsupNZ : NZ.sup (fun b => m.toSyn (m.degree (h b * (b : MvPolynomial σ K)))) = δ := by
      rw [← hδeq, hdeltaOf]
      apply le_antisymm (Finset.sup_mono (Finset.filter_subset _ _))
      apply Finset.sup_le
      intro b _
      by_cases hb0 : h b * (b : MvPolynomial σ K) = 0
      · simp [hb0]
      · exact Finset.le_sup (f := fun b => m.toSyn (m.degree (h b * (b : MvPolynomial σ K))))
          (Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb0⟩)
    obtain ⟨b₀, hb₀mem, hb₀eq⟩ := Finset.exists_mem_eq_sup NZ hNZne
      (fun b => m.toSyn (m.degree (h b * (b : MvPolynomial σ K))))
    have hb₀ne : h b₀ * (b₀ : MvPolynomial σ K) ≠ 0 :=
      (Finset.mem_filter.mp hb₀mem).2
    have hb₀δ : m.toSyn (m.degree (h b₀ * (b₀ : MvPolynomial σ K))) = δ := by
      rw [← hb₀eq, hsupNZ]
    refine ⟨b₀, b₀.2, ?_⟩
    -- `m.degree (h b₀ · b₀) = m.degree f` (equal syn values, `toSyn` injective).
    have hdegeq : m.degree (h b₀ * (b₀ : MvPolynomial σ K)) = m.degree f :=
      m.toSyn.injective (by rw [hb₀δ, heq])
    have hle : m.degree (b₀ : MvPolynomial σ K) ≤ m.degree (h b₀ * (b₀ : MvPolynomial σ K)) :=
      degree_le_degree_mul hb₀ne
    rwa [hdegeq] at hle
  · -- Strict case: build a smaller-`δ` representation, contradicting minimality of `δ`.
    exfalso
    -- `δ > 0` since `0 ≤ degree-syn f < δ`.
    have hδpos : (0 : m.syn) < δ := lt_of_le_of_lt (m.zero_le _) hlt
    -- `BelowDelta p` : `p` is a `B`-combination all of whose summands have degree-syn `< δ`.
    let BelowDelta : MvPolynomial σ K → Prop := fun p => ∃ h' : B → MvPolynomial σ K,
      p = ∑ b : B, h' b * (b : MvPolynomial σ K) ∧
        ∀ b : B, m.toSyn (m.degree (h' b * (b : MvPolynomial σ K))) < δ
    -- `BelowDelta` is closed under `0`, addition, and finite sums.
    have hBD0 : BelowDelta 0 := ⟨0, by simp, fun b => by simp [hδpos]⟩
    have hBDadd : ∀ p₁ p₂, BelowDelta p₁ → BelowDelta p₂ → BelowDelta (p₁ + p₂) := by
      rintro p₁ p₂ ⟨h₁, hp₁, hd₁⟩ ⟨h₂, hp₂, hd₂⟩
      refine ⟨fun b => h₁ b + h₂ b, ?_, fun b => ?_⟩
      · rw [hp₁, hp₂, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun b _ => by rw [add_mul])
      · rw [add_mul]
        exact lt_of_le_of_lt degree_add_le (max_lt (hd₁ b) (hd₂ b))
    have hBDsum : ∀ (s : Finset B) (p : B → MvPolynomial σ K),
        (∀ i ∈ s, BelowDelta (p i)) → BelowDelta (∑ i ∈ s, p i) := by
      intro s p hp
      classical
      induction s using Finset.induction_on with
      | empty => simpa using hBD0
      | insert a s ha ih =>
        rw [Finset.sum_insert ha]
        exact hBDadd _ _ (hp a (Finset.mem_insert_self a s))
          (ih (fun i hi => hp i (Finset.mem_insert_of_mem hi)))
    -- Leading-term family: at top-degree summands take `LT(h b) · b`, else `0`.
    set g : B → MvPolynomial σ K := fun b =>
      if m.toSyn (m.degree (h b * (b : MvPolynomial σ K))) = δ
        then m.leadingTerm (h b) * (b : MvPolynomial σ K) else 0 with hg
    -- Each top-degree summand `h b · b` is nonzero (its degree-syn is `δ > 0`).
    have hbne : ∀ b : B, m.toSyn (m.degree (h b * (b : MvPolynomial σ K))) = δ →
        h b * (b : MvPolynomial σ K) ≠ 0 := by
      intro b hb h0
      rw [h0, degree_zero, map_zero] at hb
      exact (ne_of_lt hδpos) hb
    -- `m.degree (g b) = m.degree (h b · b)` and `g b ≠ 0` at top-degree summands.
    have hgdeg : ∀ b : B, m.toSyn (m.degree (h b * (b : MvPolynomial σ K))) = δ →
        m.degree (g b) = m.degree (h b * (b : MvPolynomial σ K)) := by
      intro b hb
      rw [hg]; simp only [hb, if_true]
      exact degree_leadingTerm_mul (h b) (b : MvPolynomial σ K)
    -- Family hypothesis for `sPolynomial_decomposition`.
    have hd : ∀ b ∈ (Finset.univ : Finset B),
        (m.toSyn (m.degree (g b)) = δ ∧ IsUnit (m.leadingCoeff (g b))) ∨ g b = 0 := by
      intro b _
      by_cases hb : m.toSyn (m.degree (h b * (b : MvPolynomial σ K))) = δ
      · left
        have hgdegb : m.toSyn (m.degree (g b)) = δ := by rw [hgdeg b hb, hb]
        refine ⟨hgdegb, ?_⟩
        rw [isUnit_leadingCoeff]
        intro h0
        rw [h0, degree_zero, map_zero] at hgdegb
        exact (ne_of_lt hδpos) hgdegb
      · right
        rw [hg]; simp only [hb, if_false]
    -- Each `h b · b - g b` (the "lower part" of summand `b`) has degree-syn `< δ`.
    have hlow : ∀ b : B, m.toSyn (m.degree (h b * (b : MvPolynomial σ K) - g b)) < δ := by
      intro b
      by_cases hb : m.toSyn (m.degree (h b * (b : MvPolynomial σ K))) = δ
      · -- top summand: `h b·b - LT(h b)·b = (h b - leadingTerm (h b))·b`
        have hgb : g b = m.leadingTerm (h b) * (b : MvPolynomial σ K) := by
          rw [hg]; simp only [hb, if_true]
        rw [hgb, ← sub_mul]
        by_cases hsub : h b - m.leadingTerm (h b) = 0
        · rw [hsub, zero_mul, degree_zero, map_zero]; exact hδpos
        · have hbne0 : (b : MvPolynomial σ K) ≠ 0 := by
            intro h0; exact hbne b hb (by rw [h0, mul_zero])
          have hhb0 : h b ≠ 0 := by
            intro h0; exact hbne b hb (by rw [h0, zero_mul])
          have hdeghb : m.degree (h b) ≠ 0 :=
            m.degree_ne_zero_of_sub_leadingTerm_ne_zero hsub
          have hdsub : m.degree (h b - m.leadingTerm (h b)) ≺[m] m.degree (h b) :=
            (m.degree_sub_leadingTerm_lt_iff).mpr hdeghb
          calc m.toSyn (m.degree ((h b - m.leadingTerm (h b)) * (b : MvPolynomial σ K)))
              ≤ m.toSyn (m.degree (h b - m.leadingTerm (h b)) + m.degree (b : MvPolynomial σ K)) :=
                degree_mul_le
            _ = m.toSyn (m.degree (h b - m.leadingTerm (h b)))
                  + m.toSyn (m.degree (b : MvPolynomial σ K)) := by rw [map_add]
            _ < m.toSyn (m.degree (h b)) + m.toSyn (m.degree (b : MvPolynomial σ K)) := by
                exact add_lt_add_of_lt_of_le hdsub le_rfl
            _ = m.toSyn (m.degree (h b) + m.degree (b : MvPolynomial σ K)) := by rw [map_add]
            _ = m.toSyn (m.degree (h b * (b : MvPolynomial σ K))) := by rw [degree_mul hhb0 hbne0]
            _ = δ := hb
      · -- non-top summand: `g b = 0`, so the term is `h b·b`, with degree-syn `< δ`.
        have hgb : g b = 0 := by rw [hg]; simp only [hb, if_false]
        rw [hgb, sub_zero]
        have hle : m.toSyn (m.degree (h b * (b : MvPolynomial σ K))) ≤ δ := by
          rw [← hδeq, hdeltaOf]
          exact Finset.le_sup (f := fun b => m.toSyn (m.degree (h b * (b : MvPolynomial σ K))))
            (Finset.mem_univ b)
        exact lt_of_le_of_ne hle hb
    -- Hence `∑ g b = f - ∑ (h b·b - g b)` has degree-syn `< δ`.
    have hfd : m.toSyn (m.degree (∑ b : B, g b)) < δ := by
      have hsumeq : (∑ b : B, g b) = f - ∑ b : B, (h b * (b : MvPolynomial σ K) - g b) := by
        rw [Finset.sum_sub_distrib, ← hfh]; ring
      rw [hsumeq]
      refine lt_of_le_of_lt degree_sub_le ?_
      rw [max_lt_iff]
      exact ⟨hlt, lt_of_le_of_lt degree_sum_le ((Finset.sup_lt_iff hδpos).mpr
        (fun b _ => hlow b))⟩
    obtain ⟨cc, hcc⟩ := m.sPolynomial_decomposition hd hfd
    -- Each scaled S-polynomial `cc•S(g b₁, g b₂)` is `BelowDelta`.
    have hSpair : ∀ b₁ b₂ : B, BelowDelta (cc b₁ b₂ • m.sPolynomial (g b₁) (g b₂)) := by
      intro b₁ b₂
      by_cases hz : g b₁ = 0 ∨ g b₂ = 0
      · rcases hz with h0 | h0 <;> simpa [h0] using hBD0
      push Not at hz
      obtain ⟨hz1, hz2⟩ := hz
      -- both `g bᵢ` are top-degree, hence `g bᵢ = LT(h bᵢ)·bᵢ` with degree-syn `δ`.
      have htop1 : m.toSyn (m.degree (h b₁ * (b₁ : MvPolynomial σ K))) = δ := by
        by_contra hb; rw [hg] at hz1; simp only [hb, if_false] at hz1; exact hz1 rfl
      have htop2 : m.toSyn (m.degree (h b₂ * (b₂ : MvPolynomial σ K))) = δ := by
        by_contra hb; rw [hg] at hz2; simp only [hb, if_false] at hz2; exact hz2 rfl
      have hgb1 : g b₁ = m.leadingTerm (h b₁) * (b₁ : MvPolynomial σ K) := by
        rw [hg]; simp only [htop1, if_true]
      have hgb2 : g b₂ = m.leadingTerm (h b₂) * (b₂ : MvPolynomial σ K) := by
        rw [hg]; simp only [htop2, if_true]
      have hb1ne : (b₁ : MvPolynomial σ K) ≠ 0 := fun h0 => hbne b₁ htop1 (by rw [h0, mul_zero])
      have hb2ne : (b₂ : MvPolynomial σ K) ≠ 0 := fun h0 => hbne b₂ htop2 (by rw [h0, mul_zero])
      -- both `g bᵢ` have the *same* Finsupp degree `m.toSyn.symm δ`.
      have hdfs1 : m.degree (g b₁) = m.toSyn.symm δ := by
        rw [hgb1, degree_leadingTerm_mul, ← htop1, AddEquiv.symm_apply_apply]
      have hdfs2 : m.degree (g b₂) = m.toSyn.symm δ := by
        rw [hgb2, degree_leadingTerm_mul, ← htop2, AddEquiv.symm_apply_apply]
      -- expand `S(g b₁, g b₂) = (monomial e d) * ourS b₁ b₂` (leading-term scaling + bridge).
      obtain ⟨q, hq, hqdeg⟩ := hS b₁ b₁.2 b₂ b₂.2
      set e : σ →₀ ℕ :=
        (m.degree (h b₁) + m.degree (b₁ : MvPolynomial σ K))
            ⊔ (m.degree (h b₂) + m.degree (b₂ : MvPolynomial σ K))
          - m.degree (b₁ : MvPolynomial σ K) ⊔ m.degree (b₂ : MvPolynomial σ K) with he
      set d : K := m.leadingCoeff (h b₁) * m.leadingCoeff (h b₂)
          * (m.leadingCoeff (b₁ : MvPolynomial σ K) * m.leadingCoeff (b₂ : MvPolynomial σ K))
          with hd_def
      -- bridge in the un-normalized direction.
      have hbridge : m.sPolynomial (b₁ : MvPolynomial σ K) (b₂ : MvPolynomial σ K)
          = (m.leadingCoeff (b₁ : MvPolynomial σ K) * m.leadingCoeff (b₂ : MvPolynomial σ K))
              • sPolynomial m b₁ b₂ := by
        rw [sPolynomial_eq_inv_smul_mathlib m hb1ne hb2ne, smul_smul,
          mul_inv_cancel₀ (mul_ne_zero (m.leadingCoeff_ne_zero_iff.mpr hb1ne)
            (m.leadingCoeff_ne_zero_iff.mpr hb2ne)), one_smul]
      have hSexp : m.sPolynomial (g b₁) (g b₂) = monomial e d * sPolynomial m b₁ b₂ := by
        rw [hgb1, hgb2, sPolynomial_leadingTerm_mul, ← he, hbridge, hd_def,
          mul_smul_comm, ← smul_mul_assoc, smul_monomial, smul_eq_mul, mul_comm
            (m.leadingCoeff (b₁ : MvPolynomial σ K) * m.leadingCoeff (b₂ : MvPolynomial σ K))]
      -- if `S(g b₁,g b₂) = 0`, the scaled term is `0` (`BelowDelta`).
      by_cases hSz : m.sPolynomial (g b₁) (g b₂) = 0
      · rw [hSz, smul_zero]; exact hBD0
      have hourSne : sPolynomial m (b₁ : MvPolynomial σ K) (b₂ : MvPolynomial σ K) ≠ 0 := by
        intro hh; apply hSz; rw [hSexp, hh, mul_zero]
      have hd0 : d ≠ 0 := fun hh => by simp [hSexp, hh] at hSz
      have hSltδ : m.toSyn (m.degree (m.sPolynomial (g b₁) (g b₂))) < δ := by
        have := m.degree_sPolynomial_lt_sup_degree hSz
        rwa [hdfs1, hdfs2, sup_idem, AddEquiv.apply_symm_apply] at this
      -- each summand `cc•(monomial e d * q c · c)` has degree `≤ degree(S(g·,g·)) < δ`.
      have hkey : ∀ c : B, m.toSyn (m.degree (cc b₁ b₂ •
          (monomial e d * q c * (c : MvPolynomial σ K)))) < δ := by
        intro c
        calc m.toSyn (m.degree (cc b₁ b₂ • (monomial e d * q c * (c : MvPolynomial σ K))))
            ≤ m.toSyn (m.degree (monomial e d * q c * (c : MvPolynomial σ K))) :=
              degree_smul_le
          _ = m.toSyn (m.degree (monomial e d * (q c * (c : MvPolynomial σ K)))) := by
              rw [mul_assoc]
          _ ≤ m.toSyn (m.degree (monomial e d) + m.degree (q c * (c : MvPolynomial σ K))) :=
              degree_mul_le
          _ ≤ m.toSyn (m.degree (monomial e d)
                + m.degree (sPolynomial m (b₁ : MvPolynomial σ K) (b₂ : MvPolynomial σ K))) := by
              rw [map_add, map_add]; gcongr; exact hqdeg c
          _ = m.toSyn (m.degree (monomial e d
                * sPolynomial m (b₁ : MvPolynomial σ K) (b₂ : MvPolynomial σ K))) := by
              rw [degree_mul ((monomial_eq_zero (s := e)).not.mpr hd0) hourSne]
          _ = m.toSyn (m.degree (m.sPolynomial (g b₁) (g b₂))) := by rw [hSexp]
          _ < δ := hSltδ
      -- assemble `cc•S(g b₁,g b₂)` as a `B`-sum of `BelowDelta` terms.
      refine ⟨fun c => cc b₁ b₂ • (monomial e d * q c), ?_, ?_⟩
      · rw [hSexp, hq, Finset.mul_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl (fun c _ => ?_)
        rw [smul_mul_assoc, mul_assoc]
      · intro c; rw [smul_mul_assoc]; exact hkey c
    -- `∑ g b = ∑∑ cc•S(g·,g·)` is `BelowDelta`; so is `∑ (lowpart)`; hence `f` is `BelowDelta`.
    have hSumG : BelowDelta (∑ b : B, g b) := by
      rw [hcc]
      exact hBDsum Finset.univ (fun b₁ => ∑ b₂ : B, cc b₁ b₂ • m.sPolynomial (g b₁) (g b₂))
        (fun b₁ _ => hBDsum Finset.univ _ (fun b₂ _ => hSpair b₁ b₂))
    have hlowBD : BelowDelta (∑ b : B, (h b * (b : MvPolynomial σ K) - g b)) := by
      refine hBDsum _ _ (fun b _ => ?_)
      -- `h b·b - g b = (lowcoeff b)·b` with degree `< δ` (proved in `hlow`).
      by_cases hb : m.toSyn (m.degree (h b * (b : MvPolynomial σ K))) = δ
      · have hgb : g b = m.leadingTerm (h b) * (b : MvPolynomial σ K) := by
          rw [hg]; simp only [hb, if_true]
        refine ⟨fun c => if c = b then h b - m.leadingTerm (h b) else 0, ?_, fun c => ?_⟩
        · simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
          rw [hgb, sub_mul]
        · by_cases hc : c = b
          · subst hc; simp only [if_true]; rw [sub_mul, ← hgb]; exact hlow c
          · simp [hc, hδpos]
      · have hgb : g b = 0 := by rw [hg]; simp only [hb, if_false]
        refine ⟨fun c => if c = b then h b else 0, ?_, fun c => ?_⟩
        · simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
          rw [hgb, sub_zero]
        · by_cases hc : c = b
          · subst hc; simp only [if_true]
            have := hlow c; rwa [hgb, sub_zero] at this
          · simp [hc, hδpos]
    -- `f = (∑ g b) + ∑ (h b·b - g b)`, so `f` is `BelowDelta`: a smaller-`δ` representation.
    have hfBD : BelowDelta f := by
      have : f = (∑ b : B, g b) + ∑ b : B, (h b * (b : MvPolynomial σ K) - g b) := by
        rw [Finset.sum_sub_distrib, ← hfh]; ring
      rw [this]; exact hBDadd _ _ hSumG hlowBD
    -- this contradicts minimality of `δ`.
    obtain ⟨h', hfh', hd'⟩ := hfBD
    have hδ' : deltaOf h' < δ := by
      rw [hdeltaOf]; exact (Finset.sup_lt_iff hδpos).mpr (fun b _ => hd' b)
    exact hwf.not_lt_min D (show deltaOf h' ∈ D from ⟨h', hfh', rfl⟩) hδ'

/-- Buchberger's criterion, converse half: a generating set `B` of `I` with unit leading
coefficients whose every S-polynomial has a standard representation `∑ q c · c` with summand degrees
`≼[m] m.degree (S(b,b'))` (i.e. reduces to `0` modulo `B`) is a Gröbner basis of `I`. -/
theorem isGroebnerBasis_of_sPolynomial_reducesToZero {K : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (B : Finset (MvPolynomial σ K))
    (hBI : ∀ b ∈ B, b ∈ I) (hlc : ∀ b ∈ B, IsUnit (m.leadingCoeff b))
    (hspan : Ideal.span (↑B : Set (MvPolynomial σ K)) = I)
    (hS : ∀ b ∈ B, ∀ b' ∈ B, ∃ q : B → MvPolynomial σ K,
      sPolynomial m b b' = ∑ c ∈ B.attach, q c * (c : MvPolynomial σ K) ∧
        ∀ c, m.degree (q c * (c : MvPolynomial σ K)) ≼[m] m.degree (sPolynomial m b b')) :
    IsGroebnerBasis m I (↑B : Set (MvPolynomial σ K)) :=
  isGroebnerBasis_of_exists_leadingMonomial_le hBI hlc
    (exists_leadingMonomial_le I B hspan hS)

/-! ## Buchberger's algorithm: completion step, termination, and correctness

The S-polynomial completion step (adjoining nonzero remainders), with termination from the
Noetherian ascending-chain condition on leading-term ideals and the resulting correctness. -/

/-- The chosen division data (quotient family, remainder) of `f` by the finite set `B`
(with unit leading coefficients), extracted from `MonomialOrder.div_set` by choice. -/
noncomputable def divData {K : Type*} [Field K] (m : MonomialOrder σ)
    {B : Finset (MvPolynomial σ K)} (hB : ∀ b ∈ B, IsUnit (m.leadingCoeff b))
    (f : MvPolynomial σ K) :
    ((↑B : Set (MvPolynomial σ K)) →₀ MvPolynomial σ K) × MvPolynomial σ K :=
  let h := MonomialOrder.div_set (m := m) (B := (↑B : Set (MvPolynomial σ K)))
    (fun b hb => hB b (by simpa using hb)) f
  (h.choose, h.choose_spec.choose)

/-- The division remainder (normal form) of `f` by `B`: the `r` from `MonomialOrder.div_set`. -/
noncomputable def remainder {K : Type*} [Field K] (m : MonomialOrder σ)
    {B : Finset (MvPolynomial σ K)} (hB : ∀ b ∈ B, IsUnit (m.leadingCoeff b))
    (f : MvPolynomial σ K) : MvPolynomial σ K :=
  (divData m hB f).2

/-- The defining `div_set` properties of `remainder m hB f`: a standard representation
`f = ∑ b·(g b) + r`, degree bounds `m.degree (b·g b) ≼[m] m.degree f`, and the remainder is
reduced (no support monomial is divisible by a leading monomial of `B`). -/
theorem remainder_spec {K : Type*} [Field K] (m : MonomialOrder σ)
    {B : Finset (MvPolynomial σ K)} (hB : ∀ b ∈ B, IsUnit (m.leadingCoeff b))
    (f : MvPolynomial σ K) :
    (f = Finsupp.linearCombination _
        (fun (b : (↑B : Set (MvPolynomial σ K))) => (b : MvPolynomial σ K)) (divData m hB f).1
        + remainder m hB f) ∧
      (∀ (b : (↑B : Set (MvPolynomial σ K))),
        m.degree ((b : MvPolynomial σ K) * ((divData m hB f).1 b)) ≼[m] m.degree f) ∧
      (∀ c ∈ (remainder m hB f).support, ∀ b ∈ (↑B : Set (MvPolynomial σ K)),
        ¬ (m.degree b ≤ c)) := by
  unfold remainder divData
  exact (MonomialOrder.div_set (m := m) (B := (↑B : Set (MvPolynomial σ K)))
    (fun b hb => hB b (by simpa using hb)) f).choose_spec.choose_spec

/-- `Finsupp.linearCombination` over `↑B` rewritten as a sum over `B.attach`: the two index
subtypes `{x // x ∈ ↑B}` and `{x // x ∈ B}` coincide. -/
theorem linearCombination_eq_attach_sum {K : Type*} [Field K] (B : Finset (MvPolynomial σ K))
    (g : (↑B : Set (MvPolynomial σ K)) →₀ MvPolynomial σ K) :
    Finsupp.linearCombination _
        (fun (b : (↑B : Set (MvPolynomial σ K))) => (b : MvPolynomial σ K)) g
      = ∑ c ∈ B.attach, g c * (c : MvPolynomial σ K) := by
  classical
  rw [Finsupp.linearCombination_apply, Finsupp.sum,
    Finset.sum_subset (s₁ := g.support) (s₂ := B.attach) (fun x _ => Finset.mem_attach _ _)]
  · exact Finset.sum_congr rfl (fun c _ => by rw [smul_eq_mul])
  · intro x _ hx
    rw [Finsupp.notMem_support_iff.mp hx, zero_smul]

/-- The `div_set` quotient combination `f - remainder m hB f` lies in `Ideal.span ↑B`. -/
theorem sub_remainder_mem_span {K : Type*} [Field K] (m : MonomialOrder σ)
    {B : Finset (MvPolynomial σ K)} (hB : ∀ b ∈ B, IsUnit (m.leadingCoeff b))
    (f : MvPolynomial σ K) :
    f - remainder m hB f ∈ Ideal.span (↑B : Set (MvPolynomial σ K)) := by
  have heq := (remainder_spec m hB f).1
  rw [show f - remainder m hB f = Finsupp.linearCombination _
      (fun (b : (↑B : Set (MvPolynomial σ K))) => (b : MvPolynomial σ K)) (divData m hB f).1 by
    rw [sub_eq_iff_eq_add]; exact heq]
  exact linearCombination_mem_of_subset (fun b hb => Ideal.subset_span hb) (divData m hB f).1

/-- The remainder of an ideal element stays in the ideal: if `f ∈ Ideal.span ↑B` then
`remainder m hB f ∈ Ideal.span ↑B`. -/
theorem remainder_mem_span_of_mem {K : Type*} [Field K] (m : MonomialOrder σ)
    {B : Finset (MvPolynomial σ K)} (hB : ∀ b ∈ B, IsUnit (m.leadingCoeff b))
    {f : MvPolynomial σ K} (hf : f ∈ Ideal.span (↑B : Set (MvPolynomial σ K))) :
    remainder m hB f ∈ Ideal.span (↑B : Set (MvPolynomial σ K)) := by
  rw [show remainder m hB f = f - (f - remainder m hB f) by ring]
  exact (Ideal.span _).sub_mem hf (sub_remainder_mem_span m hB f)

open Classical in
/-- The nonzero S-polynomial remainders adjoined in one Buchberger step: over all pairs
`b, b' ∈ B`, the `remainder m hB (sPolynomial m b b')` that are nonzero. -/
noncomputable def newRemainders {K : Type*} [Field K] (m : MonomialOrder σ)
    {B : Finset (MvPolynomial σ K)} (hB : ∀ b ∈ B, IsUnit (m.leadingCoeff b)) :
    Finset (MvPolynomial σ K) :=
  ((B ×ˢ B).image (fun p => remainder m hB (sPolynomial m p.1 p.2))).erase 0

/-- Membership in `newRemainders`: `r ≠ 0` and `r` is the remainder of some pair's S-polynomial. -/
theorem mem_newRemainders {K : Type*} [Field K] (m : MonomialOrder σ)
    {B : Finset (MvPolynomial σ K)} (hB : ∀ b ∈ B, IsUnit (m.leadingCoeff b))
    (r : MvPolynomial σ K) :
    r ∈ newRemainders m hB ↔
      r ≠ 0 ∧ ∃ b ∈ B, ∃ b' ∈ B, remainder m hB (sPolynomial m b b') = r := by
  classical
  unfold newRemainders
  rw [Finset.mem_erase, Finset.mem_image]
  constructor
  · rintro ⟨hr0, ⟨p, hp, rfl⟩⟩
    rw [Finset.mem_product] at hp
    exact ⟨hr0, p.1, hp.1, p.2, hp.2, rfl⟩
  · rintro ⟨hr0, b, hb, b', hb', rfl⟩
    exact ⟨hr0, ⟨(b, b'), Finset.mem_product.mpr ⟨hb, hb'⟩, rfl⟩⟩

open Classical in
/-- **Buchberger's step**: adjoin to `B` the nonzero division remainders of all S-polynomials
`S(b,b')` (`b, b' ∈ B`). -/
noncomputable def buchbergerStep {K : Type*} [Field K] (m : MonomialOrder σ)
    {B : Finset (MvPolynomial σ K)} (hB : ∀ b ∈ B, IsUnit (m.leadingCoeff b)) :
    Finset (MvPolynomial σ K) :=
  B ∪ newRemainders m hB

/-- Every element of a Buchberger step has a unit leading coefficient (the originals by `hB`,
the new remainders because they are nonzero over a field). -/
theorem isUnit_leadingCoeff_of_mem_buchbergerStep {K : Type*} [Field K] (m : MonomialOrder σ)
    {B : Finset (MvPolynomial σ K)} (hB : ∀ b ∈ B, IsUnit (m.leadingCoeff b))
    {r : MvPolynomial σ K} (hr : r ∈ buchbergerStep m hB) : IsUnit (m.leadingCoeff r) := by
  classical
  unfold buchbergerStep at hr
  rw [Finset.mem_union] at hr
  rcases hr with h | h
  · exact hB r h
  · exact m.isUnit_leadingCoeff.mpr ((mem_newRemainders m hB r).mp h).1

/-- A Buchberger step contains the original basis: `↑B ⊆ ↑(buchbergerStep m hB)`. -/
theorem subset_buchbergerStep {K : Type*} [Field K] (m : MonomialOrder σ)
    {B : Finset (MvPolynomial σ K)} (hB : ∀ b ∈ B, IsUnit (m.leadingCoeff b)) :
    (↑B : Set (MvPolynomial σ K)) ⊆ ↑(buchbergerStep m hB) := by
  classical
  intro x hx
  unfold buchbergerStep
  rw [Finset.coe_union]
  exact Or.inl hx

/-- **A Buchberger step preserves the ideal**: the new elements are remainders of
S-polynomials of ideal members, hence already in `Ideal.span ↑B`. -/
theorem span_buchbergerStep {K : Type*} [Field K] (m : MonomialOrder σ)
    {B : Finset (MvPolynomial σ K)} (hB : ∀ b ∈ B, IsUnit (m.leadingCoeff b)) :
    Ideal.span (↑(buchbergerStep m hB) : Set (MvPolynomial σ K))
      = Ideal.span (↑B : Set (MvPolynomial σ K)) := by
  classical
  apply le_antisymm
  · rw [Ideal.span_le]
    intro x hx
    unfold buchbergerStep at hx
    rw [Finset.coe_union, Set.mem_union] at hx
    rcases hx with h | h
    · exact Ideal.subset_span h
    · rw [Finset.mem_coe, mem_newRemainders] at h
      obtain ⟨_, b, hb, b', hb', rfl⟩ := h
      exact remainder_mem_span_of_mem m hB
        (sPolynomial_mem (Ideal.subset_span hb) (Ideal.subset_span hb'))
  · exact Ideal.span_mono (subset_buchbergerStep m hB)

/-- The leading-term ideal of `B`: the ideal generated by the leading monomials of `B`
(`monomial (m.degree b) 1`, `b ∈ B`). Strictly grows whenever the step adds a new leading
monomial. -/
noncomputable def leadTermIdeal {K : Type*} [Field K] (m : MonomialOrder σ)
    (B : Finset (MvPolynomial σ K)) : Ideal (MvPolynomial σ K) :=
  Ideal.span ((fun b => monomial (m.degree b) (1 : K)) '' (↑B : Set (MvPolynomial σ K)))

/-- Membership in the leading-term ideal: `x ∈ leadTermIdeal m B` iff every support monomial of
`x` is divisible by some leading monomial `m.degree b` (`b ∈ B`). -/
theorem mem_leadTermIdeal {K : Type*} [Field K] (m : MonomialOrder σ)
    (B : Finset (MvPolynomial σ K)) (x : MvPolynomial σ K) :
    x ∈ leadTermIdeal m B ↔
      ∀ xi ∈ x.support, ∃ b ∈ (↑B : Set (MvPolynomial σ K)), m.degree b ≤ xi := by
  classical
  unfold leadTermIdeal
  rw [show (fun b => monomial (m.degree b) (1 : K)) '' (↑B : Set (MvPolynomial σ K))
      = (fun s => monomial s (1 : K)) '' (m.degree '' (↑B : Set (MvPolynomial σ K))) by
    rw [Set.image_image], mem_ideal_span_monomial_image]
  constructor
  · intro h xi hxi
    obtain ⟨si, ⟨b, hb, rfl⟩, hle⟩ := h xi hxi
    exact ⟨b, hb, hle⟩
  · intro h xi hxi
    obtain ⟨b, hb, hle⟩ := h xi hxi
    exact ⟨m.degree b, ⟨b, hb, rfl⟩, hle⟩

/-- The leading-term ideal is monotone in the basis. -/
theorem leadTermIdeal_mono {K : Type*} [Field K] (m : MonomialOrder σ)
    {B C : Finset (MvPolynomial σ K)} (h : (↑B : Set (MvPolynomial σ K)) ⊆ ↑C) :
    leadTermIdeal m B ≤ leadTermIdeal m C :=
  Ideal.span_mono (Set.image_mono h)

/-- **Progress dichotomy, the strict-growth half**: if a Buchberger step changes `B`, the new
leading monomial is not divisible by any `m.degree b` (`b ∈ B`), so the leading-term ideal
strictly grows: `leadTermIdeal m B < leadTermIdeal m (buchbergerStep m hB)`. -/
theorem leadTermIdeal_lt_of_ne {K : Type*} [Field K] (m : MonomialOrder σ)
    {B : Finset (MvPolynomial σ K)} (hB : ∀ b ∈ B, IsUnit (m.leadingCoeff b))
    (hne : buchbergerStep m hB ≠ B) :
    leadTermIdeal m B < leadTermIdeal m (buchbergerStep m hB) := by
  classical
  refine lt_of_le_of_ne (leadTermIdeal_mono m (subset_buchbergerStep m hB)) ?_
  intro heq
  apply hne
  refine Finset.Subset.antisymm ?_ (subset_buchbergerStep m hB)
  intro x hx
  by_contra hxB
  unfold buchbergerStep at hx
  rw [Finset.mem_union] at hx
  rcases hx with h | h
  · exact hxB h
  rw [mem_newRemainders] at h
  obtain ⟨hx0, b, hb, b', hb', hr⟩ := h
  have hxstep : x ∈ buchbergerStep m hB := by
    unfold buchbergerStep; rw [Finset.mem_union]; right
    rw [mem_newRemainders]; exact ⟨hx0, b, hb, b', hb', hr⟩
  have hmem : monomial (m.degree x) (1 : K) ∈ leadTermIdeal m (buchbergerStep m hB) :=
    Ideal.subset_span ⟨x, hxstep, rfl⟩
  rw [← heq, mem_leadTermIdeal] at hmem
  have hsupp : m.degree x ∈ (monomial (m.degree x) (1 : K)).support := by
    rw [mem_support_iff, coeff_monomial, if_pos rfl]; exact one_ne_zero
  obtain ⟨c, hc, hle⟩ := hmem (m.degree x) hsupp
  have hxsupp : m.degree x ∈ (remainder m hB (sPolynomial m b b')).support := by
    rw [hr]; exact degree_mem_support hx0
  exact (remainder_spec m hB (sPolynomial m b b')).2.2 (m.degree x) hxsupp c hc hle

/-- **Progress dichotomy, the fixed-point half**: if a Buchberger step does not change `B`,
every S-polynomial `S(b,b')` reduces to `0` (its remainder was not adjoined). -/
theorem remainder_sPolynomial_eq_zero_of_fixed {K : Type*} [Field K] (m : MonomialOrder σ)
    {B : Finset (MvPolynomial σ K)} (hB : ∀ b ∈ B, IsUnit (m.leadingCoeff b))
    (hfix : buchbergerStep m hB = B) {b b' : MvPolynomial σ K} (hb : b ∈ B) (hb' : b' ∈ B) :
    remainder m hB (sPolynomial m b b') = 0 := by
  classical
  by_contra hne
  have hmemstep : remainder m hB (sPolynomial m b b') ∈ buchbergerStep m hB := by
    unfold buchbergerStep; rw [Finset.mem_union]; right
    rw [mem_newRemainders]; exact ⟨hne, b, hb, b', hb', rfl⟩
  rw [hfix] at hmemstep
  exact (remainder_spec m hB (sPolynomial m b b')).2.2 _ (degree_mem_support hne) _ hmemstep le_rfl

/-- **A Buchberger fixed point is a Gröbner basis.** If a Buchberger step does not change `B`,
then `B` is a Gröbner basis of `Ideal.span ↑B`: every S-polynomial reduces to `0`, supplying the
standard-representation hypothesis of `isGroebnerBasis_of_sPolynomial_reducesToZero`. -/
theorem isGroebnerBasis_of_buchbergerStep_eq {K : Type*} [Field K] [Finite σ] (m : MonomialOrder σ)
    {B : Finset (MvPolynomial σ K)} (hB : ∀ b ∈ B, IsUnit (m.leadingCoeff b))
    (hfix : buchbergerStep m hB = B) :
    IsGroebnerBasis m (Ideal.span (↑B : Set (MvPolynomial σ K))) (↑B : Set (MvPolynomial σ K)) := by
  classical
  refine isGroebnerBasis_of_sPolynomial_reducesToZero _ B (fun b hb => Ideal.subset_span hb)
    hB rfl (fun b hb b' hb' => ?_)
  have hrem0 := remainder_sPolynomial_eq_zero_of_fixed m hB hfix hb hb'
  have hspec := remainder_spec m hB (sPolynomial m b b')
  have heq : sPolynomial m b b' = ∑ c ∈ B.attach,
      (divData m hB (sPolynomial m b b')).1 c * (c : MvPolynomial σ K) := by
    rw [← linearCombination_eq_attach_sum]
    have := hspec.1; rw [hrem0, add_zero] at this; exact this
  refine ⟨fun c => (divData m hB (sPolynomial m b b')).1 c, heq, fun c => ?_⟩
  have := hspec.2.1 c
  rwa [mul_comm] at this

/-- **Buchberger's algorithm terminates and is correct.** Over a field with finitely many
variables, iterating `buchbergerStep` from any finite `B` (with unit leading coefficients)
reaches a Gröbner basis `G ⊇ B` of `Ideal.span ↑B` with the same span. Termination is the
Noetherian ascending-chain condition (`WellFoundedGT` on the leading-term ideals): each step
either fixes `B` (a Gröbner basis) or strictly grows `leadTermIdeal`, which cannot happen
forever. -/
theorem buchberger_terminates_correct {K : Type*} [Field K] [Finite σ] (m : MonomialOrder σ)
    {B : Finset (MvPolynomial σ K)} (hB : ∀ b ∈ B, IsUnit (m.leadingCoeff b)) :
    ∃ G : Finset (MvPolynomial σ K), (↑B : Set (MvPolynomial σ K)) ⊆ ↑G ∧
      Ideal.span (↑G : Set (MvPolynomial σ K)) = Ideal.span (↑B : Set (MvPolynomial σ K)) ∧
      IsGroebnerBasis m (Ideal.span (↑B : Set (MvPolynomial σ K))) (↑G : Set (MvPolynomial σ K)) := by
  classical
  -- Well-founded recursion on the leading-term ideal: every basis with a strictly-larger
  -- leading-term ideal reaches a Gröbner basis, hence so does this one.
  suffices H : ∀ J : Ideal (MvPolynomial σ K), ∀ C : Finset (MvPolynomial σ K),
      ∀ hC : (∀ c ∈ C, IsUnit (m.leadingCoeff c)), leadTermIdeal m C = J →
      ∃ G : Finset (MvPolynomial σ K), (↑C : Set (MvPolynomial σ K)) ⊆ ↑G ∧
        Ideal.span (↑G : Set (MvPolynomial σ K)) = Ideal.span (↑C : Set (MvPolynomial σ K)) ∧
        IsGroebnerBasis m (Ideal.span (↑C : Set (MvPolynomial σ K))) (↑G : Set (MvPolynomial σ K)) by
    exact H (leadTermIdeal m B) B hB rfl
  intro J
  induction J using WellFoundedGT.induction with
  | _ J ih =>
    intro C hC hCJ
    by_cases hfix : buchbergerStep m hC = C
    · -- fixed point: C itself is a Gröbner basis
      exact ⟨C, subset_refl _, rfl, isGroebnerBasis_of_buchbergerStep_eq m hC hfix⟩
    · -- strict growth: recurse on the (larger) leading-term ideal of the step
      have hlt : leadTermIdeal m C < leadTermIdeal m (buchbergerStep m hC) :=
        leadTermIdeal_lt_of_ne m hC hfix
      obtain ⟨G, hCG, hspanG, hgb⟩ :=
        ih (leadTermIdeal m (buchbergerStep m hC))
          (hCJ ▸ hlt)
          (buchbergerStep m hC)
          (fun c hc => isUnit_leadingCoeff_of_mem_buchbergerStep m hC hc) rfl
      -- transport the conclusion back across the span-preserving step
      have hspaneq := span_buchbergerStep m hC
      refine ⟨G, (subset_buchbergerStep m hC).trans hCG, by rw [hspanG, hspaneq], ?_⟩
      rwa [hspaneq] at hgb

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

/-- If `g ≠ 0` and no `m.degree b` (`b ∈ B'`) divides `m.degree g`, then
`(remainder m hB' g).coeff (m.degree g) = m.leadingCoeff g`: division leaves the leading term intact. -/
theorem coeff_remainder_degree_eq {K : Type*} [Field K] (m : MonomialOrder σ)
    {B' : Finset (MvPolynomial σ K)} (hB' : ∀ b ∈ B', IsUnit (m.leadingCoeff b))
    {g : MvPolynomial σ K}
    (hnd : ∀ b ∈ (↑B' : Set (MvPolynomial σ K)), ¬ (m.degree b ≤ m.degree g)) :
    (remainder m hB' g).coeff (m.degree g) = m.leadingCoeff g := by
  classical
  have hspec := remainder_spec m hB' g
  -- `g = q + r` with `q = ∑ b·g_b`, each `m.degree (b·g_b) ≼[m] m.degree g`.
  have hgqr : g = Finsupp.linearCombination _
      (fun (b : (↑B' : Set (MvPolynomial σ K))) => (b : MvPolynomial σ K)) (divData m hB' g).1
      + remainder m hB' g := hspec.1
  -- the `m.degree g`-coefficient of every summand `b·g_b` vanishes.
  have hqcoeff : (Finsupp.linearCombination _
      (fun (b : (↑B' : Set (MvPolynomial σ K))) => (b : MvPolynomial σ K))
        (divData m hB' g).1).coeff (m.degree g) = 0 := by
    rw [linearCombination_eq_attach_sum, coeff_sum]
    refine Finset.sum_eq_zero (fun c _ => ?_)
    have hcle : m.toSyn (m.degree ((divData m hB' g).1 c * (c : MvPolynomial σ K)))
        ≤ m.toSyn (m.degree g) := by
      have := hspec.2.1 c; rwa [mul_comm] at this
    by_cases hz : (divData m hB' g).1 c * (c : MvPolynomial σ K) = 0
    · rw [hz, coeff_zero]
    rcases lt_or_eq_of_le hcle with hlt | heq
    · exact coeff_eq_zero_of_lt hlt
    · -- equality of degrees would force `m.degree c ≤ m.degree g`, contradicting `hnd`.
      exfalso
      have hdegeq : m.degree ((divData m hB' g).1 c * (c : MvPolynomial σ K)) = m.degree g :=
        m.toSyn.injective heq
      have hdle : m.degree (c : MvPolynomial σ K)
          ≤ m.degree ((divData m hB' g).1 c * (c : MvPolynomial σ K)) :=
        degree_le_degree_mul hz
      exact hnd c c.2 (hdegeq ▸ hdle)
  -- hence `r.coeff (m.degree g) = g.coeff (m.degree g) = lc g`.
  have hgc : (remainder m hB' g).coeff (m.degree g) = g.coeff (m.degree g) := by
    have := congrArg (fun p => MvPolynomial.coeff (m.degree g) p) hgqr
    simp only [coeff_add, hqcoeff, zero_add] at this
    exact this.symm
  rw [hgc, ← MonomialOrder.leadingCoeff]

/-- Under the hypotheses of `coeff_remainder_degree_eq`, the remainder is nonzero and has the same
leading monomial and leading coefficient as `g`. -/
theorem degree_remainder_eq {K : Type*} [Field K] (m : MonomialOrder σ)
    {B' : Finset (MvPolynomial σ K)} (hB' : ∀ b ∈ B', IsUnit (m.leadingCoeff b))
    {g : MvPolynomial σ K} (hg : g ≠ 0)
    (hnd : ∀ b ∈ (↑B' : Set (MvPolynomial σ K)), ¬ (m.degree b ≤ m.degree g)) :
    remainder m hB' g ≠ 0 ∧ m.degree (remainder m hB' g) = m.degree g ∧
      m.leadingCoeff (remainder m hB' g) = m.leadingCoeff g := by
  classical
  have hcoeff := coeff_remainder_degree_eq m hB' hnd
  have hlcg : m.leadingCoeff g ≠ 0 := m.leadingCoeff_ne_zero_iff.mpr hg
  have hspec := remainder_spec m hB' g
  -- `m.degree (remainder) ≼[m] m.degree g` from `g = q + r` and `degree_sub_le`.
  have hrle : m.toSyn (m.degree (remainder m hB' g)) ≤ m.toSyn (m.degree g) := by
    have hreq : remainder m hB' g = g - Finsupp.linearCombination _
        (fun (b : (↑B' : Set (MvPolynomial σ K))) => (b : MvPolynomial σ K)) (divData m hB' g).1 := by
      rw [eq_sub_iff_add_eq, add_comm]; exact hspec.1.symm
    rw [hreq]
    refine degree_sub_le.trans ?_
    rw [sup_le_iff]
    refine ⟨le_rfl, ?_⟩
    rw [linearCombination_eq_attach_sum]
    refine (degree_sum_le).trans (Finset.sup_le (fun c _ => ?_))
    have := hspec.2.1 c; rwa [mul_comm] at this
  -- `m.degree g ∈ remainder.support` (its coeff there is `lc g ≠ 0`).
  have hmem : m.degree g ∈ (remainder m hB' g).support := by
    rw [mem_support_iff, hcoeff]; exact hlcg
  have hne : remainder m hB' g ≠ 0 := by
    intro h0; rw [h0, support_zero] at hmem; exact absurd hmem (Finset.notMem_empty _)
  -- degree equality from the two-sided bound.
  have hge : m.toSyn (m.degree g) ≤ m.toSyn (m.degree (remainder m hB' g)) := m.le_degree hmem
  have hdeg : m.degree (remainder m hB' g) = m.degree g := m.toSyn.injective (le_antisymm hrle hge)
  refine ⟨hne, hdeg, ?_⟩
  rw [MonomialOrder.leadingCoeff, hdeg, hcoeff, MonomialOrder.leadingCoeff]

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

open Classical in
/-- Leading coefficients of `B.erase g` are units when those of `B` are. -/
theorem isUnit_leadingCoeff_erase {K : Type*} [Field K] (m : MonomialOrder σ)
    {B : Finset (MvPolynomial σ K)} (hBu : ∀ b ∈ B, IsUnit (m.leadingCoeff b))
    (g : MvPolynomial σ K) : ∀ b ∈ B.erase g, IsUnit (m.leadingCoeff b) := by
  classical
  intro b hb; exact hBu b (Finset.mem_of_mem_erase hb)

open Classical in
/-- Auto-reduction of one element: the remainder of `g` on division by the other elements
`B.erase g`. -/
noncomputable def autoReduceElt {K : Type*} [Field K] (m : MonomialOrder σ)
    {B : Finset (MvPolynomial σ K)} (hBu : ∀ b ∈ B, IsUnit (m.leadingCoeff b))
    (g : MvPolynomial σ K) : MvPolynomial σ K :=
  remainder m (isUnit_leadingCoeff_erase m hBu g) g

open Classical in
/-- When `g`'s leading monomial is divided by no other element's, `autoReduceElt` is nonzero,
degree-preserving, and preserves the leading coefficient. -/
theorem autoReduceElt_spec {K : Type*} [Field K] (m : MonomialOrder σ)
    {B : Finset (MvPolynomial σ K)} (hBu : ∀ b ∈ B, IsUnit (m.leadingCoeff b))
    {g : MvPolynomial σ K} (hg : g ≠ 0)
    (hnd : ∀ h ∈ B.erase g, ¬ (m.degree h ≤ m.degree g)) :
    autoReduceElt m hBu g ≠ 0 ∧ m.degree (autoReduceElt m hBu g) = m.degree g ∧
      m.leadingCoeff (autoReduceElt m hBu g) = m.leadingCoeff g := by
  classical
  refine degree_remainder_eq m (isUnit_leadingCoeff_erase m hBu g) hg ?_
  intro b hb; exact hnd b (Finset.mem_coe.mp hb)

open Classical in
/-- No support monomial of `autoReduceElt m hBu g` is divisible by the leading monomial of another
element `h ∈ B.erase g`. -/
theorem autoReduceElt_reduced {K : Type*} [Field K] (m : MonomialOrder σ)
    {B : Finset (MvPolynomial σ K)} (hBu : ∀ b ∈ B, IsUnit (m.leadingCoeff b))
    (g : MvPolynomial σ K) {c : σ →₀ ℕ} (hc : c ∈ (autoReduceElt m hBu g).support)
    {h : MvPolynomial σ K} (hh : h ∈ B.erase g) : ¬ (m.degree h ≤ c) :=
  (remainder_spec m (isUnit_leadingCoeff_erase m hBu g) g).2.2 c hc h (Finset.mem_coe.mpr hh)

/-- `g - autoReduceElt m hBu g ∈ span (B.erase g) ⊆ span B`, so `autoReduceElt` keeps `g ∈ I`. -/
theorem sub_autoReduceElt_mem_span {K : Type*} [Field K] (m : MonomialOrder σ)
    {B : Finset (MvPolynomial σ K)} (hBu : ∀ b ∈ B, IsUnit (m.leadingCoeff b))
    (g : MvPolynomial σ K) :
    g - autoReduceElt m hBu g ∈ Ideal.span (↑B : Set (MvPolynomial σ K)) := by
  classical
  have hmem := sub_remainder_mem_span m (isUnit_leadingCoeff_erase m hBu g) g
  have hle : Ideal.span (↑(B.erase g) : Set (MvPolynomial σ K))
      ≤ Ideal.span (↑B : Set (MvPolynomial σ K)) :=
    Ideal.span_mono (fun x hx => Finset.mem_coe.mpr (Finset.mem_of_mem_erase (Finset.mem_coe.mp hx)))
  exact hle hmem

open Classical in
/-- Auto-reduction of a basis: replace each `g ∈ B` by its remainder on division by the other
elements. -/
noncomputable def autoReduce {K : Type*} [Field K] (m : MonomialOrder σ)
    {B : Finset (MvPolynomial σ K)} (hBu : ∀ b ∈ B, IsUnit (m.leadingCoeff b)) :
    Finset (MvPolynomial σ K) :=
  B.attach.image (fun g => autoReduceElt m hBu g.1)

open Classical in
/-- Membership in `autoReduce m hBu`: `x = autoReduceElt m hBu g` for some `g ∈ B`. -/
theorem mem_autoReduce {K : Type*} [Field K] (m : MonomialOrder σ)
    {B : Finset (MvPolynomial σ K)} (hBu : ∀ b ∈ B, IsUnit (m.leadingCoeff b))
    {x : MvPolynomial σ K} :
    x ∈ autoReduce m hBu ↔ ∃ g ∈ B, autoReduceElt m hBu g = x := by
  classical
  unfold autoReduce
  rw [Finset.mem_image]
  constructor
  · rintro ⟨g, _, rfl⟩; exact ⟨g.1, g.2, rfl⟩
  · rintro ⟨g, hg, rfl⟩; exact ⟨⟨g, hg⟩, Finset.mem_attach _ _, rfl⟩

/-- Auto-reducing a monic Gröbner basis of `I` with pairwise non-dividing leading monomials gives a
reduced Gröbner basis of `I`. -/
theorem isReducedGroebnerBasis_autoReduce {K : Type*} [Field K] [Finite σ]
    {I : Ideal (MvPolynomial σ K)} {B : Finset (MvPolynomial σ K)}
    (hBu : ∀ b ∈ B, IsUnit (m.leadingCoeff b))
    (hB : IsGroebnerBasis m I (↑B : Set (MvPolynomial σ K)))
    (hmonic : ∀ b ∈ (↑B : Set (MvPolynomial σ K)), m.leadingCoeff b = 1)
    (hpair : ∀ b ∈ (↑B : Set (MvPolynomial σ K)), ∀ b' ∈ (↑B : Set (MvPolynomial σ K)),
      b ≠ b' → ¬ (m.degree b' ≤ m.degree b)) :
    IsReducedGroebnerBasis m I (↑(autoReduce m hBu) : Set (MvPolynomial σ K)) := by
  classical
  -- For each `g ∈ B`, the other leading monomials don't divide `m.degree g`.
  have hnd : ∀ g ∈ B, ∀ h ∈ B.erase g, ¬ (m.degree h ≤ m.degree g) := by
    intro g hg h hh
    have hhB : h ∈ B := Finset.mem_of_mem_erase hh
    have hhg : h ≠ g := Finset.ne_of_mem_erase hh
    exact hpair g (Finset.mem_coe.mpr hg) h (Finset.mem_coe.mpr hhB) (fun he => hhg he.symm)
  -- `g ≠ 0` for every `g ∈ B`.
  have hg0 : ∀ g ∈ B, g ≠ 0 := fun g hg => m.leadingCoeff_ne_zero_iff.mp
    (by rw [hmonic g (Finset.mem_coe.mpr hg)]; exact one_ne_zero)
  -- per-element spec of `autoReduceElt`.
  have hspec : ∀ g ∈ B, autoReduceElt m hBu g ≠ 0 ∧
      m.degree (autoReduceElt m hBu g) = m.degree g ∧
      m.leadingCoeff (autoReduceElt m hBu g) = m.leadingCoeff g :=
    fun g hg => autoReduceElt_spec m hBu (hg0 g hg) (hnd g hg)
  -- the auto-reduced map is degree-injective enough: `autoReduceElt g = autoReduceElt g'` ⟹ same degree.
  -- (1) membership in `I`.
  have hsubI : ∀ b ∈ (↑(autoReduce m hBu) : Set (MvPolynomial σ K)), b ∈ I := by
    intro b hb
    obtain ⟨g, hg, rfl⟩ := (mem_autoReduce m hBu).mp (Finset.mem_coe.mp hb)
    have : autoReduceElt m hBu g = g - (g - autoReduceElt m hBu g) := by ring
    rw [this]
    exact I.sub_mem (hB.1 g (Finset.mem_coe.mpr hg))
      (hB.span_eq ▸ sub_autoReduceElt_mem_span m hBu g)
  -- (2) monic.
  have hmonic' : ∀ b ∈ (↑(autoReduce m hBu) : Set (MvPolynomial σ K)), m.leadingCoeff b = 1 := by
    intro b hb
    obtain ⟨g, hg, rfl⟩ := (mem_autoReduce m hBu).mp (Finset.mem_coe.mp hb)
    rw [(hspec g hg).2.2, hmonic g (Finset.mem_coe.mpr hg)]
  have hlc' : ∀ b ∈ (↑(autoReduce m hBu) : Set (MvPolynomial σ K)), IsUnit (m.leadingCoeff b) :=
    fun b hb => by rw [hmonic' b hb]; exact isUnit_one
  -- (3) the leading-monomial-degree set is preserved.
  have hdegimg : m.degree '' (↑(autoReduce m hBu) : Set (MvPolynomial σ K))
      = m.degree '' (↑B : Set (MvPolynomial σ K)) := by
    ext s
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨g, hg, rfl⟩ := (mem_autoReduce m hBu).mp (Finset.mem_coe.mp hx)
      exact ⟨g, Finset.mem_coe.mpr hg, (hspec g hg).2.1.symm⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨autoReduceElt m hBu g, Finset.mem_coe.mpr ((mem_autoReduce m hBu).mpr
        ⟨g, Finset.mem_coe.mp hg, rfl⟩), (hspec g (Finset.mem_coe.mp hg)).2.1⟩
  have hltideal : leadTermIdeal m (autoReduce m hBu) = leadTermIdeal m B := by
    unfold leadTermIdeal
    rw [show (fun b => monomial (m.degree b) (1 : K)) '' (↑(autoReduce m hBu) : Set (MvPolynomial σ K))
        = (fun s => monomial s (1 : K)) '' (m.degree '' (↑(autoReduce m hBu) : Set (MvPolynomial σ K))) by
      rw [Set.image_image],
      show (fun b => monomial (m.degree b) (1 : K)) '' (↑B : Set (MvPolynomial σ K))
        = (fun s => monomial s (1 : K)) '' (m.degree '' (↑B : Set (MvPolynomial σ K))) by
      rw [Set.image_image], hdegimg]
  have hgb : IsGroebnerBasis m I (↑(autoReduce m hBu) : Set (MvPolynomial σ K)) := by
    rw [isGroebnerBasis_iff_leadTermIdeal_eq hsubI hlc', hltideal,
      ← hB.initialIdeal_eq_leadTermIdeal]
  -- (4) the reduced property.
  refine ⟨hgb, hmonic', fun b hb b' hb' hbb' c hc => ?_⟩
  obtain ⟨g, hg, rfl⟩ := (mem_autoReduce m hBu).mp (Finset.mem_coe.mp hb)
  obtain ⟨g', hg', rfl⟩ := (mem_autoReduce m hBu).mp (Finset.mem_coe.mp hb')
  -- distinct reduced elements come from distinct `g ≠ g'`.
  have hgg' : g' ≠ g := by
    intro he; exact hbb' (by rw [he])
  have hg'erase : g' ∈ B.erase g := Finset.mem_erase.mpr ⟨hgg', hg'⟩
  rw [(hspec g' hg').2.1]
  exact autoReduceElt_reduced m hBu g hc hg'erase

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
theorem lazard_lemma1 {K : Type*} [Field K] {m : MonomialOrder (Fin 2)}
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
theorem lazard_lemma1_injOn {K : Type*} [Field K] {m : MonomialOrder (Fin 2)}
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis m I (↑B : Set (MvPolynomial (Fin 2) K))) :
    Set.InjOn (fun b => (m.degree b) 1) (↑B : Set (MvPolynomial (Fin 2) K)) := by
  intro b hb b' hb' hyeq
  by_contra hne
  exact lazard_lemma1 hB b hb b' hb' hne hyeq

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

-- Restatements against the intended wording.
example {d d' : Fin 2 →₀ ℕ} (h : d 1 = d' 1) : d ≤ d' ∨ d' ≤ d :=
  finsupp_fin_two_le_or_le_of_apply_eq h

example {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K} (hf : f ≠ 0) :
    (MonomialOrder.lex.degree f) 0 = degreeOf 0 f :=
  lex_degree_apply_zero hf

example {K : Type*} [Field K] (f : MvPolynomial (Fin 2) K) :
    (lazardView f).natDegree = degreeOf 0 f :=
  natDegree_lazardView f

example {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K} :
    leadingYCoeff f ≠ 0 ↔ f ≠ 0 :=
  leadingYCoeff_ne_zero

example {K : Type*} [Field K] (f g : MvPolynomial (Fin 2) K) :
    leadingYCoeff (f * g) = leadingYCoeff f * leadingYCoeff g :=
  leadingYCoeff_mul f g

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

example {K : Type*} [Field K] {I : Ideal (MvPolynomial σ K)} {B : Set (MvPolynomial σ K)}
    (hB : IsReducedGroebnerBasis m I B) {b b' : MvPolynomial σ K} (hb : b ∈ B) (hb' : b' ∈ B)
    (hne : b ≠ b') : ¬ (m.degree b' ≤ m.degree b) :=
  hB.leadingMonomial_not_le hb hb' hne

example {K : Type*} [Field K] {m : MonomialOrder (Fin 2)}
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis m I (↑B : Set (MvPolynomial (Fin 2) K))) :
    ∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → (m.degree b) 1 ≠ (m.degree b') 1 :=
  lazard_lemma1 hB

example {K : Type*} [Field K] (k : ℕ) {f : MvPolynomial (Fin 2) K} (hf : f ≠ 0) :
    degreeOf 0 (X 0 ^ k * f) = degreeOf 0 f + k :=
  degreeOf_X_pow_mul k hf

example {K : Type*} [Field K] (k : ℕ) (f : MvPolynomial (Fin 2) K) :
    leadingYCoeff (X 0 ^ k * f) = leadingYCoeff f :=
  leadingYCoeff_X_pow_mul k f

/-! ## GCD / Bézout structure on the leading-`y`-coefficient ring `MvPolynomial (Fin 1) K`

A chosen `GCDMonoid` and Bézout identity on `MvPolynomial (Fin 1) K ≃ K[x]` (a PID), transferred
from `K[x]`. Provided as local `letI` instances, not global (to avoid diamonds). -/

open scoped Classical in
/-- The ring equivalence `MvPolynomial (Fin 1) K ≃+* K[x]`: pull out the single variable
(`finSuccEquiv K 0`), then erase the now-empty inner `MvPolynomial (Fin 0) K ≃ K`. -/
noncomputable def mvPolynomialFinOneEquivPolynomial (K : Type*) [Field K] :
    MvPolynomial (Fin 1) K ≃+* Polynomial K :=
  ((finSuccEquiv K 0).trans (Polynomial.mapAlgEquiv (isEmptyAlgEquiv K (Fin 0)))).toRingEquiv

open scoped Classical in
/-- A chosen `GCDMonoid` on `MvPolynomial (Fin 1) K` (UFD `⟹` GCD domain). Used as a local
`letI`; not a global instance. -/
@[reducible] noncomputable def gcdMonoidMvPolynomialFinOne (K : Type*) [Field K] :
    GCDMonoid (MvPolynomial (Fin 1) K) :=
  UniqueFactorizationMonoid.toGCDMonoid _

/-- `MvPolynomial (Fin 1) K` is a Bézout ring (transfer `K[x]`'s `IsBezout` through the surjective
`mvPolynomialFinOneEquivPolynomial.symm`). Used as a local `letI`; not a global instance. -/
@[reducible] noncomputable def isBezoutMvPolynomialFinOne (K : Type*) [Field K] :
    IsBezout (MvPolynomial (Fin 1) K) :=
  Function.Surjective.isBezout (mvPolynomialFinOneEquivPolynomial K).symm.toRingHom
    (mvPolynomialFinOneEquivPolynomial K).symm.surjective

open scoped Classical in
/-- Bézout's identity: there are `a, b` with `a·g + b·g' = gcd g g'` in `MvPolynomial (Fin 1) K`. -/
theorem exists_mul_add_mul_eq_gcd {K : Type*} [Field K] (g g' : MvPolynomial (Fin 1) K) :
    ∃ a b : MvPolynomial (Fin 1) K,
      a * g + b * g' = @gcd _ _ (gcdMonoidMvPolynomialFinOne K) g g' := by
  letI := gcdMonoidMvPolynomialFinOne K
  letI := isBezoutMvPolynomialFinOne K
  have hdvd : @gcd _ _ (gcdMonoidMvPolynomialFinOne K) g g' ∣ gcd g g' := dvd_refl _
  rw [gcd_dvd_iff_exists] at hdvd
  obtain ⟨a, b, hab⟩ := hdvd
  exact ⟨a, b, by rw [hab]; ring⟩

/-- `gcd g g' ∣ g` (left) for the chosen `GCDMonoid` on `MvPolynomial (Fin 1) K`. -/
theorem gcd_dvd_left_mvPolynomialFinOne {K : Type*} [Field K] (g g' : MvPolynomial (Fin 1) K) :
    @gcd _ _ (gcdMonoidMvPolynomialFinOne K) g g' ∣ g :=
  letI := gcdMonoidMvPolynomialFinOne K
  gcd_dvd_left g g'

/-- `gcd g g' ∣ g'` (right) for the chosen `GCDMonoid` on `MvPolynomial (Fin 1) K`. -/
theorem gcd_dvd_right_mvPolynomialFinOne {K : Type*} [Field K] (g g' : MvPolynomial (Fin 1) K) :
    @gcd _ _ (gcdMonoidMvPolynomialFinOne K) g g' ∣ g' :=
  letI := gcdMonoidMvPolynomialFinOne K
  gcd_dvd_right g g'

/-- `natDegree (e r) = degreeOf 0 r` for `e = mvPolynomialFinOneEquivPolynomial K`. -/
theorem natDegree_mvPolynomialFinOneEquivPolynomial {K : Type*} [Field K]
    (r : MvPolynomial (Fin 1) K) :
    (mvPolynomialFinOneEquivPolynomial K r).natDegree = degreeOf 0 r := by
  rw [mvPolynomialFinOneEquivPolynomial]
  show (Polynomial.mapAlgEquiv (isEmptyAlgEquiv K (Fin 0)) (finSuccEquiv K 0 r)).natDegree = _
  rw [Polynomial.coe_mapAlgEquiv, ← natDegree_finSuccEquiv r]
  apply Polynomial.natDegree_map_eq_of_injective
  exact EquivLike.injective (isEmptyAlgEquiv K (Fin 0))

/-- On `MvPolynomial (Fin 1) K`, `p ∣ q` and `q ≠ 0` imply `degreeOf 0 p ≤ degreeOf 0 q`. -/
theorem degreeOf_le_of_dvd {K : Type*} [Field K] {p q : MvPolynomial (Fin 1) K}
    (hpq : p ∣ q) (hq : q ≠ 0) : degreeOf 0 p ≤ degreeOf 0 q := by
  set e := mvPolynomialFinOneEquivPolynomial K with he
  rw [← natDegree_mvPolynomialFinOneEquivPolynomial, ← natDegree_mvPolynomialFinOneEquivPolynomial]
  refine Polynomial.natDegree_le_of_dvd (map_dvd e hpq) ?_
  rwa [Ne, map_eq_zero_iff _ e.injective]

/-- On `MvPolynomial (Fin 1) K`, if `p ∣ q`, `q ≠ 0` and `degreeOf 0 q ≤ degreeOf 0 p`, then
`q ∣ p`. -/
theorem dvd_of_dvd_of_degreeOf_le {K : Type*} [Field K] {p q : MvPolynomial (Fin 1) K}
    (hpq : p ∣ q) (hq : q ≠ 0) (hdeg : degreeOf 0 q ≤ degreeOf 0 p) : q ∣ p := by
  set e := mvPolynomialFinOneEquivPolynomial K with he
  have heq : e p ∣ e q := map_dvd e hpq
  have hq' : e q ≠ 0 := by rwa [Ne, map_eq_zero_iff _ e.injective]
  rw [← natDegree_mvPolynomialFinOneEquivPolynomial, ← natDegree_mvPolynomialFinOneEquivPolynomial]
    at hdeg
  have hassoc : Associated (e p) (e q) :=
    Polynomial.associated_of_dvd_of_natDegree_le heq hq' hdeg
  have h2 : e q ∣ e p := hassoc.symm.dvd
  have h3 : e.symm (e q) ∣ e.symm (e p) := map_dvd e.symm h2
  rwa [e.symm_apply_apply, e.symm_apply_apply] at h3

-- Restatements against the intended wording.
noncomputable example {K : Type*} [Field K] : MvPolynomial (Fin 1) K ≃+* Polynomial K :=
  mvPolynomialFinOneEquivPolynomial K

example {K : Type*} [Field K] (g g' : MvPolynomial (Fin 1) K) :
    ∃ a b : MvPolynomial (Fin 1) K,
      a * g + b * g' = @gcd _ _ (gcdMonoidMvPolynomialFinOne K) g g' :=
  exists_mul_add_mul_eq_gcd g g'

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
    congr 1
    rw [← hfsdeg, ← natDegree_lazardView, Polynomial.coeff_natDegree, ← hfslc]; rfl
  have hqcoeff : q.coeff d = b * gi1 := by
    rw [hq_def, Polynomial.coeff_C_mul]
    congr 1
    rw [hd_def, ← natDegree_lazardView, Polynomial.coeff_natDegree]; rfl
  have hsum_ne : p.coeff d + q.coeff d ≠ 0 := by rw [hpcoeff, hqcoeff, hab]; exact hgcd_ne
  obtain ⟨hPdeg, hPlc⟩ := natDegree_leadingCoeff_add hpdeg hqdeg hsum_ne
  rw [← hlazP] at hPdeg hPlc
  exact ⟨P, hPI, by rw [← natDegree_lazardView, hPdeg],
    by rw [leadingYCoeff, hPlc, hpcoeff, hqcoeff, hab]⟩

/-- Under `MonomialOrder.lex` on `Fin 2` with `f ≠ 0`, the index-`1` exponent of the leading
monomial is the `x`-degree `degreeOf 0 (leadingYCoeff f)` of the leading-`y`-coefficient. -/
theorem lex_degree_apply_one {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K} (hf : f ≠ 0) :
    (MonomialOrder.lex.degree f) 1 = degreeOf 0 (leadingYCoeff f) := by
  classical
  set δ := MonomialOrder.lex.degree f with hδ
  have hδ0 : δ 0 = degreeOf 0 f := lex_degree_apply_zero hf
  have hlyc : leadingYCoeff f = (lazardView f).coeff (degreeOf 0 f) := by
    rw [leadingYCoeff, Polynomial.leadingCoeff, natDegree_lazardView]
  have hsucc : (1 : Fin 2) = (0 : Fin 1).succ := rfl
  apply le_antisymm
  · -- `δ 1 ≤ deg_x`: `δ = (tail δ).cons (δ 0)`, and `tail δ ∈ support (leadingYCoeff f)`.
    have hδmem : δ ∈ f.support := MonomialOrder.degree_mem_support hf
    set mon' : Fin 1 →₀ ℕ := Finsupp.tail δ with hmon'
    have hcons : Finsupp.cons (δ 0) mon' = δ := by rw [hmon', Finsupp.cons_tail]
    have hmem' : mon' ∈ (leadingYCoeff f).support := by
      rw [hlyc, lazardView, mem_support_coeff_finSuccEquiv, ← hδ0, hcons]; exact hδmem
    have hval : mon' 0 = δ 1 := by rw [hmon', Finsupp.tail_apply, hsucc]
    rw [← hval, degreeOf_eq_sup]
    exact Finset.le_sup (f := fun s : Fin 1 →₀ ℕ => s 0) hmem'
  · -- `deg_x ≤ δ 1`: each `mon ∈ support (leadingYCoeff f)` gives `mon.cons (δ 0) ≼[lex] δ`.
    rw [degreeOf_eq_sup]
    apply Finset.sup_le
    intro mon hmon
    rw [hlyc, lazardView, mem_support_coeff_finSuccEquiv, ← hδ0] at hmon
    have hle : (Finsupp.cons (δ 0) mon) ≼[MonomialOrder.lex] δ := MonomialOrder.le_degree hmon
    rw [MonomialOrder.lex_le_iff] at hle
    have h0eq : (Finsupp.cons (δ 0) mon) 0 = δ 0 := Finsupp.cons_zero _ _
    have hmain := apply_one_le_of_toLex_le_of_apply_zero_eq hle h0eq
    have hcons1 : (Finsupp.cons (δ 0) mon) 1 = mon 0 := by rw [hsucc, Finsupp.cons_succ]
    rwa [hcons1] at hmain

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
example {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K} (hf : f ≠ 0) :
    (MonomialOrder.lex.degree f) 1 = degreeOf 0 (leadingYCoeff f) :=
  lex_degree_apply_one hf

example {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    {fi fi1 : MvPolynomial (Fin 2) K} (hfi : fi ∈ B) (hfi1 : fi1 ∈ B)
    (hd : degreeOf 0 fi < degreeOf 0 fi1) :
    leadingYCoeff fi1 ∣ leadingYCoeff fi :=
  lazard_lemma2 hB hfi hfi1 hd

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

-- Restatements against the intended wording.
example {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K))) :
    ∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → degreeOf 0 b ≠ degreeOf 0 b' :=
  lazard_degreeOf_ne hB

example {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (i : Fin B.card) : sortedByYDegree hB i ∈ B :=
  sortedByYDegree_mem hB i

example {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K))) :
    StrictMono (fun i => degreeOf 0 (sortedByYDegree hB i)) :=
  degreeOf_sortedByYDegree_strictMono hB

example {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K))) :
    Set.range (sortedByYDegree hB) = (↑B : Set (MvPolynomial (Fin 2) K)) :=
  range_sortedByYDegree hB

/-! ## The reduction step and the `Pₖ = Rₖ·Sₖ` split

The reduction step: with `q = gᵢ/g_{i+1}`, the ideal element `yConst q·f_{i+1} − y^{shift}·fᵢ` has
`y`-degree `< d_{i+1}` (leading terms cancel). The `Pₖ = Rₖ·Sₖ` split: given `gᵢ ∣ fᵢ`, the content
of `lazardView fᵢ` is associated to `Rᵢ = leadingYCoeff fᵢ` and the primitive part `Sᵢ` is
monic-in-`y`. -/

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

/-! ## Lazard's Lemma 3: the full descent in the no-common-factor case

Lazard (1985), Theorem 1 proof + Lemma 3 (p.262–263). The descent `C(gᵢ) ∣ lazardView fᵢ`
("`gᵢ ∣ fᵢ`") is proved by **upward** induction over the `y`-degree-sorted enumeration, in the
strengthened form `P(i) : ∀ j ≤ i, C(gᵢ) ∣ lazardView (sorted j)`. The step `i → i+1` is
non-circular: with `q = gᵢ/g_{i+1}` the reduction element `R = yConst q · f_{i+1} − y^{shift}·fᵢ`
has `y`-degree `< d(i+1)`, so its GB-reduction uses only lower elements `sorted j (j ≤ i)`, all
divisible by `C(gᵢ)` by the IH; hence `C(gᵢ) ∣ lazardView R`. The IH also gives `C(gᵢ) ∣ lazardView
fᵢ`, so from `C q · lazardView f_{i+1} = lazardView R + X^{shift}·lazardView fᵢ` one gets
`C(gᵢ) ∣ C q · lazardView f_{i+1}`; since `C(gᵢ) = C(g_{i+1})·C(q)`, cancelling `C(q)` yields
`C(g_{i+1}) ∣ lazardView f_{i+1}` — the goal at `i+1`, **without** using `g_{i+1} ∣ f_{i+1}` itself.

The descent's **base** `P(0) : C(g₀) ∣ lazardView f₀` is where Lazard's "divide out the common
content" enters: it is equivalent to `f₀ ∈ K[x]` (`degreeOf 0 f₀ = 0`), which holds precisely after
dividing the basis by `primpart(gcd) · content(gcd)` so the `fᵢ` have no common factor — recorded
as the hypothesis `hbase`. -/

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

/-- **The non-circular descent step** (Lazard 1985, p.263, Lemma 3 induction `i → i+1`). Let
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

/-! ## Part A: the common factor of the basis (Lazard's `P·Gₖ₊₁`) and the no-common-factor base

Lazard (1985), Theorem 1 proof (p.262): the basis may be divided by `P·Gₖ₊₁` where
`P = primpart(gcd(f₀,…,fₖ))` (the `y`-**primitive part**, a `K[x][y]` polynomial carrying the
`y`-dependence) and `Gₖ₊₁ = content(gcd(f₀,…,fₖ))` (a `K[x]` polynomial), to reduce to the
**no-common-factor** case where `P = Gₖ₊₁ = 1`. *Both* factors must be divided out for the base
`f₀ ∈ K[x]` of the Lemma 3 descent.

Two layers, with **different** scope:
* The `K[x]`-layer `Gₖ₊₁` has a clean closed form: since the higher-`y`-degree `g_j` divides every
  lower `gᵢ` (`leadingYCoeff_sortedByYDegree_dvd_of_le`), the **top** `gₖ = leadingYCoeff (sorted
  top)` divides *all* `gᵢ`, so up to associates `Gₖ₊₁ ∼ gₖ` — recorded as `gbCommonContent` and the
  predicate `gbLeadingCoeffIsUnit := IsUnit gₖ`.
* The `K[x][y]`-layer `P` (the `y`-content of the gcd) is **not** captured by `gₖ`: e.g. `I = (y)`
  has `gₖ = 1` (`IsUnit gₖ` holds) yet `f₀ = y ∉ K[x]`, because `P = primpart(gcd) = y` is still to
  be divided out. So `IsUnit gₖ` is *necessary but not sufficient* for the descent base. The base is
  recorded directly as `hbase : degreeOf 0 (sorted 0) = 0` — see the §2.6 residual for why
  discharging it needs the genuine `K[x][y]` divide-out construction, not just `gₖ`. -/

/-- **The `K[x]`-content common divisor of the leading `y`-coefficients** (Lazard's `Gₖ₊₁`, closed
form): the leading `y`-coefficient `gₖ` of the **top** (`y`-degree-maximal) sorted basis element. By
`leadingYCoeff_sortedByYDegree_dvd_of_le` it divides `leadingYCoeff (sorted i)` for every `i`. (Only
the `K[x]`-layer; the `y`-primitive part `P` of the gcd is a separate factor — see the section
docstring.) -/
noncomputable def gbCommonContent {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (htop : Fin B.card) : MvPolynomial (Fin 1) K :=
  leadingYCoeff (sortedByYDegree hB htop)

/-- **`gbCommonContent` divides every leading `y`-coefficient**: with `htop` the `y`-degree-maximal
index (`∀ i, i ≤ htop`), `gₖ = gbCommonContent` divides `leadingYCoeff (sorted i)` for all `i`. -/
theorem gbCommonContent_dvd {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    {htop : Fin B.card} (hmax : ∀ i : Fin B.card, i ≤ htop) (i : Fin B.card) :
    gbCommonContent hB htop ∣ leadingYCoeff (sortedByYDegree hB i) :=
  leadingYCoeff_sortedByYDegree_dvd_of_le hB (hmax i)

/-- **The `K[x]`-content-unit condition** (Lazard's `Gₖ₊₁ = 1`): `IsUnit gₖ` for the top element.
**Necessary but not sufficient** for the descent base — it ignores the `y`-primitive part `P` of the
gcd (`I = (y)` satisfies it yet has `f₀ = y ∉ K[x]`). Records only the `K[x]`-layer of Lazard's
`P·Gₖ₊₁` divide-out. -/
def gbLeadingCoeffIsUnit {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (htop : Fin B.card) : Prop :=
  IsUnit (gbCommonContent hB htop)

/-! ### Part A: dividing out a common factor preserves the Gröbner-basis structure

Lazard (1985), Theorem 1 proof: `hgᵢ := fᵢ / (P·Gₖ₊₁)` is a minimal Gröbner basis iff the `fᵢ`
are, "since `LM(P·Gₖ₊₁)` divides every `LM(fᵢ)` and the relations of divisibility between the
leading monomials are preserved". The arithmetic core is the **leading-monomial shift**: writing
`b = h * q` (a common factor `h ∣ b`), `m.degree b = m.degree h + m.degree q` and
`m.leadingCoeff b = m.leadingCoeff h * m.leadingCoeff q` — so every leading monomial of the divided
set drops by exactly `m.degree h`, an order-isomorphism on degrees that preserves divisibility and
minimality. This is the reachable framework half; the genuine wall (which `h` to divide by so the
quotient's minimal element lands in `K[x]`) is Part B. -/

/-- **Degree of a cofactor** (leading-monomial shift): if `b = h * q` with `h, q ≠ 0`, then
`m.degree q = m.degree b - m.degree h` (`MonomialOrder.degree_mul`, over a domain). -/
theorem degree_cofactor {K : Type*} [Field K] (m : MonomialOrder σ)
    {h q : MvPolynomial σ K} (hh : h ≠ 0) (hq : q ≠ 0) :
    m.degree q = m.degree (h * q) - m.degree h := by
  rw [degree_mul hh hq, add_comm, add_tsub_cancel_right]

/-- **Leading coefficient of a cofactor**: `m.leadingCoeff (h * q) = m.leadingCoeff h *
m.leadingCoeff q` (`MonomialOrder.leadingCoeff_mul`, over a domain) — the leading coefficient
scales multiplicatively under dividing out a common factor. -/
theorem leadingCoeff_cofactor {K : Type*} [Field K] (m : MonomialOrder σ)
    (h q : MvPolynomial σ K) :
    m.leadingCoeff (h * q) = m.leadingCoeff h * m.leadingCoeff q :=
  MonomialOrder.leadingCoeff_mul

/-- **The leading monomial of a common multiple dominates that of the cofactor**: `m.degree q ≤
m.degree (h * q)` (the divided-out factor `h` only adds to the degree). -/
theorem degree_cofactor_le {K : Type*} [Field K] (m : MonomialOrder σ)
    {h q : MvPolynomial σ K} (hh : h ≠ 0) (hq : q ≠ 0) :
    m.degree q ≤ m.degree (h * q) := by
  rw [degree_mul hh hq]; exact le_add_self

/-- **Leading-monomial divisibility is preserved by a common shift** (Part A core). For a fixed
shift `s` (`= m.degree h`), `s + c ≤ s + d ↔ c ≤ d`: dividing both leading monomials by `LM(h)`
preserves the divisibility relation between them — the order-isomorphism `c ↦ s + c` on degrees. -/
theorem degree_add_le_add_iff {s c d : σ →₀ ℕ} : s + c ≤ s + d ↔ c ≤ d :=
  add_le_add_iff_left s

/-- **Leading-monomial shift, equation form**: with `b = h * q`, `b' = h * q'` (`h, q, q' ≠ 0`),
`m.degree b ≤ m.degree b' ↔ m.degree q ≤ m.degree q'` — both leading monomials carry the same `LM(h)`
shift, so the divisibility relation among the divided set matches that among `B`. -/
theorem degree_mul_le_mul_iff {K : Type*} [Field K] (m : MonomialOrder σ)
    {h q q' : MvPolynomial σ K} (hh : h ≠ 0) (hq : q ≠ 0) (hq' : q' ≠ 0) :
    m.degree (h * q) ≤ m.degree (h * q') ↔ m.degree q ≤ m.degree q' := by
  rw [degree_mul hh hq, degree_mul hh hq', degree_add_le_add_iff]

/-- **Minimality is preserved by dividing out a common factor** (Part A, the minimal-basis half of
Lazard's Theorem 1 reduction). If `b' = h·q'` does not lead-monomial-divide a distinct `b = h·q` in
the reduced GB, then `q'` does not lead-monomial-divide `q` after the divide-out: the `LM(h)` shift
cancels (`degree_mul_le_mul_iff`), so the no-divisibility relation transfers to the quotient set. -/
theorem leadingMonomial_cofactor_not_le {K : Type*} [Field K]
    {I : Ideal (MvPolynomial σ K)} {B : Set (MvPolynomial σ K)}
    (hB : IsReducedGroebnerBasis m I B) {h q q' : MvPolynomial σ K} (hh : h ≠ 0)
    (hq : q ≠ 0) (hq' : q' ≠ 0) (hb : h * q ∈ B) (hb' : h * q' ∈ B) (hne : h * q ≠ h * q') :
    ¬ (m.degree q' ≤ m.degree q) := by
  rw [← degree_mul_le_mul_iff m hh hq' hq]
  exact hB.leadingMonomial_not_le hb hb' hne

/-! ### The base obstruction is genuine: `f = xy + 1` (refuting a free base case)

The descent base `C(g₀) ∣ lazardView f₀` cannot be discharged for free: it is **not** implied by any
leading-coefficient unit fact, and is genuinely **false** for some reduced-GB-shaped minimal elements.
The witness is `f = xy + 1` (with `y = X 0`, `x = X 1`): its `K[x][y]` view is `C(x)·Y + 1`, so its
leading-`y`-coefficient is `g = x`, which is **not a unit** of `K[x]`, and `C(x) ∤ C(x)·Y + 1` (the
constant term `1` is not divisible by `x`). Since `xy + 1` generates a reduced Gröbner basis whose only
(hence minimal-`y`-degree) element it is, this refutes "`IsUnit (leadingYCoeff f₀)`" and the base
divisibility alike — so Lazard's divide-out by the genuine `K[x][y]` common factor `P·Gₖ₊₁` is unavoidable
(`I = (xy+1)` has `gₖ = x`, not even `K[x]`-content-unit, but `I = (y)` shows even `IsUnit gₖ` fails to
suffice). -/

/-- `xy + 1`'s leading-`y`-coefficient `x = X 0` does not divide `1` in `K[x]` (`= MvPolynomial (Fin 1)
K`): evaluating at `x ↦ 0` would force `0 ∣ 1` in `K`. -/
theorem leadingYCoeff_xyAddOne_not_dvd_one {K : Type*} [Field K] :
    ¬ (X (0 : Fin 1) : MvPolynomial (Fin 1) K) ∣ 1 := by
  intro h
  have he : (MvPolynomial.eval (fun _ => (0 : K))) (X (0 : Fin 1))
      ∣ (MvPolynomial.eval (fun _ => (0 : K))) 1 := map_dvd _ h
  rw [MvPolynomial.eval_X, map_one, zero_dvd_iff] at he
  exact one_ne_zero he

/-- The `K[x][y]` view of `xy + 1` is `C(x)·Y + 1` (`x = X 0`, `y = X 1`). -/
theorem lazardView_xyAddOne {K : Type*} [Field K] :
    lazardView (X 1 * X 0 + 1 : MvPolynomial (Fin 2) K)
      = Polynomial.C (X 0) * Polynomial.X + 1 := by
  have h1 : (X (1 : Fin 2) : MvPolynomial (Fin 2) K) = X (0 : Fin 1).succ := by congr 1
  rw [lazardView, map_add, map_mul, map_one, finSuccEquiv_X_zero, h1, finSuccEquiv_X_succ]

/-- `leadingYCoeff (xy + 1) = x` (`= X 0`): the coefficient of `Y¹` in `C(x)·Y + 1`. -/
theorem leadingYCoeff_xyAddOne {K : Type*} [Field K] :
    leadingYCoeff (X 1 * X 0 + 1 : MvPolynomial (Fin 2) K) = X 0 := by
  rw [leadingYCoeff, lazardView_xyAddOne]
  have hCX : (Polynomial.C (X (0 : Fin 1) : MvPolynomial (Fin 1) K) * Polynomial.X).natDegree = 1 :=
    Polynomial.natDegree_C_mul_X _ (MvPolynomial.X_ne_zero _)
  have hd : (Polynomial.C (X (0 : Fin 1) : MvPolynomial (Fin 1) K) * Polynomial.X + 1).natDegree = 1 := by
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt
      (by rw [hCX, Polynomial.natDegree_one]; decide), hCX]
  rw [Polynomial.leadingCoeff, hd, Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_one, mul_one, Polynomial.coeff_one, if_neg (by decide), add_zero]

/-- **`leadingYCoeff f₀` need not be a unit** (refuting the cheap base case, unit half): `xy + 1` has
`leadingYCoeff = x`, not a unit of `K[x]`. -/
theorem not_isUnit_leadingYCoeff_xyAddOne {K : Type*} [Field K] :
    ¬ IsUnit (leadingYCoeff (X 1 * X 0 + 1 : MvPolynomial (Fin 2) K)) := by
  rw [leadingYCoeff_xyAddOne]
  exact fun h => leadingYCoeff_xyAddOne_not_dvd_one (isUnit_iff_dvd_one.mp h)

/-- **The base divisibility `C(g₀) ∣ lazardView f₀` genuinely fails** (refuting the cheap base case,
divisibility half): for `f = xy + 1`, `C(leadingYCoeff f) = C(x)` does **not** divide
`lazardView f = C(x)·Y + 1` — the constant term `1` is not divisible by `x`. So the Lemma 3 descent
`lazard_lemma3_dvd` would be **false** for a reduced GB with this minimal element; the no-common-factor
base is a real hypothesis, not a free lemma (Route to discharging it: Lazard's `P·Gₖ₊₁` divide-out). -/
theorem not_C_leadingYCoeff_dvd_lazardView_xyAddOne {K : Type*} [Field K] :
    ¬ Polynomial.C (leadingYCoeff (X 1 * X 0 + 1 : MvPolynomial (Fin 2) K))
        ∣ lazardView (X 1 * X 0 + 1 : MvPolynomial (Fin 2) K) := by
  rw [leadingYCoeff_xyAddOne, lazardView_xyAddOne, Polynomial.C_dvd_iff_dvd_coeff]
  intro h
  have h0 := h 0
  simp only [Polynomial.coeff_add, Polynomial.mul_coeff_zero, Polynomial.coeff_C,
    Polynomial.coeff_X_zero, mul_zero, Polynomial.coeff_one_zero, zero_add] at h0
  exact leadingYCoeff_xyAddOne_not_dvd_one h0

/-- Lazard's base divisibility at the minimal sorted `y`-degree. -/
abbrev HasLazardBaseDvd {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K))) : Prop :=
  ∀ i0 : Fin B.card, i0.val = 0 →
    Polynomial.C (leadingYCoeff (sortedByYDegree hB i0)) ∣ lazardView (sortedByYDegree hB i0)

/-- Lazard's stronger degree-zero base at the minimal sorted `y`-degree. -/
abbrev HasLazardBaseDegreeZero {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K))) : Prop :=
  ∀ i0 : Fin B.card, i0.val = 0 → degreeOf 0 (sortedByYDegree hB i0) = 0

/-- **Lazard's Lemma 3 descent, strengthened induction** (Part B). Assuming the **base divisibility**
`C(g₀) ∣ lazardView f₀` at the minimal `y`-degree index (`hbase`, the genuinely necessary-and-sufficient
form of "no common factor" — strictly weaker than `f₀ ∈ K[x]`, which it follows from via
`C_dvd_lazardView_of_degreeOf_zero`), the divisibility `C(gᵢ) ∣ lazardView (sorted j)` holds for **all**
`j ≤ i` — by strong induction on `i.val`: the base `i.val = 0` is `hbase`; the step uses the
predecessor's IH together with the non-circular `C_dvd_lazardView_succ` (for `j = i`) and the
`gᵢ ∣ g_{i'}` chain (for `j < i`). -/
theorem C_dvd_lazardView_sortedByYDegree_of_le {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hbase : HasLazardBaseDvd hB)
    (i : Fin B.card) :
    ∀ j : Fin B.card, j ≤ i →
      Polynomial.C (leadingYCoeff (sortedByYDegree hB i)) ∣ lazardView (sortedByYDegree hB j) := by
  induction hi : i.val using Nat.strong_induction_on generalizing i with
  | _ n ih =>
    subst hi
    rcases Nat.eq_zero_or_pos i.val with h0 | hpos
    · -- base `i.val = 0`: the only `j ≤ i` is `i`, where `hbase` supplies the divisibility.
      intro j hji
      have hji0 : j.val = 0 := Nat.le_zero.mp (h0 ▸ (Fin.le_def.mp hji))
      have hji_eq : j = i := Fin.ext (by rw [hji0, h0])
      rw [hji_eq]
      exact hbase i h0
    · -- step: let `i'` be the predecessor (`i'.val = i.val - 1`).
      set i' : Fin B.card := ⟨i.val - 1, by omega⟩ with hi'_def
      have hi'val : i'.val = i.val - 1 := by rw [hi'_def]
      have hi'lt : i' < i := by rw [Fin.lt_def, hi'val]; omega
      have hsucc : ∀ k : Fin B.card, k < i → k ≤ i' := by
        intro k hk; rw [Fin.le_def, hi'val]; rw [Fin.lt_def] at hk; omega
      -- IH on `i'` (smaller key).
      have hIH' : ∀ k : Fin B.card, k ≤ i' →
          Polynomial.C (leadingYCoeff (sortedByYDegree hB i'))
            ∣ lazardView (sortedByYDegree hB k) := ih i'.val (by rw [hi'val]; omega) i' rfl
      -- `C(g_i) ∣ lazardView (sorted i)` via the non-circular succ step (IH covers `j ≤ i'`).
      have hsuccdvd : Polynomial.C (leadingYCoeff (sortedByYDegree hB i))
          ∣ lazardView (sortedByYDegree hB i) :=
        C_dvd_lazardView_succ hB hi'lt hsucc hIH'
      -- assemble `∀ j ≤ i`: `j = i` is `hsuccdvd`; `j ≤ i'` uses IH + `g_i ∣ g_{i'}` chain.
      intro j hji
      rcases eq_or_lt_of_le hji with hje | hjl
      · rw [hje]; exact hsuccdvd
      · have hji' : j ≤ i' := hsucc j hjl
        have hchain : leadingYCoeff (sortedByYDegree hB i)
            ∣ leadingYCoeff (sortedByYDegree hB i') :=
          leadingYCoeff_sortedByYDegree_dvd_of_le hB (le_of_lt hi'lt)
        exact dvd_trans (map_dvd Polynomial.C hchain) (hIH' j hji')

/-- **The base divisibility from `f₀ ∈ K[x]`** (the `degreeOf 0 (sorted 0) = 0` ⟹ base-divisibility
adapter). The old no-common-factor base `degreeOf 0 (sorted i0) = 0` (`f₀ ∈ K[x]`) implies the genuinely
necessary-and-sufficient base divisibility `C(g₀) ∣ lazardView f₀` (via
`C_dvd_lazardView_of_degreeOf_zero`), so theorems taking the weaker hypothesis specialize to the
`degreeOf = 0` form. -/
theorem baseDvd_of_degreeOf_zero {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hbase : HasLazardBaseDegreeZero hB)
    (i0 : Fin B.card) (hi0 : i0.val = 0) :
    Polynomial.C (leadingYCoeff (sortedByYDegree hB i0)) ∣ lazardView (sortedByYDegree hB i0) :=
  C_dvd_lazardView_of_degreeOf_zero (hbase i0 hi0)

/-- **Lazard's Lemma 3, the diagonal descent** (Part B conclusion). Under the base divisibility
`C(g₀) ∣ lazardView f₀` at the minimal `y`-degree index (`hbase`, the genuinely necessary-and-sufficient
"no common factor" — see `baseDvd_of_degreeOf_zero` for the `f₀ ∈ K[x]` special case), each sorted basis
element satisfies `gᵢ ∣ fᵢ` in the form `C(leadingYCoeff (sorted i)) ∣ lazardView (sorted i)` — the
`j = i` specialization of `C_dvd_lazardView_sortedByYDegree_of_le`. -/
theorem lazard_lemma3_dvd {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hbase : HasLazardBaseDvd hB)
    (i : Fin B.card) :
    Polynomial.C (leadingYCoeff (sortedByYDegree hB i)) ∣ lazardView (sortedByYDegree hB i) :=
  C_dvd_lazardView_sortedByYDegree_of_le hB hbase i i le_rfl

/-- **Lazard's Lemma 3, the diagonal descent from `f₀ ∈ K[x]`** (Part B conclusion, `degreeOf = 0`
form). The `degreeOf 0 (sorted 0) = 0` specialization of `lazard_lemma3_dvd` (base discharged by
`baseDvd_of_degreeOf_zero`). -/
theorem lazard_lemma3_dvd_of_degreeOf_zero {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hbase : HasLazardBaseDegreeZero hB)
    (i : Fin B.card) :
    Polynomial.C (leadingYCoeff (sortedByYDegree hB i)) ∣ lazardView (sortedByYDegree hB i) :=
  lazard_lemma3_dvd hB (baseDvd_of_degreeOf_zero hB hbase) i

open scoped Classical in
/-- A `NormalizedGCDMonoid` on `MvPolynomial (Fin 1) K` (UFD `⟹` normalized GCD domain), supplying
the normalization that `Polynomial.content`/`primPart` need. Used as a local `letI`; not a global
instance (avoids diamonds with `gcdMonoidMvPolynomialFinOne`). -/
@[reducible] noncomputable def normalizedGcdMonoidMvPolynomialFinOne (K : Type*) [Field K] :
    NormalizedGCDMonoid (MvPolynomial (Fin 1) K) :=
  letI := UniqueFactorizationMonoid.normalizationMonoid (α := MvPolynomial (Fin 1) K)
  UniqueFactorizationMonoid.toNormalizedGCDMonoid _

/-- **Content divides the leading-`y`-coefficient**: for the chosen `NormalizedGCDMonoid`, the
content of `lazardView f` divides `Rᵢ = leadingYCoeff f` (`content` divides every coefficient,
including the leading one). -/
theorem content_lazardView_dvd_leadingYCoeff {K : Type*} [Field K] (f : MvPolynomial (Fin 2) K) :
    @Polynomial.content _ _ (normalizedGcdMonoidMvPolynomialFinOne K) (lazardView f)
      ∣ leadingYCoeff f := by
  letI := normalizedGcdMonoidMvPolynomialFinOne K
  rw [leadingYCoeff, Polynomial.leadingCoeff]
  exact Polynomial.content_dvd_coeff _

/-- **Lazard's Lemma 3, content half of `Pₖ = Rₖ·Sₖ`**: if `gᵢ ∣ fᵢ` in the form `C(Rᵢ) ∣ lazardView fᵢ`
(equivalently `Rᵢ ∣ content`, the converse of the always-true `content ∣ Rᵢ`), then the content of
`lazardView fᵢ` is **associated** to `Rᵢ = leadingYCoeff fᵢ`. -/
theorem content_associated_leadingYCoeff_of_C_dvd {K : Type*} [Field K]
    {f : MvPolynomial (Fin 2) K}
    (hdvd : Polynomial.C (leadingYCoeff f) ∣ lazardView f) :
    Associated (@Polynomial.content _ _ (normalizedGcdMonoidMvPolynomialFinOne K) (lazardView f))
      (leadingYCoeff f) := by
  letI := normalizedGcdMonoidMvPolynomialFinOne K
  refine associated_of_dvd_dvd (content_lazardView_dvd_leadingYCoeff f) ?_
  exact Polynomial.dvd_content_iff_C_dvd.mpr hdvd

/-- **The base divisibility is the content criterion** (the "no common factor" characterization). The
descent base `C(gᵢ) ∣ lazardView fᵢ` holds **iff** the content of `lazardView fᵢ` is *associated* to
`Rᵢ = leadingYCoeff fᵢ` (i.e. `fᵢ` is `y`-primitive up to its leading coefficient). Forward is
`content_associated_leadingYCoeff_of_C_dvd`; the converse uses `gᵢ ∣ content` (from the association) and
`Polynomial.dvd_content_iff_C_dvd`. This is the exact obstruction Lazard's `P·Gₖ₊₁` divide-out removes —
it makes every `fᵢ` `y`-primitive (`content ∼ Rᵢ`) so the base holds. -/
theorem C_dvd_lazardView_iff_content_associated {K : Type*} [Field K]
    {f : MvPolynomial (Fin 2) K} :
    Polynomial.C (leadingYCoeff f) ∣ lazardView f ↔
      Associated (@Polynomial.content _ _ (normalizedGcdMonoidMvPolynomialFinOne K) (lazardView f))
        (leadingYCoeff f) := by
  letI := normalizedGcdMonoidMvPolynomialFinOne K
  refine ⟨content_associated_leadingYCoeff_of_C_dvd, fun hassoc => ?_⟩
  exact Polynomial.dvd_content_iff_C_dvd.mp hassoc.symm.dvd

/-- **Lazard's Lemma 3, monic-primpart half of `Pₖ = Rₖ·Sₖ`**: if `C(Rᵢ) ∣ lazardView fᵢ` (`gᵢ ∣ fᵢ`),
the primitive part `Sᵢ = (lazardView fᵢ).primPart` is **monic in `y`** — its leading coefficient is a
unit of `K[x]` (a nonzero constant). Since `Rᵢ = content · leadingCoeff(Sᵢ)` and `content ∼ Rᵢ`, the
factor `leadingCoeff(Sᵢ)` must be a unit. -/
theorem leadingCoeff_primPart_isUnit_of_C_dvd {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    (hf : f ≠ 0) (hdvd : Polynomial.C (leadingYCoeff f) ∣ lazardView f) :
    IsUnit ((@Polynomial.primPart _ _ (normalizedGcdMonoidMvPolynomialFinOne K)
      (lazardView f)).leadingCoeff) := by
  letI := normalizedGcdMonoidMvPolynomialFinOne K
  set c := Polynomial.content (lazardView f) with hc
  set s := Polynomial.primPart (lazardView f) with hs
  have hassoc : Associated c (leadingYCoeff f) := content_associated_leadingYCoeff_of_C_dvd hdvd
  have hc0 : c ≠ 0 := by
    rw [hc, Ne, Polynomial.content_eq_zero_iff]; exact lazardView_eq_zero_iff.not.mpr hf
  -- `Rᵢ = leadingCoeff (C c * s) = c * leadingCoeff s` (domain), and `c ∼ Rᵢ`, so `leadingCoeff s` is a unit.
  have hReq : leadingYCoeff f = c * s.leadingCoeff := by
    conv_lhs => rw [leadingYCoeff, Polynomial.eq_C_content_mul_primPart (lazardView f), ← hc, ← hs]
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
  obtain ⟨u, hu⟩ := hassoc
  -- `c * (s.leadingCoeff) = c * u`, cancel `c` to get `s.leadingCoeff = u`, a unit.
  have : c * s.leadingCoeff = c * (u : MvPolynomial (Fin 1) K) := by rw [← hReq, hu]
  rw [mul_right_inj' hc0] at this
  rw [this]; exact u.isUnit

/-- **Lazard's Lemma 3, the `Pₖ = Rₖ·Sₖ` factorization** (Bronstein/Czichowski §2.6(i)). If `gᵢ ∣ fᵢ`
(`C(Rᵢ) ∣ lazardView fᵢ`), the `K[x][y]` view splits as `lazardView fᵢ = C(cᵢ)·Sᵢ` with content `cᵢ`
associated to `Rᵢ = leadingYCoeff fᵢ` and `Sᵢ` primitive and monic-in-`y` (unit leading coefficient) —
the Czichowski structure `Pₖ = Rₖ·Sₖ`. -/
theorem lazard_Pk_eq_Rk_Sk {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K} (hf : f ≠ 0)
    (hdvd : Polynomial.C (leadingYCoeff f) ∣ lazardView f) :
    ∃ S : Polynomial (MvPolynomial (Fin 1) K),
      lazardView f = Polynomial.C (@Polynomial.content _ _
          (normalizedGcdMonoidMvPolynomialFinOne K) (lazardView f)) * S ∧
        Associated (@Polynomial.content _ _ (normalizedGcdMonoidMvPolynomialFinOne K)
          (lazardView f)) (leadingYCoeff f) ∧
        S.IsPrimitive ∧ IsUnit S.leadingCoeff := by
  letI := normalizedGcdMonoidMvPolynomialFinOne K
  refine ⟨(lazardView f).primPart, Polynomial.eq_C_content_mul_primPart (lazardView f),
    content_associated_leadingYCoeff_of_C_dvd hdvd, Polynomial.isPrimitive_primPart _,
    leadingCoeff_primPart_isUnit_of_C_dvd hf hdvd⟩

/-- **Lazard's `Pₖ = Rₖ·Sₖ` for every sorted basis element** (Part C, no-common-factor case). With
the base divisibility `C(g₀) ∣ lazardView f₀` (`hbase`, the necessary-and-sufficient "no common factor"),
the descent `lazard_lemma3_dvd` discharges the divisibility hypothesis of `lazard_Pk_eq_Rk_Sk`, so
*every* `fᵢ = sorted i` splits as `lazardView fᵢ = C(cᵢ)·Sᵢ` with content `cᵢ ∼ Rᵢ = leadingYCoeff fᵢ`
and `Sᵢ` primitive and monic in `y` (unit leading coefficient). -/
theorem lazard_Pk_eq_Rk_Sk_of_sortedByYDegree {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hbase : HasLazardBaseDvd hB)
    (i : Fin B.card) :
    ∃ S : Polynomial (MvPolynomial (Fin 1) K),
      lazardView (sortedByYDegree hB i) = Polynomial.C (@Polynomial.content _ _
          (normalizedGcdMonoidMvPolynomialFinOne K) (lazardView (sortedByYDegree hB i))) * S ∧
        Associated (@Polynomial.content _ _ (normalizedGcdMonoidMvPolynomialFinOne K)
          (lazardView (sortedByYDegree hB i))) (leadingYCoeff (sortedByYDegree hB i)) ∧
        S.IsPrimitive ∧ IsUnit S.leadingCoeff :=
  lazard_Pk_eq_Rk_Sk (hB.ne_zero (Finset.mem_coe.mpr (sortedByYDegree_mem hB i)))
    (lazard_lemma3_dvd hB hbase i)

/-- **Lazard's `Pₖ = Rₖ·Sₖ` for every sorted basis element from `f₀ ∈ K[x]`** (Part C, `degreeOf = 0`
form): the `degreeOf 0 (sorted 0) = 0` specialization of `lazard_Pk_eq_Rk_Sk_of_sortedByYDegree` (base
discharged by `baseDvd_of_degreeOf_zero`). -/
theorem lazard_Pk_eq_Rk_Sk_of_sortedByYDegree_of_degreeOf_zero {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hbase : HasLazardBaseDegreeZero hB)
    (i : Fin B.card) :
    ∃ S : Polynomial (MvPolynomial (Fin 1) K),
      lazardView (sortedByYDegree hB i) = Polynomial.C (@Polynomial.content _ _
          (normalizedGcdMonoidMvPolynomialFinOne K) (lazardView (sortedByYDegree hB i))) * S ∧
        Associated (@Polynomial.content _ _ (normalizedGcdMonoidMvPolynomialFinOne K)
          (lazardView (sortedByYDegree hB i))) (leadingYCoeff (sortedByYDegree hB i)) ∧
        S.IsPrimitive ∧ IsUnit S.leadingCoeff :=
  lazard_Pk_eq_Rk_Sk_of_sortedByYDegree hB (baseDvd_of_degreeOf_zero hB hbase) i

/-! ## Part B: the no-common-factor base, and the genuine `K[x][y]` divide-out obstruction

Lazard (1985), Lemma 3 (p.263): *if the `fᵢ` have no common factor, then `f₀ ∈ K[x]` and `gₖ = 1`*.
The mechanism is the `y`-**primitive part** `P := primPart(lazardView f₀)`. Lazard shows `P` divides
every `fᵢ` by an induction that feeds `(gᵢ/g_{i+1})·fᵢ ∈ (fᵢ,…,f₀)` through the IH and then strips
the `K[x]`-scalar `gᵢ/g_{i+1}` by Gauss's lemma (a primitive polynomial dividing `C(c)·g` divides
`g`). No common factor then forces `P` to be a unit, i.e. `f₀ ∈ K[x]` (`natDegree = 0`).

This section formalizes the reusable arithmetic of that route — the **general-`K[x][y]`-divisor**
propagation (the `C d`-specialized descent of Part A↑ generalized to any divisor `P`) and the
**Gauss-lemma scalar-strip** — and pins the precise remaining obstruction. The single missing input
(`§2.6 residual`) is `P ∣ lazardView fᵢ` for *all* `i` (the structure induction), whose step needs `P`
to survive the `y`-shift `X^{shift}` inside `(gᵢ/g_{i+1})·fᵢ − y^{shift}·f₀`; unlike a `K[x]` constant
`C d` (`C_dvd_of_C_dvd_X_pow_mul`), a general `P` does **not** survive `X^{shift}` (e.g. `X ∣ X·p`,
`X ∤ p`). Lazard sidesteps this by reducing `(gᵢ/g_{i+1})·fᵢ` as an ideal member (degree `< d(i+1)`)
rather than peeling `X^{shift}`, so the structure induction is over GB-reductions of the whole
combination — the genuinely research-grade core left open here. -/

/-- **General-divisor sum propagation** (Part B core, generalizing `C_dvd_lazardView_sum` off the
`C d` form). If a divisor `P : K[x][y]` divides `lazardView b` for every `b` in the support of a
finite `K[x][y]`-combination `R = ∑ b ∈ s, h b · b`, then `P ∣ lazardView R` — `lazardView` is a ring
hom, so `P` divides every term and hence the sum. -/
theorem dvd_lazardView_sum {K : Type*} [Field K] {P : Polynomial (MvPolynomial (Fin 1) K)}
    {s : Finset (MvPolynomial (Fin 2) K)} {h : MvPolynomial (Fin 2) K → MvPolynomial (Fin 2) K}
    (hdvd : ∀ b ∈ s, P ∣ lazardView b) :
    P ∣ lazardView (∑ b ∈ s, h b * b) := by
  rw [lazardView, map_sum]
  refine Finset.dvd_sum (fun b hb => ?_)
  rw [map_mul]
  exact Dvd.dvd.mul_left (hdvd b hb) _

/-- **General-divisor bounded-representation propagation** (Part B core, generalizing
`C_dvd_lazardView_of_mem_of_dvd_bounded` off the `C d` form). If `R ∈ I` is nonzero and a divisor
`P : K[x][y]` divides `lazardView b` for every basis element `b` of `y`-degree `≤ degreeOf 0 R`
(`exists_yDegree_bounded_representation` selects those as the only contributors), then `P ∣ lazardView
R`. This is the IH-aggregation step of Lazard's structure induction for a general `K[x][y]` factor. -/
theorem dvd_lazardView_of_mem_of_dvd_bounded {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    {P : Polynomial (MvPolynomial (Fin 1) K)} {R : MvPolynomial (Fin 2) K}
    (hRI : R ∈ I) (hR0 : R ≠ 0)
    (hdvd : ∀ b ∈ B, degreeOf 0 b ≤ degreeOf 0 R → P ∣ lazardView b) :
    P ∣ lazardView R := by
  obtain ⟨g, hgsum, hgdeg⟩ := exists_yDegree_bounded_representation hB hRI hR0
  rw [hgsum, lazardView, map_sum]
  refine Finset.dvd_sum (fun b hb => ?_)
  by_cases hbne : g b * b = 0
  · rw [hbne, map_zero]; exact dvd_zero _
  · rw [map_mul]
    exact Dvd.dvd.mul_left (hdvd b hb (hgdeg b hb hbne)) _

/-- **Gauss's lemma, scalar-strip form** (Part B core). A `y`-primitive `P : K[x][y]` dividing
`C(c)·g` (a `K[x]`-scalar `c` times `g`) divides `g` itself: `P ∣ C(c)·g ⟹ P ∣ (C(c)·g).primPart =
(C c).primPart · g.primPart` (a unit times `g.primPart`, `isUnit_primPart_C`/`primPart_mul`), and a
primitive divisor of a primitive part divides the polynomial (`IsPrimitive.dvd_primPart_iff_dvd`). This
is the step that peels the `K[x]`-factor `gᵢ/g_{i+1}` in Lazard's `primpart(f₀)`-divides-all induction. -/
theorem isPrimitive_dvd_of_dvd_C_mul {K : Type*} [Field K]
    {P g : Polynomial (MvPolynomial (Fin 1) K)} {c : MvPolynomial (Fin 1) K}
    (hP : P.IsPrimitive) (hc : c ≠ 0) (hg : g ≠ 0) (hdvd : P ∣ Polynomial.C c * g) :
    P ∣ g := by
  letI := normalizedGcdMonoidMvPolynomialFinOne K
  have hCg0 : Polynomial.C c * g ≠ 0 :=
    mul_ne_zero (by rwa [Ne, Polynomial.C_eq_zero]) hg
  -- `P ∣ (C c * g).primPart` (primitive divisor `↔` divides primPart).
  have hpp : P ∣ (Polynomial.C c * g).primPart :=
    (hP.dvd_primPart_iff_dvd hCg0).mpr hdvd
  -- `(C c * g).primPart = (C c).primPart * g.primPart`, a unit times `g.primPart`.
  rw [Polynomial.primPart_mul hCg0] at hpp
  obtain ⟨u, hu⟩ := Polynomial.isUnit_primPart_C c
  rw [← hu] at hpp
  -- strip the unit `u` on the dividend, then `P ∣ g.primPart ⟹ P ∣ g`.
  rw [(u.isUnit).dvd_mul_left] at hpp
  exact (hP.dvd_primPart_iff_dvd hg).mp hpp

/-- **The candidate common `y`-factor is primitive** (Part B): `primPart(lazardView f)` is `y`-primitive
(`Polynomial.isPrimitive_primPart`) — the `P` Lazard divides the whole basis by. -/
theorem isPrimitive_primPart_lazardView {K : Type*} [Field K] (f : MvPolynomial (Fin 2) K) :
    (@Polynomial.primPart _ _ (normalizedGcdMonoidMvPolynomialFinOne K) (lazardView f)).IsPrimitive :=
  letI := normalizedGcdMonoidMvPolynomialFinOne K
  Polynomial.isPrimitive_primPart _

/-- **The candidate common `y`-factor divides the min element** (Part B): `primPart(lazardView f₀) ∣
lazardView f₀` (`Polynomial.primPart_dvd`) — the base of Lazard's `primpart(f₀)`-divides-all induction. -/
theorem primPart_lazardView_dvd {K : Type*} [Field K] (f : MvPolynomial (Fin 2) K) :
    (@Polynomial.primPart _ _ (normalizedGcdMonoidMvPolynomialFinOne K) (lazardView f))
      ∣ lazardView f :=
  letI := normalizedGcdMonoidMvPolynomialFinOne K
  Polynomial.primPart_dvd _

/-- **`f₀ ∈ K[x]` ⟺ the candidate `y`-factor `primPart(lazardView f₀)` is a unit** (Part B, the exact
collapse target). The minimal element has `y`-degree `0` iff `lazardView f₀` has `natDegree 0` iff its
primitive part is a unit (a primitive `y`-constant). So Lazard's conclusion "`f₀ ∈ K[x]`" is exactly
"`primPart(lazardView f₀)` is a unit", which the no-common-factor divide-out forces. -/
theorem degreeOf_zero_iff_isUnit_primPart_lazardView {K : Type*} [Field K]
    {f : MvPolynomial (Fin 2) K} :
    degreeOf 0 f = 0 ↔
      IsUnit (@Polynomial.primPart _ _ (normalizedGcdMonoidMvPolynomialFinOne K) (lazardView f)) := by
  letI := normalizedGcdMonoidMvPolynomialFinOne K
  rw [← natDegree_lazardView, ← Polynomial.natDegree_primPart (p := lazardView f)]
  constructor
  · intro h0
    -- `natDegree (primPart) = 0` and primitive ⟹ unit (a primitive `y`-constant).
    rw [Polynomial.eq_C_of_natDegree_eq_zero h0]
    rw [Polynomial.isUnit_C]
    -- a primitive constant `C r` has `r` a unit (`content = normalize r = 1`).
    have hprim := Polynomial.isPrimitive_primPart (lazardView f)
    rw [Polynomial.eq_C_of_natDegree_eq_zero h0, Polynomial.isPrimitive_iff_content_eq_one,
      Polynomial.content_C, normalize_eq_one] at hprim
    exact hprim
  · intro hu
    exact Polynomial.natDegree_eq_zero_of_isUnit hu

/-- **The min element's `y`-primitive part divides the next basis element** (Part B, structure
induction step — Lazard's "`primpart(f₀)` divides `f_{i+1}`"). Fix `P := primPart(lazardView f₀)`
(`f₀ = sorted 0`). With `i < i1` immediate (`hsucc`) and the IH `P ∣ lazardView (sorted j)` for all
`j ≤ i`, one gets `P ∣ lazardView f_{i1}`. Mechanism (`C_dvd_lazardView_succ` shape, but for the fixed
primitive divisor `P`): the reduction `R = yConst q · f_{i1} − y^{shift}·fi ∈ I` (`q = gᵢ/g_{i1}`) has
`y`-degree `< d(i1)`, so by IH `P ∣ lazardView R`; with `P ∣ lazardView fi` (IH at `i`), the reduction
equation gives `P ∣ C q · lazardView f_{i1}`; the `K[x]`-scalar `q` is stripped by Gauss's lemma
(`isPrimitive_dvd_of_dvd_C_mul`, `P` primitive). -/
theorem primPart_lazardView_min_dvd_succ {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (i0 : Fin B.card) {i i1 : Fin B.card} (hii1 : i < i1)
    (hsucc : ∀ j : Fin B.card, j < i1 → j ≤ i)
    (hIH : ∀ j : Fin B.card, j ≤ i →
      (@Polynomial.primPart _ _ (normalizedGcdMonoidMvPolynomialFinOne K)
        (lazardView (sortedByYDegree hB i0))) ∣ lazardView (sortedByYDegree hB j)) :
    (@Polynomial.primPart _ _ (normalizedGcdMonoidMvPolynomialFinOne K)
      (lazardView (sortedByYDegree hB i0))) ∣ lazardView (sortedByYDegree hB i1) := by
  letI := normalizedGcdMonoidMvPolynomialFinOne K
  set P := (lazardView (sortedByYDegree hB i0)).primPart with hP_def
  set fi := sortedByYDegree hB i with hfi_def
  set fj := sortedByYDegree hB i1 with hfj_def
  have hfi0 : fi ≠ 0 := hB.ne_zero (Finset.mem_coe.mpr (sortedByYDegree_mem hB i))
  have hfj0 : fj ≠ 0 := hB.ne_zero (Finset.mem_coe.mpr (sortedByYDegree_mem hB i1))
  have hdlt : degreeOf 0 fi < degreeOf 0 fj := degreeOf_sortedByYDegree_strictMono hB hii1
  obtain ⟨q, hq⟩ := leadingYCoeff_sortedByYDegree_dvd_of_lt hB hii1
  set sh := degreeOf 0 fj - degreeOf 0 fi with hsh
  set R := yConst q * fj - X 0 ^ sh * fi with hR_def
  have hRmem : R ∈ I :=
    lazard_lemma3_reductionStep_mem (hB.isGroebnerBasis.1 fi (sortedByYDegree_mem hB i))
      (hB.isGroebnerBasis.1 fj (sortedByYDegree_mem hB i1))
  have hRdeg : degreeOf 0 R < degreeOf 0 fj :=
    lazard_lemma3_reductionStep hfi0 hdlt hq.symm
  -- `P ∣ lazardView R`: every GB-reduction contributor has `y`-degree `< d(i1)`, so index `≤ i`.
  have hRdvd : P ∣ lazardView R := by
    by_cases hR0 : R = 0
    · rw [hR0, lazardView_eq_zero_iff.mpr rfl]; exact dvd_zero _
    refine dvd_lazardView_of_mem_of_dvd_bounded hB hRmem hR0 (fun b hb hbdeg => ?_)
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
  -- `P ∣ C q · lazardView f_{i1}` from the reduction equation (IH at `i` gives `P ∣ lazardView fi`).
  have hfi_dvd : P ∣ lazardView fi := hIH i le_rfl
  have hCq : P ∣ Polynomial.C q * lazardView fj := by
    have heq : Polynomial.C q * lazardView fj
        = lazardView R + Polynomial.X ^ sh * lazardView fi := by
      rw [hR_def, lazardView_reductionStep]; ring
    rw [heq]
    exact dvd_add hRdvd (Dvd.dvd.mul_left hfi_dvd _)
  -- strip the `K[x]`-scalar `q` by Gauss (`P` primitive, `q ≠ 0`, `lazardView fj ≠ 0`).
  have hq0 : (q : MvPolynomial (Fin 1) K) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hq
    exact (leadingYCoeff_ne_zero.mpr hfi0) hq
  exact isPrimitive_dvd_of_dvd_C_mul (isPrimitive_primPart_lazardView _) hq0
    (lazardView_eq_zero_iff.not.mpr hfj0) hCq

/-- **The min element's `y`-primitive part divides every basis element** (Part B, full structure
induction — Lazard's "`primpart(f₀)` divides `f₀,…,fₖ`"). For the min-`y`-degree element `f₀ = sorted
0`, `P := primPart(lazardView f₀)` divides `lazardView (sorted i)` for all `i`, by strong induction on
`i.val`: the base `i.val = 0` is `primPart_lazardView_dvd` (`P ∣ lazardView f₀`); the step is
`primPart_lazardView_min_dvd_succ`. This is the genuine structure fact behind the no-common-factor
base. -/
theorem primPart_lazardView_min_dvd_all {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (i0 : Fin B.card) (hi0 : i0.val = 0) (i : Fin B.card) :
    (@Polynomial.primPart _ _ (normalizedGcdMonoidMvPolynomialFinOne K)
      (lazardView (sortedByYDegree hB i0))) ∣ lazardView (sortedByYDegree hB i) := by
  letI := normalizedGcdMonoidMvPolynomialFinOne K
  induction hi : i.val using Nat.strong_induction_on generalizing i with
  | _ n ih =>
    subst hi
    rcases Nat.eq_zero_or_pos i.val with h0 | hpos
    · -- base: `i.val = 0 = i0.val`, so `i = i0`; `P ∣ lazardView f₀` is `primPart_lazardView_dvd`.
      have hii0 : i = i0 := Fin.ext (by rw [h0, hi0])
      rw [hii0]
      exact primPart_lazardView_dvd _
    · -- step: `i'` the predecessor; IH at `i'` covers all `j ≤ i'`, then the succ step.
      set i' : Fin B.card := ⟨i.val - 1, by omega⟩ with hi'_def
      have hi'val : i'.val = i.val - 1 := by rw [hi'_def]
      have hi'lt : i' < i := by rw [Fin.lt_def, hi'val]; omega
      have hsucc : ∀ k : Fin B.card, k < i → k ≤ i' := by
        intro k hk; rw [Fin.le_def, hi'val]; rw [Fin.lt_def] at hk; omega
      have hIH : ∀ j : Fin B.card, j ≤ i' →
          (lazardView (sortedByYDegree hB i0)).primPart ∣ lazardView (sortedByYDegree hB j) := by
        intro j hji'
        exact ih j.val (by rw [Fin.le_def, hi'val] at hji'; omega) j rfl
      exact primPart_lazardView_min_dvd_succ hB i0 hi'lt hsucc hIH

/-- **The basis has no common `y`-factor** (Lazard's "the `fᵢ` have no common factor", `K[x][y]`-layer
`P = 1`): every `K[x][y]`-divisor common to all `lazardView (sorted i)` is a unit. This is the genuine
no-common-factor hypothesis of Lazard's Theorem 1 reduction — the state reached after dividing out
`P·Gₖ₊₁`. (The `K[x]`-layer `Gₖ₊₁ = 1` is the separate `gbLeadingCoeffIsUnit`.) -/
def HasNoCommonYFactor {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K))) : Prop :=
  ∀ P : Polynomial (MvPolynomial (Fin 1) K),
    (∀ i : Fin B.card, P ∣ lazardView (sortedByYDegree hB i)) → IsUnit P

/-- **No common `y`-factor ⟹ the min element is in `K[x]`** (Part B conclusion, Lazard's "`f₀ ∈ K[x]`").
The candidate `P = primPart(lazardView f₀)` is a common `y`-factor of every basis view
(`primPart_lazardView_min_dvd_all`); no-common-factor forces `P` to be a unit, which is exactly
`degreeOf 0 f₀ = 0` (`degreeOf_zero_iff_isUnit_primPart_lazardView`). -/
theorem degreeOf_min_eq_zero_of_hasNoCommonYFactor {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hncf : HasNoCommonYFactor hB) (i0 : Fin B.card) (hi0 : i0.val = 0) :
    degreeOf 0 (sortedByYDegree hB i0) = 0 := by
  letI := normalizedGcdMonoidMvPolynomialFinOne K
  have hunit : IsUnit ((lazardView (sortedByYDegree hB i0)).primPart) :=
    hncf _ (fun i => primPart_lazardView_min_dvd_all hB i0 hi0 i)
  exact degreeOf_zero_iff_isUnit_primPart_lazardView.mpr hunit

/-- **Lazard's Lemma 3 descent, unconditional under no-common-factor** (Part C, the divide-out
discharges the base). With `HasNoCommonYFactor` (Lazard's `P·Gₖ₊₁` already divided out), the base
hypothesis `hbase` of `lazard_lemma3_dvd` is discharged via
`degreeOf_min_eq_zero_of_hasNoCommonYFactor`, so each sorted element satisfies `gᵢ ∣ fᵢ` in the form
`C(leadingYCoeff (sorted i)) ∣ lazardView (sorted i)` with **no** base hypothesis. -/
theorem lazard_lemma3_dvd_of_hasNoCommonYFactor {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hncf : HasNoCommonYFactor hB) (i : Fin B.card) :
    Polynomial.C (leadingYCoeff (sortedByYDegree hB i)) ∣ lazardView (sortedByYDegree hB i) :=
  lazard_lemma3_dvd_of_degreeOf_zero hB
    (fun i0 hi0 => degreeOf_min_eq_zero_of_hasNoCommonYFactor hB hncf i0 hi0) i

/-- **Lazard's `Pₖ = Rₖ·Sₖ`, unconditional under no-common-factor** (Part C). With
`HasNoCommonYFactor`, every sorted basis element splits as `lazardView fᵢ = C(cᵢ)·Sᵢ` with content
`cᵢ ∼ Rᵢ = leadingYCoeff fᵢ` and `Sᵢ` primitive and monic in `y` — the Czichowski structure, with the
base hypothesis discharged by the divide-out (`degreeOf_min_eq_zero_of_hasNoCommonYFactor`). -/
theorem lazard_Pk_eq_Rk_Sk_of_hasNoCommonYFactor {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hncf : HasNoCommonYFactor hB) (i : Fin B.card) :
    ∃ S : Polynomial (MvPolynomial (Fin 1) K),
      lazardView (sortedByYDegree hB i) = Polynomial.C (@Polynomial.content _ _
          (normalizedGcdMonoidMvPolynomialFinOne K) (lazardView (sortedByYDegree hB i))) * S ∧
        Associated (@Polynomial.content _ _ (normalizedGcdMonoidMvPolynomialFinOne K)
          (lazardView (sortedByYDegree hB i))) (leadingYCoeff (sortedByYDegree hB i)) ∧
        S.IsPrimitive ∧ IsUnit S.leadingCoeff :=
  lazard_Pk_eq_Rk_Sk_of_sortedByYDegree_of_degreeOf_zero hB
    (fun i0 hi0 => degreeOf_min_eq_zero_of_hasNoCommonYFactor hB hncf i0 hi0) i

-- Part B/C: the structure induction and the unconditional descent under no-common-factor.
example {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (i0 : Fin B.card) (hi0 : i0.val = 0) (i : Fin B.card) :
    (@Polynomial.primPart _ _ (normalizedGcdMonoidMvPolynomialFinOne K)
      (lazardView (sortedByYDegree hB i0))) ∣ lazardView (sortedByYDegree hB i) :=
  primPart_lazardView_min_dvd_all hB i0 hi0 i

example {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hncf : HasNoCommonYFactor hB) (i0 : Fin B.card) (hi0 : i0.val = 0) :
    degreeOf 0 (sortedByYDegree hB i0) = 0 :=
  degreeOf_min_eq_zero_of_hasNoCommonYFactor hB hncf i0 hi0

example {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hncf : HasNoCommonYFactor hB) (i : Fin B.card) :
    Polynomial.C (leadingYCoeff (sortedByYDegree hB i)) ∣ lazardView (sortedByYDegree hB i) :=
  lazard_lemma3_dvd_of_hasNoCommonYFactor hB hncf i

-- Restatements against the intended wording.
example {K : Type*} [Field K] (r : MvPolynomial (Fin 1) K) :
    lazardView (yConst r) = Polynomial.C r :=
  lazardView_yConst r

example {K : Type*} [Field K] {fi fi1 : MvPolynomial (Fin 2) K}
    (hfi : fi ≠ 0) (hd : degreeOf 0 fi < degreeOf 0 fi1)
    {q : MvPolynomial (Fin 1) K} (hq : leadingYCoeff fi1 * q = leadingYCoeff fi) :
    degreeOf 0 (yConst q * fi1 - X 0 ^ (degreeOf 0 fi1 - degreeOf 0 fi) * fi)
      < degreeOf 0 fi1 :=
  lazard_lemma3_reductionStep hfi hd hq

-- Restatements of the Lemma 3 descent components against the intended wording.
example {K : Type*} [Field K] {fi fi1 : MvPolynomial (Fin 2) K} {q d : MvPolynomial (Fin 1) K}
    {sh : ℕ} (hfi1 : Polynomial.C d ∣ lazardView fi1)
    (hR : Polynomial.C d ∣ lazardView (yConst q * fi1 - X 0 ^ sh * fi)) :
    Polynomial.C d ∣ lazardView fi :=
  C_dvd_lazardView_of_reductionStep hfi1 hR

example {K : Type*} [Field K] {d : MvPolynomial (Fin 1) K}
    {s : Finset (MvPolynomial (Fin 2) K)} {h : MvPolynomial (Fin 2) K → MvPolynomial (Fin 2) K}
    (hdvd : ∀ b ∈ s, Polynomial.C d ∣ lazardView b) :
    Polynomial.C d ∣ lazardView (∑ b ∈ s, h b * b) :=
  C_dvd_lazardView_sum hdvd

example {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    {R : MvPolynomial (Fin 2) K} (hRI : R ∈ I) (hR0 : R ≠ 0) :
    ∃ g : MvPolynomial (Fin 2) K → MvPolynomial (Fin 2) K,
      R = ∑ b ∈ B, g b * b ∧ ∀ b ∈ B, g b * b ≠ 0 → degreeOf 0 b ≤ degreeOf 0 R :=
  exists_yDegree_bounded_representation hB hRI hR0

example {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    {i j : Fin B.card} (hij : i ≤ j) :
    leadingYCoeff (sortedByYDegree hB j) ∣ leadingYCoeff (sortedByYDegree hB i) :=
  leadingYCoeff_sortedByYDegree_dvd_of_le hB hij

-- Restatements of the no-common-factor descent (Parts A–C) against the intended wording.
-- Part A: dividing out a common factor preserves the leading-monomial structure.
example {K : Type*} [Field K] (m : MonomialOrder σ) {h q : MvPolynomial σ K}
    (hh : h ≠ 0) (hq : q ≠ 0) :
    m.degree q = m.degree (h * q) - m.degree h :=
  degree_cofactor m hh hq

example {K : Type*} [Field K] (m : MonomialOrder σ) {h q q' : MvPolynomial σ K}
    (hh : h ≠ 0) (hq : q ≠ 0) (hq' : q' ≠ 0) :
    m.degree (h * q) ≤ m.degree (h * q') ↔ m.degree q ≤ m.degree q' :=
  degree_mul_le_mul_iff m hh hq hq'

example {K : Type*} [Field K] {I : Ideal (MvPolynomial σ K)} {B : Set (MvPolynomial σ K)}
    (hB : IsReducedGroebnerBasis m I B) {h q q' : MvPolynomial σ K} (hh : h ≠ 0)
    (hq : q ≠ 0) (hq' : q' ≠ 0) (hb : h * q ∈ B) (hb' : h * q' ∈ B) (hne : h * q ≠ h * q') :
    ¬ (m.degree q' ≤ m.degree q) :=
  leadingMonomial_cofactor_not_le hB hh hq hq' hb hb' hne

-- Part B: the Gauss-lemma scalar-strip and the `f₀ ∈ K[x]` ⟺ unit-primPart collapse target.
example {K : Type*} [Field K] {P g : Polynomial (MvPolynomial (Fin 1) K)}
    {c : MvPolynomial (Fin 1) K} (hP : P.IsPrimitive) (hc : c ≠ 0) (hg : g ≠ 0)
    (hdvd : P ∣ Polynomial.C c * g) : P ∣ g :=
  isPrimitive_dvd_of_dvd_C_mul hP hc hg hdvd

example {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K} :
    degreeOf 0 f = 0 ↔
      IsUnit (@Polynomial.primPart _ _ (normalizedGcdMonoidMvPolynomialFinOne K) (lazardView f)) :=
  degreeOf_zero_iff_isUnit_primPart_lazardView

example {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    {htop : Fin B.card} (hmax : ∀ i : Fin B.card, i ≤ htop) (i : Fin B.card) :
    gbCommonContent hB htop ∣ leadingYCoeff (sortedByYDegree hB i) :=
  gbCommonContent_dvd hB hmax i

example {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hbase : HasLazardBaseDvd hB)
    (i : Fin B.card) :
    Polynomial.C (leadingYCoeff (sortedByYDegree hB i)) ∣ lazardView (sortedByYDegree hB i) :=
  lazard_lemma3_dvd hB hbase i

example {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hbase : HasLazardBaseDegreeZero hB)
    (i : Fin B.card) :
    Polynomial.C (leadingYCoeff (sortedByYDegree hB i)) ∣ lazardView (sortedByYDegree hB i) :=
  lazard_lemma3_dvd_of_degreeOf_zero hB hbase i

example {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    {i i1 : Fin B.card} (hii1 : i < i1)
    (hsucc : ∀ j : Fin B.card, j < i1 → j ≤ i)
    (hIH : ∀ j : Fin B.card, j ≤ i →
      Polynomial.C (leadingYCoeff (sortedByYDegree hB i)) ∣ lazardView (sortedByYDegree hB j)) :
    Polynomial.C (leadingYCoeff (sortedByYDegree hB i1))
      ∣ lazardView (sortedByYDegree hB i1) :=
  C_dvd_lazardView_succ hB hii1 hsucc hIH

example {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K} (hf0 : degreeOf 0 f = 0) :
    Polynomial.C (leadingYCoeff f) ∣ lazardView f :=
  C_dvd_lazardView_of_degreeOf_zero hf0

example {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    {d : MvPolynomial (Fin 1) K} {R : MvPolynomial (Fin 2) K} (hRI : R ∈ I) (hR0 : R ≠ 0)
    (hdvd : ∀ b ∈ B, degreeOf 0 b ≤ degreeOf 0 R → Polynomial.C d ∣ lazardView b) :
    Polynomial.C d ∣ lazardView R :=
  C_dvd_lazardView_of_mem_of_dvd_bounded hB hRI hR0 hdvd

example {K : Type*} [Field K] {fj : MvPolynomial (Fin 2) K} {gi gj q : MvPolynomial (Fin 1) K}
    (hq : gj * q = gi) (hfj : Polynomial.C gj ∣ lazardView fj) :
    Polynomial.C gi ∣ Polynomial.C q * lazardView fj :=
  C_dvd_C_mul_lazardView_of_dvd hq hfj

example {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K} (hf : f ≠ 0)
    (hdvd : Polynomial.C (leadingYCoeff f) ∣ lazardView f) :
    IsUnit ((@Polynomial.primPart _ _ (normalizedGcdMonoidMvPolynomialFinOne K)
      (lazardView f)).leadingCoeff) :=
  leadingCoeff_primPart_isUnit_of_C_dvd hf hdvd

-- The base divisibility is the content criterion.
example {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K} :
    Polynomial.C (leadingYCoeff f) ∣ lazardView f ↔
      Associated (@Polynomial.content _ _ (normalizedGcdMonoidMvPolynomialFinOne K) (lazardView f))
        (leadingYCoeff f) :=
  C_dvd_lazardView_iff_content_associated

-- The base obstruction is genuine: `f = xy + 1` refutes a free base case.
example {K : Type*} [Field K] :
    ¬ IsUnit (leadingYCoeff (X 1 * X 0 + 1 : MvPolynomial (Fin 2) K)) :=
  not_isUnit_leadingYCoeff_xyAddOne

example {K : Type*} [Field K] :
    ¬ Polynomial.C (leadingYCoeff (X 1 * X 0 + 1 : MvPolynomial (Fin 2) K))
        ∣ lazardView (X 1 * X 0 + 1 : MvPolynomial (Fin 2) K) :=
  not_C_leadingYCoeff_dvd_lazardView_xyAddOne

-- Restatements against the intended wording.
example {K : Type*} [Field K] {I : Ideal (MvPolynomial σ K)} {B : Set (MvPolynomial σ K)}
    (hB : IsGroebnerBasis m I B) {f : MvPolynomial σ K} (hfI : f ∈ I) (hf0 : f ≠ 0) :
    ∃ b ∈ B, b ≠ 0 ∧ m.degree b ≤ m.degree f :=
  hB.exists_degree_le hfI hf0

example {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {fi fi1 : MvPolynomial (Fin 2) K} (hfiI : fi ∈ I) (hfi1I : fi1 ∈ I)
    (hfi : fi ≠ 0) (hd : degreeOf 0 fi ≤ degreeOf 0 fi1) :
    ∃ P ∈ I, degreeOf 0 P = degreeOf 0 fi1 ∧
      leadingYCoeff P = @gcd _ _ (gcdMonoidMvPolynomialFinOne K)
        (leadingYCoeff fi) (leadingYCoeff fi1) :=
  lazard_gcd_construction hfiI hfi1I hfi hd

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

noncomputable example {K : Type*} [Field K] (m : MonomialOrder σ) (f g : MvPolynomial σ K) :
    MvPolynomial σ K :=
  monomial ((m.degree f ⊔ m.degree g) - m.degree f) (m.leadingCoeff f)⁻¹ * f -
    monomial ((m.degree f ⊔ m.degree g) - m.degree g) (m.leadingCoeff g)⁻¹ * g

example {K : Type*} [Field K] {I : Ideal (MvPolynomial σ K)} {f g : MvPolynomial σ K}
    (hf : f ∈ I) (hg : g ∈ I) : sPolynomial m f g ∈ I :=
  sPolynomial_mem hf hg

example {K : Type*} [Field K] {I : Ideal (MvPolynomial σ K)} {B : Set (MvPolynomial σ K)}
    (hB : IsGroebnerBasis m I B) {b b' : MvPolynomial σ K} (hb : b ∈ B) (hb' : b' ∈ B)
    {g : B →₀ MvPolynomial σ K} {r : MvPolynomial σ K}
    (hgr : sPolynomial m b b' = Finsupp.linearCombination _ (fun x : B => (x : MvPolynomial σ K)) g + r)
    (hrem : ∀ c ∈ r.support, ∀ x ∈ B, ¬ (m.degree x ≤ c)) : r = 0 :=
  hB.sPolynomial_div_remainder_eq_zero hb hb' hgr hrem

example {K : Type*} [Field K] (m : MonomialOrder σ)
    {f g : MvPolynomial σ K} (h : m.degree f = m.degree g) :
    sPolynomial m f g = C (m.leadingCoeff f)⁻¹ * f - C (m.leadingCoeff g)⁻¹ * g :=
  sPolynomial_eq_of_degree_eq m h

example {K : Type*} [Field K] (m : MonomialOrder σ)
    {f g : MvPolynomial σ K} (h : m.degree f = m.degree g) (hf : f ≠ 0) (hg : g ≠ 0)
    (hδ : m.degree f ≠ 0) :
    m.degree (sPolynomial m f g) ≺[m] m.degree f :=
  sPolynomial_degree_lt_of_degree_eq m h hf hg hδ

example {K : Type*} [Field K] (m : MonomialOrder σ) {n : ℕ}
    {p : Fin (n + 1) → MvPolynomial σ K} {δ : σ →₀ ℕ}
    (hδ : ∀ i, m.degree (p i) = δ) (hp : ∀ i, p i ≠ 0)
    (hcancel : m.degree (∑ i, p i) ≺[m] δ) :
    (∑ i, p i = ∑ i ∈ Finset.univ.erase (Fin.last n),
        m.leadingCoeff (p i) • sPolynomial m (p i) (p (Fin.last n))) ∧
      ∀ i ≠ Fin.last n, m.degree (sPolynomial m (p i) (p (Fin.last n))) ≺[m] δ :=
  cancellation_lemma m hδ hp hcancel

example {K : Type*} [Field K] (m : MonomialOrder σ) {f g : MvPolynomial σ K}
    (hf : f ≠ 0) (hg : g ≠ 0) :
    sPolynomial m f g = (m.leadingCoeff f * m.leadingCoeff g)⁻¹ • m.sPolynomial f g :=
  sPolynomial_eq_inv_smul_mathlib m hf hg

example {K : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (B : Finset (MvPolynomial σ K))
    (hBI : ∀ b ∈ B, b ∈ I) (hlc : ∀ b ∈ B, IsUnit (m.leadingCoeff b))
    (hspan : Ideal.span (↑B : Set (MvPolynomial σ K)) = I)
    (hS : ∀ b ∈ B, ∀ b' ∈ B, ∃ q : B → MvPolynomial σ K,
      sPolynomial m b b' = ∑ c ∈ B.attach, q c * (c : MvPolynomial σ K) ∧
        ∀ c, m.degree (q c * (c : MvPolynomial σ K)) ≼[m] m.degree (sPolynomial m b b')) :
    IsGroebnerBasis m I (↑B : Set (MvPolynomial σ K)) :=
  isGroebnerBasis_of_sPolynomial_reducesToZero I B hBI hlc hspan hS

example {K : Type*} [Field K] (m : MonomialOrder σ) {B : Finset (MvPolynomial σ K)}
    (hB : ∀ b ∈ B, IsUnit (m.leadingCoeff b)) :
    Ideal.span (↑(buchbergerStep m hB) : Set (MvPolynomial σ K))
      = Ideal.span (↑B : Set (MvPolynomial σ K)) :=
  span_buchbergerStep m hB

example {K : Type*} [Field K] (m : MonomialOrder σ) {B : Finset (MvPolynomial σ K)}
    (hB : ∀ b ∈ B, IsUnit (m.leadingCoeff b)) (hne : buchbergerStep m hB ≠ B) :
    leadTermIdeal m B < leadTermIdeal m (buchbergerStep m hB) :=
  leadTermIdeal_lt_of_ne m hB hne

example {K : Type*} [Field K] [Finite σ] (m : MonomialOrder σ) {B : Finset (MvPolynomial σ K)}
    (hB : ∀ b ∈ B, IsUnit (m.leadingCoeff b)) (hfix : buchbergerStep m hB = B) :
    IsGroebnerBasis m (Ideal.span (↑B : Set (MvPolynomial σ K))) (↑B : Set (MvPolynomial σ K)) :=
  isGroebnerBasis_of_buchbergerStep_eq m hB hfix

example {K : Type*} [Field K] [Finite σ] (m : MonomialOrder σ) {B : Finset (MvPolynomial σ K)}
    (hB : ∀ b ∈ B, IsUnit (m.leadingCoeff b)) :
    ∃ G : Finset (MvPolynomial σ K), (↑B : Set (MvPolynomial σ K)) ⊆ ↑G ∧
      Ideal.span (↑G : Set (MvPolynomial σ K)) = Ideal.span (↑B : Set (MvPolynomial σ K)) ∧
      IsGroebnerBasis m (Ideal.span (↑B : Set (MvPolynomial σ K))) (↑G : Set (MvPolynomial σ K)) :=
  buchberger_terminates_correct m hB

/-! ## The `P·Gₖ₊₁` divide-out: from an arbitrary reduced GB to the no-common-factor case

Lazard (1985), Theorem 1 proof (p.262): "Let `P = primpart(GCD(f₀,…,fₖ))` and `Gₖ₊₁ =
content(GCD(f₀,…,fₖ))`. … Thus we may divide by `P·Gₖ₊₁` and suppose that the `fᵢ` have no common
divisors." The single common factor to divide out is `H := GCD(f₀,…,fₖ) = P·Gₖ₊₁`, the gcd of the
whole basis in `K[x][y]`. Here `H` is taken in the `lazardView` ring `K[x][y] = Polynomial
(MvPolynomial (Fin 1) K)` (a UFD, hence `GCDMonoid`) as `gbYGcd hB := ⨅ᵍᶜᵈ_i lazardView (sorted i)`,
its cofactors `lazardView (sorted i) / H` are produced by `gbYGcd_dvd`, and their gcd is a **unit**
(`gbYGcd_cofactor_gcd_isUnit`) — exactly `HasNoCommonYFactor` for the divided family. So the
structural conclusions proved unconditional under `HasNoCommonYFactor` apply to every divided
arbitrary reduced bivariate Gröbner basis. -/

open scoped Classical in
/-- A chosen `NormalizedGCDMonoid` on the `lazardView` ring `K[x][y] = Polynomial (MvPolynomial
(Fin 1) K)` (a UFD over the UFD `K[x]`, hence a normalized GCD domain) — supplies the `Finset.gcd`
over the basis. Used as a local `letI`; not a global instance. -/
@[reducible] noncomputable def gcdMonoidLazardRing (K : Type*) [Field K] :
    NormalizedGCDMonoid (Polynomial (MvPolynomial (Fin 1) K)) :=
  letI := UniqueFactorizationMonoid.normalizationMonoid
    (α := Polynomial (MvPolynomial (Fin 1) K))
  UniqueFactorizationMonoid.toNormalizedGCDMonoid _

open scoped Classical in
/-- **The common `K[x][y]`-factor of the basis** (Lazard's `GCD(f₀,…,fₖ) = P·Gₖ₊₁`): the gcd of the
`lazardView`s of all sorted basis elements, taken in `K[x][y]`. Dividing it out yields the
no-common-factor case. -/
noncomputable def gbYGcd {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K))) :
    Polynomial (MvPolynomial (Fin 1) K) :=
  letI := gcdMonoidLazardRing K
  (Finset.univ : Finset (Fin B.card)).gcd (fun i => lazardView (sortedByYDegree hB i))

/-- **`gbYGcd` divides every basis view** (`H ∣ lazardView (sorted i)`): the gcd of a family divides
each member (`Finset.gcd_dvd`). -/
theorem gbYGcd_dvd {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (i : Fin B.card) :
    @Dvd.dvd _ _ (gbYGcd hB) (lazardView (sortedByYDegree hB i)) := by
  letI := gcdMonoidLazardRing K
  exact Finset.gcd_dvd (Finset.mem_univ i)

open scoped Classical in
/-- **The divided basis cofactors** (`b'ᵢ` in `lazardView`-space): the `K[x][y]`-cofactor family with
`lazardView (sorted i) = gbYGcd hB * gbYGcdCofactor hB i` and gcd a unit. From `Finset.extract_gcd`
(nonempty `B`), which produces both the cofactors and their coprimality. -/
noncomputable def gbYGcdCofactor {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hne : (Finset.univ : Finset (Fin B.card)).Nonempty) :
    Fin B.card → Polynomial (MvPolynomial (Fin 1) K) :=
  letI := gcdMonoidLazardRing K
  (Finset.extract_gcd (fun i => lazardView (sortedByYDegree hB i)) hne).choose

/-- **The divided-basis factorization** (Lazard's `fᵢ = H·b'ᵢ`, view form): `lazardView (sorted i) =
gbYGcd hB * gbYGcdCofactor hB i`, the gcd times its cofactor (`Finset.extract_gcd`). -/
theorem gbYGcd_mul_cofactor {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hne : (Finset.univ : Finset (Fin B.card)).Nonempty) (i : Fin B.card) :
    lazardView (sortedByYDegree hB i) = gbYGcd hB * gbYGcdCofactor hB hne i := by
  letI := gcdMonoidLazardRing K
  exact (Finset.extract_gcd (fun i => lazardView (sortedByYDegree hB i)) hne).choose_spec.1 i
    (Finset.mem_univ i)

/-- **The cofactors are coprime** (Lazard's "no common factor", normalized form): `univ.gcd
(gbYGcdCofactor hB hne) = 1` — dividing out the gcd leaves a unit gcd (`Finset.extract_gcd`). -/
theorem gbYGcdCofactor_gcd_eq_one {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hne : (Finset.univ : Finset (Fin B.card)).Nonempty) :
    letI := gcdMonoidLazardRing K
    (Finset.univ : Finset (Fin B.card)).gcd (gbYGcdCofactor hB hne) = 1 := by
  letI := gcdMonoidLazardRing K
  exact (Finset.extract_gcd (fun i => lazardView (sortedByYDegree hB i)) hne).choose_spec.2

/-- **The divided basis has no common `y`-factor** (sub-goal 3, Lazard's `P = Gₖ₊₁ = 1`): every
`K[x][y]`-divisor common to all cofactors `gbYGcdCofactor hB hne i` is a unit — it divides their gcd
`= 1` (`gbYGcdCofactor_gcd_eq_one`). This is exactly `HasNoCommonYFactor` for the divided family. -/
theorem cofactor_hasNoCommonYFactor {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hne : (Finset.univ : Finset (Fin B.card)).Nonempty)
    (P : Polynomial (MvPolynomial (Fin 1) K))
    (hP : ∀ i : Fin B.card, P ∣ gbYGcdCofactor hB hne i) : IsUnit P := by
  letI := gcdMonoidLazardRing K
  have hdvd : P ∣ (Finset.univ : Finset (Fin B.card)).gcd (gbYGcdCofactor hB hne) :=
    Finset.dvd_gcd (fun i _ => hP i)
  rw [gbYGcdCofactor_gcd_eq_one hB hne] at hdvd
  exact isUnit_of_dvd_one hdvd

/-- **The common factor pulled back to `K[x,y]`** (Lazard's `H = P·Gₖ₊₁` as a bivariate polynomial):
`(finSuccEquiv K 1).symm (gbYGcd hB)`, the divisor `H` that divides every basis element directly in
`MvPolynomial (Fin 2) K`. -/
noncomputable def gbCommonYFactor {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K))) :
    MvPolynomial (Fin 2) K :=
  (finSuccEquiv K 1).symm (gbYGcd hB)

/-- **The pullback's `lazardView` is `gbYGcd`** (`lazardView H = gbYGcd hB`): `lazardView` is
`finSuccEquiv K 1`, so its `symm` is the inverse (`apply_symm_apply`). -/
@[simp] theorem lazardView_gbCommonYFactor {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K))) :
    lazardView (gbCommonYFactor hB) = gbYGcd hB := by
  rw [gbCommonYFactor, lazardView, AlgEquiv.apply_symm_apply]

/-- **The common factor `H` divides every basis element** (Lazard's `H ∣ fᵢ`, bivariate form): from
`gbYGcd hB ∣ lazardView (sorted i)` (`gbYGcd_dvd`), transported back through the ring iso `lazardView`
(`map_dvd_iff`). This is the divisor Lazard's Theorem 1 proof divides the basis by. -/
theorem gbCommonYFactor_dvd {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (i : Fin B.card) :
    gbCommonYFactor hB ∣ sortedByYDegree hB i := by
  letI := gcdMonoidLazardRing K
  rw [← map_dvd_iff (finSuccEquiv K 1)]
  show lazardView (gbCommonYFactor hB) ∣ lazardView (sortedByYDegree hB i)
  rw [lazardView_gbCommonYFactor]
  exact gbYGcd_dvd hB i

/-- **Lazard's Theorem 1, the `P·Gₖ₊₁` divide-out** (capstone, the general bivariate case). For an
**arbitrary** (nonempty) reduced bivariate Gröbner basis, there is a common factor `H` (the gcd of the
basis, `gbCommonYFactor`) dividing every element, and a cofactor family `b'ᵢ` with `fᵢ = H·b'ᵢ` whose
views `lazardView`-coincide with the divided basis and have **no common `y`-factor** — exactly the
state in which the structural conclusions (`lazard_Pk_eq_Rk_Sk_of_hasNoCommonYFactor`, the descent)
hold unconditionally. So every arbitrary reduced bivariate GB reduces, by this divide-out, to the
no-common-factor case where Lazard's structure theorem applies. -/
theorem lazard_thm1_divideOut {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hne : (Finset.univ : Finset (Fin B.card)).Nonempty) :
    ∃ (H : MvPolynomial (Fin 2) K)
      (b' : Fin B.card → Polynomial (MvPolynomial (Fin 1) K)),
      (∀ i, H ∣ sortedByYDegree hB i) ∧
        (∀ i, lazardView (sortedByYDegree hB i) = lazardView H * b' i) ∧
        (∀ P : Polynomial (MvPolynomial (Fin 1) K),
          (∀ i, P ∣ b' i) → IsUnit P) :=
  ⟨gbCommonYFactor hB, gbYGcdCofactor hB hne, gbCommonYFactor_dvd hB,
    fun i => by rw [lazardView_gbCommonYFactor]; exact gbYGcd_mul_cofactor hB hne i,
    cofactor_hasNoCommonYFactor hB hne⟩

/-- **The divide-out delivers `HasNoCommonYFactor` to the divided reduced GB** (the bridge to the
unconditional structural conclusions). If `hB'` is *any* reduced GB whose sorted basis views
**recover every** divide-out cofactor up to associates — each `gbYGcdCofactor hB hne i` is associated
to some view `lazardView (sorted hB' j)` (a reduced re-presentation of the divided family
`{lazardView (sorted i) / H}` rescales only by units, so the divisor lattices agree) — then
`HasNoCommonYFactor hB'` holds: a common divisor `P` of all `hB'`-views divides each cofactor (via the
association), hence divides the cofactors' gcd `= 1` (`cofactor_hasNoCommonYFactor`). This is the exact
predicate `lazard_Pk_eq_Rk_Sk_of_hasNoCommonYFactor`/`lazard_lemma3_dvd_of_hasNoCommonYFactor` consume,
so the full structural decomposition `Pₖ = Rₖ·Sₖ` applies to the divided basis of an arbitrary GB. -/
theorem hasNoCommonYFactor_of_cofactor_associated {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hne : (Finset.univ : Finset (Fin B.card)).Nonempty)
    {I' : Ideal (MvPolynomial (Fin 2) K)} {B' : Finset (MvPolynomial (Fin 2) K)}
    (hB' : IsReducedGroebnerBasis MonomialOrder.lex I' (↑B' : Set (MvPolynomial (Fin 2) K)))
    (hassoc : ∀ i : Fin B.card, ∃ j : Fin B'.card,
      Associated (gbYGcdCofactor hB hne i) (lazardView (sortedByYDegree hB' j))) :
    HasNoCommonYFactor hB' := by
  intro P hP
  refine cofactor_hasNoCommonYFactor hB hne P (fun i => ?_)
  obtain ⟨j, hij⟩ := hassoc i
  -- `P ∣ lazardView (sorted hB' j) ∼ cofactor i`, so `P ∣ cofactor i`.
  exact (hP j).trans hij.symm.dvd

/-- **Lazard's `Pₖ = Rₖ·Sₖ` for an arbitrary reduced bivariate GB, through the divide-out** (the full
Theorem 1 structural conclusion, general case). For any reduced GB `hB'` that re-presents the
divide-out cofactors of `hB` (the `hassoc` recovery hypothesis), every sorted element of `hB'` splits
as `lazardView fⱼ = C(cⱼ)·Sⱼ` with content `cⱼ ∼ leadingYCoeff fⱼ`, `Sⱼ` primitive and monic in `y`.
Chains `hasNoCommonYFactor_of_cofactor_associated` into `lazard_Pk_eq_Rk_Sk_of_hasNoCommonYFactor`, so
the structure theorem holds for the general case once the basis is divided by `gbCommonYFactor hB`. -/
theorem lazard_Pk_eq_Rk_Sk_of_divideOut {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hne : (Finset.univ : Finset (Fin B.card)).Nonempty)
    {I' : Ideal (MvPolynomial (Fin 2) K)} {B' : Finset (MvPolynomial (Fin 2) K)}
    (hB' : IsReducedGroebnerBasis MonomialOrder.lex I' (↑B' : Set (MvPolynomial (Fin 2) K)))
    (hassoc : ∀ i : Fin B.card, ∃ j : Fin B'.card,
      Associated (gbYGcdCofactor hB hne i) (lazardView (sortedByYDegree hB' j)))
    (j : Fin B'.card) :
    ∃ S : Polynomial (MvPolynomial (Fin 1) K),
      lazardView (sortedByYDegree hB' j) = Polynomial.C (@Polynomial.content _ _
          (normalizedGcdMonoidMvPolynomialFinOne K) (lazardView (sortedByYDegree hB' j))) * S ∧
        Associated (@Polynomial.content _ _ (normalizedGcdMonoidMvPolynomialFinOne K)
          (lazardView (sortedByYDegree hB' j))) (leadingYCoeff (sortedByYDegree hB' j)) ∧
        S.IsPrimitive ∧ IsUnit S.leadingCoeff :=
  lazard_Pk_eq_Rk_Sk_of_hasNoCommonYFactor hB'
    (hasNoCommonYFactor_of_cofactor_associated hB hne hB' hassoc) j

-- The `P·Gₖ₊₁` divide-out (Lazard's Theorem 1, general case).
example {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (i : Fin B.card) :
    @Dvd.dvd _ _ (gbYGcd hB) (lazardView (sortedByYDegree hB i)) :=
  gbYGcd_dvd hB i

example {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hne : (Finset.univ : Finset (Fin B.card)).Nonempty) (i : Fin B.card) :
    lazardView (sortedByYDegree hB i) = gbYGcd hB * gbYGcdCofactor hB hne i :=
  gbYGcd_mul_cofactor hB hne i

example {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hne : (Finset.univ : Finset (Fin B.card)).Nonempty)
    (P : Polynomial (MvPolynomial (Fin 1) K))
    (hP : ∀ i : Fin B.card, P ∣ gbYGcdCofactor hB hne i) : IsUnit P :=
  cofactor_hasNoCommonYFactor hB hne P hP

example {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (i : Fin B.card) :
    gbCommonYFactor hB ∣ sortedByYDegree hB i :=
  gbCommonYFactor_dvd hB i

example {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hne : (Finset.univ : Finset (Fin B.card)).Nonempty) :
    ∃ (H : MvPolynomial (Fin 2) K)
      (b' : Fin B.card → Polynomial (MvPolynomial (Fin 1) K)),
      (∀ i, H ∣ sortedByYDegree hB i) ∧
        (∀ i, lazardView (sortedByYDegree hB i) = lazardView H * b' i) ∧
        (∀ P : Polynomial (MvPolynomial (Fin 1) K), (∀ i, P ∣ b' i) → IsUnit P) :=
  lazard_thm1_divideOut hB hne

-- The divide-out delivers `HasNoCommonYFactor` to the divided GB, hence `Pₖ = Rₖ·Sₖ`.
example {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hne : (Finset.univ : Finset (Fin B.card)).Nonempty)
    {I' : Ideal (MvPolynomial (Fin 2) K)} {B' : Finset (MvPolynomial (Fin 2) K)}
    (hB' : IsReducedGroebnerBasis MonomialOrder.lex I' (↑B' : Set (MvPolynomial (Fin 2) K)))
    (hassoc : ∀ i : Fin B.card, ∃ j : Fin B'.card,
      Associated (gbYGcdCofactor hB hne i) (lazardView (sortedByYDegree hB' j))) :
    HasNoCommonYFactor hB' :=
  hasNoCommonYFactor_of_cofactor_associated hB hne hB' hassoc

example {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hne : (Finset.univ : Finset (Fin B.card)).Nonempty)
    {I' : Ideal (MvPolynomial (Fin 2) K)} {B' : Finset (MvPolynomial (Fin 2) K)}
    (hB' : IsReducedGroebnerBasis MonomialOrder.lex I' (↑B' : Set (MvPolynomial (Fin 2) K)))
    (hassoc : ∀ i : Fin B.card, ∃ j : Fin B'.card,
      Associated (gbYGcdCofactor hB hne i) (lazardView (sortedByYDegree hB' j)))
    (j : Fin B'.card) :
    ∃ S : Polynomial (MvPolynomial (Fin 1) K),
      lazardView (sortedByYDegree hB' j) = Polynomial.C (@Polynomial.content _ _
          (normalizedGcdMonoidMvPolynomialFinOne K) (lazardView (sortedByYDegree hB' j))) * S ∧
        Associated (@Polynomial.content _ _ (normalizedGcdMonoidMvPolynomialFinOne K)
          (lazardView (sortedByYDegree hB' j))) (leadingYCoeff (sortedByYDegree hB' j)) ∧
        S.IsPrimitive ∧ IsUnit S.leadingCoeff :=
  lazard_Pk_eq_Rk_Sk_of_divideOut hB hne hB' hassoc j

/-! ## The divided family is a reduced Gröbner basis (discharging `hassoc`)

Lazard (1985), Theorem 1, final step: the divided family `{fᵢ/H}` (`H = gbCommonYFactor hB` the common
`K[x][y]`-factor) is itself a **reduced** Gröbner basis of the quotient ideal `I' := span {fᵢ/H}`, and
its leading monomials are those of `B` shifted down by `LM(H)` — an order-isomorphism preserving the
GB and reducedness structure. The arithmetic core is the membership equivalence `g ∈ ⟨fᵢ/H⟩ ⟺ H·g ∈
⟨fᵢ⟩` (cancel `H` over the domain). This discharges the `hassoc` recovery hypothesis of
`lazard_Pk_eq_Rk_Sk_of_divideOut`, making `Pₖ = Rₖ·Sₖ` **unconditional** for an arbitrary reduced
bivariate Gröbner basis. -/

/-- **Membership in the divided ideal** (cancel the common factor `H`, domain). For a finite family
`q : ι → MvPolynomial σ K` and `H ≠ 0`, a polynomial `g` lies in `span (range q)` iff `H·g` lies in
`span (range (H · q))`: forward multiplies a representation by `H`; backward cancels `H`
(`mul_left_cancel₀`). -/
theorem mem_span_divided_iff {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    (q : ι → MvPolynomial σ K) {H : MvPolynomial σ K} (hH : H ≠ 0) (g : MvPolynomial σ K) :
    g ∈ Ideal.span (Set.range q) ↔
      H * g ∈ Ideal.span (Set.range (fun i => H * q i)) := by
  classical
  constructor
  · -- `g = ∑ cᵢ·qᵢ ⟹ H·g = ∑ cᵢ·(H·qᵢ)`.
    intro hg
    rw [Ideal.mem_span_range_iff_exists_fun] at hg ⊢
    obtain ⟨c, hc⟩ := hg
    refine ⟨c, ?_⟩
    rw [← hc, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  · -- `H·g = ∑ cᵢ·(H·qᵢ) = H·(∑ cᵢ·qᵢ) ⟹ g = ∑ cᵢ·qᵢ` (cancel `H`).
    intro hHg
    rw [Ideal.mem_span_range_iff_exists_fun] at hHg ⊢
    obtain ⟨c, hc⟩ := hHg
    refine ⟨c, ?_⟩
    apply mul_left_cancel₀ hH
    rw [← hc, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)

/-- **The common `y`-factor `gbYGcd` is nonzero**: the gcd of the nonzero basis views (a nonempty
family in the domain `K[x][y]`) is nonzero (`Finset.gcd_eq_zero_iff`). -/
theorem gbYGcd_ne_zero {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hne : (Finset.univ : Finset (Fin B.card)).Nonempty) : gbYGcd hB ≠ 0 := by
  letI := gcdMonoidLazardRing K
  rw [gbYGcd, Ne, Finset.gcd_eq_zero_iff]
  push Not
  obtain ⟨i, hi⟩ := hne
  exact ⟨i, hi, lazardView_eq_zero_iff.not.mpr (hB.ne_zero (sortedByYDegree_mem hB i))⟩

/-- **The bivariate common factor `H = gbCommonYFactor hB` is nonzero**: its `lazardView` is the
nonzero `gbYGcd hB` (`gbYGcd_ne_zero`), and `lazardView` is injective. -/
theorem gbCommonYFactor_ne_zero {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hne : (Finset.univ : Finset (Fin B.card)).Nonempty) : gbCommonYFactor hB ≠ 0 := by
  intro h0
  apply gbYGcd_ne_zero hB hne
  rw [← lazardView_gbCommonYFactor hB, h0, lazardView, map_zero]

/-- **The divided basis cofactor, pulled back to `K[x,y]`** (Lazard's `qᵢ = fᵢ/H`): the bivariate
preimage `(finSuccEquiv K 1).symm (gbYGcdCofactor hB hne i)` of the `K[x][y]`-cofactor. Its
`lazardView` is `gbYGcdCofactor hB hne i`, and `gbCommonYFactor hB * dividedBasis hB hne i =
sortedByYDegree hB i`. -/
noncomputable def dividedBasis {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hne : (Finset.univ : Finset (Fin B.card)).Nonempty) (i : Fin B.card) :
    MvPolynomial (Fin 2) K :=
  (finSuccEquiv K 1).symm (gbYGcdCofactor hB hne i)

/-- `lazardView (dividedBasis hB hne i) = gbYGcdCofactor hB hne i` (`apply_symm_apply`). -/
@[simp] theorem lazardView_dividedBasis {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hne : (Finset.univ : Finset (Fin B.card)).Nonempty) (i : Fin B.card) :
    lazardView (dividedBasis hB hne i) = gbYGcdCofactor hB hne i := by
  rw [dividedBasis, lazardView, AlgEquiv.apply_symm_apply]

/-- **The divided-basis factorization, bivariate form** (`H · qᵢ = fᵢ`): `gbCommonYFactor hB *
dividedBasis hB hne i = sortedByYDegree hB i`, the pullback of `gbYGcd_mul_cofactor` through the ring
iso `finSuccEquiv` (`lazardView` injective). -/
theorem gbCommonYFactor_mul_dividedBasis {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hne : (Finset.univ : Finset (Fin B.card)).Nonempty) (i : Fin B.card) :
    gbCommonYFactor hB * dividedBasis hB hne i = sortedByYDegree hB i := by
  apply lazardView_injective
  rw [lazardView, map_mul, ← lazardView, ← lazardView, lazardView_gbCommonYFactor,
    lazardView_dividedBasis]
  exact (gbYGcd_mul_cofactor hB hne i).symm

/-- **The divided basis is nonzero** (`qᵢ ≠ 0`): `H · qᵢ = fᵢ ≠ 0` (`gbCommonYFactor_mul_dividedBasis`,
basis elements nonzero). -/
theorem dividedBasis_ne_zero {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hne : (Finset.univ : Finset (Fin B.card)).Nonempty) (i : Fin B.card) :
    dividedBasis hB hne i ≠ 0 := by
  intro h0
  exact hB.ne_zero (sortedByYDegree_mem hB i)
    (by rw [← gbCommonYFactor_mul_dividedBasis hB hne i, h0, mul_zero])

/-- **`lazardView` of a `K`-scalar multiple**: `lazardView (C c * f) = Polynomial.C (C c) * lazardView f`
(`finSuccEquiv` is a `K`-algebra hom, `finSuccEquiv_comp_C_eq_C`). -/
theorem lazardView_C_scalar_mul {K : Type*} [Field K] (c : K) (f : MvPolynomial (Fin 2) K) :
    lazardView (MvPolynomial.C c * f) = Polynomial.C (MvPolynomial.C c) * lazardView f := by
  rw [lazardView, map_mul, lazardView]
  congr 1
  have h2 := RingHom.congr_fun (finSuccEquiv_comp_C_eq_C (R := K) 1) c
  simp only [RingHom.comp_apply] at h2
  exact ((finSuccEquiv K 1).symm_apply_eq.mp h2).symm

/-- **The monic divided basis** (`fᵢ/H` rescaled to lex-leading-coefficient `1`): the divided cofactor
`dividedBasis hB hne i` scaled by `(lex.leadingCoeff)⁻¹`. A unit-scalar multiple of the cofactor, so
its `lazardView` is *associated* to `gbYGcdCofactor hB hne i` — the form needed for a *reduced* GB. -/
noncomputable def monicDividedBasis {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hne : (Finset.univ : Finset (Fin B.card)).Nonempty) (i : Fin B.card) :
    MvPolynomial (Fin 2) K :=
  MvPolynomial.C (MonomialOrder.lex.leadingCoeff (dividedBasis hB hne i))⁻¹ * dividedBasis hB hne i

/-- The lex leading coefficient of `dividedBasis hB hne i` is nonzero (`dividedBasis_ne_zero`). -/
theorem leadingCoeff_dividedBasis_ne_zero {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hne : (Finset.univ : Finset (Fin B.card)).Nonempty) (i : Fin B.card) :
    MonomialOrder.lex.leadingCoeff (dividedBasis hB hne i) ≠ 0 :=
  MonomialOrder.lex.leadingCoeff_ne_zero_iff.mpr (dividedBasis_ne_zero hB hne i)

/-- `monicDividedBasis hB hne i ≠ 0` (unit-scalar multiple of the nonzero `dividedBasis`). -/
theorem monicDividedBasis_ne_zero {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hne : (Finset.univ : Finset (Fin B.card)).Nonempty) (i : Fin B.card) :
    monicDividedBasis hB hne i ≠ 0 := by
  rw [monicDividedBasis, ← smul_eq_C_mul, smul_ne_zero_iff]
  exact ⟨inv_ne_zero (leadingCoeff_dividedBasis_ne_zero hB hne i), dividedBasis_ne_zero hB hne i⟩

/-- `lex.degree (monicDividedBasis hB hne i) = lex.degree (dividedBasis hB hne i)`: scaling by the
nonzero constant `(leadingCoeff)⁻¹` preserves the leading monomial (`degree_C_mul`). -/
theorem degree_monicDividedBasis {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hne : (Finset.univ : Finset (Fin B.card)).Nonempty) (i : Fin B.card) :
    MonomialOrder.lex.degree (monicDividedBasis hB hne i)
      = MonomialOrder.lex.degree (dividedBasis hB hne i) :=
  degree_C_mul MonomialOrder.lex (inv_ne_zero (leadingCoeff_dividedBasis_ne_zero hB hne i)) _

/-- `lex.leadingCoeff (monicDividedBasis hB hne i) = 1`: the scaling by `(leadingCoeff)⁻¹` normalizes
the leading coefficient to `1` (`leadingCoeff_C_mul`, field inverse). -/
theorem leadingCoeff_monicDividedBasis {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hne : (Finset.univ : Finset (Fin B.card)).Nonempty) (i : Fin B.card) :
    MonomialOrder.lex.leadingCoeff (monicDividedBasis hB hne i) = 1 := by
  rw [monicDividedBasis, leadingCoeff_C_mul MonomialOrder.lex
    (inv_ne_zero (leadingCoeff_dividedBasis_ne_zero hB hne i)),
    inv_mul_cancel₀ (leadingCoeff_dividedBasis_ne_zero hB hne i)]

/-- **`lazardView (monicDividedBasis hB hne i)` is associated to the cofactor**
`gbYGcdCofactor hB hne i`: they differ by the unit scalar `C (C (leadingCoeff)⁻¹)`. So the divided
ideal's divisor lattice agrees with the cofactors'. -/
theorem lazardView_monicDividedBasis_associated {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hne : (Finset.univ : Finset (Fin B.card)).Nonempty) (i : Fin B.card) :
    Associated (gbYGcdCofactor hB hne i) (lazardView (monicDividedBasis hB hne i)) := by
  rw [monicDividedBasis, lazardView_C_scalar_mul, lazardView_dividedBasis]
  -- `C (C (leadingCoeff)⁻¹)` is a unit (nonzero field constant lifted twice).
  refine associated_unit_mul_right _ _ (Polynomial.isUnit_C.mpr ?_)
  exact (inv_ne_zero (leadingCoeff_dividedBasis_ne_zero hB hne i)).isUnit.map MvPolynomial.C

open scoped Classical in
/-- **The quotient ideal of the divided basis** (`I' := span {fᵢ/H}`): the ideal generated by the
monic divided basis `{monicDividedBasis hB hne i}` in `MvPolynomial (Fin 2) K`. -/
noncomputable def dividedIdeal {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hne : (Finset.univ : Finset (Fin B.card)).Nonempty) : Ideal (MvPolynomial (Fin 2) K) :=
  Ideal.span (Set.range (monicDividedBasis hB hne))

/-- **`span {monicDividedBasis} = span {dividedBasis}`**: the monic basis differs from the raw divided
cofactor only by the unit scalar `C (leadingCoeff)⁻¹`, so the two ranges span the same ideal. -/
theorem span_monicDividedBasis_eq {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hne : (Finset.univ : Finset (Fin B.card)).Nonempty) :
    Ideal.span (Set.range (monicDividedBasis hB hne))
      = Ideal.span (Set.range (dividedBasis hB hne)) := by
  apply le_antisymm <;> rw [Ideal.span_le] <;> rintro _ ⟨i, rfl⟩
  · -- `monicDividedBasis i = C c⁻¹ · dividedBasis i ∈ ⟨dividedBasis⟩`.
    rw [monicDividedBasis, SetLike.mem_coe]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · -- `dividedBasis i = C c · monicDividedBasis i ∈ ⟨monicDividedBasis⟩`.
    rw [SetLike.mem_coe]
    have : dividedBasis hB hne i
        = MvPolynomial.C (MonomialOrder.lex.leadingCoeff (dividedBasis hB hne i))
            * monicDividedBasis hB hne i := by
      rw [monicDividedBasis, ← mul_assoc, ← C_mul,
        mul_inv_cancel₀ (leadingCoeff_dividedBasis_ne_zero hB hne i), C_1, one_mul]
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

/-- **The divided-ideal membership equivalence** (`g ∈ I' ⟺ H·g ∈ I`). Chains `mem_span_divided_iff`
(cancel `H`) with `H·(fᵢ/H) = fᵢ` (`gbCommonYFactor_mul_dividedBasis`) and `range (sortedByYDegree) =
↑B`, `span ↑B = I` (`hB` is a GB). The right side `H·g` lands in the *original* GB ideal `I`. -/
theorem mem_dividedIdeal_iff {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hne : (Finset.univ : Finset (Fin B.card)).Nonempty) (g : MvPolynomial (Fin 2) K) :
    g ∈ dividedIdeal hB hne ↔ gbCommonYFactor hB * g ∈ I := by
  classical
  rw [dividedIdeal, span_monicDividedBasis_eq hB hne,
    mem_span_divided_iff (dividedBasis hB hne) (gbCommonYFactor_ne_zero hB hne) g]
  -- `(fun i => H · dividedBasis i) = sortedByYDegree hB` as functions, so the ranges coincide.
  have hfun : (fun i => gbCommonYFactor hB * dividedBasis hB hne i) = sortedByYDegree hB :=
    funext (fun i => gbCommonYFactor_mul_dividedBasis hB hne i)
  rw [hfun, range_sortedByYDegree hB, hB.isGroebnerBasis.span_eq]

/-- **Leading-monomial domination for the divided ideal** (the `hdvd` core of the GB property). For
nonzero `g ∈ I'`, `H·g` is a nonzero element of the original GB ideal `I`, so some basis element
`sortedByYDegree hB i_b = H·(fᵢ_b/H)` has `lex.degree ≤ lex.degree (H·g)`; cancelling the common
`lex.degree H` shift (`degree_mul`, domain) gives `lex.degree (monicDividedBasis i_b) ≤ lex.degree g`. -/
theorem exists_degree_le_dividedIdeal {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hne : (Finset.univ : Finset (Fin B.card)).Nonempty)
    {g : MvPolynomial (Fin 2) K} (hgI : g ∈ dividedIdeal hB hne) (hg0 : g ≠ 0) :
    ∃ b ∈ Set.range (monicDividedBasis hB hne),
      MonomialOrder.lex.degree b ≤ MonomialOrder.lex.degree g := by
  have hH : gbCommonYFactor hB ≠ 0 := gbCommonYFactor_ne_zero hB hne
  have hHg0 : gbCommonYFactor hB * g ≠ 0 := mul_ne_zero hH hg0
  have hHgI : gbCommonYFactor hB * g ∈ I := (mem_dividedIdeal_iff hB hne g).mp hgI
  obtain ⟨b, hbB, _, hble⟩ := hB.isGroebnerBasis.exists_degree_le hHgI hHg0
  -- `b = sortedByYDegree hB i_b = H · dividedBasis i_b`.
  rw [← range_sortedByYDegree hB] at hbB
  obtain ⟨ib, rfl⟩ := hbB
  rw [← gbCommonYFactor_mul_dividedBasis hB hne ib] at hble
  -- cancel the `lex.degree H` shift on both sides.
  rw [degree_mul hH (dividedBasis_ne_zero hB hne ib), degree_mul hH hg0,
    add_le_add_iff_left] at hble
  exact ⟨monicDividedBasis hB hne ib, ⟨ib, rfl⟩,
    (degree_monicDividedBasis hB hne ib).le.trans hble⟩

/-- **The monic divided family is a Gröbner basis of the quotient ideal `I'`** (Lazard Thm 1, Part C):
`IsGroebnerBasis lex I' {fᵢ/H}`. The leading coefficients are `1` (monic), the family generates `I'`
(by definition), and leading-monomial domination holds (`exists_degree_le_dividedIdeal`), so
`isGroebnerBasis_of_exists_leadingMonomial_le` applies. -/
theorem isGroebnerBasis_dividedBasis {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hne : (Finset.univ : Finset (Fin B.card)).Nonempty) :
    IsGroebnerBasis MonomialOrder.lex (dividedIdeal hB hne)
      (Set.range (monicDividedBasis hB hne)) := by
  refine isGroebnerBasis_of_exists_leadingMonomial_le ?_ ?_ ?_
  · -- `B' ⊆ I'`.
    rintro _ ⟨i, rfl⟩
    exact Ideal.subset_span ⟨i, rfl⟩
  · -- unit leading coefficients (`= 1`).
    rintro _ ⟨i, rfl⟩
    rw [leadingCoeff_monicDividedBasis hB hne i]
    exact isUnit_one
  · -- leading-monomial domination.
    rintro g hgI hg0
    exact exists_degree_le_dividedIdeal hB hne hgI hg0

/-- **The divided basis is `sortedByYDegree`-distinct ⟹ index-distinct**: `monicDividedBasis hB hne`
is injective (the cofactors `dividedBasis` are, since `H·qᵢ = fᵢ` and `sortedByYDegree` is injective;
monic scaling is injective). -/
theorem monicDividedBasis_injective {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hne : (Finset.univ : Finset (Fin B.card)).Nonempty) :
    Function.Injective (monicDividedBasis hB hne) := by
  intro i j hij
  set ci := MonomialOrder.lex.leadingCoeff (dividedBasis hB hne i) with hci_def
  set cj := MonomialOrder.lex.leadingCoeff (dividedBasis hB hne j) with hcj_def
  have hci : ci ≠ 0 := leadingCoeff_dividedBasis_ne_zero hB hne i
  have hcj : cj ≠ 0 := leadingCoeff_dividedBasis_ne_zero hB hne j
  -- multiply `monicDividedBasis i = monicDividedBasis j` by `H`:
  -- `C cᵢ⁻¹ · fᵢ = C cⱼ⁻¹ · fⱼ` (using `H · monicDividedBasis k = C cₖ⁻¹ · fₖ`).
  have key : MvPolynomial.C ci⁻¹ * sortedByYDegree hB i
      = MvPolynomial.C cj⁻¹ * sortedByYDegree hB j := by
    have e : ∀ k : Fin B.card,
        gbCommonYFactor hB * monicDividedBasis hB hne k
          = MvPolynomial.C (MonomialOrder.lex.leadingCoeff (dividedBasis hB hne k))⁻¹
            * sortedByYDegree hB k := by
      intro k
      rw [monicDividedBasis, mul_left_comm, gbCommonYFactor_mul_dividedBasis]
    have := congrArg (fun p => gbCommonYFactor hB * p) hij
    simp only [e] at this
    exact this
  -- leading coefficients: `B` is monic, so `leadingCoeff (C cₖ⁻¹ · fₖ) = cₖ⁻¹`. Hence `cᵢ⁻¹ = cⱼ⁻¹`.
  have hlc := congrArg (fun p => MonomialOrder.lex.leadingCoeff p) key
  simp only [leadingCoeff_C_mul MonomialOrder.lex (inv_ne_zero hci),
    leadingCoeff_C_mul MonomialOrder.lex (inv_ne_zero hcj),
    hB.2.1 _ (sortedByYDegree_mem hB i), hB.2.1 _ (sortedByYDegree_mem hB j), mul_one] at hlc
  -- `cᵢ⁻¹ = cⱼ⁻¹`, so `key` cancels `C cᵢ⁻¹` to give `fᵢ = fⱼ`, hence `i = j`.
  rw [hlc] at key
  exact sortedByYDegree_injective hB
    (mul_left_cancel₀ (by rw [Ne, MvPolynomial.C_eq_zero]; exact inv_ne_zero hcj) key)

/-- **The divided basis has pairwise non-dividing leading monomials** (Lazard's Theorem 1 minimality,
leading-monomial form). For distinct `i ≠ i'`, neither `lex.degree (monicDividedBasis i')` divides
`lex.degree (monicDividedBasis i)`: the `lex.degree H` shift cancels (`leadingMonomial_cofactor_not_le`
on `B`'s reducedness). This is the minimal-Gröbner-basis condition the divided family inherits. -/
theorem dividedBasis_leadingMonomial_not_le {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hne : (Finset.univ : Finset (Fin B.card)).Nonempty) {i i' : Fin B.card} (hii : i ≠ i') :
    ¬ (MonomialOrder.lex.degree (monicDividedBasis hB hne i')
        ≤ MonomialOrder.lex.degree (monicDividedBasis hB hne i)) := by
  rw [degree_monicDividedBasis, degree_monicDividedBasis]
  refine leadingMonomial_cofactor_not_le hB (gbCommonYFactor_ne_zero hB hne)
    (dividedBasis_ne_zero hB hne i) (dividedBasis_ne_zero hB hne i') ?_ ?_ ?_
  · rw [gbCommonYFactor_mul_dividedBasis]; exact sortedByYDegree_mem hB i
  · rw [gbCommonYFactor_mul_dividedBasis]; exact sortedByYDegree_mem hB i'
  · rw [gbCommonYFactor_mul_dividedBasis, gbCommonYFactor_mul_dividedBasis]
    exact fun h => hii (sortedByYDegree_injective hB h)

/-- **The monic divided family has no common `y`-factor** (Lazard's `P = Gₖ₊₁ = 1` for `{fᵢ/H}`): any
`K[x][y]`-divisor `P` common to all `lazardView (monicDividedBasis hB hne i)` is a unit. Each view is
*associated* to the cofactor `gbYGcdCofactor hB hne i` (`lazardView_monicDividedBasis_associated`),
whose family gcd is `1` (`cofactor_hasNoCommonYFactor`). -/
theorem monicDividedBasis_hasNoCommonYFactor {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hne : (Finset.univ : Finset (Fin B.card)).Nonempty)
    (P : Polynomial (MvPolynomial (Fin 1) K))
    (hP : ∀ i : Fin B.card, P ∣ lazardView (monicDividedBasis hB hne i)) : IsUnit P := by
  refine cofactor_hasNoCommonYFactor hB hne P (fun i => ?_)
  exact (hP i).trans (lazardView_monicDividedBasis_associated hB hne i).symm.dvd

/-- **Ideal-membership transfer of `P ∣ lazardView`** (the `HasNoCommonYFactor`-invariance core).
If `P` divides `lazardView b'` for every `b'` in a generating set `B'` of an ideal containing `g`,
then `P ∣ lazardView g`: writing `g = ∑ cₖ·b'ₖ`, `lazardView g = ∑ lazardView(cₖ)·lazardView(b'ₖ)` and
`P` divides each term. So a common `y`-factor of one generating set divides every ideal member's view
— the fact that makes `HasNoCommonYFactor` an *ideal* invariant, not a basis-presentation artefact. -/
theorem dvd_lazardView_of_mem_span {K : Type*}
    [Field K] {P : Polynomial (MvPolynomial (Fin 1) K)}
    {B' : Set (MvPolynomial (Fin 2) K)} (hP : ∀ b' ∈ B', P ∣ lazardView b')
    {g : MvPolynomial (Fin 2) K} (hg : g ∈ Ideal.span B') : P ∣ lazardView g := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hg
  · intro x hx; exact hP x hx
  · rw [lazardView, map_zero]; exact dvd_zero _
  · intro x y _ _ hx hy; rw [lazardView, map_add]; exact dvd_add hx hy
  · intro a x _ hx
    rw [lazardView, smul_eq_mul, map_mul]
    exact Dvd.dvd.mul_left hx _

/-- **`HasNoCommonYFactor` for ANY reduced GB of the divided ideal `I'`** (the ideal-invariance
bridge). Any reduced GB `hB'` of `dividedIdeal hB hne` has no common `y`-factor: a `P` dividing all
`lazardView (sortedByYDegree hB' j)` divides `lazardView g` for every `g ∈ I'`
(`dvd_lazardView_of_mem_span`, the `sortedByYDegree hB' j` generate `I'`), in particular every
`monicDividedBasis hB hne i ∈ I'`; those have no common factor
(`monicDividedBasis_hasNoCommonYFactor`), so `P` is a unit. This works for *any* presentation of `I'`
— the no-common-factor property is an ideal invariant, not tied to the explicit divided basis. -/
theorem hasNoCommonYFactor_of_dividedIdeal {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hne : (Finset.univ : Finset (Fin B.card)).Nonempty)
    {B' : Finset (MvPolynomial (Fin 2) K)}
    (hB' : IsReducedGroebnerBasis MonomialOrder.lex (dividedIdeal hB hne)
      (↑B' : Set (MvPolynomial (Fin 2) K))) :
    HasNoCommonYFactor hB' := by
  intro P hP
  -- `P` divides every basis view `lazardView (sortedByYDegree hB' j)`.
  have hPB' : ∀ b' ∈ (↑B' : Set (MvPolynomial (Fin 2) K)), P ∣ lazardView b' := by
    intro b' hb'
    rw [← range_sortedByYDegree hB'] at hb'
    obtain ⟨j, rfl⟩ := hb'
    exact hP j
  -- hence `P ∣ lazardView g` for every `g ∈ I' = span ↑B'`.
  have hPg : ∀ g ∈ dividedIdeal hB hne, P ∣ lazardView g := by
    intro g hg
    refine dvd_lazardView_of_mem_span hPB' ?_
    rwa [hB'.isGroebnerBasis.span_eq]
  -- in particular `P` divides every `lazardView (monicDividedBasis hB hne i)`, which has no common factor.
  refine monicDividedBasis_hasNoCommonYFactor hB hne P (fun i => ?_)
  exact hPg _ (Ideal.subset_span ⟨i, rfl⟩)

/-- **Lazard's `Pₖ = Rₖ·Sₖ` for the divided ideal, no `hassoc` needed** (the Theorem 1 structural
conclusion, general case, discharged). For an **arbitrary** reduced bivariate GB `hB` and *any*
reduced GB `hB'` of its divided ideal `I' = span {fᵢ/H}`, every sorted element of `hB'` splits as
`lazardView fⱼ = C(cⱼ)·Sⱼ` with content `cⱼ ∼ leadingYCoeff fⱼ`, `Sⱼ` primitive and monic in `y`. The
`HasNoCommonYFactor hB'` hypothesis of `lazard_Pk_eq_Rk_Sk_of_hasNoCommonYFactor` is discharged
**automatically** by `hasNoCommonYFactor_of_dividedIdeal` (the ideal-invariance bridge) — replacing the
hand-supplied `hassoc` recovery hypothesis of `lazard_Pk_eq_Rk_Sk_of_divideOut`. -/
theorem lazard_Pk_eq_Rk_Sk_dividedIdeal {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hne : (Finset.univ : Finset (Fin B.card)).Nonempty)
    {B' : Finset (MvPolynomial (Fin 2) K)}
    (hB' : IsReducedGroebnerBasis MonomialOrder.lex (dividedIdeal hB hne)
      (↑B' : Set (MvPolynomial (Fin 2) K)))
    (j : Fin B'.card) :
    ∃ S : Polynomial (MvPolynomial (Fin 1) K),
      lazardView (sortedByYDegree hB' j) = Polynomial.C (@Polynomial.content _ _
          (normalizedGcdMonoidMvPolynomialFinOne K) (lazardView (sortedByYDegree hB' j))) * S ∧
        Associated (@Polynomial.content _ _ (normalizedGcdMonoidMvPolynomialFinOne K)
          (lazardView (sortedByYDegree hB' j))) (leadingYCoeff (sortedByYDegree hB' j)) ∧
        S.IsPrimitive ∧ IsUnit S.leadingCoeff :=
  lazard_Pk_eq_Rk_Sk_of_hasNoCommonYFactor hB'
    (hasNoCommonYFactor_of_dividedIdeal hB hne hB') j

/-- **Lazard's `Pₖ = Rₖ·Sₖ`, fully unconditional** (Theorem 1, the divide-out closed). For a reduced
bivariate Gröbner basis `hB` of `I` (nonempty), there *exists* a reduced Gröbner basis `B'` of the
divided ideal `I' = span {fᵢ/H}` (`exists_isReducedGroebnerBasis`), and every sorted element of `B'`
splits as `lazardView fⱼ = C(cⱼ)·Sⱼ` with content `cⱼ ∼ leadingYCoeff fⱼ`, `Sⱼ` primitive and monic
in `y`. No `hassoc`/`HasNoCommonYFactor` hypothesis: both are discharged by the divided-ideal
invariance and the reduced-GB existence theorem. -/
theorem lazard_Pk_eq_Rk_Sk_unconditional {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hne : (Finset.univ : Finset (Fin B.card)).Nonempty) :
    ∃ B' : Finset (MvPolynomial (Fin 2) K),
      ∃ hB' : IsReducedGroebnerBasis MonomialOrder.lex (dividedIdeal hB hne)
        (↑B' : Set (MvPolynomial (Fin 2) K)),
      ∀ j : Fin B'.card, ∃ S : Polynomial (MvPolynomial (Fin 1) K),
        lazardView (sortedByYDegree hB' j) = Polynomial.C (@Polynomial.content _ _
            (normalizedGcdMonoidMvPolynomialFinOne K) (lazardView (sortedByYDegree hB' j))) * S ∧
          Associated (@Polynomial.content _ _ (normalizedGcdMonoidMvPolynomialFinOne K)
            (lazardView (sortedByYDegree hB' j))) (leadingYCoeff (sortedByYDegree hB' j)) ∧
          S.IsPrimitive ∧ IsUnit S.leadingCoeff := by
  obtain ⟨B', hB'⟩ := exists_isReducedGroebnerBasis MonomialOrder.lex (dividedIdeal hB hne)
  exact ⟨B', hB', fun j => lazard_Pk_eq_Rk_Sk_dividedIdeal hB hne hB' j⟩

-- The divided family is a Gröbner basis of `I' = span {fᵢ/H}` (Lazard Thm 1, Part C).
example {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hne : (Finset.univ : Finset (Fin B.card)).Nonempty) :
    IsGroebnerBasis MonomialOrder.lex (dividedIdeal hB hne)
      (Set.range (monicDividedBasis hB hne)) :=
  isGroebnerBasis_dividedBasis hB hne

-- The divided basis has pairwise non-dividing leading monomials (minimal-GB condition).
example {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hne : (Finset.univ : Finset (Fin B.card)).Nonempty) {i i' : Fin B.card} (hii : i ≠ i') :
    ¬ (MonomialOrder.lex.degree (monicDividedBasis hB hne i')
        ≤ MonomialOrder.lex.degree (monicDividedBasis hB hne i)) :=
  dividedBasis_leadingMonomial_not_le hB hne hii

-- `g ∈ I' ⟺ H·g ∈ I` (the divided-ideal membership equivalence).
example {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hne : (Finset.univ : Finset (Fin B.card)).Nonempty) (g : MvPolynomial (Fin 2) K) :
    g ∈ dividedIdeal hB hne ↔ gbCommonYFactor hB * g ∈ I :=
  mem_dividedIdeal_iff hB hne g

-- Any reduced GB of `I'` has no common `y`-factor (ideal invariance), hence `Pₖ = Rₖ·Sₖ`.
example {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hne : (Finset.univ : Finset (Fin B.card)).Nonempty)
    {B' : Finset (MvPolynomial (Fin 2) K)}
    (hB' : IsReducedGroebnerBasis MonomialOrder.lex (dividedIdeal hB hne)
      (↑B' : Set (MvPolynomial (Fin 2) K))) :
    HasNoCommonYFactor hB' :=
  hasNoCommonYFactor_of_dividedIdeal hB hne hB'

-- Every ideal over a field with finitely many variables has a reduced Gröbner basis.
example {σ K : Type*} [Finite σ] [Field K] (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ K)) :
    ∃ B : Finset (MvPolynomial σ K), IsReducedGroebnerBasis m I (↑B : Set (MvPolynomial σ K)) :=
  exists_isReducedGroebnerBasis m I

-- Auto-reducing a minimal monic Gröbner basis yields a reduced Gröbner basis.
example {σ K : Type*} [Finite σ] [Field K] {m : MonomialOrder σ} {I : Ideal (MvPolynomial σ K)}
    {B : Finset (MvPolynomial σ K)} (hBu : ∀ b ∈ B, IsUnit (m.leadingCoeff b))
    (hB : IsGroebnerBasis m I (↑B : Set (MvPolynomial σ K)))
    (hmonic : ∀ b ∈ (↑B : Set (MvPolynomial σ K)), m.leadingCoeff b = 1)
    (hpair : ∀ b ∈ (↑B : Set (MvPolynomial σ K)), ∀ b' ∈ (↑B : Set (MvPolynomial σ K)),
      b ≠ b' → ¬ (m.degree b' ≤ m.degree b)) :
    IsReducedGroebnerBasis m I (↑(autoReduce m hBu) : Set (MvPolynomial σ K)) :=
  isReducedGroebnerBasis_autoReduce hBu hB hmonic hpair

end DeepWiki.SymbolicIntegration
