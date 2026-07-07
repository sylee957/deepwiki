import DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner.BasisBasic
import DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner.SPolynomial

/-! # Buchberger criterion

Buchberger's criterion in standard-representation form: S-polynomial reductions
force the leading-monomial divisibility condition for Gröbner bases. -/

open MvPolynomial MonomialOrder

namespace DeepWiki.SymbolicIntegration

variable {σ : Type*} {m : MonomialOrder σ}

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

end DeepWiki.SymbolicIntegration
