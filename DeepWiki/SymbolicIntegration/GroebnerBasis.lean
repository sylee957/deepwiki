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

/-- The **S-polynomial** `S(f,g)` over a field: with `γ = m.degree f ⊔ m.degree g` the lcm of the
leading monomials, `monomial (γ - m.degree f) (m.leadingCoeff f)⁻¹ * f - monomial (γ - m.degree g)
(m.leadingCoeff g)⁻¹ * g`; the two scaled terms share leading monomial `γ`, so `S(f,g)` cancels
the leading terms of `f` and `g`. -/
noncomputable def sPolynomial {K : Type*} [Field K] (m : MonomialOrder σ)
    (f g : MvPolynomial σ K) : MvPolynomial σ K :=
  monomial ((m.degree f ⊔ m.degree g) - m.degree f) (m.leadingCoeff f)⁻¹ * f -
    monomial ((m.degree f ⊔ m.degree g) - m.degree g) (m.leadingCoeff g)⁻¹ * g

/-- The S-polynomial of two ideal members lies in the ideal: `S(f,g) = monomial _ _ * f -
monomial _ _ * g` is a difference of left multiples of `f, g ∈ I`. -/
theorem sPolynomial_mem {K : Type*} [Field K] {I : Ideal (MvPolynomial σ K)}
    {f g : MvPolynomial σ K} (hf : f ∈ I) (hg : g ∈ I) : sPolynomial m f g ∈ I :=
  I.sub_mem (Ideal.mul_mem_left _ _ hf) (Ideal.mul_mem_left _ _ hg)

/-- **Buchberger's criterion, the forward (easy) half.** A Gröbner basis `B` of `I` reduces every
S-polynomial `S(b,b')` (`b, b' ∈ B`) to zero: any division remainder of `S(b,b')` by `B` is `0`.
The converse — S-polynomials reducing to `0` forcing `B` to be a Gröbner basis (Buchberger's
theorem, via the syzygy argument) — is the deferred research-grade direction. -/
theorem IsGroebnerBasis.sPolynomial_div_remainder_eq_zero {K : Type*} [Field K]
    {I : Ideal (MvPolynomial σ K)} {B : Set (MvPolynomial σ K)} (hB : IsGroebnerBasis m I B)
    {b b' : MvPolynomial σ K} (hb : b ∈ B) (hb' : b' ∈ B) {g : B →₀ MvPolynomial σ K}
    {r : MvPolynomial σ K}
    (hgr : sPolynomial m b b' = Finsupp.linearCombination _ (fun x : B => (x : MvPolynomial σ K)) g + r)
    (hrem : ∀ c ∈ r.support, ∀ x ∈ B, ¬ (m.degree x ≤ c)) : r = 0 :=
  (hB.mem_iff_div_remainder_eq_zero _ hgr hrem).mp (sPolynomial_mem (hB.1 b hb) (hB.1 b' hb'))

/-- `m.degree (C c * f) = m.degree f` over a field for `c ≠ 0` (regular scaling). -/
theorem degree_C_mul {K : Type*} [Field K] (m : MonomialOrder σ) {c : K} (hc : c ≠ 0)
    (f : MvPolynomial σ K) : m.degree (C c * f) = m.degree f := by
  rw [← smul_eq_C_mul]
  exact degree_smul_of_isRegular (IsRegular.of_ne_zero hc) ..

/-- `m.leadingCoeff (C c * f) = c * m.leadingCoeff f` over a field for `c ≠ 0`. -/
theorem leadingCoeff_C_mul {K : Type*} [Field K] (m : MonomialOrder σ) {c : K} (hc : c ≠ 0)
    (f : MvPolynomial σ K) : m.leadingCoeff (C c * f) = c * m.leadingCoeff f := by
  unfold MonomialOrder.leadingCoeff
  rw [degree_C_mul m hc, ← smul_eq_C_mul, coeff_smul, smul_eq_mul]

/-- **S-polynomial collapse for equal leading monomials** (CLO §2.6): when `m.degree f =
m.degree g`, the lcm `f ⊔ g = m.degree f`, so the monomial shifts are `monomial 0 = C`, and
`S(f,g) = C (m.leadingCoeff f)⁻¹ * f - C (m.leadingCoeff g)⁻¹ * g` is a scalar combination. -/
theorem sPolynomial_eq_of_degree_eq {K : Type*} [Field K] (m : MonomialOrder σ)
    {f g : MvPolynomial σ K} (h : m.degree f = m.degree g) :
    sPolynomial m f g = C (m.leadingCoeff f)⁻¹ * f - C (m.leadingCoeff g)⁻¹ * g := by
  unfold sPolynomial
  rw [h, sup_idem, tsub_self, monomial_zero']

/-- **S-polynomial of equal-leading-monomial polynomials has strictly smaller degree** (CLO
§2.6): both `C (lc f)⁻¹ * f` and `C (lc g)⁻¹ * g` are monic of degree `m.degree f`, so the
leading terms cancel and `m.degree (S(f,g)) ≺[m] m.degree f` (`m.degree f ≠ 0`). -/
theorem sPolynomial_degree_lt_of_degree_eq {K : Type*} [Field K] (m : MonomialOrder σ)
    {f g : MvPolynomial σ K} (h : m.degree f = m.degree g) (hf : f ≠ 0) (hg : g ≠ 0)
    (hδ : m.degree f ≠ 0) :
    m.degree (sPolynomial m f g) ≺[m] m.degree f := by
  rw [sPolynomial_eq_of_degree_eq m h]
  have hcf : (m.leadingCoeff f)⁻¹ ≠ 0 := inv_ne_zero (m.leadingCoeff_ne_zero_iff.mpr hf)
  have hcg : (m.leadingCoeff g)⁻¹ ≠ 0 := inv_ne_zero (m.leadingCoeff_ne_zero_iff.mpr hg)
  set u := C (m.leadingCoeff f)⁻¹ * f with hu
  set v := C (m.leadingCoeff g)⁻¹ * g with hv
  have hdegu : m.degree u = m.degree f := degree_C_mul m hcf f
  have hdegv : m.degree v = m.degree f := by rw [hv, degree_C_mul m hcg g, h]
  have hlcu : m.leadingCoeff u = 1 := by
    rw [hu, leadingCoeff_C_mul m hcf f, inv_mul_cancel₀ (m.leadingCoeff_ne_zero_iff.mpr hf)]
  have hlcv : m.leadingCoeff v = 1 := by
    rw [hv, leadingCoeff_C_mul m hcg g, inv_mul_cancel₀ (m.leadingCoeff_ne_zero_iff.mpr hg)]
  -- the `m.degree f`-coefficient of `u - v` is `lc u - lc v = 1 - 1 = 0`
  have hcoeff : (u - v).coeff (m.degree f) = 0 := by
    rw [coeff_sub]
    have e1 : u.coeff (m.degree f) = 1 := by rw [← hdegu]; exact hlcu
    have e2 : v.coeff (m.degree f) = 1 := by rw [← hdegv]; exact hlcv
    rw [e1, e2, sub_self]
  have hle : m.degree (u - v) ≼[m] m.degree f := by
    apply degree_sub_le.trans
    rw [hdegu, hdegv, sup_idem]
  refine hle.lt_of_ne (fun heq => ?_)
  apply m.toSyn.injective at heq
  rcases eq_or_ne (u - v) 0 with h0 | h0
  · rw [h0, degree_zero] at heq
    exact hδ heq.symm
  · refine (m.leadingCoeff_ne_zero_iff.mpr h0) ?_
    rw [MonomialOrder.leadingCoeff, heq, hcoeff]

/-- **Scaled S-polynomial rewrite** (CLO §2.6 telescoping step): for equal leading monomials,
`(m.leadingCoeff f) • S(f,g) = f - (m.leadingCoeff f / m.leadingCoeff g) • g`. -/
theorem leadingCoeff_smul_sPolynomial_of_degree_eq {K : Type*} [Field K] (m : MonomialOrder σ)
    {f g : MvPolynomial σ K} (h : m.degree f = m.degree g) (hf : f ≠ 0) :
    m.leadingCoeff f • sPolynomial m f g
      = f - (m.leadingCoeff f / m.leadingCoeff g) • g := by
  rw [sPolynomial_eq_of_degree_eq m h, smul_sub, ← smul_eq_C_mul, ← smul_eq_C_mul,
    smul_smul, smul_smul, mul_inv_cancel₀ (m.leadingCoeff_ne_zero_iff.mpr hf), one_smul,
    div_eq_mul_inv]

/-- **The cancellation lemma** (Cox–Little–O'Shea §2.6, Lemma 5): if `p₀,…,pₙ` are nonzero with
the same leading monomial `δ` and their leading terms cancel (`m.degree (∑ᵢ pᵢ) ≺[m] δ`), then
the sum telescopes into a combination of S-polynomials pivoting on the last element,
`∑ᵢ pᵢ = ∑_{i≠last} (m.leadingCoeff (pᵢ)) • S(pᵢ, p_last)`, and each `S(pᵢ, p_last)` has degree
`≺[m] δ` — the leading-term-free combination at the heart of the converse Buchberger criterion. -/
theorem cancellation_lemma {K : Type*} [Field K] (m : MonomialOrder σ) {n : ℕ}
    {p : Fin (n + 1) → MvPolynomial σ K} {δ : σ →₀ ℕ}
    (hδ : ∀ i, m.degree (p i) = δ) (hp : ∀ i, p i ≠ 0)
    (hcancel : m.degree (∑ i, p i) ≺[m] δ) :
    (∑ i, p i = ∑ i ∈ Finset.univ.erase (Fin.last n),
        m.leadingCoeff (p i) • sPolynomial m (p i) (p (Fin.last n))) ∧
      ∀ i ≠ Fin.last n, m.degree (sPolynomial m (p i) (p (Fin.last n))) ≺[m] δ := by
  classical
  set last := Fin.last n
  set d : Fin (n + 1) → K := fun i => m.leadingCoeff (p i) with hd
  have hδ0 : δ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hcancel
    exact absurd hcancel (not_lt_of_ge bot_le)
  -- the `δ`-coefficient of `∑ pᵢ` is `∑ lc (pᵢ)`, and it vanishes by cancellation
  have hsum0 : ∑ i, d i = 0 := by
    have hco : (∑ i, p i).coeff δ = ∑ i, d i := by
      rw [coeff_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [hd]
      simp only
      rw [MonomialOrder.leadingCoeff, hδ i]
    rw [← hco]
    exact coeff_eq_zero_of_lt hcancel
  have hpart2 : ∀ i ≠ last, m.degree (sPolynomial m (p i) (p last)) ≺[m] δ := by
    intro i _
    have hh : m.degree (p i) = m.degree (p last) := by rw [hδ i, hδ last]
    have := sPolynomial_degree_lt_of_degree_eq m hh (hp i) (hp last) (by rw [hδ i]; exact hδ0)
    rwa [hδ i] at this
  refine ⟨?_, hpart2⟩
  have hnonpivot : ∑ i ∈ Finset.univ.erase last, d i = - d last := by
    have hsplit := Finset.sum_erase_add Finset.univ d (Finset.mem_univ last)
    rw [hsum0] at hsplit
    rw [eq_neg_iff_add_eq_zero, hsplit]
  have hdlast : d last ≠ 0 := m.leadingCoeff_ne_zero_iff.mpr (hp last)
  have hterm : ∀ i, d i • sPolynomial m (p i) (p last)
      = p i - (d i * (d last)⁻¹) • p last := by
    intro i
    have hh : m.degree (p i) = m.degree (p last) := by rw [hδ i, hδ last]
    rw [leadingCoeff_smul_sPolynomial_of_degree_eq m hh (hp i), div_eq_mul_inv]
  -- telescope: `∑_{i≠last}(pᵢ - (dᵢ/d_last)•p_last) = ∑_{i≠last} pᵢ + p_last = ∑ᵢ pᵢ`
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_sub_distrib,
    ← Finset.sum_smul, ← Finset.sum_mul, hnonpivot, neg_mul,
    mul_inv_cancel₀ hdlast, neg_smul, one_smul, sub_neg_eq_add,
    Finset.sum_erase_add Finset.univ p (Finset.mem_univ last)]

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

end DeepWiki.SymbolicIntegration
