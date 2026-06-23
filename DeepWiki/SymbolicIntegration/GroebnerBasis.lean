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

/-- **Bridge to Mathlib's S-polynomial** (for nonzero `f, g`). Mathlib's `m.sPolynomial` avoids
inverting leading coefficients (`monomial _ (lc g) * f - monomial _ (lc f) * g`); ours normalizes
by `(lc f)⁻¹`, `(lc g)⁻¹`. They differ by the scalar `(lc f * lc g)⁻¹`:
`S(f,g) = (lc f * lc g)⁻¹ • m.sPolynomial f g`. -/
theorem sPolynomial_eq_inv_smul_mathlib {K : Type*} [Field K] (m : MonomialOrder σ)
    {f g : MvPolynomial σ K} (hf : f ≠ 0) (hg : g ≠ 0) :
    sPolynomial m f g = (m.leadingCoeff f * m.leadingCoeff g)⁻¹ • m.sPolynomial f g := by
  classical
  have hcf : m.leadingCoeff f ≠ 0 := m.leadingCoeff_ne_zero_iff.mpr hf
  have hcg : m.leadingCoeff g ≠ 0 := m.leadingCoeff_ne_zero_iff.mpr hg
  rw [sPolynomial, m.sPolynomial_def, smul_sub]
  have e1 : (m.leadingCoeff f * m.leadingCoeff g)⁻¹ * m.leadingCoeff g = (m.leadingCoeff f)⁻¹ := by
    rw [mul_inv, mul_assoc, inv_mul_cancel₀ hcg, mul_one]
  have e2 : (m.leadingCoeff f * m.leadingCoeff g)⁻¹ * m.leadingCoeff f = (m.leadingCoeff g)⁻¹ := by
    rw [mul_inv, mul_comm (m.leadingCoeff f)⁻¹, mul_assoc, inv_mul_cancel₀ hcf, mul_one]
  rw [← smul_mul_assoc, smul_monomial, smul_eq_mul, e1,
    ← smul_mul_assoc, smul_monomial, smul_eq_mul, e2]

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

/-- **Leading-monomial divisibility ⟹ Gröbner basis** (the bookkeeping wrapper of CLO §2.6
Theorem 6). If `B ⊆ I` has unit leading coefficients, generates `I`, and every nonzero `f ∈ I`
has its leading monomial divisible by `m.degree b` for some `b ∈ B`, then `B` is a Gröbner basis
of `I`. The hard content of the converse Buchberger criterion is establishing the divisibility
hypothesis. -/
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

/-- **The leading-monomial divisibility core of the converse Buchberger criterion**
(Cox–Little–O'Shea §2.6, Theorem 6, the minimal-representation argument). If `B` generates `I` and
every S-polynomial `S(b,b')` of `B` has a *standard representation* `∑ q c · c` whose summand
degrees are all `≼[m] m.degree (S(b,b'))`, then every nonzero `f ∈ I` has its leading monomial
divisible by `m.degree b` for some `b ∈ B`. The proof minimizes the representation `f = ∑ h b · b`
over the well-founded degree of its largest summand; if the leading monomial of `f` lies strictly
below that degree, the top-degree part cancels into S-polynomials (`sPolynomial_decomposition`),
each reducible via `hS` to a strictly-smaller representation — contradicting minimality. -/
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

/-- **Buchberger's criterion, the converse (hard) half** (Cox–Little–O'Shea §2.6, Theorem 6). A
generating set `B` of `I` with unit leading coefficients, *every* of whose S-polynomials `S(b,b')`
has a standard representation `∑ q c · c` over `B` with summand degrees `≼[m] m.degree (S(b,b'))`
(equivalently: every S-polynomial reduces to `0` modulo `B`), is a Gröbner basis of `I`. -/
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

end DeepWiki.SymbolicIntegration
