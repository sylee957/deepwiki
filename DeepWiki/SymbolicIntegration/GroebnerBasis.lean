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

/-! ## Buchberger's algorithm: the S-polynomial completion step, termination, and correctness

The remaining ingredients of Buchberger's algorithm. Over a field with finitely many
variables, the ring `MvPolynomial σ K` is Noetherian, so the leading-term ideals form a
well-founded ascending chain. One *step* adjoins the nonzero division remainders of all
S-polynomials; either every S-polynomial already reduces to `0` (so `B` is a Gröbner basis
by `isGroebnerBasis_of_sPolynomial_reducesToZero`) or a new leading monomial strictly grows
the leading-term ideal. The `WellFoundedGT` ascending-chain condition turns this dichotomy
into termination + correctness. -/

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

/-! ## Lazard's Lemma 1: distinct leading y-degrees in a minimal bivariate Gröbner basis

Lazard (1985), J. Symb. Comp. 1, 261–270, Lemma 1 — the foundational step of his bivariate
Gröbner-basis structure theorem, and the stepping stone toward Czichowski's structural lemmas
(Bronstein §2.6). Over `MvPolynomial (Fin 2) K` (index `0 = x`, `1 = y`) the leading y-degree of
`b` is `(m.degree b) 1`; the lemma says distinct elements of a minimal/reduced Gröbner basis have
distinct leading y-degrees. -/

/-- In `Fin 2 →₀ ℕ`, two exponent vectors agreeing at index `1` (the y-coordinate) are comparable:
since the remaining ℕ-values at index `0` are totally ordered, the finsupps are comparable
pointwise. -/
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

/-- **Minimality extraction.** In a reduced Gröbner basis, the leading monomial of `b'` does not
divide that of a distinct `b`: instantiating the reduced condition at the leading monomial
`m.degree b ∈ b.support` (`b ≠ 0`). -/
theorem IsReducedGroebnerBasis.leadingMonomial_not_le {K : Type*} [Field K]
    {I : Ideal (MvPolynomial σ K)} {B : Set (MvPolynomial σ K)}
    (hB : IsReducedGroebnerBasis m I B) {b b' : MvPolynomial σ K} (hb : b ∈ B) (hb' : b' ∈ B)
    (hne : b ≠ b') : ¬ (m.degree b' ≤ m.degree b) :=
  hB.2.2 b hb b' hb' hne (m.degree b) (degree_mem_support (hB.ne_zero hb))

/-- **Lazard (1985), Lemma 1.** In a reduced (minimal) Gröbner basis `B` of a two-variable ideal,
distinct elements have distinct leading y-degrees `(m.degree ·) 1`. If two shared a y-degree they
would be comparable (`finsupp_fin_two_le_or_le_of_apply_eq`), so one leading monomial would divide
the other — contradicting minimality (`IsReducedGroebnerBasis.leadingMonomial_not_le`). -/
theorem lazard_lemma1 {K : Type*} [Field K] {m : MonomialOrder (Fin 2)}
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis m I (↑B : Set (MvPolynomial (Fin 2) K))) :
    ∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → (m.degree b) 1 ≠ (m.degree b') 1 := by
  intro b hb b' hb' hne hy
  rcases finsupp_fin_two_le_or_le_of_apply_eq hy with hle | hle
  · exact hB.leadingMonomial_not_le (Finset.mem_coe.mpr hb') (Finset.mem_coe.mpr hb)
      (Ne.symm hne) hle
  · exact hB.leadingMonomial_not_le (Finset.mem_coe.mpr hb) (Finset.mem_coe.mpr hb') hne hle

/-- **Lazard's Lemma 1, injectivity form.** The leading-y-degree map `b ↦ (m.degree b) 1` is
injective on a reduced Gröbner basis of a two-variable ideal. -/
theorem lazard_lemma1_injOn {K : Type*} [Field K] {m : MonomialOrder (Fin 2)}
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis m I (↑B : Set (MvPolynomial (Fin 2) K))) :
    Set.InjOn (fun b => (m.degree b) 1) (↑B : Set (MvPolynomial (Fin 2) K)) := by
  intro b hb b' hb' hyeq
  by_contra hne
  exact lazard_lemma1 hB b hb b' hb' hne hyeq

/-! ## The `MvPolynomial (Fin 2) K ↔ K[x][y]` representation bridge

Lazard's bivariate Gröbner-basis structure theory (Lazard 1985, for Bronstein §2.6 /
Czichowski) views a bivariate polynomial `f : MvPolynomial (Fin 2) K` as a univariate
polynomial in `y` with coefficients in `K[x]`. Mathlib's `MvPolynomial.finSuccEquiv` pulls out
**variable `0`** as the `Polynomial` variable, so we adopt the convention `y = variable 0`,
`x = variable 1` — `finSuccEquiv K 1 f : Polynomial (MvPolynomial (Fin 1) K)` is the `K[x][y]`
view, its `natDegree` is the `y`-degree `degreeOf 0 f`, and its `leadingCoeff` (in the GCD domain
`MvPolynomial (Fin 1) K ≃ K[x]`) is the leading-`y`-coefficient `Rₖ` of Lazard's lemmas.

For Lazard's structure theory the `y`-degree must be the **dominant** coordinate of the monomial
order. The lex order `MonomialOrder.lex` on `Fin 2` makes the *smaller* index dominant (`X 1 <
X 0 ^ 2`), i.e. index `0 = y` dominant — the right convention. We package this dominance as a
hypothesis `hdom : ∀ f ≠ 0, (m.degree f) 0 = degreeOf 0 f` and prove `MonomialOrder.lex`
satisfies it (`lex_degree_apply_zero`), so the bridge is stated for any dominant order and
instantiated concretely by lex. -/

/-- For lex on `Fin 2`, comparable exponent vectors are comparable at the dominant index `0`:
`toLex s ≤ toLex t → s 0 ≤ t 0` (index `0` is the most significant lex coordinate). -/
theorem apply_zero_le_of_toLex_le {s t : Fin 2 →₀ ℕ} (h : toLex s ≤ toLex t) : s 0 ≤ t 0 := by
  rcases h.lt_or_eq with hlt | heq
  · obtain ⟨i, hbelow, hi⟩ := Finsupp.Lex.lt_iff.mp hlt
    fin_cases i
    · exact hi.le
    · exact (hbelow 0 (by decide)).le
  · exact (congrArg (fun u => (ofLex u) 0) heq).le

/-- **Lex makes the `y`-degree (index `0`) dominant**: for `MonomialOrder.lex` on `Fin 2` and
`f ≠ 0`, the index-`0` exponent of the leading monomial equals the `y`-degree `degreeOf 0 f`. -/
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

/-- **The `K[x][y]` view of a bivariate polynomial** (`y = variable 0`): `finSuccEquiv K 1 f`
re-reads `f : MvPolynomial (Fin 2) K` as a univariate polynomial in `y` with coefficients in
`MvPolynomial (Fin 1) K ≃ K[x]`. -/
noncomputable def lazardView {K : Type*} [Field K] (f : MvPolynomial (Fin 2) K) :
    Polynomial (MvPolynomial (Fin 1) K) :=
  finSuccEquiv K 1 f

/-- **Lazard's leading-`y`-coefficient `Rₖ`**: the `K[x]`-coefficient of the top `y`-power of `f`,
`(finSuccEquiv K 1 f).leadingCoeff ∈ MvPolynomial (Fin 1) K`. -/
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

/-- **The `y`-degree bridge**: the `natDegree` of the `K[x][y]` view is the `y`-degree
`degreeOf 0 f` (Mathlib's `natDegree_finSuccEquiv`). -/
theorem natDegree_lazardView {K : Type*} [Field K] (f : MvPolynomial (Fin 2) K) :
    (lazardView f).natDegree = degreeOf 0 f :=
  natDegree_finSuccEquiv f

/-- **The degree bridge** (under a dominant order): for a `MonomialOrder (Fin 2) m` whose leading
monomial maximizes the variable-`0` exponent (`hdom`), the index-`0` component of `m.degree f` is
the `K[x][y]` `natDegree`. Combines `hdom` with `natDegree_finSuccEquiv`. -/
theorem degree_apply_zero_eq_natDegree_lazardView {K : Type*} [Field K] {m : MonomialOrder (Fin 2)}
    (hdom : ∀ f : MvPolynomial (Fin 2) K, f ≠ 0 → (m.degree f) 0 = degreeOf 0 f)
    {f : MvPolynomial (Fin 2) K} (hf : f ≠ 0) :
    (m.degree f) 0 = (lazardView f).natDegree := by
  rw [hdom f hf, natDegree_lazardView]

/-- **`leadingYCoeff f ≠ 0 ↔ f ≠ 0`**: the leading-`y`-coefficient vanishes exactly when `f` does
(`Polynomial.leadingCoeff_ne_zero` through the `finSuccEquiv` injection). -/
@[simp] theorem leadingYCoeff_ne_zero {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K} :
    leadingYCoeff f ≠ 0 ↔ f ≠ 0 := by
  rw [ne_eq, ne_eq, leadingYCoeff, Polynomial.leadingCoeff_eq_zero, lazardView_eq_zero_iff]

/-- **`leadingYCoeff f = 0 ↔ f = 0`**. -/
@[simp] theorem leadingYCoeff_eq_zero {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K} :
    leadingYCoeff f = 0 ↔ f = 0 := by
  rw [leadingYCoeff, Polynomial.leadingCoeff_eq_zero, lazardView_eq_zero_iff]

/-- **Multiplicativity of the leading-`y`-coefficient**: `leadingYCoeff (f * g) = leadingYCoeff f *
leadingYCoeff g` — `lazardView` is a ring hom into the domain `Polynomial (MvPolynomial (Fin 1) K)`
(no zero divisors), so `Polynomial.leadingCoeff_mul` applies. -/
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

/-! ## Toward Lazard's Lemma 2: the `y`-shift toolbox

Lazard (1985), Lemma 2 — the leading-`y`-coefficient `R_{i+1} = leadingYCoeff f_{i+1}` divides
`Rᵢ = leadingYCoeff fᵢ` along a minimal bivariate Gröbner basis sorted by increasing `y`-degree
(Lemma 1, `lazard_lemma1`). The proof's algebraic core: since `d(i) < d(i+1)` the ideal members
`y^{d(i+1)−d(i)}·fᵢ` and `f_{i+1}` share `y`-degree `d(i+1)`; dividing their leading terms produces an
ideal element of `y`-degree `d(i+1)` whose leading-`y`-coefficient is `gcd(Rᵢ, R_{i+1})`; its leading
monomial must be divisible by some basis element's leading monomial, and minimality forces
`R_{i+1} = gcd(Rᵢ, R_{i+1})`, i.e. `R_{i+1} ∣ Rᵢ`.

The `y`-shift `f ↦ y^k·f` is the move that aligns the two `y`-degrees. Under the `K[x][y]` view
(`y = X 0`), it multiplies `lazardView` by `Polynomial.X ^ k`, so it adds `k` to the `y`-degree and
leaves the leading-`y`-coefficient unchanged. These facts (`degreeOf_X_pow_mul`,
`leadingYCoeff_X_pow_mul`) and the resulting same-`y`-degree alignment (`leadingYCoeff_yShift_eq`)
are formalized; the full divisibility conclusion rests on Lazard's Theorem 1 structure (content /
primpart / `Pₖ = Rₖ·Sₖ`), which is unformalized — see the §2.6 residual. -/

/-- The `K[x][y]` view of a `y`-shift: `lazardView (X 0 ^ k * f) = Polynomial.X ^ k * lazardView f`
(`finSuccEquiv (X 0) = Polynomial.X`). -/
theorem lazardView_X_pow_mul {K : Type*} [Field K] (k : ℕ) (f : MvPolynomial (Fin 2) K) :
    lazardView (X 0 ^ k * f) = Polynomial.X ^ k * lazardView f := by
  rw [lazardView, lazardView, map_mul, map_pow, finSuccEquiv_X_zero]

/-- **`y`-shift adds `k` to the `y`-degree**: `degreeOf 0 (X 0 ^ k * f) = degreeOf 0 f + k` for
`f ≠ 0` (the `K[x][y]` `natDegree` of `X^k * lazardView f`). -/
theorem degreeOf_X_pow_mul {K : Type*} [Field K] (k : ℕ) {f : MvPolynomial (Fin 2) K} (hf : f ≠ 0) :
    degreeOf 0 (X 0 ^ k * f) = degreeOf 0 f + k := by
  have hne : lazardView f ≠ 0 := lazardView_eq_zero_iff.not.mpr hf
  rw [← natDegree_lazardView, ← natDegree_lazardView, lazardView_X_pow_mul,
    Polynomial.natDegree_X_pow_mul k hne]

/-- **`y`-shift fixes the leading-`y`-coefficient**: `leadingYCoeff (X 0 ^ k * f) = leadingYCoeff f`
(`Polynomial.leadingCoeff_mul_X_pow`). -/
theorem leadingYCoeff_X_pow_mul {K : Type*} [Field K] (k : ℕ) (f : MvPolynomial (Fin 2) K) :
    leadingYCoeff (X 0 ^ k * f) = leadingYCoeff f := by
  rw [leadingYCoeff, leadingYCoeff, lazardView_X_pow_mul, mul_comm, Polynomial.leadingCoeff_mul_X_pow]

/-- **The same-`y`-degree alignment of Lazard's Lemma 2** (the `R_{i+1} ∣ Rᵢ` setup): if `fᵢ` has
`y`-degree `dᵢ` and `f_{i+1}` has `y`-degree `d_{i+1}` with `dᵢ ≤ d_{i+1}`, then the `y`-shifted
`y^{d_{i+1}−dᵢ}·fᵢ` matches the `y`-degree `d_{i+1}` of `f_{i+1}` while keeping the leading-`y`-coefficient
`Rᵢ` — so their leading terms (degree `d_{i+1}`) can be divided, the step producing `gcd(Rᵢ, R_{i+1})`. -/
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

The leading-`y`-coefficients `Rₖ = leadingYCoeff fₖ` live in `MvPolynomial (Fin 1) K ≃ K[x]`, a
**principal ideal domain**. Lazard's Lemma 2 needs (i) a chosen `gcd` (`MvPolynomial (Fin 1) K`
is a UFD, hence a `GCDMonoid` via `UniqueFactorizationMonoid.toGCDMonoid`), and (ii) **Bézout's
identity** — `gcd g g'` as a `K[x]`-combination `a·g + b·g'` (transferring `K[x]`'s `IsBezout`
through the ring equivalence `MvPolynomial (Fin 1) K ≃+* K[x]`). These are provided as local
`letI` instances inside the lemmas; no global instance is registered (to avoid diamonds). -/

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
/-- **Bézout's identity for the leading-`y`-coefficient ring** (for the chosen `GCDMonoid`):
there are `a, b ∈ MvPolynomial (Fin 1) K` with `a·g + b·g' = gcd g g'`. -/
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

-- Restatements against the intended wording.
noncomputable example {K : Type*} [Field K] : MvPolynomial (Fin 1) K ≃+* Polynomial K :=
  mvPolynomialFinOneEquivPolynomial K

example {K : Type*} [Field K] (g g' : MvPolynomial (Fin 1) K) :
    ∃ a b : MvPolynomial (Fin 1) K,
      a * g + b * g' = @gcd _ _ (gcdMonoidMvPolynomialFinOne K) g g' :=
  exists_mul_add_mul_eq_gcd g g'

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

end DeepWiki.SymbolicIntegration
