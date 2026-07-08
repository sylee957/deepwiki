import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.Data.Finsupp.MonomialOrder
import DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner.BasisBasic
import DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner.BuchbergerAlgorithm

/-! # Gröbner auto-reduction

Auto-reduction replaces each basis element by its remainder modulo the other
elements while preserving leading degrees and the generated ideal.
-/

open MvPolynomial MonomialOrder

namespace DeepWiki.SymbolicIntegration

variable {σ : Type*} {m : MonomialOrder σ} {R : Type*} [CommRing R]

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
    refine ⟨hsubI, hlc', ?_⟩
    change leadTermIdeal m (autoReduce m hBu) = initialIdeal m I
    rw [hltideal]
    unfold leadTermIdeal
    exact hB.2.2
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

end DeepWiki.SymbolicIntegration
