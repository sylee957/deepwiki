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
import DeepWiki.SymbolicIntegration.Core.Polynomial.GroebnerBuchbergerCriterion

/-! # Buchberger algorithm

Buchberger completion by adjoining nonzero S-polynomial remainders, with the
fixed-point criterion and termination/correctness theorem. -/

open MvPolynomial MonomialOrder

namespace DeepWiki.SymbolicIntegration

variable {σ : Type*} {m : MonomialOrder σ} {R : Type*} [CommRing R]
variable {I : Ideal (MvPolynomial σ R)} {B : Set (MvPolynomial σ R)}
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

end DeepWiki.SymbolicIntegration
