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
import DeepWiki.SymbolicIntegration.Core.Polynomial.GroebnerBuchbergerAlgorithm
import DeepWiki.SymbolicIntegration.Core.Polynomial.GroebnerBasisExistence
import DeepWiki.SymbolicIntegration.Core.Polynomial.GroebnerReducedBasis
import DeepWiki.SymbolicIntegration.Core.Polynomial.GroebnerBivariateView
import DeepWiki.SymbolicIntegration.Core.Polynomial.GroebnerOneVariableGcd
import DeepWiki.SymbolicIntegration.Core.Polynomial.GroebnerLeadingYCoeffGcd
import DeepWiki.SymbolicIntegration.Core.Polynomial.GroebnerBivariateSorting
import DeepWiki.SymbolicIntegration.Core.Polynomial.GroebnerReductionStep
import DeepWiki.SymbolicIntegration.Core.Polynomial.GroebnerBoundedReduction
import DeepWiki.SymbolicIntegration.Core.Polynomial.GroebnerLazardStep
import DeepWiki.SymbolicIntegration.Core.Polynomial.GroebnerCommonFactor
import DeepWiki.SymbolicIntegration.Core.Polynomial.GroebnerLazardDescent
import DeepWiki.SymbolicIntegration.Core.Polynomial.GroebnerLazardFactorization
import DeepWiki.SymbolicIntegration.Core.Polynomial.GroebnerNoCommonYFactor

/-! # Gröbner bases over a monomial order

A Gröbner-basis predicate over Mathlib's monomial-order division algorithm:
`IsGroebnerBasis m I B` says the leading monomials of `B ⊆ I` generate the initial
ideal of `I`, with the characteristic property `f ∈ I ↔` remainder `= 0`. -/

open MvPolynomial MonomialOrder

namespace DeepWiki.SymbolicIntegration

variable {σ : Type*} {m : MonomialOrder σ} {R : Type*} [CommRing R]
variable {I : Ideal (MvPolynomial σ R)} {B : Set (MvPolynomial σ R)}

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

/-! ### Part A: dividing out a common factor preserves the Gröbner-basis structure

Lazard (1985), Theorem 1 proof: `hgᵢ := fᵢ / (P·Gₖ₊₁)` is a minimal Gröbner basis iff the `fᵢ`
are, "since `LM(P·Gₖ₊₁)` divides every `LM(fᵢ)` and the relations of divisibility between the
leading monomials are preserved". The arithmetic core is the **leading-monomial shift**: writing
`b = h * q` (a common factor `h ∣ b`), `m.degree b = m.degree h + m.degree q` and
`m.leadingCoeff b = m.leadingCoeff h * m.leadingCoeff q` — so every leading monomial of the divided
set drops by exactly `m.degree h`, an order-isomorphism on degrees that preserves divisibility and
minimality. This is the reachable framework half; the genuine wall (which `h` to divide by so the
quotient's minimal element lands in `K[x]`) is Part B. -/

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
