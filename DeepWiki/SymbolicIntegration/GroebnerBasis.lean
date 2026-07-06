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
import DeepWiki.SymbolicIntegration.Core.Polynomial.GroebnerDivideOutCommonFactor
import DeepWiki.SymbolicIntegration.Core.Polynomial.GroebnerDividedBasis

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

end DeepWiki.SymbolicIntegration
