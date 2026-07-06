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
