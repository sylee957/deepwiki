import Mathlib.FieldTheory.Differential.Liouville
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Tactic

/-! # The transcendental logarithmic Liouville extension (completeness keystone)

Rosenlicht's *Integration in finite terms* (1972), transcendental logarithmic case of Liouville's
theorem.  Mathlib already has the **differential-Liouville framework**
(`Mathlib/FieldTheory/Differential/Liouville.lean`): `class IsLiouville F K`, `IsLiouville.trans`,
`IsLiouville.equiv`, and `isLiouville_of_finiteDimensional` (every algebraic char-0 extension is
Liouville, via the Galois normal-closure + trace-averaging argument).  The **transcendental**
instances — that a simple transcendental *logarithmic* extension `F(t)` with `t' = u'/u =
logDeriv u` (`t = log u`, `u ∈ F`) is Liouville over `F` — are exactly what is missing, and they
are the single piece the whole transcendental Risch *completeness* direction waits on.

This file **builds the full setup** for the log monomial faithfully and reduces the keystone to a
**single sharp partial-fraction residual** (`DerivSimplePoleSeparation`), with the genuine
transcendence input isolated as `NondegenerateLog u` (`log u ∉ F`).

## Status (the keystone roadmap)

- **Setup — CLOSED.**  `logDifferential u : Differential (RatFunc F)` is a *genuine* differential
  field structure with `t' = u'/u`, and `logDifferentialAlgebra u : DifferentialAlgebra F (RatFunc
  F)` is real — so `F(log u) = RatFunc F` is an actual differential field extension of `F`.  The
  load-bearing piece is `fracDeriv`: **a derivation on `F[X]` extends to its fraction field by the
  quotient rule** — a self-derivation `Derivation ℤ K K` for any fraction field `K` of `F[X]`,
  built from scratch here (Mathlib has no such extension — only the Kähler-module-valued
  localization).  This is Mathlib-contributable on its own.
- **The keystone — UNCONDITIONAL modulo `NondegenerateLog u` + one partial-fraction residual.**
  `isLiouville_logExtension (hnd : NondegenerateLog u) (hsep : DerivSimplePoleSeparation u) :
  IsLiouville F (RatFunc F)` (axiom-clean: `propext, Classical.choice, Quot.sound`).  The entire
  Rosenlicht multi-term pole-matching is **proved** here: the corrected `v`-reduction
  `deriv_mem_range_imp_linear` (`v′ ∈ F ⟹ v = v₀ + b·t`), the UFD factorization fold
  (`logDeriv_algebraMap_eq_unit_add_sum`), the per-`w` and multi-term pole decompositions
  (`logDeriv_eq_wConst_add_sum`, `sum_const_logDeriv_eq_wConst_add_pole`), the constant-residue
  cancellation `poleIndependence_finset_const`, and the assembly
  `multiLogPoleObligation_of_nondegenerateLog`.  Both `RationalToPolyObligation` and
  `PoleIndependenceObligation` are now **theorems** from `NondegenerateLog`.  The *sole* remaining
  content is `DerivSimplePoleSeparation u`: a twisted-derivative `v′` has no *simple* `t`-pole (its
  poles have order `≥ 2`, since `D(r·π⁻ᵏ) = … − k·r·(Dπ)·π⁻ᵏ⁻¹` with `π ∤ Dπ`), so the order-`1`
  poles `logDeriv π` separate.  Discharging it (a partial-fractions-with-multiplicities +
  per-irreducible twisted pole-order development; Mathlib has only the *formal-derivative*,
  *root*-multiplicity analogue `rootMultiplicity_sub_one_le_derivative_rootMultiplicity`) makes the
  keystone unconditional modulo `NondegenerateLog` alone.
- **Obligation 4 (`ContainConstants`, only for towering logs).**  Polynomial layer discharged
  (`eq_C_of_logDerivPoly_eq_zero`); reduces to `NoDegreeDropObligation` (the transcendence input)
  and carries `logDeriv u ≠ 0` (when `u' = 0`, `log u` *is* a new constant — `ContainConstants`
  genuinely fails).

## Orientation: the log monomial derivation

`F` is a `Differential` field of characteristic `0`.  Fix `u ∈ F`, and let `c := logDeriv u = u'/u`
(a *constant of `F`* exactly when `u' = 0`, but in general just an element of `F`).  The simple
transcendental logarithmic extension is `F(t) = RatFunc F` with the derivation extended by
`t' = c` (the **log monomial**: `D t = u'/u`, NOT `t' = 1`).  Concretely, on the polynomial ring
`F[t]` this is `Differential.implicitDeriv (C c)` — Mathlib's "the unique derivation making a
`DifferentialAlgebra F F[t]` with `t' = v`" — instantiated at the *constant* polynomial `v = C c`,
then extended to `RatFunc F` by `fracDeriv`.
-/

open scoped Differential
open Polynomial Differential

namespace DeepWiki.SymbolicIntegration.LiouvilleLog

section PolynomialSetup

variable {F : Type*} [Field F] [Differential F]

/-- The log-monomial coefficient `c = logDeriv u = u'/u`; `t' = c` for `t = log u`. -/
noncomputable abbrev logCoeff (u : F) : F := logDeriv u

/-- The log-monomial derivation on `F[t]`: `Differential.implicitDeriv (C (logDeriv u))`,
the unique derivation making `F[t]` a `DifferentialAlgebra F F[t]` with `t' = u'/u`. -/
noncomputable def logDerivPoly (u : F) : Derivation ℤ F[X] F[X] :=
  Differential.implicitDeriv (C (logCoeff u))

/-- `F[t]` as a `Differential` ring under the log-monomial derivation `t' = u'/u`. -/
@[reducible]
noncomputable def logDifferentialPoly (u : F) : Differential F[X] :=
  ⟨logDerivPoly u⟩

/-- On `F[t]` with `t' = u'/u`, `t' = C (u'/u)` (the log-monomial defining equation, `t = log u`). -/
@[simp]
lemma logDerivPoly_X (u : F) : logDerivPoly u (X : F[X]) = C (logCoeff u) := by
  simp [logDerivPoly]

/-- On `F[t]`, the derivation sends a constant `C b` to `C b'` (it extends `F`'s derivation). -/
@[simp]
lemma logDerivPoly_C (u : F) (b : F) : logDerivPoly u (C b) = C b′ := by
  simp [logDerivPoly]

/-- The log-monomial derivation makes `F[t]` a `DifferentialAlgebra F F[t]` (extends `F`). -/
lemma logDerivPoly_differentialAlgebra (u : F) :
    letI := logDifferentialPoly u
    DifferentialAlgebra F F[X] := by
  letI := logDifferentialPoly u
  refine ⟨fun a => ?_⟩
  change logDerivPoly u (C a) = C a′
  simp

/-- **The coefficient formula for the log-monomial derivation** (engine of all degree/pole
comparisons): `(D p).coeff i = (p.coeff i)' + (u'/u)·(i+1)·p.coeff (i+1)`.  The first summand is
the "constant-field" part (`F`'s derivation on each coefficient); the second is the monomial part
`t' · (∂p/∂t)`. -/
lemma coeff_logDerivPoly (u : F) (p : F[X]) (i : ℕ) :
    (logDerivPoly u p).coeff i
      = (p.coeff i)′ + logCoeff u * ((i + 1) * p.coeff (i + 1)) := by
  simp only [logDerivPoly, implicitDeriv, Derivation.coe_add, Pi.add_apply,
    Derivation.coe_smul, Pi.smul_apply, Derivation.restrictScalars_apply,
    derivative'_apply, coeff_add, coeff_mapCoeffs, smul_eq_mul, coeff_C_mul,
    coeff_derivative]
  ring

/-- The log-monomial derivation does **not raise `t`-degree**: `natDegree (D p) ≤ natDegree p`.
This is the structural fact behind "the `t`-poles/degree of `a ∈ F` are controlled" in the
transcendental Liouville argument. -/
lemma natDegree_logDerivPoly_le (u : F) (p : F[X]) :
    (logDerivPoly u p).natDegree ≤ p.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [coeff_logDerivPoly]
  have h1 : p.coeff i = 0 := coeff_eq_zero_of_natDegree_lt hi
  have h2 : p.coeff (i + 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (le_of_lt hi) (Nat.lt_succ_self i))
  rw [h1, h2]
  simp

/-- **At the top `t`-degree the monomial part vanishes**: the `t`-leading coefficient transforms by
`F`'s derivation alone, `(D p).coeff (deg p) = (leadingCoeff p)'`.  This is the non-degeneracy that
makes "a new constant would be algebraic, contradicting transcendence" work: a polynomial `p` of
positive `t`-degree with `D p = 0` would need `(leadingCoeff p)' = 0` and the `t`-coupling to cancel
exactly, which (in char 0) forces `t` algebraic. -/
lemma coeff_natDegree_logDerivPoly (u : F) (p : F[X]) :
    (logDerivPoly u p).coeff p.natDegree = (p.leadingCoeff)′ := by
  rw [coeff_logDerivPoly]
  have h : p.coeff (p.natDegree + 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _)
  rw [h, leadingCoeff]
  simp

/-- A *constant of `F`* viewed in `F[t]` is annihilated by the log-monomial derivation
(`b' = 0 → D (C b) = 0`).  Conversely (`ContainConstants` direction, an obligation below) every
`t`-polynomial constant is such a `C b` — this is where transcendence of `t` enters. -/
lemma logDerivPoly_C_of_deriv_eq_zero (u : F) {b : F} (hb : b′ = 0) :
    logDerivPoly u (C b) = 0 := by
  rw [logDerivPoly_C, hb, map_zero]

/-! ### The `t`-polynomial `ContainConstants` engine (Obligation 4, polynomial layer)

These are the proven pieces of "no new constants on `F[t]`", driving the `ContainConstantsObligation`
and the `v ∈ F` half of Obligation 3 (Rosenlicht). -/

/-- **`t`-constant ⟹ `t`-leading coefficient is an `F`-constant.**  If `D p = 0` then `(leadingCoeff
p)' = 0`: the highest `t`-coefficient of a `t`-constant is itself a constant of `F`.  Direct from
`coeff_natDegree_logDerivPoly` (the top coefficient sees only `F`'s derivation). -/
lemma leadingCoeff_deriv_eq_zero_of_logDerivPoly_eq_zero (u : F) {p : F[X]}
    (h : logDerivPoly u p = 0) : (p.leadingCoeff)′ = 0 := by
  have := coeff_natDegree_logDerivPoly u p
  rw [h, coeff_zero] at this
  exact this.symm

/-- **A `t`-constant of `t`-degree `0` is a single `F`-constant `C b` with `b' = 0`.**  The base case
of "constants don't grow": a degree-`0` `t`-polynomial annihilated by `D` is `C (p.coeff 0)` with
that coefficient an `F`-constant. -/
lemma eq_C_of_logDerivPoly_eq_zero_of_natDegree_eq_zero (u : F) {p : F[X]}
    (h : logDerivPoly u p = 0) (hdeg : p.natDegree = 0) :
    ∃ b : F, p = C b ∧ b′ = 0 := by
  refine ⟨p.coeff 0, Polynomial.eq_C_of_natDegree_eq_zero hdeg, ?_⟩
  have := coeff_logDerivPoly u p 0
  rw [h, coeff_zero] at this
  have hc1 : p.coeff 1 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  rw [hc1] at this
  simpa using this.symm

/-- **The transcendence obstruction, made precise (a genuine adjudication).**  The remaining content
of "`t`-constant ⟹ `t`-degree `0`" (which closes `ContainConstantsObligation`) is exactly:
*for a genuine log monomial there is no degree drop solvable inside `F`.*  Concretely, if `p = C b·t
+ (lower)` with `b' = 0` and `D p = 0`, the coefficient-`(deg−1)` relation forces an `a ∈ F` with
`a' = −(deg)·b·logDeriv u`, i.e. `(deg)·b·(u'/u)` must be a *derivative of an `F`-element*.  This is
**not** a coefficient identity — it is the transcendence statement "`log u ∉ F`", and is precisely
where `t` being a genuine new transcendental (`logDeriv u ≠ 0` and `u'/u` has no antiderivative in
`F`) enters.  When `logDeriv u = 0` (`u` an `F`-constant) the statement is genuinely **false**:
`t = log u` is then itself a *new constant*, so the constants legitimately grow and
`ContainConstants F F(t)` fails — the obligation must carry `logDeriv u ≠ 0`.  This `def` records the
exact residual obligation (the "no `F`-antiderivative of `b·logDeriv u`" input) for a follow-up. -/
def NoDegreeDropObligation (u : F) : Prop :=
  logDeriv u ≠ 0 →
    ∀ {p : F[X]}, logDerivPoly u p = 0 → p.natDegree = 0

/-- **GIVEN the no-degree-drop input, `t`-constants are single `F`-constants** — the full polynomial
`ContainConstants` engine.  This reduces `ContainConstantsObligation` to `NoDegreeDropObligation`
(the transcendence input), with everything else discharged here. -/
lemma eq_C_of_logDerivPoly_eq_zero (u : F) (hndd : NoDegreeDropObligation u)
    (hu : logDeriv u ≠ 0) {p : F[X]} (h : logDerivPoly u p = 0) :
    ∃ b : F, p = C b ∧ b′ = 0 :=
  eq_C_of_logDerivPoly_eq_zero_of_natDegree_eq_zero u h (hndd hu h)

/-! ### The Rosenlicht pole-counting engine (Obligation 3, polynomial layer)

The mechanism behind "matching `t`-pole orders": `logDeriv` of a **monic** `t`-polynomial `π` is a
*proper* rational function in `t` (`logDeriv π = (D π)/π` with `deg (D π) < deg π`), so it genuinely
contributes a `t`-pole that can be cancelled **only** by another `wᵢ`'s pole, never by `a ∈ F` (which
has none).  This is the precise fact that forces the `t`-polynomial parts of the `wᵢ` to combine into
a single `logDeriv u`-multiple. -/

/-- **`logDeriv` of a monic `t`-polynomial is proper**: for monic `p` with `deg p ≥ 1`, `D p` has
strictly smaller `t`-degree than `p`.  Hence `logDeriv p = (D p)/p` is a proper rational function of
`t` (a genuine `t`-pole).  Proof: at the top degree `D p` sees only `(leadingCoeff p)' = (1)' = 0`
(`coeff_natDegree_logDerivPoly`), so the top coefficient of `D p` vanishes and its degree drops. -/
lemma natDegree_logDerivPoly_lt_of_monic (u : F) {p : F[X]} (hm : p.Monic)
    (hdeg : 1 ≤ p.natDegree) : (logDerivPoly u p).natDegree < p.natDegree := by
  rcases lt_or_eq_of_le (natDegree_logDerivPoly_le u p) with h | h
  · exact h
  · exfalso
    have htop : (logDerivPoly u p).coeff p.natDegree = 0 := by
      rw [coeff_natDegree_logDerivPoly, hm.leadingCoeff]; simp
    by_cases hz : logDerivPoly u p = 0
    · rw [hz, natDegree_zero] at h; omega
    · have hlc : (logDerivPoly u p).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hz
      rw [leadingCoeff, h] at hlc
      exact hlc htop

/-- **The `t`-polynomial part of a `logDeriv` folds into `logDeriv u`.**  For `w = C b · tⁿ` (a pure
`t`-power scaled by an `F`-element `b ≠ 0`, `n ≥ 1`), `logDeriv w = logDeriv (C b) + n · logDeriv t`,
and `logDeriv t = D t / t = C (u'/u) / t`.  This is the "`logDeriv` of the `t`-part contributes only
`n · t'/(…)`" step (degenerate monomial case): the `t`-power's logarithmic-derivative is
`n · (u'/u)/t`, a single pole that the global pole-matching cancels into the constants.  (Stated on
`F[t]`; the `/t` lives in `F(t)`.  The general monic-factor case is `natDegree_logDerivPoly_lt_of_monic`
above.) -/
lemma logDerivPoly_monomial_eq (u : F) (n : ℕ) (b : F) :
    logDerivPoly u (C b * X ^ n)
      = C b′ * X ^ n + C b * C (logCoeff u) * (n : F[X]) * X ^ (n - 1) := by
  rw [Derivation.leibniz, logDerivPoly_C]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · rw [Derivation.leibniz_pow, logDerivPoly_X, nsmul_eq_mul]
    ring

/-- **Pole-order drops by at most one under the log-monomial derivation** (the pure-Leibniz core of
the `t`-pole analysis, fully provable for *any* derivation).  If `q^n ∣ p` then `q^(n-1) ∣ D p`:
differentiating `p = q^n · r` gives `D p = (n · q^(n-1) · D q) · r + q^n · D r`, both summands divisible
by `q^(n-1)` (`Derivation.leibniz`, `Derivation.leibniz_pow`).  This is the general-derivation analogue
of Mathlib's `Polynomial.pow_sub_one_dvd_derivative_of_pow_dvd` (which is stated only for the formal
`derivative`).  It is the load-bearing divisibility behind "the `t`-derivative raises pole order" in the
`RationalToPolyObligation` / `PoleIndependenceObligation` analyses — the *strict* increase additionally
needs `q ∤ D q` (`not_dvd_logDerivPoly_of_natDegree_lt` below), which is where transcendence enters. -/
lemma pow_sub_one_dvd_logDerivPoly (u : F) {p q : F[X]} {n : ℕ} (hdvd : q ^ n ∣ p) :
    q ^ (n - 1) ∣ logDerivPoly u p := by
  obtain ⟨r, rfl⟩ := hdvd
  -- `q^(n-1) ∣ D(q^n)` directly from `leibniz_pow` (`D(q^n) = ↑n * (q^(n-1) * D q)`).
  have hpn : q ^ (n - 1) ∣ logDerivPoly u (q ^ n) := by
    rw [Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul]
    exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _
  -- `q^(n-1) ∣ q^n` (so the `q^n · D r` summand is divisible).
  have hpow : q ^ (n - 1) ∣ q ^ n := pow_dvd_pow q (Nat.sub_le n 1)
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  exact dvd_add (dvd_mul_of_dvd_left hpow _) (dvd_mul_of_dvd_right hpn _)

/-- **The log-monomial derivative of `q^k · m` factors a clean `q^(k-1)`** (the engine of the *exact*
pole-order drop): `D(q^k · m) = q^(k-1) · (k · (D q) · m + q · D m)` for `k ≥ 1`.  The bracket carries
the leading pole term `k · (D q) · m`; combined with `q ∤ D q` (transcendence) and `q ∤ m` (exact
multiplicity) it makes the pole order drop by *exactly* one. -/
lemma logDerivPoly_pow_mul (u : F) {q m : F[X]} {k : ℕ} (hk : 1 ≤ k) :
    logDerivPoly u (q ^ k * m)
      = q ^ (k - 1) * ((k : F[X]) * logDerivPoly u q * m + q * logDerivPoly u m) := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, Derivation.leibniz_pow, nsmul_eq_mul,
    smul_eq_mul]
  have hqk : q ^ k = q ^ (k - 1) * q := by
    rw [← pow_succ]; congr 1; omega
  rw [hqk]; ring

/-- **A monic irreducible factor `q` does not divide `D p` to its full multiplicity** (the *exact*
strict pole-order drop, the real content of "`v′` has no simple pole"): if `q ∤ D q` (transcendence),
`q^k ∣ p` but `q^(k+1) ∤ p` (so `q^k ∣∣ p`, `k ≥ 1`), then `q^k ∤ D p`.  With
`pow_sub_one_dvd_logDerivPoly` (`q^(k-1) ∣ D p`) this pins `v_q(D p) = k − 1` exactly.  Proof:
`p = q^k · m` with `q ∤ m`, and `D p = q^(k-1) · (k · (D q) · m + q · D m)` (`logDerivPoly_pow_mul`); since
`q` is prime and `q` divides none of `↑k` (char 0), `D q` (hyp), `m` (exact), `q ∤ (k·(D q)·m + q·D m)`,
so `q^k = q^(k-1)·q ∤ D p`. -/
lemma not_pow_dvd_logDerivPoly_of_exact [CharZero F] (u : F) {p q : F[X]} {k : ℕ}
    (hq : Irreducible q) (hDq : ¬ q ∣ logDerivPoly u q) (hk : 1 ≤ k)
    (hdvd : q ^ k ∣ p) (hndvd : ¬ q ^ (k + 1) ∣ p) : ¬ q ^ k ∣ logDerivPoly u p := by
  obtain ⟨m, rfl⟩ := hdvd
  -- `q ∤ m` (else `q^(k+1) ∣ q^k·m`).
  have hqm : ¬ q ∣ m := by
    rintro ⟨m', rfl⟩
    exact hndvd ⟨m', by rw [pow_succ]; ring⟩
  rw [logDerivPoly_pow_mul u (q := q) (m := m) hk]
  -- `q^k = q^(k-1)·q`; cancel `q^(k-1)` to reduce to `q ∤ (k·Dq·m + q·Dm)`.
  have hqk : q ^ k = q ^ (k - 1) * q := by rw [← pow_succ]; congr 1; omega
  rw [hqk]
  intro hdvd'
  have hcancel : q ∣ ((k : F[X]) * logDerivPoly u q * m + q * logDerivPoly u m) :=
    (mul_dvd_mul_iff_left (pow_ne_zero (k - 1) hq.ne_zero)).mp hdvd'
  -- `q ∣ q·Dm`, so `q ∣ k·Dq·m`; `q` prime divides none of `↑k`, `Dq`, `m`.
  have hk_part : q ∣ (k : F[X]) * logDerivPoly u q * m :=
    (dvd_add_right (dvd_mul_right q (logDerivPoly u m))).mp (by rwa [add_comm] at hcancel)
  have hkne : ¬ q ∣ (k : F[X]) := by
    intro hdvdk
    have : q.natDegree ≤ ((k : F[X])).natDegree :=
      Polynomial.natDegree_le_of_dvd hdvdk (by
        simpa using (Nat.cast_ne_zero.mpr (by omega : k ≠ 0) : (k : F) ≠ 0))
    have hkdeg : ((k : F[X])).natDegree = 0 := Polynomial.natDegree_natCast k
    have := hq.natDegree_pos
    omega
  rcases (hq.prime.dvd_mul.mp hk_part) with h1 | h2
  · rcases (hq.prime.dvd_mul.mp h1) with hk' | hDq'
    · exact hkne hk'
    · exact hDq hDq'
  · exact hqm h2

/-- **The `π`-adic valuation of `D p` is exactly one less than that of `p`** (the exact pole-order
drop, as an `emultiplicity` equality): for monic irreducible `π` with `π ∤ D π` (transcendence),
`emultiplicity π p = k` with `k ≥ 1` forces `emultiplicity π (logDerivPoly u p) = k − 1`.  Combines
`pow_sub_one_dvd_logDerivPoly` (the `≥ k−1` half) with `not_pow_dvd_logDerivPoly_of_exact` (the `< k`
half).  This is the engine of "`v′` has no simple pole": a pole of order `k` in `v` becomes a pole of
order exactly `k + 1` in `v′`. -/
lemma emultiplicity_logDerivPoly_eq [CharZero F] (u : F) {p q : F[X]} {k : ℕ}
    (hq : Irreducible q) (hDq : ¬ q ∣ logDerivPoly u q) (hk : 1 ≤ k)
    (hmult : emultiplicity q p = (k : ℕ∞)) :
    emultiplicity q (logDerivPoly u p) = ((k - 1 : ℕ) : ℕ∞) := by
  -- `q^k ∣ p` and `q^(k+1) ∤ p` from the multiplicity equality.
  have hdvd : q ^ k ∣ p := pow_dvd_of_le_emultiplicity (by rw [hmult])
  have hndvd : ¬ q ^ (k + 1) ∣ p := by
    rw [← emultiplicity_lt_iff_not_dvd, hmult]; exact_mod_cast Nat.lt_succ_self k
  -- `q^(k-1) ∣ D p` (lower bound) and `q^k ∤ D p` (strict upper bound).
  have hlo : ((k - 1 : ℕ) : ℕ∞) ≤ emultiplicity q (logDerivPoly u p) :=
    le_emultiplicity_of_pow_dvd (pow_sub_one_dvd_logDerivPoly u hdvd)
  have hhi : emultiplicity q (logDerivPoly u p) < (k : ℕ∞) :=
    emultiplicity_lt_iff_not_dvd.mpr (not_pow_dvd_logDerivPoly_of_exact u hq hDq hk hdvd hndvd)
  -- `k - 1 ≤ … < k = (k-1)+1` forces `… = k - 1`.
  have hk1 : (k : ℕ∞) = ((k - 1 : ℕ) : ℕ∞) + 1 := by
    rw [← ENat.coe_one, ← Nat.cast_add]; congr 1; omega
  rw [hk1] at hhi
  exact le_antisymm ((ENat.lt_add_one_iff (ENat.coe_ne_top _)).mp hhi) hlo

/-- **A monic `t`-factor `q` does not divide its own log-monomial derivative `D q`**, *provided*
`D q ≠ 0` (and `q` has positive degree): since `(D q).natDegree < q.natDegree`
(`natDegree_logDerivPoly_lt_of_monic`), a nonzero `D q` is too low-degree to be a `q`-multiple.  Hence
at a `q`-pole the order strictly increases — the missing strict half of `pow_sub_one_dvd_logDerivPoly`.
The hypothesis `D q ≠ 0` is *exactly* the transcendence input: for a genuine new transcendental
`t = log u` no monic irreducible of positive `t`-degree is annihilated by `D`, whereas if `F` already
contains an antiderivative `s` of `u'/u` then `q = t − C s` has `D q = 0` and the pole can vanish — so
this is unprovable from the abstract typeclasses alone (see the obligation notes below). -/
lemma not_dvd_logDerivPoly_of_natDegree_lt (u : F) {q : F[X]} (hm : q.Monic)
    (hdeg : 1 ≤ q.natDegree) (hDq : logDerivPoly u q ≠ 0) : ¬ q ∣ logDerivPoly u q := by
  intro hdvd
  have hlt := natDegree_logDerivPoly_lt_of_monic u hm hdeg
  have hle := Polynomial.natDegree_le_of_dvd hdvd hDq
  omega

/-- **`t = log u` is a genuine new (differentially transcendental) monomial.**  The unifying
non-degeneracy hypothesis the whole transcendental case is conditional on: *no monic irreducible
`t`-polynomial is annihilated by the log-monomial derivation* (`D π ≠ 0` for every monic irreducible
`π`).  This is precisely "`log u ∉ F`" — the Risch *new-monomial* condition: if some monic irreducible
`π` had `D π = 0` then (constant-term analysis on `π`) `F` would contain an antiderivative `s` of `u'/u`,
i.e. `log u = s ∈ F`, so `t` would be differentially algebraic over `F` and *not* a new transcendental.
Equivalent to `ContainConstants F (RatFunc F)` restricted to the log monomial.  Discharging the three
partial-fraction / transcendence obligations from this single `Prop` is the content below — so the
keystone `IsLiouville F (RatFunc F)` holds *whenever the log is a genuine new monomial*, which is exactly
what the Risch structure-theorem decision certifies. -/
def NondegenerateLog (u : F) : Prop :=
  ∀ π : F[X], π.Monic → Irreducible π → logDerivPoly u π ≠ 0

/-- **`NondegenerateLog u` forbids an `F`-antiderivative of `u'/u`** — the operational form of
"`log u ∉ F`".  If some `s ∈ F` had `s′ = logDeriv u`, then `X − C s` would be a monic irreducible with
`D (X − C s) = C(u'/u) − C(s′) = 0`, contradicting `NondegenerateLog`.  This is the single contradiction
both the degree-drop (`logDerivPoly_ne_zero_of_monic`) and the degree-`≤ 1` descent
(`natDegree_le_one_of_logDerivPoly_natDegree_eq_zero`) reduce to. -/
lemma not_isAntideriv_of_nondegenerateLog (u : F) (hnd : NondegenerateLog u) {s : F}
    (hs : s′ = logDeriv u) : False := by
  refine hnd (X - C s) (monic_X_sub_C s) (irreducible_X_sub_C s) ?_
  rw [map_sub, logDerivPoly_X, logDerivPoly_C, hs]
  simp

/-- **No monic `t`-polynomial of positive degree is annihilated by `D`, given `NondegenerateLog`.**
The key strengthening from irreducibles to *all* monic `d` of degree `m ≥ 1`: if `D d = 0` then the
coefficient-`(m−1)` relation (`coeff_logDerivPoly`, with `d.coeff m = 1` monic) gives
`(d.coeff (m−1))′ = −m·(u'/u)`, so `s := −(d.coeff (m−1))/m ∈ F` is an **antiderivative of `u'/u`**
(`s′ = logDeriv u`), forbidden by `not_isAntideriv_of_nondegenerateLog`.  (No induction or multiplicity
bookkeeping — the top-coefficient relation produces the forbidden antiderivative directly.) -/
lemma logDerivPoly_ne_zero_of_monic [CharZero F] (u : F) (hnd : NondegenerateLog u) {d : F[X]}
    (hm : d.Monic) (hdeg : 1 ≤ d.natDegree) : logDerivPoly u d ≠ 0 := by
  intro hDd
  set m := d.natDegree with hmdef
  have hmF : (m : F) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- Coefficient-`(m−1)` relation: `0 = (d.coeff (m−1))′ + (u'/u)·m·(d.coeff m)`, `d.coeff m = 1`.
  have hcoeff := coeff_logDerivPoly u d (m - 1)
  rw [hDd, coeff_zero] at hcoeff
  have hsucc : m - 1 + 1 = m := by omega
  rw [hsucc, hm.coeff_natDegree] at hcoeff
  have hcast : ((m - 1 : ℕ) : F) + 1 = (m : F) := by
    rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]; ring
  rw [hcast, mul_one] at hcoeff
  -- so `(d.coeff (m−1))′ = −m·(u'/u)`; set `s := −(d.coeff (m−1))/m`, then `s′ = u'/u`.
  refine not_isAntideriv_of_nondegenerateLog u hnd (s := -(d.coeff (m - 1)) / (m : F)) ?_
  have hmcast : Differential.deriv (m : F) = 0 := Derivation.map_natCast _ m
  rw [Differential.deriv.leibniz_div_const (-(d.coeff (m - 1))) (m : F) hmcast,
    smul_eq_mul, map_neg]
  rw [show (d.coeff (m - 1))′ = -((m : F) * logDeriv u) from by linear_combination -hcoeff]
  rw [neg_neg, ← mul_assoc, inv_mul_cancel₀ hmF, one_mul]

/-- **A monic `t`-polynomial of positive degree does not divide its own derivative `D d`, given
`NondegenerateLog`.**  Combines `logDerivPoly_ne_zero_of_monic` (`D d ≠ 0`) with the strict pole drop
`not_dvd_logDerivPoly_of_natDegree_lt` (`deg (D d) < deg d`).  This is the engine of the
rational-to-polynomial descent: at a `t`-pole `d` of order `k`, `D d` has order exactly `k − 1`, so the
pole strictly increases in `1/d`-derivatives and cannot disappear. -/
lemma not_dvd_logDerivPoly_of_monic [CharZero F] (u : F) (hnd : NondegenerateLog u) {d : F[X]}
    (hm : d.Monic) (hdeg : 1 ≤ d.natDegree) : ¬ d ∣ logDerivPoly u d :=
  not_dvd_logDerivPoly_of_natDegree_lt u hm hdeg (logDerivPoly_ne_zero_of_monic u hnd hm hdeg)

/-- **`D p` constant ⟹ `t`-degree `≤ 1`, given `NondegenerateLog`** — the *corrected* degree descent
(the formal `PolyVReductionObligation`'s `= 0` is false; the truth is `≤ 1`).  If `(D p).natDegree = 0`
and `m := p.natDegree ≥ 2`, the top coefficient is constant (`(leadingCoeff p)′ = 0`,
`coeff_natDegree_logDerivPoly`) and the coefficient-`(m−1)` relation forces `(p.coeff (m−1))′ =
−m·(leadingCoeff p)·(u'/u)`, so `s := −p.coeff (m−1)/(m·leadingCoeff p) ∈ F` is an antiderivative of
`u'/u` — forbidden (`not_isAntideriv_of_nondegenerateLog`).  Hence `m ≤ 1`.  (The surviving `t`-linear
term `b·t` is the *new logarithm* `b·log u`, not an `F`-element — which is exactly why the descent stops
at `≤ 1`, not `= 0`.) -/
lemma natDegree_le_one_of_logDerivPoly_natDegree_eq_zero [CharZero F] (u : F)
    (hnd : NondegenerateLog u) {p : F[X]} (h : (logDerivPoly u p).natDegree = 0) :
    p.natDegree ≤ 1 := by
  by_contra hlt
  rw [not_le] at hlt
  set m := p.natDegree with hmdef
  have hm2 : 2 ≤ m := hlt
  have hlcne : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr (by
    intro h0; rw [h0] at hmdef; simp at hmdef; omega)
  -- Top coefficient is an `F`-constant: `(leadingCoeff p)′ = 0`.
  have hlc0 : (p.leadingCoeff)′ = 0 := by
    have htop := coeff_natDegree_logDerivPoly u p
    rw [← htop]
    exact coeff_eq_zero_of_natDegree_lt (by rw [h]; omega)
  -- Coefficient-`(m−1)` relation: `(p.coeff (m−1))′ = −m·(leadingCoeff p)·(u'/u)`.
  have hcoeff := coeff_logDerivPoly u p (m - 1)
  have hzero : (logDerivPoly u p).coeff (m - 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by rw [h]; omega)
  rw [hzero] at hcoeff
  have hsucc : m - 1 + 1 = m := by omega
  have hlc : p.coeff m = p.leadingCoeff := rfl
  rw [hsucc, hlc] at hcoeff
  have hcast : ((m - 1 : ℕ) : F) + 1 = (m : F) := by
    rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]; ring
  rw [hcast] at hcoeff
  -- `s := −p.coeff (m−1)/(m·leadingCoeff p)` has `s′ = u'/u`: contradiction.
  have hmlcne : (m : F) * p.leadingCoeff ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) hlcne
  have hmlc0 : Differential.deriv ((m : F) * p.leadingCoeff) = 0 := by
    rw [Derivation.leibniz, Derivation.map_natCast, hlc0, smul_zero, smul_zero, add_zero]
  refine not_isAntideriv_of_nondegenerateLog u hnd
    (s := -(p.coeff (m - 1)) / ((m : F) * p.leadingCoeff)) ?_
  rw [Differential.deriv.leibniz_div_const (-(p.coeff (m - 1))) ((m : F) * p.leadingCoeff) hmlc0,
    smul_eq_mul, map_neg]
  rw [show (p.coeff (m - 1))′ = -((m : F) * p.leadingCoeff * logDeriv u) from by
    linear_combination -hcoeff]
  rw [neg_neg, ← mul_assoc, inv_mul_cancel₀ hmlcne, one_mul]

/-- **`NondegenerateLog u` forces `logDeriv u ≠ 0`** — a genuine new monomial is non-constant.  The
monomial `t = X` itself is monic irreducible (`monic_X`, `irreducible_X`) with `D X = C (u'/u)`; if
`u'/u = 0` then `D X = 0`, contradicting `NondegenerateLog`.  (When `u' = 0`, `log u` is a new
*constant*, not a new transcendental — exactly the degenerate case `NondegenerateLog` excludes.) -/
lemma logDeriv_ne_zero_of_nondegenerateLog (u : F) (hnd : NondegenerateLog u) : logDeriv u ≠ 0 := by
  intro h0
  refine hnd X monic_X irreducible_X ?_
  rw [logDerivPoly_X]
  simp [logCoeff, h0]

-- Restatements pinning the log-monomial setup to the book's wording (Rosenlicht §, log case).
-- `t' = u'/u`: the defining equation of the log monomial `t = log u`.
example (u : F) : logDerivPoly u (X : F[X]) = C (logDeriv u) := logDerivPoly_X u
-- The derivation on `F(t)` restricted to the linear monomial `b·t` (`b ∈ F`) is
-- `b'·t + b·(u'/u)`: the constant-field part plus the monomial part.
example (u b : F) :
    logDerivPoly u (C b * X) = C b′ * X + C b * C (logCoeff u) := by
  have := (logDerivPoly u).leibniz (C b) X
  simp only [logDerivPoly_C, logDerivPoly_X] at this
  rw [this]; ring
-- The coefficient formula is exactly `(D p).coeff i = (p.coeff i)' + (u'/u)·(i+1)·p.coeff (i+1)`.
example (u : F) (p : F[X]) (i : ℕ) :
    (logDerivPoly u p).coeff i
      = (p.coeff i)′ + logDeriv u * ((i + 1) * p.coeff (i + 1)) :=
  coeff_logDerivPoly u p i
-- `logDeriv` of a monic `t`-polynomial is proper (the pole-matching engine): `deg (D p) < deg p`.
example (u : F) {p : F[X]} (hm : p.Monic) (hdeg : 1 ≤ p.natDegree) :
    (logDerivPoly u p).natDegree < p.natDegree :=
  natDegree_logDerivPoly_lt_of_monic u hm hdeg
-- Pole order drops by at most one: `q^n ∣ p ⟹ q^(n-1) ∣ D p` (pure Leibniz, any derivation).
example (u : F) {p q : F[X]} {n : ℕ} (hdvd : q ^ n ∣ p) :
    q ^ (n - 1) ∣ logDerivPoly u p :=
  pow_sub_one_dvd_logDerivPoly u hdvd
-- A monic irreducible-degree factor does not divide its own derivative (strict pole increase),
-- provided `D q ≠ 0` (the transcendence input).
example (u : F) {q : F[X]} (hm : q.Monic) (hdeg : 1 ≤ q.natDegree)
    (hDq : logDerivPoly u q ≠ 0) : ¬ q ∣ logDerivPoly u q :=
  not_dvd_logDerivPoly_of_natDegree_lt u hm hdeg hDq
-- A `t`-constant has an `F`-constant `t`-leading coefficient.
example (u : F) {p : F[X]} (h : logDerivPoly u p = 0) : (p.leadingCoeff)′ = 0 :=
  leadingCoeff_deriv_eq_zero_of_logDerivPoly_eq_zero u h

/-! ### The `v ∈ F` polynomial descent engine (Obligation 3, the `v`-term reduction)

The half of Rosenlicht's reduction that handles the integral part: in `a = ∑ cᵢ logDeriv wᵢ + v′`
the term `v` (after the `wᵢ`-poles cancel) has `v′ ∈ F`, and must itself be reduced to `F`.  On the
polynomial layer this is "if `D p` has `t`-degree `0` then `p` has `t`-degree `≤ 1`, and the linear
`t`-coefficient is an obstruction solvable only by `t` being algebraic".  The fully-provable core is
the leading-coefficient/degree descent; the irreducible residue is the same transcendence input as
`NoDegreeDropObligation` (no `F`-antiderivative of `b·logDeriv u`). -/

/-- **`D p` constant ⟹ `t`-leading coefficient of `p` is an `F`-constant.**  If `(D p).natDegree = 0`
(the `t`-derivative is a constant polynomial) and `p` has positive `t`-degree, then `(leadingCoeff
p)′ = 0`: at the top `t`-degree `D p` sees only `F`'s derivation (`coeff_natDegree_logDerivPoly`),
and that coefficient of a degree-`0` polynomial vanishes.  Fully provable — no transcendence input. -/
lemma leadingCoeff_deriv_eq_zero_of_natDegree_logDerivPoly_le (u : F) {p : F[X]}
    (h : (logDerivPoly u p).natDegree = 0) (hdeg : 1 ≤ p.natDegree) :
    (p.leadingCoeff)′ = 0 := by
  have htop := coeff_natDegree_logDerivPoly u p
  rw [← htop]
  exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (le_of_eq h) hdeg)

/-- **`D p` constant ⟹ the coefficient just below the top is an `F`-antiderivative obstruction.**
If `(D p).natDegree = 0` and `n := p.natDegree ≥ 2`, the coefficient-`(n−1)` relation gives
`(p.coeff (n−1))′ = − n · (leadingCoeff p) · logDeriv u`.  Hence `n · (leadingCoeff p) · logDeriv u`
*is* a derivative of an `F`-element — exactly the transcendence obstruction (`log u ∉ F`) for the
`t`-degree to be forced down.  Fully provable as the identity; the *consequence* (degree drop) needs
the no-`F`-antiderivative input.  (Needs `n ≥ 2` so the index `n − 1 ≥ 1` and `(D p).coeff (n−1) = 0`;
the `n = 1` case is the residual linear-term `(b·t)′ = b·u'/u` obstruction.) -/
lemma deriv_coeff_predTop_of_natDegree_logDerivPoly_le (u : F) {p : F[X]}
    (h : (logDerivPoly u p).natDegree = 0) (hdeg : 2 ≤ p.natDegree) :
    (p.coeff (p.natDegree - 1))′
      = - ((p.natDegree : F) * (p.leadingCoeff * logDeriv u)) := by
  have hcoeff := coeff_logDerivPoly u p (p.natDegree - 1)
  have hlt : 0 < p.natDegree - 1 := by omega
  have hzero : (logDerivPoly u p).coeff (p.natDegree - 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (le_of_eq h) hlt)
  rw [hzero] at hcoeff
  have hsucc : p.natDegree - 1 + 1 = p.natDegree := by omega
  rw [hsucc] at hcoeff
  have hlc : p.coeff p.natDegree = p.leadingCoeff := rfl
  rw [hlc] at hcoeff
  have hcast : ((p.natDegree - 1 : ℕ) : F) + 1 = (p.natDegree : F) := by
    rw [Nat.cast_sub (by omega : 1 ≤ p.natDegree), Nat.cast_one]; ring
  rw [hcast] at hcoeff
  linear_combination -hcoeff

/-- **The polynomial `v ∈ F` obligation** — the precise transcendence residue for the `v`-term
reduction.  It records exactly: when `t = log u` is a genuine new transcendental (`logDeriv u ≠ 0`),
a `t`-polynomial `p` whose `t`-derivative `D p` is a *constant* (`(D p).natDegree = 0`) has
`t`-degree `≤ 1`.  (For `natDegree p ≥ 2` the `n·lc·logDeriv u` term of
`deriv_coeff_predTop_of_natDegree_logDerivPoly_le` would have an `F`-antiderivative — impossible for a
genuine log.  For `natDegree p = 1` the linear `t`-coefficient `b·t` survives with `(b·t)′ = b·u'/u`,
the same obstruction.)  This is the `v`-analogue of `NoDegreeDropObligation`. -/
def PolyVReductionObligation (u : F) : Prop :=
  logDeriv u ≠ 0 →
    ∀ {p : F[X]}, (logDerivPoly u p).natDegree = 0 → p.natDegree = 0

/-- **GIVEN the transcendence input, `D p` constant ⟹ `p` is an `F`-constant `C b`.**  The full
polynomial layer of the `v ∈ F` reduction: a `t`-polynomial with constant `t`-derivative is a single
`C b` (with `b′` the value of `D p`).  Reduces the `v`-term polynomial step to `PolyVReductionObligation`
(the no-`F`-antiderivative input), everything else discharged here.  (When `natDegree p = 0` directly,
`p = C (p.coeff 0)`.) -/
lemma eq_C_of_natDegree_logDerivPoly_le (u : F) (hpv : PolyVReductionObligation u)
    (hu : logDeriv u ≠ 0) {p : F[X]} (h : (logDerivPoly u p).natDegree = 0) :
    ∃ b : F, p = C b :=
  ⟨p.coeff 0, Polynomial.eq_C_of_natDegree_eq_zero (hpv hu h)⟩

end PolynomialSetup

/-! ## Obligation 1 CLOSED — the derivation extends to the fraction field `F(t) = RatFunc F`

The missing "a `Derivation A A` on a domain extends to `Derivation (FractionRing A) (FractionRing A)`
by the quotient rule" — built here from scratch (Mathlib has only the Kähler-module-valued
localization, no self-derivation extension to a fraction field).  This discharges the derivation half
of the keystone setup: composed with `logDerivPoly u` it yields the genuine `Differential (RatFunc F)`
with `t' = u'/u`, and `differentialAlgebra_of_derivExtends` then makes `RatFunc F` a real
`DifferentialAlgebra F (RatFunc F)` — the **setup fully closes**.  (Mathlib-contributable as
`Derivation.fractionRing` / a `Differential (FractionRing A)` instance.) -/

section FractionFieldDeriv

open IsLocalization
open scoped nonZeroDivisors

-- Generic over an *opaque* fraction field `K` of `F[X]` (avoids the `RatFunc`-specific
-- `Algebra ℤ (RatFunc F)` instance diamond against `Ring.toIntAlgebra`).  Specialized to
-- `K = RatFunc F` at the end.
variable {F : Type*} [Field F] {K : Type*} [Field K] [Algebra F[X] K] [IsFractionRing F[X] K]

/-- The raw quotient-rule value on a numerator/denominator pair: `(q·d p − p·d q)/q²`. -/
noncomputable def rawDeriv (d : Derivation ℤ F[X] F[X]) (p : F[X]) (q : F[X]⁰) : K :=
  mk' K ((q : F[X]) * d p - p * d q) (q * q)

/-- Well-definedness: equal fractions give equal quotient-rule value.  Crux — the polynomial cross
identity `p₁·q₂ = p₂·q₁`, differentiated by `d`, closes the target by `linear_combination`. -/
theorem rawDeriv_well_defined (d : Derivation ℤ F[X] F[X]) (p₁ p₂ : F[X]) (q₁ q₂ : F[X]⁰)
    (h : mk' K p₁ q₁ = mk' K p₂ q₂) :
    rawDeriv (K := K) d p₁ q₁ = rawDeriv (K := K) d p₂ q₂ := by
  rw [IsLocalization.mk'_eq_iff_eq'] at h
  have hinj : Function.Injective (algebraMap F[X] K) := IsFractionRing.injective F[X] K
  have hcross : p₁ * (q₂ : F[X]) = p₂ * (q₁ : F[X]) := hinj h
  have hd : p₁ * d q₂ + (q₂ : F[X]) * d p₁ = p₂ * d q₁ + (q₁ : F[X]) * d p₂ := by
    have := congrArg d hcross
    simpa only [Derivation.leibniz, smul_eq_mul] using this
  rw [rawDeriv, rawDeriv, IsLocalization.mk'_eq_iff_eq']
  apply congrArg
  push_cast
  linear_combination
    (-((q₁ : F[X]) * d q₂ + (q₂ : F[X]) * d q₁)) * hcross + ((q₁ : F[X]) * q₂) * hd

/-- The extended derivation's underlying function on `K`, via a canonical representative. -/
noncomputable def fracDerivFun (d : Derivation ℤ F[X] F[X]) (x : K) : K :=
  rawDeriv d (IsLocalization.sec F[X]⁰ x).1 (IsLocalization.sec F[X]⁰ x).2

/-- `fracDerivFun` computes by the raw quotient rule on *any* representative. -/
theorem fracDerivFun_mk' (d : Derivation ℤ F[X] F[X]) (p : F[X]) (q : F[X]⁰) :
    fracDerivFun (K := K) d (mk' K p q) = rawDeriv d p q := by
  apply rawDeriv_well_defined
  rw [IsLocalization.mk'_sec]

/-- Additivity of the raw quotient rule (over a common denominator). -/
theorem rawDeriv_add (d : Derivation ℤ F[X] F[X]) (p₁ p₂ : F[X]) (q₁ q₂ : F[X]⁰) :
    rawDeriv (K := K) d (p₁ * q₂ + p₂ * q₁) (q₁ * q₂)
      = rawDeriv d p₁ q₁ + rawDeriv d p₂ q₂ := by
  rw [rawDeriv, rawDeriv, rawDeriv, ← IsLocalization.mk'_add, IsLocalization.mk'_eq_iff_eq']
  apply congrArg
  push_cast
  simp only [map_add, Derivation.leibniz, smul_eq_mul]
  ring

/-- Leibniz product rule for the raw quotient rule. -/
theorem rawDeriv_mul (d : Derivation ℤ F[X] F[X]) (p₁ p₂ : F[X]) (q₁ q₂ : F[X]⁰) :
    rawDeriv (K := K) d (p₁ * p₂) (q₁ * q₂)
      = mk' K p₁ q₁ * rawDeriv d p₂ q₂ + mk' K p₂ q₂ * rawDeriv d p₁ q₁ := by
  rw [rawDeriv, rawDeriv, rawDeriv, ← IsLocalization.mk'_mul, ← IsLocalization.mk'_mul,
    ← IsLocalization.mk'_add, IsLocalization.mk'_eq_iff_eq']
  apply congrArg
  push_cast
  simp only [Derivation.leibniz, smul_eq_mul]
  ring

/-- `fracDerivFun` sends `0` to `0`. -/
theorem fracDerivFun_zero (d : Derivation ℤ F[X] F[X]) : fracDerivFun (K := K) d 0 = 0 := by
  have h0 : (0 : K) = mk' K 0 (1 : F[X]⁰) := by simp only [IsLocalization.mk'_zero]
  rw [h0, fracDerivFun_mk', rawDeriv, IsLocalization.mk'_eq_iff_eq']
  apply congrArg
  simp

/-- `fracDerivFun` is additive. -/
theorem fracDerivFun_add (d : Derivation ℤ F[X] F[X]) (x y : K) :
    fracDerivFun d (x + y) = fracDerivFun d x + fracDerivFun d y := by
  obtain ⟨⟨p₁, q₁⟩, rfl⟩ := IsLocalization.mk'_surjective F[X]⁰ x
  obtain ⟨⟨p₂, q₂⟩, rfl⟩ := IsLocalization.mk'_surjective F[X]⁰ y
  rw [← IsLocalization.mk'_add, fracDerivFun_mk', fracDerivFun_mk', fracDerivFun_mk', rawDeriv_add]

/-- `fracDerivFun` satisfies the Leibniz product rule. -/
theorem fracDerivFun_mul (d : Derivation ℤ F[X] F[X]) (x y : K) :
    fracDerivFun d (x * y) = x * fracDerivFun d y + y * fracDerivFun d x := by
  obtain ⟨⟨p₁, q₁⟩, rfl⟩ := IsLocalization.mk'_surjective F[X]⁰ x
  obtain ⟨⟨p₂, q₂⟩, rfl⟩ := IsLocalization.mk'_surjective F[X]⁰ y
  rw [← IsLocalization.mk'_mul, fracDerivFun_mk', fracDerivFun_mk', fracDerivFun_mk', rawDeriv_mul]

/-- `fracDerivFun` as an additive homomorphism (its `toIntLinearMap` is the ℤ-linear map). -/
noncomputable def fracDerivHom (d : Derivation ℤ F[X] F[X]) : K →+ K where
  toFun := fracDerivFun d
  map_zero' := fracDerivFun_zero d
  map_add' := fracDerivFun_add d

/-- **Obligation 1, CLOSED.**  A derivation `d` on `F[X]` extended to a fraction field `K` by the
quotient rule, as a self-derivation `Derivation ℤ K K`. -/
noncomputable def fracDeriv (d : Derivation ℤ F[X] F[X]) : Derivation ℤ K K :=
  Derivation.mk' (fracDerivHom d).toIntLinearMap (fun a b => by
    have := fracDerivFun_mul (K := K) d a b
    simpa only [AddMonoidHom.coe_toIntLinearMap, fracDerivHom, AddMonoidHom.coe_mk,
      ZeroHom.coe_mk, smul_eq_mul] using this)

@[simp]
lemma fracDeriv_mk' (d : Derivation ℤ F[X] F[X]) (p : F[X]) (q : F[X]⁰) :
    fracDeriv (K := K) d (mk' K p q) = rawDeriv d p q := fracDerivFun_mk' d p q

/-- **`fracDeriv` restricts to `d` on the image of `F[X]`** (the defining property of Obligation 1):
`fracDeriv d (algebraMap F[X] K p) = algebraMap F[X] K (d p)`. -/
theorem fracDeriv_algebraMap (d : Derivation ℤ F[X] F[X]) (p : F[X]) :
    fracDeriv (K := K) d (algebraMap F[X] K p) = algebraMap F[X] K (d p) := by
  have h1 : (algebraMap F[X] K p) = mk' K p (1 : F[X]⁰) := by rw [IsLocalization.mk'_one]
  rw [h1, fracDeriv_mk', rawDeriv]
  have hnum : ((1 : F[X]⁰) : F[X]) * d p - p * d (1 : F[X]⁰) = d p := by
    rw [show ((1 : F[X]⁰) : F[X]) = 1 from rfl, one_mul, Derivation.map_one_eq_zero,
      mul_zero, sub_zero]
  have hden : ((1 : F[X]⁰) * (1 : F[X]⁰) : F[X]⁰) = (1 : F[X]⁰) := by simp
  rw [hnum, hden, IsLocalization.mk'_one]

/-- The fraction-field extension `Differential K` from a `Differential F[X]`. -/
@[reducible]
noncomputable def fracDifferential (h : Differential F[X]) : Differential K :=
  letI := h
  ⟨fracDeriv h.deriv⟩

end FractionFieldDeriv

/-! ## The genuine field extension `F(t) = RatFunc F` (setup CLOSED; one obligation left)

The `IsLiouville` instance and `trans`-towering require the carrier to be a **field**, so the
target is `RatFunc F`, the fraction field of `F[t]`.  Mathlib supplies `Field`, `Algebra F (RatFunc
F)`, `CharZero (RatFunc F)`, `IsFractionRing F[t] (RatFunc F)` — and now, via `fracDeriv` above, the
**derivation too**.  So `logDifferential u` / `logDifferentialAlgebra u` make this a *real*
differential field extension (Obligations 1, 2 CLOSED).  What remains (`IsLiouvilleReductionObligation`)
is exactly the Rosenlicht `IsLiouville` reduction. -/

section FieldObligations

variable {F : Type*} [Field F] [Differential F] [CharZero F]

open RatFunc

/-- The genuine `Differential (RatFunc F)` for the log monomial `t = log u` (`t' = u'/u`), via the
fraction-field extension `fracDeriv` of `logDerivPoly u`. -/
@[reducible]
noncomputable def logDifferential (u : F) : Differential (RatFunc F) :=
  fracDifferential (K := RatFunc F) (logDifferentialPoly u)

omit [CharZero F] in
/-- **Obligation 1, CLOSED.**  The log-monomial derivation on `RatFunc F` (`logDifferential u`)
restricts to `logDerivPoly u` on the image of `F[t]`:
`(algebraMap F[t] (RatFunc F) p)′ = algebraMap F[t] (RatFunc F) (logDerivPoly u p)`. -/
theorem derivExtends (u : F) :
    letI := logDifferential u
    ∀ p : F[X], (algebraMap F[X] (RatFunc F) p)′
      = algebraMap F[X] (RatFunc F) (logDerivPoly u p) :=
  fun p => fracDeriv_algebraMap (K := RatFunc F) (logDerivPoly u) p

omit [CharZero F] in
/-- **Obligation 2 is DISCHARGED conditionally.**  GIVEN any `Differential (RatFunc F)` whose
derivation restricts to `logDerivPoly u` on `F[t]` (the content of Obligation 1), the extension is a
`DifferentialAlgebra F (RatFunc F)`: it commutes with `algebraMap F (RatFunc F)`.  Proof: factor
`algebraMap F (RatFunc F) = (algebraMap F[t] (RatFunc F)) ∘ C` through the scalar tower, then use the
restriction property at `C a` together with `logDerivPoly_C` (`D (C a) = C a'`).  So Obligation 2
needs **no** new mathematics beyond Obligation 1. -/
theorem differentialAlgebra_of_derivExtends [Differential (RatFunc F)] {u : F}
    (h : ∀ p : F[X], (algebraMap F[X] (RatFunc F) p)′
      = algebraMap F[X] (RatFunc F) (logDerivPoly u p)) :
    DifferentialAlgebra F (RatFunc F) where
  deriv_algebraMap a := by
    have hfac : (algebraMap F (RatFunc F)) a
        = algebraMap F[X] (RatFunc F) (C a) := by
      rw [IsScalarTower.algebraMap_eq F F[X] (RatFunc F)]
      simp [Polynomial.algebraMap_eq]
    rw [hfac, h (C a), logDerivPoly_C]
    rw [IsScalarTower.algebraMap_eq F F[X] (RatFunc F)]
    simp [Polynomial.algebraMap_eq]

omit [CharZero F] in
/-- **Obligation 2, CLOSED.**  `RatFunc F` with the log-monomial derivation is a genuine
`DifferentialAlgebra F (RatFunc F)` — the **setup is now a real differential field extension**, not
conditional. -/
theorem logDifferentialAlgebra (u : F) :
    letI := logDifferential u
    DifferentialAlgebra F (RatFunc F) :=
  letI := logDifferential u
  differentialAlgebra_of_derivExtends (u := u) (derivExtends u)

omit [CharZero F] in
/-- **The `logDeriv`-to-polynomial bridge** (the entry point for Obligation 3): in `RatFunc F`, the
logarithmic derivative of `algebraMap p` is `algebraMap (D p) / algebraMap p`, with `D p` the
proven polynomial engine `logDerivPoly u p`.  This is how the `IsLiouville` statement's `logDeriv
wᵢ` connects to the `t`-pole engine. -/
theorem logDeriv_algebraMap_eq (u : F) (p : F[X]) :
    letI := logDifferential u
    logDeriv (algebraMap F[X] (RatFunc F) p)
      = algebraMap F[X] (RatFunc F) (logDerivPoly u p) / algebraMap F[X] (RatFunc F) p := by
  letI := logDifferential u
  unfold logDeriv
  rw [derivExtends u p]

omit [CharZero F] in
/-- **A monic `t`-factor contributes a genuine `t`-pole to its `logDeriv`** (the pole-matching
mechanism, lifted to `RatFunc F`): for monic `p` of `t`-degree `≥ 1`, `logDeriv (algebraMap p) =
algebraMap (D p) / algebraMap p` is a *proper* fraction in `t` — `D p` has strictly smaller
`t`-degree than `p` (`natDegree_logDerivPoly_lt_of_monic`).  Since `a ∈ F` carries **no** `t`-pole,
in `a = ∑ cᵢ logDeriv wᵢ + v′` these poles must cancel among the `wᵢ` — the crux of Obligation 3. -/
theorem logDeriv_monic_proper (u : F) {p : F[X]} (hm : p.Monic) (hdeg : 1 ≤ p.natDegree) :
    letI := logDifferential u
    logDeriv (algebraMap F[X] (RatFunc F) p)
        = algebraMap F[X] (RatFunc F) (logDerivPoly u p) / algebraMap F[X] (RatFunc F) p ∧
      (logDerivPoly u p).natDegree < p.natDegree :=
  letI := logDifferential u
  ⟨logDeriv_algebraMap_eq u p, natDegree_logDerivPoly_lt_of_monic u hm hdeg⟩

/-! ### The `v ∈ F` reduction lifted to `RatFunc F` (Obligation 3, the `v`-term)

Lifting the polynomial `v ∈ F` descent (`eq_C_of_natDegree_logDerivPoly_le`) to the fraction field.
The bridge: `algebraMap F (RatFunc F)` factors through `F[t]` (scalar tower), so an `F`-membership
question becomes a `C`-image (degree-`0`) question on the polynomial preimage.  The remaining genuine
content is the *rational-to-polynomial* step (a rational function whose derivative is a polynomial is
itself a polynomial — the partial-fraction "no `t`-pole survives in the derivative" fact), isolated
as `RationalToPolyObligation`. -/

omit [Differential F] [CharZero F] in
/-- **`algebraMap F` factors through `F[t]` as `C`.**  `algebraMap F (RatFunc F) b = algebraMap F[t]
(RatFunc F) (C b)` (the scalar tower `F → F[t] → RatFunc F`). -/
theorem algebraMap_eq_algebraMap_C (b : F) :
    algebraMap F (RatFunc F) b = algebraMap F[X] (RatFunc F) (Polynomial.C b) := by
  rw [IsScalarTower.algebraMap_eq F F[X] (RatFunc F)]
  simp [Polynomial.algebraMap_eq]

omit [Differential F] [CharZero F] in
/-- **`F`-membership of a `t`-polynomial image is degree-`0`.**  `algebraMap F[t] (RatFunc F) p ∈
range (algebraMap F (RatFunc F))` iff `p ∈ range C`, i.e. `p = C b` for some `b ∈ F`.  Forward by
`algebraMap`-injectivity (`F[t] ↪ RatFunc F`); backward by `algebraMap_eq_algebraMap_C`. -/
theorem algebraMap_poly_mem_range_iff (p : F[X]) :
    algebraMap F[X] (RatFunc F) p ∈ (algebraMap F (RatFunc F)).range
      ↔ ∃ b : F, p = Polynomial.C b := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    apply FaithfulSMul.algebraMap_injective F[X] (RatFunc F)
    rw [← algebraMap_eq_algebraMap_C, hb]
  · rintro ⟨b, rfl⟩
    exact ⟨b, (algebraMap_eq_algebraMap_C b).symm⟩

/-- **The rational-to-polynomial obligation** — the partial-fraction "no `t`-pole" content of the
`v`-term reduction, sharply isolated.  It says: a rational function `v ∈ RatFunc F` whose
log-monomial derivative `v′` is a *polynomial* (`v′ ∈ range (algebraMap F[t])`) is itself a
*polynomial* (`v ∈ range (algebraMap F[t])`).  This is the genuine pole-order fact — a `t`-pole of
order `k ≥ 1` in `v` produces a pole of order `≥ k+1` in `v′`, so `v′` polynomial forces `v` pole-free
— and is the residual partial-fraction frontier of the `v`-term descent.  (Carries `logDeriv u ≠ 0`:
the genuine-log hypothesis, kept uniform with the other obligations.) -/
def RationalToPolyObligation (u : F) : Prop :=
  letI := logDifferential u
  logDeriv u ≠ 0 →
    ∀ v : RatFunc F, v′ ∈ (algebraMap F[X] (RatFunc F)).range →
      v ∈ (algebraMap F[X] (RatFunc F)).range

/-- **`RationalToPolyObligation` DISCHARGED from `NondegenerateLog`** — the rational-to-polynomial
pole-order descent, proved.  For `v ∈ RatFunc F` with `v′` a polynomial: write `v = ↑n/↑d`
(`n = num v`, `d = denom v` monic, `IsCoprime n d`).  Clearing the denominator and differentiating
`↑d · v = ↑n` (Leibniz, `derivExtends`: `D ↑p = ↑(D p)`) gives `↑n · ↑(D d) = ↑(d·(D n) − d·P)` once
`v′ = ↑P`; by `algebraMap`-injectivity `n · D d = d · (D n − d·P)`, so **`d ∣ n · (D d)`**.  Since
`IsCoprime n d`, `d ∣ D d`.  If `deg d ≥ 1` this contradicts `not_dvd_logDerivPoly_of_monic` (the
strict pole increase from `NondegenerateLog`), so `deg d = 0`, `d = 1`, and `v = ↑n` is a polynomial.
This is the precise "a `t`-pole survives differentiation" content, now resting only on the
non-degeneracy of the log. -/
theorem rationalToPolyObligation_of_nondegenerateLog (u : F) (hnd : NondegenerateLog u) :
    RationalToPolyObligation u := by
  letI := logDifferential u
  intro _hu v hvpoly
  -- `v = 0` is a polynomial trivially.
  rcases eq_or_ne v 0 with rfl | hv0
  · exact ⟨0, by rw [map_zero]⟩
  obtain ⟨P, hP⟩ := hvpoly
  set n := RatFunc.num v with hndef
  set d := RatFunc.denom v with hddef
  have hdmon : d.Monic := RatFunc.monic_denom v
  have hdne0 : d ≠ 0 := RatFunc.denom_ne_zero v
  have hnne0 : n ≠ 0 := RatFunc.num_ne_zero hv0
  have hcop : IsCoprime n d := RatFunc.isCoprime_num_denom v
  have hnA : algebraMap F[X] (RatFunc F) n ≠ 0 := RatFunc.algebraMap_ne_zero hnne0
  have hdA : algebraMap F[X] (RatFunc F) d ≠ 0 := RatFunc.algebraMap_ne_zero hdne0
  -- `v = ↑n/↑d`, and `logDeriv v = ↑(D n)/↑n − ↑(D d)/↑d` (split + `logDeriv_algebraMap_eq`).
  have hveq : v = algebraMap F[X] (RatFunc F) n / algebraMap F[X] (RatFunc F) d := by
    rw [← RatFunc.num_div_denom v, ← hndef, ← hddef]
  have hlogv : logDeriv v
      = algebraMap F[X] (RatFunc F) (logDerivPoly u n) / algebraMap F[X] (RatFunc F) n
        - algebraMap F[X] (RatFunc F) (logDerivPoly u d) / algebraMap F[X] (RatFunc F) d := by
    have hsplit : logDeriv v = logDeriv (algebraMap F[X] (RatFunc F) n)
        - logDeriv (algebraMap F[X] (RatFunc F) d) := by
      conv_lhs => rw [hveq]
      exact logDeriv_div _ _ hnA hdA
    rw [hsplit, logDeriv_algebraMap_eq u n, logDeriv_algebraMap_eq u d]
  -- `v′ = v · logDeriv v` (definition), so `↑P = (↑n/↑d)·(↑(Dn)/↑n − ↑(Dd)/↑d)`.
  have hv'eq : v′ = v * logDeriv v := by
    rw [logDeriv, mul_div_cancel₀ _ hv0]
  -- Clear denominators to a polynomial identity `P·d² = d·(Dn) − n·(Dd)`.
  have hkey : algebraMap F[X] (RatFunc F) (P * (d * d))
      = algebraMap F[X] (RatFunc F) (d * logDerivPoly u n - n * logDerivPoly u d) := by
    have hPv : algebraMap F[X] (RatFunc F) P = v * logDeriv v := by rw [hP, hv'eq]
    rw [hlogv, hveq] at hPv
    rw [map_mul, map_mul, map_sub, map_mul, map_mul]
    field_simp at hPv ⊢
    linear_combination hPv
  have hkeyP : P * (d * d) = d * logDerivPoly u n - n * logDerivPoly u d :=
    FaithfulSMul.algebraMap_injective F[X] (RatFunc F) hkey
  -- `d ∣ n·(D d)`, so by coprimality `d ∣ D d`.
  have hdvd_nDd : d ∣ n * logDerivPoly u d := by
    have hrw : n * logDerivPoly u d = d * logDerivPoly u n - P * (d * d) := by
      linear_combination hkeyP
    rw [hrw]
    exact Dvd.dvd.sub (dvd_mul_right d _) (dvd_mul_of_dvd_right (dvd_mul_right d d) P)
  have hdvd_Dd : d ∣ logDerivPoly u d := hcop.symm.dvd_of_dvd_mul_left hdvd_nDd
  -- If `deg d ≥ 1` this contradicts the strict pole increase; so `deg d = 0`, `d = 1`, `v = ↑n`.
  have hdeg0 : d.natDegree = 0 := by
    by_contra hdeg
    exact not_dvd_logDerivPoly_of_monic u hnd hdmon (Nat.one_le_iff_ne_zero.mpr hdeg) hdvd_Dd
  have hd1 : d = 1 := eq_one_of_monic_natDegree_zero hdmon hdeg0
  refine ⟨n, ?_⟩
  rw [hveq, hd1, map_one, div_one]

/-- **The CORRECTED `v`-reduction: `v′ ∈ F ⟹ v = v₀ + b·t` (`v₀, b ∈ F`, `b` constant), given
`NondegenerateLog`.**  Replaces the *false* `mem_range_of_deriv_mem_range` (`v′ ∈ F ⟹ v ∈ F`, refuted by
`v = log u`).  The correct conclusion is `v ∈ F ⊕ Const·t`: the surviving linear term `b·t = b·log u` is
a **new logarithm**, not an `F`-element.  Proof: `v′ ∈ F ⊆ F[t]`, so by the proved pole descent
(`rationalToPolyObligation_of_nondegenerateLog`) `v = ↑p`; then `D p` is a constant
(`(D p).natDegree = 0`), so `p.natDegree ≤ 1` (`natDegree_le_one_of_logDerivPoly_natDegree_eq_zero`),
giving `p = C (p.coeff 0) + C (p.coeff 1)·X`; the index-`1` coefficient relation forces `(p.coeff 1)′ =
0` (the linear coefficient is a constant of `F`).  So `v = ↑(p.coeff 0) + ↑(p.coeff 1)·t` with
`(p.coeff 1)′ = 0`. -/
theorem deriv_mem_range_imp_linear (u : F) (hnd : NondegenerateLog u) {v : RatFunc F}
    (hv : letI := logDifferential u; v′ ∈ (algebraMap F (RatFunc F)).range) :
    letI := logDifferential u
    ∃ (v₀ b : F), b′ = 0 ∧
      v = algebraMap F (RatFunc F) v₀
        + algebraMap F (RatFunc F) b * algebraMap F[X] (RatFunc F) X := by
  letI := logDifferential u
  -- `v′ ∈ F ⊆ F[t]`, so by the pole descent `v = ↑p`.
  obtain ⟨b, hb⟩ := hv
  have hvpoly : v′ ∈ (algebraMap F[X] (RatFunc F)).range := by
    refine ⟨Polynomial.C b, ?_⟩
    rw [← algebraMap_eq_algebraMap_C, hb]
  obtain ⟨p, hp⟩ := rationalToPolyObligation_of_nondegenerateLog u hnd
    (logDeriv_ne_zero_of_nondegenerateLog u hnd) v hvpoly
  -- `D p` is the constant `C b`, so `(D p).natDegree = 0` and `p.natDegree ≤ 1`.
  have hDpCb : logDerivPoly u p = Polynomial.C b :=
    FaithfulSMul.algebraMap_injective F[X] (RatFunc F) (by
      rw [← derivExtends u p, hp, ← hb, algebraMap_eq_algebraMap_C])
  have hdeg0 : (logDerivPoly u p).natDegree = 0 := by rw [hDpCb]; exact natDegree_C b
  have hple1 : p.natDegree ≤ 1 := natDegree_le_one_of_logDerivPoly_natDegree_eq_zero u hnd hdeg0
  -- The linear coefficient is a constant: `(p.coeff 1)′ = 0` (index-`1` coefficient relation).
  have hb1 : (p.coeff 1)′ = 0 := by
    have hcoeff := coeff_logDerivPoly u p 1
    rw [hDpCb] at hcoeff
    have hc2 : p.coeff 2 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    rw [Polynomial.coeff_C] at hcoeff
    simp only [show (1 : ℕ) ≠ 0 by decide, if_false] at hcoeff
    rw [hc2] at hcoeff
    simpa using hcoeff.symm
  -- `p = C (p.coeff 1)·X + C (p.coeff 0)` (degree `≤ 1`), so `v = ↑(p.coeff 0) + ↑(p.coeff 1)·t`.
  refine ⟨p.coeff 0, p.coeff 1, hb1, ?_⟩
  conv_lhs => rw [← hp, Polynomial.eq_X_add_C_of_natDegree_le_one hple1, map_add, map_mul,
    ← algebraMap_eq_algebraMap_C, ← algebraMap_eq_algebraMap_C]
  rw [add_comm]

omit [CharZero F] in
/-- **The `v ∈ F` reduction on `RatFunc F`, modulo the two residues.**  GIVEN the rational-to-poly
input (`RationalToPolyObligation`, the partial-fraction "no pole") and the polynomial descent input
(`PolyVReductionObligation`, the transcendence "no `F`-antiderivative"), a `v ∈ RatFunc F` whose
derivative `v′` lies in `F` (`v′ = algebraMap F b`) lies in `F` itself.  All the fraction-field glue
— pulling `v′ ∈ F` back to a polynomial preimage `v = algebraMap p`, identifying `logDerivPoly u p =
C b`, and descending `p` to `C b₀` — is discharged here; only the two stated residues remain.  This
is the full `v`-term reduction modulo its two sharply-isolated frontiers. -/
theorem mem_range_of_deriv_mem_range (u : F) (hrtp : RationalToPolyObligation u)
    (hpv : PolyVReductionObligation u) (hu : logDeriv u ≠ 0) :
    letI := logDifferential u
    ∀ {v : RatFunc F}, v′ ∈ (algebraMap F (RatFunc F)).range →
      v ∈ (algebraMap F (RatFunc F)).range := by
  letI := logDifferential u
  intro v hv
  -- `v′ ∈ F ⊆ F[t]`, so by the partial-fraction obligation `v` is a polynomial image.
  obtain ⟨b, hb⟩ := hv
  have hvpoly : v′ ∈ (algebraMap F[X] (RatFunc F)).range := by
    refine ⟨Polynomial.C b, ?_⟩
    rw [← algebraMap_eq_algebraMap_C, hb]
  obtain ⟨p, hp⟩ := hrtp hu v hvpoly
  -- Identify `D p = C b` via injectivity, hence `(D p).natDegree = 0`.
  have hderiv : algebraMap F[X] (RatFunc F) (logDerivPoly u p)
      = algebraMap F[X] (RatFunc F) (Polynomial.C b) := by
    rw [← derivExtends u p, hp, ← hb, algebraMap_eq_algebraMap_C]
  have hDpCb : logDerivPoly u p = Polynomial.C b :=
    FaithfulSMul.algebraMap_injective F[X] (RatFunc F) hderiv
  have hdeg0 : (logDerivPoly u p).natDegree = 0 := by rw [hDpCb]; exact natDegree_C b
  -- Descend `p` to a constant `C b₀` by the polynomial obligation; conclude `v ∈ F`.
  obtain ⟨b₀, hb₀⟩ := eq_C_of_natDegree_logDerivPoly_le u hpv hu hdeg0
  rw [← hp]
  exact (algebraMap_poly_mem_range_iff p).mpr ⟨b₀, hb₀⟩

/-! ### The single-logarithm case (Obligation 3, `ι` a singleton)

`a = c · logDeriv w + v′` with `a ∈ F`.  The structural decomposition `logDeriv w =
logDeriv(num w) − logDeriv(denom w)` splits the logarithm into its numerator/denominator polynomial
parts; each polynomial's `logDeriv` is a sum of `logDeriv` of monic irreducibles (proper `t`-poles,
`logDeriv_monic_proper`).  Since `a ∈ F` carries no `t`-pole, those simple poles must cancel — the
*pole-independence* fact isolated as `SingleLogPoleObligation`.  The decomposition is fully provable;
the pole-independence is the genuine partial-fraction frontier. -/

omit [CharZero F] in
/-- **`logDeriv` of a `RatFunc` splits as numerator minus denominator `logDeriv`** (the entry to the
single-log pole analysis): for `w ≠ 0`, `logDeriv w = logDeriv(algebraMap (num w)) −
logDeriv(algebraMap (denom w))` in `RatFunc F`, via `w = num w / denom w` and `logDeriv_div`. -/
theorem logDeriv_eq_num_sub_denom (u : F) {w : RatFunc F} (hw : w ≠ 0) :
    letI := logDifferential u
    logDeriv w = logDeriv (algebraMap F[X] (RatFunc F) (RatFunc.num w))
        - logDeriv (algebraMap F[X] (RatFunc F) (RatFunc.denom w)) := by
  letI := logDifferential u
  have hnum : algebraMap F[X] (RatFunc F) (RatFunc.num w) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (RatFunc.num_ne_zero hw)
  have hden : algebraMap F[X] (RatFunc F) (RatFunc.denom w) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero w)
  conv_lhs => rw [← RatFunc.num_div_denom w]
  exact logDeriv_div _ _ hnum hden

omit [CharZero F] in
/-- **`logDeriv` of a polynomial image folds along a factorization** (the single-log decomposition):
if `p = ∏ⱼ (g j)^(e j)` with each `g j ≠ 0` (e.g. a unit-times-monic-irreducibles factorization in
`F[t]`), then `logDeriv (algebraMap p) = ∑ⱼ (e j) · logDeriv (algebraMap (g j))` in `RatFunc F`.
Each factor's `logDeriv` is `logDeriv (algebraMap (g j))`; the monic ones are proper `t`-poles
(`logDeriv_monic_proper`).  Fully provable from `logDeriv_prod`/`logDeriv_pow`. -/
theorem logDeriv_algebraMap_prod_pow (u : F) {ι : Type*} (s : Finset ι) (g : ι → F[X])
    (e : ι → ℕ) (hg : ∀ j ∈ s, g j ≠ 0) :
    letI := logDifferential u
    logDeriv (algebraMap F[X] (RatFunc F) (∏ j ∈ s, (g j) ^ (e j)))
      = ∑ j ∈ s, (e j : RatFunc F) * logDeriv (algebraMap F[X] (RatFunc F) (g j)) := by
  letI := logDifferential u
  have hne : ∀ j ∈ s, algebraMap F[X] (RatFunc F) ((g j) ^ (e j)) ≠ 0 :=
    fun j hj => RatFunc.algebraMap_ne_zero (pow_ne_zero _ (hg j hj))
  rw [map_prod, logDeriv_prod ι s _ hne]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_pow, logDeriv_pow]

omit [CharZero F] in
/-- **`logDeriv` of a polynomial image folds along its UFD factorization** (the multi-term decomposition
engine): for `p ≠ 0` in `F[t]`, `logDeriv (algebraMap p) = logDeriv (algebraMap (C p.leadingCoeff)) +
∑_{π ∈ (normalizedFactors p).toFinset} (count π) · logDeriv (algebraMap π)`, the `π` ranging over the
*distinct monic irreducible* factors of `p` (each weighted by its multiplicity).  The leading-coefficient
term is an `F`-element (`C lc ∈ range C`), and each `logDeriv (algebraMap π)` is a proper `t`-pole
(`logDeriv_monic_proper`).  Proof: `p = C lc · ∏ (normalizedFactors p)` (`leadingCoeff_mul_prod_normalizedFactors`),
then `logDeriv_mul` + `logDeriv_multisetProd` collapse the product, and `Finset.sum_multiset_map_count`
collects equal factors. -/
theorem logDeriv_algebraMap_eq_unit_add_sum [DecidableEq F] (u : F) {p : F[X]} (hp : p ≠ 0) :
    letI := logDifferential u
    logDeriv (algebraMap F[X] (RatFunc F) p)
      = logDeriv (algebraMap F[X] (RatFunc F) (Polynomial.C p.leadingCoeff))
        + ∑ π ∈ (UniqueFactorizationMonoid.normalizedFactors p).toFinset,
            ((UniqueFactorizationMonoid.normalizedFactors p).count π : RatFunc F)
              * logDeriv (algebraMap F[X] (RatFunc F) π) := by
  letI := logDifferential u
  -- Each normalized factor is monic irreducible, in particular nonzero.
  have hfac_ne : ∀ π ∈ UniqueFactorizationMonoid.normalizedFactors p, π ≠ 0 := fun π hπ =>
    UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors hπ
  -- `p = C lc · ∏ (normalizedFactors p)`.
  have hprod : Polynomial.C p.leadingCoeff * (UniqueFactorizationMonoid.normalizedFactors p).prod = p :=
    Polynomial.leadingCoeff_mul_prod_normalizedFactors p
  have hlcne : Polynomial.C p.leadingCoeff ≠ 0 := by
    simpa [Polynomial.C_eq_zero] using Polynomial.leadingCoeff_ne_zero.mpr hp
  have hprodne : (UniqueFactorizationMonoid.normalizedFactors p).prod ≠ 0 := by
    intro h0
    apply hp
    rw [← hprod, h0, mul_zero]
  -- Map the factorization to `RatFunc F`, split `logDeriv` of the product.
  have hAlc : algebraMap F[X] (RatFunc F) (Polynomial.C p.leadingCoeff) ≠ 0 :=
    RatFunc.algebraMap_ne_zero hlcne
  have hAprod : algebraMap F[X] (RatFunc F) (UniqueFactorizationMonoid.normalizedFactors p).prod ≠ 0 :=
    RatFunc.algebraMap_ne_zero hprodne
  conv_lhs => rw [← hprod, map_mul, Differential.logDeriv_mul _ _ hAlc hAprod]
  congr 1
  -- `logDeriv (algebraMap ∏factors) = ∑_{multiset} logDeriv (algebraMap π)`, then collect by count.
  rw [map_multiset_prod,
    Differential.logDeriv_multisetProd (UniqueFactorizationMonoid.normalizedFactors p)
      (f := fun π => algebraMap F[X] (RatFunc F) π)
      (fun π hπ => RatFunc.algebraMap_ne_zero (hfac_ne π hπ))]
  rw [Finset.sum_multiset_map_count]
  refine Finset.sum_congr rfl fun π hπ => ?_
  rw [nsmul_eq_mul]

/-- The `F`-unit part of `w ∈ RatFunc F`: `(num w).leadingCoeff / (denom w).leadingCoeff` — the
nonzero `F`-scalar `w` differs from a ratio of *monic* `t`-polynomials by.  Its `logDeriv` is the
`F`-valued part of `logDeriv w` (the `t`-pole-free part). -/
noncomputable def wConst (w : RatFunc F) : F :=
  (RatFunc.num w).leadingCoeff / (RatFunc.denom w).leadingCoeff

/-- The signed `t`-pole multiplicity of a monic irreducible `π` in `w ∈ RatFunc F`, as an `F`-element:
`(count π in factors(num w)) − (count π in factors(denom w))`.  This is the residue that the multi-term
pole-matching collects across the `wᵢ`. -/
noncomputable def poleMult [DecidableEq F] (w : RatFunc F) (π : F[X]) : F :=
  ((UniqueFactorizationMonoid.normalizedFactors (RatFunc.num w)).count π : F)
    - ((UniqueFactorizationMonoid.normalizedFactors (RatFunc.denom w)).count π : F)

/-- The finite set of monic irreducible `t`-factors of `w ∈ RatFunc F` (numerator and denominator):
the support of `poleMult w`. -/
noncomputable def factorsFinset [DecidableEq F] (w : RatFunc F) : Finset F[X] :=
  (UniqueFactorizationMonoid.normalizedFactors (RatFunc.num w)).toFinset ∪
    (UniqueFactorizationMonoid.normalizedFactors (RatFunc.denom w)).toFinset

omit [Differential F] [CharZero F] in
/-- A normalized `t`-factor is monic (`normalize π = π` ⟺ monic over a field). -/
theorem monic_of_mem_normalizedFactors [DecidableEq F] {a π : F[X]}
    (hπ : π ∈ UniqueFactorizationMonoid.normalizedFactors a) : π.Monic := by
  have hne : π ≠ 0 := UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors hπ
  exact (Polynomial.normalize_eq_self_iff_monic hne).mp
    (UniqueFactorizationMonoid.normalize_normalized_factor π hπ)

omit [Differential F] [CharZero F] in
/-- Every element of `factorsFinset w` is a monic irreducible `t`-polynomial. -/
theorem factorsFinset_monic_irreducible [DecidableEq F] {w : RatFunc F} {π : F[X]}
    (hπ : π ∈ factorsFinset w) : π.Monic ∧ Irreducible π := by
  rw [factorsFinset, Finset.mem_union, Multiset.mem_toFinset, Multiset.mem_toFinset] at hπ
  rcases hπ with hπ | hπ <;>
    exact ⟨monic_of_mem_normalizedFactors hπ,
      UniqueFactorizationMonoid.irreducible_of_normalized_factor _ hπ⟩

omit [CharZero F] in
/-- **The `RatFunc` `logDeriv` pole decomposition** (the per-`wᵢ` engine of multi-term pole-matching):
for `w ≠ 0`, `logDeriv w = logDeriv (algebraMap (wConst w)) + ∑_{π ∈ factorsFinset w}
algebraMap (C (poleMult w π)) · logDeriv (algebraMap π)`, the first term `F`-valued (no `t`-pole) and
each numerator `C (poleMult w π)` a *constant* (`t`-degree `0`).  Proof: split `logDeriv w =
logDeriv ↑(num w) − logDeriv ↑(denom w)` (`logDeriv_eq_num_sub_denom`), fold each by
`logDeriv_algebraMap_eq_unit_add_sum`, identify the leading-coefficient parts as
`logDeriv (algebraMap (wConst w))`, cast the `(count)` weights to `C (count)` constants, and merge the
num/denom sums over the union `factorsFinset w` (`Finset.sum_subset`, counts vanish off-support). -/
theorem logDeriv_eq_wConst_add_sum [DecidableEq F] (u : F) {w : RatFunc F} (hw : w ≠ 0) :
    letI := logDifferential u
    logDeriv w = logDeriv (algebraMap F (RatFunc F) (wConst w))
      + ∑ π ∈ factorsFinset w,
          algebraMap F[X] (RatFunc F) (Polynomial.C (poleMult w π))
            * logDeriv (algebraMap F[X] (RatFunc F) π) := by
  letI := logDifferential u
  set n := RatFunc.num w with hn
  set d := RatFunc.denom w with hd
  have hnne : n ≠ 0 := RatFunc.num_ne_zero hw
  have hdne : d ≠ 0 := RatFunc.denom_ne_zero w
  -- Split, then fold numerator and denominator.
  rw [logDeriv_eq_num_sub_denom u hw, ← hn, ← hd,
    logDeriv_algebraMap_eq_unit_add_sum u hnne, logDeriv_algebraMap_eq_unit_add_sum u hdne]
  -- Notation for the two normalized-factor multisets.
  set Mn := UniqueFactorizationMonoid.normalizedFactors n with hMn
  set Md := UniqueFactorizationMonoid.normalizedFactors d with hMd
  have hlcn : n.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hnne
  have hlcd : d.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hdne
  -- The leading-coefficient part is `logDeriv (algebraMap (wConst w))`.
  have hAn : algebraMap F[X] (RatFunc F) (Polynomial.C n.leadingCoeff) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (by simpa [Polynomial.C_eq_zero] using hlcn)
  have hAd : algebraMap F[X] (RatFunc F) (Polynomial.C d.leadingCoeff) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (by simpa [Polynomial.C_eq_zero] using hlcd)
  have hwconst : logDeriv (algebraMap F[X] (RatFunc F) (Polynomial.C n.leadingCoeff))
      - logDeriv (algebraMap F[X] (RatFunc F) (Polynomial.C d.leadingCoeff))
      = logDeriv (algebraMap F (RatFunc F) (wConst w)) := by
    rw [wConst, ← hn, ← hd, map_div₀, algebraMap_eq_algebraMap_C, algebraMap_eq_algebraMap_C,
      logDeriv_div _ _ hAn hAd]
  -- A `count` weight `(k : RatFunc F)` is the constant `algebraMap (C (k : F))`.
  have hcast : ∀ (m : Multiset F[X]) (π : F[X]),
      ((m.count π : ℕ) : RatFunc F)
        = algebraMap F[X] (RatFunc F) (Polynomial.C ((m.count π : ℕ) : F)) := by
    intro m π
    rw [← algebraMap_eq_algebraMap_C, map_natCast]
  -- Extend each factor sum over the union `factorsFinset w`; off-support counts are `0`.
  have hsub_n : (Mn.toFinset : Finset F[X]) ⊆ factorsFinset w := by
    rw [factorsFinset, ← hn]; exact Finset.subset_union_left
  have hsub_d : (Md.toFinset : Finset F[X]) ⊆ factorsFinset w := by
    rw [factorsFinset, ← hd]; exact Finset.subset_union_right
  have hext_n : ∑ π ∈ Mn.toFinset,
        ((Mn.count π : ℕ) : RatFunc F) * logDeriv (algebraMap F[X] (RatFunc F) π)
      = ∑ π ∈ factorsFinset w,
          algebraMap F[X] (RatFunc F) (Polynomial.C ((Mn.count π : ℕ) : F))
            * logDeriv (algebraMap F[X] (RatFunc F) π) := by
    rw [Finset.sum_subset hsub_n (fun π _ hπ => by
      rw [Multiset.mem_toFinset, ← Multiset.count_eq_zero] at hπ
      rw [hπ]; simp)]
    exact Finset.sum_congr rfl fun π _ => by rw [hcast]
  have hext_d : ∑ π ∈ Md.toFinset,
        ((Md.count π : ℕ) : RatFunc F) * logDeriv (algebraMap F[X] (RatFunc F) π)
      = ∑ π ∈ factorsFinset w,
          algebraMap F[X] (RatFunc F) (Polynomial.C ((Md.count π : ℕ) : F))
            * logDeriv (algebraMap F[X] (RatFunc F) π) := by
    rw [Finset.sum_subset hsub_d (fun π _ hπ => by
      rw [Multiset.mem_toFinset, ← Multiset.count_eq_zero] at hπ
      rw [hπ]; simp)]
    exact Finset.sum_congr rfl fun π _ => by rw [hcast]
  -- Assemble: leading-coeff part + (num sum − denom sum) merged into the `poleMult` sum.
  rw [hext_n, hext_d, ← hwconst]
  -- Expand the `poleMult` sum on the RHS into a difference of the two count-products.
  have hpole : ∑ π ∈ factorsFinset w,
        algebraMap F[X] (RatFunc F) (Polynomial.C (poleMult w π))
          * logDeriv (algebraMap F[X] (RatFunc F) π)
      = ∑ π ∈ factorsFinset w,
          algebraMap F[X] (RatFunc F) (Polynomial.C ((Mn.count π : ℕ) : F))
            * logDeriv (algebraMap F[X] (RatFunc F) π)
        - ∑ π ∈ factorsFinset w,
          algebraMap F[X] (RatFunc F) (Polynomial.C ((Md.count π : ℕ) : F))
            * logDeriv (algebraMap F[X] (RatFunc F) π) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [poleMult, ← hn, ← hd, ← hMn, ← hMd, map_sub, map_sub, sub_mul]
  rw [hpole]; ring

omit [Differential F] [CharZero F] in
/-- **`poleMult` vanishes off `factorsFinset`** — the support fact merging the per-`wᵢ` sums into the
global pole-collection: if `π ∉ factorsFinset w` then `poleMult w π = 0` (both `t`-factor counts are
`0` there). -/
theorem poleMult_eq_zero_of_notMem [DecidableEq F] {w : RatFunc F} {π : F[X]}
    (hπ : π ∉ factorsFinset w) : poleMult w π = 0 := by
  simp only [factorsFinset, Finset.mem_union, Multiset.mem_toFinset, not_or,
    ← Multiset.count_eq_zero] at hπ
  rw [poleMult, hπ.1, hπ.2]; simp

omit [CharZero F] in
/-- **The multi-term `logDeriv`-sum pole-collection** (the multi-term pole-matching engine):
`∑ᵢ ↑(cᵢ)·logDeriv wᵢ = ∑ᵢ ↑(cᵢ)·logDeriv (↑(wConst wᵢ)) + ∑_{π ∈ S} ↑(C (∑ᵢ cᵢ · poleMult wᵢ π)) ·
logDeriv (↑π)`, where `S = ⋃ᵢ factorsFinset wᵢ` collects every monic-irreducible `t`-factor and the
residue `∑ᵢ cᵢ · poleMult wᵢ π` is a *constant* `F`-element.  The first summand is `F`-valued (no
`t`-pole); the collected sum is the `poleIndependence_finset_const`-ready simple-pole part.  Proof:
expand each `logDeriv wᵢ` by `logDeriv_eq_wConst_add_sum`, extend each pole sum to `S` (`poleMult`
vanishes off `factorsFinset`), swap the order of summation, and fold `cᵢ · ↑(C(poleMult)) = ↑(C(cᵢ ·
poleMult))` into the constant residue. -/
theorem sum_const_logDeriv_eq_wConst_add_pole [DecidableEq F] (u : F) {ι : Type*} [Fintype ι]
    (c : ι → F) (w : ι → RatFunc F) (hw : ∀ i, w i ≠ 0) :
    letI := logDifferential u
    ∑ i, algebraMap F (RatFunc F) (c i) * logDeriv (w i)
      = ∑ i, algebraMap F (RatFunc F) (c i)
            * logDeriv (algebraMap F (RatFunc F) (wConst (w i)))
        + ∑ π ∈ Finset.univ.biUnion (fun i => factorsFinset (w i)),
            algebraMap F[X] (RatFunc F)
                (Polynomial.C (∑ i, c i * poleMult (w i) π))
              * logDeriv (algebraMap F[X] (RatFunc F) π) := by
  letI := logDifferential u
  set S := Finset.univ.biUnion (fun i => factorsFinset (w i)) with hS
  -- Per-`i`: extend the pole sum to `S`, then `cᵢ·logDeriv wᵢ = cᵢ·logDeriv ↑(wConst) + ∑_S …`.
  have hsubS : ∀ i, factorsFinset (w i) ⊆ S := fun i =>
    Finset.subset_biUnion_of_mem (fun i => factorsFinset (w i)) (Finset.mem_univ i)
  have hper : ∀ i, algebraMap F (RatFunc F) (c i) * logDeriv (w i)
      = algebraMap F (RatFunc F) (c i) * logDeriv (algebraMap F (RatFunc F) (wConst (w i)))
        + ∑ π ∈ S, algebraMap F (RatFunc F) (c i)
            * (algebraMap F[X] (RatFunc F) (Polynomial.C (poleMult (w i) π))
                * logDeriv (algebraMap F[X] (RatFunc F) π)) := by
    intro i
    rw [logDeriv_eq_wConst_add_sum u (hw i), mul_add, Finset.mul_sum]
    congr 1
    rw [Finset.sum_subset (hsubS i) (fun π _ hπ => by
      rw [poleMult_eq_zero_of_notMem hπ]; simp)]
  -- Sum over `i`, split into the `F`-part and the (swapped) pole part.
  rw [Finset.sum_congr rfl (fun i _ => hper i), Finset.sum_add_distrib]
  congr 1
  -- Swap `∑ᵢ ∑_S` to `∑_S ∑ᵢ` and fold `cᵢ·↑(C(poleMult)) = ↑(C(cᵢ·poleMult))`.
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [algebraMap_eq_algebraMap_C, ← mul_assoc, ← map_mul, ← Polynomial.C_mul]

/-- **The single-log pole-independence obligation** — the genuine partial-fraction content of the
single-logarithm case, sharply isolated.  GIVEN `a ∈ F`, a constant `c ∈ F`, `w v ∈ RatFunc F` with
`algebraMap a = c · logDeriv w + v′`, there exist `w₀ : F` and `v₀ : RatFunc F` rewriting the same
sum with the logarithm's argument **already in `F`** and `v₀′` the corrected `v`-term.  Content: the
simple `t`-poles of `logDeriv w` (one per monic-irreducible `t`-factor of `num w`/`denom w`, all of
residue-order `1` by `logDeriv_monic_proper`) cannot be matched by `a ∈ F` (no pole) nor by `v′`
(poles of order `≥ 2`), forcing every `t`-factor's exponent to `0`, i.e. `w ∈ F·(t-unit)`.  This is
the `ι`-singleton instance of the full pole-matching, isolated from the multi-term linear-independence
(`SharedFactorObligation`). -/
def SingleLogPoleObligation (u : F) : Prop :=
  letI := logDifferential u
  letI := logDifferentialAlgebra u
  ∀ (a : F) (c : F), c′ = 0 → ∀ (w v : RatFunc F),
    algebraMap F (RatFunc F) a = algebraMap F (RatFunc F) c * logDeriv w + v′ →
    ∃ (w₀ : F) (v₀ : RatFunc F),
      algebraMap F (RatFunc F) a
        = algebraMap F (RatFunc F) c * logDeriv (algebraMap F (RatFunc F) w₀) + v₀′
      ∧ v₀′ ∈ (algebraMap F (RatFunc F)).range

omit [CharZero F] in
/-- **The single-logarithm case closes modulo its two residues** (pole-independence + the `v ∈ F`
descent).  GIVEN `SingleLogPoleObligation` (the simple-pole independence isolating the log argument
into `F` with a corrected `v₀` whose derivative is in `F`) and the `v ∈ F` inputs
(`RationalToPolyObligation`, `PolyVReductionObligation`), any single-log representation `algebraMap a
= c · logDeriv w + v′` of `a ∈ F` yields `F`-data: `w₀ ∈ F` and a `v₀ ∈ F`.  This is the `ι`-singleton
instance of `LiouvilleFDataReduction`, with all glue proven and only the stated frontiers open. -/
theorem singleLog_fData (u : F) (hslp : SingleLogPoleObligation u)
    (hrtp : RationalToPolyObligation u) (hpv : PolyVReductionObligation u) (hu : logDeriv u ≠ 0)
    (a : F) (c : F) (hc : c′ = 0) (w v : RatFunc F)
    (h : letI := logDifferential u; letI := logDifferentialAlgebra u;
      algebraMap F (RatFunc F) a = algebraMap F (RatFunc F) c * logDeriv w + v′) :
    letI := logDifferential u
    letI := logDifferentialAlgebra u
    ∃ (w₀ : F) (v₀ : F),
      algebraMap F (RatFunc F) a
        = algebraMap F (RatFunc F) c * logDeriv (algebraMap F (RatFunc F) w₀)
            + (algebraMap F (RatFunc F) v₀)′ := by
  letI := logDifferential u
  letI := logDifferentialAlgebra u
  -- Pole-independence: pull the log argument into `F`, leaving a corrected `v₀` with `v₀′ ∈ F`.
  obtain ⟨w₀, v₁, h₁, hv₁⟩ := hslp a c hc w v h
  -- The corrected `v₁` has derivative in `F`, so by the `v ∈ F` reduction `v₁ ∈ F`.
  obtain ⟨v₀, hv₀⟩ := mem_range_of_deriv_mem_range u hrtp hpv hu hv₁
  exact ⟨w₀, v₀, by rw [h₁, hv₀]⟩

/-- **Obligation 4 (`ContainConstants F F(t)`, the transcendence non-degeneracy — needed only to
*tower* logs).**  GIVEN the extended derivation, every `t`-constant is in `F`:
`x′ = 0 → x ∈ range (algebraMap F (RatFunc F))`.  This is *not* needed for the single keystone
`IsLiouville F F(t)`; it is what `IsLiouville.trans` requires to chain a tower `F ⊆ F(log u₁) ⊆
F(log u₁, log u₂) ⊆ …`.  The polynomial layer is **already discharged** above
(`eq_C_of_logDerivPoly_eq_zero`): a `t`-constant is a single `C b` with `b' = 0`, hence in `F` —
reducing this obligation to `NoDegreeDropObligation u` (the transcendence input "`b·u'/u` has no
`F`-antiderivative") plus the fraction-field denominator-clearing step.  Carries `logDeriv u ≠ 0`:
when `u' = 0`, `log u` *is* a new constant and `ContainConstants F F(t)` is genuinely false. -/
def ContainConstantsObligation (u : F) [Differential (RatFunc F)] : Prop :=
  logDeriv u ≠ 0 → Differential.ContainConstants F (RatFunc F)

/-- **The F-data reduction residual** — the *sole* mathematical content left in Obligation 3, sharply
isolated.  It says: any `RatFunc F` representation `a = ∑ cᵢ logDeriv wᵢ + v′` of `a ∈ F` (`wᵢ, v ∈
F(t)`, `cᵢ` constant) can be re-expressed with the logarithms' arguments and the `v`-term **already
in `F`** — i.e. there exist `w₀ : ι → F`, `v₀ : F` with `a = ∑ cᵢ logDeriv (w₀ x) + v₀′` *as an
equation in `RatFunc F`*.  This is exactly the Rosenlicht pole-matching: factor each `wᵢ`, cancel its
proper `t`-poles (`logDeriv_monic_proper` — none survive since `a ∈ F` has no `t`-pole), and reduce
`v` to `F` via the top-coefficient/transcendence descent.  Everything *after* this (the final
`IsLiouville` packaging) is mechanical and **proven** in `isLiouvilleReduction_of_fDataReduction`. -/
def LiouvilleFDataReduction (u : F) : Prop :=
  letI := logDifferential u
  letI := logDifferentialAlgebra u
  ∀ (a : F) (ι : Type) [Fintype ι] (c : ι → F), (∀ x, (c x)′ = 0) →
    ∀ (w : ι → RatFunc F) (v : RatFunc F),
      algebraMap F (RatFunc F) a = ∑ x, algebraMap F (RatFunc F) (c x) * logDeriv (w x) + v′ →
      ∃ (w₀ : ι → F) (v₀ : F),
        algebraMap F (RatFunc F) a
          = ∑ x, algebraMap F (RatFunc F) (c x) * logDeriv (algebraMap F (RatFunc F) (w₀ x))
              + (algebraMap F (RatFunc F) v₀)′

/-! ### The multi-term pole-matching residual (the general `Σᵢ` case)

The full reduction beyond the single-logarithm case.  The genuine new content is the *multi-term*
`t`-pole cancellation: distinct `wᵢ` may **share** irreducible `t`-factors `πⱼ`, so `∑ᵢ cᵢ logDeriv
wᵢ` collects, at each `πⱼ`, the combination `(∑_{i : πⱼ | wᵢ} cᵢ eᵢⱼ) · logDeriv πⱼ`.  Since the
simple `t`-poles `{logDeriv πⱼ}` are *`F`-linearly independent modulo polynomials* (the partial-
fraction `t`-pole independence over `F[t]`) and `a ∈ F` has no pole, each such coefficient sum must
vanish — which lets the `wᵢ` be replaced by their `F`-parts and `∏ⱼ πⱼ^{…}` regrouped, leaving a
corrected `v`-term with derivative in `F`.  This residue is isolated below as
`MultiLogPoleObligation`; the linear-independence input it abstracts is `PoleIndependenceObligation`. -/

omit [CharZero F] in
/-- **The pole-independence input** — the precise partial-fraction `t`-pole-independence over `F[t]`
that the multi-term reduction needs, stated abstractly.  It says: if a finite `F`-combination of
logarithmic derivatives of monic irreducible `t`-polynomials, `∑ⱼ algebraMap (d j) · logDeriv
(algebraMap (π j))` (the `d j ∈ F[t]` of `t`-degree `< deg π j`, the `π j` distinct monic
irreducibles), is itself a *polynomial* (lies in `range (algebraMap F[t])`), then every numerator
`d j` is `0`.  Equivalently: the proper simple `t`-poles `(D πⱼ)/πⱼ` are `F[t]`-linearly independent
modulo `F[t]`.  This is the engine `logDeriv_monic_proper` upgraded from "each is a pole" to "they
cannot cancel each other or a polynomial" — the genuine multi-term frontier. -/
def PoleIndependenceObligation (u : F) : Prop :=
  letI := logDifferential u
  ∀ {ιπ : Type} [Fintype ιπ] (π : ιπ → F[X]) (d : ιπ → F[X]),
    (∀ j, (π j).Monic) → (∀ j, Irreducible (π j)) → Function.Injective π →
    (∀ j, (d j).natDegree < (π j).natDegree) →
    (∑ j, algebraMap F[X] (RatFunc F) (d j)
        * logDeriv (algebraMap F[X] (RatFunc F) (π j)))
      ∈ (algebraMap F[X] (RatFunc F)).range →
    ∀ j, d j = 0

open scoped algebraMap in
omit [CharZero F] in
/-- **`PoleIndependenceObligation` PROVED from the engine, modulo the one transcendence residue
`∀ j, D πⱼ ≠ 0`.**  This is the genuine pole-independence proof: given distinct monic irreducible
`t`-polynomials `πⱼ`, numerators `dⱼ` with `deg dⱼ < deg πⱼ`, and `∑ⱼ dⱼ · logDeriv πⱼ` a *polynomial*,
every `dⱼ = 0` — *provided* no `πⱼ` is annihilated by the log-monomial derivation (`D πⱼ ≠ 0`).  The
argument is exactly Rosenlicht's: rewrite `logDeriv πⱼ = (D πⱼ)/πⱼ`, do polynomial division
`dⱼ·(D πⱼ) = πⱼ·quoⱼ + remⱼ` (`degree remⱼ < degree πⱼ`), so the sum is `↑(∑ quoⱼ) + ∑ ↑remⱼ/↑πⱼ`; matching
it against the polynomial value via the **partial-fraction uniqueness** `quo_add_sum_rem_div_unique`
(distinct monic irreducibles are pairwise coprime, `Irreducible.coprime_iff_not_dvd` +
`eq_of_monic_of_associated`) forces every `remⱼ = 0`, i.e. `πⱼ ∣ dⱼ·(D πⱼ)`.  Since
`πⱼ ∤ D πⱼ` (the strict pole increase `not_dvd_logDerivPoly_of_natDegree_lt`, using `D πⱼ ≠ 0`), Euclid's
lemma gives `πⱼ ∣ dⱼ`, and `deg dⱼ < deg πⱼ` forces `dⱼ = 0`.  **The residue `D πⱼ ≠ 0` is precisely the
transcendence of `log u`** (see `PolyVReductionObligation`): for a genuine log no positive-degree monic
irreducible is killed by `D`; if `F` already contains an antiderivative `s` of `u'/u` then `π = t − C s`
has `D π = 0` and the statement is **false** — so this residue cannot be discharged from the abstract
`[Field F] [Differential F] [CharZero F]` alone, and `PoleIndependenceObligation` as literally stated
(no such guard) is a non-theorem in that degenerate case. -/
theorem poleIndependence_of_logDerivPoly_ne_zero (u : F) {ιπ : Type*} [Fintype ιπ]
    (π : ιπ → F[X]) (d : ιπ → F[X]) (hmon : ∀ j, (π j).Monic) (hirr : ∀ j, Irreducible (π j))
    (hinj : Function.Injective π) (hdeg : ∀ j, (d j).natDegree < (π j).natDegree)
    (hDne : ∀ j, logDerivPoly u (π j) ≠ 0)
    (hpoly : letI := logDifferential u
      (∑ j, algebraMap F[X] (RatFunc F) (d j)
          * logDeriv (algebraMap F[X] (RatFunc F) (π j)))
        ∈ (algebraMap F[X] (RatFunc F)).range) :
    ∀ j, d j = 0 := by
  letI := logDifferential u
  -- Notation: `D πⱼ`, the quotient/remainder of `dⱼ · D πⱼ` by the monic `πⱼ`.
  set Dπ : ιπ → F[X] := fun j => logDerivPoly u (π j) with hDπ
  set rem : ιπ → F[X] := fun j => (d j * Dπ j) %ₘ (π j) with hrem
  set quo : ιπ → F[X] := fun j => (d j * Dπ j) /ₘ (π j) with hquo
  -- `deg πⱼ ≥ 1` and `deg remⱼ < deg πⱼ`.
  have hdegπ : ∀ j, 1 ≤ (π j).natDegree := fun j => (hirr j).natDegree_pos
  have hdegrem : ∀ j, (rem j).degree < (π j).degree := fun j =>
    degree_modByMonic_lt _ (hmon j)
  -- Each term equals `↑quoⱼ + ↑remⱼ / ↑πⱼ` in `RatFunc F`.
  have hπne : ∀ j, (algebraMap F[X] (RatFunc F) (π j)) ≠ 0 := fun j =>
    RatFunc.algebraMap_ne_zero (hmon j).ne_zero
  have hterm : ∀ j, algebraMap F[X] (RatFunc F) (d j)
      * logDeriv (algebraMap F[X] (RatFunc F) (π j))
      = (quo j : RatFunc F) + (rem j : RatFunc F) / (π j : RatFunc F) := by
    intro j
    rw [logDeriv_algebraMap_eq u (π j)]
    show algebraMap F[X] (RatFunc F) (d j)
        * (algebraMap F[X] (RatFunc F) (Dπ j) / algebraMap F[X] (RatFunc F) (π j))
      = (quo j : RatFunc F) + (rem j : RatFunc F) / (π j : RatFunc F)
    -- `dⱼ · (D πⱼ / πⱼ) = (dⱼ · D πⱼ) / πⱼ`, then `dⱼ·D πⱼ = πⱼ·quoⱼ + remⱼ`.
    have hsplit : d j * Dπ j = π j * quo j + rem j := by
      rw [hrem, hquo, add_comm]; exact (modByMonic_add_div (d j * Dπ j) (π j)).symm
    rw [mul_div_assoc', ← map_mul, hsplit, map_add, map_mul, add_div]
    congr 1
    rw [mul_comm, mul_div_assoc, div_self (hπne j), mul_one]
  -- Rewrite the whole sum and pull out the polynomial value `P`.
  obtain ⟨P, hP⟩ := hpoly
  simp_rw [hterm] at hP
  rw [Finset.sum_add_distrib, ← map_sum] at hP
  -- Now `↑P = ↑(∑ quoⱼ) + ∑ ↑remⱼ/↑πⱼ`; uniqueness against `↑P + ∑ ↑0/↑πⱼ` forces `remⱼ = 0`.
  have hcop : Set.Pairwise (Finset.univ : Finset ιπ) fun i j => IsCoprime (π i) (π j) := by
    intro i _ j _ hij
    rw [(hirr i).coprime_iff_not_dvd]
    intro hdvd
    exact hij (hinj (eq_of_monic_of_associated (hmon i) (hmon j)
      ((hirr i).associated_of_dvd (hirr j) hdvd)))
  have hdeg0 : ∀ j, (0 : F[X]).degree < (π j).degree := by
    intro j
    rw [Polynomial.degree_zero]
    exact bot_lt_iff_ne_bot.mpr (Polynomial.degree_eq_bot.not.mpr (hmon j).ne_zero)
  have huniq := Polynomial.quo_add_sum_rem_div_unique (R := F) (K := RatFunc F)
    (g := π) (s := Finset.univ) (fun j _ => hmon j) hcop
    (q₁ := ∑ j, quo j) (q₂ := P) (r₁ := rem) (r₂ := fun _ => 0)
    (fun j _ => hdegrem j) (fun j _ => hdeg0 j)
    (by push_cast; simpa [div_eq_mul_inv] using hP.symm)
  -- From uniqueness `remⱼ = 0`, get `πⱼ ∣ dⱼ · D πⱼ`, then `πⱼ ∣ dⱼ`, then `dⱼ = 0`.
  intro j
  have hrem0 : rem j = 0 := huniq.2 j (Finset.mem_univ j)
  have hdvd : π j ∣ d j * Dπ j :=
    (Polynomial.modByMonic_eq_zero_iff_dvd (hmon j)).mp hrem0
  have hnd : ¬ π j ∣ Dπ j :=
    not_dvd_logDerivPoly_of_natDegree_lt u (hmon j) (hdegπ j) (hDne j)
  have hdvdd : π j ∣ d j := ((hirr j).prime.dvd_or_dvd hdvd).resolve_right hnd
  by_contra hd0
  exact absurd (Polynomial.natDegree_le_of_dvd hdvdd hd0) (by have := hdeg j; omega)

omit [CharZero F] in
/-- **`PoleIndependenceObligation` DISCHARGED from `NondegenerateLog`.**  The non-degeneracy hypothesis
supplies `D πⱼ ≠ 0` for every monic irreducible `πⱼ`, which is exactly the residue
`poleIndependence_of_logDerivPoly_ne_zero` needs — so the pole-independence holds unconditionally once
the log is a genuine new monomial. -/
theorem poleIndependenceObligation_of_nondegenerateLog (u : F) (hnd : NondegenerateLog u) :
    PoleIndependenceObligation u := by
  letI := logDifferential u
  intro ιπ _ π d hmon hirr hinj hdeg hpoly
  exact poleIndependence_of_logDerivPoly_ne_zero u π d hmon hirr hinj hdeg
    (fun j => hnd (π j) (hmon j) (hirr j)) hpoly

open scoped algebraMap in
omit [CharZero F] in
/-- **Pole-independence over a `Finset` of distinct monic irreducibles, with constant residues**
(the `MultiLogPoleObligation`-facing form of `PoleIndependenceObligation`).  GIVEN `NondegenerateLog`,
a finite set `S` of monic irreducible `t`-polynomials and *constant* residues `r : F[X] → F`, if the
collected simple-pole sum `∑_{π ∈ S} ↑(C (r π)) · logDeriv (algebraMap π)` is a *polynomial*, then
every residue `r π = 0` (`π ∈ S`).  This packages the abstract `poleIndependence_of_logDerivPoly_ne_zero`
over the subtype `↥S` (a `Fintype` with injective `Subtype.val`), with each numerator `C (r π)` of
`t`-degree `0 < deg π` (irreducibles have positive degree). -/
theorem poleIndependence_finset_const (u : F) (hnd : NondegenerateLog u) (S : Finset F[X])
    (hmon : ∀ π ∈ S, π.Monic) (hirr : ∀ π ∈ S, Irreducible π) (r : F[X] → F)
    (hpoly : letI := logDifferential u
      (∑ π ∈ S, algebraMap F[X] (RatFunc F) (Polynomial.C (r π))
          * logDeriv (algebraMap F[X] (RatFunc F) π))
        ∈ (algebraMap F[X] (RatFunc F)).range) :
    ∀ π ∈ S, r π = 0 := by
  letI := logDifferential u
  -- Apply the subtype-indexed pole-independence; `π = Subtype.val`, `d = C ∘ r ∘ val`.
  have hkey := poleIndependence_of_logDerivPoly_ne_zero u (ιπ := ↥S)
    (π := fun j => (j : F[X])) (d := fun j => Polynomial.C (r (j : F[X])))
    (fun j => hmon j j.2) (fun j => hirr j j.2) Subtype.val_injective
    (fun j => by
      -- `deg (C (r j)) ≤ 0 < 1 ≤ deg (val j)` (irreducible ⇒ positive degree).
      calc (Polynomial.C (r (j : F[X]))).natDegree ≤ 0 := (Polynomial.natDegree_C _).le
        _ < (↑j : F[X]).natDegree := (hirr j j.2).natDegree_pos)
    (fun j => hnd (↑j) (hmon j j.2) (hirr j j.2))
    (by
      -- The subtype-`Fintype` sum equals the `Finset` sum `hpoly`.
      rw [← Finset.sum_attach S (fun π => algebraMap F[X] (RatFunc F) (Polynomial.C (r π))
        * logDeriv (algebraMap F[X] (RatFunc F) π))] at hpoly
      exact hpoly)
  intro π hπ
  have hcj := hkey ⟨π, hπ⟩
  simpa using congrArg (fun q : F[X] => q.coeff 0) hcj

/-- **The multi-term pole-matching obligation** — the full `Σᵢ` analogue of `SingleLogPoleObligation`,
sharply isolated.  GIVEN `a ∈ F`, constants `cᵢ`, and `wᵢ, v ∈ RatFunc F` with `algebraMap a = ∑ᵢ cᵢ
logDeriv wᵢ + v′`, there exist `F`-arguments `w₀ : ι → F` and a corrected `v₀ : RatFunc F` with the
same sum (logarithms' arguments **in `F`**) and `v₀′ ∈ F`.  Content: factoring every `wᵢ` and using
the pole-independence (`PoleIndependenceObligation`), the shared/non-shared `t`-factor exponents
cancel against `a`'s (absent) pole and `v′`'s (order-`≥ 2`) poles, collapsing each `wᵢ` to its
`F`-part and absorbing the `t`-polynomial remainder into `v₀`.  Discharging this is the heart of the
transcendental Liouville theorem. -/
def MultiLogPoleObligation (u : F) : Prop :=
  letI := logDifferential u
  letI := logDifferentialAlgebra u
  ∀ (a : F) (ι : Type) [Fintype ι] (c : ι → F), (∀ x, (c x)′ = 0) →
    ∀ (w : ι → RatFunc F) (v : RatFunc F),
      algebraMap F (RatFunc F) a = ∑ x, algebraMap F (RatFunc F) (c x) * logDeriv (w x) + v′ →
      ∃ (w₀ : ι → F) (v₀ : RatFunc F),
        (algebraMap F (RatFunc F) a
          = ∑ x, algebraMap F (RatFunc F) (c x) * logDeriv (algebraMap F (RatFunc F) (w₀ x)) + v₀′)
        ∧ v₀′ ∈ (algebraMap F (RatFunc F)).range

omit [Differential F] [CharZero F] in
/-- **An `F`-coefficient combination of `logDeriv`s of `F`-elements is a polynomial** (the
`F`-valued, `t`-pole-free part of the collected sum): `∑ᵢ ↑(cᵢ) · logDeriv (algebraMap (xᵢ))` lies in
`range (algebraMap F[t])`, since each `logDeriv (algebraMap xᵢ) = algebraMap (logDeriv xᵢ)` is an
`F`-element (`logDeriv_algebraMap`) and `↑cᵢ · ↑(logDeriv xᵢ) = ↑(C (cᵢ · logDeriv xᵢ))`. -/
theorem sum_const_logDeriv_algebraMap_mem_range [Differential F] (u : F) {ι : Type*} [Fintype ι]
    (c : ι → F) (x : ι → F) :
    letI := logDifferential u
    (∑ i, algebraMap F (RatFunc F) (c i)
        * logDeriv (algebraMap F (RatFunc F) (x i)))
      ∈ (algebraMap F[X] (RatFunc F)).range := by
  letI := logDifferential u
  letI := logDifferentialAlgebra u
  refine ⟨Polynomial.C (∑ i, c i * logDeriv (x i)), ?_⟩
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [logDeriv_algebraMap, ← algebraMap_eq_algebraMap_C, ← map_mul]

/-- **The simple-pole separation residual** — the *sole* remaining content of the transcendental log
keystone, sharply isolated.  It says: for `v ∈ RatFunc F`, a finite set `S` of monic irreducible
`t`-polynomials and *constant* residues `r : F[X] → F`, if the derivative `v′` plus the simple-pole sum
`∑_{π ∈ S} ↑(C (r π)) · logDeriv (algebraMap π)` is a *polynomial*, then the simple-pole sum is *by
itself* a polynomial.  This is the genuine partial-fraction frontier: under `NondegenerateLog` the
twisted derivative `v′` has only poles of order `≥ 2` (`D(rπ⁻ᵏ) = … − k r (Dπ) π⁻ᵏ⁻¹`, with `π ∤ Dπ`),
while `logDeriv (algebraMap π) = (Dπ)/π` is a *simple* (order-`1`) pole — so the two pole parts cannot
cancel and separate.  Discharging it (a partial-fractions-with-multiplicities + twisted-derivative
pole-order development) closes the keystone; everything else — factoring, collecting, and cancelling
via `poleIndependence_finset_const` — is proved. -/
def DerivSimplePoleSeparation (u : F) : Prop :=
  letI := logDifferential u
  ∀ (v : RatFunc F) (S : Finset F[X]) (r : F[X] → F),
    (∀ π ∈ S, π.Monic) → (∀ π ∈ S, Irreducible π) →
    (v′ + ∑ π ∈ S, algebraMap F[X] (RatFunc F) (Polynomial.C (r π))
        * logDeriv (algebraMap F[X] (RatFunc F) π))
      ∈ (algebraMap F[X] (RatFunc F)).range →
    (∑ π ∈ S, algebraMap F[X] (RatFunc F) (Polynomial.C (r π))
        * logDeriv (algebraMap F[X] (RatFunc F) π))
      ∈ (algebraMap F[X] (RatFunc F)).range

omit [CharZero F] in
/-- **`MultiLogPoleObligation` DISCHARGED from `NondegenerateLog` + the simple-pole separation.**
The full multi-term pole-matching, proved modulo the single sharp residual `DerivSimplePoleSeparation`.
Given `algebraMap a = ∑ᵢ ↑cᵢ · logDeriv wᵢ + v′` (`a ∈ F`, `cᵢ` constants): replace any zero `wᵢ` by
`1` (same `logDeriv`), factor and collect (`sum_const_logDeriv_eq_wConst_add_pole`) into the `F`-part
`∑ᵢ ↑cᵢ · logDeriv (↑(wConst w'ᵢ))` plus the constant-residue simple-pole sum `∑_{π∈S} ↑(C Dπ) ·
logDeriv ↑π` with `Dπ = ∑ᵢ cᵢ · poleMult w'ᵢ π`.  Since `algebraMap a` and the `F`-part are polynomials
(`sum_const_logDeriv_algebraMap_mem_range`), `v′ + (simple-pole sum)` is a polynomial, so by
`DerivSimplePoleSeparation` the simple-pole sum is a polynomial; then `poleIndependence_finset_const`
(from `NondegenerateLog`) forces every `Dπ = 0`, the pole sum vanishes, and `v′ = algebraMap a − ∑ᵢ ↑cᵢ
logDeriv (↑w₀ᵢ) ∈ F`.  Take `w₀ᵢ = wConst w'ᵢ` and `v₀ = v`. -/
theorem multiLogPoleObligation_of_nondegenerateLog (u : F) (hnd : NondegenerateLog u)
    (hsep : DerivSimplePoleSeparation u) : MultiLogPoleObligation u := by
  letI := logDifferential u
  letI := logDifferentialAlgebra u
  classical
  intro a ι _ c _hc w v h
  -- Replace zero `wᵢ` by `1` (`logDeriv 1 = 0 = logDeriv 0`); `w'ᵢ ≠ 0`.
  set w' : ι → RatFunc F := fun i => if w i = 0 then 1 else w i with hw'def
  have hw'ne : ∀ i, w' i ≠ 0 := by
    intro i; rw [hw'def]; dsimp only; split
    · exact one_ne_zero
    · assumption
  have hlog_eq : ∀ i, logDeriv (w' i) = logDeriv (w i) := by
    intro i; rw [hw'def]; dsimp only; split
    · rename_i h0; rw [h0, logDeriv_one, Differential.logDeriv_zero]
    · rfl
  -- Collection: `∑ᵢ ↑cᵢ logDeriv wᵢ = F-part + simple-pole sum` over `S`.
  set S := Finset.univ.biUnion (fun i => factorsFinset (w' i)) with hSdef
  have hcollect := sum_const_logDeriv_eq_wConst_add_pole u c w' hw'ne
  simp_rw [hlog_eq] at hcollect
  -- The `F`-part is a polynomial; so is `algebraMap a`.
  have hFpart : (∑ i, algebraMap F (RatFunc F) (c i)
      * logDeriv (algebraMap F (RatFunc F) (wConst (w' i))))
      ∈ (algebraMap F[X] (RatFunc F)).range :=
    sum_const_logDeriv_algebraMap_mem_range u c (fun i => wConst (w' i))
  obtain ⟨pF, hpF⟩ := hFpart
  obtain ⟨pa, hpa⟩ : algebraMap F (RatFunc F) a ∈ (algebraMap F[X] (RatFunc F)).range :=
    ⟨Polynomial.C a, (algebraMap_eq_algebraMap_C a).symm⟩
  -- `v′ + (simple-pole sum) = algebraMap a − F-part`, a polynomial.
  set P : RatFunc F := ∑ π ∈ S, algebraMap F[X] (RatFunc F)
      (Polynomial.C (∑ i, c i * poleMult (w' i) π)) * logDeriv (algebraMap F[X] (RatFunc F) π)
    with hPdef
  have hvP : v′ + P ∈ (algebraMap F[X] (RatFunc F)).range := by
    refine ⟨pa - pF, ?_⟩
    rw [map_sub, hpa, hpF, h, hcollect]; ring
  -- Membership hypotheses: every `π ∈ S` is monic irreducible.
  have hmonS : ∀ π ∈ S, π.Monic := fun π hπ => by
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hπ
    exact (factorsFinset_monic_irreducible hi).1
  have hirrS : ∀ π ∈ S, Irreducible π := fun π hπ => by
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hπ
    exact (factorsFinset_monic_irreducible hi).2
  -- Simple-pole separation: the simple-pole sum `P` is itself a polynomial.
  have hPpoly : P ∈ (algebraMap F[X] (RatFunc F)).range :=
    hsep v S (fun π => ∑ i, c i * poleMult (w' i) π) hmonS hirrS hvP
  -- Pole-independence: every residue `∑ᵢ cᵢ · poleMult w'ᵢ π = 0`, so `P = 0`.
  have hres0 : ∀ π ∈ S, (∑ i, c i * poleMult (w' i) π) = 0 :=
    poleIndependence_finset_const u hnd S hmonS hirrS _ hPpoly
  have hP0 : P = 0 := by
    rw [hPdef]
    refine Finset.sum_eq_zero fun π hπ => ?_
    rw [hres0 π hπ]; simp
  -- The `F`-part is `algebraMap F (RatFunc F) xF` for the `F`-element `xF`.
  set xF : F := ∑ i, c i * logDeriv (wConst (w' i)) with hxFdef
  have hFpart_eq : (∑ i, algebraMap F (RatFunc F) (c i)
      * logDeriv (algebraMap F (RatFunc F) (wConst (w' i))))
      = algebraMap F (RatFunc F) xF := by
    rw [hxFdef, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [logDeriv_algebraMap, ← map_mul]
  -- Conclude: `w₀ = wConst ∘ w'`, `v₀ = v`; `v′ = ↑a − ↑xF = ↑(a − xF) ∈ F`.
  refine ⟨fun i => wConst (w' i), v, ?_, ?_⟩
  · -- `↑a = F-part + P + v′ = F-part + v′` (since `P = 0`).
    rw [h, hcollect, hP0, add_zero]
  · -- `v′ = ↑a − F-part = ↑(a − xF) ∈ range (algebraMap F)`.
    refine ⟨a - xF, ?_⟩
    have hh : algebraMap F (RatFunc F) a
        = algebraMap F (RatFunc F) xF + v′ := by
      rw [h, hcollect, hFpart_eq, hP0, add_zero]
    rw [map_sub, hh]; ring

omit [CharZero F] in
/-- **`LiouvilleFDataReduction` closes modulo the multi-term pole residue + the `v ∈ F` descent.**
GIVEN `MultiLogPoleObligation` (the full pole-matching collapsing every `wᵢ` to `F` with a corrected
`v₀`, `v₀′ ∈ F`) and the `v ∈ F` inputs (`RationalToPolyObligation`, `PolyVReductionObligation`), the
entire Rosenlicht reduction `LiouvilleFDataReduction u` holds: feed each representation through the
pole-matching, then reduce the corrected `v₀` to `F` via `mem_range_of_deriv_mem_range`.  All the
glue — chaining pole-matching into the `v`-term descent and repackaging — is proven; only the stated
frontiers (`MultiLogPoleObligation`, itself resting on `PoleIndependenceObligation`, plus the two
`v ∈ F` residues) remain.  This is the keystone reduced to its sharpest pole-matching core. -/
theorem fDataReduction_of_multiLogPole (u : F) (hmlp : MultiLogPoleObligation u)
    (hrtp : RationalToPolyObligation u) (hpv : PolyVReductionObligation u) (hu : logDeriv u ≠ 0) :
    LiouvilleFDataReduction u := by
  letI := logDifferential u
  letI := logDifferentialAlgebra u
  intro a ι _ c hc w v h
  -- Multi-term pole-matching: log arguments into `F`, leaving a corrected `v₀` with `v₀′ ∈ F`.
  obtain ⟨w₀, v₁, h₁, hv₁⟩ := hmlp a ι c hc w v h
  -- The corrected `v₁` has derivative in `F`, so by the `v ∈ F` reduction `v₁ ∈ F`.
  obtain ⟨v₀, hv₀⟩ := mem_range_of_deriv_mem_range u hrtp hpv hu hv₁
  exact ⟨w₀, v₀, by rw [h₁, hv₀]⟩

omit [CharZero F] in
/-- **The single-log pole obligation is the `ι = Fin 1` instance of the multi-term one — PROVEN.**
`SingleLogPoleObligation` follows from `MultiLogPoleObligation` by specializing to a one-element index
(`∑ x : Fin 1, … = …`), so the single-logarithm pole-independence is genuinely a *special case* of the
full pole-matching, not an independent assumption.  (Confirms the obligation hierarchy: discharging
`MultiLogPoleObligation` discharges the single-log case too.) -/
theorem singleLogPole_of_multiLogPole (u : F) (hmlp : MultiLogPoleObligation u) :
    SingleLogPoleObligation u := by
  letI := logDifferential u
  letI := logDifferentialAlgebra u
  intro a c hc w v h
  obtain ⟨w₀, v₀, h₀, hv₀⟩ :=
    hmlp a (Fin 1) (fun _ => c) (fun _ => hc) (fun _ => w) v (by simpa using h)
  exact ⟨w₀ 0, v₀, by simpa using h₀, hv₀⟩

omit [CharZero F] in
/-- **The mechanical packaging — PROVEN.**  Given `F`-data for a single representation (the output of
the pole-matching reduction), `IsLiouville`'s existential conclusion holds: pull the
already-`F`-valued logarithms and `v`-term back through `algebraMap` injectivity
(`logDeriv_algebraMap`, `deriv_algebraMap`).  This is the entire "assembly" half of Obligation 3. -/
theorem isLiouville_conclusion_of_fData [Differential (RatFunc F)]
    [DifferentialAlgebra F (RatFunc F)]
    (a : F) (ι : Type) [Fintype ι] (c : ι → F) (hc : ∀ x, (c x)′ = 0)
    (w₀ : ι → F) (v₀ : F)
    (h : algebraMap F (RatFunc F) a
          = ∑ x, algebraMap F (RatFunc F) (c x) * logDeriv (algebraMap F (RatFunc F) (w₀ x))
              + (algebraMap F (RatFunc F) v₀)′) :
    ∃ (ι₀ : Type) (_ : Fintype ι₀) (c₀ : ι₀ → F) (_ : ∀ x, (c₀ x)′ = 0)
      (u₀ : ι₀ → F) (v₀' : F), a = ∑ x, c₀ x * logDeriv (u₀ x) + v₀'′ := by
  refine ⟨ι, inferInstance, c, hc, w₀, v₀, ?_⟩
  apply FaithfulSMul.algebraMap_injective F (RatFunc F)
  rw [map_add, map_sum, ← deriv_algebraMap]
  have hsum : ∀ x, (algebraMap F (RatFunc F)) (c x * logDeriv (w₀ x))
      = algebraMap F (RatFunc F) (c x) * logDeriv (algebraMap F (RatFunc F) (w₀ x)) := by
    intro x; rw [map_mul, ← logDeriv_algebraMap]
  simp_rw [hsum]
  exact h

/-- **Obligation 3 — the single remaining obligation: the `IsLiouville` reduction** on the genuine
log extension `RatFunc F` (Rosenlicht's partial-fraction / pole-matching argument, the heart of the
transcendental case).  The setup (`logDifferential`, `logDifferentialAlgebra`) is now fully real, so
the **entire** keystone reduces to this one `Prop`, and *that* reduces further (via the proven
`isLiouvilleReduction_of_fDataReduction`) to `LiouvilleFDataReduction u` — the pure pole-matching
content. -/
def IsLiouvilleReductionObligation (u : F) : Prop :=
  letI := logDifferential u
  letI := logDifferentialAlgebra u
  IsLiouville F (RatFunc F)

omit [CharZero F] in
/-- **The keystone, reduced to the pure pole-matching content — PROVEN assembly.**  Given
`LiouvilleFDataReduction u` (the Rosenlicht reduction of any representation to `F`-data),
`IsLiouville F (RatFunc F)` holds: feed each representation through the reduction, then package via
`isLiouville_conclusion_of_fData`.  So Obligation 3 ⟺ `LiouvilleFDataReduction u`, with the
`IsLiouville`-packaging fully discharged here. -/
theorem isLiouvilleReduction_of_fDataReduction (u : F)
    (hred : LiouvilleFDataReduction u) : IsLiouvilleReductionObligation u := by
  letI := logDifferential u
  letI := logDifferentialAlgebra u
  refine ⟨fun a ι _ c hc w v h => ?_⟩
  obtain ⟨w₀, v₀, h₀⟩ := hred a ι c hc w v h
  exact isLiouville_conclusion_of_fData a ι c hc w₀ v₀ h₀

omit [CharZero F] in
/-- **The keystone in one step from the single residual** (`LiouvilleFDataReduction u`): the genuine
`IsLiouville F (RatFunc F)` instance on the log extension.  Discharging `LiouvilleFDataReduction u`
(the Rosenlicht pole-matching) makes this an unconditional `instance`. -/
theorem isLiouville_of_fDataReduction (u : F) (hred : LiouvilleFDataReduction u) :
    letI := logDifferential u
    letI := logDifferentialAlgebra u
    IsLiouville F (RatFunc F) :=
  isLiouvilleReduction_of_fDataReduction u hred

omit [CharZero F] in
/-- **The keystone reduced one further step to the pole-matching core — PROVEN assembly.**  Composing
`fDataReduction_of_multiLogPole` with `isLiouvilleReduction_of_fDataReduction`: GIVEN the multi-term
pole residue and the `v ∈ F` inputs, the genuine `IsLiouville F (RatFunc F)` instance holds.  So the
keystone is unconditional **as soon as** `MultiLogPoleObligation` (+ the three transcendence/partial-
fraction residues) is discharged — every step after the pole-matching is proven here. -/
theorem isLiouville_of_multiLogPole (u : F) (hmlp : MultiLogPoleObligation u)
    (hrtp : RationalToPolyObligation u) (hpv : PolyVReductionObligation u) (hu : logDeriv u ≠ 0) :
    letI := logDifferential u
    letI := logDifferentialAlgebra u
    IsLiouville F (RatFunc F) :=
  isLiouvilleReduction_of_fDataReduction u
    (fDataReduction_of_multiLogPole u hmlp hrtp hpv hu)

omit [CharZero F] in
/-- **The keystone, assembled and PROVEN modulo the single `IsLiouville` reduction.**  The setup is
genuine (`logDifferential u` is a real `Differential (RatFunc F)`, `logDifferentialAlgebra u` a real
`DifferentialAlgebra F (RatFunc F)`, Obligations 1 and 2 *closed* above).  So `F(log u) = RatFunc F`
is a Liouville extension of `F` **iff** the `IsLiouville` reduction (Obligation 3,
`IsLiouvilleReductionObligation u`) holds — which itself reduces (via the proven
`isLiouvilleReduction_of_fDataReduction`) to the pure pole-matching `LiouvilleFDataReduction u`.
Only that Rosenlicht reduction-to-`F`-data now stands between this and an unconditional
`instance : IsLiouville F (RatFunc F)`; everything else (setup + `IsLiouville`-packaging) is proven.
(Towering several logs additionally needs Obligation 4, `ContainConstantsObligation`, via
`IsLiouville.trans`.) -/
theorem keystone (u : F) (hreduction : IsLiouvilleReductionObligation u) :
    letI := logDifferential u
    letI := logDifferentialAlgebra u
    IsLiouville F (RatFunc F) :=
  hreduction

omit [CharZero F] in
/-- **`t` lifts the log derivative: `(↑b · t)′ = ↑b · ↑(logDeriv u)` for a constant `b` (`b′ = 0`).**
The `b·t = b·log u` term differentiates to `b·(u'/u)` — exactly a `u`-logarithm with constant
coefficient.  Proved via `logDeriv` (`(↑b·t)′ = (↑b·t)·logDeriv(↑b·t)`, `logDeriv ↑b = 0` since `b′ = 0`,
`logDeriv t = ↑(C(u'/u))/t`), sidestepping the `RatFunc`-`Derivation.leibniz` algebra diamond. -/
theorem deriv_algebraMap_mul_X (u : F) {b : F} (hb : b′ = 0) :
    letI := logDifferential u
    letI := logDifferentialAlgebra u
    (algebraMap F (RatFunc F) b * algebraMap F[X] (RatFunc F) X)′
      = algebraMap F (RatFunc F) b * algebraMap F (RatFunc F) (logDeriv u) := by
  letI := logDifferential u
  letI := logDifferentialAlgebra u
  rcases eq_or_ne b 0 with rfl | hbne
  · simp
  have hbA : algebraMap F (RatFunc F) b ≠ 0 := RatFunc.algebraMap_ne_zero (by
    simpa using (FaithfulSMul.algebraMap_injective F (RatFunc F)).ne hbne)
  have hXA : algebraMap F[X] (RatFunc F) X ≠ 0 := RatFunc.algebraMap_ne_zero X_ne_zero
  -- `(↑b·t)′ = (↑b·t)·logDeriv(↑b·t)`, `logDeriv(↑b·t) = logDeriv ↑b + logDeriv t`.
  have hmulne : algebraMap F (RatFunc F) b * algebraMap F[X] (RatFunc F) X ≠ 0 :=
    mul_ne_zero hbA hXA
  have hv'eq : (algebraMap F (RatFunc F) b * algebraMap F[X] (RatFunc F) X)′
      = (algebraMap F (RatFunc F) b * algebraMap F[X] (RatFunc F) X)
        * logDeriv (algebraMap F (RatFunc F) b * algebraMap F[X] (RatFunc F) X) := by
    rw [logDeriv, mul_div_cancel₀ _ hmulne]
  -- `logDeriv ↑b = ↑(logDeriv b) = 0`, `logDeriv t = ↑(C(u'/u))/t`.
  have hlogb : logDeriv (algebraMap F (RatFunc F) b) = 0 := by
    rw [logDeriv_algebraMap, logDeriv, hb, zero_div, map_zero]
  have hlogX : logDeriv (algebraMap F[X] (RatFunc F) X)
      = algebraMap F (RatFunc F) (logDeriv u) / algebraMap F[X] (RatFunc F) X := by
    rw [logDeriv_algebraMap_eq u X, logDerivPoly_X, ← algebraMap_eq_algebraMap_C]
  have hlogmul : logDeriv (algebraMap F (RatFunc F) b * algebraMap F[X] (RatFunc F) X)
      = algebraMap F (RatFunc F) (logDeriv u) / algebraMap F[X] (RatFunc F) X := by
    rw [Differential.logDeriv_mul _ _ hbA hXA, hlogb, hlogX, zero_add]
  rw [hv'eq, hlogmul]
  field_simp

/-- **The transcendental-log Liouville keystone — UNCONDITIONAL modulo `NondegenerateLog` and the
single multi-term pole-matching residue.**  `F(log u) = RatFunc F` is a Liouville extension of `F`
whenever the log is a genuine new monomial (`NondegenerateLog u`) and the multi-term `t`-pole-matching
`MultiLogPoleObligation u` holds.  **The false `PolyVReductionObligation` is GONE:** the corrected
`v`-reduction `deriv_mem_range_imp_linear` (`v₀′ ∈ F ⟹ v₀ = vF + b·t`, `b` constant) feeds the surviving
linear term `b·t` back as the *new logarithm* `b·log u` (its derivative is `b·(u'/u)`,
`deriv_algebraMap_mul_X`), so `v₀′ = (↑vF)′ + b·logDeriv u`.  Packaging over `Option ι` (the extra index
carrying `b·log u`) yields the `IsLiouville` `F`-data.  Thus only `NondegenerateLog u` (the necessary
transcendence) and `MultiLogPoleObligation u` (the genuine pole-matching heart) remain — both proved
*around* it: `RationalToPolyObligation` and `PoleIndependenceObligation` are now theorems from
`NondegenerateLog`. -/
theorem isLiouville_of_nondegenerateLog (u : F) (hnd : NondegenerateLog u)
    (hmlp : MultiLogPoleObligation u) :
    letI := logDifferential u
    letI := logDifferentialAlgebra u
    IsLiouville F (RatFunc F) := by
  letI := logDifferential u
  letI := logDifferentialAlgebra u
  refine ⟨fun a ι _ c hc w v h => ?_⟩
  -- Multi-term pole-matching: log arguments into `F`, leaving a corrected `v₀` with `v₀′ ∈ F`.
  obtain ⟨w₀, v₀, h₀, hv₀⟩ := hmlp a ι c hc w v h
  -- Corrected `v`-reduction: `v₀ = ↑vF + ↑b·t` with `b` constant.
  obtain ⟨vF, b, hbconst, hv₀eq⟩ := deriv_mem_range_imp_linear u hnd hv₀
  -- `v₀′ = (↑vF)′ + ↑b·logDeriv(↑u)` (additivity + `deriv_algebraMap` + `deriv_algebraMap_mul_X`).
  have hv₀' : v₀′ = (algebraMap F (RatFunc F) vF)′
      + algebraMap F (RatFunc F) b * algebraMap F (RatFunc F) (logDeriv u) := by
    rw [hv₀eq, map_add, deriv_algebraMap_mul_X u hbconst]
  -- Assemble the fresh `F`-data over `Option ι`: `none ↦ b·log u`, `some x ↦ cₓ·log(w₀ x)`.
  refine ⟨Option ι, inferInstance, fun x => x.elim b c, ?_, fun x => x.elim u w₀, vF, ?_⟩
  · rintro (_ | x) <;> simp [hbconst, hc]
  · apply FaithfulSMul.algebraMap_injective F (RatFunc F)
    rw [map_add, ← deriv_algebraMap, Fintype.sum_option]
    simp only [Option.elim, map_add, map_sum]
    have hsum : ∀ x, algebraMap F (RatFunc F) (c x * logDeriv (w₀ x))
        = algebraMap F (RatFunc F) (c x) * logDeriv (algebraMap F (RatFunc F) (w₀ x)) := by
      intro x; rw [map_mul, ← logDeriv_algebraMap]
    simp_rw [hsum]
    -- `↑a = ↑b·logDeriv ↑u + ∑ ↑cᵢ logDeriv(↑w₀ᵢ) + (↑vF)′`, matching `h₀` + `hv₀'`.
    rw [h₀, hv₀', map_mul]
    ring

/-- **The transcendental-log Liouville keystone — UNCONDITIONAL modulo `NondegenerateLog` and the
single simple-pole separation residual.**  `F(log u) = RatFunc F` is a Liouville extension of `F`
whenever the log is a genuine new monomial (`NondegenerateLog u`, i.e. `log u ∉ F`) and the sharp
partial-fraction residual `DerivSimplePoleSeparation u` (a twisted-derivative `v′` has no simple
`t`-pole, so simple poles separate) holds.  **Every other ingredient is proved here:** the corrected
`v`-reduction `deriv_mem_range_imp_linear`, `RationalToPolyObligation` and `PoleIndependenceObligation`
(now theorems from `NondegenerateLog`), the UFD factorization fold, the multi-term pole collection, and
the constant-residue cancellation `poleIndependence_finset_const` — assembled in
`multiLogPoleObligation_of_nondegenerateLog`, then packaged into `IsLiouville` by
`isLiouville_of_nondegenerateLog`.  So the transcendental-completeness keystone is unconditional modulo
exactly two inputs: the necessary transcendence `NondegenerateLog u` and the one residual
`DerivSimplePoleSeparation u`. -/
theorem isLiouville_logExtension (u : F) (hnd : NondegenerateLog u)
    (hsep : DerivSimplePoleSeparation u) :
    letI := logDifferential u
    letI := logDifferentialAlgebra u
    IsLiouville F (RatFunc F) :=
  isLiouville_of_nondegenerateLog u hnd (multiLogPoleObligation_of_nondegenerateLog u hnd hsep)

-- Restatements pinning the genuine field setup.
-- `t' = u'/u` on `RatFunc F` itself (the log monomial, on the fraction field):
example (u : F) :
    letI := logDifferential u
    (algebraMap F[X] (RatFunc F) X)′ = algebraMap F[X] (RatFunc F) (C (logDeriv u)) := by
  have := derivExtends u X
  simpa [logDerivPoly_X] using this
-- The setup is a genuine differential field extension: `D` commutes with `algebraMap F (RatFunc F)`.
example (u : F) (a : F) :
    letI := logDifferential u
    letI := logDifferentialAlgebra u
    (algebraMap F (RatFunc F) a)′ = algebraMap F (RatFunc F) a′ :=
  letI := logDifferential u
  letI := logDifferentialAlgebra u
  deriv_algebraMap a
-- The keystone genuinely closes from the single pole-matching residual: discharging
-- `LiouvilleFDataReduction u` yields the real `IsLiouville F (RatFunc F)` instance.
example (u : F) (hred : LiouvilleFDataReduction u) :
    letI := logDifferential u
    letI := logDifferentialAlgebra u
    IsLiouville F (RatFunc F) :=
  isLiouville_of_fDataReduction u hred
-- The `v ∈ F` reduction: `v′ ∈ F ⟹ v ∈ F` on `RatFunc F`, modulo the two stated residues.
example (u : F) (hrtp : RationalToPolyObligation u) (hpv : PolyVReductionObligation u)
    (hu : logDeriv u ≠ 0) :
    letI := logDifferential u
    ∀ {v : RatFunc F}, v′ ∈ (algebraMap F (RatFunc F)).range →
      v ∈ (algebraMap F (RatFunc F)).range :=
  mem_range_of_deriv_mem_range u hrtp hpv hu
-- The keystone closes from the multi-term pole-matching core: discharging `MultiLogPoleObligation`
-- (+ the `v ∈ F` residues) yields the real `IsLiouville F (RatFunc F)` instance.
example (u : F) (hmlp : MultiLogPoleObligation u) (hrtp : RationalToPolyObligation u)
    (hpv : PolyVReductionObligation u) (hu : logDeriv u ≠ 0) :
    letI := logDifferential u
    letI := logDifferentialAlgebra u
    IsLiouville F (RatFunc F) :=
  isLiouville_of_multiLogPole u hmlp hrtp hpv hu
-- `PoleIndependenceObligation` is PROVEN from the engine once the transcendence residue
-- `∀ j, D πⱼ ≠ 0` is supplied: feeding that residue into `poleIndependence_of_logDerivPoly_ne_zero`
-- discharges the obligation, so the obligation ⟺ "no positive-degree monic irreducible is killed by `D`".
example (u : F)
    (hDne : letI := logDifferential u; ∀ {ιπ : Type} [Fintype ιπ] (π : ιπ → F[X]),
      (∀ j, Irreducible (π j)) → ∀ j, logDerivPoly u (π j) ≠ 0) :
    PoleIndependenceObligation u := by
  letI := logDifferential u
  intro ιπ _ π d hmon hirr hinj hdeg hpoly
  exact poleIndependence_of_logDerivPoly_ne_zero u π d hmon hirr hinj hdeg
    (hDne π hirr) hpoly
-- From the genuine non-degeneracy `NondegenerateLog u` (= `log u ∉ F`), BOTH the rational-to-poly
-- pole descent AND the pole-independence obligations are theorems (no longer assumptions).
example (u : F) (hnd : NondegenerateLog u) : RationalToPolyObligation u :=
  rationalToPolyObligation_of_nondegenerateLog u hnd
example (u : F) (hnd : NondegenerateLog u) : PoleIndependenceObligation u :=
  poleIndependenceObligation_of_nondegenerateLog u hnd
-- The keystone: a genuine new log monomial (`NondegenerateLog u`) plus ONLY the multi-term
-- pole-matching residue (`MultiLogPoleObligation u`) yields the real `IsLiouville F (RatFunc F)` —
-- the false `PolyVReductionObligation` no longer appears (its `b·t` survivor folds into `b·log u`).
example (u : F) (hnd : NondegenerateLog u) (hmlp : MultiLogPoleObligation u) :
    letI := logDifferential u
    letI := logDifferentialAlgebra u
    IsLiouville F (RatFunc F) :=
  isLiouville_of_nondegenerateLog u hnd hmlp
-- `MultiLogPoleObligation` is now a THEOREM from `NondegenerateLog u` plus the single sharp residual
-- `DerivSimplePoleSeparation u` (the simple poles of `logDeriv` separate from `v′`'s order-`≥ 2` poles).
example (u : F) (hnd : NondegenerateLog u) (hsep : DerivSimplePoleSeparation u) :
    MultiLogPoleObligation u :=
  multiLogPoleObligation_of_nondegenerateLog u hnd hsep
-- THE KEYSTONE, assembled: a genuine new log monomial (`NondegenerateLog u`) plus ONLY the simple-pole
-- separation residual (`DerivSimplePoleSeparation u`) yields the real `IsLiouville F (RatFunc F)`.  All
-- the factoring / collecting / pole-cancellation in between is proved (`isLiouville_logExtension`).
example (u : F) (hnd : NondegenerateLog u) (hsep : DerivSimplePoleSeparation u) :
    letI := logDifferential u
    letI := logDifferentialAlgebra u
    IsLiouville F (RatFunc F) :=
  isLiouville_logExtension u hnd hsep

end FieldObligations

end DeepWiki.SymbolicIntegration.LiouvilleLog
