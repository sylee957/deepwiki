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

This file **builds the full setup** for the log monomial faithfully and **closes everything except
one named obligation**.

## Status (the keystone roadmap)

- **Setup — CLOSED.**  `logDifferential u : Differential (RatFunc F)` is a *genuine* differential
  field structure with `t' = u'/u`, and `logDifferentialAlgebra u : DifferentialAlgebra F (RatFunc
  F)` is real — so `F(log u) = RatFunc F` is an actual differential field extension of `F`.  The
  load-bearing piece is `fracDeriv`: **a derivation on `F[X]` extends to its fraction field by the
  quotient rule** — a self-derivation `Derivation ℤ K K` for any fraction field `K` of `F[X]`,
  built from scratch here (Mathlib has no such extension — only the Kähler-module-valued
  localization).  This is Mathlib-contributable on its own.
- **Obligation 3 — assembly PROVEN, reduced to one pole-matching `Prop`.**  `keystone` reduces the
  *entire* transcendental-log Liouville instance to `IsLiouvilleReductionObligation u`, and the
  `IsLiouville`-packaging half is **proven** (`isLiouville_conclusion_of_fData`,
  `isLiouvilleReduction_of_fDataReduction`), leaving the *single* residual `LiouvilleFDataReduction
  u` — the pure Rosenlicht reduction of any `F(t)`-representation to `F`-data (partial-fraction /
  `t`-pole-matching).  Its engine is built and proven here (`natDegree_logDerivPoly_lt_of_monic`,
  `coeff_logDerivPoly`, `logDerivPoly_monomial_eq`, `logDeriv_monic_proper`).  Discharging that one
  `Prop` makes `IsLiouville F (RatFunc F)` unconditional (`isLiouville_of_fDataReduction`).
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
theorem poleIndependence_of_logDerivPoly_ne_zero (u : F) {ιπ : Type} [Fintype ιπ]
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

end FieldObligations

end DeepWiki.SymbolicIntegration.LiouvilleLog
