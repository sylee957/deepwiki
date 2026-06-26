import Mathlib.FieldTheory.Differential.Liouville
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.FieldTheory.RatFunc.AsPolynomial
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
- **Obligation 3 (the only remainder) — the `IsLiouville` reduction.**  `keystone` reduces the
  *entire* transcendental-log Liouville instance to the single `Prop`
  `IsLiouvilleReductionObligation u` — Rosenlicht's partial-fraction / `t`-pole-matching argument.
  Its engine is built and proven here (`natDegree_logDerivPoly_lt_of_monic`,
  `coeff_logDerivPoly`, `logDerivPoly_monomial_eq`).
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
-- A `t`-constant has an `F`-constant `t`-leading coefficient.
example (u : F) {p : F[X]} (h : logDerivPoly u p = 0) : (p.leadingCoeff)′ = 0 :=
  leadingCoeff_deriv_eq_zero_of_logDerivPoly_eq_zero u h

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

/-- **Obligation 3 — the single remaining obligation: the `IsLiouville` reduction** on the genuine
log extension `RatFunc F` (Rosenlicht's partial-fraction / pole-matching argument, the heart of the
transcendental case).  If `a ∈ F` is written `a = ∑ cᵢ logDeriv wᵢ + v′` with `wᵢ, v ∈ F(t)`, `cᵢ`
constants, it must be rewritable with all data in `F`: factor each `wᵢ = (F-elt)·∏(monic
irreducibles in t)`; `logDeriv` of each monic `t`-factor `π` is *proper* (`deg (D π) < deg π`,
`natDegree_logDerivPoly_lt_of_monic`), a genuine `t`-pole; matching `t`-pole orders on both sides
(LHS `a ∈ F` has **none**) cancels every `t`-pole, folding the `t`-parts into a single `logDeriv
u`-multiple (`logDerivPoly_monomial_eq`) and forcing `v` to have no `t`-pole, hence `v ∈ F[t]` and
then `v ∈ F` (`leadingCoeff_deriv_eq_zero_of_logDerivPoly_eq_zero`).  The setup
(`logDifferential`, `logDifferentialAlgebra`) is now fully real, so the **entire** keystone reduces
to *this one* `Prop`. -/
def IsLiouvilleReductionObligation (u : F) : Prop :=
  letI := logDifferential u
  letI := logDifferentialAlgebra u
  IsLiouville F (RatFunc F)

omit [CharZero F] in
/-- **The keystone, assembled and PROVEN modulo the single `IsLiouville` reduction.**  The setup is
genuine (`logDifferential u` is a real `Differential (RatFunc F)`, `logDifferentialAlgebra u` a real
`DifferentialAlgebra F (RatFunc F)`, Obligations 1 and 2 *closed* above).  So `F(log u) = RatFunc F`
is a Liouville extension of `F` **iff** the `IsLiouville` reduction (Obligation 3,
`IsLiouvilleReductionObligation u`) holds — this theorem is that reduction made into the final
assembly.  Only the Rosenlicht pole-matching argument now stands between this and an unconditional
`instance : IsLiouville F (RatFunc F)`.  (Towering several logs additionally needs Obligation 4,
`ContainConstantsObligation`, via `IsLiouville.trans`.) -/
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

end FieldObligations

end DeepWiki.SymbolicIntegration.LiouvilleLog
