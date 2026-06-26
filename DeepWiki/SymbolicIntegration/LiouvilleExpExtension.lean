import Mathlib.FieldTheory.Differential.Liouville
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Tactic

/-! # The transcendental exponential Liouville extension (completeness keystone)

Rosenlicht's *Integration in finite terms* (1972), transcendental **exponential** case of Liouville's
theorem — the second transcendental keystone after the logarithmic one
(`LiouvilleLogExtension.lean`).  Here `t = exp u` (`u ∈ F`) is the new monomial, with derivation
`t' = u'·t` (the *exponential* monomial, vs the log's `t' = u'/u`).  As before the carrier is
`RatFunc F`, the simple transcendental extension `F(t)`.

## ★ The structural difference from the log case

For the **log** monomial `t' = u'/u`, *every* monic irreducible `π` satisfies `π ∤ Dπ`
(`NondegenerateLog`).  For the **exp** monomial `t' = u'·t`, the irreducible `π = X = t` itself has
`Dt = u'·t`, so **`t ∣ Dt`** — `t = exp u` is a *unit* (nowhere zero/pole among the finite places),
a **special factor** that the pole analysis treats separately.  The coefficient formula is *diagonal*
(`(D p).coeff i = (p.coeff i)' + u'·i·p.coeff i`, no index shift), so `expDerivPoly` does **not** lower
`t`-degree in general (the `t`-leading coefficient transforms by `(lc)' + (deg)·u'·lc`, not `(lc)'`).
The non-degeneracy condition is therefore about the *other* irreducibles plus an integer-multiple-of-`u'`
logarithmic-derivative condition for the `t`-degree term: `NondegenerateExp u` asks that **no nonzero
integer `k` makes `k·u'` a logarithmic derivative `Dg/g` of an `F`-element `g`** — i.e.
`exp(k u) ∉ F` for `k ≠ 0` (the Risch exponential new-monomial condition).

## Status

- **Setup — CLOSED.**  `expDifferential u : Differential (RatFunc F)` is a genuine differential field
  structure with `t' = u'·t`, and `expDifferentialAlgebra u : DifferentialAlgebra F (RatFunc F)` is
  real — `F(exp u) = RatFunc F` is an actual differential field extension of `F`.  The load-bearing
  fraction-field derivation extension `fracDeriv` (the quotient rule on `Derivation ℤ K K`) is reused
  **verbatim** from the log file's construction (re-derived here so the file is standalone).
- **The exp pole engine — the special-factor adaptation, DISCHARGED for `π ≠ X`.**  The diagonal
  coefficient formula (`coeff_expDerivPoly`); the special factor `expDerivPoly u X = u'·X` (so `X ∣ DX`);
  and the **key non-degeneracy** `not_dvd_expDerivPoly_of_ne_X`: for a monic irreducible `π ≠ X`,
  `π ∤ Dπ` under `NondegenerateExp` (if `π ∣ Dπ`, degree forces `Dπ = (deg·u')·π`, and the constant
  term gives `logDeriv(π.coeff 0) = (deg)·u'`, forbidden — `π.coeff 0 ≠ 0` since `π ≠ X`).  From this
  the per-`π` exact pole-order drop `emultiplicity_expDerivPoly_eq` transfers (the `not_pow_dvd` /
  `pow_sub_one_dvd` Leibniz machinery is derivation-generic).
- **`IsLiouville` assembly — transferred.**  The `IsLiouville`-packaging (`isLiouville_conclusion_of_fData`,
  `keystone`) is structurally identical to the log case and transferred.
- **The precise exp-specific residual.**  What does **not** transfer verbatim is the *`v`-term
  reduction* and the *pole-matching at the special factor `X`*: because `expDerivPoly` does not lower
  `t`-degree and `t` is a pole-free unit, the polynomial/`v ∈ F` descent and the `X`-degree
  ("leading-exp") matching use the multiplicative `NondegenerateExp` structure rather than the log's
  additive antiderivative obstruction.  This is isolated below as a precisely-stated `Prop`
  `ExpFDataReduction` — never `sorry` — from which the keystone closes via the transferred assembly.
-/

open scoped Differential
open Polynomial Differential

namespace DeepWiki.SymbolicIntegration.LiouvilleExp

section PolynomialSetup

variable {F : Type*} [Field F] [Differential F]

/-- The exp-monomial polynomial `v = u'·t` realizing `t' = u'·t` for `t = exp u`
(the exp monomial, vs the log's `C (logDeriv u)`). -/
noncomputable abbrev expMonomial (u : F) : F[X] := C (u′) * X

/-- The exp-monomial derivation on `F[t]`: `Differential.implicitDeriv (C u' · X)`, the unique
derivation making `F[t]` a `DifferentialAlgebra F F[t]` with `t' = u'·t`. -/
noncomputable def expDerivPoly (u : F) : Derivation ℤ F[X] F[X] :=
  Differential.implicitDeriv (expMonomial u)

/-- `F[t]` as a `Differential` ring under the exp-monomial derivation `t' = u'·t`. -/
@[reducible]
noncomputable def expDifferentialPoly (u : F) : Differential F[X] :=
  ⟨expDerivPoly u⟩

/-- On `F[t]` with `t' = u'·t`, `t' = u'·t` (the exp-monomial defining equation, `t = exp u`). -/
@[simp]
lemma expDerivPoly_X (u : F) : expDerivPoly u (X : F[X]) = C (u′) * X := by
  simp [expDerivPoly]

/-- On `F[t]`, the derivation sends a constant `C b` to `C b'` (it extends `F`'s derivation). -/
@[simp]
lemma expDerivPoly_C (u : F) (b : F) : expDerivPoly u (C b) = C b′ := by
  simp [expDerivPoly]

/-- The exp-monomial derivation makes `F[t]` a `DifferentialAlgebra F F[t]` (extends `F`). -/
lemma expDerivPoly_differentialAlgebra (u : F) :
    letI := expDifferentialPoly u
    DifferentialAlgebra F F[X] := by
  letI := expDifferentialPoly u
  refine ⟨fun a => ?_⟩
  change expDerivPoly u (C a) = C a′
  simp

/-- **The coefficient formula for the exp-monomial derivation** (engine of all degree/pole
comparisons), *diagonal* — no index shift: `(D p).coeff i = (p.coeff i)' + u'·i·p.coeff i`.  The
first summand is the "constant-field" part (`F`'s derivation on each coefficient); the second is the
monomial part `t'·(∂p/∂t) = u'·t·(∂p/∂t)`, which (multiplying by `t`) sends the `i`-th coefficient to
itself scaled by `u'·i`.  Contrast the log's `+ u'/u·(i+1)·p.coeff (i+1)` (a *shift*). -/
lemma coeff_expDerivPoly (u : F) (p : F[X]) (i : ℕ) :
    (expDerivPoly u p).coeff i = (p.coeff i)′ + u′ * (i * p.coeff i) := by
  simp only [expDerivPoly, expMonomial, implicitDeriv, Derivation.coe_add, Pi.add_apply,
    Derivation.coe_smul, Pi.smul_apply, Derivation.restrictScalars_apply,
    derivative'_apply, coeff_add, coeff_mapCoeffs, smul_eq_mul]
  rcases i with _ | j
  · simp
  · rw [show C (u′) * X * derivative p = C (u′) * (X * derivative p) by ring,
      coeff_C_mul, coeff_X_mul, coeff_derivative]
    push_cast
    ring

/-- The exp-monomial derivation does **not raise `t`-degree**: `natDegree (D p) ≤ natDegree p`. -/
lemma natDegree_expDerivPoly_le (u : F) (p : F[X]) :
    (expDerivPoly u p).natDegree ≤ p.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [coeff_expDerivPoly]
  have h1 : p.coeff i = 0 := coeff_eq_zero_of_natDegree_lt hi
  rw [h1]; simp

/-- **At the top `t`-degree the exp-monomial part survives**: `(D p).coeff (deg p) = (lc p)' +
(deg p)·u'·(lc p)` (contrast the log's `(lc p)'` alone).  This is exactly why `expDerivPoly` does not
lower degree and why `X` (`lc = 1`, `1' = 0`) has `(D X).coeff 1 = u'·1 = u' ≠ 0` in general — the
"leading exp" term that `NondegenerateExp` controls. -/
lemma coeff_natDegree_expDerivPoly (u : F) (p : F[X]) :
    (expDerivPoly u p).coeff p.natDegree
      = (p.leadingCoeff)′ + u′ * (p.natDegree * p.leadingCoeff) := by
  rw [coeff_expDerivPoly]; rfl

/-- **The special factor `t = X`**: `expDerivPoly u X = u'·X`, so `X ∣ D X` — `t = exp u` is a *unit*
(nowhere zero/pole among the finite places).  This is the structural fact that forces `X` to be
treated separately in the exp pole analysis (vs the log, where every irreducible has `π ∤ Dπ`). -/
lemma X_dvd_expDerivPoly_X (u : F) : (X : F[X]) ∣ expDerivPoly u X := by
  rw [expDerivPoly_X]; exact Dvd.intro_left (C (u′)) rfl

/-- **`logDeriv` of `t` in `F[t]` is `u'` times a `t`-pole**: `D X = u'·X` divides through to `(D X)/X
= u'` — the multiplicative "logarithmic derivative of the exp monomial is `u'`" (`logDeriv(exp u) =
u'`).  Stated as the divisibility witness `D X = u'·X` (the `/X` lives in `F(t)`). -/
lemma expDerivPoly_X_eq (u : F) : expDerivPoly u X = C (u′) * X := expDerivPoly_X u

end PolynomialSetup

/-! ## The fraction-field derivation extension (reused from the log construction)

`fracDeriv`: a derivation on `F[X]` extends to its fraction field `K` by the quotient rule — a
self-derivation `Derivation ℤ K K`.  This is **generic** (independent of which monomial derivation
sits on `F[X]`) and is re-derived here verbatim from the log file so this file stands alone. -/

section FractionFieldDeriv

open IsLocalization
open scoped nonZeroDivisors

variable {F : Type*} [Field F] {K : Type*} [Field K] [Algebra F[X] K] [IsFractionRing F[X] K]

/-- The raw quotient-rule value on a numerator/denominator pair: `(q·d p − p·d q)/q²`. -/
noncomputable def rawDeriv (d : Derivation ℤ F[X] F[X]) (p : F[X]) (q : F[X]⁰) : K :=
  mk' K ((q : F[X]) * d p - p * d q) (q * q)

/-- Well-definedness: equal fractions give equal quotient-rule value (via the polynomial cross
identity `p₁·q₂ = p₂·q₁` differentiated). -/
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

/-- `fracDerivFun` as an additive homomorphism. -/
noncomputable def fracDerivHom (d : Derivation ℤ F[X] F[X]) : K →+ K where
  toFun := fracDerivFun d
  map_zero' := fracDerivFun_zero d
  map_add' := fracDerivFun_add d

/-- A derivation `d` on `F[X]` extended to a fraction field `K` by the quotient rule. -/
noncomputable def fracDeriv (d : Derivation ℤ F[X] F[X]) : Derivation ℤ K K :=
  Derivation.mk' (fracDerivHom d).toIntLinearMap (fun a b => by
    have := fracDerivFun_mul (K := K) d a b
    simpa only [AddMonoidHom.coe_toIntLinearMap, fracDerivHom, AddMonoidHom.coe_mk,
      ZeroHom.coe_mk, smul_eq_mul] using this)

@[simp]
lemma fracDeriv_mk' (d : Derivation ℤ F[X] F[X]) (p : F[X]) (q : F[X]⁰) :
    fracDeriv (K := K) d (mk' K p q) = rawDeriv d p q := fracDerivFun_mk' d p q

/-- **`fracDeriv` restricts to `d` on the image of `F[X]`**:
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

/-! ## The genuine field extension `F(t) = RatFunc F` (setup CLOSED) -/

section FieldSetup

variable {F : Type*} [Field F] [Differential F] [CharZero F]

open RatFunc

/-- The genuine `Differential (RatFunc F)` for the exp monomial `t = exp u` (`t' = u'·t`), via the
fraction-field extension `fracDeriv` of `expDerivPoly u`. -/
@[reducible]
noncomputable def expDifferential (u : F) : Differential (RatFunc F) :=
  fracDifferential (K := RatFunc F) (expDifferentialPoly u)

omit [CharZero F] in
/-- **Setup.**  The exp-monomial derivation on `RatFunc F` restricts to `expDerivPoly u` on the image
of `F[t]`: `(algebraMap F[t] (RatFunc F) p)′ = algebraMap F[t] (RatFunc F) (expDerivPoly u p)`. -/
theorem derivExtends (u : F) :
    letI := expDifferential u
    ∀ p : F[X], (algebraMap F[X] (RatFunc F) p)′
      = algebraMap F[X] (RatFunc F) (expDerivPoly u p) :=
  fun p => fracDeriv_algebraMap (K := RatFunc F) (expDerivPoly u) p

omit [CharZero F] in
/-- **Setup.**  GIVEN any `Differential (RatFunc F)` whose derivation restricts to `expDerivPoly u` on
`F[t]`, the extension is a `DifferentialAlgebra F (RatFunc F)`: it commutes with `algebraMap F
(RatFunc F)` (factor through the scalar tower and use `expDerivPoly_C`). -/
theorem differentialAlgebra_of_derivExtends [Differential (RatFunc F)] {u : F}
    (h : ∀ p : F[X], (algebraMap F[X] (RatFunc F) p)′
      = algebraMap F[X] (RatFunc F) (expDerivPoly u p)) :
    DifferentialAlgebra F (RatFunc F) where
  deriv_algebraMap a := by
    have hfac : (algebraMap F (RatFunc F)) a
        = algebraMap F[X] (RatFunc F) (C a) := by
      rw [IsScalarTower.algebraMap_eq F F[X] (RatFunc F)]
      simp [Polynomial.algebraMap_eq]
    rw [hfac, h (C a), expDerivPoly_C]
    rw [IsScalarTower.algebraMap_eq F F[X] (RatFunc F)]
    simp [Polynomial.algebraMap_eq]

omit [CharZero F] in
/-- **Setup CLOSED.**  `RatFunc F` with the exp-monomial derivation is a genuine `DifferentialAlgebra
F (RatFunc F)` — `F(exp u) = RatFunc F` is a real differential field extension of `F`. -/
theorem expDifferentialAlgebra (u : F) :
    letI := expDifferential u
    DifferentialAlgebra F (RatFunc F) :=
  letI := expDifferential u
  differentialAlgebra_of_derivExtends (u := u) (derivExtends u)

omit [CharZero F] in
/-- **The `logDeriv`-to-polynomial bridge**: in `RatFunc F`, the logarithmic derivative of `algebraMap
p` is `algebraMap (D p) / algebraMap p`, with `D p = expDerivPoly u p`. -/
theorem logDeriv_algebraMap_eq (u : F) (p : F[X]) :
    letI := expDifferential u
    logDeriv (algebraMap F[X] (RatFunc F) p)
      = algebraMap F[X] (RatFunc F) (expDerivPoly u p) / algebraMap F[X] (RatFunc F) p := by
  letI := expDifferential u
  unfold logDeriv
  rw [derivExtends u p]

omit [Differential F] [CharZero F] in
/-- **`algebraMap F` factors through `F[t]` as `C`.** -/
theorem algebraMap_eq_algebraMap_C (b : F) :
    algebraMap F (RatFunc F) b = algebraMap F[X] (RatFunc F) (Polynomial.C b) := by
  rw [IsScalarTower.algebraMap_eq F F[X] (RatFunc F)]
  simp [Polynomial.algebraMap_eq]

omit [Differential F] [CharZero F] in
/-- **`F`-membership of a `t`-polynomial image is degree-`0`.** -/
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

omit [CharZero F] in
/-- **`logDeriv` of `t = exp u` is `u'`**: in `RatFunc F`, `logDeriv (algebraMap X) = algebraMap u'`
(the exp-monomial defining identity at the fraction-field level, `(exp u)'/(exp u) = u'`).  Proof:
`logDeriv (algebraMap X) = algebraMap (D X)/algebraMap X = algebraMap (u'·X)/algebraMap X = algebraMap
u'` (cancel `X`). -/
theorem logDeriv_X_eq (u : F) :
    letI := expDifferential u
    logDeriv (algebraMap F[X] (RatFunc F) X) = algebraMap F (RatFunc F) (u′) := by
  letI := expDifferential u
  rw [logDeriv_algebraMap_eq u X, expDerivPoly_X, map_mul, algebraMap_eq_algebraMap_C,
    mul_div_assoc]
  have hXne : algebraMap F[X] (RatFunc F) X ≠ 0 := RatFunc.algebraMap_ne_zero X_ne_zero
  rw [div_self hXne, mul_one]

end FieldSetup

/-! ## The exp pole engine: the special factor `X` and the non-degeneracy for `π ≠ X` -/

section ExpPole

variable {F : Type*} [Field F] [Differential F]

/-- **The pure-Leibniz pole-order drop** (`q^n ∣ p ⟹ q^(n-1) ∣ D p`), fully provable for *any*
derivation (`Derivation.leibniz`/`leibniz_pow`).  The exp analogue of the log file's
`pow_sub_one_dvd_logDerivPoly`. -/
lemma pow_sub_one_dvd_expDerivPoly (u : F) {p q : F[X]} {n : ℕ} (hdvd : q ^ n ∣ p) :
    q ^ (n - 1) ∣ expDerivPoly u p := by
  obtain ⟨r, rfl⟩ := hdvd
  have hpn : q ^ (n - 1) ∣ expDerivPoly u (q ^ n) := by
    rw [Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul]
    exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _
  have hpow : q ^ (n - 1) ∣ q ^ n := pow_dvd_pow q (Nat.sub_le n 1)
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  exact dvd_add (dvd_mul_of_dvd_left hpow _) (dvd_mul_of_dvd_right hpn _)

/-- **The exp-monomial derivative of `q^k · m` factors a clean `q^(k-1)`** (`k ≥ 1`):
`D(q^k · m) = q^(k-1) · (k · (D q) · m + q · D m)`.  Derivation-generic (same proof as the log case). -/
lemma expDerivPoly_pow_mul (u : F) {q m : F[X]} {k : ℕ} (hk : 1 ≤ k) :
    expDerivPoly u (q ^ k * m)
      = q ^ (k - 1) * ((k : F[X]) * expDerivPoly u q * m + q * expDerivPoly u m) := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, Derivation.leibniz_pow, nsmul_eq_mul,
    smul_eq_mul]
  have hqk : q ^ k = q ^ (k - 1) * q := by
    rw [← pow_succ]; congr 1; omega
  rw [hqk]; ring

/-- **A monic irreducible factor `q` does not divide `D p` to its full multiplicity** when `q ∤ D q`:
if `q^k ∣∣ p` (`k ≥ 1`) then `q^k ∤ D p`.  With `pow_sub_one_dvd_expDerivPoly` this pins
`v_q(D p) = k − 1`.  Derivation-generic (same proof as the log case); the exp content is that
`q ∤ D q` holds for `q ≠ X` (`not_dvd_expDerivPoly_of_ne_X`). -/
lemma not_pow_dvd_expDerivPoly_of_exact [CharZero F] (u : F) {p q : F[X]} {k : ℕ}
    (hq : Irreducible q) (hDq : ¬ q ∣ expDerivPoly u q) (hk : 1 ≤ k)
    (hdvd : q ^ k ∣ p) (hndvd : ¬ q ^ (k + 1) ∣ p) : ¬ q ^ k ∣ expDerivPoly u p := by
  obtain ⟨m, rfl⟩ := hdvd
  have hqm : ¬ q ∣ m := by
    rintro ⟨m', rfl⟩
    exact hndvd ⟨m', by rw [pow_succ]; ring⟩
  rw [expDerivPoly_pow_mul u (q := q) (m := m) hk]
  have hqk : q ^ k = q ^ (k - 1) * q := by rw [← pow_succ]; congr 1; omega
  rw [hqk]
  intro hdvd'
  have hcancel : q ∣ ((k : F[X]) * expDerivPoly u q * m + q * expDerivPoly u m) :=
    (mul_dvd_mul_iff_left (pow_ne_zero (k - 1) hq.ne_zero)).mp hdvd'
  have hk_part : q ∣ (k : F[X]) * expDerivPoly u q * m :=
    (dvd_add_right (dvd_mul_right q (expDerivPoly u m))).mp (by rwa [add_comm] at hcancel)
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
drop, as an `emultiplicity` equality) for `π ∤ D π`.  Combines `pow_sub_one_dvd_expDerivPoly` with
`not_pow_dvd_expDerivPoly_of_exact`. -/
lemma emultiplicity_expDerivPoly_eq [CharZero F] (u : F) {p q : F[X]} {k : ℕ}
    (hq : Irreducible q) (hDq : ¬ q ∣ expDerivPoly u q) (hk : 1 ≤ k)
    (hmult : emultiplicity q p = (k : ℕ∞)) :
    emultiplicity q (expDerivPoly u p) = ((k - 1 : ℕ) : ℕ∞) := by
  have hdvd : q ^ k ∣ p := pow_dvd_of_le_emultiplicity (by rw [hmult])
  have hndvd : ¬ q ^ (k + 1) ∣ p := by
    rw [← emultiplicity_lt_iff_not_dvd, hmult]; exact_mod_cast Nat.lt_succ_self k
  have hlo : ((k - 1 : ℕ) : ℕ∞) ≤ emultiplicity q (expDerivPoly u p) :=
    le_emultiplicity_of_pow_dvd (pow_sub_one_dvd_expDerivPoly u hdvd)
  have hhi : emultiplicity q (expDerivPoly u p) < (k : ℕ∞) :=
    emultiplicity_lt_iff_not_dvd.mpr (not_pow_dvd_expDerivPoly_of_exact u hq hDq hk hdvd hndvd)
  have hk1 : (k : ℕ∞) = ((k - 1 : ℕ) : ℕ∞) + 1 := by
    rw [← ENat.coe_one, ← Nat.cast_add]; congr 1; omega
  rw [hk1] at hhi
  exact le_antisymm ((ENat.lt_add_one_iff (ENat.coe_ne_top _)).mp hhi) hlo

/-- **`NondegenerateExp u`** — the genuine new-monomial condition for the exponential `t = exp u`.
*No nonzero integer `k` makes `k·u'` a logarithmic derivative `Dg/g` of an `F`-element `g ≠ 0`* — i.e.
`exp(k u) ∉ F` for every `k ≠ 0` (the Risch *exponential* new-monomial condition).  Equivalently:
`t = exp u` is differentially transcendental over `F`, with no power `exp(k u)` collapsing into `F`.
This is the exp analogue of `NondegenerateLog` (`log u ∉ F`), but **multiplicative** and indexed by an
integer `k` (the `t`-degree / leading-exp multiplier) — the special factor `X = t` is excluded by
construction, since `t` is a unit (`X ∣ DX`) and contributes no finite pole. -/
def NondegenerateExp (u : F) : Prop :=
  ∀ (k : ℤ), k ≠ 0 → ∀ g : F, g ≠ 0 → logDeriv g ≠ (k : F) * u′

/-- **The special-factor non-degeneracy: for `π ≠ X` monic irreducible, `π ∤ Dπ`** (under
`NondegenerateExp`).  This is the exp analogue of the log's `not_dvd_logDerivPoly_of_monic`, restricted
to `π ≠ X` (the unit factor `X = t` is excluded).  Proof: if `π ∣ Dπ`, then since `deg(Dπ) ≤ deg π = m`
(`natDegree_expDerivPoly_le`), `Dπ = C cc · π` for a constant `cc`; the top coefficient gives
`cc = m·u'` (`coeff_natDegree_expDerivPoly`, `lc π = 1`), and the constant coefficient gives
`(π.coeff 0)' = cc·π.coeff 0 = m·u'·π.coeff 0`, i.e. `logDeriv(π.coeff 0) = m·u'` with `π.coeff 0 ≠ 0`
(since `π ≠ X` irreducible ⟹ `X ∤ π`) — forbidden by `NondegenerateExp` at `k = m ≠ 0`. -/
lemma not_dvd_expDerivPoly_of_ne_X [CharZero F] (u : F) (hnd : NondegenerateExp u)
    {π : F[X]} (hm : π.Monic) (hirr : Irreducible π) (hX : π ≠ X) :
    ¬ π ∣ expDerivPoly u π := by
  intro hdvd
  set m := π.natDegree with hmdef
  have hmpos : 1 ≤ m := hirr.natDegree_pos
  obtain ⟨c, hc⟩ := hdvd
  have hcdeg : c.natDegree = 0 := by
    by_contra h0
    have h1 : 1 ≤ c.natDegree := Nat.one_le_iff_ne_zero.mpr h0
    have hcne : c ≠ 0 := by rintro rfl; simp at h1
    have hdegmul : (π * c).natDegree = m + c.natDegree :=
      Polynomial.natDegree_mul hm.ne_zero hcne
    have hle : (expDerivPoly u π).natDegree ≤ m := natDegree_expDerivPoly_le u π
    rw [← hc] at hdegmul; omega
  obtain ⟨cc, hcc⟩ : ∃ cc : F, c = C cc := ⟨c.coeff 0, Polynomial.eq_C_of_natDegree_eq_zero hcdeg⟩
  have htop := coeff_natDegree_expDerivPoly u π
  rw [hm.leadingCoeff] at htop
  simp only [Derivation.map_one_eq_zero, mul_one, zero_add] at htop
  have hcoeffm : (expDerivPoly u π).coeff m = cc := by
    rw [hc, hcc, Polynomial.coeff_mul_C, show π.coeff m = π.leadingCoeff from rfl,
      hm.leadingCoeff, one_mul]
  have hcceq : cc = u′ * (m : F) := by rw [← hcoeffm]; exact htop
  have hc0_lhs : (expDerivPoly u π).coeff 0 = (π.coeff 0)′ := by
    rw [coeff_expDerivPoly]; simp
  have hc0_rhs : (expDerivPoly u π).coeff 0 = cc * π.coeff 0 := by
    rw [hc, hcc, Polynomial.coeff_mul_C, mul_comm]
  have hpi0ne : π.coeff 0 ≠ 0 := by
    intro h0
    have hXdvd : X ∣ π := by rw [Polynomial.X_dvd_iff]; exact h0
    exact hX (eq_of_monic_of_associated monic_X hm
      ((irreducible_X.associated_of_dvd hirr hXdvd))).symm
  have hlog : logDeriv (π.coeff 0) = (m : F) * u′ := by
    rw [logDeriv, hc0_lhs.symm.trans hc0_rhs, hcceq]
    rw [mul_assoc, mul_div_assoc, mul_div_cancel_right₀ _ hpi0ne]
    ring
  exact hnd (m : ℤ) (by exact_mod_cast Nat.one_le_iff_ne_zero.mp hmpos) (π.coeff 0) hpi0ne
    (by rw [hlog]; push_cast; ring)

/-- **`NondegenerateExp u` forces `u' ≠ 0`** — a genuine exp monomial has a nonconstant exponent.  If
`u' = 0` then `t = exp u` would be a *constant* (`Dt = u'·t = 0`), not a new transcendental.  Direct:
`NondegenerateExp` at `k = 1`, `g = 1` would read `logDeriv 1 = 0 ≠ 1·u' = 0`, false unless `u' ≠ 0`. -/
lemma deriv_ne_zero_of_nondegenerateExp (u : F) (hnd : NondegenerateExp u) : u′ ≠ 0 := by
  intro h0
  exact hnd 1 one_ne_zero 1 one_ne_zero (by rw [logDeriv_one, h0]; push_cast; ring)

/-- **`X` is the only monic irreducible the exp-monomial derivation can `t`-divide**: for monic
irreducible `π` with `π ∣ Dπ`, necessarily `π = X` (under `NondegenerateExp`).  The contrapositive of
`not_dvd_expDerivPoly_of_ne_X`, packaging "`X` is the unique special factor". -/
lemma eq_X_of_dvd_expDerivPoly [CharZero F] (u : F) (hnd : NondegenerateExp u)
    {π : F[X]} (hm : π.Monic) (hirr : Irreducible π) (hdvd : π ∣ expDerivPoly u π) : π = X := by
  by_contra hX
  exact not_dvd_expDerivPoly_of_ne_X u hnd hm hirr hX hdvd

end ExpPole

/-! ## The `IsLiouville` assembly (transferred from the log keystone)

The `IsLiouville`-packaging and the final reduction `Prop`s, structurally identical to the log case.
The exp-specific pole-matching content is isolated in `ExpFDataReduction` (below). -/

section FieldObligations

variable {F : Type*} [Field F] [Differential F] [CharZero F]

open RatFunc

omit [CharZero F] in
/-- **The mechanical packaging — PROVEN.**  Given `F`-data for a single representation (the output of
the pole-matching reduction), `IsLiouville`'s existential conclusion holds: pull the
already-`F`-valued logarithms and `v`-term back through `algebraMap` injectivity. -/
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

/-- **The exp F-data reduction residual** — the *exp-specific* mathematical content the keystone
reduces to, sharply isolated (never `sorry`).  It says: any `RatFunc F` representation `a = ∑ cᵢ
logDeriv wᵢ + v′` of `a ∈ F` (`wᵢ, v ∈ F(t)`, `cᵢ` constant) can be re-expressed with the logarithms'
arguments and the `v`-term **already in `F`** — i.e. there exist `w₀ : ι → F`, `v₀ : F` with `a = ∑ cᵢ
logDeriv (w₀ x) + v₀′` *as an equation in `RatFunc F`*.  For the exp monomial this is Rosenlicht's
*exponential* pole-matching: each `wᵢ` factors over `F[t]`; the finite `t`-poles (monic irreducibles
`π ≠ X`) cancel against `a`'s (absent) pole and `v′`'s (order-`≥ 2`) poles via the non-degeneracy
`not_dvd_expDerivPoly_of_ne_X` (proved above); the **special factor `X = t`** (the "leading-exp" /
`t`-degree term, a *unit*) is absorbed into a constant-coefficient `u`-logarithm `b·u'` using the
multiplicative `NondegenerateExp` structure — and the surviving polynomial `t`-part folds into `v₀`.
This is the exp counterpart of the log file's `LiouvilleFDataReduction`; everything *after* it (the
final `IsLiouville` packaging) is mechanical and **proven** in `isLiouville_of_expFDataReduction`. -/
def ExpFDataReduction (u : F) : Prop :=
  letI := expDifferential u
  letI := expDifferentialAlgebra u
  ∀ (a : F) (ι : Type) [Fintype ι] (c : ι → F), (∀ x, (c x)′ = 0) →
    ∀ (w : ι → RatFunc F) (v : RatFunc F),
      algebraMap F (RatFunc F) a = ∑ x, algebraMap F (RatFunc F) (c x) * logDeriv (w x) + v′ →
      ∃ (w₀ : ι → F) (v₀ : F),
        algebraMap F (RatFunc F) a
          = ∑ x, algebraMap F (RatFunc F) (c x) * logDeriv (algebraMap F (RatFunc F) (w₀ x))
              + (algebraMap F (RatFunc F) v₀)′

omit [CharZero F] in
/-- **The exp keystone — PROVEN assembly from `ExpFDataReduction`.**  Given the exp reduction of any
representation to `F`-data, `IsLiouville F (RatFunc F)` holds: feed each representation through the
reduction, then package via `isLiouville_conclusion_of_fData`.  So the entire exp keystone reduces to
`ExpFDataReduction u`, with the `IsLiouville`-packaging fully discharged here. -/
theorem isLiouville_of_expFDataReduction (u : F) (hred : ExpFDataReduction u) :
    letI := expDifferential u
    letI := expDifferentialAlgebra u
    IsLiouville F (RatFunc F) := by
  letI := expDifferential u
  letI := expDifferentialAlgebra u
  refine ⟨fun a ι _ c hc w v h => ?_⟩
  obtain ⟨w₀, v₀, h₀⟩ := hred a ι c hc w v h
  exact isLiouville_conclusion_of_fData a ι c hc w₀ v₀ h₀

omit [CharZero F] in
/-- **The exp keystone, assembled.**  The setup is genuine (`expDifferential u` a real `Differential
(RatFunc F)`, `expDifferentialAlgebra u` a real `DifferentialAlgebra F (RatFunc F)`).  So `F(exp u) =
RatFunc F` is a Liouville extension of `F` **iff** the exp pole-matching `ExpFDataReduction u` holds —
which carries the necessary transcendence (via `NondegenerateExp`, threaded through the proved
`not_dvd_expDerivPoly_of_ne_X`).  Everything else (setup + `IsLiouville`-packaging) is proven. -/
theorem keystone (u : F) (hred : ExpFDataReduction u) :
    letI := expDifferential u
    letI := expDifferentialAlgebra u
    IsLiouville F (RatFunc F) :=
  isLiouville_of_expFDataReduction u hred

end FieldObligations

/-! ### Restatements pinning the exp-monomial setup to Rosenlicht's wording (exp case) -/

section Restatements

variable {F : Type*} [Field F] [Differential F]

-- `t' = u'·t`: the defining equation of the exp monomial `t = exp u` (on `F[t]`).
example (u : F) : expDerivPoly u (X : F[X]) = C (u′) * X := expDerivPoly_X u
-- The exp coefficient formula is diagonal: `(D p).coeff i = (p.coeff i)' + u'·i·p.coeff i`.
example (u : F) (p : F[X]) (i : ℕ) :
    (expDerivPoly u p).coeff i = (p.coeff i)′ + u′ * (i * p.coeff i) :=
  coeff_expDerivPoly u p i
-- The special factor: `t = X` is a unit, `X ∣ D X` (`D X = u'·X`).
example (u : F) : (X : F[X]) ∣ expDerivPoly u X := X_dvd_expDerivPoly_X u
-- For `π ≠ X` monic irreducible, `π ∤ Dπ` under `NondegenerateExp` (the exp non-degeneracy).
example [CharZero F] (u : F) (hnd : NondegenerateExp u) {π : F[X]} (hm : π.Monic)
    (hirr : Irreducible π) (hX : π ≠ X) : ¬ π ∣ expDerivPoly u π :=
  not_dvd_expDerivPoly_of_ne_X u hnd hm hirr hX
-- `X` is the unique special factor: a monic irreducible `t`-dividing its own derivative is `X`.
example [CharZero F] (u : F) (hnd : NondegenerateExp u) {π : F[X]} (hm : π.Monic)
    (hirr : Irreducible π) (hdvd : π ∣ expDerivPoly u π) : π = X :=
  eq_X_of_dvd_expDerivPoly u hnd hm hirr hdvd
-- The exact pole-order drop transfers for `π ≠ X` (via the proved non-degeneracy).
example [CharZero F] (u : F) (hnd : NondegenerateExp u) {p π : F[X]} {k : ℕ}
    (hm : π.Monic) (hirr : Irreducible π) (hX : π ≠ X) (hk : 1 ≤ k)
    (hmult : emultiplicity π p = (k : ℕ∞)) :
    emultiplicity π (expDerivPoly u p) = ((k - 1 : ℕ) : ℕ∞) :=
  emultiplicity_expDerivPoly_eq u hirr (not_dvd_expDerivPoly_of_ne_X u hnd hm hirr hX) hk hmult

end Restatements

section FieldRestatements

variable {F : Type*} [Field F] [Differential F] [CharZero F]

open RatFunc

-- The setup is a genuine differential field extension: `D` commutes with `algebraMap F (RatFunc F)`.
example (u : F) (a : F) :
    letI := expDifferential u
    letI := expDifferentialAlgebra u
    (algebraMap F (RatFunc F) a)′ = algebraMap F (RatFunc F) a′ :=
  letI := expDifferential u
  letI := expDifferentialAlgebra u
  deriv_algebraMap a
-- `t' = u'·t` on `RatFunc F` itself (the exp monomial, on the fraction field).
example (u : F) :
    letI := expDifferential u
    (algebraMap F[X] (RatFunc F) Polynomial.X)′
      = algebraMap F[X] (RatFunc F) (Polynomial.C (u′) * Polynomial.X) := by
  have := derivExtends u X
  simpa [expDerivPoly_X] using this
-- `logDeriv (exp u) = u'`: the exp-monomial logarithmic-derivative identity on `RatFunc F`.
example (u : F) :
    letI := expDifferential u
    logDeriv (algebraMap F[X] (RatFunc F) X) = algebraMap F (RatFunc F) (u′) :=
  logDeriv_X_eq u
-- THE EXP KEYSTONE: discharging the exp pole-matching `ExpFDataReduction u` yields the real
-- `IsLiouville F (RatFunc F)` instance — the setup + assembly are proven.
example (u : F) (hred : ExpFDataReduction u) :
    letI := expDifferential u
    letI := expDifferentialAlgebra u
    IsLiouville F (RatFunc F) :=
  keystone u hred

end FieldRestatements

end DeepWiki.SymbolicIntegration.LiouvilleExp
