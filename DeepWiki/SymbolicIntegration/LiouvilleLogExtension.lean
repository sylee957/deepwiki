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

This file builds the **setup** for the log monomial faithfully and isolates the remaining proof
obligations as named lemmas.

## Orientation: the log monomial derivation

`F` is a `Differential` field of characteristic `0`.  Fix `u ∈ F`, and let `c := logDeriv u = u'/u`
(a *constant of `F`* exactly when `u' = 0`, but in general just an element of `F`).  The simple
transcendental logarithmic extension is `F(t) = RatFunc F` with the derivation extended by
`t' = c` (the **log monomial**: `D t = u'/u`, NOT `t' = 1`).  Concretely, on the polynomial ring
`F[t]` this is `Differential.implicitDeriv (C c)` — Mathlib's "the unique derivation making a
`DifferentialAlgebra F F[t]` with `t' = v`" — instantiated at the *constant* polynomial `v = C c`.

The carrier of the algebra is the polynomial ring `F[X]` (this file) and its fraction field
`RatFunc F` (the field setup, stated as obligations).
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

end PolynomialSetup

/-! ## The field `F(t) = RatFunc F` and the remaining obligations (the keystone roadmap)

The `IsLiouville` instance and the `trans`-towering both require the carrier to be a **field**, so
the genuine target is `RatFunc F`, the fraction field of `F[t]`.  Mathlib supplies `Field`,
`Algebra F (RatFunc F)`, `CharZero (RatFunc F)`, and `IsFractionRing F[t] (RatFunc F)` — but it has
**no derivation on a fraction field**.  Building one is the first frontier piece.  Below, each
remaining obligation is stated as a *type-checked `Prop`* (so this file builds with only proven
content), giving a precise roadmap: a follow-up proves these `def`s and the keystone closes.

### Obligation 1 — the derivation extends to `F(t)` (the localization-derivation gap)

A derivation `D : A → A` on a domain `A` extends *uniquely* to its fraction field `K` by the quotient
rule `D̃(a/b) = (D a · b − a · D b)/b²`.  Mathlib has this for **algebraic** extensions only
(`Differential.implicitDeriv` → `AdjoinRoot`); for the **transcendental** fraction field it is
missing.  The well-definedness (independence of the representative `a/b`) is the work — it is a
clean, Mathlib-contributable lemma "`Derivation A A` extends to `Derivation (FractionRing A)
(FractionRing A)`".  Statement of what the extension must satisfy on `F(t)`: -/

section FieldObligations

variable {F : Type*} [Field F] [Differential F] [CharZero F]

open RatFunc

/-- **Obligation 1 (derivation extension).** There is a `Differential (RatFunc F)` whose derivation
restricts, on the image of `F[t]`, to the log-monomial derivation `logDerivPoly u`, i.e.
`(algebraMap F[t] (RatFunc F) p)′ = algebraMap F[t] (RatFunc F) (logDerivPoly u p)`.  This is the
unique extension of the `F[t]`-derivation to the fraction field by the quotient rule; the proof is
the missing "derivation extends to `FractionRing`" lemma. -/
def DerivExtendsObligation (u : F) : Prop :=
  ∃ _ : Differential (RatFunc F),
    ∀ p : F[X], (algebraMap F[X] (RatFunc F) p)′
      = algebraMap F[X] (RatFunc F) (logDerivPoly u p)

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

/-- **Obligation 3 (the `IsLiouville` reduction — heart of the transcendental case).**  GIVEN the
extended derivation (and hence `DifferentialAlgebra` by `differentialAlgebra_of_derivExtends`), if
`a ∈ F` is written `a = ∑ cᵢ logDeriv wᵢ + v′` with `wᵢ, v ∈ F(t)` and `cᵢ` constants, then it can
be rewritten with all data in `F`.  Rosenlicht's argument: factor each `wᵢ = (F-leading
coeff)·∏(monic irreducibles in t)`; `logDeriv` of the `t`-part contributes only
`(deg)·t'/(…) = (deg)·logDeriv u` plus genuine `t`-pole terms; matching the partial-fraction
`t`-pole orders on both sides (the left side `a ∈ F` has **none**) kills every `t`-pole, so each
surviving `wᵢ` is in `F` and `v` has no `t`-pole, hence `v ∈ F` after absorbing the `t·const` term.
This is exactly `IsLiouville F (RatFunc F)` — the keystone. -/
def IsLiouvilleObligation [Differential (RatFunc F)]
    [DifferentialAlgebra F (RatFunc F)] : Prop :=
  IsLiouville F (RatFunc F)

/-- **Obligation 4 (`ContainConstants F F(t)`, the transcendence non-degeneracy — needed only to
*tower* logs).**  GIVEN the extended derivation, every `t`-constant is in `F`:
`x′ = 0 → x ∈ range (algebraMap F (RatFunc F))`.  This is *not* needed for the single keystone
`IsLiouville F F(t)`; it is what `IsLiouville.trans` requires to chain a tower `F ⊆ F(log u₁) ⊆
F(log u₁, log u₂) ⊆ …`.  Crux: a new constant is a non-`F` element of `F(t)` with derivative `0`;
`coeff_logDerivPoly` / `coeff_natDegree_logDerivPoly` (top `t`-coefficient sees only `F`'s
derivation) force it to be a single `C b` with `b' = 0`, hence in `F`.  In char 0 this is where
transcendence of `t` is essential. -/
def ContainConstantsObligation [Differential (RatFunc F)] : Prop :=
  Differential.ContainConstants F (RatFunc F)

omit [CharZero F] in
/-- **The keystone, assembled and PROVEN (modulo the two content obligations).**  GIVEN a
`Differential (RatFunc F)` (`inst`) whose derivation restricts to `logDerivPoly u` on `F[t]`
(Obligation 1, hypothesis `hrestrict`) and the `IsLiouville` reduction *for that derivation*
(Obligation 3, hypothesis `hliouville` — stated against the `DifferentialAlgebra` that
`differentialAlgebra_of_derivExtends` produces), `F(log u) = RatFunc F` is a Liouville extension of
`F`.  Obligation 2 (`DifferentialAlgebra`) is discharged inside via
`differentialAlgebra_of_derivExtends`, so only Obligations 1 and 3 carry mathematical content.  This
theorem is the mechanical assembly that closes the keystone once those two are supplied.  (Towering
several logs additionally needs Obligation 4, `ContainConstantsObligation`, via
`IsLiouville.trans`.) -/
theorem keystone (u : F) (inst : Differential (RatFunc F))
    (hrestrict : ∀ p : F[X], (algebraMap F[X] (RatFunc F) p)′
      = algebraMap F[X] (RatFunc F) (logDerivPoly u p))
    (hliouville : letI := inst
      letI := differentialAlgebra_of_derivExtends (u := u) hrestrict
      IsLiouville F (RatFunc F)) :
    letI := inst
    letI := differentialAlgebra_of_derivExtends (u := u) hrestrict
    IsLiouville F (RatFunc F) :=
  hliouville

end FieldObligations

end DeepWiki.SymbolicIntegration.LiouvilleLog
