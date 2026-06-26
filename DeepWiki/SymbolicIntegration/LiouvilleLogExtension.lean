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

end PolynomialSetup

end DeepWiki.SymbolicIntegration.LiouvilleLog
