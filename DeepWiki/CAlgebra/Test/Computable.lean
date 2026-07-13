import DeepWiki.CAlgebra.Poly.Euclid
import DeepWiki.CAlgebra.Poly.Derivative
import DeepWiki.CAlgebra.Frac.Basic

/-! # Computability guards

Each declaration below is an **operation given as a function value** — no concrete inputs. It
elaborates only if that operation has a computable code path; Lean's compiler rejects a
non-`noncomputable` definition depending on `noncomputable` data (`dependsOnNoncomputable`). So these
are a build-checked proof that the intended-computable API is on the computable path: if any op
regresses, the gate breaks here.

They are `private` — witnesses, not API — so nothing outside this file can reference them and doc-gen
omits them; privacy is visibility-only, so the computability check still fires. Stated **generically
over the coefficient ring `R`** and at the **function level** because computability is a property of
the operation, not of any input (not brittle against literals), and a generic `R` instantiates to
`ℚ`, tower carriers like `DensePoly ℚ`, etc., so one guard covers every computable-instance carrier.

These are `def`s, not `native_decide` — a `def` compiling is codegen, not a proof axiom, so they add
nothing to any theorem's trusted base (and are unaffected by the `@[csimp]`/`native_decide`
axiom-tracking issue, leanprover/lean4#7463). Correctness of the *output* is a separate matter, handled
by the `toX_*` bridge squares. -/

namespace DeepWiki.CAlgebra.Test.Computable

section
variable {R : Type u}

/-! ### Ring operations (any `CommRing` coefficient) -/

/-- Dense polynomial multiplication is computable. -/
private def mul [CommRing R] [DecidableEq R] : DensePoly R → DensePoly R → DensePoly R := (· * ·)
/-- Dense polynomial addition is computable. -/
private def add [CommRing R] [DecidableEq R] : DensePoly R → DensePoly R → DensePoly R := (· + ·)
/-- Dense polynomial subtraction is computable. -/
private def sub [CommRing R] [DecidableEq R] : DensePoly R → DensePoly R → DensePoly R := (· - ·)
/-- Dense polynomial negation is computable. -/
private def neg [CommRing R] [DecidableEq R] : DensePoly R → DensePoly R := (- ·)
/-- Natural-number power is computable (via the hand-built computable `CommRing`). -/
private def pow [CommRing R] [DecidableEq R] : DensePoly R → ℕ → DensePoly R := (· ^ ·)
/-- `ℕ`-scalar multiplication is computable. -/
private def nsmul [CommRing R] [DecidableEq R] : ℕ → DensePoly R → DensePoly R := (· • ·)
/-- Natural-number cast is computable. -/
private def natCast [CommRing R] [DecidableEq R] : ℕ → DensePoly R := Nat.cast
/-- The formal derivative is computable. -/
private def deriv [CommRing R] [DecidableEq R] : DensePoly R → DensePoly R := DensePoly.deriv

/-! ### Euclidean operations (any `Field` coefficient) -/

/-- Euclidean division is computable. -/
private def divMod [Field R] [DecidableEq R] : DensePoly R → DensePoly R → DensePoly R × DensePoly R :=
  DensePoly.divMod
/-- Polynomial gcd is computable. -/
private def gcd [Field R] [DecidableEq R] : DensePoly R → DensePoly R → DensePoly R := DensePoly.gcd

/-! ### Rational-function carrier operations -/

/-- Rational-function multiplication (carrier) is computable. -/
private def fracMul [CommRing R] [DecidableEq R] : DenseFrac R → DenseFrac R → DenseFrac R := (· * ·)
/-- Rational-function addition (carrier) is computable. -/
private def fracAdd [CommRing R] [DecidableEq R] : DenseFrac R → DenseFrac R → DenseFrac R := (· + ·)

end

end DeepWiki.CAlgebra.Test.Computable
