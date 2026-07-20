import DeepWiki.CAlgebra.Poly.Euclid
import DeepWiki.CAlgebra.Poly.DivisionMonic
import DeepWiki.CAlgebra.Poly.DivisionPseudo
import DeepWiki.CAlgebra.Gcd
import DeepWiki.CAlgebra.Poly.Derivative
import DeepWiki.CAlgebra.Frac.Basic
import DeepWiki.CAlgebra.Frac.Field

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
/-- Pseudo-division is computable over any `CommRing` coefficient (no `Field` needed). -/
private def pseudoDivMod [CommRing R] [DecidableEq R] :
    DensePoly R → DensePoly R → DensePoly R × DensePoly R := DensePoly.pseudoDivMod

/-! ### Euclidean operations (any `Field` coefficient) -/

/-- Division by a monic divisor is computable over any nontrivial `CommRing` (no field ops). -/
private def divModMonic [CommRing R] [DecidableEq R] [Nontrivial R] :
    DensePoly R → DensePolyMonic R → DensePoly R × DensePoly R := DensePoly.divModMonic

/-- Euclidean division is computable. -/
private def divMod [Field R] [DecidableEq R] : DensePoly R → DensePoly R → DensePoly R × DensePoly R :=
  DensePoly.divMod
/-- The dispatching class gcd is computable (through whichever instance resolves). -/
private def classGcd [Field R] [DecidableEq R] [DensePolyGcd R] :
    DensePoly R → DensePoly R → DensePoly R := DensePolyGcd.gcd
/-- The subresultant-PRS gcd is computable. -/
private def gcdSubresultant [Field R] [DecidableEq R] : DensePoly R → DensePoly R → DensePoly R :=
  DensePoly.gcdSubresultant
/-- Mathlib's generic `EuclideanDomain.gcd` runs computably on the dense carrier (through the
computable `EuclideanDomain (DensePoly R)` instance). -/
private def euclideanDomainGcd [Field R] [DecidableEq R] :
    DensePoly R → DensePoly R → DensePoly R := EuclideanDomain.gcd

/-! ### Rational-function carrier operations -/

/-- Fraction canonicalization (gcd-reduce + monic denominator) is computable. -/
private def fracNormalize [Field R] [DecidableEq R] :
    DensePoly R → DensePoly R → DenseFrac R := DenseFrac.normalize
/-- Canonical-fraction multiplication (renormalizing) is computable. -/
private def fracMul [Field R] [DecidableEq R] : DenseFrac R → DenseFrac R → DenseFrac R := (· * ·)
/-- Canonical-fraction addition (renormalizing) is computable. -/
private def fracAdd [Field R] [DecidableEq R] : DenseFrac R → DenseFrac R → DenseFrac R := (· + ·)
/-- Canonical-fraction inversion is computable. -/
private def fracInv [Field R] [DecidableEq R] : DenseFrac R → DenseFrac R := (·⁻¹)
/-- Semantic equality of rational functions is decidable on the canonical carrier. -/
private def fracEq [Field R] [DecidableEq R] : DenseFrac R → DenseFrac R → Bool :=
  fun a b => decide (a = b)

end

end DeepWiki.CAlgebra.Test.Computable
