import DeepWiki.CAlgebra.Poly.Euclid
import DeepWiki.CAlgebra.Poly.Derivative
import DeepWiki.CAlgebra.Frac.Additive

/-! # Computability guards

Each `def` below elaborates ONLY if its operation has a computable code path — Lean's compiler
rejects a non-`noncomputable` definition that depends on `noncomputable` data (the
`dependsOnNoncomputable` error). So these are a **build-checked proof** that the intended-computable
API (`DensePoly`/`DenseFrac` arithmetic, Euclidean division, gcd, derivative) really is on the
computable path: if any of them regresses to noncomputable, the gate breaks here.

This is not `native_decide` — a `def` compiling is codegen, not a proof axiom, so it adds nothing to
any theorem's trusted base. Since the `CommRing (DensePoly R)` instance is now hand-built and fully
computable (not `Function.Injective.commRing`), `^`/`•`/`natCast` are on the computable path too and
are guarded here. -/

namespace DeepWiki.CAlgebra.ComputableGuard

open DeepWiki.CAlgebra DensePoly

/-- Dense polynomial multiplication is computable. -/
def poly_mul : List ℚ := ((ofList [1, 2, 3] : DensePoly ℚ) * ofList [1, 1]).coeffs
/-- Dense polynomial addition is computable. -/
def poly_add : List ℚ := ((ofList [1, 2] : DensePoly ℚ) + ofList [0, 0, 5]).coeffs
/-- Dense polynomial subtraction is computable. -/
def poly_sub : List ℚ := ((ofList [1, 2] : DensePoly ℚ) - ofList [1, 1]).coeffs
/-- Euclidean division is computable. -/
def poly_divMod : List ℚ × List ℚ :=
  let r := DensePoly.divMod (ofList [-1, 0, 1] : DensePoly ℚ) (ofList [-1, 1])
  (r.1.coeffs, r.2.coeffs)
/-- Polynomial gcd is computable. -/
def poly_gcd : List ℚ := (DensePoly.gcd (ofList [-1, 0, 1] : DensePoly ℚ) (ofList [-1, 1])).coeffs
/-- The formal derivative is computable. -/
def poly_deriv : List ℚ := (DensePoly.deriv (ofList [5, 4, 3] : DensePoly ℚ)).coeffs
/-- Natural-number power is computable (via the hand-built computable `CommRing`). -/
def poly_pow : List ℚ := ((ofList [1, 1] : DensePoly ℚ) ^ 3).coeffs
/-- Natural-number cast is computable. -/
def poly_natCast : List ℚ := ((7 : DensePoly ℚ)).coeffs
/-- `ℕ`-scalar multiplication is computable. -/
def poly_nsmul : List ℚ := ((3 : ℕ) • (ofList [1, 2] : DensePoly ℚ)).coeffs

/-- Rational-function multiplication (carrier) is computable. -/
def frac_mul : List ℚ :=
  (((⟨ofList [1], ofList [1, 1]⟩ : DenseFrac ℚ) * ⟨ofList [1], ofList [0, 1]⟩).num).coeffs
/-- Rational-function addition (carrier) is computable. -/
def frac_add : List ℚ :=
  (((⟨ofList [1], ofList [1, 1]⟩ : DenseFrac ℚ) + ⟨ofList [1], ofList [0, 1]⟩).num).coeffs

end DeepWiki.CAlgebra.ComputableGuard
