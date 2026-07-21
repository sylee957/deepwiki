import DeepWiki.CAlgebra.Poly.DivisionPseudo
import DeepWiki.CAlgebra.Gcd.Dense

/-! # The primitive pseudo-remainder sequence over `K[z]`

Bivariate `K[z][x]` machinery (`x` outermost): constant lifts, `z`-contents, and the
primitive pseudo-remainder sequence — pseudo-divide, strip the `z`-content, recurse. Its
elements differ from the true subresultants only by `z`-contents, which specialize to
constants; the Lazard–Rioboo–Trager log arguments are read off this sequence. -/

namespace DeepWiki.CAlgebra

universe u

namespace DensePoly

variable {R : Type u} [Field R] [DecidableEq R] [DensePolyGcd R]

/-- Lift an `x`-polynomial into `K[z][x]`: coefficients become `z`-constants. -/
def liftX (p : DensePoly R) : DensePoly (DensePoly R) := ofList (p.coeffs.map C)

/-- The indeterminate `z`, as a constant of `K[z][x]`. -/
def zC : DensePoly (DensePoly R) := C (ofList [0, 1])

/-- The `z`-content: the gcd of the `x`-coefficients. -/
def zContent (p : DensePoly (DensePoly R)) : DensePoly R :=
  p.coeffs.foldr (fun c acc => DensePolyGcd.gcd c acc) 0

/-- The `z`-primitive part: divide each `x`-coefficient by the content. -/
def zPrimitive (p : DensePoly (DensePoly R)) : DensePoly (DensePoly R) :=
  ofList (p.coeffs.map fun c => div c (zContent p))

/-- The primitive pseudo-remainder sequence in `x` over `K[z]`, starting from the second
input: pseudo-divide, take the `z`-primitive part, recurse. -/
def primPRS : ℕ → DensePoly (DensePoly R) → DensePoly (DensePoly R) →
    List (DensePoly (DensePoly R))
  | 0, _, _ => []
  | fuel + 1, A, B =>
      if B = 0 then []
      else B :: primPRS fuel B (zPrimitive (pseudoMod A B))

end DensePoly

end DeepWiki.CAlgebra
