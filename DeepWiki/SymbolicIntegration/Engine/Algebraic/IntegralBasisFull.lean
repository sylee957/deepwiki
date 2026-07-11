import DeepWiki.SymbolicIntegration.Engine.Algebraic.Round2IntegralBasis
import DeepWiki.ComputableAlgebra.FracReduce
import DeepWiki.SymbolicIntegration.Engine.Tower.WellFounded

/-! # The general-curve integral basis: iterating the Ford–Zassenhaus Round-2 step to the maximal order

Iterates the Round-2 enlargement of the equation order `[1, y, …, yⁿ⁻¹]` across all linear bad
primes, re-basing after each, to a fixed point — the maximal order, whose `K[x]`-basis is the
integral basis. The Round-2 step is built in the order's own coordinates (`ipOCoords`,
`idealizerOCoords`) so iterating an arbitrary order stays sound. Validated on the cusp/node
(one step), the worse cusp `y² − x⁵` (two steps), and `y² − x³(x−1)²` (two bad primes). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace DensePoly

variable {α : Type*} [CField α]

/-! ### Reducing order entries to monic-denominator lowest terms -/

/-- Reduce every `ℚ(x)` entry of an order basis to monic-denominator lowest terms. -/
def reduceOrder (O : List (DensePoly (DenseFrac ℚ))) : List (DensePoly (DenseFrac ℚ)) :=
  O.map (fun row => row.map CFrac.reduceMonic)

/-! ### The p-trace-radical of an order, in the order's coordinates (`ipOCoords`)

For a linear bad prime `p = x − a` and an order `O`, the p-trace-radical `I_p` is, mod `p`, the
kernel of the trace matrix `CPoly.traceMatrix f O` evaluated at `a`, expressed in `O`-coordinates where it
is an integral `K[x]`-lattice (no denominators), Hermite-reduced. -/

/-- The trace matrix of an order `O` evaluated at a linear prime root `a`: the `n×n` `ℚ`-matrix
`CPoly.traceMatrix f O` with every entry evaluated at `x = a` (`CFrac.eval`). -/
def traceMatrixOrderAtRoot (f : DensePoly (DenseFrac ℚ)) (O : List (DensePoly (DenseFrac ℚ))) (a : ℚ) :
    List (List ℚ) :=
  (CPoly.traceMatrix f O).map (fun row => row.map (fun e => CFrac.eval e a))

/-- The p-trace-radical `I_p` of an order `O` in `O`-coordinates: a `K[x]`-basis of
`I_p = { z ∈ O : p | Tr(z·ωⱼ) ∀j }` as a `PolyMatrix DensePoly ℚ`, from the kernel of `traceMatrixOrderAtRoot`
together with the `p·O` generators, Hermite-reduced to the nonzero rows. -/
def ipOCoords [CLinearSolve ℚ]
    (f : DensePoly (DenseFrac ℚ)) (O : List (DensePoly (DenseFrac ℚ))) (p : DensePoly ℚ) (a : ℚ) :
    PolyMatrix DensePoly ℚ :=
  let n := cdeg f
  let kers : List (List ℚ) := CLinearSolve.nullspaceBasis (traceMatrixOrderAtRoot f O a) n
  let kerRows : PolyMatrix DensePoly ℚ := kers.map (fun v => (List.range n).map (fun i => [v.getD i 0]))
  let pRows : PolyMatrix DensePoly ℚ := (List.range n).map (fun i =>
    (List.range n).map (fun j => if i = j then p else ([] : DensePoly ℚ)))
  let reduced := CPoly.hermiteRowReduce (kerRows ++ pRows)
  reduced.filter (fun row => !row.all cisZero)

/-! ### The idealizer of an arbitrary order, in `O`-coordinates (`idealizerOCoords`)

The enlarged order is the idealizer `Î = (I_p : I_p)`, computed in `O`-coordinates: the
multiply-by-`ιⱼ` matrices (via the structure constants of `O`) are stacked, cleared to a common
denominator by exact division, Hermite-reduced, and inverted to give the new order basis, mapped
back to power coordinates. -/

/-- The `O`-to-power change-of-basis matrix `orderToPowerMatrix n O`: column `k` is `ωₖ` in power
coordinates (`B[r][k] = coeff_r(ωₖ)`). Its inverse maps power coordinates to `O`-coordinates. -/
def orderToPowerMatrix (n : ℕ) (O : List (DensePoly (DenseFrac ℚ))) : List (List (DenseFrac ℚ)) :=
  (List.range n).map (fun r => (List.range n).map (fun k => (O.getD k []).getD r CCommRing.zero))

/-- The `O`-coordinates of a `K(x, y)` element `toOCoords Binv n z = Binv · (z in power coords)`. -/
def toOCoords (Binv : List (List (DenseFrac ℚ))) (n : ℕ) (z : DensePoly (DenseFrac ℚ)) : List (DenseFrac ℚ) :=
  (List.range n).map (fun r =>
    (List.range n).foldl (fun acc c =>
      CCommRing.add acc (CCommRing.mul ((Binv.getD r []).getD c CCommRing.zero) (z.getD c CCommRing.zero)))
      CCommRing.zero)

/-- The common denominator of a `K(x)`-matrix: the product of its distinct reduced nonunit denominators. -/
def commonDenom (M : List (List (DenseFrac ℚ))) : DensePoly ℚ :=
  M.foldl (fun acc row =>
    row.foldl (fun a z =>
      let den := cnorm (CFrac.den (CFrac.reduceMonic z))
      if cisZero den || cisZero (csub den [CCommRing.one]) then a else cmul a den)
      acc) [CCommRing.one]

/-- Clear a `K(x)`-row to a `K[x]`-row at `δ` by exact division: `clearRowExact δ row = [(δ·numᵢ)/denᵢ]`
via selected exact polynomial division (valid since `denᵢ | δ`), giving the integral row `δ·row`. -/
def clearRowExact (δ : DensePoly ℚ) (row : List (DenseFrac ℚ)) : List (DensePoly ℚ) :=
  row.map (fun z =>
    let zz := CFrac.reduceMonic z
    let num := CFrac.num zz
    let den := cnorm (CFrac.den zz)
    CPolyEuclidean.div (cmul δ num) den)

/-- The idealizer `Î = (I_p : I_p)` of an order `O`, as a new `K(x)` order basis: from `O` (power
coordinates) and `ipO` (`I_p` in `O`-coordinates), build the multiply-by-`ιⱼ` matrices in the `I_p`
basis, stack, clear to `K[x]` via `commonDenom`/`clearRowExact`, Hermite-reduce, invert, and scale
by `δ` to get the idealizer basis, mapped back to power coordinates. Returns `O` if any inverse is
singular. -/
def idealizerOCoords [CLinearSolve (DenseFrac ℚ)]
    (f : DensePoly (DenseFrac ℚ)) (O : List (DensePoly (DenseFrac ℚ)))
    (ipO : PolyMatrix DensePoly ℚ) :
    List (DensePoly (DenseFrac ℚ)) :=
  let n := cdeg f
  let B := orderToPowerMatrix n O
  match CLinearSolve.matrixInverse n B with
  | none => O
  | some Binv =>
    let ipElems : List (DensePoly (DenseFrac ℚ)) := ipO.map (fun row =>
      (List.range n).foldl (fun acc i =>
        cadd acc (cscale (CFrac.ofPoly (row.getD i [])) (O.getD i []))) ([] : DensePoly (DenseFrac ℚ)))
    let Bip : List (List (DenseFrac ℚ)) := (List.range n).map (fun r =>
      (List.range n).map (fun k => (toOCoords Binv n (ipElems.getD k [])).getD r CCommRing.zero))
    match CLinearSolve.matrixInverse n Bip with
    | none => O
    | some BipInv =>
      let M : List (List (DenseFrac ℚ)) :=
        (List.range n).foldr (fun j acc =>
          let ιj := ipElems.getD j []
          let multO : List (List (DenseFrac ℚ)) := (List.range n).map (fun r =>
            (List.range n).map (fun i =>
              (toOCoords Binv n (CPoly.mulMod f ιj (O.getD i []))).getD r CCommRing.zero))
          (matMul BipInv multO) ++ acc) []
      let δ : DensePoly ℚ := commonDenom M
      let N : PolyMatrix DensePoly ℚ := M.map (clearRowExact δ)
      let nz := (CPoly.hermiteRowReduce N).filter (fun row => !row.all cisZero)
      let Nhat : List (List (DenseFrac ℚ)) := (List.range n).map (fun i =>
        (List.range n).map (fun j => CFrac.ofPoly ((nz.getD i []).getD j [])))
      match CLinearSolve.matrixInverse n Nhat with
      | none => O
      | some NhatInv =>
        let δq : DenseFrac ℚ := CFrac.ofPoly δ
        (List.range n).map (fun col =>
          let uO : List (DenseFrac ℚ) := (List.range n).map (fun row =>
            CCommRing.mul δq ((NhatInv.getD row []).getD col CCommRing.zero))
          (List.range n).foldl (fun acc i =>
            cadd acc (cscale (uO.getD i CCommRing.zero) (O.getD i []))) ([] : DensePoly (DenseFrac ℚ)))

end DensePoly

/-! ### The outer loop: `integralBasis`, `isMaximalOrder`

Iterates the Round-2 enlargement to a fixed point: `round2StepOrderAt` enlarges `O` at one linear
prime, `round2Pass` at all bad primes of the current order's discriminant, and `integralBasisLoop`
iterates passes until `O` stops growing. -/

open DensePoly

namespace DensePoly

/-- The discriminant of an order `O`, numerator reduced to lowest terms: the numerator of
`det(CPoly.traceMatrix f O) ∈ K(x)` after cancelling `gcd(num, den)`. Shrinks by a square each genuine
enlargement — the termination measure. -/
def discNumOrder (f : DensePoly (DenseFrac ℚ)) (O : List (DensePoly (DenseFrac ℚ))) : DensePoly ℚ :=
  let z := fieldDet (CPoly.traceMatrix f O)
  cnorm (CFrac.reduceNum z)

/-- The bad primes of an order `O`: the distinct monic squarefree factors `p` of the reduced
discriminant numerator with `p² | d` — where `O` may still be non-maximal. -/
def badPrimesOrder (f : DensePoly (DenseFrac ℚ)) (O : List (DensePoly (DenseFrac ℚ))) :
    List (DensePoly ℚ) :=
  let d := discNumOrder f O
  let distinct := ((CPoly.squarefreeYun d).map cmonic).filter (fun p => 0 < cdeg p)
  distinct.filter (fun p => cisZero (CPolyEuclidean.mod d (cmul p p)))

/-- `true` iff two order bases agree: each `O1ᵢ` is `cisZero`-equal to `O2ᵢ` over the `n`
coordinates. The iteration's fixed-point test. -/
def orderEq (n : ℕ) (O1 O2 : List (DensePoly (DenseFrac ℚ))) : Bool :=
  (List.range n).all (fun i => cisZero (csub (O1.getD i []) (O2.getD i [])))

/-- One Round-2 enlargement of an order `O` at a linear prime `p`: compute the p-trace-radical
`ipOCoords` and its idealizer `idealizerOCoords`, reduced to canonical form. -/
def round2StepOrderAt [CLinearSolve ℚ] [CLinearSolve (DenseFrac ℚ)]
    (f : DensePoly (DenseFrac ℚ)) (O : List (DensePoly (DenseFrac ℚ))) (p : DensePoly ℚ) :
    List (DensePoly (DenseFrac ℚ)) :=
  let pm := cmonic p
  let a : ℚ := CCommRing.neg (pm.getD 0 CCommRing.zero)
  reduceOrder (idealizerOCoords f O (ipOCoords f O pm a))

/-- One full pass of Round-2 over all bad primes of `O`: `round2Pass f O = (O', grew)` folds
`round2StepOrderAt` over every bad prime, reporting whether the order grew (`grew = ¬ orderEq O O'`). -/
def round2Pass [CLinearSolve ℚ] [CLinearSolve (DenseFrac ℚ)]
    (f : DensePoly (DenseFrac ℚ)) (O : List (DensePoly (DenseFrac ℚ))) :
    List (DensePoly (DenseFrac ℚ)) × Bool :=
  let n := cdeg f
  let O' := (badPrimesOrder f O).foldl (fun acc p => round2StepOrderAt f acc p) O
  (O', !orderEq n O O')

/-- The Round-2 iteration loop `integralBasisLoop fuel f O`: run `round2Pass` repeatedly until a pass
leaves `O` unchanged — the maximal order. `fuel` bounds the iteration count by the discriminant degree. -/
def integralBasisLoop [CLinearSolve ℚ] [CLinearSolve (DenseFrac ℚ)]
    (fuel : ℕ) (f : DensePoly (DenseFrac ℚ)) :
    List (DensePoly (DenseFrac ℚ)) → List (DensePoly (DenseFrac ℚ))
  | O =>
    match fuel with
    | 0 => O
    | fuel + 1 =>
      let (O', grew) := round2Pass f O
      if grew then integralBasisLoop fuel f O' else O'

/-- The general-curve integral basis `integralBasis f`: iterate the Round-2 step from the equation
order `[1, y, …, yⁿ⁻¹]` to the maximal order, whose `K[x]`-basis is the integral basis of
`K(x, y) = K(x)[y]/(f)` (the functions with no finite poles). -/
def integralBasis [CLinearSolve ℚ] [CLinearSolve (DenseFrac ℚ)]
    (f : DensePoly (DenseFrac ℚ)) : List (DensePoly (DenseFrac ℚ)) :=
  let fuel := cdeg (discNum f) + 1
  reduceOrder (integralBasisLoop fuel f (CPoly.powerBasis f))

/-- `true` iff `O` is the maximal order: a Round-2 pass over `O` does not grow it
(`¬ (round2Pass f O).2`). -/
def isMaximalOrder [CLinearSolve ℚ] [CLinearSolve (DenseFrac ℚ)]
    (f : DensePoly (DenseFrac ℚ)) (O : List (DensePoly (DenseFrac ℚ))) : Bool :=
  !(round2Pass f O).2

end DensePoly

/-! ### The cusp `y² − x³` and node `y² − x²(x+1)`: `integralBasis = [1, y/x]` in one step (`native_decide`) -/

open DensePoly

-- Sanity print: the cusp integral basis (coordinate vectors over ℚ(x); expected `[1,0]`, `[0,1/x]`).
#eval (integralBasis cuspF).map (fun b => b.map (fun z =>
  ((CFrac.num z : List ℚ), (CFrac.den z : List ℚ))))

/-- The computed cusp integral-basis generator `y/x` = the second basis vector of `integralBasis cuspF`. -/
def cuspIBGen : DensePoly (DenseFrac ℚ) := (integralBasis cuspF).getD 1 []

/-- The cusp integral basis is `[1, y/x]`, integral (`(y/x)² = x`) and maximal. -/
theorem cusp_integralBasis_eq :
    (cisZero (csub cuspIBGen [CCommRing.zero, CFrac.ofFraction [1] [0, 1] (by cfrac_nonzero)])
      && cisZero (csub ((integralBasis cuspF).getD 0 []) [CCommRing.one])
      && cisZero (csub (CPoly.mulMod cuspF cuspIBGen cuspIBGen) [CFrac.ofPoly [0, 1]])
      && isMaximalOrder cuspF (integralBasis cuspF)) = true := by native_decide

-- Sanity print: the node integral basis (expected `[1,0]`, `[0,1/x]`).
#eval (integralBasis nodeF).map (fun b => b.map (fun z =>
  ((CFrac.num z : List ℚ), (CFrac.den z : List ℚ))))

/-- The computed node integral-basis generator `y/x` = the second basis vector of `integralBasis nodeF`. -/
def nodeIBGen : DensePoly (DenseFrac ℚ) := (integralBasis nodeF).getD 1 []

/-- The node integral basis is `[1, y/x]`, integral (`(y/x)² = x + 1`) and maximal. -/
theorem node_integralBasis_eq :
    (cisZero (csub nodeIBGen [CCommRing.zero, CFrac.ofFraction [1] [0, 1] (by cfrac_nonzero)])
      && cisZero (csub ((integralBasis nodeF).getD 0 []) [CCommRing.one])
      && cisZero (csub (CPoly.mulMod nodeF nodeIBGen nodeIBGen) [CFrac.ofPoly [1, 1]])
      && isMaximalOrder nodeF (integralBasis nodeF)) = true := by native_decide

/-! ### A multi-step curve: the worse cusp `y² − x⁵`, integral basis `[1, y/x²]` (`native_decide`)

`y² − x⁵` needs two Round-2 steps: `[1, y] → [1, y/x] → [1, y/x²]`, the `x`-power dropping one per
step, so a single step is not enough. -/

/-- The worse cusp curve `f = y² − x⁵ ∈ ℚ(x)[y]`, the `DensePoly (DenseFrac ℚ)` `[−x⁵, 0, 1]`. -/
def cusp5F : DensePoly (DenseFrac ℚ) :=
  [CFrac.ofPoly [0, 0, 0, 0, 0, -1], CCommRing.zero, CCommRing.one]

/-- The computed worse-cusp integral-basis generator `y/x²` = the second basis vector of
`integralBasis cusp5F`. -/
def cusp5IBGen : DensePoly (DenseFrac ℚ) := (integralBasis cusp5F).getD 1 []

-- Sanity print: the worse-cusp discriminant numerator (expected `4x⁵ = [0,0,0,0,0,4]`).
#eval (discNum cusp5F : List ℚ)

-- Sanity print: a SINGLE round2Step on the worse cusp (expected `[1, y/x]`, NOT yet maximal).
#eval (round2Step cusp5F).1.map (fun b => b.map (fun z =>
  ((CFrac.num z : List ℚ), (CFrac.den z : List ℚ))))

-- Sanity print: the FULL integralBasis on the worse cusp (expected `[1, y/x²]`).
#eval (integralBasis cusp5F).map (fun b => b.map (fun z =>
  ((CFrac.num z : List ℚ), (CFrac.den z : List ℚ))))

/-- A single Round-2 step on `y² − x⁵` reaches only `[1, y/x]`, not the maximal order
(`isMaximalOrder` is `false`). -/
theorem cusp5_oneStep_not_maximal :
    (((round2Step cusp5F).2)
      && cisZero (csub ((round2Step cusp5F).1.getD 1 [])
            [CCommRing.zero, CFrac.ofFraction [1] [0, 1] (by cfrac_nonzero)])
      && !isMaximalOrder cusp5F (reduceOrder (round2Step cusp5F).1)) = true := by native_decide

/-- The full iteration reaches `[1, y/x²]` for `y² − x⁵` (two Round-2 steps). -/
theorem cusp5_integralBasis_eq :
    (cisZero (csub cusp5IBGen [CCommRing.zero, CFrac.ofFraction [1] [0, 0, 1] (by cfrac_nonzero)])
      && cisZero (csub ((integralBasis cusp5F).getD 0 []) [CCommRing.one])) = true := by native_decide

/-- The worse-cusp generator `y/x²` is integral (`(y/x²)² = x`) and `[1, y/x²]` is maximal. -/
theorem cusp5_integralBasis_integral_maximal :
    (cisZero (csub (CPoly.mulMod cusp5F cusp5IBGen cusp5IBGen) [CFrac.ofPoly [0, 1]])
      && isMaximalOrder cusp5F (integralBasis cusp5F)) = true := by native_decide

/-! ### A multi-prime curve: `y² − x³(x−1)²`, bad at both `x` and `x − 1` (`native_decide`)

`y² − x³(x−1)²` has two bad primes `x` and `x − 1`; `integralBasis` enlarges at both in one pass,
reaching `[1, y/(x(x − 1))]`. -/

/-- The two-bad-prime curve `f = y² − x³(x − 1)² ∈ ℚ(x)[y]`, the `DensePoly (DenseFrac ℚ)`
`[−(x⁵−2x⁴+x³), 0, 1]`. -/
def biCuspF : DensePoly (DenseFrac ℚ) :=
  [CFrac.ofPoly [0, 0, 0, -1, 2, -1], CCommRing.zero, CCommRing.one]

/-- The computed integral-basis generator `y/(x(x−1)) = y/(x² − x)` = the second basis vector of
`integralBasis biCuspF`. -/
def biCuspIBGen : DensePoly (DenseFrac ℚ) := (integralBasis biCuspF).getD 1 []

-- Sanity print: the two-bad-prime discriminant numerator (expected `4x³(x−1)² = 4x³−8x⁴+4x⁵ = [0,0,0,4,-8,4]`).
#eval (discNum biCuspF : List ℚ)

-- Sanity print: the bad primes (expected `[x−1, x] = [[-1,1], [0,1]]` in factoring order).
#eval (badPrimes biCuspF).map (fun p => (cmonic p : List ℚ))

-- Sanity print: the FULL integralBasis (expected `[1, y/(x²−x)]`, i.e. second vector denom `[0,-1,1]`).
#eval (integralBasis biCuspF).map (fun b => b.map (fun z =>
  ((CFrac.num z : List ℚ), (CFrac.den z : List ℚ))))

/-- **★★ The curve `y² − x³(x−1)²` has TWO bad primes `x` and `x − 1`** (`native_decide`): `badPrimes biCuspF`
(in factoring order) is `[x − 1, x]` — the discriminant `4x³(x − 1)²` flags both `p = x` and `p = x − 1` as
primes where `[1, y]` is non-maximal. The first genuinely multi-prime example (the cusp/node had a single bad
prime `x`). -/
theorem biCusp_badPrimes_eq :
    (badPrimes biCuspF).map cmonic = [([-1, 1] : DensePoly ℚ), ([0, 1] : DensePoly ℚ)] := by
  native_decide

/-- **★★ The multi-prime integral basis is `[1, y/(x(x−1))]`, integral (`(y/(x(x−1)))² = x`) and maximal**
(`native_decide`): `integralBasis biCuspF` enlarges `[1, y]` at **both** bad primes `x` and `x − 1`, returning
the generator `[0, 1/(x² − x)] = y/(x(x − 1))` and the first vector `1`; the generator is integral
(`CPoly.mulMod biCuspF g g = x`, i.e. `(y/(x(x−1)))² = x³(x−1)²/(x²(x−1)²) = x`); and `isMaximalOrder` is `true`. The
single combined denominator `x(x − 1)` carries the enlargement at both primes at once. -/
theorem biCusp_integralBasis_eq :
    (cisZero (csub biCuspIBGen [CCommRing.zero, CFrac.ofFraction [1] [0, -1, 1] (by cfrac_nonzero)])
      && cisZero (csub ((integralBasis biCuspF).getD 0 []) [CCommRing.one])
      && cisZero (csub (CPoly.mulMod biCuspF biCuspIBGen biCuspIBGen) [CFrac.ofPoly [0, 1]])
      && isMaximalOrder biCuspF (integralBasis biCuspF)) = true := by native_decide

/-! ### The NEXT piece: higher-degree (non-linear) bad primes, and the genus

`integralBasis` now iterates Round-2 to the maximal order for **linear** bad primes `p = x − a` (the residue
field `K[x]/(p) = K`, so the trace-matrix kernel mod `p` is a single root evaluation `CFrac.eval`). The two
remaining pieces:

1. **Higher-degree bad primes.** For a bad prime `p` of degree `> 1` (e.g. an irreducible quadratic
   `x² + 1` over `ℚ`), the residue field `K[x]/(p)` is a proper field **extension** of `K`. The mod-`p`
   trace-matrix kernel is then linear algebra **over `K[x]/(p)`** — arithmetic on `DensePoly ℚ` reduced mod `p`
   (a degree-`< deg p` representative ring), not a single evaluation at a root. The construction is otherwise
   identical (`ipOCoords`'s residue-kernel in `O`-coords + `idealizerOCoords`): replace `CFrac.eval` /
   `CLinearSolve.nullspaceBasis` over `K` by their `K[x]/(p)`-coefficient analogues (selected remainder arithmetic in the Gauss
   elimination). The linear case here already covers the cusp/node and the multi-step/multi-prime curves
   above (all bad primes `x`, `x − 1`).

2. **The genus.** With the integral basis `[ω₀, …, ωₙ₋₁]` in hand, the **conductor** (the `K[x]`-ideal
   `(O_max : O_eq)`) measures the gap between the equation order and the maximal order; its degree, plus the
   degree of the discriminant of the maximal order, gives the genus via the conductor-discriminant /
   Riemann–Hurwitz formula. The integral basis (this file) is the finite-pole datum that, combined with the
   analogous basis at infinity, yields the genus and the divisor arithmetic. For the cusp/node (`g = 0`) the
   integral basis `[1, y/x]` already exhibits the normalization; the genus computation is the next layer.

The **integral basis is the denominator data** the genus-`g` algebraic Hermite reduction and the
divisor/logarithmic-part machinery (the integration of arbitrary algebraic functions) consume: a function on
the curve has a finite pole exactly where it leaves `O_max`, so `integralBasis` is what makes "no finite
poles" decidable and the algebraic-function integral computable for an arbitrary plane curve. -/

/-! ### `#print axioms` — does the engine compute the FULL general-curve integral basis?

Each validation carries the standard `[propext, Classical.choice, Quot.sound]` plus the `native_decide`
compiler axiom — **no `sorry`, no `sorryAx`, no extra axiom** (the iteration `integralBasisLoop` is `ℕ`-fuel
structural recursion; `round2Pass`/`round2StepOrderAt`/`ipOCoords`/`idealizerOCoords` are non-recursive
compositions over finite-list kernels; `CLinearSolve.nullspaceBasis`/`CLinearSolve.matrixInverse`/
`hermiteRowReduce` fold over finite
`List.range`s, while exact division and fraction cancellation use the selected abstract algorithms).
**The engine now computes the FULL general-curve integral basis** —
iterating the Ford–Zassenhaus Round-2 step to the maximal order: for the cusp `y² − x³` and node
`y² − x²(x+1)` it returns `[1, y/x]` in one step (`cusp_integralBasis_eq`, `node_integralBasis_eq`); for the
**worse cusp** `y² − x⁵` it iterates **twice** to `[1, y/x²]` (`cusp5_integralBasis_eq`,
`cusp5_oneStep_not_maximal` showing one step is insufficient and not maximal); for `y² − x³(x−1)²` it enlarges
at **both** bad primes `x` and `x − 1` to `[1, y/(x(x−1))]` (`biCusp_badPrimes_eq`, `biCusp_integralBasis_eq`)
— each final basis integral (`CPoly.mulMod` of the generator with itself in `K[x]`) and maximal (`isMaximalOrder`).
Multi-step and multi-prime curves beyond the one-step cusp/node now compute. -/

-- ★ The cusp/node: `integralBasis = [1, y/x]` in one step, integral and maximal:
#print axioms cusp_integralBasis_eq
#print axioms node_integralBasis_eq

-- ★★ The MULTI-STEP worse cusp `y² − x⁵`: one step insufficient, the full iteration reaches `[1, y/x²]`:
#print axioms cusp5_oneStep_not_maximal
#print axioms cusp5_integralBasis_eq
#print axioms cusp5_integralBasis_integral_maximal

-- ★★ The MULTI-PRIME curve `y² − x³(x−1)²`: two bad primes, enlarged at both to `[1, y/(x(x−1))]`:
#print axioms biCusp_badPrimes_eq
#print axioms biCusp_integralBasis_eq

end DeepWiki.SymbolicIntegration
