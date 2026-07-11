import DeepWiki.SymbolicIntegration.Engine.Algebraic.IntegralBasisFull
import DeepWiki.SymbolicIntegration.Engine.Algebraic.GeneralSetup
import DeepWiki.ComputableAlgebra.FracReduce

/-! # Divisors on a general plane curve as fractional ideals

Divisors on `K(x, y) = K(x)[y]/(f)` as fractional `O`-ideals over the integral basis (`n×n`
matrices over `K(x)`): identity `idealIdentity`, principal `principalDivisor`, the Pic group law
`idealProduct`, and the tests `idealEq`, `idealIsIntegral`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace DensePoly

open DensePoly

/-! ### The representation: a fractional `O`-ideal as a `K(x)`-matrix in `[w]`-coordinates (`GenDivisor`) -/

/-- A fractional `O`-ideal: an `n×n` matrix over `K(x)` whose row `i` is a generator
`genᵢ = Σⱼ Mᵢⱼ wⱼ` in integral-basis `[w]`-coordinates. -/
abbrev GenDivisor := List (List (DenseFrac ℚ))

/-- The identity divisor `idealIdentity n = Iₙ` — the order `O`, the Pic neutral element. -/
def idealIdentity (n : ℕ) : GenDivisor :=
  (List.range n).map (fun i =>
    (List.range n).map (fun j => if i = j then (CCommRing.one : DenseFrac ℚ) else CCommRing.zero))

/-- Entrywise lowest-terms reduction `reduceMat I = I.map (List.map CFrac.reduce)`, value-preserving on
each `ℚ(x)` entry (cancels common polynomial factors only). -/
def reduceMat (I : GenDivisor) : GenDivisor :=
  I.map (List.map CFrac.reduce)

/-- Reconstruct a `K(x, y)` element from `[w]`-coordinates: `wToAf basis row = Σⱼ rowⱼ·wⱼ` (inverse
of `toOCoords`). -/
def wToAf {P : Type → Type} [CPoly P] [CPolyEngine P]
    (basis : List (P (DenseFrac ℚ))) (row : List (DenseFrac ℚ)) : P (DenseFrac ℚ) :=
  (List.range basis.length).foldl (fun acc i =>
    CPolyEngine.add acc
      (CPolyEngine.scale (row.getD i CCommRing.zero) (basis.getD i CPoly.czero))) CPoly.czero

example :
    let ofList : List (DenseFrac ℚ) → CPoly.SparsePoly (DenseFrac ℚ) := CPolyEngine.ofCoeffList
    let one : DenseFrac ℚ := CCommRing.one
    CPolyEngine.cisZero
      (CPolyEngine.sub (wToAf [ofList [one], ofList [CCommRing.zero, one]] [one, one])
        (ofList [one, one])) = true := by
  native_decide

/-! ### `div(g) = g·O`: the principal divisor (`principalDivisor`) -/

/-- The principal divisor `principalDivisor f basis g = div(g) = g·O`: row `i` is the `[w]`-coordinates
of `g·wᵢ = CPoly.mulMod f g wᵢ` (via `B⁻¹`); empty matrix if `B` is singular. -/
def principalDivisor (f : DensePoly (DenseFrac ℚ)) (basis : List (DensePoly (DenseFrac ℚ)))
    (g : DensePoly (DenseFrac ℚ)) : GenDivisor :=
  let n := cdeg f
  let B := orderToPowerMatrix n basis
  match matInv n B with
  | none => []
  | some Binv =>
    basis.map (fun wi => toOCoords Binv n (CPoly.mulMod f g wi))

/-! ### Clearing a fractional ideal to an integral `K[x]`-matrix at a common denominator (`idealClear`) -/

/-- Clear a fractional ideal to `(δ, N)` with `δ = commonDenom I` and `Nᵢⱼ = δ·Iᵢⱼ` over `K[x]`, so
`I = (1/δ)·N`. -/
def idealClear (I : GenDivisor) : DensePoly ℚ × PolyMatrix DensePoly ℚ :=
  let δ : DensePoly ℚ := commonDenom I
  (δ, I.map (clearRowExact δ))

/-! ### The ideal product `I·J` (the Pic group law) (`idealProduct`) -/

/-- The ideal product `idealProduct f basis I J` (the Pic group law): the fractional `O`-ideal from
the `n²` cross-products `genᵢ·genₖ`, cleared to a common denominator and `hermiteRowReduce`d to `n`
generators; `[]` if `B` is singular. -/
def idealProduct (f : DensePoly (DenseFrac ℚ)) (basis : List (DensePoly (DenseFrac ℚ)))
    (I J : GenDivisor) : GenDivisor :=
  let n := cdeg f
  let B := orderToPowerMatrix n basis
  match matInv n B with
  | none => []
  | some Binv =>
    -- the n² cross-products genᵢ·genₖ in [w]-coords, each entry put in lowest terms (`reduceMat`,
    -- value-preserving) before the common-denominator clearing below
    let cross : List (List (DenseFrac ℚ)) :=
      reduceMat (I.flatMap (fun gi =>
        J.map (fun gk =>
          toOCoords Binv n (CPoly.mulMod f (wToAf basis gi) (wToAf basis gk)))))
    -- clear to K[x] at a common denom δ, Hermite-reduce, take the n nonzero rows
    let δ : DensePoly ℚ := commonDenom cross
    let N : PolyMatrix DensePoly ℚ := cross.map (clearRowExact δ)
    let nz := (CPoly.hermiteRowReduce N).filter (fun row => !row.all cisZero)
    -- read back the first n rows as the fractional ideal (1/δ)·Nhat, then put every entry in lowest terms
    -- (`reduceMat`, value-preserving) so the product fed back into the next `idealProduct` is canonical
    reduceMat ((List.range n).map (fun i =>
      (List.range n).map (fun j =>
        let num := (nz.getD i []).getD j []
        let dd := cnorm δ
        if h : cisZero dd = false then CFrac.reduceMonic (CFrac.ofFraction num dd h)
        else CCommRing.zero)))

/-! ### Normalization / equality of fractional ideals (`idealHNF`, `idealEq`, `idealIsIntegral`) -/

/-- The Hermite normal form `idealHNF I = (δ, H)`: clear `I` to `(δ, N)`, `hermiteRowReduce` over
`K[x]`, keep the nonzero rows normalized by `cnorm`; the presentation `(1/δ)·H`. -/
def idealHNF (I : GenDivisor) : DensePoly ℚ × PolyMatrix DensePoly ℚ :=
  let (δ, N) := idealClear I
  let H := (CPoly.hermiteRowReduce N).filter (fun row => !row.all cisZero)
  (cnorm δ, H.map (fun row => row.map cnorm))

/-- `true` iff two fractional ideals are equal `idealEq I J`: scale both to the common denominator
`δ_I·δ_J`, `hermiteRowReduce` over `K[x]`, and compare the normal forms entrywise. -/
def idealEq (I J : GenDivisor) : Bool :=
  let (δI, _) := idealClear I
  let (δJ, _) := idealClear J
  -- scale both ideals to the common denom δI·δJ, then compare cleared HNFs
  let scale : DensePoly ℚ → GenDivisor → PolyMatrix DensePoly ℚ := fun c K =>
    let cc := cnorm c
    K.map (fun row => row.map (fun z =>
      let zz := CFrac.reduceMonic z
      let num := CFrac.num zz
      let den := cnorm (CFrac.den zz)
      CPolyEuclidean.div (cmul cc num) den))
  let NI := scale (cmul δI δJ) I
  let NJ := scale (cmul δI δJ) J
  let HI := (CPoly.hermiteRowReduce NI).filter (fun row => !row.all cisZero)
  let HJ := (CPoly.hermiteRowReduce NJ).filter (fun row => !row.all cisZero)
  let n := max HI.length HJ.length
  let w := max (HI.headD []).length (HJ.headD []).length
  (List.range n).all (fun i =>
    (List.range w).all (fun j =>
      cisZero (csub ((HI.getD i []).getD j []) ((HJ.getD i []).getD j []))))

/-- `true` iff the divisor is integral `idealIsIntegral I`: every entry reduces to a fraction with
denominator `1` (i.e. `I ⊆ O`). -/
def idealIsIntegral (I : GenDivisor) : Bool :=
  I.all (fun row => row.all (fun z =>
    let zz := CFrac.reduceMonic z
    cisZero (csub (cnorm (CFrac.den zz)) [CCommRing.one])))

end DensePoly

end DeepWiki.SymbolicIntegration
