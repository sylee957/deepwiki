import DeepWiki.SymbolicIntegration.Engine.Algebraic.IntegralBasisFull
import DeepWiki.SymbolicIntegration.Engine.Algebraic.GeneralSetup
import DeepWiki.SymbolicIntegration.Engine.QFunReduce

/-! # Divisors on a general plane curve as fractional ideals

Divisors on `K(x, y) = K(x)[y]/(f)` as fractional `O`-ideals over the integral basis (`n×n`
matrices over `K(x)`): identity `idealIdentity`, principal `principalDivisor`, the Pic group law
`idealProduct`, and the tests `idealEq`, `idealIsIntegral`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace CPolyG

open CPolyG

/-! ### The representation: a fractional `O`-ideal as a `K(x)`-matrix in `[w]`-coordinates (`GenDivisor`) -/

/-- A fractional `O`-ideal: an `n×n` matrix over `K(x)` whose row `i` is a generator
`genᵢ = Σⱼ Mᵢⱼ wⱼ` in integral-basis `[w]`-coordinates. -/
abbrev GenDivisor := List (List (QFunNZG ℚ))

/-- The identity divisor `idealIdentity n = Iₙ` — the order `O`, the Pic neutral element. -/
def idealIdentity (n : ℕ) : GenDivisor :=
  (List.range n).map (fun i =>
    (List.range n).map (fun j => if i = j then (CField.one : QFunNZG ℚ) else CField.zero))

/-- Entrywise lowest-terms reduction `qReduceMat I = I.map (List.map qReduce)`, value-preserving on
each `ℚ(x)` entry (cancels common polynomial factors only). -/
def qReduceMat (I : GenDivisor) : GenDivisor :=
  I.map (List.map qReduce)

/-- Reconstruct a `K(x, y)` element from `[w]`-coordinates: `wToAf basis row = Σⱼ rowⱼ·wⱼ` (inverse
of `toOCoords`). -/
def wToAf (basis : List (CPolyG (QFunNZG ℚ))) (row : List (QFunNZG ℚ)) : CPolyG (QFunNZG ℚ) :=
  (List.range basis.length).foldl (fun acc i =>
    caddG acc (cscaleG (row.getD i CField.zero) (basis.getD i []))) ([] : CPolyG (QFunNZG ℚ))

/-! ### `div(g) = g·O`: the principal divisor (`principalDivisor`) -/

/-- The principal divisor `principalDivisor f basis g = div(g) = g·O`: row `i` is the `[w]`-coordinates
of `g·wᵢ = afMul f g wᵢ` (via `B⁻¹`); empty matrix if `B` is singular. -/
def principalDivisor (f : CPolyG (QFunNZG ℚ)) (basis : List (CPolyG (QFunNZG ℚ)))
    (g : CPolyG (QFunNZG ℚ)) : GenDivisor :=
  let n := cdegG f
  let B := orderToPowerMatrix n basis
  match matInvG n B with
  | none => []
  | some Binv =>
    basis.map (fun wi => toOCoords Binv n (afMul f g wi))

/-! ### Clearing a fractional ideal to an integral `K[x]`-matrix at a common denominator (`idealClear`) -/

/-- Clear a fractional ideal to `(δ, N)` with `δ = commonDenomG I` and `Nᵢⱼ = δ·Iᵢⱼ` over `K[x]`, so
`I = (1/δ)·N`. -/
def idealClear (I : GenDivisor) : CPolyG ℚ × PolyMatrix ℚ :=
  let δ : CPolyG ℚ := commonDenomG I
  (δ, I.map (clearRowExact δ))

/-! ### The ideal product `I·J` (the Pic group law) (`idealProduct`) -/

/-- The ideal product `idealProduct f basis I J` (the Pic group law): the fractional `O`-ideal from
the `n²` cross-products `genᵢ·genₖ`, cleared to a common denominator and `hermiteRowReduce`d to `n`
generators; `[]` if `B` is singular. -/
def idealProduct (f : CPolyG (QFunNZG ℚ)) (basis : List (CPolyG (QFunNZG ℚ)))
    (I J : GenDivisor) : GenDivisor :=
  let n := cdegG f
  let B := orderToPowerMatrix n basis
  match matInvG n B with
  | none => []
  | some Binv =>
    -- the n² cross-products genᵢ·genₖ in [w]-coords, each entry put in lowest terms (`qReduceMat`,
    -- value-preserving) before the common-denominator clearing below
    let cross : List (List (QFunNZG ℚ)) :=
      qReduceMat (I.flatMap (fun gi =>
        J.map (fun gk =>
          toOCoords Binv n (afMul f (wToAf basis gi) (wToAf basis gk)))))
    -- clear to K[x] at a common denom δ, Hermite-reduce, take the n nonzero rows
    let δ : CPolyG ℚ := commonDenomG cross
    let N : PolyMatrix ℚ := cross.map (clearRowExact δ)
    let nz := (hermiteRowReduce N).filter (fun row => !row.all cisZeroG)
    -- read back the first n rows as the fractional ideal (1/δ)·Nhat, then put every entry in lowest terms
    -- (`qReduceMat`, value-preserving) so the product fed back into the next `idealProduct` is canonical
    qReduceMat ((List.range n).map (fun i =>
      (List.range n).map (fun j =>
        let num := (nz.getD i []).getD j []
        let dd := cnormG δ
        if h : cisZeroG dd = false then qReduceNZG (qxOfFrac num dd h) else CField.zero)))

/-! ### Normalization / equality of fractional ideals (`idealHNF`, `idealEq`, `idealIsIntegral`) -/

/-- The Hermite normal form `idealHNF I = (δ, H)`: clear `I` to `(δ, N)`, `hermiteRowReduce` over
`K[x]`, keep the nonzero rows normalized by `cnormG`; the presentation `(1/δ)·H`. -/
def idealHNF (I : GenDivisor) : CPolyG ℚ × PolyMatrix ℚ :=
  let (δ, N) := idealClear I
  let H := (hermiteRowReduce N).filter (fun row => !row.all cisZeroG)
  (cnormG δ, H.map (fun row => row.map cnormG))

/-- `true` iff two fractional ideals are equal `idealEq I J`: scale both to the common denominator
`δ_I·δ_J`, `hermiteRowReduce` over `K[x]`, and compare the normal forms entrywise. -/
def idealEq (I J : GenDivisor) : Bool :=
  let (δI, _) := idealClear I
  let (δJ, _) := idealClear J
  -- scale both ideals to the common denom δI·δJ, then compare cleared HNFs
  let scale : CPolyG ℚ → GenDivisor → PolyMatrix ℚ := fun c K =>
    let cc := cnormG c
    K.map (fun row => row.map (fun z =>
      let zz := qReduceNZG z
      let num := zz.1.1
      let den := cnormG zz.1.2
      cdivWf (cmulG cc num) den))
  let NI := scale (cmulG δI δJ) I
  let NJ := scale (cmulG δI δJ) J
  let HI := (hermiteRowReduce NI).filter (fun row => !row.all cisZeroG)
  let HJ := (hermiteRowReduce NJ).filter (fun row => !row.all cisZeroG)
  let n := max HI.length HJ.length
  let w := max (HI.headD []).length (HJ.headD []).length
  (List.range n).all (fun i =>
    (List.range w).all (fun j =>
      cisZeroG (csubG ((HI.getD i []).getD j []) ((HJ.getD i []).getD j []))))

/-- `true` iff the divisor is integral `idealIsIntegral I`: every entry reduces to a fraction with
denominator `1` (i.e. `I ⊆ O`). -/
def idealIsIntegral (I : GenDivisor) : Bool :=
  I.all (fun row => row.all (fun z =>
    let zz := qReduceNZG z
    cisZeroG (csubG (cnormG zz.1.2) [CField.one])))

end CPolyG

end DeepWiki.SymbolicIntegration
