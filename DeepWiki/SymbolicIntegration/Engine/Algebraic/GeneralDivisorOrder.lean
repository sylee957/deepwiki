import DeepWiki.SymbolicIntegration.Engine.Algebraic.GeneralDivisorExamples
import DeepWiki.ComputableAlgebra.FracReduce

/-! # The general divisor order (torsion test) over an arbitrary plane curve

Deciding whether a degree-0 divisor class `δ ∈ Pic⁰(C)` on `K(x, y) = K(x)[y]/(f)` is torsion:
`δ` is `m`-torsion iff `m·δ` (repeated `idealProduct`) is principal, so `order(δ)` is the smallest
`m ≥ 1` with `m·δ` principal. Built from `idealReduce` (canonical HNF representative),
`isPrincipalIdeal` (principality oracle), and the fuel-bounded search `genDivisorOrder`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace DensePoly

open DensePoly

/-! ### A canonical (unique) Hermite normal form over `K[x]` (`canonHNF`) -/

/-- Canonicalize a triangular `PolyMatrix DensePoly ℚ`: make pivots monic and reduce above them. -/
def canonHNF (M : PolyMatrix DensePoly ℚ) : PolyMatrix DensePoly ℚ :=
  let n := M.length
  -- 1. scale each row so its diagonal pivot is monic
  let M1 : PolyMatrix DensePoly ℚ := (List.range n).foldl (fun acc i =>
    let piv := CPoly.polyMatGet acc i i
    if cisZero piv then acc
    else CPoly.rowScale acc i [CField.inv (clead piv)]) M
  -- 2. reduce each above-pivot entry M[k][i] (k < i) mod the monic pivot M[i][i]
  (List.range n).foldl (fun acc i =>
    let piv := CPoly.polyMatGet acc i i
    if cisZero piv then acc
    else
      (List.range n).foldl (fun a k =>
        if k < i then
          let e := CPoly.polyMatGet a k i
          let q := CPolyEuclidean.div e piv
          if cisZero q then a else CPoly.rowSub a k i q
        else a) acc) M1

/-- `true` iff two fractional ideals have the same canonical HNF `canonHNFEq I J`: scale both to the
common denominator `δ_I·δ_J`, `hermiteRowReduce` and `canonHNF` over `K[x]`, and compare the unique
normal forms entrywise — a sound ideal-equality test. -/
def canonHNFEq (I J : GenDivisor) : Bool :=
  let (δI, _) := idealClear I
  let (δJ, _) := idealClear J
  let scale : DensePoly ℚ → GenDivisor → PolyMatrix DensePoly ℚ := fun c K =>
    let cc := cnorm c
    K.map (fun row => row.map (fun z =>
      let zz := CFrac.reduceMonic z
      let num := CFrac.num zz
      let den := cnorm (CFrac.den zz)
      CPolyEuclidean.div (cmul cc num) den))
  let NI := scale (cmul δI δJ) I
  let NJ := scale (cmul δI δJ) J
  let HI := canonHNF ((CPoly.hermiteRowReduce NI).filter (fun row => !row.all cisZero))
  let HJ := canonHNF ((CPoly.hermiteRowReduce NJ).filter (fun row => !row.all cisZero))
  let n := max HI.length HJ.length
  let w := max (HI.headD []).length (HJ.headD []).length
  (List.range n).all (fun i =>
    (List.range w).all (fun j =>
      cisZero (csub ((HI.getD i []).getD j []) ((HJ.getD i []).getD j []))))

end DensePoly

/-! ### The reduced representative of a fractional ideal (`idealReduce`) -/

open DensePoly

namespace DensePoly

/-- The canonical reduced representative `idealReduce f basis I`: clear `I` to `(δ, N)`,
`hermiteRowReduce` and `canonHNF` over `K[x]`, read back as `(1/δ)·Ĥ` in lowest terms. `f`/`basis`
are unused (kept for the uniform divisor-API signature). -/
def idealReduce (_f : DensePoly (DenseFrac ℚ)) (_basis : List (DensePoly (DenseFrac ℚ)))
    (I : GenDivisor) : GenDivisor :=
  let (δ, N) := idealClear I
  let H := canonHNF ((CPoly.hermiteRowReduce N).filter (fun row => !row.all cisZero))
  let dd := cnorm δ
  -- read back as the fractional ideal (1/δ)·Ĥ, then reduce every entry to lowest terms (`reduceMat`,
  -- value-preserving via `CFrac.toRatFunc_reduce`) so the reduced representative carries no swollen factors
  reduceMat (H.map (fun row => row.map (fun p =>
    if h : cisZero dd = false then CFrac.reduceMonic (CFrac.ofFraction p dd h)
    else CFrac.ofPoly p)))

/-! ### Principality: is the ideal `g·O`? (`genCandidates`, `isPrincipalIdeal`) -/

/-- The candidate single generators `genCandidates basis I`: each canonical-HNF row of `I`'s cleared
integral matrix reconstructed as a `K(x, y)` element (`wToAf basis`). For a principal ideal `g·O` the
generator `g` is among these up to a unit. -/
def genCandidates (basis : List (DensePoly (DenseFrac ℚ))) (I : GenDivisor) : List (DensePoly (DenseFrac ℚ)) :=
  let H := canonHNF ((CPoly.hermiteRowReduce (idealClear I).2).filter (fun row => !row.all cisZero))
  H.map (fun row => wToAf basis (row.map CFrac.ofPoly))

/-- `true` iff `I` is principal `isPrincipalIdeal f basis I`: `canonHNFEq I (principalDivisor f basis
g)` for some candidate generator `g ∈ genCandidates basis I`. Sound — a `true` means `[I] = 0` in
`Pic⁰(C)`. -/
def isPrincipalIdeal (f : DensePoly (DenseFrac ℚ)) (basis : List (DensePoly (DenseFrac ℚ)))
    (I : GenDivisor) : Bool :=
  (genCandidates basis I).any (fun g => canonHNFEq I (principalDivisor f basis g))

/-! ### The order search `genDivisorOrder` (smallest `m ≥ 1` with `m·δ` principal) -/

/-- Order-search loop `genDivisorOrderAux f basis δ fuel acc n`: with `acc = n·δ`, test
`(n+1)·δ = idealProduct δ acc` for principality; on a hit return `some (n+1)`, else recurse.
`fuel` bounds the remaining multiples. -/
def genDivisorOrderAux (f : DensePoly (DenseFrac ℚ)) (basis : List (DensePoly (DenseFrac ℚ))) (δ : GenDivisor) :
    ℕ → GenDivisor → ℕ → Option ℕ
  | 0, _, _ => none
  | fuel + 1, acc, n =>
    let acc := idealProduct f basis δ acc
    if isPrincipalIdeal f basis acc then some (n + 1)
    else genDivisorOrderAux f basis δ fuel acc (n + 1)

/-- The divisor order `genDivisorOrder fuel f basis δ`: `some m` = the smallest `m ≥ 1` with `m·δ`
principal (⟹ `δ` is `m`-torsion), searching up to `fuel` multiples; `none` if no `m ≤ fuel` works. -/
def genDivisorOrder (fuel : ℕ) (f : DensePoly (DenseFrac ℚ)) (basis : List (DensePoly (DenseFrac ℚ)))
    (δ : GenDivisor) : Option ℕ :=
  genDivisorOrderAux f basis δ fuel (idealIdentity (cdeg f)) 0

end DensePoly

/-! ## Validation: principal classes have order 1 (`native_decide`) -/

open DensePoly

/-- `div(y)` is principal and has order 1 on `y³ = x²`: `isPrincipalIdeal gdDivY = true` and
`genDivisorOrder 4 … gdDivY = some 1`. -/
theorem gdo_divY_principal_order1 :
    (isPrincipalIdeal gcuspCubicF gcuspCubicBasis gdDivY
      && (genDivisorOrder 4 gcuspCubicF gcuspCubicBasis gdDivY == some 1)) = true := by native_decide

/-- The identity `O` has order 1 on `y³ = x²`: `isPrincipalIdeal gdIdentity = true` and
`genDivisorOrder 4 … gdIdentity = some 1`. -/
theorem gdo_identity_order1 :
    (isPrincipalIdeal gcuspCubicF gcuspCubicBasis gdIdentity
      && (genDivisorOrder 4 gcuspCubicF gcuspCubicBasis gdIdentity == some 1)) = true := by native_decide

/-! ## The 3-torsion `(0,1) − ∞` on `y² = x³ + 1` (`native_decide`)

On `y² = x³ + 1` (integral basis `[1, y]`), the inflection point `(0, 1)` gives the 3-torsion class
`[(0,1) − ∞]`, represented by the place ideal `P = (x, y − 1)·O`: `P` and `P²` are non-principal but
`P³ = div(y − 1)` is principal, so `order = 3`. -/

/-- The curve `f = y² − (x³ + 1)` (`[−(x³+1), 0, 1]`) over `DensePoly (DenseFrac ℚ)`. -/
def hcubeF : DensePoly (DenseFrac ℚ) := [CFrac.ofPoly [-1, 0, 0, -1], CCommRing.zero, CCommRing.one]

/-- The integral basis `[1, y]` of `y² = x³ + 1` (no finite poles — the power basis, since `x³ + 1` is
squarefree). -/
def hcubeBasis : List (DensePoly (DenseFrac ℚ)) := integralBasis hcubeF

/-- The 3-torsion divisor `δ = P = (x, y − 1)·O` on `y² = x³ + 1`, built from its `O`-generators reduced
to a `2×2` ideal matrix by one `idealProduct` with the identity. -/
def hcubeTorsionDiv : GenDivisor :=
  idealProduct hcubeF hcubeBasis
    [ [CFrac.ofPoly [0, 1], CCommRing.zero],
      [CCommRing.zero, CFrac.ofPoly [0, 1]],
      [CFrac.ofPoly [-1], CFrac.ofPoly [1]],
      [CFrac.ofPoly [1, 0, 0, 1], CFrac.ofPoly [-1]] ]
    (idealIdentity 2)

-- Sanity print: δ = P = (x, y−1) as a [w]=[1,y] ideal matrix (Hermite-reduced).
#eval hcubeTorsionDiv.map (fun row =>
  row.map (fun z => ((CFrac.num z : List ℚ), (CFrac.den z : List ℚ))))

-- Sanity print: the reduced canonical-HNF representative of δ = P (first row `1 − y`, second `x·y`; norm `x`).
#eval (idealReduce hcubeF hcubeBasis hcubeTorsionDiv).map
  (fun row => row.map (fun z => ((CFrac.num z : List ℚ), (CFrac.den z : List ℚ))))

/-- The order-3 ladder on `y² = x³+1`: `P` and `P²` are non-principal but `P³ = div(y − 1)` is
principal, via `isPrincipalIdeal` on the repeated `idealProduct` powers. -/
theorem hcube_torsion_ladder :
    (isPrincipalIdeal hcubeF hcubeBasis hcubeTorsionDiv == false
      && isPrincipalIdeal hcubeF hcubeBasis
            (idealProduct hcubeF hcubeBasis hcubeTorsionDiv hcubeTorsionDiv) == false
      && isPrincipalIdeal hcubeF hcubeBasis
            (idealProduct hcubeF hcubeBasis hcubeTorsionDiv
              (idealProduct hcubeF hcubeBasis hcubeTorsionDiv hcubeTorsionDiv)) == true) = true := by
  native_decide

/-- `genDivisorOrder 8 hcubeF hcubeBasis hcubeTorsionDiv = some 3` — the 3-torsion class `P = (x, y −
1)·O` on `y² = x³+1` has order 3. -/
theorem hcube_genDivisorOrder_eq3 :
    genDivisorOrder 8 hcubeF hcubeBasis hcubeTorsionDiv = some 3 := by native_decide

/-! ## The general-divisor-order milestone (`native_decide`) -/

/-- The general divisor order validates: principal classes (`div(y)` on `y³ = x²`, and `O`) have order
1, and the 3-torsion class `P = (x, y − 1)·O` on `y² = x³ + 1` has `genDivisorOrder = some 3` with the
ladder `P, P²` non-principal and `P³` principal. -/
theorem general_divisor_order_validates :
    -- principal classes have order 1
    (isPrincipalIdeal gcuspCubicF gcuspCubicBasis gdDivY = true
      ∧ genDivisorOrder 4 gcuspCubicF gcuspCubicBasis gdDivY = some 1
      ∧ genDivisorOrder 4 gcuspCubicF gcuspCubicBasis gdIdentity = some 1)
    -- the 3-torsion (0,1) − ∞ on y² = x³+1 has order 3 (hyperelliptic conservativity)
    ∧ genDivisorOrder 8 hcubeF hcubeBasis hcubeTorsionDiv = some 3
    -- the order-3 ladder: P, P² non-principal, P³ principal
    ∧ isPrincipalIdeal hcubeF hcubeBasis hcubeTorsionDiv = false
    ∧ isPrincipalIdeal hcubeF hcubeBasis
          (idealProduct hcubeF hcubeBasis hcubeTorsionDiv
            (idealProduct hcubeF hcubeBasis hcubeTorsionDiv hcubeTorsionDiv)) = true := by
  native_decide

/-! ## The remaining piece: the good-reduction torsion bound (termination)

`genDivisorOrder` is fuel-bounded. To make the search terminate with a definite non-torsion answer, the
fuel must be a genuine ceiling on the order, bounded by the size of the finite torsion subgroup of
`Pic⁰(C)` via good reduction modulo a prime `p` (run the same fractional-ideal machinery over `ZMod p`
to count `|Pic⁰(C)(𝔽_p)|`). This total torsion decision builds on the present order search. -/

end DeepWiki.SymbolicIntegration
