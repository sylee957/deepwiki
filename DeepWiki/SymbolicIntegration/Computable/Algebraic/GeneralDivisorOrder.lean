import DeepWiki.SymbolicIntegration.Computable.Algebraic.GeneralDivisor
import DeepWiki.SymbolicIntegration.Computable.QFunReduce

/-! # The GENERAL divisor ORDER (torsion test): is a divisor class `δ ∈ Pic⁰(C)` of finite order, for an
ARBITRARY plane curve (Trager, *Integration of Algebraic Functions*, Ch. 6 "Principal Divisors and Points of
Finite Order")

`ComputableGeneralDivisor` represents a divisor on an arbitrary curve `K(x, y) = K(x)[y]/(f)` as a fractional
`O`-ideal (a `K(x)`-matrix in `[w]`-coordinates over the integral basis), with the PRINCIPAL divisor `div(g) =
g·O`, the IDEAL PRODUCT `idealProduct` (the Pic group law / general Cantor composition), the IDENTITY `O`
(`idealIdentity`), the equality test `idealEq`, and the integrality test `idealIsIntegral`. This file builds
the **general lift of the hyperelliptic `cantorOrder`** (`ComputableDivisorOrder`): deciding whether a divisor
class is **torsion** in `Pic⁰(C)` — for an arbitrary curve, not just `y² = ρ(x)`.

**The math.** A degree-0 divisor class `δ ∈ Pic⁰(C)` is `m`-**torsion** iff `m·δ` is **principal** (the
trivial class = the order `O` = the Pic neutral). In ideal terms: `δ` is a fractional `O`-ideal, `m·δ =
idealProduct^m δ` (repeated Pic composition), and `m·δ` is principal iff its **reduced** representative equals
`idealIdentity` (= `O`). So

  **`order(δ) = the smallest m ≥ 1 with reduced(m·δ) = O`**

— exactly the shape of the hyperelliptic `cantorOrder` (smallest `n` with `n·D = mumfordIdentity`), lifted from
the Mumford pair to the fractional-ideal-over-the-integral-basis representation.

* **`idealReduce f basis I`** — the **reduced** (canonical, minimal-`K[x]`-degree) representative of the
  fractional ideal `I`: clear `I` to an integral `K[x]`-matrix (`idealClear`), Hermite-reduce over `K[x]`
  (`hermiteRowReduce`), and **canonicalize** it (`canonHNF`: monic pivots, above-pivot entries reduced — the
  *unique* `K[x]`-row-lattice normal form, which the raw triangularization is not). The general analogue of
  Cantor reduction (`deg u ≤ g`), here a Hess-style `K[x]`-Hermite reduction over the integral basis; two
  fractional ideals are equal iff their `idealReduce`s agree (`canonHNFEq`).
* **`isPrincipalIdeal f basis I`** — `true` iff `I`'s class is **trivial**: `I = div(g)` for a generator `g`
  read off the canonical reduced ideal (`canonHNFEq I (div g)` for some canonical-HNF-row candidate `g`,
  `genCandidates`). **Sound** — a `true` means `I` genuinely equals `div(g)`. The principality oracle for the
  torsion test.
* **`genDivisorOrder fuel f basis δ`** — `Option ℕ`, the **order**: search `m = 1, 2, …` (each `m·δ =
  idealProduct δ ((m−1)·δ)`) for `isPrincipalIdeal (m·δ)`, fuel-bounded. `some m` = `δ` is `m`-torsion;
  `none` = no `m ≤ fuel` works (the order exceeds the fuel — a non-torsion candidate). The general lift of
  `cantorOrder`.

**Validations** (`native_decide`):
* **HYPERELLIPTIC CONSERVATIVITY** — on `y² = x³ + 1` (integral basis `[1, y]`, where the general
  fractional-ideal machinery specializes to the hyperelliptic Jacobian): the 3-torsion class of the
  inflection point `(0, 1)` (represented as the fractional ideal of the degree-0 divisor `(0,1) − ∞`) has
  **`genDivisorOrder = 3`** — matching the hyperelliptic `cantorOrder`/`cantorMul_pt01_order3`. The general
  divisor order recovers the hyperelliptic answer.
* **The class `2·δ` is NOT principal, `3·δ` IS** (`isPrincipalIdeal`) — the order-3 ladder
  (`reduced(δ) ≠ O`, `reduced(2δ) ≠ O`, `reduced(3δ) = O`), the torsion witness.
* **Principal classes have order 1** — `div(g)` (e.g. `div(y)` on the cuspidal cubic `y³ = x²`) is already
  trivial, so `genDivisorOrder (div g) = some 1`; and `O` itself has order 1.

**The engine now computes the GENERAL divisor order (the torsion test) for an arbitrary curve** — the general
lift of the hyperelliptic `cantorOrder`, via repeated `idealProduct` + an ideal-reduction/principality test
over the fractional-ideal representation. The good-reduction torsion BOUND (reduce mod `p`, `|Pic⁰(C)(𝔽_p)|`
as the terminating ceiling — the general lift of `ComputableDivisorOrder`'s `mumfordReduceModP`) is documented
at the end as the next piece. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace CPolyG

open CPolyG

/-! ### A canonical (unique) Hermite normal form over `K[x]` (`canonHNF`)

`hermiteRowReduce` (`ComputableHermiteNormalForm`) only **triangularizes** — it leaves the pivots un-normalized
and the above-pivot entries un-reduced, so two matrices with the *same* `K[x]`-row span (the same lattice / the
same fractional ideal) can have **different** triangular forms (e.g. `[[-4, x⁶−2x³+4], [0, x³]]` vs
`[[-1, 1], [0, x³]]`, both `= (y−1)·O = P³` on `y² = x³+1`). The **true** Hermite NORMAL form is unique per
lattice: make each pivot **monic** (scale the row by `1/lead`) and reduce every **above-pivot** entry modulo
its column's monic pivot (`cdivWf` quotient subtraction). Then equal lattices have *identical* canonical forms, and entrywise
comparison is a sound ideal-equality test (`canonHNFEq`). -/

/-- Make the triangular matrix's pivots monic and reduce above-pivot entries `canonHNF M`: on an
already-upper-triangular `PolyMatrix ℚ` (the `hermiteRowReduce` output, nonzero rows), for each diagonal pivot
`M[i][i]` scale row `i` by `1/lead(M[i][i])` (pivot becomes monic), then reduce each entry `M[k][i]` strictly
**above** the pivot (`k < i`) modulo the monic pivot (via `cdivWf`, subtracting the right `K[x]`-multiple of row
`i`). The result is the **unique** Hermite normal form of the row lattice — two matrices with the same `K[x]`-row
span have identical `canonHNF`. (Square `n×n` case: the pivots sit on the diagonal.) -/
def canonHNF (M : PolyMatrix ℚ) : PolyMatrix ℚ :=
  let n := M.length
  -- 1. scale each row so its diagonal pivot is monic
  let M1 : PolyMatrix ℚ := (List.range n).foldl (fun acc i =>
    let piv := polyMatGet acc i i
    if cisZeroG piv then acc
    else rowScale acc i [CField.inv (cleadG piv)]) M
  -- 2. reduce each above-pivot entry M[k][i] (k < i) mod the monic pivot M[i][i]
  (List.range n).foldl (fun acc i =>
    let piv := polyMatGet acc i i
    if cisZeroG piv then acc
    else
      (List.range n).foldl (fun a k =>
        if k < i then
          let e := polyMatGet a k i
          let q := cdivWf e piv
          if cisZeroG q then a else rowSub a k i q
        else a) acc) M1

/-- `true` iff two fractional ideals have the same canonical HNF `canonHNFEq I J`: clear both to a common
denominator `δ = δ_I·δ_J` (scaling each cleared generator matrix to that `δ`), `hermiteRowReduce` and `canonHNF`
both over `K[x]`, and compare the resulting **unique** normal forms entrywise (`cisZeroG` of the difference).
Sound **ideal** equality (`I = J` as fractional `O`-ideals) — unlike `idealEq` (whose un-canonicalized HNF
mis-reports equal lattices with different triangular forms, e.g. `P³` vs `div(y−1)`). The principality /
torsion test compares `m·δ` against `div(g)` through this. -/
def canonHNFEq (I J : GenDivisor) : Bool :=
  let (δI, _) := idealClear I
  let (δJ, _) := idealClear J
  let scale : CPolyG ℚ → GenDivisor → PolyMatrix ℚ := fun c K =>
    let cc := cnormG c
    K.map (fun row => row.map (fun z =>
      let zz := qReduceNZG z
      let num := zz.1.1
      let den := cnormG zz.1.2
      cdivWf (cmulG cc num) den))
  let NI := scale (cmulG δI δJ) I
  let NJ := scale (cmulG δI δJ) J
  let HI := canonHNF ((hermiteRowReduce NI).filter (fun row => !row.all cisZeroG))
  let HJ := canonHNF ((hermiteRowReduce NJ).filter (fun row => !row.all cisZeroG))
  let n := max HI.length HJ.length
  let w := max (HI.headD []).length (HJ.headD []).length
  (List.range n).all (fun i =>
    (List.range w).all (fun j =>
      cisZeroG (csubG ((HI.getD i []).getD j []) ((HJ.getD i []).getD j []))))

end CPolyG

/-! ### The reduced representative of a fractional ideal (`idealReduce`)

`idealReduce I` brings a fractional ideal to its canonical, minimal-`K[x]`-degree representative: clear `I` to
`(δ, N)` over a common `K[x]` denominator (`idealClear`), Hermite-reduce `N` over `K[x]` (`hermiteRowReduce`, the
Hess-style `K[x]`-reduction minimizing the generator degrees), and **canonicalize** it (`canonHNF`: monic pivots,
above-pivot entries reduced) — the **unique** `K[x]`-row-lattice normal form. The result is read back as the
fractional `O`-ideal `(1/δ)·Ĥ`. Two fractional ideals are **equal** (as ideals) iff their `idealReduce`s agree —
the canonicalization is what `canonHNFEq` compares; for the principality / torsion test the reduced `m·δ` is
compared against `div(g)`. -/

open CPolyG

namespace CPolyG

/-- The reduced (canonical Hermite-normal-form) representative of a fractional ideal `idealReduce f basis
I`: clear `I` to `(δ, N)` (`idealClear`), `hermiteRowReduce` `N` over `K[x]`, and `canonHNF` it (monic pivots,
above-pivot entries reduced) — the **unique** `K[x]`-row-lattice normal form. Read back as the fractional
`O`-ideal `(1/δ)·Ĥ` (entries `qReduceNZG (Ĥᵢⱼ / δ)`). The canonical, minimal-`K[x]`-degree representative of
`I` as a fractional ideal — the general analogue of the reduced Cantor divisor (`deg u ≤ g`), a Hess-style
`K[x]`-Hermite reduction over the integral basis. Two fractional ideals are **equal** iff their `idealReduce`s
agree (the canonical form `canonHNFEq` runs on); for the principality / torsion test it is compared against
`div(g)`. `f`/`basis` are unused by the reduction itself (the lattice data is in `I`) but kept for the uniform
`f basis I` signature of the divisor API. -/
def idealReduce (_f : CPolyG (QFunNZG ℚ)) (_basis : List (CPolyG (QFunNZG ℚ)))
    (I : GenDivisor) : GenDivisor :=
  let (δ, N) := idealClear I
  let H := canonHNF ((hermiteRowReduce N).filter (fun row => !row.all cisZeroG))
  let dd := cnormG δ
  -- read back as the fractional ideal (1/δ)·Ĥ, then reduce every entry to lowest terms (`qReduceMat`,
  -- value-preserving via `toQFunNZG_qReduce`) so the reduced representative carries no swollen factors
  qReduceMat (H.map (fun row => row.map (fun p =>
    if h : cisZeroG dd = false then qReduceNZG (qxOfFrac p dd h) else qxOfNum p)))

/-! ### Principality: is the ideal `g·O` (the trivial Pic class)? (`genCandidates`, `isPrincipalIdeal`)

A fractional ideal `I` is **principal** (its Pic class is trivial, `[I] = 0`) iff `I = g·O = div(g)` for some
`g ∈ K(x, y)` — the general analogue of "is the reduced Cantor divisor the identity `(1, 0)`?". For a principal
ideal the generator `g` is (up to a unit) one of the **module generators of the reduced ideal**, i.e. one of the
**canonical-HNF rows** reconstructed as a `K(x, y)` element (`wToAf basis`): on `y² = x³+1`, `P³`'s first
canonical-HNF row is `1 − y` and `div(1 − y) = P³`; on `y³ = x²`, `div(y)`'s canonical-HNF rows are `x·1`, `y`,
`x·(y²/x)` and the *second* row `y` is the generator. So we take all canonical-HNF rows as **candidate
generators** `genCandidates basis I` and test `canonHNFEq I (div g)` for each. This is **sound**: a `true` means
`I` genuinely equals `div(g)`, hence is principal — the order search never over-reports torsion. (The
`afLogArgSolveWf`-style single-generator test: `I = g·O` iff a single `g` generates the whole ideal; here the
candidate `g`s are read off the canonical reduced ideal.) -/

/-- The candidate single generators of a fractional ideal `genCandidates basis I`: each **canonical-HNF row**
of `I`'s cleared integral matrix, reconstructed as a `K(x, y)` element (`wToAf basis (row.map qxOfNum)`) — the
reduced module generators of `I`. For a **principal** ideal `g·O`, the generator `g` is among these up to a unit
(some HNF row reconstructs to a unit multiple of `g`); for a non-principal ideal no candidate `g` has `div(g) =
I`. The principality probes behind `isPrincipalIdeal`. -/
def genCandidates (basis : List (CPolyG (QFunNZG ℚ))) (I : GenDivisor) : List (CPolyG (QFunNZG ℚ)) :=
  let H := canonHNF ((hermiteRowReduce (idealClear I).2).filter (fun row => !row.all cisZeroG))
  H.map (fun row => wToAf basis (row.map qxOfNum))

/-- `true` iff the fractional ideal `I` is principal `isPrincipalIdeal f basis I`: `I = g·O = div(g)` for
**some** candidate generator `g ∈ genCandidates basis I` (a canonical-HNF row of `I`), tested by `canonHNFEq I
(principalDivisor f basis g)`. **Sound** — a `true` means `I` genuinely equals `div(g)`, so `[I] = 0` in
`Pic⁰(C)`. The principality oracle of the torsion test (Trager Ch. 6): `m·δ` is principal iff `isPrincipalIdeal
(m·δ) = true`, the condition behind `order(δ) = smallest m with m·δ principal`. -/
def isPrincipalIdeal (f : CPolyG (QFunNZG ℚ)) (basis : List (CPolyG (QFunNZG ℚ)))
    (I : GenDivisor) : Bool :=
  (genCandidates basis I).any (fun g => canonHNFEq I (principalDivisor f basis g))

/-! ### The order search `genDivisorOrder` (the smallest `m ≥ 1` with `m·δ` principal)

The **order** of a divisor class `δ` is the smallest `m ≥ 1` with `m·δ` principal (the trivial class). We search
`1·δ, 2·δ, 3·δ, …` by the running accumulator `acc ← idealProduct δ acc` (each step one Pic composition), and
at each `m` test `isPrincipalIdeal acc`; on a hit return `some m`, else recurse. `fuel` bounds how many
multiples are tried (the torsion-subgroup-size ceiling — the good-reduction bound below makes this terminating);
`none` if no `m ≤ fuel` works. This is the **general lift** of the hyperelliptic `cantorOrder` (smallest `n`
with `n·D = O`), on the fractional-ideal representation: `idealProduct` replaces `cantorAdd`, `isPrincipalIdeal`
replaces `mumfordNormEq · mumfordIdentity`. -/

/-- Order-search loop `genDivisorOrderAux fuel f basis δ acc n`: with `acc = n·δ` already computed (`acc`
the running Pic multiple), test `(n+1)·δ = idealProduct δ acc` for principality (`isPrincipalIdeal`); on a hit
return `some (n+1)`, else recurse with the new accumulator. `fuel` bounds the remaining multiples to try. The
general analogue of `cantorOrderAux`. -/
def genDivisorOrderAux (f : CPolyG (QFunNZG ℚ)) (basis : List (CPolyG (QFunNZG ℚ))) (δ : GenDivisor) :
    ℕ → GenDivisor → ℕ → Option ℕ
  | 0, _, _ => none
  | fuel + 1, acc, n =>
    let acc := idealProduct f basis δ acc
    if isPrincipalIdeal f basis acc then some (n + 1)
    else genDivisorOrderAux f basis δ fuel acc (n + 1)

/-- The general divisor order `genDivisorOrder fuel f basis δ = some m` — the smallest `m ≥ 1` with `m·δ`
**principal** (the trivial class = the order `O`) in `Pic⁰(C)` for the arbitrary curve `K(x, y) = K(x)[y]/(f)`,
searching `1·δ, 2·δ, …` up to `fuel` multiples (each `idealProduct δ ·`, tested by `isPrincipalIdeal`). `none`
if no `m ≤ fuel` works — the order exceeds the fuel (a non-torsion candidate). The **torsion / point-of-finite-
order** quantity (Trager Ch. 6): `some m` says `δ` is `m`-torsion ⟹ the algebraic-function integral is
elementary with a `(1/m)·log` term. The **general lift of the hyperelliptic `cantorOrder`** from the Mumford
pair to the fractional-ideal-over-the-integral-basis representation: `idealProduct` for the Pic composition,
`isPrincipalIdeal` (reduced class `= O`) for the order test. -/
def genDivisorOrder (fuel : ℕ) (f : CPolyG (QFunNZG ℚ)) (basis : List (CPolyG (QFunNZG ℚ)))
    (δ : GenDivisor) : Option ℕ :=
  genDivisorOrderAux f basis δ fuel (idealIdentity (cdegG f)) 0

/-- Is `δ` torsion within `fuel` `genIsTorsion fuel f basis δ`: `true` iff `genDivisorOrder` finds a finite
order `≤ fuel`. A `Bool` view of `genDivisorOrder` for the decision wrappers (the general-curve analogue of
the hyperelliptic `cantorOrder`-`isSome` torsion test). -/
def genIsTorsion (fuel : ℕ) (f : CPolyG (QFunNZG ℚ)) (basis : List (CPolyG (QFunNZG ℚ)))
    (δ : GenDivisor) : Bool :=
  (genDivisorOrder fuel f basis δ).isSome

end CPolyG

/-! ## Validation: principal classes have order 1 (`native_decide`)

On the cuspidal cubic `y³ = x²` (`gcuspCubicF`, integral basis `[1, y, y²/x]`), the principal divisors `div(y)`,
`div(y²)` and the identity `O` are all **trivial** Pic classes (`[div g] = 0`), so `isPrincipalIdeal` is `true`
and `genDivisorOrder` is `some 1`. This is the easy end of the order spectrum — a principal class is its own
generator. -/

open CPolyG

/-- `div(y)` is principal and has order 1 on `y³ = x²` (`native_decide`): `isPrincipalIdeal (div y) =
true` (one candidate generator `genCandidates` recovers `y` up to a unit — the second canonical-HNF row of
`y·O` is `y` — so `canonHNFEq (div y) (div y)`), and `genDivisorOrder (div y) = some 1` (`1·div(y) = div(y)` is
already principal). A principal class is trivial in `Pic⁰(C)` ⟹ order 1. -/
theorem gdo_divY_principal_order1 :
    (isPrincipalIdeal gcuspCubicF gcuspCubicBasis gdDivY
      && (genDivisorOrder 4 gcuspCubicF gcuspCubicBasis gdDivY == some 1)) = true := by native_decide

/-- The identity `O` has order 1 on `y³ = x²` (`native_decide`): `isPrincipalIdeal O = true` (`O = div(1)`
is principal) and `genDivisorOrder O = some 1` — the trivial torsion order of the Pic neutral element, the
general analogue of `cantorOrder mumfordIdentity = some 1`. -/
theorem gdo_identity_order1 :
    (isPrincipalIdeal gcuspCubicF gcuspCubicBasis gdIdentity
      && (genDivisorOrder 4 gcuspCubicF gcuspCubicBasis gdIdentity == some 1)) = true := by native_decide

/-! ## Hyperelliptic conservativity: the 3-torsion `(0,1) − ∞` on `y² = x³ + 1` (`native_decide`)

The headline validation: the GENERAL divisor order **recovers the hyperelliptic answer**. On the elliptic curve
`y² = x³ + 1` (which the general fractional-ideal machinery handles as the degree-2 case — its integral basis
is `[1, y]`), the inflection point `(0, 1)` gives the **3-torsion** class `[(0,1) − ∞]`, matching
`cantorMul_pt01_order3` / `cantorOrder hypPt01 = some 3` in `ComputableDivisorOrder`.

In the **ideal class group** (≅ `Pic⁰(C)` for this one-point-at-infinity curve), the class `[(0,1) − ∞]` is
represented by the **prime ideal of the place `(0, 1)`**: `P = (x, y − 1)·O` (the functions vanishing at
`(0,1)`), a degree-1 integral ideal with `[P] ↔ [(0,1) − ∞]`. Its order in the ideal class group is 3:
`P` and `P²` are non-principal, but `P³ = (y − 1)·O = div(y − 1)` **is** principal — because
`div(y − 1) = 3·(0,1) − 3·∞` (the function `y − 1` has a triple zero at `(0,1)` and triple pole at `∞`). So
`genDivisorOrder δ = some 3` for `δ = P`, with the ladder `reduced(δ) ≠ O`, `reduced(2δ) ≠ O`,
`reduced(3δ) = div(y−1)` principal. -/

/-- The curve `f = y² − (x³ + 1) ∈ ℚ(x)[y]` (`[−(x³+1), 0, 1]`), the elliptic curve `y² = x³ + 1` — the same
radicand as the hyperelliptic `hypRhoX3p1`, here as the `CPolyG (QFunNZG ℚ)` for the general fractional-ideal
machinery (degree-2 case). -/
def hcubeF : CPolyG (QFunNZG ℚ) := [qxOfNum [-1, 0, 0, -1], CField.zero, CField.one]

/-- The integral basis `[1, y]` of `y² = x³ + 1` (no finite poles — the power basis, since `x³ + 1` is
squarefree). -/
def hcubeBasis : List (CPolyG (QFunNZG ℚ)) := integralBasis hcubeF

/-- The 3-torsion divisor `δ = [(0,1) − ∞]` as the place ideal `P = (x, y − 1)·O` on `y² = x³ + 1`, built from
its `O`-generators `x·1, x·y, (y−1)·1, (y−1)·y` (in the `[1, y]` coordinates: `[x,0]`, `[0,x]`, `[−1,1]`,
`[x³+1,−1]`) reduced to a `2×2` ideal matrix by one `idealProduct` with the identity (`idealProduct`'s
clear-and-Hermite reduction of the `4` generators to `2`). The general-curve representation of the 3-torsion
class of the inflection point `(0,1)`. -/
def hcubeTorsionDiv : GenDivisor :=
  idealProduct hcubeF hcubeBasis
    [ [qxOfNum [0, 1], CField.zero],
      [CField.zero, qxOfNum [0, 1]],
      [qxOfNum [-1], qxOfNum [1]],
      [qxOfNum [1, 0, 0, 1], qxOfNum [-1]] ]
    (idealIdentity 2)

-- Sanity print: δ = P = (x, y−1) as a [w]=[1,y] ideal matrix (Hermite-reduced).
#eval hcubeTorsionDiv.map (fun row => row.map (fun z => ((z.1.1 : List ℚ), (z.1.2 : List ℚ))))

-- Sanity print: the reduced canonical-HNF representative of δ = P (first row `1 − y`, second `x·y`; norm `x`).
#eval (idealReduce hcubeF hcubeBasis hcubeTorsionDiv).map
  (fun row => row.map (fun z => ((z.1.1 : List ℚ), (z.1.2 : List ℚ))))

/-- `δ = P` is NOT principal, `δ²` is NOT principal, but `δ³` IS principal on `y² = x³+1` (`native_decide`):
the order-3 ladder via `isPrincipalIdeal` on the repeated `idealProduct` powers — `P` and `P² = idealProduct δ δ`
are non-principal (`false`), while `P³ = idealProduct δ (idealProduct δ δ)` **is** principal (`true`), because
`P³ = div(y − 1)` (the function `y − 1` realizes `3·(0,1) − 3·∞`). The torsion witness: `3` is the smallest
`m` with `m·δ` principal. -/
theorem hcube_torsion_ladder :
    (isPrincipalIdeal hcubeF hcubeBasis hcubeTorsionDiv == false
      && isPrincipalIdeal hcubeF hcubeBasis
            (idealProduct hcubeF hcubeBasis hcubeTorsionDiv hcubeTorsionDiv) == false
      && isPrincipalIdeal hcubeF hcubeBasis
            (idealProduct hcubeF hcubeBasis hcubeTorsionDiv
              (idealProduct hcubeF hcubeBasis hcubeTorsionDiv hcubeTorsionDiv)) == true) = true := by
  native_decide

/-- HYPERELLIPTIC CONSERVATIVITY: `genDivisorOrder δ = some 3` for the 3-torsion `(0,1) − ∞` on
`y² = x³+1` (`native_decide`): the GENERAL divisor order, run on the fractional-ideal representation `δ = P =
(x, y − 1)·O` of the inflection-point class `[(0,1) − ∞]`, returns **`some 3`** — matching the hyperelliptic
`cantorOrder hypPt01 = some 3` / `cantorMul_pt01_order3` exactly. The search composes `δ, 2δ, 3δ` by repeated
`idealProduct` (the Pic group law) and finds `3δ = div(y − 1)` is the first principal multiple
(`isPrincipalIdeal`). **The general lift of the hyperelliptic `cantorOrder` recovers its answer on a curve both
handle.** -/
theorem hcube_genDivisorOrder_eq3 :
    genDivisorOrder 8 hcubeF hcubeBasis hcubeTorsionDiv = some 3 := by native_decide

/-! ## The general-divisor-order milestone (`native_decide`) -/

/-- THE GENERAL DIVISOR ORDER (TORSION TEST) COMPUTES AND VALIDATES (Trager Ch. 6, "Principal Divisors
and Points of Finite Order", `native_decide`). The general lift of the hyperelliptic `cantorOrder`
(`ComputableDivisorOrder`) onto the **fractional-ideal-over-the-integral-basis** representation
(`ComputableGeneralDivisor`): `idealReduce` (the canonical Hermite-normal-form reduced representative),
`genCandidates` + `isPrincipalIdeal` (the principality oracle: `I = div(g)` for a canonical-HNF-row generator),
and `genDivisorOrder` (the smallest `m` with `m·δ` principal, via repeated `idealProduct`):
* a **principal** class (`div(y)` on the cuspidal cubic `y³ = x²`, and the identity `O`) has order 1
  (`gdo_divY_principal_order1`, `gdo_identity_order1`);
* on `y² = x³ + 1`, the **3-torsion** inflection-point class `[(0,1) − ∞]`, represented as the place ideal
  `P = (x, y − 1)·O`, has **`genDivisorOrder = some 3`** (`hcube_genDivisorOrder_eq3`) — matching the
  hyperelliptic `cantorOrder hypPt01 = some 3` — with the ladder `P, P²` non-principal and `P³ = div(y − 1)`
  principal (`hcube_torsion_ladder`).
**The engine now computes the GENERAL divisor order (the torsion test) for an arbitrary curve** — the general
lift of `cantorOrder`, via repeated `idealProduct` (the Pic group law) + an ideal-reduction / principality
test, recovering the hyperelliptic order on a shared curve. The good-reduction torsion BOUND is the next
piece. -/
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

`genDivisorOrder` searches `m = 1, 2, …` for the first principal multiple `m·δ`, **fuel-bounded**. To make the
search **terminate with a definite "non-torsion"** answer (rather than "no order within fuel"), the fuel must be
a genuine **ceiling** on the order — and the order of a torsion class over `ℚ` is bounded by the size of the
**finite** torsion subgroup of `Pic⁰(C)`, itself bounded via **good reduction modulo a prime `p`** (Trager
Ch. 6 §2 / Davenport):

* reduce the curve `f mod p` over `𝔽_p` for a **good** prime `p` (not dividing the discriminant
  `Resultant(f, f')` or the leading coefficients / denominators of the integral basis);
* compute the **finite** group order `|Pic⁰(C)(𝔽_p)|` — the general analogue of the hyperelliptic point count,
  via the *same* fractional-ideal machinery (`idealProduct` / `isPrincipalIdeal` / `genDivisorOrder`) run over
  `α = ZMod p` (which the `[CField α]`-generic engine supports, exactly as `ComputableDivisorOrder`'s
  `instCFieldZMod` / `mumfordReduceModP` instantiate the hyperelliptic Cantor engine at `ZMod p`);
* the reduction map `Pic⁰(C)(ℚ) → Pic⁰(C)(𝔽_p)` is injective on prime-to-`p` torsion, so `order_ℚ(δ) ∣
  order_{𝔽_p}(δ mod p) ≤ |Pic⁰(C)(𝔽_p)|` — only `m ≤ |Pic⁰(C)(𝔽_p)|` need be tried, and reaching that
  ceiling without a principal multiple **proves** `δ` is non-torsion (⟹ the algebraic-function integral is not
  elementary).

This is the **general lift of `ComputableDivisorOrder`'s `mumfordReduceModP` + `orderModP` + `isTorsionDivisor`
/ `elementarityViaTorsion`** (the hyperelliptic good-reduction torsion decision) from the Mumford pair to the
fractional-ideal representation. It needs: a coefficient-reduction `GenDivisor → GenDivisor over ZMod p` (the
matrix-entry `ℚ → 𝔽_p` map), the `CField (ZMod p)` instantiation of the divisor machinery (the integral basis
mod `p`, `idealProduct` mod `p`), and the count `|Pic⁰(C)(𝔽_p)|` (enumerate the reduced ideal classes, or run
`genDivisorOrder` over `ZMod p` for the ceiling). With it, `genDivisorOrder` becomes a **total** torsion
decision — the general lift of Trager's "points of finite order". Recorded (not formalized) in the
`Sources/Doi_10_1007_b138171` catalog `## NOT YET FORMALIZED` blocks. -/

end DeepWiki.SymbolicIntegration
