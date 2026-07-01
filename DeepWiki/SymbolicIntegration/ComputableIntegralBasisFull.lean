import DeepWiki.SymbolicIntegration.ComputableRound2IntegralBasis
import DeepWiki.SymbolicIntegration.ComputableQFunReduce
import DeepWiki.SymbolicIntegration.ComputableTowerWellFounded

/-! # The FULL general-curve INTEGRAL BASIS: iterating the Ford–Zassenhaus Round-2 step to the maximal
order (Trager, *Integration of Algebraic Functions*, Ch. 2 §1–2, p. 18–26)

`ComputableRound2IntegralBasis` runs **one** Round-2 enlargement of the equation order
`O = [1, y, …, yⁿ⁻¹]` at the first linear bad prime: `pTraceRadical` (residue-field kernel of the trace
matrix mod `p`, Hermite-reduced over `K[x]`), `idealizerBasis` (`Î = (I_p : I_p)`), `round2Step`. On the
cusp `y² − x³` and node `y² − x²(x+1)` it produces `[1, y/x]`, which is already maximal (one step).

This file runs the **outer loop**: iterate the Round-2 step **across all linear bad primes** and **re-base
after each enlargement** until the order stops growing — the fixed point is the **maximal order**, whose
`K[x]`-basis is the **integral basis** (the functions with no finite poles). The single-step idealizer of
`ComputableRound2IntegralBasis` works in *power* coordinates and tacitly assumes the input order IS the
power basis; iterating requires the enlargement of an **arbitrary** order, so this file builds the Round-2
step in the **order's own coordinates**:

* **`ipOCoords f O p a`** — the p-trace-radical `I_p` of an order `O` (a `K(x)`-basis), expressed in the
  `O`-**coordinates** over `K[x]` (where it is **integral**: the kernel lifts are constant `O`-coordinate
  rows and `p·O` is `p` on the diagonal). The kernel mod `p` is the kernel of `traceMatrix f O` evaluated at
  the root `a` (`traceMatrixOrderAtRoot`), Hermite-reduced over `K[x]`.

* **`idealizerOCoords f O ipO`** — the idealizer `Î = (I_p : I_p)` computed entirely in `O`-coordinates: the
  multiply-by-`ιⱼ` matrices use the structure constants of `O` (`afMul ιⱼ ωᵢ` re-expressed in `O`-coords via
  `B⁻¹`), the Trager §1.1 clear-and-Hermite solve runs over `K[x]`, and the `δ·N̂⁻¹` columns (the new order
  in `O`-coords) are mapped back to power coordinates (`Σ uᵢ ωᵢ`). Keeping `I_p` integral in `O`-coords is
  what makes the iteration sound — clearing in power coordinates double-counts the order's denominators. The
  fraction clearing uses **exact division** `(δ·num)/den` (`clearRowExact`), not a raw-numerator read.

* **`integralBasis f`** — the iteration. Start `O = [1, y, …]`; over **all** linear bad primes of the
  *current* order's discriminant `det(traceMatrix f O)` (reduced to lowest terms, `discNumOrder`), run the
  Round-2 step to enlarge `O`; repeat until a full pass leaves `O` unchanged (`isMaximalOrder`). Fuel is the
  discriminant degree (it shrinks by a square each genuine enlargement, so the loop terminates).

**Validations** (`native_decide`):
* **Cusp `y² − x³` / node `y² − x²(x+1)`**: `integralBasis = [1, y/x]` (one step, matching Round-2),
  integral (`(y/x)² ∈ K[x]`) and maximal.
* **★★ Worse cusp `y² − x⁵`** (integral basis `[1, y/x²]`, the `x`-power drops one per step → **two** Round-2
  steps): `integralBasis = [1, y/x²]` with `(y/x²)² = x`; one step alone reaches only `[1, y/x]` and is NOT
  maximal (`cusp5_oneStep_not_maximal`) — a genuinely **multi-step** iteration.
* **★★ Two bad primes `y² − x³(x−1)²`** (bad at `x` AND `x−1`): `integralBasis = [1, y/(x(x−1))]`, enlarging
  at **both** primes in the pass, with `(y/(x(x−1)))² = x` — a genuinely **multi-prime** iteration.

**The engine now computes the FULL general-curve integral basis** — iterating Round-2 to the maximal order
for multi-step and multi-prime curves, not just the one-step cusp/node. The higher-degree (non-linear)
bad-prime residue field `K[x]/(p)` (where the mod-`p` kernel needs arithmetic over a proper field extension,
not a single root evaluation) is documented at the end as the remaining harder case. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace CPolyG

variable {α : Type*} [CField α]

/-! ### Reducing `QFunNZG ℚ` fractions to monic-denominator lowest terms (`qReduceNZG`)

`QFunNZG ℚ ≅ ℚ(x)` is an **unreduced** fraction `num/den` (the engine tests `K`-equality through `isZero`,
never canonicalizing). Across Round-2 iterations the order's coordinate fractions accumulate spurious common
factors (e.g. `x⁸/x⁸` for `1`), which blow up the trace-matrix/discriminant computation and starve the
squarefree factoring of the bad primes. `qReduceNZG` reuses the shared fuel-free reducer internals
(`QFunNZG.reduceNum`/`QFunNZG.reduceDen`, backed by `cgcdMonicWf`) and then normalizes the denominator to
monic — the canonical-form step the iteration applies after each enlargement (`reduceOrder`) and inside the
clearing helpers. -/

/-- **Reduce a `ℚ(x)` element to lowest terms** `qReduceNZG z = (num/g)/(den/g)` with `g = gcd(num, den)`
(`QFunNZG.reduceGcd`, the shared fuel-free monic gcd), then scale numerator and denominator so the denominator
is **monic**. Cancels the spurious common factors that `QFunNZG`'s unreduced `mul`/`add` accumulate; the
canonical form the Round-2 iteration relies on (a zero denominator falls back to the input, never reached for
nonzero `z`). -/
def qReduceNZG (z : QFunNZG ℚ) : QFunNZG ℚ :=
  let num1 := QFunNZG.reduceNum z
  let den1 := cnormG (QFunNZG.reduceDen z)
  if cisZeroG den1 then z
  else
    let c := CField.inv (cleadG den1)
    let num2 := cscaleG c num1
    let den2 := cscaleG c den1
    if h : cisZeroG den2 = false then ⟨(num2, den2), h⟩ else z

/-- **Reduce every entry of an order basis to lowest terms** `reduceOrder O`: `qReduceNZG` on each `ℚ(x)`
coordinate of each basis vector. Applied after each Round-2 enlargement so the running order stays in
canonical form (`1`, `y/x`, `y/x²`, …) rather than the unreduced fractions the idealizer's matrix algebra
produces. -/
def reduceOrder (O : List (CPolyG (QFunNZG ℚ))) : List (CPolyG (QFunNZG ℚ)) :=
  O.map (fun row => row.map qReduceNZG)

/-! ### The p-trace-radical of an order, in the ORDER's coordinates (`ipOCoords`)

For a linear bad prime `p = x − a` and an order `O = [ω₀, …, ωₙ₋₁]` (a `K(x)`-basis), the p-trace-radical
`I_p = { z = Σ cᵢ ωᵢ ∈ O : p | Σᵢ cᵢ Tr(ωᵢ ωⱼ) ∀j }` is, mod `p`, the **kernel of `T = traceMatrix f O`
evaluated at `a`** (over the residue field `K`), in the `O`-coordinates `(c₀, …, c_{n−1})`. Crucially, in
`O`-coordinates `I_p` is an **integral** `K[x]`-lattice: the kernel vectors are constant rows, and `p·O` is
`p` on the diagonal. So `ipOCoords` returns `I_p`'s `K[x]`-basis in `O`-coordinates — a clean `PolyMatrix ℚ`,
no denominators — Hermite-reduced. (Working in power coordinates would make `I_p` carry the order's
denominators and double-count them in the idealizer's clearing — the bug the `O`-coordinate formulation
avoids.) For `O = powerBasis f` the `O`-coordinates ARE the power coordinates, so this is the power-basis
p-trace-radical. -/

/-- **The trace matrix of an order `O` reduced at a linear prime root `a`** `traceMatrixOrderAtRoot f O a`:
the `n×n` `ℚ`-matrix `traceMatrix f O` with every `ℚ(x)` entry evaluated at `x = a` (`qEvalAtRoot`), i.e.
`T mod (x − a)` over the residue field `ℚ` for the order `O`. Its kernel over `ℚ` (in `O`-coordinates) is the
p-trace-radical mod `p`. For `O = powerBasis f` this is `traceMatrixAtRoot f a`. -/
def traceMatrixOrderAtRoot (f : CPolyG (QFunNZG ℚ)) (O : List (CPolyG (QFunNZG ℚ))) (a : ℚ) :
    List (List ℚ) :=
  (traceMatrix f O).map (fun row => row.map (fun e => qEvalAtRoot e a))

/-- **The p-trace-radical `I_p` of an order `O`, in `O`-coordinates** `ipOCoords f O p a`: a `K[x]`-basis of
`I_p = { z ∈ O : p | Tr(z·ωⱼ) ∀j }` as a `PolyMatrix ℚ` (rows = basis vectors in the `O`-coordinates, entries
`∈ ℚ[x]`). The kernel of `traceMatrixOrderAtRoot f O a` over `ℚ` (`kernelBasisG`) gives the residue-class
generators as constant `O`-coordinate rows; together with the `p·O` generators (`p` on the diagonal),
`hermiteRowReduce` triangularizes to the `K[x]`-basis (nonzero rows). Integral in `O`-coordinates (no
denominators); `idealizerOCoords` lifts them back through `O`. For `O = powerBasis f` this is the power-basis
p-trace-radical. -/
def ipOCoords (f : CPolyG (QFunNZG ℚ)) (O : List (CPolyG (QFunNZG ℚ))) (p : CPolyG ℚ) (a : ℚ) :
    PolyMatrix ℚ :=
  let n := cdegG f
  let kers : List (List ℚ) := kernelBasisG n (traceMatrixOrderAtRoot f O a)
  let kerRows : PolyMatrix ℚ := kers.map (fun v => (List.range n).map (fun i => [v.getD i 0]))
  let pRows : PolyMatrix ℚ := (List.range n).map (fun i =>
    (List.range n).map (fun j => if i = j then p else ([] : CPolyG ℚ)))
  let reduced := hermiteRowReduce (kerRows ++ pRows)
  reduced.filter (fun row => !row.all cisZeroG)

/-! ### The idealizer of an arbitrary order, in `O`-coordinates (`idealizerOCoords`)

The enlarged order is the idealizer `Î = (I_p : I_p) = { z ∈ K(x, y) : z·I_p ⊆ I_p }`. Computed in
`O`-coordinates: with `B` the `O`-to-power change of basis (column `k` = `ωₖ` in power coords) and `Binv =
B⁻¹` (power → `O`), the multiply-by-`ιⱼ` matrix in `O`-coordinates has column `i` = `ιⱼ·ωᵢ` re-expressed in
`O`-coords (`toOCoords Binv (afMul f ιⱼ ωᵢ)`). Re-expressing further in the `I_p` basis (`BipInv`, the inverse
of the `I_p`-in-`O`-coords matrix) and stacking over `j` gives `M` (`n²×n` over `K(x)`); clearing to a common
denominator `δ` by **exact division** and Hermite-reducing over `K[x]`, the first `n` rows form `N̂`, and the
**columns of `δ·N̂⁻¹`** are the idealizer basis in `O`-coordinates — mapped back to power coordinates by
`Σ uᵢ ωᵢ`. Returns `O` unchanged if any inverse is singular. -/

/-- **The `O`-to-power change-of-basis matrix** `orderToPowerMatrix n O`: the `n×n` `ℚ(x)`-matrix whose
column `k` is `ωₖ` in power coordinates (`B[r][k] = coeff_r(ωₖ)`), the change of basis from the `O`-basis to
the power basis `[1, y, …]`. Its inverse maps power coordinates to `O`-coordinates. -/
def orderToPowerMatrix (n : ℕ) (O : List (CPolyG (QFunNZG ℚ))) : List (List (QFunNZG ℚ)) :=
  (List.range n).map (fun r => (List.range n).map (fun k => (O.getD k []).getD r CField.zero))

/-- **The `O`-coordinates of a `K(x, y)` element** `toOCoords Binv n z = Binv · (z in power coords)`: apply
the power → `O` change of basis `Binv = (orderToPowerMatrix)⁻¹` to the power-coordinate vector of `z`, giving
its coordinates in the order basis `O`. -/
def toOCoords (Binv : List (List (QFunNZG ℚ))) (n : ℕ) (z : CPolyG (QFunNZG ℚ)) : List (QFunNZG ℚ) :=
  (List.range n).map (fun r =>
    (List.range n).foldl (fun acc c =>
      CField.add acc (CField.mul ((Binv.getD r []).getD c CField.zero) (z.getD c CField.zero)))
      CField.zero)

/-- **The common denominator of a `K(x)`-matrix (reduced)** `commonDenomG M = ∏ (distinct reduced entry
denominators)` (`CPolyG ℚ`): for each entry, reduce (`qReduceNZG`) and multiply in its monic denominator
unless it is `1`. A coarse common multiple (product), sufficient for the Hermite-mod-`δ` solve (invariant
under enlarging `δ`). The `O`-coordinate analogue of `commonDenom`, reducing first so the product stays
small. -/
def commonDenomG (M : List (List (QFunNZG ℚ))) : CPolyG ℚ :=
  M.foldl (fun acc row =>
    row.foldl (fun a z =>
      let den := cnormG (qReduceNZG z).1.2
      if cisZeroG den || cisZeroG (csubG den [CField.one]) then a else cmulG a den)
      acc) [CField.one]

/-- **Clear a `K(x)`-row to a `K[x]`-row at `δ` by EXACT division** `clearRowExact δ row = [(δ·numᵢ)/denᵢ]`:
reduce each entry `numᵢ/denᵢ` (`qReduceNZG`), then compute `(δ·numᵢ)/denᵢ` by **exact** polynomial division
(`cdivWf`, valid since `denᵢ | δ` when `δ` is a common denominator). Unlike a raw-numerator read of `δ·z`
(which keeps `z`'s denominator and over-counts), this produces the genuine integral row `δ·row`. -/
def clearRowExact (δ : CPolyG ℚ) (row : List (QFunNZG ℚ)) : List (CPolyG ℚ) :=
  row.map (fun z =>
    let zz := qReduceNZG z
    let num := zz.1.1
    let den := cnormG zz.1.2
    cdivWf (cmulG δ num) den)

/-- **The idealizer `Î = (I_p : I_p)` of an order `O`, as a new `K(x)` order basis** `idealizerOCoords f O
ipO`. `O` is the current order's `K(x, y)` basis and `ipO` is `I_p` in `O`-coordinates (`ipOCoords` output).
Returns the idealizer's basis as `n` `K(x, y)` elements (power coordinates), per Trager §2 p. 26, computed in
`O`-coordinates:

* `B = orderToPowerMatrix O`, `Binv = B⁻¹` (power → `O`); the `I_p` basis elements `ιₖ = Σᵢ ipO[k][i]·ωᵢ`;
* `Bip` = the `I_p`-in-`O`-coords matrix (`column k = toOCoords Binv ιₖ`), `BipInv = Bip⁻¹`;
* for each `ιⱼ`, the multiply-by-`ιⱼ` matrix in `O`-coords (`column i = toOCoords Binv (afMul f ιⱼ ωᵢ)`),
  re-expressed in the `I_p` basis (`BipInv · ·`), stacked into `M` (`n²×n`);
* clear `M` to `K[x]` by `δ = commonDenomG M` via **exact division** (`clearRowExact`), Hermite-reduce, take
  the first `n` rows `N̂`, invert (`matInvG`), scale by `δ`: the **columns of `δ·N̂⁻¹`** are the idealizer in
  `O`-coords, mapped back to power coords by `Σ uᵢ ωᵢ`.

Returns `O` unchanged if `B`, `Bip`, or `N̂` is singular (a safe no-op). For `O = powerBasis f` (`B = Binv =
Iₙ`) this is the power-basis idealizer. -/
def idealizerOCoords (f : CPolyG (QFunNZG ℚ)) (O : List (CPolyG (QFunNZG ℚ))) (ipO : PolyMatrix ℚ) :
    List (CPolyG (QFunNZG ℚ)) :=
  let n := cdegG f
  let B := orderToPowerMatrix n O
  match matInvG n B with
  | none => O
  | some Binv =>
    let ipElems : List (CPolyG (QFunNZG ℚ)) := ipO.map (fun row =>
      (List.range n).foldl (fun acc i =>
        caddG acc (cscaleG (qxOfNum (row.getD i [])) (O.getD i []))) ([] : CPolyG (QFunNZG ℚ)))
    let Bip : List (List (QFunNZG ℚ)) := (List.range n).map (fun r =>
      (List.range n).map (fun k => (toOCoords Binv n (ipElems.getD k [])).getD r CField.zero))
    match matInvG n Bip with
    | none => O
    | some BipInv =>
      let M : List (List (QFunNZG ℚ)) :=
        (List.range n).foldr (fun j acc =>
          let ιj := ipElems.getD j []
          let multO : List (List (QFunNZG ℚ)) := (List.range n).map (fun r =>
            (List.range n).map (fun i =>
              (toOCoords Binv n (afMul f ιj (O.getD i []))).getD r CField.zero))
          (matMulG BipInv multO) ++ acc) []
      let δ : CPolyG ℚ := commonDenomG M
      let N : PolyMatrix ℚ := M.map (clearRowExact δ)
      let nz := (hermiteRowReduce N).filter (fun row => !row.all cisZeroG)
      let Nhat : List (List (QFunNZG ℚ)) := (List.range n).map (fun i =>
        (List.range n).map (fun j => qxOfNum ((nz.getD i []).getD j [])))
      match matInvG n Nhat with
      | none => O
      | some NhatInv =>
        let δq : QFunNZG ℚ := qxOfNum δ
        (List.range n).map (fun col =>
          let uO : List (QFunNZG ℚ) := (List.range n).map (fun row =>
            CField.mul δq ((NhatInv.getD row []).getD col CField.zero))
          (List.range n).foldl (fun acc i =>
            caddG acc (cscaleG (uO.getD i CField.zero) (O.getD i []))) ([] : CPolyG (QFunNZG ℚ)))

end CPolyG

/-! ### The outer loop: `integralBasis`, `isMaximalOrder`

The integral-basis algorithm (Trager p. 21) iterates the Round-2 enlargement to a fixed point. We carry the
running order `O` as a `K(x)`-basis in power-basis coordinates. One step `round2StepOrderAt` enlarges `O` at
a given linear prime (`ipOCoords` + `idealizerOCoords`); a pass `round2Pass` enlarges `O` at **all** bad
primes of the current order's discriminant (reduced to lowest terms); the loop `integralBasisLoop` iterates
passes until `O` no longer grows. -/

open CPolyG

namespace CPolyG

/-- **The discriminant of an order `O`, numerator reduced to lowest terms** `discNumOrder f O`: the numerator
of `det(traceMatrix f O) ∈ K(x)` after cancelling `gcd(num, den)` through the shared fuel-free reducer. For `O =
powerBasis f` this is `discNum f`; after an enlargement `O → Î` it is `disc(f)/(det M)²`, which **shrinks by
the square of the change of basis** — the termination measure. Reducing to lowest terms is essential: the
unreduced determinant of an enlarged order's trace matrix is a huge polynomial whose squarefree factoring
fails (and misses the bad primes). -/
def discNumOrder (f : CPolyG (QFunNZG ℚ)) (O : List (CPolyG (QFunNZG ℚ))) : CPolyG ℚ :=
  let z := fieldDet (traceMatrix f O)
  cnormG (QFunNZG.reduceNum z)

/-- **The bad primes of an order `O`** `badPrimesOrder f O`: the distinct monic squarefree factors `p`
of the **order's** reduced discriminant numerator (`discNumOrder`) with `p² | d` — the primes where `O` may
still be non-maximal. For `O = powerBasis f` this is the fuel-free divisibility-test analogue of
`badPrimes fuel f`. Drives each pass of the outer loop. -/
def badPrimesOrder (f : CPolyG (QFunNZG ℚ)) (O : List (CPolyG (QFunNZG ℚ))) :
    List (CPolyG ℚ) :=
  let d := discNumOrder f O
  let distinct := ((cSqfreeYunFFGWf d).map cmonicG).filter (fun p => 0 < cdegG p)
  distinct.filter (fun p => cisZeroG (cmodWf d (cmulG p p)))

/-- **`true` iff two order bases agree** `orderEq n O1 O2`: each `O1ᵢ` is `cisZeroG`-equal to `O2ᵢ`, entry by
entry over the `n` power-basis coordinates. The iteration's fixed-point test (whether an enlargement grew the
order). -/
def orderEq (n : ℕ) (O1 O2 : List (CPolyG (QFunNZG ℚ))) : Bool :=
  (List.range n).all (fun i => cisZeroG (csubG (O1.getD i []) (O2.getD i [])))

/-- **One Round-2 enlargement of an order `O` at a given linear prime** `round2StepOrderAt f O p`: read the
root `a = −p₀` of the monic linear `p = [−a, 1]`, compute the p-trace-radical `ipOCoords f O p a` and its
idealizer `idealizerOCoords f O (·)`, reducing the result to canonical form (`reduceOrder`). The single-prime
kernel of the outer loop. -/
def round2StepOrderAt (f : CPolyG (QFunNZG ℚ)) (O : List (CPolyG (QFunNZG ℚ))) (p : CPolyG ℚ) :
    List (CPolyG (QFunNZG ℚ)) :=
  let pm := cmonicG p
  let a : ℚ := CField.neg (pm.getD 0 CField.zero)
  reduceOrder (idealizerOCoords f O (ipOCoords f O pm a))

/-- **One full pass of Round-2 over ALL bad primes of `O`** `round2Pass f O = (O', grew)`: fold
`round2StepOrderAt` over every bad prime of the current order (`badPrimesOrder`), enlarging `O` at each in
turn, and report whether the pass changed the order (`grew = ¬ orderEq O O'`). Enlarging at all bad primes in
one pass realizes the product-of-bad-primes enlargement of Trager p. 24 as a sequential fold. -/
def round2Pass (f : CPolyG (QFunNZG ℚ)) (O : List (CPolyG (QFunNZG ℚ))) :
    List (CPolyG (QFunNZG ℚ)) × Bool :=
  let n := cdegG f
  let O' := (badPrimesOrder f O).foldl (fun acc p => round2StepOrderAt f acc p) O
  (O', !orderEq n O O')

/-- **The Round-2 iteration loop** `integralBasisLoop fuel f O`: run `round2Pass` repeatedly, replacing `O`
by the enlarged order, until a pass leaves `O` unchanged (`grew = false`) — the maximal order. `fuel : ℕ`
bounds the iteration count (the discriminant degree: each genuine enlargement divides the discriminant by a
nontrivial square, so its degree strictly drops). Structural recursion on `fuel`. -/
def integralBasisLoop (fuel : ℕ) (f : CPolyG (QFunNZG ℚ)) :
    List (CPolyG (QFunNZG ℚ)) → List (CPolyG (QFunNZG ℚ))
  | O =>
    match fuel with
    | 0 => O
    | fuel + 1 =>
      let (O', grew) := round2Pass f O
      if grew then integralBasisLoop fuel f O' else O'

/-- **The general-curve INTEGRAL BASIS** `integralBasis f`: iterate the Ford–Zassenhaus Round-2 step to the
maximal order. Start from the equation order `O = [1, y, …, yⁿ⁻¹]` (`powerBasis f`) and run
`integralBasisLoop` — over **all** linear bad primes, re-basing after each enlargement — to a fixed point.
The result is the `K[x]`-basis of the maximal order = the integral basis of `K(x, y) = K(x)[y]/(f)` (the
functions with no finite poles), in power-basis coordinates, reduced to canonical form. Fuel `= cdegG
(discNum f) + 1`. For the cusp/node it returns `[1, y/x]` in one step; for the worse cusp `y² − x⁵` it takes
two steps to reach `[1, y/x²]`; for `y² − x³(x−1)²` it enlarges at the two bad primes `x` and `x − 1` to
`[1, y/(x(x−1))]`. -/
def integralBasis (f : CPolyG (QFunNZG ℚ)) : List (CPolyG (QFunNZG ℚ)) :=
  let fuel := cdegG (discNum f) + 1
  reduceOrder (integralBasisLoop fuel f (powerBasis f))

/-- **`true` iff `O` is the maximal order** `isMaximalOrder f O`: a Round-2 pass over `O` does not grow
it (`¬ (round2Pass f O).2`) — the integral-basis termination test. When `true`, `O` is integrally closed
(no finite-pole functions outside it); `integralBasis` returns an order on which this holds. -/
def isMaximalOrder (f : CPolyG (QFunNZG ℚ)) (O : List (CPolyG (QFunNZG ℚ))) : Bool :=
  !(round2Pass f O).2

end CPolyG

/-! ### ★ The cusp `y² − x³` and node `y² − x²(x+1)`: `integralBasis = [1, y/x]` in one step (`native_decide`)

The headline curves of `ComputableRound2IntegralBasis` reach their maximal order in a single Round-2 step.
The full `integralBasis` iteration reproduces `[1, y/x]` (bad prime `x`, one enlargement, then a fixed point)
and `isMaximalOrder` on the result is `true`. -/

open CPolyG

-- Sanity print: the cusp integral basis (coordinate vectors over ℚ(x); expected `[1,0]`, `[0,1/x]`).
#eval (integralBasis cuspF).map (fun b => b.map (fun z => ((z.1.1 : List ℚ), (z.1.2 : List ℚ))))

/-- The computed cusp integral-basis generator `y/x` = the second basis vector of `integralBasis cuspF`. -/
def cuspIBGen : CPolyG (QFunNZG ℚ) := (integralBasis cuspF).getD 1 []

/-- **★ The cusp integral basis is `[1, y/x]`, integral (`(y/x)² = x`) and maximal** (`native_decide`): the
full Round-2 iteration `integralBasis (y² − x³)` returns `[1, y/x]` (first vector `1`, second `[0, 1/x] =
y/x`), the generator is integral (`afMul cuspF (y/x) (y/x) = x`), and `isMaximalOrder` is `true` — the
iteration reaches the maximal order and stops, matching the one-step `round2Step` result. -/
theorem cusp_integralBasis_eq :
    (cisZeroG (csubG cuspIBGen [CField.zero, qxOfFrac [1] [0, 1] (by decide)])
      && cisZeroG (csubG ((integralBasis cuspF).getD 0 []) [CField.one])
      && cisZeroG (csubG (afMul cuspF cuspIBGen cuspIBGen) [qxOfNum [0, 1]])
      && isMaximalOrder cuspF (integralBasis cuspF)) = true := by native_decide

-- Sanity print: the node integral basis (expected `[1,0]`, `[0,1/x]`).
#eval (integralBasis nodeF).map (fun b => b.map (fun z => ((z.1.1 : List ℚ), (z.1.2 : List ℚ))))

/-- The computed node integral-basis generator `y/x` = the second basis vector of `integralBasis nodeF`. -/
def nodeIBGen : CPolyG (QFunNZG ℚ) := (integralBasis nodeF).getD 1 []

/-- **★ The node integral basis is `[1, y/x]`, integral (`(y/x)² = x + 1`) and maximal** (`native_decide`):
`integralBasis (y² − x²(x+1))` returns `[1, y/x]` (second vector `[0, 1/x]`, first `1`); the generator is
integral with relation `(y/x)² = x + 1` (`afMul = [1, 1]`); and `isMaximalOrder` is `true`. The iteration
matches the one-step node result. -/
theorem node_integralBasis_eq :
    (cisZeroG (csubG nodeIBGen [CField.zero, qxOfFrac [1] [0, 1] (by decide)])
      && cisZeroG (csubG ((integralBasis nodeF).getD 0 []) [CField.one])
      && cisZeroG (csubG (afMul nodeF nodeIBGen nodeIBGen) [qxOfNum [1, 1]])
      && isMaximalOrder nodeF (integralBasis nodeF)) = true := by native_decide

/-! ### ★★ A genuinely MULTI-STEP curve: the worse cusp `y² − x⁵`, integral basis `[1, y/x²]` (`native_decide`)

The worse cusp `f = y² − x⁵` over `ℚ(x)`: `a₀ = −x⁵`, discriminant `−4a₀ = 4x⁵`, bad prime `x` (`x² | 4x⁵`).
The maximal order is `[1, y/x²]`: `(y/x²)² = y²/x⁴ = x⁵/x⁴ = x`, integral. But `y/x` is **not** the end —
`(y/x)² = x⁵/x² = x³` is integral, so one Round-2 step enlarges `[1, y] → [1, y/x]`, and a **second** step is
needed because `[1, y/x]` is *still* non-maximal: its discriminant is `4x⁵/x² = 4x³` (the `x`-power dropped by
one), still flagging `p = x`, and `(y/x)/x = y/x²` is integral. So `integralBasis` iterates **twice**:
`[1, y] → [1, y/x] → [1, y/x²]`. This is the first genuinely multi-step example — the iteration loop (not a
single Round-2 step) is what reaches the answer. -/

/-- The worse cusp curve `f = y² − x⁵ ∈ ℚ(x)[y]` (`a₀ = −x⁵`, `a₁ = 0`, monic), the `CPolyG (QFunNZG ℚ)`
`[−x⁵, 0, 1]`. A higher-order cusp; the integral basis is `[1, y/x²]`, reached in **two** Round-2 steps
(`[1, y] → [1, y/x] → [1, y/x²]`, the `x`-power dropping one per step). -/
def cusp5F : CPolyG (QFunNZG ℚ) :=
  [qxOfNum [0, 0, 0, 0, 0, -1], CField.zero, CField.one]

/-- The computed worse-cusp integral-basis generator `y/x²` = the second basis vector of
`integralBasis cusp5F` (`= [0, 1/x²]` in the `[1, y]` coords). -/
def cusp5IBGen : CPolyG (QFunNZG ℚ) := (integralBasis cusp5F).getD 1 []

-- Sanity print: the worse-cusp discriminant numerator (expected `4x⁵ = [0,0,0,0,0,4]`).
#eval (discNum cusp5F : List ℚ)

-- Sanity print: a SINGLE round2Step on the worse cusp (expected `[1, y/x]`, NOT yet maximal).
#eval (round2Step 12 cusp5F).1.map (fun b => b.map (fun z => ((z.1.1 : List ℚ), (z.1.2 : List ℚ))))

-- Sanity print: the FULL integralBasis on the worse cusp (expected `[1, y/x²]`).
#eval (integralBasis cusp5F).map (fun b => b.map (fun z => ((z.1.1 : List ℚ), (z.1.2 : List ℚ))))

/-- **★★ A single Round-2 step on `y² − x⁵` reaches only `[1, y/x]`, NOT the maximal order** (`native_decide`):
`round2Step cusp5F` enlarges `[1, y] → [1, y/x]` (`.2 = true`, second vector `[0, 1/x]`), but this is **not**
yet the integral basis — `[1, y/x]` is still non-maximal (`(y/x)/x = y/x²` is integral, so `isMaximalOrder`
is `false`). This is exactly why the outer iteration loop is needed: one step is not enough for a worse
cusp. -/
theorem cusp5_oneStep_not_maximal :
    (((round2Step 12 cusp5F).2)
      && cisZeroG (csubG ((round2Step 12 cusp5F).1.getD 1 [])
            [CField.zero, qxOfFrac [1] [0, 1] (by decide)])
      && !isMaximalOrder cusp5F (reduceOrder (round2Step 12 cusp5F).1)) = true := by native_decide

/-- **★★ The FULL iteration reaches `[1, y/x²]` for `y² − x⁵`** (`native_decide`): `integralBasis cusp5F`
iterates Round-2 **twice** (`[1, y] → [1, y/x] → [1, y/x²]`) to the maximal order, returning the generator
`[0, 1/x²] = y/x²` and the first vector `1`. The multi-step iteration computes the integral basis of the
worse cusp, which a single Round-2 step cannot. Checked by `cisZeroG` of the generator minus `y/x²`. -/
theorem cusp5_integralBasis_eq :
    (cisZeroG (csubG cusp5IBGen [CField.zero, qxOfFrac [1] [0, 0, 1] (by decide)])
      && cisZeroG (csubG ((integralBasis cusp5F).getD 0 []) [CField.one])) = true := by native_decide

/-- **★★ The worse-cusp integral-basis generator `y/x²` is INTEGRAL: `(y/x²)² = x`, and `[1, y/x²]` is
MAXIMAL** (`native_decide`): `afMul cusp5F (y/x²) (y/x²) = x` in `ℚ(x)[y]/(y² − x⁵)` (`(y/x²)² = y²/x⁴ =
x⁵/x⁴ = x`, a monic integral relation), and `isMaximalOrder` on `integralBasis cusp5F` is `true` (the order's
discriminant `4x⁵/x⁴ = 4x` is squarefree, no bad prime). The two-step iteration reaches the genuine maximal
order. -/
theorem cusp5_integralBasis_integral_maximal :
    (cisZeroG (csubG (afMul cusp5F cusp5IBGen cusp5IBGen) [qxOfNum [0, 1]])
      && isMaximalOrder cusp5F (integralBasis cusp5F)) = true := by native_decide

/-! ### ★★ A genuinely MULTI-PRIME curve: `y² − x³(x−1)²`, bad at BOTH `x` and `x − 1` (`native_decide`)

The curve `f = y² − x³(x − 1)² = y² − (x⁵ − 2x⁴ + x³)` over `ℚ(x)`: discriminant `−4a₀ = 4x³(x − 1)²`, so
**two** bad primes `p = x` (`x² | 4x³(x−1)²`) and `p = x − 1` (`(x−1)² | 4x³(x−1)²`). The order `[1, y]` is
non-maximal at *both*: near `x = 0`, `y/x` is integral (`(y/x)² = x³(x−1)²/x² = x(x−1)²`); near `x = 1`,
`y/(x − 1)` is integral (`(y/(x−1))² = x³(x−1)²/(x−1)² = x³`). The maximal order is generated by
`y/(x(x − 1))` — integral since `(y/(x(x−1)))² = x³(x−1)²/(x²(x−1)²) = x`. `integralBasis` enlarges at **both**
primes in the pass, reaching `[1, y/(x(x − 1))] = [1, y/(x² − x)]`. -/

/-- The two-bad-prime curve `f = y² − x³(x − 1)² = y² − (x⁵ − 2x⁴ + x³) ∈ ℚ(x)[y]` (`a₀ = −(x⁵ − 2x⁴ + x³)`,
`a₁ = 0`, monic), the `CPolyG (QFunNZG ℚ)` `[−(x⁵−2x⁴+x³), 0, 1]`. Singular at `x = 0` (a cusp-like point) and
`x = 1` (a node-like point); the integral basis is `[1, y/(x(x−1))]`, enlarging at both bad primes `x` and
`x − 1`. -/
def biCuspF : CPolyG (QFunNZG ℚ) :=
  [qxOfNum [0, 0, 0, -1, 2, -1], CField.zero, CField.one]

/-- The computed integral-basis generator `y/(x(x−1)) = y/(x² − x)` = the second basis vector of
`integralBasis biCuspF` (`= [0, 1/(x² − x)]` in the `[1, y]` coords). -/
def biCuspIBGen : CPolyG (QFunNZG ℚ) := (integralBasis biCuspF).getD 1 []

-- Sanity print: the two-bad-prime discriminant numerator (expected `4x³(x−1)² = 4x³−8x⁴+4x⁵ = [0,0,0,4,-8,4]`).
#eval (discNum biCuspF : List ℚ)

-- Sanity print: the bad primes (expected `[x−1, x] = [[-1,1], [0,1]]` in factoring order).
#eval (badPrimes 16 biCuspF).map (fun p => (cmonicG p : List ℚ))

-- Sanity print: the FULL integralBasis (expected `[1, y/(x²−x)]`, i.e. second vector denom `[0,-1,1]`).
#eval (integralBasis biCuspF).map (fun b => b.map (fun z => ((z.1.1 : List ℚ), (z.1.2 : List ℚ))))

/-- **★★ The curve `y² − x³(x−1)²` has TWO bad primes `x` and `x − 1`** (`native_decide`): `badPrimes biCuspF`
(in factoring order) is `[x − 1, x]` — the discriminant `4x³(x − 1)²` flags both `p = x` and `p = x − 1` as
primes where `[1, y]` is non-maximal. The first genuinely multi-prime example (the cusp/node had a single bad
prime `x`). -/
theorem biCusp_badPrimes_eq :
    (badPrimes 16 biCuspF).map cmonicG = [([-1, 1] : CPolyG ℚ), ([0, 1] : CPolyG ℚ)] := by
  native_decide

/-- **★★ The multi-prime integral basis is `[1, y/(x(x−1))]`, integral (`(y/(x(x−1)))² = x`) and maximal**
(`native_decide`): `integralBasis biCuspF` enlarges `[1, y]` at **both** bad primes `x` and `x − 1`, returning
the generator `[0, 1/(x² − x)] = y/(x(x − 1))` and the first vector `1`; the generator is integral
(`afMul biCuspF g g = x`, i.e. `(y/(x(x−1)))² = x³(x−1)²/(x²(x−1)²) = x`); and `isMaximalOrder` is `true`. The
single combined denominator `x(x − 1)` carries the enlargement at both primes at once. -/
theorem biCusp_integralBasis_eq :
    (cisZeroG (csubG biCuspIBGen [CField.zero, qxOfFrac [1] [0, -1, 1] (by decide)])
      && cisZeroG (csubG ((integralBasis biCuspF).getD 0 []) [CField.one])
      && cisZeroG (csubG (afMul biCuspF biCuspIBGen biCuspIBGen) [qxOfNum [0, 1]])
      && isMaximalOrder biCuspF (integralBasis biCuspF)) = true := by native_decide

/-! ### The NEXT piece: higher-degree (non-linear) bad primes, and the genus

`integralBasis` now iterates Round-2 to the maximal order for **linear** bad primes `p = x − a` (the residue
field `K[x]/(p) = K`, so the trace-matrix kernel mod `p` is a single root evaluation `qEvalAtRoot`). The two
remaining pieces:

1. **Higher-degree bad primes.** For a bad prime `p` of degree `> 1` (e.g. an irreducible quadratic
   `x² + 1` over `ℚ`), the residue field `K[x]/(p)` is a proper field **extension** of `K`. The mod-`p`
   trace-matrix kernel is then linear algebra **over `K[x]/(p)`** — arithmetic on `CPolyG ℚ` reduced mod `p`
   (a degree-`< deg p` representative ring), not a single evaluation at a root. The construction is otherwise
   identical (`ipOCoords`'s residue-kernel in `O`-coords + `idealizerOCoords`): replace `qEvalAtRoot` /
   `kernelBasisG` over `K` by their `K[x]/(p)`-coefficient analogues (`cmodWf · p` arithmetic in the Gauss
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
compositions over finite-list kernels; `kernelBasisG`/`matInvG`/`hermiteRowReduce` fold over finite
`List.range`s, while exact division and fraction cancellation use the fuel-free `cdivWf`/`qReduceNZG` path).
**The engine now computes the FULL general-curve integral basis** —
iterating the Ford–Zassenhaus Round-2 step to the maximal order: for the cusp `y² − x³` and node
`y² − x²(x+1)` it returns `[1, y/x]` in one step (`cusp_integralBasis_eq`, `node_integralBasis_eq`); for the
**worse cusp** `y² − x⁵` it iterates **twice** to `[1, y/x²]` (`cusp5_integralBasis_eq`,
`cusp5_oneStep_not_maximal` showing one step is insufficient and not maximal); for `y² − x³(x−1)²` it enlarges
at **both** bad primes `x` and `x − 1` to `[1, y/(x(x−1))]` (`biCusp_badPrimes_eq`, `biCusp_integralBasis_eq`)
— each final basis integral (`afMul` of the generator with itself in `K[x]`) and maximal (`isMaximalOrder`).
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
