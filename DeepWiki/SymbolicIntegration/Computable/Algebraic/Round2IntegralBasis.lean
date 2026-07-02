import DeepWiki.SymbolicIntegration.Computable.Algebraic.AlgFunctionField
import DeepWiki.SymbolicIntegration.Computable.Algebraic.RadicalLogArgGeneric

/-! # The Ford–Zassenhaus ROUND-2 step: p-trace-radical + idealizer ENLARGING the order toward the
maximal order (= the integral basis of `K(x, y) = K(x)[y]/(f)`)
(Trager, *Integration of Algebraic Functions*, Ch. 2 §1–2, p. 18–26)

`ComputableAlgFunctionField` built the **inputs** for an arbitrary monic curve `f`: the carrier `α[y]/(f)`
(`afMul`/`afPow`), the trace `Tr : K(x, y) → K(x)` (`trace`), the trace matrix `[Tr(ωᵢ ωⱼ)]`
(`traceMatrix`), and the discriminant `det[Tr(ωᵢωⱼ)] = ± Res(f, f')` (`discriminant`/`discResultant`).
`ComputableHermiteNormalForm` built **Hermite row reduction over `K[x]`** (`hermiteRowReduce`, the
Euclidean-domain triangularizer). This file runs **one Round-2 step**: starting from the equation order
`O = [1, y, …, yⁿ⁻¹]`, it ENLARGES `O` toward the maximal order.

The algorithm (Trager p. 21, improved form), one step:

1. **Bad primes** (`badPrimes`): squarefree-factor `d = discriminant f` over `K[x]` (the engine's generic
   Yun `cSqfreeYunFFG`); the bad primes are the factors `p` with `p² | d` (`O` may be non-maximal only at
   these). For the cusp `y² − x³`, `d = 4x³`, squarefree part `x`, and `x² | 4x³` — so `p = x` is bad.

2. **p-trace-radical** (`pTraceRadical`): `I_p = { z ∈ O : p | Tr(z·ωⱼ) ∀j }` is, over the residue field
   `K[x]/(p)`, the **kernel of the trace matrix `T` reduced mod `p`** (Trager eq. 5). For a **linear**
   prime `p = x − a`, `K[x]/(p) = K`, so `T mod p` = evaluate `T` at `x = a` (`qEvalAtRoot`), and the
   kernel is plain `K`-linear algebra (the field `gaussElimG`/`kernelBasisG`). `I_p`'s `K[x]`-module
   generators are `{p·ωᵢ} ∪ {lifts of the kernel basis}`, Hermite-reduced (`hermiteRowReduce`) to a
   `K[x]`-basis.

3. **Idealizer** (`round2Step`): the enlarged order `Î = (I_p : I_p) = { z ∈ K(x, y) : z·I_p ⊆ I_p }`
   (Trager §2, p. 26). With an `I_p`-basis `[ι₁, …, ιₙ]` (coordinate matrix `B` over `K(x)` in the `[1,y]`
   order basis), the multiplication-by-`ιⱼ` matrices in the `I_p` output basis are `Mⱼ = B⁻¹ · (mult-ιⱼ
   matrix)`; clearing each `Mⱼ` to a common denominator `δ` reduces `z·I_p ⊆ I_p` to the **same**
   `Aū ∈ δ·K[x]ⁿ` Hermite-mod-`δ` solve as the p-trace-radical. The columns of `M̂⁻¹` (first `n` rows of
   the Hermite reduction) are the idealizer basis, expressed in the order basis `[1, y]` — carrying the
   denominators that ENLARGE the order. `Î ⊇ O`; `Î ⊋ O` iff `O` was non-maximal at `p`.

**The headline** (`native_decide`): on the **cusp** `f = y² − x³` (genus 0), `discriminant` is `4x³` so
`p = x` is bad, and `[1, y]` is NON-maximal because `y/x` is integral (`(y/x)² = y²/x² = x³/x² = x`, monic).
`round2Step` ENLARGES `[1, y] → [1, y/x]`: the new basis element `y/x` satisfies `afMul (y/x) (y/x) = x`
(integral), and `[1, y/x]` is the maximal order (a second `round2Step` does not grow it). The engine now
computes (at least one Round-2 step of) the general-curve integral basis.

**Honest scope.** The p-trace-radical (residue-field kernel) and the idealizer with the `y² − x³`
enlargement `[1, y] → [1, y/x]` is the milestone. The full `integralBasis` (iterating `round2Step` to a
fixed point, and the higher-degree / non-linear-prime residue kernels) is documented at the end as the
next piece. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace CPolyG

variable {α : Type*} [CField α]

/-! ### Residue-field reduction at a linear prime `p = x − a` (`qEvalAtRoot`)

For a **linear** bad prime `p = x − a`, the residue field `K[x]/(p)` is `K` itself, and reducing a
`K[x]`-element (or, more generally, a `K(x)`-element with denominator coprime to `p`) modulo `p` is
**evaluation at the root `a`**. `qEvalAtRoot` evaluates a fraction `num/den ∈ QFunNZG ℚ` at `a` by Horner
(`cevalG num a / cevalG den a`). Applied entrywise to the trace matrix it produces the `ℚ`-matrix
`T mod p`, whose kernel is the p-trace-radical (mod `p`). -/

/-- **Evaluate a `ℚ(x)` element at a root `a`** `qEvalAtRoot z a = num(a)/den(a) ∈ ℚ` — Horner-evaluate
the numerator and denominator coefficient lists (`cevalG`) of `z : QFunNZG ℚ` at `a` and divide. For a
linear prime `p = x − a` this is the reduction `z mod p ∈ K[x]/(p) = ℚ` (valid when `den(a) ≠ 0`, i.e. `p`
does not divide the denominator — automatic for trace-matrix entries, which lie in `K[x]`). -/
def qEvalAtRoot (z : QFunNZG ℚ) (a : ℚ) : ℚ :=
  CField.div (cevalG (z.1.1 : CPolyG ℚ) a) (cevalG (z.1.2 : CPolyG ℚ) a)

/-! ### A full kernel BASIS of a `β`-matrix over `[CField β]` (`kernelBasisG`)

`kernelVectorG` (`ComputableRadicalLogArgGeneric`) returns a single kernel vector (the first free column).
The p-trace-radical needs the **whole** kernel: one vector per free column. `kernelBasisG` runs the same
`gaussElimG` once and emits, for **each** free column `fc`, the basis vector with a `1` at `fc`, each pivot
variable set to the negated pivot-row entry at `fc`, other free variables `0` — the standard reduced-
row-echelon nullspace basis. (For a `1`-dimensional kernel this is `[kernelVectorG]`.) -/

/-- **A basis of the kernel of a `β`-matrix over `[CField β]`** `kernelBasisG nCols rows`: one vector per
**free** (non-pivot) column of the `gaussElimG` reduction. For free column `fc`, the vector has `1` at
`fc`, each pivot variable `pc` set to `−(rref pivot row at fc)`, other entries `0` — the reduced-row-
echelon nullspace basis. Generalizes `kernelVectorG` (which returns only the first such vector). Pure
`CField`-arithmetic, fuel-free, `native_decide`-able. -/
def kernelBasisG {β : Type*} [CField β] (nCols : ℕ) (rows : List (List β)) :
    List (List β) :=
  let (rs, pivots) := gaussElimG nCols rows
  let freeCols := (List.range nCols).filter (fun c => ¬ pivots.contains c)
  freeCols.map (fun fc =>
    let base : List β := (List.range nCols).map (fun c =>
      if c = fc then (CField.one : β) else CField.zero)
    (List.range pivots.length).foldl (fun (acc : List β) r =>
      let pc := pivots[r]!
      let v := CField.neg ((rs[r]!).getD fc CField.zero)
      acc.set pc v) base)

end CPolyG

/-! ### Bad primes: squarefree-factor the discriminant, keep the factors with `p² | d` (`badPrimes`)

The discriminant `d = discriminant f ∈ K(x)` is a polynomial in `x` (denominator `1` for a monic `f`); its
numerator is a `CPolyG ℚ = ℚ[x]`. Yun-factoring it (`cSqfreeYunFFG` over `α = ℚ`) gives the squarefree
factors `[p₁, p₂, …]` of multiplicity `1, 2, …`. The **bad primes** are those with `p² | d`, i.e. the
factors of multiplicity `≥ 2` (`cSqfreeYunFFG`'s entries from index `1` on) together with any multiplicity-
`1` factor that nonetheless squares-divides `d` — equivalently, every distinct prime `p` with `p² | d`. We
test `p² | d` directly (`cmodWf d (p²) = 0`) on the distinct squarefree factors. -/

open CPolyG

/-- **The numerator of the discriminant as a `ℚ[x]` polynomial** `discNum f = (discriminant f).1.1`
(the numerator coefficient list of the `QFunNZG ℚ` discriminant; the denominator is `1` for a monic `f`).
The polynomial in `x` whose squarefree part bounds the bad primes. -/
def discNum (f : CPolyG (QFunNZG ℚ)) : CPolyG ℚ := (discriminant f).1.1

/-- **The bad primes of `f`** `badPrimes fuel f`: the distinct monic irreducible-or-squarefree factors `p`
of the discriminant numerator (`cSqfreeYunFFG` Yun factorization over `ℚ[x]`) that satisfy `p² | d`
(tested by `cisZeroG (cmodWf d (p·p))`). Over `ℚ[x]` these are the primes where the equation order
`O = K[x][y]/(f)` may be non-maximal — the primes Round-2 enlarges the order at. (For the cusp `y² − x³`,
`d = 4x³`, Yun gives `[…, …, x]` with `x` at multiplicity `3`, and `x² | 4x³`, so `badPrimes = [x]`.) -/
def badPrimes (fuel : ℕ) (f : CPolyG (QFunNZG ℚ)) : List (CPolyG ℚ) :=
  let d := discNum f
  let sqf := cSqfreeYunFFG fuel d
  -- distinct nonconstant squarefree factors, each made monic
  let distinct := (sqf.map cmonicG).filter (fun p => 0 < cdegG p)
  distinct.filter (fun p => cisZeroG (cmodWf d (cmulG p p)))

/-! ### The cusp `f = y² − x³` over `ℚ(x)` (the headline curve, genus 0)

`α = QFunNZG ℚ ≅ ℚ(x)`, `n = 2`, `f(y) = y² − x³` (`a₁ = 0`, `a₀ = −x³`, monic), basis `[1, y]`;
`y² ≡ x³ (mod f)`. The discriminant is `a₁² − 4a₀ = 4x³`, so `p = x` is the (only) bad prime
(`x² | 4x³`). The order `[1, y]` is NON-maximal: `y/x` is integral (`(y/x)² = x`). -/

/-- The cusp curve `f = y² − x³ ∈ ℚ(x)[y]` (`a₀ = −x³`, `a₁ = 0`, monic), the `CPolyG (QFunNZG ℚ)`
`[−x³, 0, 1]`. Genus 0; the equation order `[1, y]` is non-maximal at `x` because `y/x` is integral. -/
def cuspF : CPolyG (QFunNZG ℚ) :=
  [qxOfNum [0, 0, 0, -1], CField.zero, CField.one]

/-- The generator `y` of `ℚ(x)[y]/(y² − x³)` (`afBasisElem 1 = [0, 1]`). -/
def cuspY : CPolyG (QFunNZG ℚ) := afBasisElem 1

-- Sanity print: the cusp discriminant numerator (expected `4x³ = [0,0,0,4]`).
#eval (discNum cuspF : List ℚ)

-- Sanity print: the bad primes of the cusp (expected `[x] = [[0,1]]`).
#eval (badPrimes 12 cuspF).map (fun p => (p : List ℚ))

/-- **★ The bad prime of the cusp is `x`** (`native_decide`): `badPrimes cuspF = [x]` (the single monic
factor `x = [0, 1]` with `x² | 4x³`). The discriminant `4x³` flags exactly `p = x` as the prime where the
equation order `[1, y]` may be non-maximal. -/
theorem cusp_badPrimes_eq :
    (badPrimes 12 cuspF).map cmonicG = [([0, 1] : CPolyG ℚ)] := by native_decide

/-! ### The p-trace-radical `I_p` at a linear prime (`pTraceRadical`)

For a **linear** bad prime `p = x − a`, the p-trace-radical `I_p = { z ∈ O : p | Tr(z·ωⱼ) ∀j }` is, over
the residue field `K[x]/(p) = K`, the kernel of `T = traceMatrix f` reduced mod `p` = evaluated at `a`
(Trager eq. 5; the `K` linear-algebra case). The order `O` is given by a `K[x]`-basis `[ω₀, …, ωₙ₋₁]`
(coordinate matrix `B` of order-basis elements in the *power* basis `[1, y, …]`, entries `∈ K[x]`); at the
start `B = Iₙ` (the order IS the power basis). `pTraceRadical` returns a `K[x]`-basis of `I_p` as a
`PolyMatrix ℚ` (rows = basis vectors, columns = power-basis coordinates), Hermite-reduced. -/

namespace CPolyG

/-- **The power-basis coordinate row of an order element** `afCoordRow n z = [num(c₀), …, num(c_{n−1})]`:
the first `n` coefficients of `z : CPolyG (QFunNZG ℚ)` (an element of `α[y]/(f)`) read as `ℚ[x]`
numerators (`CPolyG ℚ`). When `z ∈ O` with the order basis `[1, y, …]`, these are the integral `K[x]`
coordinates of `z`. -/
def afCoordRow (n : ℕ) (z : CPolyG (QFunNZG ℚ)) : List (CPolyG ℚ) :=
  (List.range n).map (fun i => ((z.getD i CField.zero : QFunNZG ℚ).1.1 : CPolyG ℚ))

/-- **The trace matrix reduced at a linear prime root `a`** `traceMatrixAtRoot f a`: the `n×n` `ℚ`-matrix
`(traceMatrix f (powerBasis f))` with every `ℚ(x)` entry evaluated at `x = a` (`qEvalAtRoot`), i.e. the
trace matrix `T mod (x − a)` over the residue field `ℚ`. Its kernel (over `ℚ`) is the p-trace-radical mod
`p`. -/
def traceMatrixAtRoot (f : CPolyG (QFunNZG ℚ)) (a : ℚ) : List (List ℚ) :=
  (traceMatrix f (powerBasis f)).map (fun row => row.map (fun e => qEvalAtRoot e a))

/-- **The p-trace-radical `I_p` at a linear prime `p = x − a`** `pTraceRadical fuel f p a`: a `K[x]`-basis
of `I_p = { z ∈ O : p | Tr(z·ωⱼ) ∀j }`, as a `PolyMatrix ℚ` (rows = basis vectors in the power-basis
`[1, y, …]` coordinates, entries `∈ ℚ[x]`). Construction (Trager eq. 5, linear-prime case): the kernel of
`traceMatrixAtRoot f a` over `ℚ` (`kernelBasisG`) gives the residue-class generators; each kernel vector
`(c₀, …, c_{n−1}) ∈ ℚⁿ` lifts to the order element `Σ cᵢ ωᵢ` (a constant `ℚ[x]` coordinate row). Together
with `p·ωᵢ` (the `p`-scaled power-basis rows, `p = [−a, 1]`), these generate `I_p ⊇ p·O`; `hermiteRowReduce`
triangularizes the stacked generators to a `K[x]`-basis (the nonzero rows). The kernel lift carries the
denominators-to-be: it is the part of `I_p` strictly larger than `p·O`. -/
def pTraceRadical (f : CPolyG (QFunNZG ℚ)) (p : CPolyG ℚ) (a : ℚ) : PolyMatrix ℚ :=
  let n := cdegG f
  let kers : List (List ℚ) := kernelBasisG n (traceMatrixAtRoot f a)
  -- lift each kernel vector to a constant `ℚ[x]` coordinate row (the residue generators)
  let kerRows : PolyMatrix ℚ := kers.map (fun v => (List.range n).map (fun i => [v.getD i 0]))
  -- the `p·ωᵢ` rows: `p` in column `i`, zero elsewhere
  let pRows : PolyMatrix ℚ := (List.range n).map (fun i =>
    (List.range n).map (fun j => if i = j then p else ([] : CPolyG ℚ)))
  let gens : PolyMatrix ℚ := kerRows ++ pRows
  let reduced := hermiteRowReduce gens
  reduced.filter (fun row => !row.all cisZeroG)

end CPolyG

/-! ### ★ The cusp p-trace-radical `I_x = ⟨x, y⟩` (`native_decide`)

For `f = y² − x³`, `p = x` (`a = 0`): the trace matrix is `[[2, 0], [0, 2x³]]`, which at `x = 0` is
`[[2, 0], [0, 0]]`; its kernel over `ℚ` is `{(0, 1)}` — the element `y`. So `I_x` is generated by `y`
together with `x·1, x·y`, and Hermite-reduces to the `K[x]`-basis `[x, y]` (coordinate rows
`[x, 0]` and `[0, 1]`). `I_x = ⟨x, y⟩` strictly contains `x·O = ⟨x, xy⟩` — the `y` generator is what
makes the idealizer enlarge the order. -/

open CPolyG

-- Sanity print: the cusp trace matrix evaluated at `x = 0` (expected `[[2,0],[0,0]]`).
#eval traceMatrixAtRoot cuspF 0

-- Sanity print: the kernel basis of the reduced trace matrix (expected `[(0,1)]` = the element `y`).
#eval kernelBasisG (cdegG cuspF) (traceMatrixAtRoot cuspF 0)

-- Sanity print: the `K[x]`-basis of `I_x` (rows of power-basis coords; expected `[x,0]` and `[0,1]`).
#eval (pTraceRadical cuspF [0, 1] 0).map (fun row => row.map (fun q => cnormG q))

/-- **★ The cusp trace matrix mod `x` is `[[2, 0], [0, 0]]`** (`native_decide`): evaluating
`traceMatrix (y² − x³) = [[2, 0], [0, 2x³]]` at `x = 0` gives `[[2, 0], [0, 0]]` — a rank-`1` `ℚ`-matrix
whose kernel `{(0, 1)}` is the residue class of the p-trace-radical generator `y`. -/
theorem cusp_traceMatrixAtRoot_eq :
    traceMatrixAtRoot cuspF 0 = [[2, 0], [0, 0]] := by native_decide

/-- **★ The cusp p-trace-radical kernel is `(0, 1) = y`** (`native_decide`): the kernel basis of the
reduced trace matrix mod `x` is the single vector `(0, 1)` — the order element `0·1 + 1·y = y`. So `y`
(beyond `x·O`) lies in `I_x`; this is the extra generator that the idealizer uses to produce `y/x`. -/
theorem cusp_pTraceRadical_kernel_eq :
    kernelBasisG (cdegG cuspF) (traceMatrixAtRoot cuspF 0) = [[0, 1]] := by native_decide

/-- **★ The cusp p-trace-radical has `K[x]`-basis `[x, y]`** (`native_decide`): `pTraceRadical (y² − x³) x`
Hermite-reduces the generators `{y, x·1, x·y}` to the two nonzero coordinate rows `[x, 0]` (= `x·1`) and
`[0, 1]` (= `y`) — i.e. `I_x = ⟨x, y⟩_{K[x]}`, strictly larger than `x·O = ⟨x·1, x·y⟩`. THE P-TRACE-RADICAL
COMPUTES (via the residue-field kernel + Hermite reduction over `K[x]`). -/
theorem cusp_pTraceRadical_basis :
    (pTraceRadical cuspF [0, 1] 0).map (fun row => row.map cmonicG) =
      [[[0, 1], []], [[], [1]]] := by native_decide

/-! ### The idealizer `Î = (I_p : I_p)` — one Round-2 enlargement (`round2Step`)

The enlarged order is the idealizer `Î = (I_p : I_p) = { z ∈ K(x, y) : z·I_p ⊆ I_p }` (Trager §2, p. 26).
Writing `z` in the order basis `[1, y, …]` with coordinate vector `ū ∈ K(x)ⁿ`, and the `I_p`-basis as the
columns of the `K(x)`-matrix `B` (`B[r][k]` = the `r`-th power-basis coordinate of `ιₖ`), the condition
`z·ιⱼ ∈ I_p` is `Mⱼ·ū ∈ K[x]ⁿ` where `Mⱼ = B⁻¹·(multMatrix f ιⱼ)` (multiply-by-`ιⱼ` in the power basis,
re-expressed in the `I_p` output basis). Stacking the `Mⱼ` gives `M` (`n²×n` over `K(x)`); clearing to a
common denominator `δ ∈ K[x]` turns `M·ū ∈ K[x]^{n²}` into the Trager §1.1 solve `N·ū ≡ 0 (mod δ)` with
`N = δ·M ∈ K[x]`. Adjoining `δ·Iₙ` (so that `ū ∈ K[x]ⁿ` too) and Hermite-reducing over `K[x]`
(`hermiteRowReduce`), the first `n` rows form `M̂`; the **columns of `M̂⁻¹`** are the idealizer basis, in
the order basis `[1, y]` — carrying the denominators that ENLARGE the order. -/

namespace CPolyG

/-! #### Field matrix algebra over `K(x) = QFunNZG ℚ` (inverse, product) -/

/-- **Matrix product over a `[CField β]`** `matMulG A Bm`: the `(i, j)` entry is `Σₖ A[i][k]·Bm[k][j]`
(`p×q` times `q×r`). Used to form `Mⱼ = B⁻¹·(multMatrix f ιⱼ)` over `K(x)`. -/
def matMulG {β : Type*} [CField β] (A Bm : List (List β)) : List (List β) :=
  let r := (Bm.headD []).length
  A.map (fun rowA =>
    (List.range r).map (fun j =>
      ((List.range rowA.length).foldl (fun acc k =>
        CField.add acc (CField.mul (rowA.getD k CField.zero) ((Bm.getD k []).getD j CField.zero)))
        CField.zero)))

/-- **Inverse of a square `n×n` matrix over a `[CField β]`** `matInvG n M = some M⁻¹` (or `none` if
singular): Gauss–Jordan on the augmented `[M | Iₙ]` (the same elimination as `gaussElimG`, scaling each
pivot row to a leading `1` and clearing the column above and below), reading the right half. Pure
`CField`-arithmetic, fuel-free. Used to invert the `I_p`-basis matrix `B` and the reduced `M̂`. -/
def matInvG {β : Type*} [CField β] (n : ℕ) (M : List (List β)) : Option (List (List β)) :=
  -- augment each row with the identity
  let aug : List (List β) := (List.range n).map (fun i =>
    (M.getD i []) ++ (List.range n).map (fun j => if i = j then (CField.one : β) else CField.zero))
  -- Gauss–Jordan over the 2n columns, pivoting on columns 0 … n−1
  let step : Option (List (List β)) → ℕ → Option (List (List β)) :=
    fun st col =>
      match st with
      | none => none
      | some rs =>
        match (List.range n).find?
            (fun i => i ≥ col && (!CField.isZero ((rs.getD i []).getD col CField.zero))) with
        | none => none
        | some i =>
          let rowCol := rs.getD col []
          let rowI := rs.getD i []
          let rs := (rs.set col rowI).set i rowCol
          let pivRow := rs.getD col []
          let lead := pivRow.getD col CField.zero
          let pivRow := pivRow.map (fun a => CField.div a lead)
          let rs := rs.set col pivRow
          let rs := (List.range n).foldl (fun acc rr =>
            if rr = col then acc
            else
              let row := acc.getD rr []
              let factor := row.getD col CField.zero
              if CField.isZero factor then acc
              else
                let newRow := (List.range (2 * n)).map (fun c =>
                  CField.sub (row.getD c CField.zero) (CField.mul factor (pivRow.getD c CField.zero)))
                acc.set rr newRow) rs
          some rs
  match (List.range n).foldl step (some aug) with
  | none => none
  | some rs => some (rs.map (fun row => (List.range n).map (fun j => row.getD (n + j) CField.zero)))

/-! #### `K(x) ↔ K[x]` denominator clearing and lifts -/

/-- **Lift a `K[x]` coordinate row to a `K(x, y)` element** `rowToAf row = Σᵢ qxOfNum(rowᵢ)·yⁱ`: the
`CPolyG (QFunNZG ℚ)` whose `i`-th coefficient is the `ℚ(x)` value of the `i`-th `ℚ[x]` coordinate. Turns an
`I_p`-basis row (power-basis coordinates over `K[x]`) into the order element it represents (so `afMul` can
multiply by it). -/
def rowToAf (row : List (CPolyG ℚ)) : CPolyG (QFunNZG ℚ) := row.map qxOfNum

/-- **The `I_p`-basis matrix `B` over `K(x)`** `ipBasisMatrix n ipRows`: the `n×n` `QFunNZG ℚ`-matrix whose
column `k` is the `k`-th `I_p`-basis row (power-basis coordinates), i.e. `B[r][k] = qxOfNum (ipRows[k][r])`.
(The `I_p` rows are *row* vectors of coordinates; `B` puts them in *columns*, the change-of-basis from the
`I_p` basis to the power basis.) -/
def ipBasisMatrix (n : ℕ) (ipRows : PolyMatrix ℚ) : List (List (QFunNZG ℚ)) :=
  (List.range n).map (fun r =>
    (List.range n).map (fun k => qxOfNum ((ipRows.getD k []).getD r [])))

/-- **The common denominator of a `K(x)`-matrix** `commonDenom M = ∏ (distinct entry denominators)`
(`CPolyG ℚ`): the product over all entries of their normalized denominator numerators (`z.1.2`), used to
clear `M` to `K[x]`. A coarse common multiple (product, not lcm) — sufficient, since the Hermite-mod-`δ`
solve is invariant under enlarging `δ` to a multiple. -/
def commonDenom (M : List (List (QFunNZG ℚ))) : CPolyG ℚ :=
  M.foldl (fun acc row =>
    row.foldl (fun a z =>
      let den := cnormG (z.1.2 : CPolyG ℚ)
      if cisZeroG den || cisZeroG (csubG den [CField.one]) then a else cmulG a den)
      acc) [CField.one]

/-- **Clear a `K(x)`-row to a `K[x]`-row at denominator `δ`** `clearRow δ row = [num(δ·zᵢ)]`: multiply each
`ℚ(x)` entry by `δ` and take the numerator (`CPolyG ℚ`). When `δ` is a common denominator of `row`, every
`δ·zᵢ ∈ K[x]`, so the result is the integral row `δ·row` over `K[x]`. -/
def clearRow (δ : CPolyG ℚ) (row : List (QFunNZG ℚ)) : List (CPolyG ℚ) :=
  row.map (fun z => (CField.mul (qxOfNum δ) z).1.1)

/-! #### The idealizer of `I_p`, given an order basis (`idealizerBasis`) -/

/-- **The idealizer `Î = (I_p : I_p)`, as a new `K(x)` order basis** `idealizerBasis f orderBasis ipRows`.
`orderBasis = [ω₀, …, ωₙ₋₁]` is the current order's `K(x, y)` basis (`CPolyG (QFunNZG ℚ)` elements), and
`ipRows` is the `I_p` `K[x]`-basis in power-basis coordinates (`pTraceRadical` output). Returns the
idealizer's basis as `n` `K(x, y)` elements (each a coordinate vector in `[1, y, …]`), per Trager §2 p. 26:

* `B` = the `I_p`-basis matrix over `K(x)` (`ipBasisMatrix`; column `k` = `ιₖ` in power coords);
* for each `ιⱼ = rowToAf (ipRows[j])`, the multiply-by-`ιⱼ` matrix `multMatrix f ιⱼ` over `K(x)`, and
  `Mⱼ = B⁻¹ · multMatrix f ιⱼ` (output re-expressed in the `I_p` basis);
* stack the `Mⱼ` into `M` (`n²×n` over `K(x)`); the idealizer is `{ū : M·ū ∈ K[x]^{n²}}`;
* clear `M` to `N = δ·M` over `K[x]` (`δ = commonDenom M`), Hermite-reduce `N` (`hermiteRowReduce`), take
  the first `n` (pivot) rows `N̂`, invert over `K(x)` (`matInvG`), and scale by `δ`: the **columns of
  `δ·N̂⁻¹`** are the idealizer basis (in the order/power basis), carrying the enlarging denominators.

Returns `orderBasis` unchanged if any inverse is singular (a safe no-op). -/
def idealizerBasis (f : CPolyG (QFunNZG ℚ)) (orderBasis : List (CPolyG (QFunNZG ℚ)))
    (ipRows : PolyMatrix ℚ) : List (CPolyG (QFunNZG ℚ)) :=
  let n := cdegG f
  let B : List (List (QFunNZG ℚ)) := ipBasisMatrix n ipRows
  match matInvG n B with
  | none => orderBasis
  | some Binv =>
    -- stack the `Mⱼ = Binv · multMatrix f ιⱼ` (each `n×n` over K(x))
    let M : List (List (QFunNZG ℚ)) :=
      (List.range n).foldr (fun j acc =>
        let ιj : CPolyG (QFunNZG ℚ) := rowToAf ((ipRows.getD j []))
        let Mj := matMulG Binv (multMatrix f ιj)
        Mj ++ acc) []
    -- clear to K[x] by a common denominator δ
    let δ : CPolyG ℚ := commonDenom M
    let N : PolyMatrix ℚ := M.map (clearRow δ)
    -- Hermite-reduce N over K[x]; the first n rows are the upper-triangular invertible part
    let reduced := hermiteRowReduce N
    let Nhat : List (List (QFunNZG ℚ)) :=
      (List.range n).map (fun i => (List.range n).map (fun j => qxOfNum ((reduced.getD i []).getD j [])))
    match matInvG n Nhat with
    | none => orderBasis
    | some NhatInv =>
      -- columns of δ·N̂⁻¹ are the new basis vectors (in the [1,y,…] order/power basis)
      let δq : QFunNZG ℚ := qxOfNum δ
      (List.range n).map (fun col =>
        (List.range n).map (fun row => CField.mul δq ((NhatInv.getD row []).getD col CField.zero)))

end CPolyG

/-! #### `round2Step`: one enlargement of the equation order at all bad primes -/

namespace CPolyG

/-- **`true` iff a `K(x, y)` order basis equals the power basis `[1, y, …, yⁿ⁻¹]`** `isPowerBasis n basis`:
each `basisᵢ` is `cisZeroG`-equal to `yⁱ` (`afBasisElem i`), entry by entry. Used to test whether
`round2Step` actually grew the order (the new basis differs from `[1, y, …]` iff the order enlarged). -/
def isPowerBasis (n : ℕ) (basis : List (CPolyG (QFunNZG ℚ))) : Bool :=
  (List.range n).all (fun i =>
    cisZeroG (csubG (basis.getD i []) (afBasisElem i)))

/-- **One Ford–Zassenhaus Round-2 enlargement** `round2Step fuel f = (newBasis, grew)`. Starting from the
equation order `O = [1, y, …, yⁿ⁻¹]` (`powerBasis f`), for the **first** bad prime `p = x − a` of `f`
(`badPrimes`; here read off as `a = −p₀` for a monic linear `p = [−a, 1]`), compute the p-trace-radical
`I_p` (`pTraceRadical`) and the idealizer `Î = (I_p : I_p)` (`idealizerBasis`), returning `Î`'s `K(x, y)`
basis and whether it strictly enlarged `O` (`grew = ¬ isPowerBasis`). When there is no bad prime, the order
is already maximal at every linear prime and the power basis is returned with `grew = false`. (The headline
linear-prime case; multiple bad primes / higher-degree residue fields iterate this, documented at the end.) -/
def round2Step (fuel : ℕ) (f : CPolyG (QFunNZG ℚ)) :
    List (CPolyG (QFunNZG ℚ)) × Bool :=
  let n := cdegG f
  let O := powerBasis f
  match (badPrimes fuel f) with
  | [] => (O, false)
  | p :: _ =>
    let pm := cmonicG p
    -- root of a monic linear prime `p = [−a, 1]` is `a = −p₀`
    let a : ℚ := CField.neg (pm.getD 0 CField.zero)
    let ip := pTraceRadical f pm a
    let newBasis := idealizerBasis f O ip
    (newBasis, !isPowerBasis n newBasis)

end CPolyG

/-! ### ★★ THE HEADLINE: `round2Step` ENLARGES `[1, y] → [1, y/x]` for `y² = x³` (`native_decide`)

For the cusp `f = y² − x³`, the single bad prime is `p = x` (root `a = 0`). The p-trace-radical is
`I_x = ⟨x, y⟩`; its idealizer is `(I_x : I_x) = K[x]·1 + K[x]·(y/x)`. `round2Step` computes the new basis
`[1, y/x]` (coordinate vectors `[1, 0]` and `[0, 1/x]` over `K(x)`), strictly enlarging `[1, y]`. The new
generator `y/x` is integral: `(y/x)² = y²/x² = x³/x² = x`. A second `round2Step` does not grow it — `[1, y/x]`
is the maximal order (the integral basis of the cusp). -/

open CPolyG

-- Sanity print: the inverse of the cusp `I_x`-basis matrix `B = [[x,0],[0,1]]` (expected `[[1/x,0],[0,1]]`).
#eval (matInvG 2 (ipBasisMatrix 2 (pTraceRadical cuspF [0, 1] 0))).map
  (fun M => M.map (fun row => row.map (fun z => ((z.1.1 : List ℚ), (z.1.2 : List ℚ)))))

-- Sanity print: the new basis from round2Step (coordinate vectors over ℚ(x); expected `[1,0]`, `[0,1/x]`).
#eval (round2Step 12 cuspF).1.map (fun b => b.map (fun z => ((z.1.1 : List ℚ), (z.1.2 : List ℚ))))

-- Sanity print: did the order grow? (expected `true`).
#eval (round2Step 12 cuspF).2

/-- The computed enlarged generator `y/x ∈ ℚ(x)[y]/(y² − x³)` = the second basis vector of `round2Step`
(`= [0, 1/x]` in the `[1, y]` order basis). The element the engine produces as the Round-2 enlargement. -/
def cuspNewGen : CPolyG (QFunNZG ℚ) := (round2Step 12 cuspF).1.getD 1 []

/-- **★★ `round2Step` ENLARGES the cusp order** (`native_decide`): `(round2Step (y² − x³)).2 = true` — the
idealizer `(I_x : I_x)` strictly contains the equation order `[1, y]`. The Ford–Zassenhaus Round-2 step
detects and performs the enlargement. THE ENGINE COMPUTES A ROUND-2 STEP OF THE GENERAL-CURVE INTEGRAL
BASIS. -/
theorem cusp_round2_grew :
    (round2Step 12 cuspF).2 = true := by native_decide

/-- **★★ The enlarged generator is `y/x`** (`native_decide`): the second basis vector computed by
`round2Step` for the cusp is `[0, 1/x]` in the `[1, y]` order basis — i.e. the element `y/x`. The first
basis vector stays `1` (`[1]`). So `round2Step` produces exactly `[1, y/x]`, the enlargement predicted by
the integrality of `y/x`. Checked by `cisZeroG (cuspNewGen − [0, 1/x])` and the first vector being `1`. -/
theorem cusp_round2_newGen_eq :
    (cisZeroG (csubG cuspNewGen [CField.zero, qxOfFrac [1] [0, 1] (by decide)])
      && cisZeroG (csubG ((round2Step 12 cuspF).1.getD 0 []) [CField.one])) = true := by native_decide

/-- **★★ The enlarged generator `y/x` is INTEGRAL: `(y/x)² = x`** (`native_decide`): `afMul f (y/x) (y/x) =
x` in `ℚ(x)[y]/(y² − x³)`, i.e. `(y/x)² = y²/x² = x³/x² = x` — a monic integral relation. This is the
algebraic proof that `y/x` belongs in the maximal order (and that `[1, y]` was non-maximal): the engine's
computed enlargement is genuinely integral. Checked by `cisZeroG (afMul f (y/x) (y/x) − x)`. -/
theorem cusp_newGen_integral :
    cisZeroG (csubG (afMul cuspF cuspNewGen cuspNewGen) [qxOfNum [0, 1]]) = true := by native_decide

/-- **★★ `[1, y/x]` is the MAXIMAL order — a second `round2Step` does not grow it** (`native_decide`): the
idealizer of the p-trace-radical computed against the **already-enlarged** basis `[1, y/x]` is `[1, y/x]`
again (`grew = false`). So the Round-2 iteration has reached a fixed point: `[1, y/x]` is the integral basis
of the cusp `y² − x³` (genus 0, the well-known result). Verified by running `idealizerBasis` /
`pTraceRadical` against `[1, y/x]` and checking the order does not enlarge. -/
theorem cusp_secondStep_stable :
    let O2 := (round2Step 12 cuspF).1
    let ip2 := pTraceRadical cuspF [0, 1] 0
    let O3 := idealizerBasis cuspF O2 ip2
    (List.range 2).all (fun i =>
      cisZeroG (csubG (O3.getD i []) (O2.getD i []))) = true := by native_decide

/-! ### ★ A second curve: the NODE `f = y² − x²(x + 1)` enlarges `[1, y] → [1, y/x]` (`native_decide`)

The node (an ordinary double point at the origin) `f(y) = y² − x²(x + 1) = y² − x³ − x²` over `ℚ(x)`:
`a₀ = −(x³ + x²)`, discriminant `−4a₀ = 4x²(x + 1)`, so `p = x` is the (only) bad prime (`x² | 4x²(x+1)`,
but `(x+1)² ∤`). The trace matrix is `[[2, 0], [0, 2(x³ + x²)]]`, which at `x = 0` is `[[2, 0], [0, 0]]`;
the kernel is `(0, 1) = y`, so `I_x = ⟨x, y⟩` and `round2Step` enlarges `[1, y] → [1, y/x]`, exactly as for
the cusp. Here the new generator is integral with a **different** minimal relation: `(y/x)² = y²/x² =
(x³ + x²)/x² = x + 1`. So `[1, y/x]` is the maximal order (normalization) of the node too — confirming the
Round-2 step is curve-generic, not special to `y² − x³`. -/

/-- The node curve `f = y² − x²(x + 1) = y² − x³ − x² ∈ ℚ(x)[y]` (`a₀ = −(x³ + x²)`, `a₁ = 0`, monic), the
`CPolyG (QFunNZG ℚ)` `[−(x³ + x²), 0, 1]`. An ordinary double point at the origin; `[1, y]` is non-maximal
at `x` because `y/x` is integral (`(y/x)² = x + 1`). -/
def nodeF : CPolyG (QFunNZG ℚ) :=
  [qxOfNum [0, 0, -1, -1], CField.zero, CField.one]

/-- The computed enlarged generator `y/x ∈ ℚ(x)[y]/(y² − x²(x+1))` = the second basis vector of
`round2Step nodeF` (`= [0, 1/x]` in the `[1, y]` order basis). -/
def nodeNewGen : CPolyG (QFunNZG ℚ) := (round2Step 12 nodeF).1.getD 1 []

-- Sanity print: the node discriminant numerator (expected `4x²(x+1) = 4x² + 4x³ = [0,0,4,4]`).
#eval (discNum nodeF : List ℚ)

-- Sanity print: the node bad primes (expected `[x] = [[0,1]]`).
#eval (badPrimes 12 nodeF).map (fun p => (cmonicG p : List ℚ))

/-- **★ The node bad prime is `x`, and `round2Step` enlarges to `[1, y/x]`** (`native_decide`):
`badPrimes nodeF = [x]`, the order grows (`.2 = true`), and the new generator is `[0, 1/x] = y/x` while the
first basis vector stays `1`. Same enlargement as the cusp, on a different curve. -/
theorem node_round2_newGen_eq :
    ((badPrimes 12 nodeF).map cmonicG = [([0, 1] : CPolyG ℚ)]
      && (round2Step 12 nodeF).2
      && cisZeroG (csubG nodeNewGen [CField.zero, qxOfFrac [1] [0, 1] (by decide)])
      && cisZeroG (csubG ((round2Step 12 nodeF).1.getD 0 []) [CField.one])) = true := by
  native_decide

/-- **★ The node's enlarged generator is INTEGRAL with relation `(y/x)² = x + 1`** (`native_decide`):
`afMul f (y/x) (y/x) = x + 1` in `ℚ(x)[y]/(y² − x²(x+1))` — i.e. `(y/x)² = (x³ + x²)/x² = x + 1`, a monic
integral relation (distinct from the cusp's `(y/x)² = x`). The Round-2 enlargement is genuinely integral on
this curve too. Checked by `cisZeroG (afMul f (y/x) (y/x) − (x + 1))`. -/
theorem node_newGen_integral :
    cisZeroG (csubG (afMul nodeF nodeNewGen nodeNewGen) [qxOfNum [1, 1]]) = true := by native_decide

/-- **★ `[1, y/x]` is the maximal order of the node — a second `round2Step` does not grow it**
(`native_decide`): the idealizer of the p-trace-radical against the enlarged basis `[1, y/x]` is `[1, y/x]`
again. The Round-2 iteration reaches its fixed point in one step for the node, as for the cusp. -/
theorem node_secondStep_stable :
    let O2 := (round2Step 12 nodeF).1
    let ip2 := pTraceRadical nodeF [0, 1] 0
    let O3 := idealizerBasis nodeF O2 ip2
    (List.range 2).all (fun i =>
      cisZeroG (csubG (O3.getD i []) (O2.getD i []))) = true := by native_decide

/-! ### The NEXT pieces: the full `integralBasis` iteration (Trager Ch. 2, p. 21, steps 1–5)

`round2Step` is **one** Ford–Zassenhaus enlargement at the first linear bad prime. The full integral-basis
algorithm (Trager p. 21) iterates it to a fixed point:

1. **Iterate `round2Step` over all bad primes** (`q = ∏ pᵢ` with `pᵢ² | d`), not just the first. The
   p-trace-radical at a product `q` is `J_q = ⋂ J_{pᵢ}` (Trager eq. on p. 24), computed by the same kernel
   solve with the `q·Iₙ` augmentation; the idealizer of `J_q` enlarges at all bad primes simultaneously.

2. **Re-base and repeat.** After one enlargement `O → Î` (change-of-basis matrix `M`, `det M`), set
   `d ← d / (det M)²` and recompute the trace matrix / bad primes **in the new basis** `Î` (the order is no
   longer the power basis, so `traceMatrix` must take the `Î` basis elements, and the `K[x]`-coordinate
   bookkeeping carries the denominators). Repeat until `Î = O` (`grew = false`) — the fixed point is the
   **maximal order**, whose `K[x]`-basis is the integral basis. The cusp reaches it in one step
   (`cusp_secondStep_stable`); higher-genus curves take several.

3. **Higher-degree / non-linear bad primes.** For a bad prime `p` of degree `> 1`, the residue field
   `K[x]/(p)` is a proper extension of `K`, so the trace-matrix kernel is computed over `K[x]/(p)` (modular
   linear algebra over `CPolyG ℚ`-mod-`p`), not by a single evaluation `qEvalAtRoot`. The construction is
   otherwise identical (`pTraceRadical`'s residue-kernel + lift + Hermite). `traceMatrixAtRoot`/`qEvalAtRoot`
   handle the linear case (`p = x − a`), which already covers the cusp headline.

The Round-2 **primitives are all in place** — `badPrimes` (squarefree discriminant), `pTraceRadical`
(residue kernel + `hermiteRowReduce`), `idealizerBasis` (`B⁻¹`, common-denominator clear, Hermite, `M̂⁻¹`),
and `round2Step` (one enlargement, growth detection). What remains is the orchestration loop (re-basing the
trace matrix after each enlargement, iterating over all bad primes to a fixed point) and the modular kernel
for higher-degree residues — and the abstract correctness of the whole pipeline (here `native_decide`-
validated on the cusp). The integral basis is the denominator data the genus-`g` algebraic Hermite
reduction and the divisor/logarithmic-part machinery consume. -/

/-! ### `#print axioms` — does the engine compute a Round-2 step of the general-curve integral basis?

Each validation carries the standard `[propext, Classical.choice, Quot.sound]` plus the `native_decide`
compiler axiom — **no `sorry`, no `sorryAx`, no extra axiom** (every recursion is `ℕ`-fuel-bounded or
structural: `cevalG`/`gaussElimG`/`matInvG` fold over finite `List.range`s, `hermiteRowReduce` is fuel-
bounded, `pTraceRadical`/`idealizerBasis`/`round2Step` are non-recursive compositions). **The engine now
computes one Ford–Zassenhaus Round-2 step of the general-curve integral basis**, ENLARGING the equation
order `[1, y]` toward the maximal order: for the cusp `y² − x³` it produces `[1, y/x]` — bad prime `x`
(`cusp_badPrimes_eq`), p-trace-radical `I_x = ⟨x, y⟩` (`cusp_pTraceRadical_basis`), idealizer enlargement
`[1, y] → [1, y/x]` (`cusp_round2_grew`, `cusp_round2_newGen_eq`) with the new generator integral `(y/x)² =
x` (`cusp_newGen_integral`) and maximal (`cusp_secondStep_stable`). -/

-- The bad prime + p-trace-radical of the cusp:
#print axioms cusp_badPrimes_eq
#print axioms cusp_pTraceRadical_basis

-- ★★ The headline: the idealizer ENLARGES `[1, y] → [1, y/x]`, integral and maximal:
#print axioms cusp_round2_grew
#print axioms cusp_round2_newGen_eq
#print axioms cusp_newGen_integral
#print axioms cusp_secondStep_stable

-- ★ The node `y² − x²(x+1)`: the same enlargement `[1, y] → [1, y/x]`, integral relation `(y/x)² = x+1`:
#print axioms node_round2_newGen_eq
#print axioms node_newGen_integral
#print axioms node_secondStep_stable

end DeepWiki.SymbolicIntegration
