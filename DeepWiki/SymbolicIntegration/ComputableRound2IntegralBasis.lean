import DeepWiki.SymbolicIntegration.ComputableAlgFunctionField
import DeepWiki.SymbolicIntegration.ComputableRadicalLogArgGeneric

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
test `p² | d` directly (`cmodG d (p²) = 0`) on the distinct squarefree factors. -/

open CPolyG

/-- **The numerator of the discriminant as a `ℚ[x]` polynomial** `discNum f = (discriminant f).1.1`
(the numerator coefficient list of the `QFunNZG ℚ` discriminant; the denominator is `1` for a monic `f`).
The polynomial in `x` whose squarefree part bounds the bad primes. -/
def discNum (f : CPolyG (QFunNZG ℚ)) : CPolyG ℚ := (discriminant f).1.1

/-- **The bad primes of `f`** `badPrimes fuel f`: the distinct monic irreducible-or-squarefree factors `p`
of the discriminant numerator (`cSqfreeYunFFG` Yun factorization over `ℚ[x]`) that satisfy `p² | d`
(tested by `cisZeroG (cmodG d (p·p))`). Over `ℚ[x]` these are the primes where the equation order
`O = K[x][y]/(f)` may be non-maximal — the primes Round-2 enlarges the order at. (For the cusp `y² − x³`,
`d = 4x³`, Yun gives `[…, …, x]` with `x` at multiplicity `3`, and `x² | 4x³`, so `badPrimes = [x]`.) -/
def badPrimes (fuel : ℕ) (f : CPolyG (QFunNZG ℚ)) : List (CPolyG ℚ) :=
  let d := discNum f
  let sqf := cSqfreeYunFFG fuel d
  -- distinct nonconstant squarefree factors, each made monic
  let distinct := (sqf.map cmonicG).filter (fun p => 0 < cdegG p)
  distinct.filter (fun p => cisZeroG (cmodG (d.length + 1) d (cmulG p p)))

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

end DeepWiki.SymbolicIntegration
