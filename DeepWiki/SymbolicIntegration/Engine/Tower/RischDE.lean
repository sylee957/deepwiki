import DeepWiki.SymbolicIntegration.Engine.Tower.Lvl2
import DeepWiki.SymbolicIntegration.Engine.Tower.Deriv
import DeepWiki.SymbolicIntegration.Engine.Tower.Integrate
import DeepWiki.SymbolicIntegration.Engine.QFunReduce
import DeepWiki.SymbolicIntegration.Engine.RischFieldCore
import DeepWiki.SymbolicIntegration.Engine.Hyperexp.Eta
import DeepWiki.ComputableAlgebra.PolyEngine

/-! # Carrier-generic Risch-DE helper defs over the tower

The carrier-generic building blocks of the Risch-DE pipeline: the residue positive-integer-root test,
the degree bound, and a shared level-2 right-hand side. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open DensePoly

universe u

/-! ### Positive-integer-root test for residue resultants

The weak normalizer needs the positive integer roots of the residue resultant `r ∈ α[z]`; the nodes
`n : ℕ` are lifted by the `[CField α]`-only natural cast `cnatCast`. -/

namespace DensePoly

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P] {α : Type u} [CField α]

/-- `cisRootNat r n = true` iff `r(cnatCast n) = 0` in `α` (Horner via `ceval`): whether the
natural number `n`, lifted to `α`, is a root of `r`. -/
def cisRootNat (r : P α) (n : ℕ) : Bool :=
  CCommRing.isZero (CPolyEngine.eval r (cnatCast n))

/-- `cPosIntRoots r bound = [n ∈ {1,…,bound} : r(cnatCast n) = 0]`: the positive integer roots of
`r` up to `bound`; empty for an already-weakly-normalized input. -/
def cPosIntRoots (r : P α) (bound : ℕ) : List ℕ :=
  (List.range bound).filterMap (fun k =>
    let n : ℕ := k + 1
    if cisRootNat r n then some n else none)

example :
    cPosIntRoots (CPoly.SparsePoly.ofList [(0, (-1 : ℚ)), (2, 1)]) 4 = [1] := by
  native_decide

end DensePoly

/-! ### The generic degree bound over the tower

`cRdeBoundDegree` is the explicit `deg_t(q)` upper bound, case-split by `δ = deg(Dt)`. Purely
list-degree arithmetic — `[CField α]`-only. -/

namespace DensePoly

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P] {α : Type u} [CField α]

/-- Generic degree bound `cRdeBoundDegree Dt a b c = n ∈ ℕ`: an upper bound on `deg_t(q)` for any
polynomial solution `q ∈ α[t]` of `a·Dq + b·q = c`. With `d_a, d_b, d_c` the degrees and `δ = deg(Dt)`:
nonlinear (`δ ≥ 2`) `max(0, d_c − max(d_a + δ − 1, d_b))`; hyperexponential (`δ = 1`)
`max(0, d_c − max(d_b, d_a))`; primitive (`δ = 0`) `max(0, d_c − d_b)` if `d_b > d_a` else
`max(0, d_c − d_a + 1)`. -/
def cRdeBoundDegree (Dt : P α) (a b c : P α) : ℕ :=
  let da : ℤ := (CPolyEngine.cdeg a : ℤ)
  let db : ℤ := (CPolyEngine.cdeg b : ℤ)
  let dc : ℤ := (CPolyEngine.cdeg c : ℤ)
  let δ : ℤ := (CPolyEngine.cdeg Dt : ℤ)
  let n : ℤ :=
    if 2 ≤ δ then
      max 0 (dc - max (da + δ - 1) db)
    else if δ = 1 then
      max 0 (dc - max db da)
    else
      if da < db then max 0 (dc - db) else max 0 (dc - da + 1)
  n.toNat

example :
    cRdeBoundDegree
      (CPoly.SparsePoly.ofList [(2, (1 : ℚ))])
      (CPoly.SparsePoly.ofList [(0, 1)])
      (CPoly.SparsePoly.ofList [(0, 1)])
      (CPoly.SparsePoly.ofList [(3, 1)]) = 2 := by
  native_decide

end DensePoly

/-! ### Shared level-2 RDE data

The level-2 right-hand side below is reused by the fuel-free RDE and sound-solver validations. -/

/-- The level-2 right-hand side `g = t₁ + 1 ∈ Lvl2 = ℚ(x)(t₁)` (`lvl2T1` is `t₁`). -/
def towerRdeLvl2GPlusOne : Lvl2 := CCommRing.add lvl2T1 CCommRing.one

end DeepWiki.SymbolicIntegration
