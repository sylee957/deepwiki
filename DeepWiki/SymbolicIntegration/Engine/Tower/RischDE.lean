import DeepWiki.SymbolicIntegration.Engine.Tower.Field
import DeepWiki.SymbolicIntegration.Engine.Tower.Deriv
import DeepWiki.SymbolicIntegration.Engine.Tower.Integrate
import DeepWiki.SymbolicIntegration.Engine.QFunReduce
import DeepWiki.SymbolicIntegration.Engine.RischFieldCore
import DeepWiki.SymbolicIntegration.Engine.Hyperexp.Eta

/-! # Carrier-generic Risch-DE helper defs over the tower

The carrier-generic building blocks of the Risch-DE pipeline: the residue positive-integer-root test,
the degree bound, the primitive polynomial antiderivative, and a shared level-2 right-hand side. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open CPoly

/-! ### Positive-integer-root test for residue resultants

The weak normalizer needs the positive integer roots of the residue resultant `r ∈ α[z]`; the nodes
`n : ℕ` are lifted by the `[CField α]`-only natural cast `cnatCast`. -/

namespace CPoly

variable {α : Type*} [CField α]

/-- `cisRootNat r n = true` iff `r(cnatCast n) = 0` in `α` (Horner via `cHorner`): whether the
natural number `n`, lifted to `α`, is a root of `r`. -/
def cisRootNat (r : CPoly α) (n : ℕ) : Bool :=
  CField.isZero (cHorner r (cnatCast n))

/-- `cPosIntRoots r bound = [n ∈ {1,…,bound} : r(cnatCast n) = 0]`: the positive integer roots of
`r` up to `bound`; empty for an already-weakly-normalized input. -/
def cPosIntRoots (r : CPoly α) (bound : ℕ) : List ℕ :=
  (List.range bound).filterMap (fun k =>
    let n : ℕ := k + 1
    if cisRootNat r n then some n else none)

end CPoly

/-! ### The generic degree bound over the tower

`cRdeBoundDegree` is the explicit `deg_t(q)` upper bound, case-split by `δ = deg(Dt)`. Purely
list-degree arithmetic — `[CField α]`-only. -/

namespace CPoly

variable {α : Type*} [CField α]

/-- Generic degree bound `cRdeBoundDegree Dt a b c = n ∈ ℕ`: an upper bound on `deg_t(q)` for any
polynomial solution `q ∈ α[t]` of `a·Dq + b·q = c`. With `d_a, d_b, d_c` the degrees and `δ = deg(Dt)`:
nonlinear (`δ ≥ 2`) `max(0, d_c − max(d_a + δ − 1, d_b))`; hyperexponential (`δ = 1`)
`max(0, d_c − max(d_b, d_a))`; primitive (`δ = 0`) `max(0, d_c − d_b)` if `d_b > d_a` else
`max(0, d_c − d_a + 1)`. -/
def cRdeBoundDegree (Dt : CPoly α) (a b c : CPoly α) : ℕ :=
  let da : ℤ := (cdeg a : ℤ)
  let db : ℤ := (cdeg b : ℤ)
  let dc : ℤ := (cdeg c : ℤ)
  let δ : ℤ := (cdeg Dt : ℤ)
  let n : ℤ :=
    if 2 ≤ δ then
      max 0 (dc - max (da + δ - 1) db)
    else if δ = 1 then
      max 0 (dc - max db da)
    else
      if da < db then max 0 (dc - db) else max 0 (dc - da + 1)
  n.toNat

/-! ### The generic primitive `b = 0` integration branch

When `b = 0` the equation `Dq + b·q = c` is the pure integration `Dq = c`; for the canonical primitive
monomial (`Dt = 1`) with constant coefficients this is termwise `∫ Σ cᵢtⁱ = Σ (cᵢ/(i+1)) t^{i+1}`. -/

/-- Generic polynomial antiderivative `cIntegratePoly c = q` with `Dq = c` and `q(0) = 0`, for the
canonical primitive monomial (`Dt = 1`) and constant coefficients: termwise
`∫ Σ cᵢtⁱ = Σ (cᵢ/(i+1)) t^{i+1}` (`cᵢ/(i+1) = CField.div cᵢ (cnatCast (i+1))`). -/
def cIntegratePoly (c : CPoly α) : CPoly α :=
  CField.zero :: ((c : List α).zipIdx.map (fun (a, i) => CField.div a (cnatCast (i + 1))))

end CPoly

/-! ### Shared level-2 RDE data

The level-2 right-hand side below is reused by the fuel-free RDE and sound-solver validations. -/

/-- The level-2 right-hand side `g = t₁ + 1 ∈ Lvl2 = ℚ(x)(t₁)` (`lvl2T1` is `t₁`). -/
def towerRdeLvl2GPlusOne : Lvl2 := CField.add lvl2T1 CField.one

end DeepWiki.SymbolicIntegration
