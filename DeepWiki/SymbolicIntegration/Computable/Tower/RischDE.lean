import DeepWiki.SymbolicIntegration.Computable.Tower.Field
import DeepWiki.SymbolicIntegration.Computable.Tower.Deriv
import DeepWiki.SymbolicIntegration.Computable.Tower.Integrate
import DeepWiki.SymbolicIntegration.Computable.QFunReduce
import DeepWiki.SymbolicIntegration.Computable.RischFieldCore
import DeepWiki.SymbolicIntegration.Computable.Hyperexp.Eta

/-! # Fuel-agnostic §6 RDE helper defs over the tower

The carrier-generic, fuel-agnostic building blocks of the §6 Risch-DE pipeline that survive the
fuel-free switch: the residue positive-integer-root test, the §6.3 degree bound, the primitive
polynomial antiderivative, and the shared level-2 right-hand side. The fuel-threaded stage functions
(weak normalizer, normal/special denominator, SPDE, PolyRischDE dispatcher, and the assembled oracle)
were retired in favour of their well-founded `…Wf` companions (`Tower/RischDEWellFounded.lean`), which
the `CRischField (QFunNZG β)` instance (`Tower/RischDEInstance.lean`) now runs. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

/-! ### Positive-integer-root test for residue resultants

The weak normalizer needs the positive integer roots of the residue resultant `r ∈ α[z]`; the nodes
`n : ℕ` are lifted by the `[CField α]`-only natural cast `cnatCastG`. -/

namespace CPolyG

variable {α : Type*} [CField α]

/-- `cisRootNatG r n = true` iff `r(cnatCastG n) = 0` in `α` (Horner via `cHornerG`): whether the
natural number `n`, lifted to `α`, is a root of `r`. -/
def cisRootNatG (r : CPolyG α) (n : ℕ) : Bool :=
  CField.isZero (cHornerG r (cnatCastG n))

/-- `cPosIntRootsG r bound = [n ∈ {1,…,bound} : r(cnatCastG n) = 0]`: the positive integer roots of
`r` up to `bound` — the multiplicities of the weak-normalizer product; empty for an
already-weakly-normalized input. -/
def cPosIntRootsG (r : CPolyG α) (bound : ℕ) : List ℕ :=
  (List.range bound).filterMap (fun k =>
    let n : ℕ := k + 1
    if cisRootNatG r n then some n else none)

end CPolyG

/-! ### The generic §6.3 degree bound over the tower

`cRdeBoundDegreeG` is the explicit `deg_t(q)` upper bound, case-split by `δ = deg(Dt)`. Purely
list-degree arithmetic — `[CField α]`-only. The cancellation refinements (Ch. 7) are documented but
not run. -/

namespace CPolyG

variable {α : Type*} [CField α]

/-- **Generic degree bound** `cRdeBoundDegreeG Dt a b c = n ∈ ℕ` (Bronstein §6.3, book p.198–201): an
upper bound on `deg_t(q)` for any polynomial solution `q ∈ α[t]` of `a·Dq + b·q = c`. With `d_a, d_b,
d_c` the degrees and `δ = deg(Dt)`: nonlinear (`δ ≥ 2`) `max(0, d_c − max(d_a + δ − 1, d_b))`;
hyperexponential (`δ = 1`) `max(0, d_c − max(d_b, d_a))`; primitive (`δ = 0`) `max(0, d_c − d_b)` if
`d_b > d_a` else `max(0, d_c − d_a + 1)`. The non-cancellation formula reproduced exactly; the
cancellation refinements are the documented continuation. -/
def cRdeBoundDegreeG (Dt : CPolyG α) (a b c : CPolyG α) : ℕ :=
  let da : ℤ := (cdegG a : ℤ)
  let db : ℤ := (cdegG b : ℤ)
  let dc : ℤ := (cdegG c : ℤ)
  let δ : ℤ := (cdegG Dt : ℤ)
  let n : ℤ :=
    if 2 ≤ δ then
      max 0 (dc - max (da + δ - 1) db)
    else if δ = 1 then
      max 0 (dc - max db da)
    else
      if da < db then max 0 (dc - db) else max 0 (dc - da + 1)
  n.toNat

/-! ### The generic primitive `b = 0` integration branch (Bronstein §6.5, the `cIntegratePolyQ` analog)

When `b = 0` the equation `Dq + b·q = c` is the pure integration `Dq = c`. In the primitive base case
the monomial is the canonical iterating variable (`Dt = 1`, `δ = 0`) with *constant* coefficients, so
integration is **termwise**: `∫ Σ cᵢtⁱ = Σ (cᵢ/(i+1)) t^{i+1}`. The `[CField α]`-generic mirror of
`cIntegratePolyQ`; the division by `(i+1)` is `CField.div · (cnatCastG (i+1))`. -/

/-- **Generic polynomial antiderivative** `cIntegratePolyG c = q` with `Dq = c` and `q(0) = 0`, for the
canonical primitive monomial (`Dt = 1`) and constant coefficients: termwise
`∫ Σ cᵢtⁱ = Σ (cᵢ/(i+1)) t^{i+1}` (`cᵢ/(i+1) = CField.div cᵢ (cnatCastG (i+1))`). The `[CField α]`-generic
mirror of `cIntegratePolyQ`, the `b = 0` branch of the primitive PolyRischDE. -/
def cIntegratePolyG (c : CPolyG α) : CPolyG α :=
  CField.zero :: ((c : List α).zipIdx.map (fun (a, i) => CField.div a (cnatCastG (i + 1))))

end CPolyG

/-! ### Shared level-2 RDE data

The level-2 right-hand side below is reused by the fuel-free RDE and sound-solver validations. -/

/-- The level-2 right-hand side `g = t₁ + 1 ∈ Lvl2 = ℚ(x)(t₁)` for the non-trivial-`f` headline case
(`lvl2T1` from `ComputableTowerDeriv` is `t₁`). -/
def towerRdeLvl2GPlusOne : Lvl2 := CField.add lvl2T1 CField.one

end DeepWiki.SymbolicIntegration
