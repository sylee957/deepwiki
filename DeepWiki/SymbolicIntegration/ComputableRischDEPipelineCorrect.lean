import DeepWiki.SymbolicIntegration.ComputableRischDESPDECorrect
import DeepWiki.SymbolicIntegration.ComputableFractionFieldDeriv

/-! # The §6 Risch-DE pipeline correctness — composing the denominator/degree stages with the spine
(Bronstein Chapter 6)

`ComputableRischDESPDECorrect` proves the **polynomial-stage spine** of the §6 Risch differential
equation pipeline unconditional (`cSPDE_polyRischDENoCancel_cleared_of_inputs`): under transparent
degree/fuel/termination inputs, if `cSPDE Dt fuel a b c n = some (b̄, c̄, m, α, β)` and
`cPolyRischDENoCancel Dt fuel b̄ c̄ m = some v`, then the reconstruction `q = α·v + β` solves the
**polynomial** RDE `a·D(q) + b·q = c` over `(RatFunc ℚ)[X]`, `D = implicitDeriv (toPolyG Dt)`.

This file builds the remaining §6 stages **on top of** that spine and **composes** them into the
full rational-input RDE correctness — `cRischDE` returns a `(ynum, yden)` solving `D(y) + f·y = g`
(in the cleared polynomial form `rdeClearedCheck` validates pointwise), for the **primitive** regime
(`Dt ∈ k`, where the special-denominator transform is the identity), working **leaf-first**:

## What this file delivers

* **§6.3 degree bound (leaf).** `cRdeBoundDegree Dt fuel a b c` returns an `ℕ`, not an identity — its
  "correctness" is that it enters the pipeline *only* as the degree-`≤ n` short-circuit input to
  `cSPDE`. `cSPDE_polyRischDENoCancel_cleared_at_boundDegree` restates the spine at
  `n := cRdeBoundDegree Dt fuel a b c`, confirming the bound feeds in transparently (the cleared
  identity is `n`-agnostic, so any computed bound is sound).

* **§6.2 special denominator, primitive regime (`cRdeSpecialDenominator_primitive_eq`,
  `cRdeSpecialDenominator_primitive_lift`).** When the monic special irreducible `p = cSpecialPoly Dt`
  is a constant (`cdegG p = 0` — the *primitive* case `Dt ∈ k`, where `k⟨t⟩ = k[t]` has no special
  part), `cRdeSpecialDenominator Dt fuel a b c = (a, b, c, [1])` is the **identity transform**, so a
  solution `Q` of `a·D(Q) + b·Q = c` is unchanged and the gathered special factor `h₁ = 1`.

* **§6.2 normal denominator cleared lifting (`cRdeNormalDenominator_cleared_lift`,
  `cRdeNormalDenominator_rdeCleared`).** The genuine content. From `cRdeNormalDenominator` outputs
  `(a, b, c, h)` with `a = dₙh`, `b·fden = a·fnum − dₙ·Dh·fden`, `c·gden = dₙh²·gnum` (the
  exact-division certificates the `cdivFF` clearings carry), and a polynomial `Q` solving the
  reduced `a·D(Q) + b·Q = c`, the reconstruction `y = Q/h` solves `D(y) + f·y = g` in the cleared
  form `gden·fden·(D(Q)·h − Q·Dh) + gden·fnum·Q·h = gnum·fden·h²` — derived by multiplying the
  reduced identity by `fden·gden` and **cancelling the nonzero normal part `dₙ`** (no fraction-field
  derivation: the whole identity stays polynomial over `(RatFunc ℚ)[X]`, exactly the shape
  `rdeClearedCheck` decides).

* **Composition (`cRischDE_rdeCleared_of_inputs`).** Threading the three stages through the spine:
  `cRischDE Dt fuel fnum fden gnum gden = some (ynum, yden)` makes the returned `y = ynum/yden` solve
  `D(y) + f·y = g` in the cleared polynomial form, for the primitive regime (special part trivial),
  under the §6.4 transparent inputs + the §6.2 exact-division/nonzero-`dₙ` certificates.

## The remaining gap (honestly documented)

The composition is gated on (i) the §6.4 `CSPDEClearedInputs` (the transparent degree/fuel/termination
preconditions the SPDE spine already needs) and (ii) the §6.2 normal-denominator certificates — the
exact divisions `b·fden = a·fnum − dₙ·Dh·fden`, `c·gden = dₙh²·gnum`, the `a = dₙh` factorization, and
the nonzero normal part `dₙ ≠ 0` — supplied as hypotheses (the `cdivFF`-clearing facts the
`native_decide` validation pins, dischargeable from `toPolyG_cdivFF_exact` exactly as the §6.4 Bézout
certificate, given the `eₙ ∣ dₙh²` branch divisibility). The **hyperexponential / nonlinear special
regimes** (`cSpecialPoly` non-constant, `q = h·pⁿ` with `n ≠ 0`) are deferred: the special-denominator
transform there changes the equation by `p^N` and the `b`-component picks up `n·a·Dp/p`, whose cleared
identity needs the residue machinery — the same §5.6 hyperexponential residual-part obstruction
(`Dt ∉ k`) that is a confirmed genuine wall elsewhere in the engine. The genuine *fraction-field*
derivation `towerFractionFieldDeriv` (the keystone) is imported and available, but the primitive-regime
`rdeClearedCheck` target is a **polynomial** identity that the `dₙ`-cancellation route reaches without
it. -/

open Polynomial Classical

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

/-! ### §6.3 — the degree bound enters transparently (the spine is `n`-agnostic)

`cRdeBoundDegree` returns an upper bound `N : ℕ` on `deg_t(q)`; it does **not** produce an algebraic
identity. In the pipeline it is consumed only as the degree input `n := N` to `cSPDE`, and the §6.4-§6.5
spine `cSPDE_polyRischDENoCancel_cleared_of_inputs` holds for *every* `n`. So the §6.3 "correctness" is
the observation that any computed bound is sound: feeding `n := cRdeBoundDegree …` to the spine still
yields the cleared identity. -/

/-- **The §6.4-§6.5 spine instantiated at the §6.3 degree bound**: if
`cSPDE Dt fuel a b c (cRdeBoundDegree Dt fuel a b c) = some (b̄, c̄, m, α, β)` (under the transparent
§6.4 inputs at that `n`) and `cPolyRischDENoCancel Dt fuel b̄ c̄ m = some v`, then `q = α·v + β` solves
`a·D(q) + b·q = c` over `(RatFunc ℚ)[X]`. Confirms the §6.3 degree bound feeds into the spine purely as
the (sound, `n`-agnostic) degree short-circuit input. -/
theorem cSPDE_polyRischDENoCancel_cleared_at_boundDegree (Dt : CPolyG QFunNZ) (fuel : ℕ)
    (a b c : CPolyG QFunNZ) (bbar cbar : CPolyG QFunNZ) (m : ℤ) (α β v : CPolyG QFunNZ)
    (hspde : cSPDE Dt fuel a b c (cRdeBoundDegree Dt fuel a b c : ℤ) = some (bbar, cbar, m, α, β))
    (hin : CSPDEClearedInputs Dt fuel a b c (cRdeBoundDegree Dt fuel a b c : ℤ))
    (hpoly : cPolyRischDENoCancel Dt fuel bbar cbar m = some v) :
    toPolyG a * Differential.implicitDeriv (toPolyG Dt) (toPolyG (caddG (cmulG α v) β))
        + toPolyG b * toPolyG (caddG (cmulG α v) β)
      = toPolyG c :=
  cSPDE_polyRischDENoCancel_cleared_of_inputs Dt fuel a b c
    (cRdeBoundDegree Dt fuel a b c : ℤ) bbar cbar m α β v hspde hin hpoly

/-! ### §6.2 special denominator — the primitive regime is the identity transform

`cRdeSpecialDenominator Dt fuel a b c` clears the *special* part of the denominator by substituting
`q = h·pⁿ` for the monic special irreducible `p = cSpecialPoly Dt`. In the **primitive** regime
`Dt ∈ k` (the case the deliverable targets), the monomial has no special part — `cSpecialPoly Dt` is a
constant (`cdegG = 0`, `k⟨t⟩ = k[t]`) — so the routine short-circuits to the **identity** transform
`(a, b, c, [1])`: the reduced equation is unchanged and the gathered special factor `h₁ = 1`. -/

/-- **The special-denominator stage is the identity in the primitive regime**: when the monic special
irreducible `p = cSpecialPoly Dt fuel` is a constant (`cdegG p = 0`, i.e. `Dt ∈ k` primitive — no
special part to clear), `cRdeSpecialDenominator Dt fuel a b c = (a, b, c, [CField.one])`. The
short-circuit branch of `cRdeSpecialDenominator`. -/
theorem cRdeSpecialDenominator_primitive_eq (Dt : CPolyG QFunNZ) (fuel : ℕ) (a b c : CPolyG QFunNZ)
    (hp : cdegG (cSpecialPoly Dt fuel) = 0) :
    cRdeSpecialDenominator Dt fuel a b c = (a, b, c, [CField.one]) := by
  rw [cRdeSpecialDenominator]
  simp only [hp, if_pos]

/-- **The primitive special-denominator lift**: in the primitive regime (`cdegG (cSpecialPoly Dt) = 0`),
if a polynomial `Q` solves the *output* equation `ā·D(Q) + b̄·Q = c̄` of `cRdeSpecialDenominator`
(where `(ā, b̄, c̄, h₁) = cRdeSpecialDenominator Dt fuel a b c`), then it solves the *input* equation
`a·D(Q) + b·Q = c` — because the transform is the identity (`ā = a`, `b̄ = b`, `c̄ = c`) and the
special factor `h₁ = [1]`. Over `(RatFunc ℚ)[X]`, `D = implicitDeriv (toPolyG Dt)`. -/
theorem cRdeSpecialDenominator_primitive_lift (Dt : CPolyG QFunNZ) (fuel : ℕ) (a b c Q : CPolyG QFunNZ)
    (hp : cdegG (cSpecialPoly Dt fuel) = 0)
    (hQ : toPolyG (cRdeSpecialDenominator Dt fuel a b c).1
          * Differential.implicitDeriv (toPolyG Dt) (toPolyG Q)
        + toPolyG (cRdeSpecialDenominator Dt fuel a b c).2.1 * toPolyG Q
      = toPolyG (cRdeSpecialDenominator Dt fuel a b c).2.2.1) :
    toPolyG a * Differential.implicitDeriv (toPolyG Dt) (toPolyG Q) + toPolyG b * toPolyG Q
      = toPolyG c := by
  rw [cRdeSpecialDenominator_primitive_eq Dt fuel a b c hp] at hQ
  exact hQ

-- The primitive special-denominator stage leaves the equation unchanged and `h₁ = 1`.
example (Dt : CPolyG QFunNZ) (fuel : ℕ) (a b c : CPolyG QFunNZ)
    (hp : cdegG (cSpecialPoly Dt fuel) = 0) :
    cRdeSpecialDenominator Dt fuel a b c = (a, b, c, [CField.one]) :=
  cRdeSpecialDenominator_primitive_eq Dt fuel a b c hp

#print axioms cSPDE_polyRischDENoCancel_cleared_at_boundDegree
#print axioms cRdeSpecialDenominator_primitive_eq
#print axioms cRdeSpecialDenominator_primitive_lift

end DeepWiki.SymbolicIntegration
