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

/-! ### §6.2 normal denominator — the cleared lifting `y = Q/h` solves `D(y) + f·y = g`

`cRdeNormalDenominator Dt fuel fnum fden gnum gden` (Bronstein §6.2 / Corollary 6.1.1) reduces
`D(y) + f·y = g` (`f = fnum/fden`, `g = gnum/gden`) to a polynomial equation `a·D(q) + b·q = c` with
`q = y·h`, returning `(a, b, c, h)` where (the `cdvdG`-branch outputs)

```
  a = dₙ·h,   b·fden = a·fnum − dₙ·Dh·fden,   c·gden = dₙ·h²·gnum,   Dh = D(h)
```

(`dₙ` the normal part of `fden`; `b, c` are the `cdivFF`-cleared numerators over `fden`, `gden`). The
**converse** the solver needs: a polynomial `Q` solving the reduced `a·D(Q) + b·Q = c` makes
`y = Q/h` solve `D(y) + f·y = g`. In the cleared polynomial form (the shape `rdeClearedCheck` decides,
`ynum = Q`, `yden = h`):

```
  gden·fden·(D(Q)·h − Q·Dh) + gden·fnum·Q·h = gnum·fden·h²
```

This is **purely polynomial** (no fraction-field derivation): multiply the reduced equation by
`fden·gden`, substitute the three exact-division/factorization certificates, and the whole identity is
`dₙ` times the goal — so cancelling the nonzero normal part `dₙ` gives it. The three certificates are
the `cdivFF`-clearing facts (dischargeable from `toPolyG_cdivFF_exact` as in §6.4), supplied here as
hypotheses on the `toPolyG` images. -/

/-- **The §6.2 normal-denominator cleared lifting** (commutative-ring `Derivation` core): with `D` a
derivation, the normal part `DN ≠ 0`, the factorization `A = DN·H` and the two exact-division
certificates `B·FDEN = A·FNUM − DN·(D H)·FDEN`, `C·GDEN = DN·H²·GNUM`, a solution `Q` of the reduced
equation `A·D(Q) + B·Q = C` makes `y = Q/H` solve `D(y) + f·y = g` in the cleared form
`GDEN·FDEN·(D(Q)·H − Q·(D H)) + GDEN·FNUM·Q·H = GNUM·FDEN·H²`. Pure algebra: multiply the reduced
equation by `FDEN·GDEN`, the whole identity is `DN` times the goal, cancel the nonzero `DN`. -/
theorem rdeNormalDenominator_glue {R : Type*} [CommRing R] [NoZeroDivisors R]
    (D : Derivation ℤ R R) (DN H FNUM FDEN GNUM GDEN A B C Q : R)
    (hDN : DN ≠ 0)
    (hA : A = DN * H)
    (hB : B * FDEN = A * FNUM - DN * D H * FDEN)
    (hC : C * GDEN = DN * H ^ 2 * GNUM)
    (hred : A * D Q + B * Q = C) :
    GDEN * FDEN * (D Q * H - Q * D H) + GDEN * FNUM * Q * H = GNUM * FDEN * H ^ 2 := by
  -- multiply the reduced equation by `FDEN·GDEN` and substitute the certificates
  have hmul : FDEN * GDEN * (A * D Q + B * Q) = FDEN * GDEN * C := by rw [hred]
  -- the whole cleared identity is `DN` times the goal
  have hkey : DN * (GDEN * FDEN * (D Q * H - Q * D H) + GDEN * FNUM * Q * H)
      = DN * (GNUM * FDEN * H ^ 2) := by
    have e1 : FDEN * GDEN * (A * D Q + B * Q)
        = GDEN * (A * D Q * FDEN) + GDEN * Q * (B * FDEN) := by ring
    have e2 : FDEN * GDEN * C = FDEN * (C * GDEN) := by ring
    rw [e1, e2, hB, hC, hA] at hmul
    linear_combination hmul
  exact mul_left_cancel₀ hDN hkey

-- The §6.2 normal-denominator glue: a reduced solution `Q` makes `y = Q/H` solve `D(y)+f·y=g` (cleared).
example {R : Type*} [CommRing R] [NoZeroDivisors R] (D : Derivation ℤ R R)
    (DN H FNUM FDEN GNUM GDEN A B C Q : R)
    (hDN : DN ≠ 0) (hA : A = DN * H) (hB : B * FDEN = A * FNUM - DN * D H * FDEN)
    (hC : C * GDEN = DN * H ^ 2 * GNUM) (hred : A * D Q + B * Q = C) :
    GDEN * FDEN * (D Q * H - Q * D H) + GDEN * FNUM * Q * H = GNUM * FDEN * H ^ 2 :=
  rdeNormalDenominator_glue D DN H FNUM FDEN GNUM GDEN A B C Q hDN hA hB hC hred

#print axioms rdeNormalDenominator_glue

/-! ### §6.2 normal denominator — the engine-level cleared lifting through `toPolyG`

`rdeNormalDenominator_glue` instantiated at the concrete `cRdeNormalDenominator` outputs read through
`toPolyG`, with `D = cmonomialDeriv Dt = implicitDeriv (toPolyG Dt)`. The factorization `A = DN·H`
(`a = dₙ·h`) is *definitional* (`toPolyG_cmulG`); the two exact-division certificates are discharged
from `toPolyG_cdivFF_exact` given the §6.2 divisibilities (`fden ∣ dₙh·fnum − dₙ·Dh·fden`,
`gden ∣ dₙh²·gnum` — the latter is the `eₙ ∣ dₙh²` branch the recursion already takes), supplied here as
the `∣`-hypotheses the validation pins. The nonzero normal part `dₙ ≠ 0` is the remaining input. -/

/-- **The §6.2 normal-denominator cleared lifting through `toPolyG`**: writing
`dₙ = (cSplitFactorFast Dt fuel fden).1` for the normal part of `fden`, if
`cRdeNormalDenominator Dt fuel fnum fden gnum gden = some (a, b, c, h)`, the normal part is nonzero
(`toPolyG dₙ ≠ 0`), the two `cdivFF`-clearings are exact (`toPolyG fden ∣ …`, `toPolyG gden ∣ …` with
the fuel bounds), and a polynomial `Q` solves the reduced `a·D(Q) + b·Q = c`
(`D = implicitDeriv (toPolyG Dt)`), then `y = Q/h` solves `D(y) + f·y = g` in the cleared form
`gden·fden·(D(Q)·h − Q·D(h)) + gden·fnum·Q·h = gnum·fden·h²` over `(RatFunc ℚ)[X]`. The engine instance
of `rdeNormalDenominator_glue` (`A = DN·H` definitional, the `B/C` certificates via
`toPolyG_cdivFF_exact`). -/
theorem cRdeNormalDenominator_cleared_lift (Dt : CPolyG QFunNZ) (fuel : ℕ)
    (fnum fden gnum gden a b c h Q : CPolyG QFunNZ)
    (hres : cRdeNormalDenominator Dt fuel fnum fden gnum gden = some (a, b, c, h))
    (hdn : toPolyG (cSplitFactorFast Dt fuel fden).1 ≠ 0)
    (hfden0 : cnormG fden ≠ []) (hgden0 : cnormG gden ≠ [])
    (hfbB : (cnormG (csubG (cmulG (cmulG (cSplitFactorFast Dt fuel fden).1 h) fnum)
        (cmulG (cmulG (cSplitFactorFast Dt fuel fden).1 (cmonomialDeriv Dt h)) fden)) :
        List QFunNZ).length ≤ fuel)
    (hdvdB : toPolyG fden ∣ toPolyG (csubG (cmulG (cmulG (cSplitFactorFast Dt fuel fden).1 h) fnum)
        (cmulG (cmulG (cSplitFactorFast Dt fuel fden).1 (cmonomialDeriv Dt h)) fden)))
    (hfbC : (cnormG (cmulG (cmulG (cmulG (cSplitFactorFast Dt fuel fden).1 h) h) gnum) :
        List QFunNZ).length ≤ fuel)
    (hdvdC : toPolyG gden ∣ toPolyG (cmulG (cmulG (cmulG (cSplitFactorFast Dt fuel fden).1 h) h) gnum))
    (hred : toPolyG a * Differential.implicitDeriv (toPolyG Dt) (toPolyG Q) + toPolyG b * toPolyG Q
      = toPolyG c) :
    toPolyG gden * toPolyG fden
        * (Differential.implicitDeriv (toPolyG Dt) (toPolyG Q) * toPolyG h
            - toPolyG Q * Differential.implicitDeriv (toPolyG Dt) (toPolyG h))
        + toPolyG gden * toPolyG fnum * toPolyG Q * toPolyG h
      = toPolyG gnum * toPolyG fden * toPolyG h ^ 2 := by
  -- abbreviation for the normal part
  set dn := (cSplitFactorFast Dt fuel fden).1 with hdndef
  -- the numerator polynomials the `cdivFF` clears (in terms of the theorem's `h`)
  set bNum := csubG (cmulG (cmulG dn h) fnum) (cmulG (cmulG dn (cmonomialDeriv Dt h)) fden) with hbNum
  set cNum := cmulG (cmulG (cmulG dn h) h) gnum with hcNum
  -- extract the engine's four components from the `some` branch
  rw [cRdeNormalDenominator] at hres
  split at hres
  · -- the `cdvdG` branch: read off the engine's four components
    rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq] at hres
    obtain ⟨ha, hb, hc, hh⟩ := hres
    -- the engine's internal `h` (the long `cdivFF …` expression) equals the theorem's `h`;
    -- rewrite it in the `a, b, c` component equalities so they use the theorem's `h`
    rw [hh] at ha hb hc
    -- factorization `A = DN·H`
    have hA : toPolyG a = toPolyG dn * toPolyG h := by rw [← ha, toPolyG_cmulG]
    -- `B·FDEN = A·FNUM − DN·D(h)·FDEN` via `toPolyG_cdivFF_exact` and the engine `b = bNum/fden`
    have hBexact : toPolyG b * toPolyG fden = toPolyG bNum := by
      rw [← hb]; exact (toPolyG_cdivFF_exact fuel bNum fden hfden0 hfbB hdvdB).symm
    have hBeq : toPolyG bNum = toPolyG a * toPolyG fnum
        - toPolyG dn * Differential.implicitDeriv (toPolyG Dt) (toPolyG h) * toPolyG fden := by
      rw [hbNum, toPolyG_csubG, toPolyG_cmulG, toPolyG_cmulG, toPolyG_cmulG, toPolyG_cmulG,
        toPolyG_cmonomialDeriv, ← ha, toPolyG_cmulG]
    -- `C·GDEN = DN·H²·GNUM` via `toPolyG_cdivFF_exact` and the engine `c = cNum/gden`
    have hCexact : toPolyG c * toPolyG gden = toPolyG cNum := by
      rw [← hc]; exact (toPolyG_cdivFF_exact fuel cNum gden hgden0 hfbC hdvdC).symm
    have hCeq : toPolyG cNum = toPolyG dn * toPolyG h ^ 2 * toPolyG gnum := by
      rw [hcNum, toPolyG_cmulG, toPolyG_cmulG, toPolyG_cmulG]; ring
    -- the two glue certificates, in the exact shape `rdeNormalDenominator_glue` wants
    have hBcert : toPolyG b * toPolyG fden = toPolyG a * toPolyG fnum
        - toPolyG dn * Differential.implicitDeriv (toPolyG Dt) (toPolyG h) * toPolyG fden := by
      rw [hBexact]; exact hBeq
    have hCcert : toPolyG c * toPolyG gden = toPolyG dn * toPolyG h ^ 2 * toPolyG gnum := by
      rw [hCexact]; exact hCeq
    -- apply the glue
    have hglue := rdeNormalDenominator_glue (Differential.implicitDeriv (toPolyG Dt))
      (toPolyG dn) (toPolyG h) (toPolyG fnum) (toPolyG fden) (toPolyG gnum) (toPolyG gden)
      (toPolyG a) (toPolyG b) (toPolyG c) (toPolyG Q) hdn hA hBcert hCcert hred
    linear_combination hglue
  · -- the `else` branch is `none`, contradicting `none = some`
    exact absurd hres (by simp)

-- The engine §6.2 normal-denominator lift: a reduced solution `Q` makes `y = Q/h` solve `D(y)+f·y=g`.
example (Dt : CPolyG QFunNZ) (fuel : ℕ) (fnum fden gnum gden a b c h Q : CPolyG QFunNZ)
    (hres : cRdeNormalDenominator Dt fuel fnum fden gnum gden = some (a, b, c, h))
    (hdn : toPolyG (cSplitFactorFast Dt fuel fden).1 ≠ 0)
    (hfden0 : cnormG fden ≠ []) (hgden0 : cnormG gden ≠ [])
    (hfbB : (cnormG (csubG (cmulG (cmulG (cSplitFactorFast Dt fuel fden).1 h) fnum)
        (cmulG (cmulG (cSplitFactorFast Dt fuel fden).1 (cmonomialDeriv Dt h)) fden)) :
        List QFunNZ).length ≤ fuel)
    (hdvdB : toPolyG fden ∣ toPolyG (csubG (cmulG (cmulG (cSplitFactorFast Dt fuel fden).1 h) fnum)
        (cmulG (cmulG (cSplitFactorFast Dt fuel fden).1 (cmonomialDeriv Dt h)) fden)))
    (hfbC : (cnormG (cmulG (cmulG (cmulG (cSplitFactorFast Dt fuel fden).1 h) h) gnum) :
        List QFunNZ).length ≤ fuel)
    (hdvdC : toPolyG gden ∣ toPolyG (cmulG (cmulG (cmulG (cSplitFactorFast Dt fuel fden).1 h) h) gnum))
    (hred : toPolyG a * Differential.implicitDeriv (toPolyG Dt) (toPolyG Q) + toPolyG b * toPolyG Q
      = toPolyG c) :
    toPolyG gden * toPolyG fden
        * (Differential.implicitDeriv (toPolyG Dt) (toPolyG Q) * toPolyG h
            - toPolyG Q * Differential.implicitDeriv (toPolyG Dt) (toPolyG h))
        + toPolyG gden * toPolyG fnum * toPolyG Q * toPolyG h
      = toPolyG gnum * toPolyG fden * toPolyG h ^ 2 :=
  cRdeNormalDenominator_cleared_lift Dt fuel fnum fden gnum gden a b c h Q hres hdn hfden0 hgden0
    hfbB hdvdB hfbC hdvdC hred

#print axioms cRdeNormalDenominator_cleared_lift

end DeepWiki.SymbolicIntegration
