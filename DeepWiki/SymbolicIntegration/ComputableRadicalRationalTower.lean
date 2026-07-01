import DeepWiki.SymbolicIntegration.ComputableElementaryIntegrate

/-! # COMPUTING the RATIONAL half over a TRANSCENDENTAL tower (the grand unification, rational part)

`ComputableElementaryIntegrate` fused the rational part `v` and the log part `Σ cᵢ log uᵢ` of an
elementary-radical integrand over a *transcendental* tower like `α = ℚ(x)(eˣ)` — but with one honest gap:
the **log** half was fully COMPUTED (`radLogArgSolveG`, the ACTUAL tower derivation), while the **rational**
half `v = 2y` was **supplied**. The reason: the Case-3 degree-lowering `radReduceCase3Iterate`
(`ComputableRadicalRationalDriver`) ran with the **formal** derivation `cderivG` (`θ' = 1`), which is the
**wrong** derivation for `θ = eˣ` (`θ' = θ`). This file closes that last gap — it makes the rational half
COMPUTE over the tower with the ACTUAL derivation, exactly the fix the log half already received
(`radLogResidualG` routes `CDiffField.cderiv`).

**The same `C/y` degree-lowering; only the DERIVATION generalizes (and the cofactor *shape* follows).** The
Case-3 step (Trager Appendix A §2.3) lowers `deg_θ C` by cancelling its leading term with a cofactor
monomial `B`, accumulating `B·f` into the rational-part numerator `v` (over the common denominator `y`).
The cleared identity `(Bf/y)' − C/y = D/y` is `B'f + Bg − C = D` (`deg D < deg C`), where **`B' = der B`** is
the radicand-level derivative of the cofactor. The original `radReduceCase3Iterate` hard-wires `der =
cderivG` (`θ' = 1`); over the exp tower the genuine `der` is `cmonomialDeriv [θ]` (`θ' = θ`, via
`expDt1 = [0,1]`). **The cofactor shape changes with `der`**: for `θ' = 1`, `der` *lowers* degree, so
`g = ½ρ'` has `deg g = deg f − 1` and `B = b·θ^{deg C − deg f + 1}`; for `θ' = θ`, `der` *preserves* degree,
so `g = ½ρ'` has `deg g = deg f` and the cofactor drops to `B = b·θ^{deg C − deg f}`. Both unify as
`deg B = deg C − deg g` (the `B·g` term always reaches `deg C`), and the leading coefficient `b` is read off
generically — `b = lcf(C)/κ`, `κ = lcf(der(θ^{deg B})·f + θ^{deg B}·g)` the per-unit-`b` leading
contribution — so **no closed cofactor formula is hard-wired to `θ' = 1`**; the derivation `der` decides
both the degree and `κ`.

* **`radCase3CofactorTower`** — the generic leading-term cofactor: `B = b·θ^m`, `m = deg C − deg g`,
  `b = lcf(C)/κ` with `κ = lcf(der(θ^m)·f + θ^m·g)`. Reduces to `radCase3Cofactor`'s `b·θ^{deg C−deg f+1}`
  when `der = cderivG` (`deg g = deg f − 1`); gives `b·θ^{deg C−deg f}` when `der = cmonomialDeriv [θ]`
  (`deg g = deg f`). The `der` is the ACTUAL derivation, NOT formal `cderivG`.

* **`radReduceCase3IterateG`** — fuel-free `radReduceCase3Iterate` with the cofactor swapped to
  `radCase3CofactorTower der` (so the ACTUAL derivation drives both `B` and the residual `D = der B·f + Bg −
  C`). It recurses directly on the degree of `C`, accumulates `B·f` into `vNum`, and bottoms at
  `deg C < deg f`.

* **`radIntegrateCase3G`** — the `∫ C/y` driver over the tower base, using the fuel-free
  `radReduceCase3IterateG`.

**★★ THE MILESTONE** (`native_decide`): over `α = ℚ(x)(eˣ)` (the exp tower, `θ' = θ` via `expDt1`),
`∫√(eˣ+1) dx` integrand `y = ρ/y` (`C = ρ = θ+1`), `radIntegrateCase3G (cmonomialDeriv [θ]) ρ (½ρ') C`
**COMPUTES** the rational-part numerator `vNum = 2ρ = 2θ+2`, so the rational part `v = vNum/y = 2y = [0,2]`
— and the ACTUAL radical derivation `radDeriv 2 ρ [0,2] = [0, θ/(θ+1)] = eˣ/√(eˣ+1)` (the `eˣ/√(eˣ+1)`
piece). The rational half is now an OUTPUT, not a supplied constant.

**★★ THE FULLY-COMPUTED ROUND-TRIP** (`native_decide`): combine with the COMPUTED log half — for
`∫√(eˣ+1) dx` (integrand `y`), Case-3-G COMPUTES `v = 2y`, `radLogArgSolveG` COMPUTES `u = (y−1)/(y+1)`, and
`algDerivG ⟨2y, [(1, u)]⟩ = y` (the integrand) over the tower, through the ACTUAL exp derivation. BOTH halves
now COMPUTED — no supplied `v`. The unified elementary integral `∫√(eˣ+1) dx = 2√(eˣ+1) + log((y−1)/(y+1))`
is computed end-to-end over the transcendental tower.

**STRETCH** (`native_decide`): `radIntegrateCase3G cderivG` reduces to the ℚ-base `radIntegrateCase3` behavior
at `α = ℚ(x)` (the conservative `θ' = 1` specialization on `∫ x⁴/√(x³+1)`). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem CPolyG

namespace CPolyG

variable {α : Type*} [CField α]

/-! ### The generic leading-term Case-3 cofactor (ACTUAL derivation, any `der`)

The original `radCase3Cofactor` (`ComputableRadicalExtension`) bakes in the `θ' = 1` cofactor shape `B =
b·θ^{deg C − deg f + 1}` with `b = lcf(C)/((deg C − deg f + 1) + lcf(g))` — both the monomial degree and the
denominator assume the *formal* derivation lowers degree (so `g = ½ρ'` has `deg g = deg f − 1`). For a
general derivation `der` (the radicand-level `D` on `CPolyG α`) the cofactor degree and leading coefficient
must be re-read off `der` itself. `radCase3CofactorTower` does this generically. -/

/-- **The generic leading-term Case-3 cofactor** `radCase3CofactorTower der f g C = B = b·θ^m` — cancels the
leading term of `C` in the `C/y` degree-lowering for **any** radicand-level derivation `der` (with `B' = der
B`), NOT just the formal `θ' = 1`. The monomial degree is `m = deg C − deg g` (the `B·g` term reaches
`deg C` regardless of `der`), and the leading coefficient is read off `der` generically: `κ = lcf(der(θ^m)·f
+ θ^m·g)` is the per-unit-`b` leading contribution of the trial cofactor `θ^m`, so `b = lcf(C)/κ`. Reduces to
`radCase3Cofactor`'s `b·θ^{deg C−deg f+1}` when `der = cderivG` (`deg g = deg f − 1`, `der` lowers degree);
gives `b·θ^{deg C−deg f}` when `der = cmonomialDeriv [θ]` (`deg g = deg f`, `der` preserves degree). Returns
`[]` when `deg C < deg f` (nothing to lower). Generic over `[CField α]`. -/
def radCase3CofactorTower (der : CPolyG α → CPolyG α) (f g C : CPolyG α) : CPolyG α :=
  if cisZeroG C || cdegG C < cdegG f then []
  else
    let m := cdegG C - cdegG g                                      -- `deg B`, so `deg(B·g) = deg C`
    let trial := cshiftG m [CField.one]                            -- the unit cofactor `θ^m`
    let κ := cleadG (caddG (cmulG (der trial) f) (cmulG trial g))  -- per-unit-`b` leading contribution
    let b := CField.div (cleadG C) κ                               -- `b = lcf(C)/κ`
    cshiftG m [b]                                                   -- `b·θ^m`

/-! ### The iterated Case-3 reduction with the ACTUAL derivation (Trager Appendix A §2.3, generic `der`)

`radReduceCase3IterateG` is the fuel-free companion of `radReduceCase3Iterate`
(`ComputableRadicalRationalDriver`), with the cofactor swapped from the `θ' = 1`-baked `radCase3Cofactor` to
the generic `radCase3CofactorTower der`. The `der` is the ACTUAL radicand-level derivation —
`cmonomialDeriv [θ]` over the exp tower (`θ' = θ`), or `cderivG` over the ℚ-base (`θ' = 1`). Everything else
(the residual `radCase3Residual`, the `B·f` accumulation, the `deg C < deg f` bottom) is identical to
`radReduceCase3Iterate`; only the derivation and termination witness change. The recursion is well-founded
on `(cnormG C).length`, with a runtime degree-drop guard before the recursive call. -/

/-- **Fuel-free iterated Case-3 reduction with the ACTUAL derivation** `radReduceCase3IterateG der f g C
vNum = (Crem, vNumOut)` (Trager Appendix A §2.3, iterated). This is `radReduceCase3Iterate` with the
cofactor `B := radCase3CofactorTower der f g C` (the generic leading-term cofactor that reads its degree and
leading coefficient off the ACTUAL `der`), NOT the `θ' = 1`-baked `radCase3Cofactor`. While `deg C ≥ deg f`
it cancels the leading term of `C` with `B`, forms the residual `D := radCase3Residual f g B C (der B)` (the
ACTUAL `der B`), **accumulates** the contribution `B·f` into `vNum` (the rational-part numerator over the
common denominator `y`), and recurses on the negated residual `−D` under the structural degree-drop guard.
Bottoms at `deg C < deg f` returning `(C, vNum)`. `der` is the radicand-level derivation:
`cmonomialDeriv [θ]` over the exp tower (`θ' = θ`), `cderivG` over the ℚ-base (`θ' = 1`). Generic over
`[CField α]`; no runtime fuel. -/
def radReduceCase3IterateG (der : CPolyG α → CPolyG α) (f g : CPolyG α) :
    CPolyG α → CPolyG α → CPolyG α × CPolyG α
  | C, vNum =>
    if cisZeroG C || cdegG C < cdegG f then (C, vNum)
    else
      let B := radCase3CofactorTower der f g C
      let D := radCase3Residual f g B C (der B)
      if (cnormG (cnegG D) : List α).length < (cnormG C : List α).length then
        radReduceCase3IterateG der f g (cnegG D) (caddG vNum (cmulG B f))
      else (C, vNum)
termination_by C => (cnormG C : List α).length
decreasing_by assumption

/-- **The simple-radical rational-part driver (Case 3) with the ACTUAL derivation** `radIntegrateCase3G der
f g C = (Crem, vNum)` (Trager Appendix A §2.3) — the `∫ C/y` driver over a simple radical `y² = f` for a
polynomial numerator `C`, with the radicand-level derivation `der` the ACTUAL one (`cmonomialDeriv [θ]` over
the exp tower, `θ' = θ`). Runs the fuel-free `radReduceCase3IterateG`, returning the
irreducible leftover `Crem` (`deg Crem < deg f`) and the accumulated rational-part numerator `vNum` over the
common denominator `y`. Master identity: `∫ C/y = vNum/y + ∫ Crem/y`. Generic over `[CField α]`. -/
def radIntegrateCase3G (der : CPolyG α → CPolyG α) (f g C : CPolyG α) : CPolyG α × CPolyG α :=
  radReduceCase3IterateG der f g C []

end CPolyG

/-! ### ★★ THE MILESTONE: Case-3-G COMPUTES the rational part `v = 2y` for `∫√(eˣ+1) dx` (`native_decide`)

`β = ℚ(x) = QFunNZG ℚ`, `α = QFunNZG β = ℚ(x)(eˣ) = Lvl2`, `θ = eˣ`, `ρ = θ+1`, `y² = ρ`, with the
**exponential** derivation `θ' = θ` (the radicand-level derivation `cmonomialDeriv expDt1` over
`CPolyG (QFunNZG ℚ)`, `expDt1 = [0,1]` making `t₁' = t₁`). The integrand `√(eˣ+1) = y = ρ/y` is the `C/y`
form with `C = ρ = θ+1`.

`radIntegrateCase3G (cmonomialDeriv expDt1) ρ (½ρ') C` runs one Case-3-G step: the generic cofactor
`radCase3CofactorTower` computes `B = [2]` (a constant! — `deg B = deg C − deg g = 1 − 1 = 0`, since `g =
½ρ' = θ/2` has `deg g = 1 = deg f` under `θ' = θ`), accumulating `vNum = B·f = 2(θ+1) = 2ρ`. So the rational
part `v = vNum/y = 2ρ/y = 2y` — **COMPUTED**, not supplied. (The formal `θ' = 1` cofactor would force `B =
b·θ`, the wrong shape.) Validated by the **actual** radical derivation `radDeriv 2 ρ [0,2] = [0, θ/(θ+1)] =
eˣ/√(eˣ+1)`. -/

open RadElem CPolyG

/-- The exp-tower radicand `ρ = θ+1 = eˣ+1 ∈ ℚ(x)[θ]` (`y² = ρ`) as the `CPolyG (QFunNZG ℚ)` `[1,1]` (poly in
`θ = t₁` over `ℚ(x)`: `1 + t₁`). The polynomial-level radicand for the Case-3-G degree-lowering. -/
def expC3Rho : CPolyG (QFunNZG ℚ) := [CField.one, CField.one]

/-- The exp-tower Case-3 helper `g = ½ρ'` over `ℚ(x)[θ]` with the **ACTUAL** `θ' = θ` derivation: `ρ' =
(θ+1)' = θ` (the actual `cmonomialDeriv [θ]`, NOT the formal `ρ' = 1`), so `g = θ/2 = [0, 1/2]` — degree `1`,
matching `deg f = 1` (the hallmark of `θ' = θ`: `g` does NOT drop a degree, unlike the `θ' = 1` case). -/
def expC3G : CPolyG (QFunNZG ℚ) :=
  cscaleG (CField.div CField.one (cnatCastG 2)) (cmonomialDeriv expDt1 expC3Rho)

/-- The exp-tower Case-3 numerator `C = ρ = θ+1 ∈ ℚ(x)[θ]` (the integrand `√(eˣ+1) = ρ/y`, so `C = ρ`),
`[1,1]`. -/
def expC3C : CPolyG (QFunNZG ℚ) := [CField.one, CField.one]

/-- **The Case-3-G run over the exp tower** `radIntegrateCase3G (cmonomialDeriv expDt1) ρ (½ρ') C =
(Crem, vNum)` on `∫√(eˣ+1) dx` with the ACTUAL `θ' = θ` derivation — one degree-lowering step, returning the
irreducible residual `Crem` and the accumulated rational-part numerator `vNum` over the common denominator
`y`. The cofactor `B = [2]` (computed by `radCase3CofactorTower`) gives `vNum = 2(θ+1) = 2ρ`. -/
def expC3Run : CPolyG (QFunNZG ℚ) × CPolyG (QFunNZG ℚ) :=
  radIntegrateCase3G (cmonomialDeriv expDt1) expC3Rho expC3G expC3C

-- Sanity print: the COMPUTED rational-part numerator `vNum` (should be `2ρ = 2θ+2 = [2,2]`) and the
-- residual `Crem`, as ℚ(x)-coefficient lists.
#eval (expC3Run.2.map (fun (z : QFunNZG ℚ) => (z.1.1 : List ℚ)),
       expC3Run.1.map (fun (z : QFunNZG ℚ) => (z.1.1 : List ℚ)))

/-- **★ Case-3-G COMPUTES `vNum = 2ρ` (so `v = 2y`) over the exp tower** (`native_decide`): the generic
Case-3 reduction with the ACTUAL `θ' = θ` derivation produces the rational-part numerator `vNum = 2(θ+1) =
2ρ` over the common denominator `y` — checked by `cisZeroG (vNum − 2ρ)` over `ℚ(x)[θ]`. Since `v = vNum/y =
2ρ/y = 2y`, the rational half `2y` is now an OUTPUT of the engine over the transcendental tower, not a
supplied constant. (The formal `θ' = 1` cofactor would give the wrong `B = b·θ` shape.) -/
theorem expC3_vNum_eq_two_rho :
    cisZeroG (csubG expC3Run.2 (cscaleG (cnatCastG 2) expC3Rho)) = true := by native_decide

/-- The exp-tower radicand `ρ = θ+1 = eˣ+1 ∈ ℚ(x)(eˣ) = Lvl2` lifted to a level-2 scalar (numerator `ρ` over
`[1]`), the radicand for `radDeriv 2` at level 2 — the same carrier value as `expRadicand`
(`ComputableRadicalOverTower`). -/
def expC3RhoLvl2 : Lvl2 := lvl2OfNum expC3Rho

/-- The COMPUTED rational part `v = vNum/y = 2y` lifted to `RadElem Lvl2` — the pure-`y` element
`[0, vNum/ρ]` over `ℚ(x)(eˣ)` (an `R/y` form is `[0, R/ρ]` since `R/y = (R/ρ)·y`; here the common
denominator is just `y`). With `vNum = 2ρ`, this reduces to `[0, 2] = 2y`. The rational half is the engine's
OUTPUT (`expC3Run.2`), not a supplied `[0,2]`. -/
def expC3Vlift : RadElem Lvl2 :=
  [CField.zero, CField.div (lvl2OfNum expC3Run.2) (lvl2OfNum expC3Rho)]

/-- The expected `eˣ/√(eˣ+1)` piece `[0, θ/(θ+1)]` over `ℚ(x)(eˣ)` — the rational-part contribution
`radDeriv(2y)` should equal: `(2y)' = (ρ'/ρ)·y = (θ/(θ+1))·y`, so the only coefficient is the `y`-coefficient
`θ/(θ+1) = eˣ/(eˣ+1)`. The same value as `expIntegrand` (`ComputableRadicalOverTower`). -/
def expC3RatContribution : RadElem Lvl2 :=
  [CField.zero, CField.div expTheta expRadicand]

/-- **★★ Case-3-G's COMPUTED rational part `v = 2y` has `radDeriv(v) = eˣ/√(eˣ+1)`** (`native_decide`) — the
ACTUAL diagonal radical derivation `radDeriv 2 ρ` (with the **exponential** base derivation `θ' = θ` via
`expTowerDiff`) of the COMPUTED rational part `v = vNum/y` (where `vNum = expC3Run.2 = 2ρ`, the engine's
output) equals the `eˣ/√(eˣ+1)` piece `[0, θ/(θ+1)]`. Since `radDeriv(2y) = (ρ'/ρ)·y = (θ/(θ+1))·y =
eˣ/√(eˣ+1)`, the COMPUTED rational half is exactly the `eˣ/√(eˣ+1)` contribution of the integrand. Checked by
`radIsZero` of the difference over `ℚ(x)(eˣ)`. THE RATIONAL HALF IS COMPUTED (not supplied) OVER THE
TRANSCENDENTAL TOWER, validated through the real radical derivation with the actual exp derivation. -/
theorem expC3_radDeriv_vlift_eq :
    radIsZero (radSub (@radDeriv _ _ expTowerDiff 2 expC3RhoLvl2 expC3Vlift) expC3RatContribution)
      = true := by native_decide

/-! ### ★★ THE FULLY-COMPUTED ROUND-TRIP: BOTH halves of `∫√(eˣ+1) dx` computed over ℚ(x)(eˣ)

The headline: combine the now-COMPUTED rational half (Case-3-G, `v = 2y`) with the COMPUTED log half
(`radLogArgSolveG`, `u = (y−1)/(y+1)`). For `∫√(eˣ+1) dx` the integrand `√(eˣ+1) = y` splits as `v' + (log
u)' = eˣ/√(eˣ+1) + 1/√(eˣ+1) = (eˣ+1)/√(eˣ+1) = √(eˣ+1) = y`. Neither half is supplied: `v = 2y` is
`expC3Vlift` (Case-3-G's output, `vNum = 2ρ`), and `u` is computed by the log solver. Assemble `F' = ⟨v,
[(1, u)]⟩` and `native_decide` that `algDerivG F' = y` (the integrand) over the tower, through the ACTUAL exp
derivation. BOTH halves COMPUTED — the unified elementary integral `∫√(eˣ+1) dx = 2√(eˣ+1) + log((y−1)/(y+1))`
fully computed end-to-end over the transcendental tower. -/

/-- The combined round-trip integrand `√(eˣ+1) = y = [0,1]` over `ℚ(x)(eˣ)` — the integrand we integrate
back, the radical generator. (Same value as `radGen`; `∫ y dx = 2y + log((y−1)/(y+1))` since `(2y +
log((y−1)/(y+1)))' = eˣ/√(eˣ+1) + 1/√(eˣ+1) = √(eˣ+1) = y`.) -/
def rtFullIntegrand : RadElem Lvl2 := (radGen : RadElem Lvl2)

/-- The log residual `1/√(eˣ+1) = 1/y` lifted to `[0, 1/ρ]` over `ℚ(x)(eˣ)` (`ρ = eˣ+1`) — the log-derivative
half the solver absorbs (the same value as `elemLogResidual` / `expArgIntegrand`). The integrand `y` minus
the COMPUTED rational derivative `radDeriv(2y) = eˣ/√(eˣ+1)` leaves `1/√(eˣ+1)`. -/
def rtFullLogResidual : RadElem Lvl2 := radInvYLift expC3RhoLvl2 CField.one

/-- **The integrand splits exactly into the COMPUTED rational + log halves** (`native_decide`): the log
residual `1/√(eˣ+1) = [0, 1/ρ]` equals the integrand `y` minus the **COMPUTED** rational-part derivative
`radDeriv(v)` (`v = expC3Vlift`, Case-3-G's output, both the ACTUAL exp derivation). Confirms the
rational/log split of `√(eˣ+1)` is exact with the COMPUTED rational half: `√(eˣ+1) − eˣ/√(eˣ+1) =
1/√(eˣ+1)`. Checked by `radIsZero` over `ℚ(x)(eˣ)`. -/
theorem rtFull_split_exact :
    radIsZero (radSub rtFullLogResidual
      (radSub rtFullIntegrand (@radDeriv _ _ expTowerDiff 2 expC3RhoLvl2 expC3Vlift))) = true := by
  native_decide

/-- The fixed log-solve denominator `D = θ = eˣ ∈ ℚ(x)(eˣ)` as a `CPolyG (QFunNZG ℚ)` (`β = ℚ(x)`): the
polynomial `θ = t₁`, `[0, 1]`. The same value as `elemDenTheta` / `expDenTheta`; the denominator of `u =
(y−1)/(y+1) = ((θ+2)−2y)/θ`. -/
def rtFullDenTheta : CPolyG (QFunNZG ℚ) := [CField.zero, CField.one]

/-- **★★ The FULLY-COMPUTED recovered result `F'` — BOTH halves computed**. `cIntegrateElementaryG ρ
(expC3Vlift) residual 1 θ 1` over `ℚ(x)(eˣ)`: the rational part `v` is the **COMPUTED** Case-3-G output
`expC3Vlift` (`vNum = 2ρ`, so `v = 2y`) — NOT a supplied `[0,2]` — and the log argument is **COMPUTED** from
the residual `[0, 1/ρ]` by `radLogArgSolveG` (the ACTUAL exp derivation `expTowerDiff` via `@`, `D = θ`,
degree `1`), `u = N/θ` with `N = (θ+2)−2y`. Assembles `F' = ⟨2y, [(1, u)]⟩` with BOTH halves the engine's
output. -/
def rtFullRecovered : AlgIntegralResultG Lvl2 :=
  @cIntegrateElementaryG _ _ _ expTowerDiff expC3RhoLvl2 expC3Vlift rtFullLogResidual
    CField.one rtFullDenTheta 1

-- Sanity print: the recovered rational part `v` (should be `2y = [0,2]`, i.e. coefficient `2` on `y`) and
-- the recovered log argument `u` (a constant multiple of `(y−1)/(y+1) = ((θ+2)−2y)/θ`).
#eval (rtFullRecovered.ratPart.map (fun (z : Lvl2) => (z.1.1.map (fun (w : QFunNZG ℚ) => (w.1.1 : List ℚ)))),
       rtFullRecovered.logTerms.map (fun (_, u) =>
         u.map (fun (z : Lvl2) => (z.1.1.map (fun (w : QFunNZG ℚ) => (w.1.1 : List ℚ))))))

/-- **★★ THE FULLY-COMPUTED ROUND-TRIP: `algDerivG F' = √(eˣ+1)`, BOTH halves COMPUTED** (`native_decide`) —
the full Bronstein-1990 elementary integral `∫√(eˣ+1) dx = 2√(eˣ+1) + log((y−1)/(y+1))` over `ℚ(x)(eˣ)` with
**NEITHER** half supplied. The rational part `v = 2y` is COMPUTED by `radIntegrateCase3G` (the ACTUAL `θ' = θ`
derivation, `vNum = 2ρ`); the log argument `u = (y−1)/(y+1)` is COMPUTED by `radLogArgSolveG` (the ACTUAL exp
derivation, a kernel vector over `β = ℚ(x)`); and `algDerivG F' = radDeriv(2y) + radLogDeriv(u) =
eˣ/√(eˣ+1) + 1/√(eˣ+1) = √(eˣ+1) = y`, the integrand. Checked by `radIsZero` of `algDerivG F' − y` over
`ℚ(x)(eˣ)`. THE UNIFIED ELEMENTARY INTEGRAL HAS BOTH HALVES COMPUTED OVER A TRANSCENDENTAL TOWER — the
rational half is no longer supplied; Case-3-G with the actual derivation reconstructs `2y` from the
integrand `y`, the log solver reconstructs `log u`, and the round-trip validates both through the real
radical derivation. -/
theorem rtFull_both_halves_computed :
    radIsZero (radSub (@algDerivG _ _ expTowerDiff expC3RhoLvl2 rtFullRecovered) rtFullIntegrand)
      = true := by native_decide

/-- **The fully-computed result has a COMPUTED nonzero rational part AND one COMPUTED log term**
(`native_decide`): `F'` carries a nonzero `ratPart` (`2y`, the Case-3-G output) and exactly one log term (the
solver output) — the structural signature of a genuine combined elementary integral `∫ = v + c·log u` with
**both** parts the engine's output, over the tower. Checked on `(radIsZero F'.ratPart, F'.logTerms.length)` =
`(false, 1)`. -/
theorem rtFull_shape :
    (radIsZero rtFullRecovered.ratPart, rtFullRecovered.logTerms.length) = (false, 1) := by
  native_decide

/-- **★ The COMPUTED rational part is `2y`** (`native_decide`): the recovered `F'.ratPart = v = [a₀, a₁]`
over `ℚ(x)(eˣ)` has `a₀ = 0` and `a₁ = 2` — i.e. `v = 2y` exactly (the Case-3-G output `vNum = 2ρ` divided by
`ρ` gives the `y`-coefficient `2`). Confirms the COMPUTED rational half is the expected `2√(eˣ+1)`. Checked by
`radIsZero` of `v − [0,2]`. -/
theorem rtFull_ratPart_eq_two_y :
    radIsZero (radSub rtFullRecovered.ratPart
      [CField.zero, CField.add CField.one CField.one]) = true := by native_decide

/-! ### STRETCH: `radIntegrateCase3G cderivG` reduces to the ℚ-base behavior at `α = ℚ(x)` (`native_decide`)

Conservativity: at the ℚ-base (`α = QFunNZG ℚ ≅ ℚ(x)`, `θ = x`, `θ' = 1`), `radIntegrateCase3G cderivG`
reproduces the original `radIntegrateCase3 cderivG` on `∫ x⁴/√(x³+1)`. The generic leading-term cofactor
`radCase3CofactorTower cderivG` specializes back to `radCase3Cofactor`'s `b·θ^{deg C−deg f+1}` (since with
`der = cderivG`, `g = ½ρ'` has `deg g = deg f − 1`, so `deg B = deg C − deg g = deg C − deg f + 1`). We check
the two drivers agree exactly on `∫ x⁴/√(x³+1)` (the same `(Crem, vNum)` output as `c3itRun`,
`ComputableRadicalRationalDriver`). -/

/-- Stretch ℚ-base radicand `ρ = x³ + 1 ∈ ℚ(x)` as the `CPolyG ℚ` `[1,0,0,1]` — the same value as `c3itRho`
(`ComputableRadicalRationalDriver`). -/
def stretchRho : CPolyG ℚ := [1, 0, 0, 1]

/-- Stretch ℚ-base helper `g = ½ρ' = (3/2)x²` (`θ' = 1`, `(f/y)' = g/y`) — the same value as `c3itG`. -/
def stretchG : CPolyG ℚ := cscaleG (1/2 : ℚ) (cderivG stretchRho)

/-- Stretch ℚ-base numerator `C = x⁴ ∈ ℚ(x)` (`[0,0,0,0,1]`) — the same value as `c3itC`. -/
def stretchC : CPolyG ℚ := [0, 0, 0, 0, 1]

/-- **★ `radIntegrateCase3G cderivG` agrees with `radIntegrateCase3 cderivG` at the ℚ-base** (`native_decide`)
— on `∫ x⁴/√(x³+1)` (`θ' = 1`), the generic Case-3-G driver and the original `radIntegrateCase3` produce the
**identical** `(Crem, vNum)`. So the ACTUAL-derivation generalization is conservative: with `der = cderivG`
the leading-term cofactor `radCase3CofactorTower` specializes back to `radCase3Cofactor`, and Case-3-G
reduces to the ℚ-base Case-3 exactly. Checked by structural equality of the two driver outputs. -/
theorem stretch_case3G_eq_case3_base :
    radIntegrateCase3G cderivG stretchRho stretchG stretchC
      = radIntegrateCase3 cderivG stretchRho stretchG stretchC := by native_decide

/-! ### `#print axioms` — is the RATIONAL half now COMPUTED (not supplied) over the tower?

Each compute-then-validate theorem carries the standard `[propext, Classical.choice, Quot.sound]` plus the
`native_decide` compiler axiom — no `sorry`, no extra axiom. **The rational half is now COMPUTED over the
transcendental tower.** `radIntegrateCase3G` runs the `C/y` degree-lowering with the **ACTUAL** radicand-level
derivation (`cmonomialDeriv [θ]`, `θ' = θ`) via the generic leading-term cofactor `radCase3CofactorTower`
(whose degree and leading coefficient are read off the actual `der`, NOT hard-wired to `θ' = 1`): over
`α = ℚ(x)(eˣ)` it COMPUTES the rational-part numerator `vNum = 2ρ` for `∫√(eˣ+1) dx`, so the rational part
`v = 2y` is an OUTPUT (`radDeriv(2y) = eˣ/√(eˣ+1)`, the exact rational contribution). Combined with the
COMPUTED log half (`radLogArgSolveG`), the FULLY-COMPUTED round-trip `algDerivG ⟨2y, [(1, (y−1)/(y+1))]⟩ =
√(eˣ+1)` holds with **NEITHER** half supplied — the unified elementary integral `∫√(eˣ+1) dx = 2√(eˣ+1) +
log((y−1)/(y+1))` is now computed end-to-end over the tower. At the ℚ-base (`θ' = 1`) `radIntegrateCase3G
cderivG` reduces to the original `radIntegrateCase3` exactly (conservative). -/

-- ★ Case-3-G COMPUTES the rational-part numerator `vNum = 2ρ` (so `v = 2y`) over the exp tower:
#print axioms expC3_vNum_eq_two_rho

-- ★★ The COMPUTED rational part `v = 2y` has `radDeriv(v) = eˣ/√(eˣ+1)` (the actual exp derivation):
#print axioms expC3_radDeriv_vlift_eq

-- ★★ THE HEADLINE: the FULLY-COMPUTED round-trip — BOTH halves of `∫√(eˣ+1) dx` computed over ℚ(x)(eˣ):
#print axioms rtFull_both_halves_computed

-- The COMPUTED rational part is exactly `2y` (and the result has both parts present):
#print axioms rtFull_ratPart_eq_two_y
#print axioms rtFull_shape

-- STRETCH: `radIntegrateCase3G cderivG` reduces to the ℚ-base `radIntegrateCase3` (conservative):
#print axioms stretch_case3G_eq_case3_base

end DeepWiki.SymbolicIntegration
