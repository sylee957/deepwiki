import DeepWiki.SymbolicIntegration.Engine.ElementaryIntegrate
import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalOverTower

/-! # Computing the rational half over a transcendental tower

The Case-3 `C/y` degree-lowering generalized to run with the actual radicand-level derivation `der`
(e.g. `CPolyEngine.monomialDeriv [θ]`, `θ' = θ`, over `α = ℚ(x)(eˣ)`), so the rational part `v` is an output
rather than supplied. Combined with the computed log half, gives the fully-computed round-trip
`algDeriv ⟨2y, [(1, (y−1)/(y+1))]⟩ = √(eˣ+1)` over the tower. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

universe u

open RadElem DensePoly

namespace DensePoly

variable {α : Type*} [CField α]

/-! ### The generic leading-term Case-3 cofactor (any derivation `der`)

The cofactor degree and leading coefficient are re-read off the radicand-level derivation `der`,
rather than baked to the formal `θ' = 1`. -/

/-- The generic leading-term Case-3 cofactor `radCase3CofactorTower der f g C = B = b·θ^m`, cancelling the
leading term of `C` for any derivation `der` (with `B' = der B`). Degree `m = deg C − deg g`, leading
coefficient `b = lcf(C)/κ` with `κ = lcf(der(θ^m)·f + θ^m·g)`. Returns `[]` when `deg C < deg f`. Generic
over `[CField α]`. -/
def radCase3CofactorTower {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] (der : P α → P α) (f g C : P α) : P α :=
  if CPolyEngine.cisZero C || CPolyEngine.cdeg C < CPolyEngine.cdeg f then
    CPolyEngine.ofCoeffList []
  else
    let m := CPolyEngine.cdeg C - CPolyEngine.cdeg g               -- `deg B`, so `deg(B·g) = deg C`
    let trial := CPolyEngine.monomial CCommRing.one m               -- the unit cofactor `θ^m`
    let κ := CPolyEngine.clead (CPolyEngine.add
      (CPolyEngine.mul (der trial) f) (CPolyEngine.mul trial g))    -- per-unit-`b` contribution
    let b := CField.div (CPolyEngine.clead C) κ                     -- `b = lcf(C)/κ`
    CPolyEngine.monomial b m                                       -- `b·θ^m`

example :
    let ofList : List ℚ → CPoly.SparsePoly ℚ := CPolyEngine.ofCoeffList
    let f := ofList [0, 1]
    let g := ofList [1 / 2]
    let C := ofList [0, 1, 1]
    CPoly.coeff (radCase3CofactorTower CPolyEngine.deriv f g C) 2 = 2 / 5 := by
  native_decide

/-! ### The iterated Case-3 reduction with the actual derivation

`radReduceCase3IterateG` is `radReduceCase3Iterate` with the cofactor swapped to the generic
`radCase3CofactorTower der`, well-founded on `(cnorm C).length` under a degree-drop guard. -/

/-- Fuel-free iterated Case-3 reduction `radReduceCase3IterateG der f g C vNum = (Crem, vNumOut)`, using
the generic cofactor `B := radCase3CofactorTower der f g C`: while `deg C ≥ deg f`, cancel the leading term
with `B`, form the residual `D := CPoly.radCase3Residual f g B C (der B)`, accumulate `B·f` into `vNum`, recurse
on `−D`; bottom at `deg C < deg f`. `der` the radicand-level derivation. Generic over `[CField α]`. -/
def radReduceCase3IterateG (der : DensePoly α → DensePoly α) (f g : DensePoly α) :
    DensePoly α → DensePoly α → DensePoly α × DensePoly α
  | C, vNum =>
    if cisZero C || cdeg C < cdeg f then (C, vNum)
    else
      let B := radCase3CofactorTower der f g C
      let D := CPoly.radCase3Residual f g B C (der B)
      if (cnorm (cneg D) : List α).length < (cnorm C : List α).length then
        radReduceCase3IterateG der f g (cneg D) (cadd vNum (cmul B f))
      else (C, vNum)
termination_by C => (cnorm C : List α).length
decreasing_by assumption

/-- Case-3 rational-part driver with the actual derivation `radIntegrateCase3G der f g C = (Crem, vNum)`
for `∫ C/y` over `y² = f`: runs `radReduceCase3IterateG`, returning the irreducible leftover and the
numerator over `y`. Master identity `∫ C/y = vNum/y + ∫ Crem/y`. Generic over `[CField α]`. -/
def radIntegrateCase3G (der : DensePoly α → DensePoly α) (f g C : DensePoly α) : DensePoly α × DensePoly α :=
  radReduceCase3IterateG der f g C []

end DensePoly

/-! ### Case-3-G computes the rational part `v = 2y` for `∫√(eˣ+1) dx`

Over `α = ℚ(x)(eˣ)`, `θ = eˣ`, `ρ = θ+1`, with the derivation `θ' = θ`: the integrand `√(eˣ+1) = ρ/y`
gives `C = ρ`, and `radIntegrateCase3G` computes `vNum = 2ρ`, so `v = 2y`. -/

open RadElem DensePoly

/-- The exp-tower radicand `ρ = θ+1 = eˣ+1 ∈ ℚ(x)[θ]` (`y² = ρ`) as `DensePoly (DenseFrac ℚ)` `[1,1]`. -/
def expC3Rho : DensePoly (DenseFrac ℚ) := [CCommRing.one, CCommRing.one]

/-- The exp-tower Case-3 helper `g = ½ρ'` over `ℚ(x)[θ]` with the `θ' = θ` derivation: `ρ' = θ`, so
`g = θ/2 = [0, 1/2]` (degree `1`, matching `deg f`). -/
def expC3 : DensePoly (DenseFrac ℚ) :=
  cscale (CField.div CCommRing.one (CField.natCast 2)) (CPolyEngine.monomialDeriv expDt1 expC3Rho)

/-- The exp-tower Case-3 numerator `C = ρ = θ+1 ∈ ℚ(x)[θ]` (integrand `√(eˣ+1) = ρ/y`), `[1,1]`. -/
def expC3C : DensePoly (DenseFrac ℚ) := [CCommRing.one, CCommRing.one]

/-- The Case-3-G run `radIntegrateCase3G (CPolyEngine.monomialDeriv expDt1) ρ (½ρ') C = (Crem, vNum)` on `∫√(eˣ+1) dx`
with the `θ' = θ` derivation: the cofactor `B = [2]` gives `vNum = 2ρ`. -/
def expC3Run : DensePoly (DenseFrac ℚ) × DensePoly (DenseFrac ℚ) :=
  radIntegrateCase3G (CPolyEngine.monomialDeriv expDt1) expC3Rho expC3 expC3C

-- Sanity print: the COMPUTED rational-part numerator `vNum` (should be `2ρ = 2θ+2 = [2,2]`) and the
-- residual `Crem`, as ℚ(x)-coefficient lists.
#eval (expC3Run.2.map (fun (z : DenseFrac ℚ) => (CFrac.num z : List ℚ)),
       expC3Run.1.map (fun (z : DenseFrac ℚ) => (CFrac.num z : List ℚ)))

/-- Case-3-G computes `vNum = 2ρ` (so `v = 2y`) over the exp tower: the reduction with `θ' = θ` produces
`vNum = 2(θ+1) = 2ρ`, checked by `cisZero (vNum − 2ρ)`. -/
theorem expC3_vNum_eq_two_rho :
    cisZero (csub expC3Run.2 (cscale (CField.natCast 2) expC3Rho)) = true := by native_decide

/-- The exp-tower radicand `ρ = θ+1 = eˣ+1 ∈ ℚ(x)(eˣ) = Lvl2` lifted to a level-2 scalar, the radicand for
`radDeriv 2` (the same value as `expRadicand`). -/
def expC3RhoLvl2 : Lvl2 := CFrac.ofPoly expC3Rho

/-- The computed rational part `v = vNum/y = 2y` lifted to `RadElem Lvl2` as `[0, vNum/ρ]`; with
`vNum = 2ρ` this is `[0, 2] = 2y`, the engine's output `expC3Run.2`. -/
def expC3Vlift : RadElem Lvl2 :=
  [CCommRing.zero, CField.div (CFrac.ofPoly expC3Run.2) (CFrac.ofPoly expC3Rho)]

/-- The expected `eˣ/√(eˣ+1)` piece `[0, θ/(θ+1)]` over `ℚ(x)(eˣ)`, which `radDeriv(2y)` should equal
(the same value as `expIntegrand`). -/
def expC3RatContribution : RadElem Lvl2 :=
  [CCommRing.zero, CField.div expTheta expRadicand]

/-- Case-3-G's computed rational part `v = 2y` has `radDeriv(v) = eˣ/√(eˣ+1)`: `radDeriv 2 ρ` (with the
exponential derivation `expTowerDiff`) of `v = vNum/y` (`vNum = 2ρ`) equals `[0, θ/(θ+1)]`. -/
theorem expC3_radDeriv_vlift_eq :
    DensePoly.cisZero (DensePoly.csub (@radDeriv _ _ expTowerDiff 2 expC3RhoLvl2 expC3Vlift) expC3RatContribution)
      = true := by native_decide

/-! ### The fully-computed round-trip: both halves of `∫√(eˣ+1) dx` over ℚ(x)(eˣ)

Combining the computed rational half (`v = 2y`) with the computed log half (`u = (y−1)/(y+1)`):
`algDeriv ⟨v, [(1, u)]⟩ = y`, the integrand, over the tower, with neither half supplied. -/

/-- The round-trip integrand `√(eˣ+1) = y = [0,1]` over `ℚ(x)(eˣ)` (the same value as `radGen`). -/
def rtFullIntegrand : RadElem Lvl2 := (radGen : RadElem Lvl2)

/-- The log residual `1/√(eˣ+1) = 1/y` lifted to `[0, 1/ρ]` over `ℚ(x)(eˣ)` (the log-derivative half the
solver absorbs; `y` minus `radDeriv(2y) = eˣ/√(eˣ+1)` leaves `1/√(eˣ+1)`). -/
def rtFullLogResidual : RadElem Lvl2 := radInvYLift expC3RhoLvl2 CCommRing.one

/-- The integrand splits exactly into the computed rational + log halves: the log residual `[0, 1/ρ]` equals
`y` minus the computed rational-part derivative `radDeriv(v)` (`v = expC3Vlift`). -/
theorem rtFull_split_exact :
    DensePoly.cisZero (DensePoly.csub rtFullLogResidual
      (DensePoly.csub rtFullIntegrand (@radDeriv _ _ expTowerDiff 2 expC3RhoLvl2 expC3Vlift))) = true := by
  native_decide

/-- The fixed log-solve denominator `D = θ = eˣ ∈ ℚ(x)(eˣ)` as `DensePoly (DenseFrac ℚ)` `[0, 1]`; the
denominator of `u = (y−1)/(y+1) = ((θ+2)−2y)/θ`. -/
def rtFullDenTheta : DensePoly (DenseFrac ℚ) := [CCommRing.zero, CCommRing.one]

/-- The fully-computed recovered result `F'`: `cIntegrateElementary` over `ℚ(x)(eˣ)` with the computed
rational part `expC3Vlift` (`v = 2y`) and the log argument computed from the residual by `radLogArgSolve`,
assembling `F' = ⟨2y, [(1, u)]⟩`. -/
def rtFullRecovered : AlgIntegralResult Lvl2 :=
  letI : CDiffField Lvl2 := expTowerDiff
  cIntegrateElementary expC3RhoLvl2 expC3Vlift rtFullLogResidual CCommRing.one rtFullDenTheta 1

-- Sanity print: the recovered rational part `v` (should be `2y = [0,2]`, i.e. coefficient `2` on `y`) and
-- the recovered log argument `u` (a constant multiple of `(y−1)/(y+1) = ((θ+2)−2y)/θ`).
#eval (rtFullRecovered.ratPart.map (fun (z : Lvl2) =>
         (CFrac.num z).map (fun (w : DenseFrac ℚ) => (CFrac.num w : List ℚ))),
       rtFullRecovered.logTerms.map (fun (_, u) =>
         u.map (fun (z : Lvl2) =>
           (CFrac.num z).map (fun (w : DenseFrac ℚ) => (CFrac.num w : List ℚ)))))

/-- The fully-computed round-trip `algDeriv F' = √(eˣ+1)` with both halves computed: the elementary integral
`∫√(eˣ+1) dx = 2√(eˣ+1) + log((y−1)/(y+1))` over `ℚ(x)(eˣ)`, `v = 2y` from `radIntegrateCase3G` and
`u = (y−1)/(y+1)` from `radLogArgSolve`, with `algDeriv F' = y`. Checked by `DensePoly.cisZero` of
`algDeriv F' − y`. -/
theorem rtFull_both_halves_computed :
    DensePoly.cisZero (DensePoly.csub (@algDeriv _ _ expTowerDiff expC3RhoLvl2 rtFullRecovered) rtFullIntegrand)
      = true := by native_decide

/-- The fully-computed result has a nonzero rational part and one log term: `F'` carries a nonzero `ratPart`
(`2y`) and exactly one log term, checked on `(DensePoly.cisZero F'.ratPart, F'.logTerms.length) = (false, 1)`. -/
theorem rtFull_shape :
    (DensePoly.cisZero rtFullRecovered.ratPart, rtFullRecovered.logTerms.length) = (false, 1) := by
  native_decide

/-- The computed rational part is `2y`: the recovered `F'.ratPart = v` equals `[0, 2]` over `ℚ(x)(eˣ)`,
checked by `DensePoly.cisZero` of `v − [0,2]`. -/
theorem rtFull_ratPart_eq_two_y :
    DensePoly.cisZero (DensePoly.csub rtFullRecovered.ratPart
      [CCommRing.zero, CCommRing.add CCommRing.one CCommRing.one]) = true := by native_decide

/-! ### `radIntegrateCase3G cderiv` reduces to the ℚ-base behavior at `α = ℚ(x)`

Conservativity: at the ℚ-base (`θ = x`, `θ' = 1`), `radIntegrateCase3G cderiv` reproduces
`radIntegrateCase3Wf cderiv` on `∫ x⁴/√(x³+1)`. -/

/-- ℚ-base radicand `ρ = x³ + 1 ∈ ℚ(x)` as `DensePoly ℚ` `[1,0,0,1]` (the same value as `c3itRho`). -/
def stretchRho : DensePoly ℚ := [1, 0, 0, 1]

/-- ℚ-base helper `g = ½ρ' = (3/2)x²` (`θ' = 1`) (the same value as `c3it`). -/
def stretch : DensePoly ℚ := cscale (1/2 : ℚ) (cderiv stretchRho)

/-- ℚ-base numerator `C = x⁴ ∈ ℚ(x)` (`[0,0,0,0,1]`) (the same value as `c3itC`). -/
def stretchC : DensePoly ℚ := [0, 0, 0, 0, 1]

/-- `radIntegrateCase3G cderiv` agrees with `radIntegrateCase3Wf cderiv` at the ℚ-base: on `∫ x⁴/√(x³+1)`
the two drivers produce identical `(Crem, vNum)`, checked by structural equality. -/
theorem stretch_case3G_eq_case3_base :
    radIntegrateCase3G cderiv stretchRho stretch stretchC
      = radIntegrateCase3Wf cderiv stretchRho stretch stretchC := by native_decide

/-! ### `#print axioms` — the rational half computed over the tower -/

-- ★ Case-3-G COMPUTES the rational-part numerator `vNum = 2ρ` (so `v = 2y`) over the exp tower:
#print axioms expC3_vNum_eq_two_rho

-- ★★ The COMPUTED rational part `v = 2y` has `radDeriv(v) = eˣ/√(eˣ+1)` (the actual exp derivation):
#print axioms expC3_radDeriv_vlift_eq

-- ★★ THE HEADLINE: the FULLY-COMPUTED round-trip — BOTH halves of `∫√(eˣ+1) dx` computed over ℚ(x)(eˣ):
#print axioms rtFull_both_halves_computed

-- The COMPUTED rational part is exactly `2y` (and the result has both parts present):
#print axioms rtFull_ratPart_eq_two_y
#print axioms rtFull_shape

-- STRETCH: `radIntegrateCase3G cderiv` reduces to the ℚ-base `radIntegrateCase3Wf` (conservative):
#print axioms stretch_case3G_eq_case3_base

end DeepWiki.SymbolicIntegration
