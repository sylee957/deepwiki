import DeepWiki.SymbolicIntegration.Engine.Algebraic.PrincipalGenerator

/-! # The non-principal `(1/m)·log` branch: torsion → integrator log term

For a residue divisor `D` with no single principal generator: if `D` is torsion of order `m`
(`m·D = O`), then `m·D` is principal and the log part is `(1/m)·log g` with `g` the generator of
`m·D`. `torsionLogTerm` runs the torsion decision then the generator construction to produce that
term; non-torsion `D` gives `none` (not elementary). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open DensePoly RadElem

/-! ## `torsionLogTerm` — the non-principal branch as a usable function -/

/-- The non-principal `(1/m)·log` branch `torsionLogTerm p ρ ρq g D`: via `isTorsionDivisor p ρq g D`,
returns `some (1/m, principalGenerator ρ ρq g m D)` when `D` is torsion of order `m` (log term
`(1/m)·log g` with `div(g) = m·D`), else `none` (infinite order, not elementary). `ρ`/`ρq` are the
radicand as `ℚ(x)`/`ℚ[x]`, `g` the genus. -/
def torsionLogTerm (p : ℕ) [Fact p.Prime]
    (ρ : DenseFrac ℚ) (ρq : DensePoly ℚ) (g : ℕ) (D : MumfordDivisor ℚ) :
    Option (DenseFrac ℚ × RadElem (DenseFrac ℚ)) :=
  match isTorsionDivisor p ρq g D with
  | none => none
  | some m => some
      (CField.div (CCommRing.one : DenseFrac ℚ) (CFrac.ofScalar (m : ℚ)),
        principalGenerator ρ ρq g m D)

/-! ## Round-trip: `(0, 1)` → `(1/3)·log(y − 1)` from the divisor on `y² = x³ + 1` -/

open RadElem

/-- The radicand `ρ = x³ + 1` as a `ℚ(x)` element (`DenseFrac ℚ`), for the radical-extension generator. -/
def tltRhoX3p1 : DenseFrac ℚ := CFrac.ofPoly [1, 0, 0, 1]

/-- The torsion log term `torsionLogTerm 5 ρ … (0, 1)` on `y² = x³ + 1` — expected `(1/3, y − 1)`. -/
def tltTerm01 : Option (DenseFrac ℚ × RadElem (DenseFrac ℚ)) :=
  torsionLogTerm 5 tltRhoX3p1 hypRhoX3p1 1 hypPt01

/-- The target generator `g = y − 1 = [−1, 1]` over `ℚ(x)` (the flex tangent line). -/
def tltYm1 : RadElem (DenseFrac ℚ) := [CCommRing.neg CCommRing.one, CCommRing.one]

/-- The recovered-term check `tltTermCheck t`: `Bool` that a term `t = (c, g)` equals `(1/3, y − 1)`. -/
def tltTermCheck (t : DenseFrac ℚ × RadElem (DenseFrac ℚ)) : Bool :=
  CFrac.eq t.1 (CField.div CCommRing.one (CFrac.ofScalar (3 : ℚ)))
    && DensePoly.cisZero (DensePoly.csub t.2 tltYm1)

/-- `torsionLogTerm` on `(0, 1)` returns a term whose coefficient is field-equal to `1/3`. -/
theorem tltTerm01_coeff :
    (tltTerm01.map fun t =>
      CFrac.eq t.1 (CField.div CCommRing.one (CFrac.ofScalar (3 : ℚ)))) = some true := by
  native_decide

/-- `torsionLogTerm` on `(0, 1)` returns the log term `(1/3, y − 1)` (`tltTermCheck` holds). -/
theorem tltTerm01_eq :
    (tltTerm01.map tltTermCheck) = some true := by native_decide

/-! ### The `(1/3)·log(y − 1)` differential check -/

/-- The `(1/3)·log(y − 1)` differential `ι = (1/3)·g'/g` over `ℚ(x)`, `y² = x³ + 1`. -/
def tltDiff01 : RadElem (DenseFrac ℚ) :=
  DensePoly.cscale (CField.div CCommRing.one (CFrac.ofScalar (3 : ℚ)))
    (radLogDeriv tltRhoX3p1 tltYm1)

/-- The `(1/3)·log(y − 1)` differential passes the cleared log-derivative certificate
`radIsLogIntegral 2 tltRhoX3p1 tltYm1 (DensePoly.cscale (CFrac.ofPoly [3]) tltDiff01)`. -/
theorem tltTerm01_logderiv :
    radIsLogIntegral 2 tltRhoX3p1 tltYm1 (DensePoly.cscale (CFrac.ofPoly [3]) tltDiff01) = true := by native_decide

/-! ## Assembling the torsion term into an `AlgIntegralResult (DenseFrac ℚ)` -/

/-- Assemble `∫ = v + (1/m)·log g` as an `AlgIntegralResult (DenseFrac ℚ)` `torsionAlgResult p ρ ρq g v D`: rational
part `v` plus the `torsionLogTerm` in `logTerms` (empty if `D` is non-torsion). -/
def torsionAlgResult (p : ℕ) [Fact p.Prime]
    (ρ : DenseFrac ℚ) (ρq : DensePoly ℚ) (g : ℕ) (v : RadElem (DenseFrac ℚ)) (D : MumfordDivisor ℚ) :
    AlgIntegralResult (DenseFrac ℚ) :=
  match torsionLogTerm p ρ ρq g D with
  | none => ⟨v, []⟩
  | some term => ⟨v, [term]⟩

/-- The assembled torsion result `∫ = 0 + (1/3)·log(y − 1)` (no rational part) for `(0, 1)` on
`y² = x³ + 1` — `torsionAlgResult` with `v = 0` (`radZero`). Expected `logTerms = [(1/3, y − 1)]`. -/
def tltResult01 : AlgIntegralResult (DenseFrac ℚ) :=
  torsionAlgResult 5 tltRhoX3p1 hypRhoX3p1 1 radZero hypPt01

/-- The assembled `tltResult01` has empty rational part and one log term with coefficient field-equal
to `1/3`. -/
theorem tltResult01_shape :
    (DensePoly.cisZero tltResult01.ratPart,
     tltResult01.logTerms.length,
     (tltResult01.logTerms.head?.map fun t =>
       CFrac.eq t.1 (CField.div CCommRing.one (CFrac.ofScalar (3 : ℚ))))) = (true, 1, some true) := by
  native_decide

/-- `algDeriv tltRhoX3p1 tltResult01` equals the differential `tltDiff01` (`DensePoly.cisZero` of the
difference). -/
theorem tltResult01_algDeriv :
    DensePoly.cisZero (DensePoly.csub (algDeriv tltRhoX3p1 tltResult01) tltDiff01) = true := by native_decide

/-! ## Non-torsion propagates to `none` on `y² = x³ − 2` -/

/-- The radicand `ρ = x³ − 2` as a `ℚ(x)` element, for the non-torsion witness. -/
def tltRhoX3m2 : DenseFrac ℚ := CFrac.ofPoly [-2, 0, 0, 1]

/-- `torsionLogTerm` on the infinite-order `(3, 5)` returns `none` (not elementary). -/
theorem tltTerm35_none :
    torsionLogTerm 5 tltRhoX3m2 hypRhoX3m2 1 hypPt35 = none := by native_decide

/-- The assembled result for the non-torsion `(3, 5)` — `torsionAlgResult` with `v = 0`; expected
`⟨0, []⟩` (empty log list, the non-elementary signature). -/
def tltResult35 : AlgIntegralResult (DenseFrac ℚ) :=
  torsionAlgResult 5 tltRhoX3m2 hypRhoX3m2 1 radZero hypPt35

/-- The non-torsion assembled result `tltResult35` has empty rational part and empty log list. -/
theorem tltResult35_shape :
    (DensePoly.cisZero tltResult35.ratPart, tltResult35.logTerms.length) = (true, 0) := by native_decide

/-! ## The non-principal-branch summary -/

/-- The non-principal `(1/m)·log` branch computes and validates: on the order-3 point `(0, 1)` of
`y² = x³ + 1`, `torsionLogTerm` returns `(1/3, y − 1)`, the differential passes the log-derivative
certificate, and the term assembles into an `AlgIntegralResult (DenseFrac ℚ)` whose `algDeriv` round-trips; on the
infinite-order `(3, 5)` of `y² = x³ − 2` it returns `none` with an empty log list. -/
theorem torsion_log_branch_validates :
    -- the non-principal branch fires on the order-3 flex (0,1), returning (1/3, y − 1)
    (tltTerm01.map tltTermCheck = some true
      ∧ radIsLogIntegral 2 tltRhoX3p1 tltYm1 (DensePoly.cscale (CFrac.ofPoly [3]) tltDiff01) = true)
    -- the term assembles into the integrator's AlgIntegralResult (DenseFrac ℚ) and algDeriv round-trips
    ∧ ((DensePoly.cisZero tltResult01.ratPart,
        tltResult01.logTerms.length,
        tltResult01.logTerms.head?.map fun t =>
          CFrac.eq t.1 (CField.div CCommRing.one (CFrac.ofScalar (3 : ℚ)))) = (true, 1, some true)
      ∧ DensePoly.cisZero (DensePoly.csub (algDeriv tltRhoX3p1 tltResult01) tltDiff01) = true)
    -- non-torsion (3,5) propagates to none ⟹ NOT elementary
    ∧ ((torsionLogTerm 5 tltRhoX3m2 hypRhoX3m2 1 hypPt35).isNone = true
      ∧ (DensePoly.cisZero tltResult35.ratPart, tltResult35.logTerms.length) = (true, 0)) := by native_decide

end DeepWiki.SymbolicIntegration
