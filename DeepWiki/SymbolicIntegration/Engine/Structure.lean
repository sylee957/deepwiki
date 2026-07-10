import DeepWiki.SymbolicIntegration.Engine.Parametric
import DeepWiki.SymbolicIntegration.Engine.FuelFreeGcd
import DeepWiki.SymbolicIntegration.Engine.Tower.Lvl2

/-! # Structure decision: is a candidate exp/log a new transcendental monomial?

Over a logarithmic tower `C(x)(log u₁,…,log uₘ)` with base `ℚ(x)`, a candidate `log(u)`/`exp(b)` is a
new transcendental monomial iff its (logarithmic) derivative is not a ℚ-linear combination of the
existing `Duᵢ/uᵢ ∈ ℚ(x)`, decided by the ℚ-nullspace solver `cNullspaceBasisQ`. -/

namespace DeepWiki.SymbolicIntegration

open DensePoly

namespace DensePoly

/-! ### The ℚ-linear-dependence test among rational-function logarithmic derivatives -/

/-- `cClearedNumCoeffs d w`: the dense `ℚ`-coefficient list of `w·d ∈ ℚ[x]` (well-defined because `d`
is a common multiple of `w`'s denominator), via `qnormPair`-reducing `w` then `numerator·(d/denom)`. -/
def cClearedNumCoeffs (d : DensePoly ℚ) (w : DenseFrac ℚ) : DensePoly ℚ :=
  let wn := qnormPair w.num w.den            -- `w` in lowest terms `(a, b)`
  -- `w·d = a·(d / b)` as a polynomial (`b ∣ d` since `d` is a common multiple of all denominators).
  cmul wn.1 (cdivWf d wn.2)

/-- `cLinearDepData ws w = (M, m)`: clear `w₁,…,wₘ,w` to a common denominator and assemble the
coefficient matrix `M` (`w` last) whose nullspace vectors are the ℚ-relations `Σ rⱼ wⱼ + r·w = 0`;
`m = ws.length`. -/
def cLinearDepData (ws : List (DenseFrac ℚ)) (w : DenseFrac ℚ) :
    List (List ℚ) × ℕ :=
  let all := ws ++ [w]
  -- common denominator `d = lcm(denom wⱼ)` over the lowest-terms forms.
  let dens := all.map (fun u => (qnormPair u.num u.den).2)
  let d := dens.foldl (fun acc den => cLcmQ acc den) [(1 : ℚ)]
  let cols : List (DensePoly ℚ) := all.map (fun u => cClearedNumCoeffs d u)
  let nrows := (cols.map cdeg).foldl Nat.max 0 + 1
  let M : List (List ℚ) :=
    (List.range nrows).map (fun i =>
      cols.map (fun c => (cnorm c).getD i 0))
  (M, ws.length)

/-- `cLogIsNewMonomial logDerivs w = true` iff `log(u)` with logarithmic derivative `w = Du/u` is a
new transcendental monomial, i.e. no `rᵢ ∈ ℚ` give `Du/u = Σ rᵢ (Duᵢ/uᵢ)`. -/
def cLogIsNewMonomial (logDerivs : List (DenseFrac ℚ)) (w : DenseFrac ℚ) : Bool :=
  let (M, m) := cLinearDepData logDerivs w
  let basis := cNullspaceBasisQ M (m + 1)
  -- `log(u)` is a *new* monomial iff NO nullspace relation involves the `w`-column (index `m`).
  !(basis.any (fun rel => rel.getD m 0 ≠ 0))

/-- `cLogRelationExists logDerivs w = !cLogIsNewMonomial …`: `true` iff `w = Du/u` is a ℚ-linear
combination of the existing logarithmic derivatives (`log(u)` is dependent). -/
def cLogRelationExists (logDerivs : List (DenseFrac ℚ)) (w : DenseFrac ℚ) : Bool :=
  !cLogIsNewMonomial logDerivs w

/-- `cLogRelationCoeffs logDerivs w`: when a relation exists with nonzero `w`-coordinate, returns
`some [r₁,…,rₘ]` with `Du/u = Σ rᵢ (Duᵢ/uᵢ)` (`w`-column normalized to `−1`); else `none`. -/
def cLogRelationCoeffs (logDerivs : List (DenseFrac ℚ)) (w : DenseFrac ℚ) : Option (List ℚ) :=
  let (M, m) := cLinearDepData logDerivs w
  let basis := cNullspaceBasisQ M (m + 1)
  match basis.find? (fun rel => rel.getD m 0 ≠ 0) with
  | none => none
  | some rel =>
    let wc := rel.getD m 0                          -- the `w`-column coefficient `r` in `Σ rⱼwⱼ + r·w = 0`
    -- `Du/u = Σ (−rⱼ/r) (Duⱼ/uⱼ)`: solve `r·w = −Σ rⱼ wⱼ` for `w`.
    some ((List.range m).map (fun j => - (rel.getD j 0) / wc))

end DensePoly

/-! ### Logarithmic-monomial examples over `ℚ(x)`

Logarithmic derivatives as `DenseFrac ℚ` values: `log(x) ⟹ 1/x`, `log(x²) ⟹ 2/x` (dependent, `2·(1/x)`),
`log(x+1) ⟹ 1/(x+1)` (independent of `1/x`). -/

open DensePoly

/-- `D(x)/x = 1/x`: the logarithmic derivative of `log(x)`. Numerator `[1]`, denominator `x = [0,1]`. -/
def structLogDerivX : DenseFrac ℚ := CFrac.ofFraction [1] [0, 1]
/-- `D(x²)/x² = 2/x`: the logarithmic derivative of `log(x²)`. Numerator `[2]`, denominator `x = [0,1]`
(`2x/x² = 2/x`). Equal to `2·structLogDerivX`, so `log(x²) = 2 log(x)` is a ℚ-linear relation. -/
def structLogDerivX2 : DenseFrac ℚ := CFrac.ofFraction [2] [0, 1]
/-- `D(x+1)/(x+1) = 1/(x+1)`: the logarithmic derivative of `log(x+1)`. Numerator `[1]`, denominator
`x+1 = [1,1]`. Independent of `1/x` over ℚ. -/
def structLogDerivX1 : DenseFrac ℚ := CFrac.ofFraction [1] [1, 1]

-- Computed decisions against the existing monomial `log(x)` (`logDerivs = [1/x]`):
-- `log(x²)` is dependent with relation `2/x = 2·(1/x)`, while `log(x+1)` is new.
#eval DensePoly.cLogIsNewMonomial [structLogDerivX] structLogDerivX2   -- expect false
#eval DensePoly.cLogIsNewMonomial [structLogDerivX] structLogDerivX1   -- expect true
#eval DensePoly.cLogRelationCoeffs [structLogDerivX] structLogDerivX2  -- expect some [2]

/-- `structRelationCheck logDerivs w rs = true` iff the ℚ-coefficients `rs` satisfy `w = Σ rᵢ (Duᵢ/uᵢ)`
over `ℚ(x)`, by `CCommRing.isZero` of `w − Σ rᵢ (logDerivsᵢ)`. -/
def structRelationCheck (logDerivs : List (DenseFrac ℚ)) (w : DenseFrac ℚ) (rs : List ℚ) : Bool :=
  let combo := (List.zip logDerivs rs).foldl
    (fun acc (wi, r) => CCommRing.add acc (CCommRing.mul (CFrac.ofFraction [r] [1]) wi)) CCommRing.zero
  CCommRing.isZero (CField.sub w combo)

/-- The shared logarithmic-dependence test computes over `C(x)(log x)`: derivative `2/x` is dependent
with relation `[2]`, while `1/(x+1)` is independent, for either logarithmic or exponential candidates. -/
theorem structureTheorem_example :
    (-- (1) `log(x²)` is dependent on `log(x)` — relation detected and verified `D(x²)/x² = 2·D(x)/x`.
     (DensePoly.cLogIsNewMonomial [structLogDerivX] structLogDerivX2 == false)
     && (match DensePoly.cLogRelationCoeffs [structLogDerivX] structLogDerivX2 with
         | some rs => structRelationCheck [structLogDerivX] structLogDerivX2 rs && (rs == [2])
         | none => false)
     -- (2) `log(x+1)` is a new transcendental monomial over `C(x)(log x)`.
     && (DensePoly.cLogIsNewMonomial [structLogDerivX] structLogDerivX1 == true)) = true := by
  native_decide

#print axioms structureTheorem_example

/-! ### Multi-generator logarithmic examples

Over the 2-element tower `C(x)(log x, log(x+1))` (`1/x`, `1/(x+1)` ℚ-independent), `log(x²+x)` is
dependent with relation `[1, 1]` (`1/x + 1/(x+1)`). -/

/-- `D(x²+x)/(x²+x) = (2x+1)/(x²+x) = 1/x + 1/(x+1)`: the logarithmic derivative of `log(x²+x)`.
Numerator `2x+1 = [1,2]`, denominator `x²+x = [0,1,1]`. Equals `1·(1/x) + 1·(1/(x+1))`. -/
def structLogDerivX2pX : DenseFrac ℚ := CFrac.ofFraction [1, 2] [0, 1, 1]

-- Computed decisions against the two-generator tower `[1/x, 1/(x+1)]`.
-- `log(x²+x)` is dependent with relation `[1, 1]`.
#eval DensePoly.cLogIsNewMonomial [structLogDerivX, structLogDerivX1] structLogDerivX2pX  -- false
#eval DensePoly.cLogRelationCoeffs [structLogDerivX, structLogDerivX1] structLogDerivX2pX -- some [1,1]

/-- The multi-generator structure decision computes over `C(x)(log x, log(x+1))`: `log(x²+x)` is not a
new monomial (relation `[1, 1]`, verified by `structRelationCheck`) and the two generators are mutually
independent. -/
theorem multiStructureTheorem_example :
    (-- `log(x²+x)` is dependent on `{log x, log(x+1)}` with the verified relation `[1,1]`.
     (DensePoly.cLogIsNewMonomial [structLogDerivX, structLogDerivX1] structLogDerivX2pX == false)
     && (match DensePoly.cLogRelationCoeffs [structLogDerivX, structLogDerivX1] structLogDerivX2pX with
         | some rs => structRelationCheck [structLogDerivX, structLogDerivX1] structLogDerivX2pX rs
                        && (rs == [1, 1])
         | none => false)
     -- the two generators are independent of each other.
     && (DensePoly.cLogIsNewMonomial [structLogDerivX1] structLogDerivX == true)
     && (DensePoly.cLogIsNewMonomial [structLogDerivX] structLogDerivX1 == true)) = true := by
  native_decide

#print axioms multiStructureTheorem_example

end DeepWiki.SymbolicIntegration
