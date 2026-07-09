import DeepWiki.SymbolicIntegration.Engine.Parametric
import DeepWiki.SymbolicIntegration.Engine.FuelFreeGcd
import DeepWiki.SymbolicIntegration.Engine.Tower.Lvl2

/-! # Structure decision: is a candidate exp/log a new transcendental monomial?

Over a logarithmic tower `C(x)(log u₁,…,log uₘ)` with base `ℚ(x)`, a candidate `log(u)`/`exp(b)` is a
new transcendental monomial iff its (logarithmic) derivative is not a ℚ-linear combination of the
existing `Duᵢ/uᵢ ∈ ℚ(x)`, decided by the ℚ-nullspace solver `cNullspaceBasisQ`. -/

namespace DeepWiki.SymbolicIntegration

open CPoly

namespace CPoly

/-! ### The ℚ-linear-dependence test among rational-function logarithmic derivatives -/

/-- `cClearedNumCoeffs d w`: the dense `ℚ`-coefficient list of `w·d ∈ ℚ[x]` (well-defined because `d`
is a common multiple of `w`'s denominator), via `qnormPair`-reducing `w` then `numerator·(d/denom)`. -/
def cClearedNumCoeffs (d : CPoly ℚ) (w : CFrac ℚ) : CPoly ℚ :=
  let wn := qnormPair w.1.1 w.1.2            -- `w` in lowest terms `(a, b)`
  -- `w·d = a·(d / b)` as a polynomial (`b ∣ d` since `d` is a common multiple of all denominators).
  cmul wn.1 (cdivWf d wn.2)

/-- `cLinearDepData ws w = (M, m)`: clear `w₁,…,wₘ,w` to a common denominator and assemble the
coefficient matrix `M` (`w` last) whose nullspace vectors are the ℚ-relations `Σ rⱼ wⱼ + r·w = 0`;
`m = ws.length`. -/
def cLinearDepData (ws : List (CFrac ℚ)) (w : CFrac ℚ) :
    List (List ℚ) × ℕ :=
  let all := ws ++ [w]
  -- common denominator `d = lcm(denom wⱼ)` over the lowest-terms forms.
  let dens := all.map (fun u => (qnormPair u.1.1 u.1.2).2)
  let d := dens.foldl (fun acc den => cLcmQ acc den) [(1 : ℚ)]
  let cols : List (CPoly ℚ) := all.map (fun u => cClearedNumCoeffs d u)
  let nrows := (cols.map cdeg).foldl Nat.max 0 + 1
  let M : List (List ℚ) :=
    (List.range nrows).map (fun i =>
      cols.map (fun c => (cnorm c).getD i 0))
  (M, ws.length)

/-- `cLogIsNewMonomial logDerivs w = true` iff `log(u)` with logarithmic derivative `w = Du/u` is a
new transcendental monomial, i.e. no `rᵢ ∈ ℚ` give `Du/u = Σ rᵢ (Duᵢ/uᵢ)`. -/
def cLogIsNewMonomial (logDerivs : List (CFrac ℚ)) (w : CFrac ℚ) : Bool :=
  let (M, m) := cLinearDepData logDerivs w
  let basis := cNullspaceBasisQ M (m + 1)
  -- `log(u)` is a *new* monomial iff NO nullspace relation involves the `w`-column (index `m`).
  !(basis.any (fun rel => rel.getD m 0 ≠ 0))

/-- `cExpIsNewMonomial logDerivs b = true` iff `exp(b)` with exponent derivative `Db` is a new
transcendental monomial, i.e. no `rᵢ ∈ ℚ` give `Db = Σ rᵢ (Duᵢ/uᵢ)` — the same ℚ-linear-dependence
test as the logarithm case applied to `Db`. -/
def cExpIsNewMonomial (logDerivs : List (CFrac ℚ)) (b : CFrac ℚ) : Bool :=
  cLogIsNewMonomial logDerivs b

/-- `cLogRelationExists logDerivs w = !cLogIsNewMonomial …`: `true` iff `w = Du/u` is a ℚ-linear
combination of the existing logarithmic derivatives (`log(u)` is dependent). -/
def cLogRelationExists (logDerivs : List (CFrac ℚ)) (w : CFrac ℚ) : Bool :=
  !cLogIsNewMonomial logDerivs w

/-- `cLogRelationCoeffs logDerivs w`: when a relation exists with nonzero `w`-coordinate, returns
`some [r₁,…,rₘ]` with `Du/u = Σ rᵢ (Duᵢ/uᵢ)` (`w`-column normalized to `−1`); else `none`. -/
def cLogRelationCoeffs (logDerivs : List (CFrac ℚ)) (w : CFrac ℚ) : Option (List ℚ) :=
  let (M, m) := cLinearDepData logDerivs w
  let basis := cNullspaceBasisQ M (m + 1)
  match basis.find? (fun rel => rel.getD m 0 ≠ 0) with
  | none => none
  | some rel =>
    let wc := rel.getD m 0                          -- the `w`-column coefficient `r` in `Σ rⱼwⱼ + r·w = 0`
    -- `Du/u = Σ (−rⱼ/r) (Duⱼ/uⱼ)`: solve `r·w = −Σ rⱼ wⱼ` for `w`.
    some ((List.range m).map (fun j => - (rel.getD j 0) / wc))

end CPoly

/-! ### Logarithmic-monomial examples over `ℚ(x)`

Logarithmic derivatives as `CFrac ℚ` values: `log(x) ⟹ 1/x`, `log(x²) ⟹ 2/x` (dependent, `2·(1/x)`),
`log(x+1) ⟹ 1/(x+1)` (independent of `1/x`). -/

open CPoly

/-- A ℚ(x) fraction `num/den` as a `CFrac ℚ` element (`den ≠ 0` discharged automatically). -/
def qFracStruct (num den : List ℚ) (h : CPoly.cisZero den = false := by native_decide) : CFrac ℚ :=
  ⟨(num, den), h⟩

/-- `D(x)/x = 1/x`: the logarithmic derivative of `log(x)`. Numerator `[1]`, denominator `x = [0,1]`. -/
def structLogDerivX : CFrac ℚ := qFracStruct [1] [0, 1]
/-- `D(x²)/x² = 2/x`: the logarithmic derivative of `log(x²)`. Numerator `[2]`, denominator `x = [0,1]`
(`2x/x² = 2/x`). Equal to `2·structLogDerivX`, so `log(x²) = 2 log(x)` is a ℚ-linear relation. -/
def structLogDerivX2 : CFrac ℚ := qFracStruct [2] [0, 1]
/-- `D(x+1)/(x+1) = 1/(x+1)`: the logarithmic derivative of `log(x+1)`. Numerator `[1]`, denominator
`x+1 = [1,1]`. Independent of `1/x` over ℚ. -/
def structLogDerivX1 : CFrac ℚ := qFracStruct [1] [1, 1]

-- Computed decisions against the existing monomial `log(x)` (`logDerivs = [1/x]`):
-- `log(x²)` is dependent with relation `2/x = 2·(1/x)`, while `log(x+1)` is new.
#eval CPoly.cLogIsNewMonomial [structLogDerivX] structLogDerivX2   -- expect false
#eval CPoly.cLogIsNewMonomial [structLogDerivX] structLogDerivX1   -- expect true
#eval CPoly.cLogRelationCoeffs [structLogDerivX] structLogDerivX2  -- expect some [2]

/-- `structRelationCheck logDerivs w rs = true` iff the ℚ-coefficients `rs` satisfy `w = Σ rᵢ (Duᵢ/uᵢ)`
over `ℚ(x)`, by `CField.isZero` of `w − Σ rᵢ (logDerivsᵢ)`. -/
def structRelationCheck (logDerivs : List (CFrac ℚ)) (w : CFrac ℚ) (rs : List ℚ) : Bool :=
  let combo := (List.zip logDerivs rs).foldl
    (fun acc (wi, r) => CField.add acc (CField.mul (qFracStruct [r] [1]) wi)) CField.zero
  CField.isZero (CField.sub w combo)

/-- The logarithmic-monomial structure decision computes over `C(x)(log x)`: `log(x²)` is not a new
monomial (`cLogRelationCoeffs = some [2]`, verified by `structRelationCheck`) and `log(x+1)` is a new
transcendental monomial. -/
theorem structureTheorem_example :
    (-- (1) `log(x²)` is dependent on `log(x)` — relation detected and verified `D(x²)/x² = 2·D(x)/x`.
     (CPoly.cLogIsNewMonomial [structLogDerivX] structLogDerivX2 == false)
     && (match CPoly.cLogRelationCoeffs [structLogDerivX] structLogDerivX2 with
         | some rs => structRelationCheck [structLogDerivX] structLogDerivX2 rs && (rs == [2])
         | none => false)
     -- (2) `log(x+1)` is a new transcendental monomial over `C(x)(log x)`.
     && (CPoly.cLogIsNewMonomial [structLogDerivX] structLogDerivX1 == true)) = true := by
  native_decide

#print axioms structureTheorem_example

/-! ### Exponential-monomial examples

Over `C(x)(log x)`: `exp(b)` with `Db = 2/x` is not new (`Db = 2·(1/x)`), while `Db = 1/(x+1)` gives a
new exponential monomial. -/

/-- The exponential-monomial structure decision computes over `C(x)(log x)`: `exp(b)` with `Db = 2/x`
is not a new monomial (relation `[2]`, verified by `structRelationCheck`) and `Db = 1/(x+1)` gives a
new transcendental monomial. -/
theorem expStructureTheorem_example :
    ((CPoly.cExpIsNewMonomial [structLogDerivX] structLogDerivX2 == false)
     && (match CPoly.cLogRelationCoeffs [structLogDerivX] structLogDerivX2 with
         | some rs => structRelationCheck [structLogDerivX] structLogDerivX2 rs && (rs == [2])
         | none => false)
     && (CPoly.cExpIsNewMonomial [structLogDerivX] structLogDerivX1 == true)) = true := by
  native_decide

#print axioms expStructureTheorem_example

/-! ### Multi-generator logarithmic examples

Over the 2-element tower `C(x)(log x, log(x+1))` (`1/x`, `1/(x+1)` ℚ-independent), `log(x²+x)` is
dependent with relation `[1, 1]` (`1/x + 1/(x+1)`). -/

/-- `D(x²+x)/(x²+x) = (2x+1)/(x²+x) = 1/x + 1/(x+1)`: the logarithmic derivative of `log(x²+x)`.
Numerator `2x+1 = [1,2]`, denominator `x²+x = [0,1,1]`. Equals `1·(1/x) + 1·(1/(x+1))`. -/
def structLogDerivX2pX : CFrac ℚ := qFracStruct [1, 2] [0, 1, 1]

-- Computed decisions against the two-generator tower `[1/x, 1/(x+1)]`.
-- `log(x²+x)` is dependent with relation `[1, 1]`.
#eval CPoly.cLogIsNewMonomial [structLogDerivX, structLogDerivX1] structLogDerivX2pX  -- false
#eval CPoly.cLogRelationCoeffs [structLogDerivX, structLogDerivX1] structLogDerivX2pX -- some [1,1]

/-- The multi-generator structure decision computes over `C(x)(log x, log(x+1))`: `log(x²+x)` is not a
new monomial (relation `[1, 1]`, verified by `structRelationCheck`) and the two generators are mutually
independent. -/
theorem multiStructureTheorem_example :
    (-- `log(x²+x)` is dependent on `{log x, log(x+1)}` with the verified relation `[1,1]`.
     (CPoly.cLogIsNewMonomial [structLogDerivX, structLogDerivX1] structLogDerivX2pX == false)
     && (match CPoly.cLogRelationCoeffs [structLogDerivX, structLogDerivX1] structLogDerivX2pX with
         | some rs => structRelationCheck [structLogDerivX, structLogDerivX1] structLogDerivX2pX rs
                        && (rs == [1, 1])
         | none => false)
     -- the two generators are independent of each other.
     && (CPoly.cLogIsNewMonomial [structLogDerivX1] structLogDerivX == true)
     && (CPoly.cLogIsNewMonomial [structLogDerivX] structLogDerivX1 == true)) = true := by
  native_decide

#print axioms multiStructureTheorem_example

end DeepWiki.SymbolicIntegration
