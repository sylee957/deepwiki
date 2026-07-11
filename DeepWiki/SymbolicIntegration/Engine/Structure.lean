import DeepWiki.SymbolicIntegration.Engine.Parametric
import DeepWiki.ComputableAlgebra.PolyEuclideanDense
import DeepWiki.SymbolicIntegration.Engine.Tower.Lvl2

/-! # Structure decision: is a candidate exp/log a new transcendental monomial?

Over a logarithmic tower `C(x)(log u₁,…,log uₘ)` with base `ℚ(x)`, a candidate `log(u)`/`exp(b)` is a
new transcendental monomial iff its (logarithmic) derivative is not a ℚ-linear combination of the
existing `Duᵢ/uᵢ ∈ ℚ(x)`, decided through `CLinearSolve.nullspaceBasis`. -/

namespace DeepWiki.SymbolicIntegration

open DensePoly

namespace CFrac

/-! ### The ℚ-linear-dependence test among represented logarithmic derivatives -/

/-- File-local cleared numerator representing `w * d`. -/
private def clearedNumCoeffs
    {F : (α : Type) → [CField α] → Type} {P : Type → Type}
    [CPoly P] [CPolyEngine P] [CPolyGcd P ℚ] [CPolyEuclidean P] [CFrac F P] [LawfulCFrac F P]
    (d : P ℚ) (w : F ℚ) : P ℚ :=
  let wn := CPoly.normalizeFracPair (CFrac.num w) (CFrac.den w)
  -- `w·d = a·(d / b)` as a polynomial (`b ∣ d` since `d` is a common multiple of all denominators).
  CPolyEngine.mul wn.1 (CPolyEuclidean.div d wn.2)

/-- `linearDepData ws w = (M, m)`: clear `w₁,…,wₘ,w` to a common denominator and assemble the
coefficient matrix `M` (`w` last) whose nullspace vectors are the ℚ-relations `Σ rⱼ wⱼ + r·w = 0`;
`m = ws.length`. -/
def linearDepData
    {F : (α : Type) → [CField α] → Type} {P : Type → Type}
    [CPoly P] [CPolyEngine P] [CPolyGcd P ℚ] [CPolyEuclidean P] [CFrac F P] [LawfulCFrac F P]
    (ws : List (F ℚ)) (w : F ℚ) :
    List (List ℚ) × ℕ :=
  let all := ws ++ [w]
  -- common denominator `d = lcm(denom wⱼ)` over the lowest-terms forms.
  let dens := all.map (fun u => (CPoly.normalizeFracPair (CFrac.num u) (CFrac.den u)).2)
  let d := dens.foldl (fun acc den => CPoly.lcm acc den) (CPoly.one : P ℚ)
  let cols : List (P ℚ) := all.map (fun u => clearedNumCoeffs d u)
  let nrows := (cols.map CPolyEngine.cdeg).foldl Nat.max 0 + 1
  let M : List (List ℚ) :=
    (List.range nrows).map (fun i =>
      cols.map (fun c => CPoly.coeff c i))
  (M, ws.length)

/-- Every cleared logarithmic-dependence row has one column per input derivative. -/
theorem linearDepData_row_length
    {F : (α : Type) → [CField α] → Type} {P : Type → Type}
    [CPoly P] [CPolyEngine P] [CPolyGcd P ℚ] [CPolyEuclidean P] [CFrac F P] [LawfulCFrac F P]
    (ws : List (F ℚ)) (w : F ℚ) :
    ∀ row ∈ (linearDepData ws w).1, row.length = ws.length + 1 := by
  simp [linearDepData]

/-- Every selected logarithmic-dependence kernel vector satisfies each cleared relation row. -/
theorem linearDepData_kernel_mem_row_sound
    {F : (α : Type) → [CField α] → Type} {P : Type → Type}
    [CPoly P] [CPolyEngine P] [CPolyGcd P ℚ] [CPolyEuclidean P] [CFrac F P] [LawfulCFrac F P]
    [CLinearSolve ℚ] [LawfulCLinearSolve ℚ]
    (ws : List (F ℚ)) (w : F ℚ) (rel : List ℚ)
    (hrel : rel ∈ CLinearSolve.nullspaceBasis (linearDepData ws w).1
      ((linearDepData ws w).2 + 1)) :
    ∀ i, i < (linearDepData ws w).1.length →
      linearDot ((linearDepData ws w).1.getD i []) rel = 0 := by
  apply LawfulCLinearSolve.nullspaceBasis_sound (linearDepData ws w).1
    ((linearDepData ws w).2 + 1) rel ?_ hrel
  intro row hrow
  simpa [linearDepData] using linearDepData_row_length ws w row hrow

/-- `logIsNewMonomial logDerivs w = true` iff `log(u)` with logarithmic derivative `w = Du/u` is a
new transcendental monomial, i.e. no `rᵢ ∈ ℚ` give `Du/u = Σ rᵢ (Duᵢ/uᵢ)`. -/
def logIsNewMonomial
    {F : (α : Type) → [CField α] → Type} {P : Type → Type}
    [CPoly P] [CPolyEngine P] [CPolyGcd P ℚ] [CPolyEuclidean P] [CFrac F P] [LawfulCFrac F P] [CLinearSolve ℚ]
    (logDerivs : List (F ℚ)) (w : F ℚ) : Bool :=
  let (M, m) := linearDepData logDerivs w
  let basis := CLinearSolve.nullspaceBasis M (m + 1)
  -- `log(u)` is a *new* monomial iff NO nullspace relation involves the `w`-column (index `m`).
  !(basis.any (fun rel => rel.getD m 0 ≠ 0))

/-- `logRelationCoeffs logDerivs w`: when a relation exists with nonzero `w`-coordinate, returns
`some [r₁,…,rₘ]` with `Du/u = Σ rᵢ (Duᵢ/uᵢ)` (`w`-column normalized to `−1`); else `none`. -/
def logRelationCoeffs
    {F : (α : Type) → [CField α] → Type} {P : Type → Type}
    [CPoly P] [CPolyEngine P] [CPolyGcd P ℚ] [CPolyEuclidean P] [CFrac F P] [LawfulCFrac F P] [CLinearSolve ℚ]
    (logDerivs : List (F ℚ)) (w : F ℚ) : Option (List ℚ) :=
  let (M, m) := linearDepData logDerivs w
  let basis := CLinearSolve.nullspaceBasis M (m + 1)
  match basis.find? (fun rel => rel.getD m 0 ≠ 0) with
  | none => none
  | some rel =>
    let wc := rel.getD m 0                          -- the `w`-column coefficient `r` in `Σ rⱼwⱼ + r·w = 0`
    -- `Du/u = Σ (−rⱼ/r) (Duⱼ/uⱼ)`: solve `r·w = −Σ rⱼ wⱼ` for `w`.
    some ((List.range m).map (fun j => - (rel.getD j 0) / wc))

/-- Check that rational coefficients express one represented logarithmic derivative as a linear
combination of the others. -/
def logRelationCheck
    {F : (α : Type) → [CField α] → Type} {P : Type → Type}
    [CPoly P] [CPolyEngine P] [CFrac F P] [LawfulCFrac F P] [CFieldDomain ℚ P]
    (logDerivs : List (F ℚ)) (w : F ℚ) (rs : List ℚ) : Bool :=
  let combo := (List.zip logDerivs rs).foldl
    (fun acc (wi, r) =>
      CCommRing.add acc (CCommRing.mul (CFrac.ofScalar (F := F) r) wi)) CCommRing.zero
  CCommRing.isZero (CField.sub w combo)

end CFrac

/-- Sparse fractions use the same logarithmic-dependence decision and recover `2/x = 2 · (1/x)`. -/
theorem sparse_logRelation_example :
    let x := CPoly.SparsePoly.ofList [(1, (1 : ℚ))]
    let one := CPoly.SparsePoly.ofList [(0, (1 : ℚ))]
    let two := CPoly.SparsePoly.ofList [(0, (2 : ℚ))]
    let oneOverX : SparseFrac ℚ := CFrac.ofFraction one x (by cfrac_nonzero)
    let twoOverX : SparseFrac ℚ := CFrac.ofFraction two x (by cfrac_nonzero)
    CFrac.logIsNewMonomial [oneOverX] twoOverX = false ∧
      CFrac.logRelationCoeffs [oneOverX] twoOverX = some [2] ∧
      CFrac.logRelationCheck [oneOverX] twoOverX [2] = true := by
  ccompute

/-! ### Logarithmic-monomial examples over `ℚ(x)`

Logarithmic derivatives as `DenseFrac ℚ` values: `log(x) ⟹ 1/x`, `log(x²) ⟹ 2/x` (dependent, `2·(1/x)`),
`log(x+1) ⟹ 1/(x+1)` (independent of `1/x`). -/

open DensePoly

/-- `D(x)/x = 1/x`: the logarithmic derivative of `log(x)`. Numerator `[1]`, denominator `x = [0,1]`. -/
def structLogDerivX : DenseFrac ℚ := CFrac.ofFraction [1] [0, 1] (by cfrac_nonzero)
/-- `D(x²)/x² = 2/x`: the logarithmic derivative of `log(x²)`. Numerator `[2]`, denominator `x = [0,1]`
(`2x/x² = 2/x`). Equal to `2·structLogDerivX`, so `log(x²) = 2 log(x)` is a ℚ-linear relation. -/
def structLogDerivX2 : DenseFrac ℚ := CFrac.ofFraction [2] [0, 1] (by cfrac_nonzero)
/-- `D(x+1)/(x+1) = 1/(x+1)`: the logarithmic derivative of `log(x+1)`. Numerator `[1]`, denominator
`x+1 = [1,1]`. Independent of `1/x` over ℚ. -/
def structLogDerivX1 : DenseFrac ℚ := CFrac.ofFraction [1] [1, 1] (by cfrac_nonzero)

/-- The shared logarithmic-dependence test computes over `C(x)(log x)`: derivative `2/x` is dependent
with relation `[2]`, while `1/(x+1)` is independent, for either logarithmic or exponential candidates. -/
theorem structureTheorem_example :
    (-- (1) `log(x²)` is dependent on `log(x)` — relation detected and verified `D(x²)/x² = 2·D(x)/x`.
     (CFrac.logIsNewMonomial [structLogDerivX] structLogDerivX2 == false)
     && (match CFrac.logRelationCoeffs [structLogDerivX] structLogDerivX2 with
         | some rs => CFrac.logRelationCheck [structLogDerivX] structLogDerivX2 rs && (rs == [2])
         | none => false)
     -- (2) `log(x+1)` is a new transcendental monomial over `C(x)(log x)`.
     && (CFrac.logIsNewMonomial [structLogDerivX] structLogDerivX1 == true)) = true := by
  ccompute

/-! ### Multi-generator logarithmic examples

Over the 2-element tower `C(x)(log x, log(x+1))` (`1/x`, `1/(x+1)` ℚ-independent), `log(x²+x)` is
dependent with relation `[1, 1]` (`1/x + 1/(x+1)`). -/

/-- `D(x²+x)/(x²+x) = (2x+1)/(x²+x) = 1/x + 1/(x+1)`: the logarithmic derivative of `log(x²+x)`.
Numerator `2x+1 = [1,2]`, denominator `x²+x = [0,1,1]`. Equals `1·(1/x) + 1·(1/(x+1))`. -/
def structLogDerivX2pX : DenseFrac ℚ := CFrac.ofFraction [1, 2] [0, 1, 1] (by cfrac_nonzero)

/-- The multi-generator structure decision computes over `C(x)(log x, log(x+1))`: `log(x²+x)` is not a
new monomial (relation `[1, 1]`, verified by `CFrac.logRelationCheck`) and the two generators are mutually
independent. -/
theorem multiStructureTheorem_example :
    (-- `log(x²+x)` is dependent on `{log x, log(x+1)}` with the verified relation `[1,1]`.
     (CFrac.logIsNewMonomial [structLogDerivX, structLogDerivX1] structLogDerivX2pX == false)
     && (match CFrac.logRelationCoeffs [structLogDerivX, structLogDerivX1] structLogDerivX2pX with
         | some rs => CFrac.logRelationCheck [structLogDerivX, structLogDerivX1] structLogDerivX2pX rs
                        && (rs == [1, 1])
         | none => false)
     -- the two generators are independent of each other.
     && (CFrac.logIsNewMonomial [structLogDerivX1] structLogDerivX == true)
     && (CFrac.logIsNewMonomial [structLogDerivX] structLogDerivX1 == true)) = true := by
  ccompute

end DeepWiki.SymbolicIntegration
