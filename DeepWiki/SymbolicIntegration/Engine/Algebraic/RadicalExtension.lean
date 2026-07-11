import DeepWiki.SymbolicIntegration.Engine.Tower.Lvl2
import DeepWiki.SymbolicIntegration.Engine.Tower.Deriv
import DeepWiki.ComputableAlgebra.GenericBezout
import DeepWiki.SymbolicIntegration.Engine.MonomialDeriv
import DeepWiki.SymbolicIntegration.Engine.FuelFreeDiophantine

/-! # Algebraic-function integration: simple radical extensions

Core operations for a simple radical extension `F(y)` with `yⁿ = f ∈ F`.

The carrier `RadElem α` represents `α[y]/(yⁿ − f)` as coefficient lists, with
componentwise arithmetic, `radMul`, diagonal `radDeriv`, projection `radProj`,
and rational-part reduction routines for the `θ' = 1`, `θ = log v`, and
`θ = exp v` cases. Concrete validation examples live in
`RadicalExtensionExamples`.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

universe u

/-! ### The simple-radical-extension carrier `RadExt α n f`

`F(y)` with `yⁿ = f ∈ F` (`F = α` a tower-level `[CField α]`), represented as a length-`n` dense
polynomial `RadElem α = DensePoly α` (index = power of `y`) with `yⁿ = f` baked into multiplication. -/

/-- **A radical-extension element** over `α` — a coefficient list `[a₀,…,a_{n−1}]` for `Σ aᵢyⁱ` in
`α[y]/(yⁿ − f)`. A reducible specialization of `DensePoly α`; the degree `n` and radicand `f` are
carried by the operations, not the type. -/
abbrev RadElem (α : Type*) := DensePoly α

namespace RadElem

variable {α : Type*} [CField α]

/-- **Zero** of `α[y]/(yⁿ − f)`: the empty coefficient list. -/
def radZero : RadElem α := []

/-- **One** of `α[y]/(yⁿ − f)`: the constant `1` (`[1]`). -/
def radOne : RadElem α := [CCommRing.one]

/-- **The generator `y`** of `α[y]/(yⁿ − f)` (`[0, 1]`, i.e. `0 + 1·y`). -/
def radGen : RadElem α := [CCommRing.zero, CCommRing.one]

/-- **Reduce a free `y`-polynomial modulo `yⁿ = f`**: fold every coefficient at index `≥ n` down by
`y^{n+k} = f·yᵏ` (the coefficient `aₘ` at index `m = n + k` adds `aₘ·f` to index `k`). Implemented by a
fuel-bounded pass that repeatedly folds the top overflow coefficient into the slot `n` below. Returns a
list of length `≤ n`. -/
def radReduce (n : ℕ) (f : α) : ℕ → RadElem α → RadElem α
  | 0, p => p
  | fuel + 1, p =>
    let p := DensePoly.cnorm p
    if (p : List α).length ≤ n then p
    else
      -- the top coefficient sits at index `length − 1 = n + k` with `k = length − 1 − n`; fold it down
      -- to index `k` via `y^{n+k} = f·yᵏ`, then recurse.
      let m := (p : List α).length - 1
      let k := m - n
      let am := (p : List α).getLast?.getD CCommRing.zero
      let p' := (p : List α).dropLast                       -- drop the top coefficient
      let foldIn := DensePoly.cshift k [CCommRing.mul am f]       -- `am·f · yᵏ`
      radReduce n f fuel (DensePoly.cadd p' foldIn)

/-- **Multiplication** in `α[y]/(yⁿ − f)`: free polynomial multiplication in `y` (`cmul`) followed by
the reduction `yⁿ → f` (`radReduce`). Fuel for the reduction is the product length (`≤ 2n`). -/
def radMul (n : ℕ) (f : α) (p q : RadElem α) : RadElem α :=
  let prod := DensePoly.cmul p q
  radReduce n f ((prod : List α).length + 1) prod

/-! ### The diagonal derivation `radDeriv`

From `yⁿ = f`, `y' = (f'/(n·f))·y`, so the derivation on `Σ aᵢyⁱ` is diagonal:
`D(Σ aᵢyⁱ) = Σ [D(aᵢ) + aᵢ·i·(f'/(n·f))]·yⁱ` (base derivation `CDiffField.cderiv`). -/

variable [CDiffField α]

/-- `logDerRadicand n f = f'/(n·f)` as a base element: the diagonal `radDeriv` multiplier, with
`y' = logDerRadicand · y` and the `yⁱ`-component scaled by `i · logDerRadicand`. -/
def logDerRadicand (n : ℕ) (f : α) : α :=
  CField.div (CDiffField.cderiv f) (CCommRing.mul (CField.natCast n) f)

/-- The diagonal radical derivation `radDeriv n f [a₀,…] = [D a₀ + 0·a₀·ℓ, D a₁ + 1·a₁·ℓ, …]`
(`ℓ = f'/(n·f)`): the `i`-th component maps `aᵢ ↦ D(aᵢ) + aᵢ·(i·ℓ)`, preserving each `yⁱ`-component. -/
def radDeriv (n : ℕ) (f : α) (p : RadElem α) : RadElem α :=
  let ℓ := logDerRadicand n f
  (p.zipIdx.map (fun (a, i) =>
    CCommRing.add (CDiffField.cderiv a) (CCommRing.mul a (CCommRing.mul (CField.natCast i) ℓ))))

end RadElem

/-- The radicand `f = x³ + 1 ∈ ℚ(x)` (numerator `[1,0,0,1]` = `1 + x³`). -/
def radicandX3p1 : DenseFrac ℚ := CFrac.ofPoly [1, 0, 0, 1]

/-- The ℚ(x) value `3x² = (x³+1)' ∈ ℚ(x)`, the derivative of the radicand. -/
def radicandDeriv : DenseFrac ℚ := CFrac.ofPoly [0, 0, 3]

/-- The diagonal multiplier `ℓ = f'/(2f) = 3x²/(2(x³+1)) ∈ ℚ(x)` for `D(y) = ℓ·y`. -/
def radicandLogDer : DenseFrac ℚ := RadElem.logDerRadicand 2 radicandX3p1

/-! ### The `Tᵢ` decoupling

The per-`y`-power projection `radProj i` (keep the `yⁱ`-component, zero the rest) satisfies
`Tᵢ(yʲ) = yʲ·[i=j]` and commutes with `radDeriv` (by diagonality), so `∫(Σ gᵢyⁱ)` decouples into the
independent `∫gᵢyⁱ`. -/

namespace RadElem

variable {α : Type*} [CField α]

/-- The projection `Tᵢ` `radProj i p`: keep the `yⁱ`-component of `p`, zero every other power
(satisfies `Tᵢ(yʲ) = yʲ·[i=j]`). -/
def radProj (i : ℕ) (p : RadElem α) : RadElem α :=
  match (p : List α)[i]? with
  | none => []
  | some a => DensePoly.cnorm (DensePoly.cshift i [a])

end RadElem

/-! ### Case 1 rational-part reduction (`θ' = 1`)

The piece `C/(Vᵏy)` with `V` coprime to the radicand `f`. A Hermite-style step lowers `k` by finding `B`
with `(1−k)V'fB ≡ C (mod V)` (solvable since `gcd((1−k)V'f, V) = 1`) and residual
`D = ((1−k)V'fB − C)/V + B'f + Bg` (`g` from `(f/y)' = g/y`); cleared over `Vᵏy` the step is the pure
`F[θ]` identity `(1−k)V'fB − C + V(B'f + Bg) = V·D`. -/

namespace CPoly

/-- Case-1 cofactor `radCase1Cofactor k V Df f C = B`: the degree-`< deg V` polynomial solving
`(1−k)·V'·f·B ≡ C (mod V)` via `CPoly.diophantineReduced ((1−k)·V'·f) V C`. `Df = V'` is passed in. -/
def radCase1Cofactor {P : Type u → Type u} [CPoly P] [CPolyEngine P] [CPolyEuclidean P]
    {α : Type u} [CField α] (k : ℕ) (V Df f C : P α) : P α :=
  let oneMinusK := CPolyEngine.ofCoeffList
    [CCommRing.neg (CField.natCast (k - 1))]
  let coeff := CPolyEngine.mul oneMinusK (CPolyEngine.mul Df f)
  (CPoly.diophantineReduced coeff V C).1

/-- Case-1 residual `radCase1Residual k V Df f g B C Bder = D`: the lowered-`k` numerator
`D = ((1−k)V'fB − C)/V + B'f + Bg`. `Df = V'`, `Bder = B'`, `g` from `(f/y)' = g/y` passed in; division
by `V` is selected through `CPolyEuclidean.div`. -/
def radCase1Residual {P : Type u → Type u} [CPoly P] [CPolyEngine P] [CPolyEuclidean P]
    {α : Type u} [CField α] (k : ℕ) (V Df f g B C Bder : P α) : P α :=
  let oneMinusK := CPolyEngine.ofCoeffList
    [CCommRing.neg (CField.natCast (k - 1))]
  let topNum := CPolyEngine.sub
    (CPolyEngine.mul oneMinusK (CPolyEngine.mul Df (CPolyEngine.mul f B))) C
  let quotient := CPolyEuclidean.div topNum V
  CPolyEngine.add quotient
    (CPolyEngine.add (CPolyEngine.mul Bder f) (CPolyEngine.mul B g))

/-! ### Case 2 rational-part reduction (`θ' = 1`, `n = 2`)

The piece `C/(Wᵏy)` where `W` is a squarefree factor of the radicand `f` (not coprime to `f`). With
`h = f/W`, `radDeriv(Bf/(Wᵏy)) = (B·(½−k)·W'·h)/(Wᵏy) + (B'h + ½Bh')/(W^{k−1}y)`, so subtracting
`C/(Wᵏy)` leaves `D/(W^{k−1}y)` provided `B·(½−k)·W'·h ≡ C (mod W)`; residual
`D = (B·(½−k)W'h − C)/W + B'h + ½Bh'`, cleared identity `B·(½−k)W'h − C + W·(B'h + ½Bh') = W·D`. -/

/-- Case-2 cofactor (`n = 2`) `radCase2Cofactor k W h C = B`: the degree-`< deg W` polynomial solving
`B·(½−k)·W'·h ≡ C (mod W)` via `CPoly.diophantineReduced ((½−k)W'h) W C`. `h = f/W`, `W'` is `cderiv W`. -/
def radCase2Cofactor {P : Type u → Type u} [CPoly P] [CPolyEngine P] [CPolyEuclidean P]
    {α : Type u} [CField α] (k : ℕ) (W h C : P α) : P α :=
  let half := CPolyEngine.ofCoeffList (P := P)
    [CField.div CCommRing.one (CField.natCast 2)]
  let kpoly := CPolyEngine.ofCoeffList (P := P) [CField.natCast k]
  let coef := CPolyEngine.mul (CPolyEngine.sub half kpoly)
    (CPolyEngine.mul (CPolyEngine.deriv W) h)
  (CPoly.diophantineReduced coef W C).1

/-- Case-2 residual (`n = 2`) `radCase2Residual k W h C B = D`: the lowered-`k` numerator
`D = (B·(½−k)W'h − C)/W + B'h + ½Bh'`; `B'` is `cderiv B`, `h'` is `cderiv h`, division by `W` is
`CPolyEuclidean.div`. -/
def radCase2Residual {P : Type u → Type u} [CPoly P] [CPolyEngine P] [CPolyEuclidean P]
    {α : Type u} [CField α] (k : ℕ) (W h C B : P α) : P α :=
  let half := CPolyEngine.ofCoeffList (P := P)
    [CField.div CCommRing.one (CField.natCast 2)]
  let kpoly := CPolyEngine.ofCoeffList (P := P) [CField.natCast k]
  let coef := CPolyEngine.mul (CPolyEngine.sub half kpoly)
    (CPolyEngine.mul (CPolyEngine.deriv W) h)
  let topNum := CPolyEngine.sub (CPolyEngine.mul B coef) C
  let quotient := CPolyEuclidean.div topNum W
  CPolyEngine.add quotient
    (CPolyEngine.add (CPolyEngine.mul (CPolyEngine.deriv B) h)
      (CPolyEngine.mul half (CPolyEngine.mul B (CPolyEngine.deriv h))))

example :
    let ofList : List ℚ → CPoly.SparsePoly ℚ := CPolyEngine.ofCoeffList
    let f := ofList [0, 1]
    let V := ofList [-1, 1]
    let Df := ofList [1]
    let C := ofList [1]
    let g := ofList [1 / 2]
    let B := radCase1Cofactor 2 V Df f C
    let D := radCase1Residual 2 V Df f g B C (CPolyEngine.deriv B)
    CPolyEngine.cisZero (CPolyEngine.sub B (ofList [-1])) = true ∧
      CPolyEngine.cisZero (CPolyEngine.sub D (ofList [1 / 2])) = true := by
  ccompute

example :
    let ofList : List ℚ → CPoly.SparsePoly ℚ := CPolyEngine.ofCoeffList
    let W := ofList [0, 1]
    let h := ofList [-1, 0, 1]
    let C := ofList [1]
    let B := radCase2Cofactor 2 W h C
    let D := radCase2Residual 2 W h C B
    CPolyEngine.cisZero (CPolyEngine.sub B (ofList [2 / 3])) = true ∧
      CPolyEngine.cisZero (CPolyEngine.sub D (ofList [0, -1 / 3])) = true := by
  ccompute

/-! ### Case 3 rational-part reduction (`θ' = 1`)

The leftover `C/y`, lowering `deg C` rather than a denominator. With `(Bf/y)' = (B'f + Bg)/y`, taking
`B = b·θ^{j+1}` a single constant-coefficient monomial (`j+1 = deg C − deg f + 1`), the leading relation
gives `b = lcf(C) / ((j+1) + lcf(g))` and residual `D = B'f + Bg − C` with `deg D < deg C`. -/

/-- Case-3 leading-coefficient cofactor `radCase3Cofactor f g C = B`: the constant-coefficient monomial
`B = b·θ^{j+1}` (`j+1 = deg C − deg f + 1`) with `b = lcf(C) / ((j+1) + lcf(g))`, cancelling the leading
term of `C` in the `C/y` degree-lowering (`[]` when `deg C < deg f`). -/
def radCase3Cofactor {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] (f g C : P α) : P α :=
  let dC := CPolyEngine.cdeg C
  let dF := CPolyEngine.cdeg f
  if CPolyEngine.cisZero C || dC < dF then CPolyEngine.ofCoeffList []
  else
    let jp1 := dC - dF + 1                                         -- `j + 1 = deg C − deg f + 1`
    let denom := CCommRing.add (CField.natCast jp1) (CPolyEngine.clead g)
    let b := CField.div (CPolyEngine.clead C) denom                -- `b = lcf(C)/((j+1)+lcf(g))`
    CPolyEngine.monomial b jp1                                     -- `b·θ^{j+1}`

/-- Case-3 residual `radCase3Residual f g B C Bder = D`: the lowered-degree numerator `D = B'f + Bg − C`
of the `C/y` step. `Bder = B'`, `g` from `(f/y)' = g/y` passed in; with `B` from `radCase3Cofactor`,
`deg D < deg C`. -/
def radCase3Residual {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] (f g B C Bder : P α) : P α :=
  CPolyEngine.sub
    (CPolyEngine.add (CPolyEngine.mul Bder f) (CPolyEngine.mul B g)) C -- `B'f + Bg − C`

/-! ### `θ = log v` rational-part reduction

For `θ = log v` (`θ' = v'/v ∈ F`) the `C/y` degree-lowering is shaped as Case 3, but the leading-coefficient
bracket becomes `(j+1)·θ' + lcf(g)`, so `b = lcf(C)/((j+1)θ' + lcf(g))` (`radCase3CofactorGen` takes `θ'`
as `Dt`), and `B'` is the full monomial derivative `CPolyEngine.monomialDeriv [θ'] B`. Setting `Dt = 1` recovers
Case 3. -/

/-- Generalized Case-3 cofactor `radCase3CofactorGen Dt f g C = B`: the monomial `B = b·θ^{j+1}` with
`b = lcf(C) / ((j+1)·θ' + lcf(g))` for any `θ` of derivative `Dt = θ'` (`[]` when `deg C < deg f`);
`Dt = 1` recovers Case 3. -/
def radCase3CofactorGen {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] (Dt : α) (f g C : P α) : P α :=
  let dC := CPolyEngine.cdeg C
  let dF := CPolyEngine.cdeg f
  if CPolyEngine.cisZero C || dC < dF then CPolyEngine.ofCoeffList []
  else
    let jp1 := dC - dF + 1                                         -- `j + 1 = deg C − deg f + 1`
    let denom := CCommRing.add
      (CCommRing.mul (CField.natCast jp1) Dt) (CPolyEngine.clead g)
    let b := CField.div (CPolyEngine.clead C) denom                 -- `b = lcf(C)/((j+1)θ' + lcf(g))`
    CPolyEngine.monomial b jp1                                      -- `b·θ^{j+1}`

example :
    let ofList : List ℚ → CPoly.SparsePoly ℚ := CPolyEngine.ofCoeffList
    let f := ofList [0, 1]
    let g := ofList [1 / 2]
    let C := ofList [0, 1, 1]
    let B := radCase3Cofactor f g C
    let D := radCase3Residual f g B C (CPolyEngine.deriv B)
    CPoly.coeff B 2 = 2 / 5 ∧ CPoly.coeff D 1 = -1 ∧
      CPoly.coeff (radCase3CofactorGen (1 : ℚ) f g C) 2 = 2 / 5 := by
  ccompute

/-! ### `θ = exp v` rational-part reduction

For `θ = exp v`, `θ` divides its own derivative (`θ' = v'·θ`); the new piece is `C/(θᵏy)` with
`(Bf/(θᵏy))' = (B'f + Bg − k·v'·B·f)/(θᵏy)`. Matching constant (θ-degree-`0`) terms
`c₀ = b₀g₀ − k·v'·b₀·f₀` on the constant-`b₀` slice gives `b₀ = c₀/(g₀ − k·v'·f₀)`, residual
`D = ((B'f + Bg − kv'Bf) − C)/θ`, cleared identity `(B'f + Bg − kv'Bf) − C = θ·D`. -/

/-- `θ = exp v` `C/(θᵏy)` cofactor `radExpCofactor k vder f g C = B`: the constant `B = [b₀]` with
`b₀ = c₀ / (g₀ − k·v'·f₀)` (`f₀, g₀, c₀` the `θ⁰`-coefficients of `f, g, C`, `vder = v'`), solving the
constant-term match `c₀ = b₀g₀ − k·v'·b₀·f₀`. -/
def radExpCofactor {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] (k : ℕ) (vder : α) (f g C : P α) : P α :=
  let f0 := CPoly.coeff f 0
  let g0 := CPoly.coeff g 0
  let c0 := CPoly.coeff C 0
  let denom := CField.sub g0
    (CCommRing.mul (CCommRing.mul (CField.natCast k) vder) f0)
  CPolyEngine.ofCoeffList [CField.div c0 denom]                               -- `[b₀]`

example :
    let ofList : List ℚ → CPoly.SparsePoly ℚ := CPolyEngine.ofCoeffList
    let f := ofList [1, 1]
    let g := ofList [0, 1 / 2]
    let C := ofList [1, 1]
    CPoly.coeff (radExpCofactor 1 (1 : ℚ) f g C) 0 = -1 := by
  ccompute

/-- `θ = exp v` `C/(θᵏy)` residual `radExpResidual k vder f g B C Bder = D`: the lowered-`k` numerator
`D = ((B'f + Bg − k·v'·B·f) − C)/θ`. `vder = v'`, `Bder = B'`, `g` passed in; division by `θ` is
`CPolyEuclidean.div _ [0,1]`. -/
def radExpResidual {P : Type u → Type u} [CPoly P] [CPolyEngine P] [CPolyEuclidean P]
    {α : Type u} [CField α] (k : ℕ) (vder : α) (f g B C Bder : P α) : P α :=
  let kpoly := CPolyEngine.ofCoeffList (P := P)
    [CCommRing.mul (CField.natCast k) vder]
  let kvBf := CPolyEngine.mul kpoly (CPolyEngine.mul B f)
  let num := CPolyEngine.sub
    (CPolyEngine.sub
      (CPolyEngine.add (CPolyEngine.mul Bder f) (CPolyEngine.mul B g)) kvBf) C
  CPolyEuclidean.div num
    (CPolyEngine.ofCoeffList (P := P) [CCommRing.zero, CCommRing.one])

end CPoly

end DeepWiki.SymbolicIntegration
