import DeepWiki.SymbolicIntegration.Computable.Tower.Field
import DeepWiki.SymbolicIntegration.Computable.Tower.Deriv
import DeepWiki.SymbolicIntegration.Computable.GenericBezout
import DeepWiki.SymbolicIntegration.Computable.MonomialDeriv
import DeepWiki.SymbolicIntegration.Computable.FuelFreeDiophantine

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

/-! ### The simple-radical-extension carrier `RadExt α n f`

`F(y)` with `yⁿ = f ∈ F` (`F = α` a tower-level `[CField α]`), represented as a length-`n` coefficient
list `RadElem α = List α` (index = power of `y`) with `yⁿ = f` baked into multiplication. -/

/-- **A radical-extension element** over `α` — a coefficient list `[a₀,…,a_{n−1}]` for `Σ aᵢyⁱ` in
`α[y]/(yⁿ − f)`. A reducible `abbrev` for `List α` so the `List` instances transfer (the degree `n` and
radicand `f` are carried by the operations, not the type). -/
abbrev RadElem (α : Type*) := List α

namespace RadElem

variable {α : Type*} [CField α]

/-- **Zero** of `α[y]/(yⁿ − f)`: the empty coefficient list. -/
def radZero : RadElem α := []

/-- **One** of `α[y]/(yⁿ − f)`: the constant `1` (`[1]`). -/
def radOne : RadElem α := [CField.one]

/-- **The generator `y`** of `α[y]/(yⁿ − f)` (`[0, 1]`, i.e. `0 + 1·y`). -/
def radGen : RadElem α := [CField.zero, CField.one]

/-- **Componentwise addition** in `α[y]/(yⁿ − f)` (the shorter list zero-extended). -/
def radAdd (p q : RadElem α) : RadElem α := CPolyG.caddG p q

/-- **Negation** in `α[y]/(yⁿ − f)`, componentwise. -/
def radNeg (p : RadElem α) : RadElem α := CPolyG.cnegG p

/-- **Subtraction** in `α[y]/(yⁿ − f)`, `p − q := p + (−q)`. -/
def radSub (p q : RadElem α) : RadElem α := CPolyG.csubG p q

/-- **Scalar multiplication** of a `RadElem` by a base element `c : α`, componentwise. -/
def radScale (c : α) (p : RadElem α) : RadElem α := CPolyG.cscaleG c p

/-- **Reduce a free `y`-polynomial modulo `yⁿ = f`**: fold every coefficient at index `≥ n` down by
`y^{n+k} = f·yᵏ` (the coefficient `aₘ` at index `m = n + k` adds `aₘ·f` to index `k`). Implemented by a
fuel-bounded pass that repeatedly folds the top overflow coefficient into the slot `n` below. Returns a
list of length `≤ n`. -/
def radReduce (n : ℕ) (f : α) : ℕ → RadElem α → RadElem α
  | 0, p => p
  | fuel + 1, p =>
    let p := CPolyG.cnormG p
    if (p : List α).length ≤ n then p
    else
      -- the top coefficient sits at index `length − 1 = n + k` with `k = length − 1 − n`; fold it down
      -- to index `k` via `y^{n+k} = f·yᵏ`, then recurse.
      let m := (p : List α).length - 1
      let k := m - n
      let am := (p : List α).getLast?.getD CField.zero
      let p' := (p : List α).dropLast                       -- drop the top coefficient
      let foldIn := CPolyG.cshiftG k [CField.mul am f]       -- `am·f · yᵏ`
      radReduce n f fuel (CPolyG.caddG p' foldIn)

/-- **Multiplication** in `α[y]/(yⁿ − f)`: free polynomial multiplication in `y` (`cmulG`) followed by
the reduction `yⁿ → f` (`radReduce`). Fuel for the reduction is the product length (`≤ 2n`). -/
def radMul (n : ℕ) (f : α) (p q : RadElem α) : RadElem α :=
  let prod := CPolyG.cmulG p q
  radReduce n f ((prod : List α).length + 1) prod

/-- **Zero test** in `α[y]/(yⁿ − f)`: read `cisZeroG` off the coefficient list (all components vanish). -/
def radIsZero (p : RadElem α) : Bool := CPolyG.cisZeroG p

/-! ### The diagonal derivation `radDeriv`

From `yⁿ = f`, `y' = (f'/(n·f))·y`, so the derivation on `Σ aᵢyⁱ` is diagonal:
`D(Σ aᵢyⁱ) = Σ [D(aᵢ) + aᵢ·i·(f'/(n·f))]·yⁱ` (base derivation `CDiffField.cderiv`). -/

variable [CDiffField α]

/-- `logDerRadicand n f = f'/(n·f)` as a base element: the diagonal `radDeriv` multiplier, with
`y' = logDerRadicand · y` and the `yⁱ`-component scaled by `i · logDerRadicand`. -/
def logDerRadicand (n : ℕ) (f : α) : α :=
  CField.div (CDiffField.cderiv f) (CField.mul (CPolyG.cnatCastG n) f)

/-- The diagonal radical derivation `radDeriv n f [a₀,…] = [D a₀ + 0·a₀·ℓ, D a₁ + 1·a₁·ℓ, …]`
(`ℓ = f'/(n·f)`): the `i`-th component maps `aᵢ ↦ D(aᵢ) + aᵢ·(i·ℓ)`, preserving each `yⁱ`-component. -/
def radDeriv (n : ℕ) (f : α) (p : RadElem α) : RadElem α :=
  let ℓ := logDerRadicand n f
  (p.zipIdx.map (fun (a, i) =>
    CField.add (CDiffField.cderiv a) (CField.mul a (CField.mul (CPolyG.cnatCastG i) ℓ))))

end RadElem

/-- A `ℚ(x)` value (`QFunNZG ℚ`) from a numerator `CPoly = List ℚ` over denominator `1`. -/
def qxOfNum (num : CPolyG ℚ) : QFunNZG ℚ :=
  ⟨(num, [CField.one]), QFunNZG.cisZeroG_one_singleton⟩

/-- A `ℚ(x)` value `num/den` from a numerator and a nonzero denominator `CPolyG ℚ`. -/
def qxOfFrac (num den : CPolyG ℚ) (h : CPolyG.cisZeroG den = false) : QFunNZG ℚ :=
  ⟨(num, den), h⟩

/-- The radicand `f = x³ + 1 ∈ ℚ(x)` (numerator `[1,0,0,1]` = `1 + x³`). -/
def radicandX3p1 : QFunNZG ℚ := qxOfNum [1, 0, 0, 1]

/-- The ℚ(x) value `3x² = (x³+1)' ∈ ℚ(x)`, the derivative of the radicand. -/
def radicandDeriv : QFunNZG ℚ := qxOfNum [0, 0, 3]

/-- The diagonal multiplier `ℓ = f'/(2f) = 3x²/(2(x³+1)) ∈ ℚ(x)` for `D(y) = ℓ·y`. -/
def radicandLogDer : QFunNZG ℚ := RadElem.logDerRadicand 2 radicandX3p1

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
  | some a => CPolyG.cnormG (CPolyG.cshiftG i [a])

end RadElem

/-! ### Case 1 rational-part reduction (`θ' = 1`)

The piece `C/(Vᵏy)` with `V` coprime to the radicand `f`. A Hermite-style step lowers `k` by finding `B`
with `(1−k)V'fB ≡ C (mod V)` (solvable since `gcd((1−k)V'f, V) = 1`) and residual
`D = ((1−k)V'fB − C)/V + B'f + Bg` (`g` from `(f/y)' = g/y`); cleared over `Vᵏy` the step is the pure
`F[θ]` identity `(1−k)V'fB − C + V(B'f + Bg) = V·D`. -/

namespace CPolyG

variable {α : Type*} [CField α]

/-- Case-1 cofactor `radCase1Cofactor k V Df f C = B`: the degree-`< deg V` polynomial solving
`(1−k)·V'·f·B ≡ C (mod V)` via `cdiophantineGWf ((1−k)·V'·f) V C`. `Df = V'` is passed in. -/
def radCase1Cofactor (k : ℕ) (V Df f C : CPolyG α) : CPolyG α :=
  let oneMinusK := cnegG [cnatCastG (k - 1)]                    -- the constant `(1 − k) = −(k−1)`
  let coeff := cmulG oneMinusK (cmulG Df f)                     -- `(1−k)·V'·f`
  (cdiophantineGWf coeff V C).1

/-- Case-1 residual `radCase1Residual k V Df f g B C Bder = D`: the lowered-`k` numerator
`D = ((1−k)V'fB − C)/V + B'f + Bg`. `Df = V'`, `Bder = B'`, `g` from `(f/y)' = g/y` passed in; division
by `V` is `cdivWf`. -/
def radCase1Residual (k : ℕ) (V Df f g B C Bder : CPolyG α) : CPolyG α :=
  let oneMinusK := cnegG [cnatCastG (k - 1)]
  let topNum := csubG (cmulG oneMinusK (cmulG Df (cmulG f B))) C  -- `(1−k)V'fB − C`
  let quotient := cdivWf topNum V                                 -- `((1−k)V'fB − C)/V`
  caddG quotient (caddG (cmulG Bder f) (cmulG B g))               -- `… + B'f + Bg`

/-! ### Case 2 rational-part reduction (`θ' = 1`, `n = 2`)

The piece `C/(Wᵏy)` where `W` is a squarefree factor of the radicand `f` (not coprime to `f`). With
`h = f/W`, `radDeriv(Bf/(Wᵏy)) = (B·(½−k)·W'·h)/(Wᵏy) + (B'h + ½Bh')/(W^{k−1}y)`, so subtracting
`C/(Wᵏy)` leaves `D/(W^{k−1}y)` provided `B·(½−k)·W'·h ≡ C (mod W)`; residual
`D = (B·(½−k)W'h − C)/W + B'h + ½Bh'`, cleared identity `B·(½−k)W'h − C + W·(B'h + ½Bh') = W·D`. -/

/-- Case-2 cofactor (`n = 2`) `radCase2Cofactor k W h C = B`: the degree-`< deg W` polynomial solving
`B·(½−k)·W'·h ≡ C (mod W)` via `cdiophantineGWf ((½−k)W'h) W C`. `h = f/W`, `W'` is `cderivG W`. -/
def radCase2Cofactor (k : ℕ) (W h C : CPolyG α) : CPolyG α :=
  let half : CPolyG α := [CField.div CField.one (cnatCastG 2)]              -- `½`
  let coef := cmulG (csubG half [cnatCastG k]) (cmulG (cderivG W) h)        -- `(½ − k)·W'·h`
  (cdiophantineGWf coef W C).1

/-- Case-2 residual (`n = 2`) `radCase2Residual k W h C B = D`: the lowered-`k` numerator
`D = (B·(½−k)W'h − C)/W + B'h + ½Bh'`; `B'` is `cderivG B`, `h'` is `cderivG h`, division by `W` is
`cdivWf`. -/
def radCase2Residual (k : ℕ) (W h C B : CPolyG α) : CPolyG α :=
  let half : CPolyG α := [CField.div CField.one (cnatCastG 2)]              -- `½`
  let coef := cmulG (csubG half [cnatCastG k]) (cmulG (cderivG W) h)        -- `(½ − k)·W'·h`
  let topNum := csubG (cmulG B coef) C                                      -- `B·(½−k)W'h − C`
  let quotient := cdivWf topNum W                                           -- `/W`
  caddG quotient (caddG (cmulG (cderivG B) h)                              -- `+ B'h`
    (cmulG half (cmulG B (cderivG h))))                                     -- `+ ½Bh'`

/-! ### Case 3 rational-part reduction (`θ' = 1`)

The leftover `C/y`, lowering `deg C` rather than a denominator. With `(Bf/y)' = (B'f + Bg)/y`, taking
`B = b·θ^{j+1}` a single constant-coefficient monomial (`j+1 = deg C − deg f + 1`), the leading relation
gives `b = lcf(C) / ((j+1) + lcf(g))` and residual `D = B'f + Bg − C` with `deg D < deg C`. -/

/-- Case-3 leading-coefficient cofactor `radCase3Cofactor f g C = B`: the constant-coefficient monomial
`B = b·θ^{j+1}` (`j+1 = deg C − deg f + 1`) with `b = lcf(C) / ((j+1) + lcf(g))`, cancelling the leading
term of `C` in the `C/y` degree-lowering (`[]` when `deg C < deg f`). -/
def radCase3Cofactor (f g C : CPolyG α) : CPolyG α :=
  let dC := cdegG C
  let dF := cdegG f
  if cisZeroG C || dC < dF then []
  else
    let jp1 := dC - dF + 1                                         -- `j + 1 = deg C − deg f + 1`
    let denom := CField.add (cnatCastG jp1) (cleadG g)            -- `(j+1) + lcf(g)`
    let b := CField.div (cleadG C) denom                          -- `b = lcf(C)/((j+1)+lcf(g))`
    cshiftG jp1 [b]                                                -- `b·θ^{j+1}`

/-- Case-3 residual `radCase3Residual f g B C Bder = D`: the lowered-degree numerator `D = B'f + Bg − C`
of the `C/y` step. `Bder = B'`, `g` from `(f/y)' = g/y` passed in; with `B` from `radCase3Cofactor`,
`deg D < deg C`. -/
def radCase3Residual (f g B C Bder : CPolyG α) : CPolyG α :=
  csubG (caddG (cmulG Bder f) (cmulG B g)) C                       -- `B'f + Bg − C`

/-! ### `θ = log v` rational-part reduction

For `θ = log v` (`θ' = v'/v ∈ F`) the `C/y` degree-lowering is shaped as Case 3, but the leading-coefficient
bracket becomes `(j+1)·θ' + lcf(g)`, so `b = lcf(C)/((j+1)θ' + lcf(g))` (`radCase3CofactorGen` takes `θ'`
as `Dt`), and `B'` is the full monomial derivative `cmonomialDeriv [θ'] B`. Setting `Dt = 1` recovers
Case 3. -/

/-- Generalized Case-3 cofactor `radCase3CofactorGen Dt f g C = B`: the monomial `B = b·θ^{j+1}` with
`b = lcf(C) / ((j+1)·θ' + lcf(g))` for any `θ` of derivative `Dt = θ'` (`[]` when `deg C < deg f`);
`Dt = 1` recovers Case 3. -/
def radCase3CofactorGen (Dt : α) (f g C : CPolyG α) : CPolyG α :=
  let dC := cdegG C
  let dF := cdegG f
  if cisZeroG C || dC < dF then []
  else
    let jp1 := dC - dF + 1                                         -- `j + 1 = deg C − deg f + 1`
    let denom := CField.add (CField.mul (cnatCastG jp1) Dt) (cleadG g)  -- `(j+1)·θ' + lcf(g)`
    let b := CField.div (cleadG C) denom                          -- `b = lcf(C)/((j+1)θ' + lcf(g))`
    cshiftG jp1 [b]                                                -- `b·θ^{j+1}`

/-! ### `θ = exp v` rational-part reduction

For `θ = exp v`, `θ` divides its own derivative (`θ' = v'·θ`); the new piece is `C/(θᵏy)` with
`(Bf/(θᵏy))' = (B'f + Bg − k·v'·B·f)/(θᵏy)`. Matching constant (θ-degree-`0`) terms
`c₀ = b₀g₀ − k·v'·b₀·f₀` on the constant-`b₀` slice gives `b₀ = c₀/(g₀ − k·v'·f₀)`, residual
`D = ((B'f + Bg − kv'Bf) − C)/θ`, cleared identity `(B'f + Bg − kv'Bf) − C = θ·D`. -/

/-- `radConstCoeff p`: the `θ⁰` (head) coefficient of `p` (`CField.zero` for the empty list), the
residue of `p` modulo `θ`. -/
def radConstCoeff (p : CPolyG α) : α := (p : List α).headD CField.zero

/-- `θ = exp v` `C/(θᵏy)` cofactor `radExpCofactor k vder f g C = B`: the constant `B = [b₀]` with
`b₀ = c₀ / (g₀ − k·v'·f₀)` (`f₀, g₀, c₀` the `θ⁰`-coefficients of `f, g, C`, `vder = v'`), solving the
constant-term match `c₀ = b₀g₀ − k·v'·b₀·f₀`. -/
def radExpCofactor (k : ℕ) (vder : α) (f g C : CPolyG α) : CPolyG α :=
  let f0 := radConstCoeff f
  let g0 := radConstCoeff g
  let c0 := radConstCoeff C
  let denom := CField.sub g0 (CField.mul (CField.mul (cnatCastG k) vder) f0)  -- `g₀ − k·v'·f₀`
  [CField.div c0 denom]                                                       -- `[b₀]`

/-- `θ = exp v` `C/(θᵏy)` residual `radExpResidual k vder f g B C Bder = D`: the lowered-`k` numerator
`D = ((B'f + Bg − k·v'·B·f) − C)/θ`. `vder = v'`, `Bder = B'`, `g` passed in; division by `θ` is
`cdivWf _ [0,1]`. -/
def radExpResidual (k : ℕ) (vder : α) (f g B C Bder : CPolyG α) : CPolyG α :=
  let kvBf := cmulG [CField.mul (cnatCastG k) vder] (cmulG B f)    -- `k·v'·B·f`
  let num := csubG (csubG (caddG (cmulG Bder f) (cmulG B g)) kvBf) C  -- `B'f + Bg − kv'Bf − C`
  cdivWf num [CField.zero, CField.one]                             -- `… / θ`

end CPolyG

end DeepWiki.SymbolicIntegration
