import DeepWiki.SymbolicIntegration.Computable.Tower.Field
import DeepWiki.SymbolicIntegration.Computable.Tower.Deriv
import DeepWiki.SymbolicIntegration.Computable.GenericBezout
import DeepWiki.SymbolicIntegration.Computable.MonomialDeriv
import DeepWiki.SymbolicIntegration.Computable.FuelFreeDiophantine

/-! # Algebraic-function integration: simple radical extensions

Integration over a simple radical extension `F(y)` with `yⁿ = f ∈ F` (`F` a char-0 differential field),
built on the computable tower engine. The carrier `RadExt α n f` represents `α[y]/(yⁿ − f)` as a
length-`n` coefficient list, with componentwise `radAdd`, `radMul` (poly-multiply then reduce `yⁿ → f`),
and the diagonal derivation `radDeriv` (`y' = (f'/(nf))·y`). The rational-part reductions cover the
per-`y`-power projection `Tᵢ` decoupling and the partial-fraction pieces `C/(Vᵏy)`, `C/(Wᵏy)`, `C/y`
across the level kinds `θ' = 1`, `θ = log v`, `θ = exp v`, each solved via `cdiophantineGWf` and validated
by cleared `cisZeroG` identities. -/

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

/-! ### The carrier validates: `y = √(x³+1)` over `ℚ(x)`

`F = QFunNZG ℚ ≅ ℚ(x)`, `n = 2`, `f = x³+1`: checks `y·y = f` and `D(y) = (3x²/(2(x³+1)))·y`. -/

open RadElem

/-- A `ℚ(x)` value (`QFunNZG ℚ`) from a numerator `CPoly = List ℚ` over denominator `1`. -/
def qxOfNum (num : CPolyG ℚ) : QFunNZG ℚ :=
  ⟨(num, [CField.one]), QFunNZG.cisZeroG_one_singleton⟩

/-- The radicand `f = x³ + 1 ∈ ℚ(x)` (numerator `[1,0,0,1]` = `1 + x³`). -/
def radicandX3p1 : QFunNZG ℚ := qxOfNum [1, 0, 0, 1]

/-- `y·y = f` over `ℚ(x)`: `y = √(x³+1)` squared in `(QFunNZG ℚ)[y]/(y² − (x³+1))` folds to `f = x³+1`. -/
theorem radGen_sq_eq_radicand :
    radIsZero (radSub (radMul 2 radicandX3p1 (radGen : RadElem (QFunNZG ℚ)) radGen) [radicandX3p1])
      = true := by native_decide

/-- The ℚ(x) value `3x² = (x³+1)' ∈ ℚ(x)` (numerator `[0,0,3]`), the derivative of the radicand. -/
def radicandDeriv : QFunNZG ℚ := qxOfNum [0, 0, 3]

/-- The diagonal multiplier `ℓ = f'/(2f) = 3x²/(2(x³+1)) ∈ ℚ(x)` for `D(y) = ℓ·y`. -/
def radicandLogDer : QFunNZG ℚ := logDerRadicand 2 radicandX3p1

/-- `D(y) = (3x²/(2(x³+1)))·y` over `ℚ(x)`: the diagonal derivation of `y = √(x³+1)` is `ℓ·y`,
`ℓ = f'/(2f) = 3x²/(2(x³+1))`. -/
theorem radDeriv_radGen_eq :
    radIsZero (radSub (radDeriv 2 radicandX3p1 (radGen : RadElem (QFunNZG ℚ)))
        [CField.zero, radicandLogDer]) = true := by native_decide

/-- `D(1) = 0` over `ℚ(x)`: the radical derivation annihilates the constant `1`. -/
theorem radDeriv_radOne_eq_zero :
    radIsZero (radDeriv 2 radicandX3p1 (radOne : RadElem (QFunNZG ℚ))) = true := by native_decide

/-- Ring sanity `y·1 = y` over `ℚ(x)`: `radMul` with `radOne` is the identity. -/
theorem radMul_radOne_eq :
    radIsZero (radSub (radMul 2 radicandX3p1 (radGen : RadElem (QFunNZG ℚ)) radOne) radGen)
      = true := by native_decide

/-- Ring sanity `(1+y)·(1+y) = 1 + 2y + f` over `ℚ(x)`: `1 + 2y + y²` folds `y² → f = x³+1`. -/
theorem radMul_onePlusGen_sq :
    radIsZero (radSub
        (radMul 2 radicandX3p1 [CField.one, CField.one] [(CField.one : QFunNZG ℚ), CField.one])
        [CField.add CField.one radicandX3p1, CField.add CField.one CField.one]) = true := by
  native_decide

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

/-! #### `Tᵢ` decoupling validates over `√(x³+1)`

`Tᵢ(yʲ) = yʲ·[i=j]`, `Tᵢ ∘ D = D ∘ Tᵢ`, and the `∫(g₀+g₁y)` split, on `α = ℚ(x)`, `n = 2`, `f = x³+1`. -/

/-- `T₁(y) = y`: the projection onto the `y`-power fixes `y = √(x³+1)`. -/
theorem radProj_one_radGen :
    radIsZero (radSub (radProj 1 (radGen : RadElem (QFunNZG ℚ))) radGen) = true := by native_decide

/-- `T₀(y) = 0`: the projection onto the constant power kills `y`. -/
theorem radProj_zero_radGen :
    radIsZero (radProj 0 (radGen : RadElem (QFunNZG ℚ))) = true := by native_decide

/-- `T₁(1) = 0`: the projection onto the `y`-power kills the constant `1`. -/
theorem radProj_one_radOne :
    radIsZero (radProj 1 (radOne : RadElem (QFunNZG ℚ))) = true := by native_decide

/-- A mixed element `g = (x³+1) + 3x²·y ∈ ℚ(x)[y]/(y²−(x³+1))` (`g₀ = f`, `g₁ = f'`), test integrand for
the `Tᵢ` decoupling. -/
def mixedElem : RadElem (QFunNZG ℚ) := [radicandX3p1, radicandDeriv]

/-- `T₁ ∘ D = D ∘ T₁` on the mixed element: `T₁(D g) = D(T₁ g)` for `g = (x³+1) + 3x²·y`. -/
theorem radProj_one_radDeriv_comm :
    radIsZero (radSub
        (radProj 1 (radDeriv 2 radicandX3p1 mixedElem))
        (radDeriv 2 radicandX3p1 (radProj 1 mixedElem))) = true := by native_decide

/-- `T₀ ∘ D = D ∘ T₀` on the mixed element: `T₀(D g) = D(T₀ g)`. -/
theorem radProj_zero_radDeriv_comm :
    radIsZero (radSub
        (radProj 0 (radDeriv 2 radicandX3p1 mixedElem))
        (radDeriv 2 radicandX3p1 (radProj 0 mixedElem))) = true := by native_decide

/-- The `∫(g₀+g₁y)` split: `D(g) = D(T₀ g) + D(T₁ g)` decomposes additively into `1`- and `y`-components
sharing no power of `y`, so `∫g` reduces to `∫g₀ + ∫g₁y` independently. -/
theorem radDeriv_decouples :
    radIsZero (radSub
        (radDeriv 2 radicandX3p1 mixedElem)
        (radAdd (radDeriv 2 radicandX3p1 (radProj 0 mixedElem))
          (radDeriv 2 radicandX3p1 (radProj 1 mixedElem)))) = true := by native_decide

/-- The `y`-component of `D(g)` stays in the `y`-component: `D(T₁ g) = T₁(D(T₁ g))`, so the rational
part of `∫g₁y` is `v₁·y`. -/
theorem radDeriv_projOne_stays :
    radIsZero (radSub
        (radDeriv 2 radicandX3p1 (radProj 1 mixedElem))
        (radProj 1 (radDeriv 2 radicandX3p1 (radProj 1 mixedElem)))) = true := by native_decide

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

/-! #### Case 1 validates: `∫ C/(V²y)` with `y = √x`, `V = x−1`

Radicand `y² = f = x`, `V = x − 1`, `k = 2`, `C = 1` (integrand `1/((x−1)²√x)`): the congruence gives
`B = −1` and residual `D = 1/2` (constant), dropping the multiplicity `2 → 1`; `g = f'/2 = 1/2`. -/

open CPolyG

/-- Case-1 example radicand `f = x` (`y² = x`, `y = √x`), as a `ℚ[x]` polynomial `[0, 1]`. -/
def case1F : CPolyG ℚ := [0, 1]

/-- Case-1 example squarefree denominator factor `V = x − 1` (coprime to `f = x`), `[−1, 1]`. -/
def case1V : CPolyG ℚ := [-1, 1]

/-- Case-1 example numerator `C = 1`, `[1]`. -/
def case1C : CPolyG ℚ := [1]

/-- `V' = (x−1)' = 1` over `ℚ[x]` (`cderivG`, `θ' = 1`, ℚ-constant coefficients). -/
def case1Vder : CPolyG ℚ := cderivG case1V

/-- `g = ((n−1)/n)·f' = (1/2)·1 = 1/2` for `n = 2`, `f = x` squarefree (`(f/y)' = g/y`), `[1/2]`. -/
def case1G : CPolyG ℚ := cscaleG (1/2 : ℚ) (cderivG case1F)

/-- The solved Case-1 cofactor `B` for `−x·B ≡ 1 (mod x−1)` — expected `B = −1`. -/
def case1B : CPolyG ℚ := radCase1Cofactor 2 case1V case1Vder case1F case1C

/-- The Case-1 residual `D` — expected the constant `1/2`. -/
def case1D : CPolyG ℚ :=
  radCase1Residual 2 case1V case1Vder case1F case1G case1B case1C (cderivG case1B)

/-- The cofactor is `B = −1`: `−x·B ≡ 1 (mod x−1)` gives `B = −1`. -/
theorem case1_cofactor_eq :
    cisZeroG (csubG case1B [(-1 : ℚ)]) = true := by native_decide

/-- The Case-1 congruence `(1−k)V'fB − C ≡ 0 (mod V)` holds: `cmodWf ((1−k)V'fB − C) V` vanishes. -/
theorem case1_congruence :
    cisZeroG (cmodWf
      (csubG (cmulG (cnegG [cnatCastG 1]) (cmulG case1Vder (cmulG case1F case1B))) case1C)
      case1V) = true := by native_decide

/-- The Case-1 cleared identity `(1−k)V'fB − C + V·(B'f + Bg) = V·D` in `ℚ[x]` (`B = −1`, `D = 1/2`). -/
theorem case1_cleared_identity :
    cisZeroG (csubG
      (caddG
        (csubG (cmulG (cnegG [cnatCastG 1]) (cmulG case1Vder (cmulG case1F case1B))) case1C)
        (cmulG case1V (caddG (cmulG (cderivG case1B) case1F) (cmulG case1B case1G))))
      (cmulG case1V case1D)) = true := by native_decide

/-- The residual `D = 1/2` has degree `< deg V`, so the multiplicity dropped `k = 2 → 1`. -/
theorem case1_residual_eq :
    cisZeroG (csubG case1D [(1/2 : ℚ)]) = true := by native_decide

/-! #### Case 2 validates: `∫ C/(W²y)` with `y = √(x³−x)`, `W = x`

Radicand `y² = f = x³ − x`, squarefree factor `W = x`, `h = f/W = x² − 1`, `k = 2`, `C = 1` (integrand
`1/(x²√(x³−x))`): the congruence gives `B = 2/3` and residual `D = −x/3`, dropping the multiplicity
`k = 2 → 1`. -/

/-- Case-2 example radicand `f = x³ − x = x(x−1)(x+1)` (`y² = f`, squarefree), `ℚ[x]` `[0,−1,0,1]`. -/
def case2F : CPolyG ℚ := [0, -1, 0, 1]

/-- Case-2 example squarefree denominator factor `W = x` (a factor of `f`, a branch place), `[0, 1]`. -/
def case2W : CPolyG ℚ := [0, 1]

/-- Case-2 example cofactor `h = f/W = x² − 1`, `[−1, 0, 1]`. -/
def case2H : CPolyG ℚ := [-1, 0, 1]

/-- Case-2 example numerator `C = 1`, `[1]`. -/
def case2C : CPolyG ℚ := [1]

/-- `W' = x' = 1` over `ℚ[x]` (`cderivG`, `θ' = 1`). -/
def case2Wder : CPolyG ℚ := cderivG case2W

/-- The solved Case-2 cofactor `B` for `B·(½−2)·W'·h ≡ 1 (mod x)` — expected `B = 2/3`. -/
def case2B : CPolyG ℚ := radCase2Cofactor 2 case2W case2H case2C

/-- The Case-2 residual `D` — expected `−x/3` (multiplicity dropped `k = 2 → 1`). -/
def case2D : CPolyG ℚ :=
  radCase2Residual 2 case2W case2H case2C case2B

/-- The cofactor is `B = 2/3`: `B·(½−2)·W'·h ≡ 1 (mod x)` gives `B = 2/3`. -/
theorem case2_cofactor_eq :
    cisZeroG (csubG case2B [(2/3 : ℚ)]) = true := by native_decide

/-- The Case-2 congruence `B·(½−k)·W'·h − C ≡ 0 (mod W)` holds: `cmodWf (B·(½−k)W'h − C) W` vanishes. -/
theorem case2_congruence :
    cisZeroG (cmodWf
      (csubG (cmulG case2B
        (cmulG (csubG [CField.div CField.one (cnatCastG 2)] [cnatCastG 2])
          (cmulG case2Wder case2H))) case2C)
      case2W) = true := by native_decide

/-- The Case-2 cleared identity `B·(½−k)W'h − C + W·(B'h + ½Bh') = W·D` in `ℚ[x]` (`B = 2/3`, `D = −x/3`). -/
theorem case2_cleared_identity :
    cisZeroG (csubG
      (caddG
        (csubG (cmulG case2B
          (cmulG (csubG [CField.div CField.one (cnatCastG 2)] [cnatCastG 2])
            (cmulG case2Wder case2H))) case2C)
        (cmulG case2W
          (caddG (cmulG (cderivG case2B) case2H)
            (cmulG [CField.div CField.one (cnatCastG 2)] (cmulG case2B (cderivG case2H))))))
      (cmulG case2W case2D)) = true := by native_decide

/-- The residual `D = −x/3`, so the Case-2 step lowered the multiplicity of `W = x` from `k = 2` to `1`. -/
theorem case2_residual_eq :
    cisZeroG (csubG case2D [(0 : ℚ), -1/3]) = true := by native_decide

/-! #### Case 3 validates: degree-lowering `∫ (x²+x)/√x` with `y = √x`

Radicand `y² = f = x`, `g = 1/2`, `C = x² + x`: the leading-coefficient solve gives `B = (2/5)x²` and
residual `D = −x` of degree `1 < deg C = 2`, lowering `deg C` by one. -/

/-- Case-3 example radicand `f = x` (`y² = x`, `m = deg f = 1`), as a `ℚ[x]` polynomial `[0, 1]`. -/
def case3F : CPolyG ℚ := [0, 1]

/-- `g = ((n−1)/n)·f' = (1/2)·1 = 1/2` for `n = 2`, `f = x` (`(f/y)' = g/y`, `lcf(g) = 1/2`), `[1/2]`. -/
def case3G : CPolyG ℚ := cscaleG (1/2 : ℚ) (cderivG case3F)

/-- Case-3 example numerator `C = x² + x` (`deg C = 2 ≥ m = 1`), `[0, 1, 1]`. -/
def case3C : CPolyG ℚ := [0, 1, 1]

/-- The solved Case-3 leading-coefficient cofactor `B = (2/5)x²` (`j+1 = 2`, `b = 1/(2+1/2) = 2/5`). -/
def case3B : CPolyG ℚ := radCase3Cofactor case3F case3G case3C

/-- The Case-3 residual `D = B'f + Bg − C` — expected `−x` (degree `1 < deg C = 2`). -/
def case3D : CPolyG ℚ := radCase3Residual case3F case3G case3B case3C (cderivG case3B)

/-- The cofactor is `B = (2/5)x²`: `b = lcf(C)/((j+1)+lcf(g)) = 1/(2+1/2) = 2/5` at degree `j+1 = 2`. -/
theorem case3_cofactor_eq :
    cisZeroG (csubG case3B [(0 : ℚ), 0, 2/5]) = true := by native_decide

/-- The Case-3 cleared identity `B'f + Bg − C = D` in `ℚ[x]` (`B = (2/5)x²`, `D = −x`). -/
theorem case3_cleared_identity :
    cisZeroG (csubG
      (csubG (caddG (cmulG (cderivG case3B) case3F) (cmulG case3B case3G)) case3C)
      case3D) = true := by native_decide

/-- The residual `D = −x` has degree `1`, strictly below `deg C = 2`. -/
theorem case3_residual_eq :
    cisZeroG (csubG case3D [(0 : ℚ), -1]) = true := by native_decide

/-- The Case-3 step strictly lowers `deg C`: `deg D = 1 < deg C = 2`. -/
theorem case3_degree_drop : cdegG case3D < cdegG case3C := by native_decide

/-! #### `θ = log v` validates: degree-lowering `∫ C/y` over `ℚ(x)[log x]`, `y = √(log x)`

A 2-level tower: base `ℚ(x)`, monomial `θ = log x` (`θ' = 1/x`), radicand `y² = f = log x`, `g = 1/(2x)`.
For `C` with leading term `(5/(2x))θ²` the bracket `(j+1)·θ' + lcf(g) = 5/(2x)` gives the constant `b = 1`,
`B = θ²`, and residual `D = −θ`, dropping `deg_θ C` by one. -/

/-- A `ℚ(x)` value `num/den` (`QFunNZG ℚ`) from a numerator and a **nonzero** denominator `CPolyG ℚ`;
the proof obligation `cisZeroG den = false` is discharged by `decide` at each call site. -/
def qxOfFrac (num den : CPolyG ℚ) (h : CPolyG.cisZeroG den = false) : QFunNZG ℚ := ⟨(num, den), h⟩

/-- `θ' = (log x)' = v'/v = 1/x ∈ ℚ(x)` (numerator `[1]`, denominator `[0,1] = x`), the derivative of
the monomial `θ = log x`. -/
def logDt : QFunNZG ℚ := qxOfFrac [1] [0, 1] (by decide)

/-- The ℚ(x) leading coefficient `lcf(g) = g = 1/(2x)` for `f = θ`, `g = (1/2)f'/f·f = 1/(2x)`
(numerator `[1]`, denominator `[0,2] = 2x`). -/
def logGlead : QFunNZG ℚ := qxOfFrac [1] [0, 2] (by decide)

/-- The radicand `f = θ = log x ∈ ℚ(x)[θ]` (`y² = log x`), the `θ`-polynomial `[0, 1]`. -/
def logF : CPolyG (QFunNZG ℚ) := [CField.zero, CField.one]

/-- `g = 1/(2x)` as a degree-`0`-in-θ element of `ℚ(x)[θ]` (`(f/y)' = g/y`), `[1/(2x)]`. -/
def logG : CPolyG (QFunNZG ℚ) := [logGlead]

/-- The numerator `C = (5/(2x))θ² + θ ∈ ℚ(x)[θ]` (`deg_θ C = 2 ≥ m`), with leading coefficient
`5/(2x) = (j+1)θ' + lcf(g)` chosen so the constant `b = 1` solves eq. 5. -/
def logC : CPolyG (QFunNZG ℚ) := [CField.zero, CField.one, qxOfFrac [5] [0, 2] (by decide)]

/-- The `θ`-derivative as a polynomial `[θ'] = [1/x] ∈ ℚ(x)[θ]`, the `Dt` for `cmonomialDeriv`. -/
def logDtPoly : CPolyG (QFunNZG ℚ) := [logDt]

/-- The solved `θ = log v` leading-coefficient cofactor `B = b·θ² = 1·θ²` (`b = lcf(C)/bracket =
(5/(2x))/(5/(2x)) = 1`, a constant). -/
def logB : CPolyG (QFunNZG ℚ) := radCase3CofactorGen logDt logF logG logC

/-- The `θ = log v` residual `D = B'f + Bg − C`, with `B' = cmonomialDeriv [θ'] B` the full log-monomial
derivative — expected `−θ` (degree `1 < deg_θ C = 2`). -/
def logD : CPolyG (QFunNZG ℚ) :=
  radCase3Residual logF logG logB logC (cmonomialDeriv logDtPoly logB)

/-- The `log` cofactor is the constant monomial `B = θ²`: `b = (5/(2x))/((2)(1/x) + 1/(2x)) = 1` at
degree `j+1 = 2`. -/
theorem logCase_cofactor_eq :
    cisZeroG (csubG logB [CField.zero, CField.zero, (CField.one : QFunNZG ℚ)]) = true := by
  native_decide

/-- The `θ = log v` cleared identity `B'f + Bg − C = D` in `ℚ(x)[log x]` (`B = θ²`, `B' = cmonomialDeriv
[1/x] B`, `D = −θ`). -/
theorem logCase_cleared_identity :
    cisZeroG (csubG
      (csubG (caddG (cmulG (cmonomialDeriv logDtPoly logB) logF) (cmulG logB logG)) logC)
      logD) = true := by native_decide

/-- The `log` residual `D = −θ` has `θ`-degree `1`, strictly below `deg_θ C = 2`. -/
theorem logCase_residual_eq :
    cisZeroG (csubG logD [CField.zero, (CField.neg CField.one : QFunNZG ℚ)]) = true := by native_decide

/-- The `θ = log v` step strictly lowers `deg_θ C`: `deg D = 1 < deg C = 2` over `ℚ(x)[log x]`. -/
theorem logCase_degree_drop : cdegG logD < cdegG logC := by native_decide

/-! #### `θ = exp v` validates: `∫ C/(θy)` over `ℚ(x)[eˣ]`, `y = √(eˣ+1)`

A 2-level exponential tower: base `ℚ(x)`, monomial `θ = exp x` (`θ' = θ`), radicand `y² = f = eˣ + 1`,
`g = (1/2)θ`. The `C/(θy)` step (`k = 1`, `C = θ + 1`): the constant-term match gives `b₀ = −1`,
`B = [−1]`, residual `D = −1/2`, dropping `k = 1 → 0`. -/

/-- The radicand `f = θ + 1 = eˣ + 1 ∈ ℚ(x)[θ]` (`y² = eˣ + 1`, `θ ∤ f`, `f₀ = 1`), `[1, 1]`. -/
def expF : CPolyG (QFunNZG ℚ) := [CField.one, CField.one]

/-- `g = (1/2)θ ∈ ℚ(x)[θ]` for `f = θ+1`, `θ = exp x` (`(f/y)' = g/y`, `g₀ = 0`), `[0, 1/2]`. -/
def expG : CPolyG (QFunNZG ℚ) := [CField.zero, qxOfNum [1/2]]

/-- The numerator `C = θ + 1 ∈ ℚ(x)[θ]` (`c₀ = 1`), `[1, 1]`. -/
def expC : CPolyG (QFunNZG ℚ) := [CField.one, CField.one]

/-- `v' = (x)' = 1 ∈ ℚ(x)` for `θ = exp x` (`v = x`), the `CField.one` of `QFunNZG ℚ`. -/
def expVder : QFunNZG ℚ := CField.one

/-- `θ' = v'·θ = θ` as the `Dt` polynomial `[0, 1] ∈ ℚ(x)[θ]` for `cmonomialDeriv` (`θ = exp x` is a
factor of its own derivative). -/
def expDtPoly : CPolyG (QFunNZG ℚ) := [CField.zero, CField.one]

/-- The solved `θ = exp v` `C/(θy)` cofactor `B = [b₀] = [−1]` (`b₀ = c₀/(g₀ − kv'f₀) = 1/(0−1) = −1`,
a constant). -/
def expB : CPolyG (QFunNZG ℚ) := radExpCofactor 1 expVder expF expG expC

/-- The `θ = exp v` `C/(θy)` residual `D = ((B'f + Bg − kv'Bf) − C)/θ`, `B' = cmonomialDeriv [θ] B` —
expected `−1/2` (the multiplicity dropped `k = 1 → 0`). -/
def expD : CPolyG (QFunNZG ℚ) :=
  radExpResidual 1 expVder expF expG expB expC (cmonomialDeriv expDtPoly expB)

/-- The `exp` cofactor is the constant `B = [−1]`: `b₀ = 1/(0 − 1·1·1) = −1` over `ℚ(x)[eˣ]`. -/
theorem expCase_cofactor_eq :
    cisZeroG (csubG expB [(CField.neg CField.one : QFunNZG ℚ)]) = true := by native_decide

/-- The `θ = exp v` constant-term congruence `(B'f + Bg − kv'Bf) − C ≡ 0 (mod θ)`: the numerator `(−1/2)θ`
is divisible by `θ`. -/
theorem expCase_congruence :
    cisZeroG (cmodWf
      (csubG (csubG (caddG (cmulG (cmonomialDeriv expDtPoly expB) expF) (cmulG expB expG))
          (cmulG [CField.mul (cnatCastG 1) expVder] (cmulG expB expF))) expC)
      [CField.zero, CField.one]) = true := by native_decide

/-- The `θ = exp v` cleared identity `(B'f + Bg − k·v'·B·f) − C = θ·D` in `ℚ(x)[eˣ]` (`B = [−1]`,
`D = [−1/2]`). -/
theorem expCase_cleared_identity :
    cisZeroG (csubG
      (csubG (csubG (caddG (cmulG (cmonomialDeriv expDtPoly expB) expF) (cmulG expB expG))
          (cmulG [CField.mul (cnatCastG 1) expVder] (cmulG expB expF))) expC)
      (cmulG [CField.zero, CField.one] expD)) = true := by native_decide

/-- The `exp` residual `D = −1/2` (a `θ`-constant): the `C/(θᵏy)` step lowered the `θ`-power multiplicity
`k = 1 → 0`. -/
theorem expCase_residual_eq :
    cisZeroG (csubG expD [qxOfNum [-1/2]]) = true := by native_decide

/-! ### `#print axioms` -/

-- Carrier: `y·y = f` and the diagonal `D(y) = (f'/(2f))·y` over ℚ(x):
#print axioms radGen_sq_eq_radicand
#print axioms radDeriv_radGen_eq

-- `Tᵢ` decoupling: the derivation-commutation and the `∫(g₀+g₁y)` split:
#print axioms radProj_one_radDeriv_comm
#print axioms radDeriv_decouples

-- Case-1 rational reduction: the cofactor congruence and the cleared Hermite identity:
#print axioms case1_congruence
#print axioms case1_cleared_identity

-- Case-2 reduction (W ∣ f): the cofactor congruence and the cleared identity:
#print axioms case2_congruence
#print axioms case2_cleared_identity

-- Case-3 degree-lowering (C/y, θ'=1): the cleared identity and the strict degree drop:
#print axioms case3_cleared_identity
#print axioms case3_degree_drop

-- `θ = log v` degree-lowering (2-level tower): the cleared identity and the strict degree drop:
#print axioms logCase_cleared_identity
#print axioms logCase_degree_drop

-- `θ = exp v` `C/(θᵏy)` reduction (exponential tower): the constant-term congruence and cleared identity:
#print axioms expCase_congruence
#print axioms expCase_cleared_identity

end DeepWiki.SymbolicIntegration
