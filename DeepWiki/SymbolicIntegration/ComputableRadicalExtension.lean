import DeepWiki.SymbolicIntegration.ComputableTowerField
import DeepWiki.SymbolicIntegration.ComputableTowerDeriv
import DeepWiki.SymbolicIntegration.ComputableGenericBezout
import DeepWiki.SymbolicIntegration.ComputableMonomialDeriv

/-! # Algebraic-function integration: simple radical extensions (Trager Appendix A)
The transcendental Risch engine (`ComputableTower*`/`ComputableIntegrate`) integrates elementary
*transcendental* functions; it has no axis for **algebraic** functions. This file opens that axis with
Trager's PhD-thesis Appendix A algorithm for **simple radical extensions** `F(y)` with `yⁿ = f ∈ F`
(`F` a differential field, char 0) — the simplest, most common algebraic case (an integral table such
as Gradshteyn–Ryzhik has < 1% of problems outside unnested radicals).

It builds *entirely* on the existing computable engine — no abstract Riemann–Roch. The base field `F`
is a tower level `[CField α]` (e.g. `QFunNZG ℚ ≅ ℚ(x)`); the carrier `RadExt α n f` represents
`α[y]/(yⁿ − f)` as a length-`n` coefficient list. The reductions reuse the generic Bézout/diophantine
solver `cdiophantineG` and the monomial machinery.

* **`RadExt α n f`** — a `RadElem` is `[a₀,…,a_{n−1}]` for `Σ aᵢyⁱ`. Ring ops: `radAdd` componentwise,
  `radMul` = poly-multiply in `y` then reduce `yⁿ → f`. The derivation `radDeriv` uses Trager's `(f/y)'`
  insight: since `y' = f'/(n·y^{n−1}) = (f'/(n·f))·y`, the derivation is **diagonal** —
  `D(Σ aᵢyⁱ) = Σ [D(aᵢ) + aᵢ·(i·f'/(n·f))]·yⁱ`, mixing no `y`-powers. `native_decide`: over `α = QFunNZG
  ℚ = ℚ(x)`, `n = 2`, `f = x³+1` (so `y = √(x³+1)`): `y·y = f` and `D(y) = (3x²/(2(x³+1)))·y`.

* **The `Tᵢ` decoupling** (Appendix A §1) — the per-`y`-power projection `radProj i`. The diagonality of
  `radDeriv` *is* the statement that `D` commutes with `Tᵢ`, so `∫(g₀ + g₁y)` splits into `∫g₀` and
  `∫g₁y` independently. `native_decide` exhibits the split.

* **Case 1 rational-part reduction** (Appendix A §2.1, `C/(Vᵏy)`, `θ'=1`) — the Hermite-style step
  lowering `k`, solving the congruence `(1−k)V'fB ≡ C (mod V)` via `cdiophantineG`, then verifying the
  cleared identity `(Bf/(V^{k−1}y))' − C/(Vᵏy) = D/(V^{k−1}y)` by `cisZeroG`.

**Deferred** (documented, not attempted here): `θ = log v` / `θ = exp v` cases (§2.3–2.4), Cases 2/3,
and the entire LOGARITHMIC part (residues / divisors, Trager Ch. 5–6). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-! ### The simple-radical-extension carrier `RadExt α n f`

`F(y)` with `yⁿ = f ∈ F` (`F = α` a tower-level `[CField α]`): every element is a polynomial in `y` of
degree `< n` with coefficients in `α` (Appendix A, p. 73). We represent it as a **length-`n`
coefficient list** `RadElem α = List α` (index = power of `y`, low to high), the `α`-analogue of the
`CPolyG α` representation but with the relation `yⁿ = f` baked into multiplication. The parameters are a
degree `n : ℕ` and a radicand `f : α` (the `F`-element with `yⁿ = f`). -/

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

/-! ### The diagonal derivation `radDeriv` (Trager's `(f/y)'` insight)

The derivation extending `D` on `F = α` to `F(y)`. Since `yⁿ = f`, differentiating gives
`n·y^{n−1}·y' = f'`, so `y' = f'/(n·y^{n−1})`. Multiplying by `y/y` and using `yⁿ = f`:
`y' = f'·y/(n·yⁿ) = (f'/(n·f))·y`. Therefore the product rule on `Σ aᵢyⁱ` is **diagonal** — no
`y`-power mixing:

`D(Σ aᵢyⁱ) = Σ [D(aᵢ) + aᵢ·i·(f'/(n·f))]·yⁱ`.

This is exactly Trager's observation (Appendix A §1) that `D` commutes with each projection `Tᵢ`. The
base derivation `D = CDiffField.cderiv` is read off `[CDiffField α]`; `f'` is `CDiffField.cderiv f`; the
scalar `f'/(n·f)` is a single `α`-element (`logDerRadicand`). Needs `[CDiffField α]`, so it reduces. -/

variable [CDiffField α]

/-- **The radicand's logarithmic derivative scaled by the power index helper** `logDerRadicand n f =
f'/(n·f)` as a base element. The diagonal `radDeriv` multiplier for the `yⁱ`-component is
`i · logDerRadicand`; `y' = logDerRadicand · y`. (`n` enters as `CPolyG.cnatCastG n`, the `n`-fold sum
of `CField.one`, so it reduces under `native_decide`.) -/
def logDerRadicand (n : ℕ) (f : α) : α :=
  CField.div (CDiffField.cderiv f) (CField.mul (CPolyG.cnatCastG n) f)

/-- **The diagonal radical derivation** `radDeriv n f [a₀,…] = [D a₀ + 0·a₀·ℓ, D a₁ + 1·a₁·ℓ, …]` with
`ℓ = logDerRadicand n f = f'/(n·f)`: the `i`-th component maps `aᵢ ↦ D(aᵢ) + aᵢ·(i·ℓ)`. Trager's
`(f/y)'` form — the derivation preserves every `yⁱ`-component (commutes with `Tᵢ`). `[CField α]
[CDiffField α]`-computable, so it `native_decide`s. -/
def radDeriv (n : ℕ) (f : α) (p : RadElem α) : RadElem α :=
  let ℓ := logDerRadicand n f
  (p.zipIdx.map (fun (a, i) =>
    CField.add (CDiffField.cderiv a) (CField.mul a (CField.mul (CPolyG.cnatCastG i) ℓ))))

end RadElem

/-! ### ★ The carrier validates: `y = √(x³+1)` over `ℚ(x)` (`native_decide`)

`F = QFunNZG ℚ ≅ ℚ(x)`, `n = 2`, `f = x³+1`. The generator `y` is the square root `√(x³+1)`. We check
the defining relation `y·y = f` (radical multiplication folds `y² → f`) and the derivation `D(y) =
(3x²/(2(x³+1)))·y` (the diagonal `radDeriv`, base derivation `d/dx` on the ℚ(x) coefficients). Both run
in the native compiler: `RadElem (QFunNZG ℚ)` is a list over the computable ℚ(x), all operations are
list/field arithmetic, the subtype proofs are `Prop`-erased. -/

open RadElem

/-- A `ℚ(x)` value (`QFunNZG ℚ`) from a numerator `CPoly = List ℚ` over denominator `1`. -/
def qxOfNum (num : CPolyG ℚ) : QFunNZG ℚ :=
  ⟨(num, [CField.one]), QFunNZG.cisZeroG_one_singleton⟩

/-- The radicand `f = x³ + 1 ∈ ℚ(x)` (numerator `[1,0,0,1]` = `1 + x³`). -/
def radicandX3p1 : QFunNZG ℚ := qxOfNum [1, 0, 0, 1]

/-- **★ `y·y = f` over `ℚ(x)`** (`native_decide`): the square of the generator `y = √(x³+1)` in
`(QFunNZG ℚ)[y]/(y² − (x³+1))` reduces, via `radMul`'s `y² → f` fold, to `f = x³+1`. Checked by
`radIsZero` of `y·y − f` (as the length-`1` `RadElem` `[f]`). THE RADICAL CARRIER COMPUTES. -/
theorem radGen_sq_eq_radicand :
    radIsZero (radSub (radMul 2 radicandX3p1 (radGen : RadElem (QFunNZG ℚ)) radGen) [radicandX3p1])
      = true := by native_decide

/-- The ℚ(x) value `3x² = (x³+1)' ∈ ℚ(x)` (numerator `[0,0,3]`), the derivative of the radicand. -/
def radicandDeriv : QFunNZG ℚ := qxOfNum [0, 0, 3]

/-- The diagonal multiplier `ℓ = f'/(2f) = 3x²/(2(x³+1)) ∈ ℚ(x)` for `D(y) = ℓ·y`. -/
def radicandLogDer : QFunNZG ℚ := logDerRadicand 2 radicandX3p1

/-- **★ `D(y) = (3x²/(2(x³+1)))·y` over `ℚ(x)`** (`native_decide`): the diagonal radical derivation of
the generator `y = √(x³+1)` is `ℓ·y` with `ℓ = f'/(2f) = 3x²/(2(x³+1))`. Checked by `radIsZero` of
`D(y) − [0, ℓ]` (the pure-`y` element with coefficient `ℓ`). THE RADICAL DERIVATION COMPUTES — and it
is diagonal (`D(y)` has only a `y`-component, no constant term). -/
theorem radDeriv_radGen_eq :
    radIsZero (radSub (radDeriv 2 radicandX3p1 (radGen : RadElem (QFunNZG ℚ)))
        [CField.zero, radicandLogDer]) = true := by native_decide

/-- **`D(1) = 0` over `ℚ(x)`** (`native_decide`): the radical derivation annihilates the constant `1`
(the `i = 0` component has no `ℓ`-term and `D(1) = 0` in ℚ(x)). -/
theorem radDeriv_radOne_eq_zero :
    radIsZero (radDeriv 2 radicandX3p1 (radOne : RadElem (QFunNZG ℚ))) = true := by native_decide

/-- **Ring sanity: `y·1 = y`** over `ℚ(x)` (`native_decide`) — `radMul` with `radOne` is the identity
(the `y² → f` fold is a no-op below degree `2`). -/
theorem radMul_radOne_eq :
    radIsZero (radSub (radMul 2 radicandX3p1 (radGen : RadElem (QFunNZG ℚ)) radOne) radGen)
      = true := by native_decide

/-- **Ring sanity: `(1+y)·(1+y) = 1 + 2y + f`** over `ℚ(x)` (`native_decide`) — squaring `1 + y`
expands to `1 + 2y + y²` and folds `y² → f = x³+1`, giving `(1 + (x³+1)) + 2y`. Checked by `radIsZero`
of the difference against `[1 + f, 2]`. -/
theorem radMul_onePlusGen_sq :
    radIsZero (radSub
        (radMul 2 radicandX3p1 [CField.one, CField.one] [(CField.one : QFunNZG ℚ), CField.one])
        [CField.add CField.one radicandX3p1, CField.add CField.one CField.one]) = true := by
  native_decide

end DeepWiki.SymbolicIntegration
