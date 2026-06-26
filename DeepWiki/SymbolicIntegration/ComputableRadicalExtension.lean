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

* **Case 2** (Appendix A §2.2, `C/(Wᵏy)`, `W = Pⱼ` a squarefree factor of `f`, `n = 2`) —
  `radCase2Cofactor`/`radCase2Residual`: solve the `radDeriv`-validated congruence `B·(½−k)W'h ≡ C
  (mod W)` (`h = f/W`; the bracket `½−k = 1−k−eⱼ/n` is Trager's, at `eⱼ = 1, n = 2`) via `cdiophantineG`,
  eliminating `f`-factors from denominators; cleared identity `B·(½−k)W'h − C + W·(B'h + ½Bh') = W·D`,
  with the end-to-end `radDeriv` validation `case2cDriver_integrates` in `ComputableRadicalCase2`.

* **Case 3** (Appendix A §2.3, `C/y`, `θ'=1`) — `radCase3Cofactor`/`radCase3Residual`: degree-lowering
  by the leading-coefficient match `c_{j+m} = (j+1 + lcf(g))b`, `b = lcf(C)/((j+1)+lcf(g))`; cleared
  identity `B'f + Bg − C = D` with `deg D < deg C`.

* **`θ = log v`** (Appendix A §2.3 eq. 5) — `radCase3CofactorGen`: the same `C/y` degree-lowering with the
  `v'/v`-weighted bracket `(j+1)·θ' + lcf(g)` and the full monomial derivative `cmonomialDeriv [θ']` for
  `B'`, validated on a genuine 2-level tower `ℚ(x)[log x]`, `y = √(log x)`.

* **`θ = exp v`** (Appendix A §2.4) — `radExpCofactor`/`radExpResidual`: the `C/(θᵏy)` step where `θ ∣ θ'`,
  matching **constant** (θ-degree-`0`) terms `c₀ = b₀g₀ − k·v'·b₀·f₀` (constant-`b₀` slice
  `b₀ = c₀/(g₀ − kv'f₀)`), cleared identity `(B'f + Bg − kv'Bf) − C = θ·D`, validated on a genuine
  exponential tower `ℚ(x)[eˣ]`, `y = √(eˣ+1)`.

With Cases 1–3 + `θ = log v` + the `θ = exp v` `C/(θᵏy)` step, the simple-radical **rational part** is
realized across all four `θ`-level kinds (`θ' = 1`, `θ = log v`, `θ = exp v`).

**Deferred** (documented, not attempted here): the general first-order-ODE coefficient solves of the
`θ = log v` / `θ = exp v` *lower* coefficients (Risch [38], beyond the leading/constant slice shown), the
`θ = exp v` `C/y` sub-case (eq. 6, same ODE character), and the entire LOGARITHMIC part (residues /
divisors, Trager Ch. 5–6). -/

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

/-! ### The `Tᵢ` decoupling (Trager Appendix A §1)

With `σ(y) = ωy` (ω a primitive `n`-th root of unity) Trager builds the projection operators
`Tᵢ = (1/n)·Σⱼ σʲ/ωⁱʲ`, which satisfy `Tᵢ(yʲ) = yʲ` if `i = j` else `0`, and **commute with the
derivation** (`Tᵢ(v') = (Tᵢ v)'`). On the coefficient-list representation `Tᵢ` is just "keep the `yⁱ`
component, zero the rest" — `radProj i`. The diagonality of `radDeriv` (each `yⁱ`-component maps to a
`yⁱ`-component) *is* the statement `Tᵢ ∘ D = D ∘ Tᵢ`. Consequence (Appendix A §1): `∫(Σ gᵢyⁱ)`
**decouples** — `g` integrable iff each `gᵢyⁱ` is, and the rational part of `∫gᵢyⁱ` is `vᵢyⁱ`. -/

namespace RadElem

variable {α : Type*} [CField α]

/-- **The projection `Tᵢ`** `radProj i p` — keep the `yⁱ`-component of `p`, zero every other power:
the coefficient list with `aᵢ` at index `i` and `CField.zero` elsewhere (length `i+1`, normalized). The
list realization of Trager's `Tᵢ = (1/n)Σⱼσʲ/ωⁱʲ`, satisfying `Tᵢ(yʲ) = yʲ·[i=j]`. -/
def radProj (i : ℕ) (p : RadElem α) : RadElem α :=
  match (p : List α)[i]? with
  | none => []
  | some a => CPolyG.cnormG (CPolyG.cshiftG i [a])

end RadElem

/-! #### ★ `Tᵢ` decoupling validates over `√(x³+1)` (`native_decide`)

`Tᵢ(yʲ) = yʲ·[i=j]`, `Tᵢ ∘ D = D ∘ Tᵢ`, and the `∫(g₀+g₁y)` split, exhibited on `α = ℚ(x)`, `n = 2`,
`f = x³+1`. -/

/-- **`T₁(y) = y`** (`native_decide`): the projection onto the `y`-power fixes `y = √(x³+1)`. -/
theorem radProj_one_radGen :
    radIsZero (radSub (radProj 1 (radGen : RadElem (QFunNZG ℚ))) radGen) = true := by native_decide

/-- **`T₀(y) = 0`** (`native_decide`): the projection onto the constant power kills `y` (Trager's
`Tᵢ(yʲ) = 0` for `i ≠ j`). -/
theorem radProj_zero_radGen :
    radIsZero (radProj 0 (radGen : RadElem (QFunNZG ℚ))) = true := by native_decide

/-- **`T₁(1) = 0`** (`native_decide`): the projection onto the `y`-power kills the constant `1`. -/
theorem radProj_one_radOne :
    radIsZero (radProj 1 (radOne : RadElem (QFunNZG ℚ))) = true := by native_decide

/-- A mixed element `g = g₀ + g₁y = (x³+1) + 3x²·y ∈ ℚ(x)[y]/(y²−(x³+1))` (`g₀ = f`, `g₁ = f'`), the
test integrand for the `Tᵢ` decoupling. -/
def mixedElem : RadElem (QFunNZG ℚ) := [radicandX3p1, radicandDeriv]

/-- **★ `T₁ ∘ D = D ∘ T₁` on the mixed element** (`native_decide`): the projection onto the `y`-power
commutes with the radical derivation — `T₁(D g) = D(T₁ g)` for `g = (x³+1) + 3x²·y`. This is Trager's
"`Tᵢ` commutes with the derivation", the engine of the `∫gᵢyⁱ` decoupling, verified by `radIsZero` of
the difference over ℚ(x). -/
theorem radProj_one_radDeriv_comm :
    radIsZero (radSub
        (radProj 1 (radDeriv 2 radicandX3p1 mixedElem))
        (radDeriv 2 radicandX3p1 (radProj 1 mixedElem))) = true := by native_decide

/-- **★ `T₀ ∘ D = D ∘ T₀` on the mixed element** (`native_decide`): the projection onto the constant
power commutes with the radical derivation — `T₀(D g) = D(T₀ g)`. The other half of the commutation. -/
theorem radProj_zero_radDeriv_comm :
    radIsZero (radSub
        (radProj 0 (radDeriv 2 radicandX3p1 mixedElem))
        (radDeriv 2 radicandX3p1 (radProj 0 mixedElem))) = true := by native_decide

/-- **★ The `∫(g₀+g₁y)` split** (`native_decide`): `D(g) = D(T₀ g) + D(T₁ g)` decomposes additively
into its `1`-component and `y`-component, and the two pieces share no power of `y` (each `D(Tᵢ g)` lies
in the `yⁱ`-component, by `radDeriv`'s diagonality). So `∫g` reduces to `∫(g₀) + ∫(g₁y)` *independently*
(Appendix A §1). Verified by `radIsZero` of `D(g) − (D(T₀ g) + D(T₁ g))` over ℚ(x). -/
theorem radDeriv_decouples :
    radIsZero (radSub
        (radDeriv 2 radicandX3p1 mixedElem)
        (radAdd (radDeriv 2 radicandX3p1 (radProj 0 mixedElem))
          (radDeriv 2 radicandX3p1 (radProj 1 mixedElem)))) = true := by native_decide

/-- **The `y`-component of `D(g)` stays in the `y`-component** (`native_decide`): `D(T₁ g) = T₁(D(T₁ g))`
— the `y`-part of the derivative has no constant term, so its rational part is `v₁·y` (Appendix A §1:
"the rational part of `∫gᵢyⁱ` is `vᵢyⁱ`"). The diagonality of `radDeriv` made concrete. -/
theorem radDeriv_projOne_stays :
    radIsZero (radSub
        (radDeriv 2 radicandX3p1 (radProj 1 mixedElem))
        (radProj 1 (radDeriv 2 radicandX3p1 (radProj 1 mixedElem)))) = true := by native_decide

/-! ### Case 1 rational-part reduction (Trager Appendix A §2.1, `θ' = 1`)

By §1 we are reduced to integrands `R/y` (rewrite `Syⁱ = R/y^{n−i}`, then choose `y` so the form is
`R/y`), and by §2 we partial-fraction into `C/(Vᵏy)`, `C/(Wᵏy)`, `C/y`. **Case 1** is the piece
`C/(Vᵏy)` with `V` coprime to the radicand `f` (here `yⁿ = f ∈ F[θ]`, `θ' = 1` the base variable). The
Hermite-style step lowers `k`: find a polynomial `B` with

`(Bf/(V^{k−1}y))' − C/(Vᵏy) = D/(V^{k−1}y)`,

and since `(Bf/(V^{k−1}y))' = ((1−k)V'Bf)/(Vᵏy) + (B'f + Bg)/(V^{k−1}y)` (with `g` from `(f/y)' = g/y`),
this needs `(1−k)V'fB ≡ C (mod V)`, solvable because `gcd((1−k)V'f, V) = 1` (V squarefree, coprime to
`f`, `k ≥ 2`). The residual is `D = ((1−k)V'fB − C)/V + B'f + Bg`. The congruence is solved by the
generic Bézout/diophantine solver `cdiophantineG`. Cleared over the common denominator `Vᵏy`, the whole
step is the **pure `F[θ]` identity** `(1−k)V'fB − C + V(B'f + Bg) = V·D` (no `y`), checkable by
`cisZeroG` — the model is `cHermiteReduceTower`'s cleared `D(g)+h = f` check.

`g` is read off `(f/y)' = g/y`; for the worked example `f` is a single squarefree θ-factor with `d = 1`,
so `g = ((n−1)/n)·f'` (Appendix A p. 76, `Σ(1−eᵢ/n)Pᵢ'/Pᵢ` with one `e₁ = 1` factor). -/

namespace CPolyG

variable {α : Type*} [CField α]

/-- **Case-1 cofactor solve** `radCase1Cofactor fuel k V Df f C = B` — the polynomial `B` (degree
`< deg V`) solving the Case-1 congruence `(1−k)·V'·f·B ≡ C (mod V)` (Trager Appendix A §2.1), via the
generic diophantine solver `cdiophantineG (((1−k)·V'·f)) V C` (which returns `(B, _)` with `B·((1−k)V'f)
+ c·V = C`). `Df = V'` is passed in (the monomial derivative `V'`, computed by the caller so the base
derivation is whatever the level uses); `(1−k)` is `cnatCastG (k−1)` negated. Generic over `[CField α]`. -/
def radCase1Cofactor (fuel : ℕ) (k : ℕ) (V Df f C : CPolyG α) : CPolyG α :=
  let oneMinusK := cnegG [cnatCastG (k - 1)]                    -- the constant `(1 − k) = −(k−1)`
  let coeff := cmulG oneMinusK (cmulG Df f)                     -- `(1−k)·V'·f`
  (cdiophantineG fuel coeff V C).1

/-- **Case-1 residual** `radCase1Residual k V Df f g B C Bder = D` — the lowered-`k` residual numerator
`D = ((1−k)V'fB − C)/V + B'f + Bg` of the Case-1 step (Trager Appendix A §2.1). `Df = V'`, `Bder = B'`,
and `g` (from `(f/y)' = g/y`) are passed in (the caller supplies the derivatives at the level's base
derivation). The exact division by `V` is `cdivG` (`V ∣ (1−k)V'fB − C` by the cofactor congruence).
Generic over `[CField α]`. -/
def radCase1Residual (fuel : ℕ) (k : ℕ) (V Df f g B C Bder : CPolyG α) : CPolyG α :=
  let oneMinusK := cnegG [cnatCastG (k - 1)]
  let topNum := csubG (cmulG oneMinusK (cmulG Df (cmulG f B))) C  -- `(1−k)V'fB − C`
  let quotient := cdivG fuel topNum V                             -- `((1−k)V'fB − C)/V`
  caddG quotient (caddG (cmulG Bder f) (cmulG B g))               -- `… + B'f + Bg`

/-! ### Case 2 rational-part reduction (Trager Appendix A §2.2, `θ' = 1`, `n = 2`)

**Case 2** is the partial-fraction piece `C/(Wᵏy)` where `W = Pⱼ` is a **squarefree factor of the
radicand `f`** (not coprime to `f`, unlike Case 1). For a simple radical `y² = f` with `f` squarefree
(the integrating factor `∏Pᵢ` equals the radicand `f`), `h = f/W`, the **actual** diagonal derivation
`radDeriv 2 f` satisfies (validated over `ℚ(x)`, see `ComputableRadicalCase2`):

`radDeriv(Bf/(Wᵏy)) = (B·(½−k)·W'·h)/(Wᵏy) + (B'h + ½Bh')/(W^{k−1}y)`,

so subtracting `C/(Wᵏy)` leaves `D/(W^{k−1}y)` provided `B·(½−k)·W'·h ≡ C (mod W)`. The bracket
`½ − k = 1 − k − eⱼ/n` (at `eⱼ = 1, n = 2`) is exactly Trager's congruence on p. 76
(`B(1−k−eⱼ/n)W'h ≡ C (mod W)`); `gcd((½−k)W'h, W) = 1` (`W'`, `h` both coprime to the squarefree `W`,
`½ − k ≠ 0` for `k ≥ 1`), so it is solvable for any `k`. The residual numerator is
`D = (B·(½−k)W'h − C)/W + B'h + ½Bh'`. Cleared over `Wᵏy`, the step is the **pure `F[θ]` identity**
`B·(½−k)W'h − C + W·(B'h + ½Bh') = W·D` (no `y`), checkable by `cisZeroG`, and `radDeriv`-validated
end-to-end in `ComputableRadicalCase2` (`case2cDriver_integrates`). Repeated application eliminates
every `f`-factor from the integrand's denominator.

(NB. An earlier rendering used `B·g − k·W'·h ≡ C (mod W)` with `g = (f/y)'`'s numerator — a true
polynomial identity, but the `−kW'h` term lacks the `B` factor, so it does **not** match `radDeriv`.
The `½ − k` form here is the faithful one; the `g`-form is not needed and is dropped.) -/

/-- **Case-2 cofactor solve (n = 2)** `radCase2Cofactor fuel k W h C = B` — the polynomial `B`
(degree `< deg W`) solving the `radDeriv`-validated Case-2 congruence `B·(½−k)·W'·h ≡ C (mod W)` (Trager
Appendix A §2.2, `B(1−k−eⱼ/n)W'h ≡ C (mod W)` at `eⱼ = 1, n = 2`), via `cdiophantineG ((½−k)W'h) W C`
(`gcd((½−k)W'h, W) = 1` since `W = Pⱼ` is a squarefree factor of `f`, coprime to `h = f/W`, and
`½ − k ≠ 0`). `h = f/W` and `W` are passed in; `W'` is `cderivG W`. Generic over `[CField α]`. -/
def radCase2Cofactor (fuel : ℕ) (k : ℕ) (W h C : CPolyG α) : CPolyG α :=
  let half : CPolyG α := [CField.div CField.one (cnatCastG 2)]              -- `½`
  let coef := cmulG (csubG half [cnatCastG k]) (cmulG (cderivG W) h)        -- `(½ − k)·W'·h`
  (cdiophantineG fuel coef W C).1

/-- **Case-2 residual (n = 2)** `radCase2Residual fuel k W h C B = D` — the lowered-`k` residual numerator
`D = (B·(½−k)W'h − C)/W + B'h + ½Bh'` of the `radDeriv`-validated Case-2 step (Trager Appendix A §2.2).
`h = f/W` and `W` are passed in; `B'` is `cderivG B`, `h'` is `cderivG h`. The exact division by `W` is
`cdivG` (`W ∣ B·(½−k)W'h − C` by the cofactor congruence). With this `D`,
`radDeriv(Bf/(Wᵏy)) = C/(Wᵏy) + D/(W^{k−1}y)`. Generic over `[CField α]`. -/
def radCase2Residual (fuel : ℕ) (k : ℕ) (W h C B : CPolyG α) : CPolyG α :=
  let half : CPolyG α := [CField.div CField.one (cnatCastG 2)]              -- `½`
  let coef := cmulG (csubG half [cnatCastG k]) (cmulG (cderivG W) h)        -- `(½ − k)·W'·h`
  let topNum := csubG (cmulG B coef) C                                      -- `B·(½−k)W'h − C`
  let quotient := cdivG fuel topNum W                                       -- `/W`
  caddG quotient (caddG (cmulG (cderivG B) h)                              -- `+ B'h`
    (cmulG half (cmulG B (cderivG h))))                                     -- `+ ½Bh'`

/-! ### Case 3 rational-part reduction (Trager Appendix A §2.3, `θ' = 1`)

**Case 3** is the leftover `C/y` after Cases 1–2 cleared every denominator factor. Here there is no
denominator to lower; instead we lower **`deg C`**. With `(f/y)' = g/y` clean we have
`(Bf/y)' = (B'f + Bg)/y`, so `(Bf/y)' − C/y = (B'f + Bg − C)/y`. Taking `B = b·θ^{j+1}` a single
**constant**-coefficient monomial of degree `j+1 := deg C − deg f + 1` (so `B'f` and `Bg` both top out at
degree `deg C`), the top-degree relation (Trager Appendix A §2.3 eqs. 3–4, `θ' = 1`) is
`c_{j+m} = (j + 1 + lcf(g))·b` with `lcf(g) = Σ deg(Pᵢ)(1 − eᵢ/n)` — so the leading coefficient `b`
is determined (`j + 1 ≥ 0` makes the bracket nonzero), and `deg(B'f + Bg − C) < deg C`. Since `lcf(g)`
is literally the **leading coefficient of the given `g`**, the solve is the single field division
`b = lcf(C) / ((j+1) + lcf(g))`. Cleared over `y`, the step is the pure `F[θ]` identity
`B'f + Bg − C = D` with `deg D < deg C`, checkable by `cisZeroG`. Iterating drops `deg C` below `m − 1`,
leaving the irreducible rational part. -/

/-- **Case-3 leading-coefficient cofactor** `radCase3Cofactor f g C = B` — the single constant-coefficient
monomial `B = b·θ^{j+1}` (`j + 1 = deg C − deg f + 1`) cancelling the leading term of `C` in the `C/y`
degree-lowering (Trager Appendix A §2.3 eq. 4, `θ' = 1`): `b = lcf(C) / ((j+1) + lcf(g))`, with
`lcf(g) = Σ deg(Pᵢ)(1 − eᵢ/n)` the leading coefficient of the supplied `g` (from `(f/y)' = g/y`). The
bracket `(j+1) + lcf(g)` is nonzero for `j + 1 ≥ 0`. Returns `[]` when `deg C < deg f` (nothing to
lower). Generic over `[CField α]`. -/
def radCase3Cofactor (f g C : CPolyG α) : CPolyG α :=
  let dC := cdegG C
  let dF := cdegG f
  if cisZeroG C || dC < dF then []
  else
    let jp1 := dC - dF + 1                                         -- `j + 1 = deg C − deg f + 1`
    let denom := CField.add (cnatCastG jp1) (cleadG g)            -- `(j+1) + lcf(g)`
    let b := CField.div (cleadG C) denom                          -- `b = lcf(C)/((j+1)+lcf(g))`
    cshiftG jp1 [b]                                                -- `b·θ^{j+1}`

/-- **Case-3 residual** `radCase3Residual f g B C Bder = D` — the lowered-degree numerator
`D = B'f + Bg − C` of the `C/y` degree-lowering step (Trager Appendix A §2.3), where `(Bf/y)' =
(B'f + Bg)/y`. `Bder = B'` and `g` (from `(f/y)' = g/y`) are passed in; with `B` the leading-coefficient
monomial from `radCase3Cofactor`, `deg D < deg C`. Generic over `[CField α]`. -/
def radCase3Residual (f g B C Bder : CPolyG α) : CPolyG α :=
  csubG (caddG (cmulG Bder f) (cmulG B g)) C                       -- `B'f + Bg − C`

/-! ### `θ = log v` rational-part reduction (Trager Appendix A §2.3 eq. 5)

For `θ = log v` (so `θ' = v'/v ∈ F`, a base-field element, no longer `1`) the `C/y` degree-lowering is
identical in shape to Case 3 — the derivation identity `(Bf/y)' = (B'f + Bg)/y` holds for any `θ` — but
the leading-coefficient relation (Trager Appendix A §2.3 eq. 5) becomes
`c_{j+m} = b_{j+1}((j+1)·v'/v + lcf(g)) + bⱼ'`,
where `lcf(g) = Σ(1−eᵢ/n)(deg(Pᵢ)v'/v + aᵢ')` is the leading `F`-coefficient of `g`. The coefficient of
`b_{j+1}` is `(j+1)·v'/v + lcf(g)`, whose `v'/v`-part `(j+1) + Σdeg(Pᵢ)(1−eᵢ/n)` is nonzero for
`j + 1 ≥ 0`, so the leading constant `b_{j+1}` is uniquely determined. The two differences from Case 3
are: (i) the bracket carries the field element `θ' = v'/v` in the `(j+1)` term — `radCase3CofactorGen`
takes it as `Dt`; (ii) `B'` is the **full** monomial derivative `cmonomialDeriv [θ'] B` (the coefficient
derivative plus the `θ'`-term), not the formal `cderivG` — supplied by the caller. The residual and
cleared check `B'f + Bg − C = D` are unchanged (`radCase3Residual`). Setting `Dt = 1` (`θ' = 1`,
`cmonomialDeriv [1] = cderivG` on constant coefficients) recovers Case 3 exactly. -/

/-- **Generalized Case-3 leading-coefficient cofactor** `radCase3CofactorGen Dt f g C = B` — the
constant-coefficient monomial `B = b·θ^{j+1}` (`j + 1 = deg C − deg f + 1`) cancelling the leading term
of `C` in the `C/y` degree-lowering, for **any** `θ` with derivative `Dt = θ' ∈ α` (the base-field
element): `b = lcf(C) / ((j+1)·θ' + lcf(g))` (Trager Appendix A §2.3 eqs. 4–5). For `θ' = 1` this is the
Case-3 bracket `(j+1) + lcf(g)`; for `θ = log v` it is the `eq. 5` bracket `(j+1)v'/v + lcf(g)`. Returns
`[]` when `deg C < deg f`. Generic over `[CField α]`. -/
def radCase3CofactorGen (Dt : α) (f g C : CPolyG α) : CPolyG α :=
  let dC := cdegG C
  let dF := cdegG f
  if cisZeroG C || dC < dF then []
  else
    let jp1 := dC - dF + 1                                         -- `j + 1 = deg C − deg f + 1`
    let denom := CField.add (CField.mul (cnatCastG jp1) Dt) (cleadG g)  -- `(j+1)·θ' + lcf(g)`
    let b := CField.div (cleadG C) denom                          -- `b = lcf(C)/((j+1)θ' + lcf(g))`
    cshiftG jp1 [b]                                                -- `b·θ^{j+1}`

/-! ### `θ = exp v` rational-part reduction (Trager Appendix A §2.4)

For `θ = exp v` the distinguishing feature is that **`θ` divides its own derivative** (`θ' = v'·θ`), so a
squarefree polynomial need not be coprime to its derivative — only `θᵏ` factors of the denominator need
special handling. After a partial fraction, the non-`θ` denominators reduce exactly as Cases 1–2; the
new piece is `C/(θᵏy)`. Here (Trager Appendix A §2.4, p. 79)
`(Bf/(θᵏy))' = (B'f + Bg − k·v'·B·f)/(θᵏy)`,
and requiring the numerator `≡ C (mod θ)` is equating **constant** (θ-degree-`0`) terms:
`c₀ = b₀'·f₀ + b₀·g₀ − k·v'·b₀·f₀` (`θ ∤ f` ⇒ `f₀ ≠ 0`). In general this is a first-order linear ODE for
`b₀ ∈ F` (Risch [38]); on the **constant-`b₀` slice** (`b₀' = 0`, the common case where the witness lands
in the field of constants) it collapses to the single field division `b₀ = c₀/(g₀ − k·v'·f₀)`. The
residual `D = ((B'f + Bg − kv'Bf) − C)/θ` drops `k → k−1`; cleared over `θᵏy` the step is the pure `F[θ]`
identity `(B'f + Bg − kv'Bf) − C = θ·D`, checkable by `cisZeroG`. (The `C/y` exp sub-case, eq. 6, has the
same ODE character and is left with the full logarithmic part.) -/

/-- **`θ`-constant coefficient** `radConstCoeff p = ` the `θ⁰` (head) coefficient of `p` (`CField.zero`
for the zero polynomial) — the residue of `p` modulo `θ`, used by the `θ = exp v` constant-term match. -/
def radConstCoeff (p : CPolyG α) : α := (p : List α).headD CField.zero

/-- **`θ = exp v` `C/(θᵏy)` constant-coefficient cofactor** `radExpCofactor k vder f g C = B` — the
constant `B = [b₀]` solving the exp constant-term match `c₀ = b₀g₀ − k·v'·b₀·f₀` (Trager Appendix A §2.4,
constant-`b₀` slice `b₀' = 0`): `b₀ = c₀ / (g₀ − k·v'·f₀)`, with `f₀, g₀, c₀` the `θ⁰`-coefficients of
`f, g, C` and `vder = v' ∈ α`. `θ ∤ f` makes `f₀ ≠ 0`, so the denominator `g₀ − kv'f₀` is generically
nonzero. Generic over `[CField α]`. -/
def radExpCofactor (k : ℕ) (vder : α) (f g C : CPolyG α) : CPolyG α :=
  let f0 := radConstCoeff f
  let g0 := radConstCoeff g
  let c0 := radConstCoeff C
  let denom := CField.sub g0 (CField.mul (CField.mul (cnatCastG k) vder) f0)  -- `g₀ − k·v'·f₀`
  [CField.div c0 denom]                                                       -- `[b₀]`

/-- **`θ = exp v` `C/(θᵏy)` residual** `radExpResidual k vder f g B C Bder = D` — the lowered-`k` residual
`D = ((B'f + Bg − k·v'·B·f) − C)/θ` of the exp `C/(θᵏy)` step (Trager Appendix A §2.4). `vder = v'`,
`Bder = B'` (the full `cmonomialDeriv [θ'] B`), and `g` are passed in. The exact division by `θ` is
`cdivG _ _ [0,1]` (`θ ∣ (B'f + Bg − kv'Bf) − C` by the constant-term match). Generic over `[CField α]`. -/
def radExpResidual (fuel : ℕ) (k : ℕ) (vder : α) (f g B C Bder : CPolyG α) : CPolyG α :=
  let kvBf := cmulG [CField.mul (cnatCastG k) vder] (cmulG B f)    -- `k·v'·B·f`
  let num := csubG (csubG (caddG (cmulG Bder f) (cmulG B g)) kvBf) C  -- `B'f + Bg − kv'Bf − C`
  cdivG fuel num [CField.zero, CField.one]                         -- `… / θ`

end CPolyG

/-! #### ★ Case 1 validates: `∫ C/(V²y)` with `y = √x`, `V = x−1` (`native_decide`)

`F = ℚ` (constants), `θ = x` (`θ' = 1`, so `D = d/dx = cderivG` on `ℚ[x]`), radicand `y² = f = x`
(`n = 2`, `y = √x`), `V = x − 1` (coprime to `f = x`), `k = 2`, `C = 1`. So the integrand is
`1/((x−1)²√x)`. The cofactor congruence `(1−2)·V'·f·B ≡ C (mod V)` is `−x·B ≡ 1 (mod x−1)`; mod `x−1`,
`x ≡ 1`, so `B = −1`. The residual `D = ((1−2)·1·x·(−1) − 1)/(x−1) + 0 + (−1)·(1/2) = (x−1)/(x−1) − 1/2
= 1/2`, a constant (degree `< deg V`), so the multiplicity dropped `2 → 1`. `g = f'/2 = 1/2`. -/

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
def case1B : CPolyG ℚ := radCase1Cofactor 8 2 case1V case1Vder case1F case1C

/-- The Case-1 residual `D` — expected the constant `1/2`. -/
def case1D : CPolyG ℚ :=
  radCase1Residual 8 2 case1V case1Vder case1F case1G case1B case1C (cderivG case1B)

/-- **The cofactor is `B = −1`** (`native_decide`): the diophantine solve of `−x·B ≡ 1 (mod x−1)` gives
`B = −1` (`cisZeroG` of `B − (−1)`). The Case-1 congruence solver runs over `ℚ[x]`. -/
theorem case1_cofactor_eq :
    cisZeroG (csubG case1B [(-1 : ℚ)]) = true := by native_decide

/-- **★ The Case-1 congruence holds**: `(1−k)V'fB − C ≡ 0 (mod V)` (`native_decide`) — the numerator
`(1−2)·V'·f·B − C = −x·(−1) − 1 = x − 1` is divisible by `V = x − 1`, the defining property of the
cofactor `B`. Checked by `cisZeroG` of the remainder `cmodG ((1−k)V'fB − C) V`. -/
theorem case1_congruence :
    cisZeroG (cmodG 8
      (csubG (cmulG (cnegG [cnatCastG 1]) (cmulG case1Vder (cmulG case1F case1B))) case1C)
      case1V) = true := by native_decide

/-- **★ The Case-1 cleared Hermite identity** (`native_decide`): the reduction
`(Bf/(V^{k−1}y))' − C/(Vᵏy) = D/(V^{k−1}y)`, cleared over the common denominator `Vᵏy`, is the pure
`ℚ[x]` identity `(1−k)V'fB − C + V·(B'f + Bg) = V·D`. With `B = −1`, `D = 1/2`: LHS `= x − 1 + (x−1)·(0
+ (−1)(1/2)) = (x−1) − (x−1)/2 = (x−1)/2`, RHS `= (x−1)·(1/2) = (x−1)/2`. Checked by `cisZeroG` of
LHS − RHS over `ℚ[x]`. THE CASE-1 RATIONAL REDUCTION COMPUTES — it lowers the multiplicity `k = 2 → 1`
and `D(reduced) + residual = original` holds exactly. -/
theorem case1_cleared_identity :
    cisZeroG (csubG
      (caddG
        (csubG (cmulG (cnegG [cnatCastG 1]) (cmulG case1Vder (cmulG case1F case1B))) case1C)
        (cmulG case1V (caddG (cmulG (cderivG case1B) case1F) (cmulG case1B case1G))))
      (cmulG case1V case1D)) = true := by native_decide

/-- **The residual `D = 1/2` has degree `< deg V`** (`native_decide`): `D` is the constant `1/2`
(`cisZeroG` of `D − 1/2`), so the Case-1 step lowered the apparent denominator multiplicity from
`k = 2` to `k − 1 = 1`, exactly as the Hermite reduction guarantees. -/
theorem case1_residual_eq :
    cisZeroG (csubG case1D [(1/2 : ℚ)]) = true := by native_decide

/-! #### ★ Case 2 validates: `∫ C/(W²y)` with `y = √(x³−x)`, `W = x` (`native_decide`)

`F = ℚ` (constants), `θ = x` (`θ' = 1`), radicand `y² = f = x³ − x = x(x−1)(x+1)` (`n = 2`, `m = 3`,
squarefree so the integrating factor `∏Pᵢ = f`). The squarefree factor `W = x` (so `W ∣ f`, `e₁ = 1`, a
branch place `x = 0` of the radical), `h = f/W = x² − 1`, `W' = 1`. Take `k = 2`, `C = 1`, so the
integrand is `1/(x²√(x³−x))`. The `radDeriv`-validated congruence `B·(½−k)·W'·h ≡ C (mod W=x)` reads
`B·(−3/2)·1·(−1) ≡ 1 (mod x)`, i.e. `(3/2)B(0) = 1`, so `B = 2/3`. The residual
`D = (B·(½−k)W'h − C)/W + B'h + ½Bh' = −x/3`, lowering the multiplicity `k = 2 → 1`. (See
`ComputableRadicalCase2` for the end-to-end `radDeriv` validation `case2cDriver_integrates`.) -/

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
def case2B : CPolyG ℚ := radCase2Cofactor 8 2 case2W case2H case2C

/-- The Case-2 residual `D` — expected `−x/3` (multiplicity dropped `k = 2 → 1`). -/
def case2D : CPolyG ℚ :=
  radCase2Residual 8 2 case2W case2H case2C case2B

/-- **The cofactor is `B = 2/3`** (`native_decide`): the diophantine solve of `B·(½−2)·W'·h ≡ 1 (mod x)`
gives `B = 2/3` (`cisZeroG` of `B − 2/3`). The Case-2 congruence solver runs over `ℚ[x]`. -/
theorem case2_cofactor_eq :
    cisZeroG (csubG case2B [(2/3 : ℚ)]) = true := by native_decide

/-- **★ The Case-2 congruence holds**: `B·(½−k)·W'·h − C ≡ 0 (mod W)` (`native_decide`) — the numerator
`B·(½−2)·1·(x²−1) − 1` is divisible by `W = x`, the defining property of the cofactor `B`. Checked by
`cisZeroG` of `cmodG (B·(½−k)W'h − C) W`. -/
theorem case2_congruence :
    cisZeroG (cmodG 8
      (csubG (cmulG case2B
        (cmulG (csubG [CField.div CField.one (cnatCastG 2)] [cnatCastG 2])
          (cmulG case2Wder case2H))) case2C)
      case2W) = true := by native_decide

/-- **★ The Case-2 cleared Hermite identity** (`native_decide`): the reduction
`(Bf/(Wᵏy))' − C/(Wᵏy) = D/(W^{k−1}y)`, cleared over the common denominator `Wᵏy`, is the pure `ℚ[x]`
identity `B·(½−k)W'h − C + W·(B'h + ½Bh') = W·D`. With `B = 2/3`, `D = −x/3`. Checked by `cisZeroG` of
LHS − RHS over `ℚ[x]`. THE CASE-2 RATIONAL REDUCTION COMPUTES — it eliminates the `f`-factor `W = x` from
the denominator, lowering its multiplicity `k = 2 → 1` (and `radDeriv`-validated end-to-end in
`ComputableRadicalCase2`). -/
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

/-- **The residual `D = −x/3` has multiplicity dropped** (`native_decide`): `D = −x/3` (`cisZeroG` of
`D + x/3`), so the Case-2 step lowered the apparent denominator multiplicity of `W = x` from `k = 2` to
`k − 1 = 1`, eliminating one `f`-factor exactly as Trager's reduction guarantees. -/
theorem case2_residual_eq :
    cisZeroG (csubG case2D [(0 : ℚ), -1/3]) = true := by native_decide

/-! #### ★ Case 3 validates: degree-lowering `∫ (x²+x)/√x` with `y = √x` (`native_decide`)

`F = ℚ` (constants), `θ = x` (`θ' = 1`), radicand `y² = f = x` (`n = 2`, `m = deg f = 1`, single factor
`P₁ = x`, `e₁ = 1`, so `lcf(g) = deg(P₁)(1 − e₁/n) = 1·(1 − 1/2) = 1/2`, `g = (1/2)f' = 1/2`). The
integrand is `(x² + x)/√x`, `C = x² + x` (`deg C = 2 ≥ m`). The leading-coefficient solve gives
`j + 1 = deg C − deg f + 1 = 2`, `b = lcf(C)/((j+1) + lcf(g)) = 1/(2 + 1/2) = 2/5`, so `B = (2/5)x²`. The
residual `D = B'f + Bg − C = (4/5)x² + (1/5)x² − (x²+x) = −x`, of degree `1 < deg C = 2` — the leading
`x²` is cancelled, lowering `deg C` by one. (A second Case-3 step on `−x` would finish it to `D = 0`.) -/

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

/-- **The cofactor is `B = (2/5)x²`** (`native_decide`): the leading-coefficient solve gives
`b = lcf(C)/((j+1)+lcf(g)) = 1/(2+1/2) = 2/5` at degree `j+1 = 2` (`cisZeroG` of `B − (2/5)x²`). -/
theorem case3_cofactor_eq :
    cisZeroG (csubG case3B [(0 : ℚ), 0, 2/5]) = true := by native_decide

/-- **★ The Case-3 cleared degree-lowering identity** (`native_decide`): the reduction
`(Bf/y)' − C/y = D/y`, cleared over the denominator `y`, is the pure `ℚ[x]` identity `B'f + Bg − C = D`.
With `B = (2/5)x²`, `D = −x`: `B'f + Bg = (4/5)x·x + (2/5)x²·(1/2) = (4/5)x² + (1/5)x² = x²`, so
`x² − (x²+x) = −x = D`. Checked by `cisZeroG` of `(B'f + Bg) − C − D` over `ℚ[x]`. THE CASE-3 DEGREE
REDUCTION COMPUTES — it cancels the leading `c_{j+m}` term, lowering `deg C`. -/
theorem case3_cleared_identity :
    cisZeroG (csubG
      (csubG (caddG (cmulG (cderivG case3B) case3F) (cmulG case3B case3G)) case3C)
      case3D) = true := by native_decide

/-- **The residual `D = −x` has lower degree** (`native_decide`): `D = −x` (`cisZeroG` of `D + x`), of
degree `1`, strictly below `deg C = 2` — the Case-3 step cancelled the leading `x²`, exactly the
`deg C` drop Trager's leading-coefficient match guarantees. -/
theorem case3_residual_eq :
    cisZeroG (csubG case3D [(0 : ℚ), -1]) = true := by native_decide

/-- **★ The Case-3 step strictly lowers `deg C`** (`native_decide`): `deg D = 1 < deg C = 2`. The
degree-lowering invariant of the `C/y` reduction made explicit — iterating drives `deg C` below
`m − 1 = 0`, leaving only the irreducible rational part. -/
theorem case3_degree_drop : cdegG case3D < cdegG case3C := by native_decide

/-! #### ★ `θ = log v` validates: degree-lowering `∫ C/y` over `ℚ(x)[log x]`, `y = √(log x)` (`native_decide`)

A genuine **2-level** tower: base `F = QFunNZG ℚ ≅ ℚ(x)`, monomial `θ = log x` (so `v = x`,
`θ' = v'/v = 1/x ∈ ℚ(x)`); the ring `F[θ] = ℚ(x)[log x]` is `CPolyG (QFunNZG ℚ)`. Radicand
`y² = f = θ = log x` (`n = 2`, `m = deg_θ f = 1`, `P₁ = θ`, `e₁ = 1`), so `(f/y)' = g/y` with
`g = (1/2)·(1/x) = 1/(2x)` (a degree-`0`-in-θ element, `lcf(g) = 1/(2x)`). For `C` whose leading term is
`(5/(2x))θ²` the eq. 5 bracket is `(j+1)·θ' + lcf(g) = 2·(1/x) + 1/(2x) = 5/(2x)`, so `b = lcf(C)/bracket
= 1` — a genuine **constant** — and `B = θ²`. The residual `D = B'f + Bg − C` drops `deg_θ C` by one,
with `B' = cmonomialDeriv [θ'] B` the full log-monomial derivative. -/

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

/-- **The `log` cofactor is the constant monomial `B = θ²`** (`native_decide`): the eq. 5
leading-coefficient solve over the 2-level tower `ℚ(x)[log x]` gives `b = (5/(2x))/((2)(1/x) + 1/(2x)) =
1` at degree `j+1 = 2`, i.e. `B = 1·θ²` (`radIsZero` of `B − θ²` as a `RadElem`). `b` is a genuine
constant — the integrability witness for the leading coefficient. -/
theorem logCase_cofactor_eq :
    cisZeroG (csubG logB [CField.zero, CField.zero, (CField.one : QFunNZG ℚ)]) = true := by
  native_decide

/-- **★ The `θ = log v` cleared degree-lowering identity** (`native_decide`): the reduction
`(Bf/y)' − C/y = D/y`, cleared over `y`, is the pure `ℚ(x)[log x]` identity `B'f + Bg − C = D` with
`B' = cmonomialDeriv [1/x] B` the full log-monomial derivative. With `B = θ²`: `B' = (2/x)θ`,
`B'f + Bg = (2/x)θ² + (1/(2x))θ² = (5/(2x))θ²`, so `D = (5/(2x))θ² − ((5/(2x))θ² + θ) = −θ`. Checked by
`cisZeroG` of `(B'f + Bg) − C − D` over `ℚ(x)[log x]`. THE `θ = log v` DEGREE REDUCTION COMPUTES on a
genuine 2-level monomial tower — the `v'/v`-weighted leading relation (eq. 5) cancels `c_{j+m}`. -/
theorem logCase_cleared_identity :
    cisZeroG (csubG
      (csubG (caddG (cmulG (cmonomialDeriv logDtPoly logB) logF) (cmulG logB logG)) logC)
      logD) = true := by native_decide

/-- **The `log` residual `D = −θ` has lower degree** (`native_decide`): `D = −θ = −log x` (`cisZeroG` of
`D + θ`), of `θ`-degree `1`, strictly below `deg_θ C = 2` — the leading `(5/(2x))θ²` is cancelled, the
eq. 5 `deg C` drop on the log tower. -/
theorem logCase_residual_eq :
    cisZeroG (csubG logD [CField.zero, (CField.neg CField.one : QFunNZG ℚ)]) = true := by native_decide

/-- **★ The `θ = log v` step strictly lowers `deg_θ C`** (`native_decide`): `deg D = 1 < deg C = 2` over
`ℚ(x)[log x]`. The eq. 5 degree-lowering invariant on the genuine 2-level monomial tower. -/
theorem logCase_degree_drop : cdegG logD < cdegG logC := by native_decide

/-! #### ★ `θ = exp v` validates: `∫ C/(θy)` over `ℚ(x)[eˣ]`, `y = √(eˣ+1)` (`native_decide`)

The 2-level **exponential** tower: base `F = QFunNZG ℚ ≅ ℚ(x)`, monomial `θ = exp x` (so `v = x`,
`v' = 1`, `θ' = v'·θ = θ`); `F[θ] = ℚ(x)[eˣ]` is `CPolyG (QFunNZG ℚ)`. Radicand `y² = f = θ + 1 = eˣ + 1`
(`n = 2`, `θ ∤ f`, `f₀ = 1`, `m = 1`, `P₁ = θ+1`, `e₁ = 1`, θ-power `j = 0`), so `(f/y)' = g/y` with
`g = (1/2)θ` (the `−j/n·v'` term vanishes as `j = 0`; `g₀ = 0`). The `C/(θᵏy)` step with `k = 1`,
`C = θ + 1` (so `c₀ = 1`): the **constant-term match** `c₀ = b₀g₀ − k·v'·b₀·f₀` gives
`b₀ = c₀/(g₀ − kv'f₀) = 1/(0 − 1) = −1` (a genuine constant, `b₀' = 0`), so `B = [−1]`. The residual
`D = ((B'f + Bg − kv'Bf) − C)/θ = ((1/2)θ + 1 − (θ+1))/θ`... `= (−1/2)`, dropping `k = 1 → 0`. The exp
feature `θ ∣ θ'` enters through the `−k·v'·B·f` term. -/

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
  radExpResidual 8 1 expVder expF expG expB expC (cmonomialDeriv expDtPoly expB)

/-- **The `exp` cofactor is the constant `B = [−1]`** (`native_decide`): the exp constant-term match
`c₀ = b₀g₀ − k·v'·b₀·f₀` over `ℚ(x)[eˣ]` gives `b₀ = 1/(0 − 1·1·1) = −1` (`cisZeroG` of `B − (−1)`). The
witness `b₀` is a genuine constant (`b₀' = 0`), the constant-`b₀` slice of the exp reduction. -/
theorem expCase_cofactor_eq :
    cisZeroG (csubG expB [(CField.neg CField.one : QFunNZG ℚ)]) = true := by native_decide

/-- **★ The `θ = exp v` constant-term congruence**: `(B'f + Bg − kv'Bf) − C ≡ 0 (mod θ)`
(`native_decide`) — the numerator `B'f + Bg − kv'Bf − C = ((1/2)θ + 1) − (θ+1) = (−1/2)θ` has vanishing
`θ⁰`-coefficient (is divisible by `θ`), the defining property of the exp cofactor `b₀`. Checked by
`cisZeroG` of `cmodG (numerator) θ` over `ℚ(x)[eˣ]`. -/
theorem expCase_congruence :
    cisZeroG (cmodG 8
      (csubG (csubG (caddG (cmulG (cmonomialDeriv expDtPoly expB) expF) (cmulG expB expG))
          (cmulG [CField.mul (cnatCastG 1) expVder] (cmulG expB expF))) expC)
      [CField.zero, CField.one]) = true := by native_decide

/-- **★ The `θ = exp v` cleared `C/(θᵏy)` identity** (`native_decide`): the reduction
`(Bf/(θᵏy))' − C/(θᵏy) = D/(θ^{k−1}y)`, cleared over `θᵏy`, is the pure `ℚ(x)[eˣ]` identity
`(B'f + Bg − k·v'·B·f) − C = θ·D`. With `B = [−1]`, `D = [−1/2]`: LHS `= (1/2)θ + 1 − (θ+1) = (−1/2)θ`,
RHS `= θ·(−1/2) = (−1/2)θ`. Checked by `cisZeroG` of LHS − RHS over `ℚ(x)[eˣ]`. THE `θ = exp v` RATIONAL
REDUCTION COMPUTES on a genuine exponential tower — the `θ ∣ θ'` complication handled via the `−kv'Bf`
term, lowering the `θ`-power multiplicity `k = 1 → 0`. -/
theorem expCase_cleared_identity :
    cisZeroG (csubG
      (csubG (csubG (caddG (cmulG (cmonomialDeriv expDtPoly expB) expF) (cmulG expB expG))
          (cmulG [CField.mul (cnatCastG 1) expVder] (cmulG expB expF))) expC)
      (cmulG [CField.zero, CField.one] expD)) = true := by native_decide

/-- **The `exp` residual `D = −1/2` dropped the `θ`-power** (`native_decide`): `D = −1/2` (`cisZeroG` of
`D + 1/2`), a `θ`-constant — the exp `C/(θᵏy)` step lowered the `θ`-power multiplicity from `k = 1` to
`k − 1 = 0`, eliminating the `θ`-factor as Trager's §2.4 reduction guarantees. -/
theorem expCase_residual_eq :
    cisZeroG (csubG expD [qxOfNum [-1/2]]) = true := by native_decide

/-! ### `#print axioms` — the headline lemmas

Each headline result carries the standard `[propext, Classical.choice, Quot.sound]` plus its
`native_decide` compiler axiom — there is no `sorry` and no extra axiom. The radical carrier, the `Tᵢ`
decoupling, and **all** the rational-part reductions (Cases 1–3 for `θ' = 1`, plus `θ = log v` and the
`θ = exp v` `C/(θᵏy)` step) reduce in the native compiler over the existing tower engine. The
simple-radical **rational part** is thus realized across all four `θ`-level kinds; the logarithmic part
(Trager Ch. 5–6, residues / divisors) and the general first-order-ODE coefficient solves remain. -/

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
