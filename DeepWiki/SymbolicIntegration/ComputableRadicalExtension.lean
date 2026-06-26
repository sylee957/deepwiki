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

/-! ### Case 2 rational-part reduction (Trager Appendix A §2.2, `θ' = 1`)

**Case 2** is the partial-fraction piece `C/(Wᵏy)` where `W = Pⱼ` is a **squarefree factor of the
radicand `f`** (not coprime to `f`, unlike Case 1). Writing `h = f/W`, the reduction step is
`(Bf/(Wᵏy))' = (Bg − kW'h)/(Wᵏy) + B'h/(W^{k−1}y)` (Trager Appendix A §2.2), so subtracting `C/(Wᵏy)`
leaves `D/(W^{k−1}y)` provided
`Bg − kW'h ≡ C (mod W)`,
i.e. `B·g ≡ (C + kW'h) (mod W)`. Since `W = Pⱼ` gives `g ≡ (1 − eⱼ/n)W'h (mod W)` and `gcd(g, W) = 1`
(`W'`, `h` both coprime to the squarefree `W`, `eⱼ < n`), the congruence is solvable for **any `k`**.
The residual numerator is `D = (Bg − kW'h − C)/W + B'h`. Cleared over the common denominator `Wᵏy`, the
step is the **pure `F[θ]` identity** `Bg − kW'h − C + W·(B'h) = W·D` (no `y`), checkable by `cisZeroG`.
Repeated application eliminates every `f`-factor from the integrand's denominator. -/

/-- **Case-2 cofactor solve** `radCase2Cofactor fuel k W g h Wder C = B` — the polynomial `B`
(degree `< deg W`) solving the Case-2 congruence `B·g ≡ (C + k·W'·h) (mod W)` (Trager Appendix A §2.2),
via `cdiophantineG g W (C + k·W'·h)` (`gcd(g, W) = 1` since `W = Pⱼ` is a squarefree factor of `f`).
`h = f/W`, `Wder = W'`, and `g` (from `(f/y)' = g/y`) are passed in. Generic over `[CField α]`. -/
def radCase2Cofactor (fuel : ℕ) (k : ℕ) (W g h Wder C : CPolyG α) : CPolyG α :=
  let rhs := caddG C (cmulG [cnatCastG k] (cmulG Wder h))         -- `C + k·W'·h`
  (cdiophantineG fuel g W rhs).1

/-- **Case-2 residual** `radCase2Residual fuel k W g h Wder B C Bder = D` — the lowered-`k` residual
numerator `D = (B·g − k·W'·h − C)/W + B'·h` of the Case-2 step (Trager Appendix A §2.2). `h = f/W`,
`Wder = W'`, `Bder = B'`, and `g` are passed in. The exact division by `W` is `cdivG` (`W ∣ Bg − kW'h − C`
by the cofactor congruence). Generic over `[CField α]`. -/
def radCase2Residual (fuel : ℕ) (k : ℕ) (W g h Wder B C Bder : CPolyG α) : CPolyG α :=
  let topNum := csubG (csubG (cmulG B g) (cmulG [cnatCastG k] (cmulG Wder h))) C  -- `Bg − kW'h − C`
  let quotient := cdivG fuel topNum W                                            -- `(Bg − kW'h − C)/W`
  caddG quotient (cmulG Bder h)                                                  -- `… + B'h`

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

`F = ℚ` (constants), `θ = x` (`θ' = 1`), radicand `y² = f = x³ − x = x(x−1)(x+1)` (`n = 2`, `m = 3`).
The squarefree factor `W = x` (so `W ∣ f`, `e₁ = 1`), `h = f/W = x² − 1`, `W' = 1`,
`g = ((n−1)/n)·f' = (1/2)(3x² − 1)` (all `eᵢ = 1`, `d = 1`). Take `k = 2`, `C = 1`, so the integrand is
`1/(x²√(x³−x))`. The congruence `B·g ≡ C + kW'h (mod W=x)` reads `−(1/2)B ≡ 1 + 2(−1) = −1 (mod x)`, so
`B = 2`. The residual `D = (Bg − kW'h − C)/W + B'h = (x²)/x + 0 = x`, of degree `< deg W·?`... it lowered
the multiplicity `k = 2 → 1`. -/

/-- Case-2 example radicand `f = x³ − x = x(x−1)(x+1)` (`y² = f`), as a `ℚ[x]` polynomial `[0,−1,0,1]`. -/
def case2F : CPolyG ℚ := [0, -1, 0, 1]

/-- Case-2 example squarefree denominator factor `W = x` (a factor of `f`), `[0, 1]`. -/
def case2W : CPolyG ℚ := [0, 1]

/-- Case-2 example cofactor `h = f/W = x² − 1`, `[−1, 0, 1]`. -/
def case2H : CPolyG ℚ := [-1, 0, 1]

/-- Case-2 example numerator `C = 1`, `[1]`. -/
def case2C : CPolyG ℚ := [1]

/-- `W' = x' = 1` over `ℚ[x]` (`cderivG`, `θ' = 1`). -/
def case2Wder : CPolyG ℚ := cderivG case2W

/-- `g = ((n−1)/n)·f' = (1/2)·(3x² − 1)` for `n = 2`, `f = x³ − x` (`(f/y)' = g/y`). -/
def case2G : CPolyG ℚ := cscaleG (1/2 : ℚ) (cderivG case2F)

/-- The solved Case-2 cofactor `B` for `−(1/2)B ≡ −1 (mod x)` — expected `B = 2`. -/
def case2B : CPolyG ℚ := radCase2Cofactor 8 2 case2W case2G case2H case2Wder case2C

/-- The Case-2 residual `D` — expected the linear `x`. -/
def case2D : CPolyG ℚ :=
  radCase2Residual 8 2 case2W case2G case2H case2Wder case2B case2C (cderivG case2B)

/-- **The cofactor is `B = 2`** (`native_decide`): the diophantine solve of `B·g ≡ −1 (mod x)` gives
`B = 2` (`cisZeroG` of `B − 2`). The Case-2 congruence solver runs over `ℚ[x]`. -/
theorem case2_cofactor_eq :
    cisZeroG (csubG case2B [(2 : ℚ)]) = true := by native_decide

/-- **★ The Case-2 congruence holds**: `B·g − k·W'·h − C ≡ 0 (mod W)` (`native_decide`) — the numerator
`Bg − kW'h − C = 2·(1/2)(3x²−1) − 2(x²−1) − 1 = x²` is divisible by `W = x`, the defining property of
the cofactor `B`. Checked by `cisZeroG` of `cmodG (Bg − kW'h − C) W`. -/
theorem case2_congruence :
    cisZeroG (cmodG 8
      (csubG (csubG (cmulG case2B case2G) (cmulG [cnatCastG 2] (cmulG case2Wder case2H))) case2C)
      case2W) = true := by native_decide

/-- **★ The Case-2 cleared Hermite identity** (`native_decide`): the reduction
`(Bf/(Wᵏy))' − C/(Wᵏy) = D/(W^{k−1}y)`, cleared over the common denominator `Wᵏy`, is the pure `ℚ[x]`
identity `Bg − kW'h − C + W·(B'h) = W·D`. With `B = 2`, `D = x`: LHS `= x² + x·0 = x²`, RHS `= x·x = x²`.
Checked by `cisZeroG` of LHS − RHS over `ℚ[x]`. THE CASE-2 RATIONAL REDUCTION COMPUTES — it eliminates
the `f`-factor `W = x` from the denominator, lowering its multiplicity `k = 2 → 1`. -/
theorem case2_cleared_identity :
    cisZeroG (csubG
      (caddG
        (csubG (csubG (cmulG case2B case2G) (cmulG [cnatCastG 2] (cmulG case2Wder case2H))) case2C)
        (cmulG case2W (cmulG (cderivG case2B) case2H)))
      (cmulG case2W case2D)) = true := by native_decide

/-- **The residual `D = x` has multiplicity dropped** (`native_decide`): `D = x` (`cisZeroG` of `D − x`),
so the Case-2 step lowered the apparent denominator multiplicity of `W = x` from `k = 2` to `k − 1 = 1`,
eliminating one `f`-factor exactly as Trager's reduction guarantees. -/
theorem case2_residual_eq :
    cisZeroG (csubG case2D [(0 : ℚ), 1]) = true := by native_decide

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

/-! ### `#print axioms` — the headline lemmas

Each headline result carries the standard `[propext, Classical.choice, Quot.sound]` plus its
`native_decide` compiler axiom — there is no `sorry` and no extra axiom. The radical carrier, the `Tᵢ`
decoupling, and the Case-1 rational reduction all reduce in the native compiler over the existing
tower engine. -/

-- Carrier: `y·y = f` and the diagonal `D(y) = (f'/(2f))·y` over ℚ(x):
#print axioms radGen_sq_eq_radicand
#print axioms radDeriv_radGen_eq

-- `Tᵢ` decoupling: the derivation-commutation and the `∫(g₀+g₁y)` split:
#print axioms radProj_one_radDeriv_comm
#print axioms radDeriv_decouples

-- Case-1 rational reduction: the cofactor congruence and the cleared Hermite identity:
#print axioms case1_congruence
#print axioms case1_cleared_identity

end DeepWiki.SymbolicIntegration
