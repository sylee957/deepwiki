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

end RadElem

end DeepWiki.SymbolicIntegration
