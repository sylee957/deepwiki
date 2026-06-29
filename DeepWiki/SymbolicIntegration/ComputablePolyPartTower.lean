import DeepWiki.SymbolicIntegration.ComputableHermiteTower
import DeepWiki.SymbolicIntegration.ComputableTowerDeriv

/-! # Computable polynomial reduction + special-part handling over ℚ(x)[t] (Bronstein §5.4, §5.8)
After the rational (`cHermiteReduceTower`, §5.3) and logarithmic (`cResidueResultantTower`/
`cLogArgTower`, §5.6) parts of `∫f`, the **canonical representation** `f = fₚ + fₛ + fₙ`
(`canonicalRepresentationFast`) still leaves the *polynomial part* `fₚ ∈ k[t]` and the *special part*
`fₛ` (reduced element with special denominator). This file makes the §5.4 **polynomial reduction** and
the §5.8 **primitive-case** reduced-element integration computable over the tower ℚ(x)[t].

* **`cPolyReduceTower Dt fuel p`** = Bronstein's `PolynomialReduce(p, D)` (§5.4, p.141): for a
  **nonlinear** monomial `t` (`δ(t) = deg(Dt) ≥ 2`, `λ(t) = lc(Dt)`), returns `(q, r)` with
  `p = D(q) + r` and `deg(r) < δ(t)` — degree-lowering by peeling the leading term `q₀ = (lc(p)/(m·
  λ(t)))·tᵐ`, `m = deg(p) − δ(t) + 1`, whose derivative `D(q₀)` (`cmonomialDeriv Dt`) cancels the top
  of `p`. The generic mirror of the recursion, needing only `[CField α] [CDiffField α]`.

* **`cPrimitivePolyIntegrate Dt fuel p`** = the degree-lowering loop of Bronstein's
  `IntegratePrimitivePolynomial(p, D)` (§5.8, p.158) for a **primitive** monomial `t` (`Dt ∈ k`,
  `δ(t) = 0`, e.g. `t = log x`, `Dt = 1/x`): integrate `p = ∑ aᵢtⁱ` top-down by `aₘ = Db + (m+1)c·Dt`
  giving `q₀ = c·t^(m+1)/(m+1) + b·tᵐ`. The full `LimitedIntegrate` solve for `(b, c)` is the deferred
  **Chapter-7** oracle; here we implement the antiderivative recurrence in the **constant-coefficient
  sub-case** (`Db = 0`, so `c = aₘ/((m+1)·Dt)`, `b = 0`) — exactly the integrals `∫ ∑ aᵢtⁱ dx` whose
  coefficient antiderivatives `∫aₘ` are immediate, returning `(q, rem)` with `D(q) + rem = p`.

**`native_decide` validations** (`polyReduceTower_example`, `primitivePolyIntegrate_example`):
PRIMITIVE `t = log x` (`Dt = 1/x`) integrating a polynomial part, and NONLINEAR `t = tan x`
(`Dt = t² + 1`) reducing one. Each checks the cleared identity `D(q) + rem = p` via
`cisZeroG (csubG …)` over the **generic** ℚ(x)[t] = `CPolyG (QFunNZG ℚ)` (`QFunNZG ℚ` has no
`DecidableEq`, hence the `cisZeroG∘csubG` form).

The full **integrability test** (deciding whether `∫p` is non-elementary via the residue criterion of
§5.7 / the Risch differential equation of §5.9, or the general `LimitedIntegrate` of §5.8) is the deep
part and is **deferred** — see the module note below. We implement the degree-lowering REDUCTION (the
`D(q) + rem` split) and validate it; abstract correctness is NOT proved. -/

namespace DeepWiki.SymbolicIntegration

open Compute

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α]

/-! ### The polynomial reduction (Bronstein §5.4, `PolynomialReduce`)

For a nonlinear monomial `t` over `k` (so `δ(t) = deg(Dt) ≥ 2`, `λ(t) = lc(Dt)`), every `p ∈ k[t]`
splits as `p = D(q) + r` with `deg(r) < δ(t)` (Theorem 5.4.1). One step peels the leading term: with
`n = deg(p)`, `m = n − δ(t) + 1`, and `c = lc(p)/(m·λ(t))`, set `q₀ = c·tᵐ`; then `D(q₀) = κ_D(c·tᵐ) +
m·c·t^(m−1)·Dt` has degree `n` and leading coefficient `m·c·λ(t) = lc(p)`, so `p − D(q₀)` has degree
`< n`, and we recurse. (`cmonomialDeriv Dt` realizes `D = κ_D + Dt·d/dt`.) -/

/-- **Computable polynomial reduction** `cPolyReduceTower Dt fuel p = (q, r)` (Bronstein §5.4,
`PolynomialReduce`, p.141) for a **nonlinear** monomial `t` (`δ(t) = deg(Dt) ≥ 2`, `λ(t) = lc(Dt)`):
`p = D(q) + r` with `deg(r) < δ(t)`, peeling the leading term `q₀ = (lc(p)/(m·λ(t)))·tᵐ` (`m = deg(p) −
δ(t) + 1`) whose monomial derivative `D(q₀)` (`cmonomialDeriv Dt`) cancels the top of `p`, then
recursing on `p − D(q₀)`. Fuel-bounded; generic over `[CField α] [CDiffField α]`, so it reduces. -/
def cPolyReduceTower (Dt : CPolyG α) : ℕ → CPolyG α → CPolyG α × CPolyG α
  | 0, p => ([], cnormG p)
  | fuel + 1, p =>
    let p := cnormG p
    let delta := cdegG Dt                                          -- `δ(t) = deg(Dt)`
    if (p : List α).length ≤ delta then ([], p)                    -- `deg(p) < δ(t)` ⇒ done
    else
      let n := cdegG p
      let m := n - delta + 1                                       -- `m = deg(p) − δ(t) + 1`
      let lam := cleadG Dt                                         -- `λ(t) = lc(Dt)`
      let c := CField.div (cleadG p) (CField.mul (cnatCastG m) lam) -- `lc(p)/(m·λ(t))`
      let q0 := cshiftG m [c]                                      -- `c·tᵐ`
      let p' := csubG p (cmonomialDeriv Dt q0)                     -- `p − D(q₀)`
      let (q, r) := cPolyReduceTower Dt fuel p'
      (caddG q0 q, r)

/-! ### The primitive-case reduced-element integration (Bronstein §5.8, `IntegratePrimitivePolynomial`)

For a **primitive** monomial `t` (`Dt ∈ k`, i.e. `δ(t) = 0`, e.g. `t = log x` with `Dt = 1/x`),
integrating `p = ∑ aᵢtⁱ ∈ k[t]` proceeds top-down: at degree `m` with leading coefficient `aₘ`, solve
`aₘ = Db + (m+1)·c·Dt` (the `LimitedIntegrate` step, a Chapter-7 oracle) and peel
`q₀ = c·t^(m+1)/(m+1) + b·tᵐ`, since `D(q₀) = c·(m+1)·tᵐ·(Dt/(m+1))·… ` reproduces the top coefficient.
We implement the **constant-coefficient sub-case** `Db = 0` (so `c = aₘ/((m+1)·Dt)`, `b = 0`), which
needs no oracle and handles `∫ ∑ aᵢtⁱ dx` whose coefficient antiderivatives `∫aₘ` are immediate. -/

/-- **Primitive-case polynomial integration** `cPrimitivePolyIntegrate Dt fuel p = (q, rem)` (the
degree-lowering loop of Bronstein's `IntegratePrimitivePolynomial`, §5.8, p.158) for a **primitive**
monomial `t` (`Dt ∈ k`, `δ(t) = 0`, e.g. `t = log x`, `Dt = 1/x`): integrate `p = ∑ aᵢtⁱ` top-down by
peeling `q₀ = c·t^(m+1)/(m+1)` for each leading term `aₘ` with `c = aₘ/((m+1)·Dt)` (the
constant-coefficient `LimitedIntegrate` sub-case `b = 0`; the general solve is the deferred Chapter-7
oracle). Returns `(q, rem)` with `D(q) + rem = p`, peeling all degrees `≥ 1` (degree-`0` term stays in
`rem`, being `∫a₀ ∈ k`, not eliminable in `k[t]`). Fuel-bounded; generic. -/
def cPrimitivePolyIntegrate (Dt : CPolyG α) : ℕ → CPolyG α → CPolyG α × CPolyG α
  | 0, p => ([], cnormG p)
  | fuel + 1, p =>
    let p := cnormG p
    if (p : List α).length ≤ 1 then ([], p)                        -- only the `t⁰` term left ⇒ done
    else
      let m := cdegG p                                             -- current top degree `m ≥ 1`
      let am := cleadG p                                           -- leading coefficient `aₘ`
      -- `q₀ = c·t^(m+1)/(m+1)` with `c = aₘ/((m+1)·Dt)` (constant-coeff `LimitedIntegrate`, `b = 0`).
      let mp1 : α := cnatCastG (m + 1)
      -- `Dt ∈ k` is a constant `t`-polynomial; use its constant coefficient `Dt(0) = lc(Dt)`.
      let dtConst := cleadG Dt
      let c := CField.div am (CField.mul mp1 dtConst)
      let q0 := cshiftG (m + 1) [c]                                -- `c·t^(m+1)`
      let p' := csubG p (cmonomialDeriv Dt q0)                     -- `p − D(q₀)`
      let (q, rem) := cPrimitivePolyIntegrate Dt fuel p'
      (caddG q0 q, rem)

end CPolyG

/-! ### `native_decide` validation — the cleared identity `D(q) + rem = p` over ℚ(x)[t]

Both checks pin the load-bearing reduction identity `D(q) + rem = p` (with `D = cmonomialDeriv Dt`),
cleared of denominators and checked by `cisZeroG` of the difference over ℚ(x)[t] — the integrand
parts are genuine `CPolyG (QFunNZG ℚ)` polynomials (no fractions among `q`, `rem`, `p`), so the identity
is the direct `cisZeroG (csubG (caddG (D q) rem) p)`. -/

open CPolyG

/-- A ℚ constant `n ∈ ℚ ⊂ ℚ(x)` as a `QFunNZG ℚ` element (the validation coefficient builder, mirroring
`QFunNZ.ofConstNZ` one tower level down; denominator `[1]` nonzero by `cisZeroG_one_singleton`). -/
def qConstG (n : ℚ) : QFunNZG ℚ := ⟨([n], [(1 : ℚ)]), QFunNZG.cisZeroG_one_singleton⟩

/-- A ℚ(x) fraction `num/den` as a `QFunNZG ℚ` element (mirroring `QFunNZ.ofNumDen`; `den ≠ 0` by
`native_decide`). -/
def qFracG (num den : List ℚ) (h : CPolyG.cisZeroG den = false := by native_decide) : QFunNZG ℚ :=
  ⟨(num, den), h⟩

/-! #### Primitive case `t = log x`, `Dt = 1/x` (Bronstein §5.8 setting)

`k = ℚ(x)`, `t = log x`, so `Dt = 1/x ∈ k` (a constant in `t`: `cdegG Dt = 0`). We integrate the
polynomial part `p = (1/x)·t² = (log x)²/x` over ℚ(x)[t]. The recurrence's leading step has `m = 2`,
`aₘ = 1/x`, and `c = aₘ/((m+1)·Dt) = (1/x)/(3·(1/x)) = 1/3` — a `ℚ`-constant, so the
constant-coefficient sub-case applies. With `q = c·t³ = (1/3)t³`, the coefficient antiderivative is a
constant (`κ_D((1/3)t³) = 0`) and `D((1/3)t³) = (1/3)·3t²·(1/x) = (1/x)t² = p`, so `rem = 0` and
`D(q) + rem = p`. (`∫ (log x)²/x dx = (log x)³/3`.) -/

/-- Validation monomial derivative for the primitive case: `Dt = 1/x` (a constant in `t`), i.e.
`t = log x`. As a `CPolyG (QFunNZG ℚ)` it is the single `t⁰`-coefficient `1/x` (`num = [1]`, `den = x`). -/
def primitivePolyIntegrateExampleDt : CPolyG (QFunNZG ℚ) :=
  [qFracG [1] [0, 1]]                                             -- the rational function `1/x`

/-- The polynomial part `p = (1/x)·t²` over ℚ(x)[t] (`t = log x`): coefficients `[0, 0, 1/x]`. Its
primitive under `D = κ_D + (1/x)·d/dt` is `q = (1/3)·t³` (a `ℚ`-constant `1/3` times `t³`), the
constant-coefficient sub-case, with remainder `0`. -/
def primitivePolyIntegrateExampleP : CPolyG (QFunNZG ℚ) :=
  [qConstG 0, qConstG 0, qFracG [1] [0, 1]]                       -- `[0, 0, 1/x]`

/-- **`cPrimitivePolyIntegrate` satisfies `D(q) + rem = p`** (`native_decide`): for the primitive
monomial `t = log x` (`Dt = 1/x`) and polynomial part `p = (1/x)·t²` over ℚ(x)[t], the computed
`(q, rem)` satisfies the reduction identity `D(q) + rem = p` for the monomial derivation
`D = cmonomialDeriv Dt`. Checked by `cisZeroG` of `D(q) + rem − p` over ℚ(x)[t]. This is the
deliverable for the special/reduced primitive case: the degree-lowering integration loop executes over
the tower and `D(q) + rem` genuinely reconstructs the polynomial part. -/
theorem primitivePolyIntegrate_example :
    (let res := CPolyG.cPrimitivePolyIntegrate primitivePolyIntegrateExampleDt 8
        primitivePolyIntegrateExampleP
      let q := res.1
      let rem := res.2
      let Dq := CPolyG.cmonomialDeriv primitivePolyIntegrateExampleDt q
      CPolyG.cisZeroG (CPolyG.csubG (CPolyG.caddG Dq rem) primitivePolyIntegrateExampleP)) = true := by
  native_decide

/-! #### Nonlinear case `t = tan x`, `Dt = t² + 1` (Bronstein §5.4 / Example 5.4.1 setting)

`k = ℚ(x)`, `t = tan x`, so `Dt = 1 + t²` (`δ(t) = 2`, `λ(t) = 1`). We reduce the polynomial part
`p = t³` over ℚ(x)[t]: `m = 3 − 2 + 1 = 2`, `c = lc(p)/(m·λ) = 1/2`, `q₀ = (1/2)t²`, and
`D((1/2)t²) = (1/2)·2t·(t²+1) = t³ + t`, so `p − D(q₀) = −t` has degree `1 = δ(t) − 1`. One more step is
impossible (`deg(−t) = 1 < δ(t) = 2`), so the reduction returns `q = (1/2)t²`, `r = −t`, satisfying
`D(q) + r = t³ + t − t = t³ = p`. -/

/-- Validation monomial derivative for the nonlinear case: `Dt = t² + 1` (`t = tan x`; `δ(t) = 2`,
`λ(t) = 1`), Bronstein Example 5.4.1 setting. -/
def polyReduceTowerExampleDt : CPolyG (QFunNZG ℚ) := [qConstG 1, qConstG 0, qConstG 1]

/-- The polynomial part `p = t³` over ℚ(x)[t] (`t = tan x`), to be reduced by §5.4. -/
def polyReduceTowerExampleP : CPolyG (QFunNZG ℚ) := [qConstG 0, qConstG 0, qConstG 0, qConstG 1]

/-- **`cPolyReduceTower` satisfies `D(q) + r = p` with `deg(r) < δ(t)`** (`native_decide`): for the
nonlinear monomial `t = tan x` (`Dt = t² + 1`, `δ(t) = 2`) and polynomial part `p = t³` over ℚ(x)[t],
Bronstein's `PolynomialReduce` returns `(q, r) = ((1/2)t², −t)` satisfying the §5.4 reduction identity
`D(q) + r = p` for `D = cmonomialDeriv Dt`. Checked by `cisZeroG` of `D(q) + r − p` over ℚ(x)[t]. The
remainder `r = −t` has `t`-degree `1 < δ(t) = 2`, as Theorem 5.4.1 guarantees. This is the deliverable:
the polynomial reduction executes over the tower, lowering the degree of the polynomial part with
`D(q) + r` genuinely reconstructing it. -/
theorem polyReduceTower_example :
    (let res := CPolyG.cPolyReduceTower polyReduceTowerExampleDt 8 polyReduceTowerExampleP
      let q := res.1
      let r := res.2
      let Dq := CPolyG.cmonomialDeriv polyReduceTowerExampleDt q
      CPolyG.cisZeroG (CPolyG.csubG (CPolyG.caddG Dq r) polyReduceTowerExampleP)) = true := by
  native_decide

/-- **The reduced remainder has `t`-degree `< δ(t)`** (`native_decide`): the §5.4 reduction of `p = t³`
under `Dt = t² + 1` (`δ(t) = 2`) returns a remainder `r` of degree `1`, strictly below `δ(t) = 2`, as
Theorem 5.4.1 guarantees. -/
theorem polyReduceTower_example_remainder_degree :
    CPolyG.cdegG (CPolyG.cPolyReduceTower polyReduceTowerExampleDt 8 polyReduceTowerExampleP).2 = 1 := by
  native_decide

#print axioms polyReduceTower_example

end DeepWiki.SymbolicIntegration
