import DeepWiki.SymbolicIntegration.Computable.Tower.Deriv

/-! # Computable polynomial reduction and primitive-case integration over ℚ(x)[t]

`cPolyReduceTower` reduces `p ∈ k[t]` for a nonlinear monomial to `(q, r)` with `p = D(q) + r`,
`deg(r) < deg(Dt)`; `cPrimitivePolyIntegrate` integrates a polynomial part for a primitive
monomial in the constant-coefficient sub-case. Both generic over `[CField α] [CDiffField α]`. -/

namespace DeepWiki.SymbolicIntegration

open Compute

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α]

/-! ### The polynomial reduction

For a nonlinear monomial `t` (`δ(t) = deg(Dt) ≥ 2`, `λ(t) = lc(Dt)`), every `p ∈ k[t]` splits as
`p = D(q) + r` with `deg(r) < δ(t)`, peeling the leading term one step at a time. -/

/-- **Computable polynomial reduction** `cPolyReduceTower Dt fuel p = (q, r)` for a **nonlinear**
monomial `t` (`δ(t) = deg(Dt) ≥ 2`, `λ(t) = lc(Dt)`): `p = D(q) + r` with `deg(r) < δ(t)`, peeling
`q₀ = (lc(p)/(m·λ(t)))·tᵐ` (`m = deg(p) − δ(t) + 1`) whose monomial derivative `D(q₀)`
(`cmonomialDeriv Dt`) cancels the top of `p`, then recursing on `p − D(q₀)`. Fuel-bounded; generic. -/
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

/-! ### The primitive-case reduced-element integration

For a **primitive** monomial `t` (`Dt ∈ k`, `δ(t) = 0`, e.g. `t = log x`), integrating `p = ∑ aᵢtⁱ`
proceeds top-down. We implement the **constant-coefficient sub-case** `c = aₘ/((m+1)·Dt)`, `b = 0`. -/

/-- **Primitive-case polynomial integration** `cPrimitivePolyIntegrate Dt fuel p = (q, rem)` for a
**primitive** monomial `t` (`Dt ∈ k`, `δ(t) = 0`, e.g. `t = log x`, `Dt = 1/x`): integrate `p = ∑ aᵢtⁱ`
top-down by peeling `q₀ = c·t^(m+1)/(m+1)` for each leading term `aₘ` with `c = aₘ/((m+1)·Dt)`
(constant-coefficient sub-case `b = 0`). Returns `(q, rem)` with `D(q) + rem = p`, peeling all degrees
`≥ 1` (the degree-`0` term stays in `rem`). Fuel-bounded; generic. -/
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

/-! ### Validation of the reduction identity `D(q) + rem = p` over ℚ(x)[t] -/

open CPolyG

/-- A ℚ constant `n` as a `QFunNZG ℚ` element (denominator `[1]`, nonzero by
`cisZeroG_one_singleton`). -/
def qConstG (n : ℚ) : QFunNZG ℚ := ⟨([n], [(1 : ℚ)]), QFunNZG.cisZeroG_one_singleton⟩

/-- A ℚ(x) fraction `num/den` as a `QFunNZG ℚ` element (`den ≠ 0` by `native_decide`). -/
def qFracG (num den : List ℚ) (h : CPolyG.cisZeroG den = false := by native_decide) : QFunNZG ℚ :=
  ⟨(num, den), h⟩

/-! #### Primitive case `t = log x`, `Dt = 1/x`

`k = ℚ(x)`, `t = log x`, `Dt = 1/x`. Integrating `p = (1/x)·t²` gives `q = (1/3)t³`, `rem = 0`. -/

/-- Validation monomial derivative for the primitive case: `Dt = 1/x` (`t = log x`). As a
`CPolyG (QFunNZG ℚ)` it is the single `t⁰`-coefficient `1/x` (`num = [1]`, `den = x`). -/
def primitivePolyIntegrateExampleDt : CPolyG (QFunNZG ℚ) :=
  [qFracG [1] [0, 1]]                                             -- the rational function `1/x`

/-- The polynomial part `p = (1/x)·t²` over ℚ(x)[t] (`t = log x`): coefficients `[0, 0, 1/x]`. Its
primitive under `D = κ_D + (1/x)·d/dt` is `q = (1/3)·t³`, with remainder `0`. -/
def primitivePolyIntegrateExampleP : CPolyG (QFunNZG ℚ) :=
  [qConstG 0, qConstG 0, qFracG [1] [0, 1]]                       -- `[0, 0, 1/x]`

/-- `cPrimitivePolyIntegrate` satisfies `D(q) + rem = p` for the primitive monomial `t = log x`
(`Dt = 1/x`) and polynomial part `p = (1/x)·t²` over ℚ(x)[t], with `D = cmonomialDeriv Dt`; checked
by `cisZeroG` of the difference. -/
theorem primitivePolyIntegrate_example :
    (let res := CPolyG.cPrimitivePolyIntegrate primitivePolyIntegrateExampleDt 8
        primitivePolyIntegrateExampleP
      let q := res.1
      let rem := res.2
      let Dq := CPolyG.cmonomialDeriv primitivePolyIntegrateExampleDt q
      CPolyG.cisZeroG (CPolyG.csubG (CPolyG.caddG Dq rem) primitivePolyIntegrateExampleP)) = true := by
  native_decide

/-! #### Nonlinear case `t = tan x`, `Dt = t² + 1`

`k = ℚ(x)`, `t = tan x`, `Dt = 1 + t²` (`δ(t) = 2`). Reducing `p = t³` gives `q = (1/2)t²`, `r = −t`. -/

/-- Validation monomial derivative for the nonlinear case: `Dt = t² + 1` (`t = tan x`; `δ(t) = 2`,
`λ(t) = 1`). -/
def polyReduceTowerExampleDt : CPolyG (QFunNZG ℚ) := [qConstG 1, qConstG 0, qConstG 1]

/-- The polynomial part `p = t³` over ℚ(x)[t] (`t = tan x`), to be reduced. -/
def polyReduceTowerExampleP : CPolyG (QFunNZG ℚ) := [qConstG 0, qConstG 0, qConstG 0, qConstG 1]

/-- `cPolyReduceTower` satisfies `D(q) + r = p` with `deg(r) < δ(t)` for the nonlinear monomial
`t = tan x` (`Dt = t² + 1`, `δ(t) = 2`) and `p = t³` over ℚ(x)[t], returning `(q, r) = ((1/2)t², −t)`;
checked by `cisZeroG` of the difference with `D = cmonomialDeriv Dt`. -/
theorem polyReduceTower_example :
    (let res := CPolyG.cPolyReduceTower polyReduceTowerExampleDt 8 polyReduceTowerExampleP
      let q := res.1
      let r := res.2
      let Dq := CPolyG.cmonomialDeriv polyReduceTowerExampleDt q
      CPolyG.cisZeroG (CPolyG.csubG (CPolyG.caddG Dq r) polyReduceTowerExampleP)) = true := by
  native_decide

/-- The reduced remainder has `t`-degree `< δ(t)`: reducing `p = t³` under `Dt = t² + 1` (`δ(t) = 2`)
returns a remainder of degree `1`. -/
theorem polyReduceTower_example_remainder_degree :
    CPolyG.cdegG (CPolyG.cPolyReduceTower polyReduceTowerExampleDt 8 polyReduceTowerExampleP).2 = 1 := by
  native_decide

#print axioms polyReduceTower_example

end DeepWiki.SymbolicIntegration
