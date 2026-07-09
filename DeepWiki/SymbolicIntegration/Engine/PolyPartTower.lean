import DeepWiki.SymbolicIntegration.Engine.Tower.Deriv

/-! # Computable polynomial reduction and primitive-case integration over ℚ(x)[t]

`cPolyReduceTower` reduces `p ∈ k[t]` for a nonlinear monomial to `(q, r)` with `p = D(q) + r`,
`deg(r) < deg(Dt)`; `cPrimitivePolyIntegrate` integrates a polynomial part for a primitive
monomial in the constant-coefficient sub-case. Both generic over `[CField α] [CDiffField α]`. -/

namespace DeepWiki.SymbolicIntegration


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

end DeepWiki.SymbolicIntegration
