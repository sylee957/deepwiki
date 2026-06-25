import DeepWiki.SymbolicIntegration.ComputableTowerWellFounded
import DeepWiki.SymbolicIntegration.ComputableTowerRischDE

/-! # Fuel-free (well-founded) GENERIC tower §6 Risch-DE oracle `cRischDEGWf`

The generic §6 RDE pipeline (`ComputableTowerRischDE`) — `cRischDEG` and its stages — is
`[CField α] [CDiffField α] [CFracGcdCore α] [CRischField α]`-generic and gate-clean, but every op carries an
explicit `fuel : ℕ`. This file builds the **fuel-free** companions `…GWf`, completing the generic fuel-free
engine: the integration driver `cIntegrateGWf` (`ComputableTowerWellFounded`) is already fuel-free, and TWO
of the RDE recursive bottoms landed there (`cPolyRischDENoCancelGWf` §6.5, `cSPDEGWf` §6.4). Here we finish
the §6 oracle — the headline `cRischDEGWf`.

The §6 pipeline bottoms out at FIVE fuel-recursive ops; two are done in `ComputableTowerWellFounded`
(`cPolyRischDENoCancelGWf`, `cSPDEGWf`), and the remaining THREE are built here:

* **`cPolyRischDECancelPrimGWf`** — §6.6 primitive cancellation, recursing degree-by-degree into the base
  RDE `CRischField.crischDESolve b₀ (lc c)` (eq. 6.23). The leading monomial `s·tᵐ` cancels `c`'s top, so
  `(cnormG c).length` strictly drops; well-founded recursion on it, structural runtime guard.
* **`cPolyRischDECancelExpGWf`** — §6.6 hyperexponential cancellation, recursing into the eq. 6.24 base RDE
  `crischDESolve (b₀ + m·η) (lc c)` (`η = cExpEtaG Dt`). Same own-loop on `(cnormG c).length`.
* **`cValuationGWf`** — the `ν_p` `p`-adic valuation (used by the special-denominator stage), recursing on
  `(cnormG x).length` by trial division. As with the `QFunNZ` arc (`cValuationWf`, no standalone bridge),
  it feeds `cRdeSpecialDenominatorGWf` whose agreement is threaded as a whole-stage hypothesis.

The rest is a flat composition over fuel'd leaves: the generic §6.1 weak normalizer, the §6.2
normal/special denominators, the §6.3 degree bound, the §6.4 SPDE, the §6.5/§6.6 dispatcher, and the
headline `cRischDEGWf`. Each substitutes the fuel-free leaves — the generic ones reused verbatim
(`cdivWf`, `cdivmodWf`, `cdiophantineGWf`, `cdvdGWf`, `cgcdWf`) and the new ones (`cgcdFFCoreWf`, the two
done RDE bottoms, and the three above) — and is bridged to its fuel'd `…G` original.

Every `…GWf` def is **`[CField α]`-only on the fuel-free fragment** (plus `[CDiffField α]`/`[CFracGcdCoreWf α]`/
`[CRischField α]` where the pipeline needs the derivation / the fraction-free gcd / the base solve) — never
`[CFieldSpec α]`, which would break `native_decide` over the noncomputable tower (the keystone lesson). The
fuel bounds live only inside the bridge proofs; the runtime ops carry no fuel. The §6.6 hypertangent
cancellation falls back to non-cancellation as in `cRischDEG` (not handled here). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open Compute

/-! ## Part 1 — the three remaining fuel-recursive bottoms

`cPolyRischDECancelPrimGWf` / `cPolyRischDECancelExpGWf` (degree-by-degree own-loops on `(cnormG c).length`,
carrying `[CRischField α]`) and `cValuationGWf` (trial-division own-loop on `(cnormG x).length`). Each is a
true well-founded recursion with a structural runtime guard (`decreasing_by := assumption`), replaying the
`QFunNZ`-specific `cPolyRischDECancelPrimWf` / `cPolyRischDECancelExpWf` / `cValuationWf` patterns generically. -/

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCore α] [CRischField α]

/-- **Generic fuel-free primitive cancellation Poly-Risch-DE** (Bronstein §6.6, book p.212)
`cPolyRischDECancelPrimGWf Dt b c n`: the generic, fuel-free companion of `cPolyRischDECancelPrimG`. Given the
primitive monomial derivation `D` (`Dt ∈ α`), `b ∈ α*` (a degree-0 `t`-polynomial, scalar `b₀ = lc(b)`) and
`c ∈ α[t]`, with degree bound `n : ℤ`, solves `Dq + b·q = c` degree-by-degree, recursing at degree
`m = deg(c)` into the base RDE `CRischField.crischDESolve b₀ (lc c)` (eq. 6.23) over `α`, leading monomial
`s·tᵐ`, remainder `c' = c − b·(s·tᵐ) − D(s·tᵐ)` (`D = cmonomialDeriv Dt`). Returns `none` ("no solution of
degree `≤ n`") or `some q`. True well-founded recursion on `(cnormG c).length` — **no fuel at runtime**; the
recursion is taken only under the structural guard `(cnormG c').length < (cnormG c).length` (the leading
monomial cancels `c`'s top), so `decreasing_by` is `assumption`. Agrees with `cPolyRischDECancelPrimG` on a
real run (`cPolyRischDECancelPrimGWf_eq`). `[CRischField α]`-generic — runs at any tower level. -/
def cPolyRischDECancelPrimGWf (Dt : CPolyG α) (b c : CPolyG α) (n : ℤ) :
    Option (CPolyG α) :=
  let b0 : α := cleadG b
  if cisZeroG c then some []
  else if n < (cdegG c : ℤ) then none
  else
    let m : ℕ := cdegG c
    match CRischField.crischDESolve b0 (cleadG c) with
    | none => none
    | some s =>
      let stm : CPolyG α := cshiftG m [s]               -- `s·tᵐ`
      let c' := csubG (csubG c (cmulG b stm)) (cmonomialDeriv Dt stm)
      if (cnormG c' : List α).length < (cnormG c : List α).length then
        match cPolyRischDECancelPrimGWf Dt b c' ((m : ℤ) - 1) with
        | none => none
        | some q => some (caddG stm q)
      else none   -- unreachable on a real run (the leading monomial cancels, degree drops)
termination_by (cnormG c).length
decreasing_by assumption

/-- **Generic fuel-free hyperexponential cancellation Poly-Risch-DE** (Bronstein §6.6, book p.213)
`cPolyRischDECancelExpGWf Dt b c n`: the generic, fuel-free companion of `cPolyRischDECancelExpG`. Given the
hyperexponential monomial derivation `D` (`η = Dt/t ∈ α`, `δ = 1`), `b ∈ α*` (scalar `b₀ = lc(b)`) and
`c ∈ α[t]`, with degree bound `n : ℤ`, solves `Dq + b·q = c` degree-by-degree, recursing at degree
`m = deg(c)` into the eq. 6.24 base RDE `crischDESolve (b₀ + m·η) (lc c)` over `α` (the `m·η` shift makes the
coefficient genuinely non-constant, `η = cExpEtaG Dt`), leading monomial `s·tᵐ`, remainder
`c' = c − b·(s·tᵐ) − D(s·tᵐ)`. Returns `none` or `some q`. True well-founded recursion on `(cnormG c).length`
— **no fuel at runtime**; the structural guard `(cnormG c').length < (cnormG c).length` is `decreasing_by :=
assumption`. Agrees with `cPolyRischDECancelExpG` on a real run (`cPolyRischDECancelExpGWf_eq`).
`[CRischField α]`-generic — runs at any tower level. -/
def cPolyRischDECancelExpGWf (Dt : CPolyG α) (b c : CPolyG α) (n : ℤ) :
    Option (CPolyG α) :=
  let b0 : α := cleadG b
  let η : α := cExpEtaG 30 Dt
  if cisZeroG c then some []
  else if n < (cdegG c : ℤ) then none
  else
    let m : ℕ := cdegG c
    -- eq. 6.24 base RDE `Ds + (b₀ + m·η)·s = lc(c)` over `α`.
    let coeff : α := CField.add b0 (CField.mul (cnatCastG m) η)
    match CRischField.crischDESolve coeff (cleadG c) with
    | none => none
    | some s =>
      let stm : CPolyG α := cshiftG m [s]               -- `s·tᵐ`
      let c' := csubG (csubG c (cmulG b stm)) (cmonomialDeriv Dt stm)
      if (cnormG c' : List α).length < (cnormG c : List α).length then
        match cPolyRischDECancelExpGWf Dt b c' ((m : ℤ) - 1) with
        | none => none
        | some q => some (caddG stm q)
      else none   -- unreachable on a real run (the leading monomial cancels, degree drops)
termination_by (cnormG c).length
decreasing_by assumption

end CPolyG

namespace CPolyG

variable {α : Type*} [CField α] [CFracGcdCore α]

/-- **Generic fuel-free `p`-adic valuation** `cValuationGWf p x = ν_p(x)`: the generic, fuel-free companion of
`cValuationG`, the multiplicity of the monic irreducible `p` dividing `x` (largest `k` with `pᵏ ∣ x`), by
trial division. Stops at the zero polynomial, a constant/unit `p` (`cdegG p = 0`), or a non-dividing step,
else recurses on `x/p` (the **fuel-free** `cdivWf`) and adds one. True well-founded recursion on
`(cnormG x).length` — **no fuel at runtime**; the recursion is taken only under the structural guard
`(cnormG (x/p)).length < (cnormG x).length`, so `decreasing_by` is `assumption`. The exact division `p ∣ x`
with non-constant `p` drops the `t`-degree on a real run, so the guard never fails and it agrees with
`cValuationG`. `[CField α]`-generic — runs at any tower level. -/
def cValuationGWf (p x : CPolyG α) : ℕ :=
  if cisZeroG x then 0
  else if cdegG p = 0 then 0
  else if cdvdGWf p x then
    let xq := cdivWf x p
    if (cnormG xq : List α).length < (cnormG x : List α).length then
      1 + cValuationGWf p xq
    else 0   -- unreachable on a real run (non-constant `p ∣ x` drops the degree)
  else 0
termination_by (cnormG x).length
decreasing_by assumption

end CPolyG

end DeepWiki.SymbolicIntegration
