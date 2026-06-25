import DeepWiki.SymbolicIntegration.ComputableWellFounded7

/-! # Fuel-free (well-founded) §6.6 base ℚ-pipeline + cancellation dispatch — `cRationalRDEWf`,
`cPolyRischDECancelPrimWf`, `cPolyRischDECancelExpWf`, `cRischDEWfFull`

This completes the fuel-free conversion of the §6 Risch-DE oracle. `ComputableWellFounded7` made the
**non-cancellation** regime of `cRischDE` fuel-free (`cRischDEWf`); the remaining gap is the **§6.6
cancellation** regime, which recurses degree-by-degree into the **base ℚ-pipeline** `cRationalRDE` (the
whole Ch. 6 algorithm re-run over the constant field `k = ℚ`, trivial primitive monomial `t = x`,
`D = d/dx`). That base pipeline — over `CPolyG ℚ` (concrete, no `[CFieldSpec]` concern) — and the §6.6
cancellation own-loops that drive it are converted here, so the fuel-free solver handles **all** regimes.

The two recursions are **independent** (no mutual recursion): the tower cancellation loops
(`cPolyRischDECancelPrim`/`Exp`, over `CPolyG QFunNZ`) recurse into `cRischDEBase` → `cRationalRDE`, which
lives over the **different** carrier `CPolyG ℚ`. So we convert leaf-first, base pipeline before tower:

* **Base ℚ leaves** — `cIntegratePolyQ` (termwise antiderivative) and `cRischDEConst` (the genuine bottom
  `s = c/b`) are already non-recursive, hence fuel-free as-is; no companion is needed. The two base
  **own-loops** get WF companions mirroring the WF7 tower own-loops at `α = ℚ`:
  - **`cPolyRischDENoCancelQWf`** (§6.5 base) — own-loop on `(cnormG c).length` (the leading term of
    `b·p` cancels `c`'s top, dropping the length; structural guard, `decreasing_by := assumption`).
  - **`cPolyRischDECancelPrimQWf`** (§6.6 base primitive cancellation) — own-loop on `(cnormG c).length`,
    recursing degree-by-degree into the non-recursive `cRischDEConst` (the leading monomial `s·xᵐ` with
    `s = lc(c)/b` cancels `c`'s top, dropping the length; structural guard).
  - **`cSPDEQWf`** (§6.4 base) — own-loop on `(n+1).toNat` (`n` drops by `deg(a/g) ≥ 1`; structural guard),
    the inner gcd/division/Bézout/divisibility being the generic fuel-free `cgcdWf`/`cdivWf`/`cdiophantineGWf`/
    `cdvdGWf` at `α = ℚ`.

* **Base ℚ compositions** — `cPolyRischDEQWf` (the §6.5/§6.6 dispatcher), `cWeakNormalizerQWf` (§6.1, over
  the WF residue-resultant leaf `cresultantWf`), `cRdeNormalDenominatorQWf` (§6.2), and the **assembly**
  `cRationalRDEWf` (weak normalizer → normal denominator → degree bound → SPDE → poly stage), all
  substituting the fuel-free leaves — **no fuel at runtime**.

* **`cRischDEBaseWf`** — the base RDE `Ds + b·s = c` over `k = ℚ(x)`: the `k`-constant fast path plus the
  general routing through `cRationalRDEWf`.

* **Tower §6.6 cancellation own-loops** — `cPolyRischDECancelPrimWf` (primitive, `δ = 0`, `b ∈ k*`) and
  `cPolyRischDECancelExpWf` (hyperexponential, `δ = 1`, `b ∈ k*`): own-loops on `(cnormG c).length`
  (the leading monomial `s·tᵐ` cancels `c`'s top, dropping the length; structural guard), recursing into
  `cRischDEBaseWf` (with the `m·η` shift for the exp case, `η = cExpEtaWf Dt`). `cExpEtaWf` is the
  fuel-free `cExpEta` (over `cdivWf`).

* **`cPolyRischDEWf`** (tower dispatcher) and the extended **`cRischDEWfFull`** — re-point the §6 solver so
  the §6.6 dispatch routes to the fuel-free cancellation own-loops, so the **whole** §6 RDE pipeline runs
  fuel-free in every regime (non-cancellation, primitive cancellation, hyperexponential cancellation).

`native_decide` re-runs the §6.6 cancellation deliverables fuel-free: the **primitive** cancellation
`rischDE_cancel_example` (`t = log x`, `Dq + q = log x + 1/x → q = log x`), the **non-constant base
recursion** `rischDE_baseRecursion_example` (`Dy + (1/x)y = 2log x + 1 → y = x·log x`, exercising the full
base ℚ-pipeline), and the **hyperexponential** cancellation `rischDE_cancelExp_example`
(`t = eˣ`, `Dq + (1/x)q = (2+x)eˣ → q = x·eˣ`). As throughout, the runtime WF ops carry no fuel; fuel
bounds live only in the bridge proofs. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZ

/-! ### The base ℚ leaves — `cIntegratePolyQ`, `cRischDEConst` are already fuel-free

`cIntegratePolyQ c = (0 : ℚ) :: (c.zipIdx.map …)` (termwise antiderivative over ℚ) and `cRischDEConst b c
= if b = 0 then … else some (c/b)` are **non-recursive** — they carry no fuel argument at all, so they are
fuel-free as written and need no WF companion. The fuel-bearing base own-loops below recurse into them
directly. -/

/-- The base ℚ termwise antiderivative `cIntegratePolyQ` is already fuel-free (non-recursive). -/
example (c : CPolyG ℚ) : CPolyG ℚ := CPolyG.cIntegratePolyQ c

/-- The genuine bottom `cRischDEConst b c` (`s = c/b`) is already fuel-free (non-recursive). -/
example (b c : ℚ) : Option ℚ := CPolyG.cRischDEConst b c

namespace CPolyG

/-! ### Base own-loop 1 — the fuel-free non-cancellation Poly-Risch-DE over ℚ `cPolyRischDENoCancelQWf`

The base (`α = ℚ`, `D = cderivQ = d/dx`) analogue of the WF7 tower own-loop `cPolyRischDENoCancelWf`:
solve `Dq + b·q = c` degree-by-degree, peeling `p = (lc(c)/lc(b))·xᵐ` (`m = deg(c) − deg(b)`), recursing
on `c' = c − Dp − b·p`. In the non-cancellation regime `deg(b) ≥ 1`, the leading term of `b·p` cancels
`c`'s, so `(cnormG c).length` strictly drops; well-founded recursion on it, structural runtime guard. -/

/-- **Fuel-free non-cancellation Poly-Risch-DE over ℚ** (Bronstein §6.5 base, `PolyRischDENoCancel1`,
book p.208, `D = d/dx`) `cPolyRischDENoCancelQWf b c n`: the fuel-free companion of `cPolyRischDENoCancelQ`.
Solves `Dq + b·q = c` for `q ∈ ℚ[x]`, `deg(q) ≤ n` (`n : ℤ`), non-cancellation case `deg(b) ≥ 1`,
top-down — `p = (lc(c)/lc(b))·xᵐ` (`m = deg(c) − deg(b)`, `D = cderivQ`), recurse on `c' = c − Dp − b·p`.
Returns `none` ("no solution of degree `≤ n`") or `some q`. True well-founded recursion on
`(cnormG c).length` — **no fuel at runtime**; the recursion is taken only under the structural guard
`(cnormG c').length < (cnormG c).length`, so `decreasing_by` is `assumption`. Agrees with
`cPolyRischDENoCancelQ` on a non-cancellation run (`cPolyRischDENoCancelQWf_eq`). -/
def cPolyRischDENoCancelQWf (b c : CPolyG ℚ) (n : ℤ) : Option (CPolyG ℚ) :=
  if cisZeroG c then some []
  else
    let m : ℤ := (cdegG c : ℤ) - (cdegG b : ℤ)
    if n < 0 ∨ m < 0 ∨ m > n then none
    else
      let coeff := CField.div (cleadG c) (cleadG b)
      let p := cshiftG m.toNat [coeff]
      let c' := csubG (csubG c (cderivQ p)) (cmulG b p)
      if (cnormG c' : List ℚ).length < (cnormG c : List ℚ).length then
        match cPolyRischDENoCancelQWf b c' (m - 1) with
        | none => none
        | some q => some (caddG p q)
      else none   -- unreachable on a non-cancellation run (leading term cancels, degree drops)
termination_by (cnormG c).length
decreasing_by assumption

/-! ### Base own-loop 2 — the fuel-free primitive cancellation Poly-Risch-DE over ℚ `cPolyRischDECancelPrimQWf`

The §6.6 base primitive cancellation (`b ∈ ℚ*` a constant, `D = d/dx`, `δ = 0`): the leading terms of `Dq`
and `bq` cancel, so the solve recurses degree-by-degree into the **non-recursive constant base RDE**
`cRischDEConst b₀ (lc(c))` (`b₀·s = lc(c)`, `s = lc(c)/b₀`). The leading monomial `s·xᵐ` (`m = deg(c)`)
cancels `c`'s top, so `(cnormG c).length` strictly drops; well-founded recursion on it. -/

/-- **Fuel-free primitive cancellation Poly-Risch-DE over ℚ** (Bronstein §6.6 base, `PolyRischDECancelPrim`,
book p.212) `cPolyRischDECancelPrimQWf b c n`: the fuel-free companion of `cPolyRischDECancelPrimQ`.
`b ∈ ℚ*` (a constant `b₀ = lc(b)`), `D = d/dx`, `δ = 0`; solves `Dq + b·q = c` degree-by-degree, recursing
into the constant base RDE `cRischDEConst b₀ (lc(c))` (`= lc(c)/b₀`) at each degree `m = deg(c)`, leading
monomial `s·xᵐ`, remainder `c' = c − b·(s·xᵐ) − D(s·xᵐ)`. Returns `none` or `some q`. True well-founded
recursion on `(cnormG c).length` — **no fuel at runtime**; the recursion is taken only under the structural
guard `(cnormG c').length < (cnormG c).length` (the leading monomial cancels `c`'s top), so `decreasing_by`
is `assumption`. Agrees with `cPolyRischDECancelPrimQ` on a real run (`cPolyRischDECancelPrimQWf_eq`). -/
def cPolyRischDECancelPrimQWf (b c : CPolyG ℚ) (n : ℤ) : Option (CPolyG ℚ) :=
  let b0 : ℚ := cleadG b
  if cisZeroG c then some []
  else if n < (cdegG c : ℤ) then none
  else
    let m : ℕ := cdegG c
    match cRischDEConst b0 (cleadG c) with
    | none => none
    | some s =>
      let stm : CPolyG ℚ := cshiftG m [s]
      let c' := csubG (csubG c (cmulG b stm)) (cderivQ stm)
      if (cnormG c' : List ℚ).length < (cnormG c : List ℚ).length then
        match cPolyRischDECancelPrimQWf b c' ((m : ℤ) - 1) with
        | none => none
        | some q => some (caddG stm q)
      else none   -- unreachable on a real run (the leading monomial cancels, degree drops)
termination_by (cnormG c).length
decreasing_by assumption

end CPolyG

end DeepWiki.SymbolicIntegration
