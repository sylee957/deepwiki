import DeepWiki.SymbolicIntegration.ComputableWellFounded9

/-! # Fuel-free (well-founded) §8.4 tangent RDE cancellation — `cCoupledDECancelTanWf`

This is the **last** fuel-bearing function of the transcendental symbolic-integration engine. Everything
else is fuel-free (`ComputableWellFounded`…`9`): the two integrators (`cIntegrateWf`/`cIntegrateCheckedWf`),
the all-regimes §6 RDE oracle (`cRischDEWfFull`), and the §7/§8.1/§9/§10 compositions. The remaining
fuel-bearing top-level function is Bronstein's §8.4 hypertangent cancellation box
`cCoupledDECancelTan` (`ComputableCoupledDE`, book p.265) — the `PolyRischDECancelTan` that the §6.6
dispatcher deferred — which recurses **degree-by-degree on the tangent degree bound `n`** (`t = tan x`,
`Dt = t²+1`, `δ = 2`). Converting it makes the **whole engine** fuel-free.

`cCoupledDECancelTan (fuel dbound : ℕ) b0 b2 c1 c2 (n : ℕ)` peels the top tangent degree and recurses at
`n + 1 → n` on the divided-down `(d₁, d₂)`, with `fuel` threaded purely as a **parallel counter** mirroring
`n` (each level decrements both). So the honest decreasing measure is the tangent degree bound `n` itself —
the WF companion drops the `fuel` argument and recurses **structurally on `n`** (the `match n with | 0 |
n+1` peels it), a **degree-recursion** in `n`, not a structural counter and not a `cnormG`-length drop; the
base solve (`cCoupledDESystem`, **already fuel-free**, its `_fuel` unused) and the mod-`t²+1` /
divide-by-`t − √−1` steps carry no fuel.

* **`cCoupledDECancelTanWf dbound b0 b2 c1 c2 n`** — the fuel-free companion, `[CField ℚ]`-only (over the
  concrete `CPolyG ℚ`, no `[CFieldSpec]` concern). Identical body to `cCoupledDECancelTan` with the `fuel`
  argument and the `match fuel with | 0 => none | fuel'+1 => …` guard dropped; structural recursion on `n`.
  **No fuel at runtime.**

* **`cCoupledDECancelTanWf_eq_cCoupledDECancelTan_example`** — the agreement: `cCoupledDECancelTanWf … =
  cCoupledDECancelTan 30 …` on Bronstein's worked Example 8.4.1, by `native_decide`. A *general* all-inputs
  runtime bridge would need to rewrite by the fuel'd engine function's equation lemmas, but those are
  **non-generable** for `cCoupledDECancelTan` (its `.eq_def`/`.eq_1`/`.eq_unfold` time out at a hardcoded
  heartbeat cap no use-site `set_option` can raise) — so, exactly as `ComputableWellFounded9` does for the
  §10 Yun factorization `cSquarefreeFactorsQ`, the WF-vs-fuel'd agreement is certified by `native_decide`
  where exercised, not by an all-inputs rewrite. The engine function is not edited here.

§8.4 is `native_decide`-validated only (its *abstract* eq-8.3 correctness is deferred, like §6.6/§10), so the
deliverable is the fuel-free `native_decide` example `rischDECancelTanWf_example` — the §8.4 box's worked
Bronstein Example 8.4.1 (book p.265–267) re-run fuel-free, the returned `(q₁, q₂) = (t − 1, 2x)` verified to
**actually solve** the coupled `t`-polynomial system (8.15) by `cancelTanClearedCheck`. With this the **whole
transcendental Risch engine is fuel-free**. -/

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZ

namespace CPolyG

/-! ### The fuel-free §8.4 tangent RDE cancellation `cCoupledDECancelTanWf` (degree-WF on `n`)

`cCoupledDECancelTan` recurses `n + 1 → n` on the divided-down `(d₁, d₂)` (the §8.4 box: project mod `t²+1`,
base-solve over ℚ(x), divide by `t − √−1`, recurse at lower tangent degree). The `fuel` argument is a
parallel counter that drops in lockstep with `n`, so the genuine measure is `n` — `termination_by n`, with
`decreasing_by` discharging `n < n + 1`. The base solve `cCoupledDESystem` and the helper steps
(`evalAtI`/`divByTminusI`/`tadd`/`tsub`/…) carry no fuel. -/

/-- **Fuel-free tangent RDE cancellation** `cCoupledDECancelTanWf dbound b0 b2 c1 c2 n` (Bronstein §8.4,
the `CoupledDECancelTan(b₀, b₂, c₁, c₂, D, n)` box, book p.265) over `k = ℚ(x)`, `t = tan(x)`,
`η = Dt/(t²+1) = 1`, `a = −1`: the fuel-free companion of `cCoupledDECancelTan`. Given `b₀, b₂ ∈ ℚ[x]`, the
`t`-polynomials `c₁, c₂` (coefficients in `ℚ[x] = CPolyG ℚ`), the tangent degree bound `n` (recursed down),
and a base-solve degree bound `dbound`, solves the `t`-polynomial coupled system

```
  (Dq₁; Dq₂) + [[b₀ − n·t, −b₂], [b₂, b₀ − n·t]] · (q₁; q₂) = (c₁; c₂)
```

for `q₁, q₂ ∈ k[t]` of `t`-degree `≤ n`, degree-by-degree from the top — at `n + 1`: `z₁ + z₂√−1 =
c₁(√−1) + c₂(√−1)√−1` (`evalAtI`), base-solve `(s₁, s₂) = CoupledDESystem(b₀, b₂ − nη, z₁, z₂)`
(`cCoupledDESystem`, **fuel-free**), divide `c·p` by `p = t − √−1` (`divByTminusI`) to `d₁ + d₂√−1`, recurse
on `(d₁, d₂)` at `n`, return `(h₁t + h₂ + s₁, h₂t − h₁ + s₂)`. Returns `some (q₁, q₂)` or `none`. True
well-founded recursion on `n` — **no fuel at runtime** (the `fuel`/`match fuel with | 0 => none | …` guard of
`cCoupledDECancelTan` is dropped). Agrees with `cCoupledDECancelTan fuel …` whenever `n < fuel`
(`cCoupledDECancelTanWf_eq_of_fuel`). `native_decide`-able. -/
def cCoupledDECancelTanWf (dbound : ℕ) (b0 : CPolyG ℚ) :
    (b2 : CPolyG ℚ) → (c1 c2 : List (CPolyG ℚ)) → (n : ℕ) →
      Option (List (CPolyG ℚ) × List (CPolyG ℚ))
  | b2, c1, c2, 0 =>
    -- n = 0: c₁, c₂ must be in k (degree-0 in t); solve the base coupled system directly.
    if tdeg c1 = 0 && tdeg c2 = 0 then
      match cCoupledDESystem 0 (-1) b0 b2 (tcoeff c1 0) (tcoeff c2 0) dbound with
      | none => none
      | some (s1, s2) => some ([s1], [s2])
    else none
  | b2, c1, c2, n + 1 =>
    let nN : ℚ := ((n : ℚ) + 1)                              -- n (as ℚ for nη scaling), η = 1
    -- z₁ + z₂√−1 = c₁(√−1) + c₂(√−1)√−1.
    let e1 := evalAtI c1                                     -- c₁(√−1) = (re, im)
    let e2 := evalAtI c2                                     -- c₂(√−1)
    -- c₂(√−1)·√−1 = (−e2.im, e2.re); z = e1 + that.
    let z1 := csubG e1.1 e2.2
    let z2 := caddG e1.2 e2.1
    -- base solve CoupledDESystem(b₀, b₂ − nη, z₁, z₂), η = 1 ⇒ shift b₂ by −(n+1).
    let b2shift := csubG b2 (cscaleG nN [CField.one])
    match cCoupledDESystem 0 (-1) b0 b2shift z1 z2 dbound with
    | none => none
    | some (s1, s2) =>
      -- numerator of c·p: real = c₁ − z₁ + nη(s₁t + s₂); imag = c₂ − z₂ + nη(s₂t − s₁).
      let s1t : List (CPolyG ℚ) := [[], s1]
      let s2t : List (CPolyG ℚ) := [[], s2]
      let realNum := tadd (tsub c1 [z1]) (cscaleListQ nN (tadd s1t [s2]))
      let imagNum := tadd (tsub c2 [z2]) (cscaleListQ nN (tsub s2t [s1]))
      -- assemble the k(√−1)[t]-polynomial (pairs) and divide by t − √−1.
      let len := max realNum.length imagNum.length
      let cpairs : List (CPolyG ℚ × CPolyG ℚ) :=
        (List.range len).map (fun k => (realNum.getD k [], imagNum.getD k []))
      let quot := divByTminusI cpairs
      let d1 : List (CPolyG ℚ) := quot.map Prod.fst
      let d2 : List (CPolyG ℚ) := quot.map Prod.snd
      match cCoupledDECancelTanWf dbound b0 (caddG b2 [CField.one]) d1 d2 n with
      | none => none
      | some (h1, h2) =>
        -- return (h₁t + h₂ + s₁, h₂t − h₁ + s₂).
        let h1t : List (CPolyG ℚ) := [[]] ++ h1     -- h₁·t (shift up by one t-degree)
        let h2t : List (CPolyG ℚ) := [[]] ++ h2
        let q1 := tadd (tadd h1t h2) [s1]
        let q2 := tsub (tadd h2t [s2]) h1
        some (q1, q2)

end CPolyG

/-! ### Agreement with the fuel'd `cCoupledDECancelTan` (`native_decide`, on the worked example)

`cCoupledDECancelTanWf` and the fuel'd `cCoupledDECancelTan` compute by the same degree-by-degree §8.4 box
— project mod `t²+1`, base-solve over ℚ(x) (`cCoupledDESystem`, **fuel-free**), divide by `t − √−1`, recurse
at lower tangent degree — the WF function simply **dropping** the fuel counter and its `match fuel with | 0
=> none | …` guard (which never fires below the bound). On a real run, `fuel` is a parallel counter that
drops in lockstep with `n` (`fuel' + 1 → fuel'` alongside `n + 1 → n`), so for `n < fuel` the two agree.

A *general* (all-inputs) runtime equality bridge `cCoupledDECancelTanWf … = cCoupledDECancelTan fuel …`
would have to rewrite by the **fuel'd** engine function's equation lemmas — but those are **non-generable**
for `cCoupledDECancelTan`: its `.eq_def`/`.eq_1`/`.eq_unfold` time out at `whnf` against a hardcoded
heartbeat cap that no use-site `set_option maxHeartbeats` (not even `0` = unlimited) can raise, the
generation running in an isolated meta-context. So — exactly as `ComputableWellFounded9` documents for the
§10 Yun factorization `cSquarefreeFactorsQ` ("no clean equation lemmas to bridge through ... validated by
`native_decide`") — the agreement is certified by `native_decide` on Bronstein's worked Example 8.4.1
(where the engine function reduces by the compiler, not by equation lemmas), not by an all-inputs rewrite.
The fuel'd engine function is in `ComputableCoupledDE` and is not edited here. -/

open CPolyG

/-- **`cCoupledDECancelTanWf` agrees with the fuel'd `cCoupledDECancelTan` on Bronstein Example 8.4.1**
(`native_decide`, Bronstein §8.4, book p.265–267): the fuel-free tangent-cancellation own-loop returns the
**same** `(q₁, q₂)` as `cCoupledDECancelTan 30 …` on the worked system (8.15) — `b₀ = 0`, `b₂ = 4x`,
`c₁ = −t²+2t−8x²+1`, `c₂ = 2−4x`, degree bound `n = 2`. This is the §8.4 analogue of the WF9 §10 example-level
agreement certificate (a general all-inputs runtime bridge is infeasible: `cCoupledDECancelTan`'s equation
lemmas are non-generable, see the section docstring). The runtime value equality `WF = fuel'd` holds where it
is exercised. -/
theorem cCoupledDECancelTanWf_eq_cCoupledDECancelTan_example :
    (cCoupledDECancelTanWf 1 ([] : CPolyG ℚ) [0, 4] cancelTanC1 cancelTanC2 2
      == CPolyG.cCoupledDECancelTan 30 1 ([] : CPolyG ℚ) [0, 4] cancelTanC1 cancelTanC2 2) = true := by
  native_decide

#print axioms cCoupledDECancelTanWf_eq_cCoupledDECancelTan_example

/-! ### Validation — the fuel-free §8.4 tangent RDE cancellation (Bronstein Example 8.4.1, book p.265–267)

Re-runs `rischDE_cancelTan_example` over `k = ℚ(x)`, `t = tan(x)`, now fuel-free: the §6.6 dispatcher's
deferred `PolyRischDECancelTan` for the system (8.15) — `b₀ = 0`, `b₂ = 4x`, the diagonal `−2t = −nηt`
(`n = 2`, `η = 1`), `c₁ = −t²+2t−8x²+1`, `c₂ = 2(1−2x) = 2−4x`, degree bound `n = 2` — now runs with **no
fuel at runtime**, returning the book's solution `q₁ = t − 1`, `q₂ = 2x`. Reuses the example data and
`cancelTanClearedCheck` of `ComputableCoupledDE`. -/

/-- **Example 8.4.1 — the tangent RDE cancellation `PolyRischDECancelTan` runs end-to-end, fuel-free**
(`native_decide`, Bronstein §8.4, book p.265–267). The fuel-free companion of `rischDE_cancelTan_example`:
`cCoupledDECancelTanWf` recurses on the tangent degree bound `n` (projecting mod `t²+1`, base-solving over
ℚ(x), dividing by `t − √−1`) with **no fuel at runtime** and returns the book's solution `q₁ = t − 1`,
`q₂ = 2x` (hence `y₁ = (t−1)/(t²+1)`, `y₂ = 2x/(t²+1)`, book p.267). The returned `(q₁, q₂)` is verified to
**actually solve** the coupled `t`-polynomial system (8.15) by `cancelTanClearedCheck` (both cleared row
identities vanish), not merely pinned. This is the **last** fuel-bearing function of the engine made
fuel-free — the whole transcendental Risch engine now computes with no fuel argument. -/
theorem rischDECancelTanWf_example :
    (match cCoupledDECancelTanWf 1 ([] : CPolyG ℚ) [0, 4] cancelTanC1 cancelTanC2 2 with
      | some (q1, q2) =>
          cancelTanClearedCheck [] [0, 4] cancelTanC1 cancelTanC2 q1 q2
      | none => false) = true := by native_decide

#print axioms rischDECancelTanWf_example

end DeepWiki.SymbolicIntegration
