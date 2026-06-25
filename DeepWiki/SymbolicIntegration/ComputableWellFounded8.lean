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

/-! ### Bridge of `cPolyRischDENoCancelQWf` to the fuel'd `cPolyRischDENoCancelQ`

`cPolyRischDENoCancelQ` uses **no** fuel-bearing sub-ops (only `cderivQ`/`cmulG`/`csubG`/`cshiftG`/
arithmetic); it recurses on `fuel` purely as a counter. So the bridge needs only that the structural guard
fires on a real non-cancellation run; the inductive gate `CPolyRischNoCancelQReg fuel b c n` (nodes
concluding at fuel `fuel + 1`) carries that as a step budget mirroring `cPolyRischDENoCancelQ`'s recursion.
The base analogue of WF7's `CPolyRischNoCancelReg`/`cPolyRischDENoCancelWf_eq`. -/

/-- **Per-run base non-cancellation-loop regularity** `CPolyRischNoCancelQReg b c n` (nodes conclude at
fuel `fuel + 1`): mirrors the `cPolyRischDENoCancelQ` recursion. `baseZero` (`c = 0`) and `baseGuard`
(`n < 0 ∨ m < 0 ∨ m > n`) are terminal; `step` requires the WF guard fires (the peeled leading term drops
the normalized length, `c' = c − Dp − b·p`, `p = (lc(c)/lc(b))·xᵐ`, `m = deg(c) − deg(b)`, `D = cderivQ`)
and the same holds recursively on `c'` at `m − 1`. -/
inductive CPolyRischNoCancelQReg (b : CPolyG ℚ) : ℕ → CPolyG ℚ → ℤ → Prop
  /-- terminal: `c = 0`, returns `[]`. -/
  | baseZero {fuel : ℕ} {c : CPolyG ℚ} {n : ℤ} (hc : cisZeroG c = true) :
      CPolyRischNoCancelQReg b (fuel + 1) c n
  /-- terminal: the degree guard fails (`n < 0 ∨ m < 0 ∨ m > n`), returns `none`. -/
  | baseGuard {fuel : ℕ} {c : CPolyG ℚ} {n : ℤ} (hc : ¬ cisZeroG c = true)
      (hg : n < 0 ∨ (cdegG c : ℤ) - (cdegG b : ℤ) < 0 ∨ (cdegG c : ℤ) - (cdegG b : ℤ) > n) :
      CPolyRischNoCancelQReg b (fuel + 1) c n
  /-- recursive: peel the leading monomial, the WF guard fires, recurse on `c'` within budget. -/
  | step {fuel : ℕ} {c : CPolyG ℚ} {n : ℤ} (hc : ¬ cisZeroG c = true)
      (hg : ¬ (n < 0 ∨ (cdegG c : ℤ) - (cdegG b : ℤ) < 0 ∨ (cdegG c : ℤ) - (cdegG b : ℤ) > n))
      (hguard : (cnormG (csubG (csubG c (cderivQ (cshiftG ((cdegG c : ℤ) - (cdegG b : ℤ)).toNat
            [CField.div (cleadG c) (cleadG b)]))) (cmulG b (cshiftG ((cdegG c : ℤ) - (cdegG b : ℤ)).toNat
            [CField.div (cleadG c) (cleadG b)]))) : List ℚ).length < (cnormG c : List ℚ).length)
      (hrec : CPolyRischNoCancelQReg b fuel
        (csubG (csubG c (cderivQ (cshiftG ((cdegG c : ℤ) - (cdegG b : ℤ)).toNat
            [CField.div (cleadG c) (cleadG b)]))) (cmulG b (cshiftG ((cdegG c : ℤ) - (cdegG b : ℤ)).toNat
            [CField.div (cleadG c) (cleadG b)])))
        (((cdegG c : ℤ) - (cdegG b : ℤ)) - 1)) :
      CPolyRischNoCancelQReg b (fuel + 1) c n

namespace CPolyG

/-- **Bridge — `cPolyRischDENoCancelQWf` equals the fuel'd `cPolyRischDENoCancelQ` on a regular run.**
Under `CPolyRischNoCancelQReg b (fuel + 1) c n`, `cPolyRischDENoCancelQWf b c n = cPolyRischDENoCancelQ
(fuel + 1) b c n`. The gate lives only here; the WF own-loop carries no fuel. By induction on the gate. -/
theorem cPolyRischDENoCancelQWf_eq (b : CPolyG ℚ) :
    ∀ (fuel : ℕ) (c : CPolyG ℚ) (n : ℤ), CPolyRischNoCancelQReg b fuel c n →
      cPolyRischDENoCancelQWf b c n = CPolyG.cPolyRischDENoCancelQ fuel b c n := by
  intro fuel c n hreg
  induction hreg with
  | @baseZero fuel c n hc =>
    rw [cPolyRischDENoCancelQWf.eq_def, if_pos hc, CPolyG.cPolyRischDENoCancelQ, if_pos hc]
  | @baseGuard fuel c n hc hg =>
    rw [cPolyRischDENoCancelQWf.eq_def, if_neg hc, CPolyG.cPolyRischDENoCancelQ, if_neg hc]
    simp only [if_pos hg]
  | @step fuel c n hc hg hguard hrec ih =>
    rw [cPolyRischDENoCancelQWf.eq_def, if_neg hc, CPolyG.cPolyRischDENoCancelQ, if_neg hc]
    simp only [if_neg hg, if_pos hguard, ih]
    rfl

end CPolyG

/-! ### Bridge of `cPolyRischDECancelPrimQWf` to the fuel'd `cPolyRischDECancelPrimQ`

`cPolyRischDECancelPrimQ` uses **no** fuel-bearing sub-ops (only `cleadG`/`cderivQ`/`cmulG`/`csubG`/
`cshiftG`/`cRischDEConst`, all fuel-free); it recurses on `fuel` purely as a counter. The gate
`CPolyRischCancelPrimQReg fuel b c n` (nodes concluding at fuel `fuel + 1`) mirrors the recursion with a
step budget. The `step` node carries the base solve `cRischDEConst (lc(b)) (lc(c)) = some s` and the WF
guard (`c' = c − b·(s·xᵐ) − D(s·xᵐ)`, `m = deg(c)`) firing, recursively on `c'` at `m − 1`. -/

/-- **Per-run base primitive-cancellation-loop regularity** `CPolyRischCancelPrimQReg b c n` (nodes
conclude at fuel `fuel + 1`): mirrors the `cPolyRischDECancelPrimQ` recursion. `baseZero` (`c = 0`) and
`baseDeg` (`n < deg(c)`) are terminal; `baseNoSol` (the constant base solve `cRischDEConst (lc b)(lc c)`
returns `none`) is terminal; `step` carries `cRischDEConst (lc b)(lc c) = some s`, the WF guard firing
(`c' = c − b·(s·xᵐ) − D(s·xᵐ)`, `m = deg(c)`, `D = cderivQ`), and the same recursively on `c'` at `m − 1`. -/
inductive CPolyRischCancelPrimQReg (b : CPolyG ℚ) : ℕ → CPolyG ℚ → ℤ → Prop
  /-- terminal: `c = 0`, returns `[]`. -/
  | baseZero {fuel : ℕ} {c : CPolyG ℚ} {n : ℤ} (hc : cisZeroG c = true) :
      CPolyRischCancelPrimQReg b (fuel + 1) c n
  /-- terminal: `n < deg(c)`, returns `none`. -/
  | baseDeg {fuel : ℕ} {c : CPolyG ℚ} {n : ℤ} (hc : ¬ cisZeroG c = true)
      (hn : n < (cdegG c : ℤ)) : CPolyRischCancelPrimQReg b (fuel + 1) c n
  /-- terminal: the constant base solve `cRischDEConst (lc b)(lc c)` returns `none`. -/
  | baseNoSol {fuel : ℕ} {c : CPolyG ℚ} {n : ℤ} (hc : ¬ cisZeroG c = true)
      (hn : ¬ n < (cdegG c : ℤ)) (hs : cRischDEConst (cleadG b) (cleadG c) = none) :
      CPolyRischCancelPrimQReg b (fuel + 1) c n
  /-- recursive: the base solve gives `s`, the WF guard fires, recurse on `c'` within budget. -/
  | step {fuel : ℕ} {c : CPolyG ℚ} {n : ℤ} {s : ℚ} (hc : ¬ cisZeroG c = true)
      (hn : ¬ n < (cdegG c : ℤ)) (hs : cRischDEConst (cleadG b) (cleadG c) = some s)
      (hguard : (cnormG (csubG (csubG c (cmulG b (cshiftG (cdegG c) [s])))
            (cderivQ (cshiftG (cdegG c) [s]))) : List ℚ).length < (cnormG c : List ℚ).length)
      (hrec : CPolyRischCancelPrimQReg b fuel
        (csubG (csubG c (cmulG b (cshiftG (cdegG c) [s]))) (cderivQ (cshiftG (cdegG c) [s])))
        ((cdegG c : ℤ) - 1)) :
      CPolyRischCancelPrimQReg b (fuel + 1) c n

namespace CPolyG

/-- **Bridge — `cPolyRischDECancelPrimQWf` equals the fuel'd `cPolyRischDECancelPrimQ` on a regular run.**
Under `CPolyRischCancelPrimQReg b (fuel + 1) c n`, `cPolyRischDECancelPrimQWf b c n =
cPolyRischDECancelPrimQ (fuel + 1) b c n`. The gate lives only here; the WF own-loop carries no fuel. By
induction on the gate. -/
theorem cPolyRischDECancelPrimQWf_eq (b : CPolyG ℚ) :
    ∀ (fuel : ℕ) (c : CPolyG ℚ) (n : ℤ), CPolyRischCancelPrimQReg b fuel c n →
      cPolyRischDECancelPrimQWf b c n = CPolyG.cPolyRischDECancelPrimQ fuel b c n := by
  intro fuel c n hreg
  induction hreg with
  | @baseZero fuel c n hc =>
    rw [cPolyRischDECancelPrimQWf.eq_def, if_pos hc, CPolyG.cPolyRischDECancelPrimQ, if_pos hc]
  | @baseDeg fuel c n hc hn =>
    rw [cPolyRischDECancelPrimQWf.eq_def, if_neg hc, if_pos hn,
      CPolyG.cPolyRischDECancelPrimQ, if_neg hc, if_pos hn]
  | @baseNoSol fuel c n hc hn hs =>
    rw [cPolyRischDECancelPrimQWf.eq_def, if_neg hc, if_neg hn,
      CPolyG.cPolyRischDECancelPrimQ, if_neg hc, if_neg hn]
    simp only [hs]
  | @step fuel c n s hc hn hs hguard hrec ih =>
    rw [cPolyRischDECancelPrimQWf.eq_def, if_neg hc, if_neg hn,
      CPolyG.cPolyRischDECancelPrimQ, if_neg hc, if_neg hn]
    simp only [hs, if_pos hguard, ih]
    rfl

end CPolyG

namespace CPolyG

/-! ### Base own-loop 3 — the fuel-free Rothstein SPDE over ℚ `cSPDEQWf` (own-loop on `(n+1).toNat`)

The base (`α = ℚ`, `D = cderivQ = d/dx`) analogue of the WF7 tower own-loop `cSPDEWf`: peel `g = gcd(a, b)`
each step, recurse on the divided `a/g` with the bound lowered to `n − deg(a/g)`. The recursion is taken
only when `n ≥ 0` and `deg(a/g) ≥ 1` (constant base case `deg(a/g) = 0` returns directly), so `n` strictly
drops by `deg(a/g) ≥ 1`; well-founded recursion on `(n + 1).toNat`, structural runtime guard. The inner
gcd/division/divisibility/Bézout are the generic fuel-free `cgcdWf`/`cdivWf`/`cdvdGWf`/`cdiophantineGWf` at
`α = ℚ`. -/

/-- **Fuel-free Rothstein SPDE over ℚ** (Bronstein §6.4 base, `SPDE(a,b,c,D,n)`, book p.203, `D = d/dx`)
`cSPDEQWf a b c n`: the fuel-free companion of `cSPDEQ`. Given `a, b, c ∈ ℚ[x]` (`a ≠ 0`) and a degree
bound `n : ℤ`, returns `none` ("no solution of degree `≤ n`") or `some (b̄, c̄, m, α, β)` so any solution
`q` of `a·Dq + b·q = c` of degree `≤ n` is `q = α·h + β` for an `h` solving `Dh + b̄·h = c̄`, `deg(h) ≤ m`.
Peels `g = (cgcdWf a b).1`; the constant `a/g` base case returns the identity reconstruction, else solves
the Bézout `cdiophantineGWf b̄ ā c̄` and recurses on `ā = a/g` at `n − deg(ā)`. True well-founded recursion
on `(n + 1).toNat` (`n` drops by `deg(ā) ≥ 1`) — **no fuel at runtime**; the inner gcd/division/Bézout are
the generic `cgcdWf`/`cdivWf`/`cdvdGWf`/`cdiophantineGWf`. Agrees with `cSPDEQ` on a regular run
(`cSPDEQWf_eq`). -/
def cSPDEQWf (a b c : CPolyG ℚ) (n : ℤ) :
    Option (CPolyG ℚ × CPolyG ℚ × ℤ × CPolyG ℚ × CPolyG ℚ) :=
  if n < 0 then
    if cisZeroG c then some ([], [], 0, [], []) else none
  else
    let g := (cgcdWf a b).1
    if cdvdGWf g c then
      let a' := cdivWf a g
      let b' := cdivWf b g
      let c' := cdivWf c g
      if cdegG a' = 0 then
        let ainv := CField.inv (cleadG a')
        some (cscaleG ainv b', cscaleG ainv c', n, [CField.one], [])
      else
        let (r, z) := cdiophantineGWf b' a' c'
        let Da := cderivQ a'
        let Dr := cderivQ r
        if (n - (cdegG a' : ℤ) + 1).toNat < (n + 1).toNat then
          match cSPDEQWf a' (caddG b' Da) (csubG z Dr) (n - (cdegG a' : ℤ)) with
          | none => none
          | some (bbar, cbar, m, α, β) =>
              some (bbar, cbar, m, cmulG a' α, caddG (cmulG a' β) r)
        else none   -- unreachable on a real run (`deg(a') ≥ 1`, `n ≥ 0`, so `n` strictly drops)
    else none
termination_by (n + 1).toNat
decreasing_by assumption

end CPolyG

/-! ### Bridge of `cSPDEQWf` to the fuel'd `cSPDEQ`

The WF `cSPDEQWf` recurses on `(n + 1).toNat`; the fuel'd `cSPDEQ` on `fuel`. At a non-base node,
`cSPDEQ (fuel + 1)` computes its `gcd`/divisions/Bézout with the **predecessor** fuel `fuel` (its body
peels one fuel), so the fuel-free leaves must match the fuel'd ops at fuel `fuel`. The bundle
`CSPDEQStepReg fuel a b c` carries the per-step length preconditions for that match (`cgcdWf` needs
`(cnormG a).length ≤ fuel`, `(cnormG b).length < fuel`; each division and the Bézout descent their own
bounds), and the inductive `CSPDEQReg fuel a b c n` (nodes concluding at `fuel + 1`) mirrors the recursion
with a step budget. The base analogue of WF7's `CSPDEWfStepReg`/`CSPDEWfReg`/`cSPDEWf_eq` over `[CFieldSpec
ℚ]` (`cgcdExtG`-based gcd, not `cgcdFF`). -/

/-- **Per-SPDE-step node-regularity bundle over ℚ** `CSPDEQStepReg fuel a b c`: the length preconditions
for one SPDE peel's fuel-free leaves to match the fuel'd ops at sub-op fuel `fuel` (used by `cSPDEQ
(fuel + 1)`). With `g = (cgcdExtG fuel a b).1`, the extended Euclid descends on `b` (`hagcd`/`hbgcd`); the
divisibility-test dividend `c` and the three divisions `a/g, b/g, c/g` are short enough; and (for the
Bézout `cdiophantineGWf bd ad cd`) the divisor `ad`, dividend `bd`, and rescaled dividend `S` are short
enough. -/
structure CSPDEQStepReg (fuel : ℕ) (a b c : CPolyG ℚ) : Prop where
  /-- `a` is short enough for the extended-Euclid `cgcdWf a b` (`(cnormG a).length ≤ fuel`). -/
  hagcd : (cnormG a : List ℚ).length ≤ fuel
  /-- `b` is strictly short enough for the extended-Euclid descent (`(cnormG b).length < fuel`). -/
  hbgcd : (cnormG b : List ℚ).length < fuel
  /-- the divisibility-test dividend `c` is reduced (for `cdvdGWf g c = cdvdG fuel g c`). -/
  hclen : (cnormG c : List ℚ).length ≤ fuel
  /-- `a` is short enough for its exact division `a/g`. -/
  halen : (cnormG a : List ℚ).length ≤ fuel
  /-- `b` is short enough for its exact division `b/g`. -/
  hblen : (cnormG b : List ℚ).length ≤ fuel
  /-- the divided divisor `ad = a/g` is strictly short enough for the Bézout extended-Euclid descent. -/
  hadlen : (cnormG (CPolyG.cdivG fuel a ((CPolyG.cgcdExtG fuel a b).1)) : List ℚ).length < fuel
  /-- the divided dividend `bd = b/g` is short enough for the Bézout extended-Euclid `cgcdWf bd ad`. -/
  hbdlen : (cnormG (CPolyG.cdivG fuel b ((CPolyG.cgcdExtG fuel a b).1)) : List ℚ).length ≤ fuel
  /-- the rescaled Bézout dividend `S` is short enough for the `cdivmodWf` mod-reduction. -/
  hSlen : (cnormG (cscaleG (CField.inv (cleadG
      (cgcdWf (CPolyG.cdivG fuel b ((CPolyG.cgcdExtG fuel a b).1))
        (CPolyG.cdivG fuel a ((CPolyG.cgcdExtG fuel a b).1))).1))
      (cmulG (CPolyG.cdivG fuel c ((CPolyG.cgcdExtG fuel a b).1))
        (cgcdWf (CPolyG.cdivG fuel b ((CPolyG.cgcdExtG fuel a b).1))
          (CPolyG.cdivG fuel a ((CPolyG.cgcdExtG fuel a b).1))).2.1)) : List ℚ).length ≤ fuel

/-- **Per-run SPDE-loop regularity bundle over ℚ** `CSPDEQReg fuel a b c n` (nodes concluding at fuel
`fuel + 1`): mirrors the `cSPDEQ (fuel + 1)` recursion with a step budget. `baseNeg` (`n < 0`),
`baseNonDvd` (`g ∤ c`), `baseConst` (`deg(a/g) = 0`) are terminal; `step` (`n ≥ 0`, `g ∣ c`,
`deg(a/g) ≠ 0`) requires the step is node-regular (`CSPDEQStepReg fuel a b c`) and the same recursively on
the divided `(ad, bd + D ad, z − D r)` at `n − deg(ad)` (gate fuel `fuel`). -/
inductive CSPDEQReg : ℕ → CPolyG ℚ → CPolyG ℚ → CPolyG ℚ → ℤ → Prop
  /-- terminal: `n < 0` (the `c = 0`/`c ≠ 0` short-circuit). -/
  | baseNeg {fuel : ℕ} {a b c : CPolyG ℚ} {n : ℤ} (hn : n < 0) :
      CSPDEQReg (fuel + 1) a b c n
  /-- terminal: `n ≥ 0`, `g ∤ c` (no solution). -/
  | baseNonDvd {fuel : ℕ} {a b c : CPolyG ℚ} {n : ℤ} (hn : ¬ n < 0)
      (hdvd : ¬ cdvdGWf ((CPolyG.cgcdExtG fuel a b).1) c = true) (hstep : CSPDEQStepReg fuel a b c) :
      CSPDEQReg (fuel + 1) a b c n
  /-- terminal: `n ≥ 0`, `g ∣ c`, `deg(a/g) = 0` (constant base case, identity reconstruction). -/
  | baseConst {fuel : ℕ} {a b c : CPolyG ℚ} {n : ℤ} (hn : ¬ n < 0)
      (hdvd : cdvdGWf ((CPolyG.cgcdExtG fuel a b).1) c = true)
      (hdeg : cdegG (CPolyG.cdivG fuel a ((CPolyG.cgcdExtG fuel a b).1)) = 0)
      (hstep : CSPDEQStepReg fuel a b c) :
      CSPDEQReg (fuel + 1) a b c n
  /-- recursive: `n ≥ 0`, `g ∣ c`, `deg(a/g) ≠ 0`; recurse on the divided equation (gate fuel `fuel`). -/
  | step {fuel : ℕ} {a b c : CPolyG ℚ} {n : ℤ} (hn : ¬ n < 0)
      (hdvd : cdvdGWf ((CPolyG.cgcdExtG fuel a b).1) c = true)
      (hdeg : cdegG (CPolyG.cdivG fuel a ((CPolyG.cgcdExtG fuel a b).1)) ≠ 0)
      (hstep : CSPDEQStepReg fuel a b c)
      (hrec : CSPDEQReg fuel (CPolyG.cdivG fuel a ((CPolyG.cgcdExtG fuel a b).1))
        (caddG (CPolyG.cdivG fuel b ((CPolyG.cgcdExtG fuel a b).1))
          (cderivQ (CPolyG.cdivG fuel a ((CPolyG.cgcdExtG fuel a b).1))))
        (csubG (CPolyG.cdiophantineG fuel (CPolyG.cdivG fuel b ((CPolyG.cgcdExtG fuel a b).1))
            (CPolyG.cdivG fuel a ((CPolyG.cgcdExtG fuel a b).1))
            (CPolyG.cdivG fuel c ((CPolyG.cgcdExtG fuel a b).1))).2
          (cderivQ (CPolyG.cdiophantineG fuel (CPolyG.cdivG fuel b ((CPolyG.cgcdExtG fuel a b).1))
            (CPolyG.cdivG fuel a ((CPolyG.cgcdExtG fuel a b).1))
            (CPolyG.cdivG fuel c ((CPolyG.cgcdExtG fuel a b).1))).1))
        (n - (cdegG (CPolyG.cdivG fuel a ((CPolyG.cgcdExtG fuel a b).1)) : ℤ))) :
      CSPDEQReg (fuel + 1) a b c n

namespace CPolyG

/-- **The per-SPDE-step fuel-free leaves match the fuel'd ops over ℚ** at sub-op fuel `fuel`, under a
regular step (`CSPDEQStepReg fuel a b c`): the gcd `(cgcdWf a b).1 = (cgcdExtG fuel a b).1`, the
divisibility test `cdvdGWf`, and the three exact divisions `cdivWf = cdivG fuel` — the conjunction the
bridge consumes. -/
theorem cSPDEQWf_step_leaves (fuel : ℕ) (a b c : CPolyG ℚ) (hstep : CSPDEQStepReg fuel a b c) :
    (cgcdWf a b).1 = (CPolyG.cgcdExtG fuel a b).1
    ∧ cdvdGWf ((CPolyG.cgcdExtG fuel a b).1) c = CPolyG.cdvdG fuel ((CPolyG.cgcdExtG fuel a b).1) c
    ∧ cdivWf a ((CPolyG.cgcdExtG fuel a b).1) = CPolyG.cdivG fuel a ((CPolyG.cgcdExtG fuel a b).1)
    ∧ cdivWf b ((CPolyG.cgcdExtG fuel a b).1) = CPolyG.cdivG fuel b ((CPolyG.cgcdExtG fuel a b).1)
    ∧ cdivWf c ((CPolyG.cgcdExtG fuel a b).1) = CPolyG.cdivG fuel c ((CPolyG.cgcdExtG fuel a b).1) := by
  obtain ⟨hagcd, hbgcd, hclen, halen, hblen, _, _, _⟩ := hstep
  have hgeq : (cgcdWf a b).1 = (CPolyG.cgcdExtG fuel a b).1 := by
    rw [cgcdWf_eq_of_fuel fuel a b hagcd hbgcd]
  refine ⟨hgeq, cdvdGWf_eq_of_fuel fuel _ c hclen, ?_, ?_, ?_⟩
  · rw [cdivWf, cdivmodWf_eq_of_fuel fuel a _ halen, cdivG]
  · rw [cdivWf, cdivmodWf_eq_of_fuel fuel b _ hblen, cdivG]
  · rw [cdivWf, cdivmodWf_eq_of_fuel fuel c _ hclen, cdivG]

/-- **Bridge — `cSPDEQWf` equals the fuel'd `cSPDEQ` on a regular run.** Under `CSPDEQReg (fuel + 1) a b c
n`, `cSPDEQWf a b c n = cSPDEQ (fuel + 1) a b c n`. The fuel bounds live only in the gate; the WF own-loop
carries none. By induction on the `CSPDEQReg` derivation, exactly as WF7's `cSPDEWf_eq` (the Bézout
cofactors agree by `cdiophantineGWf_eq_of_fuel`, the WF guard fires since `n` drops by `deg(ad) ≥ 1`). -/
theorem cSPDEQWf_eq :
    ∀ (fuel : ℕ) (a b c : CPolyG ℚ) (n : ℤ), CSPDEQReg fuel a b c n →
      cSPDEQWf a b c n = CPolyG.cSPDEQ fuel a b c n := by
  intro fuel a b c n hreg
  induction hreg with
  | @baseNeg fuel a b c n hn =>
    rw [cSPDEQWf.eq_def, if_pos hn, CPolyG.cSPDEQ, if_pos hn]
  | @baseNonDvd fuel a b c n hn hdvd hstep =>
    obtain ⟨hgeq, hdvdeq, _, _, _⟩ := cSPDEQWf_step_leaves fuel a b c hstep
    rw [hdvdeq] at hdvd
    rw [cSPDEQWf.eq_def, if_neg hn, CPolyG.cSPDEQ, if_neg hn]
    simp only [hgeq, hdvdeq, if_neg hdvd]
  | @baseConst fuel a b c n hn hdvd hdeg hstep =>
    obtain ⟨hgeq, hdvdeq, haeq, hbeq, hceq⟩ := cSPDEQWf_step_leaves fuel a b c hstep
    rw [hdvdeq] at hdvd
    rw [cSPDEQWf.eq_def, if_neg hn, CPolyG.cSPDEQ, if_neg hn]
    simp only [hgeq, hdvdeq, haeq, hbeq, hceq, if_pos hdvd, if_pos hdeg]
  | @step fuel a b c n hn hdvd hdeg hstep hrec ih =>
    obtain ⟨hgeq, hdvdeq, haeq, hbeq, hceq⟩ := cSPDEQWf_step_leaves fuel a b c hstep
    rw [hdvdeq] at hdvd
    have hdioeq : cdiophantineGWf (CPolyG.cdivG fuel b ((CPolyG.cgcdExtG fuel a b).1))
        (CPolyG.cdivG fuel a ((CPolyG.cgcdExtG fuel a b).1))
        (CPolyG.cdivG fuel c ((CPolyG.cgcdExtG fuel a b).1))
      = CPolyG.cdiophantineG fuel (CPolyG.cdivG fuel b ((CPolyG.cgcdExtG fuel a b).1))
        (CPolyG.cdivG fuel a ((CPolyG.cgcdExtG fuel a b).1))
        (CPolyG.cdivG fuel c ((CPolyG.cgcdExtG fuel a b).1)) :=
      cdiophantineGWf_eq_of_fuel fuel _ _ _ hstep.hbdlen hstep.hadlen hstep.hSlen
    have hguard : (n - (cdegG (CPolyG.cdivG fuel a ((CPolyG.cgcdExtG fuel a b).1)) : ℤ)
        + 1).toNat < (n + 1).toNat := by
      have hn0 : 0 ≤ n := not_lt.mp hn
      have hd1 : 1 ≤ (cdegG (CPolyG.cdivG fuel a ((CPolyG.cgcdExtG fuel a b).1)) : ℤ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hdeg
      omega
    rw [cSPDEQWf.eq_def, if_neg hn, CPolyG.cSPDEQ, if_neg hn]
    simp only [hgeq, hdvdeq, haeq, hbeq, hceq, hdioeq, if_pos hdvd, if_neg hdeg, if_pos hguard, ih]
    rfl

end CPolyG

namespace CPolyG

/-! ### Base composition — the fuel-free Poly-Risch-DE dispatcher over ℚ `cPolyRischDEQWf`

`cPolyRischDEQ` routes `Dq + b·q = c` (`δ = 0`) to polynomial integration (`b = 0`), the non-cancellation
solver (`deg(b) ≥ 1`), or the primitive cancellation solver (`b ∈ ℚ*`). The fuel-free dispatcher
substitutes the now-fuel-free own-loops `cPolyRischDENoCancelQWf`/`cPolyRischDECancelPrimQWf`
(`cIntegratePolyQ` is already fuel-free). -/

/-- **Fuel-free Poly-Risch-DE dispatcher over ℚ** (Bronstein §6.5 + §6.6 base, `D = d/dx`, `δ = 0`)
`cPolyRischDEQWf b c n`: the fuel-free companion of `cPolyRischDEQ`. Solves `Dq + b·q = c` for `q ∈ ℚ[x]`,
`deg(q) ≤ n`. Routes `b = 0` to polynomial integration (`cIntegratePolyQ`, with the `deg(c)+1 ≤ n` check),
`deg(b) ≥ 1` to the fuel-free non-cancellation solver `cPolyRischDENoCancelQWf`, and `b ∈ ℚ*` to the
fuel-free primitive cancellation solver `cPolyRischDECancelPrimQWf`. **No fuel at runtime**. -/
def cPolyRischDEQWf (b c : CPolyG ℚ) (n : ℤ) : Option (CPolyG ℚ) :=
  if cisZeroG b then
    if cisZeroG c then some []
    else if (cdegG c : ℤ) + 1 > n then none
    else some (cIntegratePolyQ c)
  else if (cdegG b : ℤ) > 0 then cPolyRischDENoCancelQWf b c n
  else cPolyRischDECancelPrimQWf b c n

/-- **Bridge — `cPolyRischDEQWf` equals the fuel'd `cPolyRischDEQ` on a regular run** (composition). The
two dispatchers differ only in which own-loop the non-`b=0` branches call; given the own-loop agreements
(`hnocancel`: the non-cancellation loop; `hcancel`: the primitive cancellation loop), they agree
(`cIntegratePolyQ` is identical, fuel-free). A pure case-split rewrite. -/
theorem cPolyRischDEQWf_eq (fuel : ℕ) (b c : CPolyG ℚ) (n : ℤ)
    (hnocancel : cPolyRischDENoCancelQWf b c n = CPolyG.cPolyRischDENoCancelQ fuel b c n)
    (hcancel : cPolyRischDECancelPrimQWf b c n = CPolyG.cPolyRischDECancelPrimQ fuel b c n) :
    cPolyRischDEQWf b c n = CPolyG.cPolyRischDEQ fuel b c n := by
  rw [cPolyRischDEQWf, CPolyG.cPolyRischDEQ]
  by_cases hb : cisZeroG b = true
  · simp only [hb, if_true]
  · simp only [hb, Bool.false_eq_true, if_false]
    by_cases hdb : (cdegG b : ℤ) > 0
    · simp only [hdb, if_true, hnocancel]
    · simp only [hdb, if_false, hcancel]

/-! ### Base composition — the fuel-free residue resultant + weak normalizer over ℚ

`cResidueResultantQ` builds `r(z) = res_x(a − z·d′, d)` by evaluation + interpolation (`cresultantG` at
`deg d + 1` nodes, then `cinterpolateG`); `cWeakNormalizerQ` then takes the positive integer roots of `r`
into the `WeakNormalizer` product (`cgcdExtG`, `cdivG`, `cpowG`). The fuel-free companions substitute the
generic fuel-free `cresultantWf`/`cgcdWf`/`cdivWf` (`cinterpolateG`/`cPosIntRootsQ`/`cpowG`/`cscaleG` carry
no fuel). -/

/-- **Fuel-free residue resultant over ℚ** `cResidueResultantQWf a d = r(z) = res_x(a − z·d′, d) ∈ ℚ[z]`:
the fuel-free companion of `cResidueResultantQ`, the §5.6 evaluation + interpolation template with the
generic fuel-free resultant leaf `cresultantWf` (and `cinterpolateG`, which carries no fuel). **No fuel at
runtime**. -/
def cResidueResultantQWf (a d : CPolyG ℚ) : CPolyG ℚ :=
  let Dd := cderivQ d
  let n := cdegG d
  let pts : List (ℚ × ℚ) := (List.range (n + 1)).map (fun k =>
    let zk : ℚ := (k : ℚ)
    (zk, cresultantWf d (csubG a (cscaleG zk Dd))))
  cinterpolateG pts

/-- **Fuel-free weak normalizer over ℚ** `cWeakNormalizerQWf fnum fden = q₁ ∈ ℚ[x]` (Bronstein §6.1 base,
book p.183): the fuel-free companion of `cWeakNormalizerQ`. Identical assembly — `dₙ = fden` (no special
part over ℚ), `g = gcd(dₙ, dₙ′)`, `d₁ = (dₙ/g)/gcd(dₙ/g, g)`, `a` the residue numerator from
`ExtendedEuclidean(fden/d₁, d₁, fnum)`, `r = res_x(a − z·d₁′, d₁)`, the product over the positive integer
roots `nᵢ` of `r` — but every fuel'd sub-op replaced by its fuel-free companion (`cgcdWf`, `cdivWf`,
`cdiophantineGWf`, `cResidueResultantQWf`). `q₁ = 1` when `f` is already weakly normalized. **No fuel at
runtime**. -/
def cWeakNormalizerQWf (fnum fden : CPolyG ℚ) (boundRoots : ℕ := 16) : CPolyG ℚ :=
  let dn := fden
  let g := (cgcdWf dn (cderivQ dn)).1
  let dstar := cdivWf dn g
  let d1 := cdivWf dstar (cgcdWf dstar g).1
  let fdenOverD1 := cdivWf fden d1
  let a := (cdiophantineGWf fdenOverD1 d1 fnum).1
  let Dd1 := cderivQ d1
  let r := cResidueResultantQWf a d1
  let roots := cPosIntRootsQ r boundRoots
  roots.foldl (fun (acc : CPolyG ℚ) (n : ℕ) =>
    let gi := (cgcdWf (csubG a (cscaleG ((n : ℚ)) Dd1)) d1).1
    cmulG acc (cpowG gi n)) [(1 : ℚ)]

/-- **Fuel-free normal-denominator reduction over ℚ** `cRdeNormalDenominatorQWf fnum fden gnum gden`
(Bronstein §6.2 base / Corollary 6.1.1, book p.185): the fuel-free companion of `cRdeNormalDenominatorQ`.
Over ℚ the normal parts are the whole denominators (`dₙ = fden`, `eₙ = gden`); `p = gcd(dₙ, eₙ)`,
`h = gcd(eₙ, eₙ′)/gcd(p, p′)`, the `eₙ ∣ dₙh²` test, and the quadruplet `(dₙh, dₙhf − dₙDh, dₙh²g, h)` —
every fuel'd sub-op replaced by its fuel-free companion (`cgcdWf`, `cdivWf`, `cdvdGWf`). Returns `none`
("no solution") or `some (a, B, C, h)`. **No fuel at runtime**. -/
def cRdeNormalDenominatorQWf (fnum fden gnum gden : CPolyG ℚ) :
    Option (CPolyG ℚ × CPolyG ℚ × CPolyG ℚ × CPolyG ℚ) :=
  let dn := fden
  let en := gden
  let p := (cgcdWf dn en).1
  let h := cdivWf (cgcdWf en (cderivQ en)).1 (cgcdWf p (cderivQ p)).1
  let dnh2 := cmulG (cmulG dn h) h
  if cdvdGWf en dnh2 then
    let a := cmulG dn h
    let Dh := cderivQ h
    let b := cdivWf (csubG (cmulG a fnum) (cmulG (cmulG dn Dh) fden)) fden
    let c := cdivWf (cmulG dnh2 gnum) gden
    some (a, b, c, h)
  else none

/-! ### Base composition — the fuel-free rational Risch DE over ℚ(x) `cRationalRDEWf`

`cRationalRDE` is a pure composition of the base stages: weak normalizer → reduce-to-lowest-terms →
normal denominator → degree bound (`cRdeBoundDegreeBaseQ`, already fuel-free, no recursion) → SPDE →
poly stage. The fuel-free assembly substitutes the now-fuel-free stages — **no fuel at runtime**. -/

/-- **Fuel-free rational Risch DE over ℚ(x)** `cRationalRDEWf bnum bden cnum cden` (Bronstein §6.6 eq. 6.23
base solve, `D = d/dx`): the fuel-free companion of `cRationalRDE`. Solves `Ds + b·s = c` for `s ∈ ℚ(x)`
with `b = bnum/bden`, `c = cnum/cden`, returning `some (snum, sden)` (with `s = snum/sden`) or `none`. The
whole Ch. 6 pipeline at the base level (trivial primitive monomial `t = x`, `k = ℚ`): weak normalize
(`cWeakNormalizerQWf`), reduce `b̃ = b − Dq₁/q₁`, `c̃ = c·q₁` to lowest terms (over the fuel-free `cgcdWf`/
`cdivWf`), normal denominator (`cRdeNormalDenominatorQWf`), degree bound (`cRdeBoundDegreeBaseQ`, fuel-free),
SPDE (`cSPDEQWf`), poly stage (`cPolyRischDEQWf`). **No fuel at runtime**; `native_decide`-able. -/
def cRationalRDEWf (bnum bden cnum cden : CPolyG ℚ) : Option (CPolyG ℚ × CPolyG ℚ) :=
  let q1 := cWeakNormalizerQWf bnum bden
  let Dq1 := cderivQ q1
  let bpnum := csubG (cmulG bnum q1) (cmulG Dq1 bden)
  let bpden := cmulG bden q1
  let cpnum := cmulG cnum q1
  let cpden := cden
  let gb := (cgcdWf bpnum bpden).1
  let bnum2 := cdivWf bpnum gb
  let bden2 := cdivWf bpden gb
  let gc := (cgcdWf cpnum cpden).1
  let cnum2 := cdivWf cpnum gc
  let cden2 := cdivWf cpden gc
  match cRdeNormalDenominatorQWf bnum2 bden2 cnum2 cden2 with
  | none => none
  | some (a0, b0, c0, h0) =>
    let N := cRdeBoundDegreeBaseQ a0 b0 c0
    match cSPDEQWf a0 b0 c0 N with
    | none => none
    | some (bbar, cbar, m, α, β) =>
      match cPolyRischDEQWf bbar cbar m with
      | none => none
      | some v =>
        let Q := caddG (cmulG α v) β
        some (Q, cmulG h0 q1)

end CPolyG

/-! ### Tower composition — the fuel-free base RDE over ℚ(x) `cRischDEBaseWf`

`cRischDEBase b c` (the eq. 6.23 recursion target) is the `k`-constant fast path plus the general routing
through `cRationalRDE` (over the **different** carrier `CPolyG ℚ`). The fuel-free companion substitutes
`cRationalRDEWf`; it is **not recursive** (the base ℚ-pipeline lives over `CPolyG ℚ`, so there is no mutual
recursion with the tower cancellation loops that call it) — a plain composition, **no fuel at runtime**. -/

namespace CPolyG

/-- **Fuel-free base-field Risch DE `Ds + b·s = c` over `k = ℚ(x)`** `cRischDEBaseWf b c` (Bronstein §6.6
eq. 6.23, the recursion target of the §6.6 cancellation cases): the fuel-free companion of `cRischDEBase`.
Returns `some s` (`s ∈ ℚ(x)` solving `Ds + b·s = c`, `D = d/dx`) or `none`. The `k`-constant fast path
(`b, c ∈ ℚ`: `s = c/b`, `b ≠ 0`; `s = 0` if `b = c = 0`) plus the **general** non-constant solve routing
`b = bnum/bden`, `c = cnum/cden ∈ ℚ(x)` through the fuel-free `cRationalRDEWf` (the whole base ℚ-pipeline),
lifting the returned `(snum, sden)` back to `QFunNZ`. **No fuel at runtime**; not recursive (the base
ℚ-pipeline is over `CPolyG ℚ`). Agrees with `cRischDEBase` whenever `cRationalRDEWf` agrees with the fuel'd
`cRationalRDE` (`cRischDEBaseWf_eq`). -/
def cRischDEBaseWf (b c : QFunNZ) : Option QFunNZ :=
  let isConst : QFunNZ → Bool := fun z => CField.isZero (CDiffField.cderiv z)
  if isConst b && isConst c then
    if CField.isZero b then
      if CField.isZero c then some CField.zero else none
    else
      some (CField.div c b)
  else
    match cRationalRDEWf b.1.1 b.1.2 c.1.1 c.1.2 with
    | none => none
    | some (snum, sden) =>
      if h : Compute.cisZero sden = false then some (QFunNZ.ofNumDen snum sden h) else none

/-! ### Tower own-loop — the fuel-free primitive cancellation Poly-Risch-DE `cPolyRischDECancelPrimWf`

The §6.6 tower primitive cancellation (`Dt ∈ k`, `δ = 0`, `b ∈ k*`): the leading terms of `Dq` and `bq`
cancel, so the solve recurses degree-by-degree into the base RDE `cRischDEBaseWf b₀ (lc(c))` over `k = ℚ(x)`
(eq. 6.23). The leading monomial `s·tᵐ` (`m = deg(c)`, `D = cmonomialDeriv Dt`) cancels `c`'s top, so
`(cnormG c).length` strictly drops; well-founded recursion on it, structural runtime guard. -/

/-- **Fuel-free primitive cancellation Poly-Risch-DE** (Bronstein §6.6, `PolyRischDECancelPrim(b,c,D,n)`,
book p.212) `cPolyRischDECancelPrimWf Dt b c n`: the fuel-free companion of `cPolyRischDECancelPrim`.
`Dt ∈ k = ℚ(x)`, `b ∈ k*` (degree-0 `t`-polynomial, scalar `b₀ = lc(b)`), `c ∈ k[t]`, degree bound `n : ℤ`;
solves `Dq + b·q = c` degree-by-degree, recursing at degree `m = deg(c)` into the base RDE
`cRischDEBaseWf b₀ (lc(c))` (`= RischDE(b₀, lc(c))` over `k = ℚ(x)`, eq. 6.23), leading monomial `s·tᵐ`,
remainder `c' = c − b·(s·tᵐ) − D(s·tᵐ)` (`D = cmonomialDeriv Dt`). Returns `none` ("no solution of degree
`≤ n`") or `some q`. True well-founded recursion on `(cnormG c).length` — **no fuel at runtime**; the
recursion is taken only under the structural guard `(cnormG c').length < (cnormG c).length` (the leading
monomial cancels `c`'s top), so `decreasing_by` is `assumption`. The §5.12 logarithmic-derivative branch
is the documented continuation (the general degree-by-degree recursion is sound without it). Agrees with
`cPolyRischDECancelPrim` on a real run (`cPolyRischDECancelPrimWf_eq`). `native_decide`-able. -/
def cPolyRischDECancelPrimWf (Dt : CPolyG QFunNZ) (b c : CPolyG QFunNZ) (n : ℤ) :
    Option (CPolyG QFunNZ) :=
  let b0 : QFunNZ := cleadG b
  if cisZeroG c then some []
  else if n < (cdegG c : ℤ) then none
  else
    let m : ℕ := cdegG c
    match cRischDEBaseWf b0 (cleadG c) with
    | none => none
    | some s =>
      let stm : CPolyG QFunNZ := cshiftG m [s]
      let c' := csubG (csubG c (cmulG b stm)) (cmonomialDeriv Dt stm)
      if (cnormG c' : List QFunNZ).length < (cnormG c : List QFunNZ).length then
        match cPolyRischDECancelPrimWf Dt b c' ((m : ℤ) - 1) with
        | none => none
        | some q => some (caddG stm q)
      else none   -- unreachable on a real run (the leading monomial cancels, degree drops)
termination_by (cnormG c).length
decreasing_by assumption

/-! ### Tower leaf — the fuel-free hyperexponential coefficient `cExpEtaWf`

`cExpEta fuel Dt = lc(Dt / t)` (`η = Dt/t ∈ k`) uses the fuel'd `cdivG`; the fuel-free companion
substitutes the generic `cdivWf`. -/

/-- **Fuel-free hyperexponential coefficient `η = Dt/t ∈ k`** `cExpEtaWf Dt`: the fuel-free companion of
`cExpEta`. For a hyperexponential monomial `Dt = η·t` (`δ = 1`), divide `Dt` by `t` (`cshiftG 1 [1]`) with
the generic fuel-free `cdivWf` and read the degree-0 coefficient `η ∈ ℚ(x)`. For `t = exp(x)` (`Dt = t`),
`η = 1`. **No fuel at runtime**. -/
def cExpEtaWf (Dt : CPolyG QFunNZ) : QFunNZ :=
  cleadG (cdivWf Dt (cshiftG 1 [CField.one]))

/-! ### Tower own-loop — the fuel-free hyperexponential cancellation Poly-Risch-DE `cPolyRischDECancelExpWf`

The §6.6 tower hyperexponential cancellation (`Dt/t = η ∈ k`, `δ = 1`, `b ∈ k*`): as in the primitive case
the leading terms cancel, but `D(s·tᵐ) = (Ds + m·η·s)·tᵐ`, so the eq. 6.24 base RDE is
`RischDE(b + m·η, lc(c))` (coefficient shifted by `m·η`, `η = cExpEtaWf Dt`). Same own-loop on
`(cnormG c).length`, structural runtime guard, recursing into `cRischDEBaseWf`. -/

/-- **Fuel-free hyperexponential cancellation Poly-Risch-DE** (Bronstein §6.6, `PolyRischDECancelExp(b,c,D,n)`,
book p.213) `cPolyRischDECancelExpWf Dt b c n`: the fuel-free companion of `cPolyRischDECancelExp`.
`Dt/t = η ∈ k = ℚ(x)` (`δ = 1`), `b ∈ k*` (scalar `b₀ = lc(b)`), `c ∈ k[t]`, degree bound `n : ℤ`; solves
`Dq + b·q = c` degree-by-degree, recursing at degree `m = deg(c)` into the eq. 6.24 base RDE
`cRischDEBaseWf (b₀ + m·η) (lc(c))` over `k = ℚ(x)` (the `m·η` shift makes the coefficient genuinely
non-constant, `η = cExpEtaWf Dt`), leading monomial `s·tᵐ`, remainder `c' = c − b·(s·tᵐ) − D(s·tᵐ)`
(`D = cmonomialDeriv Dt`). Returns `none` or `some q`. True well-founded recursion on `(cnormG c).length`
— **no fuel at runtime**; the structural guard `(cnormG c').length < (cnormG c).length` is `decreasing_by
:= assumption`. The §5.12 log-derivative branch is the documented continuation. Agrees with
`cPolyRischDECancelExp` on a real run (`cPolyRischDECancelExpWf_eq`). `native_decide`-able. -/
def cPolyRischDECancelExpWf (Dt : CPolyG QFunNZ) (b c : CPolyG QFunNZ) (n : ℤ) :
    Option (CPolyG QFunNZ) :=
  let b0 : QFunNZ := cleadG b
  let η : QFunNZ := cExpEtaWf Dt
  if cisZeroG c then some []
  else if n < (cdegG c : ℤ) then none
  else
    let m : ℕ := cdegG c
    let coeff : QFunNZ := CField.add b0 (CField.mul (QFunNZ.ofConstNZ ((m : ℚ))) η)
    match cRischDEBaseWf coeff (cleadG c) with
    | none => none
    | some s =>
      let stm : CPolyG QFunNZ := cshiftG m [s]
      let c' := csubG (csubG c (cmulG b stm)) (cmonomialDeriv Dt stm)
      if (cnormG c' : List QFunNZ).length < (cnormG c : List QFunNZ).length then
        match cPolyRischDECancelExpWf Dt b c' ((m : ℤ) - 1) with
        | none => none
        | some q => some (caddG stm q)
      else none   -- unreachable on a real run (the leading monomial cancels, degree drops)
termination_by (cnormG c).length
decreasing_by assumption

end CPolyG

/-! ### Bridges of the tower §6.6 cancellation own-loops to their fuel'd versions

`cPolyRischDECancelPrim`/`Exp` recurse into `cRischDEBase` (over the **different** carrier `CPolyG ℚ`,
no fuel-bearing tower sub-op aside from `cmonomialDeriv`/`cExpEta`, which carry no fuel); they recurse on
`fuel` purely as a counter. The gates `CPolyRischCancelPrimReg`/`CPolyRischCancelExpReg` (nodes concluding
at fuel `fuel + 1`) mirror the recursions with a step budget, the `step` node carrying the base solve
`cRischDEBaseWf … = cRischDEBase fuel … = some s` and the WF guard firing. -/

/-- **Per-run tower primitive-cancellation-loop regularity** `CPolyRischCancelPrimReg Dt b c n` (nodes
conclude at fuel `fuel + 1`): mirrors the `cPolyRischDECancelPrim` recursion. `baseZero`/`baseDeg` terminal
on `c = 0`/`n < deg(c)`; `baseNoSol` terminal when the base solve returns `none`; `step` carries the base
solve `cRischDEBaseWf (lc b)(lc c) = cRischDEBase fuel (lc b)(lc c) = some s` (the WF op equals the fuel'd
op *and* both yield `s`), the WF guard firing (`c' = c − b·(s·tᵐ) − D(s·tᵐ)`, `m = deg(c)`,
`D = cmonomialDeriv Dt`), and the same recursively on `c'` at `m − 1`. -/
inductive CPolyRischCancelPrimReg (Dt : CPolyG QFunNZ) (b : CPolyG QFunNZ) :
    ℕ → CPolyG QFunNZ → ℤ → Prop
  /-- terminal: `c = 0`, returns `[]`. -/
  | baseZero {fuel : ℕ} {c : CPolyG QFunNZ} {n : ℤ} (hc : cisZeroG c = true) :
      CPolyRischCancelPrimReg Dt b (fuel + 1) c n
  /-- terminal: `n < deg(c)`, returns `none`. -/
  | baseDeg {fuel : ℕ} {c : CPolyG QFunNZ} {n : ℤ} (hc : ¬ cisZeroG c = true)
      (hn : n < (cdegG c : ℤ)) : CPolyRischCancelPrimReg Dt b (fuel + 1) c n
  /-- terminal: the base solve returns `none` (both the WF and the fuel'd `cRischDEBase fuel`). -/
  | baseNoSol {fuel : ℕ} {c : CPolyG QFunNZ} {n : ℤ} (hc : ¬ cisZeroG c = true)
      (hn : ¬ n < (cdegG c : ℤ))
      (hsWf : CPolyG.cRischDEBaseWf (cleadG b) (cleadG c) = none)
      (hsFuel : CPolyG.cRischDEBase fuel (cleadG b) (cleadG c) = none) :
      CPolyRischCancelPrimReg Dt b (fuel + 1) c n
  /-- recursive: the base solve gives `s` (WF = fuel'd), the WF guard fires, recurse on `c'`. -/
  | step {fuel : ℕ} {c : CPolyG QFunNZ} {n : ℤ} {s : QFunNZ} (hc : ¬ cisZeroG c = true)
      (hn : ¬ n < (cdegG c : ℤ))
      (hsWf : CPolyG.cRischDEBaseWf (cleadG b) (cleadG c) = some s)
      (hsFuel : CPolyG.cRischDEBase fuel (cleadG b) (cleadG c) = some s)
      (hguard : (cnormG (csubG (csubG c (cmulG b (cshiftG (cdegG c) [s])))
            (cmonomialDeriv Dt (cshiftG (cdegG c) [s]))) : List QFunNZ).length
          < (cnormG c : List QFunNZ).length)
      (hrec : CPolyRischCancelPrimReg Dt b fuel
        (csubG (csubG c (cmulG b (cshiftG (cdegG c) [s]))) (cmonomialDeriv Dt (cshiftG (cdegG c) [s])))
        ((cdegG c : ℤ) - 1)) :
      CPolyRischCancelPrimReg Dt b (fuel + 1) c n

namespace CPolyG

/-- **Bridge — `cPolyRischDECancelPrimWf` equals the fuel'd `cPolyRischDECancelPrim` on a regular run.**
Under `CPolyRischCancelPrimReg Dt b (fuel + 1) c n`, `cPolyRischDECancelPrimWf Dt b c n =
cPolyRischDECancelPrim Dt (fuel + 1) b c n`. The gate (carrying the base-solve agreement
`cRischDEBaseWf = cRischDEBase fuel` at each step) lives only here; the WF own-loop carries no fuel. By
induction on the gate. -/
theorem cPolyRischDECancelPrimWf_eq (Dt : CPolyG QFunNZ) (b : CPolyG QFunNZ) :
    ∀ (fuel : ℕ) (c : CPolyG QFunNZ) (n : ℤ), CPolyRischCancelPrimReg Dt b fuel c n →
      cPolyRischDECancelPrimWf Dt b c n = CPolyG.cPolyRischDECancelPrim Dt fuel b c n := by
  intro fuel c n hreg
  induction hreg with
  | @baseZero fuel c n hc =>
    rw [cPolyRischDECancelPrimWf.eq_def, if_pos hc, CPolyG.cPolyRischDECancelPrim, if_pos hc]
  | @baseDeg fuel c n hc hn =>
    rw [cPolyRischDECancelPrimWf.eq_def, if_neg hc, if_pos hn,
      CPolyG.cPolyRischDECancelPrim, if_neg hc, if_pos hn]
  | @baseNoSol fuel c n hc hn hsWf hsFuel =>
    rw [cPolyRischDECancelPrimWf.eq_def, if_neg hc, if_neg hn,
      CPolyG.cPolyRischDECancelPrim, if_neg hc, if_neg hn]
    simp only [hsWf, hsFuel]
  | @step fuel c n s hc hn hsWf hsFuel hguard hrec ih =>
    rw [cPolyRischDECancelPrimWf.eq_def, if_neg hc, if_neg hn,
      CPolyG.cPolyRischDECancelPrim, if_neg hc, if_neg hn]
    simp only [hsWf, hsFuel, if_pos hguard, ih]
    rfl

end CPolyG

/-- **Per-run tower hyperexponential-cancellation-loop regularity** `CPolyRischCancelExpReg Dt b c n`
(nodes conclude at fuel `fuel + 1`): mirrors the `cPolyRischDECancelExp` recursion. As the primitive case
but the base solve uses the `m·η` shifted coefficient `b₀ + m·η` (`η = cExpEtaWf Dt = cExpEta fuel Dt`,
both fuel-free reads), and the gate carries `cExpEtaWf Dt = cExpEta fuel Dt` (`hη`) so the fuel-free and
fuel'd coefficients coincide. `step` carries the base solve at the shifted coefficient (WF = fuel'd = some
`s`) and the WF guard firing. -/
inductive CPolyRischCancelExpReg (Dt : CPolyG QFunNZ) (b : CPolyG QFunNZ) :
    ℕ → CPolyG QFunNZ → ℤ → Prop
  /-- terminal: `c = 0`, returns `[]`. -/
  | baseZero {fuel : ℕ} {c : CPolyG QFunNZ} {n : ℤ} (hc : cisZeroG c = true) :
      CPolyRischCancelExpReg Dt b (fuel + 1) c n
  /-- terminal: `n < deg(c)`, returns `none`. -/
  | baseDeg {fuel : ℕ} {c : CPolyG QFunNZ} {n : ℤ} (hc : ¬ cisZeroG c = true)
      (hn : n < (cdegG c : ℤ)) : CPolyRischCancelExpReg Dt b (fuel + 1) c n
  /-- terminal: the base solve at the `m·η`-shifted coefficient returns `none` (`η` reads agree). -/
  | baseNoSol {fuel : ℕ} {c : CPolyG QFunNZ} {n : ℤ} (hc : ¬ cisZeroG c = true)
      (hn : ¬ n < (cdegG c : ℤ)) (hη : cExpEtaWf Dt = CPolyG.cExpEta fuel Dt)
      (hsWf : CPolyG.cRischDEBaseWf (CField.add (cleadG b)
          (CField.mul (QFunNZ.ofConstNZ ((cdegG c : ℚ))) (cExpEtaWf Dt))) (cleadG c) = none)
      (hsFuel : CPolyG.cRischDEBase fuel (CField.add (cleadG b)
          (CField.mul (QFunNZ.ofConstNZ ((cdegG c : ℚ))) (CPolyG.cExpEta fuel Dt))) (cleadG c) = none) :
      CPolyRischCancelExpReg Dt b (fuel + 1) c n
  /-- recursive: the base solve at the shifted coefficient gives `s` (WF = fuel'd), guard fires. -/
  | step {fuel : ℕ} {c : CPolyG QFunNZ} {n : ℤ} {s : QFunNZ} (hc : ¬ cisZeroG c = true)
      (hn : ¬ n < (cdegG c : ℤ)) (hη : cExpEtaWf Dt = CPolyG.cExpEta fuel Dt)
      (hsWf : CPolyG.cRischDEBaseWf (CField.add (cleadG b)
          (CField.mul (QFunNZ.ofConstNZ ((cdegG c : ℚ))) (cExpEtaWf Dt))) (cleadG c) = some s)
      (hsFuel : CPolyG.cRischDEBase fuel (CField.add (cleadG b)
          (CField.mul (QFunNZ.ofConstNZ ((cdegG c : ℚ))) (CPolyG.cExpEta fuel Dt))) (cleadG c) = some s)
      (hguard : (cnormG (csubG (csubG c (cmulG b (cshiftG (cdegG c) [s])))
            (cmonomialDeriv Dt (cshiftG (cdegG c) [s]))) : List QFunNZ).length
          < (cnormG c : List QFunNZ).length)
      (hrec : CPolyRischCancelExpReg Dt b fuel
        (csubG (csubG c (cmulG b (cshiftG (cdegG c) [s]))) (cmonomialDeriv Dt (cshiftG (cdegG c) [s])))
        ((cdegG c : ℤ) - 1)) :
      CPolyRischCancelExpReg Dt b (fuel + 1) c n

namespace CPolyG

/-- **Bridge — `cPolyRischDECancelExpWf` equals the fuel'd `cPolyRischDECancelExp` on a regular run.**
Under `CPolyRischCancelExpReg Dt b (fuel + 1) c n`, `cPolyRischDECancelExpWf Dt b c n =
cPolyRischDECancelExp Dt (fuel + 1) b c n`. The gate (carrying `cExpEtaWf = cExpEta fuel` and the
shifted-coefficient base-solve agreement at each step) lives only here. By induction on the gate. -/
theorem cPolyRischDECancelExpWf_eq (Dt : CPolyG QFunNZ) (b : CPolyG QFunNZ) :
    ∀ (fuel : ℕ) (c : CPolyG QFunNZ) (n : ℤ), CPolyRischCancelExpReg Dt b fuel c n →
      cPolyRischDECancelExpWf Dt b c n = CPolyG.cPolyRischDECancelExp Dt fuel b c n := by
  intro fuel c n hreg
  induction hreg with
  | @baseZero fuel c n hc =>
    rw [cPolyRischDECancelExpWf.eq_def, if_pos hc, CPolyG.cPolyRischDECancelExp, if_pos hc]
  | @baseDeg fuel c n hc hn =>
    rw [cPolyRischDECancelExpWf.eq_def, if_neg hc, if_pos hn,
      CPolyG.cPolyRischDECancelExp, if_neg hc, if_pos hn]
  | @baseNoSol fuel c n hc hn hη hsWf hsFuel =>
    rw [cPolyRischDECancelExpWf.eq_def, if_neg hc, if_neg hn,
      CPolyG.cPolyRischDECancelExp, if_neg hc, if_neg hn]
    simp only [hsWf, hsFuel]
  | @step fuel c n s hc hn hη hsWf hsFuel hguard hrec ih =>
    rw [cPolyRischDECancelExpWf.eq_def, if_neg hc, if_neg hn,
      CPolyG.cPolyRischDECancelExp, if_neg hc, if_neg hn]
    simp only [hsWf, hsFuel, if_pos hguard, ih]
    rfl

end CPolyG

namespace CPolyG

/-! ### Tower dispatcher — the fuel-free Poly-Risch-DE dispatcher `cPolyRischDEWf`

`cPolyRischDE` routes `Dq + b·q = c` (eq. 6.19) by monomial type and `deg(b)` (Lemma 6.5.1): the
non-cancellation case (`deg(b) > max(0, δ−1)`) to `cPolyRischDENoCancel`, primitive cancellation (`δ = 0`,
`b ∈ k*`) to `cPolyRischDECancelPrim`, hyperexponential cancellation (`δ = 1`, `b ∈ k*`) to
`cPolyRischDECancelExp`, else the non-cancellation fallback. The fuel-free dispatcher substitutes the
fuel-free own-loops. -/

/-- **Fuel-free Poly-Risch-DE dispatcher** (Bronstein §6.5 + §6.6) `cPolyRischDEWf Dt b c n`: the fuel-free
companion of `cPolyRischDE`. Routes `Dq + b·q = c` by the monomial type and `deg(b)` (Lemma 6.5.1): the
non-cancellation case (`deg(b) > max(0, δ−1)`, `δ = deg(Dt)`) to the fuel-free `cPolyRischDENoCancelWf`,
primitive cancellation (`δ = 0`, `b ∈ k*`) to `cPolyRischDECancelPrimWf`, hyperexponential cancellation
(`δ = 1`, `b ∈ k*`) to `cPolyRischDECancelExpWf`, else the non-cancellation fallback. **No fuel at runtime**
— the §6.6 cancellation regimes now run fuel-free. -/
def cPolyRischDEWf (Dt : CPolyG QFunNZ) (b c : CPolyG QFunNZ) (n : ℤ) : Option (CPolyG QFunNZ) :=
  let δ : ℤ := (cdegG Dt : ℤ)
  let db : ℤ := (cdegG b : ℤ)
  if db > max 0 (δ - 1) then
    cPolyRischDENoCancelWf Dt b c n
  else if δ = 0 ∧ db = 0 then
    cPolyRischDECancelPrimWf Dt b c n
  else if δ = 1 ∧ db = 0 then
    cPolyRischDECancelExpWf Dt b c n
  else
    cPolyRischDENoCancelWf Dt b c n

/-- **Bridge — `cPolyRischDEWf` equals the fuel'd `cPolyRischDE` on a regular run** (composition). The two
dispatchers share the same case-split on `deg(b)` vs `max(0, δ−1)` and the monomial type; given the
per-branch own-loop agreements (`hnocancel`: the non-cancellation loop; `hprim`: the primitive
cancellation loop; `hexp`: the hyperexponential cancellation loop), they agree. A pure case-split
rewrite. -/
theorem cPolyRischDEWf_eq (Dt : CPolyG QFunNZ) (fuel : ℕ) (b c : CPolyG QFunNZ) (n : ℤ)
    (hnocancel : cPolyRischDENoCancelWf Dt b c n = CPolyG.cPolyRischDENoCancel Dt fuel b c n)
    (hprim : cPolyRischDECancelPrimWf Dt b c n = CPolyG.cPolyRischDECancelPrim Dt fuel b c n)
    (hexp : cPolyRischDECancelExpWf Dt b c n = CPolyG.cPolyRischDECancelExp Dt fuel b c n) :
    cPolyRischDEWf Dt b c n = CPolyG.cPolyRischDE Dt fuel b c n := by
  rw [cPolyRischDEWf, CPolyG.cPolyRischDE]
  by_cases h1 : (cdegG b : ℤ) > max 0 ((cdegG Dt : ℤ) - 1)
  · rw [if_pos h1, if_pos h1, hnocancel]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : (cdegG Dt : ℤ) = 0 ∧ (cdegG b : ℤ) = 0
    · rw [if_pos h2, if_pos h2, hprim]
    · rw [if_neg h2, if_neg h2]
      by_cases h3 : (cdegG Dt : ℤ) = 1 ∧ (cdegG b : ℤ) = 0
      · rw [if_pos h3, if_pos h3, hexp]
      · rw [if_neg h3, if_neg h3, hnocancel]

/-! ### The GOAL — the fuel-free full Risch DE solver `cRischDEWfFull` (all regimes)

`cRischDEWf` (WF7) handled only the non-cancellation regime (its §6.5 polynomial stage hard-wired to
`cPolyRischDENoCancelWf`). `cRischDEWfFull` re-points the polynomial stage to the **dispatcher**
`cPolyRischDEWf`, so the §6.6 cancellation regimes (primitive, hyperexponential) now run fuel-free too —
the whole §6 RDE pipeline is fuel-free in **every** regime. -/

/-- **The fuel-free full Risch differential equation solver** `cRischDEWfFull Dt fnum fden gnum gden`
(Bronstein Ch. 6, the goal, **all regimes**): the fuel-free companion of `cRischDE`. For `f = fnum/fden`,
`g = gnum/gden ∈ ℚ(x)(t)` and the monomial derivation `D = cmonomialDeriv Dt`, returns `some (ynum, yden)`
with `y = ynum/yden` solving `Dy + f·y = g`, or `none`. Identical assembly to `cRischDE` — normal
denominator → special denominator → degree bound → SPDE → polynomial **dispatcher** — with every fuel'd
sub-op replaced by its fuel-free companion (`cRdeNormalDenominatorWf`, `cRdeSpecialDenominatorWf`,
`cRdeBoundDegree`, `cSPDEWf`, and the dispatcher `cPolyRischDEWf` routing the §6.5 non-cancellation /
§6.6 primitive / §6.6 hyperexponential cancellation own-loops). **No fuel at runtime in any regime**;
`native_decide`-able over the noncomputable-`CFieldSpec` tower `QFunNZ`. Extends `cRischDEWf` (WF7, which
covered only non-cancellation) to the full §6.6 cancellation dispatch. -/
def cRischDEWfFull (Dt : CPolyG QFunNZ) (fnum fden gnum gden : CPolyG QFunNZ) :
    Option (CPolyG QFunNZ × CPolyG QFunNZ) :=
  match cRdeNormalDenominatorWf Dt fnum fden gnum gden with
  | none => none
  | some (a0, b0, c0, h0) =>
    let (a, b, c, h1) := cRdeSpecialDenominatorWf Dt a0 b0 c0
    let N := cRdeBoundDegree Dt 0 a b c
    match cSPDEWf Dt a b c (N : ℤ) with
    | none => none
    | some (bbar, cbar, _m, α, β) =>
      match cPolyRischDEWf Dt bbar cbar _m with
      | none => none
      | some v =>
        let Q := caddG (cmulG α v) β
        some (cmulG Q h1, h0)

/-- **Bridge — `cRischDEWfFull` equals `cRischDE` at sufficient fuel on any regular run** (transparent
composition, **all regimes**). From the §6.2 stage agreements (`hnorm`: the normal denominator; `hspec`:
the special denominator), the §6.3 degree bound (`cRdeBoundDegree` already fuel-free, `hbound`), the §6.4
SPDE bridge (`hspde`), and the §6.5/§6.6 polynomial **dispatcher** agreement (`hpoly`: `cPolyRischDEWf =
cPolyRischDE fuel` on the SPDE output) — `cRischDEWfFull Dt fnum fden gnum gden = cRischDE Dt fuel fnum fden
gnum gden`. Unlike WF7's `cRischDEWf_eq` (non-cancellation only, with a hard-wired noncancel-dispatch
hypothesis), this routes through the full dispatcher, so it covers the §6.6 cancellation regimes too. A
pure composition rewrite: rewrite each stage to its fuel'd form and the two drivers collapse. -/
theorem cRischDEWfFull_eq (Dt : CPolyG QFunNZ) (fuel : ℕ) (fnum fden gnum gden : CPolyG QFunNZ)
    (hnorm : cRdeNormalDenominatorWf Dt fnum fden gnum gden
      = CPolyG.cRdeNormalDenominator Dt fuel fnum fden gnum gden)
    (hspec : ∀ a0 b0 c0, cRdeSpecialDenominatorWf Dt a0 b0 c0
      = CPolyG.cRdeSpecialDenominator Dt fuel a0 b0 c0)
    (hbound : ∀ a b c, cRdeBoundDegree Dt 0 a b c = CPolyG.cRdeBoundDegree Dt fuel a b c)
    (hspde : ∀ a b c n, cSPDEWf Dt a b c n = CPolyG.cSPDE Dt fuel a b c n)
    (hpoly : ∀ bbar cbar (m : ℤ),
      cPolyRischDEWf Dt bbar cbar m = CPolyG.cPolyRischDE Dt fuel bbar cbar m) :
    cRischDEWfFull Dt fnum fden gnum gden = CPolyG.cRischDE Dt fuel fnum fden gnum gden := by
  rw [cRischDEWfFull, CPolyG.cRischDE, hnorm]
  rcases hn : CPolyG.cRdeNormalDenominator Dt fuel fnum fden gnum gden with _ | ⟨a0, b0, c0, h0⟩
  · rfl
  · simp only []
    rw [hspec a0 b0 c0]
    rcases hs : CPolyG.cRdeSpecialDenominator Dt fuel a0 b0 c0 with ⟨a, b, c, h1⟩
    simp only [hbound a b c, hspde a b c (CPolyG.cRdeBoundDegree Dt fuel a b c : ℤ)]
    rcases hsp : CPolyG.cSPDE Dt fuel a b c (CPolyG.cRdeBoundDegree Dt fuel a b c : ℤ) with
      _ | ⟨bbar, cbar, m, α, β⟩
    · rfl
    · simp only [hpoly bbar cbar m]
      rcases hpr : CPolyG.cPolyRischDE Dt fuel bbar cbar m with _ | v <;> rfl

end CPolyG

/-! ### `native_decide` — the fuel-free §6.6 cancellation regimes on Bronstein's worked examples

The §6.6 cancellation deliverables, re-run **fuel-free**: the fuel-free own-loops compute the same
elementary solutions as the fuel'd versions, each verified by `native_decide` to *actually solve* the
equation (the cleared difference reads to `0`, not merely pinning the output). These exercise the base
ℚ-pipeline (`cRationalRDEWf`) the non-cancellation Examples 6.5.1/6.4.1 do not. Reuses the example data of
`ComputableRischDE`. -/

open CPolyG QFunNZ in
/-- **Example §6.6 primitive cancellation — fuel-free** (`native_decide`, Bronstein §6.6,
`PolyRischDECancelPrim`, book p.212). For the primitive monomial `t = log(x)` (`Dt = 1/x ∈ k`, `δ = 0`),
the cancellation equation `Dq + 1·q = log(x) + 1/x` (`b = 1 ∈ ℚ*`, `c = t + 1/x`, `deg(c) = 1`) is solved
**fuel-free** by `cPolyRischDECancelPrimWf`, returning some `q` verified to **actually solve** `Dq + b·q = c`
by `cisZeroG` of the cleared difference `D(q) + b·q − c` (`D = cmonomialDeriv rischDECancelDt`) — the book's
solution `q = log(x) = t`. The fuel-free dispatcher `cPolyRischDEWf` routes this same input to the
cancellation solver (`deg(b) = 0 = max(0, δ−1)`, `δ = 0`), producing an equal `q`. The fuel-free companion
of `rischDE_cancel_example`: the §6.6 primitive cancellation case — driving the eq. 6.23 base Risch DE over
`k = ℚ(x)` (`RischDE(1,1) = 1` via the now-fuel-free `cRischDEBaseWf`) — computes with **no fuel at
runtime**. -/
theorem rischDEWf_cancel_example :
    (match cPolyRischDECancelPrimWf rischDECancelDt rischDECancelB rischDECancelC 5 with
      | some q =>
          cisZeroG (csubG (caddG (cmonomialDeriv rischDECancelDt q) (cmulG rischDECancelB q))
            rischDECancelC)
      | none => false) = true
    ∧ (match cPolyRischDEWf rischDECancelDt rischDECancelB rischDECancelC 5,
            cPolyRischDECancelPrimWf rischDECancelDt rischDECancelB rischDECancelC 5 with
        | some q1, some q2 => cisZeroG (csubG q1 q2)
        | _, _ => false) = true := by native_decide

#print axioms rischDEWf_cancel_example

open CPolyG QFunNZ in
/-- **Example §6.6 non-constant base recursion — fuel-free** (`native_decide`, Bronstein §6.6 eq. 6.23,
book p.212). For the primitive monomial `t = log(x)` (`Dt = 1/x ∈ k`, `δ = 0`), the assembled fuel-free
solver `cRischDEWfFull` on `Dy + (1/x)y = 2·log(x) + 1` over ℚ(x)(t) — normal denominator → special
(trivial) → degree bound → SPDE → §6.6 primitive cancellation, the cancellation peeling the leading
monomial via the **non-constant** base RDE `RischDE(1/x, 2)` over `k = ℚ(x)` (the whole **fuel-free** base
ℚ-pipeline `cRationalRDEWf`, `s = x`) — returns `some (ynum, yden)` verified to **actually solve** the
equation by `rdeClearedCheck` (the cleared polynomial identity): the solution `y = x·log(x)`. The standalone
fuel-free base solve `cRischDEBaseWf (1/x) 2 = x` is verified to solve `Ds + (1/x)s = 2` (cleared
difference). The fuel-free companion of `rischDE_baseRecursion_example`: the **general (non-constant)
rational base Risch DE over ℚ(x)** computes fuel-free, and the §6.6 primitive cancellation drives it to
`y = x·log(x)` with **no fuel at runtime**. -/
theorem rischDEWf_baseRecursion_example :
    (match cRischDEWfFull rischDEBaseRecDt rischDEBaseRecFnum rischDEBaseRecFden
          rischDEBaseRecGnum rischDEBaseRecGden with
      | some (ynum, yden) =>
          rdeClearedCheck rischDEBaseRecDt rischDEBaseRecFnum rischDEBaseRecFden
            rischDEBaseRecGnum rischDEBaseRecGden ynum yden
      | none => false) = true
    ∧ (match cRischDEBaseWf (ofNumDen [1] [0, 1] (by decide)) (ofConstNZ 2) with
        | some s =>
            Compute.qeq (Compute.qadd (Compute.qadd (Compute.qderiv s.1)
                (Compute.qmul ([1], [0, 1]) s.1)) (Compute.qneg ([2], [1]))) Compute.qzero
        | none => false) = true := by native_decide

#print axioms rischDEWf_baseRecursion_example

open CPolyG QFunNZ in
/-- **The standalone rational Risch DE `Ds + (1/x)s = 2` over ℚ(x) computes fuel-free** (`native_decide`,
Bronstein §6.6 eq. 6.23 base solve). The fuel-free `cRationalRDEWf` — the whole Ch. 6 pipeline at the base
level (`t = x`, `k = ℚ`, `D = d/dx`, **no fuel at runtime**) — returns `some (snum, sden)`, and `s =
snum/sden` is verified to **actually solve** `Ds + (1/x)s = 2` by clearing denominators (the quotient-rule
identity reads to `0`). The solution `s = x` (returned unreduced `(x², x)`). The fuel-free companion of
`rischDE_rationalRDE_example`: exercises the base-level **weak normalizer** (`1/x` residue `1` at `x = 0`,
`q₁ = x`), **normal denominator**, **degree bound**, **SPDE**, and **polynomial integration** (`Du = 2x`),
all fuel-free. -/
theorem rischDEWf_rationalRDE_example :
    (match cRationalRDEWf [1] [0, 1] [2] [1] with
      | some (snum, sden) =>
          let Dsn := Compute.cderiv snum
          let Dsd := Compute.cderiv sden
          let x : Compute.CPoly := [0, 1]
          Compute.cisZero (Compute.csub
            (Compute.cadd
              (Compute.cmul (Compute.csub (Compute.cmul Dsn sden) (Compute.cmul snum Dsd)) x)
              (Compute.cmul snum sden))
            (Compute.cmul (Compute.cscale 2 (Compute.cmul sden sden)) x))
      | none => false) = true := by native_decide

#print axioms rischDEWf_rationalRDE_example

open CPolyG QFunNZ in
/-- **Example §6.6 hyperexponential cancellation — fuel-free** (`native_decide`, Bronstein §6.6,
`PolyRischDECancelExp`, book p.213). For the hyperexponential monomial `t = exp(x)` (`Dt = t`, `η = Dt/t =
1 ∈ k`, `δ = 1`), the cancellation equation `Dq + (1/x)·q = (2 + x)·exp(x)` (`b = 1/x ∈ ℚ(x)*`,
`c = (2+x)t`, `deg(c) = 1`) is solved **fuel-free** by `cPolyRischDECancelExpWf`, returning some `q` verified
to **actually solve** `Dq + b·q = c` by `cisZeroG` of the cleared difference `D(q) + b·q − c`
(`D = cmonomialDeriv rischDEExpDt`) — the solution `q = x·exp(x)`. The fuel-free dispatcher `cPolyRischDEWf`
routes this same input to the hyperexponential cancellation solver (`deg(b) = 0`, `δ = 1`), producing an
equal `q`. The fuel-free companion of `rischDE_cancelExp_example`: `PolyRischDECancelExp` — driving the
eq. 6.24 base Risch DE `RischDE(1/x + 1, x+2)` over `k = ℚ(x)` (a **non-constant** base solve via the
now-fuel-free `cRischDEBaseWf`, `s = x`) — computes with **no fuel at runtime**. -/
theorem rischDEWf_cancelExp_example :
    (match cPolyRischDECancelExpWf rischDEExpDt rischDEExpB rischDEExpC 5 with
      | some q =>
          cisZeroG (csubG (caddG (cmonomialDeriv rischDEExpDt q) (cmulG rischDEExpB q))
            rischDEExpC)
      | none => false) = true
    ∧ (match cPolyRischDEWf rischDEExpDt rischDEExpB rischDEExpC 5,
            cPolyRischDECancelExpWf rischDEExpDt rischDEExpB rischDEExpC 5 with
        | some q1, some q2 => cisZeroG (csubG q1 q2)
        | _, _ => false) = true := by native_decide

#print axioms rischDEWf_cancelExp_example

end DeepWiki.SymbolicIntegration
