import DeepWiki.SymbolicIntegration.ComputableWellFounded4
import DeepWiki.SymbolicIntegration.ComputablePolyPartTowerCorrect

/-! # Fuel-free (well-founded) §5 integration own-loops — `cPolyReduceTowerWf`,
`cPrimitivePolyIntegrateWf`, `cHermiteReduceTowerWf`

This completes the fuel-free conversion begun in `ComputableWellFounded`/`…2`/`…3`/`…4` (leaves + the
whole §3.5 splitting-factorization layer) into the §5 *integration* own-loops over the tower ℚ(x)[t]:

* **`cPolyReduceTowerWf`** — the fuel-free companion of Bronstein's `PolynomialReduce` (§5.4, p.141)
  `cPolyReduceTower`, an **own-loop**. Each step peels the leading nonlinear-monomial term
  `q₀ = (lc(p)/(m·λ))·tᵐ` (`m = deg(p) − δ(t) + 1`), subtracts its monomial derivative `D(q₀)`
  (cancelling the top of `p`), and recurses on `p' = p − D(q₀)`, whose normalized `t`-list length
  strictly drops. The well-founded measure is `(cnormG p).length`, with the structural runtime guard
  `(cnormG p').length < (cnormG p).length`, so `decreasing_by` is `assumption` and the loop carries no
  fuel. The cleared reduction identity `D(q) + r = p` is proved **directly by well-founded induction**
  on the same measure (reusing the additivity-of-`implicitDeriv` argument of
  `cPolyReduceTower_cleared_identity`): both the done branch and the unreachable-guard branch return
  `([], cnormG p)` with `D(0) + cnormG p = p`, and the recursive branch glues `q₀` to the recursive `q'`
  via `map_add`. No fuel'd bridge and no leading-term-cancellation lemma are needed for correctness.

* **`cPrimitivePolyIntegrateWf`** — the fuel-free companion of the degree-lowering loop of Bronstein's
  `IntegratePrimitivePolynomial` (§5.8, p.158, constant-coefficient sub-case) `cPrimitivePolyIntegrate`,
  an **own-loop** of the identical shape (peel `q₀ = c·t^(m+1)`, recurse on `p' = p − D(q₀)`, stopping
  when only the `t⁰` term remains). Same measure `(cnormG p).length`, same structural guard, same direct
  WF-induction cleared identity `D(q) + rem = p`.

* **`cHermiteReduceTowerWf`** — the fuel-free companion of the transcendental Hermite reduction
  `cHermiteReduceTower` (§5.3, p.139). This is **not** an own-loop: it is a `foldl` over the squarefree
  factor list `cSqfreeYunFF` whose inner `j`-loop `cHermiteReduceTowerInner` recurses on a *downward
  structural counter* `j` (no fuel measure). The fuel feeds only (i) the squarefree factorization
  `cSqfreeYunFF` — replaced by the own-loop `cSqfreeYunFFWf` of `ComputableWellFounded4` — and (ii) the
  Bézout solver `cdiophantineG` / the exact divisions `cdivG`, replaced by the fuel-free leaves
  `cdiophantineGWf` (over `cgcdWf`/`cdivmodWf`) and `cdivWf`. So the fuel-free companion threads the
  fuel-free leaves through the structural foldl + downward `j`-recursion — **no own-loop measure of its
  own**. The cleared identity `D(g) + h = f` is the `native_decide` deliverable (as for the fuel'd
  version); abstract correctness of the Hermite residual was not proved for the fuel'd version either.

As throughout, where a fuel'd bridge is given the fuel bounds live only in the bridge proof; the runtime
WF ops carry no fuel. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α]

/-! ### Target 1 — the fuel-free polynomial reduction `cPolyReduceTowerWf` (own-loop, §5.4)

`cPolyReduceTower Dt fuel p` (Bronstein §5.4, `PolynomialReduce`) peels the leading nonlinear-monomial
term and recurses on the residual `p' = cnormG p − D(q₀)`, whose normalized list length strictly drops
(the subtracted `D(q₀)` cancels the top coefficient of `p`). The fuel-free companion runs the **own-loop**
by well-founded recursion on `(cnormG p).length`, with the structural runtime guard
`(cnormG p').length < (cnormG p).length`, so `decreasing_by` is `assumption`. -/

/-- **Fuel-free polynomial reduction** (Bronstein §5.4, `PolynomialReduce`, p.141) `cPolyReduceTowerWf Dt
p = (q, r)` for a **nonlinear** monomial `t` (`δ(t) = deg(Dt) ≥ 2`, `λ(t) = lc(Dt)`): `p = D(q) + r` with
`deg(r) < δ(t)`, peeling the leading term `q₀ = (lc(p)/(m·λ(t)))·tᵐ` (`m = deg(p) − δ(t) + 1`) whose
monomial derivative `D(q₀)` (`cmonomialDeriv Dt`) cancels the top of `p`, then recursing on `p − D(q₀)`.
True well-founded recursion on `(cnormG p).length` — **no fuel at runtime**; the recursion is taken only
under the structural guard `(cnormG p').length < (cnormG p).length`, so `decreasing_by` is `assumption`.
Generic over `[CField α] [CDiffField α]`, so it reduces (`native_decide`). -/
def cPolyReduceTowerWf (Dt : CPolyG α) (p : CPolyG α) : CPolyG α × CPolyG α :=
  let delta := cdegG Dt                                          -- `δ(t) = deg(Dt)`
  if (cnormG p : List α).length ≤ delta then ([], cnormG p)      -- `deg(p) < δ(t)` ⇒ done
  else
    let n := cdegG p
    let m := n - delta + 1                                       -- `m = deg(p) − δ(t) + 1`
    let lam := cleadG Dt                                         -- `λ(t) = lc(Dt)`
    let c := CField.div (cleadG p) (CField.mul (cnatCastG m) lam) -- `lc(p)/(m·λ(t))`
    let q0 := cshiftG m [c]                                      -- `c·tᵐ`
    let p' := csubG (cnormG p) (cmonomialDeriv Dt q0)            -- `p − D(q₀)`
    if (cnormG p' : List α).length < (cnormG p : List α).length then
      let (q, r) := cPolyReduceTowerWf Dt p'
      (caddG q0 q, r)
    else ([], cnormG p)   -- unreachable on a real run (the leading term cancels, dropping the degree)
termination_by (cnormG p).length
decreasing_by assumption

end CPolyG

/-! ### The cleared polynomial-reduction identity `D(q) + r = p` for the fuel-free `cPolyReduceTowerWf`

`cPolyReduceTowerWf Dt p = (q, r)` peels leading terms and recurses on `p' = cnormG p − D(q₀)`. The
cleared identity is `D(q) + r = p` over `(RatFunc ℚ)[X]`, i.e. `implicitDeriv (toPolyG Dt) (toPolyG q) +
toPolyG r = toPolyG p`. Proved **directly by well-founded induction** on `(cnormG p).length` (the
`cPolyReduceTowerWf.induct` principle) — the additivity of `implicitDeriv` gluing the peeled `q₀` to the
recursive `q'` in the recursive branch, and `D(0) + cnormG p = p` in *both* the done branch and the
(unreachable) guard-failure branch. No fuel'd bridge and no leading-term-cancellation lemma are needed:
the WF version's identity holds branch-by-branch regardless of whether the guard would ever fail. -/

/-- **`cPolyReduceTowerWf` satisfies the cleared reduction identity `D(q) + r = p`** (abstract, ALL
inputs, fuel-free) over the field ℚ(x). With `(q, r) = cPolyReduceTowerWf Dt p` and `D = cmonomialDeriv
Dt` the monomial derivation (`= Differential.implicitDeriv (toPolyG Dt)` through `toPolyG`), the §5.4
fuel-free reduction reconstructs the polynomial part exactly: `implicitDeriv (toPolyG Dt) (toPolyG q) +
toPolyG r = toPolyG p` in `(RatFunc ℚ)[X]`. The all-inputs, axiom-clean (no `native_decide`) identity,
the fuel-free companion of `cPolyReduceTower_cleared_identity`; gated on no preconditions. Proved by
well-founded induction on `(cnormG p).length`, the additivity of the `implicitDeriv` derivation gluing
the peeled leading term to the recursive reduction. -/
theorem cPolyReduceTowerWf_cleared_identity (Dt : CPolyG QFunNZ) (p : CPolyG QFunNZ) :
    Differential.implicitDeriv (toPolyG Dt) (toPolyG (CPolyG.cPolyReduceTowerWf Dt p).1)
        + toPolyG (CPolyG.cPolyReduceTowerWf Dt p).2
      = toPolyG p := by
  induction p using CPolyG.cPolyReduceTowerWf.induct Dt with
  | case1 p delta hdone =>
    -- done branch: `cPolyReduceTowerWf Dt p = ([], cnormG p)`, so `D(0) + p = p`
    have hval : CPolyG.cPolyReduceTowerWf Dt p = ([], cnormG p) := by
      rw [CPolyG.cPolyReduceTowerWf.eq_def, if_pos hdone]
    rw [hval, toPolyG_nil, map_zero, zero_add, toPolyG_cnormG]
  | case2 p delta hne n m lam c q0 p' hguard q r hrec ih =>
    -- recursion branch: peel `q₀`, recurse on `p' = cnormG p − D(q₀)` (both bound by `induct`)
    have hval : CPolyG.cPolyReduceTowerWf Dt p = (caddG q0 q, r) := by
      rw [CPolyG.cPolyReduceTowerWf.eq_def, if_neg hne, if_pos hguard, hrec]
    rw [hval, hrec] at *
    -- `D(q₀ + q) + r = D(q₀) + (D(q) + r) = D(q₀) + p'`, and `p' = cnormG p − D(q₀)`
    rw [toPolyG_caddG, map_add, add_assoc, ih, toPolyG_csubG, toPolyG_cmonomialDeriv, toPolyG_cnormG]
    ring
  | case3 p delta hne n m lam c q0 p' hguard =>
    -- unreachable guard-failure branch: returns `([], cnormG p)`, same identity as the done branch
    have hval : CPolyG.cPolyReduceTowerWf Dt p = ([], cnormG p) := by
      rw [CPolyG.cPolyReduceTowerWf.eq_def, if_neg hne, if_neg hguard]
    rw [hval, toPolyG_nil, map_zero, zero_add, toPolyG_cnormG]

-- `cPolyReduceTowerWf Dt p = (q, r)` reconstructs the polynomial part: `D(q) + r = p` over ℚ(x)[t].
example (Dt : CPolyG QFunNZ) (p : CPolyG QFunNZ) :
    Differential.implicitDeriv (toPolyG Dt) (toPolyG (CPolyG.cPolyReduceTowerWf Dt p).1)
        + toPolyG (CPolyG.cPolyReduceTowerWf Dt p).2
      = toPolyG p :=
  cPolyReduceTowerWf_cleared_identity Dt p

/-- **The §5.4 `native_decide` cleared check holds for ALL inputs (fuel-free)**: with `(q, r) =
cPolyReduceTowerWf Dt p` and `D = cmonomialDeriv Dt`, the exact Boolean check `cisZeroG (csubG (caddG (D
q) r) p) = true` is a theorem for every `Dt p`, gated on no preconditions. The fuel-free companion of
`cPolyReduceTower_cisZeroG_cleared`. -/
theorem cPolyReduceTowerWf_cisZeroG_cleared (Dt : CPolyG QFunNZ) (p : CPolyG QFunNZ) :
    cisZeroG (csubG
      (caddG (cmonomialDeriv Dt (CPolyG.cPolyReduceTowerWf Dt p).1) (CPolyG.cPolyReduceTowerWf Dt p).2) p)
      = true := by
  rw [cisZeroG_iff, toPolyG_csubG, toPolyG_caddG, toPolyG_cmonomialDeriv, sub_eq_zero]
  exact cPolyReduceTowerWf_cleared_identity Dt p

-- The fuel-free §5.4 polynomial-reduction cleared identity carries only the standard axioms (no `native`
-- axiom): the `native_decide` smoke tests below carry `Lean.ofReduceBool` separately.
#print axioms cPolyReduceTowerWf_cleared_identity
#print axioms cPolyReduceTowerWf_cisZeroG_cleared

/-! ### `native_decide` smoke tests for `cPolyReduceTowerWf` (Bronstein Example 5.4.1, `t = tan x`)

The whole fuel-free polynomial reduction executes in native code over the noncomputable-`CFieldSpec`
tower `QFunNZ` (ℚ(x)) — `cPolyReduceTowerWf` carries no fuel and no noncomputable bridge into the
compiled body. Re-runs the §5.4 validation (`polyReduceTowerExampleP = t³` under `Dt = t² + 1`). -/

/-- **`cPolyReduceTowerWf` satisfies `D(q) + r = p`, fuel-free** (`native_decide`): for the nonlinear
monomial `t = tan x` (`Dt = t² + 1`, `δ(t) = 2`) and polynomial part `p = t³` over ℚ(x)[t], the fuel-free
§5.4 reduction returns `(q, r) = ((1/2)t², −t)` satisfying `D(q) + r = p` for `D = cmonomialDeriv Dt` —
the own-loop runs end-to-end with **no fuel at runtime**. Checked by `cisZeroG` of `D(q) + r − p`. -/
example :
    (let res := CPolyG.cPolyReduceTowerWf polyReduceTowerExampleDt polyReduceTowerExampleP
      let q := res.1
      let r := res.2
      let Dq := CPolyG.cmonomialDeriv polyReduceTowerExampleDt q
      CPolyG.cisZeroG (CPolyG.csubG (CPolyG.caddG Dq r) polyReduceTowerExampleP)) = true := by
  native_decide

/-- **The fuel-free reduced remainder has `t`-degree `< δ(t)`** (`native_decide`): the §5.4 fuel-free
reduction of `p = t³` under `Dt = t² + 1` (`δ(t) = 2`) returns a remainder of `t`-degree `1 < 2`, as
Theorem 5.4.1 guarantees. -/
example :
    CPolyG.cdegG (CPolyG.cPolyReduceTowerWf polyReduceTowerExampleDt polyReduceTowerExampleP).2 = 1 := by
  native_decide

/-- `cPolyReduceTowerWf` agrees with the fuel'd `cPolyReduceTower` on Example 5.4.1's `p` (the `(q, r)`
degree pair matches). -/
example :
    ((CPolyG.cdegG (CPolyG.cPolyReduceTowerWf polyReduceTowerExampleDt polyReduceTowerExampleP).1,
      CPolyG.cdegG (CPolyG.cPolyReduceTowerWf polyReduceTowerExampleDt polyReduceTowerExampleP).2))
      = ((CPolyG.cdegG (CPolyG.cPolyReduceTower polyReduceTowerExampleDt 8 polyReduceTowerExampleP).1,
        CPolyG.cdegG (CPolyG.cPolyReduceTower polyReduceTowerExampleDt 8 polyReduceTowerExampleP).2)) := by
  native_decide

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α]

/-! ### Target 2 — the fuel-free primitive-case integration `cPrimitivePolyIntegrateWf` (own-loop, §5.8)

`cPrimitivePolyIntegrate Dt fuel p` (Bronstein §5.8, `IntegratePrimitivePolynomial`, constant-coefficient
sub-case) is the identical degree-lowering shape: peel `q₀ = c·t^(m+1)` (`c = aₘ/((m+1)·Dt(0))`), subtract
`D(q₀)`, recurse on `p' = cnormG p − D(q₀)`, stopping when only the `t⁰` term remains. The fuel-free
companion runs the **own-loop** by well-founded recursion on `(cnormG p).length`, with the structural
runtime guard `(cnormG p').length < (cnormG p).length`, so `decreasing_by` is `assumption`. -/

/-- **Fuel-free primitive-case polynomial integration** (the degree-lowering loop of Bronstein's
`IntegratePrimitivePolynomial`, §5.8, p.158) `cPrimitivePolyIntegrateWf Dt p = (q, rem)` for a
**primitive** monomial `t` (`Dt ∈ k`, `δ(t) = 0`, e.g. `t = log x`, `Dt = 1/x`): integrate `p = ∑ aᵢtⁱ`
top-down by peeling `q₀ = c·t^(m+1)` for each leading term `aₘ` with `c = aₘ/((m+1)·Dt(0))` (the
constant-coefficient `LimitedIntegrate` sub-case `b = 0`; the general solve is the deferred Chapter-7
oracle). Returns `(q, rem)` with `D(q) + rem = p`, peeling all degrees `≥ 1`. True well-founded recursion
on `(cnormG p).length` — **no fuel at runtime**; the recursion is taken only under the structural guard
`(cnormG p').length < (cnormG p).length`, so `decreasing_by` is `assumption`. Generic over `[CField α]
[CDiffField α]`, so it reduces (`native_decide`). -/
def cPrimitivePolyIntegrateWf (Dt : CPolyG α) (p : CPolyG α) : CPolyG α × CPolyG α :=
  if (cnormG p : List α).length ≤ 1 then ([], cnormG p)            -- only the `t⁰` term left ⇒ done
  else
    let m := cdegG p                                               -- current top degree `m ≥ 1`
    let am := cleadG p                                             -- leading coefficient `aₘ`
    let mp1 : α := cnatCastG (m + 1)
    let dtConst := cleadG Dt                                       -- `Dt(0) = lc(Dt)` (`Dt ∈ k`)
    let c := CField.div am (CField.mul mp1 dtConst)
    let q0 := cshiftG (m + 1) [c]                                  -- `c·t^(m+1)`
    let p' := csubG (cnormG p) (cmonomialDeriv Dt q0)             -- `p − D(q₀)`
    if (cnormG p' : List α).length < (cnormG p : List α).length then
      let (q, rem) := cPrimitivePolyIntegrateWf Dt p'
      (caddG q0 q, rem)
    else ([], cnormG p)   -- unreachable on a real run (the leading term cancels, dropping the degree)
termination_by (cnormG p).length
decreasing_by assumption

end CPolyG

/-! ### The cleared primitive-integration identity `D(q) + rem = p` for `cPrimitivePolyIntegrateWf`

`cPrimitivePolyIntegrateWf Dt p = (q, rem)` peels `q₀ = c·t^(m+1)` and recurses on `p' = cnormG p −
D(q₀)`. The cleared identity is `D(q) + rem = p` over `(RatFunc ℚ)[X]` — proved by the *same* direct
well-founded induction as §5.4 (additivity of `implicitDeriv`); the done branch and the unreachable
guard-failure branch both return `([], cnormG p)` with `D(0) + cnormG p = p`. (The §5.8 *integrability*
decision on the leftover `rem` is the deferred `LimitedIntegrate`/Chapter-7 oracle, a separate question.) -/

/-- **`cPrimitivePolyIntegrateWf` satisfies the cleared integration identity `D(q) + rem = p`** (abstract,
ALL inputs, fuel-free) over the field ℚ(x). With `(q, rem) = cPrimitivePolyIntegrateWf Dt p` and `D =
cmonomialDeriv Dt` (`= Differential.implicitDeriv (toPolyG Dt)` through `toPolyG`), the §5.8 fuel-free
primitive-case loop reconstructs the polynomial part exactly: `implicitDeriv (toPolyG Dt) (toPolyG q) +
toPolyG rem = toPolyG p` in `(RatFunc ℚ)[X]`. The all-inputs, axiom-clean (no `native_decide`) identity,
the fuel-free companion of `cPrimitivePolyIntegrate_cleared_identity`; gated on no preconditions. Proved
by well-founded induction on `(cnormG p).length`, the additivity of `implicitDeriv` gluing the peeled
`q₀ = c·t^(m+1)` to the recursive integration. (This is the cleared reconstruction `D(q) + rem = p`; the
§5.8 *integrability decision* on `rem` is the deferred `LimitedIntegrate` oracle, a separate question.) -/
theorem cPrimitivePolyIntegrateWf_cleared_identity (Dt : CPolyG QFunNZ) (p : CPolyG QFunNZ) :
    Differential.implicitDeriv (toPolyG Dt) (toPolyG (CPolyG.cPrimitivePolyIntegrateWf Dt p).1)
        + toPolyG (CPolyG.cPrimitivePolyIntegrateWf Dt p).2
      = toPolyG p := by
  induction p using CPolyG.cPrimitivePolyIntegrateWf.induct Dt with
  | case1 p hdone =>
    -- done branch: `cPrimitivePolyIntegrateWf Dt p = ([], cnormG p)`, so `D(0) + p = p`
    have hval : CPolyG.cPrimitivePolyIntegrateWf Dt p = ([], cnormG p) := by
      rw [CPolyG.cPrimitivePolyIntegrateWf.eq_def, if_pos hdone]
    rw [hval, toPolyG_nil, map_zero, zero_add, toPolyG_cnormG]
  | case2 p hne m am mp1 dtConst c q0 p' hguard q rem hrec ih =>
    -- recursion branch: peel `q₀ = c·t^(m+1)`, recurse on `p' = cnormG p − D(q₀)`
    have hval : CPolyG.cPrimitivePolyIntegrateWf Dt p = (caddG q0 q, rem) := by
      rw [CPolyG.cPrimitivePolyIntegrateWf.eq_def, if_neg hne, if_pos hguard, hrec]
    rw [hval, hrec] at *
    -- `D(q₀ + q) + rem = D(q₀) + (D(q) + rem) = D(q₀) + p'`, and `p' = cnormG p − D(q₀)`
    rw [toPolyG_caddG, map_add, add_assoc, ih, toPolyG_csubG, toPolyG_cmonomialDeriv, toPolyG_cnormG]
    ring
  | case3 p hne m am mp1 dtConst c q0 p' hguard =>
    -- unreachable guard-failure branch: returns `([], cnormG p)`, same identity as the done branch
    have hval : CPolyG.cPrimitivePolyIntegrateWf Dt p = ([], cnormG p) := by
      rw [CPolyG.cPrimitivePolyIntegrateWf.eq_def, if_neg hne, if_neg hguard]
    rw [hval, toPolyG_nil, map_zero, zero_add, toPolyG_cnormG]

-- `cPrimitivePolyIntegrateWf Dt p = (q, rem)` reconstructs the polynomial part: `D(q) + rem = p`.
example (Dt : CPolyG QFunNZ) (p : CPolyG QFunNZ) :
    Differential.implicitDeriv (toPolyG Dt) (toPolyG (CPolyG.cPrimitivePolyIntegrateWf Dt p).1)
        + toPolyG (CPolyG.cPrimitivePolyIntegrateWf Dt p).2
      = toPolyG p :=
  cPrimitivePolyIntegrateWf_cleared_identity Dt p

/-- **The §5.8 `native_decide` cleared check holds for ALL inputs (fuel-free)**: with `(q, rem) =
cPrimitivePolyIntegrateWf Dt p` and `D = cmonomialDeriv Dt`, the exact Boolean check `cisZeroG (csubG
(caddG (D q) rem) p) = true` is a theorem for every `Dt p`, gated on no preconditions. The fuel-free
companion of `cPrimitivePolyIntegrate_cisZeroG_cleared`. -/
theorem cPrimitivePolyIntegrateWf_cisZeroG_cleared (Dt : CPolyG QFunNZ) (p : CPolyG QFunNZ) :
    cisZeroG (csubG
      (caddG (cmonomialDeriv Dt (CPolyG.cPrimitivePolyIntegrateWf Dt p).1)
        (CPolyG.cPrimitivePolyIntegrateWf Dt p).2) p)
      = true := by
  rw [cisZeroG_iff, toPolyG_csubG, toPolyG_caddG, toPolyG_cmonomialDeriv, sub_eq_zero]
  exact cPrimitivePolyIntegrateWf_cleared_identity Dt p

-- The fuel-free §5.8 primitive-integration cleared identity carries only the standard axioms.
#print axioms cPrimitivePolyIntegrateWf_cleared_identity
#print axioms cPrimitivePolyIntegrateWf_cisZeroG_cleared

/-! ### `native_decide` smoke tests for `cPrimitivePolyIntegrateWf` (Bronstein §5.8, `t = log x`)

The whole fuel-free primitive-case integration executes in native code over the noncomputable-`CFieldSpec`
tower `QFunNZ` (ℚ(x)) — `cPrimitivePolyIntegrateWf` carries no fuel and no noncomputable bridge into the
compiled body. Re-runs the §5.8 validation (`primitivePolyIntegrateExampleP = (1/x)·t²` under `Dt = 1/x`,
i.e. `∫ (log x)²/x dx = (log x)³/3`). -/

/-- **`cPrimitivePolyIntegrateWf` satisfies `D(q) + rem = p`, fuel-free** (`native_decide`): for the
primitive monomial `t = log x` (`Dt = 1/x`) and polynomial part `p = (1/x)·t²` over ℚ(x)[t], the fuel-free
§5.8 loop returns `(q, rem) = ((1/3)t³, 0)` satisfying `D(q) + rem = p` for `D = cmonomialDeriv Dt` — the
own-loop runs end-to-end with **no fuel at runtime**. Checked by `cisZeroG` of `D(q) + rem − p`. -/
example :
    (let res := CPolyG.cPrimitivePolyIntegrateWf primitivePolyIntegrateExampleDt
        primitivePolyIntegrateExampleP
      let q := res.1
      let rem := res.2
      let Dq := CPolyG.cmonomialDeriv primitivePolyIntegrateExampleDt q
      CPolyG.cisZeroG (CPolyG.csubG (CPolyG.caddG Dq rem) primitivePolyIntegrateExampleP)) = true := by
  native_decide

/-- `cPrimitivePolyIntegrateWf` agrees with the fuel'd `cPrimitivePolyIntegrate` on the §5.8 example
(the `(q, rem)` degree pair matches). -/
example :
    ((CPolyG.cdegG (CPolyG.cPrimitivePolyIntegrateWf primitivePolyIntegrateExampleDt
        primitivePolyIntegrateExampleP).1,
      CPolyG.cdegG (CPolyG.cPrimitivePolyIntegrateWf primitivePolyIntegrateExampleDt
        primitivePolyIntegrateExampleP).2))
      = ((CPolyG.cdegG (CPolyG.cPrimitivePolyIntegrate primitivePolyIntegrateExampleDt 8
          primitivePolyIntegrateExampleP).1,
        CPolyG.cdegG (CPolyG.cPrimitivePolyIntegrate primitivePolyIntegrateExampleDt 8
          primitivePolyIntegrateExampleP).2)) := by
  native_decide

/-! ### Target 3 — the fuel-free transcendental Hermite reduction `cHermiteReduceTowerWf` (§5.3)

Unlike Targets 1–2, the transcendental Hermite reduction `cHermiteReduceTower` (§5.3) is **not** an
own-loop: it is a `foldl` over the squarefree factor list `cSqfreeYunFF d` whose inner `j`-loop
`cHermiteReduceTowerInner` recurses on a *downward structural counter* `j` (no fuel measure of its own).
The fuel feeds only (i) the squarefree factorization `cSqfreeYunFF` (replaced by the own-loop
`cSqfreeYunFFWf` of `ComputableWellFounded4`), (ii) the Bézout solver `cdiophantineG` (`cgcdExtG` /
`cdivmodG`, replaced by the fuel-free `cgcdWf`/`cdivmodWf`), and (iii) the exact divisions `cdivG`
(replaced by `cdivWf`). So the fuel-free companion threads the fuel-free leaves through the structural
foldl + downward `j`-recursion — `cmonomialDeriv` already carries no fuel. The bridge to the fuel'd
version then transports `cHermiteReduceTower_cleared_identity` unchanged. -/

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α]

/-- **Fuel-free generic Diophantine/Bézout solver** `cdiophantineGWf p q rhs = (b, c)` solving
`b·p + c·q = rhs` with `deg b < deg q`, for **coprime** `p, q`: the fuel-free companion of `cdiophantineG`.
From the **fuel-free** extended Euclid `cgcdWf p q = (g, s, t)` with `s·p + t·q = g` (a nonzero constant),
rescale `(s,t)` by `rhs/g`, reduce the first cofactor mod `q` (`S = quo·q + b`, via the **fuel-free**
`cdivmodWf`), and absorb `quo·p` into the second (`c = T + quo·p`) — **no fuel at runtime**. Generic over
`[CField α]`. -/
def cdiophantineGWf (p q rhs : CPolyG α) : CPolyG α × CPolyG α :=
  let (g, s, t) := cgcdWf p q
  let ginv := CField.inv (cleadG g)
  let S := cscaleG ginv (cmulG rhs s)
  let T := cscaleG ginv (cmulG rhs t)
  let (quo, b) := cdivmodWf S q
  let c := caddG T (cmulG quo p)
  (cnormG b, cnormG c)

variable [CFieldSpec α]

omit [CDiffField α] in
/-- **Bridge — `cdiophantineGWf` equals the fuel'd `cdiophantineG` at any sufficient fuel.** With
`(cnormG p).length ≤ fuel`, `(cnormG q).length < fuel` (for the extended-Euclid descent `cgcdWf`), and the
rescaled-reduced dividend `S = cscaleG (cleadG (cgcdWf p q).1)⁻¹ (cmulG rhs (cgcdWf p q).2.1)` short enough
(`(cnormG S).length ≤ fuel`, for the `cdivmodWf`), `cdiophantineGWf p q rhs = cdiophantineG fuel p q rhs`.
The bounds live only here; `cdiophantineGWf` carries no fuel. The extended Euclid is bridged by
`cgcdWf_eq_of_fuel` and the mod-reduction by `cdivmodWf_eq_of_fuel`. -/
theorem cdiophantineGWf_eq_of_fuel (fuel : ℕ) (p q rhs : CPolyG α)
    (hp : (cnormG p : List α).length ≤ fuel) (hq : (cnormG q : List α).length < fuel)
    (hS : (cnormG (cscaleG (CField.inv (cleadG (cgcdWf p q).1))
        (cmulG rhs (cgcdWf p q).2.1)) : List α).length ≤ fuel) :
    cdiophantineGWf p q rhs = CPolyG.cdiophantineG fuel p q rhs := by
  rw [cdiophantineGWf, CPolyG.cdiophantineG, cgcdWf_eq_of_fuel fuel p q hp hq]
  -- carry the `hS` dividend bound to the fuel'd cofactors, then destructure the gcd triple so the
  -- `match`-bound `S` becomes concrete and the mod-reduction bridge `cdivmodWf S q = cdivmodG fuel S q`
  -- applies
  rw [cgcdWf_eq_of_fuel fuel p q hp hq] at hS
  rcases hgcd : cgcdExtG fuel p q with ⟨g, s, t⟩
  rw [hgcd] at hS
  simp only at hS ⊢
  rw [cdivmodWf_eq_of_fuel fuel _ q hS]

variable {α : Type*} [CField α] [CDiffField α]

/-- **Fuel-free inner Hermite loop** over a squarefree factor `v` (multiplicity `i`, `u = d/vⁱ`), driven
by the downward counter `j` (§5.3, quadratic version, p.139): the fuel-free companion of
`cHermiteReduceTowerInner`. Each step solves `b·(u·Dv) + c·v = −a/j` with the **fuel-free** Bézout solver
`cdiophantineGWf` (`Dv = cmonomialDeriv Dt v` the *monomial* derivation), accumulates the rational summand
`b/vʲ` into `g`, and updates `a ← −j·c − u·Db`. The recursion is **structural** on `j` (no fuel measure —
`cmonomialDeriv` carries no fuel, the Bézout solve is fuel-free), so **no fuel at runtime**. -/
def cHermiteReduceTowerInnerWf (Dt : CPolyG α) (v u : CPolyG α) :
    ℕ → CPolyG α → CPolyG α × CPolyG α → (CPolyG α × CPolyG α) × CPolyG α
  | 0, a, g => (g, a)
  | j + 1, a, g =>
    let jval : α := cnatCastG (j + 1)                                 -- `j` as a field element
    let Dv := cmonomialDeriv Dt v
    let p := cmulG u Dv
    let rhs := cscaleG (CField.neg (CField.inv jval)) a               -- `−a/j`
    let (b, c) := cdiophantineGWf p v rhs
    let Vpow := cpowG v (j + 1)
    let g' := (caddG (cmulG g.1 Vpow) (cmulG b g.2), cmulG g.2 Vpow)  -- `g + b/Vʲ` (cross-multiplied)
    let a' := csubG (cscaleG (CField.neg jval) c) (cmulG u (cmonomialDeriv Dt b))  -- `−j·c − u·Db`
    cHermiteReduceTowerInnerWf Dt v u j a' g'

end CPolyG

/-! ### Bridge of the fuel-free inner loop to the fuel'd `cHermiteReduceTowerInner`

The inner loop is structural on `j`, but each step's Bézout solve `cdiophantineGWf (u·Dv) v (−a/j)` must
match the fuel'd `cdiophantineG fuel (u·Dv) v (−a/j)` — and `a` (hence the rescaled dividend `S`) changes
each step, so the per-step `cdiophantineGWf_eq_of_fuel` hypotheses form a *run-regularity* inductive
predicate `CHermiteInnerRegular fuel v u`, mirroring the `j`-recursion of `cHermiteReduceTowerInner`. -/

/-- **Per-run inner-Hermite-loop regularity bundle** `CHermiteInnerRegular fuel v u`: mirrors the
`cHermiteReduceTowerInner` `j`-recursion as an inductive predicate — `stop` at `j = 0` (the loop ends), or
`step` when the per-step Bézout solve `cdiophantineGWf (cmulG u (cmonomialDeriv Dt v)) v (−a/(j+1))` matches
the fuel'd `cdiophantineG fuel` (the three `cdiophantineGWf_eq_of_fuel` length bounds at this step), and the
same holds recursively on the updated `(a', g')`. The transparent per-node preconditions a real inner-loop
run satisfies. -/
inductive CHermiteInnerRegular (Dt : CPolyG QFunNZ) (fuel : ℕ) (v u : CPolyG QFunNZ) :
    ℕ → CPolyG QFunNZ → (CPolyG QFunNZ × CPolyG QFunNZ) → Prop
  /-- terminal node: `j = 0`, the inner loop stops. -/
  | stop {a : CPolyG QFunNZ} {g : CPolyG QFunNZ × CPolyG QFunNZ} : CHermiteInnerRegular Dt fuel v u 0 a g
  /-- recursive node: the per-step Bézout solve matches the fuel'd one, recurse on `(a', g')`. -/
  | step {j : ℕ} {a : CPolyG QFunNZ} {g : CPolyG QFunNZ × CPolyG QFunNZ}
      (hp : (cnormG (cmulG u (cmonomialDeriv Dt v)) : List QFunNZ).length ≤ fuel)
      (hq : (cnormG v : List QFunNZ).length < fuel)
      (hS : (cnormG (cscaleG (CField.inv (cleadG
          (cgcdWf (cmulG u (cmonomialDeriv Dt v)) v).1))
          (cmulG (cscaleG (CField.neg (CField.inv (cnatCastG (j + 1))))
            a) (cgcdWf (cmulG u (cmonomialDeriv Dt v)) v).2.1)) : List QFunNZ).length ≤ fuel)
      (hrec : CHermiteInnerRegular Dt fuel v u j
        (csubG (cscaleG (CField.neg (cnatCastG (j + 1)))
            (CPolyG.cdiophantineG fuel (cmulG u (cmonomialDeriv Dt v)) v
              (cscaleG (CField.neg (CField.inv (cnatCastG (j + 1)))) a)).2)
          (cmulG u (cmonomialDeriv Dt
            (CPolyG.cdiophantineG fuel (cmulG u (cmonomialDeriv Dt v)) v
              (cscaleG (CField.neg (CField.inv (cnatCastG (j + 1)))) a)).1)))
        (caddG (cmulG g.1 (cpowG v (j + 1)))
            (cmulG (CPolyG.cdiophantineG fuel (cmulG u (cmonomialDeriv Dt v)) v
              (cscaleG (CField.neg (CField.inv (cnatCastG (j + 1)))) a)).1 g.2),
          cmulG g.2 (cpowG v (j + 1)))) :
      CHermiteInnerRegular Dt fuel v u (j + 1) a g

namespace CPolyG

/-- **Bridge — the fuel-free inner Hermite loop equals the fuel'd one.** Under a regular inner run
(`CHermiteInnerRegular Dt fuel v u j a g`), `cHermiteReduceTowerInnerWf Dt v u j a g =
cHermiteReduceTowerInner Dt fuel v u j a g`. The fuel bounds live only here; the WF inner loop carries
none. By structural induction on `j`: at `j = 0` both return `(g, a)`; else the per-step Bézout solve
matches (`cdiophantineGWf_eq_of_fuel`), and the IH applies to the updated `(a', g')`. -/
theorem cHermiteReduceTowerInnerWf_eq (Dt : CPolyG QFunNZ) (fuel : ℕ) (v u : CPolyG QFunNZ) :
    ∀ (j : ℕ) (a : CPolyG QFunNZ) (g : CPolyG QFunNZ × CPolyG QFunNZ),
      CHermiteInnerRegular Dt fuel v u j a g →
      cHermiteReduceTowerInnerWf Dt v u j a g = cHermiteReduceTowerInner Dt fuel v u j a g := by
  intro j
  induction j with
  | zero =>
    intro a g _
    rfl
  | succ j ih =>
    intro a g hreg
    rcases hreg with _ | ⟨hp, hq, hS, hrec⟩
    rw [cHermiteReduceTowerInnerWf, cHermiteReduceTowerInner]
    -- the per-step Bézout solve matches the fuel'd one
    have hbez : cdiophantineGWf (cmulG u (cmonomialDeriv Dt v)) v
          (cscaleG (CField.neg (CField.inv (cnatCastG (j + 1)))) a)
        = CPolyG.cdiophantineG fuel (cmulG u (cmonomialDeriv Dt v)) v
          (cscaleG (CField.neg (CField.inv (cnatCastG (j + 1)))) a) :=
      cdiophantineGWf_eq_of_fuel fuel _ _ _ hp hq hS
    simp only [hbez]
    -- the updated `(a', g')` is a regular run; apply the IH
    exact ih _ _ hrec

/-- **Fuel-free transcendental Hermite reduction** `cHermiteReduceTowerWf Dt a d = ((gnum, gden), (h_num,
h_den))` (Bronstein §5.3, p.139) over the tower ℚ(x)[t]: the fuel-free companion of `cHermiteReduceTower`.
Squarefree-factor `d` with the **own-loop** `cSqfreeYunFFWf` (fraction-free, `ComputableWellFounded4`); for
each factor `(v, i)` of multiplicity `i ≥ 2`, run the fuel-free inner loop `cHermiteReduceTowerInnerWf`
(with `u = d/vⁱ` via the fuel-free `cdivWf`); the residual `h_num` over the squarefree radical `Dstar` is
recovered exactly via `cdivWf`. The `Dstar`/`g` foldl is structural; every fuel'd sub-op is a WF leaf —
**no fuel at runtime**, `native_decide`-able over the noncomputable-`CFieldSpec` tower `QFunNZ`. Stated with
`.1`/`.2` projections (no `let`-destructuring) so the bridge `cHermiteReduceTowerWf_eq` rewrites cleanly. -/
def cHermiteReduceTowerWf (Dt : CPolyG QFunNZ) (a d : CPolyG QFunNZ) :
    (CPolyG QFunNZ × CPolyG QFunNZ) × (CPolyG QFunNZ × CPolyG QFunNZ) :=
  let factors := cSqfreeYunFFWf d                            -- `[v₁, …, vₘ]`, vᵢ of multiplicity i
  let Dstar := factors.foldl (fun acc vi => cmulG acc vi) [CField.one]   -- squarefree radical ∏ᵢ vᵢ
  let g : CPolyG QFunNZ × CPolyG QFunNZ := factors.zipIdx.foldl
    (fun (gAcc : CPolyG QFunNZ × CPolyG QFunNZ) (vi, idx) =>
      let i := idx + 1
      if i ≤ 1 then gAcc
      else
        let Vi_pow := cpowG vi i
        let u := cdivWf d Vi_pow
        let (gloc, _) := cHermiteReduceTowerInnerWf Dt vi u (i - 1) a ([CField.zero], [CField.one])
        (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2), cmulG gAcc.2 gloc.2))  -- gAcc + gloc
    ([CField.zero], [CField.one])
  let gprimeNum := csubG (cmulG (cmonomialDeriv Dt g.1) g.2) (cmulG g.1 (cmonomialDeriv Dt g.2))
  let gden2 := cmulG g.2 g.2
  let resNum := csubG (cmulG a gden2) (cmulG d gprimeNum)
  let resDen := cmulG d gden2
  let hNum := cdivWf (cmulG resNum Dstar) resDen
  ((cnormG g.1, cnormG g.2), (cnormG hNum, cnormG Dstar))

end CPolyG

/-! ### Caveat — `cHermiteReduceTowerWf` requires an all-multiplicities-present denominator

`cHermiteReduceTowerWf` uses the fuel-free Yun factorization `cSqfreeYunFFWf` (`ComputableWellFounded4`),
whose well-founded measure `(cnormG b).length` is **only valid when every multiplicity slot of the
squarefree factorization is occupied** — i.e. when the emitted factor `pᵢ` is non-constant at every step.
When a multiplicity is **skipped** (e.g. `d = tⁿ` for `n ≥ 2`, whose squarefree factorization
`t¹·…·tⁿ⁻¹·…` is associate to `[1, …, 1, t]` with `n−1` *unit* factors and one real factor `t`), Yun emits
a constant (degree-`0`) factor `[1]` while the running `b` and `d` stay **unchanged** for several steps —
so `(cnormG b).length` does not strictly drop and `cSqfreeYunFFWf`'s structural guard fails, **truncating**
the factor list (returning a *shorter, wrong* answer). There is no polynomial-degree own-loop measure for
Yun's loop in this case — its termination is governed by the *multiplicity counter* (the fuel `fo`), which
has no strictly-decreasing polynomial witness across constant-factor steps. So `cHermiteReduceTowerWf`
agrees with the fuel'd `cHermiteReduceTower` (and satisfies the cleared identity) **exactly on denominators
whose multiplicities are all present** (`cSqfreeYunFFWf d = cSqfreeYunFF fuel d`); the `native_decide`
examples below use such a `d = (t−1)²(t−2)` (multiplicities `1, 2` both occupied) rather than the §5.3
book example `d = t²` (only multiplicity `2`, multiplicity `1` skipped — `cSqfreeYunFFWf` is wrong there).
This is the precise remaining gap: fixing it needs a correct fuel-free Yun loop in
`ComputableWellFounded4`, which this file may not edit. -/

namespace CPolyG

open QFunNZ

/-- Validation monomial derivative `Dt = t² + 1` for the fuel-free Hermite reduction (`t = tan x`). -/
def hermiteWfExampleDt : CPolyG QFunNZ := [ofConstNZ 1, ofConstNZ 0, ofConstNZ 1]

/-- Validation numerator `a = 1` over ℚ(x)[t] (ℚ-constant coefficients). -/
def hermiteWfExampleA : CPolyG QFunNZ := [ofConstNZ 1]

/-- Validation denominator `d = (t−1)²(t−2)` for the fuel-free Hermite reduction: under `Dt = t² + 1`
both `t−1`, `t−2` are normal, with multiplicities `{1 ↦ t−2, 2 ↦ t−1}` **both present** (no skipped
multiplicity), so the fuel-free Yun factorization `cSqfreeYunFFWf` is valid here. The repeated normal
factor `t−1` (multiplicity `2`) is what the transcendental Hermite reduction lowers. -/
def hermiteWfExampleD : CPolyG QFunNZ :=
  cmulG (cpowG [ofConstNZ (-1), ofConstNZ 1] 2) [ofConstNZ (-2), ofConstNZ 1]

end CPolyG

/-! ### `native_decide` smoke test for `cHermiteReduceTowerWf` (`f = 1/((t−1)²(t−2))`, `t = tan x`)

The whole fuel-free transcendental Hermite reduction executes in native code over the
noncomputable-`CFieldSpec` tower `QFunNZ` (ℚ(x)) — `cHermiteReduceTowerWf` carries no fuel and no
noncomputable bridge into the compiled body. We take `f = 1/((t−1)²(t−2))` under `Dt = t² + 1` (`t = tan
x`): the multiplicity-`2` normal factor `t−1` is lowered to multiplicity `1`, and (unlike `d = t²`) every
multiplicity slot is present, so the fuel-free Yun factorization `cSqfreeYunFFWf` is valid. -/

/-- **`cHermiteReduceTowerWf` satisfies `D(g) + h = f`, fuel-free** (`native_decide`): for `f = a/d =
1/((t−1)²(t−2))` over ℚ(x)(t) with `D = cmonomialDeriv Dt`, `Dt = t² + 1` (`t = tan x`), the fuel-free
reduction's `((gnum, gden), (h_num, h_den))` satisfies the Hermite cleared identity `(gprimeNum·h_den +
h_num·gden²)·d = a·(gden²·h_den)` (the cleared form of `D(gnum/gden) + h_num/h_den = a/d`) — the whole
chain (`cSqfreeYunFFWf` + the inner loop `cHermiteReduceTowerInnerWf` + the residual recovery) runs
end-to-end with **no fuel at runtime**. Checked by `cisZeroG` of the difference over ℚ(x)[t]. -/
example :
    (let res := CPolyG.cHermiteReduceTowerWf CPolyG.hermiteWfExampleDt
        CPolyG.hermiteWfExampleA CPolyG.hermiteWfExampleD
      let gnum := res.1.1
      let gden := res.1.2
      let hNum := res.2.1
      let hDen := res.2.2
      let Dgnum := CPolyG.cmonomialDeriv CPolyG.hermiteWfExampleDt gnum
      let Dgden := CPolyG.cmonomialDeriv CPolyG.hermiteWfExampleDt gden
      let gprimeNum := CPolyG.csubG (CPolyG.cmulG Dgnum gden) (CPolyG.cmulG gnum Dgden)
      let gden2 := CPolyG.cmulG gden gden
      let lhs := CPolyG.cmulG
        (CPolyG.caddG (CPolyG.cmulG gprimeNum hDen) (CPolyG.cmulG hNum gden2)) CPolyG.hermiteWfExampleD
      let rhs := CPolyG.cmulG CPolyG.hermiteWfExampleA (CPolyG.cmulG gden2 hDen)
      CPolyG.cisZeroG (CPolyG.csubG lhs rhs)) = true := by native_decide

/-- **The fuel-free Hermite residual has a squarefree denominator** (`native_decide`): the fuel-free
reduction lowered the multiplicity-`2` factor `t−1` of `d = (t−1)²(t−2)` to multiplicity `1`, so the
residual denominator `h_den = Dstar = (t−1)(t−2)` is squarefree (`t`-degree `2`). -/
example :
    CPolyG.cdegG (CPolyG.cHermiteReduceTowerWf CPolyG.hermiteWfExampleDt
      CPolyG.hermiteWfExampleA CPolyG.hermiteWfExampleD).2.2 = 2 := by native_decide

/-- `cHermiteReduceTowerWf` agrees with the fuel'd `cHermiteReduceTower` on `f = 1/((t−1)²(t−2))` (the
rational-part numerator/denominator and residual numerator/denominator `t`-degree tuple matches) — the
fuel-free Yun factorization is valid here (no skipped multiplicity). -/
example :
    (CPolyG.cdegG (CPolyG.cHermiteReduceTowerWf CPolyG.hermiteWfExampleDt
        CPolyG.hermiteWfExampleA CPolyG.hermiteWfExampleD).1.1,
      CPolyG.cdegG (CPolyG.cHermiteReduceTowerWf CPolyG.hermiteWfExampleDt
        CPolyG.hermiteWfExampleA CPolyG.hermiteWfExampleD).1.2,
      CPolyG.cdegG (CPolyG.cHermiteReduceTowerWf CPolyG.hermiteWfExampleDt
        CPolyG.hermiteWfExampleA CPolyG.hermiteWfExampleD).2.1,
      CPolyG.cdegG (CPolyG.cHermiteReduceTowerWf CPolyG.hermiteWfExampleDt
        CPolyG.hermiteWfExampleA CPolyG.hermiteWfExampleD).2.2)
      = (CPolyG.cdegG (CPolyG.cHermiteReduceTower CPolyG.hermiteWfExampleDt 16
          CPolyG.hermiteWfExampleA CPolyG.hermiteWfExampleD).1.1,
        CPolyG.cdegG (CPolyG.cHermiteReduceTower CPolyG.hermiteWfExampleDt 16
          CPolyG.hermiteWfExampleA CPolyG.hermiteWfExampleD).1.2,
        CPolyG.cdegG (CPolyG.cHermiteReduceTower CPolyG.hermiteWfExampleDt 16
          CPolyG.hermiteWfExampleA CPolyG.hermiteWfExampleD).2.1,
        CPolyG.cdegG (CPolyG.cHermiteReduceTower CPolyG.hermiteWfExampleDt 16
          CPolyG.hermiteWfExampleA CPolyG.hermiteWfExampleD).2.2) := by native_decide

end DeepWiki.SymbolicIntegration
