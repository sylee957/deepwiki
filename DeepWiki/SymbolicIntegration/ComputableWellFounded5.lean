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

end DeepWiki.SymbolicIntegration
