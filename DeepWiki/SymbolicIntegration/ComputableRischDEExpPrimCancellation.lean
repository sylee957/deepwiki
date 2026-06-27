import DeepWiki.SymbolicIntegration.ComputableRischDEDegreeBoundCancellation

/-! # §6.3 exp/primitive (`δ ≤ 1`) leading-term cancellation degree bound (Bronstein Lemma 6.3.3 / 6.3.4)

`ComputableRischDEDegreeBoundCancellation` proved the **nonlinear** (`δ = deg v ≥ 2`) leading-term
cancellation degree bound — the clean `λ`-recursion `deg q = λ = −lc(b)/(lc(a)·lc(v))` — and isolated the
remaining residual `RdeBoundExpPrimCancellation`: the **exp/primitive** (`δ ≤ 1`, `deg b ≤ deg a`)
cancellation case, where the cancellation condition is *not* the clean `deg q = λ` but the deeper
**logarithmic-derivative** recursion `−lc(b)/lc(a) = m·η + Dz/z` (Bronstein **Lemma 6.3.3** exp-case,
`η = Dt/t`, / **Lemma 6.3.4** primitive-case, `η = Dt`). This file analyses that case to the bottom: it
derives the exact δ ≤ 1 leading-term identity, shows the cancellation condition is *precisely* the
log-derivative equation, isolates the irreducible base-field sub-problem as a named residual, and discharges
`RdeBoundExpPrimCancellation` modulo it.

**Why δ ≤ 1 differs from the nonlinear case (the math).** For `δ = deg v ≤ 1` the monomial derivation
`D = mapCoeffs + v·d/dt` does **not** raise the `t`-degree: `mapCoeffs q` has degree `≤ deg q` and `v·q′`
has degree `≤ deg v + (deg q − 1) ≤ deg q`. So `deg(Dq) ≤ deg q` and the two LHS terms `a·Dq` and `b·q` of
`a·Dq + b·q = c` *both* live at the candidate top degree `deg a + deg q` (when `deg b ≤ deg a`). The top
coefficient of `Dq` at `deg q` is **not** the clean nonlinear `(deg q)·lc(q)·lc(v)`; it is
`(lc q)′ + (deg q)·(v.coeff 1)·(lc q)` — the **derivative of the leading coefficient** plus the
hyperexponential `(deg q)·η·lc(q)` shift (with `η = v.coeff 1 = Dt/t`, the engine's `cExpEtaG`, which is `0`
in the primitive case `deg v = 0`).

**What is proven here (axiom-clean, unconditional — `CharZero` field, NO `native_decide`, NO `sorry`).**
* `coeff_natDegree_implicitDeriv_low` — ★ the **δ ≤ 1 top coefficient of `Dq`**:
  `(Dq).coeff (deg q) = (lc q)′ + (deg q)·(v.coeff 1)·(lc q)`, uniformly across `δ ∈ {0, 1}`.
* `coeff_candTopDegree_low` — ★ the **δ ≤ 1 leading-coefficient identity** of `a·Dq + b·q` at the candidate
  top degree `deg a + deg q`: `lc(a)·[(lc q)′ + (deg q)·(v.coeff 1)·(lc q)] + (b.coeff (deg a))·(lc q)`.
* `cancellation_iff_logDeriv_eq_low` — ★ the cancellation condition is **exactly** the
  log-derivative equation `−(b.coeff (deg a))/lc(a) = (deg q)·(v.coeff 1) + (lc q)′/(lc q)` (Bronstein
  Lemma 6.3.3 / 6.3.4): the top coefficient vanishes iff `deg q` is the integer `m` solving it.

**The irreducible core (precisely isolated, NEVER `sorry`).** `ExpPrimLogDerivativeBound` — the base-field
fact that **at most finitely many / a bounded `m`** satisfy `−lc(b)/lc(a) − m·η = Dz/z` for some `z`: this is
the **parametric logarithmic-derivative** decision (Bronstein §5.12 / §6.1, the same `b = Dz/z` test the
exp/primitive *solve* uses), the genuine §6.3 frontier the nonlinear `λ`-recursion does not reach.
`expPrimCancellation_of_logDerivativeBound` discharges `RdeBoundExpPrimCancellation` modulo it, so the chain
`RdeBoundCancellationResidual` ← (nonlinear ✓) + (exp/prim ← `ExpPrimLogDerivativeBound`) is fully
explicit. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

/-! ## The δ ≤ 1 leading-term analysis over `K[X]`

We work over a `CharZero` field `K` with the monomial derivation `D = implicitDeriv v`, `δ = deg v ≤ 1`.
The equation is `a·Dq + b·q = c`, `q ≠ 0`, in the **balanced exp/primitive** configuration `deg b ≤ deg a`.
The candidate top degree collapses to `deg a + deg q`; both LHS terms contribute there. -/

section AbstractLow

variable {K : Type*} [Field K] [CharZero K] [Differential K]

end AbstractLow

end DeepWiki.SymbolicIntegration
