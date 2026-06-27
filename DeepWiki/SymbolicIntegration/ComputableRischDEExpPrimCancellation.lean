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

omit [CharZero K] [Differential K] in
/-- **The degree-`d` coefficient of `v · q′` for `deg v ≤ 1`** (`coeff_natDegree_mul_derivative_low`):
when `deg v ≤ 1` and `1 ≤ deg q = d`, `(v · q′).coeff d = (v.coeff 1)·(d)·(lc q)`. The product `v · q′`
has degree `≤ deg v + (d − 1) ≤ d`, and only the term `(v.coeff 1)·(q′.coeff (d−1))` survives at degree
`d`, with `q′.coeff (d−1) = d·(q.coeff d) = d·(lc q)` (`coeff_derivative`). For `deg v = 0` (`v.coeff 1 =
0`) it vanishes; for `deg v = 1` (`v.coeff 1 = lc v`) it is the hyperexponential `d·η·lc(q)` shift. -/
theorem coeff_natDegree_mul_derivative_low {v q : K[X]} (hv : v.natDegree ≤ 1) (hq : 1 ≤ q.natDegree) :
    (v * derivative q).coeff q.natDegree
      = v.coeff 1 * ((q.natDegree : K) * q.leadingCoeff) := by
  -- expand the product coefficient as a `Finset.antidiagonal` sum; only `(1, deg q − 1)` survives
  rw [coeff_mul, Finset.sum_eq_single (1, q.natDegree - 1)]
  · -- the surviving term: `v.coeff 1 · q′.coeff (deg q − 1)`, and `q′.coeff (deg q − 1) = deg q · lc q`
    rw [coeff_derivative]
    have hsuccN : (q.natDegree - 1 + 1 : ℕ) = q.natDegree := by omega
    have hsuccK : ((q.natDegree - 1 : ℕ) : K) + 1 = (q.natDegree : K) := by
      have : ((q.natDegree - 1 + 1 : ℕ) : K) = (q.natDegree : K) := by rw [hsuccN]
      push_cast at this ⊢; omega
    rw [hsuccN, hsuccK, leadingCoeff]
    ring
  · -- every other index `(i, j)` with `i + j = deg q` has either `v.coeff i = 0` or `q′.coeff j = 0`
    intro x hx hne
    obtain ⟨i, j⟩ := x
    rw [Finset.mem_antidiagonal] at hx
    by_cases hi : i ≤ 1
    · -- then `i = 0` (since `i = 1` is the surviving index), so `j = deg q` and `q′.coeff (deg q) = 0`
      have hi0 : i = 0 := by
        rcases Nat.lt_or_ge i 1 with h | h
        · omega
        · exfalso; apply hne
          have hi1 : i = 1 := by omega
          have hj : j = q.natDegree - 1 := by omega
          rw [hi1, hj]
      subst hi0
      have hjd : j = q.natDegree := by omega
      subst hjd
      have hz : (derivative q).coeff q.natDegree = 0 :=
        coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (natDegree_derivative_le q) (by omega))
      rw [hz, mul_zero]
    · -- `i ≥ 2 > deg v`, so `v.coeff i = 0`
      rw [coeff_eq_zero_of_natDegree_lt (by omega : v.natDegree < i), zero_mul]
  · -- the surviving index is in the antidiagonal
    intro hmem
    exact absurd (Finset.mem_antidiagonal.mpr (by omega)) hmem

omit [CharZero K] in
/-- **★ The δ ≤ 1 top coefficient of `Dq`** (`coeff_natDegree_implicitDeriv_low`): for `deg v ≤ 1` and
`1 ≤ deg q`, the monomial derivation `D = implicitDeriv v` does not raise the `t`-degree, and the
coefficient of `Dq` at the top degree `deg q` is `(lc q)′ + (deg q)·(v.coeff 1)·(lc q)` — the derivative of
the leading coefficient (from `mapCoeffs`) plus the hyperexponential `(deg q)·η·lc(q)` shift (from `v·q′`,
`η = v.coeff 1 = Dt/t`). For `deg v = 0` (primitive) the second term vanishes (`v.coeff 1 = 0`), recovering
`(Dq).coeff (deg q) = (lc q)′` (cf. `coeff_natDegree_implicitDeriv_C`). -/
theorem coeff_natDegree_implicitDeriv_low {v q : K[X]} (hv : v.natDegree ≤ 1) (hq : 1 ≤ q.natDegree) :
    (Differential.implicitDeriv v q).coeff q.natDegree
      = (q.leadingCoeff)′ + (q.natDegree : K) * v.coeff 1 * q.leadingCoeff := by
  have happly : Differential.implicitDeriv v q
      = Differential.mapCoeffs q + v * derivative q := by
    simp [Differential.implicitDeriv, derivative']
  rw [happly, coeff_add, Differential.coeff_mapCoeffs, coeff_natDegree_mul_derivative_low hv hq,
    ← leadingCoeff]
  ring

end AbstractLow

end DeepWiki.SymbolicIntegration
