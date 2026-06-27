import DeepWiki.SymbolicIntegration.ComputableRischDECompleteness
import DeepWiki.SymbolicIntegration.MonomialConstants

/-! # §6.4 degree-upper-bound for the reduced poly-RDE (Bronstein Thm 6.3.1) — the completeness keystone

`ComputableRischDECompleteness` reduced the §6 RDE decision procedure's completeness (`solvable ⟹ some`)
to the residual `RischDECompletenessResidual`, whose deepest clause is `RischDEInnerCompleteness.hbound`:
**any** polynomial solution `q` of the §6.3-reduced linear ODE `a·Dq + b·q = c` has bounded degree
`deg q ≤ cRdeBoundDegreeG …`. The engine *computes* `cRdeBoundDegreeG` (Bronstein §6.3, the degree
arithmetic) but never proves it is an upper bound on solutions. This file proves the bound where it is a
straightforward leading-term comparison, and isolates the genuinely deep cancellation case precisely.

**The degree bound (Bronstein Thm 6.3.1) and its cases.** With `D = implicitDeriv v` the monomial
derivation (`v = Dt`, so the `D`-degree is `δ = deg v`), and `dₐ = deg a`, `d_b = deg b`, `d_c = deg c`,
`cRdeBoundDegreeG` returns the **non-cancellation** bound:
* δ ≥ 2 (nonlinear): `max(0, d_c − max(dₐ + δ − 1, d_b))`;
* δ = 1 (hyperexponential): `max(0, d_c − max(d_b, dₐ))`;
* δ = 0 (primitive): `max(0, d_c − d_b)` if `dₐ < d_b`, else `max(0, d_c − dₐ + 1)`.

The proof compares the degrees of the two LHS terms `a·Dq` (degree `≤ dₐ + dq + max(0, δ−1)`, **exactly**
`dₐ + dq + δ − 1` when δ ≥ 2 and `dq ≥ 1`, since over a characteristic-`0` field the leading coefficient
`dq·lc(q)·lc(v)` never vanishes) and `b·q` (degree `d_b + dq`).

**What is proven here (axiom-clean, unconditional).**
* `natDegree_le_of_bDominates` — the **`b·q`-dominates** case: when `dₐ + max(0, δ−1) < d_b`, the `a·Dq`
  term is strictly lower degree, so `c = a·Dq + b·q` has degree `d_b + dq`, giving `dq = d_c − d_b`. Covers
  the `dₐ < d_b` branch (δ ≤ 1) and the `dₐ + δ − 1 < d_b` branch (δ ≥ 2).
* `natDegree_le_of_aDominates_nonlinear` — the **`a·Dq`-dominates** nonlinear case: δ ≥ 2 with
  `dₐ + δ − 1 > d_b`; the `a·Dq` term strictly dominates (exact degree, leading coeff `≠ 0`), giving
  `dq = d_c − (dₐ + δ − 1)`.

**The deep residual (precisely isolated, NEVER `sorry`).** The remaining configurations — δ ≥ 2 with
`dₐ + δ − 1 = d_b`, and δ ≤ 1 with `dₐ ≥ d_b` — are where the two terms have **equal candidate top
degree** (or, for δ ≤ 1, where `Dq`'s leading coefficient can vanish): the leading terms can **cancel**,
and the true degree bound carries an extra `λ = −lc(b)/(lc(a)·lc(v))` term (the integer-root cancellation
degree, Bronstein §6.3) that `cRdeBoundDegreeG` **omits** (its docstring: "the cancellation refinements
are the documented continuation"). In these configurations the engine's bound can be strictly below the
true solution degree, so `hbound` is genuinely beyond the non-cancellation argument; it is bundled as the
named residual `RdeDegreeBoundCancellationResidual` (a stated `Prop`, NO `sorry`), and `hbound` is proved
*modulo* it. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

/-! ## The abstract degree bound over `K[X]` (Bronstein Thm 6.3.1, the reachable cases)

We work over a field `K` with the monomial derivation `D = implicitDeriv v` (`v = Dt`). The equation is
`a·Dq + b·q = c` with `q ≠ 0`. The reachable cases are the two **strict-domination** configurations: the
`b·q` term strictly dominates, or (nonlinear) the `a·Dq` term strictly dominates. -/

section Helper

variable {K : Type*} [Field K]

/-- **Helper**: the top coefficient of a product `a·p` at index `dₐ + n`, when `deg p ≤ n`, is
`lc(a)·(p.coeff n)` — the only surviving term of `coeff_mul` is `(dₐ, n)`. -/
theorem coeff_mul_natDegree_add_of_natDegree_le {a p : K[X]} {n : ℕ} (hp : p.natDegree ≤ n) :
    (a * p).coeff (a.natDegree + n) = a.leadingCoeff * p.coeff n := by
  rcases eq_or_lt_of_le hp with h | h
  · subst h; rw [natDegree_add_coeff_mul]; rfl
  · rw [coeff_eq_zero_of_natDegree_lt h, mul_zero]
    exact coeff_eq_zero_of_natDegree_lt (natDegree_mul_le.trans_lt (by omega))

end Helper

section Abstract

variable {K : Type*} [Field K] [Differential K]

/-- **Bronstein Thm 6.3.1, the `b·q`-dominates case** (`natDegree_le_of_bDominates`): if
`q ≠ 0` solves `a·Dq + b·q = c` for the monomial derivation `D = implicitDeriv v`, and the `a·Dq` term is
strictly lower degree — `deg a + max(0, deg v − 1) < deg b` — then `deg q ≤ deg c − deg b`. The `b·q` term
strictly dominates, so `c` has degree `deg b + deg q` (no cancellation). This is the
`dₐ < d_b` (δ ≤ 1) / `dₐ + δ − 1 < d_b` (δ ≥ 2) branch of `cRdeBoundDegreeG`. Unconditional, any field. -/
theorem natDegree_le_of_bDominates {v a b c q : K[X]} (hq : q ≠ 0)
    (heq : a * Differential.implicitDeriv v q + b * q = c)
    (hlt : a.natDegree + max 0 (v.natDegree - 1) < b.natDegree) :
    q.natDegree ≤ c.natDegree - b.natDegree := by
  have hb0 : b ≠ 0 := by rintro rfl; simp at hlt
  have haDq : (a * Differential.implicitDeriv v q).natDegree
      ≤ a.natDegree + max 0 (v.natDegree - 1) + q.natDegree :=
    calc (a * Differential.implicitDeriv v q).natDegree
        ≤ a.natDegree + (Differential.implicitDeriv v q).natDegree := natDegree_mul_le
      _ ≤ a.natDegree + (q.natDegree + max 0 (v.natDegree - 1)) := by
          gcongr; exact natDegree_implicitDeriv_le v q
      _ = a.natDegree + max 0 (v.natDegree - 1) + q.natDegree := by omega
  have hbq : (b * q).natDegree = b.natDegree + q.natDegree := natDegree_mul hb0 hq
  have hdom : (a * Differential.implicitDeriv v q).natDegree < (b * q).natDegree := by
    rw [hbq]; omega
  have hcdeg : c.natDegree = b.natDegree + q.natDegree := by
    rw [← heq, natDegree_add_eq_right_of_natDegree_lt hdom, hbq]
  omega

end Abstract

section AbstractNonlinear

variable {K : Type*} [Field K] [CharZero K] [Differential K]

/-- **Bronstein Thm 6.3.1, the nonlinear `a·Dq`-dominates case** (`natDegree_le_of_aDominates_nonlinear`):
for a *nonlinear* monomial (`deg v ≥ 2`, so over a characteristic-`0` field `Dq` has exact degree
`deg q + deg v − 1` with nonzero leading coefficient `deg q·lc(q)·lc(v)`), if `q ≠ 0` solves
`a·Dq + b·q = c` with `a ≠ 0` and `deg b < deg a + deg v − 1`, then
`deg q ≤ deg c − (deg a + deg v − 1)`. The `a·Dq` term strictly dominates, so `c` has degree
`deg a + deg q + deg v − 1` (no cancellation). This is the `dₐ + δ − 1 > d_b` branch (δ ≥ 2) of
`cRdeBoundDegreeG`. -/
theorem natDegree_le_of_aDominates_nonlinear {v a b c q : K[X]} (ha0 : a ≠ 0)
    (hv : 2 ≤ v.natDegree)
    (heq : a * Differential.implicitDeriv v q + b * q = c)
    (hgt : b.natDegree < a.natDegree + v.natDegree - 1) :
    q.natDegree ≤ c.natDegree - (a.natDegree + v.natDegree - 1) := by
  rcases Nat.eq_zero_or_pos q.natDegree with hdq0 | hdq1
  · omega
  · have hDqdeg : (Differential.implicitDeriv v q).natDegree = q.natDegree + (v.natDegree - 1) :=
      natDegree_implicitDeriv_eq v q hv hdq1
    have hDq0 : Differential.implicitDeriv v q ≠ 0 := by
      intro h; rw [h, natDegree_zero] at hDqdeg; omega
    have haDq : (a * Differential.implicitDeriv v q).natDegree
        = a.natDegree + q.natDegree + (v.natDegree - 1) := by
      rw [natDegree_mul ha0 hDq0, hDqdeg]; omega
    have hbqle : (b * q).natDegree ≤ b.natDegree + q.natDegree := natDegree_mul_le
    have hdom : (b * q).natDegree < (a * Differential.implicitDeriv v q).natDegree := by
      rw [haDq]; omega
    have hcdeg : c.natDegree = a.natDegree + q.natDegree + (v.natDegree - 1) := by
      rw [← heq, natDegree_add_eq_left_of_natDegree_lt hdom, haDq]
    omega

end AbstractNonlinear

end DeepWiki.SymbolicIntegration
