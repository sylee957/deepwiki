import DeepWiki.SymbolicIntegration.ComputableRischDEDegreeBound

/-! # §6.3 leading-term-cancellation degree bound for the reduced poly-RDE (Bronstein, the `λ`-recursion)

`ComputableRischDEDegreeBound` proved the **non-cancellation** degree bound of Bronstein's
"Non-Cancellation Cases" (Thm 6.3.1 / Lemma 6.3.5 / §6.5 in the 2005 edition) and precisely isolated the
single remaining gap as `RdeBoundCancellationResidual`: the **leading-term cancellation** case where, for a
polynomial solution `q` of the §6.3-reduced linear ODE `a·Dq + b·q = c`, the two leading terms of `a·Dq` and
`b·q` have equal degree and **cancel** (so the top coefficient of `c` at the candidate maximal degree
vanishes). There the engine's bound `cRdeBoundDegreeG` can fall short, because the true bound carries an
extra `λ = −lc(b)/(lc(a)·lc(v))` integer-root term (`v = Dt`, so `lc(v) = λ(t)`, the leading coefficient of
the derivation).

**This file closes the deepest reachable part of that residual — the nonlinear `λ`-recursion.** Bronstein
**Lemma 6.3.5** (nonlinear case, `δ = deg v ≥ 2`, `deg b = deg a + δ − 1`): for `a ≠ 0`, `deg q > 0`, either
`deg(a·Dq + b·q) = deg b + deg q` (no cancellation), **or** `−lc(b)/lc(a) = (deg q)·lc(v)`, i.e.
`deg q = −lc(b)/(lc(a)·lc(v)) = λ`. So in the balanced nonlinear configuration the leading term of
`a·Dq + b·q` is `(deg(q)·lc(v) + lc(b)/lc(a))·lc(a)·lc(q)·t^(deg q + δ − 1)`, which vanishes **iff**
`deg q = λ`. Hence either `c.coeff(candTopDegree) ≠ 0` (no cancellation, the existing top-coefficient bound
applies) or `deg q = λ` — so `deg q ≤ max(rdeBoundDegreeAbstract, λ) =: rdeBoundDegreeWithLambda`.

**What is proven here (axiom-clean, unconditional — `CharZero` field, NO `native_decide`, NO `sorry`).**
* `coeff_candTopDegree_balanced_nonlinear` — ★ the **leading-coefficient identity** in the balanced
  nonlinear case: `c.coeff (candTopDegree v a b q) = (deg(q)·lc(v) + lc(b)/lc(a))·lc(a)·lc(q)` (the two top
  terms add at the shared degree `db + dq`).
* `natDegree_le_rdeBoundDegreeWithLambda_of_balanced_nonlinear` — ★ the **`λ`-cancellation bound**: a
  nonzero `q` solving `a·Dq + b·q = c` (with `a ≠ 0`, balanced nonlinear `2 ≤ δ`, `db = da + δ − 1`) has
  `deg q ≤ rdeBoundDegreeWithLambda` for **any** non-neg-integer `λ`-witness `N` (a `N : ℕ` with
  `(N:K)·lc(a)·lc(v) + lc(b) = 0`); when no such `N` exists the leading term never cancels and the bound is
  just `rdeBoundDegreeAbstract`.
* `natDegree_le_rdeBoundDegreeWithLambda` — the **uniform** statement folding in the non-cancellation cases:
  outside the balanced nonlinear configuration the non-cancellation bound already holds (`hbal`), and inside
  it the `λ`-recursion supplies the bound.

**The remaining residual (precisely isolated, NEVER `sorry`).** The **non-nonlinear cancellation**
configurations — `δ = 1` (hyperexponential) and `δ = 0` (primitive), where `deg b = deg a` resp.
`deg b = deg a − 1` — have a *different*, genuinely deeper cancellation condition `−lc(b)/lc(a) = m·η + Du/u`
(a logarithmic-derivative / `π∞` condition, Bronstein Lemma 6.3.3 / 6.3.4) rather than the clean
`deg q = λ`. Those stay in `RdeBoundCancellationResidual`; this file discharges the **nonlinear** balanced
case, the deepest single piece (the genuine `λ`-recursion of the task), and isolates the exp/primitive
cancellation as the named `RdeBoundExpPrimCancellationResidual`. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

/-! ## The `λ`-extended degree bound over `K[X]` (Bronstein Lemma 6.3.5, nonlinear `λ`-recursion)

We work over a `CharZero` field `K` with the monomial derivation `D = implicitDeriv v` (`v = Dt`, the
`D`-degree `δ = deg v`). The equation is `a·Dq + b·q = c`, `q ≠ 0`. The **balanced nonlinear**
configuration is `2 ≤ δ` and `deg b = deg a + δ − 1`: the two LHS terms share the candidate top degree
`db + dq` and their leading terms can cancel. -/

section AbstractLambda

variable {K : Type*} [Field K] [CharZero K] [Differential K]

/-- **The `λ`-extended degree bound** `rdeBoundDegreeWithLambda v a b c N = max(rdeBoundDegreeAbstract v a b
c, N)`: the non-cancellation bound, extended by a candidate cancellation degree `N` (Bronstein's `λ`, a
non-neg integer when `λ = −lc(b)/(lc(a)·lc(v)) ∈ ℤ≥0`). In the balanced nonlinear case the leading term of
`a·Dq + b·q` cancels **only** at `deg q = λ`, so `max(non-cancellation bound, λ)` bounds every solution
degree. (`N` is supplied as a witness satisfying the `λ`-equation; absent such a witness no cancellation
occurs and the plain `rdeBoundDegreeAbstract` already bounds `deg q`.) -/
def rdeBoundDegreeWithLambda (v a b c : K[X]) (N : ℕ) : ℕ :=
  max (rdeBoundDegreeAbstract v a b c) N

omit [CharZero K] [Differential K] in
/-- `rdeBoundDegreeAbstract ≤ rdeBoundDegreeWithLambda`: the `λ`-extension only enlarges the bound. -/
theorem rdeBoundDegreeAbstract_le_withLambda (v a b c : K[X]) (N : ℕ) :
    rdeBoundDegreeAbstract v a b c ≤ rdeBoundDegreeWithLambda v a b c N :=
  le_max_left _ _

/-- **★ The leading-coefficient identity in the balanced nonlinear case**
(`coeff_candTopDegree_balanced_nonlinear`): for a nonlinear monomial (`2 ≤ deg v`) with `a ≠ 0`,
`deg b = deg a + deg v − 1`, `q ≠ 0`, `deg q ≥ 1`, the coefficient of `a·Dq + b·q` at the candidate maximal
degree `candTopDegree v a b q = db + dq` is `(deg(q)·lc(a)·lc(v) + lc(b))·lc(q)` — the leading terms of
`a·Dq` (degree `da + dq + δ − 1 = db + dq`, leading coeff `lc(a)·deg(q)·lc(q)·lc(v)`) and `b·q` (degree
`db + dq`, leading coeff `lc(b)·lc(q)`) add at the shared top degree. -/
theorem coeff_candTopDegree_balanced_nonlinear {v a b q : K[X]} (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hq0 : q ≠ 0)
    (hv : 2 ≤ v.natDegree) (hdq : 1 ≤ q.natDegree) (hbal : b.natDegree = a.natDegree + v.natDegree - 1) :
    (a * Differential.implicitDeriv v q + b * q).coeff (candTopDegree v a b q)
      = ((q.natDegree : K) * a.leadingCoeff * v.leadingCoeff + b.leadingCoeff) * q.leadingCoeff := by
  -- the candidate top degree collapses to `db + dq` in the balanced configuration
  have hcand : candTopDegree v a b q = b.natDegree + q.natDegree := by
    simp only [candTopDegree]
    rw [show max 0 (v.natDegree - 1) = v.natDegree - 1 from by omega,
      show max (a.natDegree + (v.natDegree - 1)) b.natDegree = b.natDegree from by omega]
  -- the `a·Dq` term: exact degree `da + dq + δ − 1 = db + dq`, leading coeff `lc(a)·dq·lc(q)·lc(v)`
  have hDqdeg : (Differential.implicitDeriv v q).natDegree = q.natDegree + (v.natDegree - 1) :=
    natDegree_implicitDeriv_eq v q hv hdq
  have hDq0 : Differential.implicitDeriv v q ≠ 0 := by
    intro h; rw [h, natDegree_zero] at hDqdeg; omega
  have hDqlc : (Differential.implicitDeriv v q).leadingCoeff
      = (q.natDegree : K) * q.leadingCoeff * v.leadingCoeff :=
    leadingCoeff_implicitDeriv_nonlinear v q hv hdq
  have haDqdeg : (a * Differential.implicitDeriv v q).natDegree = b.natDegree + q.natDegree := by
    rw [natDegree_mul ha0 hDq0, hDqdeg]; omega
  have haDqcoeff : (a * Differential.implicitDeriv v q).coeff (b.natDegree + q.natDegree)
      = (q.natDegree : K) * a.leadingCoeff * v.leadingCoeff * q.leadingCoeff := by
    rw [← haDqdeg, coeff_natDegree, leadingCoeff_mul, hDqlc]; ring
  -- the `b·q` term: exact degree `db + dq`, leading coeff `lc(b)·lc(q)`
  have hbqdeg : (b * q).natDegree = b.natDegree + q.natDegree := natDegree_mul hb0 hq0
  have hbqcoeff : (b * q).coeff (b.natDegree + q.natDegree) = b.leadingCoeff * q.leadingCoeff := by
    rw [← hbqdeg, coeff_natDegree, leadingCoeff_mul]
  -- add the two coefficients at the shared top degree
  rw [hcand, coeff_add, haDqcoeff, hbqcoeff]; ring

/-- **★ Bronstein Lemma 6.3.5 over `K[X]`, the `λ`-recursion (nonlinear cancellation bound)**
(`natDegree_le_rdeBoundDegreeWithLambda_of_balanced_nonlinear`): for a nonlinear monomial (`2 ≤ deg v`) in
the balanced configuration `deg b = deg a + deg v − 1`, a nonzero `q` solving `a·Dq + b·q = c` (with
`a ≠ 0`) has `deg q ≤ rdeBoundDegreeWithLambda v a b c N` whenever `N` is a **non-negative-integer
`λ`-witness** — `(N:K)·lc(a)·lc(v) + lc(b) = 0` (i.e. `N = −lc(b)/(lc(a)·lc(v)) = λ`). Either the top
coefficient of `c` does not cancel (so `deg q ≤ rdeBoundDegreeAbstract` by the top-coefficient bound), or it
cancels — but then the leading-coefficient identity forces `(deg(q):K)·lc(a)·lc(v) + lc(b) = 0`, whose
**unique** non-neg-integer solution is `N` (as `lc(a)·lc(v) ≠ 0` in a field), giving `deg q = N`. Either way
`deg q ≤ max(rdeBoundDegreeAbstract, N)`. -/
theorem natDegree_le_rdeBoundDegreeWithLambda_of_balanced_nonlinear {v a b c q : K[X]} (hq : q ≠ 0)
    (ha0 : a ≠ 0) (hv : 2 ≤ v.natDegree) (hbal : b.natDegree = a.natDegree + v.natDegree - 1)
    (heq : a * Differential.implicitDeriv v q + b * q = c) {N : ℕ}
    (hlam : (N : K) * a.leadingCoeff * v.leadingCoeff + b.leadingCoeff = 0) :
    q.natDegree ≤ rdeBoundDegreeWithLambda v a b c N := by
  have hb0 : b ≠ 0 := by
    rintro rfl; simp only [natDegree_zero] at hbal
    have : 1 ≤ a.natDegree := by
      rcases Nat.eq_zero_or_pos a.natDegree with h | h
      · omega
      · exact h
    omega
  by_cases htop : c.coeff (candTopDegree v a b q) = 0
  · -- cancellation: extract the `λ`-equation; the nonzero `lc(a)·lc(v)` pins `deg q = N`
    refine le_trans ?_ (le_max_right (rdeBoundDegreeAbstract v a b c) N)
    rcases Nat.eq_zero_or_pos q.natDegree with hdq0 | hdq1
    · omega
    · -- the leading-coefficient identity at the (cancelled) top degree
      have hcoeff := coeff_candTopDegree_balanced_nonlinear ha0 hb0 hq hv hdq1 hbal
      rw [heq, htop] at hcoeff
      -- `(deg q · lc a · lc v + lc b) · lc q = 0`, and `lc q ≠ 0`, so the factor vanishes
      have hlcq : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hq
      have hfac : (q.natDegree : K) * a.leadingCoeff * v.leadingCoeff + b.leadingCoeff = 0 := by
        rcases mul_eq_zero.mp hcoeff.symm with h | h
        · exact h
        · exact absurd h hlcq
      -- subtract the `λ`-equation: `(deg q − N)·lc a·lc v = 0`, and `lc a·lc v ≠ 0`
      have hlca : a.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr ha0
      have hlcv : v.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr (by rintro rfl; simp at hv)
      have hdiff : ((q.natDegree : K) - (N : K)) * (a.leadingCoeff * v.leadingCoeff) = 0 := by
        -- both `↑deg q · lc a · lc v` and `↑N · lc a · lc v` equal `−lc b`
        have heqlc : (q.natDegree : K) * a.leadingCoeff * v.leadingCoeff
            = (N : K) * a.leadingCoeff * v.leadingCoeff := by
          have h1 : (q.natDegree : K) * a.leadingCoeff * v.leadingCoeff = -b.leadingCoeff := by
            linear_combination hfac
          have h2 : (N : K) * a.leadingCoeff * v.leadingCoeff = -b.leadingCoeff := by
            linear_combination hlam
          rw [h1, h2]
        linear_combination heqlc
      have hcast : (q.natDegree : K) = (N : K) := by
        rcases mul_eq_zero.mp hdiff with h | h
        · exact sub_eq_zero.mp h
        · exact absurd h (mul_ne_zero hlca hlcv)
      have hnat : q.natDegree = N := Nat.cast_injective hcast
      exact hnat.le
  · -- no cancellation: the sharp top-coefficient bound applies directly
    exact le_trans (natDegree_le_rdeBoundDegreeAbstract_of_topCoeff_ne_zero heq htop)
      (le_max_left _ _)

/-! ### The exp/primitive cancellation residual (`δ ≤ 1`), and the uniform `RdeIsBalanced` discharge

`RdeIsBalanced` (the locked file's cancellation-prone configuration) splits into exactly two sub-cases: the
**nonlinear** balanced one (`2 ≤ δ`, forcing `deg b = deg a + δ − 1`), discharged above by the `λ`-recursion;
and the **exp/primitive** balanced one (`δ ≤ 1`, `deg b ≤ deg a`), whose cancellation condition is the
deeper `−lc(b)/lc(a) = m·η + Dz/z` (Bronstein Lemma 6.3.3 / 6.3.4, a logarithmic-derivative recursion into
the base field) rather than the clean `deg q = λ`. The latter is the precisely-isolated remaining residual. -/

omit [CharZero K] [Differential K] in
/-- **`RdeIsBalanced` splits into nonlinear vs exp/primitive** (`rdeIsBalanced_nonlinear_or_low`): a
balanced configuration is either nonlinear with `deg b = deg a + δ − 1` (`2 ≤ deg v`), or has `δ ≤ 1` with
`deg b ≤ deg a` (the exp/primitive case). This is the case split underlying the two cancellation mechanisms:
the nonlinear one is the clean `λ`-recursion, the `δ ≤ 1` one is the deeper logarithmic-derivative recursion. -/
theorem rdeIsBalanced_nonlinear_or_low {v a b c : K[X]} (hbal : RdeIsBalanced v a b c) :
    (2 ≤ v.natDegree ∧ b.natDegree = a.natDegree + v.natDegree - 1)
      ∨ (v.natDegree ≤ 1 ∧ b.natDegree ≤ a.natDegree) := by
  obtain ⟨hnb, hna⟩ := hbal
  rcases le_or_gt 2 v.natDegree with hδ | hδ
  · refine Or.inl ⟨hδ, ?_⟩
    -- `¬(da + (δ−1) < db)` gives `db ≤ da+δ−1`; `¬(2≤δ ∧ db < da+δ−1)` with `2≤δ` gives `da+δ−1 ≤ db`
    have h1 : ¬ (a.natDegree + (v.natDegree - 1) < b.natDegree) := by
      rw [show max 0 (v.natDegree - 1) = v.natDegree - 1 from by omega] at hnb; exact hnb
    have h2 : ¬ (b.natDegree < a.natDegree + v.natDegree - 1) := fun h => hna ⟨hδ, h⟩
    omega
  · refine Or.inr ⟨by omega, ?_⟩
    rw [show max 0 (v.natDegree - 1) = 0 from by omega] at hnb; omega

/-- **★ The exp/primitive (`δ ≤ 1`) leading-term cancellation residual** `RdeBoundExpPrimCancellation v a b
c N`: in the balanced exp/primitive configuration (`deg v ≤ 1`, `deg b ≤ deg a`), a nonzero `q` solving
`a·Dq + b·q = c` has `deg q ≤ rdeBoundDegreeWithLambda v a b c N`. Unlike the nonlinear case, here the
cancellation condition is `−lc(b)/lc(a) = m·η + Dz/z` (Bronstein Lemma 6.3.3 / 6.3.4) — a
logarithmic-derivative recursion into the base field, **not** the clean `deg q = λ`; `N` is the
non-neg-integer `m` it produces (when it exists). A stated `Prop`, NO `sorry`; the precise, minimal deep
content of the cancellation bound that the nonlinear `λ`-recursion does not reach (it depends on a base-field
"is this `m·η + a logarithmic derivative" oracle, the genuine §6.3 frontier). -/
def RdeBoundExpPrimCancellation (v a b c : K[X]) (N : ℕ) : Prop :=
  ∀ q : K[X], q ≠ 0 → a ≠ 0 → v.natDegree ≤ 1 → b.natDegree ≤ a.natDegree →
    a * Differential.implicitDeriv v q + b * q = c →
    q.natDegree ≤ rdeBoundDegreeWithLambda v a b c N

/-- **★ The full `λ`-cancellation bound over `K[X]`, modulo the exp/primitive residual**
(`natDegree_le_rdeBoundDegreeWithLambda`): a nonzero `q` solving `a·Dq + b·q = c` (with `a ≠ 0`) has
`deg q ≤ rdeBoundDegreeWithLambda v a b c N` for a non-neg-integer `λ`-witness `N`
(`(N:K)·lc(a)·lc(v) + lc(b) = 0`), **provided** the exp/primitive cancellation residual `hexp` covers the
`δ ≤ 1` balanced configuration. The two strict-domination cases (`natDegree_le_rdeBoundDegreeAbstract_of_*`,
through `rdeBoundDegreeAbstract ≤ rdeBoundDegreeWithLambda`) and the **nonlinear** balanced case (the proven
`λ`-recursion) are discharged unconditionally; only the exp/primitive balanced case needs `hexp`. -/
theorem natDegree_le_rdeBoundDegreeWithLambda {v a b c q : K[X]} (hq : q ≠ 0) (ha0 : a ≠ 0)
    (heq : a * Differential.implicitDeriv v q + b * q = c) {N : ℕ}
    (hlam : (N : K) * a.leadingCoeff * v.leadingCoeff + b.leadingCoeff = 0)
    (hexp : RdeBoundExpPrimCancellation v a b c N) :
    q.natDegree ≤ rdeBoundDegreeWithLambda v a b c N := by
  -- non-balanced configs are unconditional (strict-domination → `rdeBoundDegreeAbstract`);
  -- balanced splits into the proven nonlinear `λ`-recursion and the exp/primitive residual
  by_cases hbal : RdeIsBalanced v a b c
  · rcases rdeIsBalanced_nonlinear_or_low hbal with ⟨hv, hbeq⟩ | ⟨hv, hble⟩
    · -- nonlinear balanced: the proven `λ`-recursion (already lands in `rdeBoundDegreeWithLambda`)
      exact natDegree_le_rdeBoundDegreeWithLambda_of_balanced_nonlinear hq ha0 hv hbeq heq hlam
    · -- exp/primitive balanced: the isolated residual (also lands in `rdeBoundDegreeWithLambda`)
      exact hexp q hq ha0 hv hble heq
  · -- not balanced: the locked-file strict-domination discharge gives `≤ rdeBoundDegreeAbstract`
    refine (natDegree_le_rdeBoundDegreeAbstract_of_balanced hq ha0 heq ?_).trans (le_max_left _ _)
    exact fun h => absurd h hbal

end AbstractLambda

end DeepWiki.SymbolicIntegration
