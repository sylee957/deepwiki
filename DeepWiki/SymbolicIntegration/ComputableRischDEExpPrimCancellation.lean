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

omit [CharZero K] [Differential K] in
/-- **`coeff (a · p) (deg a + i) = lc(a)·(p.coeff i)` when `deg p ≤ i`**
(`coeff_mul_natDegree_add_of_natDegree_le`): in the product `a · p`, the coefficient at `deg a + i`
(`i ≥ deg p`) collapses to the single antidiagonal term `(deg a, i)` — every `(j, k)` with `j + k = deg a +
i` and `j ≠ deg a` has either `j > deg a` (`a.coeff j = 0`) or `k > i ≥ deg p` (`p.coeff k = 0`). -/
theorem coeff_mul_natDegree_add_of_natDegree_le {a p : K[X]} {i : ℕ} (hp : p.natDegree ≤ i) :
    (a * p).coeff (a.natDegree + i) = a.leadingCoeff * p.coeff i := by
  rw [coeff_mul, Finset.sum_eq_single (a.natDegree, i)]
  · rw [leadingCoeff]
  · -- non-diagonal indices vanish
    intro x hx hne
    obtain ⟨j, k⟩ := x
    rw [Finset.mem_antidiagonal] at hx
    by_cases hj : j ≤ a.natDegree
    · -- then `k ≥ i`; if `k > i` then `p.coeff k = 0`, else `(j,k) = (deg a, i)` (excluded)
      rcases Nat.lt_or_ge i k with hk | hk
      · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp hk), mul_zero]
      · exfalso; apply hne
        have hjeq : j = a.natDegree := by omega
        have hkeq : k = i := by omega
        rw [hjeq, hkeq]
    · -- `j > deg a`, so `a.coeff j = 0`
      rw [coeff_eq_zero_of_natDegree_lt (by omega : a.natDegree < j), zero_mul]
  · intro hmem
    exact absurd (Finset.mem_antidiagonal.mpr (rfl : a.natDegree + i = a.natDegree + i)) hmem

omit [CharZero K] in
/-- **★ The δ ≤ 1 leading-coefficient identity** (`coeff_candTopDegree_low`): in the balanced
exp/primitive configuration (`deg v ≤ 1`, `deg b ≤ deg a`, `1 ≤ deg q`), the coefficient of `a·Dq + b·q`
at the candidate top degree `candTopDegree v a b q = deg a + deg q` is
`lc(a)·[(lc q)′ + (deg q)·(v.coeff 1)·(lc q)] + (b.coeff (deg a))·(lc q)` — the `a·Dq` term (degree `≤ deg a
+ deg q`, top coeff `lc(a)·(Dq).coeff (deg q)`) plus the `b·q` term (`b.coeff (deg a)·lc(q)`, which is
`lc(b)·lc(q)` when `deg b = deg a` and `0` when `deg b < deg a`). -/
theorem coeff_candTopDegree_low {v a b q : K[X]} (hv : v.natDegree ≤ 1)
    (hdq : 1 ≤ q.natDegree) (hble : b.natDegree ≤ a.natDegree) :
    (a * Differential.implicitDeriv v q + b * q).coeff (candTopDegree v a b q)
      = a.leadingCoeff * ((q.leadingCoeff)′ + (q.natDegree : K) * v.coeff 1 * q.leadingCoeff)
        + b.coeff a.natDegree * q.leadingCoeff := by
  -- the candidate top degree collapses to `da + dq` in the balanced exp/prim configuration
  have hcand : candTopDegree v a b q = a.natDegree + q.natDegree := by
    simp only [candTopDegree]
    rw [show max 0 (v.natDegree - 1) = 0 from by omega, add_zero,
      show max a.natDegree b.natDegree = a.natDegree from by omega]
  -- the `a·Dq` term: `Dq` has degree ≤ deg q, so `coeff (a·Dq) (da+dq) = lc(a)·(Dq).coeff dq`
  have hDqle : (Differential.implicitDeriv v q).natDegree ≤ q.natDegree := by
    refine (natDegree_implicitDeriv_le v q).trans ?_
    rw [show max 0 (v.natDegree - 1) = 0 from by omega, add_zero]
  have haDq : (a * Differential.implicitDeriv v q).coeff (a.natDegree + q.natDegree)
      = a.leadingCoeff * (Differential.implicitDeriv v q).coeff q.natDegree :=
    coeff_mul_natDegree_add_of_natDegree_le hDqle
  -- the `b·q` term: `coeff (b·q) (da+dq) = lc(q)·(b.coeff da)` (b has degree ≤ da)
  have hbq : (b * q).coeff (a.natDegree + q.natDegree) = b.coeff a.natDegree * q.leadingCoeff := by
    rw [mul_comm b q, add_comm a.natDegree q.natDegree,
      coeff_mul_natDegree_add_of_natDegree_le hble, leadingCoeff, mul_comm]
  rw [hcand, coeff_add, haDq, hbq, coeff_natDegree_implicitDeriv_low hv hdq]

/-! ### The cancellation condition is the logarithmic-derivative equation (Bronstein Lemma 6.3.3 / 6.3.4)

Setting the δ ≤ 1 leading coefficient to `0` and dividing by `lc(a)·lc(q)` (both nonzero) yields the
Bronstein cancellation condition `−lc(b)/lc(a) = m·η + Dz/z` with `m = deg q`, `η = v.coeff 1` (`= Dt/t` in
the hyperexponential case, `0` in the primitive case), and `z = lc(q)` (so `Dz/z = logDeriv (lc q)`). -/

omit [CharZero K] in
/-- **★ The δ ≤ 1 cancellation condition is the logarithmic-derivative equation**
(`cancellation_iff_logDeriv_eq_low`, Bronstein Lemma 6.3.3 / 6.3.4): in the balanced exp/primitive
configuration (`deg v ≤ 1`, `deg b ≤ deg a`, `a ≠ 0`, `q ≠ 0`, `1 ≤ deg q`), the leading term of
`a·Dq + b·q` at the candidate top degree **vanishes iff** `deg q` satisfies the log-derivative equation
`−(b.coeff (deg a))/lc(a) = (deg q)·(v.coeff 1) + logDeriv (lc q)` — i.e. `−lc(b)/lc(a) = m·η + Dz/z` with
`m = deg q`, `η = v.coeff 1` (`Dt/t`), `z = lc q`. This is the deep cancellation condition (a
logarithmic-derivative recursion into the base field `K`), NOT the clean nonlinear `deg q = λ`. -/
theorem cancellation_iff_logDeriv_eq_low {v a b q : K[X]} (ha0 : a ≠ 0) (hq0 : q ≠ 0)
    (hv : v.natDegree ≤ 1) (hdq : 1 ≤ q.natDegree) (hble : b.natDegree ≤ a.natDegree) :
    (a * Differential.implicitDeriv v q + b * q).coeff (candTopDegree v a b q) = 0
      ↔ -(b.coeff a.natDegree) / a.leadingCoeff
          = (q.natDegree : K) * v.coeff 1 + Differential.logDeriv q.leadingCoeff := by
  have hlca : a.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr ha0
  have hlcq : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hq0
  rw [coeff_candTopDegree_low hv hdq hble, Differential.logDeriv]
  -- the leading coefficient `E` factors as `lc(a)·lc(q)·R` where `R` is the equation's defect
  set D := (q.leadingCoeff)′ with hD
  set η := v.coeff 1 with hη
  set m := (q.natDegree : K) with hm
  set bc := b.coeff a.natDegree with hbc
  have hfac : a.leadingCoeff * (D + m * η * q.leadingCoeff) + bc * q.leadingCoeff
      = (a.leadingCoeff * q.leadingCoeff) * ((m * η + D / q.leadingCoeff) - (-bc / a.leadingCoeff)) := by
    field_simp
    ring
  rw [hfac, mul_eq_zero, sub_eq_zero]
  -- `lc(a)·lc(q) ≠ 0`, so the product is `0` iff the defect vanishes; flip to the book's orientation
  constructor
  · rintro (hz | heq)
    · exact absurd hz (mul_ne_zero hlca hlcq)
    · exact heq.symm
  · intro heq; exact Or.inr heq.symm

end AbstractLow

/-! ## ★ The irreducible core: the parametric logarithmic-derivative bound

The δ ≤ 1 cancellation forces `deg q` to satisfy `−lc(b)/lc(a) = (deg q)·η + logDeriv z` for `z = lc q ≠ 0`
(`cancellation_iff_logDeriv_eq_low`). Bounding `deg q` is therefore the base-field question: **for how many
`m ∈ ℕ` is `−lc(b)/lc(a) − m·η` a logarithmic derivative of a nonzero base-field element?** This is the
**parametric logarithmic-derivative** decision (Bronstein §5.12 / §6.1, the very `b = Dz/z` test the
exp/primitive *solve* `cPolyRischDECancel{Exp,Prim}G` uses degree-by-degree). It is the genuine §6.3
frontier — the deeper recursion the nonlinear `λ`-bound never enters — and is isolated here as a named
`Prop`, never `sorry`. -/

section LogDerivativeBound

variable {K : Type*} [Field K] [CharZero K] [Differential K]

/-- **★ The parametric logarithmic-derivative bound** `ExpPrimLogDerivativeBound v a b N`: every natural
number `m` for which `−lc(b)/lc(a) = m·(v.coeff 1) + logDeriv z` holds for **some** nonzero `z ∈ K` is `≤ N`
(`v.coeff 1 = η = Dt/t` in the hyperexponential case, `0` in the primitive case). This is the irreducible
base-field content of the δ ≤ 1 cancellation degree bound: the parametric logarithmic-derivative problem
(Bronstein §5.12 / §6.1) — exactly the `b = Dz/z` test the engine's exp/primitive cancellation *solve* runs.
A stated `Prop`, NO `sorry`; the deep §6.3 sub-problem the nonlinear `λ`-recursion does not reach. (`b`'s
relevant coefficient is `b.coeff (deg a)`, which is `lc(b)` in the genuinely balanced `deg b = deg a` case.)
-/
def ExpPrimLogDerivativeBound (v a b : K[X]) (N : ℕ) : Prop :=
  ∀ m : ℕ, (∃ z : K, z ≠ 0 ∧
      -(b.coeff a.natDegree) / a.leadingCoeff = (m : K) * v.coeff 1 + Differential.logDeriv z) →
    m ≤ N

omit [CharZero K] in
/-- **★ The exp/primitive cancellation bound, modulo the log-derivative bound**
(`expPrimCancellation_of_logDerivativeBound`): for the balanced exp/primitive configuration (`deg v ≤ 1`,
`deg b ≤ deg a`), a nonzero `q` solving `a·Dq + b·q = c` (with `a ≠ 0`) has
`deg q ≤ rdeBoundDegreeWithLambda v a b c N`, **provided** the parametric log-derivative bound
`ExpPrimLogDerivativeBound v a b N` holds. Either the top coefficient of `c` does not cancel (the existing
top-coefficient bound applies, landing in `rdeBoundDegreeAbstract ≤ rdeBoundDegreeWithLambda`), or it cancels
— but then `cancellation_iff_logDeriv_eq_low` exhibits `−lc(b)/lc(a) = (deg q)·η + logDeriv (lc q)` with
`lc q ≠ 0`, so `ExpPrimLogDerivativeBound` forces `deg q ≤ N ≤ rdeBoundDegreeWithLambda`. This proves
`RdeBoundExpPrimCancellation` modulo the precisely isolated base-field core. -/
theorem expPrimCancellation_of_logDerivativeBound {v a b c q : K[X]} (hq : q ≠ 0) (ha0 : a ≠ 0)
    (hv : v.natDegree ≤ 1) (hble : b.natDegree ≤ a.natDegree)
    (heq : a * Differential.implicitDeriv v q + b * q = c) {N : ℕ}
    (hbound : ExpPrimLogDerivativeBound v a b N) :
    q.natDegree ≤ rdeBoundDegreeWithLambda v a b c N := by
  by_cases htop : c.coeff (candTopDegree v a b q) = 0
  · -- cancellation: extract the log-derivative equation and apply the parametric bound
    refine le_trans ?_ (le_max_right (rdeBoundDegreeAbstract v a b c) N)
    rcases Nat.eq_zero_or_pos q.natDegree with hdq0 | hdq1
    · omega
    · -- the leading coefficient vanishes at the cancelled top degree
      have hcancel : (a * Differential.implicitDeriv v q + b * q).coeff (candTopDegree v a b q) = 0 := by
        rw [heq]; exact htop
      -- the cancellation iff exhibits the witness `z = lc q ≠ 0`
      have hlog := (cancellation_iff_logDeriv_eq_low ha0 hq hv hdq1 hble).mp hcancel
      exact hbound q.natDegree ⟨q.leadingCoeff, leadingCoeff_ne_zero.mpr hq, hlog⟩
  · -- no cancellation: the sharp top-coefficient bound applies directly
    exact le_trans (natDegree_le_rdeBoundDegreeAbstract_of_topCoeff_ne_zero heq htop)
      (rdeBoundDegreeAbstract_le_withLambda v a b c N)

omit [CharZero K] in
/-- **★ `RdeBoundExpPrimCancellation` is discharged by the log-derivative bound**
(`rdeBoundExpPrimCancellation_of_logDerivativeBound`): the precise exp/primitive cancellation residual
`RdeBoundExpPrimCancellation v a b c N` (from `ComputableRischDEDegreeBoundCancellation`) follows from the
parametric log-derivative bound `ExpPrimLogDerivativeBound v a b N`. So the deepest §6.3 cancellation
residual reduces to **exactly** the base-field parametric logarithmic-derivative problem — the genuine
frontier — with everything else proven. -/
theorem rdeBoundExpPrimCancellation_of_logDerivativeBound (v a b c : K[X]) {N : ℕ}
    (hbound : ExpPrimLogDerivativeBound v a b N) :
    RdeBoundExpPrimCancellation v a b c N := by
  intro q hq ha0 hv hble heq
  exact expPrimCancellation_of_logDerivativeBound hq ha0 hv hble heq hbound

/-! ### The primitive sub-case (`δ = 0`): the cancellation condition loses its `m`-dependence

For a *primitive* monomial (`deg v = 0`, `v = C w`), `η = v.coeff 1 = 0`, so the cancellation condition
collapses to `−lc(b)/lc(a) = logDeriv (lc q)` — **independent of `deg q`**. The leading-term analysis alone
therefore does **not** bound the primitive degree (Bronstein's primitive degree bound comes from the SPDE /
degree-by-degree recursion 6.6.1, not the top term): `ExpPrimLogDerivativeBound` holds for a primitive
configuration **iff** `−lc(b)/lc(a)` is *not* a logarithmic derivative (then no `m` qualifies, the bound is
vacuous for any `N`) — honestly reflecting that the bound's content is elsewhere when it *is*. -/

omit [CharZero K] [Differential K] in
/-- **The primitive (`δ = 0`) hyperexponential coefficient vanishes** (`coeff_one_eq_zero_of_natDegree_le`):
for `deg v = 0` the degree-`1` coefficient `η = v.coeff 1` is `0`, so the δ ≤ 1 cancellation condition loses
its `(deg q)·η` term. -/
theorem coeff_one_eq_zero_of_natDegree_le {v : K[X]} (hv : v.natDegree = 0) : v.coeff 1 = 0 :=
  coeff_eq_zero_of_natDegree_lt (by omega)

omit [CharZero K] in
/-- **★ The primitive cancellation condition is `deg q`-independent** (`cancellation_iff_logDeriv_eq_prim`):
for a primitive monomial (`deg v = 0`), the δ ≤ 1 leading term of `a·Dq + b·q` at the candidate top degree
vanishes **iff** `−lc(b)/lc(a) = logDeriv (lc q)` — with **no** `deg q` term. So the primitive degree bound
cannot be read off the leading term (it is the SPDE recursion 6.6.1, Bronstein §6.6); the leading-term
condition only constrains `lc q`, not `deg q`. -/
theorem cancellation_iff_logDeriv_eq_prim {v a b q : K[X]} (ha0 : a ≠ 0) (hq0 : q ≠ 0)
    (hv : v.natDegree = 0) (hdq : 1 ≤ q.natDegree) (hble : b.natDegree ≤ a.natDegree) :
    (a * Differential.implicitDeriv v q + b * q).coeff (candTopDegree v a b q) = 0
      ↔ -(b.coeff a.natDegree) / a.leadingCoeff = Differential.logDeriv q.leadingCoeff := by
  rw [cancellation_iff_logDeriv_eq_low ha0 hq0 (by omega) hdq hble,
    coeff_one_eq_zero_of_natDegree_le hv, mul_zero, zero_add]

end LogDerivativeBound

/-! ## ★ The exp/primitive bound at the `CPolyG` layer (the §6.3 frontier over the tower)

Lifting the abstract exp/primitive cancellation discharge to `CPolyG` over `(CFieldSpec.K α)[X]`: a
§6.3-reduced δ ≤ 1 solution `q` has `cdegG q ≤ max(cRdeBoundDegreeG …, N)` modulo the parametric
log-derivative bound on `(CFieldSpec.K α)`. Combined with the **nonlinear** `λ`-recursion (proven in
`ComputableRischDEDegreeBoundCancellation`), this closes the §6.3 cancellation degree bound modulo a single
base-field oracle — the parametric logarithmic-derivative decision. -/

section ComputableExpPrim

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCore α]

omit [CFracGcdCore α] in
/-- **★ `RdeBoundExpPrimCancellation` at the `CPolyG` layer** (`rdeBoundExpPrimCancellation_cpolyG`): the
exp/primitive cancellation residual over `(CFieldSpec.K α)[X]` follows from the parametric log-derivative
bound `ExpPrimLogDerivativeBound (toPolyG v) (toPolyG a) (toPolyG b) N`. This is the `CPolyG`-layer
discharge of the deepest §6.3 cancellation sub-residual, modulo the base-field parametric
logarithmic-derivative oracle. -/
theorem rdeBoundExpPrimCancellation_cpolyG (v a b c : CPolyG α) {N : ℕ}
    (hbound : ExpPrimLogDerivativeBound (toPolyG v) (toPolyG a) (toPolyG b) N) :
    RdeBoundExpPrimCancellation (toPolyG v) (toPolyG a) (toPolyG b) (toPolyG c) N :=
  rdeBoundExpPrimCancellation_of_logDerivativeBound (toPolyG v) (toPolyG a) (toPolyG b) (toPolyG c) hbound

omit [CFracGcdCore α] in
/-- **★ The full §6.3 cancellation degree bound at the `CPolyG` layer, modulo ONE base-field oracle**
(`cdegG_le_max_cRdeBoundDegreeG_expPrim`): a §6.3-reduced solution `q` of `a·Dq + b·q = c`
(`IsReducedRdeSol Dt a b c q`, `toPolyG q ≠ 0`, `toPolyG a ≠ 0`) in the δ ≤ 1 balanced configuration has
`cdegG q ≤ max(cRdeBoundDegreeG Dt fuel a b c, N)`, modulo the parametric log-derivative bound `hbound` on
`(CFieldSpec.K α)`. With the nonlinear `λ`-recursion (`cdegG_le_max_cRdeBoundDegreeG_of_isReducedRdeSol`),
this is the **whole** §6.3 cancellation degree bound reduced to a single base-field oracle. -/
theorem cdegG_le_max_cRdeBoundDegreeG_expPrim (Dt : CPolyG α) (fuel : ℕ) (a b c q : CPolyG α)
    (hqP : toPolyG q ≠ 0) (ha0 : toPolyG a ≠ 0) (hsol : IsReducedRdeSol Dt a b c q)
    (hv : (toPolyG Dt).natDegree ≤ 1) (hble : (toPolyG b).natDegree ≤ (toPolyG a).natDegree) {N : ℕ}
    (hbound : ExpPrimLogDerivativeBound (toPolyG Dt) (toPolyG a) (toPolyG b) N) :
    cdegG q ≤ max (cRdeBoundDegreeG Dt fuel a b c) N := by
  have heq : toPolyG a * Differential.implicitDeriv (toPolyG Dt) (toPolyG q)
      + toPolyG b * toPolyG q = toPolyG c := hsol
  have habs := expPrimCancellation_of_logDerivativeBound hqP ha0 hv hble heq hbound
  rw [cdegG_eq_natDegree, cRdeBoundDegreeG_eq_abstract]
  exact habs

end ComputableExpPrim

end DeepWiki.SymbolicIntegration
