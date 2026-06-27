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
* `natDegree_le_rdeBoundDegreeAbstract_of_topCoeff_ne_zero` — ★ the **sharp top-coefficient bound**: when
  the leading coefficient of `c` at the candidate maximal degree `candTopDegree = max(dₐ + max(0, δ−1), d_b)
  + dq` does **not** vanish (no leading-term cancellation), `deg q ≤ rdeBoundDegreeAbstract`, uniformly
  across **all** δ (no `CharZero`). This is the discharge the computable bound uses.
* `natDegree_le_of_bDominates` — the explicit **`b·q`-dominates** case: when `dₐ + max(0, δ−1) < d_b`, the
  `a·Dq` term is strictly lower degree, so `c = a·Dq + b·q` has degree `d_b + dq`, giving `dq = d_c − d_b`.
* `natDegree_le_of_aDominates_nonlinear` — the explicit **`a·Dq`-dominates** nonlinear case: δ ≥ 2 with
  `dₐ + δ − 1 > d_b`; the `a·Dq` term strictly dominates (exact degree, leading coeff `≠ 0`), giving
  `dq = d_c − (dₐ + δ − 1)`. (In both strict cases the dominant term provides a nonzero top coefficient, so
  they are special cases of the top-coefficient bound.)

**The deep residual (precisely isolated, NEVER `sorry`).** The single uncovered case is **leading-term
cancellation**: the top coefficient of `c` at the candidate maximal degree **vanishes**
(`c.coeff (candTopDegree …) = 0`), dropping `deg c` below it. This can fire only in the **balanced**
configurations (δ ≥ 2 with `dₐ + δ − 1 = d_b`, δ ≤ 1 with `d_b ≤ dₐ`), where the two LHS leading terms can
cancel and the true degree bound carries an extra `λ = −lc(b)/(lc(a)·lc(v))` term (the integer-root
cancellation degree, Bronstein §6.3) that `cRdeBoundDegreeG` **omits** (its docstring: "the cancellation
refinements are the documented continuation"). There the engine's bound can be strictly below the true
solution degree, so `hbound` is genuinely beyond the non-cancellation argument; it is bundled as the named
residual `RdeBoundCancellationResidual` (a stated `Prop`, NO `sorry`), and `hbound` is proved *modulo*
it. -/

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

/-! ## The abstract `cRdeBoundDegreeG` formula and `hbound` modulo the cancellation residual

`rdeBoundDegreeAbstract v a b c` is the **non-cancellation** degree bound of Bronstein §6.3, written over
`K[X]` in `natDegree`s exactly as `cRdeBoundDegreeG` computes it over `cdegG`s; the computable bridge
`cRdeBoundDegreeG_eq_abstract` identifies the two. The two strict-domination cases discharge the bound for
the dominant configurations; the **balanced** configurations (`RdeIsBalanced`) — where the two LHS terms
share a candidate top degree and the leading terms can cancel — are the deep §6.3 `λ`-cancellation gap,
isolated as the residual. -/

section AbstractBound

variable {K : Type*} [Field K] [CharZero K] [Differential K]

/-- **The abstract non-cancellation degree bound** `rdeBoundDegreeAbstract v a b c` (Bronstein §6.3),
written over `K[X]` in `natDegree`s exactly as `cRdeBoundDegreeG` computes it over `cdegG`s: with
`dₐ, d_b, d_c, δ` the degrees of `a, b, c, v`, it is `max(0, d_c − max(dₐ + δ − 1, d_b))` (δ ≥ 2),
`max(0, d_c − max(d_b, dₐ))` (δ = 1), and `max(0, d_c − d_b)`/`max(0, d_c − dₐ + 1)` (δ = 0, by
`dₐ < d_b`). -/
def rdeBoundDegreeAbstract (v a b c : K[X]) : ℕ :=
  let da : ℤ := (a.natDegree : ℤ)
  let db : ℤ := (b.natDegree : ℤ)
  let dc : ℤ := (c.natDegree : ℤ)
  let δ : ℤ := (v.natDegree : ℤ)
  let n : ℤ :=
    if 2 ≤ δ then max 0 (dc - max (da + δ - 1) db)
    else if δ = 1 then max 0 (dc - max db da)
    else if da < db then max 0 (dc - db) else max 0 (dc - da + 1)
  n.toNat

/-- **The balanced (cancellation-prone) configuration** `RdeIsBalanced v a b c`: the two strict-domination
cases of Bronstein Thm 6.3.1 both fail — neither `b·q` strictly dominates (`deg a + max(0, δ−1) < deg b`
fails) nor does `a·Dq` strictly dominate in the nonlinear case (`2 ≤ δ ∧ deg b < deg a + δ − 1` fails).
Concretely the configurations δ ≥ 2 with `deg a + δ − 1 = deg b`, and δ ≤ 1 with `deg b ≤ deg a`: here the
LHS terms share a candidate top degree, the leading terms can **cancel**, and the true degree bound carries
the `λ` term `cRdeBoundDegreeG` omits. The precise domain of the deep §6.3 residual. (`c` is carried for
signature uniformity with `rdeBoundDegreeAbstract`; the balance is a `v, a, b` degree condition.) -/
def RdeIsBalanced (v a b _c : K[X]) : Prop :=
  ¬ (a.natDegree + max 0 (v.natDegree - 1) < b.natDegree) ∧
    ¬ (2 ≤ v.natDegree ∧ b.natDegree < a.natDegree + v.natDegree - 1)

/-- **★ Bronstein Thm 6.3.1 over `K[X]`, modulo the cancellation residual**
(`natDegree_le_rdeBoundDegreeAbstract_of_balanced`): a nonzero `q` solving `a·Dq + b·q = c` (with `a ≠ 0`)
has `deg q ≤ rdeBoundDegreeAbstract v a b c`, **provided** that whenever the configuration is balanced
(`RdeIsBalanced`) the bound is already known to hold (`hbal`). The two strict-domination cases discharge
all non-balanced configurations unconditionally (`natDegree_le_of_bDominates` /
`natDegree_le_of_aDominates_nonlinear`); `hbal` supplies exactly the balanced (cancellation) configurations
the engine's bound does not cover — the precise residual. -/
theorem natDegree_le_rdeBoundDegreeAbstract_of_balanced {v a b c q : K[X]} (hq : q ≠ 0) (ha0 : a ≠ 0)
    (heq : a * Differential.implicitDeriv v q + b * q = c)
    (hbal : RdeIsBalanced v a b c → q.natDegree ≤ rdeBoundDegreeAbstract v a b c) :
    q.natDegree ≤ rdeBoundDegreeAbstract v a b c := by
  by_cases hbd : a.natDegree + max 0 (v.natDegree - 1) < b.natDegree
  · -- b·q strictly dominates: covered unconditionally
    have hle := natDegree_le_of_bDominates hq heq hbd
    -- the abstract bound in this configuration is `max(0, dc - db)`, which ≥ dc - db ≥ dq
    have hb0 : b.natDegree ≠ 0 := by omega
    refine hle.trans ?_
    -- show `c.natDegree - b.natDegree ≤ rdeBoundDegreeAbstract v a b c`
    simp only [rdeBoundDegreeAbstract]
    split
    · -- δ ≥ 2: db dominates max(da+δ-1, db) since b dominates ⟹ da+δ-1 < db
      rename_i hδ
      have : a.natDegree + (v.natDegree - 1) < b.natDegree := by
        have : max 0 (v.natDegree - 1) = v.natDegree - 1 := by omega
        omega
      have hmax : max (a.natDegree + v.natDegree - 1 : ℤ) (b.natDegree : ℤ) = (b.natDegree : ℤ) := by
        rw [max_eq_right]; omega
      rw [hmax]; omega
    · split
      · -- δ = 1: max(db, da) = db since da < db (from b dominates with δ-1=0)
        rename_i hδ1
        have hda : a.natDegree < b.natDegree := by
          have : max 0 (v.natDegree - 1) = 0 := by omega
          omega
        have hmax : max (b.natDegree : ℤ) (a.natDegree : ℤ) = (b.natDegree : ℤ) := by
          rw [max_eq_left]; exact_mod_cast hda.le
        rw [hmax]; omega
      · -- δ = 0: da < db (from b dominates), so the bound is max(0, dc - db)
        rename_i hδ0
        have hda : a.natDegree < b.natDegree := by
          have : max 0 (v.natDegree - 1) = 0 := by omega
          omega
        rw [if_pos (by exact_mod_cast hda)]; omega
  · by_cases hnl : 2 ≤ v.natDegree ∧ b.natDegree < a.natDegree + v.natDegree - 1
    · -- a·Dq strictly dominates (nonlinear): covered unconditionally
      obtain ⟨hv, hgt⟩ := hnl
      have hle := natDegree_le_of_aDominates_nonlinear ha0 hv heq hgt
      refine hle.trans ?_
      simp only [rdeBoundDegreeAbstract]
      rw [if_pos (by exact_mod_cast hv)]
      -- max(da+δ-1, db) = da+δ-1 since db < da+δ-1
      have hmax : max (a.natDegree + v.natDegree - 1 : ℤ) (b.natDegree : ℤ)
          = (a.natDegree + v.natDegree - 1 : ℤ) := by
        rw [max_eq_left]; omega
      rw [hmax]; omega
    · -- balanced: the residual
      exact hbal ⟨hbd, hnl⟩

/-! ### The sharp top-coefficient bound (the precise cancellation residual)

A sharper, uniform discharge of the degree bound for **all** δ: the candidate maximal degree of
`a·Dq + b·q` is `candTopDegree v a b q = max(dₐ + max(0, δ−1), d_b) + dq`; if the leading coefficient of
`c` *at that degree* does **not** vanish (no cancellation), the bound holds — `deg q ≤
rdeBoundDegreeAbstract v a b c`. This subsumes both strict-domination cases (there the dominant term
provides a nonzero top coefficient automatically) and pins the residual to **exactly** the top-coefficient
cancellation `c.coeff(candTopDegree) = 0` — the precise §6.3 `λ`-cancellation phenomenon, no `CharZero`
needed. -/

/-- **The candidate maximal degree** `candTopDegree v a b q = max(dₐ + max(0, δ−1), d_b) + dq` of the LHS
`a·Dq + b·q` (`D = implicitDeriv v`): both terms have degree `≤` this (the `a·Dq` term via
`natDegree_implicitDeriv_le`, the `b·q` term via `natDegree_mul_le`). The degree at which a leading-term
cancellation, if any, occurs. -/
def candTopDegree (v a b q : K[X]) : ℕ :=
  max (a.natDegree + max 0 (v.natDegree - 1)) b.natDegree + q.natDegree

omit [CharZero K] in
/-- **★ Bronstein Thm 6.3.1 over `K[X]`, the sharp top-coefficient form**
(`natDegree_le_rdeBoundDegreeAbstract_of_topCoeff_ne_zero`): if `q` solves `a·Dq + b·q = c` and the leading
coefficient of `c` at the candidate maximal degree does **not** vanish
(`c.coeff (candTopDegree v a b q) ≠ 0` — i.e. the top does not cancel), then
`deg q ≤ rdeBoundDegreeAbstract v a b c`. Uniform across **all** δ (no `CharZero`), and tight: `c` then has
degree exactly `candTopDegree`, so `dq = d_c − max(dₐ + max(0, δ−1), d_b)`, which is `≤` the engine's bound
in every case (with the δ = 0 `+1` absorbed). The residual is pinned to the precise cancellation
`c.coeff(candTopDegree) = 0`. -/
theorem natDegree_le_rdeBoundDegreeAbstract_of_topCoeff_ne_zero {v a b c q : K[X]}
    (heq : a * Differential.implicitDeriv v q + b * q = c)
    (htop : c.coeff (candTopDegree v a b q) ≠ 0) :
    q.natDegree ≤ rdeBoundDegreeAbstract v a b c := by
  -- upper bound: deg c ≤ candTopDegree (both LHS terms are bounded by it)
  have hub : c.natDegree ≤ candTopDegree v a b q := by
    rw [← heq, candTopDegree]
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · calc (a * Differential.implicitDeriv v q).natDegree
          ≤ a.natDegree + (Differential.implicitDeriv v q).natDegree := natDegree_mul_le
        _ ≤ a.natDegree + (q.natDegree + max 0 (v.natDegree - 1)) := by
            gcongr; exact natDegree_implicitDeriv_le v q
        _ ≤ _ := by
            have := le_max_left (a.natDegree + max 0 (v.natDegree - 1)) b.natDegree; omega
    · calc (b * q).natDegree ≤ b.natDegree + q.natDegree := natDegree_mul_le
        _ ≤ _ := by
            have := le_max_right (a.natDegree + max 0 (v.natDegree - 1)) b.natDegree; omega
  -- lower bound from the nonzero top coefficient: deg c = candTopDegree
  have hdc : c.natDegree = candTopDegree v a b q :=
    le_antisymm hub (le_natDegree_of_ne_zero htop)
  -- case on δ, matching the bound's branches
  simp only [rdeBoundDegreeAbstract, candTopDegree] at hdc ⊢
  split
  · -- δ ≥ 2
    rename_i hδ
    rw [show max 0 (v.natDegree - 1) = v.natDegree - 1 from by omega] at hdc
    rw [show max (a.natDegree + v.natDegree - 1 : ℤ) (b.natDegree : ℤ)
        = ((max (a.natDegree + (v.natDegree - 1)) b.natDegree : ℕ) : ℤ) from by push_cast; omega]
    omega
  · split
    · -- δ = 1
      rename_i hδ1
      rw [show max 0 (v.natDegree - 1) = 0 from by omega] at hdc
      rw [show max (b.natDegree : ℤ) (a.natDegree : ℤ)
          = ((max (a.natDegree + 0) b.natDegree : ℕ) : ℤ) from by push_cast; omega]
      omega
    · -- δ = 0
      rename_i hδ0
      rw [show max 0 (v.natDegree - 1) = 0 from by omega] at hdc
      split <;> omega

end AbstractBound

/-! ## The computable bridge `cRdeBoundDegreeG ↔ rdeBoundDegreeAbstract`

`cRdeBoundDegreeG` is the same §6.3 formula as `rdeBoundDegreeAbstract`, computed over `cdegG`s; since
`cdegG p = (toPolyG p).natDegree` (`cdegG_eq_natDegree`), the two coincide term-by-term. -/

section Bridge

variable {α : Type*} [CField α] [CFieldSpec α]

/-- **The computable degree bound equals the abstract one** (`cRdeBoundDegreeG_eq_abstract`):
`cRdeBoundDegreeG Dt fuel a b c = rdeBoundDegreeAbstract (toPolyG Dt) (toPolyG a) (toPolyG b) (toPolyG c)`
over `(CFieldSpec.K α)[X]`. Both are the identical Bronstein §6.3 case formula; the only difference is
`cdegG` vs `natDegree (toPolyG ·)`, identified by `cdegG_eq_natDegree`. -/
theorem cRdeBoundDegreeG_eq_abstract (Dt : CPolyG α) (fuel : ℕ) (a b c : CPolyG α) :
    cRdeBoundDegreeG Dt fuel a b c
      = rdeBoundDegreeAbstract (toPolyG Dt) (toPolyG a) (toPolyG b) (toPolyG c) := by
  simp only [cRdeBoundDegreeG, rdeBoundDegreeAbstract, cdegG_eq_natDegree]

end Bridge

/-! ## ★ The computable degree bound `cdegG q ≤ cRdeBoundDegreeG`, modulo the cancellation residual

Assembling the abstract bound with the bridge: a `CPolyG`-level solution `q` of the §6.3-reduced
`a·Dq + b·q = c` (`IsReducedRdeSol`) has `cdegG q ≤ cRdeBoundDegreeG …`, discharged uniformly via the sharp
top-coefficient bound and reducing exactly to the deep §6.3 cancellation residual. The residual condition —
the leading coefficient of `c` at the candidate maximal degree **vanishes**
(`(toPolyG c).coeff (candTopDegree …) = 0`) — is the precise §6.3 `λ`-cancellation: when the two LHS
leading terms cancel, the engine's bound omits the `λ` term and can fall short. No `CharZero`, no `a = 0`
special case (the top-coefficient lemma covers all configurations). This is exactly
`RischDEInnerCompleteness.hbound`'s shape. -/

section ComputableBound

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]

/-- **★ The §6.3 degree bound at the `CPolyG` layer, modulo the cancellation residual**
(`cdegG_le_cRdeBoundDegreeG_of_isReducedRdeSol`): any solution `q` of the §6.3-reduced
`a·Dq + b·q = c` (`IsReducedRdeSol Dt a b c q`, with `D = implicitDeriv (toPolyG Dt)`) has
`cdegG q ≤ cRdeBoundDegreeG Dt fuel a b c`, **provided** the residual `hres` discharges the **leading-term
cancellation** case `(toPolyG c).coeff (candTopDegree …) = 0`. When the top coefficient does *not* vanish
(no cancellation), the sharp `natDegree_le_rdeBoundDegreeAbstract_of_topCoeff_ne_zero` discharges the bound
unconditionally (all δ, including the strict-domination configurations); the residual supplies only the
genuine cancellation. This is `RischDEInnerCompleteness.hbound` modulo the precisely isolated deep §6.3
`λ`-cancellation. -/
theorem cdegG_le_cRdeBoundDegreeG_of_isReducedRdeSol (Dt : CPolyG α) (fuel : ℕ) (a b c q : CPolyG α)
    (hsol : IsReducedRdeSol Dt a b c q)
    (hres : (toPolyG c).coeff
          (candTopDegree (toPolyG Dt) (toPolyG a) (toPolyG b) (toPolyG q)) = 0 →
      cdegG q ≤ cRdeBoundDegreeG Dt fuel a b c) :
    cdegG q ≤ cRdeBoundDegreeG Dt fuel a b c := by
  -- the equation, read abstractly over `(CFieldSpec.K α)[X]`
  have heq : toPolyG a * Differential.implicitDeriv (toPolyG Dt) (toPolyG q)
      + toPolyG b * toPolyG q = toPolyG c := hsol
  by_cases htop : (toPolyG c).coeff
      (candTopDegree (toPolyG Dt) (toPolyG a) (toPolyG b) (toPolyG q)) = 0
  · exact hres htop
  · rw [cdegG_eq_natDegree, cRdeBoundDegreeG_eq_abstract]
    exact natDegree_le_rdeBoundDegreeAbstract_of_topCoeff_ne_zero heq htop

end ComputableBound

/-! ## ★ Wiring: `RischDEInnerCompleteness.hbound` modulo the precise cancellation residual

`cdegG_le_cRdeBoundDegreeG_of_isReducedRdeSol` proves the degree bound for the §6.3-reduced equation,
modulo the cancellation residual `toPolyG a = 0 ∨ RdeIsBalanced …`. We now bundle that residual over the
§6.2-special-cleared coefficients of an RDE input as the named `Prop` `RdeBoundCancellationResidual`, and
produce the **exact `hbound` field** of `RischDEInnerCompleteness` from it — closing the single deepest gap
of the completeness proof down to the precisely isolated deep §6.3 cancellation content (the omitted `λ`
term). The `hnorm`/`hsolve` clauses (the §6.2 normal-denominator and §6.4–6.6 exhaustiveness) remain the
*other* deep residuals, out of this file's scope; this file discharges `hbound`. -/

section Wiring

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCore α]

/-- **★ The precise §6.3 degree-bound cancellation residual** `RdeBoundCancellationResidual Dt fnum fden
gnum gden`: for every §6.2-normal-denominator output `(a0, b0, c0, h0)` and every solution `q` of the
§6.2-special-cleared §6.3-reduced equation, the degree bound `cdegG q ≤ cRdeBoundDegreeG …` holds whenever
the **leading-term cancellation** occurs — the leading coefficient of `c` at the candidate maximal degree
vanishes (`(toPolyG c).coeff (candTopDegree …) = 0`). This is exactly the residual that the sharp
top-coefficient bound does *not* cover: the genuine §6.3 `λ`-cancellation (the two LHS leading terms cancel,
`cRdeBoundDegreeG` omits the `λ` term, and the engine's bound can fall short). A stated `Prop`, NO `sorry`;
the precise, minimal deep content of `hbound`. -/
def RdeBoundCancellationResidual (Dt fnum fden gnum gden : CPolyG α) : Prop :=
  ∀ a0 b0 c0 h0 : CPolyG α,
    cRdeNormalDenominatorG Dt towerRischDEFuel fnum fden gnum gden = some (a0, b0, c0, h0) →
    ∀ q : CPolyG α,
      IsReducedRdeSol Dt (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).1
          (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.1
          (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.2.1 q →
      (toPolyG (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.2.1).coeff
          (candTopDegree (toPolyG Dt)
            (toPolyG (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).1)
            (toPolyG (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.1)
            (toPolyG q)) = 0 →
      cdegG q ≤ cRdeBoundDegreeG Dt towerRischDEFuel
        (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).1
        (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.1
        (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.2.1

/-- **★ `RischDEInnerCompleteness.hbound` modulo the cancellation residual**
(`hbound_of_cancellationResidual`): the **exact `hbound` field type** of `RischDEInnerCompleteness` —
every solution `q` of the §6.2-special-cleared §6.3-reduced equation has
`cdegG q ≤ cRdeBoundDegreeG …` — follows from the precise cancellation residual
`RdeBoundCancellationResidual`. The two strict-domination cases of Bronstein Thm 6.3.1 are discharged
unconditionally (`cdegG_le_cRdeBoundDegreeG_of_isReducedRdeSol`); the residual supplies only the
cancellation-prone configurations. This closes `hbound` — the single deepest gap of the completeness
proof — down to the precisely isolated deep §6.3 `λ`-cancellation content. -/
theorem hbound_of_cancellationResidual (Dt fnum fden gnum gden : CPolyG α)
    (hres : RdeBoundCancellationResidual Dt fnum fden gnum gden) :
    ∀ a0 b0 c0 h0 : CPolyG α,
      cRdeNormalDenominatorG Dt towerRischDEFuel fnum fden gnum gden = some (a0, b0, c0, h0) →
      ∀ q : CPolyG α,
        IsReducedRdeSol Dt (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).1
            (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.1
            (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.2.1 q →
        cdegG q ≤ cRdeBoundDegreeG Dt towerRischDEFuel
          (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).1
          (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.1
          (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.2.1 := by
  intro a0 b0 c0 h0 hnorm q hsol
  exact cdegG_le_cRdeBoundDegreeG_of_isReducedRdeSol Dt towerRischDEFuel _ _ _ q hsol
    (hres a0 b0 c0 h0 hnorm q hsol)

end Wiring

/-! ### Restatement against `RischDEInnerCompleteness.hbound`'s field type (anonymous `example`) -/

-- ★ The produced `hbound` has exactly `RischDEInnerCompleteness.hbound`'s type — confirmed by using it
-- as that field in a partial structure check (the `where`-field type, modulo the cancellation residual).
example {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCore α]
    [CRischField α] [Algebra ℚ (CFieldSpec.K α)] (Dt fnum fden gnum gden : CPolyG α)
    (hnorm : (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
      (cRdeNormalDenominatorG Dt towerRischDEFuel fnum fden gnum gden).isSome = true)
    (hsolve : (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
      (cRischDEG Dt towerRischDEFuel fnum fden gnum gden).isSome = true)
    (hres : RdeBoundCancellationResidual Dt fnum fden gnum gden) :
    RischDEInnerCompleteness Dt fnum fden gnum gden :=
  { hnorm := hnorm
    hbound := hbound_of_cancellationResidual Dt fnum fden gnum gden hres
    hsolve := hsolve }

/-! ### Final verdict (stated precisely)

**Is the §6.4 degree bound (Bronstein Thm 6.3.1) proven?** **The reachable cases, yes; the deep
cancellation case is precisely isolated.** `cdegG_le_cRdeBoundDegreeG_of_isReducedRdeSol` proves
`cdegG q ≤ cRdeBoundDegreeG …` for any solution `q` of the §6.3-reduced `a·Dq + b·q = c`, **modulo** the
precise residual `RdeBoundCancellationResidual` — the single **leading-term cancellation** case where the
top coefficient of `c` at the candidate maximal degree vanishes (`(toPolyG c).coeff (candTopDegree …) = 0`).
`hbound_of_cancellationResidual` produces the **exact `hbound` field** of `RischDEInnerCompleteness` from
that residual (confirmed by the structure-building `example`), closing the single deepest gap of the
completeness proof down to the deep §6.3 content.

**Which §6.3 cases are closed, and which is the deep residual?**
* **Closed unconditionally** (axiom-clean, NO `native_decide`/`sorry`): the sharp top-coefficient bound
  `natDegree_le_rdeBoundDegreeAbstract_of_topCoeff_ne_zero` — whenever the top coefficient of `c` at the
  candidate maximal degree `candTopDegree = max(dₐ + max(0, δ−1), d_b) + dq` does **not** vanish (no
  cancellation), `deg q ≤ rdeBoundDegreeAbstract`, uniformly across **all** δ (no `CharZero`). This subsumes
  the two explicit **strict-domination** lemmas `natDegree_le_of_bDominates` (the `b·q` term strictly
  dominates: `dₐ + max(0, δ−1) < d_b`) and `natDegree_le_of_aDominates_nonlinear` (δ ≥ 2 with
  `d_b < dₐ + δ − 1`, char-`0` exact degree) — in both, the dominant term provides a nonzero top coefficient
  automatically. Together they discharge every configuration where the two LHS leading terms do not cancel.
* **The deep residual** (`RdeBoundCancellationResidual`, NEVER `sorry`). The single **leading-term
  cancellation** case `(toPolyG c).coeff (candTopDegree …) = 0`: the two LHS leading terms cancel at the
  candidate maximal degree, dropping `deg c` below it. There the true degree bound (Bronstein §6.3) carries
  an extra `λ = −lc(b)/(lc(a)·lc(v))` integer-root term that `cRdeBoundDegreeG` **omits** ("the cancellation
  refinements are the documented continuation"), so the engine's bound can fall strictly below the solution
  degree — genuinely beyond the non-cancellation comparison. This is the precise §6.3 cancellation frontier.
  (The configurations where this can fire are exactly the **balanced** ones `RdeIsBalanced`: δ ≥ 2 with
  `dₐ + δ − 1 = d_b`, or δ ≤ 1 with `d_b ≤ dₐ` — recorded as a separate `Prop` with the earlier
  strict-domination discharge `natDegree_le_rdeBoundDegreeAbstract_of_balanced`.)

**Decision procedure?** Not yet unconditional: `hbound` is the single deepest gap *closed here modulo the
cancellation residual*, but `RischDEInnerCompleteness`'s sibling clauses `hnorm` (§6.2 normal-denominator
completeness) and `hsolve` (§6.4–6.6 SPDE/poly-RDE exhaustiveness) are the *other* deep residuals — out of
this file's scope. So `crischDESolveSound_decides` (the unconditional `some ⟺ solvable`) remains modulo
those; this file closes `hbound` to the reachable cases + the isolated cancellation residual. -/

/-! ### Axiom audit (the reachable §6.3 cases, the bridge, and the `hbound` discharge are axiom-clean;
NO `native_decide`, NO `sorry`) -/

#print axioms natDegree_le_of_bDominates
#print axioms natDegree_le_of_aDominates_nonlinear
#print axioms natDegree_le_rdeBoundDegreeAbstract_of_balanced
#print axioms natDegree_le_rdeBoundDegreeAbstract_of_topCoeff_ne_zero
#print axioms cRdeBoundDegreeG_eq_abstract
#print axioms cdegG_le_cRdeBoundDegreeG_of_isReducedRdeSol
#print axioms hbound_of_cancellationResidual

end DeepWiki.SymbolicIntegration
