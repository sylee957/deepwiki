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
`a·Dq + b·q = c` (`IsReducedRdeSol`) has `cdegG q ≤ cRdeBoundDegreeG …`, discharging the two
strict-domination configurations unconditionally and reducing exactly to the deep §6.3 cancellation
residual. The residual domain `toPolyG a = 0 ∨ RdeIsBalanced …` is the precise complement of the clean
cases: the genuine `λ`-cancellation (`RdeIsBalanced`, where the leading terms cancel and `cRdeBoundDegreeG`
omits the `λ` term) together with the degenerate `a = 0` (where the equation collapses to `b·q = c` and the
nonlinear branch is vacuous). This is exactly `RischDEInnerCompleteness.hbound`'s shape. -/

section ComputableBound

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

/-- **★ The §6.3 degree bound at the `CPolyG` layer, modulo the cancellation residual**
(`cdegG_le_cRdeBoundDegreeG_of_isReducedRdeSol`): any solution `q` of the §6.3-reduced
`a·Dq + b·q = c` (`IsReducedRdeSol Dt a b c q`, with `D = implicitDeriv (toPolyG Dt)`) has
`cdegG q ≤ cRdeBoundDegreeG Dt fuel a b c`, **provided** the residual `hres` discharges the
cancellation-prone configurations `toPolyG a = 0 ∨ RdeIsBalanced …`. The two strict-domination
configurations (`toPolyG a ≠ 0` with `b·q` or nonlinear `a·Dq` strictly dominating) are discharged
unconditionally via `natDegree_le_rdeBoundDegreeAbstract_of_balanced` and the bridge; `q = 0` is trivial.
This is `RischDEInnerCompleteness.hbound` modulo the precisely isolated deep §6.3 residual (the omitted `λ`
cancellation term + the degenerate `a = 0`). -/
theorem cdegG_le_cRdeBoundDegreeG_of_isReducedRdeSol (Dt : CPolyG α) (fuel : ℕ) (a b c q : CPolyG α)
    (hsol : IsReducedRdeSol Dt a b c q)
    (hres : (toPolyG a = 0 ∨
        RdeIsBalanced (toPolyG Dt) (toPolyG a) (toPolyG b) (toPolyG c)) →
      cdegG q ≤ cRdeBoundDegreeG Dt fuel a b c) :
    cdegG q ≤ cRdeBoundDegreeG Dt fuel a b c := by
  haveI : CharZero (CFieldSpec.K α) := algebraRat.charZero (R := CFieldSpec.K α)
  -- the equation, read abstractly over `(CFieldSpec.K α)[X]`
  have heq : toPolyG a * Differential.implicitDeriv (toPolyG Dt) (toPolyG q)
      + toPolyG b * toPolyG q = toPolyG c := hsol
  rw [cdegG_eq_natDegree, cRdeBoundDegreeG_eq_abstract]
  by_cases hq0 : toPolyG q = 0
  · rw [hq0]; simp
  · by_cases ha0 : toPolyG a = 0
    · -- degenerate `a = 0`: routed to the residual
      have := hres (Or.inl ha0)
      rwa [cdegG_eq_natDegree, cRdeBoundDegreeG_eq_abstract] at this
    · -- `a ≠ 0`: the abstract bound, balanced → residual
      refine natDegree_le_rdeBoundDegreeAbstract_of_balanced hq0 ha0 heq (fun hbal => ?_)
      have := hres (Or.inr hbal)
      rwa [cdegG_eq_natDegree, cRdeBoundDegreeG_eq_abstract] at this

end ComputableBound

end DeepWiki.SymbolicIntegration
