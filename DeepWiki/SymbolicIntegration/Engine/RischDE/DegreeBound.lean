import DeepWiki.SymbolicIntegration.Engine.RischDE.Completeness
import DeepWiki.SymbolicIntegration.MonomialConstants

/-! # Degree-upper-bound for the reduced poly-RDE — the completeness keystone

Any polynomial solution `q` of the reduced linear ODE `a·Dq + b·q = c` has bounded degree
`deg q ≤ cRdeBoundDegree …`. Proved by leading-term comparison where it is a strict-domination case, with
the leading-term-cancellation case isolated as `RdeBoundCancellationResidualWf`. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac

/-! ## The abstract degree bound over `K[X]`, strict-domination cases

Over a field `K` with monomial derivation `D = implicitDeriv v`, for `a·Dq + b·q = c` with `q ≠ 0`. -/

section Abstract

variable {K : Type*} [Field K] [Differential K]

/-- The `b·q`-dominates case: if `q ≠ 0` solves `a·Dq + b·q = c` and `deg a + max(0, deg v − 1) < deg b`,
then `deg q ≤ deg c − deg b`. -/
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

/-- The nonlinear `a·Dq`-dominates case: for `deg v ≥ 2` over `CharZero K`, if `q ≠ 0` solves
`a·Dq + b·q = c` with `a ≠ 0` and `deg b < deg a + deg v − 1`, then `deg q ≤ deg c − (deg a + deg v − 1)`. -/
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

/-! ## The abstract `cRdeBoundDegree` formula and `hbound` modulo the cancellation residual -/

section AbstractBound

variable {K : Type*} [Field K] [CharZero K] [Differential K]

/-- The non-cancellation degree bound `rdeBoundDegreeAbstract v a b c` over `K[X]` in `natDegree`s, the
`cRdeBoundDegree` case formula (by `δ = deg v`). -/
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

/-- The balanced (cancellation-prone) configuration `RdeIsBalanced v a b c`: both strict-domination cases
fail — `deg a + max(0, δ−1) < deg b` and `2 ≤ δ ∧ deg b < deg a + δ − 1` both fail — so the two LHS leading
terms can cancel. -/
def RdeIsBalanced (v a b _c : K[X]) : Prop :=
  ¬ (a.natDegree + max 0 (v.natDegree - 1) < b.natDegree) ∧
    ¬ (2 ≤ v.natDegree ∧ b.natDegree < a.natDegree + v.natDegree - 1)

/-- The degree bound over `K[X]` modulo the cancellation residual: a nonzero `q` solving `a·Dq + b·q = c`
(with `a ≠ 0`) has `deg q ≤ rdeBoundDegreeAbstract v a b c`, provided the bound holds in the balanced case
(`hbal`). -/
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

/-! ### The sharp top-coefficient bound -/

/-- The candidate maximal degree `candTopDegree v a b q = max(dₐ + max(0, δ−1), d_b) + dq` of the LHS
`a·Dq + b·q` (`D = implicitDeriv v`): both terms have degree `≤` this. -/
def candTopDegree (v a b q : K[X]) : ℕ :=
  max (a.natDegree + max 0 (v.natDegree - 1)) b.natDegree + q.natDegree

omit [CharZero K] in
/-- The sharp top-coefficient form: if `q` solves `a·Dq + b·q = c` and
`c.coeff (candTopDegree v a b q) ≠ 0` (no top-degree cancellation), then
`deg q ≤ rdeBoundDegreeAbstract v a b c`, uniformly across all `δ`. -/
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

/-! ## The computable bridge `cRdeBoundDegree ↔ rdeBoundDegreeAbstract` -/

section Bridge

variable {α : Type*} [CField α] [CFieldSpec α]

/-- `cRdeBoundDegree Dt a b c = rdeBoundDegreeAbstract (toPoly Dt) (toPoly a) (toPoly b) (toPoly c)`
over `(CFieldSpec.K α)[X]`. -/
theorem cRdeBoundDegreeG_eq_abstract (Dt : DensePoly α) (a b c : DensePoly α) :
    cRdeBoundDegree Dt a b c
      = rdeBoundDegreeAbstract (toPoly Dt) (toPoly a) (toPoly b) (toPoly c) := by
  simp only [cRdeBoundDegree, rdeBoundDegreeAbstract, CPolyEngine.cdeg_dense_eq,
    cdegG_eq_natDegree]

end Bridge

/-! ## The computable degree bound `cdeg q ≤ cRdeBoundDegree`, modulo the cancellation residual -/

section ComputableBound

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]

/-- The degree bound at the `DensePoly` layer, modulo the cancellation residual: any `IsReducedRdeSol Dt a b c q`
has `cdeg q ≤ cRdeBoundDegree Dt a b c`, provided the residual `hres` discharges the leading-term
cancellation case `(toPoly c).coeff (candTopDegree …) = 0`. -/
theorem cdegG_le_cRdeBoundDegreeG_of_isReducedRdeSol (Dt : DensePoly α) (a b c q : DensePoly α)
    (hsol : IsReducedRdeSol Dt a b c q)
    (hres : (toPoly c).coeff
          (candTopDegree (toPoly Dt) (toPoly a) (toPoly b) (toPoly q)) = 0 →
      cdeg q ≤ cRdeBoundDegree Dt a b c) :
    cdeg q ≤ cRdeBoundDegree Dt a b c := by
  -- the equation, read abstractly over `(CFieldSpec.K α)[X]`
  have heq : toPoly a * Differential.implicitDeriv (toPoly Dt) (toPoly q)
      + toPoly b * toPoly q = toPoly c := hsol
  by_cases htop : (toPoly c).coeff
      (candTopDegree (toPoly Dt) (toPoly a) (toPoly b) (toPoly q)) = 0
  · exact hres htop
  · rw [cdegG_eq_natDegree, cRdeBoundDegreeG_eq_abstract]
    exact natDegree_le_rdeBoundDegreeAbstract_of_topCoeff_ne_zero heq htop

end ComputableBound

/-! ## Wiring: `RischDEInnerCompletenessWf.hbound` modulo the cancellation residual -/

section WiringWf

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [CPolyGcd DensePoly α] [CPolySplitFactor DensePoly α]

/-- The degree-bound cancellation residual over the special-cleared coefficients. -/
def RdeBoundCancellationResidualWf (Dt fnum fden gnum gden : DensePoly α) : Prop :=
  ∀ a0 b0 c0 h0 : DensePoly α,
    cRdeNormalDenominator Dt fnum fden gnum gden = some (a0, b0, c0, h0) →
    ∀ q : DensePoly α,
      IsReducedRdeSol Dt (cRdeSpecialDenominator Dt a0 b0 c0).1
          (cRdeSpecialDenominator Dt a0 b0 c0).2.1
          (cRdeSpecialDenominator Dt a0 b0 c0).2.2.1 q →
      (toPoly (cRdeSpecialDenominator Dt a0 b0 c0).2.2.1).coeff
          (candTopDegree (toPoly Dt)
            (toPoly (cRdeSpecialDenominator Dt a0 b0 c0).1)
            (toPoly (cRdeSpecialDenominator Dt a0 b0 c0).2.1)
            (toPoly q)) = 0 →
      cdeg q ≤ cRdeBoundDegree Dt
        (cRdeSpecialDenominator Dt a0 b0 c0).1
        (cRdeSpecialDenominator Dt a0 b0 c0).2.1
        (cRdeSpecialDenominator Dt a0 b0 c0).2.2.1

/-- The `hbound` field follows from the cancellation residual. -/
theorem hboundWf_of_cancellationResidualWf (Dt fnum fden gnum gden : DensePoly α)
    (hres : RdeBoundCancellationResidualWf Dt fnum fden gnum gden) :
    ∀ a0 b0 c0 h0 : DensePoly α,
      cRdeNormalDenominator Dt fnum fden gnum gden = some (a0, b0, c0, h0) →
      ∀ q : DensePoly α,
        IsReducedRdeSol Dt (cRdeSpecialDenominator Dt a0 b0 c0).1
            (cRdeSpecialDenominator Dt a0 b0 c0).2.1
            (cRdeSpecialDenominator Dt a0 b0 c0).2.2.1 q →
        cdeg q ≤ cRdeBoundDegree Dt
          (cRdeSpecialDenominator Dt a0 b0 c0).1
          (cRdeSpecialDenominator Dt a0 b0 c0).2.1
          (cRdeSpecialDenominator Dt a0 b0 c0).2.2.1 := by
  intro a0 b0 c0 h0 hnorm q hsol
  exact cdegG_le_cRdeBoundDegreeG_of_isReducedRdeSol Dt _ _ _ q hsol
    (hres a0 b0 c0 h0 hnorm q hsol)

end WiringWf

/-! ## Operational witness: the degree bound on a concrete primitive RDE -/

section Witness

open scoped Differential

/-- A concrete reduced primitive RDE solution: over `ℚ[x]`, `q = x` solves `1·Dq + 1·q = x + 1`
(`a = 1`, `b = 1`, `Dt = 1`, `D = d/dx`), an `IsReducedRdeSol` instance. -/
theorem reducedRdeSol_witness :
    IsReducedRdeSol ([1] : DensePoly ℚ) [1] [1] [1, 1] [0, 1] := by
  show toPoly ([1] : DensePoly ℚ)
        * Differential.implicitDeriv (toPoly ([1] : DensePoly ℚ)) (toPoly ([0, 1] : DensePoly ℚ))
      + toPoly ([1] : DensePoly ℚ) * toPoly ([0, 1] : DensePoly ℚ) = toPoly ([1, 1] : DensePoly ℚ)
  have h1 : toPoly ([1] : DensePoly ℚ) = 1 := by simp [toPoly, CRingSpec.toR, CFieldSpec.toK]
  have hx : toPoly ([0, 1] : DensePoly ℚ) = X := by simp [toPoly, CRingSpec.toR, CFieldSpec.toK]
  have hc : toPoly ([1, 1] : DensePoly ℚ) = 1 + X := by simp [toPoly, CRingSpec.toR, CFieldSpec.toK]
  rw [h1, hx, hc, Differential.implicitDeriv_X]; ring

/-- The computable degree bound holds on the witness: for `1·Dq + 1·q = x + 1` over `ℚ[x]`, `q = x` has
`cdeg q = 1 ≤ cRdeBoundDegree [1] [1] [1] [1,1] = 2`. -/
theorem cdegG_le_cRdeBoundDegreeG_witness :
    cdeg ([0, 1] : DensePoly ℚ) ≤ cRdeBoundDegree ([1] : DensePoly ℚ) [1] [1] [1, 1] := by
  native_decide

end Witness

end DeepWiki.SymbolicIntegration
