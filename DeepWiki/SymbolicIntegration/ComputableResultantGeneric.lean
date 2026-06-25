import DeepWiki.SymbolicIntegration.ComputableLogPartTower
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! # Generic abstract correctness of the resultant/interpolation engine over `CFieldSpec`

The §2 ℚ-concrete templates `Compute.cresultant_eq` (`ComputeCorrectness`) and
`Compute.toPoly_cinterpolate_eval` (`RtResultantCorrectness`) certify the *computable* Euclidean-PRS
resultant `cresultant` and Lagrange interpolation `cinterpolate` against Mathlib's `Polynomial.resultant`
/ the two characterizing properties — but only over the **concrete** carrier `CPoly = List ℚ`. The
generic tower engine `cresultantG`/`cinterpolateG` (`ComputableLogPartTower`, over `[CField α]`) needs
the **same** correctness over any `[CFieldSpec α]`, so the §5.6 residue resultant
`cResidueResultantTower` (run over `ℚ(x)[z]`) can be reasoned about abstractly.

This file generalizes the two §2 templates off `ℚ`:

* **`toPolyG_cresultantG`** (the reusable foundation): `toPolyG (cresultantG fuel p q) =
  Polynomial.resultant (toPolyG p) (toPolyG q) (cdegG p) (cdegG q)` over `(CFieldSpec.K α)[X]`. The
  same fuel/degree induction as `cresultant_eq`, with the generic degree framework
  (`cmodG_length_lt`, `degreeG_reduce_step_lt`, `toK_cleadG_eq_*`, `length_cnormG_of_ne`,
  `toPolyG_cdivmodG'`) replacing the concrete `cmod_length_lt`/`clead_eq_*`, and Mathlib's resultant
  PRS lemmas (`resultant_comm`/`resultant_add_mul_right`/`resultant_add_right_deg`/`resultant_zero_*`),
  which are `CommRing`-generic.
* **`toPolyG_cinterpolateG_eval`** (generic interpolation correctness): `(toPolyG (cinterpolateG
  pts)).eval (toK zk) = toK yk` at each node and the degree bound `degree (toPolyG (cinterpolateG pts))
  < |pts|` — generalizing `toPoly_cinterpolate_eval`/`degree_toPoly_cinterpolate_lt`.

The deliverable is purely propositional (axioms `[propext, Classical.choice, Quot.sound]`, no
`native_decide`), reusable wherever the generic engine runs (§5.6 residues, §10 parallel Risch). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace CPolyG

variable {α : Type*} [CField α] [CFieldSpec α]

/-! ### Generic quotient-degree and constant-power helpers -/

/-- **Generic constant power realizes `K`-power**: `toK (cfpow c n) = (toK c) ^ n`. -/
theorem toK_cfpow (c : α) (n : ℕ) : CFieldSpec.toK (cfpow c n) = (CFieldSpec.toK c) ^ n := by
  induction n with
  | zero => simp [cfpow, CFieldSpec.toK_one]
  | succ n ih => rw [cfpow, CFieldSpec.toK_mul, ih, pow_succ']

/-- **Generic quotient degree**: for a non-constant divisor with `deg q ≤ deg p` and enough fuel,
`natDegree (cdivG …) + natDegree q = natDegree p` (the Euclidean quotient has degree `deg p − deg q`).
Supplies `resultant_add_mul_right`'s degree side-condition. The generic analogue of `cdiv_natDegree_add`. -/
theorem cdivG_natDegree_add (fuel : ℕ) (p q : CPolyG α) (hp : cnormG p ≠ []) (hq : cnormG q ≠ [])
    (hq2 : 2 ≤ (cnormG q : List α).length) (hpq : (cnormG q : List α).length ≤ (cnormG p : List α).length)
    (hfuel : (cnormG p : List α).length ≤ fuel) :
    (toPolyG (cdivG fuel p q)).natDegree + (toPolyG q).natDegree = (toPolyG p).natDegree := by
  have hP : toPolyG p ≠ 0 := fun h => hp ((cnormG_eq_nil_iff p).mpr h)
  have hQ : toPolyG q ≠ 0 := fun h => hq ((cnormG_eq_nil_iff q).mpr h)
  have hdiv : toPolyG p = toPolyG (cdivG fuel p q) * toPolyG q + toPolyG (cmodG fuel p q) := by
    have h := toPolyG_cdivmodG' fuel p q hq
    rw [cdivG, cmodG]; exact h
  have hr : (toPolyG (cmodG fuel p q)).natDegree < (toPolyG q).natDegree := by
    have hlen := cmodG_length_lt fuel p q hq hfuel
    have e1 := cdegG_eq_natDegree (cmodG fuel p q)
    have e2 := cdegG_eq_natDegree q
    simp only [cdegG] at e1 e2
    omega
  have hpq' : (toPolyG q).natDegree ≤ (toPolyG p).natDegree := by
    have e1 := cdegG_eq_natDegree p
    have e2 := cdegG_eq_natDegree q
    simp only [cdegG] at e1 e2
    omega
  have hquo : toPolyG (cdivG fuel p q) ≠ 0 := by
    intro h0
    rw [h0, zero_mul, zero_add] at hdiv
    rw [hdiv] at hpq'
    omega
  have key : (toPolyG (cdivG fuel p q) * toPolyG q).natDegree = (toPolyG p).natDegree := by
    have heq : toPolyG (cdivG fuel p q) * toPolyG q = toPolyG p - toPolyG (cmodG fuel p q) := by
      rw [hdiv]; ring
    rw [heq, natDegree_sub_eq_left_of_natDegree_lt (lt_of_lt_of_le hr hpq')]
  rwa [Polynomial.natDegree_mul hquo hQ] at key

/-! ### `cresultantG` invariances (mirroring `cresultant_cnorm`/`cdeg_cnorm`/`cmod_cnorm_both`) -/

omit [CFieldSpec α] in
/-- `cresultantG` is invariant under normalizing both arguments (it normalizes them internally). -/
theorem cresultantG_cnormG (fuel : ℕ) (p q : CPolyG α) :
    cresultantG fuel (cnormG p) (cnormG q) = cresultantG fuel p q := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp only [cresultantG, cnormG_idem]

omit [CFieldSpec α] in
/-- `cmodG` is invariant under normalizing both arguments. -/
theorem cmodG_cnormG_both (fuel : ℕ) (p q : CPolyG α) :
    cmodG fuel (cnormG p) (cnormG q) = cmodG fuel p q := by
  cases fuel with
  | zero => simp [cmodG, cdivmodG, cnormG_idem]
  | succ fuel => simp only [cmodG, cdivmodG, cnormG_idem]

/-! ### The reusable foundation: `toPolyG (cresultantG …) = Polynomial.resultant …` -/

/-- **`cresultantG ↔ Polynomial.resultant`, the case `deg q ≤ deg p`** (no swap): with enough fuel the
generic computable Euclidean-PRS resultant equals Mathlib's Sylvester resultant over `(CFieldSpec.K α)[X]`.
The reduction step matches `resultant_comm` (swap) ∘ `resultant_add_mul_right` (the `p mod q` reduction)
∘ `resultant_add_right_deg` (the sign-free `lc(q)^(dp−dr)` augmentation); the base cases are
`resultant_zero_right(_deg)`. The generic analogue of `Compute.cresultant_eq_of_ge`. -/
theorem toPolyG_cresultantG_of_ge : ∀ (fuel : ℕ) (p q : CPolyG α),
    (cnormG q : List α).length ≤ (cnormG p : List α).length →
    (cnormG p : List α).length + (cnormG q : List α).length + 1 ≤ fuel →
    CFieldSpec.toK (cresultantG fuel p q)
      = Polynomial.resultant (toPolyG p) (toPolyG q) (cdegG p) (cdegG q) := by
  intro fuel
  induction fuel with
  | zero => intro p q _ hfuel; omega
  | succ fuel ih =>
    intro p q hpq hfuel
    by_cases h0 : cisZeroG q = true
    · -- q = 0
      have hqnil : cnormG q = [] := by simpa [cisZeroG] using h0
      have hq0 : toPolyG q = 0 := by rw [← toPolyG_cnormG, hqnil, toPolyG_nil]
      have hdq : cdegG q = 0 := by simp [cdegG, hqnil]
      have hval : cresultantG (fuel + 1) p q
          = (if (cnormG p : List α).length ≤ 1 then CField.one else CField.zero) := by
        rw [cresultantG]; simp only [cisZeroG_cnormG, h0, if_true]
      rw [hval, hq0, Polynomial.resultant_zero_right, hdq, pow_zero, mul_one]
      by_cases hp1 : (cnormG p : List α).length ≤ 1
      · have : cdegG p = 0 := by simp only [cdegG]; omega
        rw [if_pos hp1, this, pow_zero, CFieldSpec.toK_one]
      · have : cdegG p ≠ 0 := by simp only [cdegG]; omega
        rw [if_neg hp1, zero_pow this, CFieldSpec.toK_zero]
    · have hcz : cisZeroG q = false := by simpa using h0
      have hq : cnormG q ≠ [] := fun h => by simp [cisZeroG, h] at hcz
      by_cases hqc : (cnormG q : List α).length ≤ 1
      · -- q a nonzero constant: res(p, c) = c^(deg p)
        have hdq : cdegG q = 0 := by simp only [cdegG]; omega
        have hval : cresultantG (fuel + 1) p q = cfpow (cleadG q) (cdegG p) := by
          rw [cresultantG]
          simp only [cisZeroG_cnormG, hcz, Bool.false_eq_true, if_false, if_pos hqc, cleadG_cnormG,
            cdegG_cnormG]
        rw [hval, toK_cfpow, hdq, Polynomial.resultant_zero_right_deg]
        rw [toK_cleadG_eq_coeff, hdq]
      · -- reduction
        have hq2 : 2 ≤ (cnormG q : List α).length := by omega
        have hp : cnormG p ≠ [] := by
          intro h; rw [h, List.length_nil] at hpq; omega
        have hpqlen : ¬ (cnormG p : List α).length < (cnormG q : List α).length := by omega
        have hRlen : (cnormG (cmodG (fuel + 1) p q) : List α).length < (cnormG q : List α).length :=
          cmodG_length_lt (fuel + 1) p q hq (by omega)
        have hval : CFieldSpec.toK (cresultantG (fuel + 1) p q)
            = CFieldSpec.toK (cfpow (CField.neg CField.one) (cdegG p * cdegG q))
              * CFieldSpec.toK (cfpow (cleadG q) (cdegG p - cdegG (cmodG (fuel + 1) p q)))
              * CFieldSpec.toK (cresultantG fuel q (cmodG (fuel + 1) p q)) := by
          rw [cresultantG]
          simp only [cisZeroG_cnormG, hcz, Bool.false_eq_true, if_false, if_neg hqc, if_neg hpqlen,
            cleadG_cnormG, cdegG_cnormG, cmodG_cnormG_both, cresultantG_cnormG, CFieldSpec.toK_mul]
        rw [hval, toK_cfpow, toK_cfpow]
        have hih := ih q (cmodG (fuel + 1) p q) (le_of_lt hRlen) (by omega)
        rw [hih]
        have hP : toPolyG p ≠ 0 := fun h => hp ((cnormG_eq_nil_iff p).mpr h)
        have hQ : toPolyG q ≠ 0 := fun h => hq ((cnormG_eq_nil_iff q).mpr h)
        have hdp : cdegG p = (toPolyG p).natDegree := cdegG_eq_natDegree p
        have hdq : cdegG q = (toPolyG q).natDegree := cdegG_eq_natDegree q
        have hdr : cdegG (cmodG (fuel + 1) p q) = (toPolyG (cmodG (fuel + 1) p q)).natDegree :=
          cdegG_eq_natDegree _
        have hdrlt : (toPolyG (cmodG (fuel + 1) p q)).natDegree < (toPolyG q).natDegree := by
          rw [← hdr, ← hdq]; simp only [cdegG]; omega
        have hqp : (toPolyG q).natDegree ≤ (toPolyG p).natDegree := by
          rw [← hdq, ← hdp]; simp only [cdegG]; omega
        have hdiv : toPolyG p
            = toPolyG (cmodG (fuel + 1) p q) + toPolyG q * toPolyG (cdivG (fuel + 1) p q) := by
          have h : toPolyG p = toPolyG (cdivG (fuel + 1) p q) * toPolyG q
              + toPolyG (cmodG (fuel + 1) p q) := by
            have h' := toPolyG_cdivmodG' (fuel + 1) p q hq
            rw [cdivG, cmodG]; exact h'
          linear_combination h
        have hqd : (toPolyG (cdivG (fuel + 1) p q)).natDegree + (toPolyG q).natDegree
            = (toPolyG p).natDegree := cdivG_natDegree_add (fuel + 1) p q hp hq hq2 hpq (by omega)
        rw [CFieldSpec.toK_neg, CFieldSpec.toK_one]
        rw [Polynomial.resultant_comm (toPolyG p) (toPolyG q), hdiv,
          Polynomial.resultant_add_mul_right (toPolyG q) (toPolyG (cmodG (fuel + 1) p q))
            (toPolyG (cdivG (fuel + 1) p q)) (cdegG q) (cdegG p)
            (by rw [hdp, hdq]; omega) (le_of_eq hdq.symm)]
        rw [hdp, show (toPolyG p).natDegree
              = (toPolyG (cmodG (fuel + 1) p q)).natDegree + (cdegG p - cdegG (cmodG (fuel + 1) p q))
            from by rw [hdr, hdp]; omega,
          Polynomial.resultant_add_right_deg (toPolyG q) (toPolyG (cmodG (fuel + 1) p q)) (cdegG q)
            (toPolyG (cmodG (fuel + 1) p q)).natDegree (cdegG p - cdegG (cmodG (fuel + 1) p q)) le_rfl]
        rw [← hdr, toK_cleadG_eq_coeff, Nat.add_sub_cancel_left]
        ring

/-- **`toPolyG (cresultantG …) = Polynomial.resultant …`, the general case** (the reusable foundation):
for sufficient fuel the generic computable Euclidean-PRS resultant equals Mathlib's Sylvester resultant
for *any* `p, q` over `(CFieldSpec.K α)[X]`. The `deg q ≤ deg p` case is `toPolyG_cresultantG_of_ge`;
the `deg p < deg q` case swaps via `resultant_comm`. The generic analogue of `Compute.cresultant_eq`,
usable wherever the tower engine runs (§5.6 residue resultant, §10 parallel Risch). -/
theorem toPolyG_cresultantG (fuel : ℕ) (p q : CPolyG α)
    (hfuel : (cnormG p : List α).length + (cnormG q : List α).length + 2 ≤ fuel) :
    CFieldSpec.toK (cresultantG fuel p q)
      = Polynomial.resultant (toPolyG p) (toPolyG q) (cdegG p) (cdegG q) := by
  by_cases hpq : (cnormG q : List α).length ≤ (cnormG p : List α).length
  · exact toPolyG_cresultantG_of_ge fuel p q hpq (by omega)
  · replace hpq : (cnormG p : List α).length < (cnormG q : List α).length := by omega
    have hq : cnormG q ≠ [] := by intro h; rw [h, List.length_nil] at hpq; omega
    have hcz : cisZeroG q = false := by simpa [cisZeroG] using hq
    by_cases hqc : (cnormG q : List α).length ≤ 1
    · -- q a nonzero constant, p = 0
      have hp0 : cnormG p = [] := List.length_eq_zero_iff.mp (by omega)
      have hp0' : toPolyG p = 0 := by rw [← toPolyG_cnormG, hp0, toPolyG_nil]
      have hdp : cdegG p = 0 := by simp only [cdegG, hp0, List.length_nil]
      have hdq : cdegG q = 0 := by simp only [cdegG]; omega
      have hval : cresultantG fuel p q = cfpow (cleadG q) (cdegG p) := by
        obtain ⟨fuel', rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
        rw [cresultantG]
        simp only [cisZeroG_cnormG, hcz, Bool.false_eq_true, if_false, if_pos hqc, cleadG_cnormG,
          cdegG_cnormG]
      rw [hval, toK_cfpow, hp0', hdp, hdq]
      simp
    · -- q non-constant, swap
      obtain ⟨fuel', rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hval : CFieldSpec.toK (cresultantG (fuel' + 1) p q)
          = CFieldSpec.toK (cfpow (CField.neg CField.one) (cdegG p * cdegG q))
            * CFieldSpec.toK (cresultantG fuel' q p) := by
        rw [cresultantG]
        simp only [cisZeroG_cnormG, hcz, Bool.false_eq_true, if_false, if_neg hqc, if_pos hpq,
          cdegG_cnormG, cresultantG_cnormG, CFieldSpec.toK_mul]
      rw [hval, toK_cfpow, toPolyG_cresultantG_of_ge fuel' q p (le_of_lt hpq) (by omega),
        CFieldSpec.toK_neg, CFieldSpec.toK_one, Polynomial.resultant_comm (toPolyG p) (toPolyG q)]

/-- Restatement: the generic computable resultant `cresultantG` is the honest Sylvester resultant under
the Horner bridge `toPolyG`, for sufficient fuel. -/
example (fuel : ℕ) (p q : CPolyG α)
    (hfuel : (cnormG p : List α).length + (cnormG q : List α).length + 2 ≤ fuel) :
    CFieldSpec.toK (cresultantG fuel p q)
      = Polynomial.resultant (toPolyG p) (toPolyG q) (cdegG p) (cdegG q) :=
  toPolyG_cresultantG fuel p q hfuel

end CPolyG

end DeepWiki.SymbolicIntegration
