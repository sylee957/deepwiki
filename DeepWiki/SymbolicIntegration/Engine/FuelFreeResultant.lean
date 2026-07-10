import DeepWiki.SymbolicIntegration.Engine.FuelFreeGcd
import DeepWiki.ComputableAlgebra.GenericBezout
import DeepWiki.ComputableAlgebra.PolyResultant

/-! # Well-founded generic resultant `cresultantWf`

The Euclidean-PRS resultant on `DensePoly`, by well-founded recursion on `cresultantMeasure`;
`[CField α]`-only, with the Sylvester-resultant identity `toPolyG_cresultantWf`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace DensePoly

variable {α : Type*} [CField α]

/-- Well-founded measure for `cresultantWf`: `2·(len p + len q) + len q`, `len` the normalized-list
length; strictly dropped by both the swap and reduce branches. -/
def cresultantMeasure (p q : DensePoly α) : ℕ :=
  2 * ((cnorm p : List α).length + (cnorm q : List α).length) + (cnorm q : List α).length

/-- Generic univariate resultant `cresultantWf p q = res(p, q) ∈ α` by the Euclidean PRS,
`[CField α]`-only; base cases `q = 0` (`1` if `p` constant, else `0`) and constant `q = c`
(`c^(deg p)`). -/
def cresultantWf (p q : DensePoly α) : α :=
  let pn := cnorm p
  let qn := cnorm q
  if cisZero qn then
    if (pn : List α).length ≤ 1 then CCommRing.one else CCommRing.zero
  else if (qn : List α).length ≤ 1 then
    cfpow (clead qn) (cdeg pn)
  else if (pn : List α).length < (qn : List α).length then
    let s := cfpow (CCommRing.neg CCommRing.one) (cdeg pn * cdeg qn)
    if cresultantMeasure q p < cresultantMeasure p q then
      CCommRing.mul s (cresultantWf q p)
    else s   -- unreachable over a genuine field (`cresultantMeasure_swap_lt`)
  else
    let r := cnorm (cmodWf p q)
    let sign := cfpow (CCommRing.neg CCommRing.one) (cdeg pn * cdeg qn)
    let lcpow := cfpow (clead qn) (cdeg pn - cdeg r)
    if cresultantMeasure q r < cresultantMeasure p q then
      CCommRing.mul (CCommRing.mul sign lcpow) (cresultantWf q r)
    else CCommRing.mul sign lcpow   -- unreachable over a genuine field (`cresultantMeasure_reduce_lt`)
termination_by cresultantMeasure p q
decreasing_by · assumption
              · assumption

variable [CFieldSpec α]

omit [CFieldSpec α] in
/-- The swap strictly drops the measure: `len p < len q` gives
`cresultantMeasure q p < cresultantMeasure p q`. -/
theorem cresultantMeasure_swap_lt (p q : DensePoly α)
    (hpq : (cnorm p : List α).length < (cnorm q : List α).length) :
    cresultantMeasure q p < cresultantMeasure p q := by
  simp only [cresultantMeasure]
  omega

/-- The reduce strictly drops the measure: for a nonzero divisor `q` with `len q ≤ len p`,
`cresultantMeasure q (cnorm (cmodWf p q)) < cresultantMeasure p q`. -/
theorem cresultantMeasure_reduce_lt (p q : DensePoly α) (hq : cnorm q ≠ [])
    (hpq : ¬ (cnorm p : List α).length < (cnorm q : List α).length) :
    cresultantMeasure q (cnorm (cmodWf p q)) < cresultantMeasure p q := by
  have hr : (cnorm (cmodWf p q) : List α).length < (cnorm q : List α).length :=
    cmodWf_length_lt p q hq
  simp only [cresultantMeasure, cnormG_idem]
  omega

/-- Quotient degree: for a non-constant divisor with `deg q ≤ deg p`,
`natDegree (cdivWf p q) + natDegree q = natDegree p`. -/
theorem cdivWf_natDegree_add (p q : DensePoly α) (hp : cnorm p ≠ []) (hq : cnorm q ≠ [])
    (hq2 : 2 ≤ (cnorm q : List α).length) (hpq : (cnorm q : List α).length ≤ (cnorm p : List α).length) :
    (toPoly (cdivWf p q)).natDegree + (toPoly q).natDegree = (toPoly p).natDegree := by
  have hP : toPoly p ≠ 0 := fun h => hp ((cnormG_eq_nil_iff p).mpr h)
  have hQ : toPoly q ≠ 0 := fun h => hq ((cnormG_eq_nil_iff q).mpr h)
  have hdiv : toPoly p = toPoly (cdivWf p q) * toPoly q + toPoly (cmodWf p q) :=
    toPolyG_cmodWf p q hq
  have hr : (toPoly (cmodWf p q)).natDegree < (toPoly q).natDegree := by
    have hlen := cmodWf_length_lt p q hq
    have e1 := cdegG_eq_natDegree (cmodWf p q)
    have e2 := cdegG_eq_natDegree q
    simp only [cdeg] at e1 e2
    omega
  have hpq' : (toPoly q).natDegree ≤ (toPoly p).natDegree := by
    have e1 := cdegG_eq_natDegree p
    have e2 := cdegG_eq_natDegree q
    simp only [cdeg] at e1 e2
    omega
  have hquo : toPoly (cdivWf p q) ≠ 0 := by
    intro h0
    rw [h0, zero_mul, zero_add] at hdiv
    rw [hdiv] at hpq'
    omega
  have key : (toPoly (cdivWf p q) * toPoly q).natDegree = (toPoly p).natDegree := by
    have heq : toPoly (cdivWf p q) * toPoly q = toPoly p - toPoly (cmodWf p q) := by
      rw [hdiv]; ring
    rw [heq, natDegree_sub_eq_left_of_natDegree_lt (lt_of_lt_of_le hr hpq')]
  rwa [Polynomial.natDegree_mul hquo hQ] at key

/-- Sylvester-resultant identity for `cresultantWf`:
`toK (cresultantWf p q) = Polynomial.resultant (toPoly p) (toPoly q) (deg p) (deg q)`. -/
@[denote] theorem toPolyG_cresultantWf (p q : DensePoly α) :
    CFieldSpec.toK (cresultantWf p q)
      = Polynomial.resultant (toPoly p) (toPoly q) (cdeg p) (cdeg q) := by
  induction p, q using cresultantWf.induct with
  | case1 p q =>
    -- `q = 0`, `len p ≤ 1`: `cresultantWf p q = 1`, `res(p, 0) = 1` (deg p = 0)
    rename_i pn qn hcz hp1
    have hcz' : cisZero (cnorm q) = true := hcz
    have hp1' : (cnorm p : List α).length ≤ 1 := hp1
    have hqnil : cnorm q = [] := by simpa [cisZero, cnormG_idem] using hcz'
    have hq0 : toPoly q = 0 := by
      have hnorm := congrArg toPoly hqnil
      simpa only [denote, toPolyG_nil] using hnorm
    have hdq : cdeg q = 0 := by simp [cdeg, hqnil]
    have hdp : cdeg p = 0 := by simp only [cdeg]; omega
    have hval : cresultantWf p q = CCommRing.one := by
      rw [cresultantWf.eq_def]; simp only [hcz', if_true, hp1']
    rw [hval, CFieldSpec.toK_one, hq0, Polynomial.resultant_zero_right, hdq, pow_zero, mul_one, hdp,
      pow_zero]
  | case2 p q =>
    -- `q = 0`, `¬ len p ≤ 1`: `cresultantWf p q = 0`, `res(p, 0) = 0` (deg p ≠ 0)
    rename_i pn qn hcz hp1
    have hcz' : cisZero (cnorm q) = true := hcz
    have hp1' : ¬ (cnorm p : List α).length ≤ 1 := hp1
    have hqnil : cnorm q = [] := by simpa [cisZero, cnormG_idem] using hcz'
    have hq0 : toPoly q = 0 := by
      have hnorm := congrArg toPoly hqnil
      simpa only [denote, toPolyG_nil] using hnorm
    have hdq : cdeg q = 0 := by simp [cdeg, hqnil]
    have hdp : cdeg p ≠ 0 := by simp only [cdeg]; omega
    have hval : cresultantWf p q = CCommRing.zero := by
      rw [cresultantWf.eq_def]; simp only [hcz', if_true, hp1', if_false]
    rw [hval, CFieldSpec.toK_zero, hq0, Polynomial.resultant_zero_right, hdq, pow_zero, mul_one,
      zero_pow hdp]
  | case3 p q =>
    -- `q` a nonzero constant (`len q ≤ 1`): `cresultantWf p q = (lead q)^(deg p)`, `res(p, c) = c^(deg p)`
    rename_i pn qn hcz hqc
    have hcz' : ¬ cisZero (cnorm q) = true := hcz
    have hqc' : (cnorm q : List α).length ≤ 1 := hqc
    have hq : cnorm q ≠ [] := fun h => by simp [cisZero, h] at hcz'
    have hdq : cdeg q = 0 := by simp only [cdeg]; omega
    have hval : cresultantWf p q = cfpow (clead q) (cdeg p) := by
      rw [cresultantWf.eq_def]
      simp only [hcz', Bool.false_eq_true, if_false, if_pos hqc', cleadG_cnormG, cdegG_cnormG]
    rw [hval, toK_cfpow, hdq, Polynomial.resultant_zero_right_deg, toK_cleadG_eq_coeff, hdq]
  | case4 p q =>
    -- swap branch (recursing): `cresultantWf p q = (-1)^(deg p·deg q) · cresultantWf q p`, `resultant_comm`
    rename_i pn qn hcz hqc hpq hdec ih
    have hcz' : ¬ cisZero (cnorm q) = true := hcz
    have hqc' : ¬ (cnorm q : List α).length ≤ 1 := hqc
    have hpq' : (cnorm p : List α).length < (cnorm q : List α).length := hpq
    have hdec' : cresultantMeasure q p < cresultantMeasure p q := hdec
    have hval : CFieldSpec.toK (cresultantWf p q)
        = CFieldSpec.toK (cfpow (CCommRing.neg CCommRing.one) (cdeg p * cdeg q))
          * CFieldSpec.toK (cresultantWf q p) := by
      rw [cresultantWf.eq_def]
      simp only [hcz', Bool.false_eq_true, if_false, if_neg hqc', if_pos hpq',
        if_pos hdec', cdegG_cnormG, CFieldSpec.toK_mul]
    rw [hval, toK_cfpow, ih, CFieldSpec.toK_neg, CFieldSpec.toK_one,
      Polynomial.resultant_comm (toPoly p) (toPoly q)]
  | case5 p q =>
    -- swap branch (unreachable): `cresultantMeasure_swap_lt`
    rename_i pn qn hcz hqc hpq hdec
    have hpq' : (cnorm p : List α).length < (cnorm q : List α).length := hpq
    have hdec' : ¬ cresultantMeasure q p < cresultantMeasure p q := hdec
    exact absurd (cresultantMeasure_swap_lt p q hpq') hdec'
  | case6 p q =>
    -- reduce branch (recursing): `cresultantWf p q = sign · lcpow · cresultantWf q r`, `r = cnorm (cmodWf p q)`
    rename_i pn qn hcz hqc hpq rr hdec ih
    have hcz' : ¬ cisZero (cnorm q) = true := hcz
    have hqc' : ¬ (cnorm q : List α).length ≤ 1 := hqc
    have hpqlen : ¬ (cnorm p : List α).length < (cnorm q : List α).length := hpq
    have hdec' : cresultantMeasure q (cnorm (cmodWf p q)) < cresultantMeasure p q := hdec
    have hq : cnorm q ≠ [] := fun h => by simp [cisZero, h] at hcz'
    have hp : cnorm p ≠ [] := by
      intro h; rw [h, List.length_nil] at hpqlen; exact hpqlen (by omega)
    have hq2 : 2 ≤ (cnorm q : List α).length := by omega
    have hpqge : (cnorm q : List α).length ≤ (cnorm p : List α).length := by omega
    have hRlen : (cnorm (cmodWf p q) : List α).length < (cnorm q : List α).length :=
      cmodWf_length_lt p q hq
    have hval : CFieldSpec.toK (cresultantWf p q)
        = CFieldSpec.toK (cfpow (CCommRing.neg CCommRing.one) (cdeg p * cdeg q))
          * CFieldSpec.toK (cfpow (clead q) (cdeg p - cdeg (cnorm (cmodWf p q))))
          * CFieldSpec.toK (cresultantWf q (cnorm (cmodWf p q))) := by
      rw [cresultantWf.eq_def]
      simp only [hcz', Bool.false_eq_true, if_false, if_neg hqc', if_neg hpqlen,
        if_pos hdec', cleadG_cnormG, cdegG_cnormG, CFieldSpec.toK_mul]
    rw [hval, toK_cfpow, toK_cfpow]
    -- IH on `(q, r)` with `r = cnorm (cmodWf p q)`
    rw [ih]
    have hP : toPoly p ≠ 0 := fun h => hp ((cnormG_eq_nil_iff p).mpr h)
    have hQ : toPoly q ≠ 0 := fun h => hq ((cnormG_eq_nil_iff q).mpr h)
    have hdp : cdeg p = (toPoly p).natDegree := cdegG_eq_natDegree p
    have hdq : cdeg q = (toPoly q).natDegree := cdegG_eq_natDegree q
    have hdr : cdeg (cmodWf p q) = (toPoly (cmodWf p q)).natDegree := cdegG_eq_natDegree _
    have hdrlt : (toPoly (cmodWf p q)).natDegree < (toPoly q).natDegree := by
      rw [← hdr, ← hdq]; simp only [cdeg]; omega
    have hqp : (toPoly q).natDegree ≤ (toPoly p).natDegree := by
      rw [← hdq, ← hdp]; simp only [cdeg]; omega
    have hrnorm : toPoly (cnorm (cmodWf p q)) = toPoly (cmodWf p q) := by
      simp only [denote]
    have hdrnorm : cdeg (cnorm (cmodWf p q)) = cdeg (cmodWf p q) := cdegG_cnormG _
    have hdiv : toPoly p
        = toPoly (cmodWf p q) + toPoly q * toPoly (cdivWf p q) := by
      have h : toPoly p = toPoly (cdivWf p q) * toPoly q + toPoly (cmodWf p q) :=
        toPolyG_cmodWf p q hq
      linear_combination h
    have hqd : (toPoly (cdivWf p q)).natDegree + (toPoly q).natDegree = (toPoly p).natDegree :=
      cdivWf_natDegree_add p q hp hq hq2 hpqge
    rw [hrnorm, hdrnorm]
    rw [CFieldSpec.toK_neg, CFieldSpec.toK_one]
    rw [Polynomial.resultant_comm (toPoly p) (toPoly q), hdiv,
      Polynomial.resultant_add_mul_right (toPoly q) (toPoly (cmodWf p q))
        (toPoly (cdivWf p q)) (cdeg q) (cdeg p)
        (by rw [hdp, hdq]; omega) (le_of_eq hdq.symm)]
    rw [hdp, show (toPoly p).natDegree
          = (toPoly (cmodWf p q)).natDegree + (cdeg p - cdeg (cmodWf p q))
        from by rw [hdr, hdp]; omega,
      Polynomial.resultant_add_right_deg (toPoly q) (toPoly (cmodWf p q)) (cdeg q)
        (toPoly (cmodWf p q)).natDegree (cdeg p - cdeg (cmodWf p q)) le_rfl]
    rw [← hdr, toK_cleadG_eq_coeff, Nat.add_sub_cancel_left]
    ring
  | case7 p q =>
    -- reduce branch (unreachable): `cresultantMeasure_reduce_lt`
    rename_i pn qn hcz hqc hpq rr hdec
    have hcz' : ¬ cisZero (cnorm q) = true := hcz
    have hpqlen : ¬ (cnorm p : List α).length < (cnorm q : List α).length := hpq
    have hdec' : ¬ cresultantMeasure q (cnorm (cmodWf p q)) < cresultantMeasure p q := hdec
    have hq : cnorm q ≠ [] := fun h => by simp [cisZero, h] at hcz'
    exact absurd (cresultantMeasure_reduce_lt p q hq hpqlen) hdec'

end DensePoly

/-! ### Dense capability instance -/

/-- Dense polynomials select the well-founded Euclidean-PRS resultant. -/
instance instCPolyResultantDense : CPolyResultant DensePoly where
  compute := DensePoly.cresultantWf

namespace CPolyResultant

/-- Dense resultant selection is `DensePoly.cresultantWf`. -/
@[simp] theorem compute_dense_eq {α : Type*} [CField α] (p q : DensePoly α) :
    CPolyResultant.compute p q = DensePoly.cresultantWf p q := rfl

end CPolyResultant

/-- The dense well-founded resultant satisfies the abstract resultant law. -/
instance instLawfulCPolyResultantDense : LawfulCPolyResultant DensePoly where
  compute_spec := by
    intro α _ _ p q
    rw [CPolyResultant.compute_dense_eq, toPoly_list_eq, toPoly_list_eq,
      cdeg_list_eq, cdeg_list_eq]
    exact DensePoly.toPolyG_cresultantWf p q

end DeepWiki.SymbolicIntegration
