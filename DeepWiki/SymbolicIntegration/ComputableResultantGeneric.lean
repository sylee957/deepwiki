import DeepWiki.SymbolicIntegration.ComputableLogPartTower
import DeepWiki.SymbolicIntegration.ComputableIntegrate
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.LinearAlgebra.Lagrange

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

/-! ### Generic interpolation correctness (generalizing `toPoly_cinterpolate_eval`)

The generic `cinterpolateG pts` filters abscissas `zⱼ` by `isZero (zⱼ − zₖ) = false`, i.e.
`toK zⱼ ≠ toK zₖ` in `K`. So node evaluation and the degree bound are stated through `toK` on the
abscissas: `(toPolyG (cinterpolateG pts)).eval (toK zₖ) = toK yₖ` when the abscissa images
`pts.map (toK ∘ Prod.fst)` are nodup, and `degree (toPolyG (cinterpolateG pts)) < |pts|`. -/

/-- **`clagNumG` realizes `∏ (X − C (toK zⱼ))`**: the Horner bridge sends the generic basis numerator to
the abstract product of linear factors. -/
theorem toPolyG_clagNumG (zs : List α) :
    toPolyG (clagNumG zs) = (zs.map (fun z => Polynomial.X - Polynomial.C (CFieldSpec.toK z))).prod := by
  induction zs with
  | nil => simp [clagNumG, toPolyG_cons, CFieldSpec.toK_one]
  | cons z zs ih =>
    rw [clagNumG, toPolyG_cmulG, ih, List.map_cons, List.prod_cons]
    have hfac : toPolyG ([CField.neg z, CField.one] : CPolyG α)
        = Polynomial.X - Polynomial.C (CFieldSpec.toK z) := by
      rw [toPolyG_cons, toPolyG_cons, toPolyG_nil, CFieldSpec.toK_neg, CFieldSpec.toK_one, map_neg,
        map_one]; ring
    rw [hfac]

/-- **`toPolyG` of the `cinterpolateG` accumulator fold** is the running sum (generic analogue of
`toPoly_foldl_cadd`). -/
theorem toPolyG_foldl_caddG (f : α × α → CPolyG α) (pts : List (α × α)) (init : CPolyG α) :
    toPolyG (pts.foldl (fun acc p => caddG acc (f p)) init)
      = toPolyG init + (pts.map (fun p => toPolyG (f p))).sum := by
  induction pts generalizing init with
  | nil => simp
  | cons p ps ih =>
    rw [List.foldl_cons, ih, toPolyG_caddG, List.map_cons, List.sum_cons]
    ring

/-- The generic denominator fold `∏ acc·(zk − zⱼ)` equals `toK init · ∏ (toK zk − toK zⱼ)` under `toK`. -/
theorem toK_foldl_csub_mul (zk : α) (others : List α) (init : α) :
    CFieldSpec.toK (others.foldl (fun acc zj => CField.mul acc (CField.sub zk zj)) init)
      = CFieldSpec.toK init
        * (others.map (fun zj => CFieldSpec.toK zk - CFieldSpec.toK zj)).prod := by
  induction others generalizing init with
  | nil => simp
  | cons z zs ih =>
    rw [List.foldl_cons, ih, CFieldSpec.toK_mul, CFieldSpec.toK_sub, List.map_cons, List.prod_cons]
    ring

/-- The product `∏_{zⱼ ∈ others}(toK zk − toK zⱼ)` is nonzero when every `toK zⱼ ≠ toK zk`. -/
theorem prodG_sub_ne_zero {zk : α} {others : List α}
    (hne : ∀ zj ∈ others, CFieldSpec.toK zj ≠ CFieldSpec.toK zk) :
    (others.map (fun zj => CFieldSpec.toK zk - CFieldSpec.toK zj)).prod ≠ 0 := by
  rw [Ne, List.prod_eq_zero_iff]
  intro hy
  rw [List.mem_map] at hy
  obtain ⟨zj, hzj, hzeq⟩ := hy
  exact hne zj hzj (sub_eq_zero.mp hzeq).symm

/-- **The generic Lagrange term as a polynomial**: `toPolyG` of a single interpolation term
`cscaleG (yk/denom) (clagNumG others)`. -/
theorem toPolyG_termG (zk yk : α) (others : List α) :
    toPolyG (cscaleG (CField.div yk
        (others.foldl (fun acc zj => CField.mul acc (CField.sub zk zj)) CField.one))
        (clagNumG others))
      = Polynomial.C (CFieldSpec.toK yk
          / (others.map (fun zj => CFieldSpec.toK zk - CFieldSpec.toK zj)).prod)
        * (others.map (fun z => Polynomial.X - Polynomial.C (CFieldSpec.toK z))).prod := by
  rw [toPolyG_cscaleG, toPolyG_clagNumG, CFieldSpec.toK_div, toK_foldl_csub_mul, CFieldSpec.toK_one,
    one_mul]

/-- **Eval of a generic Lagrange term at a value** `x`. -/
theorem eval_toPolyG_termG (zk yk : α) (others : List α) (x : CFieldSpec.K α) :
    (toPolyG (cscaleG (CField.div yk
        (others.foldl (fun acc zj => CField.mul acc (CField.sub zk zj)) CField.one))
        (clagNumG others))).eval x
      = (CFieldSpec.toK yk / (others.map (fun zj => CFieldSpec.toK zk - CFieldSpec.toK zj)).prod)
        * (others.map (fun zj => x - CFieldSpec.toK zj)).prod := by
  rw [toPolyG_termG, eval_mul, eval_C]
  congr 1
  rw [eval_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro zj _
  simp [Function.comp, eval_sub, eval_X, eval_C]

/-- **Eval of a generic Lagrange term at its own node** `toK zk`: evaluates to `toK yk` (the denominator
matches the numerator product, nonzero since each `toK zⱼ ≠ toK zk`). -/
theorem eval_toPolyG_termG_at_self (zk yk : α) (others : List α)
    (hne : ∀ zj ∈ others, CFieldSpec.toK zj ≠ CFieldSpec.toK zk) :
    (toPolyG (cscaleG (CField.div yk
        (others.foldl (fun acc zj => CField.mul acc (CField.sub zk zj)) CField.one))
        (clagNumG others))).eval (CFieldSpec.toK zk) = CFieldSpec.toK yk := by
  rw [eval_toPolyG_termG, div_mul_cancel₀]
  exact prodG_sub_ne_zero hne

/-- **Eval of a generic Lagrange term at another node** `toK x` with `x ∈ others` is `0`: the numerator
product contains the vanishing factor `(toK x − toK x)`. -/
theorem eval_toPolyG_termG_at_other (zk yk x : α) (others : List α) (hx : x ∈ others) :
    (toPolyG (cscaleG (CField.div yk
        (others.foldl (fun acc zj => CField.mul acc (CField.sub zk zj)) CField.one))
        (clagNumG others))).eval (CFieldSpec.toK x) = 0 := by
  rw [eval_toPolyG_termG]
  have : (others.map (fun zj => CFieldSpec.toK x - CFieldSpec.toK zj)).prod = 0 := by
    rw [List.prod_eq_zero_iff, List.mem_map]
    exact ⟨x, hx, sub_self _⟩
  rw [this, mul_zero]

/-- The `cinterpolateG` local `term` function for a points list with abscissas `zs`. -/
private def cinterpTermG (zs : List α) (p : α × α) : CPolyG α :=
  cscaleG (CField.div p.2 ((zs.filter (fun zj => CField.isZero (CField.sub zj p.1) = false)).foldl
      (fun acc zj => CField.mul acc (CField.sub p.1 zj)) CField.one))
    (clagNumG (zs.filter (fun zj => CField.isZero (CField.sub zj p.1) = false)))

/-- **`cinterpolateG` as a normalized sum of terms** (under `toPolyG`). -/
theorem toPolyG_cinterpolateG (pts : List (α × α)) :
    toPolyG (cinterpolateG pts)
      = (pts.map (fun p => toPolyG (cinterpTermG (pts.map Prod.fst) p))).sum := by
  rw [cinterpolateG, toPolyG_cnormG, toPolyG_foldl_caddG]
  simp [cinterpTermG]

open scoped Classical in
/-- Summing `if toK p.1 = toK zk then toK p.2 else 0` over a points list whose abscissa images
`pts.map (toK ∘ fst)` are nodup picks out the unique entry `(zk, yk)` (`toK`-keyed). -/
theorem sum_ite_eq_of_nodup_toK_fst (pts : List (α × α))
    (hnodup : (pts.map (fun p => CFieldSpec.toK p.1)).Nodup)
    {zk yk : α} (hmem : (zk, yk) ∈ pts) :
    (pts.map (fun p => if CFieldSpec.toK p.1 = CFieldSpec.toK zk
        then CFieldSpec.toK p.2 else 0)).sum = CFieldSpec.toK yk := by
  induction pts with
  | nil => simp at hmem
  | cons p ps ih =>
    rw [List.map_cons, List.sum_cons]
    rw [List.map_cons, List.nodup_cons] at hnodup
    obtain ⟨hpnotin, hpsnodup⟩ := hnodup
    rcases List.mem_cons.mp hmem with hpeq | hpps
    · obtain rfl := hpeq
      rw [if_pos rfl]
      have hzero : (ps.map (fun q => if CFieldSpec.toK q.1 = CFieldSpec.toK zk
          then CFieldSpec.toK q.2 else 0)).sum = 0 := by
        apply List.sum_eq_zero
        intro w hw
        rw [List.mem_map] at hw
        obtain ⟨q, hq, rfl⟩ := hw
        rw [if_neg]
        intro hqzk
        exact hpnotin (by rw [List.mem_map]; exact ⟨q, hq, hqzk⟩)
      rw [hzero, add_zero]
    · have hp1 : CFieldSpec.toK p.1 ≠ CFieldSpec.toK zk := by
        intro h
        exact hpnotin (by rw [h, List.mem_map]; exact ⟨(zk, yk), hpps, rfl⟩)
      rw [if_neg hp1, zero_add]
      exact ih hpsnodup hpps

open scoped Classical in
/-- **`cinterpolateG` evaluation correctness**: when the abscissa images `pts.map (toK ∘ fst)` are
**distinct in `K`**, the interpolant evaluates to `toK yk` at each node `toK zk` —
`R(toK zk) = toK yk` for `(zk, yk) ∈ pts`. The generic analogue of `toPoly_cinterpolate_eval`: the
on-node term contributes `toK yk`, every off-node term vanishes. -/
theorem eval_toPolyG_cinterpolateG (pts : List (α × α))
    (hnodup : (pts.map (fun p => CFieldSpec.toK p.1)).Nodup)
    {zk yk : α} (hmem : (zk, yk) ∈ pts) :
    (toPolyG (cinterpolateG pts)).eval (CFieldSpec.toK zk) = CFieldSpec.toK yk := by
  rw [toPolyG_cinterpolateG]
  rw [show (List.map (fun p => toPolyG (cinterpTermG (pts.map Prod.fst) p)) pts).sum.eval
        (CFieldSpec.toK zk)
      = (Polynomial.evalRingHom (CFieldSpec.toK zk))
          (List.map (fun p => toPolyG (cinterpTermG (pts.map Prod.fst) p)) pts).sum from rfl,
    map_list_sum, List.map_map]
  set zs := pts.map Prod.fst with hzs
  have key : ∀ p ∈ pts,
      ((Polynomial.evalRingHom (CFieldSpec.toK zk)) ∘
          fun p => toPolyG (cinterpTermG zs p)) p
        = if CFieldSpec.toK p.1 = CFieldSpec.toK zk then CFieldSpec.toK p.2 else 0 := by
    rintro ⟨a, b⟩ hp
    simp only [Function.comp_apply, Polynomial.coe_evalRingHom, cinterpTermG]
    by_cases hak : CFieldSpec.toK a = CFieldSpec.toK zk
    · rw [if_pos hak, ← hak]
      apply eval_toPolyG_termG_at_self
      intro zj hzj
      rw [List.mem_filter] at hzj
      have hzj2 : CField.isZero (CField.sub zj a) = false := by
        have := hzj.2; simpa using this
      rw [Bool.eq_false_iff, Ne, CFieldSpec.isZero_iff, CFieldSpec.toK_sub, sub_eq_zero] at hzj2
      exact hzj2
    · rw [if_neg hak]
      apply eval_toPolyG_termG_at_other
      rw [List.mem_filter]
      refine ⟨by rw [hzs, List.mem_map]; exact ⟨(zk, yk), hmem, rfl⟩, ?_⟩
      have hgoal : CField.isZero (CField.sub zk a) = false := by
        rw [Bool.eq_false_iff, Ne, CFieldSpec.isZero_iff, CFieldSpec.toK_sub, sub_eq_zero]
        exact fun h => hak h.symm
      simpa using hgoal
  rw [List.map_congr_left key]
  exact sum_ite_eq_of_nodup_toK_fst pts hnodup hmem

/-- **Per-term degree bound** (generic): each `cinterpolateG` term has `natDegree ≤ |others|` (the
numerator is a product of `|others|` linear factors). -/
theorem natDegree_toPolyG_cinterpTermG_le (zs : List α) (p : α × α) :
    (toPolyG (cinterpTermG zs p)).natDegree
      ≤ (zs.filter (fun zj => CField.isZero (CField.sub zj p.1) = false)).length := by
  obtain ⟨a, b⟩ := p
  rw [cinterpTermG, toPolyG_termG]
  refine (natDegree_C_mul_le _ _).trans ?_
  refine (natDegree_list_prod_le _).trans ?_
  rw [List.map_map]
  refine (List.sum_le_card_nsmul _ 1 ?_).trans ?_
  · intro x hx
    rw [List.mem_map] at hx
    obtain ⟨zj, _, rfl⟩ := hx
    simp only [Function.comp_apply]
    exact natDegree_X_sub_C_le _
  · simp

/-- **`cinterpolateG` degree bound**: the interpolant has degree `< |pts|`. Each term has degree
`≤ |others| ≤ |pts| − 1` (the abscissa `zk`'s image is filtered out). The generic analogue of
`degree_toPoly_cinterpolate_lt`; the degree side of interpolation uniqueness. -/
theorem degree_toPolyG_cinterpolateG_lt (pts : List (α × α)) (hne : pts ≠ []) :
    (toPolyG (cinterpolateG pts)).degree < (pts.length : WithBot ℕ) := by
  rw [toPolyG_cinterpolateG]
  have hlen : 1 ≤ pts.length := List.length_pos_iff.mpr hne
  refine lt_of_le_of_lt (degree_list_sum_le_of_forall_degree_le _ ((pts.length : ℕ) - 1 : ℕ) ?_) ?_
  · intro p hp
    rw [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    apply Polynomial.degree_le_of_natDegree_le
    refine le_trans (natDegree_toPolyG_cinterpTermG_le (pts.map Prod.fst) q) ?_
    have hq1 : q.1 ∈ pts.map Prod.fst := List.mem_map.mpr ⟨q, hq, rfl⟩
    have hfilt : ((pts.map Prod.fst).filter
          (fun zj => CField.isZero (CField.sub zj q.1) = false)).length
        < (pts.map Prod.fst).length := by
      apply List.length_filter_lt_length_iff_exists.mpr
      refine ⟨q.1, hq1, ?_⟩
      -- the predicate `isZero (q.1 − q.1) = false` is itself `false` at `q.1`
      have hz : CField.isZero (CField.sub q.1 q.1) = true := by
        rw [CFieldSpec.isZero_iff, CFieldSpec.toK_sub, sub_self]
      simp [hz]
    rw [List.length_map] at hfilt
    omega
  · rw [Nat.cast_lt]; omega

/-- Restatement: generic interpolation evaluates to `toK yk` at each node `toK zk` when the node images
are distinct in `K`. -/
example (pts : List (α × α)) (hnodup : (pts.map (fun p => CFieldSpec.toK p.1)).Nodup)
    {zk yk : α} (hmem : (zk, yk) ∈ pts) :
    (toPolyG (cinterpolateG pts)).eval (CFieldSpec.toK zk) = CFieldSpec.toK yk :=
  eval_toPolyG_cinterpolateG pts hnodup hmem

end CPolyG

/-! ### The seed-generic abstract Rothstein–Trager resultant `R(z) = res_t(d, a − z·Dd)`

The §5.6 residue construction uses the **monomial seed** `Dd = Δd` rather than `derivative d`, so the
abstract bivariate resultant `R(z) = res_t(d, a − z·Dd) ∈ K[z]` needs to be seed-generic (the
`RationalIntegrationAlgorithms.rtResultant` fixes `Dd = derivative d`). `rtResultantSeed A D Dd` lifts
`D, A, Dd` to `(K[z])[t]` (constant `z = C z`) and eliminates `t`; `rtResultantSeed_eval` recovers the
parameter resultant `res_t(d, a − c·Dd)` at `z = c` (same formal `t`-degrees). The polynomial structure
the §5.6 residue resultant `cResidueResultantTower` realizes. -/

variable {K : Type*} [Field K]

/-- **Seed-generic abstract Rothstein–Trager resultant** `R(z) = res_t(D, A − z·Dd) ∈ K[z]`: `D, A, Dd`
lifted to `(K[z])[t]` (coefficients embedded by `C : K → K[z]`, the parameter `z` becoming the constant
`C X`), the resultant eliminating `t`. Formal `t`-degrees `(deg D, deg D)` — the §5.6 monomial seed `Δd`
has the *same* `t`-degree as `D` (`mapCoeffs d` preserves degree), unlike the d/dx seed `derivative D`
(degree `deg D − 1`), so the second formal degree is `deg D` here. The seed-generic analogue of
`rtResultant`. -/
noncomputable def rtResultantSeed (A D Dd : K[X]) : K[X] :=
  Polynomial.resultant (D.map (C : K →+* K[X]))
    (A.map (C : K →+* K[X]) - C Polynomial.X * Dd.map (C : K →+* K[X]))
    D.natDegree D.natDegree

/-- **Specialization of `rtResultantSeed`**: evaluating `R(z)` at `z = c` recovers the parameter
resultant `res_t(D, A − c·Dd)` (same formal `t`-degrees `(deg D, deg D)`). The seed-generic analogue
of `rtResultant_eval`. -/
theorem rtResultantSeed_eval (A D Dd : K[X]) (c : K) :
    (rtResultantSeed A D Dd).eval c
      = Polynomial.resultant D (A - C c * Dd) D.natDegree D.natDegree := by
  have hcomp : (Polynomial.evalRingHom c).comp (C : K →+* K[X]) = RingHom.id K := by
    ext k; simp
  show Polynomial.evalRingHom c (rtResultantSeed A D Dd) = _
  rw [rtResultantSeed, ← Polynomial.resultant_map_map]
  congr 1
  · rw [Polynomial.map_map, hcomp, Polynomial.map_id]
  · simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_map, Polynomial.map_C, hcomp,
      Polynomial.map_id]
    simp

/-- Restatement: the seed-generic abstract RT-resultant specializes at `z = c` to the parameter
resultant `res_t(D, A − c·Dd)`. -/
example (A D Dd : K[X]) (c : K) :
    (rtResultantSeed A D Dd).eval c
      = Polynomial.resultant D (A - C c * Dd) D.natDegree D.natDegree :=
  rtResultantSeed_eval A D Dd c

open Polynomial in
/-- **`natDegree` of a `K[X]`-matrix determinant** is bounded by the sum of per-column degree bounds:
if every entry of column `j` has `natDegree ≤ b j`, then `natDegree (det M) ≤ ∑ j, b j`. The `K`-generic
analogue of `natDegree_det_le_sum_col`. -/
theorem natDegree_det_le_sum_col {ι : Type*} [DecidableEq ι] [Fintype ι]
    (M : Matrix ι ι K[X]) (b : ι → ℕ) (hb : ∀ i j, (M i j).natDegree ≤ b j) :
    (M.det).natDegree ≤ ∑ j, b j := by
  rw [Matrix.det_apply]
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, ?_⟩
  intro σ _
  rw [Function.comp_apply]
  refine (natDegree_smul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  exact Finset.sum_le_sum (fun i _ => hb (σ i) i)

open Polynomial in
/-- **The `t`-coefficients of `rtResultantSeed`'s second polynomial have `z`-degree `≤ 1`**: each
`t`-coefficient of `A.map C − C z · Dd.map C` is `C (A.coeff k) − z · C (Dd.coeff k)`, degree `≤ 1`. -/
theorem natDegree_coeff_rtResultantSeed_g_le (A Dd : K[X]) (k : ℕ) :
    ((A.map (C : K →+* K[X]) - C Polynomial.X * Dd.map (C : K →+* K[X])).coeff k).natDegree ≤ 1 := by
  rw [Polynomial.coeff_sub, Polynomial.coeff_map, Polynomial.coeff_C_mul, Polynomial.coeff_map]
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · rw [Polynomial.natDegree_C]; exact Nat.zero_le 1
  · refine (Polynomial.natDegree_mul_le (p := (Polynomial.X : K[X]))
      (q := Polynomial.C (Dd.coeff k))).trans ?_
    rw [Polynomial.natDegree_X, Polynomial.natDegree_C]

open Polynomial in
/-- **`rtResultantSeed` has degree `≤ deg D` in `z`**: the Sylvester matrix of `D.map C` (constant
`z`-entries) and `A.map C − C z · Dd.map C` (degree-`≤ 1` `z`-entries) has only the `deg D` columns from
the second polynomial carrying a `z`, so its determinant has `z`-degree `≤ deg D`. The degree side of the
interpolation uniqueness (`deg D + 1` nodes determine `R(z)`). The seed-generic analogue of
`natDegree_rtResultant_le`. -/
theorem natDegree_rtResultantSeed_le (A D Dd : K[X]) :
    (rtResultantSeed A D Dd).natDegree ≤ D.natDegree := by
  rw [rtResultantSeed, resultant]
  refine le_trans (natDegree_det_le_sum_col _
    (fun j => j.addCases (fun _ => 1) (fun _ => 0)) ?_) ?_
  · intro i j
    rw [Polynomial.sylvester, Matrix.of_apply]
    refine j.addCases (fun j₁ => ?_) (fun j₁ => ?_)
    · simp only [Fin.addCases_left]
      split_ifs with h
      · exact natDegree_coeff_rtResultantSeed_g_le A Dd _
      · simp
    · simp only [Fin.addCases_right]
      split_ifs with h
      · rw [Polynomial.coeff_map, Polynomial.natDegree_C]
      · simp
  · rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      mul_one]
    rw [Finset.sum_eq_zero (fun i _ => by rw [Fin.addCases_right])]
    omega

/-! ### The §5.6 residue resultant `cResidueResultantTower` realizes `rtResultantSeed`

Composing the generic resultant correctness (step 1) with the interpolation correctness (step 2): the
computable `cResidueResultantTower Dt fuel a d` (built by evaluation + Lagrange interpolation over the
tower `ℚ(x)[z]`) reads under `toPolyG` as the abstract seed-generic RT-resultant `rtResultantSeed
(toPolyG a) (toPolyG d) (Δd)`, with `Δd = implicitDeriv (toPolyG Dt) (toPolyG d)` the monomial seed.
Both are `K[z]`-polynomials of degree `≤ deg d` agreeing at the `deg d + 1` rational nodes `0, …, deg d`,
hence equal by Lagrange uniqueness. -/

namespace CPolyG

open QFunNZ

/-- **`cAmcDd` reads as `A − C c · Δd`** under `toPolyG`: the §5.6 sampled second polynomial realizes
the abstract `a − z·Δd` (with `Δd = implicitDeriv (toPolyG Dt) (toPolyG d)`). -/
theorem toPolyG_cAmcDd (Dt a d : CPolyG QFunNZ) (c : QFunNZ) :
    toPolyG (cAmcDd Dt a d c)
      = toPolyG a - Polynomial.C (CFieldSpec.toK c)
          * Differential.implicitDeriv (toPolyG Dt) (toPolyG d) := by
  rw [cAmcDd, cDd, toPolyG_csubG, toPolyG_cscaleG, toPolyG_cmonomialDeriv]

/-- **Node-agreement** (monic `toPolyG d`): the §5.6 resultant sample `cresultantG fuel d
(cAmcDd Dt a d (ofConstNZ k))` reads under `toK` as the specialization of the abstract seed-generic
RT-resultant `rtResultantSeed (toPolyG a)(toPolyG d)(Δd)` at `toK(ofConstNZ k)`. The §5.6 analogue of
`cresultant_sample_eq_eval`: the formal degrees `(cdegG d, cdegG amc)` (used by `cresultantG`) and
`(deg d, deg d)` (used by `rtResultantSeed`) are reconciled by `resultant_add_right_deg`; the
augmentation factor `lc(d)^k = 1` since `toPolyG d` is monic. Needs `deg amc ≤ deg d`. -/
theorem cresultantG_sample_eq_eval (Dt a d : CPolyG QFunNZ) (k : ℚ)
    (hdmonic : (toPolyG d).Monic)
    (hamc : (toPolyG (cAmcDd Dt a d (ofConstNZ k))).natDegree ≤ (toPolyG d).natDegree)
    (fuel : ℕ)
    (hfuel : (cnormG d : List QFunNZ).length
      + (cnormG (cAmcDd Dt a d (ofConstNZ k)) : List QFunNZ).length + 2 ≤ fuel) :
    CFieldSpec.toK (cresultantG fuel d (cAmcDd Dt a d (ofConstNZ k)))
      = (rtResultantSeed (toPolyG a) (toPolyG d)
          (Differential.implicitDeriv (toPolyG Dt) (toPolyG d))).eval
            (CFieldSpec.toK (ofConstNZ k)) := by
  set amc := cAmcDd Dt a d (ofConstNZ k) with hamcdef
  rw [toPolyG_cresultantG fuel d amc hfuel, cdegG_eq_natDegree d, cdegG_eq_natDegree amc,
    rtResultantSeed_eval, ← toPolyG_cAmcDd Dt a d (ofConstNZ k)]
  -- reconcile the RHS's second formal degree `deg d` down to actual `deg amc` (the LHS's slot)
  obtain ⟨j, hj⟩ : ∃ j, (toPolyG d).natDegree = (toPolyG amc).natDegree + j :=
    ⟨(toPolyG d).natDegree - (toPolyG amc).natDegree, by omega⟩
  conv_rhs => rw [show (toPolyG d).natDegree = (toPolyG amc).natDegree + j from hj]
  rw [Polynomial.resultant_add_right_deg (toPolyG d) (toPolyG amc) ((toPolyG amc).natDegree + j)
    (toPolyG amc).natDegree j le_rfl, ← hj,
    show (toPolyG d).coeff (toPolyG d).natDegree = (toPolyG d).leadingCoeff from rfl,
    hdmonic.leadingCoeff, one_pow, one_mul]

/-- The tower fraction field's `Algebra ℚ` (matching the keystone instances in
`ComputableIntegrateCorrect`/`towerLogPart_*`), so `algebraMap ℚ (CFieldSpec.K QFunNZ)` resolves. -/
noncomputable local instance : Algebra ℚ (CFieldSpec.K QFunNZ) :=
  inferInstanceAs (Algebra ℚ (RatFunc ℚ))

/-- **`toK (ofConstNZ n)` is the constant rational function `n`**: the tower bridge sends the rational
constant `ofConstNZ n` to `algebraMap ℚ (RatFunc ℚ) n` (the composite `ℚ → ℚ[x] → ℚ(x)`). -/
theorem toK_ofConstNZ (n : ℚ) :
    CFieldSpec.toK (ofConstNZ n) = algebraMap ℚ (CFieldSpec.K QFunNZ) n := by
  show toQFunNZ (ofConstNZ n) = _
  rw [toQFunNZ, ofConstNZ, ofNumDen, Compute.toQFun]
  have h1 : Compute.toPoly ([n] : Compute.CPoly) = Polynomial.C n := by
    rw [Compute.toPoly_cons, Compute.toPoly_nil]; simp
  have h2 : Compute.toPoly ([1] : Compute.CPoly) = 1 := by
    rw [Compute.toPoly_cons, Compute.toPoly_nil]; simp
  rw [h1, h2, map_one, div_one]
  show (algebraMap ℚ[X] (RatFunc ℚ)) (Polynomial.C n) = algebraMap ℚ (RatFunc ℚ) n
  rw [IsScalarTower.algebraMap_eq ℚ ℚ[X] (RatFunc ℚ), RingHom.comp_apply, Polynomial.algebraMap_eq]

/-- **`toK ∘ ofConstNZ` is injective**: distinct rational constants have distinct tower images
(`algebraMap ℚ (RatFunc ℚ)` is injective). -/
theorem toK_ofConstNZ_injective :
    Function.Injective (fun n : ℚ => CFieldSpec.toK (ofConstNZ n)) := by
  intro x y hxy
  simp only [toK_ofConstNZ] at hxy
  exact FaithfulSMul.algebraMap_injective ℚ (CFieldSpec.K QFunNZ) hxy

open scoped Classical in
/-- **The §5.6 residue resultant realizes the seed-generic abstract RT-resultant** (the polynomial match,
combining steps 1–3): for monic `toPolyG d` with `deg(a − k·Δd) ≤ deg d` at each integer node and
sufficient fuel, the computable `cResidueResultantTower Dt fuel a d` reads under `toPolyG` as the abstract
`rtResultantSeed (toPolyG a)(toPolyG d)(Δd)`, `Δd = implicitDeriv (toPolyG Dt)(toPolyG d)`. Both are
`K[z]`-polynomials of degree `≤ deg d` agreeing at the `deg d + 1` rational nodes `0, …, deg d`
(`cresultantG_sample_eq_eval`), hence equal by Lagrange uniqueness
(`Lagrange.eq_of_degrees_lt_of_eval_index_eq`). -/
theorem toPolyG_cResidueResultantTower (Dt a d : CPolyG QFunNZ) (fuel : ℕ)
    (hdmonic : (toPolyG d).Monic)
    (hamc : ∀ k ∈ Finset.range (cdegG d + 1),
      (toPolyG (cAmcDd Dt a d (ofConstNZ (k : ℚ)))).natDegree ≤ (toPolyG d).natDegree)
    (hfuel : ∀ k ∈ Finset.range (cdegG d + 1),
      (cnormG d : List QFunNZ).length
        + (cnormG (cAmcDd Dt a d (ofConstNZ (k : ℚ))) : List QFunNZ).length + 2 ≤ fuel) :
    toPolyG (cResidueResultantTower Dt fuel a d)
      = rtResultantSeed (toPolyG a) (toPolyG d)
          (Differential.implicitDeriv (toPolyG Dt) (toPolyG d)) := by
  classical
  -- the abscissa list `zs`, exactly as `cResidueResultantTower`'s inner `do`-block builds it
  set zs : List ℚ := (do let k ← List.range (cdegG d + 1); pure (k : ℚ)) with hzs
  -- the node points, exactly as `cResidueResultantTower` builds them
  set pts : List (QFunNZ × QFunNZ) := zs.map (fun k : ℚ =>
    (ofConstNZ k, cresultantG fuel d (cAmcDd Dt a d (ofConstNZ k)))) with hpts
  have hcompute : cResidueResultantTower Dt fuel a d = cinterpolateG pts := rfl
  -- `zs = (range (n+1)).map (↑·)`, a clean cast-mapped range
  have hzsmap : zs = (List.range (cdegG d + 1)).map (fun k : ℕ => (k : ℚ)) := by
    rw [hzs]; exact List.flatMap_pure_eq_map _ _
  have hzsnodup : zs.Nodup := by
    rw [hzsmap]
    exact (List.nodup_range (n := cdegG d + 1)).map (fun a' b' h => by exact_mod_cast h)
  have hfst : pts.map (fun p => CFieldSpec.toK p.1)
      = zs.map (fun k : ℚ => CFieldSpec.toK (ofConstNZ k)) := by
    rw [hpts, List.map_map]; rfl
  have hnodup : (pts.map (fun p => CFieldSpec.toK p.1)).Nodup := by
    rw [hfst]
    exact hzsnodup.map toK_ofConstNZ_injective
  have hne : pts ≠ [] := by rw [hpts, hzsmap]; simp [List.range_succ]
  have hlen : pts.length = cdegG d + 1 := by
    rw [hpts, List.length_map, hzsmap, List.length_map, List.length_range]
  -- `#zs.toFinset = cdegG d + 1` (zs nodup)
  have hcard : zs.toFinset.card = cdegG d + 1 := by
    rw [List.toFinset_card_of_nodup hzsnodup, hzsmap, List.length_map, List.length_range]
  rw [hcompute]
  symm
  refine Polynomial.eq_of_degrees_lt_of_eval_index_eq (R := CFieldSpec.K QFunNZ) (ι := ℚ)
    (s := zs.toFinset) (v := fun k => CFieldSpec.toK (ofConstNZ k))
    (f := rtResultantSeed (toPolyG a) (toPolyG d)
      (Differential.implicitDeriv (toPolyG Dt) (toPolyG d)))
    (g := toPolyG (cinterpolateG pts)) ?_ ?_ ?_ ?_
  · -- `Set.InjOn` of the node map on `zs.toFinset`
    intro a' _ b' _ h
    exact toK_ofConstNZ_injective h
  · -- `degree (rtResultantSeed) < #zs.toFinset`
    rw [hcard, Nat.cast_withBot]
    refine lt_of_le_of_lt (Polynomial.degree_le_natDegree) ?_
    rw [Nat.cast_withBot, WithBot.coe_lt_coe]
    have h1 := natDegree_rtResultantSeed_le (toPolyG a) (toPolyG d)
      (Differential.implicitDeriv (toPolyG Dt) (toPolyG d))
    have h2 := cdegG_eq_natDegree d
    omega
  · -- `degree (toPolyG (cinterpolateG pts)) < #zs.toFinset`
    rw [hcard, Nat.cast_withBot]
    have := degree_toPolyG_cinterpolateG_lt pts hne
    rw [hlen] at this
    simpa [Nat.cast_withBot] using this
  · -- agree at the nodes `i ∈ zs.toFinset`, i.e. `i = (k : ℚ)` for some `k ∈ range (n+1)`
    intro i hi
    rw [List.mem_toFinset, hzsmap, List.mem_map] at hi
    obtain ⟨k, hk, rfl⟩ := hi
    rw [List.mem_range] at hk
    have hmem : (ofConstNZ (k : ℚ), cresultantG fuel d (cAmcDd Dt a d (ofConstNZ (k : ℚ)))) ∈ pts := by
      rw [hpts, hzsmap, List.mem_map]
      exact ⟨(k : ℚ), List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩, rfl⟩
    rw [eval_toPolyG_cinterpolateG pts hnodup hmem]
    -- the sample equals the abstract eval
    exact (cresultantG_sample_eq_eval Dt a d (k : ℚ) hdmonic
      (hamc k (Finset.mem_range.mpr hk)) fuel (hfuel k (Finset.mem_range.mpr hk))).symm

open scoped Classical in
/-- Restatement: the §5.6 computable residue resultant `cResidueResultantTower` reads under `toPolyG` as
the abstract seed-generic Rothstein–Trager resultant `rtResultantSeed`. -/
example (Dt a d : CPolyG QFunNZ) (fuel : ℕ) (hdmonic : (toPolyG d).Monic)
    (hamc : ∀ k ∈ Finset.range (cdegG d + 1),
      (toPolyG (cAmcDd Dt a d (ofConstNZ (k : ℚ)))).natDegree ≤ (toPolyG d).natDegree)
    (hfuel : ∀ k ∈ Finset.range (cdegG d + 1),
      (cnormG d : List QFunNZ).length
        + (cnormG (cAmcDd Dt a d (ofConstNZ (k : ℚ))) : List QFunNZ).length + 2 ≤ fuel) :
    toPolyG (cResidueResultantTower Dt fuel a d)
      = rtResultantSeed (toPolyG a) (toPolyG d)
          (Differential.implicitDeriv (toPolyG Dt) (toPolyG d)) :=
  toPolyG_cResidueResultantTower Dt a d fuel hdmonic hamc hfuel

/-! ### Step 4: discharging the residue-set enumeration `hkeysImage`/`hkeysNodup`

The concrete `cRationalResidues Dt fuel a d cands` keeps a candidate `c ∈ cands` iff
`cevalG R (ofConstNZ c) = 0` (`R = cResidueResultantTower`), i.e. iff `R(toK(ofConstNZ c)) = 0` in `K`.
By step 3 `R` reads as `rtResultantSeed`, so `R(toK(ofConstNZ c)) = res_t(d, a − c·Δd)` (the parameter
resultant), and by Mathlib's `resultant_eq_zero_iff` + the split squarefree `toPolyG d = nodal s id`
this vanishes exactly when `c` is a residue of some root `α ∈ s`. Composing this per-candidate criterion
gives the residue-set match `hkeysImage`/`hkeysNodup` — provided the candidate list `cands` is
**complete** (contains every rational residue) and **nodup** under `toK ∘ ofConstNZ`. -/

section CEvalBridge

variable {α : Type*} [CField α] [CFieldSpec α]

/-- **`cevalG` realizes polynomial evaluation under `toK`**: `toK (cevalG p c) = (toPolyG p).eval
(toK c)`. The Horner evaluation in `α` agrees with the abstract `K`-evaluation through the bridge. -/
theorem toK_cevalG (p : CPolyG α) (c : α) :
    CFieldSpec.toK (cevalG p c) = (toPolyG p).eval (CFieldSpec.toK c) := by
  rw [cevalG]
  induction p with
  | nil => simp [CFieldSpec.toK_zero]
  | cons a' as ih =>
    rw [List.foldr_cons, CFieldSpec.toK_add, CFieldSpec.toK_mul, ih, toPolyG_cons, eval_add,
      eval_C, eval_mul, eval_X]

end CEvalBridge

end CPolyG

/-! ### The resultant-vanishing residue criterion over a split squarefree denominator

For `d = nodal s id` (split squarefree, monic) over a field `K` and a seed `Dd` nonzero at every root,
the parameter resultant `res_t(d, a − c·Dd)` (with formal degrees `(deg d, deg d)`) vanishes exactly
when some root `α ∈ s` has residue `a(α)/Dd(α) = c`. This is the base-field analogue of
`residue_iff_resultant_eq_zero` (which needs `IsAlgClosed`): here the roots already live in `K` because
`d` splits over `s`. The bridge from the §5.6 residue resultant (via step 3) to the residue set. -/

open scoped Classical in
/-- **Resultant-vanishing residue criterion** (split squarefree, base field): for `d = nodal s id` and a
seed `Dd` with `Dd(α) ≠ 0` at each `α ∈ s`, given `deg(a − C c·Dd) ≤ deg d`, the resultant
`res_t(d, a − C c·Dd)` (formal degrees `(deg d, deg d)`) is `0` iff some root `α ∈ s` has residue
`a(α)/Dd(α) = c`. Reduces the `(deg d, deg d)` resultant to the default-degree one (monic `d`), turns
`resultant = 0` into non-coprimality (`resultant_eq_zero_iff`), and—since `d` splits over `s`—into a
common root `α ∈ s` of `d` and `a − C c·Dd`, which the §5.6 residue criterion
`residue_eq_iff_isRoot_sub_seed` reads as the residue equation. -/
theorem resultant_split_eq_zero_iff_residue {K : Type*} [Field K] (s : Finset K) (a Dd : K[X])
    (hDd : ∀ α ∈ s, Dd.eval α ≠ 0) (c : K)
    (hEdeg : (a - C c * Dd).natDegree ≤ (Lagrange.nodal s id).natDegree) :
    Polynomial.resultant (Lagrange.nodal s id) (a - C c * Dd)
        (Lagrange.nodal s id).natDegree (Lagrange.nodal s id).natDegree = 0
      ↔ ∃ α ∈ s, a.eval α / Dd.eval α = c := by
  classical
  set d := Lagrange.nodal s id with hd
  set E := a - C c * Dd with hE
  have hd0 : d ≠ 0 := hd ▸ Lagrange.nodal_ne_zero
  have hdmonic : d.Monic := hd ▸ Lagrange.nodal_monic
  have hdprod : d = ∏ α ∈ s, (X - C α) := by simp [hd, Lagrange.nodal_eq, id]
  have hdroots : d.roots = s.val := by rw [hdprod, roots_prod_X_sub_C]
  -- reduce the `(deg d, deg d)` resultant to the default-degree resultant (monic `d`, `deg E ≤ deg d`)
  have hred : Polynomial.resultant d E d.natDegree d.natDegree = Polynomial.resultant d E := by
    obtain ⟨j, hj⟩ : ∃ j, d.natDegree = E.natDegree + j :=
      ⟨d.natDegree - E.natDegree, by omega⟩
    conv_lhs => rw [show d.natDegree = E.natDegree + j from hj]
    rw [Polynomial.resultant_add_right_deg d E (E.natDegree + j) E.natDegree j le_rfl, ← hj,
      show d.coeff d.natDegree = d.leadingCoeff from rfl, hdmonic.leadingCoeff, one_pow, one_mul]
  rw [hred, Polynomial.resultant_eq_zero_iff, and_iff_right (Or.inl hd0)]
  -- the §5.6 residue criterion at a root (inline): `a(α)/Dd(α) = c ↔ (a − C c·Dd).IsRoot α`
  have hrescrit : ∀ α ∈ s, (a.eval α / Dd.eval α = c ↔ E.IsRoot α) := by
    intro α hαs
    rw [hE, IsRoot.def, eval_sub, eval_mul, eval_C, sub_eq_zero, div_eq_iff (hDd α hαs)]
  -- `IsCoprime d E ↔ ∀ α ∈ s, ¬ E.IsRoot α` (split `d`, each factor `X − α` prime in the PID `K[X]`)
  have hcopiff : IsCoprime d E ↔ ∀ α ∈ s, a.eval α / Dd.eval α ≠ c := by
    rw [hdprod, IsCoprime.prod_left_iff]
    refine forall_congr' fun α => ?_
    refine imp_congr_right fun hαs => ?_
    rw [(prime_X_sub_C α).coprime_iff_not_dvd, dvd_iff_isRoot, ← hrescrit α hαs]
  rw [not_iff_comm, hcopiff, not_exists]
  simp only [not_and, ne_eq]

namespace CPolyG

open QFunNZ

open scoped Classical Differential in
/-- **The per-candidate residue criterion** (composing steps 1–4a): in the split squarefree primitive
regime `toPolyG d = Lagrange.nodal s id` with the monomial seed `Δd` nonzero at every root, a candidate
`c ∈ ℚ` passes `cRationalResidues`' test — `cisZeroG [cevalG R (ofConstNZ c)] = true` for
`R = cResidueResultantTower Dt fuel a d` — **iff** `c` is a residue, i.e.
`∃ α ∈ s, A(α)/(Δd)(α) = toK(ofConstNZ c)`. The vanishing of the residue resultant at `c` reads through
step 3 (`toPolyG_cResidueResultantTower` + `rtResultantSeed_eval`) as `res_t(d, a − c·Δd) = 0`, which
`resultant_split_eq_zero_iff_residue` turns into the residue equation. -/
theorem cisZeroG_cevalG_cResidueResultantTower_iff (Dt a d : CPolyG QFunNZ) (fuel : ℕ)
    (s : Finset (CFieldSpec.K QFunNZ)) (hden : toPolyG d = Lagrange.nodal s id)
    (hDd : ∀ α ∈ s, (Differential.implicitDeriv (toPolyG Dt) (toPolyG d)).eval α ≠ 0)
    (hadeg : (toPolyG a).natDegree ≤ (toPolyG d).natDegree)
    (hδdeg : (Differential.implicitDeriv (toPolyG Dt) (toPolyG d)).natDegree
      ≤ (toPolyG d).natDegree)
    (hamc : ∀ k ∈ Finset.range (cdegG d + 1),
      (toPolyG (cAmcDd Dt a d (ofConstNZ (k : ℚ)))).natDegree ≤ (toPolyG d).natDegree)
    (hfuel : ∀ k ∈ Finset.range (cdegG d + 1),
      (cnormG d : List QFunNZ).length
        + (cnormG (cAmcDd Dt a d (ofConstNZ (k : ℚ))) : List QFunNZ).length + 2 ≤ fuel) (c : ℚ) :
    cisZeroG [cevalG (cResidueResultantTower Dt fuel a d) (ofConstNZ c)] = true
      ↔ ∃ α ∈ s, (toPolyG a).eval α
          / (Differential.implicitDeriv (toPolyG Dt) (toPolyG d)).eval α
            = CFieldSpec.toK (ofConstNZ c) := by
  classical
  set δ := Differential.implicitDeriv (toPolyG Dt) (toPolyG d) with hδ
  have hdmonic : (toPolyG d).Monic := hden ▸ Lagrange.nodal_monic
  -- `cisZeroG [cevalG R c'] = true ↔ R(toK c') = 0`
  have hzero : cisZeroG [cevalG (cResidueResultantTower Dt fuel a d) (ofConstNZ c)] = true
      ↔ (toPolyG (cResidueResultantTower Dt fuel a d)).eval (CFieldSpec.toK (ofConstNZ c)) = 0 := by
    rw [cisZeroG_iff, toPolyG_cons, toPolyG_nil, mul_zero, add_zero, ← toK_cevalG,
      Polynomial.C_eq_zero]
  rw [hzero, toPolyG_cResidueResultantTower Dt a d fuel hdmonic hamc hfuel, ← hδ,
    rtResultantSeed_eval]
  -- `deg(a − C c·δ) ≤ deg d` (from `deg a ≤ deg d` and `deg δ ≤ deg d`)
  have hEdeg : (toPolyG a - C (CFieldSpec.toK (ofConstNZ c)) * δ).natDegree
      ≤ (toPolyG d).natDegree :=
    (natDegree_sub_le _ _).trans (max_le hadeg
      ((natDegree_C_mul_le _ _).trans hδdeg))
  rw [show (toPolyG d).natDegree = (Lagrange.nodal s id).natDegree from by rw [hden]] at hEdeg
  -- specialize the split-field criterion (with `d = nodal s id`)
  rw [hden, resultant_split_eq_zero_iff_residue s (toPolyG a) δ hDd
    (CFieldSpec.toK (ofConstNZ c)) hEdeg]

/-! ### Discharging `hkeysImage`/`hkeysNodup` — the residue-set enumeration

The `cLogPart Dt fuel a d cands` keys are exactly `cRationalResidues = cands.filter (residue test)`, and
by the per-candidate criterion a candidate passes the test iff it is a residue. So the keys' `toK`-images
are exactly `{toK(ofConstNZ c) | c ∈ cands, c a residue}`. Equating this with `s.image res`
(`hkeysImage`) and proving it nodup (`hkeysNodup`) requires two transparent facts about the candidate
list: it is **complete** (every residue value `res α`, `α ∈ s`, is `toK(ofConstNZ c)` for some `c ∈ cands`)
and **`toK`-distinct** (the residue-passing candidates have distinct `toK ∘ ofConstNZ` images). These are
exactly the residue-enumeration preconditions the §5.6 capstone needs. -/

open scoped Classical Differential in
/-- **`hkeysNodup` discharged**: if the residue-passing candidates have distinct `toK ∘ ofConstNZ`
images, the `cLogPart` keys are nodup under `toK ∘ ofConstNZ`. (Immediate from `cLogPart`'s keys being
`cRationalResidues` and the candidate-distinctness hypothesis.) -/
theorem cLogPart_keys_nodup (Dt a d : CPolyG QFunNZ) (fuel : ℕ) (cands : List ℚ)
    (hdistinct : (cands.filter (fun c =>
        cisZeroG [cevalG (cResidueResultantTower Dt fuel a d) (ofConstNZ c)])).map
        (fun c => CFieldSpec.toK (ofConstNZ c)) |>.Nodup) :
    ((cLogPart Dt fuel a d cands).map (fun cv => CFieldSpec.toK (ofConstNZ cv.1))).Nodup := by
  rw [cLogPart, cRationalResidues, List.map_map]
  exact hdistinct

open scoped Classical Differential in
/-- **`hkeysImage` discharged** (the residue-set enumeration, composing step 4b): in the split squarefree
primitive regime, if the candidate list `cands` is **complete** — every residue value `res α` (`α ∈ s`)
equals `toK(ofConstNZ c)` for some `c ∈ cands` — then the `toK`-images of the `cLogPart` keys are exactly
the distinct-residue set `s.image res`. Each `cLogPart` key is a residue (per-candidate criterion
`cisZeroG_cevalG_cResidueResultantTower_iff`), and conversely each residue is reached by a candidate
(completeness). This is exactly the `hkeysImage` hypothesis of the §5.6 capstone
`cIntegrate_checkIdentity_of_residueData`. -/
theorem cLogPart_keys_image (Dt a d : CPolyG QFunNZ) (fuel : ℕ) (cands : List ℚ)
    (s : Finset (CFieldSpec.K QFunNZ)) (hden : toPolyG d = Lagrange.nodal s id)
    (hDd : ∀ α ∈ s, (Differential.implicitDeriv (toPolyG Dt) (toPolyG d)).eval α ≠ 0)
    (hadeg : (toPolyG a).natDegree ≤ (toPolyG d).natDegree)
    (hδdeg : (Differential.implicitDeriv (toPolyG Dt) (toPolyG d)).natDegree
      ≤ (toPolyG d).natDegree)
    (hamc : ∀ k ∈ Finset.range (cdegG d + 1),
      (toPolyG (cAmcDd Dt a d (ofConstNZ (k : ℚ)))).natDegree ≤ (toPolyG d).natDegree)
    (hfuel : ∀ k ∈ Finset.range (cdegG d + 1),
      (cnormG d : List QFunNZ).length
        + (cnormG (cAmcDd Dt a d (ofConstNZ (k : ℚ))) : List QFunNZ).length + 2 ≤ fuel)
    (hcompl : ∀ α ∈ s, ∃ c ∈ cands, (toPolyG a).eval α
        / (Differential.implicitDeriv (toPolyG Dt) (toPolyG d)).eval α
          = CFieldSpec.toK (ofConstNZ c)) :
    ((cLogPart Dt fuel a d cands).map (fun cv => CFieldSpec.toK (ofConstNZ cv.1))).toFinset
      = s.image (fun α => (toPolyG a).eval α
          / (Differential.implicitDeriv (toPolyG Dt) (toPolyG d)).eval α) := by
  classical
  set res : CFieldSpec.K QFunNZ → CFieldSpec.K QFunNZ := fun α => (toPolyG a).eval α
    / (Differential.implicitDeriv (toPolyG Dt) (toPolyG d)).eval α with hres
  -- the key-image set is `{toK(ofConstNZ c) | c ∈ cands ∧ test c}`
  rw [cLogPart, cRationalResidues, List.map_map]
  ext v
  rw [List.mem_toFinset, List.mem_map, Finset.mem_image]
  constructor
  · rintro ⟨c, hc, rfl⟩
    rw [List.mem_filter] at hc
    obtain ⟨_, htest⟩ := hc
    -- `c` passes the test ⟹ `c` is a residue
    obtain ⟨α, hαs, hαres⟩ := (cisZeroG_cevalG_cResidueResultantTower_iff Dt a d fuel s hden hDd
      hadeg hδdeg hamc hfuel c).mp htest
    exact ⟨α, hαs, hαres⟩
  · rintro ⟨α, hαs, rfl⟩
    -- a residue `res α` is reached by some complete candidate `c`, which then passes the test
    obtain ⟨c, hcc, hceq⟩ := hcompl α hαs
    refine ⟨c, ?_, hceq.symm⟩
    rw [List.mem_filter]
    refine ⟨hcc, ?_⟩
    -- `c` is a residue (`res α = toK(ofConstNZ c)`), so it passes the test
    exact (cisZeroG_cevalG_cResidueResultantTower_iff Dt a d fuel s hden hDd hadeg hδdeg hamc hfuel
      c).mpr ⟨α, hαs, hceq⟩

end CPolyG

end DeepWiki.SymbolicIntegration
