import DeepWiki.SymbolicIntegration.Compute.Hermite
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! # Correctness of the computable engine (`toPoly` agreement bridge)
Through the `toPoly : CPoly → ℚ[X]` bridge, the computable operations (`cdivmod`/`cgcdExt`/
`cresultant`/…) realize the `ℚ[X]` operations on all inputs, culminating in the resultant agreement
`cresultant = Polynomial.resultant`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration.Compute

/-- `cnorm [] = []`. -/
@[simp] theorem cnorm_nil : cnorm ([] : CPoly) = [] := rfl

/-- `cnorm` on a cons cell, unfolded to its defining `match`. -/
theorem cnorm_cons_eq (a : ℚ) (as : CPoly) :
    cnorm (a :: as)
      = (match cnorm as with | [] => if a = 0 then [] else [a] | r => a :: r) := by
  show CPolyG.cnormG (a :: as)
      = (match CPolyG.cnormG as with | [] => if a = 0 then [] else [a] | r => a :: r)
  rw [CPolyG.cnormG_cons_eq]
  cases CPolyG.cnormG as with
  | nil => show (if (decide (a = 0) = true) then _ else _) = _; by_cases ha : a = 0 <;> simp [ha]
  | cons b bs => rfl

/-- `cnorm` is idempotent: stripping trailing zeros twice is the same as once. -/
@[simp] theorem cnorm_idem (p : CPoly) : cnorm (cnorm p) = cnorm p := by
  induction p with
  | nil => rfl
  | cons a as ih =>
    rw [cnorm_cons_eq]
    cases h : cnorm as with
    | nil => by_cases ha : a = 0 <;> simp [cnorm_cons_eq, ha]
    | cons b bs =>
      rw [h] at ih
      simp only [cnorm_cons_eq, ih]

/-- `toPoly (cnorm p) = toPoly p`: stripping trailing zeros does not change the polynomial. -/
@[simp] theorem toPoly_cnorm (p : CPoly) : toPoly (cnorm p) = toPoly p := by
  induction p with
  | nil => rfl
  | cons a as ih =>
    rw [cnorm_cons_eq]
    cases h : cnorm as with
    | nil =>
      rw [h] at ih
      simp only [toPoly_nil] at ih
      have has : toPoly as = 0 := ih.symm
      by_cases ha : a = 0 <;> simp [ha, toPoly_cons, has]
    | cons b bs =>
      rw [h] at ih
      simp only [toPoly_cons, ih]

/-- Euclidean-division identity through `toPoly` (for `q` normalized and nonzero):
`toPoly p = toPoly (quotient) · toPoly q + toPoly (remainder)`. -/
theorem toPoly_cdivmod (fuel : ℕ) (p q : CPoly) (hqn : cnorm q = q) (hq0 : q ≠ []) :
    toPoly p
      = toPoly (cdivmod fuel p q).1 * toPoly q + toPoly (cdivmod fuel p q).2 := by
  induction fuel generalizing p with
  | zero => simp [cdivmod, toPoly_cnorm]
  | succ fuel ih =>
    have hcz : cisZero q = false := by
      simp only [cisZero, hqn, beq_eq_false_iff_ne, ne_eq]
      exact hq0
    rw [cdivmod]
    simp only [hqn, hcz, Bool.false_eq_true, if_false]
    by_cases hlen : (cnorm p).length < q.length
    · simp [hlen, toPoly_cnorm]
    · simp only [hlen, if_false]
      rcases hqr : cdivmod fuel (cnorm (csub (cnorm p)
          (cmul (cshift ((cnorm p).length - q.length) [clead (cnorm p) / clead q]) q))) q
        with ⟨quo, rem⟩
      have hih := ih (cnorm (csub (cnorm p)
          (cmul (cshift ((cnorm p).length - q.length) [clead (cnorm p) / clead q]) q)))
      rw [hqr] at hih
      simp only [toPoly_cadd, toPoly_cnorm, toPoly_csub, toPoly_cmul] at hih ⊢
      linear_combination hih

/-- `cdivmod fuel p q = cdivmod fuel p (cnorm q)`: `cdivmod` normalizes its divisor. -/
theorem cdivmod_cnorm_right (fuel : ℕ) (p q : CPoly) :
    cdivmod fuel p q = cdivmod fuel p (cnorm q) := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp only [cdivmod, cnorm_idem]

/-- Euclidean-division identity through `toPoly` for an arbitrary nonzero divisor (`cnorm q ≠ []`):
`toPoly p = toPoly (quotient) · toPoly q + toPoly (remainder)`. -/
theorem toPoly_cdivmod' (fuel : ℕ) (p q : CPoly) (hq0 : cnorm q ≠ []) :
    toPoly p
      = toPoly (cdivmod fuel p q).1 * toPoly q + toPoly (cdivmod fuel p q).2 := by
  rw [cdivmod_cnorm_right]
  simpa [toPoly_cnorm] using toPoly_cdivmod fuel p (cnorm q) (cnorm_idem q) hq0

/-- Bézout identity through `toPoly` for `cgcdExt`: with `(g, s, t) = cgcdExt fuel a b`,
`toPoly s · toPoly a + toPoly t · toPoly b = toPoly g`. -/
theorem toPoly_cgcdExt (fuel : ℕ) (a b : CPoly) :
    toPoly (cgcdExt fuel a b).2.1 * toPoly a + toPoly (cgcdExt fuel a b).2.2 * toPoly b
      = toPoly (cgcdExt fuel a b).1 := by
  induction fuel generalizing a b with
  | zero => simp [cgcdExt, toPoly_cnorm]
  | succ fuel ih =>
    rw [cgcdExt]
    cases hb : cisZero b with
    | true => simp [toPoly_cnorm]
    | false =>
      simp only [Bool.false_eq_true, if_false]
      rcases hqr : cdivmod (fuel + 1) a b with ⟨q, r⟩
      rcases hg : cgcdExt fuel b r with ⟨g, s, t⟩
      have hdiv : toPoly a = toPoly q * toPoly b + toPoly r := by
        have h := toPoly_cdivmod' (fuel + 1) a b (by simpa [cisZero] using hb)
        rw [hqr] at h; exact h
      have hih := ih b r
      rw [hg] at hih
      simp only [toPoly_csub, toPoly_cmul]
      linear_combination hih + toPoly t * hdiv

/-- The `LogToAtan` cofactor invariant `B·D − A·C = G` in `ℚ[X]`: for
`(G, D, C) = cgcdExt fuel B (−A)`, `toPoly B · toPoly D − toPoly A · toPoly C = toPoly G`. -/
theorem logToAtan_cofactor_bezout (fuel : ℕ) (A B : CPoly) :
    toPoly B * toPoly (cgcdExt fuel B (cneg A)).2.1
        - toPoly A * toPoly (cgcdExt fuel B (cneg A)).2.2
      = toPoly (cgcdExt fuel B (cneg A)).1 := by
  have h := toPoly_cgcdExt fuel B (cneg A)
  rw [toPoly_cneg] at h
  linear_combination h

/-! ### The bivariate bridge `toBPoly : BPoly → ℚ[t][x]` and its homomorphism lemmas
Reads a `BPoly = List CPoly` as a `Polynomial (Polynomial ℚ)` in `x`, each `x`-coefficient via
`toPoly`; the homomorphism lemmas reduce the `BPoly` algebra to `(ℚ[X])[X]` operations. -/

/-- Bivariate bridge `toBPoly : BPoly → (ℚ[X])[X]`: read a `BPoly` as a `Polynomial (Polynomial ℚ)`
in Horner form in `x`, each `x`-coefficient embedded via `toPoly`. -/
noncomputable def toBPoly : BPoly → Polynomial (Polynomial ℚ)
  | [] => 0
  | a :: p => Polynomial.C (toPoly a) + Polynomial.X * toBPoly p

@[simp] theorem toBPoly_nil : toBPoly ([] : BPoly) = 0 := rfl

@[simp] theorem toBPoly_cons (a : CPoly) (p : BPoly) :
    toBPoly (a :: p) = Polynomial.C (toPoly a) + Polynomial.X * toBPoly p := rfl

/-- `toBPoly` is additive: `badd` realizes `(ℚ[X])[X]` addition. -/
theorem toBPoly_badd (p q : BPoly) : toBPoly (badd p q) = toBPoly p + toBPoly q := by
  induction p generalizing q with
  | nil => simp [badd]
  | cons a as ih =>
    cases q with
    | nil => simp [badd]
    | cons b bs =>
      simp only [badd, toBPoly_cons, ih, toPoly_cadd, map_add]
      ring

/-- `bneg` realizes `(ℚ[X])[X]` negation through `toBPoly`. -/
theorem toBPoly_bneg (p : BPoly) : toBPoly (bneg p) = - toBPoly p := by
  induction p with
  | nil => simp [bneg]
  | cons a as ih =>
    show toBPoly (cneg a :: bneg as) = _
    simp only [toBPoly_cons, toPoly_cneg, map_neg, ih]
    ring

/-- `bsub` realizes `(ℚ[X])[X]` subtraction through `toBPoly`. -/
theorem toBPoly_bsub (p q : BPoly) : toBPoly (bsub p q) = toBPoly p - toBPoly q := by
  simp [bsub, toBPoly_badd, toBPoly_bneg, sub_eq_add_neg]

/-- `bscaleC c p` realizes scaling by a `ℚ[t]` coefficient: `C (toPoly c) · toBPoly p`. -/
theorem toBPoly_bscaleC (c : CPoly) (p : BPoly) :
    toBPoly (bscaleC c p) = Polynomial.C (toPoly c) * toBPoly p := by
  induction p with
  | nil => simp [bscaleC]
  | cons a as ih =>
    show toBPoly (cmul c a :: bscaleC c as) = _
    simp only [toBPoly_cons, toPoly_cmul, map_mul, ih]
    ring

/-- `bshift k p` realizes the `x`-shift: `Xᵏ · toBPoly p`. -/
theorem toBPoly_bshift (k : ℕ) (p : BPoly) :
    toBPoly (bshift k p) = Polynomial.X ^ k * toBPoly p := by
  induction k with
  | zero => simp [bshift]
  | succ n ih =>
    show toBPoly ([] :: bshift n p) = _
    simp only [toBPoly_cons, toPoly_nil, map_zero, ih]
    ring

/-- `toBPoly` is multiplicative: `bmul` realizes `(ℚ[X])[X]` multiplication. -/
theorem toBPoly_bmul (p q : BPoly) : toBPoly (bmul p q) = toBPoly p * toBPoly q := by
  induction p with
  | nil => simp [bmul]
  | cons a as ih =>
    show toBPoly (badd (bscaleC a q) ([] :: bmul as q)) = _
    simp only [toBPoly_badd, toBPoly_bscaleC, toBPoly_cons, toPoly_nil, map_zero, ih]
    ring

/-- `bnorm [] = []`. -/
@[simp] theorem bnorm_nil : bnorm ([] : BPoly) = [] := rfl

/-- `bnorm` on a cons cell, unfolded to its defining `match`. -/
theorem bnorm_cons_eq (a : CPoly) (as : BPoly) :
    bnorm (a :: as)
      = (match bnorm as with
          | [] => if cisZero (cnorm a) then [] else [cnorm a]
          | r => cnorm a :: r) := rfl

/-- `bnorm` is idempotent. -/
@[simp] theorem bnorm_idem (p : BPoly) : bnorm (bnorm p) = bnorm p := by
  induction p with
  | nil => rfl
  | cons a as ih =>
    rw [bnorm_cons_eq]
    cases h : bnorm as with
    | nil => cases ha : cisZero (cnorm a) <;> simp [bnorm_cons_eq, cnorm_idem, ha]
    | cons b bs =>
      rw [h] at ih
      simp only [bnorm_cons_eq, cnorm_idem, ih]

/-- `bpsremainder fuel p q = bpsremainder fuel p (bnorm q)`: `bpsremainder` normalizes its divisor. -/
theorem bpsremainder_bnorm_right (fuel : ℕ) (p q : BPoly) :
    bpsremainder fuel p q = bpsremainder fuel p (bnorm q) := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp only [bpsremainder, bnorm_idem]

/-- `toBPoly (bnorm p) = toBPoly p`: normalization does not change the polynomial. -/
@[simp] theorem toBPoly_bnorm (p : BPoly) : toBPoly (bnorm p) = toBPoly p := by
  induction p with
  | nil => rfl
  | cons a as ih =>
    rw [bnorm_cons_eq]
    cases h : bnorm as with
    | nil =>
      rw [h] at ih
      simp only [toBPoly_nil] at ih
      have has : toBPoly as = 0 := ih.symm
      cases ha : cisZero (cnorm a) with
      | true =>
        have hpa : toPoly a = 0 := by
          have hca : cnorm a = [] := by simpa [cisZero, cnorm_idem] using ha
          rw [← toPoly_cnorm, hca, toPoly_nil]
        simp [toBPoly_cons, hpa, has]
      | false => simp [toBPoly_cons, toPoly_cnorm, has]
    | cons b bs =>
      rw [h] at ih
      simp only [toBPoly_cons, toPoly_cnorm, ih]

/-- `toBPoly [[1]] = 1`: the `BPoly` constant `1`. -/
@[simp] theorem toBPoly_one : toBPoly ([[1]] : BPoly) = 1 := by
  simp [toBPoly_cons, toPoly_cons]

/-- Pseudo-division identity through `toBPoly`: there exist a multiplier `c ∈ ℚ[t]` and quotient `s`
with `C (toPoly c) · toBPoly p = toBPoly s · toBPoly q + toBPoly (bpsremainder fuel p q)`. -/
theorem toBPoly_bpsremainder (fuel : ℕ) (p q : BPoly) :
    ∃ (s : BPoly) (c : CPoly),
      Polynomial.C (toPoly c) * toBPoly p
        = toBPoly s * toBPoly q + toBPoly (bpsremainder fuel p q) := by
  induction fuel generalizing p with
  | zero => exact ⟨[], [1], by simp [bpsremainder, toBPoly_bnorm, toPoly_cons]⟩
  | succ fuel ih =>
    simp only [bpsremainder]
    split_ifs with hq hlen
    · exact ⟨[], [1], by simp [toBPoly_bnorm, toPoly_cons]⟩
    · exact ⟨[], [1], by simp [toBPoly_bnorm, toPoly_cons]⟩
    · obtain ⟨s', c', hsc⟩ := ih (bnorm (bsub (bscaleC (blc (bnorm q)) (bnorm p))
        (bscaleC (blc (bnorm p)) (bshift ((bnorm p).length - (bnorm q).length) (bnorm q)))))
      have hp' : toBPoly (bnorm (bsub (bscaleC (blc (bnorm q)) (bnorm p))
          (bscaleC (blc (bnorm p)) (bshift ((bnorm p).length - (bnorm q).length) (bnorm q)))))
          = Polynomial.C (toPoly (blc (bnorm q))) * toBPoly p
            - Polynomial.C (toPoly (blc (bnorm p)))
              * Polynomial.X ^ ((bnorm p).length - (bnorm q).length) * toBPoly q := by
        rw [toBPoly_bnorm, toBPoly_bsub, toBPoly_bscaleC, toBPoly_bscaleC, toBPoly_bshift,
          toBPoly_bnorm, toBPoly_bnorm]
        ring
      rw [hp', bpsremainder_bnorm_right] at hsc
      refine ⟨badd s' (bscaleC (cmul c' (blc (bnorm p)))
          (bshift ((bnorm p).length - (bnorm q).length) [[1]])),
          cmul c' (blc (bnorm q)), ?_⟩
      rw [toBPoly_badd, toBPoly_bscaleC, toBPoly_bshift, toBPoly_one, toPoly_cmul, map_mul,
        toPoly_cmul, map_mul]
      linear_combination hsc

/-- Diophantine/Bézout solver correctness through `toPoly`: when `gcd(p, q)` is a nonzero constant,
`cdiophantine fuel p q rhs = (B, C)` satisfies `toPoly B · toPoly p + toPoly C · toPoly q = toPoly rhs`. -/
theorem toPoly_cdiophantine (fuel : ℕ) (p q rhs : CPoly) (hq : cnorm q ≠ [])
    (hg : toPoly (cgcdExt fuel p q).1 = Polynomial.C (clead (cgcdExt fuel p q).1))
    (hgc : clead (cgcdExt fuel p q).1 ≠ 0) :
    toPoly (cdiophantine fuel p q rhs).1 * toPoly p
        + toPoly (cdiophantine fuel p q rhs).2 * toPoly q
      = toPoly rhs := by
  rcases hgst : cgcdExt fuel p q with ⟨g, s, t⟩
  rw [hgst] at hg hgc
  have hbez : toPoly s * toPoly p + toPoly t * toPoly q = toPoly g := by
    have h := toPoly_cgcdExt fuel p q; rw [hgst] at h; exact h
  simp only [cdiophantine, hgst]
  rcases hqB : cdivmod fuel (cscale (clead g)⁻¹ (cmul rhs s)) q with ⟨quo, B⟩
  have hdiv : toPoly (cscale (clead g)⁻¹ (cmul rhs s)) = toPoly quo * toPoly q + toPoly B := by
    have h := toPoly_cdivmod' fuel (cscale (clead g)⁻¹ (cmul rhs s)) q hq
    rw [hqB] at h; exact h
  simp only [toPoly_cnorm, toPoly_cadd, toPoly_cmul, toPoly_cscale] at hdiv ⊢
  have hinv : Polynomial.C (clead g)⁻¹ * toPoly g = 1 := by
    rw [hg, ← map_mul, inv_mul_cancel₀ hgc, map_one]
  linear_combination (-toPoly p) * hdiv
    + (Polynomial.C (clead g)⁻¹ * toPoly rhs) * hbez + toPoly rhs * hinv

/-- `cgcdExt`'s gcd is greatest among common divisors: any `d` dividing both `toPoly a` and
`toPoly b` divides `toPoly (cgcdExt fuel a b).1`. -/
theorem toPoly_dvd_cgcdExt {d : ℚ[X]} (fuel : ℕ) (a b : CPoly)
    (ha : d ∣ toPoly a) (hb : d ∣ toPoly b) :
    d ∣ toPoly (cgcdExt fuel a b).1 := by
  rw [← toPoly_cgcdExt fuel a b]
  exact dvd_add (ha.mul_left _) (hb.mul_left _)

/-- Termination predicate for `cgcdExt`: the remainder sequence reaches `0` within `fuel`. -/
def cgcdTerminates : ℕ → CPoly → CPoly → Prop
  | 0, _, b => cisZero b = true
  | fuel + 1, a, b => cisZero b = true ∨ cgcdTerminates fuel b (cmod (fuel + 1) a b)

/-- `cgcdExt`'s gcd divides both inputs when the algorithm terminates: under `cgcdTerminates`,
`toPoly (cgcdExt fuel a b).1` divides `toPoly a` and `toPoly b`. -/
theorem toPoly_cgcdExt_dvd : ∀ (fuel : ℕ) (a b : CPoly), cgcdTerminates fuel a b →
    toPoly (cgcdExt fuel a b).1 ∣ toPoly a ∧ toPoly (cgcdExt fuel a b).1 ∣ toPoly b := by
  intro fuel
  induction fuel with
  | zero =>
    intro a b hterm
    simp only [cgcdTerminates] at hterm
    rw [cgcdExt]
    have hb0 : toPoly b = 0 := by
      have hcb : cnorm b = [] := by simpa [cisZero] using hterm
      rw [← toPoly_cnorm, hcb, toPoly_nil]
    exact ⟨by simp [toPoly_cnorm], by simp [hb0]⟩
  | succ fuel ih =>
    intro a b hterm
    rw [cgcdExt]
    cases hb : cisZero b with
    | true =>
      have hb0 : toPoly b = 0 := by
        have hcb : cnorm b = [] := by simpa [cisZero] using hb
        rw [← toPoly_cnorm, hcb, toPoly_nil]
      exact ⟨by simp [toPoly_cnorm], by simp [hb0]⟩
    | false =>
      simp only [Bool.false_eq_true, if_false]
      rcases hqr : cdivmod (fuel + 1) a b with ⟨q, r⟩
      rcases hg : cgcdExt fuel b r with ⟨g, s, t⟩
      have hterm' : cgcdTerminates fuel b r := by
        rw [cgcdTerminates] at hterm
        rcases hterm with h | h
        · rw [hb] at h; simp at h
        · have hcm : cmod (fuel + 1) a b = r := by rw [cmod, hqr]
          rwa [hcm] at h
      obtain ⟨hgb, hgr⟩ := ih b r hterm'
      rw [hg] at hgb hgr
      have hdiv : toPoly a = toPoly q * toPoly b + toPoly r := by
        have h := toPoly_cdivmod' (fuel + 1) a b (by simpa [cisZero] using hb)
        rw [hqr] at h; exact h
      refine ⟨?_, hgb⟩
      rw [hdiv]
      exact dvd_add (hgb.mul_left _) hgr

/-- Rational-function read of a `QFun` into `RatFunc ℚ`: `(num, den) ↦ toPoly num / toPoly den`. -/
noncomputable def toQFun (x : QFun) : RatFunc ℚ :=
  algebraMap ℚ[X] (RatFunc ℚ) (toPoly x.1) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly x.2)

/-- `qadd` realizes rational-function addition (for nonzero denominators):
`toQFun (qadd x y) = toQFun x + toQFun y`. -/
theorem toQFun_qadd (x y : QFun) (hb : toPoly x.2 ≠ 0) (hd : toPoly y.2 ≠ 0) :
    toQFun (qadd x y) = toQFun x + toQFun y := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  have hinj := IsFractionRing.injective ℚ[X] (RatFunc ℚ)
  have hb' : algebraMap ℚ[X] (RatFunc ℚ) (toPoly b) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr hb
  have hd' : algebraMap ℚ[X] (RatFunc ℚ) (toPoly d) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr hd
  simp only [toQFun, qadd, toPoly_cadd, toPoly_cmul, map_add, map_mul]
  rw [div_add_div _ _ hb' hd']
  ring

/-! ### Degree / leading coefficient bridge
`(toPoly p).coeff i = p.getD i 0`, from which `cdeg`/`clead` are the `natDegree`/`leadingCoeff`. -/

/-- Coefficient read: `(toPoly p).coeff i = p.getD i 0`. -/
theorem toPoly_coeff (p : CPoly) (i : ℕ) : (toPoly p).coeff i = p.getD i 0 := by
  induction p generalizing i with
  | nil => simp
  | cons a as ih =>
    rw [toPoly_cons]
    cases i with
    | zero => simp [coeff_C]
    | succ n => simp [coeff_X_mul, ih]

/-- Degree bound: `natDegree (toPoly p) ≤ (cnorm p).length − 1`. -/
theorem natDegree_toPoly_le (p : CPoly) : (toPoly p).natDegree ≤ (cnorm p).length - 1 := by
  rw [← toPoly_cnorm]
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro m hm
  rw [toPoly_coeff, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

/-- `cnorm` has no trailing zero: `(cnorm p).getLast? ≠ some 0`. -/
theorem cnorm_getLast?_ne_some_zero (p : CPoly) : (cnorm p).getLast? ≠ some 0 := by
  induction p with
  | nil => simp
  | cons a as ih =>
    rw [cnorm_cons_eq]
    cases h : cnorm as with
    | nil =>
      by_cases ha : a = 0 <;> simp [ha]
    | cons b bs =>
      rw [h] at ih
      rw [List.getLast?_cons_cons]
      exact ih

/-- For a normalized nonzero `CPoly`, the leading coefficient `clead` is nonzero. -/
theorem clead_ne_zero {p : CPoly} (h : cnorm p ≠ []) : clead p ≠ 0 := by
  show CPolyG.cleadG p ≠ 0
  rcases hl : (CPolyG.cnormG p).getLast? with _ | v
  · exact absurd (List.getLast?_eq_none_iff.mp hl) h
  · simp only [CPolyG.cleadG, hl, Option.getD_some]
    rintro rfl
    exact cnorm_getLast?_ne_some_zero p hl

/-- `clead p = (toPoly p).coeff (cdeg p)`: the leading coefficient sits at the top index. -/
theorem clead_eq_coeff (p : CPoly) : clead p = (toPoly p).coeff (cdeg p) := by
  show CPolyG.cleadG p = _
  rw [CPolyG.cleadG, cdeg, ← toPoly_cnorm, toPoly_coeff, List.getD_eq_getElem?_getD,
    ← List.getLast?_eq_getElem?]
  rfl

/-- `cdeg p = (toPoly p).natDegree`: `cdeg` is the honest `natDegree`. -/
theorem cdeg_eq_natDegree (p : CPoly) : cdeg p = (toPoly p).natDegree := by
  rcases eq_or_ne (cnorm p) [] with h | h
  · have h0 : toPoly p = 0 := by rw [← toPoly_cnorm, h, toPoly_nil]
    rw [cdeg, h, h0]; simp
  · refine le_antisymm ?_ (natDegree_toPoly_le p)
    apply Polynomial.le_natDegree_of_ne_zero
    rw [← clead_eq_coeff]
    exact clead_ne_zero h

/-- `clead p = (toPoly p).leadingCoeff`: `clead` is the honest `leadingCoeff`. -/
theorem clead_eq_leadingCoeff (p : CPoly) : clead p = (toPoly p).leadingCoeff := by
  rw [Polynomial.leadingCoeff, ← cdeg_eq_natDegree, ← clead_eq_coeff]

/-- One Euclidean-division step strictly drops the degree in `ℚ[X]`:
`(P - C (lcP/lcQ)·X^(degP−degQ)·Q).degree < P.degree`. -/
theorem degree_reduce_step_lt {P Q : ℚ[X]} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree ≤ P.natDegree) :
    (P - C (P.leadingCoeff / Q.leadingCoeff)
        * X ^ (P.natDegree - Q.natDegree) * Q).degree < P.degree := by
  have hQlc : Q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ
  have hPlc : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  have hc0 : P.leadingCoeff / Q.leadingCoeff ≠ 0 := div_ne_zero hPlc hQlc
  have hCc : (C (P.leadingCoeff / Q.leadingCoeff)) ≠ 0 := by
    rwa [Ne, Polynomial.C_eq_zero]
  have hXk : (X ^ (P.natDegree - Q.natDegree) : ℚ[X]) ≠ 0 := pow_ne_zero _ Polynomial.X_ne_zero
  set T := C (P.leadingCoeff / Q.leadingCoeff) * X ^ (P.natDegree - Q.natDegree) * Q with hT
  have hT0 : T ≠ 0 := mul_ne_zero (mul_ne_zero hCc hXk) hQ
  have hTnd : T.natDegree = P.natDegree := by
    rw [hT, Polynomial.natDegree_mul (mul_ne_zero hCc hXk) hQ,
      Polynomial.natDegree_mul hCc hXk, Polynomial.natDegree_C, Polynomial.natDegree_X_pow]
    omega
  have hTlc : T.leadingCoeff = P.leadingCoeff := by
    rw [hT, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      Polynomial.leadingCoeff_X_pow, mul_one, div_mul_cancel₀ _ hQlc]
  exact Polynomial.degree_sub_lt
    (by rw [Polynomial.degree_eq_natDegree hP, Polynomial.degree_eq_natDegree hT0, hTnd]) hP
    hTlc.symm

/-- `cnorm p = []` iff `toPoly p = 0` (the list normalizes to empty exactly for the zero polynomial). -/
theorem cnorm_eq_nil_iff (p : CPoly) : cnorm p = [] ↔ toPoly p = 0 := by
  constructor
  · intro h; rw [← toPoly_cnorm, h, toPoly_nil]
  · intro h
    by_contra hne
    have hcl := clead_ne_zero hne
    rw [clead_eq_leadingCoeff, h, Polynomial.leadingCoeff_zero] at hcl
    exact hcl rfl

/-- For a nonzero polynomial, the normalized list length is `natDegree + 1`. -/
theorem length_cnorm_of_ne (p : CPoly) (h : cnorm p ≠ []) :
    (cnorm p).length = (toPoly p).natDegree + 1 := by
  have hd := cdeg_eq_natDegree p
  rw [cdeg] at hd
  have hlen : 1 ≤ (cnorm p).length := List.length_pos_iff.mpr h
  omega

/-- One `cdivmod` step strictly shortens the normalized list: the remainder-loop replacement has
strictly smaller normalized length than `p`. -/
theorem step_length_lt (p q : CPoly) (hp : cnorm p ≠ []) (hq : cnorm q ≠ [])
    (hpq : (cnorm q).length ≤ (cnorm p).length) :
    (cnorm (csub (cnorm p)
        (cmul (cshift ((cnorm p).length - (cnorm q).length) [clead p / clead q])
          (cnorm q)))).length < (cnorm p).length := by
  have hP : toPoly p ≠ 0 := fun h => hp ((cnorm_eq_nil_iff p).mpr h)
  have hQ : toPoly q ≠ 0 := fun h => hq ((cnorm_eq_nil_iff q).mpr h)
  have hk : (cnorm p).length - (cnorm q).length
      = (toPoly p).natDegree - (toPoly q).natDegree := by
    rw [length_cnorm_of_ne p hp, length_cnorm_of_ne q hq]; omega
  have hc : clead p / clead q = (toPoly p).leadingCoeff / (toPoly q).leadingCoeff := by
    rw [clead_eq_leadingCoeff, clead_eq_leadingCoeff]
  set step := csub (cnorm p)
    (cmul (cshift ((cnorm p).length - (cnorm q).length) [clead p / clead q]) (cnorm q))
    with hstepdef
  have hstep : toPoly step
      = toPoly p - C ((toPoly p).leadingCoeff / (toPoly q).leadingCoeff)
          * X ^ ((toPoly p).natDegree - (toPoly q).natDegree) * toPoly q := by
    rw [hstepdef, toPoly_csub, toPoly_cnorm, toPoly_cmul, toPoly_cshift, toPoly_cnorm, hk, hc]
    simp only [toPoly_cons, toPoly_nil, mul_zero, add_zero]
    ring
  have hpq' : (toPoly q).natDegree ≤ (toPoly p).natDegree := by
    have e1 := length_cnorm_of_ne p hp
    have e2 := length_cnorm_of_ne q hq
    omega
  have hdeg : (toPoly step).degree < (toPoly p).degree := by
    rw [hstep]; exact degree_reduce_step_lt hP hQ hpq'
  by_cases hs0 : toPoly step = 0
  · rw [(cnorm_eq_nil_iff _).mpr hs0, List.length_nil]
    exact List.length_pos_iff.mpr hp
  · have hne : cnorm step ≠ [] := fun h => hs0 ((cnorm_eq_nil_iff _).mp h)
    have hlt := Polynomial.natDegree_lt_natDegree hs0 hdeg
    rw [length_cnorm_of_ne _ hne, length_cnorm_of_ne p hp]
    omega

/-- `clead` is invariant under `cnorm`: `clead (cnorm p) = clead p`. -/
theorem clead_cnorm (p : CPoly) : clead (cnorm p) = clead p := by
  show CPolyG.cleadG (CPolyG.cnormG p) = CPolyG.cleadG p
  simp only [CPolyG.cleadG, CPolyG.cnormG_idem]

/-- `cisZero` is invariant under `cnorm`. -/
theorem cisZero_cnorm (q : CPoly) : cisZero (cnorm q) = cisZero q := by
  simp only [cisZero, cnorm_idem]

/-- Remainder degree bound: with enough fuel and a nonzero divisor, `cmod fuel p q` has strictly
smaller normalized length than `q`. -/
theorem cmod_length_lt (fuel : ℕ) (p q : CPoly) (hq : cnorm q ≠ [])
    (hfuel : (cnorm p).length ≤ fuel) :
    (cnorm (cmod fuel p q)).length < (cnorm q).length := by
  induction fuel generalizing p with
  | zero =>
    have hp0 : cnorm p = [] := List.length_eq_zero_iff.mp (by omega)
    have h2 : cmod 0 p q = [] := by simp [cmod, cdivmod, hp0]
    rw [h2]; simpa using List.length_pos_iff.mpr hq
  | succ fuel ih =>
    have hcz : cisZero (cnorm q) = false := by rw [cisZero_cnorm]; simpa [cisZero] using hq
    by_cases hlen : (cnorm p).length < (cnorm q).length
    · have h2 : cmod (fuel + 1) p q = cnorm p := by
        rw [cmod, cdivmod]
        simp only [hcz, Bool.false_eq_true, if_false, if_pos hlen]
      rw [h2, cnorm_idem]; exact hlen
    · have hp : cnorm p ≠ [] := by
        rintro h
        rw [h, List.length_nil] at hlen
        exact hlen (List.length_pos_iff.mpr hq)
      have hstep := step_length_lt p q hp hq (by omega)
      have key : cmod (fuel + 1) p q
          = cmod fuel (cnorm (csub (cnorm p)
              (cmul (cshift ((cnorm p).length - (cnorm q).length) [clead p / clead q])
                (cnorm q)))) q := by
        rw [cmod, cdivmod]
        simp only [hcz, Bool.false_eq_true, if_false, if_neg hlen, clead_cnorm, cmod,
          ← cdivmod_cnorm_right]
      rw [key]
      apply ih
      rw [cnorm_idem]
      omega

/-- Euclidean-gcd descent terminates for sufficient fuel: when `fuel` bounds the first argument's
normalized length and strictly bounds the second's, `cgcdTerminates fuel a b` holds. -/
theorem cgcdTerminates_of_fuel :
    ∀ (fuel : ℕ) (a b : CPoly), (cnorm a).length ≤ fuel → (cnorm b).length < fuel →
      cgcdTerminates fuel a b := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ hb; omega
  | succ fuel ih =>
    intro a b ha hb
    rw [cgcdTerminates]
    by_cases hbz : cisZero b = true
    · exact Or.inl hbz
    · refine Or.inr ?_
      have hbne : cnorm b ≠ [] := by simpa [cisZero] using hbz
      -- the remainder strictly shortens below `(cnorm b).length`
      have hlt : (cnorm (cmod (fuel + 1) a b)).length < (cnorm b).length :=
        cmod_length_lt (fuel + 1) a b hbne ha
      -- new pair `(b, cmod …)`: first slot `≤ fuel`, second slot `< fuel`
      exact ih b (cmod (fuel + 1) a b) (by omega) (by omega)

/-- Symmetric entry to `cgcdTerminates_of_fuel`: if `fuel` strictly bounds both normalized argument
lengths, `cgcdTerminates fuel a b` holds. -/
theorem cgcdTerminates_of_fuel_lt (fuel : ℕ) (a b : CPoly)
    (ha : (cnorm a).length < fuel) (hb : (cnorm b).length < fuel) :
    cgcdTerminates fuel a b :=
  cgcdTerminates_of_fuel fuel a b (le_of_lt ha) hb

/-- The Euclidean remainder never exceeds the dividend's length:
`(cnorm (cmod fuel a b)).length ≤ (cnorm a).length`. -/
theorem cmod_length_le_left :
    ∀ (fuel : ℕ) (a b : CPoly), (cnorm (cmod fuel a b)).length ≤ (cnorm a).length := by
  intro fuel
  induction fuel with
  | zero =>
    intro a b
    have : cmod 0 a b = cnorm a := by simp [cmod, cdivmod]
    rw [this, cnorm_idem]
  | succ fuel ih =>
    intro a b
    by_cases hbz : cisZero (cnorm b) = true
    · have h2 : cmod (fuel + 1) a b = [] := by
        rw [cmod, cdivmod]; simp only [hbz, if_true]
      rw [h2]; simp
    · by_cases hlen : (cnorm a).length < (cnorm b).length
      · have h2 : cmod (fuel + 1) a b = cnorm a := by
          rw [cmod, cdivmod]
          simp only [hbz, Bool.false_eq_true, if_false, if_pos hlen]
        rw [h2, cnorm_idem]
      · have hbne : cnorm b ≠ [] := by simpa [cisZero_cnorm, cisZero] using hbz
        have hane : cnorm a ≠ [] := by
          rintro h; rw [h, List.length_nil] at hlen
          exact hlen (List.length_pos_iff.mpr hbne)
        have hstep := step_length_lt a b hane hbne (by omega)
        have key : cmod (fuel + 1) a b
            = cmod fuel (cnorm (csub (cnorm a)
                (cmul (cshift ((cnorm a).length - (cnorm b).length) [clead a / clead b])
                  (cnorm b)))) b := by
          rw [cmod, cdivmod]
          simp only [hbz, Bool.false_eq_true, if_false, if_neg hlen, clead_cnorm, cmod,
            ← cdivmod_cnorm_right]
        rw [key]
        refine (ih _ b).trans ?_
        rw [cnorm_idem]; omega

/-- `cgcdExt`'s gcd is no longer than its larger input:
`(cnorm (cgcdExt fuel a b).1).length ≤ max (cnorm a).length (cnorm b).length`. -/
theorem cgcdExt_fst_length_le :
    ∀ (fuel : ℕ) (a b : CPoly),
      (cnorm (cgcdExt fuel a b).1).length ≤ max (cnorm a).length (cnorm b).length := by
  intro fuel
  induction fuel with
  | zero =>
    intro a b
    rw [cgcdExt]
    simp [cnorm_idem]
  | succ fuel ih =>
    intro a b
    rw [cgcdExt]
    by_cases hbz : cisZero b = true
    · simp only [hbz, if_true, cnorm_idem]
      exact le_max_left _ _
    · simp only [hbz, Bool.false_eq_true, if_false]
      rcases hqr : cdivmod (fuel + 1) a b with ⟨q, r⟩
      have hr : r = cmod (fuel + 1) a b := by rw [cmod, hqr]
      -- the remainder is bounded by the dividend `a`
      have hra : (cnorm r).length ≤ (cnorm a).length := by
        rw [hr]; exact cmod_length_le_left (fuel + 1) a b
      have hih := ih b r
      rcases hg : cgcdExt fuel b r with ⟨g, s, t⟩
      rw [hg] at hih
      simp only at hih ⊢
      calc (cnorm g).length ≤ max (cnorm b).length (cnorm r).length := hih
        _ ≤ max (cnorm a).length (cnorm b).length := by
          rw [max_le_iff]
          exact ⟨le_max_right _ _, le_trans hra (le_max_left _ _)⟩

/-- Quotient degree: for a non-constant divisor with `deg q ≤ deg p` and enough fuel,
`natDegree (cdiv …) + natDegree q = natDegree p`. -/
theorem cdiv_natDegree_add (fuel : ℕ) (p q : CPoly) (hp : cnorm p ≠ []) (hq : cnorm q ≠ [])
    (hq2 : 2 ≤ (cnorm q).length) (hpq : (cnorm q).length ≤ (cnorm p).length)
    (hfuel : (cnorm p).length ≤ fuel) :
    (toPoly (cdiv fuel p q)).natDegree + (toPoly q).natDegree = (toPoly p).natDegree := by
  have hP : toPoly p ≠ 0 := fun h => hp ((cnorm_eq_nil_iff p).mpr h)
  have hQ : toPoly q ≠ 0 := fun h => hq ((cnorm_eq_nil_iff q).mpr h)
  have hdiv : toPoly p = toPoly (cdiv fuel p q) * toPoly q + toPoly (cmod fuel p q) :=
    toPoly_cdivmod' fuel p q hq
  have hr : (toPoly (cmod fuel p q)).natDegree < (toPoly q).natDegree := by
    have hlen := cmod_length_lt fuel p q hq hfuel
    have e1 := cdeg_eq_natDegree (cmod fuel p q)
    have e2 := cdeg_eq_natDegree q
    simp only [cdeg] at e1 e2
    omega
  have hpq' : (toPoly q).natDegree ≤ (toPoly p).natDegree := by
    have e1 := cdeg_eq_natDegree p
    have e2 := cdeg_eq_natDegree q
    simp only [cdeg] at e1 e2
    omega
  have hquo : toPoly (cdiv fuel p q) ≠ 0 := by
    intro h0
    rw [h0, zero_mul, zero_add] at hdiv
    rw [hdiv] at hpq'
    omega
  have key : (toPoly (cdiv fuel p q) * toPoly q).natDegree = (toPoly p).natDegree := by
    have heq : toPoly (cdiv fuel p q) * toPoly q = toPoly p - toPoly (cmod fuel p q) := by
      rw [hdiv]; ring
    rw [heq, natDegree_sub_eq_left_of_natDegree_lt (lt_of_lt_of_le hr hpq')]
  rwa [Polynomial.natDegree_mul hquo hQ] at key

/-- `cpow c n = c ^ n`. -/
theorem cpow_eq (c : ℚ) (n : ℕ) : cpow c n = c ^ n := by
  induction n with
  | zero => simp [cpow]
  | succ n ih => rw [cpow, ih, pow_succ']

/-- `cdeg` is invariant under `cnorm`. -/
theorem cdeg_cnorm (p : CPoly) : cdeg (cnorm p) = cdeg p := by
  simp only [cdeg, cnorm_idem]

/-- `cmod` is invariant under normalizing both arguments. -/
theorem cmod_cnorm_both (fuel : ℕ) (p q : CPoly) :
    cmod fuel (cnorm p) (cnorm q) = cmod fuel p q := by
  cases fuel with
  | zero => simp [cmod, cdivmod, cnorm_idem]
  | succ fuel => simp only [cmod, cdivmod, cnorm_idem]

/-- `cresultant` is invariant under normalizing both arguments (it normalizes them internally). -/
theorem cresultant_cnorm (fuel : ℕ) (p q : CPoly) :
    cresultant fuel (cnorm p) (cnorm q) = cresultant fuel p q := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp only [cresultant, cnorm_idem]

/-- `cresultant = Polynomial.resultant` for the case `deg q ≤ deg p` (with enough fuel). -/
theorem cresultant_eq_of_ge : ∀ (fuel : ℕ) (p q : CPoly),
    (cnorm q).length ≤ (cnorm p).length →
    (cnorm p).length + (cnorm q).length + 1 ≤ fuel →
    cresultant fuel p q = Polynomial.resultant (toPoly p) (toPoly q) (cdeg p) (cdeg q) := by
  intro fuel
  induction fuel with
  | zero => intro p q _ hfuel; omega
  | succ fuel ih =>
    intro p q hpq hfuel
    by_cases h0 : cisZero q = true
    · -- q = 0
      have hqnil : cnorm q = [] := by simpa [cisZero] using h0
      have hq0 : toPoly q = 0 := by rw [← toPoly_cnorm, hqnil, toPoly_nil]
      have hdq : cdeg q = 0 := by simp [cdeg, hqnil]
      have hval : cresultant (fuel + 1) p q = (if (cnorm p).length ≤ 1 then 1 else 0) := by
        rw [cresultant]; simp only [cisZero_cnorm, h0, if_true]
      rw [hval, hq0, Polynomial.resultant_zero_right, hdq, pow_zero, mul_one]
      by_cases hp1 : (cnorm p).length ≤ 1
      · have : cdeg p = 0 := by simp only [cdeg]; omega
        rw [if_pos hp1, this, pow_zero]
      · have : cdeg p ≠ 0 := by simp only [cdeg]; omega
        rw [if_neg hp1, zero_pow this]
    · have hcz : cisZero q = false := by simpa using h0
      have hq : cnorm q ≠ [] := fun h => by simp [cisZero, h] at hcz
      by_cases hqc : (cnorm q).length ≤ 1
      · -- q a nonzero constant: res(p, c) = c^(deg p)
        have hdq : cdeg q = 0 := by simp only [cdeg]; omega
        have hval : cresultant (fuel + 1) p q = cpow (clead q) (cdeg p) := by
          rw [cresultant]
          simp only [cisZero_cnorm, hcz, Bool.false_eq_true, if_false, if_pos hqc, clead_cnorm,
            cdeg_cnorm]
        rw [hval, cpow_eq, hdq, Polynomial.resultant_zero_right_deg]
        rw [clead_eq_coeff, hdq]
      · -- reduction
        have hq2 : 2 ≤ (cnorm q).length := by omega
        have hp : cnorm p ≠ [] := by
          intro h; rw [h, List.length_nil] at hpq; omega
        have hpqlen : ¬ (cnorm p).length < (cnorm q).length := by omega
        have hRlen : (cnorm (cmod (fuel + 1) p q)).length < (cnorm q).length :=
          cmod_length_lt (fuel + 1) p q hq (by omega)
        have hval : cresultant (fuel + 1) p q
            = cpow (-1) (cdeg p * cdeg q) * cpow (clead q) (cdeg p - cdeg (cmod (fuel + 1) p q))
              * cresultant fuel q (cmod (fuel + 1) p q) := by
          rw [cresultant]
          simp only [cisZero_cnorm, hcz, Bool.false_eq_true, if_false, if_neg hqc, if_neg hpqlen,
            clead_cnorm, cdeg_cnorm, cmod_cnorm_both, cresultant_cnorm]
        rw [hval, cpow_eq, cpow_eq]
        have hih := ih q (cmod (fuel + 1) p q) (le_of_lt hRlen) (by omega)
        rw [hih]
        have hP : toPoly p ≠ 0 := fun h => hp ((cnorm_eq_nil_iff p).mpr h)
        have hQ : toPoly q ≠ 0 := fun h => hq ((cnorm_eq_nil_iff q).mpr h)
        have hdp : cdeg p = (toPoly p).natDegree := cdeg_eq_natDegree p
        have hdq : cdeg q = (toPoly q).natDegree := cdeg_eq_natDegree q
        have hdr : cdeg (cmod (fuel + 1) p q) = (toPoly (cmod (fuel + 1) p q)).natDegree :=
          cdeg_eq_natDegree _
        have hdrlt : (toPoly (cmod (fuel + 1) p q)).natDegree < (toPoly q).natDegree := by
          rw [← hdr, ← hdq]; simp only [cdeg]; omega
        have hqp : (toPoly q).natDegree ≤ (toPoly p).natDegree := by
          rw [← hdq, ← hdp]; simp only [cdeg]; omega
        have hdiv : toPoly p
            = toPoly (cmod (fuel + 1) p q) + toPoly q * toPoly (cdiv (fuel + 1) p q) := by
          have h : toPoly p = toPoly (cdiv (fuel + 1) p q) * toPoly q
              + toPoly (cmod (fuel + 1) p q) := toPoly_cdivmod' (fuel + 1) p q hq
          linear_combination h
        have hqd : (toPoly (cdiv (fuel + 1) p q)).natDegree + (toPoly q).natDegree
            = (toPoly p).natDegree := cdiv_natDegree_add (fuel + 1) p q hp hq hq2 hpq (by omega)
        rw [Polynomial.resultant_comm (toPoly p) (toPoly q), hdiv,
          Polynomial.resultant_add_mul_right (toPoly q) (toPoly (cmod (fuel + 1) p q))
            (toPoly (cdiv (fuel + 1) p q)) (cdeg q) (cdeg p)
            (by rw [hdp, hdq]; omega) (le_of_eq hdq.symm)]
        rw [hdp, show (toPoly p).natDegree
              = (toPoly (cmod (fuel + 1) p q)).natDegree + (cdeg p - cdeg (cmod (fuel + 1) p q))
            from by rw [hdr, hdp]; omega,
          Polynomial.resultant_add_right_deg (toPoly q) (toPoly (cmod (fuel + 1) p q)) (cdeg q)
            (toPoly (cmod (fuel + 1) p q)).natDegree (cdeg p - cdeg (cmod (fuel + 1) p q)) le_rfl]
        rw [← hdr, clead_eq_coeff, Nat.add_sub_cancel_left]
        ring

/-- `cresultant = Polynomial.resultant`, the general case (for any `p, q`, with sufficient fuel). -/
theorem cresultant_eq (fuel : ℕ) (p q : CPoly)
    (hfuel : (cnorm p).length + (cnorm q).length + 2 ≤ fuel) :
    cresultant fuel p q = Polynomial.resultant (toPoly p) (toPoly q) (cdeg p) (cdeg q) := by
  by_cases hpq : (cnorm q).length ≤ (cnorm p).length
  · exact cresultant_eq_of_ge fuel p q hpq (by omega)
  · replace hpq : (cnorm p).length < (cnorm q).length := by omega
    have hq : cnorm q ≠ [] := by intro h; rw [h, List.length_nil] at hpq; omega
    have hcz : cisZero q = false := by simpa [cisZero] using hq
    by_cases hqc : (cnorm q).length ≤ 1
    · -- q a nonzero constant, p = 0
      have hp0 : cnorm p = [] := List.length_eq_zero_iff.mp (by omega)
      have hp0' : toPoly p = 0 := by rw [← toPoly_cnorm, hp0, toPoly_nil]
      have hdp : cdeg p = 0 := by simp only [cdeg, hp0, List.length_nil]
      have hdq : cdeg q = 0 := by simp only [cdeg]; omega
      have hval : cresultant fuel p q = cpow (clead q) (cdeg p) := by
        obtain ⟨fuel', rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
        rw [cresultant]
        simp only [cisZero_cnorm, hcz, Bool.false_eq_true, if_false, if_pos hqc, clead_cnorm,
          cdeg_cnorm]
      rw [hval, cpow_eq, hp0', hdp, hdq]
      simp
    · -- q non-constant, swap
      obtain ⟨fuel', rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hval : cresultant (fuel' + 1) p q
          = cpow (-1) (cdeg p * cdeg q) * cresultant fuel' q p := by
        rw [cresultant]
        simp only [cisZero_cnorm, hcz, Bool.false_eq_true, if_false, if_neg hqc, if_pos hpq,
          cdeg_cnorm, cresultant_cnorm]
      rw [hval, cpow_eq, cresultant_eq_of_ge fuel' q p (le_of_lt hpq) (by omega),
        Polynomial.resultant_comm (toPoly p) (toPoly q)]

end DeepWiki.SymbolicIntegration.Compute
