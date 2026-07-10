import DeepWiki.SymbolicIntegration.Compute.Hermite
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! # Correctness of the computable engine
Through `DensePoly.toPoly`, the concrete bivariate, rational-function, and resultant operations
realize the corresponding `ℚ[X]` operations. Polynomial division and gcd correctness come directly
from the representation-independent and well-founded dense APIs. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration.Compute

/-- `cnorm` on a cons cell, unfolded to its defining `match`. -/
theorem cnorm_cons_eq (a : ℚ) (as : DensePoly ℚ) :
    cnorm (a :: as)
      = (match cnorm as with | [] => if a = 0 then [] else [a] | r => a :: r) := by
  show DensePoly.cnorm (a :: as)
      = (match DensePoly.cnorm as with | [] => if a = 0 then [] else [a] | r => a :: r)
  rw [DensePoly.cnormG_cons_eq]
  cases DensePoly.cnorm as with
  | nil => show (if (decide (a = 0) = true) then _ else _) = _; by_cases ha : a = 0 <;> simp [ha]
  | cons b bs => rfl

/-! ### The bivariate bridge `toBPoly : BPoly → ℚ[t][x]` and its homomorphism lemmas
Reads a `BPoly = List (DensePoly ℚ)` as a `Polynomial (Polynomial ℚ)` in `x`, each `x`-coefficient via
`toPoly`; the homomorphism lemmas reduce the `BPoly` algebra to `(ℚ[X])[X]` operations. -/

/-- Bivariate bridge `toBPoly : BPoly → (ℚ[X])[X]`: read a `BPoly` as a `Polynomial (Polynomial ℚ)`
in Horner form in `x`, each `x`-coefficient embedded via `toPoly`. -/
noncomputable def toBPoly : BPoly → Polynomial (Polynomial ℚ)
  | [] => 0
  | a :: p => Polynomial.C (toPoly a) + Polynomial.X * toBPoly p

@[simp] theorem toBPoly_nil : toBPoly ([] : BPoly) = 0 := rfl

@[simp] theorem toBPoly_cons (a : DensePoly ℚ) (p : BPoly) :
    toBPoly (a :: p) = Polynomial.C (toPoly a) + Polynomial.X * toBPoly p := rfl

/-! ### Bridges to the generic keystone engine (`DensePoly.toPoly` / `c*` at coefficient `DensePoly ℚ`)
`BPoly = DensePoly (DensePoly ℚ)` and the ring-generalized engine makes `DensePoly.toPoly`/`cadd`/… valid at the
`DensePoly ℚ` coefficient (keystone `CRingSpec (DensePoly ℚ)`). These identify the hand-written `ℚ`-bivariate
layer with the generic one, so the `b*` homomorphism satellites reduce to the generic `toPolyG_*`
squares instead of re-proving the recursions. -/

/-- The bivariate denotation IS the generic keystone denotation: `toBPoly = DensePoly.toPoly` at `DensePoly (DensePoly ℚ)`. -/
theorem toBPoly_eq_toPolyG (p : BPoly) : toBPoly p = DensePoly.toPoly p := by
  induction p with
  | nil => rfl
  | cons a as ih =>
    rw [toBPoly, ih, DensePoly.toPolyG_cons,
      show toPoly a = DensePoly.toPoly a from rfl,
      show CRingSpec.toR a = DensePoly.toPoly a from rfl]

/-- `badd = cadd` at coefficient `DensePoly ℚ` (definitional). -/
theorem badd_eq (p q : BPoly) : badd p q = DensePoly.cadd p q := rfl

/-- `bmul = cmul` at coefficient `DensePoly ℚ` (definitional). -/
theorem bmul_eq (p q : BPoly) : bmul p q = DensePoly.cmul p q := rfl

/-- `bshift = cshift` at coefficient `DensePoly ℚ` (definitional). -/
theorem bshift_eq (k : ℕ) (p : BPoly) : bshift k p = DensePoly.cshift k p := rfl

/-- `bneg = cneg` at coefficient `DensePoly ℚ` (definitional). -/
theorem bneg_eq (p : BPoly) : bneg p = DensePoly.cneg p := rfl

/-- `bscaleC = cscale` at coefficient `DensePoly ℚ` (definitional). -/
theorem bscaleC_eq (c : DensePoly ℚ) (p : BPoly) : bscaleC c p = DensePoly.cscale c p := rfl

/-- `bsub = csub` at coefficient `DensePoly ℚ` (definitional). -/
theorem bsub_eq (p q : BPoly) : bsub p q = DensePoly.csub p q := rfl

/-- `toBPoly` is additive: `badd` realizes `(ℚ[X])[X]` addition. -/
theorem toBPoly_badd (p q : BPoly) : toBPoly (badd p q) = toBPoly p + toBPoly q := by
  simp only [toBPoly_eq_toPolyG, badd_eq, DensePoly.toPolyG_caddG]

/-- `bneg` realizes `(ℚ[X])[X]` negation through `toBPoly`. -/
theorem toBPoly_bneg (p : BPoly) : toBPoly (bneg p) = - toBPoly p := by
  simp only [toBPoly_eq_toPolyG, bneg_eq, DensePoly.toPolyG_cnegG]

/-- `bsub` realizes `(ℚ[X])[X]` subtraction through `toBPoly`. -/
theorem toBPoly_bsub (p q : BPoly) : toBPoly (bsub p q) = toBPoly p - toBPoly q := by
  simp only [toBPoly_eq_toPolyG, bsub_eq, DensePoly.toPolyG_csubG]

/-- `bscaleC c p` realizes scaling by a `ℚ[t]` coefficient: `C (toPoly c) · toBPoly p`. -/
theorem toBPoly_bscaleC (c : DensePoly ℚ) (p : BPoly) :
    toBPoly (bscaleC c p) = Polynomial.C (toPoly c) * toBPoly p := by
  simp only [toBPoly_eq_toPolyG, bscaleC_eq, DensePoly.toPolyG_cscaleG, toPoly_eq_dense,
    show ∀ c : DensePoly ℚ, CRingSpec.toR c = DensePoly.toPoly c from fun _ => rfl]

/-- `bshift k p` realizes the `x`-shift: `Xᵏ · toBPoly p`. -/
theorem toBPoly_bshift (k : ℕ) (p : BPoly) :
    toBPoly (bshift k p) = Polynomial.X ^ k * toBPoly p := by
  simp only [toBPoly_eq_toPolyG, bshift_eq, DensePoly.toPolyG_cshiftG]

/-- `toBPoly` is multiplicative: `bmul` realizes `(ℚ[X])[X]` multiplication. -/
theorem toBPoly_bmul (p q : BPoly) : toBPoly (bmul p q) = toBPoly p * toBPoly q := by
  simp only [toBPoly_eq_toPolyG, bmul_eq, DensePoly.toPolyG_cmulG]

/-- `bnorm [] = []`. -/
@[simp] theorem bnorm_nil : bnorm ([] : BPoly) = [] := rfl

/-- `bnorm` on a cons cell, unfolded to its defining `match`. -/
theorem bnorm_cons_eq (a : DensePoly ℚ) (as : BPoly) :
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
    | nil => cases ha : cisZero (cnorm a) <;> simp [bnorm_cons_eq, ha]
    | cons b bs =>
      rw [h] at ih
      simp only [bnorm_cons_eq, DensePoly.cnormG_idem, ih]

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
          have hca : cnorm a = [] := by simpa [cisZero, DensePoly.cnormG_idem] using ha
          rw [toPoly_eq_dense, ← DensePoly.toPolyG_cnormG, hca, DensePoly.toPolyG_nil]
        simp only [toPoly_eq_dense] at hpa
        simp [toBPoly_cons, toPoly_eq_dense, hpa, has]
      | false => simp [toBPoly_cons, toPoly_eq_dense, DensePoly.toPolyG_cnormG, has]
    | cons b bs =>
      rw [h] at ih
      simp only [toBPoly_cons, toPoly_eq_dense, DensePoly.toPolyG_cnormG, ih]

/-- `toBPoly [[1]] = 1`: the `BPoly` constant `1`. -/
@[simp] theorem toBPoly_one : toBPoly ([[1]] : BPoly) = 1 := by
  simp [toBPoly_cons, DensePoly.toPolyG_cons]

/-- Pseudo-division identity through `toBPoly`: there exist a multiplier `c ∈ ℚ[t]` and quotient `s`
with `C (toPoly c) · toBPoly p = toBPoly s · toBPoly q + toBPoly (bpsremainder fuel p q)`. -/
theorem toBPoly_bpsremainder (fuel : ℕ) (p q : BPoly) :
    ∃ (s : BPoly) (c : DensePoly ℚ),
      Polynomial.C (toPoly c) * toBPoly p
        = toBPoly s * toBPoly q + toBPoly (bpsremainder fuel p q) := by
  induction fuel generalizing p with
  | zero => exact ⟨[], [1], by simp [bpsremainder, toBPoly_bnorm, DensePoly.toPolyG_cons]⟩
  | succ fuel ih =>
    simp only [bpsremainder]
    split_ifs with hq hlen
    · exact ⟨[], [1], by simp [toBPoly_bnorm, DensePoly.toPolyG_cons]⟩
    · exact ⟨[], [1], by simp [toBPoly_bnorm, DensePoly.toPolyG_cons]⟩
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
      rw [toBPoly_badd, toBPoly_bscaleC, toBPoly_bshift, toBPoly_one]
      simp only [toPoly_eq_dense] at hsc ⊢
      rw [
        DensePoly.toPolyG_cmulG, map_mul,
        DensePoly.toPolyG_cmulG, map_mul]
      linear_combination hsc

/-- Diophantine/Bézout solver correctness through `toPoly`: when `gcd(p, q)` is a nonzero constant,
`cdiophantine p q rhs = (B, C)` satisfies `toPoly B · toPoly p + toPoly C · toPoly q = toPoly rhs`. -/
theorem toPoly_cdiophantine (p q rhs : DensePoly ℚ) (hq : cnorm q ≠ [])
    (hg : toPoly (DensePoly.cgcdWf p q).1 = Polynomial.C (clead (DensePoly.cgcdWf p q).1))
    (hgc : clead (DensePoly.cgcdWf p q).1 ≠ 0) :
    toPoly (cdiophantine p q rhs).1 * toPoly p
        + toPoly (cdiophantine p q rhs).2 * toPoly q
      = toPoly rhs := by
  rcases hgst : DensePoly.cgcdWf p q with ⟨g, s, t⟩
  rw [hgst] at hg hgc
  have hbez : toPoly s * toPoly p + toPoly t * toPoly q = toPoly g := by
    have h := DensePoly.toPolyG_cgcdWf p q
    rw [hgst] at h
    simpa only [toPoly_eq_dense] using h
  simp only [cdiophantine, hgst]
  rcases hqB : DensePoly.cdivmodWf (cscale (clead g)⁻¹ (cmul rhs s)) q with ⟨quo, B⟩
  have hdiv : toPoly (cscale (clead g)⁻¹ (cmul rhs s)) = toPoly quo * toPoly q + toPoly B := by
    have h := DensePoly.toPolyG_cdivmodWf (cscale (clead g)⁻¹ (cmul rhs s)) q hq
    rw [hqB] at h
    simpa only [toPoly_eq_dense] using h
  simp only [toPoly_eq_dense, DensePoly.toPolyG_cnormG, DensePoly.toPolyG_caddG,
    DensePoly.toPolyG_cmulG, DensePoly.toPolyG_cscaleG, toR_eq_toK,
    CFieldSpec.toK_rat] at hdiv ⊢
  have hinv : Polynomial.C (clead g)⁻¹ * toPoly g = 1 := by
    rw [hg, ← map_mul, inv_mul_cancel₀ hgc, map_one]
  simp only [toPoly_eq_dense] at hbez hinv
  linear_combination (-DensePoly.toPoly p) * hdiv
    + (Polynomial.C ((clead g)⁻¹ : ℚ) * DensePoly.toPoly rhs) * hbez
    + DensePoly.toPoly rhs * hinv

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
  simp only [toPoly_eq_dense] at hb' hd'
  simp only [toQFun, qadd, toPoly_eq_dense, DensePoly.toPolyG_caddG,
    DensePoly.toPolyG_cmulG, map_add, map_mul]
  rw [div_add_div _ _ hb' hd']
  ring

/-- `toQFun qzero = 0`. -/
theorem toQFun_qzero : toQFun qzero = 0 := by
  simp [toQFun, qzero, DensePoly.toPolyG_nil]

/-- `qadd x y` has nonzero denominator when both `x` and `y` do. -/
theorem toPoly_qadd_den_ne_zero {x y : QFun} (hx : toPoly x.2 ≠ 0) (hy : toPoly y.2 ≠ 0) :
    toPoly (qadd x y).2 ≠ 0 := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  show toPoly (cmul b d) ≠ 0
  rw [toPoly_eq_dense, DensePoly.toPolyG_cmulG]
  exact mul_ne_zero hx hy

/-- A `qadd` fold denotes the seed plus the sum of the entries. -/
theorem toQFun_foldl_qadd (gs : List QFun) (init : QFun) (hinit : toPoly init.2 ≠ 0)
    (hgs : ∀ g ∈ gs, toPoly g.2 ≠ 0) :
    toQFun (gs.foldl qadd init) = toQFun init + (gs.map toQFun).sum := by
  induction gs generalizing init with
  | nil => simp
  | cons hd tl ih =>
    have hhd : toPoly hd.2 ≠ 0 := hgs hd (List.mem_cons_self ..)
    have htl : ∀ g ∈ tl, toPoly g.2 ≠ 0 := fun g hg => hgs g (List.mem_cons_of_mem hd hg)
    have hnew : toPoly (qadd init hd).2 ≠ 0 := toPoly_qadd_den_ne_zero hinit hhd
    rw [List.foldl_cons, ih (qadd init hd) hnew htl, toQFun_qadd init hd hinit hhd,
      List.map_cons, List.sum_cons]
    ring

/-! ### Degree / leading coefficient bridge
`(toPoly p).coeff i = p.getD i 0`, from which `cdeg`/`clead` are the `natDegree`/`leadingCoeff`. -/

/-- Coefficient read: `(toPoly p).coeff i = p.getD i 0`. -/
theorem toPoly_coeff (p : DensePoly ℚ) (i : ℕ) : (toPoly p).coeff i = p.getD i 0 := by
  induction p generalizing i with
  | nil => simp
  | cons a as ih =>
    simp only [toPoly_eq_dense] at ih
    rw [toPoly_eq_dense, DensePoly.toPolyG_cons]
    cases i with
    | zero => simp [coeff_C]
    | succ n => simp [coeff_X_mul, ih]

/-- Degree bound: `natDegree (toPoly p) ≤ (cnorm p).length − 1`. -/
theorem natDegree_toPoly_le (p : DensePoly ℚ) : (toPoly p).natDegree ≤ (cnorm p).length - 1 := by
  rw [toPoly_eq_dense, ← DensePoly.toPolyG_cnormG]
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro m hm
  rw [DensePoly.toPolyG_coeff, toR_eq_toK, CFieldSpec.toK_rat,
    List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

/-- `cnorm` has no trailing zero: `(cnorm p).getLast? ≠ some 0`. -/
theorem cnorm_getLast?_ne_some_zero (p : DensePoly ℚ) : (cnorm p).getLast? ≠ some 0 := by
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

/-- For a normalized nonzero `DensePoly ℚ`, the leading coefficient `clead` is nonzero. -/
theorem clead_ne_zero {p : DensePoly ℚ} (h : cnorm p ≠ []) : clead p ≠ 0 := by
  show DensePoly.clead p ≠ 0
  rcases hl : (DensePoly.cnorm p).getLast? with _ | v
  · exact absurd (List.getLast?_eq_none_iff.mp hl) h
  · simp only [DensePoly.clead, hl, Option.getD_some]
    rintro rfl
    exact cnorm_getLast?_ne_some_zero p hl

/-- `clead p = (toPoly p).coeff (cdeg p)`: the leading coefficient sits at the top index. -/
theorem clead_eq_coeff (p : DensePoly ℚ) : clead p = (toPoly p).coeff (cdeg p) := by
  show DensePoly.clead p = _
  rw [DensePoly.clead, cdeg, toPoly_eq_dense, ← DensePoly.toPolyG_cnormG,
    DensePoly.toPolyG_coeff, toR_eq_toK, CFieldSpec.toK_rat,
    List.getD_eq_getElem?_getD,
    ← List.getLast?_eq_getElem?]

/-- `cdeg p = (toPoly p).natDegree`: `cdeg` is the honest `natDegree`. -/
theorem cdeg_eq_natDegree (p : DensePoly ℚ) : cdeg p = (toPoly p).natDegree := by
  rcases eq_or_ne (cnorm p) [] with h | h
  · have h0 : toPoly p = 0 := by
      rw [toPoly_eq_dense, ← DensePoly.toPolyG_cnormG, h, DensePoly.toPolyG_nil]
    rw [cdeg, h, h0]; simp
  · refine le_antisymm ?_ (natDegree_toPoly_le p)
    apply Polynomial.le_natDegree_of_ne_zero
    rw [← clead_eq_coeff]
    exact clead_ne_zero h

/-- `clead p = (toPoly p).leadingCoeff`: `clead` is the honest `leadingCoeff`. -/
theorem clead_eq_leadingCoeff (p : DensePoly ℚ) : clead p = (toPoly p).leadingCoeff := by
  rw [Polynomial.leadingCoeff, ← cdeg_eq_natDegree, ← clead_eq_coeff]

/-- `cnorm p = []` iff `toPoly p = 0` (the list normalizes to empty exactly for the zero polynomial). -/
theorem cnorm_eq_nil_iff (p : DensePoly ℚ) : cnorm p = [] ↔ toPoly p = 0 := by
  constructor
  · intro h; rw [toPoly_eq_dense, ← DensePoly.toPolyG_cnormG, h, DensePoly.toPolyG_nil]
  · intro h
    by_contra hne
    have hcl := clead_ne_zero hne
    rw [clead_eq_leadingCoeff, h, Polynomial.leadingCoeff_zero] at hcl
    exact hcl rfl

/-- For a nonzero polynomial, the normalized list length is `natDegree + 1`. -/
theorem length_cnorm_of_ne (p : DensePoly ℚ) (h : cnorm p ≠ []) :
    (cnorm p).length = (toPoly p).natDegree + 1 := by
  have hd := cdeg_eq_natDegree p
  rw [cdeg] at hd
  have hlen : 1 ≤ (cnorm p).length := List.length_pos_iff.mpr h
  omega

end DeepWiki.SymbolicIntegration.Compute
