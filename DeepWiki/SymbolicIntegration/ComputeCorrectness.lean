import DeepWiki.SymbolicIntegration.HermiteCompute

/-! # Correctness of the computable engine (`toPoly` agreement bridge)
The `*Compute` engine (`CPoly := List ℚ`, `cdivmod`/`cgcdExt`/…) is validated *pointwise* by
`native_decide` against book answers. This file upgrades that to *proven on all inputs*: through the
`toPoly : CPoly → ℚ[X]` bridge the computable operations are shown to realize the honest `ℚ[X]`
operations. The spine is the **Euclidean-division identity** `toPoly p = toPoly (cdiv … p q) · toPoly q
+ toPoly (cmod … p q)` (for `q ≠ 0`, any fuel), and the **Bézout identity** `toPoly s · toPoly a +
toPoly t · toPoly b = toPoly g` for `cgcdExt`. These feed the higher agreements (`cresultant`,
`lrtGcdCompute`, `hermiteReduce`) whose correctness theorems then transfer onto the `native_decide`
computations. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration.Compute

/-- `cnorm [] = []`. -/
@[simp] theorem cnorm_nil : cnorm ([] : CPoly) = [] := rfl

/-- `cnorm` on a cons cell, unfolded to its defining `match` (definitional). -/
theorem cnorm_cons_eq (a : ℚ) (as : CPoly) :
    cnorm (a :: as)
      = (match cnorm as with | [] => if a = 0 then [] else [a] | r => a :: r) := rfl

/-- `cnorm` is **idempotent**: stripping trailing zeros twice is the same as once. -/
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

/-- **`toPoly` ignores normalization**: `toPoly (cnorm p) = toPoly p` — stripping trailing zeros does
not change the polynomial (the dropped coefficients are zero). Foundational, since `cdivmod`/`cgcdExt`
normalize their inputs. -/
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

/-- **Euclidean-division identity through `toPoly`** (with `q` already normalized and nonzero, any
fuel): `toPoly p = toPoly (quotient) · toPoly q + toPoly (remainder)`. The `cdivmod` long division
realizes honest `ℚ[X]` division up to the polynomial value. This is the spine the `cgcdExt` Bézout
identity and the higher (resultant/subresultant/Hermite) agreements rest on. -/
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

/-- `cdivmod` **normalizes its divisor**: `cdivmod fuel p q = cdivmod fuel p (cnorm q)` (the body
shadows `q` with `cnorm q`, and `cnorm` is idempotent). Lets the division identity drop the
"`q` normalized" hypothesis. -/
theorem cdivmod_cnorm_right (fuel : ℕ) (p q : CPoly) :
    cdivmod fuel p q = cdivmod fuel p (cnorm q) := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp only [cdivmod, cnorm_idem]

/-- **Euclidean-division identity through `toPoly`** for an arbitrary nonzero divisor (`cnorm q ≠ []`,
any fuel): `toPoly p = toPoly (quotient) · toPoly q + toPoly (remainder)`. -/
theorem toPoly_cdivmod' (fuel : ℕ) (p q : CPoly) (hq0 : cnorm q ≠ []) :
    toPoly p
      = toPoly (cdivmod fuel p q).1 * toPoly q + toPoly (cdivmod fuel p q).2 := by
  rw [cdivmod_cnorm_right]
  simpa [toPoly_cnorm] using toPoly_cdivmod fuel p (cnorm q) (cnorm_idem q) hq0

/-- **Bézout identity through `toPoly`** for the extended Euclidean algorithm (any fuel): with
`(g, s, t) = cgcdExt fuel a b`, `toPoly s · toPoly a + toPoly t · toPoly b = toPoly g`. So the
computable `cgcdExt` realizes an honest Bézout relation in `ℚ[X]`. -/
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

/-- The **`LogToAtan` step invariant** `B·D − A·C = G` holds in `ℚ[X]`: the extended-Euclidean
cofactors `(G, D, C) = cgcdExt fuel B (−A)` that each `logToAtanCompute` step uses (so that
`(A·D + B·C)/G` is the next arctan argument) satisfy `toPoly B · toPoly D − toPoly A · toPoly C =
toPoly G`. A direct corollary of `toPoly_cgcdExt`, validating the Rioboo recursion's core Bézout
relation on all inputs (not just the `native_decide`'d Example 2.8.1). -/
theorem logToAtan_cofactor_bezout (fuel : ℕ) (A B : CPoly) :
    toPoly B * toPoly (cgcdExt fuel B (cneg A)).2.1
        - toPoly A * toPoly (cgcdExt fuel B (cneg A)).2.2
      = toPoly (cgcdExt fuel B (cneg A)).1 := by
  have h := toPoly_cgcdExt fuel B (cneg A)
  rw [toPoly_cneg] at h
  linear_combination h

/-! ### The bivariate bridge `toBPoly : BPoly → ℚ[t][x]` and its homomorphism lemmas
One level up from `toPoly`: a `BPoly = List CPoly` is read as a polynomial in `x` (`Polynomial`)
whose coefficients are the `ℚ[t]` polynomials `toPoly`. The homomorphism lemmas reduce the `BPoly`
algebra to honest `(ℚ[X])[X]` operations, mirroring the `CPoly` layer. -/

/-- **Bivariate bridge** `toBPoly : BPoly → (ℚ[X])[X]`: read a `BPoly` (list of `CPoly = ℚ[t]`
`x`-coefficients, low→high) as an honest `Polynomial (Polynomial ℚ)` in Horner form in `x`, each
`x`-coefficient embedded via `toPoly`. -/
noncomputable def toBPoly : BPoly → Polynomial (Polynomial ℚ)
  | [] => 0
  | a :: p => Polynomial.C (toPoly a) + Polynomial.X * toBPoly p

@[simp] theorem toBPoly_nil : toBPoly ([] : BPoly) = 0 := rfl

@[simp] theorem toBPoly_cons (a : CPoly) (p : BPoly) :
    toBPoly (a :: p) = Polynomial.C (toPoly a) + Polynomial.X * toBPoly p := rfl

/-- `toBPoly` is **additive**: `badd` realizes `(ℚ[X])[X]` addition. -/
theorem toBPoly_badd (p q : BPoly) : toBPoly (badd p q) = toBPoly p + toBPoly q := by
  induction p generalizing q with
  | nil => simp [badd]
  | cons a as ih =>
    cases q with
    | nil => simp [badd]
    | cons b bs =>
      simp only [badd, toBPoly_cons, ih, toPoly_cadd, map_add]
      ring

/-- `toBPoly` is **negation-compatible**: `bneg` realizes `(ℚ[X])[X]` negation. -/
theorem toBPoly_bneg (p : BPoly) : toBPoly (bneg p) = - toBPoly p := by
  induction p with
  | nil => simp [bneg]
  | cons a as ih =>
    show toBPoly (cneg a :: bneg as) = _
    simp only [toBPoly_cons, toPoly_cneg, map_neg, ih]
    ring

/-- `toBPoly` is **subtraction-compatible**: `bsub` realizes `(ℚ[X])[X]` subtraction. -/
theorem toBPoly_bsub (p q : BPoly) : toBPoly (bsub p q) = toBPoly p - toBPoly q := by
  simp [bsub, toBPoly_badd, toBPoly_bneg, sub_eq_add_neg]

/-- `toBPoly` realizes **scaling by a `ℚ[t]` coefficient**: `bscaleC c p` is `C (toPoly c) · toBPoly p`. -/
theorem toBPoly_bscaleC (c : CPoly) (p : BPoly) :
    toBPoly (bscaleC c p) = Polynomial.C (toPoly c) * toBPoly p := by
  induction p with
  | nil => simp [bscaleC]
  | cons a as ih =>
    show toBPoly (cmul c a :: bscaleC c as) = _
    simp only [toBPoly_cons, toPoly_cmul, map_mul, ih]
    ring

/-- `toBPoly` realizes the **`x`-shift**: `bshift k p` is `Xᵏ · toBPoly p`. -/
theorem toBPoly_bshift (k : ℕ) (p : BPoly) :
    toBPoly (bshift k p) = Polynomial.X ^ k * toBPoly p := by
  induction k with
  | zero => simp [bshift]
  | succ n ih =>
    show toBPoly ([] :: bshift n p) = _
    simp only [toBPoly_cons, toPoly_nil, map_zero, ih]
    ring

/-- `toBPoly` is **multiplicative**: `bmul` realizes `(ℚ[X])[X]` multiplication. -/
theorem toBPoly_bmul (p q : BPoly) : toBPoly (bmul p q) = toBPoly p * toBPoly q := by
  induction p with
  | nil => simp [bmul]
  | cons a as ih =>
    show toBPoly (badd (bscaleC a q) ([] :: bmul as q)) = _
    simp only [toBPoly_badd, toBPoly_bscaleC, toBPoly_cons, toPoly_nil, map_zero, ih]
    ring

/-- `bnorm [] = []`. -/
@[simp] theorem bnorm_nil : bnorm ([] : BPoly) = [] := rfl

/-- `bnorm` on a cons cell, unfolded to its defining `match` (definitional). -/
theorem bnorm_cons_eq (a : CPoly) (as : BPoly) :
    bnorm (a :: as)
      = (match bnorm as with
          | [] => if cisZero (cnorm a) then [] else [cnorm a]
          | r => cnorm a :: r) := rfl

/-- `bnorm` is **idempotent**. -/
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

/-- `bpsremainder` **normalizes its divisor**: `bpsremainder fuel p q = bpsremainder fuel p (bnorm q)`. -/
theorem bpsremainder_bnorm_right (fuel : ℕ) (p q : BPoly) :
    bpsremainder fuel p q = bpsremainder fuel p (bnorm q) := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp only [bpsremainder, bnorm_idem]

/-- **`toBPoly` ignores normalization**: `toBPoly (bnorm p) = toBPoly p`. -/
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

/-- **Pseudo-division identity through `toBPoly`** (any fuel): there is a multiplier `c ∈ ℚ[t]` (a
product of leading `x`-coefficients of `q`) and a quotient `s` with `C (toPoly c) · toBPoly p =
toBPoly s · toBPoly q + toBPoly (bpsremainder fuel p q)`. So the computable pseudo-remainder realizes
the honest `ℚ[t][x]` pseudo-division relation `lc(q)ᵏ·p = s·q + prem` — the existential matches the
non-field coefficient ring `ℚ[t]` (where division is only up to a leading-coefficient factor). This is
the spine for the subresultant-PRS gcd agreement (`lrtGcdCompute ↔ lrtSubresultant`). -/
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

/-- **Diophantine/Bézout solver correctness through `toPoly`**: when `gcd(p, q)` is a nonzero
constant (the coprimality the Hermite call sites guarantee), `cdiophantine fuel p q rhs = (B, C)`
solves `B·p + C·q = rhs` in `ℚ[X]`: `toPoly B · toPoly p + toPoly C · toPoly q = toPoly rhs`.
Validates the Hermite reduction's Bézout step on all inputs. -/
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

/-- **`cgcdExt`'s gcd is greatest among common divisors**: any `d` dividing both `toPoly a` and
`toPoly b` divides `toPoly (cgcdExt fuel a b).1` — immediate from the Bézout identity (`g` lies in the
ideal `(a, b)`). Together with the (fuel-dependent) converse `g ∣ a, g ∣ b` this characterizes `g` as
a gcd; this half is fuel-independent. -/
theorem toPoly_dvd_cgcdExt {d : ℚ[X]} (fuel : ℕ) (a b : CPoly)
    (ha : d ∣ toPoly a) (hb : d ∣ toPoly b) :
    d ∣ toPoly (cgcdExt fuel a b).1 := by
  rw [← toPoly_cgcdExt fuel a b]
  exact dvd_add (ha.mul_left _) (hb.mul_left _)

end DeepWiki.SymbolicIntegration.Compute
