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

end DeepWiki.SymbolicIntegration.Compute
