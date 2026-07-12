import DeepWiki.SymbolicIntegration.Engine.PrimPRSRegular.Content
import DeepWiki.SymbolicIntegration.Engine.SplitFactorHelpers

/-! # Primitive PRS regularity: degree control

Normalized-length readings, pseudo-division degree drops, and primitive-part degree preservation.
-/

open Polynomial Classical

namespace DeepWiki.SymbolicIntegration

open DensePoly GBPolyCore

variable {β : Type*} [CField β] [CFieldSpec β]

/-! ## The normalized list length

The generic `DensePoly.cdegG_eq_natDegree` theorem turns the list-length loop guard into a polynomial
`t`-degree statement over the integral domain `R = (CFieldSpec.K β)[X]`. -/

/-- **`(DensePoly.toPoly p).natDegree` is bounded by the normalized `t`-length**:
`(DensePoly.toPoly p).natDegree ≤ (gbnormCore p).length − 1`. This bivariate helper has a distinct
name so it does not shadow the dense-polynomial reading lemma. -/
theorem natDegree_toGBPoly_le (p : GBPolyCore β) :
    (DensePoly.toPoly p).natDegree ≤ (gbnormCore p).length - 1 := by
  rw [← toPolyG_gbnormCore]
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro m hm
  rw [DensePoly.toPolyG_coeff_dense, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega),
    Option.getD_none, toPolyG_nil]

/-- **The normalized `t`-length equals `natDegree + 1` for a nonzero `GBPolyCore`**: if
`DensePoly.cisZero p = false`, then `(gbnormCore p).length = (DensePoly.toPoly p).natDegree + 1`. -/
theorem gbnormCore_length_eq_natDegree_succ {p : GBPolyCore β} (hp : DensePoly.cisZero p = false) :
    (gbnormCore p).length = (DensePoly.toPoly p).natDegree + 1 := by
  have hne : gbnormCore p ≠ [] := by
    intro hnorm
    exact DensePoly.toPolyG_ne_zero_of_cisZeroG_false hp
      ((gbnormCore_eq_nil_iff_toPolyG p).mp hnorm)
  have hnormne : DensePoly.cnorm (gbnormCore p) ≠ [] := by rwa [cnormG_gbnormCore]
  have hlen := DensePoly.length_cnormG_of_ne (gbnormCore p) hnormne
  rwa [cnormG_gbnormCore, toPolyG_gbnormCore] at hlen

/-- Generic nested zero testing is invariant under `gbnormCore`. -/
theorem cisZero_gbnormCore (p : GBPolyCore β) :
    DensePoly.cisZero (gbnormCore p) = DensePoly.cisZero p := by
  rw [Bool.eq_iff_iff, DensePoly.cisZeroG_iff, DensePoly.cisZeroG_iff,
    toPolyG_gbnormCore]

/-! ## Sharpening termination: the pseudo-division degree drop as a theorem

The content strip preserves the `t`-degree, and the single loop body `lc(q)·p − lc(p)·tᵏ·q` strictly
drops the `t`-degree over the integral domain `R = (CFieldSpec.K β)[X]`, so termination's only remaining
conditional ingredient is the fuel-bounded loop completing. -/

/-- **`toPoly (gblcCore (gbnormCore p))` is the leading coefficient of `DensePoly.toPoly p`**. -/
theorem toPolyG_gblcCore_eq_leadingCoeff (p : GBPolyCore β) :
    DensePoly.toPoly (gblcCore (gbnormCore p)) = (DensePoly.toPoly p).leadingCoeff := by
  rw [toPolyG_gblcCore_eq_coeff, toPolyG_gbnormCore, Polynomial.leadingCoeff]
  congr 1
  rw [DensePoly.cdegG_eq_natDegree, toPolyG_gbnormCore]

/-- **The single pseudo-division step body** `gbStepReduce p q = lc(q)·p − lc(p)·tᵏ·q`
(`k = (gbnormCore p).length − (gbnormCore q).length`): one leading-term elimination of
`gbpsremainderCore`. -/
noncomputable def gbStepReduce (p q : GBPolyCore β) : GBPolyCore β :=
  DensePoly.csub (DensePoly.cscale (gblcCore (gbnormCore q)) p)
    (DensePoly.cscale (gblcCore (gbnormCore p))
      (DensePoly.cshift ((gbnormCore p).length - (gbnormCore q).length) q))

/-- **The `R[t]` reading of a step body** `DensePoly.toPoly (gbStepReduce p q) = C(lc q)·DensePoly.toPoly p −
C(lc p)·tᵏ·DensePoly.toPoly q` (`R = (CFieldSpec.K β)[X]`, `k = deg_t p − deg_t q`). -/
theorem toPolyG_gbStepReduce (p q : GBPolyCore β) :
    DensePoly.toPoly (gbStepReduce p q)
      = Polynomial.C ((DensePoly.toPoly q).leadingCoeff) * DensePoly.toPoly p
        - Polynomial.C ((DensePoly.toPoly p).leadingCoeff)
          * Polynomial.X ^ ((gbnormCore p).length - (gbnormCore q).length) * DensePoly.toPoly q := by
  rw [gbStepReduce, DensePoly.toPolyG_csubG, DensePoly.toPolyG_cscaleG,
    DensePoly.toPolyG_cscaleG, DensePoly.toPolyG_cshiftG]
  simp only [DensePoly.toR_densePoly]
  rw [toPolyG_gblcCore_eq_leadingCoeff, toPolyG_gblcCore_eq_leadingCoeff]
  ring

/-- **The single pseudo-division step strictly drops the `t`-degree** (the leading-term cancellation):
for nonzero `p, q` with `deg_t q ≤ deg_t p`, if `gbStepReduce p q` is nonzero then
`(DensePoly.toPoly (gbStepReduce p q)).natDegree < (DensePoly.toPoly p).natDegree`. -/
theorem natDegree_gbStepReduce_lt (p q : GBPolyCore β)
    (hp : DensePoly.cisZero (gbnormCore p) = false) (hq : DensePoly.cisZero (gbnormCore q) = false)
    (hdeg : (DensePoly.toPoly q).natDegree ≤ (DensePoly.toPoly p).natDegree)
    (hstepne : DensePoly.toPoly (gbStepReduce p q) ≠ 0) :
    (DensePoly.toPoly (gbStepReduce p q)).natDegree < (DensePoly.toPoly p).natDegree := by
  have hp' : DensePoly.cisZero p = false := by rwa [cisZero_gbnormCore] at hp
  have hq' : DensePoly.cisZero q = false := by rwa [cisZero_gbnormCore] at hq
  have hkp : (gbnormCore p).length = (DensePoly.toPoly p).natDegree + 1 :=
    gbnormCore_length_eq_natDegree_succ hp'
  have hkq : (gbnormCore q).length = (DensePoly.toPoly q).natDegree + 1 :=
    gbnormCore_length_eq_natDegree_succ hq'
  set np := (DensePoly.toPoly p).natDegree with hnp
  set nq := (DensePoly.toPoly q).natDegree with hnq
  have hk : (gbnormCore p).length - (gbnormCore q).length = np - nq := by rw [hkp, hkq]; omega
  set A := Polynomial.C ((DensePoly.toPoly q).leadingCoeff) * DensePoly.toPoly p with hA
  set B := Polynomial.C ((DensePoly.toPoly p).leadingCoeff)
    * Polynomial.X ^ (np - nq) * DensePoly.toPoly q with hB
  have hstep : DensePoly.toPoly (gbStepReduce p q) = A - B := by rw [toPolyG_gbStepReduce, hk]
  have hAle : A.natDegree ≤ np := natDegree_C_mul_le _ _
  have hBle : B.natDegree ≤ np := by
    rw [hB]
    refine le_trans natDegree_mul_le ?_
    have h1 : (Polynomial.C ((DensePoly.toPoly p).leadingCoeff) * Polynomial.X ^ (np - nq)).natDegree
        ≤ np - nq := by
      refine le_trans natDegree_mul_le ?_
      rw [natDegree_C, zero_add]
      exact Polynomial.natDegree_X_pow_le _
    omega
  -- coeff = leading at the respective natDegrees (np, nq) — defeq through the `set` lets
  have hpc : (DensePoly.toPoly p).coeff np = (DensePoly.toPoly p).leadingCoeff := by
    rw [hnp, Polynomial.leadingCoeff]
  have hqc : (DensePoly.toPoly q).coeff nq = (DensePoly.toPoly q).leadingCoeff := by
    rw [hnq, Polynomial.leadingCoeff]
  -- the leading-term cancellation: coeff at `np` is `lc(q)·lc(p) − lc(p)·lc(q) = 0`
  have hAcoeff : A.coeff np = (DensePoly.toPoly q).leadingCoeff * (DensePoly.toPoly p).leadingCoeff := by
    rw [hA, coeff_C_mul, hpc]
  have hBcoeff : B.coeff np = (DensePoly.toPoly p).leadingCoeff * (DensePoly.toPoly q).leadingCoeff := by
    rw [hB, mul_assoc, coeff_C_mul]
    congr 1
    have hc := coeff_X_pow_mul (DensePoly.toPoly q) (np - nq) nq
    rw [Nat.add_sub_cancel' hdeg] at hc
    rw [hc, hqc]
  have hcoeffeq : A.coeff np = B.coeff np := by rw [hAcoeff, hBcoeff, mul_comm]
  rw [hstep]
  have hle : (A - B).natDegree ≤ np := le_trans (natDegree_sub_le A B) (max_le hAle hBle)
  have hcn : (A - B).coeff np = 0 := by rw [coeff_sub, hcoeffeq, sub_self]
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · exfalso; rw [← h] at hcn; rw [hstep] at hstepne; exact (leadingCoeff_ne_zero.mpr hstepne) hcn

/-! ### The inner pseudo-division loop completes with adequate fuel

Iterating the dropping step, `gbpsremainderCore` reaches degree `< deg_t q` (or `0`) once the loop fuel
exceeds `deg_t p` — an explicit, satisfiable numeric bound. -/

/-- **A nonzero `GBPolyCore` normalizes to a nonempty list**: `0 < (gbnormCore q).length` from
`DensePoly.cisZero (gbnormCore q) = false`. -/
theorem gbnormCore_length_pos {q : GBPolyCore β} (hq : DensePoly.cisZero (gbnormCore q) = false) :
    0 < (gbnormCore q).length := by
  have hne : gbnormCore q ≠ [] := by
    intro hnorm
    exact DensePoly.toPolyG_ne_zero_of_cisZeroG_false hq (by rw [hnorm, DensePoly.toPolyG_nil])
  exact List.length_pos_iff.mpr hne

/-- **The pseudo-remainder of a zero dividend reads zero**: if `DensePoly.toPoly p = 0` then
`DensePoly.toPoly (gbpsremainderCore fuel p q) = 0`. -/
theorem toPolyG_gbpsremainderCore_eq_zero_of_zero (fuel : ℕ) (p q : GBPolyCore β)
    (hp : DensePoly.toPoly p = 0) : DensePoly.toPoly (gbpsremainderCore fuel p q) = 0 := by
  cases fuel with
  | zero => rw [gbpsremainderCore, toPolyG_gbnormCore]; exact hp
  | succ fuel =>
    have hpnil : gbnormCore p = [] := (gbnormCore_eq_nil_iff_toPolyG p).mpr hp
    rw [gbpsremainderCore]; simp only [hpnil, List.length_nil]
    by_cases hqz : DensePoly.cisZero (gbnormCore q) = true
    · simp [hqz]
    · rw [Bool.not_eq_true] at hqz; simp [hqz, gbnormCore_length_pos hqz]

/-- **The inner pseudo-division loop completes (degree drop) with adequate fuel**: for `q` nonzero and
`(DensePoly.toPoly p).natDegree < fuel`, the pseudo-remainder either drops below `q`'s `t`-degree or is zero:
`(DensePoly.toPoly (gbpsremainderCore fuel p q)).natDegree < (DensePoly.toPoly q).natDegree ∨
DensePoly.toPoly (gbpsremainderCore fuel p q) = 0`. By induction on `fuel`, iterating
`natDegree_gbStepReduce_lt`. -/
theorem gbpsremainderCore_degree_lt (q : GBPolyCore β) (hq : DensePoly.cisZero (gbnormCore q) = false) :
    ∀ (fuel : ℕ) (p : GBPolyCore β), (DensePoly.toPoly p).natDegree < fuel →
      (DensePoly.toPoly (gbpsremainderCore fuel p q)).natDegree < (DensePoly.toPoly q).natDegree
        ∨ DensePoly.toPoly (gbpsremainderCore fuel p q) = 0 := by
  have hqnz : DensePoly.cisZero q = false := by rwa [cisZero_gbnormCore] at hq
  have hql : (gbnormCore q).length = (DensePoly.toPoly q).natDegree + 1 :=
    gbnormCore_length_eq_natDegree_succ hqnz
  have hqpos : 0 < (gbnormCore q).length := gbnormCore_length_pos hq
  intro fuel
  induction fuel with
  | zero => intro p hlt; omega
  | succ fuel ih =>
    intro p hlt
    rw [gbpsremainderCore]; simp only [hq, Bool.false_eq_true, if_false]
    by_cases hlen : (gbnormCore p).length < (gbnormCore q).length
    · -- the loop exits: the (normalized) dividend already has degree below `q` (or is zero)
      rw [if_pos hlen, toPolyG_gbnormCore]
      by_cases hpz : DensePoly.toPoly p = 0
      · right; exact hpz
      · left
        have hpnz : DensePoly.cisZero p = false := by
          rw [Bool.eq_false_iff, Ne, DensePoly.cisZeroG_iff]; exact hpz
        have hpl := gbnormCore_length_eq_natDegree_succ hpnz
        omega
    · -- the loop steps: recurse on the (strictly lower degree) step body `p'`
      -- the engine recurses with divisor `gbnormCore q`; normalize it back to `q` for the IH
      rw [if_neg hlen, ← gbpsremainderCore_gbnormCore_right]
      have hpnz : DensePoly.cisZero p = false := by
        rw [Bool.eq_false_iff, Ne, DensePoly.cisZeroG_iff]
        intro hh
        have hpnil : gbnormCore p = [] := (gbnormCore_eq_nil_iff_toPolyG p).mpr hh
        rw [hpnil, List.length_nil] at hlen; omega
      have hpl := gbnormCore_length_eq_natDegree_succ hpnz
      have hdle : (DensePoly.toPoly (gbnormCore q)).natDegree ≤ (DensePoly.toPoly (gbnormCore p)).natDegree := by
        rw [toPolyG_gbnormCore, toPolyG_gbnormCore]; omega
      set p' := gbnormCore (DensePoly.csub (DensePoly.cscale (gblcCore (gbnormCore q)) (gbnormCore p))
        (DensePoly.cscale (gblcCore (gbnormCore p))
          (DensePoly.cshift ((gbnormCore p).length - (gbnormCore q).length) (gbnormCore q)))) with hp'def
      have hp'read : DensePoly.toPoly p' = DensePoly.toPoly (gbStepReduce (gbnormCore p) (gbnormCore q)) := by
        rw [hp'def, toPolyG_gbnormCore, gbStepReduce, DensePoly.toPolyG_csubG,
          DensePoly.toPolyG_csubG, DensePoly.toPolyG_cscaleG, DensePoly.toPolyG_cscaleG,
          DensePoly.toPolyG_cscaleG, DensePoly.toPolyG_cscaleG, DensePoly.toPolyG_cshiftG,
          DensePoly.toPolyG_cshiftG, gbnormCore_idemp, gbnormCore_idemp]
      by_cases hp'z : DensePoly.toPoly p' = 0
      · right; rw [toPolyG_gbpsremainderCore_eq_zero_of_zero fuel p' q hp'z]
      · have hpnn : DensePoly.cisZero (gbnormCore (gbnormCore p)) = false := by
          rw [cisZero_gbnormCore, cisZero_gbnormCore]; exact hpnz
        have hqnn : DensePoly.cisZero (gbnormCore (gbnormCore q)) = false := by
          rw [cisZero_gbnormCore]; exact hq
        have hdegstep : (DensePoly.toPoly p').natDegree < (DensePoly.toPoly p).natDegree := by
          rw [hp'read]
          have h := natDegree_gbStepReduce_lt (gbnormCore p) (gbnormCore q) hpnn hqnn
            hdle (by rw [← hp'read]; exact hp'z)
          rwa [toPolyG_gbnormCore] at h
        exact ih p' (by omega)

/-- **`toGBPoly` preserves the `t`-degree of `DensePoly.toPoly`**: `(toGBPoly p).natDegree =
(DensePoly.toPoly p).natDegree`. The coefficient lift `liftK = mapRingHom (am β)` is over the injective
field embedding `am β`, so `Polynomial.natDegree_map` applies. -/
theorem natDegree_toGBPolyG (p : GBPolyCore β) :
    (toGBPoly p).natDegree = (DensePoly.toPoly p).natDegree := by
  rw [toGBPoly, liftK, Polynomial.coe_mapRingHom,
    Polynomial.natDegree_map_eq_of_injective (RatFunc.algebraMap_injective (CFieldSpec.K β))]

/-- **The content strip preserves the `t`-degree**: under `CgcdBCorrect cgcdB`,
`(DensePoly.toPoly (gbprimitivePartCore cgcdB p)).natDegree = (DensePoly.toPoly p).natDegree`
(the strip is a `β(s)`-unit scaling, and `Associated` polynomials over `β(s)` have equal `natDegree`). -/
theorem natDegree_toPolyG_gbprimitivePartCore
    (cgcdB : DensePoly β → DensePoly β → DensePoly β) (hcorr : CgcdBCorrect cgcdB) (p : GBPolyCore β) :
    (DensePoly.toPoly (gbprimitivePartCore cgcdB p)).natDegree = (DensePoly.toPoly p).natDegree := by
  have hassoc := associated_toGBPolyG_gbprimitivePartCore_total cgcdB hcorr p
  have := natDegree_eq_of_associated hassoc
  rwa [natDegree_toGBPolyG, natDegree_toGBPolyG] at this

/-- **The list-length loop guard is exactly the pseudo-remainder `t`-degree drop**: under `CgcdBCorrect
cgcdB`, `Q` nonzero, and the stripped node nonzero (`hrz`), the
`CPrimPRSGenRegular`-`step` guard
`(gbnormCore (gbprimitivePartCore cgcdB prem)).length < (gbnormCore Q).length`
holds iff `(DensePoly.toPoly prem).natDegree < (DensePoly.toPoly Q).natDegree`. -/
theorem gbnormGuard_iff_premDegree (cgcdB : DensePoly β → DensePoly β → DensePoly β) (hcorr : CgcdBCorrect cgcdB)
    (P Q : GBPolyCore β) (hQ : DensePoly.cisZero (gbnormCore Q) = false)
    (hrz : DensePoly.cisZero (gbprimitivePartCore cgcdB
      (gbpsremainderCore (gbnormCore P).length (gbnormCore P) (gbnormCore Q))) = false) :
    ((gbnormCore (gbprimitivePartCore cgcdB
        (gbpsremainderCore (gbnormCore P).length (gbnormCore P) (gbnormCore Q)))).length
          < (gbnormCore Q).length)
      ↔ (DensePoly.toPoly (gbpsremainderCore (gbnormCore P).length
          (gbnormCore P) (gbnormCore Q))).natDegree
          < (DensePoly.toPoly (gbnormCore Q)).natDegree := by
  -- `DensePoly.cisZero Q = false` (idempotence) to apply the length lemma on the outer `gbnormCore Q`
  have hQ' : DensePoly.cisZero Q = false := by rwa [cisZero_gbnormCore] at hQ
  rw [gbnormCore_length_eq_natDegree_succ hrz, gbnormCore_length_eq_natDegree_succ hQ',
    Nat.add_lt_add_iff_right,
    natDegree_toPolyG_gbprimitivePartCore cgcdB hcorr _, toPolyG_gbnormCore]

end DeepWiki.SymbolicIntegration
