import DeepWiki.SymbolicIntegration.Engine.PrimPRSRegular.Content
import DeepWiki.SymbolicIntegration.Engine.SplitFactorHelpers

/-! # Primitive PRS regularity: degree control

Normalized-length readings, pseudo-division degree drops, and primitive-part degree preservation.
-/

open Polynomial Classical

namespace DeepWiki.SymbolicIntegration

open DensePoly GBPolyCore

variable {β : Type*} [CField β] [CFieldSpec β]

/-! ## The `t`-degree is the normalized list length

`gbdegCore p = (toGBCoeffPoly p).natDegree` turns the list-length loop guard into a polynomial
`t`-degree statement over the integral domain `R = (CFieldSpec.K β)[X]`. -/

/-- **`(toGBCoeffPoly p).natDegree` is bounded by the normalized `t`-length**:
`(toGBCoeffPoly p).natDegree ≤ (gbnormCore p).length − 1`. The `GBPolyCore` mirror of
`natDegree_toPolyG_le` — coefficients past `(gbnormCore p).length` read `toPoly [] = 0`. -/
theorem natDegree_toGBCoeffPoly_le (p : GBPolyCore β) :
    (toGBCoeffPoly p).natDegree ≤ (gbnormCore p).length - 1 := by
  rw [← toGBCoeffPoly_gbnormCore]
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro m hm
  rw [toGBCoeffPoly_coeff, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega),
    Option.getD_none, toPolyG_nil]

/-- **The `t`-degree is the normalized list length** `gbdegCore p = (toGBCoeffPoly p).natDegree`, the
`GBPolyCore` mirror of `cdegG_eq_natDegree`. -/
theorem gbdegCore_eq_natDegree (p : GBPolyCore β) : gbdegCore p = (toGBCoeffPoly p).natDegree := by
  rcases eq_or_ne (gbnormCore p) [] with h | h
  · have h0 : toGBCoeffPoly p = 0 := by rw [← toGBCoeffPoly_gbnormCore, h, toGBCoeffPoly_nil]
    rw [gbdegCore, h, h0]; simp
  · refine le_antisymm ?_ (natDegree_toGBCoeffPoly_le p)
    apply Polynomial.le_natDegree_of_ne_zero
    rw [← toPolyG_gblcCore_eq_coeff]
    -- `gblcCore p` (the top normalized coefficient) reads nonzero
    have hz : gbisZeroCore p = false := by
      rw [gbisZeroCore, List.isEmpty_eq_false_iff_exists_mem]
      obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ h
      exact ⟨a, ha⟩
    exact toPolyG_gblcCore_ne_zero hz

/-- **The normalized `t`-length equals `natDegree + 1` for a nonzero `GBPolyCore`**: if
`gbisZeroCore p = false`, then `(gbnormCore p).length = (toGBCoeffPoly p).natDegree + 1`. -/
theorem gbnormCore_length_eq_natDegree_succ {p : GBPolyCore β} (hp : gbisZeroCore p = false) :
    (gbnormCore p).length = (toGBCoeffPoly p).natDegree + 1 := by
  have hne : gbnormCore p ≠ [] := by
    rw [gbisZeroCore, List.isEmpty_eq_false_iff_exists_mem] at hp
    obtain ⟨a, ha⟩ := hp
    exact List.ne_nil_of_mem ha
  have hpos : 1 ≤ (gbnormCore p).length := List.length_pos_iff.mpr hne
  have := gbdegCore_eq_natDegree p
  rw [gbdegCore] at this
  omega

/-! ## Sharpening termination: the pseudo-division degree drop as a theorem

The content strip preserves the `t`-degree, and the single loop body `lc(q)·p − lc(p)·tᵏ·q` strictly
drops the `t`-degree over the integral domain `R = (CFieldSpec.K β)[X]`, so termination's only remaining
conditional ingredient is the fuel-bounded loop completing. -/

/-- **`toPoly (gblcCore (gbnormCore p))` is the leading coefficient of `toGBCoeffPoly p`**, via
`toPolyG_gblcCore_eq_coeff` and `gbdegCore_eq_natDegree`. -/
theorem toPolyG_gblcCore_eq_leadingCoeff (p : GBPolyCore β) :
    DensePoly.toPoly (gblcCore (gbnormCore p)) = (toGBCoeffPoly p).leadingCoeff := by
  rw [Polynomial.leadingCoeff, ← gbdegCore_eq_natDegree, toPolyG_gblcCore_eq_coeff,
    toGBCoeffPoly_gbnormCore]
  congr 1
  rw [gbdegCore, gbdegCore, gbnormCore_idemp]

/-- **The single pseudo-division step body** `gbStepReduce p q = lc(q)·p − lc(p)·tᵏ·q`
(`k = (gbnormCore p).length − (gbnormCore q).length`): one leading-term elimination of
`gbpsremainderCore`. -/
noncomputable def gbStepReduce (p q : GBPolyCore β) : GBPolyCore β :=
  DensePoly.csub (DensePoly.cscale (gblcCore (gbnormCore q)) p)
    (DensePoly.cscale (gblcCore (gbnormCore p))
      (DensePoly.cshift ((gbnormCore p).length - (gbnormCore q).length) q))

/-- **The `R[t]` reading of a step body** `toGBCoeffPoly (gbStepReduce p q) = C(lc q)·toGBCoeffPoly p −
C(lc p)·tᵏ·toGBCoeffPoly q` (`R = (CFieldSpec.K β)[X]`, `k = deg_t p − deg_t q`). -/
theorem toGBCoeffPoly_gbStepReduce (p q : GBPolyCore β) :
    toGBCoeffPoly (gbStepReduce p q)
      = Polynomial.C ((toGBCoeffPoly q).leadingCoeff) * toGBCoeffPoly p
        - Polynomial.C ((toGBCoeffPoly p).leadingCoeff)
          * Polynomial.X ^ ((gbnormCore p).length - (gbnormCore q).length) * toGBCoeffPoly q := by
  rw [gbStepReduce, toGBCoeffPoly_csub, toGBCoeffPoly_cscale, toGBCoeffPoly_cscale,
    toGBCoeffPoly_cshift, toPolyG_gblcCore_eq_leadingCoeff, toPolyG_gblcCore_eq_leadingCoeff]
  ring

/-- **The single pseudo-division step strictly drops the `t`-degree** (the leading-term cancellation):
for nonzero `p, q` with `deg_t q ≤ deg_t p`, if `gbStepReduce p q` is nonzero then
`(toGBCoeffPoly (gbStepReduce p q)).natDegree < (toGBCoeffPoly p).natDegree`. -/
theorem natDegree_gbStepReduce_lt (p q : GBPolyCore β)
    (hp : gbisZeroCore (gbnormCore p) = false) (hq : gbisZeroCore (gbnormCore q) = false)
    (hdeg : (toGBCoeffPoly q).natDegree ≤ (toGBCoeffPoly p).natDegree)
    (hstepne : toGBCoeffPoly (gbStepReduce p q) ≠ 0) :
    (toGBCoeffPoly (gbStepReduce p q)).natDegree < (toGBCoeffPoly p).natDegree := by
  have hp' : gbisZeroCore p = false := by rw [gbisZeroCore, ← gbnormCore_idemp, ← gbisZeroCore]; exact hp
  have hq' : gbisZeroCore q = false := by rw [gbisZeroCore, ← gbnormCore_idemp, ← gbisZeroCore]; exact hq
  have hkp : (gbnormCore p).length = (toGBCoeffPoly p).natDegree + 1 :=
    gbnormCore_length_eq_natDegree_succ hp'
  have hkq : (gbnormCore q).length = (toGBCoeffPoly q).natDegree + 1 :=
    gbnormCore_length_eq_natDegree_succ hq'
  set np := (toGBCoeffPoly p).natDegree with hnp
  set nq := (toGBCoeffPoly q).natDegree with hnq
  have hk : (gbnormCore p).length - (gbnormCore q).length = np - nq := by rw [hkp, hkq]; omega
  set A := Polynomial.C ((toGBCoeffPoly q).leadingCoeff) * toGBCoeffPoly p with hA
  set B := Polynomial.C ((toGBCoeffPoly p).leadingCoeff)
    * Polynomial.X ^ (np - nq) * toGBCoeffPoly q with hB
  have hstep : toGBCoeffPoly (gbStepReduce p q) = A - B := by rw [toGBCoeffPoly_gbStepReduce, hk]
  have hAle : A.natDegree ≤ np := natDegree_C_mul_le _ _
  have hBle : B.natDegree ≤ np := by
    rw [hB]
    refine le_trans natDegree_mul_le ?_
    have h1 : (Polynomial.C ((toGBCoeffPoly p).leadingCoeff) * Polynomial.X ^ (np - nq)).natDegree
        ≤ np - nq := le_trans natDegree_mul_le (by simp [natDegree_C])
    omega
  -- coeff = leading at the respective natDegrees (np, nq) — defeq through the `set` lets
  have hpc : (toGBCoeffPoly p).coeff np = (toGBCoeffPoly p).leadingCoeff := by
    rw [hnp, Polynomial.leadingCoeff]
  have hqc : (toGBCoeffPoly q).coeff nq = (toGBCoeffPoly q).leadingCoeff := by
    rw [hnq, Polynomial.leadingCoeff]
  -- the leading-term cancellation: coeff at `np` is `lc(q)·lc(p) − lc(p)·lc(q) = 0`
  have hAcoeff : A.coeff np = (toGBCoeffPoly q).leadingCoeff * (toGBCoeffPoly p).leadingCoeff := by
    rw [hA, coeff_C_mul, hpc]
  have hBcoeff : B.coeff np = (toGBCoeffPoly p).leadingCoeff * (toGBCoeffPoly q).leadingCoeff := by
    rw [hB, mul_assoc, coeff_C_mul]
    congr 1
    have hc := coeff_X_pow_mul (toGBCoeffPoly q) (np - nq) nq
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

omit [CFieldSpec β] in
/-- **`gbisZeroCore` is `gbnormCore`-invariant**: `gbisZeroCore (gbnormCore p) = `gbisZeroCore p`. -/
theorem gbisZeroCore_gbnormCore (p : GBPolyCore β) : gbisZeroCore (gbnormCore p) = gbisZeroCore p := by
  rw [gbisZeroCore, gbisZeroCore, gbnormCore_idemp]

omit [CFieldSpec β] in
/-- **A nonzero `GBPolyCore` normalizes to a nonempty list**: `0 < (gbnormCore q).length` from
`gbisZeroCore (gbnormCore q) = false`. -/
theorem gbnormCore_length_pos {q : GBPolyCore β} (hq : gbisZeroCore (gbnormCore q) = false) :
    0 < (gbnormCore q).length := by
  have hne : gbnormCore q ≠ [] := by
    rw [gbisZeroCore, List.isEmpty_eq_false_iff_exists_mem, gbnormCore_idemp] at hq
    obtain ⟨a, ha⟩ := hq; exact List.ne_nil_of_mem ha
  exact List.length_pos_iff.mpr hne

/-- **The pseudo-remainder of a zero dividend reads zero**: if `toGBCoeffPoly p = 0` then
`toGBCoeffPoly (gbpsremainderCore fuel p q) = 0`. -/
theorem toGBCoeffPoly_gbpsremainderCore_eq_zero_of_zero (fuel : ℕ) (p q : GBPolyCore β)
    (hp : toGBCoeffPoly p = 0) : toGBCoeffPoly (gbpsremainderCore fuel p q) = 0 := by
  cases fuel with
  | zero => rw [gbpsremainderCore, toGBCoeffPoly_gbnormCore]; exact hp
  | succ fuel =>
    have hpnil : gbnormCore p = [] := by
      rw [← gbisZeroCore_iff_toGBCoeffPoly, gbisZeroCore, List.isEmpty_iff] at hp; exact hp
    rw [gbpsremainderCore]; simp only [hpnil, List.length_nil]
    by_cases hqz : gbisZeroCore (gbnormCore q) = true
    · simp [hqz]
    · rw [Bool.not_eq_true] at hqz; simp [hqz, gbnormCore_length_pos hqz]

/-- **The inner pseudo-division loop completes (degree drop) with adequate fuel**: for `q` nonzero and
`(toGBCoeffPoly p).natDegree < fuel`, the pseudo-remainder either drops below `q`'s `t`-degree or is zero:
`(toGBCoeffPoly (gbpsremainderCore fuel p q)).natDegree < (toGBCoeffPoly q).natDegree ∨
toGBCoeffPoly (gbpsremainderCore fuel p q) = 0`. By induction on `fuel`, iterating
`natDegree_gbStepReduce_lt`. -/
theorem gbpsremainderCore_degree_lt (q : GBPolyCore β) (hq : gbisZeroCore (gbnormCore q) = false) :
    ∀ (fuel : ℕ) (p : GBPolyCore β), (toGBCoeffPoly p).natDegree < fuel →
      (toGBCoeffPoly (gbpsremainderCore fuel p q)).natDegree < (toGBCoeffPoly q).natDegree
        ∨ toGBCoeffPoly (gbpsremainderCore fuel p q) = 0 := by
  have hqnz : gbisZeroCore q = false := by
    rw [gbisZeroCore, ← gbnormCore_idemp, ← gbisZeroCore]; exact hq
  have hql : (gbnormCore q).length = (toGBCoeffPoly q).natDegree + 1 :=
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
      rw [if_pos hlen, toGBCoeffPoly_gbnormCore]
      by_cases hpz : toGBCoeffPoly p = 0
      · right; exact hpz
      · left
        have hpnz : gbisZeroCore p = false := by
          rw [Bool.eq_false_iff, Ne, gbisZeroCore_iff_toGBCoeffPoly]; exact hpz
        have hpl := gbnormCore_length_eq_natDegree_succ hpnz
        omega
    · -- the loop steps: recurse on the (strictly lower degree) step body `p'`
      -- the engine recurses with divisor `gbnormCore q`; normalize it back to `q` for the IH
      rw [if_neg hlen, ← gbpsremainderCore_gbnormCore_right]
      have hpnz : gbisZeroCore p = false := by
        rw [Bool.eq_false_iff, Ne, gbisZeroCore_iff_toGBCoeffPoly]
        intro hh
        have hpnil : gbnormCore p = [] := by
          rw [← gbisZeroCore_iff_toGBCoeffPoly, gbisZeroCore, List.isEmpty_iff] at hh; exact hh
        rw [hpnil, List.length_nil] at hlen; omega
      have hpl := gbnormCore_length_eq_natDegree_succ hpnz
      have hdle : (toGBCoeffPoly (gbnormCore q)).natDegree ≤ (toGBCoeffPoly (gbnormCore p)).natDegree := by
        rw [toGBCoeffPoly_gbnormCore, toGBCoeffPoly_gbnormCore]; omega
      set p' := gbnormCore (DensePoly.csub (DensePoly.cscale (gblcCore (gbnormCore q)) (gbnormCore p))
        (DensePoly.cscale (gblcCore (gbnormCore p))
          (DensePoly.cshift ((gbnormCore p).length - (gbnormCore q).length) (gbnormCore q)))) with hp'def
      have hp'read : toGBCoeffPoly p' = toGBCoeffPoly (gbStepReduce (gbnormCore p) (gbnormCore q)) := by
        rw [hp'def, toGBCoeffPoly_gbnormCore, gbStepReduce, toGBCoeffPoly_csub,
          toGBCoeffPoly_csub, toGBCoeffPoly_cscale, toGBCoeffPoly_cscale,
          toGBCoeffPoly_cscale, toGBCoeffPoly_cscale, toGBCoeffPoly_cshift,
          toGBCoeffPoly_cshift, gbnormCore_idemp, gbnormCore_idemp]
      by_cases hp'z : toGBCoeffPoly p' = 0
      · right; rw [toGBCoeffPoly_gbpsremainderCore_eq_zero_of_zero fuel p' q hp'z]
      · have hpnn : gbisZeroCore (gbnormCore (gbnormCore p)) = false := by
          rw [gbisZeroCore_gbnormCore, gbisZeroCore_gbnormCore]; exact hpnz
        have hqnn : gbisZeroCore (gbnormCore (gbnormCore q)) = false := by
          rw [gbisZeroCore_gbnormCore]; exact hq
        have hdegstep : (toGBCoeffPoly p').natDegree < (toGBCoeffPoly p).natDegree := by
          rw [hp'read]
          have h := natDegree_gbStepReduce_lt (gbnormCore p) (gbnormCore q) hpnn hqnn
            hdle (by rw [← hp'read]; exact hp'z)
          rwa [toGBCoeffPoly_gbnormCore] at h
        exact ih p' (by omega)

/-- **`toGBPoly` preserves the `t`-degree of `toGBCoeffPoly`**: `(toGBPoly p).natDegree =
(toGBCoeffPoly p).natDegree`. The coefficient lift `liftK = mapRingHom (am β)` is over the injective
field embedding `am β`, so `Polynomial.natDegree_map` applies. -/
theorem natDegree_toGBPolyG (p : GBPolyCore β) :
    (toGBPoly p).natDegree = (toGBCoeffPoly p).natDegree := by
  rw [toGBPoly, liftK, Polynomial.coe_mapRingHom,
    Polynomial.natDegree_map_eq_of_injective (RatFunc.algebraMap_injective (CFieldSpec.K β))]

/-- **The content strip preserves the `t`-degree**: under `CgcdBCorrect cgcdB` and the per-coefficient
size bound, `(toGBCoeffPoly (gbprimitivePartCore cgcdB p)).natDegree = (toGBCoeffPoly p).natDegree`
(the strip is a `β(s)`-unit scaling, and `Associated` polynomials over `β(s)` have equal `natDegree`). -/
theorem natDegree_toGBCoeffPoly_gbprimitivePartCore (fuel : ℕ)
    (cgcdB : DensePoly β → DensePoly β → DensePoly β) (hcorr : CgcdBCorrect cgcdB) (p : GBPolyCore β)
    (hfuel : ∀ a ∈ gbnormCore p, (DensePoly.cnorm a : List β).length ≤ fuel) :
    (toGBCoeffPoly (gbprimitivePartCore cgcdB p)).natDegree = (toGBCoeffPoly p).natDegree := by
  have hassoc := associated_toGBPolyG_gbprimitivePartCore_total fuel cgcdB hcorr p hfuel
  have := natDegree_eq_of_associated hassoc
  rwa [natDegree_toGBPolyG, natDegree_toGBPolyG] at this

/-- **The list-length loop guard is exactly the pseudo-remainder `t`-degree drop**: under `CgcdBCorrect
cgcdB`, the retained size bound on `prem`, `Q` nonzero, and the stripped node nonzero (`hrz`), the
`CPrimPRSGenRegular`-`step` guard
`(gbnormCore (gbprimitivePartCore cgcdB prem)).length < (gbnormCore Q).length`
holds iff `(toGBCoeffPoly prem).natDegree < (toGBCoeffPoly Q).natDegree`. -/
theorem gbnormGuard_iff_premDegree (cgcdB : DensePoly β → DensePoly β → DensePoly β) (hcorr : CgcdBCorrect cgcdB)
    (P Q : GBPolyCore β) (hQ : gbisZeroCore (gbnormCore Q) = false)
    (hfuel : ∀ a ∈ gbnormCore (gbpsremainderCore 60 (gbnormCore P) (gbnormCore Q)),
      (DensePoly.cnorm a : List β).length ≤ 30)
    (hrz : gbisZeroCore (gbprimitivePartCore cgcdB
      (gbpsremainderCore 60 (gbnormCore P) (gbnormCore Q))) = false) :
    ((gbnormCore (gbprimitivePartCore cgcdB
        (gbpsremainderCore 60 (gbnormCore P) (gbnormCore Q)))).length < (gbnormCore Q).length)
      ↔ (toGBCoeffPoly (gbpsremainderCore 60 (gbnormCore P) (gbnormCore Q))).natDegree
          < (toGBCoeffPoly (gbnormCore Q)).natDegree := by
  -- `gbisZeroCore Q = false` (idempotence) to apply the length lemma on the outer `gbnormCore Q`
  have hQ' : gbisZeroCore Q = false := by rw [gbisZeroCore, ← gbnormCore_idemp, ← gbisZeroCore]; exact hQ
  rw [gbnormCore_length_eq_natDegree_succ hrz, gbnormCore_length_eq_natDegree_succ hQ',
    Nat.add_lt_add_iff_right,
    natDegree_toGBCoeffPoly_gbprimitivePartCore 30 cgcdB hcorr _ hfuel, toGBCoeffPoly_gbnormCore]

end DeepWiki.SymbolicIntegration
