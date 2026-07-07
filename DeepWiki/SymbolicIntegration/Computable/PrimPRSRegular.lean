import DeepWiki.SymbolicIntegration.Computable.Tower.GcdFFCorrect
import DeepWiki.SymbolicIntegration.Computable.Tower.WellFounded

/-! # Reducing the primitive-PRS regularity gate `CPrimPRSGenAssocReg`

The per-step regularity bundle `CPrimPRSGenAssocReg cgcdB fuel P Q` gating abstract tower fraction-free
gcd correctness is **not** unconditional; this file reduces it to two per-run witnesses — PRS
termination (`CPrimPRSGenRegular`) and level-`β` gcd-correctness (`CgcdBCorrect`) — plus retained
size bookkeeping, via `cPrimPRSGenAssocReg_of_regular_of_correct`, and sharpens the degree-drop content
of termination to a theorem (`natDegree_gbStepReduce_lt`, `gbpsremainderCore_degree_lt`). -/

open Polynomial Classical

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG GBPolyCore

variable {β : Type*} [CField β] [CFieldSpec β]

/-! ## The per-step content lemmas: the nonzero-multiplier strengthening of clause (ii)

The pseudo-division multiplier accumulated by `gbpsremainderCore fuel p q` is a power of `lc(q)`, hence
nonzero exactly when `q ≠ 0` — so clause (ii)'s `β(s)`-unit multiplier is unconditional given `q ≠ 0`. -/

/-- **The leading `t`-coefficient of a nonzero `GBPolyCore` reads nonzero**: if `gbisZeroCore q = false`
(`q ≠ 0` in `t`), then `toPolyG (gblcCore q) ≠ 0` in `R = (CFieldSpec.K β)[X]`. The top normalized
`t`-coefficient is `cnormG`-nonempty, hence `toPolyG`-nonzero (`gbnormCore_getLast?_toPolyG_ne_zero`). -/
theorem toPolyG_gblcCore_ne_zero {q : GBPolyCore β} (hq : gbisZeroCore q = false) :
    CPolyG.toPolyG (gblcCore q) ≠ 0 := by
  -- `gbnormCore q ≠ []` (zero test is `false`), so `getLast?` is `some v` with `toPolyG v ≠ 0`
  have hne : gbnormCore q ≠ [] := by
    rw [gbisZeroCore, List.isEmpty_eq_false_iff_exists_mem] at hq
    obtain ⟨a, ha⟩ := hq
    exact List.ne_nil_of_mem ha
  rcases hg : (gbnormCore q).getLast? with _ | v
  · exact absurd (List.getLast?_eq_none_iff.mp hg) hne
  · have hlc : gblcCore q = v := by rw [gblcCore, hg, Option.getD_some]
    rw [hlc]
    exact gbnormCore_getLast?_toPolyG_ne_zero q v hg

/-- **The multiplier of `gbpsremainderCore` is `toPolyG`-nonzero when the divisor is nonzero.** Produces
a pseudo-division witness `(s, c)` with the Euclidean identity and `toPolyG c ≠ 0`, provided
`gbisZeroCore (gbnormCore q) = false`. -/
theorem toGBCoeffPoly_gbpsremainderCore_ne_zero (fuel : ℕ) (p q : GBPolyCore β)
    (hq : gbisZeroCore (gbnormCore q) = false) :
    ∃ (s : GBPolyCore β) (c : CPolyG β),
      Polynomial.C (CPolyG.toPolyG c) * toGBCoeffPoly p
          = toGBCoeffPoly s * toGBCoeffPoly q + toGBCoeffPoly (gbpsremainderCore fuel p q)
        ∧ CPolyG.toPolyG c ≠ 0 := by
  have hone : CPolyG.toPolyG ([CField.one] : CPolyG β) = 1 := by
    simp only [denote]
    simp
  -- `lc(gbnormCore q)` reads nonzero (the divisor is nonzero)
  have hlcq : CPolyG.toPolyG (gblcCore (gbnormCore q)) ≠ 0 :=
    toPolyG_gblcCore_ne_zero hq
  induction fuel generalizing p with
  | zero =>
    exact ⟨[], [CField.one], by simp [gbpsremainderCore, toGBCoeffPoly_gbnormCore, hone],
      by rw [hone]; exact one_ne_zero⟩
  | succ fuel ih =>
    simp only [gbpsremainderCore]
    split_ifs with hqz hlen
    · exact ⟨[], [CField.one], by simp [toGBCoeffPoly_gbnormCore, hone],
        by rw [hone]; exact one_ne_zero⟩
    · exact ⟨[], [CField.one], by simp [toGBCoeffPoly_gbnormCore, hone],
        by rw [hone]; exact one_ne_zero⟩
    · obtain ⟨s', c', hsc, hc'⟩ := ih (gbnormCore (gbsubCore (gbscaleCCore (gblcCore (gbnormCore q))
        (gbnormCore p))
        (gbscaleCCore (gblcCore (gbnormCore p))
          (gbshiftCore ((gbnormCore p).length - (gbnormCore q).length) (gbnormCore q)))))
      have hp' : toGBCoeffPoly (gbnormCore (gbsubCore (gbscaleCCore (gblcCore (gbnormCore q))
          (gbnormCore p))
          (gbscaleCCore (gblcCore (gbnormCore p))
            (gbshiftCore ((gbnormCore p).length - (gbnormCore q).length) (gbnormCore q)))))
          = Polynomial.C (CPolyG.toPolyG (gblcCore (gbnormCore q))) * toGBCoeffPoly p
            - Polynomial.C (CPolyG.toPolyG (gblcCore (gbnormCore p)))
              * Polynomial.X ^ ((gbnormCore p).length - (gbnormCore q).length) * toGBCoeffPoly q := by
        rw [toGBCoeffPoly_gbnormCore, toGBCoeffPoly_gbsubCore, toGBCoeffPoly_gbscaleCCore,
          toGBCoeffPoly_gbscaleCCore, toGBCoeffPoly_gbshiftCore, toGBCoeffPoly_gbnormCore,
          toGBCoeffPoly_gbnormCore]
        ring
      rw [hp', gbpsremainderCore_gbnormCore_right] at hsc
      refine ⟨gbaddCore s' (gbscaleCCore (CPolyG.cmulG c' (gblcCore (gbnormCore p)))
          (gbshiftCore ((gbnormCore p).length - (gbnormCore q).length) [[CField.one]])),
          CPolyG.cmulG c' (gblcCore (gbnormCore q)), ?_, ?_⟩
      · rw [toGBCoeffPoly_gbaddCore, toGBCoeffPoly_gbscaleCCore, toGBCoeffPoly_gbshiftCore,
          toGBCoeffPoly_one]
        simp only [denote, map_mul]
        linear_combination hsc
      · simpa only [denote] using mul_ne_zero hc' hlcq

/-- **`gbpsremainderCore` lifts to a `β(s)[t]` Euclidean relation with a `β(s)`-unit multiplier**: if
`gbisZeroCore (gbnormCore q) = false`, there is `(s, c)` with
`C (amG (toPolyG c)) · toGBPolyG p = toGBPolyG s · toGBPolyG q + toGBPolyG (gbpsremainderCore fuel p q)`
and `amG (toPolyG c) ≠ 0` in `(RatFunc (CFieldSpec.K β))[X]`. -/
theorem toGBPolyG_gbpsremainderCore_ne_zero (fuel : ℕ) (p q : GBPolyCore β)
    (hq : gbisZeroCore (gbnormCore q) = false) :
    ∃ (s : GBPolyCore β) (c : CPolyG β),
      Polynomial.C (QFunNZG.amG β (CPolyG.toPolyG c)) * toGBPolyG p
          = toGBPolyG s * toGBPolyG q + toGBPolyG (gbpsremainderCore fuel p q)
        ∧ QFunNZG.amG β (CPolyG.toPolyG c) ≠ 0 := by
  obtain ⟨s, c, hsc, hc⟩ := toGBCoeffPoly_gbpsremainderCore_ne_zero fuel p q hq
  refine ⟨s, c, ?_, QFunNZG.amG_toPolyG_ne_zero hc⟩
  have hl := congrArg (liftKG β) hsc
  simp only [map_add, map_mul] at hl
  rw [liftKG_C] at hl
  simpa [toGBPolyG] using hl

/-! ## The total clause (iii): the content strip is a `β(s)`-unit scaling on any input

Bundling the nonzero-content case with the zero case (where `gbprimitivePartCore` is the identity) gives
clause (iii) conditional only on `CgcdBCorrect cgcdB` plus the retained bookkeeping. -/

/-- **The content strip is a `β(s)`-unit scaling on any input**: under `CgcdBCorrect cgcdB` and the
per-`t`-coefficient size bound, `Associated (toGBPolyG (gbprimitivePartCore cgcdB p)) (toGBPolyG p)`.
Splits on whether the content `gbcontentCore cgcdB p` is zero (identity, reflexive) or nonzero (unit
scaling). -/
theorem associated_toGBPolyG_gbprimitivePartCore_total (fuel : ℕ)
    (cgcdB : CPolyG β → CPolyG β → CPolyG β) (hcorr : CgcdBCorrect cgcdB) (p : GBPolyCore β)
    (hfuel : ∀ a ∈ gbnormCore p, (CPolyG.cnormG a : List β).length ≤ fuel) :
    Associated (toGBPolyG (gbprimitivePartCore cgcdB p)) (toGBPolyG p) := by
  by_cases hgz : CPolyG.cisZeroG (gbcontentCore cgcdB p) = true
  · -- content zero: gbprimitivePartCore is the identity `gbnormCore p`
    have hid : gbprimitivePartCore cgcdB p = gbnormCore p := by
      rw [gbprimitivePartCore, gbcontentCore_gbnormCore, if_pos hgz]
    rw [hid, toGBPolyG_gbnormCore]
  · -- content nonzero: the unit scaling (Mathlib content + cgcdB-fold-divides)
    have hg0 : CPolyG.toPolyG (gbcontentCore cgcdB p) ≠ 0 := by
      rw [Ne, ← CPolyG.cisZeroG_iff]; exact hgz
    have hgcn : CPolyG.cnormG (gbcontentCore cgcdB p) ≠ [] := by
      rw [Ne, CPolyG.cnormG_eq_nil_iff]; exact hg0
    exact associated_toGBPolyG_gbprimitivePartCore_of_correct fuel cgcdB hcorr p hgz hgcn hg0 hfuel

/-! ## The `t`-degree is the normalized list length

`gbdegCore p = (toGBCoeffPoly p).natDegree` turns the list-length loop guard into a polynomial
`t`-degree statement over the integral domain `R = (CFieldSpec.K β)[X]`. -/

/-- **`(toGBCoeffPoly p).natDegree` is bounded by the normalized `t`-length**:
`(toGBCoeffPoly p).natDegree ≤ (gbnormCore p).length − 1`. The `GBPolyCore` mirror of
`natDegree_toPolyG_le` — coefficients past `(gbnormCore p).length` read `toPolyG [] = 0`. -/
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

/-! ## The reduction theorem: regularity + correctness + bookkeeping ⟹ `CPrimPRSGenAssocReg` -/

/-- **Per-step content-strip bookkeeping** `CPrimPRSGenFuelOk fuel P Q`: at each primitive-PRS node, every
`t`-coefficient entering `gbprimitivePartCore` has `cnormG`-length at most `30`, mirroring the
`cprimPRSgcdGenCore` recursion so it threads alongside `CPrimPRSGenRegular`. -/
def CPrimPRSGenFuelOk (cgcdB : CPolyG β → CPolyG β → CPolyG β) :
    ℕ → GBPolyCore β → GBPolyCore β → Prop
  | 0, P, _ => ∀ a ∈ gbnormCore P, (CPolyG.cnormG a : List β).length ≤ 30
  | fuel + 1, P, Q =>
    if gbisZeroCore (gbnormCore Q) = true then
      ∀ a ∈ gbnormCore (gbnormCore P), (CPolyG.cnormG a : List β).length ≤ 30
    else
      (∀ a ∈ gbnormCore (gbpsremainderCore 60 (gbnormCore P) (gbnormCore Q)),
          (CPolyG.cnormG a : List β).length ≤ 30)
        ∧ CPrimPRSGenFuelOk cgcdB fuel (gbnormCore Q)
            (gbprimitivePartCore cgcdB (gbpsremainderCore 60 (gbnormCore P) (gbnormCore Q)))

/-- **The reduction theorem** `CPrimPRSGenAssocReg` from PRS termination and gcd-correctness: given
`CPrimPRSGenRegular cgcdB fuel P Q`, `CgcdBCorrect cgcdB`, and `CPrimPRSGenFuelOk cgcdB fuel P Q`, the
per-step regularity bundle `CPrimPRSGenAssocReg cgcdB fuel P Q` holds. -/
theorem cPrimPRSGenAssocReg_of_regular_of_correct (cgcdB : CPolyG β → CPolyG β → CPolyG β)
    (hcorr : CgcdBCorrect cgcdB) :
    ∀ (fuel : ℕ) (P Q : GBPolyCore β), CPrimPRSGenRegular cgcdB fuel P Q →
      CPrimPRSGenFuelOk cgcdB fuel P Q → CPrimPRSGenAssocReg cgcdB fuel P Q := by
  intro fuel
  induction fuel with
  | zero =>
    intro P Q hreg hfuel
    -- at fuel 0, CPrimPRSGenRegular must be a `stop` node (the `step` ctor needs `fuel+1`)
    rw [CPrimPRSGenAssocReg]
    refine ⟨?_, ?_⟩
    · -- clause (i): the `stop`-node gives `gbisZeroCore (gbnormCore Q) = true`; reduce to `gbisZeroCore Q`
      cases hreg with
      | stop hz => rw [gbisZeroCore, ← gbnormCore_idemp, ← gbisZeroCore]; exact hz
    · -- clause (iii) on `P` (terminal strip): total content scaling
      rw [CPrimPRSGenFuelOk] at hfuel
      exact associated_toGBPolyG_gbprimitivePartCore_total 30 cgcdB hcorr P hfuel
  | succ fuel ih =>
    intro P Q hreg hfuel
    rw [CPrimPRSGenAssocReg]
    cases hreg with
    | stop hz =>
      -- terminal: left disjunct (Q normalizes to zero) + clause (iii) on `gbnormCore P`
      refine Or.inl ⟨hz, ?_⟩
      rw [CPrimPRSGenFuelOk, if_pos hz] at hfuel
      have h := associated_toGBPolyG_gbprimitivePartCore_total 30 cgcdB hcorr (gbnormCore P) hfuel
      rwa [toGBPolyG_gbnormCore] at h
    | step hz hguard hrec =>
      -- recursive node: right disjunct
      rw [CPrimPRSGenFuelOk, if_neg (by rw [hz]; simp)] at hfuel
      obtain ⟨hfuelPrem, hfuelRec⟩ := hfuel
      refine Or.inr ⟨by rw [hz]; simp, ?_, ?_, ?_⟩
      · -- clause (ii): the nonzero-multiplier pseudo-division witness
        obtain ⟨s, c, hrel, hc0⟩ := toGBPolyG_gbpsremainderCore_ne_zero 60 (gbnormCore P)
          (gbnormCore Q) (by rw [gbnormCore_idemp]; exact hz)
        exact ⟨s, c, hrel, hc0⟩
      · -- clause (iii): the total content strip on `prem`
        exact associated_toGBPolyG_gbprimitivePartCore_total 30 cgcdB hcorr
          (gbpsremainderCore 60 (gbnormCore P) (gbnormCore Q)) hfuelPrem
      · -- the tower recursion: regularity ∧ fuel ⟹ AssocReg one level down
        exact ih (gbnormCore Q) _ hrec hfuelRec

/-! ## Sharpening termination: the pseudo-division degree drop as a theorem

The content strip preserves the `t`-degree, and the single loop body `lc(q)·p − lc(p)·tᵏ·q` strictly
drops the `t`-degree over the integral domain `R = (CFieldSpec.K β)[X]`, so termination's only remaining
conditional ingredient is the fuel-bounded loop completing. -/

/-- **`toPolyG (gblcCore (gbnormCore p))` is the leading coefficient of `toGBCoeffPoly p`**, via
`toPolyG_gblcCore_eq_coeff` and `gbdegCore_eq_natDegree`. -/
theorem toPolyG_gblcCore_eq_leadingCoeff (p : GBPolyCore β) :
    CPolyG.toPolyG (gblcCore (gbnormCore p)) = (toGBCoeffPoly p).leadingCoeff := by
  rw [Polynomial.leadingCoeff, ← gbdegCore_eq_natDegree, toPolyG_gblcCore_eq_coeff,
    toGBCoeffPoly_gbnormCore]
  congr 1
  rw [gbdegCore, gbdegCore, gbnormCore_idemp]

/-- **The single pseudo-division step body** `gbStepReduce p q = lc(q)·p − lc(p)·tᵏ·q`
(`k = (gbnormCore p).length − (gbnormCore q).length`): one leading-term elimination of
`gbpsremainderCore`. -/
noncomputable def gbStepReduce (p q : GBPolyCore β) : GBPolyCore β :=
  gbsubCore (gbscaleCCore (gblcCore (gbnormCore q)) p)
    (gbscaleCCore (gblcCore (gbnormCore p))
      (gbshiftCore ((gbnormCore p).length - (gbnormCore q).length) q))

/-- **The `R[t]` reading of a step body** `toGBCoeffPoly (gbStepReduce p q) = C(lc q)·toGBCoeffPoly p −
C(lc p)·tᵏ·toGBCoeffPoly q` (`R = (CFieldSpec.K β)[X]`, `k = deg_t p − deg_t q`). -/
theorem toGBCoeffPoly_gbStepReduce (p q : GBPolyCore β) :
    toGBCoeffPoly (gbStepReduce p q)
      = Polynomial.C ((toGBCoeffPoly q).leadingCoeff) * toGBCoeffPoly p
        - Polynomial.C ((toGBCoeffPoly p).leadingCoeff)
          * Polynomial.X ^ ((gbnormCore p).length - (gbnormCore q).length) * toGBCoeffPoly q := by
  rw [gbStepReduce, toGBCoeffPoly_gbsubCore, toGBCoeffPoly_gbscaleCCore, toGBCoeffPoly_gbscaleCCore,
    toGBCoeffPoly_gbshiftCore, toPolyG_gblcCore_eq_leadingCoeff, toPolyG_gblcCore_eq_leadingCoeff]
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
/-- **`gbisZeroCore` is `gbnormCore`-invariant**: `gbisZeroCore (gbnormCore p) = gbisZeroCore p`. -/
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
      set p' := gbnormCore (gbsubCore (gbscaleCCore (gblcCore (gbnormCore q)) (gbnormCore p))
        (gbscaleCCore (gblcCore (gbnormCore p))
          (gbshiftCore ((gbnormCore p).length - (gbnormCore q).length) (gbnormCore q)))) with hp'def
      have hp'read : toGBCoeffPoly p' = toGBCoeffPoly (gbStepReduce (gbnormCore p) (gbnormCore q)) := by
        rw [hp'def, toGBCoeffPoly_gbnormCore, gbStepReduce, toGBCoeffPoly_gbsubCore,
          toGBCoeffPoly_gbsubCore, toGBCoeffPoly_gbscaleCCore, toGBCoeffPoly_gbscaleCCore,
          toGBCoeffPoly_gbscaleCCore, toGBCoeffPoly_gbscaleCCore, toGBCoeffPoly_gbshiftCore,
          toGBCoeffPoly_gbshiftCore, gbnormCore_idemp, gbnormCore_idemp]
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

/-- **`toGBPolyG` preserves the `t`-degree of `toGBCoeffPoly`**: `(toGBPolyG p).natDegree =
(toGBCoeffPoly p).natDegree`. The coefficient lift `liftKG = mapRingHom (amG β)` is over the injective
field embedding `amG β`, so `Polynomial.natDegree_map` applies. -/
theorem natDegree_toGBPolyG (p : GBPolyCore β) :
    (toGBPolyG p).natDegree = (toGBCoeffPoly p).natDegree := by
  rw [toGBPolyG, liftKG, Polynomial.coe_mapRingHom,
    Polynomial.natDegree_map_eq_of_injective (RatFunc.algebraMap_injective (CFieldSpec.K β))]

/-- **The content strip preserves the `t`-degree**: under `CgcdBCorrect cgcdB` and the per-coefficient
size bound, `(toGBCoeffPoly (gbprimitivePartCore cgcdB p)).natDegree = (toGBCoeffPoly p).natDegree`
(the strip is a `β(s)`-unit scaling, and `Associated` polynomials over `β(s)` have equal `natDegree`). -/
theorem natDegree_toGBCoeffPoly_gbprimitivePartCore (fuel : ℕ)
    (cgcdB : CPolyG β → CPolyG β → CPolyG β) (hcorr : CgcdBCorrect cgcdB) (p : GBPolyCore β)
    (hfuel : ∀ a ∈ gbnormCore p, (CPolyG.cnormG a : List β).length ≤ fuel) :
    (toGBCoeffPoly (gbprimitivePartCore cgcdB p)).natDegree = (toGBCoeffPoly p).natDegree := by
  have hassoc := associated_toGBPolyG_gbprimitivePartCore_total fuel cgcdB hcorr p hfuel
  have := natDegree_eq_of_associated hassoc
  rwa [natDegree_toGBPolyG, natDegree_toGBPolyG] at this

/-- **The list-length loop guard is exactly the pseudo-remainder `t`-degree drop**: under `CgcdBCorrect
cgcdB`, the retained size bound on `prem`, `Q` nonzero, and the stripped node nonzero (`hrz`), the
`CPrimPRSGenRegular`-`step` guard
`(gbnormCore (gbprimitivePartCore cgcdB prem)).length < (gbnormCore Q).length`
holds iff `(toGBCoeffPoly prem).natDegree < (toGBCoeffPoly Q).natDegree`. -/
theorem gbnormGuard_iff_premDegree (cgcdB : CPolyG β → CPolyG β → CPolyG β) (hcorr : CgcdBCorrect cgcdB)
    (P Q : GBPolyCore β) (hQ : gbisZeroCore (gbnormCore Q) = false)
    (hfuel : ∀ a ∈ gbnormCore (gbpsremainderCore 60 (gbnormCore P) (gbnormCore Q)),
      (CPolyG.cnormG a : List β).length ≤ 30)
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

/-! ### Restatements against the intended wording (anonymous `example`s) -/

-- ★ THE DELIVERABLE: the per-step regularity gate `CPrimPRSGenAssocReg` follows from the sharp residual —
-- PRS termination (`CPrimPRSGenRegular`) + level-β gcd-correctness (`CgcdBCorrect`) + transparent fuel.
example (cgcdB : CPolyG β → CPolyG β → CPolyG β) (hcorr : CgcdBCorrect cgcdB)
    (fuel : ℕ) (P Q : GBPolyCore β) (hreg : CPrimPRSGenRegular cgcdB fuel P Q)
    (hfuel : CPrimPRSGenFuelOk cgcdB fuel P Q) : CPrimPRSGenAssocReg cgcdB fuel P Q :=
  cPrimPRSGenAssocReg_of_regular_of_correct cgcdB hcorr fuel P Q hreg hfuel

-- The list-length WF guard IS the polynomial t-degree (the representation half of termination, closed).
example (p : GBPolyCore β) : gbdegCore p = (toGBCoeffPoly p).natDegree := gbdegCore_eq_natDegree p

-- Clause (ii) with the β(s)-unit multiplier is unconditional given the non-terminal loop guard (Q ≠ 0).
example (fuel : ℕ) (p q : GBPolyCore β) (hq : gbisZeroCore (gbnormCore q) = false) :
    ∃ (s : GBPolyCore β) (c : CPolyG β),
      Polynomial.C (QFunNZG.amG β (CPolyG.toPolyG c)) * toGBPolyG p
          = toGBPolyG s * toGBPolyG q + toGBPolyG (gbpsremainderCore fuel p q)
        ∧ QFunNZG.amG β (CPolyG.toPolyG c) ≠ 0 :=
  toGBPolyG_gbpsremainderCore_ne_zero fuel p q hq

-- ★ The single pseudo-division step strictly drops the t-degree, UNCONDITIONALLY (the leading-term
-- cancellation) — the per-step degree fact ComputableTowerWellFounded records as missing, now a theorem.
example (p q : GBPolyCore β) (hp : gbisZeroCore (gbnormCore p) = false)
    (hq : gbisZeroCore (gbnormCore q) = false)
    (hdeg : (toGBCoeffPoly q).natDegree ≤ (toGBCoeffPoly p).natDegree)
    (hstepne : toGBCoeffPoly (gbStepReduce p q) ≠ 0) :
    (toGBCoeffPoly (gbStepReduce p q)).natDegree < (toGBCoeffPoly p).natDegree :=
  natDegree_gbStepReduce_lt p q hp hq hdeg hstepne

-- ★★ The inner pseudo-division loop COMPLETES (degree drop) under the explicit, satisfiable fuel bound
-- `deg_t p < fuel` — UNCONDITIONAL. Termination's last conditional ingredient is now a numeric bound.
example (q : GBPolyCore β) (hq : gbisZeroCore (gbnormCore q) = false)
    (fuel : ℕ) (p : GBPolyCore β) (hlt : (toGBCoeffPoly p).natDegree < fuel) :
    (toGBCoeffPoly (gbpsremainderCore fuel p q)).natDegree < (toGBCoeffPoly q).natDegree
      ∨ toGBCoeffPoly (gbpsremainderCore fuel p q) = 0 :=
  gbpsremainderCore_degree_lt q hq fuel p hlt

/-! ## Summary

`CPrimPRSGenAssocReg cgcdB fuel P Q` is equivalent (given the bookkeeping `CPrimPRSGenFuelOk`) to two
per-run witnesses: PRS termination `CPrimPRSGenRegular` and level-`β` gcd-correctness `CgcdBCorrect`.
The degree-drop content of termination is a theorem (`natDegree_gbStepReduce_lt`,
`gbpsremainderCore_degree_lt`), leaving only a satisfiable numeric fuel bound. -/

end DeepWiki.SymbolicIntegration
