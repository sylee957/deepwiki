import DeepWiki.SymbolicIntegration.ComputeCorrectness
import DeepWiki.SymbolicIntegration.SubresultantPRS

/-! # Bridging the computable subresultant PRS to the abstract subresultant (Bronstein §1.5/§2.5)
The computable bivariate engine (`SubresultantCompute`: `BPoly := List CPoly = ℚ[t][x]`, with
`bpsremainder` the pseudo-remainder and `subresPRS` the Collins–Brown subresultant chain) is validated
*pointwise* by `native_decide` (`lrtGcd_ex241`). This file connects it to the **abstract** subresultant
theory (`Subresultants`/`SubresultantPRS`, the Sylvester-submatrix `subresultant A B n m j`) through the
already-proven `toBPoly : BPoly → (ℚ[X])[X]` homomorphism bridge of `ComputeCorrectness`.

The spine is `toBPoly_bpsremainder` — the honest `ℚ[t][x]` pseudo-division identity
`C(toPoly c) · toBPoly p = toBPoly s · toBPoly q + toBPoly (bpsremainder fuel p q)`. Combined with the
abstract subresultant reduction law `subresultant_rem` (`subresultant A B = ±·subresultant B Rem` when
`A = Rem + B·Q`) and the scaling law `subresultant_C_mul`, this realizes **one subresultant-PRS step**
of the computable pseudo-remainder against the abstract subresultant — the structural core of the
`lrtGcdCompute ↔ lrtSubresultant` agreement. (The full chain agreement — the β-divisor accumulation of
`subresPRS` against the subresultant normalization, the `bsubresultantGcd` degree filter, and the
`bprimitivePartX`/`bmonicXmodR` content steps — is the deep Collins–Brown formalization left open; see
the closing note.) -/

open Polynomial

namespace DeepWiki.SymbolicIntegration.Compute

/-! ### `toBPoly` degree / leading-`x`-coefficient bridge
The `BPoly` list structure maps to `(ℚ[X])[X]` `x`-coefficients exactly: `(toBPoly p).coeff i = toPoly
(p.getD i [])`. From this, `bdeg`/`blc` are the honest `natDegree`/`leadingCoeff` (for a normalized,
nonzero list), mirroring the `CPoly`-layer lemmas `cdeg_eq_natDegree`/`clead_eq_leadingCoeff`. -/

/-- **`x`-coefficient read**: the `i`-th `x`-coefficient of `toBPoly p` is `toPoly` of the `i`-th list
entry (`[]` past the end). The Horner bridge `toBPoly` realizes the dense `x`-coefficient list exactly. -/
theorem toBPoly_coeff (p : BPoly) (i : ℕ) : (toBPoly p).coeff i = toPoly (p.getD i []) := by
  induction p generalizing i with
  | nil => simp
  | cons a as ih =>
    rw [toBPoly_cons]
    cases i with
    | zero => simp [coeff_C]
    | succ n => simp [coeff_X_mul, ih]

/-- **`x`-degree bound**: `natDegree (toBPoly p) ≤ (bnorm p).length − 1` (`x`-coefficients past the
normalized length vanish). -/
theorem natDegree_toBPoly_le (p : BPoly) : (toBPoly p).natDegree ≤ (bnorm p).length - 1 := by
  rw [← toBPoly_bnorm]
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro m hm
  rw [toBPoly_coeff, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

/-- `bnorm` has **no trailing zero `x`-coefficient**: `(bnorm p).getLast?` is never `some` of a
`CPoly` that `toPoly`-vanishes (its `cnorm` is `[]`). -/
theorem bnorm_getLast?_toPoly_ne_zero (p : BPoly) {v : CPoly}
    (h : (bnorm p).getLast? = some v) : toPoly v ≠ 0 := by
  induction p with
  | nil => simp at h
  | cons a as ih =>
    rw [bnorm_cons_eq] at h
    cases hr : bnorm as with
    | nil =>
      rw [hr] at h
      by_cases ha : cisZero (cnorm a)
      · simp [ha] at h
      · simp only [ha, Bool.false_eq_true, if_false] at h
        rw [List.getLast?_singleton, Option.some.injEq] at h
        subst h
        rw [toPoly_cnorm]
        intro hz
        exact ha (by simp [cisZero, (cnorm_eq_nil_iff a).mpr hz])
    | cons b bs =>
      rw [hr] at h
      rw [List.getLast?_cons_cons] at h
      exact ih (by rw [hr]; exact h)

/-- `blc` is the **`x`-coefficient at the top index**: `toPoly (blc p) = (toBPoly p).coeff (bdeg p)`. -/
theorem toPoly_blc_eq_coeff (p : BPoly) : toPoly (blc p) = (toBPoly p).coeff (bdeg p) := by
  rw [blc, bdeg, ← toBPoly_bnorm, toBPoly_coeff, List.getD_eq_getElem?_getD,
    ← List.getLast?_eq_getElem?]

/-- `bisZero p` is `true` iff `toBPoly p = 0` (the list normalizes to empty exactly for the zero
polynomial in `x`). -/
theorem bisZero_iff_toBPoly_eq_zero (p : BPoly) : bisZero p = true ↔ toBPoly p = 0 := by
  rw [bisZero, beq_iff_eq]
  constructor
  · intro h; rw [← toBPoly_bnorm, h, toBPoly_nil]
  · intro h
    rcases hb : bnorm p with _ | ⟨c, cs⟩
    · rfl
    · exfalso
      have hlast : ((c :: cs).getLast?) ≠ none := by simp
      rcases hg : (c :: cs).getLast? with _ | v
      · exact hlast hg
      · have hv := bnorm_getLast?_toPoly_ne_zero p (by rw [hb]; exact hg)
        have : (toBPoly p).coeff (bdeg p) = 0 := by rw [h]; simp
        rw [← toPoly_blc_eq_coeff] at this
        rw [blc, hb] at this
        rw [hg] at this
        simp only [Option.getD_some] at this
        exact hv this

/-- The leading `x`-coefficient of a normalized nonzero `BPoly` is nonzero (under `toPoly`):
`toPoly (blc p) ≠ 0` when `¬ bisZero p`. -/
theorem toPoly_blc_ne_zero (p : BPoly) (h : ¬ bisZero p = true) : toPoly (blc p) ≠ 0 := by
  have hbne : bnorm p ≠ [] := by
    intro hb
    exact h (by rw [bisZero, beq_iff_eq, hb])
  rw [blc]
  rcases hg : (bnorm p).getLast? with _ | v
  · exact absurd (List.getLast?_eq_none_iff.mp hg) hbne
  · simp only [Option.getD_some]
    exact bnorm_getLast?_toPoly_ne_zero p hg

/-- **`bdeg` is the honest `x`-`natDegree`**: `bdeg p = (toBPoly p).natDegree`. -/
theorem bdeg_eq_natDegree (p : BPoly) : bdeg p = (toBPoly p).natDegree := by
  by_cases h : bisZero p = true
  · have hz : toBPoly p = 0 := (bisZero_iff_toBPoly_eq_zero p).mp h
    have hb : bnorm p = [] := by simpa [bisZero] using h
    rw [bdeg, hb, hz]; simp
  · refine le_antisymm ?_ ?_
    · -- bdeg ≤ natDegree via the leading coeff being nonzero at index bdeg
      apply Polynomial.le_natDegree_of_ne_zero
      rw [← toPoly_blc_eq_coeff]
      exact toPoly_blc_ne_zero p h
    · -- natDegree ≤ bdeg via natDegree_toBPoly_le and the length count
      have hbne : bnorm p ≠ [] := by
        intro hb
        exact h (by rw [bisZero, beq_iff_eq, hb])
      have hpos : 1 ≤ (bnorm p).length := List.length_pos_iff.mpr hbne
      have hle := natDegree_toBPoly_le p
      rw [bdeg]; omega

/-- For a normalized nonzero `BPoly`, the normalized list length is `natDegree (toBPoly p) + 1`. -/
theorem length_bnorm_of_ne (p : BPoly) (h : ¬ bisZero p = true) :
    (bnorm p).length = (toBPoly p).natDegree + 1 := by
  have hbne : bnorm p ≠ [] := by
    intro hb
    exact h (by rw [bisZero, beq_iff_eq, hb])
  have hd := bdeg_eq_natDegree p
  rw [bdeg] at hd
  have hpos : 1 ≤ (bnorm p).length := List.length_pos_iff.mpr hbne
  omega

/-- **`blc` is the honest `x`-`leadingCoeff`**: `toPoly (blc p) = (toBPoly p).leadingCoeff`. -/
theorem toPoly_blc_eq_leadingCoeff (p : BPoly) : toPoly (blc p) = (toBPoly p).leadingCoeff := by
  rw [Polynomial.leadingCoeff, ← bdeg_eq_natDegree, ← toPoly_blc_eq_coeff]

/-! ### The abstract subresultant under a one-sided constant scaling
A specialization of `subresultant_C_mul` (`Subresultants`) that scales only the **first** argument: it
absorbs the `C(toPoly c)` content factor that the computable pseudo-division identity
(`toBPoly_bpsremainder`) puts on `toBPoly p`, so the subresultant reduction `subresultant_rem` applies
to `C(toPoly c) · toBPoly p` rather than `toBPoly p` directly. -/

/-- **Subresultant scaled in the first argument only**: `Sⱼ(C c · A, B) = c^(m−j) · Sⱼ(A, B)`
(`j ≤ m`, `j ≤ n`). The `b = 1` case of `subresultant_C_mul` (`C 1 * B = B`, `1^(n−j) = 1`). -/
theorem subresultant_C_mul_left {R : Type*} [CommRing R] (c : R) (A B : R[X]) (n m j : ℕ)
    (hjm : j ≤ m) (hjn : j ≤ n) :
    subresultant (C c * A) B n m j = C (c ^ (m - j)) * subresultant A B n m j := by
  have h := subresultant_C_mul c 1 A B n m j hjm hjn
  rw [map_one, one_mul, one_pow, mul_one] at h
  rw [h]

/-! ### One subresultant-PRS step of the computable pseudo-remainder
The structural core: through `toBPoly`, one pseudo-division step of the computable engine
(`bpsremainder`) realizes the abstract subresultant reduction `subresultant_rem`. With `A = toBPoly p`,
`B = toBPoly q`, the pseudo-division identity `C(toPoly c) · A = toBPoly s · B + toBPoly prem`
(`toBPoly_bpsremainder`) plus the one-sided scaling law absorbs the content factor `c^(m−j)` and yields
`Sⱼ(A, B) · c^(m−j) = ±·Sⱼ(B, prem)` — the equation that, iterated along the chain, is the subresultant
PRS. The degree side-conditions of `subresultant_rem` (`deg B ≤ m`, `deg(quotient) + m ≤ n`) are taken
as hypotheses: they hold in the regular subresultant-PRS use (where `deg B = m`, `deg A = n`), and stating
them keeps this a clean abstract bridge over the already-proven `toBPoly` homomorphism. -/

/-- **One subresultant-PRS step through `toBPoly`** (Bronstein §1.5, Geddes §7.3 Lemma 7.1, realized on
the computable engine): let `A = toBPoly p`, `B = toBPoly q`, `Rem = toBPoly (bpsremainder fuel p q)`,
and `(s, c)` the quotient/content witnesses of `toBPoly_bpsremainder` (so `C(toPoly c)·A = toBPoly s·B +
Rem`). For formal degrees `n, m` with `j ≤ m`, `j < n`, `deg B ≤ m`, and `deg(toBPoly s) + m ≤ n`, the
abstract subresultant satisfies
`C((toPoly c)^(m−j)) · Sⱼ(A,B; n,m) = (-1)^((m−j)(n−j)) · Sⱼ(B, Rem; m,n)`.
Pure consequence of `subresultant_C_mul_left` (absorb the content factor) and `subresultant_rem` (the
division-step reduction). This is the one-step engine of the subresultant chain; iterating it along
`subresPRS` (with the β-divisor bookkeeping) is the full `lrtGcdCompute ↔ lrtSubresultant` agreement. -/
theorem subresultant_C_mul_eq_rem_of_bpsremainder (fuel : ℕ) (p q : BPoly) (n m j : ℕ)
    (s : BPoly) (c : CPoly)
    (hsc : Polynomial.C (toPoly c) * toBPoly p
        = toBPoly s * toBPoly q + toBPoly (bpsremainder fuel p q))
    (hjm : j ≤ m) (hjn : j < n)
    (hB : (toBPoly q).natDegree ≤ m)
    (hQ : (toBPoly s).natDegree + m ≤ n) :
    Polynomial.C ((toPoly c) ^ (m - j)) * subresultant (toBPoly p) (toBPoly q) n m j
      = (-1 : (ℚ[X])[X]) ^ ((m - j) * (n - j))
        * subresultant (toBPoly q) (toBPoly (bpsremainder fuel p q)) m n j := by
  rw [← subresultant_C_mul_left (toPoly c) (toBPoly p) (toBPoly q) n m j hjm (le_of_lt hjn)]
  exact subresultant_rem (Polynomial.C (toPoly c) * toBPoly p) (toBPoly q) (toBPoly s)
    (toBPoly (bpsremainder fuel p q)) n m j hjm hjn hB hQ (by rw [hsc]; ring)

/-- **One subresultant-PRS step, packaged from `toBPoly_bpsremainder`**: extracting the
quotient/content witnesses `(s, c)` from `toBPoly_bpsremainder`, there exist a content `c : CPoly` and
quotient `s : BPoly` realizing the pseudo-division identity, *and* — once the quotient-degree bound
`deg(toBPoly s) + m ≤ n` is known — the subresultant reduction
`C((toPoly c)^(m−j)) · Sⱼ(A,B; n,m) = (-1)^((m−j)(n−j)) · Sⱼ(B, Rem; m,n)`. So the only remaining
side-condition is the quotient-degree bound (automatic in the regular subresultant-PRS use). -/
theorem exists_subresultant_C_mul_eq_rem_of_bpsremainder (fuel : ℕ) (p q : BPoly) (n m j : ℕ)
    (hjm : j ≤ m) (hjn : j < n) (hB : (toBPoly q).natDegree ≤ m) :
    ∃ (s : BPoly) (c : CPoly),
      Polynomial.C (toPoly c) * toBPoly p
          = toBPoly s * toBPoly q + toBPoly (bpsremainder fuel p q)
        ∧ ((toBPoly s).natDegree + m ≤ n →
          Polynomial.C ((toPoly c) ^ (m - j)) * subresultant (toBPoly p) (toBPoly q) n m j
            = (-1 : (ℚ[X])[X]) ^ ((m - j) * (n - j))
              * subresultant (toBPoly q) (toBPoly (bpsremainder fuel p q)) m n j) := by
  obtain ⟨s, c, hsc⟩ := toBPoly_bpsremainder fuel p q
  exact ⟨s, c, hsc, fun hQs =>
    subresultant_C_mul_eq_rem_of_bpsremainder fuel p q n m j s c hsc hjm hjn hB hQs⟩

/-! ### Identifying the LRT operands: the computable lifts realize `D.map C`, `A − t·D'`
The abstract LRT subresultant `lrtSubresultant A D j` (`RationalIntegrationAlgorithms`) takes the
subresultant of `D.map C` and `A.map C − C X · (D').map C` over `(ℚ[X])[X]`. The computable engine
forms the same operands as `BPoly`s (`liftCtoBPoly D`, `bArgAmtD' A D`). These lemmas show the `toBPoly`
images of the computable operands are *exactly* the abstract LRT operands — closing the gap between the
two operand constructions so the subresultant chain above is literally about `lrtSubresultant`. -/

/-- `toPoly (cC c) = C c`: the constant-`CPoly` lift realizes the `ℚ[X]` constant. -/
@[simp] theorem toPoly_cC (c : ℚ) : toPoly (cC c) = Polynomial.C c := by
  rw [cC, toPoly_cnorm]
  simp [toPoly_cons]

/-- **`liftCtoBPoly` realizes `·.map C`**: `toBPoly (liftCtoBPoly p) = (toPoly p).map C` — lifting a
`CPoly` (`= ℚ[x]`) into `BPoly` with constant `t`-coefficients realizes the abstract coefficient
embedding `C : ℚ →+* ℚ[t]` applied to `toPoly p`. -/
theorem toBPoly_liftCtoBPoly (p : CPoly) :
    toBPoly (liftCtoBPoly p) = (toPoly p).map (Polynomial.C : ℚ →+* ℚ[X]) := by
  induction p with
  | nil => simp [liftCtoBPoly]
  | cons a as ih =>
    show toBPoly (cC a :: liftCtoBPoly as) = _
    rw [toBPoly_cons, toPoly_cons, ih, toPoly_cC, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_X, Polynomial.map_C]

/-- `toPoly ctVar = X`: the computable `t`-variable lifts to `X ∈ ℚ[t]` (the `t`-indeterminate
realized in `ComputeCorrectness`'s `ℚ[X]` reading of `CPoly = ℚ[t]`). -/
@[simp] theorem toPoly_ctVar : toPoly ctVar = (Polynomial.X : ℚ[X]) := by
  rw [ctVar]; simp [toPoly_cons]

/-- **`bArgAmtD'` realizes the LRT second operand**: `toBPoly (bArgAmtD' A D) = (toPoly A).map C −
C X · (derivative (toPoly D)).map C` — the computable `A − t·D'` lift is exactly the
`A.map C − C t · (D').map C` operand of `lrtSubresultant`. -/
theorem toBPoly_bArgAmtD' (A D : CPoly) :
    toBPoly (bArgAmtD' A D)
      = (toPoly A).map (Polynomial.C : ℚ →+* ℚ[X])
        - Polynomial.C Polynomial.X * (derivative (toPoly D)).map (Polynomial.C : ℚ →+* ℚ[X]) := by
  rw [bArgAmtD', toBPoly_bsub, toBPoly_liftCtoBPoly, toBPoly_bscaleC, toBPoly_liftCtoBPoly,
    toPoly_ctVar, toPoly_cderiv]

/-- **The computable LRT operands are the abstract LRT operands**: `toBPoly (liftCtoBPoly D)` and
`toBPoly (bArgAmtD' A D)` are exactly the two arguments of `lrtSubresultant A D j` (with the book's
formal degrees `deg D`, `deg D − 1`). So the subresultant chain `subresultant_C_mul_eq_rem_of_bpsremainder`
run on these lifts is literally about `lrtSubresultant`. -/
theorem lrtSubresultant_eq_subresultant_toBPoly (A D : CPoly) (j : ℕ) :
    lrtSubresultant (toPoly A) (toPoly D) j
      = subresultant (toBPoly (liftCtoBPoly D)) (toBPoly (bArgAmtD' A D))
          (toPoly D).natDegree ((toPoly D).natDegree - 1) j := by
  rw [lrtSubresultant, toBPoly_liftCtoBPoly, toBPoly_bArgAmtD']

end DeepWiki.SymbolicIntegration.Compute
