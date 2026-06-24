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

/-- **Subresultant scaled in the second argument only**: `Sⱼ(A, C c · B) = c^(n−j) · Sⱼ(A, B)`
(`j ≤ m`, `j ≤ n`). The `a = 1` case of `subresultant_C_mul` — the mirror of `subresultant_C_mul_left`,
absorbing the `C(toPoly β)` content the β-divisor `bdivC` carries on the *next* PRS element. -/
theorem subresultant_C_mul_right {R : Type*} [CommRing R] (c : R) (A B : R[X]) (n m j : ℕ)
    (hjm : j ≤ m) (hjn : j ≤ n) :
    subresultant A (C c * B) n m j = C (c ^ (n - j)) * subresultant A B n m j := by
  have h := subresultant_C_mul 1 c A B n m j hjm hjn
  rw [map_one, one_mul, one_pow, one_mul] at h
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

/-! ### The LRT subresultant reduced to the first computable pseudo-remainder
Combining the operand identification with the one-step subresultant-PRS reduction: the abstract
`lrtSubresultant A D j` equals — up to the content factor `c^(m−j)` and the swap sign — the abstract
subresultant of `D` (lifted) against the *first computable pseudo-remainder* `bpsremainder fuel (D lifted)
(A − t·D')`. This is the entry point of the subresultant chain: the LRT subresultant, one
pseudo-division step in, is the subresultant of the next PRS pair. -/

/-- **LRT subresultant after one computable pseudo-division step**: with the book's formal degrees
`n = deg D`, `m = deg D − 1`, `P = liftCtoBPoly D`, `Q = bArgAmtD' A D`, and `(s, c)` the
`toBPoly_bpsremainder` witnesses for the LRT PRS step `prem(D, A−t·D') = bpsremainder fuel P Q` (so
`C(toPoly c)·P = s·Q + prem`), the abstract `lrtSubresultant A D j` satisfies
`C((toPoly c)^(m−j)) · lrtSubresultant A D j = (-1)^((m−j)(n−j)) · Sⱼ(Q, prem(P,Q); m, n)`
once `j ≤ deg D − 1`, `j < deg D`, `deg(toBPoly Q) ≤ deg D − 1`, and the quotient-degree bound
`deg(toBPoly s) + (deg D − 1) ≤ deg D` hold. This is `subresultant_C_mul_eq_rem_of_bpsremainder`
(with `p = P`, `q = Q`, `n = deg D`, `m = deg D − 1`) transported across
`lrtSubresultant_eq_subresultant_toBPoly` — the LRT subresultant as one step of the computable PRS. -/
theorem lrtSubresultant_C_mul_eq_rem_of_bpsremainder (fuel : ℕ) (A D : CPoly) (j : ℕ)
    (s : BPoly) (c : CPoly)
    (hsc : Polynomial.C (toPoly c) * toBPoly (liftCtoBPoly D)
        = toBPoly s * toBPoly (bArgAmtD' A D)
          + toBPoly (bpsremainder fuel (liftCtoBPoly D) (bArgAmtD' A D)))
    (hjm : j ≤ (toPoly D).natDegree - 1) (hjn : j < (toPoly D).natDegree)
    (hB : (toBPoly (bArgAmtD' A D)).natDegree ≤ (toPoly D).natDegree - 1)
    (hQ : (toBPoly s).natDegree + ((toPoly D).natDegree - 1) ≤ (toPoly D).natDegree) :
    Polynomial.C ((toPoly c) ^ (((toPoly D).natDegree - 1) - j))
        * lrtSubresultant (toPoly A) (toPoly D) j
      = (-1 : (ℚ[X])[X]) ^ ((((toPoly D).natDegree - 1) - j) * ((toPoly D).natDegree - j))
        * subresultant (toBPoly (bArgAmtD' A D))
            (toBPoly (bpsremainder fuel (liftCtoBPoly D) (bArgAmtD' A D)))
            ((toPoly D).natDegree - 1) (toPoly D).natDegree j := by
  rw [lrtSubresultant_eq_subresultant_toBPoly]
  exact subresultant_C_mul_eq_rem_of_bpsremainder fuel (liftCtoBPoly D) (bArgAmtD' A D)
    (toPoly D).natDegree ((toPoly D).natDegree - 1) j s c hsc hjm hjn hB hQ

/-! ### `bdivC` realizes exact `ℚ[t]`-division (the β-divisor exact-division core)
`bdivC fuel p c` divides every `x`-coefficient of `p` by the `ℚ[t]` scalar `c` (via the per-`CPoly`
Euclidean quotient `cdiv`). In the subresultant PRS the β-divisor `c = βᵢ` always *divides* the
pseudo-remainder (Collins's theorem), so this scalar division is **exact**: `C(toPoly c) · toBPoly
(bdivC fuel p c) = toBPoly p`. The honest content is per-`x`-coefficient — the `CPoly` exact-division
bridge (the `toPoly_cdivmod'` Euclidean identity with a zero remainder), folded over the
`x`-coefficient list through `toBPoly`. We state it from the directly-checkable `cmod`-zero certificate
and give the `ℚ[t]` divisibility wrapper. -/

/-- **`CPoly` exact-division bridge**: if the remainder `cmod fuel a c` reads to `0` in `ℚ[X]`, then
`cdiv` realizes honest division `toPoly a = toPoly (cdiv fuel a c) · toPoly c`. From the
Euclidean-division identity `toPoly_cdivmod'` with a zero remainder (needs `cnorm c ≠ []`). (Local copy
of the `HermiteCorrectness` bridge, kept here to avoid the Hermite import.) -/
theorem toPoly_cdiv_of_cmod_zero_loc (fuel : ℕ) (a c : CPoly) (hc : cnorm c ≠ [])
    (hrem : toPoly (cmod fuel a c) = 0) :
    toPoly a = toPoly (cdiv fuel a c) * toPoly c := by
  have h := toPoly_cdivmod' fuel a c hc
  rw [show (cdivmod fuel a c).1 = cdiv fuel a c from rfl,
      show (cdivmod fuel a c).2 = cmod fuel a c from rfl, hrem, add_zero] at h
  exact h

/-- **Divisibility ⟹ exact remainder** (`CPoly`): if `toPoly c ∣ toPoly a` in `ℚ[X]` (with `c ≠ 0` and
enough fuel), the computable remainder reads to `0`. The remainder has degree `< deg c` (`cmod_length_lt`)
yet is divisible by `c`, hence vanishes. (Local copy of the `HermiteCorrectness` bridge.) -/
theorem cmod_eq_zero_of_dvd_loc (fuel : ℕ) (a c : CPoly) (hc : cnorm c ≠ [])
    (hfuel : (cnorm a).length ≤ fuel) (hdvd : toPoly c ∣ toPoly a) :
    toPoly (cmod fuel a c) = 0 := by
  have hc0 : toPoly c ≠ 0 := fun h => hc ((cnorm_eq_nil_iff c).mpr h)
  have hdiv := toPoly_cdivmod' fuel a c hc
  rw [show (cdivmod fuel a c).1 = cdiv fuel a c from rfl,
      show (cdivmod fuel a c).2 = cmod fuel a c from rfl] at hdiv
  have hqr : toPoly c ∣ toPoly (cmod fuel a c) := by
    have hd2 : toPoly c ∣ toPoly (cdiv fuel a c) * toPoly c := Dvd.intro_left _ rfl
    have hsub : toPoly (cmod fuel a c) = toPoly a - toPoly (cdiv fuel a c) * toPoly c := by
      rw [hdiv]; ring
    rw [hsub]; exact dvd_sub hdvd hd2
  have hlen : (cnorm (cmod fuel a c)).length < (cnorm c).length := cmod_length_lt fuel a c hc hfuel
  by_contra hne
  have hrne : toPoly (cmod fuel a c) ≠ 0 := hne
  have hdeg : (toPoly c).degree ≤ (toPoly (cmod fuel a c)).degree :=
    Polynomial.degree_le_of_dvd hqr hrne
  have e1 : (cnorm (cmod fuel a c)).length = (toPoly (cmod fuel a c)).natDegree + 1 :=
    length_cnorm_of_ne _ (fun h => hrne ((cnorm_eq_nil_iff _).mp h))
  have e2 : (cnorm c).length = (toPoly c).natDegree + 1 := length_cnorm_of_ne c hc
  rw [Polynomial.degree_eq_natDegree hrne, Polynomial.degree_eq_natDegree hc0, Nat.cast_le] at hdeg
  omega

/-- **`toBPoly` of a coefficient-wise exact division**: if dividing every `x`-coefficient `a` of `p`
by the `ℚ[t]` scalar `c` is exact (`toPoly (cmod fuel a c) = 0`, i.e. `toPoly c ∣ toPoly a`), then
`C(toPoly c) · toBPoly (p.map (cdiv fuel · c)) = toBPoly p` — the scalar `C(toPoly c)` factors back out
of the divided `x`-coefficient list. Per-coefficient `toPoly_cdiv_of_cmod_zero_loc`, folded over the
list through the `toBPoly` Horner shape. -/
theorem toBPoly_map_cdiv_exact (fuel : ℕ) (p : BPoly) (c : CPoly) (hc : cnorm c ≠ [])
    (hrem : ∀ a ∈ p, toPoly (cmod fuel a c) = 0) :
    Polynomial.C (toPoly c) * toBPoly (p.map (fun a => cdiv fuel a c)) = toBPoly p := by
  induction p with
  | nil => simp
  | cons a as ih =>
    have has := ih (fun b hb => hrem b (by simp [hb]))
    have ha : toPoly a = toPoly (cdiv fuel a c) * toPoly c :=
      toPoly_cdiv_of_cmod_zero_loc fuel a c hc (hrem a (by simp))
    rw [List.map_cons, toBPoly_cons, toBPoly_cons]
    rw [ha, map_mul]
    linear_combination Polynomial.X * has

/-- **`bdivC` realizes exact `ℚ[t]`-division** (Collins's β-divisor division, the chain-content core):
when dividing every `x`-coefficient of `p` by `c` is exact (`toPoly (cmod fuel a c) = 0` for each
`x`-coefficient `a` — the β-divisor always divides the pseudo-remainder over `ℚ[t]`),
`C(toPoly c) · toBPoly (bdivC fuel p c) = toBPoly p`. So `bdivC` is honest exact scalar division in `x`,
the step that strips the pseudo-remainder `lc`-power inflation in `subresPRS`. -/
theorem toBPoly_bdivC_exact (fuel : ℕ) (p : BPoly) (c : CPoly) (hc : cnorm c ≠ [])
    (hrem : ∀ a ∈ p, toPoly (cmod fuel a c) = 0) :
    Polynomial.C (toPoly c) * toBPoly (bdivC fuel p c) = toBPoly p := by
  rw [bdivC, toBPoly_bnorm]
  exact toBPoly_map_cdiv_exact fuel p c hc hrem

/-- **`bdivC` exact-division from `ℚ[t]` divisibility** (the form the subresultant chain feeds): if the
`ℚ[t]` scalar `c` divides every `x`-coefficient of `p` in `ℚ[t]` (`toPoly c ∣ toPoly a`, with enough
fuel), then `C(toPoly c) · toBPoly (bdivC fuel p c) = toBPoly p`. Converts the per-coefficient
divisibility certificate (Collins: βᵢ ∣ each coefficient of the pseudo-remainder) into the exact
scalar division via `cmod_eq_zero_of_dvd_loc`. -/
theorem toBPoly_bdivC_exact_of_dvd (fuel : ℕ) (p : BPoly) (c : CPoly) (hc : cnorm c ≠ [])
    (hfuel : ∀ a ∈ p, (cnorm a).length ≤ fuel) (hdvd : ∀ a ∈ p, toPoly c ∣ toPoly a) :
    Polynomial.C (toPoly c) * toBPoly (bdivC fuel p c) = toBPoly p :=
  toBPoly_bdivC_exact fuel p c hc
    (fun a ha => cmod_eq_zero_of_dvd_loc fuel a c hc (hfuel a ha) (hdvd a ha))

/-- **`bprimitivePartX` realizes exact `ℚ[t]`-content division** (the `lrtSubresultantCompute` content
step): when the `ℚ[t]`-content `g = bcontentX fuel p` is nonzero (`hg`) and divides every `x`-coefficient
of `bnorm p` exactly (`toPoly (cmod fuel a g) = 0` — true since the content is the `ℚ[t]`-gcd of the
coefficients), `C(toPoly g) · toBPoly (bprimitivePartX fuel p) = toBPoly p`. So `bprimitivePartX` strips a
`ℚ[t]` content factor in `x` — a similarity-preserving step (the content `C(toPoly g)` is the absorbed
unit). Reuses `toBPoly_map_cdiv_exact` over the normalized coefficient list, through `toBPoly_bnorm`. -/
theorem toBPoly_bprimitivePartX_exact (fuel : ℕ) (p : BPoly)
    (hg : ¬ cisZero (bcontentX fuel p) = true) (hgcn : cnorm (bcontentX fuel p) ≠ [])
    (hrem : ∀ a ∈ bnorm p, toPoly (cmod fuel a (bcontentX fuel p)) = 0) :
    Polynomial.C (toPoly (bcontentX fuel p)) * toBPoly (bprimitivePartX fuel p) = toBPoly p := by
  have hbc : bcontentX fuel (bnorm p) = bcontentX fuel p := by
    rw [bcontentX, bcontentX, bnorm_idem]
  rw [bprimitivePartX]
  simp only [hbc, hg, Bool.false_eq_true, if_false]
  rw [toBPoly_bnorm, toBPoly_map_cdiv_exact fuel (bnorm p) (bcontentX fuel p) hgcn hrem,
    toBPoly_bnorm]

/-! ### One *subresultant-PRS* step on the β-divided remainder (the actual `subresPRS` recurrence)
The raw step `subresultant_C_mul_eq_rem_of_bpsremainder` relates `Sⱼ(p,q)` to `Sⱼ(q, prem(p,q))` against
the *raw* pseudo-remainder. The actual `subresPRS` recurrence forms the next element as
`r = bdivC fuel (prem p q) β` — the β-divided pseudo-remainder (exact `ℚ[t]`-division stripping the
`lc`-power inflation). Folding in the β-divisor exact-division `toBPoly_bdivC_exact`, the relation reads
directly on the divided element `r`, the form the chain induction telescopes. -/

/-- **One subresultant-PRS step on the β-divided remainder** (the literal `subresPRS` recurrence step):
with `A = toBPoly p`, `B = toBPoly q`, and `r = bdivC fuel (bpsremainder fuel p q) β` the next PRS
element (so `toPoly β` divides every `x`-coefficient of `bpsremainder fuel p q` exactly), the
pseudo-division content factor `(s, c)` and the β-content combine to
`C((toPoly c)^(m−j)) · Sⱼ(A,B; n,m) = (-1)^((m−j)(n−j)) · C((toPoly β)^(m−j)) · Sⱼ(B, toBPoly r; m,n)`.
Composes `subresultant_C_mul_eq_rem_of_bpsremainder` (the raw step) with the β-divisor exact-division
`toBPoly_bdivC_exact` (restoring `toBPoly (bpsremainder…) = C(toPoly β)·toBPoly r`) and the
second-argument scaling `subresultant_C_mul_right`. This is the literal one-step law of `subresPRS`. -/
theorem subresultant_C_mul_eq_bdivC_of_bpsremainder (fuel : ℕ) (p q : BPoly) (β : CPoly) (n m j : ℕ)
    (s : BPoly) (c : CPoly)
    (hsc : Polynomial.C (toPoly c) * toBPoly p
        = toBPoly s * toBPoly q + toBPoly (bpsremainder fuel p q))
    (hβ : cnorm β ≠ [])
    (hdiv : ∀ a ∈ bpsremainder fuel p q, toPoly (cmod fuel a β) = 0)
    (hjm : j ≤ m) (hjn : j < n)
    (hB : (toBPoly q).natDegree ≤ m)
    (hQ : (toBPoly s).natDegree + m ≤ n) :
    Polynomial.C ((toPoly c) ^ (m - j)) * subresultant (toBPoly p) (toBPoly q) n m j
      = (-1 : (ℚ[X])[X]) ^ ((m - j) * (n - j))
        * (Polynomial.C ((toPoly β) ^ (m - j))
          * subresultant (toBPoly q) (toBPoly (bdivC fuel (bpsremainder fuel p q) β)) m n j) := by
  have hstep := subresultant_C_mul_eq_rem_of_bpsremainder fuel p q n m j s c hsc hjm hjn hB hQ
  have hexact : toBPoly (bpsremainder fuel p q)
      = Polynomial.C (toPoly β) * toBPoly (bdivC fuel (bpsremainder fuel p q) β) :=
    (toBPoly_bdivC_exact fuel (bpsremainder fuel p q) β hβ hdiv).symm
  rw [hstep, hexact,
    subresultant_C_mul_right (toPoly β) (toBPoly q)
      (toBPoly (bdivC fuel (bpsremainder fuel p q) β)) m n j (le_of_lt hjn) hjm]

/-- **LRT subresultant after one β-divided PRS step** (the literal first chain step of
`lrtSubresultantCompute`/`subresPRS` on the LRT operands): with the book's formal degrees `n = deg D`,
`m = deg D − 1`, `P = liftCtoBPoly D`, `Q = bArgAmtD' A D`, `(s, c)` the `toBPoly_bpsremainder` witnesses
and `R₃ = bdivC fuel (bpsremainder fuel P Q) β` the next `subresPRS` element (β dividing every
`x`-coefficient of the pseudo-remainder), the abstract `lrtSubresultant A D j` satisfies
`C((toPoly c)^(m−j)) · lrtSubresultant A D j = (-1)^((m−j)(n−j)) · C((toPoly β)^(m−j)) · Sⱼ(Q, R₃; m,n)`.
This is `subresultant_C_mul_eq_bdivC_of_bpsremainder` (with `p = P`, `q = Q`) transported across
`lrtSubresultant_eq_subresultant_toBPoly` — the LRT subresultant as one *divided* step of `subresPRS`,
the chain-recurrence entry point whose iterate is the full `lrtGcdCompute ↔ lrtSubresultant` agreement. -/
theorem lrtSubresultant_C_mul_eq_bdivC_of_bpsremainder (fuel : ℕ) (A D : CPoly) (β : CPoly) (j : ℕ)
    (s : BPoly) (c : CPoly)
    (hsc : Polynomial.C (toPoly c) * toBPoly (liftCtoBPoly D)
        = toBPoly s * toBPoly (bArgAmtD' A D)
          + toBPoly (bpsremainder fuel (liftCtoBPoly D) (bArgAmtD' A D)))
    (hβ : cnorm β ≠ [])
    (hdiv : ∀ a ∈ bpsremainder fuel (liftCtoBPoly D) (bArgAmtD' A D), toPoly (cmod fuel a β) = 0)
    (hjm : j ≤ (toPoly D).natDegree - 1) (hjn : j < (toPoly D).natDegree)
    (hB : (toBPoly (bArgAmtD' A D)).natDegree ≤ (toPoly D).natDegree - 1)
    (hQ : (toBPoly s).natDegree + ((toPoly D).natDegree - 1) ≤ (toPoly D).natDegree) :
    Polynomial.C ((toPoly c) ^ (((toPoly D).natDegree - 1) - j))
        * lrtSubresultant (toPoly A) (toPoly D) j
      = (-1 : (ℚ[X])[X]) ^ ((((toPoly D).natDegree - 1) - j) * ((toPoly D).natDegree - j))
        * (Polynomial.C ((toPoly β) ^ (((toPoly D).natDegree - 1) - j))
          * subresultant (toBPoly (bArgAmtD' A D))
              (toBPoly (bdivC fuel (bpsremainder fuel (liftCtoBPoly D) (bArgAmtD' A D)) β))
              ((toPoly D).natDegree - 1) (toPoly D).natDegree j) := by
  rw [lrtSubresultant_eq_subresultant_toBPoly]
  exact subresultant_C_mul_eq_bdivC_of_bpsremainder fuel (liftCtoBPoly D) (bArgAmtD' A D) β
    (toPoly D).natDegree ((toPoly D).natDegree - 1) j s c hsc hβ hdiv hjm hjn hB hQ

/-! ### The one-step PRS reduction as a `ℚ[t]`-similarity (the "up to content/unit" form)
The `C(...)` content factors of the one-divided-step law are all `C`-of-constants in `ℚ[t] = ℚ[X]`, so —
when those factors are nonzero — the law reads as a `ℚ[t]`-**similarity** `IsSimilar` (Bronstein §1.5's
"similar" relation, `PseudoDivision`): the LRT subresultant is similar over `ℚ[t]` to the abstract
subresultant of the next divided PRS pair. This is the exact sense in which the chain agreement holds
"up to a `ℚ[t]` content/unit", at the one-step level. -/

/-- **One divided PRS step as a `ℚ[t]`-similarity**: under the β-divided step hypotheses, with the
content factors nonzero (`toPoly c ≠ 0`, `toPoly β ≠ 0`), the LRT subresultant is *similar over `ℚ[t]`*
to the abstract subresultant of the next divided PRS pair `(Q, R₃)`:
`IsSimilar (lrtSubresultant A D j) (Sⱼ(Q, bdivC … prem; m, n))`. Packages
`lrtSubresultant_C_mul_eq_bdivC_of_bpsremainder` as the similarity witnesses
`(toPoly c)^(m−j)` and `(-1)^((m−j)(n−j))·(toPoly β)^(m−j)` (the `(-1)^…` absorbed into the `C`-constant).
This is the "up to `ℚ[t]` content/unit" chain agreement at one divided step. -/
theorem isSimilar_lrtSubresultant_subresultant_bdivC (fuel : ℕ) (A D : CPoly) (β : CPoly) (j : ℕ)
    (s : BPoly) (c : CPoly)
    (hsc : Polynomial.C (toPoly c) * toBPoly (liftCtoBPoly D)
        = toBPoly s * toBPoly (bArgAmtD' A D)
          + toBPoly (bpsremainder fuel (liftCtoBPoly D) (bArgAmtD' A D)))
    (hβ : cnorm β ≠ [])
    (hdiv : ∀ a ∈ bpsremainder fuel (liftCtoBPoly D) (bArgAmtD' A D), toPoly (cmod fuel a β) = 0)
    (hc0 : toPoly c ≠ 0) (hβ0 : toPoly β ≠ 0)
    (hjm : j ≤ (toPoly D).natDegree - 1) (hjn : j < (toPoly D).natDegree)
    (hB : (toBPoly (bArgAmtD' A D)).natDegree ≤ (toPoly D).natDegree - 1)
    (hQ : (toBPoly s).natDegree + ((toPoly D).natDegree - 1) ≤ (toPoly D).natDegree) :
    IsSimilar (lrtSubresultant (toPoly A) (toPoly D) j)
      (subresultant (toBPoly (bArgAmtD' A D))
        (toBPoly (bdivC fuel (bpsremainder fuel (liftCtoBPoly D) (bArgAmtD' A D)) β))
        ((toPoly D).natDegree - 1) (toPoly D).natDegree j) := by
  refine ⟨(toPoly c) ^ (((toPoly D).natDegree - 1) - j),
    (-1 : ℚ[X]) ^ ((((toPoly D).natDegree - 1) - j) * ((toPoly D).natDegree - j))
      * (toPoly β) ^ (((toPoly D).natDegree - 1) - j),
    pow_ne_zero _ hc0,
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hβ0), ?_⟩
  rw [lrtSubresultant_C_mul_eq_bdivC_of_bpsremainder fuel A D β j s c hsc hβ hdiv hjm hjn hB hQ]
  simp only [Polynomial.C_mul, map_pow, map_neg, map_one]
  ring

/-! ### Telescoping the divided one-step similarity along the whole `subresPRS`
The divided one-step law `subresultant_C_mul_eq_bdivC_of_bpsremainder` relates `Sⱼ(p,q)` to `Sⱼ(q,r)`
for the *literal* `subresPRS` recurrence `r = bdivC fuel (prem p q) β`. The **multi-step** agreement is its
telescoping along an entire chain of `BPoly` elements `G : ℕ → BPoly` (where `G i` is the `i`-th element of
the computable PRS), each consecutive pair `(G i, G (i+1))` satisfying the divided one-step hypotheses with
its own pseudo-division witnesses `(s i, c i)` and β-divisor `β i`. Packaging the one step as a generic
`IsSimilar` (over arbitrary `BPoly`s, with a per-index formal-degree function `d : ℕ → ℕ`) and chaining
through `IsSimilar.trans` lands `IsSimilar (Sⱼ(G 0, G 1)) (Sⱼ(G n, G (n+1)))` for every `n` — the full
chain agreement, *without* matching the computable `cpowP`/`cdiv` β/ψ accumulators against the abstract
`subresPRS_beta`/`subresPRS_gamma`: every per-step constant is absorbed by `IsSimilar`. The accumulator
algebra only governs *which* `BPoly` is `G i` and *which* scalar `β i` divides the pseudo-remainder; those
enter purely as the per-step hypotheses, discharged once for the real `subresPRS` at the application site. -/

/-- **Generic divided one-step similarity** (the chain link, over arbitrary `BPoly`s): if
`r = bdivC fuel (bpsremainder fuel p q) β` is the next divided PRS element (β dividing every
`x`-coefficient of the pseudo-remainder exactly), the pseudo-division witnesses `(s, c)` are nonzero under
`toPoly`, and the degree side-conditions hold, then the subresultant of `(p, q)` at formal degrees `(n, m)`
is `ℚ[t]`-similar to that of `(q, r)` at `(m, n')`:
`IsSimilar (Sⱼ(toBPoly p, toBPoly q; n, m)) (Sⱼ(toBPoly q, toBPoly r; m, n'))` (`n' = n` here; the `n'`
slot is kept explicit so a degree chain can supply `deg (G (i+2))`'s formal padding). The repackaging of
`subresultant_C_mul_eq_bdivC_of_bpsremainder` into `IsSimilar` — the `(-1)^…`-and-content factors are the
similarity witnesses. -/
theorem isSimilar_subresultant_bdivC_step (fuel : ℕ) (p q : BPoly) (β : CPoly) (n m j : ℕ)
    (s : BPoly) (c : CPoly)
    (hsc : Polynomial.C (toPoly c) * toBPoly p
        = toBPoly s * toBPoly q + toBPoly (bpsremainder fuel p q))
    (hβ : cnorm β ≠ [])
    (hdiv : ∀ a ∈ bpsremainder fuel p q, toPoly (cmod fuel a β) = 0)
    (hc0 : toPoly c ≠ 0) (hβ0 : toPoly β ≠ 0)
    (hjm : j ≤ m) (hjn : j < n)
    (hB : (toBPoly q).natDegree ≤ m)
    (hQ : (toBPoly s).natDegree + m ≤ n) :
    IsSimilar (subresultant (toBPoly p) (toBPoly q) n m j)
      (subresultant (toBPoly q) (toBPoly (bdivC fuel (bpsremainder fuel p q) β)) m n j) := by
  refine ⟨(toPoly c) ^ (m - j),
    (-1 : ℚ[X]) ^ ((m - j) * (n - j)) * (toPoly β) ^ (m - j),
    pow_ne_zero _ hc0,
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hβ0), ?_⟩
  rw [subresultant_C_mul_eq_bdivC_of_bpsremainder fuel p q β n m j s c hsc hβ hdiv hjm hjn hB hQ]
  simp only [Polynomial.C_mul, map_pow, map_neg, map_one]
  ring

/-- **The combined per-step PRS relation through `toBPoly`** (the bridge into the abstract telescope):
combining the pseudo-division identity `C(toPoly c)·toBPoly p = toBPoly s·toBPoly q + toBPoly (prem p q)`
with the β-divisor exact division `toBPoly (prem p q) = C(toPoly β)·toBPoly r`
(`r = bdivC fuel (prem p q) β`), the computable PRS step reads as the **abstract** Brown–Traub PRS
relation with constant scalars: `C(toPoly c)·toBPoly p = C(toPoly β)·toBPoly r + toBPoly s·toBPoly q`.
This is the exact `hrel` shape `subresultant_prs_telescope` (`SubresultantPRS`) consumes — so the computable
chain feeds the abstract telescope verbatim, with `α = toPoly c`, `β = toPoly β`, `Q = toBPoly s`. -/
theorem toBPoly_prs_rel (fuel : ℕ) (p q : BPoly) (β : CPoly) (s : BPoly) (c : CPoly)
    (hsc : Polynomial.C (toPoly c) * toBPoly p
        = toBPoly s * toBPoly q + toBPoly (bpsremainder fuel p q))
    (hβ : cnorm β ≠ [])
    (hdiv : ∀ a ∈ bpsremainder fuel p q, toPoly (cmod fuel a β) = 0) :
    Polynomial.C (toPoly c) * toBPoly p
      = Polynomial.C (toPoly β) * toBPoly (bdivC fuel (bpsremainder fuel p q) β)
        + toBPoly q * toBPoly s := by
  rw [hsc, toBPoly_bdivC_exact fuel (bpsremainder fuel p q) β hβ hdiv]; ring

/-! ### The abstract-PRS telescope over the computable chain (the full multi-step agreement)
With the combined relation `toBPoly_prs_rel` in hand, the computable `subresPRS` chain — realized as an
abstract sequence `F i := toBPoly (G i)` of `(ℚ[X])[X]` polynomials — satisfies the Brown–Traub PRS
relation verbatim (constant scalars `α i = toPoly (c i)`, `β i = toPoly (β i)`, quotient
`Q i = toBPoly (s i)`). So the abstract Fundamental PRS Theorem `subresultant_prs_telescope`
(`SubresultantPRS`) telescopes the *whole* chain in one shot: `Sⱼ(F 0, F 1) ~ Sⱼ(F m, F (m+1))` at the
elements' own degrees, for every `m`. This is the multi-step agreement the one-step engine was the link
for — the `IsSimilar.trans` chaining is performed inside `subresultant_prs_telescope`, so no manual
accumulator matching is needed: every per-step `α/β` constant is a `toPoly` content factor absorbed by the
similarity. -/

/-- **Full chain telescope through `toBPoly`** (the multi-step `subresPRS ↔ subresultant` agreement): for a
computable PRS chain `G : ℕ → BPoly` whose consecutive elements satisfy the divided one-step hypotheses —
the pseudo-division witnesses `(s l, c l)`, the β-divisors `bt l` dividing every `x`-coefficient of the
pseudo-remainder (`hsc`, `hβcn`, `hdiv`), the next element `G (l+2) = bdivC fuel (prem (G l) (G (l+1)))
(bt l)` (`hG2`), and the degree side-conditions on the elements' own `natDegree`s (nonzero leading
coefficients `hlc`, strict decrease `hcb`, the index bound `hj`, quotient bound `hQ`) — the subresultant of
`(G 0, G 1)` is `ℚ[t]`-similar to that of `(G m, G (m+1))`:
`IsSimilar (Sⱼ(toBPoly (G 0), toBPoly (G 1))) (Sⱼ(toBPoly (G m), toBPoly (G (m+1))))`. The computable chain
is fed to the abstract `subresultant_prs_telescope` via the combined relation `toBPoly_prs_rel`; the whole
`IsSimilar.trans` telescoping happens inside it. -/
theorem isSimilar_subresPRS_telescope (fuel : ℕ) (G : ℕ → BPoly)
    (bt : ℕ → CPoly) (s : ℕ → BPoly) (c : ℕ → CPoly) (j m : ℕ)
    (hsc : ∀ l < m, Polynomial.C (toPoly (c l)) * toBPoly (G l)
        = toBPoly (s l) * toBPoly (G (l + 1)) + toBPoly (bpsremainder fuel (G l) (G (l + 1))))
    (hβcn : ∀ l < m, cnorm (bt l) ≠ [])
    (hdiv : ∀ l < m, ∀ a ∈ bpsremainder fuel (G l) (G (l + 1)), toPoly (cmod fuel a (bt l)) = 0)
    (hG2 : ∀ l < m, G (l + 2) = bdivC fuel (bpsremainder fuel (G l) (G (l + 1))) (bt l))
    (hc0 : ∀ l < m, toPoly (c l) ≠ 0) (hβ0 : ∀ l < m, toPoly (bt l) ≠ 0)
    (hlc : ∀ l < m, (toBPoly (G (l + 1))).coeff (toBPoly (G (l + 1))).natDegree ≠ 0)
    (hcb : ∀ l < m, (toBPoly (G (l + 2))).natDegree < (toBPoly (G (l + 1))).natDegree)
    (hj : ∀ l < m, j < (toBPoly (G (l + 2))).natDegree)
    (hQ : ∀ l < m, (toBPoly (s l)).natDegree + (toBPoly (G (l + 1))).natDegree
      ≤ (toBPoly (G l)).natDegree) :
    IsSimilar
      (subresultant (toBPoly (G 0)) (toBPoly (G 1))
        (toBPoly (G 0)).natDegree (toBPoly (G 1)).natDegree j)
      (subresultant (toBPoly (G m)) (toBPoly (G (m + 1)))
        (toBPoly (G m)).natDegree (toBPoly (G (m + 1))).natDegree j) :=
  subresultant_prs_telescope (fun i => toBPoly (G i)) (fun l => toPoly (c l))
    (fun l => toPoly (bt l)) (fun l => toBPoly (s l)) j m
    hc0 hβ0 hlc hcb hj hQ
    (fun l hl => by
      have hrel := toBPoly_prs_rel fuel (G l) (G (l + 1)) (bt l) (s l) (c l)
        (hsc l hl) (hβcn l hl) (hdiv l hl)
      rw [hG2 l hl]; exact hrel)

/-! ### The chain endpoint: `Sⱼ` is similar to the degree-`j` `subresPRS` element
`isSimilar_subresPRS_telescope` lands the chain *endpoint* `Sⱼ(G m, G (m+1))`. At the **regular index**
`j = deg (toBPoly (G (m+2)))` — the degree of the next PRS element — the abstract Fundamental PRS Theorem
`subresultant_prs_similar_elt` collapses the endpoint subresultant all the way to that element
`toBPoly (G (m+2))` itself (the telescope's `IsSimilar.trans` plus the regular-index remainder step). So
`Sⱼ(toBPoly (G 0), toBPoly (G 1)) ~ toBPoly (G (m+2))` — the subresultant of the first pair is similar to
the degree-`j` chain element, which is exactly what the computable `bsubresultantGcd` filters out. -/

/-- **`Sⱼ` similar to the degree-`j` `subresPRS` element** (the endpoint of the chain agreement, regular
index): with the per-step divided-PRS hypotheses on the chain `G` (as in `isSimilar_subresPRS_telescope`,
now over `l ≤ m`), the index `j = deg (toBPoly (G (m+2)))` strictly below every earlier element
(`hjlt`), and `toBPoly (G (m+2)) ≠ 0` (`hCne`), the subresultant of `(G 0, G 1)` at that index is
`ℚ[t]`-similar to the element `toBPoly (G (m+2))`:
`IsSimilar (Sⱼ(toBPoly (G 0), toBPoly (G 1))) (toBPoly (G (m+2)))`. The `toBPoly` instance of
`subresultant_prs_similar_elt`, fed the combined relation `toBPoly_prs_rel` at each step. -/
theorem isSimilar_subresPRS_elt (fuel : ℕ) (G : ℕ → BPoly)
    (bt : ℕ → CPoly) (s : ℕ → BPoly) (c : ℕ → CPoly) (m : ℕ)
    (hsc : ∀ l ≤ m, Polynomial.C (toPoly (c l)) * toBPoly (G l)
        = toBPoly (s l) * toBPoly (G (l + 1)) + toBPoly (bpsremainder fuel (G l) (G (l + 1))))
    (hβcn : ∀ l ≤ m, cnorm (bt l) ≠ [])
    (hdiv : ∀ l ≤ m, ∀ a ∈ bpsremainder fuel (G l) (G (l + 1)), toPoly (cmod fuel a (bt l)) = 0)
    (hG2 : ∀ l ≤ m, G (l + 2) = bdivC fuel (bpsremainder fuel (G l) (G (l + 1))) (bt l))
    (hc0 : ∀ l ≤ m, toPoly (c l) ≠ 0) (hβ0 : ∀ l ≤ m, toPoly (bt l) ≠ 0)
    (hlc : ∀ l ≤ m, (toBPoly (G (l + 1))).coeff (toBPoly (G (l + 1))).natDegree ≠ 0)
    (hcb : ∀ l ≤ m, (toBPoly (G (l + 2))).natDegree < (toBPoly (G (l + 1))).natDegree)
    (hjlt : ∀ l < m, (toBPoly (G (m + 2))).natDegree < (toBPoly (G (l + 2))).natDegree)
    (hQ : ∀ l ≤ m, (toBPoly (s l)).natDegree + (toBPoly (G (l + 1))).natDegree
      ≤ (toBPoly (G l)).natDegree)
    (hCne : toBPoly (G (m + 2)) ≠ 0) :
    IsSimilar
      (subresultant (toBPoly (G 0)) (toBPoly (G 1))
        (toBPoly (G 0)).natDegree (toBPoly (G 1)).natDegree (toBPoly (G (m + 2))).natDegree)
      (toBPoly (G (m + 2))) :=
  subresultant_prs_similar_elt (fun i => toBPoly (G i)) (fun l => toPoly (c l))
    (fun l => toPoly (bt l)) (fun l => toBPoly (s l)) m
    hc0 hβ0 hlc hcb hjlt hQ
    (fun l hl => by
      have hrel := toBPoly_prs_rel fuel (G l) (G (l + 1)) (bt l) (s l) (c l)
        (hsc l hl) (hβcn l hl) (hdiv l hl)
      rw [hG2 l hl]; exact hrel)
    hCne

/-! ### LRT endpoint: `lrtSubresultant` similar to the degree-`j` `subresPRS` element
Specializing `isSimilar_subresPRS_elt` to the LRT chain — `G 0 = liftCtoBPoly D`, `G 1 = bArgAmtD' A D`
(the operands of `lrtSubresultant`, via `lrtSubresultant_eq_subresultant_toBPoly`) — and using that
`toBPoly (liftCtoBPoly D)` has `x`-degree `deg D` and `toBPoly (bArgAmtD' A D)` has `x`-degree `deg D − 1`
(the regular LRT case, taken as hypotheses), the **abstract** `lrtSubresultant A D j` at the index
`j = deg (toBPoly (G (m+2)))` is `ℚ[t]`-similar to the degree-`j` computable PRS element. This is the
endpoint of the LRT chain agreement: the noncomputable LRT subresultant matches the computable engine's
degree-`j` subresultant-PRS element up to a `ℚ[t]` content/unit. -/

/-- **`lrtSubresultant` similar to the degree-`j` LRT `subresPRS` element** (the LRT chain endpoint): for
the LRT chain `G` with `G 0 = liftCtoBPoly D`, `G 1 = bArgAmtD' A D`, formal-degree agreement
`hd0 : (toBPoly (G 0)).natDegree = (toPoly D).natDegree`,
`hd1 : (toBPoly (G 1)).natDegree = (toPoly D).natDegree − 1` (the regular case), and the per-step divided
hypotheses, the abstract `lrtSubresultant A D (deg (toBPoly (G (m+2))))` is similar to `toBPoly (G (m+2))`:
`IsSimilar (lrtSubresultant A D (deg (G (m+2)))) (toBPoly (G (m+2)))`. Transports `isSimilar_subresPRS_elt`
across `lrtSubresultant_eq_subresultant_toBPoly` (with the two formal-degree rewrites). -/
theorem isSimilar_lrtSubresultant_subresPRS_elt (fuel : ℕ) (A D : CPoly) (G : ℕ → BPoly)
    (bt : ℕ → CPoly) (s : ℕ → BPoly) (c : ℕ → CPoly) (m : ℕ)
    (hG0 : G 0 = liftCtoBPoly D) (hG1 : G 1 = bArgAmtD' A D)
    (hd0 : (toBPoly (G 0)).natDegree = (toPoly D).natDegree)
    (hd1 : (toBPoly (G 1)).natDegree = (toPoly D).natDegree - 1)
    (hsc : ∀ l ≤ m, Polynomial.C (toPoly (c l)) * toBPoly (G l)
        = toBPoly (s l) * toBPoly (G (l + 1)) + toBPoly (bpsremainder fuel (G l) (G (l + 1))))
    (hβcn : ∀ l ≤ m, cnorm (bt l) ≠ [])
    (hdiv : ∀ l ≤ m, ∀ a ∈ bpsremainder fuel (G l) (G (l + 1)), toPoly (cmod fuel a (bt l)) = 0)
    (hG2 : ∀ l ≤ m, G (l + 2) = bdivC fuel (bpsremainder fuel (G l) (G (l + 1))) (bt l))
    (hc0 : ∀ l ≤ m, toPoly (c l) ≠ 0) (hβ0 : ∀ l ≤ m, toPoly (bt l) ≠ 0)
    (hlc : ∀ l ≤ m, (toBPoly (G (l + 1))).coeff (toBPoly (G (l + 1))).natDegree ≠ 0)
    (hcb : ∀ l ≤ m, (toBPoly (G (l + 2))).natDegree < (toBPoly (G (l + 1))).natDegree)
    (hjlt : ∀ l < m, (toBPoly (G (m + 2))).natDegree < (toBPoly (G (l + 2))).natDegree)
    (hQ : ∀ l ≤ m, (toBPoly (s l)).natDegree + (toBPoly (G (l + 1))).natDegree
      ≤ (toBPoly (G l)).natDegree)
    (hCne : toBPoly (G (m + 2)) ≠ 0) :
    IsSimilar (lrtSubresultant (toPoly A) (toPoly D) (toBPoly (G (m + 2))).natDegree)
      (toBPoly (G (m + 2))) := by
  have hend := isSimilar_subresPRS_elt fuel G bt s c m hsc hβcn hdiv hG2 hc0 hβ0 hlc hcb hjlt hQ hCne
  rw [hd0, hd1] at hend
  rw [lrtSubresultant_eq_subresultant_toBPoly, ← hG0, ← hG1]
  exact hend

/-! ### `bsubresultantGcd ∼ lrtSubresultant` (the chain agreement, modulo the degree-`j` filter identity)
The endpoint `isSimilar_lrtSubresultant_subresPRS_elt` lands `lrtSubresultant A D j ~ toBPoly (G (m+2))`,
the abstract LRT subresultant similar to the **degree-`j` computable PRS element** `G (m+2)`. The computable
`bsubresultantGcd fuel j P Q` extracts that same element by a degree-`j` filter over the `subresPRS` list;
since the chain's degrees strictly decrease, the degree-`j` element is unique, so the filter returns exactly
`G (m+2)`. Taking that **filter identity** `toBPoly (bsubresultantGcd fuel j P Q) = toBPoly (G (m+2))` as a
hypothesis (the one remaining list-structure fact — see the ceiling note), the agreement
`IsSimilar (lrtSubresultant A D j) (toBPoly (bsubresultantGcd fuel j P Q))` follows by `Eq ▸` on the
endpoint similarity. This isolates the residual gap to a *single* purely-structural list identity. -/

/-! #### The degree-`j` filter identity, structurally (discharging `hfilt` for the real `subresPRS`)
`bsubresultantGcd fuel j P Q` filters the chain `subresPRS fuel P Q` to its degree-`j` nonzero elements
and takes the **last**. Since the `subresPRS` `x`-degrees strictly decrease, the degree-`j` element is
**unique**, so the filtered list is a singleton and the last element *is* that one element — the chain's
degree-`j` element `G (m+2)`. These lemmas turn that uniqueness into the literal filter identity `hfilt`,
abstracted over the list (so it applies to the real `subresPRS` once the chain element is exhibited at the
filtered position). -/

/-- **Filter-last is the unique filtered element**: if filtering a list `L` by a predicate yields a
*singleton* `[w]`, the `getLast?.getD d` read of the filter returns exactly `w`. The list-structure core of
the degree-`j` filter identity: a singleton filter has its single element as its last. -/
theorem getLast?_getD_filter_eq_of_singleton {α : Type*} (L : List α) (pred : α → Bool) (w d : α)
    (hfil : L.filter pred = [w]) :
    (L.filter pred).getLast?.getD d = w := by
  rw [hfil, List.getLast?_singleton, Option.getD_some]

/-- **`bsubresultantGcd` reads as the singleton-filtered element**: if the degree-`j` nonzero filter of
`subresPRS fuel P Q` is a singleton `[w]`, then `bsubresultantGcd fuel j P Q = w`. Unfolds
`bsubresultantGcd` and applies `getLast?_getD_filter_eq_of_singleton`. -/
theorem bsubresultantGcd_eq_of_filter_singleton (fuel j : ℕ) (P Q : BPoly) (w : BPoly)
    (hfil : (subresPRS fuel P Q).filter (fun R => decide (bdeg R = j ∧ ¬ bisZero R)) = [w]) :
    bsubresultantGcd fuel j P Q = w := by
  rw [bsubresultantGcd]
  exact getLast?_getD_filter_eq_of_singleton _ _ w [] hfil

/-- **The degree-`j` filter identity** (the `hfilt` hypothesis, structurally): if the degree-`j` nonzero
filter of `subresPRS fuel P Q` is the singleton `[G (m+2)]` (the chain element of `x`-degree `j` —
the unique such element, by strict degree decrease), then `bsubresultantGcd fuel j P Q = G (m+2)`, hence
`toBPoly (bsubresultantGcd fuel j P Q) = toBPoly (G (m+2))` — the literal `hfilt` of
`isSimilar_lrtSubresultant_bsubresultantGcd`. So exhibiting the chain's degree-`j` element as the sole
filtered element discharges `hfilt`. -/
theorem toBPoly_bsubresultantGcd_eq_of_filter_singleton (fuel : ℕ) (P Q : BPoly) (G : ℕ → BPoly) (m : ℕ)
    (hfil : (subresPRS fuel P Q).filter
        (fun R => decide (bdeg R = (toBPoly (G (m + 2))).natDegree ∧ ¬ bisZero R)) = [G (m + 2)]) :
    toBPoly (bsubresultantGcd fuel (toBPoly (G (m + 2))).natDegree P Q) = toBPoly (G (m + 2)) := by
  rw [bsubresultantGcd_eq_of_filter_singleton fuel (toBPoly (G (m + 2))).natDegree P Q (G (m + 2)) hfil]

/-- **`bsubresultantGcd ∼ lrtSubresultant`, modulo the filter identity** (the chain agreement, endpoint
form): under the LRT-chain endpoint hypotheses (as in `isSimilar_lrtSubresultant_subresPRS_elt`) and the
**filter identity** `hfilt : toBPoly (bsubresultantGcd fuel (deg (G (m+2))) (G 0) (G 1)) = toBPoly (G (m+2))`
— that the computable degree-`j` filter returns the chain's degree-`j` element (true since strict degree
decrease makes that element unique) — the computable `bsubresultantGcd` is `ℚ[t]`-similar to the abstract
`lrtSubresultant`: `IsSimilar (lrtSubresultant A D j) (toBPoly (bsubresultantGcd fuel j (G 0) (G 1)))` at
`j = deg (toBPoly (G (m+2)))`. The endpoint similarity `isSimilar_lrtSubresultant_subresPRS_elt` rewritten
through `hfilt`. The hypothesis `hfilt` isolates the sole remaining list-structure fact. -/
theorem isSimilar_lrtSubresultant_bsubresultantGcd (fuel : ℕ) (A D : CPoly) (G : ℕ → BPoly)
    (bt : ℕ → CPoly) (s : ℕ → BPoly) (c : ℕ → CPoly) (m : ℕ)
    (hG0 : G 0 = liftCtoBPoly D) (hG1 : G 1 = bArgAmtD' A D)
    (hd0 : (toBPoly (G 0)).natDegree = (toPoly D).natDegree)
    (hd1 : (toBPoly (G 1)).natDegree = (toPoly D).natDegree - 1)
    (hsc : ∀ l ≤ m, Polynomial.C (toPoly (c l)) * toBPoly (G l)
        = toBPoly (s l) * toBPoly (G (l + 1)) + toBPoly (bpsremainder fuel (G l) (G (l + 1))))
    (hβcn : ∀ l ≤ m, cnorm (bt l) ≠ [])
    (hdiv : ∀ l ≤ m, ∀ a ∈ bpsremainder fuel (G l) (G (l + 1)), toPoly (cmod fuel a (bt l)) = 0)
    (hG2 : ∀ l ≤ m, G (l + 2) = bdivC fuel (bpsremainder fuel (G l) (G (l + 1))) (bt l))
    (hc0 : ∀ l ≤ m, toPoly (c l) ≠ 0) (hβ0 : ∀ l ≤ m, toPoly (bt l) ≠ 0)
    (hlc : ∀ l ≤ m, (toBPoly (G (l + 1))).coeff (toBPoly (G (l + 1))).natDegree ≠ 0)
    (hcb : ∀ l ≤ m, (toBPoly (G (l + 2))).natDegree < (toBPoly (G (l + 1))).natDegree)
    (hjlt : ∀ l < m, (toBPoly (G (m + 2))).natDegree < (toBPoly (G (l + 2))).natDegree)
    (hQ : ∀ l ≤ m, (toBPoly (s l)).natDegree + (toBPoly (G (l + 1))).natDegree
      ≤ (toBPoly (G l)).natDegree)
    (hCne : toBPoly (G (m + 2)) ≠ 0)
    (hfilt : toBPoly (bsubresultantGcd fuel (toBPoly (G (m + 2))).natDegree (G 0) (G 1))
      = toBPoly (G (m + 2))) :
    IsSimilar (lrtSubresultant (toPoly A) (toPoly D) (toBPoly (G (m + 2))).natDegree)
      (toBPoly (bsubresultantGcd fuel (toBPoly (G (m + 2))).natDegree (G 0) (G 1))) := by
  rw [hfilt]
  exact isSimilar_lrtSubresultant_subresPRS_elt fuel A D G bt s c m hG0 hG1 hd0 hd1
    hsc hβcn hdiv hG2 hc0 hβ0 hlc hcb hjlt hQ hCne

/-- **`bsubresultantGcd ∼ lrtSubresultant`, from the singleton filter** (the `hfilt`-free chain agreement):
the same as `isSimilar_lrtSubresultant_bsubresultantGcd`, but instead of taking the filter identity `hfilt`
as a hypothesis, it derives it from the **structural** singleton-filter fact `hfil` — that the degree-`j`
nonzero filter of `subresPRS fuel (G 0) (G 1)` is the singleton `[G (m+2)]` (the chain's degree-`j` element,
unique by strict degree decrease). So the only list-structure input is `hfil` (the filter is a singleton),
which `toBPoly_bsubresultantGcd_eq_of_filter_singleton` turns into the `hfilt` the agreement consumes. -/
theorem isSimilar_lrtSubresultant_bsubresultantGcd_real (fuel : ℕ) (A D : CPoly) (G : ℕ → BPoly)
    (bt : ℕ → CPoly) (s : ℕ → BPoly) (c : ℕ → CPoly) (m : ℕ)
    (hG0 : G 0 = liftCtoBPoly D) (hG1 : G 1 = bArgAmtD' A D)
    (hd0 : (toBPoly (G 0)).natDegree = (toPoly D).natDegree)
    (hd1 : (toBPoly (G 1)).natDegree = (toPoly D).natDegree - 1)
    (hsc : ∀ l ≤ m, Polynomial.C (toPoly (c l)) * toBPoly (G l)
        = toBPoly (s l) * toBPoly (G (l + 1)) + toBPoly (bpsremainder fuel (G l) (G (l + 1))))
    (hβcn : ∀ l ≤ m, cnorm (bt l) ≠ [])
    (hdiv : ∀ l ≤ m, ∀ a ∈ bpsremainder fuel (G l) (G (l + 1)), toPoly (cmod fuel a (bt l)) = 0)
    (hG2 : ∀ l ≤ m, G (l + 2) = bdivC fuel (bpsremainder fuel (G l) (G (l + 1))) (bt l))
    (hc0 : ∀ l ≤ m, toPoly (c l) ≠ 0) (hβ0 : ∀ l ≤ m, toPoly (bt l) ≠ 0)
    (hlc : ∀ l ≤ m, (toBPoly (G (l + 1))).coeff (toBPoly (G (l + 1))).natDegree ≠ 0)
    (hcb : ∀ l ≤ m, (toBPoly (G (l + 2))).natDegree < (toBPoly (G (l + 1))).natDegree)
    (hjlt : ∀ l < m, (toBPoly (G (m + 2))).natDegree < (toBPoly (G (l + 2))).natDegree)
    (hQ : ∀ l ≤ m, (toBPoly (s l)).natDegree + (toBPoly (G (l + 1))).natDegree
      ≤ (toBPoly (G l)).natDegree)
    (hCne : toBPoly (G (m + 2)) ≠ 0)
    (hfil : (subresPRS fuel (G 0) (G 1)).filter
        (fun R => decide (bdeg R = (toBPoly (G (m + 2))).natDegree ∧ ¬ bisZero R)) = [G (m + 2)]) :
    IsSimilar (lrtSubresultant (toPoly A) (toPoly D) (toBPoly (G (m + 2))).natDegree)
      (toBPoly (bsubresultantGcd fuel (toBPoly (G (m + 2))).natDegree (G 0) (G 1))) :=
  isSimilar_lrtSubresultant_bsubresultantGcd fuel A D G bt s c m hG0 hG1 hd0 hd1
    hsc hβcn hdiv hG2 hc0 hβ0 hlc hcb hjlt hQ hCne
    (toBPoly_bsubresultantGcd_eq_of_filter_singleton fuel (G 0) (G 1) G m hfil)

/-! ### `bprimitivePartX` preserves similarity, and `lrtSubresultant ∼ lrtSubresultantCompute`
`toBPoly_bprimitivePartX_exact` says `bprimitivePartX` strips a `ℚ[t]` content factor — a similarity-
preserving operation. Packaged as `IsSimilar`, it gives `toBPoly p ~ toBPoly (bprimitivePartX fuel p)`.
Since `lrtSubresultantCompute fuel j A D = bprimitivePartX fuel (bsubresultantGcd fuel j (liftCtoBPoly D)
(bArgAmtD' A D))`, chaining this through `isSimilar_lrtSubresultant_bsubresultantGcd` (via `IsSimilar.trans`)
lands `lrtSubresultant A D j ~ toBPoly (lrtSubresultantCompute fuel j A D)` — the abstract LRT subresultant
similar to the computable *primitive* LRT subresultant, modulo the same single filter identity. -/

/-- **`bprimitivePartX` preserves `ℚ[t]`-similarity**: `toBPoly p` is similar to `toBPoly (bprimitivePartX
fuel p)` (the stripped content `C(toPoly g)` is the absorbed unit), under the exact-content hypotheses of
`toBPoly_bprimitivePartX_exact`. -/
theorem isSimilar_toBPoly_bprimitivePartX (fuel : ℕ) (p : BPoly)
    (hg : ¬ cisZero (bcontentX fuel p) = true) (hgcn : cnorm (bcontentX fuel p) ≠ [])
    (hg0 : toPoly (bcontentX fuel p) ≠ 0)
    (hrem : ∀ a ∈ bnorm p, toPoly (cmod fuel a (bcontentX fuel p)) = 0) :
    IsSimilar (toBPoly p) (toBPoly (bprimitivePartX fuel p)) :=
  ⟨1, toPoly (bcontentX fuel p), one_ne_zero, hg0, by
    rw [map_one, one_mul, toBPoly_bprimitivePartX_exact fuel p hg hgcn hrem]⟩

/-- **`lrtSubresultant ∼ lrtSubresultantCompute`, modulo the filter identity** (the chain agreement after
the content step): under the LRT-chain endpoint hypotheses, the filter identity `hfilt`, and the content-
exactness of `bprimitivePartX` on the degree-`j` element (`hg`/`hgcn`/`hg0`/`hrem`), the abstract
`lrtSubresultant A D j` is `ℚ[t]`-similar to the computable **primitive** LRT subresultant
`lrtSubresultantCompute fuel j (liftCtoBPoly⁻ …)`. Chains `isSimilar_lrtSubresultant_bsubresultantGcd`
(abstract ∼ raw subresultant) with `isSimilar_toBPoly_bprimitivePartX` (raw ∼ primitive) via
`IsSimilar.trans`. -/
theorem isSimilar_lrtSubresultant_lrtSubresultantCompute (fuel : ℕ) (A D : CPoly) (G : ℕ → BPoly)
    (bt : ℕ → CPoly) (s : ℕ → BPoly) (c : ℕ → CPoly) (m : ℕ)
    (hG0 : G 0 = liftCtoBPoly D) (hG1 : G 1 = bArgAmtD' A D)
    (hd0 : (toBPoly (G 0)).natDegree = (toPoly D).natDegree)
    (hd1 : (toBPoly (G 1)).natDegree = (toPoly D).natDegree - 1)
    (hsc : ∀ l ≤ m, Polynomial.C (toPoly (c l)) * toBPoly (G l)
        = toBPoly (s l) * toBPoly (G (l + 1)) + toBPoly (bpsremainder fuel (G l) (G (l + 1))))
    (hβcn : ∀ l ≤ m, cnorm (bt l) ≠ [])
    (hdiv : ∀ l ≤ m, ∀ a ∈ bpsremainder fuel (G l) (G (l + 1)), toPoly (cmod fuel a (bt l)) = 0)
    (hG2 : ∀ l ≤ m, G (l + 2) = bdivC fuel (bpsremainder fuel (G l) (G (l + 1))) (bt l))
    (hc0 : ∀ l ≤ m, toPoly (c l) ≠ 0) (hβ0 : ∀ l ≤ m, toPoly (bt l) ≠ 0)
    (hlc : ∀ l ≤ m, (toBPoly (G (l + 1))).coeff (toBPoly (G (l + 1))).natDegree ≠ 0)
    (hcb : ∀ l ≤ m, (toBPoly (G (l + 2))).natDegree < (toBPoly (G (l + 1))).natDegree)
    (hjlt : ∀ l < m, (toBPoly (G (m + 2))).natDegree < (toBPoly (G (l + 2))).natDegree)
    (hQ : ∀ l ≤ m, (toBPoly (s l)).natDegree + (toBPoly (G (l + 1))).natDegree
      ≤ (toBPoly (G l)).natDegree)
    (hCne : toBPoly (G (m + 2)) ≠ 0)
    (hfilt : toBPoly (bsubresultantGcd fuel (toBPoly (G (m + 2))).natDegree (G 0) (G 1))
      = toBPoly (G (m + 2)))
    (hg : ¬ cisZero (bcontentX fuel
        (bsubresultantGcd fuel (toBPoly (G (m + 2))).natDegree (G 0) (G 1))) = true)
    (hgcn : cnorm (bcontentX fuel
        (bsubresultantGcd fuel (toBPoly (G (m + 2))).natDegree (G 0) (G 1))) ≠ [])
    (hg0 : toPoly (bcontentX fuel
        (bsubresultantGcd fuel (toBPoly (G (m + 2))).natDegree (G 0) (G 1))) ≠ 0)
    (hrem : ∀ a ∈ bnorm (bsubresultantGcd fuel (toBPoly (G (m + 2))).natDegree (G 0) (G 1)),
      toPoly (cmod fuel a
        (bcontentX fuel (bsubresultantGcd fuel (toBPoly (G (m + 2))).natDegree (G 0) (G 1)))) = 0) :
    IsSimilar (lrtSubresultant (toPoly A) (toPoly D) (toBPoly (G (m + 2))).natDegree)
      (toBPoly (lrtSubresultantCompute fuel (toBPoly (G (m + 2))).natDegree A D)) := by
  have hraw := isSimilar_lrtSubresultant_bsubresultantGcd fuel A D G bt s c m hG0 hG1 hd0 hd1
    hsc hβcn hdiv hG2 hc0 hβ0 hlc hcb hjlt hQ hCne hfilt
  have hprim := isSimilar_toBPoly_bprimitivePartX fuel
    (bsubresultantGcd fuel (toBPoly (G (m + 2))).natDegree (G 0) (G 1)) hg hgcn hg0 hrem
  rw [lrtSubresultantCompute, ← hG0, ← hG1]
  exact hraw.trans hprim

/-! ### The honest ceiling: from the chain agreement to `lrtGcdCompute`
The pieces above now realize the **full multi-step subresultant-PRS chain agreement** of the computable
engine against the abstract subresultant — no longer just one step:
- β-divisor exact-division `toBPoly_bdivC_exact`, the divided one-step law
  `subresultant_C_mul_eq_bdivC_of_bpsremainder` and its `IsSimilar` packaging
  `isSimilar_subresultant_bdivC_step`;
- the combined per-step relation `toBPoly_prs_rel` (computable pseudo-division + β-division = the abstract
  Brown–Traub PRS relation), feeding the **whole-chain telescope** `isSimilar_subresPRS_telescope`
  (`Sⱼ(G 0,G 1) ~ Sⱼ(G m,G (m+1))` for every `m`, via the abstract `subresultant_prs_telescope` — the
  `IsSimilar.trans` chaining is internal, so **no manual `cpowP`/`cdiv` vs `subresPRS_beta`/`_gamma`
  accumulator matching** is needed: every per-step `α/β` is a `toPoly` content factor absorbed by `IsSimilar`);
- the endpoint collapse `isSimilar_subresPRS_elt` (`Sⱼ(G 0,G 1) ~ toBPoly (G (m+2))`, the degree-`j`
  element, via `subresultant_prs_similar_elt`) and its LRT specialization
  `isSimilar_lrtSubresultant_subresPRS_elt` (`lrtSubresultant A D j ~ toBPoly (G (m+2))`);
- `isSimilar_lrtSubresultant_bsubresultantGcd` — `lrtSubresultant A D j ∼ bsubresultantGcd` — modulo the
  single remaining **filter identity** `toBPoly (bsubresultantGcd …) = toBPoly (G (m+2))`;
- the content step `toBPoly_bprimitivePartX_exact` / its similarity packaging
  `isSimilar_toBPoly_bprimitivePartX`, chained into
  `isSimilar_lrtSubresultant_lrtSubresultantCompute` — `lrtSubresultant A D j ∼ lrtSubresultantCompute`
  (same filter-identity modulus + the content exactness of `bprimitivePartX` on the degree-`j` element).

What remains for an *unconditional* `lrtGcdCompute ↔ lrtSubresultant` is purely *structural/computable*
bookkeeping, no longer the recurrence-matching that this work eliminated:
1. **The filter identity** `hfilt`: that `bsubresultantGcd`'s degree-`j` filter over the `subresPRS` list
   returns the chain element `G (m+2)`, with `G i = (subresPRS fuel P Q).getD i []`. Needs the structural
   induction on `subresPRS`'s recursive `go` (each list element is the next divided pseudo-remainder, with
   `bt i` the literal `cpowP`/`cdiv` β-accumulator) plus uniqueness from strict degree decrease — and the
   discharge, for the *real* `subresPRS`, of the per-step hypotheses (`hsc` from `toBPoly_bpsremainder`,
   `hdiv` from Collins's β-divisibility `toBPoly_bdivC_exact_of_dvd`, the degree bounds). The content-
   exactness inputs `hg`/`hgcn`/`hg0`/`hrem` of the content step are the analogous `bcontentX`-divides-
   coefficients structural facts (the `ℚ[t]`-gcd divides each coefficient, over a `cgcdExt` `foldl`).
2. **`bmonicXmodR` normalization** (`lrtGcdCompute = bmonicXmodR R (lrtSubresultantCompute …)`): the monic-
   in-`x` reduction mod `R` is a `ℚ[t]/(R)`-unit operation, so similarity-preserving over the residue ring —
   needs the monic-mod-`R` unit `toBPoly` bridge (a `bredR`/`cinvMod` analogue of `toBPoly_bprimitivePartX_exact`),
   composed with `isSimilar_lrtSubresultant_lrtSubresultantCompute` through `IsSimilar.trans`. (Note this
   step changes the ambient ring to `ℚ[t]/(R)`, so the similarity is over the residue ring, not `ℚ[t]`.)

These are the closing steps; the whole-chain telescoping, endpoint collapse, β-divisor exact-division, the
`bprimitivePartX` content bridge, and operand/similarity packaging proven here are their complete reusable
foundation. -/

-- Restatement: `bdivC` is exact ℚ[t]-division — `C(toPoly c)·toBPoly(bdivC fuel p c) = toBPoly p`
-- when every x-coefficient divides exactly.
example (fuel : ℕ) (p : BPoly) (c : CPoly) (hc : cnorm c ≠ [])
    (hrem : ∀ a ∈ p, toPoly (cmod fuel a c) = 0) :
    Polynomial.C (toPoly c) * toBPoly (bdivC fuel p c) = toBPoly p :=
  toBPoly_bdivC_exact fuel p c hc hrem

-- Restatement: the LRT subresultant is ℚ[t]-similar to the next divided PRS pair's subresultant.
example (fuel : ℕ) (A D β : CPoly) (j : ℕ) (s : BPoly) (c : CPoly)
    (hsc : Polynomial.C (toPoly c) * toBPoly (liftCtoBPoly D)
        = toBPoly s * toBPoly (bArgAmtD' A D)
          + toBPoly (bpsremainder fuel (liftCtoBPoly D) (bArgAmtD' A D)))
    (hβ : cnorm β ≠ [])
    (hdiv : ∀ a ∈ bpsremainder fuel (liftCtoBPoly D) (bArgAmtD' A D), toPoly (cmod fuel a β) = 0)
    (hc0 : toPoly c ≠ 0) (hβ0 : toPoly β ≠ 0)
    (hjm : j ≤ (toPoly D).natDegree - 1) (hjn : j < (toPoly D).natDegree)
    (hB : (toBPoly (bArgAmtD' A D)).natDegree ≤ (toPoly D).natDegree - 1)
    (hQ : (toBPoly s).natDegree + ((toPoly D).natDegree - 1) ≤ (toPoly D).natDegree) :
    IsSimilar (lrtSubresultant (toPoly A) (toPoly D) j)
      (subresultant (toBPoly (bArgAmtD' A D))
        (toBPoly (bdivC fuel (bpsremainder fuel (liftCtoBPoly D) (bArgAmtD' A D)) β))
        ((toPoly D).natDegree - 1) (toPoly D).natDegree j) :=
  isSimilar_lrtSubresultant_subresultant_bdivC fuel A D β j s c hsc hβ hdiv hc0 hβ0 hjm hjn hB hQ

-- Restatement: the WHOLE computable PRS chain telescopes — `Sⱼ(G 0, G 1) ~ Sⱼ(G m, G (m+1))` for any `m`.
example (fuel : ℕ) (G : ℕ → BPoly) (bt : ℕ → CPoly) (s : ℕ → BPoly) (c : ℕ → CPoly) (j m : ℕ)
    (hsc : ∀ l < m, Polynomial.C (toPoly (c l)) * toBPoly (G l)
        = toBPoly (s l) * toBPoly (G (l + 1)) + toBPoly (bpsremainder fuel (G l) (G (l + 1))))
    (hβcn : ∀ l < m, cnorm (bt l) ≠ [])
    (hdiv : ∀ l < m, ∀ a ∈ bpsremainder fuel (G l) (G (l + 1)), toPoly (cmod fuel a (bt l)) = 0)
    (hG2 : ∀ l < m, G (l + 2) = bdivC fuel (bpsremainder fuel (G l) (G (l + 1))) (bt l))
    (hc0 : ∀ l < m, toPoly (c l) ≠ 0) (hβ0 : ∀ l < m, toPoly (bt l) ≠ 0)
    (hlc : ∀ l < m, (toBPoly (G (l + 1))).coeff (toBPoly (G (l + 1))).natDegree ≠ 0)
    (hcb : ∀ l < m, (toBPoly (G (l + 2))).natDegree < (toBPoly (G (l + 1))).natDegree)
    (hj : ∀ l < m, j < (toBPoly (G (l + 2))).natDegree)
    (hQ : ∀ l < m, (toBPoly (s l)).natDegree + (toBPoly (G (l + 1))).natDegree
      ≤ (toBPoly (G l)).natDegree) :
    IsSimilar
      (subresultant (toBPoly (G 0)) (toBPoly (G 1))
        (toBPoly (G 0)).natDegree (toBPoly (G 1)).natDegree j)
      (subresultant (toBPoly (G m)) (toBPoly (G (m + 1)))
        (toBPoly (G m)).natDegree (toBPoly (G (m + 1))).natDegree j) :=
  isSimilar_subresPRS_telescope fuel G bt s c j m hsc hβcn hdiv hG2 hc0 hβ0 hlc hcb hj hQ

end DeepWiki.SymbolicIntegration.Compute
