import DeepWiki.SymbolicIntegration.ComputeCorrectness
import DeepWiki.SymbolicIntegration.SubresultantPRS
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.SpecificDegree

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

/-! ### The `bmonicXmodR` mod-`R` unit bridge (`lrtSubresultantCompute → lrtGcdCompute`)
`lrtGcdCompute = bmonicXmodR R (lrtSubresultantCompute …)`: reduce mod `R`, then multiply every
`x`-coefficient by the mod-`R` inverse of the leading `x`-coefficient (Exercise 2.7's monic-in-`x`
normalization). This is a **unit** operation in the residue ring `ℚ[t]/(R)`, so it preserves similarity
*over `ℚ[t]/(R)`*. We model the residue ring by an **arbitrary** ring hom `φ : ℚ[X] →+* S` killing
`toPoly R` (`hφR : φ (toPoly R) = 0`); the bridge then lands an exact `Φ`-image unit-multiple identity in
`S[x]` (where `Φ = Polynomial.mapRingHom φ`), which is the residue-ring `IsSimilar` content. Working over a
generic `φ` (rather than constructing `ℚ[t]/(R)`) keeps the bridge reusable and quotient-construction-free:
`ℚ[t]/(R)`'s quotient map is one such `φ`. -/

/-- **`credR` agrees mod `R`**: for any ring hom `φ : ℚ[X] →+* S` killing `toPoly R`, the mod-`R` reduction
`credR fuel R c = cmod fuel c R` has the same `φ`-image as `c`: `φ (toPoly (credR fuel R c)) = φ (toPoly c)`.
From the Euclidean identity `toPoly c = q·toPoly R + toPoly (cmod fuel c R)` (`toPoly_cdivmod'`), the
`toPoly R` term maps to `0`. -/
theorem map_toPoly_credR {S : Type*} [CommRing S] (φ : ℚ[X] →+* S) (fuel : ℕ) (R c : CPoly)
    (hR : cnorm R ≠ []) (hφR : φ (toPoly R) = 0) :
    φ (toPoly (credR fuel R c)) = φ (toPoly c) := by
  have hdiv := toPoly_cdivmod' fuel c R hR
  rw [show (cdivmod fuel c R).1 = cdiv fuel c R from rfl,
      show (cdivmod fuel c R).2 = cmod fuel c R from rfl] at hdiv
  rw [credR, hdiv, map_add, map_mul, hφR, mul_zero, zero_add]

/-- **`Φ ∘ toBPoly` ignores a coefficient-wise mod-`R` reduction**: with `Φ = Polynomial.mapRingHom φ` and
`φ` killing `toPoly R`, mapping every `x`-coefficient of `p` through `credR fuel R` leaves the `Φ`-image of
`toBPoly` unchanged: `Φ (toBPoly (p.map (credR fuel R))) = Φ (toBPoly p)`. Coefficient-wise
`map_toPoly_credR`, folded over the `x`-coefficient list through the Horner shape (`Φ` a ring hom). -/
theorem mapRingHom_toBPoly_map_credR {S : Type*} [CommRing S] (φ : ℚ[X] →+* S) (fuel : ℕ) (R : CPoly)
    (p : BPoly) (hR : cnorm R ≠ []) (hφR : φ (toPoly R) = 0) :
    (Polynomial.mapRingHom φ) (toBPoly (p.map (credR fuel R)))
      = (Polynomial.mapRingHom φ) (toBPoly p) := by
  induction p with
  | nil => simp
  | cons a as ih =>
    rw [List.map_cons, toBPoly_cons, toBPoly_cons, map_add, map_add, map_mul, map_mul, ih]
    congr 1
    rw [Polynomial.coe_mapRingHom, Polynomial.map_C, Polynomial.map_C, map_toPoly_credR φ fuel R a hR hφR]

/-- **`bredR` is `Φ`-transparent**: with `Φ = Polynomial.mapRingHom φ` and `φ` killing `toPoly R`, the
mod-`R` reduction `bredR fuel R p` has the same `Φ`-image of `toBPoly` as `p`:
`Φ (toBPoly (bredR fuel R p)) = Φ (toBPoly p)`. Unfolds `bredR` (`bnorm (p.map (credR fuel R))`) through
`toBPoly_bnorm` and `mapRingHom_toBPoly_map_credR`. -/
theorem mapRingHom_toBPoly_bredR {S : Type*} [CommRing S] (φ : ℚ[X] →+* S) (fuel : ℕ) (R : CPoly)
    (p : BPoly) (hR : cnorm R ≠ []) (hφR : φ (toPoly R) = 0) :
    (Polynomial.mapRingHom φ) (toBPoly (bredR fuel R p)) = (Polynomial.mapRingHom φ) (toBPoly p) := by
  rw [bredR, toBPoly_bnorm, mapRingHom_toBPoly_map_credR φ fuel R p hR hφR]

/-- **`cinvMod` is the mod-`R` inverse**: for any ring hom `φ : ℚ[X] →+* S` killing `toPoly R`, when the
extended-Euclidean gcd `g = (cgcdExt fuel c R).1` reduces to a **nonzero constant** `C u` (`hg`, `u ≠ 0` —
Exercise 2.7's regularity that the leading `x`-coefficient is a unit mod `R`), the computable inverse
`cinvMod fuel R c` satisfies `φ (toPoly (cinvMod fuel R c)) · φ (toPoly c) = 1` in `S`. From the Bézout
identity `toPoly s · toPoly c + toPoly t · toPoly R = toPoly g = C u` (`toPoly_cgcdExt`): applying `φ`
kills the `toPoly R` term, giving `φ(toPoly s)·φ(toPoly c) = φ(C u)`; scaling by `u⁻¹` (the `cscale (clead
g)⁻¹` in `cinvMod`, with `clead g = u`) makes the product `1`. -/
theorem map_toPoly_cinvMod_mul {S : Type*} [CommRing S] (φ : ℚ[X] →+* S) (fuel : ℕ) (R c : CPoly)
    (hR : cnorm R ≠ []) (hφR : φ (toPoly R) = 0) {u : ℚ} (hu : u ≠ 0)
    (hg : toPoly (cgcdExt fuel c R).1 = Polynomial.C u) :
    φ (toPoly (cinvMod fuel R c)) * φ (toPoly c) = 1 := by
  -- Bézout: toPoly s · toPoly c + toPoly t · toPoly R = toPoly g = C u
  have hbez := toPoly_cgcdExt fuel c R
  -- clead g = u (leading coeff of the constant C u)
  have hlead : clead (cgcdExt fuel c R).1 = u := by
    rw [clead_eq_leadingCoeff, hg, Polynomial.leadingCoeff_C]
  -- φ image of the inverse: drop the credR, expand the cscale
  rw [cinvMod]
  -- cinvMod fuel R c = credR fuel R (cscale (clead g)⁻¹ s), with s = (cgcdExt fuel c R).2.1
  rw [map_toPoly_credR φ fuel R _ hR hφR, toPoly_cscale, map_mul, hlead]
  -- now: φ (C u⁻¹) * φ (toPoly s) * φ (toPoly c) = 1
  -- from Bézout image: φ(toPoly s)·φ(toPoly c) = φ (C u)
  have himg : φ (toPoly (cgcdExt fuel c R).2.1) * φ (toPoly c) = φ (Polynomial.C u) := by
    have := congrArg φ hbez
    rw [map_add, map_mul, map_mul, hφR, mul_zero, add_zero, hg] at this
    exact this
  rw [mul_assoc, himg, ← map_mul, ← Polynomial.C_mul, inv_mul_cancel₀ hu, Polynomial.C_1, map_one]

/-- **Coefficient-wise `credR ∘ (· * inv)` is `Φ`-scaling by `φ(toPoly inv)`**: with `Φ =
Polynomial.mapRingHom φ` and `φ` killing `toPoly R`, mapping every `x`-coefficient `c ↦ credR fuel R (cmul
c inv)` realizes, under `Φ`, multiplication of `toBPoly q` by the constant `C (φ (toPoly inv))`:
`Φ (toBPoly (q.map (fun c => credR fuel R (cmul c inv)))) = C (φ (toPoly inv)) · Φ (toBPoly q)`. Per
coefficient `credR` drops (`map_toPoly_credR`) and `cmul` is `toPoly`-multiplicative; folding over the
Horner list factors the constant `φ (toPoly inv)` out. -/
theorem mapRingHom_toBPoly_map_credR_cmul {S : Type*} [CommRing S] (φ : ℚ[X] →+* S) (fuel : ℕ)
    (R inv : CPoly) (q : BPoly) (hR : cnorm R ≠ []) (hφR : φ (toPoly R) = 0) :
    (Polynomial.mapRingHom φ) (toBPoly (q.map (fun c => credR fuel R (cmul c inv))))
      = Polynomial.C (φ (toPoly inv)) * (Polynomial.mapRingHom φ) (toBPoly q) := by
  induction q with
  | nil => simp
  | cons a as ih =>
    rw [List.map_cons, toBPoly_cons, toBPoly_cons, map_add, map_add, map_mul, map_mul, ih, mul_add]
    congr 1
    · rw [Polynomial.coe_mapRingHom, Polynomial.map_C, Polynomial.map_C,
        map_toPoly_credR φ fuel R _ hR hφR, toPoly_cmul, map_mul, Polynomial.C_mul, mul_comm]
    · rw [Polynomial.coe_mapRingHom (f := φ), Polynomial.map_X]; ring

/-- **`bmonicXmodR` is a `Φ`-image unit-multiple** (the mod-`R` monic-normalization unit bridge): for any
ring hom `φ : ℚ[X] →+* S` killing `toPoly R`, with `Φ = Polynomial.mapRingHom φ`, when the leading-
`x`-coefficient's mod-`R` gcd reduces to a nonzero constant `C u` (`hg`/`hu` — Exercise 2.7 regularity), the
`Φ`-image of `bmonicXmodR fuel R p` is the **unit** `φ (toPoly (cinvMod fuel R (blc (bredR fuel R p))))`
times the `Φ`-image of `toBPoly p`:
`Φ (toBPoly (bmonicXmodR fuel R p)) = C (φ (toPoly inv)) · Φ (toBPoly p)`, and `φ (toPoly inv)` is a unit in
`S` (its inverse is `φ (toPoly (blc (bredR fuel R p)))`, by `map_toPoly_cinvMod_mul`). So `bmonicXmodR`
preserves similarity over the residue ring `S = ℚ[t]/(R)`: the monic-in-`x` normalization is multiplication
by a residue-ring unit. -/
theorem mapRingHom_toBPoly_bmonicXmodR {S : Type*} [CommRing S] (φ : ℚ[X] →+* S) (fuel : ℕ) (R : CPoly)
    (p : BPoly) (hR : cnorm R ≠ []) (hφR : φ (toPoly R) = 0) {u : ℚ} (hu : u ≠ 0)
    (hg : toPoly (cgcdExt fuel (blc (bredR fuel R p)) R).1 = Polynomial.C u)
    (hpz : ¬ bisZero (bredR fuel R p) = true) :
    (Polynomial.mapRingHom φ) (toBPoly (bmonicXmodR fuel R p))
        = Polynomial.C (φ (toPoly (cinvMod fuel R (blc (bredR fuel R p)))))
          * (Polynomial.mapRingHom φ) (toBPoly p)
      ∧ φ (toPoly (cinvMod fuel R (blc (bredR fuel R p))))
          * φ (toPoly (blc (bredR fuel R p))) = 1 := by
  refine ⟨?_, map_toPoly_cinvMod_mul φ fuel R (blc (bredR fuel R p)) hR hφR hu hg⟩
  rw [bmonicXmodR]
  simp only [hpz, Bool.false_eq_true, if_false]
  rw [toBPoly_bnorm,
    mapRingHom_toBPoly_map_credR_cmul φ fuel R (cinvMod fuel R (blc (bredR fuel R p)))
      (bredR fuel R p) hR hφR,
    mapRingHom_toBPoly_bredR φ fuel R p hR hφR]

/-! ### The full `lrtGcdCompute ↔ lrtSubresultant` agreement over the residue ring `ℚ[t]/(R)`
Chaining the `ℚ[t]`-similarity `lrtSubresultant ∼ lrtSubresultantCompute`
(`isSimilar_lrtSubresultant_lrtSubresultantCompute`) — pushed through the residue map `φ : ℚ[X] →+* S` —
with the `bmonicXmodR` unit bridge (`mapRingHom_toBPoly_bmonicXmodR`: `lrtGcdCompute`'s `Φ`-image is a
residue-ring unit times `lrtSubresultantCompute`'s) lands the headline: over the residue ring `S = ℚ[t]/(R)`,
the abstract `lrtSubresultant` is `IsSimilar` to the computable `lrtGcdCompute`. The push-through needs the
content witnesses to stay nonzero mod `R` (Ex 2.7 regularity), taken as `φ`-nonzero hypotheses. -/

/-- **`IsSimilar` pushes through a ring hom keeping the witnesses nonzero**: a `ℚ[t]`-similarity
`IsSimilar A B` whose witnesses `a, b` map to *nonzero* `φ a, φ b` in `S` gives a residue-ring similarity of
the `Φ`-images, `IsSimilar (Φ A) (Φ B)` (`Φ = Polynomial.mapRingHom φ`). The witnesses are `φ a, φ b`; the
defining equation maps over since `Φ ∘ C = C ∘ φ`. -/
theorem isSimilar_mapRingHom {S : Type*} [CommRing S] (φ : ℚ[X] →+* S) {A B : (ℚ[X])[X]}
    (h : IsSimilar A B) (hne : ∀ a b : ℚ[X], a ≠ 0 → b ≠ 0 → Polynomial.C a * A = Polynomial.C b * B
      → φ a ≠ 0 ∧ φ b ≠ 0) :
    IsSimilar ((Polynomial.mapRingHom φ) A) ((Polynomial.mapRingHom φ) B) := by
  obtain ⟨a, b, ha, hb, hab⟩ := h
  obtain ⟨hφa, hφb⟩ := hne a b ha hb hab
  refine ⟨φ a, φ b, hφa, hφb, ?_⟩
  have hcong := congrArg (Polynomial.map φ) hab
  rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C] at hcong
  simpa only [Polynomial.coe_mapRingHom] using hcong

/-- **A residue-ring unit multiple is `IsSimilar`**: if `Φ B = C η · Φ A` with `η` a unit in `S`
(`η · η' = 1`), then `IsSimilar (Φ A) (Φ B)` over `S` (witnesses `η` and `1`; `η ≠ 0` since it is a unit in
a — necessarily nontrivial — ring). The `bmonicXmodR` unit-multiple identity packaged as a similarity. -/
theorem isSimilar_of_unit_mul {S : Type*} [CommRing S] [Nontrivial S] {A B : S[X]} {η η' : S}
    (hη : η * η' = 1) (hAB : B = Polynomial.C η * A) :
    IsSimilar A B := by
  have hηne : η ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hη
    exact one_ne_zero hη.symm
  exact ⟨η, 1, hηne, one_ne_zero, by rw [hAB, map_one, one_mul]⟩

/-- **The full `lrtGcdCompute ↔ lrtSubresultant` agreement, over the residue ring `ℚ[t]/(R)`** (the
headline): for a residue map `φ : ℚ[X] →+* S` killing `toPoly R`, under the whole-chain LRT hypotheses
(as in `isSimilar_lrtSubresultant_lrtSubresultantCompute`), the `bmonicXmodR` regularity (the leading
`x`-coefficient's mod-`R` gcd reduces to a nonzero constant `C u`; the reduced primitive part is nonzero),
and the content witnesses staying `φ`-nonzero (Ex 2.7 regularity `hne`), the `Φ`-image of the abstract
`lrtSubresultant` is `IsSimilar` to the `Φ`-image of the computable `lrtGcdCompute` over `S = ℚ[t]/(R)`:
`IsSimilar (Φ (lrtSubresultant A D j)) (Φ (toBPoly (lrtGcdCompute fuel j R A D)))`. Chains
`isSimilar_lrtSubresultant_lrtSubresultantCompute` (mapped through `φ` by `isSimilar_mapRingHom`) with the
`bmonicXmodR` unit bridge `mapRingHom_toBPoly_bmonicXmodR` (packaged by `isSimilar_of_unit_mul`) via
`IsSimilar.trans`. This is the computable LRT log argument validated against the noncomputable subresultant,
up to a residue-ring unit — the closing step of the agreement. -/
theorem lrtGcdCompute_isSimilar_lrtSubresultant {S : Type*} [CommRing S] [IsDomain S] (φ : ℚ[X] →+* S)
    (fuel : ℕ) (R A D : CPoly) (G : ℕ → BPoly) (bt : ℕ → CPoly) (s : ℕ → BPoly) (c : ℕ → CPoly) (m : ℕ)
    (hRcn : cnorm R ≠ []) (hφR : φ (toPoly R) = 0)
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
        (bcontentX fuel (bsubresultantGcd fuel (toBPoly (G (m + 2))).natDegree (G 0) (G 1)))) = 0)
    (hne : ∀ a b : ℚ[X], a ≠ 0 → b ≠ 0 →
        Polynomial.C a * lrtSubresultant (toPoly A) (toPoly D) (toBPoly (G (m + 2))).natDegree
          = Polynomial.C b * toBPoly (lrtSubresultantCompute fuel (toBPoly (G (m + 2))).natDegree A D)
        → φ a ≠ 0 ∧ φ b ≠ 0)
    {u : ℚ} (hu : u ≠ 0)
    (hgu : toPoly (cgcdExt fuel
        (blc (bredR fuel R (lrtSubresultantCompute fuel (toBPoly (G (m + 2))).natDegree A D))) R).1
      = Polynomial.C u)
    (hpz : ¬ bisZero (bredR fuel R
        (lrtSubresultantCompute fuel (toBPoly (G (m + 2))).natDegree A D)) = true) :
    IsSimilar ((Polynomial.mapRingHom φ)
        (lrtSubresultant (toPoly A) (toPoly D) (toBPoly (G (m + 2))).natDegree))
      ((Polynomial.mapRingHom φ) (toBPoly
        (lrtGcdCompute fuel (toBPoly (G (m + 2))).natDegree R A D))) := by
  -- abstract ℚ[t]-similarity, mapped through φ to the residue ring
  have habs := isSimilar_lrtSubresultant_lrtSubresultantCompute fuel A D G bt s c m hG0 hG1 hd0 hd1
    hsc hβcn hdiv hG2 hc0 hβ0 hlc hcb hjlt hQ hCne hfilt hg hgcn hg0 hrem
  have hmap := isSimilar_mapRingHom φ habs hne
  -- the bmonicXmodR unit bridge: lrtGcdCompute = bmonicXmodR R lrtSubresultantCompute
  obtain ⟨hbridge, hunit⟩ := mapRingHom_toBPoly_bmonicXmodR φ fuel R
    (lrtSubresultantCompute fuel (toBPoly (G (m + 2))).natDegree A D) hRcn hφR hu hgu hpz
  have hsimUnit := isSimilar_of_unit_mul
    (A := (Polynomial.mapRingHom φ) (toBPoly
      (lrtSubresultantCompute fuel (toBPoly (G (m + 2))).natDegree A D)))
    (B := (Polynomial.mapRingHom φ) (toBPoly
      (lrtGcdCompute fuel (toBPoly (G (m + 2))).natDegree R A D)))
    hunit (by rw [lrtGcdCompute]; exact hbridge)
  exact hmap.trans hsimUnit

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
  **filter identity** `toBPoly (bsubresultantGcd …) = toBPoly (G (m+2))`, now **discharged structurally**
  by `toBPoly_bsubresultantGcd_eq_of_filter_singleton` (the singleton-filter list fact:
  `bsubresultantGcd`'s degree-`j` filter is `[G (m+2)]`, so its last element is `G (m+2)`), giving the
  `hfilt`-free `isSimilar_lrtSubresultant_bsubresultantGcd_real`;
- the content step `toBPoly_bprimitivePartX_exact` / its similarity packaging
  `isSimilar_toBPoly_bprimitivePartX`, chained into
  `isSimilar_lrtSubresultant_lrtSubresultantCompute` — `lrtSubresultant A D j ∼ lrtSubresultantCompute`;
- **the `bmonicXmodR` mod-`R` unit bridge** (`map_toPoly_credR`, `mapRingHom_toBPoly_bredR`,
  `map_toPoly_cinvMod_mul`, `mapRingHom_toBPoly_bmonicXmodR`): over any residue map `φ : ℚ[X] →+* S` killing
  `toPoly R`, the monic-in-`x` normalization `bmonicXmodR` is multiplication by a residue-ring **unit**
  (`cinvMod` is the mod-`R` inverse, by the `cgcdExt` Bézout identity); composed through
  `isSimilar_mapRingHom` + `IsSimilar.trans` this lands the **headline**
  `lrtGcdCompute_isSimilar_lrtSubresultant` — `Φ (lrtSubresultant A D j) ∼ Φ (toBPoly (lrtGcdCompute …))`
  over the residue ring `S = ℚ[t]/(R)`.

So the two isolated structural facts that closed the agreement are both landed: (1) the **degree-`j` filter
identity** (singleton filter ⟹ `bsubresultantGcd` is the chain element), and (2) the **`bmonicXmodR` mod-`R`
unit bridge** (monic normalization = residue-ring unit multiple). The remaining **data-instantiation** for
the **real** `subresPRS` is **also now done** (see the `goState` section below): the internal
`let rec subresPRS.go` is mirrored by the top-level state machine `goState`, whose chain element
`chainG`, β-divisor `chainBt`, and `Classical.choose` pseudo-division witnesses `chainS`/`chainC`
discharge the abstract `G`/`bt`/`s`/`c`; `hsc` is `chain_hsc` (the `toBPoly_bpsremainder` spec), `hG2` is
`chain_hG2` (definitional via `goState_fst_add_two`), `hG0`/`hG1` are `chainG_zero`/`chainG_one`, and the
singleton-filter `hfilt` is `chain_hfilt` (`subresPRS_eq_range` + `filter_range_unique` +
`unique_of_strictAnti` — the strict-`bdeg`-decrease uniqueness, no `let rec` induction needed thanks to
`go.eq_2`). The fully-instantiated `lrtGcdCompute_isSimilar_lrtSubresultant_concrete` quantifies over **no**
abstract chain: only the genuine *mathematics-grade* regularity remains as hypotheses — Collins
β-divisibility (`hdiv`), the chain nonzero/degree side-conditions, the `bprimitivePartX` content-exactness
(`bcontentX` divides each coefficient), and the Exercise 2.7 residue-ring regularity (`φ` killing
`toPoly R`, the leading coeff a unit mod `R`, witnesses `φ`-nonzero). No recurrence-matching or
list/`let rec` plumbing is left. -/

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

-- Restatement: FACT 1 — the degree-`j` filter identity. A singleton degree-`j` filter of `subresPRS`
-- makes `bsubresultantGcd` read as that single chain element `G (m+2)` (under `toBPoly`).
example (fuel : ℕ) (P Q : BPoly) (G : ℕ → BPoly) (m : ℕ)
    (hfil : (subresPRS fuel P Q).filter
        (fun R => decide (bdeg R = (toBPoly (G (m + 2))).natDegree ∧ ¬ bisZero R)) = [G (m + 2)]) :
    toBPoly (bsubresultantGcd fuel (toBPoly (G (m + 2))).natDegree P Q) = toBPoly (G (m + 2)) :=
  toBPoly_bsubresultantGcd_eq_of_filter_singleton fuel P Q G m hfil

-- Restatement: FACT 2 — the `bmonicXmodR` mod-`R` unit bridge. Over any `φ : ℚ[X] →+* S` killing
-- `toPoly R`, `bmonicXmodR`'s `Φ`-image is a residue-ring UNIT (`η · η' = 1`) times `toBPoly p`'s.
example {S : Type*} [CommRing S] (φ : ℚ[X] →+* S) (fuel : ℕ) (R : CPoly) (p : BPoly)
    (hR : cnorm R ≠ []) (hφR : φ (toPoly R) = 0) {u : ℚ} (hu : u ≠ 0)
    (hg : toPoly (cgcdExt fuel (blc (bredR fuel R p)) R).1 = Polynomial.C u)
    (hpz : ¬ bisZero (bredR fuel R p) = true) :
    (Polynomial.mapRingHom φ) (toBPoly (bmonicXmodR fuel R p))
        = Polynomial.C (φ (toPoly (cinvMod fuel R (blc (bredR fuel R p)))))
          * (Polynomial.mapRingHom φ) (toBPoly p)
      ∧ φ (toPoly (cinvMod fuel R (blc (bredR fuel R p))))
          * φ (toPoly (blc (bredR fuel R p))) = 1 :=
  mapRingHom_toBPoly_bmonicXmodR φ fuel R p hR hφR hu hg hpz

/-! ### Instantiating the abstract chain from the concrete `subresPRS.go` (data plumbing)
The headline `lrtGcdCompute_isSimilar_lrtSubresultant` quantifies over an abstract chain `G : ℕ → BPoly`
with per-step witnesses `bt`/`s`/`c` and side-conditions. To instantiate it from the **real**
`subresPRS fuel P Q`, we mirror the internal `let rec subresPRS.go` as a top-level **state machine**
`goState`: its state `(Ri₋₁, Ri, ψ, δ)` carries everything one `go`-step needs, and one application of
`goStep` reproduces the `go` recurrence (`Riₙ₊₁ = bdivC fuel (prem Ri₋₁ Ri) βᵢ`, `βᵢ = goBeta …`). The
chain element `G i := (goState … i).1` and the β-divisor `bt i := goBeta …` are then *computable*
projections of the state, and the divided-step recurrence `hG2` holds **definitionally** — no list
reasoning. The `go`-list bridge (`go_state_getD`) connects this state machine back to the literal
`subresPRS` list for the singleton-filter fact `hfil`. -/

/-- **ψ-accumulator update of one `subresPRS.go` step**: `ψ' = (−lc Ri₋₁)^δ / ψ^(δ−1)` (`ψ' = ψ` when
`δ = 0`), the exact-over-`ℚ[t]` subresultant ψ recurrence carried by `go`. -/
def goPsi' (fuel : ℕ) (Ri_1 : BPoly) (psi : CPoly) (dp : ℕ) : CPoly :=
  if dp = 0 then psi else cdiv fuel (cpowP (cneg (blc Ri_1)) dp) (cpowP psi (dp - 1))

/-- **β-divisor of one `subresPRS.go` step**: `β = −lc(Ri₋₁) · ψ'^δ` (`ψ'` from `goPsi'`), the exact
`ℚ[t]`-divisor stripping the pseudo-remainder `lc`-power inflation in the subresultant PRS. -/
def goBeta (fuel : ℕ) (Ri_1 : BPoly) (psi : CPoly) (dp : ℕ) : CPoly :=
  cmul (cneg (blc Ri_1)) (cpowP (goPsi' fuel Ri_1 psi dp) dp)

/-- **One `subresPRS.go` step on the state** `(Ri₋₁, Ri, ψ, δ) ↦ (Ri, Ri₊₁, ψ', δ')` with
`Ri₊₁ = bdivC fuel (prem Ri₋₁ Ri) β`, `ψ' = goPsi'`, `β = goBeta`, `δ' = bdeg Ri − bdeg Ri₊₁` —
the top-level mirror of the internal `let rec subresPRS.go` recurrence. -/
def goStep (fuel : ℕ) : BPoly × BPoly × CPoly × ℕ → BPoly × BPoly × CPoly × ℕ
  | (Ri_1, Ri, psi, dp) =>
    let psi' := goPsi' fuel Ri_1 psi dp
    let beta := goBeta fuel Ri_1 psi dp
    let Ri1 := bdivC fuel (bpsremainder fuel Ri_1 Ri) beta
    (Ri, Ri1, psi', bdeg Ri - bdeg Ri1)

/-- **The `subresPRS.go` state at index `i`** `goState fuel s₀ i = goStepⁱ s₀`: the `go`-recurrence state
after `i` steps from the initial state `s₀ = (P, Q, [-1], bdeg P − bdeg Q)`. The chain element is the
first component, the next chain element the second. -/
def goState (fuel : ℕ) (s0 : BPoly × BPoly × CPoly × ℕ) : ℕ → BPoly × BPoly × CPoly × ℕ
  | 0 => s0
  | i + 1 => goStep fuel (goState fuel s0 i)

/-- **`goState` commutes with one step**: `goState fuel (goStep fuel s₀) k = goState fuel s₀ (k+1)`. -/
theorem goState_goStep (fuel : ℕ) (s0 : BPoly × BPoly × CPoly × ℕ) (k : ℕ) :
    goState fuel (goStep fuel s0) k = goState fuel s0 (k + 1) := by
  induction k generalizing s0 with
  | zero => rfl
  | succ n ih => rw [goState, goState, ih]

/-- **The next chain element is the second state component**: `(goState fuel s₀ (l+1)).1 =
(goState fuel s₀ l).2.1` — `go` shifts the pair `(Ri₋₁, Ri)` to `(Ri, Ri₊₁)`, so element `l+1` is the
second slot of state `l`. -/
theorem goState_succ_fst (fuel : ℕ) (s0 : BPoly × BPoly × CPoly × ℕ) (l : ℕ) :
    (goState fuel s0 (l + 1)).1 = (goState fuel s0 l).2.1 := by
  show (goStep fuel (goState fuel s0 l)).1 = _
  rw [goStep]

/-- **The divided-PRS recurrence `hG2` holds definitionally for `goState`**: with `G i := (goState fuel s₀
i).1` and the β-divisor `bt l := goBeta fuel (G l) ψₗ δₗ` (the ψ/δ of state `l`), the chain element
`G (l+2)` is exactly `bdivC fuel (bpsremainder fuel (G l) (G (l+1))) (bt l)` — the literal `subresPRS`
divided-step recurrence, by definition of `goStep`. This discharges `hG2` for the concrete chain with no
list reasoning. -/
theorem goState_fst_add_two (fuel : ℕ) (s0 : BPoly × BPoly × CPoly × ℕ) (l : ℕ) :
    (goState fuel s0 (l + 2)).1
      = bdivC fuel (bpsremainder fuel (goState fuel s0 l).1 (goState fuel s0 (l + 1)).1)
          (goBeta fuel (goState fuel s0 l).1 (goState fuel s0 l).2.2.1 (goState fuel s0 l).2.2.2) := by
  rw [goState_succ_fst fuel s0 (l + 1)]
  show (goStep fuel (goState fuel s0 l)).2.1 = _
  rw [goStep]
  rw [goState_succ_fst fuel s0 l]

/-! #### The `go`-list ↔ `goState` bridge (reading `subresPRS` off the state machine)
The `goState` machine carries the chain data; to identify `subresPRS`'s *list* elements with the state
machine (for the singleton-filter `hfil`), these lemmas read the `go` list — and then `subresPRS` —
through `goState`, valid while the chain stays nonzero and fuel suffices. -/

/-- **One `subresPRS.go` step against `goState`**: while `Ri` (the current element `s.2.1`) is nonzero,
`go fuel (fo+1) …` emits `Ri` then recurses on the `goStep`-advanced state — the literal `go` recurrence
re-expressed through the top-level `goStep`. -/
theorem go_step_state (fuel fo : ℕ) (s : BPoly × BPoly × CPoly × ℕ) (hz : ¬ bisZero s.2.1 = true) :
    subresPRS.go fuel (fo + 1) s.1 s.2.1 s.2.2.1 s.2.2.2
      = s.2.1 :: subresPRS.go fuel fo (goStep fuel s).1 (goStep fuel s).2.1
          (goStep fuel s).2.2.1 (goStep fuel s).2.2.2 := by
  obtain ⟨Ri_1, Ri, psi, dp⟩ := s
  rw [subresPRS.go.eq_2]
  simp only at hz
  simp only [hz, Bool.false_eq_true, if_false]
  rfl

/-- **`go`-list index reads the state machine**: as long as the chain elements stay nonzero through index
`k` and the fuel `fo` exceeds `k`, the `k`-th element of `go fuel fo …` is the second state component
`(goState fuel s k).2.1`. Induction on `k`, peeling one `go_step_state` and shifting `goState` by
`goState_goStep`. -/
theorem go_getD (fuel : ℕ) (s : BPoly × BPoly × CPoly × ℕ) (k fo : ℕ) (hfo : k < fo)
    (hnz : ∀ i ≤ k, ¬ bisZero (goState fuel s i).2.1 = true) :
    (subresPRS.go fuel fo s.1 s.2.1 s.2.2.1 s.2.2.2).getD k [] = (goState fuel s k).2.1 := by
  induction k generalizing s fo with
  | zero =>
    obtain ⟨f', rfl⟩ : ∃ f', fo = f' + 1 := ⟨fo - 1, by omega⟩
    rw [go_step_state fuel f' s (hnz 0 (by omega))]
    rfl
  | succ n ih =>
    obtain ⟨f', rfl⟩ : ∃ f', fo = f' + 1 := ⟨fo - 1, by omega⟩
    rw [go_step_state fuel f' s (hnz 0 (by omega)), List.getD_cons_succ,
      ih (goStep fuel s) f' (by omega)
        (fun i hi => by rw [goState_goStep]; exact hnz (i + 1) (by omega)),
      goState_goStep]

/-- **`subresPRS` index reads the chain element `G i := (goState fuel s₀ i).1`**: with the initial state
`s₀ = (P, Q, [-1], bdeg P − bdeg Q)`, the `i`-th element of `subresPRS fuel P Q` is `(goState fuel s₀ i).1`
— provided the chain stays nonzero through index `i−1` and `i ≤ fuel`. So `subresPRS`'s list is literally
the `goState` chain, the identification that lets the singleton-filter fact be stated on the state machine.
-/
theorem subresPRS_getD (fuel : ℕ) (P Q : BPoly) (i : ℕ) (hfo : i ≤ fuel)
    (hnz : ∀ k < i, ¬ bisZero (goState fuel (P, Q, [-1], bdeg P - bdeg Q) k).2.1 = true) :
    (subresPRS fuel P Q).getD i [] = (goState fuel (P, Q, [-1], bdeg P - bdeg Q) i).1 := by
  rw [subresPRS.eq_def]
  cases i with
  | zero => rfl
  | succ n =>
    rw [List.getD_cons_succ]
    have h := go_getD fuel (P, Q, [-1], bdeg P - bdeg Q) n fuel (by omega)
      (fun k hk => hnz k (by omega))
    simp only at h
    rw [h, goState_succ_fst]

/-- **`go` stops at a zero element**: if the current element `s.2.1` is zero, `go fuel fo …` is `[]` (the
nonzero-prefix recursion terminates). -/
theorem go_zero (fuel fo : ℕ) (s : BPoly × BPoly × CPoly × ℕ) (hz : bisZero s.2.1 = true) :
    subresPRS.go fuel fo s.1 s.2.1 s.2.2.1 s.2.2.2 = [] := by
  cases fo with
  | zero => rw [subresPRS.go.eq_1]
  | succ f' =>
    obtain ⟨Ri_1, Ri, psi, dp⟩ := s
    rw [subresPRS.go.eq_2]
    simp only at hz
    simp only [hz, if_true]

/-- **Full `go` list as a `range`-map**: when the chain elements stay nonzero through index `k` and the
next is zero (and fuel suffices), `go fuel fo …` is *exactly* `[s.2.1, …, (goState fuel s k).2.1]` =
`(List.range (k+1)).map (fun i => (goState fuel s i).2.1)`. Induction peeling one `go_step_state`,
`go_zero` at the terminal step. -/
theorem go_eq_range (fuel : ℕ) (s : BPoly × BPoly × CPoly × ℕ) (k fo : ℕ) (hfo : k + 1 < fo)
    (hnz : ∀ i ≤ k, ¬ bisZero (goState fuel s i).2.1 = true)
    (hz : bisZero (goState fuel s (k + 1)).2.1 = true) :
    subresPRS.go fuel fo s.1 s.2.1 s.2.2.1 s.2.2.2
      = (List.range (k + 1)).map (fun i => (goState fuel s i).2.1) := by
  induction k generalizing s fo with
  | zero =>
    obtain ⟨f', rfl⟩ : ∃ f', fo = f' + 1 := ⟨fo - 1, by omega⟩
    rw [go_step_state fuel f' s (hnz 0 (by omega)),
      go_zero fuel f' (goStep fuel s) hz]
    rfl
  | succ n ih =>
    obtain ⟨f', rfl⟩ : ∃ f', fo = f' + 1 := ⟨fo - 1, by omega⟩
    rw [go_step_state fuel f' s (hnz 0 (by omega)),
      ih (goStep fuel s) f' (by omega)
        (fun i hi => by rw [goState_goStep]; exact hnz (i + 1) (by omega))
        (by rw [goState_goStep]; exact hz)]
    conv_rhs => rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply]
    rw [goState_goStep]

/-- **Filter of `List.range n` with a unique satisfier is a singleton**: if `q N = true`, `N < n`, and
`N` is the *only* index below `n` with `q i = true`, then `(List.range n).filter q = [N]`. (`range` is
nodup, so the filtered list is nodup with every element `= N`, hence `[N]`.) -/
theorem filter_range_unique {n N : ℕ} (q : ℕ → Bool) (hN : N < n) (hqN : q N = true)
    (huniq : ∀ i, i < n → q i = true → i = N) :
    (List.range n).filter q = [N] := by
  have hnodup : (List.range n).Nodup := List.nodup_range
  have hfnodup : ((List.range n).filter q).Nodup := hnodup.filter q
  have hmem : N ∈ (List.range n).filter q := by
    rw [List.mem_filter, List.mem_range]; exact ⟨hN, hqN⟩
  have hall : ∀ x ∈ (List.range n).filter q, x = N := by
    intro x hx
    rw [List.mem_filter, List.mem_range] at hx
    exact huniq x hx.1 hx.2
  cases hl : (List.range n).filter q with
  | nil => rw [hl] at hmem; simp at hmem
  | cons a as =>
    rw [hl] at hall hmem hfnodup
    have ha : a = N := hall a (by simp)
    have has : as = [] := by
      cases as with
      | nil => rfl
      | cons b bs =>
        exfalso
        have hb : b = N := hall b (by simp)
        rw [ha, hb] at hfnodup
        simp at hfnodup
    rw [ha, has]

/-- **Full `subresPRS` list as a `range`-map of the chain `G i := (goState fuel s₀ i).1`**: with
`s₀ = (P, Q, [-1], bdeg P − bdeg Q)`, when the chain elements `G 0, …, G N` are all nonzero, `G (N+1)`
is zero, and `N+1 < fuel`, the list `subresPRS fuel P Q` is exactly `[G 0, …, G N] =
(List.range (N+1)).map G`. Prepends `G 0 = P` to `go_eq_range` (the `go` list is the chain from `G 1`),
shifting `(goState …).2.1` to `(goState … (·+1)).1` via `goState_succ_fst`. -/
theorem subresPRS_eq_range (fuel : ℕ) (P Q : BPoly) (N : ℕ) (hfo : N + 1 < fuel)
    (hnz : ∀ i ≤ N, ¬ bisZero (goState fuel (P, Q, [-1], bdeg P - bdeg Q) i).1 = true)
    (hzN : bisZero (goState fuel (P, Q, [-1], bdeg P - bdeg Q) (N + 1)).1 = true) :
    subresPRS fuel P Q
      = (List.range (N + 1)).map (fun i => (goState fuel (P, Q, [-1], bdeg P - bdeg Q) i).1) := by
  set s0 : BPoly × BPoly × CPoly × ℕ := (P, Q, [-1], bdeg P - bdeg Q) with hs0
  rw [subresPRS.eq_def]
  cases N with
  | zero =>
    have hQz : bisZero s0.2.1 = true := by
      have := hzN; rw [goState_succ_fst] at this; exact this
    rw [go_zero fuel fuel s0 hQz]
    show [P] = [(goState fuel s0 0).1]
    rfl
  | succ n =>
    rw [go_eq_range fuel s0 n fuel (by omega)
      (fun i hi => by rw [← goState_succ_fst]; exact hnz (i + 1) (by omega))
      (by rw [← goState_succ_fst]; exact hzN)]
    conv_rhs => rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    refine congrArg (P :: ·) (List.map_congr_left ?_)
    intro i _
    simp only [Function.comp_apply, goState_succ_fst]

/-- **Strict degree decrease ⟹ unique degree-`N` index**: if `f (i+1) < f i` for all `i < N`, then `N`
is the *only* index `i ≤ N` with `f i = f N`. The arithmetic core of the singleton-filter uniqueness:
strict decrease of the `bdeg` chain makes the degree-`N` element unique. -/
theorem unique_of_strictAnti (f : ℕ → ℕ) (N : ℕ) (hstrict : ∀ i < N, f (i + 1) < f i) :
    ∀ i ≤ N, f i = f N → i = N := by
  have mono : ∀ j ≤ N, ∀ i < j, f j < f i := by
    intro j hj
    induction j with
    | zero => intro i hi; omega
    | succ n ih =>
      intro i hi
      have hstep : f (n + 1) < f n := hstrict n (by omega)
      rcases Nat.lt_or_ge i n with hlt | hge
      · have := ih (by omega) i hlt; omega
      · have : i = n := by omega
        subst this; omega
  intro i hi heq
  by_contra hne
  have hiN : i < N := lt_of_le_of_ne hi hne
  have := mono N (le_refl N) i hiN
  omega

/-- **The degree-`N` filter of `subresPRS` is the singleton `[G N]`** (the structural `hfil`, discharged):
with `s₀ = (P, Q, [-1], bdeg P − bdeg Q)` and the chain `G i := (goState fuel s₀ i).1`, when the elements
`G 0, …, G N` are nonzero (`hnz`), `G (N+1)` is zero (`hzN`), the `bdeg` chain strictly decreases
(`hstrict`), and `N+1 < fuel`, the degree-`bdeg (G N)` nonzero filter of `subresPRS fuel P Q` is exactly
`[G N]`. The full-list `subresPRS_eq_range` pushed through `List.filter_map` and `filter_range_unique`
(uniqueness via `unique_of_strictAnti`). -/
theorem subresPRS_filter_singleton (fuel : ℕ) (P Q : BPoly) (N : ℕ) (hfo : N + 1 < fuel)
    (hnz : ∀ i ≤ N, ¬ bisZero (goState fuel (P, Q, [-1], bdeg P - bdeg Q) i).1 = true)
    (hzN : bisZero (goState fuel (P, Q, [-1], bdeg P - bdeg Q) (N + 1)).1 = true)
    (hstrict : ∀ i < N, bdeg (goState fuel (P, Q, [-1], bdeg P - bdeg Q) (i + 1)).1
        < bdeg (goState fuel (P, Q, [-1], bdeg P - bdeg Q) i).1) :
    (subresPRS fuel P Q).filter
        (fun R => decide (bdeg R = bdeg (goState fuel (P, Q, [-1], bdeg P - bdeg Q) N).1
          ∧ ¬ bisZero R))
      = [(goState fuel (P, Q, [-1], bdeg P - bdeg Q) N).1] := by
  set s0 : BPoly × BPoly × CPoly × ℕ := (P, Q, [-1], bdeg P - bdeg Q) with hs0
  set G := fun i => (goState fuel s0 i).1 with hG
  rw [subresPRS_eq_range fuel P Q N hfo hnz hzN, List.filter_map]
  have hfilt : (List.range (N + 1)).filter
      ((fun R => decide (bdeg R = bdeg (G N) ∧ ¬ bisZero R)) ∘ G) = [N] := by
    apply filter_range_unique
    · omega
    · simp only [Function.comp_apply, decide_eq_true_eq, true_and]
      exact hnz N (le_refl N)
    · intro i hi hqi
      simp only [Function.comp_apply, decide_eq_true_eq] at hqi
      exact unique_of_strictAnti (fun i => bdeg (G i)) N hstrict i (by omega) hqi.1
  rw [hfilt, List.map_singleton]

/-! #### Concrete chain data from `subresPRS` (discharging `G`/`bt`/`s`/`c`, `hsc`, `hG2`, `hfilt`)
The chain element `chainG`, β-divisor `chainBt`, and pseudo-division witnesses `chainS`/`chainC` are now
*defined* (computable projections of `goState`, and `Classical.choose` of `toBPoly_bpsremainder` for the
existential quotient/content). The per-step pseudo-division identity `hsc` and divided recurrence `hG2`
hold for them automatically; combined with `subresPRS_filter_singleton` this discharges `hfilt`. -/

/-- **The concrete `subresPRS` chain element** `chainG fuel P Q i := (goState fuel (P,Q,[-1],…) i).1` —
the `i`-th element of `subresPRS fuel P Q`, as a function `ℕ → BPoly`. -/
noncomputable def chainG (fuel : ℕ) (P Q : BPoly) (i : ℕ) : BPoly :=
  (goState fuel (P, Q, [-1], bdeg P - bdeg Q) i).1

/-- **The concrete `subresPRS` β-divisor** `chainBt fuel P Q l := goBeta …` at the `l`-th state — the
exact `ℚ[t]`-divisor `βₗ` of the `subresPRS` divided step `Rₗ₊₂ = prem(Rₗ,Rₗ₊₁)/βₗ`. -/
noncomputable def chainBt (fuel : ℕ) (P Q : BPoly) (l : ℕ) : CPoly :=
  goBeta fuel (goState fuel (P, Q, [-1], bdeg P - bdeg Q) l).1
    (goState fuel (P, Q, [-1], bdeg P - bdeg Q) l).2.2.1
    (goState fuel (P, Q, [-1], bdeg P - bdeg Q) l).2.2.2

/-- **The concrete pseudo-division quotient** `chainS fuel P Q l`: the `Classical.choose` quotient of the
pseudo-division identity `toBPoly_bpsremainder` for the chain pair `(chainG l, chainG (l+1))`. -/
noncomputable def chainS (fuel : ℕ) (P Q : BPoly) (l : ℕ) : BPoly :=
  (toBPoly_bpsremainder fuel (chainG fuel P Q l) (chainG fuel P Q (l + 1))).choose

/-- **The concrete pseudo-division content** `chainC fuel P Q l`: the `Classical.choose` content `c ∈ ℚ[t]`
of the pseudo-division identity for the chain pair `(chainG l, chainG (l+1))`. -/
noncomputable def chainC (fuel : ℕ) (P Q : BPoly) (l : ℕ) : CPoly :=
  (toBPoly_bpsremainder fuel (chainG fuel P Q l) (chainG fuel P Q (l + 1))).choose_spec.choose

/-- **`chainG 0 = P`**: the chain's first element is the first `subresPRS` argument. -/
@[simp] theorem chainG_zero (fuel : ℕ) (P Q : BPoly) : chainG fuel P Q 0 = P := rfl

/-- **`chainG 1 = Q`**: the chain's second element is the second `subresPRS` argument. -/
@[simp] theorem chainG_one (fuel : ℕ) (P Q : BPoly) : chainG fuel P Q 1 = Q := by
  rw [chainG, goState_succ_fst]; rfl

/-- **`hsc` for the concrete chain**: the pseudo-division identity holds for `chainS`/`chainC` by the very
`Classical.choose` spec of `toBPoly_bpsremainder`. -/
theorem chain_hsc (fuel : ℕ) (P Q : BPoly) (l : ℕ) :
    Polynomial.C (toPoly (chainC fuel P Q l)) * toBPoly (chainG fuel P Q l)
      = toBPoly (chainS fuel P Q l) * toBPoly (chainG fuel P Q (l + 1))
        + toBPoly (bpsremainder fuel (chainG fuel P Q l) (chainG fuel P Q (l + 1))) :=
  (toBPoly_bpsremainder fuel (chainG fuel P Q l) (chainG fuel P Q (l + 1))).choose_spec.choose_spec

/-- **`hG2` for the concrete chain**: the divided-PRS recurrence `chainG (l+2) =
bdivC fuel (prem (chainG l) (chainG (l+1))) (chainBt l)` holds definitionally via `goState_fst_add_two`. -/
theorem chain_hG2 (fuel : ℕ) (P Q : BPoly) (l : ℕ) :
    chainG fuel P Q (l + 2)
      = bdivC fuel (bpsremainder fuel (chainG fuel P Q l) (chainG fuel P Q (l + 1)))
          (chainBt fuel P Q l) := by
  rw [chainG, goState_fst_add_two, chainBt]
  rfl

/-- **`hfilt` for the concrete chain**: the degree-`(toBPoly (chainG (m+2))).natDegree` filter of
`subresPRS fuel P Q` returns the chain element `chainG (m+2)` (under `toBPoly`). Combines the singleton
filter `subresPRS_filter_singleton` (rewriting `bdeg = natDegree` via `bdeg_eq_natDegree`) with
`toBPoly_bsubresultantGcd_eq_of_filter_singleton`. -/
theorem chain_hfilt (fuel : ℕ) (P Q : BPoly) (m : ℕ) (hfo : m + 2 + 1 < fuel)
    (hnz : ∀ i ≤ m + 2, ¬ bisZero (chainG fuel P Q i) = true)
    (hzN : bisZero (chainG fuel P Q (m + 2 + 1)) = true)
    (hstrict : ∀ i < m + 2, bdeg (chainG fuel P Q (i + 1)) < bdeg (chainG fuel P Q i)) :
    toBPoly (bsubresultantGcd fuel (toBPoly (chainG fuel P Q (m + 2))).natDegree P Q)
      = toBPoly (chainG fuel P Q (m + 2)) := by
  have hfil := subresPRS_filter_singleton fuel P Q (m + 2) hfo hnz hzN hstrict
  rw [bdeg_eq_natDegree] at hfil
  exact toBPoly_bsubresultantGcd_eq_of_filter_singleton fuel P Q (chainG fuel P Q) m hfil

/-! ### The clean concrete agreement: `lrtGcdCompute ↔ lrtSubresultant` for the real `subresPRS`
Instantiating the headline `lrtGcdCompute_isSimilar_lrtSubresultant` with the **concrete** chain data
(`chainG`/`chainBt`/`chainS`/`chainC` from `subresPRS`) discharges the abstract chain `G`/`bt`/`s`/`c`,
the per-step identity `hsc` (`chain_hsc`), the divided recurrence `hG2` (`chain_hG2`), the endpoints
`hG0`/`hG1` (`chainG_zero`/`chainG_one`), and the singleton-filter `hfilt` (`chain_hfilt`). What remains
are exactly the genuine regularity inputs the task isolates: Collins β-divisibility (`hdiv`), the chain
nonzero/degree side-conditions (`hβcn`/`hc0`/`hβ0`/`hlc`/`hcb`/`hjlt`/`hQ` and the filter's
`hnzF`/`hzNF`/`hstrictF`), the `bprimitivePartX` content-exactness, and the residue-ring regularity of
Exercise 2.7 (`φ` killing `toPoly R`, leading coeff a unit mod `R`, witnesses `φ`-nonzero). No abstract
chain is quantified over: `P = liftCtoBPoly D`, `Q = bArgAmtD' A D` and the chain is `subresPRS`'s own. -/

/-- **The clean concrete `lrtGcdCompute ↔ lrtSubresultant` agreement** (the LAST step, fully
data-instantiated): for the **real** `subresPRS fuel (liftCtoBPoly D) (bArgAmtD' A D)` chain
`chainG`/`chainBt`/`chainS`/`chainC`, with `j := (toBPoly (chainG (m+2))).natDegree` the regular index,
and a residue map `φ : ℚ[X] →+* S` killing `toPoly R` — under the genuine regularity inputs (Collins
β-divisibility `hdiv`; the chain nonzero/degree side-conditions; the `bprimitivePartX` content exactness;
and the Exercise 2.7 residue-ring regularity) — the `Φ`-image of the abstract `lrtSubresultant` is
`IsSimilar` to the `Φ`-image of the computable `lrtGcdCompute` over `S = ℚ[t]/(R)`. This is the headline
`lrtGcdCompute_isSimilar_lrtSubresultant` with the abstract chain `G`/`bt`/`s`/`c` and the structural
hypotheses `hG0`/`hG1`/`hsc`/`hG2`/`hfilt` *discharged from `subresPRS`* — only the mathematics-grade
regularity (no list/recurrence plumbing) is left as hypotheses. -/
theorem lrtGcdCompute_isSimilar_lrtSubresultant_concrete {S : Type*} [CommRing S] [IsDomain S]
    (φ : ℚ[X] →+* S) (fuel : ℕ) (R A D : CPoly) (m : ℕ)
    (hRcn : cnorm R ≠ []) (hφR : φ (toPoly R) = 0)
    (hd0 : (toBPoly (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) 0)).natDegree
      = (toPoly D).natDegree)
    (hd1 : (toBPoly (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) 1)).natDegree
      = (toPoly D).natDegree - 1)
    -- singleton-filter inputs (chain nonzero through m+2, zero after, strict bdeg decrease, fuel)
    (hfoF : m + 2 + 1 < fuel)
    (hnzF : ∀ i ≤ m + 2, ¬ bisZero (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) i) = true)
    (hzNF : bisZero (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) (m + 2 + 1)) = true)
    (hstrictF : ∀ i < m + 2,
      bdeg (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) (i + 1))
        < bdeg (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) i))
    -- Collins β-divisibility + chain degree/nonzero regularity
    (hβcn : ∀ l ≤ m, cnorm (chainBt fuel (liftCtoBPoly D) (bArgAmtD' A D) l) ≠ [])
    (hdiv : ∀ l ≤ m, ∀ a ∈ bpsremainder fuel (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) l)
        (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) (l + 1)),
      toPoly (cmod fuel a (chainBt fuel (liftCtoBPoly D) (bArgAmtD' A D) l)) = 0)
    (hc0 : ∀ l ≤ m, toPoly (chainC fuel (liftCtoBPoly D) (bArgAmtD' A D) l) ≠ 0)
    (hβ0 : ∀ l ≤ m, toPoly (chainBt fuel (liftCtoBPoly D) (bArgAmtD' A D) l) ≠ 0)
    (hlc : ∀ l ≤ m, (toBPoly (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) (l + 1))).coeff
      (toBPoly (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) (l + 1))).natDegree ≠ 0)
    (hcb : ∀ l ≤ m, (toBPoly (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) (l + 2))).natDegree
      < (toBPoly (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) (l + 1))).natDegree)
    (hjlt : ∀ l < m, (toBPoly (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) (m + 2))).natDegree
      < (toBPoly (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) (l + 2))).natDegree)
    (hQ : ∀ l ≤ m, (toBPoly (chainS fuel (liftCtoBPoly D) (bArgAmtD' A D) l)).natDegree
        + (toBPoly (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) (l + 1))).natDegree
      ≤ (toBPoly (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) l)).natDegree)
    (hCne : toBPoly (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) (m + 2)) ≠ 0)
    -- bprimitivePartX content-exactness on the degree-j element
    (hg : ¬ cisZero (bcontentX fuel
        (bsubresultantGcd fuel
          (toBPoly (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) (m + 2))).natDegree
          (liftCtoBPoly D) (bArgAmtD' A D))) = true)
    (hgcn : cnorm (bcontentX fuel
        (bsubresultantGcd fuel
          (toBPoly (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) (m + 2))).natDegree
          (liftCtoBPoly D) (bArgAmtD' A D))) ≠ [])
    (hg0 : toPoly (bcontentX fuel
        (bsubresultantGcd fuel
          (toBPoly (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) (m + 2))).natDegree
          (liftCtoBPoly D) (bArgAmtD' A D))) ≠ 0)
    (hrem : ∀ a ∈ bnorm (bsubresultantGcd fuel
        (toBPoly (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) (m + 2))).natDegree
        (liftCtoBPoly D) (bArgAmtD' A D)),
      toPoly (cmod fuel a (bcontentX fuel
        (bsubresultantGcd fuel
          (toBPoly (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) (m + 2))).natDegree
          (liftCtoBPoly D) (bArgAmtD' A D)))) = 0)
    (hne : ∀ a b : ℚ[X], a ≠ 0 → b ≠ 0 →
        Polynomial.C a * lrtSubresultant (toPoly A) (toPoly D)
            (toBPoly (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) (m + 2))).natDegree
          = Polynomial.C b * toBPoly (lrtSubresultantCompute fuel
            (toBPoly (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) (m + 2))).natDegree A D)
        → φ a ≠ 0 ∧ φ b ≠ 0)
    {u : ℚ} (hu : u ≠ 0)
    (hgu : toPoly (cgcdExt fuel
        (blc (bredR fuel R (lrtSubresultantCompute fuel
          (toBPoly (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) (m + 2))).natDegree A D))) R).1
      = Polynomial.C u)
    (hpz : ¬ bisZero (bredR fuel R
        (lrtSubresultantCompute fuel
          (toBPoly (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) (m + 2))).natDegree A D)) = true) :
    IsSimilar ((Polynomial.mapRingHom φ)
        (lrtSubresultant (toPoly A) (toPoly D)
          (toBPoly (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) (m + 2))).natDegree))
      ((Polynomial.mapRingHom φ) (toBPoly
        (lrtGcdCompute fuel
          (toBPoly (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) (m + 2))).natDegree R A D))) := by
  have hfilt := chain_hfilt fuel (liftCtoBPoly D) (bArgAmtD' A D) m hfoF hnzF hzNF hstrictF
  exact lrtGcdCompute_isSimilar_lrtSubresultant φ fuel R A D
    (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D))
    (chainBt fuel (liftCtoBPoly D) (bArgAmtD' A D))
    (chainS fuel (liftCtoBPoly D) (bArgAmtD' A D))
    (chainC fuel (liftCtoBPoly D) (bArgAmtD' A D)) m
    hRcn hφR (chainG_zero fuel (liftCtoBPoly D) (bArgAmtD' A D))
    (chainG_one fuel (liftCtoBPoly D) (bArgAmtD' A D)) hd0 hd1
    (fun l _ => chain_hsc fuel (liftCtoBPoly D) (bArgAmtD' A D) l)
    hβcn hdiv
    (fun l _ => chain_hG2 fuel (liftCtoBPoly D) (bArgAmtD' A D) l)
    hc0 hβ0 hlc hcb hjlt hQ hCne hfilt hg hgcn hg0 hrem hne hu hgu hpz

-- Restatement: the divided-PRS recurrence `hG2` holds DEFINITIONALLY for the concrete `subresPRS`
-- chain element `chainG` and β-divisor `chainBt` (no list/recurrence plumbing).
example (fuel : ℕ) (P Q : BPoly) (l : ℕ) :
    chainG fuel P Q (l + 2)
      = bdivC fuel (bpsremainder fuel (chainG fuel P Q l) (chainG fuel P Q (l + 1)))
          (chainBt fuel P Q l) :=
  chain_hG2 fuel P Q l

-- Restatement: the degree-`j` filter of the REAL `subresPRS` returns the chain's degree-`j` element —
-- the singleton-filter fact `hfilt` DISCHARGED from strict `bdeg` decrease (no hypothesis taken).
example (fuel : ℕ) (P Q : BPoly) (m : ℕ) (hfo : m + 2 + 1 < fuel)
    (hnz : ∀ i ≤ m + 2, ¬ bisZero (chainG fuel P Q i) = true)
    (hzN : bisZero (chainG fuel P Q (m + 2 + 1)) = true)
    (hstrict : ∀ i < m + 2, bdeg (chainG fuel P Q (i + 1)) < bdeg (chainG fuel P Q i)) :
    toBPoly (bsubresultantGcd fuel (toBPoly (chainG fuel P Q (m + 2))).natDegree P Q)
      = toBPoly (chainG fuel P Q (m + 2)) :=
  chain_hfilt fuel P Q m hfo hnz hzN hstrict

/-! ### Closing Example 2.4.1: the residue ring `ℚ[t]/(4t²+1)` and `IsDomain`
The concrete agreement `lrtGcdCompute_isSimilar_lrtSubresultant_concrete` needs a residue map
`φ : ℚ[X] →+* S` killing `toPoly R` with `S` a domain. For Example 2.4.1 the modulus is `R = 4t²+1`
(`cR241`); since `4X²+1` is **irreducible over ℚ** (degree 2, no rational root: `4x²+1 ≥ 1 > 0`),
`S = AdjoinRoot (toPoly cR241) ≅ ℚ(i/2)` is a **field**, hence a domain. The quotient map
`φ = AdjoinRoot.mk (toPoly cR241)` kills `toPoly cR241` by `AdjoinRoot.mk_self`. -/

/-- **`toPoly cR241 = 1 + 4·X²`**: the Rothstein–Trager modulus `R = 4t²+1` read into `ℚ[X]`
(here `X` is the `t`-indeterminate). -/
theorem toPoly_cR241 : toPoly cR241 = 1 + 4 * X ^ 2 := by
  show toPoly [(1 : ℚ), 0, 4] = _
  rw [toPoly_cons, toPoly_cons, toPoly_cons, toPoly_nil]
  simp only [map_zero, map_one, mul_zero, add_zero, map_ofNat]
  ring

/-- **`toPoly cR241` has degree 2**: `(toPoly cR241).natDegree = 2`. -/
theorem natDegree_toPoly_cR241 : (toPoly cR241).natDegree = 2 := by
  rw [toPoly_cR241]
  compute_degree!

/-- **`4X²+1` has no rational root**: `4x²+1 ≥ 1 > 0` for every `x : ℚ`, so it is never zero. -/
theorem toPoly_cR241_not_isRoot (x : ℚ) : ¬ (toPoly cR241).IsRoot x := by
  rw [Polynomial.IsRoot.def, toPoly_cR241]
  simp only [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_pow, Polynomial.eval_X]
  have : (0 : ℚ) ≤ 4 * x ^ 2 := by positivity
  intro h
  linarith

/-- **`4X²+1` (i.e. `toPoly cR241`) is irreducible over `ℚ`**: degree 2 with no rational root
(`irreducible_of_degree_le_three_of_not_isRoot`). -/
theorem irreducible_toPoly_cR241 : Irreducible (toPoly cR241) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [natDegree_toPoly_cR241]; decide
  · exact toPoly_cR241_not_isRoot

/-- **`ℚ[t]/(4t²+1)` is a field** (`Fact (Irreducible (toPoly cR241))` ⟹ `AdjoinRoot.instField`). -/
noncomputable instance : Fact (Irreducible (toPoly cR241)) := ⟨irreducible_toPoly_cR241⟩

/-- **The residue ring** `R241 := AdjoinRoot (toPoly cR241) = ℚ[t]/(4t²+1)` of Example 2.4.1 — a field
(hence a domain), over which the LRT log argument is normalized. -/
noncomputable abbrev R241 : Type := AdjoinRoot (toPoly cR241)

/-- **The residue map** `φ241 := AdjoinRoot.mk (toPoly cR241) : ℚ[X] →+* R241` (the quotient map). -/
noncomputable abbrev φ241 : ℚ[X] →+* R241 := AdjoinRoot.mk (toPoly cR241)

/-- **`φ241` kills `toPoly cR241`**: `φ241 (toPoly cR241) = 0` (`AdjoinRoot.mk_self`). -/
theorem φ241_toPoly_cR241 : φ241 (toPoly cR241) = 0 := AdjoinRoot.mk_self

/-! ### The decidable chain regularity for Example 2.4.1 (`native_decide`)
The concrete chain `subresPRS 30 (liftCtoBPoly cD241) (bArgAmtD' cA241 cD241)` has `x`-degrees
`[6,5,4,3,2,1,0]` (indices 0..6), then index 7 is zero. The book's LRT log argument is the **degree-3**
element `x³+2tx²−3x−4t` (index 3), so the regular index is `m + 2 = 3`, i.e. `m = 1`. We instantiate the
headline `lrtGcdCompute_isSimilar_lrtSubresultant` directly at this `m` (the `_concrete` wrapper's
`chain_hfilt` only extracts the *terminal* chain element, so it would force `j = 0`; instead we discharge
the singleton-filter `hfilt` at the degree-3 index by `native_decide`, since the `[6,5,4,3,2,1,0]` degrees
are all distinct ⟹ the degree-3 element is unique). Every `bdeg`/`bisZero`/`cnorm`/`cmod`/`cisZero` fact
on the chain is a decidable `ℚ`-fact, pinned by `native_decide` (the established `lrtGcd_ex241` pattern;
`decide` stalls on the GMP-backed `ℚ` arithmetic). `chainG`/`chainBt` unfold to the computable
`goState`/`goBeta`. Throughout, `fuel = 30`, `P = liftCtoBPoly cD241`, `Q = bArgAmtD' cA241 cD241`. The two
facts mentioning the `Classical.choose` witnesses `chainC`/`chainS` (the content nonzero `hc0` and
quotient-degree bound `hQ`) are derived separately (below). -/

/-- The Example 2.4.1 chain abbreviation: `gP = liftCtoBPoly cD241`, `gQ = bArgAmtD' cA241 cD241`. -/
private abbrev gP : BPoly := liftCtoBPoly cD241
private abbrev gQ : BPoly := bArgAmtD' cA241 cD241

/-- **The degree-3 element's `x`-degree is 3**: `(toBPoly (chainG 30 gP gQ 3)).natDegree = 3` (the regular
LRT index `j = m+2 = 3`). Via `bdeg_eq_natDegree` and `native_decide` on `bdeg (chainG … 3)`. -/
theorem natDegree_toBPoly_chainG3_ex241 :
    (toBPoly (chainG 30 gP gQ 3)).natDegree = 3 := by
  rw [← bdeg_eq_natDegree]
  show bdeg (goState 30 (gP, gQ, [-1], bdeg gP - bdeg gQ) 3).1 = 3
  native_decide

/-- `(toPoly cD241).natDegree = 6`: `D = x⁶−5x⁴+5x²+4` has degree 6 (via `cdeg_eq_natDegree`). -/
theorem natDegree_toPoly_cD241 : (toPoly cD241).natDegree = 6 := by
  rw [← cdeg_eq_natDegree]; native_decide

/-- **`hd0` for Ex 2.4.1**: `(toBPoly (chainG 30 gP gQ 0)).natDegree = (toPoly cD241).natDegree` (both 6). -/
theorem hd0_ex241 :
    (toBPoly (chainG 30 gP gQ 0)).natDegree = (toPoly cD241).natDegree := by
  rw [← bdeg_eq_natDegree, natDegree_toPoly_cD241]
  show bdeg (goState 30 (gP, gQ, [-1], bdeg gP - bdeg gQ) 0).1 = 6
  native_decide

/-- **`hd1` for Ex 2.4.1**: `(toBPoly (chainG 30 gP gQ 1)).natDegree = (toPoly cD241).natDegree − 1`
(5 = 6−1). -/
theorem hd1_ex241 :
    (toBPoly (chainG 30 gP gQ 1)).natDegree = (toPoly cD241).natDegree - 1 := by
  rw [← bdeg_eq_natDegree, natDegree_toPoly_cD241]
  show bdeg (goState 30 (gP, gQ, [-1], bdeg gP - bdeg gQ) 1).1 = 6 - 1
  native_decide

/-- **Chain nonzero through index 3**: `chainG 0 … chainG 3` are all nonzero (degrees `6,5,4,3`). -/
theorem chainG_ne_zero_ex241 :
    ∀ i ≤ 3, ¬ bisZero (chainG 30 gP gQ i) = true := by
  simp only [chainG]; native_decide

/-- **`hβcn` for Ex 2.4.1**: the β-divisors `chainBt 0`, `chainBt 1` are nonzero `ℚ[t]` lists
(`[1]`, `[0,0,36]`). -/
theorem hβcn_ex241 :
    ∀ l ≤ 1, cnorm (chainBt 30 gP gQ l) ≠ [] := by
  intro l hl; interval_cases l <;>
    · simp only [chainBt]; native_decide

/-- **`hβ0` for Ex 2.4.1**: the β-divisors `chainBt 0`, `chainBt 1` read to nonzero `ℚ[t]` polynomials
(`toPoly ≠ 0`), via `cnorm_eq_nil_iff`. -/
theorem hβ0_ex241 :
    ∀ l ≤ 1, toPoly (chainBt 30 gP gQ l) ≠ 0 := by
  intro l hl h
  exact hβcn_ex241 l hl ((cnorm_eq_nil_iff _).mpr h)

/-- **`hdiv` for Ex 2.4.1** (Collins β-divisibility, concrete): `chainBt l` divides every `x`-coefficient
of the pseudo-remainder `prem (chainG l) (chainG (l+1))` exactly (`cmod` reads to 0), via
`cnorm_eq_nil_iff`. The decidable per-coefficient `cmod`-zero certificate, `native_decide`'d. -/
theorem hdiv_ex241 :
    ∀ l ≤ 1, ∀ a ∈ bpsremainder 30 (chainG 30 gP gQ l) (chainG 30 gP gQ (l + 1)),
      toPoly (cmod 30 a (chainBt 30 gP gQ l)) = 0 := by
  intro l hl a ha
  rw [← cnorm_eq_nil_iff]
  revert a ha
  interval_cases l <;>
    · simp only [chainBt, chainG]; native_decide

/-- **`hlc` for Ex 2.4.1**: the leading `x`-coefficient of `chainG (l+1)` (`l ≤ 1`) is nonzero — via
`toPoly_blc_eq_coeff` + `toPoly_blc_ne_zero` (the element is nonzero). -/
theorem hlc_ex241 :
    ∀ l ≤ 1, (toBPoly (chainG 30 gP gQ (l + 1))).coeff
      (toBPoly (chainG 30 gP gQ (l + 1))).natDegree ≠ 0 := by
  intro l hl
  rw [← bdeg_eq_natDegree, ← toPoly_blc_eq_coeff]
  exact toPoly_blc_ne_zero _ (chainG_ne_zero_ex241 (l + 1) (by omega))

/-- **`hcb` for Ex 2.4.1**: the `x`-degrees strictly decrease (`chainG (l+2)` below `chainG (l+1)`,
`l ≤ 1`: `4<5`, `3<4`), via `bdeg_eq_natDegree`. -/
theorem hcb_ex241 :
    ∀ l ≤ 1, (toBPoly (chainG 30 gP gQ (l + 2))).natDegree
      < (toBPoly (chainG 30 gP gQ (l + 1))).natDegree := by
  intro l hl
  rw [← bdeg_eq_natDegree, ← bdeg_eq_natDegree]
  interval_cases l <;>
    · simp only [chainG]; native_decide

/-- **`hjlt` for Ex 2.4.1**: the degree-3 element `chainG 3` is strictly below `chainG (l+2)` for `l<1`
(only `l=0`: `3<4`), via `bdeg_eq_natDegree`. -/
theorem hjlt_ex241 :
    ∀ l < 1, (toBPoly (chainG 30 gP gQ (1 + 2))).natDegree
      < (toBPoly (chainG 30 gP gQ (l + 2))).natDegree := by
  intro l hl
  rw [← bdeg_eq_natDegree, ← bdeg_eq_natDegree]
  interval_cases l
  simp only [chainG]; native_decide

/-- **`hCne` for Ex 2.4.1**: the degree-3 chain element `chainG 3` is nonzero (`toBPoly ≠ 0`), via
`bisZero_iff_toBPoly_eq_zero`. -/
theorem hCne_ex241 : toBPoly (chainG 30 gP gQ (1 + 2)) ≠ 0 := by
  rw [Ne, ← bisZero_iff_toBPoly_eq_zero]
  exact chainG_ne_zero_ex241 3 (by omega)

end DeepWiki.SymbolicIntegration.Compute
