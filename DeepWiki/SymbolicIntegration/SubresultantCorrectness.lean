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
scalar division via `cmod_eq_zero_of_dvd`. -/
theorem toBPoly_bdivC_exact_of_dvd (fuel : ℕ) (p : BPoly) (c : CPoly) (hc : cnorm c ≠ [])
    (hfuel : ∀ a ∈ p, (cnorm a).length ≤ fuel) (hdvd : ∀ a ∈ p, toPoly c ∣ toPoly a) :
    Polynomial.C (toPoly c) * toBPoly (bdivC fuel p c) = toBPoly p :=
  toBPoly_bdivC_exact fuel p c hc
    (fun a ha => cmod_eq_zero_of_dvd_loc fuel a c hc (hfuel a ha) (hdvd a ha))

/-! ### The honest ceiling: the full `bsubresultantGcd ↔ lrtSubresultant` chain agreement
The pieces above realize **one** subresultant-PRS step of the computable engine against the abstract
subresultant, identify the LRT operands exactly, and (now) prove the β-divisor exact-division
`toBPoly_bdivC_exact`. The **full** agreement `toBPoly (bsubresultantGcd fuel j P Q) ∼ lrtSubresultant
A D j` (up to a `ℚ[t]` content/unit, then `lrtGcdCompute` after `bprimitivePartX`/`bmonicXmodR`) still
needs the genuinely deep **Collins–Brown chain induction**: with `toBPoly_bdivC_exact` in hand one can
identify each `subresPRS` element `Rᵢ₊₂ = bdivC fuel (prem Rᵢ Rᵢ₊₁) βᵢ` with the abstract subresultant
through `subresultant_C_mul_eq_rem_of_bpsremainder` (the one PRS step) — but the remaining work is to
match the *computable* β/ψ accumulation (`subresPRS`'s `cpowP`/`cdiv` ladder) against the abstract
`subresPRS_beta`/`subresPRS_gamma` (`SubresultantPRS`), induct along the chain with the
defective/normal collapse (`subresultant_prs_defective_eq`/`subresultant_prs_normal_eq`) to cancel the
accumulated content (`ηᵢ = 1`), and finally absorb the `bsubresultantGcd` degree filter and the
`bprimitivePartX`/`bmonicXmodR` content/monic-normalization. That multi-step induction (matching two
independently-defined coefficient recurrences and the per-coefficient divisibility side-conditions of
`toBPoly_bdivC_exact_of_dvd`) is the remaining work; the one-step engine, operand identification, and
the exact-division core proven here are its reusable foundation. -/

end DeepWiki.SymbolicIntegration.Compute
