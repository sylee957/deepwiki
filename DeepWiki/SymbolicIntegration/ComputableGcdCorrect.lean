import DeepWiki.SymbolicIntegration.ComputableSplitFactorFast
import DeepWiki.SymbolicIntegration.ComputableFieldGcd
import DeepWiki.SymbolicIntegration.SubresultantCorrectness

/-! # Abstract correctness of the fraction-free gcd `cgcdFF` over ℚ(x)[t]
The fraction-free monic gcd `cgcdFF` (`ComputableSplitFactorFast`) clears the ℚ(x)-denominators of its
inputs into ℚ[x][t] (`clearDenoms`), runs a **primitive polynomial-remainder sequence** `primPRSgcd`
over ℚ[x][t] (each step the primitive part of a pseudo-remainder, no field division), lifts the result
back to ℚ(x)[t] and monic-normalizes. It is validated *pointwise* by `native_decide` (Example 3.5.1 in
`ComputableSplitFactorFast`). This file proves the **abstract** correctness — for ALL inputs, axiom-clean
(no `native_decide`) — that `cgcdFF` computes the polynomial gcd over the field ℚ(x) = `RatFunc ℚ`.

Two carriers and two Horner bridges meet here, over the same indeterminate `t`:
* `toPolyG : CPolyG QFunNZ → (RatFunc ℚ)[X]` (`GenericPolyEngine`) — the honest ℚ(x)[t] polynomial of a
  `t`-list with ℚ(x)-coefficients.
* `toBPoly : BPoly → (ℚ[X])[X]` (`ComputeCorrectness`) — the honest ℚ[x][t] polynomial of a `t`-list
  with ℚ[x]-coefficients; composing with the coefficient ring embedding `algebraMap ℚ[X] (RatFunc ℚ)`
  re-reads it as a ℚ(x)[t] polynomial `toPolyB`.

The spine:
1. **`clearDenoms` bridge**: `toPolyB (clearDenoms p) = C s · toPolyG p` for the (nonzero) common
   denominator scalar `s ∈ RatFunc ℚ` — so the cleared ℚ[x][t] poly is, over the field ℚ(x), a
   **unit multiple** of `toPolyG p` (`Associated`).
2. **primitive-PRS ⇒ gcd**: each `primPRSgcd` step preserves `gcd(toPolyB·, toPolyB·)` up to associates
   over the field ℚ(x) — content stripping is a ℚ(x)-unit (`bprimitivePartX`), and a pseudo-remainder
   step is a Euclidean step up to a ℚ(x)-unit content factor. So `toPolyB (primPRSgcd P Q)` is
   `Associated` to `gcd (toPolyB P) (toPolyB Q)`.
3. **`cgcdFF` correct**: combine 1+2 — over ℚ(x), `toPolyG (cgcdFF p q)` is `Associated` to
   `gcd (toPolyG p) (toPolyG q)` in `(RatFunc ℚ)[X]`, the monic normalization fixing the unit. -/

open Polynomial Classical

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

/-! ### The coefficient-ring lift `(ℚ[X])[X] → (RatFunc ℚ)[X]` and `toPolyB`
`liftRF` is the polynomial ring map induced by the field embedding `algebraMap ℚ[X] (RatFunc ℚ)`
(injective). `toPolyB p := liftRF (toBPoly p)` reads a `BPoly` (ℚ[x][t]) as a ℚ(x)[t] polynomial, in
the **same** indeterminate `t` as `toPolyG`. Its homomorphism / coefficient lemmas all descend from the
`toBPoly` bridge of `ComputeCorrectness`. -/

/-- The field embedding `algebraMap ℚ[X] (RatFunc ℚ)` (`ℚ[x] ↪ ℚ(x)`), abbreviated. -/
noncomputable abbrev amRF : ℚ[X] →+* RatFunc ℚ := algebraMap ℚ[X] (RatFunc ℚ)

/-- The induced coefficient-ring lift `(ℚ[X])[X] →+* (RatFunc ℚ)[X]` (`ℚ[x][t] → ℚ(x)[t]`), applying
`amRF` to every `t`-coefficient. -/
noncomputable abbrev liftRF : (ℚ[X])[X] →+* (RatFunc ℚ)[X] := Polynomial.mapRingHom amRF

/-- **The ℚ(x)[t] reading of a `BPoly`** `toPolyB p`: read the ℚ[x][t] polynomial `toBPoly p` over the
field ℚ(x) via the coefficient embedding `amRF`. Lives in the same `(RatFunc ℚ)[X]` as `toPolyG`. -/
noncomputable def toPolyB (p : BPoly) : (RatFunc ℚ)[X] := liftRF (toBPoly p)

/-- `toPolyB [] = 0`. -/
@[simp] theorem toPolyB_nil : toPolyB ([] : BPoly) = 0 := by simp [toPolyB]

/-- `amRF (toPoly c) ≠ 0` whenever `toPoly c ≠ 0` (the field embedding is injective). -/
theorem amRF_toPoly_ne_zero {c : CPoly} (hc : toPoly c ≠ 0) : amRF (toPoly c) ≠ 0 :=
  Compute.am_toPoly_ne_zero hc

/-- **`toPolyB` ignores normalization**: `toPolyB (bnorm p) = toPolyB p`. -/
@[simp] theorem toPolyB_bnorm (p : BPoly) : toPolyB (bnorm p) = toPolyB p := by
  simp [toPolyB]

/-- `toPolyB p = 0 ↔ toBPoly p = 0` (the lift is injective, `amRF` injective on coefficients). -/
theorem toPolyB_eq_zero_iff (p : BPoly) : toPolyB p = 0 ↔ toBPoly p = 0 := by
  rw [toPolyB, ← Polynomial.map_zero (amRF)]
  exact Polynomial.map_injective amRF (RatFunc.algebraMap_injective ℚ) |>.eq_iff

/-- `toPolyB p = 0 ↔ bisZero p = true`. -/
theorem toPolyB_eq_zero_iff_bisZero (p : BPoly) : toPolyB p = 0 ↔ bisZero p = true := by
  rw [toPolyB_eq_zero_iff, bisZero_iff_toBPoly_eq_zero]

/-- **Coefficient read**: `(toPolyB p).coeff i = amRF (toPoly (p.getD i []))`. -/
theorem toPolyB_coeff (p : BPoly) (i : ℕ) :
    (toPolyB p).coeff i = amRF (toPoly (p.getD i [])) := by
  rw [toPolyB, liftRF, Polynomial.coe_mapRingHom, Polynomial.coeff_map, toBPoly_coeff]

/-! ### Step 1 — the `clearDenoms` bridge `ℚ(x)[t] ↔ ℚ[x][t]`
`clearDenoms p` multiplies the `t`-polynomial `p ∈ ℚ(x)[t]` through by the product of its
ℚ(x)-coefficient denominators, landing a `BPoly ∈ ℚ[x][t]` whose `i`-th coefficient is
`numᵢ · ∏_{j≠i} denⱼ`. Read back over the field ℚ(x) (`toPolyB`), this equals `C s · toPolyG p` for the
**common denominator scalar** `s = ∏_j denⱼ ∈ ℚ(x)` (nonzero, a unit). So the cleared polynomial is, over
ℚ(x), a unit multiple of `toPolyG p` (`Associated`). -/

/-- A `QFunNZ` coefficient reads as `amRF (num) / amRF (den)` in `RatFunc ℚ`. -/
theorem toQFunNZ_eq_div (c : QFunNZ) :
    QFunNZ.toQFunNZ c
      = amRF (toPoly (CPolyG.qnumCoeff c)) / amRF (toPoly (CPolyG.qdenCoeff c)) := by
  obtain ⟨⟨a, b⟩, hb⟩ := c; rfl

/-- A `QFunNZ` coefficient's denominator is a nonzero `ℚ[X]` (by subtype membership). -/
theorem toPoly_qdenCoeff_ne_zero (c : QFunNZ) : toPoly (CPolyG.qdenCoeff c) ≠ 0 := by
  obtain ⟨⟨a, b⟩, hb⟩ := c; exact hb

/-- **The common-denominator scalar** `commonDen p ∈ ℚ[X]`: the product of all the ℚ[x]-denominators of
`p`'s ℚ(x)-coefficients, `∏_j toPoly (qdenCoeff (p.get j))`. The (nonzero) ℚ(x)-unit by which
`clearDenoms` scales `toPolyG p`. -/
noncomputable def commonDen (p : CPolyG QFunNZ) : ℚ[X] :=
  ((p.map CPolyG.qdenCoeff).map toPoly).prod

/-- `commonDen p ≠ 0`: a product of nonzero denominators. -/
theorem commonDen_ne_zero (p : CPolyG QFunNZ) : commonDen p ≠ 0 := by
  rw [commonDen]
  refine List.prod_ne_zero ?_
  intro hmem
  rw [List.mem_map] at hmem
  obtain ⟨d, hd, hd0⟩ := hmem
  rw [List.mem_map] at hd
  obtain ⟨c, hc, rfl⟩ := hd
  exact toPoly_qdenCoeff_ne_zero c hd0

/-- `amRF (commonDen p) ≠ 0` (the field embedding of a nonzero product). -/
theorem amRF_commonDen_ne_zero (p : CPolyG QFunNZ) : amRF (commonDen p) ≠ 0 :=
  (map_ne_zero_iff _ (RatFunc.algebraMap_injective ℚ)).mpr (commonDen_ne_zero p)

/-- The list-getElem reading of `clearDenoms p` at an in-range index `i`: the `i`-th cleared coefficient
is `numᵢ · (∏_{j≠i} denⱼ)`, with the `∏_{j≠i}` the filtered fold over the denominator list. -/
theorem clearDenoms_getElem (p : CPolyG QFunNZ) (i : ℕ) (hi : i < p.length) :
    (CPolyG.clearDenoms p)[i]? = some (Compute.cmul (CPolyG.qnumCoeff (p.getD i CField.zero))
      ((((p.map CPolyG.qdenCoeff).zipIdx).filter (fun de => decide (de.2 ≠ i))).foldl
        (fun acc de => Compute.cmul acc de.1) [1])) := by
  unfold CPolyG.clearDenoms
  simp only
  rw [List.getElem?_map, List.getElem?_zipIdx, List.getElem?_eq_getElem hi]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

/-- `map`-`fst` over a `zipIdx` collapses to the plain `map` (the index is dropped). -/
theorem map_zipIdx_fst_toPoly (tl : List CPoly) (k : ℕ) :
    (tl.zipIdx k).map (fun de => toPoly de.1) = tl.map toPoly := by
  calc (tl.zipIdx k).map (fun de => toPoly de.1)
      = ((tl.zipIdx k).map Prod.fst).map toPoly := by rw [List.map_map]; rfl
    _ = tl.map toPoly := by simp

/-- **Filtered-product times removed factor = full product** (`CommMonoid`, via `zipIdx` index bounds):
the product over `j ≠ i` of `f (ds[j])` times `f (ds[i])` is the whole product, for `i` in range. The
combinatorial core of the `clearDenoms` per-coefficient identity. -/
theorem filter_prod_mul {α M : Type*} [CommMonoid M] (f : α → M) (def0 : α) :
    ∀ (ds : List α) (k i : ℕ), k ≤ i → i < k + ds.length →
      (((ds.zipIdx k).filter (fun de => decide (de.2 ≠ i))).map (fun de => f de.1)).prod
        * f (ds.getD (i - k) def0) = (ds.map f).prod := by
  intro ds
  induction ds with
  | nil => intro k i _ hlt; simp at hlt; omega
  | cons d tl ih =>
    intro k i hk hlt
    rw [List.zipIdx_cons, List.filter_cons]
    rcases Nat.eq_or_lt_of_le hk with hik | hik
    · subst hik
      simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, if_false]
      have hkeep : ((tl.zipIdx (k+1)).filter (fun de => decide (de.2 ≠ k))).map (fun de => f de.1)
          = (tl.zipIdx (k+1)).map (fun de => f de.1) := by
        congr 1
        rw [List.filter_eq_self.mpr]
        intro de hde
        have hge := List.le_snd_of_mem_zipIdx hde
        simp only [decide_eq_true_eq, ne_eq]; omega
      rw [hkeep]
      calc ((tl.zipIdx (k+1)).map (fun de => f de.1)).prod * f ((d :: tl).getD (k - k) def0)
          = (tl.map f).prod * f d := by
            congr 1
            · calc ((tl.zipIdx (k+1)).map (fun de => f de.1)).prod
                  = (((tl.zipIdx (k+1)).map Prod.fst).map f).prod := by rw [List.map_map]; rfl
                _ = (tl.map f).prod := by simp
            · simp
        _ = (List.map f (d :: tl)).prod := by rw [List.map_cons, List.prod_cons, mul_comm]
    · have hne : (k ≠ i) := Nat.ne_of_lt hik
      simp only [hne, ne_eq, not_false_eq_true, decide_true, if_true]
      rw [List.map_cons, List.prod_cons]
      have hsub : i - k = (i - (k+1)) + 1 := by omega
      rw [hsub, List.getD_cons_succ]
      have hih := ih (k+1) i (by omega) (by simp at hlt ⊢; omega)
      rw [List.map_cons, List.prod_cons, ← hih, mul_assoc]

/-- `toPoly` of a `cmul`-fold is `toPoly init` times the product of the `toPoly`-images of the folded
list (the `ℚ[X]`-product realized by the computable fold). -/
theorem toPoly_foldl_cmul (init : CPoly) (ds : List (CPoly × ℕ)) :
    toPoly (ds.foldl (fun acc de => Compute.cmul acc de.1) init)
      = toPoly init * (ds.map (fun de => toPoly de.1)).prod := by
  induction ds generalizing init with
  | nil => simp
  | cons hd tl ih =>
    rw [List.foldl_cons, ih, toPoly_cmul, List.map_cons, List.prod_cons]; ring

/-- `clearDenoms` preserves the `t`-length: `(clearDenoms p).length = p.length`. -/
theorem clearDenoms_length (p : CPolyG QFunNZ) : (CPolyG.clearDenoms p).length = p.length := by
  unfold CPolyG.clearDenoms; simp

/-- `toPolyG p` vanishes past the list length (the out-of-range coefficient is `CField.zero = 0`). -/
theorem toPolyG_coeff_eq_zero_of_length_le (p : CPolyG QFunNZ) {i : ℕ} (hi : p.length ≤ i) :
    (toPolyG p).coeff i = 0 := by
  rw [toPolyG_coeff, List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
  show CFieldSpec.toK (CField.zero : QFunNZ) = 0
  rw [CFieldSpec.toK_zero]

/-- **Per-coefficient `clearDenoms` identity**: `(toPolyB (clearDenoms p)).coeff i = amRF (commonDen p)
· (toPolyG p).coeff i` for every `i` — the cleared `i`-th coefficient `amRF (numᵢ · ∏_{j≠i} denⱼ)` equals
the common denominator scalar `amRF (∏_j denⱼ)` times `amRF numᵢ / amRF denᵢ`. -/
theorem toPolyB_clearDenoms_coeff (p : CPolyG QFunNZ) (i : ℕ) :
    (toPolyB (CPolyG.clearDenoms p)).coeff i
      = amRF (commonDen p) * (toPolyG p).coeff i := by
  rcases lt_or_ge i p.length with hi | hi
  · -- in range: use the getElem reading, fold-product, and the filter-product identity
    rw [toPolyB_coeff, toPolyG_coeff]
    rw [List.getD_eq_getElem?_getD, clearDenoms_getElem p i hi, Option.getD_some]
    rw [toPoly_cmul, toPoly_foldl_cmul, show toPoly ([1] : CPoly) = 1 by simp [toPoly_cons],
      one_mul]
    set dens := p.map CPolyG.qdenCoeff with hdens
    -- common denominator = ∏_j toPoly denⱼ
    have hcd : commonDen p = (dens.map toPoly).prod := by rw [commonDen, hdens]
    -- the i-th denominator (in range)
    have hlen : i < dens.length := by rw [hdens, List.length_map]; exact hi
    have hfilt := filter_prod_mul (toPoly) ([] : CPoly) dens 0 i (Nat.zero_le i)
      (by simpa using hlen)
    rw [Nat.sub_zero] at hfilt
    -- denᵢ as the getD
    have hdeni : toPoly (dens.getD i []) = toPoly (CPolyG.qdenCoeff (p.getD i CField.zero)) := by
      congr 1
      rw [hdens, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hi]
      simp
    -- num/den read of the i-th coefficient
    have hcoeff : (CFieldSpec.toK (p.getD i CField.zero) : RatFunc ℚ)
        = amRF (toPoly (CPolyG.qnumCoeff (p.getD i CField.zero)))
          / amRF (toPoly (CPolyG.qdenCoeff (p.getD i CField.zero))) := by
      show QFunNZ.toQFunNZ (p.getD i CField.zero) = _
      rw [toQFunNZ_eq_div]
    have hden0 : amRF (toPoly (CPolyG.qdenCoeff (p.getD i CField.zero))) ≠ 0 :=
      amRF_toPoly_ne_zero (toPoly_qdenCoeff_ne_zero _)
    rw [hcoeff, hcd]
    -- push amRF through the filtered product and absorb the removed factor via hfilt
    have hpushP : amRF (((dens.zipIdx.filter (fun de => decide (de.2 ≠ i))).map
        (fun de => toPoly de.1)).prod)
        * amRF (toPoly (CPolyG.qdenCoeff (p.getD i CField.zero)))
        = amRF ((dens.map toPoly).prod) := by
      rw [← map_mul, ← hdeni, hfilt]
    -- the goal is now `amRF (num * filteredProd) = amRF (∏all) * (amRF num / amRF den)`
    rw [map_mul, mul_comm (amRF ((dens.map toPoly).prod)) _, div_mul_eq_mul_div, eq_div_iff hden0,
      mul_assoc, hpushP]
  · -- out of range: both sides vanish
    rw [toPolyB_coeff, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by rw [clearDenoms_length]; exact hi), Option.getD_none, toPoly_nil,
      map_zero, toPolyG_coeff_eq_zero_of_length_le p hi, mul_zero]

/-- **Step 1 — the `clearDenoms` bridge** (exact form): over the field ℚ(x), the cleared polynomial
`toPolyB (clearDenoms p)` is the common-denominator scalar `C (amRF (commonDen p))` times `toPolyG p`.
So `clearDenoms` realizes ℚ(x)-multiplication by the (nonzero) product of denominators. -/
theorem toPolyB_clearDenoms (p : CPolyG QFunNZ) :
    toPolyB (CPolyG.clearDenoms p) = Polynomial.C (amRF (commonDen p)) * toPolyG p := by
  ext i
  rw [toPolyB_clearDenoms_coeff, Polynomial.coeff_C_mul]

/-- **Step 1 — the `clearDenoms` bridge** (`Associated` form): over the field ℚ(x), the cleared
ℚ[x][t] polynomial and `toPolyG p` are **associates** in `(RatFunc ℚ)[X]` — they differ by the unit
`C (amRF (commonDen p))` (`amRF (commonDen p)` a nonzero `RatFunc ℚ`). The fraction-clearing is a
unit-scaling over the field, so it preserves the gcd up to associates. -/
theorem associated_toPolyB_clearDenoms (p : CPolyG QFunNZ) :
    Associated (toPolyB (CPolyG.clearDenoms p)) (toPolyG p) := by
  rw [toPolyB_clearDenoms]
  exact (associated_unit_mul_left _ _
    (Polynomial.isUnit_C.mpr (amRF_commonDen_ne_zero p).isUnit))

/-! ### Step 2 — the primitive-PRS gcd invariant over ℚ(x)
Over the field ℚ(x) = `RatFunc ℚ`, each `primPRSgcd` step preserves `gcd (toPolyB ·) (toPolyB ·)` up to
associates: a pseudo-remainder step is a Euclidean step up to a ℚ(x)-unit content factor (the
pseudo-division multiplier), and `bprimitivePartX` divides out a ℚ[x]-content that is a ℚ(x)-unit. The
content/multiplier nonvanishing and the exact-division facts enter as explicit hypotheses (they hold for
real PRS runs; proving them unconditionally is the content-gcd theory left to the call site). -/

/-- `liftRF (C c) = C (amRF c)`: the lift sends a constant ℚ[x]-coefficient to its ℚ(x) embedding. -/
theorem liftRF_C (c : ℚ[X]) : liftRF (Polynomial.C c) = Polynomial.C (amRF c) := by
  simp [liftRF, Polynomial.coe_mapRingHom, Polynomial.map_C]

/-- **gcd is invariant under an associated right argument** in `(RatFunc ℚ)[X]`. -/
theorem associated_gcd_right {A B B' : (RatFunc ℚ)[X]} (h : Associated B B') :
    Associated (gcd A B) (gcd A B') := by
  apply associated_of_dvd_dvd
  · exact dvd_gcd (gcd_dvd_left A B) ((gcd_dvd_right A B).trans h.dvd)
  · exact dvd_gcd (gcd_dvd_left A B') ((gcd_dvd_right A B').trans h.symm.dvd)

/-- **The Euclidean-step gcd invariant** in `(RatFunc ℚ)[X]`: if `cu` is a unit and
`cu · A = R + S · B` (a pseudo-division step up to the unit content `cu`), then `gcd A B` and `gcd B R`
are associates — the classic invariant `gcd(A,B) = gcd(B, A mod B)` over the field. -/
theorem associated_gcd_euclid_step {A B R S cu : (RatFunc ℚ)[X]} (hu : IsUnit cu)
    (hrel : cu * A = R + S * B) : Associated (gcd A B) (gcd B R) := by
  apply associated_of_dvd_dvd
  · apply dvd_gcd (gcd_dvd_right A B)
    have h1 : gcd A B ∣ cu * A - S * B :=
      dvd_sub ((gcd_dvd_left A B).mul_left cu) ((gcd_dvd_right A B).mul_left S)
    have hR : cu * A - S * B = R := by rw [hrel]; ring
    rwa [hR] at h1
  · apply dvd_gcd _ (gcd_dvd_left B R)
    have hcuA : gcd B R ∣ cu * A := by
      rw [hrel]; exact dvd_add (gcd_dvd_right B R) ((gcd_dvd_left B R).mul_left S)
    exact (IsUnit.dvd_mul_left hu).mp hcuA

/-- **`bpsremainder` lifts to a ℚ(x)[t] Euclidean relation**: there is a quotient `s` and a multiplier
`c ∈ ℚ[x]` with `C (amRF (toPoly c)) · toPolyB p = toPolyB s · toPolyB q + toPolyB (bpsremainder fuel p
q)` in `(RatFunc ℚ)[X]` — the lift of `toBPoly_bpsremainder` through the field embedding. -/
theorem toPolyB_bpsremainder (fuel : ℕ) (p q : BPoly) :
    ∃ (s : BPoly) (c : CPoly),
      Polynomial.C (amRF (toPoly c)) * toPolyB p
        = toPolyB s * toPolyB q + toPolyB (bpsremainder fuel p q) := by
  obtain ⟨s, c, hsc⟩ := Compute.toBPoly_bpsremainder fuel p q
  refine ⟨s, c, ?_⟩
  have hl := congrArg liftRF hsc
  simp only [map_add, map_mul] at hl
  rw [liftRF_C] at hl
  simpa [toPolyB] using hl

/-- **`bprimitivePartX` lifts to a ℚ(x)-unit scaling**: when the ℚ[x]-content `g = bcontentX fuel p` is
nonzero and divides every `x`-coefficient exactly, `C (amRF (toPoly g)) · toPolyB (bprimitivePartX fuel
p) = toPolyB p` — the lift of `toBPoly_bprimitivePartX_exact`. -/
theorem toPolyB_bprimitivePartX_exact (fuel : ℕ) (p : BPoly)
    (hg : ¬ cisZero (bcontentX fuel p) = true) (hgcn : cnorm (bcontentX fuel p) ≠ [])
    (hrem : ∀ a ∈ bnorm p, toPoly (cmod fuel a (bcontentX fuel p)) = 0) :
    Polynomial.C (amRF (toPoly (bcontentX fuel p))) * toPolyB (bprimitivePartX fuel p)
      = toPolyB p := by
  have hb := Compute.toBPoly_bprimitivePartX_exact fuel p hg hgcn hrem
  have hl := congrArg liftRF hb
  simp only [map_mul] at hl
  rw [liftRF_C] at hl
  simpa [toPolyB] using hl

/-- **`bprimitivePartX` is associated to its input over ℚ(x)**: under the content-exact hypotheses (and
`toPoly g ≠ 0`), `Associated (toPolyB (bprimitivePartX fuel p)) (toPolyB p)` — stripping the ℚ[x]-content
is a ℚ(x)-unit scaling, preserving the gcd up to associates. -/
theorem associated_toPolyB_bprimitivePartX (fuel : ℕ) (p : BPoly)
    (hg : ¬ cisZero (bcontentX fuel p) = true) (hgcn : cnorm (bcontentX fuel p) ≠ [])
    (hg0 : toPoly (bcontentX fuel p) ≠ 0)
    (hrem : ∀ a ∈ bnorm p, toPoly (cmod fuel a (bcontentX fuel p)) = 0) :
    Associated (toPolyB (bprimitivePartX fuel p)) (toPolyB p) := by
  refine ⟨(Polynomial.isUnit_C.mpr (amRF_toPoly_ne_zero hg0).isUnit).unit, ?_⟩
  rw [← toPolyB_bprimitivePartX_exact fuel p hg hgcn hrem]
  show toPolyB (bprimitivePartX fuel p) * Polynomial.C (amRF (toPoly (bcontentX fuel p)))
      = Polynomial.C (amRF (toPoly (bcontentX fuel p))) * toPolyB (bprimitivePartX fuel p)
  ring

/-- **Per-run regularity of the primitive PRS** `PrimPRSRegular fuel P Q`: the inductive predicate
collecting exactly what the `gcd` invariant of each `primPRSgcd` step needs — (i) the recursion reaches
`bisZero Q = true` (termination), and at every non-terminal step, with `Pn = bnorm P`, `Qn = bnorm Q`,
`prem = bpsremainder 60 Pn Qn`, `r = bprimitivePartX 30 prem`: (ii) a pseudo-division witness `(s, c)`
with `C(amRF(toPoly c))·toPolyB Pn = toPolyB s·toPolyB Qn + toPolyB prem` and the multiplier
`amRF(toPoly c)` a ℚ(x)-unit (`≠ 0`), and (iii) `bprimitivePartX` is a ℚ(x)-unit scaling
(`Associated (toPolyB r) (toPolyB prem)`). These hold for honest PRS runs (positive-degree remainder
chain over ℚ(x), nonzero pseudo-division multipliers, primitive-part content a unit); proving them
unconditionally is the content-gcd theory deferred to the call site. -/
def PrimPRSRegular : ℕ → BPoly → BPoly → Prop
  | 0, P, Q =>
    bisZero Q = true ∧ Associated (toPolyB (bprimitivePartX 30 P)) (toPolyB P)
  | fuel + 1, P, Q =>
    (bisZero (bnorm Q) = true ∧
      Associated (toPolyB (bprimitivePartX 30 (bnorm P))) (toPolyB P)) ∨
      (¬ bisZero (bnorm Q) = true ∧
        (∃ (s : BPoly) (c : CPoly),
          Polynomial.C (amRF (toPoly c)) * toPolyB (bnorm P)
            = toPolyB s * toPolyB (bnorm Q)
              + toPolyB (bpsremainder 60 (bnorm P) (bnorm Q))
          ∧ amRF (toPoly c) ≠ 0) ∧
        Associated (toPolyB (bprimitivePartX 30 (bpsremainder 60 (bnorm P) (bnorm Q))))
          (toPolyB (bpsremainder 60 (bnorm P) (bnorm Q))) ∧
        PrimPRSRegular fuel (bnorm Q)
          (bprimitivePartX 30 (bpsremainder 60 (bnorm P) (bnorm Q))))

/-- **Step 2 — the primitive-PRS gcd invariant** (the crux): for a regular run
(`PrimPRSRegular fuel P Q`), the last nonzero primitive remainder `primPRSgcd fuel P Q` is, over the
field ℚ(x), **associated to the polynomial gcd** of the inputs:
`Associated (toPolyB (primPRSgcd fuel P Q)) (gcd (toPolyB P) (toPolyB Q))` in `(RatFunc ℚ)[X]`. The
classic Euclidean invariant `gcd(P,Q) ~ gcd(Q, prem(P,Q))` (each step a ℚ(x)-unit-scaled Euclidean step),
carried along the primitive PRS and bottoming out at `gcd(P, 0) ~ P` when the chain terminates. -/
theorem associated_toPolyB_primPRSgcd :
    ∀ (fuel : ℕ) (P Q : BPoly), PrimPRSRegular fuel P Q →
      Associated (toPolyB (CPolyG.primPRSgcd fuel P Q)) (gcd (toPolyB P) (toPolyB Q)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro P Q hreg
    obtain ⟨hQ, hprim⟩ := hreg
    -- termination: Q = 0, result = bprimitivePartX 30 P
    have hQ0 : toPolyB Q = 0 := (toPolyB_eq_zero_iff_bisZero Q).mpr hQ
    show Associated (toPolyB (bprimitivePartX 30 P)) (gcd (toPolyB P) (toPolyB Q))
    rw [hQ0]
    exact hprim.trans (gcd_zero_right' (toPolyB P)).symm
  | succ fuel ih =>
    intro P Q hreg
    show Associated (toPolyB (
        let P := bnorm P; let Q := bnorm Q;
        if bisZero Q then bprimitivePartX 30 P
        else primPRSgcd fuel Q (bprimitivePartX 30 (bpsremainder 60 P Q))))
      (gcd (toPolyB P) (toPolyB Q))
    simp only
    by_cases hQ : bisZero (bnorm Q) = true
    · rw [if_pos hQ]
      rw [PrimPRSRegular] at hreg
      rcases hreg with ⟨_, hprim⟩ | ⟨hne, _⟩
      · have hQ0 : toPolyB Q = 0 := by
          rw [← toPolyB_bnorm]; exact (toPolyB_eq_zero_iff_bisZero _).mpr hQ
        rw [hQ0]
        exact hprim.trans (gcd_zero_right' (toPolyB P)).symm
      · exact absurd hQ hne
    · rw [if_neg hQ]
      rw [PrimPRSRegular] at hreg
      rcases hreg with ⟨h, _⟩ | ⟨_, ⟨s, c, hrel, hc0⟩, hassoc, hrec⟩
      · exact absurd h hQ
      -- the step: gcd(P,Q) ~ gcd(Q, r), then recurse
      set Pn := bnorm P with hPn
      set Qn := bnorm Q with hQn
      set prem := bpsremainder 60 Pn Qn with hprem
      set r := bprimitivePartX 30 prem with hr
      have hih := ih Qn r hrec
      -- gcd(toPolyB Pn, toPolyB Qn) ~ gcd(toPolyB Qn, toPolyB r)
      have hstep : Associated (gcd (toPolyB Pn) (toPolyB Qn)) (gcd (toPolyB Qn) (toPolyB r)) := by
        have heuc : Associated (gcd (toPolyB Pn) (toPolyB Qn))
            (gcd (toPolyB Qn) (toPolyB prem)) :=
          associated_gcd_euclid_step (A := toPolyB Pn) (B := toPolyB Qn) (R := toPolyB prem)
            (S := toPolyB s) (Polynomial.isUnit_C.mpr hc0.isUnit)
            (by linear_combination hrel)
        exact heuc.trans (associated_gcd_right hassoc.symm)
      -- assemble: result = primPRSgcd fuel Qn r ~ gcd(toPolyB Qn)(toPolyB r) ~ gcd(toPolyB Pn)(toPolyB Qn)
      --   and gcd(toPolyB Pn)(toPolyB Qn) = gcd(toPolyB P)(toPolyB Q) since toPolyB bnorm = toPolyB
      rw [show toPolyB P = toPolyB Pn by rw [hPn, toPolyB_bnorm],
        show toPolyB Q = toPolyB Qn by rw [hQn, toPolyB_bnorm]]
      exact hih.trans hstep.symm

/-! ### Step 3 — the `cgcdFF` capstone
`cgcdFF p q = cmonicG (liftBPolyToQFunNZ (primPRSgcd fuel P Q))` with `(P, Q)` the `bdeg`-ordered pair
of `clearDenoms p`, `clearDenoms q`. Reading the result through `toPolyG`, the lift-back is exact, the
monic-normalization is a unit-scaling, and the primitive-PRS invariant (step 2) plus the `clearDenoms`
bridge (step 1) combine — over the field ℚ(x) — to the polynomial gcd of the inputs. -/

/-- **The lift-back bridge** `toPolyG (liftBPolyToQFunNZ b) = toPolyB b`: reading a `BPoly` (ℚ[x][t])
coefficientwise as `c/1 ∈ ℚ(x)` (`liftBPolyToQFunNZ`) and then through `toPolyG` gives the SAME ℚ(x)[t]
polynomial as the coefficient-ring embedding `toPolyB` — both send the `i`-th coefficient to
`amRF (toPoly bᵢ)`. -/
theorem toPolyG_liftBPolyToQFunNZ (b : BPoly) :
    toPolyG (CPolyG.liftBPolyToQFunNZ b) = toPolyB b := by
  apply Polynomial.ext
  intro i
  rw [toPolyG_coeff, toPolyB_coeff, CPolyG.liftBPolyToQFunNZ,
    List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : b[i]? with
  | none => simp [CFieldSpec.toK_zero, Compute.toPoly_nil]
  | some c =>
    simp only [Option.map_some, Option.getD_some]
    show QFunNZ.toQFunNZ _ = amRF (toPoly c)
    rw [toQFunNZ_eq_div]
    have h1 : Compute.toPoly [1] = 1 := by simp [Compute.toPoly_cons, Compute.toPoly_nil]
    show amRF (toPoly c) / amRF (Compute.toPoly [1]) = amRF (toPoly c)
    rw [h1, map_one, div_one]

/-- **Monic-normalization is a unit-scaling**: over a field, `cmonicG p` differs from `p` (read by
`toPolyG`) by the unit `C ((cleadG)⁻¹)`, so they are associates in `K[X]`. -/
theorem associated_toPolyG_cmonicG {α : Type*} [CField α] [CFieldSpec α] (p : CPolyG α) :
    Associated (toPolyG (CPolyG.cmonicG p)) (toPolyG p) := by
  rw [CPolyG.cmonicG]
  split_ifs with h
  · rw [toPolyG_nil]
    have hz : toPolyG p = 0 := (cisZeroG_iff p).mp (by rwa [cisZeroG_cnormG] at h)
    rw [hz]
  · rw [toPolyG_cscaleG, toPolyG_cnormG]
    have hne : cnormG (cnormG p) ≠ [] := by
      rw [cnormG_idem]; intro he
      exact h (by rw [cisZeroG_cnormG, cisZeroG_iff, ← toPolyG_cnormG, he, toPolyG_nil])
    exact associated_unit_mul_left _ _
      (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr
        (by rw [CFieldSpec.toK_inv]; exact inv_ne_zero (toK_cleadG_ne_zero hne))))

/-- **Step 3 — abstract correctness of `cgcdFF`** (under a regular run): over the field ℚ(x) =
`RatFunc ℚ`, the fraction-free monic gcd `cgcdFF fuel p q` computes the polynomial gcd of the inputs —
`toPolyG (cgcdFF fuel p q)` is `Associated` to `gcd (toPolyG p) (toPolyG q)` in `(RatFunc ℚ)[X]`. The
`PrimPRSRegular` hypothesis is on the `bdeg`-ordered cleared pair (the same ordering `cgcdFF` uses); it
captures the per-step content-exactness of the primitive PRS, which holds on real runs (validated
pointwise by `native_decide`, Example 3.5.1). -/
theorem associated_toPolyG_cgcdFF (fuel : ℕ) (p q : CPolyG QFunNZ)
    (hreg : PrimPRSRegular fuel
      (if Compute.bdeg (CPolyG.clearDenoms p) < Compute.bdeg (CPolyG.clearDenoms q)
        then CPolyG.clearDenoms q else CPolyG.clearDenoms p)
      (if Compute.bdeg (CPolyG.clearDenoms p) < Compute.bdeg (CPolyG.clearDenoms q)
        then CPolyG.clearDenoms p else CPolyG.clearDenoms q)) :
    Associated (toPolyG (CPolyG.cgcdFF fuel p q)) (gcd (toPolyG p) (toPolyG q)) := by
  have key : ∀ P Q : BPoly, PrimPRSRegular fuel P Q →
      Associated (gcd (toPolyB P) (toPolyB Q)) (gcd (toPolyG p) (toPolyG q)) →
      Associated (toPolyG (CPolyG.cmonicG (CPolyG.liftBPolyToQFunNZ (CPolyG.primPRSgcd fuel P Q))))
        (gcd (toPolyG p) (toPolyG q)) := by
    intro P Q hr hgcd
    refine (associated_toPolyG_cmonicG _).trans ?_
    rw [toPolyG_liftBPolyToQFunNZ]
    exact (associated_toPolyB_primPRSgcd fuel P Q hr).trans hgcd
  have hbridge : Associated (gcd (toPolyB (CPolyG.clearDenoms p)) (toPolyB (CPolyG.clearDenoms q)))
      (gcd (toPolyG p) (toPolyG q)) :=
    (associated_toPolyB_clearDenoms p).gcd (associated_toPolyB_clearDenoms q)
  rw [CPolyG.cgcdFF]
  by_cases hlt : Compute.bdeg (CPolyG.clearDenoms p) < Compute.bdeg (CPolyG.clearDenoms q)
  · simp only [if_pos hlt] at hreg ⊢
    refine key _ _ hreg ?_
    rw [gcd_comm]; exact hbridge
  · simp only [if_neg hlt] at hreg ⊢
    exact key _ _ hreg hbridge

/-! ### Discharging the per-step regularity — content-exactness via the `cgcd`-fold
The `PrimPRSRegular` gate bundles three clauses per step; this section discharges the algorithmically
nontrivial one, **clause (iii) content-exactness** `hrem`, from the proven `cgcd` Bézout/divides theory.
`bcontentX fuel p` folds `cgcdExt fuel` over the `x`-coefficient list of `bnorm p`, so the running gcd
**divides each coefficient** (the divides-down direction of `cgcdExt`, `toPoly_cgcdExt_dvd`, threaded
through the fold). A coefficient divisible by the content has zero `cmod` (`cmod_eq_zero_of_dvd_loc`),
which is exactly `hrem`. The only residual inputs are the genuine algorithmic preconditions: each
`cgcdExt` in the fold terminates within fuel, and the fold fuel bounds each coefficient's length. -/

/-- **Per-step termination of the content `cgcd`-fold** `ContentFoldTerminates fuel acc l`: every
`cgcdExt fuel` Euclidean step in the left fold `l.foldl (fun g c => (cgcdExt fuel g c).1) acc` reaches a
zero remainder within fuel (the same `cgcdTerminates` precondition the gcd-divides direction needs, here
threaded along the running accumulator). The genuine algorithmic precondition of the content fold. -/
def ContentFoldTerminates (fuel : ℕ) : CPoly → List CPoly → Prop
  | _, [] => True
  | acc, c :: l =>
    Compute.cgcdTerminates fuel acc c ∧
      ContentFoldTerminates fuel (Compute.cgcdExt fuel acc c).1 l

/-- **The content `cgcd`-fold divides each input** (over ℚ[x]): for the running gcd
`g = l.foldl (fun g c => (cgcdExt fuel g c).1) acc`, under per-step termination, `toPoly g` divides
`toPoly acc` and `toPoly a` for every `a ∈ l`. The divides-down direction of `cgcdExt`
(`toPoly_cgcdExt_dvd`) carried along the fold: each step's gcd divides the previous accumulator and the
new coefficient, and divisibility transports through the remaining fold. -/
theorem toPoly_foldl_cgcdExt_dvd (fuel : ℕ) :
    ∀ (acc : CPoly) (l : List CPoly), ContentFoldTerminates fuel acc l →
      toPoly (l.foldl (fun g c => (Compute.cgcdExt fuel g c).1) acc) ∣ toPoly acc ∧
        ∀ a ∈ l, toPoly (l.foldl (fun g c => (Compute.cgcdExt fuel g c).1) acc) ∣ toPoly a := by
  intro acc l
  induction l generalizing acc with
  | nil => intro _; exact ⟨dvd_refl _, by simp⟩
  | cons c l ih =>
    intro hterm
    obtain ⟨hstep, hrest⟩ := hterm
    set g₁ := (Compute.cgcdExt fuel acc c).1 with hg₁
    -- the step gcd divides the previous accumulator and the new coefficient
    obtain ⟨hg₁acc, hg₁c⟩ := Compute.toPoly_cgcdExt_dvd fuel acc c hstep
    rw [← hg₁] at hg₁acc hg₁c
    -- the remaining fold (from g₁) divides g₁ and each later coefficient
    obtain ⟨hfg₁, hfmem⟩ := ih g₁ hrest
    have hfold : (c :: l).foldl (fun g c => (Compute.cgcdExt fuel g c).1) acc
        = l.foldl (fun g c => (Compute.cgcdExt fuel g c).1) g₁ := by
      rw [List.foldl_cons]
    rw [hfold]
    refine ⟨hfg₁.trans hg₁acc, ?_⟩
    intro a ha
    rcases List.mem_cons.mp ha with rfl | hl
    · exact hfg₁.trans hg₁c
    · exact hfmem a hl

/-- **The content divides each `x`-coefficient** of `bnorm p` (over ℚ[x]): under per-step termination of
the content `cgcd`-fold, `toPoly (bcontentX fuel p) ∣ toPoly a` for every `a ∈ bnorm p`. The
specialization of `toPoly_foldl_cgcdExt_dvd` to the `[]`-seeded `bcontentX` fold over the coefficient
list of `bnorm p`. -/
theorem toPoly_bcontentX_dvd_mem (fuel : ℕ) (p : BPoly)
    (hterm : ContentFoldTerminates fuel [] (bnorm p)) :
    ∀ a ∈ bnorm p, toPoly (bcontentX fuel p) ∣ toPoly a := by
  have hbc : bcontentX fuel p = (bnorm p).foldl (fun g c => (Compute.cgcdExt fuel g c).1) [] := rfl
  rw [hbc]
  exact (toPoly_foldl_cgcdExt_dvd fuel [] (bnorm p) hterm).2

/-- **Clause (iii) discharged — content-exactness `hrem`**: under per-step termination of the content
`cgcd`-fold and fuel sufficient for each coefficient length, the content `bcontentX fuel p` divides every
`x`-coefficient of `bnorm p` *exactly* (`toPoly (cmod fuel a (bcontentX fuel p)) = 0`). Combines
`toPoly_bcontentX_dvd_mem` (the content divides each coefficient) with `cmod_eq_zero_of_dvd_loc` (a
divisible coefficient has zero computable remainder). This is the crux `hrem` hypothesis of
`associated_toPolyB_bprimitivePartX`, now a theorem on real runs rather than an assumption. -/
theorem hrem_bcontentX (fuel : ℕ) (p : BPoly)
    (hgcn : cnorm (bcontentX fuel p) ≠ [])
    (hfuel : ∀ a ∈ bnorm p, (cnorm a).length ≤ fuel)
    (hterm : ContentFoldTerminates fuel [] (bnorm p)) :
    ∀ a ∈ bnorm p, toPoly (cmod fuel a (bcontentX fuel p)) = 0 := by
  intro a ha
  exact Compute.cmod_eq_zero_of_dvd_loc fuel a (bcontentX fuel p) hgcn (hfuel a ha)
    (toPoly_bcontentX_dvd_mem fuel p hterm a ha)

/-- **`bprimitivePartX` is a ℚ(x)-unit scaling under the algorithmic preconditions** (clause (iii),
self-contained): with the content nonzero (`hg`/`hgcn`/`hg0`), per-step termination of the content
`cgcd`-fold, and fuel sufficient for each coefficient length, `bprimitivePartX fuel p` is `Associated`
to `p` over ℚ(x). Discharges the `hrem` hypothesis of `associated_toPolyB_bprimitivePartX` via
`hrem_bcontentX`, so content stripping is proven a unit scaling on real runs (no `hrem` assumption). -/
theorem associated_toPolyB_bprimitivePartX_of_term (fuel : ℕ) (p : BPoly)
    (hg : ¬ cisZero (bcontentX fuel p) = true) (hgcn : cnorm (bcontentX fuel p) ≠ [])
    (hg0 : toPoly (bcontentX fuel p) ≠ 0)
    (hfuel : ∀ a ∈ bnorm p, (cnorm a).length ≤ fuel)
    (hterm : ContentFoldTerminates fuel [] (bnorm p)) :
    Associated (toPolyB (bprimitivePartX fuel p)) (toPolyB p) :=
  associated_toPolyB_bprimitivePartX fuel p hg hgcn hg0
    (hrem_bcontentX fuel p hgcn hfuel hterm)

/-! ### Discharging clause (ii) — nonzero pseudo-division multiplier
The pseudo-division witness existence is the unconditional `toPolyB_bpsremainder`; clause (ii) additionally
needs the multiplier `amRF (toPoly c)` to be a ℚ(x)-unit (`≠ 0`). The strengthened pseudo-division
identity returns `toPoly c ≠ 0` from a nonzero divisor (the multiplier is a product of leading
`x`-coefficients of the fixed divisor `q`, each nonzero off `bisZero q`), which the field embedding `amRF`
preserves. -/

/-- `bisZero (bnorm q) = bisZero q` (`bnorm` is idempotent, `bisZero p = (bnorm p == [])`). -/
theorem bisZero_bnorm (q : BPoly) : bisZero (bnorm q) = bisZero q := by
  simp only [bisZero, bnorm_idem]

/-- **Strengthened pseudo-division identity through `toBPoly`** (nonzero multiplier): for a nonzero
divisor `q` (`¬ bisZero q`), there are `s, c` with `C (toPoly c) · toBPoly p = toBPoly s · toBPoly q +
toBPoly (bpsremainder fuel p q)` *and* `toPoly c ≠ 0`. Mirrors `Compute.toBPoly_bpsremainder` (the divisor
`q` is fixed through the recursion), tracking that the multiplier `c` is a product of `blc (bnorm q)`
factors and `[1]`, each with nonzero `toPoly` off a zero divisor (`toPoly_blc_ne_zero`). -/
theorem toBPoly_bpsremainder_ne_zero (fuel : ℕ) (p q : BPoly) (hq : ¬ bisZero q = true) :
    ∃ (s : BPoly) (c : CPoly),
      Polynomial.C (toPoly c) * toBPoly p
        = toBPoly s * toBPoly q + toBPoly (bpsremainder fuel p q)
        ∧ toPoly c ≠ 0 := by
  have hblc : toPoly (blc (bnorm q)) ≠ 0 :=
    toPoly_blc_ne_zero (bnorm q) (by rw [bisZero_bnorm]; exact hq)
  induction fuel generalizing p with
  | zero =>
    exact ⟨[], [1], by simp [bpsremainder, toBPoly_bnorm, toPoly_cons], by simp [toPoly_cons]⟩
  | succ fuel ih =>
    simp only [bpsremainder]
    split_ifs with hqz hlen
    · exact ⟨[], [1], by simp [toBPoly_bnorm, toPoly_cons], by simp [toPoly_cons]⟩
    · exact ⟨[], [1], by simp [toBPoly_bnorm, toPoly_cons], by simp [toPoly_cons]⟩
    · obtain ⟨s', c', hsc, hc'0⟩ := ih (bnorm (bsub (bscaleC (blc (bnorm q)) (bnorm p))
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
          cmul c' (blc (bnorm q)), ?_, ?_⟩
      · rw [toBPoly_badd, toBPoly_bscaleC, toBPoly_bshift, toBPoly_one, toPoly_cmul, map_mul,
          toPoly_cmul, map_mul]
        linear_combination hsc
      · rw [toPoly_cmul]
        exact mul_ne_zero hc'0 hblc

/-- **Clause (ii) discharged — nonzero-multiplier pseudo-division witness**: for a nonzero divisor `q`
(`¬ bisZero q`), `bpsremainder` lifts to a ℚ(x)[t] Euclidean relation with the multiplier a ℚ(x)-unit —
there are `s, c` with `C (amRF (toPoly c)) · toPolyB p = toPolyB s · toPolyB q + toPolyB (bpsremainder
fuel p q)` *and* `amRF (toPoly c) ≠ 0`. Strengthens `toPolyB_bpsremainder` (which drops the `≠ 0`) by the
`toBPoly_bpsremainder_ne_zero` certificate; the multiplier `lc(q)^k` is nonzero off a zero divisor. -/
theorem toPolyB_bpsremainder_ne_zero (fuel : ℕ) (p q : BPoly) (hq : ¬ bisZero q = true) :
    ∃ (s : BPoly) (c : CPoly),
      Polynomial.C (amRF (toPoly c)) * toPolyB p
        = toPolyB s * toPolyB q + toPolyB (bpsremainder fuel p q)
        ∧ amRF (toPoly c) ≠ 0 := by
  obtain ⟨s, c, hsc, hc0⟩ := toBPoly_bpsremainder_ne_zero fuel p q hq
  refine ⟨s, c, ?_, amRF_toPoly_ne_zero hc0⟩
  have hl := congrArg liftRF hsc
  simp only [map_add, map_mul] at hl
  rw [liftRF_C] at hl
  simpa [toPolyB] using hl

end DeepWiki.SymbolicIntegration
