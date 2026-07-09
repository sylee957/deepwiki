import DeepWiki.SymbolicIntegration.Engine.Tower.GcdFFCore
import DeepWiki.SymbolicIntegration.Engine.Tower.GcdFF
import DeepWiki.SymbolicIntegration.Engine.FuelFreeGcd
import Mathlib.RingTheory.Polynomial.Content

/-! # Abstract correctness of the generic fraction-free gcd `cgcdFFRawCore` over a tower level
The tower kernel fraction-free gcd `cgcdFFRawCore` over `α = QFunNZG β = Frac(β[s])` computes the
polynomial gcd up to associates. The `gb*Core` engine reads through the bridges `toGBCoeffPoly` (into
`R[X]`, `R = (CFieldSpec.K β)[X]`) and `toGBPolyG` (into `(RatFunc K)[X]`), and each clear-denominators /
Euclidean-step / primitive-part lemma is derived over `GBPolyCore β`. The content recursion is the tower
induction: the content-gcd is the level-`β` `cgcdFFRawCore`, bottoming at the raw Euclidean gcd over ℚ. -/

open Polynomial Classical

namespace DeepWiki.SymbolicIntegration

open CPolyG

/-! ### Generic gcd-step lemmas over an arbitrary field's polynomial ring `F[X]` -/

/-- Pulling one indexed factor out of a `zipIdx`-filtered finite product: filtering out the index-`i`
entry of `ds` and re-multiplying that entry's image recovers the full product of `ds.map f`. -/
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

variable {F : Type*} [Field F]

/-- gcd is invariant under an associated right argument in `F[X]`. -/
theorem associated_gcd_right_field {A B B' : F[X]} (h : Associated B B') :
    Associated (gcd A B) (gcd A B') := by
  apply associated_of_dvd_dvd
  · exact dvd_gcd (gcd_dvd_left A B) ((gcd_dvd_right A B).trans h.dvd)
  · exact dvd_gcd (gcd_dvd_left A B') ((gcd_dvd_right A B').trans h.symm.dvd)

/-- The Euclidean-step gcd invariant in `F[X]`: if `cu` is a unit and `cu · A = R + S · B`
(a pseudo-division step up to the unit content `cu`), then `gcd A B` and `gcd B R` are associates — the
classic invariant `gcd(A,B) = gcd(B, A mod B)` over the field. -/
theorem associated_gcd_euclid_step_field {A B R S cu : F[X]} (hu : IsUnit cu)
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

/-! ### The bivariate bridge `toGBCoeffPoly : GBPolyCore β → R[X]` (`R = (CFieldSpec.K β)[X] = β[s]`)
Read each `t`-coefficient through `toPolyG` and Horner-fold in `t` to get the honest `R[t]` polynomial;
the homomorphism lemmas descend coefficientwise from `toPolyG`'s ring-hom lemmas. -/

namespace GBPolyCore

variable {β : Type*} [CField β] [CFieldSpec β]

/-- Bivariate bridge `toGBCoeffPoly : GBPolyCore β → R[X]` (`R = (CFieldSpec.K β)[X]`): read a
`GBPolyCore β` as an honest `R[t]` polynomial in Horner form, each `t`-coefficient embedded via
`toPolyG`. -/
noncomputable def toGBCoeffPoly : GBPolyCore β → ((CFieldSpec.K β)[X])[X]
  | [] => 0
  | a :: p => Polynomial.C (CPolyG.toPolyG a) + Polynomial.X * toGBCoeffPoly p

/-- `toGBCoeffPoly [] = 0`. -/
@[simp] theorem toGBCoeffPoly_nil : toGBCoeffPoly ([] : GBPolyCore β) = 0 := rfl

/-- `toGBCoeffPoly`'s leading recursion (Horner). -/
@[simp] theorem toGBCoeffPoly_cons (a : CPolyG β) (p : GBPolyCore β) :
    toGBCoeffPoly (a :: p) = Polynomial.C (CPolyG.toPolyG a) + Polynomial.X * toGBCoeffPoly p := rfl

/-- `toGBCoeffPoly` is additive: `gbaddCore` realizes `R[t]` addition. -/
theorem toGBCoeffPoly_gbaddCore (p q : GBPolyCore β) :
    toGBCoeffPoly (gbaddCore p q) = toGBCoeffPoly p + toGBCoeffPoly q := by
  induction p generalizing q with
  | nil => simp [gbaddCore]
  | cons a as ih =>
    cases q with
    | nil => simp [gbaddCore]
    | cons b bs =>
      simp only [gbaddCore, toGBCoeffPoly_cons, ih bs, denote, map_add]
      ring

/-- `toGBCoeffPoly` is negation-compatible: `gbnegCore` realizes `R[t]` negation. -/
theorem toGBCoeffPoly_gbnegCore (p : GBPolyCore β) :
    toGBCoeffPoly (gbnegCore p) = - toGBCoeffPoly p := by
  induction p with
  | nil => simp [gbnegCore]
  | cons a as ih =>
    show toGBCoeffPoly (CPolyG.cnegG a :: gbnegCore as) = _
    simp only [toGBCoeffPoly_cons, denote, map_neg, ih]
    ring

/-- `toGBCoeffPoly` is subtraction-compatible: `gbsubCore` realizes `R[t]` subtraction. -/
theorem toGBCoeffPoly_gbsubCore (p q : GBPolyCore β) :
    toGBCoeffPoly (gbsubCore p q) = toGBCoeffPoly p - toGBCoeffPoly q := by
  simp [gbsubCore, toGBCoeffPoly_gbaddCore, toGBCoeffPoly_gbnegCore, sub_eq_add_neg]

/-- `toGBCoeffPoly` realizes scaling by a `β[s]` coefficient: `gbscaleCCore c p` is
`C (toPolyG c) · toGBCoeffPoly p`. -/
theorem toGBCoeffPoly_gbscaleCCore (c : CPolyG β) (p : GBPolyCore β) :
    toGBCoeffPoly (gbscaleCCore c p) = Polynomial.C (CPolyG.toPolyG c) * toGBCoeffPoly p := by
  induction p with
  | nil => simp [gbscaleCCore]
  | cons a as ih =>
    show toGBCoeffPoly (CPolyG.cmulG c a :: gbscaleCCore c as) = _
    simp only [toGBCoeffPoly_cons, denote, map_mul, ih]
    ring

/-- `toGBCoeffPoly` realizes the `t`-shift: `gbshiftCore k p` is `tᵏ · toGBCoeffPoly p`. -/
theorem toGBCoeffPoly_gbshiftCore (k : ℕ) (p : GBPolyCore β) :
    toGBCoeffPoly (gbshiftCore k p) = Polynomial.X ^ k * toGBCoeffPoly p := by
  induction k with
  | zero => simp [gbshiftCore]
  | succ n ih =>
    show toGBCoeffPoly ([] :: gbshiftCore n p) = _
    simp only [toGBCoeffPoly_cons, toPolyG_nil, map_zero, ih]
    ring

omit [CFieldSpec β] in
/-- `gbnormCore [] = []`. -/
@[simp] theorem gbnormCore_nil : gbnormCore ([] : GBPolyCore β) = [] := rfl

omit [CFieldSpec β] in
/-- `gbnormCore` on a cons cell, unfolded to its defining `match` (definitional). -/
theorem gbnormCore_cons_eq (a : CPolyG β) (as : GBPolyCore β) :
    gbnormCore (a :: as)
      = (match gbnormCore as with
          | [] => if CPolyG.cisZeroG (CPolyG.cnormG a) then [] else [CPolyG.cnormG a]
          | r => CPolyG.cnormG a :: r) := rfl

omit [CFieldSpec β] in
/-- `gbnormCore` is idempotent. -/
@[simp] theorem gbnormCore_idemp (p : GBPolyCore β) : gbnormCore (gbnormCore p) = gbnormCore p := by
  induction p with
  | nil => rfl
  | cons a as ih =>
    rw [gbnormCore_cons_eq]
    cases h : gbnormCore as with
    | nil => cases ha : CPolyG.cisZeroG (CPolyG.cnormG a) <;> simp [gbnormCore_cons_eq, cnormG_idem, ha]
    | cons b bs =>
      rw [h] at ih
      simp only [gbnormCore_cons_eq, cnormG_idem, ih]

/-- `toGBCoeffPoly` ignores normalization: `toGBCoeffPoly (gbnormCore p) = toGBCoeffPoly p`. -/
@[simp] theorem toGBCoeffPoly_gbnormCore (p : GBPolyCore β) :
    toGBCoeffPoly (gbnormCore p) = toGBCoeffPoly p := by
  induction p with
  | nil => rfl
  | cons a as ih =>
    rw [gbnormCore_cons_eq]
    cases h : gbnormCore as with
    | nil =>
      rw [h] at ih
      simp only [toGBCoeffPoly_nil] at ih
      have has : toGBCoeffPoly as = 0 := ih.symm
      cases ha : CPolyG.cisZeroG (CPolyG.cnormG a) with
      | true =>
        have hpa : CPolyG.toPolyG a = 0 := by
          have hca : CPolyG.cnormG a = [] := by simpa [CPolyG.cisZeroG, cnormG_idem] using ha
          exact (cnormG_eq_nil_iff _).mp hca
        simp [toGBCoeffPoly_cons, hpa, has]
      | false => simp [toGBCoeffPoly_cons, toPolyG_cnormG, has]
    | cons b bs =>
      rw [h] at ih
      simp only [toGBCoeffPoly_cons, denote, ih]

/-- `(toGBCoeffPoly p).coeff i = toPolyG (p.getD i [])`: the Horner bridge realizes the dense
`t`-coefficient list. -/
theorem toGBCoeffPoly_coeff (p : GBPolyCore β) (i : ℕ) :
    (toGBCoeffPoly p).coeff i = CPolyG.toPolyG (p.getD i ([] : CPolyG β)) := by
  induction p generalizing i with
  | nil => simp [toPolyG_nil]
  | cons a as ih =>
    rw [toGBCoeffPoly_cons]
    cases i with
    | zero => simp [coeff_C]
    | succ n => simp [coeff_X_mul, ih]

/-- The last coefficient of `gbnormCore p` reads to a nonzero `R = (CFieldSpec.K β)[X]`. -/
theorem gbnormCore_getLast?_toPolyG_ne_zero (p : GBPolyCore β) :
    ∀ v, (gbnormCore p).getLast? = some v → CPolyG.toPolyG v ≠ 0 := by
  induction p with
  | nil => simp
  | cons a as ih =>
    rw [gbnormCore_cons_eq]
    cases h : gbnormCore as with
    | nil =>
      cases ha : CPolyG.cisZeroG (CPolyG.cnormG a) with
      | true => rw [if_pos rfl]; simp
      | false =>
        intro v hv
        rw [if_neg (by simp), List.getLast?_singleton, Option.some.injEq] at hv
        subst hv
        simp only [denote]
        intro hz
        have hca : CPolyG.cnormG a = [] := (cnormG_eq_nil_iff a).mpr hz
        rw [CPolyG.cisZeroG, hca] at ha
        simp at ha
    | cons b bs =>
      rw [h] at ih
      intro v hv
      rw [List.getLast?_cons_cons] at hv
      exact ih v hv

/-- `gblcCore` is the `t`-coefficient at the top index: `toPolyG (gblcCore p) =
(toGBCoeffPoly p).coeff (gbdegCore p)`. -/
theorem toPolyG_gblcCore_eq_coeff (p : GBPolyCore β) :
    CPolyG.toPolyG (gblcCore p) = (toGBCoeffPoly p).coeff (gbdegCore p) := by
  rw [gblcCore, gbdegCore, ← toGBCoeffPoly_gbnormCore, toGBCoeffPoly_coeff,
    List.getD_eq_getElem?_getD, ← List.getLast?_eq_getElem?]

/-- `gbisZeroCore p = true ↔ toGBCoeffPoly p = 0`. -/
theorem gbisZeroCore_iff_toGBCoeffPoly (p : GBPolyCore β) :
    gbisZeroCore p = true ↔ toGBCoeffPoly p = 0 := by
  rw [gbisZeroCore, List.isEmpty_iff]
  constructor
  · intro h; rw [← toGBCoeffPoly_gbnormCore, h, toGBCoeffPoly_nil]
  · intro h
    rcases hb : gbnormCore p with _ | ⟨c, cs⟩
    · rfl
    · exfalso
      have hne : (gbnormCore p).getLast? ≠ none := by rw [hb]; simp
      rcases hg : (gbnormCore p).getLast? with _ | v
      · exact hne hg
      · have hv := gbnormCore_getLast?_toPolyG_ne_zero p v hg
        have hlc : gblcCore p = v := by rw [gblcCore, hg, Option.getD_some]
        have hcoeff0 : CPolyG.toPolyG (gblcCore p) = 0 := by
          rw [toPolyG_gblcCore_eq_coeff, h]; simp
        rw [hlc] at hcoeff0
        exact hv hcoeff0

end GBPolyCore

/-! ### The field-coefficient lift `R[t] → (RatFunc K)[t]` and `toGBPolyG` -/

open QFunNZG in
/-- The coefficient-ring lift `R[t] → (RatFunc K)[t]`, applying `amG β` to every `t`-coefficient. -/
noncomputable abbrev liftKG (β : Type*) [CField β] [CFieldSpec β] :
    ((CFieldSpec.K β)[X])[X] →+* (RatFunc (CFieldSpec.K β))[X] :=
  Polynomial.mapRingHom (QFunNZG.amG β)

/-- `toGBPolyG p`: the `β(s)[t]` reading of a `GBPolyCore β`, `toGBCoeffPoly p` lifted through the
coefficient embedding `amG β` into `(RatFunc (CFieldSpec.K β))[X]`. -/
noncomputable def toGBPolyG {β : Type*} [CField β] [CFieldSpec β] (p : GBPolyCore β) :
    (RatFunc (CFieldSpec.K β))[X] :=
  liftKG β (GBPolyCore.toGBCoeffPoly p)

variable {β : Type*} [CField β] [CFieldSpec β]

/-- `toGBPolyG [] = 0`. -/
@[simp, denote] theorem toGBPolyG_nil : toGBPolyG ([] : GBPolyCore β) = 0 := by simp [toGBPolyG]

/-- `liftKG (C c) = C (amG c)`: the lift sends a constant `β[s]`-coefficient to its `β(s)` embedding. -/
theorem liftKG_C (c : (CFieldSpec.K β)[X]) :
    liftKG β (Polynomial.C c) = Polynomial.C (QFunNZG.amG β c) := by
  simp [liftKG, Polynomial.coe_mapRingHom, Polynomial.map_C]

/-- `toPolyG (liftGBPolyCoreG p) = toGBPolyG p`: lifting coefficientwise as `c/1` then through `toPolyG`
agrees with the coefficient-ring embedding. -/
@[denote] theorem toPolyG_liftGBPolyCoreG (p : GBPolyCore β) :
    toPolyG (CPolyG.liftGBPolyCoreG p) = toGBPolyG p := by
  apply Polynomial.ext
  intro i
  rw [toGBPolyG, liftKG, Polynomial.coe_mapRingHom, Polynomial.coeff_map,
    GBPolyCore.toGBCoeffPoly_coeff, toPolyG_coeff, CPolyG.liftGBPolyCoreG,
    List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : p[i]? with
  | none => simp [CFieldSpec.toK_zero, toPolyG_nil, map_zero]
  | some c =>
    simp only [Option.map_some, Option.getD_some]
    show QFunNZG.toQFunNZG _ = QFunNZG.amG β (CPolyG.toPolyG c)
    rw [QFunNZG.toQFunNZG]
    have h1 : CPolyG.toPolyG ([CField.one] : CPolyG β) = 1 := by
      simp only [denote, mul_zero, add_zero, map_one]
    show QFunNZG.amG β (CPolyG.toPolyG c) / QFunNZG.amG β (CPolyG.toPolyG ([CField.one] : CPolyG β))
      = QFunNZG.amG β (CPolyG.toPolyG c)
    rw [h1, map_one, div_one]

/-! ### The `cclearDenomsCoreG` bridge `β(s)[t] ↔ (β[s])[t]`
Read back over `β(s)`, the cleared polynomial equals `C s · toPolyG p` for the common-denominator unit
`s = ∏_j denⱼ`, hence is `Associated` to `toPolyG p`; the combinatorics reuse `filter_prod_mul`. -/

variable [CFieldDomain β]

omit [CFieldDomain β] in
/-- A `QFunNZG β` coefficient reads as `amG (toPolyG num) / amG (toPolyG den)` in `RatFunc (CFieldSpec.K
β)`. -/
theorem toQFunNZG_eq_div (c : QFunNZG β) :
    QFunNZG.toQFunNZG c
      = QFunNZG.amG β (CPolyG.toPolyG (CPolyG.qnumCoeffCoreG c))
        / QFunNZG.amG β (CPolyG.toPolyG (CPolyG.qdenCoeffCoreG c)) := by
  obtain ⟨⟨a, b⟩, hb⟩ := c; rfl

omit [CFieldDomain β] in
/-- A `QFunNZG β` coefficient's denominator has nonzero `toPolyG` (by subtype membership
`cisZeroG _ = false`). -/
theorem toPolyG_qdenCoeffCoreG_ne_zero (c : QFunNZG β) :
    CPolyG.toPolyG (CPolyG.qdenCoeffCoreG c) ≠ 0 := by
  obtain ⟨⟨a, b⟩, hb⟩ := c
  exact QFunNZG.toPolyG_ne_zero_of_cisZeroG_false hb

/-- The common-denominator scalar `commonDenG p ∈ R`: the product of all the `β[s]`-denominators of `p`'s
coefficients, the unit by which `cclearDenomsCoreG` scales `toPolyG p`. -/
noncomputable def commonDenG (p : CPolyG (QFunNZG β)) : (CFieldSpec.K β)[X] :=
  ((p.map CPolyG.qdenCoeffCoreG).map CPolyG.toPolyG).prod

omit [CFieldDomain β] in
/-- `commonDenG p ≠ 0`: a product of nonzero denominators. -/
theorem commonDenG_ne_zero (p : CPolyG (QFunNZG β)) : commonDenG p ≠ 0 := by
  rw [commonDenG]
  refine List.prod_ne_zero ?_
  intro hmem
  rw [List.mem_map] at hmem
  obtain ⟨d, hd, hd0⟩ := hmem
  rw [List.mem_map] at hd
  obtain ⟨c, hc, rfl⟩ := hd
  exact toPolyG_qdenCoeffCoreG_ne_zero c hd0

omit [CFieldDomain β] in
/-- `amG (commonDenG p) ≠ 0` (the field embedding of a nonzero product). -/
theorem amG_commonDenG_ne_zero (p : CPolyG (QFunNZG β)) : QFunNZG.amG β (commonDenG p) ≠ 0 :=
  (map_ne_zero_iff _ (RatFunc.algebraMap_injective (CFieldSpec.K β))).mpr (commonDenG_ne_zero p)

omit [CFieldDomain β] in
/-- `toPolyG` of a `cmulG`-fold is `toPolyG init` times the product of the `toPolyG`-images of the folded
list. -/
@[denote] theorem toPolyG_foldl_cmulG (init : CPolyG β) (ds : List (CPolyG β × ℕ)) :
    CPolyG.toPolyG (ds.foldl (fun acc de => CPolyG.cmulG acc de.1) init)
      = CPolyG.toPolyG init * (ds.map (fun de => CPolyG.toPolyG de.1)).prod := by
  induction ds generalizing init with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, ih, denote, List.map_cons, List.prod_cons]; ring

omit [CFieldSpec β] in
/-- The `i`-th cleared coefficient of `cclearDenomsCoreG p` (in range) is `numᵢ · (∏_{j≠i} denⱼ)`. -/
theorem cclearDenomsCoreG_getElem (p : CPolyG (QFunNZG β)) (i : ℕ) (hi : i < p.length) :
    (CPolyG.cclearDenomsCoreG p)[i]? = some (CPolyG.cmulG (CPolyG.qnumCoeffCoreG (p.getD i CField.zero))
      ((((p.map CPolyG.qdenCoeffCoreG).zipIdx).filter (fun de => decide (de.2 ≠ i))).foldl
        (fun acc de => CPolyG.cmulG acc de.1) [CField.one])) := by
  unfold CPolyG.cclearDenomsCoreG
  simp only
  rw [List.getElem?_map, List.getElem?_zipIdx, List.getElem?_eq_getElem hi]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

omit [CFieldSpec β] [CFieldDomain β] in
/-- `cclearDenomsCoreG` preserves the `t`-length: `(cclearDenomsCoreG p).length = p.length`. -/
theorem cclearDenomsCoreG_length (p : CPolyG (QFunNZG β)) :
    (CPolyG.cclearDenomsCoreG p).length = p.length := by
  unfold CPolyG.cclearDenomsCoreG; simp

/-- `toPolyG p` vanishes past the list length (the out-of-range coefficient is `CField.zero = 0`). -/
theorem toPolyG_coeff_eq_zero_of_length_leG (p : CPolyG (QFunNZG β)) {i : ℕ} (hi : p.length ≤ i) :
    (toPolyG p).coeff i = 0 := by
  rw [toPolyG_coeff, List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
  show CFieldSpec.toK (CField.zero : QFunNZG β) = 0
  rw [CFieldSpec.toK_zero]

/-- `(toGBPolyG (cclearDenomsCoreG p)).coeff i = amG (commonDenG p) · (toPolyG p).coeff i`. -/
theorem toGBPolyG_cclearDenomsCoreG_coeff (p : CPolyG (QFunNZG β)) (i : ℕ) :
    (toGBPolyG (CPolyG.cclearDenomsCoreG p)).coeff i
      = QFunNZG.amG β (commonDenG p) * (toPolyG p).coeff i := by
  rcases lt_or_ge i p.length with hi | hi
  · rw [toGBPolyG, liftKG, Polynomial.coe_mapRingHom, Polynomial.coeff_map,
      GBPolyCore.toGBCoeffPoly_coeff, toPolyG_coeff,
      List.getD_eq_getElem?_getD, cclearDenomsCoreG_getElem p i hi, Option.getD_some]
    simp only [denote,
      show CPolyG.toPolyG ([CField.one] : CPolyG β) = 1 by
        simp only [denote, mul_zero, add_zero, map_one],
      one_mul]
    set dens := p.map CPolyG.qdenCoeffCoreG with hdens
    have hcd : commonDenG p = (dens.map CPolyG.toPolyG).prod := by rw [commonDenG, hdens]
    have hlen : i < dens.length := by rw [hdens, List.length_map]; exact hi
    have hfilt := filter_prod_mul (CPolyG.toPolyG) ([] : CPolyG β) dens 0 i (Nat.zero_le i)
      (by simpa using hlen)
    rw [Nat.sub_zero] at hfilt
    have hdeni : CPolyG.toPolyG (dens.getD i []) = CPolyG.toPolyG (CPolyG.qdenCoeffCoreG (p.getD i CField.zero)) := by
      congr 1
      rw [hdens, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hi]
      simp
    have hcoeff : (CFieldSpec.toK (p.getD i CField.zero) : RatFunc (CFieldSpec.K β))
        = QFunNZG.amG β (CPolyG.toPolyG (CPolyG.qnumCoeffCoreG (p.getD i CField.zero)))
          / QFunNZG.amG β (CPolyG.toPolyG (CPolyG.qdenCoeffCoreG (p.getD i CField.zero))) := by
      show QFunNZG.toQFunNZG (p.getD i CField.zero) = _
      rw [toQFunNZG_eq_div]
    have hden0 : QFunNZG.amG β (CPolyG.toPolyG (CPolyG.qdenCoeffCoreG (p.getD i CField.zero))) ≠ 0 :=
      QFunNZG.amG_toPolyG_ne_zero (toPolyG_qdenCoeffCoreG_ne_zero _)
    rw [hcoeff, hcd]
    have hpushP : QFunNZG.amG β (((dens.zipIdx.filter (fun de => decide (de.2 ≠ i))).map
        (fun de => CPolyG.toPolyG de.1)).prod)
        * QFunNZG.amG β (CPolyG.toPolyG (CPolyG.qdenCoeffCoreG (p.getD i CField.zero)))
        = QFunNZG.amG β ((dens.map CPolyG.toPolyG).prod) := by
      rw [← map_mul, ← hdeni, hfilt]
    rw [map_mul, mul_comm (QFunNZG.amG β ((dens.map CPolyG.toPolyG).prod)) _, div_mul_eq_mul_div,
      eq_div_iff hden0, mul_assoc, hpushP]
  · rw [toGBPolyG, liftKG, Polynomial.coe_mapRingHom, Polynomial.coeff_map,
      GBPolyCore.toGBCoeffPoly_coeff, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by rw [cclearDenomsCoreG_length]; exact hi), Option.getD_none,
      toPolyG_nil, map_zero, toPolyG_coeff_eq_zero_of_length_leG p hi, mul_zero]

/-- `toGBPolyG (cclearDenomsCoreG p) = C (amG (commonDenG p)) * toPolyG p` over β(s). -/
theorem toGBPolyG_cclearDenomsCoreG (p : CPolyG (QFunNZG β)) :
    toGBPolyG (CPolyG.cclearDenomsCoreG p) = Polynomial.C (QFunNZG.amG β (commonDenG p)) * toPolyG p := by
  ext i
  rw [toGBPolyG_cclearDenomsCoreG_coeff, Polynomial.coeff_C_mul]

/-- `Associated (toGBPolyG (cclearDenomsCoreG p)) (toPolyG p)`: fraction-clearing is a β(s)-unit
scaling, preserving the gcd up to associates. -/
theorem associated_toGBPolyG_cclearDenomsCoreG (p : CPolyG (QFunNZG β)) :
    Associated (toGBPolyG (CPolyG.cclearDenomsCoreG p)) (toPolyG p) := by
  rw [toGBPolyG_cclearDenomsCoreG]
  exact (associated_unit_mul_left _ _
    (Polynomial.isUnit_C.mpr (amG_commonDenG_ne_zero p).isUnit))

/-! ### The primitive PRS over the GCD-domain coefficient ring `R = β[s]`
Over β(s), each `cprimPRSgcdGenCore` step preserves the gcd up to associates: a pseudo-remainder is a
Euclidean step up to a β(s)-unit multiplier, and the content-strip divides out a β(s)-unit content. The
per-step regularity facts enter as the `CPrimPRSGenAssocReg` hypothesis bundle. -/

namespace GBPolyCore

variable {β : Type*} [CField β] [CFieldSpec β]

omit [CFieldSpec β] in
/-- `gbpsremainderCore` normalizes its divisor: `gbpsremainderCore fuel p q = gbpsremainderCore fuel p
(gbnormCore q)`. Mirror of `bpsremainder_bnorm_right`. -/
theorem gbpsremainderCore_gbnormCore_right (fuel : ℕ) (p q : GBPolyCore β) :
    gbpsremainderCore fuel p q = gbpsremainderCore fuel p (gbnormCore q) := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp only [gbpsremainderCore, gbnormCore_idemp]

/-- `toGBCoeffPoly [[CField.one]] = 1`: the `GBPolyCore` constant `1`. -/
@[simp] theorem toGBCoeffPoly_one : toGBCoeffPoly ([[CField.one]] : GBPolyCore β) = 1 := by
  rw [toGBCoeffPoly_cons, toGBCoeffPoly_nil, mul_zero, add_zero,
    show CPolyG.toPolyG ([CField.one] : CPolyG β) = 1 by
      simp only [denote, mul_zero, add_zero, map_one], map_one]

/-- Pseudo-division identity through `toGBCoeffPoly`: there exist a multiplier `c ∈ β[s]` and quotient
`s` with `C (toPolyG c) · toGBCoeffPoly p = toGBCoeffPoly s · toGBCoeffPoly q +
toGBCoeffPoly (gbpsremainderCore fuel p q)` in `R[t]`. -/
theorem toGBCoeffPoly_gbpsremainderCore (fuel : ℕ) (p q : GBPolyCore β) :
    ∃ (s : GBPolyCore β) (c : CPolyG β),
      Polynomial.C (CPolyG.toPolyG c) * toGBCoeffPoly p
        = toGBCoeffPoly s * toGBCoeffPoly q + toGBCoeffPoly (gbpsremainderCore fuel p q) := by
  have hone : CPolyG.toPolyG ([CField.one] : CPolyG β) = 1 := by
    simp only [denote, mul_zero, add_zero, map_one]
  induction fuel generalizing p with
  | zero => exact ⟨[], [CField.one], by simp [gbpsremainderCore, toGBCoeffPoly_gbnormCore, hone]⟩
  | succ fuel ih =>
    simp only [gbpsremainderCore]
    split_ifs with hq hlen
    · exact ⟨[], [CField.one], by simp [toGBCoeffPoly_gbnormCore, hone]⟩
    · exact ⟨[], [CField.one], by simp [toGBCoeffPoly_gbnormCore, hone]⟩
    · obtain ⟨s', c', hsc⟩ := ih (gbnormCore (gbsubCore (gbscaleCCore (gblcCore (gbnormCore q)) (gbnormCore p))
        (gbscaleCCore (gblcCore (gbnormCore p))
          (gbshiftCore ((gbnormCore p).length - (gbnormCore q).length) (gbnormCore q)))))
      have hp' : toGBCoeffPoly (gbnormCore (gbsubCore (gbscaleCCore (gblcCore (gbnormCore q)) (gbnormCore p))
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
          CPolyG.cmulG c' (gblcCore (gbnormCore q)), ?_⟩
      simp only [toGBCoeffPoly_gbaddCore, toGBCoeffPoly_gbscaleCCore, toGBCoeffPoly_gbshiftCore,
        toGBCoeffPoly_one, denote, map_mul]
      linear_combination hsc

end GBPolyCore

open GBPolyCore

omit [CFieldDomain β] in
/-- The β(s)[t] lift of the pseudo-division identity: `C (amG (toPolyG c)) · toGBPolyG p = toGBPolyG s ·
toGBPolyG q + toGBPolyG (gbpsremainderCore fuel p q)` for some quotient `s` and multiplier `c`. -/
theorem toGBPolyG_gbpsremainderCore (fuel : ℕ) (p q : GBPolyCore β) :
    ∃ (s : GBPolyCore β) (c : CPolyG β),
      Polynomial.C (QFunNZG.amG β (CPolyG.toPolyG c)) * toGBPolyG p
        = toGBPolyG s * toGBPolyG q + toGBPolyG (gbpsremainderCore fuel p q) := by
  obtain ⟨s, c, hsc⟩ := toGBCoeffPoly_gbpsremainderCore fuel p q
  refine ⟨s, c, ?_⟩
  have hl := congrArg (liftKG β) hsc
  simp only [map_add, map_mul] at hl
  rw [liftKG_C] at hl
  simpa [toGBPolyG] using hl

omit [CFieldDomain β] in
/-- `toGBPolyG` ignores normalization: `toGBPolyG (gbnormCore p) = toGBPolyG p`. -/
@[simp, denote] theorem toGBPolyG_gbnormCore (p : GBPolyCore β) :
    toGBPolyG (gbnormCore p) = toGBPolyG p := by
  rw [toGBPolyG, toGBCoeffPoly_gbnormCore, ← toGBPolyG]

omit [CFieldDomain β] in
/-- `toGBPolyG p = 0 ↔ toGBCoeffPoly p = 0` (the lift is injective, `amG` injective on coefficients). -/
theorem toGBPolyG_eq_zero_iff (p : GBPolyCore β) : toGBPolyG p = 0 ↔ toGBCoeffPoly p = 0 := by
  rw [toGBPolyG, liftKG, ← Polynomial.map_zero (QFunNZG.amG β)]
  exact Polynomial.map_injective (QFunNZG.amG β) (RatFunc.algebraMap_injective (CFieldSpec.K β)) |>.eq_iff

omit [CFieldDomain β] in
/-- `toGBPolyG p = 0 ↔ gbisZeroCore p = true`. -/
theorem toGBPolyG_eq_zero_iff_gbisZeroCore (p : GBPolyCore β) :
    toGBPolyG p = 0 ↔ gbisZeroCore p = true := by
  rw [toGBPolyG_eq_zero_iff, gbisZeroCore_iff_toGBCoeffPoly]

/-! ### Step 2 — the primitive-PRS gcd invariant over β(s) -/

omit [CFieldDomain β] in
/-- gcd is invariant under an associated right argument in `(RatFunc (CFieldSpec.K β))[X]`. -/
theorem associated_gcd_right_gbpolyG {A B B' : (RatFunc (CFieldSpec.K β))[X]} (h : Associated B B') :
    Associated (gcd A B) (gcd A B') :=
  associated_gcd_right_field h

/-- Per-run regularity `CPrimPRSGenAssocReg cgcdB fuel P Q`: the inductive predicate collecting what each
`cprimPRSgcdGenCore` step's gcd invariant needs — (i) termination `gbisZeroCore Q = true`, (ii) a
pseudo-division witness with β(s)-unit multiplier, and (iii) `gbprimitivePartCore` a β(s)-unit scaling. -/
def CPrimPRSGenAssocReg (cgcdB : CPolyG β → CPolyG β → CPolyG β) :
    ℕ → GBPolyCore β → GBPolyCore β → Prop
  | 0, P, Q =>
    gbisZeroCore Q = true ∧
      Associated (toGBPolyG (GBPolyCore.gbprimitivePartCore cgcdB P)) (toGBPolyG P)
  | fuel + 1, P, Q =>
    (gbisZeroCore (GBPolyCore.gbnormCore Q) = true ∧
      Associated (toGBPolyG (GBPolyCore.gbprimitivePartCore cgcdB (GBPolyCore.gbnormCore P)))
        (toGBPolyG P)) ∨
      (¬ gbisZeroCore (GBPolyCore.gbnormCore Q) = true ∧
        (∃ (s : GBPolyCore β) (c : CPolyG β),
          Polynomial.C (QFunNZG.amG β (CPolyG.toPolyG c)) * toGBPolyG (GBPolyCore.gbnormCore P)
            = toGBPolyG s * toGBPolyG (GBPolyCore.gbnormCore Q)
              + toGBPolyG (GBPolyCore.gbpsremainderCore 60 (GBPolyCore.gbnormCore P)
                  (GBPolyCore.gbnormCore Q))
          ∧ QFunNZG.amG β (CPolyG.toPolyG c) ≠ 0) ∧
        Associated (toGBPolyG (GBPolyCore.gbprimitivePartCore cgcdB
            (GBPolyCore.gbpsremainderCore 60 (GBPolyCore.gbnormCore P) (GBPolyCore.gbnormCore Q))))
          (toGBPolyG (GBPolyCore.gbpsremainderCore 60 (GBPolyCore.gbnormCore P)
              (GBPolyCore.gbnormCore Q))) ∧
        CPrimPRSGenAssocReg cgcdB fuel (GBPolyCore.gbnormCore Q)
          (GBPolyCore.gbprimitivePartCore cgcdB
            (GBPolyCore.gbpsremainderCore 60 (GBPolyCore.gbnormCore P) (GBPolyCore.gbnormCore Q))))

omit [CFieldDomain β] in
/-- The primitive-PRS gcd invariant: for a regular run, `Associated (toGBPolyG (cprimPRSgcdGenCore cgcdB
fuel P Q)) (gcd (toGBPolyG P) (toGBPolyG Q))` over β(s). -/
theorem associated_toGBPolyG_cprimPRSgcdGenCore (cgcdB : CPolyG β → CPolyG β → CPolyG β) :
    ∀ (fuel : ℕ) (P Q : GBPolyCore β), CPrimPRSGenAssocReg cgcdB fuel P Q →
      Associated (toGBPolyG (cprimPRSgcdGenCore cgcdB fuel P Q))
        (gcd (toGBPolyG P) (toGBPolyG Q)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro P Q hreg
    obtain ⟨hQ, hprim⟩ := hreg
    have hQ0 : toGBPolyG Q = 0 := (toGBPolyG_eq_zero_iff_gbisZeroCore Q).mpr hQ
    show Associated (toGBPolyG (GBPolyCore.gbprimitivePartCore cgcdB P))
      (gcd (toGBPolyG P) (toGBPolyG Q))
    rw [hQ0]
    exact hprim.trans (gcd_zero_right' (toGBPolyG P)).symm
  | succ fuel ih =>
    intro P Q hreg
    show Associated (toGBPolyG (
        let P := GBPolyCore.gbnormCore P; let Q := GBPolyCore.gbnormCore Q;
        if GBPolyCore.gbisZeroCore Q then GBPolyCore.gbprimitivePartCore cgcdB P
        else cprimPRSgcdGenCore cgcdB fuel Q
          (GBPolyCore.gbprimitivePartCore cgcdB (GBPolyCore.gbpsremainderCore 60 P Q))))
      (gcd (toGBPolyG P) (toGBPolyG Q))
    simp only
    by_cases hQ : GBPolyCore.gbisZeroCore (GBPolyCore.gbnormCore Q) = true
    · rw [if_pos hQ]
      rw [CPrimPRSGenAssocReg] at hreg
      rcases hreg with ⟨_, hprim⟩ | ⟨hne, _⟩
      · have hQ0 : toGBPolyG Q = 0 := by
          rw [← toGBPolyG_gbnormCore]; exact (toGBPolyG_eq_zero_iff_gbisZeroCore _).mpr hQ
        rw [hQ0]
        exact hprim.trans (gcd_zero_right' (toGBPolyG P)).symm
      · exact absurd hQ hne
    · rw [if_neg hQ]
      rw [CPrimPRSGenAssocReg] at hreg
      rcases hreg with ⟨h, _⟩ | ⟨_, ⟨s, c, hrel, hc0⟩, hassoc, hrec⟩
      · exact absurd h hQ
      set Pn := GBPolyCore.gbnormCore P with hPn
      set Qn := GBPolyCore.gbnormCore Q with hQn
      set prem := GBPolyCore.gbpsremainderCore 60 Pn Qn with hprem
      set r := GBPolyCore.gbprimitivePartCore cgcdB prem with hr
      have hih := ih Qn r hrec
      have hstep : Associated (gcd (toGBPolyG Pn) (toGBPolyG Qn))
          (gcd (toGBPolyG Qn) (toGBPolyG r)) := by
        have heuc : Associated (gcd (toGBPolyG Pn) (toGBPolyG Qn))
            (gcd (toGBPolyG Qn) (toGBPolyG prem)) :=
          associated_gcd_euclid_step_field (A := toGBPolyG Pn) (B := toGBPolyG Qn)
            (R := toGBPolyG prem) (S := toGBPolyG s)
            (Polynomial.isUnit_C.mpr hc0.isUnit) (by linear_combination hrel)
        exact heuc.trans (associated_gcd_right_gbpolyG hassoc.symm)
      rw [show toGBPolyG P = toGBPolyG Pn by rw [hPn, toGBPolyG_gbnormCore],
        show toGBPolyG Q = toGBPolyG Qn by rw [hQn, toGBPolyG_gbnormCore]]
      exact hih.trans hstep.symm

/-! ### Discharging clause (iii) — the content strip is a β(s)-unit scaling
When the content divides every `t`-coefficient (from the gcd-correctness of `cgcdB`, the tower
induction), `gbprimitivePartCore cgcdB prem` is exact division, i.e. a β(s)-unit scaling. -/

namespace GBPolyCore

variable {β : Type*} [CField β] [CFieldSpec β]

omit [CFieldSpec β] in
/-- The `t`-content `gbcontentCore cgcdB p` is invariant under `gbnormCore`:
`gbcontentCore cgcdB (gbnormCore p) = gbcontentCore cgcdB p`. -/
theorem gbcontentCore_gbnormCore (cgcdB : CPolyG β → CPolyG β → CPolyG β) (p : GBPolyCore β) :
    gbcontentCore cgcdB (gbnormCore p) = gbcontentCore cgcdB p := by
  rw [gbcontentCore, gbcontentCore, gbnormCore_idemp]

/-- If the content `g` divides every `t`-coefficient of `p` exactly, then `C(toPolyG g) · toGBCoeffPoly
(p.map (cdivWf · g)) = toGBCoeffPoly p`. -/
theorem toGBCoeffPoly_map_cdivWf_exact (p : GBPolyCore β) (g : CPolyG β)
    (hg : CPolyG.cnormG g ≠ [])
    (hdvd : ∀ a ∈ p, CPolyG.toPolyG g ∣ CPolyG.toPolyG a) :
    Polynomial.C (CPolyG.toPolyG g) * toGBCoeffPoly (p.map (fun a => CPolyG.cdivWf a g))
      = toGBCoeffPoly p := by
  induction p with
  | nil => simp
  | cons a as ih =>
    have has := ih (fun b hb => hdvd b (by simp [hb]))
    have ha : CPolyG.toPolyG a = CPolyG.toPolyG (CPolyG.cdivWf a g) * CPolyG.toPolyG g :=
      (toPolyG_cdivWf_exact a g hg (hdvd a (by simp))).symm
    rw [List.map_cons, toGBCoeffPoly_cons, toGBCoeffPoly_cons, ha, map_mul]
    linear_combination Polynomial.X * has

end GBPolyCore

open GBPolyCore

omit [CFieldDomain β] in
/-- When the content `g` is nonzero and divides every `t`-coefficient exactly, `C(toPolyG g) ·
toGBCoeffPoly (gbprimitivePartCore cgcdB p) = toGBCoeffPoly p`. -/
theorem toGBCoeffPoly_gbprimitivePartCore_exact (fuel : ℕ)
    (cgcdB : CPolyG β → CPolyG β → CPolyG β) (p : GBPolyCore β)
    (hg : ¬ CPolyG.cisZeroG (gbcontentCore cgcdB p) = true)
    (hgcn : CPolyG.cnormG (gbcontentCore cgcdB p) ≠ [])
    (_hfuel : ∀ a ∈ gbnormCore p, (CPolyG.cnormG a : List β).length ≤ fuel)
    (hdvd : ∀ a ∈ gbnormCore p, CPolyG.toPolyG (gbcontentCore cgcdB p) ∣ CPolyG.toPolyG a) :
    Polynomial.C (CPolyG.toPolyG (gbcontentCore cgcdB p))
        * GBPolyCore.toGBCoeffPoly (gbprimitivePartCore cgcdB p)
      = GBPolyCore.toGBCoeffPoly p := by
  rw [gbprimitivePartCore]
  simp only [gbcontentCore_gbnormCore, hg, Bool.false_eq_true, if_false]
  rw [toGBCoeffPoly_gbnormCore, toGBCoeffPoly_map_cdivWf_exact (gbnormCore p)
    (gbcontentCore cgcdB p) hgcn hdvd, toGBCoeffPoly_gbnormCore]

omit [CFieldDomain β] in
/-- Clause (iii): under the content-nonzero and content-divides-each-coefficient hypotheses, `Associated
(toGBPolyG (gbprimitivePartCore cgcdB p)) (toGBPolyG p)` over β(s). -/
theorem associated_toGBPolyG_gbprimitivePartCore (fuel : ℕ)
    (cgcdB : CPolyG β → CPolyG β → CPolyG β) (p : GBPolyCore β)
    (hg : ¬ CPolyG.cisZeroG (gbcontentCore cgcdB p) = true)
    (hgcn : CPolyG.cnormG (gbcontentCore cgcdB p) ≠ [])
    (hg0 : CPolyG.toPolyG (gbcontentCore cgcdB p) ≠ 0)
    (hfuel : ∀ a ∈ gbnormCore p, (CPolyG.cnormG a : List β).length ≤ fuel)
    (hdvd : ∀ a ∈ gbnormCore p, CPolyG.toPolyG (gbcontentCore cgcdB p) ∣ CPolyG.toPolyG a) :
    Associated (toGBPolyG (gbprimitivePartCore cgcdB p)) (toGBPolyG p) := by
  -- lift the toGBCoeffPoly-exact identity through liftKG to a C(amG g)-scaling on toGBPolyG
  have hexact := toGBCoeffPoly_gbprimitivePartCore_exact fuel cgcdB p hg hgcn hfuel hdvd
  have hl := congrArg (liftKG β) hexact
  rw [map_mul, liftKG_C] at hl
  -- hl : C (amG (toPolyG g)) * toGBPolyG (gbprimitivePartCore …) = toGBPolyG p
  have hl' : Polynomial.C (QFunNZG.amG β (CPolyG.toPolyG (gbcontentCore cgcdB p)))
      * toGBPolyG (gbprimitivePartCore cgcdB p) = toGBPolyG p := by
    simpa [toGBPolyG] using hl
  refine ⟨(Polynomial.isUnit_C.mpr (QFunNZG.amG_toPolyG_ne_zero hg0).isUnit).unit, ?_⟩
  rw [← hl']
  show toGBPolyG (gbprimitivePartCore cgcdB p)
      * Polynomial.C (QFunNZG.amG β (CPolyG.toPolyG (gbcontentCore cgcdB p)))
    = Polynomial.C (QFunNZG.amG β (CPolyG.toPolyG (gbcontentCore cgcdB p)))
      * toGBPolyG (gbprimitivePartCore cgcdB p)
  ring

/-! ### The content-gcd divides every coefficient — from `cgcdB`'s gcd-correctness (the tower link) -/

/-- `CgcdBCorrect cgcdB`: for all `a b`, `toPolyG (cgcdB a b)` is `Associated` to `gcd (toPolyG a)
(toPolyG b)` in `R = (CFieldSpec.K β)[X]`. -/
def CgcdBCorrect {β : Type*} [CField β] [CFieldSpec β] (cgcdB : CPolyG β → CPolyG β → CPolyG β) : Prop :=
  ∀ a b : CPolyG β, Associated (CPolyG.toPolyG (cgcdB a b))
    (gcd (CPolyG.toPolyG a) (CPolyG.toPolyG b))

variable {β : Type*} [CField β] [CFieldSpec β]

/-- Under `CgcdBCorrect cgcdB`, the running content fold `g = l.foldl (cgcdB) acc` has `toPolyG g`
dividing `toPolyG acc` and `toPolyG a` for every `a ∈ l`. -/
theorem toPolyG_foldl_cgcdB_dvd (cgcdB : CPolyG β → CPolyG β → CPolyG β) (hcorr : CgcdBCorrect cgcdB) :
    ∀ (acc : CPolyG β) (l : List (CPolyG β)),
      CPolyG.toPolyG (l.foldl (fun g c => cgcdB g c) acc) ∣ CPolyG.toPolyG acc ∧
        ∀ a ∈ l, CPolyG.toPolyG (l.foldl (fun g c => cgcdB g c) acc) ∣ CPolyG.toPolyG a := by
  intro acc l
  induction l generalizing acc with
  | nil => exact ⟨dvd_refl _, by simp⟩
  | cons c l ih =>
    set g₁ := cgcdB acc c with hg₁
    -- the step gcd divides the previous accumulator and the new coefficient (up to associates)
    have hcorr1 := hcorr acc c
    have hg₁acc : CPolyG.toPolyG g₁ ∣ CPolyG.toPolyG acc :=
      hcorr1.dvd.trans (gcd_dvd_left _ _)
    have hg₁c : CPolyG.toPolyG g₁ ∣ CPolyG.toPolyG c :=
      hcorr1.dvd.trans (gcd_dvd_right _ _)
    obtain ⟨hfg₁, hfmem⟩ := ih g₁
    have hfold : (c :: l).foldl (fun g c => cgcdB g c) acc
        = l.foldl (fun g c => cgcdB g c) g₁ := by rw [List.foldl_cons]
    rw [hfold]
    refine ⟨hfg₁.trans hg₁acc, ?_⟩
    intro a ha
    rcases List.mem_cons.mp ha with rfl | hl
    · exact hfg₁.trans hg₁c
    · exact hfmem a hl

/-- Under `CgcdBCorrect cgcdB`, `toPolyG (gbcontentCore cgcdB p) ∣ toPolyG a` for every
`a ∈ gbnormCore p`. -/
theorem toPolyG_gbcontentCore_dvd_mem (cgcdB : CPolyG β → CPolyG β → CPolyG β)
    (hcorr : CgcdBCorrect cgcdB) (p : GBPolyCore β) :
    ∀ a ∈ GBPolyCore.gbnormCore p, CPolyG.toPolyG (GBPolyCore.gbcontentCore cgcdB p) ∣ CPolyG.toPolyG a := by
  have hbc : GBPolyCore.gbcontentCore cgcdB p
      = (GBPolyCore.gbnormCore p).foldl (fun g c => cgcdB g c) [] := rfl
  rw [hbc]
  exact (toPolyG_foldl_cgcdB_dvd cgcdB hcorr [] (GBPolyCore.gbnormCore p)).2

/-- Clause (iii) discharged from `CgcdBCorrect cgcdB` (plus content-nonzero and the per-coefficient
bound): `Associated (toGBPolyG (gbprimitivePartCore cgcdB p)) (toGBPolyG p)`. -/
theorem associated_toGBPolyG_gbprimitivePartCore_of_correct (fuel : ℕ)
    (cgcdB : CPolyG β → CPolyG β → CPolyG β) (hcorr : CgcdBCorrect cgcdB) (p : GBPolyCore β)
    (hg : ¬ CPolyG.cisZeroG (GBPolyCore.gbcontentCore cgcdB p) = true)
    (hgcn : CPolyG.cnormG (GBPolyCore.gbcontentCore cgcdB p) ≠ [])
    (hg0 : CPolyG.toPolyG (GBPolyCore.gbcontentCore cgcdB p) ≠ 0)
    (hfuel : ∀ a ∈ GBPolyCore.gbnormCore p, (CPolyG.cnormG a : List β).length ≤ fuel) :
    Associated (toGBPolyG (GBPolyCore.gbprimitivePartCore cgcdB p)) (toGBPolyG p) :=
  associated_toGBPolyG_gbprimitivePartCore fuel cgcdB p hg hgcn hg0 hfuel
    (toPolyG_gbcontentCore_dvd_mem cgcdB hcorr p)

/-! ### Step 3 — the recursive `cgcdFFRawCore` capstone (the deliverable)
Combining the lift-back (`toPolyG_liftGBPolyCoreG`), the primitive-PRS invariant (step 2), and the
`cclearDenomsCoreG` bridge (step 1) gives the polynomial gcd over β(s). -/


/-! ### Restatements against the intended wording (anonymous `example`s) -/

-- The crux: under a regular PRS run, the generic primitive PRS computes the gcd up to associates over
-- β(s) = RatFunc (CFieldSpec.K β).
example (cgcdB : CPolyG β → CPolyG β → CPolyG β) (fuel : ℕ) (P Q : GBPolyCore β)
    (hreg : CPrimPRSGenAssocReg cgcdB fuel P Q) :
    Associated (toGBPolyG (cprimPRSgcdGenCore cgcdB fuel P Q)) (gcd (toGBPolyG P) (toGBPolyG Q)) :=
  associated_toGBPolyG_cprimPRSgcdGenCore cgcdB fuel P Q hreg


/-! ### Verdict and the remaining gap
The fraction-free-gcd correctness holds at every tower level, gated on the per-step regularity bundle
`CPrimPRSGenAssocReg`; clauses (ii) and (iii) are discharged from `CgcdBCorrect cgcdB`. The remaining gap
is unconditional bookkeeping: discharging clause (i) termination from a `t`-degree bound, and threading
`CgcdBCorrect (cgcdFFRawCore β)` with its fuel/termination side-conditions through the tower recursion. -/

#print axioms associated_toGBPolyG_cprimPRSgcdGenCore

end DeepWiki.SymbolicIntegration
