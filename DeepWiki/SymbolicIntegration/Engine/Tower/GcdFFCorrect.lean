import DeepWiki.SymbolicIntegration.Engine.Tower.GcdFFCore
import DeepWiki.ComputableAlgebra.PolyEuclideanDense
import Mathlib.RingTheory.Polynomial.Content

/-! # Abstract correctness of the generic fraction-free gcd `cgcdFFRawCore` over a tower level
The tower kernel fraction-free gcd `cgcdFFRawCore` over `α = DenseFrac β = Frac(β[s])` computes the
polynomial gcd up to associates. The `gb*Core` engine reads through the bridges `DensePoly.toPoly` (into
`R[X]`, `R = (CFieldSpec.K β)[X]`) and `toGBPoly` (into `(RatFunc K)[X]`), and each clear-denominators /
Euclidean-step / primitive-part lemma is derived over `GBPolyCore β`. The content recursion is the tower
induction: the content-gcd is the level-`β` `cgcdFFRawCore`, bottoming at the raw Euclidean gcd over ℚ. -/

open Polynomial Classical

namespace DeepWiki.SymbolicIntegration

open DensePoly

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

/-! ### The bivariate bridge `DensePoly.toPoly : GBPolyCore β → R[X]` (`R = (CFieldSpec.K β)[X] = β[s]`)
Read each `t`-coefficient through `toPoly` and Horner-fold in `t` to get the honest `R[t]` polynomial;
the homomorphism lemmas descend coefficientwise from `toPoly`'s ring-hom lemmas. -/

namespace GBPolyCore

variable {β : Type*} [CField β] [CFieldSpec β]

/-! `GBPolyCore β = DensePoly (DensePoly β)`, so its bivariate denotation is exactly the generic
`DensePoly.toPoly`; no second Horner bridge or arithmetic satellites are needed. -/

omit [CFieldSpec β] in
/-- `gbnormCore [] = []`. -/
@[simp] theorem gbnormCore_nil : gbnormCore ([] : GBPolyCore β) = [] := rfl

omit [CFieldSpec β] in
/-- `gbnormCore` on a cons cell, unfolded to its defining `match` (definitional). -/
theorem gbnormCore_cons_eq (a : DensePoly β) (as : GBPolyCore β) :
    gbnormCore (a :: as)
      = (match gbnormCore as with
          | [] => if DensePoly.cisZero (DensePoly.cnorm a) then [] else [DensePoly.cnorm a]
          | r => DensePoly.cnorm a :: r) := rfl

omit [CFieldSpec β] in
/-- `gbnormCore` is idempotent. -/
@[simp] theorem gbnormCore_idemp (p : GBPolyCore β) : gbnormCore (gbnormCore p) = gbnormCore p := by
  induction p with
  | nil => rfl
  | cons a as ih =>
    rw [gbnormCore_cons_eq]
    cases h : gbnormCore as with
    | nil => cases ha : DensePoly.cisZero (DensePoly.cnorm a) <;> simp [gbnormCore_cons_eq, cnormG_idem, ha]
    | cons b bs =>
      rw [h] at ih
      simp only [gbnormCore_cons_eq, cnormG_idem, ih]

omit [CFieldSpec β] in
/-- Outer dense normalization fixes `gbnormCore`, whose trailing coefficient is already nonzero. -/
@[simp] theorem cnormG_gbnormCore (p : GBPolyCore β) :
    DensePoly.cnorm (gbnormCore p) = gbnormCore p := by
  induction p with
  | nil => rfl
  | cons a as ih =>
    rw [gbnormCore_cons_eq]
    cases h : gbnormCore as with
    | nil =>
      cases ha : DensePoly.cisZero (DensePoly.cnorm a) with
      | true => simp
      | false =>
        have ha' : CCommRing.isZero (DensePoly.cnorm a) = false := ha
        simp [DensePoly.cnormG_cons_eq, ha']
    | cons b bs =>
      rw [h] at ih
      simp only [DensePoly.cnormG_cons_eq, ih]

/-- `DensePoly.toPoly` ignores normalization: `DensePoly.toPoly (gbnormCore p) = DensePoly.toPoly p`. -/
@[simp] theorem toPolyG_gbnormCore (p : GBPolyCore β) :
    DensePoly.toPoly (gbnormCore p) = DensePoly.toPoly p := by
  induction p with
  | nil => rfl
  | cons a as ih =>
    rw [gbnormCore_cons_eq]
    cases h : gbnormCore as with
    | nil =>
      rw [h] at ih
      simp only [DensePoly.toPolyG_nil] at ih
      have has : DensePoly.toPoly as = 0 := ih.symm
      cases ha : DensePoly.cisZero (DensePoly.cnorm a) with
      | true =>
        have hpa : DensePoly.toPoly a = 0 := by
          have hca : DensePoly.cnorm a = [] := by simpa [DensePoly.cisZero, cnormG_idem] using ha
          exact (cnormG_eq_nil_iff _).mp hca
        simp [DensePoly.toPolyG_cons, DensePoly.toR_densePoly, hpa, has]
      | false => simp [DensePoly.toPolyG_cons, DensePoly.toR_densePoly, toPolyG_cnormG, has]
    | cons b bs =>
      rw [h] at ih
      simp only [DensePoly.toPolyG_cons, DensePoly.toR_densePoly, denote, ih,
        DensePoly.toPolyG_cnormG]

/-- `gbnormCore p` is empty exactly when the nested dense polynomial reads as zero. -/
theorem gbnormCore_eq_nil_iff_toPolyG (p : GBPolyCore β) :
    gbnormCore p = [] ↔ DensePoly.toPoly p = 0 := by
  constructor
  · intro h
    rw [← toPolyG_gbnormCore, h, DensePoly.toPolyG_nil]
  · intro h
    have hnorm : DensePoly.cnorm (gbnormCore p) = [] :=
      (DensePoly.cnormG_eq_nil_iff (gbnormCore p)).mpr (by rwa [toPolyG_gbnormCore])
    rwa [cnormG_gbnormCore] at hnorm

/-- The last coefficient of `gbnormCore p` reads to a nonzero `R = (CFieldSpec.K β)[X]`. -/
theorem gbnormCore_getLast?_toPolyG_ne_zero (p : GBPolyCore β) :
    ∀ v, (gbnormCore p).getLast? = some v → DensePoly.toPoly v ≠ 0 := by
  induction p with
  | nil => simp
  | cons a as ih =>
    rw [gbnormCore_cons_eq]
    cases h : gbnormCore as with
    | nil =>
      cases ha : DensePoly.cisZero (DensePoly.cnorm a) with
      | true => rw [if_pos rfl]; simp
      | false =>
        intro v hv
        rw [if_neg (by simp), List.getLast?_singleton, Option.some.injEq] at hv
        subst hv
        simp only [denote]
        intro hz
        have hca : DensePoly.cnorm a = [] := (cnormG_eq_nil_iff a).mpr hz
        rw [DensePoly.cisZero, hca] at ha
        simp at ha
    | cons b bs =>
      rw [h] at ih
      intro v hv
      rw [List.getLast?_cons_cons] at hv
      exact ih v hv

/-- `gblcCore` is the `t`-coefficient at the top index: `toPoly (gblcCore p) =
(DensePoly.toPoly p).coeff (DensePoly.cdeg p)`. -/
theorem toPolyG_gblcCore_eq_coeff (p : GBPolyCore β) :
    DensePoly.toPoly (gblcCore p) = (DensePoly.toPoly p).coeff (DensePoly.cdeg p) := by
  have hdeg : DensePoly.cdeg p = DensePoly.cdeg (gbnormCore p) := by
    rw [DensePoly.cdegG_eq_natDegree, DensePoly.cdegG_eq_natDegree, toPolyG_gbnormCore]
  rw [gblcCore, hdeg, DensePoly.cdeg, cnormG_gbnormCore, ← toPolyG_gbnormCore,
    DensePoly.toPolyG_coeff,
    DensePoly.toR_densePoly, show (CCommRing.zero : DensePoly β) = [] from rfl,
    List.getD_eq_getElem?_getD, ← List.getLast?_eq_getElem?]

end GBPolyCore

/-! ### The field-coefficient lift `R[t] → (RatFunc K)[t]` and `toGBPoly` -/

open CFrac in
/-- The coefficient-ring lift `R[t] → (RatFunc K)[t]`, applying `am β` to every `t`-coefficient. -/
noncomputable abbrev liftK (β : Type*) [CField β] [CFieldSpec β] :
    ((CFieldSpec.K β)[X])[X] →+* (RatFunc (CFieldSpec.K β))[X] :=
  Polynomial.mapRingHom (CFrac.am β)

/-- `toGBPoly p`: the `β(s)[t]` reading of a `GBPolyCore β`, `DensePoly.toPoly p` lifted through the
coefficient embedding `am β` into `(RatFunc (CFieldSpec.K β))[X]`. -/
noncomputable def toGBPoly {β : Type*} [CField β] [CFieldSpec β] (p : GBPolyCore β) :
    (RatFunc (CFieldSpec.K β))[X] :=
  liftK β (DensePoly.toPoly p)

variable {β : Type*} [CField β] [CFieldSpec β]

/-- `toGBPoly [] = 0`. -/
@[simp, denote] theorem toGBPolyG_nil : toGBPoly ([] : GBPolyCore β) = 0 := by simp [toGBPoly]

/-- `liftK (C c) = C (am c)`: the lift sends a constant `β[s]`-coefficient to its `β(s)` embedding. -/
theorem liftKG_C (c : (CFieldSpec.K β)[X]) :
    liftK β (Polynomial.C c) = Polynomial.C (CFrac.am β c) := by
  simp [liftK, Polynomial.coe_mapRingHom, Polynomial.map_C]

/-- `toPoly (liftGBPolyCore p) = toGBPoly p`: lifting coefficientwise as `c/1` then through `toPoly`
agrees with the coefficient-ring embedding. -/
@[denote] theorem toPolyG_liftGBPolyCoreG (p : GBPolyCore β) :
    toPoly (DensePoly.liftGBPolyCore p) = toGBPoly p := by
  apply Polynomial.ext
  intro i
  rw [toGBPoly, liftK, Polynomial.coe_mapRingHom, Polynomial.coeff_map,
    DensePoly.toPolyG_coeff, toPolyG_coeff, DensePoly.liftGBPolyCore,
    List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : p[i]? with
  | none =>
    simp only [Option.map_none, Option.getD_none]
    rw [CRingSpec.toR_zero, CRingSpec.toR_zero, map_zero]
  | some c =>
    simp only [Option.map_some, Option.getD_some]
    show CFrac.toRatFunc _ = CFrac.am β (DensePoly.toPoly c)
    rw [CFrac.toRatFunc_ofPoly, toPoly_list_eq]

/-! ### The `cclearDenomsCore` bridge `β(s)[t] ↔ (β[s])[t]`
Read back over `β(s)`, the cleared polynomial equals `C s · toPoly p` for the common-denominator unit
`s = ∏_j denⱼ`, hence is `Associated` to `toPoly p`; the combinatorics reuse `filter_prod_mul`. -/

variable [CFieldDomain β DensePoly]

/-- The common-denominator scalar `commonDen p ∈ R`: the product of all the `β[s]`-denominators of `p`'s
coefficients, the unit by which `cclearDenomsCore` scales `toPoly p`. -/
noncomputable def commonDen (p : DensePoly (DenseFrac β)) : (CFieldSpec.K β)[X] :=
  ((p.map CFrac.den).map DensePoly.toPoly).prod

omit [CFieldDomain β DensePoly] in
/-- `commonDen p ≠ 0`: a product of nonzero denominators. -/
theorem commonDenG_ne_zero (p : DensePoly (DenseFrac β)) : commonDen p ≠ 0 := by
  rw [commonDen]
  refine List.prod_ne_zero ?_
  intro hmem
  rw [List.mem_map] at hmem
  obtain ⟨d, hd, hd0⟩ := hmem
  rw [List.mem_map] at hd
  obtain ⟨c, hc, rfl⟩ := hd
  have hne : DensePoly.toPoly (CFrac.den c) ≠ 0 := by
    simpa only [toPoly_list_eq] using CFrac.toPoly_den_ne_zero_generic c
  exact hne hd0

omit [CFieldDomain β DensePoly] in
/-- `am (commonDen p) ≠ 0` (the field embedding of a nonzero product). -/
theorem amG_commonDenG_ne_zero (p : DensePoly (DenseFrac β)) : CFrac.am β (commonDen p) ≠ 0 :=
  (map_ne_zero_iff _ (RatFunc.algebraMap_injective (CFieldSpec.K β))).mpr (commonDenG_ne_zero p)

omit [CFieldDomain β DensePoly] in
/-- `toPoly` of a `cmul`-fold is `toPoly init` times the product of the `toPoly`-images of the folded
list. -/
@[denote] theorem toPolyG_foldl_cmulG (init : DensePoly β) (ds : List (DensePoly β × ℕ)) :
    DensePoly.toPoly (ds.foldl (fun acc de => DensePoly.cmul acc de.1) init)
      = DensePoly.toPoly init * (ds.map (fun de => DensePoly.toPoly de.1)).prod := by
  induction ds generalizing init with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, ih, denote, List.map_cons, List.prod_cons]; ring

omit [CFieldSpec β] in
/-- The `i`-th cleared coefficient of `cclearDenomsCore p` (in range) is `numᵢ · (∏_{j≠i} denⱼ)`. -/
theorem cclearDenomsCoreG_getElem (p : DensePoly (DenseFrac β)) (i : ℕ) (hi : i < p.length) :
    (DensePoly.cclearDenomsCore p)[i]? = some (DensePoly.cmul (CFrac.num (p.getD i CCommRing.zero))
      ((((p.map CFrac.den).zipIdx).filter (fun de => decide (de.2 ≠ i))).foldl
        (fun acc de => DensePoly.cmul acc de.1) [CCommRing.one])) := by
  unfold DensePoly.cclearDenomsCore
  simp only
  rw [List.getElem?_map, List.getElem?_zipIdx, List.getElem?_eq_getElem hi]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

omit [CFieldSpec β] [CFieldDomain β DensePoly] in
/-- `cclearDenomsCore` preserves the `t`-length: `(cclearDenomsCore p).length = p.length`. -/
theorem cclearDenomsCoreG_length (p : DensePoly (DenseFrac β)) :
    (DensePoly.cclearDenomsCore p).length = p.length := by
  unfold DensePoly.cclearDenomsCore; simp

/-- `toPoly p` vanishes past the list length (the out-of-range coefficient is `CCommRing.zero = 0`). -/
theorem toPolyG_coeff_eq_zero_of_length_leG (p : DensePoly (DenseFrac β)) {i : ℕ} (hi : p.length ≤ i) :
    (toPoly p).coeff i = 0 := by
  rw [toPolyG_coeff, List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
  show CFieldSpec.toK (CCommRing.zero : DenseFrac β) = 0
  rw [CFieldSpec.toK_zero]

/-- `(toGBPoly (cclearDenomsCore p)).coeff i = am (commonDen p) · (toPoly p).coeff i`. -/
theorem toGBPolyG_cclearDenomsCoreG_coeff (p : DensePoly (DenseFrac β)) (i : ℕ) :
    (toGBPoly (DensePoly.cclearDenomsCore p)).coeff i
      = CFrac.am β (commonDen p) * (toPoly p).coeff i := by
  rcases lt_or_ge i p.length with hi | hi
  · rw [toGBPoly, liftK, Polynomial.coe_mapRingHom, Polynomial.coeff_map,
      DensePoly.toPolyG_coeff, toPolyG_coeff,
      List.getD_eq_getElem?_getD, cclearDenomsCoreG_getElem p i hi, Option.getD_some]
    rw [DensePoly.toR_densePoly, DensePoly.toPolyG_cmulG, toPolyG_foldl_cmulG,
      DensePoly.toPolyG_one_singleton, one_mul]
    set dens := p.map CFrac.den with hdens
    have hcd : commonDen p = (dens.map DensePoly.toPoly).prod := by rw [commonDen, hdens]
    have hlen : i < dens.length := by rw [hdens, List.length_map]; exact hi
    have hfilt := filter_prod_mul (DensePoly.toPoly) ([] : DensePoly β) dens 0 i (Nat.zero_le i)
      (by simpa using hlen)
    rw [Nat.sub_zero] at hfilt
    have hdeni : DensePoly.toPoly (dens.getD i []) = DensePoly.toPoly (CFrac.den (p.getD i CCommRing.zero)) := by
      congr 1
      rw [hdens, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hi]
      simp
    have hcoeff : (CFieldSpec.toK (p.getD i CCommRing.zero) : RatFunc (CFieldSpec.K β))
        = CFrac.am β (DensePoly.toPoly (CFrac.num (p.getD i CCommRing.zero)))
          / CFrac.am β (DensePoly.toPoly (CFrac.den (p.getD i CCommRing.zero))) := by
      show CFrac.toRatFunc (p.getD i CCommRing.zero) = _
      rw [CFrac.toRatFunc_eq_div]
      simp only [toPoly_list_eq]
    have hden0 : CFrac.am β (DensePoly.toPoly (CFrac.den (p.getD i CCommRing.zero))) ≠ 0 := by
      simpa only [toPoly_list_eq] using
        CFrac.am_ne_zero
          (CFrac.toPoly_den_ne_zero_generic (p.getD i CCommRing.zero))
    rw [toR_eq_toK, hcoeff, hcd]
    have hpushP : CFrac.am β (((dens.zipIdx.filter (fun de => decide (de.2 ≠ i))).map
        (fun de => DensePoly.toPoly de.1)).prod)
        * CFrac.am β (DensePoly.toPoly (CFrac.den (p.getD i CCommRing.zero)))
        = CFrac.am β ((dens.map DensePoly.toPoly).prod) := by
      rw [← map_mul, ← hdeni, hfilt]
    rw [map_mul,
      mul_comm (CFrac.am β ((dens.map DensePoly.toPoly).prod)) _, div_mul_eq_mul_div,
      eq_div_iff hden0, mul_assoc, hpushP]
  · rw [toGBPoly, liftK, Polynomial.coe_mapRingHom, Polynomial.coeff_map,
      DensePoly.toPolyG_coeff, DensePoly.toR_densePoly, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by rw [cclearDenomsCoreG_length]; exact hi), Option.getD_none,
      show (CCommRing.zero : DensePoly β) = [] from rfl, DensePoly.toPolyG_nil, map_zero,
      toPolyG_coeff_eq_zero_of_length_leG p hi, mul_zero]

/-- `toGBPoly (cclearDenomsCore p) = C (am (commonDen p)) * toPoly p` over β(s). -/
theorem toGBPolyG_cclearDenomsCoreG (p : DensePoly (DenseFrac β)) :
    toGBPoly (DensePoly.cclearDenomsCore p) = Polynomial.C (CFrac.am β (commonDen p)) * toPoly p := by
  ext i
  rw [toGBPolyG_cclearDenomsCoreG_coeff, Polynomial.coeff_C_mul]

/-- `Associated (toGBPoly (cclearDenomsCore p)) (toPoly p)`: fraction-clearing is a β(s)-unit
scaling, preserving the gcd up to associates. -/
theorem associated_toGBPolyG_cclearDenomsCoreG (p : DensePoly (DenseFrac β)) :
    Associated (toGBPoly (DensePoly.cclearDenomsCore p)) (toPoly p) := by
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

/-- `DensePoly.toPoly [[CCommRing.one]] = 1`: the `GBPolyCore` constant `1`. -/
@[simp] theorem toPolyG_one : DensePoly.toPoly ([[CCommRing.one]] : GBPolyCore β) = 1 := by
  rw [DensePoly.toPolyG_cons, DensePoly.toPolyG_nil, mul_zero, add_zero,
    DensePoly.toR_densePoly,
    show DensePoly.toPoly ([CCommRing.one] : DensePoly β) = 1 by
      simp only [denote, mul_zero, add_zero, map_one], map_one]

/-- Pseudo-division identity through `DensePoly.toPoly`: there exist a multiplier `c ∈ β[s]` and quotient
`s` with `C (toPoly c) · DensePoly.toPoly p = DensePoly.toPoly s · DensePoly.toPoly q +
DensePoly.toPoly (gbpsremainderCore fuel p q)` in `R[t]`. -/
theorem toPolyG_gbpsremainderCore (fuel : ℕ) (p q : GBPolyCore β) :
    ∃ (s : GBPolyCore β) (c : DensePoly β),
      Polynomial.C (DensePoly.toPoly c) * DensePoly.toPoly p
        = DensePoly.toPoly s * DensePoly.toPoly q + DensePoly.toPoly (gbpsremainderCore fuel p q) := by
  have hone : DensePoly.toPoly ([CCommRing.one] : DensePoly β) = 1 := by
    simp only [denote, mul_zero, add_zero, map_one]
  induction fuel generalizing p with
  | zero => exact ⟨[], [CCommRing.one], by simp [gbpsremainderCore, toPolyG_gbnormCore, hone]⟩
  | succ fuel ih =>
    simp only [gbpsremainderCore]
    split_ifs with hq hlen
    · exact ⟨[], [CCommRing.one], by simp [toPolyG_gbnormCore, hone]⟩
    · exact ⟨[], [CCommRing.one], by simp [toPolyG_gbnormCore, hone]⟩
    · obtain ⟨s', c', hsc⟩ := ih (gbnormCore (DensePoly.csub (DensePoly.cscale (gblcCore (gbnormCore q)) (gbnormCore p))
        (DensePoly.cscale (gblcCore (gbnormCore p))
          (DensePoly.cshift ((gbnormCore p).length - (gbnormCore q).length) (gbnormCore q)))))
      have hp' : DensePoly.toPoly (gbnormCore (DensePoly.csub (DensePoly.cscale (gblcCore (gbnormCore q)) (gbnormCore p))
          (DensePoly.cscale (gblcCore (gbnormCore p))
            (DensePoly.cshift ((gbnormCore p).length - (gbnormCore q).length) (gbnormCore q)))))
          = Polynomial.C (DensePoly.toPoly (gblcCore (gbnormCore q))) * DensePoly.toPoly p
            - Polynomial.C (DensePoly.toPoly (gblcCore (gbnormCore p)))
              * Polynomial.X ^ ((gbnormCore p).length - (gbnormCore q).length) * DensePoly.toPoly q := by
        rw [toPolyG_gbnormCore, DensePoly.toPolyG_csubG, DensePoly.toPolyG_cscaleG,
          DensePoly.toPolyG_cscaleG, DensePoly.toPolyG_cshiftG, toPolyG_gbnormCore,
          toPolyG_gbnormCore]
        simp only [DensePoly.toR_densePoly]
        ring
      rw [hp', gbpsremainderCore_gbnormCore_right] at hsc
      refine ⟨DensePoly.cadd s' (DensePoly.cscale (DensePoly.cmul c' (gblcCore (gbnormCore p)))
          (DensePoly.cshift ((gbnormCore p).length - (gbnormCore q).length) [[CCommRing.one]])),
          DensePoly.cmul c' (gblcCore (gbnormCore q)), ?_⟩
      simp only [DensePoly.toPolyG_caddG, DensePoly.toPolyG_cscaleG, DensePoly.toPolyG_cshiftG,
        DensePoly.toR_densePoly, toPolyG_one, denote, map_mul]
      linear_combination hsc

end GBPolyCore

open GBPolyCore

omit [CFieldDomain β DensePoly] in
/-- The β(s)[t] lift of the pseudo-division identity: `C (am (toPoly c)) · toGBPoly p = toGBPoly s ·
toGBPoly q + toGBPoly (gbpsremainderCore fuel p q)` for some quotient `s` and multiplier `c`. -/
theorem toGBPolyG_gbpsremainderCore (fuel : ℕ) (p q : GBPolyCore β) :
    ∃ (s : GBPolyCore β) (c : DensePoly β),
      Polynomial.C (CFrac.am β (DensePoly.toPoly c)) * toGBPoly p
        = toGBPoly s * toGBPoly q + toGBPoly (gbpsremainderCore fuel p q) := by
  obtain ⟨s, c, hsc⟩ := toPolyG_gbpsremainderCore fuel p q
  refine ⟨s, c, ?_⟩
  have hl := congrArg (liftK β) hsc
  simp only [map_add, map_mul] at hl
  rw [liftKG_C] at hl
  simpa [toGBPoly] using hl

omit [CFieldDomain β DensePoly] in
/-- `toGBPoly` ignores normalization: `toGBPoly (gbnormCore p) = toGBPoly p`. -/
@[simp, denote] theorem toGBPolyG_gbnormCore (p : GBPolyCore β) :
    toGBPoly (gbnormCore p) = toGBPoly p := by
  rw [toGBPoly, toPolyG_gbnormCore, ← toGBPoly]

omit [CFieldDomain β DensePoly] in
/-- `toGBPoly p = 0 ↔ DensePoly.toPoly p = 0` (the lift is injective, `am` injective on coefficients). -/
theorem toGBPolyG_eq_zero_iff (p : GBPolyCore β) : toGBPoly p = 0 ↔ DensePoly.toPoly p = 0 := by
  rw [toGBPoly, liftK, ← Polynomial.map_zero (CFrac.am β)]
  exact Polynomial.map_injective (CFrac.am β) (RatFunc.algebraMap_injective (CFieldSpec.K β)) |>.eq_iff

omit [CFieldDomain β DensePoly] in
/-- `toGBPoly p = 0 ↔ DensePoly.cisZero p = true`. -/
theorem toGBPolyG_eq_zero_iff_cisZero (p : GBPolyCore β) :
    toGBPoly p = 0 ↔ DensePoly.cisZero p = true := by
  rw [toGBPolyG_eq_zero_iff, DensePoly.cisZeroG_iff]

/-! ### Step 2 — the primitive-PRS gcd invariant over β(s) -/

omit [CFieldDomain β DensePoly] in
/-- gcd is invariant under an associated right argument in `(RatFunc (CFieldSpec.K β))[X]`. -/
theorem associated_gcd_right_gbpolyG {A B B' : (RatFunc (CFieldSpec.K β))[X]} (h : Associated B B') :
    Associated (gcd A B) (gcd A B') :=
  associated_gcd_right_field h

/-- Per-run regularity `CPrimPRSGenAssocReg cgcdB fuel P Q`: the inductive predicate collecting what each
`cprimPRSgcdGenCore` step's gcd invariant needs — (i) termination `DensePoly.cisZero Q = true`, (ii) a
pseudo-division witness with β(s)-unit multiplier, and (iii) `gbprimitivePartCore` a β(s)-unit scaling. -/
def CPrimPRSGenAssocReg (cgcdB : DensePoly β → DensePoly β → DensePoly β) :
    ℕ → GBPolyCore β → GBPolyCore β → Prop
  | 0, P, Q =>
    DensePoly.cisZero Q = true ∧
      Associated (toGBPoly (GBPolyCore.gbprimitivePartCore cgcdB P)) (toGBPoly P)
  | fuel + 1, P, Q =>
    (DensePoly.cisZero (GBPolyCore.gbnormCore Q) = true ∧
      Associated (toGBPoly (GBPolyCore.gbprimitivePartCore cgcdB (GBPolyCore.gbnormCore P)))
        (toGBPoly P)) ∨
      (¬ DensePoly.cisZero (GBPolyCore.gbnormCore Q) = true ∧
        (∃ (s : GBPolyCore β) (c : DensePoly β),
          Polynomial.C (CFrac.am β (DensePoly.toPoly c)) * toGBPoly (GBPolyCore.gbnormCore P)
            = toGBPoly s * toGBPoly (GBPolyCore.gbnormCore Q)
              + toGBPoly (GBPolyCore.gbpsremainderCore (GBPolyCore.gbnormCore P).length
                  (GBPolyCore.gbnormCore P)
                  (GBPolyCore.gbnormCore Q))
          ∧ CFrac.am β (DensePoly.toPoly c) ≠ 0) ∧
        Associated (toGBPoly (GBPolyCore.gbprimitivePartCore cgcdB
            (GBPolyCore.gbpsremainderCore (GBPolyCore.gbnormCore P).length
              (GBPolyCore.gbnormCore P) (GBPolyCore.gbnormCore Q))))
          (toGBPoly (GBPolyCore.gbpsremainderCore (GBPolyCore.gbnormCore P).length
              (GBPolyCore.gbnormCore P)
              (GBPolyCore.gbnormCore Q))) ∧
        CPrimPRSGenAssocReg cgcdB fuel (GBPolyCore.gbnormCore Q)
          (GBPolyCore.gbprimitivePartCore cgcdB
            (GBPolyCore.gbpsremainderCore (GBPolyCore.gbnormCore P).length
              (GBPolyCore.gbnormCore P) (GBPolyCore.gbnormCore Q))))

omit [CFieldDomain β DensePoly] in
/-- The primitive-PRS gcd invariant: for a regular run, `Associated (toGBPoly (cprimPRSgcdGenCore cgcdB
fuel P Q)) (gcd (toGBPoly P) (toGBPoly Q))` over β(s). -/
theorem associated_toGBPolyG_cprimPRSgcdGenCore (cgcdB : DensePoly β → DensePoly β → DensePoly β) :
    ∀ (fuel : ℕ) (P Q : GBPolyCore β), CPrimPRSGenAssocReg cgcdB fuel P Q →
      Associated (toGBPoly (cprimPRSgcdGenCore cgcdB fuel P Q))
        (gcd (toGBPoly P) (toGBPoly Q)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro P Q hreg
    obtain ⟨hQ, hprim⟩ := hreg
    have hQ0 : toGBPoly Q = 0 := (toGBPolyG_eq_zero_iff_cisZero Q).mpr hQ
    show Associated (toGBPoly (GBPolyCore.gbprimitivePartCore cgcdB P))
      (gcd (toGBPoly P) (toGBPoly Q))
    rw [hQ0]
    exact hprim.trans (gcd_zero_right' (toGBPoly P)).symm
  | succ fuel ih =>
    intro P Q hreg
    show Associated (toGBPoly (
        let P := GBPolyCore.gbnormCore P; let Q := GBPolyCore.gbnormCore Q;
        if DensePoly.cisZero Q then GBPolyCore.gbprimitivePartCore cgcdB P
        else cprimPRSgcdGenCore cgcdB fuel Q
          (GBPolyCore.gbprimitivePartCore cgcdB (GBPolyCore.gbpsremainderCore P.length P Q))))
      (gcd (toGBPoly P) (toGBPoly Q))
    simp only
    by_cases hQ : DensePoly.cisZero (GBPolyCore.gbnormCore Q) = true
    · rw [if_pos hQ]
      rw [CPrimPRSGenAssocReg] at hreg
      rcases hreg with ⟨_, hprim⟩ | ⟨hne, _⟩
      · have hQ0 : toGBPoly Q = 0 := by
          rw [← toGBPolyG_gbnormCore]; exact (toGBPolyG_eq_zero_iff_cisZero _).mpr hQ
        rw [hQ0]
        exact hprim.trans (gcd_zero_right' (toGBPoly P)).symm
      · exact absurd hQ hne
    · rw [if_neg hQ]
      rw [CPrimPRSGenAssocReg] at hreg
      rcases hreg with ⟨h, _⟩ | ⟨_, ⟨s, c, hrel, hc0⟩, hassoc, hrec⟩
      · exact absurd h hQ
      set Pn := GBPolyCore.gbnormCore P with hPn
      set Qn := GBPolyCore.gbnormCore Q with hQn
      set prem := GBPolyCore.gbpsremainderCore Pn.length Pn Qn with hprem
      set r := GBPolyCore.gbprimitivePartCore cgcdB prem with hr
      have hih := ih Qn r hrec
      have hstep : Associated (gcd (toGBPoly Pn) (toGBPoly Qn))
          (gcd (toGBPoly Qn) (toGBPoly r)) := by
        have heuc : Associated (gcd (toGBPoly Pn) (toGBPoly Qn))
            (gcd (toGBPoly Qn) (toGBPoly prem)) :=
          associated_gcd_euclid_step_field (A := toGBPoly Pn) (B := toGBPoly Qn)
            (R := toGBPoly prem) (S := toGBPoly s)
            (Polynomial.isUnit_C.mpr hc0.isUnit) (by linear_combination hrel)
        exact heuc.trans (associated_gcd_right_gbpolyG hassoc.symm)
      rw [show toGBPoly P = toGBPoly Pn by rw [hPn, toGBPolyG_gbnormCore],
        show toGBPoly Q = toGBPoly Qn by rw [hQn, toGBPolyG_gbnormCore]]
      exact hih.trans hstep.symm

/-! ### Discharging clause (iii) — the content strip is a β(s)-unit scaling
When the content divides every `t`-coefficient (from the gcd-correctness of `cgcdB`, the tower
induction), `gbprimitivePartCore cgcdB prem` is exact division, i.e. a β(s)-unit scaling. -/

namespace GBPolyCore

variable {β : Type*} [CField β] [CFieldSpec β]

omit [CFieldSpec β] in
/-- The `t`-content `gbcontentCore cgcdB p` is invariant under `gbnormCore`:
`gbcontentCore cgcdB (gbnormCore p) = gbcontentCore cgcdB p`. -/
theorem gbcontentCore_gbnormCore (cgcdB : DensePoly β → DensePoly β → DensePoly β) (p : GBPolyCore β) :
    gbcontentCore cgcdB (gbnormCore p) = gbcontentCore cgcdB p := by
  rw [gbcontentCore, gbcontentCore, gbnormCore_idemp]

/-- If `g` divides every `t`-coefficient of `p`, selected exact division reconstructs `p`. -/
theorem toPoly_map_div_exact (p : GBPolyCore β) (g : DensePoly β)
    (hg : DensePoly.cnorm g ≠ [])
    (hdvd : ∀ a ∈ p, DensePoly.toPoly g ∣ DensePoly.toPoly a) :
    Polynomial.C (DensePoly.toPoly g) *
        DensePoly.toPoly (p.map (fun a => CPolyEuclidean.div a g))
      = DensePoly.toPoly p := by
  have hgne : DensePoly.toPoly g ≠ 0 := fun h => hg ((cnormG_eq_nil_iff g).mpr h)
  induction p with
  | nil => simp
  | cons a as ih =>
    have has := ih (fun b hb => hdvd b (by simp [hb]))
    have ha : DensePoly.toPoly a =
        DensePoly.toPoly (CPolyEuclidean.div a g) * DensePoly.toPoly g := by
      have hexact := LawfulCPolyEuclidean.div_exact a g
        (by simpa only [toPoly_list_eq] using hgne)
        (by simpa only [toPoly_list_eq] using hdvd a (by simp))
      simpa only [toPoly_list_eq, mul_comm] using hexact
    rw [List.map_cons, DensePoly.toPolyG_cons, DensePoly.toPolyG_cons]
    simp only [DensePoly.toR_densePoly]
    rw [ha, map_mul]
    linear_combination Polynomial.X * has

end GBPolyCore

open GBPolyCore

omit [CFieldDomain β DensePoly] in
/-- When the content `g` is nonzero and divides every `t`-coefficient exactly, `C(toPoly g) ·
DensePoly.toPoly (gbprimitivePartCore cgcdB p) = DensePoly.toPoly p`. -/
theorem toPolyG_gbprimitivePartCore_exact
    (cgcdB : DensePoly β → DensePoly β → DensePoly β) (p : GBPolyCore β)
    (hg : ¬ DensePoly.cisZero (gbcontentCore cgcdB p) = true)
    (hgcn : DensePoly.cnorm (gbcontentCore cgcdB p) ≠ [])
    (hdvd : ∀ a ∈ gbnormCore p, DensePoly.toPoly (gbcontentCore cgcdB p) ∣ DensePoly.toPoly a) :
    Polynomial.C (DensePoly.toPoly (gbcontentCore cgcdB p))
        * DensePoly.toPoly (gbprimitivePartCore cgcdB p)
      = DensePoly.toPoly p := by
  rw [gbprimitivePartCore]
  simp only [gbcontentCore_gbnormCore, hg, Bool.false_eq_true, if_false]
  rw [toPolyG_gbnormCore]
  have hexact := toPoly_map_div_exact (gbnormCore p)
    (gbcontentCore cgcdB p) hgcn hdvd
  simpa only [toPolyG_gbnormCore] using hexact

omit [CFieldDomain β DensePoly] in
/-- Clause (iii): under the content-nonzero and content-divides-each-coefficient hypotheses, `Associated
(toGBPoly (gbprimitivePartCore cgcdB p)) (toGBPoly p)` over β(s). -/
theorem associated_toGBPolyG_gbprimitivePartCore
    (cgcdB : DensePoly β → DensePoly β → DensePoly β) (p : GBPolyCore β)
    (hg : ¬ DensePoly.cisZero (gbcontentCore cgcdB p) = true)
    (hgcn : DensePoly.cnorm (gbcontentCore cgcdB p) ≠ [])
    (hg0 : DensePoly.toPoly (gbcontentCore cgcdB p) ≠ 0)
    (hdvd : ∀ a ∈ gbnormCore p, DensePoly.toPoly (gbcontentCore cgcdB p) ∣ DensePoly.toPoly a) :
    Associated (toGBPoly (gbprimitivePartCore cgcdB p)) (toGBPoly p) := by
  -- lift the DensePoly.toPoly-exact identity through liftK to a C(am g)-scaling on toGBPoly
  have hexact := toPolyG_gbprimitivePartCore_exact cgcdB p hg hgcn hdvd
  have hl := congrArg (liftK β) hexact
  rw [map_mul, liftKG_C] at hl
  -- hl : C (am (toPoly g)) * toGBPoly (gbprimitivePartCore …) = toGBPoly p
  have hl' : Polynomial.C (CFrac.am β (DensePoly.toPoly (gbcontentCore cgcdB p)))
      * toGBPoly (gbprimitivePartCore cgcdB p) = toGBPoly p := by
    simpa [toGBPoly] using hl
  have hamg : CFrac.am β (DensePoly.toPoly (gbcontentCore cgcdB p)) ≠ 0 := by
    exact CFrac.am_ne_zero hg0
  refine ⟨(Polynomial.isUnit_C.mpr hamg.isUnit).unit, ?_⟩
  rw [← hl']
  show toGBPoly (gbprimitivePartCore cgcdB p)
      * Polynomial.C (CFrac.am β (DensePoly.toPoly (gbcontentCore cgcdB p)))
    = Polynomial.C (CFrac.am β (DensePoly.toPoly (gbcontentCore cgcdB p)))
      * toGBPoly (gbprimitivePartCore cgcdB p)
  ring

/-! ### The content-gcd divides every coefficient — from `cgcdB`'s gcd-correctness (the tower link) -/

/-- `CgcdBCorrect cgcdB`: for all `a b`, `toPoly (cgcdB a b)` is `Associated` to `gcd (toPoly a)
(toPoly b)` in `R = (CFieldSpec.K β)[X]`. -/
def CgcdBCorrect {β : Type*} [CField β] [CFieldSpec β] (cgcdB : DensePoly β → DensePoly β → DensePoly β) : Prop :=
  ∀ a b : DensePoly β, Associated (DensePoly.toPoly (cgcdB a b))
    (gcd (DensePoly.toPoly a) (DensePoly.toPoly b))

variable {β : Type*} [CField β] [CFieldSpec β]

/-- Under `CgcdBCorrect cgcdB`, the running content fold `g = l.foldl (cgcdB) acc` has `toPoly g`
dividing `toPoly acc` and `toPoly a` for every `a ∈ l`. -/
theorem toPolyG_foldl_cgcdB_dvd (cgcdB : DensePoly β → DensePoly β → DensePoly β) (hcorr : CgcdBCorrect cgcdB) :
    ∀ (acc : DensePoly β) (l : List (DensePoly β)),
      DensePoly.toPoly (l.foldl (fun g c => cgcdB g c) acc) ∣ DensePoly.toPoly acc ∧
        ∀ a ∈ l, DensePoly.toPoly (l.foldl (fun g c => cgcdB g c) acc) ∣ DensePoly.toPoly a := by
  intro acc l
  induction l generalizing acc with
  | nil => exact ⟨dvd_refl _, by simp⟩
  | cons c l ih =>
    set g₁ := cgcdB acc c with hg₁
    -- the step gcd divides the previous accumulator and the new coefficient (up to associates)
    have hcorr1 := hcorr acc c
    have hg₁acc : DensePoly.toPoly g₁ ∣ DensePoly.toPoly acc :=
      hcorr1.dvd.trans (gcd_dvd_left _ _)
    have hg₁c : DensePoly.toPoly g₁ ∣ DensePoly.toPoly c :=
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

/-- Under `CgcdBCorrect cgcdB`, `toPoly (gbcontentCore cgcdB p) ∣ toPoly a` for every
`a ∈ gbnormCore p`. -/
theorem toPolyG_gbcontentCore_dvd_mem (cgcdB : DensePoly β → DensePoly β → DensePoly β)
    (hcorr : CgcdBCorrect cgcdB) (p : GBPolyCore β) :
    ∀ a ∈ GBPolyCore.gbnormCore p, DensePoly.toPoly (GBPolyCore.gbcontentCore cgcdB p) ∣ DensePoly.toPoly a := by
  have hbc : GBPolyCore.gbcontentCore cgcdB p
      = (GBPolyCore.gbnormCore p).foldl (fun g c => cgcdB g c) [] := rfl
  rw [hbc]
  exact (toPolyG_foldl_cgcdB_dvd cgcdB hcorr [] (GBPolyCore.gbnormCore p)).2

/-- Clause (iii) discharged from `CgcdBCorrect cgcdB`: `Associated
(toGBPoly (gbprimitivePartCore cgcdB p)) (toGBPoly p)`. -/
theorem associated_toGBPolyG_gbprimitivePartCore_of_correct
    (cgcdB : DensePoly β → DensePoly β → DensePoly β) (hcorr : CgcdBCorrect cgcdB) (p : GBPolyCore β)
    (hg : ¬ DensePoly.cisZero (GBPolyCore.gbcontentCore cgcdB p) = true)
    (hgcn : DensePoly.cnorm (GBPolyCore.gbcontentCore cgcdB p) ≠ [])
    (hg0 : DensePoly.toPoly (GBPolyCore.gbcontentCore cgcdB p) ≠ 0) :
    Associated (toGBPoly (GBPolyCore.gbprimitivePartCore cgcdB p)) (toGBPoly p) :=
  associated_toGBPolyG_gbprimitivePartCore cgcdB p hg hgcn hg0
    (toPolyG_gbcontentCore_dvd_mem cgcdB hcorr p)

/-! ### Step 3 — the recursive `cgcdFFRawCore` capstone (the deliverable)
Combining the lift-back (`toPolyG_liftGBPolyCoreG`), the primitive-PRS invariant (step 2), and the
`cclearDenomsCore` bridge (step 1) gives the polynomial gcd over β(s). -/


/-! ### Restatements against the intended wording (anonymous `example`s) -/

-- The crux: under a regular PRS run, the generic primitive PRS computes the gcd up to associates over
-- β(s) = RatFunc (CFieldSpec.K β).
example (cgcdB : DensePoly β → DensePoly β → DensePoly β) (fuel : ℕ) (P Q : GBPolyCore β)
    (hreg : CPrimPRSGenAssocReg cgcdB fuel P Q) :
    Associated (toGBPoly (cprimPRSgcdGenCore cgcdB fuel P Q)) (gcd (toGBPoly P) (toGBPoly Q)) :=
  associated_toGBPolyG_cprimPRSgcdGenCore cgcdB fuel P Q hreg


/-! ### Verdict

The fuel specification's primitive-PRS invariant is reduced to `CPrimPRSGenAssocReg`; clauses (ii) and
(iii) follow from `CgcdBCorrect cgcdB`. `PrimPRSRegular/Termination` discharges the degree-fuelled
termination witness, while `WellFounded` lifts the resulting Wf primitive-PRS invariant through denominator
clearing and monic normalization to the recursive dense gcd law. -/

#print axioms associated_toGBPolyG_cprimPRSgcdGenCore

end DeepWiki.SymbolicIntegration
