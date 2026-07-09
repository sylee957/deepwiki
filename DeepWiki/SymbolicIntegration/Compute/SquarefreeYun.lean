import DeepWiki.SymbolicIntegration.Compute.Correctness
import DeepWiki.SymbolicIntegration.Compute.SquarefreeExact
import DeepWiki.SymbolicIntegration.SquarefreeFactorization

/-! # Concrete Yun correctness for `csqfreeFactor`

Bridges the computable `CPolyQ` Yun loop to the abstract squarefree-factorization API.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration.Compute

/-! ### Bridging the concrete `csqfreeFactor` monic gcd to the abstract `gcd` -/

/-- The concrete monic gcd realizes the abstract `gcd` under gcd termination. -/
theorem toPoly_cmonic_cgcdExt (fuel : ℕ) (b d : CPolyQ) (hterm : cgcdTerminates fuel b d) :
    toPoly (cmonic (cgcdExt fuel b d).1) = gcd (toPoly b) (toPoly d) := by
  rw [toPoly_cmonic_eq_normalize]
  obtain ⟨hgb, hgd⟩ := toPoly_cgcdExt_dvd fuel b d hterm
  have hassoc : Associated (toPoly (cgcdExt fuel b d).1) (gcd (toPoly b) (toPoly d)) :=
    associated_of_dvd_dvd (dvd_gcd hgb hgd) (toPoly_dvd_cgcdExt fuel b d (gcd_dvd_left _ _)
      (gcd_dvd_right _ _))
  rw [← normalize_gcd (toPoly b) (toPoly d)]
  exact normalize_eq_normalize_iff.mpr (hassoc.dvd_dvd)

/-! ### The concrete `csqfreeFactor.go` carries the abstract `YunInv` -/

/-- Per-step honesty bundle for `csqfreeFactor.go` to realize the abstract Yun step. -/
def GoYun (fuel : ℕ) : ℕ → CPolyQ → CPolyQ → Prop
  | 0, _, _ => True
  | fo + 1, b, d =>
    if b.length ≤ 1 then True
    else
      let q := cmonic (cgcdExt fuel b d).1
      let b' := cdiv fuel b q
      let d' := csub (cdiv fuel d q) (cderiv b')
      cgcdTerminates fuel b d ∧
        toPoly b = toPoly q * toPoly b' ∧
        toPoly d = toPoly q * toPoly (cdiv fuel d q) ∧
        GoYun fuel fo b' d'

/-! ### Crossing the `ℚ`-instance diamond by `convert` -/

open Classical in
/-- `A.primPart ≠ 0` for `A : ℚ[X]`. -/
theorem primPart_ne_zero_rat (A : ℚ[X]) : A.primPart ≠ 0 := A.primPart_ne_zero

/-- Every abstract Yun factor is squarefree over ambient `ℚ`. -/
theorem yunFactorizationAbs_squarefree_rat (A : ℚ[X]) (hA0 : A ≠ 0) (n : ℕ) :
    ∀ V ∈ yunFactorizationAbs A n, Squarefree V := by
  convert yunFactorizationAbs_squarefree A hA0 ?_ n using 2
  convert A.primPart_ne_zero using 2
  · rfl
  · congr 1
    exact Subsingleton.elim _ _

/-- `sqfreeFactPart A i` over `ℚ[X]` agrees across the ambient and `Classical` instance paths. -/
theorem sqfreeFactPart_rat_eq (A : ℚ[X]) (i : ℕ) :
    @sqfreeFactPart ℚ Rat.commRing Rat.isDomain _ _ A i
      = @sqfreeFactPart ℚ Rat.instField.toCommRing _ _
          (@CommGroupWithZero.instNormalizedGCDMonoid ℚ Field.toSemifield.toCommGroupWithZero
            (fun a b => Classical.propDecidable (a = b))) A i := by
  have hinst : @CommGroupWithZero.instNormalizedGCDMonoid ℚ Rat.commGroupWithZero instDecidableEqRat
      = @CommGroupWithZero.instNormalizedGCDMonoid ℚ Field.toSemifield.toCommGroupWithZero
          (fun a b => Classical.propDecidable (a = b)) := by
    congr 1
    exact Subsingleton.elim _ _
  rw [show @sqfreeFactPart ℚ Rat.commRing Rat.isDomain _ _ A i
        = @sqfreeFactPart ℚ Rat.commRing Rat.isDomain _
            (@CommGroupWithZero.instNormalizedGCDMonoid ℚ Rat.commGroupWithZero instDecidableEqRat)
            A i from rfl, hinst]

/-- Factorwise correctness for `yunFactorizationAbs` over ambient `ℚ`. -/
theorem yunFactorizationAbs_forall₂_rat (A : ℚ[X]) (hA0 : A ≠ 0) (n : ℕ) :
    List.Forall₂ Associated (yunFactorizationAbs A n)
      ((List.range n).map (fun j => sqfreeFactPart A (1 + j))) := by
  rw [List.map_congr_left fun j _ => sqfreeFactPart_rat_eq A (1 + j)]
  refine yunFactorizationAbs_forall₂ A hA0 ?_ n
  convert A.primPart_ne_zero using 2
  · rfl
  · congr 1
    exact Subsingleton.elim _ _

/-- Pairwise relative primality for `yunFactorizationAbs` over ambient `ℚ`. -/
theorem yunFactorizationAbs_pairwise_isRelPrime_rat (A : ℚ[X]) (hA0 : A ≠ 0) (n : ℕ) {p q : ℕ}
    (hpq : p ≠ q) (hp : p < (yunFactorizationAbs A n).length)
    (hq : q < (yunFactorizationAbs A n).length) :
    IsRelPrime ((yunFactorizationAbs A n).get ⟨p, hp⟩) ((yunFactorizationAbs A n).get ⟨q, hq⟩) := by
  convert yunFactorizationAbs_pairwise_isRelPrime A hA0 ?_ n hpq hp hq using 2
  convert A.primPart_ne_zero using 2
  · rfl
  · congr 1
    exact Subsingleton.elim _ _

/-- Powered-product correctness for `yunFactorizationAbs` over ambient `ℚ`. -/
theorem yunFactorizationAbs_prodPow_assoc_rat (A : ℚ[X]) (hA0 : A ≠ 0) (n : ℕ) :
    Associated (prodPow 1 (yunFactorizationAbs A n))
      (prodPow 1 ((List.range n).map (fun j => sqfreeFactPart A (1 + j)))) := by
  rw [List.map_congr_left fun j _ => sqfreeFactPart_rat_eq A (1 + j)]
  refine yunFactorizationAbs_prodPow_assoc A hA0 ?_ n
  convert A.primPart_ne_zero using 2
  · rfl
  · congr 1
    exact Subsingleton.elim _ _

/-! ### Concrete-loop step bridges over ambient `ℚ` instances -/

/-- The ambient `gcd` over `ℚ[X]` equals the `Classical`-derived one. -/
theorem gcd_rat_eq (a b : ℚ[X]) :
    @gcd ℚ[X] _ (@Polynomial.normalizedGcdMonoid ℚ Rat.commRing _).toGCDMonoid a b
      = @gcd ℚ[X] _ (@Polynomial.normalizedGcdMonoid ℚ Rat.instField.toCommRing
          (@CommGroupWithZero.instNormalizedGCDMonoid ℚ Field.toSemifield.toCommGroupWithZero
            (fun x y => Classical.propDecidable (x = y)))).toGCDMonoid a b := by
  have hinst : @CommGroupWithZero.instNormalizedGCDMonoid ℚ Rat.commGroupWithZero instDecidableEqRat
      = @CommGroupWithZero.instNormalizedGCDMonoid ℚ Field.toSemifield.toCommGroupWithZero
          (fun x y => Classical.propDecidable (x = y)) := by
    congr 1; exact Subsingleton.elim _ _
  rw [show @gcd ℚ[X] _ (@Polynomial.normalizedGcdMonoid ℚ Rat.commRing _).toGCDMonoid a b
        = @gcd ℚ[X] _ (@Polynomial.normalizedGcdMonoid ℚ Rat.commRing
            (@CommGroupWithZero.instNormalizedGCDMonoid ℚ Rat.commGroupWithZero instDecidableEqRat)).toGCDMonoid
          a b from rfl, hinst]

/-- Yun loop base case over ambient `ℚ`. -/
theorem yunInv_base_rat (A : ℚ[X]) (hA0 : A ≠ 0) :
    YunInv A 1 (A / gcd A (derivative A))
      (derivative A / gcd A (derivative A) - derivative (A / gcd A (derivative A))) := by
  have key := yunInv_base A hA0
    (by convert A.primPart_ne_zero using 2 <;> first | rfl | (congr 1; exact Subsingleton.elim _ _))
  rw [gcd_rat_eq A (derivative A)]
  exact key

/-- Scaled Yun loop base case over ambient `ℚ`. -/
theorem yunInv_base_scaled_rat (A : ℚ[X]) (hA0 : A ≠ 0) (u : ℚ) (hu : u ≠ 0) (b1 d1 : ℚ[X])
    (hb1 : b1 = Polynomial.C u * (A / gcd A (derivative A)))
    (hd1 : d1 = Polynomial.C u * (derivative A / gcd A (derivative A))
              - derivative (Polynomial.C u * (A / gcd A (derivative A)))) :
    YunInv A 1 b1 d1 := by
  obtain ⟨c, hc, hbb, hdd⟩ := yunInv_base_rat A hA0
  rw [hbb] at hb1 hd1
  have hDgcd : derivative A / gcd A (derivative A)
      = Polynomial.C c * Dabs A 1 + derivative (Polynomial.C c * Babs A 1) := by
    rw [← hbb]; exact eq_add_of_sub_eq hdd
  rw [hDgcd] at hd1
  simp only [derivative_C_mul] at hd1
  refine ⟨u * c, mul_ne_zero hu hc, ?_, ?_⟩
  · rw [hb1, map_mul]; ring
  · rw [hd1, map_mul]; ring

/-- The emitted Yun factor is associated to `Vᵢ` over ambient `ℚ`. -/
theorem yunStep_emit_assoc_rat (A : ℚ[X]) (i : ℕ) (hi : 1 ≤ i) (b d : ℚ[X]) (hinv : YunInv A i b d) :
    Associated (gcd b d) (sqfreeFactPart A i) := by
  have key := yunStep_emit_assoc A i hi
    (by convert A.primPart_ne_zero using 2 <;> first | rfl | (congr 1; exact Subsingleton.elim _ _)) hinv
  rw [sqfreeFactPart_rat_eq A i, gcd_rat_eq b d]
  exact key

/-- One Yun loop step advances the invariant over ambient `ℚ`. -/
theorem yunStep_preserves_rat (A : ℚ[X]) (i : ℕ) (hi : 1 ≤ i) (b d : ℚ[X]) (hinv : YunInv A i b d) :
    YunInv A (i + 1) (b / gcd b d) (d / gcd b d - derivative (b / gcd b d)) := by
  have key := (yunStep_preserves A i hi
    (by convert A.primPart_ne_zero using 2 <;> first | rfl | (congr 1; exact Subsingleton.elim _ _))
    hinv).2
  rw [gcd_rat_eq b d]
  exact key

/-! ### Concrete `csqfreeFactor.go` factor correspondence -/

/-- `Babs A i ≠ 0` over `ℚ`. -/
theorem Babs_ne_zero_rat (A : ℚ[X]) (i : ℕ) : Babs A i ≠ 0 := by
  rw [Babs]
  exact (squarefreePart_deflation_monic A (i - 1)
    (by convert A.primPart_ne_zero using 2 <;>
      first | rfl | (congr 1; exact Subsingleton.elim _ _))).ne_zero

/-- The working numerator `b` of a `YunInv A i b d` state is nonzero. -/
theorem ne_zero_of_yunInv_rat (A : ℚ[X]) (i : ℕ) (b d : ℚ[X]) (hinv : YunInv A i b d) : b ≠ 0 := by
  obtain ⟨c, hc, hb, _⟩ := hinv
  rw [hb]
  exact mul_ne_zero ((map_ne_zero_iff _ Polynomial.C_injective).mpr hc) (Babs_ne_zero_rat A i)

/-- `b = a / c` from the exact factorization `a = c * b` with `c ≠ 0`. -/
private theorem eq_div_of_eq_mul {a b c : ℚ[X]} (hc : c ≠ 0) (h : a = c * b) : b = a / c := by
  rw [h, mul_div_cancel_left₀ _ hc]

/-- The concrete Yun loop's kept factors are associated to the squarefree parts. -/
theorem go_factor_assoc (fuel : ℕ) (A : CPolyQ) :
    ∀ (fo : ℕ) (b d : CPolyQ) (i : ℕ), 1 ≤ i → GoYun fuel fo b d →
      YunInv (toPoly A) i (toPoly b) (toPoly d) →
      ∀ (Vm : CPolyQ × ℕ), Vm ∈ csqfreeFactor.go fuel fo b d i →
        Associated (toPoly Vm.1) (sqfreeFactPart (toPoly A) Vm.2) ∧ i ≤ Vm.2 := by
  intro fo
  induction fo with
  | zero =>
    intro b d i _ _ _ Vm hVm
    rw [csqfreeFactor.go.eq_def] at hVm; simp at hVm
  | succ fo ih =>
    intro b d i hi hgo hinv Vm hVm
    rw [csqfreeFactor.go.eq_def] at hVm
    by_cases hb : b.length ≤ 1
    · simp only [hb, if_true] at hVm; simp at hVm
    · simp only [hb, if_false] at hVm
      rw [GoYun] at hgo
      simp only [hb, if_false] at hgo
      obtain ⟨hterm, hexb, hexd, hgorest⟩ := hgo
      set q := cmonic (cgcdExt fuel b d).1 with hqdef
      set b' := cdiv fuel b q with hb'def
      set d' := csub (cdiv fuel d q) (cderiv b') with hd'def
      have hgcd : toPoly q = gcd (toPoly b) (toPoly d) := toPoly_cmonic_cgcdExt fuel b d hterm
      have hbne : toPoly b ≠ 0 := ne_zero_of_yunInv_rat (toPoly A) i (toPoly b) (toPoly d) hinv
      have hgcd0 : gcd (toPoly b) (toPoly d) ≠ 0 :=
        fun h => hbne (eq_zero_of_zero_dvd (h ▸ gcd_dvd_left _ _))
      have hbfact : toPoly b = gcd (toPoly b) (toPoly d) * toPoly b' := hgcd ▸ hexb
      have hdfact : toPoly d = gcd (toPoly b) (toPoly d) * toPoly (cdiv fuel d q) := hgcd ▸ hexd
      have hb'eq : toPoly b' = toPoly b / gcd (toPoly b) (toPoly d) := eq_div_of_eq_mul hgcd0 hbfact
      have hd'eq : toPoly d' = toPoly d / gcd (toPoly b) (toPoly d) - derivative (toPoly b') := by
        rw [hd'def, toPoly_csub, toPoly_cderiv]
        congr 1
        exact eq_div_of_eq_mul hgcd0 hdfact
      have hinv' : YunInv (toPoly A) (i + 1) (toPoly b') (toPoly d') := by
        rw [hb'eq, hd'eq, hb'eq]
        exact yunStep_preserves_rat (toPoly A) i hi (toPoly b) (toPoly d) hinv
      have hhead : Associated (toPoly q) (sqfreeFactPart (toPoly A) i) := by
        rw [hgcd]; exact yunStep_emit_assoc_rat (toPoly A) i hi (toPoly b) (toPoly d) hinv
      by_cases hq : q.length ≤ 1
      · simp only [hq, if_true] at hVm
        exact (ih b' d' (i + 1) (by omega) hgorest hinv' Vm hVm).imp id (by omega)
      · simp only [hq, if_false, List.mem_cons] at hVm
        rcases hVm with rfl | hVm
        · exact ⟨hhead, le_refl i⟩
        · exact (ih b' d' (i + 1) (by omega) hgorest hinv' Vm hVm).imp id (by omega)

/-! ### Concrete `csqfreeFactor` Yun correctness -/

/-- Associated to a squarefree part implies squarefree over ambient `ℚ`. -/
theorem squarefree_of_associated_sqfreeFactPart_rat (A : ℚ[X]) (V : ℚ[X]) (j : ℕ)
    (h : Associated V (sqfreeFactPart A j)) : Squarefree V := by
  apply squarefree_of_associated_sqfreeFactPart A j
  rw [← sqfreeFactPart_rat_eq A j]; exact h

/-- Associated to distinct squarefree parts implies relatively prime over ambient `ℚ`. -/
theorem isRelPrime_of_associated_sqfreeFactPart_rat (A : ℚ[X]) (V W : ℚ[X]) (i j : ℕ) (hij : i ≠ j)
    (hV : Associated V (sqfreeFactPart A i)) (hW : Associated W (sqfreeFactPart A j)) :
    IsRelPrime V W := by
  apply isRelPrime_of_associated_sqfreeFactPart A hij
  · rw [← sqfreeFactPart_rat_eq A i]; exact hV
  · rw [← sqfreeFactPart_rat_eq A j]; exact hW

/-- Engine-honesty bundle for `csqfreeFactor fuel D`. -/
def SqfreeYun (fuel : ℕ) (D : CPolyQ) : Prop :=
  let p := cnorm D
  let g := (cgcdExt fuel p (cderiv p)).1
  let b1 := cdiv fuel p g
  let d1 := csub (cdiv fuel (cderiv p) g) (cderiv b1)
  YunInv (toPoly D) 1 (toPoly b1) (toPoly d1) ∧ GoYun fuel fuel b1 d1

/-- Every `csqfreeFactor` factor is associated to a squarefree part. -/
theorem csqfreeFactor_factor_assoc (fuel : ℕ) (D : CPolyQ) (hex : SqfreeYun fuel D)
    (Vm : CPolyQ × ℕ) (hVm : Vm ∈ csqfreeFactor fuel D) :
    Associated (toPoly Vm.1) (sqfreeFactPart (toPoly D) Vm.2) ∧ 1 ≤ Vm.2 := by
  rw [SqfreeYun] at hex
  obtain ⟨hinv, hgo⟩ := hex
  rw [csqfreeFactor.eq_def] at hVm
  exact go_factor_assoc fuel D fuel _ _ 1 (le_refl 1) hgo hinv Vm hVm

/-- Every `csqfreeFactor` factor is squarefree under `SqfreeYun`. -/
theorem csqfreeFactor_squarefree (fuel : ℕ) (D : CPolyQ) (hex : SqfreeYun fuel D)
    (Vm : CPolyQ × ℕ) (hVm : Vm ∈ csqfreeFactor fuel D) :
    Squarefree (toPoly Vm.1) :=
  squarefree_of_associated_sqfreeFactPart_rat (toPoly D) _ Vm.2
    (csqfreeFactor_factor_assoc fuel D hex Vm hVm).1

/-- Every recorded multiplicity emitted by `csqfreeFactor.go fuel fo b d i` is at least `i`. -/
theorem go_mult_ge (fuel : ℕ) : ∀ (fo : ℕ) (b d : CPolyQ) (i : ℕ) (Vm : CPolyQ × ℕ),
    Vm ∈ csqfreeFactor.go fuel fo b d i → i ≤ Vm.2 := by
  intro fo
  induction fo with
  | zero => intro b d i Vm hVm; rw [csqfreeFactor.go.eq_def] at hVm; simp at hVm
  | succ fo ih =>
    intro b d i Vm hVm
    rw [csqfreeFactor.go.eq_def] at hVm
    by_cases hb : b.length ≤ 1
    · simp only [hb, if_true] at hVm; simp at hVm
    · simp only [hb, if_false] at hVm
      set q := cmonic (cgcdExt fuel b d).1
      set b' := cdiv fuel b q
      set d' := csub (cdiv fuel d q) (cderiv b')
      by_cases hq : q.length ≤ 1
      · simp only [hq, if_true] at hVm
        exact le_trans (Nat.le_succ i) (ih b' d' (i + 1) Vm hVm)
      · simp only [hq, if_false, List.mem_cons] at hVm
        rcases hVm with rfl | hVm
        · exact le_refl i
        · exact le_trans (Nat.le_succ i) (ih b' d' (i + 1) Vm hVm)

/-- The recorded multiplicities are pairwise distinct across `csqfreeFactor.go`. -/
theorem go_mult_pairwise (fuel : ℕ) : ∀ (fo : ℕ) (b d : CPolyQ) (i : ℕ),
    List.Pairwise (fun x y : CPolyQ × ℕ => x.2 ≠ y.2) (csqfreeFactor.go fuel fo b d i) := by
  intro fo
  induction fo with
  | zero => intro b d i; rw [csqfreeFactor.go.eq_def]; simp
  | succ fo ih =>
    intro b d i
    rw [csqfreeFactor.go.eq_def]
    by_cases hb : b.length ≤ 1
    · simp only [hb, if_true]; simp
    · simp only [hb, if_false]
      set q := cmonic (cgcdExt fuel b d).1
      set b' := cdiv fuel b q
      set d' := csub (cdiv fuel d q) (cderiv b')
      by_cases hq : q.length ≤ 1
      · simp only [hq, if_true]; exact ih b' d' (i + 1)
      · simp only [hq, if_false, List.pairwise_cons]
        refine ⟨fun Vm hVm => ?_, ih b' d' (i + 1)⟩
        have := go_mult_ge fuel fo b' d' (i + 1) Vm hVm
        omega

/-- The `csqfreeFactor` factors have pairwise-distinct multiplicities. -/
theorem csqfreeFactor_mult_pairwise (fuel : ℕ) (D : CPolyQ) :
    List.Pairwise (fun x y : CPolyQ × ℕ => x.2 ≠ y.2) (csqfreeFactor fuel D) := by
  rw [csqfreeFactor.eq_def]; exact go_mult_pairwise fuel fuel _ _ 1

/-- The `csqfreeFactor` factors are pairwise relatively prime under `SqfreeYun`. -/
theorem csqfreeFactor_pairwise_isRelPrime (fuel : ℕ) (D : CPolyQ) (hex : SqfreeYun fuel D)
    (p q : ℕ) (hpq : p ≠ q) (hp : p < (csqfreeFactor fuel D).length)
    (hq : q < (csqfreeFactor fuel D).length) :
    IsRelPrime (toPoly ((csqfreeFactor fuel D).get ⟨p, hp⟩).1)
      (toPoly ((csqfreeFactor fuel D).get ⟨q, hq⟩).1) := by
  have hpw := csqfreeFactor_mult_pairwise fuel D
  have hmne : ((csqfreeFactor fuel D).get ⟨p, hp⟩).2 ≠ ((csqfreeFactor fuel D).get ⟨q, hq⟩).2 := by
    rcases lt_or_gt_of_ne hpq with h | h
    · exact List.pairwise_iff_get.mp hpw ⟨p, hp⟩ ⟨q, hq⟩ h
    · exact (List.pairwise_iff_get.mp hpw ⟨q, hq⟩ ⟨p, hp⟩ h).symm
  exact isRelPrime_of_associated_sqfreeFactPart_rat (toPoly D) _ _ _ _ hmne
    (csqfreeFactor_factor_assoc fuel D hex _ ((csqfreeFactor fuel D).get_mem _)).1
    (csqfreeFactor_factor_assoc fuel D hex _ ((csqfreeFactor fuel D).get_mem _)).1

/-! ### Restatements against the intended Yun-correctness wording -/

open Classical in
example {K : Type*} [Field K] [CharZero K] (A : K[X]) (hA0 : A ≠ 0) (hA : A.primPart ≠ 0) (n : ℕ) :
    List.Forall₂ Associated (yunFactorizationAbs A n)
      ((List.range n).map (fun j => sqfreeFactPart A (1 + j))) :=
  yunFactorizationAbs_forall₂ A hA0 hA n

open Classical in
example {K : Type*} [Field K] [CharZero K] (A : K[X]) (hA0 : A ≠ 0) (hA : A.primPart ≠ 0) (n : ℕ) :
    ∀ V ∈ yunFactorizationAbs A n, Squarefree V :=
  yunFactorizationAbs_squarefree A hA0 hA n

open Classical in
example {K : Type*} [Field K] [CharZero K] (A : K[X]) (hA0 : A ≠ 0) (hA : A.primPart ≠ 0) (n : ℕ)
    {p q : ℕ} (hpq : p ≠ q) (hp : p < (yunFactorizationAbs A n).length)
    (hq : q < (yunFactorizationAbs A n).length) :
    IsRelPrime ((yunFactorizationAbs A n).get ⟨p, hp⟩) ((yunFactorizationAbs A n).get ⟨q, hq⟩) :=
  yunFactorizationAbs_pairwise_isRelPrime A hA0 hA n hpq hp hq

open Classical in
example {K : Type*} [Field K] [CharZero K] (A : K[X]) (hA0 : A ≠ 0) (hA : A.primPart ≠ 0) (n : ℕ) :
    Associated (prodPow 1 (yunFactorizationAbs A n))
      (prodPow 1 ((List.range n).map (fun j => sqfreeFactPart A (1 + j)))) :=
  yunFactorizationAbs_prodPow_assoc A hA0 hA n

example (fuel : ℕ) (D : CPolyQ) (hex : SqfreeYun fuel D)
    (Vm : CPolyQ × ℕ) (hVm : Vm ∈ csqfreeFactor fuel D) :
    Squarefree (toPoly Vm.1) :=
  csqfreeFactor_squarefree fuel D hex Vm hVm

example (fuel : ℕ) (D : CPolyQ) (hex : SqfreeYun fuel D)
    (p q : ℕ) (hpq : p ≠ q) (hp : p < (csqfreeFactor fuel D).length)
    (hq : q < (csqfreeFactor fuel D).length) :
    IsRelPrime (toPoly ((csqfreeFactor fuel D).get ⟨p, hp⟩).1)
      (toPoly ((csqfreeFactor fuel D).get ⟨q, hq⟩).1) :=
  csqfreeFactor_pairwise_isRelPrime fuel D hex p q hpq hp hq

end DeepWiki.SymbolicIntegration.Compute
