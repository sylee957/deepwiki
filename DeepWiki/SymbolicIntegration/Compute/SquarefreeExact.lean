import DeepWiki.SymbolicIntegration.Compute.Correctness
import DeepWiki.SymbolicIntegration.Compute.Squarefree

/-! # Exactness certificates for computable squarefree factorization

Decidable exact-division witnesses for `csqfreeFactor` under the `toPoly : DensePoly ℚ → ℚ[X]` bridge. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace Compute

/-! ### The Yun radical `Dstar` divides `D` through `toPoly` -/

/-- `cmonic q` divides `q` through `toPoly`: `toPoly (cmonic q) ∣ toPoly q`. -/
theorem toPoly_cmonic_dvd (q : DensePoly ℚ) : toPoly (cmonic q) ∣ toPoly q := by
  simp only [toPoly_eq_dense]
  unfold cmonic
  by_cases h : cisZero (cnorm q)
  · simp only [h, if_true]
    have hq0 : DensePoly.toPoly q = 0 := by
      have : cnorm q = [] := by simpa [cisZero] using h
      rw [← DensePoly.toPolyG_cnormG, this, DensePoly.toPolyG_nil]
    simp [hq0]
  · simp only [h, Bool.false_eq_true, if_false]
    rw [DensePoly.toPolyG_cscaleG, DensePoly.toPolyG_cnormG]
    have hc : clead (cnorm q) ≠ 0 := clead_ne_zero (by simpa [cisZero] using h)
    refine ⟨(Polynomial.C (clead (cnorm q)) : ℚ[X]), ?_⟩
    rw [show CField.inv (clead (cnorm q)) = (clead (cnorm q))⁻¹ from rfl]
    rw [toR_eq_toK, CFieldSpec.toK_rat]
    rw [mul_comm (Polynomial.C (clead (cnorm q))⁻¹) (DensePoly.toPoly q), mul_assoc, ← map_mul,
      inv_mul_cancel₀ hc, map_one, mul_one]

/-- The `toPoly`-product of the first components of a factor list: `goProd l = ∏ⱼ toPoly Vⱼ`. -/
noncomputable def goProd (l : List (DensePoly ℚ × ℕ)) : ℚ[X] :=
  (l.map (fun vi => DensePoly.toPoly vi.1)).prod

/-- `GoExact fo b d` records exact Yun-loop divisions through `toPoly`. -/
def GoExact : ℕ → DensePoly ℚ → DensePoly ℚ → Prop
  | 0, _, _ => True
  | fo + 1, b, d =>
    if b.length ≤ 1 then True
    else
      let q := cmonic (DensePoly.cgcdWf b d).1
      let b' := DensePoly.cdivWf b q
      let d' := csub (DensePoly.cdivWf d q) (cderiv b')
      toPoly b = toPoly q * toPoly b' ∧ GoExact fo b' d'

/-- Under `GoExact`, the product emitted by `csqfreeFactor.go fuel fo b d i` divides `toPoly b`. -/
theorem goProd_dvd : ∀ (fo : ℕ) (b d : DensePoly ℚ) (i : ℕ),
    GoExact fo b d → goProd (csqfreeFactor.go fo b d i) ∣ toPoly b := by
  intro fo
  induction fo with
  | zero =>
    intro b d i _
    rw [csqfreeFactor.go.eq_def]
    simp [goProd]
  | succ fo ih =>
    intro b d i hex
    rw [csqfreeFactor.go.eq_def]
    by_cases hb : b.length ≤ 1
    · simp only [hb, if_true]
      simp [goProd]
    · simp only [hb, if_false]
      rw [GoExact] at hex
      simp only [hb, if_false] at hex
      obtain ⟨hexb, hexrest⟩ := hex
      set q := cmonic (DensePoly.cgcdWf b d).1 with hqdef
      set b' := DensePoly.cdivWf b q with hb'def
      set d' := csub (DensePoly.cdivWf d q) (cderiv b') with hd'def
      have ihrest : goProd (csqfreeFactor.go fo b' d' (i + 1)) ∣ toPoly b' :=
        ih b' d' (i + 1) hexrest
      by_cases hq : q.length ≤ 1
      · simp only [hq, if_true]
        exact ihrest.trans ⟨toPoly q, by rw [hexb]; ring⟩
      · simp only [hq, if_false]
        rw [goProd, List.map_cons, List.prod_cons, ← goProd, hexb]
        exact mul_dvd_mul_left (toPoly q) ihrest

/-- `goProd` realizes the radical fold: `toPoly (l.foldl (cmul · vi.1) init) = toPoly init · goProd l`. -/
theorem toPoly_foldl_cmul_fst (l : List (DensePoly ℚ × ℕ)) (init : DensePoly ℚ) :
    toPoly (l.foldl (fun acc vi => cmul acc vi.1) init) = toPoly init * goProd l := by
  simp only [toPoly_eq_dense]
  induction l generalizing init with
  | nil => simp [goProd]
  | cons hd tl ih =>
    rw [List.foldl_cons, ih, DensePoly.toPolyG_cmulG]
    simp only [goProd, List.map_cons, List.prod_cons]
    ring

/-- The radical fold reads to `goProd`: `toPoly (l.foldl (cmul · vi.1) [1]) = goProd l`. -/
theorem toPoly_Dstar_eq (l : List (DensePoly ℚ × ℕ)) :
    toPoly (l.foldl (fun acc (vi : DensePoly ℚ × ℕ) => cmul acc vi.1) [1]) = goProd l := by
  rw [toPoly_foldl_cmul_fst]
  simp [DensePoly.toPolyG_cons, DensePoly.toPolyG_nil]

/-- One fuel-free Yun step is exact. -/
theorem step_exact (b d : DensePoly ℚ) (hbne : cnorm b ≠ []) :
    toPoly b = toPoly (cmonic (DensePoly.cgcdWf b d).1)
        * toPoly (DensePoly.cdivWf b (cmonic (DensePoly.cgcdWf b d).1)) := by
  set q := cmonic (DensePoly.cgcdWf b d).1 with hqdef
  have hgcd_dvd_dense : DensePoly.toPoly (DensePoly.cgcdWf b d).1 ∣ DensePoly.toPoly b :=
    (DensePoly.toPolyG_cgcdWf_dvd b d).1
  have hgcd_dvd : toPoly (DensePoly.cgcdWf b d).1 ∣ toPoly b := by
    simpa only [toPoly_eq_dense] using hgcd_dvd_dense
  have hqb : toPoly q ∣ toPoly b :=
    (toPoly_cmonic_dvd (DensePoly.cgcdWf b d).1).trans hgcd_dvd
  have hb0 : toPoly b ≠ 0 := fun h => hbne ((cnorm_eq_nil_iff b).mpr h)
  have hq0 : toPoly q ≠ 0 := by
    intro h; rw [h, zero_dvd_iff] at hqb; exact hb0 hqb
  have hqne : cnorm q ≠ [] := fun h => hq0 ((cnorm_eq_nil_iff q).mp h)
  have hqbDense : DensePoly.toPoly q ∣ DensePoly.toPoly b := by
    simpa only [toPoly_eq_dense] using hqb
  have hdiv := DensePoly.toPolyG_cdivWf_exact b q hqne hqbDense
  simpa only [toPoly_eq_dense, mul_comm] using hdiv.symm

/-- `SqfreeExact fuel D` bundles exact initial deflation and exact Yun-loop divisions. -/
def SqfreeExact (fuel : ℕ) (D : DensePoly ℚ) : Prop :=
  let p := cnorm D
  let g := (DensePoly.cgcdWf p (cderiv p)).1
  let b1 := DensePoly.cdivWf p g
  let d1 := csub (DensePoly.cdivWf (cderiv p) g) (cderiv b1)
  toPoly p = toPoly g * toPoly b1 ∧ GoExact fuel b1 d1

/-- Under `SqfreeExact fuel D`, the Yun radical of `csqfreeFactor fuel D` divides `toPoly D`. -/
theorem toPoly_Dstar_dvd_D (fuel : ℕ) (D : DensePoly ℚ) (hex : SqfreeExact fuel D) :
    toPoly ((csqfreeFactor fuel D).foldl (fun acc (vi : DensePoly ℚ × ℕ) => cmul acc vi.1) [1])
      ∣ toPoly D := by
  rw [toPoly_Dstar_eq, csqfreeFactor.eq_def]
  rw [SqfreeExact] at hex
  obtain ⟨hb1, hgo⟩ := hex
  have hdvd := goProd_dvd fuel
    (DensePoly.cdivWf (cnorm D) (DensePoly.cgcdWf (cnorm D) (cderiv (cnorm D))).1)
    (csub (DensePoly.cdivWf (cderiv (cnorm D))
        (DensePoly.cgcdWf (cnorm D) (cderiv (cnorm D))).1)
      (cderiv (DensePoly.cdivWf (cnorm D)
        (DensePoly.cgcdWf (cnorm D) (cderiv (cnorm D))).1))) 1 hgo
  have hb1D : toPoly (DensePoly.cdivWf (cnorm D)
      (DensePoly.cgcdWf (cnorm D) (cderiv (cnorm D))).1)
      ∣ toPoly D := by
    simp only [toPoly_eq_dense] at hb1 ⊢
    rw [← DensePoly.toPolyG_cnormG D, hb1]; exact Dvd.intro_left _ rfl
  exact hdvd.trans hb1D

/-! ### Computable witnesses -/

/-- `GoExactComp fo b d` records vanishing `cmodWf` remainders for each Yun-loop division. -/
def GoExactComp : ℕ → DensePoly ℚ → DensePoly ℚ → Prop
  | 0, _, _ => True
  | fo + 1, b, d =>
    if b.length ≤ 1 then True
    else
      let q := cmonic (DensePoly.cgcdWf b d).1
      let b' := DensePoly.cdivWf b q
      let d' := csub (DensePoly.cdivWf d q) (cderiv b')
      cnorm (DensePoly.cmodWf b q) = [] ∧ cnorm q ≠ [] ∧ GoExactComp fo b' d'

/-- `GoExactComp` is decidable. -/
instance decGoExactComp (fo : ℕ) (b d : DensePoly ℚ) : Decidable (GoExactComp fo b d) := by
  induction fo generalizing b d with
  | zero => exact inferInstanceAs (Decidable True)
  | succ fo ih =>
    rw [GoExactComp]
    by_cases hb : b.length ≤ 1
    · rw [if_pos hb]; exact inferInstanceAs (Decidable True)
    · rw [if_neg hb]
      have := ih (DensePoly.cdivWf b (cmonic (DensePoly.cgcdWf b d).1))
        (csub (DensePoly.cdivWf d (cmonic (DensePoly.cgcdWf b d).1))
          (cderiv (DensePoly.cdivWf b (cmonic (DensePoly.cgcdWf b d).1))))
      infer_instance

/-- `GoExactComp` implies `GoExact` by turning each vanishing `cmod` into exact division. -/
theorem GoExactComp_to_GoExact : ∀ (fo : ℕ) (b d : DensePoly ℚ),
    GoExactComp fo b d → GoExact fo b d := by
  intro fo
  induction fo with
  | zero => intro b d _; trivial
  | succ fo ih =>
    intro b d h
    rw [GoExactComp] at h
    rw [GoExact]
    by_cases hb : b.length ≤ 1
    · simp only [hb, if_true]
    · simp only [hb, if_false] at h ⊢
      obtain ⟨hrem, hqne, hrest⟩ := h
      refine ⟨?_, ih _ _ hrest⟩
      have hrem0 : toPoly (DensePoly.cmodWf b (cmonic (DensePoly.cgcdWf b d).1)) = 0 := by
        rw [toPoly_eq_dense, ← DensePoly.toPolyG_cnormG, hrem, DensePoly.toPolyG_nil]
      have hdiv := DensePoly.toPolyG_cmodWf b (cmonic (DensePoly.cgcdWf b d).1) hqne
      simp only [toPoly_eq_dense] at hdiv hrem0 ⊢
      rw [hrem0, add_zero] at hdiv
      exact hdiv.trans (mul_comm _ _)

/-- `SqfreeExactComp fuel D` bundles vanishing `cmod` remainders for squarefree factorization. -/
def SqfreeExactComp (fuel : ℕ) (D : DensePoly ℚ) : Prop :=
  let p := cnorm D
  let g := (DensePoly.cgcdWf p (cderiv p)).1
  let b1 := DensePoly.cdivWf p g
  let d1 := csub (DensePoly.cdivWf (cderiv p) g) (cderiv b1)
  (cnorm (DensePoly.cmodWf p g) = [] ∧ cnorm g ≠ []) ∧ GoExactComp fuel b1 d1

/-- `SqfreeExactComp` is decidable. -/
instance decSqfreeExactComp (fuel : ℕ) (D : DensePoly ℚ) : Decidable (SqfreeExactComp fuel D) := by
  unfold SqfreeExactComp; infer_instance

/-- `SqfreeExactComp` implies `SqfreeExact` through the `toPoly` exact-division bridge. -/
theorem SqfreeExactComp_to_SqfreeExact (fuel : ℕ) (D : DensePoly ℚ) :
    SqfreeExactComp fuel D → SqfreeExact fuel D := by
  intro h
  rw [SqfreeExactComp] at h
  rw [SqfreeExact]
  obtain ⟨⟨hrem, hgne⟩, hgo⟩ := h
  refine ⟨?_, GoExactComp_to_GoExact fuel _ _ hgo⟩
  have hrem0 : toPoly (DensePoly.cmodWf (cnorm D)
      (DensePoly.cgcdWf (cnorm D) (cderiv (cnorm D))).1) = 0 := by
    rw [toPoly_eq_dense, ← DensePoly.toPolyG_cnormG, hrem, DensePoly.toPolyG_nil]
  have hdiv := DensePoly.toPolyG_cmodWf (cnorm D)
    (DensePoly.cgcdWf (cnorm D) (cderiv (cnorm D))).1 hgne
  simp only [toPoly_eq_dense] at hdiv hrem0 ⊢
  rw [hrem0, add_zero] at hdiv
  exact hdiv.trans (mul_comm _ _)

end Compute

end DeepWiki.SymbolicIntegration
