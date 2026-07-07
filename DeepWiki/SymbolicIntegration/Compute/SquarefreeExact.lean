import DeepWiki.SymbolicIntegration.Compute.Correctness
import DeepWiki.SymbolicIntegration.Compute.Squarefree

/-! # Exactness certificates for computable squarefree factorization

Decidable exact-division witnesses for `csqfreeFactor` under the `toPoly : CPoly → ℚ[X]` bridge. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace Compute

/-! ### The Yun radical `Dstar` divides `D` through `toPoly` -/

/-- `cmonic q` divides `q` through `toPoly`: `toPoly (cmonic q) ∣ toPoly q`. -/
theorem toPoly_cmonic_dvd (q : CPoly) : toPoly (cmonic q) ∣ toPoly q := by
  unfold cmonic
  by_cases h : cisZero (cnorm q)
  · simp only [h, if_true]
    have hq0 : toPoly q = 0 := by
      have : cnorm q = [] := by simpa [cisZero] using h
      rw [← toPoly_cnorm, this, toPoly_nil]
    simp [hq0]
  · simp only [h, Bool.false_eq_true, if_false]
    rw [toPoly_cscale, toPoly_cnorm]
    have hc : clead (cnorm q) ≠ 0 := clead_ne_zero (by simpa [cisZero] using h)
    refine ⟨Polynomial.C (clead (cnorm q)), ?_⟩
    rw [mul_comm (Polynomial.C (clead (cnorm q))⁻¹) (toPoly q), mul_assoc, ← map_mul,
      inv_mul_cancel₀ hc, map_one, mul_one]

/-- The `toPoly`-product of the first components of a factor list: `goProd l = ∏ⱼ toPoly Vⱼ`. -/
noncomputable def goProd (l : List (CPoly × ℕ)) : ℚ[X] := (l.map (fun vi => toPoly vi.1)).prod

/-- `GoExact fuel fo b d` records exact Yun-loop divisions through `toPoly`. -/
def GoExact (fuel : ℕ) : ℕ → CPoly → CPoly → Prop
  | 0, _, _ => True
  | fo + 1, b, d =>
    if b.length ≤ 1 then True
    else
      let q := cmonic (cgcdExt fuel b d).1
      let b' := cdiv fuel b q
      let d' := csub (cdiv fuel d q) (cderiv b')
      toPoly b = toPoly q * toPoly b' ∧ GoExact fuel fo b' d'

/-- Under `GoExact`, the product emitted by `csqfreeFactor.go fuel fo b d i` divides `toPoly b`. -/
theorem goProd_dvd (fuel : ℕ) : ∀ (fo : ℕ) (b d : CPoly) (i : ℕ),
    GoExact fuel fo b d → goProd (csqfreeFactor.go fuel fo b d i) ∣ toPoly b := by
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
      set q := cmonic (cgcdExt fuel b d).1 with hqdef
      set b' := cdiv fuel b q with hb'def
      set d' := csub (cdiv fuel d q) (cderiv b') with hd'def
      have ihrest : goProd (csqfreeFactor.go fuel fo b' d' (i + 1)) ∣ toPoly b' :=
        ih b' d' (i + 1) hexrest
      by_cases hq : q.length ≤ 1
      · simp only [hq, if_true]
        exact ihrest.trans ⟨toPoly q, by rw [hexb]; ring⟩
      · simp only [hq, if_false]
        rw [goProd, List.map_cons, List.prod_cons, ← goProd, hexb]
        exact mul_dvd_mul_left (toPoly q) ihrest

/-- `goProd` realizes the radical fold: `toPoly (l.foldl (cmul · vi.1) init) = toPoly init · goProd l`. -/
theorem toPoly_foldl_cmul_fst (l : List (CPoly × ℕ)) (init : CPoly) :
    toPoly (l.foldl (fun acc vi => cmul acc vi.1) init) = toPoly init * goProd l := by
  induction l generalizing init with
  | nil => simp [goProd]
  | cons hd tl ih =>
    rw [List.foldl_cons, ih, toPoly_cmul]
    simp only [goProd, List.map_cons, List.prod_cons]
    ring

/-- The radical fold reads to `goProd`: `toPoly (l.foldl (cmul · vi.1) [1]) = goProd l`. -/
theorem toPoly_Dstar_eq (l : List (CPoly × ℕ)) :
    toPoly (l.foldl (fun acc (vi : CPoly × ℕ) => cmul acc vi.1) [1]) = goProd l := by
  rw [toPoly_foldl_cmul_fst]
  simp [toPoly_cons, toPoly_nil]

/-- One Yun step is exact when the extended gcd terminates with enough fuel. -/
theorem step_exact (fuel : ℕ) (b d : CPoly) (hbne : cnorm b ≠ [])
    (hterm : cgcdTerminates fuel b d) (hfuel : (cnorm b).length ≤ fuel) :
    toPoly b = toPoly (cmonic (cgcdExt fuel b d).1)
        * toPoly (cdiv fuel b (cmonic (cgcdExt fuel b d).1)) := by
  set q := cmonic (cgcdExt fuel b d).1 with hqdef
  have hgcd_dvd : toPoly (cgcdExt fuel b d).1 ∣ toPoly b := (toPoly_cgcdExt_dvd fuel b d hterm).1
  have hqb : toPoly q ∣ toPoly b := (toPoly_cmonic_dvd (cgcdExt fuel b d).1).trans hgcd_dvd
  have hb0 : toPoly b ≠ 0 := fun h => hbne ((cnorm_eq_nil_iff b).mpr h)
  have hq0 : toPoly q ≠ 0 := by
    intro h; rw [h, zero_dvd_iff] at hqb; exact hb0 hqb
  have hqne : cnorm q ≠ [] := fun h => hq0 ((cnorm_eq_nil_iff q).mp h)
  have hrem : toPoly (cmod fuel b q) = 0 := cmod_eq_zero_of_dvd fuel b q hqne hfuel hqb
  rw [toPoly_cdiv_of_cmod_zero fuel b q hqne hrem]; ring

/-- `SqfreeExact fuel D` bundles exact initial deflation and exact Yun-loop divisions. -/
def SqfreeExact (fuel : ℕ) (D : CPoly) : Prop :=
  let p := cnorm D
  let g := (cgcdExt fuel p (cderiv p)).1
  let b1 := cdiv fuel p g
  let d1 := csub (cdiv fuel (cderiv p) g) (cderiv b1)
  toPoly p = toPoly g * toPoly b1 ∧ GoExact fuel fuel b1 d1

/-- Under `SqfreeExact fuel D`, the Yun radical of `csqfreeFactor fuel D` divides `toPoly D`. -/
theorem toPoly_Dstar_dvd_D (fuel : ℕ) (D : CPoly) (hex : SqfreeExact fuel D) :
    toPoly ((csqfreeFactor fuel D).foldl (fun acc (vi : CPoly × ℕ) => cmul acc vi.1) [1])
      ∣ toPoly D := by
  rw [toPoly_Dstar_eq, csqfreeFactor.eq_def]
  rw [SqfreeExact] at hex
  obtain ⟨hb1, hgo⟩ := hex
  have hdvd := goProd_dvd fuel fuel
    (cdiv fuel (cnorm D) (cgcdExt fuel (cnorm D) (cderiv (cnorm D))).1)
    (csub (cdiv fuel (cderiv (cnorm D)) (cgcdExt fuel (cnorm D) (cderiv (cnorm D))).1)
      (cderiv (cdiv fuel (cnorm D) (cgcdExt fuel (cnorm D) (cderiv (cnorm D))).1))) 1 hgo
  have hb1D : toPoly (cdiv fuel (cnorm D) (cgcdExt fuel (cnorm D) (cderiv (cnorm D))).1)
      ∣ toPoly D := by
    rw [← toPoly_cnorm D, hb1]; exact Dvd.intro_left _ rfl
  exact hdvd.trans hb1D

/-! ### Computable witnesses -/

/-- `GoExactComp fuel fo b d` records vanishing `cmod` remainders for each Yun-loop division. -/
def GoExactComp (fuel : ℕ) : ℕ → CPoly → CPoly → Prop
  | 0, _, _ => True
  | fo + 1, b, d =>
    if b.length ≤ 1 then True
    else
      let q := cmonic (cgcdExt fuel b d).1
      let b' := cdiv fuel b q
      let d' := csub (cdiv fuel d q) (cderiv b')
      cnorm (cmod fuel b q) = [] ∧ cnorm q ≠ [] ∧ GoExactComp fuel fo b' d'

/-- `GoExactComp` is decidable. -/
instance decGoExactComp (fuel fo : ℕ) (b d : CPoly) : Decidable (GoExactComp fuel fo b d) := by
  induction fo generalizing b d with
  | zero => exact inferInstanceAs (Decidable True)
  | succ fo ih =>
    rw [GoExactComp]
    by_cases hb : b.length ≤ 1
    · rw [if_pos hb]; exact inferInstanceAs (Decidable True)
    · rw [if_neg hb]
      have := ih (cdiv fuel b (cmonic (cgcdExt fuel b d).1))
        (csub (cdiv fuel d (cmonic (cgcdExt fuel b d).1))
          (cderiv (cdiv fuel b (cmonic (cgcdExt fuel b d).1))))
      infer_instance

/-- `GoExactComp` implies `GoExact` by turning each vanishing `cmod` into exact division. -/
theorem GoExactComp_to_GoExact (fuel : ℕ) : ∀ (fo : ℕ) (b d : CPoly),
    GoExactComp fuel fo b d → GoExact fuel fo b d := by
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
      have hrem0 : toPoly (cmod fuel b (cmonic (cgcdExt fuel b d).1)) = 0 := by
        rw [← toPoly_cnorm, hrem, toPoly_nil]
      exact (toPoly_cdiv_of_cmod_zero fuel b (cmonic (cgcdExt fuel b d).1) hqne hrem0).trans
        (mul_comm _ _)

/-- `SqfreeExactComp fuel D` bundles vanishing `cmod` remainders for squarefree factorization. -/
def SqfreeExactComp (fuel : ℕ) (D : CPoly) : Prop :=
  let p := cnorm D
  let g := (cgcdExt fuel p (cderiv p)).1
  let b1 := cdiv fuel p g
  let d1 := csub (cdiv fuel (cderiv p) g) (cderiv b1)
  (cnorm (cmod fuel p g) = [] ∧ cnorm g ≠ []) ∧ GoExactComp fuel fuel b1 d1

/-- `SqfreeExactComp` is decidable. -/
instance decSqfreeExactComp (fuel : ℕ) (D : CPoly) : Decidable (SqfreeExactComp fuel D) := by
  unfold SqfreeExactComp; infer_instance

/-- `SqfreeExactComp` implies `SqfreeExact` through the `toPoly` exact-division bridge. -/
theorem SqfreeExactComp_to_SqfreeExact (fuel : ℕ) (D : CPoly) :
    SqfreeExactComp fuel D → SqfreeExact fuel D := by
  intro h
  rw [SqfreeExactComp] at h
  rw [SqfreeExact]
  obtain ⟨⟨hrem, hgne⟩, hgo⟩ := h
  refine ⟨?_, GoExactComp_to_GoExact fuel fuel _ _ hgo⟩
  have hrem0 : toPoly (cmod fuel (cnorm D) (cgcdExt fuel (cnorm D) (cderiv (cnorm D))).1) = 0 := by
    rw [← toPoly_cnorm, hrem, toPoly_nil]
  exact (toPoly_cdiv_of_cmod_zero fuel (cnorm D) (cgcdExt fuel (cnorm D) (cderiv (cnorm D))).1
    hgne hrem0).trans (mul_comm _ _)

end Compute

end DeepWiki.SymbolicIntegration
