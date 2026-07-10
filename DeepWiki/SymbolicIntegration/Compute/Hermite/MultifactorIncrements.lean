import DeepWiki.SymbolicIntegration.Compute.Hermite.InnerCorrectness

/-! # Hermite multifactor increment list
Defines the per-factor `gloc` increments used by the multifactor Hermite `g`-fold and proves the
conditional fold is the plain `QFun.qadd` fold over those increments. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration.Compute

/-! ### Multifactor increment list -/

/-- The per-factor `gloc` increment of `hermiteReduce`'s `g`-fold. -/
def glocIncr (fuel : ℕ) (A D : DensePoly ℚ) (Vi : DensePoly ℚ × ℕ) : QFun :=
  let Vi_pow := (List.range Vi.2).foldl (fun acc _ => cmul acc Vi.1) [1]
  let U := DensePoly.cdivWf D Vi_pow
  (hermiteInner fuel Vi.1 U (Vi.2 - 1) A QFun.qzero).1

/-- The list of `gloc` increments for the kept factors (`i ≥ 2`). -/
def glocList (fuel : ℕ) (A D : DensePoly ℚ) (factors : List (DensePoly ℚ × ℕ)) : List QFun :=
  (factors.filter (fun Vi => decide (2 ≤ Vi.2))).map (glocIncr fuel A D)

/-- The conditional `g`-fold is the plain `QFun.qadd`-fold over the increment list. -/
theorem foldl_cond_eq_foldl_glocList (fuel : ℕ) (A D : DensePoly ℚ) (factors : List (DensePoly ℚ × ℕ))
    (init : QFun) :
    factors.foldl
        (fun (gAcc : QFun) (Vi : DensePoly ℚ × ℕ) =>
          if Vi.2 ≤ 1 then gAcc
          else
            let Vi_pow := (List.range Vi.2).foldl (fun acc _ => cmul acc Vi.1) [1]
            let U := DensePoly.cdivWf D Vi_pow
            let gloc := (hermiteInner fuel Vi.1 U (Vi.2 - 1) A QFun.qzero).1
            QFun.qadd gAcc gloc)
        init
      = (glocList fuel A D factors).foldl QFun.qadd init := by
  induction factors generalizing init with
  | nil => simp [glocList]
  | cons hd tl ih =>
    rw [List.foldl_cons, glocList, List.filter_cons]
    by_cases hhd : 2 ≤ hd.2
    · simp only [decide_eq_true_eq.mpr hhd, if_true, List.map_cons, List.foldl_cons]
      have hcond : ¬ hd.2 ≤ 1 := by omega
      rw [if_neg hcond]
      have := ih (QFun.qadd init (glocIncr fuel A D hd))
      rw [glocList] at this
      rw [show (hermiteInner fuel hd.1 (DensePoly.cdivWf D
            ((List.range hd.2).foldl (fun acc _ => cmul acc hd.1) [1])) (hd.2 - 1) A QFun.qzero).1
          = glocIncr fuel A D hd from rfl]
      exact this
    · have hcond : hd.2 ≤ 1 := by omega
      rw [if_neg (by simpa using hhd : ¬ (decide (2 ≤ hd.2) = true)), if_pos hcond]
      have := ih init
      rw [glocList] at this
      exact this

/-! ### Increment denominator nonzero -/

/-- `hermiteInner` preserves nonzero accumulator denominator. -/
theorem hermiteInner_den_ne_zero (fuel : ℕ) (V U : DensePoly ℚ) (hV : toPoly V ≠ 0) :
    ∀ (j : ℕ) (A : DensePoly ℚ) (g : QFun), toPoly g.2 ≠ 0 →
      toPoly (hermiteInner fuel V U j A g).1.2 ≠ 0 := by
  intro j
  induction j with
  | zero => intro A g hg; simpa [hermiteInner] using hg
  | succ j ih =>
    intro A g hg
    rw [hermiteInner]
    rcases hBC : DensePoly.cdiophantine (cmul U (cderiv V)) V (cscale (-((j : ℚ) + 1)⁻¹) A) with ⟨B, C⟩
    simp only []
    set Vpow := (List.range (j + 1)).foldl (fun acc _ => cmul acc V) [1] with hVpowdef
    have hVpow0 : toPoly Vpow ≠ 0 := by
      rw [toPoly_hermiteInner_Vpow]; exact pow_ne_zero _ hV
    have hgnew : toPoly (QFun.qadd g (B, Vpow)).2 ≠ 0 := by
      show toPoly (cmul g.2 Vpow) ≠ 0
      simp only [toPoly_eq_dense] at hg hVpow0 ⊢
      rw [DensePoly.toPolyG_cmulG]; exact mul_ne_zero hg hVpow0
    exact ih _ _ hgnew

/-- The `glocIncr` increment has nonzero denominator when its factor is nonzero. -/
theorem glocIncr_den_ne_zero (fuel : ℕ) (A D : DensePoly ℚ) (Vi : DensePoly ℚ × ℕ) (hV : toPoly Vi.1 ≠ 0) :
    toPoly (glocIncr fuel A D Vi).2 ≠ 0 :=
  hermiteInner_den_ne_zero fuel Vi.1 _ hV (Vi.2 - 1) A QFun.qzero
    (by simpa [QFun.qzero] using
      (DensePoly.toPolyG_one_singleton_ne_zero (α := ℚ)))

end DeepWiki.SymbolicIntegration.Compute
