import DeepWiki.SymbolicIntegration.Computable.Tower.WellFounded
import DeepWiki.SymbolicIntegration.Computable.FuelFreeGcd
import DeepWiki.SymbolicIntegration.Computable.FieldGcd
import DeepWiki.SymbolicIntegration.Computable.SplitFactorWfCorrect
import DeepWiki.SymbolicIntegration.Computable.LogPartTowerSoundness

/-! # Abstract correctness of the fuel-free Yun factorization `cSqfreeYunFFGWf`

The computable Yun loop `cSqfreeYunFFGgoWf` mirrors the abstract `yunLoopAbs`
(`HermiteCorrectness.yunLoopAbs`) step for step: each emits the monic gcd of the working pair and
recurses on the deflated pair `(b/gcd, d/gcd − (b/gcd)′)`. This file establishes the per-step bridges
through `toPolyG`, reducing to the gcd frontier `GcdFFCorrect` (unconditional at `ℚ`). -/

open Polynomial Classical

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α]

omit [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α] in
/-- `cmonicG` realizes `normalize` through `toPolyG`: `toPolyG (cmonicG q) = normalize (toPolyG q)`.
The monic associate of `toPolyG q` is its normalization. -/
theorem toPolyG_cmonicG_eq_normalize (q : CPolyG α) :
    toPolyG (cmonicG q) = normalize (toPolyG q) := by
  by_cases hq : toPolyG q = 0
  · have hcm : toPolyG (cmonicG q) = 0 := by
      have := associated_toPolyG_cmonicG q
      rwa [hq, associated_zero_iff_eq_zero] at this
    rw [hcm, hq, normalize_zero]
  · have hmonic : (toPolyG (cmonicG q)).Monic := monic_toPolyG_cmonicG q hq
    have hassoc : Associated (toPolyG (cmonicG q)) (toPolyG q) := associated_toPolyG_cmonicG q
    rw [← hmonic.normalize_eq_self, normalize_eq_normalize_iff_associated.mpr hassoc]

omit [CDiffField α] [CDiffFieldSpec α] in
/-- The emitted Yun factor denotes the exact (monic) gcd: under the gcd frontier,
`toPolyG (cmonicG (cgcdFFCoreWf b d)) = gcd (toPolyG b) (toPolyG d)`. -/
theorem toPolyG_yunEmit_eq_gcd (hgcd : GcdFFCorrect (α := α)) (b d : CPolyG α) :
    toPolyG (cmonicG (CFracGcdCoreWf.cgcdFFCoreWf b d)) = gcd (toPolyG b) (toPolyG d) := by
  rw [toPolyG_cmonicG_eq_normalize, normalize_eq_normalize_iff_associated.mpr (hgcd b d),
    normalize_gcd]

/-- Exact quotient reading: from `X·g = b` with `g ≠ 0` in `K[X]`, `X = b / g`. -/
theorem eq_ediv_of_mul_eq {K : Type*} [Field K] {X g b : K[X]} (hg : g ≠ 0) (h : X * g = b) :
    X = b / g := by
  have hdvd : g ∣ b := ⟨X, by rw [← h, mul_comm]⟩
  have hcancel : g * (b / g) = b := EuclideanDomain.mul_div_cancel' hg hdvd
  exact (mul_left_cancel₀ hg (by rw [hcancel, ← h, mul_comm])).symm

omit [CDiffField α] [CDiffFieldSpec α] in
/-- The deflated first component denotes `b / gcd(b,d)` (the `yunLoopAbs` recursion), under the gcd
frontier: `toPolyG (cdivWf b (cmonicG (cgcdFFCoreWf b d))) = toPolyG b / gcd (toPolyG b) (toPolyG d)`. -/
theorem toPolyG_yunDeflate_fst (hgcd : GcdFFCorrect (α := α)) (b d : CPolyG α)
    (hb : toPolyG b ≠ 0) :
    toPolyG (cdivWf b (cmonicG (CFracGcdCoreWf.cgcdFFCoreWf b d)))
      = toPolyG b / gcd (toPolyG b) (toPolyG d) := by
  set p := cmonicG (CFracGcdCoreWf.cgcdFFCoreWf b d) with hpdef
  have hp : toPolyG p = gcd (toPolyG b) (toPolyG d) := toPolyG_yunEmit_eq_gcd hgcd b d
  have hgne : gcd (toPolyG b) (toPolyG d) ≠ 0 :=
    fun h => hb (zero_dvd_iff.mp (h ▸ gcd_dvd_left (toPolyG b) (toPolyG d)))
  have hpn : cnormG p ≠ [] := by
    intro h; apply hgne; rw [← hp]; exact (cisZeroG_iff p).mp (by simp [cisZeroG, h])
  have hdvd : toPolyG p ∣ toPolyG b := by rw [hp]; exact gcd_dvd_left _ _
  have hex : toPolyG (cdivWf b p) * toPolyG p = toPolyG b := toPolyG_cdivWf_exact b p hpn hdvd
  rw [hp] at hex
  exact eq_ediv_of_mul_eq hgne hex

omit [CDiffField α] [CDiffFieldSpec α] in
/-- The deflated second component denotes `d / gcd(b,d) − (b / gcd(b,d))′` (the `yunLoopAbs`
recursion), under the gcd frontier. -/
theorem toPolyG_yunDeflate_snd (hgcd : GcdFFCorrect (α := α)) (b d : CPolyG α)
    (hb : toPolyG b ≠ 0) :
    toPolyG (csubG (cdivWf d (cmonicG (CFracGcdCoreWf.cgcdFFCoreWf b d)))
        (cderivG (cdivWf b (cmonicG (CFracGcdCoreWf.cgcdFFCoreWf b d)))))
      = toPolyG d / gcd (toPolyG b) (toPolyG d)
        - derivative (toPolyG b / gcd (toPolyG b) (toPolyG d)) := by
  set p := cmonicG (CFracGcdCoreWf.cgcdFFCoreWf b d) with hpdef
  have hp : toPolyG p = gcd (toPolyG b) (toPolyG d) := toPolyG_yunEmit_eq_gcd hgcd b d
  have hgne : gcd (toPolyG b) (toPolyG d) ≠ 0 :=
    fun h => hb (zero_dvd_iff.mp (h ▸ gcd_dvd_left (toPolyG b) (toPolyG d)))
  have hpn : cnormG p ≠ [] := by
    intro h; apply hgne; rw [← hp]; exact (cisZeroG_iff p).mp (by simp [cisZeroG, h])
  have hdvdd : toPolyG p ∣ toPolyG d := by rw [hp]; exact gcd_dvd_right _ _
  have hexd : toPolyG (cdivWf d p) * toPolyG p = toPolyG d := toPolyG_cdivWf_exact d p hpn hdvdd
  rw [hp] at hexd
  have hd' : toPolyG (cdivWf d p) = toPolyG d / gcd (toPolyG b) (toPolyG d) :=
    eq_ediv_of_mul_eq hgne hexd
  rw [toPolyG_csubG, toPolyG_cderivG, hd', toPolyG_yunDeflate_fst hgcd b d hb]

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **The Yun radical divides the working polynomial.** The product of all Yun factors emitted from
`(b, d)` divides `toPolyG b`: each factor is `gcd(bⱼ, dⱼ)` dividing `bⱼ`, and the product telescopes
through the deflation. -/
theorem prod_map_cSqfreeYunFFGgoWf_dvd (hgcd : GcdFFCorrect (α := α)) :
    ∀ (fo : ℕ) (b d : CPolyG α),
      ((cSqfreeYunFFGgoWf fo b d).map toPolyG).prod ∣ toPolyG b := by
  intro fo
  induction fo with
  | zero => intro b d; simp [cSqfreeYunFFGgoWf]
  | succ fo ih =>
    intro b d
    rw [cSqfreeYunFFGgoWf]
    by_cases hdeg : cdegG b = 0
    · rw [if_pos hdeg]; simp
    · rw [if_neg hdeg]
      have hbne : toPolyG b ≠ 0 := by
        intro h; exact hdeg (by rw [cdegG_eq_natDegree, h, natDegree_zero])
      have hgne : gcd (toPolyG b) (toPolyG d) ≠ 0 :=
        fun h => hbne (zero_dvd_iff.mp (h ▸ gcd_dvd_left (toPolyG b) (toPolyG d)))
      rw [List.map_cons, List.prod_cons,
        toPolyG_yunEmit_eq_gcd hgcd b d]
      have hih := ih (cdivWf b (cmonicG (CFracGcdCoreWf.cgcdFFCoreWf b d)))
        (csubG (cdivWf d (cmonicG (CFracGcdCoreWf.cgcdFFCoreWf b d)))
          (cderivG (cdivWf b (cmonicG (CFracGcdCoreWf.cgcdFFCoreWf b d)))))
      rw [toPolyG_yunDeflate_fst hgcd b d hbne] at hih
      calc gcd (toPolyG b) (toPolyG d)
              * ((cSqfreeYunFFGgoWf fo (cdivWf b (cmonicG (CFracGcdCoreWf.cgcdFFCoreWf b d)))
                  (csubG (cdivWf d (cmonicG (CFracGcdCoreWf.cgcdFFCoreWf b d)))
                    (cderivG (cdivWf b (cmonicG (CFracGcdCoreWf.cgcdFFCoreWf b d)))))).map
                  toPolyG).prod
            ∣ gcd (toPolyG b) (toPolyG d) * (toPolyG b / gcd (toPolyG b) (toPolyG d)) :=
              mul_dvd_mul_left _ hih
        _ = toPolyG b :=
              EuclideanDomain.mul_div_cancel' hgne (gcd_dvd_left (toPolyG b) (toPolyG d))

end DeepWiki.SymbolicIntegration
