import DeepWiki.SymbolicIntegration.Computable.Tower.WellFounded
import DeepWiki.SymbolicIntegration.Computable.FuelFreeGcd
import DeepWiki.SymbolicIntegration.Computable.FieldGcd
import DeepWiki.SymbolicIntegration.Computable.SplitFactorWfCorrect
import DeepWiki.SymbolicIntegration.Computable.LogPartTowerSoundness
import DeepWiki.SymbolicIntegration.HermiteCorrectness

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

omit [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α] in
/-- The Yun-radical `foldl`-product denotes the list product through `toPolyG`:
`toPolyG (L.foldl cmulG init) = toPolyG init · ∏ (map toPolyG L)`. -/
theorem toPolyG_foldl_cmulG_plainList (init : CPolyG α) (L : List (CPolyG α)) :
    toPolyG (L.foldl (fun acc vi => cmulG acc vi) init)
      = toPolyG init * (L.map toPolyG).prod := by
  induction L generalizing init with
  | nil => simp
  | cons a L ih => rw [List.foldl_cons, List.map_cons, List.prod_cons, ih, toPolyG_cmulG]; ring

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **The Yun radical divides the input.** The product of `cSqfreeYunFFGWf p`'s factors divides
`toPolyG p`: the entry `b₁ = p / gcd(p, p′)` divides `p`, and the go-loop product divides `b₁`. -/
theorem prod_map_cSqfreeYunFFGWf_dvd (hgcd : GcdFFCorrect (α := α)) (p : CPolyG α)
    (hp : toPolyG p ≠ 0) :
    ((cSqfreeYunFFGWf p).map toPolyG).prod ∣ toPolyG p := by
  rw [cSqfreeYunFFGWf]
  set g := CFracGcdCoreWf.cgcdFFCoreWf p (cderivG p) with hgdef
  -- `toPolyG g ∣ toPolyG p` (associated to `gcd(p, p′)`).
  have hgp : toPolyG g ∣ toPolyG p :=
    (hgcd p (cderivG p)).dvd.trans (gcd_dvd_left (toPolyG p) (toPolyG (cderivG p)))
  have hgn : cnormG g ≠ [] := by
    intro h
    have hg0 : toPolyG g = 0 := (cisZeroG_iff g).mp (by simp [cisZeroG, h])
    exact hp (zero_dvd_iff.mp (hg0 ▸ hgp))
  -- `b₁ = cdivWf p g` divides `p` (exact division).
  have hb1 : toPolyG (cdivWf p g) * toPolyG g = toPolyG p := toPolyG_cdivWf_exact p g hgn hgp
  have hb1dvd : toPolyG (cdivWf p g) ∣ toPolyG p := ⟨toPolyG g, hb1.symm⟩
  exact (prod_map_cSqfreeYunFFGgoWf_dvd hgcd _ _ _).trans hb1dvd

omit [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α] in
/-- `toPolyG [CField.one] = 1`. -/
theorem toPolyG_one_singleton : toPolyG ([CField.one] : CPolyG α) = 1 := by
  rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_one, mul_zero, add_zero, map_one]

omit [CDiffFieldSpec α] in
/-- **The Yun radical `Dstar` divides `d`** (the `cHermiteReduceTowerGWf` squarefree radical): the
`foldl`-product of the Yun factors of `d` divides `d`, under the gcd frontier. -/
theorem toPolyG_cHermiteReduceTowerGWf_Dstar_dvd (hgcd : GcdFFCorrect (α := α)) (Dt a d : CPolyG α)
    (hd : toPolyG d ≠ 0) :
    toPolyG (cHermiteReduceTowerGWf Dt a d).2.2 ∣ toPolyG d := by
  rw [cHermiteReduceTowerGWf]
  simp only [toPolyG_cnormG, toPolyG_foldl_cmulG_plainList, toPolyG_one_singleton, one_mul]
  exact prod_map_cSqfreeYunFFGWf_dvd hgcd d hd

omit [CDiffFieldSpec α] in
/-- **The radical split `d = Dstar · W`** with `W = d / Dstar`: discharges the `hSD` hypothesis of
`hermiteTowerStep_field_identity_of_radical` for the `cHermiteReduceTowerGWf` output, under the gcd
frontier. -/
theorem toPolyG_yunRadical_split (hgcd : GcdFFCorrect (α := α)) (Dt a d : CPolyG α)
    (hd : toPolyG d ≠ 0) :
    toPolyG d = toPolyG (cHermiteReduceTowerGWf Dt a d).2.2
      * toPolyG (cdivWf d (cHermiteReduceTowerGWf Dt a d).2.2) := by
  set Dstar := (cHermiteReduceTowerGWf Dt a d).2.2 with hDstar
  have hdvd : toPolyG Dstar ∣ toPolyG d :=
    toPolyG_cHermiteReduceTowerGWf_Dstar_dvd hgcd Dt a d hd
  have hDstar0 : toPolyG Dstar ≠ 0 := fun h => hd (zero_dvd_iff.mp (h ▸ hdvd))
  have hDn : cnormG Dstar ≠ [] :=
    fun h => hDstar0 ((cisZeroG_iff Dstar).mp (by simp [cisZeroG, h]))
  have hex : toPolyG (cdivWf d Dstar) * toPolyG Dstar = toPolyG d :=
    toPolyG_cdivWf_exact d Dstar hDn hdvd
  rw [← hex, mul_comm]

/-! ### Toward the Yun multiplicity correspondence: `YunInv` under constant scaling

The tower entry `(toPolyG b₁, toPolyG d₁)` equals `C(u⁻¹) ·` the abstract `yunInv_base` pair (both
components scaled by the *same* unit `u`, where `toPolyG (cgcdFFCoreWf p p′) = C u · gcd(p, p′)` from
`GcdFFCorrect`). Since `YunInv`'s witness has a free scalar, common-constant scaling preserves it —
so the tower entry satisfies `YunInv`, launching the `yunLoopAbs_forall₂` correspondence. -/

open Classical in
/-- `YunInv` is preserved under a common nonzero-constant scaling of the working pair `(b, d)`:
`YunInv A i b d → e ≠ 0 → YunInv A i (C e · b) (C e · d)` (the witness scalar absorbs `e`). -/
theorem YunInv_smul {K : Type*} [Field K] (A : K[X]) (i : ℕ) {b d : K[X]}
    (h : YunInv A i b d) {e : K} (he : e ≠ 0) :
    YunInv A i (Polynomial.C e * b) (Polynomial.C e * d) := by
  obtain ⟨c, hc, hb, hd⟩ := h
  exact ⟨e * c, mul_ne_zero he hc, by rw [hb, ← mul_assoc, ← Polynomial.C_mul],
    by rw [hd, ← mul_assoc, ← Polynomial.C_mul]⟩

end DeepWiki.SymbolicIntegration
