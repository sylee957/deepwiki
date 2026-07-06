import DeepWiki.SymbolicIntegration.Computable.Tower.WellFounded
import DeepWiki.SymbolicIntegration.Computable.FuelFreeGcd
import DeepWiki.SymbolicIntegration.Computable.FieldGcd
import DeepWiki.SymbolicIntegration.Computable.SplitFactorWfCorrect
import DeepWiki.SymbolicIntegration.Computable.LogPartTowerSoundness
import DeepWiki.SymbolicIntegration.Computable.SquarefreeDecomposition
import DeepWiki.SymbolicIntegration.SquarefreeFactorization
import DeepWiki.SymbolicIntegration.HermiteCorrectness

/-! # Abstract correctness of the fuel-free Yun factorization `cSqfreeYunFFGWf`

The computable Yun loop `cSqfreeYunFFGgoWf` mirrors the squarefree theory's abstract `yunLoopAbs`
step for step: each emits the monic gcd of the working pair and
recurses on the deflated pair `(b/gcd, d/gcd − (b/gcd)′)`. This file establishes the per-step bridges
through `toPolyG`, reducing to the gcd frontier `GcdFFCorrect` (unconditional at `ℚ`). -/

open Polynomial Classical

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α]

/-- **`prodPow` splits as the plain product times the zipIdx-power product**:
`prodPow s M = (∏ mₖ^s) · ∏ₖ mₖ^k` — separating the uniform `s`-th powers from the extra `k`-fold
factors. Bridges the reconstruction `prodPow 1 (Yun factors) ~ d` to the `∏ vk^idx` divisor form. -/
theorem prodPow_eq_prod_mul_zipIdxPow {K : Type*} [Field K] (s : ℕ) (M : List K[X]) :
    prodPow s M = (M.map (· ^ s)).prod * (M.zipIdx.map (fun x => x.1 ^ x.2)).prod := by
  induction M generalizing s with
  | nil => simp [prodPow]
  | cons a es ih =>
    rw [prodPow, ih (s + 1), List.map_cons, List.prod_cons, List.zipIdx_cons', List.map_cons,
      List.prod_cons, pow_zero, one_mul]
    have hQ : (es.zipIdx.map (fun x => x.1 ^ x.2)).prod * es.prod
        = ((es.zipIdx.map (Prod.map id (· + 1))).map (fun x => x.1 ^ x.2)).prod := by
      rw [List.map_map]
      have hcomp : (fun x : K[X] × ℕ => x.1 ^ x.2) ∘ (Prod.map id (· + 1))
          = fun x : K[X] × ℕ => x.1 ^ x.2 * x.1 := by
        funext x; simp [Prod.map, pow_succ]
      have hfst : es.zipIdx.map (fun x : K[X] × ℕ => x.1) = es := List.zipIdx_map_fst 0 es
      rw [hcomp, List.prod_map_mul, hfst]
    have hP : (es.map (· ^ (s + 1))).prod = (es.map (· ^ s)).prod * es.prod := by
      have : (fun e : K[X] => e ^ (s + 1)) = fun e : K[X] => e ^ s * e := by
        funext e; rw [pow_succ]
      rw [this, List.prod_map_mul, List.map_id']
    rw [hP, ← hQ]; ring

/-- Filtering out list entries whose image under `g` is `1` leaves the mapped product unchanged. -/
theorem prod_map_filter_eq_of_one {M : Type*} [CommMonoid M] {β : Type*} (l : List β) (p : β → Bool)
    (g : β → M) (h : ∀ x ∈ l, ¬ p x → g x = 1) :
    ((l.filter p).map g).prod = (l.map g).prod := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.filter_cons, List.map_cons, List.prod_cons]
    by_cases hp : p a
    · simp only [hp, if_true, List.map_cons, List.prod_cons,
        ih (fun x hx => h x (List.mem_cons_of_mem a hx))]
    · simp only [hp, Bool.false_eq_true, if_false, ih (fun x hx => h x (List.mem_cons_of_mem a hx)),
        h a (List.mem_cons_self ..) (by simp [hp]), one_mul]

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **`prodPow 1` of the tower Yun factors = the radical product times the `∏vk^idx` divisor**:
`prodPow 1 L = L.prod · FiltProd` where `L = map toPolyG (cSqfreeYunFFGWf d)` and `FiltProd` drops the
multiplicity-1 factors (which contribute `vk^0 = 1`). Plumbs the reconstruction `d ~ prodPow 1 L`
into the `hWdvd` divisor form. -/
theorem prodPow_one_cSqfreeYunFFGWf (d : CPolyG α) :
    prodPow 1 ((cSqfreeYunFFGWf d).map toPolyG)
      = ((cSqfreeYunFFGWf d).map toPolyG).prod
        * (((cSqfreeYunFFGWf d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1))).map
            (fun x => toPolyG x.1 ^ x.2)).prod := by
  rw [prodPow_eq_prod_mul_zipIdxPow]
  have hsnd : (((cSqfreeYunFFGWf d).map toPolyG).zipIdx.map (fun x => x.1 ^ x.2)).prod
      = ((cSqfreeYunFFGWf d).zipIdx.map (fun x => toPolyG x.1 ^ x.2)).prod := by
    rw [List.zipIdx_map, List.map_map]; rfl
  congr 1
  · simp only [pow_one, List.map_id']
  · rw [hsnd, ← prod_map_filter_eq_of_one ((cSqfreeYunFFGWf d).zipIdx)
      (fun x => ¬ (x.2 + 1 ≤ 1)) (fun x => toPolyG x.1 ^ x.2) (fun x _ hx => ?_)]
    have hx0 : x.2 = 0 := by
      by_contra hne
      apply hx
      have hle : ¬ (x.2 + 1 ≤ 1) := by omega
      simpa using hle
    rw [hx0, pow_zero]

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
  | cons a L ih => simp only [List.foldl_cons, List.map_cons, List.prod_cons, ih, denote]; ring

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
  simp only [denote, toPolyG_foldl_cmulG_plainList, toPolyG_one_singleton, one_mul]
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

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **The tower Yun entry satisfies the abstract invariant.** For `A = toPolyG p ≠ 0` with primitive
part `≠ 0`, the entry pair `(p/g, p′/g − (p/g)′)` (`g = cgcdFFCoreWf p p′`) satisfies
`YunInv A 1` — it is `C(k⁻¹)·` the `yunInv_base` pair, where `toPolyG g = C k·gcd(A, A′)`. Launches the
`yunLoopAbs_forall₂` correspondence. -/
theorem toPolyG_yunEntry_YunInv [CharZero (CFieldSpec.K α)] (hgcd : GcdFFCorrect (α := α))
    (p : CPolyG α) (hp0 : toPolyG p ≠ 0) (hpp : (toPolyG p).primPart ≠ 0) :
    YunInv (toPolyG p) 1
      (toPolyG (cdivWf p (CFracGcdCoreWf.cgcdFFCoreWf p (cderivG p))))
      (toPolyG (csubG (cdivWf (cderivG p) (CFracGcdCoreWf.cgcdFFCoreWf p (cderivG p)))
        (cderivG (cdivWf p (CFracGcdCoreWf.cgcdFFCoreWf p (cderivG p)))))) := by
  set A := toPolyG p with hAdef
  set g := CFracGcdCoreWf.cgcdFFCoreWf p (cderivG p) with hgdef
  have hA'poly : toPolyG (cderivG p) = derivative A := by rw [toPolyG_cderivG, hAdef]
  set G := gcd A (derivative A) with hGdef
  have hG0 : G ≠ 0 := fun h => hp0 (zero_dvd_iff.mp (h ▸ gcd_dvd_left A (derivative A)))
  -- `toPolyG g ~ G`, hence `toPolyG g = C k · G` for a unit `k`.
  have hassoc : Associated (toPolyG g) G := by
    have := hgcd p (cderivG p); rwa [hA'poly] at this
  obtain ⟨u, hu⟩ := hassoc.symm
  obtain ⟨k, hkunit, hkC⟩ := Polynomial.isUnit_iff.mp u.isUnit
  have hk0 : k ≠ 0 := isUnit_iff_ne_zero.mp hkunit
  have hgval : toPolyG g = Polynomial.C k * G := by rw [← hu, ← hkC]; ring
  -- divisibility of `toPolyG g` into `A` and `A′`.
  have hgn : cnormG g ≠ [] := by
    intro h
    exact hG0 (zero_dvd_iff.mp (((cisZeroG_iff g).mp (by simp [cisZeroG, h])) ▸ hassoc.dvd))
  have hgA : toPolyG g ∣ A := hassoc.dvd.trans (gcd_dvd_left A (derivative A))
  have hgA' : toPolyG g ∣ derivative A :=
    hassoc.dvd.trans (gcd_dvd_right A (derivative A))
  -- the two scaling equalities: `b₁ = C(k⁻¹)·(A/G)`, first residual term `q′ = C(k⁻¹)·(A′/G)`.
  have hkinv : Polynomial.C k⁻¹ * Polynomial.C k = 1 := by
    rw [← Polynomial.C_mul, inv_mul_cancel₀ hk0, Polynomial.C_1]
  -- from `q · toPolyG g = x`: `x/G = q · C k`.
  have hb1ex : toPolyG (cdivWf p g) * toPolyG g = A := toPolyG_cdivWf_exact p g hgn hgA
  have hq'ex : toPolyG (cdivWf (cderivG p) g) * toPolyG g = derivative A := by
    have h := toPolyG_cdivWf_exact (cderivG p) g hgn (by rw [hA'poly]; exact hgA')
    rwa [hA'poly] at h
  have hAG : A / G = toPolyG (cdivWf p g) * Polynomial.C k :=
    (eq_ediv_of_mul_eq hG0 (by rw [← hb1ex, hgval]; ring)).symm
  have hA'G : derivative A / G = toPolyG (cdivWf (cderivG p) g) * Polynomial.C k :=
    (eq_ediv_of_mul_eq hG0 (by rw [← hq'ex, hgval]; ring)).symm
  have heqb : toPolyG (cdivWf p g) = Polynomial.C k⁻¹ * (A / G) := by
    rw [hAG, show Polynomial.C k⁻¹ * (toPolyG (cdivWf p g) * Polynomial.C k)
        = toPolyG (cdivWf p g) * (Polynomial.C k⁻¹ * Polynomial.C k) from by ring, hkinv, mul_one]
  -- assemble `d₁`.
  have heqd : toPolyG (csubG (cdivWf (cderivG p) g) (cderivG (cdivWf p g)))
      = Polynomial.C k⁻¹ * (derivative A / G - derivative (A / G)) := by
    rw [toPolyG_csubG, toPolyG_cderivG, heqb, derivative_C_mul, mul_sub, hA'G,
      show Polynomial.C k⁻¹ * (toPolyG (cdivWf (cderivG p) g) * Polynomial.C k)
        = toPolyG (cdivWf (cderivG p) g) * (Polynomial.C k⁻¹ * Polynomial.C k) from by ring,
      hkinv, mul_one]
  rw [heqb, heqd]
  exact YunInv_smul A 1 (yunInv_base A hp0 hpp) (inv_ne_zero hk0)

/-- `yunLoopAbs`'s spec parameters `A` and `i` are phantom: the emitted list depends only on the pair
and step count. -/
theorem yunLoopAbs_irrelevant {K : Type*} [Field K] (A A' : K[X]) :
    ∀ (n : ℕ) (p : K[X] × K[X]) (i j : ℕ), yunLoopAbs A p i n = yunLoopAbs A' p j n := by
  intro n
  induction n with
  | zero => intro p i j; rfl
  | succ n ih => intro p i j; obtain ⟨b, d⟩ := p; simp only [yunLoopAbs]; rw [ih _ (i + 1) (j + 1)]

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **The tower go-loop denotes the abstract `yunLoopAbs`** (run for its own length): the deflated
state matches `yunLoopAbs`'s recursion (`yunDeflate_fst`/`_snd`) and the emitted factor is the monic
gcd (`yunEmit_eq_gcd`). Under the gcd frontier; `i` phantom so any start index works. -/
theorem map_toPolyG_cSqfreeYunFFGgoWf_eq (hgcd : GcdFFCorrect (α := α)) :
    ∀ (fo : ℕ) (b d : CPolyG α),
      (cSqfreeYunFFGgoWf fo b d).map toPolyG
        = yunLoopAbs (0 : (CFieldSpec.K α)[X]) (toPolyG b, toPolyG d) 1
            (cSqfreeYunFFGgoWf fo b d).length := by
  intro fo
  induction fo with
  | zero => intro b d; simp [cSqfreeYunFFGgoWf, yunLoopAbs]
  | succ fo ih =>
    intro b d
    rw [cSqfreeYunFFGgoWf]
    by_cases hdeg : cdegG b = 0
    · rw [if_pos hdeg]; simp [yunLoopAbs]
    · rw [if_neg hdeg]
      have hbne : toPolyG b ≠ 0 := fun h => hdeg (by rw [cdegG_eq_natDegree, h, natDegree_zero])
      rw [List.map_cons, List.length_cons, toPolyG_yunEmit_eq_gcd hgcd b d]
      -- unfold one `yunLoopAbs` step on the RHS.
      simp only [yunLoopAbs]
      -- head gcds agree; tails via the deflate bridges + IH + `i`-irrelevance.
      congr 1
      rw [ih (cdivWf b (cmonicG (CFracGcdCoreWf.cgcdFFCoreWf b d)))
            (csubG (cdivWf d (cmonicG (CFracGcdCoreWf.cgcdFFCoreWf b d)))
              (cderivG (cdivWf b (cmonicG (CFracGcdCoreWf.cgcdFFCoreWf b d))))),
        toPolyG_yunDeflate_fst hgcd b d hbne, toPolyG_yunDeflate_snd hgcd b d hbne]
      exact yunLoopAbs_irrelevant _ _ _ _ _ _

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **The tower Yun factors correspond to `sqfreeFactPart`.** Under the gcd frontier, the factors of
`cSqfreeYunFFGWf p` are `Forall₂ Associated` to `[sqfreeFactPart A 1, sqfreeFactPart A 2, …]`
(`A = toPolyG p`) — the tower Yun factorization denotes the abstract one. Combines the go-loop
denotation (`map_toPolyG_cSqfreeYunFFGgoWf_eq`) with abstract loop correctness (`yunLoopAbs_forall₂`),
launched from the entry invariant (`toPolyG_yunEntry_YunInv`). -/
theorem cSqfreeYunFFGWf_forall₂ [CharZero (CFieldSpec.K α)] (hgcd : GcdFFCorrect (α := α))
    (p : CPolyG α) (hp0 : toPolyG p ≠ 0) (hpp : (toPolyG p).primPart ≠ 0) :
    List.Forall₂ Associated ((cSqfreeYunFFGWf p).map toPolyG)
      ((List.range (cSqfreeYunFFGWf p).length).map
        (fun j => sqfreeFactPart (toPolyG p) (1 + j))) := by
  rw [cSqfreeYunFFGWf]
  set b₁ := cdivWf p (CFracGcdCoreWf.cgcdFFCoreWf p (cderivG p)) with hb1
  set d₁ := csubG (cdivWf (cderivG p) (CFracGcdCoreWf.cgcdFFCoreWf p (cderivG p)))
    (cderivG (cdivWf p (CFracGcdCoreWf.cgcdFFCoreWf p (cderivG p)))) with hd1
  set L := (cSqfreeYunFFGgoWf (cyunBoundG p) b₁ d₁).length with hL
  have hinv : YunInv (toPolyG p) 1 (toPolyG b₁) (toPolyG d₁) :=
    toPolyG_yunEntry_YunInv hgcd p hp0 hpp
  have hmap := map_toPolyG_cSqfreeYunFFGgoWf_eq hgcd (cyunBoundG p) b₁ d₁
  rw [← hL] at hmap
  rw [hmap, yunLoopAbs_irrelevant (0 : (CFieldSpec.K α)[X]) (toPolyG p) L (toPolyG b₁, toPolyG d₁) 1 1]
  exact yunLoopAbs_forall₂ (toPolyG p) hpp L 1 (toPolyG b₁) (toPolyG d₁) (le_refl 1) hinv

omit [CDiffField α] [CDiffFieldSpec α] in
/-- The `j`-th tower Yun factor is `Associated (sqfreeFactPart (toPolyG p) (1 + j))` (per-index form of
the correspondence). -/
theorem cSqfreeYunFFGWf_get_assoc [CharZero (CFieldSpec.K α)] (hgcd : GcdFFCorrect (α := α))
    (p : CPolyG α) (hp0 : toPolyG p ≠ 0) (hpp : (toPolyG p).primPart ≠ 0)
    (j : ℕ) (hj : j < (cSqfreeYunFFGWf p).length) :
    Associated (toPolyG ((cSqfreeYunFFGWf p).get ⟨j, hj⟩))
      (sqfreeFactPart (toPolyG p) (1 + j)) := by
  have hf := cSqfreeYunFFGWf_forall₂ hgcd p hp0 hpp
  have hjm : j < ((cSqfreeYunFFGWf p).map toPolyG).length := by rwa [List.length_map]
  have hjr : j < ((List.range (cSqfreeYunFFGWf p).length).map
      (fun j => sqfreeFactPart (toPolyG p) (1 + j))).length := by
    rw [List.length_map, List.length_range]; exact hj
  have hg := hf.get hjm hjr
  simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range] at hg ⊢
  exact hg

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **Distinct tower Yun factors are relatively prime.** From the `sqfreeFactPart` correspondence and
`sqfreeFactPart_isRelPrime` (distinct multiplicities are coprime). -/
theorem cSqfreeYunFFGWf_isRelPrime [CharZero (CFieldSpec.K α)] (hgcd : GcdFFCorrect (α := α))
    (p : CPolyG α) (hp0 : toPolyG p ≠ 0) (hpp : (toPolyG p).primPart ≠ 0)
    {j k : ℕ} (hj : j < (cSqfreeYunFFGWf p).length) (hk : k < (cSqfreeYunFFGWf p).length)
    (hjk : j ≠ k) :
    IsRelPrime (toPolyG ((cSqfreeYunFFGWf p).get ⟨j, hj⟩))
      (toPolyG ((cSqfreeYunFFGWf p).get ⟨k, hk⟩)) := by
  have haj := cSqfreeYunFFGWf_get_assoc hgcd p hp0 hpp j hj
  have hak := cSqfreeYunFFGWf_get_assoc hgcd p hp0 hpp k hk
  have hne : (1 + j) ≠ (1 + k) := by omega
  exact fun d hda hdb =>
    (sqfreeFactPart_isRelPrime (toPolyG p) hne) (hda.trans haj.dvd) (hdb.trans hak.dvd)

open Classical UniqueFactorizationMonoid in
/-- `sqfreeFactPart A i ^ i ∣ A.primPart`: each squarefree part to its own multiplicity divides the
primitive part (from the `∏ Aₘ^m ~ pp(A)` decomposition; the `i`-absent case gives `Aᵢ = 1`). -/
theorem sqfreeFactPart_pow_self_dvd_primPart {K : Type*} [Field K] (A : K[X])
    (hA : A.primPart ≠ 0) (i : ℕ) : sqfreeFactPart A i ^ i ∣ A.primPart := by
  have hassoc := primPart_associated_prod_sqfreeFactPart A hA
  by_cases hi : i ∈ (normalizedFactors A.primPart).toFinset.image
      (fun P => (normalizedFactors A.primPart).count P)
  · exact (Finset.dvd_prod_of_mem (fun m => sqfreeFactPart A m ^ m) hi).trans hassoc.symm.dvd
  · have h1 : sqfreeFactPart A i = 1 := by
      rw [sqfreeFactPart, Finset.prod_eq_one]
      intro P hP
      rw [Finset.mem_filter] at hP
      exact absurd (hP.2 ▸ Finset.mem_image_of_mem _ hP.1) hi
    rw [h1, one_pow]; exact one_dvd _

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **Each tower Yun factor to its multiplicity divides `d`.** For the factor at index `j` (multiplicity
`1 + j`), `toPolyG (factor) ^ (1 + j) ∣ toPolyG p` — the `hpow` hypothesis of the pole-cancellation. -/
theorem cSqfreeYunFFGWf_pow_dvd [CharZero (CFieldSpec.K α)] (hgcd : GcdFFCorrect (α := α))
    (p : CPolyG α) (hp0 : toPolyG p ≠ 0) (hpp : (toPolyG p).primPart ≠ 0)
    (j : ℕ) (hj : j < (cSqfreeYunFFGWf p).length) :
    toPolyG ((cSqfreeYunFFGWf p).get ⟨j, hj⟩) ^ (1 + j) ∣ toPolyG p := by
  have haj := cSqfreeYunFFGWf_get_assoc hgcd p hp0 hpp j hj
  exact ((pow_dvd_pow_of_dvd haj.dvd (1 + j)).trans
    (sqfreeFactPart_pow_self_dvd_primPart (toPolyG p) hpp (1 + j))).trans (toPolyG p).primPart_dvd

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **Each tower Yun factor is squarefree** (from the `sqfreeFactPart` correspondence + squarefreeness
of `sqfreeFactPart`, transferred across associates). -/
theorem cSqfreeYunFFGWf_squarefree [CharZero (CFieldSpec.K α)] (hgcd : GcdFFCorrect (α := α))
    (p : CPolyG α) (hp0 : toPolyG p ≠ 0) (hpp : (toPolyG p).primPart ≠ 0)
    (j : ℕ) (hj : j < (cSqfreeYunFFGWf p).length) :
    Squarefree (toPolyG ((cSqfreeYunFFGWf p).get ⟨j, hj⟩)) := by
  have haj := cSqfreeYunFFGWf_get_assoc hgcd p hp0 hpp j hj
  exact fun y hy => sqfreeFactPart_squarefree (toPolyG p) (1 + j) y (hy.trans haj.dvd)

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **Each tower Yun factor is nonzero** (from the correspondence + `sqfreeFactPart_ne_zero`). -/
theorem cSqfreeYunFFGWf_get_ne_zero [CharZero (CFieldSpec.K α)] (hgcd : GcdFFCorrect (α := α))
    (p : CPolyG α) (hp0 : toPolyG p ≠ 0) (hpp : (toPolyG p).primPart ≠ 0)
    (j : ℕ) (hj : j < (cSqfreeYunFFGWf p).length) :
    toPolyG ((cSqfreeYunFFGWf p).get ⟨j, hj⟩) ≠ 0 := fun h0 =>
  sqfreeFactPart_ne_zero (toPolyG p) (1 + j)
    ((cSqfreeYunFFGWf_get_assoc hgcd p hp0 hpp j hj).eq_zero_iff.mp h0)

omit [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α] in
/-- `u·v^i = d` where `u = cdivWf d (v^i)`, given `v^i ∣ d` and `v ≠ 0` (the `hud` input of the
per-factor Hermite step). -/
theorem toPolyG_cdivWf_pow_mul (d v : CPolyG α) (i : ℕ) (hv : toPolyG v ≠ 0)
    (hdvd : toPolyG v ^ i ∣ toPolyG d) :
    toPolyG (cdivWf d (cpowG v i)) * toPolyG v ^ i = toPolyG d := by
  have hcn : cnormG (cpowG v i) ≠ [] := by
    intro h
    have hz : toPolyG (cpowG v i) = 0 := (cisZeroG_iff _).mp (by simp [cisZeroG, h])
    rw [toPolyG_cpowG] at hz; exact pow_ne_zero i hv hz
  have hd2 : toPolyG (cpowG v i) ∣ toPolyG d := by rw [toPolyG_cpowG]; exact hdvd
  have h := toPolyG_cdivWf_exact d (cpowG v i) hcn hd2
  rwa [toPolyG_cpowG] at h

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **Each tower Yun factor is coprime to its derivative** (squarefree ⟹ coprime to `v'`, char 0). -/
theorem cSqfreeYunFFGWf_coprime_deriv [CharZero (CFieldSpec.K α)] (hgcd : GcdFFCorrect (α := α))
    (p : CPolyG α) (hp0 : toPolyG p ≠ 0) (hpp : (toPolyG p).primPart ≠ 0)
    (j : ℕ) (hj : j < (cSqfreeYunFFGWf p).length) :
    IsCoprime (toPolyG ((cSqfreeYunFFGWf p).get ⟨j, hj⟩))
      (derivative (toPolyG ((cSqfreeYunFFGWf p).get ⟨j, hj⟩))) :=
  squarefree_iff_isCoprime_derivative.mp (cSqfreeYunFFGWf_squarefree hgcd p hp0 hpp j hj)

open UniqueFactorizationMonoid in
omit [CDiffField α] [CDiffFieldSpec α] in
/-- **The Yun go-loop runs at least `maxmult − (i−1)` steps.** With `YunInv (toPolyG p) i` the working
`b` is `C c · squarefreePart (deflation (toPolyG p) (i−1))`, so `cdegG b = 0 ⟺ maxmult ≤ i−1`
(`squarefreePart_deflation_natDegree_eq_zero_iff_maxmult`); each non-terminal step deflates to `i+1`
(`yunStep_preserves` + the deflate bridges), so the emitted list has length `≥ maxmult − (i−1)`. -/
theorem length_cSqfreeYunFFGgoWf_ge [CharZero (CFieldSpec.K α)] (hgcd : GcdFFCorrect (α := α))
    (p : CPolyG α) (hpp : (toPolyG p).primPart ≠ 0) :
    ∀ (fo i : ℕ) (b d : CPolyG α), 1 ≤ i →
      YunInv (toPolyG p) i (toPolyG b) (toPolyG d) →
      (normalizedFactors (toPolyG p).primPart).toFinset.sup
          (fun P => (normalizedFactors (toPolyG p).primPart).count P) - (i - 1) ≤ fo →
      (normalizedFactors (toPolyG p).primPart).toFinset.sup
          (fun P => (normalizedFactors (toPolyG p).primPart).count P) - (i - 1)
        ≤ (cSqfreeYunFFGgoWf fo b d).length := by
  set M := (normalizedFactors (toPolyG p).primPart).toFinset.sup
    (fun P => (normalizedFactors (toPolyG p).primPart).count P) with hM
  intro fo
  induction fo with
  | zero => intro i b d _ _ hfo; simp only [Nat.le_zero] at hfo; rw [hfo]; exact Nat.zero_le _
  | succ fo ih =>
    intro i b d hi hinv hfo
    rw [cSqfreeYunFFGgoWf]
    by_cases hdeg : cdegG b = 0
    · rw [if_pos hdeg]
      obtain ⟨c, hc, hb, _⟩ := hinv
      have hMle : M ≤ i - 1 := by
        rw [cdegG_eq_natDegree, hb, natDegree_C_mul hc] at hdeg
        rw [hM, ← squarefreePart_deflation_natDegree_eq_zero_iff_maxmult (toPolyG p) (i - 1) hpp]
        exact hdeg
      simp only [List.length_nil]; omega
    · rw [if_neg hdeg]
      have hbne : toPolyG b ≠ 0 := by
        intro h0; apply hdeg; rw [cdegG_eq_natDegree, h0, natDegree_zero]
      have hMgt : i ≤ M := by
        by_contra hlt
        obtain ⟨c, hc, hb, _⟩ := hinv
        apply hdeg
        rw [cdegG_eq_natDegree, hb, natDegree_C_mul hc,
          show Babs (toPolyG p) i = squarefreePart (deflation (toPolyG p) (i - 1)) from rfl,
          squarefreePart_deflation_natDegree_eq_zero_iff_maxmult (toPolyG p) (i - 1) hpp, ← hM]
        omega
      have hinv' : YunInv (toPolyG p) (i + 1)
          (toPolyG (cdivWf b (cmonicG (CFracGcdCoreWf.cgcdFFCoreWf b d))))
          (toPolyG (csubG (cdivWf d (cmonicG (CFracGcdCoreWf.cgcdFFCoreWf b d)))
            (cderivG (cdivWf b (cmonicG (CFracGcdCoreWf.cgcdFFCoreWf b d)))))) := by
        rw [toPolyG_yunDeflate_fst hgcd b d hbne, toPolyG_yunDeflate_snd hgcd b d hbne]
        exact (yunStep_preserves (toPolyG p) i hi hpp hinv).2
      have hih := ih (i + 1) _ _ (by omega) hinv' (by omega)
      rw [List.length_cons]
      omega

open UniqueFactorizationMonoid in
omit [CDiffField α] [CDiffFieldSpec α] in
/-- **The Yun factorization has length `≥ maxmult`.** The entry runs the go-loop from `i = 1` with
fuel `cyunBoundG p ≥ maxmult` (`sup_count_le_natDegree_primPart` + `primPart_dvd` +
`length_cnormG_of_ne`), so `length_cSqfreeYunFFGgoWf_ge` at `i = 1` gives `maxmult ≤ length`. -/
theorem length_cSqfreeYunFFGWf_ge [CharZero (CFieldSpec.K α)] (hgcd : GcdFFCorrect (α := α))
    (p : CPolyG α) (hp0 : toPolyG p ≠ 0) (hpp : (toPolyG p).primPart ≠ 0) :
    (normalizedFactors (toPolyG p).primPart).toFinset.sup
        (fun P => (normalizedFactors (toPolyG p).primPart).count P) ≤ (cSqfreeYunFFGWf p).length := by
  rw [cSqfreeYunFFGWf]
  have hinv : YunInv (toPolyG p) 1
      (toPolyG (cdivWf p (CFracGcdCoreWf.cgcdFFCoreWf p (cderivG p))))
      (toPolyG (csubG (cdivWf (cderivG p) (CFracGcdCoreWf.cgcdFFCoreWf p (cderivG p)))
        (cderivG (cdivWf p (CFracGcdCoreWf.cgcdFFCoreWf p (cderivG p)))))) :=
    toPolyG_yunEntry_YunInv hgcd p hp0 hpp
  have hfuel : (normalizedFactors (toPolyG p).primPart).toFinset.sup
      (fun P => (normalizedFactors (toPolyG p).primPart).count P) ≤ cyunBoundG p := by
    have hcn : cnormG p ≠ [] := fun h => hp0 ((cisZeroG_iff p).mp (by simp [cisZeroG, h]))
    rw [cyunBoundG, length_cnormG_of_ne p hcn]
    have h1 := sup_count_le_natDegree_primPart (toPolyG p) hpp
    have h2 : (toPolyG p).primPart.natDegree ≤ (toPolyG p).natDegree :=
      natDegree_le_of_dvd (toPolyG p).primPart_dvd hp0
    omega
  have h := length_cSqfreeYunFFGgoWf_ge hgcd p hpp (cyunBoundG p) 1 _ _ le_rfl hinv (by simpa using hfuel)
  simpa using h

open UniqueFactorizationMonoid in
omit [CDiffField α] [CDiffFieldSpec α] in
/-- **The Yun factorization reconstructs its input up to associates** — `hrecon`:
`toPolyG d ~ prodPow 1 (Yun factors)`. Chains the factorwise correspondence
(`cSqfreeYunFFGWf_forall₂` through `prodPow_associated`), the range reconstruction
(`prodPow_one_sqfreeFactPart_range_associated`, discharged by `length_cSqfreeYunFFGWf_ge`), and
`pp(d) ~ d`. Discharges the last frontier of the tower-Hermite pole-cancellation. -/
theorem cSqfreeYunFFGWf_reconstruction [CharZero (CFieldSpec.K α)] (hgcd : GcdFFCorrect (α := α))
    (d : CPolyG α) (hd0 : toPolyG d ≠ 0) (hpp : (toPolyG d).primPart ≠ 0) :
    Associated (toPolyG d) (prodPow 1 ((cSqfreeYunFFGWf d).map toPolyG)) := by
  have h1 : Associated (prodPow 1 ((cSqfreeYunFFGWf d).map toPolyG))
      (prodPow 1 ((List.range (cSqfreeYunFFGWf d).length).map
        (fun j => sqfreeFactPart (toPolyG d) (1 + j)))) :=
    prodPow_associated (cSqfreeYunFFGWf_forall₂ hgcd d hd0 hpp) 1
  have h2 : Associated (prodPow 1 ((List.range (cSqfreeYunFFGWf d).length).map
        (fun j => sqfreeFactPart (toPolyG d) (1 + j)))) (toPolyG d).primPart :=
    prodPow_one_sqfreeFactPart_range_associated (toPolyG d) hpp _
      (length_cSqfreeYunFFGWf_ge hgcd d hd0 hpp)
  exact ((h1.trans h2).trans (associated_primPart_self (toPolyG d) hd0)).symm

/-- **A monic, split, squarefree polynomial is the `nodal` polynomial of its root set.**
`p = ∏_{β ∈ roots} (X − β)`. The mathematical core of the RT `hden` bridge (the reduced denominator
factors into distinct linear factors over `K`). -/
theorem split_squarefree_eq_nodal {K : Type*} [Field K] [CharZero K] (p : K[X]) (hm : p.Monic)
    (hsp : p.Splits) (hsf : Squarefree p) :
    p = Lagrange.nodal p.roots.toFinset id := by
  have hnodup : p.roots.Nodup := Polynomial.nodup_roots (PerfectField.separable_iff_squarefree.mpr hsf)
  have key : (∏ β ∈ p.roots.toFinset, (Polynomial.X - Polynomial.C (id β)))
      = (p.roots.map (fun β => Polynomial.X - Polynomial.C β)).prod := by
    rw [Finset.prod_eq_multiset_prod]
    congr 1
    rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup]
    exact Multiset.map_congr rfl (fun _ _ => by simp)
  rw [Lagrange.nodal, key, ← hsp.eq_prod_roots_of_monic hm]

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **Every Yun go-loop factor is monic** — each emitted factor is `cmonicG (cgcdFFCoreWf b d)`, whose
`toPolyG` is monic (`monic_toPolyG_cmonicG`); the working `b` stays nonzero through the deflation. -/
theorem cSqfreeYunFFGgoWf_monic (hgcd : GcdFFCorrect (α := α)) :
    ∀ (fo : ℕ) (b d : CPolyG α), toPolyG b ≠ 0 →
      ∀ p ∈ cSqfreeYunFFGgoWf fo b d, (toPolyG p).Monic := by
  intro fo
  induction fo with
  | zero => intro b d _ p hp; simp [cSqfreeYunFFGgoWf] at hp
  | succ fo ih =>
    intro b d hb p hp
    rw [cSqfreeYunFFGgoWf] at hp
    by_cases hdeg : cdegG b = 0
    · rw [if_pos hdeg] at hp; simp at hp
    · rw [if_neg hdeg, List.mem_cons] at hp
      have hgne : gcd (toPolyG b) (toPolyG d) ≠ 0 :=
        fun h => hb (zero_dvd_iff.mp (h ▸ gcd_dvd_left (toPolyG b) (toPolyG d)))
      have hcg : toPolyG (CFracGcdCoreWf.cgcdFFCoreWf b d) ≠ 0 :=
        fun h => hgne ((hgcd b d).eq_zero_iff.mp h)
      rcases hp with rfl | hp
      · exact monic_toPolyG_cmonicG _ hcg
      · have hb' : toPolyG (cdivWf b (cmonicG (CFracGcdCoreWf.cgcdFFCoreWf b d))) ≠ 0 := by
          rw [toPolyG_yunDeflate_fst hgcd b d hb]
          intro h
          apply hb
          rw [← EuclideanDomain.mul_div_cancel' hgne (gcd_dvd_left (toPolyG b) (toPolyG d)), h,
            mul_zero]
        exact ih _ _ hb' p hp

omit [CDiffFieldSpec α] in
/-- **The Yun radical `Dstar` is squarefree** — a product of the pairwise-coprime, squarefree Yun
factors (`squarefree_list_prod`). -/
theorem toPolyG_cHermiteReduceTowerGWf_Dstar_squarefree [CharZero (CFieldSpec.K α)]
    (hgcd : GcdFFCorrect (α := α)) (Dt a d : CPolyG α) (hd0 : toPolyG d ≠ 0)
    (hpp : (toPolyG d).primPart ≠ 0) :
    Squarefree (toPolyG (cHermiteReduceTowerGWf Dt a d).2.2) := by
  rw [cHermiteReduceTowerGWf]
  simp only [denote, toPolyG_foldl_cmulG_plainList, toPolyG_one_singleton, one_mul]
  apply squarefree_list_prod
  · rw [List.pairwise_map, List.pairwise_iff_getElem]
    intro i j hi hj hij
    exact cSqfreeYunFFGWf_isRelPrime hgcd d hd0 hpp hi hj (Nat.ne_of_lt hij)
  · intro b hb
    rw [List.mem_map] at hb
    obtain ⟨f, hf, rfl⟩ := hb
    obtain ⟨k, hk, hfk⟩ := List.mem_iff_getElem.mp hf
    rw [← hfk]
    exact cSqfreeYunFFGWf_squarefree hgcd d hd0 hpp k hk

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **Every Yun factor is monic** (entry): the go-loop runs from `b₁ = d / gcd(d, d′) ≠ 0`. -/
theorem cSqfreeYunFFGWf_monic (hgcd : GcdFFCorrect (α := α)) (d : CPolyG α) (hd0 : toPolyG d ≠ 0) :
    ∀ p ∈ cSqfreeYunFFGWf d, (toPolyG p).Monic := by
  rw [cSqfreeYunFFGWf]
  apply cSqfreeYunFFGgoWf_monic hgcd
  set g := CFracGcdCoreWf.cgcdFFCoreWf d (cderivG d) with hgdef
  have hgp : toPolyG g ∣ toPolyG d :=
    (hgcd d (cderivG d)).dvd.trans (gcd_dvd_left (toPolyG d) (toPolyG (cderivG d)))
  have hgn : cnormG g ≠ [] := fun h =>
    hd0 (zero_dvd_iff.mp (((cisZeroG_iff g).mp (by simp [cisZeroG, h])) ▸ hgp))
  have hex := toPolyG_cdivWf_exact d g hgn hgp
  intro h; apply hd0; rw [← hex, h, zero_mul]

omit [CDiffFieldSpec α] in
/-- **The Yun radical `Dstar` is monic** — a product of the monic Yun factors (`monic_list_prod`). -/
theorem toPolyG_cHermiteReduceTowerGWf_Dstar_monic (hgcd : GcdFFCorrect (α := α)) (Dt a d : CPolyG α)
    (hd0 : toPolyG d ≠ 0) : (toPolyG (cHermiteReduceTowerGWf Dt a d).2.2).Monic := by
  rw [cHermiteReduceTowerGWf]
  simp only [denote, toPolyG_foldl_cmulG_plainList, toPolyG_one_singleton, one_mul]
  apply monic_list_prod
  intro p hp
  rw [List.mem_map] at hp
  obtain ⟨f, hf, rfl⟩ := hp
  exact cSqfreeYunFFGWf_monic hgcd d hd0 f hf

omit [CDiffFieldSpec α] in
/-- **The RT `hden` bridge.** If the Yun radical `Dstar` splits over `K` (the rational-residue slice),
then `Dstar = nodal (its root set)` — the `hden` hypothesis of the RT residue-match assemblers. Monic
and squarefree are supplied by the Yun structure; `hsplit` is the genuine rational-residue restriction. -/
theorem toPolyG_cHermiteReduceTowerGWf_Dstar_eq_nodal [CharZero (CFieldSpec.K α)]
    (hgcd : GcdFFCorrect (α := α)) (Dt a d : CPolyG α) (hd0 : toPolyG d ≠ 0)
    (hpp : (toPolyG d).primPart ≠ 0)
    (hsplit : (toPolyG (cHermiteReduceTowerGWf Dt a d).2.2).Splits) :
    toPolyG (cHermiteReduceTowerGWf Dt a d).2.2
      = Lagrange.nodal (toPolyG (cHermiteReduceTowerGWf Dt a d).2.2).roots.toFinset id :=
  split_squarefree_eq_nodal _ (toPolyG_cHermiteReduceTowerGWf_Dstar_monic hgcd Dt a d hd0) hsplit
    (toPolyG_cHermiteReduceTowerGWf_Dstar_squarefree hgcd Dt a d hd0 hpp)

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **Realization (Stage 2): `cSqfreeYunFFGWf` is a lawful squarefree decomposition.** The single
`LawfulSquarefreeDecomposition` realization theorem — bundles reconstruction, monic, squarefree, and
pairwise-coprimality. The abstract Hermite/assembler stages consume this, never the Yun loop itself. -/
theorem cSqfreeYunFFGWf_lawfulSquarefreeDecomposition [CharZero (CFieldSpec.K α)]
    (hgcd : GcdFFCorrect (α := α)) (d : CPolyG α) (hd0 : toPolyG d ≠ 0)
    (hpp : (toPolyG d).primPart ≠ 0) :
    LawfulSquarefreeDecomposition d (cSqfreeYunFFGWf d) :=
  { reconstruct := cSqfreeYunFFGWf_reconstruction hgcd d hd0 hpp
    monic := cSqfreeYunFFGWf_monic hgcd d hd0
    squarefree := fun p hp => by
      obtain ⟨k, hk, hpk⟩ := List.mem_iff_getElem.mp hp
      rw [← hpk]; exact cSqfreeYunFFGWf_squarefree hgcd d hd0 hpp k hk
    coprime := by
      rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      exact cSqfreeYunFFGWf_isRelPrime hgcd d hd0 hpp hi hj (Nat.ne_of_lt hij) }

/-! ### The Yun factorization of a constant is empty (the no-poles / trivial-normal-part base case) -/

omit [CDiffField α] [CDiffFieldSpec α] [CFieldSpec α] in
/-- **The Yun go-loop is empty once its working polynomial is a constant** (`cdegG b = 0` fires the
terminating `if`). -/
theorem cSqfreeYunFFGgoWf_eq_nil_of_cdegG_zero (fo : ℕ) (b d : CPolyG α) (hb : cdegG b = 0) :
    cSqfreeYunFFGgoWf fo b d = [] := by
  cases fo with
  | zero => rfl
  | succ n => rw [cSqfreeYunFFGgoWf]; exact if_pos hb

omit [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α] in
/-- **Dividing a constant stays a constant**: `cdegG p = 0 ⟹ cdegG (cdivWf p q) = 0`. The polynomial quotient
of a degree-`0` dividend has degree `0` (`p = q̂·q + r` with `deg r < deg q`; a positive-degree `q̂` would push
`deg p` positive). -/
theorem cdegG_cdivWf_eq_zero_of_cdegG_zero (p q : CPolyG α) (hp : cdegG p = 0) :
    cdegG (cdivWf p q) = 0 := by
  by_cases hq : cnormG q = []
  · -- zero divisor: `cdivWf p q = []` (the `cisZeroG` branch of `cdivmodWf`)
    have hcz : cisZeroG (cnormG q) = true := by
      rw [cisZeroG_cnormG]; exact (cisZeroG_iff q).mpr ((cnormG_eq_nil_iff q).mp hq)
    have hnil : cdivWf p q = ([] : CPolyG α) := by
      show (cdivmodWf p q).1 = []
      simp [cdivmodWf.eq_def, hcz]
    rw [hnil]; rfl
  rw [cdegG_eq_natDegree] at hp ⊢
  have hdiv := toPolyG_cmodWf p q hq
  have hq' : toPolyG q ≠ 0 := fun h => hq ((cnormG_eq_nil_iff q).mpr h)
  by_contra hquot
  have hquot0 : toPolyG (cdivWf p q) ≠ 0 := fun h => hquot (by rw [h, Polynomial.natDegree_zero])
  have hrem : (toPolyG (cmodWf p q)).degree < (toPolyG q).degree :=
    toPolyG_degree_lt_of_length_lt (cmodWf p q) q hq (cmodWf_length_lt p q hq)
  have hmuldeg : (toPolyG q).degree ≤ (toPolyG (cdivWf p q) * toPolyG q).degree := by
    rw [Polynomial.degree_mul]
    exact le_add_of_nonneg_left (Polynomial.zero_le_degree_iff.mpr hquot0)
  have hpdeg : (toPolyG p).degree = (toPolyG (cdivWf p q) * toPolyG q).degree := by
    rw [hdiv, add_comm]
    exact Polynomial.degree_add_eq_right_of_degree_lt (lt_of_lt_of_le hrem hmuldeg)
  have hnat := Polynomial.natDegree_eq_of_degree_eq hpdeg
  rw [Polynomial.natDegree_mul hquot0 hq'] at hnat
  omega

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **The Yun factorization of a constant is empty** (`cdegG p = 0 ⟹ cSqfreeYunFFGWf p = []`) — the base of
the no-poles / trivial-normal-part case: with no non-constant factor there are no residues. -/
theorem cSqfreeYunFFGWf_eq_nil_of_cdegG_zero (p : CPolyG α) (hp : cdegG p = 0) :
    cSqfreeYunFFGWf p = [] := by
  rw [cSqfreeYunFFGWf]
  exact cSqfreeYunFFGgoWf_eq_nil_of_cdegG_zero _ _ _
    (cdegG_cdivWf_eq_zero_of_cdegG_zero p _ hp)

end DeepWiki.SymbolicIntegration
