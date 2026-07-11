import DeepWiki.SymbolicIntegration.Engine.Tower.WellFounded
import DeepWiki.ComputableAlgebra.PolyEuclideanDense
import DeepWiki.SymbolicIntegration.Engine.SplitFactorWfCorrect
import DeepWiki.SymbolicIntegration.Engine.LogPartTowerSoundness
import DeepWiki.SymbolicIntegration.Engine.SquarefreeDecomposition
import DeepWiki.SymbolicIntegration.Core.Polynomial.SquarefreeYunLoop
import DeepWiki.SymbolicIntegration.SquarefreeFactorization

/-! # Correctness of the fuel-free Yun factorization `cSqfreeYunFF`

The computable Yun loop `cSqfreeYunFFGgoWf` mirrors the squarefree theory's abstract `yunLoopAbs`
step for step: each emits the monic gcd of the working pair and
recurses on the deflated pair `(b/gcd, d/gcd − (b/gcd)′)`. This file establishes the per-step bridges
through `toPoly`, assuming `CgcdBCorrect cgcdFFCoreWf`. -/

open Polynomial Classical

namespace DeepWiki.SymbolicIntegration

open DensePoly

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α]

/-- `prodPow` splits as the plain product times the zipIdx-power product:
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
/-- `prodPow 1` of the tower Yun factors is the radical product times the `∏vk^idx` divisor:
`prodPow 1 L = L.prod · FiltProd` where `L = map toPoly (cSqfreeYunFF d)` and `FiltProd` drops the
multiplicity-1 factors (which contribute `vk^0 = 1`). Plumbs the reconstruction `d ~ prodPow 1 L`
into the `hWdvd` divisor form. -/
theorem prodPow_one_cSqfreeYunFFG (d : DensePoly α) :
    prodPow 1 ((cSqfreeYunFF d).map toPoly)
      = ((cSqfreeYunFF d).map toPoly).prod
        * (((cSqfreeYunFF d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1))).map
            (fun x => toPoly x.1 ^ x.2)).prod := by
  rw [prodPow_eq_prod_mul_zipIdxPow]
  have hsnd : (((cSqfreeYunFF d).map toPoly).zipIdx.map (fun x => x.1 ^ x.2)).prod
      = ((cSqfreeYunFF d).zipIdx.map (fun x => toPoly x.1 ^ x.2)).prod := by
    rw [List.zipIdx_map, List.map_map]; rfl
  congr 1
  · simp only [pow_one, List.map_id']
  · rw [hsnd, ← prod_map_filter_eq_of_one ((cSqfreeYunFF d).zipIdx)
      (fun x => ¬ (x.2 + 1 ≤ 1)) (fun x => toPoly x.1 ^ x.2) (fun x _ hx => ?_)]
    have hx0 : x.2 = 0 := by
      by_contra hne
      apply hx
      have hle : ¬ (x.2 + 1 ≤ 1) := by omega
      simpa using hle
    rw [hx0, pow_zero]

omit [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α] in
/-- `cmonic` realizes `normalize` through `toPoly`: `toPoly (cmonic q) = normalize (toPoly q)`.
The monic associate of `toPoly q` is its normalization. -/
@[denote] theorem toPolyG_cmonicG_eq_normalize (q : DensePoly α) :
    toPoly (cmonic q) = normalize (toPoly q) := by
  by_cases hq : toPoly q = 0
  · have hcm : toPoly (cmonic q) = 0 := by
      have := associated_toPolyG_cmonicG q
      rwa [hq, associated_zero_iff_eq_zero] at this
    rw [hcm, hq, normalize_zero]
  · have hmonic : (toPoly (cmonic q)).Monic := monic_toPolyG_cmonicG q hq
    have hassoc : Associated (toPoly (cmonic q)) (toPoly q) := associated_toPolyG_cmonicG q
    rw [← hmonic.normalize_eq_self, normalize_eq_normalize_iff_associated.mpr hassoc]

omit [CDiffField α] [CDiffFieldSpec α] in
/-- The emitted Yun factor denotes the exact monic gcd:
`toPoly (cmonic (cgcdFFCoreWf b d)) = gcd (toPoly b) (toPoly d)`. -/
theorem toPolyG_yunEmit_eq_gcd (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) (b d : DensePoly α) :
    toPoly (cmonic (CFracGcdCoreWf.cgcdFFCoreWf b d)) = gcd (toPoly b) (toPoly d) := by
  rw [toPolyG_cmonicG_eq_normalize, normalize_eq_normalize_iff_associated.mpr (hgcd b d),
    normalize_gcd]

/-- Exact quotient reading: from `X·g = b` with `g ≠ 0` in `K[X]`, `X = b / g`. -/
theorem eq_ediv_of_mul_eq {K : Type*} [Field K] {X g b : K[X]} (hg : g ≠ 0) (h : X * g = b) :
    X = b / g := by
  have hdvd : g ∣ b := ⟨X, by rw [← h, mul_comm]⟩
  have hcancel : g * (b / g) = b := EuclideanDomain.mul_div_cancel' hg hdvd
  exact (mul_left_cancel₀ hg (by rw [hcancel, ← h, mul_comm])).symm

omit [CDiffField α] [CDiffFieldSpec α] in
/-- The deflated first component denotes `b / gcd(b,d)` in the `yunLoopAbs` recursion:
`toPoly (CPolyEuclidean.div b (cmonic (cgcdFFCoreWf b d))) = toPoly b / gcd (toPoly b) (toPoly d)`. -/
theorem toPolyG_yunDeflate_fst (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) (b d : DensePoly α)
    (hb : toPoly b ≠ 0) :
    toPoly (CPolyEuclidean.div b (cmonic (CFracGcdCoreWf.cgcdFFCoreWf b d)))
      = toPoly b / gcd (toPoly b) (toPoly d) := by
  set p := cmonic (CFracGcdCoreWf.cgcdFFCoreWf b d) with hpdef
  have hp : toPoly p = gcd (toPoly b) (toPoly d) := toPolyG_yunEmit_eq_gcd hgcd b d
  have hgne : gcd (toPoly b) (toPoly d) ≠ 0 :=
    fun h => hb (zero_dvd_iff.mp (h ▸ gcd_dvd_left (toPoly b) (toPoly d)))
  have hpn : cnorm p ≠ [] := by
    intro h; apply hgne; rw [← hp]; exact (cisZeroG_iff p).mp (by simp [cisZero, h])
  have hdvd : toPoly p ∣ toPoly b := by rw [hp]; exact gcd_dvd_left _ _
  have hex : toPoly (CPolyEuclidean.div b p) * toPoly p = toPoly b := toPolyG_div_exact b p hpn hdvd
  rw [hp] at hex
  exact eq_ediv_of_mul_eq hgne hex

omit [CDiffField α] [CDiffFieldSpec α] in
/-- The deflated second component denotes `d / gcd(b,d) − (b / gcd(b,d))′` in the
`yunLoopAbs` recursion. -/
theorem toPolyG_yunDeflate_snd (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) (b d : DensePoly α)
    (hb : toPoly b ≠ 0) :
    toPoly (csub (CPolyEuclidean.div d (cmonic (CFracGcdCoreWf.cgcdFFCoreWf b d)))
        (cderiv (CPolyEuclidean.div b (cmonic (CFracGcdCoreWf.cgcdFFCoreWf b d)))))
      = toPoly d / gcd (toPoly b) (toPoly d)
        - derivative (toPoly b / gcd (toPoly b) (toPoly d)) := by
  set p := cmonic (CFracGcdCoreWf.cgcdFFCoreWf b d) with hpdef
  have hp : toPoly p = gcd (toPoly b) (toPoly d) := toPolyG_yunEmit_eq_gcd hgcd b d
  have hgne : gcd (toPoly b) (toPoly d) ≠ 0 :=
    fun h => hb (zero_dvd_iff.mp (h ▸ gcd_dvd_left (toPoly b) (toPoly d)))
  have hpn : cnorm p ≠ [] := by
    intro h; apply hgne; rw [← hp]; exact (cisZeroG_iff p).mp (by simp [cisZero, h])
  have hdvdd : toPoly p ∣ toPoly d := by rw [hp]; exact gcd_dvd_right _ _
  have hexd : toPoly (CPolyEuclidean.div d p) * toPoly p = toPoly d := toPolyG_div_exact d p hpn hdvdd
  rw [hp] at hexd
  have hd' : toPoly (CPolyEuclidean.div d p) = toPoly d / gcd (toPoly b) (toPoly d) :=
    eq_ediv_of_mul_eq hgne hexd
  simp only [denote]
  rw [hd', toPolyG_yunDeflate_fst hgcd b d hb]

omit [CDiffField α] [CDiffFieldSpec α] in
/-- The Yun radical divides the working polynomial. The product of all Yun factors emitted from
`(b, d)` divides `toPoly b`: each factor is `gcd(bⱼ, dⱼ)` dividing `bⱼ`, and the product telescopes
through the deflation. -/
theorem prod_map_cSqfreeYunFFGgoWf_dvd (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) :
    ∀ (fo : ℕ) (b d : DensePoly α),
      ((cSqfreeYunFFGgoWf fo b d).map toPoly).prod ∣ toPoly b := by
  intro fo
  induction fo with
  | zero => intro b d; simp [cSqfreeYunFFGgoWf]
  | succ fo ih =>
    intro b d
    rw [cSqfreeYunFFGgoWf]
    by_cases hdeg : cdeg b = 0
    · rw [if_pos hdeg]; simp
    · rw [if_neg hdeg]
      simp only [CPolyGcd.compute_dense_wf_eq]
      have hbne : toPoly b ≠ 0 := by
        intro h; exact hdeg (by rw [cdegG_eq_natDegree, h, natDegree_zero])
      have hgne : gcd (toPoly b) (toPoly d) ≠ 0 :=
        fun h => hbne (zero_dvd_iff.mp (h ▸ gcd_dvd_left (toPoly b) (toPoly d)))
      rw [List.map_cons, List.prod_cons,
        toPolyG_yunEmit_eq_gcd hgcd b d]
      have hih := ih (CPolyEuclidean.div b (cmonic (CFracGcdCoreWf.cgcdFFCoreWf b d)))
        (csub (CPolyEuclidean.div d (cmonic (CFracGcdCoreWf.cgcdFFCoreWf b d)))
          (cderiv (CPolyEuclidean.div b (cmonic (CFracGcdCoreWf.cgcdFFCoreWf b d)))))
      rw [toPolyG_yunDeflate_fst hgcd b d hbne] at hih
      calc gcd (toPoly b) (toPoly d)
              * ((cSqfreeYunFFGgoWf fo (CPolyEuclidean.div b (cmonic (CFracGcdCoreWf.cgcdFFCoreWf b d)))
                  (csub (CPolyEuclidean.div d (cmonic (CFracGcdCoreWf.cgcdFFCoreWf b d)))
                    (cderiv (CPolyEuclidean.div b (cmonic (CFracGcdCoreWf.cgcdFFCoreWf b d)))))).map
                  toPoly).prod
            ∣ gcd (toPoly b) (toPoly d) * (toPoly b / gcd (toPoly b) (toPoly d)) :=
              mul_dvd_mul_left _ hih
        _ = toPoly b :=
              EuclideanDomain.mul_div_cancel' hgne (gcd_dvd_left (toPoly b) (toPoly d))

omit [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α] in
/-- The Yun-radical `foldl`-product denotes the list product through `toPoly`:
`toPoly (L.foldl cmul init) = toPoly init · ∏ (map toPoly L)`. -/
@[denote] theorem toPolyG_foldl_cmulG_plainList (init : DensePoly α) (L : List (DensePoly α)) :
    toPoly (L.foldl (fun acc vi => cmul acc vi) init)
      = toPoly init * (L.map toPoly).prod := by
  induction L generalizing init with
  | nil => simp
  | cons a L ih => simp only [List.foldl_cons, List.map_cons, List.prod_cons, ih, denote]; ring

omit [CDiffField α] [CDiffFieldSpec α] in
/-- The Yun radical divides the input. The product of `cSqfreeYunFF p`'s factors divides
`toPoly p`: the entry `b₁ = p / gcd(p, p′)` divides `p`, and the go-loop product divides `b₁`. -/
theorem prod_map_cSqfreeYunFFG_dvd (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) (p : DensePoly α)
    (hp : toPoly p ≠ 0) :
    ((cSqfreeYunFF p).map toPoly).prod ∣ toPoly p := by
  rw [cSqfreeYunFF]
  simp only [CPolyGcd.compute_dense_wf_eq]
  set g := CFracGcdCoreWf.cgcdFFCoreWf p (cderiv p) with hgdef
  -- `toPoly g ∣ toPoly p` (associated to `gcd(p, p′)`).
  have hgp : toPoly g ∣ toPoly p :=
    (hgcd p (cderiv p)).dvd.trans (gcd_dvd_left (toPoly p) (toPoly (cderiv p)))
  have hgn : cnorm g ≠ [] := by
    intro h
    have hg0 : toPoly g = 0 := (cisZeroG_iff g).mp (by simp [cisZero, h])
    exact hp (zero_dvd_iff.mp (hg0 ▸ hgp))
  -- `b₁ = CPolyEuclidean.div p g` divides `p` (exact division).
  have hb1 : toPoly (CPolyEuclidean.div p g) * toPoly g = toPoly p := toPolyG_div_exact p g hgn hgp
  have hb1dvd : toPoly (CPolyEuclidean.div p g) ∣ toPoly p := ⟨toPoly g, hb1.symm⟩
  exact (prod_map_cSqfreeYunFFGgoWf_dvd hgcd _ _ _).trans hb1dvd

omit [CDiffFieldSpec α] in
/-- The Yun radical `Dstar` divides `d`: the `foldl`-product of the Yun factors of `d` divides `d`. -/
theorem toPolyG_cHermiteReduceTowerG_Dstar_dvd (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) (Dt a d : DensePoly α)
    (hd : toPoly d ≠ 0) :
    toPoly (cHermiteReduceTower Dt a d).2.2 ∣ toPoly d := by
  rw [cHermiteReduceTower, squarefreeYun_dense_wf_eq]
  simp only [denote, map_one, mul_zero, add_zero, one_mul]
  exact prod_map_cSqfreeYunFFG_dvd hgcd d hd

omit [CDiffFieldSpec α] in
/-- The radical split `d = Dstar · W` with `W = d / Dstar` for the
`cHermiteReduceTower` output. -/
theorem toPolyG_yunRadical_split (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) (Dt a d : DensePoly α)
    (hd : toPoly d ≠ 0) :
    toPoly d = toPoly (cHermiteReduceTower Dt a d).2.2
      * toPoly (CPolyEuclidean.div d (cHermiteReduceTower Dt a d).2.2) := by
  set Dstar := (cHermiteReduceTower Dt a d).2.2 with hDstar
  have hdvd : toPoly Dstar ∣ toPoly d :=
    toPolyG_cHermiteReduceTowerG_Dstar_dvd hgcd Dt a d hd
  have hDstar0 : toPoly Dstar ≠ 0 := fun h => hd (zero_dvd_iff.mp (h ▸ hdvd))
  have hDn : cnorm Dstar ≠ [] :=
    fun h => hDstar0 ((cisZeroG_iff Dstar).mp (by simp [cisZero, h]))
  have hex : toPoly (CPolyEuclidean.div d Dstar) * toPoly Dstar = toPoly d :=
    toPolyG_div_exact d Dstar hDn hdvd
  rw [← hex, mul_comm]

/-! ### `YunInv` under constant scaling

The tower entry `(toPoly b₁, toPoly d₁)` equals `C(u⁻¹) ·` the abstract `yunInv_base` pair (both
components scaled by the *same* unit `u`, where `toPoly (cgcdFFCoreWf p p′) = C u · gcd(p, p′)` from
`CgcdBCorrect cgcdFFCoreWf`). Since `YunInv`'s witness has a free scalar, common-constant scaling preserves it —
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
/-- The tower Yun entry satisfies the abstract invariant. For `A = toPoly p ≠ 0` with primitive
part `≠ 0`, the entry pair `(p/g, p′/g − (p/g)′)` (`g = cgcdFFCoreWf p p′`) satisfies
`YunInv A 1`; it is `C(k⁻¹)·` the `yunInv_base` pair, where `toPoly g = C k·gcd(A, A′)`. -/
theorem toPolyG_yunEntry_YunInv [CharZero (CFieldSpec.K α)] (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α)))
    (p : DensePoly α) (hp0 : toPoly p ≠ 0) (hpp : (toPoly p).primPart ≠ 0) :
    YunInv (toPoly p) 1
      (toPoly (CPolyEuclidean.div p (CFracGcdCoreWf.cgcdFFCoreWf p (cderiv p))))
      (toPoly (csub (CPolyEuclidean.div (cderiv p) (CFracGcdCoreWf.cgcdFFCoreWf p (cderiv p)))
        (cderiv (CPolyEuclidean.div p (CFracGcdCoreWf.cgcdFFCoreWf p (cderiv p)))))) := by
  set A := toPoly p with hAdef
  set g := CFracGcdCoreWf.cgcdFFCoreWf p (cderiv p) with hgdef
  have hA'poly : toPoly (cderiv p) = derivative A := by
    simp only [denote]
    rw [hAdef]
  set G := gcd A (derivative A) with hGdef
  have hG0 : G ≠ 0 := fun h => hp0 (zero_dvd_iff.mp (h ▸ gcd_dvd_left A (derivative A)))
  -- `toPoly g ~ G`, hence `toPoly g = C k · G` for a unit `k`.
  have hassoc : Associated (toPoly g) G := by
    have := hgcd p (cderiv p); rwa [hA'poly] at this
  obtain ⟨u, hu⟩ := hassoc.symm
  obtain ⟨k, hkunit, hkC⟩ := Polynomial.isUnit_iff.mp u.isUnit
  have hk0 : k ≠ 0 := isUnit_iff_ne_zero.mp hkunit
  have hgval : toPoly g = Polynomial.C k * G := by rw [← hu, ← hkC]; ring
  -- divisibility of `toPoly g` into `A` and `A′`.
  have hgn : cnorm g ≠ [] := by
    intro h
    exact hG0 (zero_dvd_iff.mp (((cisZeroG_iff g).mp (by simp [cisZero, h])) ▸ hassoc.dvd))
  have hgA : toPoly g ∣ A := hassoc.dvd.trans (gcd_dvd_left A (derivative A))
  have hgA' : toPoly g ∣ derivative A :=
    hassoc.dvd.trans (gcd_dvd_right A (derivative A))
  -- the two scaling equalities: `b₁ = C(k⁻¹)·(A/G)`, first residual term `q′ = C(k⁻¹)·(A′/G)`.
  have hkinv : Polynomial.C k⁻¹ * Polynomial.C k = 1 := by
    rw [← Polynomial.C_mul, inv_mul_cancel₀ hk0, Polynomial.C_1]
  -- from `q · toPoly g = x`: `x/G = q · C k`.
  have hb1ex : toPoly (CPolyEuclidean.div p g) * toPoly g = A := toPolyG_div_exact p g hgn hgA
  have hq'ex : toPoly (CPolyEuclidean.div (cderiv p) g) * toPoly g = derivative A := by
    have h := toPolyG_div_exact (cderiv p) g hgn (by rw [hA'poly]; exact hgA')
    rwa [hA'poly] at h
  have hAG : A / G = toPoly (CPolyEuclidean.div p g) * Polynomial.C k :=
    (eq_ediv_of_mul_eq hG0 (by rw [← hb1ex, hgval]; ring)).symm
  have hA'G : derivative A / G = toPoly (CPolyEuclidean.div (cderiv p) g) * Polynomial.C k :=
    (eq_ediv_of_mul_eq hG0 (by rw [← hq'ex, hgval]; ring)).symm
  have heqb : toPoly (CPolyEuclidean.div p g) = Polynomial.C k⁻¹ * (A / G) := by
    rw [hAG, show Polynomial.C k⁻¹ * (toPoly (CPolyEuclidean.div p g) * Polynomial.C k)
        = toPoly (CPolyEuclidean.div p g) * (Polynomial.C k⁻¹ * Polynomial.C k) from by ring, hkinv, mul_one]
  -- assemble `d₁`.
  have heqd : toPoly (csub (CPolyEuclidean.div (cderiv p) g) (cderiv (CPolyEuclidean.div p g)))
      = Polynomial.C k⁻¹ * (derivative A / G - derivative (A / G)) := by
    simp only [denote]
    rw [heqb, derivative_C_mul, mul_sub, hA'G,
      show Polynomial.C k⁻¹ * (toPoly (CPolyEuclidean.div (cderiv p) g) * Polynomial.C k)
        = toPoly (CPolyEuclidean.div (cderiv p) g) * (Polynomial.C k⁻¹ * Polynomial.C k) from by ring,
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
/-- The tower go-loop denotes the abstract `yunLoopAbs` run for its own length: the deflated
state matches `yunLoopAbs`'s recursion (`yunDeflate_fst`/`_snd`) and the emitted factor is the monic
gcd (`yunEmit_eq_gcd`). The `i` parameter is phantom, so any start index works. -/
theorem map_toPolyG_cSqfreeYunFFGgoWf_eq (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) :
    ∀ (fo : ℕ) (b d : DensePoly α),
      (cSqfreeYunFFGgoWf fo b d).map toPoly
        = yunLoopAbs (0 : (CFieldSpec.K α)[X]) (toPoly b, toPoly d) 1
            (cSqfreeYunFFGgoWf fo b d).length := by
  intro fo
  induction fo with
  | zero => intro b d; simp [cSqfreeYunFFGgoWf, yunLoopAbs]
  | succ fo ih =>
    intro b d
    rw [cSqfreeYunFFGgoWf]
    by_cases hdeg : cdeg b = 0
    · rw [if_pos hdeg]; simp [yunLoopAbs]
    · rw [if_neg hdeg]
      simp only [CPolyGcd.compute_dense_wf_eq]
      have hbne : toPoly b ≠ 0 := fun h => hdeg (by rw [cdegG_eq_natDegree, h, natDegree_zero])
      rw [List.map_cons, List.length_cons, toPolyG_yunEmit_eq_gcd hgcd b d]
      -- unfold one `yunLoopAbs` step on the RHS.
      simp only [yunLoopAbs]
      -- head gcds agree; tails via the deflate bridges + IH + `i`-irrelevance.
      congr 1
      rw [ih (CPolyEuclidean.div b (cmonic (CFracGcdCoreWf.cgcdFFCoreWf b d)))
            (csub (CPolyEuclidean.div d (cmonic (CFracGcdCoreWf.cgcdFFCoreWf b d)))
              (cderiv (CPolyEuclidean.div b (cmonic (CFracGcdCoreWf.cgcdFFCoreWf b d))))),
        toPolyG_yunDeflate_fst hgcd b d hbne, toPolyG_yunDeflate_snd hgcd b d hbne]
      exact yunLoopAbs_irrelevant _ _ _ _ _ _

omit [CDiffField α] [CDiffFieldSpec α] in
/-- The tower Yun factors correspond to `sqfreeFactPart`. The factors of
`cSqfreeYunFF p` are `Forall₂ Associated` to `[sqfreeFactPart A 1, sqfreeFactPart A 2, …]`
(`A = toPoly p`), so the tower Yun factorization denotes the abstract one. -/
theorem cSqfreeYunFFG_forall₂ [CharZero (CFieldSpec.K α)] (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α)))
    (p : DensePoly α) (hp0 : toPoly p ≠ 0) (hpp : (toPoly p).primPart ≠ 0) :
    List.Forall₂ Associated ((cSqfreeYunFF p).map toPoly)
      ((List.range (cSqfreeYunFF p).length).map
        (fun j => sqfreeFactPart (toPoly p) (1 + j))) := by
  rw [cSqfreeYunFF]
  simp only [CPolyGcd.compute_dense_wf_eq]
  set b₁ := CPolyEuclidean.div p (CFracGcdCoreWf.cgcdFFCoreWf p (cderiv p)) with hb1
  set d₁ := csub (CPolyEuclidean.div (cderiv p) (CFracGcdCoreWf.cgcdFFCoreWf p (cderiv p)))
    (cderiv (CPolyEuclidean.div p (CFracGcdCoreWf.cgcdFFCoreWf p (cderiv p)))) with hd1
  set L := (cSqfreeYunFFGgoWf (cyunBound p) b₁ d₁).length with hL
  have hinv : YunInv (toPoly p) 1 (toPoly b₁) (toPoly d₁) :=
    toPolyG_yunEntry_YunInv hgcd p hp0 hpp
  have hmap := map_toPolyG_cSqfreeYunFFGgoWf_eq hgcd (cyunBound p) b₁ d₁
  rw [← hL] at hmap
  rw [hmap, yunLoopAbs_irrelevant (0 : (CFieldSpec.K α)[X]) (toPoly p) L (toPoly b₁, toPoly d₁) 1 1]
  exact yunLoopAbs_forall₂ (toPoly p) hpp L 1 (toPoly b₁) (toPoly d₁) (le_refl 1) hinv

omit [CDiffField α] [CDiffFieldSpec α] in
/-- The `j`-th tower Yun factor is `Associated (sqfreeFactPart (toPoly p) (1 + j))` (per-index form of
the correspondence). -/
theorem cSqfreeYunFFG_get_assoc [CharZero (CFieldSpec.K α)] (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α)))
    (p : DensePoly α) (hp0 : toPoly p ≠ 0) (hpp : (toPoly p).primPart ≠ 0)
    (j : ℕ) (hj : j < (cSqfreeYunFF p).length) :
    Associated (toPoly ((cSqfreeYunFF p).get ⟨j, hj⟩))
      (sqfreeFactPart (toPoly p) (1 + j)) := by
  have hf := cSqfreeYunFFG_forall₂ hgcd p hp0 hpp
  have hjm : j < ((cSqfreeYunFF p).map toPoly).length := by rwa [List.length_map]
  have hjr : j < ((List.range (cSqfreeYunFF p).length).map
      (fun j => sqfreeFactPart (toPoly p) (1 + j))).length := by
    rw [List.length_map, List.length_range]; exact hj
  have hg := hf.get hjm hjr
  simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range] at hg ⊢
  exact hg

omit [CDiffField α] [CDiffFieldSpec α] in
/-- Distinct tower Yun factors are relatively prime. From the `sqfreeFactPart` correspondence and
`sqfreeFactPart_isRelPrime` (distinct multiplicities are coprime). -/
theorem cSqfreeYunFFG_isRelPrime [CharZero (CFieldSpec.K α)] (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α)))
    (p : DensePoly α) (hp0 : toPoly p ≠ 0) (hpp : (toPoly p).primPart ≠ 0)
    {j k : ℕ} (hj : j < (cSqfreeYunFF p).length) (hk : k < (cSqfreeYunFF p).length)
    (hjk : j ≠ k) :
    IsRelPrime (toPoly ((cSqfreeYunFF p).get ⟨j, hj⟩))
      (toPoly ((cSqfreeYunFF p).get ⟨k, hk⟩)) := by
  have haj := cSqfreeYunFFG_get_assoc hgcd p hp0 hpp j hj
  have hak := cSqfreeYunFFG_get_assoc hgcd p hp0 hpp k hk
  have hne : (1 + j) ≠ (1 + k) := by omega
  exact fun d hda hdb =>
    (sqfreeFactPart_isRelPrime (toPoly p) hne) (hda.trans haj.dvd) (hdb.trans hak.dvd)

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
/-- Each tower Yun factor to its multiplicity divides `d`. For the factor at index `j` (multiplicity
`1 + j`), `toPoly (factor) ^ (1 + j) ∣ toPoly p` — the `hpow` hypothesis of the pole-cancellation. -/
theorem cSqfreeYunFFG_pow_dvd [CharZero (CFieldSpec.K α)] (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α)))
    (p : DensePoly α) (hp0 : toPoly p ≠ 0) (hpp : (toPoly p).primPart ≠ 0)
    (j : ℕ) (hj : j < (cSqfreeYunFF p).length) :
    toPoly ((cSqfreeYunFF p).get ⟨j, hj⟩) ^ (1 + j) ∣ toPoly p := by
  have haj := cSqfreeYunFFG_get_assoc hgcd p hp0 hpp j hj
  exact ((pow_dvd_pow_of_dvd haj.dvd (1 + j)).trans
    (sqfreeFactPart_pow_self_dvd_primPart (toPoly p) hpp (1 + j))).trans (toPoly p).primPart_dvd

omit [CDiffField α] [CDiffFieldSpec α] in
/-- Each tower Yun factor is squarefree, from the `sqfreeFactPart` correspondence and squarefreeness
of `sqfreeFactPart`, transferred across associates). -/
theorem cSqfreeYunFFG_squarefree [CharZero (CFieldSpec.K α)] (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α)))
    (p : DensePoly α) (hp0 : toPoly p ≠ 0) (hpp : (toPoly p).primPart ≠ 0)
    (j : ℕ) (hj : j < (cSqfreeYunFF p).length) :
    Squarefree (toPoly ((cSqfreeYunFF p).get ⟨j, hj⟩)) := by
  have haj := cSqfreeYunFFG_get_assoc hgcd p hp0 hpp j hj
  exact fun y hy => sqfreeFactPart_squarefree (toPoly p) (1 + j) y (hy.trans haj.dvd)

omit [CDiffField α] [CDiffFieldSpec α] in
/-- Each tower Yun factor is nonzero, from the correspondence and `sqfreeFactPart_ne_zero`. -/
theorem cSqfreeYunFFG_get_ne_zero [CharZero (CFieldSpec.K α)] (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α)))
    (p : DensePoly α) (hp0 : toPoly p ≠ 0) (hpp : (toPoly p).primPart ≠ 0)
    (j : ℕ) (hj : j < (cSqfreeYunFF p).length) :
    toPoly ((cSqfreeYunFF p).get ⟨j, hj⟩) ≠ 0 := fun h0 =>
  sqfreeFactPart_ne_zero (toPoly p) (1 + j)
    ((cSqfreeYunFFG_get_assoc hgcd p hp0 hpp j hj).eq_zero_iff.mp h0)

omit [CDiffField α] [CDiffFieldSpec α] in
/-- Each tower Yun factor is coprime to its derivative (squarefree gives coprime to `v'`, char `0`). -/
theorem cSqfreeYunFFG_coprime_deriv [CharZero (CFieldSpec.K α)] (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α)))
    (p : DensePoly α) (hp0 : toPoly p ≠ 0) (hpp : (toPoly p).primPart ≠ 0)
    (j : ℕ) (hj : j < (cSqfreeYunFF p).length) :
    IsCoprime (toPoly ((cSqfreeYunFF p).get ⟨j, hj⟩))
      (derivative (toPoly ((cSqfreeYunFF p).get ⟨j, hj⟩))) :=
  squarefree_iff_isCoprime_derivative.mp (cSqfreeYunFFG_squarefree hgcd p hp0 hpp j hj)

open UniqueFactorizationMonoid in
omit [CDiffField α] [CDiffFieldSpec α] in
/-- The Yun go-loop runs at least `maxmult − (i−1)` steps. With `YunInv (toPoly p) i` the working
`b` is `C c · squarefreePart (deflation (toPoly p) (i−1))`, so `cdeg b = 0 ⟺ maxmult ≤ i−1`
(`squarefreePart_deflation_natDegree_eq_zero_iff_maxmult`); each non-terminal step deflates to `i+1`
(`yunStep_preserves` + the deflate bridges), so the emitted list has length `≥ maxmult − (i−1)`. -/
theorem length_cSqfreeYunFFGgoWf_ge [CharZero (CFieldSpec.K α)] (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α)))
    (p : DensePoly α) (hpp : (toPoly p).primPart ≠ 0) :
    ∀ (fo i : ℕ) (b d : DensePoly α), 1 ≤ i →
      YunInv (toPoly p) i (toPoly b) (toPoly d) →
      (normalizedFactors (toPoly p).primPart).toFinset.sup
          (fun P => (normalizedFactors (toPoly p).primPart).count P) - (i - 1) ≤ fo →
      (normalizedFactors (toPoly p).primPart).toFinset.sup
          (fun P => (normalizedFactors (toPoly p).primPart).count P) - (i - 1)
        ≤ (cSqfreeYunFFGgoWf fo b d).length := by
  set M := (normalizedFactors (toPoly p).primPart).toFinset.sup
    (fun P => (normalizedFactors (toPoly p).primPart).count P) with hM
  intro fo
  induction fo with
  | zero => intro i b d _ _ hfo; simp only [Nat.le_zero] at hfo; rw [hfo]; exact Nat.zero_le _
  | succ fo ih =>
    intro i b d hi hinv hfo
    rw [cSqfreeYunFFGgoWf]
    by_cases hdeg : cdeg b = 0
    · rw [if_pos hdeg]
      obtain ⟨c, hc, hb, _⟩ := hinv
      have hMle : M ≤ i - 1 := by
        rw [cdegG_eq_natDegree, hb, natDegree_C_mul hc] at hdeg
        rw [hM, ← squarefreePart_deflation_natDegree_eq_zero_iff_maxmult (toPoly p) (i - 1) hpp]
        exact hdeg
      simp only [List.length_nil]; omega
    · rw [if_neg hdeg]
      simp only [CPolyGcd.compute_dense_wf_eq]
      have hbne : toPoly b ≠ 0 := by
        intro h0; apply hdeg; rw [cdegG_eq_natDegree, h0, natDegree_zero]
      have hMgt : i ≤ M := by
        by_contra hlt
        obtain ⟨c, hc, hb, _⟩ := hinv
        apply hdeg
        rw [cdegG_eq_natDegree, hb, natDegree_C_mul hc,
          show Babs (toPoly p) i = squarefreePart (deflation (toPoly p) (i - 1)) from rfl,
          squarefreePart_deflation_natDegree_eq_zero_iff_maxmult (toPoly p) (i - 1) hpp, ← hM]
        omega
      have hinv' : YunInv (toPoly p) (i + 1)
          (toPoly (CPolyEuclidean.div b (cmonic (CFracGcdCoreWf.cgcdFFCoreWf b d))))
          (toPoly (csub (CPolyEuclidean.div d (cmonic (CFracGcdCoreWf.cgcdFFCoreWf b d)))
            (cderiv (CPolyEuclidean.div b (cmonic (CFracGcdCoreWf.cgcdFFCoreWf b d)))))) := by
        rw [toPolyG_yunDeflate_fst hgcd b d hbne, toPolyG_yunDeflate_snd hgcd b d hbne]
        exact (yunStep_preserves (toPoly p) i hi hpp hinv).2
      have hih := ih (i + 1) _ _ (by omega) hinv' (by omega)
      rw [List.length_cons]
      omega

open UniqueFactorizationMonoid in
omit [CDiffField α] [CDiffFieldSpec α] in
/-- The Yun factorization has length `≥ maxmult`. The entry runs the go-loop from `i = 1` with
fuel `cyunBound p ≥ maxmult` (`sup_count_le_natDegree_primPart` + `primPart_dvd` +
`length_cnormG_of_ne`), so `length_cSqfreeYunFFGgoWf_ge` at `i = 1` gives `maxmult ≤ length`. -/
theorem length_cSqfreeYunFFG_ge [CharZero (CFieldSpec.K α)] (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α)))
    (p : DensePoly α) (hp0 : toPoly p ≠ 0) (hpp : (toPoly p).primPart ≠ 0) :
    (normalizedFactors (toPoly p).primPart).toFinset.sup
        (fun P => (normalizedFactors (toPoly p).primPart).count P) ≤ (cSqfreeYunFF p).length := by
  rw [cSqfreeYunFF]
  simp only [CPolyGcd.compute_dense_wf_eq]
  have hinv : YunInv (toPoly p) 1
      (toPoly (CPolyEuclidean.div p (CFracGcdCoreWf.cgcdFFCoreWf p (cderiv p))))
      (toPoly (csub (CPolyEuclidean.div (cderiv p) (CFracGcdCoreWf.cgcdFFCoreWf p (cderiv p)))
        (cderiv (CPolyEuclidean.div p (CFracGcdCoreWf.cgcdFFCoreWf p (cderiv p)))))) :=
    toPolyG_yunEntry_YunInv hgcd p hp0 hpp
  have hfuel : (normalizedFactors (toPoly p).primPart).toFinset.sup
      (fun P => (normalizedFactors (toPoly p).primPart).count P) ≤ cyunBound p := by
    have hcn : cnorm p ≠ [] := fun h => hp0 ((cisZeroG_iff p).mp (by simp [cisZero, h]))
    rw [cyunBound, length_cnormG_of_ne p hcn]
    have h1 := sup_count_le_natDegree_primPart (toPoly p) hpp
    have h2 : (toPoly p).primPart.natDegree ≤ (toPoly p).natDegree :=
      natDegree_le_of_dvd (toPoly p).primPart_dvd hp0
    omega
  have h := length_cSqfreeYunFFGgoWf_ge hgcd p hpp (cyunBound p) 1 _ _ le_rfl hinv (by simpa using hfuel)
  simpa using h

open UniqueFactorizationMonoid in
omit [CDiffField α] [CDiffFieldSpec α] in
/-- The Yun factorization reconstructs its input up to associates:
`toPoly d ~ prodPow 1 (Yun factors)`. Chains the factorwise correspondence
(`cSqfreeYunFFG_forall₂` through `prodPow_associated`), the range reconstruction
(`prodPow_one_sqfreeFactPart_range_associated`, discharged by `length_cSqfreeYunFFG_ge`), and
`pp(d) ~ d`. -/
theorem cSqfreeYunFFG_reconstruction [CharZero (CFieldSpec.K α)] (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α)))
    (d : DensePoly α) (hd0 : toPoly d ≠ 0) (hpp : (toPoly d).primPart ≠ 0) :
    Associated (toPoly d) (prodPow 1 ((cSqfreeYunFF d).map toPoly)) := by
  have h1 : Associated (prodPow 1 ((cSqfreeYunFF d).map toPoly))
      (prodPow 1 ((List.range (cSqfreeYunFF d).length).map
        (fun j => sqfreeFactPart (toPoly d) (1 + j)))) :=
    prodPow_associated (cSqfreeYunFFG_forall₂ hgcd d hd0 hpp) 1
  have h2 : Associated (prodPow 1 ((List.range (cSqfreeYunFF d).length).map
        (fun j => sqfreeFactPart (toPoly d) (1 + j)))) (toPoly d).primPart :=
    prodPow_one_sqfreeFactPart_range_associated (toPoly d) hpp _
      (length_cSqfreeYunFFG_ge hgcd d hd0 hpp)
  exact ((h1.trans h2).trans (associated_primPart_self (toPoly d) hd0)).symm

/-- A monic, split, squarefree polynomial is the `nodal` polynomial of its root set:
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
/-- Every Yun go-loop factor is monic: each emitted factor is `cmonic (cgcdFFCoreWf b d)`, whose
`toPoly` is monic (`monic_toPolyG_cmonicG`); the working `b` stays nonzero through the deflation. -/
theorem cSqfreeYunFFGgoWf_monic (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) :
    ∀ (fo : ℕ) (b d : DensePoly α), toPoly b ≠ 0 →
      ∀ p ∈ cSqfreeYunFFGgoWf fo b d, (toPoly p).Monic := by
  intro fo
  induction fo with
  | zero => intro b d _ p hp; simp [cSqfreeYunFFGgoWf] at hp
  | succ fo ih =>
    intro b d hb p hp
    rw [cSqfreeYunFFGgoWf] at hp
    by_cases hdeg : cdeg b = 0
    · rw [if_pos hdeg] at hp; simp at hp
    · rw [if_neg hdeg, List.mem_cons] at hp
      simp only [CPolyGcd.compute_dense_wf_eq] at hp
      have hgne : gcd (toPoly b) (toPoly d) ≠ 0 :=
        fun h => hb (zero_dvd_iff.mp (h ▸ gcd_dvd_left (toPoly b) (toPoly d)))
      have hcg : toPoly (CFracGcdCoreWf.cgcdFFCoreWf b d) ≠ 0 :=
        fun h => hgne ((hgcd b d).eq_zero_iff.mp h)
      rcases hp with rfl | hp
      · exact monic_toPolyG_cmonicG _ hcg
      · have hb' : toPoly (CPolyEuclidean.div b (cmonic (CFracGcdCoreWf.cgcdFFCoreWf b d))) ≠ 0 := by
          rw [toPolyG_yunDeflate_fst hgcd b d hb]
          intro h
          apply hb
          rw [← EuclideanDomain.mul_div_cancel' hgne (gcd_dvd_left (toPoly b) (toPoly d)), h,
            mul_zero]
        exact ih _ _ hb' p hp

omit [CDiffFieldSpec α] in
/-- The Yun radical `Dstar` is squarefree: a product of the pairwise-coprime, squarefree Yun
factors (`squarefree_list_prod`). -/
theorem toPolyG_cHermiteReduceTowerG_Dstar_squarefree [CharZero (CFieldSpec.K α)]
    (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) (Dt a d : DensePoly α) (hd0 : toPoly d ≠ 0)
    (hpp : (toPoly d).primPart ≠ 0) :
    Squarefree (toPoly (cHermiteReduceTower Dt a d).2.2) := by
  rw [cHermiteReduceTower, squarefreeYun_dense_wf_eq]
  simp only [denote, map_one, mul_zero, add_zero, one_mul]
  apply squarefree_list_prod
  · rw [List.pairwise_map, List.pairwise_iff_getElem]
    intro i j hi hj hij
    exact cSqfreeYunFFG_isRelPrime hgcd d hd0 hpp hi hj (Nat.ne_of_lt hij)
  · intro b hb
    rw [List.mem_map] at hb
    obtain ⟨f, hf, rfl⟩ := hb
    obtain ⟨k, hk, hfk⟩ := List.mem_iff_getElem.mp hf
    rw [← hfk]
    exact cSqfreeYunFFG_squarefree hgcd d hd0 hpp k hk

omit [CDiffField α] [CDiffFieldSpec α] in
/-- Every Yun factor is monic: the go-loop runs from `b₁ = d / gcd(d, d′) ≠ 0`. -/
theorem cSqfreeYunFFG_monic (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) (d : DensePoly α) (hd0 : toPoly d ≠ 0) :
    ∀ p ∈ cSqfreeYunFF d, (toPoly p).Monic := by
  rw [cSqfreeYunFF]
  simp only [CPolyGcd.compute_dense_wf_eq]
  apply cSqfreeYunFFGgoWf_monic hgcd
  set g := CFracGcdCoreWf.cgcdFFCoreWf d (cderiv d) with hgdef
  have hgp : toPoly g ∣ toPoly d :=
    (hgcd d (cderiv d)).dvd.trans (gcd_dvd_left (toPoly d) (toPoly (cderiv d)))
  have hgn : cnorm g ≠ [] := fun h =>
    hd0 (zero_dvd_iff.mp (((cisZeroG_iff g).mp (by simp [cisZero, h])) ▸ hgp))
  have hex : toPoly (CPolyEuclidean.div d g) * toPoly g = toPoly d := by
    simpa only [CPolyEuclidean.div_dense_eq] using toPolyG_div_exact d g hgn hgp
  intro h; apply hd0; rw [← hex, h, zero_mul]

omit [CDiffFieldSpec α] in
/-- The Yun radical `Dstar` is monic: a product of the monic Yun factors (`monic_list_prod`). -/
theorem toPolyG_cHermiteReduceTowerG_Dstar_monic (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) (Dt a d : DensePoly α)
    (hd0 : toPoly d ≠ 0) : (toPoly (cHermiteReduceTower Dt a d).2.2).Monic := by
  rw [cHermiteReduceTower, squarefreeYun_dense_wf_eq]
  simp only [denote, map_one, mul_zero, add_zero, one_mul]
  apply monic_list_prod
  intro p hp
  rw [List.mem_map] at hp
  obtain ⟨f, hf, rfl⟩ := hp
  exact cSqfreeYunFFG_monic hgcd d hd0 f hf

omit [CDiffFieldSpec α] in
/-- If the Yun radical `Dstar` splits over `K` (the rational-residue slice),
then `Dstar = nodal (its root set)` — the `hden` hypothesis of the RT residue-match assemblers. Monic
and squarefree are supplied by the Yun structure; `hsplit` is the genuine rational-residue restriction. -/
theorem toPolyG_cHermiteReduceTowerG_Dstar_eq_nodal [CharZero (CFieldSpec.K α)]
    (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) (Dt a d : DensePoly α) (hd0 : toPoly d ≠ 0)
    (hpp : (toPoly d).primPart ≠ 0)
    (hsplit : (toPoly (cHermiteReduceTower Dt a d).2.2).Splits) :
    toPoly (cHermiteReduceTower Dt a d).2.2
      = Lagrange.nodal (toPoly (cHermiteReduceTower Dt a d).2.2).roots.toFinset id :=
  split_squarefree_eq_nodal _ (toPolyG_cHermiteReduceTowerG_Dstar_monic hgcd Dt a d hd0) hsplit
    (toPolyG_cHermiteReduceTowerG_Dstar_squarefree hgcd Dt a d hd0 hpp)

omit [CDiffField α] [CDiffFieldSpec α] in
/-- `cSqfreeYunFF` is a lawful squarefree decomposition, bundling reconstruction, monicity,
squarefreeness, and pairwise coprimality. -/
theorem cSqfreeYunFFG_lawfulSquarefreeDecomposition [CharZero (CFieldSpec.K α)]
    (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) (d : DensePoly α) (hd0 : toPoly d ≠ 0)
    (hpp : (toPoly d).primPart ≠ 0) :
    LawfulSquarefreeDecomposition d (cSqfreeYunFF d) :=
  { reconstruct := by
      have hmap : (cSqfreeYunFF d).map CPoly.toPoly =
          (cSqfreeYunFF d).map DensePoly.toPoly := by
        apply List.map_congr_left
        intro p _
        exact toPoly_list_eq p
      rw [toPoly_list_eq, hmap]
      exact cSqfreeYunFFG_reconstruction hgcd d hd0 hpp
    monic := by
      intro p hp
      simpa only [toPoly_list_eq] using cSqfreeYunFFG_monic hgcd d hd0 p hp
    squarefree := fun p hp => by
      obtain ⟨k, hk, hpk⟩ := List.mem_iff_getElem.mp hp
      rw [← hpk]
      simpa only [List.get_eq_getElem, toPoly_list_eq] using
        cSqfreeYunFFG_squarefree hgcd d hd0 hpp k hk
    coprime := by
      rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      simpa only [List.get_eq_getElem, toPoly_list_eq] using
        cSqfreeYunFFG_isRelPrime hgcd d hd0 hpp hi hj (Nat.ne_of_lt hij) }

omit [CDiffField α] [CDiffFieldSpec α] in
/-- The selected fraction-free Yun decomposition satisfies the representation-level squarefree contract. -/
instance instLawfulCPolySquarefreeDenseWf [CharZero (CFieldSpec.K α)]
    [Fact (CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α)))] :
    LawfulCPolySquarefree DensePoly α where
  compute_lawful d hd0 hpp := by
    have hd0' : toPoly d ≠ 0 := by simpa only [toPoly_list_eq] using hd0
    have hpp' : (toPoly d).primPart ≠ 0 := by simpa only [toPoly_list_eq] using hpp
    simpa only [squarefreeYun_dense_wf_eq] using
      cSqfreeYunFFG_lawfulSquarefreeDecomposition (Fact.out (p :=
        CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α)))) d hd0' hpp'

/-! ### The Yun factorization of a constant is empty -/

omit [CDiffField α] [CDiffFieldSpec α] [CFieldSpec α] in
/-- The Yun go-loop is empty once its working polynomial is a constant (`cdeg b = 0` fires the
terminating `if`). -/
theorem cSqfreeYunFFGgoWf_eq_nil_of_cdegG_zero (fo : ℕ) (b d : DensePoly α) (hb : cdeg b = 0) :
    cSqfreeYunFFGgoWf fo b d = [] := by
  cases fo with
  | zero => rfl
  | succ n => rw [cSqfreeYunFFGgoWf]; exact if_pos hb

omit [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α] in
/-- Dividing a constant stays a constant under the selected Euclidean implementation. -/
theorem cdegG_div_eq_zero_of_cdegG_zero (p q : DensePoly α) (hp : cdeg p = 0) :
    cdeg (CPolyEuclidean.div p q) = 0 := by
  by_cases hq : toPoly q = 0
  · -- zero divisor: `CPolyEuclidean.div p q = []` (the `cisZero` branch of `cdivmodWf`)
    have hcz : cisZero (cnorm q) = true := by
      rw [cisZeroG_cnormG]
      exact (cisZeroG_iff q).mpr hq
    have hnil : CPolyEuclidean.div p q = ([] : DensePoly α) := by
      show (cdivmodWf p q).1 = []
      simp [cdivmodWf.eq_def, hcz]
    rw [hnil]; rfl
  rw [cdegG_eq_natDegree] at hp ⊢
  simpa only [toPoly_list_eq] using
    CPolyEuclidean.div_natDegree_eq_zero_of_natDegree_eq_zero p q
      (by simpa only [toPoly_list_eq] using hp)
      (by simpa only [toPoly_list_eq] using hq)

omit [CDiffField α] [CDiffFieldSpec α] in
/-- The Yun factorization of a constant is empty (`cdeg p = 0 ⟹ cSqfreeYunFF p = []`). -/
theorem cSqfreeYunFFG_eq_nil_of_cdegG_zero (p : DensePoly α) (hp : cdeg p = 0) :
    cSqfreeYunFF p = [] := by
  rw [cSqfreeYunFF]
  exact cSqfreeYunFFGgoWf_eq_nil_of_cdegG_zero _ _ _
    (cdegG_div_eq_zero_of_cdegG_zero p _ hp)

end DeepWiki.SymbolicIntegration
