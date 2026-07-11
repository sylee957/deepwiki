import DeepWiki.Algebra.ListProducts
import DeepWiki.ComputableAlgebra.PolySquarefree
import DeepWiki.SymbolicIntegration.SquarefreeFactorization

/-! # Interface: `LawfulSquarefreeDecomposition`

The squarefree-decomposition stage of the Risch reduced case, stated purely against the polynomial
denotation `toPoly` — no concrete algorithm. A list `decomp = [v₁, …, vₘ]` (the multiplicity-`i` factor at
index `i-1`) is a *lawful* squarefree decomposition of `d` when its factors denote a monic, squarefree,
pairwise-coprime family whose powered product `∏ᵢ vᵢ^i` reconstructs `d` up to associates. Algorithmic
realizations live with the squarefree decomposition engines. -/

open Polynomial Classical

namespace DeepWiki.SymbolicIntegration

universe u v

/-- **The product of pairwise-coprime squarefree polynomials is squarefree** (list form). -/
theorem squarefree_list_prod {K : Type*} [Field K] (L : List K[X])
    (hpw : L.Pairwise IsRelPrime) (hsf : ∀ a ∈ L, Squarefree a) : Squarefree L.prod := by
  induction L with
  | nil => simp
  | cons a t ih =>
    rw [List.pairwise_cons] at hpw
    rw [List.prod_cons, squarefree_mul_iff]
    exact ⟨isRelPrime_list_prod_right a t (fun b hb => hpw.1 b hb),
      hsf a (List.mem_cons_self ..),
      ih hpw.2 (fun x hx => hsf x (List.mem_cons_of_mem a hx))⟩

/-- The product of monic polynomials is monic (list form). -/
theorem monic_list_prod {K : Type*} [Field K] (L : List K[X]) (h : ∀ p ∈ L, p.Monic) :
    L.prod.Monic := by
  induction L with
  | nil => simp
  | cons a t ih =>
    rw [List.prod_cons]
    exact (h a (List.mem_cons_self ..)).mul (ih (fun p hp => h p (List.mem_cons_of_mem a hp)))

variable {P : Type u → Type u} [CPoly P]
variable {α : Type u} [CField α] [CFieldSpec.{u,v} α]

/-- File-local bridge from a selected lawful gcd to the mathematical polynomial gcd. -/
private theorem selectedGcd_associated [CPolyEngine P] [CPolyGcd P α]
    [LawfulCPolyGcd.{u,v} P α] (p q : P α) :
    Associated (CPoly.toPoly (CPolyGcd.compute p q)) (gcd (CPoly.toPoly p) (CPoly.toPoly q)) := by
  obtain ⟨hleft, hright, hgreatest⟩ := LawfulCPolyGcd.compute_isGCD' p q
  apply associated_of_dvd_dvd (dvd_gcd hleft hright)
  exact hgreatest _ (gcd_dvd_left _ _) (gcd_dvd_right _ _)

/-- File-local bridge showing engine monic normalization preserves association. -/
private theorem cmonic_associated [CPolyEngine P] [LawfulCPolyEngine.{u,v} P]
    (p : P α) (hp : CPoly.toPoly p ≠ 0) :
    Associated (CPoly.toPoly (CPolyEngine.cmonic p)) (CPoly.toPoly p) := by
  have hlead : (CPoly.toPoly p).leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
  rw [CPolyEngine.toPoly_cmonic_of_ne_zero p hp]
  refine ⟨(isUnit_C.mpr (isUnit_iff_ne_zero.mpr hlead)).unit, ?_⟩
  rw [IsUnit.unit_spec]
  calc
    Polynomial.C (CPoly.toPoly p).leadingCoeff⁻¹ * CPoly.toPoly p *
        Polynomial.C (CPoly.toPoly p).leadingCoeff =
      (Polynomial.C (CPoly.toPoly p).leadingCoeff⁻¹ *
        Polynomial.C (CPoly.toPoly p).leadingCoeff) * CPoly.toPoly p := by ring
    _ = CPoly.toPoly p := by
      rw [← Polynomial.C_mul, inv_mul_cancel₀ hlead, Polynomial.C_1, one_mul]

/-- An exact selected Euclidean quotient is associated to the mathematical quotient. -/
private theorem selectedDiv_associated_quotient [CPolyEngine P] [CPolyEuclidean P]
    [LawfulCPolyEuclidean.{u,v} P] (p q : P α) (hq : CPoly.toPoly q ≠ 0)
    (hdvd : CPoly.toPoly q ∣ CPoly.toPoly p) :
    Associated (CPoly.toPoly (CPolyEuclidean.div p q))
      (CPoly.toPoly p / CPoly.toPoly q) := by
  have hexact := LawfulCPolyEuclidean.div_exact (P := P) p q hq hdvd
  have hquot : Associated (CPoly.toPoly p / CPoly.toPoly q)
      (CPoly.toPoly (CPolyEuclidean.div p q)) := by
    rw [associated_div_iff hq hdvd]
    rw [← hexact]
  exact hquot.symm

/-- A common nonzero constant rescaling preserves the abstract Yun state invariant. -/
private theorem yunInv_smul {K : Type*} [Field K] (A : K[X]) (i : ℕ) {b d : K[X]}
    (h : YunInv A i b d) {e : K} (he : e ≠ 0) :
    YunInv A i (Polynomial.C e * b) (Polynomial.C e * d) := by
  obtain ⟨c, hc, hb, hd⟩ := h
  exact ⟨e * c, mul_ne_zero he hc, by rw [hb, ← mul_assoc, ← Polynomial.C_mul],
    by rw [hd, ← mul_assoc, ← Polynomial.C_mul]⟩

/-- An exact polynomial product reads as the corresponding Euclidean quotient. -/
private theorem quotient_eq_of_mul_eq {K : Type*} [Field K] {X g b : K[X]}
    (hg : g ≠ 0) (h : X * g = b) : X = b / g := by
  have hdvd : g ∣ b := ⟨X, by rw [← h, mul_comm]⟩
  have hcancel : g * (b / g) = b := EuclideanDomain.mul_div_cancel' hg hdvd
  exact (mul_left_cancel₀ hg (by rw [hcancel, ← h, mul_comm])).symm

/-- The selected gcd/division initialization of the generic Yun kernel denotes `YunInv A 1`. -/
private theorem defaultInit_yunInv [CPolyEngine P] [LawfulCPolyEngine.{u,v} P]
    [CPolyEuclidean P] [LawfulCPolyEuclidean.{u,v} P] [CPolyGcd P α]
    [LawfulCPolyGcd.{u,v} P α] [CharZero (CFieldSpec.K α)] (p : P α) (hp0 : CPoly.toPoly p ≠ 0)
    (hpp : (CPoly.toPoly p).primPart ≠ 0) :
    YunInv (CPoly.toPoly p) 1
      (CPoly.toPoly (CPolyEuclidean.div p (CPolyGcd.compute p (CPolyEngine.deriv p))))
      (CPoly.toPoly (CPolyEngine.sub
        (CPolyEuclidean.div (CPolyEngine.deriv p) (CPolyGcd.compute p (CPolyEngine.deriv p)))
        (CPolyEngine.deriv (CPolyEuclidean.div p (CPolyGcd.compute p (CPolyEngine.deriv p)))))) := by
  set A := CPoly.toPoly p with hA
  set g := CPolyGcd.compute p (CPolyEngine.deriv p) with hg
  set G := gcd A (derivative A) with hG
  have hA' : CPoly.toPoly (CPolyEngine.deriv p) = derivative A := by
    rw [LawfulCPolyEngine.toPoly_deriv, hA]
  have hG0 : G ≠ 0 := fun h => hp0 (zero_dvd_iff.mp (h ▸ gcd_dvd_left A (derivative A)))
  have hassoc : Associated (CPoly.toPoly g) G := by
    have h := selectedGcd_associated (P := P) p (CPolyEngine.deriv p)
    rw [hA'] at h
    exact h
  obtain ⟨u, hu⟩ := hassoc.symm
  obtain ⟨k, hkunit, hkC⟩ := Polynomial.isUnit_iff.mp u.isUnit
  have hk0 : k ≠ 0 := isUnit_iff_ne_zero.mp hkunit
  have hgval : CPoly.toPoly g = Polynomial.C k * G := by rw [← hu, ← hkC]; ring
  have hg0 : CPoly.toPoly g ≠ 0 := fun h => hG0 (zero_dvd_iff.mp (h ▸ hassoc.dvd))
  have hgA : CPoly.toPoly g ∣ A := hassoc.dvd.trans (gcd_dvd_left A (derivative A))
  have hgA' : CPoly.toPoly g ∣ derivative A :=
    hassoc.dvd.trans (gcd_dvd_right A (derivative A))
  have hkinv : Polynomial.C k⁻¹ * Polynomial.C k = 1 := by
    rw [← Polynomial.C_mul, inv_mul_cancel₀ hk0, Polynomial.C_1]
  have hbex : CPoly.toPoly (CPolyEuclidean.div p g) * CPoly.toPoly g = A := by
    simpa only [mul_comm] using
      (LawfulCPolyEuclidean.div_exact (P := P) p g hg0 hgA).symm
  have hdex : CPoly.toPoly (CPolyEuclidean.div (CPolyEngine.deriv p) g) * CPoly.toPoly g =
      derivative A := by
    have h := LawfulCPolyEuclidean.div_exact (P := P) (CPolyEngine.deriv p) g hg0 (by
      rw [hA']
      exact hgA')
    rw [hA'] at h
    simpa only [mul_comm] using h.symm
  have hAG : A / G = CPoly.toPoly (CPolyEuclidean.div p g) * Polynomial.C k :=
    (quotient_eq_of_mul_eq hG0 (by rw [← hbex, hgval]; ring)).symm
  have hA'G : derivative A / G =
      CPoly.toPoly (CPolyEuclidean.div (CPolyEngine.deriv p) g) * Polynomial.C k :=
    (quotient_eq_of_mul_eq hG0 (by rw [← hdex, hgval]; ring)).symm
  have heqb : CPoly.toPoly (CPolyEuclidean.div p g) = Polynomial.C k⁻¹ * (A / G) := by
    rw [hAG, show Polynomial.C k⁻¹ *
        (CPoly.toPoly (CPolyEuclidean.div p g) * Polynomial.C k) =
        CPoly.toPoly (CPolyEuclidean.div p g) * (Polynomial.C k⁻¹ * Polynomial.C k) from by ring,
      hkinv, mul_one]
  have heqd : CPoly.toPoly (CPolyEngine.sub (CPolyEuclidean.div (CPolyEngine.deriv p) g)
      (CPolyEngine.deriv (CPolyEuclidean.div p g))) =
      Polynomial.C k⁻¹ * (derivative A / G - derivative (A / G)) := by
    rw [CPolyEngine.toPoly_sub, LawfulCPolyEngine.toPoly_deriv, heqb, derivative_C_mul,
      mul_sub, hA'G,
      show Polynomial.C k⁻¹ *
          (CPoly.toPoly (CPolyEuclidean.div (CPolyEngine.deriv p) g) * Polynomial.C k) =
          CPoly.toPoly (CPolyEuclidean.div (CPolyEngine.deriv p) g) *
            (Polynomial.C k⁻¹ * Polynomial.C k) from by ring,
      hkinv, mul_one]
  change YunInv A 1 (CPoly.toPoly (CPolyEuclidean.div p g))
    (CPoly.toPoly (CPolyEngine.sub (CPolyEuclidean.div (CPolyEngine.deriv p) g)
      (CPolyEngine.deriv (CPolyEuclidean.div p g))))
  rw [heqb, heqd]
  letI : CharZero (CRingSpec.R α) := by
    change CharZero (CFieldSpec.K α)
    infer_instance
  exact yunInv_smul A 1 (yunInv_base A (by simpa [hA] using hp0) (by simpa [hA] using hpp))
    (inv_ne_zero hk0)

/-- The selected monic gcd is exactly the mathematical monic gcd whenever the left input is nonzero. -/
private theorem selectedMonicGcd_eq_gcd [CPolyEngine P] [LawfulCPolyEngine.{u,v} P]
    [CPolyGcd P α] [LawfulCPolyGcd.{u,v} P α] (b d : P α) (hb : CPoly.toPoly b ≠ 0) :
    CPoly.toPoly (CPolyEngine.cmonic (CPolyGcd.compute b d)) =
      gcd (CPoly.toPoly b) (CPoly.toPoly d) := by
  set g := CPolyGcd.compute b d with hg
  have hassoc : Associated (CPoly.toPoly g) (gcd (CPoly.toPoly b) (CPoly.toPoly d)) :=
    selectedGcd_associated b d
  have hg0 : CPoly.toPoly g ≠ 0 := fun h =>
    hb (zero_dvd_iff.mp (h ▸ hassoc.dvd.trans (gcd_dvd_left _ _)))
  have hlead : (CPoly.toPoly g).leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hg0
  have hmonic : (CPoly.toPoly (CPolyEngine.cmonic g)).Monic := by
    rw [CPolyEngine.toPoly_cmonic_of_ne_zero g hg0, Polynomial.Monic,
      Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, inv_mul_cancel₀ hlead]
  have hfactor : Associated (CPoly.toPoly (CPolyEngine.cmonic g))
      (gcd (CPoly.toPoly b) (CPoly.toPoly d)) :=
    (cmonic_associated g hg0).trans hassoc
  rw [← hmonic.normalize_eq_self,
    normalize_eq_normalize_iff_associated.mpr hfactor, normalize_gcd]

/-- One selected Yun deflation's first component denotes the abstract quotient state. -/
private theorem defaultGo_deflate_fst_toPoly [CPolyEngine P] [LawfulCPolyEngine.{u,v} P]
    [CPolyEuclidean P] [LawfulCPolyEuclidean.{u,v} P] [CPolyGcd P α]
    [LawfulCPolyGcd.{u,v} P α] (b d : P α) (hb : CPoly.toPoly b ≠ 0) :
    CPoly.toPoly (CPolyEuclidean.div b (CPolyEngine.cmonic (CPolyGcd.compute b d))) =
      CPoly.toPoly b / gcd (CPoly.toPoly b) (CPoly.toPoly d) := by
  let factor := CPolyEngine.cmonic (CPolyGcd.compute b d)
  have hfactor : CPoly.toPoly factor = gcd (CPoly.toPoly b) (CPoly.toPoly d) :=
    selectedMonicGcd_eq_gcd b d hb
  have hfactor0 : CPoly.toPoly factor ≠ 0 := by
    rw [hfactor]
    exact fun h => hb (zero_dvd_iff.mp (h ▸ gcd_dvd_left _ _))
  calc
    CPoly.toPoly (CPolyEuclidean.div b factor) = CPoly.toPoly b / CPoly.toPoly factor :=
      CPolyEuclidean.toPoly_div_eq_div b factor hfactor0 (by
        rw [hfactor]
        exact gcd_dvd_left _ _)
    _ = CPoly.toPoly b / gcd (CPoly.toPoly b) (CPoly.toPoly d) := by rw [hfactor]

/-- One selected Yun deflation's second component denotes the abstract residual state. -/
private theorem defaultGo_deflate_snd_toPoly [CPolyEngine P] [LawfulCPolyEngine.{u,v} P]
    [CPolyEuclidean P] [LawfulCPolyEuclidean.{u,v} P] [CPolyGcd P α]
    [LawfulCPolyGcd.{u,v} P α] (b d : P α) (hb : CPoly.toPoly b ≠ 0) :
    CPoly.toPoly (CPolyEngine.sub
      (CPolyEuclidean.div d (CPolyEngine.cmonic (CPolyGcd.compute b d)))
      (CPolyEngine.deriv (CPolyEuclidean.div b (CPolyEngine.cmonic (CPolyGcd.compute b d))))) =
      CPoly.toPoly d / gcd (CPoly.toPoly b) (CPoly.toPoly d) -
        derivative (CPoly.toPoly b / gcd (CPoly.toPoly b) (CPoly.toPoly d)) := by
  let factor := CPolyEngine.cmonic (CPolyGcd.compute b d)
  have hfactor : CPoly.toPoly factor = gcd (CPoly.toPoly b) (CPoly.toPoly d) :=
    selectedMonicGcd_eq_gcd b d hb
  have hfactor0 : CPoly.toPoly factor ≠ 0 := by
    rw [hfactor]
    exact fun h => hb (zero_dvd_iff.mp (h ▸ gcd_dvd_left _ _))
  rw [CPolyEngine.toPoly_sub, LawfulCPolyEngine.toPoly_deriv,
    CPolyEuclidean.toPoly_div_eq_div d factor hfactor0 (by
      rw [hfactor]
      exact gcd_dvd_right _ _), defaultGo_deflate_fst_toPoly b d hb, hfactor]

/-- The abstract Yun loop does not depend on its phantom polynomial or multiplicity parameters. -/
private theorem yunLoopAbs_irrelevant {K : Type*} [Field K] (A A' : K[X]) :
    ∀ (n : ℕ) (p : K[X] × K[X]) (i j : ℕ), yunLoopAbs A p i n = yunLoopAbs A' p j n := by
  intro n
  induction n with
  | zero => intro p i j; rfl
  | succ n ih =>
    intro p i j
    obtain ⟨b, d⟩ := p
    simp only [yunLoopAbs]
    rw [ih _ (i + 1) (j + 1)]

/-- The selected bounded Yun loop denotes the abstract Yun loop for its actual output length. -/
private theorem defaultGo_map_toPoly_eq_yunLoopAbs [CPolyEngine P] [LawfulCPolyEngine.{u,v} P]
    [CPolyEuclidean P] [LawfulCPolyEuclidean.{u,v} P] [CPolyGcd P α]
    [LawfulCPolyGcd.{u,v} P α] :
    ∀ (fuel : ℕ) (b d : P α),
      (CPolySquarefree.defaultGo fuel b d).map CPoly.toPoly =
        yunLoopAbs (0 : (CRingSpec.R α)[X]) (CPoly.toPoly b, CPoly.toPoly d) 1
          (CPolySquarefree.defaultGo fuel b d).length := by
  intro fuel
  induction fuel with
  | zero =>
    intro b d
    simp [CPolySquarefree.defaultGo, yunLoopAbs]
  | succ fuel ih =>
    intro b d
    rw [CPolySquarefree.defaultGo]
    by_cases hdeg : CPolyEngine.cdeg b = 0
    · rw [if_pos hdeg]
      simp [yunLoopAbs]
    · rw [if_neg hdeg]
      have hb : CPoly.toPoly b ≠ 0 := fun h => hdeg (by
        rw [LawfulCPolyEngine.cdeg_eq_natDegree, h, Polynomial.natDegree_zero])
      rw [List.map_cons, List.length_cons, selectedMonicGcd_eq_gcd b d hb]
      simp only [yunLoopAbs]
      congr 1
      rw [ih (CPolyEuclidean.div b (CPolyEngine.cmonic (CPolyGcd.compute b d)))
        (CPolyEngine.sub (CPolyEuclidean.div d (CPolyEngine.cmonic (CPolyGcd.compute b d)))
          (CPolyEngine.deriv (CPolyEuclidean.div b (CPolyEngine.cmonic (CPolyGcd.compute b d))))),
        defaultGo_deflate_fst_toPoly b d hb, defaultGo_deflate_snd_toPoly b d hb]
      exact yunLoopAbs_irrelevant _ _ _ _ _ _

open UniqueFactorizationMonoid in
/-- A generic Yun loop with sufficient fuel emits through its input's maximum multiplicity. -/
private theorem defaultGo_length_ge_maxMult [CPolyEngine P] [LawfulCPolyEngine.{u,v} P]
    [CPolyEuclidean P] [LawfulCPolyEuclidean.{u,v} P] [CPolyGcd P α]
    [LawfulCPolyGcd.{u,v} P α] [CharZero (CFieldSpec.K α)] (p : P α)
    (hpp : (CPoly.toPoly p).primPart ≠ 0) :
    ∀ (fuel i : ℕ) (b d : P α), 1 ≤ i →
      YunInv (CPoly.toPoly p) i (CPoly.toPoly b) (CPoly.toPoly d) →
      (normalizedFactors (CPoly.toPoly p).primPart).toFinset.sup
          (fun q => (normalizedFactors (CPoly.toPoly p).primPart).count q) - (i - 1) ≤ fuel →
      (normalizedFactors (CPoly.toPoly p).primPart).toFinset.sup
          (fun q => (normalizedFactors (CPoly.toPoly p).primPart).count q) - (i - 1) ≤
        (CPolySquarefree.defaultGo fuel b d).length := by
  letI : CharZero (CRingSpec.R α) := by
    change CharZero (CFieldSpec.K α)
    infer_instance
  set M := (normalizedFactors (CPoly.toPoly p).primPart).toFinset.sup
    (fun q => (normalizedFactors (CPoly.toPoly p).primPart).count q) with hM
  intro fuel
  induction fuel with
  | zero =>
    intro i b d _ _ hfuel
    simp only [Nat.le_zero] at hfuel
    rw [hfuel]
    exact Nat.zero_le _
  | succ fuel ih =>
    intro i b d hi hinv hfuel
    rw [CPolySquarefree.defaultGo]
    by_cases hdeg : CPolyEngine.cdeg b = 0
    · rw [if_pos hdeg]
      obtain ⟨c, hc, hb, _⟩ := hinv
      have hMle : M ≤ i - 1 := by
        rw [LawfulCPolyEngine.cdeg_eq_natDegree, hb, Polynomial.natDegree_C_mul hc] at hdeg
        rw [hM, ← squarefreePart_deflation_natDegree_eq_zero_iff_maxmult
          (CPoly.toPoly p) (i - 1) hpp]
        exact hdeg
      simp only [List.length_nil]
      omega
    · rw [if_neg hdeg]
      have hbne : CPoly.toPoly b ≠ 0 := fun h0 => hdeg (by
        rw [LawfulCPolyEngine.cdeg_eq_natDegree, h0, Polynomial.natDegree_zero])
      have hMgt : i ≤ M := by
        by_contra hlt
        obtain ⟨c, hc, hb, _⟩ := hinv
        apply hdeg
        rw [LawfulCPolyEngine.cdeg_eq_natDegree, hb, Polynomial.natDegree_C_mul hc,
          show Babs (CPoly.toPoly p) i =
            squarefreePart (deflation (CPoly.toPoly p) (i - 1)) from rfl,
          squarefreePart_deflation_natDegree_eq_zero_iff_maxmult
            (CPoly.toPoly p) (i - 1) hpp, ← hM]
        omega
      have hinv' : YunInv (CPoly.toPoly p) (i + 1)
          (CPoly.toPoly (CPolyEuclidean.div b (CPolyEngine.cmonic (CPolyGcd.compute b d))))
          (CPoly.toPoly (CPolyEngine.sub
            (CPolyEuclidean.div d (CPolyEngine.cmonic (CPolyGcd.compute b d)))
            (CPolyEngine.deriv
              (CPolyEuclidean.div b (CPolyEngine.cmonic (CPolyGcd.compute b d)))))) := by
        rw [defaultGo_deflate_fst_toPoly b d hbne, defaultGo_deflate_snd_toPoly b d hbne]
        exact (yunStep_preserves (CPoly.toPoly p) i hi hpp hinv).2
      have hih := ih (i + 1) _ _ (by omega) hinv' (by omega)
      rw [List.length_cons]
      omega

open UniqueFactorizationMonoid in
/-- The generic Yun decomposition has enough factors to cover every input multiplicity. -/
private theorem default_length_ge_maxMult [CPolyEngine P] [LawfulCPolyEngine.{u,v} P]
    [CPolyEuclidean P] [LawfulCPolyEuclidean.{u,v} P] [CPolyGcd P α]
    [LawfulCPolyGcd.{u,v} P α] [CharZero (CFieldSpec.K α)] (p : P α)
    (hp0 : CPoly.toPoly p ≠ 0) (hpp : (CPoly.toPoly p).primPart ≠ 0) :
    (normalizedFactors (CPoly.toPoly p).primPart).toFinset.sup
        (fun q => (normalizedFactors (CPoly.toPoly p).primPart).count q) ≤
      (CPolySquarefree.default p).length := by
  rw [CPolySquarefree.default]
  set g := CPolyGcd.compute p (CPolyEngine.deriv p)
  set b := CPolyEuclidean.div p g
  set d := CPolyEngine.sub (CPolyEuclidean.div (CPolyEngine.deriv p) g)
    (CPolyEngine.deriv b)
  have hinv : YunInv (CPoly.toPoly p) 1 (CPoly.toPoly b) (CPoly.toPoly d) := by
    simpa only [g, b, d] using defaultInit_yunInv p hp0 hpp
  have hfuel : (normalizedFactors (CPoly.toPoly p).primPart).toFinset.sup
      (fun q => (normalizedFactors (CPoly.toPoly p).primPart).count q) ≤ CPoly.degBound p := by
    have h1 := sup_count_le_natDegree_primPart (CPoly.toPoly p) hpp
    have h2 : (CPoly.toPoly p).primPart.natDegree ≤ (CPoly.toPoly p).natDegree :=
      natDegree_le_of_dvd (CPoly.toPoly p).primPart_dvd hp0
    have h3 : (CPoly.toPoly p).natDegree < CPoly.degBound p := by
      have h := CPoly.cdeg_lt_degBound_of_toPoly_ne_zero p hp0
      rw [CPoly.cdeg_eq_natDegree] at h
      exact h
    omega
  simpa only [Nat.sub_self, Nat.sub_zero] using
    (defaultGo_length_ge_maxMult p hpp (CPoly.degBound p) 1 b d (le_refl 1) hinv hfuel)

/-- The generic Yun factors are associated to the consecutive abstract squarefree parts. -/
private theorem default_forall₂_squarefreeParts [CPolyEngine P] [LawfulCPolyEngine.{u,v} P]
    [CPolyEuclidean P] [LawfulCPolyEuclidean.{u,v} P] [CPolyGcd P α]
    [LawfulCPolyGcd.{u,v} P α] [CharZero (CFieldSpec.K α)] (p : P α)
    (hp0 : CPoly.toPoly p ≠ 0) (hpp : (CPoly.toPoly p).primPart ≠ 0) :
    List.Forall₂ Associated ((CPolySquarefree.default p).map CPoly.toPoly)
      ((List.range (CPolySquarefree.default p).length).map
        (fun j => sqfreeFactPart (CPoly.toPoly p) (1 + j))) := by
  rw [CPolySquarefree.default]
  set g := CPolyGcd.compute p (CPolyEngine.deriv p)
  set b := CPolyEuclidean.div p g
  set d := CPolyEngine.sub (CPolyEuclidean.div (CPolyEngine.deriv p) g)
    (CPolyEngine.deriv b)
  set L := (CPolySquarefree.defaultGo (CPoly.degBound p) b d).length with hL
  have hinv : YunInv (CPoly.toPoly p) 1 (CPoly.toPoly b) (CPoly.toPoly d) := by
    simpa only [g, b, d] using defaultInit_yunInv p hp0 hpp
  have hmap := defaultGo_map_toPoly_eq_yunLoopAbs (P := P) (α := α)
    (CPoly.degBound p) b d
  rw [← hL] at hmap
  rw [hmap, yunLoopAbs_irrelevant (0 : (CRingSpec.R α)[X]) (CPoly.toPoly p) L
    (CPoly.toPoly b, CPoly.toPoly d) 1 1]
  letI : CharZero (CRingSpec.R α) := by
    change CharZero (CFieldSpec.K α)
    infer_instance
  exact yunLoopAbs_forall₂ (CPoly.toPoly p) hpp L 1 (CPoly.toPoly b) (CPoly.toPoly d)
    (le_refl 1) hinv

open UniqueFactorizationMonoid in
/-- The generic Yun factors reconstruct their input polynomial up to associates. -/
private theorem default_reconstruct [CPolyEngine P] [LawfulCPolyEngine.{u,v} P]
    [CPolyEuclidean P] [LawfulCPolyEuclidean.{u,v} P] [CPolyGcd P α]
    [LawfulCPolyGcd.{u,v} P α] [CharZero (CFieldSpec.K α)] (p : P α)
    (hp0 : CPoly.toPoly p ≠ 0) (hpp : (CPoly.toPoly p).primPart ≠ 0) :
    Associated (CPoly.toPoly p) (prodPow 1 ((CPolySquarefree.default p).map CPoly.toPoly)) := by
  have h1 : Associated (prodPow 1 ((CPolySquarefree.default p).map CPoly.toPoly))
      (prodPow 1 ((List.range (CPolySquarefree.default p).length).map
        (fun j => sqfreeFactPart (CPoly.toPoly p) (1 + j)))) :=
    prodPow_associated (default_forall₂_squarefreeParts p hp0 hpp) 1
  have h2 : Associated (prodPow 1 ((List.range (CPolySquarefree.default p).length).map
      (fun j => sqfreeFactPart (CPoly.toPoly p) (1 + j)))) (CPoly.toPoly p).primPart := by
    letI : CharZero (CRingSpec.R α) := by
      change CharZero (CFieldSpec.K α)
      infer_instance
    exact prodPow_one_sqfreeFactPart_range_associated (CPoly.toPoly p) hpp _
      (default_length_ge_maxMult p hp0 hpp)
  exact ((h1.trans h2).trans (associated_primPart_self (CPoly.toPoly p) hp0)).symm

/-- **Interface law: `decomp` is a squarefree decomposition of `d`.** Through `toPoly`, the factors are
monic, squarefree, and pairwise coprime, and the powered product `prodPow 1 (map toPoly decomp) = ∏ᵢ vᵢ^i`
is associated to `d`. Abstract: the assembler and the Hermite stage consume *this*, never a concrete loop. -/
structure LawfulSquarefreeDecomposition (d : P α) (decomp : List (P α)) : Prop where
  /-- The powered product `∏ᵢ vᵢ^i` reconstructs `d` up to associates. -/
  reconstruct : Associated (CPoly.toPoly d) (prodPow 1 (decomp.map CPoly.toPoly))
  /-- Each factor is monic. -/
  monic : ∀ p ∈ decomp, (CPoly.toPoly p).Monic
  /-- Each factor is squarefree. -/
  squarefree : ∀ p ∈ decomp, Squarefree (CPoly.toPoly p)
  /-- Distinct factors are relatively prime. -/
  coprime : decomp.Pairwise (fun p q => IsRelPrime (CPoly.toPoly p) (CPoly.toPoly q))

/-- Denotation law for a representation-selected squarefree decomposition. The selected output is
lawful whenever its input denotes a nonzero polynomial with nonzero primitive part. -/
class LawfulCPolySquarefree (P : Type u → Type u) [CPoly P] [CPolyEngine P] [CPolyEuclidean P]
    (α : Type u) [CField α] [CPolyGcd P α] [CFieldSpec.{u,v} α] [CharZero (CFieldSpec.K α)]
    [CPolySquarefree P α] : Prop where
  /-- The selected squarefree decomposition satisfies the semantic factorization contract. -/
  compute_lawful : ∀ (d : P α), CPoly.toPoly d ≠ 0 → (CPoly.toPoly d).primPart ≠ 0 →
      LawfulSquarefreeDecomposition d (CPoly.squarefreeYun d)

namespace LawfulCPolySquarefree

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P] [CPolyEuclidean P]
variable {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CharZero (CFieldSpec.K α)]
  [CPolyGcd P α] [CPolySquarefree P α] [LawfulCPolySquarefree.{u,v} P α]

/-- The selected squarefree decomposition satisfies its semantic contract. -/
theorem compute_lawful' (d : P α) (hd0 : CPoly.toPoly d ≠ 0)
    (hpp : (CPoly.toPoly d).primPart ≠ 0) :
    LawfulSquarefreeDecomposition d (CPoly.squarefreeYun d) :=
  LawfulCPolySquarefree.compute_lawful d hd0 hpp

end LawfulCPolySquarefree

namespace LawfulSquarefreeDecomposition

/-- The radical `∏ᵢ vᵢ` (the plain product of the factors) is squarefree — the property the Hermite stage
consumes abstractly (not from the concrete Yun loop). -/
theorem prod_squarefree {d : P α} {decomp : List (P α)}
    (h : LawfulSquarefreeDecomposition d decomp) :
    Squarefree ((decomp.map CPoly.toPoly).prod) := by
  refine squarefree_list_prod _ ?_ ?_
  · rw [List.pairwise_map]; exact h.coprime
  · intro p hp; rw [List.mem_map] at hp; obtain ⟨q, hq, rfl⟩ := hp; exact h.squarefree q hq

/-- The radical `∏ᵢ vᵢ` is monic. -/
theorem prod_monic {d : P α} {decomp : List (P α)}
    (h : LawfulSquarefreeDecomposition d decomp) :
    ((decomp.map CPoly.toPoly).prod).Monic := by
  refine monic_list_prod _ ?_
  intro p hp; rw [List.mem_map] at hp; obtain ⟨q, hq, rfl⟩ := hp; exact h.monic q hq

end LawfulSquarefreeDecomposition

end DeepWiki.SymbolicIntegration
