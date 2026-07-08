import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic

/-! # Pseudo-division of polynomials over an integral domain
Over a domain, scaling `A` by a power of `lc(B)` makes division by `B ≠ 0` exact: pseudo-division
gives `lc(B)ⁿ · A = B·Q + R` with `deg R < deg B`. Also the similarity relation and polynomial
remainder sequences, with the gcd-invariance of the PRS. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {R : Type*} [CommRing R] [IsDomain R]

/-- Pseudo-division existence: for `B ≠ 0` there are `n`, `Q`, `Rem` with
`lc(B)ⁿ · A = B·Q + Rem` and `deg Rem < deg B`. -/
theorem pseudoDivision_exists (A B : R[X]) (hB : B ≠ 0) :
    ∃ (n : ℕ) (Q Rem : R[X]),
      C B.leadingCoeff ^ n * A = B * Q + Rem ∧ Rem.degree < B.degree := by
  -- strong induction on `A.natDegree`
  suffices H : ∀ m : ℕ, ∀ A : R[X], A.natDegree = m →
      ∃ (n : ℕ) (Q Rem : R[X]), C B.leadingCoeff ^ n * A = B * Q + Rem ∧ Rem.degree < B.degree by
    exact H A.natDegree A rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro A hA
    by_cases hdeg : A.degree < B.degree
    · -- remainder is `A` itself, `n = 0`
      exact ⟨0, 0, A, by simp, hdeg⟩
    · -- one elimination step: cancel the leading term
      rw [not_lt] at hdeg  -- `B.degree ≤ A.degree`
      have hBbot : B.degree ≠ ⊥ := mt degree_eq_bot.mp hB
      have hAne : A ≠ 0 := by
        rintro rfl
        rw [degree_zero] at hdeg
        exact hBbot (le_bot_iff.mp hdeg)
      have hbne : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hB
      have hane : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
      set b := B.leadingCoeff with hb
      set a := A.leadingCoeff with ha
      set δ := A.natDegree - B.natDegree with hδ
      have hBA : B.natDegree ≤ A.natDegree := natDegree_le_natDegree hdeg
      set p := C b * A with hp
      set q := C a * (B * X ^ δ) with hq
      set A₁ := p - q with hA₁
      -- the two leading terms agree
      have hp_deg : p.degree = A.degree := by
        rw [hp, degree_mul, degree_C hbne, zero_add]
      have hq_deg : q.degree = A.degree := by
        rw [hq, degree_mul, degree_C hane, zero_add, degree_mul, degree_X_pow,
          degree_eq_natDegree hB, degree_eq_natDegree hAne]
        rw [← Nat.cast_add, Nat.add_sub_cancel' hBA]
      have hp_lc : p.leadingCoeff = b * a := by rw [hp, leadingCoeff_mul, leadingCoeff_C]
      have hq_lc : q.leadingCoeff = b * a := by
        rw [hq, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_mul, leadingCoeff_X_pow, mul_one,
          mul_comm]
      have hp_ne : p ≠ 0 := mul_ne_zero (by simpa using hbne) hAne
      have hsub_deg : A₁.degree < A.degree := by
        rw [hA₁, ← hp_deg]
        exact degree_sub_lt (hp_deg.trans hq_deg.symm) hp_ne (by rw [hp_lc, hq_lc])
      -- key rewrite: `C b * A = A₁ + q`
      have hkey : C b * A = A₁ + q := by rw [hA₁]; ring
      by_cases hA₁0 : A₁ = 0
      · -- exact after one scaling: `b¹ · A = B·(a·X^δ) + 0`
        refine ⟨1, C a * X ^ δ, 0, ?_, ?_⟩
        · rw [pow_one, hkey, hA₁0, zero_add, hq]; ring
        · rw [degree_zero]; exact bot_lt_iff_ne_bot.mpr hBbot
      · -- recurse on `A₁`, whose degree dropped
        have hlt : A₁.natDegree < A.natDegree :=
          natDegree_lt_natDegree hA₁0 hsub_deg
        obtain ⟨n₁, Q₁, R₁, hEq, hdeg₁⟩ := IH A₁.natDegree (hA ▸ hlt) A₁ rfl
        refine ⟨n₁ + 1, Q₁ + C b ^ n₁ * C a * X ^ δ, R₁, ?_, hdeg₁⟩
        calc C b ^ (n₁ + 1) * A
            = C b ^ n₁ * (C b * A) := by ring
          _ = C b ^ n₁ * (A₁ + q) := by rw [hkey]
          _ = C b ^ n₁ * A₁ + C b ^ n₁ * q := by ring
          _ = (B * Q₁ + R₁) + C b ^ n₁ * q := by rw [hEq]
          _ = B * (Q₁ + C b ^ n₁ * C a * X ^ δ) + R₁ := by rw [hq]; ring

/-- `A` is *similar* to `B` when `C a * A = C b * B` for some nonzero scalars `a, b`. -/
def IsSimilar (A B : R[X]) : Prop := ∃ a b : R, a ≠ 0 ∧ b ≠ 0 ∧ C a * A = C b * B

/-- `IsSimilar` is reflexive (witnesses `a = b = 1`). -/
@[refl] theorem IsSimilar.refl (A : R[X]) : IsSimilar A A :=
  ⟨1, 1, one_ne_zero, one_ne_zero, rfl⟩

omit [IsDomain R] in
/-- `IsSimilar` is symmetric (swap the witnesses). -/
theorem IsSimilar.symm {A B : R[X]} (h : IsSimilar A B) : IsSimilar B A :=
  let ⟨a, b, ha, hb, hab⟩ := h; ⟨b, a, hb, ha, hab.symm⟩

/-- `IsSimilar` is transitive (over a domain the product witnesses stay nonzero). -/
theorem IsSimilar.trans {A B C₀ : R[X]} (h₁ : IsSimilar A B) (h₂ : IsSimilar B C₀) :
    IsSimilar A C₀ := by
  obtain ⟨a, b, ha, hb, hab⟩ := h₁
  obtain ⟨c, d, hc, hd, hcd⟩ := h₂
  refine ⟨c * a, b * d, mul_ne_zero hc ha, mul_ne_zero hb hd, ?_⟩
  calc C (c * a) * A = C c * (C a * A) := by rw [C_mul]; ring
    _ = C c * (C b * B) := by rw [hab]
    _ = C b * (C c * B) := by ring
    _ = C b * (C d * C₀) := by rw [hcd]
    _ = C (b * d) * C₀ := by rw [C_mul]; ring

/-- Similarity is an equivalence relation. -/
theorem isSimilar_equivalence : Equivalence (IsSimilar (R := R)) :=
  ⟨IsSimilar.refl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- If `B = C η · A` with `η` a unit (`η · η' = 1`), then `IsSimilar A B`. -/
theorem isSimilar_of_unit_mul {S : Type*} [CommRing S] [Nontrivial S] {A B : S[X]} {η η' : S}
    (hη : η * η' = 1) (hAB : B = Polynomial.C η * A) :
    IsSimilar A B := by
  have hηne : η ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hη
    exact one_ne_zero hη.symm
  exact ⟨η, 1, hηne, one_ne_zero, by rw [hAB, map_one, one_mul]⟩

/-- Similar polynomials have equal `natDegree`. -/
theorem IsSimilar.natDegree_eq {A B : R[X]} (h : IsSimilar A B) : A.natDegree = B.natDegree := by
  obtain ⟨a, b, ha, hb, hab⟩ := h
  rw [← natDegree_C_mul ha, hab, natDegree_C_mul hb]

example {A B : R[X]} (h : IsSimilar A B) : A.natDegree = B.natDegree := h.natDegree_eq

/-- `Rem` is a *pseudo-remainder* of `A` by `B`: `lc(B)ᵏ · A = B·Q + Rem` with `deg Rem < deg B`
for some `k`, `Q`. -/
def IsPseudoRemainder (A B Rem : R[X]) : Prop :=
  ∃ (k : ℕ) (Q : R[X]), C B.leadingCoeff ^ k * A = B * Q + Rem ∧ Rem.degree < B.degree

/-- A pseudo-remainder exists for any nonzero divisor (repackages `pseudoDivision_exists`). -/
theorem isPseudoRemainder_exists (A B : R[X]) (hB : B ≠ 0) :
    ∃ Rem, IsPseudoRemainder A B Rem := by
  obtain ⟨n, Q, Rem, hEq, hdeg⟩ := pseudoDivision_exists A B hB
  exact ⟨Rem, n, Q, hEq, hdeg⟩

/-- Polynomial remainder sequence: `Rs 0 = A`, `Rs 1 = B`, each nonzero `Rs (i+1)` makes
`C (β (i+1)) · Rs (i+2)` a pseudo-remainder of `Rs i` by `Rs (i+1)` (`β (i+1) ≠ 0`), and a zero
term forces the next to vanish. -/
def IsPRS (A B : R[X]) (Rs : ℕ → R[X]) (β : ℕ → R) : Prop :=
  Rs 0 = A ∧ Rs 1 = B ∧
    ∀ i, (Rs (i + 1) ≠ 0 →
            β (i + 1) ≠ 0 ∧ IsPseudoRemainder (Rs i) (Rs (i + 1)) (C (β (i + 1)) * Rs (i + 2)))
      ∧ (Rs (i + 1) = 0 → C (β (i + 1)) * Rs (i + 2) = 0)

/-- Associated polynomials are similar. -/
theorem IsSimilar.of_associated {x y : R[X]} (h : Associated x y) : IsSimilar x y := by
  obtain ⟨u, rfl⟩ := h
  obtain ⟨r, hr, hru⟩ := Polynomial.isUnit_iff.mp u.isUnit
  exact ⟨r, 1, hr.ne_zero, one_ne_zero, by rw [← hru, map_one]; ring⟩

/-- `IsSimilar p q` over a domain lifts to `p = C η · q` in `Frac(D)[x]` for some nonzero `η ∈ Frac(D)`. -/
theorem IsSimilar.exists_fractionRing {D : Type*} [CommRing D] [IsDomain D] {p q : D[X]}
    (h : IsSimilar p q) :
    ∃ η : FractionRing D, η ≠ 0 ∧
      p.map (algebraMap D (FractionRing D)) = C η * q.map (algebraMap D (FractionRing D)) := by
  obtain ⟨a, b, ha, hb, hab⟩ := h
  have hinj := IsFractionRing.injective D (FractionRing D)
  have hφa : algebraMap D (FractionRing D) a ≠ 0 := (map_ne_zero_iff _ hinj).mpr ha
  have hφb : algebraMap D (FractionRing D) b ≠ 0 := (map_ne_zero_iff _ hinj).mpr hb
  refine ⟨algebraMap D (FractionRing D) b / algebraMap D (FractionRing D) a,
    div_ne_zero hφb hφa, ?_⟩
  have key : C (algebraMap D (FractionRing D) a) * p.map (algebraMap D (FractionRing D))
      = C (algebraMap D (FractionRing D) b) * q.map (algebraMap D (FractionRing D)) := by
    rw [← Polynomial.map_C, ← Polynomial.map_C, ← Polynomial.map_mul, ← Polynomial.map_mul, hab]
  calc p.map (algebraMap D (FractionRing D))
      = C ((algebraMap D (FractionRing D) a)⁻¹) * (C (algebraMap D (FractionRing D) a)
          * p.map (algebraMap D (FractionRing D))) := by
        rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hφa, map_one, one_mul]
    _ = C ((algebraMap D (FractionRing D) a)⁻¹) * (C (algebraMap D (FractionRing D) b)
          * q.map (algebraMap D (FractionRing D))) := by rw [key]
    _ = C (algebraMap D (FractionRing D) b / algebraMap D (FractionRing D) a)
          * q.map (algebraMap D (FractionRing D)) := by rw [div_eq_mul_inv, map_mul]; ring

/-- A `ℚ[t]`-similarity `IsSimilar A B` whose witnesses stay `φ`-nonzero gives
`IsSimilar (Φ A) (Φ B)` (`Φ = mapRingHom φ`). -/
theorem isSimilar_mapRingHom {S : Type*} [CommRing S] (φ : ℚ[X] →+* S) {A B : (ℚ[X])[X]}
    (h : IsSimilar A B) (hne : ∀ a b : ℚ[X], a ≠ 0 → b ≠ 0 → Polynomial.C a * A = Polynomial.C b * B
      → φ a ≠ 0 ∧ φ b ≠ 0) :
    IsSimilar ((Polynomial.mapRingHom φ) A) ((Polynomial.mapRingHom φ) B) := by
  obtain ⟨a, b, ha, hb, hab⟩ := h
  obtain ⟨hφa, hφb⟩ := hne a b ha hb hab
  refine ⟨φ a, φ b, hφa, hφb, ?_⟩
  have hcong := congrArg (Polynomial.map φ) hab
  rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C] at hcong
  simpa only [Polynomial.coe_mapRingHom] using hcong

/-- If `ker φ = (f)` for irreducible `f`, a similarity with nonzero mapped endpoints maps to a
similarity. -/
theorem isSimilar_mapRingHom_of_irreducible {S : Type*} [CommRing S] [IsDomain S]
    (f : ℚ[X]) (hf : Irreducible f) (φ : ℚ[X] →+* S) (hker : ∀ x, φ x = 0 ↔ f ∣ x)
    {A B : (ℚ[X])[X]} (h : IsSimilar A B)
    (hA : (Polynomial.mapRingHom φ) A ≠ 0) (hB : (Polynomial.mapRingHom φ) B ≠ 0) :
    IsSimilar ((Polynomial.mapRingHom φ) A) ((Polynomial.mapRingHom φ) B) := by
  classical
  obtain ⟨a, b, ha, hb, hab⟩ := h
  set g := GCDMonoid.gcd a b with hg
  have hgne : g ≠ 0 := gcd_ne_zero_of_left ha
  set a' := a / g with ha'def
  set b' := b / g with hb'def
  have hcop : IsCoprime a' b' := isCoprime_div_gcd_div_gcd hb
  have hga : g * a' = a := EuclideanDomain.mul_div_cancel' hgne (gcd_dvd_left a b)
  have hgb : g * b' = b := EuclideanDomain.mul_div_cancel' hgne (gcd_dvd_right a b)
  have ha'ne : a' ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hga; exact ha hga.symm
  have hb'ne : b' ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hgb; exact hb hgb.symm
  have hab' : Polynomial.C a' * A = Polynomial.C b' * B := by
    have hcancel : Polynomial.C g * (Polynomial.C a' * A) = Polynomial.C g * (Polynomial.C b' * B) := by
      rw [← mul_assoc, ← mul_assoc, ← Polynomial.C_mul, ← Polynomial.C_mul, hga, hgb, hab]
    have hCg : (Polynomial.C g : (ℚ[X])[X]) ≠ 0 := by
      simpa [Polynomial.C_eq_zero] using hgne
    exact mul_left_cancel₀ hCg hcancel
  have hφa' : φ a' ≠ 0 := by
    intro h0
    have hfa' : f ∣ a' := (hker a').1 h0
    have himg := congrArg (Polynomial.map φ) hab'
    rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C] at himg
    simp only [Polynomial.coe_mapRingHom] at hA hB
    rw [h0, map_zero, zero_mul] at himg
    have hφb' : φ b' = 0 := by
      by_contra hb0
      exact hB (by
        have : (Polynomial.C (φ b') : S[X]) ≠ 0 := by simpa [Polynomial.C_eq_zero] using hb0
        exact (mul_eq_zero.mp himg.symm).resolve_left this)
    have hfb' : f ∣ b' := (hker b').1 hφb'
    exact hf.not_isUnit (hcop.isUnit_of_dvd' hfa' hfb')
  have hφb' : φ b' ≠ 0 := by
    intro h0
    have hfb' : f ∣ b' := (hker b').1 h0
    have himg := congrArg (Polynomial.map φ) hab'
    rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C] at himg
    simp only [Polynomial.coe_mapRingHom] at hA hB
    rw [h0, map_zero, zero_mul] at himg
    have hφa' : φ a' = 0 := by
      by_contra ha0
      exact hA (by
        have : (Polynomial.C (φ a') : S[X]) ≠ 0 := by simpa [Polynomial.C_eq_zero] using ha0
        exact (mul_eq_zero.mp himg).resolve_left this)
    have hfa' : f ∣ a' := (hker a').1 hφa'
    exact hf.not_isUnit (hcop.isUnit_of_dvd' hfa' hfb')
  refine ⟨φ a', φ b', hφa', hφb', ?_⟩
  have hcong := congrArg (Polynomial.map φ) hab'
  rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C] at hcong
  simpa only [Polynomial.coe_mapRingHom] using hcong

/-- PRS gcd-invariance step: consecutive gcds are similar,
`gcd(Rᵢ, Rᵢ₊₁) ~ gcd(Rᵢ₊₁, Rᵢ₊₂)`. -/
theorem isSimilar_gcd_step [GCDMonoid R[X]] {A B : R[X]} {Rs : ℕ → R[X]} {β : ℕ → R}
    (hprs : IsPRS A B Rs β) {i : ℕ} (hi : Rs (i + 1) ≠ 0) :
    IsSimilar (gcd (Rs i) (Rs (i + 1))) (gcd (Rs (i + 1)) (Rs (i + 2))) := by
  obtain ⟨_, _, hrec⟩ := hprs
  obtain ⟨hβ, k, Q, hEq, _⟩ := (hrec i).1 hi
  set G := gcd (Rs i) (Rs (i + 1)) with hGdef
  set H := gcd (Rs (i + 1)) (Rs (i + 2)) with hHdef
  set cα := (Rs (i + 1)).leadingCoeff ^ k with hcαdef
  have hlc : (Rs (i + 1)).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hi
  have hcα0 : cα ≠ 0 := pow_ne_zero _ hlc
  have hEq' : C cα * Rs i = Rs (i + 1) * Q + C (β (i + 1)) * Rs (i + 2) := by
    rw [hcαdef, C_pow]; exact hEq
  have hHG : H ∣ C cα * G := by
    have h1 : H ∣ C cα * Rs i := by
      rw [hEq']
      exact dvd_add ((gcd_dvd_left _ _).mul_right Q) ((gcd_dvd_right _ _).mul_left _)
    have h2 : H ∣ C cα * Rs (i + 1) := (gcd_dvd_left _ _).mul_left _
    exact (dvd_gcd h1 h2).trans (gcd_mul_left' (C cα) (Rs i) (Rs (i + 1))).dvd
  have hGH : G ∣ C (β (i + 1)) * H := by
    have h1 : G ∣ C (β (i + 1)) * Rs (i + 2) := by
      have hsub : C (β (i + 1)) * Rs (i + 2) = C cα * Rs i - Rs (i + 1) * Q := by rw [hEq']; ring
      rw [hsub]
      exact dvd_sub ((gcd_dvd_left _ _).mul_left _) ((gcd_dvd_right _ _).mul_right Q)
    have h2 : G ∣ C (β (i + 1)) * Rs (i + 1) := (gcd_dvd_right _ _).mul_left _
    exact (dvd_gcd h2 h1).trans (gcd_mul_left' (C (β (i + 1))) (Rs (i + 1)) (Rs (i + 2))).dvd
  obtain ⟨Q₁, hQ₁⟩ := hHG
  obtain ⟨Q₂, hQ₂⟩ := hGH
  have hG0 : G ≠ 0 := fun h => hi ((gcd_eq_zero_iff _ _).mp h).2
  have key : G * C (cα * β (i + 1)) = G * (Q₁ * Q₂) := by
    have e1 : C (β (i + 1)) * (C cα * G) = G * (Q₁ * Q₂) := by
      rw [hQ₁, show C (β (i + 1)) * (H * Q₁) = C (β (i + 1)) * H * Q₁ by ring, hQ₂]; ring
    rw [← e1, C_mul]; ring
  have hQ₁Q₂ : C (cα * β (i + 1)) = Q₁ * Q₂ := mul_left_cancel₀ hG0 key
  have hconst : C (cα * β (i + 1)) ≠ 0 := by rw [Ne, C_eq_zero]; exact mul_ne_zero hcα0 hβ
  have hQ₁0 : Q₁ ≠ 0 := by rintro rfl; rw [zero_mul] at hQ₁Q₂; exact hconst hQ₁Q₂
  have hQ₂0 : Q₂ ≠ 0 := by rintro rfl; rw [mul_zero] at hQ₁Q₂; exact hconst hQ₁Q₂
  have hdeg : (Q₁ * Q₂).natDegree = 0 := by rw [← hQ₁Q₂]; exact natDegree_C _
  have hQ₁deg : Q₁.natDegree = 0 := by rw [natDegree_mul hQ₁0 hQ₂0] at hdeg; omega
  have hQ₁C : Q₁ = C (Q₁.coeff 0) := eq_C_of_natDegree_eq_zero hQ₁deg
  refine ⟨cα, Q₁.coeff 0, hcα0, ?_, ?_⟩
  · intro h; exact hQ₁0 (by rw [hQ₁C, h, map_zero])
  · rw [hQ₁]; nth_rewrite 1 [hQ₁C]; ring

/-- The last nonzero element `Rₖ` of a PRS of `A, B` is similar to `gcd(A, B)`. -/
theorem IsPRS.isSimilar_gcd [GCDMonoid R[X]] {A B : R[X]} {Rs : ℕ → R[X]} {β : ℕ → R}
    (hprs : IsPRS A B Rs β) {k : ℕ} (hk1 : Rs (k + 1) = 0)
    (hpos : ∀ j, 1 ≤ j → j ≤ k → Rs j ≠ 0) :
    IsSimilar (Rs k) (gcd A B) := by
  have hAB : gcd A B = gcd (Rs 0) (Rs 1) := by rw [hprs.1, hprs.2.1]
  have chain : ∀ i, i ≤ k → IsSimilar (gcd (Rs 0) (Rs 1)) (gcd (Rs i) (Rs (i + 1))) := by
    intro i
    induction i with
    | zero => intro _; exact IsSimilar.refl _
    | succ n ih =>
      intro hn
      exact (ih (Nat.le_of_succ_le hn)).trans
        (isSimilar_gcd_step hprs (hpos (n + 1) (Nat.le_add_left 1 n) hn))
  have hchaink := chain k le_rfl
  have hend : IsSimilar (gcd (Rs k) (Rs (k + 1))) (Rs k) := by
    rw [hk1]
    exact IsSimilar.of_associated
      (associated_of_dvd_dvd (gcd_dvd_left _ _) (dvd_gcd dvd_rfl (dvd_zero _)))
  rw [hAB]
  exact hend.symm.trans hchaink.symm

end DeepWiki.SymbolicIntegration
