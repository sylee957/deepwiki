import DeepWiki.SymbolicIntegration.SpecialFirstKind

/-! # Constants of monomial extensions and base change

Relates constants of fraction-field monomial derivations to special polynomials, nonlinear degree
comparisons, scalar monomial constants, and differential base change. -/

open scoped Differential
open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {k : Type*} [Field k] [Differential k]

section Coprime
variable {R : Type*} [CommRing R] [Differential R]

/-- If `a` and `b` are coprime and `b * a′ = a * b′`, then both are special. -/
theorem isSpecial_of_coprime_of_deriv_quotient_num_eq_zero {a b : R} (hco : IsCoprime a b)
    (h : b * a′ = a * b′) : IsSpecial a ∧ IsSpecial b := by
  refine ⟨hco.dvd_of_dvd_mul_left ?_, hco.symm.dvd_of_dvd_mul_left ?_⟩
  · exact ⟨b′, h⟩
  · exact ⟨a′, h.symm⟩

end Coprime

section FractionConstants
-- A constant `c = a/b ∈ k(t)` of a differential extension `K` of the differential ring `R = k[t]`.
-- Instantiated in the monomial case with `R = k[X]`, `Differential R = ⟨implicitDeriv v⟩`,
-- `K = k(t)` the fraction field. The conclusion `IsSpecial a` is exactly `a ∣ Da` in `k[t]`.
variable {R K : Type*} [CommRing R] [Differential R] [IsDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [Differential K] [DifferentialAlgebra R K]

omit [IsDomain R] in
/-- A constant quotient with coprime numerator and nonzero denominator has special numerator and denominator. -/
theorem isSpecial_num_denom_of_const_quotient {a b : R} (hco : IsCoprime a b) (hb : b ≠ 0)
    (hconst : (algebraMap R K a / algebraMap R K b)′ = 0) :
    IsSpecial a ∧ IsSpecial b := by
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hbK : algebraMap R K b ≠ 0 := fun h => hb (hinj (by rw [h, map_zero]))
  -- the quotient rule turns `Dc = 0` into `b·Da = a·Db` over `K`
  have hnum : algebraMap R K (b * a′) = algebraMap R K (a * b′) := by
    rw [deriv_div, div_eq_zero_iff] at hconst
    rcases hconst with hz | hz
    · rw [sub_eq_zero] at hz
      rw [map_mul, map_mul, ← deriv_algebraMap, ← deriv_algebraMap]
      exact hz
    · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp hz) hbK
  exact isSpecial_of_coprime_of_deriv_quotient_num_eq_zero hco (hinj hnum)

end FractionConstants

section Nonlinear
-- A *nonlinear* monomial: `δ(t) = deg(Dt) = deg v ≥ 2`. Here the leading term of `Dp` comes from
-- `v·dp/dt`, so `lc(Dp) = (deg p)·lc(p)·lc(v)` for `deg p ≥ 1`.
variable {F : Type*} [Field F] [CharZero F] [Differential F]

/-- In a nonlinear monomial derivation, the leading coefficient of `implicitDeriv v p` is determined by `p` and `v`. -/
theorem leadingCoeff_implicitDeriv_nonlinear (v p : F[X]) (hv : 2 ≤ v.natDegree)
    (hp : 1 ≤ p.natDegree) :
    (Differential.implicitDeriv v p).leadingCoeff
      = (p.natDegree : F) * p.leadingCoeff * v.leadingCoeff := by
  have happly : Differential.implicitDeriv v p
      = Differential.mapCoeffs p + v * derivative p := by
    simp [Differential.implicitDeriv, derivative']
  have hv0 : v ≠ 0 := by rintro rfl; simp at hv
  have hdp : derivative p ≠ 0 := derivative_ne_zero.mpr (by omega)
  have hmul : (v * derivative p).natDegree = p.natDegree + (v.natDegree - 1) := by
    rw [natDegree_mul hv0 hdp, natDegree_derivative]; omega
  have h1 : (Differential.mapCoeffs p).natDegree ≤ p.natDegree := by
    refine natDegree_le_iff_coeff_eq_zero.mpr (fun N hN => ?_)
    rw [Differential.coeff_mapCoeffs, coeff_eq_zero_of_natDegree_lt hN]; simp
  have hlt : (Differential.mapCoeffs p).natDegree < (v * derivative p).natDegree := by
    rw [hmul]; omega
  have hdeg : (Differential.implicitDeriv v p).natDegree = (v * derivative p).natDegree := by
    rw [happly, natDegree_add_eq_right_of_natDegree_lt hlt]
  rw [leadingCoeff, hdeg, happly, coeff_add, coeff_eq_zero_of_natDegree_lt (hlt.trans_le le_rfl),
    zero_add, ← leadingCoeff, leadingCoeff_mul, leadingCoeff_derivative]
  ring

/-- A special cofactor for a nonlinear monomial derivation has leading coefficient and degree controlled by `p.natDegree`. -/
theorem leadingCoeff_cofactor_nonlinear {v p g : F[X]} (hv : 2 ≤ v.natDegree) (hp0 : p ≠ 0)
    (hg : Differential.implicitDeriv v p = p * g) :
    (1 ≤ p.natDegree → g.leadingCoeff = (p.natDegree : F) * v.leadingCoeff
        ∧ g.natDegree = v.natDegree - 1)
      ∧ (p.natDegree = 0 → g.natDegree = 0) := by
  have hlcp : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp0
  have hlcv : v.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr (by rintro rfl; simp at hv)
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · -- nonlinear, `deg p ≥ 1`: compare leading coefficients and degrees of `Dp = p·g`
    have hlc : (Differential.implicitDeriv v p).leadingCoeff
        = (p.natDegree : F) * p.leadingCoeff * v.leadingCoeff :=
      leadingCoeff_implicitDeriv_nonlinear v p hv hp
    have hdeg : (Differential.implicitDeriv v p).natDegree = p.natDegree + (v.natDegree - 1) :=
      natDegree_implicitDeriv_eq v p hv hp
    have hgne : g ≠ 0 := by
      rintro rfl; rw [mul_zero] at hg; rw [hg] at hdeg; simp at hdeg; omega
    have hlcg : p.leadingCoeff * g.leadingCoeff = (p.natDegree : F) * p.leadingCoeff * v.leadingCoeff := by
      rw [← leadingCoeff_mul, ← hg, hlc]
    have hdegg : g.natDegree = v.natDegree - 1 := by
      rw [hg, natDegree_mul hp0 hgne] at hdeg; omega
    refine ⟨?_, hdegg⟩
    have := mul_left_cancel₀ hlcp (by rw [hlcg]; ring :
      p.leadingCoeff * g.leadingCoeff = p.leadingCoeff * ((p.natDegree : F) * v.leadingCoeff))
    exact this
  · -- `deg p = 0`: `p = C c`, so `Dp = C(c′)` has degree `0`, and `Dp = p·g` forces `deg g = 0`
    rcases eq_or_ne g 0 with hg0 | hgne
    · rw [hg0]; simp
    · obtain ⟨c, rfl⟩ : ∃ c, p = C c := ⟨p.coeff 0, eq_C_of_natDegree_eq_zero hp⟩
      have hDp0 : (Differential.implicitDeriv v (C c)).natDegree = 0 := by
        rw [Differential.implicitDeriv_C]; exact natDegree_C _
      rw [hg, natDegree_mul hp0 hgne, natDegree_C] at hDp0
      omega

/-- Nonzero special polynomials with zero quotient-derivative numerator have equal `natDegree` in a nonlinear monomial derivation. -/
theorem natDegree_eq_of_special_of_deriv_quotient_num_eq_zero {v a b : F[X]} (hv : 2 ≤ v.natDegree)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hsa : a ∣ Differential.implicitDeriv v a) (hsb : b ∣ Differential.implicitDeriv v b)
    (h : b * Differential.implicitDeriv v a = a * Differential.implicitDeriv v b) :
    a.natDegree = b.natDegree := by
  obtain ⟨g, hg⟩ := hsa
  obtain ⟨h', hh⟩ := hsb
  -- `g = h'` by cancelling `a·b` in `b·(a·g) = a·(b·h')`
  have hgh : g = h' := by
    have hcancel : a * b * g = a * b * h' := by
      rw [show a * b * g = b * (a * g) from by ring, show a * b * h' = a * (b * h') from by ring,
        ← hg, ← hh, h]
    exact mul_left_cancel₀ (mul_ne_zero ha0 hb0) hcancel
  subst hgh
  obtain ⟨hga, hg0a⟩ := leadingCoeff_cofactor_nonlinear hv ha0 hg
  obtain ⟨hgb, hg0b⟩ := leadingCoeff_cofactor_nonlinear hv hb0 hh
  have hlcv : v.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr (by rintro rfl; simp at hv)
  rcases Nat.eq_zero_or_pos a.natDegree with hae | hap
  · -- `deg a = 0`: then `deg g = 0`, so `deg b ≥ 1` is impossible (`leadingCoeff_cofactor` gives δ−1)
    rcases Nat.eq_zero_or_pos b.natDegree with hbe | hbp
    · rw [hae, hbe]
    · obtain ⟨_, hgdegb⟩ := hgb hbp
      rw [hg0a hae] at hgdegb
      omega
  · rcases Nat.eq_zero_or_pos b.natDegree with hbe | hbp
    · obtain ⟨_, hgdega⟩ := hga hap
      rw [hg0b hbe] at hgdega
      omega
    · -- both `≥ 1`: leading coeffs `(deg a)·lc v = lc g = (deg b)·lc v`
      obtain ⟨hlca, _⟩ := hga hap
      obtain ⟨hlcb, _⟩ := hgb hbp
      have : (a.natDegree : F) * v.leadingCoeff = (b.natDegree : F) * v.leadingCoeff := by
        rw [← hlca, ← hlcb]
      have hcast : (a.natDegree : F) = (b.natDegree : F) := mul_right_cancel₀ hlcv this
      exact_mod_cast hcast

/-- A constant quotient in a nonlinear monomial fraction field has special numerator and denominator of equal `natDegree`. -/
theorem isSpecial_and_natDegree_eq_of_const_quotient_nonlinear
    {K : Type*} [Field K] [Algebra F[X] K] [IsFractionRing F[X] K] [Differential K]
    {v a b : F[X]} (hv : 2 ≤ v.natDegree) (hco : IsCoprime a b) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hder : ∀ p : F[X], (algebraMap F[X] K p)′ = algebraMap F[X] K (Differential.implicitDeriv v p))
    (hconst : (algebraMap F[X] K a / algebraMap F[X] K b)′ = 0) :
    a ∣ Differential.implicitDeriv v a ∧ b ∣ Differential.implicitDeriv v b
      ∧ a.natDegree = b.natDegree := by
  letI : Differential F[X] := ⟨Differential.implicitDeriv v⟩
  letI : DifferentialAlgebra F[X] K := ⟨hder⟩
  obtain ⟨hsa, hsb⟩ := isSpecial_num_denom_of_const_quotient hco hb0 hconst
  -- the numerator identity `b·Da = a·Db` from `Dc = 0`, pulled back through `algebraMap`
  have hinj : Function.Injective (algebraMap F[X] K) := IsFractionRing.injective F[X] K
  have hbK : algebraMap F[X] K b ≠ 0 := fun hz => hb0 (hinj (by rw [hz, map_zero]))
  have hpoly : b * Differential.implicitDeriv v a = a * Differential.implicitDeriv v b := by
    apply hinj
    rw [deriv_div, div_eq_zero_iff] at hconst
    rcases hconst with hz | hz
    · rw [sub_eq_zero] at hz
      rw [map_mul, map_mul, ← hder, ← hder]; exact hz
    · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp hz) hbK
  exact ⟨hsa, hsb,
    natDegree_eq_of_special_of_deriv_quotient_num_eq_zero hv ha0 hb0 hsa hsb hpoly⟩

end Nonlinear

section ScalarMonomial
-- The monomial derivation with scalar `t`-component `C w`.
variable (w : k)

/-- A scalar monomial derivation does not increase polynomial `natDegree`. -/
theorem natDegree_implicitDeriv_C_le (p : k[X]) :
    (Differential.implicitDeriv (C w) p).natDegree ≤ p.natDegree := by
  refine (natDegree_implicitDeriv_le (C w) p).trans ?_
  rw [natDegree_C]; simp

/-- In a scalar monomial derivation, the top coefficient of `implicitDeriv (C w) p` is `(p.leadingCoeff)′`. -/
theorem coeff_natDegree_implicitDeriv_C (p : k[X]) :
    (Differential.implicitDeriv (C w) p).coeff p.natDegree = (p.coeff p.natDegree)′ := by
  have happly : Differential.implicitDeriv (C w) p
      = Differential.mapCoeffs p + C w * derivative p := by
    simp [Differential.implicitDeriv, derivative']
  rw [happly, coeff_add, Differential.coeff_mapCoeffs, coeff_C_mul]
  rcases Nat.eq_zero_or_pos p.natDegree with h0 | h0
  · rw [h0, eq_C_of_natDegree_eq_zero h0, derivative_C, coeff_zero, mul_zero, add_zero, coeff_C,
      if_pos rfl]
  · have hd : (derivative p).coeff p.natDegree = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (natDegree_derivative_le p) (by omega))
    rw [hd, mul_zero, add_zero]

end ScalarMonomial

/-- A monic polynomial under a scalar monomial derivation either differentiates to zero or drops `natDegree`. -/
theorem deriv_monic_eq_zero_or_natDegree_lt {w : k} {q : k[X]} (hq : q.Monic) :
    Differential.implicitDeriv (C w) q = 0
      ∨ (Differential.implicitDeriv (C w) q).natDegree < q.natDegree := by
  by_cases h0 : Differential.implicitDeriv (C w) q = 0
  · exact Or.inl h0
  · refine Or.inr (lt_of_le_of_ne (natDegree_implicitDeriv_C_le w q) ?_)
    intro heq
    have htop : (Differential.implicitDeriv (C w) q).coeff
        (Differential.implicitDeriv (C w) q).natDegree = 0 := by
      rw [heq, coeff_natDegree_implicitDeriv_C, hq.coeff_natDegree,
        (Differential.deriv : Derivation ℤ k k).map_one_eq_zero]
    exact (mt leadingCoeff_eq_zero.mp h0) htop

/-- A monic polynomial is special for a scalar monomial derivation iff its implicit derivative is zero. -/
theorem isSpecial_iff_deriv_eq_zero_of_monic {w : k} {q : k[X]} (hq : q.Monic) :
    q ∣ Differential.implicitDeriv (C w) q ↔ Differential.implicitDeriv (C w) q = 0 := by
  constructor
  · intro hdvd
    rcases deriv_monic_eq_zero_or_natDegree_lt hq with h | hlt
    · exact h
    · by_contra hne
      exact absurd (natDegree_le_of_dvd hdvd hne) (by omega)
  · intro h; rw [h]; exact dvd_zero q

omit [Differential k] in
/-- The monic normalization `p/lc(p)` of a nonzero `p` is an associate of `p` and monic. -/
theorem associated_mul_C_inv_leadingCoeff {p : k[X]} (hp : p ≠ 0) :
    Associated p (p * C p.leadingCoeff⁻¹) ∧ (p * C p.leadingCoeff⁻¹).Monic := by
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
  refine ⟨(associated_mul_unit_right p _ (isUnit_C.mpr (Ne.isUnit (inv_ne_zero hlc)))),
    monic_mul_C_of_leadingCoeff_mul_eq_one (mul_inv_cancel₀ hlc)⟩

/-- A nonzero polynomial is special for a scalar monomial derivation iff its monic normalization has zero implicit derivative. -/
theorem isSpecial_iff_deriv_normalize_eq_zero {w : k} {p : k[X]} (hp : p ≠ 0) :
    p ∣ Differential.implicitDeriv (C w) p
      ↔ Differential.implicitDeriv (C w) (p * C p.leadingCoeff⁻¹) = 0 := by
  letI : Differential k[X] := ⟨Differential.implicitDeriv (C w)⟩
  obtain ⟨hassoc, hmonic⟩ := associated_mul_C_inv_leadingCoeff hp
  rw [← isSpecial_iff_deriv_eq_zero_of_monic hmonic]
  exact ⟨fun h => IsSpecial.of_associated hassoc h, fun h => IsSpecial.of_associated hassoc.symm h⟩

section AlgebraicExtension
-- `E` a differential extension of `k`. The *special half* of base change
-- (`isSpecial_map_of_isSpecial`) lives in `SpecialFirstKind`; here is the *normal half*.
variable {E : Type*} [Field E] [Differential E] [Algebra k E] [DifferentialAlgebra k E]

/-- Coprimality of `p` and `implicitDeriv v p` is preserved by differential base change. -/
theorem isCoprime_map_implicitDeriv_of_isCoprime {v p : k[X]}
    (hp : IsCoprime p (Differential.implicitDeriv v p)) :
    IsCoprime (p.map (algebraMap k E))
      (Differential.implicitDeriv (v.map (algebraMap k E)) (p.map (algebraMap k E))) := by
  rw [← implicitDeriv_map]
  have := hp.map (Polynomial.mapRingHom (algebraMap k E))
  simpa only [coe_mapRingHom] using this

end AlgebraicExtension

section ConstantField
-- The case `Da = 0` for all `a ∈ k`, where special and normal root tests depend only on `v(a)`.
variable {K : Type*} [Field K] [Differential K]

/-- If every scalar is constant, then `X - C a` is special for `implicitDeriv v` iff it divides `v`. -/
theorem dvd_X_sub_C_implicitDeriv_iff_dvd (hconst : ∀ a : K, (a : K)′ = 0) (v : K[X]) (a : K) :
    (X - C a) ∣ Differential.implicitDeriv v (X - C a) ↔ (X - C a) ∣ v := by
  rw [dvd_X_sub_C_implicitDeriv_iff, hconst a, dvd_iff_isRoot, IsRoot.def, eq_comm]

/-- If every scalar is constant, then a product of linear factors is special for `implicitDeriv v` iff it divides `v`. -/
theorem dvd_prod_X_sub_C_implicitDeriv_iff_dvd (hconst : ∀ a : K, (a : K)′ = 0) (v : K[X])
    (s : Finset K) :
    (∏ a ∈ s, (X - C a)) ∣ Differential.implicitDeriv v (∏ a ∈ s, (X - C a))
      ↔ (∏ a ∈ s, (X - C a)) ∣ v := by
  rw [dvd_prod_X_sub_C_implicitDeriv_iff]
  constructor
  · intro h
    refine Finset.prod_dvd_of_coprime (fun a _ b _ hab => isCoprime_X_sub_C_iff.mpr
      (by rw [eval_sub, eval_X, eval_C]; exact sub_ne_zero.mpr hab)) (fun a ha => ?_)
    rw [dvd_iff_isRoot, IsRoot.def, h a ha, hconst a]
  · intro h a ha
    rw [hconst a]
    exact (dvd_iff_isRoot.mp ((Finset.dvd_prod_of_mem _ ha).trans h))

/-- If every scalar is constant, then a product of linear factors is normal for `implicitDeriv v` iff it is coprime to `v`. -/
theorem isCoprime_prod_X_sub_C_implicitDeriv_iff_isCoprime (hconst : ∀ a : K, (a : K)′ = 0)
    (v : K[X]) (s : Finset K) :
    IsCoprime (∏ a ∈ s, (X - C a)) (Differential.implicitDeriv v (∏ a ∈ s, (X - C a)))
      ↔ IsCoprime (∏ a ∈ s, (X - C a)) v := by
  rw [isCoprime_prod_X_sub_C_implicitDeriv_iff, IsCoprime.prod_left_iff]
  refine forall₂_congr (fun a ha => ?_)
  rw [isCoprime_X_sub_C_iff, hconst a, ne_comm]

end ConstantField

end DeepWiki.SymbolicIntegration
