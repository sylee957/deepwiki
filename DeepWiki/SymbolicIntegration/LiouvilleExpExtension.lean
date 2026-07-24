import Mathlib.FieldTheory.Differential.Liouville
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Tactic
import DeepWiki.SymbolicIntegration.DifferentialAlgebra.FractionField
import DeepWiki.Algebra.RatFuncEmbedding
import DeepWiki.SymbolicIntegration.LiouvilleRatFuncData

/-! # The transcendental exponential Liouville extension

The transcendental exponential case of Liouville's theorem on `RatFunc F`, with the exp monomial
`t = exp u` (`u ∈ F`) whose derivation is `t' = u'·t` (vs the log monomial `t' = u'/u`).
Conditional on `NondegenerateExp u`: `F(exp u) = RatFunc F` is Liouville over `F`.
-/

open scoped Differential
open Polynomial Differential

namespace DeepWiki.SymbolicIntegration.LiouvilleExp

section PolynomialSetup

variable {F : Type*} [Field F] [Differential F]

/-- The exp-monomial polynomial `C u' * X` realizing `t' = u'·t` for `t = exp u`. -/
noncomputable abbrev expMonomial (u : F) : F[X] := C (u′) * X

/-- The exp-monomial derivation on `F[t]` with `t' = u'·t`. -/
noncomputable def expDerivPoly (u : F) : Derivation ℤ F[X] F[X] :=
  Differential.implicitDeriv (expMonomial u)

/-- `F[t]` as a `Differential` ring under the exp-monomial derivation `t' = u'·t`. -/
@[reducible]
noncomputable def expDifferentialPoly (u : F) : Differential F[X] :=
  ⟨expDerivPoly u⟩

/-- `expDerivPoly u X = C u' * X`: the exp-monomial defining equation `t' = u'·t`. -/
@[simp]
lemma expDerivPoly_X (u : F) : expDerivPoly u (X : F[X]) = C (u′) * X := by
  simp [expDerivPoly]

/-- On `F[t]`, the derivation sends a constant `C b` to `C b'` (it extends `F`'s derivation). -/
@[simp]
lemma expDerivPoly_C (u : F) (b : F) : expDerivPoly u (C b) = C b′ := by
  simp [expDerivPoly]

/-- The exp-monomial derivation makes `F[t]` a `DifferentialAlgebra F F[t]` (extends `F`). -/
lemma expDerivPoly_differentialAlgebra (u : F) :
    letI := expDifferentialPoly u
    DifferentialAlgebra F F[X] := by
  letI := expDifferentialPoly u
  refine ⟨fun a => ?_⟩
  change expDerivPoly u (C a) = C a′
  simp

/-- The diagonal coefficient formula: `(D p).coeff i = (p.coeff i)' + u'·i·p.coeff i` (no index shift). -/
lemma coeff_expDerivPoly (u : F) (p : F[X]) (i : ℕ) :
    (expDerivPoly u p).coeff i = (p.coeff i)′ + u′ * (i * p.coeff i) := by
  simp only [expDerivPoly, expMonomial, implicitDeriv, Derivation.coe_add, Pi.add_apply,
    Derivation.coe_smul, Pi.smul_apply, Derivation.restrictScalars_apply,
    derivative'_apply, coeff_add, coeff_mapCoeffs, smul_eq_mul]
  rcases i with _ | j
  · simp
  · rw [show C (u′) * X * derivative p = C (u′) * (X * derivative p) by ring,
      coeff_C_mul, coeff_X_mul, coeff_derivative]
    push_cast
    ring

/-- The exp-monomial derivation does not raise `t`-degree: `natDegree (D p) ≤ natDegree p`. -/
lemma natDegree_expDerivPoly_le (u : F) (p : F[X]) :
    (expDerivPoly u p).natDegree ≤ p.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [coeff_expDerivPoly]
  have h1 : p.coeff i = 0 := coeff_eq_zero_of_natDegree_lt hi
  rw [h1]; simp

/-- The top `t`-degree coefficient: `(D p).coeff (deg p) = (lc p)' + (deg p)·u'·(lc p)`. -/
lemma coeff_natDegree_expDerivPoly (u : F) (p : F[X]) :
    (expDerivPoly u p).coeff p.natDegree
      = (p.leadingCoeff)′ + u′ * (p.natDegree * p.leadingCoeff) := by
  rw [coeff_expDerivPoly]; rfl

/-- The special factor `t = X`: `X ∣ D X`, since `expDerivPoly u X = u'·X` (`t = exp u` is a unit). -/
lemma X_dvd_expDerivPoly_X (u : F) : (X : F[X]) ∣ expDerivPoly u X := by
  rw [expDerivPoly_X]; exact Dvd.intro_left (C (u′)) rfl

end PolynomialSetup

/-! ## The genuine field extension `F(t) = RatFunc F`. -/

section FieldSetup

variable {F : Type*} [Field F] [Differential F] [CharZero F]

open RatFunc

/-- The `Differential (RatFunc F)` for the exp monomial `t = exp u` (`t' = u'·t`). -/
@[reducible]
noncomputable def expDifferential (u : F) : Differential (RatFunc F) :=
  FractionRingDeriv.differentialOf (K := RatFunc F) (expDifferentialPoly u)

omit [CharZero F] in
/-- The derivation on `RatFunc F` restricts to `expDerivPoly u` on the image of `F[t]`. -/
theorem derivExtends (u : F) :
    letI := expDifferential u
    ∀ p : F[X], (algebraMap F[X] (RatFunc F) p)′
      = algebraMap F[X] (RatFunc F) (expDerivPoly u p) :=
  fun p => FractionRingDeriv.deriv_algebraMap (K := RatFunc F) (expDerivPoly u) p

omit [CharZero F] in
/-- A `Differential (RatFunc F)` restricting to `expDerivPoly u` on `F[t]` is a
`DifferentialAlgebra F (RatFunc F)`. -/
theorem differentialAlgebra_of_derivExtends [Differential (RatFunc F)] {u : F}
    (h : ∀ p : F[X], (algebraMap F[X] (RatFunc F) p)′
      = algebraMap F[X] (RatFunc F) (expDerivPoly u p)) :
    DifferentialAlgebra F (RatFunc F) where
  deriv_algebraMap a := by
    have hfac : (algebraMap F (RatFunc F)) a
        = algebraMap F[X] (RatFunc F) (C a) := by
      rw [IsScalarTower.algebraMap_eq F F[X] (RatFunc F)]
      simp [Polynomial.algebraMap_eq]
    rw [hfac, h (C a), expDerivPoly_C]
    rw [IsScalarTower.algebraMap_eq F F[X] (RatFunc F)]
    simp [Polynomial.algebraMap_eq]

omit [CharZero F] in
/-- `RatFunc F` with the exp-monomial derivation is a `DifferentialAlgebra F (RatFunc F)`. -/
theorem expDifferentialAlgebra (u : F) :
    letI := expDifferential u
    DifferentialAlgebra F (RatFunc F) :=
  letI := expDifferential u
  differentialAlgebra_of_derivExtends (u := u) (derivExtends u)

omit [CharZero F] in
/-- In `RatFunc F`, `logDeriv (algebraMap p) = algebraMap (expDerivPoly u p) / algebraMap p`. -/
theorem logDeriv_algebraMap_eq (u : F) (p : F[X]) :
    letI := expDifferential u
    logDeriv (algebraMap F[X] (RatFunc F) p)
      = algebraMap F[X] (RatFunc F) (expDerivPoly u p) / algebraMap F[X] (RatFunc F) p := by
  letI := expDifferential u
  unfold logDeriv
  rw [derivExtends u p]

omit [CharZero F] in
/-- `logDeriv (exp u) = u'`: in `RatFunc F`, `logDeriv (algebraMap X) = algebraMap u'`. -/
theorem logDeriv_X_eq (u : F) :
    letI := expDifferential u
    logDeriv (algebraMap F[X] (RatFunc F) X) = algebraMap F (RatFunc F) (u′) := by
  letI := expDifferential u
  rw [logDeriv_algebraMap_eq u X, expDerivPoly_X, map_mul, ratFunc_algebraMap_eq_algebraMap_C,
    mul_div_assoc]
  have hXne : algebraMap F[X] (RatFunc F) X ≠ 0 := RatFunc.algebraMap_ne_zero X_ne_zero
  rw [div_self hXne, mul_one]

end FieldSetup

/-! ## The exp pole engine: the special factor `X` and the non-degeneracy for `π ≠ X`. -/

section ExpPole

variable {F : Type*} [Field F] [Differential F]

/-- The Leibniz pole-order drop: `q^n ∣ p ⟹ q^(n-1) ∣ expDerivPoly u p`. -/
lemma pow_sub_one_dvd_expDerivPoly (u : F) {p q : F[X]} {n : ℕ} (hdvd : q ^ n ∣ p) :
    q ^ (n - 1) ∣ expDerivPoly u p := by
  obtain ⟨r, rfl⟩ := hdvd
  have hpn : q ^ (n - 1) ∣ expDerivPoly u (q ^ n) := by
    rw [Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul]
    exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _
  have hpow : q ^ (n - 1) ∣ q ^ n := pow_dvd_pow q (Nat.sub_le n 1)
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  exact dvd_add (dvd_mul_of_dvd_left hpow _) (dvd_mul_of_dvd_right hpn _)

/-- For `k ≥ 1`, `D(q^k · m) = q^(k-1) · (k · (D q) · m + q · D m)`. -/
lemma expDerivPoly_pow_mul (u : F) {q m : F[X]} {k : ℕ} (hk : 1 ≤ k) :
    expDerivPoly u (q ^ k * m)
      = q ^ (k - 1) * ((k : F[X]) * expDerivPoly u q * m + q * expDerivPoly u m) := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, Derivation.leibniz_pow, nsmul_eq_mul,
    smul_eq_mul]
  have hqk : q ^ k = q ^ (k - 1) * q := by
    rw [← pow_succ]; congr 1; omega
  rw [hqk]; ring

/-- When `q ∤ D q` and `q^k ∣∣ p` (`k ≥ 1`), `q^k ∤ expDerivPoly u p`. -/
lemma not_pow_dvd_expDerivPoly_of_exact [CharZero F] (u : F) {p q : F[X]} {k : ℕ}
    (hq : Irreducible q) (hDq : ¬ q ∣ expDerivPoly u q) (hk : 1 ≤ k)
    (hdvd : q ^ k ∣ p) (hndvd : ¬ q ^ (k + 1) ∣ p) : ¬ q ^ k ∣ expDerivPoly u p := by
  obtain ⟨m, rfl⟩ := hdvd
  have hqm : ¬ q ∣ m := by
    rintro ⟨m', rfl⟩
    exact hndvd ⟨m', by rw [pow_succ]; ring⟩
  rw [expDerivPoly_pow_mul u (q := q) (m := m) hk]
  have hqk : q ^ k = q ^ (k - 1) * q := by rw [← pow_succ]; congr 1; omega
  rw [hqk]
  intro hdvd'
  have hcancel : q ∣ ((k : F[X]) * expDerivPoly u q * m + q * expDerivPoly u m) :=
    (mul_dvd_mul_iff_left (pow_ne_zero (k - 1) hq.ne_zero)).mp hdvd'
  have hk_part : q ∣ (k : F[X]) * expDerivPoly u q * m :=
    (dvd_add_right (dvd_mul_right q (expDerivPoly u m))).mp (by rwa [add_comm] at hcancel)
  have hkne : ¬ q ∣ (k : F[X]) := by
    intro hdvdk
    have : q.natDegree ≤ ((k : F[X])).natDegree :=
      Polynomial.natDegree_le_of_dvd hdvdk (by
        simpa using (Nat.cast_ne_zero.mpr (by omega : k ≠ 0) : (k : F) ≠ 0))
    have hkdeg : ((k : F[X])).natDegree = 0 := Polynomial.natDegree_natCast k
    have := hq.natDegree_pos
    omega
  rcases (hq.prime.dvd_mul.mp hk_part) with h1 | h2
  · rcases (hq.prime.dvd_mul.mp h1) with hk' | hDq'
    · exact hkne hk'
    · exact hDq hDq'
  · exact hqm h2

/-- For `q ∤ D q`, the exact pole-order drop `emultiplicity q (expDerivPoly u p) = emultiplicity q p - 1`. -/
lemma emultiplicity_expDerivPoly_eq [CharZero F] (u : F) {p q : F[X]} {k : ℕ}
    (hq : Irreducible q) (hDq : ¬ q ∣ expDerivPoly u q) (hk : 1 ≤ k)
    (hmult : emultiplicity q p = (k : ℕ∞)) :
    emultiplicity q (expDerivPoly u p) = ((k - 1 : ℕ) : ℕ∞) := by
  have hdvd : q ^ k ∣ p := pow_dvd_of_le_emultiplicity (by rw [hmult])
  have hndvd : ¬ q ^ (k + 1) ∣ p := by
    rw [← emultiplicity_lt_iff_not_dvd, hmult]; exact_mod_cast Nat.lt_succ_self k
  have hlo : ((k - 1 : ℕ) : ℕ∞) ≤ emultiplicity q (expDerivPoly u p) :=
    le_emultiplicity_of_pow_dvd (pow_sub_one_dvd_expDerivPoly u hdvd)
  have hhi : emultiplicity q (expDerivPoly u p) < (k : ℕ∞) :=
    emultiplicity_lt_iff_not_dvd.mpr (not_pow_dvd_expDerivPoly_of_exact u hq hDq hk hdvd hndvd)
  have hk1 : (k : ℕ∞) = ((k - 1 : ℕ) : ℕ∞) + 1 := by
    rw [← ENat.coe_one, ← Nat.cast_add]; congr 1; omega
  rw [hk1] at hhi
  exact le_antisymm ((ENat.lt_add_one_iff (ENat.coe_ne_top _)).mp hhi) hlo

/-- The exp new-monomial condition: no nonzero integer `k` makes `k·u'` a logarithmic derivative
`logDeriv g` of an `F`-element `g ≠ 0` (i.e. `exp(k u) ∉ F` for `k ≠ 0`). -/
def NondegenerateExp (u : F) : Prop :=
  ∀ (k : ℤ), k ≠ 0 → ∀ g : F, g ≠ 0 → logDeriv g ≠ (k : F) * u′

/-- Under `NondegenerateExp`, a monic `d` with `deg d ≥ 1` and `X ∤ d` has `d ∤ expDerivPoly u d`. -/
lemma not_dvd_expDerivPoly_of_monic_of_X_ndvd [CharZero F] (u : F) (hnd : NondegenerateExp u)
    {d : F[X]} (hm : d.Monic) (hdeg : 1 ≤ d.natDegree) (hXd : ¬ X ∣ d) :
    ¬ d ∣ expDerivPoly u d := by
  intro hdvd
  set m := d.natDegree with hmdef
  obtain ⟨c, hc⟩ := hdvd
  have hcdeg : c.natDegree = 0 := by
    by_contra h0
    have h1 : 1 ≤ c.natDegree := Nat.one_le_iff_ne_zero.mpr h0
    have hcne : c ≠ 0 := by rintro rfl; simp at h1
    have hdegmul : (d * c).natDegree = m + c.natDegree :=
      Polynomial.natDegree_mul hm.ne_zero hcne
    have hle : (expDerivPoly u d).natDegree ≤ m := natDegree_expDerivPoly_le u d
    rw [← hc] at hdegmul; omega
  obtain ⟨cc, hcc⟩ : ∃ cc : F, c = C cc := ⟨c.coeff 0, Polynomial.eq_C_of_natDegree_eq_zero hcdeg⟩
  have htop := coeff_natDegree_expDerivPoly u d
  rw [hm.leadingCoeff] at htop
  simp only [Derivation.map_one_eq_zero, mul_one, zero_add] at htop
  have hcoeffm : (expDerivPoly u d).coeff m = cc := by
    rw [hc, hcc, Polynomial.coeff_mul_C, show d.coeff m = d.leadingCoeff from rfl,
      hm.leadingCoeff, one_mul]
  have hcceq : cc = u′ * (m : F) := by rw [← hcoeffm]; exact htop
  have hc0_lhs : (expDerivPoly u d).coeff 0 = (d.coeff 0)′ := by
    rw [coeff_expDerivPoly]; simp
  have hc0_rhs : (expDerivPoly u d).coeff 0 = cc * d.coeff 0 := by
    rw [hc, hcc, Polynomial.coeff_mul_C, mul_comm]
  have hd0ne : d.coeff 0 ≠ 0 := fun h0 => hXd (by rw [Polynomial.X_dvd_iff]; exact h0)
  have hlog : logDeriv (d.coeff 0) = (m : F) * u′ := by
    rw [logDeriv, hc0_lhs.symm.trans hc0_rhs, hcceq]
    rw [mul_assoc, mul_div_assoc, mul_div_cancel_right₀ _ hd0ne]
    ring
  exact hnd (m : ℤ) (by exact_mod_cast Nat.one_le_iff_ne_zero.mp hdeg) (d.coeff 0) hd0ne
    (by rw [hlog]; push_cast; ring)

/-- Under `NondegenerateExp`, a monic irreducible `π ≠ X` has `π ∤ expDerivPoly u π`. -/
lemma not_dvd_expDerivPoly_of_ne_X [CharZero F] (u : F) (hnd : NondegenerateExp u)
    {π : F[X]} (hm : π.Monic) (hirr : Irreducible π) (hX : π ≠ X) :
    ¬ π ∣ expDerivPoly u π := by
  refine not_dvd_expDerivPoly_of_monic_of_X_ndvd u hnd hm hirr.natDegree_pos ?_
  intro hXdvd
  exact hX (eq_of_monic_of_associated monic_X hm
    ((irreducible_X.associated_of_dvd hirr hXdvd))).symm

/-- `NondegenerateExp u` forces `u' ≠ 0`. -/
lemma deriv_ne_zero_of_nondegenerateExp (u : F) (hnd : NondegenerateExp u) : u′ ≠ 0 := by
  intro h0
  exact hnd 1 one_ne_zero 1 one_ne_zero (by rw [logDeriv_one, h0]; push_cast; ring)

/-- Under `NondegenerateExp`, a monic irreducible `π` with `π ∣ expDerivPoly u π` is `X`. -/
lemma eq_X_of_dvd_expDerivPoly [CharZero F] (u : F) (hnd : NondegenerateExp u)
    {π : F[X]} (hm : π.Monic) (hirr : Irreducible π) (hdvd : π ∣ expDerivPoly u π) : π = X := by
  by_contra hX
  exact not_dvd_expDerivPoly_of_ne_X u hnd hm hirr hX hdvd

/-- Under `NondegenerateExp`, a monic `d ∣ expDerivPoly u d` is a pure power `d = X^(deg d)`. -/
lemma eq_X_pow_of_dvd_expDerivPoly [CharZero F] (u : F) (hnd : NondegenerateExp u)
    {d : F[X]} (hm : d.Monic) (hdvd : d ∣ expDerivPoly u d) :
    d = X ^ d.natDegree := by
  classical
  have hfac_eq : ∀ {π : F[X]}, π ∈ UniqueFactorizationMonoid.normalizedFactors d → π = X := by
    intro π hπ
    have hπmon : π.Monic := by
      have hne : π ≠ 0 := UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors hπ
      exact (Polynomial.normalize_eq_self_iff_monic hne).mp
        (UniqueFactorizationMonoid.normalize_normalized_factor π hπ)
    have hπirr : Irreducible π :=
      UniqueFactorizationMonoid.irreducible_of_normalized_factor _ hπ
    by_contra hπX
    have hπd : π ∣ d := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hπ
    have hfin : FiniteMultiplicity π d := Polynomial.finiteMultiplicity_of_degree_pos_of_monic
      (hπirr.degree_pos) hπmon hm.ne_zero
    set e := multiplicity π d with hedef
    have hmultd : emultiplicity π d = (e : ℕ∞) := hfin.emultiplicity_eq_multiplicity
    have he1 : 1 ≤ e := hfin.le_multiplicity_of_pow_dvd (by simpa using hπd)
    have hπnDπ : ¬ π ∣ expDerivPoly u π := not_dvd_expDerivPoly_of_ne_X u hnd hπmon hπirr hπX
    have hmultDd : emultiplicity π (expDerivPoly u d) = ((e - 1 : ℕ) : ℕ∞) :=
      emultiplicity_expDerivPoly_eq u hπirr hπnDπ he1 hmultd
    have hpe_dvd : π ^ e ∣ expDerivPoly u d :=
      dvd_trans (pow_dvd_of_le_emultiplicity (by rw [hmultd])) hdvd
    have hge : (e : ℕ∞) ≤ emultiplicity π (expDerivPoly u d) :=
      le_emultiplicity_of_pow_dvd hpe_dvd
    rw [hmultDd] at hge
    have hle : (e : ℕ∞) ≤ ((e - 1 : ℕ) : ℕ∞) := hge
    rw [Nat.cast_le] at hle; omega
  obtain ⟨i, hassoc⟩ :=
    UniqueFactorizationMonoid.exists_associated_prime_pow_of_unique_normalized_factor
      (p := X) (r := d) (fun {m} hm => hfac_eq hm) hm.ne_zero
  have hXmon : (X ^ i : F[X]).Monic := monic_X.pow i
  have heq : X ^ i = d := eq_of_monic_of_associated hXmon hm hassoc
  have hdeg : d.natDegree = i := by rw [← heq, natDegree_pow, natDegree_X, mul_one]
  rw [hdeg, ← heq]

/-- `(expDerivPoly u N - C (k·u') * N).coeff i = (N.coeff i)' + u'·(i − k)·N.coeff i`. -/
lemma coeff_expDerivPoly_sub_C_mul (u : F) (N : F[X]) (k : ℕ) (i : ℕ) :
    (expDerivPoly u N - C ((k : F) * u′) * N).coeff i
      = (N.coeff i)′ + u′ * ((i : F) - k) * N.coeff i := by
  rw [coeff_sub, coeff_expDerivPoly, coeff_C_mul]; ring

end ExpPole

/-! ## The `v`-term descent: `v′ ∈ F ⟹ v ∈ F` for the exp monomial.

A rational `v` with polynomial (resp. `F`-valued) derivative is itself polynomial (resp. `F`-valued),
via the special-factor structure `d ∣ D d ⟹ d = X^k`. -/

section VDescent

variable {F : Type*} [Field F] [Differential F] [CharZero F]

open RatFunc

/-- The `X`-coprime descent: if `v′` is a polynomial and `denom v` is coprime to `X`, then `v` is a
polynomial. -/
theorem rationalToPoly_of_X_coprime (u : F) (hnd : NondegenerateExp u) {v : RatFunc F}
    (hvpoly : letI := expDifferential u; v′ ∈ (algebraMap F[X] (RatFunc F)).range)
    (hcopX : IsCoprime (RatFunc.denom v) Polynomial.X) :
    letI := expDifferential u
    v ∈ (algebraMap F[X] (RatFunc F)).range := by
  letI := expDifferential u
  rcases eq_or_ne v 0 with rfl | hv0
  · exact ⟨0, by rw [map_zero]⟩
  obtain ⟨P, hP⟩ := hvpoly
  set n := RatFunc.num v with hndef
  set d := RatFunc.denom v with hddef
  have hdmon : d.Monic := RatFunc.monic_denom v
  have hdne0 : d ≠ 0 := RatFunc.denom_ne_zero v
  have hnne0 : n ≠ 0 := RatFunc.num_ne_zero hv0
  have hcop : IsCoprime n d := RatFunc.isCoprime_num_denom v
  have hnA : algebraMap F[X] (RatFunc F) n ≠ 0 := RatFunc.algebraMap_ne_zero hnne0
  have hdA : algebraMap F[X] (RatFunc F) d ≠ 0 := RatFunc.algebraMap_ne_zero hdne0
  have hveq : v = algebraMap F[X] (RatFunc F) n / algebraMap F[X] (RatFunc F) d := by
    rw [← RatFunc.num_div_denom v, ← hndef, ← hddef]
  have hlogv : logDeriv v
      = algebraMap F[X] (RatFunc F) (expDerivPoly u n) / algebraMap F[X] (RatFunc F) n
        - algebraMap F[X] (RatFunc F) (expDerivPoly u d) / algebraMap F[X] (RatFunc F) d := by
    have hsplit : logDeriv v = logDeriv (algebraMap F[X] (RatFunc F) n)
        - logDeriv (algebraMap F[X] (RatFunc F) d) := by
      conv_lhs => rw [hveq]
      exact logDeriv_div _ _ hnA hdA
    rw [hsplit, logDeriv_algebraMap_eq u n, logDeriv_algebraMap_eq u d]
  have hv'eq : v′ = v * logDeriv v := by rw [logDeriv, mul_div_cancel₀ _ hv0]
  have hkey : algebraMap F[X] (RatFunc F) (P * (d * d))
      = algebraMap F[X] (RatFunc F) (d * expDerivPoly u n - n * expDerivPoly u d) := by
    have hPv : algebraMap F[X] (RatFunc F) P = v * logDeriv v := by rw [hP, hv'eq]
    rw [hlogv, hveq] at hPv
    rw [map_mul, map_mul, map_sub, map_mul, map_mul]
    field_simp at hPv ⊢
    linear_combination hPv
  have hkeyP : P * (d * d) = d * expDerivPoly u n - n * expDerivPoly u d :=
    FaithfulSMul.algebraMap_injective F[X] (RatFunc F) hkey
  have hdvd_nDd : d ∣ n * expDerivPoly u d := by
    have hrw : n * expDerivPoly u d = d * expDerivPoly u n - P * (d * d) := by
      linear_combination hkeyP
    rw [hrw]
    exact Dvd.dvd.sub (dvd_mul_right d _) (dvd_mul_of_dvd_right (dvd_mul_right d d) P)
  have hdvd_Dd : d ∣ expDerivPoly u d := hcop.symm.dvd_of_dvd_mul_left hdvd_nDd
  have hXd : ¬ Polynomial.X ∣ d :=
    (Polynomial.irreducible_X.coprime_iff_not_dvd).mp hcopX.symm
  have hdeg0 : d.natDegree = 0 := by
    by_contra hdeg
    exact not_dvd_expDerivPoly_of_monic_of_X_ndvd u hnd hdmon
      (Nat.one_le_iff_ne_zero.mpr hdeg) hXd hdvd_Dd
  have hd1 : d = 1 := eq_one_of_monic_natDegree_zero hdmon hdeg0
  refine ⟨n, ?_⟩
  rw [hveq, hd1, map_one, div_one]

omit [CharZero F] in
/-- `logDeriv (algebraMap (X^k)) = k·u'` in `RatFunc F` (the special factor contributes no `t`-pole). -/
theorem logDeriv_X_pow_eq (u : F) (k : ℕ) :
    letI := expDifferential u
    logDeriv (algebraMap F[X] (RatFunc F) (Polynomial.X ^ k))
      = algebraMap F (RatFunc F) ((k : F) * u′) := by
  letI := expDifferential u
  rw [map_pow, logDeriv_pow, logDeriv_X_eq, map_mul, map_natCast]

omit [CharZero F] in
/-- For `b ≠ 0`, `logDeriv (algebraMap (C b · X^k)) = logDeriv b + k·u'` in `RatFunc F` (`F`-valued). -/
theorem logDeriv_C_mul_X_pow_eq (u : F) {b : F} (hb : b ≠ 0) (k : ℕ) :
    letI := expDifferential u
    letI := expDifferentialAlgebra u
    logDeriv (algebraMap F[X] (RatFunc F) (Polynomial.C b * Polynomial.X ^ k))
      = algebraMap F (RatFunc F) (logDeriv b + (k : F) * u′) := by
  letI := expDifferential u
  letI := expDifferentialAlgebra u
  have hbA : algebraMap F[X] (RatFunc F) (Polynomial.C b) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (by simpa [Polynomial.C_eq_zero] using hb)
  have hXkA : algebraMap F[X] (RatFunc F) (Polynomial.X ^ k) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
  rw [map_mul, Differential.logDeriv_mul _ _ hbA hXkA,
    ← ratFunc_algebraMap_eq_algebraMap_C, logDeriv_algebraMap,
    map_pow, logDeriv_pow, logDeriv_X_eq, map_add, map_mul, map_natCast]

omit [CharZero F] in
/-- If `v ≠ 0` has polynomial `v′`, then `denom v ∣ expDerivPoly u (denom v)`. -/
theorem denom_dvd_expDerivPoly_denom (u : F) {v : RatFunc F} (hv0 : v ≠ 0)
    (hvpoly : letI := expDifferential u; v′ ∈ (algebraMap F[X] (RatFunc F)).range) :
    (RatFunc.denom v) ∣ expDerivPoly u (RatFunc.denom v) := by
  letI := expDifferential u
  obtain ⟨P, hP⟩ := hvpoly
  set n := RatFunc.num v with hndef
  set d := RatFunc.denom v with hddef
  have hdne0 : d ≠ 0 := RatFunc.denom_ne_zero v
  have hnne0 : n ≠ 0 := RatFunc.num_ne_zero hv0
  have hcop : IsCoprime n d := RatFunc.isCoprime_num_denom v
  have hnA : algebraMap F[X] (RatFunc F) n ≠ 0 := RatFunc.algebraMap_ne_zero hnne0
  have hdA : algebraMap F[X] (RatFunc F) d ≠ 0 := RatFunc.algebraMap_ne_zero hdne0
  have hveq : v = algebraMap F[X] (RatFunc F) n / algebraMap F[X] (RatFunc F) d := by
    rw [← RatFunc.num_div_denom v, ← hndef, ← hddef]
  have hlogv : logDeriv v
      = algebraMap F[X] (RatFunc F) (expDerivPoly u n) / algebraMap F[X] (RatFunc F) n
        - algebraMap F[X] (RatFunc F) (expDerivPoly u d) / algebraMap F[X] (RatFunc F) d := by
    have hsplit : logDeriv v = logDeriv (algebraMap F[X] (RatFunc F) n)
        - logDeriv (algebraMap F[X] (RatFunc F) d) := by
      conv_lhs => rw [hveq]
      exact logDeriv_div _ _ hnA hdA
    rw [hsplit, logDeriv_algebraMap_eq u n, logDeriv_algebraMap_eq u d]
  have hv'eq : v′ = v * logDeriv v := by rw [logDeriv, mul_div_cancel₀ _ hv0]
  have hkey : algebraMap F[X] (RatFunc F) (P * (d * d))
      = algebraMap F[X] (RatFunc F) (d * expDerivPoly u n - n * expDerivPoly u d) := by
    have hPv : algebraMap F[X] (RatFunc F) P = v * logDeriv v := by rw [hP, hv'eq]
    rw [hlogv, hveq] at hPv
    rw [map_mul, map_mul, map_sub, map_mul, map_mul]
    field_simp at hPv ⊢
    linear_combination hPv
  have hkeyP : P * (d * d) = d * expDerivPoly u n - n * expDerivPoly u d :=
    FaithfulSMul.algebraMap_injective F[X] (RatFunc F) hkey
  have hdvd_nDd : d ∣ n * expDerivPoly u d := by
    have hrw : n * expDerivPoly u d = d * expDerivPoly u n - P * (d * d) := by
      linear_combination hkeyP
    rw [hrw]
    exact Dvd.dvd.sub (dvd_mul_right d _) (dvd_mul_of_dvd_right (dvd_mul_right d d) P)
  exact hcop.symm.dvd_of_dvd_mul_left hdvd_nDd

omit [CharZero F] in
/-- Under `NondegenerateExp`, if `expDerivPoly u N - C (k·u') * N = C b · X^k` then `N.coeff i = 0`
for every `i ≠ k`. -/
theorem N_coeff_eq_zero_of_eq_C_mul_X_pow (u : F) (hnd : NondegenerateExp u)
    (N : F[X]) (k : ℕ) (b : F)
    (hM : expDerivPoly u N - Polynomial.C ((k : F) * u′) * N = Polynomial.C b * Polynomial.X ^ k) :
    ∀ i, i ≠ k → N.coeff i = 0 := by
  intro i hik
  by_contra hNi
  have hMcoeff : (expDerivPoly u N - Polynomial.C ((k : F) * u′) * N).coeff i = 0 := by
    rw [hM, coeff_C_mul, coeff_X_pow]; simp [hik]
  rw [coeff_expDerivPoly_sub_C_mul] at hMcoeff
  have hlog : logDeriv (N.coeff i) = ((k : F) - i) * u′ := by
    rw [logDeriv,
      show (N.coeff i)′ = ((k : F) - i) * u′ * N.coeff i from by linear_combination hMcoeff,
      mul_div_assoc, div_self hNi, mul_one]
  refine hnd ((k : ℤ) - i) ?_ (N.coeff i) hNi ?_
  · simp only [sub_ne_zero]; exact fun h => hik (by exact_mod_cast h.symm)
  · rw [hlog]; push_cast; ring

/-- Under `NondegenerateExp`, `v′ ∈ F ⟹ v ∈ F` (the exp `v`-term reduction). -/
theorem expDeriv_mem_range_imp_mem_range (u : F) (hnd : NondegenerateExp u) {v : RatFunc F}
    (hvpoly : letI := expDifferential u; v′ ∈ (algebraMap F (RatFunc F)).range) :
    letI := expDifferential u
    v ∈ (algebraMap F (RatFunc F)).range := by
  letI := expDifferential u
  letI := expDifferentialAlgebra u
  rcases eq_or_ne v 0 with rfl | hv0
  · exact ⟨0, by rw [map_zero]⟩
  obtain ⟨b, hb⟩ := hvpoly
  have hvpoly' : v′ ∈ (algebraMap F[X] (RatFunc F)).range := by
    refine ⟨Polynomial.C b, ?_⟩; rw [← ratFunc_algebraMap_eq_algebraMap_C, hb]
  set d := RatFunc.denom v with hddef
  have hddvd : d ∣ expDerivPoly u d := denom_dvd_expDerivPoly_denom u hv0 hvpoly'
  have hdmon : d.Monic := RatFunc.monic_denom v
  set k := d.natDegree with hkdef
  have hdXk : d = Polynomial.X ^ k := eq_X_pow_of_dvd_expDerivPoly u hnd hdmon hddvd
  set N := RatFunc.num v with hNdef
  have hNne0 : N ≠ 0 := RatFunc.num_ne_zero hv0
  have hNA : algebraMap F[X] (RatFunc F) N ≠ 0 := RatFunc.algebraMap_ne_zero hNne0
  have hXkA : algebraMap F[X] (RatFunc F) (Polynomial.X ^ k) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
  have hveq : v = algebraMap F[X] (RatFunc F) N / algebraMap F[X] (RatFunc F) (Polynomial.X ^ k) := by
    rw [← RatFunc.num_div_denom v, ← hNdef, ← hddef, hdXk]
  have hlogv : logDeriv v
      = algebraMap F[X] (RatFunc F) (expDerivPoly u N) / algebraMap F[X] (RatFunc F) N
        - algebraMap F (RatFunc F) ((k : F) * u′) := by
    have hpow : logDeriv (algebraMap F[X] (RatFunc F) (Polynomial.X ^ k)) =
        algebraMap F (RatFunc F) ((k : F) * u′) := by
      rw [map_pow, logDeriv_pow, logDeriv_X_eq, map_mul, map_natCast]
    have hsplit : logDeriv v = logDeriv (algebraMap F[X] (RatFunc F) N)
        - logDeriv (algebraMap F[X] (RatFunc F) (Polynomial.X ^ k)) := by
      conv_lhs => rw [hveq]
      exact logDeriv_div _ _ hNA hXkA
    rw [hsplit, logDeriv_algebraMap_eq u N, hpow]
  have hv'eq : v′ = v * logDeriv v := by rw [logDeriv, mul_div_cancel₀ _ hv0]
  set M : F[X] := expDerivPoly u N - Polynomial.C ((k : F) * u′) * N with hMdef
  have hclear : v′ * algebraMap F[X] (RatFunc F) (Polynomial.X ^ k)
      = algebraMap F[X] (RatFunc F) M := by
    rw [hv'eq, hlogv, hveq, hMdef, map_sub, map_mul, ratFunc_algebraMap_eq_algebraMap_C]
    field_simp
    congr 1
    rw [Polynomial.C_mul, map_mul, map_mul, ratFunc_algebraMap_eq_algebraMap_C, map_natCast]
    ring
  have hMeq : M = Polynomial.C b * Polynomial.X ^ k := by
    apply FaithfulSMul.algebraMap_injective F[X] (RatFunc F)
    rw [map_mul, ← ratFunc_algebraMap_eq_algebraMap_C, ← hclear, ← hb]
  have hNzero : ∀ i, i ≠ k → N.coeff i = 0 := N_coeff_eq_zero_of_eq_C_mul_X_pow u hnd N k b hMeq
  have hNmono : N = Polynomial.C (N.coeff k) * Polynomial.X ^ k := by
    ext i
    rw [coeff_C_mul, coeff_X_pow]
    by_cases hik : i = k
    · subst hik; simp
    · rw [hNzero i hik]; simp [hik]
  set cN := N.coeff k with hcNdef
  refine ⟨cN, ?_⟩
  rw [hveq, hNmono, map_mul, ← ratFunc_algebraMap_eq_algebraMap_C,
    mul_div_assoc, div_self hXkA, mul_one]

end VDescent

/-! ## The `IsLiouville` assembly.

The `IsLiouville` packaging and the reduction `Prop`s; the exp-specific pole-matching content is
isolated in `ExpFDataReduction` / `ExpPoleMatching`. -/

section FieldObligations

variable {F : Type*} [Field F] [Differential F] [CharZero F]

open RatFunc

/-- The exp F-data reduction: any representation `a = ∑ cᵢ logDeriv wᵢ + v′` of `a ∈ F` can be
re-expressed with the logarithms' arguments and the `v`-term already in `F`. -/
def ExpFDataReduction (u : F) : Prop :=
  letI := expDifferential u
  letI := expDifferentialAlgebra u
  ∀ (a : F) (ι : Type) [Fintype ι] (c : ι → F), (∀ x, (c x)′ = 0) →
    ∀ (w : ι → RatFunc F) (v : RatFunc F),
      algebraMap F (RatFunc F) a = ∑ x, algebraMap F (RatFunc F) (c x) * logDeriv (w x) + v′ →
      ∃ (w₀ : ι → F) (v₀ : F),
        algebraMap F (RatFunc F) a
          = ∑ x, algebraMap F (RatFunc F) (c x) * logDeriv (algebraMap F (RatFunc F) (w₀ x))
              + (algebraMap F (RatFunc F) v₀)′

/-- The exp `π≠X` pole-matching residual: any representation `a = ∑ cᵢ logDeriv wᵢ + v′` can be
rewritten with `F`-valued logarithm arguments `w₀` and a corrected `v₀` with `v₀′ ∈ F`. -/
def ExpPoleMatching (u : F) : Prop :=
  letI := expDifferential u
  letI := expDifferentialAlgebra u
  ∀ (a : F) (ι : Type) [Fintype ι] (c : ι → F), (∀ x, (c x)′ = 0) →
    ∀ (w : ι → RatFunc F) (v : RatFunc F),
      algebraMap F (RatFunc F) a = ∑ x, algebraMap F (RatFunc F) (c x) * logDeriv (w x) + v′ →
      ∃ (w₀ : ι → F) (v₀ : RatFunc F),
        (algebraMap F (RatFunc F) a
          = ∑ x, algebraMap F (RatFunc F) (c x) * logDeriv (algebraMap F (RatFunc F) (w₀ x)) + v₀′)
        ∧ v₀′ ∈ (algebraMap F (RatFunc F)).range

/-- `ExpFDataReduction` follows from `ExpPoleMatching` via the `v`-term reduction. -/
theorem expFDataReduction_of_poleMatching (u : F) (hnd : NondegenerateExp u)
    (hpm : ExpPoleMatching u) : ExpFDataReduction u := by
  letI := expDifferential u
  letI := expDifferentialAlgebra u
  intro a ι _ c hc w v h
  obtain ⟨w₀, v₁, h₁, hv₁⟩ := hpm a ι c hc w v h
  obtain ⟨v₀, hv₀⟩ := expDeriv_mem_range_imp_mem_range u hnd hv₁
  exact ⟨w₀, v₀, by rw [h₁, hv₀]⟩

omit [CharZero F] in
/-- `ExpFDataReduction u` yields `IsLiouville F (RatFunc F)`. -/
theorem isLiouville_of_expFDataReduction (u : F) (hred : ExpFDataReduction u) :
    letI := expDifferential u
    letI := expDifferentialAlgebra u
    IsLiouville F (RatFunc F) := by
  letI := expDifferential u
  letI := expDifferentialAlgebra u
  refine ⟨fun a ι _ c hc w v h => ?_⟩
  obtain ⟨w₀, v₀, h₀⟩ := hred a ι c hc w v h
  exact isLiouville_conclusion_of_ratFuncData a ι c hc w₀ v₀ h₀

/-- `ExpPoleMatching u` (with `NondegenerateExp u`) yields `IsLiouville F (RatFunc F)`. -/
theorem isLiouville_of_expPoleMatching (u : F) (hnd : NondegenerateExp u)
    (hpm : ExpPoleMatching u) :
    letI := expDifferential u
    letI := expDifferentialAlgebra u
    IsLiouville F (RatFunc F) :=
  isLiouville_of_expFDataReduction u (expFDataReduction_of_poleMatching u hnd hpm)

end FieldObligations



end DeepWiki.SymbolicIntegration.LiouvilleExp
