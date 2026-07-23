import Mathlib.FieldTheory.Differential.Liouville
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Tactic
import DeepWiki.SymbolicIntegration.DifferentialAlgebra.FractionField
import DeepWiki.Algebra.RatFuncEmbedding
import DeepWiki.SymbolicIntegration.LiouvilleRatFuncData

/-! # The transcendental logarithmic Liouville extension

The transcendental logarithmic case of Liouville's theorem: the simple transcendental logarithmic
extension `F(t) = RatFunc F` with `t' = u'/u = logDeriv u` (`t = log u`, `u ∈ F`) is Liouville over
`F`, conditional on the non-degeneracy `NondegenerateLog u` (`log u ∉ F`).  Builds the log-monomial
derivation on `RatFunc F` via the quotient-rule fraction-field extension and derives
`IsLiouville F (RatFunc F)`.
-/

open scoped Differential
open Polynomial Differential

namespace DeepWiki.SymbolicIntegration.LiouvilleLog

section PolynomialSetup

variable {F : Type*} [Field F] [Differential F]

/-- The log-monomial coefficient `c = logDeriv u = u'/u`; `t' = c` for `t = log u`. -/
noncomputable abbrev logCoeff (u : F) : F := logDeriv u

/-- The log-monomial derivation on `F[t]` with `t' = u'/u`: `Differential.implicitDeriv (C (logDeriv u))`. -/
noncomputable def logDerivPoly (u : F) : Derivation ℤ F[X] F[X] :=
  Differential.implicitDeriv (C (logCoeff u))

/-- `F[t]` as a `Differential` ring under the log-monomial derivation `t' = u'/u`. -/
@[reducible]
noncomputable def logDifferentialPoly (u : F) : Differential F[X] :=
  ⟨logDerivPoly u⟩

/-- On `F[t]` with `t' = u'/u`, `t' = C (u'/u)` (the log-monomial defining equation, `t = log u`). -/
@[simp]
lemma logDerivPoly_X (u : F) : logDerivPoly u (X : F[X]) = C (logCoeff u) := by
  simp [logDerivPoly]

/-- On `F[t]`, the derivation sends a constant `C b` to `C b'` (it extends `F`'s derivation). -/
@[simp]
lemma logDerivPoly_C (u : F) (b : F) : logDerivPoly u (C b) = C b′ := by
  simp [logDerivPoly]

/-- The log-monomial derivation makes `F[t]` a `DifferentialAlgebra F F[t]` (extends `F`). -/
lemma logDerivPoly_differentialAlgebra (u : F) :
    letI := logDifferentialPoly u
    DifferentialAlgebra F F[X] := by
  letI := logDifferentialPoly u
  refine ⟨fun a => ?_⟩
  change logDerivPoly u (C a) = C a′
  simp

/-- Coefficient formula for the log-monomial derivation:
`(D p).coeff i = (p.coeff i)' + (u'/u)·(i+1)·p.coeff (i+1)`. -/
lemma coeff_logDerivPoly (u : F) (p : F[X]) (i : ℕ) :
    (logDerivPoly u p).coeff i
      = (p.coeff i)′ + logCoeff u * ((i + 1) * p.coeff (i + 1)) := by
  simp only [logDerivPoly, implicitDeriv, Derivation.coe_add, Pi.add_apply,
    Derivation.coe_smul, Pi.smul_apply, Derivation.restrictScalars_apply,
    derivative'_apply, coeff_add, coeff_mapCoeffs, smul_eq_mul, coeff_C_mul,
    coeff_derivative]
  ring

/-- The log-monomial derivation does not raise `t`-degree: `natDegree (D p) ≤ natDegree p`. -/
lemma natDegree_logDerivPoly_le (u : F) (p : F[X]) :
    (logDerivPoly u p).natDegree ≤ p.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [coeff_logDerivPoly]
  have h1 : p.coeff i = 0 := coeff_eq_zero_of_natDegree_lt hi
  have h2 : p.coeff (i + 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (le_of_lt hi) (Nat.lt_succ_self i))
  rw [h1, h2]
  simp

/-- At the top `t`-degree the monomial part vanishes:
`(D p).coeff (deg p) = (leadingCoeff p)'`. -/
lemma coeff_natDegree_logDerivPoly (u : F) (p : F[X]) :
    (logDerivPoly u p).coeff p.natDegree = (p.leadingCoeff)′ := by
  rw [coeff_logDerivPoly]
  have h : p.coeff (p.natDegree + 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _)
  rw [h, leadingCoeff]
  simp

/-- A constant of `F` with `b' = 0` is annihilated in `F[t]`: `D (C b) = 0`. -/
lemma logDerivPoly_C_of_deriv_eq_zero (u : F) {b : F} (hb : b′ = 0) :
    logDerivPoly u (C b) = 0 := by
  rw [logDerivPoly_C, hb, map_zero]

/-! ### No new constants on `F[t]`

Polynomial-layer facts that a `t`-constant is a single `F`-constant. -/

/-- `t`-constant has `F`-constant `t`-leading coefficient: `D p = 0 ⟹ (leadingCoeff p)' = 0`. -/
lemma leadingCoeff_deriv_eq_zero_of_logDerivPoly_eq_zero (u : F) {p : F[X]}
    (h : logDerivPoly u p = 0) : (p.leadingCoeff)′ = 0 := by
  have := coeff_natDegree_logDerivPoly u p
  rw [h, coeff_zero] at this
  exact this.symm

/-- A `t`-constant of `t`-degree `0` is a single `F`-constant `C b` with `b' = 0`. -/
lemma eq_C_of_logDerivPoly_eq_zero_of_natDegree_eq_zero (u : F) {p : F[X]}
    (h : logDerivPoly u p = 0) (hdeg : p.natDegree = 0) :
    ∃ b : F, p = C b ∧ b′ = 0 := by
  refine ⟨p.coeff 0, Polynomial.eq_C_of_natDegree_eq_zero hdeg, ?_⟩
  have := coeff_logDerivPoly u p 0
  rw [h, coeff_zero] at this
  have hc1 : p.coeff 1 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  rw [hc1] at this
  simpa using this.symm

/-- The no-degree-drop condition: given `logDeriv u ≠ 0`, every `t`-constant has `t`-degree `0`. -/
def NoDegreeDropObligation (u : F) : Prop :=
  logDeriv u ≠ 0 →
    ∀ {p : F[X]}, logDerivPoly u p = 0 → p.natDegree = 0

/-- Given `NoDegreeDropObligation` and `logDeriv u ≠ 0`, a `t`-constant `p` is a single `C b` with `b' = 0`. -/
lemma eq_C_of_logDerivPoly_eq_zero (u : F) (hndd : NoDegreeDropObligation u)
    (hu : logDeriv u ≠ 0) {p : F[X]} (h : logDerivPoly u p = 0) :
    ∃ b : F, p = C b ∧ b′ = 0 :=
  eq_C_of_logDerivPoly_eq_zero_of_natDegree_eq_zero u h (hndd hu h)

/-! ### Pole counting

`logDeriv` of a monic `t`-polynomial `π` is a proper rational function `(D π)/π` in `t`, so it
contributes a genuine `t`-pole. -/

/-- `logDeriv` of a monic `t`-polynomial is proper: for monic `p` with `deg p ≥ 1`,
`natDegree (D p) < natDegree p`. -/
lemma natDegree_logDerivPoly_lt_of_monic (u : F) {p : F[X]} (hm : p.Monic)
    (hdeg : 1 ≤ p.natDegree) : (logDerivPoly u p).natDegree < p.natDegree := by
  rcases lt_or_eq_of_le (natDegree_logDerivPoly_le u p) with h | h
  · exact h
  · exfalso
    have htop : (logDerivPoly u p).coeff p.natDegree = 0 := by
      rw [coeff_natDegree_logDerivPoly, hm.leadingCoeff]; simp
    by_cases hz : logDerivPoly u p = 0
    · rw [hz, natDegree_zero] at h; omega
    · have hlc : (logDerivPoly u p).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hz
      rw [leadingCoeff, h] at hlc
      exact hlc htop

/-- Log-monomial derivative of a monomial:
`D (C b · tⁿ) = C b' · tⁿ + C b · C (u'/u) · n · tⁿ⁻¹`. -/
lemma logDerivPoly_monomial_eq (u : F) (n : ℕ) (b : F) :
    logDerivPoly u (C b * X ^ n)
      = C b′ * X ^ n + C b * C (logCoeff u) * (n : F[X]) * X ^ (n - 1) := by
  rw [Derivation.leibniz, logDerivPoly_C]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · rw [Derivation.leibniz_pow, logDerivPoly_X, nsmul_eq_mul]
    ring

/-- Pole order drops by at most one: `q^n ∣ p ⟹ q^(n-1) ∣ D p`. -/
lemma pow_sub_one_dvd_logDerivPoly (u : F) {p q : F[X]} {n : ℕ} (hdvd : q ^ n ∣ p) :
    q ^ (n - 1) ∣ logDerivPoly u p := by
  obtain ⟨r, rfl⟩ := hdvd
  -- `q^(n-1) ∣ D(q^n)` directly from `leibniz_pow` (`D(q^n) = ↑n * (q^(n-1) * D q)`).
  have hpn : q ^ (n - 1) ∣ logDerivPoly u (q ^ n) := by
    rw [Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul]
    exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _
  -- `q^(n-1) ∣ q^n` (so the `q^n · D r` summand is divisible).
  have hpow : q ^ (n - 1) ∣ q ^ n := pow_dvd_pow q (Nat.sub_le n 1)
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  exact dvd_add (dvd_mul_of_dvd_left hpow _) (dvd_mul_of_dvd_right hpn _)

/-- Log-monomial derivative of `q^k · m` factors a `q^(k-1)`:
`D(q^k · m) = q^(k-1) · (k · (D q) · m + q · D m)` for `k ≥ 1`. -/
lemma logDerivPoly_pow_mul (u : F) {q m : F[X]} {k : ℕ} (hk : 1 ≤ k) :
    logDerivPoly u (q ^ k * m)
      = q ^ (k - 1) * ((k : F[X]) * logDerivPoly u q * m + q * logDerivPoly u m) := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, Derivation.leibniz_pow, nsmul_eq_mul,
    smul_eq_mul]
  have hqk : q ^ k = q ^ (k - 1) * q := by
    rw [← pow_succ]; congr 1; omega
  rw [hqk]; ring

/-- Exact strict pole-order drop: if `q ∤ D q`, `q` irreducible, `q^k ∣∣ p` (`k ≥ 1`),
then `q^k ∤ D p`. -/
lemma not_pow_dvd_logDerivPoly_of_exact [CharZero F] (u : F) {p q : F[X]} {k : ℕ}
    (hq : Irreducible q) (hDq : ¬ q ∣ logDerivPoly u q) (hk : 1 ≤ k)
    (hdvd : q ^ k ∣ p) (hndvd : ¬ q ^ (k + 1) ∣ p) : ¬ q ^ k ∣ logDerivPoly u p := by
  obtain ⟨m, rfl⟩ := hdvd
  -- `q ∤ m` (else `q^(k+1) ∣ q^k·m`).
  have hqm : ¬ q ∣ m := by
    rintro ⟨m', rfl⟩
    exact hndvd ⟨m', by rw [pow_succ]; ring⟩
  rw [logDerivPoly_pow_mul u (q := q) (m := m) hk]
  -- `q^k = q^(k-1)·q`; cancel `q^(k-1)` to reduce to `q ∤ (k·Dq·m + q·Dm)`.
  have hqk : q ^ k = q ^ (k - 1) * q := by rw [← pow_succ]; congr 1; omega
  rw [hqk]
  intro hdvd'
  have hcancel : q ∣ ((k : F[X]) * logDerivPoly u q * m + q * logDerivPoly u m) :=
    (mul_dvd_mul_iff_left (pow_ne_zero (k - 1) hq.ne_zero)).mp hdvd'
  -- `q ∣ q·Dm`, so `q ∣ k·Dq·m`; `q` prime divides none of `↑k`, `Dq`, `m`.
  have hk_part : q ∣ (k : F[X]) * logDerivPoly u q * m :=
    (dvd_add_right (dvd_mul_right q (logDerivPoly u m))).mp (by rwa [add_comm] at hcancel)
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

/-- Exact pole-order drop as an `emultiplicity` equality: for irreducible `q` with `q ∤ D q`,
`emultiplicity q p = k` (`k ≥ 1`) gives `emultiplicity q (D p) = k − 1`. -/
lemma emultiplicity_logDerivPoly_eq [CharZero F] (u : F) {p q : F[X]} {k : ℕ}
    (hq : Irreducible q) (hDq : ¬ q ∣ logDerivPoly u q) (hk : 1 ≤ k)
    (hmult : emultiplicity q p = (k : ℕ∞)) :
    emultiplicity q (logDerivPoly u p) = ((k - 1 : ℕ) : ℕ∞) := by
  -- `q^k ∣ p` and `q^(k+1) ∤ p` from the multiplicity equality.
  have hdvd : q ^ k ∣ p := pow_dvd_of_le_emultiplicity (by rw [hmult])
  have hndvd : ¬ q ^ (k + 1) ∣ p := by
    rw [← emultiplicity_lt_iff_not_dvd, hmult]; exact_mod_cast Nat.lt_succ_self k
  -- `q^(k-1) ∣ D p` (lower bound) and `q^k ∤ D p` (strict upper bound).
  have hlo : ((k - 1 : ℕ) : ℕ∞) ≤ emultiplicity q (logDerivPoly u p) :=
    le_emultiplicity_of_pow_dvd (pow_sub_one_dvd_logDerivPoly u hdvd)
  have hhi : emultiplicity q (logDerivPoly u p) < (k : ℕ∞) :=
    emultiplicity_lt_iff_not_dvd.mpr (not_pow_dvd_logDerivPoly_of_exact u hq hDq hk hdvd hndvd)
  -- `k - 1 ≤ … < k = (k-1)+1` forces `… = k - 1`.
  have hk1 : (k : ℕ∞) = ((k - 1 : ℕ) : ℕ∞) + 1 := by
    rw [← ENat.coe_one, ← Nat.cast_add]; congr 1; omega
  rw [hk1] at hhi
  exact le_antisymm ((ENat.lt_add_one_iff (ENat.coe_ne_top _)).mp hhi) hlo

/-- A monic `t`-factor `q` of positive degree with `D q ≠ 0` does not divide its own derivative: `¬ q ∣ D q`. -/
lemma not_dvd_logDerivPoly_of_natDegree_lt (u : F) {q : F[X]} (hm : q.Monic)
    (hdeg : 1 ≤ q.natDegree) (hDq : logDerivPoly u q ≠ 0) : ¬ q ∣ logDerivPoly u q := by
  intro hdvd
  have hlt := natDegree_logDerivPoly_lt_of_monic u hm hdeg
  have hle := Polynomial.natDegree_le_of_dvd hdvd hDq
  omega

/-- Non-degeneracy of the log monomial (`log u ∉ F`): no monic irreducible `t`-polynomial `π`
is annihilated by the log-monomial derivation (`D π ≠ 0`). -/
def NondegenerateLog (u : F) : Prop :=
  ∀ π : F[X], π.Monic → Irreducible π → logDerivPoly u π ≠ 0

/-- `NondegenerateLog u` forbids an `F`-antiderivative of `u'/u`: no `s ∈ F` has `s′ = logDeriv u`. -/
lemma not_isAntideriv_of_nondegenerateLog (u : F) (hnd : NondegenerateLog u) {s : F}
    (hs : s′ = logDeriv u) : False := by
  refine hnd (X - C s) (monic_X_sub_C s) (irreducible_X_sub_C s) ?_
  rw [map_sub, logDerivPoly_X, logDerivPoly_C, hs]
  simp

/-- The log dichotomy, degenerate side: over char `0`, failure of `NondegenerateLog u`
produces a base antiderivative of `u′/u` — the top-coefficient reading of the annihilated
monic irreducible. -/
lemma exists_antideriv_of_not_nondegenerateLog [CharZero F] (u : F)
    (h : ¬ NondegenerateLog u) : ∃ s : F, s′ = logDeriv u := by
  rw [NondegenerateLog] at h
  push Not at h
  obtain ⟨π, hm, hirr, hD0⟩ := h
  set m := π.natDegree with hmdef
  have hdeg : 1 ≤ m := hirr.natDegree_pos
  have hmF : (m : F) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcoeff := coeff_logDerivPoly u π (m - 1)
  rw [hD0, coeff_zero] at hcoeff
  have hsucc : m - 1 + 1 = m := by omega
  rw [hsucc, hm.coeff_natDegree] at hcoeff
  have hcast : ((m - 1 : ℕ) : F) + 1 = (m : F) := by
    rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]; ring
  rw [hcast, mul_one] at hcoeff
  refine ⟨-(π.coeff (m - 1)) / (m : F), ?_⟩
  have hmcast : Differential.deriv (m : F) = 0 := Derivation.map_natCast _ m
  rw [Differential.deriv.leibniz_div_const (-(π.coeff (m - 1))) (m : F) hmcast,
    smul_eq_mul, map_neg]
  rw [show (π.coeff (m - 1))′ = -((m : F) * logDeriv u) from by linear_combination -hcoeff]
  rw [neg_neg, ← mul_assoc, inv_mul_cancel₀ hmF, one_mul]

/-- Given `NondegenerateLog`, no monic `d` of positive `t`-degree is annihilated by `D`: `D d ≠ 0`. -/
lemma logDerivPoly_ne_zero_of_monic [CharZero F] (u : F) (hnd : NondegenerateLog u) {d : F[X]}
    (hm : d.Monic) (hdeg : 1 ≤ d.natDegree) : logDerivPoly u d ≠ 0 := by
  intro hDd
  set m := d.natDegree with hmdef
  have hmF : (m : F) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- Coefficient-`(m−1)` relation: `0 = (d.coeff (m−1))′ + (u'/u)·m·(d.coeff m)`, `d.coeff m = 1`.
  have hcoeff := coeff_logDerivPoly u d (m - 1)
  rw [hDd, coeff_zero] at hcoeff
  have hsucc : m - 1 + 1 = m := by omega
  rw [hsucc, hm.coeff_natDegree] at hcoeff
  have hcast : ((m - 1 : ℕ) : F) + 1 = (m : F) := by
    rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]; ring
  rw [hcast, mul_one] at hcoeff
  -- so `(d.coeff (m−1))′ = −m·(u'/u)`; set `s := −(d.coeff (m−1))/m`, then `s′ = u'/u`.
  refine not_isAntideriv_of_nondegenerateLog u hnd (s := -(d.coeff (m - 1)) / (m : F)) ?_
  have hmcast : Differential.deriv (m : F) = 0 := Derivation.map_natCast _ m
  rw [Differential.deriv.leibniz_div_const (-(d.coeff (m - 1))) (m : F) hmcast,
    smul_eq_mul, map_neg]
  rw [show (d.coeff (m - 1))′ = -((m : F) * logDeriv u) from by linear_combination -hcoeff]
  rw [neg_neg, ← mul_assoc, inv_mul_cancel₀ hmF, one_mul]

/-- Given `NondegenerateLog`, a monic `d` of positive `t`-degree does not divide its own derivative: `¬ d ∣ D d`. -/
lemma not_dvd_logDerivPoly_of_monic [CharZero F] (u : F) (hnd : NondegenerateLog u) {d : F[X]}
    (hm : d.Monic) (hdeg : 1 ≤ d.natDegree) : ¬ d ∣ logDerivPoly u d :=
  not_dvd_logDerivPoly_of_natDegree_lt u hm hdeg (logDerivPoly_ne_zero_of_monic u hnd hm hdeg)

/-- Given `NondegenerateLog`, `(D p).natDegree = 0 ⟹ p.natDegree ≤ 1`. -/
lemma natDegree_le_one_of_logDerivPoly_natDegree_eq_zero [CharZero F] (u : F)
    (hnd : NondegenerateLog u) {p : F[X]} (h : (logDerivPoly u p).natDegree = 0) :
    p.natDegree ≤ 1 := by
  by_contra hlt
  rw [not_le] at hlt
  set m := p.natDegree with hmdef
  have hm2 : 2 ≤ m := hlt
  have hlcne : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr (by
    intro h0; rw [h0] at hmdef; simp at hmdef; omega)
  -- Top coefficient is an `F`-constant: `(leadingCoeff p)′ = 0`.
  have hlc0 : (p.leadingCoeff)′ = 0 := by
    have htop := coeff_natDegree_logDerivPoly u p
    rw [← htop]
    exact coeff_eq_zero_of_natDegree_lt (by rw [h]; omega)
  -- Coefficient-`(m−1)` relation: `(p.coeff (m−1))′ = −m·(leadingCoeff p)·(u'/u)`.
  have hcoeff := coeff_logDerivPoly u p (m - 1)
  have hzero : (logDerivPoly u p).coeff (m - 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by rw [h]; omega)
  rw [hzero] at hcoeff
  have hsucc : m - 1 + 1 = m := by omega
  have hlc : p.coeff m = p.leadingCoeff := rfl
  rw [hsucc, hlc] at hcoeff
  have hcast : ((m - 1 : ℕ) : F) + 1 = (m : F) := by
    rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]; ring
  rw [hcast] at hcoeff
  -- `s := −p.coeff (m−1)/(m·leadingCoeff p)` has `s′ = u'/u`: contradiction.
  have hmlcne : (m : F) * p.leadingCoeff ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) hlcne
  have hmlc0 : Differential.deriv ((m : F) * p.leadingCoeff) = 0 := by
    rw [Derivation.leibniz, Derivation.map_natCast, hlc0, smul_zero, smul_zero, add_zero]
  refine not_isAntideriv_of_nondegenerateLog u hnd
    (s := -(p.coeff (m - 1)) / ((m : F) * p.leadingCoeff)) ?_
  rw [Differential.deriv.leibniz_div_const (-(p.coeff (m - 1))) ((m : F) * p.leadingCoeff) hmlc0,
    smul_eq_mul, map_neg]
  rw [show (p.coeff (m - 1))′ = -((m : F) * p.leadingCoeff * logDeriv u) from by
    linear_combination -hcoeff]
  rw [neg_neg, ← mul_assoc, inv_mul_cancel₀ hmlcne, one_mul]

/-- `NondegenerateLog u` forces `logDeriv u ≠ 0`. -/
lemma logDeriv_ne_zero_of_nondegenerateLog (u : F) (hnd : NondegenerateLog u) : logDeriv u ≠ 0 := by
  intro h0
  refine hnd X monic_X irreducible_X ?_
  rw [logDerivPoly_X]
  simp [logCoeff, h0]

-- Restatements pinning the log-monomial setup to its API-level equations.
-- `t' = u'/u`: the defining equation of the logarithmic monomial.
example (u : F) : logDerivPoly u (X : F[X]) = C (logDeriv u) := logDerivPoly_X u
-- The derivation on `F(t)` restricted to the linear monomial `b·t` (`b ∈ F`) is
-- `b'·t + b·(u'/u)`: the constant-field part plus the monomial part.
example (u b : F) :
    logDerivPoly u (C b * X) = C b′ * X + C b * C (logCoeff u) := by
  have := (logDerivPoly u).leibniz (C b) X
  simp only [logDerivPoly_C, logDerivPoly_X] at this
  rw [this]; ring
-- The coefficient formula is exactly `(D p).coeff i = (p.coeff i)' + (u'/u)·(i+1)·p.coeff (i+1)`.
example (u : F) (p : F[X]) (i : ℕ) :
    (logDerivPoly u p).coeff i
      = (p.coeff i)′ + logDeriv u * ((i + 1) * p.coeff (i + 1)) :=
  coeff_logDerivPoly u p i
-- `logDeriv` of a monic `t`-polynomial is proper (the pole-matching engine): `deg (D p) < deg p`.
example (u : F) {p : F[X]} (hm : p.Monic) (hdeg : 1 ≤ p.natDegree) :
    (logDerivPoly u p).natDegree < p.natDegree :=
  natDegree_logDerivPoly_lt_of_monic u hm hdeg
-- Pole order drops by at most one: `q^n ∣ p ⟹ q^(n-1) ∣ D p` (pure Leibniz, any derivation).
example (u : F) {p q : F[X]} {n : ℕ} (hdvd : q ^ n ∣ p) :
    q ^ (n - 1) ∣ logDerivPoly u p :=
  pow_sub_one_dvd_logDerivPoly u hdvd
-- A monic irreducible-degree factor does not divide its own derivative (strict pole increase),
-- provided `D q ≠ 0` (the transcendence input).
example (u : F) {q : F[X]} (hm : q.Monic) (hdeg : 1 ≤ q.natDegree)
    (hDq : logDerivPoly u q ≠ 0) : ¬ q ∣ logDerivPoly u q :=
  not_dvd_logDerivPoly_of_natDegree_lt u hm hdeg hDq
-- A `t`-constant has an `F`-constant `t`-leading coefficient.
example (u : F) {p : F[X]} (h : logDerivPoly u p = 0) : (p.leadingCoeff)′ = 0 :=
  leadingCoeff_deriv_eq_zero_of_logDerivPoly_eq_zero u h

/-! ### The `v`-term polynomial descent

Reducing the integral part `v` (with `v′ ∈ F`) to `F` on the polynomial layer. -/

/-- `(D p).natDegree = 0` and `p` positive degree ⟹ `(leadingCoeff p)′ = 0`. -/
lemma leadingCoeff_deriv_eq_zero_of_natDegree_logDerivPoly_le (u : F) {p : F[X]}
    (h : (logDerivPoly u p).natDegree = 0) (hdeg : 1 ≤ p.natDegree) :
    (p.leadingCoeff)′ = 0 := by
  have htop := coeff_natDegree_logDerivPoly u p
  rw [← htop]
  exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (le_of_eq h) hdeg)

/-- For `(D p).natDegree = 0` and `n := p.natDegree ≥ 2`, the sub-top coefficient satisfies
`(p.coeff (n−1))′ = − n · (leadingCoeff p) · logDeriv u`. -/
lemma deriv_coeff_predTop_of_natDegree_logDerivPoly_le (u : F) {p : F[X]}
    (h : (logDerivPoly u p).natDegree = 0) (hdeg : 2 ≤ p.natDegree) :
    (p.coeff (p.natDegree - 1))′
      = - ((p.natDegree : F) * (p.leadingCoeff * logDeriv u)) := by
  have hcoeff := coeff_logDerivPoly u p (p.natDegree - 1)
  have hlt : 0 < p.natDegree - 1 := by omega
  have hzero : (logDerivPoly u p).coeff (p.natDegree - 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (le_of_eq h) hlt)
  rw [hzero] at hcoeff
  have hsucc : p.natDegree - 1 + 1 = p.natDegree := by omega
  rw [hsucc] at hcoeff
  have hlc : p.coeff p.natDegree = p.leadingCoeff := rfl
  rw [hlc] at hcoeff
  have hcast : ((p.natDegree - 1 : ℕ) : F) + 1 = (p.natDegree : F) := by
    rw [Nat.cast_sub (by omega : 1 ≤ p.natDegree), Nat.cast_one]; ring
  rw [hcast] at hcoeff
  linear_combination -hcoeff

/-- The `v`-term polynomial condition: given `logDeriv u ≠ 0`, `(D p).natDegree = 0 ⟹ p.natDegree = 0`. -/
def PolyVReductionObligation (u : F) : Prop :=
  logDeriv u ≠ 0 →
    ∀ {p : F[X]}, (logDerivPoly u p).natDegree = 0 → p.natDegree = 0

/-- Given `PolyVReductionObligation` and `logDeriv u ≠ 0`, `(D p).natDegree = 0 ⟹ p = C b`. -/
lemma eq_C_of_natDegree_logDerivPoly_le (u : F) (hpv : PolyVReductionObligation u)
    (hu : logDeriv u ≠ 0) {p : F[X]} (h : (logDerivPoly u p).natDegree = 0) :
    ∃ b : F, p = C b :=
  ⟨p.coeff 0, Polynomial.eq_C_of_natDegree_eq_zero (hpv hu h)⟩

end PolynomialSetup

/-! ## The field extension `F(t) = RatFunc F`

`RatFunc F` with the log-monomial derivation as a differential field extension of `F`. -/

section FieldObligations

variable {F : Type*} [Field F] [Differential F] [CharZero F]

open RatFunc

/-- The `Differential (RatFunc F)` for the log monomial `t = log u` (`t' = u'/u`),
induced from `logDerivPoly u` by the fraction-field quotient rule. -/
@[reducible]
noncomputable def logDifferential (u : F) : Differential (RatFunc F) :=
  FractionRingDeriv.differentialOf (K := RatFunc F) (logDifferentialPoly u)

omit [CharZero F] in
/-- The log-monomial derivation on `RatFunc F` restricts to `logDerivPoly u` on the image of `F[t]`:
`(algebraMap F[t] (RatFunc F) p)′ = algebraMap F[t] (RatFunc F) (logDerivPoly u p)`. -/
theorem derivExtends (u : F) :
    letI := logDifferential u
    ∀ p : F[X], (algebraMap F[X] (RatFunc F) p)′
      = algebraMap F[X] (RatFunc F) (logDerivPoly u p) :=
  fun p => FractionRingDeriv.deriv_algebraMap (K := RatFunc F) (logDerivPoly u) p

omit [CharZero F] in
/-- Any `Differential (RatFunc F)` whose derivation restricts to `logDerivPoly u` on `F[t]` is a
`DifferentialAlgebra F (RatFunc F)`. -/
theorem differentialAlgebra_of_derivExtends [Differential (RatFunc F)] {u : F}
    (h : ∀ p : F[X], (algebraMap F[X] (RatFunc F) p)′
      = algebraMap F[X] (RatFunc F) (logDerivPoly u p)) :
    DifferentialAlgebra F (RatFunc F) where
  deriv_algebraMap a := by
    have hfac : (algebraMap F (RatFunc F)) a
        = algebraMap F[X] (RatFunc F) (C a) := by
      rw [IsScalarTower.algebraMap_eq F F[X] (RatFunc F)]
      simp [Polynomial.algebraMap_eq]
    rw [hfac, h (C a), logDerivPoly_C]
    rw [IsScalarTower.algebraMap_eq F F[X] (RatFunc F)]
    simp [Polynomial.algebraMap_eq]

omit [CharZero F] in
/-- `RatFunc F` with the log-monomial derivation is a `DifferentialAlgebra F (RatFunc F)`. -/
theorem logDifferentialAlgebra (u : F) :
    letI := logDifferential u
    DifferentialAlgebra F (RatFunc F) :=
  letI := logDifferential u
  differentialAlgebra_of_derivExtends (u := u) (derivExtends u)

omit [CharZero F] in
/-- In `RatFunc F`, `logDeriv (algebraMap p) = algebraMap (logDerivPoly u p) / algebraMap p`. -/
theorem logDeriv_algebraMap_eq (u : F) (p : F[X]) :
    letI := logDifferential u
    logDeriv (algebraMap F[X] (RatFunc F) p)
      = algebraMap F[X] (RatFunc F) (logDerivPoly u p) / algebraMap F[X] (RatFunc F) p := by
  letI := logDifferential u
  unfold logDeriv
  rw [derivExtends u p]

omit [CharZero F] in
/-- For monic `p` of `t`-degree `≥ 1`, `logDeriv (algebraMap p) = algebraMap (D p) / algebraMap p`
is a proper fraction in `t` (`natDegree (D p) < natDegree p`). -/
theorem logDeriv_monic_proper (u : F) {p : F[X]} (hm : p.Monic) (hdeg : 1 ≤ p.natDegree) :
    letI := logDifferential u
    logDeriv (algebraMap F[X] (RatFunc F) p)
        = algebraMap F[X] (RatFunc F) (logDerivPoly u p) / algebraMap F[X] (RatFunc F) p ∧
      (logDerivPoly u p).natDegree < p.natDegree :=
  letI := logDifferential u
  ⟨logDeriv_algebraMap_eq u p, natDegree_logDerivPoly_lt_of_monic u hm hdeg⟩

/-! ### The `v`-term reduction on `RatFunc F`

Lifting the polynomial `v ∈ F` descent to the fraction field. -/

/-- The rational-to-polynomial condition: given `logDeriv u ≠ 0`, if `v′` is a polynomial then `v` is. -/
def RationalToPolyObligation (u : F) : Prop :=
  letI := logDifferential u
  logDeriv u ≠ 0 →
    ∀ v : RatFunc F, v′ ∈ (algebraMap F[X] (RatFunc F)).range →
      v ∈ (algebraMap F[X] (RatFunc F)).range

/-- `RationalToPolyObligation` holds under `NondegenerateLog u`. -/
theorem rationalToPolyObligation_of_nondegenerateLog (u : F) (hnd : NondegenerateLog u) :
    RationalToPolyObligation u := by
  letI := logDifferential u
  intro _hu v hvpoly
  -- `v = 0` is a polynomial trivially.
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
  -- `v = ↑n/↑d`, and `logDeriv v = ↑(D n)/↑n − ↑(D d)/↑d` (split + `logDeriv_algebraMap_eq`).
  have hveq : v = algebraMap F[X] (RatFunc F) n / algebraMap F[X] (RatFunc F) d := by
    rw [← RatFunc.num_div_denom v, ← hndef, ← hddef]
  have hlogv : logDeriv v
      = algebraMap F[X] (RatFunc F) (logDerivPoly u n) / algebraMap F[X] (RatFunc F) n
        - algebraMap F[X] (RatFunc F) (logDerivPoly u d) / algebraMap F[X] (RatFunc F) d := by
    have hsplit : logDeriv v = logDeriv (algebraMap F[X] (RatFunc F) n)
        - logDeriv (algebraMap F[X] (RatFunc F) d) := by
      conv_lhs => rw [hveq]
      exact logDeriv_div _ _ hnA hdA
    rw [hsplit, logDeriv_algebraMap_eq u n, logDeriv_algebraMap_eq u d]
  -- `v′ = v · logDeriv v` (definition), so `↑P = (↑n/↑d)·(↑(Dn)/↑n − ↑(Dd)/↑d)`.
  have hv'eq : v′ = v * logDeriv v := by
    rw [logDeriv, mul_div_cancel₀ _ hv0]
  -- Clear denominators to a polynomial identity `P·d² = d·(Dn) − n·(Dd)`.
  have hkey : algebraMap F[X] (RatFunc F) (P * (d * d))
      = algebraMap F[X] (RatFunc F) (d * logDerivPoly u n - n * logDerivPoly u d) := by
    have hPv : algebraMap F[X] (RatFunc F) P = v * logDeriv v := by rw [hP, hv'eq]
    rw [hlogv, hveq] at hPv
    rw [map_mul, map_mul, map_sub, map_mul, map_mul]
    field_simp at hPv ⊢
    linear_combination hPv
  have hkeyP : P * (d * d) = d * logDerivPoly u n - n * logDerivPoly u d :=
    FaithfulSMul.algebraMap_injective F[X] (RatFunc F) hkey
  -- `d ∣ n·(D d)`, so by coprimality `d ∣ D d`.
  have hdvd_nDd : d ∣ n * logDerivPoly u d := by
    have hrw : n * logDerivPoly u d = d * logDerivPoly u n - P * (d * d) := by
      linear_combination hkeyP
    rw [hrw]
    exact Dvd.dvd.sub (dvd_mul_right d _) (dvd_mul_of_dvd_right (dvd_mul_right d d) P)
  have hdvd_Dd : d ∣ logDerivPoly u d := hcop.symm.dvd_of_dvd_mul_left hdvd_nDd
  -- If `deg d ≥ 1` this contradicts the strict pole increase; so `deg d = 0`, `d = 1`, `v = ↑n`.
  have hdeg0 : d.natDegree = 0 := by
    by_contra hdeg
    exact not_dvd_logDerivPoly_of_monic u hnd hdmon (Nat.one_le_iff_ne_zero.mpr hdeg) hdvd_Dd
  have hd1 : d = 1 := eq_one_of_monic_natDegree_zero hdmon hdeg0
  refine ⟨n, ?_⟩
  rw [hveq, hd1, map_one, div_one]

/-- Given `NondegenerateLog`, `v′ ∈ F ⟹ v = v₀ + b·t` with `v₀, b ∈ F` and `b′ = 0`
(the surviving linear term `b·t = b·log u` is a new logarithm). -/
theorem deriv_mem_range_imp_linear (u : F) (hnd : NondegenerateLog u) {v : RatFunc F}
    (hv : letI := logDifferential u; v′ ∈ (algebraMap F (RatFunc F)).range) :
    letI := logDifferential u
    ∃ (v₀ b : F), b′ = 0 ∧
      v = algebraMap F (RatFunc F) v₀
        + algebraMap F (RatFunc F) b * algebraMap F[X] (RatFunc F) X := by
  letI := logDifferential u
  -- `v′ ∈ F ⊆ F[t]`, so by the pole descent `v = ↑p`.
  obtain ⟨b, hb⟩ := hv
  have hvpoly : v′ ∈ (algebraMap F[X] (RatFunc F)).range := by
    refine ⟨Polynomial.C b, ?_⟩
    rw [← ratFunc_algebraMap_eq_algebraMap_C, hb]
  obtain ⟨p, hp⟩ := rationalToPolyObligation_of_nondegenerateLog u hnd
    (logDeriv_ne_zero_of_nondegenerateLog u hnd) v hvpoly
  -- `D p` is the constant `C b`, so `(D p).natDegree = 0` and `p.natDegree ≤ 1`.
  have hDpCb : logDerivPoly u p = Polynomial.C b :=
    FaithfulSMul.algebraMap_injective F[X] (RatFunc F) (by
      rw [← derivExtends u p, hp, ← hb, ratFunc_algebraMap_eq_algebraMap_C])
  have hdeg0 : (logDerivPoly u p).natDegree = 0 := by rw [hDpCb]; exact natDegree_C b
  have hple1 : p.natDegree ≤ 1 := natDegree_le_one_of_logDerivPoly_natDegree_eq_zero u hnd hdeg0
  -- The linear coefficient is a constant: `(p.coeff 1)′ = 0` (index-`1` coefficient relation).
  have hb1 : (p.coeff 1)′ = 0 := by
    have hcoeff := coeff_logDerivPoly u p 1
    rw [hDpCb] at hcoeff
    have hc2 : p.coeff 2 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    rw [Polynomial.coeff_C] at hcoeff
    simp only [show (1 : ℕ) ≠ 0 by decide, if_false] at hcoeff
    rw [hc2] at hcoeff
    simpa using hcoeff.symm
  -- `p = C (p.coeff 1)·X + C (p.coeff 0)` (degree `≤ 1`), so `v = ↑(p.coeff 0) + ↑(p.coeff 1)·t`.
  refine ⟨p.coeff 0, p.coeff 1, hb1, ?_⟩
  conv_lhs => rw [← hp, Polynomial.eq_X_add_C_of_natDegree_le_one hple1, map_add, map_mul,
    ← ratFunc_algebraMap_eq_algebraMap_C, ← ratFunc_algebraMap_eq_algebraMap_C]
  rw [add_comm]

/-- A nondegenerate log monomial introduces no new constants in `RatFunc F`. -/
theorem containConstants_of_nondegenerateLog (u : F) (hnd : NondegenerateLog u) :
    letI := logDifferential u
    Differential.ContainConstants F (RatFunc F) := by
  letI := logDifferential u
  letI := logDifferentialAlgebra u
  refine ⟨fun {x} hx => ?_⟩
  -- `x′ = 0 ∈ range`, so the corrected `v`-reduction gives `x = v₀ + b·(log u)`, with `b′ = 0`.
  have hxrange : x′ ∈ (algebraMap F (RatFunc F)).range := by rw [hx]; exact ⟨0, by rw [map_zero]⟩
  obtain ⟨v₀, b, hb0, hxeq⟩ := deriv_mem_range_imp_linear u hnd hxrange
  have hfa : ∀ a : F,
      algebraMap F (RatFunc F) a = algebraMap F[X] (RatFunc F) (Polynomial.C a) := by
    intro a; rw [ratFunc_algebraMap_eq_algebraMap_C]
  -- Rewrite `x` as the image of the degree-`≤ 1` polynomial `C v₀ + C b·X`.
  have hxP :
      x = algebraMap F[X] (RatFunc F) (Polynomial.C v₀ + Polynomial.C b * Polynomial.X) := by
    rw [hxeq, hfa v₀, hfa b, map_add, map_mul]
  -- `D (C v₀ + C b·X) = C v₀′ + C b · C (u'/u)`.
  have hDp :
      logDerivPoly u (Polynomial.C v₀ + Polynomial.C b * Polynomial.X) =
        Polynomial.C v₀′ + Polynomial.C b * Polynomial.C (logCoeff u) := by
    rw [map_add, Derivation.leibniz, logDerivPoly_C, logDerivPoly_C, logDerivPoly_X, hb0]
    simp only [map_zero, smul_eq_mul, mul_zero, add_zero]
  have hxder :
      x′ = algebraMap F[X] (RatFunc F)
        (Polynomial.C v₀′ + Polynomial.C b * Polynomial.C (logCoeff u)) := by
    rw [hxP, derivExtends u (Polynomial.C v₀ + Polynomial.C b * Polynomial.X), hDp]
  -- `x′ = 0`, so the polynomial derivative is `0`, i.e. `v₀′ + b·(u'/u) = 0`.
  rw [hx] at hxder
  have hpoly0 : Polynomial.C v₀′ + Polynomial.C b * Polynomial.C (logCoeff u) = 0 :=
    FaithfulSMul.algebraMap_injective F[X] (RatFunc F) (by rw [← hxder, map_zero])
  have hF0 : v₀′ + b * logCoeff u = 0 := by
    have h := hpoly0; rw [← C_mul, ← map_add] at h; exact C_eq_zero.mp h
  -- If `b ≠ 0`, `-v₀/b` is a `F`-antiderivative of `u'/u`; otherwise `x = v₀ ∈ F`.
  have hbeq0 : b = 0 := by
    by_contra hbne
    refine not_isAntideriv_of_nondegenerateLog u hnd (s := -v₀ / b) ?_
    rw [Differential.deriv.leibniz_div_const (-v₀) b hb0, smul_eq_mul, map_neg]
    field_simp; linear_combination -hF0
  exact ⟨v₀, by rw [hxP, hbeq0, map_zero, zero_mul, add_zero, ← hfa v₀]⟩

omit [CharZero F] in
/-- The range-reduction residuals turning `v′ ∈ F` into `v ∈ F`. -/
structure IsLogRangeReduction (u : F) : Prop where
  /-- Derivatives in the polynomial range force the rational function into the polynomial range. -/
  rationalToPoly : RationalToPolyObligation u
  /-- Degree-zero log-polynomial derivatives are constant polynomials. -/
  polyReduction : PolyVReductionObligation u
  /-- The logarithmic derivative of the defining element is nonzero. -/
  logDeriv_ne_zero : logDeriv u ≠ 0

omit [CharZero F] in
/-- Given `IsLogRangeReduction`, `v′ ∈ F ⟹ v ∈ F` on `RatFunc F`. -/
theorem mem_range_of_deriv_mem_range (u : F) (hrange : IsLogRangeReduction u) :
    letI := logDifferential u
    ∀ {v : RatFunc F}, v′ ∈ (algebraMap F (RatFunc F)).range →
      v ∈ (algebraMap F (RatFunc F)).range := by
  letI := logDifferential u
  intro v hv
  -- `v′ ∈ F ⊆ F[t]`, so by the partial-fraction obligation `v` is a polynomial image.
  obtain ⟨b, hb⟩ := hv
  have hvpoly : v′ ∈ (algebraMap F[X] (RatFunc F)).range := by
    refine ⟨Polynomial.C b, ?_⟩
    rw [← ratFunc_algebraMap_eq_algebraMap_C, hb]
  obtain ⟨p, hp⟩ := hrange.rationalToPoly hrange.logDeriv_ne_zero v hvpoly
  -- Identify `D p = C b` via injectivity, hence `(D p).natDegree = 0`.
  have hderiv : algebraMap F[X] (RatFunc F) (logDerivPoly u p)
      = algebraMap F[X] (RatFunc F) (Polynomial.C b) := by
    rw [← derivExtends u p, hp, ← hb, ratFunc_algebraMap_eq_algebraMap_C]
  have hDpCb : logDerivPoly u p = Polynomial.C b :=
    FaithfulSMul.algebraMap_injective F[X] (RatFunc F) hderiv
  have hdeg0 : (logDerivPoly u p).natDegree = 0 := by rw [hDpCb]; exact natDegree_C b
  -- Descend `p` to a constant `C b₀` by the polynomial obligation; conclude `v ∈ F`.
  obtain ⟨b₀, hb₀⟩ :=
    eq_C_of_natDegree_logDerivPoly_le u hrange.polyReduction hrange.logDeriv_ne_zero hdeg0
  rw [← hp]
  exact (ratFunc_algebraMap_poly_mem_range_iff p).mpr ⟨b₀, hb₀⟩

/-! ### The single-logarithm case

`a = c · logDeriv w + v′` with `a ∈ F`: decomposing `logDeriv w` into its numerator and denominator
factors' simple `t`-poles. -/

omit [CharZero F] in
/-- For `w ≠ 0`, `logDeriv w = logDeriv(algebraMap (num w)) − logDeriv(algebraMap (denom w))`. -/
theorem logDeriv_eq_num_sub_denom (u : F) {w : RatFunc F} (hw : w ≠ 0) :
    letI := logDifferential u
    logDeriv w = logDeriv (algebraMap F[X] (RatFunc F) (RatFunc.num w))
        - logDeriv (algebraMap F[X] (RatFunc F) (RatFunc.denom w)) := by
  letI := logDifferential u
  have hnum : algebraMap F[X] (RatFunc F) (RatFunc.num w) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (RatFunc.num_ne_zero hw)
  have hden : algebraMap F[X] (RatFunc F) (RatFunc.denom w) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero w)
  conv_lhs => rw [← RatFunc.num_div_denom w]
  exact logDeriv_div _ _ hnum hden

omit [CharZero F] in
/-- For `p = ∏ⱼ (g j)^(e j)` with each `g j ≠ 0`,
`logDeriv (algebraMap p) = ∑ⱼ (e j) · logDeriv (algebraMap (g j))`. -/
theorem logDeriv_algebraMap_prod_pow (u : F) {ι : Type*} (s : Finset ι) (g : ι → F[X])
    (e : ι → ℕ) (hg : ∀ j ∈ s, g j ≠ 0) :
    letI := logDifferential u
    logDeriv (algebraMap F[X] (RatFunc F) (∏ j ∈ s, (g j) ^ (e j)))
      = ∑ j ∈ s, (e j : RatFunc F) * logDeriv (algebraMap F[X] (RatFunc F) (g j)) := by
  letI := logDifferential u
  have hne : ∀ j ∈ s, algebraMap F[X] (RatFunc F) ((g j) ^ (e j)) ≠ 0 :=
    fun j hj => RatFunc.algebraMap_ne_zero (pow_ne_zero _ (hg j hj))
  rw [map_prod, logDeriv_prod ι s _ hne]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_pow, logDeriv_pow]

omit [CharZero F] in
/-- For `p ≠ 0`, `logDeriv (algebraMap p) = logDeriv (algebraMap (C p.leadingCoeff)) +
∑_{π ∈ (normalizedFactors p).toFinset} (count π) · logDeriv (algebraMap π)`
over the distinct monic irreducible factors `π`. -/
theorem logDeriv_algebraMap_eq_unit_add_sum [DecidableEq F] (u : F) {p : F[X]} (hp : p ≠ 0) :
    letI := logDifferential u
    logDeriv (algebraMap F[X] (RatFunc F) p)
      = logDeriv (algebraMap F[X] (RatFunc F) (Polynomial.C p.leadingCoeff))
        + ∑ π ∈ (UniqueFactorizationMonoid.normalizedFactors p).toFinset,
            ((UniqueFactorizationMonoid.normalizedFactors p).count π : RatFunc F)
              * logDeriv (algebraMap F[X] (RatFunc F) π) := by
  letI := logDifferential u
  -- Each normalized factor is monic irreducible, in particular nonzero.
  have hfac_ne : ∀ π ∈ UniqueFactorizationMonoid.normalizedFactors p, π ≠ 0 := fun π hπ =>
    UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors hπ
  -- `p = C lc · ∏ (normalizedFactors p)`.
  have hprod : Polynomial.C p.leadingCoeff * (UniqueFactorizationMonoid.normalizedFactors p).prod = p :=
    Polynomial.leadingCoeff_mul_prod_normalizedFactors p
  have hlcne : Polynomial.C p.leadingCoeff ≠ 0 := by
    simpa [Polynomial.C_eq_zero] using Polynomial.leadingCoeff_ne_zero.mpr hp
  have hprodne : (UniqueFactorizationMonoid.normalizedFactors p).prod ≠ 0 := by
    intro h0
    apply hp
    rw [← hprod, h0, mul_zero]
  -- Map the factorization to `RatFunc F`, split `logDeriv` of the product.
  have hAlc : algebraMap F[X] (RatFunc F) (Polynomial.C p.leadingCoeff) ≠ 0 :=
    RatFunc.algebraMap_ne_zero hlcne
  have hAprod : algebraMap F[X] (RatFunc F) (UniqueFactorizationMonoid.normalizedFactors p).prod ≠ 0 :=
    RatFunc.algebraMap_ne_zero hprodne
  conv_lhs => rw [← hprod, map_mul, Differential.logDeriv_mul _ _ hAlc hAprod]
  congr 1
  -- `logDeriv (algebraMap ∏factors) = ∑_{multiset} logDeriv (algebraMap π)`, then collect by count.
  rw [map_multiset_prod,
    Differential.logDeriv_multisetProd (UniqueFactorizationMonoid.normalizedFactors p)
      (f := fun π => algebraMap F[X] (RatFunc F) π)
      (fun π hπ => RatFunc.algebraMap_ne_zero (hfac_ne π hπ))]
  rw [Finset.sum_multiset_map_count]
  refine Finset.sum_congr rfl fun π hπ => ?_
  rw [nsmul_eq_mul]

/-- The `F`-unit part of `w ∈ RatFunc F`: `(num w).leadingCoeff / (denom w).leadingCoeff`. -/
noncomputable def wConst (w : RatFunc F) : F :=
  (RatFunc.num w).leadingCoeff / (RatFunc.denom w).leadingCoeff

/-- The signed `t`-pole multiplicity of a monic irreducible `π` in `w`, as an `F`-element:
`(count π in factors(num w)) − (count π in factors(denom w))`. -/
noncomputable def poleMult [DecidableEq F] (w : RatFunc F) (π : F[X]) : F :=
  ((UniqueFactorizationMonoid.normalizedFactors (RatFunc.num w)).count π : F)
    - ((UniqueFactorizationMonoid.normalizedFactors (RatFunc.denom w)).count π : F)

/-- The finite set of monic irreducible `t`-factors of `w` (numerator and denominator). -/
noncomputable def factorsFinset [DecidableEq F] (w : RatFunc F) : Finset F[X] :=
  (UniqueFactorizationMonoid.normalizedFactors (RatFunc.num w)).toFinset ∪
    (UniqueFactorizationMonoid.normalizedFactors (RatFunc.denom w)).toFinset

omit [Differential F] [CharZero F] in
/-- A normalized `t`-factor is monic. -/
theorem monic_of_mem_normalizedFactors [DecidableEq F] {a π : F[X]}
    (hπ : π ∈ UniqueFactorizationMonoid.normalizedFactors a) : π.Monic := by
  have hne : π ≠ 0 := UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors hπ
  exact (Polynomial.normalize_eq_self_iff_monic hne).mp
    (UniqueFactorizationMonoid.normalize_normalized_factor π hπ)

omit [Differential F] [CharZero F] in
/-- Every element of `factorsFinset w` is a monic irreducible `t`-polynomial. -/
theorem factorsFinset_monic_irreducible [DecidableEq F] {w : RatFunc F} {π : F[X]}
    (hπ : π ∈ factorsFinset w) : π.Monic ∧ Irreducible π := by
  rw [factorsFinset, Finset.mem_union, Multiset.mem_toFinset, Multiset.mem_toFinset] at hπ
  rcases hπ with hπ | hπ <;>
    exact ⟨monic_of_mem_normalizedFactors hπ,
      UniqueFactorizationMonoid.irreducible_of_normalized_factor _ hπ⟩

omit [CharZero F] in
/-- For `w ≠ 0`, `logDeriv w = logDeriv (algebraMap (wConst w)) + ∑_{π ∈ factorsFinset w}
algebraMap (C (poleMult w π)) · logDeriv (algebraMap π)`. -/
theorem logDeriv_eq_wConst_add_sum [DecidableEq F] (u : F) {w : RatFunc F} (hw : w ≠ 0) :
    letI := logDifferential u
    logDeriv w = logDeriv (algebraMap F (RatFunc F) (wConst w))
      + ∑ π ∈ factorsFinset w,
          algebraMap F[X] (RatFunc F) (Polynomial.C (poleMult w π))
            * logDeriv (algebraMap F[X] (RatFunc F) π) := by
  letI := logDifferential u
  set n := RatFunc.num w with hn
  set d := RatFunc.denom w with hd
  have hnne : n ≠ 0 := RatFunc.num_ne_zero hw
  have hdne : d ≠ 0 := RatFunc.denom_ne_zero w
  -- Split, then fold numerator and denominator.
  rw [logDeriv_eq_num_sub_denom u hw, ← hn, ← hd,
    logDeriv_algebraMap_eq_unit_add_sum u hnne, logDeriv_algebraMap_eq_unit_add_sum u hdne]
  -- Notation for the two normalized-factor multisets.
  set Mn := UniqueFactorizationMonoid.normalizedFactors n with hMn
  set Md := UniqueFactorizationMonoid.normalizedFactors d with hMd
  have hlcn : n.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hnne
  have hlcd : d.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hdne
  -- The leading-coefficient part is `logDeriv (algebraMap (wConst w))`.
  have hAn : algebraMap F[X] (RatFunc F) (Polynomial.C n.leadingCoeff) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (by simpa [Polynomial.C_eq_zero] using hlcn)
  have hAd : algebraMap F[X] (RatFunc F) (Polynomial.C d.leadingCoeff) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (by simpa [Polynomial.C_eq_zero] using hlcd)
  have hwconst : logDeriv (algebraMap F[X] (RatFunc F) (Polynomial.C n.leadingCoeff))
      - logDeriv (algebraMap F[X] (RatFunc F) (Polynomial.C d.leadingCoeff))
      = logDeriv (algebraMap F (RatFunc F) (wConst w)) := by
    rw [wConst, ← hn, ← hd, map_div₀, ratFunc_algebraMap_eq_algebraMap_C, ratFunc_algebraMap_eq_algebraMap_C,
      logDeriv_div _ _ hAn hAd]
  -- A `count` weight `(k : RatFunc F)` is the constant `algebraMap (C (k : F))`.
  have hcast : ∀ (m : Multiset F[X]) (π : F[X]),
      ((m.count π : ℕ) : RatFunc F)
        = algebraMap F[X] (RatFunc F) (Polynomial.C ((m.count π : ℕ) : F)) := by
    intro m π
    rw [← ratFunc_algebraMap_eq_algebraMap_C, map_natCast]
  -- Extend each factor sum over the union `factorsFinset w`; off-support counts are `0`.
  have hsub_n : (Mn.toFinset : Finset F[X]) ⊆ factorsFinset w := by
    rw [factorsFinset, ← hn]; exact Finset.subset_union_left
  have hsub_d : (Md.toFinset : Finset F[X]) ⊆ factorsFinset w := by
    rw [factorsFinset, ← hd]; exact Finset.subset_union_right
  have hext_n : ∑ π ∈ Mn.toFinset,
        ((Mn.count π : ℕ) : RatFunc F) * logDeriv (algebraMap F[X] (RatFunc F) π)
      = ∑ π ∈ factorsFinset w,
          algebraMap F[X] (RatFunc F) (Polynomial.C ((Mn.count π : ℕ) : F))
            * logDeriv (algebraMap F[X] (RatFunc F) π) := by
    rw [Finset.sum_subset hsub_n (fun π _ hπ => by
      rw [Multiset.mem_toFinset, ← Multiset.count_eq_zero] at hπ
      rw [hπ]; simp)]
    exact Finset.sum_congr rfl fun π _ => by rw [hcast]
  have hext_d : ∑ π ∈ Md.toFinset,
        ((Md.count π : ℕ) : RatFunc F) * logDeriv (algebraMap F[X] (RatFunc F) π)
      = ∑ π ∈ factorsFinset w,
          algebraMap F[X] (RatFunc F) (Polynomial.C ((Md.count π : ℕ) : F))
            * logDeriv (algebraMap F[X] (RatFunc F) π) := by
    rw [Finset.sum_subset hsub_d (fun π _ hπ => by
      rw [Multiset.mem_toFinset, ← Multiset.count_eq_zero] at hπ
      rw [hπ]; simp)]
    exact Finset.sum_congr rfl fun π _ => by rw [hcast]
  -- Assemble: leading-coeff part + (num sum − denom sum) merged into the `poleMult` sum.
  rw [hext_n, hext_d, ← hwconst]
  -- Expand the `poleMult` sum on the RHS into a difference of the two count-products.
  have hpole : ∑ π ∈ factorsFinset w,
        algebraMap F[X] (RatFunc F) (Polynomial.C (poleMult w π))
          * logDeriv (algebraMap F[X] (RatFunc F) π)
      = ∑ π ∈ factorsFinset w,
          algebraMap F[X] (RatFunc F) (Polynomial.C ((Mn.count π : ℕ) : F))
            * logDeriv (algebraMap F[X] (RatFunc F) π)
        - ∑ π ∈ factorsFinset w,
          algebraMap F[X] (RatFunc F) (Polynomial.C ((Md.count π : ℕ) : F))
            * logDeriv (algebraMap F[X] (RatFunc F) π) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [poleMult, ← hn, ← hd, ← hMn, ← hMd, map_sub, map_sub, sub_mul]
  rw [hpole]; ring

omit [Differential F] [CharZero F] in
/-- `poleMult` vanishes off `factorsFinset`: `π ∉ factorsFinset w ⟹ poleMult w π = 0`. -/
theorem poleMult_eq_zero_of_notMem [DecidableEq F] {w : RatFunc F} {π : F[X]}
    (hπ : π ∉ factorsFinset w) : poleMult w π = 0 := by
  simp only [factorsFinset, Finset.mem_union, Multiset.mem_toFinset, not_or,
    ← Multiset.count_eq_zero] at hπ
  rw [poleMult, hπ.1, hπ.2]; simp

omit [CharZero F] in
/-- Multi-term pole collection: `∑ᵢ ↑(cᵢ)·logDeriv wᵢ = ∑ᵢ ↑(cᵢ)·logDeriv (↑(wConst wᵢ)) +
∑_{π ∈ S} ↑(C (∑ᵢ cᵢ · poleMult wᵢ π)) · logDeriv (↑π)`, with `S = ⋃ᵢ factorsFinset wᵢ`. -/
theorem sum_const_logDeriv_eq_wConst_add_pole [DecidableEq F] (u : F) {ι : Type*} [Fintype ι]
    (c : ι → F) (w : ι → RatFunc F) (hw : ∀ i, w i ≠ 0) :
    letI := logDifferential u
    ∑ i, algebraMap F (RatFunc F) (c i) * logDeriv (w i)
      = ∑ i, algebraMap F (RatFunc F) (c i)
            * logDeriv (algebraMap F (RatFunc F) (wConst (w i)))
        + ∑ π ∈ Finset.univ.biUnion (fun i => factorsFinset (w i)),
            algebraMap F[X] (RatFunc F)
                (Polynomial.C (∑ i, c i * poleMult (w i) π))
              * logDeriv (algebraMap F[X] (RatFunc F) π) := by
  letI := logDifferential u
  set S := Finset.univ.biUnion (fun i => factorsFinset (w i)) with hS
  -- Per-`i`: extend the pole sum to `S`, then `cᵢ·logDeriv wᵢ = cᵢ·logDeriv ↑(wConst) + ∑_S …`.
  have hsubS : ∀ i, factorsFinset (w i) ⊆ S := fun i =>
    Finset.subset_biUnion_of_mem (fun i => factorsFinset (w i)) (Finset.mem_univ i)
  have hper : ∀ i, algebraMap F (RatFunc F) (c i) * logDeriv (w i)
      = algebraMap F (RatFunc F) (c i) * logDeriv (algebraMap F (RatFunc F) (wConst (w i)))
        + ∑ π ∈ S, algebraMap F (RatFunc F) (c i)
            * (algebraMap F[X] (RatFunc F) (Polynomial.C (poleMult (w i) π))
                * logDeriv (algebraMap F[X] (RatFunc F) π)) := by
    intro i
    rw [logDeriv_eq_wConst_add_sum u (hw i), mul_add, Finset.mul_sum]
    congr 1
    rw [Finset.sum_subset (hsubS i) (fun π _ hπ => by
      rw [poleMult_eq_zero_of_notMem hπ]; simp)]
  -- Sum over `i`, split into the `F`-part and the (swapped) pole part.
  rw [Finset.sum_congr rfl (fun i _ => hper i), Finset.sum_add_distrib]
  congr 1
  -- Swap `∑ᵢ ∑_S` to `∑_S ∑ᵢ` and fold `cᵢ·↑(C(poleMult)) = ↑(C(cᵢ·poleMult))`.
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ratFunc_algebraMap_eq_algebraMap_C, ← mul_assoc, ← map_mul, ← Polynomial.C_mul]

/-- Single-log pole-independence: from `algebraMap a = c · logDeriv w + v′` (`a`, `c` in `F`, `c′ = 0`)
there exist `w₀ ∈ F` and `v₀ ∈ RatFunc F` with the same sum, the log argument in `F`, and `v₀′ ∈ F`. -/
def SingleLogPoleObligation (u : F) : Prop :=
  letI := logDifferential u
  letI := logDifferentialAlgebra u
  ∀ (a : F) (c : F), c′ = 0 → ∀ (w v : RatFunc F),
    algebraMap F (RatFunc F) a = algebraMap F (RatFunc F) c * logDeriv w + v′ →
    ∃ (w₀ : F) (v₀ : RatFunc F),
      algebraMap F (RatFunc F) a
        = algebraMap F (RatFunc F) c * logDeriv (algebraMap F (RatFunc F) w₀) + v₀′
      ∧ v₀′ ∈ (algebraMap F (RatFunc F)).range

omit [CharZero F] in
/-- Given `SingleLogPoleObligation` and `IsLogRangeReduction`, a single-log representation of `a ∈ F`
yields `F`-data `w₀, v₀ ∈ F`. -/
theorem singleLog_fData (u : F) (hslp : SingleLogPoleObligation u)
    (hrange : IsLogRangeReduction u)
    (a : F) (c : F) (hc : c′ = 0) (w v : RatFunc F)
    (h : letI := logDifferential u; letI := logDifferentialAlgebra u;
      algebraMap F (RatFunc F) a = algebraMap F (RatFunc F) c * logDeriv w + v′) :
    letI := logDifferential u
    letI := logDifferentialAlgebra u
    ∃ (w₀ : F) (v₀ : F),
      algebraMap F (RatFunc F) a
        = algebraMap F (RatFunc F) c * logDeriv (algebraMap F (RatFunc F) w₀)
            + (algebraMap F (RatFunc F) v₀)′ := by
  letI := logDifferential u
  letI := logDifferentialAlgebra u
  -- Pole-independence: pull the log argument into `F`, leaving a corrected `v₀` with `v₀′ ∈ F`.
  obtain ⟨w₀, v₁, h₁, hv₁⟩ := hslp a c hc w v h
  -- The corrected `v₁` has derivative in `F`, so by the `v ∈ F` reduction `v₁ ∈ F`.
  obtain ⟨v₀, hv₀⟩ := mem_range_of_deriv_mem_range u hrange hv₁
  exact ⟨w₀, v₀, by rw [h₁, hv₀]⟩

/-- The constant condition: given `logDeriv u ≠ 0`, `ContainConstants F (RatFunc F)` holds
(every `t`-constant is in `F`). -/
def ContainConstantsObligation (u : F) [Differential (RatFunc F)] : Prop :=
  logDeriv u ≠ 0 → Differential.ContainConstants F (RatFunc F)

/-- The `F`-data reduction: any representation `a = ∑ cᵢ logDeriv wᵢ + v′` of `a ∈ F` can be
re-expressed with `w₀ : ι → F` and `v₀ : F` so that `a = ∑ cᵢ logDeriv (w₀ x) + v₀′`. -/
def LiouvilleFDataReduction (u : F) : Prop :=
  letI := logDifferential u
  letI := logDifferentialAlgebra u
  ∀ (a : F) (ι : Type) [Fintype ι] (c : ι → F), (∀ x, (c x)′ = 0) →
    ∀ (w : ι → RatFunc F) (v : RatFunc F),
      algebraMap F (RatFunc F) a = ∑ x, algebraMap F (RatFunc F) (c x) * logDeriv (w x) + v′ →
      ∃ (w₀ : ι → F) (v₀ : F),
        algebraMap F (RatFunc F) a
          = ∑ x, algebraMap F (RatFunc F) (c x) * logDeriv (algebraMap F (RatFunc F) (w₀ x))
              + (algebraMap F (RatFunc F) v₀)′

/-! ### The multi-term case

The general `∑ᵢ cᵢ logDeriv wᵢ + v′` reduction, where distinct `wᵢ` may share irreducible `t`-factors;
the simple `t`-poles are `F`-linearly independent modulo polynomials. -/

omit [CharZero F] in
/-- Pole-independence: if `∑ⱼ algebraMap (d j) · logDeriv (algebraMap (π j))` (distinct monic
irreducible `π j`, `deg (d j) < deg (π j)`) is a polynomial, then every `d j = 0`. -/
def PoleIndependenceObligation (u : F) : Prop :=
  letI := logDifferential u
  ∀ {ιπ : Type} [Fintype ιπ] (π : ιπ → F[X]) (d : ιπ → F[X]),
    (∀ j, (π j).Monic) → (∀ j, Irreducible (π j)) → Function.Injective π →
    (∀ j, (d j).natDegree < (π j).natDegree) →
    (∑ j, algebraMap F[X] (RatFunc F) (d j)
        * logDeriv (algebraMap F[X] (RatFunc F) (π j)))
      ∈ (algebraMap F[X] (RatFunc F)).range →
    ∀ j, d j = 0

open scoped algebraMap in
omit [CharZero F] in
/-- Pole-independence holds when every `D πⱼ ≠ 0`: distinct monic irreducible `πⱼ`, `deg dⱼ < deg πⱼ`,
and `∑ⱼ dⱼ · logDeriv πⱼ` a polynomial force every `dⱼ = 0`. -/
theorem poleIndependence_of_logDerivPoly_ne_zero (u : F) {ιπ : Type*} [Fintype ιπ]
    (π : ιπ → F[X]) (d : ιπ → F[X]) (hmon : ∀ j, (π j).Monic) (hirr : ∀ j, Irreducible (π j))
    (hinj : Function.Injective π) (hdeg : ∀ j, (d j).natDegree < (π j).natDegree)
    (hDne : ∀ j, logDerivPoly u (π j) ≠ 0)
    (hpoly : letI := logDifferential u
      (∑ j, algebraMap F[X] (RatFunc F) (d j)
          * logDeriv (algebraMap F[X] (RatFunc F) (π j)))
        ∈ (algebraMap F[X] (RatFunc F)).range) :
    ∀ j, d j = 0 := by
  letI := logDifferential u
  -- Notation: `D πⱼ`, the quotient/remainder of `dⱼ · D πⱼ` by the monic `πⱼ`.
  set Dπ : ιπ → F[X] := fun j => logDerivPoly u (π j) with hDπ
  set rem : ιπ → F[X] := fun j => (d j * Dπ j) %ₘ (π j) with hrem
  set quo : ιπ → F[X] := fun j => (d j * Dπ j) /ₘ (π j) with hquo
  -- `deg πⱼ ≥ 1` and `deg remⱼ < deg πⱼ`.
  have hdegπ : ∀ j, 1 ≤ (π j).natDegree := fun j => (hirr j).natDegree_pos
  have hdegrem : ∀ j, (rem j).degree < (π j).degree := fun j =>
    degree_modByMonic_lt _ (hmon j)
  -- Each term equals `↑quoⱼ + ↑remⱼ / ↑πⱼ` in `RatFunc F`.
  have hπne : ∀ j, (algebraMap F[X] (RatFunc F) (π j)) ≠ 0 := fun j =>
    RatFunc.algebraMap_ne_zero (hmon j).ne_zero
  have hterm : ∀ j, algebraMap F[X] (RatFunc F) (d j)
      * logDeriv (algebraMap F[X] (RatFunc F) (π j))
      = (quo j : RatFunc F) + (rem j : RatFunc F) / (π j : RatFunc F) := by
    intro j
    rw [logDeriv_algebraMap_eq u (π j)]
    show algebraMap F[X] (RatFunc F) (d j)
        * (algebraMap F[X] (RatFunc F) (Dπ j) / algebraMap F[X] (RatFunc F) (π j))
      = (quo j : RatFunc F) + (rem j : RatFunc F) / (π j : RatFunc F)
    -- `dⱼ · (D πⱼ / πⱼ) = (dⱼ · D πⱼ) / πⱼ`, then `dⱼ·D πⱼ = πⱼ·quoⱼ + remⱼ`.
    have hsplit : d j * Dπ j = π j * quo j + rem j := by
      rw [hrem, hquo, add_comm]; exact (modByMonic_add_div (d j * Dπ j) (π j)).symm
    rw [mul_div_assoc', ← map_mul, hsplit, map_add, map_mul, add_div]
    congr 1
    rw [mul_comm, mul_div_assoc, div_self (hπne j), mul_one]
  -- Rewrite the whole sum and pull out the polynomial value `P`.
  obtain ⟨P, hP⟩ := hpoly
  simp_rw [hterm] at hP
  rw [Finset.sum_add_distrib, ← map_sum] at hP
  -- Now `↑P = ↑(∑ quoⱼ) + ∑ ↑remⱼ/↑πⱼ`; uniqueness against `↑P + ∑ ↑0/↑πⱼ` forces `remⱼ = 0`.
  have hcop : Set.Pairwise (Finset.univ : Finset ιπ) fun i j => IsCoprime (π i) (π j) := by
    intro i _ j _ hij
    rw [(hirr i).coprime_iff_not_dvd]
    intro hdvd
    exact hij (hinj (eq_of_monic_of_associated (hmon i) (hmon j)
      ((hirr i).associated_of_dvd (hirr j) hdvd)))
  have hdeg0 : ∀ j, (0 : F[X]).degree < (π j).degree := by
    intro j
    rw [Polynomial.degree_zero]
    exact bot_lt_iff_ne_bot.mpr (Polynomial.degree_eq_bot.not.mpr (hmon j).ne_zero)
  have huniq := Polynomial.quo_add_sum_rem_div_unique (R := F) (K := RatFunc F)
    (g := π) (s := Finset.univ) (fun j _ => hmon j) hcop
    (q₁ := ∑ j, quo j) (q₂ := P) (r₁ := rem) (r₂ := fun _ => 0)
    (fun j _ => hdegrem j) (fun j _ => hdeg0 j)
    (by push_cast; simpa [div_eq_mul_inv] using hP.symm)
  -- From uniqueness `remⱼ = 0`, get `πⱼ ∣ dⱼ · D πⱼ`, then `πⱼ ∣ dⱼ`, then `dⱼ = 0`.
  intro j
  have hrem0 : rem j = 0 := huniq.2 j (Finset.mem_univ j)
  have hdvd : π j ∣ d j * Dπ j :=
    (Polynomial.modByMonic_eq_zero_iff_dvd (hmon j)).mp hrem0
  have hnd : ¬ π j ∣ Dπ j :=
    not_dvd_logDerivPoly_of_natDegree_lt u (hmon j) (hdegπ j) (hDne j)
  have hdvdd : π j ∣ d j := ((hirr j).prime.dvd_or_dvd hdvd).resolve_right hnd
  by_contra hd0
  exact absurd (Polynomial.natDegree_le_of_dvd hdvdd hd0) (by have := hdeg j; omega)

omit [CharZero F] in
/-- `PoleIndependenceObligation` holds under `NondegenerateLog u`. -/
theorem poleIndependenceObligation_of_nondegenerateLog (u : F) (hnd : NondegenerateLog u) :
    PoleIndependenceObligation u := by
  letI := logDifferential u
  intro ιπ _ π d hmon hirr hinj hdeg hpoly
  exact poleIndependence_of_logDerivPoly_ne_zero u π d hmon hirr hinj hdeg
    (fun j => hnd (π j) (hmon j) (hirr j)) hpoly

open scoped algebraMap in
omit [CharZero F] in
/-- Given `NondegenerateLog`, over a finite set `S` of monic irreducibles with constant residues
`r : F[X] → F`, if `∑_{π ∈ S} ↑(C (r π)) · logDeriv (algebraMap π)` is a polynomial then every `r π = 0`. -/
theorem poleIndependence_finset_const (u : F) (hnd : NondegenerateLog u) (S : Finset F[X])
    (hmon : ∀ π ∈ S, π.Monic) (hirr : ∀ π ∈ S, Irreducible π) (r : F[X] → F)
    (hpoly : letI := logDifferential u
      (∑ π ∈ S, algebraMap F[X] (RatFunc F) (Polynomial.C (r π))
          * logDeriv (algebraMap F[X] (RatFunc F) π))
        ∈ (algebraMap F[X] (RatFunc F)).range) :
    ∀ π ∈ S, r π = 0 := by
  letI := logDifferential u
  -- Apply the subtype-indexed pole-independence; `π = Subtype.val`, `d = C ∘ r ∘ val`.
  have hkey := poleIndependence_of_logDerivPoly_ne_zero u (ιπ := ↥S)
    (π := fun j => (j : F[X])) (d := fun j => Polynomial.C (r (j : F[X])))
    (fun j => hmon j j.2) (fun j => hirr j j.2) Subtype.val_injective
    (fun j => by
      -- `deg (C (r j)) ≤ 0 < 1 ≤ deg (val j)` (irreducible ⇒ positive degree).
      calc (Polynomial.C (r (j : F[X]))).natDegree ≤ 0 := (Polynomial.natDegree_C _).le
        _ < (↑j : F[X]).natDegree := (hirr j j.2).natDegree_pos)
    (fun j => hnd (↑j) (hmon j j.2) (hirr j j.2))
    (by
      -- The subtype-`Fintype` sum equals the `Finset` sum `hpoly`.
      rw [← Finset.sum_attach S (fun π => algebraMap F[X] (RatFunc F) (Polynomial.C (r π))
        * logDeriv (algebraMap F[X] (RatFunc F) π))] at hpoly
      exact hpoly)
  intro π hπ
  have hcj := hkey ⟨π, hπ⟩
  simpa using congrArg (fun q : F[X] => q.coeff 0) hcj

/-- Multi-term pole-matching: from `algebraMap a = ∑ᵢ cᵢ logDeriv wᵢ + v′` (`a ∈ F`, `cᵢ` constant)
there exist `w₀ : ι → F` and `v₀ : RatFunc F` with the same sum, log arguments in `F`, and `v₀′ ∈ F`. -/
def MultiLogPoleObligation (u : F) : Prop :=
  letI := logDifferential u
  letI := logDifferentialAlgebra u
  ∀ (a : F) (ι : Type) [Fintype ι] (c : ι → F), (∀ x, (c x)′ = 0) →
    ∀ (w : ι → RatFunc F) (v : RatFunc F),
      algebraMap F (RatFunc F) a = ∑ x, algebraMap F (RatFunc F) (c x) * logDeriv (w x) + v′ →
      ∃ (w₀ : ι → F) (v₀ : RatFunc F),
        (algebraMap F (RatFunc F) a
          = ∑ x, algebraMap F (RatFunc F) (c x) * logDeriv (algebraMap F (RatFunc F) (w₀ x)) + v₀′)
        ∧ v₀′ ∈ (algebraMap F (RatFunc F)).range

omit [Differential F] [CharZero F] in
/-- `∑ᵢ ↑(cᵢ) · logDeriv (algebraMap (xᵢ))` lies in `range (algebraMap F[t])`. -/
theorem sum_const_logDeriv_algebraMap_mem_range [Differential F] (u : F) {ι : Type*} [Fintype ι]
    (c : ι → F) (x : ι → F) :
    letI := logDifferential u
    (∑ i, algebraMap F (RatFunc F) (c i)
        * logDeriv (algebraMap F (RatFunc F) (x i)))
      ∈ (algebraMap F[X] (RatFunc F)).range := by
  letI := logDifferential u
  letI := logDifferentialAlgebra u
  refine ⟨Polynomial.C (∑ i, c i * logDeriv (x i)), ?_⟩
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [logDeriv_algebraMap, ← ratFunc_algebraMap_eq_algebraMap_C, ← map_mul]

omit [CharZero F] in
/-- For monic irreducibles `S`, `(∑_{π∈S} ↑(C (r π)) · logDeriv (algebraMap π)) · algebraMap (∏_{π∈S} π)`
lies in `range (algebraMap F[t])`. -/
theorem simplePole_mul_prod_mem_range (u : F) (S : Finset F[X]) (r : F[X] → F)
    (hmon : ∀ π ∈ S, π.Monic) :
    letI := logDifferential u
    ((∑ π ∈ S, algebraMap F[X] (RatFunc F) (Polynomial.C (r π))
        * logDeriv (algebraMap F[X] (RatFunc F) π))
        * algebraMap F[X] (RatFunc F) (∏ ρ ∈ S, ρ))
      ∈ (algebraMap F[X] (RatFunc F)).range := by
  classical
  letI := logDifferential u
  refine ⟨∑ π ∈ S, Polynomial.C (r π) * logDerivPoly u π * ∏ ρ ∈ S.erase π, ρ, ?_⟩
  rw [Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun π hπ => ?_
  have hπne : algebraMap F[X] (RatFunc F) π ≠ 0 :=
    RatFunc.algebraMap_ne_zero (hmon π hπ).ne_zero
  have hprod : (∏ ρ ∈ S, ρ) = π * ∏ ρ ∈ S.erase π, ρ := (Finset.mul_prod_erase S _ hπ).symm
  rw [logDeriv_algebraMap_eq u π, hprod, map_mul, map_mul, map_mul]
  field_simp

omit [Differential F] [CharZero F] in
/-- A finite set of polynomial factors is monic and irreducible pointwise. -/
structure IsMonicIrreducibleSet (S : Finset F[X]) : Prop where
  /-- Every member of the set is monic. -/
  monic : ∀ π ∈ S, π.Monic
  /-- Every member of the set is irreducible. -/
  irreducible : ∀ π ∈ S, Irreducible π

omit [Differential F] [CharZero F] in
/-- A product of distinct monic irreducibles `∏_{π∈S} π` is squarefree. -/
theorem squarefree_prod_of_monic_irreducible (S : Finset F[X]) (hS : IsMonicIrreducibleSet S) :
    Squarefree (∏ ρ ∈ S, ρ) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ (fun π hπ => (hS.irreducible π hπ).squarefree)
  intro i hi j hj hij
  simp only [Function.onFun]
  -- Distinct monic irreducibles are coprime, hence `IsRelPrime`.
  refine ((hS.irreducible i hi).coprime_iff_not_dvd.mpr fun hdvd => hij ?_).isRelPrime
  exact eq_of_monic_of_associated (hS.monic i hi) (hS.monic j hj)
    ((hS.irreducible i hi).associated_of_dvd (hS.irreducible j hj) hdvd)

/-- Valuation contradiction: for monic irreducible `π ∣ D` (`π ∤ D π`), `N` coprime to `D`, and
`G = ∏_{ρ∈S} ρ` distinct monic irreducibles, `D² ∤ (D·DN − N·DD)·G`
(`DN = logDerivPoly u N`, `DD = logDerivPoly u D`). -/
theorem not_dvd_sq_mul_of_pole (u : F) (hnd : NondegenerateLog u) {N D π : F[X]}
    (hπmon : π.Monic) (hπirr : Irreducible π) (hDne0 : D ≠ 0) (hcop : IsCoprime N D)
    (hπdvdD : π ∣ D) {S : Finset F[X]} (hS : IsMonicIrreducibleSet S) :
    ¬ D * D ∣ (D * logDerivPoly u N - N * logDerivPoly u D) * (∏ ρ ∈ S, ρ) := by
  intro hdvd
  set DN := logDerivPoly u N with hDNdef
  set DD := logDerivPoly u D with hDDdef
  set G := ∏ ρ ∈ S, ρ with hGdef
  have hπprime : Prime π := hπirr.prime
  -- `k := v_π(D) ≥ 1` (finite, since `π` prime and `D ≠ 0`).
  have hfinD : FiniteMultiplicity π D := Polynomial.finiteMultiplicity_of_degree_pos_of_monic
    (hπirr.degree_pos) hπmon hDne0
  set k := multiplicity π D with hkdef
  have hmultD : emultiplicity π D = (k : ℕ∞) := hfinD.emultiplicity_eq_multiplicity
  have hk1 : 1 ≤ k := hfinD.le_multiplicity_of_pow_dvd (by simpa using hπdvdD)
  -- `π ∤ D π` from non-degeneracy.
  have hπnDπ : ¬ π ∣ logDerivPoly u π :=
    not_dvd_logDerivPoly_of_monic u hnd hπmon hπirr.natDegree_pos
  -- `v_π(DD) = k − 1`, `v_π(N) = 0`, `v_π(G) ≤ 1`.
  have hmultDD : emultiplicity π DD = ((k - 1 : ℕ) : ℕ∞) :=
    emultiplicity_logDerivPoly_eq u hπirr hπnDπ hk1 hmultD
  have hmultN : emultiplicity π N = 0 := by
    rw [emultiplicity_eq_zero]
    intro hπN
    exact hπirr.1 (hcop.isUnit_of_dvd' hπN hπdvdD)
  have hmultG : emultiplicity π G ≤ 1 :=
    ((squarefree_iff_emultiplicity_le_one G).mp
      (squarefree_prod_of_monic_irreducible S hS) π).resolve_right hπirr.1
  -- `v_π(N·DD) = k − 1`; `v_π(D·DN) ≥ k > k − 1`; so `v_π(D·DN − N·DD) = k − 1`.
  have hmult_NDD : emultiplicity π (N * DD) = ((k - 1 : ℕ) : ℕ∞) := by
    rw [emultiplicity_mul hπprime, hmultN, hmultDD, zero_add]
  have hmult_DDN_ge : (k : ℕ∞) ≤ emultiplicity π (D * DN) := by
    rw [emultiplicity_mul hπprime, hmultD]
    exact le_add_right le_rfl
  have hk1lt : ((k - 1 : ℕ) : ℕ∞) < (k : ℕ∞) := by
    rw [Nat.cast_lt]; omega
  have hne : emultiplicity π (D * DN) ≠ emultiplicity π (N * DD) := by
    rw [hmult_NDD]; exact (lt_of_lt_of_le hk1lt hmult_DDN_ge).ne'
  have hmult_diff : emultiplicity π (D * DN - N * DD) = ((k - 1 : ℕ) : ℕ∞) := by
    rw [sub_eq_add_neg, emultiplicity_add_eq_min (by rwa [emultiplicity_neg]),
      emultiplicity_neg, hmult_NDD, min_eq_right (le_of_lt (lt_of_lt_of_le hk1lt hmult_DDN_ge))]
  -- `2k ≤ v_π((D·DN − N·DD)·G) = (k − 1) + v_π(G) ≤ (k − 1) + 1 = k`, contradiction.
  have hdvd2 : (D : F[X]) ^ 2 ∣ (D * DN - N * DD) * G := by rw [sq]; exact hdvd
  have hle : emultiplicity π (D ^ 2) ≤ emultiplicity π ((D * DN - N * DD) * G) :=
    emultiplicity_le_emultiplicity_of_dvd_right hdvd2
  rw [emultiplicity_pow hπprime, hmultD, emultiplicity_mul hπprime, hmult_diff] at hle
  -- `hle : ↑2 · ↑k ≤ ↑(k−1) + v_π(G)`; with `v_π(G) ≤ 1` and `↑(k−1)+1 = ↑k`, get `2k ≤ k`.
  have hk_succ : ((k - 1 : ℕ) : ℕ∞) + 1 = ((k : ℕ) : ℕ∞) := by
    rw [show ((k - 1 : ℕ) : ℕ∞) + 1 = (((k - 1) + 1 : ℕ) : ℕ∞) by push_cast; ring,
      show (k - 1) + 1 = k from by omega]
  have hG1 : ((k - 1 : ℕ) : ℕ∞) + emultiplicity π G ≤ ((k : ℕ) : ℕ∞) :=
    le_trans (add_le_add le_rfl hmultG) (le_of_eq hk_succ)
  have hfinal : ((2 : ℕ) : ℕ∞) * ((k : ℕ) : ℕ∞) ≤ ((k : ℕ) : ℕ∞) := le_trans hle hG1
  rw [← Nat.cast_mul, Nat.cast_le] at hfinal
  omega

/-- Given `NondegenerateLog`, if `v′ + (simple-pole sum over `S`)` is a polynomial then `v` is a polynomial. -/
theorem mem_range_of_deriv_add_simplePole_mem_range (u : F) (hnd : NondegenerateLog u)
    (v : RatFunc F) (S : Finset F[X]) (r : F[X] → F)
    (hS : IsMonicIrreducibleSet S)
    (hpoly : letI := logDifferential u
      (v′ + ∑ π ∈ S, algebraMap F[X] (RatFunc F) (Polynomial.C (r π))
          * logDeriv (algebraMap F[X] (RatFunc F) π))
        ∈ (algebraMap F[X] (RatFunc F)).range) :
    v ∈ (algebraMap F[X] (RatFunc F)).range := by
  classical
  letI := logDifferential u
  rcases eq_or_ne v 0 with rfl | hv0
  · exact ⟨0, by rw [map_zero]⟩
  set N := RatFunc.num v with hNdef
  set D := RatFunc.denom v with hDdef
  set G := ∏ ρ ∈ S, ρ with hGdef
  have hDmon : D.Monic := RatFunc.monic_denom v
  have hDne0 : D ≠ 0 := RatFunc.denom_ne_zero v
  have hNne0 : N ≠ 0 := RatFunc.num_ne_zero hv0
  have hcop : IsCoprime N D := RatFunc.isCoprime_num_denom v
  have hNA : algebraMap F[X] (RatFunc F) N ≠ 0 := RatFunc.algebraMap_ne_zero hNne0
  have hDA : algebraMap F[X] (RatFunc F) D ≠ 0 := RatFunc.algebraMap_ne_zero hDne0
  set DN := logDerivPoly u N with hDNdef
  set DD := logDerivPoly u D with hDDdef
  -- `Q · ↑G = ↑NQ` (helper) and `R = ↑Rp` (hypothesis).
  obtain ⟨NQ, hNQ⟩ := simplePole_mul_prod_mem_range u S r hS.monic
  obtain ⟨Rp, hRp⟩ := hpoly
  set Q : RatFunc F := ∑ π ∈ S, algebraMap F[X] (RatFunc F) (Polynomial.C (r π))
      * logDeriv (algebraMap F[X] (RatFunc F) π) with hQdef
  -- Quotient-rule clearing: `v′ · ↑(D·D) = ↑(D·DN − N·DD)`.
  have hveq : v = algebraMap F[X] (RatFunc F) N / algebraMap F[X] (RatFunc F) D := by
    rw [← RatFunc.num_div_denom v, ← hNdef, ← hDdef]
  have hlogv : logDeriv v
      = algebraMap F[X] (RatFunc F) DN / algebraMap F[X] (RatFunc F) N
        - algebraMap F[X] (RatFunc F) DD / algebraMap F[X] (RatFunc F) D := by
    have hsplit : logDeriv v = logDeriv (algebraMap F[X] (RatFunc F) N)
        - logDeriv (algebraMap F[X] (RatFunc F) D) := by
      conv_lhs => rw [hveq]; exact logDeriv_div _ _ hNA hDA
    rw [hsplit, logDeriv_algebraMap_eq u N, logDeriv_algebraMap_eq u D]
  have hv'eq : v′ = v * logDeriv v := by rw [logDeriv, mul_div_cancel₀ _ hv0]
  have hGA : algebraMap F[X] (RatFunc F) G ≠ 0 :=
    RatFunc.algebraMap_ne_zero (Polynomial.Monic.ne_zero (by
      rw [hGdef]; exact monic_prod_of_monic _ _ (fun π hπ => hS.monic π hπ)))
  -- `v′ · ↑D · ↑D = ↑D·↑DN − ↑N·↑DD` (the controlled `field_simp`, only `↑N`/`↑D` denominators).
  have hclear : v′ * algebraMap F[X] (RatFunc F) D * algebraMap F[X] (RatFunc F) D
      = algebraMap F[X] (RatFunc F) D * algebraMap F[X] (RatFunc F) DN
        - algebraMap F[X] (RatFunc F) N * algebraMap F[X] (RatFunc F) DD := by
    rw [hv'eq, hlogv, hveq]
    field_simp
  -- `↑NQ = (↑Rp − v′)·↑G` (from `Q·↑G = ↑NQ` and `↑Rp = v′ + Q`).
  have hNQval : algebraMap F[X] (RatFunc F) NQ
      = (algebraMap F[X] (RatFunc F) Rp - v′) * algebraMap F[X] (RatFunc F) G := by
    rw [hNQ, ← hGdef]
    have hQval : Q = algebraMap F[X] (RatFunc F) Rp - v′ := by rw [hRp]; ring
    rw [hQval]
  -- The cleared polynomial identity: both sides equal `v′·↑D·↑D·↑G` (via `hclear`, `hNQval`).
  have hpolyid : (D * DN - N * DD) * G = (D * D) * (Rp * G - NQ) := by
    apply FaithfulSMul.algebraMap_injective F[X] (RatFunc F)
    simp only [map_mul, map_sub]
    rw [hNQval]
    linear_combination (-(algebraMap F[X] (RatFunc F) G)) * hclear
  -- `D² ∣ (D·DN − N·DD)·G`.
  have hdvd : D * D ∣ (D * DN - N * DD) * G := ⟨Rp * G - NQ, hpolyid⟩
  -- Conclude `D = 1` by a per-prime valuation contradiction, hence `v = ↑N`.
  have hD1 : D = 1 := by
    by_contra hDne1
    -- `D` not a unit, so `normalizedFactors D` is nonempty: pick a monic irreducible factor `π`.
    have hDnu : ¬ IsUnit D := fun hu => hDne1 (hDmon.eq_one_of_isUnit hu)
    obtain ⟨π, hπmem⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors hDne0 hDnu
    have hπmon : π.Monic := monic_of_mem_normalizedFactors hπmem
    have hπirr : Irreducible π := UniqueFactorizationMonoid.irreducible_of_normalized_factor _ hπmem
    have hπdvdD : π ∣ D := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hπmem
    exact absurd hdvd
      (not_dvd_sq_mul_of_pole u hnd hπmon hπirr hDne0 hcop hπdvdD hS)
  rw [hveq, hD1, map_one, div_one]
  exact ⟨N, rfl⟩

/-- Simple-pole separation: for `S` monic irreducibles and constant residues `r`, if
`v′ + (simple-pole sum)` is a polynomial then the simple-pole sum is by itself a polynomial. -/
def DerivSimplePoleSeparation (u : F) : Prop :=
  letI := logDifferential u
  ∀ (v : RatFunc F) (S : Finset F[X]) (r : F[X] → F),
    (∀ π ∈ S, π.Monic) → (∀ π ∈ S, Irreducible π) →
    (v′ + ∑ π ∈ S, algebraMap F[X] (RatFunc F) (Polynomial.C (r π))
        * logDeriv (algebraMap F[X] (RatFunc F) π))
      ∈ (algebraMap F[X] (RatFunc F)).range →
    (∑ π ∈ S, algebraMap F[X] (RatFunc F) (Polynomial.C (r π))
        * logDeriv (algebraMap F[X] (RatFunc F) π))
      ∈ (algebraMap F[X] (RatFunc F)).range

/-- `DerivSimplePoleSeparation` holds under `NondegenerateLog u`. -/
theorem derivSimplePoleSeparation_of_nondegenerateLog (u : F) (hnd : NondegenerateLog u) :
    DerivSimplePoleSeparation u := by
  letI := logDifferential u
  intro v S r hmon hirr hpoly
  -- `v` is a polynomial (separation engine), hence `v′` is a polynomial.
  obtain ⟨p, hp⟩ := mem_range_of_deriv_add_simplePole_mem_range u hnd v S r ⟨hmon, hirr⟩ hpoly
  have hv'poly : v′ ∈ (algebraMap F[X] (RatFunc F)).range := by
    refine ⟨logDerivPoly u p, ?_⟩
    rw [← derivExtends u p, hp]
  -- The simple-pole sum `= (v′ + sum) − v′ ∈ range` (range closed under subtraction).
  have hsub : (∑ π ∈ S, algebraMap F[X] (RatFunc F) (Polynomial.C (r π))
        * logDeriv (algebraMap F[X] (RatFunc F) π))
      = (v′ + ∑ π ∈ S, algebraMap F[X] (RatFunc F) (Polynomial.C (r π))
          * logDeriv (algebraMap F[X] (RatFunc F) π)) - v′ := by ring
  rw [hsub]
  exact sub_mem hpoly hv'poly

omit [CharZero F] in
/-- Given `NondegenerateLog` and `DerivSimplePoleSeparation`, `MultiLogPoleObligation u` holds. -/
theorem multiLogPoleObligation_of_nondegenerateLog (u : F) (hnd : NondegenerateLog u)
    (hsep : DerivSimplePoleSeparation u) : MultiLogPoleObligation u := by
  letI := logDifferential u
  letI := logDifferentialAlgebra u
  classical
  intro a ι _ c _hc w v h
  -- Replace zero `wᵢ` by `1` (`logDeriv 1 = 0 = logDeriv 0`); `w'ᵢ ≠ 0`.
  set w' : ι → RatFunc F := fun i => if w i = 0 then 1 else w i with hw'def
  have hw'ne : ∀ i, w' i ≠ 0 := by
    intro i; rw [hw'def]; dsimp only; split
    · exact one_ne_zero
    · assumption
  have hlog_eq : ∀ i, logDeriv (w' i) = logDeriv (w i) := by
    intro i; rw [hw'def]; dsimp only; split
    · rename_i h0; rw [h0, logDeriv_one, Differential.logDeriv_zero]
    · rfl
  -- Collection: `∑ᵢ ↑cᵢ logDeriv wᵢ = F-part + simple-pole sum` over `S`.
  set S := Finset.univ.biUnion (fun i => factorsFinset (w' i)) with hSdef
  have hcollect := sum_const_logDeriv_eq_wConst_add_pole u c w' hw'ne
  simp_rw [hlog_eq] at hcollect
  -- The `F`-part is a polynomial; so is `algebraMap a`.
  have hFpart : (∑ i, algebraMap F (RatFunc F) (c i)
      * logDeriv (algebraMap F (RatFunc F) (wConst (w' i))))
      ∈ (algebraMap F[X] (RatFunc F)).range :=
    sum_const_logDeriv_algebraMap_mem_range u c (fun i => wConst (w' i))
  obtain ⟨pF, hpF⟩ := hFpart
  obtain ⟨pa, hpa⟩ : algebraMap F (RatFunc F) a ∈ (algebraMap F[X] (RatFunc F)).range :=
    ⟨Polynomial.C a, (ratFunc_algebraMap_eq_algebraMap_C a).symm⟩
  -- `v′ + (simple-pole sum) = algebraMap a − F-part`, a polynomial.
  set P : RatFunc F := ∑ π ∈ S, algebraMap F[X] (RatFunc F)
      (Polynomial.C (∑ i, c i * poleMult (w' i) π)) * logDeriv (algebraMap F[X] (RatFunc F) π)
    with hPdef
  have hvP : v′ + P ∈ (algebraMap F[X] (RatFunc F)).range := by
    refine ⟨pa - pF, ?_⟩
    rw [map_sub, hpa, hpF, h, hcollect]; ring
  -- Membership hypotheses: every `π ∈ S` is monic irreducible.
  have hmonS : ∀ π ∈ S, π.Monic := fun π hπ => by
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hπ
    exact (factorsFinset_monic_irreducible hi).1
  have hirrS : ∀ π ∈ S, Irreducible π := fun π hπ => by
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hπ
    exact (factorsFinset_monic_irreducible hi).2
  -- Simple-pole separation: the simple-pole sum `P` is itself a polynomial.
  have hPpoly : P ∈ (algebraMap F[X] (RatFunc F)).range :=
    hsep v S (fun π => ∑ i, c i * poleMult (w' i) π) hmonS hirrS hvP
  -- Pole-independence: every residue `∑ᵢ cᵢ · poleMult w'ᵢ π = 0`, so `P = 0`.
  have hres0 : ∀ π ∈ S, (∑ i, c i * poleMult (w' i) π) = 0 :=
    poleIndependence_finset_const u hnd S hmonS hirrS _ hPpoly
  have hP0 : P = 0 := by
    rw [hPdef]
    refine Finset.sum_eq_zero fun π hπ => ?_
    rw [hres0 π hπ]; simp
  -- The `F`-part is `algebraMap F (RatFunc F) xF` for the `F`-element `xF`.
  set xF : F := ∑ i, c i * logDeriv (wConst (w' i)) with hxFdef
  have hFpart_eq : (∑ i, algebraMap F (RatFunc F) (c i)
      * logDeriv (algebraMap F (RatFunc F) (wConst (w' i))))
      = algebraMap F (RatFunc F) xF := by
    rw [hxFdef, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [logDeriv_algebraMap, ← map_mul]
  -- Conclude: `w₀ = wConst ∘ w'`, `v₀ = v`; `v′ = ↑a − ↑xF = ↑(a − xF) ∈ F`.
  refine ⟨fun i => wConst (w' i), v, ?_, ?_⟩
  · -- `↑a = F-part + P + v′ = F-part + v′` (since `P = 0`).
    rw [h, hcollect, hP0, add_zero]
  · -- `v′ = ↑a − F-part = ↑(a − xF) ∈ range (algebraMap F)`.
    refine ⟨a - xF, ?_⟩
    have hh : algebraMap F (RatFunc F) a
        = algebraMap F (RatFunc F) xF + v′ := by
      rw [h, hcollect, hFpart_eq, hP0, add_zero]
    rw [map_sub, hh]; ring

omit [CharZero F] in
/-- Given `MultiLogPoleObligation` and `IsLogRangeReduction`, `LiouvilleFDataReduction u` holds. -/
theorem fDataReduction_of_multiLogPole (u : F) (hmlp : MultiLogPoleObligation u)
    (hrange : IsLogRangeReduction u) :
    LiouvilleFDataReduction u := by
  letI := logDifferential u
  letI := logDifferentialAlgebra u
  intro a ι _ c hc w v h
  -- Multi-term pole-matching: log arguments into `F`, leaving a corrected `v₀` with `v₀′ ∈ F`.
  obtain ⟨w₀, v₁, h₁, hv₁⟩ := hmlp a ι c hc w v h
  -- The corrected `v₁` has derivative in `F`, so by the `v ∈ F` reduction `v₁ ∈ F`.
  obtain ⟨v₀, hv₀⟩ := mem_range_of_deriv_mem_range u hrange hv₁
  exact ⟨w₀, v₀, by rw [h₁, hv₀]⟩

omit [CharZero F] in
/-- `SingleLogPoleObligation` is the `ι = Fin 1` instance of `MultiLogPoleObligation`. -/
theorem singleLogPole_of_multiLogPole (u : F) (hmlp : MultiLogPoleObligation u) :
    SingleLogPoleObligation u := by
  letI := logDifferential u
  letI := logDifferentialAlgebra u
  intro a c hc w v h
  obtain ⟨w₀, v₀, h₀, hv₀⟩ :=
    hmlp a (Fin 1) (fun _ => c) (fun _ => hc) (fun _ => w) v (by simpa using h)
  exact ⟨w₀ 0, v₀, by simpa using h₀, hv₀⟩

/-- The `IsLiouville` reduction condition: `IsLiouville F (RatFunc F)` on the log extension. -/
def IsLiouvilleReductionObligation (u : F) : Prop :=
  letI := logDifferential u
  letI := logDifferentialAlgebra u
  IsLiouville F (RatFunc F)

omit [CharZero F] in
/-- `LiouvilleFDataReduction u` gives `IsLiouvilleReductionObligation u`. -/
theorem isLiouvilleReduction_of_fDataReduction (u : F)
    (hred : LiouvilleFDataReduction u) : IsLiouvilleReductionObligation u := by
  letI := logDifferential u
  letI := logDifferentialAlgebra u
  refine ⟨fun a ι _ c hc w v h => ?_⟩
  obtain ⟨w₀, v₀, h₀⟩ := hred a ι c hc w v h
  exact isLiouville_conclusion_of_ratFuncData a ι c hc w₀ v₀ h₀

omit [CharZero F] in
/-- `LiouvilleFDataReduction u` gives `IsLiouville F (RatFunc F)` on the log extension. -/
theorem isLiouville_of_fDataReduction (u : F) (hred : LiouvilleFDataReduction u) :
    letI := logDifferential u
    letI := logDifferentialAlgebra u
    IsLiouville F (RatFunc F) :=
  isLiouvilleReduction_of_fDataReduction u hred

omit [CharZero F] in
/-- Given `MultiLogPoleObligation` and `IsLogRangeReduction`, `IsLiouville F (RatFunc F)` holds. -/
theorem isLiouville_of_multiLogPole (u : F) (hmlp : MultiLogPoleObligation u)
    (hrange : IsLogRangeReduction u) :
    letI := logDifferential u
    letI := logDifferentialAlgebra u
    IsLiouville F (RatFunc F) :=
  isLiouvilleReduction_of_fDataReduction u
    (fDataReduction_of_multiLogPole u hmlp hrange)

omit [CharZero F] in
/-- `IsLiouvilleReductionObligation u` gives `IsLiouville F (RatFunc F)` on the log extension. -/
theorem keystone (u : F) (hreduction : IsLiouvilleReductionObligation u) :
    letI := logDifferential u
    letI := logDifferentialAlgebra u
    IsLiouville F (RatFunc F) :=
  hreduction

omit [CharZero F] in
/-- For constant `b` (`b′ = 0`), `(↑b · t)′ = ↑b · ↑(logDeriv u)`. -/
theorem deriv_algebraMap_mul_X (u : F) {b : F} (hb : b′ = 0) :
    letI := logDifferential u
    letI := logDifferentialAlgebra u
    (algebraMap F (RatFunc F) b * algebraMap F[X] (RatFunc F) X)′
      = algebraMap F (RatFunc F) b * algebraMap F (RatFunc F) (logDeriv u) := by
  letI := logDifferential u
  letI := logDifferentialAlgebra u
  rcases eq_or_ne b 0 with rfl | hbne
  · simp
  have hbA : algebraMap F (RatFunc F) b ≠ 0 := RatFunc.algebraMap_ne_zero (by
    simpa using (FaithfulSMul.algebraMap_injective F (RatFunc F)).ne hbne)
  have hXA : algebraMap F[X] (RatFunc F) X ≠ 0 := RatFunc.algebraMap_ne_zero X_ne_zero
  -- `(↑b·t)′ = (↑b·t)·logDeriv(↑b·t)`, `logDeriv(↑b·t) = logDeriv ↑b + logDeriv t`.
  have hmulne : algebraMap F (RatFunc F) b * algebraMap F[X] (RatFunc F) X ≠ 0 :=
    mul_ne_zero hbA hXA
  have hv'eq : (algebraMap F (RatFunc F) b * algebraMap F[X] (RatFunc F) X)′
      = (algebraMap F (RatFunc F) b * algebraMap F[X] (RatFunc F) X)
        * logDeriv (algebraMap F (RatFunc F) b * algebraMap F[X] (RatFunc F) X) := by
    rw [logDeriv, mul_div_cancel₀ _ hmulne]
  -- `logDeriv ↑b = ↑(logDeriv b) = 0`, `logDeriv t = ↑(C(u'/u))/t`.
  have hlogb : logDeriv (algebraMap F (RatFunc F) b) = 0 := by
    rw [logDeriv_algebraMap, logDeriv, hb, zero_div, map_zero]
  have hlogX : logDeriv (algebraMap F[X] (RatFunc F) X)
      = algebraMap F (RatFunc F) (logDeriv u) / algebraMap F[X] (RatFunc F) X := by
    rw [logDeriv_algebraMap_eq u X, logDerivPoly_X, ← ratFunc_algebraMap_eq_algebraMap_C]
  have hlogmul : logDeriv (algebraMap F (RatFunc F) b * algebraMap F[X] (RatFunc F) X)
      = algebraMap F (RatFunc F) (logDeriv u) / algebraMap F[X] (RatFunc F) X := by
    rw [Differential.logDeriv_mul _ _ hbA hXA, hlogb, hlogX, zero_add]
  rw [hv'eq, hlogmul]
  field_simp

/-- Given `NondegenerateLog u` and `MultiLogPoleObligation u`, `IsLiouville F (RatFunc F)` holds
on the log extension. -/
theorem isLiouville_of_nondegenerateLog (u : F) (hnd : NondegenerateLog u)
    (hmlp : MultiLogPoleObligation u) :
    letI := logDifferential u
    letI := logDifferentialAlgebra u
    IsLiouville F (RatFunc F) := by
  letI := logDifferential u
  letI := logDifferentialAlgebra u
  refine ⟨fun a ι _ c hc w v h => ?_⟩
  -- Multi-term pole-matching: log arguments into `F`, leaving a corrected `v₀` with `v₀′ ∈ F`.
  obtain ⟨w₀, v₀, h₀, hv₀⟩ := hmlp a ι c hc w v h
  -- Corrected `v`-reduction: `v₀ = ↑vF + ↑b·t` with `b` constant.
  obtain ⟨vF, b, hbconst, hv₀eq⟩ := deriv_mem_range_imp_linear u hnd hv₀
  -- `v₀′ = (↑vF)′ + ↑b·logDeriv(↑u)` (additivity + `deriv_algebraMap` + `deriv_algebraMap_mul_X`).
  have hv₀' : v₀′ = (algebraMap F (RatFunc F) vF)′
      + algebraMap F (RatFunc F) b * algebraMap F (RatFunc F) (logDeriv u) := by
    rw [hv₀eq, map_add, deriv_algebraMap_mul_X u hbconst]
  -- Assemble the fresh `F`-data over `Option ι`: `none ↦ b·log u`, `some x ↦ cₓ·log(w₀ x)`.
  refine ⟨Option ι, inferInstance, fun x => x.elim b c, ?_, fun x => x.elim u w₀, vF, ?_⟩
  · rintro (_ | x) <;> simp [hbconst, hc]
  · apply FaithfulSMul.algebraMap_injective F (RatFunc F)
    rw [map_add, ← deriv_algebraMap, Fintype.sum_option]
    simp only [Option.elim, map_add, map_sum]
    have hsum : ∀ x, algebraMap F (RatFunc F) (c x * logDeriv (w₀ x))
        = algebraMap F (RatFunc F) (c x) * logDeriv (algebraMap F (RatFunc F) (w₀ x)) := by
      intro x; rw [map_mul, ← logDeriv_algebraMap]
    simp_rw [hsum]
    -- `↑a = ↑b·logDeriv ↑u + ∑ ↑cᵢ logDeriv(↑w₀ᵢ) + (↑vF)′`, matching `h₀` + `hv₀'`.
    rw [h₀, hv₀', map_mul]
    ring

/-- Given `NondegenerateLog u` and `DerivSimplePoleSeparation u`, `IsLiouville F (RatFunc F)` holds
on the log extension. -/
theorem isLiouville_logExtension (u : F) (hnd : NondegenerateLog u)
    (hsep : DerivSimplePoleSeparation u) :
    letI := logDifferential u
    letI := logDifferentialAlgebra u
    IsLiouville F (RatFunc F) :=
  isLiouville_of_nondegenerateLog u hnd (multiLogPoleObligation_of_nondegenerateLog u hnd hsep)

/-- Given `NondegenerateLog u` alone, `IsLiouville F (RatFunc F)` holds on the log extension
`F(log u) = RatFunc F`. -/
theorem isLiouville_logExtension_uncond (u : F) (hnd : NondegenerateLog u) :
    letI := logDifferential u
    letI := logDifferentialAlgebra u
    IsLiouville F (RatFunc F) :=
  isLiouville_logExtension u hnd (derivSimplePoleSeparation_of_nondegenerateLog u hnd)

-- Restatements pinning the genuine field setup.
-- `t' = u'/u` on `RatFunc F` itself (the log monomial, on the fraction field):
example (u : F) :
    letI := logDifferential u
    (algebraMap F[X] (RatFunc F) X)′ = algebraMap F[X] (RatFunc F) (C (logDeriv u)) := by
  have := derivExtends u X
  simpa [logDerivPoly_X] using this
-- The setup is a genuine differential field extension: `D` commutes with `algebraMap F (RatFunc F)`.
example (u : F) (a : F) :
    letI := logDifferential u
    letI := logDifferentialAlgebra u
    (algebraMap F (RatFunc F) a)′ = algebraMap F (RatFunc F) a′ :=
  letI := logDifferential u
  letI := logDifferentialAlgebra u
  deriv_algebraMap a
-- The keystone genuinely closes from the single pole-matching residual: discharging
-- `LiouvilleFDataReduction u` yields the real `IsLiouville F (RatFunc F)` instance.
example (u : F) (hred : LiouvilleFDataReduction u) :
    letI := logDifferential u
    letI := logDifferentialAlgebra u
    IsLiouville F (RatFunc F) :=
  isLiouville_of_fDataReduction u hred
-- The `v ∈ F` reduction: `v′ ∈ F ⟹ v ∈ F` on `RatFunc F`, modulo the two stated residues.
example (u : F) (hrtp : RationalToPolyObligation u) (hpv : PolyVReductionObligation u)
    (hu : logDeriv u ≠ 0) :
    letI := logDifferential u
    ∀ {v : RatFunc F}, v′ ∈ (algebraMap F (RatFunc F)).range →
      v ∈ (algebraMap F (RatFunc F)).range :=
  mem_range_of_deriv_mem_range u ⟨hrtp, hpv, hu⟩
-- The keystone closes from the multi-term pole-matching core: discharging `MultiLogPoleObligation`
-- (+ the `v ∈ F` residues) yields the real `IsLiouville F (RatFunc F)` instance.
example (u : F) (hmlp : MultiLogPoleObligation u) (hrtp : RationalToPolyObligation u)
    (hpv : PolyVReductionObligation u) (hu : logDeriv u ≠ 0) :
    letI := logDifferential u
    letI := logDifferentialAlgebra u
    IsLiouville F (RatFunc F) :=
  isLiouville_of_multiLogPole u hmlp ⟨hrtp, hpv, hu⟩
-- `PoleIndependenceObligation` follows from nonvanishing of `D πⱼ` on every irreducible factor.
example (u : F)
    (hDne : letI := logDifferential u; ∀ {ιπ : Type} [Fintype ιπ] (π : ιπ → F[X]),
      (∀ j, Irreducible (π j)) → ∀ j, logDerivPoly u (π j) ≠ 0) :
    PoleIndependenceObligation u := by
  letI := logDifferential u
  intro ιπ _ π d hmon hirr hinj hdeg hpoly
  exact poleIndependence_of_logDerivPoly_ne_zero u π d hmon hirr hinj hdeg
    (hDne π hirr) hpoly
-- `NondegenerateLog u` supplies both rational-to-polynomial pole descent and pole independence.
example (u : F) (hnd : NondegenerateLog u) : RationalToPolyObligation u :=
  rationalToPolyObligation_of_nondegenerateLog u hnd
example (u : F) (hnd : NondegenerateLog u) : PoleIndependenceObligation u :=
  poleIndependenceObligation_of_nondegenerateLog u hnd
-- `NondegenerateLog u` plus multi-term pole matching yields `IsLiouville F (RatFunc F)`.
example (u : F) (hnd : NondegenerateLog u) (hmlp : MultiLogPoleObligation u) :
    letI := logDifferential u
    letI := logDifferentialAlgebra u
    IsLiouville F (RatFunc F) :=
  isLiouville_of_nondegenerateLog u hnd hmlp
-- `MultiLogPoleObligation` follows from nondegeneracy plus separation of simple logarithmic poles.
example (u : F) (hnd : NondegenerateLog u) (hsep : DerivSimplePoleSeparation u) :
    MultiLogPoleObligation u :=
  multiLogPoleObligation_of_nondegenerateLog u hnd hsep
-- Conditional form using `NondegenerateLog u` and simple-pole separation.
example (u : F) (hnd : NondegenerateLog u) (hsep : DerivSimplePoleSeparation u) :
    letI := logDifferential u
    letI := logDifferentialAlgebra u
    IsLiouville F (RatFunc F) :=
  isLiouville_logExtension u hnd hsep
-- The simple-pole separation is now a THEOREM from `NondegenerateLog` (the twisted derivative `v′` has
-- no simple `t`-pole), discharging the last residual.
example (u : F) (hnd : NondegenerateLog u) : DerivSimplePoleSeparation u :=
  derivSimplePoleSeparation_of_nondegenerateLog u hnd
-- THE KEYSTONE, UNCONDITIONAL: a genuine new log monomial (`NondegenerateLog u`, = `log u ∉ F`) alone
-- yields the real `IsLiouville F (RatFunc F)` — nothing else is assumed.
example (u : F) (hnd : NondegenerateLog u) :
    letI := logDifferential u
    letI := logDifferentialAlgebra u
    IsLiouville F (RatFunc F) :=
  isLiouville_logExtension_uncond u hnd

end FieldObligations

end DeepWiki.SymbolicIntegration.LiouvilleLog
