import DeepWiki.SymbolicIntegration.MonomialExtensions

/-! # Special polynomials of the first kind (Bronstein §3.4)
The *first-kind* special polynomials refine `IsSpecial` by a residue test on the roots: a special
`p ∈ k[t]` is *of the first kind* when, at every root `α` of `p` (in the algebraic closure), the
residue `Dt − Dα` evaluated at `α` is not the logarithmic derivative of a radical in `k(α)`. This
file develops the supporting notion of a *logarithmic derivative of a radical*
(`IsLogDerivRadical`, Def 3.4.3), its descent through algebraic extensions (Lemma 3.4.8), and the
definition and semigroup structure of the first-kind class (Def 3.4.4, Thm 3.4.4). -/

open scoped Differential
open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {k : Type*} [Field k] [Differential k]

/-- **Definition 3.4.3** (§3.4, p.98): `u ∈ k` is a *logarithmic derivative of a `k`-radical* if
`n·u = Dv/v` for some `v ∈ k*` and some nonzero integer `n` — i.e. `u` is, up to an integer scale,
the logarithmic derivative `logDeriv v = v′/v` of a nonzero element. -/
def IsLogDerivRadical (u : k) : Prop :=
  ∃ (v : k) (n : ℤ), v ≠ 0 ∧ n ≠ 0 ∧ (n : k) * u = Differential.logDeriv v

/-- Spelled out: `u` is a log-derivative of a radical iff `n·u = v′/v` for some `v ≠ 0`, `n ≠ 0`. -/
theorem isLogDerivRadical_iff {u : k} :
    IsLogDerivRadical u ↔ ∃ (v : k) (n : ℤ), v ≠ 0 ∧ n ≠ 0 ∧ (n : k) * u = v′ / v :=
  Iff.rfl

/-- `0` is a log-derivative of a radical (`1·0 = logDeriv 1 = 0`). -/
theorem isLogDerivRadical_zero : IsLogDerivRadical (0 : k) :=
  ⟨1, 1, one_ne_zero, one_ne_zero, by simp⟩

/-- The logarithmic derivative of any nonzero `v` is a log-derivative of a radical (`n = 1`). -/
theorem isLogDerivRadical_logDeriv {v : k} (hv : v ≠ 0) :
    IsLogDerivRadical (Differential.logDeriv v) :=
  ⟨v, 1, hv, one_ne_zero, by rw [Int.cast_one, one_mul]⟩

/-- **Definition 3.4.3** normalization (§3.4, p.98): the integer `n` may be taken *positive*. If
`n·u = Dv/v` with `n < 0`, then `(−n)·u = D(v⁻¹)/v⁻¹` using `logDeriv (v⁻¹) = −logDeriv v`, so a
witness with positive multiplier exists. -/
theorem isLogDerivRadical_pos {u : k} (h : IsLogDerivRadical u) :
    ∃ (v : k) (n : ℤ), v ≠ 0 ∧ 0 < n ∧ (n : k) * u = Differential.logDeriv v := by
  obtain ⟨v, n, hv, hn, heq⟩ := h
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · refine ⟨v⁻¹, -n, inv_ne_zero hv, by omega, ?_⟩
    have hlog : Differential.logDeriv v⁻¹ = -Differential.logDeriv v := by
      have := Differential.logDeriv_div (1 : k) v one_ne_zero hv
      simpa using this
    rw [hlog, Int.cast_neg, neg_mul, ← heq]
  · exact ⟨v, n, hv, hpos, heq⟩

/-- **Lemma 3.4.8** (§3.4, p.98): logarithmic-derivative-of-a-radical descends through algebraic
extensions. If `E` is algebraic over `k` and `a ∈ k` is *not* a log-derivative of a `k`-radical,
then `a` is not a log-derivative of an `E`-radical either. Proof: from `n·a = Dα/α` for some
`α ∈ E*`, the minimal polynomial `p = X^m + ΣaᵢXⁱ` of `α` over `k` satisfies `p ∣ q` for
`q = mna·X^m + Σ(Daᵢ + i·n·a·aᵢ)Xⁱ ∈ k[X]` (since `q(α) = D(p(α)) = 0`); degrees force `q = mna·p`,
so comparing constant terms gives `Da₀ = m·n·a·a₀`, i.e. `(m·n)·a = logDeriv a₀` with `a₀ ≠ 0`
(as `α ≠ 0`) and `m·n ≠ 0` — a `k`-radical witness, contradiction. (Characteristic `0`, as in §3.4.) -/
theorem isLogDerivRadical_descent [CharZero k]
    {E : Type*} [Field E] [Differential E] [Algebra k E] [DifferentialAlgebra k E]
    [Algebra.IsAlgebraic k E] {a : k} (ha : ¬ IsLogDerivRadical a) :
    ¬ ∃ (α : E) (n : ℤ), α ≠ 0 ∧ n ≠ 0 ∧ (n : E) * algebraMap k E a = Differential.logDeriv α := by
  rintro ⟨α, n, hα, hn, heq⟩
  have hane : a ≠ 0 := fun h => ha ⟨1, 1, one_ne_zero, one_ne_zero, by simp [h]⟩
  set na : k := (n : k) * a with hnadef
  -- `Dα = (algebraMap k E na)·α`
  have hαderiv : α′ = algebraMap k E na * α := by
    have h1 : (n : E) * algebraMap k E a = α′ / α := heq
    have h2 : (n : E) * algebraMap k E a * α = α′ := by rw [h1]; field_simp
    rw [← h2, hnadef, map_mul, map_intCast]
  -- the minimal polynomial `p` of `α` over `k` and the auxiliary `q ∈ k[X]`
  have hint : IsIntegral k α := (Algebra.IsAlgebraic.isAlgebraic α).isIntegral
  set p := minpoly k α with hpdef
  have hpmonic : p.Monic := minpoly.monic hint
  have hpaeval : aeval α p = 0 := minpoly.aeval k α
  set m := p.natDegree with hmdef
  have hmpos : 1 ≤ m := minpoly.natDegree_pos hint
  set q : k[X] := Differential.mapCoeffs p + C na * (X * derivative p) with hqdef
  -- `q(α) = D(p(α)) = 0`
  have haevalq : aeval α q = 0 := by
    have hD : (aeval α p)′ = aeval α (Differential.mapCoeffs p)
        + aeval α (derivative p) * α′ := Differential.deriv_aeval_eq α p
    rw [hpaeval, show ((0 : E)′) = 0 from by simp] at hD
    rw [hqdef]
    simp only [map_add, map_mul, aeval_C, aeval_X]
    rw [hαderiv] at hD
    linear_combination -hD
  have hpdvd : p ∣ q := minpoly.dvd k α haevalq
  -- coefficient computations: `q.coeff 0 = a₀′`, `q.coeff m = m·na`
  have ha0 : p.coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hα
  have hcoeff0 : q.coeff 0 = (p.coeff 0)′ := by
    rw [hqdef, coeff_add, Differential.coeff_mapCoeffs, coeff_C_mul]
    have hzero : (X * derivative p).coeff 0 = 0 := by simp
    rw [hzero, mul_zero, add_zero]
  have hpcm : p.coeff m = 1 := by rw [hmdef]; exact hpmonic.coeff_natDegree
  have hmapdeg : (Differential.mapCoeffs p).coeff m = 0 := by
    rw [Differential.coeff_mapCoeffs, hpcm]; simp
  have hXderiv : (X * derivative p).coeff m = (m : k) := by
    obtain ⟨j, hj⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    rw [hj, coeff_X_mul, coeff_derivative,
      show p.coeff (j + 1) = p.coeff m from by rw [hj], hpcm, one_mul]
    push_cast; ring
  have hcoeffm : q.coeff m = (m : k) * na := by
    rw [hqdef, coeff_add, hmapdeg, zero_add, coeff_C_mul, hXderiv, mul_comm]
  have hmna : (m : k) * na ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr (by omega))
      (mul_ne_zero (Int.cast_ne_zero.mpr hn) hane)
  have hqne : q ≠ 0 := fun h => hmna (by rw [← hcoeffm, h, coeff_zero])
  -- degrees: `natDegree q ≤ m`, so `q = C c · p`
  have hdegbound : q.natDegree ≤ m := by
    rw [hqdef]
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · exact natDegree_le_iff_coeff_eq_zero.mpr fun N hN => by
        rw [Differential.coeff_mapCoeffs, coeff_eq_zero_of_natDegree_lt (by omega : m < N)]; simp
    · refine (natDegree_C_mul_le na _).trans (natDegree_mul_le.trans ?_)
      have := natDegree_derivative_le p
      simp only [natDegree_X]; omega
  obtain ⟨s, hs⟩ := hpdvd
  have hsne : s ≠ 0 := fun h => hqne (by rw [hs, h, mul_zero])
  have hsdeg : s.natDegree = 0 := by
    have hnd := hpmonic.natDegree_mul' hsne
    rw [← hs, ← hmdef] at hnd; omega
  obtain ⟨c, hc⟩ : ∃ c, s = C c := ⟨s.coeff 0, eq_C_of_natDegree_eq_zero hsdeg⟩
  -- compare constant and leading terms of `q = C c · p`
  have hqc0 : q.coeff 0 = c * p.coeff 0 := by rw [hs, hc, mul_comm, coeff_C_mul]
  have hcval : c = (m : k) * na := by
    rw [show c = q.coeff m from by rw [hs, hc, mul_comm, coeff_C_mul, hpcm, mul_one], hcoeffm]
  have hkey : (p.coeff 0)′ = ((m : k) * na) * p.coeff 0 := by rw [← hcoeff0, hqc0, hcval]
  -- this is a `k`-radical witness for `a`, contradicting `ha`
  refine ha ⟨p.coeff 0, (m : ℤ) * n, ha0,
    mul_ne_zero (Int.natCast_ne_zero.mpr (by omega)) hn, ?_⟩
  rw [Differential.logDeriv, hkey, mul_div_assoc, div_self ha0, mul_one, hnadef]
  push_cast; ring

end DeepWiki.SymbolicIntegration
