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

/-- **Definition 3.4.3** (§3.4, p.98): `u ∈ F` is a *logarithmic derivative of an `F`-radical* if
`n·u = Dv/v` for some `v ∈ F*` and some nonzero integer `n` — i.e. `u` is, up to an integer scale,
the logarithmic derivative `logDeriv v = v′/v` of a nonzero element. -/
def IsLogDerivRadical {F : Type*} [Field F] [Differential F] (u : F) : Prop :=
  ∃ (v : F) (n : ℤ), v ≠ 0 ∧ n ≠ 0 ∧ (n : F) * u = Differential.logDeriv v

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

section FirstKind
-- `Ω` is a differential extension of `k` containing every root we test against — the algebraic
-- closure in the book; here it is left as a differential extension parameter.
variable {Ω : Type*} [Field Ω] [Differential Ω] [Algebra k Ω]

/-- The *residue* `pα(α)` of the monomial derivation `Dt = v` at a root `α ∈ Ω`. The book's
`pα = (Dt − Dα)/(t − α) ∈ k(α)[t]` evaluates at its argument to `v'(α)` (it is the derivative of
`Dt − Dα` at its root `α`), so we take this closed form; `residue_eq_eval_divByMonic` proves the
agreement with `pα(α)`. -/
noncomputable def residue (v : k[X]) (α : Ω) : Ω := aeval α (derivative v)

/-- **Definition 3.4.4** (§3.4, p.98): `q ∈ k[t]` is *special of the first kind* (w.r.t. the
monomial derivation `Dt = v`), tested over the differential extension `Ω`, if `q` is special
(`q ∣ Dq`) and at every root `α ∈ Ω` of `q` the residue `pα(α) = v'(α)` is not a logarithmic
derivative of an `Ω`-radical. (By Lemma 3.4.8 testing over `Ω = k̄` is equivalent to testing over
each `k(α)`.) -/
def IsSpecialFirstKind (v : k[X]) (q : k[X]) : Prop :=
  q ∣ Differential.implicitDeriv v q ∧
    ∀ α : Ω, aeval α q = 0 → ¬ IsLogDerivRadical (residue (Ω := Ω) v α)

variable (Ω) in
/-- A special-of-the-first-kind polynomial is special (`q ∣ Dq`). -/
theorem IsSpecialFirstKind.isSpecial {v q : k[X]} (h : IsSpecialFirstKind (Ω := Ω) v q) :
    q ∣ Differential.implicitDeriv v q := h.1

variable (Ω) in
/-- **Theorem 3.4.4(i)** (§3.4, p.99): `S₁` is closed under finite products — a finite product of
special-first-kind polynomials is special of the first kind. Each root of `∏ fᵢ` is a root of some
`fᵢ` (the value is `∏ fᵢ(α)`, zero in a domain iff a factor vanishes), and specialness multiplies
(`IsSpecial.prod`). -/
theorem isSpecialFirstKind_prod {ι : Type*} (s : Finset ι) (v : k[X]) (f : ι → k[X])
    (hf : ∀ i ∈ s, IsSpecialFirstKind (Ω := Ω) v (f i)) :
    IsSpecialFirstKind (Ω := Ω) v (∏ i ∈ s, f i) := by
  letI : Differential k[X] := ⟨Differential.implicitDeriv v⟩
  refine ⟨IsSpecial.prod s f (fun i hi => (hf i hi).1), ?_⟩
  intro α hα hlog
  rw [map_prod] at hα
  obtain ⟨i, hi, hroot⟩ := Finset.prod_eq_zero_iff.mp hα
  exact (hf i hi).2 α hroot hlog

variable (Ω) in
open Classical in
/-- **Theorem 3.4.4(ii)** (§3.4, p.99): a divisor of a special-first-kind polynomial is special of
the first kind. Each root of `q ∣ p` is a root of `p`, and a divisor of a special polynomial is
special (`isSpecial_of_dvd`; char `0` makes every prime-power multiplicity a unit). -/
theorem isSpecialFirstKind_of_dvd [CharZero k] {v p q : k[X]} (hp0 : p ≠ 0)
    (hp : IsSpecialFirstKind (Ω := Ω) v p) (hdvd : q ∣ p) :
    IsSpecialFirstKind (Ω := Ω) v q := by
  letI : Differential k[X] := ⟨Differential.implicitDeriv v⟩
  have hmult : ∀ π, Prime π → π ∣ p → IsUnit ((multiplicity π p : k[X])) := by
    intro π hπ hπp
    rw [← C_eq_natCast]
    exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr
      (Nat.cast_ne_zero.mpr (by have := multiplicity_pos_of_dvd hπp; omega)))
  refine ⟨isSpecial_of_dvd hp0 hp.1 hmult hdvd, ?_⟩
  intro α hα hlog
  have hroot : aeval α p = 0 := by
    obtain ⟨r, rfl⟩ := hdvd; rw [map_mul, hα, zero_mul]
  exact hp.2 α hroot hlog

/-- For a polynomial `f` with root `a`, `(f /ₘ (X − a))(a) = f'(a)`: the value of the exact
quotient at a simple level equals the formal derivative there (`f = (X − a)·g`, so
`f' = g + (X − a)·g'`, and `(X − a)` vanishes at `a`). -/
theorem eval_divByMonic_X_sub_C_eq_eval_derivative {A : Type*} [Field A] (f : A[X]) (a : A)
    (h : f.IsRoot a) : (f /ₘ (X - C a)).eval a = (derivative f).eval a := by
  set g := f /ₘ (X - C a) with hg
  have hfac : f = (X - C a) * g := (mul_divByMonic_eq_iff_isRoot.mpr h).symm
  have hderiv : derivative f = g + (X - C a) * derivative g := by
    rw [hfac, derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul]
  rw [hderiv, eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero]

/-- **Definition 3.4.4** faithfulness (§3.4, p.98): at a *special* root `α` (where `v(α) = α′`, so
`t − α ∣ Dt − Dα` and the book's `pα` is a genuine polynomial), the closed-form `residue v α`
equals the book's `pα(α) = ((Dt − Dα)/(t − α))(α)`. -/
theorem residue_eq_eval_divByMonic [DifferentialAlgebra k Ω] (v : k[X]) (α : Ω)
    (hsp : aeval α v = α′) :
    residue (Ω := Ω) v α
      = (Differential.implicitDeriv (v.map (algebraMap k Ω)) (X - C α) /ₘ (X - C α)).eval α := by
  have hpα : Differential.implicitDeriv (v.map (algebraMap k Ω)) (X - C α)
      = v.map (algebraMap k Ω) - C α′ := implicitDeriv_X_sub_C _ α
  have hroot : (v.map (algebraMap k Ω) - C α′).IsRoot α := by
    rw [IsRoot.def, eval_sub, eval_map, eval_C, ← aeval_def, hsp, sub_self]
  rw [hpα, eval_divByMonic_X_sub_C_eq_eval_derivative _ α hroot, derivative_sub, derivative_C,
    sub_zero, residue, derivative_map, eval_map, ← aeval_def]

end FirstKind

section AlgebraicExtension
-- `E` an algebraic differential extension of `k`, both inside the common closure `Ω`.
variable {E : Type*} [Field E] [Differential E] [Algebra k E] [DifferentialAlgebra k E]

/-- `mapCoeffs` commutes with base change along a differential-algebra hom: applying `D` to the
coefficients and then mapping equals mapping then applying `D` (`deriv_algebraMap` coefficientwise). -/
theorem mapCoeffs_map (p : k[X]) :
    (Differential.mapCoeffs p).map (algebraMap k E)
      = Differential.mapCoeffs (p.map (algebraMap k E)) := by
  ext i
  rw [coeff_map, Differential.coeff_mapCoeffs, Differential.coeff_mapCoeffs, coeff_map,
    deriv_algebraMap]

/-- The monomial derivation commutes with base change: `(D[v] p).map = D[v.map] (p.map)`
(`mapCoeffs` commutes, and `v·p'` maps to `(v.map)·(p.map)'`). -/
theorem implicitDeriv_map (v p : k[X]) :
    (Differential.implicitDeriv v p).map (algebraMap k E)
      = Differential.implicitDeriv (v.map (algebraMap k E)) (p.map (algebraMap k E)) := by
  have h1 : Differential.implicitDeriv v p = Differential.mapCoeffs p + v * derivative p := by
    simp [Differential.implicitDeriv, derivative']
  have h2 : Differential.implicitDeriv (v.map (algebraMap k E)) (p.map (algebraMap k E))
      = Differential.mapCoeffs (p.map (algebraMap k E))
        + (v.map (algebraMap k E)) * derivative (p.map (algebraMap k E)) := by
    simp [Differential.implicitDeriv, derivative']
  rw [h1, h2, Polynomial.map_add, Polynomial.map_mul, mapCoeffs_map, derivative_map]

/-- **Corollary 3.4.1** (§3.4, p.95), special half: a special polynomial stays special after an
algebraic base change — `p ∣ Dp` in `k[t]` gives `p.map ∣ D(p.map)` in `E[t]` (`map` is a ring hom
preserving divisibility, and `D` commutes with `map`). -/
theorem isSpecial_map_of_isSpecial {v p : k[X]} (hp : p ∣ Differential.implicitDeriv v p) :
    (p.map (algebraMap k E)) ∣
      Differential.implicitDeriv (v.map (algebraMap k E)) (p.map (algebraMap k E)) := by
  rw [← implicitDeriv_map]; exact Polynomial.map_dvd _ hp

section ThreeKind
-- ... viewed inside the common closure `Ω` (`k ⊆ E ⊆ Ω`).
variable {Ω : Type*} [Field Ω] [Differential Ω] [Algebra k Ω] [Algebra E Ω] [IsScalarTower k E Ω]

omit [Differential k] [Differential E] [DifferentialAlgebra k E] [Differential Ω] in
/-- The residue is invariant under the intermediate base change `k → E`: `pα(α)` computed for the
mapped monomial `v.map` equals the one for `v` (the scalar tower collapses the evaluation). -/
theorem residue_map (v : k[X]) (α : Ω) :
    residue (Ω := Ω) (v.map (algebraMap k E)) α = residue (Ω := Ω) v α := by
  rw [residue, residue, derivative_map,
    ← aeval_eq_aeval_map (IsScalarTower.algebraMap_eq k E Ω).symm (derivative v) α]

/-- **Theorem 3.4.4(iii)** (§3.4, p.99): `S₁` grows with the field — if `E` is an algebraic
extension of `k`, a polynomial that is special of the first kind over `k[t]` stays special of the
first kind over `E[t]` (`S₁,k[t]:k ⊆ S₁,E[t]:E`). The polynomial stays special (Cor 3.4.1), and the
residue/root test is unchanged because we test log-derivatives over the common closure `Ω` — the
Lemma 3.4.8 step of the book is absorbed into testing over `Ω`. -/
theorem isSpecialFirstKind_map [Algebra.IsAlgebraic k Ω] {v p : k[X]}
    (hp : IsSpecialFirstKind (Ω := Ω) v p) :
    IsSpecialFirstKind (Ω := Ω) (v.map (algebraMap k E)) (p.map (algebraMap k E)) := by
  refine ⟨isSpecial_map_of_isSpecial hp.1, ?_⟩
  intro α hα hlog
  have hroot : aeval α p = 0 := by
    rwa [aeval_eq_aeval_map (IsScalarTower.algebraMap_eq k E Ω).symm p α]
  rw [residue_map] at hlog
  exact hp.2 α hroot hlog

end ThreeKind

end AlgebraicExtension

end DeepWiki.SymbolicIntegration
