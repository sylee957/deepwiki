import DeepWiki.SymbolicIntegration.SpecialFirstKind

/-! # Constants of a monomial extension and base change (Bronstein §3.4)
For a monomial `t` over `(k, D)` (so `Dt = v ∈ k[t]`), this file relates the *constants* of
`k(t)` to the *special* polynomials. When `Dt ∈ k` a nonzero `p ∈ k[t]` is special iff its monic
associate is a constant (`isSpecial_iff_deriv_monic_eq_zero`); this is the engine behind the fact
that any new constant in `k(t) ∖ k` makes `Sⁱʳʳ` nonempty. We also complete the base-change
corollary (normal polynomials stay normal under an algebraic extension `k ⊆ E`), and record the
constant-field case `Da = 0`. -/

open scoped Differential
open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {k : Type*} [Field k] [Differential k]

section Coprime
variable {R : Type*} [CommRing R] [Differential R]

/-- **Lemma 3.4.5 core** (§3.4, p.96): if `a, b` are coprime and the numerator of `D(a/b)`
vanishes (`b·Da = a·Db`), then both `a` and `b` are special. From `a ∣ b·Da` (`= a·Db`) and
`IsCoprime a b` we get `a ∣ Da`; symmetrically `b ∣ Db`. -/
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
/-- **Lemma 3.4.5** (§3.4, p.96), first part: if `c = a/b ∈ Const_D(k(t))` (i.e. `c′ = 0`) with
`a, b` coprime and `b ≠ 0`, then both the numerator `a` and the denominator `b` are special in
`k[t]`. From the quotient rule `0 = Dc = (b·Da − a·Db)/b²` we get `b·Da = a·Db`, and coprimality
forces `a ∣ Da`, `b ∣ Db` (`isSpecial_of_coprime_of_deriv_quotient_num_eq_zero`). -/
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
-- `v·dp/dt`, so `lc(Dp) = (deg p)·lc(p)·lc(v)` for `deg p ≥ 1` — the engine of Lemma 3.4.5's
-- equal-degree claim.
variable {F : Type*} [Field F] [CharZero F] [Differential F]

/-- For a *nonlinear* monomial (`deg v ≥ 2`) and `deg p ≥ 1`, the leading coefficient of `Dp` is
`(deg p)·lc(p)·lc(v)` — the leading term comes entirely from `v·dp/dt`. -/
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

/-- For a *nonlinear* monomial (`deg v ≥ 2`), a special divisor cofactor `g = Dp/p` of a nonzero
`p` reads off the degree of `p`: when `deg p ≥ 1`, `g.leadingCoeff = (deg p)·lc(v)` and
`deg g = δ(t) − 1`; when `deg p = 0`, `deg g = 0`. (From `Dp = p·g` and the leading-coefficient
formula for `Dp`.) -/
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

end Nonlinear

section ScalarMonomial
-- The base case of §3.4: the monomial derivation with `Dt = w ∈ k`, i.e. the implicit derivation
-- whose `t`-component is the *constant* polynomial `C w`.
variable (w : k)

/-- For the monomial derivation with `Dt = w ∈ k` (so `D = κ_D + w·d/dt`), the `t`-component does
not raise degree: `deg(Dp) ≤ deg p` (`κ_D` preserves degree shape; `w·dp/dt` drops a degree). -/
theorem natDegree_implicitDeriv_C_le (p : k[X]) :
    (Differential.implicitDeriv (C w) p).natDegree ≤ p.natDegree := by
  refine (natDegree_implicitDeriv_le (C w) p).trans ?_
  rw [natDegree_C]; simp

/-- The top coefficient of `Dp` is `D(lc p)`: when `Dt = w ∈ k`, the degree-`deg p` coefficient of
`Differential.implicitDeriv (C w) p` is the derivative of the leading coefficient of `p`. -/
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

/-- For the monomial derivation with `Dt = w ∈ k`, a *monic* polynomial has `deg(Dq) < deg q`
unless `Dq = 0` (the top coefficient `D(lc q) = D(1) = 0`). -/
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

/-- **Constants vs special, monic-associate form** (§3.4, p.96): with `Dt = w ∈ k`, a *monic*
`q ∈ k[t]` is special iff it is a constant of `k(t)` — `q ∣ Dq ⟺ Dq = 0`. (Forward: `q ∣ Dq` and
`deg(Dq) < deg q` force `Dq = 0`; backward: `Dq = 0 ⟹ q ∣ Dq`.) -/
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

/-- **Constants and special polynomials** (§3.4, p.96, Lemma 3.4.6): when `Dt ∈ k`, a nonzero
`p ∈ k[t]` is special iff its monic normalization `p/lc(p)` is a constant of `k(t)` —
`p ∣ Dp ⟺ D(p/lc(p)) = 0`. (Specialness is an associate invariant, reducing to the monic case
`isSpecial_iff_deriv_eq_zero_of_monic`.) -/
theorem isSpecial_iff_deriv_normalize_eq_zero {w : k} {p : k[X]} (hp : p ≠ 0) :
    p ∣ Differential.implicitDeriv (C w) p
      ↔ Differential.implicitDeriv (C w) (p * C p.leadingCoeff⁻¹) = 0 := by
  letI : Differential k[X] := ⟨Differential.implicitDeriv (C w)⟩
  obtain ⟨hassoc, hmonic⟩ := associated_mul_C_inv_leadingCoeff hp
  rw [← isSpecial_iff_deriv_eq_zero_of_monic hmonic]
  exact ⟨fun h => IsSpecial.of_associated hassoc h, fun h => IsSpecial.of_associated hassoc.symm h⟩

section AlgebraicExtension
-- `E` an algebraic differential extension of `k`. The *special half* of base change
-- (`isSpecial_map_of_isSpecial`) lives in `SpecialFirstKind`; here is the *normal half*.
variable {E : Type*} [Field E] [Differential E] [Algebra k E] [DifferentialAlgebra k E]

/-- **Corollary 3.4.1** (§3.4, p.95), normal half: a normal polynomial stays normal after an
algebraic base change — `IsCoprime p (Dp)` in `k[t]` gives `IsCoprime (p.map) (D(p.map))` in `E[t]`
(coprimality lifts along the ring hom `map`, and `D` commutes with `map` via `implicitDeriv_map`).
Combined with `isSpecial_map_of_isSpecial`, normal and special polynomials remain such over `E`. -/
theorem isCoprime_map_implicitDeriv_of_isCoprime {v p : k[X]}
    (hp : IsCoprime p (Differential.implicitDeriv v p)) :
    IsCoprime (p.map (algebraMap k E))
      (Differential.implicitDeriv (v.map (algebraMap k E)) (p.map (algebraMap k E))) := by
  rw [← implicitDeriv_map]
  have := hp.map (Polynomial.mapRingHom (algebraMap k E))
  simpa only [coe_mapRingHom] using this

end AlgebraicExtension

section ConstantField
-- The case `Da = 0` for all `a ∈ k` (the base is its own constant field). Here `Hₜ = Dt = v`,
-- and the special/normal root tests `v(a) = a′` / `v(a) ≠ a′` collapse to `v(a) = 0` / `v(a) ≠ 0`.
variable {K : Type*} [Field K] [Differential K]

/-- **Corollary 3.4.2(i)** (§3.4, p.95), linear (monic-irreducible) case: when `Da = 0` for all
`a ∈ k`, the monic irreducible `X − a` is special w.r.t. the monomial derivation (`Dt = v = Hₜ`)
iff `(X − a) ∣ Hₜ` — i.e. `a` is a root of `v`. (The special-root test `v(a) = a′` becomes
`v(a) = 0` since `a′ = 0`.) -/
theorem dvd_X_sub_C_implicitDeriv_iff_dvd (hconst : ∀ a : K, (a : K)′ = 0) (v : K[X]) (a : K) :
    (X - C a) ∣ Differential.implicitDeriv v (X - C a) ↔ (X - C a) ∣ v := by
  rw [dvd_X_sub_C_implicitDeriv_iff, hconst a, dvd_iff_isRoot, IsRoot.def, eq_comm]

/-- **Corollary 3.4.2(i)** (§3.4, p.95), squarefree form: when `Da = 0` for all `a ∈ k`, the
squarefree `∏_{a∈s}(X − a)` is special w.r.t. the monomial derivation iff it divides `Hₜ = v` —
every root of `p` is a root of `v` (the special-root test `v(a) = a′` collapses to `v(a) = 0`). -/
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

/-- **Corollary 3.4.2(ii)** (§3.4, p.95): when `Da = 0` for all `a ∈ k`, a squarefree
`∏_{a∈s}(X − a)` is normal w.r.t. the monomial derivation iff it is coprime to `Hₜ = v` —
`gcd(p, Hₜ) = 1` (the normal-root test `v(a) ≠ a′` collapses to `v(a) ≠ 0`, i.e. no root of `p` is
a root of `v`). -/
theorem isCoprime_prod_X_sub_C_implicitDeriv_iff_isCoprime (hconst : ∀ a : K, (a : K)′ = 0)
    (v : K[X]) (s : Finset K) :
    IsCoprime (∏ a ∈ s, (X - C a)) (Differential.implicitDeriv v (∏ a ∈ s, (X - C a)))
      ↔ IsCoprime (∏ a ∈ s, (X - C a)) v := by
  rw [isCoprime_prod_X_sub_C_implicitDeriv_iff, IsCoprime.prod_left_iff]
  refine forall₂_congr (fun a ha => ?_)
  rw [isCoprime_X_sub_C_iff, hconst a, ne_comm]

end ConstantField

end DeepWiki.SymbolicIntegration
