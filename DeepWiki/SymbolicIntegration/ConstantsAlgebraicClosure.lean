import DeepWiki.SymbolicIntegration.AlgebraicConstants
import DeepWiki.SymbolicIntegration.DifferentialExtensions
import Mathlib.RingTheory.Nullstellensatz

/-! # Constants of algebraic and rational extensions
Constants of a separable algebraic differential extension are exactly the algebraic elements over
the constants; over an algebraically closed base the constant subfield is algebraically closed, and
a constant-coefficient polynomial system solvable by extension constants is solvable by base
constants. -/

open scoped Differential
open Polynomial

namespace DeepWiki.SymbolicIntegration

section AlgebraicClosureConstants
variable {F E : Type*} [Field F] [Field E] [Differential F] [Differential E] [Algebra F E]
  [DifferentialAlgebra F E]

/-- `c` is a root of a nonzero polynomial over the ambient constant field of `E`. -/
def IsAlgebraicOverConst (c : E) : Prop :=
  ∃ q : E[X], q ≠ 0 ∧ (∀ i, (q.coeff i)′ = 0) ∧ q.eval c = 0

/-- A root of a separable polynomial with constant coefficients is a constant. -/
theorem deriv_eq_zero_of_separable_algebraic_const {c : E} (p : E[X])
    (hp : ∀ i, (p.coeff i)′ = 0) (hroot : p.eval c = 0) (hsep : p.derivative.eval c ≠ 0) :
    c′ = 0 := by
  have hchain : (p.eval c)′ = p.derivative.eval c * c′ := deriv_eval_of_const_coeffs p c hp
  rw [hroot, map_zero] at hchain
  exact (mul_eq_zero.mp hchain.symm).resolve_left hsep

/-- A constant of `E` that is integral over `F` is algebraic over the constants. -/
theorem isAlgebraicOverConst_of_deriv_eq_zero_of_integral {c : E} (hc : c′ = 0)
    (hint : IsIntegral F c) : IsAlgebraicOverConst c :=
  isAlgebraicOverConst_map_of_deriv_eq_zero hc hint

/-- A root of a separable (`q'(c) ≠ 0`) nonzero polynomial with constant coefficients is a constant. -/
theorem deriv_eq_zero_of_isAlgebraicOverConst {c : E} (q : E[X]) (hq : ∀ i, (q.coeff i)′ = 0)
    (hroot : q.eval c = 0) (hsep : q.derivative.eval c ≠ 0) : c′ = 0 :=
  deriv_eq_zero_of_separable_algebraic_const q hq hroot hsep

/-- A root of a separable base-constant polynomial is a constant. -/
theorem deriv_eq_zero_of_base_constant_polynomial {c : E} (p : F[X])
    (hp : ∀ i, (p.coeff i)′ = 0) (hroot : Polynomial.aeval c p = 0)
    (hsep : Polynomial.aeval c p.derivative ≠ 0) : c′ = 0 := by
  refine deriv_eq_zero_of_separable_algebraic_const (p.map (algebraMap F E)) ?_ ?_ ?_
  · intro i
    rw [Polynomial.coeff_map, deriv_algebraMap, hp i, map_zero]
  · rw [Polynomial.eval_map, ← Polynomial.aeval_def]
    exact hroot
  · rwa [Polynomial.derivative_map, Polynomial.eval_map, ← Polynomial.aeval_def]

/-- In characteristic zero, constants are exactly roots of separable base-constant polynomials. -/
theorem deriv_eq_zero_iff_isAlgebraicOverConst_separable_base [CharZero F] {c : E}
    (hint : IsIntegral F c) :
    c′ = 0 ↔ ∃ p : F[X], p ≠ 0 ∧ (∀ i, (p.coeff i)′ = 0) ∧
      Polynomial.aeval c p = 0 ∧ Polynomial.aeval c p.derivative ≠ 0 := by
  constructor
  · intro hc
    set p := minpoly F c with hpdef
    have hconst : ∀ i, (p.coeff i)′ = 0 := by
      intro i
      rw [hpdef]
      exact minpoly_coeff_deriv_eq_zero_of_deriv_eq_zero hc hint i
    refine ⟨p, ?_, hconst, ?_, ?_⟩
    · rw [hpdef]
      exact (minpoly.monic hint).ne_zero
    · rw [hpdef, minpoly.aeval]
    · rw [hpdef]
      exact (minpoly.irreducible hint).separable.aeval_derivative_ne_zero (minpoly.aeval F c)
  · rintro ⟨p, _, hp, hroot, hsep⟩
    exact deriv_eq_zero_of_base_constant_polynomial p hp hroot hsep

/-- In characteristic `0`, `c` is a constant iff it is a root of a separable nonzero polynomial in
`E[X]` with constant coefficients. -/
theorem deriv_eq_zero_iff_isAlgebraicOverConst_separable [CharZero F] {c : E}
    (hint : IsIntegral F c) :
    c′ = 0 ↔ ∃ q : E[X], q ≠ 0 ∧ (∀ i, (q.coeff i)′ = 0) ∧ q.eval c = 0 ∧
      q.derivative.eval c ≠ 0 := by
  constructor
  · intro hc
    obtain ⟨p, hpne, hpconst, hroot, hsep⟩ :=
      (deriv_eq_zero_iff_isAlgebraicOverConst_separable_base hint).mp hc
    have hconst : ∀ i, ((p.map (algebraMap F E)).coeff i)′ = 0 := by
      intro i
      rw [Polynomial.coeff_map, deriv_algebraMap]
      rw [hpconst i, map_zero]
    refine ⟨p.map (algebraMap F E), ?_, hconst, ?_, ?_⟩
    · rw [Ne, Polynomial.map_eq_zero_iff (algebraMap F E).injective]
      exact hpne
    · rw [Polynomial.eval_map, ← Polynomial.aeval_def]
      exact hroot
    · rw [Polynomial.derivative_map, Polynomial.eval_map, ← Polynomial.aeval_def]
      exact hsep
  · rintro ⟨q, _, hq, hroot, hsep⟩
    exact deriv_eq_zero_of_isAlgebraicOverConst q hq hroot hsep

end AlgebraicClosureConstants

section RationalExtensionConstants
variable {F : Type*} [Field F] [Differential F]

/-- For a coprime pair `u, v` with `v` monic and `v·κ_D(u) = u·κ_D(v)`, both `κ_D(u)` and `κ_D(v)`
vanish. -/
theorem mapCoeffs_eq_zero_of_coprime_of_relation {u v : F[X]} (hcop : IsCoprime u v)
    (hv : v.Monic) (hrel : v * Differential.mapCoeffs u = u * Differential.mapCoeffs v) :
    Differential.mapCoeffs u = 0 ∧ Differential.mapCoeffs v = 0 := by
  -- `v ∣ u · κ_D(v)` since it equals `v · κ_D(u)`; coprimality gives `v ∣ κ_D(v)`.
  have hdvd : v ∣ Differential.mapCoeffs v :=
    hcop.symm.dvd_of_dvd_mul_left ⟨Differential.mapCoeffs u, hrel.symm⟩
  -- but `deg κ_D(v) < deg v`, so `κ_D(v) = 0`.
  have hv0 : Differential.mapCoeffs v = 0 :=
    eq_zero_of_dvd_of_degree_lt hdvd (degree_mapCoeffs_lt hv)
  -- then `v · κ_D(u) = 0`, and `v ≠ 0`, so `κ_D(u) = 0`.
  have hu0 : Differential.mapCoeffs u = 0 := by
    have : v * Differential.mapCoeffs u = 0 := by rw [hrel, hv0, mul_zero]
    exact (mul_eq_zero.mp this).resolve_left hv.ne_zero
  exact ⟨hu0, hv0⟩

/-- For a coprime pair `u, v` with `v` monic and `v·κ_D(u) = u·κ_D(v)`, both numerator and
denominator have constant coefficients: `∀ i, (u.coeff i)′ = 0` and `∀ i, (v.coeff i)′ = 0`. -/
theorem coeff_deriv_eq_zero_of_coprime_of_relation {u v : F[X]} (hcop : IsCoprime u v)
    (hv : v.Monic) (hrel : v * Differential.mapCoeffs u = u * Differential.mapCoeffs v) :
    (∀ i, (u.coeff i)′ = 0) ∧ (∀ i, (v.coeff i)′ = 0) := by
  obtain ⟨hu0, hv0⟩ := mapCoeffs_eq_zero_of_coprime_of_relation hcop hv hrel
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have := congrArg (fun r => Polynomial.coeff r i) hu0
    rwa [Differential.coeff_mapCoeffs, Polynomial.coeff_zero] at this
  · have := congrArg (fun r => Polynomial.coeff r i) hv0
    rwa [Differential.coeff_mapCoeffs, Polynomial.coeff_zero] at this

end RationalExtensionConstants

section AlgebraicallyClosedConstants
variable {E : Type*} [Field E] [Differential E] [CharZero E]

/-- The constant subfield inherits characteristic `0` from `E` (its subtype injection preserves and
reflects `natCast`). -/
instance charZero_constantsSubfield : CharZero (constantsSubfield E) where
  cast_injective m n h := by
    have hι := (constantsSubfield E).subtype.injective
    apply Nat.cast_injective (R := E)
    have := congrArg (constantsSubfield E).subtype h
    rwa [map_natCast, map_natCast] at this

/-- When `E` is an algebraically closed char-`0` differential field, its constant subfield is
algebraically closed. -/
instance isAlgClosed_constantsSubfield [IsAlgClosed E] :
    IsAlgClosed (constantsSubfield E) := by
  apply IsAlgClosed.of_exists_root
  intro p hpmonic hpirr
  set ι : (constantsSubfield E) →+* E := (constantsSubfield E).subtype with hι
  set q : E[X] := p.map ι with hqdef
  -- `q`'s coefficients are constants (they are images of elements of `constantsSubfield E`).
  have hqconst : ∀ i, (q.coeff i)′ = 0 := by
    intro i
    rw [hqdef, Polynomial.coeff_map]
    exact (p.coeff i).property
  -- `q ≠ 0` and `deg q ≥ 1`, so it has a root `c ∈ E`.
  have hq0 : q ≠ 0 := by
    rw [hqdef, Ne, Polynomial.map_eq_zero_iff ι.injective]; exact hpmonic.ne_zero
  have hpsep : p.Separable := hpirr.separable
  have hdegq : q.degree ≠ 0 := by
    rw [hqdef, Polynomial.degree_map_eq_of_injective ι.injective]
    exact (Polynomial.degree_pos_of_irreducible hpirr).ne'
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_root q hdegq
  -- `q = p.map ι` is separable (char `0` irreducible `p`), so its derivative is nonzero at `c`.
  have hqsep : q.Separable := hpsep.map
  have hroot : q.eval c = 0 := hc
  have hsep : q.derivative.eval c ≠ 0 := by
    have := hqsep.eval₂_derivative_ne_zero (RingHom.id E) (x := c)
      (by rwa [Polynomial.eval₂_id])
    rwa [Polynomial.eval₂_id] at this
  -- The separable algebraic root is constant, so it lies in the constant subfield.
  have hcconst : c′ = 0 := deriv_eq_zero_of_separable_algebraic_const q hqconst hroot hsep
  refine ⟨⟨c, hcconst⟩, ?_⟩
  -- `p.eval ⟨c, _⟩ = 0` because `ι` is injective and `ι (p.eval ⟨c,_⟩) = q.eval c = 0`.
  apply ι.injective
  rw [map_zero, hι, ← Polynomial.eval₂_at_apply, Polynomial.eval₂_eq_eval_map, ← hqdef]
  exact hroot

end AlgebraicallyClosedConstants

section SystemTransfer

/-- Over an algebraically closed constant field `C`, a polynomial system `S`, `g` with coefficients
in `C` satisfied by an `E`-point (`f(c) = 0` for `f ∈ S`, `g(c) ≠ 0`) is satisfied by a `C`-point. -/
theorem exists_const_point_of_exists_extension_point {C E : Type*} [Field C] [Field E]
    [Algebra C E] [IsAlgClosed C] {σ : Type*} [Finite σ] (S : Set (MvPolynomial σ C))
    (g : MvPolynomial σ C) (c : σ → E) (hf : ∀ f ∈ S, MvPolynomial.aeval c f = 0)
    (hg : MvPolynomial.aeval c g ≠ 0) :
    ∃ a : σ → C, (∀ f ∈ S, MvPolynomial.aeval a f = 0) ∧ MvPolynomial.aeval a g ≠ 0 := by
  -- `g ∉ radical ⟨S⟩`: otherwise `gⁿ ∈ ⟨S⟩` evaluates to `0` at `c`, so `g(c)ⁿ = 0`.
  have hgrad : g ∉ (Ideal.span S).radical := by
    rw [Ideal.mem_radical_iff]
    rintro ⟨n, hn⟩
    have hzero : MvPolynomial.aeval c (g ^ n) = 0 := by
      refine Submodule.span_induction (p := fun x _ => MvPolynomial.aeval c x = 0)
        (fun f hf' => hf f hf') (by simp) (fun x y _ _ hx hy => by simp [hx, hy])
        (fun r x _ hx => by simp [hx]) hn
    rw [map_pow, pow_eq_zero_iff'] at hzero
    exact hg hzero.1
  -- strong Nullstellensatz over the algebraically closed `C`: `g` is not in the vanishing ideal of
  -- the zero locus, so it does not vanish at some `C`-point of the locus.
  rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := C)] at hgrad
  rw [MvPolynomial.mem_vanishingIdeal_iff] at hgrad
  push Not at hgrad
  obtain ⟨a, ha, hga⟩ := hgrad
  refine ⟨a, fun f hf' => ?_, hga⟩
  exact ha f (Ideal.subset_span hf')

end SystemTransfer

end DeepWiki.SymbolicIntegration
