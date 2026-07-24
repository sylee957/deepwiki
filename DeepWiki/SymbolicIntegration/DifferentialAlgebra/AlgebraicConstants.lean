import DeepWiki.SymbolicIntegration.DifferentialAlgebra.AlgebraicExtensions
import DeepWiki.SymbolicIntegration.DifferentialAlgebra.ConstantsSubfield
import Mathlib.FieldTheory.AlgebraicClosure

/-! # Algebraic closure of constants

Minimal-polynomial facts, separable algebraic constants, and algebraic closedness
of the constants subfield.
-/

open scoped Differential IntermediateField
open Polynomial

namespace DeepWiki.SymbolicIntegration

section AlgebraicConstant
variable {F E : Type*} [Field F] [Field E] [Differential F] [Differential E] [Algebra F E]
  [DifferentialAlgebra F E]

/-- High coefficients of `Differential.mapCoeffs p` vanish for monic `p`. -/
theorem coeff_mapCoeffs_eq_zero_of_monic {p : F[X]} (hp : p.Monic) {i : ℕ}
    (hi : p.natDegree ≤ i) : (Differential.mapCoeffs p).coeff i = 0 := by
  rw [Differential.coeff_mapCoeffs]
  rcases eq_or_lt_of_le hi with rfl | hlt
  · rw [Polynomial.Monic.coeff_natDegree hp]; simp
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]; simp

/-- `Differential.mapCoeffs p` has degree strictly below monic `p`. -/
theorem degree_mapCoeffs_lt {p : F[X]} (hp : p.Monic) :
    (Differential.mapCoeffs p).degree < p.degree := by
  rw [Polynomial.degree_eq_natDegree hp.ne_zero]
  apply (Polynomial.degree_lt_iff_coeff_zero _ _).mpr
  intro k hk
  exact coeff_mapCoeffs_eq_zero_of_monic hp hk

/-- The minimal polynomial of an integral constant has constant coefficients. -/
theorem minpoly_coeff_deriv_eq_zero_of_deriv_eq_zero {c : E} (hc : c′ = 0)
    (hint : IsIntegral F c) :
    ∀ i, ((minpoly F c).coeff i)′ = 0 := by
  set p := minpoly F c with hpdef
  have hpmonic : p.Monic := minpoly.monic hint
  -- the κ_D(p) term vanishes at c
  have hkappa : Polynomial.aeval c (Differential.mapCoeffs p) = 0 := by
    have hchain := Differential.deriv_aeval_eq (A := F) (R := E) c p
    rw [minpoly.aeval, map_zero, hc, mul_zero, add_zero] at hchain
    exact hchain.symm
  -- minimality forces mapCoeffs p = 0
  have hmc0 : Differential.mapCoeffs p = 0 := by
    by_contra hne
    have hle := minpoly.degree_le_of_ne_zero F c hne hkappa
    rw [← hpdef] at hle
    exact absurd (lt_of_le_of_lt hle (degree_mapCoeffs_lt hpmonic)) (lt_irrefl _)
  -- hence every coefficient of p is a constant
  have hconst : ∀ i, (p.coeff i)′ = 0 := fun i => by
    have := congrArg (fun r => Polynomial.coeff r i) hmc0
    rwa [Differential.coeff_mapCoeffs, Polynomial.coeff_zero] at this
  intro i
  exact hconst i

/-- An integral constant has a nonzero annihilating polynomial over the base constants. -/
theorem isAlgebraicOverConst_of_deriv_eq_zero {c : E} (hc : c′ = 0)
    (hint : IsIntegral F c) :
    ∃ p : F[X], p ≠ 0 ∧ (∀ i, (p.coeff i)′ = 0) ∧ Polynomial.aeval c p = 0 := by
  refine ⟨minpoly F c, (minpoly.monic hint).ne_zero, ?_, ?_⟩
  · exact minpoly_coeff_deriv_eq_zero_of_deriv_eq_zero hc hint
  · rw [minpoly.aeval]

/-- A constant algebraic over the base field is algebraic over the base constant field. -/
theorem isAlgebraic_constantsSubfield_of_deriv_eq_zero {c : E} (hc : c′ = 0)
    (halgebraic : IsAlgebraic F c) :
    IsAlgebraic (constantsSubfield F) c := by
  have hint : IsIntegral F c := halgebraic.isIntegral
  let p : F[X] := minpoly F c
  have hconst : ∀ i, (p.coeff i)′ = 0 := by
    intro i
    exact minpoly_coeff_deriv_eq_zero_of_deriv_eq_zero hc hint i
  let q : (constantsSubfield F)[X] :=
    ∑ i ∈ p.support, C ⟨p.coeff i, hconst i⟩ * X ^ i
  have hmap : q.map (constantsSubfield F).subtype = p := by
    rw [p.as_sum_support_C_mul_X_pow]
    ext n
    by_cases hn : n ∈ p.support <;> simp [q, hn]
  have hqmonic : q.Monic := Polynomial.monic_map_iff.mp <| by
    rw [hmap]
    exact minpoly.monic hint
  refine ⟨q, hqmonic.ne_zero, ?_⟩
  have halgebraMap : algebraMap (constantsSubfield F) E =
      (algebraMap F E).comp (constantsSubfield F).subtype := by
    ext x
    rfl
  rw [Polynomial.aeval_def, halgebraMap, ← Polynomial.eval₂_map, hmap,
    ← Polynomial.aeval_def]
  exact minpoly.aeval F c

/-- Mapping a base-constant annihilator gives an ambient constant-coefficient polynomial. -/
theorem isAlgebraicOverConst_map_of_deriv_eq_zero {c : E} (hc : c′ = 0)
    (hint : IsIntegral F c) :
    ∃ q : E[X], q ≠ 0 ∧ (∀ i, (q.coeff i)′ = 0) ∧ q.eval c = 0 := by
  obtain ⟨p, hpne, hconst, hroot⟩ := isAlgebraicOverConst_of_deriv_eq_zero hc hint
  refine ⟨p.map (algebraMap F E), ?_, ?_, ?_⟩
  · rw [Ne, Polynomial.map_eq_zero_iff (algebraMap F E).injective]
    exact hpne
  · intro i
    rw [Polynomial.coeff_map, deriv_algebraMap, hconst i, map_zero]
  · rw [Polynomial.eval_map, ← Polynomial.aeval_def]
    exact hroot

end AlgebraicConstant

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

section AlgebraicConstantExtension
variable {F E : Type*} [Field F] [Differential F] [CharZero F] [Field E] [Algebra F E]

/-- An element algebraic over the constants generates a unique differential extension of the base field. -/
theorem existsUnique_differentialAdjoin_of_isIntegral_constantsSubfield {α : E}
    (hα : IsIntegral (constantsSubfield F) α) :
    ∃! Δ : Differential (F⟮α⟯), IsDifferentialExtension F (F⟮α⟯) Δ := by
  have hαF : IsIntegral F α := hα.tower_top
  letI : FiniteDimensional F (F⟮α⟯) :=
    IntermediateField.adjoin.finiteDimensional hαF
  exact existsUnique_differentialExtension_finiteSeparable

end AlgebraicConstantExtension

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

/-- Evaluation of a polynomial over the base constants satisfies the ordinary chain rule. -/
theorem deriv_eval₂_constantsSubfield (p : (constantsSubfield F)[X]) (c : E) :
    (p.eval₂ ((algebraMap F E).comp (constantsSubfield F).subtype) c)′ =
      p.derivative.eval₂ ((algebraMap F E).comp (constantsSubfield F).subtype) c * c′ := by
  let ι : (constantsSubfield F) →+* E :=
    (algebraMap F E).comp (constantsSubfield F).subtype
  let q : E[X] := p.map ι
  have hqconst : ∀ i, (q.coeff i)′ = 0 := by
    intro i
    simp only [q, Polynomial.coeff_map]
    change (algebraMap F E ((p.coeff i : constantsSubfield F) : F))′ = 0
    rw [deriv_algebraMap, (p.coeff i).property, map_zero]
  have hchain := deriv_eval_of_const_coeffs q c hqconst
  simpa only [q, Polynomial.eval_map, Polynomial.derivative_map] using hchain

/-- An element algebraic and separable over the base constants is constant. -/
theorem deriv_eq_zero_of_isAlgebraic_constantsSubfield_of_isSeparable {c : E}
    (halgebraic : IsAlgebraic (constantsSubfield F) c)
    (hsep : IsSeparable (constantsSubfield F) c) :
    c′ = 0 := by
  have hint : IsIntegral (constantsSubfield F) c := halgebraic.isIntegral
  let p := minpoly (constantsSubfield F) c
  have halg : algebraMap (constantsSubfield F) E =
      (algebraMap F E).comp (constantsSubfield F).subtype := by
    ext x
    rfl
  have hroot :
      p.eval₂ ((algebraMap F E).comp (constantsSubfield F).subtype) c = 0 := by
    rw [← halg, ← Polynomial.aeval_def]
    exact minpoly.aeval (constantsSubfield F) c
  have hchain := deriv_eval₂_constantsSubfield p c
  rw [hroot, map_zero] at hchain
  have hderiv :
      p.derivative.eval₂ ((algebraMap F E).comp (constantsSubfield F).subtype) c ≠ 0 := by
    rw [← halg, ← Polynomial.aeval_def]
    exact hsep.aeval_derivative_ne_zero (minpoly.aeval (constantsSubfield F) c)
  exact (mul_eq_zero.mp hchain.symm).resolve_left hderiv

/-- In characteristic zero, a root of an irreducible polynomial over the base constants is constant. -/
theorem deriv_eq_zero_of_irreducible_constants_polynomial [CharZero F] {c : E}
    (p : (constantsSubfield F)[X]) (hp : Irreducible p)
    (hroot : p.eval₂ ((algebraMap F E).comp (constantsSubfield F).subtype) c = 0) :
    c′ = 0 := by
  have hchain := deriv_eval₂_constantsSubfield p c
  rw [hroot, map_zero] at hchain
  have hsep :
      p.derivative.eval₂ ((algebraMap F E).comp (constantsSubfield F).subtype) c ≠ 0 :=
    hp.separable.eval₂_derivative_ne_zero
      ((algebraMap F E).comp (constantsSubfield F).subtype) hroot
  exact (mul_eq_zero.mp hchain.symm).resolve_left hsep

/-- In characteristic zero, an element algebraic over the base constants is constant. -/
theorem deriv_eq_zero_of_isIntegral_constantsSubfield [CharZero F] {α : E}
    (hα : IsIntegral (constantsSubfield F) α) : α′ = 0 := by
  apply deriv_eq_zero_of_irreducible_constants_polynomial
    (minpoly (constantsSubfield F) α) (minpoly.irreducible hα)
  exact minpoly.aeval (constantsSubfield F) α

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
    exact deriv_eq_zero_of_separable_algebraic_const q hq hroot hsep

end AlgebraicClosureConstants

section RelativeAlgebraicClosureConstants
variable {F E : Type*} [Field F] [Field E] [Differential F] [Differential E]
  [CharZero F] [Algebra F E] [DifferentialAlgebra F E] [Algebra.IsAlgebraic F E]

/-- Constants in an algebraic extension are its relative algebraic closure of the base constants. -/
theorem constantsIntermediateField_eq_algebraicClosure :
    constantsIntermediateField F E = algebraicClosure (constantsSubfield F) E := by
  ext x
  rw [mem_constantsIntermediateField, mem_algebraicClosure_iff]
  constructor
  · intro hx
    exact isAlgebraic_constantsSubfield_of_deriv_eq_zero hx
      (Algebra.IsAlgebraic.isAlgebraic x)
  · intro hx
    exact deriv_eq_zero_of_isIntegral_constantsSubfield hx.isIntegral

/-- If the ambient algebraic extension is algebraically closed, its constants are an algebraic
closure of the base constants. -/
theorem isAlgClosure_constantsIntermediateField [IsAlgClosed E] :
    IsAlgClosure (constantsSubfield F) (constantsIntermediateField F E) := by
  rw [constantsIntermediateField_eq_algebraicClosure]
  infer_instance

end RelativeAlgebraicClosureConstants

section ConstantsAfterAlgebraicExtension

variable {F E Fbar L : Type*}
  [Field F] [Field E] [Field Fbar] [Field L]
  [Differential F] [Differential E] [Differential Fbar] [Differential L]
  [Algebra F E] [Algebra E L] [Algebra F L] [IsScalarTower F E L]
  [Algebra F Fbar] [Algebra Fbar L] [IsScalarTower F Fbar L]
  [DifferentialAlgebra F E] [DifferentialAlgebra E L] [DifferentialAlgebra Fbar L]
  [Algebra.IsAlgebraic E L] [IsAlgClosed Fbar]

/-- Equality of base and extension constants persists through an algebraic extension contained over an algebraically closed field. -/
theorem constantsIntermediateField_eq_bot_of_isAlgClosed_of_isAlgebraic
    (hconstants : constantsIntermediateField F E = ⊥) :
    constantsIntermediateField Fbar L = ⊥ := by
  letI : Algebra.IsAlgebraic (constantsSubfield F) (constantsIntermediateField F E) := by
    rw [hconstants]
    infer_instance
  apply le_antisymm
  · intro x hx
    have hxE : IsAlgebraic E x := Algebra.IsAlgebraic.isAlgebraic x
    have hxCE : IsAlgebraic (constantsIntermediateField F E) x :=
      isAlgebraic_constantsSubfield_of_deriv_eq_zero hx hxE
    have hxCF : IsAlgebraic (constantsSubfield F) x :=
      hxCE.isIntegral.trans_isAlgebraic (constantsSubfield F)
    have hxF : IsAlgebraic F x := hxCF.tower_top F
    have hxFbar : IsAlgebraic Fbar x := hxF.tower_top Fbar
    letI : Algebra.IsAlgebraic Fbar Fbar⟮(x : L)⟯ :=
      IntermediateField.isAlgebraic_adjoin_simple hxFbar.isIntegral
    have hadjoin : Fbar⟮(x : L)⟯ = ⊥ :=
      IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic Fbar⟮(x : L)⟯
    have hxmem : (x : L) ∈ Fbar⟮(x : L)⟯ :=
      IntermediateField.subset_adjoin Fbar ({(x : L)} : Set L) (Set.mem_singleton _)
    have hxbot : (x : L) ∈ (⊥ : IntermediateField Fbar L) := hadjoin ▸ hxmem
    obtain ⟨y, hy⟩ := IntermediateField.mem_bot.mp hxbot
    have hyconst : y′ = 0 := by
      apply (algebraMap Fbar L).injective
      rw [map_zero, ← deriv_algebraMap, hy, hx]
    apply IntermediateField.mem_bot.mpr
    exact ⟨⟨y, hyconst⟩, hy⟩
  · exact bot_le

end ConstantsAfterAlgebraicExtension

section AlgebraicallyClosedConstants
variable {E : Type*} [Field E] [Differential E] [CharZero E]

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

end DeepWiki.SymbolicIntegration
