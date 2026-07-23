import DeepWiki.SymbolicIntegration.DifferentialAlgebra.Extensions
import Mathlib.FieldTheory.PrimitiveElement

/-! # Finite separable extensions

Explicit power-basis coordinates give a choice-free extension theorem, with a classical bridge
from Mathlib's finite separable field extensions.
-/

open scoped Differential BigOperators
open Polynomial

namespace DeepWiki.SymbolicIntegration

/-- Explicit power-basis coordinates for a finite field extension. -/
structure PowerBasisPresentation
    (F E : Type*) [Field F] [Field E] [Algebra F E] where
  /-- The dimension of the presented extension. -/
  dim : ℕ
  /-- A field extension has positive presented dimension. -/
  dim_pos : 0 < dim
  /-- The generator whose powers form the presented basis. -/
  gen : E
  /-- Coordinates in the power basis `1, gen, ..., gen^(dim - 1)`. -/
  coord : E ≃ₗ[F] (Fin dim → F)
  /-- The coordinate vector of `gen ^ i` is the `i`th standard vector. -/
  coord_pow : ∀ i : Fin dim,
    coord (gen ^ (i : ℕ)) = fun j => if j = i then 1 else 0

namespace PowerBasisPresentation

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- Convert a Mathlib power basis into explicit finite power coordinates. -/
noncomputable def ofPowerBasis (pb : PowerBasis F E) : PowerBasisPresentation F E where
  dim := pb.dim
  dim_pos := pb.dim_pos
  gen := pb.gen
  coord := pb.basis.equivFun
  coord_pow := by
    intro i
    rw [← pb.basis_eq_pow i]
    funext j
    simpa [eq_comm] using pb.basis.equivFun_self i j

/-- Evaluate a finite coordinate vector as a linear combination of powers. -/
def evalPowerCoordinates (a : E) : (n : ℕ) → (Fin n → F) → E
  | 0, _ => 0
  | n + 1, c =>
      evalPowerCoordinates a n (fun i => c i.castSucc) +
        algebraMap F E (c (Fin.last n)) * a ^ n

/-- Evaluate finite power coordinates beginning at a specified exponent. -/
def evalPowerCoordinatesFrom (a : E) (q : ℕ) : (n : ℕ) → (Fin n → F) → E
  | 0, _ => 0
  | n + 1, c =>
      evalPowerCoordinatesFrom a q n (fun i => c i.castSucc) +
        c (Fin.last n) • a ^ (q + n)

/-- Evaluation of power coordinates preserves coordinatewise addition. -/
@[simp] theorem evalPowerCoordinates_add (a : E) :
    ∀ (n : ℕ) (c d : Fin n → F),
      evalPowerCoordinates a n (c + d) =
        evalPowerCoordinates a n c + evalPowerCoordinates a n d
  | 0, _, _ => by simp [evalPowerCoordinates]
  | n + 1, c, d => by
      rw [evalPowerCoordinates]
      change
        evalPowerCoordinates a n
              ((fun i => c i.castSucc) + (fun i => d i.castSucc)) +
            algebraMap F E (c (Fin.last n) + d (Fin.last n)) * a ^ n =
          _
      rw [evalPowerCoordinates_add a n]
      simp only [map_add, add_mul]
      change
        (evalPowerCoordinates a n (fun i => c i.castSucc) +
              evalPowerCoordinates a n (fun i => d i.castSucc)) +
            ((algebraMap F E) (c (Fin.last n)) * a ^ n +
              (algebraMap F E) (d (Fin.last n)) * a ^ n) =
          (evalPowerCoordinates a n (fun i => c i.castSucc) +
              (algebraMap F E) (c (Fin.last n)) * a ^ n) +
            (evalPowerCoordinates a n (fun i => d i.castSucc) +
              (algebraMap F E) (d (Fin.last n)) * a ^ n)
      ac_rfl

/-- Evaluation of power coordinates preserves scalar multiplication. -/
@[simp] theorem evalPowerCoordinates_smul (a : E) :
    ∀ (n : ℕ) (r : F) (c : Fin n → F),
      evalPowerCoordinates a n (r • c) =
        r • evalPowerCoordinates a n c
  | 0, _, _ => by simp [evalPowerCoordinates]
  | n + 1, r, c => by
      rw [evalPowerCoordinates]
      change
        evalPowerCoordinates a n (r • fun i => c i.castSucc) +
            algebraMap F E (r * c (Fin.last n)) * a ^ n =
          _
      rw [evalPowerCoordinates_smul a n]
      simp only [map_mul]
      simp only [Algebra.smul_def]
      change
        (algebraMap F E r) *
              evalPowerCoordinates a n (fun i => c i.castSucc) +
            (algebraMap F E r) * (algebraMap F E (c (Fin.last n))) * a ^ n =
          (algebraMap F E r) *
            (evalPowerCoordinates a n (fun i => c i.castSucc) +
              (algebraMap F E (c (Fin.last n))) * a ^ n)
      ring

/-- Formal differentiation of a coordinate vector in the power basis. -/
def coordinateDerivative (P : PowerBasisPresentation F E) (c : Fin P.dim → F) :
    Fin P.dim → F :=
  fun i =>
    if h : i.1 + 1 < P.dim then
      (i.1 + 1) • c ⟨i.1 + 1, h⟩
    else
      0

/-- Coefficients expressing `gen ^ dim` in the lower power basis. -/
def relationCoeffs (P : PowerBasisPresentation F E) : Fin P.dim → F :=
  P.coord (P.gen ^ P.dim)

/-- The value at `gen` of the derivative of its presented defining relation. -/
def relationDerivative (P : PowerBasisPresentation F E) : E :=
  P.dim • P.gen ^ (P.dim - 1) -
    P.coord.symm (P.coordinateDerivative P.relationCoeffs)

private lemma coordinateDerivative_sum (n : ℕ) (c : Fin n → F) (a : E) :
    (∑ i : Fin n,
      (if h : i.1 + 1 < n then (i.1 + 1) • c ⟨i.1 + 1, h⟩ else 0) • a ^ (i : ℕ)) =
    ∑ i : Fin n, algebraMap F E (c i) * ((i : ℕ) * a ^ ((i : ℕ) - 1)) := by
  cases n with
  | zero => simp
  | succ n =>
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ]
      simp only [Fin.val_castSucc, Fin.val_last]
      have hlt (i : Fin n) : i.1 + 1 < n + 1 := Nat.succ_lt_succ i.isLt
      simp_rw [dif_pos (hlt _)]
      rw [dif_neg (Nat.lt_irrefl (n + 1))]
      simp only [zero_smul, add_zero, Fin.val_succ, Nat.add_one_sub_one,
        Fin.val_zero, Nat.cast_zero, zero_mul, mul_zero, zero_add]
      apply Finset.sum_congr rfl
      intro i _
      change ((i.1 + 1) • c i.succ) • a ^ i.1 =
        algebraMap F E (c i.succ) * ((i.1 + 1 : ℕ) * a ^ i.1)
      simp [Algebra.smul_def]
      ring

/-- The presented relation derivative is the derivative of the power-basis minimal polynomial. -/
theorem relationDerivative_ofPowerBasis (pb : PowerBasis F E) :
    (ofPowerBasis pb).relationDerivative =
      aeval pb.gen (derivative pb.minpolyGen) := by
  rw [relationDerivative]
  change pb.dim • pb.gen ^ (pb.dim - 1) -
      pb.basis.equivFun.symm
        ((ofPowerBasis pb).coordinateDerivative
          (pb.basis.equivFun (pb.gen ^ pb.dim))) = _
  rw [Module.Basis.equivFun_symm_apply]
  simp_rw [pb.basis_eq_pow]
  rw [PowerBasis.minpolyGen, derivative_sub, derivative_X_pow]
  simp only [map_sub, map_mul, map_natCast, map_pow, aeval_X, nsmul_eq_mul]
  congr 1
  simp only [map_sum, derivative_C_mul, derivative_X_pow,
    map_mul, aeval_C, map_natCast, aeval_X, map_pow]
  unfold coordinateDerivative
  rw [Module.Basis.equivFun_apply]
  exact coordinateDerivative_sum pb.dim (pb.basis.repr (pb.gen ^ pb.dim)) pb.gen

/-- Power-basis coordinates evaluate to the element represented by those coordinates. -/
theorem coord_symm_eq_evalPowerCoordinates (P : PowerBasisPresentation F E)
    (c : Fin P.dim → F) :
    P.coord.symm c = evalPowerCoordinates P.gen P.dim c := by
  apply P.coord.injective
  rw [LinearEquiv.apply_symm_apply]
  ext j
  have aux :
      ∀ (n : ℕ) (hn : n ≤ P.dim) (d : Fin n → F),
        P.coord (evalPowerCoordinates P.gen n d) j =
          if h : j.1 < n then d ⟨j.1, h⟩ else 0 := by
    intro n
    induction n with
    | zero =>
        intro hn d
        simp [evalPowerCoordinates]
    | succ n ih =>
        intro hn d
        have hnlt : n < P.dim := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn
        rw [evalPowerCoordinates]
        simp only [map_add, Pi.add_apply]
        rw [ih (Nat.le_trans (Nat.le_succ n) hn) (fun i => d i.castSucc)]
        have hpow := P.coord_pow ⟨n, hnlt⟩
        have hterm :
            P.coord (algebraMap F E (d (Fin.last n)) * P.gen ^ n) =
              d (Fin.last n) • P.coord (P.gen ^ n) := by
          simpa only [Algebra.smul_def] using
            P.coord.map_smul (d (Fin.last n)) (P.gen ^ n)
        rw [congrFun hterm j, hpow]
        by_cases hj : j.1 < n
        · have hjne : j ≠ ⟨n, hnlt⟩ := by
            intro h
            have := congrArg Fin.val h
            simp at this
            omega
          have hjs : j.1 < n + 1 := by omega
          simp [hj, hjs, hjne]
        · by_cases hjs : j.1 < n + 1
          · have hjeq : j.1 = n := by omega
            have hjFin : j = ⟨n, hnlt⟩ := Fin.ext hjeq
            subst j
            simp only [lt_self_iff_false, ↓reduceDIte, Pi.smul_apply, if_true,
              smul_eq_mul, mul_one, zero_add, Nat.lt_add_one]
            apply congrArg d
            apply Fin.ext
            rfl
          · have hjne : j ≠ ⟨n, hnlt⟩ := by
              intro h
              subst j
              exact hjs (Nat.lt_succ_self n)
            simp [hj, hjs, hjne]
  symm
  simpa using aux P.dim (Nat.le_refl P.dim) c

/-- Evaluation from exponent zero agrees with ordinary power-coordinate evaluation. -/
theorem evalPowerCoordinatesFrom_zero (a : E) :
    ∀ (n : ℕ) (c : Fin n → F),
      evalPowerCoordinatesFrom a 0 n c = evalPowerCoordinates a n c
  | 0, _ => by simp [evalPowerCoordinatesFrom, evalPowerCoordinates]
  | n + 1, c => by
      rw [evalPowerCoordinatesFrom, evalPowerCoordinates]
      rw [evalPowerCoordinatesFrom_zero a n]
      simp only [zero_add, Algebra.smul_def]

/-- Shifting power-coordinate evaluation is multiplication by the offset power. -/
theorem evalPowerCoordinatesFrom_eq_pow_mul (a : E) (q : ℕ) :
    ∀ (n : ℕ) (c : Fin n → F),
      evalPowerCoordinatesFrom a q n c =
        a ^ q * evalPowerCoordinates a n c
  | 0, _ => by simp [evalPowerCoordinatesFrom, evalPowerCoordinates]
  | n + 1, c => by
      rw [evalPowerCoordinatesFrom, evalPowerCoordinates]
      rw [evalPowerCoordinatesFrom_eq_pow_mul a q n]
      rw [pow_add]
      simp only [Algebra.smul_def, mul_add]
      ac_rfl

/-- The presented relation coefficients evaluate to the leading generator power. -/
theorem evalPowerCoordinates_relationCoeffs (P : PowerBasisPresentation F E) :
    evalPowerCoordinates P.gen P.dim P.relationCoeffs = P.gen ^ P.dim := by
  rw [← P.coord_symm_eq_evalPowerCoordinates]
  simp [relationCoeffs]

end PowerBasisPresentation

/-- A separable power-basis presentation has a simple defining relation. -/
structure SeparablePowerBasisPresentation
    (F E : Type*) [Field F] [Field E] [Algebra F E] where
  /-- The underlying explicit power-basis presentation. -/
  powerBasis : PowerBasisPresentation F E
  /-- An explicit inverse for the derivative of the defining relation. -/
  relationDerivativeInv : E
  /-- The supplied inverse witnesses simplicity of the defining relation. -/
  relationDerivative_mul_inv :
    powerBasis.relationDerivative * relationDerivativeInv = 1

namespace SeparablePowerBasisPresentation

/-- Classically choose an explicit separable power basis for a finite separable extension. -/
noncomputable def ofFiniteOfSeparable
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E] :
    SeparablePowerBasisPresentation F E := by
  let pb : PowerBasis F E := Field.powerBasisOfFiniteOfSeparable F E
  let P : PowerBasisPresentation F E := PowerBasisPresentation.ofPowerBasis pb
  have hP : P.relationDerivative ≠ 0 := by
    rw [show P = PowerBasisPresentation.ofPowerBasis pb by rfl,
      PowerBasisPresentation.relationDerivative_ofPowerBasis,
      PowerBasis.minpolyGen_eq]
    exact (Algebra.IsSeparable.isSeparable F pb.gen).aeval_derivative_ne_zero
      (minpoly.aeval F pb.gen)
  exact {
    powerBasis := P
    relationDerivativeInv := P.relationDerivative⁻¹
    relationDerivative_mul_inv := mul_inv_cancel₀ hP
  }

/-- Classically choose an explicit separable power basis for a finite characteristic-zero extension. -/
noncomputable def ofFiniteOfCharZero
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [CharZero F] [FiniteDimensional F E] :
    SeparablePowerBasisPresentation F E :=
  ofFiniteOfSeparable F E

noncomputable example
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E] :
    SeparablePowerBasisPresentation F E :=
  ofFiniteOfSeparable F E

noncomputable example
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [CharZero F] [FiniteDimensional F E] :
    SeparablePowerBasisPresentation F E :=
  ofFiniteOfCharZero F E

variable {F E : Type*} [Field F] [Differential F] [Field E] [Algebra F E]

/-- Apply the base derivation to every power-basis coordinate. -/
def coefficientDerivation (S : SeparablePowerBasisPresentation F E) (x : E) : E :=
  S.powerBasis.coord.symm (fun i => (S.powerBasis.coord x i)′)

/-- Differentiate the power-basis monomials while holding their coefficients fixed. -/
def coordinateSlope (S : SeparablePowerBasisPresentation F E) (x : E) : E :=
  S.powerBasis.coord.symm
    (S.powerBasis.coordinateDerivative (S.powerBasis.coord x))

/-- Apply the base derivation to the coefficients of the defining relation. -/
def relationCoefficientDerivation (S : SeparablePowerBasisPresentation F E) : E :=
  S.powerBasis.coord.symm (fun i => (S.powerBasis.relationCoeffs i)′)

/-- The forced derivative of the presented power-basis generator. -/
def generatorDerivative (S : SeparablePowerBasisPresentation F E) : E :=
  S.relationCoefficientDerivation * S.relationDerivativeInv

/-- The forced extension of the base derivation, expressed in power-basis coordinates. -/
def extensionValue (S : SeparablePowerBasisPresentation F E) (x : E) : E :=
  S.coefficientDerivation x + S.coordinateSlope x * S.generatorDerivative

/-- Formally differentiate shifted power coordinates using the forced generator value. -/
def derivePowerCoordinatesFrom (S : SeparablePowerBasisPresentation F E) (q : ℕ) :
    (n : ℕ) → (Fin n → F) → E
  | 0, _ => 0
  | n + 1, c =>
      derivePowerCoordinatesFrom S q n (fun i => c i.castSucc) +
        (c (Fin.last n))′ • S.powerBasis.gen ^ (q + n) +
        c (Fin.last n) •
          ((q + n) • S.powerBasis.gen ^ (q + n - 1) * S.generatorDerivative)

omit [Differential F] in
/-- Formal coordinate differentiation sends zero to zero. -/
@[simp] theorem coordinateDerivative_zero (P : PowerBasisPresentation F E) :
    P.coordinateDerivative 0 = 0 := by
  funext i
  simp [PowerBasisPresentation.coordinateDerivative]

omit [Differential F] in
/-- Formal coordinate differentiation preserves addition. -/
@[simp] theorem coordinateDerivative_add (P : PowerBasisPresentation F E)
    (c d : Fin P.dim → F) :
    P.coordinateDerivative (c + d) =
      P.coordinateDerivative c + P.coordinateDerivative d := by
  funext i
  simp only [PowerBasisPresentation.coordinateDerivative, Pi.add_apply]
  split_ifs <;> simp

omit [Differential F] in
/-- Formal coordinate differentiation is linear over the base field. -/
@[simp] theorem coordinateDerivative_smul (P : PowerBasisPresentation F E)
    (a : F) (c : Fin P.dim → F) :
    P.coordinateDerivative (a • c) = a • P.coordinateDerivative c := by
  funext i
  simp only [PowerBasisPresentation.coordinateDerivative, Pi.smul_apply, smul_eq_mul]
  split_ifs
  · simp [nsmul_eq_mul]
    ring
  · simp

/-- Coefficient differentiation sends zero to zero. -/
@[simp] theorem coefficientDerivation_zero (S : SeparablePowerBasisPresentation F E) :
    S.coefficientDerivation 0 = 0 := by
  apply S.powerBasis.coord.injective
  ext i
  simp [coefficientDerivation]

/-- Coefficient differentiation preserves addition. -/
@[simp] theorem coefficientDerivation_add (S : SeparablePowerBasisPresentation F E)
    (x y : E) :
    S.coefficientDerivation (x + y) =
      S.coefficientDerivation x + S.coefficientDerivation y := by
  apply S.powerBasis.coord.injective
  ext i
  simp [coefficientDerivation]

/-- Coefficient differentiation obeys the connection rule over the base field. -/
theorem coefficientDerivation_smul (S : SeparablePowerBasisPresentation F E)
    (a : F) (x : E) :
    S.coefficientDerivation (a • x) =
      a′ • x + a • S.coefficientDerivation x := by
  apply S.powerBasis.coord.injective
  ext i
  simp [coefficientDerivation, Derivation.leibniz, mul_comm]
  ring

omit [Differential F] in
/-- The coordinate slope sends zero to zero. -/
@[simp] theorem coordinateSlope_zero (S : SeparablePowerBasisPresentation F E) :
    S.coordinateSlope 0 = 0 := by
  simp [coordinateSlope]

omit [Differential F] in
/-- The coordinate slope preserves addition. -/
@[simp] theorem coordinateSlope_add (S : SeparablePowerBasisPresentation F E)
    (x y : E) :
    S.coordinateSlope (x + y) = S.coordinateSlope x + S.coordinateSlope y := by
  simp [coordinateSlope]

omit [Differential F] in
/-- The coordinate slope is linear over the base field. -/
@[simp] theorem coordinateSlope_smul (S : SeparablePowerBasisPresentation F E)
    (a : F) (x : E) :
    S.coordinateSlope (a • x) = a • S.coordinateSlope x := by
  apply S.powerBasis.coord.injective
  simp [coordinateSlope]

/-- Coefficient differentiation vanishes on each presented basis power. -/
@[simp] theorem coefficientDerivation_gen_pow
    (S : SeparablePowerBasisPresentation F E) (i : Fin S.powerBasis.dim) :
    S.coefficientDerivation (S.powerBasis.gen ^ (i : ℕ)) = 0 := by
  apply S.powerBasis.coord.injective
  ext j
  rw [coefficientDerivation, LinearEquiv.apply_symm_apply, S.powerBasis.coord_pow i]
  rw [map_zero]
  simp only [Pi.zero_apply]
  split_ifs <;> simp

omit [Differential F] in
/-- The coordinate slope has the expected value on a presented basis power. -/
theorem coordinateSlope_gen_pow
    (S : SeparablePowerBasisPresentation F E) (i : Fin S.powerBasis.dim) :
    S.coordinateSlope (S.powerBasis.gen ^ (i : ℕ)) =
      (i : ℕ) • S.powerBasis.gen ^ ((i : ℕ) - 1) := by
  apply S.powerBasis.coord.injective
  ext j
  rcases i with ⟨_ | n, hi⟩
  · rw [coordinateSlope, LinearEquiv.apply_symm_apply]
    simp only [zero_nsmul, map_zero, Pi.zero_apply,
      PowerBasisPresentation.coordinateDerivative, S.powerBasis.coord_pow ⟨0, hi⟩]
    by_cases h : j.1 + 1 < S.powerBasis.dim
    · rw [dif_pos h]
      have hne : (⟨j.1 + 1, h⟩ : Fin S.powerBasis.dim) ≠ ⟨0, hi⟩ := by
        intro heq
        have := congrArg Fin.val heq
        simp at this
      rw [if_neg hne]
      simp
    · rw [dif_neg h]
  · have hn : n < S.powerBasis.dim := by omega
    rw [coordinateSlope, LinearEquiv.apply_symm_apply]
    simp only [PowerBasisPresentation.coordinateDerivative,
      S.powerBasis.coord_pow ⟨n + 1, hi⟩, Nat.add_sub_cancel]
    rw [map_nsmul, S.powerBasis.coord_pow ⟨n, hn⟩]
    rw [Pi.smul_apply]
    change
      (if h : j.1 + 1 < S.powerBasis.dim then
          (j.1 + 1) •
            (if (⟨j.1 + 1, h⟩ : Fin S.powerBasis.dim) = ⟨n + 1, hi⟩ then 1 else 0)
        else 0) =
        (n + 1) • (if j = ⟨n, hn⟩ then 1 else 0)
    by_cases hj : j.1 = n
    · have hjFin : j = ⟨n, hn⟩ := Fin.ext hj
      subst j
      simp [hi]
    · by_cases hjbound : j.1 + 1 < S.powerBasis.dim
      · have hjSuccNe : (⟨j.1 + 1, hjbound⟩ : Fin S.powerBasis.dim) ≠
            ⟨n + 1, hi⟩ := by
          intro h
          have := congrArg Fin.val h
          simp at this
          omega
        simp [hj, hjbound, hjSuccNe, Fin.ext_iff]
      · simp [hj, hjbound, Fin.ext_iff]

/-- The presented extension value sends zero to zero. -/
@[simp] theorem extensionValue_zero (S : SeparablePowerBasisPresentation F E) :
    S.extensionValue 0 = 0 := by
  simp [extensionValue]

/-- The presented extension value preserves addition. -/
@[simp] theorem extensionValue_add (S : SeparablePowerBasisPresentation F E)
    (x y : E) :
    S.extensionValue (x + y) = S.extensionValue x + S.extensionValue y := by
  simp [extensionValue, add_mul, add_assoc, add_left_comm]

/-- The presented extension value obeys the connection rule over the base field. -/
theorem extensionValue_smul (S : SeparablePowerBasisPresentation F E)
    (a : F) (x : E) :
    S.extensionValue (a • x) = a′ • x + a • S.extensionValue x := by
  rw [extensionValue, coefficientDerivation_smul, coordinateSlope_smul]
  simp only [extensionValue, smul_add]
  rw [Algebra.smul_mul_assoc]
  ac_rfl

/-- The extension value differentiates a shifted coordinate expansion term by term. -/
theorem extensionValue_evalPowerCoordinatesFrom
    (S : SeparablePowerBasisPresentation F E) (q : ℕ) :
    ∀ (n : ℕ) (c : Fin n → F),
      (∀ k : ℕ, k < q + n →
        S.extensionValue (S.powerBasis.gen ^ k) =
          k • S.powerBasis.gen ^ (k - 1) * S.generatorDerivative) →
      S.extensionValue
          (PowerBasisPresentation.evalPowerCoordinatesFrom S.powerBasis.gen q n c) =
        S.derivePowerCoordinatesFrom q n c
  | 0, _, _ => by
      simp [PowerBasisPresentation.evalPowerCoordinatesFrom,
        derivePowerCoordinatesFrom]
  | n + 1, c, hpow => by
      rw [PowerBasisPresentation.evalPowerCoordinatesFrom, extensionValue_add,
        extensionValue_smul]
      rw [extensionValue_evalPowerCoordinatesFrom S q n
        (fun i => c i.castSucc) (fun k hk => hpow k (by omega))]
      rw [hpow (q + n) (by omega)]
      simp only [derivePowerCoordinatesFrom]
      ac_rfl

/-- Differentiating shifted coordinates satisfies the formal power shift rule. -/
theorem derivePowerCoordinatesFrom_shift
    (S : SeparablePowerBasisPresentation F E) (q : ℕ) :
    ∀ (n : ℕ) (c : Fin n → F),
      S.derivePowerCoordinatesFrom q n c =
        S.powerBasis.gen ^ q * S.derivePowerCoordinatesFrom 0 n c +
          q • S.powerBasis.gen ^ (q - 1) *
            PowerBasisPresentation.evalPowerCoordinates S.powerBasis.gen n c *
              S.generatorDerivative := by
  rcases q with _ | q
  · intro n c
    rw [pow_zero, one_mul, zero_nsmul, zero_mul]
    rw [zero_mul, add_zero]
  · intro n
    induction n with
    | zero =>
        intro c
        change (0 : E) =
          S.powerBasis.gen ^ (q + 1) * 0 +
            (q + 1) • S.powerBasis.gen ^ (q + 1 - 1) * 0 *
              S.generatorDerivative
        rw [mul_zero, mul_zero, zero_mul, add_zero]
    | succ n ih =>
        intro c
        rw [derivePowerCoordinatesFrom, derivePowerCoordinatesFrom,
          PowerBasisPresentation.evalPowerCoordinates]
        rw [ih (fun i => c i.castSucc)]
        simp only [Nat.add_sub_cancel, Algebra.smul_def, map_add, map_one]
        by_cases hn : n = 0
        · subst n
          simp only [derivePowerCoordinatesFrom,
            PowerBasisPresentation.evalPowerCoordinates, map_zero,
            zero_mul, mul_zero, add_zero, zero_add]
          rw [Nat.add_sub_cancel q 1]
          ring
        · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
          have hpred : n - 1 + 1 = n := Nat.sub_add_cancel hnpos
          simp only [zero_add, map_zero]
          rw [pow_add S.powerBasis.gen (q + 1) n,
            Nat.add_right_comm q 1 n, Nat.add_sub_cancel (q + n) 1,
            pow_add S.powerBasis.gen q n]
          have hpow :
              S.powerBasis.gen ^ (q + 1) * S.powerBasis.gen ^ (n - 1) =
                S.powerBasis.gen ^ q * S.powerBasis.gen ^ n := by
            rw [show S.powerBasis.gen ^ (q + 1) =
              S.powerBasis.gen ^ q * S.powerBasis.gen by simp [pow_succ]]
            rw [show S.powerBasis.gen ^ n =
              S.powerBasis.gen ^ (n - 1) * S.powerBasis.gen by
                rw [← pow_succ, hpred]]
            ring
          ring_nf at hpow ⊢
          rw [hpow]
          ring

/-- The presented extension value has the expected value on a basis power. -/
theorem extensionValue_gen_pow
    (S : SeparablePowerBasisPresentation F E) (i : Fin S.powerBasis.dim) :
    S.extensionValue (S.powerBasis.gen ^ (i : ℕ)) =
      (i : ℕ) • S.powerBasis.gen ^ ((i : ℕ) - 1) * S.generatorDerivative := by
  rw [extensionValue, coefficientDerivation_gen_pow, coordinateSlope_gen_pow]
  simp

/-- The defining relation forces the expected derivative at its leading power. -/
theorem extensionValue_gen_pow_dim (S : SeparablePowerBasisPresentation F E) :
    S.extensionValue (S.powerBasis.gen ^ S.powerBasis.dim) =
      S.powerBasis.dim • S.powerBasis.gen ^ (S.powerBasis.dim - 1) *
        S.generatorDerivative := by
  rw [extensionValue]
  change
    S.relationCoefficientDerivation +
        S.powerBasis.coord.symm
            (S.powerBasis.coordinateDerivative S.powerBasis.relationCoeffs) *
          S.generatorDerivative =
      S.powerBasis.dim • S.powerBasis.gen ^ (S.powerBasis.dim - 1) *
        S.generatorDerivative
  have hgenerator :
      S.powerBasis.relationDerivative * S.generatorDerivative =
        S.relationCoefficientDerivation := by
    rw [generatorDerivative]
    calc
      S.powerBasis.relationDerivative *
          (S.relationCoefficientDerivation * S.relationDerivativeInv) =
        S.relationCoefficientDerivation *
          (S.powerBasis.relationDerivative * S.relationDerivativeInv) := by ring
      _ = S.relationCoefficientDerivation := by
        rw [S.relationDerivative_mul_inv, mul_one]
  calc
    S.relationCoefficientDerivation +
          S.powerBasis.coord.symm
              (S.powerBasis.coordinateDerivative S.powerBasis.relationCoeffs) *
            S.generatorDerivative =
        S.powerBasis.relationDerivative * S.generatorDerivative +
          S.powerBasis.coord.symm
              (S.powerBasis.coordinateDerivative S.powerBasis.relationCoeffs) *
            S.generatorDerivative := by rw [hgenerator]
    _ = S.powerBasis.dim • S.powerBasis.gen ^ (S.powerBasis.dim - 1) *
        S.generatorDerivative := by
      simp only [PowerBasisPresentation.relationDerivative]
      ring

/-- Differentiating the unshifted relation coordinates gives the leading-power value. -/
theorem derivePowerCoordinatesFrom_relation (S : SeparablePowerBasisPresentation F E) :
    S.derivePowerCoordinatesFrom 0 S.powerBasis.dim S.powerBasis.relationCoeffs =
      S.powerBasis.dim • S.powerBasis.gen ^ (S.powerBasis.dim - 1) *
        S.generatorDerivative := by
  have h := S.extensionValue_evalPowerCoordinatesFrom 0 S.powerBasis.dim
    S.powerBasis.relationCoeffs (fun k hk =>
      S.extensionValue_gen_pow ⟨k, by omega⟩)
  rw [PowerBasisPresentation.evalPowerCoordinatesFrom_zero,
    S.powerBasis.evalPowerCoordinates_relationCoeffs] at h
  rw [← h]
  exact S.extensionValue_gen_pow_dim

/-- Every shifted defining relation has its expected formal derivative. -/
theorem derivePowerCoordinatesFrom_relation_shift
    (S : SeparablePowerBasisPresentation F E) (q : ℕ) :
    S.derivePowerCoordinatesFrom q S.powerBasis.dim S.powerBasis.relationCoeffs =
      (S.powerBasis.dim + q) •
          S.powerBasis.gen ^ (S.powerBasis.dim + q - 1) *
        S.generatorDerivative := by
  rw [S.derivePowerCoordinatesFrom_shift q S.powerBasis.dim
    S.powerBasis.relationCoeffs]
  rw [S.derivePowerCoordinatesFrom_relation,
    S.powerBasis.evalPowerCoordinates_relationCoeffs]
  rcases q with _ | q
  · simp
  · have hdim : 0 < S.powerBasis.dim := S.powerBasis.dim_pos
    have hpred : S.powerBasis.dim - 1 + 1 = S.powerBasis.dim :=
      Nat.sub_add_cancel hdim
    rw [show S.powerBasis.dim + (q + 1) - 1 =
      S.powerBasis.dim + q by omega]
    rw [show S.powerBasis.gen ^ (q + 1) =
      S.powerBasis.gen ^ q * S.powerBasis.gen by simp [pow_succ]]
    have hgen : S.powerBasis.gen ^ S.powerBasis.dim =
        S.powerBasis.gen ^ (S.powerBasis.dim - 1) * S.powerBasis.gen := by
      rw [← pow_succ, hpred]
    rw [show S.powerBasis.gen ^ (S.powerBasis.dim + q) =
      S.powerBasis.gen ^ q * S.powerBasis.gen ^ S.powerBasis.dim by
        rw [Nat.add_comm, pow_add]]
    rw [hgen]
    rw [Nat.add_sub_cancel q 1]
    simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    ring

/-- The presented extension value has the formal derivative on every generator power. -/
theorem extensionValue_gen_pow_all
    (S : SeparablePowerBasisPresentation F E) (k : ℕ) :
    S.extensionValue (S.powerBasis.gen ^ k) =
      k • S.powerBasis.gen ^ (k - 1) * S.generatorDerivative := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      by_cases hk : k < S.powerBasis.dim
      · exact S.extensionValue_gen_pow ⟨k, hk⟩
      · have hdim : S.powerBasis.dim ≤ k := Nat.le_of_not_gt hk
        let q := k - S.powerBasis.dim
        have hkq : S.powerBasis.dim + q = k := Nat.add_sub_of_le hdim
        have hEval :
            PowerBasisPresentation.evalPowerCoordinatesFrom S.powerBasis.gen q
                S.powerBasis.dim S.powerBasis.relationCoeffs =
              S.powerBasis.gen ^ k := by
          rw [PowerBasisPresentation.evalPowerCoordinatesFrom_eq_pow_mul,
            S.powerBasis.evalPowerCoordinates_relationCoeffs, ← pow_add]
          congr 1
          omega
        have hderive := S.extensionValue_evalPowerCoordinatesFrom q
          S.powerBasis.dim S.powerBasis.relationCoeffs
            (fun j hj => ih j (by omega))
        rw [hEval, S.derivePowerCoordinatesFrom_relation_shift q] at hderive
        simpa only [hkq] using hderive

/-- The extension value satisfies Leibniz when one factor is a generator power. -/
theorem extensionValue_gen_pow_mul
    (S : SeparablePowerBasisPresentation F E) (q : ℕ) (y : E) :
    S.extensionValue (S.powerBasis.gen ^ q * y) =
      S.extensionValue (S.powerBasis.gen ^ q) * y +
        S.powerBasis.gen ^ q * S.extensionValue y := by
  let c := S.powerBasis.coord y
  have hy :
      y = PowerBasisPresentation.evalPowerCoordinates S.powerBasis.gen
        S.powerBasis.dim c := by
    rw [← S.powerBasis.coord_symm_eq_evalPowerCoordinates]
    simp [c]
  rw [hy]
  rw [← PowerBasisPresentation.evalPowerCoordinatesFrom_eq_pow_mul]
  rw [S.extensionValue_evalPowerCoordinatesFrom q S.powerBasis.dim c
    (fun k hk => S.extensionValue_gen_pow_all k)]
  rw [S.derivePowerCoordinatesFrom_shift q S.powerBasis.dim c]
  have hzero := S.extensionValue_evalPowerCoordinatesFrom 0 S.powerBasis.dim c
    (fun k hk => S.extensionValue_gen_pow_all k)
  rw [PowerBasisPresentation.evalPowerCoordinatesFrom_zero] at hzero
  rw [hzero, S.extensionValue_gen_pow_all]
  ring

/-- Leibniz is preserved when the first factor is scaled from the base field. -/
theorem extensionValue_smul_mul
    (S : SeparablePowerBasisPresentation F E) (a : F) (x y : E)
    (hxy : S.extensionValue (x * y) =
      S.extensionValue x * y + x * S.extensionValue y) :
    S.extensionValue ((a • x) * y) =
      S.extensionValue (a • x) * y + (a • x) * S.extensionValue y := by
  rw [Algebra.smul_mul_assoc, S.extensionValue_smul, hxy,
    S.extensionValue_smul]
  simp only [Algebra.smul_def]
  ring

/-- Leibniz holds for a coordinate expansion in the first factor. -/
theorem extensionValue_evalPowerCoordinates_mul
    (S : SeparablePowerBasisPresentation F E) :
    ∀ (n : ℕ) (c : Fin n → F) (y : E),
      S.extensionValue
          (PowerBasisPresentation.evalPowerCoordinates S.powerBasis.gen n c * y) =
        S.extensionValue
              (PowerBasisPresentation.evalPowerCoordinates S.powerBasis.gen n c) * y +
          PowerBasisPresentation.evalPowerCoordinates S.powerBasis.gen n c *
            S.extensionValue y
  | 0, _, y => by
      simp [PowerBasisPresentation.evalPowerCoordinates]
  | n + 1, c, y => by
      rw [PowerBasisPresentation.evalPowerCoordinates, add_mul,
        extensionValue_add, extensionValue_add, add_mul]
      rw [extensionValue_evalPowerCoordinates_mul S n (fun i => c i.castSucc) y]
      have hlast := S.extensionValue_smul_mul (c (Fin.last n))
        (S.powerBasis.gen ^ n) y (S.extensionValue_gen_pow_mul n y)
      simp only [Algebra.smul_def] at hlast ⊢
      linear_combination hlast

/-- The explicitly presented extension value satisfies the Leibniz rule. -/
theorem extensionValue_leibniz
    (S : SeparablePowerBasisPresentation F E) (x y : E) :
    S.extensionValue (x * y) =
      S.extensionValue x * y + x * S.extensionValue y := by
  let c := S.powerBasis.coord x
  have hx :
      x = PowerBasisPresentation.evalPowerCoordinates S.powerBasis.gen
        S.powerBasis.dim c := by
    rw [← S.powerBasis.coord_symm_eq_evalPowerCoordinates]
    simp [c]
  rw [hx]
  exact S.extensionValue_evalPowerCoordinates_mul S.powerBasis.dim c y

/-- The derivation defined by an explicit separable power-basis presentation. -/
def extensionDerivation (S : SeparablePowerBasisPresentation F E) :
    Derivation ℤ E E := by
  let dAdd : E →+ E :=
    { toFun := S.extensionValue
      map_zero' := S.extensionValue_zero
      map_add' := S.extensionValue_add }
  exact Derivation.mk' dAdd.toIntLinearMap fun x y => by
    change S.extensionValue (x * y) =
      x * S.extensionValue y + y * S.extensionValue x
    rw [S.extensionValue_leibniz]
    ring

/-- The explicit extension derivation evaluates as `extensionValue`. -/
@[simp] theorem extensionDerivation_apply
    (S : SeparablePowerBasisPresentation F E) (x : E) :
    S.extensionDerivation x = S.extensionValue x :=
  rfl

/-- The explicit extension derivation agrees with the base derivation on scalar images. -/
theorem extensionDerivation_algebraMap
    (S : SeparablePowerBasisPresentation F E) (a : F) :
    S.extensionDerivation (algebraMap F E a) = algebraMap F E (a′) := by
  change S.extensionValue (algebraMap F E a) = algebraMap F E (a′)
  rw [← mul_one (algebraMap F E a), ← Algebra.smul_def]
  rw [S.extensionValue_smul]
  have hone : S.extensionValue (1 : E) = 0 := by
    simpa using S.extensionValue_gen_pow_all 0
  rw [hone]
  simp only [Algebra.smul_def, mul_one, mul_zero, add_zero]

/-- The differential structure defined by an explicit separable power-basis presentation. -/
@[reducible] def extensionDifferential
    (S : SeparablePowerBasisPresentation F E) : Differential E :=
  ⟨S.extensionDerivation⟩

/-- The explicit differential structure extends the differential structure on the base field. -/
theorem extensionDifferential_isDifferentialExtension
    (S : SeparablePowerBasisPresentation F E) :
    IsDifferentialExtension F E S.extensionDifferential := by
  letI : Differential E := S.extensionDifferential
  change DifferentialAlgebra F E
  apply differentialAlgebra_iff_deriv_algebraMap.mpr
  intro a
  exact S.extensionDerivation_algebraMap a

omit [Differential F] in
/-- A derivation on a commutative ring has the expected value on natural powers. -/
theorem derivation_pow_eq_nsmul (e : Derivation ℤ E E) (a : E) :
    ∀ n : ℕ, e (a ^ n) = (n • a ^ (n - 1)) * e a
  | 0 => by
      rw [pow_zero, e.map_one_eq_zero, zero_nsmul, zero_mul]
  | n + 1 => by
      rw [pow_succ, e.leibniz, derivation_pow_eq_nsmul e a n]
      simp only [Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply]
      rcases n with _ | n
      · simp
      · rw [Nat.add_sub_cancel n 1]
        rw [Nat.add_sub_cancel (n + 1) 1]
        rw [pow_succ]
        rw [map_add, map_add, map_add, map_one]
        ring

omit [Differential F] in
/-- A derivation vanishing on the base field is determined by its value on the generator. -/
theorem derivation_eq_coordinateSlope_mul
    (S : SeparablePowerBasisPresentation F E) (e : Derivation ℤ E E)
    (hbase : ∀ a : F, e (algebraMap F E a) = 0) (x : E) :
    e x = S.coordinateSlope x * e S.powerBasis.gen := by
  let c := S.powerBasis.coord x
  have hx :
      x = PowerBasisPresentation.evalPowerCoordinates S.powerBasis.gen
        S.powerBasis.dim c := by
    rw [← S.powerBasis.coord_symm_eq_evalPowerCoordinates]
    simp [c]
  rw [hx]
  have aux :
      ∀ (n : ℕ) (hn : n ≤ S.powerBasis.dim) (d : Fin n → F),
        e (PowerBasisPresentation.evalPowerCoordinates S.powerBasis.gen n d) =
          S.coordinateSlope
              (PowerBasisPresentation.evalPowerCoordinates S.powerBasis.gen n d) *
            e S.powerBasis.gen := by
    intro n
    induction n with
    | zero =>
        intro hn d
        simp [PowerBasisPresentation.evalPowerCoordinates]
    | succ n ih =>
        intro hn d
        have hnlt : n < S.powerBasis.dim := by omega
        rw [PowerBasisPresentation.evalPowerCoordinates, map_add,
          S.coordinateSlope_add]
        rw [ih (by omega) (fun i => d i.castSucc)]
        have hterm :
            e (algebraMap F E (d (Fin.last n)) * S.powerBasis.gen ^ n) =
              S.coordinateSlope
                  (algebraMap F E (d (Fin.last n)) * S.powerBasis.gen ^ n) *
                e S.powerBasis.gen := by
          rw [e.leibniz, hbase, derivation_pow_eq_nsmul]
          rw [← Algebra.smul_def, S.coordinateSlope_smul,
            S.coordinateSlope_gen_pow ⟨n, hnlt⟩]
          simp only [Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply,
            mul_zero, add_zero]
          ring
        rw [hterm]
        ring
  exact aux S.powerBasis.dim (Nat.le_refl _) c

omit [Differential F] in
/-- The coordinate slope of the leading generator power is the reduced relation slope. -/
theorem coordinateSlope_gen_pow_dim (S : SeparablePowerBasisPresentation F E) :
    S.coordinateSlope (S.powerBasis.gen ^ S.powerBasis.dim) =
      S.powerBasis.coord.symm
        (S.powerBasis.coordinateDerivative S.powerBasis.relationCoeffs) := by
  simp [coordinateSlope, PowerBasisPresentation.relationCoeffs]

/-- Any compatible differential structure equals the one defined by the presentation. -/
theorem extensionDifferential_unique
    (S : SeparablePowerBasisPresentation F E) (Γ : Differential E)
    (hΓ : IsDifferentialExtension F E Γ) :
    Γ = S.extensionDifferential := by
  let e : Derivation ℤ E E := Γ.deriv - S.extensionDerivation
  have hbase (a : F) : e (algebraMap F E a) = 0 := by
    change Γ.deriv (algebraMap F E a) -
      S.extensionDerivation (algebraMap F E a) = 0
    rw [hΓ.deriv_algebraMap, S.extensionDerivation_algebraMap]
    exact sub_self _
  have hcoord (x : E) :
      e x = S.coordinateSlope x * e S.powerBasis.gen :=
    S.derivation_eq_coordinateSlope_mul e hbase x
  have hpow : e (S.powerBasis.gen ^ S.powerBasis.dim) =
      (S.powerBasis.dim • S.powerBasis.gen ^ (S.powerBasis.dim - 1)) *
        e S.powerBasis.gen := by
    exact derivation_pow_eq_nsmul e S.powerBasis.gen S.powerBasis.dim
  have hmul :
      S.powerBasis.relationDerivative * e S.powerBasis.gen = 0 := by
    rw [PowerBasisPresentation.relationDerivative,
      ← S.coordinateSlope_gen_pow_dim]
    calc
      (S.powerBasis.dim • S.powerBasis.gen ^ (S.powerBasis.dim - 1) -
            S.coordinateSlope (S.powerBasis.gen ^ S.powerBasis.dim)) *
          e S.powerBasis.gen =
        (S.powerBasis.dim • S.powerBasis.gen ^ (S.powerBasis.dim - 1)) *
            e S.powerBasis.gen -
          S.coordinateSlope (S.powerBasis.gen ^ S.powerBasis.dim) *
            e S.powerBasis.gen := by ring
      _ = e (S.powerBasis.gen ^ S.powerBasis.dim) -
          e (S.powerBasis.gen ^ S.powerBasis.dim) := by
            rw [← hpow, ← hcoord]
      _ = 0 := sub_self _
  have hegen : e S.powerBasis.gen = 0 := by
    calc
      e S.powerBasis.gen =
          1 * e S.powerBasis.gen := by rw [one_mul]
      _ = (S.powerBasis.relationDerivative * S.relationDerivativeInv) *
          e S.powerBasis.gen := by rw [S.relationDerivative_mul_inv]
      _ = S.relationDerivativeInv *
          (S.powerBasis.relationDerivative * e S.powerBasis.gen) := by ring
      _ = 0 := by rw [hmul, mul_zero]
  have hezero : e = 0 := by
    ext x
    rw [hcoord x, hegen, mul_zero]
    rfl
  apply Differential.ext
  exact sub_eq_zero.mp hezero

/-- An explicit separable power-basis presentation gives a unique differential extension. -/
theorem existsUnique_differentialExtension
    (S : SeparablePowerBasisPresentation F E) :
    ∃! Δ : Differential E, IsDifferentialExtension F E Δ :=
  ⟨S.extensionDifferential, S.extensionDifferential_isDifferentialExtension,
    S.extensionDifferential_unique⟩

end SeparablePowerBasisPresentation

example
    {F E : Type*} [Field F] [Differential F] [Field E] [Algebra F E]
    (S : SeparablePowerBasisPresentation F E) :
    ∃! Δ : Differential E, IsDifferentialExtension F E Δ :=
  S.existsUnique_differentialExtension

end DeepWiki.SymbolicIntegration
