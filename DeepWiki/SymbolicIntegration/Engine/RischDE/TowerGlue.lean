import DeepWiki.SymbolicIntegration.Engine.FuelFreeDiophantine

/-! # Generic RDE glue lemmas

Carrier-agnostic algebraic glue lemmas consumed by the tower RDE correctness: pure `Derivation`
algebra and generic-engine `toPoly` divisibility/Diophantine facts. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-- SPDE-step gluing: with Bézout witness `b·r + a·z = c` and `h` solving the reduced equation
`a·D(h) + (b + D(a))·h = z − D(r)`, the reconstruction `q = a·h + r` solves `a·D(q) + b·q = c`. -/
theorem spde_step_glue {R : Type*} [CommRing R] (D : Derivation ℤ R R)
    (a b c r z h : R)
    (hbez : b * r + a * z = c)
    (hred : a * D h + (b + D a) * h = z - D r) :
    a * D (a * h + r) + b * (a * h + r) = c := by
  have hD : D (a * h + r) = a * D h + D a * h + D r := by
    rw [map_add, Derivation.leibniz]; simp only [smul_eq_mul]; ring
  rw [hD]
  have : a * (a * D h + D a * h + D r) + b * (a * h + r)
      = a * (a * D h + (b + D a) * h) + (a * D r + b * r) := by ring
  rw [this, hred]
  linear_combination hbez

/-- Constant-`a` base-case scaling: if `a₀ ≠ 0` and `h` solves `D(h) + (a₀⁻¹·b)·h = a₀⁻¹·c`, then `h`
solves `a₀·D(h) + b·h = c`. -/
theorem spde_const_base {K : Type*} [Field K] (D : Derivation ℤ K[X] K[X])
    (a0 : K) (b c h : K[X]) (ha0 : a0 ≠ 0)
    (hred : D h + (Polynomial.C a0⁻¹ * b) * h = Polynomial.C a0⁻¹ * c) :
    Polynomial.C a0 * D h + b * h = c := by
  have key : Polynomial.C a0 * (D h + (Polynomial.C a0⁻¹ * b) * h)
      = Polynomial.C a0 * (Polynomial.C a0⁻¹ * c) := by rw [hred]
  have hinv : Polynomial.C a0 * Polynomial.C a0⁻¹ = 1 := by
    rw [← Polynomial.C_mul, mul_inv_cancel₀ ha0, Polynomial.C_1]
  calc Polynomial.C a0 * D h + b * h
      = Polynomial.C a0 * (D h + (Polynomial.C a0⁻¹ * b) * h)
          - (Polynomial.C a0 * Polynomial.C a0⁻¹ - 1) * (b * h) := by ring
    _ = Polynomial.C a0 * (Polynomial.C a0⁻¹ * c) - (1 - 1) * (b * h) := by rw [key, hinv]
    _ = (Polynomial.C a0 * Polynomial.C a0⁻¹) * c := by ring
    _ = c := by rw [hinv, one_mul]

/-- Normal-denominator cleared lifting: with `DN ≠ 0`, `A = DN·H`, exact-division certificates
`B·FDEN = A·FNUM − DN·(D H)·FDEN` and `C·GDEN = DN·H²·GNUM`, and `Q` solving `A·D(Q) + B·Q = C`,
`y = Q/H` solves the cleared form
`GDEN·FDEN·(D(Q)·H − Q·(D H)) + GDEN·FNUM·Q·H = GNUM·FDEN·H²`. -/
theorem rdeNormalDenominator_glue {R : Type*} [CommRing R] [NoZeroDivisors R]
    (D : Derivation ℤ R R) (DN H FNUM FDEN GNUM GDEN A B C Q : R)
    (hDN : DN ≠ 0)
    (hA : A = DN * H)
    (hB : B * FDEN = A * FNUM - DN * D H * FDEN)
    (hC : C * GDEN = DN * H ^ 2 * GNUM)
    (hred : A * D Q + B * Q = C) :
    GDEN * FDEN * (D Q * H - Q * D H) + GDEN * FNUM * Q * H = GNUM * FDEN * H ^ 2 := by
  have hmul : FDEN * GDEN * (A * D Q + B * Q) = FDEN * GDEN * C := by rw [hred]
  have hkey : DN * (GDEN * FDEN * (D Q * H - Q * D H) + GDEN * FNUM * Q * H)
      = DN * (GNUM * FDEN * H ^ 2) := by
    have e1 : FDEN * GDEN * (A * D Q + B * Q)
        = GDEN * (A * D Q * FDEN) + GDEN * Q * (B * FDEN) := by ring
    have e2 : FDEN * GDEN * C = FDEN * (C * GDEN) := by ring
    rw [e1, e2, hB, hC, hA] at hmul
    linear_combination hmul
  exact mul_left_cancel₀ hDN hkey

/-- Special-denominator substitution expansion: for `p` with `D p = E·p`, the reconstruction `r = q·pᵏ`
expands as `a·D(r) + b·r = (a·D(q) + b·q + k·a·E·q)·pᵏ`. -/
theorem specialDenominatorSubst_expand {R : Type*} [CommRing R] (D : Derivation ℤ R R)
    (a b p E q : R) (k : ℕ) (hDp : D p = E * p) :
    a * D (q * p ^ k) + b * (q * p ^ k)
      = (a * D q + b * q + (k : R) * (a * E) * q) * p ^ k := by
  rw [Derivation.leibniz, Derivation.leibniz_pow, hDp]
  cases k with
  | zero => simp
  | succ k => simp only [Nat.add_sub_cancel, smul_eq_mul, Nat.cast_succ, pow_succ]; ring

/-- Special-denominator cleared identity: with `D p = E·p`, if the reduced identity
`a·D(q) + b·q + k·a·E·q = c` holds, then `r = q·pᵏ` solves `a·D(r) + b·r = c·pᵏ`. -/
theorem specialDenominatorSubst_cleared {R : Type*} [CommRing R] (D : Derivation ℤ R R)
    (a b c p E q : R) (k : ℕ) (hDp : D p = E * p)
    (hreduced : a * D q + b * q + (k : R) * (a * E) * q = c) :
    a * D (q * p ^ k) + b * (q * p ^ k) = c * p ^ k := by
  rw [specialDenominatorSubst_expand D a b p E q k hDp, hreduced]

namespace DensePoly

end DensePoly

/-! ### Axiom audit for the special-denominator substitution glue -/

#print axioms specialDenominatorSubst_expand
#print axioms specialDenominatorSubst_cleared

end DeepWiki.SymbolicIntegration
