import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic

/-! # Differential polynomials

Formal polynomial expressions in a base variable and derivative variables. -/

namespace DeepWiki.SymbolicIntegration

open Polynomial MvPolynomial

variable {K : Type*} [Field K]

/-- The differential-variable polynomial ring with `X none` for `x` and `X (some n)` for `u^(n)`. -/
abbrev DiffPoly (K : Type*) [Field K] : Type _ := MvPolynomial (Option ℕ) K

/-- The base variable `x = X none` in `DiffPoly K`. -/
noncomputable abbrev dpX : DiffPoly K := X none

/-- The `n`-th derivative variable `u^(n) = X (some n)` in `DiffPoly K`. -/
noncomputable abbrev dpU (n : ℕ) : DiffPoly K := X (some n)

/-- The embedding `K[x] → DiffPoly K` sending `X` to `dpX`. -/
noncomputable def dpEmbed : Polynomial K →+* DiffPoly K :=
  Polynomial.eval₂RingHom (MvPolynomial.C : K →+* DiffPoly K) (X none)

/-- `dpEmbed` sends the polynomial variable to `dpX`. -/
@[simp] theorem dpEmbed_X : dpEmbed (Polynomial.X : Polynomial K) = (X none : DiffPoly K) := by
  simp [dpEmbed]

/-- `dpEmbed` sends a constant polynomial to the matching `MvPolynomial` constant. -/
@[simp] theorem dpEmbed_C (c : K) : dpEmbed (Polynomial.C c) = (MvPolynomial.C c : DiffPoly K) := by
  simp [dpEmbed]

/-- The `d/dx` derivation on `DiffPoly K`, with `ddx x = 1` and `ddx u^(n) = u^(n+1)`. -/
noncomputable def ddx : Derivation K (DiffPoly K) (DiffPoly K) :=
  MvPolynomial.mkDerivation K fun v => match v with
    | none => 1
    | some n => X (some (n + 1))

/-- `ddx dpX = 1`. -/
@[simp] theorem ddx_x : ddx (dpX : DiffPoly K) = 1 := by
  simp [ddx, dpX]

/-- `ddx (dpU n) = dpU (n + 1)`. -/
@[simp] theorem ddx_u (n : ℕ) : ddx (dpU n : DiffPoly K) = dpU (n + 1) := by
  simp [ddx, dpU]

/-- `ddx` kills constants from `K`. -/
@[simp] theorem ddx_C (c : K) : ddx (MvPolynomial.C c : DiffPoly K) = 0 := by
  rw [← MvPolynomial.algebraMap_eq]
  exact (ddx (K := K)).map_algebraMap c

/-- `ddx` of an embedded polynomial is the embedded formal derivative. -/
theorem ddx_dpEmbed (p : Polynomial K) : ddx (dpEmbed p) = dpEmbed (Polynomial.derivative p) := by
  induction p using Polynomial.induction_on with
  | C c => simp [dpEmbed]
  | add p q hp hq => simp [hp, hq]
  | monomial n c _ih =>
      rw [Polynomial.derivative_C_mul_X_pow, Nat.add_sub_cancel]
      have hembed : dpEmbed (Polynomial.C c * Polynomial.X ^ (n + 1))
          = MvPolynomial.C c * (X none : DiffPoly K) ^ (n + 1) := by
        simp [dpEmbed]
      have hembedR : dpEmbed (Polynomial.C (c * (↑(n + 1) : K)) * Polynomial.X ^ n)
          = MvPolynomial.C c * (↑(n + 1) : DiffPoly K) * (X none : DiffPoly K) ^ n := by
        rw [map_mul, map_pow, dpEmbed_X, dpEmbed_C, map_mul, map_natCast]
      rw [hembed, hembedR, Derivation.leibniz, ddx_C, smul_zero, add_zero,
        Derivation.leibniz_pow, ddx_x, Nat.add_sub_cancel]
      simp only [smul_eq_mul, mul_one, nsmul_eq_mul]
      push_cast
      ring

/-! ## Differential substitutions -/

/-- The differential substitution hom `DiffPoly K →ₐ[K] K[x]` sending `x` to `X` and `u^(k)` to `Diα^(k)`. -/
noncomputable def diffSubst (Diα : K[X]) : DiffPoly K →ₐ[K] K[X] :=
  MvPolynomial.aeval fun v => match v with
    | none => Polynomial.X
    | some k => derivative^[k] Diα

/-- `diffSubst` sends the base variable to `X`. -/
@[simp] theorem diffSubst_X_none (Diα : K[X]) :
    diffSubst Diα (X none : DiffPoly K) = Polynomial.X := by
  simp [diffSubst]

/-- `diffSubst` sends `u^(k)` to the `k`-th derivative of `Diα`. -/
@[simp] theorem diffSubst_X_some (Diα : K[X]) (k : ℕ) :
    diffSubst Diα (X (some k) : DiffPoly K) = derivative^[k] Diα := by
  simp [diffSubst]

/-- `diffSubst` sends constants to constant polynomials. -/
@[simp] theorem diffSubst_C (Diα : K[X]) (a : K) :
    diffSubst Diα (MvPolynomial.C a : DiffPoly K) = Polynomial.C a := by
  simp [diffSubst]

/-- `diffSubst` undoes `dpEmbed` on pure `x`-polynomials. -/
@[simp] theorem diffSubst_dpEmbed (Diα p : K[X]) : diffSubst Diα (dpEmbed p) = p := by
  have h : ((diffSubst Diα : DiffPoly K →ₐ[K] K[X]).toRingHom.comp dpEmbed) = RingHom.id K[X] := by
    apply Polynomial.ringHom_ext
    · intro c; simp [dpEmbed]
    · simp [dpEmbed]
  exact congrArg (fun f : K[X] →+* K[X] => f p) h

/-- `diffSubst Diα` carries `ddx` to the polynomial derivative. -/
theorem diffSubst_ddx (Diα : K[X]) (p : DiffPoly K) :
    diffSubst Diα (ddx p) = derivative (diffSubst Diα p) := by
  induction p using MvPolynomial.induction_on with
  | C a => rw [← MvPolynomial.algebraMap_eq, (ddx (K := K)).map_algebraMap, map_zero,
      AlgHom.commutes, Polynomial.algebraMap_eq, derivative_C]
  | add p q hp hq => rw [map_add, map_add, map_add, derivative_add, hp, hq]
  | mul_X p v hp =>
      have hbase : diffSubst Diα (ddx (X v : DiffPoly K)) = derivative (diffSubst Diα (X v)) := by
        cases v with
        | none => rw [ddx_x, map_one, diffSubst_X_none, derivative_X]
        | some k =>
            rw [show ddx (X (some k) : DiffPoly K) = X (some (k + 1)) from ddx_u k,
              diffSubst_X_some, diffSubst_X_some, ← Function.iterate_succ_apply' derivative k Diα]
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, hp, hbase,
        map_mul, derivative_mul]
      ring

/-- `(aeval f P).eval α = aeval (fun v => (f v).eval α) P`. -/
theorem eval_aeval_diffPoly (f : Option ℕ → K[X]) (α : K) (P : DiffPoly K) :
    Polynomial.eval α (MvPolynomial.aeval f P) = MvPolynomial.aeval (fun v => (f v).eval α) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp => simp [hp]

/-- The point substitution `x ↦ α`, `u^(k) ↦ (Diα^(k)).eval α`. -/
noncomputable def substEvalAt (Diα : K[X]) (α : K) : Option ℕ → K := fun v =>
  match v with
  | none => α
  | some k => (derivative^[k] Diα).eval α

/-- `(diffSubst Diα P).eval α = aeval (substEvalAt Diα α) P`. -/
theorem eval_diffSubst (Diα : K[X]) (α : K) (P : DiffPoly K) :
    Polynomial.eval α (diffSubst Diα P) = MvPolynomial.aeval (substEvalAt Diα α) P := by
  rw [diffSubst, eval_aeval_diffPoly]
  have hfun : (fun v => Polynomial.eval α
        (match v with | (none : Option ℕ) => Polynomial.X | some k => derivative^[k] Diα))
      = substEvalAt Diα α := by
    funext v
    cases v with
    | none => simp [substEvalAt]
    | some k => simp [substEvalAt]
  exact congrArg (fun f => MvPolynomial.aeval f P) hfun

/-! ## Fraction-field derivation -/

/-- The quotient-rule fraction `(ddx p * q - p * ddx q) / q^2` in `Frac (DiffPoly K)`. -/
private noncomputable def fracDerivAux (p : DiffPoly K) (q : nonZeroDivisors (DiffPoly K)) :
    FractionRing (DiffPoly K) :=
  Localization.mk (ddx p * (q : DiffPoly K) - p * ddx (q : DiffPoly K))
    ⟨(q : DiffPoly K) ^ 2, pow_mem q.2 2⟩

private theorem fracDerivAux_wd {p p' : DiffPoly K} {q q' : nonZeroDivisors (DiffPoly K)}
    (h : (Localization.r (nonZeroDivisors (DiffPoly K))) (p, q) (p', q')) :
    fracDerivAux p q = fracDerivAux p' q' := by
  rw [Localization.r_iff_exists] at h
  obtain ⟨c, hc⟩ := h
  have hc0 : (c : DiffPoly K) ≠ 0 := nonZeroDivisors.coe_ne_zero c
  have key : (q' : DiffPoly K) * p = (q : DiffPoly K) * p' := mul_left_cancel₀ hc0 (by simpa using hc)
  have keyd := congrArg ddx key
  rw [Derivation.leibniz, Derivation.leibniz] at keyd
  simp only [smul_eq_mul] at keyd
  unfold fracDerivAux
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul]
  show ((q' : DiffPoly K) ^ 2) * (ddx p * (q : DiffPoly K) - p * ddx (q : DiffPoly K))
      = ((q : DiffPoly K) ^ 2) * (ddx p' * (q' : DiffPoly K) - p' * ddx (q' : DiffPoly K))
  linear_combination ((q : DiffPoly K) * (q' : DiffPoly K)) * keyd
    - ((q : DiffPoly K) * ddx (q' : DiffPoly K) + (q' : DiffPoly K) * ddx (q : DiffPoly K)) * key

/-- The quotient-rule derivative on `FractionRing (DiffPoly K)` extending `ddx`. -/
noncomputable def fracDeriv (x : FractionRing (DiffPoly K)) : FractionRing (DiffPoly K) :=
  Localization.liftOn x fracDerivAux (fun h => fracDerivAux_wd h)

/-- Quotient rule for `fracDeriv` on a localization representative. -/
theorem fracDeriv_mk (p : DiffPoly K) (q : nonZeroDivisors (DiffPoly K)) :
    fracDeriv (Localization.mk p q) = fracDerivAux p q :=
  Localization.liftOn_mk _ _ _ _

/-- `Localization.mk a b = Localization.mk c d` from cross-multiplication `d * a = b * c`. -/
theorem diffPoly_fraction_mk_eq_of_cross_mul {a c : DiffPoly K} {b d : nonZeroDivisors (DiffPoly K)}
    (h : (d : DiffPoly K) * a = (b : DiffPoly K) * c) :
    (Localization.mk a b : FractionRing (DiffPoly K)) = Localization.mk c d := by
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp only [OneMemClass.coe_one, one_mul]; exact h⟩

/-- `fracDeriv` extends `ddx` through the algebra map into the fraction field. -/
theorem fracDeriv_algebraMap (p : DiffPoly K) :
    fracDeriv (algebraMap (DiffPoly K) (FractionRing (DiffPoly K)) p)
      = algebraMap (DiffPoly K) (FractionRing (DiffPoly K)) (ddx p) := by
  rw [← Localization.mk_one_eq_algebraMap, fracDeriv_mk]
  unfold fracDerivAux
  rw [← Localization.mk_one_eq_algebraMap]
  apply diffPoly_fraction_mk_eq_of_cross_mul
  simp

/-- `fracDeriv` is additive. -/
theorem fracDeriv_add (x y : FractionRing (DiffPoly K)) :
    fracDeriv (x + y) = fracDeriv x + fracDeriv y := by
  induction x using Localization.induction_on with | _ px =>
  induction y using Localization.induction_on with | _ py =>
  obtain ⟨p, q⟩ := px; obtain ⟨r, s⟩ := py
  rw [Localization.add_mk, fracDeriv_mk, fracDeriv_mk, fracDeriv_mk]
  unfold fracDerivAux
  rw [Localization.add_mk]
  apply diffPoly_fraction_mk_eq_of_cross_mul
  push_cast
  simp only [map_add, Derivation.leibniz, smul_eq_mul]
  ring

/-- `fracDeriv` satisfies the Leibniz rule. -/
theorem fracDeriv_mul (x y : FractionRing (DiffPoly K)) :
    fracDeriv (x * y) = fracDeriv x * y + x * fracDeriv y := by
  induction x using Localization.induction_on with | _ px =>
  induction y using Localization.induction_on with | _ py =>
  obtain ⟨p, q⟩ := px; obtain ⟨r, s⟩ := py
  rw [Localization.mk_mul, fracDeriv_mk, fracDeriv_mk, fracDeriv_mk]
  unfold fracDerivAux
  rw [Localization.mk_mul, Localization.mk_mul, Localization.add_mk]
  apply diffPoly_fraction_mk_eq_of_cross_mul
  push_cast
  simp only [Derivation.leibniz, smul_eq_mul]
  ring

/-- `fracDeriv` is `K`-linear. -/
theorem fracDeriv_smul (c : K) (x : FractionRing (DiffPoly K)) :
    fracDeriv (c • x) = c • fracDeriv x := by
  induction x using Localization.induction_on with | _ px =>
  obtain ⟨p, q⟩ := px
  rw [Localization.smul_mk, fracDeriv_mk, fracDeriv_mk]
  unfold fracDerivAux
  rw [Localization.smul_mk]
  apply diffPoly_fraction_mk_eq_of_cross_mul
  have hc : ddx (c • p) = c • ddx p := map_smul ddx.toLinearMap c p
  rw [hc, MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul]
  ring

/-- The `K`-derivation on `FractionRing (DiffPoly K)` induced by `ddx`. -/
noncomputable def fracKDeriv :
    Derivation K (FractionRing (DiffPoly K)) (FractionRing (DiffPoly K)) :=
  Derivation.mk'
    { toFun := fracDeriv, map_add' := fracDeriv_add,
      map_smul' := fun c x => by simpa using fracDeriv_smul c x }
    fun a b => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
      rw [fracDeriv_mul]
      ring

/-- `fracKDeriv` is definitionally `fracDeriv` as a function. -/
@[simp] theorem fracKDeriv_apply (x : FractionRing (DiffPoly K)) : fracKDeriv x = fracDeriv x := rfl

/-- `fracKDeriv` extends `ddx` through the algebra map into the fraction field. -/
theorem fracKDeriv_algebraMap (p : DiffPoly K) :
    fracKDeriv (algebraMap (DiffPoly K) (FractionRing (DiffPoly K)) p)
      = algebraMap (DiffPoly K) (FractionRing (DiffPoly K)) (ddx p) :=
  fracDeriv_algebraMap p

end DeepWiki.SymbolicIntegration
