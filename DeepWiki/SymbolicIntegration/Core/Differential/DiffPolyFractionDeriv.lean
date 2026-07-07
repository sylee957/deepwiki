import DeepWiki.SymbolicIntegration.Core.Differential.DifferentialPolynomials
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic

/-! # Fraction-field derivation for `DiffPoly`

The quotient-rule derivative on `FractionRing (DiffPoly K)` induced by `ddx`. -/

namespace DeepWiki.SymbolicIntegration

open MvPolynomial

variable {K : Type*} [Field K]

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
