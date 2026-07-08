import DeepWiki.SymbolicIntegration.Computable.FractionFieldDerivLinearFactor
import DeepWiki.SymbolicIntegration.Computable.LogPartTowerSoundness
import DeepWiki.SymbolicIntegration.Computable.Algebraic.RadicalLogSoundness
import DeepWiki.SymbolicIntegration.PartialFraction
import DeepWiki.SymbolicIntegration.ResidueMultiplicity
import DeepWiki.SymbolicIntegration.Core.Differential.ImplicitDerivLinearFactors

/-! # The Rothstein–Trager residue-match identity over a monomial tower

Builds the residue-match identity `∑ᵢ cᵢ·D(log vᵢ) = a/d` over `RatFunc (CFieldSpec.K α)` for the
monomial derivation `D = cmonomialDeriv Dt` (where `D(t−α) = Dt − α′ ≠ 1`, so the residue must absorb
the `Dt − α′` factor). Proves the absorption identity at a simple root, the unconditional primitive-case
match, and the general-monomial match modulo a polynomial-part cancellation hypothesis — toward
discharging the `hmatch` hypothesis of `logResidueSumG_eq_of_residue_match`. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

namespace ResidueMatchTower

variable {K : Type*} [Field K] [Differential K]

/-! ### The per-place residue matches the standard residue -/

/-- **The RT residue recovers the standard residue at a simple root** — for `d(α) = 0` with `v(α) ≠ α′`
(normal, so `(Dd)(α) ≠ 0`), the RT residue `c_α = a(α)/(Dd)(α)` satisfies
`c_α·(v(α) − α′) = a(α)/d′(α)`. From `eval_implicitDeriv_of_isRoot`. -/
theorem residue_mul_eval_sub_eq (a v d : K[X]) (α : K) (hα : d.eval α = 0)
    (hvα : v.eval α ≠ α′) :
    (a.eval α / (Differential.implicitDeriv v d).eval α) * (v.eval α - α′)
      = a.eval α / (derivative d).eval α := by
  rw [eval_implicitDeriv_of_isRoot v d α hα]
  rw [div_mul_eq_mul_div, mul_comm ((derivative d).eval α), ← div_div,
    mul_div_assoc, div_self (sub_ne_zero.mpr hvα), mul_one]

/-! ### The primitive-monomial RT partial fraction (`Dt = C w` in the base field)

For a **primitive** monomial `Dt = C w` (e.g. `t = log η`), the log-derivative `D(t−α)/(t−α)` is the
constant `C(w − α′)/(t−α)` with no polynomial part, so the RT sum matches `a/d` term by term. The
non-primitive cases (`deg_t v ≥ 1`) need a polynomial-part cancellation, isolated below. -/

variable [Algebra ℚ K]

/-- **The primitive-case monomial Rothstein–Trager partial fraction** — for a squarefree
`d = ∏_{α∈s}(t−α)`, `deg a < #s`, a primitive monomial `Dt = C w`, and every root normal (`w ≠ α′`), the
monomial RT residue sum equals `a/d`: `∑_{α∈s} C(c_α)·(D(t−α)/(t−α)) = a/d` with `c_α = a(α)/(Dd)(α)`,
`D = extendDeriv (implicitDeriv (C w))`. The unconditional residue match for primitive (logarithmic)
tower extensions. -/
theorem primitive_monomial_residue_match (s : Finset K) (a : K[X]) (w : K)
    (hA : a.degree < s.card) (hnorm : ∀ α ∈ s, w ≠ α′) :
    ∑ α ∈ s, algebraMap K[X] (RatFunc K)
          (C (a.eval α / (Differential.implicitDeriv (C w) (Lagrange.nodal s id)).eval α))
        * (extendDeriv (Differential.implicitDeriv (C w))
              (algebraMap K[X] (RatFunc K) (X - C α))
            / algebraMap K[X] (RatFunc K) (X - C α))
      = algebraMap K[X] (RatFunc K) a / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id) := by
  rw [ratFunc_eq_sum_residue_div s a hA]
  refine Finset.sum_congr rfl fun α hα => ?_
  -- per-term: monomial log-derivative is the constant `C(w−α′)/(t−α)`
  rw [extendDeriv_implicitDeriv_C_logDeriv_X_sub_C]
  -- fold the residue coefficient into the constant numerator
  rw [← mul_div_assoc, ← map_mul, ← C_mul]
  -- `c_α·(w − α′) = a(α)/d′(α)` via residue_mul_eval_sub_eq (with `v = C w`, `v.eval α = w`)
  have hroot : (Lagrange.nodal s id).eval α = 0 := by
    have := Lagrange.eval_nodal_at_node (s := s) (v := (id : K → K)) hα
    simpa using this
  have h := residue_mul_eval_sub_eq a (C w) (Lagrange.nodal s id) α hroot
    (by simpa using hnorm α hα)
  rw [eval_C] at h
  -- both sides are `algebraMap (C ·) / algebraMap (t − α)`; the constants agree by `h`
  rw [h]

/-! ### The general monomial RT partial fraction, modulo polynomial-part cancellation

For a non-primitive monomial (`deg_t v ≥ 1`), `D(t−α)/(t−α)` carries a polynomial part
`q_α = (v − Cα′) /ₘ (t−α)`, and the RT sum equals `a/d` iff `∑_α c_α·q_α = 0` (an integrability
condition, automatic in the primitive case). This is isolated as the hypothesis `hcancel`. -/

/-- **The general monomial Rothstein–Trager partial fraction, modulo polynomial-part cancellation** —
for a squarefree `d = ∏_{α∈s}(t−α)`, `deg a < #s`, an arbitrary monomial `Dt = v`, every root normal
(`v(α) ≠ α′`), and the polynomial parts cancelling (`hcancel : ∑_{α∈s} C(c_α)·((v − Cα′) /ₘ (t−α)) = 0`),
the monomial RT residue sum equals `a/d`: `∑_{α∈s} C(c_α)·(D(t−α)/(t−α)) = a/d`, `c_α = a(α)/(Dd)(α)`,
`D = extendDeriv (implicitDeriv v)`. The `hcancel` hypothesis is automatic in the primitive case. -/
theorem monomial_residue_match_of_cancel (s : Finset K) (a v : K[X])
    (hA : a.degree < s.card) (hnorm : ∀ α ∈ s, v.eval α ≠ α′)
    (hcancel : ∑ α ∈ s, algebraMap K[X] (RatFunc K)
        (C (a.eval α / (Differential.implicitDeriv v (Lagrange.nodal s id)).eval α)
          * ((v - C (α′)) /ₘ (X - C α))) = 0) :
    ∑ α ∈ s, algebraMap K[X] (RatFunc K)
          (C (a.eval α / (Differential.implicitDeriv v (Lagrange.nodal s id)).eval α))
        * (extendDeriv (Differential.implicitDeriv v)
              (algebraMap K[X] (RatFunc K) (X - C α))
            / algebraMap K[X] (RatFunc K) (X - C α))
      = algebraMap K[X] (RatFunc K) a / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id) := by
  -- abbreviation for the RT residue at `α`
  set c : K → K := fun α => a.eval α / (Differential.implicitDeriv v (Lagrange.nodal s id)).eval α
    with hc
  -- rewrite each summand: monomial log-derivative, then euclidean split
  have hterm : ∀ α ∈ s,
      algebraMap K[X] (RatFunc K) (C (c α))
          * (extendDeriv (Differential.implicitDeriv v) (algebraMap K[X] (RatFunc K) (X - C α))
              / algebraMap K[X] (RatFunc K) (X - C α))
        = algebraMap K[X] (RatFunc K) (C (c α) * ((v - C (α′)) /ₘ (X - C α)))
          + algebraMap K[X] (RatFunc K) (C (a.eval α / (derivative (Lagrange.nodal s id)).eval α))
              / algebraMap K[X] (RatFunc K) (X - C α) := by
    intro α hα
    rw [extendDeriv_implicitDeriv_logDeriv_X_sub_C, algebraMap_div_X_sub_C_split (v - C (α′)) α,
      mul_add, ← map_mul]
    congr 1
    -- the residue term: `C(c_α)·C((v−Cα′)(α))/(t−α) = C(a(α)/d′(α))/(t−α)`
    rw [eval_sub, eval_C, ← mul_div_assoc, ← map_mul, ← C_mul]
    have hroot : (Lagrange.nodal s id).eval α = 0 := by
      simpa using Lagrange.eval_nodal_at_node (s := s) (v := (id : K → K)) hα
    rw [hc]
    rw [residue_mul_eval_sub_eq a v (Lagrange.nodal s id) α hroot (hnorm α hα)]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← map_sum, hc] at *
  rw [hcancel, zero_add, ← ratFunc_eq_sum_residue_div s a hA]

/-! ### The primitive case: the cancellation is automatic

For a primitive monomial `Dt = C w`, each polynomial part `(C w − Cα′) /ₘ (X−Cα)` is `0`, so `hcancel`
holds termwise. -/

omit [Algebra ℚ K] in
/-- **Primitive monomials cancel automatically** — for `Dt = C w`, each polynomial part `(C w − Cα′) /ₘ
(X−Cα)` is `0`, so the `hcancel` hypothesis of `monomial_residue_match_of_cancel` holds termwise. -/
theorem primitive_cancel (s : Finset K) (a : K[X]) (w : K) :
    ∑ α ∈ s, algebraMap K[X] (RatFunc K)
        (C (a.eval α / (Differential.implicitDeriv (C w) (Lagrange.nodal s id)).eval α)
          * ((C w - C (α′)) /ₘ (X - C α))) = 0 := by
  apply Finset.sum_eq_zero
  intro α _
  have hdeg : (C w - C (α′)).degree < (X - C α).degree := by
    rw [degree_X_sub_C]
    calc (C w - C (α′)).degree ≤ max (C w).degree (C (α′)).degree := degree_sub_le _ _
      _ ≤ 0 := max_le degree_C_le degree_C_le
      _ < 1 := by decide
  rw [(divByMonic_eq_zero_iff (monic_X_sub_C α)).mpr hdeg, mul_zero, map_zero]

end ResidueMatchTower

/-! ### The primitive RT residue match in the engine's vocabulary

Restated over `amG α = algebraMap (CFieldSpec.K α)[X] (RatFunc (CFieldSpec.K α))` and
`towerFractionFieldDerivG Dt`, in the form `logResidueSumG_eq_of_residue_match` consumes. -/

open Compute CPolyG QFunNZG

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

/-- **The primitive RT residue match in the engine's `amG`/`towerFractionFieldDerivG` vocabulary** — for
a primitive monomial with `toPolyG Dt = C w`, a squarefree `d = ∏_{α∈s}(t−α)`, `deg a < #s`, and every
root normal, the engine-shaped residue sum `∑_{α∈s} amG(C(c_α))·(D(t−α)/(t−α)) = a/d` over
`RatFunc (CFieldSpec.K α)`, with `D = towerFractionFieldDerivG Dt`. The unconditional `hmatch` for
primitive tower extensions. -/
theorem primitive_monomial_residue_match_engine (Dt : CPolyG α) (s : Finset (CFieldSpec.K α))
    (a : (CFieldSpec.K α)[X]) (w : CFieldSpec.K α) (hDt : toPolyG Dt = C w)
    (hA : a.degree < s.card) (hnorm : ∀ β ∈ s, w ≠ β′) :
    ∑ β ∈ s, amG α
          (C (a.eval β / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β))
        * (towerFractionFieldDerivG Dt (amG α (X - C β)) / amG α (X - C β))
      = amG α a / amG α (Lagrange.nodal s id) := by
  show ∑ β ∈ s, algebraMap (CFieldSpec.K α)[X] (RatFunc (CFieldSpec.K α))
          (C (a.eval β / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β))
        * (extendDeriv (Differential.implicitDeriv (toPolyG Dt))
              (algebraMap _ (RatFunc (CFieldSpec.K α)) (X - C β))
            / algebraMap _ (RatFunc (CFieldSpec.K α)) (X - C β))
      = _
  rw [hDt]
  exact ResidueMatchTower.primitive_monomial_residue_match s a w hA hnorm

/-! ### Status

Proven: the absorption identity at a simple root (`eval_implicitDeriv_of_isRoot`), the unconditional
primitive-case match (`primitive_monomial_residue_match`, and `primitive_monomial_residue_match_engine`),
and the general-case match modulo cancellation (`monomial_residue_match_of_cancel`, with `hcancel`
automatic in the primitive case via `primitive_cancel`).

Remaining for the full unconditional match (all monomials): the non-primitive polynomial cancellation
`∑ c_α·((v−Cα′) /ₘ (t−α)) = 0` (an integrability condition, e.g. `∑ c_α = 0` for `Dt = η′·t`), and the
`List`↔`Finset` + grouped-GCD bridge to `logResidueSumG_eq_of_residue_match`. -/

#print axioms ResidueMatchTower.primitive_monomial_residue_match
#print axioms ResidueMatchTower.monomial_residue_match_of_cancel
#print axioms ResidueMatchTower.primitive_cancel
#print axioms primitive_monomial_residue_match_engine

end DeepWiki.SymbolicIntegration
