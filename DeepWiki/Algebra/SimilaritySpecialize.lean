import DeepWiki.Algebra.PseudoDivision
import Mathlib.RingTheory.Polynomial.Content

/-! # Similarity under specialization

`IsSimilar` over `K[t][x]` descends through evaluation of the `t`-coefficients when the
left side is primitive: the similarity constants specialize to nonzero scalars. -/

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K] [DecidableEq K]

/-- **Similarity specializes through a primitive left side**: if `P` has content `1` and
`IsSimilar P X` over `K[t]`, then wherever the specialized `X` survives, the
specializations are similar over `K`. -/
theorem isSimilar_map_eval_of_content_eq_one {P X : Polynomial (Polynomial K)} (a : K)
    (hP : P.content = 1) (hsim : IsSimilar P X)
    (hXa : X.map (Polynomial.evalRingHom a) ≠ 0) :
    IsSimilar (P.map (Polynomial.evalRingHom a)) (X.map (Polynomial.evalRingHom a)) := by
  obtain ⟨c₁, c₂, hc₁, hc₂, heq⟩ := hsim
  have heq2 : Polynomial.C c₁ * P = Polynomial.C (c₂ * X.content) * X.primPart := by
    rw [map_mul, mul_assoc, ← Polynomial.eq_C_content_mul_primPart]
    exact heq
  have hcont2 := congrArg Polynomial.content heq2
  rw [Polynomial.content_C_mul, Polynomial.content_C_mul, hP, mul_one,
    Polynomial.content_primPart, mul_one] at hcont2
  have hassoc : Associated c₁ (c₂ * X.content) :=
    normalize_eq_normalize_iff_associated.mp hcont2
  obtain ⟨v, hv⟩ := hassoc
  have hc₁C : (Polynomial.C c₁ : Polynomial (Polynomial K)) ≠ 0 := by
    rw [Ne, Polynomial.C_eq_zero]
    exact hc₁
  have hP_eq : P = Polynomial.C (↑v : Polynomial K) * X.primPart := by
    apply mul_left_cancel₀ hc₁C
    rw [heq2, ← hv, map_mul, mul_assoc]
  have hXmap : X.map (Polynomial.evalRingHom a)
      = Polynomial.C (Polynomial.eval a X.content)
        * (X.primPart.map (Polynomial.evalRingHom a)) := by
    conv_lhs => rw [Polynomial.eq_C_content_mul_primPart X]
    rw [Polynomial.map_mul, Polynomial.map_C]
    rfl
  have hPmap : P.map (Polynomial.evalRingHom a)
      = Polynomial.C (Polynomial.eval a (↑v : Polynomial K))
        * (X.primPart.map (Polynomial.evalRingHom a)) := by
    conv_lhs => rw [hP_eq]
    rw [Polynomial.map_mul, Polynomial.map_C]
    rfl
  obtain ⟨r, hru, hrC⟩ := Polynomial.isUnit_iff.mp v.isUnit
  have hveval : Polynomial.eval a (↑v : Polynomial K) ≠ 0 := by
    rw [← hrC, Polynomial.eval_C]
    exact hru.ne_zero
  have hweval : Polynomial.eval a X.content ≠ 0 := by
    intro h0
    apply hXa
    rw [hXmap, h0, map_zero, zero_mul]
  exact ⟨Polynomial.eval a X.content, Polynomial.eval a (↑v : Polynomial K),
    hweval, hveval, by rw [hXmap, hPmap]; ring⟩

end DeepWiki.SymbolicIntegration
