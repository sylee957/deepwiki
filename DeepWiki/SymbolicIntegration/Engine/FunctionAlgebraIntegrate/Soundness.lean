import DeepWiki.SymbolicIntegration.Engine.FunctionAlgebraIntegrate.Abstract

/-! # Function-algebra recombination soundness

The recombination `F = Σᵢ eᵢ·Fᵢ` over `K(x)[y]/(T)` differentiates to the integrand when the
idempotent indicators form a partition of unity and each component is sound. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

universe u

open scoped Differential

namespace CPoly

/-- Recombine component antiderivatives as `Σᵢ eᵢ·Fᵢ` modulo a represented curve. -/
def afIntegrateFunctionAlgebra
    {P : Type u → Type u} [CPoly P] [CPolyEngine P] [CPolyEuclidean P]
    {α : Type u} [CField α] (f : P α) (es Fs : List (P α)) : P α :=
  ((es.zip Fs).map (fun p => CPoly.mulMod f p.1 p.2)).foldl CPolyEngine.add CPoly.czero

end CPoly

/-! Function-algebra recombination executes through sparse polynomial storage. -/

example :
    let f : CPoly.SparsePoly ℚ := CPoly.SparsePoly.ofList [(0, -1), (2, 1)]
    let x : CPoly.SparsePoly ℚ := CPoly.SparsePoly.ofList [(1, 1)]
    let z : CPoly.SparsePoly ℚ := CPoly.czero
    CPolyEngine.cisZero
      (CPolyEngine.sub (CPoly.afIntegrateFunctionAlgebra f [CPoly.one, z] [x, x]) x) = true := by
  ccompute

namespace DensePoly

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]

/-- Carrier-form idempotency `IsAfIdempotent T e`: `mk(toPoly(CPoly.mulMod T e e)) = mk(toPoly e)` in
`Q = K[X] ⧸ afIdeal T`, i.e. `e² = e` in `K(x)[y]/(T)`. -/
def IsAfIdempotent (f e : DensePoly α) : Prop :=
  Ideal.Quotient.mk (afIdeal f) (toPoly (CPoly.mulMod f e e))
    = Ideal.Quotient.mk (afIdeal f) (toPoly e)

omit [CDiffField α] [CDiffFieldSpec α] in
/-- `IsAfIdempotent T e` gives `IsIdempotentElem (mk(toPoly e))` in `Q = K[X] ⧸ afIdeal T`. -/
theorem IsAfIdempotent.isIdempotentElem {f e : DensePoly α} (hf : cnorm f ≠ [])
    (he : IsAfIdempotent f e) :
    IsIdempotentElem (Ideal.Quotient.mk (afIdeal f) (toPoly e)) := by
  rw [IsIdempotentElem, ← mk_toPoly_mulMod f e e hf, he]

/-- The engine's `afDerivWf` kills a carrier idempotent: for a separable curve `T` and idempotent
`e` (`IsAfIdempotent T e`), `mk(toPoly(afDerivWf T e)) = 0` in `Q = K[X] ⧸ afIdeal T`. -/
theorem IsAfIdempotent.isConstant {f e : DensePoly α} (he : IsAfIdempotent f e)
    (hf : cnorm f ≠ [])
    (hgdeg : (toPoly (CPolyEuclidean.gcdExt (cderiv f) f).1).natDegree = 0)
    (hgne : toPoly (CPolyEuclidean.gcdExt (cderiv f) f).1 ≠ 0) :
    Ideal.Quotient.mk (afIdeal f) (toPoly (afDerivWf f e)) = 0 := by
  set ē : (CFieldSpec.K α)[X] ⧸ afIdeal f :=
    Ideal.Quotient.mk (afIdeal f) (toPoly e) with hē
  set dē : (CFieldSpec.K α)[X] ⧸ afIdeal f :=
    Ideal.Quotient.mk (afIdeal f) (toPoly (afDerivWf f e)) with hdē
  -- Leibniz at `afDerivWf`: `D(e·e) = e·D e + e·D e` (pushed through `mk`)
  have hleib := mk_toPoly_afDerivWf_mulMod f e e hf hgdeg hgne
  rw [mk_toPoly_mulMod _ _ _ hf, mk_toPoly_mulMod _ _ _ hf] at hleib
  -- `afDerivWf` descends through `e² ≡ e`.
  have hdesc : Ideal.Quotient.mk (afIdeal f) (toPoly (afDerivWf f (CPoly.mulMod f e e)))
      = Ideal.Quotient.mk (afIdeal f) (toPoly (afDerivWf f e)) := by
    rw [mk_toPolyG_afDerivWf f _ hf, mk_toPolyG_afDerivWf f e hf]
    exact mk_implicitDerivWf_congr f hf hgdeg hgne he
  rw [hdesc, ← hdē, ← hē] at hleib
  -- the idempotency `ē·ē = ē` in `Q`
  have hidem : ē * ē = ē := he.isIdempotentElem hf
  -- `dē·(1 − 2ē) = 0`, and `(1 − 2ē)² = 1`, so `dē = 0`
  have h2 : dē * (1 - 2 * ē) = 0 := by linear_combination hleib
  have hsq : (1 - 2 * ē) * (1 - 2 * ē) = 1 := by linear_combination (4 : (CFieldSpec.K α)[X] ⧸ afIdeal f) * hidem
  calc dē = dē * ((1 - 2 * ē) * (1 - 2 * ē)) := by rw [hsq, mul_one]
    _ = (dē * (1 - 2 * ē)) * (1 - 2 * ē) := by ring
    _ = 0 := by rw [h2, zero_mul]

/-- Function-algebra soundness `D(F) = integrand` over a reducible curve: for a separable curve `T`,
CRT indicators `es` each idempotent (`hidem`), per-component integrals `Fs` with
`eᵢ·D(Fᵢ) = eᵢ·integrand` (`hcomp`), and partition of unity `Σ eᵢ = 1` (`hsum`), the recombined
integral `afIntegrateFunctionAlgebra T es Fs` satisfies
`mk(toPoly(afDerivWf T F)) = mk(toPoly integrand)` in `Q = K[X] ⧸ afIdeal T`. -/
theorem afIntegrateFunctionAlgebra_sound (f integrand : DensePoly α)
    (es Fs : List (DensePoly α)) (hf : cnorm f ≠ [])
    (hgdeg : (toPoly (CPolyEuclidean.gcdExt (cderiv f) f).1).natDegree = 0)
    (hgne : toPoly (CPolyEuclidean.gcdExt (cderiv f) f).1 ≠ 0)
    (hidem : ∀ p ∈ es.zip Fs, IsAfIdempotent f p.1)
    (hcomp : ∀ p ∈ es.zip Fs,
      Ideal.Quotient.mk (afIdeal f) (toPoly p.1)
          * Ideal.Quotient.mk (afIdeal f) (toPoly (afDerivWf f p.2))
        = Ideal.Quotient.mk (afIdeal f) (toPoly p.1)
          * Ideal.Quotient.mk (afIdeal f) (toPoly integrand))
    (hsum : ((es.zip Fs).map (fun p => Ideal.Quotient.mk (afIdeal f) (toPoly p.1))).sum = 1) :
    Ideal.Quotient.mk (afIdeal f) (toPoly (afDerivWf f (CPoly.afIntegrateFunctionAlgebra f es Fs)))
      = Ideal.Quotient.mk (afIdeal f) (toPoly integrand) := by
  rw [CPoly.afIntegrateFunctionAlgebra]
  change Ideal.Quotient.mk (afIdeal f)
      (toPoly (afDerivWf f
        (((es.zip Fs).map (fun p => CPoly.mulMod f p.1 p.2)).foldl cadd ([] : DensePoly α))))
    = Ideal.Quotient.mk (afIdeal f) (toPoly integrand)
  rw [mk_toPolyG_afDerivWf_foldlCaddG f hf]
  -- `afDerivWf` of the empty seed is `0` in the quotient
  rw [mk_toPolyG_afDerivWf_nil f hf, zero_add]
  -- fuse the `map ∘ map` over `es.zip Fs`
  rw [List.map_map]
  -- each term `mk(toPoly(afDerivWf (CPoly.mulMod eᵢ Fᵢ))) = ēᵢ·integrand`  (Leibniz + `D eᵢ = 0` + `hcomp`)
  rw [List.map_congr_left (g := fun p =>
        Ideal.Quotient.mk (afIdeal f) (toPoly p.1)
          * Ideal.Quotient.mk (afIdeal f) (toPoly integrand)) (fun p hp => by
    simp only [Function.comp_apply]
    rw [mk_toPoly_afDerivWf_mulMod f p.1 p.2 hf hgdeg hgne,
      mk_toPoly_mulMod _ _ _ hf, mk_toPoly_mulMod _ _ _ hf,
      (hidem p hp).isConstant hf hgdeg hgne, zero_mul, zero_add]
    exact hcomp p hp)]
  -- `Σ ēᵢ·integrand = (Σ ēᵢ)·integrand = 1·integrand = integrand`
  rw [show (fun p : DensePoly α × DensePoly α =>
        Ideal.Quotient.mk (afIdeal f) (toPoly p.1)
          * Ideal.Quotient.mk (afIdeal f) (toPoly integrand))
      = (fun p : DensePoly α × DensePoly α =>
        (fun p : DensePoly α × DensePoly α => Ideal.Quotient.mk (afIdeal f) (toPoly p.1)) p
          * Ideal.Quotient.mk (afIdeal f) (toPoly integrand)) from rfl,
    List.sum_map_mul_right, hsum, one_mul]

end DensePoly

end DeepWiki.SymbolicIntegration
