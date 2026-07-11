import DeepWiki.SymbolicIntegration.Engine.Algebraic.GeneralWellFounded

/-! # General rational integral soundness

Rational-part soundness API for the general carrier `K(x)[y]/(f)` through `afDerivWf`: the generator
identity `D(y) = y'`, the accumulator telescoping invariant, and the round-trip closure from the engine's
`cisZero` certificate. Statements live in the quotient `K[X] ⧸ (toPoly f) = afIdeal f`, read through
`toPoly` and `Ideal.Quotient.mk`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open scoped Differential

namespace DensePoly

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]

/-! ### The rational-integral API

The rational-part predicate, generator identity, telescoping, and round-trip closure over `afDerivWf`. -/

/-- General rational-integral soundness predicate: `D(v) = g` modulo the curve ideal `afIdeal f`. -/
def IsGeneralRationalIntegralWf (f g v : DensePoly α) : Prop :=
  Ideal.Quotient.mk (afIdeal f) (toPoly (afDerivWf f v))
    = Ideal.Quotient.mk (afIdeal f) (toPoly g)

/-- The generator identity `D(y) = y'` in the quotient. -/
theorem mk_toPolyG_afDerivWf_genGen (f : DensePoly α) (hf : cnorm f ≠ []) :
    Ideal.Quotient.mk (afIdeal f) (toPoly (afDerivWf f (CPoly.afBasisElem 1)))
      = Ideal.Quotient.mk (afIdeal f) (toPoly (afYprimeWf f)) := by
  have hy : toPoly (CPoly.afBasisElem 1 : DensePoly α) = X := by
    simpa only [toPoly_list_eq] using
      (CPoly.toPoly_afBasisElem_one (P := DensePoly) (α := α))
  rw [mk_toPolyG_afDerivWf f _ hf, hy, Differential.implicitDeriv_X]

/-- The generator identity packaged as `IsGeneralRationalIntegralWf`. -/
theorem isGeneralRationalIntegralWf_gen (f : DensePoly α) (hf : cnorm f ≠ []) :
    IsGeneralRationalIntegralWf f (afYprimeWf f) (CPoly.afBasisElem 1) :=
  mk_toPolyG_afDerivWf_genGen f hf

omit [CDiffFieldSpec α] in
/-- `afDerivWf` kills the seed `[]` modulo the curve ideal. -/
theorem mk_toPolyG_afDerivWf_nil (f : DensePoly α) (hf : cnorm f ≠ []) :
    Ideal.Quotient.mk (afIdeal f) (toPoly (afDerivWf f ([] : DensePoly α))) = 0 := by
  rw [show afDerivWf f ([] : DensePoly α) = CPoly.reduceMod f ([] : DensePoly α) from rfl,
    mk_toPoly_reduceMod f _ hf, toPolyG_nil, map_zero]

/-- `afDerivWf` distributes over the accumulator fold in the quotient. -/
theorem mk_toPolyG_afDerivWf_foldlCaddG (f : DensePoly α) (hf : cnorm f ≠ [])
    (acc : DensePoly α) (cs : List (DensePoly α)) :
    Ideal.Quotient.mk (afIdeal f) (toPoly (afDerivWf f (cs.foldl cadd acc)))
      = Ideal.Quotient.mk (afIdeal f) (toPoly (afDerivWf f acc))
        + (cs.map (fun c => Ideal.Quotient.mk (afIdeal f) (toPoly (afDerivWf f c)))).sum := by
  induction cs generalizing acc with
  | nil => simp
  | cons c cs ih =>
    rw [List.foldl_cons, ih (cadd acc c), mk_toPolyG_afDerivWf_add f acc c hf, List.map_cons,
      List.sum_cons]
    ring

omit [CDiffFieldSpec α] in
/-- The per-step contributions telescope in the quotient. -/
theorem sum_mk_toPolyG_afDerivWf_telescope (f : DensePoly α) :
    ∀ (L₀ : DensePoly α) (rest : List (DensePoly α)) (cs : List (DensePoly α)),
      List.Forall₂ (fun c p => Ideal.Quotient.mk (afIdeal f) (toPoly (afDerivWf f c))
            = Ideal.Quotient.mk (afIdeal f) (toPoly p.1)
              - Ideal.Quotient.mk (afIdeal f) (toPoly p.2))
          cs ((L₀ :: rest).zip rest) →
      (cs.map (fun c => Ideal.Quotient.mk (afIdeal f) (toPoly (afDerivWf f c)))).sum
        = Ideal.Quotient.mk (afIdeal f) (toPoly L₀)
          - Ideal.Quotient.mk (afIdeal f) (toPoly (rest.getLastD L₀)) := by
  intro L₀ rest
  induction rest generalizing L₀ with
  | nil =>
    intro cs hforall
    simp only [List.zip_nil_right] at hforall
    rw [List.forall₂_nil_right_iff] at hforall
    subst hforall
    simp
  | cons L₁ rest' ih =>
    intro cs hforall
    rw [List.zip_cons_cons] at hforall
    rw [List.forall₂_cons_right_iff] at hforall
    obtain ⟨c, cs', h0, htail, rfl⟩ := hforall
    rw [List.map_cons, List.sum_cons, ih L₁ cs' htail, h0]
    rw [List.getLastD_cons]
    ring

/-- The master rational-part telescoping soundness. -/
theorem generalReduceRationalTelescopeWf (f : DensePoly α) (hf : cnorm f ≠ [])
    (L₀ : DensePoly α) (rest cs : List (DensePoly α))
    (hstep : List.Forall₂ (fun c p => Ideal.Quotient.mk (afIdeal f) (toPoly (afDerivWf f c))
          = Ideal.Quotient.mk (afIdeal f) (toPoly p.1)
            - Ideal.Quotient.mk (afIdeal f) (toPoly p.2))
        cs ((L₀ :: rest).zip rest)) :
    Ideal.Quotient.mk (afIdeal f) (toPoly (afDerivWf f (cs.foldl cadd ([] : DensePoly α))))
        + Ideal.Quotient.mk (afIdeal f) (toPoly (rest.getLastD L₀))
      = Ideal.Quotient.mk (afIdeal f) (toPoly L₀) := by
  rw [mk_toPolyG_afDerivWf_foldlCaddG f hf, mk_toPolyG_afDerivWf_nil f hf, zero_add,
    sum_mk_toPolyG_afDerivWf_telescope f L₀ rest cs hstep]
  ring

/-- The telescoping yields `IsGeneralRationalIntegralWf` when the final leftover vanishes. -/
theorem isGeneralRationalIntegralWf_of_telescope (f : DensePoly α) (hf : cnorm f ≠ [])
    (L₀ : DensePoly α) (rest cs : List (DensePoly α))
    (hstep : List.Forall₂ (fun c p => Ideal.Quotient.mk (afIdeal f) (toPoly (afDerivWf f c))
          = Ideal.Quotient.mk (afIdeal f) (toPoly p.1)
            - Ideal.Quotient.mk (afIdeal f) (toPoly p.2))
        cs ((L₀ :: rest).zip rest))
    (hleft : Ideal.Quotient.mk (afIdeal f) (toPoly (rest.getLastD L₀)) = 0) :
    IsGeneralRationalIntegralWf f L₀ (cs.foldl cadd ([] : DensePoly α)) := by
  have hkey := generalReduceRationalTelescopeWf f hf L₀ rest cs hstep
  rw [hleft, add_zero] at hkey
  exact hkey

omit [CDiffFieldSpec α] in
/-- The `afDerivWf` round-trip check discharges `IsGeneralRationalIntegralWf`. -/
theorem isGeneralRationalIntegralWf_of_roundtrip (f v g : DensePoly α)
    (hcheck : cisZero (csub (afDerivWf f v) g) = true) :
    IsGeneralRationalIntegralWf f g v :=
  congrArg (Ideal.Quotient.mk (afIdeal f)) (toPolyG_afDerivWf_eq_of_roundtrip f v g hcheck)

end DensePoly

/-! ### The named general driver run on `y³ = x²`

The round-trip theorem turns an engine certificate into rational-part soundness. -/

open DensePoly

/-- The named general run `∫ y dx = (3/5)x·y` on `y³ = x²` is sound through `afDerivWf`. -/
theorem isGeneralRationalIntegralWf_cuspCubic_intY (v : DensePoly (DenseFrac ℚ))
    (hcheck : cisZero (csub (afDerivWf gcuspCubicF v) gcuspCubicY) = true) :
    DensePoly.IsGeneralRationalIntegralWf gcuspCubicF gcuspCubicY v :=
  DensePoly.isGeneralRationalIntegralWf_of_roundtrip gcuspCubicF v gcuspCubicY hcheck

end DeepWiki.SymbolicIntegration
