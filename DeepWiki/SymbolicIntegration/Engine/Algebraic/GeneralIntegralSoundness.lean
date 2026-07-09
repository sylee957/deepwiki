import DeepWiki.SymbolicIntegration.Engine.Algebraic.GeneralWellFounded

/-! # General rational integral soundness

Rational-part soundness API for the general carrier `K(x)[y]/(f)` through `afDerivWf`: the generator
identity `D(y) = y'`, the accumulator telescoping invariant, and the round-trip closure from the engine's
`cisZeroG` certificate. Statements live in the quotient `K[X] ⧸ (toPolyG f) = afIdeal f`, read through
`toPolyG` and `Ideal.Quotient.mk`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open scoped Differential

namespace CPolyG

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]

/-! ### The rational-integral API

The rational-part predicate, generator identity, telescoping, and round-trip closure over `afDerivWf`. -/

/-- General rational-integral soundness predicate: `D(v) = g` modulo the curve ideal `afIdeal f`. -/
def IsGeneralRationalIntegralWf (f g v : CPolyG α) : Prop :=
  Ideal.Quotient.mk (afIdeal f) (toPolyG (afDerivWf f v))
    = Ideal.Quotient.mk (afIdeal f) (toPolyG g)

/-- The generator identity `D(y) = y'` in the quotient. -/
theorem mk_toPolyG_afDerivWf_genGen (f : CPolyG α) (hf : cnormG f ≠ []) :
    Ideal.Quotient.mk (afIdeal f) (toPolyG (afDerivWf f (afBasisElem 1)))
      = Ideal.Quotient.mk (afIdeal f) (toPolyG (afYprimeWf f)) := by
  rw [mk_toPolyG_afDerivWf f _ hf, toPolyG_afBasisElem_one, Differential.implicitDeriv_X]

/-- The generator identity packaged as `IsGeneralRationalIntegralWf`. -/
theorem isGeneralRationalIntegralWf_gen (f : CPolyG α) (hf : cnormG f ≠ []) :
    IsGeneralRationalIntegralWf f (afYprimeWf f) (afBasisElem 1) :=
  mk_toPolyG_afDerivWf_genGen f hf

omit [CDiffFieldSpec α] in
/-- `afDerivWf` kills the seed `[]` modulo the curve ideal. -/
theorem mk_toPolyG_afDerivWf_nil (f : CPolyG α) (hf : cnormG f ≠ []) :
    Ideal.Quotient.mk (afIdeal f) (toPolyG (afDerivWf f ([] : CPolyG α))) = 0 := by
  rw [show afDerivWf f ([] : CPolyG α) = afReduce f ([] : CPolyG α) from rfl,
    mk_toPolyG_afReduce f _ hf, toPolyG_nil, map_zero]

/-- `afDerivWf` distributes over the accumulator fold in the quotient. -/
theorem mk_toPolyG_afDerivWf_foldlCaddG (f : CPolyG α) (hf : cnormG f ≠ [])
    (acc : CPolyG α) (cs : List (CPolyG α)) :
    Ideal.Quotient.mk (afIdeal f) (toPolyG (afDerivWf f (cs.foldl caddG acc)))
      = Ideal.Quotient.mk (afIdeal f) (toPolyG (afDerivWf f acc))
        + (cs.map (fun c => Ideal.Quotient.mk (afIdeal f) (toPolyG (afDerivWf f c)))).sum := by
  induction cs generalizing acc with
  | nil => simp
  | cons c cs ih =>
    rw [List.foldl_cons, ih (caddG acc c), mk_toPolyG_afDerivWf_add f acc c hf, List.map_cons,
      List.sum_cons]
    ring

omit [CDiffFieldSpec α] in
/-- The per-step contributions telescope in the quotient. -/
theorem sum_mk_toPolyG_afDerivWf_telescope (f : CPolyG α) :
    ∀ (L₀ : CPolyG α) (rest : List (CPolyG α)) (cs : List (CPolyG α)),
      List.Forall₂ (fun c p => Ideal.Quotient.mk (afIdeal f) (toPolyG (afDerivWf f c))
            = Ideal.Quotient.mk (afIdeal f) (toPolyG p.1)
              - Ideal.Quotient.mk (afIdeal f) (toPolyG p.2))
          cs ((L₀ :: rest).zip rest) →
      (cs.map (fun c => Ideal.Quotient.mk (afIdeal f) (toPolyG (afDerivWf f c)))).sum
        = Ideal.Quotient.mk (afIdeal f) (toPolyG L₀)
          - Ideal.Quotient.mk (afIdeal f) (toPolyG (rest.getLastD L₀)) := by
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
theorem generalReduceRationalTelescopeWf (f : CPolyG α) (hf : cnormG f ≠ [])
    (L₀ : CPolyG α) (rest cs : List (CPolyG α))
    (hstep : List.Forall₂ (fun c p => Ideal.Quotient.mk (afIdeal f) (toPolyG (afDerivWf f c))
          = Ideal.Quotient.mk (afIdeal f) (toPolyG p.1)
            - Ideal.Quotient.mk (afIdeal f) (toPolyG p.2))
        cs ((L₀ :: rest).zip rest)) :
    Ideal.Quotient.mk (afIdeal f) (toPolyG (afDerivWf f (cs.foldl caddG ([] : CPolyG α))))
        + Ideal.Quotient.mk (afIdeal f) (toPolyG (rest.getLastD L₀))
      = Ideal.Quotient.mk (afIdeal f) (toPolyG L₀) := by
  rw [mk_toPolyG_afDerivWf_foldlCaddG f hf, mk_toPolyG_afDerivWf_nil f hf, zero_add,
    sum_mk_toPolyG_afDerivWf_telescope f L₀ rest cs hstep]
  ring

/-- The telescoping yields `IsGeneralRationalIntegralWf` when the final leftover vanishes. -/
theorem isGeneralRationalIntegralWf_of_telescope (f : CPolyG α) (hf : cnormG f ≠ [])
    (L₀ : CPolyG α) (rest cs : List (CPolyG α))
    (hstep : List.Forall₂ (fun c p => Ideal.Quotient.mk (afIdeal f) (toPolyG (afDerivWf f c))
          = Ideal.Quotient.mk (afIdeal f) (toPolyG p.1)
            - Ideal.Quotient.mk (afIdeal f) (toPolyG p.2))
        cs ((L₀ :: rest).zip rest))
    (hleft : Ideal.Quotient.mk (afIdeal f) (toPolyG (rest.getLastD L₀)) = 0) :
    IsGeneralRationalIntegralWf f L₀ (cs.foldl caddG ([] : CPolyG α)) := by
  have hkey := generalReduceRationalTelescopeWf f hf L₀ rest cs hstep
  rw [hleft, add_zero] at hkey
  exact hkey

omit [CDiffFieldSpec α] in
/-- The `afDerivWf` round-trip check discharges `IsGeneralRationalIntegralWf`. -/
theorem isGeneralRationalIntegralWf_of_roundtrip (f v g : CPolyG α)
    (hcheck : cisZeroG (csubG (afDerivWf f v) g) = true) :
    IsGeneralRationalIntegralWf f g v :=
  congrArg (Ideal.Quotient.mk (afIdeal f)) (toPolyG_afDerivWf_eq_of_roundtrip f v g hcheck)

end CPolyG

/-! ### The named general driver run on `y³ = x²`

The round-trip theorem turns an engine certificate into rational-part soundness. -/

open CPolyG

/-- The named general run `∫ y dx = (3/5)x·y` on `y³ = x²` is sound through `afDerivWf`. -/
theorem isGeneralRationalIntegralWf_cuspCubic_intY (v : CPolyG (QFunNZG ℚ))
    (hcheck : cisZeroG (csubG (afDerivWf gcuspCubicF v) gcuspCubicY) = true) :
    CPolyG.IsGeneralRationalIntegralWf gcuspCubicF gcuspCubicY v :=
  CPolyG.isGeneralRationalIntegralWf_of_roundtrip gcuspCubicF v gcuspCubicY hcheck

end DeepWiki.SymbolicIntegration
