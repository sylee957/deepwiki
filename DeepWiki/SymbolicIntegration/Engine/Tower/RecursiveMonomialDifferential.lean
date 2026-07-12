import DeepWiki.SymbolicIntegration.Engine.MonomialDifferentialPostprocess
import DeepWiki.SymbolicIntegration.Engine.Tower.RecursiveElementaryDynamic

/-! # Explicit-differential recursive monomial stages

A recursive monomial case consumes an explicit lower coefficient integrator. The interface keeps
that dependency visible while exporting the ordinary special and normal stage contracts required
by the compositional one-level assembly.
-/

namespace DeepWiki.SymbolicIntegration

universe u v

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P]
variable {α : Type u} [CField α] [CFieldSpec.{u,v} α]
variable {Ctx : MonomialDifferentialContext (P := P) α}

/-- A monomial case parameterized by explicit recursive elementary coefficient integration. -/
structure CDifferentialRecursiveMonomialCase
    (C : MonomialDifferentialContext (P := P) α) where
  /-- Integrate a special branch using the supplied lower coefficient stage. -/
  integrateSpecial : CRecursiveElementaryIntegratorWith α C.derivation →
    ℕ → P α → P α → P α → P α → Option (IntegralResult α P)
  /-- Postprocess a normal/Hermite result for this monomial case. -/
  postprocessNormal : P α → IntegralResult α P → Option (IntegralResult α P)

namespace CDifferentialRecursiveMonomialCase

/-- Fix an explicit recursive coefficient solver to obtain a special-branch operation. -/
@[reducible] def asSpecial (C : CDifferentialRecursiveMonomialCase (P := P) Ctx)
    (I : CRecursiveElementaryIntegratorWith α Ctx.derivation) :
    CDifferentialMonomialSpecial P α Ctx.derivation where
  integrate := C.integrateSpecial I

/-- Forget the coefficient argument to obtain the monomial-specific normal postprocessor. -/
@[reducible] def asPostprocessor (C : CDifferentialRecursiveMonomialCase (P := P) Ctx) :
    CDifferentialNormalPostprocessor P α Ctx.derivation where
  postprocess := C.postprocessNormal

end CDifferentialRecursiveMonomialCase

/-- Soundness of a recursive monomial case is stable under every lawful lower coefficient stage. -/
class LawfulCDifferentialRecursiveMonomialCase
    (C : CDifferentialRecursiveMonomialCase (P := P) Ctx) : Prop where
  /-- Installing a lawful coefficient stage yields a lawful special branch. -/
  specialLawful : ∀ (I : CRecursiveElementaryIntegratorWith α Ctx.derivation),
    LawfulCRecursiveElementaryIntegratorWith Ctx.derivation Ctx.differential I →
      letI : CDifferentialMonomialSpecial P α Ctx.derivation := C.asSpecial I
      LawfulCDifferentialMonomialSpecial Ctx
  /-- Normal postprocessing preserves the certified normal-result invariant. -/
  postprocessorLawful :
    letI : CDifferentialNormalPostprocessor P α Ctx.derivation := C.asPostprocessor
    LawfulCDifferentialNormalPostprocessor Ctx

/-- Relative completeness of a recursive monomial case is stable under complete coefficient stages. -/
class CompleteCDifferentialRecursiveMonomialCase
    (C : CDifferentialRecursiveMonomialCase (P := P) Ctx)
    (coefficientDomain : RecursiveElementaryDomainWith α)
    (specialDomain : MonomialSpecialDomain P α)
    [LawfulCDifferentialRecursiveMonomialCase C] : Prop where
  /-- Installing a complete coefficient stage yields a complete special branch. -/
  specialComplete : ∀ (I : CRecursiveElementaryIntegratorWith α Ctx.derivation),
    ∀ (hLawful : LawfulCRecursiveElementaryIntegratorWith Ctx.derivation Ctx.differential I),
    @CompleteCRecursiveElementaryIntegratorWith α _ _ Ctx.derivation Ctx.differential I
      coefficientDomain hLawful →
      letI : CDifferentialMonomialSpecial P α Ctx.derivation := C.asSpecial I
      letI : LawfulCDifferentialMonomialSpecial Ctx :=
        LawfulCDifferentialRecursiveMonomialCase.specialLawful (C := C) I hLawful
      CompleteCDifferentialMonomialSpecial Ctx specialDomain
  /-- The selected normal postprocessor is relatively complete. -/
  postprocessorComplete :
    letI : CDifferentialNormalPostprocessor P α Ctx.derivation := C.asPostprocessor
    letI : LawfulCDifferentialNormalPostprocessor Ctx :=
      LawfulCDifferentialRecursiveMonomialCase.postprocessorLawful (C := C)
    CompleteCDifferentialNormalPostprocessor Ctx

end DeepWiki.SymbolicIntegration
