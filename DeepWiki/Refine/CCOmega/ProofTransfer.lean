import DeepWiki.Refine.CCOmega.SurfaceSyntax

/-! # Type-former proof transfer in CCω

A proof-transfer problem supplies source and target carriers, source and target type formers, and
relations on inputs and outputs. The displayed witness type internalizes the requirement that related
inputs are mapped to related output types. -/

namespace DeepWiki.Refine.DependentCalculus.TypeFormerTransfer

/-! The declarations in `problemContext` represent

* source and target carriers `S` and `T`;
* source and target type formers `V` and `W`;
* an input relation `RInput` between `S` and `T`;
* an output relation `ROutput` between the types produced by `V` and `W`.
-/

/-- The object-language parameters of a small-universe type-former transfer problem. -/
def problemContext : Context 6 :=
  ccωctx!{ ⟨⟩,
    S : □[0],
    T : □[0],
    V : S → □[0],
    W : T → □[0],
    RInput : S → T → □[0],
    ROutput : □[0] → □[0] → □[0] }

/-- The uniform relational witness required of a type-former transfer solution. -/
def witnessType : Term 6 :=
  ccωterm!{ ⟨⟩,
    S : □[0],
    T : □[0],
    V : S → □[0],
    W : T → □[0],
    RInput : S → T → □[0],
    ROutput : □[0] → □[0] → □[0]
    ⊢ Π s : S, Π t : T, RInput s t → ROutput (V s) (W t) }

/-- The right-to-left arrow regarded as an object-language relation between small types. -/
def backwardOutputRelation : Term 0 :=
  ccω!{ λ A : □[0], λ B : □[0], B → A }

/-- The right-to-left output relation maps two small types to a small type. -/
theorem backwardOutputRelation_hasType :
    ccω!{ ⟨⟩ ⊢
      λ A : □[0], λ B : □[0], B → A :
      □[0] → □[0] → □[0] } := by
  let emptyWellFormed : WellFormed (.empty : Context 0) := .empty
  let sourceTypeWellTyped := HasType.sort emptyWellFormed 0
  let sourceContextWellFormed :=
    WellFormed.extend emptyWellFormed sourceTypeWellTyped
  let targetTypeWellTyped := HasType.sort sourceContextWellFormed 0
  let targetContextWellFormed :=
    WellFormed.extend sourceContextWellFormed targetTypeWellTyped
  let targetProofTypeWellTyped :=
    HasType.var targetContextWellFormed (0 : Fin 2)
  let targetProofContextWellFormed :=
    WellFormed.extend targetContextWellFormed targetProofTypeWellTyped
  let sourceProofTypeWellTyped :=
    HasType.var targetProofContextWellFormed (2 : Fin 3)
  let backwardArrowWellTyped :=
    HasType.pi targetProofTypeWellTyped sourceProofTypeWellTyped
  let targetLambdaWellTyped :=
    HasType.lam targetTypeWellTyped backwardArrowWellTyped
  exact HasType.lam sourceTypeWellTyped targetLambdaWellTyped

/-- The parameters of a type-former transfer problem form a valid dependent context. -/
theorem problemContextWellFormed : WellFormed problemContext := by
  let emptyWellFormed : WellFormed (.empty : Context 0) := .empty
  let sourceTypeWellTyped := HasType.sort emptyWellFormed 0
  let sourceContextWellFormed := WellFormed.extend emptyWellFormed sourceTypeWellTyped
  let targetTypeWellTyped := HasType.sort sourceContextWellFormed 0
  let carrierContextWellFormed :=
    WellFormed.extend sourceContextWellFormed targetTypeWellTyped

  let sourceCarrierWellTyped :=
    HasType.var carrierContextWellFormed (1 : Fin 2)
  let sourceBinderWellFormed :=
    WellFormed.extend carrierContextWellFormed sourceCarrierWellTyped
  let sourceCodomainWellTyped := HasType.sort sourceBinderWellFormed 0
  let sourceFormerTypeWellTyped :=
    HasType.pi sourceCarrierWellTyped sourceCodomainWellTyped
  let sourceFormerContextWellFormed :=
    WellFormed.extend carrierContextWellFormed sourceFormerTypeWellTyped

  let targetCarrierWellTyped :=
    HasType.var sourceFormerContextWellFormed (1 : Fin 3)
  let targetBinderWellFormed :=
    WellFormed.extend sourceFormerContextWellFormed targetCarrierWellTyped
  let targetCodomainWellTyped := HasType.sort targetBinderWellFormed 0
  let targetFormerTypeWellTyped :=
    HasType.pi targetCarrierWellTyped targetCodomainWellTyped
  let formerContextWellFormed :=
    WellFormed.extend sourceFormerContextWellFormed targetFormerTypeWellTyped

  let inputSourceWellTyped :=
    HasType.var formerContextWellFormed (3 : Fin 4)
  let inputSourceContextWellFormed :=
    WellFormed.extend formerContextWellFormed inputSourceWellTyped
  let inputTargetWellTyped :=
    HasType.var inputSourceContextWellFormed (3 : Fin 5)
  let inputTargetContextWellFormed :=
    WellFormed.extend inputSourceContextWellFormed inputTargetWellTyped
  let inputCodomainWellTyped := HasType.sort inputTargetContextWellFormed 0
  let inputTargetFormerWellTyped :=
    HasType.pi inputTargetWellTyped inputCodomainWellTyped
  let inputRelationTypeWellTyped :=
    HasType.pi inputSourceWellTyped inputTargetFormerWellTyped
  let inputRelationContextWellFormed :=
    WellFormed.extend formerContextWellFormed inputRelationTypeWellTyped

  let outputSourceWellTyped := HasType.sort inputRelationContextWellFormed 0
  let outputSourceContextWellFormed :=
    WellFormed.extend inputRelationContextWellFormed outputSourceWellTyped
  let outputTargetWellTyped := HasType.sort outputSourceContextWellFormed 0
  let outputTargetContextWellFormed :=
    WellFormed.extend outputSourceContextWellFormed outputTargetWellTyped
  let outputCodomainWellTyped := HasType.sort outputTargetContextWellFormed 0
  let outputTargetFormerWellTyped :=
    HasType.pi outputTargetWellTyped outputCodomainWellTyped
  let outputRelationTypeWellTyped :=
    HasType.pi outputSourceWellTyped outputTargetFormerWellTyped
  exact WellFormed.extend inputRelationContextWellFormed outputRelationTypeWellTyped

/-- The relational transfer witness is a small type in the transfer-problem context. -/
theorem witnessType_hasType : HasType problemContext witnessType (.sort 0) := by
  let sourceWellTyped := HasType.var problemContextWellFormed (5 : Fin 6)
  let sourceContextWellFormed :=
    WellFormed.extend problemContextWellFormed sourceWellTyped
  let targetWellTyped := HasType.var sourceContextWellFormed (5 : Fin 7)
  let targetContextWellFormed :=
    WellFormed.extend sourceContextWellFormed targetWellTyped

  let inputRelationWellTyped :=
    HasType.var targetContextWellFormed (3 : Fin 8)
  let sourceValueWellTyped :=
    HasType.var targetContextWellFormed (1 : Fin 8)
  let targetValueWellTyped :=
    HasType.var targetContextWellFormed (0 : Fin 8)
  let inputAtSourceWellTyped :=
    HasType.app inputRelationWellTyped sourceValueWellTyped
  let relatedTypeWellTyped :=
    HasType.app inputAtSourceWellTyped targetValueWellTyped
  let relatedContextWellFormed :=
    WellFormed.extend targetContextWellFormed relatedTypeWellTyped

  let outputRelationWellTyped :=
    HasType.var relatedContextWellFormed (3 : Fin 9)
  let sourceFormerWellTyped :=
    HasType.var relatedContextWellFormed (6 : Fin 9)
  let weakenedSourceValueWellTyped :=
    HasType.var relatedContextWellFormed (2 : Fin 9)
  let sourceOutputWellTyped :=
    HasType.app sourceFormerWellTyped weakenedSourceValueWellTyped
  let targetFormerWellTyped :=
    HasType.var relatedContextWellFormed (5 : Fin 9)
  let weakenedTargetValueWellTyped :=
    HasType.var relatedContextWellFormed (1 : Fin 9)
  let targetOutputWellTyped :=
    HasType.app targetFormerWellTyped weakenedTargetValueWellTyped
  let outputAtSourceWellTyped :=
    HasType.app outputRelationWellTyped sourceOutputWellTyped
  let outputsRelatedWellTyped :=
    HasType.app outputAtSourceWellTyped targetOutputWellTyped

  let relationImplicationWellTyped :=
    HasType.pi relatedTypeWellTyped outputsRelatedWellTyped
  let targetProductWellTyped :=
    HasType.pi targetWellTyped relationImplicationWellTyped
  exact HasType.pi sourceWellTyped targetProductWellTyped

/-! ## Reading a type-former transfer problem

A type-former transfer problem starts with two input types `S` and `T`. The source type former
`V : S → □[0]` is known, while `W : T → □[0]` is the target type former to be synthesized.
`RInput` says which `s : S` and `t : T` represent one another, and `ROutput` says what it means for
the resulting types `V s` and `W t` to be related.

The transfer witness has type

`Π s : S, Π t : T, RInput s t → ROutput (V s) (W t)`.

It is uniform: the same `w` must work for every related pair of inputs. If `ROutput A B` is chosen
as the backward arrow `B → A`, then `w` turns a proof of the synthesized target goal `W t` into a
proof of the original source goal `V s`.
-/

-- The full transfer-witness formula is itself a well-formed small type.
example :
    ccω!{ ⟨⟩,
      S : □[0],
      T : □[0],
      V : S → □[0],
      W : T → □[0],
      RInput : S → T → □[0],
      ROutput : □[0] → □[0] → □[0]
      ⊢ Π s : S, Π t : T, RInput s t → ROutput (V s) (W t) : □[0] } :=
  witnessType_hasType

-- The common output relation is the backward arrow from target proofs to source proofs.
example :
    (ccω!{ λ A : □[0], λ B : □[0], B → A } : Term 0) =
      backwardOutputRelation :=
  rfl

-- The backward relation has type `□[0] → □[0] → □[0]`.
example :
    ccω!{ ⟨⟩ ⊢
      λ A : □[0], λ B : □[0], B → A :
      □[0] → □[0] → □[0] } :=
  backwardOutputRelation_hasType

-- Using the backward relation as `ROutput` sends source `A` and target `B` to `B → A`.
example :
    ccω!{ ⟨⟩, A : □[0], B : □[0] ⊢
      (λ Source : □[0], λ Target : □[0], Target → Source) A B ≡
        B → A } := by
  apply Convertible.trans
  · exact .beta (.appFunction (.beta _ _ _))
  · exact .beta (.beta _ _ _)

-- The complete witness type then asks for a target proof `W t` before producing `V s`.
example :
    ccω!{ ⟨⟩,
      S : □[0],
      T : □[0],
      V : S → □[0],
      W : T → □[0],
      RInput : S → T → □[0]
      ⊢ Π s : S, Π t : T,
          RInput s t →
            (λ Source : □[0], λ Target : □[0], Target → Source) (V s) (W t) ≡
        Π s : S, Π t : T, RInput s t → W t → V s } := by
  apply Convertible.pi_codomain
  apply Convertible.pi_codomain
  apply Convertible.pi_codomain
  apply Convertible.trans
  · exact .beta (.appFunction (.beta _ _ _))
  · exact .beta (.beta _ _ _)

end DeepWiki.Refine.DependentCalculus.TypeFormerTransfer
