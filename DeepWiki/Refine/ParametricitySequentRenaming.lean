import DeepWiki.Refine.ParametricitySequents
import DeepWiki.Refine.RawParametricityTyping

/-! # Constructive admissibility for raw parametricity sequents

Domain-coherent sequents admit structural renaming and context enlargement. These operations
support an existence-based admissibility invariant that survives relational context extension. -/

namespace DeepWiki.Refine.DependentCalculus.ParametricitySequents

open RawParametricity

/-- Rename every variable of one parametricity-context triple. -/
def VariableTriple.rename (mapping : Renaming source target)
    (triple : VariableTriple source) : VariableTriple target where
  original := mapping triple.original
  primed := mapping triple.primed
  witness := mapping triple.witness

/-- Rename every variable triple in a parametricity context. -/
def ParametricityContext.rename (mapping : Renaming source target)
    (context : ParametricityContext source) : ParametricityContext target :=
  context.map (VariableTriple.rename mapping)

/-- Lift a renaming beneath an original, primed, and witness binder triple. -/
def liftTripleRenaming (mapping : Renaming source target) :
    Renaming (source + 3) (target + 3) :=
  Fin.cases 0 (Fin.cases 1 (Fin.cases 2
    (fun index => (mapping index).succ.succ.succ)))

/-- Triple lifting fixes the witness binder. -/
@[simp] theorem liftTripleRenaming_zero (mapping : Renaming source target) :
    liftTripleRenaming mapping 0 = 0 := rfl

/-- Triple lifting fixes the primed binder. -/
@[simp] theorem liftTripleRenaming_one (mapping : Renaming source target) :
    liftTripleRenaming mapping 1 = 1 := rfl

/-- Triple lifting fixes the original binder. -/
@[simp] theorem liftTripleRenaming_two (mapping : Renaming source target) :
    liftTripleRenaming mapping 2 = 2 := rfl

/-- Triple lifting maps every older variable beneath the three fixed binders. -/
@[simp] theorem liftTripleRenaming_old (mapping : Renaming source target)
    (index : Fin source) :
    liftTripleRenaming mapping index.succ.succ.succ =
      (mapping index).succ.succ.succ := rfl

/-- Renaming a fresh relational extension renames its old triples and keeps its fresh triple. -/
theorem ParametricityContext.rename_extend (mapping : Renaming source target)
    (context : ParametricityContext source) :
    context.extend.rename (liftTripleRenaming mapping) =
      (context.rename mapping).extend := by
  unfold ParametricityContext.rename ParametricityContext.extend
  simp only [List.map_cons, List.map_map]
  congr 1

/-- Renaming triples renames their flattened variable sequence pointwise. -/
theorem ParametricityContext.variableSequence_rename
    (mapping : Renaming source target) (context : ParametricityContext source) :
    (context.rename mapping).variableSequence = context.variableSequence.map mapping := by
  induction context with
  | nil => rfl
  | cons triple context inductionHypothesis =>
      simp only [ParametricityContext.rename, List.map_cons, variableSequence,
        List.flatMap_cons, List.map_append, VariableTriple.rename]
      rw [show
          (List.map (VariableTriple.rename mapping) context).flatMap
              (fun entry => [entry.original, entry.primed, entry.witness]) =
            (context.flatMap fun entry =>
              [entry.original, entry.primed, entry.witness]).map mapping by
        simpa only [ParametricityContext.rename, variableSequence] using inductionHypothesis]
      rfl

/-- Injective renaming preserves duplicate-freedom of parametricity contexts. -/
theorem ParametricityContext.WellFormed.rename
    {context : ParametricityContext source} (wellFormed : context.WellFormed)
    (mapping : Renaming source target) (injective : Function.Injective mapping) :
    (context.rename mapping).WellFormed := by
  rw [ParametricityContext.WellFormed,
    ParametricityContext.variableSequence_rename]
  exact (List.nodup_map_iff injective).2 wellFormed

/-- Shifting beneath one relational triple is injective. -/
theorem ParametricityContext.shiftThree_injective :
    Function.Injective (ParametricityContext.shiftThree : Renaming n (n + 3)) := by
  intro left right equal
  apply Fin.ext
  have valuesEqual := congrArg Fin.val equal
  simp only [ParametricityContext.shiftThree, Fin.val_succ] at valuesEqual
  omega

/-- Triple lifting is three ordinary binder lifts. -/
theorem liftTripleRenaming_eq_liftBy (mapping : Renaming source target) :
    liftTripleRenaming mapping = RawParametricity.liftBy mapping 3 := by
  funext index
  refine Fin.cases rfl ?_ index
  intro index
  refine Fin.cases rfl ?_ index
  intro index
  refine Fin.cases rfl ?_ index
  intro older
  rfl

/-- Original-binder insertion commutes with renaming beneath a relational triple. -/
theorem rename_originalBinderRenaming (body : Term (source + 1))
    (mapping : Renaming source target) :
    (body.rename originalBinderRenaming).rename (liftTripleRenaming mapping) =
      (body.rename (Renaming.lift mapping)).rename originalBinderRenaming := by
  rw [Term.rename_comp, Term.rename_comp]
  apply Term.rename_congr
  funext index
  refine Fin.cases rfl (fun _ => rfl) index

/-- Primed-binder insertion commutes with renaming beneath a relational triple. -/
theorem rename_primedBinderRenaming (body : Term (source + 1))
    (mapping : Renaming source target) :
    (body.rename primedBinderRenaming).rename (liftTripleRenaming mapping) =
      (body.rename (Renaming.lift mapping)).rename primedBinderRenaming := by
  rw [Term.rename_comp, Term.rename_comp]
  apply Term.rename_congr
  funext index
  refine Fin.cases rfl (fun _ => rfl) index

/-- Related-domain formation is natural under renaming. -/
theorem relatedDomain_rename (relation : Term source)
    (mapping : Renaming source target) :
    (relatedDomain relation).rename (RawParametricity.liftBy mapping 2) =
      relatedDomain (relation.rename mapping) := by
  unfold relatedDomain
  simp only [Term.rename, RawParametricity.weakenBy_rename,
    RawParametricity.liftBy, Renaming.lift_zero]
  rfl

/-- Dependent-product witnesses are natural under renaming. -/
theorem piWitness_rename
    (domain : Term source) (codomain : Term (source + 1))
    (primedDomain : Term source) (primedCodomain : Term (source + 1))
    (domainRelation : Term source) (codomainRelation : Term (source + 3))
    (mapping : Renaming source target) :
    (piWitness domain codomain primedDomain primedCodomain
      domainRelation codomainRelation).rename mapping =
      piWitness (domain.rename mapping) (codomain.rename (Renaming.lift mapping))
        (primedDomain.rename mapping) (primedCodomain.rename (Renaming.lift mapping))
        (domainRelation.rename mapping)
        (codomainRelation.rename (liftTripleRenaming mapping)) := by
  have primedProductNatural :
      (RawParametricity.weakenBy (.pi primedDomain primedCodomain) 1).rename
          (Renaming.lift mapping) =
        RawParametricity.weakenBy
          (.pi (primedDomain.rename mapping)
            (primedCodomain.rename (Renaming.lift mapping))) 1 := by
    rw [show
        .pi (primedDomain.rename mapping)
            (primedCodomain.rename (Renaming.lift mapping)) =
          (Term.pi primedDomain primedCodomain).rename mapping by rfl]
    exact (RawParametricity.weakenBy_rename
      (.pi primedDomain primedCodomain) mapping 1).symm
  unfold piWitness
  simp only [Term.rename, RawParametricity.weakenBy_rename]
  rw [← relatedDomain_rename]
  rw [liftTripleRenaming_eq_liftBy]
  simp only [RawParametricity.liftBy]
  rw [primedProductNatural]
  rw [Term.rename_comp, Term.rename_comp]
  apply congrArg₂ Term.lam rfl
  apply congrArg₂ Term.lam rfl
  apply congrArg₂ Term.pi rfl
  apply congrArg₂ Term.pi rfl
  apply congrArg₂ Term.pi rfl
  congr 3
  simpa only [RawParametricity.liftBy] using
    (RawParametricity.insertTwoAfterThree_natural mapping).symm


end DeepWiki.Refine.DependentCalculus.ParametricitySequents
