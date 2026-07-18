import DeepWiki.Refine.Parametricity.Raw.Typing

/-! # Formation-explicit typing for raw parametricity

This refinement of dependent typing records the codomain formation premise needed by the
raw abstraction induction. Ordinary `CCω` typing embeds into the refined system.
-/

namespace DeepWiki.Refine.DependentCalculus.RawParametricity

mutual

  /-- Context formation with recursively explicit typing-formation premises. -/
  inductive FormationWellFormed : Context n → Prop where
    /-- The empty context is formation-explicit. -/
    | empty : FormationWellFormed .empty
    /-- Extend by a formation-explicit universe-typed declaration. -/
    | extend {context : Context n} {type : Term n} {level : Nat}
        (contextWellFormed : FormationWellFormed context)
        (typeWellTyped : FormationHasType context type (.sort level)) :
        FormationWellFormed (.extend context type)

  /-- Typing with explicit codomain formation. -/
  inductive FormationHasType : Context n → Term n → Term n → Prop where
    /-- Every universe is typed by its immediate successor. -/
    | sort {context : Context n}
        (contextWellFormed : FormationWellFormed context) (level : Nat) :
        FormationHasType context (.sort level) (.sort (level + 1))
    /-- A variable has its dependent context-lookup type. -/
    | var {context : Context n}
        (contextWellFormed : FormationWellFormed context) (index : Fin n) :
        FormationHasType context (.var index) (context.lookup index)
    /-- Dependent application instantiates its codomain. -/
    | app {context : Context n} {function argument domain : Term n}
        {codomain : Term (n + 1)}
        (functionWellTyped :
          FormationHasType context function (.pi domain codomain))
        (argumentWellTyped : FormationHasType context argument domain) :
        FormationHasType context (.app function argument)
          (codomain.instantiate argument)
    /-- Lambda formation records both codomain formation and body typing. -/
    | lam {context : Context n} {domain : Term n} {body codomain : Term (n + 1)}
        {domainLevel codomainLevel : Nat}
        (domainWellTyped : FormationHasType context domain (.sort domainLevel))
        (codomainWellTyped :
          FormationHasType (.extend context domain) codomain (.sort codomainLevel))
        (bodyWellTyped : FormationHasType (.extend context domain) body codomain) :
        FormationHasType context (.lam domain body) (.pi domain codomain)
    /-- A dependent product inhabits the maximum input and output universe. -/
    | pi {context : Context n} {domain : Term n} {codomain : Term (n + 1)}
        {domainLevel codomainLevel : Nat}
        (domainWellTyped : FormationHasType context domain (.sort domainLevel))
        (codomainWellTyped :
          FormationHasType (.extend context domain) codomain (.sort codomainLevel)) :
        FormationHasType context (.pi domain codomain)
          (.sort (max domainLevel codomainLevel))
    /-- Definitional conversion changes a term's explicitly formed target type. -/
    | conversion {context : Context n} {term type type' : Term n} {level : Nat}
        (termWellTyped : FormationHasType context term type)
        (targetWellTyped : FormationHasType context type' (.sort level))
        (equal : Convertible type type') :
        FormationHasType context term type'
    /-- Cumulativity records source subtyping. -/
    | cumulativity {context : Context n} {term type type' : Term n} {level : Nat}
        (termWellTyped : FormationHasType context term type)
        (targetWellTyped : FormationHasType context type' (.sort level))
        (subtype : Cumulative type type') :
        FormationHasType context term type'

end

/-- A context renaming preserving formation-explicit dependent lookup types. -/
structure FormationTypedRenaming (source : Context sourceSize)
    (target : Context targetSize) (mapping : Renaming sourceSize targetSize) : Prop where
  /-- The target context is formation-explicit. -/
  targetWellFormed : FormationWellFormed target
  /-- Every target lookup is the renamed source lookup. -/
  lookup_eq (index : Fin sourceSize) :
    target.lookup (mapping index) = (source.lookup index).rename mapping

namespace FormationTypedRenaming

/-- The identity renaming preserves every formation-explicit context. -/
theorem identity {context : Context n}
    (contextWellFormed : FormationWellFormed context) :
    FormationTypedRenaming context context Renaming.identity where
  targetWellFormed := contextWellFormed
  lookup_eq index := (Term.rename_identity (context.lookup index)).symm

/-- Formation-explicit context renamings compose. -/
theorem comp {first : Context firstSize} {second : Context secondSize}
    {third : Context thirdSize} {inner : Renaming firstSize secondSize}
    {outer : Renaming secondSize thirdSize}
    (outerTyped : FormationTypedRenaming second third outer)
    (innerTyped : FormationTypedRenaming first second inner) :
    FormationTypedRenaming first third (Renaming.comp outer inner) where
  targetWellFormed := outerTyped.targetWellFormed
  lookup_eq index := by
    calc
      third.lookup (Renaming.comp outer inner index) =
          (second.lookup (inner index)).rename outer := by
            simpa only [Renaming.comp] using outerTyped.lookup_eq (inner index)
      _ = ((first.lookup index).rename inner).rename outer := by
            rw [innerTyped.lookup_eq index]
      _ = (first.lookup index).rename (Renaming.comp outer inner) :=
            Term.rename_comp (first.lookup index) inner outer

/-- Extend a formation-explicit renaming beneath matching dependent binders. -/
theorem lift {source : Context sourceSize} {target : Context targetSize}
    {mapping : Renaming sourceSize targetSize} {domain : Term sourceSize} {level : Nat}
    (mappingTyped : FormationTypedRenaming source target mapping)
    (domainWellTyped :
      FormationHasType target (domain.rename mapping) (.sort level)) :
    FormationTypedRenaming (.extend source domain)
      (.extend target (domain.rename mapping)) (Renaming.lift mapping) where
  targetWellFormed := .extend mappingTyped.targetWellFormed domainWellTyped
  lookup_eq index := by
    refine Fin.cases ?_ ?_ index
    · simp only [Renaming.lift_zero, Context.lookup_zero, Term.rename_comp]
      apply Term.rename_congr
      funext older
      rfl
    · intro older
      simp only [Renaming.lift_succ, Context.lookup_succ]
      rw [mappingTyped.lookup_eq older, Term.rename_comp, Term.rename_comp]
      apply Term.rename_congr
      funext index
      rfl

/-- Weakening into a formation-explicit extension preserves context lookup types. -/
theorem shift {context : Context n} {domain : Term n}
    (extendedWellFormed : FormationWellFormed (.extend context domain)) :
    FormationTypedRenaming context (.extend context domain) Renaming.shift where
  targetWellFormed := extendedWellFormed
  lookup_eq _index := rfl

end FormationTypedRenaming

namespace FormationWellFormed

/-- Forgetting explicit formation premises gives ordinary context formation. -/
theorem erase {source : Context n}
    (sourceWellFormed : FormationWellFormed source) : WellFormed source := by
  refine FormationWellFormed.rec
    (motive_1 := fun source _ => WellFormed source)
    (motive_2 := fun source term type _ => HasType source term type)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ sourceWellFormed
  · exact .empty
  · intro _ _ _ _ _ _ sourceInduction typeInduction
    exact .extend sourceInduction typeInduction
  · intro _ _ _ level sourceInduction
    exact .sort sourceInduction level
  · intro _ _ _ index sourceInduction
    exact .var sourceInduction index
  · intro _ _ _ _ _ _ _ _ functionInduction argumentInduction
    exact .app functionInduction argumentInduction
  · intro _ _ _ _ _ _ _ _ _ _ domainInduction _ bodyInduction
    exact .lam domainInduction bodyInduction
  · intro _ _ _ _ _ _ _ _ domainInduction codomainInduction
    exact .pi domainInduction codomainInduction
  · intro _ _ _ _ _ _ _ _ equal termInduction targetInduction
    exact .conversion termInduction targetInduction equal
  · intro _ _ _ _ _ _ _ _ subtype termInduction targetInduction
    exact .cumulativity termInduction targetInduction subtype

end FormationWellFormed

namespace FormationHasType

/-- Forgetting explicit formation premises gives ordinary dependent typing. -/
theorem erase {source : Context n} {term type : Term n}
    (termWellTyped : FormationHasType source term type) : HasType source term type := by
  refine FormationHasType.rec
    (motive_1 := fun source _ => WellFormed source)
    (motive_2 := fun source term type _ => HasType source term type)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ termWellTyped
  · exact .empty
  · intro _ _ _ _ _ _ sourceInduction typeInduction
    exact .extend sourceInduction typeInduction
  · intro _ _ _ level sourceInduction
    exact .sort sourceInduction level
  · intro _ _ _ index sourceInduction
    exact .var sourceInduction index
  · intro _ _ _ _ _ _ _ _ functionInduction argumentInduction
    exact .app functionInduction argumentInduction
  · intro _ _ _ _ _ _ _ _ _ _ domainInduction _ bodyInduction
    exact .lam domainInduction bodyInduction
  · intro _ _ _ _ _ _ _ _ domainInduction codomainInduction
    exact .pi domainInduction codomainInduction
  · intro _ _ _ _ _ _ _ _ equal termInduction targetInduction
    exact .conversion termInduction targetInduction equal
  · intro _ _ _ _ _ _ _ _ subtype termInduction targetInduction
    exact .cumulativity termInduction targetInduction subtype

/-- Every formation-explicit typing derivation carries formation of its context. -/
theorem contextWellFormed {source : Context n} {term type : Term n}
    (termWellTyped : FormationHasType source term type) :
    FormationWellFormed source := by
  refine FormationHasType.rec
    (motive_1 := fun source _ => FormationWellFormed source)
    (motive_2 := fun source _ _ _ => FormationWellFormed source)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ termWellTyped
  · exact .empty
  · intro _ _ _ _ sourceWellFormed typeWellTyped sourceInduction _
    exact .extend sourceInduction typeWellTyped
  · intro _ _ sourceWellFormed _ _
    exact sourceWellFormed
  · intro _ _ sourceWellFormed _ _
    exact sourceWellFormed
  · intro _ _ _ _ _ _ functionWellTyped _ functionInduction _
    exact functionInduction
  · intro _ _ _ _ _ _ _ _ _ _ domainInduction _ _
    exact domainInduction
  · intro _ _ _ _ _ _ domainWellTyped _ domainInduction _
    exact domainInduction
  · intro _ _ _ _ _ _ termWellTyped _ _ termInduction _
    exact termInduction
  · intro _ _ _ _ _ _ termWellTyped _ _ termInduction _
    exact termInduction

/-- Formation-explicit typing is preserved by formation-explicit context renaming. -/
theorem rename {source : Context sourceSize} {term type : Term sourceSize}
    (termWellTyped : FormationHasType source term type) :
    ∀ {targetSize} {target : Context targetSize}
      {mapping : Renaming sourceSize targetSize},
      FormationTypedRenaming source target mapping →
        FormationHasType target (term.rename mapping) (type.rename mapping) := by
  refine FormationHasType.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := fun {n} context term type _ =>
      ∀ {targetSize} {target : Context targetSize} {mapping : Renaming n targetSize},
        FormationTypedRenaming context target mapping →
          FormationHasType target (term.rename mapping) (type.rename mapping))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ termWellTyped
  · trivial
  · intros
    trivial
  · intro _ _ _ level _ _ _ mapping mappingTyped
    exact .sort mappingTyped.targetWellFormed level
  · intro _ _ _ index _ _ _ mapping mappingTyped
    have variableWellTyped :=
      FormationHasType.var mappingTyped.targetWellFormed (mapping index)
    rw [mappingTyped.lookup_eq index] at variableWellTyped
    exact variableWellTyped
  · intro _ _ _ _ _ _ _ _ functionInduction argumentInduction
      _ _ _ mappingTyped
    have applicationWellTyped := FormationHasType.app
      (functionInduction mappingTyped) (argumentInduction mappingTyped)
    simpa only [Term.rename, Term.rename_instantiate] using applicationWellTyped
  · intro _ _ _ _ _ _ _ _ _ _ domainInduction codomainInduction bodyInduction
      _ _ _ mappingTyped
    have renamedDomain := domainInduction mappingTyped
    have lifted := mappingTyped.lift renamedDomain
    exact .lam renamedDomain (codomainInduction lifted) (bodyInduction lifted)
  · intro _ _ _ _ _ _ _ _ domainInduction codomainInduction
      _ _ _ mappingTyped
    have renamedDomain := domainInduction mappingTyped
    exact .pi renamedDomain (codomainInduction (mappingTyped.lift renamedDomain))
  · intro _ _ _ _ _ _ _ _ equal termInduction targetInduction
      _ _ mapping mappingTyped
    exact .conversion (termInduction mappingTyped) (targetInduction mappingTyped)
      (equal.rename mapping)
  · intro _ _ _ _ _ _ _ _ subtype termInduction targetInduction
      _ _ mapping mappingTyped
    exact .cumulativity (termInduction mappingTyped) (targetInduction mappingTyped)
      (subtype.rename mapping)

/-- Weakening a formation-explicit derivation preserves its renamed type. -/
theorem weaken {context : Context n} {term type domain : Term n}
    (termWellTyped : FormationHasType context term type)
    (extendedWellFormed : FormationWellFormed (.extend context domain)) :
    FormationHasType (.extend context domain) (term.rename Renaming.shift)
      (type.rename Renaming.shift) :=
  termWellTyped.rename (FormationTypedRenaming.shift extendedWellFormed)

end FormationHasType

namespace FormationWellFormed

/-- Every lookup in a formation-explicit context is formation-explicitly universe typed. -/
theorem lookup_hasType {context : Context n}
    (contextWellFormed : FormationWellFormed context) (index : Fin n) :
    ∃ level, FormationHasType context (context.lookup index) (.sort level) := by
  refine FormationWellFormed.rec
    (motive_1 := fun {n} context _ =>
      ∀ index : Fin n,
        ∃ level, FormationHasType context (context.lookup index) (.sort level))
    (motive_2 := fun _ _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ contextWellFormed index
  · exact fun index => Fin.elim0 index
  · intro n context domain level contextWellFormed domainWellTyped
      contextInduction _ index
    have extendedWellFormed : FormationWellFormed (.extend context domain) :=
      .extend contextWellFormed domainWellTyped
    refine Fin.cases ?_ ?_ index
    · refine ⟨level, ?_⟩
      simpa only [Context.lookup_zero, Term.rename] using
        domainWellTyped.weaken extendedWellFormed
    · intro older
      obtain ⟨olderLevel, olderWellTyped⟩ := contextInduction older
      refine ⟨olderLevel, ?_⟩
      simpa only [Context.lookup_succ, Term.rename] using
        olderWellTyped.weaken extendedWellFormed
  all_goals intros
  all_goals trivial

end FormationWellFormed

/-- A simultaneous substitution preserving formation-explicit dependent lookup types. -/
structure FormationTypedSubstitution (source : Context sourceSize)
    (target : Context targetSize) (mapping : Substitution sourceSize targetSize) : Prop where
  /-- The substitution target is formation-explicit. -/
  targetWellFormed : FormationWellFormed target
  /-- Every substituted variable has its substituted source lookup type. -/
  variableWellTyped (index : Fin sourceSize) :
    FormationHasType target (mapping index)
      ((source.lookup index).substitute mapping)

namespace FormationTypedSubstitution

/-- The identity substitution preserves every formation-explicit context. -/
theorem identity {context : Context n}
    (contextWellFormed : FormationWellFormed context) :
    FormationTypedSubstitution context context Substitution.identity where
  targetWellFormed := contextWellFormed
  variableWellTyped index := by
    change FormationHasType context (.var index)
      ((context.lookup index).substitute Substitution.identity)
    rw [Term.substitute_identity]
    exact .var contextWellFormed index

/-- Every formation-explicit typed renaming induces a typed substitution. -/
theorem ofRenaming {source : Context sourceSize} {target : Context targetSize}
    {mapping : Renaming sourceSize targetSize}
    (mappingTyped : FormationTypedRenaming source target mapping) :
    FormationTypedSubstitution source target (Substitution.ofRenaming mapping) where
  targetWellFormed := mappingTyped.targetWellFormed
  variableWellTyped index := by
    have variableWellTyped :=
      FormationHasType.var mappingTyped.targetWellFormed (mapping index)
    rw [mappingTyped.lookup_eq index] at variableWellTyped
    simpa only [Substitution.ofRenaming, Term.substitute_ofRenaming] using
      variableWellTyped

/-- Extend a formation-explicit typed substitution beneath matching binders. -/
theorem lift {source : Context sourceSize} {target : Context targetSize}
    {mapping : Substitution sourceSize targetSize} {domain : Term sourceSize}
    {level : Nat} (mappingTyped : FormationTypedSubstitution source target mapping)
    (domainWellTyped :
      FormationHasType target (domain.substitute mapping) (.sort level)) :
    FormationTypedSubstitution (.extend source domain)
      (.extend target (domain.substitute mapping)) (Substitution.lift mapping) where
  targetWellFormed := .extend mappingTyped.targetWellFormed domainWellTyped
  variableWellTyped index := by
    refine Fin.cases ?_ ?_ index
    · have newestWellTyped := FormationHasType.var
        (FormationWellFormed.extend mappingTyped.targetWellFormed domainWellTyped) 0
      simpa only [Substitution.lift_zero, Context.lookup_zero,
        Term.substitute_rename_shift_lift] using newestWellTyped
    · intro older
      have olderWellTyped := (mappingTyped.variableWellTyped older).weaken
        (FormationWellFormed.extend mappingTyped.targetWellFormed domainWellTyped)
      simpa only [Substitution.lift_succ, Context.lookup_succ,
        Term.substitute_rename_shift_lift] using olderWellTyped

/-- A typed argument induces the formation-explicit newest-variable substitution. -/
theorem single {context : Context n} {domain argument : Term n}
    (contextWellFormed : FormationWellFormed context)
    (argumentWellTyped : FormationHasType context argument domain) :
    FormationTypedSubstitution (.extend context domain) context
      (Substitution.single argument) where
  targetWellFormed := contextWellFormed
  variableWellTyped index := by
    refine Fin.cases ?_ ?_ index
    · change FormationHasType context argument
        ((domain.rename Renaming.shift).instantiate argument)
      rw [Term.instantiate_rename_shift]
      exact argumentWellTyped
    · intro older
      change FormationHasType context (.var older)
        (((context.lookup older).rename Renaming.shift).instantiate argument)
      rw [Term.instantiate_rename_shift]
      exact .var contextWellFormed older

end FormationTypedSubstitution

namespace FormationHasType

/-- Typing a product exposes formation-explicit universe typings for both components. -/
theorem piComponents {context : Context n} {domain : Term n}
    {codomain : Term (n + 1)} {type : Term n} :
    FormationHasType context (.pi domain codomain) type →
      ∃ domainLevel codomainLevel,
        FormationHasType context domain (.sort domainLevel) ∧
          FormationHasType (.extend context domain) codomain
            (.sort codomainLevel) := by
  intro productWellTyped
  refine FormationHasType.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := fun context term _ _ =>
      match term with
      | .pi domain codomain =>
          ∃ domainLevel codomainLevel,
            FormationHasType context domain (.sort domainLevel) ∧
              FormationHasType (.extend context domain) codomain
                (.sort codomainLevel)
      | _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ productWellTyped
  all_goals intros
  all_goals aesop

/-- Typed simultaneous substitution preserves formation-explicit typing. -/
theorem substitute {source : Context sourceSize} {term type : Term sourceSize}
    (termWellTyped : FormationHasType source term type) :
    ∀ {targetSize} {target : Context targetSize}
      {mapping : Substitution sourceSize targetSize},
      FormationTypedSubstitution source target mapping →
        FormationHasType target (term.substitute mapping)
          (type.substitute mapping) := by
  refine FormationHasType.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := fun {n} context term type _ =>
      ∀ {targetSize} {target : Context targetSize}
        {mapping : Substitution n targetSize},
        FormationTypedSubstitution context target mapping →
          FormationHasType target (term.substitute mapping)
            (type.substitute mapping))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ termWellTyped
  · trivial
  · intros
    trivial
  · intro _ _ _ level _ _ _ mapping mappingTyped
    exact .sort mappingTyped.targetWellFormed level
  · intro _ _ _ index _ _ _ _ mappingTyped
    exact mappingTyped.variableWellTyped index
  · intro _ _ _ _ _ _ _ _ functionInduction argumentInduction
      _ _ _ mappingTyped
    have applicationWellTyped := FormationHasType.app
      (functionInduction mappingTyped) (argumentInduction mappingTyped)
    simpa only [Term.substitute, Term.substitute_instantiate] using
      applicationWellTyped
  · intro _ _ _ _ _ _ _ _ _ _ domainInduction codomainInduction bodyInduction
      _ _ _ mappingTyped
    have substitutedDomain := domainInduction mappingTyped
    have lifted := mappingTyped.lift substitutedDomain
    exact .lam substitutedDomain (codomainInduction lifted) (bodyInduction lifted)
  · intro _ _ _ _ _ _ _ _ domainInduction codomainInduction
      _ _ _ mappingTyped
    have substitutedDomain := domainInduction mappingTyped
    exact .pi substitutedDomain
      (codomainInduction (mappingTyped.lift substitutedDomain))
  · intro _ _ _ _ _ _ _ _ equal termInduction targetInduction
      _ _ mapping mappingTyped
    exact .conversion (termInduction mappingTyped) (targetInduction mappingTyped)
      (equal.substitute mapping)
  · intro _ _ _ _ _ _ _ _ subtype termInduction targetInduction
      _ _ mapping mappingTyped
    exact .cumulativity (termInduction mappingTyped) (targetInduction mappingTyped)
      (subtype.substitute mapping)

/-- Instantiating a formation-explicit body by a typed argument preserves typing. -/
theorem instantiate {context : Context n} {domain argument : Term n}
    {body type : Term (n + 1)}
    (bodyWellTyped : FormationHasType (.extend context domain) body type)
    (contextWellFormed : FormationWellFormed context)
    (argumentWellTyped : FormationHasType context argument domain) :
    FormationHasType context (body.instantiate argument)
      (type.instantiate argument) :=
  bodyWellTyped.substitute
    (FormationTypedSubstitution.single contextWellFormed argumentWellTyped)

/-- Every formation-explicit assigned type itself inhabits a universe. -/
theorem typeWellTyped {context : Context n} {term type : Term n}
    (termWellTyped : FormationHasType context term type) :
    ∃ level, FormationHasType context type (.sort level) := by
  refine FormationHasType.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := fun context _ type _ =>
      ∃ level, FormationHasType context type (.sort level))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ termWellTyped
  · trivial
  · intros
    trivial
  · intro _ _ contextWellFormed level _
    exact ⟨level + 2, by
      simpa only [Nat.add_assoc] using
        FormationHasType.sort contextWellFormed (level + 1)⟩
  · intro _ _ contextWellFormed index _
    exact contextWellFormed.lookup_hasType index
  · intro _ _ _ _ _ _ _ argumentWellTyped functionInduction _
    obtain ⟨_, functionTypeWellTyped⟩ := functionInduction
    obtain ⟨_, codomainLevel, _, codomainWellTyped⟩ :=
      piComponents functionTypeWellTyped
    exact ⟨codomainLevel,
      codomainWellTyped.instantiate argumentWellTyped.contextWellFormed
        argumentWellTyped⟩
  · intro _ _ _ _ _ domainLevel codomainLevel domainWellTyped
      codomainWellTyped _ _ _ _
    exact ⟨max domainLevel codomainLevel,
      FormationHasType.pi domainWellTyped codomainWellTyped⟩
  · intro _ _ _ _ domainLevel codomainLevel domainWellTyped _ _ _
    exact ⟨max domainLevel codomainLevel + 1,
      FormationHasType.sort domainWellTyped.contextWellFormed
        (max domainLevel codomainLevel)⟩
  · intro _ _ _ _ _ level _ targetWellTyped _ _ _
    exact ⟨level, targetWellTyped⟩
  · intro _ _ _ _ _ level _ targetWellTyped _ _ _
    exact ⟨level, targetWellTyped⟩

/-- Ordinary typing lifts to formation-explicit typing. -/
theorem ofHasType {source : Context n} {term type : Term n}
    (termWellTyped : HasType source term type) :
    FormationHasType source term type := by
  refine HasType.rec
    (motive_1 := fun source _ => FormationWellFormed source)
    (motive_2 := fun source term type _ =>
      FormationHasType source term type)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ termWellTyped
  · exact .empty
  · intro _ _ _ _ _ _ sourceInduction typeInduction
    exact .extend sourceInduction typeInduction
  · intro _ _ _ level sourceInduction
    exact .sort sourceInduction level
  · intro _ _ _ index sourceInduction
    exact .var sourceInduction index
  · intro _ _ _ _ _ _ _ _ functionInduction argumentInduction
    exact .app functionInduction argumentInduction
  · intro _ _ _ _ _ _ _ _ domainInduction bodyInduction
    obtain ⟨_, codomainInduction⟩ := bodyInduction.typeWellTyped
    exact .lam domainInduction codomainInduction bodyInduction
  · intro _ _ _ _ _ _ _ _ domainInduction codomainInduction
    exact .pi domainInduction codomainInduction
  · intro _ _ _ _ _ _ _ _ equal termInduction targetInduction
    exact .conversion termInduction targetInduction equal
  · intro _ _ _ _ _ _ _ _ subtype termInduction targetInduction
    exact .cumulativity termInduction targetInduction subtype

end FormationHasType

end DeepWiki.Refine.DependentCalculus.RawParametricity
