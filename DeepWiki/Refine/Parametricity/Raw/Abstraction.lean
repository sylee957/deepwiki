import DeepWiki.Refine.Parametricity.Raw.Conversion

/-! # Raw abstraction

Raw abstraction is proved first for a formation-explicit refinement of dependent typing.
Ordinary `CCω` cumulativity preserves every substituted relation fiber, so ordinary typing
then embeds into the formation-explicit system and satisfies the abstraction theorem.
-/

namespace DeepWiki.Refine.DependentCalculus.RawParametricity

/-- `IsRelationallyCumulative left right` compares every substituted binary relation fiber. -/
def IsRelationallyCumulative (left right : Term n) : Prop :=
  ∀ {target : Nat} (mapping : Substitution n target) (term : Term target),
    Cumulative (relatedTermType term (left.substitute mapping))
      (relatedTermType term (right.substitute mapping))

namespace IsRelationallyCumulative

/-- Definitional conversion induces relational-fiber cumulativity. -/
theorem of_convertible {left right : Term n} (conversion : Convertible left right) :
    IsRelationallyCumulative left right := fun mapping _ =>
  .conversion (relatedTermType_convertible (conversion.substitute mapping))

/-- Universe-level order induces relational-fiber cumulativity. -/
theorem sort {lower upper : Nat} (levelOrder : lower ≤ upper) :
    IsRelationallyCumulative (.sort lower : Term n) (.sort upper) := fun _ term =>
  relatedTermType_sort_cumulative term levelOrder

/-- Relational-fiber cumulativity is transitive. -/
theorem trans {first second third : Term n}
    (firstSecond : IsRelationallyCumulative first second)
    (secondThird : IsRelationallyCumulative second third) :
    IsRelationallyCumulative first third := fun mapping term =>
  (firstSecond mapping term).trans (secondThird mapping term)

/-- Convertible domains and fiberwise cumulative codomains induce cumulative product fibers. -/
theorem pi {domain domain' : Term n} {codomain codomain' : Term (n + 1)}
    (domainEqual : Convertible domain domain')
    (codomainCumulative : IsRelationallyCumulative codomain codomain') :
    IsRelationallyCumulative (.pi domain codomain) (.pi domain' codomain') :=
  fun mapping term => relatedTermType_pi_cumulative term (domainEqual.substitute mapping)
    (codomainCumulative (Substitution.lift mapping))

/-- Relational cumulativity specializes to the original scope. -/
theorem apply {left right : Term n} (subtype : IsRelationallyCumulative left right)
    (term : Term n) :
    Cumulative (relatedTermType term left) (relatedTermType term right) := by
  simpa only [Term.substitute_identity] using subtype Substitution.identity term

/-- Relational cumulativity is stable under simultaneous substitution. -/
theorem substitute {left right : Term source}
    (subtype : IsRelationallyCumulative left right)
    (mapping : Substitution source target) :
    IsRelationallyCumulative (left.substitute mapping) (right.substitute mapping) := by
  intro final outer term
  simpa only [Term.substitute_comp] using
    subtype (Substitution.comp outer mapping) term

/-- Relational cumulativity is stable under a change of free-variable scope. -/
theorem rename {left right : Term source}
    (subtype : IsRelationallyCumulative left right)
    (mapping : Renaming source target) :
    IsRelationallyCumulative (left.rename mapping) (right.rename mapping) := by
  intro final outer term
  simpa only [Term.substitute_rename] using
    subtype (fun index => outer (mapping index)) term

end IsRelationallyCumulative

/-- Every cumulative conversion acts cumulatively on all substituted raw relation fibers. -/
def HasRelationalCumulativity : Prop :=
  ∀ {n : Nat} {left right : Term n},
    Cumulative left right → IsRelationallyCumulative left right

/-- Every ordinary cumulative conversion preserves all substituted raw relation fibers. -/
theorem isRelationallyCumulative_of_cumulative {left right : Term n}
    (subtype : Cumulative left right) :
    IsRelationallyCumulative left right := by
  induction subtype with
  | conversion equal => exact IsRelationallyCumulative.of_convertible equal
  | sort level => exact IsRelationallyCumulative.sort level
  | pi domainEqual _ codomainInduction =>
      exact IsRelationallyCumulative.pi domainEqual codomainInduction
  | trans _ _ firstInduction secondInduction =>
      exact IsRelationallyCumulative.trans firstInduction secondInduction

/-- Ordinary `CCω` cumulative conversion is relationally cumulative. -/
theorem hasRelationalCumulativity : HasRelationalCumulativity :=
  fun subtype => isRelationallyCumulative_of_cumulative subtype

mutual

  /-- Context formation with recursively explicit raw-abstraction premises. -/
  inductive AbstractionWellFormed : Context n → Prop where
    /-- The empty context is formation-explicit. -/
    | empty : AbstractionWellFormed .empty
    /-- Extend by a formation-explicit universe-typed declaration. -/
    | extend {context : Context n} {type : Term n} {level : Nat}
        (contextWellFormed : AbstractionWellFormed context)
        (typeWellTyped : AbstractionHasType context type (.sort level)) :
        AbstractionWellFormed (.extend context type)

  /-- Typing with explicit codomain formation and relationally admissible cumulativity. -/
  inductive AbstractionHasType : Context n → Term n → Term n → Prop where
    /-- Every universe is typed by its immediate successor. -/
    | sort {context : Context n}
        (contextWellFormed : AbstractionWellFormed context) (level : Nat) :
        AbstractionHasType context (.sort level) (.sort (level + 1))
    /-- A variable has its dependent context-lookup type. -/
    | var {context : Context n}
        (contextWellFormed : AbstractionWellFormed context) (index : Fin n) :
        AbstractionHasType context (.var index) (context.lookup index)
    /-- Dependent application instantiates its codomain. -/
    | app {context : Context n} {function argument domain : Term n}
        {codomain : Term (n + 1)}
        (functionWellTyped :
          AbstractionHasType context function (.pi domain codomain))
        (argumentWellTyped : AbstractionHasType context argument domain) :
        AbstractionHasType context (.app function argument)
          (codomain.instantiate argument)
    /-- Lambda formation records both codomain formation and body typing. -/
    | lam {context : Context n} {domain : Term n} {body codomain : Term (n + 1)}
        {domainLevel codomainLevel : Nat}
        (domainWellTyped : AbstractionHasType context domain (.sort domainLevel))
        (codomainWellTyped :
          AbstractionHasType (.extend context domain) codomain (.sort codomainLevel))
        (bodyWellTyped : AbstractionHasType (.extend context domain) body codomain) :
        AbstractionHasType context (.lam domain body) (.pi domain codomain)
    /-- A dependent product inhabits the maximum input and output universe. -/
    | pi {context : Context n} {domain : Term n} {codomain : Term (n + 1)}
        {domainLevel codomainLevel : Nat}
        (domainWellTyped : AbstractionHasType context domain (.sort domainLevel))
        (codomainWellTyped :
          AbstractionHasType (.extend context domain) codomain (.sort codomainLevel)) :
        AbstractionHasType context (.pi domain codomain)
          (.sort (max domainLevel codomainLevel))
    /-- Definitional conversion changes a term's explicitly formed target type. -/
    | conversion {context : Context n} {term type type' : Term n} {level : Nat}
        (termWellTyped : AbstractionHasType context term type)
        (targetWellTyped : AbstractionHasType context type' (.sort level))
        (equal : Convertible type type') :
        AbstractionHasType context term type'
    /-- Cumulativity records source subtyping and its action on every relation fiber. -/
    | cumulativity {context : Context n} {term type type' : Term n} {level : Nat}
        (termWellTyped : AbstractionHasType context term type)
        (targetWellTyped : AbstractionHasType context type' (.sort level))
        (subtype : Cumulative type type')
        (relationalSubtype : IsRelationallyCumulative type type') :
        AbstractionHasType context term type'

end

/-- A context renaming preserving formation-explicit dependent lookup types. -/
structure AbstractionTypedRenaming (source : Context sourceSize)
    (target : Context targetSize) (mapping : Renaming sourceSize targetSize) : Prop where
  /-- The target context is formation-explicit. -/
  targetWellFormed : AbstractionWellFormed target
  /-- Every target lookup is the renamed source lookup. -/
  lookup_eq (index : Fin sourceSize) :
    target.lookup (mapping index) = (source.lookup index).rename mapping

namespace AbstractionTypedRenaming

/-- The identity renaming preserves every formation-explicit context. -/
theorem identity {context : Context n}
    (contextWellFormed : AbstractionWellFormed context) :
    AbstractionTypedRenaming context context Renaming.identity where
  targetWellFormed := contextWellFormed
  lookup_eq index := (Term.rename_identity (context.lookup index)).symm

/-- Formation-explicit context renamings compose. -/
theorem comp {first : Context firstSize} {second : Context secondSize}
    {third : Context thirdSize} {inner : Renaming firstSize secondSize}
    {outer : Renaming secondSize thirdSize}
    (outerTyped : AbstractionTypedRenaming second third outer)
    (innerTyped : AbstractionTypedRenaming first second inner) :
    AbstractionTypedRenaming first third (Renaming.comp outer inner) where
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
    (mappingTyped : AbstractionTypedRenaming source target mapping)
    (domainWellTyped :
      AbstractionHasType target (domain.rename mapping) (.sort level)) :
    AbstractionTypedRenaming (.extend source domain)
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
    (extendedWellFormed : AbstractionWellFormed (.extend context domain)) :
    AbstractionTypedRenaming context (.extend context domain) Renaming.shift where
  targetWellFormed := extendedWellFormed
  lookup_eq _index := rfl

end AbstractionTypedRenaming

namespace AbstractionWellFormed

/-- Forgetting explicit abstraction premises gives ordinary context formation. -/
theorem erase {source : Context n}
    (sourceWellFormed : AbstractionWellFormed source) : WellFormed source := by
  refine AbstractionWellFormed.rec
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
  · intro _ _ _ _ _ _ _ _ subtype _ termInduction targetInduction
    exact .cumulativity termInduction targetInduction subtype

end AbstractionWellFormed

namespace AbstractionHasType

/-- Forgetting explicit abstraction premises gives ordinary dependent typing. -/
theorem erase {source : Context n} {term type : Term n}
    (termWellTyped : AbstractionHasType source term type) : HasType source term type := by
  refine AbstractionHasType.rec
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
  · intro _ _ _ _ _ _ _ _ subtype _ termInduction targetInduction
    exact .cumulativity termInduction targetInduction subtype

/-- Every formation-explicit typing derivation carries formation of its context. -/
theorem contextWellFormed {source : Context n} {term type : Term n}
    (termWellTyped : AbstractionHasType source term type) :
    AbstractionWellFormed source := by
  refine AbstractionHasType.rec
    (motive_1 := fun source _ => AbstractionWellFormed source)
    (motive_2 := fun source _ _ _ => AbstractionWellFormed source)
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
  · intro _ _ _ _ _ _ termWellTyped _ _ _ termInduction _
    exact termInduction

/-- Formation-explicit typing is preserved by formation-explicit context renaming. -/
theorem rename {source : Context sourceSize} {term type : Term sourceSize}
    (termWellTyped : AbstractionHasType source term type) :
    ∀ {targetSize} {target : Context targetSize}
      {mapping : Renaming sourceSize targetSize},
      AbstractionTypedRenaming source target mapping →
        AbstractionHasType target (term.rename mapping) (type.rename mapping) := by
  refine AbstractionHasType.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := fun {n} context term type _ =>
      ∀ {targetSize} {target : Context targetSize} {mapping : Renaming n targetSize},
        AbstractionTypedRenaming context target mapping →
          AbstractionHasType target (term.rename mapping) (type.rename mapping))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ termWellTyped
  · trivial
  · intros
    trivial
  · intro _ _ _ level _ _ _ mapping mappingTyped
    exact .sort mappingTyped.targetWellFormed level
  · intro _ _ _ index _ _ _ mapping mappingTyped
    have variableWellTyped :=
      AbstractionHasType.var mappingTyped.targetWellFormed (mapping index)
    rw [mappingTyped.lookup_eq index] at variableWellTyped
    exact variableWellTyped
  · intro _ _ _ _ _ _ _ _ functionInduction argumentInduction
      _ _ _ mappingTyped
    have applicationWellTyped := AbstractionHasType.app
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
  · intro _ _ _ _ _ _ _ _ subtype relationalSubtype termInduction targetInduction
      _ _ mapping mappingTyped
    exact .cumulativity (termInduction mappingTyped) (targetInduction mappingTyped)
      (subtype.rename mapping) (relationalSubtype.rename mapping)

/-- Weakening a formation-explicit derivation preserves its renamed type. -/
theorem weaken {context : Context n} {term type domain : Term n}
    (termWellTyped : AbstractionHasType context term type)
    (extendedWellFormed : AbstractionWellFormed (.extend context domain)) :
    AbstractionHasType (.extend context domain) (term.rename Renaming.shift)
      (type.rename Renaming.shift) :=
  termWellTyped.rename (AbstractionTypedRenaming.shift extendedWellFormed)

end AbstractionHasType

namespace AbstractionWellFormed

/-- Every lookup in a formation-explicit context is formation-explicitly universe typed. -/
theorem lookup_hasType {context : Context n}
    (contextWellFormed : AbstractionWellFormed context) (index : Fin n) :
    ∃ level, AbstractionHasType context (context.lookup index) (.sort level) := by
  refine AbstractionWellFormed.rec
    (motive_1 := fun {n} context _ =>
      ∀ index : Fin n,
        ∃ level, AbstractionHasType context (context.lookup index) (.sort level))
    (motive_2 := fun _ _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ contextWellFormed index
  · exact fun index => Fin.elim0 index
  · intro n context domain level contextWellFormed domainWellTyped
      contextInduction _ index
    have extendedWellFormed : AbstractionWellFormed (.extend context domain) :=
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

end AbstractionWellFormed

/-- A simultaneous substitution preserving formation-explicit dependent lookup types. -/
structure AbstractionTypedSubstitution (source : Context sourceSize)
    (target : Context targetSize) (mapping : Substitution sourceSize targetSize) : Prop where
  /-- The substitution target is formation-explicit. -/
  targetWellFormed : AbstractionWellFormed target
  /-- Every substituted variable has its substituted source lookup type. -/
  variableWellTyped (index : Fin sourceSize) :
    AbstractionHasType target (mapping index)
      ((source.lookup index).substitute mapping)

namespace AbstractionTypedSubstitution

/-- The identity substitution preserves every formation-explicit context. -/
theorem identity {context : Context n}
    (contextWellFormed : AbstractionWellFormed context) :
    AbstractionTypedSubstitution context context Substitution.identity where
  targetWellFormed := contextWellFormed
  variableWellTyped index := by
    change AbstractionHasType context (.var index)
      ((context.lookup index).substitute Substitution.identity)
    rw [Term.substitute_identity]
    exact .var contextWellFormed index

/-- Every formation-explicit typed renaming induces a typed substitution. -/
theorem ofRenaming {source : Context sourceSize} {target : Context targetSize}
    {mapping : Renaming sourceSize targetSize}
    (mappingTyped : AbstractionTypedRenaming source target mapping) :
    AbstractionTypedSubstitution source target (Substitution.ofRenaming mapping) where
  targetWellFormed := mappingTyped.targetWellFormed
  variableWellTyped index := by
    have variableWellTyped :=
      AbstractionHasType.var mappingTyped.targetWellFormed (mapping index)
    rw [mappingTyped.lookup_eq index] at variableWellTyped
    simpa only [Substitution.ofRenaming, Term.substitute_ofRenaming] using
      variableWellTyped

/-- Extend a formation-explicit typed substitution beneath matching binders. -/
theorem lift {source : Context sourceSize} {target : Context targetSize}
    {mapping : Substitution sourceSize targetSize} {domain : Term sourceSize}
    {level : Nat} (mappingTyped : AbstractionTypedSubstitution source target mapping)
    (domainWellTyped :
      AbstractionHasType target (domain.substitute mapping) (.sort level)) :
    AbstractionTypedSubstitution (.extend source domain)
      (.extend target (domain.substitute mapping)) (Substitution.lift mapping) where
  targetWellFormed := .extend mappingTyped.targetWellFormed domainWellTyped
  variableWellTyped index := by
    refine Fin.cases ?_ ?_ index
    · have newestWellTyped := AbstractionHasType.var
        (AbstractionWellFormed.extend mappingTyped.targetWellFormed domainWellTyped) 0
      simpa only [Substitution.lift_zero, Context.lookup_zero,
        Term.substitute_rename_shift_lift] using newestWellTyped
    · intro older
      have olderWellTyped := (mappingTyped.variableWellTyped older).weaken
        (AbstractionWellFormed.extend mappingTyped.targetWellFormed domainWellTyped)
      simpa only [Substitution.lift_succ, Context.lookup_succ,
        Term.substitute_rename_shift_lift] using olderWellTyped

/-- A typed argument induces the formation-explicit newest-variable substitution. -/
theorem single {context : Context n} {domain argument : Term n}
    (contextWellFormed : AbstractionWellFormed context)
    (argumentWellTyped : AbstractionHasType context argument domain) :
    AbstractionTypedSubstitution (.extend context domain) context
      (Substitution.single argument) where
  targetWellFormed := contextWellFormed
  variableWellTyped index := by
    refine Fin.cases ?_ ?_ index
    · change AbstractionHasType context argument
        ((domain.rename Renaming.shift).instantiate argument)
      rw [Term.instantiate_rename_shift]
      exact argumentWellTyped
    · intro older
      change AbstractionHasType context (.var older)
        (((context.lookup older).rename Renaming.shift).instantiate argument)
      rw [Term.instantiate_rename_shift]
      exact .var contextWellFormed older

end AbstractionTypedSubstitution

namespace AbstractionHasType

/-- Typing a product exposes formation-explicit universe typings for both components. -/
theorem piComponents {context : Context n} {domain : Term n}
    {codomain : Term (n + 1)} {type : Term n} :
    AbstractionHasType context (.pi domain codomain) type →
      ∃ domainLevel codomainLevel,
        AbstractionHasType context domain (.sort domainLevel) ∧
          AbstractionHasType (.extend context domain) codomain
            (.sort codomainLevel) := by
  intro productWellTyped
  refine AbstractionHasType.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := fun context term _ _ =>
      match term with
      | .pi domain codomain =>
          ∃ domainLevel codomainLevel,
            AbstractionHasType context domain (.sort domainLevel) ∧
              AbstractionHasType (.extend context domain) codomain
                (.sort codomainLevel)
      | _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ productWellTyped
  all_goals intros
  all_goals aesop

/-- Typed simultaneous substitution preserves formation-explicit typing. -/
theorem substitute {source : Context sourceSize} {term type : Term sourceSize}
    (termWellTyped : AbstractionHasType source term type) :
    ∀ {targetSize} {target : Context targetSize}
      {mapping : Substitution sourceSize targetSize},
      AbstractionTypedSubstitution source target mapping →
        AbstractionHasType target (term.substitute mapping)
          (type.substitute mapping) := by
  refine AbstractionHasType.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := fun {n} context term type _ =>
      ∀ {targetSize} {target : Context targetSize}
        {mapping : Substitution n targetSize},
        AbstractionTypedSubstitution context target mapping →
          AbstractionHasType target (term.substitute mapping)
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
    have applicationWellTyped := AbstractionHasType.app
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
  · intro _ _ _ _ _ _ _ _ subtype relationalSubtype termInduction targetInduction
      _ _ mapping mappingTyped
    exact .cumulativity (termInduction mappingTyped) (targetInduction mappingTyped)
      (subtype.substitute mapping) (relationalSubtype.substitute mapping)

/-- Instantiating a formation-explicit body by a typed argument preserves typing. -/
theorem instantiate {context : Context n} {domain argument : Term n}
    {body type : Term (n + 1)}
    (bodyWellTyped : AbstractionHasType (.extend context domain) body type)
    (contextWellFormed : AbstractionWellFormed context)
    (argumentWellTyped : AbstractionHasType context argument domain) :
    AbstractionHasType context (body.instantiate argument)
      (type.instantiate argument) :=
  bodyWellTyped.substitute
    (AbstractionTypedSubstitution.single contextWellFormed argumentWellTyped)

/-- Every formation-explicit assigned type itself inhabits a universe. -/
theorem typeWellTyped {context : Context n} {term type : Term n}
    (termWellTyped : AbstractionHasType context term type) :
    ∃ level, AbstractionHasType context type (.sort level) := by
  refine AbstractionHasType.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := fun context _ type _ =>
      ∃ level, AbstractionHasType context type (.sort level))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ termWellTyped
  · trivial
  · intros
    trivial
  · intro _ _ contextWellFormed level _
    exact ⟨level + 2, by
      simpa only [Nat.add_assoc] using
        AbstractionHasType.sort contextWellFormed (level + 1)⟩
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
      AbstractionHasType.pi domainWellTyped codomainWellTyped⟩
  · intro _ _ _ _ domainLevel codomainLevel domainWellTyped _ _ _
    exact ⟨max domainLevel codomainLevel + 1,
      AbstractionHasType.sort domainWellTyped.contextWellFormed
        (max domainLevel codomainLevel)⟩
  · intro _ _ _ _ _ level _ targetWellTyped _ _ _
    exact ⟨level, targetWellTyped⟩
  · intro _ _ _ _ _ level _ targetWellTyped _ _ _ _
    exact ⟨level, targetWellTyped⟩

/-- Ordinary typing lifts to formation-explicit typing. -/
theorem ofHasType {source : Context n} {term type : Term n}
    (termWellTyped : HasType source term type) :
    AbstractionHasType source term type := by
  refine HasType.rec
    (motive_1 := fun source _ => AbstractionWellFormed source)
    (motive_2 := fun source term type _ =>
      AbstractionHasType source term type)
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
      (isRelationallyCumulative_of_cumulative subtype)

/-- Formation-explicit typing yields translated-context formation and witness typing together. -/
theorem structural {source : Context n} {term type : Term n}
    (termWellTyped : AbstractionHasType source term type) :
    WellFormed (context source) ∧
      HasType (context source) (translate term) (relatedTermType term type) := by
  refine AbstractionHasType.rec
    (motive_1 := fun source _ => WellFormed (context source))
    (motive_2 := fun source term type _ =>
      WellFormed (context source) ∧
        HasType (context source) (translate term) (relatedTermType term type))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ termWellTyped
  · exact context_empty_wellFormed
  · intro _ _ _ _ _ typeWellTyped sourceInduction typeInduction
    exact context_extend_wellFormed sourceInduction typeWellTyped.erase typeInduction.2
  · intro _ _ _ level sourceInduction
    exact ⟨sourceInduction, translate_sort_witness_hasType sourceInduction level⟩
  · intro _ _ _ index sourceInduction
    exact ⟨sourceInduction, translate_var_witness_hasType sourceInduction index⟩
  · intro _ _ _ _ _ _ functionWellTyped argumentWellTyped
      functionInduction argumentInduction
    exact ⟨functionInduction.1,
      translate_app_witness_hasType functionInduction.1
        functionWellTyped.erase argumentWellTyped.erase
        functionInduction.2 argumentInduction.2⟩
  · intro _ source domain body codomain domainLevel codomainLevel
      domainWellTyped codomainWellTyped bodyWellTyped
      domainInduction codomainInduction bodyInduction
    have productWellTyped :
        HasType source (.pi domain codomain)
          (.sort (max domainLevel codomainLevel)) :=
      .pi domainWellTyped.erase codomainWellTyped.erase
    have productWitness := translate_pi_witness_hasType
      domainInduction.1 domainWellTyped.erase codomainWellTyped.erase
      domainInduction.2 codomainInduction.2
    exact ⟨domainInduction.1,
      translate_lam_witness_hasType_of_productWitness
        domainInduction.1 domainWellTyped.erase bodyWellTyped.erase
        productWellTyped productWitness bodyInduction.2⟩
  · intro _ _ _ _ _ _ domainWellTyped codomainWellTyped
      domainInduction codomainInduction
    exact ⟨domainInduction.1,
      translate_pi_witness_hasType domainInduction.1
        domainWellTyped.erase codomainWellTyped.erase
        domainInduction.2 codomainInduction.2⟩
  · intro _ _ _ _ _ _ termWellTyped targetWellTyped equal
      termInduction targetInduction
    exact ⟨termInduction.1,
      translate_conversion_witness_hasType termInduction.1
        termWellTyped.erase targetWellTyped.erase equal
        termInduction.2 targetInduction.2⟩
  · intro _ source term _ type' _ termWellTyped targetWellTyped
      subtype relationalSubtype termInduction targetInduction
    have raisedTerm : HasType source term type' :=
      .cumulativity termWellTyped.erase targetWellTyped.erase subtype
    exact ⟨termInduction.1,
      .cumulativity termInduction.2
        (relatedTermType_hasType_of_typeWitness termInduction.1 raisedTerm
          targetWellTyped.erase targetInduction.2)
        (relationalSubtype.apply term)⟩

/-- Every formation-explicit typing derivation satisfies raw witness abstraction. -/
theorem witness {source : Context n} {term type : Term n}
    (termWellTyped : AbstractionHasType source term type) :
    HasType (context source) (translate term) (relatedTermType term type) :=
  termWellTyped.structural.2

/-- Every formation-explicit typing derivation forms its translated context. -/
theorem translatedContextWellFormed {source : Context n} {term type : Term n}
    (termWellTyped : AbstractionHasType source term type) :
    WellFormed (context source) :=
  termWellTyped.structural.1

end AbstractionHasType


/-- Formation-explicit typing proves all three displayed raw abstraction conclusions. -/
theorem abstractionConclusion_of_abstractionHasType {source : Context n}
    {term type : Term n} (termWellTyped : AbstractionHasType source term type) :
    AbstractionConclusion source term type := by
  have translatedWellFormed :=
    termWellTyped.translatedContextWellFormed
  exact ⟨HasType.original termWellTyped.erase translatedWellFormed,
    HasType.primed termWellTyped.erase translatedWellFormed,
    termWellTyped.witness⟩

/-- The displayed abstraction claim restricted to formation-explicit typing derivations. -/
def FormationExplicitRawAbstractionClaim : Prop :=
  ∀ {n : Nat} {source : Context n} {term type : Term n},
    AbstractionHasType source term type → AbstractionConclusion source term type

/-- Formation-explicit dependent typing satisfies the displayed raw abstraction theorem. -/
theorem formationExplicitRawAbstraction : FormationExplicitRawAbstractionClaim :=
  fun termWellTyped => abstractionConclusion_of_abstractionHasType termWellTyped

/-- Ordinary `CCω` typing satisfies raw abstraction. -/
theorem rawAbstraction : RawAbstractionClaim := fun termWellTyped => by
  have abstractionTyping :=
    AbstractionHasType.ofHasType termWellTyped
  exact ⟨abstractionTyping.translatedContextWellFormed,
    abstractionConclusion_of_abstractionHasType abstractionTyping⟩

/-- Ordinary `CCω` typing satisfies the displayed raw abstraction theorem. -/
theorem displayedRawAbstraction : DisplayedRawAbstractionClaim :=
  fun termWellTyped => (rawAbstraction termWellTyped).2

example :
    AbstractionHasType Context.empty (.sort 0 : Term 0) (.sort 2) :=
  .cumulativity (.sort .empty 0) (.sort .empty 2)
    (.sort (by omega)) (IsRelationallyCumulative.sort (by omega))

example {source : Context n} {term type : Term n}
    (termWellTyped : AbstractionHasType source term type) :
    AbstractionConclusion source term type :=
  formationExplicitRawAbstraction termWellTyped

example : HasRelationalCumulativity :=
  hasRelationalCumulativity

example : RawAbstractionClaim :=
  rawAbstraction

example : DisplayedRawAbstractionClaim :=
  displayedRawAbstraction

end DeepWiki.Refine.DependentCalculus.RawParametricity
