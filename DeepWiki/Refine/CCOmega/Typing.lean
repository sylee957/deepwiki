import DeepWiki.Refine.CCOmega.Syntax

/-! # Typing for a predicative dependent calculus

The scoped syntax is equipped with single-variable instantiation, compatible beta reduction,
conversion, cumulative universes, well-formed contexts, and the ordinary dependent typing rules.
De Bruijn indices make alpha-equivalence intrinsic to the representation. -/

namespace DeepWiki.Refine.DependentCalculus

namespace Substitution

/-- Substitute one term for the newest variable and leave every older variable unchanged. -/
def single (argument : Term n) : Substitution (n + 1) n :=
  Fin.cases argument Term.var

/-- Single substitution sends the newest variable to its argument. -/
@[simp] theorem single_zero (argument : Term n) : single argument 0 = argument :=
  rfl

/-- Single substitution leaves every older variable unchanged. -/
@[simp] theorem single_succ (argument : Term n) (index : Fin n) :
    single argument index.succ = .var index :=
  rfl

end Substitution

namespace Term

/-- Instantiate the newest variable of a term with a given argument. -/
def instantiate (body : Term (n + 1)) (argument : Term n) : Term n :=
  body.substitute (Substitution.single argument)

/-- Instantiating the newest variable returns the substituted argument. -/
@[simp] theorem instantiate_var_zero (argument : Term n) :
    (Term.var (0 : Fin (n + 1))).instantiate argument = argument :=
  rfl

/-- Instantiating an older variable leaves that variable unchanged. -/
@[simp] theorem instantiate_var_succ (argument : Term n) (index : Fin n) :
    (Term.var index.succ).instantiate argument = .var index :=
  rfl

/-- Renaming commutes with instantiation when the renaming is lifted beneath the binder. -/
theorem rename_instantiate (body : Term (source + 1)) (argument : Term source)
    (mapping : Renaming source target) :
    (body.instantiate argument).rename mapping =
      (body.rename (Renaming.lift mapping)).instantiate (argument.rename mapping) := by
  simp only [instantiate, Term.rename_substitute, Term.substitute_rename]
  apply Term.substitute_congr
  funext index
  exact Fin.cases rfl (fun _ => rfl) index

/-- Instantiating a weakened term cancels the weakening. -/
@[simp] theorem instantiate_rename_shift (term : Term n) (argument : Term n) :
    (term.rename Renaming.shift).instantiate argument = term := by
  simp only [instantiate, Term.substitute_rename]
  rw [show (fun index => Substitution.single argument (Renaming.shift index)) =
      Substitution.identity by
    funext index
    rfl]
  exact Term.substitute_identity term

/-- Lifted substitution after weakening equals substitution followed by weakening. -/
theorem substitute_rename_shift_lift (term : Term source)
    (mapping : Substitution source target) :
    (term.rename Renaming.shift).substitute (Substitution.lift mapping) =
      (term.substitute mapping).rename Renaming.shift := by
  simp only [Term.substitute_rename, Term.rename_substitute]
  apply Term.substitute_congr
  funext index
  rfl

/-- Simultaneous substitution commutes with single-variable instantiation. -/
theorem substitute_instantiate (body : Term (source + 1)) (argument : Term source)
    (mapping : Substitution source target) :
    (body.instantiate argument).substitute mapping =
      (body.substitute (Substitution.lift mapping)).instantiate
        (argument.substitute mapping) := by
  simp only [instantiate, Term.substitute_comp]
  apply Term.substitute_congr
  funext index
  refine Fin.cases rfl ?_ index
  intro older
  change mapping older =
    ((mapping older).rename Renaming.shift).instantiate (argument.substitute mapping)
  exact (instantiate_rename_shift (mapping older) (argument.substitute mapping)).symm

end Term

/-- One compatible beta-reduction step on intrinsically scoped terms. -/
inductive BetaStep : Term n → Term n → Prop where
  /-- Contract a beta redex by single-variable instantiation. -/
  | beta (domain : Term n) (body : Term (n + 1)) (argument : Term n) :
      BetaStep (.app (.lam domain body) argument) (body.instantiate argument)
  /-- Reduce the function of an application. -/
  | appFunction {function function' argument : Term n}
      (step : BetaStep function function') :
      BetaStep (.app function argument) (.app function' argument)
  /-- Reduce the argument of an application. -/
  | appArgument {function argument argument' : Term n}
      (step : BetaStep argument argument') :
      BetaStep (.app function argument) (.app function argument')
  /-- Reduce the domain annotation of a lambda. -/
  | lamDomain {domain domain' : Term n} {body : Term (n + 1)}
      (step : BetaStep domain domain') :
      BetaStep (.lam domain body) (.lam domain' body)
  /-- Reduce beneath a lambda binder. -/
  | lamBody {domain : Term n} {body body' : Term (n + 1)}
      (step : BetaStep body body') :
      BetaStep (.lam domain body) (.lam domain body')
  /-- Reduce the domain of a dependent product. -/
  | piDomain {domain domain' : Term n} {codomain : Term (n + 1)}
      (step : BetaStep domain domain') :
      BetaStep (.pi domain codomain) (.pi domain' codomain)
  /-- Reduce beneath a dependent-product binder. -/
  | piCodomain {domain : Term n} {codomain codomain' : Term (n + 1)}
      (step : BetaStep codomain codomain') :
      BetaStep (.pi domain codomain) (.pi domain codomain')

namespace BetaStep

/-- Renaming preserves compatible one-step beta reduction. -/
theorem rename {left right : Term source} (step : BetaStep left right)
    (mapping : Renaming source target) :
    BetaStep (left.rename mapping) (right.rename mapping) := by
  induction step generalizing target with
  | beta domain body argument =>
      simpa only [Term.rename, Term.rename_instantiate] using
        BetaStep.beta (domain.rename mapping) (body.rename (Renaming.lift mapping))
          (argument.rename mapping)
  | appFunction _ ih => exact .appFunction (ih mapping)
  | appArgument _ ih => exact .appArgument (ih mapping)
  | lamDomain _ ih => exact .lamDomain (ih mapping)
  | lamBody _ ih => exact .lamBody (ih (Renaming.lift mapping))
  | piDomain _ ih => exact .piDomain (ih mapping)
  | piCodomain _ ih => exact .piCodomain (ih (Renaming.lift mapping))

/-- Simultaneous substitution preserves compatible one-step beta reduction. -/
theorem substitute {left right : Term source} (step : BetaStep left right)
    (mapping : Substitution source target) :
    BetaStep (left.substitute mapping) (right.substitute mapping) := by
  induction step generalizing target with
  | beta domain body argument =>
      simpa only [Term.substitute, Term.substitute_instantiate] using
        BetaStep.beta (domain.substitute mapping)
          (body.substitute (Substitution.lift mapping)) (argument.substitute mapping)
  | appFunction _ ih => exact .appFunction (ih mapping)
  | appArgument _ ih => exact .appArgument (ih mapping)
  | lamDomain _ ih => exact .lamDomain (ih mapping)
  | lamBody _ ih => exact .lamBody (ih (Substitution.lift mapping))
  | piDomain _ ih => exact .piDomain (ih mapping)
  | piCodomain _ ih => exact .piCodomain (ih (Substitution.lift mapping))

end BetaStep

/-- Definitional conversion is the reflexive, symmetric, transitive closure of beta reduction. -/
inductive Convertible : Term n → Term n → Prop where
  /-- Every term is definitionally convertible to itself. -/
  | refl (term : Term n) : Convertible term term
  /-- Every beta-reduction step is a definitional conversion. -/
  | beta {left right : Term n} (step : BetaStep left right) : Convertible left right
  /-- Definitional conversion is symmetric. -/
  | symm {left right : Term n} (conversion : Convertible left right) :
      Convertible right left
  /-- Definitional conversion is transitive. -/
  | trans {first second third : Term n}
      (firstSecond : Convertible first second) (secondThird : Convertible second third) :
      Convertible first third

namespace Convertible

/-- Beta-convertibility is an equivalence relation on every scope. -/
def setoid (n : Nat) : Setoid (Term n) where
  r := Convertible
  iseqv := ⟨refl, symm, trans⟩

/-- Renaming preserves definitional conversion. -/
theorem rename {left right : Term source} (conversion : Convertible left right)
    (mapping : Renaming source target) :
    Convertible (left.rename mapping) (right.rename mapping) := by
  induction conversion with
  | refl => exact .refl _
  | beta step => exact .beta (step.rename mapping)
  | symm _ ih => exact ih.symm
  | trans _ _ first_ih second_ih => exact first_ih.trans second_ih

/-- Simultaneous substitution preserves definitional conversion. -/
theorem substitute {left right : Term source} (conversion : Convertible left right)
    (mapping : Substitution source target) :
    Convertible (left.substitute mapping) (right.substitute mapping) := by
  induction conversion with
  | refl => exact .refl _
  | beta step => exact .beta (step.substitute mapping)
  | symm _ ih => exact ih.symm
  | trans _ _ first_ih second_ih => exact first_ih.trans second_ih

/-- Convertible functions remain convertible after applying the same argument. -/
theorem app_function {function function' argument : Term n}
    (conversion : Convertible function function') :
    Convertible (.app function argument) (.app function' argument) := by
  induction conversion with
  | refl => exact .refl _
  | beta step => exact .beta (.appFunction step)
  | symm _ ih => exact ih.symm
  | trans _ _ first_ih second_ih => exact first_ih.trans second_ih

/-- Convertible arguments remain convertible under the same function. -/
theorem app_argument {function argument argument' : Term n}
    (conversion : Convertible argument argument') :
    Convertible (.app function argument) (.app function argument') := by
  induction conversion with
  | refl => exact .refl _
  | beta step => exact .beta (.appArgument step)
  | symm _ ih => exact ih.symm
  | trans _ _ first_ih second_ih => exact first_ih.trans second_ih

/-- Convertible lambda domains remain convertible under the same body. -/
theorem lam_domain {domain domain' : Term n} {body : Term (n + 1)}
    (conversion : Convertible domain domain') :
    Convertible (.lam domain body) (.lam domain' body) := by
  induction conversion with
  | refl => exact .refl _
  | beta step => exact .beta (.lamDomain step)
  | symm _ ih => exact ih.symm
  | trans _ _ first_ih second_ih => exact first_ih.trans second_ih

/-- Convertible lambda bodies remain convertible beneath their binder. -/
theorem lam_body {domain : Term n} {body body' : Term (n + 1)}
    (conversion : Convertible body body') :
    Convertible (.lam domain body) (.lam domain body') := by
  induction conversion with
  | refl => exact .refl _
  | beta step => exact .beta (.lamBody step)
  | symm _ ih => exact ih.symm
  | trans _ _ first_ih second_ih => exact first_ih.trans second_ih

/-- Convertible product domains remain convertible under the same codomain. -/
theorem pi_domain {domain domain' : Term n} {codomain : Term (n + 1)}
    (conversion : Convertible domain domain') :
    Convertible (.pi domain codomain) (.pi domain' codomain) := by
  induction conversion with
  | refl => exact .refl _
  | beta step => exact .beta (.piDomain step)
  | symm _ ih => exact ih.symm
  | trans _ _ first_ih second_ih => exact first_ih.trans second_ih

/-- Convertible product codomains remain convertible beneath their binder. -/
theorem pi_codomain {domain : Term n} {codomain codomain' : Term (n + 1)}
    (conversion : Convertible codomain codomain') :
    Convertible (.pi domain codomain) (.pi domain codomain') := by
  induction conversion with
  | refl => exact .refl _
  | beta step => exact .beta (.piCodomain step)
  | symm _ ih => exact ih.symm
  | trans _ _ first_ih second_ih => exact first_ih.trans second_ih

end Convertible

/-- Cumulative conversion for predicative universes and dependent products. -/
inductive Cumulative : Term n → Term n → Prop where
  /-- Definitional conversion is included in cumulative conversion. -/
  | conversion {left right : Term n} (equal : Convertible left right) :
      Cumulative left right
  /-- A lower universe embeds into every universe at least as high. -/
  | sort {lower upper : Nat} (level : lower ≤ upper) :
      Cumulative (.sort lower : Term n) (.sort upper)
  /-- Products are invariant up to conversion in the domain and cumulative in the codomain. -/
  | pi {domain domain' : Term n} {codomain codomain' : Term (n + 1)}
      (domainEqual : Convertible domain domain')
      (codomainCumulative : Cumulative codomain codomain') :
      Cumulative (.pi domain codomain) (.pi domain' codomain')
  /-- Application is covariant in its function while retaining the same argument. -/
  | app {function function' argument : Term n}
      (functionCumulative : Cumulative function function') :
      Cumulative (.app function argument) (.app function' argument)
  /-- Lambda abstraction is covariant in its body under an unchanged domain. -/
  | lam {domain : Term n} {body body' : Term (n + 1)}
      (bodyCumulative : Cumulative body body') :
      Cumulative (.lam domain body) (.lam domain body')
  /-- Products are contravariant in their domains and covariant in their codomains. -/
  | piStructural {domain domain' : Term n} {codomain codomain' : Term (n + 1)}
      (domainCumulative : Cumulative domain' domain)
      (codomainCumulative : Cumulative codomain codomain') :
      Cumulative (.pi domain codomain) (.pi domain' codomain')
  /-- Cumulative conversion is transitive. -/
  | trans {first second third : Term n}
      (firstSecond : Cumulative first second) (secondThird : Cumulative second third) :
      Cumulative first third

namespace Cumulative

/-- Cumulative conversion is reflexive. -/
theorem refl (term : Term n) : Cumulative term term :=
  .conversion (.refl term)

/-- Every definitional conversion is a cumulative conversion. -/
theorem of_convertible {left right : Term n} (equal : Convertible left right) :
    Cumulative left right :=
  .conversion equal

/-- Renaming preserves cumulative conversion. -/
theorem rename {left right : Term source} (subtype : Cumulative left right)
    (mapping : Renaming source target) :
    Cumulative (left.rename mapping) (right.rename mapping) := by
  induction subtype generalizing target with
  | conversion equal => exact .conversion (equal.rename mapping)
  | sort level => exact .sort level
  | pi domainEqual _ codomain_ih =>
      exact .pi (domainEqual.rename mapping) (codomain_ih (Renaming.lift mapping))
  | app _ function_ih => exact .app (function_ih mapping)
  | lam _ body_ih => exact .lam (body_ih (Renaming.lift mapping))
  | piStructural _ _ domain_ih codomain_ih =>
      exact .piStructural (domain_ih mapping) (codomain_ih (Renaming.lift mapping))
  | trans _ _ first_ih second_ih => exact (first_ih mapping).trans (second_ih mapping)

/-- Simultaneous substitution preserves cumulative conversion. -/
theorem substitute {left right : Term source} (subtype : Cumulative left right)
    (mapping : Substitution source target) :
    Cumulative (left.substitute mapping) (right.substitute mapping) := by
  induction subtype generalizing target with
  | conversion equal => exact .conversion (equal.substitute mapping)
  | sort level => exact .sort level
  | pi domainEqual _ codomain_ih =>
      exact .pi (domainEqual.substitute mapping)
        (codomain_ih (Substitution.lift mapping))
  | app _ function_ih => exact .app (function_ih mapping)
  | lam _ body_ih => exact .lam (body_ih (Substitution.lift mapping))
  | piStructural _ _ domain_ih codomain_ih =>
      exact .piStructural (domain_ih mapping)
        (codomain_ih (Substitution.lift mapping))
  | trans _ _ first_ih second_ih => exact (first_ih mapping).trans (second_ih mapping)

end Cumulative

/-- Kinds are universes or dependent products ending in a kind. -/
inductive IsKind : Term n → Prop where
  /-- Every universe is a kind. -/
  | sort (level : Nat) : IsKind (.sort level : Term n)
  /-- A product is a kind when its codomain is a kind. -/
  | pi (domain : Term n) {codomain : Term (n + 1)}
      (codomainKind : IsKind codomain) : IsKind (.pi domain codomain)

namespace IsKind

/-- Renaming preserves the syntactic shape of kinds. -/
theorem rename {kind : Term source} (kindShape : IsKind kind)
    (mapping : Renaming source target) : IsKind (kind.rename mapping) := by
  induction kindShape generalizing target with
  | sort => exact .sort _
  | pi domain _ inductionHypothesis =>
      exact .pi (domain.rename mapping) (inductionHypothesis (Renaming.lift mapping))

/-- Substitution preserves the syntactic shape of kinds. -/
theorem substitute {kind : Term source} (kindShape : IsKind kind)
    (mapping : Substitution source target) : IsKind (kind.substitute mapping) := by
  induction kindShape generalizing target with
  | sort => exact .sort _
  | pi domain _ inductionHypothesis =>
      exact .pi (domain.substitute mapping)
        (inductionHypothesis (Substitution.lift mapping))

end IsKind

mutual

  /-- A context is well-formed when every extension is by a type in some universe. -/
  inductive WellFormed : Context n → Prop where
    /-- The empty context is well-formed. -/
    | empty : WellFormed .empty
    /-- Extend a well-formed context by a well-typed type. -/
    | extend {context : Context n} {type : Term n} {level : Nat}
        (contextWellFormed : WellFormed context)
        (typeWellTyped : HasType context type (.sort level)) :
        WellFormed (.extend context type)

  /-- `HasType Γ term type` is the cumulative dependent typing judgment. -/
  inductive HasType : Context n → Term n → Term n → Prop where
    /-- Every universe is typed by its immediate predicative successor. -/
    | sort {context : Context n} (contextWellFormed : WellFormed context)
        (level : Nat) :
        HasType context (.sort level) (.sort (level + 1))
    /-- A variable has the type obtained by dependent context lookup. -/
    | var {context : Context n} (contextWellFormed : WellFormed context)
        (index : Fin n) :
        HasType context (.var index) (context.lookup index)
    /-- Applying a dependent function instantiates its codomain with the argument. -/
    | app {context : Context n} {function argument domain : Term n}
        {codomain : Term (n + 1)}
        (functionWellTyped : HasType context function (.pi domain codomain))
        (argumentWellTyped : HasType context argument domain) :
        HasType context (.app function argument) (codomain.instantiate argument)
    /-- A lambda has a dependent-product type when its body has the codomain type. -/
    | lam {context : Context n} {domain : Term n} {body codomain : Term (n + 1)}
        {domainLevel : Nat}
        (domainWellTyped : HasType context domain (.sort domainLevel))
        (bodyWellTyped : HasType (.extend context domain) body codomain) :
        HasType context (.lam domain body) (.pi domain codomain)
    /-- A dependent product lies in the maximum universe of its domain and codomain. -/
    | pi {context : Context n} {domain : Term n} {codomain : Term (n + 1)}
        {domainLevel codomainLevel : Nat}
        (domainWellTyped : HasType context domain (.sort domainLevel))
        (codomainWellTyped : HasType (.extend context domain) codomain (.sort codomainLevel)) :
        HasType context (.pi domain codomain) (.sort (max domainLevel codomainLevel))
    /-- A term may be assigned a definitionally convertible well-formed type. -/
    | conversion {context : Context n} {term type type' : Term n} {level : Nat}
        (termWellTyped : HasType context term type)
        (targetWellTyped : HasType context type' (.sort level))
        (equal : Convertible type type') :
        HasType context term type'
    /-- A term may be assigned a cumulative well-formed supertype. -/
    | cumulativity {context : Context n} {term type type' : Term n} {level : Nat}
        (termWellTyped : HasType context term type)
        (targetWellTyped : HasType context type' (.sort level))
        (subtype : Cumulative type type') :
        HasType context term type'
end

/-- A typed context renaming preserves each looked-up dependent type exactly after renaming. -/
structure TypedRenaming (source : Context sourceSize) (target : Context targetSize)
    (mapping : Renaming sourceSize targetSize) : Prop where
  /-- The target context is well-formed. -/
  targetWellFormed : WellFormed target
  /-- Every target lookup is the explicitly renamed source lookup. -/
  lookup_eq (index : Fin sourceSize) :
    target.lookup (mapping index) = (source.lookup index).rename mapping

namespace TypedRenaming

/-- The identity renaming is typed on every well-formed context. -/
theorem identity {context : Context n} (contextWellFormed : WellFormed context) :
    TypedRenaming context context Renaming.identity where
  targetWellFormed := contextWellFormed
  lookup_eq index := (Term.rename_identity (context.lookup index)).symm

/-- Typed context renamings compose. -/
theorem comp {first : Context firstSize} {second : Context secondSize}
    {third : Context thirdSize} {inner : Renaming firstSize secondSize}
    {outer : Renaming secondSize thirdSize}
    (outerTyped : TypedRenaming second third outer)
    (innerTyped : TypedRenaming first second inner) :
    TypedRenaming first third (Renaming.comp outer inner) where
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

/-- Extend a typed renaming beneath matching dependent context extensions. -/
theorem lift {source : Context sourceSize} {target : Context targetSize}
    {mapping : Renaming sourceSize targetSize} {domain : Term sourceSize} {level : Nat}
    (mappingTyped : TypedRenaming source target mapping)
    (domainWellTyped : HasType target (domain.rename mapping) (.sort level)) :
    TypedRenaming (.extend source domain) (.extend target (domain.rename mapping))
      (Renaming.lift mapping) where
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

/-- Weakening into a well-formed extension is a typed context renaming. -/
theorem shift {context : Context n} {domain : Term n}
    (extendedWellFormed : WellFormed (.extend context domain)) :
    TypedRenaming context (.extend context domain) Renaming.shift where
  targetWellFormed := extendedWellFormed
  lookup_eq _index := rfl

end TypedRenaming

namespace WellFormed

/-- A typed context renaming carries well-formedness to its target context. -/
theorem rename {source : Context sourceSize} {target : Context targetSize}
    {mapping : Renaming sourceSize targetSize} (_sourceWellFormed : WellFormed source)
    (mappingTyped : TypedRenaming source target mapping) : WellFormed target :=
  mappingTyped.targetWellFormed

end WellFormed

namespace HasType

/-- Every typing derivation contains a derivation that its context is well formed. -/
theorem contextWellFormed {context : Context n} {term type : Term n}
    (termWellTyped : HasType context term type) : WellFormed context := by
  refine HasType.rec
    (motive_1 := fun context _ => WellFormed context)
    (motive_2 := fun context _ _ _ => WellFormed context)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ termWellTyped
  · exact WellFormed.empty
  · intro n context type level contextWellFormed typeWellTyped _ _
    exact WellFormed.extend contextWellFormed typeWellTyped
  all_goals intros; assumption

/-- Typing a product term exposes universe typings for its domain and codomain. -/
theorem piComponents {context : Context n} {domain : Term n} {codomain : Term (n + 1)}
    {type : Term n} :
    HasType context (.pi domain codomain) type →
      ∃ domainLevel codomainLevel,
        HasType context domain (.sort domainLevel) ∧
          HasType (.extend context domain) codomain (.sort codomainLevel) := by
  intro productWellTyped
  refine HasType.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := fun context term _ _ =>
      match term with
      | .pi domain codomain =>
          ∃ domainLevel codomainLevel,
            HasType context domain (.sort domainLevel) ∧
              HasType (.extend context domain) codomain (.sort codomainLevel)
      | _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ productWellTyped
  all_goals intros
  all_goals aesop

/-- Typing an application exposes a dependent-function typing and its argument typing. -/
theorem appComponents {context : Context n} {function argument type : Term n} :
    HasType context (.app function argument) type →
      ∃ domain codomain,
        HasType context function (.pi domain codomain) ∧
          HasType context argument domain := by
  intro applicationWellTyped
  refine HasType.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := fun context term _ _ =>
      match term with
      | .app function argument =>
          ∃ domain codomain,
            HasType context function (.pi domain codomain) ∧
              HasType context argument domain
      | _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ applicationWellTyped
  all_goals intros
  all_goals aesop

/-- Typing a lambda exposes its universe-typed domain and its body typing. -/
theorem lamComponents {context : Context n} {domain : Term n}
    {body : Term (n + 1)} {type : Term n} :
    HasType context (.lam domain body) type →
      ∃ codomain level,
        HasType context domain (.sort level) ∧
          HasType (.extend context domain) body codomain := by
  intro lambdaWellTyped
  refine HasType.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := fun context term _ _ =>
      match term with
      | .lam domain body =>
          ∃ codomain level,
            HasType context domain (.sort level) ∧
              HasType (.extend context domain) body codomain
      | _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ lambdaWellTyped
  all_goals intros
  all_goals aesop

/-- Cumulativity types a universe by any strictly higher universe. -/
theorem sort_of_lt {context : Context n} (contextWellFormed : WellFormed context)
    {level upper : Nat} (strict : level < upper) :
    HasType context (.sort level) (.sort upper) := by
  exact .cumulativity (.sort contextWellFormed level) (.sort contextWellFormed upper)
    (.sort (Nat.succ_le_iff.mpr strict))

/-- Typed context renaming preserves dependent typing. -/
theorem rename {source : Context sourceSize} {term type : Term sourceSize}
    (termWellTyped : HasType source term type) :
    ∀ {targetSize} {target : Context targetSize}
      {mapping : Renaming sourceSize targetSize},
      TypedRenaming source target mapping →
        HasType target (term.rename mapping) (type.rename mapping) := by
  refine HasType.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := fun {n} context term type _ =>
      ∀ {targetSize} {target : Context targetSize} {mapping : Renaming n targetSize},
        TypedRenaming context target mapping →
          HasType target (term.rename mapping) (type.rename mapping))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ termWellTyped
  · trivial
  · intros
    trivial
  · intro _ _ _ level _ _ _ mapping mappingTyped
    exact .sort mappingTyped.targetWellFormed level
  · intro _ _ _ index _ _ _ mapping mappingTyped
    have variableWellTyped := HasType.var mappingTyped.targetWellFormed (mapping index)
    rw [mappingTyped.lookup_eq index] at variableWellTyped
    exact variableWellTyped
  · intro _ _ _ _ _ _ _ _ function_ih argument_ih _ _ _ mappingTyped
    have applicationWellTyped := HasType.app (function_ih mappingTyped)
      (argument_ih mappingTyped)
    simpa only [Term.rename, Term.rename_instantiate] using applicationWellTyped
  · intro _ _ _ _ _ _ _ _ domain_ih body_ih _ _ _ mappingTyped
    have renamedDomain := domain_ih mappingTyped
    have renamedBody := body_ih (mappingTyped.lift renamedDomain)
    exact .lam renamedDomain renamedBody
  · intro _ _ _ _ _ _ _ _ domain_ih codomain_ih _ _ _ mappingTyped
    have renamedDomain := domain_ih mappingTyped
    have renamedCodomain := codomain_ih (mappingTyped.lift renamedDomain)
    exact .pi renamedDomain renamedCodomain
  · intro _ _ _ _ _ _ _ _ equal term_ih target_ih _ _ mapping mappingTyped
    exact .conversion (term_ih mappingTyped) (target_ih mappingTyped)
      (equal.rename mapping)
  · intro _ _ _ _ _ _ _ _ subtype term_ih target_ih _ _ mapping mappingTyped
    exact .cumulativity (term_ih mappingTyped) (target_ih mappingTyped)
      (subtype.rename mapping)

/-- Weakening a typing derivation into a well-formed context extension preserves its type. -/
theorem weaken {context : Context n} {term type domain : Term n}
    (termWellTyped : HasType context term type)
    (extendedWellFormed : WellFormed (.extend context domain)) :
    HasType (.extend context domain) (term.rename Renaming.shift)
      (type.rename Renaming.shift) :=
  termWellTyped.rename (TypedRenaming.shift extendedWellFormed)

end HasType

namespace WellFormed

/-- Every lookup in a well-formed context is typed by some universe. -/
theorem lookup_hasType {context : Context n} (contextWellFormed : WellFormed context)
    (index : Fin n) :
    ∃ level, HasType context (context.lookup index) (.sort level) := by
  refine WellFormed.rec
    (motive_1 := fun {n} context _ =>
      ∀ index : Fin n, ∃ level, HasType context (context.lookup index) (.sort level))
    (motive_2 := fun _ _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ contextWellFormed index
  · exact fun index => Fin.elim0 index
  · intro n context domain level contextWellFormed domainWellTyped
      inductionHypothesis _ index
    refine Fin.cases ?_ ?_ index
    · refine ⟨level, ?_⟩
      simpa only [Context.lookup_zero, Term.rename] using
        domainWellTyped.weaken (.extend contextWellFormed domainWellTyped)
    · intro older
      obtain ⟨olderLevel, olderWellTyped⟩ := inductionHypothesis older
      refine ⟨olderLevel, ?_⟩
      simpa only [Context.lookup_succ, Term.rename] using
        olderWellTyped.weaken (.extend contextWellFormed domainWellTyped)
  all_goals intros; trivial

end WellFormed

/-- A typed simultaneous substitution assigns every source variable its substituted lookup type. -/
structure TypedSubstitution (source : Context sourceSize) (target : Context targetSize)
    (mapping : Substitution sourceSize targetSize) : Prop where
  /-- The substitution target context is well-formed. -/
  targetWellFormed : WellFormed target
  /-- Each substituted variable has its source lookup type after the same substitution. -/
  variableWellTyped (index : Fin sourceSize) :
    HasType target (mapping index) ((source.lookup index).substitute mapping)

namespace TypedSubstitution

/-- The identity substitution is typed on every well-formed context. -/
theorem identity {context : Context n} (contextWellFormed : WellFormed context) :
    TypedSubstitution context context Substitution.identity where
  targetWellFormed := contextWellFormed
  variableWellTyped index := by
    change HasType context (.var index)
      ((context.lookup index).substitute Substitution.identity)
    rw [Term.substitute_identity]
    exact HasType.var contextWellFormed index

/-- Every typed renaming induces a typed variable-only substitution. -/
theorem ofRenaming {source : Context sourceSize} {target : Context targetSize}
    {mapping : Renaming sourceSize targetSize}
    (mappingTyped : TypedRenaming source target mapping) :
    TypedSubstitution source target (Substitution.ofRenaming mapping) where
  targetWellFormed := mappingTyped.targetWellFormed
  variableWellTyped index := by
    have variableWellTyped := HasType.var mappingTyped.targetWellFormed (mapping index)
    rw [mappingTyped.lookup_eq index] at variableWellTyped
    simpa only [Substitution.ofRenaming, Term.substitute_ofRenaming] using variableWellTyped

/-- Extend a typed substitution beneath matching dependent context extensions. -/
theorem lift {source : Context sourceSize} {target : Context targetSize}
    {mapping : Substitution sourceSize targetSize} {domain : Term sourceSize}
    {level : Nat} (mappingTyped : TypedSubstitution source target mapping)
    (domainWellTyped : HasType target (domain.substitute mapping) (.sort level)) :
    TypedSubstitution (.extend source domain) (.extend target (domain.substitute mapping))
      (Substitution.lift mapping) where
  targetWellFormed := .extend mappingTyped.targetWellFormed domainWellTyped
  variableWellTyped index := by
    refine Fin.cases ?_ ?_ index
    · have newestWellTyped := HasType.var
        (WellFormed.extend mappingTyped.targetWellFormed domainWellTyped) 0
      simpa only [Substitution.lift_zero, Context.lookup_zero,
        Term.substitute_rename_shift_lift] using newestWellTyped
    · intro older
      have olderWellTyped := (mappingTyped.variableWellTyped older).weaken
        (WellFormed.extend mappingTyped.targetWellFormed domainWellTyped)
      simpa only [Substitution.lift_succ, Context.lookup_succ,
        Term.substitute_rename_shift_lift] using olderWellTyped

/-- A well-typed argument gives the typed single substitution for the newest variable. -/
theorem single {context : Context n} {domain argument : Term n}
    (contextWellFormed : WellFormed context)
    (argumentWellTyped : HasType context argument domain) :
    TypedSubstitution (.extend context domain) context (Substitution.single argument) where
  targetWellFormed := contextWellFormed
  variableWellTyped index := by
    refine Fin.cases ?_ ?_ index
    · change HasType context argument ((domain.rename Renaming.shift).instantiate argument)
      rw [Term.instantiate_rename_shift]
      exact argumentWellTyped
    · intro older
      change HasType context (.var older)
        (((context.lookup older).rename Renaming.shift).instantiate argument)
      rw [Term.instantiate_rename_shift]
      exact HasType.var contextWellFormed older

end TypedSubstitution

namespace WellFormed

/-- A typed simultaneous substitution carries well-formedness to its target context. -/
theorem substitute {source : Context sourceSize} {target : Context targetSize}
    {mapping : Substitution sourceSize targetSize} (_sourceWellFormed : WellFormed source)
    (mappingTyped : TypedSubstitution source target mapping) : WellFormed target :=
  mappingTyped.targetWellFormed

end WellFormed

namespace HasType

/-- Typed simultaneous substitution preserves dependent typing. -/
theorem substitute {source : Context sourceSize} {term type : Term sourceSize}
    (termWellTyped : HasType source term type) :
    ∀ {targetSize} {target : Context targetSize}
      {mapping : Substitution sourceSize targetSize},
      TypedSubstitution source target mapping →
        HasType target (term.substitute mapping) (type.substitute mapping) := by
  refine HasType.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := fun {n} context term type _ =>
      ∀ {targetSize} {target : Context targetSize} {mapping : Substitution n targetSize},
        TypedSubstitution context target mapping →
          HasType target (term.substitute mapping) (type.substitute mapping))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ termWellTyped
  · trivial
  · intros
    trivial
  · intro _ _ _ level _ _ _ mapping mappingTyped
    exact .sort mappingTyped.targetWellFormed level
  · intro _ _ _ index _ _ _ _ mappingTyped
    exact mappingTyped.variableWellTyped index
  · intro _ _ _ _ _ _ _ _ function_ih argument_ih _ _ _ mappingTyped
    have applicationWellTyped := HasType.app (function_ih mappingTyped)
      (argument_ih mappingTyped)
    simpa only [Term.substitute, Term.substitute_instantiate] using applicationWellTyped
  · intro _ _ _ _ _ _ _ _ domain_ih body_ih _ _ _ mappingTyped
    have substitutedDomain := domain_ih mappingTyped
    have substitutedBody := body_ih (mappingTyped.lift substitutedDomain)
    exact .lam substitutedDomain substitutedBody
  · intro _ _ _ _ _ _ _ _ domain_ih codomain_ih _ _ _ mappingTyped
    have substitutedDomain := domain_ih mappingTyped
    have substitutedCodomain := codomain_ih (mappingTyped.lift substitutedDomain)
    exact .pi substitutedDomain substitutedCodomain
  · intro _ _ _ _ _ _ _ _ equal term_ih target_ih _ _ mapping mappingTyped
    exact .conversion (term_ih mappingTyped) (target_ih mappingTyped)
      (equal.substitute mapping)
  · intro _ _ _ _ _ _ _ _ subtype term_ih target_ih _ _ mapping mappingTyped
    exact .cumulativity (term_ih mappingTyped) (target_ih mappingTyped)
      (subtype.substitute mapping)

/-- Instantiating a typed body with a typed argument preserves the instantiated type. -/
theorem instantiate {context : Context n} {domain argument : Term n}
    {body type : Term (n + 1)}
    (bodyWellTyped : HasType (.extend context domain) body type)
    (contextWellFormed : WellFormed context)
    (argumentWellTyped : HasType context argument domain) :
    HasType context (body.instantiate argument) (type.instantiate argument) :=
  bodyWellTyped.substitute (TypedSubstitution.single contextWellFormed argumentWellTyped)

end HasType

namespace HasType

/-- The assigned type of every well-typed term itself inhabits a universe. -/
theorem typeWellTyped {context : Context n} {term type : Term n}
    (termWellTyped : HasType context term type) :
    ∃ level, HasType context type (.sort level) := by
  refine HasType.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := fun context _ type _ =>
      ∃ level, HasType context type (.sort level))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ termWellTyped
  · trivial
  · intros
    trivial
  · intro _ _ contextWellFormed level _
    exact ⟨level + 2, by
      simpa only [Nat.add_assoc] using HasType.sort contextWellFormed (level + 1)⟩
  · intro _ _ contextWellFormed index _
    exact contextWellFormed.lookup_hasType index
  · intro _ _ _ _ _ _ _ argumentWellTyped functionInduction _
    obtain ⟨_, functionTypeWellTyped⟩ := functionInduction
    obtain ⟨_, codomainLevel, _, codomainWellTyped⟩ :=
      piComponents functionTypeWellTyped
    exact ⟨codomainLevel,
      codomainWellTyped.instantiate argumentWellTyped.contextWellFormed
        argumentWellTyped⟩
  · intro _ _ _ _ _ _ domainWellTyped _ _ bodyInduction
    obtain ⟨codomainLevel, codomainWellTyped⟩ := bodyInduction
    exact ⟨max _ codomainLevel, HasType.pi domainWellTyped codomainWellTyped⟩
  · intro _ _ _ _ domainLevel codomainLevel domainWellTyped _ _ _
    exact ⟨max domainLevel codomainLevel + 1,
      HasType.sort domainWellTyped.contextWellFormed (max domainLevel codomainLevel)⟩
  · intro _ _ _ _ _ level _ targetWellTyped _ _ _
    exact ⟨level, targetWellTyped⟩
  · intro _ _ _ _ _ level _ targetWellTyped _ _ _
    exact ⟨level, targetWellTyped⟩

end HasType

namespace TypedSubstitution

/-- Typed simultaneous substitutions compose. -/
theorem comp {first : Context firstSize} {second : Context secondSize}
    {third : Context thirdSize} {inner : Substitution firstSize secondSize}
    {outer : Substitution secondSize thirdSize}
    (outerTyped : TypedSubstitution second third outer)
    (innerTyped : TypedSubstitution first second inner) :
    TypedSubstitution first third (Substitution.comp outer inner) where
  targetWellFormed := outerTyped.targetWellFormed
  variableWellTyped index := by
    have variableWellTyped := (innerTyped.variableWellTyped index).substitute outerTyped
    simpa only [Substitution.comp, Term.substitute_comp] using variableWellTyped

end TypedSubstitution

example (argument : Term n) :
    Substitution.single argument 0 = argument :=
  rfl

example (body : Term (n + 1)) (argument : Term n) :
    body.instantiate argument = body.substitute (Substitution.single argument) :=
  rfl

example (domain : Term n) (body : Term (n + 1)) (argument : Term n) :
    BetaStep (.app (.lam domain body) argument) (body.instantiate argument) :=
  .beta domain body argument

example (domain : Term n) (body : Term (n + 1)) (argument : Term n) :
    Convertible (.app (.lam domain body) argument) (body.instantiate argument) :=
  .beta (.beta domain body argument)

example (term : Term n) : Convertible term term :=
  .refl term

example {left right : Term n} (conversion : Convertible left right) :
    Convertible right left :=
  conversion.symm

example {left right : Term n} (conversion : Convertible left right) :
    Cumulative left right :=
  .conversion conversion

example {lower upper : Nat} (level : lower ≤ upper) :
    Cumulative (.sort lower : Term n) (.sort upper) :=
  .sort level

example {domain domain' : Term n} {codomain codomain' : Term (n + 1)}
    (domainEqual : Convertible domain domain')
    (codomainCumulative : Cumulative codomain codomain') :
    Cumulative (.pi domain codomain) (.pi domain' codomain') :=
  .pi domainEqual codomainCumulative

example : WellFormed Context.empty :=
  .empty

example {context : Context n} {type : Term n} {level : Nat}
    (contextWellFormed : WellFormed context)
    (typeWellTyped : HasType context type (.sort level)) :
    WellFormed (.extend context type) :=
  .extend contextWellFormed typeWellTyped

example {context : Context n} (contextWellFormed : WellFormed context) (level : Nat) :
    HasType context (.sort level) (.sort (level + 1)) :=
  .sort contextWellFormed level

example {context : Context n} (contextWellFormed : WellFormed context)
    {level upper : Nat} (strict : level < upper) :
    HasType context (.sort level) (.sort upper) :=
  HasType.sort_of_lt contextWellFormed strict

example {context : Context n} (contextWellFormed : WellFormed context) (index : Fin n) :
    HasType context (.var index) (context.lookup index) :=
  .var contextWellFormed index

example {context : Context n} (contextWellFormed : WellFormed context) (index : Fin n) :
    ∃ level, HasType context (context.lookup index) (.sort level) :=
  contextWellFormed.lookup_hasType index

example {context : Context n} {function argument domain : Term n}
    {codomain : Term (n + 1)}
    (functionWellTyped : HasType context function (.pi domain codomain))
    (argumentWellTyped : HasType context argument domain) :
    HasType context (.app function argument) (codomain.instantiate argument) :=
  .app functionWellTyped argumentWellTyped

example {context : Context n} {domain : Term n} {body codomain : Term (n + 1)}
    {domainLevel : Nat}
    (domainWellTyped : HasType context domain (.sort domainLevel))
    (bodyWellTyped : HasType (.extend context domain) body codomain) :
    HasType context (.lam domain body) (.pi domain codomain) :=
  .lam domainWellTyped bodyWellTyped

example {context : Context n} {domain : Term n} {codomain : Term (n + 1)}
    {domainLevel codomainLevel : Nat}
    (domainWellTyped : HasType context domain (.sort domainLevel))
    (codomainWellTyped : HasType (.extend context domain) codomain (.sort codomainLevel)) :
    HasType context (.pi domain codomain) (.sort (max domainLevel codomainLevel)) :=
  .pi domainWellTyped codomainWellTyped

example {context : Context n} {domain : Term n} {codomain : Term (n + 1)}
    {type : Term n} (productWellTyped : HasType context (.pi domain codomain) type) :
    ∃ domainLevel codomainLevel,
      HasType context domain (.sort domainLevel) ∧
        HasType (.extend context domain) codomain (.sort codomainLevel) :=
  productWellTyped.piComponents

example {context : Context n} {term type type' : Term n} {level : Nat}
    (termWellTyped : HasType context term type)
    (targetWellTyped : HasType context type' (.sort level))
    (equal : Convertible type type') :
    HasType context term type' :=
  .conversion termWellTyped targetWellTyped equal

example {context : Context n} {term type type' : Term n} {level : Nat}
    (termWellTyped : HasType context term type)
    (targetWellTyped : HasType context type' (.sort level))
    (subtype : Cumulative type type') :
    HasType context term type' :=
  .cumulativity termWellTyped targetWellTyped subtype

example (body : Term (source + 1)) (argument : Term source)
    (mapping : Renaming source target) :
    (body.instantiate argument).rename mapping =
      (body.rename (Renaming.lift mapping)).instantiate (argument.rename mapping) :=
  Term.rename_instantiate body argument mapping

example {left right : Term source} (step : BetaStep left right)
    (mapping : Renaming source target) :
    BetaStep (left.rename mapping) (right.rename mapping) :=
  step.rename mapping

example {left right : Term source} (conversion : Convertible left right)
    (mapping : Substitution source target) :
    Convertible (left.substitute mapping) (right.substitute mapping) :=
  conversion.substitute mapping

example {source : Context sourceSize} {target : Context targetSize}
    {mapping : Renaming sourceSize targetSize}
    (mappingTyped : TypedRenaming source target mapping) (index : Fin sourceSize) :
    target.lookup (mapping index) = (source.lookup index).rename mapping :=
  mappingTyped.lookup_eq index

example {source : Context sourceSize} {target : Context targetSize}
    {mapping : Renaming sourceSize targetSize} {term type : Term sourceSize}
    (termWellTyped : HasType source term type)
    (mappingTyped : TypedRenaming source target mapping) :
    HasType target (term.rename mapping) (type.rename mapping) :=
  termWellTyped.rename mappingTyped

example {context : Context n} {term type domain : Term n}
    (termWellTyped : HasType context term type)
    (extendedWellFormed : WellFormed (.extend context domain)) :
    HasType (.extend context domain) (term.rename Renaming.shift)
      (type.rename Renaming.shift) :=
  termWellTyped.weaken extendedWellFormed

example {source : Context sourceSize} {target : Context targetSize}
    {mapping : Substitution sourceSize targetSize}
    (mappingTyped : TypedSubstitution source target mapping) (index : Fin sourceSize) :
    HasType target (mapping index) ((source.lookup index).substitute mapping) :=
  mappingTyped.variableWellTyped index

example {source : Context sourceSize} {target : Context targetSize}
    {mapping : Substitution sourceSize targetSize} {term type : Term sourceSize}
    (termWellTyped : HasType source term type)
    (mappingTyped : TypedSubstitution source target mapping) :
    HasType target (term.substitute mapping) (type.substitute mapping) :=
  termWellTyped.substitute mappingTyped

example {context : Context n} {domain argument : Term n}
    {body type : Term (n + 1)}
    (bodyWellTyped : HasType (.extend context domain) body type)
    (contextWellFormed : WellFormed context)
    (argumentWellTyped : HasType context argument domain) :
    HasType context (body.instantiate argument) (type.instantiate argument) :=
  bodyWellTyped.instantiate contextWellFormed argumentWellTyped

end DeepWiki.Refine.DependentCalculus
