import DeepWiki.Refine.Dependent
import DeepWiki.Refine.RelationStructure

/-! # A core parametricity calculus

An intrinsically typed lambda calculus gives a compact, executable statement of the abstraction
theorem. Its relation environments are the semantic counterpart of parametricity contexts. -/

namespace DeepWiki.Refine

universe u v w w'

/-- An annotated universe records a universe level and the relation structure requested there. -/
structure AnnotatedUniverse where
  /-- The ordinary universe level. -/
  level : Nat
  /-- The forward/backward relation annotation at that universe occurrence. -/
  annotation : Annotation
  deriving DecidableEq, Repr

/-- A minimal syntax of annotated universes and dependent products. -/
inductive AnnotatedType where
  /-- An annotated universe occurrence. -/
  | universe (data : AnnotatedUniverse)
  /-- An annotated dependent product with syntactic domain and codomain. -/
  | pi (annotation : Annotation) (domain codomain : AnnotatedType)
  deriving DecidableEq, Repr

/-- Types of the intrinsic core lambda calculus. -/
inductive CoreType where
  /-- The single open base type. -/
  | base
  /-- A function type. -/
  | arrow (domain codomain : CoreType)
  deriving DecidableEq, Repr

/-- Interpret a core type after choosing a carrier for its open base type. -/
def CoreType.interpret (Base : Type u) : CoreType → Type u
  | .base => Base
  | .arrow domain codomain => domain.interpret Base → codomain.interpret Base

/-- Fold a base relation and an arrow constructor over the intrinsic core types. -/
def CoreType.foldRelation (Motive : CoreType → Sort w) (base : Motive .base)
    (arrow : ∀ domain codomain, Motive domain → Motive codomain →
      Motive (.arrow domain codomain)) : (type : CoreType) → Motive type
  | .base => base
  | .arrow domain codomain =>
      arrow domain codomain (domain.foldRelation Motive base arrow)
        (codomain.foldRelation Motive base arrow)

/-- Respectful-arrow construction for relations in arbitrary sorts. -/
abbrev CoreType.arrowRelation {A : Type u} {B : Type v}
    {domain codomain : CoreType}
    (domainRel : domain.interpret A → domain.interpret B → Sort w)
    (codomainRel : codomain.interpret A → codomain.interpret B → Sort w')
    (f : (CoreType.arrow domain codomain).interpret A)
    (g : (CoreType.arrow domain codomain).interpret B) :=
  ∀ a b, domainRel a b → codomainRel (f a) (g b)

/-- Proposition-valued relational interpretation of a core type. -/
def CoreType.rel {A : Type u} {B : Type v} (R : A → B → Prop) :
    (type : CoreType) → type.interpret A → type.interpret B → Prop :=
  CoreType.foldRelation
    (Motive := fun type => type.interpret A → type.interpret B → Prop)
    R (fun _ _ domainRel codomainRel => CoreType.arrowRelation domainRel codomainRel)

/-- Intrinsically typed de Bruijn variables. -/
inductive CoreVar : List CoreType → CoreType → Type where
  /-- The newest variable in a context. -/
  | zero : CoreVar (type :: context) type
  /-- A variable inherited from the preceding context. -/
  | succ : CoreVar context type → CoreVar (head :: context) type

/-- Intrinsically typed terms of the core lambda calculus. -/
inductive CoreTerm : List CoreType → CoreType → Type where
  /-- A term variable. -/
  | var : CoreVar context type → CoreTerm context type
  /-- Function application. -/
  | app : CoreTerm context (.arrow domain codomain) → CoreTerm context domain →
      CoreTerm context codomain
  /-- Lambda abstraction. -/
  | lam : CoreTerm (domain :: context) codomain → CoreTerm context (.arrow domain codomain)

/-- A semantic environment for a core typing context. -/
inductive CoreEnv (Base : Type u) : List CoreType → Type u where
  /-- The empty environment. -/
  | nil : CoreEnv Base []
  /-- Extend an environment by a value for the newest variable. -/
  | cons : type.interpret Base → CoreEnv Base context → CoreEnv Base (type :: context)

/-- Look up an intrinsically typed variable in a semantic environment. -/
def CoreEnv.get {Base : Type u} :
    CoreVar context type → CoreEnv Base context → type.interpret Base
  | .zero, .cons value _ => value
  | .succ var, .cons _ env => env.get var

/-- Evaluate an intrinsically typed core term in a semantic environment. -/
def CoreTerm.evaluate {Base : Type u} :
    CoreTerm context type → CoreEnv Base context → type.interpret Base
  | .var x, env => env.get x
  | .app fn arg, env => fn.evaluate env (arg.evaluate env)
  | .lam body, env => fun value => body.evaluate (.cons value env)

/-- Two environments are related when corresponding entries satisfy their type interpretations. -/
inductive CoreEnv.Rel {A : Type u} {B : Type v} (R : A → B → Prop) :
    {context : List CoreType} → CoreEnv A context → CoreEnv B context → Prop where
  /-- Empty environments are related. -/
  | nil : CoreEnv.Rel R .nil .nil
  /-- Related values extend related environments. -/
  | cons : CoreType.rel R type left right → CoreEnv.Rel R leftEnv rightEnv →
      CoreEnv.Rel R (.cons left leftEnv) (.cons right rightEnv)

/-- Operations needed to interpret variables and terms in a relational semantics. -/
structure CoreRelationalKernel (A : Type u) (B : Type v) where
  /-- Relational interpretation of each intrinsic core type. -/
  relation : (type : CoreType) → type.interpret A → type.interpret B → Sort w
  /-- Relational interpretation of semantic environments. -/
  environment : {context : List CoreType} → CoreEnv A context → CoreEnv B context →
    Sort w
  /-- Extract the relation witness for the newest environment entry. -/
  head : ∀ {type : CoreType} {context : List CoreType}
    {left : type.interpret A} {right : type.interpret B}
    {leftEnv : CoreEnv A context} {rightEnv : CoreEnv B context},
    environment (.cons left leftEnv) (.cons right rightEnv) → relation type left right
  /-- Remove the newest entries from a related pair of environments. -/
  tail : ∀ {type : CoreType} {context : List CoreType}
    {left : type.interpret A} {right : type.interpret B}
    {leftEnv : CoreEnv A context} {rightEnv : CoreEnv B context},
    environment (.cons left leftEnv) (.cons right rightEnv) → environment leftEnv rightEnv
  /-- Extend related environments by related values. -/
  cons : ∀ {type : CoreType} {context : List CoreType}
    {left : type.interpret A} {right : type.interpret B}
    {leftEnv : CoreEnv A context} {rightEnv : CoreEnv B context},
    relation type left right → environment leftEnv rightEnv →
      environment (.cons left leftEnv) (.cons right rightEnv)
  /-- Apply related functions to related arguments. -/
  app : ∀ {domain codomain : CoreType}
    {f : (CoreType.arrow domain codomain).interpret A}
    {g : (CoreType.arrow domain codomain).interpret B} {left : domain.interpret A}
    {right : domain.interpret B},
    relation (CoreType.arrow domain codomain) f g → relation domain left right →
      relation codomain (f left) (g right)
  /-- Abstract a pointwise relation witness into a related pair of functions. -/
  lam : ∀ {domain codomain : CoreType}
    {f : (CoreType.arrow domain codomain).interpret A}
    {g : (CoreType.arrow domain codomain).interpret B},
    (∀ left right, relation domain left right → relation codomain (f left) (g right)) →
      relation (CoreType.arrow domain codomain) f g

/-- The relation witness selected by a typed variable in a relational kernel. -/
noncomputable def CoreRelationalKernel.get
    (kernel : CoreRelationalKernel.{u, v, w} A B)
    (var : CoreVar context type) {leftEnv : CoreEnv A context} {rightEnv : CoreEnv B context}
    (henv : kernel.environment leftEnv rightEnv) :
    kernel.relation type (leftEnv.get var) (rightEnv.get var) := by
  induction var with
  | zero =>
      cases leftEnv with
      | cons left leftEnv =>
          cases rightEnv with
          | cons right rightEnv => exact kernel.head henv
  | succ var ih =>
      cases leftEnv with
      | cons left leftEnv =>
          cases rightEnv with
          | cons right rightEnv => exact ih (kernel.tail henv)

/-- The proposition-valued relational kernel generated by a base relation. -/
def CoreRelationalKernel.propositional {A : Type u} {B : Type v} (R : A → B → Prop) :
    CoreRelationalKernel A B where
  relation := CoreType.rel R
  environment := CoreEnv.Rel R
  head := fun henv => by cases henv with | cons head _ => exact head
  tail := fun henv => by cases henv with | cons _ tail => exact tail
  cons := CoreEnv.Rel.cons
  app := fun functionWitness argumentWitness => functionWitness _ _ argumentWitness
  lam := fun bodyWitness => bodyWitness

/-- Related environments give related interpretations to every typed variable. -/
theorem CoreEnv.Rel.get {A : Type u} {B : Type v} {R : A → B → Prop}
    (var : CoreVar context type) {leftEnv : CoreEnv A context} {rightEnv : CoreEnv B context}
    (henv : CoreEnv.Rel R leftEnv rightEnv) :
    CoreType.rel R type (leftEnv.get var) (rightEnv.get var) :=
  (CoreRelationalKernel.propositional R).get var henv

/-- Abstraction witness generated by an arbitrary relational kernel. -/
noncomputable def CoreTerm.abstractionWith
    (kernel : CoreRelationalKernel.{u, v, w} A B)
    (term : CoreTerm context type) {leftEnv : CoreEnv A context} {rightEnv : CoreEnv B context}
    (henv : kernel.environment leftEnv rightEnv) :
    kernel.relation type (term.evaluate leftEnv) (term.evaluate rightEnv) := by
  induction term with
  | var x => exact kernel.get x henv
  | app fn arg ihFn ihArg => exact kernel.app (ihFn henv) (ihArg henv)
  | lam body ih =>
      apply kernel.lam
      intro left right related
      exact ih (kernel.cons related henv)

/-- Abstraction theorem for the proposition-valued intrinsic core calculus. -/
theorem CoreTerm.abstraction {A : Type u} {B : Type v} {R : A → B → Prop}
    (term : CoreTerm context type) {leftEnv : CoreEnv A context} {rightEnv : CoreEnv B context}
    (henv : CoreEnv.Rel R leftEnv rightEnv) :
    CoreType.rel R type (term.evaluate leftEnv) (term.evaluate rightEnv) :=
  term.abstractionWith (CoreRelationalKernel.propositional R) henv

example {A : Type u} {B : Type v} {R : A → B → Prop}
    (term : CoreTerm context type) {leftEnv : CoreEnv A context} {rightEnv : CoreEnv B context}
    (henv : CoreEnv.Rel R leftEnv rightEnv) :
    CoreType.rel R type (term.evaluate leftEnv) (term.evaluate rightEnv) :=
  term.abstraction henv

end DeepWiki.Refine
