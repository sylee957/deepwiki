import DeepWiki.Refine.Dependent
import DeepWiki.Refine.RelationStructure

/-! # A core parametricity calculus

An intrinsically typed lambda calculus gives a compact, executable statement of the abstraction
theorem. Its relation environments are the semantic counterpart of parametricity contexts. -/

namespace DeepWiki.Refine

universe u v

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

/-- Relational interpretation of a core type from a relation on its open base type. -/
def CoreType.rel {A : Type u} {B : Type v} (R : A → B → Prop) :
    (type : CoreType) → type.interpret A → type.interpret B → Prop
  | .base => R
  | .arrow domain codomain => fun f g =>
      ∀ a b, domain.rel R a b → codomain.rel R (f a) (g b)

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

/-- Related environments give related interpretations to every typed variable. -/
theorem CoreEnv.Rel.get {A : Type u} {B : Type v} {R : A → B → Prop}
    (var : CoreVar context type) {leftEnv : CoreEnv A context} {rightEnv : CoreEnv B context}
    (henv : CoreEnv.Rel R leftEnv rightEnv) :
    CoreType.rel R type (leftEnv.get var) (rightEnv.get var) := by
  induction var with
  | zero => cases henv with | cons head _ => exact head
  | succ var ih => cases henv with | cons _ tail => exact ih tail

/-- Abstraction theorem for the intrinsic core calculus. -/
theorem CoreTerm.abstraction {A : Type u} {B : Type v} {R : A → B → Prop}
    (term : CoreTerm context type) {leftEnv : CoreEnv A context} {rightEnv : CoreEnv B context}
    (henv : CoreEnv.Rel R leftEnv rightEnv) :
    CoreType.rel R type (term.evaluate leftEnv) (term.evaluate rightEnv) := by
  induction term with
  | var x => exact henv.get x
  | app fn arg ihFn ihArg => exact ihFn henv _ _ (ihArg henv)
  | lam body ih =>
      intro left right hrel
      exact ih (leftEnv := .cons left leftEnv) (rightEnv := .cons right rightEnv)
        (.cons hrel henv)

example {A : Type u} {B : Type v} {R : A → B → Prop}
    (term : CoreTerm context type) {leftEnv : CoreEnv A context} {rightEnv : CoreEnv B context}
    (henv : CoreEnv.Rel R leftEnv rightEnv) :
    CoreType.rel R type (term.evaluate leftEnv) (term.evaluate rightEnv) :=
  term.abstraction henv

end DeepWiki.Refine
