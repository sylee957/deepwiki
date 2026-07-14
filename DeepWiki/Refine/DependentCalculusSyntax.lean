import Mathlib.Data.Fin.Basic

/-! # Scoped syntax for a predicative dependent calculus

Intrinsically scoped de Bruijn terms support renaming, capture-avoiding substitution, and
well-scoped dependent contexts. -/

namespace DeepWiki.Refine.DependentCalculus

/-- Raw terms with `n` variables in scope. -/
inductive Term : Nat → Type where
  /-- A universe in the predicative hierarchy. -/
  | sort {n : Nat} (level : Nat) : Term n
  /-- A de Bruijn variable known to be in scope. -/
  | var {n : Nat} (index : Fin n) : Term n
  /-- Application of one term to another. -/
  | app {n : Nat} (function argument : Term n) : Term n
  /-- A lambda abstraction with an explicit domain and one bound variable in its body. -/
  | lam {n : Nat} (domain : Term n) (body : Term (n + 1)) : Term n
  /-- A dependent product with one bound variable in its codomain. -/
  | pi {n : Nat} (domain : Term n) (codomain : Term (n + 1)) : Term n
  deriving DecidableEq, Repr

/-- A renaming sends every source variable to a variable in the target scope. -/
abbrev Renaming (source target : Nat) := Fin source → Fin target

namespace Renaming

/-- The identity renaming on a scope. -/
def identity : Renaming n n := id

/-- Compose two renamings from right to left. -/
def comp (outer : Renaming middle target) (inner : Renaming source middle) :
    Renaming source target :=
  fun index => outer (inner index)

/-- The identity renaming is a left identity for composition. -/
@[simp] theorem identity_comp (mapping : Renaming source target) :
    comp identity mapping = mapping := by
  funext index
  rfl

/-- The identity renaming is a right identity for composition. -/
@[simp] theorem comp_identity (mapping : Renaming source target) :
    comp mapping identity = mapping := by
  funext index
  rfl

/-- Composition of renamings is associative. -/
theorem comp_assoc (outer : Renaming third fourth) (middle : Renaming second third)
    (inner : Renaming first second) :
    comp outer (comp middle inner) = comp (comp outer middle) inner := by
  funext index
  rfl

/-- Shift every variable by one to make room for a fresh variable. -/
def shift : Renaming n (n + 1) := Fin.succ

/-- Extend a renaming beneath one binder, fixing the newly bound variable. -/
def lift (rename : Renaming source target) : Renaming (source + 1) (target + 1) :=
  Fin.cases 0 (fun index => Fin.succ (rename index))

/-- Lifting fixes the newest variable. -/
@[simp] theorem lift_zero (rename : Renaming source target) : lift rename 0 = 0 :=
  rfl

/-- Lifting commutes with the successor embedding of older variables. -/
@[simp] theorem lift_succ (rename : Renaming source target) (index : Fin source) :
    lift rename index.succ = (rename index).succ :=
  rfl

/-- Lifting the identity renaming gives the identity renaming. -/
@[simp] theorem lift_identity : lift (identity : Renaming n n) = identity := by
  funext index
  exact Fin.cases rfl (fun _ => rfl) index

/-- Lifting preserves composition of renamings. -/
@[simp] theorem lift_comp (outer : Renaming middle target) (inner : Renaming source middle) :
    lift (comp outer inner) = comp (lift outer) (lift inner) := by
  funext index
  exact Fin.cases rfl (fun _ => rfl) index

end Renaming

namespace Term

/-- Rename every free variable of a term, lifting the renaming beneath binders. -/
def rename (mapping : Renaming source target) : Term source → Term target
  | .sort level => .sort level
  | .var index => .var (mapping index)
  | .app function argument => .app (rename mapping function) (rename mapping argument)
  | .lam domain body => .lam (rename mapping domain) (rename (Renaming.lift mapping) body)
  | .pi domain codomain => .pi (rename mapping domain) (rename (Renaming.lift mapping) codomain)

/-- Extensionally equal renamings act identically on a term. -/
theorem rename_congr {left right : Renaming source target} (equal : left = right)
    (term : Term source) : rename left term = rename right term := by
  cases equal
  rfl

/-- Renaming by the identity leaves a term unchanged. -/
@[simp] theorem rename_identity (term : Term n) :
    rename Renaming.identity term = term := by
  induction term with
  | sort => rfl
  | var => rfl
  | app function argument function_ih argument_ih =>
      simp only [rename, function_ih, argument_ih]
  | lam domain body domain_ih body_ih =>
      simp only [rename, domain_ih, Renaming.lift_identity, body_ih]
  | pi domain codomain domain_ih codomain_ih =>
      simp only [rename, domain_ih, Renaming.lift_identity, codomain_ih]

/-- Successive renamings act as their composition. -/
theorem rename_comp (term : Term source) (inner : Renaming source middle)
    (outer : Renaming middle target) :
    rename outer (rename inner term) = rename (Renaming.comp outer inner) term := by
  induction term generalizing middle target with
  | sort => rfl
  | var => rfl
  | app function argument function_ih argument_ih =>
      simp only [rename, function_ih, argument_ih]
  | lam domain body domain_ih body_ih =>
      simp only [rename, domain_ih, body_ih, Renaming.lift_comp]
  | pi domain codomain domain_ih codomain_ih =>
      simp only [rename, domain_ih, codomain_ih, Renaming.lift_comp]

end Term

/-- A substitution replaces each source variable by a term in the target scope. -/
abbrev Substitution (source target : Nat) := Fin source → Term target

namespace Substitution

/-- Regard a renaming as the variable-only substitution that it induces. -/
def ofRenaming (mapping : Renaming source target) : Substitution source target :=
  fun index => .var (mapping index)

/-- The identity substitution maps every variable to itself. -/
def identity : Substitution n n := ofRenaming Renaming.identity

/-- Extend a substitution beneath one binder without capturing the new variable. -/
def lift (substitute : Substitution source target) :
    Substitution (source + 1) (target + 1) :=
  Fin.cases (.var 0) (fun index => (substitute index).rename Renaming.shift)

/-- Lifting a substitution fixes the newest variable. -/
@[simp] theorem lift_zero (substitute : Substitution source target) : lift substitute 0 = .var 0 :=
  rfl

/-- Lifting weakens the image of every older variable. -/
@[simp] theorem lift_succ (substitute : Substitution source target) (index : Fin source) :
    lift substitute index.succ = (substitute index).rename Renaming.shift :=
  rfl

/-- Lifting a renaming substitution agrees with lifting the renaming. -/
@[simp] theorem lift_ofRenaming (mapping : Renaming source target) :
    lift (ofRenaming mapping) = ofRenaming (Renaming.lift mapping) := by
  funext index
  exact Fin.cases rfl (fun _ => rfl) index

/-- Lifting the identity substitution gives the identity substitution. -/
@[simp] theorem lift_identity : lift (identity : Substitution n n) = identity := by
  simpa only [identity, Renaming.lift_identity] using lift_ofRenaming Renaming.identity

/-- Lifting commutes with precomposition by a renaming. -/
theorem lift_precomp (substitute : Substitution middle target)
    (mapping : Renaming source middle) :
    lift (fun index => substitute (mapping index)) =
      fun index => lift substitute (Renaming.lift mapping index) := by
  funext index
  exact Fin.cases rfl (fun _ => rfl) index

end Substitution

namespace Term

/-- Perform capture-avoiding simultaneous substitution on a term. -/
def substitute (mapping : Substitution source target) : Term source → Term target
  | .sort level => .sort level
  | .var index => mapping index
  | .app function argument =>
      .app (substitute mapping function) (substitute mapping argument)
  | .lam domain body =>
      .lam (substitute mapping domain) (substitute (Substitution.lift mapping) body)
  | .pi domain codomain =>
      .pi (substitute mapping domain) (substitute (Substitution.lift mapping) codomain)

/-- Extensionally equal substitutions act identically on a term. -/
theorem substitute_congr {left right : Substitution source target} (equal : left = right)
    (term : Term source) : substitute left term = substitute right term := by
  cases equal
  rfl

/-- Substituting variables along a renaming is the same as renaming. -/
theorem substitute_ofRenaming (term : Term source) (mapping : Renaming source target) :
    substitute (Substitution.ofRenaming mapping) term = rename mapping term := by
  induction term generalizing target with
  | sort => rfl
  | var => rfl
  | app function argument function_ih argument_ih =>
      simp only [substitute, rename, function_ih, argument_ih]
  | lam domain body domain_ih body_ih =>
      simp only [substitute, rename, domain_ih, Substitution.lift_ofRenaming, body_ih]
  | pi domain codomain domain_ih codomain_ih =>
      simp only [substitute, rename, domain_ih, Substitution.lift_ofRenaming, codomain_ih]

/-- Substitution by the identity leaves a term unchanged. -/
@[simp] theorem substitute_identity (term : Term n) :
    substitute Substitution.identity term = term := by
  simpa only [Substitution.identity, rename_identity] using
    substitute_ofRenaming term Renaming.identity

/-- Substitution after renaming precomposes the substitution by that renaming. -/
theorem substitute_rename (term : Term source) (mapping : Renaming source middle)
    (substitute : Substitution middle target) :
    (rename mapping term).substitute substitute =
      term.substitute (fun index => substitute (mapping index)) := by
  induction term generalizing middle target with
  | sort => rfl
  | var => rfl
  | app function argument function_ih argument_ih =>
      simp only [rename, Term.substitute, function_ih, argument_ih]
  | lam domain body domain_ih body_ih =>
      simp only [rename, Term.substitute, domain_ih, body_ih]
      apply congrArg (Term.lam _)
      apply substitute_congr
      exact (Substitution.lift_precomp substitute mapping).symm
  | pi domain codomain domain_ih codomain_ih =>
      simp only [rename, Term.substitute, domain_ih, codomain_ih]
      apply congrArg (Term.pi _)
      apply substitute_congr
      exact (Substitution.lift_precomp substitute mapping).symm

end Term

namespace Substitution

/-- Lifting commutes with postcomposition by a renaming. -/
theorem lift_postrename (substitute : Substitution source middle)
    (mapping : Renaming middle target) :
    lift (fun index => (substitute index).rename mapping) =
      fun index => (lift substitute index).rename (Renaming.lift mapping) := by
  funext index
  refine Fin.cases rfl ?_ index
  intro older
  simp only [lift_succ, Term.rename_comp]
  apply Term.rename_congr
  funext element
  simp only [Renaming.comp, Renaming.shift, Renaming.lift_succ]

end Substitution

namespace Term

/-- Renaming after substitution postcomposes every substituted term by the renaming. -/
theorem rename_substitute (term : Term source) (substitute : Substitution source middle)
    (mapping : Renaming middle target) :
    (term.substitute substitute).rename mapping =
      term.substitute (fun index => (substitute index).rename mapping) := by
  induction term generalizing middle target with
  | sort => rfl
  | var => rfl
  | app function argument function_ih argument_ih =>
      simp only [Term.substitute, rename, function_ih, argument_ih]
  | lam domain body domain_ih body_ih =>
      simp only [Term.substitute, rename, domain_ih, body_ih]
      apply congrArg (Term.lam _)
      apply substitute_congr
      exact (Substitution.lift_postrename substitute mapping).symm
  | pi domain codomain domain_ih codomain_ih =>
      simp only [Term.substitute, rename, domain_ih, codomain_ih]
      apply congrArg (Term.pi _)
      apply substitute_congr
      exact (Substitution.lift_postrename substitute mapping).symm

end Term

namespace Substitution

/-- Compose substitutions by substituting the outer mapping into each inner image. -/
def comp (outer : Substitution middle target) (inner : Substitution source middle) :
    Substitution source target :=
  fun index => (inner index).substitute outer

/-- The identity substitution is a left identity for composition. -/
@[simp] theorem identity_comp (mapping : Substitution source target) :
    comp identity mapping = mapping := by
  funext index
  exact Term.substitute_identity (mapping index)

/-- The identity substitution is a right identity for composition. -/
@[simp] theorem comp_identity (mapping : Substitution source target) :
    comp mapping identity = mapping := by
  funext index
  rfl

/-- Lifting preserves composition of substitutions. -/
theorem lift_comp (outer : Substitution middle target) (inner : Substitution source middle) :
    lift (comp outer inner) = comp (lift outer) (lift inner) := by
  funext index
  refine Fin.cases rfl ?_ index
  intro older
  simp only [lift_succ, comp, Term.substitute_rename, Term.rename_substitute]
  apply Term.substitute_congr
  funext element
  simp only [Renaming.shift, lift_succ]

end Substitution

namespace Term

/-- Successive substitutions act as their composition. -/
theorem substitute_comp (term : Term source) (inner : Substitution source middle)
    (outer : Substitution middle target) :
    (term.substitute inner).substitute outer =
      term.substitute (Substitution.comp outer inner) := by
  induction term generalizing middle target with
  | sort => rfl
  | var => rfl
  | app function argument function_ih argument_ih =>
      simp only [substitute, function_ih, argument_ih]
  | lam domain body domain_ih body_ih =>
      simp only [substitute, domain_ih, body_ih, Substitution.lift_comp]
  | pi domain codomain domain_ih codomain_ih =>
      simp only [substitute, domain_ih, codomain_ih, Substitution.lift_comp]

end Term

namespace Substitution

/-- Composition of substitutions is associative. -/
theorem comp_assoc (outer : Substitution third fourth)
    (middle : Substitution second third) (inner : Substitution first second) :
    comp outer (comp middle inner) = comp (comp outer middle) inner := by
  funext index
  exact Term.substitute_comp (inner index) middle outer

end Substitution

/-- A dependent context whose newest type may mention all preceding variables. -/
inductive Context : Nat → Type where
  /-- The empty dependent context. -/
  | empty : Context 0
  /-- Extend a context by a type well-scoped in the preceding context. -/
  | extend {n : Nat} (context : Context n) (type : Term n) : Context (n + 1)
  deriving DecidableEq, Repr

namespace Context

/-- Look up a variable's type and weaken it into the full ambient context. -/
def lookup : (context : Context n) → Fin n → Term n
  | .empty, index => Fin.elim0 index
  | .extend context type, index =>
      Fin.cases (type.rename Renaming.shift)
        (fun older => (context.lookup older).rename Renaming.shift) index

/-- The newest variable has the weakened type used to extend its context. -/
@[simp] theorem lookup_zero (context : Context n) (type : Term n) :
    (extend context type).lookup 0 = type.rename Renaming.shift :=
  rfl

/-- Looking up an older variable weakens its previous type. -/
@[simp] theorem lookup_succ (context : Context n) (type : Term n) (index : Fin n) :
    (extend context type).lookup index.succ = (context.lookup index).rename Renaming.shift :=
  rfl

end Context

example : Term 0 := .sort 0

example (domain : Term n) (codomain : Term (n + 1)) : Term n := .pi domain codomain

example (term : Term n) : term.rename Renaming.identity = term :=
  Term.rename_identity term

example (term : Term source) (inner : Renaming source middle)
    (outer : Renaming middle target) :
    (term.rename inner).rename outer = term.rename (Renaming.comp outer inner) :=
  Term.rename_comp term inner outer

example (term : Term source) (inner : Substitution source middle)
    (outer : Substitution middle target) :
    (term.substitute inner).substitute outer =
      term.substitute (Substitution.comp outer inner) :=
  Term.substitute_comp term inner outer

example (context : Context n) (type : Term n) : Context (n + 1) :=
  .extend context type

end DeepWiki.Refine.DependentCalculus
