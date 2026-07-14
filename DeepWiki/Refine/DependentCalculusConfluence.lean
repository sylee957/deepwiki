import DeepWiki.Refine.DependentCalculusTyping
import Mathlib.Logic.Relation

/-! # Confluence of beta conversion

Parallel beta reduction gives the triangle property needed to distinguish beta-normal universe
sorts and to audit conversion claims in the annotation-erasure argument.
-/

namespace DeepWiki.Refine.DependentCalculus

/-- A beta expansion of `Sort 0` whose argument does not match its displayed domain. -/
def sortZeroExpansion : Term 0 :=
  .app (.lam (.sort 0) (.sort 0)) (.sort 0)

/-- Symmetric untyped beta conversion identifies `Sort 0` with `sortZeroExpansion`. -/
theorem sortZero_convertible_sortZeroExpansion :
    Convertible (.sort 0 : Term 0) sortZeroExpansion := by
  exact (Convertible.beta (BetaStep.beta (.sort 0) (.sort 0) (.sort 0))).symm

/-- Parallel beta reduction contracts any compatible collection of redexes in one step. -/
inductive Parallel : Term n → Term n → Prop where
  /-- A variable reduces in parallel to itself. -/
  | var (index : Fin n) : Parallel (.var index) (.var index)
  /-- A universe sort reduces in parallel to itself. -/
  | sort (level : Nat) : Parallel (.sort level) (.sort level)
  /-- Parallel reduction is compatible with application. -/
  | app {function function' argument argument' : Term n}
      (functionStep : Parallel function function')
      (argumentStep : Parallel argument argument') :
      Parallel (.app function argument) (.app function' argument')
  /-- Parallel reduction is compatible with lambda abstraction. -/
  | lam {domain domain' : Term n} {body body' : Term (n + 1)}
      (domainStep : Parallel domain domain') (bodyStep : Parallel body body') :
      Parallel (.lam domain body) (.lam domain' body')
  /-- Parallel reduction is compatible with dependent products. -/
  | pi {domain domain' : Term n} {codomain codomain' : Term (n + 1)}
      (domainStep : Parallel domain domain') (codomainStep : Parallel codomain codomain') :
      Parallel (.pi domain codomain) (.pi domain' codomain')
  /-- A beta redex contracts after its domain, body, and argument reduce in parallel. -/
  | beta {domain domain' argument argument' : Term n}
      {body body' : Term (n + 1)}
      (domainStep : Parallel domain domain') (bodyStep : Parallel body body')
      (argumentStep : Parallel argument argument') :
      Parallel (.app (.lam domain body) argument) (body'.instantiate argument')

namespace Parallel

/-- Every term reduces in parallel to itself. -/
theorem refl (term : Term n) : Parallel term term := by
  induction term with
  | sort level => exact .sort level
  | var index => exact .var index
  | app _ _ functionInduction argumentInduction =>
      exact .app functionInduction argumentInduction
  | lam _ _ domainInduction bodyInduction => exact .lam domainInduction bodyInduction
  | pi _ _ domainInduction codomainInduction => exact .pi domainInduction codomainInduction

/-- Renaming preserves parallel beta reduction. -/
theorem rename {left right : Term source} (step : Parallel left right)
    (mapping : Renaming source target) :
    Parallel (left.rename mapping) (right.rename mapping) := by
  induction step generalizing target with
  | var index => exact .var (mapping index)
  | sort level => exact .sort level
  | app _ _ functionInduction argumentInduction =>
      exact .app (functionInduction mapping) (argumentInduction mapping)
  | lam _ _ domainInduction bodyInduction =>
      exact .lam (domainInduction mapping) (bodyInduction (Renaming.lift mapping))
  | pi _ _ domainInduction codomainInduction =>
      exact .pi (domainInduction mapping) (codomainInduction (Renaming.lift mapping))
  | beta _ _ _ domainInduction bodyInduction argumentInduction =>
      simpa only [Term.rename, Term.rename_instantiate] using
        Parallel.beta (domainInduction mapping)
          (bodyInduction (Renaming.lift mapping)) (argumentInduction mapping)

/-- Pointwise parallel substitutions preserve parallel beta reduction. -/
theorem substitute {left right : Term source} (step : Parallel left right)
    (mapping mapping' : Substitution source target)
    (mappingStep : ∀ index, Parallel (mapping index) (mapping' index)) :
    Parallel (left.substitute mapping) (right.substitute mapping') := by
  induction step generalizing target with
  | var index => exact mappingStep index
  | sort level => exact .sort level
  | app _ _ functionInduction argumentInduction =>
      exact .app (functionInduction mapping mapping' mappingStep)
        (argumentInduction mapping mapping' mappingStep)
  | lam _ _ domainInduction bodyInduction =>
      apply Parallel.lam (domainInduction mapping mapping' mappingStep)
      apply bodyInduction (Substitution.lift mapping) (Substitution.lift mapping')
      intro index
      refine Fin.cases (.var 0) ?_ index
      intro older
      exact (mappingStep older).rename Renaming.shift
  | pi _ _ domainInduction codomainInduction =>
      apply Parallel.pi (domainInduction mapping mapping' mappingStep)
      apply codomainInduction (Substitution.lift mapping) (Substitution.lift mapping')
      intro index
      refine Fin.cases (.var 0) ?_ index
      intro older
      exact (mappingStep older).rename Renaming.shift
  | beta _ _ _ domainInduction bodyInduction argumentInduction =>
      have domainStep := domainInduction mapping mapping' mappingStep
      have bodyStep := bodyInduction (Substitution.lift mapping) (Substitution.lift mapping')
        (fun index => Fin.cases (.var 0)
          (fun older => (mappingStep older).rename Renaming.shift) index)
      have argumentStep := argumentInduction mapping mapping' mappingStep
      simpa only [Term.substitute, Term.substitute_instantiate] using
        Parallel.beta domainStep bodyStep argumentStep

/-- Parallel reduction is compatible with single-variable instantiation. -/
theorem instantiate {body body' : Term (n + 1)} {argument argument' : Term n}
    (bodyStep : Parallel body body') (argumentStep : Parallel argument argument') :
    Parallel (body.instantiate argument) (body'.instantiate argument') := by
  apply bodyStep.substitute (Substitution.single argument) (Substitution.single argument')
  intro index
  refine Fin.cases argumentStep ?_ index
  exact fun older => .var older

end Parallel

/-- Complete development contracts every redex visible after recursively developing a term. -/
def completeDevelopment : Term n → Term n
  | .sort level => .sort level
  | .var index => .var index
  | .app (.lam _ body) argument =>
      (completeDevelopment body).instantiate (completeDevelopment argument)
  | .app function argument =>
      .app (completeDevelopment function) (completeDevelopment argument)
  | .lam domain body => .lam (completeDevelopment domain) (completeDevelopment body)
  | .pi domain codomain => .pi (completeDevelopment domain) (completeDevelopment codomain)

namespace Parallel

/-- Every parallel reduct reduces in parallel to the complete development of its source. -/
theorem triangle {source target : Term n} (step : Parallel source target) :
    Parallel target (completeDevelopment source) := by
  induction step with
  | var index => exact .var index
  | sort level => exact .sort level
  | app functionStep argumentStep functionInduction argumentInduction =>
      cases functionStep with
      | var => exact .app functionInduction argumentInduction
      | sort => exact .app functionInduction argumentInduction
      | app => exact .app functionInduction argumentInduction
      | lam =>
          cases functionInduction with
          | lam domainInduction bodyInduction =>
              exact .beta domainInduction bodyInduction argumentInduction
      | pi => exact .app functionInduction argumentInduction
      | beta => exact .app functionInduction argumentInduction
  | lam _ _ domainInduction bodyInduction =>
      exact .lam domainInduction bodyInduction
  | pi _ _ domainInduction codomainInduction =>
      exact .pi domainInduction codomainInduction
  | beta _ _ _ _ bodyInduction argumentInduction =>
      exact bodyInduction.instantiate argumentInduction

/-- Parallel reduction has the diamond property. -/
theorem diamond {source left right : Term n} (leftStep : Parallel source left)
    (rightStep : Parallel source right) :
    ∃ common, Parallel left common ∧ Parallel right common :=
  ⟨completeDevelopment source, leftStep.triangle, rightStep.triangle⟩

/-- A universe sort has no nontrivial parallel reduct. -/
theorem sort_target_eq {level : Nat} {target : Term n}
    (step : Parallel (.sort level) target) : target = .sort level := by
  cases step
  rfl

/-- A parallel reduct of a product is again a product. -/
theorem pi_target {domain : Term n} {codomain : Term (n + 1)} {target : Term n}
    (step : Parallel (.pi domain codomain) target) :
    ∃ domain' codomain', target = .pi domain' codomain' ∧
      Parallel domain domain' ∧ Parallel codomain codomain' := by
  cases step with
  | pi domainStep codomainStep =>
      exact ⟨_, _, rfl, domainStep, codomainStep⟩

end Parallel

namespace BetaStep

/-- Every compatible one-step beta reduction is a parallel reduction. -/
theorem parallel {left right : Term n} (step : BetaStep left right) : Parallel left right := by
  induction step with
  | beta domain body argument =>
      exact .beta (Parallel.refl domain) (Parallel.refl body) (Parallel.refl argument)
  | appFunction _ inductionHypothesis =>
      exact .app inductionHypothesis (Parallel.refl _)
  | appArgument _ inductionHypothesis =>
      exact .app (Parallel.refl _) inductionHypothesis
  | lamDomain _ inductionHypothesis =>
      exact .lam inductionHypothesis (Parallel.refl _)
  | lamBody _ inductionHypothesis =>
      exact .lam (Parallel.refl _) inductionHypothesis
  | piDomain _ inductionHypothesis =>
      exact .pi inductionHypothesis (Parallel.refl _)
  | piCodomain _ inductionHypothesis =>
      exact .pi (Parallel.refl _) inductionHypothesis

end BetaStep

/-- Joins of reflexive-transitive parallel reduction form an equivalence relation. -/
theorem parallelJoin_equivalence (n : Nat) :
    Equivalence
      (Relation.Join (Relation.ReflTransGen (@Parallel n))) := by
  apply Relation.equivalence_join_reflTransGen
  intro source left right leftStep rightStep
  obtain ⟨common, leftCommon, rightCommon⟩ := leftStep.diamond rightStep
  exact ⟨common, .single leftCommon, .single rightCommon⟩

namespace Convertible

/-- Beta-convertible terms have a common reflexive-transitive parallel reduct. -/
theorem parallelJoin {left right : Term n} (conversion : Convertible left right) :
    Relation.Join (Relation.ReflTransGen (@Parallel n)) left right := by
  let equivalence := parallelJoin_equivalence n
  induction conversion with
  | refl term => exact equivalence.refl term
  | beta step =>
      exact ⟨_, Relation.ReflTransGen.single step.parallel, Relation.ReflTransGen.refl⟩
  | symm _ inductionHypothesis => exact equivalence.symm inductionHypothesis
  | trans _ _ firstInduction secondInduction =>
      exact equivalence.trans firstInduction secondInduction

end Convertible

/-- A reflexive-transitive parallel reduction starting at a sort ends at that sort. -/
theorem parallelStar_sort_target_eq {level : Nat} {target : Term n}
    (steps : Relation.ReflTransGen (@Parallel n) (.sort level) target) :
    target = .sort level := by
  induction steps with
  | refl => rfl
  | tail step lastStep inductionHypothesis =>
      subst inductionHypothesis
      exact lastStep.sort_target_eq

/-- A reflexive-transitive parallel reduct of a product is again a product. -/
theorem parallelStar_pi_target {domain : Term n} {codomain : Term (n + 1)}
    {target : Term n}
    (steps : Relation.ReflTransGen (@Parallel n) (.pi domain codomain) target) :
    ∃ domain' codomain', target = .pi domain' codomain' := by
  induction steps with
  | refl => exact ⟨domain, codomain, rfl⟩
  | tail _ lastStep inductionHypothesis =>
      obtain ⟨domain', codomain', rfl⟩ := inductionHypothesis
      obtain ⟨domain'', codomain'', rfl, _, _⟩ := lastStep.pi_target
      exact ⟨domain'', codomain'', rfl⟩

/-- Beta-convertible universe sorts have the same level. -/
theorem Convertible.sort_level_eq {lower upper : Nat}
    (conversion : Convertible (.sort lower : Term n) (.sort upper)) : lower = upper := by
  obtain ⟨common, lowerSteps, upperSteps⟩ := conversion.parallelJoin
  have lowerShape := parallelStar_sort_target_eq lowerSteps
  have upperShape := parallelStar_sort_target_eq upperSteps
  rw [lowerShape] at upperShape
  injection upperShape

/-- Universe sorts at distinct levels are not beta-convertible. -/
theorem Convertible.sort_not_convertible_of_ne {lower upper : Nat}
    (different : lower ≠ upper) :
    ¬ Convertible (.sort lower : Term n) (.sort upper) :=
  fun conversion => different conversion.sort_level_eq

/-- No universe sort is beta-convertible to a dependent product. -/
theorem Convertible.sort_not_pi {level : Nat} {domain : Term n}
    {codomain : Term (n + 1)} :
    ¬ Convertible (.sort level) (.pi domain codomain) := by
  intro conversion
  obtain ⟨common, sortSteps, productSteps⟩ := conversion.parallelJoin
  have sortShape := parallelStar_sort_target_eq sortSteps
  obtain ⟨domain', codomain', productShape⟩ := parallelStar_pi_target productSteps
  rw [sortShape] at productShape
  contradiction

/-- A syntactic kind beta-convertible to a sort is that same sort. -/
theorem Convertible.sort_eq_of_right_isKind {level : Nat} {right : Term n}
    (conversion : Convertible (.sort level) right) (rightKind : IsKind right) :
    right = .sort level := by
  cases rightKind with
  | sort rightLevel =>
      have levelsEqual := conversion.sort_level_eq
      subst levelsEqual
      rfl
  | pi domain codomainKind =>
      exact conversion.sort_not_pi.elim

/-- Beta conversion preserves whether a syntactic kind is a sort or a product. -/
theorem Convertible.kind_isSort_iff {left right : Term n}
    (conversion : Convertible left right) (leftKind : IsKind left)
    (rightKind : IsKind right) :
    (∃ level, left = .sort level) ↔ ∃ level, right = .sort level := by
  constructor
  · rintro ⟨level, rfl⟩
    exact ⟨level, conversion.sort_eq_of_right_isKind rightKind⟩
  · rintro ⟨level, rfl⟩
    exact ⟨level, conversion.symm.sort_eq_of_right_isKind leftKind⟩

example :
    ¬ Convertible (.sort 0 : Term 0) (.sort 1) :=
  Convertible.sort_not_convertible_of_ne Nat.zero_ne_one

end DeepWiki.Refine.DependentCalculus
