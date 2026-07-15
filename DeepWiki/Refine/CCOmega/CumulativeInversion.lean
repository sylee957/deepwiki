import DeepWiki.Refine.CCOmega.PrincipalTyping

/-! # Inversion principles for cumulative conversion

Erasing universe levels turns cumulative conversion into ordinary beta conversion. This proves
agreement of assigned types after level erasure and the kind discrimination needed downstream.
-/

namespace DeepWiki.Refine.DependentCalculus

/-- Replace every universe level in a term by zero. -/
def Term.eraseUniverseLevels : Term n → Term n
  | .sort _ => .sort 0
  | .var index => .var index
  | .app function argument =>
      .app function.eraseUniverseLevels argument.eraseUniverseLevels
  | .lam domain body =>
      .lam domain.eraseUniverseLevels body.eraseUniverseLevels
  | .pi domain codomain =>
      .pi domain.eraseUniverseLevels codomain.eraseUniverseLevels

namespace Term

/-- Universe-level erasure commutes with renaming. -/
theorem eraseUniverseLevels_rename (term : Term source)
    (mapping : Renaming source target) :
    (term.rename mapping).eraseUniverseLevels =
      term.eraseUniverseLevels.rename mapping := by
  induction term generalizing target with
  | sort => rfl
  | var => rfl
  | app function argument functionInduction argumentInduction =>
      simp only [Term.rename, eraseUniverseLevels, functionInduction,
        argumentInduction]
  | lam domain body domainInduction bodyInduction =>
      simp only [Term.rename, eraseUniverseLevels, domainInduction,
        bodyInduction]
  | pi domain codomain domainInduction codomainInduction =>
      simp only [Term.rename, eraseUniverseLevels, domainInduction,
        codomainInduction]

/-- Universe-level erasure commutes with simultaneous substitution. -/
theorem eraseUniverseLevels_substitute (term : Term source)
    (mapping : Substitution source target) :
    (term.substitute mapping).eraseUniverseLevels =
      term.eraseUniverseLevels.substitute
        (fun index => (mapping index).eraseUniverseLevels) := by
  induction term generalizing target with
  | sort => rfl
  | var => rfl
  | app function argument functionInduction argumentInduction =>
      simp only [Term.substitute, eraseUniverseLevels, functionInduction,
        argumentInduction]
  | lam domain body domainInduction bodyInduction =>
      simp only [Term.substitute, eraseUniverseLevels, domainInduction,
        bodyInduction]
      apply congrArg (Term.lam _)
      apply Term.substitute_congr
      funext index
      refine Fin.cases rfl ?_ index
      intro older
      simp only [Substitution.lift_succ, eraseUniverseLevels_rename]
  | pi domain codomain domainInduction codomainInduction =>
      simp only [Term.substitute, eraseUniverseLevels, domainInduction,
        codomainInduction]
      apply congrArg (Term.pi _)
      apply Term.substitute_congr
      funext index
      refine Fin.cases rfl ?_ index
      intro older
      simp only [Substitution.lift_succ, eraseUniverseLevels_rename]

/-- Universe-level erasure commutes with single-variable instantiation. -/
theorem eraseUniverseLevels_instantiate (body : Term (n + 1))
    (argument : Term n) :
    (body.instantiate argument).eraseUniverseLevels =
      body.eraseUniverseLevels.instantiate argument.eraseUniverseLevels := by
  simp only [Term.instantiate, eraseUniverseLevels_substitute]
  apply Term.substitute_congr
  funext index
  exact Fin.cases rfl (fun _ => rfl) index

end Term

namespace BetaStep

/-- Universe-level erasure preserves compatible beta reduction. -/
theorem eraseUniverseLevels {left right : Term n} (step : BetaStep left right) :
    BetaStep left.eraseUniverseLevels right.eraseUniverseLevels := by
  induction step with
  | beta domain body argument =>
      simpa only [Term.eraseUniverseLevels,
        Term.eraseUniverseLevels_instantiate] using
        BetaStep.beta domain.eraseUniverseLevels body.eraseUniverseLevels
          argument.eraseUniverseLevels
  | appFunction _ inductionHypothesis => exact .appFunction inductionHypothesis
  | appArgument _ inductionHypothesis => exact .appArgument inductionHypothesis
  | lamDomain _ inductionHypothesis => exact .lamDomain inductionHypothesis
  | lamBody _ inductionHypothesis => exact .lamBody inductionHypothesis
  | piDomain _ inductionHypothesis => exact .piDomain inductionHypothesis
  | piCodomain _ inductionHypothesis => exact .piCodomain inductionHypothesis

end BetaStep

namespace Convertible

/-- Universe-level erasure preserves beta conversion. -/
theorem eraseUniverseLevels {left right : Term n}
    (conversion : Convertible left right) :
    Convertible left.eraseUniverseLevels right.eraseUniverseLevels := by
  induction conversion with
  | refl => exact .refl _
  | beta step => exact .beta step.eraseUniverseLevels
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ firstInduction secondInduction =>
      exact firstInduction.trans secondInduction

end Convertible

namespace Cumulative

/-- Erasing universe indices turns cumulative conversion into beta conversion. -/
theorem eraseUniverseLevels {left right : Term n}
    (subtype : Cumulative left right) :
    Convertible left.eraseUniverseLevels right.eraseUniverseLevels := by
  induction subtype with
  | conversion equal => exact equal.eraseUniverseLevels
  | sort => exact .refl (.sort 0)
  | pi domainEqual _ codomainInduction =>
      exact domainEqual.eraseUniverseLevels.pi_domain.trans
        codomainInduction.pi_codomain
  | trans _ _ firstInduction secondInduction =>
      exact firstInduction.trans secondInduction

end Cumulative

/-- Cumulative conversion between products exposes convertible domains and cumulative codomains. -/
def CumulativeProductComponentInversion : Prop :=
  ∀ {n : Nat} {domain domain' : Term n} {codomain codomain' : Term (n + 1)},
    Cumulative (.pi domain codomain) (.pi domain' codomain') →
      Cumulative domain' domain ∧ Cumulative codomain codomain'

/-- Types assigned to one term become beta-convertible after erasing universe levels. -/
theorem assignedTypes_eraseUniverseLevels_convertible
    {context : Context n} {term type type' : Term n}
    (termWellTyped : HasType context term type)
    (termWellTyped' : HasType context term type') :
    Convertible type.eraseUniverseLevels type'.eraseUniverseLevels := by
  induction term with
  | sort level =>
      have left := termWellTyped.sort_principal.eraseUniverseLevels
      have right := termWellTyped'.sort_principal.eraseUniverseLevels
      exact left.symm.trans right
  | var index =>
      have left := termWellTyped.var_principal.eraseUniverseLevels
      have right := termWellTyped'.var_principal.eraseUniverseLevels
      exact left.symm.trans right
  | app function argument functionInduction argumentInduction =>
      obtain ⟨domain, codomain, functionWellTyped, _argumentWellTyped,
        resultLower⟩ := termWellTyped.app_principal
      obtain ⟨domain', codomain', functionWellTyped', _argumentWellTyped',
        resultLower'⟩ := termWellTyped'.app_principal
      have functionTypes := functionInduction functionWellTyped functionWellTyped'
      have codomainTypes :
          Convertible codomain.eraseUniverseLevels
            codomain'.eraseUniverseLevels := by
        exact functionTypes.pi_components.2
      have instantiatedTypes :
          Convertible
            (codomain.instantiate argument).eraseUniverseLevels
            (codomain'.instantiate argument).eraseUniverseLevels := by
        rw [Term.eraseUniverseLevels_instantiate,
          Term.eraseUniverseLevels_instantiate]
        exact codomainTypes.substitute
          (Substitution.single argument.eraseUniverseLevels)
      exact resultLower.eraseUniverseLevels.symm.trans
        (instantiatedTypes.trans resultLower'.eraseUniverseLevels)
  | lam domain body domainInduction bodyInduction =>
      obtain ⟨codomain, bodyWellTyped, resultLower⟩ :=
        termWellTyped.lam_principal
      obtain ⟨codomain', bodyWellTyped', resultLower'⟩ :=
        termWellTyped'.lam_principal
      have bodyTypes := bodyInduction bodyWellTyped bodyWellTyped'
      have productTypes :
          Convertible
            (Term.pi domain codomain).eraseUniverseLevels
            (Term.pi domain codomain').eraseUniverseLevels :=
        bodyTypes.pi_codomain
      exact resultLower.eraseUniverseLevels.symm.trans
        (productTypes.trans resultLower'.eraseUniverseLevels)
  | pi domain codomain domainInduction codomainInduction =>
      obtain ⟨level, resultLower⟩ := termWellTyped.pi_principal
      obtain ⟨level', resultLower'⟩ := termWellTyped'.pi_principal
      have left := resultLower.eraseUniverseLevels
      have right := resultLower'.eraseUniverseLevels
      exact left.symm.trans right

example {context : Context n} {term type type' : Term n}
    (termWellTyped : HasType context term type)
    (termWellTyped' : HasType context term type') :
    Convertible type.eraseUniverseLevels type'.eraseUniverseLevels :=
  assignedTypes_eraseUniverseLevels_convertible termWellTyped termWellTyped'

end DeepWiki.Refine.DependentCalculus

namespace DeepWiki.Refine.AnnotatedCalculusConservativity

/-- Assigned kinds are universe sorts whenever the same term has a universe type. -/
theorem assignedKindSortDiscrimination : AssignedKindSortDiscrimination := by
  intro n context term kind kindShape termAtKind termUniverseTyped
  obtain ⟨level, termAtSort⟩ := termUniverseTyped
  have erasedTypes :=
    DependentCalculus.assignedTypes_eraseUniverseLevels_convertible
      termAtSort termAtKind
  cases kindShape with
  | sort kindLevel => exact ⟨kindLevel, rfl⟩
  | pi domain codomainKind =>
      exact erasedTypes.sort_not_pi.elim

example : AssignedKindSortDiscrimination :=
  assignedKindSortDiscrimination

end DeepWiki.Refine.AnnotatedCalculusConservativity
