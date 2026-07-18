import DeepWiki.Refine.Parametricity.Univalent.Translation

/-! # Typing for univalent parametricity

The extended `CCω` judgment types the concrete package primitives and derives the universe
equation required by the univalent abstraction theorem. -/

namespace DeepWiki.Refine.DependentCalculus.UnivalentParametricity

/-- Extend by an original endpoint, a primed endpoint, and their projected relation witness. -/
def relationalExtend (context : Context n) (left right package : Term n) : Context (n + 3) :=
  .extend
    (.extend (.extend context left)
      (right.rename DependentCalculus.Renaming.shift))
    (Term.relatedDomain package)

namespace Term

/-- Embedding a core term commutes with one-variable instantiation. -/
theorem ofCore_instantiate (body : CoreTerm (n + 1)) (argument : CoreTerm n) :
    ofCore (body.instantiate argument) =
      (ofCore body).instantiate (ofCore argument) := by
  simp only [DependentCalculus.Term.instantiate,
    instantiate, ofCore_substitute]
  apply substitute_congr
  funext index
  exact Fin.cases rfl (fun _ => rfl) index

end Term

/-- One compatible computation step in the univalent-parametricity object calculus. -/
inductive BetaStep : Term n → Term n → Prop where
  /-- Contract a beta redex by single-variable instantiation. -/
  | beta (domain : Term n) (body : Term (n + 1)) (argument : Term n) :
      BetaStep (.app (.lam domain body) argument) (body.instantiate argument)
  /-- Projecting `p□` computes to the package family. -/
  | universeProjection (level : Nat) :
      BetaStep (Term.rel (.universePackage level : Term n)) (.packageFamily level)
  /-- Projecting `pΠ` computes to the dependent respectful relation. -/
  | dependentProductProjection
      (leftDomain rightDomain : Term n)
      (leftCodomain rightCodomain : Term (n + 1))
      (domainPackage : Term n) (codomainPackage : Term (n + 3)) :
      BetaStep
        (Term.rel (.dependentProductPackage leftDomain rightDomain
          leftCodomain rightCodomain domainPackage codomainPackage))
        (Term.dependentProductRelation leftDomain rightDomain
          leftCodomain rightCodomain domainPackage codomainPackage)
  /-- Reduce the left domain carried by a dependent-product package. -/
  | dependentProductLeftDomain
      {leftDomain leftDomain' rightDomain : Term n}
      {leftCodomain rightCodomain : Term (n + 1)}
      {domainPackage : Term n} {codomainPackage : Term (n + 3)}
      (step : BetaStep leftDomain leftDomain') :
      BetaStep
        (.dependentProductPackage leftDomain rightDomain leftCodomain rightCodomain
          domainPackage codomainPackage)
        (.dependentProductPackage leftDomain' rightDomain leftCodomain rightCodomain
          domainPackage codomainPackage)
  /-- Reduce the right domain carried by a dependent-product package. -/
  | dependentProductRightDomain
      {leftDomain rightDomain rightDomain' : Term n}
      {leftCodomain rightCodomain : Term (n + 1)}
      {domainPackage : Term n} {codomainPackage : Term (n + 3)}
      (step : BetaStep rightDomain rightDomain') :
      BetaStep
        (.dependentProductPackage leftDomain rightDomain leftCodomain rightCodomain
          domainPackage codomainPackage)
        (.dependentProductPackage leftDomain rightDomain' leftCodomain rightCodomain
          domainPackage codomainPackage)
  /-- Reduce the left codomain carried by a dependent-product package. -/
  | dependentProductLeftCodomain
      {leftDomain rightDomain : Term n}
      {leftCodomain leftCodomain' rightCodomain : Term (n + 1)}
      {domainPackage : Term n} {codomainPackage : Term (n + 3)}
      (step : BetaStep leftCodomain leftCodomain') :
      BetaStep
        (.dependentProductPackage leftDomain rightDomain leftCodomain rightCodomain
          domainPackage codomainPackage)
        (.dependentProductPackage leftDomain rightDomain leftCodomain' rightCodomain
          domainPackage codomainPackage)
  /-- Reduce the right codomain carried by a dependent-product package. -/
  | dependentProductRightCodomain
      {leftDomain rightDomain : Term n}
      {leftCodomain rightCodomain rightCodomain' : Term (n + 1)}
      {domainPackage : Term n} {codomainPackage : Term (n + 3)}
      (step : BetaStep rightCodomain rightCodomain') :
      BetaStep
        (.dependentProductPackage leftDomain rightDomain leftCodomain rightCodomain
          domainPackage codomainPackage)
        (.dependentProductPackage leftDomain rightDomain leftCodomain rightCodomain'
          domainPackage codomainPackage)
  /-- Reduce the domain package carried by a dependent-product package. -/
  | dependentProductDomainPackage
      {leftDomain rightDomain : Term n}
      {leftCodomain rightCodomain : Term (n + 1)}
      {domainPackage domainPackage' : Term n}
      {codomainPackage : Term (n + 3)}
      (step : BetaStep domainPackage domainPackage') :
      BetaStep
        (.dependentProductPackage leftDomain rightDomain leftCodomain rightCodomain
          domainPackage codomainPackage)
        (.dependentProductPackage leftDomain rightDomain leftCodomain rightCodomain
          domainPackage' codomainPackage)
  /-- Reduce the codomain package carried by a dependent-product package. -/
  | dependentProductCodomainPackage
      {leftDomain rightDomain : Term n}
      {leftCodomain rightCodomain : Term (n + 1)}
      {domainPackage : Term n}
      {codomainPackage codomainPackage' : Term (n + 3)}
      (step : BetaStep codomainPackage codomainPackage') :
      BetaStep
        (.dependentProductPackage leftDomain rightDomain leftCodomain rightCodomain
          domainPackage codomainPackage)
        (.dependentProductPackage leftDomain rightDomain leftCodomain rightCodomain
          domainPackage codomainPackage')
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
  /-- Reduce beneath a relation projection. -/
  | relationProjection {package package' : Term n}
      (step : BetaStep package package') :
      BetaStep (Term.rel package) (Term.rel package')

namespace BetaStep

/-- Renaming preserves one-step computation in the extended calculus. -/
theorem rename {left right : Term source} (step : BetaStep left right)
    (mapping : Renaming source target) :
    BetaStep (left.rename mapping) (right.rename mapping) := by
  induction step generalizing target with
  | beta domain body argument =>
      simpa only [Term.rename, Term.rename_instantiate] using
        BetaStep.beta (domain.rename mapping)
          (body.rename (DependentCalculus.Renaming.lift mapping))
          (argument.rename mapping)
  | universeProjection level => exact .universeProjection level
  | dependentProductProjection leftDomain rightDomain leftCodomain rightCodomain
      domainPackage codomainPackage =>
      simpa only [Term.rel, Term.rename, dependentProductRelation_rename] using
        BetaStep.dependentProductProjection
          (leftDomain.rename mapping) (rightDomain.rename mapping)
          (leftCodomain.rename
            (DependentCalculus.Renaming.lift mapping))
          (rightCodomain.rename
            (DependentCalculus.Renaming.lift mapping))
          (domainPackage.rename mapping)
          (codomainPackage.rename (Renaming.liftBy mapping 3))
  | dependentProductLeftDomain _ inductionHypothesis =>
      exact .dependentProductLeftDomain (inductionHypothesis mapping)
  | dependentProductRightDomain _ inductionHypothesis =>
      exact .dependentProductRightDomain (inductionHypothesis mapping)
  | dependentProductLeftCodomain _ inductionHypothesis =>
      exact .dependentProductLeftCodomain
        (inductionHypothesis
          (DependentCalculus.Renaming.lift mapping))
  | dependentProductRightCodomain _ inductionHypothesis =>
      exact .dependentProductRightCodomain
        (inductionHypothesis
          (DependentCalculus.Renaming.lift mapping))
  | dependentProductDomainPackage _ inductionHypothesis =>
      exact .dependentProductDomainPackage (inductionHypothesis mapping)
  | dependentProductCodomainPackage _ inductionHypothesis =>
      exact .dependentProductCodomainPackage
        (inductionHypothesis (Renaming.liftBy mapping 3))
  | appFunction _ inductionHypothesis =>
      exact .appFunction (inductionHypothesis mapping)
  | appArgument _ inductionHypothesis =>
      exact .appArgument (inductionHypothesis mapping)
  | lamDomain _ inductionHypothesis =>
      exact .lamDomain (inductionHypothesis mapping)
  | lamBody _ inductionHypothesis =>
      exact .lamBody
        (inductionHypothesis
          (DependentCalculus.Renaming.lift mapping))
  | piDomain _ inductionHypothesis =>
      exact .piDomain (inductionHypothesis mapping)
  | piCodomain _ inductionHypothesis =>
      exact .piCodomain
        (inductionHypothesis
          (DependentCalculus.Renaming.lift mapping))
  | relationProjection _ inductionHypothesis =>
      exact .relationProjection (inductionHypothesis mapping)

/-- Simultaneous substitution preserves one-step computation in the extended calculus. -/
theorem substitute {left right : Term source} (step : BetaStep left right)
    (mapping : Substitution source target) :
    BetaStep (left.substitute mapping) (right.substitute mapping) := by
  induction step generalizing target with
  | beta domain body argument =>
      simpa only [Term.substitute, Term.substitute_instantiate] using
        BetaStep.beta (domain.substitute mapping)
          (body.substitute (Substitution.lift mapping))
          (argument.substitute mapping)
  | universeProjection level => exact .universeProjection level
  | dependentProductProjection leftDomain rightDomain leftCodomain rightCodomain
      domainPackage codomainPackage =>
      simpa only [Term.rel, Term.substitute, dependentProductRelation_substitute] using
        BetaStep.dependentProductProjection
          (leftDomain.substitute mapping) (rightDomain.substitute mapping)
          (leftCodomain.substitute (Substitution.lift mapping))
          (rightCodomain.substitute (Substitution.lift mapping))
          (domainPackage.substitute mapping)
          (codomainPackage.substitute (Substitution.liftBy mapping 3))
  | dependentProductLeftDomain _ inductionHypothesis =>
      exact .dependentProductLeftDomain (inductionHypothesis mapping)
  | dependentProductRightDomain _ inductionHypothesis =>
      exact .dependentProductRightDomain (inductionHypothesis mapping)
  | dependentProductLeftCodomain _ inductionHypothesis =>
      exact .dependentProductLeftCodomain
        (inductionHypothesis (Substitution.lift mapping))
  | dependentProductRightCodomain _ inductionHypothesis =>
      exact .dependentProductRightCodomain
        (inductionHypothesis (Substitution.lift mapping))
  | dependentProductDomainPackage _ inductionHypothesis =>
      exact .dependentProductDomainPackage (inductionHypothesis mapping)
  | dependentProductCodomainPackage _ inductionHypothesis =>
      exact .dependentProductCodomainPackage
        (inductionHypothesis (Substitution.liftBy mapping 3))
  | appFunction _ inductionHypothesis =>
      exact .appFunction (inductionHypothesis mapping)
  | appArgument _ inductionHypothesis =>
      exact .appArgument (inductionHypothesis mapping)
  | lamDomain _ inductionHypothesis =>
      exact .lamDomain (inductionHypothesis mapping)
  | lamBody _ inductionHypothesis =>
      exact .lamBody (inductionHypothesis (Substitution.lift mapping))
  | piDomain _ inductionHypothesis =>
      exact .piDomain (inductionHypothesis mapping)
  | piCodomain _ inductionHypothesis =>
      exact .piCodomain (inductionHypothesis (Substitution.lift mapping))
  | relationProjection _ inductionHypothesis =>
      exact .relationProjection (inductionHypothesis mapping)

/-- Embedding core syntax preserves one-step core beta reduction. -/
theorem ofCore {left right : CoreTerm n}
    (step : DependentCalculus.BetaStep left right) :
    BetaStep (Term.ofCore left) (Term.ofCore right) := by
  induction step with
  | beta domain body argument =>
      simpa only [Term.ofCore, Term.ofCore_instantiate] using
        BetaStep.beta (Term.ofCore domain) (Term.ofCore body)
          (Term.ofCore argument)
  | appFunction _ inductionHypothesis => exact .appFunction inductionHypothesis
  | appArgument _ inductionHypothesis => exact .appArgument inductionHypothesis
  | lamDomain _ inductionHypothesis => exact .lamDomain inductionHypothesis
  | lamBody _ inductionHypothesis => exact .lamBody inductionHypothesis
  | piDomain _ inductionHypothesis => exact .piDomain inductionHypothesis
  | piCodomain _ inductionHypothesis => exact .piCodomain inductionHypothesis

/-- Original endpoint copies preserve core beta steps. -/
theorem original {left right : CoreTerm n}
    (step : DependentCalculus.BetaStep left right) :
    BetaStep (UnivalentParametricity.original left)
      (UnivalentParametricity.original right) := by
  unfold UnivalentParametricity.original RawParametricity.original
  exact BetaStep.ofCore (step.rename (RawParametricity.originalRenaming n))

/-- Primed endpoint copies preserve core beta steps. -/
theorem primed {left right : CoreTerm n}
    (step : DependentCalculus.BetaStep left right) :
    BetaStep (UnivalentParametricity.primed left)
      (UnivalentParametricity.primed right) := by
  unfold UnivalentParametricity.primed RawParametricity.primed
  exact BetaStep.ofCore (step.rename (RawParametricity.primedRenaming n))

end BetaStep

/-- Definitional conversion generated by the extended computation rules. -/
inductive Convertible : Term n → Term n → Prop where
  /-- Every term is definitionally convertible to itself. -/
  | refl (term : Term n) : Convertible term term
  /-- Every computation step is a definitional conversion. -/
  | beta {left right : Term n} (step : BetaStep left right) : Convertible left right
  /-- Definitional conversion is symmetric. -/
  | symm {left right : Term n} (conversion : Convertible left right) :
      Convertible right left
  /-- Definitional conversion is transitive. -/
  | trans {first second third : Term n}
      (firstSecond : Convertible first second) (secondThird : Convertible second third) :
      Convertible first third

namespace Convertible

/-- Renaming preserves definitional conversion. -/
theorem rename {left right : Term source} (conversion : Convertible left right)
    (mapping : Renaming source target) :
    Convertible (left.rename mapping) (right.rename mapping) := by
  induction conversion with
  | refl => exact .refl _
  | beta step => exact .beta (step.rename mapping)
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ firstInduction secondInduction =>
      exact firstInduction.trans secondInduction

/-- Simultaneous substitution preserves definitional conversion. -/
theorem substitute {left right : Term source} (conversion : Convertible left right)
    (mapping : Substitution source target) :
    Convertible (left.substitute mapping) (right.substitute mapping) := by
  induction conversion with
  | refl => exact .refl _
  | beta step => exact .beta (step.substitute mapping)
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ firstInduction secondInduction =>
      exact firstInduction.trans secondInduction

/-- Embedding core syntax preserves core definitional conversion. -/
theorem ofCore {left right : CoreTerm n}
    (conversion : DependentCalculus.Convertible left right) :
    Convertible (Term.ofCore left) (Term.ofCore right) := by
  induction conversion with
  | refl => exact .refl _
  | beta step => exact .beta (BetaStep.ofCore step)
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ firstInduction secondInduction =>
      exact firstInduction.trans secondInduction

/-- Convertible functions remain convertible after applying a fixed argument. -/
theorem appFunction {function function' argument : Term n}
    (conversion : Convertible function function') :
    Convertible (.app function argument) (.app function' argument) := by
  induction conversion with
  | refl => exact .refl _
  | beta step => exact .beta (.appFunction step)
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ firstInduction secondInduction =>
      exact firstInduction.trans secondInduction

/-- Convertible arguments remain convertible under a fixed function. -/
theorem appArgument {function argument argument' : Term n}
    (conversion : Convertible argument argument') :
    Convertible (.app function argument) (.app function argument') := by
  induction conversion with
  | refl => exact .refl _
  | beta step => exact .beta (.appArgument step)
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ firstInduction secondInduction =>
      exact firstInduction.trans secondInduction

/-- Conversion is congruent in both sides of application. -/
theorem appBoth {function function' argument argument' : Term n}
    (functionConversion : Convertible function function')
    (argumentConversion : Convertible argument argument') :
    Convertible (.app function argument) (.app function' argument') :=
  functionConversion.appFunction.trans argumentConversion.appArgument

/-- Conversion is congruent in lambda domains. -/
theorem lamDomain {domain domain' : Term n} {body : Term (n + 1)}
    (conversion : Convertible domain domain') :
    Convertible (.lam domain body) (.lam domain' body) := by
  induction conversion with
  | refl => exact .refl _
  | beta step => exact .beta (.lamDomain step)
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ firstInduction secondInduction =>
      exact firstInduction.trans secondInduction

/-- Conversion is congruent in lambda bodies. -/
theorem lamBody {domain : Term n} {body body' : Term (n + 1)}
    (conversion : Convertible body body') :
    Convertible (.lam domain body) (.lam domain body') := by
  induction conversion with
  | refl => exact .refl _
  | beta step => exact .beta (.lamBody step)
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ firstInduction secondInduction =>
      exact firstInduction.trans secondInduction

/-- Conversion is congruent in both lambda components. -/
theorem lamBoth {domain domain' : Term n} {body body' : Term (n + 1)}
    (domainConversion : Convertible domain domain')
    (bodyConversion : Convertible body body') :
    Convertible (.lam domain body) (.lam domain' body') :=
  domainConversion.lamDomain.trans bodyConversion.lamBody

/-- Conversion is congruent in dependent-product domains. -/
theorem piDomain {domain domain' : Term n} {codomain : Term (n + 1)}
    (conversion : Convertible domain domain') :
    Convertible (.pi domain codomain) (.pi domain' codomain) := by
  induction conversion with
  | refl => exact .refl _
  | beta step => exact .beta (.piDomain step)
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ firstInduction secondInduction =>
      exact firstInduction.trans secondInduction

/-- Conversion is congruent in dependent-product codomains. -/
theorem piCodomain {domain : Term n} {codomain codomain' : Term (n + 1)}
    (conversion : Convertible codomain codomain') :
    Convertible (.pi domain codomain) (.pi domain codomain') := by
  induction conversion with
  | refl => exact .refl _
  | beta step => exact .beta (.piCodomain step)
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ firstInduction secondInduction =>
      exact firstInduction.trans secondInduction

/-- Conversion is congruent in both dependent-product components. -/
theorem piBoth {domain domain' : Term n} {codomain codomain' : Term (n + 1)}
    (domainConversion : Convertible domain domain')
    (codomainConversion : Convertible codomain codomain') :
    Convertible (.pi domain codomain) (.pi domain' codomain') :=
  domainConversion.piDomain.trans codomainConversion.piCodomain

/-- Conversion is congruent under relation projection. -/
theorem relationProjection {package package' : Term n}
    (conversion : Convertible package package') :
    Convertible (Term.rel package) (Term.rel package') := by
  induction conversion with
  | refl => exact .refl _
  | beta step => exact .beta (.relationProjection step)
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ firstInduction secondInduction =>
      exact firstInduction.trans secondInduction

/-- Conversion is congruent in a binary relation application. -/
theorem relationApplication
    {relation relation' left left' right right' : Term n}
    (relationConversion : Convertible relation relation')
    (leftConversion : Convertible left left')
    (rightConversion : Convertible right right') :
    Convertible (Term.relationApplication relation left right)
      (Term.relationApplication relation' left' right') :=
  (relationConversion.appBoth leftConversion).appBoth rightConversion

/-- Conversion is preserved by repeated weakening. -/
theorem weakenBy {left right : Term n} (conversion : Convertible left right)
    (amount : Nat) :
    Convertible (left.weakenBy amount) (right.weakenBy amount) := by
  induction amount with
  | zero => exact conversion
  | succ amount inductionHypothesis =>
      exact inductionHypothesis.rename
        DependentCalculus.Renaming.shift

/-- Conversion is congruent in a translated relation-binder domain. -/
theorem relatedDomain {package package' : Term n}
    (conversion : Convertible package package') :
    Convertible (Term.relatedDomain package) (Term.relatedDomain package') := by
  unfold Term.relatedDomain Term.relationApplication
  exact ((conversion.weakenBy 2).relationProjection.appBoth (.refl _)).appBoth
    (.refl _)

/-- Conversion is congruent in the left domain stored by `pΠ`. -/
theorem dependentProductLeftDomain
    {leftDomain leftDomain' rightDomain : Term n}
    {leftCodomain rightCodomain : Term (n + 1)}
    {domainPackage : Term n} {codomainPackage : Term (n + 3)}
    (conversion : Convertible leftDomain leftDomain') :
    Convertible
      (.dependentProductPackage leftDomain rightDomain leftCodomain rightCodomain
        domainPackage codomainPackage)
      (.dependentProductPackage leftDomain' rightDomain leftCodomain rightCodomain
        domainPackage codomainPackage) := by
  induction conversion with
  | refl => exact .refl _
  | beta step => exact .beta (.dependentProductLeftDomain step)
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ firstInduction secondInduction =>
      exact firstInduction.trans secondInduction

/-- Conversion is congruent in the right domain stored by `pΠ`. -/
theorem dependentProductRightDomain
    {leftDomain rightDomain rightDomain' : Term n}
    {leftCodomain rightCodomain : Term (n + 1)}
    {domainPackage : Term n} {codomainPackage : Term (n + 3)}
    (conversion : Convertible rightDomain rightDomain') :
    Convertible
      (.dependentProductPackage leftDomain rightDomain leftCodomain rightCodomain
        domainPackage codomainPackage)
      (.dependentProductPackage leftDomain rightDomain' leftCodomain rightCodomain
        domainPackage codomainPackage) := by
  induction conversion with
  | refl => exact .refl _
  | beta step => exact .beta (.dependentProductRightDomain step)
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ firstInduction secondInduction =>
      exact firstInduction.trans secondInduction

/-- Conversion is congruent in the left codomain stored by `pΠ`. -/
theorem dependentProductLeftCodomain
    {leftDomain rightDomain : Term n}
    {leftCodomain leftCodomain' rightCodomain : Term (n + 1)}
    {domainPackage : Term n} {codomainPackage : Term (n + 3)}
    (conversion : Convertible leftCodomain leftCodomain') :
    Convertible
      (.dependentProductPackage leftDomain rightDomain leftCodomain rightCodomain
        domainPackage codomainPackage)
      (.dependentProductPackage leftDomain rightDomain leftCodomain' rightCodomain
        domainPackage codomainPackage) := by
  induction conversion with
  | refl => exact .refl _
  | beta step => exact .beta (.dependentProductLeftCodomain step)
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ firstInduction secondInduction =>
      exact firstInduction.trans secondInduction

/-- Conversion is congruent in the right codomain stored by `pΠ`. -/
theorem dependentProductRightCodomain
    {leftDomain rightDomain : Term n}
    {leftCodomain rightCodomain rightCodomain' : Term (n + 1)}
    {domainPackage : Term n} {codomainPackage : Term (n + 3)}
    (conversion : Convertible rightCodomain rightCodomain') :
    Convertible
      (.dependentProductPackage leftDomain rightDomain leftCodomain rightCodomain
        domainPackage codomainPackage)
      (.dependentProductPackage leftDomain rightDomain leftCodomain rightCodomain'
        domainPackage codomainPackage) := by
  induction conversion with
  | refl => exact .refl _
  | beta step => exact .beta (.dependentProductRightCodomain step)
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ firstInduction secondInduction =>
      exact firstInduction.trans secondInduction

/-- Conversion is congruent in the domain package stored by `pΠ`. -/
theorem dependentProductDomainPackage
    {leftDomain rightDomain : Term n}
    {leftCodomain rightCodomain : Term (n + 1)}
    {domainPackage domainPackage' : Term n} {codomainPackage : Term (n + 3)}
    (conversion : Convertible domainPackage domainPackage') :
    Convertible
      (.dependentProductPackage leftDomain rightDomain leftCodomain rightCodomain
        domainPackage codomainPackage)
      (.dependentProductPackage leftDomain rightDomain leftCodomain rightCodomain
        domainPackage' codomainPackage) := by
  induction conversion with
  | refl => exact .refl _
  | beta step => exact .beta (.dependentProductDomainPackage step)
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ firstInduction secondInduction =>
      exact firstInduction.trans secondInduction

/-- Conversion is congruent in the codomain package stored by `pΠ`. -/
theorem dependentProductCodomainPackage
    {leftDomain rightDomain : Term n}
    {leftCodomain rightCodomain : Term (n + 1)}
    {domainPackage : Term n} {codomainPackage codomainPackage' : Term (n + 3)}
    (conversion : Convertible codomainPackage codomainPackage') :
    Convertible
      (.dependentProductPackage leftDomain rightDomain leftCodomain rightCodomain
        domainPackage codomainPackage)
      (.dependentProductPackage leftDomain rightDomain leftCodomain rightCodomain
        domainPackage codomainPackage') := by
  induction conversion with
  | refl => exact .refl _
  | beta step => exact .beta (.dependentProductCodomainPackage step)
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ firstInduction secondInduction =>
      exact firstInduction.trans secondInduction

/-- Conversion is congruent in all fields stored by `pΠ`. -/
theorem dependentProductPackage
    {leftDomain leftDomain' rightDomain rightDomain' : Term n}
    {leftCodomain leftCodomain' rightCodomain rightCodomain' : Term (n + 1)}
    {domainPackage domainPackage' : Term n}
    {codomainPackage codomainPackage' : Term (n + 3)}
    (leftDomainConversion : Convertible leftDomain leftDomain')
    (rightDomainConversion : Convertible rightDomain rightDomain')
    (leftCodomainConversion : Convertible leftCodomain leftCodomain')
    (rightCodomainConversion : Convertible rightCodomain rightCodomain')
    (domainPackageConversion : Convertible domainPackage domainPackage')
    (codomainPackageConversion : Convertible codomainPackage codomainPackage') :
    Convertible
      (.dependentProductPackage leftDomain rightDomain leftCodomain rightCodomain
        domainPackage codomainPackage)
      (.dependentProductPackage leftDomain' rightDomain' leftCodomain' rightCodomain'
        domainPackage' codomainPackage') :=
  leftDomainConversion.dependentProductLeftDomain.trans
    (rightDomainConversion.dependentProductRightDomain.trans
      (leftCodomainConversion.dependentProductLeftCodomain.trans
        (rightCodomainConversion.dependentProductRightCodomain.trans
          (domainPackageConversion.dependentProductDomainPackage.trans
            codomainPackageConversion.dependentProductCodomainPackage))))

/-- Original endpoint copies preserve core definitional conversion. -/
theorem original {left right : CoreTerm n}
    (conversion : DependentCalculus.Convertible left right) :
    Convertible (UnivalentParametricity.original left)
      (UnivalentParametricity.original right) := by
  unfold UnivalentParametricity.original RawParametricity.original
  exact Convertible.ofCore
    (conversion.rename (RawParametricity.originalRenaming n))

/-- Primed endpoint copies preserve core definitional conversion. -/
theorem primed {left right : CoreTerm n}
    (conversion : DependentCalculus.Convertible left right) :
    Convertible (UnivalentParametricity.primed left)
      (UnivalentParametricity.primed right) := by
  unfold UnivalentParametricity.primed RawParametricity.primed
  exact Convertible.ofCore
    (conversion.rename (RawParametricity.primedRenaming n))

/-- Original codomain embeddings preserve core definitional conversion. -/
theorem originalCodomain {left right : CoreTerm (n + 1)}
    (conversion : DependentCalculus.Convertible left right) :
    Convertible (UnivalentParametricity.originalCodomain left)
      (UnivalentParametricity.originalCodomain right) := by
  unfold UnivalentParametricity.originalCodomain
  exact Convertible.ofCore
    (conversion.rename
      (DependentCalculus.Renaming.lift
        (RawParametricity.originalRenaming n)))

/-- Primed codomain embeddings preserve core definitional conversion. -/
theorem primedCodomain {left right : CoreTerm (n + 1)}
    (conversion : DependentCalculus.Convertible left right) :
    Convertible (UnivalentParametricity.primedCodomain left)
      (UnivalentParametricity.primedCodomain right) := by
  unfold UnivalentParametricity.primedCodomain
  exact Convertible.ofCore
    (conversion.rename
      (DependentCalculus.Renaming.lift
        (RawParametricity.primedRenaming n)))

end Convertible

/-- Cumulative conversion for extended predicative universes and dependent products. -/
inductive Cumulative : Term n → Term n → Prop where
  /-- Definitional conversion is cumulative conversion. -/
  | conversion {left right : Term n} (equal : Convertible left right) :
      Cumulative left right
  /-- A universe embeds into every universe at least as high. -/
  | sort {lower upper : Nat} (level : lower ≤ upper) :
      Cumulative (.sort lower : Term n) (.sort upper)
  /-- Package-family applications respect the predicative universe preorder. -/
  | packageType {lower upper : Nat} (level : lower ≤ upper) (left right : Term n) :
      Cumulative (Term.packageType lower left right)
        (Term.packageType upper left right)
  /-- Products are convertible in the domain and cumulative in the codomain. -/
  | pi {domain domain' : Term n} {codomain codomain' : Term (n + 1)}
      (domainEqual : Convertible domain domain')
      (codomainCumulative : Cumulative codomain codomain') :
      Cumulative (.pi domain codomain) (.pi domain' codomain')
  /-- Cumulative conversion is transitive. -/
  | trans {first second third : Term n}
      (firstSecond : Cumulative first second) (secondThird : Cumulative second third) :
      Cumulative first third

namespace Cumulative

/-- Renaming preserves cumulative conversion. -/
theorem rename {left right : Term source} (subtype : Cumulative left right)
    (mapping : Renaming source target) :
    Cumulative (left.rename mapping) (right.rename mapping) := by
  induction subtype generalizing target with
  | conversion equal => exact .conversion (equal.rename mapping)
  | sort level => exact .sort level
  | packageType level left right =>
      simpa only [Term.packageType_rename] using
        Cumulative.packageType level (left.rename mapping) (right.rename mapping)
  | pi domainEqual _ codomainInduction =>
      exact .pi (domainEqual.rename mapping)
        (codomainInduction
          (DependentCalculus.Renaming.lift mapping))
  | trans _ _ firstInduction secondInduction =>
      exact (firstInduction mapping).trans (secondInduction mapping)

/-- Simultaneous substitution preserves cumulative conversion. -/
theorem substitute {left right : Term source} (subtype : Cumulative left right)
    (mapping : Substitution source target) :
    Cumulative (left.substitute mapping) (right.substitute mapping) := by
  induction subtype generalizing target with
  | conversion equal => exact .conversion (equal.substitute mapping)
  | sort level => exact .sort level
  | packageType level left right =>
      simpa only [Term.packageType_substitute] using
        Cumulative.packageType level (left.substitute mapping)
          (right.substitute mapping)
  | pi domainEqual _ codomainInduction =>
      exact .pi (domainEqual.substitute mapping)
        (codomainInduction (Substitution.lift mapping))
  | trans _ _ firstInduction secondInduction =>
      exact (firstInduction mapping).trans (secondInduction mapping)

/-- Embedding core syntax preserves core cumulative conversion. -/
theorem ofCore {left right : CoreTerm n}
    (subtype : DependentCalculus.Cumulative left right) :
    Cumulative (Term.ofCore left) (Term.ofCore right) := by
  induction subtype with
  | conversion equal => exact .conversion (Convertible.ofCore equal)
  | sort level => exact .sort level
  | pi domainEqual _ codomainInduction =>
      exact .pi (Convertible.ofCore domainEqual) codomainInduction
  | trans _ _ firstInduction secondInduction =>
      exact .trans firstInduction secondInduction

end Cumulative

mutual

  /-- A univalent-parametricity context is well formed when every entry is universe-typed. -/
  inductive WellFormed : Context n → Prop where
    /-- The empty context is well formed. -/
    | empty : WellFormed .empty
    /-- Extend a well-formed context by a universe-typed entry. -/
    | extend {context : Context n} {type : Term n} {level : Nat}
        (contextWellFormed : WellFormed context)
        (typeWellTyped : HasType context type (.sort level)) :
        WellFormed (.extend context type)

  /-- Typing for core terms and the concrete univalent relation-package primitives. -/
  inductive HasType : Context n → Term n → Term n → Prop where
    /-- Every universe is typed by its immediate successor. -/
    | sort {context : Context n} (contextWellFormed : WellFormed context) (level : Nat) :
        HasType context (.sort level) (.sort (level + 1))
    /-- A variable has its dependently weakened lookup type. -/
    | var {context : Context n} (contextWellFormed : WellFormed context) (index : Fin n) :
        HasType context (.var index) (context.lookup index)
    /-- Dependent application instantiates the displayed codomain. -/
    | app {context : Context n} {function argument domain : Term n}
        {codomain : Term (n + 1)}
        (functionWellTyped : HasType context function (.pi domain codomain))
        (argumentWellTyped : HasType context argument domain) :
        HasType context (.app function argument) (codomain.instantiate argument)
    /-- A lambda has a dependent-product type. -/
    | lam {context : Context n} {domain : Term n} {body codomain : Term (n + 1)}
        {domainLevel : Nat}
        (domainWellTyped : HasType context domain (.sort domainLevel))
        (bodyWellTyped : HasType (.extend context domain) body codomain) :
        HasType context (.lam domain body) (.pi domain codomain)
    /-- A dependent product lies in the maximum domain/codomain universe. -/
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
    /-- The package family relates two types in the same universe. -/
    | packageFamily {context : Context n} (contextWellFormed : WellFormed context)
        (level : Nat) :
        HasType context (.packageFamily level)
          (Term.relationType (level + 1) (.sort level) (.sort level))
    /-- `p□` inhabits the next-level package relation on two copies of its universe. -/
    | universePackage {context : Context n} (contextWellFormed : WellFormed context)
        (level : Nat) :
        HasType context (.universePackage level)
          (Term.packageType (level + 1) (.sort level) (.sort level))
    /-- Projecting a package yields a binary relation on its endpoints. -/
    | relationProjection {context : Context n} {package left right : Term n}
        {level : Nat}
        (leftWellTyped : HasType context left (.sort level))
        (rightWellTyped : HasType context right (.sort level))
        (packageWellTyped : HasType context package (Term.packageType level left right)) :
        HasType context (Term.rel package) (Term.relationType level left right)
    /-- `pΠ` packages the dependent respectful relation and its univalent structure. -/
    | dependentProductPackage {context : Context n}
        {leftDomain rightDomain : Term n}
        {leftCodomain rightCodomain : Term (n + 1)}
        {domainPackage : Term n} {codomainPackage : Term (n + 3)}
        {domainLevel codomainLevel : Nat}
        (leftDomainWellTyped : HasType context leftDomain (.sort domainLevel))
        (rightDomainWellTyped : HasType context rightDomain (.sort domainLevel))
        (leftCodomainWellTyped :
          HasType (.extend context leftDomain) leftCodomain (.sort codomainLevel))
        (rightCodomainWellTyped :
          HasType (.extend context rightDomain) rightCodomain (.sort codomainLevel))
        (domainPackageWellTyped :
          HasType context domainPackage
            (Term.packageType domainLevel leftDomain rightDomain))
        (codomainPackageWellTyped :
          HasType (relationalExtend context leftDomain rightDomain domainPackage)
            codomainPackage
            (Term.packageType codomainLevel
              (leftCodomain.rename originalBinderRenaming)
              (rightCodomain.rename primedBinderRenaming))) :
        HasType context
          (.dependentProductPackage leftDomain rightDomain leftCodomain rightCodomain
            domainPackage codomainPackage)
          (Term.packageType (max domainLevel codomainLevel)
            (.pi leftDomain leftCodomain) (.pi rightDomain rightCodomain))

end

/-- A typed context renaming preserves each source lookup after renaming. -/
structure TypedRenaming (source : Context sourceSize) (target : Context targetSize)
    (mapping : Renaming sourceSize targetSize) : Prop where
  /-- The target context is well formed. -/
  targetWellFormed : WellFormed target
  /-- Every mapped variable has the renamed source lookup type. -/
  lookup_eq (index : Fin sourceSize) :
    target.lookup (mapping index) = (source.lookup index).rename mapping

namespace TypedRenaming

/-- The identity renaming is typed on every well-formed context. -/
theorem identity {context : Context n} (contextWellFormed : WellFormed context) :
    TypedRenaming context context
      DependentCalculus.Renaming.identity where
  targetWellFormed := contextWellFormed
  lookup_eq index := (Term.rename_identity (context.lookup index)).symm

/-- Typed context renamings compose. -/
theorem comp {first : Context firstSize} {second : Context secondSize}
    {third : Context thirdSize} {inner : Renaming firstSize secondSize}
    {outer : Renaming secondSize thirdSize}
    (outerTyped : TypedRenaming second third outer)
    (innerTyped : TypedRenaming first second inner) :
    TypedRenaming first third
      (DependentCalculus.Renaming.comp outer inner) where
  targetWellFormed := outerTyped.targetWellFormed
  lookup_eq index := by
    calc
      third.lookup
          (DependentCalculus.Renaming.comp outer inner index) =
          (second.lookup (inner index)).rename outer := by
            simpa only [DependentCalculus.Renaming.comp] using
              outerTyped.lookup_eq (inner index)
      _ = ((first.lookup index).rename inner).rename outer := by
            rw [innerTyped.lookup_eq index]
      _ = (first.lookup index).rename
          (DependentCalculus.Renaming.comp outer inner) :=
            Term.rename_comp (first.lookup index) inner outer

/-- Extend a typed renaming beneath matching dependent context extensions. -/
theorem lift {source : Context sourceSize} {target : Context targetSize}
    {mapping : Renaming sourceSize targetSize} {domain : Term sourceSize}
    {level : Nat} (mappingTyped : TypedRenaming source target mapping)
    (domainWellTyped : HasType target (domain.rename mapping) (.sort level)) :
    TypedRenaming (.extend source domain) (.extend target (domain.rename mapping))
      (DependentCalculus.Renaming.lift mapping) where
  targetWellFormed := .extend mappingTyped.targetWellFormed domainWellTyped
  lookup_eq index := by
    refine Fin.cases ?_ ?_ index
    · simp only [DependentCalculus.Renaming.lift_zero,
        Context.lookup_zero, Term.rename_comp]
      apply Term.rename_congr
      funext older
      rfl
    · intro older
      simp only [DependentCalculus.Renaming.lift_succ,
        Context.lookup_succ]
      rw [mappingTyped.lookup_eq older, Term.rename_comp, Term.rename_comp]
      apply Term.rename_congr
      funext index
      rfl

/-- Weakening into a well-formed extension is a typed renaming. -/
theorem shift {context : Context n} {domain : Term n}
    (extendedWellFormed : WellFormed (.extend context domain)) :
    TypedRenaming context (.extend context domain)
      DependentCalculus.Renaming.shift where
  targetWellFormed := extendedWellFormed
  lookup_eq _index := rfl

end TypedRenaming

namespace HasType

/-- Every typing derivation contains a well-formedness derivation for its context. -/
theorem contextWellFormed {context : Context n} {term type : Term n}
    (termWellTyped : HasType context term type) : WellFormed context := by
  refine HasType.rec
    (motive_1 := fun context _ => WellFormed context)
    (motive_2 := fun context _ _ _ => WellFormed context)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ termWellTyped
  · exact WellFormed.empty
  · intro _ context type _ contextWellFormed typeWellTyped _ _
    exact WellFormed.extend contextWellFormed typeWellTyped
  all_goals intros
  all_goals assumption

/-- The inversion predicate used to expose dependent-product formation premises. -/
private def piComponentsConclusion (context : Context n) (term : Term n) : Prop :=
  match term with
  | .pi domain codomain =>
      ∃ domainLevel codomainLevel,
        HasType context domain (.sort domainLevel) ∧
          HasType (.extend context domain) codomain (.sort codomainLevel)
  | _ => True

/-- The inversion predicate used to expose application typing premises. -/
private def appComponentsConclusion (context : Context n) (term : Term n) : Prop :=
  match term with
  | .app function argument =>
      ∃ domain codomain,
        HasType context function (.pi domain codomain) ∧
          HasType context argument domain
  | _ => True

/-- The inversion predicate used to expose relation-projection premises. -/
private def relationProjectionComponentsConclusion
    (context : Context n) (term : Term n) : Prop :=
  match term with
  | .relationProjection package =>
      ∃ level left right,
        HasType context left (.sort level) ∧
          HasType context right (.sort level) ∧
            HasType context package (Term.packageType level left right)
  | _ => True

/-- The inversion predicate used to expose dependent-product package premises. -/
private def dependentProductPackageComponentsConclusion
    (context : Context n) (term : Term n) : Prop :=
  match term with
  | .dependentProductPackage leftDomain rightDomain leftCodomain rightCodomain
      domainPackage codomainPackage =>
      ∃ domainLevel codomainLevel,
        HasType context leftDomain (.sort domainLevel) ∧
        HasType context rightDomain (.sort domainLevel) ∧
        HasType (.extend context leftDomain) leftCodomain (.sort codomainLevel) ∧
        HasType (.extend context rightDomain) rightCodomain (.sort codomainLevel) ∧
        HasType context domainPackage
          (Term.packageType domainLevel leftDomain rightDomain) ∧
        HasType (relationalExtend context leftDomain rightDomain domainPackage)
          codomainPackage
          (Term.packageType codomainLevel
            (leftCodomain.rename originalBinderRenaming)
            (rightCodomain.rename primedBinderRenaming))
  | _ => True

/-- Typing a product term exposes universe typings for its domain and codomain. -/
theorem piComponents {context : Context n} {domain : Term n}
    {codomain : Term (n + 1)} {type : Term n} :
    HasType context (.pi domain codomain) type →
      ∃ domainLevel codomainLevel,
        HasType context domain (.sort domainLevel) ∧
          HasType (.extend context domain) codomain (.sort codomainLevel) := by
  intro productWellTyped
  refine HasType.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := fun context term _ _ => piComponentsConclusion context term)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ productWellTyped
  · trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intro _ _ _ _ domainLevel codomainLevel domainWellTyped codomainWellTyped _ _
    exact ⟨domainLevel, codomainLevel, domainWellTyped, codomainWellTyped⟩
  · intros; assumption
  · intros; assumption
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial

/-- Typing an application exposes dependent-function and argument typings. -/
theorem appComponents {context : Context n} {function argument type : Term n} :
    HasType context (.app function argument) type →
      ∃ domain codomain,
        HasType context function (.pi domain codomain) ∧
          HasType context argument domain := by
  intro applicationWellTyped
  refine HasType.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := fun context term _ _ => appComponentsConclusion context term)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ applicationWellTyped
  · trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intro _ _ function argument domain codomain functionWellTyped argumentWellTyped _ _
    exact ⟨domain, codomain, functionWellTyped, argumentWellTyped⟩
  · intros; trivial
  · intros; trivial
  · intros; assumption
  · intros; assumption
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial

/-- Typing a relation projection exposes its package and endpoint premises. -/
theorem relationProjectionComponents
    {context : Context n} {package type : Term n} :
    HasType context (.relationProjection package) type →
      ∃ level left right,
        HasType context left (.sort level) ∧
          HasType context right (.sort level) ∧
            HasType context package (Term.packageType level left right) := by
  intro projectionWellTyped
  refine HasType.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := fun context term _ _ =>
      relationProjectionComponentsConclusion context term)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ projectionWellTyped
  · trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; assumption
  · intros; assumption
  · intros; trivial
  · intros; trivial
  · intro _ _ _ _ _ level leftWellTyped rightWellTyped packageWellTyped _ _ _
    exact ⟨level, _, _, leftWellTyped, rightWellTyped, packageWellTyped⟩
  · intros; trivial

/-- Typing `pΠ` exposes all endpoint and package premises. -/
theorem dependentProductPackageComponents
    {context : Context n}
    {leftDomain rightDomain : Term n}
    {leftCodomain rightCodomain : Term (n + 1)}
    {domainPackage : Term n} {codomainPackage : Term (n + 3)} {type : Term n} :
    HasType context
      (.dependentProductPackage leftDomain rightDomain leftCodomain rightCodomain
        domainPackage codomainPackage) type →
      ∃ domainLevel codomainLevel,
        HasType context leftDomain (.sort domainLevel) ∧
        HasType context rightDomain (.sort domainLevel) ∧
        HasType (.extend context leftDomain) leftCodomain (.sort codomainLevel) ∧
        HasType (.extend context rightDomain) rightCodomain (.sort codomainLevel) ∧
        HasType context domainPackage
          (Term.packageType domainLevel leftDomain rightDomain) ∧
        HasType (relationalExtend context leftDomain rightDomain domainPackage)
          codomainPackage
          (Term.packageType codomainLevel
            (leftCodomain.rename originalBinderRenaming)
            (rightCodomain.rename primedBinderRenaming)) := by
  intro packageWellTyped
  refine HasType.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := fun context term _ _ =>
      dependentProductPackageComponentsConclusion context term)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ packageWellTyped
  · trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; assumption
  · intros; assumption
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intro _ _ leftDomain rightDomain leftCodomain rightCodomain
      domainPackage codomainPackage domainLevel codomainLevel
      leftDomainWellTyped rightDomainWellTyped leftCodomainWellTyped
      rightCodomainWellTyped domainPackageWellTyped codomainPackageWellTyped
      _ _ _ _ _ _
    exact ⟨domainLevel, codomainLevel, leftDomainWellTyped,
      rightDomainWellTyped, leftCodomainWellTyped, rightCodomainWellTyped,
      domainPackageWellTyped, codomainPackageWellTyped⟩

/-- Typed context renaming preserves extended dependent typing. -/
theorem rename {source : Context sourceSize} {term type : Term sourceSize}
    (termWellTyped : HasType source term type) :
    ∀ {targetSize} {target : Context targetSize}
      {mapping : Renaming sourceSize targetSize},
      TypedRenaming source target mapping →
        HasType target (term.rename mapping) (type.rename mapping) := by
  refine HasType.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := fun {n} context term type _ =>
      ∀ {targetSize} {target : Context targetSize}
        {mapping : Renaming n targetSize},
        TypedRenaming context target mapping →
          HasType target (term.rename mapping) (type.rename mapping))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ termWellTyped
  · trivial
  · intros
    trivial
  · intro _ _ _ level _ _ _ mapping mappingTyped
    exact .sort mappingTyped.targetWellFormed level
  · intro _ _ _ index _ _ _ mapping mappingTyped
    have variableWellTyped := HasType.var mappingTyped.targetWellFormed (mapping index)
    rw [mappingTyped.lookup_eq index] at variableWellTyped
    exact variableWellTyped
  · intro _ _ _ _ _ _ _ _ functionInduction argumentInduction
      _ _ _ mappingTyped
    have applicationWellTyped := HasType.app
      (functionInduction mappingTyped) (argumentInduction mappingTyped)
    simpa only [Term.rename, Term.rename_instantiate] using applicationWellTyped
  · intro _ _ _ _ _ _ _ _ domainInduction bodyInduction
      _ _ _ mappingTyped
    have renamedDomain := domainInduction mappingTyped
    have renamedBody := bodyInduction (mappingTyped.lift renamedDomain)
    exact .lam renamedDomain renamedBody
  · intro _ _ _ _ _ _ _ _ domainInduction codomainInduction
      _ _ _ mappingTyped
    have renamedDomain := domainInduction mappingTyped
    have renamedCodomain := codomainInduction (mappingTyped.lift renamedDomain)
    exact .pi renamedDomain renamedCodomain
  · intro _ _ _ _ _ _ _ _ equal termInduction targetInduction
      _ _ mapping mappingTyped
    exact .conversion (termInduction mappingTyped) (targetInduction mappingTyped)
      (equal.rename mapping)
  · intro _ _ _ _ _ _ _ _ subtype termInduction targetInduction
      _ _ mapping mappingTyped
    exact .cumulativity (termInduction mappingTyped) (targetInduction mappingTyped)
      (subtype.rename mapping)
  · intro _ _ _ level _ _ _ _ mappingTyped
    simpa only [Term.rename, Term.relationType] using
      HasType.packageFamily mappingTyped.targetWellFormed level
  · intro _ _ _ level _ _ _ _ mappingTyped
    simpa only [Term.rename, Term.packageType] using
      HasType.universePackage mappingTyped.targetWellFormed level
  · intro _ _ _ _ _ _ _ _ _ leftInduction rightInduction packageInduction
      _ _ _ mappingTyped
    simpa only [Term.rel, Term.rename, Term.packageType_rename,
      Term.relationType_rename] using
      HasType.relationProjection (leftInduction mappingTyped)
        (rightInduction mappingTyped) (packageInduction mappingTyped)
  · intro n context leftDomain rightDomain leftCodomain rightCodomain
      domainPackage codomainPackage domainLevel codomainLevel
      _ _ _ _ _ _
      leftDomainInduction rightDomainInduction leftCodomainInduction
      rightCodomainInduction domainPackageInduction codomainPackageInduction
      targetSize target mapping mappingTyped
    have renamedLeftDomain := leftDomainInduction mappingTyped
    have renamedRightDomain := rightDomainInduction mappingTyped
    have renamedLeftCodomain :=
      leftCodomainInduction (mappingTyped.lift renamedLeftDomain)
    have renamedRightCodomain :=
      rightCodomainInduction (mappingTyped.lift renamedRightDomain)
    have renamedDomainPackage := domainPackageInduction mappingTyped
    let targetLeft : Context (targetSize + 1) :=
      .extend target (leftDomain.rename mapping)
    have targetLeftWellFormed : WellFormed targetLeft :=
      .extend mappingTyped.targetWellFormed renamedLeftDomain
    have mappingIntoTargetLeft : TypedRenaming context targetLeft
        (DependentCalculus.Renaming.comp
          DependentCalculus.Renaming.shift mapping) :=
      TypedRenaming.comp (TypedRenaming.shift targetLeftWellFormed) mappingTyped
    have renamedRightInTargetLeft :
        HasType targetLeft
          ((rightDomain.rename mapping).rename
            DependentCalculus.Renaming.shift)
          (.sort domainLevel) := by
      simpa only [targetLeft, Term.rename, Term.rename_comp] using
        rightDomainInduction mappingIntoTargetLeft
    let targetBoth : Context (targetSize + 2) :=
      .extend targetLeft
        ((rightDomain.rename mapping).rename
          DependentCalculus.Renaming.shift)
    have targetBothWellFormed : WellFormed targetBoth :=
      .extend targetLeftWellFormed renamedRightInTargetLeft
    have mappingIntoTargetBoth : TypedRenaming context targetBoth
        (DependentCalculus.Renaming.comp
          DependentCalculus.Renaming.shift
          (DependentCalculus.Renaming.comp
            DependentCalculus.Renaming.shift mapping)) :=
      TypedRenaming.comp (TypedRenaming.shift targetBothWellFormed)
        mappingIntoTargetLeft
    have weakenedDomainPackage :
        HasType targetBoth ((domainPackage.rename mapping).weakenBy 2)
          (Term.packageType domainLevel
            ((leftDomain.rename mapping).weakenBy 2)
            ((rightDomain.rename mapping).weakenBy 2)) := by
      simpa only [targetBoth, targetLeft, Term.weakenBy, Term.rename_comp,
        Term.packageType_rename] using
        domainPackageInduction mappingIntoTargetBoth
    have weakenedLeftDomain :
        HasType targetBoth ((leftDomain.rename mapping).weakenBy 2)
          (.sort domainLevel) := by
      simpa only [Term.weakenBy, Term.rename_comp, Term.rename] using
        leftDomainInduction mappingIntoTargetBoth
    have weakenedRightDomain :
        HasType targetBoth ((rightDomain.rename mapping).weakenBy 2)
          (.sort domainLevel) := by
      simpa only [Term.weakenBy, Term.rename_comp, Term.rename] using
        rightDomainInduction mappingIntoTargetBoth
    have leftVariable :
        HasType targetBoth (.var 1)
          ((leftDomain.rename mapping).weakenBy 2) := by
      have variableWellTyped :=
        HasType.var targetBothWellFormed (1 : Fin (targetSize + 2))
      change HasType targetBoth (.var 1)
        (((leftDomain.rename mapping).rename
          DependentCalculus.Renaming.shift).rename
          DependentCalculus.Renaming.shift) at variableWellTyped
      simpa only [Term.weakenBy] using variableWellTyped
    have rightVariable :
        HasType targetBoth (.var 0)
          ((rightDomain.rename mapping).weakenBy 2) := by
      have variableWellTyped :=
        HasType.var targetBothWellFormed (0 : Fin (targetSize + 2))
      change HasType targetBoth (.var 0)
        (((rightDomain.rename mapping).rename
          DependentCalculus.Renaming.shift).rename
          DependentCalculus.Renaming.shift) at variableWellTyped
      simpa only [Term.weakenBy] using variableWellTyped
    have relatedDomainWellTyped :
        HasType targetBoth
          (Term.relatedDomain (domainPackage.rename mapping))
          (.sort domainLevel) := by
      have projected := HasType.relationProjection weakenedLeftDomain weakenedRightDomain
        weakenedDomainPackage
      have appliedLeft := HasType.app projected leftVariable
      have appliedLeft' :
          HasType targetBoth
            (.app (Term.rel ((domainPackage.rename mapping).weakenBy 2)) (.var 1))
            (.pi ((rightDomain.rename mapping).weakenBy 2)
              (.sort domainLevel)) := by
        change HasType targetBoth
          (.app (Term.rel ((domainPackage.rename mapping).weakenBy 2)) (.var 1))
          (Term.pi
            ((((rightDomain.rename mapping).weakenBy 2).rename
              DependentCalculus.Renaming.shift).instantiate (.var 1))
            (.sort domainLevel)) at appliedLeft
        rw [Term.instantiate_rename_shift] at appliedLeft
        exact appliedLeft
      have appliedRight := HasType.app appliedLeft' rightVariable
      simpa only [Term.relatedDomain, Term.relationApplication,
        Term.relationType, Term.packageType, Term.rel, Term.instantiate,
        Term.substitute, Term.rename] using appliedRight
    have firstLift := mappingTyped.lift renamedLeftDomain
    have renamedShiftedRight :
        HasType targetLeft
          ((rightDomain.rename
            DependentCalculus.Renaming.shift).rename
            (DependentCalculus.Renaming.lift mapping))
          (.sort domainLevel) := by
      simpa only [Term.rename_comp, shiftRenaming_natural] using
        renamedRightInTargetLeft
    have secondLiftRaw := firstLift.lift renamedShiftedRight
    have secondLift : TypedRenaming
        (.extend (.extend context leftDomain)
          (rightDomain.rename DependentCalculus.Renaming.shift))
        targetBoth
        (DependentCalculus.Renaming.lift
          (DependentCalculus.Renaming.lift mapping)) := by
      simpa only [targetBoth, targetLeft, Term.rename_comp,
        shiftRenaming_natural] using secondLiftRaw
    have relatedDomainRenamed :
        HasType targetBoth
          ((Term.relatedDomain domainPackage).rename (Renaming.liftBy mapping 2))
          (.sort domainLevel) := by
      rw [← Term.relatedDomain_rename]
      exact relatedDomainWellTyped
    have thirdLift := secondLift.lift relatedDomainRenamed
    have relationalMapping : TypedRenaming
        (relationalExtend context leftDomain rightDomain domainPackage)
        (relationalExtend target (leftDomain.rename mapping)
          (rightDomain.rename mapping) (domainPackage.rename mapping))
        (Renaming.liftBy mapping 3) := by
      simpa only [relationalExtend, targetBoth, targetLeft,
        Term.relatedDomain_rename, Renaming.liftBy] using thirdLift
    have renamedCodomainPackage := codomainPackageInduction relationalMapping
    have renamedCodomainPackage' :
        HasType
          (relationalExtend target (leftDomain.rename mapping)
            (rightDomain.rename mapping) (domainPackage.rename mapping))
          (codomainPackage.rename (Renaming.liftBy mapping 3))
          (Term.packageType codomainLevel
            ((leftCodomain.rename
              (DependentCalculus.Renaming.lift mapping)).rename
              originalBinderRenaming)
            ((rightCodomain.rename
              (DependentCalculus.Renaming.lift mapping)).rename
              primedBinderRenaming)) := by
      simpa only [Term.packageType_rename, Term.originalBinder_rename,
        Term.primedBinder_rename] using renamedCodomainPackage
    have packageWellTyped := HasType.dependentProductPackage
      renamedLeftDomain renamedRightDomain renamedLeftCodomain renamedRightCodomain
      renamedDomainPackage renamedCodomainPackage'
    simpa only [Term.rename, Term.packageType_rename] using packageWellTyped

/-- Weakening a typing derivation into a well-formed context extension preserves its type. -/
theorem weaken {context : Context n} {term type domain : Term n}
    (termWellTyped : HasType context term type)
    (extendedWellFormed : WellFormed (.extend context domain)) :
    HasType (.extend context domain)
      (term.rename DependentCalculus.Renaming.shift)
      (type.rename DependentCalculus.Renaming.shift) :=
  termWellTyped.rename (TypedRenaming.shift extendedWellFormed)

end HasType

namespace WellFormed

/-- Every lookup in a well-formed extended context is universe-typed. -/
theorem lookup_hasType {context : Context n}
    (contextWellFormed : WellFormed context) (index : Fin n) :
    ∃ level, HasType context (context.lookup index) (.sort level) := by
  refine WellFormed.rec
    (motive_1 := fun {n} context _ =>
      ∀ index : Fin n, ∃ level, HasType context (context.lookup index) (.sort level))
    (motive_2 := fun _ _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ contextWellFormed index
  · exact fun index => Fin.elim0 index
  · intro _ context domain level sourceWellFormed domainWellTyped
      inductionHypothesis _ index
    refine Fin.cases ?_ ?_ index
    · refine ⟨level, ?_⟩
      simpa only [Context.lookup_zero, Term.rename] using
        domainWellTyped.weaken (.extend sourceWellFormed domainWellTyped)
    · intro older
      obtain ⟨olderLevel, olderWellTyped⟩ := inductionHypothesis older
      refine ⟨olderLevel, ?_⟩
      simpa only [Context.lookup_succ, Term.rename] using
        olderWellTyped.weaken (.extend sourceWellFormed domainWellTyped)
  all_goals intros
  all_goals trivial

end WellFormed

/-- A typed substitution assigns every source variable its substituted lookup type. -/
structure TypedSubstitution (source : Context sourceSize) (target : Context targetSize)
    (mapping : Substitution sourceSize targetSize) : Prop where
  /-- The substitution target context is well formed. -/
  targetWellFormed : WellFormed target
  /-- Each substitution image has the substituted source lookup type. -/
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
    simpa only [Substitution.ofRenaming, Term.substitute_ofRenaming] using
      variableWellTyped

/-- Extend a typed substitution beneath matching dependent context extensions. -/
theorem lift {source : Context sourceSize} {target : Context targetSize}
    {mapping : Substitution sourceSize targetSize} {domain : Term sourceSize}
    {level : Nat} (mappingTyped : TypedSubstitution source target mapping)
    (domainWellTyped : HasType target (domain.substitute mapping) (.sort level)) :
    TypedSubstitution (.extend source domain)
      (.extend target (domain.substitute mapping)) (Substitution.lift mapping) where
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

/-- A well-typed argument gives the single substitution for the newest variable. -/
theorem single {context : Context n} {domain argument : Term n}
    (contextWellFormed : WellFormed context)
    (argumentWellTyped : HasType context argument domain) :
    TypedSubstitution (.extend context domain) context
      (Substitution.single argument) where
  targetWellFormed := contextWellFormed
  variableWellTyped index := by
    refine Fin.cases ?_ ?_ index
    · change HasType context argument
        ((domain.rename DependentCalculus.Renaming.shift).instantiate
          argument)
      rw [Term.instantiate_rename_shift]
      exact argumentWellTyped
    · intro older
      change HasType context (.var older)
        (((context.lookup older).rename
          DependentCalculus.Renaming.shift).instantiate argument)
      rw [Term.instantiate_rename_shift]
      exact HasType.var contextWellFormed older

end TypedSubstitution

namespace HasType

/-- Typed simultaneous substitution preserves extended dependent typing. -/
theorem substitute {source : Context sourceSize} {term type : Term sourceSize}
    (termWellTyped : HasType source term type) :
    ∀ {targetSize} {target : Context targetSize}
      {mapping : Substitution sourceSize targetSize},
      TypedSubstitution source target mapping →
        HasType target (term.substitute mapping) (type.substitute mapping) := by
  refine HasType.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := fun {n} context term type _ =>
      ∀ {targetSize} {target : Context targetSize}
        {mapping : Substitution n targetSize},
        TypedSubstitution context target mapping →
          HasType target (term.substitute mapping) (type.substitute mapping))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ termWellTyped
  · trivial
  · intros
    trivial
  · intro _ _ _ level _ _ _ _ mappingTyped
    exact .sort mappingTyped.targetWellFormed level
  · intro _ _ _ index _ _ _ _ mappingTyped
    exact mappingTyped.variableWellTyped index
  · intro _ _ _ _ _ _ _ _ functionInduction argumentInduction
      _ _ _ mappingTyped
    have applicationWellTyped := HasType.app
      (functionInduction mappingTyped) (argumentInduction mappingTyped)
    simpa only [Term.substitute, Term.substitute_instantiate] using
      applicationWellTyped
  · intro _ _ _ _ _ _ _ _ domainInduction bodyInduction
      _ _ _ mappingTyped
    have substitutedDomain := domainInduction mappingTyped
    have substitutedBody := bodyInduction (mappingTyped.lift substitutedDomain)
    exact .lam substitutedDomain substitutedBody
  · intro _ _ _ _ _ _ _ _ domainInduction codomainInduction
      _ _ _ mappingTyped
    have substitutedDomain := domainInduction mappingTyped
    have substitutedCodomain := codomainInduction (mappingTyped.lift substitutedDomain)
    exact .pi substitutedDomain substitutedCodomain
  · intro _ _ _ _ _ _ _ _ equal termInduction targetInduction
      _ _ mapping mappingTyped
    exact .conversion (termInduction mappingTyped) (targetInduction mappingTyped)
      (equal.substitute mapping)
  · intro _ _ _ _ _ _ _ _ subtype termInduction targetInduction
      _ _ mapping mappingTyped
    exact .cumulativity (termInduction mappingTyped) (targetInduction mappingTyped)
      (subtype.substitute mapping)
  · intro _ _ _ level _ _ _ _ mappingTyped
    simpa only [Term.substitute, Term.relationType_substitute] using
      HasType.packageFamily mappingTyped.targetWellFormed level
  · intro _ _ _ level _ _ _ _ mappingTyped
    simpa only [Term.substitute, Term.packageType_substitute] using
      HasType.universePackage mappingTyped.targetWellFormed level
  · intro _ _ _ _ _ _ _ _ _ leftInduction rightInduction packageInduction
      _ _ _ mappingTyped
    simpa only [Term.rel, Term.substitute, Term.packageType_substitute,
      Term.relationType_substitute] using
      HasType.relationProjection (leftInduction mappingTyped)
        (rightInduction mappingTyped) (packageInduction mappingTyped)
  · intro n context leftDomain rightDomain leftCodomain rightCodomain
      domainPackage codomainPackage domainLevel codomainLevel
      _ _ _ _ _ _
      leftDomainInduction rightDomainInduction leftCodomainInduction
      rightCodomainInduction domainPackageInduction codomainPackageInduction
      targetSize target mapping mappingTyped
    have substitutedLeftDomain := leftDomainInduction mappingTyped
    have substitutedRightDomain := rightDomainInduction mappingTyped
    have substitutedLeftCodomain :=
      leftCodomainInduction (mappingTyped.lift substitutedLeftDomain)
    have substitutedRightCodomain :=
      rightCodomainInduction (mappingTyped.lift substitutedRightDomain)
    have substitutedDomainPackage := domainPackageInduction mappingTyped
    let targetLeft : Context (targetSize + 1) :=
      .extend target (leftDomain.substitute mapping)
    have targetLeftWellFormed : WellFormed targetLeft :=
      .extend mappingTyped.targetWellFormed substitutedLeftDomain
    have substitutedRightInTargetLeft :
        HasType targetLeft
          ((rightDomain.substitute mapping).rename
            DependentCalculus.Renaming.shift)
          (.sort domainLevel) :=
      substitutedRightDomain.weaken targetLeftWellFormed
    let targetBoth : Context (targetSize + 2) :=
      .extend targetLeft
        ((rightDomain.substitute mapping).rename
          DependentCalculus.Renaming.shift)
    have targetBothWellFormed : WellFormed targetBoth :=
      .extend targetLeftWellFormed substitutedRightInTargetLeft
    have weakenedDomainPackageOnce :=
      substitutedDomainPackage.weaken targetLeftWellFormed
    have weakenedDomainPackageTwice :=
      weakenedDomainPackageOnce.weaken targetBothWellFormed
    have weakenedDomainPackage :
        HasType targetBoth ((domainPackage.substitute mapping).weakenBy 2)
          (Term.packageType domainLevel
            ((leftDomain.substitute mapping).weakenBy 2)
            ((rightDomain.substitute mapping).weakenBy 2)) := by
      simpa only [targetBoth, targetLeft, Term.weakenBy,
        Term.packageType_substitute, Term.packageType_rename] using
        weakenedDomainPackageTwice
    have weakenedLeftDomainOnce :=
      substitutedLeftDomain.weaken targetLeftWellFormed
    have weakenedLeftDomainTwice :=
      weakenedLeftDomainOnce.weaken targetBothWellFormed
    have weakenedLeftDomain :
        HasType targetBoth ((leftDomain.substitute mapping).weakenBy 2)
          (.sort domainLevel) := by
      simpa only [targetBoth, targetLeft, Term.weakenBy, Term.rename,
        Term.substitute] using
        weakenedLeftDomainTwice
    have weakenedRightDomainOnce :=
      substitutedRightDomain.weaken targetLeftWellFormed
    have weakenedRightDomainTwice :=
      weakenedRightDomainOnce.weaken targetBothWellFormed
    have weakenedRightDomain :
        HasType targetBoth ((rightDomain.substitute mapping).weakenBy 2)
          (.sort domainLevel) := by
      simpa only [targetBoth, targetLeft, Term.weakenBy, Term.rename,
        Term.substitute] using
        weakenedRightDomainTwice
    have leftVariable :
        HasType targetBoth (.var 1)
          ((leftDomain.substitute mapping).weakenBy 2) := by
      have variableWellTyped :=
        HasType.var targetBothWellFormed (1 : Fin (targetSize + 2))
      change HasType targetBoth (.var 1)
        (((leftDomain.substitute mapping).rename
          DependentCalculus.Renaming.shift).rename
          DependentCalculus.Renaming.shift) at variableWellTyped
      simpa only [Term.weakenBy] using variableWellTyped
    have rightVariable :
        HasType targetBoth (.var 0)
          ((rightDomain.substitute mapping).weakenBy 2) := by
      have variableWellTyped :=
        HasType.var targetBothWellFormed (0 : Fin (targetSize + 2))
      change HasType targetBoth (.var 0)
        (((rightDomain.substitute mapping).rename
          DependentCalculus.Renaming.shift).rename
          DependentCalculus.Renaming.shift) at variableWellTyped
      simpa only [Term.weakenBy] using variableWellTyped
    have relatedDomainWellTyped :
        HasType targetBoth
          (Term.relatedDomain (domainPackage.substitute mapping))
          (.sort domainLevel) := by
      have projected := HasType.relationProjection weakenedLeftDomain weakenedRightDomain
        weakenedDomainPackage
      have appliedLeft := HasType.app projected leftVariable
      have appliedLeft' :
          HasType targetBoth
            (.app (Term.rel ((domainPackage.substitute mapping).weakenBy 2)) (.var 1))
            (.pi ((rightDomain.substitute mapping).weakenBy 2)
              (.sort domainLevel)) := by
        change HasType targetBoth
          (.app (Term.rel ((domainPackage.substitute mapping).weakenBy 2)) (.var 1))
          (Term.pi
            ((((rightDomain.substitute mapping).weakenBy 2).rename
              DependentCalculus.Renaming.shift).instantiate (.var 1))
            (.sort domainLevel)) at appliedLeft
        rw [Term.instantiate_rename_shift] at appliedLeft
        exact appliedLeft
      have appliedRight := HasType.app appliedLeft' rightVariable
      simpa only [Term.relatedDomain, Term.relationApplication,
        Term.relationType, Term.packageType, Term.rel, Term.instantiate,
        Term.substitute, Term.rename] using appliedRight
    have firstLift := mappingTyped.lift substitutedLeftDomain
    have substitutedShiftedRight :
        HasType targetLeft
          ((rightDomain.rename
            DependentCalculus.Renaming.shift).substitute
            (Substitution.lift mapping))
          (.sort domainLevel) := by
      simpa only [Term.substitute_rename_shift_lift] using
        substitutedRightInTargetLeft
    have secondLiftRaw := firstLift.lift substitutedShiftedRight
    have secondLift : TypedSubstitution
        (.extend (.extend context leftDomain)
          (rightDomain.rename DependentCalculus.Renaming.shift))
        targetBoth (Substitution.lift (Substitution.lift mapping)) := by
      simpa only [targetBoth, targetLeft,
        Term.substitute_rename_shift_lift] using secondLiftRaw
    have relatedDomainSubstituted :
        HasType targetBoth
          ((Term.relatedDomain domainPackage).substitute
            (Substitution.liftBy mapping 2))
          (.sort domainLevel) := by
      rw [← Term.relatedDomain_substitute]
      exact relatedDomainWellTyped
    have thirdLift := secondLift.lift relatedDomainSubstituted
    have relationalMapping : TypedSubstitution
        (relationalExtend context leftDomain rightDomain domainPackage)
        (relationalExtend target (leftDomain.substitute mapping)
          (rightDomain.substitute mapping) (domainPackage.substitute mapping))
        (Substitution.liftBy mapping 3) := by
      simpa only [relationalExtend, targetBoth, targetLeft,
        Term.relatedDomain_substitute, Substitution.liftBy] using thirdLift
    have substitutedCodomainPackage := codomainPackageInduction relationalMapping
    have substitutedCodomainPackage' :
        HasType
          (relationalExtend target (leftDomain.substitute mapping)
            (rightDomain.substitute mapping) (domainPackage.substitute mapping))
          (codomainPackage.substitute (Substitution.liftBy mapping 3))
          (Term.packageType codomainLevel
            ((leftCodomain.substitute (Substitution.lift mapping)).rename
              originalBinderRenaming)
            ((rightCodomain.substitute (Substitution.lift mapping)).rename
              primedBinderRenaming)) := by
      simpa only [Term.packageType_substitute, Term.originalBinder_substitute,
        Term.primedBinder_substitute] using substitutedCodomainPackage
    have packageWellTyped := HasType.dependentProductPackage
      substitutedLeftDomain substitutedRightDomain substitutedLeftCodomain
      substitutedRightCodomain substitutedDomainPackage substitutedCodomainPackage'
    simpa only [Term.substitute, Term.packageType_substitute] using packageWellTyped

/-- Instantiating a typed body with a typed argument preserves the instantiated type. -/
theorem instantiate {context : Context n} {domain argument : Term n}
    {body type : Term (n + 1)}
    (bodyWellTyped : HasType (.extend context domain) body type)
    (contextWellFormed : WellFormed context)
    (argumentWellTyped : HasType context argument domain) :
    HasType context (body.instantiate argument) (type.instantiate argument) :=
  bodyWellTyped.substitute
    (TypedSubstitution.single contextWellFormed argumentWellTyped)

end HasType

/-- Embedding a well-formed core context preserves its formation derivation. -/
theorem WellFormed.ofCore
    {source : DependentCalculus.Context n}
    (sourceWellFormed : DependentCalculus.WellFormed source) :
    WellFormed (Context.ofCore source) := by
  refine DependentCalculus.WellFormed.rec
    (motive_1 := fun source _ => WellFormed (Context.ofCore source))
    (motive_2 := fun source term type _ =>
      HasType (Context.ofCore source) (Term.ofCore term) (Term.ofCore type))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ sourceWellFormed
  · exact .empty
  · intro _ _ _ _ _ _ sourceInduction typeInduction
    exact .extend sourceInduction typeInduction
  · intro _ _ _ level sourceInduction
    exact .sort sourceInduction level
  · intro _ source _ index sourceInduction
    have variableWellTyped := HasType.var sourceInduction index
    rw [Context.ofCore_lookup source index] at variableWellTyped
    exact variableWellTyped
  · intro _ _ _ _ _ _ _ _ functionInduction argumentInduction
    have applicationWellTyped := HasType.app functionInduction argumentInduction
    simpa only [Term.ofCore, Term.ofCore_instantiate] using applicationWellTyped
  · intro _ _ _ _ _ _ _ _ domainInduction bodyInduction
    exact .lam domainInduction bodyInduction
  · intro _ _ _ _ _ _ _ _ domainInduction codomainInduction
    exact .pi domainInduction codomainInduction
  · intro _ _ _ _ _ _ _ _ equal termInduction targetInduction
    exact .conversion termInduction targetInduction (Convertible.ofCore equal)
  · intro _ _ _ _ _ _ _ _ subtype termInduction targetInduction
    exact .cumulativity termInduction targetInduction (Cumulative.ofCore subtype)

/-- Embedding a core typing derivation preserves dependent typing. -/
theorem HasType.ofCore
    {source : DependentCalculus.Context n}
    {term type : CoreTerm n}
    (termWellTyped : DependentCalculus.HasType source term type) :
    HasType (Context.ofCore source) (Term.ofCore term) (Term.ofCore type) := by
  refine DependentCalculus.HasType.rec
    (motive_1 := fun source _ => WellFormed (Context.ofCore source))
    (motive_2 := fun source term type _ =>
      HasType (Context.ofCore source) (Term.ofCore term) (Term.ofCore type))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ termWellTyped
  · exact .empty
  · intro _ _ _ _ _ _ sourceInduction typeInduction
    exact .extend sourceInduction typeInduction
  · intro _ _ _ level sourceInduction
    exact .sort sourceInduction level
  · intro _ source _ index sourceInduction
    have variableWellTyped := HasType.var sourceInduction index
    rw [Context.ofCore_lookup source index] at variableWellTyped
    exact variableWellTyped
  · intro _ _ _ _ _ _ _ _ functionInduction argumentInduction
    have applicationWellTyped := HasType.app functionInduction argumentInduction
    simpa only [Term.ofCore, Term.ofCore_instantiate] using applicationWellTyped
  · intro _ _ _ _ _ _ _ _ domainInduction bodyInduction
    exact .lam domainInduction bodyInduction
  · intro _ _ _ _ _ _ _ _ domainInduction codomainInduction
    exact .pi domainInduction codomainInduction
  · intro _ _ _ _ _ _ _ _ equal termInduction targetInduction
    exact .conversion termInduction targetInduction (Convertible.ofCore equal)
  · intro _ _ _ _ _ _ _ _ subtype termInduction targetInduction
    exact .cumulativity termInduction targetInduction (Cumulative.ofCore subtype)

/-- The original-variable embedding is a typed renaming into a translated context. -/
theorem originalTypedRenaming
    (source : DependentCalculus.Context n)
    (translatedWellFormed : WellFormed (context source)) :
    TypedRenaming (Context.ofCore source) (context source)
      (RawParametricity.originalRenaming n) where
  targetWellFormed := translatedWellFormed
  lookup_eq index := by
    rw [Context.translated_lookup_original, Context.ofCore_lookup]
    exact Term.ofCore_rename (source.lookup index)
      (RawParametricity.originalRenaming n)

/-- The primed-variable embedding is a typed renaming into a translated context. -/
theorem primedTypedRenaming
    (source : DependentCalculus.Context n)
    (translatedWellFormed : WellFormed (context source)) :
    TypedRenaming (Context.ofCore source) (context source)
      (RawParametricity.primedRenaming n) where
  targetWellFormed := translatedWellFormed
  lookup_eq index := by
    rw [Context.translated_lookup_primed, Context.ofCore_lookup]
    exact Term.ofCore_rename (source.lookup index)
      (RawParametricity.primedRenaming n)

namespace HasType

/-- Original-copy formation preserves every core typing derivation. -/
theorem original
    {source : DependentCalculus.Context n}
    {term type : CoreTerm n}
    (termWellTyped : DependentCalculus.HasType source term type)
    (translatedWellFormed : WellFormed (context source)) :
    HasType (context source) (UnivalentParametricity.original term)
      (UnivalentParametricity.original type) := by
  simpa only [UnivalentParametricity.original, RawParametricity.original,
    Term.ofCore_rename] using
    (HasType.ofCore termWellTyped).rename
      (originalTypedRenaming source translatedWellFormed)

/-- Primed-copy formation preserves every core typing derivation. -/
theorem primed
    {source : DependentCalculus.Context n}
    {term type : CoreTerm n}
    (termWellTyped : DependentCalculus.HasType source term type)
    (translatedWellFormed : WellFormed (context source)) :
    HasType (context source) (UnivalentParametricity.primed term)
      (UnivalentParametricity.primed type) := by
  simpa only [UnivalentParametricity.primed, RawParametricity.primed,
    Term.ofCore_rename] using
    (HasType.ofCore termWellTyped).rename
      (primedTypedRenaming source translatedWellFormed)

end HasType

/-- A binary relation type is formed from universe-typed endpoints. -/
theorem relationType_hasType {context : Context n} {left right : Term n}
    {leftLevel rightLevel relationLevel : Nat}
    (contextWellFormed : WellFormed context)
    (leftWellTyped : HasType context left (.sort leftLevel))
    (rightWellTyped : HasType context right (.sort rightLevel)) :
    HasType context (Term.relationType relationLevel left right)
      (.sort (max leftLevel (max rightLevel (relationLevel + 1)))) := by
  have leftExtended : WellFormed (.extend context left) :=
    .extend contextWellFormed leftWellTyped
  have rightWeakened :
      HasType (.extend context left)
        (right.rename DependentCalculus.Renaming.shift)
        (.sort rightLevel) := by
    simpa only [Term.rename] using rightWellTyped.weaken leftExtended
  have endpointsExtended :
      WellFormed
        (.extend (.extend context left)
          (right.rename DependentCalculus.Renaming.shift)) :=
    .extend leftExtended rightWeakened
  have resultSort := HasType.sort endpointsExtended relationLevel
  have innerProduct := HasType.pi rightWeakened resultSort
  have outerProduct := HasType.pi leftWellTyped innerProduct
  simpa only [Term.relationType, Nat.max_assoc] using outerProduct

/-- Applying a typed binary relation to typed endpoints yields a universe inhabitant. -/
theorem relationApplication_hasType {context : Context n}
    {relation left right leftTerm rightTerm : Term n} {level : Nat}
    (relationWellTyped :
      HasType context relation (Term.relationType level left right))
    (leftWellTyped : HasType context leftTerm left)
    (rightWellTyped : HasType context rightTerm right) :
    HasType context
      (Term.relationApplication relation leftTerm rightTerm) (.sort level) := by
  have appliedLeft := HasType.app relationWellTyped leftWellTyped
  have appliedLeft' :
      HasType context (.app relation leftTerm) (.pi right (.sort level)) := by
    change HasType context (.app relation leftTerm)
      (.pi ((right.rename
        DependentCalculus.Renaming.shift).instantiate leftTerm)
        (.sort level)) at appliedLeft
    rw [Term.instantiate_rename_shift] at appliedLeft
    exact appliedLeft
  have appliedRight := HasType.app appliedLeft' rightWellTyped
  simpa only [Term.relationApplication, Term.instantiate, Term.substitute] using
    appliedRight

/-- A package-family application is a type when both endpoints inhabit its universe. -/
theorem packageType_hasType {context : Context n} {left right : Term n}
    {level : Nat} (contextWellFormed : WellFormed context)
    (leftWellTyped : HasType context left (.sort level))
    (rightWellTyped : HasType context right (.sort level)) :
    HasType context (Term.packageType level left right) (.sort (level + 1)) := by
  have family := HasType.packageFamily contextWellFormed level
  have firstApplication := HasType.app family leftWellTyped
  have secondApplication := HasType.app firstApplication rightWellTyped
  simpa only [Term.packageType, Term.relationType, Term.instantiate,
    Term.substitute, Term.rename] using secondApplication

namespace HasType

/-- The assigned type of every well-typed extended term inhabits a universe. -/
theorem typeWellTyped {context : Context n} {term type : Term n}
    (termWellTyped : HasType context term type) :
    ∃ level, HasType context type (.sort level) := by
  refine HasType.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := fun context _ type _ =>
      ∃ level, HasType context type (.sort level))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ termWellTyped
  · trivial
  · intros; trivial
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
      HasType.sort domainWellTyped.contextWellFormed
        (max domainLevel codomainLevel)⟩
  · intro _ _ _ _ _ level _ targetWellTyped _ _ _
    exact ⟨level, targetWellTyped⟩
  · intro _ _ _ _ _ level _ targetWellTyped _ _ _
    exact ⟨level, targetWellTyped⟩
  · intro _ _ contextWellFormed level _
    have endpoint := HasType.sort contextWellFormed level
    exact ⟨_, relationType_hasType contextWellFormed endpoint endpoint⟩
  · intro _ _ contextWellFormed level _
    have endpoint := HasType.sort contextWellFormed level
    exact ⟨level + 2,
      packageType_hasType contextWellFormed endpoint endpoint⟩
  · intro _ _ _ _ _ level leftWellTyped rightWellTyped _ _ _ _
    exact ⟨_, relationType_hasType leftWellTyped.contextWellFormed
      leftWellTyped rightWellTyped⟩
  · intro _ _ _ _ _ _ _ _ domainLevel codomainLevel
      leftDomainWellTyped rightDomainWellTyped leftCodomainWellTyped
      rightCodomainWellTyped _ _ _ _ _ _ _ _
    have leftProduct := HasType.pi leftDomainWellTyped leftCodomainWellTyped
    have rightProduct := HasType.pi rightDomainWellTyped rightCodomainWellTyped
    exact ⟨max domainLevel codomainLevel + 1,
      packageType_hasType leftDomainWellTyped.contextWellFormed
        leftProduct rightProduct⟩

end HasType

/-- A universe-translated related-term type computes to its endpoint package type. -/
theorem relatedTermType_sort_convertible (term : CoreTerm n) (level : Nat) :
    Convertible (relatedTermType term (.sort level))
      (Term.packageType level (original term) (primed term)) :=
  (Convertible.beta
    (BetaStep.universeProjection (n := scopeSize n) level)).appFunction.appFunction

/-- A universe-translated related-term type is itself universe-typed. -/
theorem relatedTermType_sort_hasType
    {source : DependentCalculus.Context n}
    {term : CoreTerm n} {level : Nat}
    (translatedWellFormed : WellFormed (context source))
    (originalWellTyped : HasType (context source) (original term) (.sort level))
    (primedWellTyped : HasType (context source) (primed term) (.sort level)) :
    HasType (context source) (relatedTermType term (.sort level))
      (.sort (level + 1)) := by
  have package := HasType.universePackage translatedWellFormed level
  have universeType := HasType.sort translatedWellFormed level
  have projected :=
    HasType.relationProjection universeType universeType package
  have firstApplication := HasType.app projected originalWellTyped
  have secondApplication := HasType.app firstApplication primedWellTyped
  simpa only [relatedTermType, typeTranslation, termTranslation_sort,
    Term.relationApplication, Term.rel, Term.packageType, Term.relationType,
    Term.instantiate, Term.substitute, Term.rename] using secondApplication

/-- Translating one source extension is exactly the `pΠ` relational extension. -/
theorem context_extend_eq_relationalExtend
    (source : DependentCalculus.Context n) (domain : CoreTerm n) :
    context (.extend source domain) =
      relationalExtend (context source) (original domain) (primed domain)
        (termTranslation domain) :=
  rfl

/-- Three nested beta contractions implement substitution into a relational binder triple. -/
theorem tripleBeta_convertible
    (firstDomain : Term n) (secondDomain : Term (n + 1))
    (thirdDomain : Term (n + 2)) (body : Term (n + 3))
    (firstArgument secondArgument thirdArgument : Term n) :
    Convertible
      (.app (.app (.app
        (.lam firstDomain (.lam secondDomain (.lam thirdDomain body)))
        firstArgument) secondArgument) thirdArgument)
      (body.substitute
        (Fin.cases thirdArgument
          (Fin.cases secondArgument
            (Fin.cases firstArgument Term.var)))) := by
  let firstSingle : Substitution (n + 1) n := Substitution.single firstArgument
  let secondSingle : Substitution (n + 1) n := Substitution.single secondArgument
  let thirdSingle : Substitution (n + 1) n := Substitution.single thirdArgument
  let firstLift : Substitution (n + 2) (n + 1) := Substitution.lift firstSingle
  let firstLiftTwice : Substitution (n + 3) (n + 2) :=
    Substitution.lift firstLift
  let afterFirst : Term n :=
    .app
      (.app
        (.lam (secondDomain.substitute firstSingle)
          (.lam (thirdDomain.substitute firstLift)
            (body.substitute firstLiftTwice)))
        secondArgument)
      thirdArgument
  let afterSecond : Term n :=
    .app
      (.lam
        ((thirdDomain.substitute firstLift).substitute secondSingle)
        ((body.substitute firstLiftTwice).substitute
          (Substitution.lift secondSingle)))
      thirdArgument
  let afterThird : Term n :=
    ((body.substitute firstLiftTwice).substitute
      (Substitution.lift secondSingle)).substitute thirdSingle
  have firstConversion :
      Convertible
        (.app (.app (.app
          (.lam firstDomain (.lam secondDomain (.lam thirdDomain body)))
          firstArgument) secondArgument) thirdArgument)
        afterFirst := by
    exact .beta (.appFunction (.appFunction
      (.beta firstDomain (.lam secondDomain (.lam thirdDomain body)) firstArgument)))
  have secondConversion : Convertible afterFirst afterSecond := by
    exact .beta (.appFunction
      (.beta (secondDomain.substitute firstSingle)
        (.lam (thirdDomain.substitute firstLift)
          (body.substitute firstLiftTwice)) secondArgument))
  have thirdConversion : Convertible afterSecond afterThird := by
    exact .beta
      (.beta ((thirdDomain.substitute firstLift).substitute secondSingle)
        ((body.substitute firstLiftTwice).substitute
          (Substitution.lift secondSingle)) thirdArgument)
  refine firstConversion.trans (secondConversion.trans (thirdConversion.trans ?_))
  have equal : afterThird =
      body.substitute
        (Fin.cases thirdArgument
          (Fin.cases secondArgument
            (Fin.cases firstArgument Term.var))) := by
    unfold afterThird thirdSingle firstLiftTwice firstLift secondSingle firstSingle
    rw [Term.substitute_comp, Term.substitute_comp]
    apply Term.substitute_congr
    funext index
    simp only [Substitution.comp]
    refine Fin.cases rfl ?_ index
    intro oneOrOlder
    refine Fin.cases ?_ ?_ oneOrOlder
    · change
        (secondArgument.rename
          DependentCalculus.Renaming.shift).instantiate
            thirdArgument = secondArgument
      exact Term.instantiate_rename_shift secondArgument thirdArgument
    intro twoOrOlder
    refine Fin.cases ?_ ?_ twoOrOlder
    · change
        ((firstArgument.rename
            DependentCalculus.Renaming.shift).rename
              DependentCalculus.Renaming.shift).substitute
            (Substitution.comp
              (Substitution.single thirdArgument)
              (Substitution.lift secondSingle)) =
          firstArgument
      rw [← Term.substitute_comp, Term.substitute_rename_shift_lift]
      change
        (((firstArgument.rename
          DependentCalculus.Renaming.shift).instantiate
            secondArgument).rename
              DependentCalculus.Renaming.shift).instantiate
                thirdArgument = firstArgument
      rw [Term.instantiate_rename_shift, Term.instantiate_rename_shift]
    intro older
    rfl
  rw [equal]
  exact .refl _

/-- Translating a core head beta redex yields three extended beta contractions. -/
theorem termTranslation_beta
    (domain : CoreTerm n) (body : CoreTerm (n + 1)) (argument : CoreTerm n) :
    Convertible
      (termTranslation (.app (.lam domain body) argument))
      (termTranslation (body.instantiate argument)) := by
  have reduction := tripleBeta_convertible
    (original domain) ((primed domain).weakenBy 1)
    (Term.relatedDomain (termTranslation domain)) (termTranslation body)
    (original argument) (primed argument) (termTranslation argument)
  rw [termTranslation_instantiate]
  have mappingEqual : (relationalSingle argument).relational =
      Fin.cases (termTranslation argument)
        (Fin.cases (primed argument)
          (Fin.cases (original argument) Term.var)) := by
    rfl
  rw [mappingEqual]
  simp only [termTranslation_app, termTranslation_lam]
  convert reduction using 1
  apply Term.substitute_congr
  funext index
  rfl

/-- The package-valued translation preserves every core beta step as conversion. -/
theorem termTranslation_betaStep {left right : CoreTerm n}
    (step : DependentCalculus.BetaStep left right) :
    Convertible (termTranslation left) (termTranslation right) := by
  induction step with
  | beta domain body argument => exact termTranslation_beta domain body argument
  | appFunction _ inductionHypothesis =>
      exact inductionHypothesis.appFunction.appFunction.appFunction
  | appArgument step inductionHypothesis =>
      exact Convertible.relationApplication
        ((Convertible.refl _).appBoth (.beta (BetaStep.original step)))
        (.beta (BetaStep.primed step)) inductionHypothesis
  | lamDomain step inductionHypothesis =>
      exact (Convertible.beta (BetaStep.original step)).lamBoth
        ((Convertible.beta (BetaStep.primed step)).weakenBy 1 |>.lamBoth
          (inductionHypothesis.relatedDomain.lamBoth (.refl _)))
  | lamBody _ inductionHypothesis =>
      exact inductionHypothesis.lamBody.lamBody.lamBody
  | piDomain step inductionHypothesis =>
      exact Convertible.dependentProductPackage
        (.beta (BetaStep.original step)) (.beta (BetaStep.primed step))
        (.refl _) (.refl _) inductionHypothesis (.refl _)
  | piCodomain step inductionHypothesis =>
      exact Convertible.dependentProductPackage
        (.refl _) (.refl _)
        (Convertible.originalCodomain (.beta step))
        (Convertible.primedCodomain (.beta step))
        (.refl _) inductionHypothesis

/-- The package-valued translation preserves core definitional conversion. -/
theorem termTranslation_convertible {left right : CoreTerm n}
    (conversion : DependentCalculus.Convertible left right) :
    Convertible (termTranslation left) (termTranslation right) := by
  induction conversion with
  | refl => exact .refl _
  | beta step => exact termTranslation_betaStep step
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ firstInduction secondInduction =>
      exact firstInduction.trans secondInduction

/-- The relation-valued translation preserves core definitional conversion. -/
theorem typeTranslation_convertible {left right : CoreTerm n}
    (conversion : DependentCalculus.Convertible left right) :
    Convertible (typeTranslation left) (typeTranslation right) :=
  (termTranslation_convertible conversion).relationProjection

/-- Related-term types preserve conversion of the translated source type. -/
theorem relatedTermType_convertible (term : CoreTerm n)
    {leftType rightType : CoreTerm n}
    (conversion : DependentCalculus.Convertible leftType rightType) :
    Convertible (relatedTermType term leftType) (relatedTermType term rightType) :=
  Convertible.relationApplication (typeTranslation_convertible conversion)
    (.refl _) (.refl _)

/-- Related-term types preserve simultaneous conversion of term and source type. -/
theorem relatedTermType_convertibleBoth
    {term term' type type' : CoreTerm n}
    (termConversion : DependentCalculus.Convertible term term')
    (typeConversion : DependentCalculus.Convertible type type') :
    Convertible (relatedTermType term type) (relatedTermType term' type') :=
  Convertible.relationApplication (typeTranslation_convertible typeConversion)
    (Convertible.original termConversion) (Convertible.primed termConversion)

/-- The projected successor-universe relation applied to two copies of a universe. -/
def translatedUniversePackageType (level : Nat) : Term n :=
  Term.relationApplication (Term.rel (.universePackage (level + 1)))
    (.sort level) (.sort level)

/-- The translated universe-package type is itself universe-typed. -/
theorem translatedUniversePackageType_hasType {n : Nat} {context : Context n}
    (contextWellFormed : WellFormed context) (level : Nat) :
    HasType context (translatedUniversePackageType (n := n) level)
      (.sort (level + 2)) := by
  have higherPackage := HasType.universePackage contextWellFormed (level + 1)
  have higherSort := HasType.sort contextWellFormed (level + 1)
  have projected := HasType.relationProjection higherSort higherSort higherPackage
  have input := HasType.sort contextWellFormed level
  have firstApplication := HasType.app projected input
  have secondApplication := HasType.app firstApplication input
  simpa only [translatedUniversePackageType, Term.relationType, Term.packageType,
    Term.relationApplication, Term.rel, Term.instantiate, Term.substitute,
    Term.rename] using secondApplication

/-- The translated universe-package type computes to the direct package-family application. -/
theorem translatedUniversePackageType_convertible {n : Nat} (level : Nat) :
    Convertible (translatedUniversePackageType (n := n) level)
      (Term.packageType (level + 1) (.sort level) (.sort level)) :=
  (Convertible.beta (BetaStep.universeProjection (n := n) (level + 1))).appFunction.appFunction

/-- The translated universe package has the translated successor-universe relation type. -/
theorem universePackage_hasType_translatedUniverse {n : Nat} {context : Context n}
    (contextWellFormed : WellFormed context) (level : Nat) :
    HasType context (.universePackage level)
      (translatedUniversePackageType (n := n) level) :=
  .conversion (.universePackage contextWellFormed level)
    (translatedUniversePackageType_hasType contextWellFormed level)
    (translatedUniversePackageType_convertible level).symm

/-- Projecting a translated universe is definitionally convertible to its package family. -/
theorem universeTypeTranslation_convertible {n : Nat} (level : Nat) :
    Convertible (typeTranslation (.sort level : CoreTerm n)) (.packageFamily level) :=
  .beta (.universeProjection level)

example :
    HasType Context.empty (.universePackage 0)
      (translatedUniversePackageType (n := 0) 0) :=
  universePackage_hasType_translatedUniverse .empty 0

example :
    Convertible (typeTranslation (.sort 0 : CoreTerm 0)) (.packageFamily 0) :=
  universeTypeTranslation_convertible 0

end DeepWiki.Refine.DependentCalculus.UnivalentParametricity
