import DeepWiki.Refine.Parametricity.Raw.Naturality
import DeepWiki.Refine.Parametricity.Univalent.Realizers

/-! # Univalent parametricity translation

Package-valued term translation and its projected relation-valued type translation. -/

namespace DeepWiki.Refine.DependentCalculus.UnivalentParametricity

/-- The translated scope has one original, one primed, and one witness variable per source variable. -/
abbrev scopeSize := RawParametricity.scopeSize

/-- Embed a core term into the original slots of its translated scope. -/
def original (term : CoreTerm n) : Term (scopeSize n) :=
  Term.ofCore (RawParametricity.original term)

/-- Embed a core term into the primed slots of its translated scope. -/
def primed (term : CoreTerm n) : Term (scopeSize n) :=
  Term.ofCore (RawParametricity.primed term)

/-- Embed a codomain under only its original endpoint binder. -/
def originalCodomain (codomain : CoreTerm (n + 1)) : Term (scopeSize n + 1) :=
  Term.ofCore
    (codomain.rename
      (DependentCalculus.Renaming.lift
        (RawParametricity.originalRenaming n)))

/-- Embed a codomain under only its primed endpoint binder. -/
def primedCodomain (codomain : CoreTerm (n + 1)) : Term (scopeSize n + 1) :=
  Term.ofCore
    (codomain.rename
      (DependentCalculus.Renaming.lift
        (RawParametricity.primedRenaming n)))

/-- Translate a core term to its package-valued univalent-parametricity witness. -/
def termTranslation : {n : Nat} → CoreTerm n → Term (scopeSize n)
  | _, .sort level => .universePackage level
  | n + 1, .var index => .var (RawParametricity.witnessRenaming (n + 1) index)
  | _, .app function argument =>
      .app (.app (.app (termTranslation function) (original argument))
        (primed argument)) (termTranslation argument)
  | _, .lam domain body =>
      .lam (original domain)
        (.lam ((primed domain).weakenBy 1)
          (.lam (Term.relatedDomain (termTranslation domain))
            (termTranslation body)))
  | n, .pi domain codomain =>
      .dependentProductPackage
        (original domain) (primed domain)
        (originalCodomain (n := n) codomain) (primedCodomain (n := n) codomain)
        (termTranslation domain) (termTranslation codomain)

/-- Translate a type by projecting the relation field of its package-valued translation. -/
def typeTranslation (type : CoreTerm n) : Term (scopeSize n) :=
  .relationProjection (termTranslation type)

/-- Apply a translated type relation to the original and primed copies of a term. -/
def relatedTermType (term type : CoreTerm n) : Term (scopeSize n) :=
  Term.relationApplication (typeTranslation type) (original term) (primed term)

/-- Translate a core context by adjoining its original, primed, and relation-witness entries. -/
def context : {n : Nat} → DependentCalculus.Context n → Context (scopeSize n)
  | 0, .empty => .empty
  | _ + 1, .extend source type =>
      .extend
        (.extend
          (.extend (context source) (original type))
          ((primed type).weakenBy 1))
        (Term.relatedDomain (termTranslation type))

/-- Translating a universe produces the concrete `p□` package. -/
@[simp] theorem termTranslation_sort (level : Nat) :
    termTranslation (.sort level : CoreTerm n) = .universePackage level :=
  rfl

/-- Translating a variable selects its relation-witness slot. -/
@[simp] theorem termTranslation_var (index : Fin n) :
    termTranslation (.var index) =
      .var (RawParametricity.witnessRenaming n index) := by
  cases n with
  | zero => exact Fin.elim0 index
  | succ => rfl

/-- Translating an application supplies original, primed, and witness arguments. -/
@[simp] theorem termTranslation_app (function argument : CoreTerm n) :
    termTranslation (.app function argument) =
      .app (.app (.app (termTranslation function) (original argument))
        (primed argument)) (termTranslation argument) :=
  rfl

/-- Translating a lambda binds original, primed, and projected-relation arguments. -/
@[simp] theorem termTranslation_lam (domain : CoreTerm n) (body : CoreTerm (n + 1)) :
    termTranslation (.lam domain body) =
      .lam (original domain)
        (.lam ((primed domain).weakenBy 1)
          (.lam (Term.relatedDomain (termTranslation domain))
            (termTranslation body))) :=
  rfl

/-- Translating a dependent product applies the concrete `pΠ` package constructor. -/
@[simp] theorem termTranslation_pi (domain : CoreTerm n)
    (codomain : CoreTerm (n + 1)) :
    termTranslation (.pi domain codomain) =
      .dependentProductPackage
        (original domain) (primed domain)
        (originalCodomain codomain) (primedCodomain codomain)
        (termTranslation domain) (termTranslation codomain) :=
  rfl

/-- The relation-valued translation is definitionally the projection of the term translation. -/
@[simp] theorem typeTranslation_eq (type : CoreTerm n) :
    typeTranslation type = .relationProjection (termTranslation type) :=
  rfl

/-- The empty context translates to the empty context. -/
@[simp] theorem context_empty :
    context (DependentCalculus.Context.empty) = Context.empty :=
  rfl

/-- Context translation replaces one declaration by its original, primed, and witness triple. -/
@[simp] theorem context_extend (source : DependentCalculus.Context n)
    (type : CoreTerm n) :
    context (.extend source type) =
      .extend
        (.extend
          (.extend (context source) (original type))
          ((primed type).weakenBy 1))
        (Term.relatedDomain (termTranslation type)) :=
  rfl

/-- Original-copy formation is natural with respect to relational renamings. -/
theorem original_rename (mapping : RawParametricity.RelationalRenaming source target)
    (term : CoreTerm source) :
    original (term.rename mapping.base) =
      (original term).rename mapping.relational := by
  simpa only [original, Term.ofCore_rename] using
    congrArg Term.ofCore (RawParametricity.original_rename mapping term)

/-- Primed-copy formation is natural with respect to relational renamings. -/
theorem primed_rename (mapping : RawParametricity.RelationalRenaming source target)
    (term : CoreTerm source) :
    primed (term.rename mapping.base) =
      (primed term).rename mapping.relational := by
  simpa only [primed, Term.ofCore_rename] using
    congrArg Term.ofCore (RawParametricity.primed_rename mapping term)

/-- Original one-binder codomain embedding is natural under relational renaming. -/
theorem originalCodomain_rename
    (mapping : RawParametricity.RelationalRenaming source target)
    (codomain : CoreTerm (source + 1)) :
    originalCodomain (codomain.rename
      (DependentCalculus.Renaming.lift mapping.base)) =
      (originalCodomain codomain).rename
        (DependentCalculus.Renaming.lift mapping.relational) := by
  unfold originalCodomain
  rw [← Term.ofCore_rename]
  simp only [DependentCalculus.Term.rename_comp]
  apply congrArg Term.ofCore
  apply DependentCalculus.Term.rename_congr
  funext index
  refine Fin.cases rfl ?_ index
  intro older
  exact congrArg Fin.succ (mapping.original_eq older).symm

/-- Primed one-binder codomain embedding is natural under relational renaming. -/
theorem primedCodomain_rename
    (mapping : RawParametricity.RelationalRenaming source target)
    (codomain : CoreTerm (source + 1)) :
    primedCodomain (codomain.rename
      (DependentCalculus.Renaming.lift mapping.base)) =
      (primedCodomain codomain).rename
        (DependentCalculus.Renaming.lift mapping.relational) := by
  unfold primedCodomain
  rw [← Term.ofCore_rename]
  simp only [DependentCalculus.Term.rename_comp]
  apply congrArg Term.ofCore
  apply DependentCalculus.Term.rename_congr
  funext index
  refine Fin.cases rfl ?_ index
  intro older
  exact congrArg Fin.succ (mapping.primed_eq older).symm

/-- The package-valued translation is natural with respect to relational renamings. -/
theorem termTranslation_rename
    (mapping : RawParametricity.RelationalRenaming source target)
    (term : CoreTerm source) :
    termTranslation (term.rename mapping.base) =
      (termTranslation term).rename mapping.relational := by
  induction term generalizing target with
  | sort => rfl
  | var index =>
      simp only [DependentCalculus.Term.rename, termTranslation_var]
      exact congrArg Term.var (mapping.witness_eq index).symm
  | app function argument functionInduction argumentInduction =>
      simp only [DependentCalculus.Term.rename, termTranslation_app,
        functionInduction mapping, argumentInduction mapping,
        original_rename mapping, primed_rename mapping, Term.rename]
  | lam domain body domainInduction bodyInduction =>
      have bodyNatural :
          termTranslation
              (body.rename
                (DependentCalculus.Renaming.lift mapping.base)) =
            (termTranslation body).rename
              (DependentCalculus.Renaming.lift
                (DependentCalculus.Renaming.lift
                  (DependentCalculus.Renaming.lift
                    mapping.relational))) := by
        simpa only [RawParametricity.RelationalRenaming.lift,
          RawParametricity.scopeSize] using bodyInduction mapping.lift
      simp only [DependentCalculus.Term.rename, termTranslation_lam,
        original_rename mapping, primed_rename mapping, domainInduction mapping,
        bodyNatural, Term.rename, Term.weakenBy_rename,
        Term.relatedDomain_rename, Renaming.liftBy]
  | pi domain codomain domainInduction codomainInduction =>
      have codomainNatural :
          termTranslation
              (codomain.rename
                (DependentCalculus.Renaming.lift mapping.base)) =
            (termTranslation codomain).rename
              (DependentCalculus.Renaming.lift
                (DependentCalculus.Renaming.lift
                  (DependentCalculus.Renaming.lift
                    mapping.relational))) := by
        simpa only [RawParametricity.RelationalRenaming.lift,
          RawParametricity.scopeSize] using codomainInduction mapping.lift
      simp only [DependentCalculus.Term.rename, termTranslation_pi,
        original_rename mapping, primed_rename mapping,
        originalCodomain_rename mapping, primedCodomain_rename mapping,
        domainInduction mapping, codomainNatural, Term.rename,
        Renaming.liftBy]

/-- The relation-valued translation is natural with respect to relational renamings. -/
theorem typeTranslation_rename
    (mapping : RawParametricity.RelationalRenaming source target)
    (type : CoreTerm source) :
    typeTranslation (type.rename mapping.base) =
      (typeTranslation type).rename mapping.relational := by
  simp only [typeTranslation, termTranslation_rename mapping, Term.rename]

/-- Weakening by one relational binder triple is the translated shift renaming. -/
theorem weakenBy_three_eq_rename_translatedShift
    (term : Term (scopeSize n)) :
    term.weakenBy 3 = term.rename (RawParametricity.translatedShift n) := by
  simp only [Term.weakenBy, Term.rename_comp]
  apply Term.rename_congr
  funext index
  rfl

/-- A source substitution together with its original, primed, and witness action. -/
structure RelationalSubstitution (source target : Nat) where
  /-- The substitution on source terms. -/
  base : DependentCalculus.Substitution source target
  /-- The substitution on triple-expanded relational terms. -/
  relational : Substitution (scopeSize source) (scopeSize target)
  /-- Original variable slots receive original copies of substituted terms. -/
  original_eq (index : Fin source) :
    relational (RawParametricity.originalRenaming source index) =
      original (base index)
  /-- Primed variable slots receive primed copies of substituted terms. -/
  primed_eq (index : Fin source) :
    relational (RawParametricity.primedRenaming source index) =
      primed (base index)
  /-- Witness variable slots receive translations of substituted terms. -/
  witness_eq (index : Fin source) :
    relational (RawParametricity.witnessRenaming source index) =
      termTranslation (base index)

namespace RelationalSubstitution

/-- Lift a relational substitution through one source binder and its translated triple. -/
def lift (mapping : RelationalSubstitution source target) :
    RelationalSubstitution (source + 1) (target + 1) where
  base := DependentCalculus.Substitution.lift mapping.base
  relational := Substitution.liftBy mapping.relational 3
  original_eq index := by
    refine Fin.cases rfl ?_ index
    intro older
    calc
      Substitution.liftBy mapping.relational 3
          (RawParametricity.originalRenaming (source + 1) older.succ) =
        (mapping.relational (RawParametricity.originalRenaming source older)).weakenBy 3 := rfl
      _ = (original (mapping.base older)).weakenBy 3 :=
        congrArg (fun term => term.weakenBy 3) (mapping.original_eq older)
      _ = (original (mapping.base older)).rename
          (RawParametricity.translatedShift target) :=
        weakenBy_three_eq_rename_translatedShift _
      _ = original ((mapping.base older).rename
          DependentCalculus.Renaming.shift) :=
        (original_rename (RawParametricity.relationalShift target)
          (mapping.base older)).symm
      _ = original
          (DependentCalculus.Substitution.lift mapping.base older.succ) := rfl
  primed_eq index := by
    refine Fin.cases rfl ?_ index
    intro older
    calc
      Substitution.liftBy mapping.relational 3
          (RawParametricity.primedRenaming (source + 1) older.succ) =
        (mapping.relational (RawParametricity.primedRenaming source older)).weakenBy 3 := rfl
      _ = (primed (mapping.base older)).weakenBy 3 :=
        congrArg (fun term => term.weakenBy 3) (mapping.primed_eq older)
      _ = (primed (mapping.base older)).rename
          (RawParametricity.translatedShift target) :=
        weakenBy_three_eq_rename_translatedShift _
      _ = primed ((mapping.base older).rename
          DependentCalculus.Renaming.shift) :=
        (primed_rename (RawParametricity.relationalShift target)
          (mapping.base older)).symm
      _ = primed
          (DependentCalculus.Substitution.lift mapping.base older.succ) := rfl
  witness_eq index := by
    refine Fin.cases rfl ?_ index
    intro older
    calc
      Substitution.liftBy mapping.relational 3
          (RawParametricity.witnessRenaming (source + 1) older.succ) =
        (mapping.relational (RawParametricity.witnessRenaming source older)).weakenBy 3 := rfl
      _ = (termTranslation (mapping.base older)).weakenBy 3 :=
        congrArg (fun term => term.weakenBy 3) (mapping.witness_eq older)
      _ = (termTranslation (mapping.base older)).rename
          (RawParametricity.translatedShift target) :=
        weakenBy_three_eq_rename_translatedShift _
      _ = termTranslation ((mapping.base older).rename
          DependentCalculus.Renaming.shift) :=
        (termTranslation_rename (RawParametricity.relationalShift target)
          (mapping.base older)).symm
      _ = termTranslation
          (DependentCalculus.Substitution.lift mapping.base older.succ) := rfl

end RelationalSubstitution

/-- Original-copy formation is natural with respect to relational substitutions. -/
theorem original_substitute
    (mapping : RelationalSubstitution source target)
    (term : CoreTerm source) :
    original (term.substitute mapping.base) =
      (original term).substitute mapping.relational := by
  unfold original RawParametricity.original
  rw [DependentCalculus.Term.rename_substitute,
    Term.ofCore_substitute, Term.ofCore_rename, Term.substitute_rename]
  apply Term.substitute_congr
  funext index
  rw [mapping.original_eq index]
  rfl

/-- Primed-copy formation is natural with respect to relational substitutions. -/
theorem primed_substitute
    (mapping : RelationalSubstitution source target)
    (term : CoreTerm source) :
    primed (term.substitute mapping.base) =
      (primed term).substitute mapping.relational := by
  unfold primed RawParametricity.primed
  rw [DependentCalculus.Term.rename_substitute,
    Term.ofCore_substitute, Term.ofCore_rename, Term.substitute_rename]
  apply Term.substitute_congr
  funext index
  rw [mapping.primed_eq index]
  rfl

/-- Original codomain formation is natural with respect to relational substitutions. -/
theorem originalCodomain_substitute
    (mapping : RelationalSubstitution source target)
    (term : CoreTerm (source + 1)) :
    originalCodomain
        (term.substitute
          (DependentCalculus.Substitution.lift mapping.base)) =
      (originalCodomain term).substitute
        (Substitution.lift mapping.relational) := by
  unfold originalCodomain
  rw [DependentCalculus.Term.rename_substitute,
    Term.ofCore_substitute, Term.ofCore_rename, Term.substitute_rename]
  apply Term.substitute_congr
  funext index
  refine Fin.cases rfl ?_ index
  intro older
  change Term.ofCore
      (((mapping.base older).rename
        DependentCalculus.Renaming.shift).rename
        (DependentCalculus.Renaming.lift
          (RawParametricity.originalRenaming target))) =
    (mapping.relational (RawParametricity.originalRenaming source older)).rename
      DependentCalculus.Renaming.shift
  rw [mapping.original_eq older]
  simp only [original, RawParametricity.original,
    DependentCalculus.Term.rename_comp, Term.ofCore_rename,
    Term.rename_comp]
  apply Term.rename_congr
  funext element
  rfl

/-- Primed codomain formation is natural with respect to relational substitutions. -/
theorem primedCodomain_substitute
    (mapping : RelationalSubstitution source target)
    (term : CoreTerm (source + 1)) :
    primedCodomain
        (term.substitute
          (DependentCalculus.Substitution.lift mapping.base)) =
      (primedCodomain term).substitute
        (Substitution.lift mapping.relational) := by
  unfold primedCodomain
  rw [DependentCalculus.Term.rename_substitute,
    Term.ofCore_substitute, Term.ofCore_rename, Term.substitute_rename]
  apply Term.substitute_congr
  funext index
  refine Fin.cases rfl ?_ index
  intro older
  change Term.ofCore
      (((mapping.base older).rename
        DependentCalculus.Renaming.shift).rename
        (DependentCalculus.Renaming.lift
          (RawParametricity.primedRenaming target))) =
    (mapping.relational (RawParametricity.primedRenaming source older)).rename
      DependentCalculus.Renaming.shift
  rw [mapping.primed_eq older]
  simp only [primed, RawParametricity.primed,
    DependentCalculus.Term.rename_comp, Term.ofCore_rename,
    Term.rename_comp]
  apply Term.rename_congr
  funext element
  rfl

/-- The package-valued translation is natural with respect to relational substitutions. -/
theorem termTranslation_substitute
    (mapping : RelationalSubstitution source target)
    (term : CoreTerm source) :
    termTranslation (term.substitute mapping.base) =
      (termTranslation term).substitute mapping.relational := by
  induction term generalizing target with
  | sort => rfl
  | var index =>
      simp only [DependentCalculus.Term.substitute,
        termTranslation_var, Term.substitute]
      exact (mapping.witness_eq index).symm
  | app function argument functionInduction argumentInduction =>
      simp only [DependentCalculus.Term.substitute,
        termTranslation, Term.substitute, functionInduction mapping,
        argumentInduction mapping, original_substitute mapping,
        primed_substitute mapping]
  | lam domain body domainInduction bodyInduction =>
      have bodyNatural :
          termTranslation
              (body.substitute
                (DependentCalculus.Substitution.lift mapping.base)) =
            (termTranslation body).substitute
              (Substitution.liftBy mapping.relational 3) := by
        exact bodyInduction mapping.lift
      simp only [DependentCalculus.Term.substitute,
        termTranslation, Term.substitute, original_substitute mapping,
        primed_substitute mapping, domainInduction mapping, bodyNatural,
        Term.weakenBy_substitute, Term.relatedDomain_substitute,
        Substitution.liftBy]
  | pi domain codomain domainInduction codomainInduction =>
      have codomainNatural :
          termTranslation
              (codomain.substitute
                (DependentCalculus.Substitution.lift mapping.base)) =
            (termTranslation codomain).substitute
              (Substitution.liftBy mapping.relational 3) := by
        exact codomainInduction mapping.lift
      simp only [DependentCalculus.Term.substitute,
        termTranslation, Term.substitute, original_substitute mapping,
        primed_substitute mapping, originalCodomain_substitute mapping,
        primedCodomain_substitute mapping, domainInduction mapping,
        codomainNatural]

/-- The relation-valued translation is natural with respect to relational substitutions. -/
theorem typeTranslation_substitute
    (mapping : RelationalSubstitution source target)
    (type : CoreTerm source) :
    typeTranslation (type.substitute mapping.base) =
      (typeTranslation type).substitute mapping.relational := by
  simp only [typeTranslation, Term.substitute,
    termTranslation_substitute mapping]

/-- Inserting the two function binders commutes with ambient renaming. -/
theorem insertTwoAfterThree_natural (mapping : Renaming source target) :
    DependentCalculus.Renaming.comp
        (insertTwoAfterThree (n := target)) (Renaming.liftBy mapping 3) =
      DependentCalculus.Renaming.comp
        (Renaming.liftBy mapping 5) (insertTwoAfterThree (n := source)) := by
  funext index
  refine Fin.cases rfl ?_ index
  intro oneOrOlder
  refine Fin.cases rfl ?_ oneOrOlder
  intro twoOrOlder
  refine Fin.cases rfl ?_ twoOrOlder
  intro older
  rfl

/-- The `pΠ` codomain package embedding is natural under ambient renaming. -/
theorem codomainPackage_rename
    (codomainPackage : Term (source + 3)) (mapping : Renaming source target) :
    (codomainPackage.rename (Renaming.liftBy mapping 3)).rename
        (insertTwoAfterThree (n := target)) =
      (codomainPackage.rename (insertTwoAfterThree (n := source))).rename
        (Renaming.liftBy mapping 5) := by
  simp only [Term.rename_comp]
  apply Term.rename_congr
  exact insertTwoAfterThree_natural mapping

/-- Threefold weakening followed by binder insertion is fivefold weakening. -/
theorem weakenBy_three_insertTwoAfterThree (term : Term n) :
    (term.weakenBy 3).rename (insertTwoAfterThree (n := n)) =
      term.weakenBy 5 := by
  simp only [Term.weakenBy, Term.rename_comp]
  apply Term.rename_congr
  funext index
  rfl

/-- Lifting a substitution commutes with insertion of the two function binders. -/
theorem liftBy_insertTwoAfterThree (mapping : Substitution source target) :
    (fun index =>
        (Substitution.liftBy mapping 3 index).rename
          (insertTwoAfterThree (n := target))) =
      (fun index =>
        Substitution.liftBy mapping 5
          (insertTwoAfterThree (n := source) index)) := by
  funext index
  refine Fin.cases rfl ?_ index
  intro oneOrOlder
  refine Fin.cases rfl ?_ oneOrOlder
  intro twoOrOlder
  refine Fin.cases rfl ?_ twoOrOlder
  intro older
  change ((mapping older).weakenBy 3).rename
      (insertTwoAfterThree (n := target)) = (mapping older).weakenBy 5
  exact weakenBy_three_insertTwoAfterThree _

/-- The `pΠ` codomain package embedding is natural under ambient substitution. -/
theorem codomainPackage_substitute
    (codomainPackage : Term (source + 3))
    (mapping : Substitution source target) :
    (codomainPackage.substitute (Substitution.liftBy mapping 3)).rename
        (insertTwoAfterThree (n := target)) =
      (codomainPackage.rename (insertTwoAfterThree (n := source))).substitute
        (Substitution.liftBy mapping 5) := by
  rw [Term.rename_substitute, Term.substitute_rename]
  apply Term.substitute_congr
  exact liftBy_insertTwoAfterThree mapping

/-- The projected dependent-product relation is natural under renaming. -/
theorem dependentProductRelation_rename
    (leftDomain rightDomain : Term source)
    (leftCodomain rightCodomain : Term (source + 1))
    (domainPackage : Term source) (codomainPackage : Term (source + 3))
    (mapping : Renaming source target) :
    Term.dependentProductRelation
        (leftDomain.rename mapping) (rightDomain.rename mapping)
        (leftCodomain.rename
          (DependentCalculus.Renaming.lift mapping))
        (rightCodomain.rename
          (DependentCalculus.Renaming.lift mapping))
        (domainPackage.rename mapping)
        (codomainPackage.rename (Renaming.liftBy mapping 3)) =
      (Term.dependentProductRelation leftDomain rightDomain leftCodomain
        rightCodomain domainPackage codomainPackage).rename mapping := by
  unfold Term.dependentProductRelation
  rw [show Term.pi (rightDomain.rename mapping)
      (rightCodomain.rename
        (DependentCalculus.Renaming.lift mapping)) =
      (Term.pi rightDomain rightCodomain).rename mapping from rfl]
  simp only [Term.weakenBy_rename]
  rw [codomainPackage_rename]
  simp only [Term.relationApplication, Term.rename,
    DependentCalculus.Renaming.lift_zero, Renaming.liftBy]
  rfl

/-- The projected dependent-product relation is natural under substitution. -/
theorem dependentProductRelation_substitute
    (leftDomain rightDomain : Term source)
    (leftCodomain rightCodomain : Term (source + 1))
    (domainPackage : Term source) (codomainPackage : Term (source + 3))
    (mapping : Substitution source target) :
    Term.dependentProductRelation
        (leftDomain.substitute mapping) (rightDomain.substitute mapping)
        (leftCodomain.substitute (Substitution.lift mapping))
        (rightCodomain.substitute (Substitution.lift mapping))
        (domainPackage.substitute mapping)
        (codomainPackage.substitute (Substitution.liftBy mapping 3)) =
      (Term.dependentProductRelation leftDomain rightDomain leftCodomain
        rightCodomain domainPackage codomainPackage).substitute mapping := by
  unfold Term.dependentProductRelation
  rw [show Term.pi (rightDomain.substitute mapping)
      (rightCodomain.substitute (Substitution.lift mapping)) =
      (Term.pi rightDomain rightCodomain).substitute mapping from rfl]
  simp only [Term.weakenBy_substitute]
  rw [codomainPackage_substitute]
  simp only [Term.relationApplication, Term.substitute, Substitution.lift,
    Substitution.liftBy]
  rfl

/-- Related-term types are natural with respect to relational renamings. -/
theorem relatedTermType_rename
    (mapping : RawParametricity.RelationalRenaming source target)
    (term type : CoreTerm source) :
    relatedTermType (term.rename mapping.base) (type.rename mapping.base) =
      (relatedTermType term type).rename mapping.relational := by
  simp only [relatedTermType, Term.relationApplication,
    typeTranslation_rename mapping, original_rename mapping,
    primed_rename mapping, Term.rename]

/-- Related-term types are natural with respect to relational substitutions. -/
theorem relatedTermType_substitute
    (mapping : RelationalSubstitution source target)
    (term type : CoreTerm source) :
    relatedTermType (term.substitute mapping.base) (type.substitute mapping.base) =
      (relatedTermType term type).substitute mapping.relational := by
  simp only [relatedTermType, Term.relationApplication,
    typeTranslation_substitute mapping, original_substitute mapping,
    primed_substitute mapping, Term.substitute]

/-- Substitute one source argument into its original, primed, and witness slots. -/
def relationalSingle (argument : CoreTerm n) : RelationalSubstitution (n + 1) n where
  base := DependentCalculus.Substitution.single argument
  relational :=
    Fin.cases (termTranslation argument)
      (Fin.cases (primed argument)
        (Fin.cases (original argument) Term.var))
  original_eq index := by
    refine Fin.cases rfl ?_ index
    intro older
    rfl
  primed_eq index := by
    refine Fin.cases rfl ?_ index
    intro older
    rfl
  witness_eq index := by
    refine Fin.cases rfl ?_ index
    intro older
    simp only [RawParametricity.witnessRenaming,
      DependentCalculus.Substitution.single_succ,
      termTranslation_var, RawParametricity.finCases_succ]

/-- Translation commutes with substituting the newest source variable. -/
theorem termTranslation_instantiate (body : CoreTerm (n + 1))
    (argument : CoreTerm n) :
    termTranslation (body.instantiate argument) =
      (termTranslation body).substitute (relationalSingle argument).relational := by
  simpa only [DependentCalculus.Term.instantiate,
    relationalSingle] using
    termTranslation_substitute (relationalSingle argument) body

/-- The original copy of a codomain factors through its one-binder endpoint embedding. -/
theorem original_eq_originalCodomain_rename (codomain : CoreTerm (n + 1)) :
    original codomain =
      (originalCodomain codomain).rename originalBinderRenaming := by
  unfold original originalCodomain RawParametricity.original
  rw [← Term.ofCore_rename]
  simp only [DependentCalculus.Term.rename_comp]
  apply congrArg Term.ofCore
  apply DependentCalculus.Term.rename_congr
  funext index
  refine Fin.cases rfl ?_ index
  intro older
  rfl

/-- The primed copy of a codomain factors through its one-binder endpoint embedding. -/
theorem primed_eq_primedCodomain_rename (codomain : CoreTerm (n + 1)) :
    primed codomain =
      (primedCodomain codomain).rename primedBinderRenaming := by
  unfold primed primedCodomain RawParametricity.primed
  rw [← Term.ofCore_rename]
  simp only [DependentCalculus.Term.rename_comp]
  apply congrArg Term.ofCore
  apply DependentCalculus.Term.rename_congr
  funext index
  refine Fin.cases rfl ?_ index
  intro older
  rfl

namespace Context

/-- Original-variable lookup in a translated context is the original source lookup. -/
theorem translated_lookup_original
    (source : DependentCalculus.Context n) (index : Fin n) :
    (context source).lookup (RawParametricity.originalRenaming n index) =
      original (source.lookup index) := by
  induction source with
  | empty => exact Fin.elim0 index
  | @extend n source type inductionHypothesis =>
      refine Fin.cases ?_ ?_ index
      · change (original type).weakenBy 3 =
          original (type.rename DependentCalculus.Renaming.shift)
        rw [weakenBy_three_eq_rename_translatedShift]
        exact (original_rename (RawParametricity.relationalShift n) type).symm
      · intro older
        change ((context source).lookup
            (RawParametricity.originalRenaming n older)).weakenBy 3 =
          original ((source.lookup older).rename
            DependentCalculus.Renaming.shift)
        rw [inductionHypothesis older, weakenBy_three_eq_rename_translatedShift]
        exact (original_rename (RawParametricity.relationalShift n)
          (source.lookup older)).symm

/-- Primed-variable lookup in a translated context is the primed source lookup. -/
theorem translated_lookup_primed
    (source : DependentCalculus.Context n) (index : Fin n) :
    (context source).lookup (RawParametricity.primedRenaming n index) =
      primed (source.lookup index) := by
  induction source with
  | empty => exact Fin.elim0 index
  | @extend n source type inductionHypothesis =>
      refine Fin.cases ?_ ?_ index
      · change (primed type).weakenBy 3 =
          primed (type.rename DependentCalculus.Renaming.shift)
        rw [weakenBy_three_eq_rename_translatedShift]
        exact (primed_rename (RawParametricity.relationalShift n) type).symm
      · intro older
        change ((context source).lookup
            (RawParametricity.primedRenaming n older)).weakenBy 3 =
          primed ((source.lookup older).rename
            DependentCalculus.Renaming.shift)
        rw [inductionHypothesis older, weakenBy_three_eq_rename_translatedShift]
        exact (primed_rename (RawParametricity.relationalShift n)
          (source.lookup older)).symm

/-- Witness-variable lookup in a translated context is its related source lookup type. -/
theorem translated_lookup_witness
    (source : DependentCalculus.Context n) (index : Fin n) :
    (context source).lookup (RawParametricity.witnessRenaming n index) =
      relatedTermType (.var index) (source.lookup index) := by
  induction source with
  | empty => exact Fin.elim0 index
  | @extend n source type inductionHypothesis =>
      refine Fin.cases ?_ ?_ index
      · change (Term.relatedDomain (termTranslation type)).rename
            DependentCalculus.Renaming.shift =
          relatedTermType (.var 0)
            (type.rename DependentCalculus.Renaming.shift)
        change Term.relationApplication ((typeTranslation type).weakenBy 3)
            (.var ⟨2, by simp [scopeSize]⟩)
            (.var ⟨1, by simp [scopeSize]⟩) =
          Term.relationApplication
            (typeTranslation
              (type.rename DependentCalculus.Renaming.shift))
            (.var ⟨2, by simp [scopeSize, RawParametricity.scopeSize]⟩)
            (.var ⟨1, by simp [scopeSize, RawParametricity.scopeSize]⟩)
        rw [weakenBy_three_eq_rename_translatedShift]
        exact congrArg (fun relation =>
          Term.relationApplication relation
            (.var ⟨2, by simp [scopeSize]⟩)
            (.var ⟨1, by simp [scopeSize]⟩))
          (typeTranslation_rename (RawParametricity.relationalShift n) type).symm
      · intro older
        change ((context source).lookup
            (RawParametricity.witnessRenaming n older)).weakenBy 3 =
          relatedTermType (.var older.succ)
            ((source.lookup older).rename
              DependentCalculus.Renaming.shift)
        rw [inductionHypothesis older, weakenBy_three_eq_rename_translatedShift]
        exact (relatedTermType_rename (RawParametricity.relationalShift n)
          (.var older) (source.lookup older)).symm

end Context

example :
    context (DependentCalculus.Context.empty) = Context.empty :=
  rfl

example (source : DependentCalculus.Context n)
    (type : CoreTerm n) :
    context (.extend source type) =
      .extend
        (.extend
          (.extend (context source) (original type))
          ((primed type).weakenBy 1))
        (Term.relatedDomain (termTranslation type)) :=
  rfl

example (level : Nat) :
    termTranslation (.sort level : CoreTerm n) = .universePackage level :=
  rfl

example (index : Fin n) :
    termTranslation (.var index) =
      .var (RawParametricity.witnessRenaming n index) :=
  termTranslation_var index

example (function argument : CoreTerm n) :
    termTranslation (.app function argument) =
      .app (.app (.app (termTranslation function) (original argument))
        (primed argument)) (termTranslation argument) :=
  rfl

example (domain : CoreTerm n) (body : CoreTerm (n + 1)) :
    termTranslation (.lam domain body) =
      .lam (original domain)
        (.lam ((primed domain).weakenBy 1)
          (.lam (Term.relatedDomain (termTranslation domain))
            (termTranslation body))) :=
  rfl

example (domain : CoreTerm n) (codomain : CoreTerm (n + 1)) :
    termTranslation (.pi domain codomain) =
      .dependentProductPackage
        (original domain) (primed domain)
        (originalCodomain codomain) (primedCodomain codomain)
        (termTranslation domain) (termTranslation codomain) :=
  rfl

example (type : CoreTerm n) :
    typeTranslation type = .relationProjection (termTranslation type) :=
  rfl

end DeepWiki.Refine.DependentCalculus.UnivalentParametricity
