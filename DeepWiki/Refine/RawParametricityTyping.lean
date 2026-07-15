import DeepWiki.Refine.RawParametricitySyntax

/-! # Typing the raw parametricity translation

The syntactic universe relation is typed inside the scoped dependent calculus. Full abstraction
is reduced to its structural context-translation and witness-typing core.
-/

set_option linter.defProp false

namespace DeepWiki.Refine.DependentCalculus.RawParametricity

/-- The beta-normal type of the raw relation interpreting a universe. -/
def sortRelationType (level : Nat) (n : Nat) : Term n :=
  .pi (.sort level)
    (.pi (.sort level) (.sort (level + 1)))

/-- The literal translated type appearing on the right of the raw universe typing equation. -/
def translatedSortType (level : Nat) (n : Nat) : Term (scopeSize n) :=
  .app
    (.app (translate (.sort (level + 1) : Term n)) (.sort level))
    (.sort level)

/-- The three-argument product body produced by translating a dependent product. -/
def piRelationBody (domain : Term n) (codomain : Term (n + 1)) :
    Term (scopeSize n + 2) :=
  .pi (weakenBy (original domain) 2)
    (.pi (weakenBy (primed domain) 3)
      (.pi
        (.app (.app (weakenBy (translate domain) 4) (.var 1)) (.var 0))
        (.app
          (.app ((translate codomain).rename insertTwoAfterThree)
            (.app (.var 4) (.var 2)))
          (.app (.var 3) (.var 1)))))

/-- The beta-normal relation type assigned to a translated dependent function. -/
def piRelationFiber (domain : Term n) (codomain : Term (n + 1))
    (function : Term n) : Term (scopeSize n) :=
  ((piRelationBody domain codomain).substitute
    (Substitution.lift (Substitution.single (original function)))).instantiate
      (primed function)

/-- Weakening after substitution equals substitution lifted beneath the fresh binders. -/
theorem weakenBy_substitute (term : Term source)
    (mapping : Substitution source target) (amount : Nat) :
    weakenBy (term.substitute mapping) amount =
      (weakenBy term amount).substitute (liftSubstitutionBy mapping amount) := by
  induction amount with
  | zero => rfl
  | succ amount inductionHypothesis =>
      simpa only [weakenBy, liftSubstitutionBy,
        Term.substitute_rename_shift_lift] using
          congrArg (fun value => value.rename Renaming.shift) inductionHypothesis

/-- Inserting two variables after three binders commutes with lifted substitution. -/
theorem insertTwoAfterThree_substitute_natural (term : Term (source + 3))
    (mapping : Substitution source target) :
    (term.substitute (liftSubstitutionBy mapping 3)).rename insertTwoAfterThree =
      (term.rename insertTwoAfterThree).substitute
        (liftSubstitutionBy mapping 5) := by
  simp only [Term.rename_substitute, Term.substitute_rename]
  apply Term.substitute_congr
  funext index
  refine Fin.cases rfl ?_ index
  intro index
  refine Fin.cases rfl ?_ index
  intro index
  refine Fin.cases rfl ?_ index
  intro older
  rw [show insertTwoAfterThree older.succ.succ.succ =
    older.succ.succ.succ.succ.succ by rfl]
  simp only [liftSubstitutionBy, Substitution.lift_succ, Term.rename_comp]
  apply Term.rename_congr
  funext element
  rfl

/-- Substitute the original and primed function copies for the two product-relation binders. -/
def functionCopySubstitution (function : Term n) :
    Substitution (scopeSize n + 2) (scopeSize n) :=
  Substitution.comp (Substitution.single (primed function))
    (Substitution.lift (Substitution.single (original function)))

/-- Function-copy substitution sends the newest variable to the primed function. -/
@[simp] theorem functionCopySubstitution_zero (function : Term n) :
    functionCopySubstitution function 0 = primed function :=
  rfl

/-- Function-copy substitution sends the second-newest variable to the original function. -/
@[simp] theorem functionCopySubstitution_one (function : Term n) :
    functionCopySubstitution function 1 = original function := by
  unfold functionCopySubstitution Substitution.comp
  change ((original function).rename Renaming.shift).substitute
    (Substitution.single (primed function)) = original function
  simpa only [Term.instantiate] using
    Term.instantiate_rename_shift (original function) (primed function)

/-- Function-copy substitution preserves every variable older than its two binders. -/
@[simp] theorem functionCopySubstitution_succ_succ (function : Term n)
    (index : Fin (scopeSize n)) :
    functionCopySubstitution function index.succ.succ = .var index :=
  rfl

/-- Removing two function binders from a doubly weakened term leaves the ambient term. -/
theorem substitute_functionCopies_weakenBy_two (term : Term (scopeSize n))
    (function : Term n) :
    (weakenBy term 2).substitute (functionCopySubstitution function) = term := by
  simp only [weakenBy, Term.substitute_rename]
  calc
    term.substitute
        (fun index => functionCopySubstitution function
          (Renaming.shift (Renaming.shift index))) =
      term.substitute Substitution.identity := by
        apply Term.substitute_congr
        funext index
        rfl
    _ = term := Term.substitute_identity term

/-- Removing two function binders commutes with any surrounding binders. -/
theorem substitute_lifted_functionCopies_weakenBy (term : Term (scopeSize n))
    (function : Term n) (amount : Nat) :
    (weakenBy (weakenBy term 2) amount).substitute
        (liftSubstitutionBy (functionCopySubstitution function) amount) =
      weakenBy term amount := by
  induction amount with
  | zero => exact substitute_functionCopies_weakenBy_two term function
  | succ amount inductionHypothesis =>
      simpa only [weakenBy, liftSubstitutionBy,
        Term.substitute_rename_shift_lift] using
          congrArg (fun value => value.rename Renaming.shift) inductionHypothesis

/-- Substituting two copies into a weakened binary relation applies it to those copies. -/
theorem substitute_binaryRelation_functionCopies (relation : Term (scopeSize n))
    (function : Term n) :
    (((Term.app (Term.app (weakenBy relation 2) (.var 1)) (.var 0)).substitute
        (Substitution.lift (Substitution.single (original function)))).substitute
      (Substitution.single (primed function))) =
        Term.app (Term.app relation (original function)) (primed function) := by
  rw [Term.substitute_comp]
  change (Term.app (Term.app (weakenBy relation 2) (.var 1)) (.var 0)).substitute
    (functionCopySubstitution function) = _
  simp only [Term.substitute, functionCopySubstitution_zero,
    functionCopySubstitution_one,
    substitute_functionCopies_weakenBy_two]

/-- Removing the inserted function binders restores the codomain translation's ambient scope. -/
theorem substitute_lifted_functionCopies_insertTwoAfterThree
    (term : Term (scopeSize n + 3)) (function : Term n) :
    (term.rename insertTwoAfterThree).substitute
        (liftSubstitutionBy (functionCopySubstitution function) 3) = term := by
  rw [Term.substitute_rename]
  rw [show
      (fun index =>
        liftSubstitutionBy (functionCopySubstitution function) 3
          (insertTwoAfterThree index)) = Substitution.identity by
    funext index
    refine Fin.cases rfl ?_ index
    intro index
    refine Fin.cases rfl ?_ index
    intro index
    refine Fin.cases rfl ?_ index
    intro older
    rfl]
  exact Term.substitute_identity term

/-- The sequential beta substitutions of a product relation compose into function-copy substitution. -/
theorem piRelationFiber_eq_substitute (domain : Term n) (codomain : Term (n + 1))
    (function : Term n) :
    piRelationFiber domain codomain function =
      (piRelationBody domain codomain).substitute
        (functionCopySubstitution function) := by
  unfold piRelationFiber functionCopySubstitution Term.instantiate
  exact Term.substitute_comp _ _ _

/-- The explicit three-argument normal form of a dependent function's relation fiber. -/
def piRelationFiberNormal (domain : Term n) (codomain : Term (n + 1))
    (function : Term n) : Term (scopeSize n) :=
  .pi (original domain)
    (.pi (weakenBy (primed domain) 1)
      (.pi
        (.app (.app (weakenBy (translate domain) 2) (.var 1)) (.var 0))
        (.app
          (.app (translate codomain)
            (.app (weakenBy (original function) 3) (.var 2)))
          (.app (weakenBy (primed function) 3) (.var 1)))))

/-- The substitution presentation of a product-relation fiber equals its explicit normal form. -/
theorem piRelationFiber_eq_normal (domain : Term n) (codomain : Term (n + 1))
    (function : Term n) :
    piRelationFiber domain codomain function =
      piRelationFiberNormal domain codomain function := by
  have originalDomain := substitute_lifted_functionCopies_weakenBy
    (original domain) function 0
  change (weakenBy (original domain) 2).substitute
    (functionCopySubstitution function) = original domain at originalDomain
  have primedDomain := substitute_lifted_functionCopies_weakenBy
    (primed domain) function 1
  change (weakenBy (primed domain) 3).substitute
    (Substitution.lift (functionCopySubstitution function)) =
      weakenBy (primed domain) 1 at primedDomain
  have domainRelation := substitute_lifted_functionCopies_weakenBy
    (translate domain) function 2
  change (weakenBy (translate domain) 4).substitute
    (Substitution.lift (Substitution.lift (functionCopySubstitution function))) =
      weakenBy (translate domain) 2 at domainRelation
  have codomainRelation :=
    substitute_lifted_functionCopies_insertTwoAfterThree
      (translate codomain) function
  change ((translate codomain).rename insertTwoAfterThree).substitute
    (Substitution.lift
      (Substitution.lift
        (Substitution.lift (functionCopySubstitution function)))) =
      translate codomain at codomainRelation
  have originalFunction :
      Substitution.lift
          (Substitution.lift
            (Substitution.lift (functionCopySubstitution function))) 4 =
        weakenBy (original function) 3 := by
    change (((functionCopySubstitution function 1).rename Renaming.shift).rename
      Renaming.shift).rename Renaming.shift = weakenBy (original function) 3
    rw [functionCopySubstitution_one]
    rfl
  have primedFunction :
      Substitution.lift
          (Substitution.lift
            (Substitution.lift (functionCopySubstitution function))) 3 =
        weakenBy (primed function) 3 := by
    change (((functionCopySubstitution function 0).rename Renaming.shift).rename
      Renaming.shift).rename Renaming.shift = weakenBy (primed function) 3
    rw [functionCopySubstitution_zero]
    rfl
  have domainOriginalVariable :
      Substitution.lift (Substitution.lift (functionCopySubstitution function)) 1 =
        (.var 1 : Term (scopeSize n + 2)) :=
    rfl
  have domainPrimedVariable :
      Substitution.lift (Substitution.lift (functionCopySubstitution function)) 0 =
        (.var 0 : Term (scopeSize n + 2)) :=
    rfl
  have codomainOriginalVariable :
      Substitution.lift
          (Substitution.lift
            (Substitution.lift (functionCopySubstitution function))) 2 =
        (.var 2 : Term (scopeSize n + 3)) :=
    rfl
  have codomainPrimedVariable :
      Substitution.lift
          (Substitution.lift
            (Substitution.lift (functionCopySubstitution function))) 1 =
        (.var 1 : Term (scopeSize n + 3)) :=
    rfl
  rw [piRelationFiber_eq_substitute]
  unfold piRelationBody piRelationFiberNormal
  simp only [Term.substitute]
  rw [originalDomain, primedDomain, domainRelation, codomainRelation,
    originalFunction, primedFunction, domainOriginalVariable,
    domainPrimedVariable, codomainOriginalVariable, codomainPrimedVariable]

/-- Translating a product exposes its two function arguments and product relation body. -/
theorem translate_pi_body (domain : Term n) (codomain : Term (n + 1)) :
    translate (.pi domain codomain) =
      .lam (original (.pi domain codomain))
        (.lam (weakenBy (primed (.pi domain codomain)) 1)
          (piRelationBody domain codomain)) :=
  rfl

/-- Eliminating a finite index at numeral one selects the first successor branch. -/
@[simp] theorem finCases_one {value : Sort u}
    (zero : value) (successor : Fin (n + 1) → value) :
    Fin.cases zero successor (1 : Fin (n + 2)) = successor 0 := by
  rw [show (1 : Fin (n + 2)) = Fin.succ 0 by apply Fin.ext; rfl]
  rfl

/-- Eliminating a finite index at numeral zero selects the zero branch. -/
@[simp] theorem finCases_zero {value : Sort u}
    (zero : value) (successor : Fin n → value) :
    Fin.cases zero successor (0 : Fin (n + 1)) = zero := by
  rw [show (0 : Fin (n + 1)) = ⟨0, Nat.zero_lt_succ n⟩ by apply Fin.ext; rfl]
  rfl

/-- Eliminating an explicit successor index selects the successor branch. -/
@[simp] theorem finCases_succ {value : Sort u}
    (zero : value) (successor : Fin n → value) (index : Fin n) :
    Fin.cases zero successor index.succ = successor index :=
  rfl

/-- Substituting into a one-step weakening cancels that weakening. -/
@[simp] theorem substitute_single_rename_shift (term argument : Term n) :
    (term.rename Renaming.shift).substitute (Substitution.single argument) = term := by
  simpa only [Term.instantiate] using Term.instantiate_rename_shift term argument

/-- The beta-normal universe-relation type inhabits the universe two levels above its inputs. -/
theorem sortRelationType_hasType {context : Context n}
    (contextWellFormed : WellFormed context) (level : Nat) :
    HasType context (sortRelationType level n) (.sort (level + 2)) := by
  unfold sortRelationType
  have firstSort : HasType context (.sort level) (.sort (level + 1)) :=
    .sort contextWellFormed level
  have firstContextWellFormed : WellFormed (.extend context (.sort level)) :=
    .extend contextWellFormed firstSort
  have secondSort :
      HasType (.extend context (.sort level)) (.sort level) (.sort (level + 1)) :=
    .sort firstContextWellFormed level
  have secondContextWellFormed :
      WellFormed (.extend (.extend context (.sort level)) (.sort level)) :=
    .extend firstContextWellFormed secondSort
  have resultSort :
      HasType (.extend (.extend context (.sort level)) (.sort level))
        (.sort (level + 1)) (.sort (level + 2)) :=
    .sort secondContextWellFormed (level + 1)
  have innerProduct :
      HasType (.extend context (.sort level))
        (.pi (.sort level) (.sort (level + 1))) (.sort (level + 2)) := by
    simpa only [Nat.max_eq_right (by omega : level + 1 ≤ level + 2)] using
      HasType.pi secondSort resultSort
  simpa only [Nat.max_eq_right (by omega : level + 1 ≤ level + 2)] using
    HasType.pi firstSort innerProduct

/-- The raw relation interpreting a universe has its beta-normal dependent-function type. -/
theorem sortRelation_hasType_normal {context : Context n}
    (contextWellFormed : WellFormed context) (level : Nat) :
    HasType context (sortRelation level n) (sortRelationType level n) := by
  unfold sortRelation sortRelationType
  have firstSort : HasType context (.sort level) (.sort (level + 1)) :=
    .sort contextWellFormed level
  have firstContextWellFormed : WellFormed (.extend context (.sort level)) :=
    .extend contextWellFormed firstSort
  have secondSort :
      HasType (.extend context (.sort level)) (.sort level) (.sort (level + 1)) :=
    .sort firstContextWellFormed level
  have secondContextWellFormed :
      WellFormed (.extend (.extend context (.sort level)) (.sort level)) :=
    .extend firstContextWellFormed secondSort
  have firstVariable :
      HasType (.extend (.extend context (.sort level)) (.sort level)) (.var 1)
        (.sort level) := by
    have variableWellTyped := HasType.var secondContextWellFormed (1 : Fin (n + 2))
    change HasType (.extend (.extend context (.sort level)) (.sort level)) (.var 1)
      (.sort level) at variableWellTyped
    exact variableWellTyped
  have firstVariableContextWellFormed :
      WellFormed
        (.extend (.extend (.extend context (.sort level)) (.sort level)) (.var 1)) :=
    .extend secondContextWellFormed firstVariable
  have secondVariable :
      HasType
        (.extend (.extend (.extend context (.sort level)) (.sort level)) (.var 1))
        (.var 1) (.sort level) := by
    have variableWellTyped :=
      HasType.var firstVariableContextWellFormed (1 : Fin (n + 3))
    change HasType
      (.extend (.extend (.extend context (.sort level)) (.sort level)) (.var 1))
      (.var 1) (.sort level) at variableWellTyped
    exact variableWellTyped
  have secondVariableContextWellFormed :
      WellFormed
        (.extend
          (.extend (.extend (.extend context (.sort level)) (.sort level)) (.var 1))
          (.var 1)) :=
    .extend firstVariableContextWellFormed secondVariable
  have resultSort :
      HasType
        (.extend
          (.extend (.extend (.extend context (.sort level)) (.sort level)) (.var 1))
          (.var 1))
        (.sort level) (.sort (level + 1)) :=
    .sort secondVariableContextWellFormed level
  have secondProduct :
      HasType
        (.extend (.extend (.extend context (.sort level)) (.sort level)) (.var 1))
        (.pi (.var 1) (.sort level)) (.sort (level + 1)) := by
    simpa only [Nat.max_eq_right (Nat.le_succ level)] using
      HasType.pi secondVariable resultSort
  have firstProduct :
      HasType (.extend (.extend context (.sort level)) (.sort level))
        (.pi (.var 1) (.pi (.var 1) (.sort level))) (.sort (level + 1)) := by
    simpa only [Nat.max_eq_right (Nat.le_succ level)] using
      HasType.pi firstVariable secondProduct
  have secondLambda :
      HasType (.extend context (.sort level))
        (.lam (.sort level) (.pi (.var 1) (.pi (.var 1) (.sort level))))
        (.pi (.sort level) (.sort (level + 1))) :=
    HasType.lam secondSort firstProduct
  exact HasType.lam firstSort secondLambda

/-- The literal translated universe type beta-reduces to its dependent-function normal form. -/
theorem translatedSortType_beta (level n : Nat) :
    Convertible (translatedSortType level n) (sortRelationType level (scopeSize n)) := by
  unfold translatedSortType
  rw [translate_sort]
  unfold sortRelation sortRelationType
  refine .trans (.beta (.appFunction (.beta _ _ _))) ?_
  exact .beta (.beta _ _ _)

/-- The literal translated universe type is itself a type two universe levels above its inputs. -/
theorem translatedSortType_hasType {context : Context (scopeSize n)}
    (contextWellFormed : WellFormed context) (level : Nat) :
    HasType context (translatedSortType level n) (.sort (level + 2)) := by
  have relationWellTyped := sortRelation_hasType_normal contextWellFormed (level + 1)
  have inputWellTyped : HasType context (.sort level) (.sort (level + 1)) :=
    .sort contextWellFormed level
  have firstApplication := HasType.app relationWellTyped inputWellTyped
  have secondApplication := HasType.app firstApplication inputWellTyped
  simpa only [translatedSortType, translate_sort, sortRelationType,
    Term.instantiate, Term.substitute, Substitution.single, Term.rename] using
    secondApplication

/-- The syntactic translation of a universe has the literal translated successor-universe type. -/
theorem translate_sort_hasType {context : Context (scopeSize n)}
    (contextWellFormed : WellFormed context) (level : Nat) :
    HasType context (translate (.sort level : Term n)) (translatedSortType level n) := by
  have relationWellTyped := sortRelation_hasType_normal contextWellFormed level
  have targetWellTyped := translatedSortType_hasType contextWellFormed level
  exact .conversion relationWellTyped targetWellTyped (translatedSortType_beta level n).symm

/-- In the empty context, raw universe translation satisfies the literal universe typing equation. -/
theorem rawUniverseTranslation_hasType (level : Nat) :
    HasType Context.empty (translate (.sort level : Term 0))
      (.app
        (.app (translate (.sort (level + 1) : Term 0)) (.sort level))
        (.sort level)) :=
  translate_sort_hasType (n := 0) (context := Context.empty) WellFormed.empty level

/-- Translation preserves well-formedness of the empty context. -/
theorem context_empty_wellFormed : WellFormed (context Context.empty) :=
  WellFormed.empty

/-- Weakening a source scope by one variable weakens its translated scope by one triple. -/
def translatedShift (n : Nat) : Renaming (scopeSize n) (scopeSize (n + 1)) :=
  fun index => index.succ.succ.succ

/-- A source renaming paired with its action on original, primed, and witness variables. -/
structure RelationalRenaming (source target : Nat) where
  /-- The underlying source-variable renaming. -/
  base : Renaming source target
  /-- The induced renaming between triple-expanded scopes. -/
  relational : Renaming (scopeSize source) (scopeSize target)
  /-- The induced renaming preserves original-variable slots. -/
  original_eq (index : Fin source) :
    relational (originalRenaming source index) = originalRenaming target (base index)
  /-- The induced renaming preserves primed-variable slots. -/
  primed_eq (index : Fin source) :
    relational (primedRenaming source index) = primedRenaming target (base index)
  /-- The induced renaming preserves witness-variable slots. -/
  witness_eq (index : Fin source) :
    relational (witnessRenaming source index) = witnessRenaming target (base index)

/-- Lift a relational renaming beneath one source binder and its translated variable triple. -/
def RelationalRenaming.lift (mapping : RelationalRenaming source target) :
    RelationalRenaming (source + 1) (target + 1) where
  base := Renaming.lift mapping.base
  relational :=
    Renaming.lift (Renaming.lift (Renaming.lift mapping.relational))
  original_eq index := by
    refine Fin.cases rfl ?_ index
    intro older
    exact congrArg Fin.succ (congrArg Fin.succ (congrArg Fin.succ (mapping.original_eq older)))
  primed_eq index := by
    refine Fin.cases rfl ?_ index
    intro older
    exact congrArg Fin.succ (congrArg Fin.succ (congrArg Fin.succ (mapping.primed_eq older)))
  witness_eq index := by
    refine Fin.cases rfl ?_ index
    intro older
    exact congrArg Fin.succ (congrArg Fin.succ (congrArg Fin.succ (mapping.witness_eq older)))

/-- Lift a variable renaming beneath a specified number of fresh binders. -/
def liftBy (mapping : Renaming source target) :
    (amount : Nat) → Renaming (source + amount) (target + amount)
  | 0 => mapping
  | amount + 1 => Renaming.lift (liftBy mapping amount)

/-- Weakening after renaming agrees with renaming beneath all fresh binders. -/
theorem weakenBy_rename (term : Term source) (mapping : Renaming source target)
    (amount : Nat) :
    weakenBy (term.rename mapping) amount =
      (weakenBy term amount).rename (liftBy mapping amount) := by
  induction amount with
  | zero => rfl
  | succ amount inductionHypothesis =>
      simp only [weakenBy, inductionHypothesis, Term.rename_comp, liftBy]
      apply Term.rename_congr
      funext index
      rfl

/-- Inserting two variables after three binders commutes with lifted renaming. -/
theorem insertTwoAfterThree_natural (mapping : Renaming source target) :
    Renaming.comp insertTwoAfterThree (liftBy mapping 3) =
      Renaming.comp (liftBy mapping 5) insertTwoAfterThree := by
  funext index
  refine Fin.cases rfl ?_ index
  intro index
  refine Fin.cases rfl ?_ index
  intro index
  refine Fin.cases rfl ?_ index
  intro older
  rfl

/-- One-variable weakening paired with the corresponding three-variable weakening. -/
def relationalShift (n : Nat) : RelationalRenaming n (n + 1) where
  base := Renaming.shift
  relational := translatedShift n
  original_eq _ := rfl
  primed_eq _ := rfl
  witness_eq _ := rfl

/-- Original-copy formation is natural with respect to relational renamings. -/
theorem original_rename (mapping : RelationalRenaming source target) (term : Term source) :
    original (term.rename mapping.base) =
      (original term).rename mapping.relational := by
  unfold original
  simp only [Term.rename_comp]
  apply Term.rename_congr
  funext index
  exact (mapping.original_eq index).symm

/-- Primed-copy formation is natural with respect to relational renamings. -/
theorem primed_rename (mapping : RelationalRenaming source target) (term : Term source) :
    primed (term.rename mapping.base) =
      (primed term).rename mapping.relational := by
  unfold primed
  simp only [Term.rename_comp]
  apply Term.rename_congr
  funext index
  exact (mapping.primed_eq index).symm

/-- Raw term translation is natural with respect to relational renamings. -/
theorem translate_rename (mapping : RelationalRenaming source target) (term : Term source) :
    translate (term.rename mapping.base) =
      (translate term).rename mapping.relational := by
  induction term generalizing target with
  | sort level => rfl
  | var index =>
      simp only [Term.rename, translate_var]
      exact congrArg Term.var (mapping.witness_eq index).symm
  | app function argument functionInduction argumentInduction =>
      simp only [Term.rename, translate_app, functionInduction mapping,
        argumentInduction mapping, original_rename mapping, primed_rename mapping]
  | lam domain body domainInduction bodyInduction =>
      have bodyNatural :
          translate (body.rename (Renaming.lift mapping.base)) =
            (translate body).rename
              (Renaming.lift (Renaming.lift (Renaming.lift mapping.relational))) := by
        simpa only [RelationalRenaming.lift, scopeSize] using bodyInduction mapping.lift
      simp only [Term.rename, translate_lam, original_rename mapping,
        primed_rename mapping, domainInduction mapping,
        bodyNatural, weakenBy_rename, liftBy, Renaming.lift_zero]
      rfl
  | pi domain codomain domainInduction codomainInduction =>
      have codomainNatural :
          translate (codomain.rename (Renaming.lift mapping.base)) =
            (translate codomain).rename
              (Renaming.lift (Renaming.lift (Renaming.lift mapping.relational))) := by
        simpa only [RelationalRenaming.lift, scopeSize] using codomainInduction mapping.lift
      have originalProductNatural :
          original
              (.pi (domain.rename mapping.base)
                (codomain.rename (Renaming.lift mapping.base))) =
            (original (.pi domain codomain)).rename mapping.relational := by
        simpa only [Term.rename] using original_rename mapping (.pi domain codomain)
      have primedProductNatural :
          primed
              (.pi (domain.rename mapping.base)
                (codomain.rename (Renaming.lift mapping.base))) =
            (primed (.pi domain codomain)).rename mapping.relational := by
        simpa only [Term.rename] using primed_rename mapping (.pi domain codomain)
      have insertionNatural :
          Renaming.comp insertTwoAfterThree
              (Renaming.lift (Renaming.lift (Renaming.lift mapping.relational))) =
            Renaming.comp
              (Renaming.lift
                (Renaming.lift
                  (Renaming.lift (Renaming.lift (Renaming.lift mapping.relational)))))
              insertTwoAfterThree := by
        simpa only [liftBy] using insertTwoAfterThree_natural mapping.relational
      simp only [Term.rename, translate_pi, original_rename mapping,
        primed_rename mapping, originalProductNatural, primedProductNatural,
        domainInduction mapping, codomainNatural, weakenBy_rename, liftBy,
        Renaming.lift_zero, Term.rename_comp]
      rw [insertionNatural]
      rfl

/-- Original-copy renaming commutes with one-variable weakening. -/
theorem original_rename_shift (term : Term n) :
    original (term.rename Renaming.shift) =
      (original term).rename (translatedShift n) := by
  exact original_rename (relationalShift n) term

/-- Primed-copy renaming commutes with one-variable weakening. -/
theorem primed_rename_shift (term : Term n) :
    primed (term.rename Renaming.shift) =
      (primed term).rename (translatedShift n) := by
  exact primed_rename (relationalShift n) term

/-- Weakening a translated term by one source variable equals relational shifting. -/
theorem weakenBy_three_eq_rename_translatedShift (term : Term (scopeSize n)) :
    weakenBy term 3 = term.rename (translatedShift n) := by
  change weakenBy term 3 = term.rename (fun index => index.succ.succ.succ)
  simp only [weakenBy]
  rw [Term.rename_comp, Term.rename_comp]
  apply Term.rename_congr
  funext index
  rfl

/-- A source substitution paired with its action on original, primed, and witness variables. -/
structure RelationalSubstitution (source target : Nat) where
  /-- The underlying source-term substitution. -/
  base : Substitution source target
  /-- The induced substitution between triple-expanded scopes. -/
  relational : Substitution (scopeSize source) (scopeSize target)
  /-- The induced substitution preserves original-variable slots. -/
  original_eq (index : Fin source) :
    relational (originalRenaming source index) = original (base index)
  /-- The induced substitution preserves primed-variable slots. -/
  primed_eq (index : Fin source) :
    relational (primedRenaming source index) = primed (base index)
  /-- The induced substitution sends witness slots to translated witnesses. -/
  witness_eq (index : Fin source) :
    relational (witnessRenaming source index) = translate (base index)

/-- Lift a relational substitution beneath one source binder and its translated variable triple. -/
def RelationalSubstitution.lift (mapping : RelationalSubstitution source target) :
    RelationalSubstitution (source + 1) (target + 1) where
  base := Substitution.lift mapping.base
  relational :=
    Substitution.lift
      (Substitution.lift (Substitution.lift mapping.relational))
  original_eq index := by
    refine Fin.cases rfl ?_ index
    intro older
    calc
      Substitution.lift
          (Substitution.lift (Substitution.lift mapping.relational))
          (originalRenaming (source + 1) older.succ) =
        weakenBy (mapping.relational (originalRenaming source older)) 3 := rfl
      _ = weakenBy (original (mapping.base older)) 3 :=
        congrArg (fun term => weakenBy term 3) (mapping.original_eq older)
      _ = (original (mapping.base older)).rename (translatedShift target) :=
        weakenBy_three_eq_rename_translatedShift _
      _ = original ((mapping.base older).rename Renaming.shift) :=
        (original_rename_shift _).symm
      _ = original (Substitution.lift mapping.base older.succ) := rfl
  primed_eq index := by
    refine Fin.cases rfl ?_ index
    intro older
    calc
      Substitution.lift
          (Substitution.lift (Substitution.lift mapping.relational))
          (primedRenaming (source + 1) older.succ) =
        weakenBy (mapping.relational (primedRenaming source older)) 3 := rfl
      _ = weakenBy (primed (mapping.base older)) 3 :=
        congrArg (fun term => weakenBy term 3) (mapping.primed_eq older)
      _ = (primed (mapping.base older)).rename (translatedShift target) :=
        weakenBy_three_eq_rename_translatedShift _
      _ = primed ((mapping.base older).rename Renaming.shift) :=
        (primed_rename_shift _).symm
      _ = primed (Substitution.lift mapping.base older.succ) := rfl
  witness_eq index := by
    refine Fin.cases rfl ?_ index
    intro older
    calc
      Substitution.lift
          (Substitution.lift (Substitution.lift mapping.relational))
          (witnessRenaming (source + 1) older.succ) =
        weakenBy (mapping.relational (witnessRenaming source older)) 3 := rfl
      _ = weakenBy (translate (mapping.base older)) 3 :=
        congrArg (fun term => weakenBy term 3) (mapping.witness_eq older)
      _ = (translate (mapping.base older)).rename (translatedShift target) :=
        weakenBy_three_eq_rename_translatedShift _
      _ = translate ((mapping.base older).rename Renaming.shift) :=
        (translate_rename (relationalShift target) (mapping.base older)).symm
      _ = translate (Substitution.lift mapping.base older.succ) := rfl

/-- Original-copy formation is natural with respect to relational substitutions. -/
theorem original_substitute (mapping : RelationalSubstitution source target)
    (term : Term source) :
    original (term.substitute mapping.base) =
      (original term).substitute mapping.relational := by
  unfold original
  simp only [Term.rename_substitute, Term.substitute_rename]
  apply Term.substitute_congr
  funext index
  exact (mapping.original_eq index).symm

/-- Primed-copy formation is natural with respect to relational substitutions. -/
theorem primed_substitute (mapping : RelationalSubstitution source target)
    (term : Term source) :
    primed (term.substitute mapping.base) =
      (primed term).substitute mapping.relational := by
  unfold primed
  simp only [Term.rename_substitute, Term.substitute_rename]
  apply Term.substitute_congr
  funext index
  exact (mapping.primed_eq index).symm

/-- Raw term translation is natural with respect to relational substitutions. -/
theorem translate_substitute (mapping : RelationalSubstitution source target)
    (term : Term source) :
    translate (term.substitute mapping.base) =
      (translate term).substitute mapping.relational := by
  induction term generalizing target with
  | sort level => rfl
  | var index =>
      simp only [Term.substitute, translate_var]
      exact (mapping.witness_eq index).symm
  | app function argument functionInduction argumentInduction =>
      simp only [Term.substitute, translate_app, functionInduction mapping,
        argumentInduction mapping, original_substitute mapping,
        primed_substitute mapping]
  | lam domain body domainInduction bodyInduction =>
      have bodyNatural :
          translate (body.substitute (Substitution.lift mapping.base)) =
            (translate body).substitute
              (Substitution.lift
                (Substitution.lift (Substitution.lift mapping.relational))) := by
        simpa only [RelationalSubstitution.lift, scopeSize] using
          bodyInduction mapping.lift
      simp only [Term.substitute, translate_lam, original_substitute mapping,
        primed_substitute mapping, domainInduction mapping, bodyNatural,
        weakenBy_substitute, liftSubstitutionBy]
      rw [show Substitution.lift (Substitution.lift mapping.relational) 1 =
          (.var 1 : Term (scopeSize target + 2)) by rfl,
        show Substitution.lift (Substitution.lift mapping.relational) 0 =
          (.var 0 : Term (scopeSize target + 2)) by rfl]
  | pi domain codomain domainInduction codomainInduction =>
      have codomainNatural :
          translate (codomain.substitute (Substitution.lift mapping.base)) =
            (translate codomain).substitute
              (Substitution.lift
                (Substitution.lift (Substitution.lift mapping.relational))) := by
        simpa only [RelationalSubstitution.lift, scopeSize] using
          codomainInduction mapping.lift
      have originalProductNatural :=
        original_substitute mapping (.pi domain codomain)
      have primedProductNatural :=
        primed_substitute mapping (.pi domain codomain)
      have originalProductNaturalExpanded := originalProductNatural
      have primedProductNaturalExpanded := primedProductNatural
      simp only [Term.substitute] at originalProductNaturalExpanded
      simp only [Term.substitute] at primedProductNaturalExpanded
      have insertionNatural :
          ((translate codomain).substitute
            (Substitution.lift
              (Substitution.lift (Substitution.lift mapping.relational)))).rename
                insertTwoAfterThree =
            ((translate codomain).rename insertTwoAfterThree).substitute
              (Substitution.lift
                (Substitution.lift
                  (Substitution.lift
                    (Substitution.lift
                      (Substitution.lift mapping.relational))))) := by
        simpa only [liftSubstitutionBy, scopeSize] using
          insertTwoAfterThree_substitute_natural (translate codomain)
            mapping.relational
      simp only [Term.substitute, translate_pi, original_substitute mapping,
        primed_substitute mapping, domainInduction mapping, codomainNatural,
        weakenBy_substitute, liftSubstitutionBy]
      rw [originalProductNaturalExpanded, primedProductNaturalExpanded]
      rw [weakenBy_substitute]
      simp only [liftSubstitutionBy]
      rw [insertionNatural]
      rw [show
          Substitution.lift
              (Substitution.lift
                (Substitution.lift
                  (Substitution.lift mapping.relational))) 1 =
            (.var 1 : Term (scopeSize target + 4)) by rfl,
        show
          Substitution.lift
              (Substitution.lift
                (Substitution.lift
                  (Substitution.lift mapping.relational))) 0 =
            (.var 0 : Term (scopeSize target + 4)) by rfl,
        show
          Substitution.lift
              (Substitution.lift
                (Substitution.lift
                  (Substitution.lift
                    (Substitution.lift mapping.relational)))) 4 =
            (.var 4 : Term (scopeSize target + 5)) by rfl,
        show
          Substitution.lift
              (Substitution.lift
                (Substitution.lift
                  (Substitution.lift
                    (Substitution.lift mapping.relational)))) 2 =
            (.var 2 : Term (scopeSize target + 5)) by rfl,
        show
          Substitution.lift
              (Substitution.lift
                (Substitution.lift
                  (Substitution.lift
                    (Substitution.lift mapping.relational)))) 3 =
            (.var 3 : Term (scopeSize target + 5)) by rfl,
        show
          Substitution.lift
              (Substitution.lift
                (Substitution.lift
                  (Substitution.lift
                    (Substitution.lift mapping.relational)))) 1 =
            (.var 1 : Term (scopeSize target + 5)) by rfl]

/-- Single substitution is paired with substitution of the corresponding variable triple. -/
def relationalSingle (argument : Term n) : RelationalSubstitution (n + 1) n where
  base := Substitution.single argument
  relational := Fin.cases (translate argument)
    (Fin.cases (primed argument) (Fin.cases (original argument) Term.var))
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
    simp only [witnessRenaming_succ, finCases_succ,
      Substitution.single_succ, translate_var]

/-- The argument-triple substitution with its source scope normalized to `scopeSize n + 3`. -/
def relationalSingleSubstitution (argument : Term n) :
    Substitution (scopeSize n + 3) (scopeSize n) :=
  Fin.cases (translate argument)
    (Fin.cases (primed argument) (Fin.cases (original argument) Term.var))

/-- Triple substitution sends its witness slot to the translated argument. -/
@[simp] theorem relationalSingle_zero (argument : Term n) :
    relationalSingleSubstitution argument (0 : Fin (scopeSize n + 3)) =
      translate argument :=
  rfl

/-- Triple substitution sends its primed slot to the primed argument. -/
@[simp] theorem relationalSingle_one (argument : Term n) :
    relationalSingleSubstitution argument (1 : Fin (scopeSize n + 3)) =
      primed argument :=
  rfl

/-- Triple substitution sends its original slot to the original argument. -/
@[simp] theorem relationalSingle_two (argument : Term n) :
    relationalSingleSubstitution argument (2 : Fin (scopeSize n + 3)) =
      original argument :=
  rfl

/-- Triple substitution preserves every variable older than its three argument slots. -/
@[simp] theorem relationalSingle_succ_succ_succ (argument : Term n)
    (index : Fin (scopeSize n)) :
    relationalSingleSubstitution argument index.succ.succ.succ = .var index :=
  rfl

/-- Triple substitution removes three weakenings from an ambient translated term. -/
theorem substitute_relationalSingle_weakenBy_three (term : Term (scopeSize n))
    (argument : Term n) :
    (weakenBy term 3).substitute (relationalSingleSubstitution argument) = term := by
  simp only [weakenBy]
  rw [Term.substitute_rename, Term.substitute_rename, Term.substitute_rename]
  have mapping_eq :
    (fun index => relationalSingleSubstitution argument
      (Renaming.shift (Renaming.shift (Renaming.shift index)))) =
        Substitution.identity := by
    funext index
    rfl
  exact (Term.substitute_congr mapping_eq term).trans
    (Term.substitute_identity term)

/-- Sequentially instantiating a relational triple equals its simultaneous substitution. -/
theorem substitute_relationalSingle (term : Term (scopeSize n + 3))
    (argument : Term n) :
    (((term.substitute
          (Substitution.lift
            (Substitution.lift (Substitution.single (original argument))))).substitute
        (Substitution.lift (Substitution.single (primed argument)))).substitute
      (Substitution.single (translate argument))) =
        term.substitute (relationalSingleSubstitution argument) := by
  rw [Term.substitute_comp, Term.substitute_comp]
  apply Term.substitute_congr
  funext index
  unfold Substitution.comp relationalSingleSubstitution
  refine Fin.cases ?_ ?_ index
  · rfl
  intro index
  refine Fin.cases ?_ ?_ index
  · change ((primed argument).rename Renaming.shift).substitute
      (Substitution.single (translate argument)) = primed argument
    exact substitute_single_rename_shift (primed argument) (translate argument)
  intro index
  refine Fin.cases ?_ ?_ index
  · simp only [Substitution.lift_succ, Substitution.single_zero]
    change (((original argument).rename Renaming.shift).rename Renaming.shift).substitute
      (Substitution.comp (Substitution.single (translate argument))
        (Substitution.lift (Substitution.single (primed argument)))) = original argument
    rw [← Term.substitute_comp, Term.substitute_rename_shift_lift,
      substitute_single_rename_shift, substitute_single_rename_shift]
  intro older
  rfl

/-- Raw translation commutes with single-variable instantiation. -/
theorem translate_instantiate (body : Term (n + 1)) (argument : Term n) :
    translate (body.instantiate argument) =
      (translate body).substitute (relationalSingle argument).relational := by
  change translate (body.substitute (Substitution.single argument)) = _
  exact translate_substitute (relationalSingle argument) body

/-- Raw translation commutes with instantiation in the normalized three-variable scope. -/
theorem translate_instantiate_normalized (body : Term (n + 1)) (argument : Term n) :
    translate (body.instantiate argument) =
      (translate body).substitute (relationalSingleSubstitution argument) :=
  translate_instantiate body argument

/-- Original-copy formation commutes with single-variable instantiation. -/
theorem original_instantiate (body : Term (n + 1)) (argument : Term n) :
    original (body.instantiate argument) =
      (original body).substitute (relationalSingle argument).relational := by
  change original (body.substitute (Substitution.single argument)) = _
  exact original_substitute (relationalSingle argument) body

/-- Primed-copy formation commutes with single-variable instantiation. -/
theorem primed_instantiate (body : Term (n + 1)) (argument : Term n) :
    primed (body.instantiate argument) =
      (primed body).substitute (relationalSingle argument).relational := by
  change primed (body.substitute (Substitution.single argument)) = _
  exact primed_substitute (relationalSingle argument) body

/-- Original-variable lookup in a translated context equals renaming the source lookup. -/
theorem context_lookup_original (source : Context n) (index : Fin n) :
    (context source).lookup (originalRenaming n index) =
      (source.lookup index).rename (originalRenaming n) := by
  induction source with
  | empty => exact Fin.elim0 index
  | @extend n source type inductionHypothesis =>
      refine Fin.cases ?_ ?_ index
      · change
          (((type.rename (originalRenaming n)).rename Renaming.shift).rename
              Renaming.shift).rename Renaming.shift =
            (type.rename Renaming.shift).rename (originalRenaming (n + 1))
        simp only [Term.rename_comp]
        apply Term.rename_congr
        funext older
        rfl
      · intro older
        change
          ((((context source).lookup (originalRenaming n older)).rename
              Renaming.shift).rename Renaming.shift).rename Renaming.shift =
            ((source.lookup older).rename Renaming.shift).rename
              (originalRenaming (n + 1))
        rw [inductionHypothesis older]
        simp only [Term.rename_comp]
        apply Term.rename_congr
        funext element
        rfl

/-- Primed-variable lookup in a translated context equals renaming the source lookup. -/
theorem context_lookup_primed (source : Context n) (index : Fin n) :
    (context source).lookup (primedRenaming n index) =
      (source.lookup index).rename (primedRenaming n) := by
  induction source with
  | empty => exact Fin.elim0 index
  | @extend n source type inductionHypothesis =>
      refine Fin.cases ?_ ?_ index
      · change
          (((type.rename (primedRenaming n)).rename Renaming.shift).rename
              Renaming.shift).rename Renaming.shift =
            (type.rename Renaming.shift).rename (primedRenaming (n + 1))
        simp only [Term.rename_comp]
        apply Term.rename_congr
        funext older
        rfl
      · intro older
        change
          ((((context source).lookup (primedRenaming n older)).rename
              Renaming.shift).rename Renaming.shift).rename Renaming.shift =
            ((source.lookup older).rename Renaming.shift).rename
              (primedRenaming (n + 1))
        rw [inductionHypothesis older]
        simp only [Term.rename_comp]
        apply Term.rename_congr
        funext element
        rfl

/-- Original-variable embedding is typed whenever the translated target context is well formed. -/
def originalTypedRenaming (source : Context n)
    (translatedWellFormed : WellFormed (context source)) :
    TypedRenaming source (context source) (originalRenaming n) where
  targetWellFormed := translatedWellFormed
  lookup_eq := context_lookup_original source

/-- Primed-variable embedding is typed whenever the translated target context is well formed. -/
def primedTypedRenaming (source : Context n)
    (translatedWellFormed : WellFormed (context source)) :
    TypedRenaming source (context source) (primedRenaming n) where
  targetWellFormed := translatedWellFormed
  lookup_eq := context_lookup_primed source

/-- Original-copy renaming preserves a typing derivation into a well-formed translated context. -/
theorem HasType.original {source : Context n} {term type : Term n}
    (termWellTyped : HasType source term type)
    (translatedWellFormed : WellFormed (context source)) :
    HasType (context source) (original term) (original type) :=
  termWellTyped.rename (originalTypedRenaming source translatedWellFormed)

/-- Primed-copy renaming preserves a typing derivation into a well-formed translated context. -/
theorem HasType.primed {source : Context n} {term type : Term n}
    (termWellTyped : HasType source term type)
    (translatedWellFormed : WellFormed (context source)) :
    HasType (context source) (primed term) (primed type) :=
  termWellTyped.rename (primedTypedRenaming source translatedWellFormed)

/-- The translated relation type asserting that two translated terms are related. -/
def relatedTermType (term type : Term n) : Term (scopeSize n) :=
  .app (.app (translate type) (original term)) (primed term)

/-- Codomain relation before substituting an application's original, primed, and witness triple. -/
def applicationRelationBody (function : Term n) (codomain : Term (n + 1)) :
    Term (scopeSize n + 3) :=
  .app
    (.app (translate codomain)
      (.app (weakenBy (original function) 3) (.var 2)))
    (.app (weakenBy (primed function) 3) (.var 1))

/-- Substituting an argument triple in a codomain relation gives the related application type. -/
theorem applicationRelationBody_substitute (function argument : Term n)
    (codomain : Term (n + 1)) :
    (applicationRelationBody function codomain).substitute
        (relationalSingleSubstitution argument) =
      relatedTermType (.app function argument) (codomain.instantiate argument) := by
  unfold applicationRelationBody relatedTermType
  rw [translate_instantiate_normalized]
  simp only [Term.substitute, original, primed, Term.rename]
  congr 1
  · congr 1
    · rw [substitute_relationalSingle_weakenBy_three]
      rfl
  · rw [substitute_relationalSingle_weakenBy_three]
    rfl

/-- The relation type of a translated dependent function beta-reduces to its product fiber. -/
theorem relatedTermType_pi_beta (function domain : Term n)
    (codomain : Term (n + 1)) :
    Convertible (relatedTermType function (.pi domain codomain))
      (piRelationFiber domain codomain function) := by
  unfold relatedTermType
  rw [translate_pi_body]
  unfold piRelationFiber
  refine .trans (.beta (.appFunction (.beta _ _ _))) ?_
  exact .beta (.beta _ _ _)

/-- Applying a triply weakened original lambda to its original-variable slot beta-reduces to the original body. -/
theorem weakened_original_lam_apply_beta (domain : Term n) (body : Term (n + 1)) :
    Convertible
      (.app (weakenBy (original (.lam domain body)) 3)
        (.var (2 : Fin (scopeSize n + 3))))
      (original body) := by
  refine .trans (.beta (.beta _ _ _)) ?_
  rw [show
      ((Term.rename (Renaming.lift Renaming.shift)
        (Term.rename (Renaming.lift Renaming.shift)
          (Term.rename (Renaming.lift Renaming.shift)
            (Term.rename (Renaming.lift (originalRenaming n)) body)))).instantiate
          (.var (2 : Fin (scopeSize n + 3)))) = original body by
    unfold Term.instantiate original
    simp only [Term.substitute_rename]
    rw [← Term.substitute_ofRenaming]
    apply Term.substitute_congr
    funext index
    refine Fin.cases rfl ?_ index
    intro older
    rfl]
  exact .refl _

/-- Instantiating the outer product-relation lambda exposes its primed-function lambda. -/
theorem instantiate_piRelation_secondLambda (function domain : Term n)
    (codomain : Term (n + 1)) :
    (Term.lam (weakenBy (primed (.pi domain codomain)) 1)
      (piRelationBody domain codomain)).instantiate (original function) =
        Term.lam (primed (.pi domain codomain))
          ((piRelationBody domain codomain).substitute
            (Substitution.lift (Substitution.single (original function)))) := by
  simp only [Term.instantiate, Term.substitute, weakenBy,
    substitute_single_rename_shift]

/-- A typed product translation makes its beta-normal relation fiber universe-typed. -/
theorem piRelationFiber_hasType_of_productTranslation {source : Context n}
    {function domain : Term n} {codomain : Term (n + 1)} {translationType : Term (scopeSize n)}
    (translatedWellFormed : WellFormed (context source))
    (functionWellTyped : HasType source function (.pi domain codomain))
    (translatedProductWellTyped :
      HasType (context source) (translate (.pi domain codomain)) translationType) :
    ∃ level,
      HasType (context source) (piRelationFiber domain codomain function)
        (.sort level) := by
  rw [translate_pi_body] at translatedProductWellTyped
  obtain ⟨_, _, _, secondLambdaWellTyped⟩ :=
    translatedProductWellTyped.lamComponents
  have secondLambdaInstantiated := secondLambdaWellTyped.instantiate
    translatedWellFormed (HasType.original functionWellTyped translatedWellFormed)
  rw [instantiate_piRelation_secondLambda] at secondLambdaInstantiated
  obtain ⟨_, _, _, relationBodyWellTyped⟩ :=
    secondLambdaInstantiated.lamComponents
  have relationFiberWellTyped := relationBodyWellTyped.instantiate
    translatedWellFormed (HasType.primed functionWellTyped translatedWellFormed)
  change HasType (context source) (piRelationFiber domain codomain function) _ at relationFiberWellTyped
  obtain ⟨domainLevel, codomainLevel, domainWellTyped, codomainWellTyped⟩ :=
    relationFiberWellTyped.piComponents
  exact ⟨max domainLevel codomainLevel,
    HasType.pi domainWellTyped codomainWellTyped⟩

/-- The beta-normal relation fiber of a translated dependent function is universe-typed. -/
theorem piRelationFiber_hasType {source : Context n} {function domain : Term n}
    {codomain : Term (n + 1)}
    (translatedWellFormed : WellFormed (context source))
    (functionWellTyped : HasType source function (.pi domain codomain))
    (functionWitness :
      HasType (context source) (translate function)
        (relatedTermType function (.pi domain codomain))) :
    ∃ level,
      HasType (context source) (piRelationFiber domain codomain function)
        (.sort level) := by
  obtain ⟨_, relationTypeWellTyped⟩ := functionWitness.typeWellTyped
  change HasType (context source)
    (.app (.app (translate (.pi domain codomain)) (original function))
      (primed function)) _ at relationTypeWellTyped
  obtain ⟨_, _, firstApplicationWellTyped, _⟩ :=
    relationTypeWellTyped.appComponents
  obtain ⟨_, _, translatedProductWellTyped, _⟩ :=
    firstApplicationWellTyped.appComponents
  exact piRelationFiber_hasType_of_productTranslation translatedWellFormed
    functionWellTyped translatedProductWellTyped

/-- Application preserves the witness-typing conclusion of raw abstraction. -/
theorem translate_app_witness_hasType {source : Context n}
    {function argument domain : Term n} {codomain : Term (n + 1)}
    (translatedWellFormed : WellFormed (context source))
    (functionWellTyped : HasType source function (.pi domain codomain))
    (argumentWellTyped : HasType source argument domain)
    (functionWitness :
      HasType (context source) (translate function)
        (relatedTermType function (.pi domain codomain)))
    (argumentWitness :
      HasType (context source) (translate argument)
        (relatedTermType argument domain)) :
    HasType (context source) (translate (.app function argument))
      (relatedTermType (.app function argument) (codomain.instantiate argument)) := by
  obtain ⟨_, relationFiberWellTyped⟩ :=
    piRelationFiber_hasType translatedWellFormed functionWellTyped functionWitness
  have functionWitnessNormal :
      HasType (context source) (translate function)
        (piRelationFiber domain codomain function) :=
    .conversion functionWitness relationFiberWellTyped
      (relatedTermType_pi_beta function domain codomain)
  rw [piRelationFiber_eq_normal] at functionWitnessNormal
  have appliedOriginal := HasType.app functionWitnessNormal
    (HasType.original argumentWellTyped translatedWellFormed)
  have primedDomainInstantiated :
      (weakenBy (primed domain) 1).substitute
          (Substitution.single (original argument)) =
        primed domain := by
    simpa only [weakenBy] using
      substitute_single_rename_shift (primed domain) (original argument)
  simp only [Term.instantiate, Term.substitute] at appliedOriginal
  rw [primedDomainInstantiated] at appliedOriginal
  have appliedPrimed := HasType.app appliedOriginal
    (HasType.primed argumentWellTyped translatedWellFormed)
  have relatedDomainInstantiated :=
    substitute_binaryRelation_functionCopies (translate domain) argument
  simp only [Term.substitute] at relatedDomainInstantiated
  simp only [Term.instantiate, Term.substitute] at appliedPrimed
  rw [relatedDomainInstantiated] at appliedPrimed
  have appliedWitness := HasType.app appliedPrimed argumentWitness
  have appliedWitnessBody :
      HasType (context source) (translate (.app function argument))
        ((((applicationRelationBody function codomain).substitute
            (Substitution.lift
              (Substitution.lift (Substitution.single (original argument))))).substitute
          (Substitution.lift (Substitution.single (primed argument)))).instantiate
            (translate argument)) := by
    simpa only [applicationRelationBody, translate_app, Term.substitute] using appliedWitness
  change HasType (context source) (translate (.app function argument))
    ((((applicationRelationBody function codomain).substitute
          (Substitution.lift
            (Substitution.lift (Substitution.single (original argument))))).substitute
        (Substitution.lift (Substitution.single (primed argument)))).substitute
      (Substitution.single (translate argument))) at appliedWitnessBody
  rw [substitute_relationalSingle, applicationRelationBody_substitute] at appliedWitnessBody
  exact appliedWitnessBody

/-- Related-term types are natural with respect to relational renamings. -/
theorem relatedTermType_rename (mapping : RelationalRenaming source target)
    (term type : Term source) :
    relatedTermType (term.rename mapping.base) (type.rename mapping.base) =
      (relatedTermType term type).rename mapping.relational := by
  simp only [relatedTermType, Term.rename, translate_rename mapping,
    original_rename mapping, primed_rename mapping]

/-- A translated context assigns every witness variable its related-term type. -/
theorem context_lookup_witness (source : Context n) (index : Fin n) :
    (context source).lookup (witnessRenaming n index) =
      relatedTermType (.var index) (source.lookup index) := by
  induction source with
  | empty => exact Fin.elim0 index
  | @extend n source type inductionHypothesis =>
      refine Fin.cases ?_ ?_ index
      · rw [show
          (context (.extend source type)).lookup (witnessRenaming (n + 1) 0) =
            .app (.app (weakenBy (translate type) 3)
              (.var (originalRenaming (n + 1) 0)))
              (.var (primedRenaming (n + 1) 0)) by
              rfl]
        rw [weakenBy_three_eq_rename_translatedShift]
        have translatedTypeNatural :
            (translate type).rename (translatedShift n) =
              translate (type.rename Renaming.shift) := by
          simpa only [relationalShift] using
            (translate_rename (relationalShift n) type).symm
        simpa only [relatedTermType, Context.lookup, original_var, primed_var,
          finCases_zero] using congrArg
            (fun relation =>
              Term.app (Term.app relation (.var (originalRenaming (n + 1) 0)))
                (.var (primedRenaming (n + 1) 0)))
            translatedTypeNatural
      · intro older
        rw [show
          (context (.extend source type)).lookup (witnessRenaming (n + 1) older.succ) =
            weakenBy ((context source).lookup (witnessRenaming n older)) 3 by
              rfl]
        rw [inductionHypothesis older, weakenBy_three_eq_rename_translatedShift]
        simpa only [relationalShift, Context.lookup, Term.rename,
          Renaming.shift, finCases_succ] using
          (relatedTermType_rename (relationalShift n) (.var older)
            (source.lookup older)).symm

/-- A translated universe relation applied to two translated types is itself universe-typed. -/
theorem relatedType_hasType {source : Context n} {type : Term n} {level : Nat}
    (translatedWellFormed : WellFormed (context source))
    (typeWellTyped : HasType source type (.sort level)) :
    HasType (context source) (relatedTermType type (.sort level))
      (.sort (level + 1)) := by
  have relationConstructor :
      HasType (context source) (translate (.sort level : Term n))
        (sortRelationType level (scopeSize n)) := by
    exact .conversion (translate_sort_hasType translatedWellFormed level)
      (sortRelationType_hasType translatedWellFormed level)
      (translatedSortType_beta level n)
  have originalType := HasType.original typeWellTyped translatedWellFormed
  have primedType := HasType.primed typeWellTyped translatedWellFormed
  have firstApplication := HasType.app relationConstructor originalType
  have secondApplication := HasType.app firstApplication primedType
  simpa only [relatedTermType, sortRelationType, Term.instantiate, Term.substitute,
    Substitution.single, Term.rename] using secondApplication

/-- The beta-normal relation type between elements of two translated copies of a type. -/
def elementRelationType (type : Term n) (level : Nat) : Term (scopeSize n) :=
  .pi (original type)
    (.pi (weakenBy (primed type) 1) (.sort level))

/-- The translated universe relation at a type beta-reduces to its element-relation type. -/
theorem relatedTermType_sort_beta (type : Term n) (level : Nat) :
    Convertible (relatedTermType type (.sort level))
      (elementRelationType type level) := by
  unfold relatedTermType elementRelationType
  rw [translate_sort]
  unfold sortRelation
  refine .trans (.beta (.appFunction (.beta _ _ _))) ?_
  refine .trans (.beta (.beta _ _ _)) ?_
  simp only [Term.instantiate, Term.substitute, Substitution.single, Substitution.lift,
    finCases_one, finCases_zero, Term.rename,
    substitute_single_rename_shift, weakenBy]
  exact .refl _

/-- Applying a triply weakened primed lambda to its primed-variable slot beta-reduces to the primed body. -/
theorem weakened_primed_lam_apply_beta (domain : Term n) (body : Term (n + 1)) :
    Convertible
      (.app (weakenBy (primed (.lam domain body)) 3)
        (.var (1 : Fin (scopeSize n + 3))))
      (primed body) := by
  refine .trans (.beta (.beta _ _ _)) ?_
  rw [show
      ((Term.rename (Renaming.lift Renaming.shift)
        (Term.rename (Renaming.lift Renaming.shift)
          (Term.rename (Renaming.lift Renaming.shift)
            (Term.rename (Renaming.lift (primedRenaming n)) body)))).instantiate
          (.var (1 : Fin (scopeSize n + 3)))) = primed body by
    unfold Term.instantiate primed
    simp only [Term.substitute_rename]
    rw [← Term.substitute_ofRenaming]
    apply Term.substitute_congr
    funext index
    refine Fin.cases rfl ?_ index
    intro older
    rfl]
  exact .refl _

/-- The output relation in a lambda fiber beta-reduces to the relation between its bodies. -/
theorem lambdaRelationBody_beta (domain : Term n) (body codomain : Term (n + 1)) :
    Convertible (applicationRelationBody (.lam domain body) codomain)
      (relatedTermType body codomain) := by
  unfold applicationRelationBody relatedTermType
  have originalBeta := weakened_original_lam_apply_beta domain body
  have primedBeta := weakened_primed_lam_apply_beta domain body
  exact (originalBeta.app_argument.app_function).trans primedBeta.app_argument

/-- The element-relation type is well typed whenever its source type is. -/
theorem elementRelationType_hasType {source : Context n} {type : Term n} {level : Nat}
    (translatedWellFormed : WellFormed (context source))
    (typeWellTyped : HasType source type (.sort level)) :
    HasType (context source) (elementRelationType type level)
      (.sort (level + 1)) := by
  have originalType := HasType.original typeWellTyped translatedWellFormed
  have firstWellFormed : WellFormed (.extend (context source) (original type)) :=
    .extend translatedWellFormed originalType
  have primedType := HasType.primed typeWellTyped translatedWellFormed
  have weakenedPrimedType := primedType.weaken firstWellFormed
  have secondWellFormed :
      WellFormed
        (.extend (.extend (context source) (original type))
          (weakenBy (primed type) 1)) := by
    simpa only [weakenBy, primed, Term.rename] using
      WellFormed.extend firstWellFormed weakenedPrimedType
  have resultSort :
      HasType
        (.extend (.extend (context source) (original type))
          (weakenBy (primed type) 1))
        (.sort level) (.sort (level + 1)) :=
    .sort secondWellFormed level
  have innerProduct := HasType.pi
    (by simpa only [weakenBy, primed, Term.rename] using weakenedPrimedType)
    resultSort
  have outerProduct := HasType.pi originalType innerProduct
  simpa only [elementRelationType, Nat.max_eq_right (Nat.le_succ level)] using outerProduct

/-- A translated source type has its beta-normal binary element-relation type. -/
theorem translate_type_hasType_normal {source : Context n} {type : Term n} {level : Nat}
    (translatedWellFormed : WellFormed (context source))
    (typeWellTyped : HasType source type (.sort level))
    (witnessWellTyped :
      HasType (context source) (translate type) (relatedTermType type (.sort level))) :
    HasType (context source) (translate type) (elementRelationType type level) :=
  .conversion witnessWellTyped
    (elementRelationType_hasType translatedWellFormed typeWellTyped)
    (relatedTermType_sort_beta type level)

/-- Instantiating through two lifted weakenings removes the innermost unused binder. -/
theorem instantiate_double_lift_shift (term : Term n) :
    (((term.rename Renaming.shift).rename (Renaming.lift Renaming.shift)).rename
        (Renaming.lift Renaming.shift)).instantiate (.var 1) =
      (term.rename Renaming.shift).rename Renaming.shift := by
  unfold Term.instantiate
  simp only [Term.substitute_rename]
  rw [Term.rename_comp, ← Term.substitute_ofRenaming]
  apply Term.substitute_congr
  funext index
  rfl

/-- Instantiating a weakened constant product normalizes its independent domain. -/
theorem instantiate_pi_double_lift_shift (term : Term n) (level : Nat) :
    (Term.pi
      (((term.rename Renaming.shift).rename (Renaming.lift Renaming.shift)).rename
        (Renaming.lift Renaming.shift))
      (.sort level)).instantiate (.var 1) =
      Term.pi ((term.rename Renaming.shift).rename Renaming.shift) (.sort level) := by
  unfold Term.instantiate
  simp only [Term.substitute]
  rw [show
      (((term.rename Renaming.shift).rename (Renaming.lift Renaming.shift)).rename
        (Renaming.lift Renaming.shift)).substitute (Substitution.single (.var 1)) =
        (term.rename Renaming.shift).rename Renaming.shift by
      simpa only [Term.instantiate] using instantiate_double_lift_shift term]

/-- A translated context extension is well formed once the source type witness is typed. -/
theorem context_extend_wellFormed {source : Context n} {type : Term n} {level : Nat}
    (translatedWellFormed : WellFormed (context source))
    (typeWellTyped : HasType source type (.sort level))
    (witnessWellTyped :
      HasType (context source) (translate type) (relatedTermType type (.sort level))) :
    WellFormed (context (.extend source type)) := by
  have originalType := HasType.original typeWellTyped translatedWellFormed
  have firstWellFormed : WellFormed (.extend (context source) (original type)) :=
    .extend translatedWellFormed originalType
  have primedType := HasType.primed typeWellTyped translatedWellFormed
  have weakenedPrimedType := primedType.weaken firstWellFormed
  have secondWellFormed :
      WellFormed
        (.extend (.extend (context source) (original type))
          (weakenBy (primed type) 1)) := by
    simpa only [weakenBy, primed, Term.rename] using
      WellFormed.extend firstWellFormed weakenedPrimedType
  have relationWellTyped :=
    translate_type_hasType_normal translatedWellFormed typeWellTyped witnessWellTyped
  have relationWeakenedOnce := relationWellTyped.weaken firstWellFormed
  have relationWeakenedTwice := relationWeakenedOnce.weaken secondWellFormed
  have originalVariable := HasType.var secondWellFormed (1 : Fin (scopeSize n + 2))
  have firstApplicationRaw := HasType.app relationWeakenedTwice originalVariable
  have firstApplication :
      HasType
        (.extend (.extend (context source) (original type))
          (weakenBy (primed type) 1))
        (.app (weakenBy (translate type) 2) (.var 1))
        (.pi (weakenBy (primed type) 2) (.sort level)) := by
    simpa only [elementRelationType, weakenBy, Term.rename, Context.lookup,
      instantiate_pi_double_lift_shift] using
        firstApplicationRaw
  have primedVariable := HasType.var secondWellFormed (0 : Fin (scopeSize n + 2))
  have witnessTypeWellTyped := HasType.app firstApplication primedVariable
  simpa only [context_extend, scopeSize, elementRelationType, weakenBy, Term.rename,
    Context.lookup, Term.instantiate, Term.substitute, Substitution.single,
    Substitution.lift, finCases_zero, finCases_one,
    substitute_single_rename_shift] using
      WellFormed.extend secondWellFormed witnessTypeWellTyped

/-- Applying an inserted original function copy yields the inserted original codomain. -/
theorem original_codomain_insert_target (codomain : Term (n + 1)) :
    ((codomain.rename (Renaming.lift (originalRenaming n))).rename
          (Renaming.lift Renaming.shift) |>.rename
          (Renaming.lift Renaming.shift) |>.rename
          (Renaming.lift Renaming.shift) |>.rename
          (Renaming.lift Renaming.shift) |>.rename
          (Renaming.lift Renaming.shift) |>.instantiate (.var 2)) =
      (original codomain).rename
        (Renaming.lift (Renaming.lift (Renaming.lift
          (Renaming.comp Renaming.shift Renaming.shift)))) := by
  change _ = (codomain.rename (originalRenaming (n + 1))).rename
    (Renaming.lift (Renaming.lift (Renaming.lift
      (Renaming.comp Renaming.shift Renaming.shift))))
  rw [show
    (codomain.rename (originalRenaming (n + 1))).rename
        (Renaming.lift (Renaming.lift (Renaming.lift
          (Renaming.comp Renaming.shift Renaming.shift)))) =
      codomain.rename
        (Renaming.comp
          (Renaming.lift (Renaming.lift (Renaming.lift
            (Renaming.comp Renaming.shift Renaming.shift))))
          (originalRenaming (n + 1))) by
      exact Term.rename_comp _ _ _]
  unfold Term.instantiate
  simp only [Term.substitute_rename, Term.rename_comp]
  rw [← Term.substitute_ofRenaming]
  apply Term.substitute_congr
  funext index
  refine Fin.cases rfl ?_ index
  intro older
  rfl

/-- Applying an inserted primed function copy yields the inserted primed codomain. -/
theorem primed_codomain_insert_target (codomain : Term (n + 1)) :
    ((codomain.rename (Renaming.lift (primedRenaming n))).rename
          (Renaming.lift Renaming.shift) |>.rename
          (Renaming.lift Renaming.shift) |>.rename
          (Renaming.lift Renaming.shift) |>.rename
          (Renaming.lift Renaming.shift) |>.rename
          (Renaming.lift Renaming.shift) |>.instantiate (.var 1)) =
      (primed codomain).rename
        (Renaming.lift (Renaming.lift (Renaming.lift
          (Renaming.comp Renaming.shift Renaming.shift)))) := by
  change _ = (codomain.rename (primedRenaming (n + 1))).rename
    (Renaming.lift (Renaming.lift (Renaming.lift
      (Renaming.comp Renaming.shift Renaming.shift))))
  rw [show
    (codomain.rename (primedRenaming (n + 1))).rename
        (Renaming.lift (Renaming.lift (Renaming.lift
          (Renaming.comp Renaming.shift Renaming.shift)))) =
      codomain.rename
        (Renaming.comp
          (Renaming.lift (Renaming.lift (Renaming.lift
            (Renaming.comp Renaming.shift Renaming.shift))))
          (primedRenaming (n + 1))) by
      exact Term.rename_comp _ _ _]
  unfold Term.instantiate
  simp only [Term.substitute_rename, Term.rename_comp]
  rw [← Term.substitute_ofRenaming]
  apply Term.substitute_congr
  funext index
  refine Fin.cases rfl ?_ index
  intro older
  rfl

/-- Instantiation cancels weakening transported beneath an arbitrary renaming. -/
theorem instantiate_renamed_weakenBy_one (term : Term source)
    (mapping : Renaming source target) (argument : Term target) :
    ((term.rename Renaming.shift).rename (Renaming.lift mapping)).instantiate argument =
      term.rename mapping := by
  unfold Term.instantiate
  simp only [Term.substitute_rename, Term.rename_comp]
  rw [← Term.substitute_ofRenaming]
  apply Term.substitute_congr
  funext index
  rfl

/-- Single substitution cancels weakening transported beneath an arbitrary renaming. -/
theorem substitute_renamed_weakenBy_one (term : Term source)
    (mapping : Renaming source target) (argument : Term target) :
    ((term.rename Renaming.shift).rename (Renaming.lift mapping)).substitute
        (Substitution.single argument) = term.rename mapping := by
  simpa only [Term.instantiate] using
    instantiate_renamed_weakenBy_one term mapping argument

/-- Instantiating the inserted primed codomain removes its unused original-output binder. -/
theorem substitute_inserted_primed_codomain (codomain : Term (n + 1))
    (argument : Term (scopeSize n + 5)) :
    ((weakenBy (primed codomain) 1).rename
      (Renaming.lift (Renaming.lift (Renaming.lift (Renaming.lift
        (Renaming.comp Renaming.shift Renaming.shift)))))).substitute
        (Substitution.single argument) =
      (primed codomain).rename
        (Renaming.lift (Renaming.lift (Renaming.lift
          (Renaming.comp Renaming.shift Renaming.shift)))) := by
  simpa only [weakenBy, scopeSize, Nat.add_assoc] using
    substitute_renamed_weakenBy_one (primed codomain)
      (Renaming.lift (Renaming.lift (Renaming.lift
        (Renaming.comp Renaming.shift Renaming.shift)))) argument

/-- The body of a translated dependent-product relation has the source product's universe level. -/
theorem piRelationBody_hasType {source : Context n}
    {domain : Term n} {codomain : Term (n + 1)}
    {domainLevel codomainLevel : Nat}
    (translatedWellFormed : WellFormed (context source))
    (domainWellTyped : HasType source domain (.sort domainLevel))
    (codomainWellTyped :
      HasType (.extend source domain) codomain (.sort codomainLevel))
    (domainWitness :
      HasType (context source) (translate domain)
        (relatedTermType domain (.sort domainLevel)))
    (codomainWitness :
      HasType (context (.extend source domain)) (translate codomain)
        (relatedTermType codomain (.sort codomainLevel))) :
    HasType
      (.extend
        (.extend (context source) (original (.pi domain codomain)))
        (weakenBy (primed (.pi domain codomain)) 1))
      (piRelationBody domain codomain)
      (.sort (max domainLevel codomainLevel)) := by
  have productWellTyped := HasType.pi domainWellTyped codomainWellTyped
  have originalProduct := HasType.original productWellTyped translatedWellFormed
  have firstWellFormed := WellFormed.extend translatedWellFormed originalProduct
  have primedProduct := HasType.primed productWellTyped translatedWellFormed
  have primedProductWeakened := primedProduct.weaken firstWellFormed
  have secondWellFormed :
      WellFormed
        (.extend
          (.extend (context source) (original (.pi domain codomain)))
          (weakenBy (primed (.pi domain codomain)) 1)) := by
    simpa only [weakenBy, primed, Term.rename] using
      WellFormed.extend firstWellFormed primedProductWeakened
  have baseInsertion :
      TypedRenaming (context source)
        (.extend
          (.extend (context source) (original (.pi domain codomain)))
          (weakenBy (primed (.pi domain codomain)) 1))
        (Renaming.comp Renaming.shift Renaming.shift) := by
    exact TypedRenaming.comp (TypedRenaming.shift secondWellFormed)
      (TypedRenaming.shift firstWellFormed)
  have originalDomain := HasType.original domainWellTyped translatedWellFormed
  have originalDomainInserted :
      HasType
        (.extend
          (.extend (context source) (original (.pi domain codomain)))
          (weakenBy (primed (.pi domain codomain)) 1))
        ((original domain).rename (Renaming.comp Renaming.shift Renaming.shift))
        (.sort domainLevel) := by
    simpa only [original, Term.rename] using originalDomain.rename baseInsertion
  let insertionOne := baseInsertion.lift originalDomainInserted
  have sourceFirstWellFormed := WellFormed.extend translatedWellFormed originalDomain
  have primedDomain := HasType.primed domainWellTyped translatedWellFormed
  have primedDomainSource :
      HasType (.extend (context source) (original domain))
        (weakenBy (primed domain) 1) (.sort domainLevel) := by
    simpa only [weakenBy, primed, Term.rename] using
      primedDomain.weaken sourceFirstWellFormed
  have sourceSecondWellFormed :=
    WellFormed.extend sourceFirstWellFormed primedDomainSource
  have primedDomainInserted := primedDomainSource.rename insertionOne
  let insertionTwo := insertionOne.lift primedDomainInserted
  have relationDomainSource :
      HasType
        (.extend (.extend (context source) (original domain))
          (weakenBy (primed domain) 1))
        (.app (.app (weakenBy (translate domain) 2) (.var 1)) (.var 0))
        (.sort domainLevel) := by
    have relationWellTyped := translate_type_hasType_normal
      translatedWellFormed domainWellTyped domainWitness
    have relationWeakenedOnce := relationWellTyped.weaken sourceFirstWellFormed
    have relationWeakenedTwice := relationWeakenedOnce.weaken sourceSecondWellFormed
    have originalVariable := HasType.var sourceSecondWellFormed
      (1 : Fin (scopeSize n + 2))
    have firstApplicationRaw := HasType.app relationWeakenedTwice originalVariable
    have firstApplication :
        HasType
          (.extend (.extend (context source) (original domain))
            (weakenBy (primed domain) 1))
          (.app (weakenBy (translate domain) 2) (.var 1))
          (.pi (weakenBy (primed domain) 2) (.sort domainLevel)) := by
      simpa only [elementRelationType, weakenBy, Term.rename, Context.lookup,
        instantiate_pi_double_lift_shift] using firstApplicationRaw
    have primedVariable := HasType.var sourceSecondWellFormed
      (0 : Fin (scopeSize n + 2))
    have relationApplication := HasType.app firstApplication primedVariable
    simpa only [Term.instantiate, Term.substitute, Substitution.single,
      Substitution.lift, finCases_zero, finCases_one,
      substitute_single_rename_shift, weakenBy] using relationApplication
  have relationDomainInserted := relationDomainSource.rename insertionTwo
  let insertionThree := insertionTwo.lift relationDomainInserted
  have sourceTripleWellFormed := context_extend_wellFormed
    translatedWellFormed domainWellTyped domainWitness
  have codomainRelationNormal := translate_type_hasType_normal
    sourceTripleWellFormed codomainWellTyped codomainWitness
  have codomainRelationInserted := codomainRelationNormal.rename insertionThree
  change HasType _
    ((translate codomain).rename
      (Renaming.lift (Renaming.lift (Renaming.lift
        (Renaming.comp Renaming.shift Renaming.shift)))))
    (.pi
      ((original codomain).rename
        (Renaming.lift (Renaming.lift (Renaming.lift
          (Renaming.comp Renaming.shift Renaming.shift)))))
      (.pi
        ((weakenBy (primed codomain) 1).rename
          (Renaming.lift (Renaming.lift (Renaming.lift (Renaming.lift
            (Renaming.comp Renaming.shift Renaming.shift))))))
        (.sort codomainLevel))) at codomainRelationInserted
  have targetWellFormed := insertionThree.targetWellFormed
  have originalFunction := HasType.var targetWellFormed
    (4 : Fin (scopeSize n + 5))
  have originalArgument := HasType.var targetWellFormed
    (2 : Fin (scopeSize n + 5))
  change HasType _ (.var 2)
    (((((original domain).rename (Renaming.comp Renaming.shift Renaming.shift)).rename
      Renaming.shift).rename Renaming.shift).rename Renaming.shift) at originalArgument
  have originalArgumentType :
      (((((original domain).rename (Renaming.comp Renaming.shift Renaming.shift)).rename
        Renaming.shift).rename Renaming.shift).rename Renaming.shift) =
        weakenBy (original domain) 5 := by
    simp only [weakenBy, Term.rename_comp]
  rw [originalArgumentType] at originalArgument
  have originalApplication := HasType.app originalFunction originalArgument
  rw [original_codomain_insert_target] at originalApplication
  have primedFunction := HasType.var targetWellFormed
    (3 : Fin (scopeSize n + 5))
  have primedArgument := HasType.var targetWellFormed
    (1 : Fin (scopeSize n + 5))
  change HasType _ (.var 1)
    ((((weakenBy (primed domain) 1).rename
      (Renaming.lift (Renaming.comp Renaming.shift Renaming.shift))).rename
      Renaming.shift).rename Renaming.shift) at primedArgument
  have primedArgumentType :
      ((((weakenBy (primed domain) 1).rename
        (Renaming.lift (Renaming.comp Renaming.shift Renaming.shift))).rename
        Renaming.shift).rename Renaming.shift) =
        weakenBy (primed domain) 5 := by
    simp only [weakenBy, Term.rename_comp]
    apply Term.rename_congr
    funext index
    rfl
  rw [primedArgumentType] at primedArgument
  have primedApplication := HasType.app primedFunction primedArgument
  rw [primed_codomain_insert_target] at primedApplication
  have codomainAppliedOriginal := HasType.app codomainRelationInserted originalApplication
  simp only [Term.instantiate, Term.substitute] at codomainAppliedOriginal
  rw [substitute_inserted_primed_codomain] at codomainAppliedOriginal
  have codomainAppliedBoth := HasType.app codomainAppliedOriginal primedApplication
  have relationProduct := HasType.pi relationDomainInserted codomainAppliedBoth
  have primedProductBody := HasType.pi primedDomainInserted relationProduct
  have originalProductBody := HasType.pi originalDomainInserted primedProductBody
  have originalDomainInserted_eq :
      (original domain).rename (Renaming.comp Renaming.shift Renaming.shift) =
        weakenBy (original domain) 2 := by
    simp only [weakenBy, Term.rename_comp]
  have primedDomainInserted_eq :
      (weakenBy (primed domain) 1).rename
          (Renaming.lift (Renaming.comp Renaming.shift Renaming.shift)) =
        weakenBy (primed domain) 3 := by
    simp only [weakenBy, Term.rename_comp]
    apply Term.rename_congr
    funext index
    rfl
  have relationDomainInserted_eq :
      (Term.app (Term.app (weakenBy (translate domain) 2) (.var 1)) (.var 0)).rename
          (Renaming.lift (Renaming.lift
            (Renaming.comp Renaming.shift Renaming.shift))) =
        Term.app (Term.app (weakenBy (translate domain) 4) (.var 1)) (.var 0) := by
    simp only [Term.rename, weakenBy, Term.rename_comp]
    apply congrArg₂ Term.app
    · apply congrArg₂ Term.app
      · apply Term.rename_congr
        funext index
        rfl
      · rfl
    · rfl
  have codomainInserted_eq :
      (translate codomain).rename
          (Renaming.lift (Renaming.lift (Renaming.lift
            (Renaming.comp Renaming.shift Renaming.shift)))) =
        (translate codomain).rename insertTwoAfterThree := by
    apply Term.rename_congr
    funext index
    refine Fin.cases rfl ?_ index
    intro index
    refine Fin.cases rfl ?_ index
    intro index
    refine Fin.cases rfl ?_ index
    intro older
    rfl
  have productLevel_eq :
      max domainLevel (max domainLevel (max domainLevel codomainLevel)) =
        max domainLevel codomainLevel := by
    omega
  rw [productLevel_eq] at originalProductBody
  simpa only [piRelationBody, originalDomainInserted_eq,
    primedDomainInserted_eq, relationDomainInserted_eq, codomainInserted_eq,
    max_self, Nat.max_assoc] using originalProductBody

/-- Product translation preserves witness typing from the domain and codomain witnesses. -/
theorem translate_pi_witness_hasType {source : Context n}
    {domain : Term n} {codomain : Term (n + 1)} {domainLevel codomainLevel : Nat}
    (translatedWellFormed : WellFormed (context source))
    (domainWellTyped : HasType source domain (.sort domainLevel))
    (codomainWellTyped :
      HasType (.extend source domain) codomain (.sort codomainLevel))
    (domainWitness :
      HasType (context source) (translate domain)
        (relatedTermType domain (.sort domainLevel)))
    (codomainWitness :
      HasType (context (.extend source domain)) (translate codomain)
        (relatedTermType codomain (.sort codomainLevel))) :
    HasType (context source) (translate (.pi domain codomain))
      (relatedTermType (.pi domain codomain)
        (.sort (max domainLevel codomainLevel))) := by
  have productWellTyped := HasType.pi domainWellTyped codomainWellTyped
  have originalProduct := HasType.original productWellTyped translatedWellFormed
  have firstWellFormed := WellFormed.extend translatedWellFormed originalProduct
  have primedProduct := HasType.primed productWellTyped translatedWellFormed
  have primedProductWeakened := primedProduct.weaken firstWellFormed
  have bodyWellTyped := piRelationBody_hasType translatedWellFormed
    domainWellTyped codomainWellTyped domainWitness codomainWitness
  have translatedProductNormal := HasType.lam originalProduct
    (HasType.lam
      (by simpa only [weakenBy, primed, Term.rename] using primedProductWeakened)
      bodyWellTyped)
  have translatedProductNormal' :
      HasType (context source) (translate (.pi domain codomain))
        (elementRelationType (.pi domain codomain)
          (max domainLevel codomainLevel)) := by
    simpa only [translate_pi_body, elementRelationType] using translatedProductNormal
  exact .conversion translatedProductNormal'
    (relatedType_hasType translatedWellFormed productWellTyped)
    (relatedTermType_sort_beta (.pi domain codomain)
      (max domainLevel codomainLevel)).symm

/-- Lambda translation preserves witness typing once the product type and body translations are typed. -/
theorem translate_lam_witness_hasType_of_productWitness {source : Context n}
    {domain : Term n} {body codomain : Term (n + 1)} {domainLevel typeLevel : Nat}
    (translatedWellFormed : WellFormed (context source))
    (domainWellTyped : HasType source domain (.sort domainLevel))
    (bodyWellTyped : HasType (.extend source domain) body codomain)
    (productWellTyped : HasType source (.pi domain codomain) (.sort typeLevel))
    (productWitness :
      HasType (context source) (translate (.pi domain codomain))
        (relatedTermType (.pi domain codomain) (.sort typeLevel)))
    (bodyWitness :
      HasType (context (.extend source domain)) (translate body)
        (relatedTermType body codomain)) :
    HasType (context source) (translate (.lam domain body))
      (relatedTermType (.lam domain body) (.pi domain codomain)) := by
  let function : Term n := .lam domain body
  have functionWellTyped : HasType source function (.pi domain codomain) :=
    .lam domainWellTyped bodyWellTyped
  obtain ⟨fiberLevel, fiberWellTyped⟩ :=
    piRelationFiber_hasType_of_productTranslation translatedWellFormed
      functionWellTyped productWitness
  rw [piRelationFiber_eq_normal] at fiberWellTyped
  obtain ⟨_, _, originalDomainWellTyped, secondProductWellTyped⟩ :=
    fiberWellTyped.piComponents
  obtain ⟨_, _, primedDomainWellTyped, thirdProductWellTyped⟩ :=
    secondProductWellTyped.piComponents
  obtain ⟨_, outputLevel, domainRelationWellTyped, outputRelationWellTyped⟩ :=
    thirdProductWellTyped.piComponents
  change HasType (context (.extend source domain))
    (applicationRelationBody function codomain) (.sort outputLevel) at outputRelationWellTyped
  have bodyWitnessExpanded :
      HasType (context (.extend source domain)) (translate body)
        (applicationRelationBody function codomain) :=
    .conversion bodyWitness outputRelationWellTyped
      (lambdaRelationBody_beta domain body codomain).symm
  have translatedLambdaNormal :
      HasType (context source) (translate function)
        (piRelationFiberNormal domain codomain function) := by
    change HasType (context source)
      (.lam (original domain)
        (.lam (weakenBy (primed domain) 1)
          (.lam
            (.app (.app (weakenBy (translate domain) 2) (.var 1)) (.var 0))
            (translate body))))
      (piRelationFiberNormal domain codomain function)
    exact .lam originalDomainWellTyped
      (.lam primedDomainWellTyped (.lam domainRelationWellTyped bodyWitnessExpanded))
  have productTranslationNormal := translate_type_hasType_normal
    translatedWellFormed productWellTyped productWitness
  have productAppliedOriginal := HasType.app productTranslationNormal
    (HasType.original functionWellTyped translatedWellFormed)
  have primedProductInstantiated :
      (weakenBy (primed (.pi domain codomain)) 1).substitute
          (Substitution.single (original function)) =
        primed (.pi domain codomain) := by
    simpa only [weakenBy] using substitute_single_rename_shift
      (primed (.pi domain codomain)) (original function)
  simp only [Term.instantiate, Term.substitute] at productAppliedOriginal
  rw [primedProductInstantiated] at productAppliedOriginal
  have relatedFunctionTypeRaw := HasType.app productAppliedOriginal
    (HasType.primed functionWellTyped translatedWellFormed)
  have relatedFunctionTypeWellTyped :
      HasType (context source) (relatedTermType function (.pi domain codomain))
        (.sort typeLevel) := by
    simpa only [elementRelationType, relatedTermType, function, Term.instantiate,
      Term.substitute, Substitution.single, weakenBy, substitute_single_rename_shift]
      using relatedFunctionTypeRaw
  have fiberConversion := (relatedTermType_pi_beta function domain codomain).symm
  rw [piRelationFiber_eq_normal] at fiberConversion
  exact .conversion translatedLambdaNormal relatedFunctionTypeWellTyped fiberConversion

/-- The three typing conclusions of raw parametricity abstraction. -/
def AbstractionConclusion (source : Context n) (term type : Term n) : Prop :=
  HasType (context source) (original term) (original type) ∧
    HasType (context source) (primed term) (primed type) ∧
      HasType (context source) (translate term) (relatedTermType term type)

/-- The displayed raw abstraction claim consists exactly of its three typing conclusions. -/
def DisplayedRawAbstractionClaim : Prop :=
  ∀ {n : Nat} {source : Context n} {term type : Term n},
    HasType source term type → AbstractionConclusion source term type

/-- The full scoped raw abstraction statement, including well-formedness of the translated context. -/
def RawAbstractionClaim : Prop :=
  ∀ {n : Nat} {source : Context n} {term type : Term n},
    HasType source term type →
      WellFormed (context source) ∧ AbstractionConclusion source term type

/-- The structural core combines translated-context formation with witness typing. -/
def StructuralAbstractionClaim : Prop :=
  ∀ {n : Nat} {source : Context n} {term type : Term n},
    HasType source term type →
      WellFormed (context source) ∧
        HasType (context source) (translate term) (relatedTermType term type)

/-- The irreducible witness-typing content of raw parametricity abstraction. -/
def WitnessAbstractionClaim : Prop :=
  ∀ {n : Nat} {source : Context n} {term type : Term n},
    HasType source term type →
      HasType (context source) (translate term) (relatedTermType term type)

/-- Witness abstraction alone makes the translation of every well-formed context well formed. -/
theorem context_wellFormed_of_witness (witnessAbstraction : WitnessAbstractionClaim) :
    ∀ {n : Nat} {source : Context n}, WellFormed source → WellFormed (context source) := by
  intro n source sourceWellFormed
  refine WellFormed.rec
    (motive_1 := fun source _ => WellFormed (context source))
    (motive_2 := fun _ _ _ _ => True)
    context_empty_wellFormed ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ sourceWellFormed
  · intro n source type level sourceWellFormed typeWellTyped sourceInduction _
    exact context_extend_wellFormed sourceInduction typeWellTyped
      (witnessAbstraction typeWellTyped)
  all_goals intros; trivial

/-- Structural abstraction is equivalent to witness typing alone. -/
theorem structuralAbstractionClaim_iff_witness :
    StructuralAbstractionClaim ↔ WitnessAbstractionClaim := by
  constructor
  · intro structural n source term type termWellTyped
    exact (structural termWellTyped).2
  · intro witness n source term type termWellTyped
    exact ⟨context_wellFormed_of_witness witness
        (HasType.contextWellFormed termWellTyped),
      witness termWellTyped⟩

/-- The universe constructor satisfies the witness-typing conclusion in any translated context. -/
theorem translate_sort_witness_hasType {source : Context n}
    (translatedWellFormed : WellFormed (context source)) (level : Nat) :
    HasType (context source) (translate (.sort level : Term n))
      (relatedTermType (.sort level) (.sort (level + 1))) := by
  simpa only [relatedTermType, translatedSortType, original, primed, Term.rename] using
    translate_sort_hasType (n := n) (context := context source) translatedWellFormed level

/-- The universe constructor satisfies all three raw abstraction typing conclusions. -/
theorem abstractionConclusion_sort {source : Context n}
    (translatedWellFormed : WellFormed (context source)) (level : Nat) :
    AbstractionConclusion source (.sort level) (.sort (level + 1)) := by
  refine ⟨?_, ?_, translate_sort_witness_hasType translatedWellFormed level⟩
  · simpa only [original, Term.rename] using HasType.sort translatedWellFormed level
  · simpa only [primed, Term.rename] using HasType.sort translatedWellFormed level

/-- A translated source variable is typed by the relation recorded in its context triple. -/
theorem translate_var_witness_hasType {source : Context n}
    (translatedWellFormed : WellFormed (context source)) (index : Fin n) :
    HasType (context source) (translate (.var index))
      (relatedTermType (.var index) (source.lookup index)) := by
  have witnessVariable :=
    HasType.var translatedWellFormed (witnessRenaming n index)
  rw [context_lookup_witness source index] at witnessVariable
  simpa only [translate_var] using witnessVariable

/-- The variable constructor satisfies all three raw abstraction typing conclusions. -/
theorem abstractionConclusion_var {source : Context n}
    (translatedWellFormed : WellFormed (context source)) (index : Fin n) :
    AbstractionConclusion source (.var index) (source.lookup index) := by
  have originalVariable :=
    HasType.var translatedWellFormed (originalRenaming n index)
  rw [context_lookup_original source index] at originalVariable
  have primedVariable :=
    HasType.var translatedWellFormed (primedRenaming n index)
  rw [context_lookup_primed source index] at primedVariable
  exact ⟨originalVariable, primedVariable,
    translate_var_witness_hasType translatedWellFormed index⟩

/-- Raw abstraction is equivalent to its translated-context and witness-typing core. -/
theorem rawAbstractionClaim_iff_structural :
    RawAbstractionClaim ↔ StructuralAbstractionClaim := by
  constructor
  · intro abstraction n source term type termWellTyped
    obtain ⟨translatedWellFormed, _, _, witnessWellTyped⟩ := abstraction termWellTyped
    exact ⟨translatedWellFormed, witnessWellTyped⟩
  · intro structural n source term type termWellTyped
    obtain ⟨translatedWellFormed, witnessWellTyped⟩ := structural termWellTyped
    exact ⟨translatedWellFormed,
      HasType.original termWellTyped translatedWellFormed,
      HasType.primed termWellTyped translatedWellFormed,
      witnessWellTyped⟩

/-- The explicit context-formation conjunct is equivalent to the displayed abstraction claim. -/
theorem rawAbstractionClaim_iff_displayed :
    RawAbstractionClaim ↔ DisplayedRawAbstractionClaim := by
  constructor
  · intro abstraction n source term type termWellTyped
    exact (abstraction termWellTyped).2
  · intro abstraction n source term type termWellTyped
    have conclusion := abstraction termWellTyped
    exact ⟨HasType.contextWellFormed conclusion.1, conclusion⟩

/-- The displayed abstraction claim reduces to translated-context formation and witness typing. -/
theorem displayedRawAbstractionClaim_iff_structural :
    DisplayedRawAbstractionClaim ↔ StructuralAbstractionClaim :=
  rawAbstractionClaim_iff_displayed.symm.trans rawAbstractionClaim_iff_structural

/-- Raw abstraction is equivalent to its witness-typing component. -/
theorem rawAbstractionClaim_iff_witness :
    RawAbstractionClaim ↔ WitnessAbstractionClaim :=
  rawAbstractionClaim_iff_structural.trans structuralAbstractionClaim_iff_witness

example (level : Nat) :
    HasType Context.empty (translate (.sort level : Term 0))
      (.app
        (.app (translate (.sort (level + 1) : Term 0)) (.sort level))
        (.sort level)) :=
  rawUniverseTranslation_hasType level

example (source : Context n) (index : Fin n) :
    (context source).lookup (originalRenaming n index) =
      (source.lookup index).rename (originalRenaming n) :=
  context_lookup_original source index

example (source : Context n) (translatedWellFormed : WellFormed (context source)) :
    TypedRenaming source (context source) (primedRenaming n) :=
  primedTypedRenaming source translatedWellFormed

example {source : Context n} {domain : Term n} {codomain : Term (n + 1)}
    {domainLevel codomainLevel : Nat}
    (translatedWellFormed : WellFormed (context source))
    (domainWellTyped : HasType source domain (.sort domainLevel))
    (codomainWellTyped :
      HasType (.extend source domain) codomain (.sort codomainLevel))
    (domainWitness :
      HasType (context source) (translate domain)
        (relatedTermType domain (.sort domainLevel)))
    (codomainWitness :
      HasType (context (.extend source domain)) (translate codomain)
        (relatedTermType codomain (.sort codomainLevel))) :
    HasType (context source) (translate (.pi domain codomain))
      (relatedTermType (.pi domain codomain)
        (.sort (max domainLevel codomainLevel))) :=
  translate_pi_witness_hasType translatedWellFormed domainWellTyped
    codomainWellTyped domainWitness codomainWitness

example {source : Context n} {domain : Term n} {body codomain : Term (n + 1)}
    {domainLevel typeLevel : Nat}
    (translatedWellFormed : WellFormed (context source))
    (domainWellTyped : HasType source domain (.sort domainLevel))
    (bodyWellTyped : HasType (.extend source domain) body codomain)
    (productWellTyped : HasType source (.pi domain codomain) (.sort typeLevel))
    (productWitness :
      HasType (context source) (translate (.pi domain codomain))
        (relatedTermType (.pi domain codomain) (.sort typeLevel)))
    (bodyWitness :
      HasType (context (.extend source domain)) (translate body)
        (relatedTermType body codomain)) :
    HasType (context source) (translate (.lam domain body))
      (relatedTermType (.lam domain body) (.pi domain codomain)) :=
  translate_lam_witness_hasType_of_productWitness translatedWellFormed
    domainWellTyped bodyWellTyped productWellTyped productWitness bodyWitness

example : RawAbstractionClaim ↔ StructuralAbstractionClaim :=
  rawAbstractionClaim_iff_structural

example : DisplayedRawAbstractionClaim ↔ StructuralAbstractionClaim :=
  displayedRawAbstractionClaim_iff_structural

example : RawAbstractionClaim ↔ WitnessAbstractionClaim :=
  rawAbstractionClaim_iff_witness

end DeepWiki.Refine.DependentCalculus.RawParametricity
