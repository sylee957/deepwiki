import DeepWiki.Refine.Parametricity.Raw.Naturality

/-! # Relation types for raw parametricity

Universe and dependent-function relation types are presented with their normalization and typing bridges.
-/

namespace DeepWiki.Refine.DependentCalculus.RawParametricity

open DeepWiki.Refine.CCOmega.SurfaceSyntax

/-- The beta-normal type of the raw relation interpreting a universe. -/
def sortRelationType (level : Nat) (n : Nat) : Term n :=
  ccω!{
    %{Term.sort level} →
    %{Term.sort level} →
    %{Term.sort (level + 1)} }

/-- The literal translated type appearing on the right of the raw universe typing equation. -/
def translatedSortType (level : Nat) (n : Nat) : Term (scopeSize n) :=
  ccω!{
    %{translate (.sort (level + 1) : Term n)}
    %{Term.sort level}
    %{Term.sort level} }

/-- The three-argument product body produced by translating a dependent product. -/
def piRelationBody (domain : Term n) (codomain : Term (n + 1)) :
    Term (scopeSize n + 2) :=
  let f0 : Term (scopeSize n + 5) := .var 4
  let f1 : Term (scopeSize n + 5) := .var 3
  ccω!{
    Π x0 : %{weakenBy (original domain) 2},
    Π x1 : %{weakenBy (primed domain) 3},
    Π xR : %{weakenBy (translate domain) 4} x0 x1,
    %{(translate codomain).rename insertTwoAfterThree}
      (%{f0} x0)
      (%{f1} x1) }

/-- The beta-normal relation type assigned to a translated dependent function. -/
def piRelationFiber (domain : Term n) (codomain : Term (n + 1))
    (function : Term n) : Term (scopeSize n) :=
  ((piRelationBody domain codomain).substitute
    (Substitution.lift (Substitution.single (original function)))).instantiate
      (primed function)

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

/-- Codomain relation before substituting an application's original, primed, and witness triple. -/
def applicationRelationBody (function : Term n) (codomain : Term (n + 1)) :
    Term (scopeSize n + 3) :=
  let x0 : Term (scopeSize n + 3) := .var 2
  let x1 : Term (scopeSize n + 3) := .var 1
  ccω!{
    %{translate codomain}
      (%{weakenBy (original function) 3} %{x0})
      (%{weakenBy (primed function) 3} %{x1}) }

/-- The explicit three-argument normal form of a dependent function's relation fiber. -/
def piRelationFiberNormal (domain : Term n) (codomain : Term (n + 1))
    (function : Term n) : Term (scopeSize n) :=
  ccω!{
    Π x0 : %{original domain},
    Π x1 : %{weakenBy (primed domain) 1},
    Π xR : %{weakenBy (translate domain) 2} x0 x1,
    %{applicationRelationBody function codomain} }

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
  unfold piRelationBody piRelationFiberNormal applicationRelationBody
  simp only [Term.substitute]
  rw [originalDomain, primedDomain, domainRelation, codomainRelation,
    originalFunction, primedFunction, domainOriginalVariable,
    domainPrimedVariable, codomainOriginalVariable, codomainPrimedVariable]
  rfl

/-- Translating a product exposes its two function arguments and product relation body. -/
theorem translate_pi_body (domain : Term n) (codomain : Term (n + 1)) :
    translate (ccω!{ Π x : %{domain}, %{codomain} }) =
      ccω!{
        λ f0 : %{original (.pi domain codomain)},
        λ f1 : %{weakenBy (primed (.pi domain codomain)) 1},
        %{piRelationBody domain codomain} } :=
  rfl

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
    ccω!{
      ⟨⟩ ⊢
      %{translate (.sort level : Term 0)} :
      %{translate (.sort (level + 1) : Term 0)}
        %{Term.sort level}
        %{Term.sort level} } :=
  translate_sort_hasType (n := 0) (context := ccωctx!{ ⟨⟩ }) WellFormed.empty level

/-- The translated relation type asserting that two translated terms are related. -/
def relatedTermType (term type : Term n) : Term (scopeSize n) :=
  ccω!{ %{translate type} %{original term} %{primed term} }

/-- Substituting an argument triple in a codomain relation gives the related application type. -/
theorem applicationRelationBody_substitute (function argument : Term n)
    (codomain : Term (n + 1)) :
    (applicationRelationBody function codomain).substitute
        (relationalSingleSubstitution argument) =
      relatedTermType (ccω!{ %{function} %{argument} })
        (codomain.instantiate argument) := by
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
    Convertible
      (relatedTermType function (ccω!{ Π x : %{domain}, %{codomain} }))
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
    (ccω!{
      λ f1 : %{weakenBy (primed (.pi domain codomain)) 1},
      %{piRelationBody domain codomain} }).instantiate (original function) =
        ccω!{
          λ f1 : %{primed (.pi domain codomain)},
          %{(piRelationBody domain codomain).substitute
            (Substitution.lift (Substitution.single (original function)))} } := by
  simp only [Term.instantiate, Term.substitute, weakenBy,
    substitute_single_rename_shift]

/-- Related-term types are natural with respect to relational renamings. -/
theorem relatedTermType_rename (mapping : RelationalRenaming source target)
    (term type : Term source) :
    relatedTermType (term.rename mapping.base) (type.rename mapping.base) =
      (relatedTermType term type).rename mapping.relational := by
  simp only [relatedTermType, Term.rename, translate_rename mapping,
    original_rename mapping, primed_rename mapping]

/-- The beta-normal relation type between elements of two translated copies of a type. -/
def elementRelationType (type : Term n) (level : Nat) : Term (scopeSize n) :=
  ccω!{
    Π x0 : %{original type},
    Π x1 : %{weakenBy (primed type) 1},
    %{Term.sort level} }

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
    Convertible
      (applicationRelationBody (ccω!{ λ x : %{domain}, %{body} }) codomain)
      (relatedTermType body codomain) := by
  unfold applicationRelationBody relatedTermType
  have originalBeta := weakened_original_lam_apply_beta domain body
  have primedBeta := weakened_primed_lam_apply_beta domain body
  exact (originalBeta.app_argument.app_function).trans primedBeta.app_argument

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

example (level : Nat) :
    ccω!{
      ⟨⟩ ⊢
      %{translate (.sort level : Term 0)} :
      %{translate (.sort (level + 1) : Term 0)}
        %{Term.sort level}
        %{Term.sort level} } :=
  rawUniverseTranslation_hasType level

end DeepWiki.Refine.DependentCalculus.RawParametricity
