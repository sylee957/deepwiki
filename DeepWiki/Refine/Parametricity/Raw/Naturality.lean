import DeepWiki.Refine.Parametricity.Raw.Translation

/-! # Naturality of raw parametricity

Relational renamings and substitutions act coherently on original, primed, and witness variables.
-/

namespace DeepWiki.Refine.DependentCalculus.RawParametricity

open DeepWiki.Refine.CCOmega.SurfaceSyntax

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

/-- Weakening after renaming agrees with renaming beneath all fresh binders. -/
theorem weakenBy_rename (term : Term source) (mapping : Renaming source target)
    (amount : Nat) :
    weakenBy (term.rename mapping) amount =
      (weakenBy term amount).rename (Renaming.liftBy mapping amount) := by
  induction amount with
  | zero => rfl
  | succ amount inductionHypothesis =>
      simp only [weakenBy, inductionHypothesis, Term.rename_comp, Renaming.liftBy]
      apply Term.rename_congr
      funext index
      rfl

/-- Inserting two variables after three binders commutes with lifted renaming. -/
theorem insertTwoAfterThree_natural (mapping : Renaming source target) :
    Renaming.comp insertTwoAfterThree (Renaming.liftBy mapping 3) =
      Renaming.comp (Renaming.liftBy mapping 5) insertTwoAfterThree := by
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
        bodyNatural, weakenBy_rename, Renaming.liftBy, Renaming.lift_zero]
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
        simpa only [Renaming.liftBy] using insertTwoAfterThree_natural mapping.relational
      simp only [Term.rename, translate_pi, original_rename mapping,
        primed_rename mapping, originalProductNatural, primedProductNatural,
        domainInduction mapping, codomainNatural, weakenBy_rename, Renaming.liftBy,
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
  (relationalSingle argument).relational

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

end DeepWiki.Refine.DependentCalculus.RawParametricity
