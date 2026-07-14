import DeepWiki.Refine.RawParametricitySyntax
import DeepWiki.Refine.DependentCalculusTyping
import Mathlib.Data.List.Nodup

/-! # Raw parametricity sequents

Scoped variable triples support a literal raw sequent judgment and a separate
domain-coherent strengthening suitable for functionality and typing arguments. -/

namespace DeepWiki.Refine.DependentCalculus.ParametricitySequents

open RawParametricity

/-- Three variables respectively naming an original, a primed copy, and a relation witness. -/
structure VariableTriple (n : Nat) where
  /-- The original variable. -/
  original : Fin n
  /-- The primed variable. -/
  primed : Fin n
  /-- The relation-witness variable. -/
  witness : Fin n
  deriving DecidableEq, Repr

/-- A parametricity context is a list of variable triples in one ambient scope. -/
abbrev ParametricityContext (n : Nat) := List (VariableTriple n)

namespace ParametricityContext

/-- Enumerate every variable of a parametricity context, retaining multiplicities. -/
def variableSequence (context : ParametricityContext n) : List (Fin n) :=
  context.flatMap fun triple => [triple.original, triple.primed, triple.witness]

/-- A parametricity context is well formed when its variable enumeration has no duplicates. -/
def WellFormed (context : ParametricityContext n) : Prop :=
  context.variableSequence.Nodup

/-- Shift a variable past the three variables introduced by a relational binder. -/
def shiftThree : Renaming n (n + 3) :=
  fun index => index.succ.succ.succ

/-- Shift all three entries of a variable triple past a relational binder. -/
def VariableTriple.shiftThree (triple : VariableTriple n) : VariableTriple (n + 3) where
  original := ParametricityContext.shiftThree triple.original
  primed := ParametricityContext.shiftThree triple.primed
  witness := ParametricityContext.shiftThree triple.witness

/-- Extend a parametricity context by a fresh canonical triple. -/
def extend (context : ParametricityContext n) : ParametricityContext (n + 3) :=
  { original := ⟨2, by omega⟩
    primed := ⟨1, by omega⟩
    witness := ⟨0, by omega⟩ } :: context.map VariableTriple.shiftThree

/-- Shifting triples shifts every entry of their variable enumeration. -/
theorem variableSequence_map_shiftThree (context : ParametricityContext n) :
    variableSequence (context.map VariableTriple.shiftThree) =
      (variableSequence context).map shiftThree := by
  induction context with
  | nil => rfl
  | cons triple context inductionHypothesis =>
      simp only [variableSequence, List.map_cons, List.flatMap_cons,
        VariableTriple.shiftThree, shiftThree, List.map_append]
      rw [show (context.map VariableTriple.shiftThree).flatMap
          (fun triple => [triple.original, triple.primed, triple.witness]) =
          (context.flatMap fun triple =>
            [triple.original, triple.primed, triple.witness]).map shiftThree by
        simpa only [variableSequence] using inductionHypothesis]
      rfl

/-- The extended context enumerates its fresh triple before the shifted old variables. -/
theorem variableSequence_extend (context : ParametricityContext n) :
    variableSequence context.extend =
      (⟨2, by omega⟩ : Fin (n + 3)) ::
      ⟨1, by omega⟩ ::
      ⟨0, by omega⟩ ::
      (variableSequence context).map shiftThree := by
  change [⟨2, by omega⟩, ⟨1, by omega⟩, ⟨0, by omega⟩] ++
      variableSequence (context.map VariableTriple.shiftThree) = _
  rw [variableSequence_map_shiftThree]
  rfl

/-- Extending a well-formed parametricity context preserves well-formedness. -/
theorem WellFormed.extend {context : ParametricityContext n}
  (wellFormed : context.WellFormed) : context.extend.WellFormed := by
  rw [WellFormed, variableSequence_extend]
  have shiftInjective : Function.Injective (shiftThree : Fin n → Fin (n + 3)) := by
    intro left right equal
    apply Fin.ext
    simpa [shiftThree] using congrArg Fin.val equal
  have shiftedNodup : ((variableSequence context).map shiftThree).Nodup :=
    (List.nodup_map_iff shiftInjective).2 wellFormed
  have fresh (value : Fin (n + 3)) (small : value.val < 3) :
      value ∉ (variableSequence context).map shiftThree := by
    intro member
    obtain ⟨index, _, equal⟩ := List.mem_map.mp member
    have := congrArg Fin.val equal
    simp only [shiftThree, Fin.val_succ] at this
    omega
  have twoFresh : (⟨2, by omega⟩ : Fin (n + 3)) ∉
      (variableSequence context).map shiftThree := fresh _ (by change 2 < 3; omega)
  have oneFresh : (⟨1, by omega⟩ : Fin (n + 3)) ∉
      (variableSequence context).map shiftThree := fresh _ (by change 1 < 3; omega)
  have zeroFresh : (⟨0, by omega⟩ : Fin (n + 3)) ∉
      (variableSequence context).map shiftThree := fresh _ (by change 0 < 3; omega)
  rw [List.nodup_cons]
  constructor
  · simp only [List.mem_cons, not_or, Fin.mk.injEq]
    exact ⟨by decide, by exact ⟨by decide, twoFresh⟩⟩
  rw [List.nodup_cons]
  constructor
  · simp only [List.mem_cons, not_or, Fin.mk.injEq]
    exact ⟨by decide, oneFresh⟩
  rw [List.nodup_cons]
  exact ⟨zeroFresh, shiftedNodup⟩

/-- Original variables form a sublist of the full variable enumeration. -/
theorem originals_sublist (context : ParametricityContext n) :
    List.Sublist (context.map VariableTriple.original) context.variableSequence := by
  induction context with
  | nil => exact .slnil
  | cons triple context inductionHypothesis =>
      simp only [List.map_cons, variableSequence, List.flatMap_cons]
      exact .cons_cons _ (.cons _ (.cons _ inductionHypothesis))

/-- Duplicate-free original variables make a triple lookup functional. -/
theorem eq_of_original_eq_of_originals_nodup {context : ParametricityContext n}
    (originalsNodup : (context.map VariableTriple.original).Nodup)
    {left right : VariableTriple n} (leftMember : left ∈ context)
    (rightMember : right ∈ context) (originalEqual : left.original = right.original) :
    left = right := by
  induction context with
  | nil => simp at leftMember
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons, List.nodup_cons] at originalsNodup
      simp only [List.mem_cons] at leftMember rightMember
      rcases leftMember with rfl | leftMember
      · rcases rightMember with rfl | rightMember
        · rfl
        · exfalso
          have originalInTail : left.original ∈ tail.map VariableTriple.original := by
            exact List.mem_map.mpr ⟨right, rightMember, originalEqual.symm⟩
          exact originalsNodup.1 originalInTail
      · rcases rightMember with rfl | rightMember
        · exfalso
          have originalInTail : right.original ∈ tail.map VariableTriple.original := by
            exact List.mem_map.mpr ⟨left, leftMember, originalEqual⟩
          exact originalsNodup.1 originalInTail
        · exact inductionHypothesis originalsNodup.2 leftMember rightMember

/-- A well-formed context contains at most one triple with a given original variable. -/
theorem WellFormed.eq_of_original_eq {context : ParametricityContext n}
    (wellFormed : context.WellFormed) {left right : VariableTriple n}
    (leftMember : left ∈ context) (rightMember : right ∈ context)
    (originalEqual : left.original = right.original) : left = right := by
  have originalsNodup : (context.map VariableTriple.original).Nodup :=
    wellFormed.sublist (originals_sublist context)
  exact eq_of_original_eq_of_originals_nodup originalsNodup leftMember rightMember originalEqual

end ParametricityContext

/-- Embed a one-binder source scope under a fresh original/prime/witness triple. -/
def originalBinderRenaming : Renaming (n + 1) (n + 3) :=
  Fin.cases ⟨2, by omega⟩ ParametricityContext.shiftThree

/-- Embed a one-binder primed scope under a fresh original/prime/witness triple. -/
def primedBinderRenaming : Renaming (n + 1) (n + 3) :=
  Fin.cases ⟨1, by omega⟩ ParametricityContext.shiftThree

/-- Project an extended relational scope back to its primed one-binder scope. -/
def primedBinderProjection : Fin (n + 3) → Fin (n + 1) :=
  Fin.cases 0 (Fin.cases 0 (Fin.cases 0 Fin.succ))

/-- Primed-binder projection is a left inverse of primed-binder embedding. -/
theorem primedBinderProjection_renaming (index : Fin (n + 1)) :
    primedBinderProjection (primedBinderRenaming index) = index := by
  refine Fin.cases rfl (fun _ => rfl) index

/-- The primed-variable embedding beneath a relational binder is injective. -/
theorem primedBinderRenaming_injective :
    Function.Injective (primedBinderRenaming : Renaming (n + 1) (n + 3)) :=
  Function.LeftInverse.injective primedBinderProjection_renaming

/-- Renaming by an injective variable map is injective on scoped terms. -/
theorem Term.rename_injective (mapping : Renaming source target)
    (mappingInjective : Function.Injective mapping) :
    Function.Injective (Term.rename mapping) := by
  classical
  let inverse : Substitution target source := fun index =>
    if member : ∃ preimage, mapping preimage = index then
      .var member.choose
    else
      .sort 0
  have inverseMapping (index : Fin source) : inverse (mapping index) = .var index := by
    rw [show inverse (mapping index) =
        if member : ∃ preimage, mapping preimage = mapping index then
          .var member.choose
        else
          .sort 0 from rfl]
    simp only [dif_pos (⟨index, rfl⟩ : ∃ preimage, mapping preimage = mapping index)]
    congr 1
    apply mappingInjective
    exact Classical.choose_spec (show ∃ preimage, mapping preimage = mapping index from
      ⟨index, rfl⟩)
  apply Function.LeftInverse.injective (g := fun term => term.substitute inverse)
  intro term
  change (term.rename mapping).substitute inverse = term
  rw [Term.substitute_rename]
  rw [show (fun index => inverse (mapping index)) = Substitution.identity by
    funext index
    exact inverseMapping index]
  exact Term.substitute_identity term

/-- The relation type assigned to a fresh witness variable from a domain relation. -/
def relatedDomain (relation : Term n) : Term (n + 2) :=
  .app (.app (weakenBy relation 2) (.var 1)) (.var 0)

/-- Assemble the three nested witness binders of a relational lambda. -/
def lambdaWitness (domain primedDomain : Term n) (witnessDomain : Term (n + 2))
    (bodyWitness : Term (n + 3)) : Term n :=
  .lam domain
    (.lam (weakenBy primedDomain 1)
      (.lam witnessDomain bodyWitness))

/-- Assemble the proof-relevant relation generated by a dependent product. -/
def piWitness (domain : Term n) (codomain : Term (n + 1))
    (primedDomain : Term n) (primedCodomain : Term (n + 1))
    (domainRelation : Term n) (codomainRelation : Term (n + 3)) : Term n :=
  .lam (.pi domain codomain)
    (.lam (weakenBy (.pi primedDomain primedCodomain) 1)
      (.pi (weakenBy domain 2)
        (.pi (weakenBy primedDomain 3)
          (.pi (relatedDomain (weakenBy domainRelation 2))
            (.app
              (.app (codomainRelation.rename insertTwoAfterThree)
                (.app (.var 4) (.var 2)))
              (.app (.var 3) (.var 1)))))))

/-- The literal raw sequent rules over intrinsically scoped terms. -/
inductive RawSequent : (context : ParametricityContext n) → Term n → Term n → Term n → Prop where
  /-- A universe relates to itself by the type of proof-relevant binary relations. -/
  | paramSort (context : ParametricityContext n) (level : Nat) :
      RawSequent context (.sort level) (.sort level) (sortRelation level n)
  /-- A context triple translates its original variable to its primed and witness variables. -/
  | paramVar {context : ParametricityContext n} (contextWellFormed : context.WellFormed)
      {triple : VariableTriple n} (member : triple ∈ context) :
      RawSequent context (.var triple.original) (.var triple.primed) (.var triple.witness)
  /-- Application translates its function and argument independently. -/
  | paramApp {context : ParametricityContext n}
      {function function' functionRelation argument argument' argumentRelation : Term n}
      (functionSequent : RawSequent context function function' functionRelation)
      (argumentSequent : RawSequent context argument argument' argumentRelation) :
      RawSequent context (.app function argument) (.app function' argument')
        (.app (.app (.app functionRelation argument) argument') argumentRelation)
  /-- Lambda translation extends the variable triples but leaves binder-domain coherence implicit. -/
  | paramLam {context : ParametricityContext n}
      {domain primedDomain : Term n} {witnessDomain : Term (n + 2)}
      {body body' : Term (n + 1)} {bodyRelation : Term (n + 3)}
      (bodySequent : RawSequent context.extend
        (body.rename originalBinderRenaming) (body'.rename primedBinderRenaming) bodyRelation) :
      RawSequent context (.lam domain body) (.lam primedDomain body')
        (lambdaWitness domain primedDomain witnessDomain bodyRelation)
  /-- Product translation relates functions pointwise on related arguments. -/
  | paramPi {context : ParametricityContext n}
      {domain primedDomain domainRelation : Term n}
      {codomain primedCodomain : Term (n + 1)} {codomainRelation : Term (n + 3)}
      (domainSequent : RawSequent context domain primedDomain domainRelation)
      (codomainSequent : RawSequent context.extend
        (codomain.rename originalBinderRenaming)
        (primedCodomain.rename primedBinderRenaming) codomainRelation) :
      RawSequent context (.pi domain codomain) (.pi primedDomain primedCodomain)
        (piWitness domain codomain primedDomain primedCodomain domainRelation codomainRelation)

/-- A typing context is admissible when every related variable triple has coherent lookup types. -/
def Admissible (typingContext : Context n) (context : ParametricityContext n) : Prop :=
  context.WellFormed ∧ WellFormed typingContext ∧
    ∀ {triple : VariableTriple n}, triple ∈ context →
      ∀ {primedType relationType : Term n},
        RawSequent context (typingContext.lookup triple.original) primedType relationType →
        typingContext.lookup triple.primed = primedType ∧
          typingContext.lookup triple.witness =
            .app (.app relationType (.var triple.original)) (.var triple.primed)

/-- The raw abstraction conclusion for a translated term and its translated type. -/
def AbstractionConclusion (typingContext : Context n)
    (term' termRelation type' typeRelation term : Term n) : Prop :=
  HasType typingContext term' type' ∧
    HasType typingContext termRelation (.app (.app typeRelation term) term')

/-- Extend a typing context by original, primed, and relation-witness declarations. -/
def relationalExtension (typingContext : Context n) (domain primedDomain relation : Term n) :
    Context (n + 3) :=
  .extend
    (.extend
      (.extend typingContext domain)
      (weakenBy primedDomain 1))
    (relatedDomain relation)

/-- Structural strengthening needed to recover a primed binder from a relational extension. -/
def PrimedBinderStrengtheningClaim : Prop :=
  ∀ {n : Nat} {typingContext : Context n} {domain primedDomain relation : Term n}
    {body bodyType : Term (n + 1)},
    HasType (relationalExtension typingContext domain primedDomain relation)
      (body.rename primedBinderRenaming) (bodyType.rename primedBinderRenaming) →
    HasType (.extend typingContext primedDomain) body bodyType

/-- The exact sequent-form raw abstraction claim as a proposition. -/
def RawAbstractionClaim : Prop :=
  ∀ {n : Nat} {typingContext : Context n} {context : ParametricityContext n}
    {term term' termRelation type type' typeRelation : Term n},
    Admissible typingContext context →
    HasType typingContext term type →
    RawSequent context term term' termRelation →
    RawSequent context type type' typeRelation →
    AbstractionConclusion typingContext term' termRelation type' typeRelation term

/-- The literal lambda rule is not functional because its primed domain is unconstrained. -/
theorem rawSequent_not_functional :
    ∃ (context : ParametricityContext 0) (term left right leftRelation rightRelation : Term 0),
      context.WellFormed ∧
      RawSequent context term left leftRelation ∧
      RawSequent context term right rightRelation ∧
      (left, leftRelation) ≠ (right, rightRelation) := by
  let context : ParametricityContext 0 := []
  let body : Term 1 := .sort 0
  let bodyRelation : Term 3 := sortRelation 0 3
  let witnessDomain : Term 2 := .sort 0
  refine ⟨context, .lam (.sort 0) body,
    .lam (.sort 0) body, .lam (.sort 1) body,
    lambdaWitness (.sort 0) (.sort 0) witnessDomain bodyRelation,
    lambdaWitness (.sort 0) (.sort 1) witnessDomain bodyRelation, ?_⟩
  constructor
  · change ([] : List (Fin 0)).Nodup
    exact .nil
  constructor
  · exact .paramLam (.paramSort context.extend 0)
  constructor
  · exact .paramLam (.paramSort context.extend 0)
  · decide

/-- Raw lambda sequents have coherent domains when their binder witness is induced by a domain sequent. -/
def HasCoherentLambdaDomain {context : ParametricityContext n}
    {domain : Term n} {body : Term (n + 1)} {primedLambda relationLambda : Term n} : Prop :=
  ∃ (primedDomain domainRelation : Term n) (primedBody : Term (n + 1))
      (bodyRelation : Term (n + 3)),
    RawSequent context domain primedDomain domainRelation ∧
    RawSequent context.extend (body.rename originalBinderRenaming)
      (primedBody.rename primedBinderRenaming) bodyRelation ∧
    primedLambda = .lam primedDomain primedBody ∧
    relationLambda = lambdaWitness domain primedDomain (relatedDomain domainRelation) bodyRelation

/-- The domain-coherent raw sequent rules make every lambda binder relation explicit. -/
inductive CoherentRawSequent :
    (context : ParametricityContext n) → Term n → Term n → Term n → Prop where
  /-- A universe relates to itself by the type of proof-relevant binary relations. -/
  | paramSort (context : ParametricityContext n) (level : Nat) :
      CoherentRawSequent context (.sort level) (.sort level) (sortRelation level n)
  /-- A context triple translates its original variable to its primed and witness variables. -/
  | paramVar {context : ParametricityContext n} (contextWellFormed : context.WellFormed)
      {triple : VariableTriple n} (member : triple ∈ context) :
      CoherentRawSequent context (.var triple.original) (.var triple.primed) (.var triple.witness)
  /-- Application translates its function and argument independently. -/
  | paramApp {context : ParametricityContext n}
      {function function' functionRelation argument argument' argumentRelation : Term n}
      (functionSequent : CoherentRawSequent context function function' functionRelation)
      (argumentSequent : CoherentRawSequent context argument argument' argumentRelation) :
      CoherentRawSequent context (.app function argument) (.app function' argument')
        (.app (.app (.app functionRelation argument) argument') argumentRelation)
  /-- Lambda translation requires a translated domain before extending the variable triples. -/
  | paramLam {context : ParametricityContext n}
      {domain primedDomain domainRelation : Term n}
      {body body' : Term (n + 1)} {bodyRelation : Term (n + 3)}
      (domainSequent : CoherentRawSequent context domain primedDomain domainRelation)
      (bodySequent : CoherentRawSequent context.extend
        (body.rename originalBinderRenaming) (body'.rename primedBinderRenaming) bodyRelation) :
      CoherentRawSequent context (.lam domain body) (.lam primedDomain body')
        (lambdaWitness domain primedDomain (relatedDomain domainRelation) bodyRelation)
  /-- Product translation relates functions pointwise on related arguments. -/
  | paramPi {context : ParametricityContext n}
      {domain primedDomain domainRelation : Term n}
      {codomain primedCodomain : Term (n + 1)} {codomainRelation : Term (n + 3)}
      (domainSequent : CoherentRawSequent context domain primedDomain domainRelation)
      (codomainSequent : CoherentRawSequent context.extend
        (codomain.rename originalBinderRenaming)
        (primedCodomain.rename primedBinderRenaming) codomainRelation) :
      CoherentRawSequent context (.pi domain codomain) (.pi primedDomain primedCodomain)
        (piWitness domain codomain primedDomain primedCodomain domainRelation codomainRelation)

/-- Every domain-coherent derivation is a derivation of the literal raw rules. -/
theorem CoherentRawSequent.toRaw {context : ParametricityContext n}
    {term term' termRelation : Term n}
    (sequent : CoherentRawSequent context term term' termRelation) :
    RawSequent context term term' termRelation := by
  induction sequent with
  | paramSort context level => exact .paramSort context level
  | paramVar contextWellFormed member => exact .paramVar contextWellFormed member
  | paramApp _ _ functionInduction argumentInduction =>
      exact .paramApp functionInduction argumentInduction
  | paramLam _ _ domainInduction bodyInduction =>
      exact .paramLam bodyInduction
  | paramPi _ _ domainInduction codomainInduction =>
      exact .paramPi domainInduction codomainInduction

/-- A domain-coherent lambda sequent exposes the relation translating its binder domain. -/
theorem CoherentRawSequent.hasCoherentLambdaDomain
    {context : ParametricityContext n} {domain : Term n} {body : Term (n + 1)}
    {primedLambda relationLambda : Term n}
    (sequent : CoherentRawSequent context (.lam domain body) primedLambda relationLambda) :
    HasCoherentLambdaDomain (context := context) (domain := domain) (body := body)
      (primedLambda := primedLambda) (relationLambda := relationLambda) := by
  cases sequent with
  | paramLam domainSequent bodySequent =>
      exact ⟨_, _, _, _, domainSequent.toRaw, bodySequent.toRaw, rfl, rfl⟩

/-- The domain-coherent raw translation is functional in its primed term and witness. -/
theorem CoherentRawSequent.functional {context : ParametricityContext n}
    (contextWellFormed : context.WellFormed) {term left right leftRelation rightRelation : Term n}
    (leftSequent : CoherentRawSequent context term left leftRelation)
    (rightSequent : CoherentRawSequent context term right rightRelation) :
    (left, leftRelation) = (right, rightRelation) := by
  induction leftSequent with
  | paramSort context level =>
      cases rightSequent
      rfl
  | @paramVar _ context _ triple leftMember =>
      generalize sourceEqual : (Term.var triple.original) = source at rightSequent
      cases rightSequent with
      | paramSort => cases sourceEqual
      | @paramVar _ _ _ rightTriple rightMember =>
          injection sourceEqual with _ originalEqual
          have tripleEqual := contextWellFormed.eq_of_original_eq leftMember rightMember originalEqual
          cases tripleEqual
          rfl
      | paramApp => cases sourceEqual
      | paramLam => cases sourceEqual
      | paramPi => cases sourceEqual
  | paramApp functionSequent argumentSequent functionInduction argumentInduction =>
      cases rightSequent with
      | paramApp rightFunction rightArgument =>
          have functionEqual := functionInduction contextWellFormed rightFunction
          have argumentEqual := argumentInduction contextWellFormed rightArgument
          cases functionEqual
          cases argumentEqual
          rfl
  | paramLam domainSequent bodySequent domainInduction bodyInduction =>
      cases rightSequent with
      | paramLam rightDomain rightBody =>
          have domainEqual := domainInduction contextWellFormed rightDomain
          have bodyEqual := bodyInduction contextWellFormed.extend rightBody
          have primedBodyEqual := Term.rename_injective primedBinderRenaming
            primedBinderRenaming_injective (congrArg Prod.fst bodyEqual)
          have bodyRelationEqual := congrArg Prod.snd bodyEqual
          cases domainEqual
          cases primedBodyEqual
          cases bodyRelationEqual
          rfl
  | paramPi domainSequent codomainSequent domainInduction codomainInduction =>
      cases rightSequent with
      | paramPi rightDomain rightCodomain =>
          have domainEqual := domainInduction contextWellFormed rightDomain
          have codomainEqual := codomainInduction contextWellFormed.extend rightCodomain
          have primedCodomainEqual := Term.rename_injective primedBinderRenaming
            primedBinderRenaming_injective (congrArg Prod.fst codomainEqual)
          have codomainRelationEqual := congrArg Prod.snd codomainEqual
          cases domainEqual
          cases primedCodomainEqual
          cases codomainRelationEqual
          rfl

/-- The abstraction claim restricted to the domain-coherent sequent relation. -/
def CoherentRawAbstractionClaim : Prop :=
  ∀ {n : Nat} {typingContext : Context n} {context : ParametricityContext n}
    {term term' termRelation type type' typeRelation : Term n},
    Admissible typingContext context →
    HasType typingContext term type →
    CoherentRawSequent context term term' termRelation →
    CoherentRawSequent context type type' typeRelation →
    AbstractionConclusion typingContext term' termRelation type' typeRelation term

example (context : ParametricityContext n) (level : Nat) :
    RawSequent context (.sort level) (.sort level) (sortRelation level n) :=
  .paramSort context level

example {context : ParametricityContext n} (contextWellFormed : context.WellFormed)
    {triple : VariableTriple n} (member : triple ∈ context) :
    RawSequent context (.var triple.original) (.var triple.primed) (.var triple.witness) :=
  .paramVar contextWellFormed member

example {context : ParametricityContext n}
    {function function' functionRelation argument argument' argumentRelation : Term n}
    (functionSequent : RawSequent context function function' functionRelation)
    (argumentSequent : RawSequent context argument argument' argumentRelation) :
    RawSequent context (.app function argument) (.app function' argument')
      (.app (.app (.app functionRelation argument) argument') argumentRelation) :=
  .paramApp functionSequent argumentSequent

example {typingContext : Context n} {context : ParametricityContext n}
    (admissible : Admissible typingContext context) :
    context.WellFormed ∧ WellFormed typingContext :=
  ⟨admissible.1, admissible.2.1⟩

example :
    ∃ (context : ParametricityContext 0) (term left right leftRelation rightRelation : Term 0),
      context.WellFormed ∧
      RawSequent context term left leftRelation ∧
      RawSequent context term right rightRelation ∧
      (left, leftRelation) ≠ (right, rightRelation) :=
  rawSequent_not_functional

example {context : ParametricityContext n} (contextWellFormed : context.WellFormed)
    {term left right leftRelation rightRelation : Term n}
    (leftSequent : CoherentRawSequent context term left leftRelation)
    (rightSequent : CoherentRawSequent context term right rightRelation) :
    (left, leftRelation) = (right, rightRelation) :=
  leftSequent.functional contextWellFormed rightSequent

example {typingContext : Context n} {domain primedDomain relation : Term n}
    {body bodyType : Term (n + 1)}
    (strengthening : PrimedBinderStrengtheningClaim)
    (bodyWellTyped : HasType (relationalExtension typingContext domain primedDomain relation)
      (body.rename primedBinderRenaming) (bodyType.rename primedBinderRenaming)) :
    HasType (.extend typingContext primedDomain) body bodyType :=
  strengthening bodyWellTyped

example : RawAbstractionClaim =
    (∀ {n : Nat} {typingContext : Context n} {context : ParametricityContext n}
      {term term' termRelation type type' typeRelation : Term n},
      Admissible typingContext context →
      HasType typingContext term type →
      RawSequent context term term' termRelation →
      RawSequent context type type' typeRelation →
      AbstractionConclusion typingContext term' termRelation type' typeRelation term) :=
  rfl

example : CoherentRawAbstractionClaim =
    (∀ {n : Nat} {typingContext : Context n} {context : ParametricityContext n}
      {term term' termRelation type type' typeRelation : Term n},
      Admissible typingContext context →
      HasType typingContext term type →
      CoherentRawSequent context term term' termRelation →
      CoherentRawSequent context type type' typeRelation →
      AbstractionConclusion typingContext term' termRelation type' typeRelation term) :=
  rfl

end DeepWiki.Refine.DependentCalculus.ParametricitySequents
