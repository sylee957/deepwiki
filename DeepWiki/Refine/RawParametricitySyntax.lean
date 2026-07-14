import DeepWiki.Refine.DependentCalculusTyping

/-! # Syntactic raw parametricity

The intrinsically scoped dependent calculus admits the standard three-copy context translation:
each source variable gives an original variable, a primed variable, and a relational witness.
The corresponding term translation is capture-avoiding by construction. -/

namespace DeepWiki.Refine.DependentCalculus.RawParametricity

/-- Number of variables in the relational translation of an `n`-variable scope. -/
def scopeSize : Nat → Nat
  | 0 => 0
  | n + 1 => scopeSize n + 3

/-- The translated scope contains exactly three variables per source variable. -/
@[simp] theorem scopeSize_eq (n : Nat) : scopeSize n = 3 * n := by
  induction n with
  | zero => rfl
  | succ n inductionHypothesis =>
      simp only [scopeSize, Nat.mul_add, inductionHypothesis]

/-- Embed source variables as the original variables in the translated scope. -/
def originalRenaming : (n : Nat) → Renaming n (scopeSize n)
  | 0 => Fin.elim0
  | n + 1 => Fin.cases ⟨2, by simp [scopeSize]⟩
      (fun index => (originalRenaming n index).succ.succ.succ)

/-- Embed source variables as the primed variables in the translated scope. -/
def primedRenaming : (n : Nat) → Renaming n (scopeSize n)
  | 0 => Fin.elim0
  | n + 1 => Fin.cases ⟨1, by simp [scopeSize]⟩
      (fun index => (primedRenaming n index).succ.succ.succ)

/-- Embed source variables as their relation-witness variables in the translated scope. -/
def witnessRenaming : (n : Nat) → Renaming n (scopeSize n)
  | 0 => Fin.elim0
  | n + 1 => Fin.cases ⟨0, by simp [scopeSize]⟩
      (fun index => (witnessRenaming n index).succ.succ.succ)

/-- Rename a term into the original copy of its context. -/
def original (term : Term n) : Term (scopeSize n) :=
  term.rename (originalRenaming n)

/-- Rename a term into the primed copy of its context. -/
def primed (term : Term n) : Term (scopeSize n) :=
  term.rename (primedRenaming n)

/-- The original copy of a variable uses its original slot in the translated context. -/
@[simp] theorem original_var (index : Fin n) :
    original (.var index) = .var (originalRenaming n index) :=
  rfl

/-- The primed copy of a variable uses its primed slot in the translated context. -/
@[simp] theorem primed_var (index : Fin n) :
    primed (.var index) = .var (primedRenaming n index) :=
  rfl

/-- Weaken a term by any finite number of freshly introduced variables. -/
def weakenBy (term : Term n) : (amount : Nat) → Term (n + amount)
  | 0 => term
  | amount + 1 => (weakenBy term amount).rename Renaming.shift

/-- Lift a simultaneous substitution beneath any finite number of binders. -/
def liftSubstitutionBy (mapping : Substitution source target) :
    (amount : Nat) → Substitution (source + amount) (target + amount)
  | 0 => mapping
  | amount + 1 => Substitution.lift (liftSubstitutionBy mapping amount)

/-- Insert two variables between the three newest variables and an older ambient scope. -/
def insertTwoAfterThree : Renaming (n + 3) (n + 5) :=
  Fin.cases 0 (Fin.cases 1 (Fin.cases 2
    (fun index => index.succ.succ.succ.succ.succ)))

/-- The raw relational interpretation of a universe. -/
def sortRelation (level : Nat) (n : Nat) : Term n :=
  .lam (.sort level)
    (.lam (.sort level)
      (.pi (.var 1)
        (.pi (.var 1) (.sort level))))

mutual

  /-- Translate a raw term to its proof-relevant relational witness. -/
  def translate : {n : Nat} → Term n → Term (scopeSize n)
    | _, .sort level => sortRelation level _
    | n + 1, .var index => .var (witnessRenaming (n + 1) index)
    | _, .app function argument =>
        .app (.app (.app (translate function) (original argument)) (primed argument))
          (translate argument)
    | _, .lam domain body =>
        .lam (original domain)
          (.lam (weakenBy (primed domain) 1)
            (.lam
              (.app (.app (weakenBy (translate domain) 2) (.var 1)) (.var 0))
              (translate body)))
    | _, .pi domain codomain =>
        .lam (original (.pi domain codomain))
          (.lam (weakenBy (primed (.pi domain codomain)) 1)
            (.pi (weakenBy (original domain) 2)
              (.pi (weakenBy (primed domain) 3)
                (.pi
                  (.app (.app (weakenBy (translate domain) 4) (.var 1)) (.var 0))
                  (.app
                    (.app ((translate codomain).rename insertTwoAfterThree)
                      (.app (.var 4) (.var 2)))
                    (.app (.var 3) (.var 1)))))))

  /-- Translate a context by adjoining original, primed, and witness declarations in that order. -/
  def context : {n : Nat} → Context n → Context (scopeSize n)
    | 0, .empty => .empty
    | _ + 1, .extend source type =>
        .extend
          (.extend
            (.extend (context source) (original type))
            (weakenBy (primed type) 1))
          (.app (.app (weakenBy (translate type) 2) (.var 1)) (.var 0))

end

/-- Translating the empty context returns the empty context. -/
@[simp] theorem context_empty : context Context.empty = Context.empty :=
  rfl

/-- Context translation replaces one declaration by its original, primed, and witness copies. -/
@[simp] theorem context_extend (source : Context n) (type : Term n) :
    context (.extend source type) =
      .extend
        (.extend
          (.extend (context source) (original type))
          (weakenBy (primed type) 1))
        (.app (.app (weakenBy (translate type) 2) (.var 1)) (.var 0)) :=
  rfl

/-- The newest source variable is embedded at index two of its triple. -/
@[simp] theorem originalRenaming_zero_value : (originalRenaming (n + 1) 0).val = 2 :=
  rfl

/-- The newest source variable is embedded at index one of its triple. -/
@[simp] theorem primedRenaming_zero_value : (primedRenaming (n + 1) 0).val = 1 :=
  rfl

/-- The newest source variable's witness is embedded at index zero of its triple. -/
@[simp] theorem witnessRenaming_zero_value : (witnessRenaming (n + 1) 0).val = 0 :=
  rfl

/-- Older original variables remain in their original slots after context extension. -/
@[simp] theorem originalRenaming_succ (index : Fin n) :
    originalRenaming (n + 1) index.succ = (originalRenaming n index).succ.succ.succ :=
  rfl

/-- Older primed variables remain in their primed slots after context extension. -/
@[simp] theorem primedRenaming_succ (index : Fin n) :
    primedRenaming (n + 1) index.succ = (primedRenaming n index).succ.succ.succ :=
  rfl

/-- Older witness variables remain in their witness slots after context extension. -/
@[simp] theorem witnessRenaming_succ (index : Fin n) :
    witnessRenaming (n + 1) index.succ = (witnessRenaming n index).succ.succ.succ :=
  rfl

/-- A source variable translates to the witness variable allocated to it. -/
@[simp] theorem translate_var (index : Fin n) :
    translate (.var index) = .var (witnessRenaming n index) := by
  cases n with
  | zero => exact Fin.elim0 index
  | succ => rfl

/-- A universe translates to the type of heterogeneous relations at the same level. -/
@[simp] theorem translate_sort (level : Nat) :
    translate (.sort level : Term n) = sortRelation level (scopeSize n) :=
  rfl

/-- Application translation applies a function witness to both arguments and their witness. -/
@[simp] theorem translate_app (function argument : Term n) :
    translate (.app function argument) =
      .app (.app (.app (translate function) (original argument)) (primed argument))
        (translate argument) :=
  rfl

/-- Lambda translation binds an original, a primed, and a related argument. -/
@[simp] theorem translate_lam (domain : Term n) (body : Term (n + 1)) :
    translate (.lam domain body) =
      .lam (original domain)
        (.lam (weakenBy (primed domain) 1)
          (.lam
            (.app (.app (weakenBy (translate domain) 2) (.var 1)) (.var 0))
            (translate body))) :=
  rfl

/-- Product translation relates functions that send related inputs to related outputs. -/
@[simp] theorem translate_pi (domain : Term n) (codomain : Term (n + 1)) :
    translate (.pi domain codomain) =
      .lam (original (.pi domain codomain))
        (.lam (weakenBy (primed (.pi domain codomain)) 1)
          (.pi (weakenBy (original domain) 2)
            (.pi (weakenBy (primed domain) 3)
              (.pi
                (.app (.app (weakenBy (translate domain) 4) (.var 1)) (.var 0))
                (.app
                  (.app ((translate codomain).rename insertTwoAfterThree)
                    (.app (.var 4) (.var 2)))
                  (.app (.var 3) (.var 1))))))) :=
  rfl

example : context Context.empty = Context.empty :=
  rfl

example (source : Context n) (type : Term n) :
    context (.extend source type) =
      .extend
        (.extend
          (.extend (context source) (original type))
          (weakenBy (primed type) 1))
        (.app (.app (weakenBy (translate type) 2) (.var 1)) (.var 0)) :=
  rfl

example (index : Fin n) : translate (.var index) = .var (witnessRenaming n index) :=
  translate_var index

example (index : Fin n) : original (.var index) = .var (originalRenaming n index) :=
  rfl

example (index : Fin n) : primed (.var index) = .var (primedRenaming n index) :=
  rfl

example (level : Nat) :
    translate (.sort level : Term n) =
      .lam (.sort level)
        (.lam (.sort level)
          (.pi (.var 1) (.pi (.var 1) (.sort level)))) :=
  rfl

example (function argument : Term n) :
    translate (.app function argument) =
      .app (.app (.app (translate function) (original argument)) (primed argument))
        (translate argument) :=
  rfl

example (domain : Term n) (body : Term (n + 1)) :
    translate (.lam domain body) =
      .lam (original domain)
        (.lam (weakenBy (primed domain) 1)
          (.lam
            (.app (.app (weakenBy (translate domain) 2) (.var 1)) (.var 0))
            (translate body))) :=
  rfl

example (domain : Term n) (codomain : Term (n + 1)) :
    translate (.pi domain codomain) =
      .lam (original (.pi domain codomain))
        (.lam (weakenBy (primed (.pi domain codomain)) 1)
          (.pi (weakenBy (original domain) 2)
            (.pi (weakenBy (primed domain) 3)
              (.pi
                (.app (.app (weakenBy (translate domain) 4) (.var 1)) (.var 0))
                (.app
                  (.app ((translate codomain).rename insertTwoAfterThree)
                    (.app (.var 4) (.var 2)))
                  (.app (.var 3) (.var 1))))))) :=
  rfl

end DeepWiki.Refine.DependentCalculus.RawParametricity
