import DeepWiki.RelationalDatabases.RelationalModel

/-! # Classification and algebra of constraints
The hierarchy of constraints: a *tuple constraint* is one checkable tuple by tuple. Such
constraints are downward closed and union closed, and a whole set of them is equivalent to a
single tuple constraint (closed under conjunction). Relation constraints embed into database
constraints and into dynamic constraints.

The book's exercise that *every consequence of a set of tuple constraints is a tuple
constraint* is **false as literally stated**: a consequence can drop union-closure. The
constant `not_forall_isConsequence_isTupleConstraint` refutes it with a one-attribute,
two-value witness, and `isTupleConstraint_conjunction` records the true kernel — the
conjunction of tuple constraints is a tuple constraint. -/

namespace DeepWiki

universe u v w

variable {Att : Type u} {Val : Type v}

/-- A relation constraint is a *tuple constraint* if it is checkable tuple by tuple: it holds
of an instance exactly when every tuple satisfies a fixed predicate `p`. -/
def IsTupleConstraint {P : PrimRelScheme Att Val} (c : RelConstraint P) : Prop :=
  ∃ p : TupleOf P → Prop, ∀ r : PossibleRelInstance P, c r ↔ ∀ t ∈ r, p t

/-- A tuple constraint is *downward closed*: any subset of a satisfying instance also
satisfies it. -/
theorem IsTupleConstraint.downward_closed {P : PrimRelScheme Att Val} {c : RelConstraint P}
    (hc : IsTupleConstraint c) {r r' : PossibleRelInstance P} (hsub : r' ⊆ r) (h : c r) :
    c r' := by
  obtain ⟨p, hp⟩ := hc
  rw [hp] at h ⊢
  exact fun t ht => h t (hsub ht)

/-- A tuple constraint is *union closed*: the union of two satisfying instances satisfies it. -/
theorem IsTupleConstraint.union_closed {P : PrimRelScheme Att Val} {c : RelConstraint P}
    (hc : IsTupleConstraint c) {r₁ r₂ : PossibleRelInstance P} (h₁ : c r₁) (h₂ : c r₂) :
    c (r₁ ∪ r₂) := by
  obtain ⟨p, hp⟩ := hc
  rw [hp] at h₁ h₂ ⊢
  intro t ht
  rcases ht with ht | ht
  · exact h₁ t ht
  · exact h₂ t ht

/-- A set of tuple constraints is equivalent to a single tuple constraint: the conjunction of
any family of tuple constraints is again a tuple constraint. -/
theorem isTupleConstraint_conjunction {P : PrimRelScheme Att Val} {S : Set (RelConstraint P)}
    (hS : ∀ c ∈ S, IsTupleConstraint c) :
    IsTupleConstraint (fun r => ∀ c ∈ S, c r) := by
  classical
  choose p hp using hS
  refine ⟨fun t => ∀ c (hc : c ∈ S), p c hc t, fun r => ?_⟩
  constructor
  · intro h t ht c hc
    exact (hp c hc r).mp (h c hc) t ht
  · intro h c hc
    rw [hp c hc r]
    intro t ht
    exact h t ht c hc

/-- Lift a relation constraint on the `i`-th relation scheme of a database to a database
constraint, satisfied exactly when the `i`-th relation satisfies it: relation constraints
embed into database constraints. -/
def liftRelToDb {ι : Type w} [Fintype ι] {P : PrimDbScheme ι Att Val} (i : ι)
    (c : RelConstraint (P.scheme i).prim) : DbConstraint P :=
  fun d => c (d i)

@[simp] theorem liftRelToDb_apply {ι : Type w} [Fintype ι] {P : PrimDbScheme ι Att Val}
    (i : ι) (c : RelConstraint (P.scheme i).prim) (d : PossibleDbInstance P) :
    liftRelToDb i c d ↔ c (d i) := Iff.rfl

/-- Lift a relation constraint to the dynamic relation constraint requiring it at every time:
relation constraints embed into dynamic relation constraints. -/
def liftRelToDyn {R : RelScheme Att Val} (c : RelConstraint R.prim) : DynRelConstraint R :=
  fun rs => ∀ n, c (rs n)

/-- Lift a database constraint to the dynamic database constraint requiring it at every time:
database constraints embed into dynamic database constraints. -/
def liftDbToDyn {ι : Type w} [Fintype ι] {D : DbScheme ι Att Val} (c : DbConstraint D.prim) :
    DynDbConstraint D :=
  fun ds => ∀ n, c (ds n)

/-- `c` is a *consequence* of a set `S` of constraints: every possible relation instance
satisfying all of `S` also satisfies `c`. -/
def IsConsequence {P : PrimRelScheme Att Val} (S : Set (RelConstraint P)) (c : RelConstraint P) :
    Prop :=
  ∀ r : PossibleRelInstance P, (∀ d ∈ S, d r) → c r

namespace ConsequenceCounterexample

/-- A one-attribute scheme with the full two-element domain — the witness for the failure of
"consequences of tuple constraints are tuple constraints". -/
def P0 : PrimRelScheme Unit Bool := ⟨{()}, fun _ => Set.univ⟩

/-- The all-`false` tuple of `P0`. -/
def t0 : TupleOf P0 := ⟨fun _ => false, fun _ => Set.mem_univ _⟩

/-- The all-`true` tuple of `P0`. -/
def t1 : TupleOf P0 := ⟨fun _ => true, fun _ => Set.mem_univ _⟩

/-- The two witness tuples are distinct. -/
theorem t0_ne_t1 : t0 ≠ t1 := by
  intro h
  have := congrFun (Subtype.ext_iff.mp h) ⟨(), Finset.mem_singleton_self ()⟩
  exact absurd this (by decide)

end ConsequenceCounterexample

open ConsequenceCounterexample in
/-- A consequence of a set of tuple constraints need not be a tuple constraint. Over one
attribute with a two-value domain, the constraint "the instance is `∅`, `{t0}`, or `{t1}`" is
a consequence of the tuple constraint "every tuple equals `t0`" (whose models are exactly `∅`
and `{t0}`) yet is not a tuple constraint — it holds on `{t0}` and `{t1}` but not on their
union, breaking union-closure. -/
theorem exists_isConsequence_not_isTupleConstraint :
    ∃ (P : PrimRelScheme Unit Bool) (S : Set (RelConstraint P)) (c : RelConstraint P),
      (∀ d ∈ S, IsTupleConstraint d) ∧ IsConsequence S c ∧ ¬ IsTupleConstraint c := by
  refine ⟨P0, {fun r => ∀ t ∈ r, t = t0},
    (fun r => r = ∅ ∨ r = {t0} ∨ r = {t1}), ?_, ?_, ?_⟩
  · -- every member of `S` is a tuple constraint
    intro d hd
    rw [Set.mem_singleton_iff] at hd
    subst hd
    exact ⟨fun t => t = t0, fun _ => Iff.rfl⟩
  · -- the constraint is a consequence of `S`
    intro r hr
    have hc0 : ∀ t ∈ r, t = t0 := hr _ rfl
    rcases Set.subset_singleton_iff_eq.mp (Set.subset_singleton_iff.mpr hc0) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · -- but it is not a tuple constraint (union-closure fails)
    intro hc
    have hct0 : (fun r : PossibleRelInstance P0 => r = ∅ ∨ r = {t0} ∨ r = {t1}) {t0} :=
      Or.inr (Or.inl rfl)
    have hct1 : (fun r : PossibleRelInstance P0 => r = ∅ ∨ r = {t0} ∨ r = {t1}) {t1} :=
      Or.inr (Or.inr rfl)
    have hunion := hc.union_closed hct0 hct1
    rw [Set.singleton_union] at hunion
    rcases hunion with h | h | h
    · exact Set.notMem_empty t0 (h ▸ Set.mem_insert t0 {t1})
    · exact t0_ne_t1 (Set.mem_singleton_iff.mp (h ▸ Set.mem_insert_iff.mpr (Or.inr rfl))).symm
    · exact t0_ne_t1 (Set.mem_singleton_iff.mp (h ▸ Set.mem_insert t0 {t1}))

/-- The exercise "every consequence of a set of tuple constraints is a tuple constraint" is
false: there is no such implication, even over a single attribute with a two-value domain. -/
theorem not_forall_isConsequence_isTupleConstraint :
    ¬ ∀ (P : PrimRelScheme Unit Bool) (S : Set (RelConstraint P)) (c : RelConstraint P),
        (∀ d ∈ S, IsTupleConstraint d) → IsConsequence S c → IsTupleConstraint c := by
  intro h
  obtain ⟨P, S, c, h1, h2, h3⟩ := exists_isConsequence_not_isTupleConstraint
  exact h3 (h P S c h1 h2)

end DeepWiki
