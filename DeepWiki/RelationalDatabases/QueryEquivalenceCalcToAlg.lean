import DeepWiki.RelationalDatabases.QueryEquivalenceFO
import DeepWiki.RelationalDatabases.RelationalAlgebraExpr

/-! # Reduction of the tuple calculus to the algebra (§2.4): context flattening
The hard direction of Codd's theorem. The book's method (§2.4.1) tags each tuple variable's
attributes by its index, forming a clash-free *product scheme*, then translates recursively. Here
the de Bruijn context already *is* the tagging: this file builds the bridge from a context to its
product scheme — `flattenCtx Γ` is the union of all the variable schemes, and `envToTuple` glues an
environment into a single flat row over it. Under a pairwise-disjoint context (no attribute clashes,
so no renaming `ρ` is needed) reading a variable is reading the flat row restricted to its scheme;
the recursive translation of conditions is layered on this. -/

namespace DeepWiki

universe u v w

variable {Att : Type u} [DecidableEq Att] {Val : Type v}

/-- The *product scheme* of a context: the union of all its variable schemes. -/
def flattenCtx : Ctx Att → Finset Att
  | [] => ∅
  | Ω :: Γ => Ω ∪ flattenCtx Γ

@[simp] theorem flattenCtx_nil : flattenCtx ([] : Ctx Att) = ∅ := rfl

@[simp] theorem flattenCtx_cons (Ω : Finset Att) (Γ : Ctx Att) :
    flattenCtx (Ω :: Γ) = Ω ∪ flattenCtx Γ := rfl

theorem mem_flattenCtx_cons {a : Att} {Ω : Finset Att} {Γ : Ctx Att} :
    a ∈ flattenCtx (Ω :: Γ) ↔ a ∈ Ω ∨ a ∈ flattenCtx Γ := by
  simp [flattenCtx]

/-- Glue an environment into a single flat row over the product scheme: each attribute reads from
the first (innermost) variable whose scheme contains it. -/
def envToTuple : {Γ : Ctx Att} → Env Val Γ → Tuple (flattenCtx Γ) Val
  | [], _ => fun a => absurd a.property (Finset.notMem_empty a.val)
  | Ω :: _, (t, e) => fun a =>
      if h : a.val ∈ Ω then t ⟨a.val, h⟩
      else (envToTuple e) ⟨a.val, (mem_flattenCtx_cons.mp a.property).resolve_left h⟩

/-- An attribute of any context scheme lies in the product scheme. -/
theorem mem_flattenCtx_of_mem {a : Att} {Ω : Finset Att} {Γ : Ctx Att} (hΩ : Ω ∈ Γ)
    (ha : a ∈ Ω) : a ∈ flattenCtx Γ := by
  induction Γ with
  | nil => exact absurd hΩ (by simp)
  | cons Ω' Γ' ih =>
    rw [mem_flattenCtx_cons]
    rcases List.mem_cons.mp hΩ with h | h
    · exact Or.inl (h ▸ ha)
    · exact Or.inr (ih h)

/-- A *disjoint context*: the variable schemes are pairwise disjoint (no attribute clashes, so the
book's renaming `ρ` is unnecessary). -/
def CtxDisjoint (Γ : Ctx Att) : Prop := Γ.Pairwise Disjoint

omit [DecidableEq Att] in
/-- The scheme of a de Bruijn variable occurs in its context. -/
theorem Var.scheme_mem : {Γ : Ctx Att} → {Ω : Finset Att} → Var Γ Ω → Ω ∈ Γ
  | _, _, .here => List.mem_cons.mpr (.inl rfl)
  | _, _, .there v => List.mem_cons.mpr (.inr v.scheme_mem)

/-- **Lookup bridge**: in a disjoint context, reading a variable equals the flattened row restricted
to that variable's scheme. -/
theorem lookup_eq_envToTuple : {Γ : Ctx Att} → {Ω : Finset Att} → (v : Var Γ Ω) →
    CtxDisjoint Γ → (e : Env Val Γ) → {a : Att} → (ha : a ∈ Ω) → (hflat : a ∈ flattenCtx Γ) →
    lookup v e ⟨a, ha⟩ = envToTuple e ⟨a, hflat⟩
  | _, _, .here, _, (_, _), a, ha, _ => by
      simp only [lookup, envToTuple, dif_pos ha]
  | _, _, .there v', hd, (_, e'), a, ha, _ => by
      have hne : a ∉ _ := Finset.disjoint_right.mp ((List.pairwise_cons.mp hd).1 _ v'.scheme_mem) ha
      simp only [lookup, envToTuple, dif_neg hne]
      exact lookup_eq_envToTuple v' (List.pairwise_cons.mp hd).2 e' ha _

/-- A context scheme is a subset of the product scheme. -/
theorem scheme_subset_flattenCtx {Ω : Finset Att} {Γ : Ctx Att} (hΩ : Ω ∈ Γ) :
    Ω ⊆ flattenCtx Γ := fun _ ha => mem_flattenCtx_of_mem hΩ ha

/-- The flat-row form of heterogeneous variable agreement on `X`: the row's `Ω`- and `Ω'`-parts
share every value on a common attribute of `X`. -/
def flatAgree {S Ω Ω' : Finset Att} (X : Finset Att) (sub₁ : Ω ⊆ S) (sub₂ : Ω' ⊆ S)
    (flat : Tuple S Val) : Prop :=
  ∀ a ∈ X, ∀ (h : a ∈ Ω) (h' : a ∈ Ω'), flat ⟨a, sub₁ h⟩ = flat ⟨a, sub₂ h'⟩

variable {ι : Type w} {sch : ι → Finset Att}

/-- **Reduction of the tuple calculus to the algebra** (§2.4): translate a first-order condition to
an algebra expression over the product scheme. Atoms become computable predicates (`comp`) on the
flat row; negation is the domain-relative complement (`DOM − ·`); conjunction/disjunction are
intersection/union; the existential is projection (dropping the bound variable's scheme). The
correctness holds on a disjoint context (the book's renaming `ρ` is unnecessary there). -/
def calcToAlg (db : (i : ι) → Table (sch i) Val) :
    {Γ : Ctx Att} → FOCond ι sch Val Γ → AlgExpr Att Val (flattenCtx Γ)
  | _, .relA i v =>
      AlgExpr.comp (fun flat => flat.restrict (scheme_subset_flattenCtx v.scheme_mem) ∈ db i)
  | _, .compA v P =>
      AlgExpr.comp (fun flat => P (flat.restrict (scheme_subset_flattenCtx v.scheme_mem)))
  | _, .agreeA v₁ v₂ X =>
      AlgExpr.comp (flatAgree X (scheme_subset_flattenCtx v₁.scheme_mem)
        (scheme_subset_flattenCtx v₂.scheme_mem))
  | _, .neg C => AlgExpr.diff (AlgExpr.comp (fun _ => True)) (calcToAlg db C)
  | _, .and C D => (calcToAlg db C).inter (calcToAlg db D)
  | _, .or C D => AlgExpr.union (calcToAlg db C) (calcToAlg db D)
  | _, .ex _ C => AlgExpr.proj Finset.subset_union_right (calcToAlg db C)

/-- Reading a variable equals the flattened row restricted to its scheme (tuple form of the lookup
bridge). -/
theorem lookup_eq_restrict {Γ : Ctx Att} {Ω : Finset Att} (hd : CtxDisjoint Γ) (v : Var Γ Ω)
    (e : Env Val Γ) :
    lookup v e = (envToTuple e).restrict (scheme_subset_flattenCtx v.scheme_mem) := by
  funext a
  exact lookup_eq_envToTuple v hd e a.property _

/-- A scheme disjoint from every context scheme is disjoint from the product scheme. -/
theorem disjoint_flattenCtx {Ω : Finset Att} : {Γ : Ctx Att} → (∀ Ω' ∈ Γ, Disjoint Ω Ω') →
    Disjoint Ω (flattenCtx Γ)
  | [], _ => by simp [flattenCtx]
  | _ :: _, h => by
      rw [flattenCtx_cons, Finset.disjoint_union_right]
      exact ⟨h _ (List.mem_cons.mpr (.inl rfl)),
        disjoint_flattenCtx fun _ hΩ'' => h _ (List.mem_cons.mpr (.inr hΩ''))⟩

/-- The tail part of a flattened cons-environment is the flattened tail (the head scheme being
disjoint from the rest). -/
theorem restrict_envToTuple_cons {Ω : Finset Att} {Γ : Ctx Att} (hd : Disjoint Ω (flattenCtx Γ))
    (e : Env Val (Ω :: Γ)) :
    (envToTuple e).restrict Finset.subset_union_right = envToTuple e.2 := by
  obtain ⟨t, e'⟩ := e
  funext a
  have hne : a.val ∉ Ω := Finset.disjoint_right.mp hd a.property
  simp only [Tuple.restrict, envToTuple, dif_neg hne]

/-- **Well-scoped** condition: every existentially bound scheme is disjoint from its context (the
freshness the book's renaming `ρ` provides), so the flattened contexts stay clash-free. -/
def WellScoped : {Γ : Ctx Att} → FOCond ι sch Val Γ → Prop
  | _, .relA _ _ => True
  | _, .compA _ _ => True
  | _, .agreeA _ _ _ => True
  | _, .neg C => WellScoped C
  | _, .and C D => WellScoped C ∧ WellScoped D
  | _, .or C D => WellScoped C ∧ WellScoped D
  | Γ, .ex Ω C => Disjoint Ω (flattenCtx Γ) ∧ WellScoped C

/-- Split a flat row over the product scheme back into an environment (the inverse of `envToTuple`):
each variable's tuple is the row restricted to that variable's scheme. -/
def splitEnv : (Γ : Ctx Att) → Tuple (flattenCtx Γ) Val → Env Val Γ
  | [], _ => PUnit.unit
  | _ :: Γ, flat =>
      (flat.restrict Finset.subset_union_left, splitEnv Γ (flat.restrict Finset.subset_union_right))

/-- `envToTuple` is a left inverse of `splitEnv`: re-gluing a split row recovers it. -/
theorem envToTuple_splitEnv : (Γ : Ctx Att) → (flat : Tuple (flattenCtx Γ) Val) →
    envToTuple (splitEnv Γ flat) = flat
  | [], flat => by funext a; exact absurd a.property (Finset.notMem_empty a.val)
  | Ω :: Γ, flat => by
      funext a
      simp only [splitEnv, envToTuple]
      by_cases h : a.val ∈ Ω
      · rw [dif_pos h]; rfl
      · rw [dif_neg h, envToTuple_splitEnv Γ (flat.restrict Finset.subset_union_right)]; rfl

/-- Cons a tuple onto an environment, with the dependent `Env` type pinned (the `Env` def is not
reducible, so a bare pair does not unify with `Env Val (Ω :: Γ)`). -/
def consEnv {Ω : Finset Att} {Γ : Ctx Att} (t : Tuple Ω Val) (e : Env Val Γ) :
    Env Val (Ω :: Γ) := (t, e)

/-- **Existential reconstruction**: a flat row whose tail (the `flattenCtx Γ` part) is `envToTuple e`
is the flattening of `e` extended by the row's head part. -/
theorem envToTuple_consEnv {Ω : Finset Att} {Γ : Ctx Att} (flat : Tuple (flattenCtx (Ω :: Γ)) Val)
    (e : Env Val Γ) (he : flat.restrict Finset.subset_union_right = envToTuple e) :
    envToTuple (consEnv (flat.restrict Finset.subset_union_left) e) = flat := by
  funext a
  by_cases h : a.val ∈ Ω
  · simp only [consEnv, envToTuple, dif_pos h, Tuple.restrict]
  · simp only [consEnv, envToTuple, dif_neg h]
    rw [← he]; rfl

/-- **Reduction of the tuple calculus to the algebra — correctness** (§2.4): over a disjoint context
and for a well-scoped condition, the flattened environment satisfies the algebra translation exactly
when the condition holds. Atoms go through the lookup bridge; negation is the domain-relative
complement; the existential is projection (with the environment reconstructed from the flat row). -/
theorem mem_evalAlg_calcToAlg (db : (i : ι) → Table (sch i) Val) :
    {Γ : Ctx Att} → (C : FOCond ι sch Val Γ) → CtxDisjoint Γ → WellScoped C →
    (e : Env Val Γ) → (envToTuple e ∈ evalAlg (calcToAlg db C) ↔ evalFO db C e)
  | _, .relA i v, hd, _, e => by
      simp only [calcToAlg, evalAlg_comp, Set.mem_setOf_eq, evalFO, lookup_eq_restrict hd v e]
  | _, .compA v P, hd, _, e => by
      simp only [calcToAlg, evalAlg_comp, Set.mem_setOf_eq, evalFO, lookup_eq_restrict hd v e]
  | _, .agreeA v₁ v₂ X, hd, _, e => by
      simp only [calcToAlg, evalAlg_comp, Set.mem_setOf_eq, evalFO]
      constructor
      · intro _ a _ h1 h2
        rw [lookup_eq_envToTuple v₁ hd e h1 (scheme_subset_flattenCtx v₁.scheme_mem h1),
            lookup_eq_envToTuple v₂ hd e h2 (scheme_subset_flattenCtx v₂.scheme_mem h2)]
      · intro _ a _ h1 h2
        rfl
  | _, .neg C, hd, hw, e => by
      simp only [calcToAlg, evalAlg_diff, evalAlg_comp, mem_diff, Set.mem_setOf_eq, evalFO,
        true_and, mem_evalAlg_calcToAlg db C hd hw e]
  | _, .and C D, hd, hw, e => by
      simp only [calcToAlg, evalAlg_inter, mem_inter, evalFO,
        mem_evalAlg_calcToAlg db C hd hw.1 e, mem_evalAlg_calcToAlg db D hd hw.2 e]
  | _, .or C D, hd, hw, e => by
      simp only [calcToAlg, evalAlg_union, mem_union, evalFO,
        mem_evalAlg_calcToAlg db C hd hw.1 e, mem_evalAlg_calcToAlg db D hd hw.2 e]
  | Γ, .ex Ω C, hd, hw, e => by
      have hdisj : Disjoint Ω (flattenCtx Γ) := hw.1
      have hd' : CtxDisjoint (Ω :: Γ) := List.pairwise_cons.mpr
        ⟨fun _ hΩ' => Finset.disjoint_of_subset_right (scheme_subset_flattenCtx hΩ') hdisj, hd⟩
      simp only [calcToAlg, evalAlg_proj, mem_project, evalFO]
      constructor
      · rintro ⟨flat', hflat', hrestr⟩
        have key : envToTuple (consEnv (flat'.restrict Finset.subset_union_left) e) = flat' :=
          envToTuple_consEnv flat' e hrestr
        have hmem : envToTuple (consEnv (flat'.restrict Finset.subset_union_left) e)
            ∈ evalAlg (calcToAlg db C) := key.symm ▸ hflat'
        exact ⟨flat'.restrict Finset.subset_union_left,
          (mem_evalAlg_calcToAlg db C hd' hw.2 _).mp hmem⟩
      · rintro ⟨t, ht⟩
        exact ⟨envToTuple (consEnv t e),
          (mem_evalAlg_calcToAlg db C hd' hw.2 (consEnv t e)).mpr ht,
          restrict_envToTuple_cons hdisj (consEnv t e)⟩

/-- **Codd's theorem, the calculus ⊆ algebra direction** (§2.4), single-free-variable form: a tuple
is in the view `{t(Ω) | C}` of a well-scoped condition iff its flattened environment is in the
algebra translation. With `algToFO` (algebra ⊆ calculus), the tuple calculus and the relational
algebra have the same expressive power (on well-scoped conditions over a disjoint context). -/
theorem mem_evalFOExpr_calcToAlg (db : (i : ι) → Table (sch i) Val) {Ω : Finset Att}
    (C : FOCond ι sch Val [Ω]) (hw : WellScoped C) (t : Tuple Ω Val) :
    t ∈ evalFOExpr db C ↔ envToTuple (consEnv (Γ := ([] : Ctx Att)) t PUnit.unit) ∈ evalAlg (calcToAlg db C) := by
  simp only [evalFOExpr, Set.mem_setOf_eq]
  exact (mem_evalAlg_calcToAlg db C (by simp [CtxDisjoint]) hw (consEnv (Γ := ([] : Ctx Att)) t PUnit.unit)).symm

end DeepWiki
