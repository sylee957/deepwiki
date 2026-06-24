import DeepWiki.RelationalDatabases.QueryEquivalenceCalcToAlg

/-! # Reduction of the tuple calculus to the algebra (§2.4): the general case via position tagging
The disjoint-context reduction (`QueryEquivalenceCalcToAlg`) assumes the variable schemes do not
clash. The book's general method (§2.4.1, Step 2) removes that assumption by *tagging* each
attribute with its tuple variable's position. We tag by **co-depth** (distance from the outermost
variable) rather than de Bruijn depth: co-depth is stable when the existential adds a fresh innermost
variable, so the tagged tail is left unchanged and the existential becomes a plain projection (no
attribute renaming on the algebra side is needed). A variable of co-depth `k` over scheme `Ω`
contributes tags `{(k, a) | a ∈ Ω}`; different variables get different `k`, so the product scheme is
clash-free even when two variables range over the same database relation.

The tagged environment-flattening, lookup bridge, translation (where an agreement atom becomes a
genuine equality constraint between tagged copies, not the vacuous condition of the disjoint case)
and correctness are layered on this. -/

namespace DeepWiki

universe u v w

variable {Att : Type u} [DecidableEq Att] {Val : Type v}

/-- *Position-tagged attributes* (§2.4.1, Step 2): attribute `a` at position `i` is `(i, a)`. -/
abbrev TagAtt (Att : Type u) : Type u := ℕ × Att

/-- Tag an attribute with a fixed position `n`. -/
def tagAt (n : ℕ) : Att ↪ TagAtt Att := ⟨fun a => (n, a), fun _ _ h => by simpa using h⟩

/-- The *tagged product scheme* of a context: the head variable (outermost co-depth `Γ.length`)
tagged with `Γ.length`, the rest keeping their (stable) co-depth tags. -/
def flattenTagged : Ctx Att → Finset (TagAtt Att)
  | [] => ∅
  | Ω :: Γ => Ω.map (tagAt Γ.length) ∪ flattenTagged Γ

@[simp] theorem flattenTagged_nil : flattenTagged ([] : Ctx Att) = ∅ := rfl

@[simp] theorem flattenTagged_cons (Ω : Finset Att) (Γ : Ctx Att) :
    flattenTagged (Ω :: Γ) = Ω.map (tagAt Γ.length) ∪ flattenTagged Γ := rfl

/-- Every tag of the product scheme has position below the context length (so co-depth tags of a
context never reach `Γ.length`). -/
theorem flattenTagged_lt : {Γ : Ctx Att} → {p : TagAtt Att} → p ∈ flattenTagged Γ → p.1 < Γ.length
  | [], p, h => absurd h (Finset.notMem_empty p)
  | Ω :: Γ, p, h => by
      rw [flattenTagged_cons, Finset.mem_union] at h
      rcases h with h | h
      · obtain ⟨a, _, hap⟩ := Finset.mem_map.mp h
        rw [tagAt, Function.Embedding.coeFn_mk] at hap
        rw [← hap]; exact Nat.lt_succ_self _
      · exact Nat.lt_succ_of_lt (flattenTagged_lt h)

/-- A top-position (`= Γ.length`) tag of `flattenTagged (Ω :: Γ)` comes from the head variable. -/
theorem mem_flattenTagged_head {p : TagAtt Att} {Ω : Finset Att} {Γ : Ctx Att}
    (hp : p ∈ flattenTagged (Ω :: Γ)) (h0 : p.1 = Γ.length) : p.2 ∈ Ω := by
  rw [flattenTagged_cons, Finset.mem_union] at hp
  rcases hp with hp | hp
  · obtain ⟨a, ha, hap⟩ := Finset.mem_map.mp hp
    rw [tagAt, Function.Embedding.coeFn_mk] at hap
    rw [← hap]; exact ha
  · exact absurd h0 (Nat.ne_of_lt (flattenTagged_lt hp))

/-- A below-top tag of `flattenTagged (Ω :: Γ)` belongs (unchanged) to the tail. -/
theorem mem_flattenTagged_tail {p : TagAtt Att} {Ω : Finset Att} {Γ : Ctx Att}
    (hp : p ∈ flattenTagged (Ω :: Γ)) (hn : p.1 ≠ Γ.length) : p ∈ flattenTagged Γ := by
  rw [flattenTagged_cons, Finset.mem_union] at hp
  rcases hp with hp | hp
  · obtain ⟨a, _, hap⟩ := Finset.mem_map.mp hp
    rw [tagAt, Function.Embedding.coeFn_mk] at hap
    exact absurd (by rw [← hap]) hn
  · exact hp

/-- Glue an environment into a flat row over the tagged product scheme: the tag `(k, a)` reads
attribute `a` from the variable of co-depth `k`. -/
def envToTupleTagged : {Γ : Ctx Att} → Env Val Γ → Tuple (flattenTagged Γ) Val
  | [], _ => fun p => absurd p.property (Finset.notMem_empty p.val)
  | _ :: Γ, (t, e) => fun p =>
      if h : p.val.1 = Γ.length then t ⟨p.val.2, mem_flattenTagged_head p.property h⟩
      else (envToTupleTagged e) ⟨p.val, mem_flattenTagged_tail p.property h⟩

/-- The co-depth of a variable — its position tag in the product scheme (distance from outermost). -/
def Var.cotag : {Γ : Ctx Att} → {Ω : Finset Att} → Var Γ Ω → ℕ
  | (_ :: Γ'), _, .here => Γ'.length
  | _, _, .there v' => v'.cotag

/-- A variable's attribute, tagged with the variable's co-depth, lies in the product scheme. -/
theorem tag_mem_flattenTagged : {Γ : Ctx Att} → {Ω : Finset Att} → (v : Var Γ Ω) → {a : Att} →
    a ∈ Ω → (v.cotag, a) ∈ flattenTagged Γ
  | _, _, .here, a, ha => by
      rw [flattenTagged_cons, Finset.mem_union]
      exact Or.inl (Finset.mem_map.mpr ⟨a, ha, rfl⟩)
  | _, _, .there v, a, ha => by
      rw [flattenTagged_cons, Finset.mem_union]
      exact Or.inr (tag_mem_flattenTagged v ha)

/-- **Tagged lookup bridge**: reading a variable equals the tagged flat row at the variable's
co-depth tags — needing *no* disjointness, since co-depth tags are unique. -/
theorem lookup_eq_envToTupleTagged : {Γ : Ctx Att} → {Ω : Finset Att} → (v : Var Γ Ω) →
    (e : Env Val Γ) → {a : Att} → (ha : a ∈ Ω) → (hflat : (v.cotag, a) ∈ flattenTagged Γ) →
    lookup v e ⟨a, ha⟩ = envToTupleTagged e ⟨(v.cotag, a), hflat⟩
  | _ :: Γ', _, .here, (_, _), a, ha, _ => by
      simp only [lookup, envToTupleTagged, Var.cotag, dif_pos]
  | _ :: Γ', _, .there v', (_, e'), a, ha, _ => by
      have hne : v'.cotag ≠ Γ'.length := Nat.ne_of_lt (flattenTagged_lt (tag_mem_flattenTagged v' ha))
      simp only [lookup, envToTupleTagged, Var.cotag, dif_neg hne]
      exact lookup_eq_envToTupleTagged v' e' ha _

/-- Read a variable's tuple out of a tagged flat row (at the variable's co-depth tags). -/
def tagRead {Γ : Ctx Att} {Ω : Finset Att} (v : Var Γ Ω) (flat : Tuple (flattenTagged Γ) Val) :
    Tuple Ω Val := fun a => flat ⟨(v.cotag, a.val), tag_mem_flattenTagged v a.property⟩

/-- Reading a variable out of the flattened environment is the variable's tuple. -/
theorem tagRead_envToTupleTagged {Γ : Ctx Att} {Ω : Finset Att} (v : Var Γ Ω) (e : Env Val Γ) :
    tagRead v (envToTupleTagged e) = lookup v e := by
  funext a
  exact (lookup_eq_envToTupleTagged v e a.property _).symm

/-- The flat-row equality a tagged agreement atom asserts: the rows at the two variables' co-depth
tags coincide on every common attribute of `X` (a genuine cross-tag equality, not vacuous). -/
def tagAgree {Γ : Ctx Att} {Ω Ω' : Finset Att} (X : Finset Att) (v₁ : Var Γ Ω) (v₂ : Var Γ Ω')
    (flat : Tuple (flattenTagged Γ) Val) : Prop :=
  ∀ a ∈ X, ∀ (h : a ∈ Ω) (h' : a ∈ Ω'),
    flat ⟨(v₁.cotag, a), tag_mem_flattenTagged v₁ h⟩
      = flat ⟨(v₂.cotag, a), tag_mem_flattenTagged v₂ h'⟩

variable {ι : Type w} {sch : ι → Finset Att}

/-- **Reduction of the tuple calculus to the algebra, general case** (§2.4): translate a first-order
condition to an algebra expression over the *tagged* product scheme — clash-free without any
disjointness assumption. Atoms read variables out of the tagged row (`tagRead`); an agreement atom
is a genuine cross-tag equality; negation is the domain-relative complement; the existential is a
plain projection (dropping the head variable's tags — co-depth tagging leaves the tail unchanged, so
no renaming is needed). -/
def calcToAlgTagged (db : (i : ι) → Table (sch i) Val) :
    {Γ : Ctx Att} → FOCond ι sch Val Γ → AlgExpr (TagAtt Att) Val (flattenTagged Γ)
  | _, .relA i v => AlgExpr.comp (fun flat => tagRead v flat ∈ db i)
  | _, .compA v P => AlgExpr.comp (fun flat => P (tagRead v flat))
  | _, .agreeA v₁ v₂ X => AlgExpr.comp (tagAgree X v₁ v₂)
  | _, .neg C => AlgExpr.diff (AlgExpr.comp (fun _ => True)) (calcToAlgTagged db C)
  | _, .and C D => (calcToAlgTagged db C).inter (calcToAlgTagged db D)
  | _, .or C D => AlgExpr.union (calcToAlgTagged db C) (calcToAlgTagged db D)
  | _, .ex _ C => AlgExpr.proj Finset.subset_union_right (calcToAlgTagged db C)

/-- The head variable's tags lie in the product scheme. -/
theorem head_tag_mem {a : Att} {Ω : Finset Att} {Γ : Ctx Att} (ha : a ∈ Ω) :
    (Γ.length, a) ∈ flattenTagged (Ω :: Γ) := by
  rw [flattenTagged_cons, Finset.mem_union]
  exact Or.inl (Finset.mem_map.mpr ⟨a, ha, rfl⟩)

/-- Read the head variable's tuple out of a tagged flat row over `flattenTagged (Ω :: Γ)`. -/
def headRead {Ω : Finset Att} {Γ : Ctx Att} (flat : Tuple (flattenTagged (Ω :: Γ)) Val) :
    Tuple Ω Val := fun a => flat ⟨(Γ.length, a.val), head_tag_mem a.property⟩

/-- The tail part of a flattened cons-environment is the flattened tail (the head's tags being at
the top position, the tail's strictly below). -/
theorem restrict_envToTupleTagged_cons {Ω : Finset Att} {Γ : Ctx Att} (e : Env Val (Ω :: Γ)) :
    (envToTupleTagged e).restrict Finset.subset_union_right = envToTupleTagged e.2 := by
  obtain ⟨t, e'⟩ := e
  funext p
  have hne : p.val.1 ≠ Γ.length := Nat.ne_of_lt (flattenTagged_lt p.property)
  simp only [Tuple.restrict, envToTupleTagged, dif_neg hne]

/-- Existential reconstruction: a flat row whose tail part is `envToTupleTagged e` is the flattening
of `e` extended by the row's head part. -/
theorem envToTupleTagged_consEnv {Ω : Finset Att} {Γ : Ctx Att}
    (flat : Tuple (flattenTagged (Ω :: Γ)) Val) (e : Env Val Γ)
    (he : flat.restrict Finset.subset_union_right = envToTupleTagged e) :
    envToTupleTagged (consEnv (headRead flat) e) = flat := by
  funext p
  by_cases h : p.val.1 = Γ.length
  · simp only [consEnv, envToTupleTagged, dif_pos h, headRead]
    exact congrArg flat (Subtype.ext (Prod.ext_iff.mpr ⟨h.symm, rfl⟩))
  · simp only [consEnv, envToTupleTagged, dif_neg h]
    rw [← he]; rfl

/-- **Reduction correctness, general case** (§2.4): the flattened environment of a tuple assignment
satisfies the tagged algebra translation iff the assignment satisfies the first-order condition.
Unlike the disjoint-context version this is **unconditional** — no `CtxDisjoint`, no `WellScoped`:
co-depth position-tagging makes variable schemes clash-free by construction and the head variable's
tags automatically disjoint from the tail's, so the method works for *every* condition. -/
theorem mem_evalAlg_calcToAlgTagged (db : (i : ι) → Table (sch i) Val) :
    {Γ : Ctx Att} → (C : FOCond ι sch Val Γ) → (e : Env Val Γ) →
    (envToTupleTagged e ∈ evalAlg (calcToAlgTagged db C) ↔ evalFO db C e)
  | _, .relA i v, e => by
      simp only [calcToAlgTagged, evalAlg_comp, Set.mem_setOf_eq, evalFO, tagRead_envToTupleTagged v e]
  | _, .compA v P, e => by
      simp only [calcToAlgTagged, evalAlg_comp, Set.mem_setOf_eq, evalFO, tagRead_envToTupleTagged v e]
  | _, .agreeA v₁ v₂ X, e => by
      simp only [calcToAlgTagged, evalAlg_comp, Set.mem_setOf_eq, evalFO]
      constructor
      · intro hag a ha h1 h2
        rw [lookup_eq_envToTupleTagged v₁ e h1 (tag_mem_flattenTagged v₁ h1),
            lookup_eq_envToTupleTagged v₂ e h2 (tag_mem_flattenTagged v₂ h2)]
        exact hag a ha h1 h2
      · intro hag a ha h1 h2
        rw [← lookup_eq_envToTupleTagged v₁ e h1 (tag_mem_flattenTagged v₁ h1),
            ← lookup_eq_envToTupleTagged v₂ e h2 (tag_mem_flattenTagged v₂ h2)]
        exact hag a ha h1 h2
  | _, .neg C, e => by
      simp only [calcToAlgTagged, evalAlg_diff, evalAlg_comp, mem_diff, Set.mem_setOf_eq, evalFO,
        true_and, mem_evalAlg_calcToAlgTagged db C e]
  | _, .and C D, e => by
      simp only [calcToAlgTagged, evalAlg_inter, mem_inter, evalFO,
        mem_evalAlg_calcToAlgTagged db C e, mem_evalAlg_calcToAlgTagged db D e]
  | _, .or C D, e => by
      simp only [calcToAlgTagged, evalAlg_union, mem_union, evalFO,
        mem_evalAlg_calcToAlgTagged db C e, mem_evalAlg_calcToAlgTagged db D e]
  | _, .ex Ω C, e => by
      simp only [calcToAlgTagged, evalAlg_proj, mem_project, evalFO]
      constructor
      · rintro ⟨flat', hflat', hrestr⟩
        have key : envToTupleTagged (consEnv (headRead flat') e) = flat' :=
          envToTupleTagged_consEnv flat' e hrestr
        have hmem : envToTupleTagged (consEnv (headRead flat') e)
            ∈ evalAlg (calcToAlgTagged db C) := key.symm ▸ hflat'
        exact ⟨headRead flat',
          (mem_evalAlg_calcToAlgTagged db C (consEnv (headRead flat') e)).mp hmem⟩
      · rintro ⟨t, ht⟩
        exact ⟨envToTupleTagged (consEnv t e),
          (mem_evalAlg_calcToAlgTagged db C (consEnv t e)).mpr ht,
          restrict_envToTupleTagged_cons (consEnv t e)⟩

/-- **Codd's theorem, calculus ⊆ algebra, general single-free-variable form** (§2.4): a tuple is in
the view `{t(Ω) | C}` of an *arbitrary* first-order condition iff its tagged flattened environment is
in the algebra translation — no disjointness/well-scoping needed (position tagging is unconditional).
The algebra translation reads over the position-tagged copy `{(0, a) | a ∈ Ω}` of `Ω`. -/
theorem mem_evalFOExpr_calcToAlgTagged (db : (i : ι) → Table (sch i) Val) {Ω : Finset Att}
    (C : FOCond ι sch Val [Ω]) (t : Tuple Ω Val) :
    t ∈ evalFOExpr db C ↔
      envToTupleTagged (consEnv (Γ := ([] : Ctx Att)) t PUnit.unit)
        ∈ evalAlg (calcToAlgTagged db C) := by
  simp only [evalFOExpr, Set.mem_setOf_eq]
  exact (mem_evalAlg_calcToAlgTagged db C (consEnv (Γ := ([] : Ctx Att)) t PUnit.unit)).symm

end DeepWiki
