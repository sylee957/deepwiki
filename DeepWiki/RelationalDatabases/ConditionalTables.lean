import DeepWiki.RelationalDatabases.RelationalAlgebra

/-! # Conditional tables (C-tables) — §6.1/§6.2
The third representation system for existing-but-unknown nulls (§6.1). A **V-table** lets each entry
be a *constant* or a *marked variable* (`Val ⊕ Var`); two occurrences of the same variable denote the
same (unknown) value. A **C-table** is a V-table in which each row carries a *condition* (a
conjunction of equalities/inequalities among variables and constants — Def 6.3) plus a *global*
condition. Its semantics (`CTable.rep`) is the set of ordinary relations obtained from all valuations
`ν : Var → Val` satisfying the global condition, keeping the rows whose condition holds under `ν`.
C-tables overcome the limitations of Codd tables (the `Option`-null `NullTable` of `NullValues`) and
plain V-tables. -/

namespace DeepWiki

universe u v w

variable {Att : Type u} {Val : Type v} {Var : Type w} {Ω : Finset Att}

/-- A V-table *entry*: a constant value (`Sum.inl`) or a marked null / variable (`Sum.inr`). -/
abbrev VEntry (Val : Type v) (Var : Type w) : Type _ := Val ⊕ Var

/-- A **V-tuple**: each attribute holds a constant or a variable. -/
abbrev VTuple (Ω : Finset Att) (Val : Type v) (Var : Type w) : Type _ := Tuple Ω (VEntry Val Var)

/-- Evaluate an entry under a valuation `ν : Var → Val` (constants fixed, variables substituted). -/
def evalEntry (ν : Var → Val) : VEntry Val Var → Val := Sum.elim id ν

@[simp] theorem evalEntry_const (ν : Var → Val) (v : Val) : evalEntry ν (Sum.inl v) = v := rfl

@[simp] theorem evalEntry_var (ν : Var → Val) (x : Var) : evalEntry ν (Sum.inr x) = ν x := rfl

/-- Apply a valuation to a V-tuple, yielding an ordinary tuple (naive evaluation). -/
def applyV (ν : Var → Val) (vt : VTuple Ω Val Var) : Tuple Ω Val := fun a => evalEntry ν (vt a)

@[simp] theorem applyV_apply (ν : Var → Val) (vt : VTuple Ω Val Var) (a : {a : Att // a ∈ Ω}) :
    applyV ν vt a = evalEntry ν (vt a) := rfl

/-- An ordinary tuple as a (constant) V-tuple. -/
def Tuple.toV (t : Tuple Ω Val) : VTuple Ω Val Var := fun a => Sum.inl (t a)

/-- A constant V-tuple is valuation-invariant. -/
@[simp] theorem applyV_toV (ν : Var → Val) (t : Tuple Ω Val) :
    applyV ν (Tuple.toV (Var := Var) t) = t := by
  funext a; simp [applyV, Tuple.toV]

/-- An **elementary condition** (Def 6.3): an equality or inequality between two entries. -/
inductive ECond (Val : Type v) (Var : Type w)
  | eq : VEntry Val Var → VEntry Val Var → ECond Val Var
  | ne : VEntry Val Var → VEntry Val Var → ECond Val Var

/-- A **condition** is a conjunction of elementary conditions (Def 6.3). (Named `CCond` — the
C-table condition — to avoid clashing with the tuple-calculus `Cond`.) -/
abbrev CCond (Val : Type v) (Var : Type w) : Type _ := List (ECond Val Var)

/-- Whether an elementary condition holds under a valuation. -/
def ECond.Holds (ν : Var → Val) : ECond Val Var → Prop
  | .eq e₁ e₂ => evalEntry ν e₁ = evalEntry ν e₂
  | .ne e₁ e₂ => evalEntry ν e₁ ≠ evalEntry ν e₂

/-- A condition holds under `ν` iff every conjunct does. -/
def CCond.Holds (ν : Var → Val) (F : CCond Val Var) : Prop := ∀ c ∈ F, c.Holds ν

/-- The empty condition holds under every valuation. -/
@[simp] theorem CCond.holds_nil (ν : Var → Val) : CCond.Holds ν ([] : CCond Val Var) := by
  simp [CCond.Holds]

/-- A condition `c :: F` holds iff `c` holds and `F` holds. -/
@[simp] theorem CCond.holds_cons (ν : Var → Val) (c : ECond Val Var) (F : CCond Val Var) :
    CCond.Holds ν (c :: F) ↔ c.Holds ν ∧ CCond.Holds ν F := by
  simp [CCond.Holds]

/-- A **conditional table** (C-table, §6.1): V-tuples each tagged with a condition, plus a global
condition constraining the admissible valuations. -/
structure CTable (Ω : Finset Att) (Val : Type v) (Var : Type w) where
  /-- The conditioned rows: V-tuples paired with their local condition. -/
  rows : Set (VTuple Ω Val Var × CCond Val Var)
  /-- The global condition, restricting which valuations are admissible. -/
  global : CCond Val Var

/-- The ordinary relation a C-table yields under a single valuation: the images of the rows whose
local condition holds under `ν`. -/
def CTable.instAt (T : CTable Ω Val Var) (ν : Var → Val) : Table Ω Val :=
  { t | ∃ p ∈ T.rows, p.2.Holds ν ∧ applyV ν p.1 = t }

@[simp] theorem CTable.mem_instAt {T : CTable Ω Val Var} {ν : Var → Val} {t : Tuple Ω Val} :
    t ∈ T.instAt ν ↔ ∃ p ∈ T.rows, p.2.Holds ν ∧ applyV ν p.1 = t := Iff.rfl

/-- **Representation of a C-table** (§6.1): the relations it denotes — its instances under all
valuations satisfying the global condition. -/
def CTable.rep (T : CTable Ω Val Var) : Set (Table Ω Val) :=
  { r | ∃ ν : Var → Val, T.global.Holds ν ∧ T.instAt ν = r }

theorem CTable.mem_rep {T : CTable Ω Val Var} {r : Table Ω Val} :
    r ∈ T.rep ↔ ∃ ν : Var → Val, T.global.Holds ν ∧ T.instAt ν = r := Iff.rfl

/-- A C-table with no rows denotes only the empty relation under every valuation. -/
@[simp] theorem CTable.instAt_empty (ν : Var → Val) (g : CCond Val Var) :
    CTable.instAt (Ω := Ω) ⟨∅, g⟩ ν = (∅ : Table Ω Val) := by
  ext t; simp [CTable.instAt]

/-! ## V-tables as conditionless C-tables -/

/-- A **V-table** (§6.1): a set of V-tuples (constants and marked variables), with no conditions —
evaluated naively under a valuation. -/
abbrev VTable (Ω : Finset Att) (Val : Type v) (Var : Type w) : Type _ := Set (VTuple Ω Val Var)

/-- The relations a V-table represents: the naive images under all valuations. -/
def VTable.rep (T : VTable Ω Val Var) : Set (Table Ω Val) := { r | ∃ ν : Var → Val, applyV ν '' T = r }

/-- A V-table as a C-table: every row carries the (always-true) empty condition, and the global
condition is empty. -/
def VTable.toCTable (T : VTable Ω Val Var) : CTable Ω Val Var :=
  ⟨{p | p.1 ∈ T ∧ p.2 = ([] : CCond Val Var)}, []⟩

/-- Under any valuation, the conditionless C-table of a V-table yields its naive image. -/
theorem VTable.instAt_toCTable (T : VTable Ω Val Var) (ν : Var → Val) :
    (VTable.toCTable T).instAt ν = applyV ν '' T := by
  ext t
  simp only [CTable.mem_instAt, VTable.toCTable, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨p, ⟨hp, -⟩, -, ht⟩; exact ⟨p.1, hp, ht⟩
  · rintro ⟨vt, hvt, ht⟩; exact ⟨(vt, []), ⟨hvt, rfl⟩, by simp, ht⟩

/-- **C-tables subsume V-tables**: the C-table of a V-table represents exactly the V-table's naive
relations. -/
theorem VTable.rep_toCTable (T : VTable Ω Val Var) : (VTable.toCTable T).rep = T.rep := by
  ext r
  rw [CTable.mem_rep]
  simp only [VTable.rep, Set.mem_setOf_eq, VTable.instAt_toCTable]
  constructor
  · rintro ⟨ν, -, hr⟩; exact ⟨ν, hr⟩
  · rintro ⟨ν, hr⟩; exact ⟨ν, by show CCond.Holds ν []; simp, hr⟩

/-! ## Ordinary relations as C-tables -/

/-- An ordinary table as a V-table (all entries constants). -/
def Table.toVTable (r : Table Ω Val) : VTable Ω Val Var := Tuple.toV '' r

/-- The naive image of a constant V-table is the table itself, for every valuation. -/
@[simp] theorem applyV_image_toVTable (ν : Var → Val) (r : Table Ω Val) :
    applyV ν '' (Table.toVTable (Var := Var) r) = r := by
  ext t
  constructor
  · rintro ⟨vt, hvt, rfl⟩
    obtain ⟨s, hs, rfl⟩ := hvt
    rw [applyV_toV]; exact hs
  · intro ht; exact ⟨Tuple.toV t, ⟨t, ht, rfl⟩, by rw [applyV_toV]⟩

/-! ## Relational operators on C-tables (Theorem 6.7: correct evaluation)
Each operator commutes with `instAt` — its result, evaluated under any valuation, is the operator
applied to the evaluated input. So C-tables *correctly evaluate* these operators (part of Theorem
6.7; selection is exact here, the key advantage over V-tables). -/

/-- Naive evaluation commutes with restriction. -/
theorem applyV_restrict {Ω₁ : Finset Att} (h : Ω₁ ⊆ Ω) (ν : Var → Val) (vt : VTuple Ω Val Var) :
    applyV ν (vt.restrict h) = (applyV ν vt).restrict h := rfl

/-- **Union of C-tables**: union the conditioned rows (the global conditions conjoined). -/
def CTable.union (T₁ T₂ : CTable Ω Val Var) : CTable Ω Val Var :=
  ⟨T₁.rows ∪ T₂.rows, T₁.global ++ T₂.global⟩

/-- C-tables correctly evaluate union: under any valuation, the instance of the union is the union of
the instances. -/
theorem CTable.instAt_union (T₁ T₂ : CTable Ω Val Var) (ν : Var → Val) :
    (T₁.union T₂).instAt ν = T₁.instAt ν ∪ T₂.instAt ν := by
  ext t
  constructor
  · rintro ⟨p, (hp | hp), hc, ht⟩
    exacts [Or.inl ⟨p, hp, hc, ht⟩, Or.inr ⟨p, hp, hc, ht⟩]
  · rintro (⟨p, hp, hc, ht⟩ | ⟨p, hp, hc, ht⟩)
    exacts [⟨p, Or.inl hp, hc, ht⟩, ⟨p, Or.inr hp, hc, ht⟩]

/-- **Projection of a C-table** onto `Ω₁ ⊆ Ω`: restrict each row's V-tuple, keeping its condition. -/
def CTable.proj {Ω₁ : Finset Att} (h : Ω₁ ⊆ Ω) (T : CTable Ω Val Var) : CTable Ω₁ Val Var :=
  ⟨(fun p => (p.1.restrict h, p.2)) '' T.rows, T.global⟩

/-- C-tables correctly evaluate projection: the instance of the projection is the projection of the
instance. -/
theorem CTable.instAt_proj {Ω₁ : Finset Att} (h : Ω₁ ⊆ Ω) (T : CTable Ω Val Var) (ν : Var → Val) :
    (T.proj h).instAt ν = project h (T.instAt ν) := by
  ext s
  simp only [CTable.mem_instAt, CTable.proj, Set.mem_image, mem_project]
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, hc, rfl⟩
    exact ⟨applyV ν q.1, ⟨q, hq, hc, rfl⟩, (applyV_restrict h ν q.1).symm⟩
  · rintro ⟨t, ⟨p, hp, hc, rfl⟩, rfl⟩
    exact ⟨(p.1.restrict h, p.2), ⟨p, hp, rfl⟩, hc, applyV_restrict h ν p.1⟩

/-- **Selection of a C-table** by `A = c`: conjoin the elementary condition `(row's A-entry) = c` to
each row's condition. Unlike V-tables, C-tables can capture an arbitrary selection *exactly*. -/
def CTable.selectEq (a : {x : Att // x ∈ Ω}) (c : Val) (T : CTable Ω Val Var) : CTable Ω Val Var :=
  ⟨(fun p => (p.1, ECond.eq (p.1 a) (Sum.inl c) :: p.2)) '' T.rows, T.global⟩

/-- C-tables correctly *and exactly* evaluate selection: the instance of `σ_{A=c}` is the selection
of the instance — the defining advantage of C-tables (V-tables fail this, Theorem 6.6). -/
theorem CTable.instAt_selectEq (a : {x : Att // x ∈ Ω}) (c : Val) (T : CTable Ω Val Var)
    (ν : Var → Val) :
    (T.selectEq a c).instAt ν = select (fun t => t a = c) (T.instAt ν) := by
  ext t
  simp only [CTable.mem_instAt, CTable.selectEq, Set.mem_image, mem_select]
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, hc, rfl⟩
    rw [CCond.holds_cons] at hc
    refine ⟨⟨q, hq, hc.2, rfl⟩, ?_⟩
    have := hc.1
    rw [ECond.Holds] at this
    simpa [applyV_apply] using this
  · rintro ⟨⟨p, hp, hc, rfl⟩, hsel⟩
    refine ⟨(p.1, ECond.eq (p.1 a) (Sum.inl c) :: p.2), ⟨p, hp, rfl⟩, ?_, rfl⟩
    rw [CCond.holds_cons]
    refine ⟨?_, hc⟩
    rw [ECond.Holds]
    simpa [applyV_apply] using hsel

/-- A constant V-table represents exactly the original relation (a complete-information table). -/
theorem Table.rep_toVTable [Nonempty Val] (r : Table Ω Val) :
    (Table.toVTable (Var := Var) r).rep = {r} := by
  ext s
  simp only [VTable.rep, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨ν, hν⟩; rw [applyV_image_toVTable] at hν; exact hν.symm
  · rintro rfl; exact ⟨fun _ => Classical.arbitrary Val, applyV_image_toVTable _ _⟩

/-! ## Join of C-tables (Theorem 6.7, join case)
The join merges every pair of rows over `Ω ∪ Ω'`, conjoining equality conditions that force the two
rows to agree on the shared attributes `Ω ∩ Ω'` (the rest of `con` carried along). -/

section Join

variable [DecidableEq Att] {Ω Ω' : Finset Att}

/-- A condition holds on `F ++ G` iff it holds on each part. -/
@[simp] theorem CCond.holds_append (ν : Var → Val) (F G : CCond Val Var) :
    CCond.Holds ν (F ++ G) ↔ CCond.Holds ν F ∧ CCond.Holds ν G := by
  simp only [CCond.Holds, List.mem_append]
  constructor
  · intro h; exact ⟨fun c hc => h c (Or.inl hc), fun c hc => h c (Or.inr hc)⟩
  · rintro ⟨h1, h2⟩ c (hc | hc)
    exacts [h1 c hc, h2 c hc]

/-- Merge two V-tuples into one over the union, taking the left row's entry on shared attributes. -/
def mergeV (vt₁ : VTuple Ω Val Var) (vt₂ : VTuple Ω' Val Var) : VTuple (Ω ∪ Ω') Val Var :=
  fun a => if h : a.val ∈ Ω then vt₁ ⟨a.val, h⟩
           else vt₂ ⟨a.val, (Finset.mem_union.mp a.property).resolve_left h⟩

/-- The left restriction of a merged row's completion is the left row's completion. -/
theorem applyV_mergeV_left (ν : Var → Val) (vt₁ : VTuple Ω Val Var) (vt₂ : VTuple Ω' Val Var) :
    (applyV ν (mergeV vt₁ vt₂)).restrict Finset.subset_union_left = applyV ν vt₁ := by
  funext a; simp only [Tuple.restrict, applyV_apply, mergeV, dif_pos a.property]

/-- The join condition forcing two rows to agree on the shared attributes. -/
noncomputable def joinCond (vt₁ : VTuple Ω Val Var) (vt₂ : VTuple Ω' Val Var) : CCond Val Var :=
  (Ω ∩ Ω').attach.toList.map (fun a =>
    ECond.eq (vt₁ ⟨a.val, (Finset.mem_inter.mp a.property).1⟩)
             (vt₂ ⟨a.val, (Finset.mem_inter.mp a.property).2⟩))

/-- The join condition holds under `ν` iff the two completions agree on the shared attributes. -/
theorem joinCond_holds_iff (vt₁ : VTuple Ω Val Var) (vt₂ : VTuple Ω' Val Var) (ν : Var → Val) :
    CCond.Holds ν (joinCond vt₁ vt₂) ↔
      ∀ a : {x : Att // x ∈ Ω ∩ Ω'},
        evalEntry ν (vt₁ ⟨a.val, (Finset.mem_inter.mp a.property).1⟩)
          = evalEntry ν (vt₂ ⟨a.val, (Finset.mem_inter.mp a.property).2⟩) := by
  rw [CCond.Holds, joinCond]
  constructor
  · intro h a
    exact h _ (List.mem_map.mpr ⟨a, Finset.mem_toList.mpr (Finset.mem_attach _ a), rfl⟩)
  · rintro h c hc
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hc
    exact h a

/-- The right restriction of a merged row's completion is the right row's completion, provided the
two rows agree on the shared attributes under `ν`. -/
theorem applyV_mergeV_right (ν : Var → Val) (vt₁ : VTuple Ω Val Var) (vt₂ : VTuple Ω' Val Var)
    (hag : CCond.Holds ν (joinCond vt₁ vt₂)) :
    (applyV ν (mergeV vt₁ vt₂)).restrict Finset.subset_union_right = applyV ν vt₂ := by
  rw [joinCond_holds_iff] at hag
  funext a
  simp only [Tuple.restrict, applyV_apply, mergeV]
  by_cases h : a.val ∈ Ω
  · rw [dif_pos h]
    exact hag ⟨a.val, Finset.mem_inter.mpr ⟨h, a.property⟩⟩
  · rw [dif_neg h]

/-- **Join of C-tables** over `Ω ∪ Ω'`: merge each pair of rows, conjoining the agreement condition
on the shared attributes with the two rows' conditions. -/
noncomputable def CTable.join (T₁ : CTable Ω Val Var) (T₂ : CTable Ω' Val Var) :
    CTable (Ω ∪ Ω') Val Var :=
  ⟨{p | ∃ q₁ ∈ T₁.rows, ∃ q₂ ∈ T₂.rows,
      p = (mergeV q₁.1 q₂.1, joinCond q₁.1 q₂.1 ++ q₁.2 ++ q₂.2)}, T₁.global ++ T₂.global⟩

/-- **Theorem 6.7**, join case: C-tables correctly evaluate the natural join — the instance of the
join is the join of the instances. -/
theorem CTable.instAt_join (T₁ : CTable Ω Val Var) (T₂ : CTable Ω' Val Var) (ν : Var → Val) :
    (T₁.join T₂).instAt ν = _root_.DeepWiki.join (T₁.instAt ν) (T₂.instAt ν) := by
  ext t
  simp only [CTable.mem_instAt, CTable.join, Set.mem_setOf_eq, mem_join]
  constructor
  · rintro ⟨p, ⟨q₁, hq₁, q₂, hq₂, rfl⟩, hc, rfl⟩
    rw [CCond.holds_append, CCond.holds_append] at hc
    obtain ⟨⟨hjc, hF₁⟩, hF₂⟩ := hc
    refine ⟨?_, ?_⟩
    · rw [applyV_mergeV_left]; exact ⟨q₁, hq₁, hF₁, rfl⟩
    · rw [applyV_mergeV_right ν q₁.1 q₂.1 hjc]; exact ⟨q₂, hq₂, hF₂, rfl⟩
  · rintro ⟨⟨q₁, hq₁, hF₁, hl⟩, ⟨q₂, hq₂, hF₂, hr⟩⟩
    have hag : CCond.Holds ν (joinCond q₁.1 q₂.1) := by
      rw [joinCond_holds_iff]
      intro a
      have h₁ := congrFun hl ⟨a.val, (Finset.mem_inter.mp a.property).1⟩
      have h₂ := congrFun hr ⟨a.val, (Finset.mem_inter.mp a.property).2⟩
      simp only [Tuple.restrict, applyV_apply] at h₁ h₂
      rw [h₁, h₂]
    refine ⟨(mergeV q₁.1 q₂.1, joinCond q₁.1 q₂.1 ++ q₁.2 ++ q₂.2),
      ⟨q₁, hq₁, q₂, hq₂, rfl⟩, ?_, ?_⟩
    · rw [CCond.holds_append, CCond.holds_append]; exact ⟨⟨hag, hF₁⟩, hF₂⟩
    · funext a
      by_cases h : a.val ∈ Ω
      · have := congrFun hl ⟨a.val, h⟩
        simpa [Tuple.restrict, applyV_apply, mergeV, dif_pos h] using this
      · have h' : a.val ∈ Ω' := (Finset.mem_union.mp a.property).resolve_left h
        have := congrFun hr ⟨a.val, h'⟩
        simpa [Tuple.restrict, applyV_apply, mergeV, dif_neg h] using this

end Join

end DeepWiki
