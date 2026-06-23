import DeepWiki.NetworkCalculus.BooleanSatisfiability

/-! # A CNF-constraint DSL (the assembly language of Cook–Levin tableaux)

Clause-family builders over `CnfFormula`'s `Clause`/`List (Clause n)`, each shipped with a
*fully proved* satisfaction-semantics characterization. These are the reusable building blocks
a Cook–Levin tableau encoding is assembled from: "at least one", "at most one", "exactly one",
implication, and the conjunction/append lemmas that let a formula's satisfaction be proved
family-by-family.

Everything is over a fixed variable count `n` (so each builder lives in `Clause n` /
`List (Clause n)`), and nothing here is restricted to 3-CNF — `atLeastOneTrue` clauses may be
arbitrarily long; the Cook–Levin target is general SAT.
-/

namespace DeepWiki.BooleanConstraints

open CnfFormula

/-! ## (5) Conjunction / assembly: how `eval` decomposes over clause lists -/

/-- `assign` **satisfies every clause** in `cs`: the `∀ ∈` reading of `eval ⟨n, cs⟩`. -/
def satisfiesAll {n : ℕ} (assign : Fin n → Bool) (cs : List (Clause n)) : Prop :=
  ∀ c ∈ cs, clauseSat assign c = true

/-- `satisfiesAll` is decidable (a bounded `Bool`-check over the clause list). -/
instance {n : ℕ} (assign : Fin n → Bool) (cs : List (Clause n)) :
    Decidable (satisfiesAll assign cs) := by
  unfold satisfiesAll; infer_instance

/-- `eval ⟨n, cs⟩ assign = true` is exactly `satisfiesAll assign cs` (the `Bool`/`Prop` bridge). -/
theorem eval_iff_satisfiesAll {n : ℕ} (assign : Fin n → Bool) (cs : List (Clause n)) :
    eval ⟨n, cs⟩ assign = true ↔ satisfiesAll assign cs := by
  simp [eval, satisfiesAll, List.all_eq_true]

/-- `satisfiesAll` over a `cons` splits into the head clause and the tail. -/
theorem satisfiesAll_cons {n : ℕ} (assign : Fin n → Bool) (c : Clause n) (cs : List (Clause n)) :
    satisfiesAll assign (c :: cs) ↔
      (clauseSat assign c = true ∧ satisfiesAll assign cs) := by
  simp [satisfiesAll]

/-- `satisfiesAll` over `nil` is vacuously true. -/
@[simp] theorem satisfiesAll_nil {n : ℕ} (assign : Fin n → Bool) :
    satisfiesAll assign ([] : List (Clause n)) := by
  simp [satisfiesAll]

/-- `satisfiesAll` distributes over `++`: both halves must be satisfied. -/
theorem satisfiesAll_append {n : ℕ} (assign : Fin n → Bool) (c₁ c₂ : List (Clause n)) :
    satisfiesAll assign (c₁ ++ c₂) ↔
      (satisfiesAll assign c₁ ∧ satisfiesAll assign c₂) := by
  simp only [satisfiesAll, List.mem_append]
  constructor
  · intro h; exact ⟨fun c hc => h c (Or.inl hc), fun c hc => h c (Or.inr hc)⟩
  · rintro ⟨h₁, h₂⟩ c (hc | hc)
    · exact h₁ c hc
    · exact h₂ c hc

/-- **`eval`-append.** `eval ⟨n, c₁ ++ c₂⟩` holds iff each half-formula does. -/
theorem eval_append {n : ℕ} (assign : Fin n → Bool) (c₁ c₂ : List (Clause n)) :
    eval ⟨n, c₁ ++ c₂⟩ assign = true ↔
      (eval ⟨n, c₁⟩ assign = true ∧ eval ⟨n, c₂⟩ assign = true) := by
  rw [eval_iff_satisfiesAll, eval_iff_satisfiesAll, eval_iff_satisfiesAll, satisfiesAll_append]

/-- `satisfiesAll` over a `flatten`: every clause of every group is satisfied. -/
theorem satisfiesAll_flatten {n : ℕ} (assign : Fin n → Bool) (gs : List (List (Clause n))) :
    satisfiesAll assign gs.flatten ↔ ∀ g ∈ gs, satisfiesAll assign g := by
  simp only [satisfiesAll, List.mem_flatten]
  constructor
  · intro h g hg c hc; exact h c ⟨g, hg, hc⟩
  · rintro h c ⟨g, hg, hc⟩; exact h g hg c hc

/-! ## (1) "At least one": a single disjunctive clause -/

/-- The clause `l₁ ∨ … ∨ l_k` from a literal list (a disjunction is exactly a clause). -/
def atLeastOne {n : ℕ} (lits : List (Literal n)) : Clause n := lits

/-- **`atLeastOne` semantics.** The clause is satisfied iff some literal in it is true. -/
theorem atLeastOne_sat_iff {n : ℕ} (assign : Fin n → Bool) (lits : List (Literal n)) :
    clauseSat assign (atLeastOne lits) = true ↔ ∃ l ∈ lits, litSat assign l = true := by
  simp [atLeastOne, clauseSat, List.any_eq_true]

/-- The clause "at least one of `vars` is `true`", i.e. `⋁ v ∈ vars, v`. -/
def atLeastOneTrue {n : ℕ} (vars : List (Fin n)) : Clause n := vars.map (·, true)

/-- **`atLeastOneTrue` semantics.** Satisfied iff some variable in `vars` is assigned `true`. -/
theorem atLeastOneTrue_sat_iff {n : ℕ} (assign : Fin n → Bool) (vars : List (Fin n)) :
    clauseSat assign (atLeastOneTrue vars) = true ↔ ∃ v ∈ vars, assign v = true := by
  simp only [atLeastOneTrue, clauseSat, List.any_eq_true, List.mem_map]
  constructor
  · rintro ⟨l, ⟨v, hv, rfl⟩, hl⟩
    exact ⟨v, hv, by simpa [litSat] using hl⟩
  · rintro ⟨v, hv, hval⟩
    exact ⟨(v, true), ⟨v, hv, rfl⟩, by simp [litSat, hval]⟩

/-! ## (2) "At most one": pairwise mutual exclusion -/

/-- All ordered/forward pairs `(x, y)` with `x` the head and `y` ranging over `ys`. -/
private def pairWithHead {n : ℕ} (x : Fin n) (ys : List (Fin n)) : List (Fin n × Fin n) :=
  ys.map (x, ·)

/-- For each unordered pair `i < j` (in list order) in `vars`, the exclusion clause
`¬vᵢ ∨ ¬vⱼ` forbidding both being `true`. -/
def atMostOne {n : ℕ} : List (Fin n) → List (Clause n)
  | [] => []
  | x :: xs => (pairWithHead x xs).map (fun p => [(p.1, false), (p.2, false)]) ++ atMostOne xs

/-- The two-literal exclusion clause `¬a ∨ ¬b` is satisfied iff not both `a`, `b` are `true`. -/
theorem notBoth_sat_iff {n : ℕ} (assign : Fin n → Bool) (a b : Fin n) :
    clauseSat assign [(a, false), (b, false)] = true ↔ ¬ (assign a = true ∧ assign b = true) := by
  simp only [clauseSat, List.any_cons, List.any_nil, litSat, Bool.or_false]
  constructor
  · intro h ⟨ha, hb⟩
    rw [ha, hb] at h; simp at h
  · intro h
    by_cases ha : assign a = true
    · by_cases hb : assign b = true
      · exact absurd ⟨ha, hb⟩ h
      · simp [hb]
    · simp [ha]

/-- Membership in `atMostOne (x :: xs)` splits into the head's exclusion clauses and the tail. -/
theorem mem_atMostOne_cons {n : ℕ} (x : Fin n) (xs : List (Fin n)) (c : Clause n) :
    c ∈ atMostOne (x :: xs) ↔
      ((∃ y ∈ xs, c = [(x, false), (y, false)]) ∨ c ∈ atMostOne xs) := by
  simp only [atMostOne, List.mem_append, List.mem_map, pairWithHead]
  constructor
  · rintro (⟨p, ⟨y, hy, rfl⟩, rfl⟩ | h)
    · exact Or.inl ⟨y, hy, rfl⟩
    · exact Or.inr h
  · rintro (⟨y, hy, rfl⟩ | h)
    · exact Or.inl ⟨(x, y), ⟨y, hy, rfl⟩, rfl⟩
    · exact Or.inr h

/-- `satisfiesAll (atMostOne (x :: xs))` splits into the head's pairwise exclusions
(`x` and any tail entry are not both `true`) and the tail's own `atMostOne`. -/
theorem satisfiesAll_atMostOne_cons {n : ℕ} (assign : Fin n → Bool) (x : Fin n)
    (xs : List (Fin n)) :
    satisfiesAll assign (atMostOne (x :: xs)) ↔
      ((∀ y ∈ xs, ¬ (assign x = true ∧ assign y = true)) ∧
        satisfiesAll assign (atMostOne xs)) := by
  constructor
  · intro h
    refine ⟨fun y hy => ?_, fun c hc => ?_⟩
    · rw [← notBoth_sat_iff]
      exact h _ ((mem_atMostOne_cons x xs _).2 (Or.inl ⟨y, hy, rfl⟩))
    · exact h c ((mem_atMostOne_cons x xs c).2 (Or.inr hc))
  · rintro ⟨hhead, htail⟩ c hc
    rw [mem_atMostOne_cons] at hc
    rcases hc with ⟨y, hy, rfl⟩ | hc
    · rw [notBoth_sat_iff]; exact hhead y hy
    · exact htail c hc

/-- **`atMostOne` semantics.** Every exclusion clause is satisfied iff **at most one** of `vars`
is assigned `true`, in the duplicate-robust form: the list of `true`-assigned entries has length
`≤ 1`. (The naive "pairwise distinct" form fails on lists with repeated variables — e.g.
`[x, x]` with `assign x = true` violates `atMostOne` yet has `x = x`; the filter-length form
correctly reports length `2`.) -/
theorem atMostOne_sat_iff {n : ℕ} (assign : Fin n → Bool) (vars : List (Fin n)) :
    satisfiesAll assign (atMostOne vars) ↔
      ((vars.filter (fun v => assign v)).length ≤ 1) := by
  induction vars with
  | nil => simp [atMostOne]
  | cons x xs ih =>
    rw [satisfiesAll_atMostOne_cons, ih, List.filter_cons]
    -- The head exclusions say: if `assign x = true`, no tail entry is `true`.
    have hhead_iff : (∀ y ∈ xs, ¬ (assign x = true ∧ assign y = true)) ↔
        (assign x = true → xs.filter (fun v => assign v) = []) := by
      constructor
      · intro hhead hx
        rw [List.filter_eq_nil_iff]
        intro y hy hdy
        exact hhead y hy ⟨hx, by simpa using hdy⟩
      · intro hhead y hy ⟨hax, hay⟩
        have : y ∈ xs.filter (fun v => assign v) := by
          rw [List.mem_filter]; exact ⟨hy, by simpa using hay⟩
        rw [hhead hax] at this; simp at this
    rw [hhead_iff]
    by_cases hx : assign x = true
    · rw [if_pos hx]
      simp only [hx, forall_true_left, List.length_cons]
      constructor
      · rintro ⟨hempty, _⟩; rw [hempty]; simp
      · intro hlen
        have hempty : xs.filter (fun v => assign v) = [] :=
          List.length_eq_zero_iff.1 (by omega)
        exact ⟨hempty, by rw [hempty]; simp⟩
    · rw [if_neg hx]
      constructor
      · rintro ⟨_, htail⟩; exact htail
      · intro htail; exact ⟨fun h => absurd h hx, htail⟩

/-! ## (3) "Exactly one": at least one and at most one -/

/-- The clause list "exactly one of `vars` is `true`": the disjunction plus all exclusions. -/
def exactlyOne {n : ℕ} (vars : List (Fin n)) : List (Clause n) :=
  atLeastOneTrue vars :: atMostOne vars

/-- **`exactlyOne` semantics.** All clauses are satisfied iff at least one of `vars` is `true`
*and* at most one is — equivalently, the list of `true`-assigned entries has length exactly `1`. -/
theorem exactlyOne_sat_iff {n : ℕ} (assign : Fin n → Bool) (vars : List (Fin n)) :
    satisfiesAll assign (exactlyOne vars) ↔
      ((∃ v ∈ vars, assign v = true) ∧
        ((vars.filter (fun v => assign v)).length ≤ 1)) := by
  rw [exactlyOne, satisfiesAll_cons, atLeastOneTrue_sat_iff, atMostOne_sat_iff]

/-- **`exactlyOne` length form.** All clauses are satisfied iff *exactly one* of `vars` is `true`:
the `true`-assigned sublist has length `1`. -/
theorem exactlyOne_sat_iff_length {n : ℕ} (assign : Fin n → Bool) (vars : List (Fin n)) :
    satisfiesAll assign (exactlyOne vars) ↔
      ((vars.filter (fun v => assign v)).length = 1) := by
  rw [exactlyOne_sat_iff]
  constructor
  · rintro ⟨⟨v, hv, hvt⟩, hle⟩
    have hpos : 0 < (vars.filter (fun v => assign v)).length := by
      rw [List.length_pos_iff_exists_mem]
      exact ⟨v, by rw [List.mem_filter]; exact ⟨hv, by simpa using hvt⟩⟩
    omega
  · intro hlen
    have hpos : 0 < (vars.filter (fun v => assign v)).length := by omega
    rw [List.length_pos_iff_exists_mem] at hpos
    obtain ⟨v, hv⟩ := hpos
    rw [List.mem_filter] at hv
    exact ⟨⟨v, hv.1, by simpa using hv.2⟩, by omega⟩

/-! ## (4) Implication `¬a ∨ b` -/

/-- The implication clause `a → b`, i.e. `¬a ∨ b`. -/
def implies {n : ℕ} (a b : Literal n) : Clause n := [(a.1, !a.2), b]

/-- **`implies` semantics.** `¬a ∨ b` is satisfied iff `a`'s satisfaction implies `b`'s. -/
theorem implies_sat_iff {n : ℕ} (assign : Fin n → Bool) (a b : Literal n) :
    clauseSat assign (implies a b) = true ↔ (litSat assign a = true → litSat assign b = true) := by
  simp only [implies, clauseSat, List.any_cons, List.any_nil, litSat, Bool.or_false]
  constructor
  · intro h ha
    rw [Bool.or_eq_true] at h
    rcases h with h' | h'
    · exfalso
      -- `assign a.1 == !a.2` true means `assign a.1 = !a.2`, contradicting `assign a.1 = a.2`
      rw [beq_iff_eq] at h' ha
      rw [ha] at h'
      exact absurd h' (by simp)
    · exact h'
  · intro h
    by_cases ha : (assign a.1 == a.2) = true
    · rw [h ha]; simp
    · -- `assign a.1 ≠ a.2` over `Bool` means `assign a.1 = !a.2`, so the first literal is true
      have hfst : (assign a.1 == !a.2) = true := by
        rw [Bool.not_eq_true, beq_eq_false_iff_ne] at ha
        rw [beq_iff_eq]
        cases hb : assign a.1 <;> cases hc : a.2 <;> simp_all
      rw [hfst]; simp

/-! ## Restatements: each builder's iff against its intended wording -/

-- `atLeastOne`: the clause is satisfied iff some literal in it is true.
example {n : ℕ} (assign : Fin n → Bool) (lits : List (Literal n)) :
    clauseSat assign (atLeastOne lits) = true ↔ ∃ l ∈ lits, litSat assign l = true :=
  atLeastOne_sat_iff assign lits

-- `atLeastOneTrue`: the clause is satisfied iff some variable is assigned `true`.
example {n : ℕ} (assign : Fin n → Bool) (vars : List (Fin n)) :
    clauseSat assign (atLeastOneTrue vars) = true ↔ ∃ v ∈ vars, assign v = true :=
  atLeastOneTrue_sat_iff assign vars

-- `atMostOne`: all exclusions hold iff at most one variable is assigned `true`.
example {n : ℕ} (assign : Fin n → Bool) (vars : List (Fin n)) :
    satisfiesAll assign (atMostOne vars) ↔ (vars.filter (fun v => assign v)).length ≤ 1 :=
  atMostOne_sat_iff assign vars

-- `exactlyOne`: all clauses hold iff exactly one variable is assigned `true`.
example {n : ℕ} (assign : Fin n → Bool) (vars : List (Fin n)) :
    satisfiesAll assign (exactlyOne vars) ↔ (vars.filter (fun v => assign v)).length = 1 :=
  exactlyOne_sat_iff_length assign vars

-- `implies`: the clause `¬a ∨ b` is satisfied iff `a`'s satisfaction implies `b`'s.
example {n : ℕ} (assign : Fin n → Bool) (a b : Literal n) :
    clauseSat assign (implies a b) = true ↔ (litSat assign a = true → litSat assign b = true) :=
  implies_sat_iff assign a b

-- `eval_append`: a concatenated formula evaluates iff each half does.
example {n : ℕ} (assign : Fin n → Bool) (c₁ c₂ : List (Clause n)) :
    eval ⟨n, c₁ ++ c₂⟩ assign = true ↔
      (eval ⟨n, c₁⟩ assign = true ∧ eval ⟨n, c₂⟩ assign = true) :=
  eval_append assign c₁ c₂

end DeepWiki.BooleanConstraints
