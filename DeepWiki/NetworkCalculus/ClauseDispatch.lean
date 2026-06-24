import DeepWiki.NetworkCalculus.BooleanConstraints
import Mathlib.Data.Fin.Tuple.Basic

/-! # Clause dispatch & variable-space offset embedding (Cook–Levin tableau plumbing)

Two general SAT-infrastructure primitives used to assemble a Cook–Levin tableau formula:

* **`conditionOn`** — guards every clause of a clause set by "variable `v` is true",
  prepending the literal `(v, false)` so each clause becomes the implication `v → c`.
  This is the dispatch mechanism: clauses fire only on the selected branch.
* **`liftClauseL`/`liftClauseR`** — transport a clause set across a `Fin` index offset via
  `Fin.castAdd`/`Fin.natAdd`, embedding a formula over `Fin n` (resp. `Fin m`) into the
  combined variable space `Fin (n + m)`. The satisfaction-transport lemmas say a lifted
  clause set is satisfied by a combined assignment iff the original is satisfied by the
  assignment restricted to that block.

Everything is generic over the variable count — no tableau or Turing-machine types appear.
-/

namespace DeepWiki.BooleanConstraints

open CnfFormula

/-! ## Part 1 — `conditionOn`: guard a clause set by a variable -/

/-- Guard every clause of `cs` by "variable `v` is true": each `c` becomes `(v, false) :: c`,
encoding the implication `v → c`. -/
def conditionOn {n : ℕ} (v : Fin n) (cs : List (Clause n)) : List (Clause n) :=
  cs.map (fun c => (v, false) :: c)

/-- A clause is in `conditionOn v cs` iff it is `(v, false) :: c` for some `c ∈ cs`. -/
theorem mem_conditionOn {n : ℕ} (v : Fin n) (cs : List (Clause n)) (d : Clause n) :
    d ∈ conditionOn v cs ↔ ∃ c ∈ cs, d = (v, false) :: c := by
  simp only [conditionOn, List.mem_map, eq_comm]

/-- A guarded clause `(v, false) :: c` is satisfied iff `assign v = false` or `c` is. -/
theorem clauseSat_guard {n : ℕ} (assign : Fin n → Bool) (v : Fin n) (c : Clause n) :
    clauseSat assign ((v, false) :: c) = true ↔
      (assign v = false ∨ clauseSat assign c = true) := by
  simp only [clauseSat, List.any_cons, litSat, Bool.or_eq_true, beq_iff_eq]

/-- **Dispatch spec.** If `assign` satisfies the guarded set and the guard variable `v` is
`true`, then `assign` satisfies the original body `cs`. -/
theorem conditionOn_spec {n : ℕ} (assign : Fin n → Bool) (v : Fin n) (cs : List (Clause n))
    (h : satisfiesAll assign (conditionOn v cs)) (hv : assign v = true) :
    satisfiesAll assign cs := by
  intro c hc
  have hd : ((v, false) :: c) ∈ conditionOn v cs :=
    (mem_conditionOn v cs _).2 ⟨c, hc, rfl⟩
  rcases (clauseSat_guard assign v c).1 (h _ hd) with hvf | hcs
  · rw [hv] at hvf; exact absurd hvf (by simp)
  · exact hcs

/-- **Vacuous guard.** If the guard variable `v` is `false`, every guarded clause holds
(the guard literal `(v, false)` is satisfied), so the whole guarded set is satisfied. -/
theorem conditionOn_of_false {n : ℕ} (assign : Fin n → Bool) (v : Fin n) (cs : List (Clause n))
    (hv : assign v = false) : satisfiesAll assign (conditionOn v cs) := by
  intro d hd
  obtain ⟨c, _, rfl⟩ := (mem_conditionOn v cs d).1 hd
  exact (clauseSat_guard assign v c).2 (Or.inl hv)

/-- **Body ⟹ guarded.** If `assign` satisfies the body `cs`, it satisfies the guarded set
(each guarded clause holds via its tail). -/
theorem conditionOn_of_satisfiesAll {n : ℕ} (assign : Fin n → Bool) (v : Fin n)
    (cs : List (Clause n)) (h : satisfiesAll assign cs) :
    satisfiesAll assign (conditionOn v cs) := by
  intro d hd
  obtain ⟨c, hc, rfl⟩ := (mem_conditionOn v cs d).1 hd
  exact (clauseSat_guard assign v c).2 (Or.inr (h c hc))

/-- **Dispatch characterization.** The guarded set is satisfied iff the body is satisfied
whenever the guard variable `v` is `true`. -/
theorem satisfiesAll_conditionOn_iff {n : ℕ} (assign : Fin n → Bool) (v : Fin n)
    (cs : List (Clause n)) :
    satisfiesAll assign (conditionOn v cs) ↔ (assign v = true → satisfiesAll assign cs) := by
  constructor
  · intro h hv; exact conditionOn_spec assign v cs h hv
  · intro h
    by_cases hv : assign v = true
    · exact conditionOn_of_satisfiesAll assign v cs (h hv)
    · exact conditionOn_of_false assign v cs (by simpa using hv)

/-! ## Part 2 — `liftClause`: offset-embed a clause set into `Fin (n + m)`

Left block via `Fin.castAdd m : Fin n → Fin (n + m)`, right block via
`Fin.natAdd n : Fin m → Fin (n + m)`. -/

/-- Embed a left-block literal: `Fin.castAdd m` on the variable, sign unchanged. -/
def liftLitL {n m : ℕ} (l : Literal n) : Literal (n + m) := (Fin.castAdd m l.1, l.2)

/-- Embed a left-block clause by lifting each literal. -/
def liftClauseL {n m : ℕ} (c : Clause n) : Clause (n + m) := c.map liftLitL

/-- Embed a left-block clause set by lifting each clause. -/
def liftClausesL {n m : ℕ} (cs : List (Clause n)) : List (Clause (n + m)) := cs.map liftClauseL

/-- Embed a right-block literal: `Fin.natAdd n` on the variable, sign unchanged. -/
def liftLitR {n m : ℕ} (l : Literal m) : Literal (n + m) := (Fin.natAdd n l.1, l.2)

/-- Embed a right-block clause by lifting each literal. -/
def liftClauseR {n m : ℕ} (c : Clause m) : Clause (n + m) := c.map liftLitR

/-- Embed a right-block clause set by lifting each clause. -/
def liftClausesR {n m : ℕ} (cs : List (Clause m)) : List (Clause (n + m)) := cs.map liftClauseR

/-! ### Satisfaction transport (the key lemmas) -/

/-- A lifted left-block literal is satisfied by `assign` iff the original is satisfied by the
left-block restriction `i ↦ assign (Fin.castAdd m i)`. -/
@[simp] theorem litSat_liftLitL {n m : ℕ} (assign : Fin (n + m) → Bool) (l : Literal n) :
    litSat assign (liftLitL l) = litSat (fun i => assign (Fin.castAdd m i)) l := by
  simp [litSat, liftLitL]

/-- A lifted right-block literal is satisfied by `assign` iff the original is satisfied by the
right-block restriction `i ↦ assign (Fin.natAdd n i)`. -/
@[simp] theorem litSat_liftLitR {n m : ℕ} (assign : Fin (n + m) → Bool) (l : Literal m) :
    litSat assign (liftLitR l) = litSat (fun i => assign (Fin.natAdd n i)) l := by
  simp [litSat, liftLitR]

/-- A lifted left-block clause is satisfied by `assign` iff the original is satisfied by the
left-block restriction. -/
theorem clauseSat_liftClauseL {n m : ℕ} (assign : Fin (n + m) → Bool) (c : Clause n) :
    clauseSat assign (liftClauseL c) = clauseSat (fun i => assign (Fin.castAdd m i)) c := by
  simp [clauseSat, liftClauseL, List.any_map, Function.comp_def]

/-- A lifted right-block clause is satisfied by `assign` iff the original is satisfied by the
right-block restriction. -/
theorem clauseSat_liftClauseR {n m : ℕ} (assign : Fin (n + m) → Bool) (c : Clause m) :
    clauseSat assign (liftClauseR c) = clauseSat (fun i => assign (Fin.natAdd n i)) c := by
  simp [clauseSat, liftClauseR, List.any_map, Function.comp_def]

/-- A lifted left-block clause set is satisfied by a combined `assign` iff the original is
satisfied by the left-block restriction `i ↦ assign (Fin.castAdd m i)`. -/
theorem satisfiesAll_liftClausesL {n m : ℕ} (assign : Fin (n + m) → Bool) (cs : List (Clause n)) :
    satisfiesAll assign (liftClausesL cs) ↔
      satisfiesAll (fun i => assign (Fin.castAdd m i)) cs := by
  simp only [satisfiesAll, liftClausesL, List.mem_map]
  constructor
  · intro h c hc
    rw [← clauseSat_liftClauseL]
    exact h _ ⟨c, hc, rfl⟩
  · rintro h d ⟨c, hc, rfl⟩
    rw [clauseSat_liftClauseL]
    exact h c hc

/-- A lifted right-block clause set is satisfied by a combined `assign` iff the original is
satisfied by the right-block restriction `i ↦ assign (Fin.natAdd n i)`. -/
theorem satisfiesAll_liftClausesR {n m : ℕ} (assign : Fin (n + m) → Bool) (cs : List (Clause m)) :
    satisfiesAll assign (liftClausesR cs) ↔
      satisfiesAll (fun i => assign (Fin.natAdd n i)) cs := by
  simp only [satisfiesAll, liftClausesR, List.mem_map]
  constructor
  · intro h c hc
    rw [← clauseSat_liftClauseR]
    exact h _ ⟨c, hc, rfl⟩
  · rintro h d ⟨c, hc, rfl⟩
    rw [clauseSat_liftClauseR]
    exact h c hc

/-! ### Combined `eval` of two lifted formulas

`Fin.castAdd`/`Fin.natAdd` cover `Fin (n + m)` disjointly (`Fin.addCases_castAdd_natAdd`), so a
combined assignment is determined by its two blocks. The append of the two lifted clause sets is
satisfied iff each side is satisfied by its block restriction. -/

/-- **Combined transport.** The append of a left-lifted and a right-lifted clause set is
satisfied by `assign` iff the left set holds on the left-block restriction and the right set on
the right-block restriction. -/
theorem satisfiesAll_append_lift {n m : ℕ} (assign : Fin (n + m) → Bool)
    (cs : List (Clause n)) (ds : List (Clause m)) :
    satisfiesAll assign (liftClausesL cs ++ liftClausesR ds) ↔
      (satisfiesAll (fun i => assign (Fin.castAdd m i)) cs ∧
        satisfiesAll (fun i => assign (Fin.natAdd n i)) ds) := by
  rw [satisfiesAll_append, satisfiesAll_liftClausesL, satisfiesAll_liftClausesR]

/-- **Combined `eval`.** The combined formula `⟨n + m, liftClausesL cs ++ liftClausesR ds⟩`
evaluates to `true` under `assign` iff each side's formula evaluates to `true` under its block
restriction. -/
theorem eval_append_lift {n m : ℕ} (assign : Fin (n + m) → Bool)
    (cs : List (Clause n)) (ds : List (Clause m)) :
    eval ⟨n + m, liftClausesL cs ++ liftClausesR ds⟩ assign = true ↔
      (eval ⟨n, cs⟩ (fun i => assign (Fin.castAdd m i)) = true ∧
        eval ⟨m, ds⟩ (fun i => assign (Fin.natAdd n i)) = true) := by
  rw [eval_iff_satisfiesAll, eval_iff_satisfiesAll, eval_iff_satisfiesAll,
    satisfiesAll_append_lift]

/-! ## Restatements: each load-bearing lemma against its intended wording -/

-- `conditionOn_spec`: guard satisfied + guard var true ⟹ body satisfied.
example {n : ℕ} (assign : Fin n → Bool) (v : Fin n) (cs : List (Clause n))
    (h : satisfiesAll assign (conditionOn v cs)) (hv : assign v = true) :
    satisfiesAll assign cs :=
  conditionOn_spec assign v cs h hv

-- `satisfiesAll_liftClausesL`: a left-lifted set is satisfied iff the original is on the block.
example {n m : ℕ} (assign : Fin (n + m) → Bool) (cs : List (Clause n)) :
    satisfiesAll assign (liftClausesL cs) ↔
      satisfiesAll (fun i => assign (Fin.castAdd m i)) cs :=
  satisfiesAll_liftClausesL assign cs

end DeepWiki.BooleanConstraints
