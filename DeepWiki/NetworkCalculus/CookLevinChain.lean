import DeepWiki.NetworkCalculus.ThreeSatReduction
import DeepWiki.NetworkCalculus.ThreeDMReduction
import DeepWiki.NetworkCalculus.ThreeDimensionalMatchingReduction
import DeepWiki.NetworkCalculus.WorstCaseBoundNPHardness

/-! # Closing the Cook–Levin chain to DNC Theorem 10.2
The reductions `SAT ≤ₖ 3SAT ≤ₖ 3DM ≤ₖ X3C ≤ₖ worst-case-backlog` are all proved, but the
`3SAT ≤ₖ 3DM` leg measures its **source** by `ThreeDM.cnfSize = numVars + #clauses + #literals`
whereas Cook–Levin (`isNPHard_TM_threeSat`) is stated against `(cnfEncode ·).length`. The two
differ by `numVars`: `cnfEncode` records the variable count as a single list entry, so a formula
with many *unused* variables has a tiny encoding but a huge gadget (rings grow as `numVars²`).

This file supplies the missing **variable-compaction** prepass `compactCnf`, dropping variables
absent from every literal and relabelling the rest into a contiguous block `Fin k` with
`k = #used variables ≤ #literals`. It preserves 3-CNF-ness and satisfiability (both directions),
so `threeSat φ ↔ threeSat (compactCnf φ)`, and gives the size bound `cnfSize (compactCnf φ) ≤
poly ((cnfEncode φ).length)` because `numVars(compactCnf φ) ≤ #literals` and `#clauses`,
`#literals` are each `≤ (cnfEncode φ).length`. Packaged as `compactRed`, composed with the rest of
the chain, and capped by `isNPHard_TM_worstCaseBacklog` over the genuine TM NP class (modulo the
single `cookLevin` tableau axiom). -/

namespace DeepWiki

open CnfFormula

/-! ## Used variables
`usedVars φ` is the set of variable indices occurring in *some* literal of *some* clause. Its
cardinality is the new variable count after compaction. -/

/-- The set of variable indices occurring in some literal of some clause of `φ`. -/
def usedVars (φ : CnfFormula) : Finset (Fin φ.numVars) :=
  (φ.clauses.flatMap (fun c => c.map Prod.fst)).toFinset

/-- A variable is **used** iff it is the variable of some literal of some clause. -/
theorem mem_usedVars_iff {φ : CnfFormula} (v : Fin φ.numVars) :
    v ∈ usedVars φ ↔ ∃ c ∈ φ.clauses, ∃ l ∈ c, l.1 = v := by
  simp only [usedVars, List.mem_toFinset, List.mem_flatMap, List.mem_map]

/-- A literal's variable, for a literal occurring in a clause of `φ`, is used. -/
theorem mem_usedVars_of_mem {φ : CnfFormula} {c : Clause φ.numVars} (hc : c ∈ φ.clauses)
    {l : Literal φ.numVars} (hl : l ∈ c) : l.1 ∈ usedVars φ :=
  (mem_usedVars_iff l.1).2 ⟨c, hc, l, hl, rfl⟩

/-- The compacted variable count `k = #used variables`. -/
def compactNumVars (φ : CnfFormula) : ℕ := (usedVars φ).card

/-! ## The relabelling equiv `usedVars φ ≃ Fin k`
`Finset.equivFin` gives the noncomputable bijection between the used-variable subtype and
`Fin k`; its forward direction re-indexes used variables to the compact range, its inverse
re-expands compact indices back to original variables. -/

/-- The relabelling bijection `usedVars φ ≃ Fin (compactNumVars φ)`. -/
noncomputable def reindexEquiv (φ : CnfFormula) :
    {v // v ∈ usedVars φ} ≃ Fin (compactNumVars φ) :=
  (usedVars φ).equivFin

/-- Re-index a used variable into the compact range. -/
noncomputable def reindexVar {φ : CnfFormula} (v : Fin φ.numVars) (hv : v ∈ usedVars φ) :
    Fin (compactNumVars φ) :=
  reindexEquiv φ ⟨v, hv⟩

/-- Expand a compact index back to its original variable (the chosen representative). -/
noncomputable def expandVar (φ : CnfFormula) (w : Fin (compactNumVars φ)) : Fin φ.numVars :=
  ((reindexEquiv φ).symm w).val

/-- `expandVar` of `reindexVar` is the identity (round-trip on used variables). -/
theorem expandVar_reindexVar {φ : CnfFormula} (v : Fin φ.numVars) (hv : v ∈ usedVars φ) :
    expandVar φ (reindexVar v hv) = v := by
  simp only [expandVar, reindexVar, Equiv.symm_apply_apply]

/-! ## Relabelling literals and clauses
A literal `(v, s)` of `φ` with `v ∈ usedVars φ` is relabelled to `(reindexVar v, s)`; a clause is
relabelled literal-by-literal (carrying the used-variable proofs via `List.pmap`). -/

/-- Relabel one clause into the compact variable space, given that every literal's variable is
used. -/
noncomputable def relabelClause {φ : CnfFormula} (c : Clause φ.numVars)
    (hc : ∀ l ∈ c, l.1 ∈ usedVars φ) : Clause (compactNumVars φ) :=
  c.pmap (fun l (hl : l.1 ∈ usedVars φ) => (reindexVar l.1 hl, l.2)) hc

/-- Relabelling preserves clause length. -/
theorem length_relabelClause {φ : CnfFormula} (c : Clause φ.numVars)
    (hc : ∀ l ∈ c, l.1 ∈ usedVars φ) : (relabelClause c hc).length = c.length := by
  simp only [relabelClause, List.length_pmap]

/-- Relabel the whole clause list (carrying `c ∈ φ.clauses` so every literal's variable is
used). -/
noncomputable def relabelClauses (φ : CnfFormula) :
    List (Clause (compactNumVars φ)) :=
  φ.clauses.pmap (fun c (hc : c ∈ φ.clauses) =>
    relabelClause c (fun _ hl => mem_usedVars_of_mem hc hl)) (fun _ h => h)

/-- The **variable-compaction map**: `φ` with its used variables relabelled into `Fin k`
(`k = #used variables`), removing the unused ones. -/
noncomputable def compactCnf (φ : CnfFormula) : CnfFormula :=
  ⟨compactNumVars φ, relabelClauses φ⟩

@[simp] theorem compactCnf_numVars (φ : CnfFormula) :
    (compactCnf φ).numVars = compactNumVars φ := rfl

@[simp] theorem compactCnf_clauses (φ : CnfFormula) :
    (compactCnf φ).clauses = relabelClauses φ := rfl

/-! ## 3-CNF preservation
Relabelling preserves clause lengths, so `compactCnf` preserves the `≤ 3`-literal property. -/

/-- Membership in `relabelClauses φ`: every member is the relabelling of an original clause. -/
theorem mem_relabelClauses {φ : CnfFormula} {c' : Clause (compactNumVars φ)}
    (hc' : c' ∈ relabelClauses φ) :
    ∃ c, ∃ (hc : c ∈ φ.clauses),
      c' = relabelClause c (fun _ hl => mem_usedVars_of_mem hc hl) := by
  rw [relabelClauses, List.mem_pmap] at hc'
  obtain ⟨c, hc, heq⟩ := hc'
  exact ⟨c, hc, heq.symm⟩

/-- The compacted clause list has the same per-clause lengths as `φ` (literal counts unchanged).
Read off the `pmap` length equation, clause by clause. -/
theorem mem_relabelClauses_length {φ : CnfFormula} {c' : Clause (compactNumVars φ)}
    (hc' : c' ∈ relabelClauses φ) : ∃ c ∈ φ.clauses, c'.length = c.length := by
  obtain ⟨c, hc, rfl⟩ := mem_relabelClauses hc'
  exact ⟨c, hc, length_relabelClause c _⟩

/-- `compactCnf` preserves 3-CNF-ness (clause lengths are unchanged). -/
theorem is3Cnf_compactCnf {φ : CnfFormula} (h : Is3Cnf φ) : Is3Cnf (compactCnf φ) := by
  intro c' hc'
  rw [compactCnf_clauses] at hc'
  obtain ⟨c, hc, hlen⟩ := mem_relabelClauses_length hc'
  exact hlen ▸ h c hc

/-- The relabelled image of a clause `c ∈ φ.clauses` lies in the compacted clause list, with the
same length. -/
theorem exists_relabel_mem {φ : CnfFormula} {c : Clause φ.numVars} (hc : c ∈ φ.clauses) :
    ∃ c' ∈ relabelClauses φ, c'.length = c.length := by
  refine ⟨relabelClause c (fun l hl => mem_usedVars_of_mem hc hl), ?_, length_relabelClause c _⟩
  simp only [relabelClauses, List.mem_pmap]; exact ⟨c, hc, rfl⟩

/-- Conversely, `Is3Cnf (compactCnf φ) → Is3Cnf φ` (compaction is length-preserving both ways). -/
theorem is3Cnf_of_compactCnf {φ : CnfFormula} (h : Is3Cnf (compactCnf φ)) : Is3Cnf φ := by
  intro c hc
  obtain ⟨c', hc', hlen⟩ := exists_relabel_mem hc
  rw [← hlen]; exact h c' (by rw [compactCnf_clauses]; exact hc')

/-! ## Satisfiability equivalence
A literal `(v, s)` (with `v` used) and its relabelled image `(reindexVar v, s)` satisfy *the
same* truth value under the paired assignments `assign` and `assign ∘ expandVar` (forward) /
`assign'` and the used-branch extension (reverse). So clause and formula satisfaction transport
in both directions. -/

/-- **Forward literal transport.** A relabelled literal `(reindexVar l.1 hl, l.2)` is satisfied
by `assign ∘ expandVar` iff the original literal `l` is satisfied by `assign`. -/
theorem litSat_relabel_expand {φ : CnfFormula} (assign : Fin φ.numVars → Bool)
    (l : Literal φ.numVars) (hl : l.1 ∈ usedVars φ) :
    litSat (fun w => assign (expandVar φ w)) (reindexVar l.1 hl, l.2) = litSat assign l := by
  simp only [litSat, expandVar_reindexVar]

/-- **Forward clause transport.** If `assign` satisfies clause `c`, then `assign ∘ expandVar`
satisfies the relabelled clause. -/
theorem clauseSat_relabel_expand {φ : CnfFormula} (assign : Fin φ.numVars → Bool)
    (c : Clause φ.numVars) (hc : ∀ l ∈ c, l.1 ∈ usedVars φ)
    (hsat : clauseSat assign c = true) :
    clauseSat (fun w => assign (expandVar φ w)) (relabelClause c hc) = true := by
  rw [clauseSat_iff] at hsat ⊢
  obtain ⟨l, hlmem, hlsat⟩ := hsat
  refine ⟨(reindexVar l.1 (hc l hlmem), l.2), ?_, ?_⟩
  · simp only [relabelClause, List.mem_pmap]; exact ⟨l, hlmem, rfl⟩
  · rw [litSat_relabel_expand]; exact hlsat

/-- **Forward satisfiability.** `Satisfiable φ → Satisfiable (compactCnf φ)`: restrict a
satisfying assignment to the used variables, re-indexed. -/
theorem satisfiable_compactCnf_of {φ : CnfFormula} (hsat : Satisfiable φ) :
    Satisfiable (compactCnf φ) := by
  obtain ⟨assign, heval⟩ := hsat
  refine ⟨fun w => assign (expandVar φ w), ?_⟩
  rw [CnfFormula.eval, List.all_eq_true] at heval ⊢
  intro c' hc'
  rw [compactCnf_clauses] at hc'
  obtain ⟨c, hc, rfl⟩ := mem_relabelClauses hc'
  exact clauseSat_relabel_expand assign c _ (heval c hc)

/-- The reverse extension: a compact assignment `assign'` lifted to all original variables, set
arbitrarily (`false`) on the unused ones. -/
noncomputable def expandAssign {φ : CnfFormula} (assign' : Fin (compactNumVars φ) → Bool)
    (v : Fin φ.numVars) : Bool :=
  if hv : v ∈ usedVars φ then assign' (reindexVar v hv) else false

/-- **Reverse literal transport.** A relabelled literal is satisfied by `assign'` iff the
original literal is satisfied by `expandAssign assign'` (used variables only). -/
theorem litSat_relabel_expandAssign {φ : CnfFormula} (assign' : Fin (compactNumVars φ) → Bool)
    (l : Literal φ.numVars) (hl : l.1 ∈ usedVars φ) :
    litSat (expandAssign assign') l = litSat assign' (reindexVar l.1 hl, l.2) := by
  simp only [litSat, expandAssign, dif_pos hl]

/-- **Reverse clause transport.** If `assign'` satisfies a relabelled clause, then
`expandAssign assign'` satisfies the original clause. -/
theorem clauseSat_of_relabel_expandAssign {φ : CnfFormula}
    (assign' : Fin (compactNumVars φ) → Bool) (c : Clause φ.numVars)
    (hc : ∀ l ∈ c, l.1 ∈ usedVars φ)
    (hsat : clauseSat assign' (relabelClause c hc) = true) :
    clauseSat (expandAssign assign') c = true := by
  rw [clauseSat_iff] at hsat ⊢
  obtain ⟨l', hl'mem, hl'sat⟩ := hsat
  simp only [relabelClause, List.mem_pmap] at hl'mem
  obtain ⟨l, hlmem, rfl⟩ := hl'mem
  exact ⟨l, hlmem, by rw [litSat_relabel_expandAssign assign' l (hc l hlmem)]; exact hl'sat⟩

/-- **Reverse satisfiability.** `Satisfiable (compactCnf φ) → Satisfiable φ`: extend a compact
satisfying assignment to all variables (unused ones arbitrary). -/
theorem satisfiable_of_compactCnf {φ : CnfFormula} (hsat : Satisfiable (compactCnf φ)) :
    Satisfiable φ := by
  obtain ⟨assign', heval⟩ := hsat
  refine ⟨expandAssign assign', ?_⟩
  rw [CnfFormula.eval, List.all_eq_true] at heval ⊢
  intro c hc
  have hc' : relabelClause c (fun l hl => mem_usedVars_of_mem hc hl) ∈ relabelClauses φ := by
    simp only [relabelClauses, List.mem_pmap]; exact ⟨c, hc, rfl⟩
  rw [compactCnf_clauses] at heval
  exact clauseSat_of_relabel_expandAssign assign' c _ (heval _ hc')

/-- **Satisfiability equivalence.** `φ` is satisfiable iff its compaction is. -/
theorem satisfiable_compactCnf_iff (φ : CnfFormula) :
    Satisfiable φ ↔ Satisfiable (compactCnf φ) :=
  ⟨satisfiable_compactCnf_of, satisfiable_of_compactCnf⟩

/-- **3SAT equivalence.** `threeSat φ ↔ threeSat (compactCnf φ)` (3-CNF and satisfiability both
transport through compaction). -/
theorem threeSat_compactCnf_iff (φ : CnfFormula) :
    threeSat φ ↔ threeSat (compactCnf φ) := by
  constructor
  · rintro ⟨h3, hsat⟩
    exact ⟨is3Cnf_compactCnf h3, (satisfiable_compactCnf_iff φ).1 hsat⟩
  · rintro ⟨h3, hsat⟩
    exact ⟨is3Cnf_of_compactCnf h3, (satisfiable_compactCnf_iff φ).2 hsat⟩

/-! ## The polynomial size bound
After compaction `numVars = #used variables ≤ #literals`, while `#clauses` and `#literals` are
unchanged; the latter two are each `≤ (cnfEncode φ).length`. So `cnfSize (compactCnf φ) ≤
3 · (cnfEncode φ).length` — a linear (hence polynomial) bound against the genuine encoding. -/

/-- Relabelling preserves the clause count. -/
theorem length_relabelClauses (φ : CnfFormula) :
    (relabelClauses φ).length = φ.clauses.length := by
  simp only [relabelClauses, List.length_pmap]

/-- The length-map of the compacted clauses equals that of `φ` (each clause length unchanged). -/
theorem map_length_relabelClauses (φ : CnfFormula) :
    (relabelClauses φ).map List.length = φ.clauses.map List.length := by
  rw [relabelClauses, List.map_pmap]
  rw [List.pmap_congr_left _ (g := fun c (_ : c ∈ φ.clauses) => c.length)
    (fun c hc _ _ => length_relabelClause c (fun l hl => mem_usedVars_of_mem hc hl))]
  rw [List.pmap_eq_map]
  intro a ha; exact ha

/-- Relabelling preserves the total literal count (each clause length is unchanged). -/
theorem relabelClauses_litsum (φ : CnfFormula) :
    ((relabelClauses φ).map List.length).sum = (φ.clauses.map List.length).sum := by
  rw [map_length_relabelClauses]

/-- The used-variable count is bounded by the total literal count: `usedVars` is the dedup of the
list of all literal variables, whose length is `#literals`. -/
theorem compactNumVars_le_litsum (φ : CnfFormula) :
    compactNumVars φ ≤ (φ.clauses.map List.length).sum := by
  rw [compactNumVars, usedVars]
  refine (List.toFinset_card_le _).trans ?_
  rw [List.length_flatMap]
  refine le_of_eq ?_
  congr 1
  apply List.map_congr_left
  intro c _; rw [List.length_map]

/-- **The size bound** for the compaction reduction: `cnfSize (compactCnf φ) ≤
3 · (cnfEncode φ).length`. -/
theorem cnfSize_compactCnf_le (φ : CnfFormula) :
    ThreeDM.cnfSize (compactCnf φ) ≤ 3 * (cnfEncode φ).length := by
  set S := (φ.clauses.map List.length).sum with hS
  have henc : (cnfEncode φ).length = 2 + φ.clauses.length + 2 * S := cnfEncode_length φ
  have hsize : ThreeDM.cnfSize (compactCnf φ) =
      compactNumVars φ + (relabelClauses φ).length + ((relabelClauses φ).map List.length).sum :=
    rfl
  rw [length_relabelClauses, relabelClauses_litsum] at hsize
  have hvar : compactNumVars φ ≤ S := compactNumVars_le_litsum φ
  rw [hsize, ← hS]; omega

/-! ## The compaction Karp reduction `compactRed`
The compaction map, packaged as a `KarpReduction` whose **source size is `(cnfEncode ·).length`**
(the encoding Cook–Levin is stated against) and whose **target size is `ThreeDM.cnfSize`** (what
`threeSatToThreeDM` consumes). This is exactly the adapter the `3SAT ≤ₖ 3DM` leg needed. -/

/-- **The variable-compaction Karp reduction** `3SAT ≤ₖ 3SAT`, re-measuring the source by the
genuine `cnfEncode` length and the target by `ThreeDM.cnfSize` (so it composes onto
`threeSatToThreeDM`): correctness is `threeSat_compactCnf_iff`, the size bound is the linear
`3 · X`. -/
noncomputable def compactRed :
    KarpReduction (fun φ => (cnfEncode φ).length) ThreeDM.cnfSize threeSat threeSat where
  toFun := compactCnf
  correct := threeSat_compactCnf_iff
  poly := 3 * Polynomial.X
  size_bound φ := by simpa using cnfSize_compactCnf_le φ

/-! ## The X3C target-size encoding `x3cEnc`
`IsNPHard_TM.viaReduction` requires the reduction's *target* size to be `(ec z).length` for some
list-encoding `ec`. The chain's natural target size is `WellFormedX3C.size`; we realize it as a
list length by the trivial unary encoding `z ↦ replicate (size z) ()`, whose length is exactly
`WellFormedX3C.size z`. -/

/-- A trivial unary list-encoding of a well-formed X3C instance: a `replicate` block of length
`WellFormedX3C.size z`, so `(x3cEnc z).length = WellFormedX3C.size z`. -/
def x3cEnc (z : WellFormedX3C) : List Unit := List.replicate (WellFormedX3C.size z) ()

/-- `(x3cEnc z).length = WellFormedX3C.size z`: the unary encoding realizes the size as a length. -/
@[simp] theorem length_x3cEnc (z : WellFormedX3C) :
    (x3cEnc z).length = WellFormedX3C.size z := by
  simp only [x3cEnc, List.length_replicate]

/-! ## The full chain `worstCaseChain`
Compose `compactRed` with the (already-proved) `3SAT ≤ₖ 3DM ≤ₖ X3C ≤ₖ worst-case-backlog`, with
the target size adapted from `WellFormedX3C.size` to `(x3cEnc ·).length` (equal by
`length_x3cEnc`). This is the complete, genuine Karp reduction from 3SAT to the worst-case-backlog
decision problem at the encodings Cook–Levin is stated against. -/

/-- The composed reduction `3SAT ≤ₖ worst-case-backlog` measured at the genuine encodings:
source `(cnfEncode ·).length`, target `WellFormedX3C.size`. -/
noncomputable def threeSatToWorstCaseBacklog :
    KarpReduction (fun φ => (cnfEncode φ).length) WellFormedX3C.size
      threeSat worstCaseBacklogDecision :=
  ((x3cToWorstCaseBacklog.comp threeDMToX3C).comp threeSatToThreeDM).comp compactRed

/-- **The full Cook–Levin chain** `SAT ≤ₖ 3SAT ≤ₖ 3DM ≤ₖ X3C ≤ₖ worst-case-backlog`, with the
target size carried by the unary encoding `x3cEnc` (so it has the `(ec ·).length` shape
`IsNPHard_TM.viaReduction` expects). Source size is `(cnfEncode ·).length`, matching
`isNPHard_TM_threeSat`. The compaction prepass (`compactRed`) is exactly what makes the
`cnfEncode`-length source bound hold. -/
noncomputable def worstCaseChain :
    KarpReduction (fun φ => (cnfEncode φ).length) (fun z => (x3cEnc z).length)
      threeSat worstCaseBacklogDecision where
  toFun := threeSatToWorstCaseBacklog.toFun
  correct := threeSatToWorstCaseBacklog.correct
  poly := threeSatToWorstCaseBacklog.poly
  size_bound z := by
    simpa only [length_x3cEnc] using threeSatToWorstCaseBacklog.size_bound z

/-! ## The capstone — DNC Theorem 10.2 NP-hard over the genuine NP class
With `IsNPHard_TM`/`viaReduction` generalized to a `Type*` target (`ComplexityNP.lean` — the NP
*membership* side stays `Type 0`, only the target `Q` is `Type*`, so the `Type 1` instances
`WellFormedX3C`/`ThreeDMInstance` are now admissible targets), the capstone is
`isNPHard_TM_threeSat.viaReduction worstCaseChain`: **worst-case-backlog is NP-hard over the genuine
Turing-machine-grounded NP class, modulo only the `cookLevin` tableau axiom**. The `IsNPHardVia`
(unconditional, "relative to" 3SAT/SAT) forms are also recorded — they need no axiom at all. -/

/-- **DNC Theorem 10.2 — NP-hardness over the genuine TM NP class (capstone).** Worst-case-backlog
decision is `IsNPHard_TM`: every TM-grounded NP problem Karp-reduces to it, via Cook–Levin's SAT and
the full compacted chain `SAT ≤ₖ 3SAT ≤ₖ 3DM ≤ₖ X3C ≤ₖ worst-case-backlog`. `#print axioms` =
Mathlib's 3 standard axioms + exactly `cookLevin` — the single research-scale tableau is the only
unproved input; every reduction in the chain is genuine. -/
theorem isNPHard_TM_worstCaseBacklog :
    IsNPHard_TM x3cEnc worstCaseBacklogDecision :=
  isNPHard_TM_threeSat.viaReduction worstCaseChain

/-- **DNC Theorem 10.2 (NP-hardness relative to 3SAT), via the full compacted chain.**
Worst-case-backlog decision is NP-hard relative to 3SAT — `worstCaseChain` is a genuine Karp
reduction `3SAT ≤ₖ worst-case-backlog` at the Cook–Levin encodings. (The absolute
`IsNPHard_TM`-form is blocked only by the `Type 0`-vs-`Type 1` universe pin of `IsNPHard_TM`; see
the section note.) -/
theorem isNPHardVia_threeSat_worstCaseBacklog :
    KarpReduction.IsNPHardVia (fun φ => (cnfEncode φ).length) (fun z => (x3cEnc z).length)
      threeSat worstCaseBacklogDecision :=
  ⟨worstCaseChain⟩

/-- The chain rooted at **SAT** (Cook–Levin's actual seed): prepend `satToThreeSat` to get
`SAT ≤ₖ worst-case-backlog` at the genuine encodings, so worst-case-backlog is NP-hard relative to
SAT. (Same universe caveat as the 3SAT form for the absolute `IsNPHard_TM` statement.) -/
theorem isNPHardVia_sat_worstCaseBacklog :
    KarpReduction.IsNPHardVia (fun φ => (cnfEncode φ).length) (fun z => (x3cEnc z).length)
      Satisfiable worstCaseBacklogDecision :=
  ⟨worstCaseChain.comp satToThreeSat⟩

/-! ## Verification
Each headline restated as an anonymous `example` against its expected type. -/

-- Compaction preserves 3SAT (both directions).
example (φ : CnfFormula) : threeSat φ ↔ threeSat (compactCnf φ) := threeSat_compactCnf_iff φ

-- Compaction preserves satisfiability (both directions).
example (φ : CnfFormula) : Satisfiable φ ↔ Satisfiable (compactCnf φ) :=
  satisfiable_compactCnf_iff φ

-- The compaction size bound is linear in the genuine encoding length.
example (φ : CnfFormula) : ThreeDM.cnfSize (compactCnf φ) ≤ 3 * (cnfEncode φ).length :=
  cnfSize_compactCnf_le φ

-- The unary encoding realizes `WellFormedX3C.size` as a list length.
example (z : WellFormedX3C) : (x3cEnc z).length = WellFormedX3C.size z := length_x3cEnc z

-- The full chain is a genuine Karp reduction from 3SAT to worst-case-backlog at the genuine
-- (cnfEncode-length / x3cEnc-length) encodings.
noncomputable example :
    KarpReduction (fun φ => (cnfEncode φ).length) (fun z => (x3cEnc z).length)
      threeSat worstCaseBacklogDecision := worstCaseChain

-- NP-hardness of worst-case-backlog relative to 3SAT via the full compacted chain.
example :
    KarpReduction.IsNPHardVia (fun φ => (cnfEncode φ).length) (fun z => (x3cEnc z).length)
      threeSat worstCaseBacklogDecision := isNPHardVia_threeSat_worstCaseBacklog

-- The absolute capstone: worst-case-backlog NP-hard over the genuine TM NP class.
example : IsNPHard_TM x3cEnc worstCaseBacklogDecision := isNPHard_TM_worstCaseBacklog

end DeepWiki
