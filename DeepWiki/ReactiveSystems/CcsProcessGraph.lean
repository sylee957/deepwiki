import DeepWiki.ReactiveSystems.Ccs

/-! # Encoding finite process graphs as CCS
A finite process graph (states `Q`, labelled transition function
`δ : Q → Act A → List Q`) is encoded as a CCS process by taking the states as
process constants: each state `q` becomes the choice-sum, over every label and
successor, of the corresponding prefixed constant. The encoding is faithful — the
CCS constant `const q` has exactly the graph's transitions. -/

namespace DeepWiki.ReactiveSystems

variable {Q : Type*} {A : Type*}

/-- The CCS body of graph state `q`: the choice-sum, over every label `a` and
every successor `q' ∈ delta q a`, of the prefix `a.(const q')`. -/
def graphBody (delta : Q → Act A → List Q) (allActs : List (Act A)) (q : Q) : CCS A Q :=
  (allActs.flatMap (fun a => (delta q a).map (fun q' => CCS.pre a (CCS.const q')))).foldr
    CCS.choice CCS.nil

/-- The defining environment encoding a finite process graph as CCS: each state
`q` is a process constant whose body is `graphBody delta allActs q`. -/
def graphToCCS (delta : Q → Act A → List Q) (allActs : List (Act A)) : Q → CCS A Q :=
  graphBody delta allActs

/-- Faithfulness of the encoding: the CCS constant `const q` has exactly the
transitions of the graph — `const q —a→ R` iff `R = const q'` for some
successor `q' ∈ delta q a` (for any label `a` present in `allActs`). -/
theorem graphToCCS_step_iff (delta : Q → Act A → List Q) (allActs : List (Act A))
    (q : Q) (a : Act A) (R : CCS A Q) (ha : a ∈ allActs) :
    ((ccsLTS (graphToCCS delta allActs)) ⊢ CCS.const q ⟶[a] R) ↔
      ∃ q', q' ∈ delta q a ∧ R = CCS.const q' := by
  rw [ccsLTS_step, step_const_iff, graphToCCS, graphBody, step_foldr_choice_iff]
  constructor
  · rintro ⟨t, ht, hstep⟩
    rw [List.mem_flatMap] at ht
    obtain ⟨a', ha', hmem⟩ := ht
    rw [List.mem_map] at hmem
    obtain ⟨q', hq', rfl⟩ := hmem
    rw [step_pre_iff] at hstep
    obtain ⟨rfl, rfl⟩ := hstep
    exact ⟨q', hq', rfl⟩
  · rintro ⟨q', hq', rfl⟩
    refine ⟨CCS.pre a (CCS.const q'), ?_, by rw [step_pre_iff]; exact ⟨rfl, rfl⟩⟩
    rw [List.mem_flatMap]
    exact ⟨a, ha, List.mem_map.2 ⟨q', hq', rfl⟩⟩

end DeepWiki.ReactiveSystems
