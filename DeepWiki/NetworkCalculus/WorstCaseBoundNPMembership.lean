import DeepWiki.NetworkCalculus.WorstCaseBoundNPHardness
import DeepWiki.NetworkCalculus.WorstCaseBoundX3CReductionBridge

/-! # NP-membership and NP-completeness of worst-case-backlog decision (DNC Theorem 10.2)
`WorstCaseBoundNPHardness` proves worst-case-backlog decision is **NP-hard** (modulo the
cited `X3CIsNPHard` axiom). This file proves it is also **in NP** — axiom-free — and
concludes it is **NP-complete**.

**The certificate is the exact-cover assignment.** `worstCaseBacklogDecision w` holds iff
the bundled X3C instance `w.I` has an exact 3-cover, iff some assignment `assign : w.α →
w.ι` is feasible (`IsAssignment`) and saturates `w.I.q` subsets (`saturatedCount = q`).
That assignment is the natural NP-witness. But the verifier-form `IsInNP` needs `Cert` to
be a *single* `Type`, while `w.α`, `w.ι` vary with `w`. We therefore **encode** the
assignment as a `List ℕ` (`encodeAssign`): the list of subset-indices each element routes
to, indexed by `Fintype.equivFin`. The checker `check w c` asserts that `c` is the encoding
of some feasible, `q`-saturating assignment — a *finite, decidable* existential
(`Fintype.decidableExistsFintype` over the finite function type `w.α → w.ι`), genuinely
tied to `c` because `encodeAssign` is injective (`encodeAssign_injective`), so `c`
*determines* the assignment.

**Honest cost model** (matching `KarpReduction` / `IsInNP`): "poly-time checker" is modeled
by the certificate **size bound** plus decidability, NOT a Turing-machine time model. We
exhibit an explicit `certPoly = (X + 1)^2` and show a valid certificate has
`sizeCert ≤ certPoly.eval (size w)` with `size w = card ι + card α` and
`sizeCert c = c.length + c.sum` (a valid assignment encoding has `card α` entries, each
`< card ι`). This is the same structural proxy used throughout the framework, made
explicit.

**What is axiom-free vs cited.** NP-membership (this file's `isInNP_*`) is axiom-free: a
real certificate type, a decidable checker, and a `spec` chained from the existing
`threshold_le_worstCaseBacklog_iff_exists_cover` and
`exists_saturatedCount_eq_q_iff_exists_cover`. NP-completeness `=`
NP-hardness `∧` NP-membership; only the NP-hardness half rests on the single cited
`X3CIsNPHard` axiom (Garey-Johnson X3C-completeness). -/

namespace DeepWiki

open Finset Polynomial

/-! ## `IsNPComplete`: NP-hard and in NP
The `KarpReduction` framework has `IsNPHard` and `IsInNP` but no `IsNPComplete`; we define
it as the conjunction (the standard definition: `Q` is NP-complete iff it is NP-hard and in
NP). -/

/-- `Q : τ → Prop` is **NP-complete** (relative to encoding size `sizeτ`): it is NP-hard
(`IsNPHard`) and in NP (`IsInNP`). The standard definition; the only cited input downstream
is the seed problem's NP-completeness (here `X3CIsNPHard`), which the NP-hardness half rests
on, while the NP-membership half is axiom-free. -/
structure IsNPComplete {τ : Type*} (sizeτ : τ → ℕ) (Q : τ → Prop) : Prop where
  /-- `Q` is NP-hard: every NP problem Karp-reduces to it. -/
  isNPHard : IsNPHard sizeτ Q
  /-- `Q` is in NP: membership has a polynomially-bounded, decidably-checked certificate. -/
  isInNP : Nonempty (IsInNP sizeτ Q)

/-! ## The certificate encoding
An assignment `assign : w.α → w.ι` encodes to the `List ℕ` of subset-indices each element
routes to, indexed by `Fintype.equivFin`. The encoding is injective, so the certificate
determines the assignment. -/

/-- The element-indexing equivalence `w.α ≃ Fin (card α)` (from `Fintype.equivFin`). -/
noncomputable def WellFormedX3C.eltEquiv (w : WellFormedX3C) :
    w.α ≃ Fin (Fintype.card w.α) :=
  Fintype.equivFin w.α

/-- The subset-indexing equivalence `w.ι ≃ Fin (card ι)` (from `Fintype.equivFin`). -/
noncomputable def WellFormedX3C.subsetEquiv (w : WellFormedX3C) :
    w.ι ≃ Fin (Fintype.card w.ι) :=
  Fintype.equivFin w.ι

/-- **The certificate encoding of an assignment**: the `List ℕ` whose `j`-th entry is the
index (in `0..card ι − 1`) of the subset that the `j`-th element routes to under `assign`.
Length `card α`, entries `< card ι`. -/
noncomputable def WellFormedX3C.encodeAssign (w : WellFormedX3C) (assign : w.α → w.ι) :
    List ℕ :=
  (List.finRange (Fintype.card w.α)).map
    (fun j => (w.subsetEquiv (assign (w.eltEquiv.symm j))).val)

/-- The encoding has length `card α`. -/
theorem WellFormedX3C.encodeAssign_length (w : WellFormedX3C) (assign : w.α → w.ι) :
    (w.encodeAssign assign).length = Fintype.card w.α := by
  simp [WellFormedX3C.encodeAssign]

/-- Every entry of the encoding is `< card ι` (a subset index). -/
theorem WellFormedX3C.encodeAssign_lt (w : WellFormedX3C) (assign : w.α → w.ι)
    {n : ℕ} (hn : n ∈ w.encodeAssign assign) : n < Fintype.card w.ι := by
  simp only [WellFormedX3C.encodeAssign, List.mem_map] at hn
  obtain ⟨j, _, rfl⟩ := hn
  exact (w.subsetEquiv (assign (w.eltEquiv.symm j))).isLt

/-- **The encoding is injective**: distinct assignments encode to distinct lists, so the
certificate determines the assignment. (Two encodings agree pointwise at every element
index, hence the assignments agree at every element.) -/
theorem WellFormedX3C.encodeAssign_injective (w : WellFormedX3C) :
    Function.Injective w.encodeAssign := by
  intro a b hab
  funext e
  -- read off the entry at the element's index via `getElem?`, where the lists agree by `hab`
  have hidx : (w.encodeAssign a)[(w.eltEquiv e : ℕ)]? =
      (w.encodeAssign b)[(w.eltEquiv e : ℕ)]? := by rw [hab]
  have hlt : (w.eltEquiv e : ℕ) < Fintype.card w.α := (w.eltEquiv e).isLt
  simp only [WellFormedX3C.encodeAssign, List.getElem?_map, List.getElem?_eq_getElem,
    List.length_finRange, hlt, List.getElem_finRange, Fin.cast_mk, Fin.eta,
    Equiv.symm_apply_apply, Option.map_some, Option.some.injEq] at hidx
  exact w.subsetEquiv.injective (Fin.ext hidx)

/-! ## The verifier
`sizeCert c = c.length + c.sum`; `check w c` asserts `c` encodes a feasible assignment
saturating `w.I.q` subsets (equivalently, an exact cover). The check is decidable: a finite
existential over the function type `w.α → w.ι` of decidable conjuncts. -/

/-- The **certificate size**: list length plus sum of entries (`card α` entries, each a
subset index `< card ι`), bounding both the count and the magnitudes of the encoded
assignment. -/
def WellFormedX3C.sizeCert (c : List ℕ) : ℕ := c.length + c.sum

/-- **The verifier predicate**: `c` is the encoding of some assignment that is feasible
(`IsAssignment`) and saturates `w.I.q` subsets (`saturatedCount = q`) — equivalently
encodes an exact 3-cover. A *finite, decidable* existential over `w.α → w.ι` (the
certificate `c` pins the assignment via `encodeAssign_injective`). -/
def WellFormedX3C.check (w : WellFormedX3C) (c : List ℕ) : Prop :=
  ∃ assign : w.α → w.ι,
    w.encodeAssign assign = c ∧ w.I.IsAssignment assign ∧
      w.I.saturatedCount assign = w.I.q

/-- The verifier is decidable: a finite existential (`w.α → w.ι` is a `Fintype`) over
decidable conjuncts (`IsAssignment` is `∀`-over-a-Fintype, `saturatedCount` and the
encoding are computable `ℕ`/`List ℕ`). -/
noncomputable instance WellFormedX3C.instDecidableCheck (w : WellFormedX3C) (c : List ℕ) :
    Decidable (w.check c) := by
  classical
  unfold WellFormedX3C.check X3CInstance.IsAssignment
  infer_instance

/-! ## The certificate polynomial and the size bound
A valid certificate `c = encodeAssign assign` has `c.length = card α` and entries `< card ι`,
so `c.sum ≤ card α · card ι`; hence `sizeCert c ≤ card α + card α · card ι ≤ (size + 1)^2 =
certPoly.eval (size w)` with `certPoly = (X + 1)^2`. -/

/-- The **certificate polynomial** `(X + 1)^2`: bounds the encoding size of a valid
assignment by `(size + 1)^2`, with `size = card ι + card α`. -/
noncomputable def certPolyWCB : Polynomial ℕ := (Polynomial.X + 1) ^ 2

/-- `certPolyWCB.eval n = (n + 1)^2`. -/
theorem certPolyWCB_eval (n : ℕ) : certPolyWCB.eval n = (n + 1) ^ 2 := by
  simp [certPolyWCB]

/-- A valid certificate's size is bounded by `certPolyWCB.eval (size w)`: an encoded
assignment has `card α` entries each `< card ι`, so
`length + sum ≤ card α + card α · card ι ≤ (card ι + card α + 1)^2`. -/
theorem WellFormedX3C.sizeCert_encodeAssign_le (w : WellFormedX3C) (assign : w.α → w.ι) :
    WellFormedX3C.sizeCert (w.encodeAssign assign) ≤ certPolyWCB.eval w.size := by
  rw [certPolyWCB_eval, WellFormedX3C.size, WellFormedX3C.sizeCert,
    w.encodeAssign_length assign]
  -- bound the sum: `card α` entries, each `< card ι`, so `sum ≤ card α * card ι`
  have hsum : (w.encodeAssign assign).sum ≤ Fintype.card w.α * Fintype.card w.ι := by
    calc (w.encodeAssign assign).sum
        ≤ (w.encodeAssign assign).length * Fintype.card w.ι := by
          apply List.sum_le_card_nsmul
          intro n hn
          exact le_of_lt (w.encodeAssign_lt assign hn)
      _ = Fintype.card w.α * Fintype.card w.ι := by rw [w.encodeAssign_length assign]
  set a := Fintype.card w.α
  set i := Fintype.card w.ι
  calc a + (w.encodeAssign assign).sum
      ≤ a + a * i := by exact Nat.add_le_add_left hsum a
    _ ≤ (i + a + 1) ^ 2 := by nlinarith [Nat.zero_le a, Nat.zero_le i]

/-! ## NP-membership: the `spec` and the `IsInNP` instance
The verifier `spec` chains the existing combinatorial bi-implications: the decision holds
iff a cover exists iff a feasible assignment saturates `q` subsets, which (encoded) is a
poly-bounded passing certificate. -/

/-- **The verifier `spec`**: `worstCaseBacklogDecision w` holds iff some poly-bounded
certificate passes the check. Forward: a cover gives a feasible `q`-saturating assignment
(`exists_saturatedCount_eq_q_iff_exists_cover`), whose encoding is a passing,
size-bounded certificate. Backward: a passing certificate yields such an assignment, hence
a cover, hence the decision (via `threshold_le_worstCaseBacklog_iff_exists_cover`). -/
theorem worstCaseBacklogDecision_iff_exists_cert (w : WellFormedX3C) :
    worstCaseBacklogDecision w ↔
      ∃ c, WellFormedX3C.sizeCert c ≤ certPolyWCB.eval w.size ∧ w.check c := by
  constructor
  · intro hdec
    -- decision ⇒ cover ⇒ feasible q-saturating assignment
    have hcover : ∃ assign C, w.I.IsExactCover C assign ∧
        (∀ e, ∃ i ∈ C, e ∈ w.I.members i) :=
      (w.I.threshold_le_worstCaseBacklog_iff_exists_cover w.hasAssignment w.qle).mp hdec
    obtain ⟨assign, hassign, hsat⟩ :=
      (w.I.exists_saturatedCount_eq_q_iff_exists_cover).mpr hcover
    refine ⟨w.encodeAssign assign, w.sizeCert_encodeAssign_le assign, ?_⟩
    exact ⟨assign, rfl, hassign, hsat⟩
  · rintro ⟨c, _, assign, _, hassign, hsat⟩
    -- a passing certificate ⇒ feasible q-saturating assignment ⇒ cover ⇒ decision
    have hcover : ∃ assign C, w.I.IsExactCover C assign ∧
        (∀ e, ∃ i ∈ C, e ∈ w.I.members i) :=
      (w.I.exists_saturatedCount_eq_q_iff_exists_cover).mp ⟨assign, hassign, hsat⟩
    exact (w.I.threshold_le_worstCaseBacklog_iff_exists_cover w.hasAssignment w.qle).mpr
      hcover

/-- **Worst-case-backlog decision is in NP** (axiom-free): certificate `List ℕ` (the
encoded exact-cover assignment), size `length + sum`, decidable verifier `check`,
certificate polynomial `(X + 1)^2`, and the `spec` from
`worstCaseBacklogDecision_iff_exists_cert`. The poly-time of the checker is modeled by the
certificate size bound + decidability (the honest framework proxy), not a TM cost model. -/
noncomputable def isInNP_worstCaseBacklogDecision :
    IsInNP WellFormedX3C.size worstCaseBacklogDecision where
  Cert := List ℕ
  sizeCert := WellFormedX3C.sizeCert
  check := WellFormedX3C.check
  decCheck := WellFormedX3C.instDecidableCheck
  certPoly := certPolyWCB
  spec := worstCaseBacklogDecision_iff_exists_cert

/-! ## NP-completeness
NP-hard (`isNPHard_worstCaseBacklogDecision`, modulo the cited `X3CIsNPHard`) and in NP
(`isInNP_worstCaseBacklogDecision`, axiom-free) give NP-completeness. -/

/-- **Worst-case-backlog decision is NP-complete** (Theorem 10.2, upgraded): NP-hard
(modulo the single cited `X3CIsNPHard` axiom, Garey-Johnson X3C-completeness) and in NP
(axiom-free). -/
theorem isNPComplete_worstCaseBacklogDecision :
    IsNPComplete WellFormedX3C.size worstCaseBacklogDecision where
  isNPHard := isNPHard_worstCaseBacklogDecision
  isInNP := ⟨isInNP_worstCaseBacklogDecision⟩

/-! ## Book restatement (Theorem 10.2, NP-completeness)
Computing the exact worst-case backlog is NP-complete: NP-hard (the Figure-10.7 X3C
reduction, modulo X3C's cited NP-completeness) and in NP (the exact-cover assignment is a
decidably-checkable, polynomially-bounded certificate — axiom-free). The certificate is the
assignment encoded as a `List ℕ` of subset indices; the verifier confirms it encodes a
feasible `q`-saturating assignment; the size proxy is `(card ι + card α + 1)^2`. -/
example :
    -- in NP: there is a certificate scheme whose verifier `spec` decides the problem
    Nonempty (IsInNP WellFormedX3C.size worstCaseBacklogDecision) ∧
    -- NP-hard (modulo cited X3C-completeness)
    IsNPHard WellFormedX3C.size worstCaseBacklogDecision ∧
    -- hence NP-complete
    IsNPComplete WellFormedX3C.size worstCaseBacklogDecision :=
  ⟨⟨isInNP_worstCaseBacklogDecision⟩, isNPHard_worstCaseBacklogDecision,
   isNPComplete_worstCaseBacklogDecision⟩

/-- NP-membership is genuinely axiom-free: the verifier `spec` holds for every well-formed
instance, decided by the `check` predicate (the certificate is the encoded exact-cover
assignment). -/
example (w : WellFormedX3C) :
    worstCaseBacklogDecision w ↔
      ∃ c, WellFormedX3C.sizeCert c ≤ certPolyWCB.eval w.size ∧ w.check c :=
  worstCaseBacklogDecision_iff_exists_cert w

end DeepWiki
