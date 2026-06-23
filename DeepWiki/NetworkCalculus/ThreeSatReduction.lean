import DeepWiki.NetworkCalculus.BooleanSatisfiability
import DeepWiki.NetworkCalculus.KarpReduction
import DeepWiki.NetworkCalculus.CookLevin

/-! # The classic Karp reduction `SAT ≤ₖ 3SAT` (clause-splitting to 3-CNF)
The first leg of the chain connecting `cookLevin` toward DNC Theorem 10.2. A general CNF
formula is turned into an equisatisfiable 3-CNF formula by splitting every clause of length
`> 3` into a chain of 3-literal clauses linked by fresh auxiliary variables.

For a clause `[l₁,…,l_k]` with `k > 3` and fresh variables `z₁,…,z_{k-3}` the chain is

  `[l₁, l₂, z₁], [¬z₁, l₃, z₂], …, [¬z_{k-4}, l_{k-2}, z_{k-3}], [¬z_{k-3}, l_{k-1}, l_k]`.

Clauses of length `≤ 3` are kept (after re-indexing their literals into the enlarged
variable space). Both correctness directions and the 3-CNF guarantee are proved here.

**Design.** The split is decoupled into a *structural* recursion `splitChain` over a list of
already-cast literals, parameterised by a function `z : ℕ → Fin total` supplying the fresh
variables (so index validity is isolated from the recursion). A wrapper `splitClause` builds
`z` from a base offset, and `satToThreeSatMap` threads the running offset across clauses.
-/

namespace DeepWiki

open CnfFormula

/-! ## The 3-CNF predicate -/

/-- A CNF formula is in **3-CNF** iff every clause has at most three literals (the standard
"at most 3" form of 3SAT). -/
def Is3Cnf (φ : CnfFormula) : Prop := ∀ c ∈ φ.clauses, c.length ≤ 3

/-- `Is3Cnf` is decidable (a bounded check over the clause list). -/
instance (φ : CnfFormula) : Decidable (Is3Cnf φ) := by
  unfold Is3Cnf; infer_instance

/-- The empty formula is trivially 3-CNF. -/
@[simp] theorem is3Cnf_nil {n : ℕ} : Is3Cnf ⟨n, []⟩ := by
  intro c hc; simp at hc

/-! ## The structural clause-splitting chain

`splitChain z carry lits` splits a clause given as a `carry` prefix (the previous link's
`¬zᵢ`, or `none` for the first link) followed by the remaining literals `lits`, using fresh
variables `z 0, z 1, …`. All literals are already over the final space `Fin total`. -/

/-- Split a (cast) clause body into ≤3-literal clauses. `carry` is the optional leading
literal `¬zᵢ` linking from the previous clause; `lits` are the still-unplaced literals;
`z j` supplies the `j`-th fresh chaining variable. While `> 3` literals remain (counting the
carry) it peels enough literals to leave room for a fresh `z`, emitting a 3-literal clause
and recursing with `¬z` as the next carry. -/
def splitChain {total : ℕ} (z : ℕ → Fin total) :
    Option (Literal total) → List (Literal total) → ℕ → List (Clause total)
  | none, lits, _ =>
    -- first link, no carry
    if lits.length ≤ 3 then [lits]
    else match lits with
      | l₁ :: l₂ :: rest => [l₁, l₂, (z 0, true)] :: splitChain z (some (z 0, false)) rest 1
      | _ => [lits]  -- unreachable (length > 3 ⇒ at least 2 elements)
  | some c, lits, j =>
    -- a carry literal c occupies one slot; room for 2 more before needing a fresh z
    if lits.length ≤ 2 then [c :: lits]
    else match lits with
      | l₁ :: rest => [c, l₁, (z j, true)] :: splitChain z (some (z j, false)) rest (j + 1)
      | _ => [c :: lits]  -- unreachable (length > 2 ⇒ nonempty)

/-! ## Index bookkeeping -/

/-- Number of fresh aux variables a single clause needs: `length - 3` (zero for `≤ 3`). -/
def clauseAux {n : ℕ} (c : Clause n) : ℕ := c.length - 3

/-- Total number of fresh aux variables for a formula: the sum over its clauses. -/
def auxCount (φ : CnfFormula) : ℕ := (φ.clauses.map clauseAux).sum

/-- The output variable count: original variables plus all fresh aux variables. -/
def threeSatNumVars (φ : CnfFormula) : ℕ := φ.numVars + auxCount φ

/-- Re-index a literal of the original formula into the enlarged variable space `Fin total`
(`orig ≤ total`), keeping its sign. -/
def castLiteral {orig total : ℕ} (h : orig ≤ total) (l : Literal orig) : Literal total :=
  (Fin.castLE h l.1, l.2)

/-- A literal is satisfied through `castLiteral` iff it is satisfied by the restricted
assignment `assign ∘ castLE`. -/
@[simp] theorem litSat_castLiteral {orig total : ℕ} (h : orig ≤ total)
    (assign : Fin total → Bool) (l : Literal orig) :
    litSat assign (castLiteral h l) = litSat (fun i => assign (Fin.castLE h i)) l := rfl

/-! ## Computational equations for `splitChain`

Explicit equation lemmas (each provable by `rfl` / a single `if`-reduction) so proofs can
unfold one chain step without re-triggering the match-exhaustiveness side goals. -/

/-- `splitChain` with no carry on a short (`≤ 3`) clause is that single clause. -/
theorem splitChain_none_short {total : ℕ} (z : ℕ → Fin total) (lits : List (Literal total))
    (j : ℕ) (h : lits.length ≤ 3) : splitChain z none lits j = [lits] := by
  cases lits with
  | nil => rfl
  | cons l₁ tail =>
    cases tail with
    | nil => rfl
    | cons l₂ rest => rw [splitChain, if_pos h]

/-- `splitChain` with no carry on a long clause peels two literals and a fresh `z 0`. -/
theorem splitChain_none_long {total : ℕ} (z : ℕ → Fin total) (l₁ l₂ : Literal total)
    (rest : List (Literal total)) (j : ℕ) (h : ¬ (l₁ :: l₂ :: rest).length ≤ 3) :
    splitChain z none (l₁ :: l₂ :: rest) j =
      [l₁, l₂, (z 0, true)] :: splitChain z (some (z 0, false)) rest 1 := by
  rw [splitChain, if_neg h]

/-- `splitChain` with a carry on a `≤ 2`-clause is the carry prepended, a single clause. -/
theorem splitChain_some_short {total : ℕ} (z : ℕ → Fin total) (c : Literal total)
    (lits : List (Literal total)) (j : ℕ) (h : lits.length ≤ 2) :
    splitChain z (some c) lits j = [c :: lits] := by
  cases lits with
  | nil => rfl
  | cons l₁ rest => rw [splitChain, if_pos h]

/-- `splitChain` with a carry on a long clause peels one literal and a fresh `z j`. -/
theorem splitChain_some_long {total : ℕ} (z : ℕ → Fin total) (c l₁ : Literal total)
    (rest : List (Literal total)) (j : ℕ) (h : ¬ (l₁ :: rest).length ≤ 2) :
    splitChain z (some c) (l₁ :: rest) j =
      [c, l₁, (z j, true)] :: splitChain z (some (z j, false)) rest (j + 1) := by
  rw [splitChain, if_neg h]

/-! ## Backward direction: the chain forces a body literal true

For *any* assignment, if all clauses of `splitChain z carry lits j` are satisfied then either
the carry literal is true or some `lits` literal is true. This is the link forcing the
chain to "pass through" an original literal. -/

/-- A clause-list `all (clauseSat assign)` distributes over `cons`. -/
theorem all_clauseSat_cons {n : ℕ} (assign : Fin n → Bool) (c : Clause n)
    (cs : List (Clause n)) :
    (c :: cs).all (clauseSat assign) =
      (clauseSat assign c && cs.all (clauseSat assign)) := by simp

/-- A clause is satisfied iff some literal in it is true (the `∃ ∈` reading). -/
theorem clauseSat_iff {n : ℕ} (assign : Fin n → Bool) (c : Clause n) :
    clauseSat assign c = true ↔ ∃ l ∈ c, litSat assign l = true := by
  simp [clauseSat, List.any_eq_true]

/-- **Backward chain lemma.** If every clause emitted by `splitChain z carry lits j` is
satisfied by `assign`, then the carry literal is satisfied (when present) or some literal in
`lits` is satisfied. Proved by strong induction on `lits.length`. -/
theorem splitChain_forces {total : ℕ} (z : ℕ → Fin total) (assign : Fin total → Bool)
    (carry : Option (Literal total)) (lits : List (Literal total)) (j : ℕ)
    (hall : (splitChain z carry lits j).all (clauseSat assign) = true) :
    (∃ c, carry = some c ∧ litSat assign c = true) ∨
      (∃ l ∈ lits, litSat assign l = true) := by
  induction hn : lits.length using Nat.strong_induction_on generalizing carry lits j with
  | _ n ih =>
  subst hn
  cases carry with
  | none =>
    rcases lits with _ | ⟨l₁, _ | ⟨l₂, rest⟩⟩
    · right; rw [splitChain_none_short z [] j (by simp)] at hall; simp at hall
    · right; rw [splitChain_none_short z [l₁] j (by simp)] at hall
      simp only [List.all_cons, List.all_nil, Bool.and_true] at hall
      rw [clauseSat_iff] at hall; obtain ⟨l, hl, hlsat⟩ := hall; exact ⟨l, hl, hlsat⟩
    · by_cases hlen : (l₁ :: l₂ :: rest).length ≤ 3
      · right; rw [splitChain_none_short z _ j hlen] at hall
        simp only [List.all_cons, List.all_nil, Bool.and_true] at hall
        rw [clauseSat_iff] at hall; obtain ⟨l, hl, hlsat⟩ := hall; exact ⟨l, hl, hlsat⟩
      · rw [splitChain_none_long z l₁ l₂ rest j hlen] at hall
        simp only [List.all_cons, Bool.and_eq_true] at hall
        obtain ⟨h1, h2⟩ := hall
        rw [clauseSat_iff] at h1
        obtain ⟨l, hl, hlsat⟩ := h1
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with heq | heq | heq <;> rw [heq] at hlsat
        · right; exact ⟨l₁, by simp, hlsat⟩
        · right; exact ⟨l₂, by simp, hlsat⟩
        · -- l = (z 0, true); recurse on carry (z 0, false)
          have hrec := ih rest.length (by simp [List.length_cons])
            (some (z 0, false)) rest 1 h2 rfl
          rcases hrec with ⟨c, hc, hcsat⟩ | ⟨l', hlm, hl'sat⟩
          · simp only [Option.some.injEq] at hc; subst hc
            simp only [litSat] at hcsat hlsat
            rw [beq_iff_eq] at hcsat hlsat; rw [hcsat] at hlsat; exact absurd hlsat (by decide)
          · right; exact ⟨l', by simp [hlm], hl'sat⟩
  | some c =>
    rcases lits with _ | ⟨l₁, rest⟩
    · left; rw [splitChain_some_short z c [] j (by simp)] at hall
      simp only [List.all_cons, List.all_nil, Bool.and_true] at hall
      rw [clauseSat_iff] at hall; obtain ⟨l, hl, hlsat⟩ := hall
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl; rw [hl] at hlsat
      exact ⟨c, rfl, hlsat⟩
    · by_cases hlen : (l₁ :: rest).length ≤ 2
      · rw [splitChain_some_short z c _ j hlen] at hall
        simp only [List.all_cons, List.all_nil, Bool.and_true] at hall
        rw [clauseSat_iff] at hall; obtain ⟨l, hl, hlsat⟩ := hall
        simp only [List.mem_cons] at hl
        rcases hl with heq | hl
        · left; rw [heq] at hlsat; exact ⟨c, rfl, hlsat⟩
        · right; exact ⟨l, by simp [hl], hlsat⟩
      · rw [splitChain_some_long z c l₁ rest j hlen] at hall
        simp only [List.all_cons, Bool.and_eq_true] at hall
        obtain ⟨h1, h2⟩ := hall
        rw [clauseSat_iff] at h1
        obtain ⟨l, hl, hlsat⟩ := h1
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with heq | heq | heq <;> rw [heq] at hlsat
        · left; exact ⟨c, rfl, hlsat⟩
        · right; exact ⟨l₁, by simp, hlsat⟩
        · have hrec := ih rest.length (by simp [List.length_cons])
            (some (z j, false)) rest (j + 1) h2 rfl
          rcases hrec with ⟨c', hc', hc'sat⟩ | ⟨l', hlm, hl'sat⟩
          · simp only [Option.some.injEq] at hc'; subst hc'
            simp only [litSat] at hc'sat hlsat
            rw [beq_iff_eq] at hc'sat hlsat; rw [hc'sat] at hlsat; exact absurd hlsat (by decide)
          · right; exact ⟨l', by simp [hlm], hl'sat⟩

/-! ## Forward direction: a satisfying assignment extends through the chain

If `assign` already satisfies the carry literal (the chain "entry" is open) then setting *all*
fresh `z`-variables in the rest of the chain to `false` keeps every clause satisfied: each
later clause leads with `¬z_prev`, which the previous step turned true. The general forward
direction first walks to the satisfied body literal making leading `z`'s true, then applies
this "tail" lemma. We bake the `z`-rule into `assign` via the hypotheses `hcarry`/`hztail`. -/

/-- **Forward tail.** If the carry literal is satisfied and every fresh variable used from
step `j` onward is set `false`, all chain clauses hold (each later clause's leading `¬z` is
true). -/
theorem splitChain_forward_tail {total : ℕ} (z : ℕ → Fin total) (assign : Fin total → Bool)
    (N : ℕ) (c : Literal total) (lits : List (Literal total)) (j : ℕ)
    (hcarry : litSat assign c = true)
    (hbound : j + lits.length ≤ N + 2)
    (hztail : ∀ i, j ≤ i → i < N → assign (z i) = false) :
    (splitChain z (some c) lits j).all (clauseSat assign) = true := by
  induction hn : lits.length using Nat.strong_induction_on generalizing c lits j with
  | _ n ih =>
  subst hn
  rcases lits with _ | ⟨l₁, rest⟩
  · rw [splitChain_some_short z c [] j (by simp)]
    simp only [List.all_cons, List.all_nil, Bool.and_true]
    rw [clauseSat_iff]; exact ⟨c, by simp, hcarry⟩
  · by_cases hlen : (l₁ :: rest).length ≤ 2
    · rw [splitChain_some_short z c _ j hlen]
      simp only [List.all_cons, List.all_nil, Bool.and_true]
      rw [clauseSat_iff]; exact ⟨c, by simp, hcarry⟩
    · rw [splitChain_some_long z c l₁ rest j hlen]
      simp only [List.length_cons] at hlen hbound
      simp only [List.all_cons, Bool.and_eq_true]
      refine ⟨?_, ?_⟩
      · -- first clause [c, l₁, (z j, true)] is satisfied by c
        rw [clauseSat_iff]; exact ⟨c, by simp, hcarry⟩
      · -- recurse: new carry is (z j, false), satisfied because assign (z j) = false
        apply ih rest.length (by simp [List.length_cons]) (z j, false) rest (j + 1)
        · simp only [litSat]; rw [hztail j (le_refl j) (by omega)]; rfl
        · omega
        · intro i hi hib; exact hztail i (by omega) hib
        · rfl

/-- **Forward walk (with carry).** The walk consumes the first `d` literals of `lits` as skip
steps `j, …, j+d-1`, each carried by its third fresh literal `(z i, true)` because
`assign (z i) = true` there (`hlead`); these literals are all unsatisfied (`hskip`), so the
clause genuinely needs the fresh carrier. At step `j + d` a literal in the remaining body
`lits.drop d` is satisfied (`hsat`) — that clause is satisfied directly and
`splitChain_forward_tail` finishes the rest with all later fresh vars `false` (`htail`). -/
theorem splitChain_forward_some {total : ℕ} (z : ℕ → Fin total) (assign : Fin total → Bool)
    (N : ℕ) :
    ∀ (d : ℕ) (c : Literal total) (lits : List (Literal total)) (j : ℕ),
      j + lits.length ≤ N + 2 →
      (∀ i, j ≤ i → i < j + d → i < N → assign (z i) = true) →
      (∀ i, j + d ≤ i → i < N → assign (z i) = false) →
      -- pivot: a literal of the clause peeled at step `j + d` is satisfied. That clause's body
      -- is `[lits[d]]` if still long, or the whole short remainder `lits.drop d`.
      ((∃ l, lits.drop d = l :: lits.drop (d + 1) ∧ litSat assign l = true) ∨
        ((lits.drop d).length ≤ 2 ∧ ∃ l ∈ lits.drop d, litSat assign l = true)) →
      (splitChain z (some c) lits j).all (clauseSat assign) = true := by
  intro d
  induction d with
  | zero =>
    intro c lits j hbound _ htail hsat
    simp only [Nat.add_zero, List.drop_zero, Nat.zero_add] at htail hsat
    rcases lits with _ | ⟨l₁, rest⟩
    · rcases hsat with ⟨l, hl, _⟩ | ⟨_, l, hl, _⟩ <;> simp [List.drop_nil] at hl
    · by_cases hlen : (l₁ :: rest).length ≤ 2
      · rw [splitChain_some_short z c _ j hlen]
        simp only [List.all_cons, List.all_nil, Bool.and_true, clauseSat_iff]
        rcases hsat with ⟨l, hd, hlsat⟩ | ⟨_, l, hl, hlsat⟩
        · refine ⟨l, ?_, hlsat⟩; rw [hd]; simp
        · exact ⟨l, by simp [hl], hlsat⟩
      · rw [splitChain_some_long z c l₁ rest j hlen]
        simp only [List.length_cons] at hlen hbound
        simp only [List.all_cons, Bool.and_eq_true]
        -- short branch impossible here (clause long); satisfier is the head l₁
        rcases hsat with ⟨l, hd, hlsat⟩ | ⟨hshort, _⟩
        · simp only [List.cons.injEq] at hd
          obtain ⟨rfl, _⟩ := hd
          refine ⟨by rw [clauseSat_iff]; exact ⟨l₁, by simp, hlsat⟩, ?_⟩
          apply splitChain_forward_tail z assign N (z j, false) rest (j + 1)
          · simp only [litSat]; rw [htail j (le_refl j) (by omega)]; rfl
          · omega
          · intro i _ hib; exact htail i (by omega) hib
        · exact absurd hshort (by simpa using hlen)
  | succ d ih =>
    intro c lits j hbound hlead htail hsat
    rcases lits with _ | ⟨l₁, rest⟩
    · rcases hsat with ⟨l, hd, _⟩ | ⟨_, l, hl, _⟩
      · simp [List.drop_nil] at hd
      · simp [List.drop_nil] at hl
    · by_cases hlen : (l₁ :: rest).length ≤ 2
      · rw [splitChain_some_short z c _ j hlen]
        simp only [List.all_cons, List.all_nil, Bool.and_true, clauseSat_iff]
        -- short clause, but d+1 skips planned ⇒ satisfier in drop (d+1) ⊆ short body
        rcases hsat with ⟨l, hd, hlsat⟩ | ⟨_, l, hl, hlsat⟩
        · refine ⟨l, ?_, hlsat⟩
          have hmem : l ∈ (l₁ :: rest).drop (d + 1) := by rw [hd]; simp
          exact List.mem_cons_of_mem c (List.mem_of_mem_drop hmem)
        · exact ⟨l, List.mem_cons_of_mem c (List.mem_of_mem_drop hl), hlsat⟩
      · rw [splitChain_some_long z c l₁ rest j hlen]
        simp only [List.length_cons] at hlen hbound
        simp only [List.all_cons, Bool.and_eq_true]
        refine ⟨?_, ?_⟩
        · rw [clauseSat_iff]; exact ⟨(z j, true), by simp, by
            simp only [litSat]; rw [hlead j (le_refl j) (by omega) (by omega)]; rfl⟩
        · apply ih (z j, false) rest (j + 1) (by omega)
          · intro i hi hii hiN; exact hlead i (by omega) (by omega) hiN
          · intro i hi hib; exact htail i (by omega) hib
          · rcases hsat with ⟨l, hd, hlsat⟩ | ⟨hshort, l, hl, hlsat⟩
            · left; refine ⟨l, ?_, hlsat⟩
              simpa [List.drop_succ_cons] using hd
            · right; refine ⟨?_, l, ?_, hlsat⟩
              · simpa [List.drop_succ_cons] using hshort
              · simpa [List.drop_succ_cons] using hl

/-- Updating `assign` at a fresh variable `w` (disjoint from the body literals' variables of
`lits` and from `c`) leaves a clause-list's satisfaction unchanged, when the update value
keeps every clause's deciding literal intact. Concretely: setting `w := true` only *helps*
positive occurrences and *hurts* negative ones; we use the precise transport below. -/
theorem clauseSat_update_of_ne {total : ℕ} [DecidableEq (Fin total)]
    (assign : Fin total → Bool) (w : Fin total) (b : Bool) (cl : Clause total)
    (hne : ∀ l ∈ cl, l.1 ≠ w) :
    clauseSat (Function.update assign w b) cl = clauseSat assign cl := by
  rw [Bool.eq_iff_iff, clauseSat_iff, clauseSat_iff]
  constructor
  · rintro ⟨l, hl, hlsat⟩
    exact ⟨l, hl, by rwa [litSat, Function.update_of_ne (hne l hl)] at hlsat⟩
  · rintro ⟨l, hl, hlsat⟩
    exact ⟨l, hl, by rwa [litSat, Function.update_of_ne (hne l hl)]⟩

/-- Updating `assign` at a fresh variable `w` leaves the satisfaction of every clause in a
list unchanged, provided `w` is not the variable of any literal appearing in any clause. -/
theorem all_clauseSat_update_of_ne {total : ℕ} [DecidableEq (Fin total)]
    (assign : Fin total → Bool) (w : Fin total) (b : Bool) (cls : List (Clause total))
    (hne : ∀ cl ∈ cls, ∀ l ∈ cl, l.1 ≠ w) :
    cls.all (clauseSat (Function.update assign w b)) = cls.all (clauseSat assign) := by
  induction cls with
  | nil => rfl
  | cons cl rest ih =>
    rw [all_clauseSat_cons, all_clauseSat_cons]
    rw [clauseSat_update_of_ne assign w b cl (fun l hl => hne cl (by simp) l hl)]
    rw [ih (fun c hc => hne c (by simp [hc]))]

/-- **Forward, no carry (chain entry).** The full forward direction for one clause's chain
(carry `none`), with pivot peel-step `d`: fresh vars at steps `< d` are `true`, at steps `≥ d`
are `false`. The first clause peels *two* literals (`l₁, l₂`), each later clause one; so at
pivot `d = 0` the satisfier is among `lits.take 2`, and at pivot `d ≥ 1` it is the literal at
`lits.drop (d + 1)` (or in the short final clause). Dispatches the first clause then hands off
to `splitChain_forward_some`. -/
theorem splitChain_forward_none {total : ℕ} (z : ℕ → Fin total) (assign : Fin total → Bool)
    (N d : ℕ) (lits : List (Literal total))
    (hbound : lits.length ≤ N + 3)
    (hlead : ∀ i, i < d → i < N → assign (z i) = true)
    (htail : ∀ i, d ≤ i → i < N → assign (z i) = false)
    (hsat :
      -- pivot at first clause (d = 0): a literal of `lits.take 2` is satisfied; otherwise the
      -- satisfier is the literal at peel-step `d ≥ 1`, i.e. head of `lits.drop (d + 1)`, or in
      -- the final short clause (`_some` short form, `lits.drop (d + 1)` of length ≤ 2).
      ((∃ l, lits.drop (d + 1) = l :: lits.drop (d + 2) ∧ litSat assign l = true) ∨
        ((lits.drop (d + 1)).length ≤ 2 ∧ 1 ≤ d ∧
          ∃ l ∈ lits.drop (d + 1), litSat assign l = true) ∨
        (d = 0 ∧ (∃ l ∈ lits.take 2, litSat assign l = true)))) :
    (splitChain z none lits 0).all (clauseSat assign) = true := by
  rcases lits with _ | ⟨l₁, _ | ⟨l₂, rest⟩⟩
  · rcases hsat with ⟨l, hd, _⟩ | ⟨_, _, l, hl, _⟩ | ⟨_, l, hl, _⟩
    · simp [List.drop_nil] at hd
    · simp [List.drop_nil] at hl
    · simp at hl
  · rw [splitChain_none_short z [l₁] 0 (by simp)]
    simp only [List.all_cons, List.all_nil, Bool.and_true, clauseSat_iff]
    rcases hsat with ⟨l, hd, hlsat⟩ | ⟨_, _, l, hl, hlsat⟩ | ⟨_, l, hl, hlsat⟩
    · exact absurd hd (by simp [List.drop_nil])
    · exact ⟨l, List.mem_of_mem_drop hl, hlsat⟩
    · refine ⟨l, ?_, hlsat⟩; have := List.mem_of_mem_take hl; simpa using this
  · by_cases hlen : (l₁ :: l₂ :: rest).length ≤ 3
    · rw [splitChain_none_short z _ 0 hlen]
      simp only [List.all_cons, List.all_nil, Bool.and_true, clauseSat_iff]
      rcases hsat with ⟨l, hd, hlsat⟩ | ⟨_, _, l, hl, hlsat⟩ | ⟨_, l, hl, hlsat⟩
      · refine ⟨l, ?_, hlsat⟩
        have hmem : l ∈ (l₁ :: l₂ :: rest).drop (d + 1) := by rw [hd]; simp
        exact List.mem_of_mem_drop hmem
      · exact ⟨l, List.mem_of_mem_drop hl, hlsat⟩
      · exact ⟨l, List.mem_of_mem_take hl, hlsat⟩
    · rw [splitChain_none_long z l₁ l₂ rest 0 hlen]
      simp only [List.all_cons, Bool.and_eq_true]
      cases d with
      | zero =>
        -- pivot at first clause: l₁ or l₂ satisfied; tail handles rest
        refine ⟨?_, ?_⟩
        · rw [clauseSat_iff]
          rcases hsat with ⟨l, hd, hlsat⟩ | ⟨_, hd1, _⟩ | ⟨_, l, hl, hlsat⟩
          · -- drop 1 = l :: drop 2 means l = l₂
            simp only [List.drop_succ_cons, List.drop_zero] at hd
            rcases rest with _ | ⟨r₀, rest'⟩
            · exact absurd hlen (by simp)
            · simp only [List.cons.injEq] at hd; obtain ⟨rfl, _⟩ := hd
              exact ⟨l₂, by simp, hlsat⟩
          · exact absurd hd1 (by omega)
          · -- l ∈ take 2 = [l₁, l₂]
            simp only [List.take_succ_cons, List.take_zero, List.mem_cons,
              List.not_mem_nil, or_false] at hl
            rcases hl with rfl | rfl
            · exact ⟨l, by simp, hlsat⟩
            · exact ⟨l, by simp, hlsat⟩
        · apply splitChain_forward_tail z assign N (z 0, false) rest 1
          · simp only [litSat]; rw [htail 0 (le_refl 0) (by
              simp only [List.length_cons] at hlen hbound; omega)]; rfl
          · simp only [List.length_cons] at hbound; omega
          · intro i _ hib; exact htail i (by omega) hib
      | succ d =>
        -- skip first clause (z 0 = true), recurse into the some-walk with d skips
        refine ⟨?_, ?_⟩
        · rw [clauseSat_iff]; exact ⟨(z 0, true), by simp, by
            simp only [litSat]
            rw [hlead 0 (by omega) (by
              simp only [List.length_cons] at hlen hbound; omega)]; rfl⟩
        · apply splitChain_forward_some z assign N d (z 0, false) rest 1
            (by simp only [List.length_cons] at hbound ⊢; omega)
          · intro i hi hii hiN; exact hlead i (by omega) hiN
          · intro i hi hib; exact htail i (by omega) hib
          · rcases hsat with ⟨l, hd, hlsat⟩ | ⟨hshort, _, l, hl, hlsat⟩ | ⟨hd0, _⟩
            · left; refine ⟨l, ?_, hlsat⟩
              simpa only [List.drop_succ_cons] using hd
            · right; refine ⟨?_, l, ?_, hlsat⟩
              · simp only [List.drop_succ_cons, List.length_drop] at hshort ⊢; omega
              · simpa only [List.drop_succ_cons] using hl
            · exact absurd hd0 (by omega)

/-! ## 3-CNF guarantee for the chain

Every clause emitted by `splitChain` has at most three literals. -/

/-- Every clause produced by `splitChain` has length `≤ 3` (the chain is in 3-CNF). -/
theorem splitChain_length_le {total : ℕ} (z : ℕ → Fin total) :
    ∀ (carry : Option (Literal total)) (lits : List (Literal total)) (j : ℕ),
      ∀ cl ∈ splitChain z carry lits j, cl.length ≤ 3 := by
  intro carry lits j
  induction hn : lits.length using Nat.strong_induction_on generalizing carry lits j with
  | _ n ih =>
  subst hn
  cases carry with
  | none =>
    rcases lits with _ | ⟨l₁, _ | ⟨l₂, rest⟩⟩
    · intro cl hcl; rw [splitChain_none_short z [] j (by simp)] at hcl; simp at hcl; subst hcl; simp
    · intro cl hcl; rw [splitChain_none_short z [l₁] j (by simp)] at hcl
      simp only [List.mem_singleton] at hcl; subst hcl; simp
    · by_cases hlen : (l₁ :: l₂ :: rest).length ≤ 3
      · intro cl hcl; rw [splitChain_none_short z _ j hlen] at hcl
        simp only [List.mem_singleton] at hcl; subst hcl; exact hlen
      · intro cl hcl; rw [splitChain_none_long z l₁ l₂ rest j hlen] at hcl
        simp only [List.mem_cons] at hcl
        rcases hcl with rfl | hcl
        · simp
        · exact ih rest.length (by simp [List.length_cons]) (some (z 0, false)) rest 1 rfl cl hcl
  | some c =>
    rcases lits with _ | ⟨l₁, rest⟩
    · intro cl hcl; rw [splitChain_some_short z c [] j (by simp)] at hcl
      simp only [List.mem_singleton] at hcl; subst hcl; simp
    · by_cases hlen : (l₁ :: rest).length ≤ 2
      · intro cl hcl; rw [splitChain_some_short z c _ j hlen] at hcl
        simp only [List.mem_singleton] at hcl; subst hcl
        simp only [List.length_cons] at hlen ⊢; omega
      · intro cl hcl; rw [splitChain_some_long z c l₁ rest j hlen] at hcl
        simp only [List.mem_cons] at hcl
        rcases hcl with rfl | hcl
        · simp
        · exact ih rest.length (by simp [List.length_cons]) (some (z j, false)) rest (j + 1) rfl cl hcl

/-! ## Formula-level clause splitting

`globalZ φ` indexes the shared aux block `[φ.numVars, φ.numVars + auxCount φ)`; each clause at
cumulative base `b` uses the contiguous sub-block `b, b + 1, …`. `splitClauses` threads `b`. -/

/-- Split a list of original clauses into 3-CNF clauses over the enlarged space, placing each
clause's fresh aux block at the running cumulative base `base`. The aux-variable index map
`z : ℕ → Fin total` (with `total = threeSatNumVars φ`) is supplied externally so its codomain
is known nonempty wherever this is invoked. -/
def splitClauses (φ : CnfFormula) (h : φ.numVars ≤ threeSatNumVars φ)
    (z : ℕ → Fin (threeSatNumVars φ)) :
    ℕ → List (Clause φ.numVars) → List (Clause (threeSatNumVars φ))
  | _, [] => []
  | base, c :: cs =>
    splitChain (fun i => z (base + i)) none (c.map (castLiteral h)) 0 ++
      splitClauses φ h z (base + clauseAux c) cs

/-- The aux-variable index map used by the reduction, when there is at least one output
variable: aux-index `i` ↦ `φ.numVars + i` (in range when `i < auxCount φ`; clamped otherwise,
which never occurs in correctness uses). -/
def auxZ (φ : CnfFormula) (hpos : 0 < threeSatNumVars φ) (i : ℕ) : Fin (threeSatNumVars φ) :=
  if h : φ.numVars + i < threeSatNumVars φ then ⟨φ.numVars + i, h⟩ else ⟨0, hpos⟩

/-- The **clause-splitting reduction map**: `φ ↦` the 3-CNF formula obtained by splitting each
clause of `φ` into `≤ 3`-literal clauses with fresh chaining variables. (When the output has
no variables — `φ` has no variables, hence only empty clauses — the splitting is trivial and
each clause stays empty; we feed it an arbitrary index map, never evaluated.) -/
def satToThreeSatMap (φ : CnfFormula) : CnfFormula :=
  if hpos : 0 < threeSatNumVars φ then
    ⟨threeSatNumVars φ,
      splitClauses φ (by unfold threeSatNumVars; omega) (auxZ φ hpos) 0 φ.clauses⟩
  else
    -- `threeSatNumVars φ = 0` ⇒ `φ.numVars = 0`, so every clause is empty; output `φ` as-is
    φ

/-- Every clause of `splitClauses` has length `≤ 3`. -/
theorem splitClauses_length_le (φ : CnfFormula) (h : φ.numVars ≤ threeSatNumVars φ)
    (z : ℕ → Fin (threeSatNumVars φ)) (base : ℕ) (cs : List (Clause φ.numVars)) :
    ∀ cl ∈ splitClauses φ h z base cs, cl.length ≤ 3 := by
  induction cs generalizing base with
  | nil => intro cl hcl; simp [splitClauses] at hcl
  | cons c cs ih =>
    intro cl hcl
    rw [splitClauses] at hcl
    rw [List.mem_append] at hcl
    rcases hcl with hcl | hcl
    · exact splitChain_length_le _ none _ 0 cl hcl
    · exact ih (base + clauseAux c) cl hcl

/-- When `φ` has no variables, every clause is empty (length `0`). -/
theorem clause_eq_nil_of_numVars_zero (φ : CnfFormula) (h0 : φ.numVars = 0)
    (cl : Clause φ.numVars) (hcl : cl ∈ φ.clauses) : cl = [] := by
  rcases cl with _ | ⟨l, _⟩
  · rfl
  · have := l.1.isLt; omega

/-- **3-CNF guarantee.** The output of `satToThreeSatMap` is always in 3-CNF. -/
theorem is3Cnf_satToThreeSatMap (φ : CnfFormula) : Is3Cnf (satToThreeSatMap φ) := by
  unfold satToThreeSatMap
  split
  · intro cl hcl
    exact splitClauses_length_le φ _ _ 0 φ.clauses cl hcl
  · -- φ has no output variables ⇒ numVars = 0 ⇒ all clauses empty
    rename_i hpos
    have h0 : φ.numVars = 0 := by unfold threeSatNumVars at hpos; omega
    intro cl hcl
    rw [clause_eq_nil_of_numVars_zero φ h0 cl hcl]; simp

/-! ## Backward direction (restriction): split satisfiable ⇒ original satisfiable

If `assign` satisfies all the split clauses, its restriction to the original variables
satisfies the original formula: each original clause's chain forces an original literal true
(`splitChain_forces`). -/

/-- If every clause of `splitClauses … base cs` is satisfied by `assign`, then every original
clause in `cs` is satisfied by the restricted assignment `assign ∘ castLE`. -/
theorem clauseSat_restrict_of_splitClauses (φ : CnfFormula) (h : φ.numVars ≤ threeSatNumVars φ)
    (z : ℕ → Fin (threeSatNumVars φ)) (assign : Fin (threeSatNumVars φ) → Bool) :
    ∀ (base : ℕ) (cs : List (Clause φ.numVars)),
      (splitClauses φ h z base cs).all (clauseSat assign) = true →
      ∀ c ∈ cs, clauseSat (fun i => assign (Fin.castLE h i)) c = true := by
  intro base cs
  induction cs generalizing base with
  | nil => intro _ c hc; simp at hc
  | cons c cs ih =>
    intro hall c' hc'
    rw [splitClauses, List.all_append, Bool.and_eq_true] at hall
    obtain ⟨hchain, hrest⟩ := hall
    simp only [List.mem_cons] at hc'
    rcases hc' with rfl | hc'
    · -- c' = c: its chain is satisfied; forces an original literal
      have hforce := splitChain_forces (fun i => z (base + i)) assign none
        (c'.map (castLiteral h)) 0 hchain
      rcases hforce with ⟨cc, hcc, _⟩ | ⟨l, hl, hlsat⟩
      · simp at hcc
      · -- l = castLiteral h l₀ for some l₀ ∈ c'
        rw [List.mem_map] at hl
        obtain ⟨l₀, hl₀mem, rfl⟩ := hl
        rw [clauseSat_iff]
        exact ⟨l₀, hl₀mem, by rwa [litSat_castLiteral] at hlsat⟩
    · exact ih (base + clauseAux c) hrest c' hc'

/-- **Backward direction.** A satisfying assignment of the split formula restricts to a
satisfying assignment of the original. -/
theorem satisfiable_of_satToThreeSatMap (φ : CnfFormula)
    (hsat : Satisfiable (satToThreeSatMap φ)) : Satisfiable φ := by
  unfold satToThreeSatMap at hsat
  split at hsat
  · obtain ⟨assign, heval⟩ := hsat
    rename_i hpos
    have hle : φ.numVars ≤ threeSatNumVars φ := by unfold threeSatNumVars; omega
    refine ⟨fun i => assign (Fin.castLE hle i), ?_⟩
    rw [CnfFormula.eval, List.all_eq_true]
    intro c hc
    rw [CnfFormula.eval, List.all_eq_true] at heval
    exact clauseSat_restrict_of_splitClauses φ hle (auxZ φ hpos) assign 0 φ.clauses
      (List.all_eq_true.2 heval) c hc
  · exact hsat

/-! ## Forward direction (extension): original satisfiable ⇒ split satisfiable

From a satisfying assignment `assignOrig` of `φ` we build a satisfying assignment of the split
by the carry rule per clause. The pivot peel-step of a clause `c` is `firstSatIdx c - 1`, where
`firstSatIdx c` is the position of the first satisfied literal; the clause's fresh aux block is
set `true` before the pivot and `false` from it on. `auxValList` computes the aux value at a
global aux index by walking the clauses with cumulative bases. -/

/-- Position of the first satisfied literal of clause `c` under `assignOrig`. -/
def firstSatIdx {n : ℕ} (assignOrig : Fin n → Bool) (c : Clause n) : ℕ :=
  c.findIdx (litSat assignOrig)

/-- Pivot peel-step of clause `c`: `firstSatIdx c - 1` (the first clause peels two literals, so
a satisfier at position `p` is reached at step `p - 1`, or step `0` for `p ≤ 1`). -/
def pivotStep {n : ℕ} (assignOrig : Fin n → Bool) (c : Clause n) : ℕ :=
  firstSatIdx assignOrig c - 1

/-- The aux-bit at aux offset `q` (relative to the current clause list's start), computed by
walking the clause list: in the block of the clause containing `q`, the bit is `true` iff the
local offset is strictly below that clause's pivot step. Past all blocks ⇒ `false`. -/
def auxValList {n : ℕ} (assignOrig : Fin n → Bool) :
    List (Clause n) → ℕ → Bool
  | [], _ => false
  | c :: cs, q =>
    if q < clauseAux c then decide (q < pivotStep assignOrig c)
    else auxValList assignOrig cs (q - clauseAux c)

/-- The full extended assignment: original variables keep `assignOrig`, aux variables get the
carry-rule bit from `auxValList`. -/
def extendAssign (φ : CnfFormula) (assignOrig : Fin φ.numVars → Bool) :
    Fin (threeSatNumVars φ) → Bool :=
  fun v =>
    if hv : v.val < φ.numVars then assignOrig ⟨v.val, hv⟩
    else auxValList assignOrig φ.clauses (v.val - φ.numVars)

/-- `extendAssign` on an original variable (cast up) is just `assignOrig`. -/
theorem extendAssign_castLE {φ : CnfFormula} (assignOrig : Fin φ.numVars → Bool)
    (hle : φ.numVars ≤ threeSatNumVars φ) (i : Fin φ.numVars) :
    extendAssign φ assignOrig (Fin.castLE hle i) = assignOrig i := by
  simp only [extendAssign, Fin.castLE, i.isLt, dif_pos]

/-- `litSat` through `castLiteral` under `extendAssign` reads off `assignOrig`. -/
theorem litSat_castLiteral_extend {φ : CnfFormula} (assignOrig : Fin φ.numVars → Bool)
    (hle : φ.numVars ≤ threeSatNumVars φ) (l : Literal φ.numVars) :
    litSat (extendAssign φ assignOrig) (castLiteral hle l) = litSat assignOrig l := by
  rw [litSat_castLiteral]
  congr 1; ext i; exact extendAssign_castLE assignOrig hle i

/-- A query past the cumulative aux of a prefix `pre` only depends on the suffix `cs`: walking
`auxValList` over `pre ++ cs` at offset `q ≥ (pre aux sum)` equals walking `cs` at the shifted
offset `q - (pre aux sum)`. -/
theorem auxValList_suffix {n : ℕ} (assignOrig : Fin n → Bool) (cs : List (Clause n)) :
    ∀ (pre : List (Clause n)) (q : ℕ),
      (pre.map clauseAux).sum ≤ q →
      auxValList assignOrig (pre ++ cs) q =
        auxValList assignOrig cs (q - (pre.map clauseAux).sum) := by
  intro pre
  induction pre with
  | nil => intro q _; simp
  | cons c pre ih =>
    intro q hq
    simp only [List.map_cons, List.sum_cons] at hq ⊢
    rw [List.cons_append, auxValList, if_neg (by omega)]
    rw [ih (q - clauseAux c) (by omega)]
    congr 1; omega

/-- `auxZ` at an in-range aux index `q < auxCount φ` is the output variable `φ.numVars + q`. -/
theorem auxZ_val {φ : CnfFormula} (hpos : 0 < threeSatNumVars φ) (q : ℕ) (hq : q < auxCount φ) :
    (auxZ φ hpos q).val = φ.numVars + q := by
  simp only [auxZ]
  rw [dif_pos (by unfold threeSatNumVars; omega)]

/-- `extendAssign` on an in-range aux index reads off `auxValList`. -/
theorem extendAssign_auxZ {φ : CnfFormula} (hpos : 0 < threeSatNumVars φ)
    (assignOrig : Fin φ.numVars → Bool) (q : ℕ) (hq : q < auxCount φ) :
    extendAssign φ assignOrig (auxZ φ hpos q) = auxValList assignOrig φ.clauses q := by
  simp only [extendAssign]
  rw [dif_neg (by rw [auxZ_val hpos q hq]; omega)]
  rw [auxZ_val hpos q hq]; congr 1; omega

/-- The aux value for clause `c` (at cumulative base `b`, `φ.clauses = pre ++ c :: cs`,
`b = pre`'s aux sum) at local offset `i < clauseAux c` follows the carry rule
`decide (i < pivotStep c)`. -/
theorem extendAssign_block {φ : CnfFormula} (hpos : 0 < threeSatNumVars φ)
    (assignOrig : Fin φ.numVars → Bool) (pre : List (Clause φ.numVars)) (c : Clause φ.numVars)
    (cs : List (Clause φ.numVars)) (hsplit : φ.clauses = pre ++ c :: cs)
    (i : ℕ) (hi : i < clauseAux c) :
    extendAssign φ assignOrig (auxZ φ hpos ((pre.map clauseAux).sum + i)) =
      decide (i < pivotStep assignOrig c) := by
  have hb : (pre.map clauseAux).sum + i < auxCount φ := by
    rw [auxCount, hsplit, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
    omega
  rw [extendAssign_auxZ hpos assignOrig _ hb, hsplit]
  rw [auxValList_suffix assignOrig (c :: cs) pre _ (by omega)]
  rw [show (pre.map clauseAux).sum + i - (pre.map clauseAux).sum = i by omega]
  rw [auxValList, if_pos hi]

/-- `firstSatIdx`/`pivotStep` on a cast clause `c.map castLiteral` under `extendAssign` agree
with those on `c` under `assignOrig`. -/
theorem firstSatIdx_castMap {φ : CnfFormula} (assignOrig : Fin φ.numVars → Bool)
    (hle : φ.numVars ≤ threeSatNumVars φ) (c : Clause φ.numVars) :
    firstSatIdx (extendAssign φ assignOrig) (c.map (castLiteral hle)) =
      firstSatIdx assignOrig c := by
  simp only [firstSatIdx, List.findIdx_map]
  congr 1; ext l; exact litSat_castLiteral_extend assignOrig hle l

/-- **Per-clause forward.** A clause `c` (at cumulative base `pre`-sum, with `φ.clauses =
pre ++ c :: cs`) satisfied by `assignOrig` has its split chain satisfied by `extendAssign`. -/
theorem splitChain_forward_clause {φ : CnfFormula} (hpos : 0 < threeSatNumVars φ)
    (assignOrig : Fin φ.numVars → Bool) (hle : φ.numVars ≤ threeSatNumVars φ)
    (pre : List (Clause φ.numVars)) (c : Clause φ.numVars) (cs : List (Clause φ.numVars))
    (hsplit : φ.clauses = pre ++ c :: cs)
    (hcsat : clauseSat assignOrig c = true) :
    (splitChain (fun i => auxZ φ hpos ((pre.map clauseAux).sum + i)) none
      (c.map (castLiteral hle)) 0).all (clauseSat (extendAssign φ assignOrig)) = true := by
  set assign := extendAssign φ assignOrig with hassign
  set z : ℕ → Fin (threeSatNumVars φ) := fun i => auxZ φ hpos ((pre.map clauseAux).sum + i)
    with hz
  set lits := c.map (castLiteral hle) with hlits
  -- first satisfied literal of c (p = firstSatIdx, defeq to findIdx)
  have hfi : (c.findIdx (litSat assignOrig)) < c.length := by
    rw [List.findIdx_lt_length]; rwa [clauseSat_iff] at hcsat
  have hfip : firstSatIdx assignOrig c < c.length := hfi
  have hflits : firstSatIdx assignOrig c < lits.length := by
    simp only [hlits, List.length_map]; exact hfip
  -- the satisfier literal in the cast list
  have hssat : litSat assign (lits[firstSatIdx assignOrig c]) = true := by
    have hcp : litSat assignOrig (c[firstSatIdx assignOrig c]) = true :=
      List.findIdx_getElem (p := litSat assignOrig) (xs := c) (w := hfi)
    have heq : lits[firstSatIdx assignOrig c] =
        castLiteral hle (c[firstSatIdx assignOrig c]) := by
      simp only [hlits]; rw [List.getElem_map]
    rw [heq, litSat_castLiteral_extend]; exact hcp
  set p := firstSatIdx assignOrig c with hp
  set s := lits[p] with hs
  -- head decomposition of the drop at p
  have hdrop : lits.drop p = s :: lits.drop (p + 1) := List.drop_eq_getElem_cons hflits
  -- carry-rule value of z
  have hzval : ∀ i, i < clauseAux c → assign (z i) = decide (i < pivotStep assignOrig c) := by
    intro i hi; exact extendAssign_block hpos assignOrig pre c cs hsplit i hi
  apply splitChain_forward_none z assign (clauseAux c) (pivotStep assignOrig c) lits
  · -- hbound: lits.length ≤ clauseAux c + 3
    simp only [hlits, List.length_map, clauseAux]; omega
  · -- hlead
    intro i hi hiN
    rw [hzval i hiN]; simp only [decide_eq_true_eq]; exact hi
  · -- htail
    intro i hi hib
    rw [hzval i hib]; simp only [decide_eq_false_iff_not, not_lt]; exact hi
  · -- hsat: the pivot
    by_cases hp01 : p ≤ 1
    · -- d = pivotStep = p - 1 = 0
      have hd0 : pivotStep assignOrig c = 0 := by simp only [pivotStep]; omega
      right; right
      refine ⟨hd0, s, ?_, hssat⟩
      apply List.mem_take_iff_getElem.2
      exact ⟨p, by simp only [hlits, List.length_map]; omega, by rw [hs]⟩
    · -- p ≥ 2, d = p - 1 ≥ 1, satisfier is head of lits.drop (d+1) = lits.drop p
      simp only [not_le] at hp01
      have hdp : pivotStep assignOrig c + 1 = p := by simp only [pivotStep]; omega
      left
      refine ⟨s, ?_, hssat⟩
      rw [hdp, show pivotStep assignOrig c + 2 = p + 1 by omega, hdrop]

/-- **Forward over a clause list.** If every clause in the suffix `cs` (with `φ.clauses =
pre ++ cs`) is satisfied by `assignOrig`, then `splitClauses` at base `pre`-sum is all
satisfied by `extendAssign`. -/
theorem splitClauses_forward {φ : CnfFormula} (hpos : 0 < threeSatNumVars φ)
    (assignOrig : Fin φ.numVars → Bool) (hle : φ.numVars ≤ threeSatNumVars φ) :
    ∀ (pre cs : List (Clause φ.numVars)), φ.clauses = pre ++ cs →
      (∀ c ∈ cs, clauseSat assignOrig c = true) →
      (splitClauses φ hle (auxZ φ hpos) (pre.map clauseAux).sum cs).all
        (clauseSat (extendAssign φ assignOrig)) = true := by
  intro pre cs
  induction cs generalizing pre with
  | nil => intro _ _; rfl
  | cons c rest ih =>
    intro hsplit hsat
    rw [splitClauses, List.all_append, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · -- chain for c
      exact splitChain_forward_clause hpos assignOrig hle pre c rest hsplit
        (hsat c (by simp))
    · -- recurse on rest with prefix pre ++ [c]
      have hsplit' : φ.clauses = (pre ++ [c]) ++ rest := by rw [hsplit]; simp
      have hbase : ((pre ++ [c]).map clauseAux).sum = (pre.map clauseAux).sum + clauseAux c := by
        simp [List.map_append]
      have := ih (pre ++ [c]) hsplit' (fun c' hc' => hsat c' (by simp [hc']))
      rwa [hbase] at this

/-- **Forward direction.** A satisfying assignment of the original formula extends to a
satisfying assignment of the split formula (the carry-rule extension). -/
theorem satToThreeSatMap_satisfiable_of (φ : CnfFormula) (hsat : Satisfiable φ) :
    Satisfiable (satToThreeSatMap φ) := by
  obtain ⟨assignOrig, heval⟩ := hsat
  unfold satToThreeSatMap
  split
  · rename_i hpos
    refine ⟨extendAssign φ assignOrig, ?_⟩
    rw [CnfFormula.eval, List.all_eq_true] at heval ⊢
    have hall := splitClauses_forward hpos assignOrig (by unfold threeSatNumVars; omega)
      [] φ.clauses rfl (fun c hc => heval c hc)
    simp only [List.map_nil, List.sum_nil] at hall
    rw [List.all_eq_true] at hall
    exact hall
  · exact ⟨assignOrig, heval⟩

/-- **Satisfiability equivalence.** `φ` is satisfiable iff its 3-CNF split is. -/
theorem satisfiable_satToThreeSatMap_iff (φ : CnfFormula) :
    Satisfiable φ ↔ Satisfiable (satToThreeSatMap φ) :=
  ⟨satToThreeSatMap_satisfiable_of φ, satisfiable_of_satToThreeSatMap φ⟩

/-! ## Polynomial size bound

The split formula's encoding length is linearly bounded by the input's. -/

/-- The chain for a clause has at most `lits.length + 1` sub-clauses. -/
theorem splitChain_count_le {total : ℕ} (z : ℕ → Fin total) :
    ∀ (carry : Option (Literal total)) (lits : List (Literal total)) (j : ℕ),
      (splitChain z carry lits j).length ≤ lits.length + 1 := by
  intro carry lits j
  induction hn : lits.length using Nat.strong_induction_on generalizing carry lits j with
  | _ n ih =>
  subst hn
  cases carry with
  | none =>
    rcases lits with _ | ⟨l₁, _ | ⟨l₂, rest⟩⟩
    · rw [splitChain_none_short z [] j (by simp)]; simp
    · rw [splitChain_none_short z [l₁] j (by simp)]; simp
    · by_cases hlen : (l₁ :: l₂ :: rest).length ≤ 3
      · rw [splitChain_none_short z _ j hlen]; simp
      · rw [splitChain_none_long z l₁ l₂ rest j hlen, List.length_cons]
        have := ih rest.length (by simp [List.length_cons]) (some (z 0, false)) rest 1 rfl
        simp only [List.length_cons]; omega
  | some c =>
    rcases lits with _ | ⟨l₁, rest⟩
    · rw [splitChain_some_short z c [] j (by simp)]; simp
    · by_cases hlen : (l₁ :: rest).length ≤ 2
      · rw [splitChain_some_short z c _ j hlen]; simp
      · rw [splitChain_some_long z c l₁ rest j hlen, List.length_cons]
        have := ih rest.length (by simp [List.length_cons]) (some (z j, false)) rest (j + 1) rfl
        simp only [List.length_cons]; omega

/-- Each clause produced by `splitClauses` has length `≤ 3` (`splitClauses_length_le`,
restated for the local literal-count bound). -/
theorem splitClauses_count_le (φ : CnfFormula) (h : φ.numVars ≤ threeSatNumVars φ)
    (z : ℕ → Fin (threeSatNumVars φ)) (base : ℕ) (cs : List (Clause φ.numVars)) :
    (splitClauses φ h z base cs).length ≤ (cs.map (fun c => c.length + 1)).sum := by
  induction cs generalizing base with
  | nil => simp [splitClauses]
  | cons c cs ih =>
    rw [splitClauses, List.length_append, List.map_cons, List.sum_cons]
    have h1 := splitChain_count_le (fun i => z (base + i)) none (c.map (castLiteral h)) 0
    rw [List.length_map] at h1
    have h2 := ih (base + clauseAux c)
    omega

/-- Total literal occurrences in `splitClauses` are `≤ 3 ·` its clause count. -/
theorem splitClauses_litsum_le (φ : CnfFormula) (h : φ.numVars ≤ threeSatNumVars φ)
    (z : ℕ → Fin (threeSatNumVars φ)) (base : ℕ) (cs : List (Clause φ.numVars)) :
    ((splitClauses φ h z base cs).map List.length).sum ≤
      3 * (splitClauses φ h z base cs).length := by
  have hle : ∀ cl ∈ splitClauses φ h z base cs, cl.length ≤ 3 :=
    splitClauses_length_le φ h z base cs
  calc ((splitClauses φ h z base cs).map List.length).sum
      ≤ ((splitClauses φ h z base cs).map (fun _ => 3)).sum :=
        List.sum_le_sum (fun cl hcl => hle cl hcl)
    _ = 3 * (splitClauses φ h z base cs).length := by
        rw [List.map_const']; simp [Nat.mul_comm]

/-- A clause's serialization length is `1 + 2 ·` its literal count. -/
theorem clauseEncode_length {n : ℕ} (c : Clause n) : (clauseEncode c).length = 1 + 2 * c.length := by
  simp only [clauseEncode, litEncode, List.length_cons, List.length_flatMap]
  rw [List.map_const']; simp; ring

/-- The CNF serialization length: `2 + #clauses + 2 ·` total literal occurrences. -/
theorem cnfEncode_length (ψ : CnfFormula) :
    (cnfEncode ψ).length = 2 + ψ.clauses.length + 2 * (ψ.clauses.map List.length).sum := by
  simp only [cnfEncode, List.length_cons, List.length_flatMap]
  rw [show (ψ.clauses.map (fun c => (clauseEncode c).length)) =
        ψ.clauses.map (fun c => 1 + 2 * c.length) by
      apply List.map_congr_left; intro c _; exact clauseEncode_length c]
  induction ψ.clauses with
  | nil => simp
  | cons c cs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons] at ih ⊢; omega

/-- **Output-size bound.** The split formula's encoding length is `≤ 14 ·` the input's plus a
constant — a linear (hence polynomial) bound. -/
theorem cnfEncode_satToThreeSatMap_le (φ : CnfFormula) :
    (cnfEncode (satToThreeSatMap φ)).length ≤ 14 * (cnfEncode φ).length + 2 := by
  -- input total literals S and clause count C
  set S := (φ.clauses.map List.length).sum with hS
  set C := φ.clauses.length with hC
  have hin : (cnfEncode φ).length = 2 + C + 2 * S := by rw [cnfEncode_length φ]
  -- `S + C ≤ cnfEncode φ length` (used in the assembly)
  have hSC : S + C ≤ (cnfEncode φ).length := by omega
  unfold satToThreeSatMap
  split
  · rename_i hpos
    rw [cnfEncode_length]
    set OUT := splitClauses φ (by unfold threeSatNumVars; omega) (auxZ φ hpos) 0 φ.clauses
      with hOUT
    have hcount : OUT.length ≤ S + C := by
      have hc := splitClauses_count_le φ (by unfold threeSatNumVars; omega) (auxZ φ hpos) 0 φ.clauses
      rw [← hOUT] at hc
      have hsum : (φ.clauses.map (fun c => c.length + 1)).sum = S + C := by
        rw [hS, hC]
        induction φ.clauses with
        | nil => simp
        | cons c cs ih =>
          simp only [List.map_cons, List.sum_cons, List.length_cons] at ih ⊢; omega
      omega
    have hlit : (OUT.map List.length).sum ≤ 3 * OUT.length :=
      splitClauses_litsum_le φ (by unfold threeSatNumVars; omega) (auxZ φ hpos) 0 φ.clauses
    show 2 + OUT.length + 2 * (OUT.map List.length).sum ≤ 14 * (cnfEncode φ).length + 2
    omega
  · -- degenerate: output = φ
    omega

/-! ## The 3SAT decision problem and the Karp reduction `SAT ≤ₖ 3SAT` -/

/-- **3SAT**: the decision problem on 3-CNF instances — `φ` is in 3-CNF *and* satisfiable. -/
def threeSat (φ : CnfFormula) : Prop := Is3Cnf φ ∧ Satisfiable φ

/-- `threeSat` is decidable. -/
instance (φ : CnfFormula) : Decidable (threeSat φ) := by unfold threeSat; infer_instance

/-- **The Karp reduction `SAT ≤ₖ 3SAT`** by clause-splitting: `satToThreeSatMap` is many-one
correct (`Satisfiable φ ↔ threeSat (map φ)`, since the output is always 3-CNF and equisatisfiable)
with a linear output-size bound. -/
noncomputable def satToThreeSat :
    KarpReduction (fun φ => (cnfEncode φ).length) (fun φ => (cnfEncode φ).length)
      Satisfiable threeSat where
  toFun := satToThreeSatMap
  correct φ := by
    rw [threeSat]
    constructor
    · intro hsat
      exact ⟨is3Cnf_satToThreeSatMap φ, (satisfiable_satToThreeSatMap_iff φ).1 hsat⟩
    · rintro ⟨_, hsat⟩
      exact (satisfiable_satToThreeSatMap_iff φ).2 hsat
  poly := 14 * Polynomial.X + Polynomial.C 2
  size_bound φ := by
    simpa using cnfEncode_satToThreeSatMap_le φ

/-- **Payoff.** Composing Cook–Levin with this reduction, **3SAT is NP-hard** over the genuine
Turing-machine NP class (`IsNPHard_TM`), with the same encoding as SAT. This realizes the first
leg of the chain `SAT ≤ₖ 3SAT ≤ₖ … ⟹` DNC Theorem 10.2. -/
theorem isNPHard_TM_threeSat : IsNPHard_TM cnfEncode threeSat :=
  isNPHard_TM_of_satReduction satToThreeSat

/-- The same payoff as a self-contained `example` against the expected type. -/
example : IsNPHard_TM cnfEncode threeSat :=
  isNPHard_TM_of_satReduction satToThreeSat

end DeepWiki
