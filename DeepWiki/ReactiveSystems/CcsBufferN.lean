import DeepWiki.ReactiveSystems.Bisimulation
import DeepWiki.ReactiveSystems.Ccs

/-! # An `n`-place buffer equals `n` one-place buffers (Proposition 3.2)
The general buffer-implementation result: a capacity-`n` buffer
`Bⁿ₀ = in.Bⁿ₁`, `Bⁿᵢ = in.Bⁿᵢ₊₁ + out.Bⁿᵢ₋₁` (`0 < i < n`), `Bⁿₙ = out.Bⁿₙ₋₁`
is strongly bisimilar to the parallel product of `n` one-place buffers
`B¹₀ = in.B¹₁`, `B¹₁ = out.B¹₀`. We represent the product faithfully as a bag
`bufBag bs` over a bit-list (`true ↦ B¹₁` full, `false ↦ B¹₀` empty); an `in`
flips some empty component to full, an `out` flips some full to empty, and the
length stays `n` while the number of full components (`bs.count true`) is the
buffer's contents. The book's relation `R` (`bufNRel`) is a strong bisimulation
(Proposition 3.2), whence `Bⁿ₀ ~ (B¹₀)ⁿ`. -/

namespace DeepWiki.ReactiveSystems

open LTS

/-- The two channels of the buffer: `in` and `out`. -/
inductive BufNChan | bin | bout
  deriving DecidableEq

/-- Process constants: the one-place buffer states `one false = B¹₀` (empty) /
`one true = B¹₁` (full), and the capacity-`n` buffer `nbuf n i = Bⁿᵢ`. -/
inductive BufNK | one (b : Bool) | nbuf (n i : ℕ)
  deriving DecidableEq

open BufNChan BufNK

/-- The defining environment (§3.3, p.51): `B¹₀ = in.B¹₁`, `B¹₁ = out.B¹₀`; and
`Bⁿᵢ` offers `in.Bⁿᵢ₊₁` exactly when not full (`i < n`) and `out.Bⁿᵢ₋₁` exactly
when not empty (`0 < i`). -/
def bufNDefn : BufNK → CCS BufNChan BufNK
  | one false => .pre (.name bin) (.const (one true))
  | one true => .pre (.name bout) (.const (one false))
  | nbuf n i =>
      if i < n then
        if 0 < i then
          .choice (.pre (.name bin) (.const (nbuf n (i + 1))))
            (.pre (.name bout) (.const (nbuf n (i - 1))))
        else .pre (.name bin) (.const (nbuf n (i + 1)))
      else
        if 0 < i then .pre (.name bout) (.const (nbuf n (i - 1)))
        else .nil

/-- A one-place buffer component: `bbItem true = B¹₁` (full), `bbItem false = B¹₀`
(empty). -/
def bbItem (b : Bool) : CCS BufNChan BufNK := .const (one b)

/-- The parallel product `B¹ᵢ₁ ∣ ⋯ ∣ B¹ᵢₙ` as a bag (right-nested) over a
bit-list: `bufBag [] = 0` and `bufBag (b :: bs) = bbItem b ∣ bufBag bs`. -/
def bufBag : List Bool → CCS BufNChan BufNK
  | [] => .nil
  | b :: bs => .par (bbItem b) (bufBag bs)

/-- A one-place buffer component steps by toggling: empty does `in` to full, full
does `out` to empty. -/
theorem bbItem_step_iff {b : Bool} {α : Act BufNChan} {Q : CCS BufNChan BufNK} :
    Step bufNDefn (bbItem b) α Q ↔
      (b = false ∧ α = Act.name bin ∧ Q = bbItem true) ∨
      (b = true ∧ α = Act.name bout ∧ Q = bbItem false) := by
  cases b with
  | false => simp [bbItem, step_const_iff, bufNDefn]
  | true => simp [bbItem, step_const_iff, bufNDefn]

/-- The bag never performs a co-name (its components only do the names
`in`/`out`), so a synchronisation is impossible. -/
theorem bufBag_no_co {bs : List Bool} {x : BufNChan} {P : CCS BufNChan BufNK} :
    ¬ Step bufNDefn (bufBag bs) (Act.coname x) P := by
  induction bs generalizing P with
  | nil => rw [bufBag]; simp
  | cons b bs ih =>
    rw [bufBag, step_par_iff]
    rintro (⟨P', hP, rfl⟩ | ⟨Q', hQ, rfl⟩ | ⟨ℓ, P', Q', hτ, -, -, -, rfl⟩)
    · rcases bbItem_step_iff.1 hP with ⟨-, hco, -⟩ | ⟨-, hco, -⟩ <;> simp at hco
    · exact ih hQ
    · simp at hτ

/-- **Reachable-state transitions of the bag.** `bufBag bs` performs exactly:
`in`, flipping some empty component to full (`bs = pre ++ false :: suf ↦
pre ++ true :: suf`); or `out`, flipping some full component to empty. -/
theorem bufBag_step_iff {bs : List Bool} {α : Act BufNChan} {Q : CCS BufNChan BufNK} :
    Step bufNDefn (bufBag bs) α Q ↔
      (α = Act.name bin ∧
        ∃ pre suf, bs = pre ++ false :: suf ∧ Q = bufBag (pre ++ true :: suf)) ∨
      (α = Act.name bout ∧
        ∃ pre suf, bs = pre ++ true :: suf ∧ Q = bufBag (pre ++ false :: suf)) := by
  induction bs generalizing Q with
  | nil =>
    rw [bufBag]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro (⟨_, _, _, h, _⟩ | ⟨_, _, _, h, _⟩) <;> simp at h
  | cons b bs ih =>
    rw [bufBag, step_par_iff]
    constructor
    · rintro (⟨P', hP, rfl⟩ | ⟨Q', hQ, rfl⟩ | ⟨ℓ, P', Q', rfl, -, hP, hQ, rfl⟩)
      · -- COM1: the head component toggles
        rcases bbItem_step_iff.1 hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        · exact Or.inl ⟨rfl, [], bs, rfl, rfl⟩
        · exact Or.inr ⟨rfl, [], bs, rfl, rfl⟩
      · -- COM2: a component deeper in the bag toggles
        rcases ih.1 hQ with ⟨rfl, pre, suf, rfl, rfl⟩ | ⟨rfl, pre, suf, rfl, rfl⟩
        · exact Or.inl ⟨rfl, b :: pre, suf, rfl, rfl⟩
        · exact Or.inr ⟨rfl, b :: pre, suf, rfl, rfl⟩
      · -- COM3: synchronisation is impossible (no co-name)
        rcases bbItem_step_iff.1 hP with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;>
          exact absurd hQ bufBag_no_co
    · rintro (⟨rfl, pre, suf, hbs, rfl⟩ | ⟨rfl, pre, suf, hbs, rfl⟩)
      · -- in: flip some empty to full
        cases pre with
        | nil =>
          obtain ⟨rfl, rfl⟩ : b = false ∧ bs = suf := by simpa using hbs
          exact Or.inl ⟨bbItem true, bbItem_step_iff.2 (Or.inl ⟨rfl, rfl, rfl⟩), rfl⟩
        | cons c pre =>
          obtain ⟨rfl, rfl⟩ : b = c ∧ bs = pre ++ false :: suf := by simpa using hbs
          exact Or.inr (Or.inl ⟨bufBag (pre ++ true :: suf),
            ih.2 (Or.inl ⟨rfl, pre, suf, rfl, rfl⟩), rfl⟩)
      · -- out: flip some full to empty
        cases pre with
        | nil =>
          obtain ⟨rfl, rfl⟩ : b = true ∧ bs = suf := by simpa using hbs
          exact Or.inl ⟨bbItem false, bbItem_step_iff.2 (Or.inr ⟨rfl, rfl, rfl⟩), rfl⟩
        | cons c pre =>
          obtain ⟨rfl, rfl⟩ : b = c ∧ bs = pre ++ true :: suf := by simpa using hbs
          exact Or.inr (Or.inl ⟨bufBag (pre ++ false :: suf),
            ih.2 (Or.inr ⟨rfl, pre, suf, rfl, rfl⟩), rfl⟩)

/-- **Transitions of the buffer specification.** `Bⁿᵢ` does `in` to `Bⁿᵢ₊₁` when
not full (`i < n`), and `out` to `Bⁿᵢ₋₁` when not empty (`0 < i`). -/
theorem nbuf_step_iff {n i : ℕ} {α : Act BufNChan} {Q : CCS BufNChan BufNK} :
    Step bufNDefn (.const (nbuf n i)) α Q ↔
      (i < n ∧ α = Act.name bin ∧ Q = .const (nbuf n (i + 1))) ∨
      (0 < i ∧ α = Act.name bout ∧ Q = .const (nbuf n (i - 1))) := by
  rw [step_const_iff, bufNDefn]
  split_ifs <;> simp_all

/-- A toggle preserves the length of the bag. -/
theorem length_flip (pre suf : List Bool) (a b : Bool) :
    (pre ++ a :: suf).length = (pre ++ b :: suf).length := by simp

/-- A `true`-flip raises the `full` count by one. -/
theorem countT_flip (pre suf : List Bool) :
    (pre ++ true :: suf).count true = (pre ++ false :: suf).count true + 1 := by
  have h1 : (true :: suf).count true = suf.count true + 1 := by simp
  have h2 : (false :: suf).count true = suf.count true := by simp
  rw [List.count_append, List.count_append, h1, h2]; omega

/-- `count true < length` exactly when an empty (`false`) component is present. -/
theorem countT_lt_length {bs : List Bool} (h : false ∈ bs) :
    bs.count true < bs.length := by
  rcases Nat.lt_or_ge (bs.count true) bs.length with h' | h'
  · exact h'
  · have hle : bs.count true ≤ bs.length := List.count_le_length
    have heq : bs.count true = bs.length := le_antisymm hle h'
    rw [List.count_eq_length] at heq
    exact absurd (heq false h) (by simp)

/-- **The book's relation `R`** (§3.3, p.51): a bag of one-place buffers is
related to the capacity-`length` buffer holding as many items as the bag has full
components. -/
def bufNRel : CCS BufNChan BufNK → CCS BufNChan BufNK → Prop := fun p q =>
  ∃ bs : List Bool, p = bufBag bs ∧ q = .const (nbuf bs.length (bs.count true))

/-- **Proposition 3.2** (§3.3, p.51). The relation `bufNRel` (the book's `R`) is a
strong bisimulation. -/
theorem isBisimulation_bufNRel : IsBisimulation (ccsLTS bufNDefn) bufNRel := by
  rintro p q ⟨bs, rfl, rfl⟩
  refine ⟨fun α p' hp => ?_, fun α q' hq => ?_⟩
  · -- a move of `bufBag bs` is matched by `B^(len) (count)`
    rw [ccsLTS_step, bufBag_step_iff] at hp
    rcases hp with ⟨rfl, pre, suf, rfl, rfl⟩ | ⟨rfl, pre, suf, rfl, rfl⟩
    · -- `in`: count rises, still < length
      refine ⟨.const (nbuf (pre ++ false :: suf).length
        ((pre ++ false :: suf).count true + 1)), ?_, ⟨_, rfl, ?_⟩⟩
      · rw [ccsLTS_step, nbuf_step_iff]
        exact Or.inl ⟨countT_lt_length (by simp), rfl, rfl⟩
      · rw [length_flip _ _ true false, countT_flip]
    · -- `out`: count drops, still > 0
      refine ⟨.const (nbuf (pre ++ true :: suf).length
        ((pre ++ true :: suf).count true - 1)), ?_, ⟨_, rfl, ?_⟩⟩
      · rw [ccsLTS_step, nbuf_step_iff]
        exact Or.inr ⟨by rw [countT_flip]; omega, rfl, rfl⟩
      · rw [length_flip _ _ false true, countT_flip]; simp
  · -- a move of `B^(len) (count)` is matched by `bufBag bs`
    rw [ccsLTS_step, nbuf_step_iff] at hq
    rcases hq with ⟨hlt, rfl, rfl⟩ | ⟨hpos, rfl, rfl⟩
    · -- `in`: count < length ⟹ an empty component exists
      have hmem : false ∈ bs := by
        by_contra hf
        have hall : ∀ x ∈ bs, true = x := by
          intro x hx; cases x
          · exact absurd hx hf
          · rfl
        rw [← List.count_eq_length] at hall; omega
      obtain ⟨pre, suf, rfl⟩ := List.append_of_mem hmem
      refine ⟨bufBag (pre ++ true :: suf), ?_, ⟨_, rfl, ?_⟩⟩
      · rw [ccsLTS_step, bufBag_step_iff]; exact Or.inl ⟨rfl, pre, suf, rfl, rfl⟩
      · rw [length_flip _ _ true false, countT_flip]
    · -- `out`: count > 0 ⟹ a full component exists
      have hmem : true ∈ bs := List.count_pos_iff.1 hpos
      obtain ⟨pre, suf, rfl⟩ := List.append_of_mem hmem
      refine ⟨bufBag (pre ++ false :: suf), ?_, ⟨_, rfl, ?_⟩⟩
      · rw [ccsLTS_step, bufBag_step_iff]; exact Or.inr ⟨rfl, pre, suf, rfl, rfl⟩
      · rw [length_flip _ _ false true, countT_flip]; simp

/-- **Proposition 3.2** (§3.3, p.51). A capacity-`n` buffer is strongly bisimilar
to `n` one-place buffers in parallel: `Bⁿ₀ ~ (B¹₀)ⁿ`. -/
theorem bufN_bisim (n : ℕ) :
    (CCS.const (nbuf n 0)) ~[ccsLTS bufNDefn] (bufBag (List.replicate n false)) := by
  refine Bisimilar.symm (isBisimulation_bufNRel.le_bisimilar ⟨List.replicate n false, rfl, ?_⟩)
  simp [List.length_replicate, List.count_replicate]

end DeepWiki.ReactiveSystems
