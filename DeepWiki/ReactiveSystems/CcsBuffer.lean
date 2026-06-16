import DeepWiki.ReactiveSystems.Ccs
import DeepWiki.ReactiveSystems.CcsProcessGraph
import Mathlib.Data.Fintype.Basic


/-! # The one-place buffer Cell and a two-place bag (Exercise 2.12)
The book's value-passing one-place buffer `Cell = in(x).Cell(x)`,
`Cell(x) = out(x).Cell`. Since this is the *pure* CCS calculus, value passing is
encoded over a finite data domain `D`: `in(x)`/`out(x)` become action families
`inᵥ`/`outᵥ` indexed by `v : D`, and `Cell` is the finite choice-sum
`Σ_{v∈D} inᵥ.Cell(v)`. A two-place bag is two cells in parallel; a two-place FIFO
queue chains two cells via the linking combinator (relabel the first cell's output
to an internal `link` channel feeding the second's input, then restrict it). -/

open DeepWiki.ReactiveSystems

namespace DeepWiki.ReactiveSystems

/-- A finite choice-sum `Σᵢ∈s f i` over a `Finset`: fold `choice` over `s.toList.map f`. -/
noncomputable def bigChoice {Name K ι : Type*} (s : Finset ι) (f : ι → CCS Name K) :
    CCS Name K :=
  (s.toList.map f).foldr CCS.choice CCS.nil

/-- A finite choice-sum moves iff one of its summands `f i` (for `i ∈ s`) moves. -/
theorem step_bigChoice_iff {Name K ι : Type*} {defn : K → CCS Name K} {s : Finset ι}
    {f : ι → CCS Name K} {a : Act Name} {R : CCS Name K} :
    Step defn (bigChoice s f) a R ↔ ∃ i ∈ s, Step defn (f i) a R := by
  rw [bigChoice, step_foldr_choice_iff]
  constructor
  · rintro ⟨t, ht, hstep⟩
    rw [List.mem_map] at ht
    obtain ⟨i, hi, rfl⟩ := ht
    exact ⟨i, Finset.mem_toList.1 hi, hstep⟩
  · rintro ⟨i, hi, hstep⟩
    exact ⟨f i, List.mem_map.2 ⟨i, Finset.mem_toList.2 hi, rfl⟩, hstep⟩

/-- Value-passing channels for the buffer: input `in(d)` and output `out(d)`,
one channel per data value `d`. -/
inductive CellChan (D : Type*)
  /-- The input channel carrying value `d`. -/
  | inp : D → CellChan D
  /-- The output channel carrying value `d`. -/
  | out : D → CellChan D
  /-- The internal link channel carrying value `d` (used to chain two cells into
  a FIFO queue). -/
  | link : D → CellChan D
  deriving DecidableEq

/-- Process constants for the buffer: the empty cell `Cell` and the full cell
`Cell(d)` holding value `d`. -/
inductive CellK (D : Type*)
  /-- The empty one-place buffer `Cell`. -/
  | cell : CellK D
  /-- The full one-place buffer `Cell(d)` holding value `d`. -/
  | cellVal : D → CellK D
  deriving DecidableEq

/-- Defining environment of the one-place buffer over a finite data domain:
`Cell = Σ_{v∈D} inᵥ.Cell(v)` and `Cell(v) = outᵥ.Cell`. -/
noncomputable def cellDefn {D : Type*} [Fintype D] : CellK D → CCS (CellChan D) (CellK D)
  | .cell => bigChoice (Finset.univ : Finset D)
      (fun v => CCS.pre (Act.name (CellChan.inp v)) (CCS.const (CellK.cellVal v)))
  | .cellVal v => CCS.pre (Act.name (CellChan.out v)) (CCS.const CellK.cell)

/-- The empty cell can input value `v`, becoming the full cell `Cell(v)`. -/
theorem cell_input {D : Type*} [Fintype D] (v : D) :
    Step cellDefn (CCS.const CellK.cell) (Act.name (CellChan.inp v))
      (CCS.const (CellK.cellVal v)) := by
  apply Step.con
  rw [cellDefn]
  rw [step_bigChoice_iff]
  exact ⟨v, Finset.mem_univ v, Step.act _ _⟩

/-- The full cell `Cell(v)` can output its value `v`, becoming empty again. -/
theorem cell_output {D : Type*} [Fintype D] (v : D) :
    Step cellDefn (CCS.const (CellK.cellVal v)) (Act.name (CellChan.out v))
      (CCS.const CellK.cell) := by
  apply Step.con
  rw [cellDefn]
  exact Step.act _ _

/-- The only moves of the empty cell are inputs: `Cell —a→ R` iff `a = inᵥ` and
`R = Cell(v)` for some value `v`. -/
theorem cell_input_iff {D : Type*} [Fintype D] (a : Act (CellChan D))
    (R : CCS (CellChan D) (CellK D)) :
    Step cellDefn (CCS.const CellK.cell) a R ↔
      ∃ v, a = Act.name (CellChan.inp v) ∧ R = CCS.const (CellK.cellVal v) := by
  rw [step_const_iff, cellDefn, step_bigChoice_iff]
  constructor
  · rintro ⟨v, _, hstep⟩
    rw [step_pre_iff] at hstep
    obtain ⟨rfl, rfl⟩ := hstep
    exact ⟨v, rfl, rfl⟩
  · rintro ⟨v, rfl, rfl⟩
    exact ⟨v, Finset.mem_univ v, Step.act _ _⟩

/-- A two-place bag: two empty cells in parallel, with `in`/`out` as the external
interface (unrestricted). -/
def twoBag {D : Type*} [Fintype D] : CCS (CellChan D) (CellK D) :=
  CCS.par (CCS.const CellK.cell) (CCS.const CellK.cell)

/-- The bag can input value `v` via its left cell, filling it to `Cell(v)`. -/
theorem twoBag_input {D : Type*} [Fintype D] (v : D) :
    Step cellDefn twoBag (Act.name (CellChan.inp v))
      (CCS.par (CCS.const (CellK.cellVal v)) (CCS.const CellK.cell)) := by
  exact Step.com1 (cell_input v)

/-! ## A two-place FIFO queue via the linking combinator -/

/-- Relabelling for the *left* cell of the queue: its output channel `outᵥ` is
renamed to the internal link `linkᵥ`; everything else is unchanged. -/
def relOut {D : Type*} : Act (CellChan D) → Act (CellChan D)
  | Act.name (CellChan.out v) => Act.name (CellChan.link v)
  | Act.coname (CellChan.out v) => Act.coname (CellChan.link v)
  | a => a

/-- Relabelling for the *right* cell of the queue: its input channel `inᵥ` is
renamed to the *complementary* internal link, so it consumes the left cell's link
output; everything else is unchanged. -/
def relIn {D : Type*} : Act (CellChan D) → Act (CellChan D)
  | Act.name (CellChan.inp v) => Act.coname (CellChan.link v)
  | Act.coname (CellChan.inp v) => Act.name (CellChan.link v)
  | a => a

/-- The internal link channels, restricted away in the queue. -/
def linkChans (D : Type*) : Set (Act (CellChan D)) :=
  {a | ∃ v, a = Act.name (CellChan.link v) ∨ a = Act.coname (CellChan.link v)}

/-- A **two-place FIFO queue** built from two cells by the linking combinator: the
left cell's output is renamed to an internal link feeding the right cell's input,
which is then restricted. The queue's external interface is the left cell's input
and the right cell's output. -/
def fifoQueue {D : Type*} [Fintype D] : CCS (CellChan D) (CellK D) :=
  CCS.restrict
    (CCS.par (CCS.relabel (CCS.const CellK.cell) relOut)
      (CCS.relabel (CCS.const CellK.cell) relIn))
    (linkChans D)

/-- The queue can input value `v` (into its left cell), an externally observable
`inᵥ` action surviving the link restriction. -/
theorem fifoQueue_input {D : Type*} [Fintype D] (v : D) :
    Step cellDefn fifoQueue (Act.name (CellChan.inp v))
      (CCS.restrict
        (CCS.par (CCS.relabel (CCS.const (CellK.cellVal v)) relOut)
          (CCS.relabel (CCS.const CellK.cell) relIn))
        (linkChans D)) := by
  refine Step.res ?_ ?_ (Step.com1 (Step.rel (cell_input v)))
  · rintro ⟨w, hw | hw⟩ <;> simp at hw
  · rintro ⟨w, hw | hw⟩ <;> simp [Act.co] at hw

end DeepWiki.ReactiveSystems
