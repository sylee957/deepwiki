import DeepWiki.NetworkCalculus.ThreeSatReduction
import DeepWiki.NetworkCalculus.ThreeDimensionalMatchingReduction

/-! # The classic Karp reduction `3SAT ≤ₖ 3DM` (Garey-Johnson Theorem 3.2 / Karp 1972)
The keystone gadget connecting `cookLevin` through `3SAT` to 3-Dimensional Matching, and
thence (via the already-proved `3DM ≤ₖ X3C` and `X3C ≤ₖ worst-case-backlog`) to DNC
Theorem 10.2.

For a 3-CNF `φ` with `n` variables and `m` clauses the construction has three layers:

* **Truth-setting** (per variable `uᵢ`): a `2m`-triple ring over `2m` core elements whose
  two perfect-cover orientations encode `uᵢ = true` / `uᵢ = false`. The ring leaves exactly
  the `m` *tip* elements of the *unselected* orientation free for a clause gadget to consume.
* **Satisfaction-testing** (per clause `cⱼ`): two fresh elements and one triple per literal,
  each triple consuming a *true-tip* of the satisfying orientation of the literal's variable;
  the two clause elements can be covered iff some literal of `cⱼ` is true.
* **Garbage collection**: extra core elements + triples consuming all tips left free by the
  truth-setting rings and not used by clause gadgets, balancing `|W| = |X| = |Y| = q`.

What is **proved** here (both correctness directions): the gadget data, the equal-card map
(`threeSatToThreeDMMap`, with `|W| = |X| = |Y| = 2nm` proved), and the full bi-implication
`threeSat φ ↔ threeDMDecision (map φ)` —
* **forward** (`threeDMDecision_gadgetInstance_of_satisfiable`): a satisfying assignment yields
  a perfect matching (orient each ring, route each clause through a satisfying literal's tip,
  garbage-collect the rest); and
* **reverse** (`satisfiable_of_threeDMDecision_gadgetInstance`): a perfect matching reads off a
  consistent satisfying assignment — the *ring consistency* lemma
  (`forall_falseTriple_mem_of_one`) shows the cyclic chaining forces a uniform orientation per
  variable, and the clause gadgets (`clauseSat_readAssign`) force a true literal.

This packages into `threeSatToThreeDM : KarpReduction ThreeDM.cnfSize ThreeDMInstance.size
threeSat threeDMDecision` (genuine Karp reduction; `IsNPHardVia`, unconditional). The only
piece **not** wired is the absolute Cook–Levin chain `isNPHard_TM_threeDM`, which needs the
source measured by `cnfEncode · |·|` rather than `cnfSize`; the two differ by `numVars`, so a
variable-compaction prepass is required (scoped `[infra]` in the note at the end).
-/

namespace DeepWiki

open Finset

namespace ThreeDM

/-! ## Gadget dimensions
A 3-CNF formula `φ` is summarized by `n = φ.numVars` and `m = φ.clauses.length`. We build the
gadget over these two numbers; the whole construction is parameterized by `(n, m)` with the
literal data of the clauses entering only the clause gadget. We always work in the regime
`m ≥ 1` (a formula with no clauses is trivially satisfiable and is handled by the total map's
degenerate branch). -/

/-- The number of clauses of `φ` (gadget parameter `m`). -/
def numClauses (φ : CnfFormula) : ℕ := φ.clauses.length

/-! ## The three parts `W`, `X`, `Y`
With `n` variables, `m` clauses, and (in the non-degenerate regime) `n ≥ 1`, the exact element
counts are:

* **`W`** `= ` ring `a`-cores `(Fin n × Fin m)` `⊕` clause-`W` `(Fin m)` `⊕` garbage-`W`
  `(Fin ((n-1)*m))` — total `nm + m + (n-1)m = 2nm`.
* **`X`** `= ` ring `b`-cores `(Fin n × Fin m)` `⊕` clause-`X` `(Fin m)` `⊕` garbage-`X`
  `(Fin ((n-1)*m))` — total `2nm`.
* **`Y`** `= ` positive tips `(Fin n × Fin m)` `⊕` negative tips `(Fin n × Fin m)` — total
  `2nm`.

So `|W| = |X| = |Y| = 2nm =: q`, the equal-card invariant the `ThreeDMInstance` demands. -/

/-- The `W` part: ring `a`-cores `Fin n × Fin m`, clause-`W` elements `Fin m`, garbage-`W`
elements `Fin ((n-1)*m)`. Cardinality `2nm` when `n ≥ 1`. -/
abbrev PartW (n m : ℕ) : Type := (Fin n × Fin m) ⊕ Fin m ⊕ Fin ((n - 1) * m)

/-- The `X` part: ring `b`-cores `Fin n × Fin m`, clause-`X` elements `Fin m`, garbage-`X`
elements `Fin ((n-1)*m)`. Cardinality `2nm` when `n ≥ 1`. -/
abbrev PartX (n m : ℕ) : Type := (Fin n × Fin m) ⊕ Fin m ⊕ Fin ((n - 1) * m)

/-- The `Y` part: positive tips `Fin n × Fin m` and negative tips `Fin n × Fin m`.
Cardinality `2nm`. -/
abbrev PartY (n m : ℕ) : Type := (Fin n × Fin m) ⊕ (Fin n × Fin m)

/-- `|W| = 2nm` when `n ≥ 1`. -/
theorem card_partW (n m : ℕ) (hn : 1 ≤ n) :
    Fintype.card (PartW n m) = 2 * n * m := by
  simp only [PartW, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  rw [Nat.sub_one_mul]
  have : m ≤ n * m := Nat.le_mul_of_pos_left m hn
  ring_nf
  omega

/-- `|X| = 2nm` when `n ≥ 1`. -/
theorem card_partX (n m : ℕ) (hn : 1 ≤ n) :
    Fintype.card (PartX n m) = 2 * n * m :=
  card_partW n m hn

/-- `|Y| = 2nm`. -/
theorem card_partY (n m : ℕ) :
    Fintype.card (PartY n m) = 2 * n * m := by
  simp only [PartY, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  ring

/-! ## Element constructors
Named injections of each element kind into its part. -/

/-- Ring `a`-core `(i, j)` as a `W` element. -/
def aCore {n m : ℕ} (i : Fin n) (j : Fin m) : PartW n m := Sum.inl (i, j)
/-- Clause-`W` element of clause `j`. -/
def clauseW {n m : ℕ} (j : Fin m) : PartW n m := Sum.inr (Sum.inl j)
/-- Garbage-`W` element `k`. -/
def garbW {n m : ℕ} (k : Fin ((n - 1) * m)) : PartW n m := Sum.inr (Sum.inr k)

/-- Ring `b`-core `(i, j)` as an `X` element. -/
def bCore {n m : ℕ} (i : Fin n) (j : Fin m) : PartX n m := Sum.inl (i, j)
/-- Clause-`X` element of clause `j`. -/
def clauseX {n m : ℕ} (j : Fin m) : PartX n m := Sum.inr (Sum.inl j)
/-- Garbage-`X` element `k`. -/
def garbX {n m : ℕ} (k : Fin ((n - 1) * m)) : PartX n m := Sum.inr (Sum.inr k)

/-- Positive tip `(i, j)` as a `Y` element — free when variable `i` is set `true`, consumed by
positive literals of `uᵢ`. -/
def posTip {n m : ℕ} (i : Fin n) (j : Fin m) : PartY n m := Sum.inl (i, j)
/-- Negative tip `(i, j)` as a `Y` element — free when variable `i` is set `false`, consumed by
negative literals of `uᵢ`. -/
def negTip {n m : ℕ} (i : Fin n) (j : Fin m) : PartY n m := Sum.inr (i, j)

/-- The triple type `W × X × Y` of the gadget. -/
abbrev Triple (n m : ℕ) : Type := PartW n m × PartX n m × PartY n m

/-- Cyclic successor on `Fin m` (needs no `NeZero m`: the existence of `j : Fin m` forces
`m > 0`). Used to chain the false-triples around the ring. -/
def ringSucc {m : ℕ} (j : Fin m) : Fin m :=
  ⟨(j.val + 1) % m, Nat.mod_lt _ (Nat.pos_of_ne_zero (by rintro rfl; exact absurd j.isLt (by simp)))⟩

/-- `ringSucc` is a bijection of `Fin m` (it is the standard `m`-cycle). -/
theorem ringSucc_bijective {m : ℕ} : Function.Bijective (ringSucc (m := m)) := by
  refine (Finite.injective_iff_bijective).1 ?_
  intro a b hab
  have hab' : (a.val + 1) % m = (b.val + 1) % m := congrArg Fin.val hab
  have ha := a.isLt
  have hb := b.isLt
  refine Fin.ext ?_
  rcases Nat.lt_or_ge (a.val + 1) m with h1 | h1 <;>
  rcases Nat.lt_or_ge (b.val + 1) m with h2 | h2
  · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hab'; omega
  · rw [Nat.mod_eq_of_lt h1, show b.val + 1 = m by omega, Nat.mod_self] at hab'; omega
  · rw [Nat.mod_eq_of_lt h2, show a.val + 1 = m by omega, Nat.mod_self] at hab'; omega
  · omega

/-- Every ring index has a `ringSucc`-predecessor (`ringSucc` is surjective). Used to cover
the `a`-cores of a false-oriented variable. -/
theorem exists_ringSucc_eq {m : ℕ} (j : Fin m) : ∃ j', ringSucc j' = j :=
  ringSucc_bijective.surjective j

/-- Cyclic predecessor on `Fin m`: the `ringSucc`-preimage of `j`. -/
noncomputable def ringPred {m : ℕ} (j : Fin m) : Fin m :=
  (exists_ringSucc_eq j).choose

/-- `ringSucc (ringPred j) = j`. -/
@[simp] theorem ringSucc_ringPred {m : ℕ} (j : Fin m) : ringSucc (ringPred j) = j :=
  (exists_ringSucc_eq j).choose_spec

/-- `ringPred (ringSucc j) = j`. -/
@[simp] theorem ringPred_ringSucc {m : ℕ} (j : Fin m) : ringPred (ringSucc j) = j :=
  ringSucc_bijective.injective (ringSucc_ringPred (ringSucc j))

/-- Iterating `ringSucc` `d` times advances the index by `d` (mod `m`). -/
theorem ringSucc_iterate_val {m : ℕ} (j : Fin m) (d : ℕ) :
    (ringSucc^[d] j).val = (j.val + d) % m := by
  induction d with
  | zero => simp [Nat.mod_eq_of_lt j.isLt]
  | succ d ih =>
    rw [Function.iterate_succ_apply']
    show ((ringSucc^[d] j).val + 1) % m = (j.val + (d + 1)) % m
    rw [ih, Nat.mod_add_mod, Nat.add_assoc]

/-- Every ring index is reachable from any other by iterating `ringSucc` (the ring is one
`m`-cycle). -/
theorem exists_iterate_ringSucc {m : ℕ} (j j' : Fin m) : ∃ d, ringSucc^[d] j = j' := by
  refine ⟨j'.val + m - j.val, ?_⟩
  apply Fin.ext
  rw [ringSucc_iterate_val]
  have hj := j.isLt
  have hj' := j'.isLt
  rw [show j.val + (j'.val + m - j.val) = j'.val + m by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt hj']

/-! ## The truth-setting ring triples
For variable `i` and ring index `j`:

* **True-triple** `T i j = (aCore i j, bCore i j, negTip i j)` — selected when `uᵢ = true`;
  covers the `negTip` (so `posTip`s stay free for positive literals).
* **False-triple** `F i j = (aCore i (j+1), bCore i j, posTip i j)` — selected when
  `uᵢ = false`; the cyclic `j+1` makes the false-triples cover all `a`-cores, and covers the
  `posTip` (so `negTip`s stay free for negative literals).

Selecting *all* true-triples or *all* false-triples of variable `i` perfectly covers its
`2m` cores; the two orientations encode the truth value. -/

/-- True-triple `T i j = (aCore i j, bCore i j, negTip i j)` (selected when `uᵢ = true`). -/
def trueTriple {n m : ℕ} (i : Fin n) (j : Fin m) : Triple n m :=
  (aCore i j, bCore i j, negTip i j)

/-- False-triple `F i j = (aCore i (j+1), bCore i j, posTip i j)` (selected when `uᵢ = false`;
cyclic `j+1` in `Fin m`). -/
def falseTriple {n m : ℕ} (i : Fin n) (j : Fin m) : Triple n m :=
  (aCore i (ringSucc j), bCore i j, posTip i j)

/-! ## Garbage triples
For garbage index `k` and *any* tip `t`, a triple `(garbW k, garbX k, t)`. A garbage pair can
therefore absorb any single leftover tip; the `(n-1)m` garbage pairs absorb exactly the
`(n-1)m` tips left free by the rings and unused by clauses. -/

/-- Garbage triple `(garbW k, garbX k, t)` for garbage index `k` and tip `t`. -/
def garbTriple {n m : ℕ} (k : Fin ((n - 1) * m)) (t : PartY n m) : Triple n m :=
  (garbW k, garbX k, t)

/-! ## The clause (satisfaction-testing) triples
For clause `j` and a literal `l = (v, sign)` of it, the triple `(clauseW j, clauseX j, tip)`,
where `tip = posTip v j` for a positive literal (`sign = true`, satisfied by `uᵥ = true`, which
frees `posTip`) and `tip = negTip v j` for a negative literal (`sign = false`, satisfied by
`uᵥ = false`, which frees `negTip`). Covering the pair `(clauseW j, clauseX j)` thus needs some
literal of clause `j` to be true under the chosen orientation. -/

/-- The `Y`-tip a literal `l = (v, sign)` of clause `j` consumes: `posTip v j` if positive,
`negTip v j` if negative. -/
def litTip {n m : ℕ} (j : Fin m) (l : Fin n × Bool) : PartY n m :=
  if l.2 then posTip l.1 j else negTip l.1 j

/-- The clause triple for literal `l` of clause `j`: `(clauseW j, clauseX j, litTip j l)`. -/
def clauseTriple {n m : ℕ} (j : Fin m) (l : Fin n × Bool) : Triple n m :=
  (clauseW j, clauseX j, litTip j l)

/-! ## The full triple family `M`
`M` is the union of all ring triples (`trueTriple`/`falseTriple` over every `(i, j)`), all
clause triples (one per literal occurrence), and all garbage triples (every garbage index ×
every tip). We work with `n = φ.numVars` and `m = φ.clauses.length`. -/

variable (φ : CnfFormula)

/-- All ring triples of the gadget: `trueTriple i j` and `falseTriple i j` for every variable
`i` and ring index `j`. -/
def ringTriples (n m : ℕ) : Finset (Triple n m) :=
  (Finset.univ.image (fun p : Fin n × Fin m => trueTriple p.1 p.2)) ∪
    (Finset.univ.image (fun p : Fin n × Fin m => falseTriple p.1 p.2))

/-- All garbage triples: `garbTriple k t` for every garbage index `k` and every tip `t`. -/
def garbTriples (n m : ℕ) : Finset (Triple n m) :=
  Finset.univ.image (fun p : Fin ((n - 1) * m) × PartY n m => garbTriple p.1 p.2)

/-- All clause triples of `φ`: for each clause index `j` and each literal `l` occurring in
clause `j`, the triple `clauseTriple j l`. -/
def clauseTriples : Finset (Triple φ.numVars φ.clauses.length) :=
  Finset.univ.biUnion (fun j : Fin φ.clauses.length =>
    ((φ.clauses.get j).map (fun l => clauseTriple j l)).toFinset)

/-- The full gadget triple family `M` of `φ`: ring ∪ clause ∪ garbage triples. -/
def gadgetM : Finset (Triple φ.numVars φ.clauses.length) :=
  ringTriples φ.numVars φ.clauses.length ∪ clauseTriples φ ∪
    garbTriples φ.numVars φ.clauses.length

/-! ## The 3DM instance of the gadget
Bundled as a `ThreeDMInstance` with the three parts `PartW/X/Y n m`, the gadget triple family
`gadgetM φ`, and the common size `q = 2nm` (proved equal for all three parts when `n ≥ 1`). -/

/-- The 3DM instance built from `φ` when `n = numVars ≥ 1` (the non-degenerate regime). Parts
`PartW/X/Y`, triple family `gadgetM φ`, common card `q = 2 * numVars * (#clauses)`. -/
def gadgetInstance (hn : 1 ≤ φ.numVars) : ThreeDMInstance where
  W := PartW φ.numVars φ.clauses.length
  X := PartX φ.numVars φ.clauses.length
  Y := PartY φ.numVars φ.clauses.length
  M := gadgetM φ
  q := 2 * φ.numVars * φ.clauses.length
  card_W := card_partW _ _ hn
  card_X := card_partX _ _ hn
  card_Y := card_partY _ _

@[simp] theorem gadgetInstance_W (hn : 1 ≤ φ.numVars) :
    (gadgetInstance φ hn).W = PartW φ.numVars φ.clauses.length := rfl
@[simp] theorem gadgetInstance_X (hn : 1 ≤ φ.numVars) :
    (gadgetInstance φ hn).X = PartX φ.numVars φ.clauses.length := rfl
@[simp] theorem gadgetInstance_Y (hn : 1 ≤ φ.numVars) :
    (gadgetInstance φ hn).Y = PartY φ.numVars φ.clauses.length := rfl
@[simp] theorem gadgetInstance_M (hn : 1 ≤ φ.numVars) :
    (gadgetInstance φ hn).M = gadgetM φ := rfl

/-! ## Forward direction: a satisfying assignment yields a perfect matching
Given `σ` satisfying `φ`, the matching `N` is built in three layers:

* the **ring orientation** of each variable (all true-triples if `σ i = true`, else all
  false-triples),
* one **clause triple** per clause routed through a satisfying literal, and
* **garbage triples** covering every tip left free.

We first set up the chosen satisfying literal of each clause. -/

variable {φ}

/-- The tip a tip-element `t : PartY` is, read as `(variable, sign, ring-index)`: `posTip i j ↦
(i, true, j)`, `negTip i j ↦ (i, false, j)`. -/
def tipData {n m : ℕ} : PartY n m → (Fin n × Bool × Fin m)
  | Sum.inl (i, j) => (i, true, j)
  | Sum.inr (i, j) => (i, false, j)

/-- A tip is **free** under `σ` iff it is in the satisfying orientation of its variable:
`posTip i j` free iff `σ i = true`, `negTip i j` free iff `σ i = false`. -/
def IsFreeTip {n m : ℕ} (σ : Fin n → Bool) (t : PartY n m) : Prop :=
  σ (tipData t).1 = (tipData t).2.1

instance {n m : ℕ} (σ : Fin n → Bool) (t : PartY n m) : Decidable (IsFreeTip σ t) := by
  unfold IsFreeTip; infer_instance

/-- `litSat σ l = true` means exactly `σ l.1 = l.2`. -/
theorem litSat_eq_true_iff {n : ℕ} (σ : Fin n → Bool) (l : Fin n × Bool) :
    CnfFormula.litSat σ l = true ↔ σ l.1 = l.2 := by
  simp [CnfFormula.litSat]

/-- A satisfying `σ` satisfies clause `j`: `∃ l ∈ φ.clauses.get j, σ l.1 = l.2`. -/
theorem exists_litSat_of_eval {σ : Fin φ.numVars → Bool} (hσ : φ.eval σ = true)
    (j : Fin φ.clauses.length) :
    ∃ l ∈ φ.clauses.get j, σ l.1 = l.2 := by
  rw [CnfFormula.eval, List.all_eq_true] at hσ
  have hj : φ.clauses.get j ∈ φ.clauses := List.get_mem _ _
  have := hσ _ hj
  rw [clauseSat_iff] at this
  obtain ⟨l, hl, hlsat⟩ := this
  exact ⟨l, hl, (litSat_eq_true_iff σ l).mp hlsat⟩

variable {σ : Fin φ.numVars → Bool} (hσ : φ.eval σ = true)

/-- For a satisfying `σ`, each clause `j` has a satisfying literal; `chosenLit σ j` picks one
(its membership and satisfaction are `chosenLit_mem` / `chosenLit_sat`). -/
noncomputable def chosenLit (j : Fin φ.clauses.length) : Fin φ.numVars × Bool :=
  (exists_litSat_of_eval hσ j).choose

/-- The chosen literal of clause `j` occurs in clause `j`. -/
theorem chosenLit_mem (j : Fin φ.clauses.length) :
    chosenLit hσ j ∈ φ.clauses.get j :=
  (exists_litSat_of_eval hσ j).choose_spec.1

/-- The chosen literal of clause `j` is satisfied: `σ (chosenLit j).1 = (chosenLit j).2`. -/
theorem chosenLit_sat (j : Fin φ.clauses.length) :
    σ (chosenLit hσ j).1 = (chosenLit hσ j).2 :=
  (exists_litSat_of_eval hσ j).choose_spec.2

/-- The tip clause `j` consumes via its chosen literal: `litTip j (chosenLit j)`. -/
noncomputable def consumedTip (j : Fin φ.clauses.length) :
    PartY φ.numVars φ.clauses.length :=
  litTip j (chosenLit hσ j)

/-- `tipData` of the tip consumed by clause `j` reads `(chosenLit.var, chosenLit.sign, j)`. -/
theorem tipData_consumedTip (j : Fin φ.clauses.length) :
    tipData (consumedTip hσ j) = ((chosenLit hσ j).1, (chosenLit hσ j).2, j) := by
  simp only [consumedTip, litTip]
  rcases h : (chosenLit hσ j).2 with _ | _ <;> simp [posTip, negTip, tipData]

/-- The tip consumed by clause `j` is **free** under `σ` (the chosen literal is satisfied). -/
theorem isFreeTip_consumedTip (j : Fin φ.clauses.length) :
    IsFreeTip σ (consumedTip hσ j) := by
  unfold IsFreeTip
  rw [tipData_consumedTip hσ j]
  exact chosenLit_sat hσ j

/-- The ring-index of a consumed tip is the clause index: `(tipData (consumedTip j)).2.2 = j`.
Hence different clauses consume tips with different ring indices — the consumed tips are
distinct. -/
theorem consumedTip_injective : Function.Injective (consumedTip hσ) := by
  intro a b hab
  have ha := tipData_consumedTip hσ a
  have hb := tipData_consumedTip hσ b
  rw [hab, hb] at ha
  exact ((Prod.ext_iff.mp ha).2.symm |> Prod.ext_iff.mp).2

/-! ### Counting the free tips
Exactly one of `posTip i j`, `negTip i j` is free per index `(i, j)`, so there are `nm` free
tips. The witness is the bijection `(i, j) ↦ freeTipOf σ i j` (the satisfying-orientation tip).
-/

/-- The free tip at index `(i, j)`: `posTip i j` if `σ i = true`, else `negTip i j`. -/
def freeTipOf {n m : ℕ} (σ : Fin n → Bool) (i : Fin n) (j : Fin m) : PartY n m :=
  if σ i then posTip i j else negTip i j

/-- `freeTipOf σ i j` is indeed free. -/
theorem isFreeTip_freeTipOf {n m : ℕ} (σ : Fin n → Bool) (i : Fin n) (j : Fin m) :
    IsFreeTip σ (freeTipOf σ i j) := by
  unfold IsFreeTip freeTipOf
  rcases h : σ i with _ | _ <;> simp [h, posTip, negTip, tipData]

/-- Every free tip is `freeTipOf σ i j` for its own index — the free tips are exactly the
range of `freeTipOf`. -/
theorem eq_freeTipOf_of_isFreeTip {n m : ℕ} (σ : Fin n → Bool) {t : PartY n m}
    (ht : IsFreeTip σ t) : t = freeTipOf σ (tipData t).1 (tipData t).2.2 := by
  unfold IsFreeTip at ht
  rcases t with ⟨i, j⟩ | ⟨i, j⟩ <;>
    simp only [tipData] at ht ⊢ <;>
    simp [freeTipOf, ht, posTip, negTip]

/-- `freeTipOf σ` is injective on index pairs. -/
theorem freeTipOf_injective {n m : ℕ} (σ : Fin n → Bool) :
    Function.Injective (fun p : Fin n × Fin m => freeTipOf σ p.1 p.2) := by
  intro ⟨i, j⟩ ⟨i', j'⟩ hab
  simp only [freeTipOf] at hab
  rcases hi : σ i with _ | _ <;> rcases hi' : σ i' with _ | _ <;>
    simp_all [posTip, negTip]

/-- The Finset of free tips under `σ`. -/
def freeTips (n m : ℕ) (σ : Fin n → Bool) : Finset (PartY n m) :=
  Finset.univ.filter (IsFreeTip σ)

/-- The free tips are exactly the image of `freeTipOf` over all index pairs. -/
theorem freeTips_eq_image (n m : ℕ) (σ : Fin n → Bool) :
    freeTips n m σ = Finset.univ.image (fun p : Fin n × Fin m => freeTipOf σ p.1 p.2) := by
  ext t
  simp only [freeTips, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro ht
    exact ⟨((tipData t).1, (tipData t).2.2), (eq_freeTipOf_of_isFreeTip σ ht).symm⟩
  · rintro ⟨⟨i, j⟩, rfl⟩
    exact isFreeTip_freeTipOf σ i j

/-- There are exactly `nm` free tips. -/
theorem card_freeTips (n m : ℕ) (σ : Fin n → Bool) :
    (freeTips n m σ).card = n * m := by
  rw [freeTips_eq_image, Finset.card_image_of_injective _ (freeTipOf_injective σ),
    Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

/-- The Finset of tips consumed by the clauses (`consumedTip` over all clause indices). -/
noncomputable def consumedTips : Finset (PartY φ.numVars φ.clauses.length) :=
  Finset.univ.image (consumedTip hσ)

/-- Every consumed tip is free. -/
theorem consumedTips_subset_freeTips :
    consumedTips hσ ⊆ freeTips φ.numVars φ.clauses.length σ := by
  intro t ht
  simp only [consumedTips, Finset.mem_image, Finset.mem_univ, true_and] at ht
  obtain ⟨j, rfl⟩ := ht
  simp only [freeTips, Finset.mem_filter, Finset.mem_univ, true_and]
  exact isFreeTip_consumedTip hσ j

/-- There are exactly `m` consumed tips (the `consumedTip` map is injective). -/
theorem card_consumedTips : (consumedTips hσ).card = φ.clauses.length := by
  rw [consumedTips, Finset.card_image_of_injective _ (consumedTip_injective hσ),
    Finset.card_univ, Fintype.card_fin]

/-- The **leftover tips**: free tips not consumed by any clause. -/
noncomputable def leftoverTips : Finset (PartY φ.numVars φ.clauses.length) :=
  freeTips φ.numVars φ.clauses.length σ \ consumedTips hσ

/-- There are exactly `(n-1)·m` leftover tips, matching the garbage-index count. -/
theorem card_leftoverTips :
    (leftoverTips hσ).card = (φ.numVars - 1) * φ.clauses.length := by
  rw [leftoverTips, Finset.card_sdiff_of_subset (consumedTips_subset_freeTips hσ),
    card_freeTips, card_consumedTips, Nat.sub_one_mul]

/-! ### The garbage-tip bijection
The `(n-1)m` garbage indices are matched bijectively to the `(n-1)m` leftover tips via
`garbAssign`. -/

/-- A bijection `Fin ((n-1)·m) ≃ {leftover tips}` (cards agree, `card_leftoverTips`). -/
noncomputable def leftoverEquiv :
    Fin ((φ.numVars - 1) * φ.clauses.length) ≃ {t // t ∈ leftoverTips hσ} :=
  (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, card_leftoverTips])).symm

/-- The garbage tip assigned to garbage index `k`: a leftover tip, the `k`-th under
`leftoverEquiv`. -/
noncomputable def garbAssign (k : Fin ((φ.numVars - 1) * φ.clauses.length)) :
    PartY φ.numVars φ.clauses.length :=
  (leftoverEquiv hσ k).val

/-- `garbAssign` lands in the leftover tips. -/
theorem garbAssign_mem (k : Fin ((φ.numVars - 1) * φ.clauses.length)) :
    garbAssign hσ k ∈ leftoverTips hσ :=
  (leftoverEquiv hσ k).property

/-- `garbAssign` is injective. -/
theorem garbAssign_injective : Function.Injective (garbAssign hσ) := by
  intro a b hab
  exact (leftoverEquiv hσ).injective (Subtype.ext hab)

/-- `garbAssign` is surjective onto the leftover tips: every leftover tip is some
`garbAssign k`. -/
theorem exists_garbAssign_of_mem_leftoverTips {t : PartY φ.numVars φ.clauses.length}
    (ht : t ∈ leftoverTips hσ) : ∃ k, garbAssign hσ k = t := by
  refine ⟨(leftoverEquiv hσ).symm ⟨t, ht⟩, ?_⟩
  simp [garbAssign]

/-! ### The matching `N`
The perfect matching `N` for a satisfying `σ`: per-variable ring orientation, one clause
triple per clause, one garbage triple per garbage index. -/

/-- The ring triple selected for variable `i`, ring index `j`: `trueTriple` if `σ i = true`,
else `falseTriple`. -/
def ringTripleOf {n m : ℕ} (σ : Fin n → Bool) (i : Fin n) (j : Fin m) : Triple n m :=
  if σ i then trueTriple i j else falseTriple i j

/-- The selected ring triples. -/
def ringMatch (n m : ℕ) (σ : Fin n → Bool) : Finset (Triple n m) :=
  Finset.univ.image (fun p : Fin n × Fin m => ringTripleOf σ p.1 p.2)

/-- The selected clause triples (one per clause, via its chosen satisfying literal). -/
noncomputable def clauseMatch : Finset (Triple φ.numVars φ.clauses.length) :=
  Finset.univ.image (fun j : Fin φ.clauses.length => clauseTriple j (chosenLit hσ j))

/-- The selected garbage triples (one per garbage index, via `garbAssign`). -/
noncomputable def garbMatch : Finset (Triple φ.numVars φ.clauses.length) :=
  Finset.univ.image
    (fun k : Fin ((φ.numVars - 1) * φ.clauses.length) => garbTriple k (garbAssign hσ k))

/-- The full matching `N`: ring ∪ clause ∪ garbage selected triples. -/
noncomputable def gadgetN : Finset (Triple φ.numVars φ.clauses.length) :=
  ringMatch φ.numVars φ.clauses.length σ ∪ clauseMatch hσ ∪ garbMatch hσ

/-! ### `N ⊆ M` -/

/-- `trueTriple i j` is in the gadget family `M`. -/
theorem trueTriple_mem_gadgetM (i : Fin φ.numVars) (j : Fin φ.clauses.length) :
    trueTriple i j ∈ gadgetM φ := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, j)))

/-- `falseTriple i j` is in the gadget family `M`. -/
theorem falseTriple_mem_gadgetM (i : Fin φ.numVars) (j : Fin φ.clauses.length) :
    falseTriple i j ∈ gadgetM φ := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, j)))

/-- A clause triple for a literal `l` occurring in clause `j` is in `M`. -/
theorem clauseTriple_mem_gadgetM {j : Fin φ.clauses.length} {l : Fin φ.numVars × Bool}
    (hl : l ∈ φ.clauses.get j) : clauseTriple j l ∈ gadgetM φ := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  simp only [clauseTriples, Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact ⟨j, List.mem_toFinset.mpr (List.mem_map_of_mem hl)⟩

/-- A garbage triple `garbTriple k t` (any tip `t`) is in `M`. -/
theorem garbTriple_mem_gadgetM (k : Fin ((φ.numVars - 1) * φ.clauses.length))
    (t : PartY φ.numVars φ.clauses.length) : garbTriple k t ∈ gadgetM φ := by
  apply Finset.mem_union_right
  exact Finset.mem_image_of_mem _ (Finset.mem_univ (k, t))

/-! ### Structural description of `N`'s triples
A triple lies in `N` iff it is a selected ring triple, a selected clause triple, or a selected
garbage triple. -/

/-- Membership in `N` is one of the three selected-triple forms. -/
theorem mem_gadgetN_iff (t : Triple φ.numVars φ.clauses.length) :
    t ∈ gadgetN hσ ↔
      (∃ i j, t = ringTripleOf σ i j) ∨
      (∃ j, t = clauseTriple j (chosenLit hσ j)) ∨
      (∃ k, t = garbTriple k (garbAssign hσ k)) := by
  simp only [gadgetN, Finset.mem_union, ringMatch, clauseMatch, garbMatch, Finset.mem_image,
    Finset.mem_univ, true_and, Prod.exists]
  constructor
  · rintro ((⟨i, j, rfl⟩ | ⟨j, rfl⟩) | ⟨k, rfl⟩)
    · exact Or.inl ⟨i, j, rfl⟩
    · exact Or.inr (Or.inl ⟨j, rfl⟩)
    · exact Or.inr (Or.inr ⟨k, rfl⟩)
  · rintro (⟨i, j, rfl⟩ | ⟨j, rfl⟩ | ⟨k, rfl⟩)
    · exact Or.inl (Or.inl ⟨i, j, rfl⟩)
    · exact Or.inl (Or.inr ⟨j, rfl⟩)
    · exact Or.inr ⟨k, rfl⟩

/-! ### Ground membership reduces to a single component
A `W`-element `groundW w` lies in `tripleGround t` iff `w = t.1` (it cannot equal the `X`/`Y`
components); likewise for `X` and `Y`. These collapse the perfect-matching `∃!` to component
equalities. -/

/-- `groundW w ∈ tripleGround t ↔ w = t.1`. -/
theorem groundW_mem_tripleGround {n m : ℕ} (w : PartW n m) (t : Triple n m) :
    (groundW w : ThreeDMGround _ _ _) ∈ tripleGround t ↔ w = t.1 := by
  simp only [tripleGround, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h | h)
    · exact (Sum.inl.injEq w t.1).mp h
    · exact absurd h (groundW_ne_groundX _ _)
    · exact absurd h (groundW_ne_groundY _ _)
  · rintro rfl; left; rfl

/-- `groundX x ∈ tripleGround t ↔ x = t.2.1`. -/
theorem groundX_mem_tripleGround {n m : ℕ} (x : PartX n m) (t : Triple n m) :
    (groundX x : ThreeDMGround _ _ _) ∈ tripleGround t ↔ x = t.2.1 := by
  simp only [tripleGround, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h | h)
    · exact absurd h.symm (groundW_ne_groundX _ _)
    · exact Sum.inl_injective (Sum.inr_injective h)
    · exact absurd h (groundX_ne_groundY _ _)
  · rintro rfl; right; left; rfl

/-- `groundY y ∈ tripleGround t ↔ y = t.2.2`. -/
theorem groundY_mem_tripleGround {n m : ℕ} (y : PartY n m) (t : Triple n m) :
    (groundY y : ThreeDMGround _ _ _) ∈ tripleGround t ↔ y = t.2.2 := by
  simp only [tripleGround, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h | h)
    · exact absurd h.symm (groundW_ne_groundY _ _)
    · exact absurd h.symm (groundX_ne_groundY _ _)
    · exact Sum.inr_injective (Sum.inr_injective h)
  · rintro rfl; right; right; rfl

/-! ### The selected triples lie in `N` -/

/-- The selected ring triple is in `N`. -/
theorem ringTripleOf_mem_gadgetN (i : Fin φ.numVars) (j : Fin φ.clauses.length) :
    ringTripleOf σ i j ∈ gadgetN hσ :=
  (mem_gadgetN_iff hσ _).mpr (Or.inl ⟨i, j, rfl⟩)

/-- The selected clause triple is in `N`. -/
theorem clauseTriple_chosen_mem_gadgetN (j : Fin φ.clauses.length) :
    clauseTriple j (chosenLit hσ j) ∈ gadgetN hσ :=
  (mem_gadgetN_iff hσ _).mpr (Or.inr (Or.inl ⟨j, rfl⟩))

/-- The selected garbage triple is in `N`. -/
theorem garbTriple_assign_mem_gadgetN (k : Fin ((φ.numVars - 1) * φ.clauses.length)) :
    garbTriple k (garbAssign hσ k) ∈ gadgetN hσ :=
  (mem_gadgetN_iff hσ _).mpr (Or.inr (Or.inr ⟨k, rfl⟩))

/-! ### The three components are injective on `N`
The `W`-, `X`-, and `Y`-components of the selected triples are pairwise distinct across `N`, so
any shared ground element forces equality of the triples (the perfect-matching uniqueness). -/

/-- X-component of a selected triple: `bCore i j` (ring), `clauseX j` (clause), `garbX k`
(garbage). -/
theorem snd_fst_ringTripleOf (i : Fin φ.numVars) (j : Fin φ.clauses.length) :
    (ringTripleOf σ i j).2.1 = bCore i j := by
  unfold ringTripleOf; split <;> rfl

/-- W-component of a selected ring triple: `aCore i j` (true) or `aCore i (ringSucc j)`
(false). -/
theorem fst_ringTripleOf (i : Fin φ.numVars) (j : Fin φ.clauses.length) :
    (ringTripleOf σ i j).1 = if σ i then aCore i j else aCore i (ringSucc j) := by
  unfold ringTripleOf; split <;> rfl

/-- The W-component is injective on `N`. -/
theorem gadgetN_fst_inj {t t' : Triple φ.numVars φ.clauses.length}
    (ht : t ∈ gadgetN hσ) (ht' : t' ∈ gadgetN hσ) (h : t.1 = t'.1) : t = t' := by
  rw [mem_gadgetN_iff] at ht ht'
  rcases ht with ⟨i, j, rfl⟩ | ⟨j, rfl⟩ | ⟨k, rfl⟩ <;>
    rcases ht' with ⟨i', j', rfl⟩ | ⟨j', rfl⟩ | ⟨k', rfl⟩ <;>
    simp only [fst_ringTripleOf, clauseTriple, garbTriple, aCore, clauseW, garbW] at h
  · -- ring/ring: same variable ⇒ same orientation ⇒ same ring index
    rcases hi : σ i with _ | _ <;> rcases hi' : σ i' with _ | _ <;>
      simp only [hi, hi', Bool.false_eq_true, if_true, if_false,
        Sum.inl.injEq, Prod.mk.injEq] at h
    -- false.false
    · obtain ⟨rfl, hj⟩ := h
      have := ringSucc_bijective.injective hj
      subst this; simp [ringTripleOf, hi]
    -- false.true
    · obtain ⟨rfl, _⟩ := h; rw [hi'] at hi; exact absurd hi (by simp)
    -- true.false
    · obtain ⟨rfl, _⟩ := h; rw [hi'] at hi; exact absurd hi (by simp)
    -- true.true
    · obtain ⟨rfl, rfl⟩ := h; simp [ringTripleOf, hi]
  -- cross-kind and same-kind clause/garb cases
  · split at h <;> simp at h
  · split at h <;> simp at h
  · split at h <;> simp at h
  · obtain rfl := Sum.inl_injective (Sum.inr_injective h); rfl
  · rcases h
  · split at h <;> simp at h
  · rcases h
  · obtain rfl := Sum.inr_injective (Sum.inr_injective h); rfl

/-- Y-component of a selected ring triple: `negTip i j` (true) or `posTip i j` (false). -/
theorem snd_snd_ringTripleOf (i : Fin φ.numVars) (j : Fin φ.clauses.length) :
    (ringTripleOf σ i j).2.2 = if σ i then negTip i j else posTip i j := by
  unfold ringTripleOf; split <;> rfl

/-- A ring triple's Y-component (`negTip` for a true variable, `posTip` for a false one) is the
*covered* tip, hence **not free** — the truth-setting covers the opposite orientation. -/
theorem not_isFreeTip_snd_snd_ringTripleOf (i : Fin φ.numVars) (j : Fin φ.clauses.length) :
    ¬ IsFreeTip σ (ringTripleOf σ i j).2.2 := by
  rw [snd_snd_ringTripleOf]
  unfold IsFreeTip
  rcases hi : σ i with _ | _ <;> simp [hi, posTip, negTip, tipData]

/-- A clause triple's Y-component is the consumed tip (free). -/
theorem snd_snd_clauseTriple_chosen (j : Fin φ.clauses.length) :
    (clauseTriple j (chosenLit hσ j)).2.2 = consumedTip hσ j := rfl

/-- A garbage triple's Y-component is the assigned leftover tip (free). -/
theorem snd_snd_garbTriple (k : Fin ((φ.numVars - 1) * φ.clauses.length)) :
    (garbTriple k (garbAssign hσ k)).2.2 = garbAssign hσ k := rfl

/-- A consumed tip lies in `consumedTips`. -/
theorem consumedTip_mem_consumedTips (j : Fin φ.clauses.length) :
    consumedTip hσ j ∈ consumedTips hσ :=
  Finset.mem_image_of_mem _ (Finset.mem_univ j)

/-- A garbage-assigned tip is free. -/
theorem isFreeTip_garbAssign (k : Fin ((φ.numVars - 1) * φ.clauses.length)) :
    IsFreeTip σ (garbAssign hσ k) :=
  (Finset.mem_filter.mp (Finset.mem_sdiff.mp (garbAssign_mem hσ k)).1).2

/-- A garbage-assigned tip is not consumed by any clause. -/
theorem garbAssign_not_mem_consumedTips (k : Fin ((φ.numVars - 1) * φ.clauses.length)) :
    garbAssign hσ k ∉ consumedTips hσ :=
  (Finset.mem_sdiff.mp (garbAssign_mem hσ k)).2

/-- The Y-component is injective on `N`. -/
theorem gadgetN_snd_snd_inj {t t' : Triple φ.numVars φ.clauses.length}
    (ht : t ∈ gadgetN hσ) (ht' : t' ∈ gadgetN hσ) (h : t.2.2 = t'.2.2) : t = t' := by
  rw [mem_gadgetN_iff] at ht ht'
  rcases ht with ⟨i, j, rfl⟩ | ⟨j, rfl⟩ | ⟨k, rfl⟩ <;>
    rcases ht' with ⟨i', j', rfl⟩ | ⟨j', rfl⟩ | ⟨k', rfl⟩
  -- ring/ring
  · rw [snd_snd_ringTripleOf, snd_snd_ringTripleOf] at h
    rcases hi : σ i with _ | _ <;> rcases hi' : σ i' with _ | _ <;>
      simp only [hi, hi', Bool.false_eq_true, if_true, if_false, posTip, negTip,
        Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, Prod.mk.injEq] at h <;>
      (obtain ⟨rfl, rfl⟩ := h; simp [ringTripleOf, hi])
  -- ring/clause: ring Y not free, clause Y free
  · refine absurd ?_ (not_isFreeTip_snd_snd_ringTripleOf (σ := σ) i j)
    rw [h, snd_snd_clauseTriple_chosen]; exact isFreeTip_consumedTip hσ j'
  -- ring/garb: ring Y not free, garb Y free
  · refine absurd ?_ (not_isFreeTip_snd_snd_ringTripleOf (σ := σ) i j)
    rw [h, snd_snd_garbTriple]; exact isFreeTip_garbAssign hσ k'
  -- clause/ring
  · refine absurd ?_ (not_isFreeTip_snd_snd_ringTripleOf (σ := σ) i' j')
    rw [← h, snd_snd_clauseTriple_chosen]; exact isFreeTip_consumedTip hσ j
  -- clause/clause
  · rw [snd_snd_clauseTriple_chosen, snd_snd_clauseTriple_chosen] at h
    obtain rfl := consumedTip_injective hσ h; rfl
  -- clause/garb
  · exfalso
    rw [snd_snd_clauseTriple_chosen, snd_snd_garbTriple] at h
    exact garbAssign_not_mem_consumedTips hσ k' (h ▸ consumedTip_mem_consumedTips hσ j)
  -- garb/ring
  · refine absurd ?_ (not_isFreeTip_snd_snd_ringTripleOf (σ := σ) i' j')
    rw [← h, snd_snd_garbTriple]; exact isFreeTip_garbAssign hσ k
  -- garb/clause
  · exfalso
    rw [snd_snd_garbTriple, snd_snd_clauseTriple_chosen] at h
    exact garbAssign_not_mem_consumedTips hσ k (h ▸ consumedTip_mem_consumedTips hσ j')
  -- garb/garb
  · rw [snd_snd_garbTriple, snd_snd_garbTriple] at h
    obtain rfl := garbAssign_injective hσ h; rfl

/-- The X-component is injective on `N`: equal X-components of two selected triples force the
triples equal. -/
theorem gadgetN_snd_fst_inj {t t' : Triple φ.numVars φ.clauses.length}
    (ht : t ∈ gadgetN hσ) (ht' : t' ∈ gadgetN hσ) (h : t.2.1 = t'.2.1) : t = t' := by
  rw [mem_gadgetN_iff] at ht ht'
  rcases ht with ⟨i, j, rfl⟩ | ⟨j, rfl⟩ | ⟨k, rfl⟩ <;>
    rcases ht' with ⟨i', j', rfl⟩ | ⟨j', rfl⟩ | ⟨k', rfl⟩ <;>
    simp only [snd_fst_ringTripleOf, clauseTriple, garbTriple, bCore, clauseX, garbX,
      Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq] at h <;>
    first
      | (obtain ⟨rfl, rfl⟩ := h; rfl)
      | (rcases h)

/-! ### Coverage: every ground element is in some `N`-triple
Each `W`/`X`/`Y` ground element is covered by exactly one selected triple — `aCore`/`bCore`/
non-free tips by ring triples (using the `ringSucc`-predecessor for false-oriented `a`-cores),
clause elements by clause triples, garbage elements by garbage triples, free tips by the clause
that consumes them or the garbage index that absorbs them. -/

/-- Coverage: every ground element `e : PartW ⊕ PartX ⊕ PartY` lies in the ground set of some
selected triple of `N`. -/
theorem gadgetN_covers
    (e : ThreeDMGround (PartW φ.numVars φ.clauses.length) (PartX φ.numVars φ.clauses.length)
      (PartY φ.numVars φ.clauses.length)) :
    ∃ t ∈ gadgetN hσ, e ∈ tripleGround t := by
  rcases e with w | x | t
  · -- W element
    show ∃ t ∈ gadgetN hσ, (groundW w : ThreeDMGround _ _ _) ∈ tripleGround t
    rcases w with ⟨i, j⟩ | j | k
    · -- aCore i j
      rcases hi : σ i with _ | _
      · -- false: covered by ring triple at the ringSucc-predecessor of j
        obtain ⟨j', rfl⟩ := exists_ringSucc_eq j
        refine ⟨ringTripleOf σ i j', ringTripleOf_mem_gadgetN hσ i j', ?_⟩
        rw [groundW_mem_tripleGround, fst_ringTripleOf, hi]; rfl
      · -- true: covered by ring triple at j
        refine ⟨ringTripleOf σ i j, ringTripleOf_mem_gadgetN hσ i j, ?_⟩
        rw [groundW_mem_tripleGround, fst_ringTripleOf, hi]; rfl
    · -- clauseW j
      refine ⟨clauseTriple j (chosenLit hσ j), clauseTriple_chosen_mem_gadgetN hσ j, ?_⟩
      rw [groundW_mem_tripleGround]; rfl
    · -- garbW k
      refine ⟨garbTriple k (garbAssign hσ k), garbTriple_assign_mem_gadgetN hσ k, ?_⟩
      rw [groundW_mem_tripleGround]; rfl
  · -- X element
    show ∃ t ∈ gadgetN hσ, (groundX x : ThreeDMGround _ _ _) ∈ tripleGround t
    rcases x with ⟨i, j⟩ | j | k
    · -- bCore i j
      refine ⟨ringTripleOf σ i j, ringTripleOf_mem_gadgetN hσ i j, ?_⟩
      rw [groundX_mem_tripleGround, snd_fst_ringTripleOf]; rfl
    · -- clauseX j
      refine ⟨clauseTriple j (chosenLit hσ j), clauseTriple_chosen_mem_gadgetN hσ j, ?_⟩
      rw [groundX_mem_tripleGround]; rfl
    · -- garbX k
      refine ⟨garbTriple k (garbAssign hσ k), garbTriple_assign_mem_gadgetN hσ k, ?_⟩
      rw [groundX_mem_tripleGround]; rfl
  · -- Y element (tip)
    show ∃ tr ∈ gadgetN hσ, (groundY t : ThreeDMGround _ _ _) ∈ tripleGround tr
    by_cases hf : IsFreeTip σ t
    · -- free tip: consumed by a clause or leftover (garbage)
      by_cases hc : t ∈ consumedTips hσ
      · -- consumed: t = consumedTip j for some clause j
        simp only [consumedTips, Finset.mem_image, Finset.mem_univ, true_and] at hc
        obtain ⟨j, rfl⟩ := hc
        refine ⟨clauseTriple j (chosenLit hσ j), clauseTriple_chosen_mem_gadgetN hσ j, ?_⟩
        rw [groundY_mem_tripleGround, snd_snd_clauseTriple_chosen]
      · -- leftover: t ∈ leftoverTips ⇒ t = garbAssign k for some k
        have ht : t ∈ leftoverTips hσ :=
          Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩, hc⟩
        obtain ⟨k, rfl⟩ := exists_garbAssign_of_mem_leftoverTips hσ ht
        refine ⟨garbTriple k (garbAssign hσ k), garbTriple_assign_mem_gadgetN hσ k, ?_⟩
        rw [groundY_mem_tripleGround]; rfl
    · -- non-free tip: covered by its ring triple
      -- `t` is `negTip i j` with `σ i = true` or `posTip i j` with `σ i = false`
      rcases t with ⟨i, j⟩ | ⟨i, j⟩
      · -- posTip i j: free iff σ i = true; not free ⇒ σ i = false
        have hi : σ i = false := by
          unfold IsFreeTip at hf
          rcases h : σ i with _ | _ <;> simp_all [tipData]
        refine ⟨ringTripleOf σ i j, ringTripleOf_mem_gadgetN hσ i j, ?_⟩
        rw [groundY_mem_tripleGround, snd_snd_ringTripleOf, hi]; rfl
      · -- negTip i j: free iff σ i = false; not free ⇒ σ i = true
        have hi : σ i = true := by
          unfold IsFreeTip at hf
          rcases h : σ i with _ | _ <;> simp_all [tipData]
        refine ⟨ringTripleOf σ i j, ringTripleOf_mem_gadgetN hσ i j, ?_⟩
        rw [groundY_mem_tripleGround, snd_snd_ringTripleOf, hi]; rfl

/-- The matching `N` is a sub-family of `M`. -/
theorem gadgetN_subset_gadgetM : gadgetN hσ ⊆ gadgetM φ := by
  intro t ht
  simp only [gadgetN, Finset.mem_union] at ht
  rcases ht with (ht | ht) | ht
  · simp only [ringMatch, Finset.mem_image, Finset.mem_univ, true_and] at ht
    obtain ⟨⟨i, j⟩, rfl⟩ := ht
    unfold ringTripleOf
    split
    · exact trueTriple_mem_gadgetM i j
    · exact falseTriple_mem_gadgetM i j
  · simp only [clauseMatch, Finset.mem_image, Finset.mem_univ, true_and] at ht
    obtain ⟨j, rfl⟩ := ht
    exact clauseTriple_mem_gadgetM (chosenLit_mem hσ j)
  · simp only [garbMatch, Finset.mem_image, Finset.mem_univ, true_and] at ht
    obtain ⟨k, rfl⟩ := ht
    exact garbTriple_mem_gadgetM k (garbAssign hσ k)

/-! ### Uniqueness and the perfect matching
Coverage + the three component injectivities give: each ground element lies in a *unique*
selected triple. -/

/-- Two selected triples sharing a ground element are equal (perfect-matching uniqueness):
the shared element's `W`/`X`/`Y` kind pins a common component, and that component is injective
on `N`. -/
theorem gadgetN_unique {t t' : Triple φ.numVars φ.clauses.length}
    (ht : t ∈ gadgetN hσ) (ht' : t' ∈ gadgetN hσ)
    {e : ThreeDMGround (PartW φ.numVars φ.clauses.length) (PartX φ.numVars φ.clauses.length)
      (PartY φ.numVars φ.clauses.length)}
    (he : e ∈ tripleGround t) (he' : e ∈ tripleGround t') : t = t' := by
  rcases e with w | x | y
  · -- shared W element ⇒ equal W-components
    have h1 := (groundW_mem_tripleGround w t).mp he
    have h2 := (groundW_mem_tripleGround w t').mp he'
    exact gadgetN_fst_inj hσ ht ht' (h1 ▸ h2)
  · -- shared X element ⇒ equal X-components
    have h1 := (groundX_mem_tripleGround x t).mp he
    have h2 := (groundX_mem_tripleGround x t').mp he'
    exact gadgetN_snd_fst_inj hσ ht ht' (h1 ▸ h2)
  · -- shared Y element ⇒ equal Y-components
    have h1 := (groundY_mem_tripleGround y t).mp he
    have h2 := (groundY_mem_tripleGround y t').mp he'
    exact gadgetN_snd_snd_inj hσ ht ht' (h1 ▸ h2)

/-- **`N` is a perfect matching of the gadget instance**: `N ⊆ M` and every ground element lies
in a unique triple of `N`. -/
theorem isMatching_gadgetN (hn : 1 ≤ φ.numVars) :
    (gadgetInstance φ hn).IsMatching (gadgetN hσ) := by
  refine ⟨gadgetN_subset_gadgetM hσ, fun e => ?_⟩
  obtain ⟨t, htN, hte⟩ := gadgetN_covers hσ e
  exact ⟨t, ⟨htN, hte⟩, fun t' ⟨ht'N, ht'e⟩ => gadgetN_unique hσ ht'N htN ht'e hte⟩

/-- **Forward direction (gadget instance):** if `φ` is satisfiable and has at least one
variable, its gadget 3DM instance admits a perfect matching. The witness is `gadgetN` built
from the satisfying assignment (orient each ring, route each clause, garbage-collect). -/
theorem threeDMDecision_gadgetInstance_of_satisfiable (hn : 1 ≤ φ.numVars)
    (hsat : Satisfiable φ) : (gadgetInstance φ hn).threeDMDecision := by
  obtain ⟨σ, hσ⟩ := hsat
  exact ⟨gadgetN hσ, isMatching_gadgetN hσ hn⟩

end ThreeDM

/-! ## Reverse direction: reading an assignment off a perfect matching
This is the harder half of Garey-Johnson Thm 3.2. We characterize which `M`-triples can cover
each ground element, then read each variable's ring orientation and show the clause gadgets
force a satisfying assignment. The combinatorial heart is *ring consistency*: in a perfect
matching, a variable's ring is covered by all true-triples or all false-triples (the cyclic
chaining forbids a mixed orientation). -/

namespace ThreeDM

variable {φ : CnfFormula}

/-- Structural description of `M`'s triples: ring, clause, or garbage. -/
theorem mem_gadgetM_iff (t : Triple φ.numVars φ.clauses.length) :
    t ∈ gadgetM φ ↔
      (∃ i j, t = trueTriple i j) ∨ (∃ i j, t = falseTriple i j) ∨
      (∃ j l, l ∈ φ.clauses.get j ∧ t = clauseTriple j l) ∨
      (∃ k t', t = garbTriple k t') := by
  simp only [gadgetM, Finset.mem_union, ringTriples, clauseTriples, garbTriples,
    Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_biUnion, List.mem_toFinset,
    List.mem_map]
  constructor
  · rintro ((((⟨⟨i, j⟩, h⟩) | (⟨⟨i, j⟩, h⟩)) | ⟨j, ⟨l, hl, h⟩⟩) | ⟨⟨k, t'⟩, h⟩)
    · exact Or.inl ⟨i, j, h.symm⟩
    · exact Or.inr (Or.inl ⟨i, j, h.symm⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨j, l, hl, h.symm⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨k, t', h.symm⟩))
  · rintro (⟨i, j, rfl⟩ | ⟨i, j, rfl⟩ | ⟨j, l, hl, rfl⟩ | ⟨k, t', rfl⟩)
    · exact Or.inl (Or.inl (Or.inl ⟨(i, j), rfl⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨(i, j), rfl⟩))
    · exact Or.inl (Or.inr ⟨j, l, hl, rfl⟩)
    · exact Or.inr ⟨(k, t'), rfl⟩

/-- The only `M`-triples whose X-component is `bCore i j` are the two ring triples
`trueTriple i j` / `falseTriple i j`. -/
theorem eq_ringTriple_of_bCore_mem {t : Triple φ.numVars φ.clauses.length}
    (ht : t ∈ gadgetM φ) (i : Fin φ.numVars) (j : Fin φ.clauses.length)
    (he : (groundX (bCore i j) : ThreeDMGround _ _ _) ∈ tripleGround t) :
    t = trueTriple i j ∨ t = falseTriple i j := by
  rw [groundX_mem_tripleGround] at he
  rw [mem_gadgetM_iff] at ht
  rcases ht with ⟨i', j', rfl⟩ | ⟨i', j', rfl⟩ | ⟨j', l, _, rfl⟩ | ⟨k, t', rfl⟩
  · left; simp only [trueTriple, bCore, Sum.inl.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he; rfl
  · right; simp only [falseTriple, bCore, Sum.inl.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he; rfl
  · simp only [clauseTriple, bCore, clauseX, reduceCtorEq] at he
  · simp only [garbTriple, bCore, garbX, reduceCtorEq] at he

/-- The only `M`-triples whose W-component is `aCore i j` are `trueTriple i j` (covers it as its
own `a`-core) and `falseTriple i (ringPred j)` (covers it as the *next* `a`-core in the ring). -/
theorem eq_ringTriple_of_aCore_mem {t : Triple φ.numVars φ.clauses.length}
    (ht : t ∈ gadgetM φ) (i : Fin φ.numVars) (j : Fin φ.clauses.length)
    (he : (groundW (aCore i j) : ThreeDMGround _ _ _) ∈ tripleGround t) :
    t = trueTriple i j ∨ t = falseTriple i (ringPred j) := by
  rw [groundW_mem_tripleGround] at he
  rw [mem_gadgetM_iff] at ht
  rcases ht with ⟨i', j', rfl⟩ | ⟨i', j', rfl⟩ | ⟨j', l, _, rfl⟩ | ⟨k, t', rfl⟩
  · left; simp only [trueTriple, aCore, Sum.inl.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he; rfl
  · right; simp only [falseTriple, aCore, Sum.inl.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, hj⟩ := he
    -- j = ringSucc j' ⇒ j' = ringPred j
    have : j' = ringPred j := by rw [hj, ringPred_ringSucc]
    rw [this]
  · simp only [clauseTriple, aCore, clauseW, reduceCtorEq] at he
  · simp only [garbTriple, aCore, garbW, reduceCtorEq] at he

/-! ### Ring consistency
In a perfect matching, each `b`-core is covered by `trueTriple i j` or `falseTriple i j`, and
the `a`-cores then force *all* of variable `i`'s ring to share one orientation. -/

variable {hn : 1 ≤ φ.numVars} {N : Finset (PartW φ.numVars φ.clauses.length ×
    PartX φ.numVars φ.clauses.length × PartY φ.numVars φ.clauses.length)}

/-- A ground element of the gadget instance, as the raw `Sum` type. -/
private abbrev G (φ : CnfFormula) : Type :=
  ThreeDMGround (PartW φ.numVars φ.clauses.length) (PartX φ.numVars φ.clauses.length)
    (PartY φ.numVars φ.clauses.length)

/-- In a perfect matching `N`, the unique triple covering `bCore i j` is `trueTriple i j` or
`falseTriple i j`; hence `trueTriple i j ∈ N ∨ falseTriple i j ∈ N`. -/
theorem trueTriple_or_falseTriple_mem (hM : (gadgetInstance φ hn).IsMatching N)
    (i : Fin φ.numVars) (j : Fin φ.clauses.length) :
    trueTriple i j ∈ N ∨ falseTriple i j ∈ N := by
  obtain ⟨hsub, hcov⟩ := hM
  obtain ⟨t, ⟨htN, hte⟩, _⟩ := hcov (groundX (bCore i j))
  rcases eq_ringTriple_of_bCore_mem (hsub htN) i j hte with rfl | rfl
  · exact Or.inl htN
  · exact Or.inr htN

/-- A true-triple and a false-triple are always distinct (their Y-components are a `negTip` vs a
`posTip`, opposite `Sum` sides), regardless of indices. -/
theorem trueTriple_ne_falseTriple {n m : ℕ} (i : Fin n) (j : Fin m) (i' : Fin n) (j' : Fin m) :
    trueTriple i j ≠ falseTriple i' j' := by
  intro h
  have : negTip i j = posTip i' j' := congrArg (fun t => t.2.2) h
  simp only [negTip, posTip, reduceCtorEq] at this

/-- In a matching, `trueTriple i j` and `falseTriple i j` are not both selected (they would
both cover `bCore i j`, violating uniqueness). -/
theorem not_trueTriple_and_falseTriple_mem (hM : (gadgetInstance φ hn).IsMatching N)
    (i : Fin φ.numVars) (j : Fin φ.clauses.length) :
    ¬ (trueTriple i j ∈ N ∧ falseTriple i j ∈ N) := by
  rintro ⟨htT, htF⟩
  obtain ⟨_, hcov⟩ := hM
  obtain ⟨t, _, huniq⟩ := hcov (groundX (bCore i j))
  have e1 := huniq (trueTriple i j) ⟨htT, (groundX_mem_tripleGround _ _).mpr rfl⟩
  have e2 := huniq (falseTriple i j) ⟨htF, (groundX_mem_tripleGround _ _).mpr rfl⟩
  exact trueTriple_ne_falseTriple i j i j (e1.trans e2.symm)

/-- **Forward ring propagation:** if `falseTriple i j` is selected, so is
`falseTriple i (ringSucc j)`. The shared `a`-core `aCore i (ringSucc j)` (covered by
`falseTriple i j`) forces the matching at the next index to also be false-oriented. -/
theorem falseTriple_mem_ringSucc_of (hM : (gadgetInstance φ hn).IsMatching N)
    (i : Fin φ.numVars) (j : Fin φ.clauses.length) (hjF : falseTriple i j ∈ N) :
    falseTriple i (ringSucc j) ∈ N := by
  -- `aCore i (ringSucc j)` is covered by `falseTriple i j` (its W-component)
  obtain ⟨t, _, huniq⟩ := hM.2 (groundW (aCore i (ringSucc j)))
  -- the covering triple is `trueTriple i (ringSucc j)` or `falseTriple i (ringPred (ringSucc j))`
  have hcov_eq : t = falseTriple i j :=
    (huniq (falseTriple i j) ⟨hjF, (groundW_mem_tripleGround _ _).mpr rfl⟩).symm
  -- now rule out `trueTriple i (ringSucc j)` being selected
  rcases trueTriple_or_falseTriple_mem hM i (ringSucc j) with hT | hF
  · exfalso
    have heq := huniq (trueTriple i (ringSucc j))
      ⟨hT, (groundW_mem_tripleGround _ _).mpr rfl⟩
    rw [hcov_eq] at heq
    exact trueTriple_ne_falseTriple i (ringSucc j) i j heq
  · exact hF

/-- Iterating forward propagation: `falseTriple i j ∈ N → falseTriple i (ringSucc^[d] j) ∈ N`. -/
theorem falseTriple_mem_iterate_of (hM : (gadgetInstance φ hn).IsMatching N)
    (i : Fin φ.numVars) (j : Fin φ.clauses.length) (hjF : falseTriple i j ∈ N) (d : ℕ) :
    falseTriple i (ringSucc^[d] j) ∈ N := by
  induction d with
  | zero => simpa using hjF
  | succ d ih =>
    rw [Function.iterate_succ_apply']
    exact falseTriple_mem_ringSucc_of hM i _ ih

/-- **Ring consistency (false orientation):** if any of variable `i`'s `b`-cores is covered
false, *all* of them are — the false-triples chain around the whole ring. -/
theorem forall_falseTriple_mem_of_one (hM : (gadgetInstance φ hn).IsMatching N)
    (i : Fin φ.numVars) {j : Fin φ.clauses.length} (hjF : falseTriple i j ∈ N)
    (j' : Fin φ.clauses.length) : falseTriple i j' ∈ N := by
  obtain ⟨d, hd⟩ := exists_iterate_ringSucc j j'
  rw [← hd]
  exact falseTriple_mem_iterate_of hM i j hjF d

/-! ### Reading off the assignment
`readAssign N i` is `true` iff variable `i`'s ring is true-oriented (some — equivalently every
— true-triple of `i` is selected). The clause gadgets then force this assignment to satisfy
`φ`. -/

/-- The assignment read off a matching: variable `i` is `true` iff some true-triple of its ring
is selected. -/
noncomputable def readAssign (N : Finset (Triple φ.numVars φ.clauses.length))
    (i : Fin φ.numVars) : Bool :=
  open Classical in decide (∃ j, trueTriple i j ∈ N)

/-- `readAssign N i = true` iff some true-triple of `i`'s ring is selected. -/
theorem readAssign_eq_true_iff (N : Finset (Triple φ.numVars φ.clauses.length))
    (i : Fin φ.numVars) : readAssign N i = true ↔ ∃ j, trueTriple i j ∈ N := by
  classical rw [readAssign, decide_eq_true_iff]

/-- `readAssign N i = false` iff no true-triple of `i`'s ring is selected. -/
theorem readAssign_eq_false_iff (N : Finset (Triple φ.numVars φ.clauses.length))
    (i : Fin φ.numVars) : readAssign N i = false ↔ ∀ j, trueTriple i j ∉ N := by
  rw [Bool.eq_false_iff, ne_eq, readAssign_eq_true_iff, not_exists]

/-- If variable `i` is read `true`, every true-triple of its ring is selected (true-orientation
is consistent: any true index forbids the false chain). -/
theorem forall_trueTriple_mem_of_readAssign (hM : (gadgetInstance φ hn).IsMatching N)
    (i : Fin φ.numVars) (hi : readAssign N i = true) (j : Fin φ.clauses.length) :
    trueTriple i j ∈ N := by
  obtain ⟨j₀, hj₀⟩ := (readAssign_eq_true_iff N i).mp hi
  rcases trueTriple_or_falseTriple_mem hM i j with hT | hF
  · exact hT
  · -- false at j ⇒ false at j₀ ⇒ both T and F at j₀, contradiction
    exact absurd ⟨hj₀, forall_falseTriple_mem_of_one hM i hF j₀⟩
      (not_trueTriple_and_falseTriple_mem hM i j₀)

/-- If variable `i` is read `false`, every false-triple of its ring is selected. -/
theorem forall_falseTriple_mem_of_not_readAssign (hM : (gadgetInstance φ hn).IsMatching N)
    (i : Fin φ.numVars) (hi : readAssign N i = false) (j : Fin φ.clauses.length) :
    falseTriple i j ∈ N := by
  rw [readAssign_eq_false_iff] at hi
  rcases trueTriple_or_falseTriple_mem hM i j with hT | hF
  · exact absurd hT (hi j)
  · exact hF

/-! ### Clause gadgets force satisfaction -/

/-- `tipData (litTip j l) = (l.1, l.2, j)`. -/
theorem tipData_litTip (j : Fin φ.clauses.length) (l : Fin φ.numVars × Bool) :
    tipData (litTip j l) = (l.1, l.2, j) := by
  simp only [litTip]; rcases l with ⟨v, b⟩; cases b <;> simp [posTip, negTip, tipData]

/-- A tip `litTip j l` is free under `σ` iff the literal `l` is satisfied by `σ`. -/
theorem isFreeTip_litTip_iff (σ : Fin φ.numVars → Bool) (j : Fin φ.clauses.length)
    (l : Fin φ.numVars × Bool) : IsFreeTip σ (litTip j l) ↔ σ l.1 = l.2 := by
  rw [IsFreeTip, tipData_litTip]

/-- The only `M`-triples whose X-component is `clauseX j` are the clause triples
`clauseTriple j l` for literals `l` occurring in clause `j`. -/
theorem eq_clauseTriple_of_clauseX_mem {t : Triple φ.numVars φ.clauses.length}
    (ht : t ∈ gadgetM φ) (j : Fin φ.clauses.length)
    (he : (groundX (clauseX j) : ThreeDMGround _ _ _) ∈ tripleGround t) :
    ∃ l ∈ φ.clauses.get j, t = clauseTriple j l := by
  rw [groundX_mem_tripleGround] at he
  rw [mem_gadgetM_iff] at ht
  rcases ht with ⟨i', j', rfl⟩ | ⟨i', j', rfl⟩ | ⟨j', l, hl, rfl⟩ | ⟨k, t', rfl⟩
  · simp only [trueTriple, clauseX, bCore, reduceCtorEq] at he
  · simp only [falseTriple, clauseX, bCore, reduceCtorEq] at he
  · -- clauseTriple j' l: X-comp clauseX j' = clauseX j ⇒ j' = j
    simp only [clauseTriple, clauseX, Sum.inr.injEq, Sum.inl.injEq] at he
    subst he; exact ⟨l, hl, rfl⟩
  · simp only [garbTriple, clauseX, garbX, Sum.inr.injEq, reduceCtorEq] at he

/-- A tip that is **not free** under `readAssign N` is covered by its ring triple `ringTripleOf
(readAssign N) i j`, which is in `N` (the orientation matches the tip's side). -/
theorem ringTripleOf_mem_of_not_isFreeTip (hM : (gadgetInstance φ hn).IsMatching N)
    {t : PartY φ.numVars φ.clauses.length} (hnf : ¬ IsFreeTip (readAssign N) t) :
    ∃ i j, ringTripleOf (readAssign N) i j ∈ N ∧
      (groundY t : ThreeDMGround _ _ _) ∈ tripleGround (ringTripleOf (readAssign N) i j) := by
  rcases t with ⟨i, j⟩ | ⟨i, j⟩
  · -- posTip i j: not free ⇒ readAssign i = false ⇒ falseTriple i j ∈ N covers posTip i j
    have hi : readAssign N i = false := by
      by_contra h
      exact hnf (by rw [IsFreeTip]; simp only [tipData]; simpa using h)
    refine ⟨i, j, ?_, ?_⟩
    · rw [ringTripleOf, hi]; exact forall_falseTriple_mem_of_not_readAssign hM i hi j
    · refine (groundY_mem_tripleGround _ _).mpr ?_
      rw [snd_snd_ringTripleOf, hi]; rfl
  · -- negTip i j: not free ⇒ readAssign i = true ⇒ trueTriple i j ∈ N covers negTip i j
    have hi : readAssign N i = true := by
      by_contra h
      rw [Bool.not_eq_true] at h
      exact hnf (by rw [IsFreeTip]; simp only [tipData]; simpa using h)
    refine ⟨i, j, ?_, ?_⟩
    · rw [ringTripleOf, hi]; exact forall_trueTriple_mem_of_readAssign hM i hi j
    · refine (groundY_mem_tripleGround _ _).mpr ?_
      rw [snd_snd_ringTripleOf, hi]; rfl

/-- **Clause satisfaction:** in a matching, the clause gadget of clause `j` forces some literal
of clause `j` to be satisfied by `readAssign N`. -/
theorem clauseSat_readAssign (hM : (gadgetInstance φ hn).IsMatching N)
    (j : Fin φ.clauses.length) :
    CnfFormula.clauseSat (readAssign N) (φ.clauses.get j) = true := by
  -- the clause's X-element is covered by a clause triple `clauseTriple j l`, `l ∈ clause j`
  obtain ⟨t, ⟨htN, hte⟩, _⟩ := hM.2 (groundX (clauseX j))
  obtain ⟨l, hl, rfl⟩ := eq_clauseTriple_of_clauseX_mem (hM.1 htN) j hte
  -- the tip `litTip j l` is covered by this clause triple; uniqueness keyed to that tip
  obtain ⟨_, _, huniqY⟩ := hM.2 (groundY (litTip j l))
  -- the Y-tip `litTip j l` is free, else a ring triple would also cover it (uniqueness)
  have hfree : IsFreeTip (readAssign N) (litTip j l) := by
    by_contra hnf
    obtain ⟨i', j', htrN, htre⟩ := ringTripleOf_mem_of_not_isFreeTip hM hnf
    have hc : (groundY (litTip j l) : ThreeDMGround _ _ _) ∈ tripleGround (clauseTriple j l) :=
      (groundY_mem_tripleGround _ _).mpr rfl
    have e1 := huniqY (clauseTriple j l) ⟨htN, hc⟩
    have e2 := huniqY (ringTripleOf (readAssign N) i' j') ⟨htrN, htre⟩
    -- both equal the covering triple, so the clause triple equals a ring triple; compare X-comps
    have hxeq : (clauseTriple j l).2.1 = (ringTripleOf (readAssign N) i' j').2.1 := by
      rw [e1, e2]
    rw [snd_fst_ringTripleOf] at hxeq
    simp only [clauseTriple, clauseX, bCore, reduceCtorEq] at hxeq
  -- free tip ⇒ literal satisfied ⇒ clause satisfied
  rw [clauseSat_iff]
  exact ⟨l, hl, (litSat_eq_true_iff _ l).mpr ((isFreeTip_litTip_iff _ j l).mp hfree)⟩

/-- **`readAssign N` satisfies `φ`** when `N` is a perfect matching of the gadget instance:
every clause is satisfied by the clause-gadget argument. -/
theorem eval_readAssign (hM : (gadgetInstance φ hn).IsMatching N) :
    φ.eval (readAssign N) = true := by
  rw [CnfFormula.eval, List.all_eq_true]
  intro c hc
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hc
  exact clauseSat_readAssign hM j

/-- **Reverse direction (gadget instance):** if the gadget 3DM instance admits a perfect
matching, `φ` is satisfiable — read the assignment `readAssign N` off the matching's ring
orientations; the clause gadgets force it to satisfy `φ`. -/
theorem satisfiable_of_threeDMDecision_gadgetInstance (hn : 1 ≤ φ.numVars)
    (hD : (gadgetInstance φ hn).threeDMDecision) : Satisfiable φ := by
  obtain ⟨N, hM⟩ := hD
  exact ⟨readAssign N, eval_readAssign hM⟩

/-- **Bi-implication on the gadget regime** (`Is3Cnf φ`, `numVars ≥ 1`): `threeSat φ` iff the
gadget 3DM instance admits a perfect matching. The combinatorial heart of `3SAT ≤ₖ 3DM`. -/
theorem threeSat_iff_threeDMDecision_gadgetInstance (h3 : Is3Cnf φ) (hn : 1 ≤ φ.numVars) :
    threeSat φ ↔ (gadgetInstance φ hn).threeDMDecision := by
  rw [threeSat]
  constructor
  · rintro ⟨_, hsat⟩
    exact threeDMDecision_gadgetInstance_of_satisfiable hn hsat
  · intro hD
    exact ⟨h3, satisfiable_of_threeDMDecision_gadgetInstance hn hD⟩

/-! ### Trivial yes/no 3DM instances for the total map
Degenerate inputs (not 3-CNF, or no variables) are handled by mapping to a fixed instance with
a matching (`yesInstance`, the empty instance) or with none (`noInstance`, one uncovered
ground element), per whether the *decidable* `threeSat φ` holds — the standard total-map
convention (mirrors `threeDMToX3CMap`'s no-cover fallback). The genuine reduction content lives
entirely in the gadget regime above. -/

/-- The empty 3DM instance (`q = 0`): trivially admits the empty perfect matching. -/
def yesInstance : ThreeDMInstance where
  W := Empty
  X := Empty
  Y := Empty
  M := ∅
  q := 0
  card_W := by simp
  card_X := by simp
  card_Y := by simp

/-- `yesInstance` admits a matching (the empty matching: there are no ground elements). -/
theorem threeDMDecision_yesInstance : yesInstance.threeDMDecision := by
  refine ⟨∅, Finset.empty_subset _, fun e => ?_⟩
  rcases e with e | e | e <;> exact e.elim

/-- A 3DM instance with one uncovered ground element (`q = 1`, empty triple family): no
matching. -/
def noInstance : ThreeDMInstance where
  W := Unit
  X := Unit
  Y := Unit
  M := ∅
  q := 1
  card_W := by simp
  card_X := by simp
  card_Y := by simp

/-- `noInstance` has no matching: the (unique) ground element lies in no triple of any
sub-family of the empty `M`. -/
theorem not_threeDMDecision_noInstance : ¬ noInstance.threeDMDecision := by
  rintro ⟨N, hsub, hcov⟩
  obtain ⟨t, ⟨htN, _⟩, _⟩ := hcov (groundW ())
  have hmem : t ∈ noInstance.M := hsub htN
  rw [show noInstance.M = ∅ from rfl] at hmem
  simp at hmem

/-! ### Polynomial size bound for the gadget
The gadget instance has `|M| ≤ 2nm + (literal occurrences) + 2(n-1)nm²` triples and three
`2nm`-element parts, so `size ≤ 2nm + L + 2n²m² + 6nm`, polynomial in `n`, `m`, `L`. We bound
it by a polynomial in `CnfFormula.size φ = n + L` (which dominates `n`, `m ≤ L`... up to the
clause-count `m`; we also use `m ≤ size + 1`). -/

/-- Every clause triple has the form `(clauseW j, clauseX j, tip)`, so `clauseTriples` is a
subset of the `m × |PartY|` such triples. -/
theorem clauseTriples_subset :
    clauseTriples φ ⊆ Finset.univ.image
      (fun p : Fin φ.clauses.length × PartY φ.numVars φ.clauses.length =>
        ((clauseW p.1, clauseX p.1, p.2) : Triple φ.numVars φ.clauses.length)) := by
  intro t ht
  simp only [clauseTriples, Finset.mem_biUnion, Finset.mem_univ, true_and, List.mem_toFinset,
    List.mem_map] at ht
  obtain ⟨j, l, _, rfl⟩ := ht
  exact Finset.mem_image_of_mem _ (Finset.mem_univ (j, litTip j l))

/-- `|gadgetM| ≤ 2nm + 2nm² + 2(n-1)·n·m²`: a crude polynomial bound on the triple count via
the ring, clause, and garbage families. -/
theorem gadgetM_card_le :
    (gadgetM φ).card ≤ 2 * (φ.numVars * φ.clauses.length) +
      φ.clauses.length * (2 * φ.numVars * φ.clauses.length) +
      ((φ.numVars - 1) * φ.clauses.length) * (2 * φ.numVars * φ.clauses.length) := by
  have hring : (ringTriples φ.numVars φ.clauses.length).card ≤
      2 * (φ.numVars * φ.clauses.length) := by
    refine (Finset.card_union_le _ _).trans ?_
    have h1 : ∀ f : Fin φ.numVars × Fin φ.clauses.length → Triple φ.numVars φ.clauses.length,
        (Finset.univ.image f).card ≤ φ.numVars * φ.clauses.length := by
      intro f
      refine (Finset.card_image_le).trans ?_
      rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    have := h1 (fun p => trueTriple p.1 p.2)
    have := h1 (fun p => falseTriple p.1 p.2)
    omega
  have hclause : (clauseTriples φ).card ≤
      φ.clauses.length * (2 * φ.numVars * φ.clauses.length) := by
    refine (Finset.card_le_card (clauseTriples_subset)).trans ?_
    refine (Finset.card_image_le).trans ?_
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, card_partY]
  have hgarb : (garbTriples φ.numVars φ.clauses.length).card ≤
      ((φ.numVars - 1) * φ.clauses.length) * (2 * φ.numVars * φ.clauses.length) := by
    rw [garbTriples]
    refine (Finset.card_image_le).trans ?_
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, card_partY]
  calc (gadgetM φ).card ≤ (ringTriples φ.numVars φ.clauses.length ∪ clauseTriples φ).card +
          (garbTriples φ.numVars φ.clauses.length).card := Finset.card_union_le _ _
    _ ≤ ((ringTriples φ.numVars φ.clauses.length).card + (clauseTriples φ).card) +
          (garbTriples φ.numVars φ.clauses.length).card := by
          gcongr; exact Finset.card_union_le _ _
    _ ≤ _ := by omega

/-- The combined-encoding size of `φ` (bounds variables, clauses, and literals): the honest
input measure for the gadget's quartic output bound. -/
def cnfSize (φ : CnfFormula) : ℕ :=
  φ.numVars + φ.clauses.length + (φ.clauses.map List.length).sum

/-- **Quartic output-size bound:** the gadget instance has `size ≤ 12·(cnfSize φ)^4 + 10`. -/
theorem gadgetInstance_size_le (hn : 1 ≤ φ.numVars) :
    (gadgetInstance φ hn).size ≤ 12 * (cnfSize φ) ^ 4 + 10 := by
  have hsize : (gadgetInstance φ hn).size =
      (gadgetM φ).card +
        (2 * φ.numVars * φ.clauses.length + 2 * φ.numVars * φ.clauses.length +
          2 * φ.numVars * φ.clauses.length) := by
    simp only [ThreeDMInstance.size, gadgetInstance_M]
    congr 1
    show Fintype.card (PartW φ.numVars φ.clauses.length) +
      Fintype.card (PartX φ.numVars φ.clauses.length) +
      Fintype.card (PartY φ.numVars φ.clauses.length) = _
    rw [card_partW _ _ hn, card_partY _ _]
  -- product bounds in terms of s = cnfSize
  set n := φ.numVars with hn'
  set m := φ.clauses.length with hm'
  set s := cnfSize φ with hs
  have hn_le : n ≤ s := by rw [hs, cnfSize]; omega
  have hm_le : m ≤ s := by rw [hs, cnfSize]; omega
  have hnm : n * m ≤ s ^ 2 := by
    calc n * m ≤ s * s := Nat.mul_le_mul hn_le hm_le
      _ = s ^ 2 := (sq s).symm
  have hs2 : s ^ 2 ≤ s ^ 4 := by
    rcases Nat.eq_zero_or_pos s with h | h
    · simp [h]
    · exact Nat.pow_le_pow_right h (by omega)
  have hsq : s ^ 4 = s ^ 2 * s ^ 2 := by ring
  -- bound gadgetM.card ≤ 6 s⁴
  have hMcard : (gadgetM φ).card ≤ 6 * s ^ 4 := by
    refine (gadgetM_card_le (φ := φ)).trans ?_
    show 2 * (n * m) + m * (2 * n * m) + (n - 1) * m * (2 * n * m) ≤ 6 * s ^ 4
    rw [hsq]
    have hm2 : m ≤ s ^ 2 := hm_le.trans (Nat.le_self_pow (by norm_num) s)
    have hs22 : s ^ 2 ≤ s ^ 2 * s ^ 2 := by rw [← hsq]; exact hs2
    have a1 : 2 * (n * m) ≤ 2 * (s ^ 2 * s ^ 2) := by
      have := hnm.trans hs22; omega
    have a2 : m * (2 * n * m) ≤ 2 * (s ^ 2 * s ^ 2) := by
      have hb : m * (n * m) ≤ s ^ 2 * s ^ 2 := Nat.mul_le_mul hm2 hnm
      calc m * (2 * n * m) = 2 * (m * (n * m)) := by ring
        _ ≤ 2 * (s ^ 2 * s ^ 2) := by omega
    have a3 : (n - 1) * m * (2 * n * m) ≤ 2 * (s ^ 2 * s ^ 2) := by
      have hb : (n - 1) * m * (n * m) ≤ s ^ 2 * s ^ 2 :=
        Nat.mul_le_mul ((Nat.mul_le_mul (Nat.sub_le n 1) le_rfl).trans hnm) hnm
      calc (n - 1) * m * (2 * n * m) = 2 * ((n - 1) * m * (n * m)) := by ring
        _ ≤ 2 * (s ^ 2 * s ^ 2) := by omega
    omega
  -- the 6nm tail ≤ 6 s⁴
  have htail : 2 * n * m + 2 * n * m + 2 * n * m ≤ 6 * s ^ 4 := by
    have h := hnm.trans hs2
    nlinarith [h]
  rw [hsize]
  calc (gadgetM φ).card + (2 * n * m + 2 * n * m + 2 * n * m)
      ≤ 6 * s ^ 4 + 6 * s ^ 4 := Nat.add_le_add hMcard htail
    _ ≤ 12 * s ^ 4 + 10 := by omega

end ThreeDM

/-! ## The total reduction map and the Karp reduction `3SAT ≤ₖ 3DM`
The total map sends a 3-CNF with `≥ 1` variable to its gadget instance (the genuine
construction), and degenerate inputs to a fixed yes/no instance per the *decidable* `threeSat`
(the standard total-map convention). Correctness is the gadget bi-implication on the main
branch and the decidability on the degenerate branches; the output size is the quartic gadget
bound or a constant. We measure the **source** by `ThreeDM.cnfSize` (variables + clauses +
literals), which dominates the gadget's quartic blow-up. -/

open ThreeDM

/-- The **total reduction map** `CnfFormula → ThreeDMInstance`: gadget instance for a 3-CNF
with `≥ 1` variable; a fixed yes/no instance otherwise (by the decidable `threeSat`). -/
noncomputable def threeSatToThreeDMMap (φ : CnfFormula) : ThreeDMInstance :=
  if h : Is3Cnf φ ∧ 1 ≤ φ.numVars then gadgetInstance φ h.2
  else if threeSat φ then yesInstance else noInstance

/-- **The reduction correctness** (`3SAT ≤ₖ 3DM`): `threeSat φ` iff its image under
`threeSatToThreeDMMap` admits a perfect matching. On the gadget branch this is the genuine
matching ⟺ assignment bi-implication; on the degenerate branches it is the decidability of
`threeSat` against the fixed yes/no instances. -/
theorem threeSat_iff_threeDMDecision_map (φ : CnfFormula) :
    threeSat φ ↔ (threeSatToThreeDMMap φ).threeDMDecision := by
  unfold threeSatToThreeDMMap
  by_cases h : Is3Cnf φ ∧ 1 ≤ φ.numVars
  · rw [dif_pos h]
    exact threeSat_iff_threeDMDecision_gadgetInstance h.1 h.2
  · rw [dif_neg h]
    by_cases hs : threeSat φ
    · rw [if_pos hs]
      exact ⟨fun _ => threeDMDecision_yesInstance, fun _ => hs⟩
    · rw [if_neg hs]
      exact ⟨fun h => absurd h hs, fun h => absurd h not_threeDMDecision_noInstance⟩

/-- The output size is the quartic gadget bound on the main branch and a constant (`≤ 4`) on
the degenerate branches, so `size (map φ) ≤ 12·(cnfSize φ)^4 + 10`. -/
theorem size_threeSatToThreeDMMap_le (φ : CnfFormula) :
    (threeSatToThreeDMMap φ).size ≤ 12 * (cnfSize φ) ^ 4 + 10 := by
  unfold threeSatToThreeDMMap
  by_cases h : Is3Cnf φ ∧ 1 ≤ φ.numVars
  · rw [dif_pos h]; exact gadgetInstance_size_le h.2
  · rw [dif_neg h]
    by_cases hs : threeSat φ
    · rw [if_pos hs]
      have : yesInstance.size = 0 := by simp [ThreeDMInstance.size, yesInstance]
      omega
    · rw [if_neg hs]
      have : noInstance.size = 3 := by simp [ThreeDMInstance.size, noInstance]
      omega

/-- **The Karp reduction `3SAT ≤ₖ 3DM`** (Garey-Johnson Theorem 3.2): the total map
`threeSatToThreeDMMap`, with the genuine matching ⟺ assignment bi-implication as correctness
(both directions proved) and the quartic output-size bound `12·X^4 + 10` as the honest
poly-time proxy. The source size is `ThreeDM.cnfSize` (variables + clauses + literals). -/
noncomputable def threeSatToThreeDM :
    KarpReduction cnfSize ThreeDMInstance.size threeSat ThreeDMInstance.threeDMDecision where
  toFun := threeSatToThreeDMMap
  correct := threeSat_iff_threeDMDecision_map
  poly := 12 * Polynomial.X ^ 4 + Polynomial.C 10
  size_bound φ := by
    have := size_threeSatToThreeDMMap_le φ
    simpa using this

/-- **`3DM` is NP-hard relative to `3SAT`** (unconditional): `3SAT` Karp-reduces to `3DM`. This
needs no complexity-class framework — only the reduction `threeSatToThreeDM`. -/
theorem isNPHardVia_threeSat_threeDMDecision :
    KarpReduction.IsNPHardVia cnfSize ThreeDMInstance.size threeSat
      ThreeDMInstance.threeDMDecision :=
  ⟨threeSatToThreeDM⟩

/-! ## Book restatement (`3SAT ≤ₖ 3DM`, Garey-Johnson Theorem 3.2)
The textbook Karp reduction 3-Satisfiability ⤳ 3-Dimensional Matching: each variable becomes a
`2m`-element truth-setting ring (two orientations = the two truth values), each clause a
two-element gadget routed through a satisfying literal's tip, and garbage collectors balance the
three parts to a common size `q = 2nm`. A satisfying assignment yields a perfect matching
(orient rings, route clauses, garbage-collect) and conversely a perfect matching reads off a
consistent satisfying assignment (the ring chaining forces a uniform orientation; the clause
gadgets force a true literal). Both directions are fully proved, so this is a genuine Karp
reduction. -/
example :
    -- the reduction is correct (both directions) on every input
    (∀ φ : CnfFormula, threeSat φ ↔ (threeSatToThreeDMMap φ).threeDMDecision) ∧
    -- 3DM is NP-hard relative to 3SAT (unconditional)
    KarpReduction.IsNPHardVia cnfSize ThreeDMInstance.size threeSat
      ThreeDMInstance.threeDMDecision :=
  ⟨threeSat_iff_threeDMDecision_map, isNPHardVia_threeSat_threeDMDecision⟩

/-! ## The Cook–Levin chain hookup (`isNPHard_TM_threeDM`) — scoped gap
The genuine matching ⟺ assignment reduction above is complete (both directions proved), giving
`threeSatToThreeDM : KarpReduction cnfSize ThreeDMInstance.size threeSat threeDMDecision` and
hence `3DM` NP-hard **relative to** `3SAT` (`isNPHardVia_threeSat_threeDMDecision`,
unconditional).

What is **not** yet wired is the absolute chain `isNPHard_TM_threeDM` via
`isNPHard_TM_threeSat.viaReduction`. That needs a `KarpReduction` whose **source size is
`cnfEncode · |·|`** (the encoding `isNPHard_TM_threeSat` is stated against), whereas
`threeSatToThreeDM` measures the source by `ThreeDM.cnfSize = numVars + #clauses + #literals`.
The two differ by `numVars`: `cnfEncode` records the variable count as a single list entry, so
`(cnfEncode φ).length` does **not** bound `numVars` — a formula with many *unused* variables has
a small encoding length but a large gadget (the rings grow as `numVars²`). So the honest
quartic bound holds against `cnfSize` but **not** against `(cnfEncode φ).length`, and asserting
the `cnfEncode`-sourced reduction would require a false size bound.

Closing the gap needs a **variable-compaction prepass** `compactify : CnfFormula → CnfFormula`
dropping variables absent from every clause (relabelling the rest into a contiguous block), with
`Satisfiable φ ↔ Satisfiable (compactify φ)`, `Is3Cnf φ ↔ Is3Cnf (compactify φ)`, and
`(compactify φ).numVars ≤ 3 · #clauses` (a 3-CNF clause has ≤ 3 literals). Composing
`compactify` before `threeSatToThreeDM` then bounds the gadget by `(cnfEncode φ).length` and
yields `isNPHard_TM_threeDM := isNPHard_TM_threeSat.viaReduction (threeSatToThreeDM.comp …)`.
This compaction layer is the only remaining step; the combinatorial reduction (the hard part of
Garey-Johnson Thm 3.2) is fully proved. `[infra]` -/

/-! ## Verification: the construction says the right thing
Each key claim restated as an anonymous `example` against its expected type — the forward
(satisfying assignment ⇒ matching) and reverse (matching ⇒ satisfying assignment) directions,
the equal-card invariant, and the full bi-implication. -/

-- The forward direction: a satisfying assignment yields a perfect matching.
example (φ : CnfFormula) (hn : 1 ≤ φ.numVars) (hsat : Satisfiable φ) :
    (ThreeDM.gadgetInstance φ hn).threeDMDecision :=
  ThreeDM.threeDMDecision_gadgetInstance_of_satisfiable hn hsat

-- The reverse direction: a perfect matching yields a satisfying assignment.
example (φ : CnfFormula) (hn : 1 ≤ φ.numVars)
    (hD : (ThreeDM.gadgetInstance φ hn).threeDMDecision) : Satisfiable φ :=
  ThreeDM.satisfiable_of_threeDMDecision_gadgetInstance hn hD

-- The equal-card invariant of the gadget: `|W| = |X| = |Y| = q = 2nm`.
example (φ : CnfFormula) (hn : 1 ≤ φ.numVars) :
    Fintype.card (ThreeDM.gadgetInstance φ hn).W = (ThreeDM.gadgetInstance φ hn).q ∧
    Fintype.card (ThreeDM.gadgetInstance φ hn).X = (ThreeDM.gadgetInstance φ hn).q ∧
    Fintype.card (ThreeDM.gadgetInstance φ hn).Y = (ThreeDM.gadgetInstance φ hn).q :=
  ⟨(ThreeDM.gadgetInstance φ hn).card_W, (ThreeDM.gadgetInstance φ hn).card_X,
    (ThreeDM.gadgetInstance φ hn).card_Y⟩

-- The full reduction: `threeSat φ ↔ 3DM(map φ)`, both directions, total.
example : ∀ φ : CnfFormula, threeSat φ ↔ (threeSatToThreeDMMap φ).threeDMDecision :=
  threeSat_iff_threeDMDecision_map

-- The Karp reduction `3SAT ≤ₖ 3DM` exists (NP-hardness of 3DM relative to 3SAT).
example : KarpReduction.IsNPHardVia ThreeDM.cnfSize ThreeDMInstance.size threeSat
    ThreeDMInstance.threeDMDecision :=
  isNPHardVia_threeSat_threeDMDecision

end DeepWiki
