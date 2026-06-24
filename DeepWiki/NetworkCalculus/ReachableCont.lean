import DeepWiki.NetworkCalculus.UnifSmallStep
import Mathlib.Computability.TuringMachine.Computable

/-!
# Reachable-continuation type for the Cook- and Levin-style tableau

Layer 3b-iii(d), model-side: a *finite* type of continuations `ContTok tm`
reachable from a `Turing.FinTM2` program, closed under the uniform step
`UnifSmallStep.unifStep`, together with its transition function `unifNextCont`.

The continuations that can ever occur are subterms of the program statements
`tm.m l` (`Turing.TM2.stmts₁`), plus `none` (halted). `relevantStmts tm`
collects them; `subterm_mem_relevant` proves the set is closed under taking
subterms, which is exactly the closure each `unifNextCont` arm needs.

The bridge `unifNextCont_eq_unifStep` shows `unifNextCont`, forgetting its
membership proof, equals the continuation component `(unifStep tm.m …).1` —
so the finite token type faithfully tracks `unifStep`'s control flow.

Deferred to later layers: the `funClauses₂` tableau encoding of `unifNextCont`
(the cont-transition clauses over the combined space, with `ContTok tm` as the
register value type), the state- and cell-transition assembly, and reduction
correctness.
-/

open Function (update)

namespace DeepWiki

namespace ReachableCont

open Turing.TM2 Turing.TM2.Stmt UnifSmallStep

open scoped Classical

variable (tm : Turing.FinTM2)

/-- All statements reachable as subterms of any program label: the biUnion of
`stmts₁ (tm.m l)` over the finite label type `tm.Λ`. -/
noncomputable def relevantStmts : Finset (Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) :=
  (@Finset.univ tm.Λ tm.ΛFin).biUnion (fun l => Turing.TM2.stmts₁ (tm.m l))

/-- Each program statement `tm.m l` is relevant (via `stmts₁_self`). -/
theorem program_mem_relevant (l : tm.Λ) : tm.m l ∈ relevantStmts tm := by
  rw [relevantStmts]
  exact Finset.mem_biUnion.2 ⟨l, @Finset.mem_univ _ tm.ΛFin l, Turing.TM2.stmts₁_self⟩

/-- The relevant set is closed under taking subterms: any `q' ∈ stmts₁ q` of a
relevant `q` is relevant (via `stmts₁_trans`). -/
theorem subterm_mem_relevant {q q' : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ}
    (hq : q ∈ relevantStmts tm) (hq' : q' ∈ Turing.TM2.stmts₁ q) :
    q' ∈ relevantStmts tm := by
  rw [relevantStmts] at hq ⊢
  obtain ⟨l, _, hl⟩ := Finset.mem_biUnion.1 hq
  exact Finset.mem_biUnion.2 ⟨l, @Finset.mem_univ _ tm.ΛFin l, Turing.TM2.stmts₁_trans hl hq'⟩

/-- A continuation token: `none` = halted, `some ⟨q, _⟩` = about to execute the
relevant statement `q`. A finite type (`Fintype` below) of reachable controls. -/
def ContTok : Type :=
  Option {q : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ // q ∈ relevantStmts tm}

noncomputable instance : Fintype (ContTok tm) := by
  unfold ContTok
  classical
  infer_instance

noncomputable instance : DecidableEq (ContTok tm) := by
  unfold ContTok
  classical
  infer_instance

/-- The halted token `none` is the default continuation. -/
instance : Inhabited (ContTok tm) := ⟨none⟩

variable {tm}

/-- Subterm closure for `push`: the tail `q'` of a relevant `push k f q'` is
relevant (`q' ∈ stmts₁ (push k f q') = insert _ (stmts₁ q')`). -/
theorem mem_relevant_push {k : tm.K} {f : tm.σ → tm.Γ k}
    {q' : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ}
    (hq : push k f q' ∈ relevantStmts tm) : q' ∈ relevantStmts tm :=
  subterm_mem_relevant tm hq (by
    rw [Turing.TM2.stmts₁]; exact Finset.mem_insert_of_mem Turing.TM2.stmts₁_self)

/-- Subterm closure for `peek`: the tail `q'` of a relevant `peek k f q'` is relevant. -/
theorem mem_relevant_peek {k : tm.K} {f : tm.σ → Option (tm.Γ k) → tm.σ}
    {q' : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ}
    (hq : peek k f q' ∈ relevantStmts tm) : q' ∈ relevantStmts tm :=
  subterm_mem_relevant tm hq (by
    rw [Turing.TM2.stmts₁]; exact Finset.mem_insert_of_mem Turing.TM2.stmts₁_self)

/-- Subterm closure for `pop`: the tail `q'` of a relevant `pop k f q'` is relevant. -/
theorem mem_relevant_pop {k : tm.K} {f : tm.σ → Option (tm.Γ k) → tm.σ}
    {q' : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ}
    (hq : pop k f q' ∈ relevantStmts tm) : q' ∈ relevantStmts tm :=
  subterm_mem_relevant tm hq (by
    rw [Turing.TM2.stmts₁]; exact Finset.mem_insert_of_mem Turing.TM2.stmts₁_self)

/-- Subterm closure for `load`: the tail `q'` of a relevant `load a q'` is relevant. -/
theorem mem_relevant_load {a : tm.σ → tm.σ}
    {q' : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ}
    (hq : load a q' ∈ relevantStmts tm) : q' ∈ relevantStmts tm :=
  subterm_mem_relevant tm hq (by
    rw [Turing.TM2.stmts₁]; exact Finset.mem_insert_of_mem Turing.TM2.stmts₁_self)

/-- Subterm closure for `branch`, left arm: `q₁` of a relevant `branch f q₁ q₂`
is relevant (`q₁ ∈ stmts₁ (branch …) = insert _ (stmts₁ q₁ ∪ stmts₁ q₂)`). -/
theorem mem_relevant_branch_left {f : tm.σ → Bool}
    {q₁ q₂ : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ}
    (hq : branch f q₁ q₂ ∈ relevantStmts tm) : q₁ ∈ relevantStmts tm :=
  subterm_mem_relevant tm hq (by
    rw [Turing.TM2.stmts₁]
    exact Finset.mem_insert_of_mem (Finset.mem_union_left _ Turing.TM2.stmts₁_self))

/-- Subterm closure for `branch`, right arm: `q₂` of a relevant `branch f q₁ q₂`
is relevant. -/
theorem mem_relevant_branch_right {f : tm.σ → Bool}
    {q₁ q₂ : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ}
    (hq : branch f q₁ q₂ ∈ relevantStmts tm) : q₂ ∈ relevantStmts tm :=
  subterm_mem_relevant tm hq (by
    rw [Turing.TM2.stmts₁]
    exact Finset.mem_insert_of_mem (Finset.mem_union_right _ Turing.TM2.stmts₁_self))

/-- The chosen arm `cond b q₁ q₂` of a relevant `branch f q₁ q₂` is relevant
(case-split on the boolean `b`). -/
theorem mem_relevant_branch_cond {f : tm.σ → Bool}
    {q₁ q₂ : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ} (b : Bool)
    (hq : branch f q₁ q₂ ∈ relevantStmts tm) : cond b q₁ q₂ ∈ relevantStmts tm := by
  cases b with
  | false => exact mem_relevant_branch_right hq
  | true => exact mem_relevant_branch_left hq

variable (tm)

/-- The uniform continuation transition: `none ↦ none`; on `some ⟨q, hq⟩` it
mirrors `unifStep`'s control component — `push`/`peek`/`pop`/`load` step to the
tail, `branch` to the chosen arm, `goto f` to the next program `tm.m (f v)`,
`halt` to `none`. Each target is proved relevant by the closure lemmas. -/
noncomputable def unifNextCont : ContTok tm → tm.σ → ContTok tm
  | none, _ => none
  | some ⟨q, hq⟩, v =>
    match q, hq with
    | push _ _ q', hq => some ⟨q', mem_relevant_push hq⟩
    | peek _ _ q', hq => some ⟨q', mem_relevant_peek hq⟩
    | pop _ _ q', hq => some ⟨q', mem_relevant_pop hq⟩
    | load _ q', hq => some ⟨q', mem_relevant_load hq⟩
    | branch f q₁ q₂, hq => some ⟨cond (f v) q₁ q₂, mem_relevant_branch_cond (f v) hq⟩
    | goto f, _ => some ⟨tm.m (f v), program_mem_relevant tm (f v)⟩
    | halt, _ => none

/-- `unifNextCont` on the halted token is halted. -/
@[simp] theorem unifNextCont_none (v : tm.σ) : unifNextCont tm none v = none := rfl

variable {tm}

/-- BRIDGE: `unifNextCont`, forgetting its membership proof (`Option.map
Subtype.val`), equals the continuation component `(unifStep tm.m (some q, v, S)).1`.
Proved by case analysis on `q` via the `unifStep_*` simp lemmas. -/
theorem unifNextCont_eq_unifStep (q : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hq : q ∈ relevantStmts tm) (v : tm.σ) (S : ∀ k, List (tm.Γ k)) :
    (unifNextCont tm (some ⟨q, hq⟩) v).map Subtype.val = (unifStep tm.m (some q, v, S)).1 := by
  cases q with
  | push k f q' => rfl
  | peek k f q' => rfl
  | pop k f q' => rfl
  | load a q' => rfl
  | branch f q₁ q₂ => rfl
  | goto f => rfl
  | halt => rfl

/-- The bridge, restated. -/
example (q : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) (hq : q ∈ relevantStmts tm)
    (v : tm.σ) (S : ∀ k, List (tm.Γ k)) :
    (unifNextCont tm (some ⟨q, hq⟩) v).map Subtype.val = (unifStep tm.m (some q, v, S)).1 :=
  unifNextCont_eq_unifStep q hq v S

end ReachableCont

end DeepWiki
