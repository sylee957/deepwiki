import DeepWiki.RelationalDatabases.RelationalAlgebra

/-! # The chase: tableaux and the initial tableau
The chase decides whether a join dependency is implied by a set of fds and jds (Algorithm 3.4). It
works on *tableaux* — sets of rows whose entries are symbols, *distinguished* (`αA`, one per
attribute) or *undistinguished* (`βᴬᵢ`, per attribute and row). This file builds the data model
(Def 3.11), the initial tableau of a join dependency (Def 3.12), the all-distinguished goal row
whose presence signals success, and the valuation bridge sending a tableau to a relation instance.

The chase steps (the fd- and jd-rules of Algorithm 3.4), their iteration to a fixpoint, termination
and the correctness Theorem 3.15 (`chase(τ(J))` contains the distinguished row iff `SC ⊨ J`) are
layered on later. -/

namespace DeepWiki

universe u v

variable {Att : Type u} [DecidableEq Att] {Val : Type v} {Ω : Finset Att}

/-- A chase symbol (Def 3.11): a *distinguished* variable `αA` (one per attribute) or an
*undistinguished* variable `βᴬᵢ` (per attribute `A` and row index `i`). -/
inductive ChaseSymbol (Att : Type u) where
  /-- The distinguished variable `αA`. -/
  | dist : Att → ChaseSymbol Att
  /-- The undistinguished variable `βᴬᵢ`. -/
  | undist : Att → ℕ → ChaseSymbol Att
  deriving DecidableEq

/-- A *row* of `PRS` (Def 3.11): an assignment of a chase symbol to each attribute of `Ω`. -/
abbrev ChaseRow (Ω : Finset Att) : Type u := {a // a ∈ Ω} → ChaseSymbol Att

/-- A *tableau* (Def 3.11): a set of rows. -/
abbrev Tableau (Ω : Finset Att) : Type u := Set (ChaseRow Ω)

/-- The all-distinguished row `R` with `R(A) = αA`: its presence in the chased tableau signals that
the join dependency is implied (Algorithm 3.4's success condition). -/
def distRow (Ω : Finset Att) : ChaseRow Ω := fun a => ChaseSymbol.dist a.val

/-- The *initial tableau* `τ(J)` of a join dependency with components `comp` (Def 3.12): one row per
component, distinguished on the component and freshly undistinguished elsewhere. -/
def initialTableau {k : ℕ} (comp : Fin k → Finset Att) : Tableau Ω :=
  Set.range fun (i : Fin k) (a : {x // x ∈ Ω}) =>
    if a.val ∈ comp i then ChaseSymbol.dist a.val else ChaseSymbol.undist a.val i.val

/-- The initial tableau already contains the all-distinguished row exactly when some component
covers `Ω` — i.e. the join dependency is trivial and the chase succeeds immediately. -/
theorem distRow_mem_initialTableau_iff {k : ℕ} (comp : Fin k → Finset Att) :
    distRow Ω ∈ initialTableau comp ↔ ∃ i, ∀ a : {x // x ∈ Ω}, a.val ∈ comp i := by
  rw [initialTableau, Set.mem_range]
  refine exists_congr fun i => ?_
  rw [funext_iff]
  refine forall_congr' fun a => ?_
  by_cases hc : a.val ∈ comp i <;> simp [distRow, hc]

/-- A *valuation* sends chase symbols to data values. -/
abbrev Valuation (Att : Type u) (Val : Type v) : Type _ := ChaseSymbol Att → Val

/-- A valuation turns a row into a tuple. -/
def applyRow (ρ : Valuation Att Val) (ℓ : ChaseRow Ω) : Tuple Ω Val := fun a => ρ (ℓ a)

/-- A valuation turns a tableau into a relation instance (the image of its rows) — the bridge used
to relate the chased tableau to relations in the correctness proof of the chase. -/
def applyTableau (ρ : Valuation Att Val) (T : Tableau Ω) : Table Ω Val := applyRow ρ '' T

omit [DecidableEq Att] in
/-- Membership in the image relation: `t` comes from some tableau row under the valuation. -/
@[simp] theorem mem_applyTableau (ρ : Valuation Att Val) (T : Tableau Ω) (t : Tuple Ω Val) :
    t ∈ applyTableau ρ T ↔ ∃ ℓ ∈ T, applyRow ρ ℓ = t := by
  simp [applyTableau, Set.mem_image]

end DeepWiki
