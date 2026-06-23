import DeepWiki.NetworkCalculus.TandemLinearProgram
import DeepWiki.NetworkCalculus.WorstCaseLP

/-! # The general FIFO tandem MILP as data (Theorem 11.2, §11.2.2)

The §11.2.2 construction that turns the worst-case end-to-end delay of a flow through
an `n`-server **FIFO** tandem into a *mixed-integer* linear program (Theorem 11.2).  On
top of the arbitrary-multiplexing tandem linear program (`TandemLP`, §11.1.2) it adds,
per server, the **FIFO service-order constraint**: a packet that arrives earlier
departs earlier.  Because under FIFO the order in which dates have to be compared is not
known a priori (it depends on the trajectory), the book linearises each such order
choice with a Boolean **date-ordering variable** `b ∈ {0,1}` and the *big-M* pair
(Lemma 11.1.1) — `x ≤_b y`, i.e. `x ≤ y` when `b = 0`, `y ≤ x` when `b = 1`.

This file gives the *representable* content:

* **the big-M FIFO ordering primitive** `BigMOrder` (`x ≤_b y` as data) and its faithful
  equivalence to the order disjunction (`bigMOrder_iff`, the `bigM_ordering_iff`
  pattern) — exactly *what the binary variables encode*;
* **the single-flow FIFO tandem MILP** as a Lean structure: `FifoVars` augments
  `TandemLP.Vars` with one Boolean per server and the big-M ordering constraint pair,
  `FifoFeasible` is the augmented constraint set, with well-formedness (`z ∈ {0,1}`, the
  big-M box);
* **the soundness fragment**: FIFO is a *restriction* of arbitrary multiplexing, so a
  FIFO-feasible MILP point is `TandemLP.Feasible` (`FifoFeasible.feasible`); the §11.1
  delay bound therefore transports unchanged (`fifoDelay_le_objectiveValue`), and the
  MILP optimum is below the arbitrary-mux LP optimum (`fifoOptimum_le_arbMuxOptimum`,
  `milpOptimum_le_relaxationOptimum`).

What is **not** representable here — and is scoped at the end of the file — is the full
binary-tree variable layout (`t₁,…,t_{2^{n+1}-1}`, exponentially many dates that
*double* at each server going backwards) and the claim that the MILP *optimum equals*
the worst case.  The optimum requires enumerating the `2^?` Boolean orderings and a
trajectory-from-solution reconstruction (an extremal/existence argument, §11.2.2 proof);
that is solver-dependent and is **not** a closed form, so it is documented, not proved. -/

namespace DeepWiki

open scoped BigOperators

namespace TandemFifo

/-! ## The big-M FIFO ordering primitive (Lemma 11.1.1)

The Boolean date-ordering variable `b ∈ {0,1}` and the big-M constraint pair that
linearise "compare two unknown dates" — the single new ingredient FIFO adds over
arbitrary multiplexing.  `x ≤_b y` selects `x ≤ y` (`b = 0`) or `y ≤ x` (`b = 1`). -/

/-- **The big-M ordering constraint `x ≤_b y`** (Lemma 11.1.1): the Boolean selector
`b ∈ {0,1}` (`bBool`) is boxed in `[0,M]` together with `x, y`
(`xge0`/`xleM`, `yge0`/`yleM`), and the two big-M inequalities
`x + (1−b)·M ≥ y` (`hxy`) and `y + b·M ≥ x` (`hyx`) make exactly one of `x ≤ y`,
`y ≤ x` binding according to `b` (book convention: `b = 0 ⟹ x ≤ y`,
`b = 1 ⟹ y ≤ x`).  This is the data of one FIFO date comparison. -/
structure BigMOrder (M x y b : ℝ) : Prop where
  /-- The selector is Boolean. -/
  bBool : b = 0 ∨ b = 1
  /-- `x` is boxed below by `0`. -/
  xge0 : 0 ≤ x
  /-- `x` is boxed above by `M`. -/
  xleM : x ≤ M
  /-- `y` is boxed below by `0`. -/
  yge0 : 0 ≤ y
  /-- `y` is boxed above by `M`. -/
  yleM : y ≤ M
  /-- Big-M constraint forcing `x ≤ y` when `b = 0`. -/
  hxy : x + (1 - b) * M ≥ y
  /-- Big-M constraint forcing `y ≤ x` when `b = 1`. -/
  hyx : y + b * M ≥ x

/-- **`b = 0` selects `x ≤ y`.** When the FIFO selector is `0`, the big-M pair forces
the date `x` to come before `y` (the `b = 0` branch of Lemma 11.1.1). -/
theorem BigMOrder.le_of_b_zero {M x y b : ℝ} (h : BigMOrder M x y b) (hb : b = 0) :
    x ≤ y := by
  have := h.hyx; rw [hb] at this; simpa using this

/-- **`b = 1` selects `y ≤ x`.** When the FIFO selector is `1`, the big-M pair forces
the date `y` to come before `x` (the `b = 1` branch of Lemma 11.1.1). -/
theorem BigMOrder.ge_of_b_one {M x y b : ℝ} (h : BigMOrder M x y b) (hb : b = 1) :
    y ≤ x := by
  have := h.hxy; rw [hb] at this; simpa using this

/-- **The big-M ordering selects one of the two orders** (Lemma 11.1.1): a valid
`BigMOrder M x y b` always yields a decided comparison `x ≤ y ∨ y ≤ x` — the linearised
disjunction.  (Trivial over a linear order, but this is the *content* of the encoding:
the Boolean variable's value names which branch holds.) -/
theorem BigMOrder.le_or_ge {M x y b : ℝ} (h : BigMOrder M x y b) : x ≤ y ∨ y ≤ x := by
  rcases h.bBool with hb | hb
  · exact Or.inl (h.le_of_b_zero hb)
  · exact Or.inr (h.ge_of_b_one hb)

/-- **Faithful equivalence of the big-M FIFO encoding** (the `bigM_ordering_iff`
pattern, one-pair form): given the Boolean selector `b ∈ {0,1}` and the box
`0 ≤ x,y ≤ M`, the big-M constraint pair `x + (1−b)·M ≥ y ∧ y + b·M ≥ x` is
*equivalent* to the selector consistently choosing the order — `(b = 0 → x ≤ y) ∧
(b = 1 → y ≤ x)`.  So the linearisation is faithful, not merely sound. -/
theorem bigMOrder_iff {M x y b : ℝ} (hxge0 : 0 ≤ x) (hxleM : x ≤ M)
    (hyge0 : 0 ≤ y) (hyleM : y ≤ M) (hb : b = 0 ∨ b = 1) :
    (x + (1 - b) * M ≥ y ∧ y + b * M ≥ x)
      ↔ ((b = 0 → x ≤ y) ∧ (b = 1 → y ≤ x)) := by
  rcases hb with rfl | rfl
  · refine ⟨fun ⟨_, h2⟩ => ⟨fun _ => by simpa using h2, fun h => absurd h (by norm_num)⟩,
      fun ⟨h, _⟩ => ⟨by nlinarith, by simpa using h rfl⟩⟩
  · refine ⟨fun ⟨h1, _⟩ => ⟨fun h => absurd h (by norm_num), fun _ => by simpa using h1⟩,
      fun ⟨_, h⟩ => ⟨by simpa using h rfl, by nlinarith⟩⟩

/-! ## The FIFO tandem MILP as data (Theorem 11.2, single-flow aggregate form)

The mixed-integer program of §11.2.2 augments the arbitrary-multiplexing tandem LP
(`TandemLP.Vars`/`TandemLP.Feasible`) with, *per server*, a Boolean date-ordering
variable and the big-M FIFO service-order constraint.  Under arbitrary multiplexing the
service curve is applied to the *whole* backlogged window; under **FIFO** the date at
which the tagged bit is served is tied to the date at which it arrived, and the relative
order of these dates — unknown a priori — is what the Boolean variables decide.

The representable, single-flow aggregate model: `FifoVars` carries the `TandemLP`
variables plus a per-server selector `z h ∈ {0,1}`; `FifoFeasible` carries the full
`TandemLP.Feasible` constraints *and*, per server, a `BigMOrder` linking the boundary
dates `t h.succ ≤_{z h} t h.castSucc` to the selector.  The big-M box constant `M`
bounds the dates.  This makes the **restriction** structural: FIFO feasibility *contains*
arbitrary-mux feasibility, so the §11.1 delay bound transports verbatim. -/

/-- **The variables of the FIFO tandem MILP**: the arbitrary-multiplexing tandem
variables `base : TandemLP.Vars n` (dates `t`, cumulatives `A`, `D`) together with the
per-server Boolean date-ordering selector `z h ∈ {0,1}` that FIFO adds (one binary per
server, deciding the service order of the tagged bit's arrival vs departure dates). -/
structure FifoVars (n : ℕ) where
  /-- The underlying arbitrary-mux tandem LP variables. -/
  base : TandemLP.Vars n
  /-- The per-server Boolean date-ordering selector (`0/1`-valued; well-formedness in
  `FifoFeasible`). -/
  z : Fin n → ℝ

/-- **The feasible set of the FIFO tandem MILP** (Theorem 11.2, single-flow aggregate
form): a point is FIFO-feasible for a tandem `N` with big-M constant `M` when

* its underlying `base` is `TandemLP.Feasible N` (all the arbitrary-mux constraints —
  date ordering, cumulative monotonicity, source token bucket, per-server rate-latency
  strict service, flow conservation, causality); **and**
* per server `h`, the **big-M FIFO ordering** `BigMOrder M (t h.succ) (t h.castSucc)
  (z h)` holds — the Boolean `z h` consistently selects the served order of the two
  boundary dates, with the dates boxed in `[0, M]` and the big-M constraint pair.

FIFO is thus modeled as the arbitrary-mux feasible set *plus* the Boolean ordering
constraints — a strict restriction (`FifoFeasible.feasible`). -/
def FifoFeasible {n : ℕ} (N : TandemLP.Tandem n) (M : ℝ) (v : FifoVars n) : Prop :=
  TandemLP.Feasible N v.base ∧
    ∀ h : Fin n, BigMOrder M (v.base.t h.succ) (v.base.t h.castSucc) (v.z h)

/-- The FIFO MILP **objective**: the same end-to-end delay as the arbitrary-mux LP,
read off the underlying tandem variables. -/
def fifoDelay {n : ℕ} (v : FifoVars n) : ℝ := TandemLP.delay v.base

/-! ### Soundness fragment (FIFO is a restriction of arbitrary multiplexing)

The headline: a FIFO-feasible MILP point is arbitrary-mux feasible, so its delay obeys
the §11.1 bound `(∑ₕ Rₕ·Tₕ + b)/(Rmin − r)` unchanged.  Everything is the structural
restriction `FifoFeasible ⟹ TandemLP.Feasible` plus transport through `TandemLP`. -/

/-- **FIFO ⟹ arbitrary multiplexing** (the restriction): a FIFO-feasible point's
underlying tandem variables are `TandemLP.Feasible` — FIFO only *adds* the Boolean
ordering constraints, so its feasible set sits inside the arbitrary-mux one. -/
theorem FifoFeasible.feasible {n : ℕ} {N : TandemLP.Tandem n} {M : ℝ} {v : FifoVars n}
    (hv : FifoFeasible N M v) : TandemLP.Feasible N v.base := hv.1

/-- The per-server FIFO selector is Boolean (`z h ∈ {0,1}`), the MILP integrality. -/
theorem FifoFeasible.z_bool {n : ℕ} {N : TandemLP.Tandem n} {M : ℝ} {v : FifoVars n}
    (hv : FifoFeasible N M v) (h : Fin n) : v.z h = 0 ∨ v.z h = 1 := (hv.2 h).bBool

/-- The big-M FIFO ordering decides each server's served date order: per server the two
boundary dates are comparable (`t h.succ ≤ t h.castSucc ∨ t h.castSucc ≤ t h.succ`), the
linearised FIFO service-order choice. -/
theorem FifoFeasible.order_decided {n : ℕ} {N : TandemLP.Tandem n} {M : ℝ}
    {v : FifoVars n} (hv : FifoFeasible N M v) (h : Fin n) :
    v.base.t h.succ ≤ v.base.t h.castSucc ∨ v.base.t h.castSucc ≤ v.base.t h.succ :=
  (hv.2 h).le_or_ge

/-- **Theorem 11.2 — FIFO MILP soundness (feasibility ⟹ delay bound).** For a stable
tandem (`rate0 < Rmin ≤ Rₕ` for every server), every FIFO-feasible MILP point's
end-to-end delay is at most the §11.1 objective value `(∑ₕ Rₕ·Tₕ + b)/(Rmin − r)`.
Since FIFO restricts arbitrary multiplexing (`FifoFeasible.feasible`), the arbitrary-mux
LP bound `TandemLP.delay_le_objectiveValue` applies unchanged — a FIFO-feasible point is
a valid worst-case scenario and the bound upper-bounds its realized delay. -/
theorem fifoDelay_le_objectiveValue {n : ℕ} {N : TandemLP.Tandem n} {M : ℝ}
    {v : FifoVars n} (hv : FifoFeasible N M v) {Rmin : ℝ}
    (hRmin : ∀ h : Fin n, Rmin ≤ N.rate h) (hstab : N.rate0 < Rmin) :
    fifoDelay v ≤ TandemLP.objectiveValue N Rmin :=
  TandemLP.delay_le_objectiveValue hv.feasible hRmin hstab

/-! ### The MILP optimum is below the arbitrary-mux LP optimum (§11.2.3 lower bound side)

Adding the FIFO (Boolean ordering) constraints shrinks the feasible set, so the FIFO
MILP optimum is *below* the arbitrary-mux LP optimum — FIFO can only reduce the worst
case (`programOptimum_mono_feasible`, the LP-refines-NC direction of §11.2.3). -/

/-- **FIFO MILP optimum ≤ arbitrary-mux LP optimum** (`reducedOptimum_le_milpOptimum`
pattern): the FIFO worst case is below the arbitrary-mux worst case over the same dates,
because the Boolean ordering constraints only *shrink* the feasible set.  Here both
programs share the date variables (`v.base`); FIFO additionally requires the per-server
`BigMOrder` selector to exist, so each FIFO-feasible point is arbitrary-mux feasible. -/
theorem fifoOptimum_le_arbMuxOptimum {n : ℕ} (N : TandemLP.Tandem n) (M : ℝ) :
    programOptimum (FifoFeasible N M)
        (fun v => ((fifoDelay v : ℝ) : EReal))
      ≤ programOptimum (fun v : FifoVars n => TandemLP.Feasible N v.base)
        (fun v => ((fifoDelay v : ℝ) : EReal)) :=
  programOptimum_mono_feasible fun _ hv => hv.1

/-! ## Scoping: what the FULL Theorem 11.2 needs beyond this file

The pieces above are the *representable* half of Theorem 11.2 — the FIFO constraint
system as data, the faithful big-M encoding, and the soundness/restriction direction
(`FifoFeasible ⟹ TandemLP.Feasible ⟹ delay ≤ objective`).  The remainder of the full
theorem is **solver-dependent** and is deliberately not formalized:

* **The binary-tree variable layout (§11.2.2).** The book's MILP has dates
  `t₁, …, t_{2^{n+1}-1}` that *double* at each server going backwards (`t_{2k}` for the
  FIFO arrival side, `t_{2k+1}` for the service side of `t_k`), with function values
  `Fᵢ^{(h)}(t_k)` for every flow `i` on every server `h ∈ pᵢ` of its route — an
  **exponential** number of variables.  This file models the *single-flow aggregate*
  case (one date per boundary), enough for the soundness/restriction direction; the
  full multi-flow binary-tree layout and the routing data `pᵢ`, `fst(i)`, `Fl(h)` are
  not built (they are `[infra]`: a representation layer, not a closed form).

* **The MILP optimum equals the worst case.** Theorem 11.2 states the worst-case delay
  *is* the MILP optimum.  The `≤` (soundness) direction is `fifoDelay_le_objectiveValue`;
  the `≥` (attainment) direction needs a **trajectory-from-solution reconstruction** —
  from an optimal MILP point build an admissible trajectory of the network realizing the
  delay (the §11.2.2 proof's two steps: every trajectory gives a MILP point, and every
  MILP point extrapolates to an admissible trajectory).  That is an extremal/existence
  argument over the (exponentially many) Boolean orderings, **not** a closed form, so it
  is `[research]`/`[infra]` — a solver enumerates the `2^?` orderings; no Lean lemma
  states the optimum in closed form (contrast the single FIFO node, `WorstCaseLPFifoNode`,
  whose optimum *is* closed form `T + (b₁+b₂)/R`).

* **§11.2.3 bounds.** The polynomial LP relaxation (drop the binaries) upper-bounds, and
  the date-merge reduction lower-bounds, the MILP optimum — these *are* representable and
  already live as `milpOptimum_le_relaxationOptimum` / `reducedOptimum_le_milpOptimum`
  (`WorstCaseLP`); `fifoOptimum_le_arbMuxOptimum` above is the FIFO-vs-arbitrary-mux
  instance of the same monotonicity. -/

/-! ## Restatements (the theorems say what Theorem 11.2 / Lemma 11.1.1 say) -/

/-- Lemma 11.1.1: the big-M pair is faithfully equivalent to the selected order. -/
example {M x y b : ℝ} (hx0 : 0 ≤ x) (hxM : x ≤ M) (hy0 : 0 ≤ y) (hyM : y ≤ M)
    (hb : b = 0 ∨ b = 1) :
    (x + (1 - b) * M ≥ y ∧ y + b * M ≥ x)
      ↔ ((b = 0 → x ≤ y) ∧ (b = 1 → y ≤ x)) :=
  bigMOrder_iff hx0 hxM hy0 hyM hb

/-- Theorem 11.2 (soundness): a FIFO-feasible MILP point's end-to-end delay is at most
the §11.1 objective `(∑ₕ Rₕ·Tₕ + b)/(Rmin − r)`. -/
example {n : ℕ} {N : TandemLP.Tandem n} {M : ℝ} {v : FifoVars n}
    (hv : FifoFeasible N M v) {Rmin : ℝ} (hRmin : ∀ h : Fin n, Rmin ≤ N.rate h)
    (hstab : N.rate0 < Rmin) :
    fifoDelay v ≤ TandemLP.objectiveValue N Rmin :=
  fifoDelay_le_objectiveValue hv hRmin hstab

/-- FIFO restricts arbitrary multiplexing: a FIFO-feasible point is `TandemLP.Feasible`. -/
example {n : ℕ} {N : TandemLP.Tandem n} {M : ℝ} {v : FifoVars n}
    (hv : FifoFeasible N M v) : TandemLP.Feasible N v.base :=
  hv.feasible

end TandemFifo

end DeepWiki
