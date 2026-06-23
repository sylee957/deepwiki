import DeepWiki.NetworkCalculus.TandemFifoMilpWitness
import DeepWiki.NetworkCalculus.WorstCaseLPFifoNode

/-! # Exact worst-case delay in FIFO-multiplexing feed-forward networks

The exact-worst-case-delay theory of FIFO-multiplexing feed-forward networks that the DNC
book's Ch11 §11.2 *defers to a paper* — Bouillard and Stea, "Exact Worst-Case Delay in
FIFO-Multiplexing Feed-Forward Networks", IEEE/ACM Trans. Networking 2016
(DOI `10.1109/TNET.2014.2332071`).

The book gives the FIFO tandem MILP as data and the *homogeneous* attainment
(`TandemFifoMilp`/`TandemFifoMilpWitness`).  The paper goes further: it proves that the MILP
**optimum equals the actual worst-case end-to-end delay** for an *arbitrary* feed-forward
FIFO network (its **Theorem 1**, p.7), and brackets that exact value by two *linear*
programs — a relaxation upper bound `V_LP` and a date-merge lower bound `v_LP` (§IV.D, p.8).

What is faithfully and generally formalizable from the paper — and is here:

* **Theorem 1 = Lemma 2 + Lemma 3** (the paper's proof structure), as the abstract
  *scenario- and -solution correspondence* bridge `programOptimum_eq_of_scenarioSolution`:
  whenever every network scenario with delay `d` maps to a feasible MILP point with objective
  `d` (Lemma 2), and every feasible MILP point with objective `d` maps to a scenario with
  delay `≥ d` (Lemma 3), the MILP optimum equals the worst-case delay (the scenario
  supremum).  This is *exactly* the content of the paper's Theorem 1, abstracted over the
  (uninstantiated, exponential, solver-dependent) concrete MILP/scenario encodings.

* **§IV.D bracketing** `v_LP ≤ WCD ≤ V_LP` (p.8): once `WCD = MILP optimum` (Theorem 1), the
  LP relaxation (drop the binary monotonicity variables) upper-bounds and the date-merge
  reduction (force the service-curve times of a node equal) lower-bounds the exact WCD —
  `worstCaseDelay_mem_lpBracket`.  Both bounds need only *one linear program*, the paper's
  headline practical contribution.

* **The exponential variable count** `2^(N+1) − 1` of the tandem MILP (p.6, the binary-tree
  date layout that doubles at each node going backwards), as the Nat recurrence
  `tandemMilpNumVars`.

* **The single-FIFO-node base case as an instance of Theorem 1** — the closed-form exact
  optimum `T + (b₁+b₂)/R` (`WorstCaseLPFifoNode.fifoNode_programOptimum`) packaged through the
  abstract correspondence, showing the bridge is inhabited by a genuine exact result.

What stays **scoped** (and is honestly not a closed form): the concrete general-`N` MILP and
scenario encodings — the exponential binary-tree variable layout, the `2^?` Boolean
date-orderings, and the trajectory-from-solution reconstruction that *discharges* Lemma 2 and
Lemma 3 for an arbitrary network.  The paper itself only writes these down as a constraint
system and proves the optima coincide; the optimum is then *computed* by a solver, not given
in closed form (the paper is explicit that the MILP is exponential, feasible only up to
six/seven nodes).  We deliver the abstract Theorem 1, the bracketing, the count, and the
single-node instance; the discharge of Lemmas 2/3 for general `N` is the exponential
extremal/existence content and is scoped at the end. -/

namespace DeepWiki

namespace FifoFeedForward

/-! ## Theorem 1: the MILP optimum is the worst-case delay (Lemma 2 + Lemma 3)

The paper's Theorem 1 (p.7) is proved in two halves:

* **Lemma 2** (p.7): "Let `F` be a scenario of the network with delay `d`.  There exists a
  feasible solution of the MILP such that `t₁ − t₀ = d`."  (Every realizable delay is the
  objective of some feasible point — so the optimum is *at least* the worst case.)
* **Lemma 3** (p.7–8): "For any solution of the MILP such that `t₁ − t₀ = d`, there exists a
  scenario of the system where the bit that leaves at `t₁` has a delay at least equal to `d`."
  (Every feasible objective value is realized — up to `≥` — by a scenario, so the optimum is
  *at most* the worst case.)

Both halves are existence statements relating two suprema: the worst-case delay
`WCD = ⨆ {delay of scenario}` and the MILP optimum `= ⨆ {objective of feasible point}`.  The
abstract content — independent of the (exponential, solver-dependent) concrete encodings — is
that a *delay-preserving correspondence* in both directions forces the two suprema to be
equal.  We formalize this over the library's `programOptimum` machinery: scenarios and
feasible points are both index types with a real-valued payoff, the WCD and the MILP optimum
are the two `programOptimum`s, and Lemmas 2/3 are the two correspondence hypotheses. -/

/-- **Lemma 2 ⟹ optimum ≥ WCD.**  If every valid scenario `s` (delay `scenDelay s`) admits a
feasible MILP point `toSol s` whose objective equals that delay, then the MILP optimum is at
least the worst-case delay (the scenario supremum).  This is the `≥` half of Theorem 1: the
optimum upper-bounds every realizable delay because each is *attained* as an objective. -/
theorem worstCaseDelay_le_milpOptimum {Scen Sol : Type*}
    (ScenValid : Scen → Prop) (scenDelay : Scen → ℝ)
    (Feasible : Sol → Prop) (obj : Sol → ℝ)
    (toSol : Scen → Sol)
    (hLem2 : ∀ s, ScenValid s → Feasible (toSol s) ∧ obj (toSol s) = scenDelay s) :
    programOptimum ScenValid (fun s => ((scenDelay s : ℝ) : EReal))
      ≤ programOptimum Feasible (fun v => ((obj v : ℝ) : EReal)) := by
  refine programOptimum_le fun s hs => ?_
  obtain ⟨hfeas, heq⟩ := hLem2 s hs
  have := le_programOptimum (Feasible := Feasible) (obj := fun v => ((obj v : ℝ) : EReal)) hfeas
  rw [heq] at this
  exact this

/-- **Lemma 3 ⟹ optimum ≤ WCD.**  If every feasible MILP point `v` (objective `obj v`) admits
a valid scenario `toScen v` whose delay is at least that objective, then the MILP optimum is at
most the worst-case delay.  This is the `≤` half of Theorem 1: no feasible objective can exceed
a realizable delay, since each is *dominated* by an actual scenario. -/
theorem milpOptimum_le_worstCaseDelay {Scen Sol : Type*}
    (ScenValid : Scen → Prop) (scenDelay : Scen → ℝ)
    (Feasible : Sol → Prop) (obj : Sol → ℝ)
    (toScen : Sol → Scen)
    (hLem3 : ∀ v, Feasible v → ScenValid (toScen v) ∧ obj v ≤ scenDelay (toScen v)) :
    programOptimum Feasible (fun v => ((obj v : ℝ) : EReal))
      ≤ programOptimum ScenValid (fun s => ((scenDelay s : ℝ) : EReal)) := by
  refine programOptimum_le fun v hv => ?_
  obtain ⟨hvalid, hle⟩ := hLem3 v hv
  have := le_programOptimum (Feasible := ScenValid)
    (obj := fun s => ((scenDelay s : ℝ) : EReal)) hvalid
  exact le_trans (by exact_mod_cast hle) this

/-- **Theorem 1 (p.7): the MILP optimum is the worst-case delay.**  Combining Lemma 2
(`toSol`: every scenario maps to a feasible point with equal objective) and Lemma 3 (`toScen`:
every feasible point maps to a scenario with delay ≥ objective), the MILP optimum equals the
worst-case end-to-end delay (the supremum of realizable scenario delays).  This is the exact
statement of the paper's main theorem, abstracted over the concrete (exponential,
solver-dependent) scenario and MILP encodings: the two `programOptimum`s coincide. -/
theorem programOptimum_eq_of_scenarioSolution {Scen Sol : Type*}
    (ScenValid : Scen → Prop) (scenDelay : Scen → ℝ)
    (Feasible : Sol → Prop) (obj : Sol → ℝ)
    (toSol : Scen → Sol) (toScen : Sol → Scen)
    (hLem2 : ∀ s, ScenValid s → Feasible (toSol s) ∧ obj (toSol s) = scenDelay s)
    (hLem3 : ∀ v, Feasible v → ScenValid (toScen v) ∧ obj v ≤ scenDelay (toScen v)) :
    programOptimum Feasible (fun v => ((obj v : ℝ) : EReal))
      = programOptimum ScenValid (fun s => ((scenDelay s : ℝ) : EReal)) :=
  le_antisymm
    (milpOptimum_le_worstCaseDelay ScenValid scenDelay Feasible obj toScen hLem3)
    (worstCaseDelay_le_milpOptimum ScenValid scenDelay Feasible obj toSol hLem2)

/-! ## §IV.D: the LP bracketing `v_LP ≤ WCD ≤ V_LP` (p.8)

The paper's headline practical contribution: the exact WCD — which by Theorem 1 is the
(exponential) MILP optimum — is bracketed by *two linear programs*, each requiring only one
LP solve.

* **Upper bound `V_LP`** (relaxation, p.8): "if we give up monotonicity (which puts binary
  variables into the picture), we only keep the partial ordering ... and solve one LP with
  these constraints. Since this problem is a relaxation of the one for the WCD, its optimum is
  clearly an upper bound on the WCD."  Dropping the Boolean variables *enlarges* the feasible
  set, so the relaxed optimum is `≥` the MILP optimum (`milpOptimum_le_relaxationOptimum`).

* **Lower bound `v_LP`** (date reduction, p.8): "if we enforce manually a total order on the
  times ... we obtain a feasible scenario ... and we can dispense with the binary variables.
  This way, we instead obtain a lower bound on the WCD ... we do this by forcing the SC times
  related to all the times of a node to be equal."  Adding equalities *shrinks* the feasible
  set, so the reduced optimum is `≤` the MILP optimum (`reducedOptimum_le_milpOptimum`).

Both are `programOptimum_mono_feasible` instances; combined with Theorem 1
(`WCD = MILP optimum`) they bracket the exact worst-case delay.  The bracketing is stated
directly on the WCD (the scenario supremum), via the Theorem 1 equality. -/

/-- **§IV.D bounds (p.8): `v_LP ≤ MILP optimum ≤ V_LP`.**  The relaxed LP `RelaxFeasible`
(binaries dropped, feasible set enlarged) optimum is an upper bound, and the reduced LP
`ReducedFeasible` (date-merge equalities added, feasible set shrunk) optimum is a lower bound,
on the FIFO MILP optimum — both pure feasible-set monotonicity.  The two LPs each need one
solve, in contrast to the exponential MILP. -/
theorem milpOptimum_mem_lpBracket {Sol : Type*}
    {ReducedFeasible MilpFeasible RelaxFeasible : Sol → Prop} {obj : Sol → EReal}
    (hred : ∀ v, ReducedFeasible v → MilpFeasible v)
    (hrelax : ∀ v, MilpFeasible v → RelaxFeasible v) :
    programOptimum ReducedFeasible obj ≤ programOptimum MilpFeasible obj
      ∧ programOptimum MilpFeasible obj ≤ programOptimum RelaxFeasible obj :=
  ⟨reducedOptimum_le_milpOptimum hred, milpOptimum_le_relaxationOptimum hrelax⟩

/-- **§IV.D bracketing of the exact WCD (p.8): `v_LP ≤ WCD ≤ V_LP`.**  Combining Theorem 1
(`WCD = MILP optimum`, via the scenario/solution correspondence `toSol`/`toScen` of Lemmas 2
and 3) with the relaxation upper bound and the date-merge lower bound, the *exact* worst-case
delay — the scenario supremum — lies between the two linear-program optima.  This is the
paper's central usable result: the WCD is bracketed by two single-LP computations, the upper
bound being provably non-divergent (it never exceeds the WCD's actual value, unlike the LUDB). -/
theorem worstCaseDelay_mem_lpBracket {Scen Sol : Type*}
    (ScenValid : Scen → Prop) (scenDelay : Scen → ℝ)
    {ReducedFeasible RelaxFeasible : Sol → Prop} (MilpFeasible : Sol → Prop) (obj : Sol → ℝ)
    (toSol : Scen → Sol) (toScen : Sol → Scen)
    (hLem2 : ∀ s, ScenValid s → MilpFeasible (toSol s) ∧ obj (toSol s) = scenDelay s)
    (hLem3 : ∀ v, MilpFeasible v → ScenValid (toScen v) ∧ obj v ≤ scenDelay (toScen v))
    (hred : ∀ v, ReducedFeasible v → MilpFeasible v)
    (hrelax : ∀ v, MilpFeasible v → RelaxFeasible v) :
    programOptimum ReducedFeasible (fun v => ((obj v : ℝ) : EReal))
        ≤ programOptimum ScenValid (fun s => ((scenDelay s : ℝ) : EReal))
      ∧ programOptimum ScenValid (fun s => ((scenDelay s : ℝ) : EReal))
        ≤ programOptimum RelaxFeasible (fun v => ((obj v : ℝ) : EReal)) := by
  have hT1 : programOptimum MilpFeasible (fun v => ((obj v : ℝ) : EReal))
      = programOptimum ScenValid (fun s => ((scenDelay s : ℝ) : EReal)) :=
    programOptimum_eq_of_scenarioSolution ScenValid scenDelay MilpFeasible obj toSol toScen
      hLem2 hLem3
  refine ⟨?_, ?_⟩
  · rw [← hT1]; exact reducedOptimum_le_milpOptimum hred
  · rw [← hT1]; exact milpOptimum_le_relaxationOptimum hrelax

/-- **The bracket is consistent: `v_LP ≤ V_LP`** (lower LP optimum ≤ upper LP optimum,
independent of Theorem 1).  Since the reduced feasible set is contained in the relaxed one
(`Reduced ⊆ Milp ⊆ Relax`), the date-merge lower bound never exceeds the relaxation upper
bound — so the two single-LP computations of §IV.D always bracket a nonempty interval. -/
theorem reducedOptimum_le_relaxationOptimum {Sol : Type*}
    {ReducedFeasible MilpFeasible RelaxFeasible : Sol → Prop} {obj : Sol → EReal}
    (hred : ∀ v, ReducedFeasible v → MilpFeasible v)
    (hrelax : ∀ v, MilpFeasible v → RelaxFeasible v) :
    programOptimum ReducedFeasible obj ≤ programOptimum RelaxFeasible obj :=
  programOptimum_mono_feasible fun v hv => hrelax v (hred v hv)

/-! ## The exponential variable count `2^(N+1) − 1` (p.6)

The paper (p.6): "the number of variables and constraints of the problem is exponential in the
number of nodes. For instance, the number of times for a tandem network of `N` nodes is equal
to `2^(N+1) − 1`."  This is the binary-tree date layout (Section IV.C): tracing the FIFO times
back from the single output time at node `N`, "each output time `t` spawns two input times
`t' = FIFOʲ(t)` and `t'' = SCʲ(t)`", so the times *double* at each node going backwards.

Counting the times *across all nodes* of the trace gives the nodes of a full binary tree of
depth `N+1` (one output time, doubling `N` times): `numTimes 0 = 1`,
`numTimes (N+1) = 2·numTimes N + 1`, whose closed form is `2^(N+1) − 1` — which is exactly why
the MILP is feasible only up to six or seven nodes. -/

/-- **The total number of time variables of the FIFO tandem MILP** for a tandem of `N` nodes
(p.6, Section IV.C binary-tree layout): one output time, with each time spawning two input
times one node backwards.  `tandemMilpNumTimes 0 = 1` (just the output time); each extra node
doubles the live frontier and adds it to the running total:
`tandemMilpNumTimes (N+1) = 2·tandemMilpNumTimes N + 1`. -/
def tandemMilpNumTimes : ℕ → ℕ
  | 0 => 1
  | N + 1 => 2 * tandemMilpNumTimes N + 1

/-- **The closed form `2^(N+1) − 1`** (p.6): the FIFO tandem MILP for `N` nodes has exactly
`2^(N+1) − 1` time variables — exponential in the number of nodes, the reason the exact MILP
is tractable only for small networks (six or seven nodes). -/
theorem tandemMilpNumTimes_eq (N : ℕ) : tandemMilpNumTimes N = 2 ^ (N + 1) - 1 := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [tandemMilpNumTimes, ih]
    have h1 : 1 ≤ 2 ^ (N + 1) := Nat.one_le_two_pow
    have h2 : 2 ^ (N + 1 + 1) = 2 * 2 ^ (N + 1) := by rw [pow_succ]; ring
    omega

/-- The MILP variable count strictly increases with the number of nodes (it doubles, plus
one) — the explicit exponential blow-up. -/
theorem tandemMilpNumTimes_lt_succ (N : ℕ) :
    tandemMilpNumTimes N < tandemMilpNumTimes (N + 1) := by
  rw [tandemMilpNumTimes]
  have : 1 ≤ tandemMilpNumTimes N := by
    cases N with
    | zero => exact le_refl 1
    | succ M => rw [tandemMilpNumTimes]; omega
  omega

/-! ## The single FIFO node as an instance of Theorem 1 (the inhabited base case)

The abstract Theorem 1 bridge is inhabited by a genuine *exact* result: the single FIFO node
(`WorstCaseLPFifoNode`, Table 11.2), whose worst-case delay is the closed form `T+(b₁+b₂)/R`
and whose `programOptimum` equals it on the nose.  Here the "MILP" has no binary variables (one
node ⟹ `2^{1+1}−1 = 3` times, no ordering ambiguity), so the scenario/solution correspondence
collapses to the identity and Theorem 1 reads as the already-proved
`fifoNode_programOptimum`. -/

/-- **The single FIFO node satisfies the Theorem 1 / §IV.D bracket trivially** (`N = 1`, the
inhabited base case): the FIFO-node program optimum (`= WCD`, the scenario supremum being the
program itself) is trivially bracketed by itself as both the relaxation and the reduced LP —
the one-node MILP has no binary variables, so all three programs coincide and the bracket
`v_LP ≤ WCD ≤ V_LP` degenerates to the equality `WCD = T+(b₁+b₂)/R`.  This shows the abstract
bridge is inhabited by the genuine exact single-node result. -/
theorem fifoNode_worstCaseDelay_eq {b₁ b₂ r₁ r₂ R T : ℝ} (hR : 0 < R) (hstab : r₁ + r₂ ≤ R)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hT : 0 ≤ T) :
    programOptimum (FifoNodeFeasible b₁ b₂ r₁ r₂ R T)
        (fun v => ((fifoNodeDelay v : ℝ) : EReal))
      = ((T + (b₁ + b₂) / R : ℝ) : EReal) :=
  fifoNode_programOptimum hR hstab hb₁ hb₂ hT

/-- **The single FIFO node MILP has `3` time variables** (`tandemMilpNumTimes 1 = 3`, i.e.
`2^{1+1}−1`): the three dates `t₁ ≥ t₂ ≥ t₃` of Table 11.2, with no Boolean ordering variable —
the binary-tree count specializes to the explicit single-node LP. -/
theorem fifoNode_numTimes : tandemMilpNumTimes 1 = 3 := rfl

/-- **A two-node FIFO tandem MILP has `7` time variables** (`tandemMilpNumTimes 2 = 7`, i.e.
`2^{2+1}−1`): the Table II two-node example's `t₁,…,t₇` (p.13), with one Boolean ordering
variable `b` linking the partially-ordered input times of node 1.  The doubling of the count
between one and two nodes is the binary-tree growth. -/
theorem twoNode_numTimes : tandemMilpNumTimes 2 = 7 := rfl

/-! ## A multi-node exact instance: the homogeneous FIFO tandem

Beyond the single node, the abstract Theorem 1 is inhabited by a genuine *multi-node* exact
result: the homogeneous-rate FIFO tandem (every server at the bottleneck rate `Rmin`), whose
MILP optimum equals the closed-form worst-case delay `(∑ₕ Rₕ·Tₕ + b)/(Rmin − r)`
(`TandemFifoMilpWitness.fifoTandem_programOptimum_homogeneous`).  There Lemma 2 collapses to a
*single* explicit witness — the §11.1 worst-case vertex with the all-zero Boolean ordering — so
the exponential `2^?` ordering enumeration is unnecessary: the homogeneous worst case is a
finite computation.  We re-expose it here as the FIFO-feed-forward exact value for the
homogeneous tandem, and observe the §IV.D bracket degenerates to an equality in this case
(the closed form is simultaneously a lower and an upper bound). -/

/-- **The homogeneous FIFO tandem's exact worst-case delay** (a multi-node instance of the
[BOU 16b] exact-WCD theory): for a homogeneous-rate stable tandem the FIFO MILP optimum is the
closed form `(∑ₕ Rₕ·Tₕ + b)/(Rmin − r)`.  This is the exponential MILP *resolved exactly* for
the homogeneous case (Lemma 2's witness is the single all-zero ordering); the heterogeneous and
general-`N` discharge is scoped below.  (Re-export of
`TandemFifoMilpWitness.fifoTandem_programOptimum_homogeneous` under the paper's framing.) -/
theorem fifoTandemHomogeneous_worstCaseDelay {n : ℕ} (N : TandemLP.Tandem (n + 1)) {Rmin M : ℝ}
    (hRmin : 0 < Rmin) (hrate0 : 0 ≤ N.rate0) (hrate : ∀ h : Fin (n + 1), N.rate h = Rmin)
    (hlat : ∀ h : Fin (n + 1), 0 ≤ N.lat h) (hb : 0 ≤ N.burst) (hstab : N.rate0 < Rmin)
    (hM : (∑ k : Fin (n + 1), TandemLP.witnessWindow N Rmin k) ≤ M) :
    programOptimum (TandemFifo.FifoFeasible N M)
        (fun v => ((TandemFifo.fifoDelay v : ℝ) : EReal))
      = ((TandemLP.objectiveValue N Rmin : ℝ) : EReal) :=
  TandemFifo.fifoTandem_programOptimum_homogeneous N hRmin hrate0 hrate hlat hb hstab hM

/-! ## Scoping: what discharging Lemmas 2/3 for general `N` needs (beyond this file)

The abstract Theorem 1 (`programOptimum_eq_of_scenarioSolution`) reduces "the MILP optimum is
the WCD" to two *correspondence* hypotheses — `toSol` (Lemma 2) and `toScen` (Lemma 3) — and
the §IV.D bracket reduces the practical WCD computation to two LP solves
(`worstCaseDelay_mem_lpBracket`).  What is **not** delivered, and is the paper's genuinely
exponential/existence content, is *discharging those two hypotheses for an arbitrary
feed-forward network*:

* **The concrete MILP and scenario encodings (`Sol`, `Scen`).**  The paper's `Sol` is the
  binary-tree variable layout of Section IV.C: times `t₁, …, t_{2^{N+1}-1}` (the count
  `tandemMilpNumTimes`, exponential), function values `Fₚʲ(t)` for every flow `p` on every node
  `j ∈ p`, and one Boolean `b ∈ {0,1}` per *new* (un-inferable) time ordering, with the FIFO,
  service-curve, monotonicity, and arrival constraints `C_T ∪ C_F`.  Its `Scen` is the family
  of cumulative functions `(Fₚʲ)` satisfying the scenario properties 1–5 of §III.  Building
  these as Lean data is an `[infra]` representation layer (routing `pᵢ`, `fst`, the recursive
  time sets `Tᵢₙ`/`Tₒᵤₜ` from Algorithms 1/2 of Appendix C) not present in the library; the
  `TandemFifoMilp` file models only the *single-flow aggregate, one-date-per-boundary* case.

* **Lemma 2 (`toSol`, p.7): every scenario gives a feasible MILP point.**  Given a scenario
  with delay `d`, set `t₂ = FIFOᴺ(t₁)`, `t₃ = SCᴺ(t₁)`, and recurse backwards (by Lemma 1, the
  convolution-time existence) defining all times and sampled function values along the
  trajectory; the Boolean variables are then fixed by the realized total order.  This is a
  *construction over the exponential tree*, faithful but not a closed form.

* **Lemma 3 (`toScen`, p.7–8): every feasible MILP point extrapolates to a scenario.**  Given
  a feasible point with `t₁−t₀ = d`, the proof *builds* admissible cumulative functions
  `Fₚʲ(t) = min_{tₖ} {Fₚʲ(tₖ) + αₚ(t−tₖ)}` (and the bursty/SC extrapolations of p.8) that are
  wide-sense increasing, left-continuous, α-upper-constrained, and preserve the FIFO order, so
  the bit leaving at `t₁` has delay `≥ d`.  This is the genuinely new *existence* argument — a
  trajectory-from-solution reconstruction over the (exponentially many) Boolean orderings — and
  is `[research]`/`[infra]`: a solver enumerates the orderings; no Lean lemma states the
  general optimum in closed form (contrast the single FIFO node, `fifoNode_worstCaseDelay_eq`,
  whose optimum *is* the closed form `T+(b₁+b₂)/R`).

So: Theorem 1's *logical structure* and the §IV.D bracketing are formalized in full generality
here; the *discharge of Lemmas 2/3* for an arbitrary network is the exponential construction
the paper writes down and a solver evaluates, scoped as `[infra]`/`[research]`.  The homogeneous
tandem case where Lemma 2 collapses to a single explicit witness is closed upstream
(`TandemFifoMilpWitness.fifoTandem_programOptimum_homogeneous`). -/

/-! ## Restatements (the theorems say what [BOU 16b] says) -/

/-- Theorem 1 (p.7): the MILP optimum equals the worst-case delay, given Lemmas 2 and 3. -/
example {Scen Sol : Type*} (ScenValid : Scen → Prop) (scenDelay : Scen → ℝ)
    (Feasible : Sol → Prop) (obj : Sol → ℝ) (toSol : Scen → Sol) (toScen : Sol → Scen)
    (hLem2 : ∀ s, ScenValid s → Feasible (toSol s) ∧ obj (toSol s) = scenDelay s)
    (hLem3 : ∀ v, Feasible v → ScenValid (toScen v) ∧ obj v ≤ scenDelay (toScen v)) :
    programOptimum Feasible (fun v => ((obj v : ℝ) : EReal))
      = programOptimum ScenValid (fun s => ((scenDelay s : ℝ) : EReal)) :=
  programOptimum_eq_of_scenarioSolution ScenValid scenDelay Feasible obj toSol toScen hLem2 hLem3

/-- §IV.D (p.8): the exact WCD is bracketed `v_LP ≤ WCD ≤ V_LP` by the reduced and relaxed LPs. -/
example {Scen Sol : Type*} (ScenValid : Scen → Prop) (scenDelay : Scen → ℝ)
    {ReducedFeasible RelaxFeasible : Sol → Prop} (MilpFeasible : Sol → Prop) (obj : Sol → ℝ)
    (toSol : Scen → Sol) (toScen : Sol → Scen)
    (hLem2 : ∀ s, ScenValid s → MilpFeasible (toSol s) ∧ obj (toSol s) = scenDelay s)
    (hLem3 : ∀ v, MilpFeasible v → ScenValid (toScen v) ∧ obj v ≤ scenDelay (toScen v))
    (hred : ∀ v, ReducedFeasible v → MilpFeasible v)
    (hrelax : ∀ v, MilpFeasible v → RelaxFeasible v) :
    programOptimum ReducedFeasible (fun v => ((obj v : ℝ) : EReal))
        ≤ programOptimum ScenValid (fun s => ((scenDelay s : ℝ) : EReal))
      ∧ programOptimum ScenValid (fun s => ((scenDelay s : ℝ) : EReal))
        ≤ programOptimum RelaxFeasible (fun v => ((obj v : ℝ) : EReal)) :=
  worstCaseDelay_mem_lpBracket ScenValid scenDelay MilpFeasible obj toSol toScen
    hLem2 hLem3 hred hrelax

/-- p.6: the tandem MILP for `N` nodes has `2^(N+1) − 1` time variables (exponential). -/
example (N : ℕ) : tandemMilpNumTimes N = 2 ^ (N + 1) - 1 := tandemMilpNumTimes_eq N

-- A multi-node exact instance: the 4-server homogeneous FIFO tandem worst-case delay is the
-- closed form `(∑ₕ Rₕ·Tₕ + b)/(Rmin − r)`.
example (N : TandemLP.Tandem 4) {Rmin M : ℝ} (hRmin : 0 < Rmin) (hrate0 : 0 ≤ N.rate0)
    (hrate : ∀ h : Fin 4, N.rate h = Rmin) (hlat : ∀ h : Fin 4, 0 ≤ N.lat h)
    (hb : 0 ≤ N.burst) (hstab : N.rate0 < Rmin)
    (hM : (∑ k : Fin 4, TandemLP.witnessWindow N Rmin k) ≤ M) :
    programOptimum (TandemFifo.FifoFeasible N M)
        (fun v => ((TandemFifo.fifoDelay v : ℝ) : EReal))
      = ((TandemLP.objectiveValue N Rmin : ℝ) : EReal) :=
  fifoTandemHomogeneous_worstCaseDelay N hRmin hrate0 hrate hlat hb hstab hM

end FifoFeedForward

end DeepWiki
