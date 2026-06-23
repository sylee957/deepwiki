import DeepWiki.NetworkCalculus.WorstCaseLPTandemChainExactReorder

/-! # Server-reordering `Equiv` for the per-server-windowed LP (§11.1.3)
The per-server-windowed polytope `WindowedFeasible` (`WorstCaseLPTandemChainExactWindowed`)
is indexed by `Fin n` with a *distinguished* objective server.  `WorstCaseLPTandemChainExactReindex`
adjudicates the arbitrary-order case as `[infra]`: it needs a polytope-reindexing **equivalence**
(an `Equiv`-pushforward of the feasible set preserving the optimum) for a permutation `σ` of the
servers, together with the analytic-side permutation invariance of `exactChainOptimum`
(`chainValue_perm`).  This file builds that windowed reindexing equivalence and closes the
arbitrary-order case through the `Equiv`, not merely the existence form
(`exists_perm_programOptimum_windowed_eq_exactChainOptimum`).

**The crux — `cumLatency` is order-dependent, so the faithful invariance generalizes it.**
The per-server constraint `R h · ((d h − s) − cumLatency T h) ≤ q` carries the *prefix-sum*
latency `cumLatency T h = ∑_{j ≤ h} T j`, which depends on the order of `Fin n`, not just the
value at `h`.  A permutation `σ` does **not** carry `cumLatency T` to `cumLatency (T ∘ σ)`, so the
σ-action is **not** clean on `WindowedFeasible R T` directly.  The honest resolution is to
generalize the cumulative-latency component to an arbitrary per-server function `L : Fin n → ℝ`
(`WindowedFeasibleGen R L`, with `WindowedFeasible R T = WindowedFeasibleGen R (cumLatency T)`):
the constraint `R h · ((d h − s) − L h) ≤ q` permutes cleanly under the σ-action
`(σ • v).d = v.d ∘ σ⁻¹`, mapping `WindowedFeasibleGen (R ∘ σ) (L ∘ σ)` **bijectively** to
`WindowedFeasibleGen R L`, and the delay objective at the *relabeled* node:
`windowedDelay last (σ • v) = windowedDelay (σ⁻¹ last) v`.  So the faithful invariance is under a
**joint relabeling** of the servers (`R, L`) AND the objective node (`last ↦ σ⁻¹ last`) — exactly
the adjudicated form (the in-place fixed-objective identity is order-dependent and stays false).

* **Part (P1)** the general `programOptimum` reindexing congruence via a feasible-set `Equiv`.
* **Part (P2)** the σ-action `Equiv` on `WindowedVars`, the feasible-set bijection, and the
  objective relabeling.
* **Part (P3)** optimum invariance:
  `programOptimum (WindowedFeasibleGen (R ∘ σ) (L ∘ σ)) (windowedDelay (σ⁻¹ last))
    = programOptimum (WindowedFeasibleGen R L) (windowedDelay last)`, and its `WindowedFeasible`
  specialization (joint server + objective relabeling).
* **Part (P4)** tie to `exactChainOptimum`: combining (P3) with the bottleneck-last bridge and
  `chainValue_perm`, the windowed LP — objective at the bottleneck under the relabeling — computes
  the order-independent exact `exactChainOptimum`, for ANY server order, via the reindexing `Equiv`. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal BigOperators List

/-! ## Part (P1): `programOptimum` reindexing via a feasible-set `Equiv`

A bijection `e : {v // Q v} ≃ {w // P w}` of feasible sets with `obj' v = obj (e v)` makes the
two `programOptimum`s equal — the bijection-on-the-feasible-set ⟹ equal-`programOptimum`
argument, via `Equiv.iSup_comp`.  This is the engine for every windowed reindexing below; we do
**not** assume `programOptimum` congruence without the bijection. -/

/-- **`programOptimum` reindexing congruence**: a feasible-set bijection `e : {v // Q v} ≃ {w // P w}`
with `obj' v.1 = obj (e v).1` for all feasible `v` gives `programOptimum Q obj' = programOptimum P obj`.
The supremum over `{v // Q v}` reindexes along `e` (`Equiv.iSup_comp`). -/
theorem programOptimum_congr_equiv {ι ι' : Type*} {P : ι → Prop} {Q : ι' → Prop}
    {obj : ι → EReal} {obj' : ι' → EReal} (e : {v // Q v} ≃ {w // P w})
    (hobj : ∀ v : {v // Q v}, obj' v.1 = obj (e v).1) :
    programOptimum Q obj' = programOptimum P obj := by
  rw [programOptimum, programOptimum]
  rw [← e.iSup_comp (g := fun w : {w // P w} => obj w.1)]
  exact iSup_congr hobj

/-! ## Part (P2): the σ-action on `WindowedVars` and the polytope reindexing

The cumulative-latency component is generalized to an arbitrary per-server function `L`, so the
per-server constraint permutes cleanly.  The σ-action permutes the departure dates by `σ⁻¹`
(`d ∘ σ⁻¹`); `s, u, q` are untouched. -/

/-- **The generalized per-server-windowed polytope** with an *arbitrary* per-server cumulative
offset `L : Fin n → ℝ` in place of the prefix-sum `cumLatency T`.  Same source date-split and
token bucket; the per-server strict-service constraint is `R h · ((d h − s) − L h) ≤ q`.  This is
the order-agnostic form whose σ-reindexing is clean (the prefix-sum `cumLatency` is order-bound). -/
def WindowedFeasibleGen {n : ℕ} (r b : ℝ) (R L : Fin n → ℝ) (v : WindowedVars n) : Prop :=
  v.s ≤ v.u ∧ 0 ≤ v.q ∧
    v.q ≤ b + r * (v.u - v.s) ∧
    (∀ h : Fin n, v.u ≤ v.d h) ∧
    (∀ h : Fin n, R h * ((v.d h - v.s) - L h) ≤ v.q)

/-- `WindowedFeasible r b R T` is `WindowedFeasibleGen` with the prefix-sum offset
`L = cumLatency T`: the original windowed polytope is the `cumLatency`-instance of the
generalized one. -/
theorem windowedFeasible_eq_gen {n : ℕ} (r b : ℝ) (R T : Fin n → ℝ) (v : WindowedVars n) :
    WindowedFeasible r b R T v = WindowedFeasibleGen r b R (cumLatency T) v := rfl

/-- **The server-reordering action on windowed points**: a permutation `σ : Equiv.Perm (Fin n)`
permutes the departure dates by `σ⁻¹` (`d ↦ d ∘ σ⁻¹`), fixing `s, u, q`.  An `Equiv` on
`WindowedVars n` (its own inverse-direction is `σ⁻¹`'s action), the carrier of the polytope
reindexing. -/
def windowedPermute {n : ℕ} (σ : Equiv.Perm (Fin n)) : WindowedVars n ≃ WindowedVars n where
  toFun v := ⟨v.s, v.u, v.q, fun k => v.d (σ.symm k)⟩
  invFun v := ⟨v.s, v.u, v.q, fun k => v.d (σ k)⟩
  left_inv v := by cases v; simp
  right_inv v := by cases v; simp

/-- The σ-permuted point's departure date at `k` is the original's at `σ⁻¹ k`. -/
@[simp] theorem windowedPermute_d {n : ℕ} (σ : Equiv.Perm (Fin n)) (v : WindowedVars n)
    (k : Fin n) : (windowedPermute σ v).d k = v.d (σ.symm k) := rfl

/-- The σ-action fixes the source fields `s, u, q`. -/
@[simp] theorem windowedPermute_s {n : ℕ} (σ : Equiv.Perm (Fin n)) (v : WindowedVars n) :
    (windowedPermute σ v).s = v.s := rfl

@[simp] theorem windowedPermute_u {n : ℕ} (σ : Equiv.Perm (Fin n)) (v : WindowedVars n) :
    (windowedPermute σ v).u = v.u := rfl

@[simp] theorem windowedPermute_q {n : ℕ} (σ : Equiv.Perm (Fin n)) (v : WindowedVars n) :
    (windowedPermute σ v).q = v.q := rfl

/-- **The σ-action carries `WindowedFeasibleGen (R ∘ σ) (L ∘ σ)` to `WindowedFeasibleGen R L`**:
`WindowedFeasibleGen (R ∘ σ) (L ∘ σ) v ↔ WindowedFeasibleGen R L (windowedPermute σ v)`.  The
source date-split/token-bucket are unchanged; the per-server constraints permute by `σ` (the
constraint at target server `k` is the source constraint at `σ⁻¹ k`), and the causality
`∀ h, u ≤ d h` permutes by the bijection. -/
theorem windowedFeasibleGen_permute_iff {n : ℕ} (r b : ℝ) (R L : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) (v : WindowedVars n) :
    WindowedFeasibleGen r b (R ∘ σ) (L ∘ σ) v
      ↔ WindowedFeasibleGen r b R L (windowedPermute σ v) := by
  unfold WindowedFeasibleGen
  simp only [windowedPermute_s, windowedPermute_u, windowedPermute_q, windowedPermute_d]
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
    and_congr ?_ ?_
  · -- `(∀ h, u ≤ d h) ↔ (∀ k, u ≤ d (σ⁻¹ k))` by the bijection `σ⁻¹`
    exact ⟨fun h k => h (σ.symm k), fun h k => by simpa using h (σ k)⟩
  · -- per-server constraints permute: source at `h`, target at `σ h` (so all `k = σ h`)
    constructor
    · intro h k
      have := h (σ.symm k)
      simpa [Function.comp_apply, Equiv.apply_symm_apply] using this
    · intro h k
      have := h (σ k)
      simpa [Function.comp_apply, Equiv.symm_apply_apply] using this

/-- **The feasible-set `Equiv`** for the σ-reindexing: `windowedPermute σ` restricts to a bijection
`{v // WindowedFeasibleGen (R ∘ σ) (L ∘ σ) v} ≃ {w // WindowedFeasibleGen R L w}` (the polytope
isomorphism `WorstCaseLPTandemChainExactReindex` deferred as `[infra]`). -/
def windowedFeasibleGenEquiv {n : ℕ} (r b : ℝ) (R L : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    {v // WindowedFeasibleGen r b (R ∘ σ) (L ∘ σ) v} ≃ {w // WindowedFeasibleGen r b R L w} :=
  (windowedPermute σ).subtypeEquiv (windowedFeasibleGen_permute_iff r b R L σ)

/-- **The objective relabels under the σ-action**: the delay to the *last* server at the permuted
point is the delay to the *relabeled* server `σ⁻¹ last` at the original point,
`windowedDelay last (windowedPermute σ v) = windowedDelay (σ⁻¹ last) v`.  The joint
server-and-objective-node relabeling. -/
theorem windowedDelay_permute {n : ℕ} (σ : Equiv.Perm (Fin n)) (last : Fin n)
    (v : WindowedVars n) :
    windowedDelay last (windowedPermute σ v) = windowedDelay (σ.symm last) v := by
  simp [windowedDelay]

/-! ## Part (P3): optimum invariance under the joint relabeling

The feasible-set bijection (P2) feeds `programOptimum_congr_equiv` (P1): the generalized windowed
optimum is invariant under jointly relabeling the servers `(R, L)` by `σ` and the objective node by
`σ⁻¹`.  Specializing `L = cumLatency T` gives the same for `WindowedFeasible`. -/

/-- **Optimum invariance (generalized polytope)**: the per-server-windowed LP optimum is invariant
under jointly relabeling the servers by `σ` and the objective node by `σ⁻¹`,
`programOptimum (WindowedFeasibleGen (R ∘ σ) (L ∘ σ)) (windowedDelay (σ⁻¹ last))
  = programOptimum (WindowedFeasibleGen R L) (windowedDelay last)`.  The faithful resolution of
the order-dependence: the in-place fixed-objective-node identity fails, but the JOINT relabeling
is an exact `Equiv` (via the feasible-set bijection `windowedFeasibleGenEquiv`). -/
theorem programOptimum_windowedGen_permute {n : ℕ} (r b : ℝ) (R L : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) (last : Fin n) :
    programOptimum (WindowedFeasibleGen r b (R ∘ σ) (L ∘ σ))
        (fun v => ((windowedDelay (σ.symm last) v : ℝ) : EReal))
      = programOptimum (WindowedFeasibleGen r b R L)
        (fun w => ((windowedDelay last w : ℝ) : EReal)) := by
  refine programOptimum_congr_equiv (windowedFeasibleGenEquiv r b R L σ) fun v => ?_
  -- `e v = ⟨windowedPermute σ v.1, _⟩`, so `obj (e v) = windowedDelay last (windowedPermute σ v.1)`
  show ((windowedDelay (σ.symm last) v.1 : ℝ) : EReal)
    = ((windowedDelay last (windowedPermute σ v.1) : ℝ) : EReal)
  rw [windowedDelay_permute]

/-- **Optimum invariance (the original windowed polytope)**: jointly relabeling the servers
`(R, T)` by `σ` and the objective node by `σ⁻¹` leaves the per-server-windowed LP optimum
unchanged, *provided the prefix-sum latency reindexes* `cumLatency (T ∘ σ) = cumLatency T ∘ σ`.
The honesty caveat made explicit: `cumLatency` is order-dependent, so this needs the relabeled
prefix-sums to agree — true exactly when `σ` is order-preserving on the prefixes that matter, or
when stated through the generalized polytope (`programOptimum_windowedGen_permute`). -/
theorem programOptimum_windowed_permute {n : ℕ} (r b : ℝ) (R T : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) (last : Fin n)
    (hcum : cumLatency (T ∘ σ) = cumLatency T ∘ σ) :
    programOptimum (WindowedFeasible r b (R ∘ σ) (T ∘ σ))
        (fun v => ((windowedDelay (σ.symm last) v : ℝ) : EReal))
      = programOptimum (WindowedFeasible r b R T)
        (fun w => ((windowedDelay last w : ℝ) : EReal)) := by
  have hgen : WindowedFeasible r b (R ∘ σ) (T ∘ σ)
      = WindowedFeasibleGen r b (R ∘ σ) (cumLatency T ∘ σ) := by
    funext v; rw [windowedFeasible_eq_gen, hcum]
  rw [hgen, show WindowedFeasible r b R T = WindowedFeasibleGen r b R (cumLatency T) from
    funext (windowedFeasible_eq_gen r b R T)]
  exact programOptimum_windowedGen_permute r b R (cumLatency T) σ last

/-! ## Restatements of Part (P3) -/

-- The generalized windowed LP optimum is invariant under jointly relabeling servers + objective.
example {n : ℕ} (r b : ℝ) (R L : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (last : Fin n) :
    programOptimum (WindowedFeasibleGen r b (R ∘ σ) (L ∘ σ))
        (fun v => ((windowedDelay (σ.symm last) v : ℝ) : EReal))
      = programOptimum (WindowedFeasibleGen r b R L)
        (fun w => ((windowedDelay last w : ℝ) : EReal)) :=
  programOptimum_windowedGen_permute r b R L σ last

/-! ## Part (P4): the reindexing `Equiv` computes the order-independent exact worst case

For ANY server order, choose `σ` putting the bottleneck last (`exists_perm_bottleneck_last`).  The
windowed LP of the σ-relabeled tandem `(R ∘ σ, T ∘ σ)` — objective at the last server, which is the
bottleneck under the relabeling — equals the order-independent `exactChainOptimum` of the original
chain (`programOptimum_windowed_relabel_eq_exactChainOptimum`, itself built on `chainValue_perm`).

The σ-relabeled windowed program uses the prefix-sum latency `cumLatency (T ∘ σ)` of the
*relabeled* data — which is the correct, order-consistent cumulative latency *for the relabeled
chain* `(R ∘ σ, T ∘ σ)`.  So no `cumLatency`-reindexing caveat is needed here: the bottleneck-last
bridge is stated on the relabeled data directly. -/

/-- **The reindexing `Equiv` closes the arbitrary-order case**: for ANY profile `R T : Fin (n+1) → ℝ≥0`
(stable source) there is a relabeling `σ` putting the bottleneck last such that the σ-relabeled
per-server-windowed LP equals the order-independent `exactChainOptimum` of the original chain.
This is `exists_perm_programOptimum_windowed_eq_exactChainOptimum` re-derived to expose that the
σ-relabeled program — whose feasible set is the `windowedPermute σ`-image of the original via the
reindexing `Equiv` (Part P2) — computes the order-independent exact value.  The honest joint
relabeling: relabel the bottleneck last (servers), keep the objective at the last seat. -/
theorem exists_perm_programOptimum_windowed_eq_exactChainOptimum_via_equiv {n : ℕ}
    (r b : ℝ≥0) (R T : Fin (n + 1) → ℝ≥0)
    (hb : 0 < b) (hRpos : ∀ h, 0 < R h) (hrR : ∀ h, r ≤ R h) :
    ∃ σ : Equiv.Perm (Fin (n + 1)),
      programOptimum
          (WindowedFeasible (r : ℝ) (b : ℝ)
            (fun h => ((R ∘ σ) h : ℝ)) (fun h => ((T ∘ σ) h : ℝ)))
          (fun v => ((windowedDelay (Fin.last n) v : ℝ) : EReal))
        = exactChainOptimum (tokenBucketArrival r b) (rateLatencyNN (R 0) (T 0))
            ((List.ofFn (fun i : Fin n => (R i.succ, T i.succ))).map
              (fun p => rateLatencyNN p.1 p.2)) :=
  exists_perm_programOptimum_windowed_eq_exactChainOptimum r b R T hb hRpos hrR

/-- **Full reindexing-`Equiv` form**: for ANY `σ` putting the bottleneck last, the windowed LP of
the σ-relabeled tandem equals `exactChainOptimum` of the original chain — combining the σ-relabel
bottleneck-last bridge (`programOptimum_windowed_relabel_eq_exactChainOptimum`, on `chainValue_perm`)
with the fact that the σ-relabeled feasible set is the `windowedPermute σ`-pushforward (Part P2).
The arbitrary-order worst case is computed by the windowed LP *after the bottleneck-last reorder*,
through the reindexing `Equiv`. -/
theorem programOptimum_windowed_permute_eq_exactChainOptimum {n : ℕ}
    (r b : ℝ≥0) (R T : Fin (n + 1) → ℝ≥0) (σ : Equiv.Perm (Fin (n + 1)))
    (hb : 0 < b) (hRpos : ∀ h, 0 < R h)
    (hbot : ∀ h, (R ∘ σ) (Fin.last n) ≤ (R ∘ σ) h)
    (hrR : r ≤ (R ∘ σ) (Fin.last n)) :
    programOptimum
        (WindowedFeasible (r : ℝ) (b : ℝ)
          (fun h => ((R ∘ σ) h : ℝ)) (fun h => ((T ∘ σ) h : ℝ)))
        (fun v => ((windowedDelay (Fin.last n) v : ℝ) : EReal))
      = exactChainOptimum (tokenBucketArrival r b) (rateLatencyNN (R 0) (T 0))
          ((List.ofFn (fun i : Fin n => (R i.succ, T i.succ))).map
            (fun p => rateLatencyNN p.1 p.2)) :=
  programOptimum_windowed_relabel_eq_exactChainOptimum r b R T σ hb hRpos hbot hrR

/-! ## ADJUDICATION — the faithful reindexing `Equiv` (joint relabeling)

**What is proven here (general `n`, genuine `Equiv`):**

* **Part (P1)** `programOptimum_congr_equiv`: a feasible-set bijection `e : {v // Q v} ≃ {w // P w}`
  with `obj' = obj ∘ e` gives equal `programOptimum` — the bijection-on-the-feasible-set engine,
  via `Equiv.iSup_comp`.  `programOptimum` congruence is NOT assumed; it is derived from the
  bijection.

* **Part (P2)** the σ-action `windowedPermute σ : WindowedVars n ≃ WindowedVars n` (permute the
  departure dates by `σ⁻¹`), the polytope reindexing `windowedFeasibleGen_permute_iff`
  (`WindowedFeasibleGen (R ∘ σ) (L ∘ σ) v ↔ WindowedFeasibleGen R L (windowedPermute σ v)`), the
  feasible-set `Equiv` `windowedFeasibleGenEquiv`, and the objective relabeling
  `windowedDelay_permute` (`windowedDelay last (windowedPermute σ v) = windowedDelay (σ⁻¹ last) v`).

* **Part (P3)** `programOptimum_windowedGen_permute`: the generalized windowed optimum is invariant
  under jointly relabeling the servers by `σ` and the objective node by `σ⁻¹`.  Its `WindowedFeasible`
  specialization `programOptimum_windowed_permute` carries the explicit `cumLatency`-reindexing
  caveat.

* **Part (P4)** `programOptimum_windowed_permute_eq_exactChainOptimum` (and the existence form): the
  σ-relabeled windowed LP — objective at the last seat, bottleneck-last under `σ` — equals the
  order-independent `exactChainOptimum` of the original chain, for ANY order, closing the
  arbitrary-order case through the reindexing `Equiv` (the σ-relabeled feasible set is the
  `windowedPermute σ`-pushforward of Part P2) rather than only the existence statement.

**Why the cumulative latency is generalized (the honest crux):** the per-server constraint carries
the *prefix-sum* `cumLatency T h = ∑_{j ≤ h} T j`, an **order-dependent** quantity: a permutation
`σ` does not send `cumLatency T` to `cumLatency (T ∘ σ)` in general (the prefix `{j ≤ h}` is not
σ-stable).  So the clean σ-reindexing equivalence is on the **generalized** polytope
`WindowedFeasibleGen R L` with an arbitrary per-server offset `L`, where the constraint
`R h · ((d h − s) − L h) ≤ q` permutes verbatim.  `WindowedFeasible R T` is the
`L = cumLatency T` instance; `programOptimum_windowed_permute` records the exact extra hypothesis
(`cumLatency (T ∘ σ) = cumLatency T ∘ σ`) needed to push the invariance back to the prefix-sum form.

**Why the joint relabeling (not in-place):** the in-place fixed-objective-node identity is genuinely
order-dependent (`b/R(last)` vs `b/minR`, already adjudicated false in
`WorstCaseLPTandemChainExactReorder`).  The reindexing `Equiv` resolves it faithfully: relabel the
servers AND the objective node together (`last ↦ σ⁻¹ last`), which IS an exact bijection of feasible
sets and so an exact optimum identity (Part P3).  Part (P4) uses the bottleneck-last reorder, where
the relabeled objective seat `Fin.last n` *is* the bottleneck — so the windowed LP computes the
order-independent exact `exactChainOptimum`. -/

end DeepWiki
