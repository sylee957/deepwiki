import DeepWiki.NetworkCalculus.WorstCaseLPTandemChainExactWindowed

/-! # `Fin (n+1)`↔`List` reindexing for the general-`n` windowed↔analytic bridge
The per-server-windowed LP (`WorstCaseLPTandemChainExactWindowed`) indexes its `n + 1`
servers by `Fin (n + 1)`; the analytic `exactChainOptimum_tokenBucketNN_rateLatencyNN`
(`WorstCaseLPTandemChainExact`) indexes a chain by a *head* `(R₀, T₀)` plus a `List`
tail `ps`.  Both closed forms are the same value, but identifying them for **general
`n`** needs the reindexing `ps := List.ofFn (fun i : Fin n => (R i.succ, T i.succ))`:

* `(∑ₕ T h) = T₀ + (ps.map Prod.snd).sum` — the latency sum (pure `Fin.sum_univ_succ`
  + `List.map_ofFn`/`List.sum_ofFn` bookkeeping, no math);
* `ps.foldr (· ⊓ ·) R₀ = R (Fin.last n)` **under the bottleneck-last hypothesis**
  `∀ h, R (Fin.last n) ≤ R h` — the `foldr`-min over the chain equals the bottleneck
  rate, which (and only which) the *last* server realizes.

These are the genuinely no-math reindexing identities.  The general-`n` bridge
`programOptimum_windowed_last = exactChainOptimum` then follows **under the
bottleneck-last hypothesis** (Part R3), generalizing the `n = 2` instance
`programOptimum_windowed_two_eq_exactChainOptimum`.

**Honesty:** the windowed-`last` optimum is `(∑T) + b/R(Fin.last n)` — the delay to the
*last* server — whereas `exactChainOptimum` uses `b/minR`.  They agree *iff the last
server is the bottleneck*.  The unrestricted (arbitrary-order) identity needs a server
*reorder* (Part R4 adjudication); it is NOT claimed here. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal BigOperators

/-! ## Part (R1): the `foldr`-min over a list as an infimum bound

Two generic order lemmas about `List.foldr (· ⊓ ·) z` over a `SemilatticeInf` carrier:
it is a lower bound below each element and below `z`, and conversely `c ≤ foldr` whenever
`c` lies below `z` and every element.  Used to identify the chain's `foldr`-min rate with
the bottleneck rate. -/

/-- `foldr (· ⊓ ·) z l ≤ z`: the `foldr`-min never exceeds the seed. -/
theorem foldrInf_le_init {α : Type*} [SemilatticeInf α] (z : α) :
    ∀ l : List α, l.foldr (· ⊓ ·) z ≤ z
  | [] => le_rfl
  | _ :: l => le_trans inf_le_right (foldrInf_le_init z l)

/-- `foldr (· ⊓ ·) z l ≤ a` for every `a ∈ l`: the `foldr`-min is below each element. -/
theorem foldrInf_le_of_mem {α : Type*} [SemilatticeInf α] (z : α) :
    ∀ {l : List α} {a : α}, a ∈ l → l.foldr (· ⊓ ·) z ≤ a
  | b :: l, a, ha => by
    rcases List.mem_cons.mp ha with h | h
    · subst h; exact inf_le_left
    · exact le_trans inf_le_right (foldrInf_le_of_mem z h)

/-- `c ≤ foldr (· ⊓ ·) z l` whenever `c ≤ z` and `c ≤ a` for every `a ∈ l`: the
`foldr`-min is the greatest lower bound. -/
theorem le_foldrInf {α : Type*} [SemilatticeInf α] (z c : α) :
    ∀ {l : List α}, c ≤ z → (∀ a ∈ l, c ≤ a) → c ≤ l.foldr (· ⊓ ·) z
  | [], hz, _ => hz
  | a :: _, hz, hmem =>
      le_inf (hmem a List.mem_cons_self)
        (le_foldrInf z c hz fun b hb => hmem b (List.mem_cons_of_mem _ hb))

/-- The `(fun p R => p.1 ⊓ R)` chain-`foldr` over a list of `(rate, latency)` pairs equals
the plain `(· ⊓ ·)` `foldr` over the projected rate list: the latency component is inert. -/
theorem foldr_fst_inf_eq_map {α β : Type*} [SemilatticeInf α] (z : α) :
    ∀ l : List (α × β),
      l.foldr (fun p R => p.1 ⊓ R) z = (l.map Prod.fst).foldr (· ⊓ ·) z
  | [] => rfl
  | a :: l => by rw [List.map_cons, List.foldr_cons, List.foldr_cons, foldr_fst_inf_eq_map z l]

/-! ## Part (R2): the two reindexing identities

For `R T : Fin (n + 1) → ℝ≥0`, set the chain head `(R 0, T 0)` and the tail
`ps = List.ofFn (fun i : Fin n => (R i.succ, T i.succ))`.  These are the `Fin`↔`List`
bookkeeping identities the analytic closed form needs. -/

/-- **Latency-sum reindexing**: `∑ₕ T h = T 0 + (ps.map Prod.snd).sum` for the tail list
`ps = ofFn (fun i => (R i.succ, T i.succ))` — pure `Fin.sum_univ_succ` + `List.map_ofFn`
+ `List.sum_ofFn`, no math content. -/
theorem sum_eq_head_add_tail {n : ℕ} (R T : Fin (n + 1) → ℝ≥0) :
    (∑ h, T h)
      = T 0 + ((List.ofFn (fun i : Fin n => (R i.succ, T i.succ))).map Prod.snd).sum := by
  rw [Fin.sum_univ_succ, List.map_ofFn, List.sum_ofFn]
  rfl

/-- **Bottleneck-rate reindexing**: under the bottleneck-last hypothesis
`∀ h, R (Fin.last n) ≤ R h`, the chain's `foldr`-min rate equals the last server's rate,
`ps.foldr (· ⊓ ·) (R 0) = R (Fin.last n)`.  The last rate is `≤` every chain rate (so
`≤` their `foldr`-min), and it occurs in the chain (so the `foldr`-min is `≤` it). -/
theorem foldrInf_rate_eq_last {n : ℕ} (R T : Fin (n + 1) → ℝ≥0)
    (hbot : ∀ h, R (Fin.last n) ≤ R h) :
    (List.ofFn (fun i : Fin n => (R i.succ, T i.succ))).foldr
        (fun p R => p.1 ⊓ R) (R 0)
      = R (Fin.last n) := by
  -- project to the plain `(· ⊓ ·)` `foldr` over the rate list `ofFn (R ·.succ)`
  rw [foldr_fst_inf_eq_map, List.map_ofFn]
  refine le_antisymm ?_ ?_
  · -- the `foldr`-min ≤ R(last): R(last) occurs in the projected rate list (or is R 0)
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [Fin.last_zero]
    · -- n ≥ 1: `R (Fin.last n) = R ((Fin.last (n-1)).succ)` is in `ofFn (R ·.succ)`
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
      apply foldrInf_le_of_mem
      rw [List.mem_ofFn]
      exact ⟨Fin.last m, by rw [Function.comp_apply, Fin.succ_last]⟩
  · -- R(last) ≤ the `foldr`-min: R(last) ≤ R 0 and ≤ every projected rate
    refine le_foldrInf _ _ (hbot 0) ?_
    intro a ha
    rw [List.mem_ofFn] at ha
    obtain ⟨i, rfl⟩ := ha
    exact hbot i.succ

/-! ## Restatements of the reindexing identities -/

-- The latency sum reindexes to `head + tail-sum` of the `ofFn` chain list.
example {n : ℕ} (R T : Fin (n + 1) → ℝ≥0) :
    (∑ h, T h)
      = T 0 + ((List.ofFn (fun i : Fin n => (R i.succ, T i.succ))).map Prod.snd).sum :=
  sum_eq_head_add_tail R T

-- Under bottleneck-last, the chain's `foldr`-min rate is the last server's rate.
example {n : ℕ} (R T : Fin (n + 1) → ℝ≥0) (hbot : ∀ h, R (Fin.last n) ≤ R h) :
    (List.ofFn (fun i : Fin n => (R i.succ, T i.succ))).foldr
        (fun p R => p.1 ⊓ R) (R 0)
      = R (Fin.last n) :=
  foldrInf_rate_eq_last R T hbot

/-! ## Part (R3): the general-`n` windowed↔analytic bridge (bottleneck last)

Feeding the `Fin (n + 1)`-indexed rate-latency data `R T : Fin (n + 1) → ℝ≥0` (cast to
`ℝ` on the windowed side) and reindexing the chain as head `(R 0, T 0)` + tail
`ps = ofFn (fun i => (R i.succ, T i.succ))`, the per-server-windowed LP optimum (delay to
the *last* server) **equals** the analytic relaxation-free `exactChainOptimum`, both
`(∑ₕ T h) + b/(R (Fin.last n))`, **under the bottleneck-last hypothesis**
`∀ h, R (Fin.last n) ≤ R h`.  This is `programOptimum_windowed_two_eq_exactChainOptimum`
generalized to all `n`; the two reindexing identities (R2) are exactly what closes the
`Fin`↔`List` gap. -/

/-- **The general-`n` per-server-windowed LP optimum equals the analytic `exactChainOptimum`**
(bottleneck last): for `R T : Fin (n + 1) → ℝ≥0` with the last server the bottleneck
(`∀ h, R (Fin.last n) ≤ R h`, so its rate is `minₕ R h`) and a stable source
(`0 < b`, `r ≤ R (Fin.last n)`, all `0 < R h`), the multi-window program's optimum
(`programOptimum_windowed_last`) *is* the relaxation-free `exactChainOptimum` of the
rate-latency chain `β_{R 0,T 0} :: ofFn (β_{R i.succ, T i.succ})`, both
`(∑ₕ T h) + b/(R (Fin.last n))`.  The general-`n` counterpart of
`programOptimum_windowed_two_eq_exactChainOptimum`. -/
theorem programOptimum_windowed_last_eq_exactChainOptimum {n : ℕ}
    (r b : ℝ≥0) (R T : Fin (n + 1) → ℝ≥0)
    (hb : 0 < b) (hRpos : ∀ h, 0 < R h) (hbot : ∀ h, R (Fin.last n) ≤ R h)
    (hrR : r ≤ R (Fin.last n)) :
    programOptimum
        (WindowedFeasible (r : ℝ) (b : ℝ) (fun h => (R h : ℝ)) (fun h => (T h : ℝ)))
        (fun v => ((windowedDelay (Fin.last n) v : ℝ) : EReal))
      = exactChainOptimum (tokenBucketArrival r b) (rateLatencyNN (R 0) (T 0))
          ((List.ofFn (fun i : Fin n => (R i.succ, T i.succ))).map
            (fun p => rateLatencyNN p.1 p.2)) := by
  set ps := List.ofFn (fun i : Fin n => (R i.succ, T i.succ)) with hps
  -- positivity / nonnegativity of the `ℝ`-cast `Fin (n+1)`-indexed data
  have hRpos' : ∀ h : Fin (n + 1), 0 < ((fun h => (R h : ℝ)) h) := fun h => by
    exact_mod_cast hRpos h
  have hT' : ∀ h : Fin (n + 1), 0 ≤ ((fun h => (T h : ℝ)) h) := fun h => (T h).coe_nonneg
  -- LHS: the windowed-last optimum `(∑ₕ T h) + b / R(last)` (cast to ℝ then EReal)
  have hLHS := programOptimum_windowed_last (n := n) (r := (r : ℝ)) (b := (b : ℝ))
    (R := fun h => (R h : ℝ)) (T := fun h => (T h : ℝ)) hRpos'
    (by exact_mod_cast hrR) b.coe_nonneg hT'
  rw [hLHS]
  -- RHS: the analytic closed form `(T 0 + (ps.map snd).sum) + b/(ps.foldr (⊓) (R 0))`
  have hRmin : 0 < ps.foldr (fun p R => p.1 ⊓ R) (R 0) := by
    rw [foldrInf_rate_eq_last R T hbot]; exact hRpos _
  have hrRmin : r ≤ ps.foldr (fun p R => p.1 ⊓ R) (R 0) := by
    rw [foldrInf_rate_eq_last R T hbot]; exact hrR
  have hchain := exactChainOptimum_tokenBucketNN_rateLatencyNN r b (R 0) (T 0) ps hb
    hRmin hrRmin
  rw [hchain]
  -- match the closed forms via the two reindexing identities, then NNReal↔ℝ casts
  rw [foldrInf_rate_eq_last R T hbot, ← sum_eq_head_add_tail R T,
    EReal.coe_nnreal_eq_coe_real, EReal.coe_eq_coe_iff]
  push_cast
  ring

/-! ## Restatement of Part (R3) -/

-- The general-`n` windowed-last optimum equals the analytic `exactChainOptimum`, under
-- the bottleneck-last hypothesis (the honest scope: the windowed delay is to the LAST
-- server, so the identity holds iff the last server realizes `minR`).
example {n : ℕ} (r b : ℝ≥0) (R T : Fin (n + 1) → ℝ≥0)
    (hb : 0 < b) (hRpos : ∀ h, 0 < R h) (hbot : ∀ h, R (Fin.last n) ≤ R h)
    (hrR : r ≤ R (Fin.last n)) :
    programOptimum
        (WindowedFeasible (r : ℝ) (b : ℝ) (fun h => (R h : ℝ)) (fun h => (T h : ℝ)))
        (fun v => ((windowedDelay (Fin.last n) v : ℝ) : EReal))
      = exactChainOptimum (tokenBucketArrival r b) (rateLatencyNN (R 0) (T 0))
          ((List.ofFn (fun i : Fin n => (R i.succ, T i.succ))).map
            (fun p => rateLatencyNN p.1 p.2)) :=
  programOptimum_windowed_last_eq_exactChainOptimum r b R T hb hRpos hbot hrR

/-! ## Part (R4): adjudication of the arbitrary-order case

**What is proven (faithful, general `n`):** `programOptimum_windowed_last_eq_exactChainOptimum`
identifies the per-server-windowed LP optimum with the analytic `exactChainOptimum`, for all
`n`, **strictly under the bottleneck-last hypothesis** `∀ h, R (Fin.last n) ≤ R h`.  This is
unavoidable, not a convenience: the windowed objective `windowedDelay (Fin.last n)` measures
the delay to the **last** server, whose windowed optimum is `(∑T) + b/R(Fin.last n)`, the
*last* server's rate — whereas `exactChainOptimum` uses `b/minₕ R h`.  The two closed forms
coincide **iff `R (Fin.last n) = minₕ R h`**, i.e. iff the last server is the bottleneck.
The `n = 2` instance (`programOptimum_windowed_two_eq_exactChainOptimum`, hypothesis
`R₁ ≤ R₀`) is exactly this with `n = 1`.

**The arbitrary-order identity is NOT claimed.** For an arbitrary rate profile `R` the last
server need not be the bottleneck, so
`programOptimum (WindowedFeasible … (windowedDelay (Fin.last n))) = exactChainOptimum …`
is **false in general** (LHS `(∑T) + b/R(last)`, RHS `(∑T) + b/minR`; unequal whenever
`R(last) > minR`).  The honest unrestricted statement requires a **server reorder**: the
analytic side is order-independent (`exactChainOptimum`'s rate uses `foldr (⊓)`, and
`minₕ R h` is symmetric — `worstCaseChainDelay`/`exactChainOptimum` are permutation-invariant),
so one reindexes the servers by a permutation `σ : Equiv.Perm (Fin (n + 1))` carrying the
bottleneck to `Fin.last n`, applies the bottleneck-last bridge to `R ∘ σ`, then transports
back along `σ`.

**Adjudication of that reorder — what it needs:** the windowed side is *not* a clean
`List.Perm`/`Finset` rewrite, because `WindowedVars`/`WindowedFeasible` are indexed by
`Fin (n + 1)` with a *distinguished* objective server (`Fin.last n`), not a symmetric
functional of the profile.  Permuting the servers means reindexing the whole polytope
(`WindowedVars n ≃ WindowedVars n` along `σ` on the `d` component) and proving
`WindowedFeasible (R ∘ σ) (T ∘ σ)` is carried isomorphically — a polytope-reindexing
*equivalence* argument (an `Equiv`-pushforward of the feasible set preserving the optimum),
plus the analytic-side permutation-invariance of `exactChainOptimum` (which itself reduces to
`minₕ` symmetry / `List.Perm.foldr` for the `⊓`-fold and `List.Perm.sum` for the latency sum).
The latter (analytic) half is genuinely a `List.Perm`/`Finset.sum`-symmetry fact; the former
(windowed) half is a finite-LP reindexing equivalence.  Neither is *false* and neither needs
new mathematics, but the windowed reindexing equivalence is more than a one-line `Perm`
lemma — it is the polytope-isomorphism plumbing.  It is therefore deferred as `[infra]`; the
faithful, citable content is the bottleneck-last bridge above. -/

end DeepWiki
