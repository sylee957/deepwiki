import DeepWiki.NetworkCalculus.WorstCaseLPTandemChainExactWindowedReindex

/-! # Permutation invariance and the bottleneck-last reorder bridge (§11.1.3)
The general-`n` windowed↔analytic bridge
(`programOptimum_windowed_last_eq_exactChainOptimum`) is proven **under the
bottleneck-last hypothesis** `∀ h, R (Fin.last n) ≤ R h`: the windowed objective is the
delay to the *last* server, with optimum `(∑T) + b/R(last)`, whereas the order-independent
`exactChainOptimum` uses `b/minR`.  They agree iff the last server is the bottleneck.

This file handles the **arbitrary server order** faithfully, *without* claiming the (false)
in-place identity:

* **Part (1) — permutation invariance of the closed-form value.**  The exact tandem
  worst-case value `chainValue b servers = (∑ₕ Tₕ) + b/(minₕ Rₕ)` depends only on the
  *multiset* of `(Rₕ, Tₕ)` pairs: `servers₁ ~ servers₂ → chainValue b servers₁ =
  chainValue b servers₂` (`chainValue_perm`).  The latency sum is `List.Perm.sum_eq`; the
  rate-min is the comm- and assoc-`⊓` `foldr`, `Perm`-invariant via the seed-swap lemma.
  This is the real infrastructure: it makes `exactChainOptimum` of a rate-latency chain a
  symmetric functional of its servers.

* **Part (2) — the bottleneck-last reorder/existence bridge.**  For ANY rate profile
  `R T : Fin (n+1) → ℝ≥0` there is a permutation `σ : Equiv.Perm (Fin (n+1))` carrying the
  argmin-rate server to `Fin.last n` (`exists_perm_bottleneck_last`), and the
  per-server-windowed LP of the σ-relabeled tandem `(R ∘ σ, T ∘ σ)` *equals*
  `exactChainOptimum` of the **original** chain
  (`programOptimum_windowed_relabel_eq_exactChainOptimum`): combine the bottleneck-last
  bridge on `R ∘ σ` with Part (1)'s permutation invariance.  "After relabeling the
  bottleneck last, the windowed LP computes the exact, order-independent worst case."

* **Part (3) — adjudication** of the in-place arbitrary-order case (see the foot of the
  file): the literal in-place windowed-last identity is FALSE for `R(last) > minR`; the
  order-independent exact LP is the COLLAPSED form
  (`programOptimum_exactServer_collapsed_eq_exactChainOptimum`, already exact for all
  orders); the windowed refinement is bottleneck-last by construction, so the reorder is
  handled by Part (1) + Part (2), not by an in-place windowed reindexing. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal BigOperators List

/-! ## Part (1): permutation invariance of the exact tandem worst-case value

The rate-min denominator of the closed form is a `foldr` of the comm- and assoc-`⊓`
operation `fun p R => p.1 ⊓ R`.  We prove it is seed-independent across list members and
hence `Perm`-invariant, then package the full value `(∑T) + b/(minR)` as a symmetric
functional of the server multiset. -/

/-- `fun (p : α × β) (R : α) => p.1 ⊓ R` is left-commutative for a `SemilatticeInf` carrier:
`p.1 ⊓ (q.1 ⊓ R) = q.1 ⊓ (p.1 ⊓ R)`.  Lets `List.Perm.foldr_eq` apply to the chain `foldr`. -/
instance fstInf_leftCommutative {α β : Type*} [SemilatticeInf α] :
    LeftCommutative (fun (p : α × β) (R : α) => p.1 ⊓ R) where
  left_comm a b c := inf_left_comm a.1 b.1 c

/-- **Seed-swap for the chain `foldr`-min**: if both seeds occur as rates in the list
(`z, z' ∈ l.map Prod.fst`), the `foldr`-min is the same — both equal the actual minimum.
The mechanism behind permutation invariance: a `Perm` moves the head/seed, but among
members the seed is inert. -/
theorem foldr_fstInf_seed_swap {α β : Type*} [SemilatticeInf α]
    {l : List (α × β)} {z z' : α}
    (hz : z ∈ l.map Prod.fst) (hz' : z' ∈ l.map Prod.fst) :
    l.foldr (fun p R => p.1 ⊓ R) z = l.foldr (fun p R => p.1 ⊓ R) z' := by
  rw [foldr_fst_inf_eq_map, foldr_fst_inf_eq_map]
  -- on the projected rate list both folds equal the minimum; antisymmetry via the bounds
  set rl := l.map Prod.fst with hrl
  refine le_antisymm ?_ ?_
  · exact le_foldrInf z' (rl.foldr (· ⊓ ·) z)
      (foldrInf_le_of_mem z hz') (fun a ha => foldrInf_le_of_mem z ha)
  · exact le_foldrInf z (rl.foldr (· ⊓ ·) z')
      (foldrInf_le_of_mem z' hz) (fun a ha => foldrInf_le_of_mem z' ha)

/-- `foldr (fun p R => p.1 ⊓ R) z l ≤ z`: the chain `foldr`-min never exceeds the seed
(the `fun p R => p.1 ⊓ R` analogue of `foldrInf_le_init`). -/
theorem foldrFstInf_le_init {α β : Type*} [SemilatticeInf α] (z : α) (l : List (α × β)) :
    l.foldr (fun p R => p.1 ⊓ R) z ≤ z := by
  rw [foldr_fst_inf_eq_map]; exact foldrInf_le_init z _

/-- `c ≤ foldr (fun p R => p.1 ⊓ R) z l` whenever `c ≤ z` and `c ≤ a.1` for every `a ∈ l`:
the chain `foldr`-min is the greatest lower bound (the `fun p R => p.1 ⊓ R` analogue of
`le_foldrInf`).  Used to lower-bound the chain rate-min (positivity, `r ≤ minR`). -/
theorem le_foldrFstInf {α β : Type*} [SemilatticeInf α] (z c : α) {l : List (α × β)}
    (hz : c ≤ z) (hmem : ∀ a ∈ l, c ≤ a.1) :
    c ≤ l.foldr (fun p R => p.1 ⊓ R) z := by
  rw [foldr_fst_inf_eq_map]
  refine le_foldrInf z c hz fun a ha => ?_
  rw [List.mem_map] at ha
  obtain ⟨p, hp, rfl⟩ := ha
  exact hmem p hp

/-- **The exact tandem worst-case value** as a functional of the *full* server list
`(R₀, T₀) :: ps`: `chainValue b servers = (∑ₕ Tₕ) + b/(minₕ Rₕ)`, the closed form of
`exactChainOptimum_tokenBucketNN_rateLatencyNN` (the rate-min is the head-seeded chain
`foldr`-min; the latency sum is the `Prod.snd`-sum).  Empty chain ↦ `0`. -/
noncomputable def chainValue (b : ℝ≥0) : List (ℝ≥0 × ℝ≥0) → ℝ≥0
  | [] => 0
  | (R₀, T₀) :: ps => (T₀ + (ps.map Prod.snd).sum) + b / (ps.foldr (fun p R => p.1 ⊓ R) R₀)

/-- `chainValue b ((R₀,T₀) :: ps) = (T₀ + ∑ tail latencies) + b/(tail `foldr`-min seeded by
`R₀`)` — the closed form of `exactChainOptimum_tokenBucketNN_rateLatencyNN` verbatim. -/
theorem chainValue_cons (b R₀ T₀ : ℝ≥0) (ps : List (ℝ≥0 × ℝ≥0)) :
    chainValue b ((R₀, T₀) :: ps)
      = (T₀ + (ps.map Prod.snd).sum) + b / (ps.foldr (fun p R => p.1 ⊓ R) R₀) := rfl

/-- The latency sum reads off the whole list: `T₀ + (ps.map snd).sum =
(((R₀,T₀)::ps).map snd).sum`. -/
theorem latencySum_cons (R₀ T₀ : ℝ≥0) (ps : List (ℝ≥0 × ℝ≥0)) :
    T₀ + (ps.map Prod.snd).sum = (((R₀, T₀) :: ps).map Prod.snd).sum := by
  rw [List.map_cons, List.sum_cons]

/-- The head-seeded tail `foldr`-min equals the whole-list `foldr`-min seeded by the head
rate: `ps.foldr f R₀ = ((R₀,T₀)::ps).foldr f R₀` (the head is absorbed idempotently). -/
theorem rateMin_cons {α β : Type*} [SemilatticeInf α] (R₀ : α) (T₀ : β)
    (ps : List (α × β)) :
    ps.foldr (fun p R => p.1 ⊓ R) R₀
      = ((R₀, T₀) :: ps).foldr (fun p R => p.1 ⊓ R) R₀ := by
  rw [List.foldr_cons]
  -- `R₀ ⊓ (ps.foldr ... R₀) = ps.foldr ... R₀` since the fold is `≤ R₀`
  exact (inf_of_le_right (foldrFstInf_le_init R₀ ps)).symm

/-- **`chainValue` is permutation invariant**: `servers₁ ~ servers₂ → chainValue b servers₁ =
chainValue b servers₂`.  The exact tandem worst case `(∑T) + b/(minR)` depends only on the
*multiset* of `(Rₕ, Tₕ)` servers — the latency sum is `List.Perm.sum_eq`, the rate-min is the
comm- and assoc-`⊓` `foldr` (seed-swapped to a fixed seat, then `List.Perm.foldr_eq`). -/
theorem chainValue_perm (b : ℝ≥0) {servers₁ servers₂ : List (ℝ≥0 × ℝ≥0)}
    (hperm : servers₁ ~ servers₂) :
    chainValue b servers₁ = chainValue b servers₂ := by
  -- both sides equal the whole-list value `(map snd).sum + b/(whole-list foldr-min seed z)`
  -- we route through a common helper on nonempty lists; empty case is trivial
  rcases servers₁ with _ | ⟨⟨R₁, T₁⟩, ps₁⟩
  · rw [← hperm.nil_eq]
  rcases servers₂ with _ | ⟨⟨R₂, T₂⟩, ps₂⟩
  · exact absurd hperm.eq_nil (by simp)
  rw [chainValue_cons, chainValue_cons, latencySum_cons R₁ T₁, latencySum_cons R₂ T₂,
    rateMin_cons R₁ T₁, rateMin_cons R₂ T₂]
  -- latency sums agree by `Perm.sum_eq` on the mapped lists
  have hsum : (((R₁, T₁) :: ps₁).map Prod.snd).sum = (((R₂, T₂) :: ps₂).map Prod.snd).sum :=
    (hperm.map Prod.snd).sum_eq
  -- rate-mins: fold both with the SAME seed `R₁` (`Perm.foldr_eq`), then swap seed `R₁→R₂`
  -- using that `R₂` is a member of the (permutation-equal) rate multiset
  have hseat : ((R₁, T₁) :: ps₁).foldr (fun p R => p.1 ⊓ R) R₁
      = ((R₂, T₂) :: ps₂).foldr (fun p R => p.1 ⊓ R) R₁ := hperm.foldr_eq R₁
  have hR1mem : R₁ ∈ (((R₂, T₂) :: ps₂).map Prod.fst) := by
    have : R₁ ∈ (((R₁, T₁) :: ps₁).map Prod.fst) := List.mem_cons_self
    exact (hperm.map Prod.fst).mem_iff.mp this
  have hR2mem : R₂ ∈ (((R₂, T₂) :: ps₂).map Prod.fst) := List.mem_cons_self
  have hswap : ((R₂, T₂) :: ps₂).foldr (fun p R => p.1 ⊓ R) R₁
      = ((R₂, T₂) :: ps₂).foldr (fun p R => p.1 ⊓ R) R₂ :=
    foldr_fstInf_seed_swap hR1mem hR2mem
  rw [hsum, hseat, hswap]

/-! ## Restatements of Part (1) -/

-- The exact tandem worst-case value `(∑T) + b/(minR)` is invariant under permuting servers.
example (b : ℝ≥0) {servers₁ servers₂ : List (ℝ≥0 × ℝ≥0)} (hperm : servers₁ ~ servers₂) :
    chainValue b servers₁ = chainValue b servers₂ :=
  chainValue_perm b hperm

/-- **`chainValue` is the `exactChainOptimum` closed form**: for a token-bucket source
`γ_{r,b}` (`b > 0`, `r ≤ minR`) crossing the rate-latency chain `(R₀,T₀) :: ps`, the exact
relaxation-free program optimum equals `((chainValue b ((R₀,T₀)::ps) : ℝ≥0∞) : EReal)`.  Ties
Part (1)'s symmetric value to the analytic worst case. -/
theorem exactChainOptimum_eq_chainValue (r b R₀ T₀ : ℝ≥0) (ps : List (ℝ≥0 × ℝ≥0))
    (hb : 0 < b) (hRmin : 0 < ps.foldr (fun p R => p.1 ⊓ R) R₀)
    (hrR : r ≤ ps.foldr (fun p R => p.1 ⊓ R) R₀) :
    exactChainOptimum (tokenBucketArrival r b) (rateLatencyNN R₀ T₀)
        (ps.map (fun p => rateLatencyNN p.1 p.2))
      = ((chainValue b ((R₀, T₀) :: ps) : ℝ≥0∞) : EReal) := by
  rw [exactChainOptimum_tokenBucketNN_rateLatencyNN r b R₀ T₀ ps hb hRmin hrR, chainValue_cons]

/-! ## Part (2): the bottleneck-last reorder / existence bridge

For an arbitrary rate profile there is a permutation putting the bottleneck (argmin rate)
last; the windowed-last LP of the relabeled tandem equals `exactChainOptimum` of the
original chain, combining the bottleneck-last bridge with Part (1)'s permutation invariance. -/

/-- **A permutation carrying the bottleneck (argmin rate) to the last seat**: for any
`R : Fin (n+1) → ℝ≥0` there is `σ : Equiv.Perm (Fin (n+1))` with
`∀ h, (R ∘ σ) (Fin.last n) ≤ (R ∘ σ) h` — the relabeled profile is bottleneck-last.
Built by `Finite.exists_min` for the argmin index and `Equiv.swap` to the last seat. -/
theorem exists_perm_bottleneck_last {n : ℕ} (R : Fin (n + 1) → ℝ≥0) :
    ∃ σ : Equiv.Perm (Fin (n + 1)), ∀ h, (R ∘ σ) (Fin.last n) ≤ (R ∘ σ) h := by
  obtain ⟨j, hj⟩ := Finite.exists_min R
  refine ⟨Equiv.swap j (Fin.last n), fun h => ?_⟩
  simp only [Function.comp_apply, Equiv.swap_apply_right]
  exact hj _

/-- **The relabeled tandem's chain list is a permutation of the original's**: the σ-relabeled
full server list `ofFn (fun h => (R(σ h), T(σ h)))` is `List.Perm`-equal to the original
`ofFn (fun h => (R h, T h))` (`Equiv.Perm.ofFn_comp_perm`), with both rearranged to the
head `(R 0, T 0)` + `ofFn` tail spelling. -/
theorem chainList_relabel_perm {n : ℕ} (R T : Fin (n + 1) → ℝ≥0)
    (σ : Equiv.Perm (Fin (n + 1))) :
    ((R (σ 0), T (σ 0)) ::
        List.ofFn (fun i : Fin n => (R (σ i.succ), T (σ i.succ))))
      ~ ((R 0, T 0) :: List.ofFn (fun i : Fin n => (R i.succ, T i.succ))) := by
  -- rewrite both head::tail forms as `ofFn` over `Fin (n+1)`, then apply `ofFn_comp_perm`
  have hL : ((R (σ 0), T (σ 0)) ::
        List.ofFn (fun i : Fin n => (R (σ i.succ), T (σ i.succ))))
      = List.ofFn (fun h : Fin (n + 1) => ((R ∘ σ) h, (T ∘ σ) h)) := by
    rw [List.ofFn_succ]; rfl
  have hR : ((R 0, T 0) :: List.ofFn (fun i : Fin n => (R i.succ, T i.succ)))
      = List.ofFn (fun h : Fin (n + 1) => (R h, T h)) := by
    rw [List.ofFn_succ]
  rw [hL, hR]
  exact σ.ofFn_comp_perm (fun h => (R h, T h))

/-- **The σ-relabeled windowed-last LP equals `exactChainOptimum` of the ORIGINAL chain**:
choosing `σ` to put the bottleneck last (`hbot : ∀ h, (R ∘ σ) (Fin.last n) ≤ (R ∘ σ) h`),
the per-server-windowed LP of the relabeled tandem `(R ∘ σ, T ∘ σ)` (delay to the last
server) is the relaxation-free `exactChainOptimum` of the *original* chain
`β_{R 0,T 0} :: ofFn(β_{R i.succ, T i.succ})`.  The bottleneck-last bridge applied to
`R ∘ σ`, then Part (1)'s permutation invariance to swap back to the original order. -/
theorem programOptimum_windowed_relabel_eq_exactChainOptimum {n : ℕ}
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
            (fun p => rateLatencyNN p.1 p.2)) := by
  -- bottleneck-last bridge on the relabeled data `(R ∘ σ, T ∘ σ)`
  have hbridge := programOptimum_windowed_last_eq_exactChainOptimum r b (R ∘ σ) (T ∘ σ)
    hb (fun h => hRpos (σ h)) hbot hrR
  rw [hbridge]
  -- now both sides are `exactChainOptimum` of a rate-latency chain; reduce via `chainValue`
  set psσ := List.ofFn (fun i : Fin n => ((R ∘ σ) i.succ, (T ∘ σ) i.succ)) with hpsσ
  set ps := List.ofFn (fun i : Fin n => (R i.succ, T i.succ)) with hps
  -- the bottleneck rate `(R ∘ σ) (Fin.last n)` is `≤` *every* original rate (σ surjective)
  have hbotR : ∀ k, (R ∘ σ) (Fin.last n) ≤ R k := fun k => by
    obtain ⟨h, rfl⟩ := σ.surjective k; exact hbot h
  -- so the source rate is below every original rate, and every rate is positive
  have hrR_all : ∀ k, r ≤ R k := fun k => le_trans hrR (hbotR k)
  -- relabeled chain `foldr`-min: bottleneck-last ⇒ `(R ∘ σ) (Fin.last n)`, positive, `≥ r`
  have hRminσ : 0 < psσ.foldr (fun p R => p.1 ⊓ R) ((R ∘ σ) 0) := by
    rw [hpsσ, foldrInf_rate_eq_last (R ∘ σ) (T ∘ σ) hbot]; exact hRpos _
  have hrRσ : r ≤ psσ.foldr (fun p R => p.1 ⊓ R) ((R ∘ σ) 0) := by
    rw [hpsσ, foldrInf_rate_eq_last (R ∘ σ) (T ∘ σ) hbot]; exact hrR
  -- original chain `foldr`-min: positive and `≥ r` directly from the per-rate bounds
  have hps_mem : ∀ a ∈ ps, ∀ P : ℝ≥0 → Prop, (∀ k, P (R k)) → P a.1 := by
    intro a ha P hP
    rw [hps, List.mem_ofFn] at ha
    obtain ⟨i, rfl⟩ := ha
    exact hP i.succ
  -- original chain `foldr`-min is `≥` the (positive) bottleneck rate, and `≥ r`
  have hRmin : 0 < ps.foldr (fun p R => p.1 ⊓ R) (R 0) :=
    lt_of_lt_of_le (hRpos (σ (Fin.last n)))
      (le_foldrFstInf (R 0) ((R ∘ σ) (Fin.last n)) (hbotR 0)
        (fun a ha => hps_mem a ha (((R ∘ σ) (Fin.last n)) ≤ ·) hbotR))
  have hrRmin : r ≤ ps.foldr (fun p R => p.1 ⊓ R) (R 0) :=
    le_foldrFstInf (R 0) r (hrR_all 0) (fun a ha => hps_mem a ha (r ≤ ·) hrR_all)
  -- both sides equal `((chainValue b (full server list) : ℝ≥0∞) : EReal)`; perm invariance closes
  rw [exactChainOptimum_eq_chainValue r b ((R ∘ σ) 0) ((T ∘ σ) 0) psσ hb hRminσ hrRσ,
    exactChainOptimum_eq_chainValue r b (R 0) (T 0) ps hb hRmin hrRmin]
  norm_cast
  exact chainValue_perm b (chainList_relabel_perm R T σ)

/-! ## Restatements of Part (2) -/

-- A permutation carries the bottleneck (argmin rate) to the last seat, for any profile.
example {n : ℕ} (R : Fin (n + 1) → ℝ≥0) :
    ∃ σ : Equiv.Perm (Fin (n + 1)), ∀ h, (R ∘ σ) (Fin.last n) ≤ (R ∘ σ) h :=
  exists_perm_bottleneck_last R

-- After relabeling the bottleneck last, the windowed-last LP of the relabeled tandem is the
-- order-independent exact worst case `exactChainOptimum` of the ORIGINAL chain.
example {n : ℕ} (r b : ℝ≥0) (R T : Fin (n + 1) → ℝ≥0) (σ : Equiv.Perm (Fin (n + 1)))
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

/-- **The relabeled-bottleneck-last windowed LP exists and computes the exact worst case**:
for ANY profile `R T : Fin (n+1) → ℝ≥0` (stable source: `0 < b`, all `0 < R h`, `r ≤` every
rate) there *exists* a relabeling `σ` putting the bottleneck last whose per-server-windowed
LP equals the order-independent `exactChainOptimum` of the original chain.  The combined
existence-and-identity form of Part (2): the arbitrary-order worst case is computed by the
windowed LP *after a bottleneck-last reorder*. -/
theorem exists_perm_programOptimum_windowed_eq_exactChainOptimum {n : ℕ}
    (r b : ℝ≥0) (R T : Fin (n + 1) → ℝ≥0)
    (hb : 0 < b) (hRpos : ∀ h, 0 < R h)
    (hrR : ∀ h, r ≤ R h) :
    ∃ σ : Equiv.Perm (Fin (n + 1)),
      programOptimum
          (WindowedFeasible (r : ℝ) (b : ℝ)
            (fun h => ((R ∘ σ) h : ℝ)) (fun h => ((T ∘ σ) h : ℝ)))
          (fun v => ((windowedDelay (Fin.last n) v : ℝ) : EReal))
        = exactChainOptimum (tokenBucketArrival r b) (rateLatencyNN (R 0) (T 0))
            ((List.ofFn (fun i : Fin n => (R i.succ, T i.succ))).map
              (fun p => rateLatencyNN p.1 p.2)) := by
  obtain ⟨σ, hbot⟩ := exists_perm_bottleneck_last R
  exact ⟨σ, programOptimum_windowed_relabel_eq_exactChainOptimum r b R T σ hb hRpos hbot
    (hrR (σ (Fin.last n)))⟩

/-! ## Part (3): ADJUDICATION — the in-place arbitrary-order identity, faithfully scoped

**What is FALSE (and is NOT stated as a theorem).** The literal in-place arbitrary-order
identity
`programOptimum (WindowedFeasible … (windowedDelay (Fin.last n))) = exactChainOptimum …`
**fails** for any profile with `R (Fin.last n) > minₕ R h`: the windowed objective measures
the delay to the *last* server, with optimum `(∑T) + b/R(Fin.last n)`
(`programOptimum_windowed_last`), whereas `exactChainOptimum`'s order-independent value is
`(∑T) + b/minₕ R h`.  These are unequal whenever the last server is not the bottleneck.  The
windowed model is bottleneck-last by construction (each server clears the burst over the
*shared* backlog window from the common start `s`, so the dominating constraint is the
slowest server's, and it is exhibited at the *last* departure date only when the slowest
server *is* last).  Stating the in-place identity unconditionally would be a false lemma; we
do not.

**What IS order-independent and exact for ALL orders** is the *collapsed* exact LP:
`programOptimum_exactServer_collapsed_eq_exactChainOptimum` (in `WorstCaseLPTandemChainExact`)
collapses the chain to a single server at `(∑Tₕ, minₕRₕ)` *before* sampling, so its optimum
is `(∑T) + b/minR` for every input order — the minₕ/∑ₕ are symmetric functionals, no reorder
needed.  That is the honest order-independent finite LP.

**How the windowed refinement handles arbitrary order** is the **reorder**, not an in-place
windowed reindexing:

* Part (1) — `chainValue_perm`: the analytic worst-case value `(∑T) + b/minR` is a symmetric
  functional of the server multiset (`List.Perm`-invariant), so `exactChainOptimum` of a
  rate-latency chain does not depend on server order.

* Part (2) — `exists_perm_bottleneck_last` + `programOptimum_windowed_relabel_eq_exactChainOptimum`
  (and the combined `exists_perm_programOptimum_windowed_eq_exactChainOptimum`): one *relabels*
  the bottleneck to the last seat by a permutation `σ`, applies the bottleneck-last bridge to
  `R ∘ σ`, then transports back along Part (1)'s permutation invariance.  The per-server
  windowed LP of the *relabeled* tandem then equals the order-independent exact worst case of
  the *original* chain.

So the arbitrary-order case is faithful and complete: the *value* is order-independent
(Part 1); the *windowed LP* attains it after a bottleneck-last reorder (Part 2); the *in-place*
windowed identity is false and is left unstated; and the genuinely order-independent finite LP
is the collapsed form (`WorstCaseLPTandemChainExact`).  No in-place windowed reindexing is
claimed because none is true — the windowed objective is intrinsically the delay to the last
server. -/

end DeepWiki
