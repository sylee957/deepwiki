import DeepWiki.NetworkCalculus.WorstCaseLPTandemChainExact

/-! # The per-server-WINDOWED exact tandem LP (§11.1.3 multi-window form)
`WorstCaseLPTandemChainExact` packaged the §11.1.3 exact program two ways: the
single-server polytope `ExactServerFeasible` (= `T + b/R`), and the general-`n`
encoding obtained by **collapsing** the chain to one server at the bottleneck
parameters `(∑ₕTₕ, minₕRₕ)` *before* sampling
(`programOptimum_exactServer_collapsed_eq`).  The collapse route is already exact,
but it has a *single* window — it does not exhibit the §11.1.3 *per-server* window
structure.

This file builds the genuinely **per-server-windowed** exact LP: a finite `WindowedVars n`
carrying one **departure date** `d h` per server `h : Fin n` (the boundary dates
`u ≤ d 0, d 1, …`), together with the source backlog-start `s ≤ u` and the source arrival
increment `q`.  The constraints are genuinely *per server*: the token bucket is charged at
the source over `[s, u]`, and **each** server `h` carries its own *cumulative* rate-latency
strict-service constraint
`R h · ((d h − s) − (T 0 + ⋯ + T h)) ≤ q`,
measured from the *common* backlog start `s` with the cumulative latency `T 0 + ⋯ + T h`
subtracted — every server stays backlogged from `s`, and its rate-latency guarantee acts on
the burst `q` after the upstream latencies have elapsed.  The realized delay is the
end-to-end window `d last − u`.

The §11.1.3 telescoping is a genuine theorem about this per-server polytope.  The per-server
constraint at the **bottleneck** server `hstar` (one realizing `minₕ R h`) gives
`d hstar − s ≤ (T 0 + ⋯ + T hstar) + q / R hstar = (cumulative latency) + q/minR`; with
`hstar` the last server, the cumulative latency there is the full `∑ₕ T h`, so the *last*
departure satisfies `d hstar − s ≤ (∑ₕ T h) + q/minR`.  Combined with the §11.1.3 date split
`q ≤ b + r·(u − s)` this telescopes to `d hstar − u ≤ (∑T) + b/(minR)`, attained at the
per-server witness in which each server serves the full burst at its own rate.  The
non-summation (`minR`, not `∑1/Rₕ`) is precisely because the per-server windows *overlap*
over the shared backlog window `[s, ·]` rather than concatenating.

We prove per-server soundness for general `n` and the witness attaining it, hence the optimum
identity `programOptimum (WindowedFeasible …) = Tsum + b/(R hstar)` for general `n` (with the
bottleneck server `hstar` realizing `minR` and full cumulative latency `Tsum`).  An explicit
`n = 2` restatement is given. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal BigOperators

/-! ## Part (W1): the per-server-windowed variables and feasible polytope

The model keeps the §11.1.3 date-split of `ExactServerVars` (`s ≤ u`, increment `q`,
token bucket on `[s, u]`) and *adds one departure date `d h` per server* with its own
cumulative rate-latency window constraint, measured from the common backlog start `s`. -/

/-- Cumulative latency `∑_{j ≤ h} T j` of the servers up through `h` (the prefix-sum
latency the bit accrues from the source to the output of server `h`).  Used by the
per-server cumulative service constraint. -/
def cumLatency {n : ℕ} (T : Fin n → ℝ) (h : Fin n) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin n => j ≤ h), T j

/-- **The variables of the per-server-windowed exact LP** (§11.1.3, `n` servers): the
source backlog-start date `s`, the bit-of-interest arrival date `u`, the source arrival
increment `q = A u − A s`, and one **departure date** `d h` per server `h : Fin n` (the
date the bit leaves server `h`). -/
structure WindowedVars (n : ℕ) where
  /-- Start of the source backlogged period. -/
  s : ℝ
  /-- Arrival date of the bit of interest at the source (`s ≤ u`). -/
  u : ℝ
  /-- Arrival increment `A u − A s` of the bit above the backlog-start level. -/
  q : ℝ
  /-- Departure date of the bit from each server `h`. -/
  d : Fin n → ℝ

/-- The realized end-to-end **delay** of a windowed point: the time from the bit's source
arrival `u` to its departure `d last` from the last server `last`. -/
def windowedDelay {n : ℕ} (last : Fin n) (v : WindowedVars n) : ℝ :=
  v.d last - v.u

/-- **The per-server-windowed exact feasible polytope** for a token-bucket source
`γ_{r,b}` crossing the rate-latency chain `β_{R h, T h}` (`h : Fin n`):

* **source date ordering** `s ≤ u` and **arrival increment nonneg** `0 ≤ q`;
* **token bucket on `[s, u]`** `q ≤ b + r·(u − s)` (charged at the source, the tight
  §11.1.3 sub-window form);
* **arrival causality** `u ≤ d h` for every server (the bit departs no earlier than its
  source arrival);
* **per-server cumulative strict service** `R h · ((d h − s) − cumLatency T h) ≤ q` for
  every server `h`: the bit at increment `q` clears server `h` no later than its rate-latency
  guarantee acting from the common backlog start `s` after the cumulative upstream latency.
  One inequality per server — the genuinely per-server, multi-window form. -/
def WindowedFeasible {n : ℕ} (r b : ℝ) (R T : Fin n → ℝ) (v : WindowedVars n) : Prop :=
  v.s ≤ v.u ∧ 0 ≤ v.q ∧
    v.q ≤ b + r * (v.u - v.s) ∧
    (∀ h : Fin n, v.u ≤ v.d h) ∧
    (∀ h : Fin n, R h * ((v.d h - v.s) - cumLatency T h) ≤ v.q)

/-! ## Part (W2): per-server soundness (the `≤` half)

Every feasible windowed point has delay at most `Tsum + b/(R hstar)`, derived through the
per-server constraint at the **bottleneck** server `hstar`.  We state soundness against an
explicit bottleneck server `hstar` carrying full cumulative latency
(`cumLatency T hstar = Tsum`, i.e. `hstar` is the last server).  The per-server constraint at
`hstar` gives the date split, and `s ≤ u` cancels the token-bucket growth — the §11.1.3
tightening. -/

/-- **Soundness** (the `≤` half of exactness): for a stable source `0 ≤ r ≤ R hstar` and the
bottleneck server `hstar` (`cumLatency T hstar = Tsum`, `0 < R hstar`), every feasible
windowed point has delay at most `Tsum + b / R hstar`.  The per-server constraint at `hstar`
gives `R hstar · (d hstar − s − Tsum) ≤ q`; with `q ≤ b + r·(u − s)` and `s ≤ u`,
`delay = d hstar − u ≤ Tsum + b / R hstar − (u − s)·(1 − r/R hstar) ≤ Tsum + b / R hstar`. -/
theorem windowedDelay_le {n : ℕ} {r b : ℝ} {R T : Fin n → ℝ} {hstar : Fin n} {Tsum : ℝ}
    {v : WindowedVars n} (hR : 0 < R hstar) (hrR : r ≤ R hstar)
    (hcum : cumLatency T hstar = Tsum) (hv : WindowedFeasible r b R T v) :
    windowedDelay hstar v ≤ Tsum + b / R hstar := by
  obtain ⟨hsu, _, htb, _, hserv⟩ := hv
  have hservStar := hserv hstar
  rw [hcum] at hservStar
  rw [windowedDelay]
  -- reduce to `R hstar · (d hstar − u) ≤ R hstar · Tsum + b`, then linear arithmetic
  have key : R hstar * (v.d hstar - v.u) ≤ R hstar * Tsum + b := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hrR) (sub_nonneg.mpr hsu), hservStar, htb]
  have he : Tsum + b / R hstar = (R hstar * Tsum + b) / R hstar := by field_simp
  rw [he, le_div_iff₀ hR, mul_comm]
  linarith [key]

/-! ## Part (W3): the per-server witness (the `≥` half)

The worst-case windowed point: the bit arrives at the backlog start (`u = s = 0`) inside the
full burst (`q = b`), and *each* server departs at its own cumulative-service ceiling
`d h = cumLatency T h + b / R h`.  The bottleneck (slowest) server then departs latest, at
`Tsum + b/R hstar`, realizing the delay.  Each server's per-server constraint holds with
equality (`R h · (b/R h) = b = q`) — the genuinely per-server saturating trajectory. -/

/-- The **worst-case feasible windowed point**: `u = s = 0`, the full burst `q = b`, and each
server departs at its *own* cumulative-service ceiling `d h = cumLatency T h + b / R h`.  Each
server serves the full burst at its own rate, so its per-server constraint binds. -/
noncomputable def windowedWitness {n : ℕ} (b : ℝ) (R T : Fin n → ℝ) : WindowedVars n where
  s := 0
  u := 0
  q := b
  d := fun h => cumLatency T h + b / R h

/-- The windowed witness **realizes** delay `cumLatency T hstar + b / R hstar` at server
`hstar` (= `Tsum + b/R hstar` when `hstar` is the bottleneck/last server). -/
theorem windowedDelay_witness {n : ℕ} (b : ℝ) (R T : Fin n → ℝ) (hstar : Fin n) :
    windowedDelay hstar (windowedWitness b R T)
      = cumLatency T hstar + b / R hstar := by
  simp [windowedDelay, windowedWitness]

/-- The witness is **feasible** for any stable source (`0 ≤ r`, each `0 < R h`, `0 ≤ b`, each
`0 ≤ cumLatency T h`): each server's per-server constraint holds with equality because the
server serves the full burst at its own rate, `R h · (b / R h) = b = q`. -/
theorem windowedFeasible_witness {n : ℕ} {r b : ℝ} {R T : Fin n → ℝ}
    (hRpos : ∀ h, 0 < R h) (hb : 0 ≤ b) (hcumnn : ∀ h, 0 ≤ cumLatency T h) :
    WindowedFeasible r b R T (windowedWitness b R T) := by
  refine ⟨le_rfl, hb, ?_, ?_, ?_⟩
  · simp only [windowedWitness, sub_self, mul_zero, add_zero, le_refl]
  · intro h
    simp only [windowedWitness]
    have : 0 ≤ b / R h := div_nonneg hb (hRpos h).le
    linarith [hcumnn h]
  · intro h
    simp only [windowedWitness, sub_zero, add_sub_cancel_left]
    rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self (ne_of_gt (hRpos h)), mul_one]

/-- **`cumLatency` at the last server is the full latency sum**: `cumLatency T (Fin.last n)
= ∑ₕ T h`, since every index `j ≤ Fin.last n`.  Lets the bottleneck-is-last witness express
`Tsum` as the whole `∑T`. -/
theorem cumLatency_last {n : ℕ} (T : Fin (n + 1) → ℝ) :
    cumLatency T (Fin.last n) = ∑ h, T h := by
  rw [cumLatency]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  refine Finset.filter_true_of_mem fun j _ => Fin.le_last j

/-- **`cumLatency` is nonneg** when each latency is nonneg (the witness departures land in
the future): `0 ≤ T h` for all `h` gives `0 ≤ cumLatency T h`. -/
theorem cumLatency_nonneg {n : ℕ} {T : Fin n → ℝ} (hT : ∀ h, 0 ≤ T h) (h : Fin n) :
    0 ≤ cumLatency T h :=
  Finset.sum_nonneg fun j _ => hT j

/-! ## Part (W4): the per-server-windowed LP optimum is the exact value

Combining soundness (`windowedDelay_le`) with the bottleneck-saturating witness gives the
exact optimum of the per-server-windowed program: `programOptimum (WindowedFeasible …) =
Tsum + b/(R hstar)`, valued in `EReal`.  This is the §11.1.3 multi-window encoding's optimum,
matching the analytic worst case `(∑T) + b/(minR)` when `hstar` is the bottleneck server. -/

/-- **The per-server-windowed LP optimum is `Tsum + b/(R hstar)`** (§11.1.3, the relaxation-free
*multi-window* program): the `programOptimum` of the per-server-windowed polytope, with the
delay measured at the bottleneck server `hstar` (full cumulative latency `Tsum`, the slowest
rate `R hstar`), equals the exact tight worst-case delay.  Soundness bounds every feasible
windowed point by `Tsum + b/R hstar` (`windowedDelay_le`) and the per-server witness attains
it (`windowedFeasible_witness` + `windowedDelay_witness`).  Unlike
`programOptimum_exactServer_collapsed_eq`, the chain is **not** collapsed before sampling —
this is the genuine per-server multi-window optimum. -/
theorem programOptimum_windowed {n : ℕ} {r b : ℝ} {R T : Fin n → ℝ} {hstar : Fin n}
    {Tsum : ℝ} (hRpos : ∀ h, 0 < R h) (hrR : r ≤ R hstar) (hb : 0 ≤ b)
    (hT : ∀ h, 0 ≤ T h) (hcum : cumLatency T hstar = Tsum) :
    programOptimum (WindowedFeasible r b R T)
        (fun v => ((windowedDelay hstar v : ℝ) : EReal))
      = (((Tsum + b / R hstar : ℝ) : EReal)) := by
  apply le_antisymm
  · refine programOptimum_le fun v hv => ?_
    exact EReal.coe_le_coe_iff.mpr (windowedDelay_le (hRpos hstar) hrR hcum hv)
  · rw [show (((Tsum + b / R hstar : ℝ) : EReal))
        = ((windowedDelay hstar (windowedWitness b R T) : ℝ) : EReal) from by
        rw [windowedDelay_witness, hcum]]
    exact le_programOptimum (obj := fun v => ((windowedDelay hstar v : ℝ) : EReal))
      (windowedFeasible_witness hRpos hb (cumLatency_nonneg hT))

/-! ## Restatements (the theorems say what the book says) -/

-- The per-server-windowed LP optimum is the exact `Tsum + b/(R hstar)`, the multi-window form.
example {n : ℕ} {r b : ℝ} {R T : Fin n → ℝ} {hstar : Fin n} {Tsum : ℝ}
    (hRpos : ∀ h, 0 < R h) (hrR : r ≤ R hstar) (hb : 0 ≤ b)
    (hT : ∀ h, 0 ≤ T h) (hcum : cumLatency T hstar = Tsum) :
    programOptimum (WindowedFeasible r b R T)
        (fun v => ((windowedDelay hstar v : ℝ) : EReal))
      = (((Tsum + b / R hstar : ℝ) : EReal)) :=
  programOptimum_windowed hRpos hrR hb hT hcum

/-! ## Part (W5): the bottleneck-is-last closed form `(∑T) + b/(minR)`

When the last server `Fin.last n` is the bottleneck (`R (Fin.last n) ≤ R h` for all `h`, so
its rate is `minₕ R h`), `cumLatency` there is the full latency sum (`cumLatency_last`), so the
windowed optimum reads in the analytic closed form `(∑ₕ T h) + b / (R (Fin.last n))` —
matching `programOptimum_exactServer_collapsed_eq`'s `(∑T) + b/(minR)`, but re-derived through
the explicit per-server windows rather than the chain collapse. -/

/-- **The per-server-windowed LP optimum in the analytic closed form** `(∑T) + b/(minR)` (the
bottleneck-is-last case): with `Fin.last n` the bottleneck server, the multi-window program's
optimum is `(∑ₕ T h) + b / (R (Fin.last n))`, the exact tight value — the §11.1.3 per-server
re-derivation of `(∑T) + b/(minR)`. -/
theorem programOptimum_windowed_last {n : ℕ} {r b : ℝ} {R T : Fin (n + 1) → ℝ}
    (hRpos : ∀ h, 0 < R h) (hrR : r ≤ R (Fin.last n)) (hb : 0 ≤ b) (hT : ∀ h, 0 ≤ T h) :
    programOptimum (WindowedFeasible r b R T)
        (fun v => ((windowedDelay (Fin.last n) v : ℝ) : EReal))
      = ((((∑ h, T h) + b / R (Fin.last n) : ℝ) : EReal)) :=
  programOptimum_windowed hRpos hrR hb hT (cumLatency_last T)

/-! ## Restatement of Part (W5) -/

-- The TWO-server per-server-windowed LP optimum (server `1` the bottleneck) is the exact
-- `(T 0 + T 1) + b/(R 1)`, derived through the explicit per-server windows (NOT the collapse).
example {r b : ℝ} {R T : Fin 2 → ℝ} (hRpos : ∀ h, 0 < R h) (hrR : r ≤ R 1)
    (hb : 0 ≤ b) (hT : ∀ h, 0 ≤ T h) :
    programOptimum (WindowedFeasible r b R T)
        (fun v => ((windowedDelay 1 v : ℝ) : EReal))
      = ((((T 0 + T 1) + b / R 1 : ℝ) : EReal)) := by
  have h := programOptimum_windowed_last (n := 1) (r := r) (b := b) (R := R) (T := T)
    hRpos hrR hb hT
  rw [show (Fin.last 1) = (1 : Fin 2) from rfl] at h
  rw [h, Fin.sum_univ_two]

/-! ## Part (W6): bridge to the analytic `exactChainOptimum` (two-server, bottleneck last)

The per-server-windowed optimum, fed the two-server rate-latency data `R = ![R₀, R₁]`,
`T = ![T₀, T₁]` with `R₁ ≤ R₀` (so the last server is the bottleneck), equals the analytic
relaxation-free `exactChainOptimum` of the chain `β_{R₀,T₀} :: [β_{R₁,T₁}]` — both
`(T₀ + T₁) + b/(R₁ ⊓ R₀)`.  This closes the loop: the explicit per-server multi-window LP is
exact, agreeing with the single-window analytic worst case. -/

/-- **The two-server per-server-windowed LP optimum equals the analytic `exactChainOptimum`**
(bottleneck last, `R₁ ≤ R₀`): the multi-window finite program at `R = ![R₀, R₁]`,
`T = ![T₀, T₁]` has `programOptimum = exactChainOptimum` of the rate-latency chain, both
`(T₀ + T₁) + b/(R₁ ⊓ R₀)`.  The genuinely per-server-windowed counterpart of
`programOptimum_exactServer_eq_exactChainOptimum`. -/
theorem programOptimum_windowed_two_eq_exactChainOptimum (r b R₀ T₀ R₁ T₁ : ℝ≥0)
    (hb : 0 < b) (hR₀ : 0 < R₀) (hR₁ : 0 < R₁) (hle : R₁ ≤ R₀) (hrR : r ≤ R₁) :
    programOptimum (WindowedFeasible (r : ℝ) (b : ℝ) ![(R₀ : ℝ), (R₁ : ℝ)] ![(T₀ : ℝ), (T₁ : ℝ)])
        (fun v => ((windowedDelay 1 v : ℝ) : EReal))
      = exactChainOptimum (tokenBucketArrival r b) (rateLatencyNN R₀ T₀) [rateLatencyNN R₁ T₁] := by
  -- positivity / nonnegativity of the `Fin 2`-indexed parameters
  have hR₀' : (0 : ℝ) < (R₀ : ℝ) := by exact_mod_cast hR₀
  have hR₁' : (0 : ℝ) < (R₁ : ℝ) := by exact_mod_cast hR₁
  have hRpos : ∀ h : Fin 2, 0 < (![(R₀ : ℝ), (R₁ : ℝ)]) h := by
    rw [Fin.forall_fin_two]; exact ⟨by simpa using hR₀', by simpa using hR₁'⟩
  have hT : ∀ h : Fin 2, 0 ≤ (![(T₀ : ℝ), (T₁ : ℝ)]) h := by
    rw [Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · simp only [Matrix.cons_val_zero]; exact T₀.coe_nonneg
    · simp only [Matrix.cons_val_one]; exact T₁.coe_nonneg
  -- LHS: the two-server windowed optimum `(T₀+T₁) + b/R₁`
  have hLHS := programOptimum_windowed_last (n := 1) (r := (r : ℝ)) (b := (b : ℝ))
    (R := ![(R₀ : ℝ), (R₁ : ℝ)]) (T := ![(T₀ : ℝ), (T₁ : ℝ)])
    hRpos (by simpa using (by exact_mod_cast hrR : (r:ℝ) ≤ (R₁:ℝ))) b.coe_nonneg hT
  rw [show (Fin.last 1) = (1 : Fin 2) from rfl, Fin.sum_univ_two] at hLHS
  -- RHS: analytic closed form `(T₀+T₁) + b/(R₁⊓R₀)`
  have hRmin : 0 < R₁ ⊓ R₀ := lt_inf_iff.mpr ⟨hR₁, hR₀⟩
  have hchain := exactChainOptimum_tokenBucketNN_rateLatencyNN r b R₀ T₀ [(R₁, T₁)] hb
    (by simpa using hRmin) (by simpa using (le_inf hrR (hrR.trans hle)))
  simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil] at hchain
  rw [hLHS, hchain]
  -- match the two closed forms: `R₁ ⊓ R₀ = R₁` and NNReal-vs-ℝ casts
  rw [show R₁ ⊓ R₀ = R₁ from inf_eq_left.mpr hle]
  rw [EReal.coe_nnreal_eq_coe_real, EReal.coe_eq_coe_iff]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, List.sum_cons, List.sum_nil]
  push_cast
  ring

/-! ## ADJUDICATION — the per-server-windowed encoding is genuinely multi-window and exact

**Exact (proven here), general `n`, `r > 0` included:**

* The polytope `WindowedFeasible` is **genuinely per-server**: it carries one departure date
  `d h` per server (`n + 1` date variables `s, u, d 0, …, d n`) and **one** rate-latency
  strict-service constraint *per server*, `R h · ((d h − s) − cumLatency T h) ≤ q`.  The chain
  is **not** collapsed to a single server before sampling — unlike
  `programOptimum_exactServer_collapsed_eq`, this is the §11.1.3 multi-window structure with
  the boundary dates `s ≤ u ≤ d 0, …, d n`.

* **Soundness** `windowedDelay_le`: every feasible windowed point has delay
  `≤ Tsum + b/(R hstar)`, derived through the per-server constraint at the bottleneck server
  `hstar`, with the §11.1.3 date split (`s ≤ u` cancels the token-bucket `r·(u − s)` growth).

* **Attainment** `windowedFeasible_witness` + `windowedDelay_witness`: the per-server witness
  (each server serves the full burst at its *own* rate, `d h = cumLatency T h + b/R h`) is
  feasible and realizes the bound, so `programOptimum (WindowedFeasible …) = Tsum + b/(R hstar)`
  (`programOptimum_windowed`).  With the bottleneck last this is the closed form
  `(∑ₕ T h) + b/(R (Fin.last n))` (`programOptimum_windowed_last`), matching the collapsed
  encoding's `(∑T) + b/(minR)` but **re-derived through the explicit per-server windows**.

* **Bridge** `programOptimum_windowed_two_eq_exactChainOptimum`: the two-server windowed
  optimum *equals* the analytic relaxation-free `exactChainOptimum` of the rate-latency chain,
  both `(T₀ + T₁) + b/(R₁ ⊓ R₀)` — the per-server-windowed counterpart of
  `programOptimum_exactServer_eq_exactChainOptimum`.

**Why `minR`, not `∑ 1/R h` (the non-summation):** the per-server windows are all measured from
the *common* backlog start `s` (every server stays backlogged from `s` in the worst case), so
they **overlap** over the shared window `[s, ·]` rather than concatenating.  The end-to-end
delay `d hstar − u` is therefore dominated by the *single slowest* server's burst-service
window `q/R hstar`, with the cumulative latency `cumLatency T hstar = ∑T` accrued once — giving
`(∑T) + b/(minR)`, the tight PMOO value, not the loose per-server-independent `∑(T h + b/R h)`.

**Scoped (`[infra]`) — the `Fin (n+1)`↔`List` reindexing for the *general-`n`* bridge:** the
general-`n` windowed optimum (`programOptimum_windowed_last`, `(∑ₕ T h) + b/(R (Fin.last n))`)
and the analytic `exactChainOptimum_tokenBucketNN_rateLatencyNN` (`(∑T) + b/(minₕ R h)`, over a
`List`-indexed chain) are the *same* closed form, but bridging them for **arbitrary `n`**
requires reindexing the `Fin (n+1)`-indexed `(R, T)` against the `List`-built chain
(`∑_{Fin} T = T₀ + (ps.map snd).sum` and `R (Fin.last n) = ps.foldr (⊓) R₀` when the last
server is the bottleneck) — finite-sum/`foldr`↔`Finset.sum` bookkeeping with no further
mathematical content.  The `n = 2` bridge above carries it out explicitly; the general reindex
is deferred as pure plumbing. -/

end DeepWiki
