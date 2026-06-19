import DeepWiki.NetworkCalculus.UppSequence

/-! # `minplus` calculator core — build/validate UPP sequences from CLI data
A thin layer over the proved-correct `DeepWiki.UppSeq` (min,plus) operators: validate a raw
`(vals, period, incr)` triple into a `UppSeq ℤ` (checking `0 < period ≤ #vals`), then the CLI runs
the native-compilable `evalNat`/`add`/`min`. The printed results are computed by the *same*
functions proved correct by `evalNat_add` / `evalNat_min`. -/

namespace MinPlusCalc

open DeepWiki

/-- Untyped UPP sequence as parsed from CLI args. -/
structure RawUpp where
  /-- stored values `f(0), …` -/
  vals : List Int
  /-- period `d` -/
  period : Nat
  /-- per-period increment `c` -/
  incr : Int

/-- Validate a raw triple into a `UppSeq ℤ` (`0 < period ≤ #vals`). -/
def buildUpp (r : RawUpp) : Except String (UppSeq Int) :=
  if hp : 0 < r.period then
    if hl : r.period ≤ r.vals.length then
      .ok { vals := r.vals, incr := r.incr, period := r.period, hperiod := hp, hlen := hl }
    else .error s!"need period ({r.period}) ≤ number of values ({r.vals.length})"
  else .error "period must be positive"

/-- Sample `evalNat` at `0, 1, …, k-1`. -/
def sample (u : UppSeq Int) (k : Nat) : List Int := (List.range k).map u.evalNat

/-- Per-`d` increment (asymptotic slope over the common period `d = lcm`) of the first operand. -/
def slope (r s : UppSeq Int) : Int := ((Nat.lcm r.period s.period / r.period : Nat) : Int) * r.incr

/-- Crossover window check at `N₀`: does the offset inequality `r(·)+s(Tr) ≤ s(·)+r(0)` hold across
one full period `[N₀, N₀+d)`? By `evalNat_add_le_of_window_le`, once true at `N₀ ≥ max(rank_r,rank_s)`
it holds for all later indices — so this finite check certifies a crossover rank. -/
def windowOk (r s : UppSeq Int) (N₀ : Nat) : Bool :=
  (List.range (Nat.lcm r.period s.period)).all (fun rem =>
    decide (r.evalNat (N₀ + rem) + s.evalNat (r.vals.length - r.period)
      ≤ s.evalNat (N₀ + rem) + r.evalNat 0))

/-- Smallest crossover rank `N₀ ≥ threshold` (searched up to `fuel` steps) where `windowOk` holds. -/
def findCrossover (r s : UppSeq Int) (threshold fuel : Nat) : Nat :=
  match fuel with
  | 0 => threshold
  | fuel + 1 => if windowOk r s threshold then threshold else findCrossover r s (threshold + 1) fuel

/-- Plain crossover window check: does `r ≤ s` hold across one full period `[N₀, N₀+d)`? This is the
`min`/`max` crossover (`min_evalNat_add_lcm_window`'s `hwin`) — distinct from the *offset* `windowOk`
that the convolution's minimizer-region needs. -/
def windowLeOk (r s : UppSeq Int) (N₀ : Nat) : Bool :=
  (List.range (Nat.lcm r.period s.period)).all (fun rem =>
    decide (r.evalNat (N₀ + rem) ≤ s.evalNat (N₀ + rem)))

/-- Smallest rank `N₀ ≥ threshold` (within `fuel`) where `r ≤ s` holds on a full period. -/
def findCrossoverLe (r s : UppSeq Int) (threshold fuel : Nat) : Nat :=
  match fuel with
  | 0 => threshold
  | fuel + 1 => if windowLeOk r s threshold then threshold else findCrossoverLe r s (threshold + 1) fuel

/-- Assemble the (min,plus) **convolution** `r ⊗ s` as a `UppSeq` (the composable closed form,
Lemma 4.4): orient so the smaller-slope operand leads, find a crossover rank, and build `convFrom`
at the stabilization rank `max (max N₀ rank + rank) (rank_r+rank_s+d)`. The result is a finite UPP
object, so convolutions chain through further operators. Correct by `convFrom`/`evalNat_convFrom`
together with `convNat_add_lcm_window` (whose window hypothesis holds at the found `N₀`). -/
def convUpp (r s : UppSeq Int) : UppSeq Int :=
  let d := Nat.lcm r.period s.period
  let tr := r.vals.length - r.period
  let ts := s.vals.length - s.period
  if slope r s = slope s r then
    -- balanced (equal slopes): stable from rank rank_r+rank_s+d, no crossover (convNat_add_lcm_of_balanced)
    r.convFrom s (tr + ts + d)
  else if slope r s ≤ slope s r then
    let N₀ := findCrossover r s (max tr ts) 1000
    r.convFrom s (max (max N₀ tr + tr) (tr + ts + d))
  else
    let N₀ := findCrossover s r (max tr ts) 1000
    s.convFrom r (max (max N₀ ts + ts) (ts + tr + d))

/-- Stabilization rank for `min`/`max` of two UPP sequences: balanced (equal slopes) stabilizes at
`max(rank_r,rank_s)`; otherwise at the crossover `N₀` where the slower operand becomes the min
(`min_evalNat_add_lcm_window`). -/
def stableRank (r s : UppSeq Int) : Nat :=
  let tr := r.vals.length - r.period
  let ts := s.vals.length - s.period
  if slope r s = slope s r then max tr ts
  else if slope r s ≤ slope s r then findCrossoverLe r s (max tr ts) 1000
  else findCrossoverLe s r (max tr ts) 1000

/-- The pointwise **minimum** `f ⊓ g` as a `UppSeq` (Lemma 4.3): prefix sampled, period `d = lcm`,
increment the smaller slope `min(cr,cs)`. Correct by `fromSamples`/`evalNat_fromSamples` with
`min_evalNat_add_lcm_window`. -/
def minUpp (r s : UppSeq Int) : UppSeq Int :=
  UppSeq.fromSamples (fun n => Min.min (r.evalNat n) (s.evalNat n))
    (Min.min (slope r s) (slope s r)) (Nat.lcm r.period s.period)
    (Nat.pos_of_ne_zero (Nat.lcm_ne_zero r.hperiod.ne' s.hperiod.ne')) (stableRank r s)

/-- The pointwise **maximum** `f ⊔ g` as a `UppSeq` (Lemma 4.3): increment the larger slope
`max(cr,cs)`. Correct by `fromSamples`/`evalNat_fromSamples` with `max_evalNat_add_lcm_window`. -/
def maxUpp (r s : UppSeq Int) : UppSeq Int :=
  UppSeq.fromSamples (fun n => Max.max (r.evalNat n) (s.evalNat n))
    (Max.max (slope r s) (slope s r)) (Nat.lcm r.period s.period)
    (Nat.pos_of_ne_zero (Nat.lcm_ne_zero r.hperiod.ne' s.hperiod.ne')) (stableRank r s)

/-- The **deconvolution** `f ⊘ g` as a `UppSeq` (Lemma 4.5): prefix sampled via `deconvNat`, period
`d_f = f`'s period, increment `c_f = f`'s increment. Correct by `fromSamples`/`evalNat_fromSamples`
with `deconvNat_add_period` (valid when `slope_f ≤ slope_g`, so the deconvolution is finite). -/
def deconvUpp (r s : UppSeq Int) : UppSeq Int :=
  UppSeq.fromSamples (fun n => r.deconvNat s n) r.incr r.period r.hperiod (r.vals.length - r.period)

/-- Render a `UppSeq ℤ` as its UPP quadruplet: `v0,v1,… period=d incr=c`. -/
def renderUpp (u : UppSeq Int) : String :=
  s!"{", ".intercalate (u.vals.map toString)}  period={u.period}  incr={u.incr}"

/-- Demo sequences for composition checks (ℤ): `r1(n) = n`, `r2(n) = 2n`. -/
def r1 : UppSeq Int := ⟨[0], 1, 1, by decide, by decide⟩
/-- Demo sequence `r2(n) = 2n` (ℤ). -/
def r2 : UppSeq Int := ⟨[0], 2, 1, by decide, by decide⟩

/-- **Composition (gate-verified by `native_decide`):** operators chain — the `UppSeq` produced by
`convUpp` is fed straight into `minUpp`. `(r1 ⊗ r2) ⊓ r2` denotes `n`: `convUpp r1 r2` denotes `n`
(`r1` is the slower operand), and `min(n, 2n) = n = r1`. -/
example : ∀ n ∈ Finset.range 6,
    (minUpp (convUpp r1 r2) r2).evalNat n = r1.evalNat n := by native_decide

/-- Rate-latency service curve `β_{R,T}(t) = R·(t−T)₊` as a UPP sequence: `T+1` leading zeros
(`β = 0` on `[0,T]`), then period `1`, increment `R`. -/
def betaRL (R : Int) (T : Nat) : UppSeq Int :=
  ⟨List.replicate (T + 1) 0, R, 1, by decide, by rw [List.length_replicate]; omega⟩

/-- **Network-calculus application (gate-verified):** end-to-end **server concatenation**. The
convolution of two rate-latency service curves is again rate-latency, with the *minimum rate* and the
*summed latency*: `β_{1,2} ⊗ β_{2,1} = β_{1,3}`. Here the calculator's `convNat` reproduces this DNC
theorem on the integer samples (`min(1,2)=1`, `2+1=3`). -/
example : ∀ n ∈ Finset.range 8,
    (betaRL 1 2).convNat (betaRL 2 1) n = (betaRL 1 3).evalNat n := by native_decide

/-- Token-bucket arrival curve `α_{r,b}(t) = b + r·t` for `t > 0` (`0` at `t=0`) as a UPP sequence:
`α(0)=0`, `α(1)=b+r`, then period `1`, increment `r`. -/
def tokenBucket (r b : Int) : UppSeq Int :=
  ⟨[0, b + r], r, 1, by decide, by simp⟩

/-- **Network-calculus application (gate-verified):** the **output arrival curve** of a flow through a
server is the deconvolution `α ⊘ β`. A token-bucket `α_{1,2}` through a rate-latency server `β_{2,1}`
(rate `2 ≥ 1`, so stable) emerges as a token bucket of the *same rate* with burst inflated by `r·T`:
`(α_{1,2} ⊘ β_{2,1})(n) = (2 + 1·1) + 1·n = n + 3`. The calculator's `deconvNat` reproduces it. -/
example : ∀ n ∈ Finset.range 6,
    (tokenBucket 1 2).deconvNat (betaRL 2 1) n = (n : Int) + 3 := by native_decide

/-- The **backlog bound** `sup_t (α(t) − β(t))` — the maximum vertical deviation of arrival `α` above
service `β`, i.e. the worst-case buffer occupancy — is exactly `(α ⊘ β)(0)`, the genuine supremum by
`deconvNat_isGreatest`. The canonical network-calculus buffer bound. Finite when `slope_α ≤ slope_β`. -/
def backlogBound (α β : UppSeq Int) : Int := α.deconvNat β 0

/-- **Network-calculus application (gate-verified):** the backlog bound of a token bucket `α_{1,2}`
through a rate-latency server `β_{2,1}` is the classic `b + r·T = 2 + 1·1 = 3`. -/
example : backlogBound (tokenBucket 1 2) (betaRL 2 1) = 3 := by native_decide

/-- The **delay bound** `h(α,β) = min{d : ∀ t, α(t) ≤ β(t+d)}` — the maximum horizontal deviation
(worst-case delay): the smallest right-shift of the service curve `β` that dominates the arrival `α`.
Searched over `d`, each candidate tested on a finite `t`-window `[0, deconvBound)` (past which the gap
`α(t)−β(t+d)` is non-increasing per period, so the window is decisive). Finite when `slope_α ≤
slope_β`; its faithfulness reduces to `evalNat_le_of_window_le` on `β` advanced by `d`. -/
def delayBound (α β : UppSeq Int) : Nat :=
  let K := α.deconvBound β
  let fuel := (backlogBound α β).toNat + K + 1
  ((List.range (fuel + 1)).find? fun d =>
    (List.range K).all fun t => decide (α.evalNat t ≤ β.evalNat (t + d))).getD fuel

/-- **Network-calculus application (gate-verified):** the delay bound of a token bucket `α_{1,2}`
through a rate-latency server `β_{2,1}` is the classic `T + b/R = 1 + 2/2 = 2`. -/
example : delayBound (tokenBucket 1 2) (betaRL 2 1) = 2 := by native_decide

end MinPlusCalc
