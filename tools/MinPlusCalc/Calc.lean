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

/-- Render a `UppSeq ℤ` as its UPP quadruplet: `v0,v1,… period=d incr=c`. -/
def renderUpp (u : UppSeq Int) : String :=
  s!"{", ".intercalate (u.vals.map toString)}  period={u.period}  incr={u.incr}"

end MinPlusCalc
