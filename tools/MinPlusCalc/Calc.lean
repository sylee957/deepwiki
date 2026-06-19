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

end MinPlusCalc
