import DeepWiki.SymbolicIntegration.ComputableSoundnessCapstone

/-! # Discharging the recursive RDE residual `RischDESuccessResidual` — what falls, and the sharpened crux

`ComputableSoundnessCapstone.crischDESolve_field_of_witness_residual` closes the recursive RDE-oracle field
identity over `QFunNZG β` *up to* the explicit `RischDESuccessResidual` bundle. This file re-attacks that
bundle clause by clause for the recursive instance (`Dt = [CField.one]`, the primitive monomial), separating
the clauses that are genuine theorems from those that are a real precondition the recursive oracle does not
establish — sharpening the prior "self-certification wall" into its precise mathematical content.

* **The denominator-nonzero clauses are theorems**: `hfden`/`hgden` and the `cnormG _ ≠ []` clauses
  `hfden0`/`hgden0` come directly from the `QFunNZG β` subtype proof `cisZeroG _ = false`; `hyden` comes
  from the `cisZeroG yden = false` guard a successful `crischDESolve` already passes
  (`crischDESolve_yden_ne_zero`).
* **The §6.2 divisibility / fuel / `CSPDEGClearedInputsGen` clauses are NOT theorems for arbitrary `f g`**
  (the sharpened crux): `hdvdB`/`hdvdC` (`fden ∣ B`, `gden ∣ C`) are the **weak-normalization invariant** of
  Bronstein §6.1–§6.2 — they hold for the *post-Hermite, weakly-normalized* RDE input, but the recursive
  `crischDESolve` feeds its raw argument straight into `cRischDEG` without weak-normalizing it, and the engine
  computes the clearing `cdivG` unconditionally (truncating on non-divisibility). `hdn` likewise rests on the
  splitting-factorization product `fden = dₙ·dₛ`, which `cSplitFactorFastG` is documented not to establish
  abstractly. The fuel bounds (`hfbB`/`hfbC`) and the non-gcd `CSPDEGClearedInputsGen` clauses are per-run
  regularity. So the recursive `RischDESuccessResidual` is **not** an unconditional `∀ f g` — its precise true
  content is the §6.1 weak-normalization precondition plus per-run termination/fuel, NOT engine
  self-certification.

The verdict at the end states precisely which clauses fall and why the rest is a genuine precondition. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG GBPolyCore

/-! ## The denominator-nonzero clauses (`hfden`/`hgden`/`hfden0`/`hgden0`/`hyden`) — genuine theorems

These four-plus-one clauses of `RischDESuccessResidual` are NOT part of the crux: they follow from the
`QFunNZG β` subtype invariant `cisZeroG _ = false` (for the input denominators `f.1.2`, `g.1.2`) and from the
`cisZeroG yden = false` guard a successful `crischDESolve` passes (for the output denominator). We discharge
all of them here. -/

section Nonzero

variable {β : Type*} [CField β] [CFieldSpec β]

/-- **`cisZeroG p = false` reads as `toPolyG p ≠ 0`** — the contrapositive of `cisZeroG_iff`. The bridge
turning the `QFunNZG β` subtype's denominator-nonzero proof into the `≠ 0` polynomial fact the field bridge
wants. -/
theorem toPolyG_ne_zero_of_cisZeroG_false {p : CPolyG β} (h : CPolyG.cisZeroG p = false) :
    toPolyG p ≠ 0 := by
  intro h0
  rw [(CPolyG.cisZeroG_iff p).mpr h0] at h
  exact absurd h (by simp)

/-- **`cisZeroG p = false` gives `cnormG p ≠ []`** — the list-level form of denominator-nonzero. From
`toPolyG_ne_zero_of_cisZeroG_false` via `cnormG_eq_nil_iff`. -/
theorem cnormG_ne_nil_of_cisZeroG_false {p : CPolyG β} (h : CPolyG.cisZeroG p = false) :
    CPolyG.cnormG p ≠ [] := by
  intro he
  exact toPolyG_ne_zero_of_cisZeroG_false h ((CPolyG.cnormG_eq_nil_iff p).mp he)

/-- **The input denominator of a `QFunNZG β`-fraction is nonzero** (`hfden`/`hgden`): for `f : QFunNZG β`,
`toPolyG f.1.2 ≠ 0` — directly from the subtype proof `f.2 : cisZeroG f.1.2 = false`. -/
theorem qfunNZG_den_toPolyG_ne_zero (f : QFunNZG β) : toPolyG f.1.2 ≠ 0 :=
  toPolyG_ne_zero_of_cisZeroG_false f.2

/-- **The input denominator of a `QFunNZG β`-fraction has nonempty normal form** (`hfden0`/`hgden0`):
`cnormG f.1.2 ≠ []` — from the subtype proof. -/
theorem qfunNZG_den_cnormG_ne_nil (f : QFunNZG β) : CPolyG.cnormG f.1.2 ≠ [] :=
  cnormG_ne_nil_of_cisZeroG_false f.2

end Nonzero

/-! ## The output denominator (`hyden`) — from the `crischDESolve` success guard

A successful recursive solve `crischDESolve f g = some y` unfolds (over `QFunNZG β`,
`instCRischFieldQFunNZG`) to `cRischDEG [1] fuel f.1.1 f.1.2 g.1.1 g.1.2 = some (ynum, yden)` *together with*
the boolean guard `cisZeroG yden = false` (the `dif_pos` branch that wraps the pair into the `QFunNZG β`
output). So the output denominator `yden` is nonzero — `hyden` is forced by the success, not a residual. -/

section OutputNonzero

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFieldDomain β]
  [CFracGcdCore β] [CRischField β]

/-- **A successful recursive solve forces `cisZeroG yden = false`** (and hence `toPolyG yden ≠ 0`): if
`crischDESolve f g = some y` over `QFunNZG β` and the inner oracle returned `(ynum, yden)`, then the boolean
guard wrapping the pair into the `QFunNZG β` output was `cisZeroG yden = false`, so `toPolyG yden ≠ 0`. This
discharges the `hyden` clause of `RischDESuccessResidual` from the bare success — no residual. -/
theorem crischDESolve_yden_ne_zero (f g y : QFunNZG β)
    (hsolve : CRischField.crischDESolve f g = some y) (ynum yden : CPolyG β)
    (hsucc : cRischDEG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2 g.1.1 g.1.2
      = some (ynum, yden)) :
    toPolyG yden ≠ 0 := by
  -- unfold the recursive `crischDESolve` to its `cRischDEG`-then-guard form (mirrors the capstone)
  rw [show CRischField.crischDESolve f g
      = (match cRischDEG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2 g.1.1 g.1.2 with
         | none => none
         | some (ynum, yden) =>
           if h : CPolyG.cisZeroG yden = false then some ⟨(ynum, yden), h⟩ else none) from rfl] at hsolve
  rw [hsucc] at hsolve
  simp only at hsolve
  by_cases hyz : CPolyG.cisZeroG yden = false
  · exact toPolyG_ne_zero_of_cisZeroG_false hyz
  · rw [dif_neg hyz] at hsolve; exact absurd hsolve (by simp)

end OutputNonzero

end DeepWiki.SymbolicIntegration
