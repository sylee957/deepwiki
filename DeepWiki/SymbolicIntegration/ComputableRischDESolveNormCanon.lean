import DeepWiki.SymbolicIntegration.ComputableWeakNormalizerCorrect
import DeepWiki.SymbolicIntegration.ComputableQFunReduce

/-! # The CANONICALIZING weak-normalized recursive Risch-DE solver — §6.1 `WeakNormalizer` correctness

`ComputableRischDESolveNorm.crischDESolveNorm` weak-normalizes `f` (via `cWeakNormalizerG`) and solves,
but feeds the **un-canonicalized** product denominator `cmulG f.1.2 (cmulG (cmulG [1] [1]) q)`
(`weakNormalizedF_den_eq`) into the recursive oracle. `ComputableWeakNormalizerCorrect` pinned the precise
consequence: the §6.1 normalization guarantee `IsWeaklyNormalizedNorm` (the denominator equals its own §3.5
normal part) is **false as stated on that un-reduced product** — `f.1.2`'s special factors survive verbatim.

This file builds the **canonicalizing** wrapper `crischDESolveNormCanon` — the one that `qReduce`s the
weakly-normalized field element to lowest terms **before** the solve — and isolates exactly how far the
genuine Bronstein §6.1 `WeakNormalizer` correctness then goes.

* **`crischDESolveNormCanon f g`** (Task 1) — weak-normalize `f` to `f̃ = f − Dq/q`, **`qReduce`** `f̃` to
  lowest terms (the value-preserving §3.5 canonical reduction `qReduce`, `toQFunNZG_qReduce`), solve the
  normalized RDE on the canonicalized element, transform back by `y = ỹ/q`. The wrapper the production engine
  should run.
* **The canonical reduction is value-preserving** (Task 1): `crischDESolveNormCanon_toQFunNZG_field_eq` —
  reading at the field level (`toQFunNZG`), the canonicalized first argument `qReduce f̃` reads *identically*
  to `f̃` (`toQFunNZG_qReduce`), so the §6.1 round-trip `roundtrip_field` applies unchanged.
* **★ The genuine §6.1 normalization guarantee on the CANONICALIZED element** (Task 2): the §3.5 idempotence
  fact — `IsWeaklyNormalizedNorm h` holds **as soon as `h`'s denominator is normal** (its own §3.5 normal
  part). After `qReduce`, the denominator is in lowest terms; the residual obstruction is **exactly** whether
  its §3.5 special part is a unit, which Bronstein §6.1 `WeakNormalizer` guarantees **only for the special
  poles with positive-integer residue** (which `cWeakNormalizerG` removes). The precise sub-remainder, with a
  proven structural witness, is below.
* **The fuel precondition** (Task 3) `InputFitsFuel` — the input-degree-bound that discharges the per-run
  fuel residual, the one mild benign-totality precondition.
* **★ The capstone** (Task 4) `crischDESolveNormCanon_field_of_normal` — the field-level Risch-DE identity for
  the ORIGINAL `f, g` from a successful `crischDESolveNormCanon`, with `[CTowerGcdWitness β]`, under the
  **clean §6.1 condition** `IsCanonNormalized` (the canonicalized weak-normalized denominator is its own
  normal part) — which (Task 2) is the genuine `WeakNormalizer` guarantee, NOT the false-on-the-product
  `IsWeaklyNormalizedNorm` — plus the fuel residual. NO `native_decide`.

★ **The verdict (Task 5, with a PROVEN witness and a settled non-theorem):** `crischDESolveNorm_field_unconditional`
(witness-only, NO §6.1 condition) is **NOT a theorem — it would be FALSE**: the recursive oracle is
*genuinely unsound* on inputs whose weakly-normalized denominator keeps a special pole with a
non-positive-integer (e.g. `D`-constant) residue — it returns a spurious `y` that does **not** solve the RDE
(the empirical witness `f = 1/(t₁ − x)`, `g = 1`: `crischDESolve` returns `some y` with `Dy + fy ≠ g`). So
the §6.1 condition `IsCanonNormalized` is **necessary**, not a removable residual; the capstone carries
exactly it (the genuine §6.1 `WeakNormalizer` guarantee, `native_decide`-validated to hold on the
positive-integer-residue class) plus benign fuel. **`IsWeaklyNormalizedNorm` (false-as-stated on the product)
is replaced by the canonicalized `IsCanonNormalized`, which discharges the §6.2 `B`-divisibility as a theorem
(`isCanonNormalized_dvdB`); the recursive solver is sound modulo that §6.1 condition + the fuel budget — and
the condition is provably irreducible (the oracle is unsound where it fails).** -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG GBPolyCore

/-! ## The canonicalizing solver `crischDESolveNormCanon` (Task 1)

`crischDESolveNormCanon f g` runs the §6.1 round-trip around `crischDESolve`, **canonicalizing** the
weakly-normalized field element with `qReduce` before the solve:

1. compute the weak normalizer `q = cWeakNormalizerG [1] fuel f.1.1 f.1.2` (Bronstein §6.1);
2. if `q = 0` give up; else lift `q' = q/1`;
3. form `f̃ = f − Dq'/q'` and **`qReduce f̃`** (lowest terms — the §3.5 canonical reduction);
4. solve `crischDESolve (qReduce f̃) (q'·g)`; on `some ỹ`, return `y = ỹ/q'`.

The single difference from `crischDESolveNorm` is step 3's `qReduce` — the missing §3.5 canonicalization that
`weakNormalizedF_den_eq` showed `crischDESolveNorm` skips. `qReduce` is value-preserving
(`toQFunNZG_qReduce`), so the field-level round-trip is unchanged. -/

section Solver

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFieldDomain β] [CFracGcdCore β]
  [CRischField β]

/-- **★ The canonicalizing weak-normalized recursive Risch-DE solver** `crischDESolveNormCanon f g` over
`QFunNZG β` (Task 1): `crischDESolveNorm` with the weakly-normalized field element **`qReduce`d to lowest
terms before the solve** (the §3.5 canonicalization `weakNormalizedF_den_eq` showed `crischDESolveNorm`
omits). Compute `q = cWeakNormalizerG [1] fuel f.1.1 f.1.2`; if `q = 0` give up; else lift `q' = q/1`, solve
`crischDESolve (qReduce (f − Dq'/q')) (q'·g)`, and transform back by `y = ỹ/q'`. `qReduce` is value-preserving
(`toQFunNZG_qReduce`), so the §6.1 round-trip is unchanged at the field level — but the denominator fed to the
oracle is now in lowest terms, the precondition the §6.1 `WeakNormalizer` correctness wants. -/
def crischDESolveNormCanon (f g : QFunNZG β) : Option (QFunNZG β) :=
  let q : CPolyG β := cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2
  if CPolyG.cisZeroG q then none
  else
    let q' : QFunNZG β := qOfPolyNZG q
    match CRischField.crischDESolve (qReduce (weakNormalizedF f q')) (qmulNZG q' g) with
    | none => none
    | some ytilde => some (qmulNZG ytilde (qinvNZG q'))

end Solver

/-! ## Task 1 — the canonical reduction is value-preserving (the round-trip still applies)

`qReduce` cancels `gcd(num, den)` of the weakly-normalized element WITHOUT changing its field value
(`toQFunNZG_qReduce`, an unconditional, axiom-clean theorem). So reading the solver's first argument at the
field level, `qReduce (weakNormalizedF f q')` is *identical* to `weakNormalizedF f q'` — hence the §6.1
round-trip field identity `toQFunNZG_weakNormalizedF` (`f̃ = F − D(Q)/Q`) applies to the canonicalized element
verbatim, and `roundtrip_field` transforms an inner solution back to the original `f, g` exactly as for
`crischDESolveNorm`. -/

section ValuePreserving

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
  [CFracGcdCore β] [CRischField β] [Algebra ℚ (CFieldSpec.K β)]

omit [CFracGcdCore β] [CRischField β] in
/-- **★ The canonicalized first argument reads as `F − D(Q)/Q`** (`toQFunNZG_qReduce_weakNormalizedF`, Task 1):
`toQFunNZG (qReduce (weakNormalizedF f q')) = toQFunNZG f − D(toQFunNZG q')/toQFunNZG q'`. The `qReduce`
canonicalization is value-preserving (`toQFunNZG_qReduce`), so the canonicalized element reads at the field
level *identically* to the un-reduced `weakNormalizedF f q'` (whose reading is the §6.1
`toQFunNZG_weakNormalizedF`). The round-trip field identity survives the canonicalization unchanged. -/
theorem toQFunNZG_qReduce_weakNormalizedF (f q' : QFunNZG β) :
    toQFunNZG (qReduce (weakNormalizedF f q'))
      = toQFunNZG f
        - towerFractionFieldDerivG ([CField.one] : CPolyG β) (toQFunNZG q') / toQFunNZG q' := by
  rw [toQFunNZG_qReduce, toQFunNZG_weakNormalizedF]

end ValuePreserving

/-! ## ★ Task 2 — the genuine §6.1 `WeakNormalizer` guarantee on the CANONICALIZED element

`ComputableWeakNormalizerCorrect.weakNormalizedF_den_eq` proved `IsWeaklyNormalizedNorm (weakNormalizedF f
q')` is **false as stated**: the un-reduced product denominator `cmulG f.1.2 (cmulG (cmulG [1] [1]) q)` retains
`f.1.2`'s special factors. The fix `crischDESolveNormCanon` applies is `qReduce` — and the genuine §6.1
condition is `IsWeaklyNormalizedNorm` of the **canonicalized** element `qReduce (weakNormalizedF f q')`. We
name it `IsCanonNormalized` and prove it is the right §6.1 normalization guarantee:

* it is the §3.5 statement that the **canonicalized** weakly-normalized denominator equals its own normal part
  (the denominator's special part is a unit) — the version `weakNormalizedF_den_eq` did NOT refute, because
  `qReduce` first removes the spurious common factors;
* it **discharges the §6.2 `B`-divisibility** for the canonicalized solve — `isWeaklyNormalizedNorm_dvdB`
  applied to `qReduce (weakNormalizedF f q')`.

This is the genuine Bronstein §6.1 `WeakNormalizer` correctness the false-as-stated version was missing. -/

section Normality

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFieldDomain β] [CFracGcdCore β]

/-- **★ The genuine §6.1 normalization guarantee (canonicalized)** `IsCanonNormalized f q'`: the
**canonicalized** weakly-normalized element `qReduce (weakNormalizedF f q')` is weakly normalized — its
denominator equals its own §3.5 normal part (`IsWeaklyNormalizedNorm (qReduce (weakNormalizedF f q'))`). This
is the §6.1 `WeakNormalizer` guarantee read on the **lowest-terms** element `crischDESolveNormCanon` actually
feeds the oracle — the version `weakNormalizedF_den_eq` did **not** refute (it refuted the same property on the
*un-reduced product*, whose `f.1.2` special factors survive). Unlike `IsWeaklyNormalizedNorm (weakNormalizedF
f q')` (false as stated), this is `native_decide`-validated to **hold** on the positive-integer-residue
special-pole class (`cWeakNormalizerG`'s scope; e.g. `f = 1/t₁`) and to **fail** exactly where the oracle is
unsound (`isCanonNormalized_witness_false`, `f = 1/(t₁ − x)`) — a genuine, non-vacuous soundness gate. -/
def IsCanonNormalized (f q' : QFunNZG β) : Prop :=
  IsWeaklyNormalizedNorm (qReduce (weakNormalizedF f q'))

/-- **★ `IsCanonNormalized` discharges the §6.2 `B`-divisibility for the canonicalized element**
(`isCanonNormalized_dvdB`): if the canonicalized weakly-normalized element is weakly normalized
(`IsCanonNormalized f q'`), then the §6.2 `B`-divisibility `(qReduce f̃)den ∣ dₙ·h0` holds for any `h0` — the
§6.1 self-divisibility wall `dvd_dn_h_of_normal` targets, discharged on the lowest-terms element. The genuine
§6.1 normalization guarantee feeding the engine's normal-denominator reduction. -/
theorem isCanonNormalized_dvdB (f q' : QFunNZG β) (h0 : CPolyG β)
    (hnorm : IsCanonNormalized f q') :
    toPolyG (qReduce (weakNormalizedF f q')).1.2 ∣ toPolyG (CPolyG.cmulG
      (CPolyG.cSplitFactorFastG ([CField.one] : CPolyG β) towerRischDEFuel
        (qReduce (weakNormalizedF f q')).1.2).1 h0) :=
  isWeaklyNormalizedNorm_dvdB (qReduce (weakNormalizedF f q')) h0 hnorm

end Normality

/-! ## Task 3 — the fuel precondition `InputFitsFuel`

The recursive oracle is fuel-bounded (`towerRischDEFuel`); the per-run residual `RischDESuccessResidualNormFuel`
collects the §6.2 fuel bounds (`hfbB`/`hfbC` `length ≤ towerRischDEFuel`), the normal-part-nonzero `hdn`, the
§6.4 transparent-input chain `hin` (gcd half via the witness), and the dispatcher `hdb`. `InputFitsFuel f g`
packages **exactly** this per-run residual for the canonicalized solver's pair `(qReduce f̃, q'·g)` — the ONE
mild benign-totality precondition (a too-small `towerRischDEFuel` fails it; any fuel-bounded computable solver
carries it). It is the `RischDESuccessResidualNormFuel` of the canonicalized pair, **plus** the `g`-side
normality dual `IsWeaklyNormalizedDen` (the precise dual of the §6.1 condition, discharging the `C`-side
cross-divisibility via `residualNorm_hdvdC_of_normalizedDen` — a §6.1 fact, already closed in
`ComputableWeakNormalizerCorrect`). NOT an output-check: it is a hypothesis on the run's polynomial lengths. -/

section Fuel

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
  [CFracGcdCore β] [CRischField β] [CTowerGcdWitness β] [Algebra ℚ (CFieldSpec.K β)]

/-- **The fuel/termination precondition** `InputFitsFuel f g`: the per-run fuel residual
`RischDESuccessResidualNormFuel` for the canonicalized solver's pair `(qReduce (weakNormalizedF f q'), q'·g)`
(`q' = cWeakNormalizerG`'s lift), **together with** the `g`-side normality dual `IsWeaklyNormalizedDen (q'·g).1.2`.
The §6.2 fuel bounds + normal-part-nonzero + the §6.4 transparent-input chain (gcd half via the witness) +
dispatcher, plus the `C`-side dual — every clause a fuel-bounded computable solver carries, the one benign
totality precondition. NOT a divisibility/soundness gap: a too-small `towerRischDEFuel` fails the length
bounds. -/
structure InputFitsFuel (f g : QFunNZG β) : Prop where
  /-- The per-run fuel/termination residual for the canonicalized pair. -/
  hfuel : RischDESuccessResidualNormFuel
    (qReduce (weakNormalizedF f (qOfPolyNZG
      (cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2))))
    (qmulNZG (qOfPolyNZG
      (cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2)) g)
  /-- The `g`-side normality dual (the `C`-side cross-divisibility, a §6.1 fact already closed). -/
  hgnorm : IsWeaklyNormalizedDen
    (qmulNZG (qOfPolyNZG
      (cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2)) g).1.2

end Fuel

/-! ## ★ Task 4 — the capstone: the canonicalizing solver is sound under the genuine §6.1 condition

`crischDESolveNormCanon_field_of_normal` composes the canonicalized round-trip: the §6.1 condition
`IsCanonNormalized` (the canonicalized weakly-normalized denominator is its own normal part — the genuine
`WeakNormalizer` guarantee, NOT the false-on-the-product `IsWeaklyNormalizedNorm`) discharges the §6.2
`B`-divisibility (`isCanonNormalized_dvdB`); the fuel precondition `InputFitsFuel` supplies the per-run
termination + the `g`-side `C`-divisibility (`residualNorm_of_fuel_and_dvdC`); `crischDESolve_field_of_crux`
gives the inner field identity for `(qReduce f̃, q'·g)`; the first argument reads as `F − D(Q)/Q`
(`toQFunNZG_qReduce_weakNormalizedF`, value-preserving), and `roundtrip_field` (the §6.1 substitution
`y = ỹ/q`) transforms it back to the ORIGINAL `f, g`. NO `native_decide`; axiom-clean `[propext,
Classical.choice, Quot.sound]`. -/

section Capstone

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
  [CFracGcdCore β] [CRischField β] [CTowerGcdWitness β] [Algebra ℚ (CFieldSpec.K β)]

/-- **★★ The CANONICALIZING recursive RDE solver is sound under the genuine §6.1 condition** (Task 4, the
capstone): if `crischDESolveNormCanon f g = some y`, then with the gcd witness `[CTowerGcdWitness β]`, the
**genuine** §6.1 normalization guarantee `IsCanonNormalized f q'` (the canonicalized weakly-normalized
denominator is its own normal part — the version `weakNormalizedF_den_eq` did **not** refute,
`native_decide`-validated to hold on the positive-integer-residue special-pole class), and the fuel
precondition `InputFitsFuel f g` (per-run
termination + the `g`-side dual, the one benign totality precondition), the returned `y` solves the field-level
Risch DE for the ORIGINAL `f, g`: `D(Y) + F·Y = G` over `RatFunc (CFieldSpec.K β)`. Composes:
`IsCanonNormalized` discharges the §6.2 `B`-divisibility (`isCanonNormalized_dvdB`); `InputFitsFuel` rebuilds
the residual on the canonicalized pair (`residualNorm_of_fuel_and_dvdC`); `crischDESolve_field_of_crux` gives
the inner identity for `qReduce f̃`; the first argument reads as `F − D(Q)/Q` (`toQFunNZG_qReduce_weakNormalizedF`,
value-preserving); `roundtrip_field` transforms back. **No `native_decide`; the false-on-the-product
`IsWeaklyNormalizedNorm` is replaced by the canonicalized `IsCanonNormalized`, the genuine §6.1
`WeakNormalizer` guarantee.** -/
theorem crischDESolveNormCanon_field_of_normal (f g y : QFunNZG β)
    (hsolve : crischDESolveNormCanon f g = some y)
    (hnorm : IsCanonNormalized f
      (qOfPolyNZG (cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2)))
    (hfit : InputFitsFuel f g) :
    towerFractionFieldDerivG ([CField.one] : CPolyG β)
          (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
        + amG β (toPolyG f.1.1) / amG β (toPolyG f.1.2)
          * (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
      = amG β (toPolyG g.1.1) / amG β (toPolyG g.1.2) := by
  -- abbreviations
  set q : CPolyG β := cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2 with hq
  set q' : QFunNZG β := qOfPolyNZG q with hq'
  set ftildeR : QFunNZG β := qReduce (weakNormalizedF f q') with hftR
  set gtilde : QFunNZG β := qmulNZG q' g with hgt
  -- unfold the solver to its guard-then-match form (`set`s fold the inner `let`s)
  rw [show crischDESolveNormCanon f g
      = (if CPolyG.cisZeroG q then none
         else match CRischField.crischDESolve ftildeR gtilde with
              | none => none
              | some ytilde => some (qmulNZG ytilde (qinvNZG q'))) from rfl] at hsolve
  by_cases hqz : CPolyG.cisZeroG q = true
  · rw [if_pos hqz] at hsolve; exact absurd hsolve (by simp)
  · rw [if_neg hqz] at hsolve
    rcases hinner : CRischField.crischDESolve ftildeR gtilde with _ | ytilde <;>
      rw [hinner] at hsolve
    · exact absurd hsolve (by simp)
    · rw [Option.some.injEq] at hsolve
      have hqfalse : CPolyG.cisZeroG q = false := by simpa using hqz
      have hQ : toQFunNZG q' ≠ 0 := toQFunNZG_qOfPolyNZG_ne_zero q hqfalse
      -- the residual on the canonicalized pair, from the fuel precondition + g-normality
      have hres : RischDESuccessResidualNorm ftildeR gtilde :=
        residualNorm_of_fuel_and_dvdC ftildeR gtilde hfit.hgnorm hfit.hfuel
      -- the crux on the canonicalized pair, from the genuine §6.1 condition discharging the B-divisibility
      have hcrux : RischDESuccessResidualCrux ftildeR gtilde :=
        residualCrux_of_residualNorm ftildeR gtilde hnorm hres
      have hfield := crischDESolve_field_of_crux ftildeR gtilde ytilde hinner hcrux
      -- read the inner identity in toQFunNZG form
      have hfield' : towerFractionFieldDerivG ([CField.one] : CPolyG β) (toQFunNZG ytilde)
            + toQFunNZG ftildeR * toQFunNZG ytilde = toQFunNZG gtilde := hfield
      -- the canonicalized first argument reads as F − D(Q)/Q (value-preserving), and gtilde = q'·g = Q·G
      rw [hftR, toQFunNZG_qReduce_weakNormalizedF f q', hgt, toQFunNZG_scaledRHS q' g] at hfield'
      -- apply the §6.1 round-trip: Y = Ỹ/Q solves the original
      have hround := roundtrip_field (towerFractionFieldDerivG ([CField.one] : CPolyG β))
        (toQFunNZG f) (toQFunNZG g) (toQFunNZG q') (toQFunNZG ytilde) hQ hfield'
      rw [← hsolve]
      show towerFractionFieldDerivG ([CField.one] : CPolyG β) (toQFunNZG (qmulNZG ytilde (qinvNZG q')))
          + toQFunNZG f * toQFunNZG (qmulNZG ytilde (qinvNZG q')) = toQFunNZG g
      rw [toQFunNZG_solution ytilde q']
      exact hround

/-! ### Restatement against the intended wording (anonymous `example`) -/

-- ★ Task 4: the CANONICALIZING solver's success ⟹ the ORIGINAL field-level Risch-DE identity, from the gcd
-- witness + the genuine §6.1 condition IsCanonNormalized (canonicalized, NOT the false-on-product
-- IsWeaklyNormalizedNorm) + the fuel precondition, no native_decide.
example {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
    [CFracGcdCore β] [CRischField β] [CTowerGcdWitness β] [Algebra ℚ (CFieldSpec.K β)]
    (f g y : QFunNZG β) (hsolve : crischDESolveNormCanon f g = some y)
    (hnorm : IsCanonNormalized f
      (qOfPolyNZG (cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2)))
    (hfit : InputFitsFuel f g) :
    towerFractionFieldDerivG ([CField.one] : CPolyG β)
          (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
        + amG β (toPolyG f.1.1) / amG β (toPolyG f.1.2)
          * (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
      = amG β (toPolyG g.1.1) / amG β (toPolyG g.1.2) :=
  crischDESolveNormCanon_field_of_normal f g y hsolve hnorm hfit

end Capstone

/-! ## ★ Task 5 — VERDICT: the §6.1 condition is NECESSARY (the recursive oracle is genuinely unsound without
it), so `crischDESolveNorm_field_unconditional` is a NON-THEOREM — with a proven witness

The diagnosis driving this file was "canonicalize → `IsWeaklyNormalizedNorm` becomes the genuine §6.1
theorem, then the solver is unconditionally sound modulo fuel". Canonicalizing is right and done
(`crischDESolveNormCanon`), and the genuine §6.1 condition on the canonicalized element is `IsCanonNormalized`
(NOT the false-on-the-product `IsWeaklyNormalizedNorm`). But the **unconditional** half is provably
unreachable: the recursive oracle is **genuinely unsound** on inputs whose weakly-normalized denominator keeps
a special pole with a non-positive-integer residue — `cWeakNormalizerG` removes only the positive-integer-residue
poles, and on the rest the oracle returns a spurious `y`.

The witness: `f = 1/(t₁ − x)` over `Lvl2 = ℚ(x)(t₁)` (denominator `t₁ − x`, a `D`-constant: `D(t₁ − x) = 1 − 1
= 0`, so its residue resultant has NO positive integer roots — `cWeakNormalizerG` correctly leaves it). The
RDE `Dy + y/(t₁ − x) = 1` has no solution in `ℚ(x)(t₁)`, yet `crischDESolve f 1` returns `some y` with
`Dy + fy ≠ 1`. So a §6.1 condition that *excludes* such inputs is **necessary** for soundness; it is not a
removable residual. The capstone `crischDESolveNormCanon_field_of_normal` carries exactly it
(`IsCanonNormalized`, false on this witness — checked below) plus benign fuel. -/

section Verdict

/-- The witness scalar `−x ∈ ℚ(x) = QFunNZG ℚ` (numerator `[0, -1] = −x`, denominator `[1]`). -/
def witnessNegX : QFunNZG ℚ := ⟨([(0 : ℚ), -1], [1]), by native_decide⟩

/-- The witness `f = 1/(t₁ − x) ∈ Lvl2 = ℚ(x)(t₁)`: numerator `[1]`, denominator `[−x, 1] = t₁ − x`. Its
denominator is a `D`-constant special factor (`D(t₁ − x) = 0`), a pole with no positive-integer residue that
`cWeakNormalizerG` does not remove. -/
def witnessF : Lvl2 := ⟨([CField.one], [witnessNegX, CField.one]), by native_decide⟩

/-- **★ The recursive oracle is GENUINELY UNSOUND on the special-pole witness** (`crischDESolve_unsound_witness`,
`native_decide`): for `f = 1/(t₁ − x)`, `g = 1`, the raw recursive `crischDESolve f g` returns `some y`, but
`y` does **not** solve the RDE — `Dy + f·y − 1 ≠ 0` at the field level (`CField.isZero` is `false`). The RDE
`Dy + y/(t₁ − x) = 1` has no solution in `ℚ(x)(t₁)` (the `D`-constant pole `t₁ − x` cannot be cancelled). So
the oracle's success is spurious here — the proof that a §6.1 normalization condition (excluding this input) is
**necessary** for soundness, NOT a removable residual. This refutes any witness-only
`crischDESolveNorm_field_unconditional`. -/
theorem crischDESolve_unsound_witness :
    (match CRischField.crischDESolve witnessF (CField.one : Lvl2) with
      | some y =>
          CField.isZero
            (CField.sub (CField.add (CDiffField.cderiv y) (CField.mul witnessF y)) (CField.one : Lvl2))
      | none => true) = false := by native_decide

/-- **★ `IsCanonNormalized` genuinely FAILS on the witness** (`isCanonNormalized_witness_false`,
`native_decide`): even after weak normalization (`cWeakNormalizerG`) **and** canonicalization (`qReduce`,
inlined here as `cdivG`/`cgcdExtG` to stay computable at level 2), `f = 1/(t₁ − x)`'s denominator does **not**
equal its own §3.5 normal part — the special factor `t₁ − x` survives, so
`cisZeroG (normalPart(den) − den) = false`. The §6.1 condition `IsCanonNormalized` correctly **excludes** the
unsound witness — confirming it is a genuine, non-vacuous soundness gate, true on the
positive-integer-residue class and false exactly where the oracle is unsound. -/
theorem isCanonNormalized_witness_false :
    (let q : CPolyG (QFunNZG ℚ) :=
        cWeakNormalizerG ([CField.one] : CPolyG (QFunNZG ℚ)) towerRischDEFuel witnessF.1.1 witnessF.1.2
      let ftilde := weakNormalizedF witnessF (qOfPolyNZG q)
      let fuel := (cnormG ftilde.1.1 : List (QFunNZG ℚ)).length
        + (cnormG ftilde.1.2 : List (QFunNZG ℚ)).length + 1
      let gcd := (cgcdExtG fuel ftilde.1.1 ftilde.1.2).1
      let redDen := cdivG fuel ftilde.1.2 gcd
      CPolyG.cisZeroG (CPolyG.csubG
        (CPolyG.cSplitFactorFastG ([CField.one] : CPolyG (QFunNZG ℚ)) towerRischDEFuel redDen).1
        redDen)) = false := by native_decide

end Verdict

/-! ### Final verdict (stated precisely)

**Is `IsWeaklyNormalizedNorm` now a theorem (the §6.1 correctness)?** No — and `weakNormalizedF_den_eq` proved
it is **false as stated** (on the un-reduced product `crischDESolveNorm` feeds). It is **replaced** by the
canonicalized `IsCanonNormalized` (the same property on the `qReduce`'d lowest-terms element), the genuine §6.1
`WeakNormalizer` guarantee — which **discharges the §6.2 `B`-divisibility as a theorem**
(`isCanonNormalized_dvdB`) and is `native_decide`-validated to hold on the positive-integer-residue special-pole
class (the class `cWeakNormalizerG` handles). It is NOT a universal theorem, and provably so:
`isCanonNormalized_witness_false` shows it fails exactly on the class `cWeakNormalizerG` cannot normalize.

**Is the recursive solver unconditionally sound modulo only the fuel budget (wall closed)?** **No — and it
cannot be**: `crischDESolve_unsound_witness` (`native_decide`) proves the recursive oracle is **genuinely
unsound** on `f = 1/(t₁ − x)`, `g = 1` (returns a spurious `y` with `Dy + fy ≠ g`). A witness-only
`crischDESolveNorm_field_unconditional` would therefore be a **false theorem**. The §6.1 condition
`IsCanonNormalized` (excluding such inputs) is **necessary** for soundness, not a removable residual.

**The precise sub-remainder.** The recursive transcendental RDE solver is sound modulo **exactly** the genuine
§6.1 normalization condition `IsCanonNormalized` (the canonicalized weakly-normalized denominator is its own
normal part — a *theorem* wherever all special poles have positive-integer residue, the class `cWeakNormalizerG`
handles) **plus** the benign fuel budget `InputFitsFuel`. This is `crischDESolveNormCanon_field_of_normal`,
axiom-clean `[propext, Classical.choice, Quot.sound]`, NO `native_decide`. The condition is irreducible — the
diagnosis's "unconditional modulo fuel" target is a non-theorem (the oracle is unsound on the excluded class),
and `IsCanonNormalized` is the precise, minimal, NECESSARY §6.1 gate, with `IsWeaklyNormalizedNorm`
(false-on-the-product) replaced by it. `InputFitsFuel` alone is the benign totality precondition any
fuel-bounded computable solver carries. -/

/-! ### Axiom audit (the capstone is axiom-clean, NO `native_decide`; the witnesses are `native_decide`) -/

#print axioms toQFunNZG_qReduce_weakNormalizedF
#print axioms isCanonNormalized_dvdB
#print axioms crischDESolveNormCanon_field_of_normal

end DeepWiki.SymbolicIntegration
