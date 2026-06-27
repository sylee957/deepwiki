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
exactly it (a genuine §6.1 `WeakNormalizer` guarantee, a *theorem* on the positive-integer-residue class) plus
benign fuel. **`IsWeaklyNormalizedNorm` is replaced by the canonicalized `IsCanonNormalized` and made a
theorem on the normal-denominator class; the recursive solver is sound modulo that §6.1 condition + the fuel
budget — and the condition is provably irreducible.** -/

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

end DeepWiki.SymbolicIntegration
