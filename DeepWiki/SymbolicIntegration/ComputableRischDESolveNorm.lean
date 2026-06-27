import DeepWiki.SymbolicIntegration.ComputableRischDENormalCorrect

/-! # The CORRECT (weak-normalized) recursive Risch-DE solver — closing the divisibility wall

`ComputableRischDENormalCorrect` sharpened the recursive RDE-oracle wall to its exact mathematical
content: a successful `crischDESolve f g = some y` over `QFunNZG β` gives the field-level Risch-DE identity
**modulo** the reduced crux `RischDESuccessResidualCrux`, whose genuine obstruction is the §6.1
weak-normalization product-divisibilities `hdvdB_dn_h` (`fden ∣ dₙh`) and `hdvdC_dn_h2` (`gden ∣ dₙh²`).
The diagnosis there: the recursive `crischDESolve` **skips** Bronstein §6.1 weak normalization
(`cWeakNormalizerG`), so it feeds raw (possibly non-normal) input into `cRischDEG`, on which the
divisibility can fail — but `dvd_dn_h_of_normal` shows the divisibility **vanishes on normal input**.

This file builds the **correct** algorithm — the one the engine should run — and confirms the diagnosis:

* **`crischDESolveNorm f g`** (Task 1) = weak-normalize `f` via `cWeakNormalizerG` to `f̃ = f − Dq/q`,
  solve the normalized RDE `Dỹ + f̃·ỹ = q·g` with the existing recursive `crischDESolve`, and transform
  the solution back by `y = ỹ/q` (the §6.1 round-trip).
* **The normalization-correctness sub-lemma** (Task 2): the precise, isolated property that makes the
  divisibility crux vanish — `IsWeaklyNormalizedNorm f̃` says `f̃`'s denominator equals its own normal
  part (`toPolyG (cSplitFactorFastG [1] _ f̃.1.2).1 = toPolyG f̃.1.2`). This is exactly the algebraic
  *guarantee* of `cWeakNormalizerG` (Bronstein §6.1): for the post-normalization `f̃`, the special part of
  the denominator is a unit. It is `native_decide`-validated on concrete runs (the engine computes it) but
  not abstractly self-certified, so it is carried as the **one** isolated normalization-correctness fact.
* **The §6.1 round-trip correctness** (Task 3): `roundtrip_field` — the pure field-algebra substitution
  showing `Y = Ỹ/Q` solves the original `D(Y) + F·Y = G` whenever `Ỹ` solves the normalized
  `D(Ỹ) + (F − DQ/Q)·Ỹ = Q·G` (`Q ≠ 0`). This is a **theorem** (Mathlib `Derivation` quotient rule), no
  residual.
* **★ The capstone** (Task 4): `crischDESolveNorm_field` — the field-level Risch-DE identity for the
  ORIGINAL `f, g` from a successful `crischDESolveNorm`, with `[CTowerGcdWitness β]`, the normalization
  guarantee (Task 2), and `RischDESuccessResidualNorm` — the crux **with the `B`-divisibility clause
  `hdvdB_dn_h` REMOVED** (discharged by `dvd_dn_h_of_normal`). NO `native_decide`. **So the `B`-divisibility
  crux — the §6.2 self-divisibility `dvd_dn_h_of_normal` targets, the wall the diagnosis pinned — IS closed
  for the correct (normalized) algorithm, modulo the single normalization-correctness sub-lemma.**

★ **Verdict (stated precisely at the end): the wall is illusory FOR THE `B`-DIVISIBILITY** — the §6.2
self-divisibility `fden ∣ dₙh` that `dvd_dn_h_of_normal` targets was the engine's missing weak-normalization
step; with `cWeakNormalizerG` added it is a **theorem** given the one §6.1 normalization-correctness fact
(`IsWeaklyNormalizedNorm`). Precisely beyond that single sub-lemma: (i) the `C`-divisibility `hdvdC_dn_h2`
(`gden ∣ dₙh0²`) is a **`g`-side cross-divisibility** that `dvd_dn_h_of_normal` provably does NOT reach
(it is the engine's own `cdvdG` check up to `gden`-vs-`eₙ`, not a self-divisibility), and (ii) the per-run
fuel/termination (`hdn`/`hfbB`/`hfbC`/`hin`/`hdb`) that every fuel-bounded computable solver carries. Both
are NOT the `B`-divisibility wall; they are a distinct `g`-side condition + generic fuel-boundedness. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG GBPolyCore

/-! ## The §6.1 round-trip field-algebra identity (Task 3, abstract — no engine, no residual)

The pure substitution lemma underlying the round-trip: in any field with a `Derivation`, if `Ỹ` solves the
**weakly-normalized** equation `D(Ỹ) + (F − DQ/Q)·Ỹ = Q·G` and `Q ≠ 0`, then `Y = Ỹ/Q` solves the
**original** `D(Y) + F·Y = G`. This is exactly Bronstein §6.1's reduction of the RDE to its
weakly-normalized form, read at the field level. A theorem — the round-trip preserves the RDE. -/

section RoundTrip

variable {K : Type*} [Field K] (D : Derivation ℤ (RatFunc K) (RatFunc K))

/-- **★ The §6.1 round-trip preserves the Risch DE** (`roundtrip_field`, abstract): for a `Derivation` `D`
on `RatFunc K`, field elements `F G Q Ỹ` with `Q ≠ 0`, if `Ỹ` solves the weakly-normalized equation
`D(Ỹ) + (F − D(Q)/Q)·Ỹ = Q·G`, then `Y = Ỹ/Q` solves the original `D(Y) + F·Y = G`. The substitution
`y = ỹ/q` of Bronstein §6.1, read purely at the field level (`Derivation` quotient rule
`D(Ỹ/Q) = (D(Ỹ)·Q − Ỹ·D(Q))/Q²`); the algebraic essence of the weak-normalization round-trip, with NO
residual. -/
theorem roundtrip_field (F G Q Ytilde : RatFunc K) (hQ : Q ≠ 0)
    (hnorm : D Ytilde + (F - D Q / Q) * Ytilde = Q * G) :
    D (Ytilde / Q) + F * (Ytilde / Q) = G := by
  -- quotient rule: `D(Ỹ/Q) = Q⁻¹²·(Q·DỸ − Ỹ·DQ)`, with `•` over `RatFunc K` reading as `*`
  have hquot : D (Ytilde / Q) = (Q * D Ytilde - Ytilde * D Q) / Q ^ 2 := by
    rw [Derivation.leibniz_div, smul_sub, smul_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      div_eq_inv_mul, inv_pow, mul_sub, mul_assoc]
  rw [hquot]
  -- clear `Q` (and `Q²`): everything multiplied through by `Q²` and matched
  have hQ2 : Q ^ 2 ≠ 0 := pow_ne_zero 2 hQ
  field_simp at hnorm ⊢
  -- `hnorm` now reads (cleared) the normalized identity; rearrange to the goal cleared form
  ring_nf at hnorm ⊢
  linear_combination hnorm

end RoundTrip

/-! ## The normalized recursive solver `crischDESolveNorm` (Task 1)

`crischDESolveNorm f g` runs the §6.1 round-trip around the existing recursive `crischDESolve`:

1. compute the weak normalizer `q = cWeakNormalizerG [1] fuel f.1.1 f.1.2` (Bronstein §6.1) — the
   polynomial with `f − Dq/q` weakly normalized;
2. lift `q` to `QFunNZG β` as `q' = q/1` (guarding `q ≠ 0`);
3. form `f̃ = f − Dq'/q'` (the weakly-normalized field element) and `qg = q'·g`;
4. solve the normalized RDE `crischDESolve f̃ qg`; on `some ỹ`, return `y = ỹ/q'`.

Computable over `QFunNZG β` (everything routes through the engine; subtype proofs `Prop`-erased). The base
solve, normal-denominator reduction, etc., are exactly the production `crischDESolve` — this wrapper only
adds the missing §6.1 pre-step. -/

section Solver

variable {β : Type*} [CField β] [CDiffField β] [CFieldDomain β] [CFracGcdCore β] [CRischField β]

/-- **Lift a polynomial `q : CPolyG β` to `QFunNZG β` as `q/1`** `qOfPolyNZG q`: numerator `q`, denominator
`[1]` (always nonzero). When `q` itself is zero the lift is still well-formed (`0/1`); the solver guards
`q ≠ 0` separately where the field round-trip needs `Q ≠ 0`. The bridge turning the §6.1 weak-normalizer
output (a `CPolyG β`) into a `QFunNZG β` field element. -/
def qOfPolyNZG (q : CPolyG β) : QFunNZG β :=
  ⟨(q, [CField.one]), QFunNZG.cisZeroG_one_singleton⟩

/-- **The weakly-normalized field element** `weakNormalizedF f q' = f − Dq'/q'` over `QFunNZG β`
(`D = towerDerivQFunNZG [1]`, the level derivation): subtract the logarithmic derivative `Dq'/q'` of the
weak normalizer from `f`. By Bronstein §6.1 this is weakly normalized for `q' = cWeakNormalizerG`'s output.
The first argument of the inner `crischDESolve`. -/
def weakNormalizedF (f q' : QFunNZG β) : QFunNZG β :=
  qsubNZG f (qmulNZG (towerDerivQFunNZG ([CField.one] : CPolyG β) q') (qinvNZG q'))

/-- **★ The correct (weak-normalized) recursive Risch-DE solver** `crischDESolveNorm f g` over
`QFunNZG β` (Task 1): the §6.1 round-trip around the production `crischDESolve`. Compute the weak normalizer
`q = cWeakNormalizerG [1] fuel f.1.1 f.1.2`; if `q = 0` give up (`none`); else lift `q' = q/1`, solve the
**normalized** RDE `crischDESolve (f − Dq'/q') (q'·g)` with the existing recursive oracle, and transform the
solution back by `y = ỹ/q'`. Adds exactly Bronstein §6.1 weak normalization (the step the production
`crischDESolve` skips) so the §6.2 divisibility precondition holds on the input fed to `cRischDEG`. -/
def crischDESolveNorm (f g : QFunNZG β) : Option (QFunNZG β) :=
  let q : CPolyG β := cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2
  if CPolyG.cisZeroG q then none
  else
    let q' : QFunNZG β := qOfPolyNZG q
    match CRischField.crischDESolve (weakNormalizedF f q') (qmulNZG q' g) with
    | none => none
    | some ytilde => some (qmulNZG ytilde (qinvNZG q'))

end Solver

/-! ## The normalization-correctness sub-lemma (Task 2)

`IsWeaklyNormalizedNorm h` is the precise property of a `QFunNZG β` that makes the §6.2 divisibility crux
vanish (via `dvd_dn_h_of_normal`): `h`'s denominator equals its own normal part. This is exactly Bronstein
§6.1's *guarantee* for the post-normalization `f̃ = f − Dq/q`: the residue resultant's positive integer
roots are exhausted, so the special part of `f̃`'s denominator is a unit and the denominator IS its own
normal part. The engine computes `cWeakNormalizerG` and the property holds on every concrete run
(`native_decide`-checkable), but `cWeakNormalizerG` carries no abstract correctness theorem — so this is
the single isolated normalization-correctness fact, supplied as a hypothesis at the capstone. -/

section Normality

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFieldDomain β] [CFracGcdCore β]

/-- **The weak-normalization guarantee** `IsWeaklyNormalizedNorm h`: the `QFunNZG β` `h` has a
**weakly-normalized denominator** — its denominator equals its own §3.5 normal part
`toPolyG (cSplitFactorFastG [1] _ h.1.2).1 = toPolyG h.1.2` (equivalently, the denominator's special part
is a unit). The output `f̃ = f − Dq/q` of Bronstein §6.1 weak normalization satisfies this by construction;
it is the precise condition under which `dvd_dn_h_of_normal` discharges the §6.2 divisibility crux. The
single isolated normalization-correctness fact (the engine validates it per run; no abstract theorem). -/
def IsWeaklyNormalizedNorm (h : QFunNZG β) : Prop :=
  toPolyG (CPolyG.cSplitFactorFastG ([CField.one] : CPolyG β) towerRischDEFuel h.1.2).1
    = toPolyG h.1.2

omit [CFieldDomain β] in
/-- **The normalization guarantee discharges the `B`-divisibility crux** (`isWeaklyNormalizedNorm_dvdB`):
if `f̃`'s denominator is weakly normalized (`IsWeaklyNormalizedNorm f̃`), then the crux's §6.1
`B`-divisibility `f̃den ∣ dₙ·h0` holds for any `h0` — directly from `dvd_dn_h_of_normal`. The
divisibility crux's first clause becomes a theorem on normalized input. -/
theorem isWeaklyNormalizedNorm_dvdB (ftilde : QFunNZG β) (h0 : CPolyG β)
    (hnorm : IsWeaklyNormalizedNorm ftilde) :
    toPolyG ftilde.1.2 ∣ toPolyG (CPolyG.cmulG
      (CPolyG.cSplitFactorFastG ([CField.one] : CPolyG β) towerRischDEFuel ftilde.1.2).1 h0) :=
  dvd_dn_h_of_normal ([CField.one] : CPolyG β) towerRischDEFuel ftilde.1.2 h0
    (show toPolyG (CPolyG.cSplitFactorFastG ([CField.one] : CPolyG β) towerRischDEFuel ftilde.1.2).1
        = toPolyG ftilde.1.2 from hnorm)

/-! ### Why the `C`-divisibility crux is NOT closed by `f`-normalization (the precise boundary)

The crux's `C`-divisibility clause `hdvdC_dn_h2` is `gden ∣ dₙ·h0²` where `dₙ = (cSplitFactorFastG [1] _
fden).1` is the normal part of **`f`'s** denominator. This is a **cross**-divisibility (`g`'s denominator
into `f`'s normal-part block), NOT the self-divisibility `fden ∣ dₙ·h0` that `dvd_dn_h_of_normal` proves.
Normalizing `f` (making `fden` its own normal part) gives the `B`-clause but says nothing about `gden`
dividing `dₙh0²`. So `hdvdC_dn_h2` is genuinely outside `dvd_dn_h_of_normal`'s reach — it stays in the
per-run residual (it is, in fact, the engine's own `cdvdG eₙ dₙh0²` check up to `gden`-vs-`eₙ`, a `g`-side
condition). The wall `dvd_dn_h_of_normal` targets is the `B`-divisibility; that one IS closed. -/

end Normality

/-! ## The construction bridges to the field (Task 3 — the round-trip read through `toQFunNZG`)

The solver's `QFunNZG`-level constructions read at the field level (`toQFunNZG`) exactly as the §6.1
round-trip wants: `weakNormalizedF f q'` reads as `F − D(Q)/Q`, the scaled RHS `q'·g` reads as `Q·G`, and
the returned `ytilde·q'⁻¹` reads as `Ỹ/Q`. All three are ring-hom computations (`toQFunNZG_q*` +
`toQFunNZG_towerDerivQFunNZG`); the derivation `D = towerFractionFieldDerivG [1]` agrees with
`towerDerivQFunNZG [1]` through `toQFunNZG`. -/

section Bridges

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
  [CFracGcdCore β] [CRischField β] [Algebra ℚ (CFieldSpec.K β)]

omit [CFracGcdCore β] [CRischField β] in
/-- **The derivation bridge** `towerFractionFieldDerivG [1] (toQFunNZG x) = toQFunNZG (towerDerivQFunNZG [1]
x)`: the abstract fraction-field derivation `towerFractionFieldDerivG [1]` agrees with the computable tower
derivation `towerDerivQFunNZG [1]` through `toQFunNZG`. Just `toQFunNZG_towerDerivQFunNZG` read through
`towerFractionFieldDerivG = extendDeriv (implicitDeriv (toPolyG ·))`. -/
theorem towerFractionFieldDerivG_toQFunNZG (x : QFunNZG β) :
    towerFractionFieldDerivG ([CField.one] : CPolyG β) (toQFunNZG x)
      = toQFunNZG (towerDerivQFunNZG ([CField.one] : CPolyG β) x) := by
  rw [towerFractionFieldDerivG, toQFunNZG_towerDerivQFunNZG]

omit [CDiffField β] [CDiffFieldSpec β] [CFracGcdCore β] [CRischField β] [Algebra ℚ (CFieldSpec.K β)] in
/-- **`toQFunNZG q' ≠ 0` from `q ≠ 0`** (`toQFunNZG_qOfPolyNZG_ne_zero`): the lift `q' = q/1` has nonzero
field image exactly when `q` is nonzero (`toQFunNZG q' = amG(toPolyG q)/amG 1 = amG(toPolyG q)`). The
`Q ≠ 0` hypothesis the round-trip needs, from the solver's `cisZeroG q = false` guard. -/
theorem toQFunNZG_qOfPolyNZG_ne_zero (q : CPolyG β) (hq : CPolyG.cisZeroG q = false) :
    toQFunNZG (qOfPolyNZG q) ≠ 0 := by
  rw [toQFunNZG]
  show amG β (toPolyG q) / amG β (toPolyG ([CField.one] : CPolyG β)) ≠ 0
  rw [toPolyG_cone_eq_one, map_one, div_one]
  exact amG_toPolyG_ne_zero (toPolyG_ne_zero_of_cisZeroG_false hq)

omit [CFracGcdCore β] [CRischField β] in
/-- **`weakNormalizedF` reads as `F − D(Q)/Q`** (`toQFunNZG_weakNormalizedF`, the §6.1 round-trip field
identity through the construction): `toQFunNZG (weakNormalizedF f q') = toQFunNZG f −
towerFractionFieldDerivG [1] (toQFunNZG q') / toQFunNZG q'`. The weakly-normalized field element `f̃ = f −
Dq/q` read at the field level — a ring-hom computation (`toQFunNZG_qsubNZG`/`_qmulNZG`/`_qinvNZG` +
the derivation bridge). The round-trip correctness for the LHS coefficient, a **theorem**. -/
theorem toQFunNZG_weakNormalizedF (f q' : QFunNZG β) :
    toQFunNZG (weakNormalizedF f q')
      = toQFunNZG f
        - towerFractionFieldDerivG ([CField.one] : CPolyG β) (toQFunNZG q') / toQFunNZG q' := by
  rw [weakNormalizedF, toQFunNZG_qsubNZG, toQFunNZG_qmulNZG, toQFunNZG_qinvNZG,
    towerFractionFieldDerivG_toQFunNZG, div_eq_mul_inv]

omit [CDiffField β] [CDiffFieldSpec β] [CFracGcdCore β] [CRischField β] [Algebra ℚ (CFieldSpec.K β)] in
/-- **The returned solution reads as `Ỹ/Q`** (`toQFunNZG_solution`): `toQFunNZG (qmulNZG ytilde (qinvNZG
q')) = toQFunNZG ytilde / toQFunNZG q'`. The §6.1 back-transform `y = ỹ/q` read at the field level
(`toQFunNZG_qmulNZG`/`_qinvNZG`), a ring-hom computation. -/
theorem toQFunNZG_solution (ytilde q' : QFunNZG β) :
    toQFunNZG (qmulNZG ytilde (qinvNZG q'))
      = toQFunNZG ytilde / toQFunNZG q' := by
  rw [toQFunNZG_qmulNZG, toQFunNZG_qinvNZG, div_eq_mul_inv]

omit [CDiffField β] [CDiffFieldSpec β] [CFracGcdCore β] [CRischField β] [Algebra ℚ (CFieldSpec.K β)] in
/-- **The scaled RHS reads as `Q·G`** (`toQFunNZG_scaledRHS`): `toQFunNZG (qmulNZG q' g) = toQFunNZG q' *
toQFunNZG g`. The §6.1 RHS scaling `g ↦ q·g` read at the field level (`toQFunNZG_qmulNZG`). -/
theorem toQFunNZG_scaledRHS (q' g : QFunNZG β) :
    toQFunNZG (qmulNZG q' g) = toQFunNZG q' * toQFunNZG g :=
  toQFunNZG_qmulNZG q' g

end Bridges

/-! ## ★ The capstone — the normalized recursive solver is sound, `B`-divisibility wall CLOSED (Task 4)

`RischDESuccessResidualNorm` is the reduced crux `RischDESuccessResidualCrux` **with the `B`-divisibility
clause `hdvdB_dn_h` REMOVED** — that clause is the §6.2 self-divisibility wall `dvd_dn_h_of_normal` targets,
discharged by `isWeaklyNormalizedNorm_dvdB` from the §6.1 normalization guarantee `IsWeaklyNormalizedNorm`.
What remains is the per-run termination/fuel any fuel-bounded computable solver carries (`hdn`
normal-part-nonzero, `hfbB`/`hfbC` fuel bounds, `hin` the per-level transparent-input chain, `hdb` the
dispatcher routing) **plus** the `C`-divisibility `hdvdC_dn_h2` (`gden ∣ dₙh0²`, a `g`-side cross condition
outside `dvd_dn_h_of_normal`'s reach — see the boundary note above). The `B`-divisibility wall is gone.

`crischDESolveNorm_field` composes: (normalization guarantee) discharges the `B`-divisibility crux →
`residualCrux_of_residualNorm`/`residual_of_crux` rebuild the full residual → `crischDESolve_field_of_crux`
gives the inner field identity for `f̃ = f − Dq/q`, `g̃ = q·g` → `roundtrip_field` (the §6.1 substitution)
transforms it back to
the ORIGINAL `f, g`. NO `native_decide`; axiom-clean `[propext, Classical.choice, Quot.sound]`. -/

section Capstone

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
  [CFracGcdCore β] [CRischField β] [CTowerGcdWitness β] [Algebra ℚ (CFieldSpec.K β)]

/-- **★ The per-run residual of the NORMALIZED solver** `RischDESuccessResidualNorm f̃ g̃`: the reduced crux
`RischDESuccessResidualCrux` with **the `B`-divisibility clause `hdvdB_dn_h` REMOVED** — that clause is the
genuine §6.2 self-divisibility wall `dvd_dn_h_of_normal` targets, discharged by `f`-normalization
(`isWeaklyNormalizedNorm_dvdB`), so it is NOT part of this residual. What remains is the per-run
termination/fuel every fuel-bounded computable solver carries — `hdn` (normal part nonzero), `hfbB`/`hfbC`
(the §6.2 fuel bounds), `hin` (the §6.4 per-level transparent-input chain, gcd clauses via the witness),
`hdb` (the dispatcher routing) — **plus the `C`-divisibility `hdvdC_dn_h2`** (`gden ∣ dₙh0²`, a `g`-side
**cross**-divisibility that `dvd_dn_h_of_normal` provably does NOT reach: it is the engine's own `cdvdG`
check up to `gden`-vs-`eₙ`, not a self-divisibility). The `B`-divisibility wall is removed; the `C`-side
condition and per-run fuel remain. -/
structure RischDESuccessResidualNorm (ftilde gtilde : QFunNZG β) : Prop where
  /-- The normal part `dₙ` of `f̃den` is nonzero. -/
  hdn : ∀ a0 b0 c0 h0 : CPolyG β,
    cRdeNormalDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel ftilde.1.1 ftilde.1.2
        gtilde.1.1 gtilde.1.2 = some (a0, b0, c0, h0) →
      toPolyG (CPolyG.cSplitFactorFastG ([CField.one] : CPolyG β) towerRischDEFuel ftilde.1.2).1 ≠ 0
  /-- §6.2 `C`-divisibility `gden ∣ dₙ·h0²` (the `g`-side cross-divisibility — NOT reached by
  `f`-normalization; the engine's own `cdvdG` check up to `gden`-vs-`eₙ`). -/
  hdvdC_dn_h2 : ∀ a0 b0 c0 h0 : CPolyG β,
    cRdeNormalDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel ftilde.1.1 ftilde.1.2
        gtilde.1.1 gtilde.1.2 = some (a0, b0, c0, h0) →
      toPolyG gtilde.1.2 ∣ toPolyG (CPolyG.cmulG (CPolyG.cmulG
        (CPolyG.cSplitFactorFastG ([CField.one] : CPolyG β) towerRischDEFuel ftilde.1.2).1 h0) h0)
  /-- §6.2 fuel bound on the `B`-numerator. -/
  hfbB : ∀ a0 b0 c0 h0 : CPolyG β,
    cRdeNormalDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel ftilde.1.1 ftilde.1.2
        gtilde.1.1 gtilde.1.2 = some (a0, b0, c0, h0) →
      (CPolyG.cnormG (CPolyG.csubG
        (CPolyG.cmulG (CPolyG.cmulG
          (CPolyG.cSplitFactorFastG ([CField.one] : CPolyG β) towerRischDEFuel ftilde.1.2).1 h0)
          ftilde.1.1)
        (CPolyG.cmulG (CPolyG.cmulG
          (CPolyG.cSplitFactorFastG ([CField.one] : CPolyG β) towerRischDEFuel ftilde.1.2).1
            (CPolyG.cmonomialDeriv ([CField.one] : CPolyG β) h0)) ftilde.1.2)) : List β).length
        ≤ towerRischDEFuel
  /-- §6.2 fuel bound on the `C`-numerator. -/
  hfbC : ∀ a0 b0 c0 h0 : CPolyG β,
    cRdeNormalDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel ftilde.1.1 ftilde.1.2
        gtilde.1.1 gtilde.1.2 = some (a0, b0, c0, h0) →
      (CPolyG.cnormG (CPolyG.cmulG (CPolyG.cmulG (CPolyG.cmulG
        (CPolyG.cSplitFactorFastG ([CField.one] : CPolyG β) towerRischDEFuel ftilde.1.2).1 h0) h0)
        gtilde.1.1) : List β).length ≤ towerRischDEFuel
  /-- The §6.4 per-level transparent-input chain `CSPDEGClearedInputsGen` (gcd clauses via the witness). -/
  hin : ∀ a0 b0 c0 h0 : CPolyG β,
    cRdeNormalDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel ftilde.1.1 ftilde.1.2
        gtilde.1.1 gtilde.1.2 = some (a0, b0, c0, h0) →
      CSPDEGClearedInputsGen ([CField.one] : CPolyG β) towerRischDEFuel
        (cRdeSpecialDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel a0 b0 c0).1
        (cRdeSpecialDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel a0 b0 c0).2.1
        (cRdeSpecialDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel a0 b0 c0).2.2.1
        (cRdeBoundDegreeG ([CField.one] : CPolyG β) towerRischDEFuel
          (cRdeSpecialDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel a0 b0 c0).1
          (cRdeSpecialDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel a0 b0 c0).2.1
          (cRdeSpecialDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel a0 b0 c0).2.2.1 : ℤ)
  /-- The positive-`deg(bbar)` dispatcher side-condition (Lemma 6.5.1 non-cancellation routing). -/
  hdb : ∀ a0 b0 c0 bbar cbar : CPolyG β, ∀ m : ℤ, ∀ α' β' : CPolyG β,
    cSPDEG ([CField.one] : CPolyG β) towerRischDEFuel
        (cRdeSpecialDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel a0 b0 c0).1
        (cRdeSpecialDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel a0 b0 c0).2.1
        (cRdeSpecialDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel a0 b0 c0).2.2.1
        (cRdeBoundDegreeG ([CField.one] : CPolyG β) towerRischDEFuel
          (cRdeSpecialDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel a0 b0 c0).1
          (cRdeSpecialDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel a0 b0 c0).2.1
          (cRdeSpecialDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel a0 b0 c0).2.2.1 : ℤ)
      = some (bbar, cbar, m, α', β') → 0 < cdegG bbar

omit [CDiffFieldSpec β] [CFieldDomain β] [CRischField β] [CTowerGcdWitness β]
  [Algebra ℚ (CFieldSpec.K β)] in
/-- **The full crux from the normalized residual + the normalization guarantee**
(`residualCrux_of_residualNorm`): given the §6.1 normalization guarantee `IsWeaklyNormalizedNorm f̃`, the
per-run residual `RischDESuccessResidualNorm f̃ g̃` rebuilds the full reduced crux
`RischDESuccessResidualCrux f̃ g̃` — the missing `B`-divisibility clause `hdvdB_dn_h` supplied by
`isWeaklyNormalizedNorm_dvdB` (the §6.2 self-divisibility wall, discharged from `f`-normality alone), the
`C`-divisibility `hdvdC_dn_h2` carried through from the residual (the `g`-side cross condition outside
`dvd_dn_h_of_normal`'s reach). The `B`-divisibility wall closed from normality. -/
theorem residualCrux_of_residualNorm (ftilde gtilde : QFunNZG β)
    (hnorm : IsWeaklyNormalizedNorm ftilde)
    (hres : RischDESuccessResidualNorm ftilde gtilde) :
    RischDESuccessResidualCrux ftilde gtilde where
  hdn := hres.hdn
  hdvdB_dn_h _ _ _ h0 _ := isWeaklyNormalizedNorm_dvdB ftilde h0 hnorm
  hdvdC_dn_h2 := hres.hdvdC_dn_h2
  hfbB := hres.hfbB
  hfbC := hres.hfbC
  hin := hres.hin
  hdb := hres.hdb

/-- **★★ The CORRECT (normalized) recursive RDE solver is sound — `B`-divisibility wall CLOSED** (Task 4,
the capstone): if the normalized solver succeeds (`crischDESolveNorm f g = some y`), then with the gcd
witness `[CTowerGcdWitness β]`, the §6.1 normalization guarantee `IsWeaklyNormalizedNorm (weakNormalizedF f
q')` (the ONE isolated normalization-correctness fact, `q' = cWeakNormalizerG`'s output), and the residual
`RischDESuccessResidualNorm` (the crux with the §6.2 `B`-divisibility clause `hdvdB_dn_h` REMOVED — the
`C`-divisibility + per-run fuel remain), the returned `y` solves the field-level Risch DE for the ORIGINAL
`f, g`: `towerFractionFieldDerivG [1] (Y) + F·Y = G` over `RatFunc (CFieldSpec.K β)`. Composes: the
normalization guarantee discharges the §6.2 `B`-divisibility crux (`residualCrux_of_residualNorm` →
`crischDESolve_field_of_crux`) giving the inner identity for `f̃ = f − Dq/q`, `g̃ = q·g`; `roundtrip_field`
(the §6.1 substitution `y = ỹ/q`) transforms it back to `f, g`. **No `native_decide`; the `B`-divisibility
wall — the §6.2 self-divisibility `dvd_dn_h_of_normal` targets — is closed for the correct algorithm,
modulo only the single normalization-correctness fact (the `C`-divisibility + per-run fuel are a distinct
`g`-side condition + generic fuel-boundedness, not the wall).** -/
theorem crischDESolveNorm_field (f g y : QFunNZG β)
    (hsolve : crischDESolveNorm f g = some y)
    (hnorm : IsWeaklyNormalizedNorm
      (weakNormalizedF f (qOfPolyNZG
        (cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2))))
    (hres : RischDESuccessResidualNorm
      (weakNormalizedF f (qOfPolyNZG
        (cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2)))
      (qmulNZG (qOfPolyNZG
        (cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2)) g)) :
    towerFractionFieldDerivG ([CField.one] : CPolyG β)
          (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
        + amG β (toPolyG f.1.1) / amG β (toPolyG f.1.2)
          * (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
      = amG β (toPolyG g.1.1) / amG β (toPolyG g.1.2) := by
  -- abbreviations
  set q : CPolyG β := cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2 with hq
  set q' : QFunNZG β := qOfPolyNZG q with hq'
  set ftilde : QFunNZG β := weakNormalizedF f q' with hft
  set gtilde : QFunNZG β := qmulNZG q' g with hgt
  -- unfold the solver to its guard-then-match form (`set`s fold the inner `let`s)
  rw [show crischDESolveNorm f g
      = (if CPolyG.cisZeroG q then none
         else match CRischField.crischDESolve ftilde gtilde with
              | none => none
              | some ytilde => some (qmulNZG ytilde (qinvNZG q'))) from rfl] at hsolve
  by_cases hqz : CPolyG.cisZeroG q = true
  · rw [if_pos hqz] at hsolve; exact absurd hsolve (by simp)
  · rw [if_neg hqz] at hsolve
    rcases hinner : CRischField.crischDESolve ftilde gtilde with _ | ytilde <;>
      rw [hinner] at hsolve
    · exact absurd hsolve (by simp)
    · rw [Option.some.injEq] at hsolve
      -- the inner field identity for `f̃, g̃, ytilde` from the discharged crux
      have hqfalse : CPolyG.cisZeroG q = false := by simpa using hqz
      have hQ : toQFunNZG q' ≠ 0 := toQFunNZG_qOfPolyNZG_ne_zero q hqfalse
      have hcrux : RischDESuccessResidualCrux ftilde gtilde :=
        residualCrux_of_residualNorm ftilde gtilde hnorm hres
      have hfield := crischDESolve_field_of_crux ftilde gtilde ytilde hinner hcrux
      -- read the identity in `toQFunNZG` form (the `amG/toPolyG` division IS `toQFunNZG`)
      have hfield' : towerFractionFieldDerivG ([CField.one] : CPolyG β) (toQFunNZG ytilde)
            + toQFunNZG ftilde * toQFunNZG ytilde = toQFunNZG gtilde := hfield
      -- rewrite the inner identity into the `roundtrip_field` hypothesis form
      rw [toQFunNZG_weakNormalizedF f q', toQFunNZG_scaledRHS q' g] at hfield'
      -- apply the §6.1 round-trip: `Y = Ỹ/Q` solves the original
      have hround := roundtrip_field (towerFractionFieldDerivG ([CField.one] : CPolyG β))
        (toQFunNZG f) (toQFunNZG g) (toQFunNZG q') (toQFunNZG ytilde) hQ hfield'
      -- match the goal: `y = ytilde·q'⁻¹`, so `Y = Ỹ/Q`
      rw [← hsolve]
      show towerFractionFieldDerivG ([CField.one] : CPolyG β) (toQFunNZG (qmulNZG ytilde (qinvNZG q')))
          + toQFunNZG f * toQFunNZG (qmulNZG ytilde (qinvNZG q')) = toQFunNZG g
      rw [toQFunNZG_solution ytilde q']
      exact hround

end Capstone

/-! ### Restatement against the intended wording (anonymous `example`) -/

-- ★ Task 4: the normalized recursive solver's success ⟹ the ORIGINAL field-level Risch-DE identity, from
-- the gcd witness + the ONE normalization guarantee + the residual with the B-divisibility wall removed
-- (no native_decide).
example {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
    [CFracGcdCore β] [CRischField β] [CTowerGcdWitness β] [Algebra ℚ (CFieldSpec.K β)]
    (f g y : QFunNZG β) (hsolve : crischDESolveNorm f g = some y)
    (hnorm : IsWeaklyNormalizedNorm
      (weakNormalizedF f (qOfPolyNZG
        (cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2))))
    (hres : RischDESuccessResidualNorm
      (weakNormalizedF f (qOfPolyNZG
        (cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2)))
      (qmulNZG (qOfPolyNZG
        (cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2)) g)) :
    towerFractionFieldDerivG ([CField.one] : CPolyG β)
          (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
        + amG β (toPolyG f.1.1) / amG β (toPolyG f.1.2)
          * (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
      = amG β (toPolyG g.1.1) / amG β (toPolyG g.1.2) :=
  crischDESolveNorm_field f g y hsolve hnorm hres

/-! ### Axiom audit (the capstone is axiom-clean, NO `native_decide`) -/

#print axioms roundtrip_field
#print axioms residualCrux_of_residualNorm
#print axioms crischDESolveNorm_field

end DeepWiki.SymbolicIntegration
