import DeepWiki.SymbolicIntegration.ComputableRischDESolveNorm

/-! # Closing the residual pieces of the normalized recursive RDE solver — `C`-side + the precise remainder

`ComputableRischDESolveNorm.crischDESolveNorm_field` closes the recursive transcendental RDE soundness
**modulo** `RischDESuccessResidualNorm` — the per-run residual with the `B`-divisibility clause already
removed (discharged by `isWeaklyNormalizedNorm_dvdB` from the §6.1 normalization guarantee
`IsWeaklyNormalizedNorm`). This file attacks the THREE remaining residual pieces, separating what is a
genuine theorem from the one precisely-isolated true remainder.

* **★ The `C`-side cross-divisibility `hdvdC_dn_h2` (Task 2) — a THEOREM from bare success + `g`-normality.**
  The engine's `cRdeNormalDenominatorG` returns `some` **only after** its own `cdvdG eₙ dₙh²` check passes
  (`eₙ` = `gden`'s §3.5 normal part), so on success `eₙ ∣ dₙh²` is honest (`dvd_of_cdvdG`). The residual
  asks `gden ∣ dₙh²`; bridging `eₙ ∣ dₙh²` to `gden ∣ dₙh²` needs exactly `gden ∣ eₙ`, i.e. `gden` equals
  its own normal part — the **precise dual** of `IsWeaklyNormalizedNorm` on the `g` side. With that one
  `g`-normality fact, `hdvdC_dn_h2` is a theorem (`cRdeNormalDenominatorG_dvdC`); we package it as
  `IsWeaklyNormalizedDen` + `isWeaklyNormalizedDen_dvdC_dn_h2` and assemble the `C`-clause of the residual
  from bare success alone (`hdvdC_dn_h2_of_success`).
* **The fuel/gcd discharge (Task 3) — the gcd half closed, the non-gcd fuel a genuine per-run condition.**
  `[CTowerGcdWitness β]` supplies the per-level gcd-correctness inside `CSPDEGClearedInputsGen`/`hin`
  (`cTowerWitness_assocReg`); the **non-gcd** fuel bounds (`hfbB`/`hfbC` `length ≤ 60`, the per-level fuel of
  `hin`, `hdb`, `hdn`) are genuine per-run termination, NOT `∀`-theorems — a too-small constant
  `towerRischDEFuel = 60` fails them on a large input. So they stay as the per-run residual.
* **★ The one true remainder (Task 1, stated precisely sharper than before).** `IsWeaklyNormalizedNorm
  (weakNormalizedF f q')` is, as *stated* (a **strict** equality `toPolyG (cSplitFactorFastG [1] _ den).1 =
  toPolyG den` on the **un-reduced product** denominator that `weakNormalizedF`/`qsubNZG`/`qmulNZG`
  produce), **not a theorem — it is false for general `f`**: `weakNormalizedF f q'`'s denominator is the
  *un-cancelled* product `fden · (q' stuff)`, which retains `fden`'s special factors, so its special part is
  a non-unit and the strict equality fails. The genuine §6.1 `WeakNormalizer` guarantee is about the
  **reduced** field element `f − Dq/q` *after canonicalization* — a property of `cWeakNormalizerG` composed
  with `cCanonicalRepFastG`, which the wrapper `crischDESolveNorm` does **not** apply. So the precise true
  remainder is: **`IsWeaklyNormalizedNorm` holds only on the canonicalized normal form, and `crischDESolveNorm`
  feeds the un-reduced product** — closing it needs either the abstract §6.1 `WeakNormalizer`-after-canonicalize
  correctness (over `cWeakNormalizerG`, an engine-side theorem) or a wrapper that canonicalizes. See the
  verdict.

The bar — `crischDESolveNorm_field_unconditional` with `[CTowerGcdWitness β]` only — is therefore **not**
fully reachable: the `C`-side and the witness-covered gcd clauses close, but the `f`-normality remainder
(false-as-stated on the un-reduced product) and the genuine per-run fuel bounds remain. We deliver the
genuine `C`-side theorem, the witness gcd discharge, and the sharp statement of the remainder. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG GBPolyCore

/-! ## ★ Task 2 — the `C`-side cross-divisibility `gden ∣ dₙh²` from bare success + `g`-normality

`cRdeNormalDenominatorG Dt fuel fnum fden gnum gden` returns `some (a, b, c, h)` **only** in the `then`
branch of `if cdvdG fuel eₙ (dₙ·h·h) then … else none`, where `eₙ = (cSplitFactorFastG Dt fuel gden).1` is
`gden`'s §3.5 normal part, `dₙ = (cSplitFactorFastG Dt fuel fden).1` is `fden`'s, and `h` is the returned
4th component. So a successful normal-denominator reduction **forces** `cdvdG fuel eₙ (dₙhh) = true`, hence
(`dvd_of_cdvdG`, `eₙ ≠ 0`) the honest divisibility `eₙ ∣ dₙhh`. This is the engine's own check; we extract
it. -/

section Cside

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFracGcdCore β]

omit [CFieldSpec β] in
/-- **A successful normal-denominator reduction forces its `cdvdG` check** (`cRdeNormalDenominatorG_cdvdG`):
if `cRdeNormalDenominatorG Dt fuel fnum fden gnum gden = some (a0, b0, c0, h0)`, then the engine's own
divisibility check `cdvdG fuel eₙ (dₙ·h0·h0) = true` held (`eₙ = (cSplitFactorFastG Dt fuel gden).1` the
normal part of `gden`, `dₙ = (cSplitFactorFastG Dt fuel fden).1`), and the returned `h0` is exactly the
`h = gcd(eₙ, eₙ')/gcd(p, p')` of §6.2. The `some`-branch is guarded by precisely this `cdvdG`. -/
theorem cRdeNormalDenominatorG_cdvdG (Dt : CPolyG β) (fuel : ℕ) (fnum fden gnum gden : CPolyG β)
    (a0 b0 c0 h0 : CPolyG β)
    (hsucc : CPolyG.cRdeNormalDenominatorG Dt fuel fnum fden gnum gden = some (a0, b0, c0, h0)) :
    CPolyG.cdvdG fuel (CPolyG.cSplitFactorFastG Dt fuel gden).1
        (CPolyG.cmulG (CPolyG.cmulG (CPolyG.cSplitFactorFastG Dt fuel fden).1
          (CPolyG.cdivG fuel
            (CFracGcdCore.cgcdFFCore fuel (CPolyG.cSplitFactorFastG Dt fuel gden).1
              (CPolyG.cderivG (CPolyG.cSplitFactorFastG Dt fuel gden).1))
            (CFracGcdCore.cgcdFFCore fuel
              (CFracGcdCore.cgcdFFCore fuel (CPolyG.cSplitFactorFastG Dt fuel fden).1
                (CPolyG.cSplitFactorFastG Dt fuel gden).1)
              (CPolyG.cderivG (CFracGcdCore.cgcdFFCore fuel
                (CPolyG.cSplitFactorFastG Dt fuel fden).1
                (CPolyG.cSplitFactorFastG Dt fuel gden).1))))) h0) = true := by
  -- unfold `cRdeNormalDenominatorG` to its guard-then-some form and read off the `cdvdG` from the `some`
  rw [CPolyG.cRdeNormalDenominatorG] at hsucc
  -- `h` in the engine is `cdivG (cgcdFFCore en en') (cgcdFFCore p p')`; the guard is `cdvdG en (dn·h·h)`
  set dn := (CPolyG.cSplitFactorFastG Dt fuel fden).1 with hdn
  set en := (CPolyG.cSplitFactorFastG Dt fuel gden).1 with hen
  set p := CFracGcdCore.cgcdFFCore fuel dn en with hp
  set hh := CPolyG.cdivG fuel (CFracGcdCore.cgcdFFCore fuel en (CPolyG.cderivG en))
    (CFracGcdCore.cgcdFFCore fuel p (CPolyG.cderivG p)) with hhh
  set dnh2 := CPolyG.cmulG (CPolyG.cmulG dn hh) hh with hdnh2
  by_cases hck : CPolyG.cdvdG fuel en dnh2 = true
  · -- success branch: the returned `h0` equals the engine's `hh`
    rw [if_pos hck] at hsucc
    rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq] at hsucc
    obtain ⟨_, _, _, hh0⟩ := hsucc
    -- rewrite the goal's `h0` to `hh`; both are the same engine division (`h0 = hh`)
    rw [← hh0]
    exact hck
  · rw [if_neg hck] at hsucc
    exact absurd hsucc (by simp)

omit [CFieldSpec β] in
/-- **The 4th component of a successful reduction is the engine's `h`** (`cRdeNormalDenominatorG_h0_eq`):
if `cRdeNormalDenominatorG Dt fuel fnum fden gnum gden = some (a0, b0, c0, h0)`, then `h0 =
cdivG fuel (cgcdFFCore eₙ eₙ') (cgcdFFCore p p')` — the §6.2 `h = gcd(eₙ, eₙ')/gcd(p, p')`
(`eₙ = (cSplitFactorFastG Dt fuel gden).1`, `p = gcd(dₙ, eₙ)`). Read off the `some`-branch's tuple, so the
`h0` quantified in the residual is pinned to the engine's `h` from bare success — no extra hypothesis. -/
theorem cRdeNormalDenominatorG_h0_eq (Dt : CPolyG β) (fuel : ℕ) (fnum fden gnum gden : CPolyG β)
    (a0 b0 c0 h0 : CPolyG β)
    (hsucc : CPolyG.cRdeNormalDenominatorG Dt fuel fnum fden gnum gden = some (a0, b0, c0, h0)) :
    h0 = CPolyG.cdivG fuel
      (CFracGcdCore.cgcdFFCore fuel (CPolyG.cSplitFactorFastG Dt fuel gden).1
        (CPolyG.cderivG (CPolyG.cSplitFactorFastG Dt fuel gden).1))
      (CFracGcdCore.cgcdFFCore fuel
        (CFracGcdCore.cgcdFFCore fuel (CPolyG.cSplitFactorFastG Dt fuel fden).1
          (CPolyG.cSplitFactorFastG Dt fuel gden).1)
        (CPolyG.cderivG (CFracGcdCore.cgcdFFCore fuel
          (CPolyG.cSplitFactorFastG Dt fuel fden).1
          (CPolyG.cSplitFactorFastG Dt fuel gden).1))) := by
  rw [CPolyG.cRdeNormalDenominatorG] at hsucc
  set dn := (CPolyG.cSplitFactorFastG Dt fuel fden).1 with hdn
  set en := (CPolyG.cSplitFactorFastG Dt fuel gden).1 with hen
  set p := CFracGcdCore.cgcdFFCore fuel dn en with hp
  set hh := CPolyG.cdivG fuel (CFracGcdCore.cgcdFFCore fuel en (CPolyG.cderivG en))
    (CFracGcdCore.cgcdFFCore fuel p (CPolyG.cderivG p)) with hhh
  set dnh2 := CPolyG.cmulG (CPolyG.cmulG dn hh) hh with hdnh2
  by_cases hck : CPolyG.cdvdG fuel en dnh2 = true
  · rw [if_pos hck] at hsucc
    rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq] at hsucc
    exact hsucc.2.2.2.symm
  · rw [if_neg hck] at hsucc
    exact absurd hsucc (by simp)

/-- **The honest `eₙ ∣ dₙh0²` from a successful reduction** (`cRdeNormalDenominatorG_en_dvd`): with `eₙ =
(cSplitFactorFastG Dt fuel gden).1` nonzero, a successful `cRdeNormalDenominatorG = some (a0, b0, c0, h0)`
gives the honest divisibility `toPolyG eₙ ∣ toPolyG (dₙ·h0·h0)` — the engine's `cdvdG` check
(`cRdeNormalDenominatorG_cdvdG`) read through `dvd_of_cdvdG`, with `h0` pinned to the engine's `h`
(`cRdeNormalDenominatorG_h0_eq`). Driven purely by bare success + `eₙ ≠ 0`. -/
theorem cRdeNormalDenominatorG_en_dvd (Dt : CPolyG β) (fuel : ℕ) (fnum fden gnum gden : CPolyG β)
    (a0 b0 c0 h0 : CPolyG β)
    (hen0 : CPolyG.cnormG (CPolyG.cSplitFactorFastG Dt fuel gden).1 ≠ [])
    (hsucc : CPolyG.cRdeNormalDenominatorG Dt fuel fnum fden gnum gden = some (a0, b0, c0, h0)) :
    toPolyG (CPolyG.cSplitFactorFastG Dt fuel gden).1
      ∣ toPolyG (CPolyG.cmulG (CPolyG.cmulG (CPolyG.cSplitFactorFastG Dt fuel fden).1 h0) h0) := by
  have hck := cRdeNormalDenominatorG_cdvdG Dt fuel fnum fden gnum gden a0 b0 c0 h0 hsucc
  have hh0 := cRdeNormalDenominatorG_h0_eq Dt fuel fnum fden gnum gden a0 b0 c0 h0 hsucc
  -- `cRdeNormalDenominatorG_cdvdG` checks `dₙ·hh·hh` with `hh = h0`; rewrite to the goal's `dₙ·h0·h0`
  rw [← hh0] at hck
  exact CPolyG.dvd_of_cdvdG fuel _ _ hen0 hck

end Cside

/-! ## The `g`-side normality dual `IsWeaklyNormalizedDen` and the discharged `C`-divisibility

`IsWeaklyNormalizedDen gden` is the **precise dual** of `IsWeaklyNormalizedNorm` on the `g` denominator:
`gden` equals its own §3.5 normal part. Under it, `gden ∣ eₙ` is `gden ∣ gden` (trivial), so the engine's
honest `eₙ ∣ dₙh0²` upgrades to the residual's `gden ∣ dₙh0²` — closing `hdvdC_dn_h2`. -/

section Cnorm

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFracGcdCore β]

/-- **The `g`-denominator normality dual** `IsWeaklyNormalizedDen gden`: `gden` equals its own §3.5 normal
part `toPolyG (cSplitFactorFastG [1] _ gden).1 = toPolyG gden` (the special part of `gden` is a unit). The
precise dual of `IsWeaklyNormalizedNorm` on the `g` side; under it the engine's `eₙ ∣ dₙh²` (with
`eₙ = gden`'s normal part) reads as the residual's `gden ∣ dₙh²`. -/
def IsWeaklyNormalizedDen (gden : CPolyG β) : Prop :=
  toPolyG (CPolyG.cSplitFactorFastG ([CField.one] : CPolyG β) towerRischDEFuel gden).1
    = toPolyG gden

/-- **★ The `C`-divisibility from bare success + `g`-normality** (`isWeaklyNormalizedDen_dvdC_dn_h2`): if
`gden = gtilde.1.2` is weakly normalized (`IsWeaklyNormalizedDen`), then a successful normal-denominator
reduction `cRdeNormalDenominatorG [1] fuel fnum fden gnum gden = some (a0, b0, c0, h0)` yields the residual's
§6.2 `C`-divisibility `gden ∣ dₙ·h0²` — the engine's honest `eₙ ∣ dₙh0²` (`cRdeNormalDenominatorG_en_dvd`)
with `eₙ` rewritten to `gden` by the normality equality. The `g`-side cross-divisibility is a theorem on
`g`-normal input + bare success. -/
theorem isWeaklyNormalizedDen_dvdC_dn_h2 (fnum fden gnum gden : CPolyG β)
    (a0 b0 c0 h0 : CPolyG β)
    (hnorm : IsWeaklyNormalizedDen gden)
    (hen0 : CPolyG.cnormG (CPolyG.cSplitFactorFastG ([CField.one] : CPolyG β) towerRischDEFuel gden).1
      ≠ [])
    (hsucc : CPolyG.cRdeNormalDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel
      fnum fden gnum gden = some (a0, b0, c0, h0)) :
    toPolyG gden ∣ toPolyG (CPolyG.cmulG
      (CPolyG.cmulG (CPolyG.cSplitFactorFastG ([CField.one] : CPolyG β) towerRischDEFuel fden).1 h0)
      h0) := by
  have hdvd := cRdeNormalDenominatorG_en_dvd ([CField.one] : CPolyG β) towerRischDEFuel
    fnum fden gnum gden a0 b0 c0 h0 hen0 hsucc
  -- the honest divisibility is `eₙ ∣ dₙh0²`; rewrite `eₙ`'s toPolyG to `gden`'s via normality
  rwa [hnorm] at hdvd

/-- **`eₙ ≠ 0` from `g`-normality + `gden ≠ 0`** (`cnormG_en_ne_nil_of_normalizedDen`): if `gden` is weakly
normalized (`IsWeaklyNormalizedDen`, so its normal part `eₙ` has `toPolyG eₙ = toPolyG gden`) and `gden ≠ 0`
(`cnormG gden ≠ []`), then `cnormG eₙ ≠ []`. The `eₙ ≠ 0` side-condition of the `C`-divisibility, derived
from `g`-normality + the `QFunNZG` subtype proof — so the `C`-clause needs only `IsWeaklyNormalizedDen`. -/
theorem cnormG_en_ne_nil_of_normalizedDen (gden : CPolyG β)
    (hnorm : IsWeaklyNormalizedDen gden) (hgden0 : CPolyG.cnormG gden ≠ []) :
    CPolyG.cnormG (CPolyG.cSplitFactorFastG ([CField.one] : CPolyG β) towerRischDEFuel gden).1 ≠ [] := by
  intro he
  -- `cnormG eₙ = []` ⟹ `toPolyG eₙ = 0` ⟹ (normality) `toPolyG gden = 0` ⟹ `cnormG gden = []`, contra
  have hez : toPolyG (CPolyG.cSplitFactorFastG ([CField.one] : CPolyG β) towerRischDEFuel gden).1 = 0 :=
    (CPolyG.cnormG_eq_nil_iff _).mp he
  rw [hnorm] at hez
  exact hgden0 ((CPolyG.cnormG_eq_nil_iff gden).mpr hez)

end Cnorm

/-! ## ★ Task 2 (assembled) — the residual's `hdvdC_dn_h2` clause from `g`-normality alone

The `RischDESuccessResidualNorm.hdvdC_dn_h2` field, for the normalized solver's `(ftilde, gtilde)`, is
exactly the universally-quantified `gtilde.1.2 ∣ dₙh0²` over successful normal-denominator reductions. We
build it from a *single* `g`-normality hypothesis `IsWeaklyNormalizedDen gtilde.1.2` — `hen0` is derived
(`cnormG_en_ne_nil_of_normalizedDen` from the `QFunNZG` subtype proof), so the whole `C`-clause is closed by
bare success + the one dual normality fact, matching the `B`-clause's `IsWeaklyNormalizedNorm` discharge. -/

section CResidualClause

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFieldDomain β] [CFracGcdCore β]

omit [CFieldDomain β] in
/-- **★ The residual's `C`-divisibility clause from `g`-normality** (`residualNorm_hdvdC_of_normalizedDen`):
for the normalized solver's pair `ftilde, gtilde : QFunNZG β`, given `IsWeaklyNormalizedDen gtilde.1.2` (the
`g`-side normality dual), the `RischDESuccessResidualNorm.hdvdC_dn_h2` clause holds — for every successful
`cRdeNormalDenominatorG [1] fuel ftilde.1.1 ftilde.1.2 gtilde.1.1 gtilde.1.2 = some (a0,b0,c0,h0)`,
`gtilde.1.2 ∣ dₙ·h0²`. The `eₙ ≠ 0` side-condition comes from `cnormG_en_ne_nil_of_normalizedDen` (the
subtype proof `gtilde.2`). So the `C`-clause is closed by bare success + the single dual normality fact,
exactly mirroring the `B`-clause discharge. -/
theorem residualNorm_hdvdC_of_normalizedDen (ftilde gtilde : QFunNZG β)
    (hnorm : IsWeaklyNormalizedDen gtilde.1.2) :
    ∀ a0 b0 c0 h0 : CPolyG β,
      CPolyG.cRdeNormalDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel
          ftilde.1.1 ftilde.1.2 gtilde.1.1 gtilde.1.2 = some (a0, b0, c0, h0) →
        toPolyG gtilde.1.2 ∣ toPolyG (CPolyG.cmulG (CPolyG.cmulG
          (CPolyG.cSplitFactorFastG ([CField.one] : CPolyG β) towerRischDEFuel ftilde.1.2).1 h0) h0) := by
  intro a0 b0 c0 h0 hsucc
  have hen0 : CPolyG.cnormG
      (CPolyG.cSplitFactorFastG ([CField.one] : CPolyG β) towerRischDEFuel gtilde.1.2).1 ≠ [] :=
    cnormG_en_ne_nil_of_normalizedDen gtilde.1.2 hnorm
      (cnormG_ne_nil_of_cisZeroG_false gtilde.2)
  exact isWeaklyNormalizedDen_dvdC_dn_h2 ftilde.1.1 ftilde.1.2 gtilde.1.1 gtilde.1.2
    a0 b0 c0 h0 hnorm hen0 hsucc

end CResidualClause
/-! ## Task 3 — the fuel/termination clauses: the gcd half closed by the witness, the rest a genuine residual

The residual `RischDESuccessResidualNorm` carries, besides the now-closed `C`-divisibility, the per-run
clauses `hdn`/`hfbB`/`hfbC`/`hin`/`hdb`. We pin precisely how far `[CTowerGcdWitness β]` reaches into them.

`CSPDEGClearedInputsGen` (`hin`'s payload) interleaves, **per recursion level**, the gcd-correctness clause
`Associated (toPolyG g) (gcd …)` with the non-gcd fuel/termination clauses (`cnormG _ ≠ []`, the three
`length ≤ fuel` bounds, `cgcdTerminatesG`). `[CTowerGcdWitness β]` discharges the gcd half — for the
level-`β` content-gcd this is `cTowerWitness_assocReg` (the §6.4 per-step `CPrimPRSGenAssocReg` from the
witness + the run's own termination + fuel). But the **non-gcd** clauses are genuine per-run termination: the
constant fuel `towerRischDEFuel = 60` makes `length ≤ 60` **false** on any input whose intermediate
polynomials exceed 60 list-entries, so `hfbB`/`hfbC`/the `length`-bounds-inside-`hin`/`hdb`/`hdn` are NOT
`∀`-theorems. They are exactly the fuel-boundedness every fuel-bounded computable solver carries. -/

section Fuel

variable {α : Type*} [CField α] [CFieldSpec α] [CFracGcdCore α] [CTowerGcdWitness α]

/-- **The witness discharges the per-step gcd-correctness inside `hin`** (`towerGcd_assocReg_for_hin`): for
any level-`α` content-gcd PRS run satisfying its own termination `CPrimPRSGenRegular` and fuel
`CPrimPRSGenFuelOk` on `(P, Q)`, the per-step regularity bundle `CPrimPRSGenAssocReg` — whose `Associated`
content is exactly the gcd clause appearing per level in `CSPDEGClearedInputsGen` — holds from
`[CTowerGcdWitness α]` (`cTowerWitness_assocReg`). The gcd half of the `hin` chain is witness-covered; the
interleaved non-gcd fuel/termination clauses remain the genuine per-run residual. -/
theorem towerGcd_assocReg_for_hin (fuel : ℕ) (P Q : GBPolyCore α)
    (hreg : CPrimPRSGenRegular (CFracGcdCore.cgcdFFRawCore (α := α) fuel) fuel P Q)
    (hfuel : CPrimPRSGenFuelOk (CFracGcdCore.cgcdFFRawCore (α := α) fuel) fuel P Q) :
    CPrimPRSGenAssocReg (CFracGcdCore.cgcdFFRawCore (α := α) fuel) fuel P Q :=
  cTowerWitness_assocReg fuel P Q hreg hfuel

end Fuel

/-! ## ★ Task 4 (honest assembly) — the capstone with the `C`-divisibility DISCHARGED

We assemble as far as the closed pieces allow: a smaller residual `RischDESuccessResidualNormFuel` carrying
**only** the genuine per-run fuel/termination clauses (`hdn`/`hfbB`/`hfbC`/`hin`/`hdb`) — the `C`-divisibility
clause `hdvdC_dn_h2` is **REMOVED**, discharged instead from the single `g`-normality fact
`IsWeaklyNormalizedDen gtilde.1.2` (`residualNorm_hdvdC_of_normalizedDen`). `residualNorm_of_fuel_and_dvdC`
rebuilds the full `RischDESuccessResidualNorm` from the fuel residual + that `g`-normality fact, and
`crischDESolveNorm_field_of_fuel` chains to `crischDESolveNorm_field` — so the original-`f,g` field identity
holds from: the gcd witness, the `f`-normality `IsWeaklyNormalizedNorm` (the one true remainder), the
`g`-normality `IsWeaklyNormalizedDen` (its dual, also a §6.1 fact), and the genuine fuel residual — with the
`C`-divisibility no longer a hypothesis. NO `native_decide`. -/

section Assembly

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
  [CFracGcdCore β] [CRischField β] [CTowerGcdWitness β] [Algebra ℚ (CFieldSpec.K β)]

/-- **The genuine fuel/termination residual** `RischDESuccessResidualNormFuel ftilde gtilde`: exactly the
per-run fuel/termination clauses of `RischDESuccessResidualNorm` with the `C`-divisibility `hdvdC_dn_h2`
**removed** (that clause is discharged from `g`-normality). Carries `hdn` (normal part nonzero), the §6.2
fuel bounds `hfbB`/`hfbC`, the §6.4 transparent-input chain `hin` (gcd clauses via the witness), and the
dispatcher `hdb`. These are the irreducible per-run fuel-boundedness every fuel-bounded computable solver
carries — NOT a divisibility precondition. -/
structure RischDESuccessResidualNormFuel (ftilde gtilde : QFunNZG β) : Prop where
  /-- The normal part `dₙ` of `f̃den` is nonzero. -/
  hdn : ∀ a0 b0 c0 h0 : CPolyG β,
    cRdeNormalDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel ftilde.1.1 ftilde.1.2
        gtilde.1.1 gtilde.1.2 = some (a0, b0, c0, h0) →
      toPolyG (CPolyG.cSplitFactorFastG ([CField.one] : CPolyG β) towerRischDEFuel ftilde.1.2).1 ≠ 0
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
/-- **★ The full normalized residual from the fuel residual + `g`-normality**
(`residualNorm_of_fuel_and_dvdC`): given the genuine fuel residual `RischDESuccessResidualNormFuel ftilde
gtilde` and the `g`-normality dual `IsWeaklyNormalizedDen gtilde.1.2`, the full
`RischDESuccessResidualNorm ftilde gtilde` holds — the missing `C`-divisibility clause `hdvdC_dn_h2` is
supplied by `residualNorm_hdvdC_of_normalizedDen` (a theorem on `g`-normal input + bare success). So the
`C`-clause is no longer a residual hypothesis; only the fuel/termination + the dual normality fact remain. -/
theorem residualNorm_of_fuel_and_dvdC (ftilde gtilde : QFunNZG β)
    (hgnorm : IsWeaklyNormalizedDen gtilde.1.2)
    (hfuel : RischDESuccessResidualNormFuel ftilde gtilde) :
    RischDESuccessResidualNorm ftilde gtilde where
  hdn := hfuel.hdn
  hdvdC_dn_h2 := residualNorm_hdvdC_of_normalizedDen ftilde gtilde hgnorm
  hfbB := hfuel.hfbB
  hfbC := hfuel.hfbC
  hin := hfuel.hin
  hdb := hfuel.hdb

/-- **★★ The normalized recursive RDE solver is sound — `C`-divisibility DISCHARGED, `B`-wall closed**
(Task 4, honest assembly): if `crischDESolveNorm f g = some y`, then with the gcd witness
`[CTowerGcdWitness β]`, the §6.1 `f`-normality guarantee `IsWeaklyNormalizedNorm (weakNormalizedF f q')`
(the ONE true remainder — false-as-stated on the un-reduced product, see `weakNormalizedF_den_eq`/the
verdict), the `g`-normality dual `IsWeaklyNormalizedDen (qmulNZG q' g).1.2`, and the genuine fuel residual
`RischDESuccessResidualNormFuel` (the `C`-divisibility clause REMOVED), the returned `y` solves the
field-level Risch DE for the ORIGINAL `f, g`. Composes `residualNorm_of_fuel_and_dvdC` (discharge the
`C`-clause from `g`-normality) with `crischDESolveNorm_field`. **No `native_decide`.** This is the strongest
honest assembly: the `C`-side and the witness gcd clauses are closed; what remains is the `f`-normality
guarantee (the precisely-isolated remainder), its `g`-side dual, and generic per-run fuel. -/
theorem crischDESolveNorm_field_of_fuel (f g y : QFunNZG β)
    (hsolve : crischDESolveNorm f g = some y)
    (hnorm : IsWeaklyNormalizedNorm
      (weakNormalizedF f (qOfPolyNZG
        (cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2))))
    (hgnorm : IsWeaklyNormalizedDen
      (qmulNZG (qOfPolyNZG
        (cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2)) g).1.2)
    (hfuel : RischDESuccessResidualNormFuel
      (weakNormalizedF f (qOfPolyNZG
        (cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2)))
      (qmulNZG (qOfPolyNZG
        (cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2)) g)) :
    towerFractionFieldDerivG ([CField.one] : CPolyG β)
          (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
        + amG β (toPolyG f.1.1) / amG β (toPolyG f.1.2)
          * (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
      = amG β (toPolyG g.1.1) / amG β (toPolyG g.1.2) :=
  crischDESolveNorm_field f g y hsolve hnorm
    (residualNorm_of_fuel_and_dvdC _ _ hgnorm hfuel)

end Assembly

/-! ### Restatement against the intended wording (anonymous `example`) -/

-- ★ Task 4 (honest assembly): the normalized solver's success ⟹ the ORIGINAL field-level Risch-DE identity
-- from the gcd witness + f-normality (the one remainder) + its g-side dual + the genuine fuel residual,
-- with the C-divisibility DISCHARGED (no longer a hypothesis), no native_decide.
example {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
    [CFracGcdCore β] [CRischField β] [CTowerGcdWitness β] [Algebra ℚ (CFieldSpec.K β)]
    (f g y : QFunNZG β) (hsolve : crischDESolveNorm f g = some y)
    (hnorm : IsWeaklyNormalizedNorm
      (weakNormalizedF f (qOfPolyNZG
        (cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2))))
    (hgnorm : IsWeaklyNormalizedDen
      (qmulNZG (qOfPolyNZG
        (cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2)) g).1.2)
    (hfuel : RischDESuccessResidualNormFuel
      (weakNormalizedF f (qOfPolyNZG
        (cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2)))
      (qmulNZG (qOfPolyNZG
        (cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2)) g)) :
    towerFractionFieldDerivG ([CField.one] : CPolyG β)
          (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
        + amG β (toPolyG f.1.1) / amG β (toPolyG f.1.2)
          * (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
      = amG β (toPolyG g.1.1) / amG β (toPolyG g.1.2) :=
  crischDESolveNorm_field_of_fuel f g y hsolve hnorm hgnorm hfuel

/-! ## ★ Task 1 — the precise true remainder: `IsWeaklyNormalizedNorm` is FALSE-as-stated on the un-reduced
product `crischDESolveNorm` feeds

The capstone's `hnorm` hypothesis is `IsWeaklyNormalizedNorm (weakNormalizedF f q')` — a **strict** equality
`toPolyG (cSplitFactorFastG [1] _ den).1 = toPolyG den` of `den := (weakNormalizedF f q').1.2` with its own
§3.5 normal part (the denominator's special part is a unit). The decisive fact: `weakNormalizedF`'s
denominator is an **un-reduced product** that *contains `fden = f.1.2` as a factor* — `qsubNZG`/`qaddNZG`/
`qmulNZG`/`towerDerivQFunNZG`/`qinvNZG` cross-multiply with **no gcd cancellation**. So the special part of
the product is at least the special part of `fden`, which is a non-unit whenever `f` is not already normal —
hence the strict equality **fails for general `f`**. The genuine §6.1 `WeakNormalizer` guarantee is about the
**reduced** field element `f − Dq/q` *after* `cCanonicalRepFastG`, which `crischDESolveNorm` does not apply.

We make the obstruction a **theorem** (not an assertion): the denominator factors as `cmulG fden X`. -/

section Remainder

variable {β : Type*} [CField β] [CDiffField β] [CFieldDomain β]

/-- **★ The un-reduced denominator of `weakNormalizedF` contains `fden` as a factor**
(`weakNormalizedF_den_eq`): when the weak normalizer is nonzero (`cisZeroG q = false`, the solver's guard),
the denominator of `weakNormalizedF f (qOfPolyNZG q)` is the **un-cancelled** product
`cmulG f.1.2 (cmulG (cmulG [1] [1]) q)` — `f`'s original denominator `f.1.2` times the squared
weak-normalizer denominator times `q`. No gcd reduction happens (`qsubNZG`/`qaddNZG`/`qmulNZG`/`qinvNZG`
cross-multiply raw), so `f.1.2` (with all its special factors) survives verbatim in the product. The
structural witness that `IsWeaklyNormalizedNorm (weakNormalizedF f (qOfPolyNZG q))` is **false** whenever
`f.1.2`'s special part is a non-unit — the precise true remainder. -/
theorem weakNormalizedF_den_eq (f : QFunNZG β) (q : CPolyG β) (hq : CPolyG.cisZeroG q = false) :
    (weakNormalizedF f (qOfPolyNZG q)).1.2
      = CPolyG.cmulG f.1.2 (CPolyG.cmulG (CPolyG.cmulG ([CField.one] : CPolyG β) [CField.one]) q) := by
  -- unfold the layered constructions; only `qinvNZG`'s branch depends on `cisZeroG q`
  show CPolyG.cmulG f.1.2 (CPolyG.cmulG
      (CPolyG.cmulG (qOfPolyNZG q).1.2 (qOfPolyNZG q).1.2) (qinvNZG (qOfPolyNZG q)).1.2)
    = CPolyG.cmulG f.1.2 (CPolyG.cmulG (CPolyG.cmulG [CField.one] [CField.one]) q)
  -- `(qOfPolyNZG q).1.2 = [1]`; `(qinvNZG (qOfPolyNZG q)).1.2 = q` on the `cisZeroG q = false` branch
  have hqfalse : CPolyG.cisZeroG (qOfPolyNZG q).1.1 = false := hq
  have hinv : (qinvNZG (qOfPolyNZG q)).1.2 = q := by
    rw [qinvNZG, dif_neg (by rw [hqfalse]; simp : ¬ CPolyG.cisZeroG (qOfPolyNZG q).1.1)]
    rfl
  rw [hinv]
  rfl

end Remainder

/-! ## ★ VERDICT — is the recursive solver FULLY UNCONDITIONALLY sound?

**No — the wall is NOT fully closed; the bar `crischDESolveNorm_field_unconditional` (witness-only) is not
reachable, and the obstruction is now pinned exactly.** Of the three residual pieces:

### (2) `C`-side cross-divisibility — ✅ CLOSED as a theorem (modulo the `g`-side normality dual)

`hdvdC_dn_h2` (`gden ∣ dₙh²`) is a **theorem** from bare success + the single `g`-normality fact
`IsWeaklyNormalizedDen gtilde.1.2` (`residualNorm_hdvdC_of_normalizedDen`): the engine's own `cdvdG eₙ dₙh²`
success-check gives the honest `eₙ ∣ dₙh²` (`cRdeNormalDenominatorG_en_dvd` via `dvd_of_cdvdG`), and
`gden = eₙ` (its own normal part) upgrades it to `gden ∣ dₙh²`. The `eₙ ≠ 0` side-condition is derived from
the `QFunNZG` subtype. This is the **exact dual** of the `B`-side `IsWeaklyNormalizedNorm` discharge — the
`C`-side is now at the same status as the `B`-side, NOT a separate wall.

### (3) Fuel/termination — ✅ gcd half closed by the witness, the non-gcd fuel a genuine per-run residual

`[CTowerGcdWitness β]` discharges the per-step gcd-correctness inside `hin` (`towerGcd_assocReg_for_hin` =
`cTowerWitness_assocReg`). The **non-gcd** clauses (`hfbB`/`hfbC` `length ≤ 60`, the `length`-bounds and
`cgcdTerminatesG` interleaved in `hin`, `hdb`, `hdn`) are genuine per-run termination — a too-small constant
`towerRischDEFuel = 60` falsifies them, so they are NOT `∀`-theorems. This is the fuel-boundedness every
fuel-bounded computable solver carries, not the divisibility wall.

### (1) ★ `IsWeaklyNormalizedNorm` — the ONE TRUE REMAINDER, now sharper: FALSE-as-stated on the wrapper's input

`crischDESolveNorm_field` needs `IsWeaklyNormalizedNorm (weakNormalizedF f q')`. This is **not a missing
theorem to be proven — as *stated* it is FALSE for general `f`**: `weakNormalizedF`'s denominator is the
**un-reduced product** `cmulG f.1.2 (cmulG (cmulG [1] [1]) q)` (`weakNormalizedF_den_eq`, a theorem), which
retains `f.1.2`'s special factors verbatim, so its §3.5 normal part is a **proper** divisor of the
denominator whenever `f.1.2` (or `q`) has a non-unit special part — the strict equality
`toPolyG (cSplitFactorFastG [1] _ den).1 = toPolyG den` then fails. The genuine §6.1 `WeakNormalizer`
guarantee is about the **canonicalized** `f − Dq/q` (after `cCanonicalRepFastG`), which the wrapper
`crischDESolveNorm` (a locked file) does **not** apply.

**So the true remainder is structural, not a divisibility wall**: closing it needs **either** (a) a wrapper
that canonicalizes (`cCanonicalRepFastG`) the weakly-normalized field element before feeding it to
`cRischDEG` — at which point the denominator IS its own normal part and `IsWeaklyNormalizedNorm` becomes a
theorem of §6.1 `WeakNormalizer`-after-canonicalize correctness over `cWeakNormalizerG`; **or** (b) the
abstract §6.1 correctness theorem over `cWeakNormalizerG` *plus* a residual rephrased on the canonical form.
Both are engine-side (touching the locked `crischDESolveNorm`/`cWeakNormalizerG`), out of this file's scope.

### Bottom line

The recursive transcendental RDE solver is **NOT yet fully unconditionally sound**. Two of the three residual
pieces close here: the `C`-side cross-divisibility (a theorem, dual to the `B`-side) and the witness-covered
gcd clauses. The single true remainder is the `f`-normality guarantee `IsWeaklyNormalizedNorm` — and the
sharper finding is that it is **false as stated on the un-reduced product** `crischDESolveNorm` feeds
(`weakNormalizedF_den_eq`), so it is closable only by canonicalizing the wrapper input (an engine change) or
the abstract §6.1 `WeakNormalizer`-after-canonicalize correctness — NOT by any theorem provable over the
current locked wrapper. The per-run fuel bounds remain as generic fuel-boundedness. -/

/-! ### Axiom audit (every result here is axiom-clean, NO `native_decide`) -/

#print axioms cRdeNormalDenominatorG_en_dvd
#print axioms residualNorm_hdvdC_of_normalizedDen
#print axioms towerGcd_assocReg_for_hin
#print axioms residualNorm_of_fuel_and_dvdC
#print axioms crischDESolveNorm_field_of_fuel
#print axioms weakNormalizedF_den_eq

end DeepWiki.SymbolicIntegration
