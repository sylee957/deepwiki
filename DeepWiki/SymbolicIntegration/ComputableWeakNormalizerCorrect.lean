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

end DeepWiki.SymbolicIntegration
