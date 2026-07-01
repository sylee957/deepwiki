import DeepWiki.SymbolicIntegration.ComputableRischDECompleteness
import DeepWiki.SymbolicIntegration.ComputableWeakNormalizerCorrect

/-! # §6.2 RDE completeness — the normal-denominator step preserves solvability (`hnorm`)

`RischDEInnerCompleteness` (`ComputableRischDECompleteness`) decomposes the deep §6 inner-solve
completeness into three converse clauses, `hnorm` / `hbound` / `hsolve`. `hbound` is produced (modulo a
precise cancellation residual) by `ComputableRischDEDegreeBound`; this file pursues `hnorm`.

**What `hnorm` says.** `hnorm` is the SOLVABILITY-PRESERVATION of Bronstein §6.2's `RdeNormalDenominator`:
*if the input RDE has a polynomial solution then the §6.2 reduction does not return `none`* —
`(∃ ynum yden, IsCRischDEGPolySol …) → (cRdeNormalDenominatorG …).isSome = true`. It is the **reverse**
direction of the §6.2 soundness step (whose forward `some ⟹ cleared-identity` is the proven soundness arc).

**The §6.2 transformation, made precise.** `cRdeNormalDenominatorG Dt fuel fnum fden gnum gden`
(`ComputableTowerRischDE`) splits the denominators into normal parts `dₙ = (cSplitFactorFastG Dt fuel
fden).1`, `eₙ = (cSplitFactorFastG Dt fuel gden).1`, forms `h = gcd(eₙ, eₙ')/gcd(p, p')`
(`p = gcd(dₙ, eₙ)`), and returns `some (a, b, c, h)` **iff the single guard `cdvdG fuel eₙ (dₙ·h·h)`
holds** — otherwise `none`. So the §6.2 step loses a solution **only** through that one divisibility gate,
and `hnorm` is **exactly**:

  a polynomial solution `⟹ cdvdG fuel eₙ (dₙ·h·h) = true`   (equivalently `(…).isSome = true`).

**The two-layer structure of `hnorm` (this file's contribution).**

* **The engine layer is fully reachable** and is closed here, axiom-clean (NO `native_decide`/`sorry`):
  - `cRdeNormalDenominatorG_isSome_iff` — the §6.2 step's `isSome` is *exactly* its `cdvdG` guard
    (`(…).isSome = true ↔ cdvdG fuel eₙ (dₙ·h·h) = true`), the precise control-flow reading.
  - `cdvdG_of_dvd` — the **converse of `dvd_of_cdvdG`**: a *mathematical* divisibility
    `toPolyG eₙ ∣ toPolyG (dₙ·h·h)` (with `eₙ ≠ 0` and the benign fuel bound) forces the engine check
    `cdvdG = true`, via the unique-remainder property of the §6.2 Euclidean `cmodG`.
  - `cRdeNormalDenominatorG_isSome_of_dvd` — composing the two: the *mathematical* §6.2 divisibility
    `eₙ ∣ dₙh²` makes the §6.2 step return `some`. This collapses `hnorm` to a single divisibility fact.

* **The mathematical divisibility is the irreducible §6.2 residual** (precisely isolated, NEVER `sorry`).
  That a *polynomial solution forces* `eₙ ∣ dₙh²` is **Bronstein Theorem 6.1.2** — the necessity of the
  normal-denominator divisibility, a valuation-theoretic fact at the normal poles that the engine does not
  self-certify (the soundness arc only ever *reads off* `eₙ ∣ dₙh²` from a successful `cdvdG`, never
  *derives* it from a solution). It is bundled as `RdeNormalDivisibilityResidual`, and `hnorm` is produced
  modulo it (`hnorm_of_divisibilityResidual`).

So `hnorm` reduces — through a fully proven engine layer — to the single mathematical divisibility
`solution ⟹ eₙ ∣ dₙh²` (Bronstein Thm 6.1.2), which is the precise §6.2 frontier. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

/-! ## The engine layer: `isSome` is exactly the `cdvdG` guard, and `dvd ⟹ cdvdG`

`cRdeNormalDenominatorG`'s body is `if cdvdG fuel eₙ (dₙ·h·h) then some (…) else none`. The `isSome` is
therefore *definitionally* the guard. And the engine `cdvdG` is honest in **both** directions on a nonzero
divisor with enough fuel: `dvd_of_cdvdG` is the proven forward read; `cdvdG_of_dvd` here is the converse,
from the §6.2 Euclidean division identity (`toPolyG_cdivmodG'`) and the unique-remainder property. -/

section EngineLayer

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CFracGcdCore α]

/-- **The §6.2 normal part `eₙ` of the `g`-denominator** `rdeNormEn Dt fuel gden`
(`= (cSplitFactorFastG Dt fuel gden).1`): the §3.5 normal part of `gden`, the divisor in the §6.2 guard
`cdvdG fuel eₙ (dₙ·h·h)`. An abbreviation pinning the §6.2 `cdvdG`-guard divisor without re-spelling the
splitting. -/
def rdeNormEn (Dt : CPolyG α) (fuel : ℕ) (gden : CPolyG α) : CPolyG α :=
  (CPolyG.cSplitFactorFastG Dt fuel gden).1

/-- **The §6.2 normal part `dₙ` of the `f`-denominator** `rdeNormDn Dt fuel fden`
(`= (cSplitFactorFastG Dt fuel fden).1`): the §3.5 normal part of `fden`, the `dₙ` in the §6.2 guard
`cdvdG fuel eₙ (dₙ·h·h)` and in the §6.2 dividend `dₙ·h²`. -/
def rdeNormDn (Dt : CPolyG α) (fuel : ℕ) (fden : CPolyG α) : CPolyG α :=
  (CPolyG.cSplitFactorFastG Dt fuel fden).1

/-- **The §6.2 multiplicity factor `h`** `rdeNormH Dt fuel fden gden`
(`= cdivWf (cgcdFFCore eₙ eₙ') (cgcdFFCore p p')`, `p = cgcdFFCore dₙ eₙ`): the §6.2
`h = gcd(eₙ, eₙ')/gcd(p, p')` of Bronstein p.185, the 4th component returned by a successful
`cRdeNormalDenominatorG` (`cRdeNormalDenominatorG_h0_eq`). Abbreviation pinning the §6.2 guard's `h`. -/
def rdeNormH (Dt : CPolyG α) (fuel : ℕ) (fden gden : CPolyG α) : CPolyG α :=
  CPolyG.cdivWf
    (CFracGcdCore.cgcdFFCore fuel (rdeNormEn Dt fuel gden) (CPolyG.cderivG (rdeNormEn Dt fuel gden)))
    (CFracGcdCore.cgcdFFCore fuel
      (CFracGcdCore.cgcdFFCore fuel (rdeNormDn Dt fuel fden) (rdeNormEn Dt fuel gden))
      (CPolyG.cderivG (CFracGcdCore.cgcdFFCore fuel
        (rdeNormDn Dt fuel fden) (rdeNormEn Dt fuel gden))))

/-- **The §6.2 dividend `dₙ·h²`** `rdeNormDnh2 Dt fuel fden gden`
(`= cmulG (cmulG dₙ h) h`): the dividend in the §6.2 guard `cdvdG fuel eₙ (dₙ·h·h)`. Abbreviation. -/
def rdeNormDnh2 (Dt : CPolyG α) (fuel : ℕ) (fden gden : CPolyG α) : CPolyG α :=
  CPolyG.cmulG (CPolyG.cmulG (rdeNormDn Dt fuel fden) (rdeNormH Dt fuel fden gden))
    (rdeNormH Dt fuel fden gden)

omit [CFieldSpec α] in
/-- **The §6.2 step's `isSome` is exactly its `cdvdG` guard** (`cRdeNormalDenominatorG_isSome_iff`):
`(cRdeNormalDenominatorG Dt fuel fnum fden gnum gden).isSome = true` **↔**
`cdvdG fuel (rdeNormEn …) (rdeNormDnh2 …) = true`, i.e. `eₙ ∣ dₙh²` *as the engine checks it*.
`cRdeNormalDenominatorG`'s body is `if cdvdG fuel eₙ (dₙ·h·h) then some (…) else none`, so its `isSome`
is *definitionally* the guard. The exact control-flow reading on which §6.2 completeness rests: a solution
forcing `some` is *precisely* a solution forcing this `cdvdG`. -/
theorem cRdeNormalDenominatorG_isSome_iff (Dt : CPolyG α) (fuel : ℕ) (fnum fden gnum gden : CPolyG α) :
    (CPolyG.cRdeNormalDenominatorG Dt fuel fnum fden gnum gden).isSome = true ↔
      CPolyG.cdvdG fuel (rdeNormEn Dt fuel gden) (rdeNormDnh2 Dt fuel fden gden) = true := by
  rw [CPolyG.cRdeNormalDenominatorG]
  simp only [rdeNormDnh2, rdeNormH, rdeNormDn, rdeNormEn]
  split <;> simp_all

omit [CDiffField α] [CFracGcdCore α] in
/-- **The converse of `dvd_of_cdvdG`: mathematical divisibility forces the engine check**
(`cdvdG_of_dvd`): if the divisor `q` is nonzero (`cnormG q ≠ []`), the fuel covers the dividend
(`(cnormG p).length ≤ fuel`), and `toPolyG q ∣ toPolyG p` **mathematically**, then `cdvdG fuel q p = true`.
The §6.2 Euclidean remainder `cmodG fuel p q` satisfies the division identity (`toPolyG_cdivmodG'`) and is
properly reduced (`cmodG_length_lt`); since `q ∣ p` it divides the remainder, which is then a `q`-multiple
of degree `< deg q` — hence `0` (`cdvdG_iff`). The exact converse of `dvd_of_cdvdG`; with it the §6.2
guard `cdvdG` is honest in **both** directions, so engine-`isSome` ⟺ mathematical `eₙ ∣ dₙh²`. -/
theorem cdvdG_of_dvd (fuel : ℕ) (q p : CPolyG α) (hq0 : CPolyG.cnormG q ≠ [])
    (hfuel : (CPolyG.cnormG p : List α).length ≤ fuel)
    (hdvd : toPolyG q ∣ toPolyG p) :
    CPolyG.cdvdG fuel q p = true := by
  rw [CPolyG.cdvdG_iff]
  -- `r := cmodG fuel p q` is the §6.2 remainder; show `toPolyG r = 0`.
  set r := CPolyG.cmodG fuel p q with hr
  -- the division identity: `toPolyG p = (quotient)·toPolyG q + toPolyG r`.
  have hid := CPolyG.toPolyG_cdivmodG' fuel p q hq0
  -- `cmodG fuel p q = (cdivmodG fuel p q).2` by definition; pin `r` to the `.2`.
  have hr2 : r = (CPolyG.cdivmodG fuel p q).2 := rfl
  rw [← hr2] at hid
  -- `q ∣ r`: `toPolyG r = toPolyG p − (quotient)·toPolyG q`, both summands `q`-divisible.
  have hqr : toPolyG q ∣ toPolyG r := by
    have heq : toPolyG r
        = toPolyG p - toPolyG (CPolyG.cdivmodG fuel p q).1 * toPolyG q := by
      rw [hid]; ring
    rw [heq]
    exact dvd_sub hdvd (Dvd.intro_left _ rfl)
  -- the remainder is properly reduced: `natDegree r < natDegree q` (when `r ≠ 0`).
  by_contra hrne
  have hrne' : toPolyG r ≠ 0 := hrne
  have hqne' : toPolyG q ≠ 0 := fun h => hq0 ((CPolyG.cnormG_eq_nil_iff q).mpr h)
  -- a nonzero `q`-multiple has degree `≥ deg q`.
  have hge : (toPolyG q).natDegree ≤ (toPolyG r).natDegree :=
    Polynomial.natDegree_le_of_dvd hqr hrne'
  -- but the §6.2 remainder is strictly shorter than `q`.
  have hlt := CPolyG.cmodG_length_lt fuel p q hq0 hfuel
  rw [← hr] at hlt
  have hrnil : CPolyG.cnormG r ≠ [] := fun h => hrne' ((CPolyG.cnormG_eq_nil_iff r).mp h)
  rw [CPolyG.length_cnormG_of_ne r hrnil, CPolyG.length_cnormG_of_ne q hq0] at hlt
  omega

/-- **The §6.2 step returns `some` from the mathematical §6.2 divisibility**
(`cRdeNormalDenominatorG_isSome_of_dvd`): with `eₙ = (cSplitFactorFastG Dt fuel gden).1` nonzero, the fuel
covering the dividend, and the **mathematical** divisibility `toPolyG eₙ ∣ toPolyG (dₙ·h²)`, the §6.2
reduction succeeds — `(cRdeNormalDenominatorG …).isSome = true`. Composes the control-flow reading
`cRdeNormalDenominatorG_isSome_iff` with the converse-divisibility bridge `cdvdG_of_dvd`. This collapses
`hnorm` to the single divisibility fact `eₙ ∣ dₙh²` (no engine internals left). -/
theorem cRdeNormalDenominatorG_isSome_of_dvd (Dt : CPolyG α) (fuel : ℕ)
    (fnum fden gnum gden : CPolyG α)
    (hen0 : CPolyG.cnormG (rdeNormEn Dt fuel gden) ≠ [])
    (hfuel : (CPolyG.cnormG (rdeNormDnh2 Dt fuel fden gden) : List α).length ≤ fuel)
    (hdvd : toPolyG (rdeNormEn Dt fuel gden) ∣ toPolyG (rdeNormDnh2 Dt fuel fden gden)) :
    (CPolyG.cRdeNormalDenominatorG Dt fuel fnum fden gnum gden).isSome = true :=
  (cRdeNormalDenominatorG_isSome_iff Dt fuel fnum fden gnum gden).mpr
    (cdvdG_of_dvd fuel _ _ hen0 hfuel hdvd)

end EngineLayer

/-! ## ★ The §6.2 divisibility residual (Bronstein Thm 6.1.2) and `hnorm` modulo it

The engine layer collapsed `hnorm` to the single mathematical divisibility `eₙ ∣ dₙh²` (plus two benign
engine side-conditions). That divisibility — *a polynomial solution forces* `eₙ ∣ dₙh²` — is **Bronstein
Theorem 6.1.2**, the necessity of the normal-denominator condition. It is genuinely deep: the cleared
identity `IsCRischDEGPolySol` is an equation in the polynomial ring, while `eₙ ∣ dₙh²` is a statement about
the **denominator's normal-pole structure** (factor `eₙ` into its squarefree normal poles and count the
order of `y` at each — the valuation-theoretic argument of §6.2). The engine never derives it from a
cleared identity; the soundness arc only ever *reads it off* a successful `cdvdG`
(`cRdeNormalDenominatorG_en_dvd`). So it is the irreducible §6.2 frontier, bundled here as
`RdeNormalDivisibilityResidual` (NEVER `sorry`), with `hnorm` produced modulo it. -/

section DivisibilityResidual

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCore α]
  [CRischField α]

/-- **★ The precise §6.2 divisibility residual** `RdeNormalDivisibilityResidual Dt fnum fden gnum gden`:
the converse facts a polynomial solution clears the §6.2 `none`-gate, all in solvability-implies form.
`hdvd`: ★ **Bronstein Theorem 6.1.2** — a `cRischDEG`-polynomial solution forces the mathematical
normal-denominator divisibility `toPolyG eₙ ∣ toPolyG (dₙ·h²)` (`eₙ = rdeNormEn …`, `dₙ = rdeNormDn …`,
`h = rdeNormH …`); the valuation-theoretic necessity at the normal poles, which the engine does not derive
from the cleared identity (it only reads it off a successful `cdvdG`) — the single deep §6.2 gap. The
actionable route: at each normal pole `p ∣ eₙ` the derivative drops the order by exactly one
(`p ∤ Dp`, normality), so a pole of `y` at `p` would leave `Dy` unbalanced in `Dy + fy = g`; Mathlib's
`Polynomial.derivative_rootMultiplicity_of_root_of_mem_nonZeroDivisors` is the per-pole drop, to be lifted
through `cValuationG`/`rootMultiplicity` over the tower — a full Thm 6.1.2 development, not done here.
`hen0`:
the §6.2 normal part `eₙ` is nonzero (benign: free when `gden ≠ 0` is weakly normalized,
`cnormG_en_ne_nil_of_normalizedDen`). `hfuel`: `towerRischDEFuel = 60` covers the §6.2 dividend's length
(benign per-run fuel). A `Prop`-bundle of stated assumptions, NO `sorry`; `hdvd` is the keystone. -/
structure RdeNormalDivisibilityResidual (Dt fnum fden gnum gden : CPolyG α) : Prop where
  /-- ★ Bronstein Thm 6.1.2: a polynomial solution forces the §6.2 divisibility `eₙ ∣ dₙh²`. -/
  hdvd : (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
    toPolyG (rdeNormEn Dt towerRischDEFuel gden)
      ∣ toPolyG (rdeNormDnh2 Dt towerRischDEFuel fden gden)
  /-- The §6.2 normal part `eₙ` of `gden` is nonzero (benign — free for weakly-normalized `gden ≠ 0`). -/
  hen0 : CPolyG.cnormG (rdeNormEn Dt towerRischDEFuel gden) ≠ []
  /-- The §6.2 fuel `towerRischDEFuel = 60` covers the dividend `dₙ·h²` (benign per-run fuel). -/
  hfuel : (CPolyG.cnormG (rdeNormDnh2 Dt towerRischDEFuel fden gden) : List α).length
    ≤ towerRischDEFuel

omit [CRischField α] in
/-- **★ `hnorm` from the §6.2 divisibility residual** (`hnorm_of_divisibilityResidual`): under
`RdeNormalDivisibilityResidual Dt fnum fden gnum gden`, the §6.2 normal-denominator step preserves
solvability — a polynomial solution makes `cRdeNormalDenominatorG` return `some`,
`(∃ ynum yden, IsCRischDEGPolySol …) → (cRdeNormalDenominatorG Dt towerRischDEFuel …).isSome = true`. This
is **exactly** the `hnorm` clause of `RischDEInnerCompleteness`. Feeds the residual's three facts (the deep
Bronstein-Thm-6.1.2 divisibility + the two benign engine side-conditions) into the fully-proven engine
bridge `cRdeNormalDenominatorG_isSome_of_dvd`. The §6.2 completeness clause, modulo the precisely isolated
deep divisibility. -/
theorem hnorm_of_divisibilityResidual (Dt fnum fden gnum gden : CPolyG α)
    (hres : RdeNormalDivisibilityResidual Dt fnum fden gnum gden) :
    (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
      (cRdeNormalDenominatorG Dt towerRischDEFuel fnum fden gnum gden).isSome = true := by
  intro hsol
  exact cRdeNormalDenominatorG_isSome_of_dvd Dt towerRischDEFuel fnum fden gnum gden
    hres.hen0 hres.hfuel (hres.hdvd hsol)

/-! ### When the §6.2 divisibility is FREE (the reachable cases of `hdvd`, unconditional)

The deep clause `hdvd` is *not* vacuous: it is genuinely free — independent of any solution — in the
structural cases where `eₙ` already divides `dₙ`. Then `eₙ ∣ dₙh²` by multiplying through by `h²`. The
`g`-side analogue of the soundness file's `dvd_dn_h_of_normal`/`dvd_dn_h_one`. These discharge `hdvd`
**unconditionally** on those inputs, so on them `hnorm` needs no Bronstein-Thm-6.1.2 input at all. -/

omit [CDiffFieldSpec α] [CRischField α] in
/-- **`eₙ ∣ dₙ` makes the §6.2 divisibility free** (`dvd_dnh2_of_en_dvd_dn`): if the normal part `eₙ` of
`gden` divides the normal part `dₙ` of `fden` (`toPolyG eₙ ∣ toPolyG dₙ`), then `eₙ ∣ dₙ·h²` for any `h` —
multiply the hypothesis by `h²`. The structural case where the §6.2 `cdvdG` guard passes regardless of a
solution; the `g`-side analogue of `dvd_dn_h_of_normal`. -/
theorem dvd_dnh2_of_en_dvd_dn (Dt : CPolyG α) (fuel : ℕ) (fden gden : CPolyG α)
    (hdvd : toPolyG (rdeNormEn Dt fuel gden) ∣ toPolyG (rdeNormDn Dt fuel fden)) :
    toPolyG (rdeNormEn Dt fuel gden) ∣ toPolyG (rdeNormDnh2 Dt fuel fden gden) := by
  rw [rdeNormDnh2, CPolyG.toPolyG_cmulG, CPolyG.toPolyG_cmulG]
  exact (hdvd.mul_right _).mul_right _

omit [CRischField α] in
/-- **`hdvd` is free when `eₙ ∣ dₙ`** (`hdvd_free_of_en_dvd_dn`): if `eₙ ∣ dₙ` then the deep §6.2
divisibility clause holds **unconditionally** (no solution hypothesis used) — the solution-implication of
`RdeNormalDivisibilityResidual.hdvd` collapses to `dvd_dnh2_of_en_dvd_dn`. On such inputs `hnorm`'s deep
keystone vanishes; the §6.2 step's `cdvdG` guard passes structurally. -/
theorem hdvd_free_of_en_dvd_dn (Dt fnum fden gnum gden : CPolyG α)
    (hdvd : toPolyG (rdeNormEn Dt towerRischDEFuel gden) ∣ toPolyG (rdeNormDn Dt towerRischDEFuel fden)) :
    (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
      toPolyG (rdeNormEn Dt towerRischDEFuel gden)
        ∣ toPolyG (rdeNormDnh2 Dt towerRischDEFuel fden gden) :=
  fun _ => dvd_dnh2_of_en_dvd_dn Dt towerRischDEFuel fden gden hdvd

end DivisibilityResidual

/-! ## ★ `RischDEInnerCompleteness` from the §6.2/§6.3/§6.4-6.6 residuals assembled

With `hnorm` produced here (`hnorm_of_divisibilityResidual`), `hbound` produced by
`ComputableRischDEDegreeBound` (modulo a cancellation residual), and `hsolve` the §6.4–6.6 exhaustiveness,
the full `RischDEInnerCompleteness` is assembled from its three component residuals. We record the
assembly that *consumes* a produced `hnorm`, so `RischDEInnerCompleteness` now needs only `hbound`
(nearly done) + `hsolve` (the deep SPDE/poly-RDE core) as the remaining `Prop` inputs. -/

section Assemble

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCore α]
  [CRischField α]

/-- **★ `RischDEInnerCompleteness` with `hnorm` discharged from the §6.2 residual**
(`rischDEInnerCompleteness_of_norm_bound_solve`): given the §6.2 divisibility residual
`RdeNormalDivisibilityResidual` (which produces `hnorm` via `hnorm_of_divisibilityResidual`) together with
the `hbound` and `hsolve` clauses, `RischDEInnerCompleteness Dt fnum fden gnum gden` holds. This is the
assembly point: `hnorm` is **no longer** a residual input — it is produced from the §6.2 divisibility
residual through the fully-proven engine bridge. `RischDEInnerCompleteness` now reduces to exactly `hbound`
(nearly done, `ComputableRischDEDegreeBound`) + `hsolve` (the deep §6.4–6.6 core) + the deep §6.2
divisibility (Bronstein Thm 6.1.2). -/
theorem rischDEInnerCompleteness_of_norm_bound_solve (Dt fnum fden gnum gden : CPolyG α)
    (hnormRes : RdeNormalDivisibilityResidual Dt fnum fden gnum gden)
    (hbound : ∀ a0 b0 c0 h0 : CPolyG α,
      cRdeNormalDenominatorG Dt towerRischDEFuel fnum fden gnum gden = some (a0, b0, c0, h0) →
      ∀ q : CPolyG α,
        IsReducedRdeSol Dt (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).1
            (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.1
            (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.2.1 q →
        cdegG q ≤ cRdeBoundDegreeG Dt
          (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).1
          (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.1
          (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.2.1)
    (hsolve : (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
      (cRischDEG Dt towerRischDEFuel fnum fden gnum gden).isSome = true) :
    RischDEInnerCompleteness Dt fnum fden gnum gden where
  hnorm := hnorm_of_divisibilityResidual Dt fnum fden gnum gden hnormRes
  hbound := hbound
  hsolve := hsolve

end Assemble

/-! ### Restatement against `RischDEInnerCompleteness.hnorm`'s field type (anonymous `example`) -/

-- ★ The produced `hnorm` has exactly `RischDEInnerCompleteness.hnorm`'s type — confirmed by using it as
-- that field in a partial structure check together with abstract `hbound`/`hsolve`.
example {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCore α]
    [CRischField α] (Dt fnum fden gnum gden : CPolyG α)
    (hres : RdeNormalDivisibilityResidual Dt fnum fden gnum gden) :
    (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
      (cRdeNormalDenominatorG Dt towerRischDEFuel fnum fden gnum gden).isSome = true :=
  hnorm_of_divisibilityResidual Dt fnum fden gnum gden hres

/-! ### Final verdict (stated precisely)

**Is `hnorm` discharged?** **YES — modulo a single, precisely isolated deep divisibility (Bronstein Thm
6.1.2).** `hnorm_of_divisibilityResidual` produces the **exact** `hnorm` clause of
`RischDEInnerCompleteness` from `RdeNormalDivisibilityResidual` (confirmed by the field-type `example`).
The §6.2 transformation loses a solution **only** through its one `cdvdG` divisibility gate, and `hnorm` is
that gate's completeness.

**What is closed unconditionally (the fully-proven engine layer; NO `native_decide`/`sorry`):**
* `cRdeNormalDenominatorG_isSome_iff` — the §6.2 step's `isSome` is *exactly* its `cdvdG` guard `eₙ ∣ dₙh²`
  (definitional control-flow reading);
* `cdvdG_of_dvd` — the **converse of `dvd_of_cdvdG`**: mathematical `toPolyG q ∣ toPolyG p` (+ `q ≠ 0`,
  fuel) forces the engine check `cdvdG = true`, via the §6.2 Euclidean division identity and the
  unique-remainder property — so the §6.2 guard is honest in **both** directions;
* `cRdeNormalDenominatorG_isSome_of_dvd` — composing them: the *mathematical* §6.2 divisibility `eₙ ∣ dₙh²`
  makes the §6.2 step return `some`, collapsing `hnorm` to that single divisibility.

**The single deep residual** (`RdeNormalDivisibilityResidual`, NEVER `sorry`): `hdvd` — a polynomial
solution forces `eₙ ∣ dₙh²` (**Bronstein Thm 6.1.2**, the valuation-theoretic necessity at the normal
poles), plus two **benign** engine side-conditions (`hen0`: `eₙ ≠ 0`, free for weakly-normalized
`gden ≠ 0`; `hfuel`: per-run fuel bound). The deep `hdvd` is the one genuinely irreducible piece — it is
*not* derivable from the cleared identity `IsCRischDEGPolySol` by elementary algebra (the identity lives in
the polynomial ring, the divisibility is about the denominator's normal-pole structure).

**`hdvd` is reachable in the structural cases, and the deep case has a concrete Mathlib route.**
`dvd_dnh2_of_en_dvd_dn` / `hdvd_free_of_en_dvd_dn` discharge `hdvd` **unconditionally** when `eₙ ∣ dₙ` (so
it is non-vacuous, not a hidden `sorry`). The full deep case (arbitrary normal poles) reduces to the
per-pole order-drop `Polynomial.derivative_rootMultiplicity_of_root_of_mem_nonZeroDivisors` (Mathlib has
it) lifted through `cValuationG` over the tower — a complete Thm 6.1.2 development, the actionable
frontier for closing `hdvd` outright.

**What `RischDEInnerCompleteness` now reduces to.** With `hnorm` produced here
(`rischDEInnerCompleteness_of_norm_bound_solve`), `RischDEInnerCompleteness` reduces to: `hbound` (nearly
done — `ComputableRischDEDegreeBound` produces it modulo a cancellation residual) + `hsolve` (the deep
§6.4–6.6 SPDE/poly-RDE exhaustiveness) + the deep §6.2 divisibility (Bronstein Thm 6.1.2,
`RdeNormalDivisibilityResidual.hdvd`). The §6.2 normal-denominator completeness clause is discharged down
to its single valuation-theoretic keystone, through a fully proven engine layer. -/

/-! ### Axiom audit (the engine layer + the modular assembly are axiom-clean; NO `native_decide`,
NO `sorry`) -/

#print axioms cRdeNormalDenominatorG_isSome_iff
#print axioms cdvdG_of_dvd
#print axioms cRdeNormalDenominatorG_isSome_of_dvd
#print axioms hnorm_of_divisibilityResidual
#print axioms rischDEInnerCompleteness_of_norm_bound_solve

end DeepWiki.SymbolicIntegration
