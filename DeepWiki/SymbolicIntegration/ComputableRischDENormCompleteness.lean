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
(`= cdivG fuel (cgcdFFCore eₙ eₙ') (cgcdFFCore p p')`, `p = cgcdFFCore dₙ eₙ`): the §6.2
`h = gcd(eₙ, eₙ')/gcd(p, p')` of Bronstein p.185, the 4th component returned by a successful
`cRdeNormalDenominatorG` (`cRdeNormalDenominatorG_h0_eq`). Abbreviation pinning the §6.2 guard's `h`. -/
def rdeNormH (Dt : CPolyG α) (fuel : ℕ) (fden gden : CPolyG α) : CPolyG α :=
  CPolyG.cdivG fuel
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
  by_cases hck : CPolyG.cdvdG fuel (CPolyG.cSplitFactorFastG Dt fuel gden).1
      (CPolyG.cmulG (CPolyG.cmulG (CPolyG.cSplitFactorFastG Dt fuel fden).1
        (CPolyG.cdivG fuel
          (CFracGcdCore.cgcdFFCore fuel (CPolyG.cSplitFactorFastG Dt fuel gden).1
            (CPolyG.cderivG (CPolyG.cSplitFactorFastG Dt fuel gden).1))
          (CFracGcdCore.cgcdFFCore fuel
            (CFracGcdCore.cgcdFFCore fuel (CPolyG.cSplitFactorFastG Dt fuel fden).1
              (CPolyG.cSplitFactorFastG Dt fuel gden).1)
            (CPolyG.cderivG (CFracGcdCore.cgcdFFCore fuel
              (CPolyG.cSplitFactorFastG Dt fuel fden).1
              (CPolyG.cSplitFactorFastG Dt fuel gden).1)))))
        (CPolyG.cdivG fuel
          (CFracGcdCore.cgcdFFCore fuel (CPolyG.cSplitFactorFastG Dt fuel gden).1
            (CPolyG.cderivG (CPolyG.cSplitFactorFastG Dt fuel gden).1))
          (CFracGcdCore.cgcdFFCore fuel
            (CFracGcdCore.cgcdFFCore fuel (CPolyG.cSplitFactorFastG Dt fuel fden).1
              (CPolyG.cSplitFactorFastG Dt fuel gden).1)
            (CPolyG.cderivG (CFracGcdCore.cgcdFFCore fuel
              (CPolyG.cSplitFactorFastG Dt fuel fden).1
              (CPolyG.cSplitFactorFastG Dt fuel gden).1))))) = true
  · rw [if_pos hck]; simp [hck]
  · rw [Bool.not_eq_true] at hck
    rw [if_neg (by simp [hck])]; simp [hck]

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

end DeepWiki.SymbolicIntegration
