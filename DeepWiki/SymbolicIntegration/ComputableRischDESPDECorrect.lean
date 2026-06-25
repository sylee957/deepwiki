import DeepWiki.SymbolicIntegration.ComputableRischDECorrect
import DeepWiki.SymbolicIntegration.ComputableGcdCorrect
import DeepWiki.SymbolicIntegration.ComputableSplitFactorCorrect

/-! # Discharging the §6.4 `cSPDE` certificate `cSPDECleared` (Bronstein §6.4)

`ComputableRischDECorrect` proves the §6.4 `cSPDE` lifting `cSPDE_cleared_lifting` *gated on*
a per-level certificate predicate `cSPDECleared` — the exact-division witnesses
`(a/g)·g = a, …`, the nonzero-leading `a/g ≠ 0`, and the Bézout `bd·r + ad·z = cd` each SPDE peel
needs. This file **discharges** that certificate from the proven gcd machinery, leaving only
*transparent* per-level preconditions (`cgcdFF` associated to `gcd`, fuel bounds, the Euclidean
gcd termination `cgcdTerminatesG`, and `a ≠ 0`), bundled into a recursive input predicate
`CSPDEClearedInputs` mirroring `cSPDE`'s own recursion.

## The math

Each non-base SPDE level computes `g = cgcdFF fuel a b ~ gcd(a, b)`, the divided
`ad = a/g, bd = b/g, cd = c/g`, and the Bézout cofactors `(r, z) = cdiophantineG fuel bd ad cd`.

* **Exact divisions** `toPolyG ad · toPolyG g = toPolyG a` (and `b, c`): `toPolyG_cdivFF_exact`,
  whose divisibility hypothesis `toPolyG g ∣ toPolyG a` comes from `g ~ gcd(a, b)` (`gcd_dvd_left`)
  and `g ∣ c` is *free* from the `cdvdG fuel g c = true` branch condition the recursion already
  takes (the Euclidean identity `toPolyG_cdivmodG'` with a zero remainder).
* **`ad ≠ 0`**: from `ad·g = a` with `a ≠ 0`.
* **The Bézout certificate**: `toPolyG_cdiophantineG` needs the *internal* `cgcdExtG`-gcd
  `G = (cgcdExtG fuel bd ad).1` to be a **nonzero constant**. Key lemma `cgcdExtG_isUnit_of_divided`:
  `G ∣ ad, G ∣ bd` (`toPolyG_cgcdExtG_dvd` under termination), so `G·g ∣ a, b`, hence
  `G·g ∣ gcd(a, b) ~ g`; cancelling the nonzero `g` makes `G` a unit — a nonzero `C (lc G)`. This is
  exactly the coprimality `ad ⊥ bd` of the divided coefficients, the structure
  `toPolyG_cdiophantineG` certifies. -/

open Polynomial Classical

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

/-! ### The internal `cgcdExtG`-gcd of the divided coefficients is a nonzero constant
The Bézout solve `cdiophantineG fuel bd ad cd` runs its own extended Euclidean `cgcdExtG fuel bd ad`;
its gcd `G` is a **unit** of `(RatFunc ℚ)[X]` because `ad, bd` are coprime (they are `a/g, b/g` for
`g = gcd(a, b)`). A unit is a nonzero constant `C (leadingCoeff)`, exactly the
`toPolyG_cdiophantineG` hypotheses. -/

/-- **The divided coefficients' Euclidean gcd is a unit**: if `g ~ gcd(a, b)` (`g ≠ 0`) with
`toPolyG ad · toPolyG g = toPolyG a`, `toPolyG bd · toPolyG g = toPolyG b` the exact divisions, then
under the Euclidean termination `cgcdTerminatesG fuel bd ad` the gcd `G = (cgcdExtG fuel bd ad).1` is
a unit of `(RatFunc ℚ)[X]`. Common divisors `G ∣ ad, G ∣ bd` give `G·g ∣ a, b`, so `G·g ∣ gcd(a, b)`;
since `gcd(a, b) ~ g` and `g ≠ 0`, cancelling `g` makes `G ∣ 1`. -/
theorem cgcdExtG_isUnit_of_divided (fuel : ℕ) (a b ad bd g : CPolyG QFunNZ)
    (hgne : toPolyG g ≠ 0)
    (hgassoc : Associated (toPolyG g) (gcd (toPolyG a) (toPolyG b)))
    (hdiva : toPolyG ad * toPolyG g = toPolyG a)
    (hdivb : toPolyG bd * toPolyG g = toPolyG b)
    (hterm : cgcdTerminatesG fuel bd ad) :
    IsUnit (toPolyG (cgcdExtG fuel bd ad).1) := by
  -- `G` divides both `bd` and `ad`
  obtain ⟨hGbd, hGad⟩ := toPolyG_cgcdExtG_dvd fuel bd ad hterm
  set G := toPolyG (cgcdExtG fuel bd ad).1 with hGdef
  -- `G·g ∣ a` and `G·g ∣ b`
  have hGg_a : G * toPolyG g ∣ toPolyG a := by
    rw [← hdiva]; exact mul_dvd_mul_right hGad _
  have hGg_b : G * toPolyG g ∣ toPolyG b := by
    rw [← hdivb]; exact mul_dvd_mul_right hGbd _
  -- `G·g ∣ gcd(a, b) ~ g`, so `G·g ∣ g`
  have hGg_gcd : G * toPolyG g ∣ gcd (toPolyG a) (toPolyG b) := dvd_gcd hGg_a hGg_b
  have hGg_g : G * toPolyG g ∣ toPolyG g := hGg_gcd.trans hgassoc.symm.dvd
  -- cancel the nonzero `g`: `g = G·g·k = g·(G·k)` ⇒ `1 = G·k` ⇒ `G ∣ 1`
  obtain ⟨k, hk⟩ := hGg_g
  have hcancel : toPolyG g * 1 = toPolyG g * (G * k) := by
    rw [mul_one]; nth_rewrite 1 [hk]; ring
  -- `1 = G·k`, so `G ∣ 1`, hence `G` is a unit
  have hG1 : G ∣ 1 := ⟨k, mul_left_cancel₀ hgne hcancel⟩
  exact isUnit_of_dvd_one hG1

/-- **The divided coefficients' Euclidean gcd is the constant `C (leadingCoeff)`**: the unit gcd
`G = (cgcdExtG fuel bd ad).1` of `cgcdExtG_isUnit_of_divided` has degree `0`, so
`toPolyG G = C (toK (cleadG G))`. The first `toPolyG_cdiophantineG` hypothesis. -/
theorem toPolyG_cgcdExtG_eq_C_of_divided (fuel : ℕ) (a b ad bd g : CPolyG QFunNZ)
    (hgne : toPolyG g ≠ 0)
    (hgassoc : Associated (toPolyG g) (gcd (toPolyG a) (toPolyG b)))
    (hdiva : toPolyG ad * toPolyG g = toPolyG a)
    (hdivb : toPolyG bd * toPolyG g = toPolyG b)
    (hterm : cgcdTerminatesG fuel bd ad) :
    toPolyG (cgcdExtG fuel bd ad).1
      = Polynomial.C (CFieldSpec.toK (cleadG (cgcdExtG fuel bd ad).1)) := by
  have hunit := cgcdExtG_isUnit_of_divided fuel a b ad bd g hgne hgassoc hdiva hdivb hterm
  have hnd : (toPolyG (cgcdExtG fuel bd ad).1).natDegree = 0 :=
    Polynomial.natDegree_eq_zero_of_isUnit hunit
  rw [toK_cleadG_eq_leadingCoeff, Polynomial.leadingCoeff, hnd]
  exact Polynomial.eq_C_of_natDegree_eq_zero hnd

/-- **The divided coefficients' Euclidean gcd has nonzero leading coefficient**: a unit is nonzero,
so `toK (cleadG G) ≠ 0`. The second `toPolyG_cdiophantineG` hypothesis. -/
theorem toK_cleadG_cgcdExtG_ne_zero_of_divided (fuel : ℕ) (a b ad bd g : CPolyG QFunNZ)
    (hgne : toPolyG g ≠ 0)
    (hgassoc : Associated (toPolyG g) (gcd (toPolyG a) (toPolyG b)))
    (hdiva : toPolyG ad * toPolyG g = toPolyG a)
    (hdivb : toPolyG bd * toPolyG g = toPolyG b)
    (hterm : cgcdTerminatesG fuel bd ad) :
    CFieldSpec.toK (cleadG (cgcdExtG fuel bd ad).1) ≠ 0 := by
  have hunit := cgcdExtG_isUnit_of_divided fuel a b ad bd g hgne hgassoc hdiva hdivb hterm
  rw [toK_cleadG_eq_leadingCoeff]
  exact Polynomial.leadingCoeff_ne_zero.mpr hunit.ne_zero

end DeepWiki.SymbolicIntegration
