import DeepWiki.SymbolicIntegration.ComputableSplitFactorCorrect
import DeepWiki.SymbolicIntegration.ComputableGenericBezout

/-! # Generic Bézout-split / canonical-field-identity helpers for §3.5 correctness
Abstract correctness of `cSplitSquarefreeFactorFast` and the `canonicalRepresentationFast` capstone over
a tower level is the generic tower-recursive `canonicalRepresentationFastG_reconstructs`
(`ComputableTowerUnify`) at `QFunNZG ℚ`. This file holds three reusable generic helpers consumed by that
generic engine: `toPolyG_cbezoutOne` (`u·a + w·b = 1` from the extended-Euclid Bézout),
`toPolyG_cextendedEuclideanSplit` (`b·dₙ + c·dₛ = r`), and the field-arithmetic
`canonicalRepFast_field_identity` (`q + b/dₛ + c/dₙ = a/d`). -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

variable {α : Type*} [CField α] [CFieldSpec α]

/-- **`cbezoutOne` solves the Bézout identity** `u·a + w·b = 1` over `K[X]`: with `(g, s, t) = cgcdExtG
fuel a b` and `g` a nonzero **constant** (`natDegree (toPolyG g) = 0`, `toPolyG g ≠ 0` — the coprime
case), the rescaled cofactors `(u, w) = cbezoutOne fuel a b` (each scaled by `(lead g)⁻¹`) satisfy
`toPolyG u · toPolyG a + toPolyG w · toPolyG b = 1`. From the raw Bézout `toPolyG_cgcdExtG` divided by
the constant `g`. -/
theorem toPolyG_cbezoutOne (fuel : ℕ) (a b : CPolyG α)
    (hgdeg : (toPolyG (cgcdExtG fuel a b).1).natDegree = 0)
    (hgne : toPolyG (cgcdExtG fuel a b).1 ≠ 0) :
    toPolyG (CPolyG.cbezoutOne fuel a b).1 * toPolyG a
        + toPolyG (CPolyG.cbezoutOne fuel a b).2 * toPolyG b = 1 := by
  set g := (cgcdExtG fuel a b).1 with hg
  set s := (cgcdExtG fuel a b).2.1 with hs
  set t := (cgcdExtG fuel a b).2.2 with ht
  -- the raw Bézout identity from `cgcdExtG`.
  have hbez : toPolyG s * toPolyG a + toPolyG t * toPolyG b = toPolyG g :=
    toPolyG_cgcdExtG fuel a b
  -- freeze the leading coefficient `c = lead g`, a nonzero scalar.
  set c := (toPolyG g).leadingCoeff with hc
  have hlead_ne : c ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hgne
  -- `toPolyG g = C c`, a nonzero constant.
  have hgC : toPolyG g = Polynomial.C c := by
    conv_lhs => rw [Polynomial.eq_C_of_natDegree_eq_zero hgdeg]
    rw [hc, Polynomial.leadingCoeff, hgdeg]
  -- `cbezoutOne` rescales `(s, t)` by `(toK (cleadG g))⁻¹ = c⁻¹`.
  have hu : toPolyG (CPolyG.cbezoutOne fuel a b).1 = Polynomial.C c⁻¹ * toPolyG s := by
    rw [CPolyG.cbezoutOne]
    show toPolyG (cscaleG (CField.inv (cleadG g)) s) = _
    rw [toPolyG_cscaleG, CFieldSpec.toK_inv, toK_cleadG_eq_leadingCoeff, ← hc]
  have hw : toPolyG (CPolyG.cbezoutOne fuel a b).2 = Polynomial.C c⁻¹ * toPolyG t := by
    rw [CPolyG.cbezoutOne]
    show toPolyG (cscaleG (CField.inv (cleadG g)) t) = _
    rw [toPolyG_cscaleG, CFieldSpec.toK_inv, toK_cleadG_eq_leadingCoeff, ← hc]
  rw [hu, hw]
  -- `C(c⁻¹)·s·a + C(c⁻¹)·t·b = C(c⁻¹)·(s·a + t·b) = C(c⁻¹)·C(c) = 1`.
  have hcombine : Polynomial.C c⁻¹ * toPolyG s * toPolyG a
      + Polynomial.C c⁻¹ * toPolyG t * toPolyG b = Polynomial.C c⁻¹ * toPolyG g := by
    rw [← hbez]; ring
  rw [hcombine, hgC, ← Polynomial.C_mul, inv_mul_cancel₀ hlead_ne, Polynomial.C_1]

/-- **`cextendedEuclideanSplit` solves `b·dₙ + c·dₛ = r`** over `K[X]`: with a Bézout pair `u·dₙ + w·dₛ
= 1` (read through `toPolyG`), `cextendedEuclideanSplit fuel dn ds r u w = (b, c)` gives `toPolyG b ·
toPolyG dn + toPolyG c · toPolyG ds = toPolyG r`. Mirrors `extendedEuclideanSplit_spec`. Requires `dₛ`
nonzero (`cnormG ds ≠ []`). -/
theorem toPolyG_cextendedEuclideanSplit (fuel : ℕ) (dn ds r u w : CPolyG α)
    (hds0 : cnormG ds ≠ [])
    (hbez : toPolyG u * toPolyG dn + toPolyG w * toPolyG ds = 1) :
    toPolyG (CPolyG.cextendedEuclideanSplit fuel dn ds r u w).1 * toPolyG dn
        + toPolyG (CPolyG.cextendedEuclideanSplit fuel dn ds r u w).2 * toPolyG ds
      = toPolyG r := by
  -- `b = (u·r) mod ds`, `c = w·r + (u·r div ds)·dn`.
  set ur := cmulG u r with hur
  -- Euclidean identity `u·r = (u·r div ds)·ds + (u·r mod ds)`.
  have hdivmod : toPolyG ur
      = toPolyG (cdivG fuel ur ds) * toPolyG ds + toPolyG (cmodG fuel ur ds) :=
    toPolyG_cdivmodG' fuel ur ds hds0
  -- the components of `cextendedEuclideanSplit`.
  have hb : (CPolyG.cextendedEuclideanSplit fuel dn ds r u w).1 = cmodG fuel ur ds := by
    rw [CPolyG.cextendedEuclideanSplit]; simp only [cmodG, hur]
  have hc : (CPolyG.cextendedEuclideanSplit fuel dn ds r u w).2
      = caddG (cmulG w r) (cmulG (cdivG fuel ur ds) dn) := by
    rw [CPolyG.cextendedEuclideanSplit]; simp only [cdivG, hur]
  rw [hb, hc, toPolyG_caddG, toPolyG_cmulG, toPolyG_cmulG]
  -- substitute the Euclidean remainder `(u·r mod ds) = u·r − (u·r div ds)·ds`.
  have hrem : toPolyG (cmodG fuel ur ds)
      = toPolyG ur - toPolyG (cdivG fuel ur ds) * toPolyG ds := by
    rw [hdivmod]; ring
  rw [hrem, hur, toPolyG_cmulG]
  -- `(u·r − Q·ds)·dn + (w·r + Q·dn)·ds = (u·dn + w·ds)·r = r`.
  have hkey : (toPolyG u * toPolyG r - toPolyG (cdivG fuel (cmulG u r) ds) * toPolyG ds) * toPolyG dn
      + (toPolyG w * toPolyG r + toPolyG (cdivG fuel (cmulG u r) ds) * toPolyG dn) * toPolyG ds
      = (toPolyG u * toPolyG dn + toPolyG w * toPolyG ds) * toPolyG r := by ring
  rw [show cmulG u r = ur from rfl] at hkey ⊢
  rw [hkey, hbez, one_mul]

/-- **`cextendedEuclideanSplit`'s first cofactor is proper** — `deg b < deg dₛ`: the first cofactor `b =
(u·r) mod dₛ` is a Euclidean remainder mod `dₛ` (`cmodG_length_lt` bounds its normalized length below
`dₛ`'s, `toPolyG_degree_lt_of_length_lt` turns that into the `degree` bound). Needs `dₛ` nonzero (`cnormG ds
≠ []`) and enough fuel for `u·r`. Mirrors `extendedEuclideanSplit_degree_lt`. -/
theorem cextendedEuclideanSplit_fst_degree_lt (fuel : ℕ) (dn ds r u w : CPolyG α)
    (hds : cnormG ds ≠ [])
    (hfuel : (cnormG (cmulG u r) : List α).length ≤ fuel) :
    (toPolyG (CPolyG.cextendedEuclideanSplit fuel dn ds r u w).1).degree < (toPolyG ds).degree := by
  have hfst : (CPolyG.cextendedEuclideanSplit fuel dn ds r u w).1
      = cmodG fuel (cmulG u r) ds := by rw [CPolyG.cextendedEuclideanSplit]; rfl
  rw [hfst]
  refine toPolyG_degree_lt_of_length_lt _ _ hds ?_
  show (cnormG (cmodG fuel (cmulG u r) ds) : List α).length < _
  exact cmodG_length_lt fuel _ ds hds hfuel

/-- **★ `cextendedEuclideanSplit`'s second cofactor is proper** — `deg c < deg dₙ`: from the Bézout split
`b·dₙ + c·dₛ = r` (`toPolyG_cextendedEuclideanSplit`), the first cofactor `deg b < deg dₛ`
(`cextendedEuclideanSplit_fst_degree_lt`), the denominator split `d = dₛ·dₙ`, and `deg r < deg d`. Then
`c·dₛ = r − b·dₙ` has `deg(c·dₛ) < deg d = deg dₛ + deg dₙ` (both `deg r` and `deg(b·dₙ) = deg b + deg dₙ`
are below `deg d`), so `deg c < deg dₙ` cancelling `deg dₛ`. This is the simple-fraction properness the
canonical representation's simple part `c/dₙ` needs — the second-cofactor analogue of
`cdiophantineG_fst_degree_lt`, given the split as a hypothesis. -/
theorem cextendedEuclideanSplit_snd_degree_lt (fuel : ℕ) (dn ds r u w d : CPolyG α)
    (hds : cnormG ds ≠ []) (hdn : cnormG dn ≠ [])
    (hsplit : toPolyG d = toPolyG ds * toPolyG dn)
    (hfuel : (cnormG (cmulG u r) : List α).length ≤ fuel)
    (hbez : toPolyG u * toPolyG dn + toPolyG w * toPolyG ds = 1)
    (hr : (toPolyG r).degree < (toPolyG d).degree) :
    (toPolyG (CPolyG.cextendedEuclideanSplit fuel dn ds r u w).2).degree < (toPolyG dn).degree := by
  set b := toPolyG (CPolyG.cextendedEuclideanSplit fuel dn ds r u w).1 with hbdef
  set c := toPolyG (CPolyG.cextendedEuclideanSplit fuel dn ds r u w).2 with hcdef
  have hds0 : toPolyG ds ≠ 0 := fun h => hds ((cnormG_eq_nil_iff ds).mpr h)
  have hdn0 : toPolyG dn ≠ 0 := fun h => hdn ((cnormG_eq_nil_iff dn).mpr h)
  have hspec : b * toPolyG dn + c * toPolyG ds = toPolyG r :=
    toPolyG_cextendedEuclideanSplit fuel dn ds r u w hds hbez
  have hbdeg : b.degree < (toPolyG ds).degree :=
    cextendedEuclideanSplit_fst_degree_lt fuel dn ds r u w hds hfuel
  -- `deg(b·dₙ) < deg(dₛ·dₙ) = deg d`
  have hbdn : (b * toPolyG dn).degree < (toPolyG d).degree := by
    rw [hsplit, Polynomial.degree_mul, Polynomial.degree_mul]
    exact WithBot.add_lt_add_right (by rwa [Ne, Polynomial.degree_eq_bot]) hbdeg
  -- `c·dₛ = r − b·dₙ`, so `deg(c·dₛ) < deg d`
  have hcds : c * toPolyG ds = toPolyG r - b * toPolyG dn := by linear_combination hspec
  have hcdsdeg : (c * toPolyG ds).degree < (toPolyG d).degree := by
    rw [hcds]
    calc (toPolyG r - b * toPolyG dn).degree
        ≤ max (toPolyG r).degree (b * toPolyG dn).degree := Polynomial.degree_sub_le _ _
      _ < (toPolyG d).degree := max_lt hr hbdn
  -- cancel `deg dₛ`: `deg c < deg dₙ`
  rw [Polynomial.degree_mul, hsplit, Polynomial.degree_mul] at hcdsdeg
  have hdsdeg : (toPolyG ds).degree ≠ ⊥ := by rwa [Ne, Polynomial.degree_eq_bot]
  rw [add_comm (toPolyG ds).degree (toPolyG dn).degree] at hcdsdeg
  exact (WithBot.add_lt_add_iff_right hdsdeg).mp hcdsdeg

/-- **The abstract canonical field identity** over ℚ(x)(t): from the division `a = q·d + r`, the
denominator split `d = dₛ·dₙ`, and the Bézout split `b·dₙ + c·dₛ = r`, the three pieces recombine to
`a/d` — `q + b/dₛ + c/dₙ = a/d`. The field-arithmetic core, independent of the computable engine. -/
theorem canonicalRepFast_field_identity {K : Type*} [Field K] (a d q r dn ds b c : K[X])
    (hd : d ≠ 0) (hdn : dn ≠ 0) (hds : ds ≠ 0)
    (hadiv : a = q * d + r) (hsplit : d = ds * dn) (hbcr : b * dn + c * ds = r) :
    (algebraMap K[X] (RatFunc K) q)
        + algebraMap K[X] (RatFunc K) b / algebraMap K[X] (RatFunc K) ds
        + algebraMap K[X] (RatFunc K) c / algebraMap K[X] (RatFunc K) dn
      = algebraMap K[X] (RatFunc K) a / algebraMap K[X] (RatFunc K) d := by
  set A := algebraMap K[X] (RatFunc K) with hA
  have hAd : A d ≠ 0 := RatFunc.algebraMap_ne_zero hd
  have hAdn : A dn ≠ 0 := RatFunc.algebraMap_ne_zero hdn
  have hAds : A ds ≠ 0 := RatFunc.algebraMap_ne_zero hds
  have hAa : A a = A q * (A ds * A dn) + (A b * A dn + A c * A ds) := by
    rw [hadiv, hsplit, ← hbcr]; push_cast [hA]; ring
  rw [show A d = A ds * A dn by rw [hsplit, map_mul]]
  rw [eq_div_iff (mul_ne_zero hAds hAdn), hAa]
  field_simp
  ring

end DeepWiki.SymbolicIntegration
