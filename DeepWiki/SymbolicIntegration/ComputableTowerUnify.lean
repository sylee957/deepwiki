import DeepWiki.SymbolicIntegration.ComputableTowerIntegrate
import DeepWiki.SymbolicIntegration.Computable.CanonicalRepCorrect

/-! # The `canonicalRepresentationFastG` reconstruction probe

Foundation lemmas for the generic tower engine's abstract correctness, over `[CField α] [CFieldSpec α]`:

1. **The reconstruction probe** `canonicalRepresentationFastG_reconstructs`: the §3.5 capstone's
   reconstruction `toPolyG d = toPolyG dₛ·dₙ ⇒ …`, modulo the denominator split (the abstract
   correctness of that split is filled at `α = QFunNZG ℚ` in `ComputableSplitFactorTowerCorrectG`). -/

open Polynomial Classical

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

/-! ### The generic §3.5 reconstruction `canonicalRepresentationFastG_reconstructs`

The §3.5 capstone correctness, generic over `[CField α] [CFieldSpec α]`: the canonical-representation
split `canonicalRepresentationFastG Dt fuel a d = (q, (b, dₛ), (c, dₙ))` recombines to `f = a/d`, i.e.
`q + b/dₛ + c/dₙ = a/d` in `RatFunc (CFieldSpec.K α)`.

**Structure of the proof.** The reconstruction decomposes as (1) the denominator split
`toPolyG d = toPolyG dₛ · toPolyG dₙ`, (2) the Euclidean division, (3) the Bézout cofactors, (4) the
Bézout split, assembled by the field identity. Steps **(2), (3), (4), and the assembly use only generic
lemmas** — `toPolyG_cdivmodWf`, `toPolyG_cbezoutOneWf`, `toPolyG_cextendedEuclideanSplitWf` (all stated over
`[CField α] [CFieldSpec α]`), and `canonicalRepFast_field_identity` (over any `[Field K]`). The only
remaining ingredient is the split fact (1), which `cSplitFactorFastG` does not yet prove abstractly (only
a fuel-free `native_decide` validator `towerCanRepLvl2_recombinesWf`).

So we state the generic reconstruction **modulo** the split fact (taking `toPolyG d = toPolyG dₛ·dₙ` as a
hypothesis), and the rest of the proof is entirely generic. The one ingredient a fully abstract collapse
still needs: an abstract correctness lemma for `cSplitFactorFastG`. -/

variable {α : Type*}

open RatFunc in
/-- **★ `canonicalRepresentationFastG` reconstructs `f`, generic over `[CField α]
[CDiffField α] [CFieldSpec α]`**, modulo the denominator split. With the generic output
`(q, (b, dₛ), (c, dₙ)) = canonicalRepresentationFastG Dt fuel a d`, *given* the split factorization
`toPolyG d = toPolyG dₛ · toPolyG dₙ` (the one ingredient `cSplitFactorFastG` does not yet prove
abstractly), the Bézout-gcd-constant witness, and `d ≠ 0` with enough fuel, the three pieces recombine
to `f = a/d` in `RatFunc (CFieldSpec.K α)`. Every helper (`toPolyG_cdivmodWf`, `toPolyG_cbezoutOneWf`,
`toPolyG_cextendedEuclideanSplitWf`, `canonicalRepFast_field_identity`) is already generic, so once the
denominator split is supplied the reconstruction is entirely generic. -/
theorem canonicalRepresentationFastG_reconstructs [CField α] [CDiffField α] [CFracGcdCore α]
    [CFieldSpec α] (Dt : CPolyG α) (fuel : ℕ) (a d : CPolyG α)
    (hd : toPolyG d ≠ 0)
    (hsplit_eq : toPolyG (cSplitFactorFastG Dt fuel d).2 ≠ 0 →
      toPolyG (cSplitFactorFastG Dt fuel d).1 ≠ 0 →
      toPolyG d = toPolyG (cSplitFactorFastG Dt fuel d).2 * toPolyG (cSplitFactorFastG Dt fuel d).1)
    (hsplit_dn_ne : toPolyG (cSplitFactorFastG Dt fuel d).1 ≠ 0)
    (hsplit_ds_ne : toPolyG (cSplitFactorFastG Dt fuel d).2 ≠ 0)
    (hgdeg : (toPolyG (cgcdWf (cSplitFactorFastG Dt fuel d).1
      (cSplitFactorFastG Dt fuel d).2).1).natDegree = 0)
    (hgne : toPolyG (cgcdWf (cSplitFactorFastG Dt fuel d).1
      (cSplitFactorFastG Dt fuel d).2).1 ≠ 0) :
    (let res := CPolyG.canonicalRepresentationFastG Dt fuel a d
      let q := res.1
      let b := res.2.1.1
      let ds := res.2.1.2
      let c := res.2.2.1
      let dn := res.2.2.2
      (algebraMap (CFieldSpec.K α)[X] (RatFunc (CFieldSpec.K α)) (toPolyG q))
          + algebraMap (CFieldSpec.K α)[X] (RatFunc (CFieldSpec.K α)) (toPolyG b)
              / algebraMap (CFieldSpec.K α)[X] (RatFunc (CFieldSpec.K α)) (toPolyG ds)
          + algebraMap (CFieldSpec.K α)[X] (RatFunc (CFieldSpec.K α)) (toPolyG c)
              / algebraMap (CFieldSpec.K α)[X] (RatFunc (CFieldSpec.K α)) (toPolyG dn)
        = algebraMap (CFieldSpec.K α)[X] (RatFunc (CFieldSpec.K α)) (toPolyG a)
            / algebraMap (CFieldSpec.K α)[X] (RatFunc (CFieldSpec.K α)) (toPolyG d)) := by
  -- names matching the `let`-bindings of `canonicalRepresentationFastG` (the generic def, identical
  -- shape to `canonicalRepresentationFast` modulo `cSplitFactorFastG`).
  set qr := cdivmodWf a d with hqr
  set dnds := cSplitFactorFastG Dt fuel d with hdnds
  set dn := dnds.1 with hdn
  set ds := dnds.2 with hds
  set q := qr.1 with hq
  set r := qr.2 with hr
  set uw := CPolyG.cbezoutOneWf dn ds with huw
  set u := uw.1 with hu
  set w := uw.2 with hw
  set bc := CPolyG.cextendedEuclideanSplitWf dn ds r u w with hbc
  set b := bc.1 with hb
  set c := bc.2 with hc
  -- 1. the denominator split `toPolyG d = toPolyG ds · toPolyG dn` (the HYPOTHESIS standing in for the
  --    missing generic `cSplitFactorFastG` correctness).
  have hsplit_eq' : toPolyG d = toPolyG ds * toPolyG dn := hsplit_eq hsplit_ds_ne hsplit_dn_ne
  -- 2. the Euclidean division `toPolyG a = toPolyG q · toPolyG d + toPolyG r` (generic).
  have hdcn : cnormG d ≠ [] := fun h => hd ((cnormG_eq_nil_iff d).mp h)
  have hadiv : toPolyG a = toPolyG q * toPolyG d + toPolyG r := by
    have h := toPolyG_cdivmodWf a d hdcn
    rw [← hqr, ← hq, ← hr] at h
    exact h
  -- 3. the Bézout cofactors `u·dn + w·ds = 1` (generic).
  have hbez : toPolyG u * toPolyG dn + toPolyG w * toPolyG ds = 1 := by
    have := toPolyG_cbezoutOneWf dn ds hgdeg hgne
    rw [← hu, ← hw] at this; exact this
  -- 4. the Bézout split `b·dn + c·ds = r` (generic).
  have hds0 : cnormG ds ≠ [] := fun h => hsplit_ds_ne ((cnormG_eq_nil_iff ds).mp h)
  have hbcr : toPolyG b * toPolyG dn + toPolyG c * toPolyG ds = toPolyG r := by
    have := toPolyG_cextendedEuclideanSplitWf dn ds r u w hds0 hbez
    rw [← hb, ← hc] at this; exact this
  -- assemble the field identity (generic over any `[Field K]`).
  simpa [CPolyG.canonicalRepresentationFastG, ← hqr, ← hdnds, ← hdn, ← hds, ← hq, ← hr,
    ← huw, ← hu, ← hw, ← hbc, ← hb, ← hc] using
    canonicalRepFast_field_identity (toPolyG a) (toPolyG d) (toPolyG q) (toPolyG r)
      (toPolyG dn) (toPolyG ds) (toPolyG b) (toPolyG c) hd hsplit_dn_ne hsplit_ds_ne hadiv
      hsplit_eq' hbcr

/-! ### The simple part `cₙ/dₙ` is a PROPER fraction — `deg cₙ < deg dₙ`

The canonical split `f = fₚ + b/dₛ + cₙ/dₙ` makes the simple part `cₙ/dₙ` proper. `cₙ` is the **second**
Bézout cofactor of `cextendedEuclideanSplitWf` (`c = w·r + (u·r div dₛ)·dₙ`, NOT structurally a remainder
mod `dₙ`), so `deg cₙ < deg dₙ` is the second-cofactor properness `cextendedEuclideanSplitWf_snd_degree_lt`:
it follows from the Bézout split `b·dₙ + c·dₛ = r`, the first cofactor `deg b < deg dₛ`, the denominator
split `d = dₛ·dₙ`, and `deg r < deg d` (`r = a mod d`). This feeds `hproper`/`haProper` of
`cHermiteReduceTowerG_residual_proper_of_degree_le_one` — the last open dependency of the §3.5
split-correctness frontier. Generic over `α`, with the split carried as a hypothesis (the abstract split
correctness is discharged at `α = QFunNZG ℚ` in `ComputableSplitFactorTowerCorrectG`). -/

/-- **★ The simple part `cₙ/dₙ` of the canonical split is proper** — `deg cₙ < deg dₙ`: for
`canonicalRepresentationFastG Dt fuel a d = (q, (b, dₛ), (cₙ, dₙ))`, the simple-part numerator `cₙ` has
degree below `dₙ`. Given the denominator split `d = dₛ·dₙ` (`hsplit_eq`, the abstract split correctness as a
hypothesis), the coprime Bézout gcd constant (`hgdeg`/`hgne`), and `d ≠ 0`. `cₙ =
(cextendedEuclideanSplitWf …).2`, so this is `cextendedEuclideanSplitWf_snd_degree_lt` with
`deg r < deg d` discharged from `r = a mod d` (`cmodWf_length_lt`) and the Bézout identity from
`toPolyG_cbezoutOneWf`. The last open dependency of
`hproper` for `deg Dt ≤ 1`. -/
theorem canonicalRepresentationFastG_simple_proper [CField α] [CFieldSpec α] [CDiffField α]
    [CFracGcdCore α] (Dt : CPolyG α) (fuel : ℕ) (a d : CPolyG α)
    (hd : toPolyG d ≠ 0)
    (hsplit_eq : toPolyG d
      = toPolyG (cSplitFactorFastG Dt fuel d).2 * toPolyG (cSplitFactorFastG Dt fuel d).1)
    (hsplit_dn_ne : toPolyG (cSplitFactorFastG Dt fuel d).1 ≠ 0)
    (hsplit_ds_ne : toPolyG (cSplitFactorFastG Dt fuel d).2 ≠ 0)
    (hgdeg : (toPolyG (cgcdWf (cSplitFactorFastG Dt fuel d).1
      (cSplitFactorFastG Dt fuel d).2).1).natDegree = 0)
    (hgne : toPolyG (cgcdWf (cSplitFactorFastG Dt fuel d).1
      (cSplitFactorFastG Dt fuel d).2).1 ≠ 0) :
    (toPolyG (CPolyG.canonicalRepresentationFastG Dt fuel a d).2.2.1).degree
      < (toPolyG (CPolyG.canonicalRepresentationFastG Dt fuel a d).2.2.2).degree := by
  set dnds := cSplitFactorFastG Dt fuel d with hdnds
  set dn := dnds.1 with hdn
  set ds := dnds.2 with hds
  set r := (cdivmodWf a d).2 with hr
  set uw := CPolyG.cbezoutOneWf dn ds with huw
  set u := uw.1 with hu
  set w := uw.2 with hw
  -- canonical-rep components: `cₙ = (cextendedEuclideanSplitWf …).2`, denominator-part `= dₙ`.
  have hcn : (CPolyG.canonicalRepresentationFastG Dt fuel a d).2.2.1
      = (CPolyG.cextendedEuclideanSplitWf dn ds r u w).2 := by
    rw [CPolyG.canonicalRepresentationFastG]
  have hdnpart : (CPolyG.canonicalRepresentationFastG Dt fuel a d).2.2.2 = dn := by
    rw [CPolyG.canonicalRepresentationFastG]
  rw [hcn, hdnpart]
  have hds0 : cnormG ds ≠ [] := fun h => hsplit_ds_ne ((cnormG_eq_nil_iff ds).mp h)
  have hdn0 : cnormG dn ≠ [] := fun h => hsplit_dn_ne ((cnormG_eq_nil_iff dn).mp h)
  have hbez : toPolyG u * toPolyG dn + toPolyG w * toPolyG ds = 1 := by
    have := toPolyG_cbezoutOneWf dn ds hgdeg hgne
    rw [← hu, ← hw] at this; exact this
  -- `deg r < deg d`: `r = a mod d`, a remainder mod `d` (no `deg a < deg d` needed).
  have hdcn : cnormG d ≠ [] := fun h => hd ((cnormG_eq_nil_iff d).mp h)
  have hrdeg : (toPolyG r).degree < (toPolyG d).degree := by
    have hrmod : r = cmodWf a d := rfl
    rw [hrmod]
    refine toPolyG_degree_lt_of_length_lt _ _ hdcn ?_
    show (cnormG (cmodWf a d) : List α).length < _
    exact cmodWf_length_lt a d hdcn
  exact cextendedEuclideanSplitWf_snd_degree_lt dn ds r u w d hds0 hdn0 hsplit_eq hbez hrdeg

end DeepWiki.SymbolicIntegration
