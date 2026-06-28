import DeepWiki.SymbolicIntegration.ComputableTowerReduce
import DeepWiki.SymbolicIntegration.ComputableFuelFreeGcd

/-! # Generic monic-gcd correctness + the `canonicalRepresentationFastG` reconstruction probe

Foundation lemmas for the generic tower engine's abstract correctness, over `[CField α] [CFieldSpec α]`:

1. **Generic gcd correctness + fuel-free**: `associated_toPolyG_cgcdMonicG` (the generic monic gcd is
   the polynomial gcd up to associates) from the generic `cgcdExtG` Bézout / divides theory; plus a
   fuel-free `cgcdMonicGWf` bridged to `cgcdMonicG` at sufficient fuel.
2. **The reconstruction probe** `canonicalRepresentationFastG_reconstructs`: the §3.5 capstone's
   reconstruction `toPolyG d = toPolyG dₛ·dₙ ⇒ …`, modulo the denominator split (the abstract
   correctness of that split is filled at `α = QFunNZ` in `ComputableSplitFactorTowerCorrect`). -/

open Polynomial Classical

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

/-! ### Task 3 — generic monic-gcd correctness `associated_toPolyG_cgcdMonicG`

The generic monic gcd `cgcdMonicG fuel p q = cmonicG (cgcdExtG fuel p q).1` returns the polynomial gcd
of the inputs up to associates over the genuine field `K = CFieldSpec.K α`. This is the generic
`[CField α] [CFieldSpec α]`-mirror of the QFunNZ-specific `associated_toPolyG_cgcdFF`
(`ComputableGcdCorrect`). It is assembled from the EXISTING generic gcd theory:

* `toPolyG_cgcdExtG_dvd` — under termination, the raw gcd divides both inputs (gives `gcd ∣ rawGcd`,
  via `dvd_gcd`);
* `toPolyG_dvd_cgcdExtG` — the raw gcd is divisible by *every* common divisor, in particular by
  `gcd (toPolyG p) (toPolyG q)` (gives `rawGcd ∣ gcd`, via `gcd_dvd_left`/`gcd_dvd_right`);
* `associated_toPolyG_cmonicG` — monic normalization is a unit-scaling.

Mutual divisibility yields `Associated` (`associated_of_dvd_dvd`). The `gcd` is over `K[X]` with `K` a
field (the `CFieldSpec.K α` field instance), so the `NormalizedGCDMonoid` structure on `K[X]` is
available generically. -/

variable {α : Type*} [CField α] [CFieldSpec α]

/-- **Abstract correctness of the generic monic gcd `cgcdMonicG`** (under a terminating run): over the
genuine field `K = CFieldSpec.K α`, `toPolyG (cgcdMonicG fuel p q)` is `Associated` to
`gcd (toPolyG p) (toPolyG q)` in `K[X]`. The generic `[CField α] [CFieldSpec α]`-mirror of
`associated_toPolyG_cgcdFF` — here the proof is purely algebraic (no `PrimPRSRegular` content gate),
because the generic `cgcdExtG` is the field-division Euclid (gcd is exact every step), so termination
alone gives both divisibility directions; monic normalization fixes the unit. -/
theorem associated_toPolyG_cgcdMonicG (fuel : ℕ) (p q : CPolyG α)
    (hterm : cgcdTerminatesG fuel p q) :
    Associated (toPolyG (CPolyG.cgcdMonicG fuel p q)) (gcd (toPolyG p) (toPolyG q)) := by
  -- The raw extended-Euclid gcd divides both inputs (termination), and is the greatest common divisor.
  obtain ⟨hdvd_p, hdvd_q⟩ := toPolyG_cgcdExtG_dvd fuel p q hterm
  -- monic-normalization is a unit-scaling of the raw gcd.
  have hassoc : Associated (toPolyG (CPolyG.cgcdMonicG fuel p q))
      (toPolyG (cgcdExtG fuel p q).1) := associated_toPolyG_cmonicG _
  refine hassoc.trans ?_
  -- Mutual divisibility between the raw gcd and the Mathlib `gcd`.
  apply associated_of_dvd_dvd
  · -- rawGcd ∣ gcd : rawGcd divides both p and q (`toPolyG_cgcdExtG_dvd`), so divides their gcd.
    exact dvd_gcd hdvd_p hdvd_q
  · -- gcd ∣ rawGcd : the Mathlib gcd is a common divisor, so it divides the (greatest) raw gcd.
    exact toPolyG_dvd_cgcdExtG fuel p q (gcd_dvd_left _ _) (gcd_dvd_right _ _)

/-! ### Task 3 — fuel-free generic monic gcd `cgcdMonicGWf`

The generic `cgcdMonicG` carries a `fuel : ℕ`. The fuel-free well-founded extended Euclid `cgcdWf`
(`ComputableFuelFreeGcd`, recursing on `(cnormG b).length`) already exists at the same generic
`[CField α]` level; we wrap it the same way `cgcdMonicG` wraps `cgcdExtG` and bridge through
`cgcdWf_eq`. -/

/-- **Fuel-free generic monic gcd** `cgcdMonicGWf p q = monic gcd(p, q)`: the gcd component of the
fuel-free well-founded extended Euclid `cgcdWf`, monic-normalized (`cmonicG`). The `[CField α]`-generic,
**fuel-free** companion of `cgcdMonicG` — `native_decide`-able over noncomputable-`CFieldSpec`
carriers, no fuel at runtime. -/
def cgcdMonicGWf (p q : CPolyG α) : CPolyG α :=
  CPolyG.cmonicG (CPolyG.cgcdWf p q).1

/-- **Bridge — `cgcdMonicGWf` equals `cgcdMonicG` at the self-sufficient fuel.** With
`fuel = (cnormG p).length + (cnormG q).length + 1`, the fuel-free `cgcdMonicGWf p q` agrees with
`cgcdMonicG fuel p q`: both are `cmonicG` of the same gcd component, and `cgcdWf p q = cgcdExtG fuel p q`
at this fuel (`cgcdWf_eq`). -/
theorem cgcdMonicGWf_eq (p q : CPolyG α) :
    cgcdMonicGWf p q
      = CPolyG.cgcdMonicG ((cnormG p : List α).length + (cnormG q : List α).length + 1) p q := by
  rw [cgcdMonicGWf, CPolyG.cgcdMonicG, CPolyG.cgcdWf_eq]

/-- **Bridge — `cgcdMonicGWf` equals `cgcdMonicG` at any sufficient fuel.** With
`(cnormG p).length ≤ fuel` and `(cnormG q).length < fuel`, the fuel-free `cgcdMonicGWf p q` agrees with
`cgcdMonicG fuel p q` (`cgcdWf_eq_of_fuel`). -/
theorem cgcdMonicGWf_eq_of_fuel (fuel : ℕ) (p q : CPolyG α)
    (hp : (cnormG p : List α).length ≤ fuel) (hq : (cnormG q : List α).length < fuel) :
    cgcdMonicGWf p q = CPolyG.cgcdMonicG fuel p q := by
  rw [cgcdMonicGWf, CPolyG.cgcdMonicG, CPolyG.cgcdWf_eq_of_fuel fuel p q hp hq]

/-! ### ★ Task 4 — THE PROBE: transporting a high-level QFunNZ correctness lemma to the generic engine

The key deliverable: measure how mechanical the transport of a *high-level* correctness proof is, to
gauge whether the full collapse (~12 correctness/fuel-free files) is mechanical or research.

We pick `canonicalRepFast_reconstructs` (`ComputableCanonicalRepCorrect`): the §3.5 capstone correctness
that the canonical-representation split `canonicalRepresentationFast Dt fuel a d = (q, (b, dₛ), (c, dₙ))`
recombines to `f = a/d`, i.e. `q + b/dₛ + c/dₙ = a/d` in `RatFunc (CFieldSpec.K QFunNZ)`. Its generic
analog is `canonicalRepresentationFastG_reconstructs` over `[CField α] [CFieldSpec α]`.

**Transport readout.** The two definitions are structurally identical — `canonicalRepresentationFastG`
is `canonicalRepresentationFast` with `cSplitFactorFast → cSplitFactorFastG`, every other step
(`cdivmodG`, `cbezoutOne`, `cextendedEuclideanSplit`) *already generic*. The QFunNZ proof decomposes as
(1) the denominator split `toPolyG d = toPolyG dₛ · toPolyG dₙ`, (2) the Euclidean division, (3) the
Bézout cofactors, (4) the Bézout split, assembled by the field identity. Of these, **(2), (3), (4), and
the assembly already use only generic lemmas** — `toPolyG_cdivmodG'`, `toPolyG_cbezoutOne`,
`toPolyG_cextendedEuclideanSplit` (all stated over `[CField α] [CFieldSpec α]`), and
`canonicalRepFast_field_identity` (over any `[Field K]`). The *only* QFunNZ-specific step is (1), which
the QFunNZ proof discharges via `cSplitFactorFast_isSplittingFactorizationGen` — and `cSplitFactorFastG`
has **no** abstract correctness lemma yet (only a `native_decide` validator `towerCanRepLvl2_recombines`).

So we state the generic reconstruction **modulo** the split fact (taking `toPolyG d = toPolyG dₛ·dₙ` as a
hypothesis — *exactly* what the QFunNZ split-correctness provides), and the entire rest of the proof
transports **verbatim** by the `QFunNZ → α` substitution. This pins the precise single ingredient the
full collapse needs: generify `cSplitFactorFast_isSplittingFactorizationGen` to `cSplitFactorFastG`. -/

variable {α : Type*}

open RatFunc in
/-- **★ THE PROBE — `canonicalRepresentationFastG` reconstructs `f`, generic over `[CField α]
[CDiffField α] [CFieldSpec α]`**, modulo the denominator split. With the generic output
`(q, (b, dₛ), (c, dₙ)) = canonicalRepresentationFastG Dt fuel a d`, *given* the split factorization
`toPolyG d = toPolyG dₛ · toPolyG dₙ` (the one ingredient `cSplitFactorFastG` does not yet prove
abstractly — `cSplitFactorFast_isSplittingFactorizationGen`'s generic analog), the Bézout-gcd-constant
witness, and `d ≠ 0` with enough fuel, the three pieces recombine to `f = a/d` in
`RatFunc (CFieldSpec.K α)`. The proof is the `QFunNZ → α` transport of `canonicalRepFast_reconstructs`,
*verbatim* — every helper (`toPolyG_cdivmodG'`, `toPolyG_cbezoutOne`,
`toPolyG_cextendedEuclideanSplit`, `canonicalRepFast_field_identity`) is already generic. **The probe
result**: high-level reconstruction proofs transport mechanically once the split-factor correctness is
generified. -/
theorem canonicalRepresentationFastG_reconstructs [CField α] [CDiffField α] [CFracGcdCore α]
    [CFieldSpec α] (Dt : CPolyG α) (fuel : ℕ) (a d : CPolyG α)
    (hd : toPolyG d ≠ 0)
    (hsplit_eq : toPolyG (cSplitFactorFastG Dt fuel d).2 ≠ 0 →
      toPolyG (cSplitFactorFastG Dt fuel d).1 ≠ 0 →
      toPolyG d = toPolyG (cSplitFactorFastG Dt fuel d).2 * toPolyG (cSplitFactorFastG Dt fuel d).1)
    (hsplit_dn_ne : toPolyG (cSplitFactorFastG Dt fuel d).1 ≠ 0)
    (hsplit_ds_ne : toPolyG (cSplitFactorFastG Dt fuel d).2 ≠ 0)
    (hgdeg : (toPolyG (cgcdExtG fuel (cSplitFactorFastG Dt fuel d).1
      (cSplitFactorFastG Dt fuel d).2).1).natDegree = 0)
    (hgne : toPolyG (cgcdExtG fuel (cSplitFactorFastG Dt fuel d).1
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
  set qr := cdivmodG fuel a d with hqr
  set dnds := cSplitFactorFastG Dt fuel d with hdnds
  set dn := dnds.1 with hdn
  set ds := dnds.2 with hds
  set q := qr.1 with hq
  set r := qr.2 with hr
  set uw := CPolyG.cbezoutOne fuel dn ds with huw
  set u := uw.1 with hu
  set w := uw.2 with hw
  set bc := CPolyG.cextendedEuclideanSplit fuel dn ds r u w with hbc
  set b := bc.1 with hb
  set c := bc.2 with hc
  -- 1. the denominator split `toPolyG d = toPolyG ds · toPolyG dn` (the HYPOTHESIS standing in for the
  --    missing generic `cSplitFactorFastG` correctness).
  have hsplit_eq' : toPolyG d = toPolyG ds * toPolyG dn := hsplit_eq hsplit_ds_ne hsplit_dn_ne
  -- 2. the Euclidean division `toPolyG a = toPolyG q · toPolyG d + toPolyG r` (generic).
  have hdcn : cnormG d ≠ [] := fun h => hd ((cnormG_eq_nil_iff d).mp h)
  have hadiv : toPolyG a = toPolyG q * toPolyG d + toPolyG r :=
    toPolyG_cdivmodG' fuel a d hdcn
  -- 3. the Bézout cofactors `u·dn + w·ds = 1` (generic).
  have hbez : toPolyG u * toPolyG dn + toPolyG w * toPolyG ds = 1 := by
    have := toPolyG_cbezoutOne fuel dn ds hgdeg hgne
    rw [← hu, ← hw] at this; exact this
  -- 4. the Bézout split `b·dn + c·ds = r` (generic).
  have hds0 : cnormG ds ≠ [] := fun h => hsplit_ds_ne ((cnormG_eq_nil_iff ds).mp h)
  have hbcr : toPolyG b * toPolyG dn + toPolyG c * toPolyG ds = toPolyG r := by
    have := toPolyG_cextendedEuclideanSplit fuel dn ds r u w hds0 hbez
    rw [← hb, ← hc] at this; exact this
  -- assemble the field identity (generic over any `[Field K]`).
  show (algebraMap (CFieldSpec.K α)[X] (RatFunc (CFieldSpec.K α)) (toPolyG q))
      + algebraMap (CFieldSpec.K α)[X] (RatFunc (CFieldSpec.K α)) (toPolyG b)
          / algebraMap (CFieldSpec.K α)[X] (RatFunc (CFieldSpec.K α)) (toPolyG ds)
      + algebraMap (CFieldSpec.K α)[X] (RatFunc (CFieldSpec.K α)) (toPolyG c)
          / algebraMap (CFieldSpec.K α)[X] (RatFunc (CFieldSpec.K α)) (toPolyG dn)
    = algebraMap (CFieldSpec.K α)[X] (RatFunc (CFieldSpec.K α)) (toPolyG a)
        / algebraMap (CFieldSpec.K α)[X] (RatFunc (CFieldSpec.K α)) (toPolyG d)
  exact canonicalRepFast_field_identity (toPolyG a) (toPolyG d) (toPolyG q) (toPolyG r)
    (toPolyG dn) (toPolyG ds) (toPolyG b) (toPolyG c) hd hsplit_dn_ne hsplit_ds_ne hadiv
    hsplit_eq' hbcr

/-! ### The simple part `cₙ/dₙ` is a PROPER fraction — `deg cₙ < deg dₙ`

The canonical split `f = fₚ + b/dₛ + cₙ/dₙ` makes the simple part `cₙ/dₙ` proper. `cₙ` is the **second**
Bézout cofactor of `cextendedEuclideanSplit` (`c = w·r + (u·r div dₛ)·dₙ`, NOT structurally a remainder
mod `dₙ`), so `deg cₙ < deg dₙ` is the second-cofactor properness `cextendedEuclideanSplit_snd_degree_lt`:
it follows from the Bézout split `b·dₙ + c·dₛ = r`, the first cofactor `deg b < deg dₛ`, the denominator
split `d = dₛ·dₙ`, and `deg r < deg d` (`r = a mod d`). This feeds `hproper`/`haProper` of
`cHermiteReduceTowerG_residual_proper_of_degree_le_one` — the last open dependency of the §3.5
split-correctness frontier. Generic over `α`, with the split carried as a hypothesis (the abstract split
correctness is discharged at `α = QFunNZG ℚ` in `ComputableSplitFactorTowerCorrectG`). -/

/-- **★ The simple part `cₙ/dₙ` of the canonical split is proper** — `deg cₙ < deg dₙ`: for
`canonicalRepresentationFastG Dt fuel a d = (q, (b, dₛ), (cₙ, dₙ))`, the simple-part numerator `cₙ` has
degree below `dₙ`. Given the denominator split `d = dₛ·dₙ` (`hsplit_eq`, the abstract split correctness as a
hypothesis), the coprime Bézout gcd constant (`hgdeg`/`hgne`), `d ≠ 0`, and enough fuel for `a` (`hfuelA`)
and the rescaled dividend `u·r` (`hfuelUR`). `cₙ = (cextendedEuclideanSplit …).2`, so this is
`cextendedEuclideanSplit_snd_degree_lt` with `deg r < deg d` discharged from `r = a mod d`
(`cmodG_length_lt`) and the Bézout identity from `toPolyG_cbezoutOne`. The last open dependency of
`hproper` for `deg Dt ≤ 1`. -/
theorem canonicalRepresentationFastG_simple_proper [CField α] [CFieldSpec α] [CDiffField α]
    [CFracGcdCore α] (Dt : CPolyG α) (fuel : ℕ) (a d : CPolyG α)
    (hd : toPolyG d ≠ 0)
    (hsplit_eq : toPolyG d
      = toPolyG (cSplitFactorFastG Dt fuel d).2 * toPolyG (cSplitFactorFastG Dt fuel d).1)
    (hsplit_dn_ne : toPolyG (cSplitFactorFastG Dt fuel d).1 ≠ 0)
    (hsplit_ds_ne : toPolyG (cSplitFactorFastG Dt fuel d).2 ≠ 0)
    (hgdeg : (toPolyG (cgcdExtG fuel (cSplitFactorFastG Dt fuel d).1
      (cSplitFactorFastG Dt fuel d).2).1).natDegree = 0)
    (hgne : toPolyG (cgcdExtG fuel (cSplitFactorFastG Dt fuel d).1
      (cSplitFactorFastG Dt fuel d).2).1 ≠ 0)
    (hfuelA : (cnormG a : List α).length ≤ fuel)
    (hfuelUR : (cnormG (cmulG (CPolyG.cbezoutOne fuel (cSplitFactorFastG Dt fuel d).1
      (cSplitFactorFastG Dt fuel d).2).1 (cdivmodG fuel a d).2) : List α).length ≤ fuel) :
    (toPolyG (CPolyG.canonicalRepresentationFastG Dt fuel a d).2.2.1).degree
      < (toPolyG (CPolyG.canonicalRepresentationFastG Dt fuel a d).2.2.2).degree := by
  set dnds := cSplitFactorFastG Dt fuel d with hdnds
  set dn := dnds.1 with hdn
  set ds := dnds.2 with hds
  set r := (cdivmodG fuel a d).2 with hr
  set uw := CPolyG.cbezoutOne fuel dn ds with huw
  set u := uw.1 with hu
  set w := uw.2 with hw
  -- canonical-rep components: `cₙ = (cextendedEuclideanSplit …).2`, denominator-part `= dₙ`.
  have hcn : (CPolyG.canonicalRepresentationFastG Dt fuel a d).2.2.1
      = (CPolyG.cextendedEuclideanSplit fuel dn ds r u w).2 := by
    rw [CPolyG.canonicalRepresentationFastG]
  have hdnpart : (CPolyG.canonicalRepresentationFastG Dt fuel a d).2.2.2 = dn := by
    rw [CPolyG.canonicalRepresentationFastG]
  rw [hcn, hdnpart]
  have hds0 : cnormG ds ≠ [] := fun h => hsplit_ds_ne ((cnormG_eq_nil_iff ds).mp h)
  have hdn0 : cnormG dn ≠ [] := fun h => hsplit_dn_ne ((cnormG_eq_nil_iff dn).mp h)
  have hbez : toPolyG u * toPolyG dn + toPolyG w * toPolyG ds = 1 := by
    have := toPolyG_cbezoutOne fuel dn ds hgdeg hgne
    rw [← hu, ← hw] at this; exact this
  -- `deg r < deg d`: `r = a mod d`, a remainder mod `d` (no `deg a < deg d` needed).
  have hdcn : cnormG d ≠ [] := fun h => hd ((cnormG_eq_nil_iff d).mp h)
  have hrdeg : (toPolyG r).degree < (toPolyG d).degree := by
    have hrmod : r = cmodG fuel a d := rfl
    rw [hrmod]
    refine toPolyG_degree_lt_of_length_lt _ _ hdcn ?_
    show (cnormG (cmodG fuel a d) : List α).length < _
    exact cmodG_length_lt fuel a d hdcn hfuelA
  exact cextendedEuclideanSplit_snd_degree_lt fuel dn ds r u w d hds0 hdn0 hsplit_eq hfuelUR hbez hrdeg

end DeepWiki.SymbolicIntegration
