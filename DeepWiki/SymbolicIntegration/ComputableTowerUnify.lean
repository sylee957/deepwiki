import DeepWiki.SymbolicIntegration.ComputableTowerReduce
import DeepWiki.SymbolicIntegration.ComputableWellFounded

/-! # Unifying the generic tower engine with the level-1 QFunNZ engine

This file is the FOUNDATION + a MECHANICALNESS PROBE for collapsing the two parallel
symbolic-integration engines into one. The two engines are:

* the **level-1 QFunNZ engine** (`cIntegrate`/`cRischDE`/`cgcdFF`/…) — specialized to the carrier
  `QFunNZ = ℚ(x)`, abstractly **proven** and fuel-free;
* the **generic tower engine** (`cIntegrateG`/`cRischDEG`/`cgcdMonicG`/… over `[CField α]`) —
  `native_decide`-validated only.

The end goal is to *replace* the base algorithms by the generic ones with the rigor preserved. The
safe path is to first lift the generic engine to the QFunNZ engine's rigor, then collapse. This file
takes the first steps and measures whether the full collapse is mechanical:

1. **`instance : CRischField QFunNZ`** — the missing typeclass instance so the generic engine runs at
   `α = QFunNZ` (the level-1 carrier of the old engine). Its base RDE is the existing `cRischDEBase`
   (the §6.6 base solve over ℚ(x), `D = d/dx`), whose signature `QFunNZ → QFunNZ → Option QFunNZ`
   matches `crischDESolve` exactly.
2. **The "generic subsumes base" headline**: `cIntegrateG` *at* `α = QFunNZ` reproduces the level-1
   `cIntegrate` worked integral (Bronstein Example 5.6.2, `t = log x`) on the *same* literal inputs —
   the generic driver lands an antiderivative satisfying `D(∫f) = f` (`checkIdentityG`).
3. **Generic gcd correctness + fuel-free** (the proven foundation): `associated_toPolyG_cgcdMonicG`
   (the generic monic gcd is the polynomial gcd up to associates) from the generic `cgcdExtG` Bézout /
   divides theory; plus a fuel-free `cgcdMonicGWf` bridged to `cgcdMonicG` at sufficient fuel.
4. **The probe**: the generic analog of a high-level QFunNZ correctness lemma, with a precise readout
   of how mechanical the transport was.

Nothing here modifies or weakens the existing QFunNZ engine — it is purely additive. -/

open Polynomial Classical

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

/-! ### Task 1 — `CRischField QFunNZ`: running the generic engine at the level-1 carrier

The generic tower engine's RDE solver `cRischDEG` recurses, at every step, into the typeclass method
`CRischField.crischDESolve : α → α → Option α` (solving `Dy + f·y = g` over `α` with `α`'s own
derivation). To run the generic engine at `α = QFunNZ = ℚ(x)` (the level-1 carrier of the *old*
engine) we must supply `CRischField QFunNZ`. The other instances the generic algorithms need —
`CField QFunNZ`, `CFieldSpec QFunNZ`, `CDiffField QFunNZ`, and `CFieldDomain QFunNZ` (the last via the
global `[CFieldSpec α] → CFieldDomain α`) — all already resolve (verified by `#synth` below).

The RDE over ℚ(x) (`D = d/dx`) is *exactly* the existing level-1 base solver `cRischDEBase`
(`ComputableRischDE`, §6.6 eq. 6.23): `cRischDEBase fuel b c : Option QFunNZ` returns `some s` with
`Ds + b·s = c` (`D = d/dx` on `QFunNZ`, the `CDiffField QFunNZ` derivation `qderivNZ`), or `none`. Its
signature `QFunNZ → QFunNZ → Option QFunNZ` matches `crischDESolve` after fixing the fuel — so we wrap
it directly, no re-implementation. -/

/-- **The fixed fuel budget** for the `CRischField QFunNZ` base solve (the class method `crischDESolve`
carries no fuel argument). Matches `towerRischDEFuel`; generous for the small-degree validations. -/
def qfunNZRischDEFuel : ℕ := 60

/-- **★ `CRischField QFunNZ`** — the RDE over `QFunNZ = ℚ(x)` (`D = d/dx`), wrapping the existing level-1
base solver `cRischDEBase` (Bronstein §6.6 eq. 6.23). This is the missing instance that lets the
*generic* tower engine (`cRischDEG`/`cIntegrateG`/…) run at `α = QFunNZ`, i.e. on top of the old
engine's level-1 carrier. `crischDESolve f g = cRischDEBase fuel f g` solves `Dy + f·y = g` for
`y ∈ ℚ(x)`. Because `cRischDEBase` routes general non-constant inputs through the whole base ℚ-pipeline
`cRationalRDE` (over `CPolyG ℚ`, monomial `x`), this realizes the same level-1 RDE the QFunNZ engine
uses — now exposed to the generic driver via the typeclass. -/
instance instCRischFieldQFunNZ : CRischField QFunNZ where
  crischDESolve f g := CPolyG.cRischDEBase qfunNZRischDEFuel f g

/-- **All generic-engine instances resolve at `QFunNZ`** (the Task 1 readout): the generic algorithms
`cgcdMonicG`/`cRischDEG`/`cIntegrateG`/… need `CField`, `CFieldSpec`, `CDiffField`, `CFieldDomain`, and
`CRischField` — every one is provided at `α = QFunNZ`. (`CFieldDomain QFunNZ` comes from the global
`[CFieldSpec α] → CFieldDomain α` instance `instCFieldDomainOfCFieldSpec`; `CRischField QFunNZ` is
`instCRischFieldQFunNZ` above.) We pin them by name rather than `inferInstance` — `CFieldSpec`'s `Type*`
field (`K`) makes term-mode `inferInstance` fragile while `#synth`/by-name resolution succeeds; this is
the explicit witness that the whole stack is present. -/
theorem qfunNZ_resolves_all_generic_instances :
    Nonempty (CField QFunNZ) ∧ Nonempty (CFieldSpec.{0, 0} QFunNZ) ∧ Nonempty (CDiffField QFunNZ) ∧
      Nonempty (CFieldDomain QFunNZ) ∧ Nonempty (CRischField QFunNZ) :=
  ⟨⟨instCFieldQFunNZ⟩, ⟨instCFieldSpecQFunNZ⟩, ⟨instCDiffFieldQFunNZ⟩,
    ⟨instCFieldDomainOfCFieldSpec⟩, ⟨instCRischFieldQFunNZ⟩⟩

/-! ### ★ Task 2 — THE HEADLINE: `cIntegrateG` at `α = QFunNZ` reproduces the level-1 `cIntegrate`

The demonstration that the generic engine **structurally subsumes** the QFunNZ one. We take the level-1
worked integral — Bronstein **Example 5.6.2**, `t = log x`, `Dt = 1/x`, the transcendental integrand
`f = (1/2)·D(t+x)/(t+x) − (1/2)·D(t−x)/(t−x) ∈ ℚ(x)(log x)` with elementary antiderivative
`(1/2)log(t+x) − (1/2)log(t−x)` — and feed the **same literal inputs** (`integrateExampleDt`,
`integrateExampleNum`, `integrateExampleDen`, all `CPolyG QFunNZ`) to the **generic** driver
`cIntegrateG` *at* `α = QFunNZ`. It lands the same antiderivative: `checkIdentityG` certifies
`D(∫f) = f`, and the logarithmic part has the same length 2 (the two rational-residue logs `t ± x`).

The candidate residue set must be lifted from `List ℚ` (the level-1 `cIntegrate` shape) to `List QFunNZ`
(the generic `cIntegrateG` shape) — the *only* adaptation; the rationals embed via `ofConstNZ`. -/

/-- The level-1 residue candidates `{1/2, −1/2, 1, −1, 0}` (`integrateExampleCands`) lifted to `QFunNZ`
constants, the candidate set for the generic driver `cIntegrateG` (which scans over `List α`, not
`List ℚ`). The only input adaptation needed to run the level-1 Example 5.6.2 through the generic
engine. -/
def integrateExampleCandsG : List QFunNZ :=
  [QFunNZ.ofConstNZ (1/2), QFunNZ.ofConstNZ (-1/2), QFunNZ.ofConstNZ 1, QFunNZ.ofConstNZ (-1),
    QFunNZ.ofConstNZ 0]

/-- **★ The generic driver subsumes the level-1 integral** (`native_decide`): the generic
`cIntegrateG` *at* `α = QFunNZ`, on the *same* literal Example 5.6.2 inputs the level-1 `cIntegrate`
uses (`integrateExampleDt/Num/Den`), returns `some res` whose antiderivative identity `D(res) = f`
holds — `checkIdentityG` true, cleared of denominators over ℚ(x)[t]. The generic engine *computes the
same elementary antiderivative* over the level-1 carrier ℚ(x) that the specialized engine does. -/
theorem cIntegrateG_at_qfunNZ_reproduces_integrate_example :
    (match CPolyG.cIntegrateG integrateExampleDt 30 integrateExampleNum integrateExampleDen
        integrateExampleCandsG with
      | some res => CPolyG.checkIdentityG integrateExampleDt res
          integrateExampleNum integrateExampleDen
      | none => false) = true := by native_decide

/-- **The generic driver recovers the same two logarithms** (`native_decide`): like the level-1
`integrate_example_logs_length`, the generic `cIntegrateG` at `α = QFunNZ` returns a `logs` list of
length `2` — the rational-residue logs `t + x` and `t − x` of the Rothstein–Trager construction (the
`±1/2`-residue part). Same logarithmic structure as the specialized engine. -/
theorem cIntegrateG_at_qfunNZ_logs_length :
    (match CPolyG.cIntegrateG integrateExampleDt 30 integrateExampleNum integrateExampleDen
        integrateExampleCandsG with
      | some res => res.logs.length
      | none => 0) = 2 := by native_decide

/-- **Both engines agree on Example 5.6.2** (`native_decide`): the level-1 `cIntegrate` *and* the
generic `cIntegrateG` (at `α = QFunNZ`) each return a result satisfying its own antiderivative-identity
check on the same inputs — `integrate_example_driver` for the specialized engine and
`cIntegrateG_at_qfunNZ_reproduces_integrate_example` for the generic, conjoined. The explicit
"generic ⊇ base" statement: where the base engine integrates, the generic engine integrates the same
thing. -/
theorem both_engines_integrate_example_agree :
    ((match CPolyG.cIntegrate integrateExampleDt 30 integrateExampleNum integrateExampleDen
        integrateExampleCands with
      | some res => IntegralResult.checkIdentity integrateExampleDt res
          integrateExampleNum integrateExampleDen
      | none => false)
    && (match CPolyG.cIntegrateG integrateExampleDt 30 integrateExampleNum integrateExampleDen
        integrateExampleCandsG with
      | some res => CPolyG.checkIdentityG integrateExampleDt res
          integrateExampleNum integrateExampleDen
      | none => false)) = true := by native_decide

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
(`ComputableWellFounded`, recursing on `(cnormG b).length`) already exists at the same generic
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

end DeepWiki.SymbolicIntegration
