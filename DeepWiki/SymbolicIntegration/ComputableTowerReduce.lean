import DeepWiki.SymbolicIntegration.ComputableTowerField
import DeepWiki.SymbolicIntegration.ComputableTowerIntegrate
import DeepWiki.SymbolicIntegration.ComputableFuelFreeGcd
import DeepWiki.SymbolicIntegration.ComputableHyperexpNormal

/-! # A gcd-cancel reduction layer for the tower fraction field `QFunNZG α`
The generic tower fraction field `QFunNZG α` (`ComputableTowerField`) keeps fractions **unreduced**:
`qaddNZG`/`qmulNZG` cross-multiply num/den with no gcd-cancel. This is correct but causes (a) coefficient
**swell** up the tower (each `qmul` squares the denominator size, limiting practical depth) and (b)
`crischDESolve`'s weak-normalizer to **choke** on spurious denominators when a residual arrives as an
unreduced fraction (the `ComputableHyperexpNormal` §5.9 frontier — e.g. a residue assembled as `2x/2x`).

This file adds the missing **reduction**: `qreduceG x` divides numerator and denominator of `x` by their
monic gcd `g = cgcdMonicG fuel num den` (`ComputableTowerIntegrate`), the `[CField α]`-computable
extended-Euclidean monic gcd. The denominator-nonzero subtype proof is `Prop`-erased via a `cisZeroG`
guard (the `CFieldDomain` discipline — no `toK` leak), so `qreduceG` stays computable and the tower still
`native_decide`s.

* **`qreduceG`** — the gcd-cancel `⟨(num/g, den/g), guard⟩`, guarded so the reduced denominator stays
  `cisZeroG`-nonzero (else it falls back to `x` unchanged), keeping it `[CField α]`-computable.
* **★ `toQFunNZG_qreduceG`** — the **key correctness lemma**: `toQFunNZG (qreduceG x) = toQFunNZG x` in
  `RatFunc (CFieldSpec.K α)`. The cancelled fraction equals the original (axiom-clean `[propext,
  Classical.choice, Quot.sound]`), via the generic exact-division identity `toPolyG_cdivG_exact_g` (gcd
  divides both ⇒ exact division) built here from `toPolyG_cdivmodG'` + the `cmodG`-is-zero argument.
* **SWELL demo** (`native_decide`) — a fraction with a common factor whose `qreduceG` is strictly
  smaller, with the field value unchanged.
* **STRETCH** — applying `qreduceG` to a hyperexponential residual `R` before `crischDESolve 0 R`.

The pervasive bake-into-`qaddNZG`/`qmulNZG` is a documented follow-up (it would re-pin the existing
representation-sensitive tower `native_decide`s); this file is the standalone reduction primitive + its
correctness, leaving the existing engine untouched. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open Compute

/-! ### Generic exact division through the bridge: `(p/q)·q = p` when `q ∣ p`

The denominator-preservation proof needs a **generic** exact-division identity: when `toPolyG q` divides
`toPolyG p` (and `q` is nonzero, fuel suffices), `toPolyG (cdivG fuel p q) · toPolyG q = toPolyG p`. We
prove the `[CField α] [CFieldSpec α]`-generic version directly from the Euclidean
identity `toPolyG_cdivmodG'` — the remainder is divisible by `q` yet has smaller degree, hence is zero. -/

namespace CPolyG

variable {α : Type*} [CField α] [CFieldSpec α]

/-- **The Euclidean remainder vanishes when the divisor divides the dividend** (generic, through
`toPolyG`): if `toPolyG q ∣ toPolyG p` with `q` nonzero (`cnormG q ≠ []`) and the fuel bounds the
dividend length (`(cnormG p).length ≤ fuel`), then `toPolyG (cmodG fuel p q) = 0`. The remainder is
divisible by `q` (from the Euclidean identity) yet strictly lower-degree than `q` (`cmodG_length_lt`), so
it must be the zero polynomial. The generic core of exact division. -/
theorem toPolyG_cmodG_eq_zero_of_dvd (fuel : ℕ) (p q : CPolyG α) (hq0 : cnormG q ≠ [])
    (hfuel : (cnormG p : List α).length ≤ fuel) (hdvd : toPolyG q ∣ toPolyG p) :
    toPolyG (cmodG fuel p q) = 0 := by
  have hQ0 : toPolyG q ≠ 0 := fun h => hq0 ((cnormG_eq_nil_iff q).mpr h)
  -- the Euclidean identity `p = quo·q + rem`
  have hid : toPolyG p
      = toPolyG (cdivmodG fuel p q).1 * toPolyG q + toPolyG (cdivmodG fuel p q).2 :=
    toPolyG_cdivmodG' fuel p q hq0
  -- so `q ∣ rem`
  have hdvdrem : toPolyG q ∣ toPolyG (cdivmodG fuel p q).2 := by
    have : toPolyG (cdivmodG fuel p q).2
        = toPolyG p - toPolyG (cdivmodG fuel p q).1 * toPolyG q := by
      rw [hid]; ring
    rw [this]; exact dvd_sub hdvd (Dvd.intro_left _ rfl)
  -- the remainder has strictly smaller normalized length than `q`
  have hlen : (cnormG (cmodG fuel p q) : List α).length < (cnormG q : List α).length :=
    cmodG_length_lt fuel p q hq0 hfuel
  -- `cmodG fuel p q = (cdivmodG fuel p q).2`
  have hmod : cmodG fuel p q = (cdivmodG fuel p q).2 := rfl
  by_contra hne
  -- a nonzero polynomial divisible by `q` has degree `≥ deg q`, contradicting the length bound
  rw [hmod] at hne hlen
  have hdeg : (toPolyG q).natDegree ≤ (toPolyG (cdivmodG fuel p q).2).natDegree :=
    Polynomial.natDegree_le_of_dvd hdvdrem hne
  have hrn : cnormG (cdivmodG fuel p q).2 ≠ [] := fun h => hne ((cnormG_eq_nil_iff _).mp h)
  rw [length_cnormG_of_ne _ hrn, length_cnormG_of_ne q hq0] at hlen
  omega

/-- **Generic exact division through `toPolyG`**: if `toPolyG q ∣ toPolyG p`, `q` is nonzero
(`cnormG q ≠ []`) and the fuel bounds the dividend length, then
`toPolyG (cdivG fuel p q) · toPolyG q = toPolyG p` — the quotient times the divisor recovers the
dividend exactly. The `[CField α] [CFieldSpec α]`-generic exact-division identity, derived from the
Euclidean identity `toPolyG_cdivmodG'` with a zero remainder
(`toPolyG_cmodG_eq_zero_of_dvd`). -/
theorem toPolyG_cdivG_exact_g (fuel : ℕ) (p q : CPolyG α) (hq0 : cnormG q ≠ [])
    (hfuel : (cnormG p : List α).length ≤ fuel) (hdvd : toPolyG q ∣ toPolyG p) :
    toPolyG (cdivG fuel p q) * toPolyG q = toPolyG p := by
  have hid : toPolyG p
      = toPolyG (cdivmodG fuel p q).1 * toPolyG q + toPolyG (cdivmodG fuel p q).2 :=
    toPolyG_cdivmodG' fuel p q hq0
  have hrem0 : toPolyG (cmodG fuel p q) = 0 :=
    toPolyG_cmodG_eq_zero_of_dvd fuel p q hq0 hfuel hdvd
  have hmod : cmodG fuel p q = (cdivmodG fuel p q).2 := rfl
  rw [hmod] at hrem0
  rw [cdivG, hid, hrem0, add_zero]

/-! ### The monic gcd divides both inputs (through `toPolyG`)

`cgcdMonicG fuel p q = cmonicG (cgcdExtG fuel p q).1` is the monic normalization of the extended-Euclidean
gcd. Under termination it divides both `p` and `q` (`toPolyG_cgcdExtG_dvd` for the raw gcd, transported
across the unit-associate `associated_toPolyG_cmonicG`). These are the `g ∣ num`, `g ∣ den` facts that
`qreduceG` cancels with. -/

/-- **The monic gcd divides both inputs** (through `toPolyG`): under `cgcdTerminatesG fuel p q`,
`toPolyG (cgcdMonicG fuel p q)` divides `toPolyG p` and `toPolyG q`. The monic gcd is an associate of the
extended-Euclidean gcd (`associated_toPolyG_cmonicG`), which divides both inputs (`toPolyG_cgcdExtG_dvd`);
divisibility transports across associates. -/
theorem toPolyG_cgcdMonicG_dvd (fuel : ℕ) (p q : CPolyG α) (hterm : cgcdTerminatesG fuel p q) :
    toPolyG (cgcdMonicG fuel p q) ∣ toPolyG p ∧ toPolyG (cgcdMonicG fuel p q) ∣ toPolyG q := by
  obtain ⟨hp, hq⟩ := toPolyG_cgcdExtG_dvd fuel p q hterm
  have hassoc : Associated (toPolyG (cgcdMonicG fuel p q)) (toPolyG (cgcdExtG fuel p q).1) :=
    associated_toPolyG_cmonicG _
  exact ⟨hassoc.dvd.trans hp, hassoc.dvd.trans hq⟩

end CPolyG

/-! ### `qreduceG`: the gcd-cancel reduction on `QFunNZG α`

`qreduceG fuel x` reduces the fraction `x = num/den ∈ QFunNZG α` by dividing both by their monic gcd
`g = cgcdMonicG fuel num den`. The reduced denominator `cdivG fuel den g` stays in the den-nonzero subtype
only when it passes the `cisZeroG` test — over a degenerate/under-fuelled run the exact division could
misbehave, so we **guard**: if `cisZeroG (cdivG fuel den g) = false` use the reduced pair, else fall back
to `x` unchanged. The guard makes the subtype proof trivial (it is exactly the branch condition) and the
whole thing `[CField α] [CFieldDomain α]`-computable — no `toK`/`CFieldSpec` leak. -/

namespace QFunNZG

variable {α : Type*} [CField α] [CFieldDomain α]

/-- **The gcd-cancel reduction** `qreduceG fuel x = (num/g, den/g)` with `g = cgcdMonicG fuel num den`
(`ComputableTowerIntegrate`): divide numerator and denominator of the fraction `x ∈ QFunNZG α` by their
monic gcd, cancelling the common factor. **Guarded**: the reduced pair is used only when its denominator
`cdivG fuel den g` passes the `[CField α]`-only nonzero test `cisZeroG _ = false` (so the den-nonzero
subtype proof is the branch condition itself, `Prop`-erased); otherwise `qreduceG` returns `x` unchanged.
Kept `[CField α] [CFieldDomain α]`-**computable** (no `toK` leak — the `CFieldDomain` discipline), so the
tower still `native_decide`s. The cure for fraction-field swell and the `crischDESolve` spurious-
denominator choke. -/
def qreduceG (fuel : ℕ) (x : QFunNZG α) : QFunNZG α :=
  let num := x.1.1
  let den := x.1.2
  let g := CPolyG.cgcdMonicG fuel num den
  let den' := CPolyG.cdivG fuel den g
  if h : CPolyG.cisZeroG den' = false then
    ⟨(CPolyG.cdivG fuel num g, den'), h⟩
  else x

end QFunNZG

/-! ### ★ The key correctness lemma: `qreduceG` preserves the field value

`toQFunNZG_qreduceG : toQFunNZG (qreduceG fuel x) = toQFunNZG x`. On the fall-back branch this is
`rfl`-immediate. On the reduced branch, with `g = cgcdMonicG fuel num den` dividing both `num` and `den`
(`toPolyG_cgcdMonicG_dvd`, under termination), exact division (`toPolyG_cdivG_exact_g`) gives
`toPolyG (num/g)·toPolyG g = toPolyG num` and likewise for `den`, so
`amG(toPolyG(num/g))/amG(toPolyG(den/g)) = amG(toPolyG num)/amG(toPolyG den)` after clearing the common
`amG(toPolyG g)` — the cancelled fraction equals the original in `RatFunc (CFieldSpec.K α)`. The
hypotheses (termination + fuel) are exactly what a real run satisfies; the headline demos discharge them
by `native_decide`/`decide`. -/

namespace QFunNZG

-- `[CFieldDomain α]` is synthesized from `[CFieldSpec α]` (`instCFieldDomainOfCFieldSpec`), so it is NOT
-- listed here — listing it would shadow that instance and trip the unused-section-variable linter.
variable {α : Type*} [CField α] [CFieldSpec α]

/-- **★ `qreduceG` preserves the field value** (the KEY correctness lemma): under the gcd termination
predicate and a fuel bounding both numerator and denominator lengths,
`toQFunNZG (qreduceG fuel x) = toQFunNZG x` in `RatFunc (CFieldSpec.K α)` — the cancelled fraction equals
the original. The reduced branch cancels the common monic-gcd factor `g`: `g ∣ num`, `g ∣ den`
(`toPolyG_cgcdMonicG_dvd`), exact division `toPolyG (num/g)·toPolyG g = toPolyG num` and the den analogue
(`toPolyG_cdivG_exact_g`), so the two fractions agree after clearing `amG (toPolyG g)`. The fall-back
branch is definitionally `x`. Axiom-clean `[propext, Classical.choice, Quot.sound]`. This certifies the
swell fix is **value-preserving** — `qreduceG` only shrinks the representation, never changes the element
of `ℚ(x)(t₁)…`. -/
theorem toQFunNZG_qreduceG (fuel : ℕ) (x : QFunNZG α)
    (hterm : CPolyG.cgcdTerminatesG fuel x.1.1 x.1.2)
    (hfn : (CPolyG.cnormG x.1.1 : List α).length ≤ fuel)
    (hfd : (CPolyG.cnormG x.1.2 : List α).length ≤ fuel) :
    toQFunNZG (qreduceG fuel x) = toQFunNZG x := by
  rw [qreduceG]
  set num := x.1.1 with hnum
  set den := x.1.2 with hden
  set g := CPolyG.cgcdMonicG fuel num den with hg
  set den' := CPolyG.cdivG fuel den g with hden'
  by_cases h : CPolyG.cisZeroG den' = false
  · rw [dif_pos h]
    -- the denominator `den` is nonzero (subtype membership of `x`)
    have hdenNZ : CPolyG.cisZeroG den = false := x.2
    have hdenNorm : CPolyG.cnormG den ≠ [] := by
      rw [CPolyG.cisZeroG] at hdenNZ
      exact fun he => by rw [he] at hdenNZ; simp at hdenNZ
    -- the gcd `g` is nonzero (it divides the nonzero `den`, and `den/g` is nonzero)
    have hgNorm : CPolyG.cnormG g ≠ [] := by
      intro he
      -- `g = 0` ⇒ `toPolyG g = 0` ⇒ `cdivG den g` is junk; but its `cisZeroG` is false by guard.
      -- We rule this out: if `cnormG g = []`, then `cdivG fuel den g = cnormG`-of-something with a zero
      -- divisor. Use the exact-division contradiction below instead via dvd.
      have hg0 : CPolyG.toPolyG g = 0 := (CPolyG.cnormG_eq_nil_iff g).mp he
      -- `g ∣ den` so `toPolyG den = 0`, contradicting `den` nonzero
      obtain ⟨_, hgd⟩ := CPolyG.toPolyG_cgcdMonicG_dvd fuel num den hterm
      rw [← hg] at hgd
      rw [hg0] at hgd
      have : CPolyG.toPolyG den = 0 := zero_dvd_iff.mp hgd
      exact hdenNorm ((CPolyG.cnormG_eq_nil_iff den).mpr this)
    -- `g` divides `num` and `den` through `toPolyG`
    obtain ⟨hgn, hgd⟩ := CPolyG.toPolyG_cgcdMonicG_dvd fuel num den hterm
    rw [← hg] at hgn hgd
    -- exact division identities
    have hexn : CPolyG.toPolyG (CPolyG.cdivG fuel num g) * CPolyG.toPolyG g = CPolyG.toPolyG num :=
      CPolyG.toPolyG_cdivG_exact_g fuel num g hgNorm hfn hgn
    have hexd : CPolyG.toPolyG den' * CPolyG.toPolyG g = CPolyG.toPolyG den := by
      rw [hden']; exact CPolyG.toPolyG_cdivG_exact_g fuel den g hgNorm hfd hgd
    -- nonzero images in `RatFunc`
    have hgImg : amG α (CPolyG.toPolyG g) ≠ 0 :=
      amG_toPolyG_ne_zero (fun he => hgNorm ((CPolyG.cnormG_eq_nil_iff g).mpr he))
    have hdenImg : amG α (CPolyG.toPolyG den) ≠ 0 :=
      amG_toPolyG_ne_zero (toPolyG_ne_zero_of_cisZeroG_false hdenNZ)
    have hden'Img : amG α (CPolyG.toPolyG den') ≠ 0 :=
      amG_toPolyG_ne_zero (toPolyG_ne_zero_of_cisZeroG_false h)
    -- unfold both sides of `toQFunNZG`
    show amG α (CPolyG.toPolyG (CPolyG.cdivG fuel num g)) / amG α (CPolyG.toPolyG den')
      = amG α (CPolyG.toPolyG num) / amG α (CPolyG.toPolyG den)
    -- rewrite num/den by the exact-division products and cancel `amG (toPolyG g)`
    rw [← hexn, ← hexd, map_mul, map_mul]
    field_simp
  · rw [dif_neg h]
end QFunNZG

/-! ### ★ SWELL demo: `qreduceG` shrinks an unreduced product, value unchanged (`native_decide`)

We build a fraction over `CPolyG ℚ = ℚ[x]` (level 0, the base field — `ℚ` is a `CField`/`CFieldSpec`/
`CFieldDomain`) with a deliberate common factor, demonstrate `qreduceG` strictly shrinks its
numerator/denominator length, and certify (via `toQFunNZG_qreduceG`) that the field value is unchanged.
The unreduced fraction is `qmulNZG (t/(t-1)) ((t-1)/t) = (t·(t-1))/((t-1)·t)`, whose num and den both have
length 3 (degree 2) but which is the constant `1`; `qreduceG` cancels to the reduced `1/1` (length 1).
This is the swell that iterated `qmulNZG` accumulates and that `qreduceG` removes. -/

namespace QFunNZG

/-- The base-field fraction `t/(t−1) ∈ QFunNZG ℚ = ℚ(x)` (numerator `[0,1]`, denominator `[−1,1]`), a
nonzero-denominator fraction over `CPolyG ℚ = ℚ[x]`. -/
def swellA : QFunNZG ℚ := ⟨([(0 : ℚ), 1], [(-1 : ℚ), 1]), by native_decide⟩

/-- The base-field fraction `(t−1)/t ∈ QFunNZG ℚ` (numerator `[−1,1]`, denominator `[0,1]`); the
reciprocal of `swellA`, so their `qmulNZG` is the constant `1` but stored **unreduced** as
`(t·(t−1))/((t−1)·t)`. -/
def swellB : QFunNZG ℚ := ⟨([(-1 : ℚ), 1], [(0 : ℚ), 1]), by native_decide⟩

/-- The **unreduced** product `swellA · swellB = (t·(t−1))/((t−1)·t)` (via `qmulNZG`, no gcd-cancel):
both numerator `t·(t−1) = t²−t` and denominator `(t−1)·t = t²−t` have length 3 (degree 2), even though
the fraction is the constant `1` — the swell. -/
def swellProd : QFunNZG ℚ := qmulNZG swellA swellB

/-- **The unreduced product has numerator length 3** (`native_decide`): `qmulNZG` cross-multiplied to
`t²−t` (degree 2, length-3 list) — the swollen representation. -/
theorem swellProd_num_length : (CPolyG.cnormG swellProd.1.1 : List ℚ).length = 3 := by native_decide

/-- **The unreduced product has denominator length 3** (`native_decide`): the cross-multiplied
denominator `(t−1)·t = t²−t` is likewise length 3 — both sides carry the spurious common factor. -/
theorem swellProd_den_length : (CPolyG.cnormG swellProd.1.2 : List ℚ).length = 3 := by native_decide

/-- **★ `qreduceG` shrinks the swollen product's numerator to length 1** (`native_decide`): cancelling the
common factor `t²−t` collapses `(t²−t)/(t²−t)` to `1/1`, so the reduced numerator has length 1 — the swell
is removed (3 → 1). -/
theorem swellProd_reduced_num_length :
    (CPolyG.cnormG (qreduceG 8 swellProd).1.1 : List ℚ).length = 1 := by native_decide

/-- **★ `qreduceG` shrinks the swollen product's denominator to length 1** (`native_decide`): the reduced
denominator is likewise length 1 (`1`), confirming `qreduceG` strictly controls the fraction-field swell
(3 → 1 on both sides). -/
theorem swellProd_reduced_den_length :
    (CPolyG.cnormG (qreduceG 8 swellProd).1.2 : List ℚ).length = 1 := by native_decide

/-- **The reduced product is `cisZeroG`-nonzero in numerator** (`native_decide`): `qreduceG swellProd`
landed `1/1`, whose numerator `1` is nonzero — the reduction produced a genuine nonzero fraction (the
constant `1`), not a degenerate one. -/
theorem swellProd_reduced_num_nonzero :
    CPolyG.cisZeroG (qreduceG 8 swellProd).1.1 = false := by native_decide

/-- **★ The swell reduction preserves the field value** (via `toQFunNZG_qreduceG`): `qreduceG 8 swellProd`
equals `swellProd` as an element of `RatFunc ℚ` — the representation shrank (length 3 → 1, the previous
`native_decide`s) but the value is unchanged. The termination hypothesis is discharged by
`cgcdTerminatesG_of_fuel` (`ComputableFuelFreeGcd`) from the two length bounds, themselves closed by
`native_decide` (the gcd run on these concrete degree-≤2 lists terminates well within fuel 8). This is the
milestone: a **value-preserving** swell reduction. -/
theorem swellProd_value_preserved :
    toQFunNZG (qreduceG 8 swellProd) = toQFunNZG swellProd :=
  toQFunNZG_qreduceG 8 swellProd
    (CPolyG.cgcdTerminatesG_of_fuel 8 swellProd.1.1 swellProd.1.2 (by native_decide)
      (by native_decide))
    (by native_decide) (by native_decide)

/-! #### `qreduceG` preserves the zero test — the bake-into-ops safety fact

Every tower `native_decide` reads the field zero test `CField.isZero = isZeroNZG`, certified
*value-faithful* by `isZeroNZG_iff`. Since `qreduceG` preserves the field value
(`toQFunNZG_qreduceG`), it preserves `isZeroNZG`: a reduced fraction tests zero exactly when the
original does. This is the load-bearing fact for the **bake-into-`qaddNZG`/`qmulNZG` assessment** — any
test of the form `CField.isZero (… add/mul …) = true/false` is unaffected by inserting `qreduceG` into the
ops (the value, hence the zero test, is unchanged); only a test pinning a *literal* fraction
representation could shift, and the tower suite pins outer `CPolyG`-list lengths (degree in the new
monomial), not the inner coefficient-fraction lists `qreduceG` touches. -/

variable {α : Type*} [CField α] [CFieldSpec α]

/-- **`qreduceG` preserves the zero test** (`isZeroNZG (qreduceG fuel x) = isZeroNZG x`), under the same
gcd-termination + fuel preconditions as `toQFunNZG_qreduceG`: the reduced fraction is zero in
`RatFunc (CFieldSpec.K α)` exactly when the original is (`isZeroNZG_iff` both ways, bridged by the
value-preservation `toQFunNZG_qreduceG`). This is the bake-safety fact: every tower `CField.isZero` check
reads `isZeroNZG`, so inserting `qreduceG` into `qaddNZG`/`qmulNZG` cannot flip any such check. -/
theorem isZeroNZG_qreduceG (fuel : ℕ) (x : QFunNZG α)
    (hterm : CPolyG.cgcdTerminatesG fuel x.1.1 x.1.2)
    (hfn : (CPolyG.cnormG x.1.1 : List α).length ≤ fuel)
    (hfd : (CPolyG.cnormG x.1.2 : List α).length ≤ fuel) :
    isZeroNZG (qreduceG fuel x) = isZeroNZG x := by
  have hval : toQFunNZG (qreduceG fuel x) = toQFunNZG x := toQFunNZG_qreduceG fuel x hterm hfn hfd
  have h1 := isZeroNZG_iff (qreduceG fuel x)
  have h2 := isZeroNZG_iff x
  rw [hval] at h1
  -- both Bools test the same proposition `toQFunNZG x = 0`, so they are equal
  by_cases hz : toQFunNZG x = 0
  · rw [h1.mpr hz, h2.mpr hz]
  · rw [Bool.eq_false_iff.mpr (fun h => hz (h1.mp h)),
      Bool.eq_false_iff.mpr (fun h => hz (h2.mp h))]

#print axioms toQFunNZG_qreduceG
#print axioms swellProd_value_preserved
#print axioms isZeroNZG_qreduceG

end QFunNZG

/-! ### STRETCH demo: `qreduceG` unblocks a hyperexponential residual that chokes `crischDESolve`

`ComputableHyperexpNormal`'s §5.9 feedback integrates a normal hyperexponential part `fₙ` via the residual
base solve `crischDESolve 0 R`. That solve can return `none` not because the residual `R` is
non-elementary, but because it arrives as an **unreduced** `QFunNZG` fraction whose spurious denominator
trips the weak-normalizer. We exhibit that representational frontier on a residual that is the value `1`
stored as `(2x)/(2x)`: `crischDESolve 0 R` **chokes** (`Rstuck_unreduced_chokes`), but after the gcd-cancel
`qreduceG` collapses it to `1/1` the base solve **succeeds**, recovering `∫1 = x` (`Rstuck_reduced_solves`).
So the choke is **purely representational** (the value is the elementary δ-constant `1`) and `qreduceG`
genuinely unblocks it — value-preserving (`toQFunNZG_qreduceG`). -/

namespace QFunNZG

open CPolyG

/-! #### The decisive choke/unblock: an unreduced residual `crischDESolve` can't solve until `qreduceG`

`Rstuck` is the value `1 ∈ ℚ(x)` stored **unreduced** as the fraction `(2x)/(2x)` — built by
`qmulNZG (2x/1) (1/2x)`, exactly the `2x/2x` shape the §5.9 frontier flags. `crischDESolve 0 Rstuck` chokes
(`none`) on the spurious `2x` denominator; `crischDESolve 0 (qreduceG Rstuck)` solves it. This is the
concrete non-constant-R unblock — value-preserving (`qreduceG` keeps `Rstuck = 1`), and it converts a
`none` into a correct `some` (`y = x`). -/

/-- The residual `1 ∈ ℚ(x)` stored **unreduced** as `(2x)/(2x)`: `qmulNZG (2x/1) (1/(2x))`, with numerator
`2x·1` and denominator `1·2x` (both length-2 lists, the swollen `2x/2x` shape) yet the value `1`. The exact
representational frontier `ComputableHyperexpNormal` describes. -/
def Rstuck : QFunNZG ℚ :=
  qmulNZG nLvl1TwoX ⟨([CField.one], [(0 : ℚ), (2 : ℚ)]), by native_decide⟩

/-- **`Rstuck` is the value `1`** (`native_decide`): the unreduced `(2x)/(2x)` equals `1 ∈ ℚ(x)`
(`isZero (Rstuck − 1) = true`). So it is a genuine elementary δ-constant residue — the choke below is
representational, not non-elementarity. -/
theorem Rstuck_eq_one : CField.isZero (CField.sub Rstuck (CField.one : QFunNZG ℚ)) = true := by
  native_decide

/-- **`Rstuck`'s stored denominator is swollen (length 2)** (`native_decide`): the unreduced `(2x)/(2x)` has
a length-2 denominator `2x`, not the reduced `1`. This `2x` is the spurious denominator that chokes
`crischDESolve`. -/
theorem Rstuck_den_swollen : (CPolyG.cnormG Rstuck.1.2 : List ℚ).length = 2 := by native_decide

/-- **★ The unreduced residual chokes `crischDESolve`** (`native_decide`, the choke): `crischDESolve 0
Rstuck` over `k = ℚ(x)` returns **`none`** — even though `Rstuck = 1` (`Rstuck_eq_one`), the weak-
normalizer/normal-denominator stages trip on the spurious `2x` denominator of the unreduced `(2x)/(2x)`.
This is the §5.9 hyperexponential frontier the module docstring flags, reproduced concretely. -/
theorem Rstuck_unreduced_chokes :
    CRischField.crischDESolve (CField.zero : QFunNZG ℚ) Rstuck = none := by native_decide

/-- **★ `qreduceG` unblocks the residual: `crischDESolve` then solves, recovering `∫1 = x`**
(`native_decide`, the UNBLOCK). After `qreduceG 8 Rstuck` cancels `(2x)/(2x)` to `1/1`,
`crischDESolve 0 (qreduceG 8 Rstuck)` over `ℚ(x)` returns **`some y`** with `y = x` (the base integral
`∫1 = x`). So the gcd-cancel layer turns the choke (`Rstuck_unreduced_chokes`, `none`) into a correct
`some` — the non-constant-R hyperexp residual unblock, value-preserving (`Rstuck = 1`, so `∫1 = x`). **This
is the stretch deliverable: a residual that currently chokes `crischDESolve` computes once reduced.** -/
theorem Rstuck_reduced_solves :
    (match CRischField.crischDESolve (CField.zero : QFunNZG ℚ) (qreduceG 8 Rstuck) with
      | some y => CField.isZero (CField.sub y nLvl1X)
      | none => false) = true := by native_decide

#print axioms Rstuck_unreduced_chokes
#print axioms Rstuck_reduced_solves

end QFunNZG

end DeepWiki.SymbolicIntegration
