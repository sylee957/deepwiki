import DeepWiki.SymbolicIntegration.ComputableTowerGcdFFCore
import DeepWiki.SymbolicIntegration.ComputableTowerGcdFF
import DeepWiki.SymbolicIntegration.ComputableGcdCorrect
import DeepWiki.SymbolicIntegration.ComputableWellFounded
import Mathlib.RingTheory.Polynomial.Content

/-! # Abstract correctness of the GENERIC fraction-free gcd `cgcdFFRawCore` over a tower level
The QFunNZ-specific fraction-free gcd `cgcdFF` was proved abstractly correct in `ComputableGcdCorrect`
(`associated_toPolyG_cgcdFF`): over the field ℚ(x), `cgcdFF` computes the polynomial gcd up to associates,
by clearing denominators into ℚ[x][t], running a primitive polynomial-remainder sequence, and lifting
back. This file proves the **generic** counterpart for the tower kernel `cgcdFFRawCore`
(`ComputableTowerGcdFFCore`), which runs the SAME strategy over an arbitrary level
`α = QFunNZG β = Frac(CPolyG β = β[s])`: clear denominators into `GBPolyCore β = (β[s])[t]`, run the
primitive PRS over the GCD-domain coefficient ring `CPolyG β = β[s]` stripping the **content** each step
(via the level-`β` gcd `cgcdFFRawCore` as the content-gcd), and lift back.

The verdict (Task 1): the QFunNZ proof's *spine* transports — the `clearDenoms` unit-scaling bridge, the
Euclidean-step gcd invariant, the primitive-part unit scaling — but it is NOT a re-instantiation: the
concrete `Compute.b*` engine (`bnorm`/`bpsremainder`/`bcontentX`/`bprimitivePartX`) and its `toBPoly`
bridge are replaced by the generic `gb*Core` engine and a new bridge `toGBPolyG`, so each homomorphism /
PRS lemma is **re-derived** over `GBPolyCore β`. The genuinely new ingredient is the **content recursion**:
where QFunNZ's content-exactness came from the concrete `cgcdExt`-divides theory (`toPoly_cgcdExt_dvd`),
the generic content-gcd is the level-`β` `cgcdFFRawCore` *passed in*, so its content-exactness is the
**tower induction hypothesis** — the gcd-correctness at level `β` feeds the gcd-correctness at `QFunNZG β`,
bottoming at the raw Euclidean gcd over `ℚ`. Mathlib's generic content theory
(`Mathlib/RingTheory/Polynomial/Content.lean`, over `(CFieldSpec.K β)[X]` which is a
`NormalizedGCDMonoid`) supplies the content lemmas the `ℚ[x]`-specific steps used.

The bridge `K := CFieldSpec.K β`, `R := K[X]` (`= β[s]` abstractly, the GCD-domain coefficient ring):
* `toGBPolyG : GBPolyCore β → (RatFunc K)[X]` reads a `(β[s])[t]` list over the field `K(x) = Frac R`,
  the generic mirror of `ComputableGcdCorrect.toPolyB`.
* `toGBCoeffPoly : GBPolyCore β → R[X]` is the honest `R[t]` polynomial (mirror of `toBPoly`); `toGBPolyG`
  is its lift through `amG β : R → RatFunc K`. -/

open Polynomial Classical

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

/-! ### Generic gcd-step lemmas over an arbitrary field's polynomial ring
The `gcd`-invariant lemmas of `ComputableGcdCorrect` were stated over `(RatFunc ℚ)[X]`; the tower needs
them over `(RatFunc (CFieldSpec.K β))[X]` (and in fact over any field's polynomial ring). We re-state
them generically over `[Field F]`'s `F[X]` (a `NormalizedGCDMonoid` / Euclidean domain). -/

variable {F : Type*} [Field F]

/-- **gcd is invariant under an associated right argument** in `F[X]`. -/
theorem associated_gcd_right_field {A B B' : F[X]} (h : Associated B B') :
    Associated (gcd A B) (gcd A B') := by
  apply associated_of_dvd_dvd
  · exact dvd_gcd (gcd_dvd_left A B) ((gcd_dvd_right A B).trans h.dvd)
  · exact dvd_gcd (gcd_dvd_left A B') ((gcd_dvd_right A B').trans h.symm.dvd)

/-- **The Euclidean-step gcd invariant** in `F[X]`: if `cu` is a unit and `cu · A = R + S · B`
(a pseudo-division step up to the unit content `cu`), then `gcd A B` and `gcd B R` are associates — the
classic invariant `gcd(A,B) = gcd(B, A mod B)` over the field. -/
theorem associated_gcd_euclid_step_field {A B R S cu : F[X]} (hu : IsUnit cu)
    (hrel : cu * A = R + S * B) : Associated (gcd A B) (gcd B R) := by
  apply associated_of_dvd_dvd
  · apply dvd_gcd (gcd_dvd_right A B)
    have h1 : gcd A B ∣ cu * A - S * B :=
      dvd_sub ((gcd_dvd_left A B).mul_left cu) ((gcd_dvd_right A B).mul_left S)
    have hR : cu * A - S * B = R := by rw [hrel]; ring
    rwa [hR] at h1
  · apply dvd_gcd _ (gcd_dvd_left B R)
    have hcuA : gcd B R ∣ cu * A := by
      rw [hrel]; exact dvd_add (gcd_dvd_right B R) ((gcd_dvd_left B R).mul_left S)
    exact (IsUnit.dvd_mul_left hu).mp hcuA

/-! ### The base case `CFracGcdCore ℚ`: the raw Euclidean gcd computes the gcd up to associates
At the bottom of the tower `cgcdFFRawCore = (cgcdExtG _).1` over `ℚ[t]`. We package the gcd-correctness
of the **raw** generic Euclidean gcd `(cgcdExtG fuel a b).1` over any `[CField α] [CFieldSpec α]` level:
it is associated to the abstract `gcd` in `(CFieldSpec.K α)[X]`, from the proven Bézout
(`toPolyG_cgcdExtG`/`toPolyG_dvd_cgcdExtG`) and divides (`toPolyG_cgcdExtG_dvd`, under termination)
halves of the engine. This is the bottom of the tower induction (and reused for the *content*-gcd at any
level, since the content-gcd over `CPolyG β = β[s]` is itself a level-`β` `cgcdFFRawCore`). -/

/-- **The raw generic Euclidean gcd is associated to the abstract gcd** (under termination): for any
`[CField α] [CFieldSpec α]`, if `cgcdExtG fuel a b` terminates (`cgcdTerminatesG`), then
`toPolyG (cgcdExtG fuel a b).1` is `Associated` to `gcd (toPolyG a) (toPolyG b)` in `(CFieldSpec.K α)[X]`.
Combines the gcd-divides direction (`toPolyG_cgcdExtG_dvd`) with the greatest-common-divisor direction
(`toPolyG_dvd_cgcdExtG`, from Bézout) via `associated_of_dvd_dvd`. -/
theorem associated_toPolyG_cgcdExtG {α : Type*} [CField α] [CFieldSpec α] (fuel : ℕ) (a b : CPolyG α)
    (hterm : cgcdTerminatesG fuel a b) :
    Associated (toPolyG (cgcdExtG fuel a b).1) (gcd (toPolyG a) (toPolyG b)) := by
  obtain ⟨hda, hdb⟩ := toPolyG_cgcdExtG_dvd fuel a b hterm
  apply associated_of_dvd_dvd
  · exact dvd_gcd hda hdb
  · exact toPolyG_dvd_cgcdExtG fuel a b (gcd_dvd_left _ _) (gcd_dvd_right _ _)

/-! ### The bivariate bridge `toGBCoeffPoly : GBPolyCore β → R[X]` (`R = (CFieldSpec.K β)[X] = β[s]`)
A `GBPolyCore β = List (CPolyG β)` is a `t`-polynomial whose coefficients are `CPolyG β = β[s]`. Reading
each coefficient through `toPolyG : CPolyG β → R := (CFieldSpec.K β)[X]` and Horner-folding in `t` gives
the honest `R[t]` polynomial `toGBCoeffPoly p : R[X]` — the generic mirror of `ComputeCorrectness.toBPoly`
(which read `ℚ[x][t]` into `(ℚ[X])[X]`). Its homomorphism lemmas descend coefficientwise from `toPolyG`'s
ring-hom lemmas (`toPolyG_caddG`/`cnegG`/`cmulG`/…), mirroring `toBPoly_*` verbatim with
`ℚ ⟿ CFieldSpec.K β`. -/

namespace GBPolyCore

variable {β : Type*} [CField β] [CFieldSpec β]

/-- **Bivariate bridge** `toGBCoeffPoly : GBPolyCore β → ((CFieldSpec.K β)[X])[X]`: read a `GBPolyCore β`
(list of `CPolyG β = β[s]` `t`-coefficients, low→high) as an honest `R[t]` polynomial `R = (CFieldSpec.K
β)[X]` in Horner form in `t`, each `t`-coefficient embedded via `toPolyG`. The generic mirror of
`Compute.toBPoly`. -/
noncomputable def toGBCoeffPoly : GBPolyCore β → ((CFieldSpec.K β)[X])[X]
  | [] => 0
  | a :: p => Polynomial.C (CPolyG.toPolyG a) + Polynomial.X * toGBCoeffPoly p

/-- `toGBCoeffPoly [] = 0`. -/
@[simp] theorem toGBCoeffPoly_nil : toGBCoeffPoly ([] : GBPolyCore β) = 0 := rfl

/-- `toGBCoeffPoly`'s leading recursion (Horner). -/
@[simp] theorem toGBCoeffPoly_cons (a : CPolyG β) (p : GBPolyCore β) :
    toGBCoeffPoly (a :: p) = Polynomial.C (CPolyG.toPolyG a) + Polynomial.X * toGBCoeffPoly p := rfl

/-- `toGBCoeffPoly` is **additive**: `gbaddCore` realizes `R[t]` addition. -/
theorem toGBCoeffPoly_gbaddCore (p q : GBPolyCore β) :
    toGBCoeffPoly (gbaddCore p q) = toGBCoeffPoly p + toGBCoeffPoly q := by
  induction p generalizing q with
  | nil => simp [gbaddCore]
  | cons a as ih =>
    cases q with
    | nil => simp [gbaddCore]
    | cons b bs =>
      simp only [gbaddCore, toGBCoeffPoly_cons, ih bs, CPolyG.toPolyG_caddG, map_add]
      ring

/-- `toGBCoeffPoly` is **negation-compatible**: `gbnegCore` realizes `R[t]` negation. -/
theorem toGBCoeffPoly_gbnegCore (p : GBPolyCore β) :
    toGBCoeffPoly (gbnegCore p) = - toGBCoeffPoly p := by
  induction p with
  | nil => simp [gbnegCore]
  | cons a as ih =>
    show toGBCoeffPoly (CPolyG.cnegG a :: gbnegCore as) = _
    simp only [toGBCoeffPoly_cons, CPolyG.toPolyG_cnegG, map_neg, ih]
    ring

/-- `toGBCoeffPoly` is **subtraction-compatible**: `gbsubCore` realizes `R[t]` subtraction. -/
theorem toGBCoeffPoly_gbsubCore (p q : GBPolyCore β) :
    toGBCoeffPoly (gbsubCore p q) = toGBCoeffPoly p - toGBCoeffPoly q := by
  simp [gbsubCore, toGBCoeffPoly_gbaddCore, toGBCoeffPoly_gbnegCore, sub_eq_add_neg]

/-- `toGBCoeffPoly` realizes **scaling by a `β[s]` coefficient**: `gbscaleCCore c p` is
`C (toPolyG c) · toGBCoeffPoly p`. -/
theorem toGBCoeffPoly_gbscaleCCore (c : CPolyG β) (p : GBPolyCore β) :
    toGBCoeffPoly (gbscaleCCore c p) = Polynomial.C (CPolyG.toPolyG c) * toGBCoeffPoly p := by
  induction p with
  | nil => simp [gbscaleCCore]
  | cons a as ih =>
    show toGBCoeffPoly (CPolyG.cmulG c a :: gbscaleCCore c as) = _
    simp only [toGBCoeffPoly_cons, CPolyG.toPolyG_cmulG, map_mul, ih]
    ring

/-- `toGBCoeffPoly` realizes the **`t`-shift**: `gbshiftCore k p` is `tᵏ · toGBCoeffPoly p`. -/
theorem toGBCoeffPoly_gbshiftCore (k : ℕ) (p : GBPolyCore β) :
    toGBCoeffPoly (gbshiftCore k p) = Polynomial.X ^ k * toGBCoeffPoly p := by
  induction k with
  | zero => simp [gbshiftCore]
  | succ n ih =>
    show toGBCoeffPoly ([] :: gbshiftCore n p) = _
    simp only [toGBCoeffPoly_cons, toPolyG_nil, map_zero, ih]
    ring

omit [CFieldSpec β] in
/-- `gbnormCore [] = []`. -/
@[simp] theorem gbnormCore_nil : gbnormCore ([] : GBPolyCore β) = [] := rfl

omit [CFieldSpec β] in
/-- `gbnormCore` on a cons cell, unfolded to its defining `match` (definitional). -/
theorem gbnormCore_cons_eq (a : CPolyG β) (as : GBPolyCore β) :
    gbnormCore (a :: as)
      = (match gbnormCore as with
          | [] => if CPolyG.cisZeroG (CPolyG.cnormG a) then [] else [CPolyG.cnormG a]
          | r => CPolyG.cnormG a :: r) := rfl

omit [CFieldSpec β] in
/-- `gbnormCore` is **idempotent**. -/
@[simp] theorem gbnormCore_idem (p : GBPolyCore β) : gbnormCore (gbnormCore p) = gbnormCore p := by
  induction p with
  | nil => rfl
  | cons a as ih =>
    rw [gbnormCore_cons_eq]
    cases h : gbnormCore as with
    | nil => cases ha : CPolyG.cisZeroG (CPolyG.cnormG a) <;> simp [gbnormCore_cons_eq, cnormG_idem, ha]
    | cons b bs =>
      rw [h] at ih
      simp only [gbnormCore_cons_eq, cnormG_idem, ih]

/-- **`toGBCoeffPoly` ignores normalization**: `toGBCoeffPoly (gbnormCore p) = toGBCoeffPoly p`. -/
@[simp] theorem toGBCoeffPoly_gbnormCore (p : GBPolyCore β) :
    toGBCoeffPoly (gbnormCore p) = toGBCoeffPoly p := by
  induction p with
  | nil => rfl
  | cons a as ih =>
    rw [gbnormCore_cons_eq]
    cases h : gbnormCore as with
    | nil =>
      rw [h] at ih
      simp only [toGBCoeffPoly_nil] at ih
      have has : toGBCoeffPoly as = 0 := ih.symm
      cases ha : CPolyG.cisZeroG (CPolyG.cnormG a) with
      | true =>
        have hpa : CPolyG.toPolyG a = 0 := by
          have hca : CPolyG.cnormG a = [] := by simpa [CPolyG.cisZeroG, cnormG_idem] using ha
          rw [← toPolyG_cnormG, hca, toPolyG_nil]
        simp [toGBCoeffPoly_cons, hpa, has]
      | false => simp [toGBCoeffPoly_cons, toPolyG_cnormG, has]
    | cons b bs =>
      rw [h] at ih
      simp only [toGBCoeffPoly_cons, toPolyG_cnormG, ih]

end GBPolyCore

end DeepWiki.SymbolicIntegration
