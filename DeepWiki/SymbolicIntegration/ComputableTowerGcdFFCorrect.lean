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

end DeepWiki.SymbolicIntegration
