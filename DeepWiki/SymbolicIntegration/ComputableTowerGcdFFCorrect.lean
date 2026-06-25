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

/-! ### Generic exact Euclidean division `cdivG` (for the content strip)
The content strip `gbprimitivePartCore` divides every `t`-coefficient by the content via the generic
Euclidean `cdivG`. When the content divides the coefficient (in `R = (CFieldSpec.K α)[X]`), the division
is **exact** — `toPolyG (cdivG fuel c g) · toPolyG g = toPolyG c`. We prove this generically (the engine
analogues of `cmod_eq_zero_of_dvd_loc` / the `cdiv`-exact certificate), upstream-importable. -/

/-- **Generic exact-modulo from divisibility**: if `toPolyG g ∣ toPolyG c` and fuel bounds `c`'s length,
the Euclidean remainder vanishes (`toPolyG (cmodG fuel c g) = 0`). The Euclidean identity puts the
remainder in `(toPolyG g)` and below its degree, forcing it to `0`. Generic mirror of
`SubresultantCorrectness.cmod_eq_zero_of_dvd_loc`. -/
theorem toPolyG_cmodG_eq_zero_of_dvd {α : Type*} [CField α] [CFieldSpec α] (fuel : ℕ) (c g : CPolyG α)
    (hg : cnormG g ≠ []) (hfuel : (cnormG c : List α).length ≤ fuel)
    (hdvd : toPolyG g ∣ toPolyG c) : toPolyG (cmodG fuel c g) = 0 := by
  -- toPolyG c = quo · toPolyG g + toPolyG rem, with rem = cmodG, quo = cdivG
  have hid : toPolyG c = toPolyG (cdivG fuel c g) * toPolyG g + toPolyG (cmodG fuel c g) := by
    have h := toPolyG_cdivmodG' fuel c g hg
    rw [cdivG, cmodG]; exact h
  -- toPolyG g divides the remainder
  have hdvdrem : toPolyG g ∣ toPolyG (cmodG fuel c g) := by
    have hsub : toPolyG (cmodG fuel c g) = toPolyG c - toPolyG (cdivG fuel c g) * toPolyG g := by
      rw [hid]; ring
    rw [hsub]
    exact dvd_sub hdvd (Dvd.dvd.mul_left (dvd_refl _) _)
  -- the remainder has length < deg g; a nonzero multiple of g must reach deg g ⇒ contradiction
  by_contra hne
  -- a nonzero remainder has normalized length ≥ 1, so it is degree-bounded below g's
  have hcmodnil : cnormG (cmodG fuel c g) ≠ [] := fun h => hne ((cnormG_eq_nil_iff _).mp h)
  have hlen := cmodG_length_lt fuel c g hg hfuel
  have e1 : (toPolyG (cmodG fuel c g)).natDegree ≤ (cnormG (cmodG fuel c g) : List α).length - 1 :=
    natDegree_toPolyG_le _
  have e2 : (toPolyG g).natDegree = (cnormG g : List α).length - 1 := by
    rw [← cdegG_eq_natDegree, cdegG]
  have hcmodpos : 1 ≤ (cnormG (cmodG fuel c g) : List α).length :=
    List.length_pos_iff.mpr hcmodnil
  -- a nonzero multiple of g reaches at least deg g
  have hge : (toPolyG g).natDegree ≤ (toPolyG (cmodG fuel c g)).natDegree :=
    Polynomial.natDegree_le_of_dvd hdvdrem hne
  omega

/-- **Generic exact `cdivG`-division from divisibility**: if `toPolyG g ∣ toPolyG c` (and fuel/`g`
nonzero), the Euclidean quotient is exact — `toPolyG (cdivG fuel c g) · toPolyG g = toPolyG c`. From the
Euclidean identity with the (now zero) remainder. -/
theorem toPolyG_cdivG_exact {α : Type*} [CField α] [CFieldSpec α] (fuel : ℕ) (c g : CPolyG α)
    (hg : cnormG g ≠ []) (hfuel : (cnormG c : List α).length ≤ fuel)
    (hdvd : toPolyG g ∣ toPolyG c) : toPolyG (cdivG fuel c g) * toPolyG g = toPolyG c := by
  have hid : toPolyG c = toPolyG (cdivG fuel c g) * toPolyG g + toPolyG (cmodG fuel c g) := by
    have h := toPolyG_cdivmodG' fuel c g hg
    rw [cdivG, cmodG]; exact h
  rw [hid, toPolyG_cmodG_eq_zero_of_dvd fuel c g hg hfuel hdvd, add_zero]

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
/-- `gbnormCore` is **idempotent**. (Named `gbnormCore_idemp` to avoid clashing with the identical
`@[simp]` `GBPolyCore.gbnormCore_idem` defined downstream in `ComputableTowerWellFounded`, which this file
sits upstream of and so cannot import — the lemma's natural home is `ComputableTowerGcdFFCore`.) -/
@[simp] theorem gbnormCore_idemp (p : GBPolyCore β) : gbnormCore (gbnormCore p) = gbnormCore p := by
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

/-- **Coefficient read** of `toGBCoeffPoly`: `(toGBCoeffPoly p).coeff i = toPolyG (p.getD i [])`. The
Horner bridge realizes the dense `t`-coefficient list exactly (mirror of `toBPoly_coeff`). -/
theorem toGBCoeffPoly_coeff (p : GBPolyCore β) (i : ℕ) :
    (toGBCoeffPoly p).coeff i = CPolyG.toPolyG (p.getD i ([] : CPolyG β)) := by
  induction p generalizing i with
  | nil => simp [toPolyG_nil]
  | cons a as ih =>
    rw [toGBCoeffPoly_cons]
    cases i with
    | zero => simp [coeff_C]
    | succ n => simp [coeff_X_mul, ih]

/-- `gbnormCore` has **no trailing `toPolyG`-zero**: the last coefficient of `gbnormCore p` reads to a
nonzero `R = (CFieldSpec.K β)[X]` (its `cnormG` is nonempty, hence `toPolyG ≠ 0`). Mirror of
`SubresultantCorrectness.bnorm_getLast?_toPoly_ne_zero`. -/
theorem gbnormCore_getLast?_toPolyG_ne_zero (p : GBPolyCore β) :
    ∀ v, (gbnormCore p).getLast? = some v → CPolyG.toPolyG v ≠ 0 := by
  induction p with
  | nil => simp
  | cons a as ih =>
    rw [gbnormCore_cons_eq]
    cases h : gbnormCore as with
    | nil =>
      cases ha : CPolyG.cisZeroG (CPolyG.cnormG a) with
      | true => rw [if_pos rfl]; simp
      | false =>
        intro v hv
        rw [if_neg (by simp), List.getLast?_singleton, Option.some.injEq] at hv
        subst hv
        rw [toPolyG_cnormG]
        intro hz
        have hca : CPolyG.cnormG a = [] := (cnormG_eq_nil_iff a).mpr hz
        rw [CPolyG.cisZeroG, hca] at ha
        simp at ha
    | cons b bs =>
      rw [h] at ih
      intro v hv
      rw [List.getLast?_cons_cons] at hv
      exact ih v hv

/-- `gblcCore` is the **`t`-coefficient at the top index**: `toPolyG (gblcCore p) =
(toGBCoeffPoly p).coeff (gbdegCore p)`. -/
theorem toPolyG_gblcCore_eq_coeff (p : GBPolyCore β) :
    CPolyG.toPolyG (gblcCore p) = (toGBCoeffPoly p).coeff (gbdegCore p) := by
  rw [gblcCore, gbdegCore, ← toGBCoeffPoly_gbnormCore, toGBCoeffPoly_coeff,
    List.getD_eq_getElem?_getD, ← List.getLast?_eq_getElem?]

/-- **`gbisZeroCore` reads as `toGBCoeffPoly = 0`**: `gbisZeroCore p = true ↔ toGBCoeffPoly p = 0` (the
list normalizes to empty exactly for the zero polynomial in `t`). Generic mirror of
`SubresultantCorrectness.bisZero_iff_toBPoly_eq_zero`. -/
theorem gbisZeroCore_iff_toGBCoeffPoly (p : GBPolyCore β) :
    gbisZeroCore p = true ↔ toGBCoeffPoly p = 0 := by
  rw [gbisZeroCore, List.isEmpty_iff]
  constructor
  · intro h; rw [← toGBCoeffPoly_gbnormCore, h, toGBCoeffPoly_nil]
  · intro h
    rcases hb : gbnormCore p with _ | ⟨c, cs⟩
    · rfl
    · exfalso
      have hne : (gbnormCore p).getLast? ≠ none := by rw [hb]; simp
      rcases hg : (gbnormCore p).getLast? with _ | v
      · exact hne hg
      · have hv := gbnormCore_getLast?_toPolyG_ne_zero p v hg
        have hlc : gblcCore p = v := by rw [gblcCore, hg, Option.getD_some]
        have hcoeff0 : CPolyG.toPolyG (gblcCore p) = 0 := by
          rw [toPolyG_gblcCore_eq_coeff, h]; simp
        rw [hlc] at hcoeff0
        exact hv hcoeff0

end GBPolyCore

/-! ### The field-coefficient lift `R[t] → (RatFunc K)[t]` and `toGBPolyG`
`liftK = mapRingHom (amG β)` is the polynomial ring map induced by the field embedding
`amG β : R = (CFieldSpec.K β)[X] ↪ RatFunc (CFieldSpec.K β)`. `toGBPolyG p := liftK (toGBCoeffPoly p)`
reads a `GBPolyCore β` (`(β[s])[t]`) as a `(RatFunc K)[t]` polynomial, in the same indeterminate `t` as
`toPolyG` over `CPolyG (QFunNZG β)`. The generic mirror of `ComputableGcdCorrect.liftRF`/`toPolyB`. -/

open QFunNZG in
/-- The induced coefficient-ring lift `R[t] → (RatFunc K)[t]` (`(β[s])[t] → β(s)[t]`), applying
`amG β` to every `t`-coefficient. -/
noncomputable abbrev liftKG (β : Type*) [CField β] [CFieldSpec β] :
    ((CFieldSpec.K β)[X])[X] →+* (RatFunc (CFieldSpec.K β))[X] :=
  Polynomial.mapRingHom (QFunNZG.amG β)

/-- **The β(s)[t] reading of a `GBPolyCore β`** `toGBPolyG p`: read the `(β[s])[t]` polynomial
`toGBCoeffPoly p` over the field `β(s) = RatFunc (CFieldSpec.K β)` via the coefficient embedding
`amG β`. Lives in the same `(RatFunc (CFieldSpec.K β))[X] = (CFieldSpec.K (QFunNZG β))[X]` as
`toPolyG`. The generic mirror of `ComputableGcdCorrect.toPolyB`. -/
noncomputable def toGBPolyG {β : Type*} [CField β] [CFieldSpec β] (p : GBPolyCore β) :
    (RatFunc (CFieldSpec.K β))[X] :=
  liftKG β (GBPolyCore.toGBCoeffPoly p)

variable {β : Type*} [CField β] [CFieldSpec β]

/-- `toGBPolyG [] = 0`. -/
@[simp] theorem toGBPolyG_nil : toGBPolyG ([] : GBPolyCore β) = 0 := by simp [toGBPolyG]

/-- `liftKG (C c) = C (amG c)`: the lift sends a constant `β[s]`-coefficient to its `β(s)` embedding. -/
theorem liftKG_C (c : (CFieldSpec.K β)[X]) :
    liftKG β (Polynomial.C c) = Polynomial.C (QFunNZG.amG β c) := by
  simp [liftKG, Polynomial.coe_mapRingHom, Polynomial.map_C]

/-- **The lift-back bridge** `toPolyG (liftGBPolyCoreG p) = toGBPolyG p`: reading a `GBPolyCore β`
(`(β[s])[t]`) coefficientwise as the fraction `c/1 ∈ QFunNZG β` (`liftGBPolyCoreG`) and then through
`toPolyG` gives the SAME `β(s)[t]` polynomial as the coefficient-ring embedding `toGBPolyG` — both send
the `i`-th coefficient to `amG (toPolyG cᵢ)`. The generic mirror of `toPolyG_liftBPolyToQFunNZ`. -/
theorem toPolyG_liftGBPolyCoreG (p : GBPolyCore β) :
    toPolyG (CPolyG.liftGBPolyCoreG p) = toGBPolyG p := by
  apply Polynomial.ext
  intro i
  rw [toGBPolyG, liftKG, Polynomial.coe_mapRingHom, Polynomial.coeff_map,
    GBPolyCore.toGBCoeffPoly_coeff, toPolyG_coeff, CPolyG.liftGBPolyCoreG,
    List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : p[i]? with
  | none => simp [CFieldSpec.toK_zero, toPolyG_nil, map_zero]
  | some c =>
    simp only [Option.map_some, Option.getD_some]
    show QFunNZG.toQFunNZG _ = QFunNZG.amG β (CPolyG.toPolyG c)
    rw [QFunNZG.toQFunNZG]
    have h1 : CPolyG.toPolyG ([CField.one] : CPolyG β) = 1 := by
      rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_one, mul_zero, add_zero, map_one]
    show QFunNZG.amG β (CPolyG.toPolyG c) / QFunNZG.amG β (CPolyG.toPolyG ([CField.one] : CPolyG β))
      = QFunNZG.amG β (CPolyG.toPolyG c)
    rw [h1, map_one, div_one]

/-! ### The `cclearDenomsCoreG` bridge `β(s)[t] ↔ (β[s])[t]`
`cclearDenomsCoreG p` multiplies the `t`-polynomial `p ∈ β(s)[t]` through by the product of its
β(s)-coefficient denominators, landing a `GBPolyCore β ∈ (β[s])[t]` whose `i`-th coefficient is
`numᵢ · ∏_{j≠i} denⱼ`. Read back over the field `β(s)` (`toGBPolyG`), this equals `C s · toPolyG p` for
the **common denominator scalar** `s = ∏_j denⱼ ∈ β(s)` (nonzero, a unit). So the cleared polynomial is,
over β(s), a unit multiple of `toPolyG p` (`Associated`). The generic mirror of
`ComputableGcdCorrect.toPolyB_clearDenoms` — and structurally `cclearDenomsCoreG` is *identical* to the
concrete `clearDenoms` (same `zipIdx.map` + `filter`-fold), so the combinatorial core (`filter_prod_mul`)
is reused verbatim. -/

variable [CFieldDomain β]

omit [CFieldDomain β] in
/-- A `QFunNZG β` coefficient reads as `amG (toPolyG num) / amG (toPolyG den)` in `RatFunc (CFieldSpec.K
β)`. -/
theorem toQFunNZG_eq_div (c : QFunNZG β) :
    QFunNZG.toQFunNZG c
      = QFunNZG.amG β (CPolyG.toPolyG (CPolyG.qnumCoeffCoreG c))
        / QFunNZG.amG β (CPolyG.toPolyG (CPolyG.qdenCoeffCoreG c)) := by
  obtain ⟨⟨a, b⟩, hb⟩ := c; rfl

omit [CFieldDomain β] in
/-- A `QFunNZG β` coefficient's denominator has nonzero `toPolyG` (by subtype membership
`cisZeroG _ = false`). -/
theorem toPolyG_qdenCoeffCoreG_ne_zero (c : QFunNZG β) :
    CPolyG.toPolyG (CPolyG.qdenCoeffCoreG c) ≠ 0 := by
  obtain ⟨⟨a, b⟩, hb⟩ := c
  exact QFunNZG.toPolyG_ne_zero_of_cisZeroG_false hb

/-- **The common-denominator scalar** `commonDenG p ∈ R = (CFieldSpec.K β)[X]`: the product of all the
`β[s]`-denominators of `p`'s β(s)-coefficients, `∏_j toPolyG (qdenCoeffCoreG (p.get j))`. The (nonzero)
β(s)-unit by which `cclearDenomsCoreG` scales `toPolyG p`. The generic mirror of
`ComputableGcdCorrect.commonDen`. -/
noncomputable def commonDenG (p : CPolyG (QFunNZG β)) : (CFieldSpec.K β)[X] :=
  ((p.map CPolyG.qdenCoeffCoreG).map CPolyG.toPolyG).prod

omit [CFieldDomain β] in
/-- `commonDenG p ≠ 0`: a product of nonzero denominators. -/
theorem commonDenG_ne_zero (p : CPolyG (QFunNZG β)) : commonDenG p ≠ 0 := by
  rw [commonDenG]
  refine List.prod_ne_zero ?_
  intro hmem
  rw [List.mem_map] at hmem
  obtain ⟨d, hd, hd0⟩ := hmem
  rw [List.mem_map] at hd
  obtain ⟨c, hc, rfl⟩ := hd
  exact toPolyG_qdenCoeffCoreG_ne_zero c hd0

omit [CFieldDomain β] in
/-- `amG (commonDenG p) ≠ 0` (the field embedding of a nonzero product). -/
theorem amG_commonDenG_ne_zero (p : CPolyG (QFunNZG β)) : QFunNZG.amG β (commonDenG p) ≠ 0 :=
  (map_ne_zero_iff _ (RatFunc.algebraMap_injective (CFieldSpec.K β))).mpr (commonDenG_ne_zero p)

omit [CFieldDomain β] in
/-- `toPolyG` of a `cmulG`-fold is `toPolyG init` times the product of the `toPolyG`-images of the folded
list (the `R`-product realized by the computable fold). The generic mirror of
`ComputableGcdCorrect.toPoly_foldl_cmul`. -/
theorem toPolyG_foldl_cmulG (init : CPolyG β) (ds : List (CPolyG β × ℕ)) :
    CPolyG.toPolyG (ds.foldl (fun acc de => CPolyG.cmulG acc de.1) init)
      = CPolyG.toPolyG init * (ds.map (fun de => CPolyG.toPolyG de.1)).prod := by
  induction ds generalizing init with
  | nil => simp
  | cons hd tl ih =>
    rw [List.foldl_cons, ih, CPolyG.toPolyG_cmulG, List.map_cons, List.prod_cons]; ring

omit [CFieldSpec β] in
/-- The list-getElem reading of `cclearDenomsCoreG p` at an in-range index `i`: the `i`-th cleared
coefficient is `numᵢ · (∏_{j≠i} denⱼ)`, with `∏_{j≠i}` the filtered fold over the denominator list.
Mirror of `ComputableGcdCorrect.clearDenoms_getElem`. -/
theorem cclearDenomsCoreG_getElem (p : CPolyG (QFunNZG β)) (i : ℕ) (hi : i < p.length) :
    (CPolyG.cclearDenomsCoreG p)[i]? = some (CPolyG.cmulG (CPolyG.qnumCoeffCoreG (p.getD i CField.zero))
      ((((p.map CPolyG.qdenCoeffCoreG).zipIdx).filter (fun de => decide (de.2 ≠ i))).foldl
        (fun acc de => CPolyG.cmulG acc de.1) [CField.one])) := by
  unfold CPolyG.cclearDenomsCoreG
  simp only
  rw [List.getElem?_map, List.getElem?_zipIdx, List.getElem?_eq_getElem hi]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

omit [CFieldSpec β] [CFieldDomain β] in
/-- `cclearDenomsCoreG` preserves the `t`-length: `(cclearDenomsCoreG p).length = p.length`. -/
theorem cclearDenomsCoreG_length (p : CPolyG (QFunNZG β)) :
    (CPolyG.cclearDenomsCoreG p).length = p.length := by
  unfold CPolyG.cclearDenomsCoreG; simp

/-- `toPolyG p` vanishes past the list length (the out-of-range coefficient is `CField.zero = 0`). -/
theorem toPolyG_coeff_eq_zero_of_length_leG (p : CPolyG (QFunNZG β)) {i : ℕ} (hi : p.length ≤ i) :
    (toPolyG p).coeff i = 0 := by
  rw [toPolyG_coeff, List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
  show CFieldSpec.toK (CField.zero : QFunNZG β) = 0
  rw [CFieldSpec.toK_zero]

/-- **Per-coefficient `cclearDenomsCoreG` identity**: `(toGBPolyG (cclearDenomsCoreG p)).coeff i =
amG (commonDenG p) · (toPolyG p).coeff i` — the cleared `i`-th coefficient `amG (numᵢ · ∏_{j≠i} denⱼ)`
equals the common-denominator scalar `amG (∏_j denⱼ)` times `amG numᵢ / amG denᵢ`. Generic mirror of
`toPolyB_clearDenoms_coeff`. -/
theorem toGBPolyG_cclearDenomsCoreG_coeff (p : CPolyG (QFunNZG β)) (i : ℕ) :
    (toGBPolyG (CPolyG.cclearDenomsCoreG p)).coeff i
      = QFunNZG.amG β (commonDenG p) * (toPolyG p).coeff i := by
  rcases lt_or_ge i p.length with hi | hi
  · rw [toGBPolyG, liftKG, Polynomial.coe_mapRingHom, Polynomial.coeff_map,
      GBPolyCore.toGBCoeffPoly_coeff, toPolyG_coeff,
      List.getD_eq_getElem?_getD, cclearDenomsCoreG_getElem p i hi, Option.getD_some]
    rw [CPolyG.toPolyG_cmulG, toPolyG_foldl_cmulG,
      show CPolyG.toPolyG ([CField.one] : CPolyG β) = 1 by
        rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_one, mul_zero, add_zero, map_one],
      one_mul]
    set dens := p.map CPolyG.qdenCoeffCoreG with hdens
    have hcd : commonDenG p = (dens.map CPolyG.toPolyG).prod := by rw [commonDenG, hdens]
    have hlen : i < dens.length := by rw [hdens, List.length_map]; exact hi
    have hfilt := filter_prod_mul (CPolyG.toPolyG) ([] : CPolyG β) dens 0 i (Nat.zero_le i)
      (by simpa using hlen)
    rw [Nat.sub_zero] at hfilt
    have hdeni : CPolyG.toPolyG (dens.getD i []) = CPolyG.toPolyG (CPolyG.qdenCoeffCoreG (p.getD i CField.zero)) := by
      congr 1
      rw [hdens, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hi]
      simp
    have hcoeff : (CFieldSpec.toK (p.getD i CField.zero) : RatFunc (CFieldSpec.K β))
        = QFunNZG.amG β (CPolyG.toPolyG (CPolyG.qnumCoeffCoreG (p.getD i CField.zero)))
          / QFunNZG.amG β (CPolyG.toPolyG (CPolyG.qdenCoeffCoreG (p.getD i CField.zero))) := by
      show QFunNZG.toQFunNZG (p.getD i CField.zero) = _
      rw [toQFunNZG_eq_div]
    have hden0 : QFunNZG.amG β (CPolyG.toPolyG (CPolyG.qdenCoeffCoreG (p.getD i CField.zero))) ≠ 0 :=
      QFunNZG.amG_toPolyG_ne_zero (toPolyG_qdenCoeffCoreG_ne_zero _)
    rw [hcoeff, hcd]
    have hpushP : QFunNZG.amG β (((dens.zipIdx.filter (fun de => decide (de.2 ≠ i))).map
        (fun de => CPolyG.toPolyG de.1)).prod)
        * QFunNZG.amG β (CPolyG.toPolyG (CPolyG.qdenCoeffCoreG (p.getD i CField.zero)))
        = QFunNZG.amG β ((dens.map CPolyG.toPolyG).prod) := by
      rw [← map_mul, ← hdeni, hfilt]
    rw [map_mul, mul_comm (QFunNZG.amG β ((dens.map CPolyG.toPolyG).prod)) _, div_mul_eq_mul_div,
      eq_div_iff hden0, mul_assoc, hpushP]
  · rw [toGBPolyG, liftKG, Polynomial.coe_mapRingHom, Polynomial.coeff_map,
      GBPolyCore.toGBCoeffPoly_coeff, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by rw [cclearDenomsCoreG_length]; exact hi), Option.getD_none,
      toPolyG_nil, map_zero, toPolyG_coeff_eq_zero_of_length_leG p hi, mul_zero]

/-- **The `cclearDenomsCoreG` bridge** (exact form): over the field β(s), the cleared polynomial
`toGBPolyG (cclearDenomsCoreG p)` is the common-denominator scalar `C (amG (commonDenG p))` times
`toPolyG p`. Generic mirror of `toPolyB_clearDenoms`. -/
theorem toGBPolyG_cclearDenomsCoreG (p : CPolyG (QFunNZG β)) :
    toGBPolyG (CPolyG.cclearDenomsCoreG p) = Polynomial.C (QFunNZG.amG β (commonDenG p)) * toPolyG p := by
  ext i
  rw [toGBPolyG_cclearDenomsCoreG_coeff, Polynomial.coeff_C_mul]

/-- **The `cclearDenomsCoreG` bridge** (`Associated` form): over the field β(s), the cleared `(β[s])[t]`
polynomial and `toPolyG p` are **associates** in `(RatFunc (CFieldSpec.K β))[X]` — they differ by the
unit `C (amG (commonDenG p))`. The fraction-clearing is a unit-scaling over the field, so it preserves
the gcd up to associates. Generic mirror of `associated_toPolyB_clearDenoms`. -/
theorem associated_toGBPolyG_cclearDenomsCoreG (p : CPolyG (QFunNZG β)) :
    Associated (toGBPolyG (CPolyG.cclearDenomsCoreG p)) (toPolyG p) := by
  rw [toGBPolyG_cclearDenomsCoreG]
  exact (associated_unit_mul_left _ _
    (Polynomial.isUnit_C.mpr (amG_commonDenG_ne_zero p).isUnit))

/-! ### The primitive PRS over the GCD-domain coefficient ring `R = β[s]`
The kernel `cprimPRSgcdGenCore cgcdB fuel P Q` runs a primitive polynomial-remainder sequence over the
coefficient ring `CPolyG β = β[s]`, stripping the content each step. Over the field `β(s) = Frac R`, each
step preserves the gcd up to associates: the pseudo-remainder is a Euclidean step up to a β(s)-unit (the
pseudo-division multiplier), and the content-strip `gbprimitivePartCore` divides out a β[s]-content that
is a β(s)-unit. The content/multiplier nonvanishing and the content-strip-is-unit facts enter as explicit
hypotheses (a `CPrimPRSGenAssocReg`-style bundle) — they hold on real PRS runs; this is the same gating as
`ComputableGcdCorrect.associated_toPolyB_primPRSgcd` (gated on `PrimPRSRegular`). -/

namespace GBPolyCore

variable {β : Type*} [CField β] [CFieldSpec β]

omit [CFieldSpec β] in
/-- `gbpsremainderCore` **normalizes its divisor**: `gbpsremainderCore fuel p q = gbpsremainderCore fuel p
(gbnormCore q)`. Mirror of `bpsremainder_bnorm_right`. -/
theorem gbpsremainderCore_gbnormCore_right (fuel : ℕ) (p q : GBPolyCore β) :
    gbpsremainderCore fuel p q = gbpsremainderCore fuel p (gbnormCore q) := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp only [gbpsremainderCore, gbnormCore_idemp]

/-- `toGBCoeffPoly [[CField.one]] = 1`: the `GBPolyCore` constant `1` (`[1] ∈ β[s]` as the single
`t`-coefficient). -/
@[simp] theorem toGBCoeffPoly_one : toGBCoeffPoly ([[CField.one]] : GBPolyCore β) = 1 := by
  rw [toGBCoeffPoly_cons, toGBCoeffPoly_nil, mul_zero, add_zero,
    show CPolyG.toPolyG ([CField.one] : CPolyG β) = 1 by
      rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_one, mul_zero, add_zero, map_one], map_one]

/-- **Pseudo-division identity through `toGBCoeffPoly`** (any fuel): there is a multiplier `c ∈ β[s]`
(a product of leading `t`-coefficients of `q`) and a quotient `s` with `C (toPolyG c) · toGBCoeffPoly p =
toGBCoeffPoly s · toGBCoeffPoly q + toGBCoeffPoly (gbpsremainderCore fuel p q)` in `R[t]`. The computable
pseudo-remainder realizes the honest `R[t]` pseudo-division relation `lc(q)ᵏ·p = s·q + prem` (the
existential matches the non-field coefficient ring `R = β[s]`). The generic mirror of
`ComputeCorrectness.toBPoly_bpsremainder`. -/
theorem toGBCoeffPoly_gbpsremainderCore (fuel : ℕ) (p q : GBPolyCore β) :
    ∃ (s : GBPolyCore β) (c : CPolyG β),
      Polynomial.C (CPolyG.toPolyG c) * toGBCoeffPoly p
        = toGBCoeffPoly s * toGBCoeffPoly q + toGBCoeffPoly (gbpsremainderCore fuel p q) := by
  have hone : CPolyG.toPolyG ([CField.one] : CPolyG β) = 1 := by
    rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_one, mul_zero, add_zero, map_one]
  induction fuel generalizing p with
  | zero => exact ⟨[], [CField.one], by simp [gbpsremainderCore, toGBCoeffPoly_gbnormCore, hone]⟩
  | succ fuel ih =>
    simp only [gbpsremainderCore]
    split_ifs with hq hlen
    · exact ⟨[], [CField.one], by simp [toGBCoeffPoly_gbnormCore, hone]⟩
    · exact ⟨[], [CField.one], by simp [toGBCoeffPoly_gbnormCore, hone]⟩
    · obtain ⟨s', c', hsc⟩ := ih (gbnormCore (gbsubCore (gbscaleCCore (gblcCore (gbnormCore q)) (gbnormCore p))
        (gbscaleCCore (gblcCore (gbnormCore p))
          (gbshiftCore ((gbnormCore p).length - (gbnormCore q).length) (gbnormCore q)))))
      have hp' : toGBCoeffPoly (gbnormCore (gbsubCore (gbscaleCCore (gblcCore (gbnormCore q)) (gbnormCore p))
          (gbscaleCCore (gblcCore (gbnormCore p))
            (gbshiftCore ((gbnormCore p).length - (gbnormCore q).length) (gbnormCore q)))))
          = Polynomial.C (CPolyG.toPolyG (gblcCore (gbnormCore q))) * toGBCoeffPoly p
            - Polynomial.C (CPolyG.toPolyG (gblcCore (gbnormCore p)))
              * Polynomial.X ^ ((gbnormCore p).length - (gbnormCore q).length) * toGBCoeffPoly q := by
        rw [toGBCoeffPoly_gbnormCore, toGBCoeffPoly_gbsubCore, toGBCoeffPoly_gbscaleCCore,
          toGBCoeffPoly_gbscaleCCore, toGBCoeffPoly_gbshiftCore, toGBCoeffPoly_gbnormCore,
          toGBCoeffPoly_gbnormCore]
        ring
      rw [hp', gbpsremainderCore_gbnormCore_right] at hsc
      refine ⟨gbaddCore s' (gbscaleCCore (CPolyG.cmulG c' (gblcCore (gbnormCore p)))
          (gbshiftCore ((gbnormCore p).length - (gbnormCore q).length) [[CField.one]])),
          CPolyG.cmulG c' (gblcCore (gbnormCore q)), ?_⟩
      rw [toGBCoeffPoly_gbaddCore, toGBCoeffPoly_gbscaleCCore, toGBCoeffPoly_gbshiftCore,
        toGBCoeffPoly_one, CPolyG.toPolyG_cmulG, map_mul, CPolyG.toPolyG_cmulG, map_mul]
      linear_combination hsc

end GBPolyCore

open GBPolyCore

omit [CFieldDomain β] in
/-- **`gbpsremainderCore` lifts to a β(s)[t] Euclidean relation**: there is a quotient `s` and a
multiplier `c ∈ β[s]` with `C (amG (toPolyG c)) · toGBPolyG p = toGBPolyG s · toGBPolyG q +
toGBPolyG (gbpsremainderCore fuel p q)` in `(RatFunc (CFieldSpec.K β))[X]` — the lift of
`toGBCoeffPoly_gbpsremainderCore` through the field embedding `amG`. Generic mirror of
`toPolyB_bpsremainder`. -/
theorem toGBPolyG_gbpsremainderCore (fuel : ℕ) (p q : GBPolyCore β) :
    ∃ (s : GBPolyCore β) (c : CPolyG β),
      Polynomial.C (QFunNZG.amG β (CPolyG.toPolyG c)) * toGBPolyG p
        = toGBPolyG s * toGBPolyG q + toGBPolyG (gbpsremainderCore fuel p q) := by
  obtain ⟨s, c, hsc⟩ := toGBCoeffPoly_gbpsremainderCore fuel p q
  refine ⟨s, c, ?_⟩
  have hl := congrArg (liftKG β) hsc
  simp only [map_add, map_mul] at hl
  rw [liftKG_C] at hl
  simpa [toGBPolyG] using hl

omit [CFieldDomain β] in
/-- **`toGBPolyG` ignores normalization**: `toGBPolyG (gbnormCore p) = toGBPolyG p`. -/
@[simp] theorem toGBPolyG_gbnormCore (p : GBPolyCore β) :
    toGBPolyG (gbnormCore p) = toGBPolyG p := by
  rw [toGBPolyG, toGBCoeffPoly_gbnormCore, ← toGBPolyG]

omit [CFieldDomain β] in
/-- `toGBPolyG p = 0 ↔ toGBCoeffPoly p = 0` (the lift is injective, `amG` injective on coefficients). -/
theorem toGBPolyG_eq_zero_iff (p : GBPolyCore β) : toGBPolyG p = 0 ↔ toGBCoeffPoly p = 0 := by
  rw [toGBPolyG, liftKG, ← Polynomial.map_zero (QFunNZG.amG β)]
  exact Polynomial.map_injective (QFunNZG.amG β) (RatFunc.algebraMap_injective (CFieldSpec.K β)) |>.eq_iff

omit [CFieldDomain β] in
/-- `toGBPolyG p = 0 ↔ gbisZeroCore p = true`. -/
theorem toGBPolyG_eq_zero_iff_gbisZeroCore (p : GBPolyCore β) :
    toGBPolyG p = 0 ↔ gbisZeroCore p = true := by
  rw [toGBPolyG_eq_zero_iff, gbisZeroCore_iff_toGBCoeffPoly]

/-! ### Step 2 — the primitive-PRS gcd invariant over β(s)
Over the field β(s) = `RatFunc (CFieldSpec.K β)`, each `cprimPRSgcdGenCore` step preserves
`gcd (toGBPolyG ·) (toGBPolyG ·)` up to associates: a pseudo-remainder step is a Euclidean step up to a
β(s)-unit content factor (the pseudo-division multiplier), and `gbprimitivePartCore` divides out a
β[s]-content that is a β(s)-unit. The content/multiplier nonvanishing and the content-strip-is-unit facts
enter as explicit hypotheses (the `CPrimPRSGenAssocReg` bundle) — these hold for real PRS runs; proving
them unconditionally is the content-gcd theory left to the call site (and is the TOWER INDUCTION: the
content-strip-is-unit at level `β` follows from the gcd-correctness of `cgcdB = cgcdFFRawCore` at level
`β`). This is the same gating shape as `ComputableGcdCorrect.PrimPRSRegular`. -/

omit [CFieldDomain β] in
/-- **gcd is invariant under an associated right argument** in `(RatFunc (CFieldSpec.K β))[X]`. -/
theorem associated_gcd_right_gbpolyG {A B B' : (RatFunc (CFieldSpec.K β))[X]} (h : Associated B B') :
    Associated (gcd A B) (gcd A B') :=
  associated_gcd_right_field h

/-- **Per-run regularity of the primitive PRS** `CPrimPRSGenAssocReg cgcdB fuel P Q`: the inductive
predicate collecting exactly what the `gcd` invariant of each `cprimPRSgcdGenCore` step needs — (i) the
recursion reaches `gbisZeroCore Q = true` (termination), and at every non-terminal step (with `Pn =
gbnormCore P`, `Qn = gbnormCore Q`, `prem = gbpsremainderCore 60 Pn Qn`, `r = gbprimitivePartCore 30 cgcdB
prem`): (ii) a pseudo-division witness `(s, c)` with `C (amG (toPolyG c)) · toGBPolyG Pn = toGBPolyG s ·
toGBPolyG Qn + toGBPolyG prem` and the multiplier `amG (toPolyG c)` a β(s)-unit (`≠ 0`), and (iii)
`gbprimitivePartCore` is a β(s)-unit scaling (`Associated (toGBPolyG r) (toGBPolyG prem)`). These hold for
honest PRS runs; proving them unconditionally is the content-gcd theory deferred to the call site. The
generic mirror of `ComputableGcdCorrect.PrimPRSRegular`. -/
def CPrimPRSGenAssocReg (cgcdB : CPolyG β → CPolyG β → CPolyG β) :
    ℕ → GBPolyCore β → GBPolyCore β → Prop
  | 0, P, Q =>
    gbisZeroCore Q = true ∧
      Associated (toGBPolyG (GBPolyCore.gbprimitivePartCore 30 cgcdB P)) (toGBPolyG P)
  | fuel + 1, P, Q =>
    (gbisZeroCore (GBPolyCore.gbnormCore Q) = true ∧
      Associated (toGBPolyG (GBPolyCore.gbprimitivePartCore 30 cgcdB (GBPolyCore.gbnormCore P)))
        (toGBPolyG P)) ∨
      (¬ gbisZeroCore (GBPolyCore.gbnormCore Q) = true ∧
        (∃ (s : GBPolyCore β) (c : CPolyG β),
          Polynomial.C (QFunNZG.amG β (CPolyG.toPolyG c)) * toGBPolyG (GBPolyCore.gbnormCore P)
            = toGBPolyG s * toGBPolyG (GBPolyCore.gbnormCore Q)
              + toGBPolyG (GBPolyCore.gbpsremainderCore 60 (GBPolyCore.gbnormCore P)
                  (GBPolyCore.gbnormCore Q))
          ∧ QFunNZG.amG β (CPolyG.toPolyG c) ≠ 0) ∧
        Associated (toGBPolyG (GBPolyCore.gbprimitivePartCore 30 cgcdB
            (GBPolyCore.gbpsremainderCore 60 (GBPolyCore.gbnormCore P) (GBPolyCore.gbnormCore Q))))
          (toGBPolyG (GBPolyCore.gbpsremainderCore 60 (GBPolyCore.gbnormCore P)
              (GBPolyCore.gbnormCore Q))) ∧
        CPrimPRSGenAssocReg cgcdB fuel (GBPolyCore.gbnormCore Q)
          (GBPolyCore.gbprimitivePartCore 30 cgcdB
            (GBPolyCore.gbpsremainderCore 60 (GBPolyCore.gbnormCore P) (GBPolyCore.gbnormCore Q))))

omit [CFieldDomain β] in
/-- **Step 2 — the primitive-PRS gcd invariant** (the crux): for a regular run
(`CPrimPRSGenAssocReg cgcdB fuel P Q`), the last nonzero primitive remainder
`cprimPRSgcdGenCore cgcdB fuel P Q` is, over the field β(s), **associated to the polynomial gcd** of the
inputs: `Associated (toGBPolyG (cprimPRSgcdGenCore cgcdB fuel P Q)) (gcd (toGBPolyG P) (toGBPolyG Q))` in
`(RatFunc (CFieldSpec.K β))[X]`. The classic Euclidean invariant `gcd(P,Q) ~ gcd(Q, prem(P,Q))` carried
along the primitive PRS, bottoming at `gcd(P, 0) ~ P`. Generic mirror of
`associated_toPolyB_primPRSgcd`. -/
theorem associated_toGBPolyG_cprimPRSgcdGenCore (cgcdB : CPolyG β → CPolyG β → CPolyG β) :
    ∀ (fuel : ℕ) (P Q : GBPolyCore β), CPrimPRSGenAssocReg cgcdB fuel P Q →
      Associated (toGBPolyG (cprimPRSgcdGenCore cgcdB fuel P Q))
        (gcd (toGBPolyG P) (toGBPolyG Q)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro P Q hreg
    obtain ⟨hQ, hprim⟩ := hreg
    have hQ0 : toGBPolyG Q = 0 := (toGBPolyG_eq_zero_iff_gbisZeroCore Q).mpr hQ
    show Associated (toGBPolyG (GBPolyCore.gbprimitivePartCore 30 cgcdB P))
      (gcd (toGBPolyG P) (toGBPolyG Q))
    rw [hQ0]
    exact hprim.trans (gcd_zero_right' (toGBPolyG P)).symm
  | succ fuel ih =>
    intro P Q hreg
    show Associated (toGBPolyG (
        let P := GBPolyCore.gbnormCore P; let Q := GBPolyCore.gbnormCore Q;
        if GBPolyCore.gbisZeroCore Q then GBPolyCore.gbprimitivePartCore 30 cgcdB P
        else cprimPRSgcdGenCore cgcdB fuel Q
          (GBPolyCore.gbprimitivePartCore 30 cgcdB (GBPolyCore.gbpsremainderCore 60 P Q))))
      (gcd (toGBPolyG P) (toGBPolyG Q))
    simp only
    by_cases hQ : GBPolyCore.gbisZeroCore (GBPolyCore.gbnormCore Q) = true
    · rw [if_pos hQ]
      rw [CPrimPRSGenAssocReg] at hreg
      rcases hreg with ⟨_, hprim⟩ | ⟨hne, _⟩
      · have hQ0 : toGBPolyG Q = 0 := by
          rw [← toGBPolyG_gbnormCore]; exact (toGBPolyG_eq_zero_iff_gbisZeroCore _).mpr hQ
        rw [hQ0]
        exact hprim.trans (gcd_zero_right' (toGBPolyG P)).symm
      · exact absurd hQ hne
    · rw [if_neg hQ]
      rw [CPrimPRSGenAssocReg] at hreg
      rcases hreg with ⟨h, _⟩ | ⟨_, ⟨s, c, hrel, hc0⟩, hassoc, hrec⟩
      · exact absurd h hQ
      set Pn := GBPolyCore.gbnormCore P with hPn
      set Qn := GBPolyCore.gbnormCore Q with hQn
      set prem := GBPolyCore.gbpsremainderCore 60 Pn Qn with hprem
      set r := GBPolyCore.gbprimitivePartCore 30 cgcdB prem with hr
      have hih := ih Qn r hrec
      have hstep : Associated (gcd (toGBPolyG Pn) (toGBPolyG Qn))
          (gcd (toGBPolyG Qn) (toGBPolyG r)) := by
        have heuc : Associated (gcd (toGBPolyG Pn) (toGBPolyG Qn))
            (gcd (toGBPolyG Qn) (toGBPolyG prem)) :=
          associated_gcd_euclid_step_field (A := toGBPolyG Pn) (B := toGBPolyG Qn)
            (R := toGBPolyG prem) (S := toGBPolyG s)
            (Polynomial.isUnit_C.mpr hc0.isUnit) (by linear_combination hrel)
        exact heuc.trans (associated_gcd_right_gbpolyG hassoc.symm)
      rw [show toGBPolyG P = toGBPolyG Pn by rw [hPn, toGBPolyG_gbnormCore],
        show toGBPolyG Q = toGBPolyG Qn by rw [hQn, toGBPolyG_gbnormCore]]
      exact hih.trans hstep.symm

/-! ### Discharging clause (iii) — the content strip is a β(s)-unit scaling
The content strip `gbprimitivePartCore 30 cgcdB prem` divides every `t`-coefficient by the content
`g = gbcontentCore cgcdB prem` via `cdivG`. When the content divides every coefficient (in `R = β[s]`,
which on a real run follows from the gcd-correctness of `cgcdB = cgcdFFRawCore β` — the TOWER INDUCTION),
the division is exact and `gbprimitivePartCore` is multiplication by the β(s)-unit `1/g`. We discharge
clause (iii) from the content-divides-coefficients hypothesis (the Mathlib-content / inductive half),
mirroring `ComputableGcdCorrect.associated_toPolyB_bprimitivePartX`. -/

namespace GBPolyCore

variable {β : Type*} [CField β] [CFieldSpec β]

omit [CFieldSpec β] in
/-- The `t`-content `gbcontentCore cgcdB p` is invariant under `gbnormCore`:
`gbcontentCore cgcdB (gbnormCore p) = gbcontentCore cgcdB p`. -/
theorem gbcontentCore_gbnormCore (cgcdB : CPolyG β → CPolyG β → CPolyG β) (p : GBPolyCore β) :
    gbcontentCore cgcdB (gbnormCore p) = gbcontentCore cgcdB p := by
  rw [gbcontentCore, gbcontentCore, gbnormCore_idemp]

/-- **`toGBCoeffPoly` of a coefficient-wise exact division**: if dividing every `t`-coefficient `a` of `p`
by the `β[s]` content `g` is exact (`toPolyG g ∣ toPolyG a`, fuel-bounded), then
`C(toPolyG g) · toGBCoeffPoly (p.map (cdivG fuel · g)) = toGBCoeffPoly p` — the content `C(toPolyG g)`
factors back out of the divided `t`-coefficient list. Generic mirror of
`SubresultantCorrectness.toBPoly_map_cdiv_exact`. -/
theorem toGBCoeffPoly_map_cdivG_exact (fuel : ℕ) (p : GBPolyCore β) (g : CPolyG β)
    (hg : CPolyG.cnormG g ≠ []) (hfuel : ∀ a ∈ p, (CPolyG.cnormG a : List β).length ≤ fuel)
    (hdvd : ∀ a ∈ p, CPolyG.toPolyG g ∣ CPolyG.toPolyG a) :
    Polynomial.C (CPolyG.toPolyG g) * toGBCoeffPoly (p.map (fun a => CPolyG.cdivG fuel a g))
      = toGBCoeffPoly p := by
  induction p with
  | nil => simp
  | cons a as ih =>
    have has := ih (fun b hb => hfuel b (by simp [hb])) (fun b hb => hdvd b (by simp [hb]))
    have ha : CPolyG.toPolyG a = CPolyG.toPolyG (CPolyG.cdivG fuel a g) * CPolyG.toPolyG g :=
      (toPolyG_cdivG_exact fuel a g hg (hfuel a (by simp)) (hdvd a (by simp))).symm
    rw [List.map_cons, toGBCoeffPoly_cons, toGBCoeffPoly_cons, ha, map_mul]
    linear_combination Polynomial.X * has

end GBPolyCore

open GBPolyCore

omit [CFieldDomain β] in
/-- **`gbprimitivePartCore` realizes exact `β[s]`-content division through `toGBCoeffPoly`**: when the
content `g = gbcontentCore cgcdB p` is nonzero (`hg`) and divides every `t`-coefficient of `gbnormCore p`
exactly, `C(toPolyG g) · toGBCoeffPoly (gbprimitivePartCore fuel cgcdB p) = toGBCoeffPoly p`. Generic
mirror of `toBPoly_bprimitivePartX_exact`. -/
theorem toGBCoeffPoly_gbprimitivePartCore_exact (fuel : ℕ)
    (cgcdB : CPolyG β → CPolyG β → CPolyG β) (p : GBPolyCore β)
    (hg : ¬ CPolyG.cisZeroG (gbcontentCore cgcdB p) = true)
    (hgcn : CPolyG.cnormG (gbcontentCore cgcdB p) ≠ [])
    (hfuel : ∀ a ∈ gbnormCore p, (CPolyG.cnormG a : List β).length ≤ fuel)
    (hdvd : ∀ a ∈ gbnormCore p, CPolyG.toPolyG (gbcontentCore cgcdB p) ∣ CPolyG.toPolyG a) :
    Polynomial.C (CPolyG.toPolyG (gbcontentCore cgcdB p))
        * GBPolyCore.toGBCoeffPoly (gbprimitivePartCore fuel cgcdB p)
      = GBPolyCore.toGBCoeffPoly p := by
  rw [gbprimitivePartCore]
  simp only [gbcontentCore_gbnormCore, hg, Bool.false_eq_true, if_false]
  rw [toGBCoeffPoly_gbnormCore, toGBCoeffPoly_map_cdivG_exact fuel (gbnormCore p)
    (gbcontentCore cgcdB p) hgcn hfuel hdvd, toGBCoeffPoly_gbnormCore]

omit [CFieldDomain β] in
/-- **Clause (iii) discharged — `gbprimitivePartCore` is a β(s)-unit scaling** (the Mathlib-content half):
under the content-nonzero and content-divides-each-coefficient hypotheses (with `toPolyG g ≠ 0`),
`Associated (toGBPolyG (gbprimitivePartCore fuel cgcdB p)) (toGBPolyG p)` over β(s) — stripping the
`β[s]`-content is a β(s)-unit scaling, preserving the gcd up to associates. The content-divides
hypotheses hold on a real run by the gcd-correctness of `cgcdB = cgcdFFRawCore β` (the TOWER INDUCTION).
Generic mirror of `associated_toPolyB_bprimitivePartX`. -/
theorem associated_toGBPolyG_gbprimitivePartCore (fuel : ℕ)
    (cgcdB : CPolyG β → CPolyG β → CPolyG β) (p : GBPolyCore β)
    (hg : ¬ CPolyG.cisZeroG (gbcontentCore cgcdB p) = true)
    (hgcn : CPolyG.cnormG (gbcontentCore cgcdB p) ≠ [])
    (hg0 : CPolyG.toPolyG (gbcontentCore cgcdB p) ≠ 0)
    (hfuel : ∀ a ∈ gbnormCore p, (CPolyG.cnormG a : List β).length ≤ fuel)
    (hdvd : ∀ a ∈ gbnormCore p, CPolyG.toPolyG (gbcontentCore cgcdB p) ∣ CPolyG.toPolyG a) :
    Associated (toGBPolyG (gbprimitivePartCore fuel cgcdB p)) (toGBPolyG p) := by
  -- lift the toGBCoeffPoly-exact identity through liftKG to a C(amG g)-scaling on toGBPolyG
  have hexact := toGBCoeffPoly_gbprimitivePartCore_exact fuel cgcdB p hg hgcn hfuel hdvd
  have hl := congrArg (liftKG β) hexact
  rw [map_mul, liftKG_C] at hl
  -- hl : C (amG (toPolyG g)) * toGBPolyG (gbprimitivePartCore …) = toGBPolyG p
  have hl' : Polynomial.C (QFunNZG.amG β (CPolyG.toPolyG (gbcontentCore cgcdB p)))
      * toGBPolyG (gbprimitivePartCore fuel cgcdB p) = toGBPolyG p := by
    simpa [toGBPolyG] using hl
  refine ⟨(Polynomial.isUnit_C.mpr (QFunNZG.amG_toPolyG_ne_zero hg0).isUnit).unit, ?_⟩
  rw [← hl']
  show toGBPolyG (gbprimitivePartCore fuel cgcdB p)
      * Polynomial.C (QFunNZG.amG β (CPolyG.toPolyG (gbcontentCore cgcdB p)))
    = Polynomial.C (QFunNZG.amG β (CPolyG.toPolyG (gbcontentCore cgcdB p)))
      * toGBPolyG (gbprimitivePartCore fuel cgcdB p)
  ring

/-! ### The content-gcd divides every coefficient — from `cgcdB`'s gcd-correctness (the tower link)
The content `gbcontentCore cgcdB p` folds the content-gcd `cgcdB` over the `t`-coefficients. When `cgcdB`
computes the gcd up to associates in `R = β[s]` (`CgcdBCorrect` — on a real run this is the
gcd-correctness of `cgcdFFRawCore` at level `β`, the tower induction hypothesis), the running fold
**divides each coefficient** in `R`. This is the divisibility clause (iii) needs, now reduced to the
level-`β` gcd-correctness. Generic mirror of `ComputableGcdCorrect.toPoly_foldl_cgcdExt_dvd`. -/

/-- **The content-gcd `cgcdB` is gcd-correct** `CgcdBCorrect cgcdB`: for all `a b ∈ β[s]`,
`toPolyG (cgcdB a b)` is `Associated` to `gcd (toPolyG a) (toPolyG b)` in `R = (CFieldSpec.K β)[X]`. On a
real tower run this is supplied by `associated_toPolyG_cgcdFFRawCore` at level `β` (the recursion). -/
def CgcdBCorrect {β : Type*} [CField β] [CFieldSpec β] (cgcdB : CPolyG β → CPolyG β → CPolyG β) : Prop :=
  ∀ a b : CPolyG β, Associated (CPolyG.toPolyG (cgcdB a b))
    (gcd (CPolyG.toPolyG a) (CPolyG.toPolyG b))

variable {β : Type*} [CField β] [CFieldSpec β]

/-- **The content `cgcdB`-fold divides each input** (over `R = β[s]`): for the running content
`g = l.foldl (fun g c => cgcdB g c) acc`, under `CgcdBCorrect cgcdB`, `toPolyG g` divides `toPolyG acc`
and `toPolyG a` for every `a ∈ l`. Each step's gcd (up to associates) divides the previous accumulator
and the new coefficient; divisibility transports through the fold. Generic mirror of
`ComputableGcdCorrect.toPoly_foldl_cgcdExt_dvd`. -/
theorem toPolyG_foldl_cgcdB_dvd (cgcdB : CPolyG β → CPolyG β → CPolyG β) (hcorr : CgcdBCorrect cgcdB) :
    ∀ (acc : CPolyG β) (l : List (CPolyG β)),
      CPolyG.toPolyG (l.foldl (fun g c => cgcdB g c) acc) ∣ CPolyG.toPolyG acc ∧
        ∀ a ∈ l, CPolyG.toPolyG (l.foldl (fun g c => cgcdB g c) acc) ∣ CPolyG.toPolyG a := by
  intro acc l
  induction l generalizing acc with
  | nil => exact ⟨dvd_refl _, by simp⟩
  | cons c l ih =>
    set g₁ := cgcdB acc c with hg₁
    -- the step gcd divides the previous accumulator and the new coefficient (up to associates)
    have hcorr1 := hcorr acc c
    have hg₁acc : CPolyG.toPolyG g₁ ∣ CPolyG.toPolyG acc :=
      hcorr1.dvd.trans (gcd_dvd_left _ _)
    have hg₁c : CPolyG.toPolyG g₁ ∣ CPolyG.toPolyG c :=
      hcorr1.dvd.trans (gcd_dvd_right _ _)
    obtain ⟨hfg₁, hfmem⟩ := ih g₁
    have hfold : (c :: l).foldl (fun g c => cgcdB g c) acc
        = l.foldl (fun g c => cgcdB g c) g₁ := by rw [List.foldl_cons]
    rw [hfold]
    refine ⟨hfg₁.trans hg₁acc, ?_⟩
    intro a ha
    rcases List.mem_cons.mp ha with rfl | hl
    · exact hfg₁.trans hg₁c
    · exact hfmem a hl

/-- **The content divides each `t`-coefficient** of `gbnormCore p` (over `R = β[s]`): under
`CgcdBCorrect cgcdB`, `toPolyG (gbcontentCore cgcdB p) ∣ toPolyG a` for every `a ∈ gbnormCore p`. The
`[]`-seeded specialization of `toPolyG_foldl_cgcdB_dvd`. This is the content-divides hypothesis clause
(iii) needs, supplied entirely by the level-`β` gcd-correctness. -/
theorem toPolyG_gbcontentCore_dvd_mem (cgcdB : CPolyG β → CPolyG β → CPolyG β)
    (hcorr : CgcdBCorrect cgcdB) (p : GBPolyCore β) :
    ∀ a ∈ GBPolyCore.gbnormCore p, CPolyG.toPolyG (GBPolyCore.gbcontentCore cgcdB p) ∣ CPolyG.toPolyG a := by
  have hbc : GBPolyCore.gbcontentCore cgcdB p
      = (GBPolyCore.gbnormCore p).foldl (fun g c => cgcdB g c) [] := rfl
  rw [hbc]
  exact (toPolyG_foldl_cgcdB_dvd cgcdB hcorr [] (GBPolyCore.gbnormCore p)).2

/-- **Clause (iii) discharged from `cgcdB`-correctness alone** (the tower-induction packaging): under
`CgcdBCorrect cgcdB` (the level-`β` gcd-correctness), content-nonzero, and a per-coefficient fuel bound,
`gbprimitivePartCore fuel cgcdB p` is a β(s)-unit scaling (`Associated (toGBPolyG (gbprimitivePartCore
fuel cgcdB p)) (toGBPolyG p)`) — the content-divides hypotheses of
`associated_toGBPolyG_gbprimitivePartCore` are now *theorems* via `toPolyG_gbcontentCore_dvd_mem`. So
clause (iii) of `CPrimPRSGenAssocReg` needs only the recursion's gcd-correctness plus transparent
algorithmics, no separate content assumption. -/
theorem associated_toGBPolyG_gbprimitivePartCore_of_correct (fuel : ℕ)
    (cgcdB : CPolyG β → CPolyG β → CPolyG β) (hcorr : CgcdBCorrect cgcdB) (p : GBPolyCore β)
    (hg : ¬ CPolyG.cisZeroG (GBPolyCore.gbcontentCore cgcdB p) = true)
    (hgcn : CPolyG.cnormG (GBPolyCore.gbcontentCore cgcdB p) ≠ [])
    (hg0 : CPolyG.toPolyG (GBPolyCore.gbcontentCore cgcdB p) ≠ 0)
    (hfuel : ∀ a ∈ GBPolyCore.gbnormCore p, (CPolyG.cnormG a : List β).length ≤ fuel) :
    Associated (toGBPolyG (GBPolyCore.gbprimitivePartCore fuel cgcdB p)) (toGBPolyG p) :=
  associated_toGBPolyG_gbprimitivePartCore fuel cgcdB p hg hgcn hg0 hfuel
    (toPolyG_gbcontentCore_dvd_mem cgcdB hcorr p)

/-! ### Step 3 — the recursive `cgcdFFRawCore` capstone (the deliverable)
`cgcdFFRawCore fuel p q = liftGBPolyCoreG (cprimPRSgcdGenCore (cgcdFFRawCore β) fuel P Q)` with `(P, Q)`
the `gbdegCore`-ordered pair of `cclearDenomsCoreG p`, `cclearDenomsCoreG q`. Reading the result through
`toPolyG`, the lift-back is exact (`toPolyG_liftGBPolyCoreG`), the primitive-PRS invariant (step 2) plus
the `cclearDenomsCoreG` bridge (step 1) combine — over the field β(s) — to the polynomial gcd of the
inputs. This is the *raw* gcd (no `cmonicG`); the public monic `cgcdFFCore = cmonicG ∘ cgcdFFRawCore`
reads through `associated_toPolyG_cmonicG`. The generic mirror of `associated_toPolyG_cgcdFF`, at the
recursive tower instance `instCFracGcdCoreQFunNZG`. -/

section
variable [CFracGcdCore β]

/-- **Step 3 — abstract correctness of the recursive `cgcdFFRawCore` over β(s)[t]** (under a regular
run): over the field β(s) = `RatFunc (CFieldSpec.K β)`, the raw fraction-free gcd
`cgcdFFRawCore fuel p q` (`instCFracGcdCoreQFunNZG`, with content-gcd `CFracGcdCore.cgcdFFRawCore` at
level `β`) computes the polynomial gcd of the inputs — `toPolyG (cgcdFFRawCore fuel p q)` is `Associated`
to `gcd (toPolyG p) (toPolyG q)` in `(CFieldSpec.K (QFunNZG β))[X] = (RatFunc (CFieldSpec.K β))[X]`. The
`CPrimPRSGenAssocReg` hypothesis is on the `gbdegCore`-ordered cleared pair (the same ordering the instance
uses) with content-gcd `CFracGcdCore.cgcdFFRawCore fuel`; it captures the per-step content-exactness of
the primitive PRS, which on real runs follows from the gcd-correctness of `cgcdFFRawCore` at level `β`
(the tower induction). Generic mirror of `associated_toPolyG_cgcdFF`. -/
theorem associated_toPolyG_cgcdFFRawCore (fuel : ℕ) (p q : CPolyG (QFunNZG β))
    (hreg : CPrimPRSGenAssocReg (CFracGcdCore.cgcdFFRawCore fuel) fuel
      (if GBPolyCore.gbdegCore (CPolyG.cclearDenomsCoreG p)
          < GBPolyCore.gbdegCore (CPolyG.cclearDenomsCoreG q)
        then CPolyG.cclearDenomsCoreG q else CPolyG.cclearDenomsCoreG p)
      (if GBPolyCore.gbdegCore (CPolyG.cclearDenomsCoreG p)
          < GBPolyCore.gbdegCore (CPolyG.cclearDenomsCoreG q)
        then CPolyG.cclearDenomsCoreG p else CPolyG.cclearDenomsCoreG q)) :
    Associated (toPolyG (CFracGcdCore.cgcdFFRawCore fuel p q))
      (gcd (toPolyG p) (toPolyG q)) := by
  -- the engine output, with the cleared pair lifted back through liftGBPolyCoreG
  have key : ∀ P Q : GBPolyCore β, CPrimPRSGenAssocReg (CFracGcdCore.cgcdFFRawCore fuel) fuel P Q →
      Associated (gcd (toGBPolyG P) (toGBPolyG Q)) (gcd (toPolyG p) (toPolyG q)) →
      Associated (toPolyG (CPolyG.liftGBPolyCoreG
          (cprimPRSgcdGenCore (CFracGcdCore.cgcdFFRawCore fuel) fuel P Q)))
        (gcd (toPolyG p) (toPolyG q)) := by
    intro P Q hr hgcd
    rw [toPolyG_liftGBPolyCoreG]
    exact (associated_toGBPolyG_cprimPRSgcdGenCore (CFracGcdCore.cgcdFFRawCore fuel) fuel P Q hr).trans
      hgcd
  have hbridge : Associated (gcd (toGBPolyG (CPolyG.cclearDenomsCoreG p))
      (toGBPolyG (CPolyG.cclearDenomsCoreG q))) (gcd (toPolyG p) (toPolyG q)) :=
    (associated_toGBPolyG_cclearDenomsCoreG p).gcd (associated_toGBPolyG_cclearDenomsCoreG q)
  -- unfold the instance: cgcdFFRawCore = liftGBPolyCoreG (cprimPRSgcdGenCore … P Q) with the deg-order
  show Associated (toPolyG (
      let P := CPolyG.cclearDenomsCoreG p
      let Q := CPolyG.cclearDenomsCoreG q
      let (P, Q) := if GBPolyCore.gbdegCore P < GBPolyCore.gbdegCore Q then (Q, P) else (P, Q)
      CPolyG.liftGBPolyCoreG (cprimPRSgcdGenCore (CFracGcdCore.cgcdFFRawCore fuel) fuel P Q)))
    (gcd (toPolyG p) (toPolyG q))
  simp only
  by_cases hlt : GBPolyCore.gbdegCore (CPolyG.cclearDenomsCoreG p)
      < GBPolyCore.gbdegCore (CPolyG.cclearDenomsCoreG q)
  · simp only [if_pos hlt] at hreg ⊢
    refine key _ _ hreg ?_
    rw [gcd_comm]; exact hbridge
  · simp only [if_neg hlt] at hreg ⊢
    exact key _ _ hreg hbridge

/-- **The public monic `cgcdFFCore` correct over β(s)[t]** (under a regular run): the public monic
fraction-free gcd `cgcdFFCore fuel p q = cmonicG (cgcdFFRawCore fuel p q)` reads through `toPolyG` to the
polynomial gcd up to associates — composing the raw correctness `associated_toPolyG_cgcdFFRawCore` with
the monic unit-scaling `associated_toPolyG_cmonicG`. So the generic flat gcd the engine actually calls
(`cgcdFFCore`) is the abstract gcd up to associates, with NO `cgcdFF` bridge. -/
theorem associated_toPolyG_cgcdFFCore (fuel : ℕ) (p q : CPolyG (QFunNZG β))
    (hreg : CPrimPRSGenAssocReg (CFracGcdCore.cgcdFFRawCore fuel) fuel
      (if GBPolyCore.gbdegCore (CPolyG.cclearDenomsCoreG p)
          < GBPolyCore.gbdegCore (CPolyG.cclearDenomsCoreG q)
        then CPolyG.cclearDenomsCoreG q else CPolyG.cclearDenomsCoreG p)
      (if GBPolyCore.gbdegCore (CPolyG.cclearDenomsCoreG p)
          < GBPolyCore.gbdegCore (CPolyG.cclearDenomsCoreG q)
        then CPolyG.cclearDenomsCoreG p else CPolyG.cclearDenomsCoreG q)) :
    Associated (toPolyG (CFracGcdCore.cgcdFFCore fuel p q)) (gcd (toPolyG p) (toPolyG q)) := by
  rw [CFracGcdCore.cgcdFFCore]
  exact (associated_toPolyG_cmonicG _).trans (associated_toPolyG_cgcdFFRawCore fuel p q hreg)

end

/-! ### Restatements against the intended wording (anonymous `example`s) -/

-- The base case: the raw generic Euclidean gcd computes the abstract gcd up to associates (under
-- termination), over ANY tower level — the bottom of the tower (α = ℚ, cgcdFFRawCore = (cgcdExtG _).1)
-- and the content-gcd at any level both read through this.
example {α : Type*} [CField α] [CFieldSpec α] (fuel : ℕ) (a b : CPolyG α)
    (hterm : cgcdTerminatesG fuel a b) :
    Associated (toPolyG (cgcdExtG fuel a b).1) (gcd (toPolyG a) (toPolyG b)) :=
  associated_toPolyG_cgcdExtG fuel a b hterm

-- The crux: under a regular PRS run, the generic primitive PRS computes the gcd up to associates over
-- β(s) = RatFunc (CFieldSpec.K β).
example (cgcdB : CPolyG β → CPolyG β → CPolyG β) (fuel : ℕ) (P Q : GBPolyCore β)
    (hreg : CPrimPRSGenAssocReg cgcdB fuel P Q) :
    Associated (toGBPolyG (cprimPRSgcdGenCore cgcdB fuel P Q)) (gcd (toGBPolyG P) (toGBPolyG Q)) :=
  associated_toGBPolyG_cprimPRSgcdGenCore cgcdB fuel P Q hreg

section
variable [CFracGcdCore β]

-- THE DELIVERABLE: the recursive tower fraction-free gcd `cgcdFFRawCore` computes the polynomial gcd of
-- the inputs up to associates over β(s)[t] = (CFieldSpec.K (QFunNZG β))[X], under the per-step
-- `CPrimPRSGenAssocReg` bundle a real run satisfies.
example (fuel : ℕ) (p q : CPolyG (QFunNZG β))
    (hreg : CPrimPRSGenAssocReg (CFracGcdCore.cgcdFFRawCore fuel) fuel
      (if GBPolyCore.gbdegCore (CPolyG.cclearDenomsCoreG p)
          < GBPolyCore.gbdegCore (CPolyG.cclearDenomsCoreG q)
        then CPolyG.cclearDenomsCoreG q else CPolyG.cclearDenomsCoreG p)
      (if GBPolyCore.gbdegCore (CPolyG.cclearDenomsCoreG p)
          < GBPolyCore.gbdegCore (CPolyG.cclearDenomsCoreG q)
        then CPolyG.cclearDenomsCoreG p else CPolyG.cclearDenomsCoreG q)) :
    Associated (toPolyG (CFracGcdCore.cgcdFFRawCore fuel p q)) (gcd (toPolyG p) (toPolyG q)) :=
  associated_toPolyG_cgcdFFRawCore fuel p q hreg

end

/-! ### Verdict and the precise remaining gap

**Verdict (Task 1): the QFunNZ proof transports — mechanically in spirit, by re-derivation in fact.**
The spine of `ComputableGcdCorrect` (clear-denominators unit-scaling, Euclidean-step gcd invariant,
primitive-part unit scaling, the `filter_prod_mul` combinatorics) carries over with `ℚ ⟿ CFieldSpec.K β`
and the concrete `Compute.b*` engine + `toBPoly` bridge replaced by the generic `gb*Core` engine +
`toGBPolyG`. NO `ℚ[x]`/`ℚ`-specific fact was needed: every `ℚ[x]`-content step became a Mathlib
generic-content / field-generic step (the `(CFieldSpec.K β)[X]` is a `NormalizedGCDMonoid`/Euclidean
domain, and `RatFunc (CFieldSpec.K β)` is a field), and `filter_prod_mul` was reused verbatim. So the
algorithm's "almost-purely-mechanical" generalization is matched by an almost-purely-mechanical proof
generalization.

**What is fully proved (axiom-clean, `[propext, Classical.choice, Quot.sound]`):**
* `associated_toPolyG_cgcdFFRawCore` / `associated_toPolyG_cgcdFFCore` — THE deliverable: the recursive
  tower fraction-free gcd computes the polynomial gcd up to associates over β(s)[t], gated on the
  per-step regularity bundle `CPrimPRSGenAssocReg` (the generic mirror of `PrimPRSRegular`).
* Clause (ii) (pseudo-division witness) `toGBPolyG_gbpsremainderCore`, and clause (iii) (content strip is
  a β(s)-unit) DISCHARGED from `CgcdBCorrect cgcdB` (the level-`β` gcd-correctness) +
  transparent algorithmics, via Mathlib content + the `cgcdB`-fold-divides theory
  (`associated_toGBPolyG_gbprimitivePartCore_of_correct`).
* The base case `associated_toPolyG_cgcdExtG` (the bottom of the tower, and the content-gcd at any level).

**The precise remaining gap (toward a fully *unconditional* tower induction):**
1. **Clause (i) termination** of `CPrimPRSGenAssocReg` is still assumed. It is discharged in the QFunNZ
   file by `primPRSInputs_of_nodeRegular` from a `t`-degree bound via the strict per-step
   `bdeg`-decrease; the generic version needs the `gb*Core` analogue of `bdegree_reduce_step_lt` /
   `primPRSstep_length_lt` (a mechanical re-derivation, not a new idea).
2. **The tower recursion** must thread `CgcdBCorrect (cgcdFFRawCore β)` as the induction hypothesis. This
   is NOT a plain structural induction: `CFracGcdCore` is a depth-free typeclass, so it needs a companion
   correctness class (`CFracGcdCoreCorrect`, with a base instance at `ℚ` and a recursive instance at
   `QFunNZG β`) capturing "this level's `cgcdFFRawCore` is gcd-correct on terminating runs". The genuine
   subtlety found: **`CgcdBCorrect` (unconditional over all inputs) does NOT hold for the base
   `cgcdFFRawCore ℚ = (cgcdExtG _).1`** — `associated_toPolyG_cgcdExtG` needs `cgcdTerminatesG` — so the
   recursion must carry the fuel/termination side-conditions (the `cgcdTerminatesG`/`ContentFoldTerminates`
   threading the QFunNZ file does), not a clean `∀`-correctness.

So the residual obstruction is **not** a missing Mathlib/GCD-domain fact (the content lever closed every
`ℚ[x]`-specific step) — it is the **bookkeeping of the fuel-termination side-conditions through the tower
recursion**, exactly the machinery `ComputableGcdCorrect`'s `PrimPRSInputs`/`primPRSInputs_of_nodeRegular`
layer carries at the single concrete level, now to be lifted to the depth-indexed tower. -/

#print axioms associated_toPolyG_cgcdExtG
#print axioms associated_toGBPolyG_cprimPRSgcdGenCore
#print axioms associated_toPolyG_cgcdFFRawCore
#print axioms associated_toPolyG_cgcdFFCore

end DeepWiki.SymbolicIntegration
