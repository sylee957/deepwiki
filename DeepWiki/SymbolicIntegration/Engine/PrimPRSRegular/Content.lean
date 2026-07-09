import DeepWiki.SymbolicIntegration.Engine.Tower.GcdFFCorrect
import DeepWiki.SymbolicIntegration.Engine.Tower.WellFounded

/-! # Primitive PRS regularity: content witnesses

Nonzero leading coefficients, pseudo-remainder multiplier witnesses, and content-strip associatedness.
-/

open Polynomial Classical

namespace DeepWiki.SymbolicIntegration

open CPoly GBPolyCore

variable {β : Type*} [CField β] [CFieldSpec β]

/-! ## The per-step content lemmas: the nonzero-multiplier strengthening of clause (ii)

The pseudo-division multiplier accumulated by `gbpsremainderCore fuel p q` is a power of `lc(q)`, hence
nonzero exactly when `q ≠ 0` — so clause (ii)'s `β(s)`-unit multiplier is unconditional given `q ≠ 0`. -/

/-- **The leading `t`-coefficient of a nonzero `GBPolyCore` reads nonzero**: if `gbisZeroCore q = false`
(`q ≠ 0` in `t`), then `toPoly (gblcCore q) ≠ 0` in `R = (CFieldSpec.K β)[X]`. The top normalized
`t`-coefficient is `cnorm`-nonempty, hence `toPoly`-nonzero (`gbnormCore_getLast?_toPolyG_ne_zero`). -/
theorem toPolyG_gblcCore_ne_zero {q : GBPolyCore β} (hq : gbisZeroCore q = false) :
    CPoly.toPoly (gblcCore q) ≠ 0 := by
  -- `gbnormCore q ≠ []` (zero test is `false`), so `getLast?` is `some v` with `toPoly v ≠ 0`
  have hne : gbnormCore q ≠ [] := by
    rw [gbisZeroCore, List.isEmpty_eq_false_iff_exists_mem] at hq
    obtain ⟨a, ha⟩ := hq
    exact List.ne_nil_of_mem ha
  rcases hg : (gbnormCore q).getLast? with _ | v
  · exact absurd (List.getLast?_eq_none_iff.mp hg) hne
  · have hlc : gblcCore q = v := by rw [gblcCore, hg, Option.getD_some]
    rw [hlc]
    exact gbnormCore_getLast?_toPolyG_ne_zero q v hg

/-- **The multiplier of `gbpsremainderCore` is `toPoly`-nonzero when the divisor is nonzero.** Produces
a pseudo-division witness `(s, c)` with the Euclidean identity and `toPoly c ≠ 0`, provided
`gbisZeroCore (gbnormCore q) = false`. -/
theorem toGBCoeffPoly_gbpsremainderCore_ne_zero (fuel : ℕ) (p q : GBPolyCore β)
    (hq : gbisZeroCore (gbnormCore q) = false) :
    ∃ (s : GBPolyCore β) (c : CPoly β),
      Polynomial.C (CPoly.toPoly c) * toGBCoeffPoly p
          = toGBCoeffPoly s * toGBCoeffPoly q + toGBCoeffPoly (gbpsremainderCore fuel p q)
        ∧ CPoly.toPoly c ≠ 0 := by
  have hone : CPoly.toPoly ([CField.one] : CPoly β) = 1 := by
    simp only [denote]
    simp
  -- `lc(gbnormCore q)` reads nonzero (the divisor is nonzero)
  have hlcq : CPoly.toPoly (gblcCore (gbnormCore q)) ≠ 0 :=
    toPolyG_gblcCore_ne_zero hq
  induction fuel generalizing p with
  | zero =>
    exact ⟨[], [CField.one], by simp [gbpsremainderCore, toGBCoeffPoly_gbnormCore, hone],
      by rw [hone]; exact one_ne_zero⟩
  | succ fuel ih =>
    simp only [gbpsremainderCore]
    split_ifs with hqz hlen
    · exact ⟨[], [CField.one], by simp [toGBCoeffPoly_gbnormCore, hone],
        by rw [hone]; exact one_ne_zero⟩
    · exact ⟨[], [CField.one], by simp [toGBCoeffPoly_gbnormCore, hone],
        by rw [hone]; exact one_ne_zero⟩
    · obtain ⟨s', c', hsc, hc'⟩ := ih (gbnormCore (gbsubCore (gbscaleCCore (gblcCore (gbnormCore q))
        (gbnormCore p))
        (gbscaleCCore (gblcCore (gbnormCore p))
          (gbshiftCore ((gbnormCore p).length - (gbnormCore q).length) (gbnormCore q)))))
      have hp' : toGBCoeffPoly (gbnormCore (gbsubCore (gbscaleCCore (gblcCore (gbnormCore q))
          (gbnormCore p))
          (gbscaleCCore (gblcCore (gbnormCore p))
            (gbshiftCore ((gbnormCore p).length - (gbnormCore q).length) (gbnormCore q)))))
          = Polynomial.C (CPoly.toPoly (gblcCore (gbnormCore q))) * toGBCoeffPoly p
            - Polynomial.C (CPoly.toPoly (gblcCore (gbnormCore p)))
              * Polynomial.X ^ ((gbnormCore p).length - (gbnormCore q).length) * toGBCoeffPoly q := by
        rw [toGBCoeffPoly_gbnormCore, toGBCoeffPoly_gbsubCore, toGBCoeffPoly_gbscaleCCore,
          toGBCoeffPoly_gbscaleCCore, toGBCoeffPoly_gbshiftCore, toGBCoeffPoly_gbnormCore,
          toGBCoeffPoly_gbnormCore]
        ring
      rw [hp', gbpsremainderCore_gbnormCore_right] at hsc
      refine ⟨gbaddCore s' (gbscaleCCore (CPoly.cmul c' (gblcCore (gbnormCore p)))
          (gbshiftCore ((gbnormCore p).length - (gbnormCore q).length) [[CField.one]])),
          CPoly.cmul c' (gblcCore (gbnormCore q)), ?_, ?_⟩
      · rw [toGBCoeffPoly_gbaddCore, toGBCoeffPoly_gbscaleCCore, toGBCoeffPoly_gbshiftCore,
          toGBCoeffPoly_one]
        simp only [denote, map_mul]
        linear_combination hsc
      · simpa only [denote] using mul_ne_zero hc' hlcq

/-- **`gbpsremainderCore` lifts to a `β(s)[t]` Euclidean relation with a `β(s)`-unit multiplier**: if
`gbisZeroCore (gbnormCore q) = false`, there is `(s, c)` with
`C (amG (toPoly c)) · toGBPolyG p = toGBPolyG s · toGBPolyG q + toGBPolyG (gbpsremainderCore fuel p q)`
and `amG (toPoly c) ≠ 0` in `(RatFunc (CFieldSpec.K β))[X]`. -/
theorem toGBPolyG_gbpsremainderCore_ne_zero (fuel : ℕ) (p q : GBPolyCore β)
    (hq : gbisZeroCore (gbnormCore q) = false) :
    ∃ (s : GBPolyCore β) (c : CPoly β),
      Polynomial.C (QFunNZG.amG β (CPoly.toPoly c)) * toGBPolyG p
          = toGBPolyG s * toGBPolyG q + toGBPolyG (gbpsremainderCore fuel p q)
        ∧ QFunNZG.amG β (CPoly.toPoly c) ≠ 0 := by
  obtain ⟨s, c, hsc, hc⟩ := toGBCoeffPoly_gbpsremainderCore_ne_zero fuel p q hq
  refine ⟨s, c, ?_, QFunNZG.amG_toPolyG_ne_zero hc⟩
  have hl := congrArg (liftKG β) hsc
  simp only [map_add, map_mul] at hl
  rw [liftKG_C] at hl
  simpa [toGBPolyG] using hl

/-! ## The total clause (iii): the content strip is a `β(s)`-unit scaling on any input

Bundling the nonzero-content case with the zero case (where `gbprimitivePartCore` is the identity) gives
clause (iii) conditional only on `CgcdBCorrect cgcdB` plus the retained bookkeeping. -/

/-- **The content strip is a `β(s)`-unit scaling on any input**: under `CgcdBCorrect cgcdB` and the
per-`t`-coefficient size bound, `Associated (toGBPolyG (gbprimitivePartCore cgcdB p)) (toGBPolyG p)`.
Splits on whether the content `gbcontentCore cgcdB p` is zero (identity, reflexive) or nonzero (unit
scaling). -/
theorem associated_toGBPolyG_gbprimitivePartCore_total (fuel : ℕ)
    (cgcdB : CPoly β → CPoly β → CPoly β) (hcorr : CgcdBCorrect cgcdB) (p : GBPolyCore β)
    (hfuel : ∀ a ∈ gbnormCore p, (CPoly.cnorm a : List β).length ≤ fuel) :
    Associated (toGBPolyG (gbprimitivePartCore cgcdB p)) (toGBPolyG p) := by
  by_cases hgz : CPoly.cisZero (gbcontentCore cgcdB p) = true
  · -- content zero: gbprimitivePartCore is the identity `gbnormCore p`
    have hid : gbprimitivePartCore cgcdB p = gbnormCore p := by
      rw [gbprimitivePartCore, gbcontentCore_gbnormCore, if_pos hgz]
    rw [hid, toGBPolyG_gbnormCore]
  · -- content nonzero: the unit scaling (Mathlib content + cgcdB-fold-divides)
    have hg0 : CPoly.toPoly (gbcontentCore cgcdB p) ≠ 0 := by
      rw [Ne, ← CPoly.cisZeroG_iff]; exact hgz
    have hgcn : CPoly.cnorm (gbcontentCore cgcdB p) ≠ [] := by
      rw [Ne, CPoly.cnormG_eq_nil_iff]; exact hg0
    exact associated_toGBPolyG_gbprimitivePartCore_of_correct fuel cgcdB hcorr p hgz hgcn hg0 hfuel

end DeepWiki.SymbolicIntegration
