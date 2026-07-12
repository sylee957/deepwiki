import DeepWiki.SymbolicIntegration.Engine.Tower.GcdFFCorrect

/-! # Primitive PRS regularity: content witnesses

Nonzero leading coefficients, pseudo-remainder multiplier witnesses, and content-strip associatedness.
-/

open Polynomial Classical

namespace DeepWiki.SymbolicIntegration

open DensePoly GBPolyCore

variable {β : Type*} [CField β] [CFieldSpec β]

/-! ## The per-step content lemmas: the nonzero-multiplier strengthening of clause (ii)

The pseudo-division multiplier accumulated by `gbpsremainderCore fuel p q` is a power of `lc(q)`, hence
nonzero exactly when `q ≠ 0` — so clause (ii)'s `β(s)`-unit multiplier is unconditional given `q ≠ 0`. -/

/-- **The leading `t`-coefficient of a nonzero `GBPolyCore` reads nonzero**: if `DensePoly.cisZero q = false`
(`q ≠ 0` in `t`), then `toPoly (gblcCore q) ≠ 0` in `R = (CFieldSpec.K β)[X]`. The top normalized
`t`-coefficient is `cnorm`-nonempty, hence `toPoly`-nonzero (`gbnormCore_getLast?_toPolyG_ne_zero`). -/
theorem toPolyG_gblcCore_ne_zero {q : GBPolyCore β} (hq : DensePoly.cisZero q = false) :
    DensePoly.toPoly (gblcCore q) ≠ 0 := by
  -- `gbnormCore q ≠ []` (zero test is `false`), so `getLast?` is `some v` with `toPoly v ≠ 0`
  have hne : gbnormCore q ≠ [] := by
    intro hnorm
    apply DensePoly.toPolyG_ne_zero_of_cisZeroG_false hq
    rw [← toPolyG_gbnormCore, hnorm, DensePoly.toPolyG_nil]
  rcases hg : (gbnormCore q).getLast? with _ | v
  · exact absurd (List.getLast?_eq_none_iff.mp hg) hne
  · have hlc : gblcCore q = v := by rw [gblcCore, hg, Option.getD_some]
    rw [hlc]
    exact gbnormCore_getLast?_toPolyG_ne_zero q v hg

/-- **The multiplier of `gbpsremainderCore` is `toPoly`-nonzero when the divisor is nonzero.** Produces
a pseudo-division witness `(s, c)` with the Euclidean identity and `toPoly c ≠ 0`, provided
`DensePoly.cisZero (gbnormCore q) = false`. -/
theorem toPolyG_gbpsremainderCore_ne_zero (fuel : ℕ) (p q : GBPolyCore β)
    (hq : DensePoly.cisZero (gbnormCore q) = false) :
    ∃ (s : GBPolyCore β) (c : DensePoly β),
      Polynomial.C (DensePoly.toPoly c) * DensePoly.toPoly p
          = DensePoly.toPoly s * DensePoly.toPoly q + DensePoly.toPoly (gbpsremainderCore fuel p q)
        ∧ DensePoly.toPoly c ≠ 0 := by
  have hone : DensePoly.toPoly ([CCommRing.one] : DensePoly β) = 1 := by
    simp only [denote]
    simp
  -- `lc(gbnormCore q)` reads nonzero (the divisor is nonzero)
  have hlcq : DensePoly.toPoly (gblcCore (gbnormCore q)) ≠ 0 :=
    toPolyG_gblcCore_ne_zero hq
  induction fuel generalizing p with
  | zero =>
    exact ⟨[], [CCommRing.one], by simp [gbpsremainderCore, toPolyG_gbnormCore, hone],
      by rw [hone]; exact one_ne_zero⟩
  | succ fuel ih =>
    simp only [gbpsremainderCore]
    split_ifs with hqz hlen
    · exact ⟨[], [CCommRing.one], by simp [toPolyG_gbnormCore, hone],
        by rw [hone]; exact one_ne_zero⟩
    · exact ⟨[], [CCommRing.one], by simp [toPolyG_gbnormCore, hone],
        by rw [hone]; exact one_ne_zero⟩
    · obtain ⟨s', c', hsc, hc'⟩ := ih (gbnormCore (DensePoly.csub (DensePoly.cscale (gblcCore (gbnormCore q))
        (gbnormCore p))
        (DensePoly.cscale (gblcCore (gbnormCore p))
          (DensePoly.cshift ((gbnormCore p).length - (gbnormCore q).length) (gbnormCore q)))))
      have hp' : DensePoly.toPoly (gbnormCore (DensePoly.csub (DensePoly.cscale (gblcCore (gbnormCore q))
          (gbnormCore p))
          (DensePoly.cscale (gblcCore (gbnormCore p))
            (DensePoly.cshift ((gbnormCore p).length - (gbnormCore q).length) (gbnormCore q)))))
          = Polynomial.C (DensePoly.toPoly (gblcCore (gbnormCore q))) * DensePoly.toPoly p
            - Polynomial.C (DensePoly.toPoly (gblcCore (gbnormCore p)))
              * Polynomial.X ^ ((gbnormCore p).length - (gbnormCore q).length) * DensePoly.toPoly q := by
        rw [toPolyG_gbnormCore, DensePoly.toPolyG_csubG, DensePoly.toPolyG_cscaleG,
          DensePoly.toPolyG_cscaleG, DensePoly.toPolyG_cshiftG, toPolyG_gbnormCore,
          toPolyG_gbnormCore]
        simp only [DensePoly.toR_densePoly]
        ring
      rw [hp', gbpsremainderCore_gbnormCore_right] at hsc
      refine ⟨DensePoly.cadd s' (DensePoly.cscale (DensePoly.cmul c' (gblcCore (gbnormCore p)))
          (DensePoly.cshift ((gbnormCore p).length - (gbnormCore q).length) [[CCommRing.one]])),
          DensePoly.cmul c' (gblcCore (gbnormCore q)), ?_, ?_⟩
      · rw [DensePoly.toPolyG_caddG, DensePoly.toPolyG_cscaleG, DensePoly.toPolyG_cshiftG,
          toPolyG_one]
        simp only [DensePoly.toR_densePoly, denote, map_mul]
        linear_combination hsc
      · simpa only [denote] using mul_ne_zero hc' hlcq

/-- **`gbpsremainderCore` lifts to a `β(s)[t]` Euclidean relation with a `β(s)`-unit multiplier**: if
`DensePoly.cisZero (gbnormCore q) = false`, there is `(s, c)` with
`C (am (toPoly c)) · toGBPoly p = toGBPoly s · toGBPoly q + toGBPoly (gbpsremainderCore fuel p q)`
and `am (toPoly c) ≠ 0` in `(RatFunc (CFieldSpec.K β))[X]`. -/
theorem toGBPolyG_gbpsremainderCore_ne_zero (fuel : ℕ) (p q : GBPolyCore β)
    (hq : DensePoly.cisZero (gbnormCore q) = false) :
    ∃ (s : GBPolyCore β) (c : DensePoly β),
      Polynomial.C (CFrac.am β (DensePoly.toPoly c)) * toGBPoly p
          = toGBPoly s * toGBPoly q + toGBPoly (gbpsremainderCore fuel p q)
        ∧ CFrac.am β (DensePoly.toPoly c) ≠ 0 := by
  obtain ⟨s, c, hsc, hc⟩ := toPolyG_gbpsremainderCore_ne_zero fuel p q hq
  refine ⟨s, c, ?_, CFrac.am_ne_zero hc⟩
  have hl := congrArg (liftK β) hsc
  simp only [map_add, map_mul] at hl
  rw [liftKG_C] at hl
  simpa [toGBPoly] using hl

/-! ## The total clause (iii): the content strip is a `β(s)`-unit scaling on any input

Bundling the nonzero-content case with the zero case (where `gbprimitivePartCore` is the identity) gives
clause (iii) from `CgcdBCorrect cgcdB` alone. -/

/-- **The content strip is a `β(s)`-unit scaling on any input**: under `CgcdBCorrect cgcdB`,
`Associated (toGBPoly (gbprimitivePartCore cgcdB p)) (toGBPoly p)`.
Splits on whether the content `gbcontentCore cgcdB p` is zero (identity, reflexive) or nonzero (unit
scaling). -/
theorem associated_toGBPolyG_gbprimitivePartCore_total
    (cgcdB : DensePoly β → DensePoly β → DensePoly β) (hcorr : CgcdBCorrect cgcdB) (p : GBPolyCore β) :
    Associated (toGBPoly (gbprimitivePartCore cgcdB p)) (toGBPoly p) := by
  by_cases hgz : DensePoly.cisZero (gbcontentCore cgcdB p) = true
  · -- content zero: gbprimitivePartCore is the identity `gbnormCore p`
    have hid : gbprimitivePartCore cgcdB p = gbnormCore p := by
      rw [gbprimitivePartCore, gbcontentCore_gbnormCore, if_pos hgz]
    rw [hid, toGBPolyG_gbnormCore]
  · -- content nonzero: the unit scaling (Mathlib content + cgcdB-fold-divides)
    have hg0 : DensePoly.toPoly (gbcontentCore cgcdB p) ≠ 0 := by
      rw [Ne, ← DensePoly.cisZeroG_iff]; exact hgz
    have hgcn : DensePoly.cnorm (gbcontentCore cgcdB p) ≠ [] := by
      rw [Ne, DensePoly.cnormG_eq_nil_iff]; exact hg0
    exact associated_toGBPolyG_gbprimitivePartCore_of_correct cgcdB hcorr p hgz hgcn hg0

end DeepWiki.SymbolicIntegration
