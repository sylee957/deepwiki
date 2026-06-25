import DeepWiki.SymbolicIntegration.ComputableIntegrate
import DeepWiki.SymbolicIntegration.ComputableIntegrateCorrect
import DeepWiki.SymbolicIntegration.ComputableResidueBridge
import DeepWiki.SymbolicIntegration.ComputableResultantGeneric

/-! # The self-validating integrator `cIntegrateChecked` — UNCONDITIONAL correctness (Bronstein Ch. 5)

The engine `cIntegrate` (`ComputableIntegrate`) assembles the transcendental Risch loop but returns its
`IntegralResult` **without** re-validating it against the antiderivative identity. In regimes outside its
documented scope (hyperexponential `Dt`, an unmatched residue field) it can therefore emit a `some res`
whose derivative is `f + R` with `R ≠ 0` — an incorrect answer.

This file closes that gap with a **checked wrapper** `cIntegrateChecked`, which guards `cIntegrate`'s
output by the engine's own cleared antiderivative check `IntegralResult.checkIdentity`: it returns
`some res` only when `checkIdentity Dt res a d = true`, and `none` otherwise. The headline
`cIntegrateChecked_correct` then proves — **unconditionally, for ALL inputs and ALL regimes** (primitive,
hyperexponential, anything) — that whenever `cIntegrateChecked` returns `some res`, the field-level
antiderivative identity `D(res) = f` holds over the tower fraction field `RatFunc (RatFunc ℚ)`, with
`D = towerFractionFieldDeriv Dt` and `f = a/d`. No regime hypothesis, no `fₛ = 0`, no residue-set or
degree side conditions: the `checkIdentity` guard supplies everything.

The crux is the **converse bridge** `field_identity_of_checkIdentity` — the reverse of the proven
`checkIdentity_of_field_identity`. The forward bridge clears the field fraction identity into the
engine's `cisZeroG` polynomial check; the converse runs the same clearing **backwards**: `checkIdentity
= true` is `cisZeroG (cleared difference) = true`, hence (via `cisZeroG_iff`) the cleared polynomial
identity `toPolyG (…) = 0`; lift it into the tower fraction field through the injective `towerAlg`,
divide by the nonzero denominators (`gden²·Lden·aden`), and read `GP/GD² = D(g)` (quotient rule) and
`LN/LD = logResidueSum` (the `checkIdentity_fold_eq` reindex) to recover the field identity. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZ

/-! ### The checked wrapper -/

namespace CPolyG

/-- **The self-validating integrator** `cIntegrateChecked Dt fuel a d cands`: run the engine
`cIntegrate`, then **guard** its output by the engine's own cleared antiderivative check
`IntegralResult.checkIdentity`. Returns `some res` only when `checkIdentity Dt res a d = true` (i.e.
`res` is a genuine antiderivative of `f = a/d`), and `none` otherwise — so it never returns a wrong
answer. A thin wrapper: it does **not** modify the engine `cIntegrate`. -/
def cIntegrateChecked (Dt : CPolyG QFunNZ) (fuel : ℕ) (a d : CPolyG QFunNZ) (cands : List ℚ) :
    Option IntegralResult :=
  (cIntegrate Dt fuel a d cands).bind
    (fun res => if IntegralResult.checkIdentity Dt res a d then some res else none)

end CPolyG

/-! ### The converse bridge — `checkIdentity = true ⟹ field identity` (the crux)

The reverse of `checkIdentity_of_field_identity`. From the engine's cleared `cisZeroG` check we recover
the field-level antiderivative identity `D(g) + logResidueSum = a/d`. This is what makes the checked
wrapper's correctness **unconditional**: `checkIdentity` alone — no regime, no residue match — pins
down the field identity. -/

open IntegralResult in
/-- **`checkIdentity = true ⟹ field identity** (the converse bridge, the crux): if the engine's cleared
antiderivative check `IntegralResult.checkIdentity Dt res anum aden = true` holds, with the denominators
`gden = res.rational.2`, `aden` nonzero and every log argument `vᵢ` nonzero, then the field-level
antiderivative identity
`towerFractionFieldDeriv Dt (towerAlg gnum / towerAlg gden) + logResidueSum Dt res.logs = towerAlg anum /
towerAlg aden` holds over the tower fraction field `RatFunc (RatFunc ℚ)`. Runs the forward bridge's
clearing **backwards**: `cisZeroG_iff` turns the check into the cleared polynomial identity, the injective
`towerAlg` lifts it into the field, and dividing by the nonzero `GD²·LD·AD` with the quotient-rule reading
`GP/GD² = D(g)` and the fold reindex `LN/LD = logResidueSum` recovers the field identity. -/
theorem field_identity_of_checkIdentity (Dt : CPolyG QFunNZ) (res : IntegralResult)
    (anum aden : CPolyG QFunNZ)
    (hgden : toPolyG res.rational.2 ≠ 0) (haden : toPolyG aden ≠ 0)
    (hlogs : ∀ cv ∈ res.logs, toPolyG cv.2 ≠ 0)
    (hcheck : IntegralResult.checkIdentity Dt res anum aden = true) :
    towerFractionFieldDeriv Dt (towerAlg (toPolyG res.rational.1) / towerAlg (toPolyG res.rational.2))
        + logResidueSum Dt res.logs
      = towerAlg (toPolyG anum) / towerAlg (toPolyG aden) := by
  -- names matching `checkIdentity`
  set gnum := res.rational.1 with hgnum
  set gden := res.rational.2 with hgdenE
  set gprimeNum := csubG (cmulG (cmonomialDeriv Dt gnum) gden) (cmulG gnum (cmonomialDeriv Dt gden))
    with hgp
  set gden2 := cmulG gden gden with hgden2
  -- the fold result `(Lnum, Lden)`
  set folded := res.logs.foldl
    (fun (acc : CPolyG QFunNZ × CPolyG QFunNZ) (cv : ℚ × CPolyG QFunNZ) =>
      let c := cv.1
      let v := cv.2
      let Dv := cmonomialDeriv Dt v
      let termNum := cscaleG (ofConstNZ c) Dv
      (caddG (cmulG acc.1 v) (cmulG termNum acc.2), cmulG acc.2 v))
    ([CField.zero], [CField.one]) with hfolded
  -- the fold computes `logResidueSum` over the field, with nonzero `Lden`
  have hseedden : toPolyG ([CField.one] : CPolyG QFunNZ) ≠ 0 := by
    rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_one, mul_zero, add_zero]; exact one_ne_zero
  obtain ⟨hLden_ne, hLfield⟩ := checkIdentity_fold_eq Dt res.logs [CField.zero] [CField.one]
    hseedden hlogs
  rw [← hfolded] at hLden_ne hLfield
  -- the seed fraction `0/1 = 0`
  have hseed0 : towerAlg (toPolyG ([CField.zero] : CPolyG QFunNZ))
      / towerAlg (toPolyG ([CField.one] : CPolyG QFunNZ)) = 0 := by
    rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_zero, map_zero, mul_zero, add_zero, map_zero,
      zero_div]
  rw [hseed0, zero_add] at hLfield
  -- abbreviations over the field
  set GP := towerAlg (toPolyG gprimeNum) with hGP
  set LN := towerAlg (toPolyG folded.1) with hLN
  set LD := towerAlg (toPolyG folded.2) with hLD
  set AN := towerAlg (toPolyG anum) with hAN
  set AD := towerAlg (toPolyG aden) with hAD
  set GD := towerAlg (toPolyG gden) with hGD
  -- nonzero readings
  have hGDne : GD ≠ 0 := by rw [hGD]; exact towerAlg_ne_zero hgden
  have hLDne : LD ≠ 0 := by rw [hLD]; exact towerAlg_ne_zero hLden_ne
  have hADne : AD ≠ 0 := by rw [hAD]; exact towerAlg_ne_zero haden
  -- `D(gnum/gden) = GP/GD²` (quotient rule); `logResidueSum = LN/LD` (fold bridge)
  have hquot : towerFractionFieldDeriv Dt (towerAlg (toPolyG gnum) / towerAlg (toPolyG gden))
      = GP / GD ^ 2 := by
    rw [towerFractionFieldDeriv_div, hGP, hgp, toPolyG_csubG, toPolyG_cmulG, toPolyG_cmulG,
      toPolyG_cmonomialDeriv, toPolyG_cmonomialDeriv, map_sub, map_mul, map_mul, hGD]
  have hLfield' : logResidueSum Dt res.logs = LN / LD := by rw [← hLfield, hLN, hLD]
  -- ── the converse direction: extract the cleared polynomial identity from `checkIdentity = true` ──
  -- unfold `checkIdentity = true` to `cisZeroG (csubG lhs rhs) = true`, then `toPolyG (…) = 0`
  rw [IntegralResult.checkIdentity] at hcheck
  simp only [← hgnum, ← hgdenE, ← hgp, ← hgden2, ← hfolded] at hcheck
  rw [cisZeroG_iff, toPolyG_csubG, sub_eq_zero, toPolyG_cmulG, toPolyG_cmulG, toPolyG_caddG,
    toPolyG_cmulG, toPolyG_cmulG, toPolyG_cmulG] at hcheck
  -- lift the cleared polynomial equation into the tower fraction field (towerAlg injective)
  rw [← (RatFunc.algebraMap_injective (CFieldSpec.K QFunNZ)).eq_iff] at hcheck
  simp only [map_mul, map_add, hgden2, toPolyG_cmulG] at hcheck
  -- now `hcheck` is the cleared field equation `(GP·LD + LN·GD²)·AD = AN·(GD²·LD)` (over the field)
  rw [← hGP, ← hLN, ← hLD, ← hAN, ← hAD, ← hGD] at hcheck
  -- divide through the nonzero `GD²·LD·AD` to land the field fraction identity `GP/GD² + LN/LD = AN/AD`
  have hfield : GP / GD ^ 2 + LN / LD = AN / AD := by
    rw [div_add_div _ _ (pow_ne_zero 2 hGDne) hLDne, div_eq_div_iff (mul_ne_zero (pow_ne_zero 2 hGDne) hLDne) hADne]
    ring_nf
    ring_nf at hcheck
    linear_combination hcheck
  -- assemble: rewrite the field readings back into the goal
  rw [hquot, hLfield', hfield]

/-! ### The headline — `D(cIntegrateChecked f) = f`, UNCONDITIONAL (all inputs, all regimes)

Immediate from the wrapper definition and the converse bridge: `cIntegrateChecked = some res` forces
`cIntegrate = some res` **and** `checkIdentity Dt res a d = true` (the guard), and the converse bridge
turns the latter into the field identity `D(res) = f`. No regime hypothesis — the only side conditions
are the structural nonzero-denominator facts the field statement itself needs. -/

open IntegralResult in
/-- **`cIntegrateChecked f = some res ⟹ D(res) = f`**, the ultimate integrator-correctness statement —
**UNCONDITIONAL**, for ALL inputs and ALL regimes (primitive, hyperexponential, anything). If
`cIntegrateChecked Dt fuel a d cands = some res`, then the field-level antiderivative identity
`towerFractionFieldDeriv Dt (g) + logResidueSum Dt res.logs = a/d` holds over the tower fraction field
`RatFunc (RatFunc ℚ)`, where `g = towerAlg(res.rational.1)/towerAlg(res.rational.2)`. The only side
conditions are the structural nonzero-denominator hypotheses (`gden`, `aden`, every log argument `vᵢ`
nonzero) the field statement needs to even be a fraction identity; **no** regime / `fₛ = 0` / residue-set
/ degree hypothesis is required — the `checkIdentity` guard inside `cIntegrateChecked` supplies all of
that. Immediate from the wrapper definition (`some` forces `checkIdentity = true`) and the converse
bridge `field_identity_of_checkIdentity`. -/
theorem cIntegrateChecked_correct (Dt : CPolyG QFunNZ) (fuel : ℕ) (a d : CPolyG QFunNZ)
    (cands : List ℚ) (res : IntegralResult)
    (hsome : cIntegrateChecked Dt fuel a d cands = some res)
    (hgden : toPolyG res.rational.2 ≠ 0) (hdne : toPolyG d ≠ 0)
    (hlogs : ∀ cv ∈ res.logs, toPolyG cv.2 ≠ 0) :
    towerFractionFieldDeriv Dt (towerAlg (toPolyG res.rational.1) / towerAlg (toPolyG res.rational.2))
        + logResidueSum Dt res.logs
      = towerAlg (toPolyG a) / towerAlg (toPolyG d) := by
  -- the wrapper returned `some res`, so the guard `checkIdentity` fired `true`
  have hcheck : IntegralResult.checkIdentity Dt res a d = true := by
    rw [cIntegrateChecked] at hsome
    -- `(cIntegrate …).bind guard = some res` ⟹ `cIntegrate … = some res'` and `guard res' = some res`
    rcases hcinteg : cIntegrate Dt fuel a d cands with _ | res'
    · rw [hcinteg] at hsome; simp only [Option.bind_none] at hsome; exact absurd hsome (by simp)
    · rw [hcinteg] at hsome
      simp only [Option.bind_some] at hsome
      by_cases hc : IntegralResult.checkIdentity Dt res' a d
      · simp only [hc, if_true, Option.some.injEq] at hsome
        rw [← hsome]; exact hc
      · simp only [hc] at hsome; exact absurd hsome (by simp)
  -- the converse bridge turns the guard into the field identity
  exact field_identity_of_checkIdentity Dt res a d hgden hdne hlogs hcheck

/-! ### Restatement against the intended wording (anonymous `example`) -/

-- The HEADLINE: the self-validating integrator never returns a wrong answer. `cIntegrateChecked f =
-- some res` ⟹ `D(res) = f` over the tower fraction field — UNCONDITIONAL, for EVERY input and EVERY
-- regime (primitive, hyperexponential, …). The `checkIdentity` guard alone supplies correctness; the
-- only side conditions are the structural nonzero-denominator facts the field fraction identity needs.
example (Dt : CPolyG QFunNZ) (fuel : ℕ) (a d : CPolyG QFunNZ) (cands : List ℚ) (res : IntegralResult)
    (hsome : cIntegrateChecked Dt fuel a d cands = some res)
    (hgden : toPolyG res.rational.2 ≠ 0) (hdne : toPolyG d ≠ 0)
    (hlogs : ∀ cv ∈ res.logs, toPolyG cv.2 ≠ 0) :
    towerFractionFieldDeriv Dt (towerAlg (toPolyG res.rational.1) / towerAlg (toPolyG res.rational.2))
        + logResidueSum Dt res.logs
      = towerAlg (toPolyG a) / towerAlg (toPolyG d) :=
  cIntegrateChecked_correct Dt fuel a d cands res hsome hgden hdne hlogs

#print axioms cIntegrateChecked_correct

end DeepWiki.SymbolicIntegration
