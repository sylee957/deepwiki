import DeepWiki.SymbolicIntegration.ComputableSplitFactorTowerCorrect
import DeepWiki.SymbolicIntegration.ComputableIntegrateCorrect
import DeepWiki.SymbolicIntegration.ComputableIntegrateChecked

/-! # Abstract correctness of the GENERIC tower integrator `cIntegrateG` at the level-1 carrier ℚ(x)
The generic tower engine's top-level driver `cIntegrateG` (`ComputableTowerIntegrate`) assembles the
transcendental Risch loop on the `[CField α] [CDiffField α] [CFracGcdCore α]`-generic ops — canonical
split (`canonicalRepresentationFastG`), Hermite rational part (`cHermiteReduceTowerG`), and the
Rothstein–Trager residue logarithms (`cLogPartG`) — and certifies its output with the generic cleared
antiderivative check `checkIdentityG`. It is `native_decide`-validated only (`towerIntLvl2_driver`).

This file gives the generic engine the abstract `D(∫f) = f` capstone it lacked — at the level-1 carrier
`α = QFunNZ` the engine collapse instantiates, where `cgcdFFCore` reads through `toPolyG` to the SAME gcd
as `cgcdFF` up to associates (the nucleus `ComputableSplitFactorTowerCorrect` filled the §3.5 piece).

**The route.** The generic driver `cIntegrateG` at `α = QFunNZ` differs from the QFunNZ `cIntegrate` only
in (1) the gcd (`cgcdFFCore` vs `cgcdFF`, inside the split/squarefree/log-argument steps), (2) the
residue candidates (`List QFunNZ` vs `List ℚ`), and (3) the result type (`IntegralResultG QFunNZ` with
`QFunNZ`-coefficient logs vs `IntegralResult` with `ℚ`-coefficient logs). The **field-level
antiderivative identity** `D(g) + ∑ᵢ cᵢ·(Δvᵢ)/vᵢ = f` over the tower fraction field `RatFunc (RatFunc ℚ)`
— with `Δ = implicitDeriv (toPolyG Dt)` and `D = towerFractionFieldDeriv Dt` — is what `checkIdentityG`
clears, exactly as `checkIdentity` clears the QFunNZ identity. Since `checkIdentityG` **never calls the
gcd** (it only folds the residue terms `cᵢ·D(vᵢ)/vᵢ` and clears denominators), the whole
field ⇒ Boolean clearing bridge transports **verbatim** from the QFunNZ proof — only the residue-sum
spelling changes (`C (toK cᵢ)` directly, with `cᵢ : QFunNZ`, in place of `C (toK (ofConstNZ cᵢ))`).

The deliverable:

* **`logResidueSumG`** — the generic residue sum `∑_{(c,v)} C(toK c)·(Δv)/v` (the symbolic derivative of
  the generic logarithmic part `∑ c·log v`), and the fold reading `checkIdentityG_fold_eq`.
* **`checkIdentityG_of_field_identity` / `field_identity_of_checkIdentityG`** — the field ⇔ engine bridge,
  the generic mirror of `checkIdentity_of_field_identity` / `field_identity_of_checkIdentity`.
* **★ `cIntegrateG_field_identity`** — the generic engine's `D(∫f) = f` field-level capstone: in the
  primitive regime (`fₚ = fₛ = 0`, the `cIntegrateG` `some`-branch), `cIntegrateG Dt fuel a d cands =
  some res` lands an `IntegralResultG` whose antiderivative identity holds over `RatFunc (RatFunc ℚ)`. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZ

/-- The engine carrier `CFieldSpec.K QFunNZ` is `RatFunc ℚ`, a `ℚ`-algebra. Re-declared as a local
instance (matching the keystone's) so this file synthesizes the **same** `Algebra ℚ` as
`towerFractionFieldDeriv`, avoiding an instance-mismatch detour. -/
noncomputable local instance : Algebra ℚ (CFieldSpec.K QFunNZ) :=
  inferInstanceAs (Algebra ℚ (RatFunc ℚ))

/-! ### The generic logarithmic-part residue sum (over `QFunNZ`-valued coefficients)

The generic checker `checkIdentityG` folds the logarithmic part `∑ᵢ cᵢ·log(vᵢ)` (coefficients
`cᵢ : QFunNZ`) into its symbolic derivative `∑ᵢ cᵢ·(Δvᵢ)/vᵢ` (the log-derivative `D(log v) = (Δv)/v`),
accumulated as a single fraction `(Lnum, Lden)` over `∏ᵢ vᵢ`. We give it as a genuine field element
`logResidueSumG` over `RatFunc (RatFunc ℚ)`. Unlike the QFunNZ `logResidueSum` (which reads `ℚ`
coefficients through `ofConstNZ`), the coefficient here is *already* a `QFunNZ` constant, so it embeds
directly as `C (toK c)`. -/

/-- **The generic logarithmic-part residue sum** `logResidueSumG Dt logs = ∑_{(c,v)∈logs} C(toK c)·(Δv)/v`
over the tower fraction field `RatFunc (RatFunc ℚ)`, with `Δ = implicitDeriv (toPolyG Dt)` (so
`Δv = toPolyG (cmonomialDeriv Dt v)`). The symbolic derivative of the generic logarithmic part
`∑ᵢ cᵢ·log(vᵢ)` (`cᵢ : QFunNZ`) — exactly the residue sum `checkIdentityG` clears against `f`. The generic
mirror of `logResidueSum`, with the residue coefficient `c : QFunNZ` embedded directly as `C (toK c)`. -/
noncomputable def logResidueSumG (Dt : CPolyG QFunNZ) (logs : List (QFunNZ × CPolyG QFunNZ)) :
    RatFunc (CFieldSpec.K QFunNZ) :=
  (logs.map (fun cv =>
    towerAlg (Polynomial.C (CFieldSpec.toK cv.1))
      * (towerAlg (toPolyG (cmonomialDeriv Dt cv.2)) / towerAlg (toPolyG cv.2)))).sum

/-- `logResidueSumG` of the empty list is `0`. -/
@[simp] theorem logResidueSumG_nil (Dt : CPolyG QFunNZ) : logResidueSumG Dt [] = 0 := rfl

/-- `logResidueSumG` peels the head: `logResidueSumG Dt ((c,v) :: rest) = C(toK c)·(Δv)/v
+ logResidueSumG Dt rest`. -/
theorem logResidueSumG_cons (Dt : CPolyG QFunNZ) (cv : QFunNZ × CPolyG QFunNZ)
    (rest : List (QFunNZ × CPolyG QFunNZ)) :
    logResidueSumG Dt (cv :: rest)
      = towerAlg (Polynomial.C (CFieldSpec.toK cv.1))
          * (towerAlg (toPolyG (cmonomialDeriv Dt cv.2)) / towerAlg (toPolyG cv.2))
        + logResidueSumG Dt rest := by
  simp only [logResidueSumG, List.map_cons, List.sum_cons]

/-! ### The `checkIdentityG` fold computes the residue sum

`checkIdentityG`'s `foldl` accumulates `∑ cᵢ·(Δvᵢ)/vᵢ` as one fraction `(Lnum, Lden)` over `∏ᵢ vᵢ`,
starting at `([0], [1])` and combining `acc.1/acc.2 + (c·Δv)/v = (acc.1·v + c·Δv·acc.2)/(acc.2·v)`.
Reading through `towerAlg`, the running fraction is the seed plus the partial `logResidueSumG`; with all
`vᵢ` nonzero the seed contributes `0`. Verbatim transport of `checkIdentity_fold_eq` — the only change is
`cscaleG cv.1` (direct `QFunNZ` coefficient) in place of `cscaleG (ofConstNZ cv.1)`. -/

/-- **The `checkIdentityG` fold computes the residue sum** (field reading): folding from a seed
`(snum, sden)` (`sden ≠ 0`) over a generic log list whose every argument `v` is nonzero, the running
fraction `towerAlg(Lnum)/towerAlg(Lden)` equals the seed fraction plus `logResidueSumG`, and the running
denominator `Lden = sden·∏ᵢ vᵢ` stays nonzero. By induction on the list — the generic mirror of
`checkIdentity_fold_eq`. -/
theorem checkIdentityG_fold_eq (Dt : CPolyG QFunNZ) :
    ∀ (logs : List (QFunNZ × CPolyG QFunNZ)) (snum sden : CPolyG QFunNZ),
      toPolyG sden ≠ 0 →
      (∀ cv ∈ logs, toPolyG cv.2 ≠ 0) →
      let res := logs.foldl
        (fun (acc : CPolyG QFunNZ × CPolyG QFunNZ) (cv : QFunNZ × CPolyG QFunNZ) =>
          let c := cv.1
          let v := cv.2
          let Dv := cmonomialDeriv Dt v
          let termNum := cscaleG c Dv
          (caddG (cmulG acc.1 v) (cmulG termNum acc.2), cmulG acc.2 v))
        (snum, sden)
      toPolyG res.2 ≠ 0 ∧
        towerAlg (toPolyG res.1) / towerAlg (toPolyG res.2)
          = towerAlg (toPolyG snum) / towerAlg (toPolyG sden) + logResidueSumG Dt logs := by
  intro logs
  induction logs with
  | nil =>
    intro snum sden hsden _
    refine ⟨hsden, ?_⟩
    simp only [logResidueSumG_nil, add_zero, List.foldl_nil]
  | cons cv rest ih =>
    intro snum sden hsden hv
    -- the head argument `v` is nonzero
    have hvne : toPolyG cv.2 ≠ 0 := hv cv List.mem_cons_self
    -- one fold step: new accumulator
    set newnum := caddG (cmulG snum cv.2) (cmulG (cscaleG cv.1 (cmonomialDeriv Dt cv.2)) sden)
      with hnewnum
    set newden := cmulG sden cv.2 with hnewden
    have hnewden_ne : toPolyG newden ≠ 0 := by
      rw [hnewden, toPolyG_cmulG]; exact mul_ne_zero hsden hvne
    -- the IH applied to the rest with the new seed
    have hrest : ∀ cv' ∈ rest, toPolyG cv'.2 ≠ 0 := fun cv' hcv' => hv cv' (List.mem_cons_of_mem _ hcv')
    obtain ⟨hden, heq⟩ := ih newnum newden hnewden_ne hrest
    refine ⟨?_, ?_⟩
    · -- the running denominator after the head step is `(newnum, newden)`
      simp only [List.foldl_cons]
      exact hden
    simp only [List.foldl_cons]
    rw [heq, logResidueSumG_cons]
    -- the field algebra: `snum/sden + C(c)·(Δv)/v = newnum/newden`
    have hAsden : towerAlg (toPolyG sden) ≠ 0 := towerAlg_ne_zero hsden
    have hAv : towerAlg (toPolyG cv.2) ≠ 0 := towerAlg_ne_zero hvne
    have hstep : towerAlg (toPolyG newnum) / towerAlg (toPolyG newden)
        = towerAlg (toPolyG snum) / towerAlg (toPolyG sden)
          + towerAlg (Polynomial.C (CFieldSpec.toK cv.1))
              * (towerAlg (toPolyG (cmonomialDeriv Dt cv.2)) / towerAlg (toPolyG cv.2)) := by
      rw [hnewnum, hnewden, toPolyG_caddG, toPolyG_cmulG, toPolyG_cmulG, toPolyG_cscaleG,
        toPolyG_cmulG, map_add, map_mul, map_mul, map_mul]
      field_simp
      simp only [map_mul]
      ring
    rw [hstep]; ring

/-! ### The `checkIdentityG` ⇔ field-identity bridge

`checkIdentityG Dt res anum aden = true` is (via `cisZeroG_iff`) the cleared polynomial identity
`(GP·LD + LN·GD²)·AD = AN·(GD²·LD)` over `(RatFunc ℚ)[X]`, where `GP = toPolyG gprimeNum`,
`(LN, LD) = fold-result`, etc. Dividing through the nonzero `GD²·LD·AD` and reading `D(gnum/gden) =
GP/GD²` (quotient rule) and `LN/LD = logResidueSumG` (the fold bridge), this is exactly the field
identity `D(gnum/gden) + logResidueSumG = anum/aden`. Both directions transport **verbatim** from the
QFunNZ `checkIdentity_of_field_identity` / `field_identity_of_checkIdentity` — only the residue spelling
(`cscaleG cv.1`, `C (toK cv.1)`) and result type (`IntegralResultG`) differ; the gcd never enters. -/

/-- **Field identity ⟹ `checkIdentityG = true`** (the generic mirror of `checkIdentity_of_field_identity`):
if the field-level antiderivative identity `towerFractionFieldDeriv Dt (towerAlg gnum / towerAlg gden) +
logResidueSumG Dt res.logs = towerAlg anum / towerAlg aden` holds over the tower fraction field, with
`res.rational = (gnum, gden)`, the denominators `gden, aden` nonzero, and every log argument `vᵢ` nonzero,
then `checkIdentityG Dt res anum aden = true`. The clearing converts the field fraction identity back to
the cleared `cisZeroG` polynomial identity the generic checker runs. -/
theorem checkIdentityG_of_field_identity (Dt : CPolyG QFunNZ) (res : IntegralResultG QFunNZ)
    (anum aden : CPolyG QFunNZ)
    (hgden : toPolyG res.rational.2 ≠ 0) (haden : toPolyG aden ≠ 0)
    (hlogs : ∀ cv ∈ res.logs, toPolyG cv.2 ≠ 0)
    (hfield : towerFractionFieldDeriv Dt (towerAlg (toPolyG res.rational.1) / towerAlg (toPolyG res.rational.2))
        + logResidueSumG Dt res.logs
      = towerAlg (toPolyG anum) / towerAlg (toPolyG aden)) :
    CPolyG.checkIdentityG Dt res anum aden = true := by
  -- names matching `checkIdentityG`
  set gnum := res.rational.1 with hgnum
  set gden := res.rational.2 with hgdenE
  set gprimeNum := csubG (cmulG (cmonomialDeriv Dt gnum) gden) (cmulG gnum (cmonomialDeriv Dt gden))
    with hgp
  set gden2 := cmulG gden gden with hgden2
  -- the fold result `(Lnum, Lden)`
  set folded := res.logs.foldl
    (fun (acc : CPolyG QFunNZ × CPolyG QFunNZ) (cv : QFunNZ × CPolyG QFunNZ) =>
      let c := cv.1
      let v := cv.2
      let Dv := cmonomialDeriv Dt v
      let termNum := cscaleG c Dv
      (caddG (cmulG acc.1 v) (cmulG termNum acc.2), cmulG acc.2 v))
    ([CField.zero], [CField.one]) with hfolded
  -- the fold computes `logResidueSumG` over the field, with nonzero `Lden`
  have hseedden : toPolyG ([CField.one] : CPolyG QFunNZ) ≠ 0 := by
    rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_one, mul_zero, add_zero]; exact one_ne_zero
  obtain ⟨hLden_ne, hLfield⟩ := checkIdentityG_fold_eq Dt res.logs [CField.zero] [CField.one]
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
  -- `D(gnum/gden) = GP/GD²` (quotient rule); `logResidueSumG = LN/LD` (fold bridge)
  have hquot : towerFractionFieldDeriv Dt (towerAlg (toPolyG gnum) / towerAlg (toPolyG gden))
      = GP / GD ^ 2 := by
    rw [towerFractionFieldDeriv_div, hGP, hgp, toPolyG_csubG, toPolyG_cmulG, toPolyG_cmulG,
      toPolyG_cmonomialDeriv, toPolyG_cmonomialDeriv, map_sub, map_mul, map_mul, hGD]
  have hLfield' : logResidueSumG Dt res.logs = LN / LD := by rw [← hLfield, hLN, hLD]
  -- the field identity, rewritten with the readings: `GP/GD² + LN/LD = AN/AD`
  rw [hquot, hLfield'] at hfield
  -- the cleared polynomial equation `(GP·LD + LN·GD²)·AD = AN·(GD²·LD)`
  have hclear : (GP * LD + LN * (GD * GD)) * AD = AN * (GD * GD * LD) := by
    have hh := hfield
    field_simp at hh
    linear_combination hh
  -- unfold `checkIdentityG` to its `cisZeroG` and convert to the cleared `toPolyG` polynomial equation
  show CPolyG.checkIdentityG Dt res anum aden = true
  rw [CPolyG.checkIdentityG]
  simp only [← hgnum, ← hgdenE, ← hgp, ← hgden2, ← hfolded]
  rw [cisZeroG_iff, toPolyG_csubG, sub_eq_zero, toPolyG_cmulG, toPolyG_cmulG, toPolyG_caddG,
    toPolyG_cmulG, toPolyG_cmulG, toPolyG_cmulG]
  -- lift the cleared polynomial equation into the tower fraction field (towerAlg injective)
  rw [← (RatFunc.algebraMap_injective (CFieldSpec.K QFunNZ)).eq_iff]
  simp only [map_mul, map_add, hgden2, toPolyG_cmulG]
  -- the goal is now the cleared field equation, matching `hclear` term-by-term
  rw [← hGP, ← hLN, ← hLD, ← hAN, ← hAD, ← hGD]
  linear_combination hclear

/-- **`checkIdentityG = true ⟹ field identity`** (the converse bridge, the generic mirror of
`field_identity_of_checkIdentity`): if the generic cleared antiderivative check
`checkIdentityG Dt res anum aden = true` holds, with the denominators `gden = res.rational.2`, `aden`
nonzero and every log argument `vᵢ` nonzero, then the field-level antiderivative identity
`towerFractionFieldDeriv Dt (towerAlg gnum / towerAlg gden) + logResidueSumG Dt res.logs =
towerAlg anum / towerAlg aden` holds over `RatFunc (RatFunc ℚ)`. Runs the forward clearing backwards:
`cisZeroG_iff` turns the check into the cleared polynomial identity, the injective `towerAlg` lifts it,
and dividing by the nonzero `GD²·LD·AD` with `GP/GD² = D(g)` and `LN/LD = logResidueSumG` recovers the
field identity. The generic engine's `D(∫f) = f`, in field form, gated only on `checkIdentityG = true`. -/
theorem field_identity_of_checkIdentityG (Dt : CPolyG QFunNZ) (res : IntegralResultG QFunNZ)
    (anum aden : CPolyG QFunNZ)
    (hgden : toPolyG res.rational.2 ≠ 0) (haden : toPolyG aden ≠ 0)
    (hlogs : ∀ cv ∈ res.logs, toPolyG cv.2 ≠ 0)
    (hcheck : CPolyG.checkIdentityG Dt res anum aden = true) :
    towerFractionFieldDeriv Dt (towerAlg (toPolyG res.rational.1) / towerAlg (toPolyG res.rational.2))
        + logResidueSumG Dt res.logs
      = towerAlg (toPolyG anum) / towerAlg (toPolyG aden) := by
  -- names matching `checkIdentityG`
  set gnum := res.rational.1 with hgnum
  set gden := res.rational.2 with hgdenE
  set gprimeNum := csubG (cmulG (cmonomialDeriv Dt gnum) gden) (cmulG gnum (cmonomialDeriv Dt gden))
    with hgp
  set gden2 := cmulG gden gden with hgden2
  -- the fold result `(Lnum, Lden)`
  set folded := res.logs.foldl
    (fun (acc : CPolyG QFunNZ × CPolyG QFunNZ) (cv : QFunNZ × CPolyG QFunNZ) =>
      let c := cv.1
      let v := cv.2
      let Dv := cmonomialDeriv Dt v
      let termNum := cscaleG c Dv
      (caddG (cmulG acc.1 v) (cmulG termNum acc.2), cmulG acc.2 v))
    ([CField.zero], [CField.one]) with hfolded
  -- the fold computes `logResidueSumG` over the field, with nonzero `Lden`
  have hseedden : toPolyG ([CField.one] : CPolyG QFunNZ) ≠ 0 := by
    rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_one, mul_zero, add_zero]; exact one_ne_zero
  obtain ⟨hLden_ne, hLfield⟩ := checkIdentityG_fold_eq Dt res.logs [CField.zero] [CField.one]
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
  -- `D(gnum/gden) = GP/GD²` (quotient rule); `logResidueSumG = LN/LD` (fold bridge)
  have hquot : towerFractionFieldDeriv Dt (towerAlg (toPolyG gnum) / towerAlg (toPolyG gden))
      = GP / GD ^ 2 := by
    rw [towerFractionFieldDeriv_div, hGP, hgp, toPolyG_csubG, toPolyG_cmulG, toPolyG_cmulG,
      toPolyG_cmonomialDeriv, toPolyG_cmonomialDeriv, map_sub, map_mul, map_mul, hGD]
  have hLfield' : logResidueSumG Dt res.logs = LN / LD := by rw [← hLfield, hLN, hLD]
  -- ── the converse direction: extract the cleared polynomial identity from `checkIdentityG = true` ──
  rw [CPolyG.checkIdentityG] at hcheck
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
    rw [div_add_div _ _ (pow_ne_zero 2 hGDne) hLDne,
      div_eq_div_iff (mul_ne_zero (pow_ne_zero 2 hGDne) hLDne) hADne]
    ring_nf
    ring_nf at hcheck
    linear_combination hcheck
  -- assemble: rewrite the field readings back into the goal
  rw [hquot, hLfield', hfield]

/-! ### The generic Hermite reduction as a field identity `D(g) + hₛ = fₙ`

`cHermiteReduceTowerG Dt fuel a d = ((gnum, gden), (hNum, Dstar))` reconstructs the normal part `fₙ = a/d`
as `D(g) + hₛ` with `g = gnum/gden` the rational part and `hₛ = hNum/Dstar` the simple residual. Its
internal component relations (`gprimeNum`, `resNum`, `resDen`, `hNum = (resNum·Dstar)/resDen`) are
**identical** to the QFunNZ `cHermiteReduceTower`'s — so the cleared identity proof of
`cHermiteReduceTower_cleared_identity` transports verbatim (it only uses those relations and the
exact-division certificate, never the squarefree-factorization's gcd). We assemble the field identity
through the already-generic field-clearing `hermite_field_div_of_cleared` and the quotient rule
`towerFractionFieldDeriv_div`, exactly as `cHermiteReduceTower_field_identity`. -/

/-- **The generic Hermite cleared identity** over ℚ(x) (all inputs, under the exact-division certificate):
for components `((gnumR, gdenR), (_, DstarR)) = cHermiteReduceTowerG Dt fuel a d` and the engine's internal
`gprimeNum = D(gnumR)·gdenR − gnumR·D(gdenR)`, `resNum = a·gdenR² − d·gprimeNum`, `resDen = d·gdenR²`,
`hNumR = (resNum·DstarR)/resDen` (`D = cmonomialDeriv Dt`), under the exact-division certificate
(`resDen ∣ resNum·DstarR`, nonzero divisor, fuel), the cleared identity `(gprimeNum·DstarR + hNumR·gdenR²)·d
= a·(gdenR²·DstarR)` holds in `(RatFunc ℚ)[X]`. The generic mirror of `cHermiteReduceTower_cleared_identity`
— the proof is the same `toPolyG` ring algebra (`hermiteTower_cleared_of_exact` + `toPolyG_cdivG_exact_mul`),
the component relations being identical to the QFunNZ engine's. -/
theorem cHermiteReduceTowerG_cleared_identity (Dt : CPolyG QFunNZ) (fuel : ℕ) (a d : CPolyG QFunNZ)
    (gnumR gdenR DstarR gprimeNum resNum resDen hNumR : CPolyG QFunNZ)
    (_hgnum : gnumR = (cHermiteReduceTowerG Dt fuel a d).1.1)
    (_hgden : gdenR = (cHermiteReduceTowerG Dt fuel a d).1.2)
    (_hDstar : DstarR = (cHermiteReduceTowerG Dt fuel a d).2.2)
    (hgprime : gprimeNum
      = csubG (cmulG (cmonomialDeriv Dt gnumR) gdenR) (cmulG gnumR (cmonomialDeriv Dt gdenR)))
    (hresNum : resNum = csubG (cmulG a (cmulG gdenR gdenR)) (cmulG d gprimeNum))
    (hresDen : resDen = cmulG d (cmulG gdenR gdenR))
    (hhNum : hNumR = cdivG fuel (cmulG resNum DstarR) resDen)
    (hq0 : cnormG resDen ≠ [])
    (hfuel : (cnormG (cmulG resNum DstarR) : List QFunNZ).length ≤ fuel)
    (hdvd : toPolyG resDen ∣ toPolyG (cmulG resNum DstarR)) :
    ((toPolyG (cmonomialDeriv Dt gnumR) * toPolyG gdenR
        - toPolyG gnumR * toPolyG (cmonomialDeriv Dt gdenR)) * toPolyG DstarR
        + toPolyG hNumR * (toPolyG gdenR * toPolyG gdenR)) * toPolyG d
      = toPolyG a * ((toPolyG gdenR * toPolyG gdenR) * toPolyG DstarR) := by
  -- the exact-division witness `toPolyG hNumR · toPolyG resDen = toPolyG (resNum·Dstar)`
  have hwit0 : toPolyG hNumR * toPolyG resDen = toPolyG (cmulG resNum DstarR) := by
    rw [hhNum]; exact toPolyG_cdivG_exact_mul fuel (cmulG resNum DstarR) resDen hq0 hfuel hdvd
  have hgp : toPolyG gprimeNum
      = toPolyG (cmonomialDeriv Dt gnumR) * toPolyG gdenR
          - toPolyG gnumR * toPolyG (cmonomialDeriv Dt gdenR) := by
    rw [hgprime, toPolyG_csubG, toPolyG_cmulG, toPolyG_cmulG]
  have hwit : toPolyG hNumR * (toPolyG d * (toPolyG gdenR * toPolyG gdenR))
      = (toPolyG a * (toPolyG gdenR * toPolyG gdenR)
          - toPolyG d * toPolyG gprimeNum) * toPolyG DstarR := by
    have hlhs : toPolyG resDen = toPolyG d * (toPolyG gdenR * toPolyG gdenR) := by
      rw [hresDen, toPolyG_cmulG, toPolyG_cmulG]
    have hrhs : toPolyG (cmulG resNum DstarR)
        = (toPolyG a * (toPolyG gdenR * toPolyG gdenR) - toPolyG d * toPolyG gprimeNum)
            * toPolyG DstarR := by
      rw [hresNum, toPolyG_cmulG, toPolyG_csubG, toPolyG_cmulG, toPolyG_cmulG, toPolyG_cmulG]
    rw [← hlhs, hwit0, hrhs]
  rw [hgp] at hwit
  linear_combination hwit

/-- **The generic Hermite reduction as a field identity** `D(gₕ) + hₛ = fₙ` over the tower fraction field
`RatFunc (RatFunc ℚ)`: writing `((gnum, gden), (hNum, Dstar)) = cHermiteReduceTowerG Dt fuel a d`, the
rational part `gₕ = towerAlg(gnum)/towerAlg(gden)` and the simple residual `hₛ = towerAlg(hNum)/towerAlg(Dstar)`
satisfy `towerFractionFieldDeriv Dt gₕ + hₛ = towerAlg(a)/towerAlg(d)`. Composes the generic cleared identity
`cHermiteReduceTowerG_cleared_identity` with the (already-generic) field clearing
`hermite_field_div_of_cleared` and the quotient rule `towerFractionFieldDeriv_div`. The generic mirror of
`cHermiteReduceTower_field_identity`, gated on the same transparent exact-division/nonzero-divisor/fuel
preconditions plus nonzero `gden, Dstar, d`. -/
theorem cHermiteReduceTowerG_field_identity (Dt : CPolyG QFunNZ) (fuel : ℕ) (a d : CPolyG QFunNZ)
    (gnumR gdenR DstarR gprimeNum resNum resDen hNumR : CPolyG QFunNZ)
    (hgnum : gnumR = (cHermiteReduceTowerG Dt fuel a d).1.1)
    (hgden : gdenR = (cHermiteReduceTowerG Dt fuel a d).1.2)
    (hDstar : DstarR = (cHermiteReduceTowerG Dt fuel a d).2.2)
    (hgprime : gprimeNum
      = csubG (cmulG (cmonomialDeriv Dt gnumR) gdenR) (cmulG gnumR (cmonomialDeriv Dt gdenR)))
    (hresNum : resNum = csubG (cmulG a (cmulG gdenR gdenR)) (cmulG d gprimeNum))
    (hresDen : resDen = cmulG d (cmulG gdenR gdenR))
    (hhNum : hNumR = cdivG fuel (cmulG resNum DstarR) resDen)
    (hq0 : cnormG resDen ≠ [])
    (hfuel : (cnormG (cmulG resNum DstarR) : List QFunNZ).length ≤ fuel)
    (hdvd : toPolyG resDen ∣ toPolyG (cmulG resNum DstarR))
    (hgdenne : toPolyG gdenR ≠ 0) (hDstarne : toPolyG DstarR ≠ 0) (hdne : toPolyG d ≠ 0) :
    towerFractionFieldDeriv Dt (towerAlg (toPolyG gnumR) / towerAlg (toPolyG gdenR))
        + towerAlg (toPolyG hNumR) / towerAlg (toPolyG DstarR)
      = towerAlg (toPolyG a) / towerAlg (toPolyG d) := by
  have hcleared := cHermiteReduceTowerG_cleared_identity Dt fuel a d gnumR gdenR DstarR gprimeNum
    resNum resDen hNumR hgnum hgden hDstar hgprime hresNum hresDen hhNum hq0 hfuel hdvd
  rw [towerFractionFieldDeriv_div]
  set P : (CFieldSpec.K QFunNZ)[X] :=
    Differential.implicitDeriv (toPolyG Dt) (toPolyG gnumR) * toPolyG gdenR
      - toPolyG gnumR * Differential.implicitDeriv (toPolyG Dt) (toPolyG gdenR) with hP
  have hcleared' : (P * toPolyG DstarR + toPolyG hNumR * (toPolyG gdenR * toPolyG gdenR)) * toPolyG d
      = toPolyG a * (toPolyG gdenR * toPolyG gdenR * toPolyG DstarR) := by
    rw [hP, ← toPolyG_cmonomialDeriv, ← toPolyG_cmonomialDeriv]
    linear_combination hcleared
  rw [show towerAlg (Differential.implicitDeriv (toPolyG Dt) (toPolyG gnumR)) * towerAlg (toPolyG gdenR)
        - towerAlg (toPolyG gnumR) * towerAlg (Differential.implicitDeriv (toPolyG Dt) (toPolyG gdenR))
      = towerAlg P by rw [hP, map_sub, map_mul, map_mul]]
  exact hermite_field_div_of_cleared P (toPolyG DstarR) (toPolyG gdenR) (toPolyG hNumR) (toPolyG d)
    (toPolyG a) hgdenne hDstarne hdne hcleared'

end DeepWiki.SymbolicIntegration
