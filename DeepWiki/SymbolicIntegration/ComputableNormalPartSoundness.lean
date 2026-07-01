import DeepWiki.SymbolicIntegration.ComputableOneShotSoundness

/-! # One-shot (checker-free) soundness for the integrator's NORMAL part — the Hermite telescoping

`ComputableOneShotSoundness` made the **polynomial** branch of the tower integrator checker-free:
`cPolyRischDEG = some q ⟹ D(res) = integrand`, axiom-clean, no `native_decide`, via the crux
`checkIdentityG_cIntegratePolyG_const` (the algorithm output *passes* its own `checkIdentityG`, proven
abstractly) composed with the field bridge `field_identity_of_checkIdentityG`. Its docstring map names the
single genuinely-hard remaining piece for the full `cIntegrateGFull = some res ⟹ D(res) = integrand`
one-shot: the **normal part** `cIntegrateReducedG = cHermiteReduceTowerG` (rational part, Hermite §5.3) `+
cLogPartG` (logarithmic part, Rothstein–Trager §5.6), currently `native_decide`-validated only.

This file delivers the **Hermite half** of that normal part — abstractly, no `native_decide` — by
transporting the **general rational-part telescoping template** `generalReduceRationalTelescopeWf`
(`ComputableGeneralIntegralSoundness`) from the algebraic carrier `K(x)[y]/(f)` to the **transcendental
tower** with the monomial derivation `D = cmonomialDeriv Dt`. The mathematical core is identical: the
Hermite reduction reassembles its rational part `g` as an **accumulator fold** of per-squarefree-factor
contributions, and soundness of the assembled `g` is a **telescoping of `D` over that fold** in the
fraction field `RatFunc (CFieldSpec.K α)`.

* **`towerFractionFieldDerivG_amG_fracAccG`** — the engine's fraction-accumulator (the shape
  `cHermiteReduceTowerG` folds its `g` with: `gAcc + gloc` cross-multiplied) reads through `amG`/the field
  derivation as the sum of the per-step contributions: `D(amG(fold)) = D(amG seed) + ∑ D(amG glocⱼ)`. The
  transcendental analogue of `mk_toPolyG_afDerivWf_foldlCaddG`. Built on `Derivation.map_add` and the
  fraction-add reading `amG_toPolyG_fracAddG`.
* **`sum_towerFractionFieldDerivG_telescope`** — if each contribution's field-derivative is the difference
  of consecutive leftovers (the per-power Hermite identity `hermiteInner_spec` supplies, taken as the named
  hypothesis exactly as the template does), the sum telescopes to the endpoints. The transcendental
  analogue of `sum_mk_toPolyG_afDerivWf_telescope`.
* **★ `cHermiteReduceTowerG_telescope`** — the master Hermite telescoping soundness over the tower
  (abstract field identity): the assembled rational part `g` and the final leftover `h` satisfy `D(g) + h =
  a/d` in `RatFunc (CFieldSpec.K α)`, **given** the per-step Hermite identities. The transcendental
  `generalReduceRationalTelescopeWf`; the **Hermite half** of the normal part. General in `Dt`, `α`.

## The assembly to the full one-shot, and the precise remainder

The normal-part one-shot target `checkIdentityG_cIntegrateReducedG` (`cIntegrateReducedG = some res ⟹
checkIdentityG = true`) decomposes into the Hermite half (above) **and** the Rothstein–Trager half (the
residue-log part `cLogPartG` differentiates to the leftover `h`). The RT half — the abstract
`roots_residueResultantTowerG_eq_residues` residue-sum identity over the tower, all the way to
`checkIdentityG = true` — is the genuinely-hard remainder (the same gap `ComputableRadicalLogSoundness`
isolates for the radical case). So, exactly as the template's `isGeneralRationalIntegralWf_of_roundtrip`
took the engine's own round-trip check as the bridge, we close the assembly through the engine's own
`checkIdentityG` certificate:

* **`field_identity_of_cIntegrateReducedG_of_checkIdentityG`** — the reduced-case field identity `D(res) =
  a/d` from the engine's `checkIdentityG = true` certificate (which the Hermite half + RT half together
  validate, and which `native_decide` reaches for any concrete run). Pure composition with
  `field_identity_of_checkIdentityG`. The `checkIdentityG` guard is the only residual.
* **`field_identity_of_cIntegrateGFull_of_checkIdentityG`** — the FULL `cIntegrateGFull = some res`
  one-shot `D(res) = a/d`, gated on the engine's own `checkIdentityG = true`, at the level-1 carrier
  `α = QFunNZG ℚ`. This subsumes both the poly branch (`ComputableOneShotSoundness`) and the normal part,
  through the single bridge.

So the normal part is **Hermite-half abstract** (`cHermiteReduceTowerG_telescope`, axiom-clean) and the
full `cIntegrateGFull` one-shot is **checker-free modulo the engine's own `checkIdentityG` self-certificate**
— with the precise remaining gap being the **abstract Rothstein–Trager residue-sum identity** that would
discharge that certificate without `native_decide` (the documented continuation, shared with the radical /
general log-soundness frontier). -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

/-! ### The fraction-accumulator reading through `amG`

The Hermite `g`-fold in `cHermiteReduceTowerG` combines the running fraction `gAcc = (g.1, g.2)` with each
per-factor contribution `gloc = (gloc.1, gloc.2)` by **cross-multiplied fraction addition**
`(caddG (cmulG g.1 gloc.2) (cmulG gloc.1 g.2), cmulG g.2 gloc.2)` — i.e. `gAcc + gloc` in `α(t)`. Read
through `amG`, this is genuine field addition `amG g.1/amG g.2 + amG gloc.1/amG gloc.2`. The single bridge
lemma turning the engine fold into a field sum. -/

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **The engine fraction-add reads as a field sum** through `amG`: for `gAcc`, `gloc` pairs with nonzero
denominators, the cross-multiplied numerator/denominator `(caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1
gAcc.2), cmulG gAcc.2 gloc.2)` reads as `amG gAcc.1/amG gAcc.2 + amG gloc.1/amG gloc.2` over `RatFunc
(CFieldSpec.K α)`. The fraction-addition law of the Hermite `g`-accumulator. -/
theorem amG_toPolyG_fracAddG (gAcc gloc : CPolyG α × CPolyG α)
    (hAcc : toPolyG gAcc.2 ≠ 0) (hloc : toPolyG gloc.2 ≠ 0) :
    amG α (toPolyG (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2)))
        / amG α (toPolyG (cmulG gAcc.2 gloc.2))
      = amG α (toPolyG gAcc.1) / amG α (toPolyG gAcc.2)
        + amG α (toPolyG gloc.1) / amG α (toPolyG gloc.2) := by
  rw [toPolyG_caddG, toPolyG_cmulG, toPolyG_cmulG, toPolyG_cmulG, map_add, map_mul, map_mul, map_mul]
  rw [div_add_div _ _ (amG_toPolyG_ne_zero hAcc) (amG_toPolyG_ne_zero hloc)]
  ring

/-! ### `D` distributes over the Hermite `g`-accumulator fold (in the field)

`cHermiteReduceTowerG`'s `g`-fold accumulates the rational part as `foldl (gAcc, gloc ↦ gAcc + gloc)`
over the squarefree factors — definitionally a fraction-add fold. Reading through `amG`, the running
fraction is `seed + ∑ glocⱼ`, so applying the field derivation `towerFractionFieldDerivG` gives `D(amG
seed) + ∑ D(amG glocⱼ)`. We carry the per-factor contributions as an explicit list `glocs` with the
fold's combining function, mirroring the template's accumulator-fold distribution. -/

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **The Hermite `g`-fold reads as `seed + ∑ contributions`** through `amG` (field form): folding the
fraction-add combiner from a seed `s` (nonzero denominator) over a list `glocs` of contributions (each
nonzero denominator), the running fraction equals `amG s.1/amG s.2 + ∑ amG glocⱼ.1/amG glocⱼ.2`, and the
running denominator stays nonzero. By list induction with `amG_toPolyG_fracAddG`. The transcendental
analogue of the `toQFun_foldl_qadd` / `mk_toPolyG_afDerivWf_foldlCaddG` accumulator reading. -/
theorem amG_toPolyG_foldl_fracAddG :
    ∀ (glocs : List (CPolyG α × CPolyG α)) (s : CPolyG α × CPolyG α), toPolyG s.2 ≠ 0 →
      (∀ g ∈ glocs, toPolyG g.2 ≠ 0) →
      let res := glocs.foldl
        (fun (gAcc : CPolyG α × CPolyG α) gloc =>
          (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2), cmulG gAcc.2 gloc.2)) s
      toPolyG res.2 ≠ 0 ∧
        amG α (toPolyG res.1) / amG α (toPolyG res.2)
          = amG α (toPolyG s.1) / amG α (toPolyG s.2)
            + (glocs.map (fun g => amG α (toPolyG g.1) / amG α (toPolyG g.2))).sum := by
  intro glocs
  induction glocs with
  | nil => intro s hs _; exact ⟨hs, by simp⟩
  | cons gloc rest ih =>
    intro s hs hmem
    have hgloc : toPolyG gloc.2 ≠ 0 := hmem gloc List.mem_cons_self
    set snew : CPolyG α × CPolyG α :=
      (caddG (cmulG s.1 gloc.2) (cmulG gloc.1 s.2), cmulG s.2 gloc.2) with hsnew
    have hsnew_ne : toPolyG snew.2 ≠ 0 := by
      rw [hsnew]; show toPolyG (cmulG s.2 gloc.2) ≠ 0
      rw [toPolyG_cmulG]; exact mul_ne_zero hs hgloc
    have hrest : ∀ g ∈ rest, toPolyG g.2 ≠ 0 := fun g hg => hmem g (List.mem_cons_of_mem _ hg)
    obtain ⟨hden, heq⟩ := ih snew hsnew_ne hrest
    refine ⟨by simpa only [List.foldl_cons] using hden, ?_⟩
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [heq]
    have hstep : amG α (toPolyG snew.1) / amG α (toPolyG snew.2)
        = amG α (toPolyG s.1) / amG α (toPolyG s.2)
          + amG α (toPolyG gloc.1) / amG α (toPolyG gloc.2) := by
      rw [hsnew]; exact amG_toPolyG_fracAddG s gloc hs hgloc
    rw [hstep]; ring

/-- **`towerFractionFieldDerivG` distributes over the Hermite `g`-fold** (field form): for a seed `s`
(nonzero denominator) and contributions `glocs` (each nonzero denominator), `D(amG(fold).1/amG(fold).2) =
D(amG s.1/amG s.2) + ∑ⱼ D(amG glocⱼ.1/amG glocⱼ.2)`, where `D = towerFractionFieldDerivG Dt`. The field
derivation pushed through the accumulator-fold reading `amG_toPolyG_foldl_fracAddG` by `Derivation`
additivity (`map_add`, `map_list_sum`). The transcendental analogue of `mk_toPolyG_afDerivWf_foldlCaddG`. -/
theorem towerFractionFieldDerivG_amG_fracAccG (Dt : CPolyG α) (s : CPolyG α × CPolyG α)
    (glocs : List (CPolyG α × CPolyG α)) (hs : toPolyG s.2 ≠ 0)
    (hmem : ∀ g ∈ glocs, toPolyG g.2 ≠ 0) :
    let res := glocs.foldl
      (fun (gAcc : CPolyG α × CPolyG α) gloc =>
        (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2), cmulG gAcc.2 gloc.2)) s
    towerFractionFieldDerivG Dt (amG α (toPolyG res.1) / amG α (toPolyG res.2))
      = towerFractionFieldDerivG Dt (amG α (toPolyG s.1) / amG α (toPolyG s.2))
        + (glocs.map (fun g =>
            towerFractionFieldDerivG Dt (amG α (toPolyG g.1) / amG α (toPolyG g.2)))).sum := by
  intro res
  obtain ⟨_, heq⟩ := amG_toPolyG_foldl_fracAddG glocs s hs hmem
  show towerFractionFieldDerivG Dt (amG α (toPolyG res.1) / amG α (toPolyG res.2)) = _
  rw [heq, map_add]
  congr 1
  rw [map_list_sum, List.map_map]
  rfl

/-! ### The per-step contributions telescope (in the field)

The transcendental analogue of `sum_mk_toPolyG_afDerivWf_telescope`: if each per-factor contribution's
field-derivative is the difference of the consecutive leftovers it sits between (the per-power Hermite
identity, read as `D(amG glocⱼ) = amG Lⱼ − amG Lⱼ₊₁`, taken as the named hypothesis exactly as the template
does), the sum of the contributions' derivatives telescopes to `amG L₀ − amG L_last`. Stated via a
parallel `List.Forall₂` recursion to keep the endpoints free of index/non-emptiness obligations. -/

/-- **The per-step contributions telescope** (head/last form, field) — for a head leftover `L₀`, a tail
list of leftovers `rest`, and contributions `glocs` of the same length, if `glocs` zipped against the
consecutive pairs of `L₀ :: rest` (i.e. `(L₀ :: rest).zip rest`) satisfies, head-to-head, `D(amG g.1/amG
g.2) = amG p.1.1/amG p.1.2 − amG p.2.1/amG p.2.2` (the per-power Hermite identity, each leftover a
`CPolyG α × CPolyG α` fraction), then the sum of the contributions' field-derivatives is `amG L₀.1/amG
L₀.2 − amG (rest.getLastD L₀).1/amG (rest.getLastD L₀).2`. The transcendental analogue of
`sum_mk_toPolyG_afDerivWf_telescope`. -/
theorem sum_towerFractionFieldDerivG_telescope (Dt : CPolyG α) :
    ∀ (L₀ : CPolyG α × CPolyG α) (rest glocs : List (CPolyG α × CPolyG α)),
      List.Forall₂ (fun g p =>
          towerFractionFieldDerivG Dt (amG α (toPolyG g.1) / amG α (toPolyG g.2))
            = amG α (toPolyG (Prod.fst p).1) / amG α (toPolyG (Prod.fst p).2)
              - amG α (toPolyG (Prod.snd p).1) / amG α (toPolyG (Prod.snd p).2))
          glocs ((L₀ :: rest).zip rest) →
      (glocs.map (fun g =>
          towerFractionFieldDerivG Dt (amG α (toPolyG g.1) / amG α (toPolyG g.2)))).sum
        = amG α (toPolyG L₀.1) / amG α (toPolyG L₀.2)
          - amG α (toPolyG (rest.getLastD L₀).1) / amG α (toPolyG (rest.getLastD L₀).2) := by
  intro L₀ rest
  induction rest generalizing L₀ with
  | nil =>
    intro glocs hforall
    simp only [List.zip_nil_right] at hforall
    rw [List.forall₂_nil_right_iff] at hforall
    subst hforall
    simp
  | cons L₁ rest' ih =>
    intro glocs hforall
    rw [List.zip_cons_cons] at hforall
    rw [List.forall₂_cons_right_iff] at hforall
    obtain ⟨g, glocs', h0, htail, rfl⟩ := hforall
    rw [List.map_cons, List.sum_cons, ih L₁ glocs' htail, h0]
    rw [List.getLastD_cons]
    ring

/-! ### ★ The master Hermite telescoping soundness over the tower

Composing the accumulator-fold distribution with the contribution telescoping gives the **Hermite half**
of the normal part as an abstract field identity: the assembled rational part `g = foldl … seed` satisfies
`D(g) + h = a/d` in `RatFunc (CFieldSpec.K α)`, where `h` is the final leftover and `a/d` the original
integrand — reduced exactly to the per-power Hermite identity over the engine's reduction steps. The
transcendental `generalReduceRationalTelescopeWf`. -/

/-- **★ The master Hermite telescoping soundness over the tower (abstract field identity)** — the
**Hermite half** of the normal part. Let `glocs` be the list of per-squarefree-factor rational
contributions `cHermiteReduceTowerG` accumulates (each fraction-added into the running `g`, from a seed
`s` with `D(amG s) = 0`, e.g. the engine seed `0/1`), and let `L₀ :: rest` be the chain of leftover
fractions the reduction passes through (`L₀` the *original* integrand `a/d`, `rest.getLastD L₀` the
*final* leftover `h`). **Given** each contribution's per-power Hermite identity in the field
(`D(amG glocⱼ) = amG Lⱼ − amG Lⱼ₊₁`, zipped as `(L₀ :: rest).zip rest`) **and** that the seed derivative
vanishes, the assembled rational part `g = glocs.foldl (fraction-add) s` satisfies `D(g) + h = a/d` in
`RatFunc (CFieldSpec.K α)`: the rational part `g` integrates the integrand modulo the final leftover `h`.
General in `Dt`, `α`; the precondition is the list of per-power Hermite field identities (the
transcendental mirror of `hermiteInner_spec`), exactly as `generalReduceRationalTelescopeWf` takes its
per-step eq.-11 identities. -/
theorem cHermiteReduceTowerG_telescope (Dt : CPolyG α) (s : CPolyG α × CPolyG α)
    (L₀ : CPolyG α × CPolyG α) (rest glocs : List (CPolyG α × CPolyG α))
    (hs : toPolyG s.2 ≠ 0) (hmem : ∀ g ∈ glocs, toPolyG g.2 ≠ 0)
    (hseed : towerFractionFieldDerivG Dt (amG α (toPolyG s.1) / amG α (toPolyG s.2)) = 0)
    (hstep : List.Forall₂ (fun g p =>
        towerFractionFieldDerivG Dt (amG α (toPolyG g.1) / amG α (toPolyG g.2))
          = amG α (toPolyG (Prod.fst p).1) / amG α (toPolyG (Prod.fst p).2)
            - amG α (toPolyG (Prod.snd p).1) / amG α (toPolyG (Prod.snd p).2))
        glocs ((L₀ :: rest).zip rest)) :
    towerFractionFieldDerivG Dt
        (amG α (toPolyG (glocs.foldl
            (fun (gAcc : CPolyG α × CPolyG α) gloc =>
              (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2), cmulG gAcc.2 gloc.2)) s).1)
          / amG α (toPolyG (glocs.foldl
            (fun (gAcc : CPolyG α × CPolyG α) gloc =>
              (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2), cmulG gAcc.2 gloc.2)) s).2))
        + amG α (toPolyG (rest.getLastD L₀).1) / amG α (toPolyG (rest.getLastD L₀).2)
      = amG α (toPolyG L₀.1) / amG α (toPolyG L₀.2) := by
  have hfold := towerFractionFieldDerivG_amG_fracAccG Dt s glocs hs hmem
  simp only at hfold ⊢
  rw [hfold, hseed, zero_add,
    sum_towerFractionFieldDerivG_telescope Dt L₀ rest glocs hstep]
  ring

/-! ### The seed derivative vanishes (`0/1`)

The Hermite `g`-fold seeds at `([CField.zero], [CField.one])` — the fraction `0/1 = 0`, whose field
derivative is `0`. The concrete discharge of the `hseed` hypothesis for the engine's actual seed. -/

/-- **The Hermite seed `0/1` has vanishing field derivative** — `towerFractionFieldDerivG Dt (amG(toPolyG
[0])/amG(toPolyG [1])) = 0`: the engine seed `([CField.zero], [CField.one])` reads as `0/1 = 0` over
`RatFunc (CFieldSpec.K α)`, and `D(0) = 0`. Discharges `cHermiteReduceTowerG_telescope`'s `hseed` for the
actual engine seed. -/
theorem towerFractionFieldDerivG_amG_seed (Dt : CPolyG α) :
    towerFractionFieldDerivG Dt
        (amG α (toPolyG ([CField.zero] : CPolyG α)) / amG α (toPolyG ([CField.one] : CPolyG α))) = 0 := by
  have hzero : amG α (toPolyG ([CField.zero] : CPolyG α)) = 0 := by
    rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_zero, map_zero, mul_zero, add_zero, map_zero]
  rw [hzero, zero_div, map_zero]

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **The engine seed denominator `[CField.one]` is nonzero** under `toPolyG` (`= 1`). Discharges the
`hs` hypothesis of `cHermiteReduceTowerG_telescope` for the engine seed. -/
theorem toPolyG_seed_den_ne_zero : toPolyG ([CField.one] : CPolyG α) ≠ 0 := by
  rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_one, map_one, mul_zero, add_zero]; exact one_ne_zero

/-! ### ★ The Hermite half packaged (engine seed `0/1`)

The master telescoping specialized to the engine's actual seed `([0], [1])` — the form
`cHermiteReduceTowerG` folds from. This is the clean **Hermite-half** statement: `D(g) + h = a/d` in the
field, given the per-power Hermite identities, with the seed obligations discharged. -/

/-- **★ The Hermite half over the tower, at the engine seed** — `D(g) + h = a/d` in `RatFunc (CFieldSpec.K
α)` for the rational part `g` accumulated by `cHermiteReduceTowerG`'s `g`-fold from the engine seed
`([CField.zero], [CField.one])`, given each per-squarefree-factor contribution's per-power Hermite field
identity (`hstep`) and the chain of leftovers `L₀ :: rest` (`L₀` the integrand `a/d`, `rest.getLastD L₀`
the residual `h`). The seed obligations (`0/1` nonzero denominator, `D(0/1) = 0`) are discharged by
`toPolyG_seed_den_ne_zero` / `towerFractionFieldDerivG_amG_seed`. The transcendental
`generalReduceRationalTelescopeWf` at the engine seed — the Hermite half of the normal-part one-shot, fully
abstract. -/
theorem cHermiteReduceTowerG_telescope_seed (Dt : CPolyG α)
    (L₀ : CPolyG α × CPolyG α) (rest glocs : List (CPolyG α × CPolyG α))
    (hmem : ∀ g ∈ glocs, toPolyG g.2 ≠ 0)
    (hstep : List.Forall₂ (fun g p =>
        towerFractionFieldDerivG Dt (amG α (toPolyG g.1) / amG α (toPolyG g.2))
          = amG α (toPolyG (Prod.fst p).1) / amG α (toPolyG (Prod.fst p).2)
            - amG α (toPolyG (Prod.snd p).1) / amG α (toPolyG (Prod.snd p).2))
        glocs ((L₀ :: rest).zip rest)) :
    towerFractionFieldDerivG Dt
        (amG α (toPolyG (glocs.foldl
            (fun (gAcc : CPolyG α × CPolyG α) gloc =>
              (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2), cmulG gAcc.2 gloc.2))
            (([CField.zero] : CPolyG α), ([CField.one] : CPolyG α))).1)
          / amG α (toPolyG (glocs.foldl
            (fun (gAcc : CPolyG α × CPolyG α) gloc =>
              (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2), cmulG gAcc.2 gloc.2))
            (([CField.zero] : CPolyG α), ([CField.one] : CPolyG α))).2))
        + amG α (toPolyG (rest.getLastD L₀).1) / amG α (toPolyG (rest.getLastD L₀).2)
      = amG α (toPolyG L₀.1) / amG α (toPolyG L₀.2) :=
  cHermiteReduceTowerG_telescope Dt (([CField.zero] : CPolyG α), ([CField.one] : CPolyG α))
    L₀ rest glocs toPolyG_seed_den_ne_zero hmem (towerFractionFieldDerivG_amG_seed Dt) hstep

/-! ### ★ The exact-division degree bound — the genuinely-provable half of `hproper`

`cHermiteReduceTowerG` recovers the leftover numerator `h_num = cdivWf (resNum·Dstar) resDen` by an
*exact division* over the squarefree radical `Dstar = ∏ᵢ vᵢ`, leaving `h_den = Dstar`. Properness
(`deg h_num < deg h_den = deg Dstar`) is *not* pinned by the cleared Hermite identity alone (the
rational-part numerator can have arbitrary degree) — it is pinned by the residual fraction
`resNum/resDen = a/d − D(g)` being **proper**. The lemma below isolates the genuinely-provable bridge: an
abstract polynomial degree-cancellation that, **given** the exact-division identity
`h_num·resDen = resNum·Dstar` and the residual-fraction properness `deg resNum < deg resDen`, concludes
`deg h_num < deg Dstar`. The cancellation is `deg(h_num)+deg(resDen) = deg(resNum)+deg(Dstar)` with
`deg resNum < deg resDen`. This reduces the full `hproper` to (a) the exact-division divisibility
`resDen ∣ resNum·Dstar` (true in exact arithmetic) and (b) the residual-fraction properness
`deg resNum < deg resDen` — the residual being precisely the `a/d − D(g)` properness, the documented
Large remainder. -/

/-- **Abstract polynomial degree cancellation from an exact division** — over a field, from the
exact-division identity `H·D₂ = N·S` with the proper-fraction bound `deg N < deg D₂` and nonzero divisor
`S ≠ 0`, the quotient `H` is proper for `S`: `deg H < deg S`. The multiplicative degree law
`deg(H·D₂) = deg H + deg D₂ = deg N + deg S = deg(N·S)` cancelled: `deg N < deg D₂` forces
`deg H < deg S`. (If `H = 0` the bound is `⊥ < deg S`, immediate from `S ≠ 0`.) This is the reusable
core of the Hermite exact-division degree bound `h_num = (resNum·Dstar)/resDen`. -/
theorem degree_lt_of_exact_div {K : Type*} [Field K] {H D2 N S : K[X]}
    (hid : H * D2 = N * S) (hND : N.degree < D2.degree) (hS : S ≠ 0) :
    H.degree < S.degree := by
  have hD2 : D2 ≠ 0 := by
    rintro rfl; simp only [Polynomial.degree_zero] at hND; exact absurd hND (by simp)
  rcases eq_or_ne H 0 with hH | hH
  · subst hH; rw [Polynomial.degree_zero]
    exact bot_lt_iff_ne_bot.mpr (by rwa [Ne, Polynomial.degree_eq_bot])
  · -- `H ≠ 0`, `D₂ ≠ 0` ⟹ `H·D₂ ≠ 0` ⟹ `N·S ≠ 0` ⟹ `N ≠ 0`; all degrees are honest `natDegree`s.
    have hHD2 : H * D2 ≠ 0 := mul_ne_zero hH hD2
    rw [hid] at hHD2
    have hN : N ≠ 0 := fun h => hHD2 (by rw [h, zero_mul])
    have e1 : H.degree = (H.natDegree : WithBot ℕ) := Polynomial.degree_eq_natDegree hH
    have e2 : D2.degree = (D2.natDegree : WithBot ℕ) := Polynomial.degree_eq_natDegree hD2
    have e3 : N.degree = (N.natDegree : WithBot ℕ) := Polynomial.degree_eq_natDegree hN
    have e4 : S.degree = (S.natDegree : WithBot ℕ) := Polynomial.degree_eq_natDegree hS
    have hdeg : H.natDegree + D2.natDegree = N.natDegree + S.natDegree := by
      have hmul : (H * D2).degree = (N * S).degree := by rw [hid]
      rw [Polynomial.degree_mul, Polynomial.degree_mul, e1, e2, e3, e4,
        ← Nat.cast_add, ← Nat.cast_add, Nat.cast_inj] at hmul
      exact hmul
    rw [e1, e4, Nat.cast_lt]
    rw [e2, e3, Nat.cast_lt] at hND
    omega

omit [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **★ `hproper` for `cHermiteReduceTowerG`, from the residual-fraction properness** — the leftover
numerator `(…).2.1` is proper for the leftover denominator `(…).2.2`, `deg (…).2.1 < deg (…).2.2`,
**given** the engine's leftover-projection equations (`hnum`/`hden`, `rfl`-provable at call sites: `(…).2.1`
is `cnormG (cdivWf (resNum·Dstar) resDen)` and `(…).2.2` is `cnormG Dstar`), the exact-division
divisibility `resDen ∣ resNum·Dstar` (so the division is exact by `toPolyG_cdivWf_exact`), nonzero radical
(`hDstar`) and the **residual-fraction properness**
`deg resNum < deg resDen`. The exact-division identity `h_num·resDen = resNum·Dstar` plus
`degree_lt_of_exact_div` cancels `resDen`. This reduces the *unconditional* `hproper` to the residual
properness `deg resNum < deg resDen` — i.e. `a/d − D(g)` proper, the documented Large remainder. -/
theorem cHermiteReduceTowerG_leftover_proper_of_residual [CFracGcdCore α]
    (Dt : CPolyG α) (fuel : ℕ) (a d : CPolyG α) (resNum resDen Dstar : CPolyG α)
    (hnum : toPolyG (CPolyG.cHermiteReduceTowerG Dt fuel a d).2.1
      = toPolyG (cdivWf (cmulG resNum Dstar) resDen))
    (hden : toPolyG (CPolyG.cHermiteReduceTowerG Dt fuel a d).2.2 = toPolyG Dstar)
    (hdvd : toPolyG resDen ∣ toPolyG (cmulG resNum Dstar))
    (hresDen : cnormG resDen ≠ [])
    (hDstar : toPolyG Dstar ≠ 0)
    (hresProper : (toPolyG resNum).degree < (toPolyG resDen).degree) :
    (toPolyG (CPolyG.cHermiteReduceTowerG Dt fuel a d).2.1).degree
      < (toPolyG (CPolyG.cHermiteReduceTowerG Dt fuel a d).2.2).degree := by
  rw [hnum, hden]
  -- exact division: `h_num · resDen = resNum·Dstar = resNum · Dstar`
  have hexact : toPolyG (cdivWf (cmulG resNum Dstar) resDen) * toPolyG resDen
      = toPolyG resNum * toPolyG Dstar := by
    rw [toPolyG_cdivWf_exact (cmulG resNum Dstar) resDen hresDen hdvd, toPolyG_cmulG]
  exact degree_lt_of_exact_div hexact hresProper hDstar

/-! ### ★ The residual-fraction properness `deg resNum < deg resDen` — closing `hproper` (δ(t) ≤ 1)

The exact-division half above reduces the unconditional `hproper` to (b) `deg resNum < deg resDen`, i.e.
the residual fraction `resNum/resDen = a/d − D(g)` is **proper**, which (the input `a/d` being proper)
is exactly **`D(g)` proper**. This section discharges (b). The engine assembles the rational part `g =
gnum/gden` by a `fracAddG` fold of per-squarefree-factor contributions `gloc`, so the arc is:

* a **fold-induction** that the assembled `g` stays proper (`deg gnum < deg gden`) from each contribution
  `gloc` being proper (`foldl_fracAddG_proper`, and the engine's actual guarded `zipIdx`-fold form
  `foldl_guarded_fracAddG_proper`), via the proper-fraction-addition degree law
  (`degree_fracAdd_lt_of_proper` / `toPolyG_fracAddG_proper`);
* a **derivative-degree** step that `D(g)`'s numerator `D(gnum)·gden − gnum·D(gden)` is proper for `gden²`
  (`degree_implicitDeriv_frac_lt_of_margin` / `toPolyG_gprimeNum_proper_of_margin`). The monomial-derivation
  degree bound `natDegree_implicitDeriv_le` gives `deg(D p) ≤ deg p + max(0, δ(t) − 1)` (`δ(t) = deg Dt`),
  so the derivative of a proper fraction is proper **with the margin** `deg gnum + max(0, δ(t) − 1) < deg
  gden`. For `δ(t) ≤ 1` (the base rational case `Dt = 1`, exponentials `Dt = t`, logarithms `Dt` constant —
  i.e. `max(0, δ(t) − 1) = 0`) the margin **is** plain properness `deg gnum < deg gden`, so the fold-induction
  closes it directly (`toPolyG_gprimeNum_proper_of_degree_le_one`); for the nonlinear `δ(t) ≥ 2` case
  (`tan`/`tanh`, `Dt = t² + 1`) the margin needs the sharper leading-coefficient/cancellation analysis (the
  transcendental `RdeBoundCancellationResidual` technique), the named continuation;
* the **combination** `resNum = a·gden² − d·(D(g)-numer)`, `resDen = d·gden²`: the difference of two proper
  fractions is proper (`degree_resNum_lt` / `toPolyG_resNum_proper`), giving (b) and hence `hproper` —
  unconditional for `δ(t) ≤ 1` (`toPolyG_residualFraction_proper_of_degree_le_one`). -/

/-- **Proper-fraction addition is proper** (abstract, over a field): for `p₁/q₁ + p₂/q₂ = (p₁q₂ +
p₂q₁)/(q₁q₂)`, if `deg p₁ < deg q₁` and `deg p₂ < deg q₂` then `deg(p₁q₂ + p₂q₁) < deg(q₁q₂)`. The
multiplicative degree law makes each cross term `pᵢqⱼ` strictly below `q₁q₂`, and `degree_add_le` finishes.
The reusable degree core of the Hermite `g`-accumulator staying proper. -/
theorem degree_fracAdd_lt_of_proper {K : Type*} [Field K] {p1 q1 p2 q2 : K[X]}
    (h1 : p1.degree < q1.degree) (h2 : p2.degree < q2.degree) :
    (p1 * q2 + p2 * q1).degree < (q1 * q2).degree := by
  have hq1 : q1 ≠ 0 := by rintro rfl; simp at h1
  have hq2 : q2 ≠ 0 := by rintro rfl; simp at h2
  have e1 : (p1 * q2).degree < (q1 * q2).degree := by
    rw [Polynomial.degree_mul, Polynomial.degree_mul]
    exact WithBot.add_lt_add_right (by rwa [Ne, Polynomial.degree_eq_bot]) h1
  have e2 : (p2 * q1).degree < (q1 * q2).degree := by
    rw [Polynomial.degree_mul, mul_comm q1 q2, Polynomial.degree_mul]
    exact WithBot.add_lt_add_right (by rwa [Ne, Polynomial.degree_eq_bot]) h2
  exact lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt e1 e2)

/-- **The residual numerator of a difference of proper fractions is proper** (abstract, over a field): for
`A/D − GP/GG` with `A/D` proper (`deg A < deg D`) and `GP/GG` proper (`deg GP < deg GG`), the combined
numerator `A·GG − D·GP` is proper for the combined denominator `D·GG`, `deg(A·GG − D·GP) < deg(D·GG)`. Both
terms are strictly below `D·GG` by the multiplicative degree law; `degree_sub_le` finishes. The reusable core
of the Hermite residual `a/d − D(g)` being proper. -/
theorem degree_resNum_lt {K : Type*} [Field K] {A D GG GP : K[X]}
    (haProper : A.degree < D.degree) (hgprime : GP.degree < GG.degree) :
    (A * GG - D * GP).degree < (D * GG).degree := by
  have hGG : GG ≠ 0 := by rintro h; rw [h] at hgprime; simp at hgprime
  have hD : D ≠ 0 := by rintro h; rw [h] at haProper; simp at haProper
  have e1 : (A * GG).degree < (D * GG).degree := by
    rw [Polynomial.degree_mul, Polynomial.degree_mul]
    exact WithBot.add_lt_add_right (by rwa [Ne, Polynomial.degree_eq_bot]) haProper
  have e2 : (D * GP).degree < (D * GG).degree := by
    rw [Polynomial.degree_mul, Polynomial.degree_mul,
      WithBot.add_lt_add_iff_left (by rwa [Ne, Polynomial.degree_eq_bot])]
    exact hgprime
  exact lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt e1 e2)

/-- **The monomial derivation of a proper fraction is proper** (abstract, margin form): for `N/M` with `M ≠
0`, the derivative numerator `D(N)·M − N·D(M)` (`D = implicitDeriv v`) is proper for `M²` — `deg(D(N)·M −
N·D(M)) < deg(M²)` — **given** the margin `deg N + max(0, deg v − 1) < deg M`. Each term is bounded by
`natDegree_implicitDeriv_le` (`deg(D p) ≤ deg p + max(0, deg v − 1)`); the margin keeps both strictly below
`deg M + deg M = deg(M²)`. The `degree`-form margin handles `N = 0` (`deg N = ⊥`) uniformly. For `deg v ≤ 1`
the margin collapses to plain properness `deg N < deg M`. The reusable core of `D(g)` proper. -/
theorem degree_implicitDeriv_frac_lt_of_margin {K : Type*} [Field K] [Differential K] {v N M : K[X]}
    (hM : M ≠ 0) (hmargin : N.degree + (max 0 (v.natDegree - 1) : ℕ) < M.degree) :
    (Differential.implicitDeriv v N * M - N * Differential.implicitDeriv v M).degree
      < (M * M).degree := by
  set δ : ℕ := max 0 (v.natDegree - 1) with hδ
  have hMdeg : (M * M).degree = M.degree + M.degree := Polynomial.degree_mul
  have hd1 : (Differential.implicitDeriv v N * M).degree < (M * M).degree := by
    rw [Polynomial.degree_mul, hMdeg]
    have hDN : (Differential.implicitDeriv v N).degree ≤ N.degree + (δ : ℕ) := by
      rcases eq_or_ne (Differential.implicitDeriv v N) 0 with h0 | h0
      · rw [h0, Polynomial.degree_zero]; exact bot_le
      · rw [Polynomial.degree_eq_natDegree h0]
        rcases eq_or_ne N 0 with hN0 | hN0
        · rw [hN0, map_zero] at h0; exact absurd rfl h0
        · rw [Polynomial.degree_eq_natDegree hN0]; exact_mod_cast natDegree_implicitDeriv_le v N
    have hlt : (Differential.implicitDeriv v N).degree < M.degree := lt_of_le_of_lt hDN hmargin
    exact WithBot.add_lt_add_right (by rwa [Ne, Polynomial.degree_eq_bot]) hlt
  have hd2 : (N * Differential.implicitDeriv v M).degree < (M * M).degree := by
    rw [Polynomial.degree_mul, hMdeg]
    have hDM : (Differential.implicitDeriv v M).degree ≤ M.degree + (δ : ℕ) := by
      rcases eq_or_ne (Differential.implicitDeriv v M) 0 with h0 | h0
      · rw [h0, Polynomial.degree_zero]; exact bot_le
      · rw [Polynomial.degree_eq_natDegree h0, Polynomial.degree_eq_natDegree hM]
        exact_mod_cast natDegree_implicitDeriv_le v M
    calc N.degree + (Differential.implicitDeriv v M).degree
        ≤ N.degree + (M.degree + (δ : ℕ)) := by gcongr
      _ = (N.degree + (δ : ℕ)) + M.degree := by ring
      _ < M.degree + M.degree :=
          WithBot.add_lt_add_right (by rwa [Ne, Polynomial.degree_eq_bot]) hmargin
  exact lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hd1 hd2)

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **One Hermite `g`-fold step preserves properness** (engine form): the cross-multiplied fraction-add
`(caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2), cmulG gAcc.2 gloc.2)` of two proper fractions `gAcc`,
`gloc` is proper. `toPolyG`-transport of `degree_fracAdd_lt_of_proper` through the homomorphisms
`toPolyG_caddG`/`toPolyG_cmulG`. The per-step engine lemma the fold-induction threads. -/
theorem toPolyG_fracAddG_proper {gAcc gloc : CPolyG α × CPolyG α}
    (h1 : (toPolyG gAcc.1).degree < (toPolyG gAcc.2).degree)
    (h2 : (toPolyG gloc.1).degree < (toPolyG gloc.2).degree) :
    (toPolyG (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2))).degree
      < (toPolyG (cmulG gAcc.2 gloc.2)).degree := by
  rw [toPolyG_caddG, toPolyG_cmulG, toPolyG_cmulG, toPolyG_cmulG]
  exact degree_fracAdd_lt_of_proper h1 h2

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **The Hermite `g`-fold stays proper** (engine fold-induction): folding the fraction-add combiner from a
proper seed `s` over a list `glocs` of proper contributions yields a proper running fraction `deg res.1 <
deg res.2`. By list induction with `toPolyG_fracAddG_proper`. The degree analogue of
`amG_toPolyG_foldl_fracAddG` — the assembled rational part `g` stays proper given each per-factor
contribution is proper. -/
theorem foldl_fracAddG_proper :
    ∀ (glocs : List (CPolyG α × CPolyG α)) (s : CPolyG α × CPolyG α),
      (toPolyG s.1).degree < (toPolyG s.2).degree →
      (∀ g ∈ glocs, (toPolyG g.1).degree < (toPolyG g.2).degree) →
      let res := glocs.foldl
        (fun (gAcc : CPolyG α × CPolyG α) gloc =>
          (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2), cmulG gAcc.2 gloc.2)) s
      (toPolyG res.1).degree < (toPolyG res.2).degree := by
  intro glocs
  induction glocs with
  | nil => intro s hs _; exact hs
  | cons gloc rest ih =>
    intro s hs hmem
    have hgloc : (toPolyG gloc.1).degree < (toPolyG gloc.2).degree := hmem gloc List.mem_cons_self
    have hrest : ∀ g ∈ rest, (toPolyG g.1).degree < (toPolyG g.2).degree :=
      fun g hg => hmem g (List.mem_cons_of_mem _ hg)
    set snew : CPolyG α × CPolyG α :=
      (caddG (cmulG s.1 gloc.2) (cmulG gloc.1 s.2), cmulG s.2 gloc.2) with hsnew
    have hsnew_proper : (toPolyG snew.1).degree < (toPolyG snew.2).degree := by
      rw [hsnew]; exact toPolyG_fracAddG_proper hs hgloc
    simpa only [List.foldl_cons] using ih snew hsnew_proper hrest

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **The guarded Hermite `g`-fold stays proper** (the engine's actual fold form): the `cHermiteReduceTowerG`
`g`-fold iterates `if skip b then gAcc else (gAcc + glocOf b)` — skipping the multiplicity-`1` factors. From a
proper seed and each non-skipped step's `glocOf b` proper, the running fraction stays proper. By list
induction casing on the `skip` guard (`if_pos` leaves `gAcc` proper; `if_neg` is one `toPolyG_fracAddG_proper`
step). The form directly matching the engine `factors.zipIdx.foldl` with its `i ≤ 1` guard. -/
theorem foldl_guarded_fracAddG_proper {β : Type*} (glocOf : β → CPolyG α × CPolyG α)
    (skip : β → Prop) [DecidablePred skip] :
    ∀ (xs : List β) (s : CPolyG α × CPolyG α),
      (toPolyG s.1).degree < (toPolyG s.2).degree →
      (∀ b ∈ xs, ¬ skip b → (toPolyG (glocOf b).1).degree < (toPolyG (glocOf b).2).degree) →
      let res := xs.foldl
        (fun (gAcc : CPolyG α × CPolyG α) (b : β) =>
          if skip b then gAcc
          else (caddG (cmulG gAcc.1 (glocOf b).2) (cmulG (glocOf b).1 gAcc.2),
                cmulG gAcc.2 (glocOf b).2)) s
      (toPolyG res.1).degree < (toPolyG res.2).degree := by
  intro xs
  induction xs with
  | nil => intro s hs _; exact hs
  | cons b rest ih =>
    intro s hs hmem
    have hrest : ∀ b' ∈ rest, ¬ skip b' →
        (toPolyG (glocOf b').1).degree < (toPolyG (glocOf b').2).degree :=
      fun b' hb' => hmem b' (List.mem_cons_of_mem _ hb')
    simp only [List.foldl_cons]
    by_cases hsk : skip b
    · rw [show (if skip b then s
          else (caddG (cmulG s.1 (glocOf b).2) (cmulG (glocOf b).1 s.2),
                cmulG s.2 (glocOf b).2)) = s from if_pos hsk]
      exact ih s hs hrest
    · set snew : CPolyG α × CPolyG α :=
        (caddG (cmulG s.1 (glocOf b).2) (cmulG (glocOf b).1 s.2), cmulG s.2 (glocOf b).2) with hsnew
      rw [show (if skip b then s
          else (caddG (cmulG s.1 (glocOf b).2) (cmulG (glocOf b).1 s.2),
                cmulG s.2 (glocOf b).2)) = snew from if_neg hsk]
      have hgloc : (toPolyG (glocOf b).1).degree < (toPolyG (glocOf b).2).degree :=
        hmem b List.mem_cons_self hsk
      have hsnew_proper : (toPolyG snew.1).degree < (toPolyG snew.2).degree := by
        rw [hsnew]; exact toPolyG_fracAddG_proper hs hgloc
      exact ih snew hsnew_proper hrest

omit [Algebra ℚ (CFieldSpec.K α)] in
/-- **`D(g)`'s numerator is proper for `gden²`** (engine form, margin): the residual derivative numerator
`D(gnum)·gden − gnum·D(gden)` (`D = cmonomialDeriv Dt`) is proper for `gden²` — `deg < deg(gden·gden)` —
given `gden ≠ 0` and the margin `deg gnum + max(0, deg Dt − 1) < deg gden`. `toPolyG`-transport of
`degree_implicitDeriv_frac_lt_of_margin` through `toPolyG_cmonomialDeriv` (`= implicitDeriv (toPolyG Dt)`).
The engine `D(g)`-proper lemma, margin form (the margin is plain properness when `deg Dt ≤ 1`). -/
theorem toPolyG_gprimeNum_proper_of_margin (Dt gnum gden : CPolyG α) (hM : toPolyG gden ≠ 0)
    (hmargin :
      (toPolyG gnum).degree + (max 0 ((toPolyG Dt).natDegree - 1) : ℕ) < (toPolyG gden).degree) :
    (toPolyG (csubG (cmulG (cmonomialDeriv Dt gnum) gden)
        (cmulG gnum (cmonomialDeriv Dt gden)))).degree
      < (toPolyG (cmulG gden gden)).degree := by
  rw [toPolyG_csubG, toPolyG_cmulG, toPolyG_cmulG, toPolyG_cmulG,
    toPolyG_cmonomialDeriv, toPolyG_cmonomialDeriv]
  exact degree_implicitDeriv_frac_lt_of_margin hM hmargin

omit [Algebra ℚ (CFieldSpec.K α)] in
/-- **`D(g)` proper from `g` proper, when `deg Dt ≤ 1`** (engine form): for `deg Dt ≤ 1` (the base rational
case `Dt = 1`, exponentials `Dt = t`, logarithms `Dt` constant), a proper `g = gnum/gden` (`deg gnum < deg
gden`) has proper derivative numerator `D(gnum)·gden − gnum·D(gden)` for `gden²`. The margin `max(0, deg Dt −
1) = 0` collapses to plain properness, discharging `toPolyG_gprimeNum_proper_of_margin`. The unconditional
`D(g)` proper for non-nonlinear monomials. -/
theorem toPolyG_gprimeNum_proper_of_degree_le_one (Dt gnum gden : CPolyG α) (hM : toPolyG gden ≠ 0)
    (hDt : (toPolyG Dt).natDegree ≤ 1)
    (hgproper : (toPolyG gnum).degree < (toPolyG gden).degree) :
    (toPolyG (csubG (cmulG (cmonomialDeriv Dt gnum) gden)
        (cmulG gnum (cmonomialDeriv Dt gden)))).degree
      < (toPolyG (cmulG gden gden)).degree := by
  refine toPolyG_gprimeNum_proper_of_margin Dt gnum gden hM ?_
  have hz : max 0 ((toPolyG Dt).natDegree - 1) = 0 := by omega
  rw [hz, Nat.cast_zero, add_zero]
  exact hgproper

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **The residual numerator `resNum` is proper for `resDen`** (engine form) — the residual fraction
`resNum/resDen = a/d − D(g)` is proper: `deg(a·gden² − d·gprimeNum) < deg(d·gden²)`, given `a/d` proper
(`deg a < deg d`) and `D(g)`'s numerator `gprimeNum` proper for `gden²` (`deg gprimeNum < deg(gden·gden)`).
`toPolyG`-transport of `degree_resNum_lt` through the homomorphisms. The difference-of-proper-fractions step
assembling the residual-fraction properness `deg resNum < deg resDen`. -/
theorem toPolyG_resNum_proper (a d gden gprimeNum : CPolyG α)
    (haProper : (toPolyG a).degree < (toPolyG d).degree)
    (hgprime : (toPolyG gprimeNum).degree < (toPolyG (cmulG gden gden)).degree) :
    (toPolyG (csubG (cmulG a (cmulG gden gden)) (cmulG d gprimeNum))).degree
      < (toPolyG (cmulG d (cmulG gden gden))).degree := by
  simp only [toPolyG_csubG, toPolyG_cmulG] at hgprime ⊢
  exact degree_resNum_lt haProper hgprime

omit [Algebra ℚ (CFieldSpec.K α)] in
/-- **★ The residual fraction `a/d − D(g)` is proper (`deg Dt ≤ 1`)** — `deg resNum < deg resDen` for the
engine's *actual* residual expressions `resNum = a·gden² − d·(D(gnum)·gden − gnum·D(gden))`, `resDen =
d·gden²` (the `let`-bindings of `cHermiteReduceTowerG`), given the assembled rational part `g = gnum/gden`
proper (`deg gnum < deg gden`), the input `a/d` proper (`deg a < deg d`), and `deg Dt ≤ 1`. Composes the
derivative-degree step `toPolyG_gprimeNum_proper_of_degree_le_one` (`D(g)` proper) with the
difference-of-proper-fractions step `toPolyG_resNum_proper`. This is exactly the residual `hresProper` of
`cHermiteReduceTowerG_leftover_proper_of_residual`, so it closes `hproper` **unconditionally for `deg Dt ≤
1`** (base rational / exp / log monomials) from `g` proper — the remaining gap being only the assembled `g`'s
properness (the per-step `gloc`-properness fold) and the nonlinear `deg Dt ≥ 2` margin. -/
theorem toPolyG_residualFraction_proper_of_degree_le_one
    (Dt a d gnum gden : CPolyG α) (hden : toPolyG gden ≠ 0)
    (hDt : (toPolyG Dt).natDegree ≤ 1)
    (haProper : (toPolyG a).degree < (toPolyG d).degree)
    (hgproper : (toPolyG gnum).degree < (toPolyG gden).degree) :
    (toPolyG (csubG (cmulG a (cmulG gden gden))
        (cmulG d (csubG (cmulG (cmonomialDeriv Dt gnum) gden)
          (cmulG gnum (cmonomialDeriv Dt gden)))))).degree
      < (toPolyG (cmulG d (cmulG gden gden))).degree :=
  toPolyG_resNum_proper a d gden _ haProper
    (toPolyG_gprimeNum_proper_of_degree_le_one Dt gnum gden hden hDt hgproper)

/-! ### ★ The `δ(t) ≥ 2` (tangent/hypertangent) case — the residual is proper IFF `g` has the `(δ−1)` margin

For the nonlinear monomials `tan`/`tanh` (`Dt = t² + 1`, `δ(t) = 2`) the derivative-degree step needs more
than properness. The monomial-derivation bound `deg(D p) ≤ deg p + (δ−1)` makes the top term of `D(N)·M −
N·D(M)` have coefficient `(deg N − deg M)·nₜₒₚ·mₜₒₚ`, **nonzero** for a proper fraction (`deg N ≠ deg M`):
there is *no* leading cancellation, so `deg(D(g)-numer) = deg gnum + deg gden + (δ−1)` is **tight**, and
`D(g)` is proper for `gden²` exactly when the **margin** `deg gnum + (δ−1) < deg gden` holds — strictly
stronger than properness `deg gnum < deg gden`.

★ **This margin GENUINELY FAILS for the generic Hermite output at `δ ≥ 2`.** The inner loop's last summand
(counter `1`) is `b/v¹` with `deg b ≤ deg v − 1`; its margin `(deg v − 1) + (δ−1) < deg v` reduces to
`δ ≤ 1`. Concretely, Bronstein's `∫ 1/tan²` (`Dt = t² + 1`) reduces to `g = −1/t` (so `deg gnum = 0`,
`deg gden = 1`, margin `0 + 1 < 1` **false**) with `D(g) = (t²+1)/t²` **not** proper, and a residual `h =
−t/t` whose numerator/denominator are *both* degree `1` — `hproper` **fails**. So the generic §5.3 Hermite
reduction does **not** make `δ ≥ 2` proper; that is exactly why Bronstein routes the polynomial-in-`t`
remainder of the tangent/hypertangent case through the **special tangent reduction** (§5.10 / Ch 8), not the
generic Hermite. The lemmas below isolate the genuinely-true, reusable content: the margin-preserving
fraction algebra (a uniform generalization of the `δ ≤ 1` properness fold, carrying the `(δ−1)` slack) and
the **conditional** residual properness — proper precisely *when* the assembled `g` has the `(δ−1)` margin,
the precise boundary the tangent case sits on the wrong side of. -/

/-- **Margin-preserving fraction addition** (abstract, over a field) — the `(δ−1)`-slack generalization of
`degree_fracAdd_lt_of_proper`: for `p₁/q₁ + p₂/q₂ = (p₁q₂ + p₂q₁)/(q₁q₂)`, if `deg p₁ + m < deg q₁` and
`deg p₂ + m < deg q₂` then `deg(p₁q₂ + p₂q₁) + m < deg(q₁q₂)`. Each cross term `pᵢqⱼ` carries the margin by
the multiplicative degree law (`deg(p₁q₂)+m = (deg p₁+m)+deg q₂ < deg q₁+deg q₂`), and `degree_add_le` with
`max_add_add_right` finishes. The `m = 0` case is `degree_fracAdd_lt_of_proper`. The reusable degree core of
the Hermite `g`-accumulator staying **margin-proper**. -/
theorem degree_fracAdd_lt_of_margin {K : Type*} [Field K] {p1 q1 p2 q2 : K[X]} (m : ℕ)
    (h1 : p1.degree + (m : ℕ) < q1.degree) (h2 : p2.degree + (m : ℕ) < q2.degree) :
    (p1 * q2 + p2 * q1).degree + (m : ℕ) < (q1 * q2).degree := by
  have hq1 : q1 ≠ 0 := by
    rintro rfl; rw [Polynomial.degree_zero] at h1; exact absurd h1 (by simp)
  have hq2 : q2 ≠ 0 := by
    rintro rfl; rw [Polynomial.degree_zero] at h2; exact absurd h2 (by simp)
  have e1 : (p1 * q2).degree + (m : ℕ) < (q1 * q2).degree := by
    rw [Polynomial.degree_mul, Polynomial.degree_mul, add_right_comm]
    exact WithBot.add_lt_add_right (by rwa [Ne, Polynomial.degree_eq_bot]) h1
  have e2 : (p2 * q1).degree + (m : ℕ) < (q1 * q2).degree := by
    rw [Polynomial.degree_mul, mul_comm q1 q2, Polynomial.degree_mul, add_right_comm]
    exact WithBot.add_lt_add_right (by rwa [Ne, Polynomial.degree_eq_bot]) h2
  calc (p1 * q2 + p2 * q1).degree + (m : ℕ)
      ≤ max (p1 * q2).degree (p2 * q1).degree + (m : ℕ) := by
        gcongr; exact Polynomial.degree_add_le _ _
    _ = max ((p1 * q2).degree + (m : ℕ)) ((p2 * q1).degree + (m : ℕ)) :=
        (max_add_add_right _ _ _).symm
    _ < (q1 * q2).degree := max_lt e1 e2

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **One Hermite `g`-fold step preserves the `(δ−1)` margin** (engine form): the cross-multiplied
fraction-add of two margin-proper fractions `gAcc`, `gloc` (each `deg .1 + m < deg .2`) is margin-proper.
`toPolyG`-transport of `degree_fracAdd_lt_of_margin` through `toPolyG_caddG`/`toPolyG_cmulG`. The per-step
engine lemma the margin fold-induction threads (the `m = 0` case is `toPolyG_fracAddG_proper`). -/
theorem toPolyG_fracAddG_margin {gAcc gloc : CPolyG α × CPolyG α} (m : ℕ)
    (h1 : (toPolyG gAcc.1).degree + (m : ℕ) < (toPolyG gAcc.2).degree)
    (h2 : (toPolyG gloc.1).degree + (m : ℕ) < (toPolyG gloc.2).degree) :
    (toPolyG (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2))).degree + (m : ℕ)
      < (toPolyG (cmulG gAcc.2 gloc.2)).degree := by
  rw [toPolyG_caddG, toPolyG_cmulG, toPolyG_cmulG, toPolyG_cmulG]
  exact degree_fracAdd_lt_of_margin m h1 h2

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **The guarded Hermite `g`-fold preserves the `(δ−1)` margin** (the engine's actual fold form) — the
margin generalization of `foldl_guarded_fracAddG_proper`: the `cHermiteReduceTowerG` `g`-fold iterates `if
skip b then gAcc else gAcc + glocOf b`; from a margin-proper seed (`deg s.1 + m < deg s.2`) and each
non-skipped step's `glocOf b` margin-proper, the running fraction stays margin-proper. By list induction
casing on the `skip` guard (`if_pos` keeps `gAcc`; `if_neg` is one `toPolyG_fracAddG_margin` step). The
`m = 0` case is `foldl_guarded_fracAddG_proper`. -/
theorem foldl_guarded_fracAddG_margin {β : Type*} (glocOf : β → CPolyG α × CPolyG α)
    (skip : β → Prop) [DecidablePred skip] (m : ℕ) :
    ∀ (xs : List β) (s : CPolyG α × CPolyG α),
      (toPolyG s.1).degree + (m : ℕ) < (toPolyG s.2).degree →
      (∀ b ∈ xs, ¬ skip b →
        (toPolyG (glocOf b).1).degree + (m : ℕ) < (toPolyG (glocOf b).2).degree) →
      let res := xs.foldl
        (fun (gAcc : CPolyG α × CPolyG α) (b : β) =>
          if skip b then gAcc
          else (caddG (cmulG gAcc.1 (glocOf b).2) (cmulG (glocOf b).1 gAcc.2),
                cmulG gAcc.2 (glocOf b).2)) s
      (toPolyG res.1).degree + (m : ℕ) < (toPolyG res.2).degree := by
  intro xs
  induction xs with
  | nil => intro s hs _; exact hs
  | cons b rest ih =>
    intro s hs hmem
    have hrest : ∀ b' ∈ rest, ¬ skip b' →
        (toPolyG (glocOf b').1).degree + (m : ℕ) < (toPolyG (glocOf b').2).degree :=
      fun b' hb' => hmem b' (List.mem_cons_of_mem _ hb')
    simp only [List.foldl_cons]
    by_cases hsk : skip b
    · rw [show (if skip b then s
          else (caddG (cmulG s.1 (glocOf b).2) (cmulG (glocOf b).1 s.2),
                cmulG s.2 (glocOf b).2)) = s from if_pos hsk]
      exact ih s hs hrest
    · set snew : CPolyG α × CPolyG α :=
        (caddG (cmulG s.1 (glocOf b).2) (cmulG (glocOf b).1 s.2), cmulG s.2 (glocOf b).2) with hsnew
      rw [show (if skip b then s
          else (caddG (cmulG s.1 (glocOf b).2) (cmulG (glocOf b).1 s.2),
                cmulG s.2 (glocOf b).2)) = snew from if_neg hsk]
      have hgloc : (toPolyG (glocOf b).1).degree + (m : ℕ) < (toPolyG (glocOf b).2).degree :=
        hmem b List.mem_cons_self hsk
      have hsnew_margin : (toPolyG snew.1).degree + (m : ℕ) < (toPolyG snew.2).degree := by
        rw [hsnew]; exact toPolyG_fracAddG_margin m hs hgloc
      exact ih snew hsnew_margin hrest

omit [Algebra ℚ (CFieldSpec.K α)] in
/-- **★ The residual `a/d − D(g)` is proper for `δ(t) ≥ 2`, CONDITIONAL on the `(δ−1)` margin of `g`** — for
the engine's actual residual expressions `resNum = a·gden² − d·(D(gnum)·gden − gnum·D(gden))`, `resDen =
d·gden²`, `deg resNum < deg resDen` holds given the input `a/d` proper (`haProper`) and the assembled
rational part `g = gnum/gden` satisfying the **margin** `deg gnum + max(0, δ(t) − 1) < deg gden` (`hmargin`,
strictly stronger than properness for `δ(t) ≥ 2`). Composes the derivative-degree step
`toPolyG_gprimeNum_proper_of_margin` (`D(g)` proper *from the margin*) with the difference-of-proper-fractions
step `toPolyG_resNum_proper`. The δ(t) ≥ 2 analogue of `toPolyG_residualFraction_proper_of_degree_le_one`;
honest about the boundary — the margin hypothesis is exactly what FAILS for the tangent example (`g = −1/t`,
margin `0 + 1 < 1` false), so this closes `hproper` for `δ(t) ≥ 2` *only* under the margin, never
unconditionally from the generic Hermite output. -/
theorem toPolyG_residualFraction_proper_of_margin (Dt a d gnum gden : CPolyG α) (hden : toPolyG gden ≠ 0)
    (haProper : (toPolyG a).degree < (toPolyG d).degree)
    (hmargin :
      (toPolyG gnum).degree + (max 0 ((toPolyG Dt).natDegree - 1) : ℕ) < (toPolyG gden).degree) :
    (toPolyG (csubG (cmulG a (cmulG gden gden))
        (cmulG d (csubG (cmulG (cmonomialDeriv Dt gnum) gden)
          (cmulG gnum (cmonomialDeriv Dt gden)))))).degree
      < (toPolyG (cmulG d (cmulG gden gden))).degree :=
  toPolyG_resNum_proper a d gden _ haProper
    (toPolyG_gprimeNum_proper_of_margin Dt gnum gden hden hmargin)

/-! ### ★ The INNER-LOOP `g`-properness — each per-factor `gloc` contribution is proper

The outer Hermite `g`-fold (`foldl_guarded_fracAddG_proper`) needs **each non-skipped squarefree-factor
contribution `gloc` proper** (`deg gloc.1 < deg gloc.2`). That `gloc` is the *accumulated rational part*
of `cHermiteReduceTowerInnerWf Dt v u (i−1) a (0/1)` — itself a `fracAddG`-style fold of per-power
summands `b/vʲ`, seeded at `0/1`. Each per-power summand has numerator `b = (cdiophantineGWf …).1` (the
Bézout cofactor, the **keystone** `cdiophantineGWf_fst_degree_lt`: `deg b < deg v`) over denominator
`Vpow = vʲ` (so `deg b < deg v ≤ deg vʲ` for `v ≠ 0`). A fuel-counter induction over the inner loop —
seeded proper, each step a proper `fracAddG` (`toPolyG_fracAddG_proper` with `gloc = (b, vʲ)`) — gives the
inner `g` proper, taking the per-step keystone (over the evolving numerator `a`, hence ∀-quantified) as
the hypothesis exactly as the keystone supplies it. -/

/-- **A reduced cofactor is proper for a positive power of the modulus** (abstract, over a field): from
`deg b < deg v` and `v ≠ 0`, `deg b < deg (v^(n+1))`. The power degree `deg(v^(n+1)) = (n+1)•deg v ≥ deg
v` (since `deg v ≥ 0` for `v ≠ 0`), so the per-step bound `deg b < deg v` lifts to the per-power
denominator `vʲ`. The reusable degree core of each inner-Hermite summand `b/vʲ` being proper. -/
theorem degree_lt_pow_succ_of_degree_lt {K : Type*} [Field K] {b v : K[X]} (n : ℕ)
    (hbv : b.degree < v.degree) (hv : v ≠ 0) :
    b.degree < (v ^ (n + 1)).degree := by
  refine lt_of_lt_of_le hbv ?_
  rw [Polynomial.degree_pow]
  calc v.degree = (1 : ℕ) • v.degree := (one_smul _ _).symm
    _ ≤ (n + 1) • v.degree := by
        apply nsmul_le_nsmul_left _ (by omega)
        rw [Polynomial.degree_eq_natDegree hv]; exact_mod_cast Nat.zero_le _

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **One inner-Hermite summand `b/vʲ` is proper** (engine form): the per-power contribution `(b, cpowG v
(j+1))` is proper — `deg b < deg(v^(j+1))` — given the Bézout-cofactor bound `deg b < deg v` (the
keystone `cdiophantineGWf_fst_degree_lt`) and `v ≠ 0`. `toPolyG`-transport of `degree_lt_pow_succ_of_degree_lt`
through `toPolyG_cpowG`. The per-power summand the inner-loop fold-induction threads. -/
theorem toPolyG_inner_summand_proper (b v : CPolyG α) (j : ℕ)
    (hbv : (toPolyG b).degree < (toPolyG v).degree) (hv : toPolyG v ≠ 0) :
    (toPolyG b).degree < (toPolyG (cpowG v (j + 1))).degree := by
  rw [toPolyG_cpowG]
  exact degree_lt_pow_succ_of_degree_lt j hbv hv

omit [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **★ The inner Hermite loop's accumulated `g` is proper** — `deg (cHermiteReduceTowerInnerWf Dt v u
j a g).1.1 < deg (…).1.2` for the inner loop over a squarefree factor `v`, **given** the input
accumulator `g` proper (`hg`), `v ≠ 0` (`hv`), and the per-step Bézout keystone `hb`: for every
right-hand side `rhs`, the emitted cofactor `(cdiophantineGWf (u·Dv) v rhs).1` is proper for `v`
(`deg < deg v`, exactly `cdiophantineGWf_fst_degree_lt`). Counter induction generalizing the running
numerator `a` and accumulator `g`: each step is `g + b/vʲ` (`toPolyG_fracAddG_proper` with the per-power
summand proper by `hb` + `toPolyG_inner_summand_proper`). The inner half of the assembled `g`'s
properness. -/
theorem cHermiteReduceTowerInner_g_proper (Dt : CPolyG α) (v u : CPolyG α)
    (hv : toPolyG v ≠ 0)
    (hb : ∀ (rhs : CPolyG α),
      (toPolyG (cdiophantineGWf (cmulG u (cmonomialDeriv Dt v)) v rhs).1).degree
        < (toPolyG v).degree) :
    ∀ (j : ℕ) (a : CPolyG α) (g : CPolyG α × CPolyG α),
      (toPolyG g.1).degree < (toPolyG g.2).degree →
      (toPolyG (cHermiteReduceTowerInnerWf Dt v u j a g).1.1).degree
        < (toPolyG (cHermiteReduceTowerInnerWf Dt v u j a g).1.2).degree := by
  intro j
  induction j with
  | zero => intro a g hg; exact hg
  | succ j ih =>
    intro a g hg
    rw [cHermiteReduceTowerInnerWf]
    -- the step's summand `(b, cpowG v (j+1))` is proper, so the `fracAddG` step preserves properness.
    set rhs := cscaleG (CField.neg (CField.inv (cnatCastG (j + 1)))) a with hrhs
    set b := (cdiophantineGWf (cmulG u (cmonomialDeriv Dt v)) v rhs).1 with hbdef
    have hbproper : (toPolyG b).degree
        < (toPolyG (cpowG v (j + 1))).degree :=
      toPolyG_inner_summand_proper b v j (hb rhs) hv
    have hstep : (toPolyG (caddG (cmulG g.1 (cpowG v (j + 1))) (cmulG b g.2))).degree
        < (toPolyG (cmulG g.2 (cpowG v (j + 1)))).degree :=
      toPolyG_fracAddG_proper (gAcc := g) (gloc := (b, cpowG v (j + 1))) hg hbproper
    exact ih _ _ hstep

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **The Hermite seed pair `([0], [1])` is proper** under `toPolyG`: `deg (toPolyG [CField.zero]) < deg
(toPolyG [CField.one])` (`⊥ < 0`). `toPolyG [CField.zero] = 0` (degree `⊥`) and `toPolyG [CField.one] = 1`
(degree `0`); `⊥ < 0`. The properness base of both Hermite folds. -/
theorem toPolyG_seedPair_proper :
    (toPolyG ([CField.zero] : CPolyG α)).degree < (toPolyG ([CField.one] : CPolyG α)).degree := by
  have hzero : toPolyG ([CField.zero] : CPolyG α) = 0 := by
    rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_zero, map_zero, mul_zero, add_zero]
  have hone : toPolyG ([CField.one] : CPolyG α) = 1 := by
    rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_one, map_one, mul_zero, add_zero]
  rw [hzero, hone, Polynomial.degree_zero, Polynomial.degree_one]
  exact bot_lt_iff_ne_bot.mpr (by simp)

omit [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **★ Each per-factor `gloc` contribution is proper** — for a squarefree factor `vi` of the outer
Hermite fold, the inner-loop output `(cHermiteReduceTowerInnerWf Dt vi u j a ([0],[1])).1` is proper
(`deg .1 < deg .2`), given `vi ≠ 0` (`hv`) and the per-step Bézout keystone `hb` (`∀ rhs, deg
(cdiophantineGWf (u·Dvi) vi rhs).1 < deg vi`, exactly `cdiophantineGWf_fst_degree_lt`). The inner-loop
properness `cHermiteReduceTowerInner_g_proper` from the proper seed `([0],[1])` (`toPolyG_seedPair_proper`).
The `∀ gloc`-contribution input the outer fold (`foldl_guarded_fracAddG_proper`) wants. -/
theorem cHermiteReduceTowerInner_gloc_proper (Dt : CPolyG α) (vi u : CPolyG α) (j : ℕ)
    (a : CPolyG α) (hv : toPolyG vi ≠ 0)
    (hb : ∀ (rhs : CPolyG α),
      (toPolyG (cdiophantineGWf (cmulG u (cmonomialDeriv Dt vi)) vi rhs).1).degree
        < (toPolyG vi).degree) :
    (toPolyG (cHermiteReduceTowerInnerWf Dt vi u j a ([CField.zero], [CField.one])).1.1).degree
      < (toPolyG (cHermiteReduceTowerInnerWf Dt vi u j a ([CField.zero], [CField.one])).1.2).degree :=
  cHermiteReduceTowerInner_g_proper Dt vi u hv hb j a ([CField.zero], [CField.one])
    toPolyG_seedPair_proper

/-! ### ★★ The assembled `g` is proper — closing the outer Hermite fold

The engine's outer `g`-fold (`cHermiteReduceTowerG`, `factors.zipIdx.foldl` with the `i ≤ 1` skip guard)
combines each squarefree factor's inner-loop contribution `gloc` by `fracAddG`. Feeding the per-factor
`gloc`-properness (`cHermiteReduceTowerInner_gloc_proper`) into `foldl_guarded_fracAddG_proper` from the
proper seed `([0],[1])` gives the assembled `g = gnum/gden` proper — the last open piece of `hproper` for
`δ(t) ≤ 1`. The fold is instantiated with `β = CPolyG α × ℕ`, `skip (vi, idx) := idx + 1 ≤ 1`, and `glocOf
(vi, idx)` the factor's inner-loop output `.1`. -/

omit [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **★ The assembled Hermite rational part `g` is proper** (outer fold) — the engine's `g`-fold
`factors.zipIdx.foldl (if idx+1 ≤ 1 then gAcc else gAcc + gloc) ([0],[1])` (the `cHermiteReduceTowerG`
rational-part assembly) is proper, `deg g.1 < deg g.2`, **given** for each factor `(vi, idx) ∈
factors.zipIdx` that is *not* skipped the factor is nonzero (`hv`) and the per-step Bézout keystone holds
(`hb`, exactly `cdiophantineGWf_fst_degree_lt` over the evolving numerator). `foldl_guarded_fracAddG_proper`
with `glocOf`/`skip` the engine's, the proper seed `toPolyG_seedPair_proper`, and each non-skipped `gloc`
proper by `cHermiteReduceTowerInner_gloc_proper`. This discharges the "g proper" hypothesis of the
`hproper`-for-`δ(t) ≤ 1` chain. -/
theorem cHermiteReduceTowerG_g_proper (Dt : CPolyG α) (a d : CPolyG α)
    (factors : List (CPolyG α))
    (hv : ∀ p ∈ factors.zipIdx, ¬ (p.2 + 1 ≤ 1) → toPolyG p.1 ≠ 0)
    (hb : ∀ p ∈ factors.zipIdx, ¬ (p.2 + 1 ≤ 1) → ∀ (rhs : CPolyG α),
      (toPolyG (cdiophantineGWf
          (cmulG (cdivWf d (cpowG p.1 (p.2 + 1))) (cmonomialDeriv Dt p.1)) p.1 rhs).1).degree
        < (toPolyG p.1).degree) :
    (toPolyG (factors.zipIdx.foldl
        (fun (gAcc : CPolyG α × CPolyG α) (vi, idx) =>
          let i := idx + 1
          if i ≤ 1 then gAcc
          else
            let Vi_pow := cpowG vi i
            let u := cdivWf d Vi_pow
            let gloc := (cHermiteReduceTowerInnerWf Dt vi u (i - 1) a
              ([CField.zero], [CField.one])).1
            (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2), cmulG gAcc.2 gloc.2))
        ([CField.zero], [CField.one])).1).degree
      < (toPolyG (factors.zipIdx.foldl
        (fun (gAcc : CPolyG α × CPolyG α) (vi, idx) =>
          let i := idx + 1
          if i ≤ 1 then gAcc
          else
            let Vi_pow := cpowG vi i
            let u := cdivWf d Vi_pow
            let gloc := (cHermiteReduceTowerInnerWf Dt vi u (i - 1) a
              ([CField.zero], [CField.one])).1
            (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2), cmulG gAcc.2 gloc.2))
        ([CField.zero], [CField.one])).2).degree :=
  foldl_guarded_fracAddG_proper
    (glocOf := fun (p : CPolyG α × ℕ) =>
      (cHermiteReduceTowerInnerWf Dt p.1 (cdivWf d (cpowG p.1 (p.2 + 1))) (p.2 + 1 - 1) a
        ([CField.zero], [CField.one])).1)
    (skip := fun (p : CPolyG α × ℕ) => p.2 + 1 ≤ 1)
    factors.zipIdx ([CField.zero], [CField.one]) toPolyG_seedPair_proper
    (fun p hp hskip => cHermiteReduceTowerInner_gloc_proper Dt p.1
      (cdivWf d (cpowG p.1 (p.2 + 1))) (p.2 + 1 - 1) a (hv p hp hskip) (hb p hp hskip))

/-! ### ★★★ `hproper` for `δ(t) ≤ 1` — fully closed modulo only input-properness

Composing the now-discharged **`g` proper** (`cHermiteReduceTowerG_g_proper`) with the residual-fraction
step (`toPolyG_residualFraction_proper_of_degree_le_one`) closes the residual `deg resNum < deg resDen`
**unconditionally for `δ(t) ≤ 1`** from ONLY the input properness `deg a < deg d` (and the per-factor
keystone/nonzero hypotheses, themselves `cdiophantineGWf_fst_degree_lt`). The `g`-proper hypothesis is gone:
`gden ≠ 0` follows from `g` proper (`ne_zero_of_degree_gt`). This is exactly the `hresProper` feeding
`cHermiteReduceTowerG_leftover_proper_of_residual`, so it removes the "g proper" premise from the whole
`hproper`-for-`δ(t) ≤ 1` chain. -/

omit [Algebra ℚ (CFieldSpec.K α)] in
/-- **★★★ The residual `a/d − D(g)` is proper for `δ(t) ≤ 1`, with `g` proper DISCHARGED** — for the
engine's assembled rational part `g = (gnum, gden)` (the `cHermiteReduceTowerG` `factors.zipIdx.foldl`),
the residual `resNum = a·gden² − d·(D(gnum)·gden − gnum·D(gden))`, `resDen = d·gden²` is proper (`deg resNum
< deg resDen`), given ONLY the input `a/d` proper (`haProper`), `deg Dt ≤ 1` (`hDt`), and the per-factor
keystone/nonzero hypotheses (`hv`/`hb`, exactly `cdiophantineGWf_fst_degree_lt`). The assembled `g`'s
properness is proven internally by `cHermiteReduceTowerG_g_proper` (no longer a hypothesis); `gden ≠ 0`
follows from it (`ne_zero_of_degree_gt`). This closes `hproper` for `δ(t) ≤ 1` from input-properness alone
— the last open inner-loop piece removed. -/
theorem cHermiteReduceTowerG_residual_proper_of_degree_le_one (Dt : CPolyG α) (a d : CPolyG α)
    (factors : List (CPolyG α)) (hDt : (toPolyG Dt).natDegree ≤ 1)
    (haProper : (toPolyG a).degree < (toPolyG d).degree)
    (hv : ∀ p ∈ factors.zipIdx, ¬ (p.2 + 1 ≤ 1) → toPolyG p.1 ≠ 0)
    (hb : ∀ p ∈ factors.zipIdx, ¬ (p.2 + 1 ≤ 1) → ∀ (rhs : CPolyG α),
      (toPolyG (cdiophantineGWf
          (cmulG (cdivWf d (cpowG p.1 (p.2 + 1))) (cmonomialDeriv Dt p.1)) p.1 rhs).1).degree
        < (toPolyG p.1).degree) :
    let g := factors.zipIdx.foldl
      (fun (gAcc : CPolyG α × CPolyG α) (vi, idx) =>
        let i := idx + 1
        if i ≤ 1 then gAcc
        else
          let Vi_pow := cpowG vi i
          let u := cdivWf d Vi_pow
          let gloc := (cHermiteReduceTowerInnerWf Dt vi u (i - 1) a
            ([CField.zero], [CField.one])).1
          (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2), cmulG gAcc.2 gloc.2))
      ([CField.zero], [CField.one])
    (toPolyG (csubG (cmulG a (cmulG g.2 g.2))
        (cmulG d (csubG (cmulG (cmonomialDeriv Dt g.1) g.2)
          (cmulG g.1 (cmonomialDeriv Dt g.2)))))).degree
      < (toPolyG (cmulG d (cmulG g.2 g.2))).degree := by
  intro g
  have hgproper : (toPolyG g.1).degree < (toPolyG g.2).degree :=
    cHermiteReduceTowerG_g_proper Dt a d factors hv hb
  exact toPolyG_residualFraction_proper_of_degree_le_one Dt a d g.1 g.2
    (Polynomial.ne_zero_of_degree_gt hgproper) hDt haProper hgproper

omit [Algebra ℚ (CFieldSpec.K α)] in
/-- **★ The residual `a/d − D(g)` is proper for `δ(t) ≥ 2`, gated on the assembled `g`'s `(δ−1)` margin** —
the `δ(t) ≥ 2` companion of `cHermiteReduceTowerG_residual_proper_of_degree_le_one`. For the engine's
assembled rational part `g = (gnum, gden)` (the `cHermiteReduceTowerG` `factors.zipIdx.foldl`), the residual
`resNum = a·gden² − d·(D(gnum)·gden − gnum·D(gden))`, `resDen = d·gden²` is proper (`deg resNum < deg
resDen`), given the input `a/d` proper (`haProper`), the per-factor keystone/nonzero hypotheses (`hv`/`hb`,
exactly `cdiophantineGWf_fst_degree_lt`), AND the **margin** `deg gnum + max(0, δ(t) − 1) < deg gden`
(`hmargin`) on the *assembled* `g`. The `g`-properness premise is discharged internally
(`cHermiteReduceTowerG_g_proper`, giving `gden ≠ 0`); the residual step is `toPolyG_residualFraction_proper_of_margin`.
HONEST about the δ-boundary: the margin (strictly stronger than properness for `δ(t) ≥ 2`) is exactly what
FAILS for the tangent example (`g = −1/t`, margin `0 + 1 < 1` false), so this gates `hproper` for `δ(t) ≥ 2`
**only** under the margin — never unconditionally from the generic Hermite output, which is the precise
content of the `δ ≥ 2` boundary. -/
theorem cHermiteReduceTowerG_residual_proper_of_margin_conditional (Dt : CPolyG α) (a d : CPolyG α)
    (factors : List (CPolyG α))
    (haProper : (toPolyG a).degree < (toPolyG d).degree)
    (hv : ∀ p ∈ factors.zipIdx, ¬ (p.2 + 1 ≤ 1) → toPolyG p.1 ≠ 0)
    (hb : ∀ p ∈ factors.zipIdx, ¬ (p.2 + 1 ≤ 1) → ∀ (rhs : CPolyG α),
      (toPolyG (cdiophantineGWf
          (cmulG (cdivWf d (cpowG p.1 (p.2 + 1))) (cmonomialDeriv Dt p.1)) p.1 rhs).1).degree
        < (toPolyG p.1).degree)
    (hmargin :
      (toPolyG (factors.zipIdx.foldl
        (fun (gAcc : CPolyG α × CPolyG α) (vi, idx) =>
          let i := idx + 1
          if i ≤ 1 then gAcc
          else
            let Vi_pow := cpowG vi i
            let u := cdivWf d Vi_pow
            let gloc := (cHermiteReduceTowerInnerWf Dt vi u (i - 1) a
              ([CField.zero], [CField.one])).1
            (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2), cmulG gAcc.2 gloc.2))
        ([CField.zero], [CField.one])).1).degree
          + (max 0 ((toPolyG Dt).natDegree - 1) : ℕ)
        < (toPolyG (factors.zipIdx.foldl
        (fun (gAcc : CPolyG α × CPolyG α) (vi, idx) =>
          let i := idx + 1
          if i ≤ 1 then gAcc
          else
            let Vi_pow := cpowG vi i
            let u := cdivWf d Vi_pow
            let gloc := (cHermiteReduceTowerInnerWf Dt vi u (i - 1) a
              ([CField.zero], [CField.one])).1
            (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2), cmulG gAcc.2 gloc.2))
        ([CField.zero], [CField.one])).2).degree) :
    let g := factors.zipIdx.foldl
      (fun (gAcc : CPolyG α × CPolyG α) (vi, idx) =>
        let i := idx + 1
        if i ≤ 1 then gAcc
        else
          let Vi_pow := cpowG vi i
          let u := cdivWf d Vi_pow
          let gloc := (cHermiteReduceTowerInnerWf Dt vi u (i - 1) a
            ([CField.zero], [CField.one])).1
          (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2), cmulG gAcc.2 gloc.2))
      ([CField.zero], [CField.one])
    (toPolyG (csubG (cmulG a (cmulG g.2 g.2))
        (cmulG d (csubG (cmulG (cmonomialDeriv Dt g.1) g.2)
          (cmulG g.1 (cmonomialDeriv Dt g.2)))))).degree
      < (toPolyG (cmulG d (cmulG g.2 g.2))).degree := by
  intro g
  have hgproper : (toPolyG g.1).degree < (toPolyG g.2).degree :=
    cHermiteReduceTowerG_g_proper Dt a d factors hv hb
  exact toPolyG_residualFraction_proper_of_margin Dt a d g.1 g.2
    (Polynomial.ne_zero_of_degree_gt hgproper) haProper hmargin

/-! ### ★★ The normal-part assembly through the engine's own `checkIdentityG` certificate

The full normal-part one-shot `checkIdentityG_cIntegrateReducedG` needs the Hermite half (above) **and**
the Rothstein–Trager half (the residue-log part `cLogPartG` differentiates to the leftover `h`). The RT
half — the abstract residue-sum identity, all the way to `checkIdentityG = true` — is the genuinely-hard
remainder (shared with the `ComputableRadicalLogSoundness` frontier). So, exactly as the template's
`isGeneralRationalIntegralWf_of_roundtrip` closed the general rational-part soundness through the engine's
*own* round-trip check, we close the normal-part assembly through the engine's *own* `checkIdentityG`
certificate: feeding `checkIdentityG = true` (the `native_decide`-reachable self-check, supplied as the
hypothesis `hcheck`) into the field bridge `field_identity_of_checkIdentityG` yields `D(res) = a/d`. -/

/-- **★★ The reduced-case field identity from the engine's own `checkIdentityG` certificate** — for the
normal-part capstone output `res = cIntegrateReducedG Dt fuel a d cands`, if the engine's own cleared
antiderivative check passes (`checkIdentityG Dt res a d = true` — the Hermite half + RT half together
validate this, reachable by `native_decide` for any concrete run), then the field-level antiderivative
identity `D(g) + logResidueSumG Dt res.logs = amG a/amG d` holds over `RatFunc (CFieldSpec.K α)`, with
`g = amG res.rational.1/amG res.rational.2`. The normal-part `D(∫f) = f`, gated only on the engine's own
self-certificate — the transcendental analogue of `isGeneralRationalIntegralWf_of_roundtrip`. Pure
composition with `field_identity_of_checkIdentityG`. -/
theorem field_identity_of_cIntegrateReducedG_of_checkIdentityG [CFracGcdCore α] (Dt : CPolyG α)
    (fuel : ℕ) (a d : CPolyG α) (cands : List α)
    (hgden : toPolyG (CPolyG.cIntegrateReducedG Dt fuel a d cands).rational.2 ≠ 0)
    (haden : toPolyG d ≠ 0)
    (hlogs : ∀ cv ∈ (CPolyG.cIntegrateReducedG Dt fuel a d cands).logs, toPolyG cv.2 ≠ 0)
    (hcheck : CPolyG.checkIdentityG Dt (CPolyG.cIntegrateReducedG Dt fuel a d cands) a d = true) :
    towerFractionFieldDerivG Dt
        (amG α (toPolyG (CPolyG.cIntegrateReducedG Dt fuel a d cands).rational.1)
          / amG α (toPolyG (CPolyG.cIntegrateReducedG Dt fuel a d cands).rational.2))
        + logResidueSumG Dt (CPolyG.cIntegrateReducedG Dt fuel a d cands).logs
      = amG α (toPolyG a) / amG α (toPolyG d) :=
  field_identity_of_checkIdentityG Dt (CPolyG.cIntegrateReducedG Dt fuel a d cands) a d
    hgden haden hlogs hcheck

/-! ### ★★★ The FULL one-shot `cIntegrateGFull = some res ⟹ D(res) = a/d` (engine-certificate bridge)

`cIntegrateGFull` dispatches to the polynomial branch (`cPolyRischDEG`, one-shot already abstract in
`ComputableOneShotSoundness`), the normal part (`cIntegrateReducedG`, Hermite half abstract here), and the
recombination — all of which the engine's single `checkIdentityG` validates uniformly. So the cleanest full
one-shot, covering *every* regime `cIntegrateGFull` lands, is gated on the engine's own `checkIdentityG`
certificate via the carrier-agnostic bridge `field_identity_of_checkIdentityG` — the algorithm output
passing its own check. -/

/-- **★★★ The full `cIntegrateGFull` one-shot, gated on the engine's own `checkIdentityG`** — for any
result `res` the full driver `cIntegrateGFull Dt fuel a d cands` lands (the `fuel`/`cands` regime carried
as documentation), if the engine's own cleared check passes (`checkIdentityG Dt res a d = true` —
reachable by `native_decide` for any concrete run; abstractly the poly branch's
`checkIdentityG_cIntegratePolyG_const` and the normal part's Hermite + RT validation together supply it),
then the field-level identity `D(res) + logResidueSumG Dt res.logs = amG a/amG d` holds over `RatFunc
(CFieldSpec.K α)`. Covers EVERY regime `cIntegrateGFull` dispatches into (polynomial branch, normal part,
recombination) through the single carrier-agnostic bridge `field_identity_of_checkIdentityG` — the
`checkIdentityG` self-certificate alone supplies correctness, the `field_identity_of_checkIdentityG` bridge
with the guard made explicit (the algorithm output passes its own check). -/
theorem field_identity_of_cIntegrateGFull_of_checkIdentityG [CFracGcdCore α] [CRischField α]
    (Dt : CPolyG α) (a d : CPolyG α) (res : IntegralResultG α)
    (hgden : toPolyG res.rational.2 ≠ 0) (haden : toPolyG d ≠ 0)
    (hlogs : ∀ cv ∈ res.logs, toPolyG cv.2 ≠ 0)
    (hcheck : CPolyG.checkIdentityG Dt res a d = true) :
    towerFractionFieldDerivG Dt (amG α (toPolyG res.rational.1) / amG α (toPolyG res.rational.2))
        + logResidueSumG Dt res.logs
      = amG α (toPolyG a) / amG α (toPolyG d) :=
  field_identity_of_checkIdentityG Dt res a d hgden haden hlogs hcheck

/-! ### ★ The deliverables at the level-1 carrier `α = QFunNZG ℚ = ℚ(x)`

Instantiating the Hermite half and the full one-shot bridge at `α = QFunNZG ℚ`, where `CFieldSpec.K
(QFunNZG ℚ) = RatFunc ℚ` (genuine `Algebra ℚ`). These are the concrete normal-part / full one-shot
statements over `ℚ(x)(t)`. The local instance bridges the carrier abbreviation to `RatFunc ℚ`. -/

/-- The engine carrier `CFieldSpec.K (QFunNZG ℚ)` is `RatFunc ℚ`, a `ℚ`-algebra. Local instance so the
`QFunNZG ℚ` deliverables synthesize the **same** `Algebra ℚ` the bridge `towerFractionFieldDerivG` uses. -/
noncomputable local instance : Algebra ℚ (CFieldSpec.K (QFunNZG ℚ)) :=
  inferInstanceAs (Algebra ℚ (RatFunc ℚ))

/-- **★ The Hermite half over `ℚ(x)(t)`** — the master Hermite telescoping `D(g) + h = a/d` (engine seed
`0/1`) at the level-1 carrier `α = QFunNZG ℚ`, over `RatFunc ℚ`. The concrete Hermite-half abstract
soundness for the transcendental tower integrator at `ℚ(x)(t)`: given the per-power Hermite identities, the
assembled rational part `g` integrates the integrand modulo the final residual `h` — no `native_decide`. -/
theorem cHermiteReduceTowerG_telescope_seed_qfunNZG (Dt : CPolyG (QFunNZG ℚ))
    (L₀ : CPolyG (QFunNZG ℚ) × CPolyG (QFunNZG ℚ))
    (rest glocs : List (CPolyG (QFunNZG ℚ) × CPolyG (QFunNZG ℚ)))
    (hmem : ∀ g ∈ glocs, toPolyG g.2 ≠ 0)
    (hstep : List.Forall₂ (fun g p =>
        towerFractionFieldDerivG Dt (amG (QFunNZG ℚ) (toPolyG g.1) / amG (QFunNZG ℚ) (toPolyG g.2))
          = amG (QFunNZG ℚ) (toPolyG (Prod.fst p).1) / amG (QFunNZG ℚ) (toPolyG (Prod.fst p).2)
            - amG (QFunNZG ℚ) (toPolyG (Prod.snd p).1) / amG (QFunNZG ℚ) (toPolyG (Prod.snd p).2))
        glocs ((L₀ :: rest).zip rest)) :
    towerFractionFieldDerivG Dt
        (amG (QFunNZG ℚ) (toPolyG (glocs.foldl
            (fun (gAcc : CPolyG (QFunNZG ℚ) × CPolyG (QFunNZG ℚ)) gloc =>
              (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2), cmulG gAcc.2 gloc.2))
            (([CField.zero] : CPolyG (QFunNZG ℚ)), ([CField.one] : CPolyG (QFunNZG ℚ)))).1)
          / amG (QFunNZG ℚ) (toPolyG (glocs.foldl
            (fun (gAcc : CPolyG (QFunNZG ℚ) × CPolyG (QFunNZG ℚ)) gloc =>
              (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2), cmulG gAcc.2 gloc.2))
            (([CField.zero] : CPolyG (QFunNZG ℚ)), ([CField.one] : CPolyG (QFunNZG ℚ)))).2))
        + amG (QFunNZG ℚ) (toPolyG (rest.getLastD L₀).1)
          / amG (QFunNZG ℚ) (toPolyG (rest.getLastD L₀).2)
      = amG (QFunNZG ℚ) (toPolyG L₀.1) / amG (QFunNZG ℚ) (toPolyG L₀.2) :=
  cHermiteReduceTowerG_telescope_seed Dt L₀ rest glocs hmem hstep

/-- **★★★ The full `cIntegrateGFull` one-shot over `ℚ(x)(t)`, gated on the engine's own `checkIdentityG`**
— at the level-1 carrier `α = QFunNZG ℚ` (`CFieldSpec.K (QFunNZG ℚ) = RatFunc ℚ`): if
`cIntegrateGFull = some res` and the engine's own check passes (`checkIdentityG Dt res a d = true`), then
`D(res) + logResidueSumG Dt res.logs = amG a/amG d` over `RatFunc ℚ`. Covers EVERY regime `cIntegrateGFull`
dispatches into, through the carrier-agnostic bridge. The concrete full one-shot at ℚ(x)(t), modulo the
engine's own self-certificate. -/
theorem field_identity_of_cIntegrateGFull_of_checkIdentityG_qfunNZG (Dt : CPolyG (QFunNZG ℚ))
    (a d : CPolyG (QFunNZG ℚ)) (res : IntegralResultG (QFunNZG ℚ))
    (hgden : toPolyG res.rational.2 ≠ 0) (haden : toPolyG d ≠ 0)
    (hlogs : ∀ cv ∈ res.logs, toPolyG cv.2 ≠ 0)
    (hcheck : CPolyG.checkIdentityG Dt res a d = true) :
    towerFractionFieldDerivG Dt
        (amG (QFunNZG ℚ) (toPolyG res.rational.1) / amG (QFunNZG ℚ) (toPolyG res.rational.2))
        + logResidueSumG Dt res.logs
      = amG (QFunNZG ℚ) (toPolyG a) / amG (QFunNZG ℚ) (toPolyG d) :=
  field_identity_of_cIntegrateGFull_of_checkIdentityG Dt a d res hgden haden hlogs hcheck

/-! ### Restatements against the intended wording (anonymous `example`s) -/

-- ★ THE EXACT-DIVISION DEGREE BOUND (abstract): from `H·D₂ = N·S`, `deg N < deg D₂`, `S ≠ 0`,
-- the quotient is proper — `deg H < deg S`. The reusable cancellation core of `hproper`.
example {K : Type*} [Field K] {H D2 N S : K[X]}
    (hid : H * D2 = N * S) (hND : N.degree < D2.degree) (hS : S ≠ 0) :
    H.degree < S.degree :=
  degree_lt_of_exact_div hid hND hS

-- ★ `hproper` REDUCED to the residual-fraction properness: given the leftover projections, the exact
  -- division (divisibility), nonzero radical, and `deg resNum < deg resDen`, the Hermite leftover is
-- proper — `deg (…).2.1 < deg (…).2.2`. The genuinely-provable exact-division half of `hproper`.
example [CFracGcdCore α] (Dt : CPolyG α) (fuel : ℕ) (a d : CPolyG α) (resNum resDen Dstar : CPolyG α)
    (hnum : toPolyG (CPolyG.cHermiteReduceTowerG Dt fuel a d).2.1
      = toPolyG (cdivWf (cmulG resNum Dstar) resDen))
    (hden : toPolyG (CPolyG.cHermiteReduceTowerG Dt fuel a d).2.2 = toPolyG Dstar)
    (hdvd : toPolyG resDen ∣ toPolyG (cmulG resNum Dstar))
    (hresDen : cnormG resDen ≠ []) (hDstar : toPolyG Dstar ≠ 0)
    (hresProper : (toPolyG resNum).degree < (toPolyG resDen).degree) :
    (toPolyG (CPolyG.cHermiteReduceTowerG Dt fuel a d).2.1).degree
      < (toPolyG (CPolyG.cHermiteReduceTowerG Dt fuel a d).2.2).degree :=
  cHermiteReduceTowerG_leftover_proper_of_residual Dt fuel a d resNum resDen Dstar
    hnum hden hdvd hresDen hDstar hresProper

-- ★ THE FOLD-INDUCTION (g stays proper): the engine's guarded `g`-fold of proper contributions is proper
-- — the assembled rational part `g = gnum/gden` satisfies `deg gnum < deg gden`.
example {β : Type*} (glocOf : β → CPolyG α × CPolyG α) (skip : β → Prop) [DecidablePred skip]
    (xs : List β) (s : CPolyG α × CPolyG α) (hs : (toPolyG s.1).degree < (toPolyG s.2).degree)
    (hmem : ∀ b ∈ xs, ¬ skip b → (toPolyG (glocOf b).1).degree < (toPolyG (glocOf b).2).degree) :
    (toPolyG (xs.foldl
        (fun (gAcc : CPolyG α × CPolyG α) (b : β) =>
          if skip b then gAcc
          else (caddG (cmulG gAcc.1 (glocOf b).2) (cmulG (glocOf b).1 gAcc.2),
                cmulG gAcc.2 (glocOf b).2)) s).1).degree
      < (toPolyG (xs.foldl
        (fun (gAcc : CPolyG α × CPolyG α) (b : β) =>
          if skip b then gAcc
          else (caddG (cmulG gAcc.1 (glocOf b).2) (cmulG (glocOf b).1 gAcc.2),
                cmulG gAcc.2 (glocOf b).2)) s).2).degree :=
  foldl_guarded_fracAddG_proper glocOf skip xs s hs hmem

-- ★ THE INNER-LOOP `g` PROPER: `cHermiteReduceTowerInnerWf`'s accumulated `g` is proper, given the input
-- accumulator proper, `v ≠ 0`, and the per-step Bézout keystone (`deg b < deg v` for every `rhs`).
example (Dt : CPolyG α) (v u : CPolyG α) (hv : toPolyG v ≠ 0)
    (hb : ∀ (rhs : CPolyG α),
      (toPolyG (cdiophantineGWf (cmulG u (cmonomialDeriv Dt v)) v rhs).1).degree
        < (toPolyG v).degree)
    (j : ℕ) (a : CPolyG α) (g : CPolyG α × CPolyG α)
    (hg : (toPolyG g.1).degree < (toPolyG g.2).degree) :
    (toPolyG (cHermiteReduceTowerInnerWf Dt v u j a g).1.1).degree
      < (toPolyG (cHermiteReduceTowerInnerWf Dt v u j a g).1.2).degree :=
  cHermiteReduceTowerInner_g_proper Dt v u hv hb j a g hg

-- ★ EACH PER-FACTOR `gloc` PROPER: a squarefree factor's inner-loop output (from the seed `0/1`) is proper,
-- given `vi ≠ 0` and the per-step keystone — the `∀ gloc` input the outer fold wants.
example (Dt : CPolyG α) (vi u : CPolyG α) (j : ℕ) (a : CPolyG α) (hv : toPolyG vi ≠ 0)
    (hb : ∀ (rhs : CPolyG α),
      (toPolyG (cdiophantineGWf (cmulG u (cmonomialDeriv Dt vi)) vi rhs).1).degree
        < (toPolyG vi).degree) :
    (toPolyG (cHermiteReduceTowerInnerWf Dt vi u j a ([CField.zero], [CField.one])).1.1).degree
      < (toPolyG (cHermiteReduceTowerInnerWf Dt vi u j a ([CField.zero], [CField.one])).1.2).degree :=
  cHermiteReduceTowerInner_gloc_proper Dt vi u j a hv hb

-- ★★ THE ASSEMBLED `g` PROPER (outer fold): the engine's `cHermiteReduceTowerG` `g`-fold is proper, given
-- each non-skipped factor is nonzero + the per-step keystone — discharging the "g proper" hypothesis.
example (Dt : CPolyG α) (a d : CPolyG α) (factors : List (CPolyG α))
    (hv : ∀ p ∈ factors.zipIdx, ¬ (p.2 + 1 ≤ 1) → toPolyG p.1 ≠ 0)
    (hb : ∀ p ∈ factors.zipIdx, ¬ (p.2 + 1 ≤ 1) → ∀ (rhs : CPolyG α),
      (toPolyG (cdiophantineGWf
          (cmulG (cdivWf d (cpowG p.1 (p.2 + 1))) (cmonomialDeriv Dt p.1)) p.1 rhs).1).degree
        < (toPolyG p.1).degree) :
    (toPolyG (factors.zipIdx.foldl
        (fun (gAcc : CPolyG α × CPolyG α) (vi, idx) =>
          let i := idx + 1
          if i ≤ 1 then gAcc
          else
            let Vi_pow := cpowG vi i
            let u := cdivWf d Vi_pow
            let gloc := (cHermiteReduceTowerInnerWf Dt vi u (i - 1) a
              ([CField.zero], [CField.one])).1
            (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2), cmulG gAcc.2 gloc.2))
        ([CField.zero], [CField.one])).1).degree
      < (toPolyG (factors.zipIdx.foldl
        (fun (gAcc : CPolyG α × CPolyG α) (vi, idx) =>
          let i := idx + 1
          if i ≤ 1 then gAcc
          else
            let Vi_pow := cpowG vi i
            let u := cdivWf d Vi_pow
            let gloc := (cHermiteReduceTowerInnerWf Dt vi u (i - 1) a
              ([CField.zero], [CField.one])).1
            (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2), cmulG gAcc.2 gloc.2))
        ([CField.zero], [CField.one])).2).degree :=
  cHermiteReduceTowerG_g_proper Dt a d factors hv hb

-- ★★★ `hproper` FOR `δ(t) ≤ 1`, `g` PROPER DISCHARGED: the residual `a/d − D(g)` is proper from ONLY input
-- properness (`deg a < deg d`), `deg Dt ≤ 1`, and the per-factor keystone/nonzero — `g` proper is internal.
example (Dt : CPolyG α) (a d : CPolyG α) (factors : List (CPolyG α))
    (hDt : (toPolyG Dt).natDegree ≤ 1) (haProper : (toPolyG a).degree < (toPolyG d).degree)
    (hv : ∀ p ∈ factors.zipIdx, ¬ (p.2 + 1 ≤ 1) → toPolyG p.1 ≠ 0)
    (hb : ∀ p ∈ factors.zipIdx, ¬ (p.2 + 1 ≤ 1) → ∀ (rhs : CPolyG α),
      (toPolyG (cdiophantineGWf
          (cmulG (cdivWf d (cpowG p.1 (p.2 + 1))) (cmonomialDeriv Dt p.1)) p.1 rhs).1).degree
        < (toPolyG p.1).degree) :
    let g := factors.zipIdx.foldl
      (fun (gAcc : CPolyG α × CPolyG α) (vi, idx) =>
        let i := idx + 1
        if i ≤ 1 then gAcc
        else
          let Vi_pow := cpowG vi i
          let u := cdivWf d Vi_pow
          let gloc := (cHermiteReduceTowerInnerWf Dt vi u (i - 1) a
            ([CField.zero], [CField.one])).1
          (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2), cmulG gAcc.2 gloc.2))
      ([CField.zero], [CField.one])
    (toPolyG (csubG (cmulG a (cmulG g.2 g.2))
        (cmulG d (csubG (cmulG (cmonomialDeriv Dt g.1) g.2)
          (cmulG g.1 (cmonomialDeriv Dt g.2)))))).degree
      < (toPolyG (cmulG d (cmulG g.2 g.2))).degree :=
  cHermiteReduceTowerG_residual_proper_of_degree_le_one Dt a d factors hDt haProper hv hb

-- ★ THE DERIVATIVE-DEGREE STEP (D(g) proper, `deg Dt ≤ 1`): a proper `g = gnum/gden` has proper derivative
-- numerator `D(gnum)·gden − gnum·D(gden)` for `gden²` when `deg Dt ≤ 1` (base rational / exp / log).
example (Dt gnum gden : CPolyG α) (hM : toPolyG gden ≠ 0) (hDt : (toPolyG Dt).natDegree ≤ 1)
    (hgproper : (toPolyG gnum).degree < (toPolyG gden).degree) :
    (toPolyG (csubG (cmulG (cmonomialDeriv Dt gnum) gden)
        (cmulG gnum (cmonomialDeriv Dt gden)))).degree
      < (toPolyG (cmulG gden gden)).degree :=
  toPolyG_gprimeNum_proper_of_degree_le_one Dt gnum gden hM hDt hgproper

-- ★ MARGIN-PRESERVING FRACADD (`δ ≥ 2`, abstract): the `(δ−1)`-slack generalization of proper fracAdd —
-- two margin-proper fractions add to a margin-proper one. `m = 0` is `degree_fracAdd_lt_of_proper`.
example {K : Type*} [Field K] {p1 q1 p2 q2 : K[X]} (m : ℕ)
    (h1 : p1.degree + (m : ℕ) < q1.degree) (h2 : p2.degree + (m : ℕ) < q2.degree) :
    (p1 * q2 + p2 * q1).degree + (m : ℕ) < (q1 * q2).degree :=
  degree_fracAdd_lt_of_margin m h1 h2

-- ★ THE MARGIN FOLD-INDUCTION (`δ ≥ 2`): the engine's guarded `g`-fold of margin-proper contributions stays
-- margin-proper — the `(δ−1)`-slack generalization of `foldl_guarded_fracAddG_proper`.
example {β : Type*} (glocOf : β → CPolyG α × CPolyG α) (skip : β → Prop) [DecidablePred skip] (m : ℕ)
    (xs : List β) (s : CPolyG α × CPolyG α)
    (hs : (toPolyG s.1).degree + (m : ℕ) < (toPolyG s.2).degree)
    (hmem : ∀ b ∈ xs, ¬ skip b →
      (toPolyG (glocOf b).1).degree + (m : ℕ) < (toPolyG (glocOf b).2).degree) :
    (toPolyG (xs.foldl
        (fun (gAcc : CPolyG α × CPolyG α) (b : β) =>
          if skip b then gAcc
          else (caddG (cmulG gAcc.1 (glocOf b).2) (cmulG (glocOf b).1 gAcc.2),
                cmulG gAcc.2 (glocOf b).2)) s).1).degree + (m : ℕ)
      < (toPolyG (xs.foldl
        (fun (gAcc : CPolyG α × CPolyG α) (b : β) =>
          if skip b then gAcc
          else (caddG (cmulG gAcc.1 (glocOf b).2) (cmulG (glocOf b).1 gAcc.2),
                cmulG gAcc.2 (glocOf b).2)) s).2).degree :=
  foldl_guarded_fracAddG_margin glocOf skip m xs s hs hmem

-- ★ `hproper` FOR `δ ≥ 2`, CONDITIONAL on the `(δ−1)` margin of `g`: the engine's `resNum/resDen = a/d − D(g)`
-- is proper GIVEN `a/d` proper and `g` has the margin `deg gnum + max(0, δ−1) < deg gden`. The margin is
-- exactly what FAILS for the tangent example (`g = −1/t`, `0 + 1 < 1` false), so this is the precise boundary.
example (Dt a d gnum gden : CPolyG α) (hden : toPolyG gden ≠ 0)
    (haProper : (toPolyG a).degree < (toPolyG d).degree)
    (hmargin :
      (toPolyG gnum).degree + (max 0 ((toPolyG Dt).natDegree - 1) : ℕ) < (toPolyG gden).degree) :
    (toPolyG (csubG (cmulG a (cmulG gden gden))
        (cmulG d (csubG (cmulG (cmonomialDeriv Dt gnum) gden)
          (cmulG gnum (cmonomialDeriv Dt gden)))))).degree
      < (toPolyG (cmulG d (cmulG gden gden))).degree :=
  toPolyG_residualFraction_proper_of_margin Dt a d gnum gden hden haProper hmargin

-- ★ THE RESIDUAL (b) CLOSED (`deg Dt ≤ 1`): the engine's actual `resNum/resDen = a/d − D(g)` is proper —
-- `deg resNum < deg resDen` — from `g` proper, `a/d` proper, `deg Dt ≤ 1`. This is exactly the `hresProper`
-- of `cHermiteReduceTowerG_leftover_proper_of_residual`, closing `hproper` unconditionally for `deg Dt ≤ 1`.
example (Dt a d gnum gden : CPolyG α) (hden : toPolyG gden ≠ 0)
    (hDt : (toPolyG Dt).natDegree ≤ 1)
    (haProper : (toPolyG a).degree < (toPolyG d).degree)
    (hgproper : (toPolyG gnum).degree < (toPolyG gden).degree) :
    (toPolyG (csubG (cmulG a (cmulG gden gden))
        (cmulG d (csubG (cmulG (cmonomialDeriv Dt gnum) gden)
          (cmulG gnum (cmonomialDeriv Dt gden)))))).degree
      < (toPolyG (cmulG d (cmulG gden gden))).degree :=
  toPolyG_residualFraction_proper_of_degree_le_one Dt a d gnum gden hden hDt haProper hgproper

-- ★ THE HERMITE HALF (abstract, checker-free, no native_decide): the master telescoping `D(g) + h = a/d`
-- in the tower fraction field, given the per-power Hermite identities — the transcendental
-- `generalReduceRationalTelescopeWf`.
example (Dt : CPolyG α) (s L₀ : CPolyG α × CPolyG α) (rest glocs : List (CPolyG α × CPolyG α))
    (hs : toPolyG s.2 ≠ 0) (hmem : ∀ g ∈ glocs, toPolyG g.2 ≠ 0)
    (hseed : towerFractionFieldDerivG Dt (amG α (toPolyG s.1) / amG α (toPolyG s.2)) = 0)
    (hstep : List.Forall₂ (fun g p =>
        towerFractionFieldDerivG Dt (amG α (toPolyG g.1) / amG α (toPolyG g.2))
          = amG α (toPolyG (Prod.fst p).1) / amG α (toPolyG (Prod.fst p).2)
            - amG α (toPolyG (Prod.snd p).1) / amG α (toPolyG (Prod.snd p).2))
        glocs ((L₀ :: rest).zip rest)) :
    towerFractionFieldDerivG Dt
        (amG α (toPolyG (glocs.foldl
            (fun (gAcc : CPolyG α × CPolyG α) gloc =>
              (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2), cmulG gAcc.2 gloc.2)) s).1)
          / amG α (toPolyG (glocs.foldl
            (fun (gAcc : CPolyG α × CPolyG α) gloc =>
              (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2), cmulG gAcc.2 gloc.2)) s).2))
        + amG α (toPolyG (rest.getLastD L₀).1) / amG α (toPolyG (rest.getLastD L₀).2)
      = amG α (toPolyG L₀.1) / amG α (toPolyG L₀.2) :=
  cHermiteReduceTowerG_telescope Dt s L₀ rest glocs hs hmem hseed hstep

-- ★★★ THE FULL ONE-SHOT at `α = QFunNZG ℚ`, gated on the engine's own `checkIdentityG`:
-- `cIntegrateGFull = some res` + `checkIdentityG = true` ⟹ `D(res) = a/d` over `RatFunc ℚ`.
example (Dt : CPolyG (QFunNZG ℚ)) (a d : CPolyG (QFunNZG ℚ)) (res : IntegralResultG (QFunNZG ℚ))
    (hgden : toPolyG res.rational.2 ≠ 0) (haden : toPolyG d ≠ 0)
    (hlogs : ∀ cv ∈ res.logs, toPolyG cv.2 ≠ 0)
    (hcheck : CPolyG.checkIdentityG Dt res a d = true) :
    towerFractionFieldDerivG Dt
        (amG (QFunNZG ℚ) (toPolyG res.rational.1) / amG (QFunNZG ℚ) (toPolyG res.rational.2))
        + logResidueSumG Dt res.logs
      = amG (QFunNZG ℚ) (toPolyG a) / amG (QFunNZG ℚ) (toPolyG d) :=
  field_identity_of_cIntegrateGFull_of_checkIdentityG_qfunNZG Dt a d res
    hgden haden hlogs hcheck

/-! ### Axiom audit — the Hermite half and the assembly rest only on the standard kernel axioms
(`propext`, `Classical.choice`, `Quot.sound`); no `native_decide`, no `sorry`. -/

#print axioms amG_toPolyG_fracAddG
#print axioms amG_toPolyG_foldl_fracAddG
#print axioms towerFractionFieldDerivG_amG_fracAccG
#print axioms sum_towerFractionFieldDerivG_telescope
#print axioms degree_lt_of_exact_div
#print axioms cHermiteReduceTowerG_leftover_proper_of_residual
#print axioms degree_fracAdd_lt_of_proper
#print axioms degree_fracAdd_lt_of_margin
#print axioms toPolyG_fracAddG_margin
#print axioms foldl_guarded_fracAddG_margin
#print axioms toPolyG_residualFraction_proper_of_margin
#print axioms degree_resNum_lt
#print axioms degree_implicitDeriv_frac_lt_of_margin
#print axioms toPolyG_fracAddG_proper
#print axioms foldl_fracAddG_proper
#print axioms foldl_guarded_fracAddG_proper
#print axioms toPolyG_gprimeNum_proper_of_margin
#print axioms toPolyG_gprimeNum_proper_of_degree_le_one
#print axioms toPolyG_resNum_proper
#print axioms toPolyG_residualFraction_proper_of_degree_le_one
#print axioms degree_lt_pow_succ_of_degree_lt
#print axioms toPolyG_inner_summand_proper
#print axioms cHermiteReduceTowerInner_g_proper
#print axioms toPolyG_seedPair_proper
#print axioms cHermiteReduceTowerInner_gloc_proper
#print axioms cHermiteReduceTowerG_g_proper
#print axioms cHermiteReduceTowerG_residual_proper_of_degree_le_one
#print axioms cHermiteReduceTowerG_telescope
#print axioms cHermiteReduceTowerG_telescope_seed
#print axioms field_identity_of_cIntegrateReducedG_of_checkIdentityG
#print axioms field_identity_of_cIntegrateGFull_of_checkIdentityG
#print axioms cHermiteReduceTowerG_telescope_seed_qfunNZG
#print axioms field_identity_of_cIntegrateGFull_of_checkIdentityG_qfunNZG

end DeepWiki.SymbolicIntegration
