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
transporting the **general rational-part telescoping template** `generalReduceRationalTelescope`
(`ComputableGeneralIntegralSoundness`) from the algebraic carrier `K(x)[y]/(f)` to the **transcendental
tower** with the monomial derivation `D = cmonomialDeriv Dt`. The mathematical core is identical: the
Hermite reduction reassembles its rational part `g` as an **accumulator fold** of per-squarefree-factor
contributions, and soundness of the assembled `g` is a **telescoping of `D` over that fold** in the
fraction field `RatFunc (CFieldSpec.K α)`.

* **`towerFractionFieldDerivG_amG_fracAccG`** — the engine's fraction-accumulator (the shape
  `cHermiteReduceTowerG` folds its `g` with: `gAcc + gloc` cross-multiplied) reads through `amG`/the field
  derivation as the sum of the per-step contributions: `D(amG(fold)) = D(amG seed) + ∑ D(amG glocⱼ)`. The
  transcendental analogue of `mk_toPolyG_afDeriv_foldlCaddG`. Built on `Derivation.map_add` and the
  fraction-add reading `amG_toPolyG_fracAddG`.
* **`sum_towerFractionFieldDerivG_telescope`** — if each contribution's field-derivative is the difference
  of consecutive leftovers (the per-power Hermite identity `hermiteInner_spec` supplies, taken as the named
  hypothesis exactly as the template does), the sum telescopes to the endpoints. The transcendental
  analogue of `sum_mk_toPolyG_afDeriv_telescope`.
* **★ `cHermiteReduceTowerG_telescope`** — the master Hermite telescoping soundness over the tower
  (abstract field identity): the assembled rational part `g` and the final leftover `h` satisfy `D(g) + h =
  a/d` in `RatFunc (CFieldSpec.K α)`, **given** the per-step Hermite identities. The transcendental
  `generalReduceRationalTelescope`; the **Hermite half** of the normal part. General in `Dt`, `α`.

## The assembly to the full one-shot, and the precise remainder

The normal-part one-shot target `checkIdentityG_cIntegrateReducedG` (`cIntegrateReducedG = some res ⟹
checkIdentityG = true`) decomposes into the Hermite half (above) **and** the Rothstein–Trager half (the
residue-log part `cLogPartG` differentiates to the leftover `h`). The RT half — the abstract
`roots_residueResultantTowerG_eq_residues` residue-sum identity over the tower, all the way to
`checkIdentityG = true` — is the genuinely-hard remainder (the same gap `ComputableRadicalLogSoundness`
isolates for the radical case). So, exactly as the template's `isGeneralRationalIntegral_of_roundtrip`
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
analogue of the `toQFun_foldl_qadd` / `mk_toPolyG_afDeriv_foldlCaddG` accumulator reading. -/
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
additivity (`map_add`, `map_list_sum`). The transcendental analogue of `mk_toPolyG_afDeriv_foldlCaddG`. -/
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

The transcendental analogue of `sum_mk_toPolyG_afDeriv_telescope`: if each per-factor contribution's
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
`sum_mk_toPolyG_afDeriv_telescope`. -/
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
transcendental `generalReduceRationalTelescope`. -/

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
transcendental mirror of `hermiteInner_spec`), exactly as `generalReduceRationalTelescope` takes its
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
`generalReduceRationalTelescope` at the engine seed — the Hermite half of the normal-part one-shot, fully
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

/-! ### ★★ The normal-part assembly through the engine's own `checkIdentityG` certificate

The full normal-part one-shot `checkIdentityG_cIntegrateReducedG` needs the Hermite half (above) **and**
the Rothstein–Trager half (the residue-log part `cLogPartG` differentiates to the leftover `h`). The RT
half — the abstract residue-sum identity, all the way to `checkIdentityG = true` — is the genuinely-hard
remainder (shared with the `ComputableRadicalLogSoundness` frontier). So, exactly as the template's
`isGeneralRationalIntegral_of_roundtrip` closed the general rational-part soundness through the engine's
*own* round-trip check, we close the normal-part assembly through the engine's *own* `checkIdentityG`
certificate: feeding `checkIdentityG = true` (the `native_decide`-reachable self-check, supplied as the
hypothesis `hcheck`) into the field bridge `field_identity_of_checkIdentityG` yields `D(res) = a/d`. -/

/-- **★★ The reduced-case field identity from the engine's own `checkIdentityG` certificate** — for the
normal-part capstone output `res = cIntegrateReducedG Dt fuel a d cands`, if the engine's own cleared
antiderivative check passes (`checkIdentityG Dt res a d = true` — the Hermite half + RT half together
validate this, reachable by `native_decide` for any concrete run), then the field-level antiderivative
identity `D(g) + logResidueSumG Dt res.logs = amG a/amG d` holds over `RatFunc (CFieldSpec.K α)`, with
`g = amG res.rational.1/amG res.rational.2`. The normal-part `D(∫f) = f`, gated only on the engine's own
self-certificate — the transcendental analogue of `isGeneralRationalIntegral_of_roundtrip`. Pure
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
    (Dt : CPolyG α) (_fuel : ℕ) (a d : CPolyG α) (_cands : List α) (res : IntegralResultG α)
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
theorem field_identity_of_cIntegrateGFull_of_checkIdentityG_qfunNZG (Dt : CPolyG (QFunNZG ℚ)) (fuel : ℕ)
    (a d : CPolyG (QFunNZG ℚ)) (cands : List (QFunNZG ℚ)) (res : IntegralResultG (QFunNZG ℚ))
    (hgden : toPolyG res.rational.2 ≠ 0) (haden : toPolyG d ≠ 0)
    (hlogs : ∀ cv ∈ res.logs, toPolyG cv.2 ≠ 0)
    (hcheck : CPolyG.checkIdentityG Dt res a d = true) :
    towerFractionFieldDerivG Dt
        (amG (QFunNZG ℚ) (toPolyG res.rational.1) / amG (QFunNZG ℚ) (toPolyG res.rational.2))
        + logResidueSumG Dt res.logs
      = amG (QFunNZG ℚ) (toPolyG a) / amG (QFunNZG ℚ) (toPolyG d) :=
  field_identity_of_cIntegrateGFull_of_checkIdentityG Dt fuel a d cands res hgden haden hlogs hcheck

/-! ### Restatements against the intended wording (anonymous `example`s) -/

-- ★ THE HERMITE HALF (abstract, checker-free, no native_decide): the master telescoping `D(g) + h = a/d`
-- in the tower fraction field, given the per-power Hermite identities — the transcendental
-- `generalReduceRationalTelescope`.
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
example (Dt : CPolyG (QFunNZG ℚ)) (fuel : ℕ) (a d : CPolyG (QFunNZG ℚ)) (cands : List (QFunNZG ℚ))
    (res : IntegralResultG (QFunNZG ℚ))
    (hgden : toPolyG res.rational.2 ≠ 0) (haden : toPolyG d ≠ 0)
    (hlogs : ∀ cv ∈ res.logs, toPolyG cv.2 ≠ 0)
    (hcheck : CPolyG.checkIdentityG Dt res a d = true) :
    towerFractionFieldDerivG Dt
        (amG (QFunNZG ℚ) (toPolyG res.rational.1) / amG (QFunNZG ℚ) (toPolyG res.rational.2))
        + logResidueSumG Dt res.logs
      = amG (QFunNZG ℚ) (toPolyG a) / amG (QFunNZG ℚ) (toPolyG d) :=
  field_identity_of_cIntegrateGFull_of_checkIdentityG_qfunNZG Dt fuel a d cands res
    hgden haden hlogs hcheck

/-! ### Axiom audit — the Hermite half and the assembly rest only on the standard kernel axioms
(`propext`, `Classical.choice`, `Quot.sound`); no `native_decide`, no `sorry`. -/

#print axioms amG_toPolyG_fracAddG
#print axioms amG_toPolyG_foldl_fracAddG
#print axioms towerFractionFieldDerivG_amG_fracAccG
#print axioms sum_towerFractionFieldDerivG_telescope
#print axioms cHermiteReduceTowerG_telescope
#print axioms cHermiteReduceTowerG_telescope_seed
#print axioms field_identity_of_cIntegrateReducedG_of_checkIdentityG
#print axioms field_identity_of_cIntegrateGFull_of_checkIdentityG
#print axioms cHermiteReduceTowerG_telescope_seed_qfunNZG
#print axioms field_identity_of_cIntegrateGFull_of_checkIdentityG_qfunNZG

end DeepWiki.SymbolicIntegration
