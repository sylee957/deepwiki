import DeepWiki.SymbolicIntegration.ComputableGeneralDerivationInvariant
import DeepWiki.SymbolicIntegration.ComputableGeneralRationalSolve
import DeepWiki.SymbolicIntegration.ComputableGeneralWellFounded

/-! # The first abstractly-verified GENERAL-curve integral and the rational-part telescoping
`ComputableGeneralDerivationInvariant` proved `afDeriv` is a genuine derivation on the GENERAL carrier
`K(x)[y]/(f)` (additive `mk_toPolyG_afDeriv_add`, Leibniz `mk_toPolyG_afDeriv_afMul`) — the
implicit-function-theorem derivation `y' = −f_x/f_y` made an honest quotient identity through the keystone
`mk_toPolyG_afDeriv` (`afDeriv = implicitDeriv (toPolyG yprime)` mod `f`). `ComputableGeneralRationalSolve`
*computes* the rational part `v` (`afRationalSolve`: undetermined coefficients over the integral basis) and
validates `afDeriv f v = integrand` by `native_decide`.

This file takes the first step from "`afDeriv` is a derivation" to "**the general integrator is sound**",
mirroring the radical template `ComputableRadicalIntegralSoundness` (`predicate → first-integral →
telescoping`). The carrier `K(x)[y]/(f)` *is* the quotient `K[X] ⧸ (toPolyG f) = afIdeal f`, so — exactly
as for `afDeriv`'s derivation laws — the faithful statements live **in that quotient**, read through
`toPolyG` and `Ideal.Quotient.mk`. With **no `native_decide`** (axiom-clean `[propext, Classical.choice,
Quot.sound]`).

* **`IsGeneralRationalIntegral fuel f g v`** — the soundness predicate (rational part, no log term): `mk
  (toPolyG (afDeriv fuel f v)) = mk (toPolyG g)` in `K[X] ⧸ (toPolyG f)`. The general analogue of
  `IsRadicalRationalIntegral`; the named target the general-curve capstone `D(∫g) = g` grows into.

* **★ `mk_toPolyG_afDeriv_genGen`** — the **first abstractly-verified general integral** `D(y) = y'`: the
  generator `y` (`afBasisElem 1 = [0,1]`, reading `toPolyG = X`) integrates the implicit derivative
  `yprime = afYprime fuel f = −f_x/f_y` — `mk (toPolyG (afDeriv fuel f y)) = mk (toPolyG (afYprime fuel
  f))`. The general analogue of `radDeriv_radGen_sound_qx` (`D(√f) = f'/(nf)·√f`): `afDeriv` realizes
  `implicitDeriv (toPolyG yprime)` (keystone) and `implicitDeriv v X = v` (`implicitDeriv_X`), so `D(y)` is
  the rule `yprime` itself. Needs only `cnormG f ≠ []` — the generator identity `D(X) = yprime` is
  unconditional (no separability). Packaged as the predicate by `isGeneralRationalIntegral_gen`.

The **general rational-part telescoping** is then assembled (abstract quotient, general in `f`/`α`),
mirroring `radReduceRationalTelescope`:

* **`mk_toPolyG_afDeriv_foldlCaddG`** — `afDeriv` distributes over the integrator's accumulator `foldl
  caddG` in the quotient: `mk (toPolyG (afDeriv f (cs.foldl caddG acc))) = mk (toPolyG (afDeriv f acc)) +
  Σ_{c∈cs} mk (toPolyG (afDeriv f c))`. The exact accumulator structure `afRationalSolve` reassembles `v`
  by (`acc ↦ caddG acc contrib`); additivity (`mk_toPolyG_afDeriv_add`) pushed through the fold. The general
  analogue of `toPolyG_radDeriv_foldlRadAdd`.

* **`sum_mk_toPolyG_afDeriv_telescope`** — if each contribution's `afDeriv` is the *difference of
  consecutive leftovers* in the quotient, the sum telescopes to the endpoints. The general analogue of
  `sum_radDeriv_telescope`.

* **★ `generalReduceRationalTelescope`** — the **general rational-part telescoping soundness** (the abstract
  quotient identity): for a list of step contributions `cs` accumulated by `foldl caddG` (seed `[]`,
  `afDeriv [] ≡ 0`) and the leftover chain `L₀ :: rest` (`L₀` the original integrand, `rest.getLastD L₀`
  the final leftover), **given** each step's quotient equation `mk (afDeriv cⱼ) = mk Lⱼ − mk Lⱼ₊₁` (the
  per-step eq.-11 identity read in the carrier — the analogue of the radical's per-step cleared `K`-equation,
  taken as a hypothesis), the assembled antiderivative `v = cs.foldl caddG []` satisfies `mk (toPolyG
  (afDeriv f v)) + mk (toPolyG (final leftover)) = mk (toPolyG (original integrand))`, i.e. `afDeriv(v) =
  integrand − final-leftover` in the carrier. General in `f`, `α`; the precondition is the list of per-step
  eq.-11 quotient identities.

So the general-curve rational-part soundness is a theorem **modulo the per-step eq.-11 quotient identity**.
Because Trager's eq.-11 reduction (`Aᵢ ≡ −kUV'Bᵢ + T·Σⱼ BⱼMⱼᵢ mod V`) is a **coupled** congruence — heavier
than the radical's single cleared `radCase3Residual = 0` — the per-step identity is **isolated as the named
hypothesis** of `generalReduceRationalTelescope` and the telescoping is proven GIVEN it (exactly as the
radical telescoping took the per-step `K`-equations as hypotheses); discharging it for a concrete eq.-11 run
is the residual. The packaging `isGeneralRationalIntegral_of_telescope` reads the telescoping as the
predicate when the final leftover vanishes (genus-0 / no-pole case: `afDeriv(v) = integrand` exactly). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open scoped Differential

namespace CPolyG

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]

/-! ### The generator reading `toPolyG (afBasisElem 1) = X`

The general analogue of `toPolyG_radGen` (`toPolyG radGen = X`). The carrier generator `y` is `afBasisElem
1 = cshiftG 1 [1] = [0, 1]`, whose `toPolyG` image is the formal variable `X` (`X¹ · toPolyG [1] = X · 1 =
X`). The single fact that turns `implicitDeriv … X = …` into a statement about `afDeriv (afBasisElem 1)`. -/

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **`toPolyG (afBasisElem 1) = X`** — the carrier generator `y` (`afBasisElem 1 = [0, 1]`) reads as the
formal variable `X` under the Horner bridge: `afBasisElem 1 = cshiftG 1 [1]`, so `toPolyG = X¹ · toPolyG
[1] = X · 1 = X`. The general analogue of `toPolyG_radGen`; the fact behind `D(y) = yprime`. -/
theorem toPolyG_afBasisElem_one : toPolyG (afBasisElem 1 : CPolyG α) = X := by
  rw [afBasisElem, toPolyG_cshiftG, pow_one]
  have h1 : toPolyG ([CField.one] : CPolyG α) = 1 := by
    rw [toPolyG_cons, toPolyG_nil, mul_zero, add_zero, CFieldSpec.toK_one, map_one]
  rw [h1, mul_one]

/-! ### The soundness predicate and the first abstractly-verified general integral

`IsGeneralRationalIntegral fuel f g v` says the carrier element `v` is an antiderivative of the integrand
`g` in `K(x)[y]/(f)`, *rational part only* (no `Σ cᵢ log uᵢ` term): the genuine-carrier reading of `afDeriv
fuel f v = g`, modulo the curve ideal. The concrete witness is `v = y` (the generator) against `g = yprime`
(the implicit derivative). -/

/-- **The general rational-integral soundness predicate** `IsGeneralRationalIntegral fuel f g v` — the
carrier element `v` integrates `g` over `K(x)[y]/(f)`, *rational part* (no logarithmic term): the
genuine-carrier identity `mk (toPolyG (afDeriv fuel f v)) = mk (toPolyG g)` in `K[X] ⧸ (toPolyG f) = afIdeal
f`. The general analogue of `IsRadicalRationalIntegral`; the named soundness target the general-curve
capstone `D(∫g) = g` grows into. An instance is a concrete general-curve integral proven correct
**abstractly** (not by `native_decide`). -/
def IsGeneralRationalIntegral (fuel : ℕ) (f g v : CPolyG α) : Prop :=
  Ideal.Quotient.mk (afIdeal f) (toPolyG (afDeriv fuel f v))
    = Ideal.Quotient.mk (afIdeal f) (toPolyG g)

/-- **★ The first abstractly-verified general integral `D(y) = y'`** — the carrier generator `y`
(`afBasisElem 1`) integrates the implicit derivative `yprime = afYprime fuel f = −f_x/f_y`: `mk (toPolyG
(afDeriv fuel f (afBasisElem 1))) = mk (toPolyG (afYprime fuel f))` in `K[X] ⧸ (toPolyG f)`. The general
analogue of `radDeriv_radGen_sound_qx` (`D(√f) = f'/(nf)·√f`). The whole proof is the keystone
`mk_toPolyG_afDeriv` (`afDeriv` realizes `implicitDeriv (toPolyG yprime)` mod `f`) + `toPolyG_afBasisElem_one`
(`toPolyG y = X`) + Mathlib's `implicitDeriv_X` (`implicitDeriv v X = v`): `mk (afDeriv y) = mk (implicitDeriv
(toPolyG yprime) X) = mk (toPolyG yprime)`. General in `fuel`, the curve `f`, and `α`; needs **only** `cnormG
f ≠ []` (the generator identity `D(X) = yprime` is unconditional — no separability). -/
theorem mk_toPolyG_afDeriv_genGen (fuel : ℕ) (f : CPolyG α) (hf : cnormG f ≠ []) :
    Ideal.Quotient.mk (afIdeal f) (toPolyG (afDeriv fuel f (afBasisElem 1)))
      = Ideal.Quotient.mk (afIdeal f) (toPolyG (afYprime fuel f)) := by
  rw [mk_toPolyG_afDeriv fuel f _ hf, toPolyG_afBasisElem_one, Differential.implicitDeriv_X]

/-- **★ The general integral `D(y) = y'` as a soundness instance** — `IsGeneralRationalIntegral fuel f
(afYprime fuel f) (afBasisElem 1)`: the carrier generator `y` integrates the implicit derivative `yprime`,
packaged as the named predicate and proven abstractly via `mk_toPolyG_afDeriv_genGen`. The first concrete
general-curve integral as the named soundness predicate. -/
theorem isGeneralRationalIntegral_gen (fuel : ℕ) (f : CPolyG α) (hf : cnormG f ≠ []) :
    IsGeneralRationalIntegral fuel f (afYprime fuel f) (afBasisElem 1) :=
  mk_toPolyG_afDeriv_genGen fuel f hf

/-! ### The reduction TELESCOPING invariant (the genuinely new lemma)

The rational-part integrator `afRationalSolve` reassembles its antiderivative `v` as an **accumulator** fold
`Σ_{ij} c_{ij}·xʲwᵢ` — definitionally `cs.foldl caddG []` over the scaled basis monomials. Soundness of the
assembled `v` rests on the loop invariant `afDeriv(v) + leftover = original integrand` (in the carrier) being
preserved across the eq.-11 reduction steps.

Stripped to its mathematical core — which is what makes it provable *generally and abstractly* — the
invariant is a **telescoping of `afDeriv` over a list of contributions in the quotient**. Two ingredients,
mirroring the radical template:

* **`mk_toPolyG_afDeriv_foldlCaddG`** — `afDeriv` distributes over the accumulator `foldl caddG`: `mk
  (toPolyG (afDeriv f (cs.foldl caddG acc))) = mk (toPolyG (afDeriv f acc)) + Σ_{c∈cs} mk (toPolyG (afDeriv f
  c))`. Additivity (`mk_toPolyG_afDeriv_add`) pushed through the fold.

* **`sum_mk_toPolyG_afDeriv_telescope`** — if each contribution's `afDeriv` is the *difference of
  consecutive leftovers* (`mk (afDeriv cⱼ) = mk Lⱼ − mk Lⱼ₊₁`, the per-step eq.-11 identity read in the
  carrier), the sum telescopes to `mk L_head − mk L_last`.

Composing, the accumulated `v = cs.foldl caddG []` satisfies `mk (afDeriv v) + mk (final leftover) = mk
(initial integrand)` (`generalReduceRationalTelescope`): the **general rational-part soundness, as an
abstract quotient identity**, reduced to the per-step eq.-11 quotient identity over the engine's reduction
steps. -/

omit [CDiffFieldSpec α] in
/-- **`afDeriv` kills the seed `[]` modulo the curve ideal** — `mk (toPolyG (afDeriv fuel f [])) = 0` in
`K[X] ⧸ (toPolyG f)`, for a nonzero curve `f`. `afDeriv f [] = afReduce f (caddG [] (cmulG (cderivG [])
yprime))`, and `caddG`/`cmulG` of the empty list give `[]` (`toPolyG [] = 0`), so the reduced derivative is
`0` mod `f`. The accumulator seed `afRationalSolve` folds from; the general analogue of
`toPolyG_radDeriv_radZero`. -/
theorem mk_toPolyG_afDeriv_nil (fuel : ℕ) (f : CPolyG α) (hf : cnormG f ≠ []) :
    Ideal.Quotient.mk (afIdeal f) (toPolyG (afDeriv fuel f ([] : CPolyG α))) = 0 := by
  rw [show afDeriv fuel f ([] : CPolyG α) = afReduce f ([] : CPolyG α) from rfl,
    mk_toPolyG_afReduce f _ hf, toPolyG_nil, map_zero]

/-- **`afDeriv` distributes over the accumulator fold (in the quotient)** — `mk (toPolyG (afDeriv f
(cs.foldl caddG acc))) = mk (toPolyG (afDeriv f acc)) + (cs.map (fun c => mk (toPolyG (afDeriv f c)))).sum`,
for a nonzero curve `f`. The exact accumulator structure `afRationalSolve` reassembles `v` by (`acc ↦ caddG
acc contrib`), so its accumulated `afDeriv` is the sum of the per-step contributions plus the seed. Proven
by list induction on `cs`, generalizing the accumulator, with the single step `mk_toPolyG_afDeriv_add`
(additivity in the quotient). The general analogue of `toPolyG_radDeriv_foldlRadAdd`. -/
theorem mk_toPolyG_afDeriv_foldlCaddG (fuel : ℕ) (f : CPolyG α) (hf : cnormG f ≠ [])
    (acc : CPolyG α) (cs : List (CPolyG α)) :
    Ideal.Quotient.mk (afIdeal f) (toPolyG (afDeriv fuel f (cs.foldl caddG acc)))
      = Ideal.Quotient.mk (afIdeal f) (toPolyG (afDeriv fuel f acc))
        + (cs.map (fun c => Ideal.Quotient.mk (afIdeal f) (toPolyG (afDeriv fuel f c)))).sum := by
  induction cs generalizing acc with
  | nil => simp
  | cons c cs ih =>
    rw [List.foldl_cons, ih (caddG acc c), mk_toPolyG_afDeriv_add fuel f acc c hf, List.map_cons,
      List.sum_cons]
    ring

omit [CDiffFieldSpec α] in
/-- **The per-step contributions telescope (head/last form, in the quotient)** — for a head leftover `L₀`, a
tail list of leftovers `rest`, and contributions `cs` of the same length as `rest`, if each contribution's
`afDeriv`-image (in the carrier) is the difference of consecutive leftovers — phrased as: `cs` zipped against
the consecutive pairs of `L₀ :: rest` (i.e. `(L₀ :: rest).zip rest`) satisfies, head-to-head, `mk (toPolyG
(afDeriv f c)) = mk (toPolyG p.1) − mk (toPolyG p.2)` (the per-step eq.-11 identity) — then the sum of the
contributions' `afDeriv`-images is `mk (toPolyG L₀) − mk (toPolyG (rest.getLastD L₀))`. The clean telescoping
over the reduction: each step "moves one piece" from the leftover into the accumulator, the sum collapsing to
the endpoints. Stated via a parallel `List.Forall₂` recursion to keep the endpoints free of
index/non-emptiness proof obligations. The general analogue of `sum_radDeriv_telescope`. -/
theorem sum_mk_toPolyG_afDeriv_telescope (fuel : ℕ) (f : CPolyG α) :
    ∀ (L₀ : CPolyG α) (rest : List (CPolyG α)) (cs : List (CPolyG α)),
      List.Forall₂ (fun c p => Ideal.Quotient.mk (afIdeal f) (toPolyG (afDeriv fuel f c))
            = Ideal.Quotient.mk (afIdeal f) (toPolyG p.1)
              - Ideal.Quotient.mk (afIdeal f) (toPolyG p.2))
          cs ((L₀ :: rest).zip rest) →
      (cs.map (fun c => Ideal.Quotient.mk (afIdeal f) (toPolyG (afDeriv fuel f c)))).sum
        = Ideal.Quotient.mk (afIdeal f) (toPolyG L₀)
          - Ideal.Quotient.mk (afIdeal f) (toPolyG (rest.getLastD L₀)) := by
  intro L₀ rest
  induction rest generalizing L₀ with
  | nil =>
    intro cs hforall
    -- `(L₀ :: []).zip [] = []`, so `cs = []`; sum = 0 and `getLastD L₀ [] = L₀`
    simp only [List.zip_nil_right] at hforall
    rw [List.forall₂_nil_right_iff] at hforall
    subst hforall
    simp
  | cons L₁ rest' ih =>
    intro cs hforall
    -- `(L₀ :: L₁ :: rest').zip (L₁ :: rest') = (L₀, L₁) :: (L₁ :: rest').zip rest'`
    rw [List.zip_cons_cons] at hforall
    -- so `cs = c :: cs'` with the head step `afDeriv c = mk L₀ − mk L₁` + the tail
    rw [List.forall₂_cons_right_iff] at hforall
    obtain ⟨c, cs', h0, htail, rfl⟩ := hforall
    rw [List.map_cons, List.sum_cons, ih L₁ cs' htail, h0]
    -- `getLastD L₀ (L₁ :: rest') = getLastD L₁ rest'`
    rw [List.getLastD_cons]
    ring

/-- **★ The master general rational-part telescoping soundness (abstract, general)** — let `cs` be the list
of per-step contributions the rational-part reduction accumulates (each `caddG`-ed into the running `v`, from
the seed `[]`), and let `L₀ :: rest` be the chain of leftover integrands it passes through (`L₀` the
*original* integrand, `rest.getLastD L₀` the *final* leftover). If each contribution's `afDeriv`-image (in
the carrier) is the difference of the consecutive leftovers it sits between (the per-step eq.-11 identity,
read in the quotient and zipped as `(L₀ :: rest).zip rest`), then the accumulated antiderivative `v =
cs.foldl caddG []` satisfies the master soundness in `K[X] ⧸ (toPolyG f)`: `mk (toPolyG (afDeriv f v)) + mk
(toPolyG (final leftover)) = mk (toPolyG (original integrand))`, i.e. `afDeriv(v) = integrand −
final-leftover`. The general rational-part soundness as an abstract quotient identity, reduced exactly to the
per-step eq.-11 quotient identity — `afDeriv` distributes over the accumulator fold
(`mk_toPolyG_afDeriv_foldlCaddG`, seed `afDeriv [] ≡ 0`) and the contributions telescope
(`sum_mk_toPolyG_afDeriv_telescope`). The general analogue of `radReduceRationalTelescope`; instantiating the
hypothesis with the eq.-11 per-step congruence gives the soundness of `afRationalSolve`'s assembled `v`. -/
theorem generalReduceRationalTelescope (fuel : ℕ) (f : CPolyG α) (hf : cnormG f ≠ [])
    (L₀ : CPolyG α) (rest cs : List (CPolyG α))
    (hstep : List.Forall₂ (fun c p => Ideal.Quotient.mk (afIdeal f) (toPolyG (afDeriv fuel f c))
          = Ideal.Quotient.mk (afIdeal f) (toPolyG p.1)
            - Ideal.Quotient.mk (afIdeal f) (toPolyG p.2))
        cs ((L₀ :: rest).zip rest)) :
    Ideal.Quotient.mk (afIdeal f) (toPolyG (afDeriv fuel f (cs.foldl caddG ([] : CPolyG α))))
        + Ideal.Quotient.mk (afIdeal f) (toPolyG (rest.getLastD L₀))
      = Ideal.Quotient.mk (afIdeal f) (toPolyG L₀) := by
  rw [mk_toPolyG_afDeriv_foldlCaddG fuel f hf, mk_toPolyG_afDeriv_nil fuel f hf, zero_add,
    sum_mk_toPolyG_afDeriv_telescope fuel f L₀ rest cs hstep]
  ring

/-- **The telescoping reads as the predicate when the final leftover vanishes** (genus-0 / no-pole case) —
if the per-step eq.-11 identities hold (`hstep`) **and** the final leftover is `0` in the carrier (`mk
(toPolyG (rest.getLastD L₀)) = 0`), then the assembled antiderivative `v = cs.foldl caddG []` is a *complete*
antiderivative of the original integrand `L₀`: `IsGeneralRationalIntegral fuel f L₀ v`. The genus-0 hallmark
— when the reduction leaves no simple-pole residual, `afDeriv(v) = integrand` exactly (the rational part is
the whole integral), as in the cusp `∫ y dx = (2/5)xy` (`cusp_intY_fully_rational`). Reads the master
telescoping `generalReduceRationalTelescope` into the named predicate. -/
theorem isGeneralRationalIntegral_of_telescope (fuel : ℕ) (f : CPolyG α) (hf : cnormG f ≠ [])
    (L₀ : CPolyG α) (rest cs : List (CPolyG α))
    (hstep : List.Forall₂ (fun c p => Ideal.Quotient.mk (afIdeal f) (toPolyG (afDeriv fuel f c))
          = Ideal.Quotient.mk (afIdeal f) (toPolyG p.1)
            - Ideal.Quotient.mk (afIdeal f) (toPolyG p.2))
        cs ((L₀ :: rest).zip rest))
    (hleft : Ideal.Quotient.mk (afIdeal f) (toPolyG (rest.getLastD L₀)) = 0) :
    IsGeneralRationalIntegral fuel f L₀ (cs.foldl caddG ([] : CPolyG α)) := by
  have hkey := generalReduceRationalTelescope fuel f hf L₀ rest cs hstep
  rw [hleft, add_zero] at hkey
  exact hkey

/-! ### ★ The general round-trip soundness — the DIRECT path (no eq.-11 `hstep` chain)

The rational-part integrator `afRationalSolve` (and the combined `afIntegrateAlgebraic`) *derive* the
antiderivative `v` and **validate** the output by an engine round-trip check `cisZeroG (csubG (afDeriv fuel
f v) g) = true` — the `native_decide`-tested form (the `afRationalSolve_*` theorems of
`ComputableGeneralRationalSolve` round-trip exactly this). This is the general analogue of the radical's
`radIsZero (radSub (algDeriv ρ F) integrand) = true` certificate, and reading it abstractly is the **direct
path** to the soundness predicate `IsGeneralRationalIntegral`: it bypasses the per-step eq.-11 congruence
`hstep` chain entirely (exactly as `toPolyG_algDeriv_eq_of_roundtrip` bypassed the radical's per-step
extraction).

`cisZeroG p = true ↔ toPolyG p = 0` (`cisZeroG_iff`, unconditional), so the engine check `cisZeroG (csubG
(afDeriv f v) g) = true` gives the **free-polynomial** identity `toPolyG (afDeriv f v) = toPolyG g` in `K[X]`
— *stronger* than the carrier-quotient `IsGeneralRationalIntegral`, which it implies by mapping through
`Ideal.Quotient.mk`. Both directions are axiom-clean (no `native_decide`); the `cnormG f ≠ []` hypothesis is
**not** needed (the round-trip read is pure `toPolyG`/`cisZeroG` bookkeeping). -/

omit [CDiffFieldSpec α] in
/-- **★ The general round-trip certificate IS the free-polynomial integrand identity** — the engine's own
round-trip check `cisZeroG (csubG (afDeriv fuel f v) g) = true` (the `native_decide`-validated form the
`afRationalSolve` round-trips use, e.g. `afRationalSolve_cuspCubic_intY`) yields the genuine-field identity
`toPolyG (afDeriv fuel f v) = toPolyG g` in `K[X]` (`K = CFieldSpec.K α`). The general analogue of
`toPolyG_algDeriv_eq_of_roundtrip`. Axiom-clean (no `native_decide`): `cisZeroG p = true ↔ toPolyG p = 0`
(`cisZeroG_iff`) + `toPolyG_csubG` + `sub_eq_zero`. The DIRECT path — the integrator's validated output IS
`afDeriv(v) = g` in `K[X]`, read abstractly, with **no** eq.-11 per-step chain and **no** `cnormG f ≠ []`. -/
theorem toPolyG_afDeriv_eq_of_roundtrip (fuel : ℕ) (f v g : CPolyG α)
    (hcheck : cisZeroG (csubG (afDeriv fuel f v) g) = true) :
    toPolyG (afDeriv fuel f v) = toPolyG g := by
  rw [cisZeroG_iff, toPolyG_csubG, sub_eq_zero] at hcheck
  exact hcheck

omit [CDiffFieldSpec α] in
/-- **★ The general round-trip soundness — engine check ⟹ the predicate** — the engine's round-trip check
`cisZeroG (csubG (afDeriv fuel f v) g) = true` discharges the soundness predicate `IsGeneralRationalIntegral
fuel f g v` (`mk (toPolyG (afDeriv fuel f v)) = mk (toPolyG g)` in `K[X] ⧸ (toPolyG f)`). The general
analogue of the radical rational-part closure: `toPolyG_afDeriv_eq_of_roundtrip` gives the free-polynomial
identity `toPolyG (afDeriv f v) = toPolyG g`, and mapping through `Ideal.Quotient.mk` lands the
carrier-quotient predicate. This makes `afDeriv(afRationalSolve g) = g` self-contained for the general
rational part — modulo only the one engine round-trip check (the `native_decide`-validated `hcheck`), no
eq.-11 `hstep` chain. Axiom-clean (no `native_decide`). -/
theorem isGeneralRationalIntegral_of_roundtrip (fuel : ℕ) (f v g : CPolyG α)
    (hcheck : cisZeroG (csubG (afDeriv fuel f v) g) = true) :
    IsGeneralRationalIntegral fuel f g v :=
  congrArg (Ideal.Quotient.mk (afIdeal f)) (toPolyG_afDeriv_eq_of_roundtrip fuel f v g hcheck)

/-! ### The fuel-free rational-integral wrappers

The Wf derivation now has the same quotient API as `afDeriv`, so the rational-part predicate, generator
example, telescoping, and round-trip closure can be stated without a fuel parameter. The proofs are the same
structural arguments as the fueled versions, replacing the derivation lemmas by their Wf twins. -/

/-- The fuel-free general rational-integral soundness predicate. -/
def IsGeneralRationalIntegralWf (f g v : CPolyG α) : Prop :=
  Ideal.Quotient.mk (afIdeal f) (toPolyG (afDerivWf f v))
    = Ideal.Quotient.mk (afIdeal f) (toPolyG g)

/-- The fuel-free generator identity `D(y) = y'` in the quotient. -/
theorem mk_toPolyG_afDerivWf_genGen (f : CPolyG α) (hf : cnormG f ≠ []) :
    Ideal.Quotient.mk (afIdeal f) (toPolyG (afDerivWf f (afBasisElem 1)))
      = Ideal.Quotient.mk (afIdeal f) (toPolyG (afYprimeWf f)) := by
  rw [mk_toPolyG_afDerivWf f _ hf, toPolyG_afBasisElem_one, Differential.implicitDeriv_X]

/-- The fuel-free generator identity packaged as `IsGeneralRationalIntegralWf`. -/
theorem isGeneralRationalIntegralWf_gen (f : CPolyG α) (hf : cnormG f ≠ []) :
    IsGeneralRationalIntegralWf f (afYprimeWf f) (afBasisElem 1) :=
  mk_toPolyG_afDerivWf_genGen f hf

omit [CDiffFieldSpec α] in
/-- `afDerivWf` kills the seed `[]` modulo the curve ideal. -/
theorem mk_toPolyG_afDerivWf_nil (f : CPolyG α) (hf : cnormG f ≠ []) :
    Ideal.Quotient.mk (afIdeal f) (toPolyG (afDerivWf f ([] : CPolyG α))) = 0 := by
  rw [show afDerivWf f ([] : CPolyG α) = afReduce f ([] : CPolyG α) from rfl,
    mk_toPolyG_afReduce f _ hf, toPolyG_nil, map_zero]

/-- `afDerivWf` distributes over the accumulator fold in the quotient. -/
theorem mk_toPolyG_afDerivWf_foldlCaddG (f : CPolyG α) (hf : cnormG f ≠ [])
    (acc : CPolyG α) (cs : List (CPolyG α)) :
    Ideal.Quotient.mk (afIdeal f) (toPolyG (afDerivWf f (cs.foldl caddG acc)))
      = Ideal.Quotient.mk (afIdeal f) (toPolyG (afDerivWf f acc))
        + (cs.map (fun c => Ideal.Quotient.mk (afIdeal f) (toPolyG (afDerivWf f c)))).sum := by
  induction cs generalizing acc with
  | nil => simp
  | cons c cs ih =>
    rw [List.foldl_cons, ih (caddG acc c), mk_toPolyG_afDerivWf_add f acc c hf, List.map_cons,
      List.sum_cons]
    ring

omit [CDiffFieldSpec α] in
/-- The fuel-free per-step contributions telescope in the quotient. -/
theorem sum_mk_toPolyG_afDerivWf_telescope (f : CPolyG α) :
    ∀ (L₀ : CPolyG α) (rest : List (CPolyG α)) (cs : List (CPolyG α)),
      List.Forall₂ (fun c p => Ideal.Quotient.mk (afIdeal f) (toPolyG (afDerivWf f c))
            = Ideal.Quotient.mk (afIdeal f) (toPolyG p.1)
              - Ideal.Quotient.mk (afIdeal f) (toPolyG p.2))
          cs ((L₀ :: rest).zip rest) →
      (cs.map (fun c => Ideal.Quotient.mk (afIdeal f) (toPolyG (afDerivWf f c)))).sum
        = Ideal.Quotient.mk (afIdeal f) (toPolyG L₀)
          - Ideal.Quotient.mk (afIdeal f) (toPolyG (rest.getLastD L₀)) := by
  intro L₀ rest
  induction rest generalizing L₀ with
  | nil =>
    intro cs hforall
    simp only [List.zip_nil_right] at hforall
    rw [List.forall₂_nil_right_iff] at hforall
    subst hforall
    simp
  | cons L₁ rest' ih =>
    intro cs hforall
    rw [List.zip_cons_cons] at hforall
    rw [List.forall₂_cons_right_iff] at hforall
    obtain ⟨c, cs', h0, htail, rfl⟩ := hforall
    rw [List.map_cons, List.sum_cons, ih L₁ cs' htail, h0]
    rw [List.getLastD_cons]
    ring

/-- The fuel-free master rational-part telescoping soundness. -/
theorem generalReduceRationalTelescopeWf (f : CPolyG α) (hf : cnormG f ≠ [])
    (L₀ : CPolyG α) (rest cs : List (CPolyG α))
    (hstep : List.Forall₂ (fun c p => Ideal.Quotient.mk (afIdeal f) (toPolyG (afDerivWf f c))
          = Ideal.Quotient.mk (afIdeal f) (toPolyG p.1)
            - Ideal.Quotient.mk (afIdeal f) (toPolyG p.2))
        cs ((L₀ :: rest).zip rest)) :
    Ideal.Quotient.mk (afIdeal f) (toPolyG (afDerivWf f (cs.foldl caddG ([] : CPolyG α))))
        + Ideal.Quotient.mk (afIdeal f) (toPolyG (rest.getLastD L₀))
      = Ideal.Quotient.mk (afIdeal f) (toPolyG L₀) := by
  rw [mk_toPolyG_afDerivWf_foldlCaddG f hf, mk_toPolyG_afDerivWf_nil f hf, zero_add,
    sum_mk_toPolyG_afDerivWf_telescope f L₀ rest cs hstep]
  ring

/-- The fuel-free telescoping predicate when the final leftover vanishes. -/
theorem isGeneralRationalIntegralWf_of_telescope (f : CPolyG α) (hf : cnormG f ≠ [])
    (L₀ : CPolyG α) (rest cs : List (CPolyG α))
    (hstep : List.Forall₂ (fun c p => Ideal.Quotient.mk (afIdeal f) (toPolyG (afDerivWf f c))
          = Ideal.Quotient.mk (afIdeal f) (toPolyG p.1)
            - Ideal.Quotient.mk (afIdeal f) (toPolyG p.2))
        cs ((L₀ :: rest).zip rest))
    (hleft : Ideal.Quotient.mk (afIdeal f) (toPolyG (rest.getLastD L₀)) = 0) :
    IsGeneralRationalIntegralWf f L₀ (cs.foldl caddG ([] : CPolyG α)) := by
  have hkey := generalReduceRationalTelescopeWf f hf L₀ rest cs hstep
  rw [hleft, add_zero] at hkey
  exact hkey

omit [CDiffFieldSpec α] in
/-- The `afDerivWf` round-trip check discharges `IsGeneralRationalIntegralWf`. -/
theorem isGeneralRationalIntegralWf_of_roundtrip (f v g : CPolyG α)
    (hcheck : cisZeroG (csubG (afDerivWf f v) g) = true) :
    IsGeneralRationalIntegralWf f g v :=
  congrArg (Ideal.Quotient.mk (afIdeal f)) (toPolyG_afDerivWf_eq_of_roundtrip f v g hcheck)

end CPolyG

/-! ### ★ The NAMED general driver run `∫ y dx = (3/5)·x·y` on `y³ = x²`, abstractly (via the round-trip)

The `afRationalSolve` named run on `∫ y dx` over the cuspidal cubic `y³ = x²` (`gcuspCubicSolvedIntY =
afRationalSolve 8 gcuspCubicF gcuspCubicBasis 1 gcuspCubicY`, `ComputableGeneralRationalSolve`) DERIVES the
rational part `v = (3/5)x·y` and the engine validates `afDeriv 8 gcuspCubicF v = y` by `native_decide`
(`afRationalSolve_cuspCubic_intY`). Here that soundness is proven **abstractly** (`[propext,
Classical.choice, Quot.sound]`, no `native_decide`) **from the engine's own round-trip check** of the
derived `v` (supplied as the explicit hypothesis `hcheck` — the run's `afRationalSolve` output and its check
are reachable for `ℚ` *only* through `native_decide`, since `decide`/`rfl` get stuck on `ℚ` arithmetic, so
the check is stated rather than discharged): `isGeneralRationalIntegral_of_roundtrip` reads it directly into
the carrier predicate. The remaining precondition is exactly `hcheck` — the engine's own round-trip
certificate for the run. The general analogue of `isRadicalRationalIntegral_c3itRun`. -/

open CPolyG

/-- **★ The named general run `∫ y dx = (3/5)x·y` on `y³ = x²` is sound, abstractly** —
`IsGeneralRationalIntegral 8 gcuspCubicF gcuspCubicY v` for the run's derived rational part `v`, i.e. `mk
(toPolyG (afDeriv 8 gcuspCubicF v)) = mk (toPolyG gcuspCubicY)` in `K[X] ⧸ (toPolyG (y³−x²))`: the GENERAL
derivation of the derived `v = (3/5)x·y` equals the integrand `y` in the carrier. Proven abstractly (no
`native_decide`) **from the engine's own round-trip check** `hcheck : cisZeroG (csubG (afDeriv 8 gcuspCubicF
v) gcuspCubicY) = true` (the `native_decide` fact `afRationalSolve_cuspCubic_intY`, here read abstractly):
`isGeneralRationalIntegral_of_roundtrip` lands it directly. The engine's `native_decide` round-trip, here a
**theorem of the abstract general derivation modulo the one round-trip check**. -/
theorem isGeneralRationalIntegral_cuspCubic_intY (v : CPolyG (QFunNZG ℚ))
    (hcheck : cisZeroG (csubG (afDeriv 8 gcuspCubicF v) gcuspCubicY) = true) :
    IsGeneralRationalIntegral 8 gcuspCubicF gcuspCubicY v :=
  isGeneralRationalIntegral_of_roundtrip 8 gcuspCubicF v gcuspCubicY hcheck

/-! ### `#print axioms` — the first general integral and the rational-part telescoping are axiom-clean

The first general integral `D(y) = y'`, its predicate packaging, the accumulator-fold distribution, the
telescoping, the master rational-part telescoping soundness, **and the round-trip soundness** carry **only**
the standard `[propext, Classical.choice, Quot.sound]` — no `native_decide` compiler axiom, no `sorry`. The
general analogues of the radical template's `radDeriv_radGen_sound_qx` / `radReduceRationalTelescope` /
`radDeriv_foldlRadAdd_zero_cons_telescope` and the round-trip `toPolyG_algDeriv_eq_of_roundtrip`, proven
generally over an arbitrary curve `f`.

**Two paths to `IsGeneralRationalIntegral` are now closed.** (1) The **telescoping**
(`generalReduceRationalTelescope`): the assembled `v = foldl caddG []` integrates the integrand modulo the
final leftover, *given* the per-step eq.-11 quotient identities (the coupled congruence `Aᵢ ≡ −kUV'Bᵢ +
T·Σⱼ BⱼMⱼᵢ mod V`, the named `hstep` hypothesis) — the structural decomposition. (2) The **round-trip**
(`isGeneralRationalIntegral_of_roundtrip`, the DIRECT path): the integrator's own engine check `cisZeroG
(csubG (afDeriv f v) g) = true` reads — via `cisZeroG_iff` + `toPolyG_csubG`, axiom-clean and
unconditional — straight into `IsGeneralRationalIntegral fuel f g v`, bypassing the eq.-11 chain entirely.
So `afDeriv(afRationalSolve g) = g` is **self-contained for the general rational part modulo only the one
engine round-trip check** (the `native_decide`-validated `hcheck`), the analogue of the radical rational-part
closure — `isGeneralRationalIntegral_cuspCubic_intY` is the literal `∫ y dx = (3/5)xy` run on `y³ = x²`,
abstractly, from its own certificate. -/

-- ★ The first abstractly-verified general integral `D(y) = y'` and its predicate packaging:
#print axioms CPolyG.mk_toPolyG_afDeriv_genGen
#print axioms CPolyG.isGeneralRationalIntegral_gen

-- The accumulator-fold distribution of `afDeriv` (additivity pushed through `foldl caddG`):
#print axioms CPolyG.mk_toPolyG_afDeriv_foldlCaddG

-- ★ The master general rational-part telescoping soundness (the genuinely-new accumulation lemma):
#print axioms CPolyG.generalReduceRationalTelescope

-- The genus-0 packaging: vanishing final leftover ⟹ the assembled `v` is a complete antiderivative:
#print axioms CPolyG.isGeneralRationalIntegral_of_telescope

-- ★ The general round-trip certificate IS the free-polynomial integrand identity `afDeriv(v) = g` in K[X]:
#print axioms CPolyG.toPolyG_afDeriv_eq_of_roundtrip

-- ★★ The general round-trip soundness (the DIRECT path): engine check ⟹ the carrier predicate:
#print axioms CPolyG.isGeneralRationalIntegral_of_roundtrip

-- The fuel-free rational predicate and Wf telescoping path:
#print axioms CPolyG.isGeneralRationalIntegralWf_gen
#print axioms CPolyG.generalReduceRationalTelescopeWf
#print axioms CPolyG.isGeneralRationalIntegralWf_of_telescope

-- The fuel-free round-trip soundness (the DIRECT path): engine check ⟹ the carrier predicate:
#print axioms CPolyG.isGeneralRationalIntegralWf_of_roundtrip

-- ★ The NAMED run `∫ y dx = (3/5)xy` on `y³ = x²`, abstractly, from its own round-trip certificate:
#print axioms isGeneralRationalIntegral_cuspCubic_intY

end DeepWiki.SymbolicIntegration
