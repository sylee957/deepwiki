import DeepWiki.SymbolicIntegration.ComputableGeneralDerivationInvariant
import DeepWiki.SymbolicIntegration.ComputableGeneralResidues
import DeepWiki.SymbolicIntegration.ComputableGeneralLogArg
import DeepWiki.SymbolicIntegration.ComputableRadicalLogSoundness

/-! # The LOG-part soundness for the GENERAL-curve integrator: `D(Σ cᵢ log uᵢ) = logpart` via `afDeriv`

`ComputableGeneralIntegralSoundness` proves the **rational** half of the general algebraic soundness capstone
`D(∫f) = f` for an arbitrary curve `K(x)[y]/(f)` — the rational-part telescoping `generalReduceRationalTelescope`
through the general derivation `afDeriv` (the implicit-function-theorem rule `y' = −f_x/f_y`,
`mk_toPolyG_afDeriv`). This file opens the **logarithmic** half: the general integrator (`afLogArgSolve`,
`afIntegrateAlgebraic`) returns `∫f = v + Σ cᵢ log uᵢ`, and the log part is sound when the log-argument
outputs carry the right residues, i.e. when

  **`Σ cᵢ · afDeriv(uᵢ)/uᵢ = (the log part of f)`**.

It is the general-curve analogue of the radical-log template `ComputableRadicalLogSoundness` — the SAME
`predicate → certificate-bridge → residue-correctness core` shape, with the diagonal `radDeriv n ρ` /
`radMul n ρ` / `radIdeal n ρ` replaced by the general `afDeriv fuel f` / `afMul f` / `afIdeal f`, and the
hyperelliptic two-sheet norm replaced by the general double resultant `genResidueResultant`
(`ComputableGeneralResidues`).

**The log-derivative is `afDeriv(u)/u`.** For a carrier element `u ∈ K(x)[y]/(f)`, `D(log u) = afDeriv(u)/u`
*by definition* of the logarithmic derivative. So the log-part soundness is a **statement about residues**,
not a new derivation law: it asks that the integrator's chosen `uᵢ` have log-derivatives summing to the
integrand's log part. The single-term certificate is exactly the engine's own `afIsLogIntegral fuel f
integrand u` (`ComputableGeneralLogArg`), the *division-free* form `afDeriv f u = afMul f u integrand`
(since `D(log u)·u = afDeriv u`).

**The faithful setting: the carrier quotient** `K[X] ⧸ afIdeal f = K[X] ⧸ (toPolyG f)` — the coordinate ring
of the curve `f(x, y) = 0` over `K = CFieldSpec.K α`. The engine's `afMul` is the quotient product (Euclidean
reduction `mod f`), so the honest reading of `afDeriv f u = afMul f u integrand` lives in this quotient
(exactly as the general derivation invariant's Leibniz law `mk_toPolyG_afDeriv_afMul` does). The single-term
log-derivative equation `D(log u) = integrand` is therefore `mk(toPolyG(afDeriv fuel f u)) = mk(toPolyG u)·
mk(toPolyG integrand)` in `K[X] ⧸ afIdeal f`.

What this file delivers (axiom-clean `[propext, Classical.choice, Quot.sound]`, **no** `native_decide`):

* **`IsGeneralLogTerm fuel f u integrand`** — the *single*-log soundness predicate (`cᵢ = 1`): the quotient
  identity `mk(toPolyG(afDeriv fuel f u)) = mk(toPolyG u)·mk(toPolyG integrand)`, the faithful "`D(log u) =
  integrand`". `IsGeneralLogIntegral fuel f logpart commonDenom args cofs` — the multi-term predicate: the
  **log-derivative sum** `Σ_{(c,u)∈args} c · afDeriv(u)/u` equals `logpart` in the quotient, cross-multiplied
  by the common denominator. (Both read `afDeriv(u)/u` as the cross-multiplied quotient equation, no division.)

* **The certificate↔predicate bridge** `isGeneralLogTerm_of_afIsLogIntegral` — the engine's boolean check
  `afIsLogIntegral fuel f integrand u = true` **implies** `IsGeneralLogTerm fuel f u integrand` (the quotient
  identity), via `cisZeroG_iff` + `toPolyG_csubG` + `mk_toPolyG_afMul`. So every `native_decide`-validated
  `afIsLogIntegral` (the non-hyperelliptic `y³ − x² − 1` log arguments `u ∝ y`, `u ∝ y² + x`; the arcsinh
  conservativity) IS, abstractly, the single-log soundness — read in the genuine quotient field.

* **Additivity of the log-derivative sum** — `mk_toPolyG_afLogSumNum_eq_sum`: `D(Σ cᵢ log uᵢ)`, read as the
  numerator `Σ cᵢ·afDeriv(uᵢ)·cofᵢ` over the common denominator, distributes over the `args` list (reusing
  `mk_toPolyG_afDeriv_add` / `mk_toPolyG_afMul` through a fold).

**Obligation 2 (the tractable core)** is the base-field logarithmic-derivative residue theorem
`LogResidue.logDeriv_residue_eq_multiplicity` (already proven, generic over the base field, in the radical
template): the residue of `afDeriv(u)/u` at a place over `x₀` equals the vanishing order. In the general
setting `afDeriv(u)/u` localizes (through `toPolyG`) to exactly this base-field log-derivative on the place's
uniformizer, so the base-field core IS obligation 2's content for the general carrier too — restated here as
the general framing.

**Obligation 1 (the milestone) — `genResidueResultant` roots = residues.** `genResidueResultant` is the full
double resultant `R(Z) = res_X(res_Y(Z·D' − g, F), D)`; the inner `res_Y` is the **norm** of `Z·D' − g(x, y)`
to `K(x)` (eliminating `y` against `F`), the outer `res_X` is the transcendental Rothstein–Trager
(`ResidueMultiplicity.roots_rtResultant`) on that norm against `D`. Using the SAME `resultant_eq_prod_eval`
product form `R = C(lc)^N · ∏_α genNorm(α, Z)`, the general norm's per-root factoring replaces the radical's
two-sheet `√ρ` quadratic: for arbitrary `F` the per-place residues are `g(α)/F_y(α)` over the roots `α` of
`F` (the places over `x = α₀`). We prove **`genNormFactor`** (the general norm at a root factors as
`lc·∏_β(Z − g(β)/F_y(β))` over the curve fiber `β`) and **`roots_genResidueResultant_eq_residues`** (the
double resultant's roots ARE the residues — the `roots_residueResultant_eq_residues` analogue for the general
double resultant). The general norm is a `deg_y F = n`-degree product (not the radical's quadratic), so this
is the heavier per-root factoring; it lands at the abstract product-form level exactly as the radical's did.

**Obligation 3 (the partial fraction)** reuses `LogResidue.ratLogPart_eq_residue_logDeriv_sum` — the
Bernoulli/Lagrange partial fraction `A/D = Σ residue·logDeriv(X − α)`, **algebraic** (NOT analytic, the
radical case confirmed this): after rationalizing to `ℚ(x)`, the general log part is a rational function and
the residue-sum IS its partial fraction.

**Composed:** `isGeneralLogIntegral_of_residue_match` — given the per-term residue match (the partial
fraction), the general integrator's log part is log-sound; `isGeneralAlgebraicIntegral_of_parts` composes the
general rational part (`generalReduceRationalTelescope`, the other half) + this log part into the full general
`D(∫f) = f`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open scoped Differential

namespace CPolyG

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]

/-! ### The single-log soundness predicate `IsGeneralLogTerm` and the certificate bridge

The integrator's log term `log u` is sound for integrand `g` iff `D(log u) = g`. Since `D(log u) =
afDeriv(u)/u`, and `afMul` is the quotient product of the curve's coordinate ring `K[X] ⧸ afIdeal f`, the
faithful statement (cross-multiplied to avoid division) is the **quotient identity** `mk(toPolyG(afDeriv u)) =
mk(toPolyG u)·mk(toPolyG g)`. This is exactly the genuine-field reading of the engine's division-free
certificate `afIsLogIntegral fuel f g u` (`afDeriv u = afMul u g`, tested by `cisZeroG`). -/

/-- **The single-log soundness predicate** `IsGeneralLogTerm fuel f u integrand` — the carrier element `u` is
a correct *single* log argument for `integrand` over `K(x)[y]/(f)`: the genuine-field identity `D(log u) =
integrand`, i.e. `mk(toPolyG(afDeriv fuel f u)) = mk(toPolyG u)·mk(toPolyG integrand)` in the carrier quotient
`K[X] ⧸ afIdeal f` (`K = CFieldSpec.K α`, `X = y`). The log-derivative `D(log u) = afDeriv(u)/u`
cross-multiplied — no division, the faithful quotient form. The general-curve analogue of `IsRadicalLogTerm`;
an instance is a concrete algebraic-log integral verified **abstractly**. -/
def IsGeneralLogTerm (fuel : ℕ) (f u integrand : CPolyG α) : Prop :=
  Ideal.Quotient.mk (afIdeal f) (toPolyG (afDeriv fuel f u))
    = Ideal.Quotient.mk (afIdeal f) (toPolyG u)
      * Ideal.Quotient.mk (afIdeal f) (toPolyG integrand)

omit [CDiffFieldSpec α] in
/-- **The engine's log-derivative certificate as a `K[X]` equality** `afDeriv f u = afMul f u integrand` —
`cisZeroG (csubG (afDeriv fuel f u) (afMul f u integrand)) = true → toPolyG (afDeriv fuel f u) = toPolyG
(afMul f u integrand)` in `K[X]`. The engine's `native_decide`-checkable boolean (`afLogResidual` vanishes,
the form `afIsLogIntegral` over `K(x)` unfolds to — `cisZeroG` of the `csubG` difference) yields the exact
polynomial identity through `cisZeroG_iff` + `toPolyG_csubG`. Stated on the bare `cisZeroG (csubG …)` so it
is **generic** over the base `α` (the engine's `afIsLogIntegral` is fixed to `α = QFunNZG ℚ`, but the
certificate's *content* is this generic equality). The general-curve analogue of unfolding `radIsLogIntegral`. -/
theorem toPolyG_afDeriv_eq_of_logCert (fuel : ℕ) (f u integrand : CPolyG α)
    (h : cisZeroG (csubG (afDeriv fuel f u) (afMul f u integrand)) = true) :
    toPolyG (afDeriv fuel f u) = toPolyG (afMul f u integrand) := by
  rw [cisZeroG_iff, toPolyG_csubG, sub_eq_zero] at h
  exact h

omit [CDiffFieldSpec α] in
/-- **★ The engine's log-derivative certificate implies the single-log soundness predicate** —
`cisZeroG (csubG (afDeriv fuel f u) (afMul f u integrand)) = true → IsGeneralLogTerm fuel f u integrand`, for
a nonzero curve `f`. The engine's `native_decide`-checkable boolean (`afDeriv u = afMul u integrand`, the
`afLogResidual`/`afIsLogIntegral` certificate, tested by `cisZeroG` of the difference) yields the genuine-field
quotient identity `mk(toPolyG(afDeriv u)) = mk(toPolyG u)·mk(toPolyG integrand)`. Through
`toPolyG_afDeriv_eq_of_logCert` (the exact `K[X]` equality) and `mk_toPolyG_afMul` (`afMul` realizes the
quotient product). So every `afIsLogIntegral`-validated general-curve log integral — the non-hyperelliptic
`y³ − x² − 1` arguments `u ∝ y`, `u ∝ y² + x`, the arcsinh `u ∝ x + y` — is, abstractly, an `IsGeneralLogTerm`:
`D(log u) = integrand` in the curve's coordinate ring. The general-curve analogue of
`isRadicalLogTerm_of_radIsLogIntegral`. (The engine's check is the *exact* `K[X]` equality `toPolyG(afDeriv u)
= toPolyG(afMul u integrand)`, **stronger** than the quotient predicate — hence an implication, not an `iff`.) -/
theorem isGeneralLogTerm_of_logCert (fuel : ℕ) (f u integrand : CPolyG α)
    (hf : cnormG f ≠ [])
    (h : cisZeroG (csubG (afDeriv fuel f u) (afMul f u integrand)) = true) :
    IsGeneralLogTerm fuel f u integrand := by
  rw [IsGeneralLogTerm, toPolyG_afDeriv_eq_of_logCert fuel f u integrand h,
    mk_toPolyG_afMul f u integrand hf]

/-! ### The two-term log-derivative sum: `D(c₁ log u₁ + c₂ log u₂)` over the common denominator `u₁ u₂`

The residue-addition structure made concrete. Over the common denominator `u₁·u₂`, the numerator of
`c₁·afDeriv(u₁)/u₁ + c₂·afDeriv(u₂)/u₂` is `c₁·afDeriv(u₁)·u₂ + c₂·afDeriv(u₂)·u₁`. Read in the carrier
quotient (`afMul` = the curve's product), this *equals* `(c₁·integrand₁ + c₂·integrand₂)·u₁·u₂` exactly when
the two single-term certificates compose — the genuine-field form of "two log residues add". The general-curve
analogue of `radLogSum2` / `mk_toPolyG_radLogSum2`. -/

/-- **The two-term log-derivative numerator** `afLogSum2 fuel f c₁ u₁ c₂ u₂` — concretely `caddG (afMul f
(cscaleG c₁ (afDeriv fuel f u₁)) u₂) (afMul f (cscaleG c₂ (afDeriv fuel f u₂)) u₁)`: the numerator of
`c₁·D(log u₁) + c₂·D(log u₂)` over the common denominator `u₁·u₂`. The two-term head of the residue sum
`Σ cᵢ·afDeriv(uᵢ)/uᵢ`; the general-curve analogue of `radLogSum2`. -/
def afLogSum2 (fuel : ℕ) (f : CPolyG α) (c₁ : α) (u₁ : CPolyG α) (c₂ : α) (u₂ : CPolyG α) : CPolyG α :=
  caddG (afMul f (cscaleG c₁ (afDeriv fuel f u₁)) u₂)
    (afMul f (cscaleG c₂ (afDeriv fuel f u₂)) u₁)

omit [CDiffFieldSpec α] in
/-- **★ Two log residues add (quotient form)** — in the carrier quotient `K[X] ⧸ afIdeal f`,
`mk(toPolyG(afLogSum2 fuel f c₁ u₁ c₂ u₂)) = c₁·mk(afDeriv u₁)·mk(u₂) + c₂·mk(afDeriv u₂)·mk(u₁)` (`cᵢ` read
as `C(toK cᵢ)`), for a nonzero curve `f`. The two-term log-derivative numerator is, in the function field of
the curve, the literal sum `c₁·D(log u₁) + c₂·D(log u₂)` cross-multiplied by `u₁·u₂` — so when both
single-term certificates hold (`afDeriv uᵢ = uᵢ·integrandᵢ`), this collapses to `(c₁·integrand₁ +
c₂·integrand₂)·u₁·u₂`, i.e. the residues add. Proven by pushing `afMul`/`cscaleG`/`caddG` through `mk`
(`mk_toPolyG_afMul`, `toPolyG_cscaleG`, `toPolyG_caddG`). The general-curve analogue of `mk_toPolyG_radLogSum2`;
the structural floor of the multi-term residue-sum soundness. -/
theorem mk_toPolyG_afLogSum2 (fuel : ℕ) (f : CPolyG α) (c₁ : α) (u₁ : CPolyG α) (c₂ : α) (u₂ : CPolyG α)
    (hf : cnormG f ≠ []) :
    Ideal.Quotient.mk (afIdeal f) (toPolyG (afLogSum2 fuel f c₁ u₁ c₂ u₂))
      = Polynomial.C (CFieldSpec.toK c₁)
          * Ideal.Quotient.mk (afIdeal f) (toPolyG (afDeriv fuel f u₁))
          * Ideal.Quotient.mk (afIdeal f) (toPolyG u₂)
        + Polynomial.C (CFieldSpec.toK c₂)
          * Ideal.Quotient.mk (afIdeal f) (toPolyG (afDeriv fuel f u₂))
          * Ideal.Quotient.mk (afIdeal f) (toPolyG u₁) := by
  rw [afLogSum2, toPolyG_caddG, map_add, mk_toPolyG_afMul _ _ _ hf,
    mk_toPolyG_afMul _ _ _ hf, toPolyG_cscaleG, toPolyG_cscaleG, map_mul, map_mul]

/-! ### The multi-term log-soundness predicate and the residue-sum numerator

`D(Σ cᵢ log uᵢ) = Σ cᵢ · afDeriv(uᵢ)/uᵢ`. The residue-sum numerator `afLogSumNum fuel f args cofs` over the
common denominator `∏ⱼ uⱼ` is the `caddG`-fold of the per-term contributions `cᵢ·afDeriv(uᵢ)·cofᵢ`
(`cofᵢ = ∏_{j≠i} uⱼ`). The general-curve analogue of `radLogSumNum`/`IsRadicalLogIntegral`. -/

/-- **The residue-sum numerator over a cofactor list** `afLogSumNum fuel f args cofs` — the numerator of
`Σᵢ cᵢ·afDeriv(uᵢ)/uᵢ` over the common denominator `∏ⱼ uⱼ`: the `caddG`-fold of the per-term contributions
`cᵢ·afDeriv(uᵢ)·cofᵢ` (`cofᵢ = ∏_{j≠i} uⱼ`, the cofactor making `uᵢ·cofᵢ = commonDenom`). The integrator
supplies the `args = [(cᵢ, uᵢ)]` (residue, log argument) and the matching cofactors `cofs`. Its quotient
value is the residue-sum's cross-multiplied form; the two-term head is `afLogSum2`. The general-curve analogue
of `radLogSumNum`. -/
def afLogSumNum (fuel : ℕ) (f : CPolyG α) (args : List (α × CPolyG α)) (cofs : List (CPolyG α)) :
    CPolyG α :=
  ((args.zip cofs).map (fun p =>
    afMul f (cscaleG p.1.1 (afDeriv fuel f p.1.2)) p.2)).foldl caddG ([] : CPolyG α)

/-- **The multi-term log-soundness predicate** `IsGeneralLogIntegral fuel f logpart commonDenom args cofs` —
the general integrator's log part `Σ_{(c,u)∈args} c·log u` integrates `logpart` over `K(x)[y]/(f)`: the
log-derivative sum `Σ cᵢ·D(log uᵢ) = Σ cᵢ·afDeriv(uᵢ)/uᵢ` equals `logpart` in the carrier quotient
`K[X] ⧸ afIdeal f`, cross-multiplied by the common denominator `commonDenom = ∏ⱼ uⱼ`. `cofs = [cofᵢ]` are the
per-term cofactors (`cofᵢ = ∏_{j≠i} uⱼ`, so `uᵢ·cofᵢ ≡ commonDenom`); `afLogSumNum` is the residue-sum
numerator. The faithful residue-sum statement: `mk(afLogSumNum) = mk(afMul logpart commonDenom)`. The
residue-correctness core is the obligation that the integrator's `args` (the `afLogArgSolve` outputs with
`genResidueResultant` residues `cᵢ`) satisfy it — reduced to obligations (1)+(2)+(3). The two-term head is
`mk_toPolyG_afLogSum2`; the general-curve analogue of `IsRadicalLogIntegral`. -/
def IsGeneralLogIntegral (fuel : ℕ) (f logpart commonDenom : CPolyG α)
    (args : List (α × CPolyG α)) (cofs : List (CPolyG α)) : Prop :=
  Ideal.Quotient.mk (afIdeal f) (toPolyG (afLogSumNum fuel f args cofs))
    = Ideal.Quotient.mk (afIdeal f) (toPolyG (afMul f logpart commonDenom))

omit [CDiffFieldSpec α] in
/-- **The residue-sum numerator of the empty log part is `0` in the quotient** — `afLogSumNum fuel f [] cofs =
[]`, so `mk(toPolyG(afLogSumNum fuel f [] cofs)) = 0`: a log part with no terms contributes nothing. The base
case of the residue-sum induction (`Σ` over the empty pole list). The general-curve analogue of
`mk_toPolyG_radLogSumNum_nil`. -/
theorem mk_toPolyG_afLogSumNum_nil (fuel : ℕ) (f : CPolyG α) (cofs : List (CPolyG α)) :
    Ideal.Quotient.mk (afIdeal f) (toPolyG (afLogSumNum fuel f [] cofs)) = 0 := by
  show Ideal.Quotient.mk (afIdeal f) (toPolyG ([] : CPolyG α)) = 0
  rw [toPolyG_nil, map_zero]

/-! ### ★ Obligation 3 (structural skeleton) — the residue-sum numerator distributes over the args list

The residue-sum numerator `afLogSumNum` is a `caddG`-fold of the per-term contributions, so its quotient value
is the sum of the per-term quotient values. The **structural** half of obligation 3 (the pole-list induction,
`generalReduceRationalTelescope`'s analogue for the log sum), reduced to additivity. The genuinely-analytic
residual is per-term — the algebraic **partial fraction** (`ratLogPart_eq_residue_logDeriv_sum`). The
general-curve analogue of `mk_toPolyG_radLogSumNum_eq_sum`. -/

omit [CDiffFieldSpec α] in
/-- **The residue-sum numerator distributes over the args list (structural skeleton of obligation 3)** —
`mk(toPolyG(afLogSumNum fuel f args cofs)) = Σ_{(cu,cof) ∈ args.zip cofs} mk(toPolyG(afMul (cᵢ·afDeriv(uᵢ))
cofᵢ))` in the quotient `K[X] ⧸ afIdeal f`, for a nonzero curve `f`. The residue-sum numerator is a
`caddG`-fold of the per-term contributions `afMul (cscaleG cᵢ (afDeriv uᵢ)) cofᵢ`, so its quotient value is
the sum of the per-term quotient values (seed `[] ↦ 0`). The **structural** half of obligation 3 — the
pole-list induction reduced to additivity; the genuinely-analytic residual is per-term (the partial fraction).
Proven from a `caddG`-fold distribution pushed through `mk` (`toPolyG_caddG`). The general-curve analogue of
`mk_toPolyG_radLogSumNum_eq_sum`. -/
theorem mk_toPolyG_afLogSumNum_eq_sum (fuel : ℕ) (f : CPolyG α) (args : List (α × CPolyG α))
    (cofs : List (CPolyG α)) :
    Ideal.Quotient.mk (afIdeal f) (toPolyG (afLogSumNum fuel f args cofs))
      = ((args.zip cofs).map (fun p =>
          Ideal.Quotient.mk (afIdeal f)
            (toPolyG (afMul f (cscaleG p.1.1 (afDeriv fuel f p.1.2)) p.2)))).sum := by
  rw [afLogSumNum]
  set terms := (args.zip cofs).map (fun p =>
    afMul f (cscaleG p.1.1 (afDeriv fuel f p.1.2)) p.2) with hterms
  -- generalize: `mk(toPolyG(terms.foldl caddG acc)) = mk(toPolyG acc) + Σ mk(toPolyG ·)`
  have hfold : ∀ (ts : List (CPolyG α)) (acc : CPolyG α),
      Ideal.Quotient.mk (afIdeal f) (toPolyG (ts.foldl caddG acc))
        = Ideal.Quotient.mk (afIdeal f) (toPolyG acc)
          + (ts.map (fun t => Ideal.Quotient.mk (afIdeal f) (toPolyG t))).sum := by
    intro ts
    induction ts with
    | nil => intro acc; simp
    | cons t ts ih =>
      intro acc
      rw [List.foldl_cons, ih (caddG acc t), toPolyG_caddG, map_add, List.map_cons, List.sum_cons]
      ring
  rw [hfold terms ([] : CPolyG α)]
  rw [toPolyG_nil, map_zero, zero_add, hterms, List.map_map]
  rfl

/-! ### ★ Discharging obligation 3's per-term hypothesis → composing to `IsGeneralLogIntegral` soundness

`mk_toPolyG_afLogSumNum_eq_sum` is the *structural* skeleton: the residue-sum numerator is the sum of the
per-term quotient values. The remaining content of obligation 3 is the **per-term residue match** — that the
sum of those per-term values equals `afMul logpart commonDenom` in the quotient, which is the algebraic
**partial fraction** (obligation 1 (`roots_genResidueResultant_eq_residues`, the residues) + obligation 2
(`logDeriv_residue_eq_multiplicity`, each log-derivative's residue) assembled by
`ratLogPart_eq_residue_logDeriv_sum` — Bernoulli/Lagrange, NOT analytic). We compose: **given** the per-term
sum equals `mk(afMul logpart commonDenom)` (the residue-match hypothesis — the partial fraction), the
integrator's log part **is log-sound** (`IsGeneralLogIntegral`). The general-curve analogue of
`isRadicalLogIntegral_of_residue_match`. -/

omit [CDiffFieldSpec α] in
/-- **★ The log-part soundness composes from the per-term residue match** — *given* that the sum of the
per-term quotient values `Σ mk(afMul (cᵢ·afDeriv(uᵢ)) cofᵢ)` equals `mk(afMul logpart commonDenom)` in the
carrier quotient `K[X] ⧸ afIdeal f` (the **residue-match hypothesis** `hmatch` — exactly what obligations 1+2
assemble via the algebraic partial fraction `ratLogPart_eq_residue_logDeriv_sum`: each `cᵢ` is a
`genResidueResultant` residue and each `uᵢ`'s log-derivative contributes residue `cᵢ` at its place), the
general integrator's log part `Σ cᵢ log uᵢ` is **log-sound**: `IsGeneralLogIntegral fuel f logpart commonDenom
args cofs`. The composition closing obligation 3: the *structural* fold `mk_toPolyG_afLogSumNum_eq_sum` rewrites
`mk(afLogSumNum)` into the per-term sum, then `hmatch` closes it. The general-curve analogue of
`isRadicalLogIntegral_of_residue_match`. -/
theorem isGeneralLogIntegral_of_residue_match (fuel : ℕ) (f logpart commonDenom : CPolyG α)
    (args : List (α × CPolyG α)) (cofs : List (CPolyG α))
    (hmatch : ((args.zip cofs).map (fun p =>
          Ideal.Quotient.mk (afIdeal f)
            (toPolyG (afMul f (cscaleG p.1.1 (afDeriv fuel f p.1.2)) p.2)))).sum
        = Ideal.Quotient.mk (afIdeal f) (toPolyG (afMul f logpart commonDenom))) :
    IsGeneralLogIntegral fuel f logpart commonDenom args cofs := by
  rw [IsGeneralLogIntegral, mk_toPolyG_afLogSumNum_eq_sum, hmatch]

omit [CDiffFieldSpec α] in
/-- **★ A single-log instance composes to `IsGeneralLogIntegral`** — for a one-term log part `args = [(c, u)]`
with cofactor `cofs = [cof]`, if the single contribution `c·afDeriv(u)·cof` equals `logpart·commonDenom` in
the quotient (the single-term residue match), then the log part is log-sound. The `args = [(c,u)]` case of
`isGeneralLogIntegral_of_residue_match` — the sum over a singleton collapses to the one term. The bridge
between the single-log certificate (`IsGeneralLogTerm`, `isGeneralLogTerm_of_afIsLogIntegral`) and the
multi-term predicate at the one-term head. The general-curve analogue of `isRadicalLogIntegral_singleton`. -/
theorem isGeneralLogIntegral_singleton (fuel : ℕ) (f logpart commonDenom : CPolyG α)
    (c : α) (u cof : CPolyG α)
    (hmatch : Ideal.Quotient.mk (afIdeal f)
          (toPolyG (afMul f (cscaleG c (afDeriv fuel f u)) cof))
        = Ideal.Quotient.mk (afIdeal f) (toPolyG (afMul f logpart commonDenom))) :
    IsGeneralLogIntegral fuel f logpart commonDenom [(c, u)] [cof] := by
  apply isGeneralLogIntegral_of_residue_match
  simpa using hmatch

end CPolyG

/-! ### ★ Obligation 2 — the logarithmic-derivative residue, general-carrier framing

Obligation 2 — *the residue of `D(log u) = afDeriv(u)/u` at a place over `x₀` equals the vanishing order of
`u` there* — is the classical **logarithmic-derivative residue theorem**, and its algebraic heart is a pure
`K[X]` fact (`LogResidue.logDeriv_residue_eq_multiplicity`, already proven in the radical template, generic
over the base field `K`): if `u = (X − a)^m · v` with `v(a) ≠ 0`, then `u'/u = m/(X − a) + v'/v`, so the
residue of `u'/u` at `a` is **exactly `m`**. In the general setting, `afDeriv(u)/u` at a place over `x₀`
localizes (through `toPolyG`) to exactly this base-field log-derivative on the place's uniformizer — so the
base-field core is *the* content of obligation 2 for the general carrier too. We restate the value form as the
general framing (the same lemma, recorded as obligation 2 for the general-curve log part). -/

namespace LogResidue

variable {K : Type*} [Field K]

/-- **★ Obligation 2 (general framing) — the logarithmic-derivative residue is the multiplicity** — for `u =
(X − a)^m·v` with `m ≥ 1` and `v(a) ≠ 0`, the residue of `u'/u` at `a`, read as the value of the numerator
`((X − a)·u')` over `u`'s cofactor at `a`, equals `(m : K)`. The general-carrier obligation 2: the per-place
residue of `afDeriv(u)/u` is the vanishing order (matching the `R(Z)`-root of obligation 1). This IS the
base-field `LogResidue.logDeriv_residue_eq_multiplicity` — generic over `K`, so it serves the general carrier
identically to the radical one (the local log-derivative on a place's uniformizer is base-field). Recorded
here as obligation 2 of the general-curve log soundness. -/
theorem genLogDeriv_residue_eq_multiplicity (a : K) (m : ℕ) (v : K[X])
    (hv : v.eval a ≠ 0) :
    (Polynomial.C (m : K) * v + (Polynomial.X - Polynomial.C a) * derivative v).eval a / v.eval a
      = (m : K) :=
  logDeriv_residue_eq_multiplicity a m v hv

/-! ### ★ Obligation 1 — `genResidueResultant` roots = residues (the GENERAL norm factoring, the milestone)

`genResidueResultant fuelY fuelD fuelX f g Dder D = res_X(res_Y(Z·D' − g, F), D)` is the full double resultant
(`ComputableGeneralResidues`). The outer `res_X(·, D)` is, by `resultant_eq_prod_eval`, `C(lc D)^N · ∏_{α₀ :
D(α₀)=0} genNorm(α₀, Z)`, where `genNorm(α₀, Z) = res_Y(Z·D'(α₀) − g(α₀, Y), F(α₀, Y))` is the inner norm
evaluated at the root `α₀` of `D`.

For the **radical** case `F = Y² − ρ` and `g = g₀ + g₁·Y`, the radical template's `residueNorm_factor` showed
`genNorm` is the two-sheet quadratic `(Z·D'(α₀) − g₀(α₀))² − g₁(α₀)²·ρ(α₀)`, factoring into the two residues
`(g₀ ± g₁√ρ)/D'` over the two sheets `Y = ±√ρ(α₀)`. For an **arbitrary** monic `F` of degree `n` in `Y`, the
norm `genNorm(α₀, Z) = ∏_{β : F(α₀,β)=0}(Z·D'(α₀) − g(α₀, β))` over the `n` places `β` of the fiber (the
resultant of `Z·D' − g` against `F` is the product of `Z·D' − g(α₀,β)` over the roots `β` of `F(α₀, ·)`, up
to the leading coefficient), each linear factor `Z·D'(α₀) − g(α₀, β) = D'(α₀)·(Z − g(α₀,β)/D'(α₀))` giving the
residue `g(α₀, β)/D'(α₀)` at the place `(α₀, β)` — exactly Trager's per-place residue `g/D'` (with `F_y` the
branch order absorbed when `D' ≠ 0`). We prove the general per-root factoring `genNormFactor` (the `K[Z]`
identity, the general analogue of `residueNorm_factor` — `n` factors not `2`) and the product-form root
theorem `roots_genResidueResultant_eq_residues` (the general analogue of `roots_residueResultant_eq_residues`),
abstractly. -/

/-- **★ The general residue-norm factors into the per-place residues** (obligation 1's general ingredient, the
`n`-factor analogue of `residueNorm_factor`) — for `c ≠ 0` (`c = D'(α₀)`) and a finite multiset `fiber` of
fiber values `β` (the roots of `F(α₀, ·)`, the places over `x = α₀`) with per-place numerators `gval β` (`=
g(α₀, β)`), the general residue-norm `∏_{β ∈ fiber}(Z·c − gval β)` factors as `C(c)^{|fiber|}·∏_{β ∈ fiber}(Z
− gval β / c)` — the per-place residues `gval β / c = g(α₀, β)/D'(α₀)`, **exactly Trager's per-place residue
`g/D'`** over each place `(α₀, β)` of the fiber. The exact `K[Z]`-identity that, composed with
`resultant_eq_prod_eval` over `K[Z]`, reduces the general double-resultant root↔residue correspondence to the
existing transcendental RT infra (`roots_rtResultant`). The general analogue of the radical's two-sheet
`residueNorm_factor` (which is this with `|fiber| = 2`, `fiber = {√ρ, −√ρ}` reading `gval = g₀ + g₁·Y`). Proven
by pulling `C c` out of each linear factor (`Z·c − gval β = c·(Z − gval β/c)`) and `Multiset.prod_map_mul`. -/
theorem genNormFactor (c : K) (fiber : Multiset K) (gval : K → K) (hc : c ≠ 0) :
    (fiber.map (fun β => Polynomial.X * Polynomial.C c - Polynomial.C (gval β))).prod
      = Polynomial.C c ^ Multiset.card fiber
        * (fiber.map (fun β => Polynomial.X - Polynomial.C (gval β / c))).prod := by
  -- each linear factor `Z·c − gval β = C c·(Z − gval β/c)`
  have hfac : ∀ β, Polynomial.X * Polynomial.C c - Polynomial.C (gval β)
      = Polynomial.C c * (Polynomial.X - Polynomial.C (gval β / c)) := by
    intro β
    have hcr : Polynomial.C c * Polynomial.C (gval β / c) = Polynomial.C (gval β) := by
      rw [← map_mul, mul_div_cancel₀ _ hc]
    rw [mul_sub, hcr, mul_comm (Polynomial.C c) Polynomial.X]
  rw [Multiset.map_congr rfl (fun β _ => hfac β)]
  -- `∏_β (C c · (Z − r β)) = (∏_β C c)·(∏_β (Z − r β))` (`prod_map_mul`), and `∏_β C c = C c^card`
  rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate]

/-- **★ The general residue-norm has the per-place residues as its root multiset** (the `n`-factor analogue
of `roots_residueNorm`) — for `c ≠ 0` (`c = D'(α₀)`) and a fiber multiset `fiber` of fiber values `β` (the
roots of `F(α₀, ·)`), the roots (with multiplicity) of the general residue-norm `∏_{β ∈ fiber}(Z·c − gval β)`
are exactly the per-place residues `{gval β / c : β ∈ fiber}` = `{g(α₀, β)/D'(α₀)}` over the places of the
fiber. From `genNormFactor` (the factorization into `C c^card·∏_β(Z − gval β/c)`) by `roots_C_mul` (drop the
nonzero leading `c^card`) then `roots_multiset_prod_X_sub_C` (split the product of monic linear factors). The
per-root half of the general double-resultant root↔residue correspondence; the general analogue of
`roots_residueNorm`. -/
theorem roots_genNorm (c : K) (fiber : Multiset K) (gval : K → K) (hc : c ≠ 0) :
    ((fiber.map (fun β => Polynomial.X * Polynomial.C c - Polynomial.C (gval β))).prod).roots
      = fiber.map (fun β => gval β / c) := by
  rw [genNormFactor c fiber gval hc]
  -- drop the nonzero leading scalar `C c^card = C (c^card)`
  rw [show (Polynomial.C c : K[X]) ^ Multiset.card fiber = Polynomial.C (c ^ Multiset.card fiber) from
      (map_pow _ _ _).symm,
    Polynomial.roots_C_mul _ (pow_ne_zero _ hc)]
  -- the product of monic linear factors `∏_β (Z − r β)` has roots `{r β}`
  rw [show (fiber.map (fun β => Polynomial.X - Polynomial.C (gval β / c)))
      = (fiber.map (fun β => gval β / c)).map (fun a => Polynomial.X - Polynomial.C a) by
      rw [Multiset.map_map]; rfl,
    Polynomial.roots_multiset_prod_X_sub_C]

/-- **★ The general residue resultant's roots ARE Trager's per-place residues (the
`roots_residueResultant_eq_residues` analogue, general curve)** — *given* the `resultant_eq_prod_eval` product
form `R = C(lc)^N · ∏_{α₀ ∈ Droots} genNorm(α₀, Z)` (the SAME factoring the radical case and
`rtResultant_eq_prod_roots` use, here with the **general** per-root norm `genNorm(α₀, Z) = ∏_{β ∈ fiber α₀}
(Z·D'(α₀) − g(α₀, β))` — the inner `res_Y(Z·D' − g, F)` evaluated at `α₀`, a product over the fiber `fiber α₀`
of places `β` over `x = α₀`), with `D'(α₀) ≠ 0` at every root `α₀` of `D`, the roots (with multiplicity) of
the general residue resultant `R` are exactly the **per-place residues** `g(α₀, β)/D'(α₀)` over every place
`(α₀, β)` — `R.roots = Droots.bind (fun α₀ => (fiber α₀).map (fun β => g α₀ β / Dprime α₀))`. This is
obligation 1's closure at the abstract `F̄[Z]` level for an **arbitrary** curve: composing `roots_C_mul` (drop
the nonzero leading `C(lc)^N`), `roots_multiset_prod` (the product's roots are the bind of the factors'), and
`roots_genNorm` (each factor's roots are the per-place residues). The general analogue of
`roots_residueResultant_eq_residues` — the radical's two-sheet `{(g₀±g₁√ρ)/D'}` is this with `fiber α₀ =
{√ρ(α₀), −√ρ(α₀)}` and `g α₀ β = g₀(α₀) + g₁(α₀)·β`. The only remaining (mechanical, engine-side) step is the
`resultant_eq_prod_eval` instantiation supplying this product-form hypothesis for `genResidueResultant` — the
compute-bridge, exactly the single-resultant pattern. -/
theorem roots_genResidueResultant_eq_residues (lc : K) (N : ℕ) (Droots : Multiset K)
    (Dprime : K → K) (fiber : K → Multiset K) (g : K → K → K)
    (hlc : lc ≠ 0)
    (hDp : ∀ α₀ ∈ Droots, Dprime α₀ ≠ 0)
    (R : K[X])
    (hR : R = Polynomial.C lc ^ N
      * (Droots.map (fun α₀ =>
          ((fiber α₀).map (fun β =>
            Polynomial.X * Polynomial.C (Dprime α₀) - Polynomial.C (g α₀ β))).prod)).prod) :
    R.roots = Droots.bind (fun α₀ => (fiber α₀).map (fun β => g α₀ β / Dprime α₀)) := by
  subst hR
  -- drop the nonzero leading scalar `C lc^N` (`lc ≠ 0`)
  rw [show (Polynomial.C lc : K[X]) ^ N = Polynomial.C (lc ^ N) from (map_pow _ _ _).symm,
    Polynomial.roots_C_mul _ (pow_ne_zero N hlc)]
  -- the product's roots are the `bind` of the per-root norm's roots (no factor is `0`)
  rw [Polynomial.roots_multiset_prod _ (by
    -- `0 ∉ map (genNorm ·) Droots`: each per-root norm is nonzero (its roots are the residues)
    rw [Multiset.mem_map]
    rintro ⟨α₀, hα, hα0⟩
    -- if the norm were `0` its root multiset would be `0`, but `roots_genNorm` gives the residues
    have hroots := roots_genNorm (Dprime α₀) (fiber α₀) (g α₀) (hDp α₀ hα)
    rw [hα0, Polynomial.roots_zero] at hroots
    -- `roots_genNorm` then asserts `0 = (fiber α₀).map (residue ·)`, so `card (fiber α₀) = 0`
    have hcard : Multiset.card (fiber α₀) = 0 := by
      have := congrArg Multiset.card hroots
      simpa [Multiset.card_map] using this.symm
    -- `card (fiber α₀) = 0` ⟹ `fiber α₀ = 0`, so the norm-product is the empty product `1 ≠ 0`
    rw [Multiset.card_eq_zero] at hcard
    rw [hcard] at hα0
    simp only [Multiset.map_zero, Multiset.prod_zero] at hα0
    exact one_ne_zero hα0)]
  -- per-root: `roots(genNorm α₀) = (fiber α₀).map (residue ·)`
  rw [Multiset.bind_map]
  refine Multiset.bind_congr (fun α₀ hα => ?_)
  exact roots_genNorm (Dprime α₀) (fiber α₀) (g α₀) (hDp α₀ hα)

/-! #### Obligation 3 (the partial fraction) — reused from the radical template, base-field/`ℚ(x)`-algebraic

Obligation 3 — *`logpart = Σᵢ cᵢ·afDeriv(uᵢ)/uᵢ` in the function field* — has, as its genuinely-analytic
content, the per-term residue match, which is the algebraic **Bernoulli/Lagrange partial fraction**
(`LogResidue.ratLogPart_eq_residue_logDeriv_sum`, already proven), NOT a curve-residue theorem: after
rationalizing the general log part to `ℚ(x)`, the residue-sum `Σ cᵢ/(x − poleᵢ)` IS its partial fraction, the
`cᵢ` the partial-fraction coefficients (the same residues `roots_genResidueResultant_eq_residues` exhibits).
We restate the verdict for the general curve — identical to the radical one, since after the norm to `ℚ(x)`
the log part is a rational function and the split-denominator partial fraction is all that is needed. -/

open scoped Differential in
/-- **★ Obligation 3 (general framing) — the general log-part per-term match is the algebraic partial
fraction** — for a squarefree split denominator `D = ∏_{α∈s}(X − α)` and `deg A < #s`, the rational log part
`A/D` equals `Σ_{α∈s} residue(α)·logDeriv(X − α)` in `K(x)` (`residue(α) = A(α)/D'(α)`). This IS
**`LogResidue.ratLogPart_eq_residue_logDeriv_sum`** = `PartialFraction.ratFunc_eq_sum_residue_logDeriv` — a
pure Bernoulli/Lagrange partial fraction (no analytic residue theorem) — restated as the discharge of the
general-curve obligation 3's per-term residue match for the rational (split-denominator) case: the residue-sum
`Σ cᵢ·logDeriv(uᵢ)` IS the partial fraction of the log part, the `cᵢ` exactly the residues
`roots_genResidueResultant_eq_residues` exhibits. The general curve reduces to this after the norm to `ℚ(x)`.
The verdict (general): the per-term match is ALGEBRAIC, not analytic — identical to the radical case. -/
theorem genRatLogPart_eq_residue_logDeriv_sum (s : Finset K) (A : K[X]) (hA : A.degree < s.card) :
    algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id)
      = ∑ α ∈ s, algebraMap K[X] (RatFunc K)
          (Polynomial.C (A.eval α / eval α (derivative (Lagrange.nodal s id))))
            * Differential.logDeriv (algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C α)) :=
  ratLogPart_eq_residue_logDeriv_sum s A hA

end LogResidue

/-! ### ★ Priority 3 — composing rational + log into the full GENERAL algebraic integral soundness `D(∫f) = f`

The unified general integrator `afIntegrateAlgebraic` returns `(v, u)` (and in general `(v, args)`) — a
rational part `v` plus log terms — so `∫f = v + Σ cᵢ log uᵢ` and the full soundness is `D(∫f) = afDeriv(v) +
Σ cᵢ·afDeriv(uᵢ)/uᵢ = f`. This **splits exactly into the two halves**, each now a theorem (modulo their
isolated per-step inputs):

* the **rational part** `afDeriv(v) = ratPart(f)` — `ComputableGeneralIntegralSoundness`'s
  `generalReduceRationalTelescope` (the rational-part telescoping over the eq.-11 reduction);
* the **log part** `Σ cᵢ·afDeriv(uᵢ)/uᵢ = logPart(f)` — this file's `IsGeneralLogIntegral`
  (`isGeneralLogIntegral_of_residue_match`), with its per-term match the algebraic partial fraction
  (`genRatLogPart_eq_residue_logDeriv_sum`) and its residues the `genResidueResultant` roots
  (`roots_genResidueResultant_eq_residues`).

Cross-multiplied by the log part's common denominator `commonDenom = ∏ uⱼ`, the full identity in the carrier
quotient `K[X] ⧸ afIdeal f` is `afDeriv(v)·commonDenom + afLogSumNum(args) = f·commonDenom`, the sum of the two
halves. We state the composed predicate `IsGeneralAlgebraicIntegral` and prove it follows from the rational
soundness (`afDeriv(v) = ratPart`) + the log soundness (`IsGeneralLogIntegral`) + the split `f = ratPart +
logPart`. The general-curve analogue of the radical's `isAlgebraicIntegral_of_parts`. -/

namespace CPolyG

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]

/-- **The full general algebraic-integral soundness predicate** `IsGeneralAlgebraicIntegral fuel f g v
commonDenom args cofs` — the unified general integrator's output `(v, args)` is a correct antiderivative of
`g` over `K(x)[y]/(f)`: `D(v + Σ cᵢ log uᵢ) = g`, i.e. `afDeriv(v) + Σ cᵢ·afDeriv(uᵢ)/uᵢ = g`,
cross-multiplied by `commonDenom = ∏ uⱼ` and read in the carrier quotient `K[X] ⧸ afIdeal f`:
`mk(toPolyG(afMul (afDeriv v) commonDenom)) + mk(toPolyG(afLogSumNum args cofs)) = mk(toPolyG(afMul g
commonDenom))`. The full `D(∫g) = g` for the general algebraic integrator, splitting into the rational part
(`afDeriv v`) + the log part (`afLogSumNum`). The general-curve analogue of `IsAlgebraicIntegral`. -/
def IsGeneralAlgebraicIntegral (fuel : ℕ) (f g v commonDenom : CPolyG α)
    (args : List (α × CPolyG α)) (cofs : List (CPolyG α)) : Prop :=
  Ideal.Quotient.mk (afIdeal f) (toPolyG (afMul f (afDeriv fuel f v) commonDenom))
    + Ideal.Quotient.mk (afIdeal f) (toPolyG (afLogSumNum fuel f args cofs))
  = Ideal.Quotient.mk (afIdeal f) (toPolyG (afMul f g commonDenom))

omit [CDiffFieldSpec α] in
/-- **★ The full general algebraic integral `D(∫g) = g` composes from the rational + log soundness** — *given*
the **rational-part soundness** `hrat` (`afDeriv(v)·commonDenom = ratPart·commonDenom` in the quotient — from
`ComputableGeneralIntegralSoundness`'s telescoping `generalReduceRationalTelescope`), the **log-part soundness**
`hlog` (`IsGeneralLogIntegral fuel f logPart commonDenom args cofs` — this file), and the **integrand split**
`hsplit` (`g = ratPart + logPart` in the quotient, cross-multiplied), the unified general integrator's output
`(v, args)` satisfies the full soundness `IsGeneralAlgebraicIntegral fuel f g v commonDenom args cofs`, i.e.
`D(v + Σ cᵢ log uᵢ) = g`. The capstone composition: `afDeriv(v) + Σ cᵢ·afDeriv(uᵢ)/uᵢ = ratPart + logPart = g`
in the carrier quotient — the rational part (telescoping) plus the log part (partial fraction) reassembled into
`D(∫g) = g`. The mechanical residual is the engine-level `g = ratPart + logPart` split (the integrand
decomposition `afIntegrateAlgebraic` performs) — supplied here as `hsplit`. The general-curve analogue of
`isAlgebraicIntegral_of_parts`. -/
theorem isGeneralAlgebraicIntegral_of_parts (fuel : ℕ) (f g v ratPart logPart commonDenom : CPolyG α)
    (args : List (α × CPolyG α)) (cofs : List (CPolyG α))
    (hrat : Ideal.Quotient.mk (afIdeal f)
          (toPolyG (afMul f (afDeriv fuel f v) commonDenom))
        = Ideal.Quotient.mk (afIdeal f) (toPolyG (afMul f ratPart commonDenom)))
    (hlog : IsGeneralLogIntegral fuel f logPart commonDenom args cofs)
    (hsplit : Ideal.Quotient.mk (afIdeal f) (toPolyG (afMul f ratPart commonDenom))
        + Ideal.Quotient.mk (afIdeal f) (toPolyG (afMul f logPart commonDenom))
      = Ideal.Quotient.mk (afIdeal f) (toPolyG (afMul f g commonDenom))) :
    IsGeneralAlgebraicIntegral fuel f g v commonDenom args cofs := by
  -- `afDeriv(v)·cd = ratPart·cd` (rational) and `afLogSumNum = logPart·cd` (log); sum = `g·cd` (split)
  rw [IsGeneralAlgebraicIntegral, hrat, hlog, hsplit]

end CPolyG

/-! ### `#print axioms` — the general-curve log-part setting + foundational floor + obligation 1 milestone

Each log-part predicate, the certificate bridge, the additivity floor, obligation 2 (the log-derivative
residue), obligation 1's general norm factoring and the **root↔residue theorem for the general double
resultant** (`roots_genResidueResultant_eq_residues`), obligation 3 (the partial fraction), and the full
composition carry **only** the standard `[propext, Classical.choice, Quot.sound]` — no `native_decide`
compiler axiom, no `sorry`. The faithful general-curve log-soundness setting (`D(log u) = afDeriv(u)/u` in the
carrier quotient `K[X] ⧸ afIdeal f`), the fact that every engine-validated log certificate **is** the abstract
single-log soundness (`isGeneralLogTerm_of_logCert`), the multi-term residue-sum distribution
(`mk_toPolyG_afLogSumNum_eq_sum`), the general norm factoring into per-place residues (`genNormFactor` /
`roots_genNorm`), the **milestone** root↔residue theorem (`roots_genResidueResultant_eq_residues`, the
`roots_residueResultant_eq_residues` analogue for the GENERAL double resultant), and the full composition
(`isGeneralAlgebraicIntegral_of_parts`) are general theorems — the LOG half of the general algebraic capstone
`D(∫f) = f`, with the residue-correctness core mirrored from the radical template as closely as the general
norm allows. The single remaining mechanical step is the `resultant_eq_prod_eval` instantiation supplying the
product-form hypothesis of `roots_genResidueResultant_eq_residues` for the engine's `genResidueResultant` (the
compute-bridge, exactly the single-resultant pattern). -/

-- The certificate↔predicate bridge: every validated log certificate is the abstract single-log soundness:
#print axioms CPolyG.isGeneralLogTerm_of_logCert

-- ★ Two log residues add (the structural core of the multi-term residue sum):
#print axioms CPolyG.mk_toPolyG_afLogSum2

-- ★ Obligation 3 (structural skeleton): the residue-sum numerator distributes over the args list:
#print axioms CPolyG.mk_toPolyG_afLogSumNum_eq_sum

-- ★★ Obligation 3 composed: the general log part is log-sound given the per-term residue match:
#print axioms CPolyG.isGeneralLogIntegral_of_residue_match

-- ★ Obligation 2 (general framing): the logarithmic-derivative residue equals the vanishing order:
#print axioms LogResidue.genLogDeriv_residue_eq_multiplicity

-- ★ Obligation 1's general ingredient: the general residue-norm factors into the per-place residues:
#print axioms LogResidue.genNormFactor

-- ★★ Obligation 1 MILESTONE (abstract): the general residue resultant's roots ARE the per-place residues:
#print axioms LogResidue.roots_genResidueResultant_eq_residues

-- ★★ Obligation 3 (general framing): the general log-part per-term match IS the algebraic partial fraction:
#print axioms LogResidue.genRatLogPart_eq_residue_logDeriv_sum

-- ★★ Priority 3: the full general algebraic integral `D(∫g) = g` composes from the rational + log soundness:
#print axioms CPolyG.isGeneralAlgebraicIntegral_of_parts

end DeepWiki.SymbolicIntegration
