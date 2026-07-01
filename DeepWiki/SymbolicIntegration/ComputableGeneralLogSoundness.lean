import DeepWiki.SymbolicIntegration.ComputableGeneralWellFounded
import DeepWiki.SymbolicIntegration.ComputableGeneralResidues
import DeepWiki.SymbolicIntegration.ComputableRadicalLogSoundness

/-! # The LOG-part soundness for the GENERAL-curve integrator: `D(Σ cᵢ log uᵢ) = logpart` via `afDerivWf`

`ComputableGeneralIntegralSoundness` proves the **rational** half of the general algebraic soundness capstone
`D(∫f) = f` for an arbitrary curve `K(x)[y]/(f)` — the rational-part telescoping
`generalReduceRationalTelescopeWf` through the fuel-free general derivation `afDerivWf`
(`mk_toPolyG_afDerivWf`). This file opens the **logarithmic** half: the general integrator
(`afLogArgSolveWf`, `afIntegrateAlgebraicWf`) returns `∫f = v + Σ cᵢ log uᵢ`, and the log part is sound when the log-argument
outputs carry the right residues, i.e. when

  **`Σ cᵢ · afDerivWf(uᵢ)/uᵢ = (the log part of f)`**.

It is the general-curve analogue of the radical-log template `ComputableRadicalLogSoundness` — the SAME
`predicate → certificate-bridge → residue-correctness core` shape, with the diagonal `radDeriv n ρ` /
`radMul n ρ` / `radIdeal n ρ` replaced by the general `afDerivWf f` / `afMul f` / `afIdeal f`, and the
hyperelliptic two-sheet norm replaced by the general double resultant `genResidueResultant`
(`ComputableGeneralResidues`).

**The log-derivative is `afDerivWf(u)/u`.** For a carrier element `u ∈ K(x)[y]/(f)`, `D(log u) = afDerivWf(u)/u`
*by definition* of the logarithmic derivative. So the log-part soundness is a **statement about residues**,
not a new derivation law: it asks that the integrator's chosen `uᵢ` have log-derivatives summing to the
integrand's log part. The single-term certificate is the fuel-free round-trip form
`cisZeroG (csubG (afDerivWf f u) (afMul f u integrand)) = true`, the *division-free* form
`afDerivWf f u = afMul f u integrand` (since `D(log u)·u = afDerivWf u`).

**The faithful setting: the carrier quotient** `K[X] ⧸ afIdeal f = K[X] ⧸ (toPolyG f)` — the coordinate ring
of the curve `f(x, y) = 0` over `K = CFieldSpec.K α`. The engine's `afMul` is the quotient product (Euclidean
reduction `mod f`), so the honest reading of `afDerivWf f u = afMul f u integrand` lives in this quotient
(exactly as the Wf derivation invariant's Leibniz law `mk_toPolyG_afDerivWf_afMul` does). The single-term
log-derivative equation `D(log u) = integrand` is therefore `mk(toPolyG(afDerivWf f u)) = mk(toPolyG u)·
mk(toPolyG integrand)` in `K[X] ⧸ afIdeal f`.

What this file delivers (axiom-clean `[propext, Classical.choice, Quot.sound]`, **no** `native_decide`):

* **`IsGeneralLogTermWf f u integrand`** — the *single*-log soundness predicate (`cᵢ = 1`): the quotient
  identity `mk(toPolyG(afDerivWf f u)) = mk(toPolyG u)·mk(toPolyG integrand)`, the faithful "`D(log u) =
  integrand`". `IsGeneralLogIntegralWf f logpart commonDenom args cofs` — the multi-term predicate: the
  **log-derivative sum** `Σ_{(c,u)∈args} c · afDerivWf(u)/u` equals `logpart` in the quotient, cross-multiplied
  by the common denominator. (Both read `afDerivWf(u)/u` as the cross-multiplied quotient equation, no division.)

* **The certificate↔predicate bridge** `isGeneralLogTermWf_of_logCert` — the engine's boolean check
  `cisZeroG (csubG (afDerivWf f u) (afMul f u integrand)) = true` **implies**
  `IsGeneralLogTermWf f u integrand` (the quotient
  identity), via `cisZeroG_iff` + `toPolyG_csubG` + `mk_toPolyG_afMul`. So every `native_decide`-validated
  `afIsLogIntegral` (the non-hyperelliptic `y³ − x² − 1` log arguments `u ∝ y`, `u ∝ y² + x`; the arcsinh
  conservativity) IS, abstractly, the single-log soundness — read in the genuine quotient field.

* **Additivity of the log-derivative sum** — `mk_toPolyG_afLogSumNumWf_eq_sum`: `D(Σ cᵢ log uᵢ)`, read as the
  numerator `Σ cᵢ·afDerivWf(uᵢ)·cofᵢ` over the common denominator, distributes over the `args` list.

**Obligation 2 (the tractable core)** is the base-field logarithmic-derivative residue theorem
`LogResidue.logDeriv_residue_eq_multiplicity` (already proven, generic over the base field, in the radical
template): the residue of `afDerivWf(u)/u` at a place over `x₀` equals the vanishing order. In the general
setting `afDerivWf(u)/u` localizes (through `toPolyG`) to exactly this base-field log-derivative on the place's
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

**Composed:** `isGeneralLogIntegralWf_of_residue_match` — given the per-term residue match (the partial
fraction), the general integrator's log part is log-sound; `isGeneralAlgebraicIntegralWf_of_parts` composes the
general rational part (`generalReduceRationalTelescopeWf`, the other half) + this log part into the full general
`D(∫f) = f`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open scoped Differential

namespace CPolyG

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]

/-! ### The fuel-free log-soundness predicate and residue-sum skeleton

The Wf derivation has the expected quotient API, so the log-part predicates can be restated without
threading a fuel parameter. The partial-fraction obligations keep the same shape; only each
`afDerivWf f uᵢ` leaf. -/

/-- The fuel-free single-log soundness predicate. -/
def IsGeneralLogTermWf (f u integrand : CPolyG α) : Prop :=
  Ideal.Quotient.mk (afIdeal f) (toPolyG (afDerivWf f u))
    = Ideal.Quotient.mk (afIdeal f) (toPolyG u)
      * Ideal.Quotient.mk (afIdeal f) (toPolyG integrand)

omit [CDiffFieldSpec α] in
/-- The Wf engine log-derivative certificate as a `K[X]` equality. -/
theorem toPolyG_afDerivWf_eq_of_logCert (f u integrand : CPolyG α)
    (h : cisZeroG (csubG (afDerivWf f u) (afMul f u integrand)) = true) :
    toPolyG (afDerivWf f u) = toPolyG (afMul f u integrand) := by
  rw [cisZeroG_iff, toPolyG_csubG, sub_eq_zero] at h
  exact h

omit [CDiffFieldSpec α] in
/-- A Wf log-derivative certificate implies the fuel-free single-log predicate. -/
theorem isGeneralLogTermWf_of_logCert (f u integrand : CPolyG α) (hf : cnormG f ≠ [])
    (h : cisZeroG (csubG (afDerivWf f u) (afMul f u integrand)) = true) :
    IsGeneralLogTermWf f u integrand := by
  rw [IsGeneralLogTermWf, toPolyG_afDerivWf_eq_of_logCert f u integrand h,
    mk_toPolyG_afMul f u integrand hf]

/-- The fuel-free two-term log-derivative numerator. -/
def afLogSum2Wf (f : CPolyG α) (c₁ : α) (u₁ : CPolyG α) (c₂ : α) (u₂ : CPolyG α) :
    CPolyG α :=
  caddG (afMul f (cscaleG c₁ (afDerivWf f u₁)) u₂)
    (afMul f (cscaleG c₂ (afDerivWf f u₂)) u₁)

omit [CDiffFieldSpec α] in
/-- Two Wf log residues add in quotient form. -/
theorem mk_toPolyG_afLogSum2Wf (f : CPolyG α) (c₁ : α) (u₁ : CPolyG α) (c₂ : α)
    (u₂ : CPolyG α) (hf : cnormG f ≠ []) :
    Ideal.Quotient.mk (afIdeal f) (toPolyG (afLogSum2Wf f c₁ u₁ c₂ u₂))
      = Polynomial.C (CFieldSpec.toK c₁)
          * Ideal.Quotient.mk (afIdeal f) (toPolyG (afDerivWf f u₁))
          * Ideal.Quotient.mk (afIdeal f) (toPolyG u₂)
        + Polynomial.C (CFieldSpec.toK c₂)
          * Ideal.Quotient.mk (afIdeal f) (toPolyG (afDerivWf f u₂))
          * Ideal.Quotient.mk (afIdeal f) (toPolyG u₁) := by
  rw [afLogSum2Wf, toPolyG_caddG, map_add, mk_toPolyG_afMul _ _ _ hf,
    mk_toPolyG_afMul _ _ _ hf, toPolyG_cscaleG, toPolyG_cscaleG, map_mul, map_mul]

/-- The fuel-free residue-sum numerator over a cofactor list. -/
def afLogSumNumWf (f : CPolyG α) (args : List (α × CPolyG α)) (cofs : List (CPolyG α)) :
    CPolyG α :=
  ((args.zip cofs).map (fun p =>
    afMul f (cscaleG p.1.1 (afDerivWf f p.1.2)) p.2)).foldl caddG ([] : CPolyG α)

/-- The fuel-free multi-term log-soundness predicate. -/
def IsGeneralLogIntegralWf (f logpart commonDenom : CPolyG α)
    (args : List (α × CPolyG α)) (cofs : List (CPolyG α)) : Prop :=
  Ideal.Quotient.mk (afIdeal f) (toPolyG (afLogSumNumWf f args cofs))
    = Ideal.Quotient.mk (afIdeal f) (toPolyG (afMul f logpart commonDenom))

omit [CDiffFieldSpec α] in
/-- The fuel-free residue-sum numerator of the empty log part is zero in the quotient. -/
theorem mk_toPolyG_afLogSumNumWf_nil (f : CPolyG α) (cofs : List (CPolyG α)) :
    Ideal.Quotient.mk (afIdeal f) (toPolyG (afLogSumNumWf f [] cofs)) = 0 := by
  show Ideal.Quotient.mk (afIdeal f) (toPolyG ([] : CPolyG α)) = 0
  rw [toPolyG_nil, map_zero]

omit [CDiffFieldSpec α] in
/-- The Wf residue-sum numerator distributes over the args list. -/
theorem mk_toPolyG_afLogSumNumWf_eq_sum (f : CPolyG α) (args : List (α × CPolyG α))
    (cofs : List (CPolyG α)) :
    Ideal.Quotient.mk (afIdeal f) (toPolyG (afLogSumNumWf f args cofs))
      = ((args.zip cofs).map (fun p =>
          Ideal.Quotient.mk (afIdeal f)
            (toPolyG (afMul f (cscaleG p.1.1 (afDerivWf f p.1.2)) p.2)))).sum := by
  rw [afLogSumNumWf]
  set terms := (args.zip cofs).map (fun p =>
    afMul f (cscaleG p.1.1 (afDerivWf f p.1.2)) p.2) with hterms
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

omit [CDiffFieldSpec α] in
/-- The fuel-free log part composes from the per-term residue match. -/
theorem isGeneralLogIntegralWf_of_residue_match (f logpart commonDenom : CPolyG α)
    (args : List (α × CPolyG α)) (cofs : List (CPolyG α))
    (hmatch : ((args.zip cofs).map (fun p =>
          Ideal.Quotient.mk (afIdeal f)
            (toPolyG (afMul f (cscaleG p.1.1 (afDerivWf f p.1.2)) p.2)))).sum
        = Ideal.Quotient.mk (afIdeal f) (toPolyG (afMul f logpart commonDenom))) :
    IsGeneralLogIntegralWf f logpart commonDenom args cofs := by
  rw [IsGeneralLogIntegralWf, mk_toPolyG_afLogSumNumWf_eq_sum, hmatch]

omit [CDiffFieldSpec α] in
/-- A one-term Wf log part composes to `IsGeneralLogIntegralWf`. -/
theorem isGeneralLogIntegralWf_singleton (f logpart commonDenom : CPolyG α)
    (c : α) (u cof : CPolyG α)
    (hmatch : Ideal.Quotient.mk (afIdeal f)
          (toPolyG (afMul f (cscaleG c (afDerivWf f u)) cof))
        = Ideal.Quotient.mk (afIdeal f) (toPolyG (afMul f logpart commonDenom))) :
    IsGeneralLogIntegralWf f logpart commonDenom [(c, u)] [cof] := by
  apply isGeneralLogIntegralWf_of_residue_match
  simpa using hmatch

end CPolyG

/-! ### ★ Obligation 2 — the logarithmic-derivative residue, general-carrier framing

Obligation 2 — *the residue of `D(log u) = afDerivWf(u)/u` at a place over `x₀` equals the vanishing order of
`u` there* — is the classical **logarithmic-derivative residue theorem**, and its algebraic heart is a pure
`K[X]` fact (`LogResidue.logDeriv_residue_eq_multiplicity`, already proven in the radical template, generic
over the base field `K`): if `u = (X − a)^m · v` with `v(a) ≠ 0`, then `u'/u = m/(X − a) + v'/v`, so the
residue of `u'/u` at `a` is **exactly `m`**. In the general setting, `afDerivWf(u)/u` at a place over `x₀`
localizes (through `toPolyG`) to exactly this base-field log-derivative on the place's uniformizer — so the
base-field core is *the* content of obligation 2 for the general carrier too. We restate the value form as the
general framing (the same lemma, recorded as obligation 2 for the general-curve log part). -/

namespace LogResidue

variable {K : Type*} [Field K]

/-- **★ Obligation 2 (general framing) — the logarithmic-derivative residue is the multiplicity** — for `u =
(X − a)^m·v` with `m ≥ 1` and `v(a) ≠ 0`, the residue of `u'/u` at `a`, read as the value of the numerator
`((X − a)·u')` over `u`'s cofactor at `a`, equals `(m : K)`. The general-carrier obligation 2: the per-place
residue of `afDerivWf(u)/u` is the vanishing order (matching the `R(Z)`-root of obligation 1). This IS the
base-field `LogResidue.logDeriv_residue_eq_multiplicity` — generic over `K`, so it serves the general carrier
identically to the radical one (the local log-derivative on a place's uniformizer is base-field). Recorded
here as obligation 2 of the general-curve log soundness. -/
theorem genLogDeriv_residue_eq_multiplicity (a : K) (m : ℕ) (v : K[X])
    (hv : v.eval a ≠ 0) :
    (Polynomial.C (m : K) * v + (Polynomial.X - Polynomial.C a) * derivative v).eval a / v.eval a
      = (m : K) :=
  logDeriv_residue_eq_multiplicity a m v hv

/-! ### ★ Obligation 1 — `genResidueResultant` roots = residues (the GENERAL norm factoring, the milestone)

`genResidueResultant fuelY fuelX f g Dder D = res_X(res_Y(Z·D' − g, F), D)` is the full double resultant
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

Obligation 3 — *`logpart = Σᵢ cᵢ·afDerivWf(uᵢ)/uᵢ` in the function field* — has, as its genuinely-analytic
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

/-! ### ★ The compute-bridge — `genResidueResultant`'s interpolation-uniqueness characterization (engine link)

`roots_genResidueResultant_eq_residues` works on the *abstract* product form `R = C(lc)^N·∏_{α₀} genNorm(α₀, Z)`.
To discharge its hypothesis `hR` for the ENGINE's `genResidueResultant fuelY fuelX f g Dder D` (which
interpolates over the `Z`-nodes `k = 0, …, n·deg_X D`, `n = deg_y f`), the bridge is the **interpolation-
uniqueness** characterization — the EXACT analogue of the radical's `toPolyG_cAlgResidueResultant_eq_of_eval`:
the engine's `genResidueResultant` is THE unique polynomial of degree `< n·deg_X D + 2` agreeing at each node
`Z = (k : ℚ)` with the abstract product form. The outer carrier is `ℚ` (`CFieldSpec.K ℚ = ℚ`, `toK = id`), so
node distinctness is `Nat.cast` injectivity into `ℚ` (char 0) and the assembly is `eval_toPolyG_cinterpolateG`
+ `degree_toPolyG_cinterpolateG_lt` + `Polynomial.eq_of_degrees_lt_of_eval_index_eq`, with the general
`n·deg_X D + 1` node count (vs the radical's doubled `2·deg D + 1`). Composed with
`roots_genResidueResultant_eq_residues`, this connects the abstract roots↔residues theorem to the engine's
`genResidueResultant` — the compute-bridge CLOSED, axiom-clean. -/

namespace CPolyG

/-- **★ The compute-bridge — the interpolation-uniqueness characterization of `genResidueResultant`** — let
`R : ℚ[X]` have `degree < cdegG f * cdegG D + 2` (the general `n·deg_X D + 1` node count, `n = deg_y f`), and
suppose at each node `k ∈ {0, …, cdegG f · cdegG D + 1}` its value is the engine's per-node outer resultant
`R.eval (k : ℚ) = cresultantG fuelX (resYAtNode fuelY f g Dder (k : ℚ)) D` (the inner `res_Y` against
`F` then outer `res_X` against `D`, the values `genResidueResultant` interpolates). Then `toPolyG
(genResidueResultant fuelY fuelX f g Dder D) = R`. The compute-bridge CLOSED: the engine's general
residue resultant is the unique degree-`< n·deg_X D + 2` polynomial with those node values — the EXACT
`toPolyG_cAlgResidueResultant_eq_of_eval` Lagrange-uniqueness, ported to the general double resultant
(`genResidueResultant`) over the concrete `ℚ` outer carrier. The node abscissae `(k : ℚ)` are distinct by
`Nat.cast` injectivity into `ℚ` (char 0), so no separate `InjOn` hypothesis is needed (unlike the radical's
generic-`α` `cnatCastG` version). Composed with `roots_genResidueResultant_eq_residues` (whose hypothesis `hR`
is the `resultant_eq_prod_eval` product form), this discharges `hR` for the engine's `genResidueResultant` —
connecting the abstract roots↔residues milestone to the actual engine. -/
theorem toPolyG_genResidueResultant_eq_of_eval (fuelY fuelX : ℕ)
    (f g : CPolyG (QFunNZG ℚ)) (Dder : QFunNZG ℚ) (D : CPolyG ℚ)
    (R : ℚ[X])
    (hRdeg : R.degree < (cdegG f * cdegG D + 2 : ℕ))
    (hnode : ∀ k ∈ Finset.range (cdegG f * cdegG D + 1 + 1),
      R.eval ((k : ℚ))
        = cresultantG fuelX (resYAtNode fuelY f g Dder ((k : ℚ))) D) :
    toPolyG (genResidueResultant fuelY fuelX f g Dder D) = R := by
  classical
  -- Lean elaborates the engine's `(range n).map (fun k:ℕ => ((k:ℚ), …))` by lifting the tuple coercion to a
  -- DOUBLE map `((range n).map Nat.cast).map (fun z:ℚ => (z, …))`. We pin `pts` in exactly that doubly-mapped
  -- form (so `hpts` is `rfl` against the engine), and the list-shape lemmas compose over the two `List.map`s.
  -- `zs` = the `ℚ`-node abscissae. Build it via `List.range'` reused through `cnatCastG`-free `map`; pin it
  -- with `List.Nodup`/`length`/`mem` facts proven by the dedicated `range_map` lemmas (the coercion makes the
  -- literal `(range).map (↑·)` re-display as a `flatMap`/`do`-block, so we keep the facts, not the syntax).
  -- `zs` = the `ℚ`-node abscissae, kept as the EXPLICIT cast-map of `range` (`List.map_coe_range`) so the
  -- coercion does not re-lift into a `flatMap`. Facts proven by the `range`/`map` lemmas via `simp`.
  set zs : List ℚ := (List.range (cdegG f * cdegG D + 1 + 1)).map (Nat.cast) with hzs
  have hzs_len : zs.length = cdegG f * cdegG D + 1 + 1 := by
    rw [hzs, List.length_map, List.length_range]
  have hzs_nodup : zs.Nodup :=
    hzs ▸ List.Nodup.map (fun a b hab => Nat.cast_injective hab) List.nodup_range
  have hzs_mem : ∀ k, k ∈ List.range (cdegG f * cdegG D + 1 + 1) → ((k : ℚ)) ∈ zs := by
    intro k hk; rw [hzs, List.mem_map]; exact ⟨k, hk, rfl⟩
  set pts : List (ℚ × ℚ) :=
    zs.map (fun z => (z, cresultantG fuelX (resYAtNode fuelY f g Dder z) D))
    with hpts
  -- bridge the engine's node list to `pts` STRUCTURALLY (no resultant evaluation): the engine's
  -- `(range).map (fun k:ℕ => let z:=↑k; (z, …))` and `pts = ((range).map ↑).map (fun z:ℚ => (z, …))` are the
  -- SAME up to `flatMap_pure_eq_map` (the lifted coercion) + `map_map`.
  have hcompute : genResidueResultant fuelY fuelX f g Dder D = cinterpolateG pts := by
    rw [genResidueResultant, hpts, hzs]
    congr 1
    rw [List.map_map]
    -- the engine's inner `do let a ← range; pure ↑a` IS `range.map Nat.cast` (`flatMap_pure_eq_map`),
    -- then `map_map` collapses both sides to `range.map ((z,…) ∘ ↑)`
    rw [show (do let a ← List.range (cdegG f * cdegG D + 1 + 1); pure (↑a : ℚ))
        = (List.range (cdegG f * cdegG D + 1 + 1)).map (Nat.cast) from
      List.flatMap_pure_eq_map _ _, List.map_map]
  have htoK : ∀ q : ℚ, CFieldSpec.toK q = q := fun _ => rfl
  -- node-abscissa images = `zs`; reusable membership/length/nodup facts over the double map
  have hmempts : ∀ z, z ∈ zs →
      (z, cresultantG fuelX (resYAtNode fuelY f g Dder z) D) ∈ pts := by
    intro z hz; rw [hpts, List.mem_map]; exact ⟨z, hz, rfl⟩
  have hfst : pts.map (fun p => CFieldSpec.toK p.1) = zs := by
    rw [hpts, List.map_map]
    simp only [htoK]
    rw [show (fun p : ℚ × ℚ => p.1) ∘ (fun z => (z, cresultantG fuelX
        (resYAtNode fuelY f g Dder z) D)) = id from rfl, List.map_id]
  have hnodup : (pts.map (fun p => CFieldSpec.toK p.1)).Nodup := by rw [hfst]; exact hzs_nodup
  have hne : pts ≠ [] := by
    rw [hpts, Ne, List.map_eq_nil_iff]
    intro hzsnil; rw [hzsnil] at hzs_len; simp at hzs_len
  have hlen : pts.length = cdegG f * cdegG D + 1 + 1 := by
    rw [hpts, List.length_map, hzs_len]
  rw [hcompute]
  -- Lagrange uniqueness: degree `< #nodes` both sides, agreeing at the nodes
  refine Polynomial.eq_of_degrees_lt_of_eval_index_eq (R := ℚ) (ι := ℕ)
    (s := Finset.range (cdegG f * cdegG D + 1 + 1))
    (v := fun k => (k : ℚ))
    (f := toPolyG (cinterpolateG pts)) (g := R)
    (fun a _ b _ hab => Nat.cast_injective hab) ?_ ?_ ?_
  · -- `degree (toPolyG (cinterpolateG pts)) < #nodes`
    rw [Finset.card_range, Nat.cast_withBot]
    have := degree_toPolyG_cinterpolateG_lt pts hne
    rw [hlen] at this
    simpa [Nat.cast_withBot] using this
  · -- `degree R < #nodes`: `cdegG f · cdegG D + 2 = #nodes`
    rw [Finset.card_range, Nat.cast_withBot]
    have hcard : (cdegG f * cdegG D + 1 + 1 : ℕ) = (cdegG f * cdegG D + 2 : ℕ) := by ring
    rw [hcard]
    exact hRdeg
  · -- agree at the nodes: `toPolyG(cinterpolateG pts)((k:ℚ)) = node value = R((k:ℚ))`
    intro k hk
    -- `(k:ℚ) ∈ zs` since `zs = (range n).map (↑·)` and `k ∈ range n`
    have hzmem : ((k : ℚ)) ∈ zs := by
      rw [hzs, List.mem_map]; exact ⟨k, by simpa using hk, rfl⟩
    have heval := eval_toPolyG_cinterpolateG pts hnodup (hmempts ((k : ℚ)) hzmem)
    rw [htoK, htoK] at heval
    rw [heval]
    exact (hnode k hk).symm

end CPolyG

/-! ### ★ Priority 3 — composing rational + log into the full GENERAL algebraic integral soundness `D(∫f) = f`

The unified general integrator `afIntegrateAlgebraicWf` returns `(v, u)` (and in general `(v, args)`) — a
rational part `v` plus log terms — so `∫f = v + Σ cᵢ log uᵢ` and the full soundness is
`D(∫f) = afDerivWf(v) + Σ cᵢ·afDerivWf(uᵢ)/uᵢ = f`. This **splits exactly into the two halves**, each now a
fuel-free theorem (modulo their isolated per-step inputs):

* the **rational part** `afDerivWf(v) = ratPart(f)` — `ComputableGeneralIntegralSoundness`'s
  `generalReduceRationalTelescopeWf` (the rational-part telescoping over the eq.-11 reduction);
* the **log part** `Σ cᵢ·afDerivWf(uᵢ)/uᵢ = logPart(f)` — this file's `IsGeneralLogIntegralWf`
  (`isGeneralLogIntegralWf_of_residue_match`), with its per-term match the algebraic partial fraction
  (`genRatLogPart_eq_residue_logDeriv_sum`) and its residues the `genResidueResultant` roots
  (`roots_genResidueResultant_eq_residues`).

Cross-multiplied by the log part's common denominator `commonDenom = ∏ uⱼ`, the full identity in the carrier
quotient `K[X] ⧸ afIdeal f` is `afDerivWf(v)·commonDenom + afLogSumNumWf(args) = f·commonDenom`, the sum of the
two halves. We state the composed predicate `IsGeneralAlgebraicIntegralWf` and prove it follows from the
rational soundness (`afDerivWf(v) = ratPart`) + the log soundness (`IsGeneralLogIntegralWf`) + the split
`f = ratPart + logPart`. The general-curve analogue of the radical's `isAlgebraicIntegral_of_parts`. -/

namespace CPolyG

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]

/-- The fuel-free full general algebraic-integral soundness predicate. -/
def IsGeneralAlgebraicIntegralWf (f g v commonDenom : CPolyG α)
    (args : List (α × CPolyG α)) (cofs : List (CPolyG α)) : Prop :=
  Ideal.Quotient.mk (afIdeal f) (toPolyG (afMul f (afDerivWf f v) commonDenom))
    + Ideal.Quotient.mk (afIdeal f) (toPolyG (afLogSumNumWf f args cofs))
  = Ideal.Quotient.mk (afIdeal f) (toPolyG (afMul f g commonDenom))

omit [CDiffFieldSpec α] in
/-- The fuel-free full general algebraic integral composes from Wf rational and log soundness. -/
theorem isGeneralAlgebraicIntegralWf_of_parts (f g v ratPart logPart commonDenom : CPolyG α)
    (args : List (α × CPolyG α)) (cofs : List (CPolyG α))
    (hrat : Ideal.Quotient.mk (afIdeal f)
          (toPolyG (afMul f (afDerivWf f v) commonDenom))
        = Ideal.Quotient.mk (afIdeal f) (toPolyG (afMul f ratPart commonDenom)))
    (hlog : IsGeneralLogIntegralWf f logPart commonDenom args cofs)
    (hsplit : Ideal.Quotient.mk (afIdeal f) (toPolyG (afMul f ratPart commonDenom))
        + Ideal.Quotient.mk (afIdeal f) (toPolyG (afMul f logPart commonDenom))
      = Ideal.Quotient.mk (afIdeal f) (toPolyG (afMul f g commonDenom))) :
    IsGeneralAlgebraicIntegralWf f g v commonDenom args cofs := by
  rw [IsGeneralAlgebraicIntegralWf, hrat, hlog, hsplit]

end CPolyG

/-! ### `#print axioms` — the general-curve log-part setting + foundational floor + obligation 1 milestone

Each log-part predicate, the certificate bridge, the additivity floor, obligation 2 (the log-derivative
residue), obligation 1's general norm factoring and the **root↔residue theorem for the general double
resultant** (`roots_genResidueResultant_eq_residues`), obligation 3 (the partial fraction), and the full
composition carry **only** the standard `[propext, Classical.choice, Quot.sound]` — no `native_decide`
compiler axiom, no `sorry`. The faithful general-curve log-soundness setting (`D(log u) = afDerivWf(u)/u` in the
carrier quotient `K[X] ⧸ afIdeal f`), the fact that every engine-validated log certificate **is** the abstract
single-log soundness (`isGeneralLogTermWf_of_logCert`), the multi-term residue-sum distribution
(`mk_toPolyG_afLogSumNumWf_eq_sum`), the general norm factoring into per-place residues (`genNormFactor` /
`roots_genNorm`), the **milestone** root↔residue theorem (`roots_genResidueResultant_eq_residues`, the
`roots_residueResultant_eq_residues` analogue for the GENERAL double resultant), and the full composition
(`isGeneralAlgebraicIntegralWf_of_parts`) are general theorems — the LOG half of the general algebraic capstone
`D(∫f) = f`, with the residue-correctness core mirrored from the radical template as closely as the general
norm allows. **The compute-bridge is now CLOSED** — `toPolyG_genResidueResultant_eq_of_eval` (the
interpolation-uniqueness characterization, the EXACT `toPolyG_cAlgResidueResultant_eq_of_eval` port to the
general double resultant `genResidueResultant`) discharges the `hR` product-form hypothesis of
`roots_genResidueResultant_eq_residues` for the ENGINE's `genResidueResultant`, so the abstract roots↔residues
milestone connects to the actual engine. With both halves' abstract cores + this engine bridge proven, the
complete algebraic `D(afIntegrateAlgebraicWf f) = f` is **self-contained at its mathematical core**, modulo the
documented `native_decide` engine boundary (the `afLogArgSolveWf`/`afRationalSolveWf` round-trip certificate, the
`hsplit`/`hnode`/`hrat`/`hlog` preconditions the composition theorems take as hypotheses — exactly as the
radical capstone's `isAlgebraicIntegral_of_parts` does), and the `resultant_eq_prod_eval` *application* feeding
the per-node values into `toPolyG_genResidueResultant_eq_of_eval`'s `hnode` (the same factoring
`rtResultant_eq_prod_roots` already provides for the single resultant). -/

-- ★ Obligation 2 (general framing): the logarithmic-derivative residue equals the vanishing order:
#print axioms LogResidue.genLogDeriv_residue_eq_multiplicity

-- ★ Obligation 1's general ingredient: the general residue-norm factors into the per-place residues:
#print axioms LogResidue.genNormFactor

-- ★★ Obligation 1 MILESTONE (abstract): the general residue resultant's roots ARE the per-place residues:
#print axioms LogResidue.roots_genResidueResultant_eq_residues

-- ★★ The compute-bridge CLOSED: the interpolation-uniqueness characterization of the engine's `genResidueResultant`:
#print axioms CPolyG.toPolyG_genResidueResultant_eq_of_eval

-- ★★ Obligation 3 (general framing): the general log-part per-term match IS the algebraic partial fraction:
#print axioms LogResidue.genRatLogPart_eq_residue_logDeriv_sum

-- The fuel-free log/capstone API, using `afDerivWf` and `afLogSumNumWf`:
#print axioms CPolyG.isGeneralLogTermWf_of_logCert
#print axioms CPolyG.mk_toPolyG_afLogSum2Wf
#print axioms CPolyG.mk_toPolyG_afLogSumNumWf_eq_sum
#print axioms CPolyG.isGeneralLogIntegralWf_of_residue_match
#print axioms CPolyG.isGeneralAlgebraicIntegralWf_of_parts

end DeepWiki.SymbolicIntegration
