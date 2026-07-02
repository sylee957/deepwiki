import DeepWiki.SymbolicIntegration.Computable.Algebraic.RadicalDerivationInvariant
import DeepWiki.SymbolicIntegration.Computable.Algebraic.RadicalIntegralSoundness
import DeepWiki.SymbolicIntegration.Computable.Algebraic.RadicalLogSoundness
import DeepWiki.SymbolicIntegration.Computable.Algebraic.GeneralIntegralSoundness
import DeepWiki.SymbolicIntegration.Computable.Algebraic.GeneralLogSoundness
import Sources.Hdl_1721_1_15391.Source

/-! # Trager catalog — SOUNDNESS: `D(∫f) = f` for the algebraic integrator (abstract correctness)
The catalogs `Sources.Hdl_1721_1_15391.{AppendixA, Chapter2, Chapter5, Chapter6, IntegrateFull}` render
Trager's algebraic-integration algorithm — the simple-radical rational part (App. A §2), the integral
basis (Ch. 2 §5), the residue double resultant (Ch. 5 §2, eq. 7), the divisor/torsion log part (Ch. 5 §3
/ Ch. 6), and the unified driver — as **computable** functions, each validated by `native_decide`. This
catalog records the **CORRECTNESS** of those same algorithm pieces: `D(∫f) = f` proven as a **general
theorem** in the genuine field `K = CFieldSpec.K α` (read through the Horner bridge `toPolyG`, with the
formal variable `X` the curve generator `y`), **without** `native_decide` — axiom-clean `[propext,
Classical.choice, Quot.sound]`.

The soundness of an already-cataloged algorithm cites the SAME Trager section as the algorithm it certifies:
the derivation laws ↔ App. A §1 (radical `(f/y)'`) / Ch. 2–4 (general `y' = −f_x/f_y`); the rational-part
soundness ↔ App. A §2; the log-part residue correctness ↔ Ch. 5 §2 (eq. 7's double resultant) + §1; and the
capstone `D(∫f) = f` ↔ App. A + Ch. 5. Two parallel arcs: the **simple-radical** carrier `RadElem α =
α[y]/(yⁿ − ρ)` (`ComputableRadical*Soundness`) and the **general curve** `K(x)[y]/(f)`
(`ComputableGeneral*Soundness`); both follow the same `derivation-invariant → first-integral → telescoping →
log-part → capstone` template.

**Abstract-vs-computable (the honest boundary).** Every entry below is an **abstract** theorem in `K[X]` (or
its carrier quotient), carrying no `native_decide` axiom — these are the correctness proofs, not the
`native_decide` validations cataloged elsewhere. They are honest about their scope: the capstone-composition
theorems (`isAlgebraicIntegral_of_parts` / `isGeneralAlgebraicIntegralWf_of_parts`) take the rational
soundness, the log soundness, and the integrand split `f = ratPart + logPart` as **hypotheses** (the engine's
own `native_decide`-validated round-trip certificate discharges the split for a concrete driver run — the
library's documented `native_decide` boundary, since the kernel cannot reduce a fuel recursion over `ℚ`); the
root↔residue theorems take the `resultant_eq_prod_eval` product form as a hypothesis (the mechanical
engine-side compute-bridge). What IS proven generally and abstractly is everything between: the derivation
laws, the keystones, the first integrals, the telescoping invariants, and the abstract residue↔roots cores.

## NOT YET FORMALIZED (audit 2026-06-26)
The capstone-composition `hsplit` (`f = ratPart + logPart`): proven for a concrete driver run only through
  the engine's `native_decide` round-trip certificate (the kernel cannot reduce the driver recursion over `ℚ`
  by `rfl`/`decide`), supplied as a hypothesis to `isAlgebraicIntegral_of_parts` /
  `isGeneralAlgebraicIntegralWf_of_parts` — the irreducible `native_decide`-only kernel residue `[deferred]`.
The root↔residue `resultant_eq_prod_eval` product-form hypothesis: the engine-side compute-bridge feeding
  `cAlgResidueResultant` / `genResidueResultant`'s per-node values into the abstract
  `roots_{,gen}ResidueResultant_eq_residues`; the abstract roots↔residues core is proven, the per-node
  `resultant_eq_prod_eval` instantiation is the mechanical residual `[deferred]`.
Per-step eq.-11 quotient identity for the GENERAL curve: `generalReduceRationalTelescopeWf` is proven GIVEN
  each step's coupled eq.-11 congruence `mk(afDerivWf cⱼ) = mk Lⱼ − mk Lⱼ₊₁` (Trager Ch. 4); discharging it
  for a concrete general (non-radical) eq.-11 run is the residual `[deferred]`. (The radical per-step
  `K`-equation IS discharged for the literal `qxOfNum`-coefficient lifts — catalog
  `Sources.Hdl_1721_1_15391.IntegrateFull` / `AppendixA`.) -/

open DeepWiki.SymbolicIntegration DeepWiki.SymbolicIntegration.RadElem
open DeepWiki.SymbolicIntegration.CPolyG DeepWiki.SymbolicIntegration.LogResidue

namespace DeepWiki.Tiaf

/-! ## The simple-radical derivation is a derivation (App. A §1) -/

/-- **★ The radical-derivation keystone** `toPolyG_radDeriv` (Trager, Appendix A §1, p.74): through the
Horner bridge `toPolyG` (with `X` the radical generator `y`), the diagonal derivation `radDeriv n f` IS
Mathlib's `Differential.implicitDeriv (C (toK ℓ) · X)` for the rule `y' = ℓ·y`, `ℓ = logDerRadicand n f =
f'/(nf)`. Trager's `(f/y)'` insight as an honest `K[X]` identity — the source of additivity and Leibniz.
Abstract (`[propext, Classical.choice, Quot.sound]`, no `native_decide`). -/
abbrev sound_radDeriv_keystone := @RadElem.toPolyG_radDeriv

/-- **★ `radDeriv` is additive** `toPolyG_radDeriv_radAdd` (Trager, Appendix A §1): the diagonal radical
derivation commutes with `radAdd` exactly in `K[X]` (neither touches the `yⁿ = f` reduction) — the first
derivation axiom, from the keystone + `implicitDeriv`'s ℤ-linearity. -/
abbrev sound_radDeriv_add := @RadElem.toPolyG_radDeriv_radAdd

/-- **★ `radDeriv` is Leibniz (modulo the radicand ideal)** `mk_toPolyG_radDeriv_radMul` (Trager, Appendix
A §1): the product rule for `radMul` in the carrier quotient `K[X] ⧸ (Xⁿ − C(toK f))`, valid for a genuine
radical extension (`n·toK f ≠ 0`) — the crux is that the derivation kills the radicand generator mod its
ideal (`D(yⁿ − f) = n·y^{n−1}·y' − f' = 0`). The product-rule derivation axiom. -/
abbrev sound_radDeriv_mul := @RadElem.mk_toPolyG_radDeriv_radMul

/-! ## The simple-radical rational-part soundness `D(v) = g` (App. A §2) -/

/-- **The radical rational-integral soundness predicate** `IsRadicalRationalIntegral n f g v` (Trager,
Appendix A §2): the radical element `v` integrates `g` over `α[y]/(yⁿ − f)`, rational part only — the
genuine-field identity `radDeriv n f v = g` read in `K[X]`. The named target the rational capstone grows
into. -/
abbrev sound_radRationalPredicate := @RadElem.IsRadicalRationalIntegral

/-- **★ The first abstractly-verified algebraic integral `∫ (f'/(nf))·√f = √f`** `toPolyG_radDeriv_radGen`
(Trager, Appendix A §1, p.74): `D(√f) = (f'/(nf))·√f` in the genuine field `K[X]`, general in `n`/`f`/`α`
(the generator identity `y' = ℓ·y` is unconditional). The engine's `native_decide` fact `radDeriv_radGen_eq`
proven as a general theorem — the first algebraic integral verified abstractly. -/
abbrev sound_radGen := @RadElem.toPolyG_radDeriv_radGen

/-- **★ The fuel-recursion telescoping invariant** `radReduceRationalTelescope` (Trager, Appendix A §2,
iterated): `radDeriv` distributes over the rational-part driver's accumulator `foldl radAdd` and the per-step
contributions telescope to the endpoints, giving `radDeriv(accumulated v) + final-leftover = original
integrand` in `K[X]` — the genuinely-new accumulation invariant underwriting `radIntegrateCase{1,2,3}`'s
assembled `v`. -/
abbrev sound_radRationalTelescope := @RadElem.radReduceRationalTelescope

/-- **★ The general rational-part soundness (assembled-`v` form)** `radDeriv_foldlRadAdd_zero_cons_telescope`
(Trager, Appendix A §2): given each step's cleared base-field equation `D(cBᵢ) + cBᵢ·ℓ = cCᵢ − cCᵢ₊₁`, the
assembled pure-`y` antiderivative `v` satisfies `radDeriv(v) = integrand − final-leftover` in `K[X]` — the
rational-part soundness as an abstract identity, reduced to the per-step cleared Case identities. -/
abbrev sound_radRationalSoundness := @RadElem.radDeriv_foldlRadAdd_zero_cons_telescope

/-! ## The simple-radical log-part soundness `D(Σ cᵢ log uᵢ) = logpart` (Ch. 5 §1–§2) -/

/-- **The single-log soundness predicate** `IsRadicalLogTerm n ρ u integrand` (Trager, Chapter 5 §1): the
radical element `u` is a correct single log argument for `integrand` — the genuine-field identity `D(log u)
= integrand`, i.e. `radDeriv(u)/u = integrand` cross-multiplied in the carrier quotient `K[X] ⧸ radIdeal n
ρ` (no division, the faithful quotient form). -/
abbrev sound_radLogPredicate := @RadElem.IsRadicalLogTerm

/-- **★ The engine's log-derivative certificate IS the single-log soundness**
`isRadicalLogTerm_of_radIsLogIntegral` (Trager, Chapter 5 §1): the `native_decide`-checkable boolean
`radIsLogIntegral n ρ u integrand = true` (the division-free `radDeriv u = radMul u integrand`) yields the
abstract quotient identity `D(log u) = integrand`. So every validated `radIsLogIntegral` — arcsinh, arccosh,
the finite-pole `∫ dx/(x√(x²+1))` — IS, abstractly, the single-log soundness in the curve's coordinate
ring. -/
abbrev sound_radLogCertificate := @RadElem.isRadicalLogTerm_of_radIsLogIntegral

/-- **★ The abstractly-verified single-log integral `D(log √f) = f'/(nf)`** `isRadicalLogTerm_radGen`
(Trager, Chapter 5 §1): `radDeriv(√f)/√f = ℓ` (`ℓ = logDerRadicand n f`) as the quotient identity — the
log-part analogue of the rational part's `radGen` first integral, the concrete algebraic-log integral
verified abstractly. -/
abbrev sound_radLogGen := @RadElem.isRadicalLogTerm_radGen

/-- **★ The residue double resultant's roots ARE Trager's residues** `roots_residueResultant_eq_residues`
(Trager, Chapter 5 §2, eq. 7, p.56–59): given the `resultant_eq_prod_eval` product form `R = C(lc)^N · ∏_α
norm(α, Z)`, the roots of the `n = 2` residue resultant are exactly the two-sheet residues `(g₀(α) ±
g₁(α)√ρ(α))/D'(α)` over the roots `α` of `D` — the abstract closure of "eq. 7's resultant computes the
residues" (the transcendental Rothstein–Trager `roots_rtResultant` analogue for the double resultant). -/
abbrev sound_residueResultant_roots := @LogResidue.roots_residueResultant_eq_residues

/-! ## The simple-radical capstone `D(∫f) = f` (App. A + Ch. 5) -/

/-- **The full algebraic-integral soundness predicate** `IsAlgebraicIntegral n ρ f v commonDenom args cofs`
(Trager, Appendix A + Ch. 5): the unified integrator's output `⟨v, args⟩` is a correct antiderivative of `f`
over `α[y]/(yⁿ − ρ)` — `D(v + Σ cᵢ log uᵢ) = f`, splitting `radDeriv(v) + Σ cᵢ·radDeriv(uᵢ)/uᵢ` cross-
multiplied by `commonDenom` and read in the carrier quotient. The full `D(∫f) = f` for the algebraic
integrator. -/
abbrev sound_radCapstonePredicate := @RadElem.IsAlgebraicIntegral

/-- **★★ THE SIMPLE-RADICAL CAPSTONE `D(∫f) = f` composes from rational + log soundness**
`isAlgebraicIntegral_of_parts` (Trager, Appendix A + Ch. 5): given the rational-part soundness (telescoping),
the log-part soundness (residue partial fraction), and the integrand split `f = ratPart + logPart`, the
unified integrator's output satisfies `D(v + Σ cᵢ log uᵢ) = f` in the carrier quotient. The capstone
reassembly — the rational part plus the log part into `D(∫f) = f` (the split is discharged for the actual
driver by its own `native_decide` round-trip certificate, read abstractly). -/
abbrev sound_radCapstone := @RadElem.isAlgebraicIntegral_of_parts

/-! ## The general-curve derivation is a derivation (Ch. 2–4, implicit `y' = −f_x/f_y`) -/

/-- **★ The fuel-free general-derivation keystone** `mk_toPolyG_afDerivWf` (Trager, Chapters 2–4): for an
arbitrary monic curve `f`, `afDerivWf f` realizes Mathlib's `implicitDeriv (toPolyG yprime)` in the quotient
`K[X] ⧸ (toPolyG f)`, with `yprime = afYprimeWf f = −f_x·f_y⁻¹` — the implicit-function-theorem total
derivative without an external fuel parameter. -/
abbrev sound_afDeriv_keystone := @CPolyG.mk_toPolyG_afDerivWf

/-- **★ `afDerivWf` is additive** `mk_toPolyG_afDerivWf_add` (Trager, Chapters 2–4): the general curve
derivation commutes with `caddG` in the quotient `K[X] ⧸ (toPolyG f)`. -/
abbrev sound_afDeriv_add := @CPolyG.mk_toPolyG_afDerivWf_add

/-- **★ `afDerivWf` is Leibniz** `mk_toPolyG_afDerivWf_afMul` (Trager, Chapters 2–4): the product rule for
`afMul` in the carrier `K[X] ⧸ (toPolyG f)`, valid when the fuel-free gcd of `f_y` and `f` is a nonzero
constant. -/
abbrev sound_afDeriv_mul := @CPolyG.mk_toPolyG_afDerivWf_afMul

/-! ## The general-curve rational-part soundness `D(v) = g` (Ch. 4, eq.-11 reduction) -/

/-- **The general rational-integral soundness predicate** `IsGeneralRationalIntegralWf f g v` (Trager,
Chapter 4): the carrier element `v` integrates `g` over `K(x)[y]/(f)`, rational part only — the quotient
identity `afDerivWf f v = g` in `K[X] ⧸ (toPolyG f)`. The general analogue of
`IsRadicalRationalIntegral`. -/
abbrev sound_genRationalPredicate := @CPolyG.IsGeneralRationalIntegralWf

/-- **★ The first abstractly-verified general integral `D(y) = y'`** `mk_toPolyG_afDerivWf_genGen` (Trager,
Chapters 2–4): the carrier generator `y` integrates the implicit derivative `yprime = −f_x/f_y` —
`afDerivWf(y) = yprime` in the quotient, the general analogue of `D(√f) = f'/(nf)·√f` (needs only a nonzero
curve, no separability). -/
abbrev sound_genGen := @CPolyG.mk_toPolyG_afDerivWf_genGen

/-- **★ The general rational-part telescoping soundness** `generalReduceRationalTelescopeWf` (Trager, Chapter
4, eq.-11 reduction): given each step's coupled eq.-11 quotient identity `mk(afDerivWf cⱼ) = mk Lⱼ − mk
Lⱼ₊₁`, the assembled antiderivative `v = cs.foldl caddG []` satisfies `afDerivWf(v) = integrand − final-leftover` in
the carrier — the general analogue of the radical `radReduceRationalTelescope`, the per-step eq.-11
congruence isolated as the named hypothesis. -/
abbrev sound_genRationalTelescope := @CPolyG.generalReduceRationalTelescopeWf

/-! ## The general-curve log-part soundness `D(Σ cᵢ log uᵢ) = logpart` (Ch. 5 §1–§2) -/

/-- **The general single-log soundness predicate** `IsGeneralLogTermWf f u integrand` (Trager, Chapter 5
§1): the carrier element `u` is a correct single log argument for `integrand` over `K(x)[y]/(f)` — the
quotient identity `D(log u) = integrand`, i.e. `afDerivWf(u)/u = integrand` cross-multiplied in `K[X] ⧸
(toPolyG f)`. The general analogue of `IsRadicalLogTerm`. -/
abbrev sound_genLogPredicate := @CPolyG.IsGeneralLogTermWf

/-- **★ The engine's general log certificate IS the single-log soundness** `isGeneralLogTermWf_of_logCert`
(Trager, Chapter 5 §1): the `native_decide`-checkable
`cisZeroG (csubG (afDerivWf f u) (afMul f u integrand)) = true` (the division-free
`afDerivWf f u = afMul f u integrand`) yields the abstract quotient identity `D(log u) =
integrand`. So every validated general log certificate — the non-hyperelliptic `y³ − x² − 1` arguments `u ∝
y`, `u ∝ y² + x` — IS, abstractly, the single-log soundness. -/
abbrev sound_genLogCertificate := @CPolyG.isGeneralLogTermWf_of_logCert

/-- **★ The GENERAL residue double resultant's roots ARE Trager's per-place residues**
`roots_genResidueResultant_eq_residues` (Trager, Chapter 5 §2, eq. 7): for an **arbitrary** curve, given the
`resultant_eq_prod_eval` product form `R = C(lc)^N · ∏_{α₀} genNorm(α₀, Z)`, the roots of the general double
resultant `R(Z) = res_X(res_Y(Z·D' − g, F), D)` are exactly the per-place residues `g(α₀, β)/D'(α₀)` over
every place `(α₀, β)` — the general analogue of `roots_residueResultant_eq_residues` (the radical's
two-sheet `√ρ` quadratic becomes the `deg_y F`-degree fiber product). The milestone root↔residue theorem for
the general double resultant. -/
abbrev sound_genResidueResultant_roots := @LogResidue.roots_genResidueResultant_eq_residues

/-- **★ The general log part is sound given the per-term residue match**
`isGeneralLogIntegralWf_of_residue_match` (Trager, Chapter 5 §1–§2): given the per-term residue match (the
algebraic partial fraction `A/D = Σ residue·logDeriv(X − α)`), the general integrator's log part satisfies
`Σ cᵢ·afDerivWf(uᵢ)/uᵢ = logpart` in the quotient — the log half of the general capstone, the residue-sum
distribution composed with the partial fraction. -/
abbrev sound_genLogSoundness := @CPolyG.isGeneralLogIntegralWf_of_residue_match

/-! ## The general-curve capstone `D(∫g) = g` (Ch. 4 + Ch. 5) -/

/-- **The full general algebraic-integral soundness predicate** `IsGeneralAlgebraicIntegralWf f g v
commonDenom args cofs` (Trager, Chapter 4 + Chapter 5): the unified general integrator's output `(v, args)`
is a correct antiderivative of `g` over `K(x)[y]/(f)` — `D(v + Σ cᵢ log uᵢ) = g`, splitting `afDerivWf(v) + Σ
cᵢ·afDerivWf(uᵢ)/uᵢ` cross-multiplied by `commonDenom` in the carrier quotient. The general analogue of
`IsAlgebraicIntegral`. -/
abbrev sound_genCapstonePredicate := @CPolyG.IsGeneralAlgebraicIntegralWf

/-- **★★ THE GENERAL-CURVE CAPSTONE `D(∫g) = g` composes from rational + log soundness**
`isGeneralAlgebraicIntegralWf_of_parts` (Trager, Chapter 4 + Chapter 5): given the rational-part soundness
(telescoping), the log-part soundness (residue partial fraction), and the integrand split `g = ratPart +
logPart`, the unified general integrator's output satisfies `D(v + Σ cᵢ log uᵢ) = g` in the carrier quotient
`K[X] ⧸ (toPolyG f)` — the full algebraic `D(∫g) = g` for an arbitrary curve, the general analogue of
`isAlgebraicIntegral_of_parts`. -/
abbrev sound_genCapstone := @CPolyG.isGeneralAlgebraicIntegralWf_of_parts

end DeepWiki.Tiaf
