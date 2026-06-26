import DeepWiki.SymbolicIntegration.ComputableAlgebraicResidues
import Sources.Hdl_1721_1_15391.Source

/-! # Trager catalog — Chapter 5 §2: The Residue Resultant (eq. 7)
After the simple-radical rational part is reduced (Appendix A, catalog
`Sources.Hdl_1721_1_15391.AppendixA`), the heart of the **logarithmic** part is the residue
resultant of Chapter 5 §2 (thesis p.56–59, eq. 7): the polynomial over the constant field `K`
whose roots are the residues of the differential, divided by their branch orders. The
`DeepWiki.SymbolicIntegration` library renders this for simple radicals (`F = yⁿ − ρ`, focus
`n = 2`) in `ComputableAlgebraicResidues`, validated by `native_decide`.

**Computable-vs-abstract.** The residue resultant, its membership test, and the integer-residue
failure certificate are computable functions over `K`, `native_decide`-validated on
`∫ dx/((x−1)√x)` on `y² = x`. The abstract correctness (Trager Theorem 2, that the resultant's
roots ARE the residues) is validated by the example, not proved in general.

**The hard next step is OUT OF SCOPE** (see the block below): this delivers the residues `cᵢ`
and the minimal-extension polynomial `R(Z)` (the tractable part), but NOT the actual log
arguments `vᵢ`, which need the divisor construction (Ch. 5 §3), the principal-divisor test, and
the torsion / points-of-finite-order bound (Ch. 6).

## NOT YET FORMALIZED (audit 2026-06-26)
Ch. 5 §3 The Divisor Construction: building the divisor of a candidate logarithmic term from a
  residue (the place-by-place pole/zero data on the curve) `[infra]`.
Ch. 6 The Principal Divisor Test / Torsion Bound: deciding whether a divisor's integer multiple
  is principal (good reduction, the points-of-finite-order bound on the Jacobian) — the genuine
  obstruction to expressing the integral `[research]`.
Ch. 5 §2: the actual log arguments `vᵢ` (the polynomials inside `Σ cᵢ log vᵢ`), assembled from
  the residues and the principal divisors `[infra]`.
Ch. 5 §2: splitting `R(Z)` over its splitting field `K'` (algebraic factoring) to extract the
  residues symbolically when they are not rational `[infra]`.
General algebraic curves (beyond simple radicals `yⁿ = ρ`): integral bases (Ch. 2), absolute
  irreducibility / the curve's function field (Ch. 3), the rational part on a general curve
  (Ch. 4) `[infra]`. -/

open DeepWiki.SymbolicIntegration DeepWiki.SymbolicIntegration.CPolyG

namespace DeepWiki.Tiaf

/-! ## The `n = 2` residue resultant (Ch. 5 §2, eq. 7) -/

/-- **The inner residue norm at a node** (Trager, Chapter 5 §2, eq. 7, p.56): `cAlgResidueNorm`
is eq. 7's inner `resultant_Y(Z·D'(X) − g(X,Y), y² − ρ)` for the simple radical `F = y² − ρ`,
`g = g₀ + g₁·y`, evaluated at `Z = c` — the norm `(c·D' − g₀)² − g₁²·ρ ∈ K[X]` of the linear-in-`y`
form. -/
abbrev ch5_residue_norm := @cAlgResidueNorm

/-- **The `n = 2` residue resultant** `R(Z) = res_X((Z·D' − g₀)² − g₁²·ρ, D)` (Trager, Chapter 5
§2, eq. 7, p.56–59): `cAlgResidueResultant`, the polynomial over `K` whose roots are the residues
divided by their branch orders. Computed by the evaluation + Lagrange-interpolation template of
the transcendental Rothstein–Trager resultant, replacing the operand by the inner norm. Restricted
to `n = 2` (the linear-in-`y` reduction collapses eq. 7's inner `resultant_Y` to one norm). -/
abbrev ch5_residue_resultant := @cAlgResidueResultant

/-- **Residue membership test** (Trager, Chapter 5 §2): `cIsResidue` tests `(Z − c) ∣ R(Z)` — is
`c ∈ K` a root of the residue resultant, hence a residue (divided by its branch order)? -/
abbrev ch5_is_residue := @cIsResidue

/-- **Integer-residue / factorization certificate** (Trager, Chapter 5 §2, the failure test):
`cResiduesMatch` checks that `R(Z)` equals (monic) a claimed product `∏ (Z − cᵢ)` of integer
linear factors — the certificate that a `df/f`-type differential passes Trager's "all residues
are integers" elementarity test. -/
abbrev ch5_residues_match := @cResiduesMatch

/-! ## Validation: `∫ dx/((x−1)·y)` on `y² = x` (Ch. 5 §2, eq. 7) -/

/-- **Chapter 5 §2, eq. 7** (validation): for `∫ dx/((x−1)√x)` on `y² = x` (so `g = y`,
`D = x²−x`), the residue resultant is `R(Z) = Z⁴ − Z² = Z²(Z−1)(Z+1)` (`native_decide`). -/
abbrev ch5_resultant_value := @algResExX_resultant_eq

/-- **Chapter 5 §2, eq. 7** (validation): the residues of `∫ dx/((x−1)√x)` are `±1` — both
`Z = 1` and `Z = −1` are roots of `R(Z)`, the residue `g/D' = (±1)/(2·1−1) = ±1` at the simple
pole `x = 1` on the two sheets (`native_decide`). -/
abbrev ch5_residues_pm_one := @algResExX_residues_pm_one

/-- **Chapter 5 §2, eq. 7** (validation): `Z = 2` is NOT a residue of `∫ dx/((x−1)√x)` — the
membership test rejects a non-root (`native_decide`). -/
abbrev ch5_two_not_residue := @algResExX_two_not_residue

/-- **Chapter 5 §2** (the integer-residue failure test): all residues of `∫ dx/((x−1)√x)` are
integers (`R = Z²(Z−1)(Z+1)`, the `±1` plus the `Z = 0` branch-place root), so this `df/f`-type
differential passes Trager's "all residues are integers" elementarity test (`native_decide`). -/
abbrev ch5_all_residues_integer := @algResExX_all_residues_integer

end DeepWiki.Tiaf
