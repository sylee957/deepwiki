import DeepWiki.SymbolicIntegration.Subresultants

/-! # Residues of rational functions (Bronstein §4.4, rational case)
The Rothstein–Trager theorem (Bronstein Thm 2.4.1) expresses `∫ A/D` for squarefree `D` as a sum of
logarithms, with coefficients the *residues* of `A/D` at the roots of `D`. For a *simple* root `α`
(`D = (x − α)·E` with `E(α) ≠ 0`), that residue is `A(α)/D'(α)`. This file builds the concrete
rational-function residue (the case §2.4 uses), starting from the derivative-at-a-simple-root relation
`D'(α) = E(α)`; the full abstract residue theory of §4.4 (the residue `π_p(f·p/Dp)` over a monomial
extension, Thm 4.4.1/4.4.2) rests on the §4.2 valuation machinery and is built separately. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {F : Type*} [Field F]

/-- **Derivative at a simple root** (the foundation of the residue): if `D = (X − α)·E`, then
`D'(α) = E(α)` — the `(X − α)·E'` term vanishes at `α`. Hence at a simple root the residue
denominator `D'(α)` equals the cofactor `E(α) = (D/(X−α))(α)`. -/
theorem eval_derivative_X_sub_C_mul (E : F[X]) (α : F) :
    (derivative ((X - C α) * E)).eval α = E.eval α := by
  rw [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul,
    eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero]

/-- **The Rothstein–Trager residue at a simple root** (Bronstein §2.4/§4.4, rational case): the residue
of `A/D` at a simple root `α` of `D = (X − α)·E` is `A(α)/D'(α)`, equal to `A(α)/E(α)` via
`eval_derivative_X_sub_C_mul`. This is the value whose collection over the roots of `D` gives the
logarithmic part of `∫ A/D`, and whose set is the zero set of the Rothstein–Trager resultant
`resultant_x(D, A − t·D')` (Thm 2.4.1). -/
theorem residue_eq_eval_div_eval_derivative (A E : F[X]) (α : F) :
    A.eval α / (derivative ((X - C α) * E)).eval α = A.eval α / E.eval α := by
  rw [eval_derivative_X_sub_C_mul]

/-- **Residue is the partial-fraction coefficient** (§4.4): if `A/D = c/(X−α) + (remainder over E)`
with `D = (X−α)·E`, i.e. `A = c·E + (X−α)·B`, then `c = A(α)/E(α) = A(α)/D'(α)` — the residue.
Recovered by evaluating `A = c·E + (X−α)·B` at `α`. -/
theorem residue_of_partialFraction (A E B : F[X]) (c α : F) (hE : E.eval α ≠ 0)
    (hpf : A = C c * E + (X - C α) * B) :
    c = A.eval α / (derivative ((X - C α) * E)).eval α := by
  rw [eval_derivative_X_sub_C_mul, hpf]
  simp only [eval_add, eval_mul, eval_C, eval_sub, eval_X, sub_self, zero_mul, add_zero]
  rw [mul_div_assoc, div_self hE, mul_one]

end DeepWiki.SymbolicIntegration
