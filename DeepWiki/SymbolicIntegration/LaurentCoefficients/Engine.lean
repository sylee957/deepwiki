import DeepWiki.SymbolicIntegration.LaurentCoefficients.Base

/-! # Laurent coefficient engine output

Substitution and output definitions for the Laurent-coefficient engine.
-/

open Polynomial MvPolynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

/-! ## The engine: `Qᵢⱼ` substitution and `Hᵢⱼ` -/

/-- The `Qᵢⱼ` substitution `Option ℕ → K[x]`: `x ↦ X`, `u^(k) ↦ Dᵢ^(k+1)/(k+1)`. -/
noncomputable def laurentSubst (Di : K[X]) : Option ℕ → K[X] := fun v =>
  match v with
  | none => Polynomial.X
  | some k => Polynomial.C ((k + 1 : K)⁻¹) * (derivative^[k + 1] Di)

/-- The polynomial `Qᵢⱼ = aeval (laurentSubst Dᵢ) Pᵢⱼ ∈ K[x]`, substituting the scaled derivatives of `Dᵢ`
into the numerator `Pᵢⱼ = laurentNum A Eᵢ i (i−j)` (`Eᵢ = laurentE D Dᵢ i`). -/
noncomputable def laurentQ (A D Di : K[X]) (i j : ℕ) : K[X] :=
  aeval (laurentSubst Di) (laurentNum A (laurentE D Di i) i (i - j))

/-- The Laurent coefficient `Hᵢⱼ = Qᵢⱼ·Bᵢ^(i−j+1)·Cᵢ^(2i−j) (mod Dᵢ) ∈ K[x]`: `Hᵢⱼ(α)` is the
`1/(x−α)^j` coefficient at a root `α` of `Dᵢ`. -/
noncomputable def laurentH (A D Di : K[X]) (i j : ℕ) : K[X] :=
  (laurentQ A D Di i j * bezoutE D Di i ^ (i - j + 1) * bezoutDeriv Di ^ (2 * i - j)) %ₘ Di

/-- Closed form of `laurentH`. -/
theorem laurentH_def (A D Di : K[X]) (i j : ℕ) :
    laurentH A D Di i j
      = (laurentQ A D Di i j * bezoutE D Di i ^ (i - j + 1) * bezoutDeriv Di ^ (2 * i - j)) %ₘ Di :=
  rfl

end DeepWiki.SymbolicIntegration
