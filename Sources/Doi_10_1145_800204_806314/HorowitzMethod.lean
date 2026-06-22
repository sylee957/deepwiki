import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms
import DeepWiki.SymbolicIntegration.HorowitzLinearSolve
import Sources.Doi_10_1145_800204_806314.Source

/-! # Horowitz–Ostrogradsky method — catalog
Pointers to the `DeepWiki.SymbolicIntegration` machinery formalizing Horowitz's paper (its §2.3 form in
Bronstein). Notation map (paper ↔ library): `B = D` (denominator), `V = D⁻ = gcd(B, B')`, `U = D* = B/V`
the squarefree part, `W = −E` where `E·V = V′·U`; the paper's numerators `C, D` are the library's `B, C`.

The denominator split, the reduction identity, and the linear-solve framework (the operator on the
degree-bounded coordinate spaces, with the solve reduced to its injectivity) are formalized. -/

namespace DeepWiki.Hor

open DeepWiki.SymbolicIntegration

/-- **Denominator split** (the paper's `V = gcd(B,B')`, `U = B/V`): `hoSplit` with `hoSplit_mul`
(`V·U = B`) and `hoSplit_snd_squarefree` (`U` squarefree). -/
noncomputable abbrev split := @hoSplit

/-- **Key divisibility** making the Horowitz `W = −V′·U/V` a polynomial: `V ∣ V′·U`. -/
noncomputable abbrev coefficient_dvd := @hoSplit_fst_dvd_deriv_mul_snd

/-- **Reduction identity** (the integral form of `A = C′U + CW + DV`): given a solution,
`A/(V·U) = (C/V)′ + D/U`, so `∫ A/B = C/V + ∫ D/U`. Abstract differential-field form. -/
abbrev reduction_identity := @horowitz_reduction_step

/-- **Reduction identity in `K(x)`** on the `algebraMap` images of the polynomials. -/
abbrev reduction_identity_ratFunc := @horowitzReduce_step_ratFunc

/-- **The Horowitz linear operator** `(C, D) ↦ C′·U − C·E + D·V` (`= C′U + CW + DV`), `K`-linear in the
numerators; `horowitzLinear_mem_degreeLT` is the degree bound `< deg V + deg U`. -/
noncomputable abbrev linear_operator := @horowitzLinear

/-- **The operator on the degree-bounded coordinate spaces** and the dimension count
(`finrank_degreeLT_prod`, `= deg V + deg U`). -/
noncomputable abbrev linear_operator_coords := @horowitzMap

/-- **The linear solve, reduced to injectivity** (the paper's "`X` is the unique vector satisfying
`EX = F`"): if the operator is injective, every numerator `A` (`deg A < deg B`) has a unique
degree-bounded `C, D` solving `A = C′·U − C·E + D·V`. -/
abbrev solve_of_injective := @exists_unique_horowitz_of_injective

/- ## NOT YET FORMALIZED (subtractive — delete each item once formalized)
Nonsingularity of the system (`det E ≠ 0`, equivalently `horowitzMap` injectivity) — the paper computes
the solution by Cramer's rule (`MUSSLE`, `g₀ = det E`), relying on the unique solvability that traces to
the existence + uniqueness of the rational part of `∫ A/B`. In the `DeepWiki` framework this is the one
remaining lemma `Function.Injective (horowitzMap …)`, by the root-multiplicity argument
(`mult_p(C) ≥ mult_p(V)` for each prime `p ∣ V`, via `pow_sub_one_dvd_derivative_of_pow_dvd` and char-0
derivative multiplicity, giving `V ∣ C` then `C = 0` by degree); it discharges `solve_of_injective`'s
hypothesis to yield the unconditional solve. -/

end DeepWiki.Hor
