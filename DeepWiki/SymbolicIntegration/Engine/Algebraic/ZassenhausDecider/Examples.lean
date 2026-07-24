import DeepWiki.SymbolicIntegration.Engine.Algebraic.ZassenhausDecider.Core

/-! # Zassenhaus decider validation examples

Concrete `native_decide` validations for the Zassenhaus decider.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-! ### The surfacing hypothesis is realizable

`FactorSurfaces` holds on the reducible witness `x² − 1` mod `5`, so the reduction is not vacuous. -/

/-- `FactorSurfaces` holds on the reducible witness `x² − 1` mod `5`. -/
theorem factorSurfaces_X_sq_sub_one :
    FactorSurfaces ([-1, 0] ++ [1] : List ℤ)
      ((5 : ℤ) ^ (2 ^ henselRounds 5 ([-1, 0] ++ [1])))
      (henselLiftMany ([-1, 0] ++ [1])
        ((factorModP 5 (reduceCoeffs 5 ([-1, 0] ++ [1]))).length + 1)
        (factorModP 5 (reduceCoeffs 5 ([-1, 0] ++ [1])))) 2 := by
  intro _ _; native_decide

/-- For `x² − 1` mod `5`, recombination over the lifted factors is non-empty (it finds `x + 1`). -/
theorem recombine_ne_nil_X_sq_sub_one :
    recombine ([-1, 0] ++ [1] : List ℤ) ((5 : ℤ) ^ (2 ^ henselRounds 5 ([-1, 0] ++ [1])))
      (henselLiftMany ([-1, 0] ++ [1])
        ((factorModP 5 (reduceCoeffs 5 ([-1, 0] ++ [1]))).length + 1)
        (factorModP 5 (reduceCoeffs 5 ([-1, 0] ++ [1])))) ≠ [] := by native_decide

/-- A passing `ℤ`-trial-division yields a genuine factorization
`toPolyZ f = listToPoly g * listToPoly (divmodByMonic f g dg).1`, so recombination never accepts a false factor. -/
theorem irreducibleZassenhaus_sound_scope (f g : List ℤ) (dg : ℕ)
    (h : dividesExactly f g dg = true) :
    toPolyZ f = listToPoly g * listToPoly (divmodByMonic f g dg).1 :=
  dividesExactly_dvd h

/-! ## The complete decider where the mod-`p` test provably fails

`irreducibleByModP` returns `false` for `x⁴ + 1` at every prime (`Φ₈` is reducible mod every prime),
yet the complete decider confirms it irreducible via the full Hensel pipeline. -/

/-- The complete decider confirms `x⁴ + 1` irreducible over `ℚ` (mod `3`, via the full pipeline). -/
theorem irreducibleZassenhaus_X_pow_four_add_one :
    irreducibleZassenhaus 3 ([1, 0, 0, 0] ++ [1]) 4 = true := by native_decide

/-- At `p = 3` for `x⁴ + 1`, the complete decider says `true` where the mod-`p` test says `false`. -/
theorem zassenhaus_beats_modp_on_X_pow_four_add_one :
    irreducibleZassenhaus 3 ([1, 0, 0, 0] ++ [1]) 4 = true ∧
    irreducibleByModP 3 ([1, 0, 0, 0] ++ [1]) 4 = false :=
  ⟨irreducibleZassenhaus_X_pow_four_add_one,
    irreducibleByModP_X_pow_four_add_one_false.2.1⟩

/-- `x⁴ + 1` is decided irreducible via mod `5` as well (prime-robust). -/
theorem irreducibleZassenhaus_X_pow_four_add_one_mod5 :
    irreducibleZassenhaus 5 ([1, 0, 0, 0] ++ [1]) 4 = true := by native_decide

/-- `x² − 2` is decided irreducible over `ℚ`. -/
theorem irreducibleZassenhaus_X_sq_sub_two :
    irreducibleZassenhaus 5 ([-2, 0] ++ [1]) 2 = true := by native_decide

/-- `x² − 1` is decided reducible over `ℚ` (`= (x − 1)(x + 1)`). -/
theorem irreducibleZassenhaus_X_sq_sub_one_false :
    irreducibleZassenhaus 5 ([-1, 0] ++ [1]) 2 = false := by native_decide

/-- `x⁴ − 1 = (x − 1)(x + 1)(x² + 1)` is decided reducible (mod `3` finds a proper `ℤ`-factor). -/
theorem irreducibleZassenhaus_X_pow_four_sub_one_false :
    irreducibleZassenhaus 3 ([-1, 0, 0, 0] ++ [1]) 4 = false := by native_decide

/-- `x³ − 2` is decided irreducible over `ℚ`. -/
theorem irreducibleZassenhaus_X_cube_sub_two :
    irreducibleZassenhaus 5 ([-2, 0, 0] ++ [1]) 3 = true := by native_decide

/-! ## The factorization the pipeline finds for `x⁴ + 1` mod `3`

Mod `3`, `factorModP` splits `x⁴ + 1` into the degree-`2` irreducibles `x² + x + 2` and `x² + 2x + 2`. -/

/-- Mod `3`, `factorModP` splits `x⁴ + 1` into **two** degree-`2` factors (the engine `edf` stalled
at one; `ddfCorrect` continues through the trivial degree-`1` block) (`native_decide`). -/
example : (factorModP 3 (reduceCoeffs 3 ([1, 0, 0, 0] ++ [1] : List ℤ))).length = 2 := by
  native_decide

/-- The two mod-`3` factors of `x⁴ + 1` are `x² + x + 2` and `x² + 2x + 2` (low-to-high coefficient
lists, with benign trailing zeros from un-trimmed engine output) (`native_decide`). -/
example : factorModP 3 (reduceCoeffs 3 ([1, 0, 0, 0] ++ [1] : List ℤ))
    = ([[2, 2, 1, 0, 0, 0], [2, 1, 1]] : List (List (ZMod 3))) := by native_decide

end DeepWiki.SymbolicIntegration
