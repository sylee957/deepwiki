import DeepWiki.SymbolicIntegration.Engine.Tower.GcdFF.LevelOneBench

/-! # Simple level-2 fraction-free gcd benchmark inputs

Shared level-2 `t₂`-polynomials over `Lvl2 = ℚ(x)(t₁)`. -/

namespace DeepWiki.SymbolicIntegration

open BenchG in
/-- The `Lvl2 = ℚ(x)(t₁)` scalar unit `(1 : Lvl2)`, for assembling `t₂`-polynomials over the tower. -/
def lvl2One : Lvl2 := CField.one

open BenchG in
/-- The `Lvl2` scalar `t₁ = s/1` (numerator `[0, 1] ∈ (QFunNZG ℚ)[s]`, denominator `[1]`). -/
def lvl2T1scalar : Lvl2 :=
  ⟨([(CField.zero : QFunNZG ℚ), CField.one], [CField.one]), QFunNZG.cisZeroG_one_singleton⟩

open BenchG in
/-- The `t₂`-polynomial `(t₂ − t₁)·(t₂ + 1)` over `Lvl2 = ℚ(x)(t₁)` (low→high in `t₂`). -/
def lvl2P : CPoly Lvl2 :=
  CPoly.cmulG [CField.neg lvl2T1scalar, lvl2One] [lvl2One, lvl2One]

open BenchG in
/-- The `t₂`-polynomial `(t₂ − t₁)·(t₂ − 1)` over `Lvl2`, sharing `(t₂ − t₁)` with `lvl2P`. -/
def lvl2Q : CPoly Lvl2 :=
  CPoly.cmulG [CField.neg lvl2T1scalar, lvl2One] [CField.neg lvl2One, lvl2One]

end DeepWiki.SymbolicIntegration
