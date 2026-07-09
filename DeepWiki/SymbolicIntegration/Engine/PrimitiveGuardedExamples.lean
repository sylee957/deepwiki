import DeepWiki.SymbolicIntegration.Engine.PrimitiveGuarded
import DeepWiki.SymbolicIntegration.Engine.IntegratorCases

/-! # Guarded primitive case examples (`native_decide`)

The guarded primitive case `primitiveGuardedCase` (P2) integrates constant-coefficient canonical-primitive
inputs and *declines* off-domain ones. These `native_decide` checks confirm it is non-vacuous (produces
`checkIdentity`-passing antiderivatives) and honestly declining. `Lvl1 = QFunNZG ℚ = ℚ(x)`, `Dt = 1`. -/

namespace DeepWiki.SymbolicIntegration

open CPoly

/-- `∫ 1/t² = −1/t` over `ℚ(x)[t]` (`Dt = 1`): the poly part is `0` (guard passes trivially), the normal
part `1/t²` integrates; `primitiveGuardedCase` lands a `checkIdentity`-passing result. -/
theorem primitiveGuardedCase_invSq :
    (match cIntegrateCase primitiveGuardedCase ([CField.one] : CPoly Lvl1)
        [CField.one] [CField.zero, CField.zero, CField.one] [CField.zero] with
      | some res => checkIdentity ([CField.one] : CPoly Lvl1) res [CField.one]
          [CField.zero, CField.zero, CField.one]
      | none => false) = true := by native_decide

/-- `∫ t = t²/2` over `ℚ(x)[t]` (`Dt = 1`): a genuine polynomial part with constant coefficients — the guard
passes and the `b = 0` poly-RDE integrates it. -/
theorem primitiveGuardedCase_polyT :
    (match cIntegrateCase primitiveGuardedCase ([CField.one] : CPoly Lvl1)
        [CField.zero, CField.one] [CField.one] [] with
      | some res => checkIdentity ([CField.one] : CPoly Lvl1) res [CField.zero, CField.one] [CField.one]
      | none => false) = true := by native_decide

/-- With a non-primitive `Dt = t` (`toPoly Dt ≠ 1`), the guard fails and
`primitiveGuardedCase` returns `none` — it does not return a wrong answer. -/
theorem primitiveGuardedCase_declines_nonPrimitive :
    cIntegrateCase primitiveGuardedCase ([CField.zero, CField.one] : CPoly Lvl1)
        [CField.zero, CField.one] [CField.one] [] = none := by native_decide

/-- Automatic candidates find fractional residues: `∫ 1/(t²−1) = ½log(t−1) − ½log(t+1)` has residues
`±1/2`. With `candidates := defaultResidueCandidates 3` (the bounded rational sweep, *not* a hand-picked
list), `primitiveGuardedCase` lands a `checkIdentity`-passing result — `candidates` is computed
automatically. -/
theorem primitiveGuardedCase_autoCands_log :
    (match cIntegrateCase primitiveGuardedCase ([CField.one] : CPoly Lvl1)
        [CField.one] [CField.neg CField.one, CField.zero, CField.one]
        (defaultResidueCandidates 3) with
      | some res => checkIdentity ([CField.one] : CPoly Lvl1) res [CField.one]
          [CField.neg CField.one, CField.zero, CField.one]
      | none => false) = true := by native_decide

end DeepWiki.SymbolicIntegration
