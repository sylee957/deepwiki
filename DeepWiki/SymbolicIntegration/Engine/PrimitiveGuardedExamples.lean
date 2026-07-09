import DeepWiki.SymbolicIntegration.Engine.PrimitiveGuarded
import DeepWiki.SymbolicIntegration.Engine.IntegratorCases

/-! # Guarded primitive case examples (`native_decide`)

The guarded primitive case `primitiveGuardedCase` (P2) integrates constant-coefficient canonical-primitive
inputs and *declines* off-domain ones. These `native_decide` checks confirm it is non-vacuous (produces
`checkIdentity`-passing antiderivatives) and honestly declining. `Lvl1 = CFrac ℚ = ℚ(x)`, `Dt = 1`. -/

namespace DeepWiki.SymbolicIntegration

open DensePoly

/-- `∫ 1/t² = −1/t` over `ℚ(x)[t]` (`Dt = 1`): the poly part is `0` (guard passes trivially), the normal
part `1/t²` integrates; `primitiveGuardedCase` lands a `checkIdentity`-passing result. -/
theorem primitiveGuardedCase_invSq :
    (match cIntegrateCase primitiveGuardedCase ([CCommRing.one] : DensePoly Lvl1)
        [CCommRing.one] [CCommRing.zero, CCommRing.zero, CCommRing.one] [CCommRing.zero] with
      | some res => checkIdentity ([CCommRing.one] : DensePoly Lvl1) res [CCommRing.one]
          [CCommRing.zero, CCommRing.zero, CCommRing.one]
      | none => false) = true := by native_decide

/-- `∫ t = t²/2` over `ℚ(x)[t]` (`Dt = 1`): a genuine polynomial part with constant coefficients — the guard
passes and the `b = 0` poly-RDE integrates it. -/
theorem primitiveGuardedCase_polyT :
    (match cIntegrateCase primitiveGuardedCase ([CCommRing.one] : DensePoly Lvl1)
        [CCommRing.zero, CCommRing.one] [CCommRing.one] [] with
      | some res => checkIdentity ([CCommRing.one] : DensePoly Lvl1) res [CCommRing.zero, CCommRing.one] [CCommRing.one]
      | none => false) = true := by native_decide

/-- With a non-primitive `Dt = t` (`toPoly Dt ≠ 1`), the guard fails and
`primitiveGuardedCase` returns `none` — it does not return a wrong answer. -/
theorem primitiveGuardedCase_declines_nonPrimitive :
    cIntegrateCase primitiveGuardedCase ([CCommRing.zero, CCommRing.one] : DensePoly Lvl1)
        [CCommRing.zero, CCommRing.one] [CCommRing.one] [] = none := by native_decide

/-- Automatic candidates find fractional residues: `∫ 1/(t²−1) = ½log(t−1) − ½log(t+1)` has residues
`±1/2`. With `candidates := defaultResidueCandidates 3` (the bounded rational sweep, *not* a hand-picked
list), `primitiveGuardedCase` lands a `checkIdentity`-passing result — `candidates` is computed
automatically. -/
theorem primitiveGuardedCase_autoCands_log :
    (match cIntegrateCase primitiveGuardedCase ([CCommRing.one] : DensePoly Lvl1)
        [CCommRing.one] [CCommRing.neg CCommRing.one, CCommRing.zero, CCommRing.one]
        (defaultResidueCandidates 3) with
      | some res => checkIdentity ([CCommRing.one] : DensePoly Lvl1) res [CCommRing.one]
          [CCommRing.neg CCommRing.one, CCommRing.zero, CCommRing.one]
      | none => false) = true := by native_decide

end DeepWiki.SymbolicIntegration
