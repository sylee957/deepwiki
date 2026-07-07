import DeepWiki.SymbolicIntegration.Computable.RischDE.TowerGcdWitnessWf
import DeepWiki.SymbolicIntegration.Computable.RischDE.NormalCorrect

/-! # The weak-normalized recursive Risch-DE solver

`crischDESolveNorm` weak-normalizes `f` to `f̃ = f − Dq/q`, solves the normalized RDE with the
recursive `crischDESolve`, and transforms the solution back by `y = ỹ/q`. The field-level
round-trip and the normalization-correctness sub-lemma `IsWeaklyNormalizedNorm` live here. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG GBPolyCore

/-! ## The round-trip field-algebra identity

If `Ỹ` solves the weakly-normalized `D(Ỹ) + (F − DQ/Q)·Ỹ = Q·G` with `Q ≠ 0`, then `Y = Ỹ/Q`
solves the original `D(Y) + F·Y = G`. -/

section RoundTrip

variable {K : Type*} [Field K] (D : Derivation ℤ (RatFunc K) (RatFunc K))

/-- `roundtrip_field`: if `Ỹ` solves `D(Ỹ) + (F − D(Q)/Q)·Ỹ = Q·G` with `Q ≠ 0`, then `Y = Ỹ/Q`
solves `D(Y) + F·Y = G`. -/
theorem roundtrip_field (F G Q Ytilde : RatFunc K) (hQ : Q ≠ 0)
    (hnorm : D Ytilde + (F - D Q / Q) * Ytilde = Q * G) :
    D (Ytilde / Q) + F * (Ytilde / Q) = G := by
  -- quotient rule: `D(Ỹ/Q) = Q⁻¹²·(Q·DỸ − Ỹ·DQ)`, with `•` over `RatFunc K` reading as `*`
  have hquot : D (Ytilde / Q) = (Q * D Ytilde - Ytilde * D Q) / Q ^ 2 := by
    rw [Derivation.leibniz_div, smul_sub, smul_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      div_eq_inv_mul, inv_pow, mul_sub, mul_assoc]
  rw [hquot]
  -- clear `Q` (and `Q²`): everything multiplied through by `Q²` and matched
  have hQ2 : Q ^ 2 ≠ 0 := pow_ne_zero 2 hQ
  field_simp at hnorm ⊢
  -- `hnorm` now reads (cleared) the normalized identity; rearrange to the goal cleared form
  ring_nf at hnorm ⊢
  linear_combination hnorm

end RoundTrip

/-! ## The normalized recursive solver `crischDESolveNorm`

Weak-normalize `f`, solve the normalized RDE with `crischDESolve`, and transform the solution back.
Computable over `QFunNZG β`. -/

section Lift

variable {β : Type*} [CField β] [CFieldDomain β]

/-- `qOfPolyNZG q`: lift a polynomial `q : CPolyG β` to `QFunNZG β` as `q/1`. -/
def qOfPolyNZG (q : CPolyG β) : QFunNZG β :=
  ⟨(q, [CField.one]), QFunNZG.cisZeroG_one_singleton⟩

end Lift

section Helpers

variable {β : Type*} [CField β] [CDiffField β] [CFieldDomain β]

/-- `weakNormalizedF f q' = f − Dq'/q'` over `QFunNZG β`: the weakly-normalized field element. -/
def weakNormalizedF (f q' : QFunNZG β) : QFunNZG β :=
  qsubNZG f (qmulNZG (towerDerivQFunNZG ([CField.one] : CPolyG β) q') (qinvNZG q'))

end Helpers


/-! ## The computable lowest-terms reduction `reduceSoundOpt`

`reduceSoundOpt` is the shared `[CField β]`-data lowest-terms reducer used by the sound wrappers. -/

section Reduce

variable {β : Type*} [CField β] [CFieldSpec β]

/-- A `[CField β]`-data lowest-terms reducer that rebuilds the `qReduce` representative. -/
def reduceSoundOpt (a : QFunNZG β) : Option (QFunNZG β) :=
  let rd := QFunNZG.reduceDen a
  if h : CPolyG.cisZeroG rd = false then some ⟨(QFunNZG.reduceNum a, rd), h⟩ else none

/-- `reduceSoundOpt a` is exactly `some (qReduce a)`. -/
theorem reduceSoundOpt_eq (a : QFunNZG β) : reduceSoundOpt a = some (qReduce a) := by
  unfold reduceSoundOpt qReduce
  rw [dif_pos (QFunNZG.cisZeroG_reduceDen a)]

end Reduce

/-! ## The normalization-correctness sub-lemma

`IsWeaklyNormalizedNorm h` says `h`'s denominator equals its own normal part — the property that
holds for a weakly-normalized field element. -/

section Normality

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFieldDomain β] [CFracGcdCoreWf β]

/-- `IsWeaklyNormalizedNorm h`: `h`'s denominator equals its own normal part
`toPolyG (cSplitFactorFastGWf [1] _ h.1.2).1 = toPolyG h.1.2`. -/
def IsWeaklyNormalizedNorm (h : QFunNZG β) : Prop :=
  toPolyG (CPolyG.cSplitFactorFastGWf ([CField.one] : CPolyG β) h.1.2).1
    = toPolyG h.1.2

end Normality

/-! ## The construction bridges to the field

The solver's `QFunNZG`-level constructions read at the field level through `toQFunNZG`:
`weakNormalizedF f q'` as `F − D(Q)/Q`, the scaled RHS `q'·g` as `Q·G`, and the returned value
as `Ỹ/Q`. -/

section Bridges

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
  [CRischField β] [Algebra ℚ (CFieldSpec.K β)]

omit [CRischField β] in
/-- `towerFractionFieldDerivG_toQFunNZG`: `towerFractionFieldDerivG [1]` agrees with
`towerDerivQFunNZG [1]` through `toQFunNZG`. -/
theorem towerFractionFieldDerivG_toQFunNZG (x : QFunNZG β) :
    towerFractionFieldDerivG ([CField.one] : CPolyG β) (toQFunNZG x)
      = toQFunNZG (towerDerivQFunNZG ([CField.one] : CPolyG β) x) := by
  rw [towerFractionFieldDerivG, toQFunNZG_towerDerivQFunNZG]

omit [CDiffField β] [CDiffFieldSpec β] [CRischField β]
  [Algebra ℚ (CFieldSpec.K β)] in
/-- `toQFunNZG_qOfPolyNZG_ne_zero`: the lift `q' = q/1` has nonzero field image when `q` is nonzero. -/
theorem toQFunNZG_qOfPolyNZG_ne_zero (q : CPolyG β) (hq : CPolyG.cisZeroG q = false) :
    toQFunNZG (qOfPolyNZG q) ≠ 0 := by
  rw [toQFunNZG]
  show amG β (toPolyG q) / amG β (toPolyG ([CField.one] : CPolyG β)) ≠ 0
  simp only [denote, map_one, mul_zero, add_zero, div_one]
  exact amG_toPolyG_ne_zero (CPolyG.toPolyG_ne_zero_of_cisZeroG_false hq)

omit [CRischField β] in
/-- `toQFunNZG_weakNormalizedF`: `toQFunNZG (weakNormalizedF f q') = toQFunNZG f −
towerFractionFieldDerivG [1] (toQFunNZG q') / toQFunNZG q'`. -/
theorem toQFunNZG_weakNormalizedF (f q' : QFunNZG β) :
    toQFunNZG (weakNormalizedF f q')
      = toQFunNZG f
        - towerFractionFieldDerivG ([CField.one] : CPolyG β) (toQFunNZG q') / toQFunNZG q' := by
  rw [weakNormalizedF, toQFunNZG_qsubNZG, toQFunNZG_qmulNZG, toQFunNZG_qinvNZG,
    towerFractionFieldDerivG_toQFunNZG, div_eq_mul_inv]

omit [CDiffField β] [CDiffFieldSpec β] [CRischField β] [Algebra ℚ (CFieldSpec.K β)] in
/-- `toQFunNZG_solution`: `toQFunNZG (qmulNZG ytilde (qinvNZG q')) = toQFunNZG ytilde / toQFunNZG q'`. -/
theorem toQFunNZG_solution (ytilde q' : QFunNZG β) :
    toQFunNZG (qmulNZG ytilde (qinvNZG q'))
      = toQFunNZG ytilde / toQFunNZG q' := by
  rw [toQFunNZG_qmulNZG, toQFunNZG_qinvNZG, div_eq_mul_inv]

omit [CDiffField β] [CDiffFieldSpec β] [CRischField β] [Algebra ℚ (CFieldSpec.K β)] in
/-- `toQFunNZG_scaledRHS`: `toQFunNZG (qmulNZG q' g) = toQFunNZG q' * toQFunNZG g`. -/
theorem toQFunNZG_scaledRHS (q' g : QFunNZG β) :
    toQFunNZG (qmulNZG q' g) = toQFunNZG q' * toQFunNZG g :=
  toQFunNZG_qmulNZG q' g

end Bridges

end DeepWiki.SymbolicIntegration
