import DeepWiki.SymbolicIntegration.Computable.QFunReduce
import DeepWiki.SymbolicIntegration.Computable.Tower.RischDE
import DeepWiki.SymbolicIntegration.Computable.Tower.RischDEInstance
import DeepWiki.SymbolicIntegration.Computable.Hyperexp.ExampleData

/-! # Tower-level demos for the `QFunNZG` gcd-cancel reducer `qReduce`
`qReduce` divides a fraction's numerator and denominator by their monic gcd, preserving the field value
(`toQFunNZG_qReduce`). These demos show it shrinks a swollen product and unblocks a hyperexponential
residual that otherwise chokes `crischDESolve`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open Compute

/-! ### SWELL demo: `qReduce` shrinks an unreduced product, value unchanged

`qmulNZG (t/(t−1)) ((t−1)/t)` stores the constant `1` as `(t·(t−1))/((t−1)·t)` (num/den length 3);
`qReduce` cancels to `1/1` (length 1) with the field value unchanged. -/

namespace QFunNZG

/-- The fraction `t/(t−1) ∈ QFunNZG ℚ` (numerator `[0,1]`, denominator `[−1,1]`). -/
def swellA : QFunNZG ℚ := ⟨([(0 : ℚ), 1], [(-1 : ℚ), 1]), by native_decide⟩

/-- The fraction `(t−1)/t ∈ QFunNZG ℚ` (numerator `[−1,1]`, denominator `[0,1]`), the reciprocal of
`swellA`. -/
def swellB : QFunNZG ℚ := ⟨([(-1 : ℚ), 1], [(0 : ℚ), 1]), by native_decide⟩

/-- The unreduced product `swellA · swellB = (t·(t−1))/((t−1)·t)` via `qmulNZG`: both num and den are
`t²−t` (length 3) though the value is `1`. -/
def swellProd : QFunNZG ℚ := qmulNZG swellA swellB

/-- The unreduced product `swellProd` has numerator length 3. -/
theorem swellProd_num_length : (CPolyG.cnormG swellProd.1.1 : List ℚ).length = 3 := by native_decide

/-- The unreduced product `swellProd` has denominator length 3. -/
theorem swellProd_den_length : (CPolyG.cnormG swellProd.1.2 : List ℚ).length = 3 := by native_decide

/-- `qReduce` shrinks the swollen product's numerator to length 1. -/
theorem swellProd_reduced_num_length :
    (CPolyG.cnormG (qReduce swellProd).1.1 : List ℚ).length = 1 := by native_decide

/-- `qReduce` shrinks the swollen product's denominator to length 1. -/
theorem swellProd_reduced_den_length :
    (CPolyG.cnormG (qReduce swellProd).1.2 : List ℚ).length = 1 := by native_decide

/-- The reduced product `qReduce swellProd` has nonzero numerator (`cisZeroG` is `false`). -/
theorem swellProd_reduced_num_nonzero :
    CPolyG.cisZeroG (qReduce swellProd).1.1 = false := by native_decide

/-- `qReduce` preserves the field value: `toQFunNZG (qReduce swellProd) = toQFunNZG swellProd`. -/
theorem swellProd_value_preserved :
    toQFunNZG (qReduce swellProd) = toQFunNZG swellProd :=
  toQFunNZG_qReduce swellProd

/-! #### `qReduce` preserves the zero test — the bake-into-ops safety fact

Every tower `native_decide` reads the field zero test `CField.isZero = isZeroNZG`, certified
*value-faithful* by `isZeroNZG_iff`. Since `qReduce` preserves the field value
(`toQFunNZG_qReduce`), it preserves `isZeroNZG`: a reduced fraction tests zero exactly when the
original does. This is the load-bearing fact for the bake-into-`qaddNZG`/`qmulNZG` assessment — any
test of the form `CField.isZero (… add/mul …) = true/false` is unaffected by inserting `qReduce` into
the ops (the value, hence the zero test, is unchanged); only a test pinning a *literal* fraction
representation could shift, and the tower suite pins outer `CPolyG`-list lengths (degree in the new
monomial), not the inner coefficient-fraction lists `qReduce` touches. The reusable theorem now lives next
to the reducer as `QFunNZG.isZeroNZG_qReduce`; this file keeps the motivating tower demo and axiom audit. -/

#print axioms swellProd_value_preserved
#print axioms isZeroNZG_qReduce

end QFunNZG

/-! ### STRETCH demo: `qReduce` unblocks a hyperexponential residual that chokes `crischDESolve`

`ComputableHyperexpNormal`'s §5.9 feedback integrates a normal hyperexponential part `fₙ` via the residual
base solve `crischDESolve 0 R`. That solve can return `none` not because the residual `R` is
non-elementary, but because it arrives as an unreduced `QFunNZG` fraction whose spurious denominator
trips the weak-normalizer. We exhibit that representational frontier on a residual that is the value `1`
stored as `(2x)/(2x)`: `crischDESolve 0 R` chokes (`Rstuck_unreduced_chokes`), but after the fuel-free
gcd-cancel `qReduce` collapses it to `1/1` the base solve succeeds, recovering `∫1 = x`
(`Rstuck_reduced_solves`). So the choke is purely representational (the value is the elementary
δ-constant `1`) and `qReduce` genuinely unblocks it — value-preserving (`toQFunNZG_qReduce`). -/

namespace QFunNZG

open CPolyG

/-! #### The decisive choke/unblock: an unreduced residual `crischDESolve` can't solve until `qReduce`

`Rstuck` is the value `1 ∈ ℚ(x)` stored unreduced as the fraction `(2x)/(2x)` — built by
`qmulNZG (2x/1) (1/2x)`, exactly the `2x/2x` shape the §5.9 frontier flags. `crischDESolve 0 Rstuck` chokes
(`none`) on the spurious `2x` denominator; `crischDESolve 0 (qReduce Rstuck)` solves it. This is the
concrete non-constant-R unblock — value-preserving (`qReduce` keeps `Rstuck = 1`), and it converts a
`none` into a correct `some` (`y = x`). -/

/-- The residual `1 ∈ ℚ(x)` stored unreduced as `(2x)/(2x)`: `qmulNZG (2x/1) (1/(2x))`, with numerator
`2x·1` and denominator `1·2x` (both length-2 lists, the swollen `2x/2x` shape) yet the value `1`. The exact
representational frontier `ComputableHyperexpNormal` describes. -/
def Rstuck : QFunNZG ℚ :=
  qmulNZG nLvl1TwoX ⟨([CField.one], [(0 : ℚ), (2 : ℚ)]), by native_decide⟩

/-- `Rstuck` is the value `1` (`native_decide`): the unreduced `(2x)/(2x)` equals `1 ∈ ℚ(x)`
(`isZero (Rstuck − 1) = true`). So it is a genuine elementary δ-constant residue — the choke below is
representational, not non-elementarity. -/
theorem Rstuck_eq_one : CField.isZero (CField.sub Rstuck (CField.one : QFunNZG ℚ)) = true := by
  native_decide

/-- `Rstuck`'s stored denominator is swollen (length 2) (`native_decide`): the unreduced `(2x)/(2x)` has
a length-2 denominator `2x`, not the reduced `1`. This `2x` is the spurious denominator that chokes
`crischDESolve`. -/
theorem Rstuck_den_swollen : (CPolyG.cnormG Rstuck.1.2 : List ℚ).length = 2 := by native_decide

/-- The unreduced residual chokes `crischDESolve` (`native_decide`, the choke): `crischDESolve 0
Rstuck` over `k = ℚ(x)` returns `none` — even though `Rstuck = 1` (`Rstuck_eq_one`), the weak-
normalizer/normal-denominator stages trip on the spurious `2x` denominator of the unreduced `(2x)/(2x)`.
This is the §5.9 hyperexponential frontier the module docstring flags, reproduced concretely. -/
theorem Rstuck_unreduced_chokes :
    CRischField.crischDESolve (CField.zero : QFunNZG ℚ) Rstuck = none := by native_decide

/-- `qReduce` unblocks the residual: `crischDESolve` then solves, recovering `∫1 = x`
(`native_decide`, the UNBLOCK). After `qReduce Rstuck` cancels `(2x)/(2x)` to `1/1`,
`crischDESolve 0 (qReduce Rstuck)` over `ℚ(x)` returns `some y` with `y = x` (the base integral
`∫1 = x`). So the gcd-cancel layer turns the choke (`Rstuck_unreduced_chokes`, `none`) into a correct
`some` — the non-constant-R hyperexp residual unblock, value-preserving (`Rstuck = 1`, so `∫1 = x`). This
is the stretch deliverable: a residual that currently chokes `crischDESolve` computes once reduced. -/
theorem Rstuck_reduced_solves :
    (match CRischField.crischDESolve (CField.zero : QFunNZG ℚ) (qReduce Rstuck) with
      | some y => CField.isZero (CField.sub y nLvl1X)
      | none => false) = true := by native_decide

#print axioms Rstuck_unreduced_chokes
#print axioms Rstuck_reduced_solves

end QFunNZG

end DeepWiki.SymbolicIntegration
