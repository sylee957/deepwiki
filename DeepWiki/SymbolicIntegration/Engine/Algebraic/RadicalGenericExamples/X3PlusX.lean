import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalGenericExamples.Helpers

/-! # Mixed-tower example over `√(x³ + x)`

Concrete radical carrier and native mixed-derivation checks for the radicand
`x³ + x`.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem CPoly

/-! ### Radicand 3 — `f₃ = x³ + x` (degree 3, odd)

A third radicand `√(x³ + x) = √(x(x²+1))`. Odd degree ⟹ the full carrier fires. -/

/-- The radicand `f₃ = x³ + x ∈ ℚ(x)` (numerator `[0,1,0,1] = x + x³`) for `√(x³+x)`. -/
def radicandX3pX : QFunNZG ℚ := qxOfNum [0, 1, 0, 1]

/-- **`toPolyG [0,1,0,1] = x + x³` has `natDegree 3`** in `ℚ[X]`. -/
theorem natDeg_toPolyG_X3pX : (toPolyG ([0, 1, 0, 1] : CPoly ℚ)).natDegree = 3 := by
  have h : toPolyG ([0, 1, 0, 1] : CPoly ℚ) = C 1 * X + X ^ 3 := by
    simp only [denote]
    show C (0 : ℚ) + X * (C 1 + X * (C 0 + X * (C 1 + X * 0))) = _
    simp; ring
  rw [h]; compute_degree!

/-- **`x³ + x` is not a square in `ℚ(x)`** — odd-degree helper (`natDegree 3`). -/
theorem not_isSquare_radicandX3pX :
    ∀ b : RatFunc ℚ, b ^ 2 ≠ CFieldSpec.toK (radicandX3pX : QFunNZG ℚ) := by
  rw [radicandX3pX, toK_qxOfNum]
  exact not_isSquare_algebraMap_of_odd_natDegree (by rw [natDeg_toPolyG_X3pX]; decide)

/-- **`y² − (x³+x)` is irreducible over `ℚ(x)`** — generic helper on the non-square `x³+x`. -/
theorem irreducible_radX3pX :
    Irreducible (X ^ 2 - C (CFieldSpec.toK (radicandX3pX : QFunNZG ℚ))) :=
  irreducible_radDeg2_of_not_isSquare not_isSquare_radicandX3pX

/-- The irreducibility `Fact` for `√(x³+x)`. -/
instance fact_irreducible_radX3pX :
    Fact (Irreducible (X ^ 2 - C (CFieldSpec.toK (radicandX3pX : QFunNZG ℚ)))) :=
  ⟨irreducible_radX3pX⟩

/-- The radical field `ℚ(x)[√(x³+x)] = RadExt (QFunNZG ℚ) 2 (x³+x)`. -/
abbrev RadX3pX : Type := RadExt (QFunNZG ℚ) 2 radicandX3pX

/-- **`CFieldDomain RadX3pX` — discharged generically.** -/
noncomputable example : CFieldDomain RadX3pX := inferInstance

/-- **The mixed tower over `√(x³+x)` is a `CField`**. -/
theorem cfield_qfunNZG_radX3pX : Nonempty (CField (QFunNZG RadX3pX)) := ⟨inferInstance⟩

/-- **The mixed tower over `√(x³+x)` is a `CDiffField`**. -/
theorem cdiffField_qfunNZG_radX3pX : Nonempty (CDiffField (QFunNZG RadX3pX)) := ⟨inferInstance⟩

/-- The generator `y = √(x³+x)` as an element of `RadX3pX`. -/
def radX3pXGen : RadX3pX := RadExt.gen

/-- The diagonal multiplier `ℓ = f'/(2f) = (3x²+1)/(2(x³+x)) ∈ ℚ(x)` for `D(y) = ℓ·y` over `√(x³+x)`. -/
def radX3pXLogDer : QFunNZG ℚ := logDerRadicand 2 radicandX3pX

/-- The `RadX3pX[t]`-polynomial `t² = [0,0,1]`. -/
def radX3pXT2sq : CPoly RadX3pX := [CField.zero, CField.zero, CField.one]

/-- The `RadX3pX[t]`-polynomial `2·t² = [0,0,2]`, the expected `D(t²)` for `t = eˣ`. -/
def radX3pXTwoT2sq : CPoly RadX3pX := [CField.zero, CField.zero, CField.add CField.one CField.one]

/-- The monomial-derivative datum `Dt = t = [0,1]` over `RadX3pX` (`t = eˣ`). -/
def radX3pXDtExp : CPoly RadX3pX := [CField.zero, CField.one]

/-- `D(t²) = 2t²` over `ℚ(x)[√(x³+x)][eˣ]`: the mixed-tower `d/dt` computation over `√(x³+x)`. -/
theorem radX3pX_monomialDeriv_t2sq :
    cisZeroG (csubG (cmonomialDeriv radX3pXDtExp radX3pXT2sq) radX3pXTwoT2sq) = true := by native_decide

/-- The `RadX3pX[t]`-polynomial `y·t = [0, y]` (`y = √(x³+x)`, `t = eˣ`). -/
def radX3pXGenT : CPoly RadX3pX := [CField.zero, radX3pXGen]

/-- The `RadX3pX[t]`-polynomial `(ℓ+1)·y·t = [0, (ℓ+1)·y]`, the expected mixed `D(y·t)`. -/
def radX3pXGenTDeriv : CPoly RadX3pX :=
  [CField.zero, CField.mul (⟨[CField.zero, CField.add radX3pXLogDer CField.one]⟩ : RadX3pX) CField.one]

/-- `D(y·t) = (ℓ+1)·y·t` over `ℚ(x)[√(x³+x)][eˣ]`: the mixed derivation over `√(x³+x)`
(`ℓ = (3x²+1)/(2(x³+x))`). -/
theorem radX3pX_monomialDeriv_genT :
    cisZeroG (csubG (cmonomialDeriv radX3pXDtExp radX3pXGenT) radX3pXGenTDeriv) = true := by
  native_decide

end DeepWiki.SymbolicIntegration
