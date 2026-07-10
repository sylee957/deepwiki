import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalGenericExamples.Helpers

/-! # Mixed-tower example over `√(x⁵ − x − 1)`

Concrete radical carrier and native mixed-derivation checks for the radicand
`x⁵ − x − 1`.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem DensePoly

/-! ### Radicand 2 — `f₂ = x⁵ − x − 1` (degree 5, odd)

A higher-degree radicand `√(x⁵ − x − 1)`. Degree 5 (odd) ⟹ not a square ⟹ the full carrier fires. -/

/-- The radicand `f₂ = x⁵ − x − 1 ∈ ℚ(x)` (numerator `[-1,-1,0,0,0,1]`) for `√(x⁵−x−1)`. -/
def radicandX5mXm1 : DenseFrac ℚ := CFrac.ofPoly [-1, -1, 0, 0, 0, 1]

/-- **`toPoly [-1,-1,0,0,0,1] = −1 − x + x⁵` has `natDegree 5`** in `ℚ[X]`. -/
theorem natDeg_toPolyG_X5mXm1 : (toPoly ([-1, -1, 0, 0, 0, 1] : DensePoly ℚ)).natDegree = 5 := by
  have h : toPoly ([-1, -1, 0, 0, 0, 1] : DensePoly ℚ) = (C (-1) + C (-1) * X) + X ^ 5 := by
    simp only [denote]
    show C (-1 : ℚ) + X * (C (-1) + X * (C 0 + X * (C 0 + X * (C 0 + X * (C 1 + X * 0))))) = _
    simp; ring
  rw [h]; compute_degree!

/-- **`x⁵ − x − 1` is not a square in `ℚ(x)`** — odd-degree helper (`natDegree 5`). -/
theorem not_isSquare_radicandX5mXm1 :
    ∀ b : RatFunc ℚ, b ^ 2 ≠ CFieldSpec.toK (radicandX5mXm1 : DenseFrac ℚ) := by
  rw [radicandX5mXm1, CFrac.toK_ofPoly]
  exact not_isSquare_algebraMap_of_odd_natDegree (by rw [natDeg_toPolyG_X5mXm1]; decide)

/-- **`y² − (x⁵−x−1)` is irreducible over `ℚ(x)`** — generic helper on the non-square `x⁵−x−1`. -/
theorem irreducible_radX5mXm1 :
    Irreducible (X ^ 2 - C (CFieldSpec.toK (radicandX5mXm1 : DenseFrac ℚ))) :=
  irreducible_radDeg2_of_not_isSquare not_isSquare_radicandX5mXm1

/-- The irreducibility `Fact` for `√(x⁵−x−1)`. -/
instance fact_irreducible_radX5mXm1 :
    Fact (Irreducible (X ^ 2 - C (CFieldSpec.toK (radicandX5mXm1 : DenseFrac ℚ)))) :=
  ⟨irreducible_radX5mXm1⟩

/-- The radical field `ℚ(x)[√(x⁵−x−1)] = RadExt (DenseFrac ℚ) 2 (x⁵−x−1)`. -/
abbrev RadX5 : Type := RadExt (DenseFrac ℚ) 2 radicandX5mXm1

/-- **`CFieldDomain RadX5` — discharged generically.** -/
noncomputable example : CFieldDomain RadX5 := inferInstance

/-- **The mixed tower over `√(x⁵−x−1)` is a `CField`** — resolves automatically from the generic radical
base. -/
theorem cfield_qfunNZG_radX5 : Nonempty (CField (DenseFrac RadX5)) := ⟨inferInstance⟩

/-- **The mixed tower over `√(x⁵−x−1)` is a `CDiffField`**. -/
theorem cdiffField_qfunNZG_radX5 : Nonempty (CDiffField (DenseFrac RadX5)) := ⟨inferInstance⟩

/-- The diagonal multiplier `ℓ = f'/(2f) = (5x⁴−1)/(2(x⁵−x−1)) ∈ ℚ(x)` for `D(y) = ℓ·y` over
`√(x⁵−x−1)`. -/
def radX5LogDer : DenseFrac ℚ := logDerRadicand 2 radicandX5mXm1

/-- The `RadX5[t]`-polynomial `t² = [0,0,1]`. -/
def radX5T2sq : DensePoly RadX5 := [CCommRing.zero, CCommRing.zero, CCommRing.one]

/-- The `RadX5[t]`-polynomial `2·t² = [0,0,2]`, the expected `D(t²)` for `t = eˣ`. -/
def radX5TwoT2sq : DensePoly RadX5 := [CCommRing.zero, CCommRing.zero, CCommRing.add CCommRing.one CCommRing.one]

/-- The monomial-derivative datum `Dt = t = [0,1]` over `RadX5` (`t = eˣ`). -/
def radX5DtExp : DensePoly RadX5 := [CCommRing.zero, CCommRing.one]

/-- `D(t²) = 2t²` over `ℚ(x)[√(x⁵−x−1)][eˣ]`: the mixed-tower `d/dt` computation over the degree-5 radical
base. -/
theorem radX5_monomialDeriv_t2sq :
    cisZero (csub (cmonomialDeriv radX5DtExp radX5T2sq) radX5TwoT2sq) = true := by native_decide

/-- The `RadX5[t]`-polynomial `y·t = [0, y]` (`y = √(x⁵−x−1)`, `t = eˣ`). -/
def radX5GenT : DensePoly RadX5 := [CCommRing.zero, RadExt.gen]

/-- The `RadX5[t]`-polynomial `(ℓ+1)·y·t = [0, (ℓ+1)·y]`, the expected mixed `D(y·t)`. -/
def radX5GenTDeriv : DensePoly RadX5 :=
  [CCommRing.zero, CCommRing.mul (⟨[CCommRing.zero, CCommRing.add radX5LogDer CCommRing.one]⟩ : RadX5) CCommRing.one]

/-- `D(y·t) = (ℓ+1)·y·t` over `ℚ(x)[√(x⁵−x−1)][eˣ]`: the mixed derivation over the degree-5 radical base
(`ℓ = (5x⁴−1)/(2(x⁵−x−1))`). -/
theorem radX5_monomialDeriv_genT :
    cisZero (csub (cmonomialDeriv radX5DtExp radX5GenT) radX5GenTDeriv) = true := by native_decide

end DeepWiki.SymbolicIntegration
