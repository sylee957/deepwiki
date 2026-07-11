import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalGenericExamples.Helpers

/-! # Mixed-tower example over `√(x³ − 2)`

Concrete radical carrier and native mixed-derivation checks for the radicand
`x³ − 2`.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem DensePoly

/-! ### Radicand 1 — `f₁ = x³ − 2` (degree 3, odd)

`x³ − 2` is the radicand of `√(x³ − 2)`. Odd degree ⟹ not a square ⟹ irreducible ⟹ the full carrier
`RadExt (DenseFrac ℚ) 2 (x³−2)` and tower fire generically. -/

/-- The radicand `f₁ = x³ − 2 ∈ ℚ(x)` (numerator `[-2,0,0,1] = −2 + x³`) for `√(x³−2)`. -/
def radicandX3m2 : DenseFrac ℚ := CFrac.ofPoly [-2, 0, 0, 1]

/-- **`toPoly [-2,0,0,1] = −2 + x³` has `natDegree 3`** in `ℚ[X]`. -/
theorem natDeg_toPolyG_X3m2 : (toPoly ([-2, 0, 0, 1] : DensePoly ℚ)).natDegree = 3 := by
  have h : toPoly ([-2, 0, 0, 1] : DensePoly ℚ) = C (-2) + X ^ 3 := by
    simp only [denote]
    show C (-2 : ℚ) + X * (C 0 + X * (C 0 + X * (C 1 + X * 0))) = _
    simp; ring
  rw [h]; compute_degree!

/-- **`x³ − 2` is not a square in `ℚ(x)`** — from the odd-degree helper (`natDegree 3`). -/
theorem not_isSquare_radicandX3m2 :
    ∀ b : RatFunc ℚ, b ^ 2 ≠ CFieldSpec.toK (radicandX3m2 : DenseFrac ℚ) := by
  rw [radicandX3m2, CFrac.toK_ofPoly, toPoly_list_eq]
  exact not_isSquare_algebraMap_of_odd_natDegree (by rw [natDeg_toPolyG_X3m2]; decide)

/-- **`y² − (x³−2)` is irreducible over `ℚ(x)`** — generic helper on the non-square `x³−2`. -/
theorem irreducible_radX3m2 :
    Irreducible (X ^ 2 - C (CFieldSpec.toK (radicandX3m2 : DenseFrac ℚ))) :=
  irreducible_radDeg2_of_not_isSquare not_isSquare_radicandX3m2

/-- The irreducibility `Fact` for `√(x³−2)`, registering it so `CFieldSpec (RadExt … 2 (x³−2))` resolves
(the generic bridge consumes exactly this). -/
instance fact_irreducible_radX3m2 :
    Fact (Irreducible (X ^ 2 - C (CFieldSpec.toK (radicandX3m2 : DenseFrac ℚ)))) :=
  ⟨irreducible_radX3m2⟩

/-- The radical field `ℚ(x)[√(x³−2)] = RadExt (DenseFrac ℚ) 2 (x³−2)`. -/
abbrev RadX3m2 : Type := RadExt (DenseFrac ℚ) 2 radicandX3m2

/-- **`CFieldDomain RadX3m2` — discharged generically** (no bespoke work): from `instCFieldSpecRadExt`
(with `fact_irreducible_radX3m2`) via the global `instCFieldDomainOfCFieldSpec`. The carrier
`RadExt (DenseFrac ℚ) 2 (x³−2)` is a genuine field/domain. -/
noncomputable example : CFieldDomain RadX3m2 DensePoly := inferInstance

/-- **The mixed tower over `√(x³−2)` is a `CField`** — `DenseFrac RadX3m2 ≅ ℚ(x)[√(x³−2)](t)` resolves its
`CField` *automatically* (the keystone `instCFieldCFrac` over the generic `CField`/`CFieldDomain`
radical base). No `x³+1`-specific input. -/
theorem cfield_qfunNZG_radX3m2 : Nonempty (CField (DenseFrac RadX3m2)) := ⟨inferInstance⟩

/-- **The mixed tower over `√(x³−2)` is a `CDiffField`** — inherits `d/dx + radical y' + ∂/∂t`
generically. -/
theorem cdiffField_qfunNZG_radX3m2 : Nonempty (CDiffField (DenseFrac RadX3m2)) := ⟨inferInstance⟩

/-- The diagonal multiplier `ℓ = f'/(2f) = 3x²/(2(x³−2)) ∈ ℚ(x)` for `D(y) = ℓ·y` over `√(x³−2)`. -/
def radX3m2LogDer : DenseFrac ℚ := logDerRadicand 2 radicandX3m2

/-- The `RadX3m2[t]`-polynomial `t² = [0,0,1]` (transcendental square over `√(x³−2)`). -/
def radX3m2T2sq : DensePoly RadX3m2 := [CCommRing.zero, CCommRing.zero, CCommRing.one]

/-- The `RadX3m2[t]`-polynomial `2·t² = [0,0,2]`, the expected `D(t²)` for `t = eˣ`. -/
def radX3m2TwoT2sq : DensePoly RadX3m2 := [CCommRing.zero, CCommRing.zero, CCommRing.add CCommRing.one CCommRing.one]

/-- The monomial-derivative datum `Dt = t = [0,1]` over `RadX3m2` (`t = eˣ`). -/
def radX3m2DtExp : DensePoly RadX3m2 := [CCommRing.zero, CCommRing.one]

/-- `D(t²) = 2t²` over `ℚ(x)[√(x³−2)][eˣ]`: `CPolyEngine.monomialDeriv` (`t = eˣ`, `Dt = t`, coefficient derivation
`radDeriv 2 (x³−2)`) gives `2t·t = 2t²`. -/
theorem radX3m2_monomialDeriv_t2sq :
    cisZero (csub (CPolyEngine.monomialDeriv radX3m2DtExp radX3m2T2sq) radX3m2TwoT2sq) = true := by
  native_decide

/-- The `RadX3m2[t]`-polynomial `y·t = [0, y]` (`y = √(x³−2)`, `t = eˣ`). -/
def radX3m2GenT : DensePoly RadX3m2 := [CCommRing.zero, RadExt.gen]

/-- The `RadX3m2[t]`-polynomial `(ℓ+1)·y·t = [0, (ℓ+1)·y]`, the expected mixed `D(y·t)`
(`ℓ = f'/(2f)`). -/
def radX3m2GenTDeriv : DensePoly RadX3m2 :=
  [CCommRing.zero, CCommRing.mul (⟨[CCommRing.zero, CCommRing.add radX3m2LogDer CCommRing.one]⟩ : RadX3m2) CCommRing.one]

/-- `D(y·t) = (ℓ+1)·y·t` over `ℚ(x)[√(x³−2)][eˣ]`: both `D(y) = ℓ·y` (`ℓ = 3x²/(2(x³−2))`) and `D(t) = t`
fire. -/
theorem radX3m2_monomialDeriv_genT :
    cisZero (csub (CPolyEngine.monomialDeriv radX3m2DtExp radX3m2GenT) radX3m2GenTDeriv) = true := by
  native_decide

end DeepWiki.SymbolicIntegration
