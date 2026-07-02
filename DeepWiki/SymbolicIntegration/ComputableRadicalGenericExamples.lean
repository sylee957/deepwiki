import DeepWiki.SymbolicIntegration.ComputableTranscendentalOverAlgebraic

/-! # The radical/mixed-tower engine over a family of radicands

A generic non-square ⟹ irreducible pipeline (`not_isSquare_algebraMap_of_odd_natDegree` +
`irreducible_radDeg2_of_not_isSquare`) instantiates the carrier `RadExt (QFunNZG ℚ) 2 g` and its mixed
tower `QFunNZG (RadExt (QFunNZG ℚ) 2 g)` for three odd-degree radicands (`x³−2`, `x⁵−x−1`, `x³+x`),
with `native_decide` mixed-tower derivation checks over each. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem CPolyG

/-! ### The generic irreducibility helper

The odd-`intDegree` parity obstruction shows any odd-`natDegree` polynomial radicand is not a square in
`ℚ(x)`; `X_pow_sub_C_irreducible_of_prime Nat.prime_two` then gives `Irreducible (X² − C(toK f))` for
any non-square radicand `f` — hence the `Fact`, hence `CFieldSpec`/`CFieldDomain` for the tower. -/

/-- `∀ b : RatFunc ℚ, b² ≠ algebraMap ℚ[X] (RatFunc ℚ) p` whenever `p.natDegree` is odd: a square `b²`
has even `intDegree = 2·intDegree b`, but `algebraMap p` has odd `intDegree = p.natDegree`. -/
theorem not_isSquare_algebraMap_of_odd_natDegree {p : ℚ[X]} (hodd : Odd p.natDegree) :
    ∀ b : RatFunc ℚ, b ^ 2 ≠ algebraMap (ℚ[X]) (RatFunc ℚ) p := by
  intro b hb
  obtain ⟨k, hk⟩ := hodd
  have hp_ne : p ≠ 0 := by rintro rfl; rw [natDegree_zero] at hk; omega
  have hrhs_ne : algebraMap (ℚ[X]) (RatFunc ℚ) p ≠ 0 := RatFunc.algebraMap_ne_zero hp_ne
  have hb_ne : b ≠ 0 := by rintro rfl; rw [zero_pow (by norm_num)] at hb; exact hrhs_ne hb.symm
  have hdeg : (b ^ 2).intDegree = (algebraMap (ℚ[X]) (RatFunc ℚ) p).intDegree := by rw [hb]
  rw [sq, RatFunc.intDegree_mul hb_ne hb_ne, RatFunc.intDegree_polynomial, hk] at hdeg
  omega

/-- For `f : QFunNZG ℚ` with `∀ b, b² ≠ toK f`, `Irreducible (X² − C(toK f))` over `ℚ(x)` — the
`X_pow_sub_C_irreducible_of_prime Nat.prime_two` instance abstracted over the radicand. -/
theorem irreducible_radDeg2_of_not_isSquare {f : QFunNZG ℚ}
    (h : ∀ b : RatFunc ℚ, b ^ 2 ≠ CFieldSpec.toK f) :
    Irreducible (X ^ 2 - C (CFieldSpec.toK f)) :=
  X_pow_sub_C_irreducible_of_prime Nat.prime_two h

/-! ### Reading a `qxOfNum` radicand into `ℚ(x)` and its `natDegree`

`CFieldSpec.toK (qxOfNum num) = algebraMap ℚ[X] (RatFunc ℚ) (toPolyG num)` (generic in `num`), plus a
per-radicand `natDegree` computation. -/

/-- `toK (qxOfNum num) = algebraMap ℚ[X] (RatFunc ℚ) (toPolyG num)`: a denominator-`1` ℚ(x)-value reads
through the tower bridge as the algebra-map image of its numerator (denominator `toPolyG [1] = 1`). -/
theorem toK_qxOfNum (num : CPolyG ℚ) :
    CFieldSpec.toK (qxOfNum num : QFunNZG ℚ) = algebraMap (ℚ[X]) (RatFunc ℚ) (toPolyG num) := by
  show QFunNZG.toQFunNZG (qxOfNum num) = _
  rw [QFunNZG.toQFunNZG]
  show QFunNZG.amG ℚ (toPolyG num) / QFunNZG.amG ℚ (toPolyG ([CField.one] : CPolyG ℚ)) = _
  have h2 : toPolyG ([CField.one] : CPolyG ℚ) = 1 := by
    show C (CFieldSpec.toK (CField.one : ℚ)) + X * 0 = 1; simp [CFieldSpec.toK_one]
  rw [h2, map_one, div_one]
  rfl

/-! ### Radicand 1 — `f₁ = x³ − 2` (degree 3, odd)

`x³ − 2` is the radicand of `√(x³ − 2)`. Odd degree ⟹ not a square ⟹ irreducible ⟹ the full carrier
`RadExt (QFunNZG ℚ) 2 (x³−2)` and tower fire generically. -/

/-- The radicand `f₁ = x³ − 2 ∈ ℚ(x)` (numerator `[-2,0,0,1] = −2 + x³`) for `√(x³−2)`. -/
def radicandX3m2 : QFunNZG ℚ := qxOfNum [-2, 0, 0, 1]

/-- **`toPolyG [-2,0,0,1] = −2 + x³` has `natDegree 3`** in `ℚ[X]`. -/
theorem natDeg_toPolyG_X3m2 : (toPolyG ([-2, 0, 0, 1] : CPolyG ℚ)).natDegree = 3 := by
  have h : toPolyG ([-2, 0, 0, 1] : CPolyG ℚ) = C (-2) + X ^ 3 := by
    simp only [toPolyG_cons, toPolyG_nil]
    show C (-2 : ℚ) + X * (C 0 + X * (C 0 + X * (C 1 + X * 0))) = _
    simp; ring
  rw [h]; compute_degree!

/-- **`x³ − 2` is not a square in `ℚ(x)`** — from the odd-degree helper (`natDegree 3`). -/
theorem not_isSquare_radicandX3m2 :
    ∀ b : RatFunc ℚ, b ^ 2 ≠ CFieldSpec.toK (radicandX3m2 : QFunNZG ℚ) := by
  rw [radicandX3m2, toK_qxOfNum]
  exact not_isSquare_algebraMap_of_odd_natDegree (by rw [natDeg_toPolyG_X3m2]; decide)

/-- **`y² − (x³−2)` is irreducible over `ℚ(x)`** — generic helper on the non-square `x³−2`. -/
theorem irreducible_radX3m2 :
    Irreducible (X ^ 2 - C (CFieldSpec.toK (radicandX3m2 : QFunNZG ℚ))) :=
  irreducible_radDeg2_of_not_isSquare not_isSquare_radicandX3m2

/-- The irreducibility `Fact` for `√(x³−2)`, registering it so `CFieldSpec (RadExt … 2 (x³−2))` resolves
(the generic bridge consumes exactly this). -/
instance fact_irreducible_radX3m2 :
    Fact (Irreducible (X ^ 2 - C (CFieldSpec.toK (radicandX3m2 : QFunNZG ℚ)))) :=
  ⟨irreducible_radX3m2⟩

/-- The radical field `ℚ(x)[√(x³−2)] = RadExt (QFunNZG ℚ) 2 (x³−2)`. -/
abbrev RadX3m2 : Type := RadExt (QFunNZG ℚ) 2 radicandX3m2

/-- **`CFieldDomain RadX3m2` — discharged generically** (no bespoke work): from `instCFieldSpecRadExt`
(with `fact_irreducible_radX3m2`) via the global `instCFieldDomainOfCFieldSpec`. The carrier
`RadExt (QFunNZG ℚ) 2 (x³−2)` is a genuine field/domain. -/
noncomputable example : CFieldDomain RadX3m2 := inferInstance

/-- **The mixed tower over `√(x³−2)` is a `CField`** — `QFunNZG RadX3m2 ≅ ℚ(x)[√(x³−2)](t)` resolves its
`CField` *automatically* (the keystone `instCFieldQFunNZG` over the generic `CField`/`CFieldDomain`
radical base). No `x³+1`-specific input. -/
theorem cfield_qfunNZG_radX3m2 : Nonempty (CField (QFunNZG RadX3m2)) := ⟨inferInstance⟩

/-- **The mixed tower over `√(x³−2)` is a `CDiffField`** — inherits `d/dx + radical y' + ∂/∂t`
generically. -/
theorem cdiffField_qfunNZG_radX3m2 : Nonempty (CDiffField (QFunNZG RadX3m2)) := ⟨inferInstance⟩

/-- The generator `y = √(x³−2)` as an element of `RadX3m2`. -/
def radX3m2Gen : RadX3m2 := RadExt.gen

/-- The diagonal multiplier `ℓ = f'/(2f) = 3x²/(2(x³−2)) ∈ ℚ(x)` for `D(y) = ℓ·y` over `√(x³−2)`. -/
def radX3m2LogDer : QFunNZG ℚ := logDerRadicand 2 radicandX3m2

/-- The `RadX3m2[t]`-polynomial `t² = [0,0,1]` (transcendental square over `√(x³−2)`). -/
def radX3m2T2sq : CPolyG RadX3m2 := [CField.zero, CField.zero, CField.one]

/-- The `RadX3m2[t]`-polynomial `2·t² = [0,0,2]`, the expected `D(t²)` for `t = eˣ`. -/
def radX3m2TwoT2sq : CPolyG RadX3m2 := [CField.zero, CField.zero, CField.add CField.one CField.one]

/-- The monomial-derivative datum `Dt = t = [0,1]` over `RadX3m2` (`t = eˣ`). -/
def radX3m2DtExp : CPolyG RadX3m2 := [CField.zero, CField.one]

/-- **★ `D(t²) = 2t²` over `ℚ(x)[√(x³−2)][eˣ]`** (`native_decide`): the SAME mixed-tower `d/dt`
computation that holds over `x³+1`, now over the radical base `√(x³−2)`. `cmonomialDeriv` (with `t = eˣ`,
`Dt = t`, coefficient derivation `radDeriv 2 (x³−2)`) gives `D(t²) = 2t·t = 2t²`. THE ENGINE INTEGRATES
OVER `√(x³−2)`. -/
theorem radX3m2_monomialDeriv_t2sq :
    cisZeroG (csubG (cmonomialDeriv radX3m2DtExp radX3m2T2sq) radX3m2TwoT2sq) = true := by
  native_decide

/-- The `RadX3m2[t]`-polynomial `y·t = [0, y]` (`y = √(x³−2)`, `t = eˣ`). -/
def radX3m2GenT : CPolyG RadX3m2 := [CField.zero, radX3m2Gen]

/-- The `RadX3m2[t]`-polynomial `(ℓ+1)·y·t = [0, (ℓ+1)·y]`, the expected mixed `D(y·t)`
(`ℓ = f'/(2f)`). -/
def radX3m2GenTDeriv : CPolyG RadX3m2 :=
  [CField.zero, CField.mul (⟨[CField.zero, CField.add radX3m2LogDer CField.one]⟩ : RadX3m2) CField.one]

/-- **★ `D(y·t) = (ℓ+1)·y·t` over `ℚ(x)[√(x³−2)][eˣ]`** (`native_decide`): the genuine MIXED derivation
over `√(x³−2)` — both `D(y) = ℓ·y` (radical, `ℓ = 3x²/(2(x³−2))`) and `D(t) = t` (monomial) fire, giving
`D(y·t) = (ℓ+1)·y·t`. BOTH HALVES OF THE MIXED TOWER DERIVATION FIRE OVER `√(x³−2)`. -/
theorem radX3m2_monomialDeriv_genT :
    cisZeroG (csubG (cmonomialDeriv radX3m2DtExp radX3m2GenT) radX3m2GenTDeriv) = true := by
  native_decide

/-! ### Radicand 2 — `f₂ = x⁵ − x − 1` (degree 5, odd)

A higher-degree radicand `√(x⁵ − x − 1)`. Degree 5 (odd) ⟹ not a square ⟹ the full carrier fires. -/

/-- The radicand `f₂ = x⁵ − x − 1 ∈ ℚ(x)` (numerator `[-1,-1,0,0,0,1]`) for `√(x⁵−x−1)`. -/
def radicandX5mXm1 : QFunNZG ℚ := qxOfNum [-1, -1, 0, 0, 0, 1]

/-- **`toPolyG [-1,-1,0,0,0,1] = −1 − x + x⁵` has `natDegree 5`** in `ℚ[X]`. -/
theorem natDeg_toPolyG_X5mXm1 : (toPolyG ([-1, -1, 0, 0, 0, 1] : CPolyG ℚ)).natDegree = 5 := by
  have h : toPolyG ([-1, -1, 0, 0, 0, 1] : CPolyG ℚ) = (C (-1) + C (-1) * X) + X ^ 5 := by
    simp only [toPolyG_cons, toPolyG_nil]
    show C (-1 : ℚ) + X * (C (-1) + X * (C 0 + X * (C 0 + X * (C 0 + X * (C 1 + X * 0))))) = _
    simp; ring
  rw [h]; compute_degree!

/-- **`x⁵ − x − 1` is not a square in `ℚ(x)`** — odd-degree helper (`natDegree 5`). -/
theorem not_isSquare_radicandX5mXm1 :
    ∀ b : RatFunc ℚ, b ^ 2 ≠ CFieldSpec.toK (radicandX5mXm1 : QFunNZG ℚ) := by
  rw [radicandX5mXm1, toK_qxOfNum]
  exact not_isSquare_algebraMap_of_odd_natDegree (by rw [natDeg_toPolyG_X5mXm1]; decide)

/-- **`y² − (x⁵−x−1)` is irreducible over `ℚ(x)`** — generic helper on the non-square `x⁵−x−1`. -/
theorem irreducible_radX5mXm1 :
    Irreducible (X ^ 2 - C (CFieldSpec.toK (radicandX5mXm1 : QFunNZG ℚ))) :=
  irreducible_radDeg2_of_not_isSquare not_isSquare_radicandX5mXm1

/-- The irreducibility `Fact` for `√(x⁵−x−1)`. -/
instance fact_irreducible_radX5mXm1 :
    Fact (Irreducible (X ^ 2 - C (CFieldSpec.toK (radicandX5mXm1 : QFunNZG ℚ)))) :=
  ⟨irreducible_radX5mXm1⟩

/-- The radical field `ℚ(x)[√(x⁵−x−1)] = RadExt (QFunNZG ℚ) 2 (x⁵−x−1)`. -/
abbrev RadX5 : Type := RadExt (QFunNZG ℚ) 2 radicandX5mXm1

/-- **`CFieldDomain RadX5` — discharged generically.** -/
noncomputable example : CFieldDomain RadX5 := inferInstance

/-- **The mixed tower over `√(x⁵−x−1)` is a `CField`** — resolves automatically from the generic radical
base. -/
theorem cfield_qfunNZG_radX5 : Nonempty (CField (QFunNZG RadX5)) := ⟨inferInstance⟩

/-- **The mixed tower over `√(x⁵−x−1)` is a `CDiffField`**. -/
theorem cdiffField_qfunNZG_radX5 : Nonempty (CDiffField (QFunNZG RadX5)) := ⟨inferInstance⟩

/-- The generator `y = √(x⁵−x−1)` as an element of `RadX5`. -/
def radX5Gen : RadX5 := RadExt.gen

/-- The diagonal multiplier `ℓ = f'/(2f) = (5x⁴−1)/(2(x⁵−x−1)) ∈ ℚ(x)` for `D(y) = ℓ·y` over
`√(x⁵−x−1)`. -/
def radX5LogDer : QFunNZG ℚ := logDerRadicand 2 radicandX5mXm1

/-- The `RadX5[t]`-polynomial `t² = [0,0,1]`. -/
def radX5T2sq : CPolyG RadX5 := [CField.zero, CField.zero, CField.one]

/-- The `RadX5[t]`-polynomial `2·t² = [0,0,2]`, the expected `D(t²)` for `t = eˣ`. -/
def radX5TwoT2sq : CPolyG RadX5 := [CField.zero, CField.zero, CField.add CField.one CField.one]

/-- The monomial-derivative datum `Dt = t = [0,1]` over `RadX5` (`t = eˣ`). -/
def radX5DtExp : CPolyG RadX5 := [CField.zero, CField.one]

/-- **★ `D(t²) = 2t²` over `ℚ(x)[√(x⁵−x−1)][eˣ]`** (`native_decide`): the mixed-tower `d/dt` computation
over the degree-5 radical base. THE ENGINE INTEGRATES OVER `√(x⁵−x−1)`. -/
theorem radX5_monomialDeriv_t2sq :
    cisZeroG (csubG (cmonomialDeriv radX5DtExp radX5T2sq) radX5TwoT2sq) = true := by native_decide

/-- The `RadX5[t]`-polynomial `y·t = [0, y]` (`y = √(x⁵−x−1)`, `t = eˣ`). -/
def radX5GenT : CPolyG RadX5 := [CField.zero, radX5Gen]

/-- The `RadX5[t]`-polynomial `(ℓ+1)·y·t = [0, (ℓ+1)·y]`, the expected mixed `D(y·t)`. -/
def radX5GenTDeriv : CPolyG RadX5 :=
  [CField.zero, CField.mul (⟨[CField.zero, CField.add radX5LogDer CField.one]⟩ : RadX5) CField.one]

/-- **★ `D(y·t) = (ℓ+1)·y·t` over `ℚ(x)[√(x⁵−x−1)][eˣ]`** (`native_decide`): the genuine MIXED derivation
over the degree-5 radical base (`ℓ = (5x⁴−1)/(2(x⁵−x−1))`). BOTH HALVES FIRE OVER `√(x⁵−x−1)`. -/
theorem radX5_monomialDeriv_genT :
    cisZeroG (csubG (cmonomialDeriv radX5DtExp radX5GenT) radX5GenTDeriv) = true := by native_decide

/-! ### Radicand 3 — `f₃ = x³ + x` (degree 3, odd)

A third radicand `√(x³ + x) = √(x(x²+1))`. Odd degree ⟹ the full carrier fires. -/

/-- The radicand `f₃ = x³ + x ∈ ℚ(x)` (numerator `[0,1,0,1] = x + x³`) for `√(x³+x)`. -/
def radicandX3pX : QFunNZG ℚ := qxOfNum [0, 1, 0, 1]

/-- **`toPolyG [0,1,0,1] = x + x³` has `natDegree 3`** in `ℚ[X]`. -/
theorem natDeg_toPolyG_X3pX : (toPolyG ([0, 1, 0, 1] : CPolyG ℚ)).natDegree = 3 := by
  have h : toPolyG ([0, 1, 0, 1] : CPolyG ℚ) = C 1 * X + X ^ 3 := by
    simp only [toPolyG_cons, toPolyG_nil]
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
def radX3pXT2sq : CPolyG RadX3pX := [CField.zero, CField.zero, CField.one]

/-- The `RadX3pX[t]`-polynomial `2·t² = [0,0,2]`, the expected `D(t²)` for `t = eˣ`. -/
def radX3pXTwoT2sq : CPolyG RadX3pX := [CField.zero, CField.zero, CField.add CField.one CField.one]

/-- The monomial-derivative datum `Dt = t = [0,1]` over `RadX3pX` (`t = eˣ`). -/
def radX3pXDtExp : CPolyG RadX3pX := [CField.zero, CField.one]

/-- **★ `D(t²) = 2t²` over `ℚ(x)[√(x³+x)][eˣ]`** (`native_decide`): the mixed-tower `d/dt` computation
over the radical base `√(x³+x)`. THE ENGINE INTEGRATES OVER `√(x³+x)`. -/
theorem radX3pX_monomialDeriv_t2sq :
    cisZeroG (csubG (cmonomialDeriv radX3pXDtExp radX3pXT2sq) radX3pXTwoT2sq) = true := by native_decide

/-- The `RadX3pX[t]`-polynomial `y·t = [0, y]` (`y = √(x³+x)`, `t = eˣ`). -/
def radX3pXGenT : CPolyG RadX3pX := [CField.zero, radX3pXGen]

/-- The `RadX3pX[t]`-polynomial `(ℓ+1)·y·t = [0, (ℓ+1)·y]`, the expected mixed `D(y·t)`. -/
def radX3pXGenTDeriv : CPolyG RadX3pX :=
  [CField.zero, CField.mul (⟨[CField.zero, CField.add radX3pXLogDer CField.one]⟩ : RadX3pX) CField.one]

/-- **★ `D(y·t) = (ℓ+1)·y·t` over `ℚ(x)[√(x³+x)][eˣ]`** (`native_decide`): the genuine MIXED derivation
over `√(x³+x)` (`ℓ = (3x²+1)/(2(x³+x))`). BOTH HALVES FIRE OVER `√(x³+x)`. -/
theorem radX3pX_monomialDeriv_genT :
    cisZeroG (csubG (cmonomialDeriv radX3pXDtExp radX3pXGenT) radX3pXGenTDeriv) = true := by
  native_decide

/-! ### STRETCH — the general-`n` scope (scoping note, no claim forced)

What a general-`n` `CFieldSpec (RadExt α n f)` would need, and what is reachable now:

* **Irreducibility for prime `n = p`.** Mathlib's `X_pow_sub_C_irreducible_iff_of_prime`
  (`KummerPolynomial.lean`) gives `Irreducible (Xᵖ − C a) ↔ ∀ b, bᵖ ≠ a` for **prime** `p` — exactly the
  "`f` not a perfect `p`-th power" condition. `irreducible_radDeg2_of_not_isSquare` is its `p = 2`
  instance; the same one-liner with `Nat.prime_three` (and a "not a perfect cube" radicand proof) would
  give the **cube-root** `Irreducible (X³ − C(toK f))`. The not-a-perfect-`p`-th-power proof for an
  odd/coprime-degree polynomial generalizes the parity argument: `intDegree (bᵖ) = p·intDegree b`, so a
  polynomial whose `natDegree` is **not divisible by `p`** cannot be a `p`-th power. So general-prime-`n`
  *irreducibility* (hence `Field (AdjoinRoot (Xⁿ − C(toK f)))` and the abstract `CFieldDomain`) is
  reachable now with no new Mathlib.

* **What blocks the general-`n` COMPUTABLE carrier.** The computable `CField (RadExt α n f)` is generic in
  `n` for `zero`/`one`/`add`/`mul`/`neg`/`isZero` (all `radCanon`-folded list arithmetic), but its `inv`
  is `radInv2` — the `n = 2` **conjugate-norm** reciprocal `u⁻¹ = ū/(a²−b²f)`, which reads only
  `y⁰`/`y¹`. A general-`n` field inverse needs the full extended-Euclid-in-`α[y]/(yⁿ−f)` (or the
  resultant/norm form), not yet built. So:
  - **Irreducibility / the genuine field `AdjoinRoot (Xⁿ − C(toK f))`:** general prime `n` now.
  - **The computable `CField` + `CFieldSpec` carrier (with a working `inv`):** `n = 2` (this file's
    three radicands), until the general-`n` inverse lands.

  A degree-3 radical (cube root) is therefore *irreducibility*-reachable today but not yet a computable
  field carrier; the `n = 2` simple-radical family — of which `√(x³+1)`, `√(x³−2)`, `√(x⁵−x−1)`, `√(x³+x)`
  are members — is the fully-realized computable mixed-tower slice. -/

/-! ### `#print axioms` — the family computes, generic helper is sorry/native-free

Each per-radicand mixed-tower integral carries only `[propext, Classical.choice, Quot.sound]` plus the
`native_decide` compiler axiom; the generic irreducibility helpers carry **no** `native`, **no** `sorry`.
So `√(x³+1)` is one member of a family of radical extensions the engine integrates over, all from ONE
generic non-square ⟹ irreducible ⟹ `Fact` ⟹ carrier pipeline. -/

-- The generic helpers (no `native`, no `sorry`):
#print axioms not_isSquare_algebraMap_of_odd_natDegree
#print axioms irreducible_radDeg2_of_not_isSquare
#print axioms irreducible_radX3m2
#print axioms irreducible_radX5mXm1
#print axioms irreducible_radX3pX

-- ★ The per-radicand mixed-tower integrals (each `[…, native]`):
#print axioms radX3m2_monomialDeriv_t2sq
#print axioms radX3m2_monomialDeriv_genT
#print axioms radX5_monomialDeriv_t2sq
#print axioms radX5_monomialDeriv_genT
#print axioms radX3pX_monomialDeriv_t2sq
#print axioms radX3pX_monomialDeriv_genT

end DeepWiki.SymbolicIntegration
