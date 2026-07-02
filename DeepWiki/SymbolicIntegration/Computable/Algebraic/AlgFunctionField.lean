import DeepWiki.SymbolicIntegration.Computable.Algebraic.RadicalExtension
import DeepWiki.SymbolicIntegration.Computable.Algebraic.HermiteNormalForm
import DeepWiki.SymbolicIntegration.Computable.Algebraic.BareissEngine

/-! # The general algebraic function field `K(x, y) = K(x)[y]/(f)` — trace and discriminant
(Trager, *Integration of Algebraic Functions*, Ch. 2 §"Integral Bases", p. 24–26)

`ComputableRadicalExtension` opened the algebraic axis for the **radical** special case `f = yⁿ − ρ`
(the carrier `RadExt`, with its diagonal `(f/y)'` derivation). The Ford–Zassenhaus **Round-2**
integral-basis algorithm (Trager Ch. 2) works for an **arbitrary** monic curve
`f(y) = yⁿ + a_{n−1}yⁿ⁻¹ + … + a₀` over `K(x)` — trigonal `y³+xy+x`, the non-radical `y²−xy−x³`, any
plane curve — not only `yⁿ = ρ`. This file builds the inputs that algorithm consumes: the general
carrier `K(x)[y]/(f)`, the **trace map** `Tr : K(x, y) → K(x)`, the **trace matrix** `[Tr(ωᵢωⱼ)]`, and
the **discriminant** `det[Tr(ωᵢωⱼ)]`, cross-checked against `Resultant(f, f')`.

The base field is `α = QFunNZG ℚ ≅ ℚ(x)` (or any `[CField α]`); an element of `K(x, y)` is a polynomial
in `y` of degree `< n` with coefficients in `α`, i.e. a `CPolyG α` reduced `mod f`. Unlike the radical
carrier (a dedicated `RadElem` list with `yⁿ → ρ` baked into multiplication), the general carrier reuses
`CPolyG α = α[y]` directly: multiplication is `cmulG` followed by `cmodWf · f` (general Euclidean
reduction, not a single `yⁿ → ρ` fold). For a radical `f = yⁿ − ρ` the two agree (`afMul` and `radMul`
give the same coset), so this is a strict generalization — confirmed by the conservativity check
`trace (y² − ρ) y = 0` matching the radical fact `Tr(y) = 0`.

* **`afReduce`/`afMul`/`afPow`** — the ring `α[y]/(f)`: reduce `mod f` (`cmodWf`), multiply-then-reduce,
  power. `afBasisElem i = yⁱ` is the `i`-th power basis vector.
* **`multMatrix f w`** — the `n×n` multiplication-by-`w` matrix `M_w` over `α` (column `i` = coeff vector
  of `w·yⁱ mod f`); **`trace f w`** = `Σ diag(M_w)`, the field trace `Tr_{K(x,y)/K(x)}(w)`.
* **`traceMatrix f basis`** = `[Tr(ωᵢ·ωⱼ)]`, the `n×n` Gram matrix of the trace form; **`discriminant
  f`** = `det(traceMatrix f [1, y, …, yⁿ⁻¹])` (the `α`-matrix Laplace determinant `fieldDet`).
* **`Resultant(f, f')` cross-check** (`cresultantG`, eliminating `y`) — the two computations of the
  discriminant agree up to sign (Trager's `disc(f) = ± Res(f, f')/lc(f)`; `lc = 1` here, monic).

**Validation** (`native_decide`): on the **non-radical** curve `f = y² − xy − x³` over `ℚ(x)`,
`trace f y = x = −a_{n−1}` is **nonzero** (vs `0` for a radical), the trace matrix is
`[[2, x], [x, x²+2x³]]`, the discriminant is `x² + 4x³`, and `det(traceMatrix f) = ± Res(f, f')`; the
trigonal curve `y³ + xy + x` is checked too. **Conservativity**: on a radical `f = y² − ρ`,
`trace f y = 0`, matching the `RadExt` fact `Tr(y) = 0`.

**The engine now has the general algebraic-function-field carrier + trace + discriminant** — the
Round-2 integral-basis inputs for arbitrary plane curves, beyond radicals. The next pieces (documented
at the end): the **p-trace-radical** (`M ū ∈ p · Rⁿ` solved by `hermiteRowReduce` over `K[x]`) and the
**idealizer**, iterated to the maximal order = integral basis. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace CPolyG

variable {α : Type*} [CField α]

/-! ### The ring `K(x)[y]/(f)` for an arbitrary monic `f` (`afReduce`/`afMul`/`afPow`)

An element of `K(x, y) = α[y]/(f)` is a `CPolyG α = α[y]` of degree `< n = deg f`. The coset arithmetic
reuses the generic engine: addition is `caddG`, multiplication is `cmulG` followed by the **general**
Euclidean reduction `cmodWf _ f` (for a monic `f` of degree `n` the remainder has degree `< n`, the
canonical coset representative). This is the arbitrary-curve analogue of `RadElem.radMul` — but where
`radMul` folds the *single* relation `yⁿ → ρ`, `afMul` divides by the *whole* `f`, so it works for any
monic curve (`y² − xy − x³`, `y³ + xy + x`, …), not just `yⁿ = ρ`. -/

/-- **Reduce a free `y`-polynomial modulo `f`** in `α[y]/(f)`: the fuel-free Euclidean remainder
`cmodWf p f` (degree `< deg f` for monic `f`), the canonical coset representative. -/
def afReduce (f p : CPolyG α) : CPolyG α := cmodWf p f

/-- **Multiplication** in `α[y]/(f)`: free polynomial multiply (`cmulG`) then reduce `mod f` (`afReduce`)
— the general-curve analogue of `RadElem.radMul`, dividing by the whole monic `f` rather than folding a
single `yⁿ → ρ`. -/
def afMul (f a b : CPolyG α) : CPolyG α := afReduce f (cmulG a b)

/-- **The `i`-th power-basis element** `yⁱ` of `α[y]/(f)` (`cshiftG i [1] = xⁱ`), the basis used for the
trace matrix `[1, y, …, yⁿ⁻¹]`. -/
def afBasisElem (i : ℕ) : CPolyG α := cshiftG i [CField.one]

/-- **Power** in `α[y]/(f)`: `afPow f a k = aᵏ mod f` by `ℕ`-recursion (`[1]` at `0`), each step an
`afMul`. -/
def afPow (f a : CPolyG α) : ℕ → CPolyG α
  | 0 => [CField.one]
  | k + 1 => afMul f a (afPow f a k)

/-! ### The multiplication matrix `M_w` and the trace `Tr(w)` (Trager p. 25)

For `w ∈ K(x, y)`, multiplication-by-`w` is a `K(x)`-linear map on the `n`-dimensional space `α[y]/(f)`;
in the power basis `[1, y, …, yⁿ⁻¹]` its matrix `M_w` has **column `i`** = the coefficient vector of
`w·yⁱ mod f`. The **field trace** `Tr_{K(x,y)/K(x)}(w)` is `tr(M_w) = Σᵢ (M_w)ᵢᵢ`, i.e. the sum over `i`
of the coefficient of `yⁱ` in `w·yⁱ mod f`. `Tr` is `K(x)`-linear and (for `f` monic of degree `n`)
`Tr(1) = n`, `Tr(y) = −a_{n−1}` — nonzero for a non-radical curve, zero for a radical `yⁿ − ρ`
(`a_{n−1} = 0`). -/

/-- **The coefficient of `yⁱ`** in `p : CPolyG α` (the `α`-entry at index `i`, `CField.zero` past the
end) — the matrix-entry read for `multMatrix`/`trace`. -/
def afCoeff (p : CPolyG α) (i : ℕ) : α := (p : List α).getD i CField.zero

/-- **The multiplication-by-`w` matrix `M_w`** of `α[y]/(f)`, an `n×n` matrix over `α` (`n = deg f`):
**row `r`, column `c`** is the coefficient of `yʳ` in `w·y^c mod f` (so column `c` is the coordinate
vector of `w·y^c`). Represented as `List (List α)` (rows of `α`-entries). -/
def multMatrix (f w : CPolyG α) : List (List α) :=
  let n := cdegG f
  (List.range n).map (fun r =>
    (List.range n).map (fun c => afCoeff (afMul f w (afBasisElem c)) r))

/-- **The field trace** `Tr_{K(x,y)/K(x)}(w) = Σᵢ (M_w)ᵢᵢ` — the sum of the diagonal of the
multiplication-by-`w` matrix, i.e. `Σᵢ` (coefficient of `yⁱ` in `w·yⁱ mod f`). `K(x)`-linear;
`Tr(1) = n`, `Tr(y) = −a_{n−1}`. -/
def trace (f w : CPolyG α) : α :=
  let n := cdegG f
  (List.range n).foldl (fun acc i =>
    CField.add acc (afCoeff (afMul f w (afBasisElem i)) i)) CField.zero

/-! ### The trace matrix `[Tr(ωᵢωⱼ)]` and the discriminant `det[Tr(ωᵢωⱼ)]`

For a `K(x)`-basis `[ω₀, …, ω_{n−1}]` of `K(x, y)`, the **trace matrix** (Gram matrix of the trace
bilinear form) is `T = [Tr(ωᵢ·ωⱼ)]`, a symmetric `n×n` matrix over `K(x)`. The **discriminant** of the
basis is `det T`. For the power basis `ωᵢ = yⁱ` this is the discriminant of the curve `f`, and equals
`± Resultant(f, f')` (`disc(f) = (−1)^{n(n−1)/2} Res(f, f')/lc(f)`; `lc = 1` monic). The discriminant's
squarefree part is the product of the *bad primes* `p` where the equation order `K[x][y]/(f)` may fail
to be integrally closed — the primes Round-2 must enlarge the order at. -/

/-- **The trace matrix** `[Tr(ωᵢ·ωⱼ)]` of a basis `basis = [ω₀, …, ω_{m−1}]` for `α[y]/(f)`: the `m×m`
symmetric matrix over `α` whose `(i, j)` entry is `trace f (afMul f ωᵢ ωⱼ)`. The Gram matrix of the
trace bilinear form. -/
def traceMatrix (f : CPolyG α) (basis : List (CPolyG α)) : List (List α) :=
  basis.map (fun ωi => basis.map (fun ωj => trace f (afMul f ωi ωj)))

/-- **The power basis** `[1, y, …, yⁿ⁻¹]` (`n = deg f`) of `α[y]/(f)`, the default basis for the
discriminant. -/
def powerBasis (f : CPolyG α) : List (CPolyG α) := (List.range (cdegG f)).map afBasisElem

/-- **Drop column `j`** from a row (the `α`-list with index `j` removed) — the minor-extraction helper
for the Laplace determinant `fieldDet`. -/
def dropCol (row : List α) (j : ℕ) : List α := row.eraseIdx j

/-- **The `n×n` determinant over the field `α`** by Laplace (cofactor) expansion along the first row,
sized by an explicit `ℕ` dimension `n` (the recursion fuel): `det M = Σⱼ (−1)ʲ · M[0][j] · det(minor₀ⱼ)`,
where `minor₀ⱼ` drops row `0` and column `j`. Generic over `[CField α]` (the entries are field elements,
NOT polynomials — the trace matrix lives over `α`); the sign `(−1)ʲ` is `CField.neg`-toggled. `n`
decreases on each minor, so the recursion is structural. Use `fieldDet M.length M` for an honest matrix. -/
def fieldDetSized : ℕ → List (List α) → α
  | 0, _ => CField.one
  | _, [] => CField.one
  | n + 1, (row :: rows) =>
    (List.range (n + 1)).foldl (fun acc j =>
      let entry := row.getD j CField.zero
      let minor := rows.map (fun r => dropCol r j)
      let cofactor := CField.mul entry (fieldDetSized n minor)
      let signed := if j % 2 = 0 then cofactor else CField.neg cofactor
      CField.add acc signed) CField.zero

/-- **The `n×n` determinant over the field `α`** by Laplace expansion (`fieldDetSized` with the matrix's
own row count as the dimension): `det M = Σⱼ (−1)ʲ · M[0][j] · det(minor₀ⱼ)`. Used for `discriminant`;
for small `n` this is direct, and the diagonal product of `hermiteRowReduce` gives an alternative for
larger `n`. -/
def fieldDet (M : List (List α)) : α := fieldDetSized M.length M

/-- **The discriminant** of the monic curve `f` over `ℚ(x) = QFunNZG ℚ`: `det[Tr(ωᵢ·ωⱼ)]` for the power
basis `[1, y, …, yⁿ⁻¹]`, computed **fraction-free** via `qfDet` (clear the `ℚ(x)`-trace-matrix to a common
denominator over `ℚ[x]`, run Bareiss, read back) — never forming the swelling `ℚ(x)` Laplace expansion that
the generic `fieldDet` does. Equal to `fieldDet (traceMatrix f (powerBasis f))` (validated by
`qfDet_eq_fieldDet_*`), hence to `± Resultant(f, f')`; its squarefree part bounds the primes where the
equation order is non-maximal (Trager Ch. 2). -/
def discriminant (f : CPolyG (QFunNZG ℚ)) : QFunNZG ℚ :=
  qfDet (traceMatrix f (powerBasis f))

/-- **`Resultant(f, f')` for the curve `f`** (the alternative discriminant up to sign): `cresultantG`
of `f` against its formal `y`-derivative `cderivG f`, eliminating `y`. Equal to `± discriminant f`
(`disc(f) = (−1)^{n(n−1)/2} Res(f, f')/lc(f)`, `lc = 1` monic). Fuel `2·deg f + 2`. -/
def discResultant (f : CPolyG α) : α := cresultantG (2 * cdegG f + 2) f (cderivG f)

end CPolyG

/-! ### ★ The non-radical curve `f = y² − x·y − x³` over `ℚ(x)` (`native_decide`)

`α = QFunNZG ℚ ≅ ℚ(x)`, `n = 2`, the **non-radical** curve `f(y) = y² − x·y − x³`
(`a₁ = −x ≠ 0` — the `−xy` term is exactly what makes it non-radical, unlike `y² − ρ`). The basis is
`[1, y]`; `y² ≡ x·y + x³ (mod f)`.

* `Tr(1) = 2` (the `2×2` identity matrix has trace `2`).
* `Tr(y) = x = −a₁` — **nonzero**, the hallmark of a non-radical curve.
* `Tr(y²) = Tr(x·y + x³) = x·Tr(y) + x³·Tr(1) = x·x + 2x³ = x² + 2x³`.
* Trace matrix `T = [[2, x], [x, x² + 2x³]]`.
* `disc = det T = 2(x² + 2x³) − x·x = x² + 4x³ = a₁² − 4a₀` (the quadratic discriminant `(−x)² − 4(−x³)`).
* Cross-check `det T = ± Res(f, f')` (`f' = 2y − x`; the resultant equals `−(a₁² − 4a₀)` here, the
  expected sign flip `(−1)^{n(n−1)/2} = −1` for `n = 2`). -/

open CPolyG

/-- The non-radical curve `f = y² − x·y − x³ ∈ ℚ(x)[y]` (coefficients `a₀ = −x³`, `a₁ = −x`, monic),
as a `CPolyG (QFunNZG ℚ)` `[−x³, −x, 1]`. The `−x·y` term makes the curve genuinely non-radical. -/
def afNonRadF : CPolyG (QFunNZG ℚ) :=
  [qxOfNum [0, 0, 0, -1], qxOfNum [0, -1], CField.one]

/-- The generator `y` of `ℚ(x)[y]/(f)` (`afBasisElem 1 = [0, 1]`). -/
def afNonRadY : CPolyG (QFunNZG ℚ) := afBasisElem 1

/-- **★ `Tr(y) = x` on the non-radical curve** (`native_decide`): the field trace of the generator `y`
of `ℚ(x)[y]/(y² − xy − x³)` is `x = −a₁`, the `ℚ(x)` value `x` — **nonzero**, unlike a radical curve
where `Tr(y) = 0`. The general trace map computes on a non-radical curve. Checked by `CField.isZero` of
`Tr(y) − x`. -/
theorem afNonRad_trace_y_eq_x :
    CField.isZero (CField.sub (trace afNonRadF afNonRadY) (qxOfNum [0, 1])) = true := by native_decide

/-- **`Tr(1) = 2` on the non-radical curve** (`native_decide`): the trace of `1` is `n = 2` (the
diagonal of the `2×2` identity matrix `M₁`), the `ℚ(x)` constant `2`. -/
theorem afNonRad_trace_one_eq_two :
    CField.isZero (CField.sub (trace afNonRadF [CField.one]) (qxOfNum [2])) = true := by native_decide

/-- **`Tr(y²) = x² + 2x³` on the non-radical curve** (`native_decide`): reducing `y² ≡ xy + x³` and
taking the trace gives `x·Tr(y) + x³·Tr(1) = x² + 2x³`, the `ℚ(x)` value `x² + 2x³`. The trace is
`K(x)`-linear and respects the `mod f` reduction. -/
theorem afNonRad_trace_ysq :
    CField.isZero (CField.sub (trace afNonRadF (afMul afNonRadF afNonRadY afNonRadY))
      (qxOfNum [0, 0, 1, 2])) = true := by native_decide

/-- **★ The trace matrix is `[[2, x], [x, x² + 2x³]]`** (`native_decide`): the `2×2` Gram matrix of the
trace form on `[1, y]` for the non-radical curve has entries `Tr(1·1) = 2`, `Tr(1·y) = Tr(y·1) = x`,
`Tr(y·y) = x² + 2x³`. Checked entrywise by `CField.isZero` of each entry minus its expected `ℚ(x)`
value. THE GENERAL TRACE MATRIX COMPUTES. -/
theorem afNonRad_traceMatrix_entries :
    let T := traceMatrix afNonRadF (powerBasis afNonRadF)
    (CField.isZero (CField.sub ((T.getD 0 []).getD 0 CField.zero) (qxOfNum [2]))
      && CField.isZero (CField.sub ((T.getD 0 []).getD 1 CField.zero) (qxOfNum [0, 1]))
      && CField.isZero (CField.sub ((T.getD 1 []).getD 0 CField.zero) (qxOfNum [0, 1]))
      && CField.isZero (CField.sub ((T.getD 1 []).getD 1 CField.zero) (qxOfNum [0, 0, 1, 2])))
      = true := by native_decide

/-- **★ The discriminant is `x² + 4x³`** (`native_decide`): `det[Tr(ωᵢωⱼ)] = 2(x² + 2x³) − x·x =
x² + 4x³ = a₁² − 4a₀` for the non-radical curve `y² − xy − x³`, the `ℚ(x)` value `x² + 4x³`. Checked by
`CField.isZero` of `discriminant f − (x² + 4x³)`. THE GENERAL DISCRIMINANT COMPUTES. -/
theorem afNonRad_discriminant_eq :
    CField.isZero (CField.sub (discriminant afNonRadF) (qxOfNum [0, 0, 1, 4])) = true := by
  native_decide

/-- **★ The discriminant equals `± Resultant(f, f')`** (`native_decide`): the trace-matrix determinant
`discriminant f` and the resultant `Res(f, f') = cresultantG f f'` (eliminating `y`, `f' = 2y − x`)
agree **up to sign** — `discriminant f + discResultant f = 0`, i.e. `Res(f, f') = −disc(f)`, the expected
`(−1)^{n(n−1)/2} = −1` sign flip for `n = 2`. The two independent computations of the discriminant
cross-check (`CField.isZero` of `discriminant f + discResultant f`). THE TRACE-MATRIX DISCRIMINANT AND
THE RESULTANT AGREE. -/
theorem afNonRad_discriminant_eq_neg_resultant :
    CField.isZero (CField.add (discriminant afNonRadF) (discResultant afNonRadF)) = true := by
  native_decide

/-! ### ★ The trigonal curve `f = y³ + x·y + x` over `ℚ(x)` (`native_decide`, `n = 3`)

A genuinely cubic non-radical curve: `α = ℚ(x)`, `n = 3`, `f(y) = y³ + x·y + x` (`a₂ = 0`, `a₁ = x`,
`a₀ = x`). The basis is `[1, y, y²]`; `y³ ≡ −x·y − x (mod f)`.

* `Tr(1) = 3` (the `3×3` identity).
* `Tr(y) = −a₂ = 0` (the `y²` coefficient of `f` is `0` — so this particular cubic has `Tr(y) = 0`, but
  it is *not* a radical: `Tr(y²)` and the discriminant are non-radical). `Tr(y²) = a₂² − 2a₁ = −2x`.
* The discriminant of `y³ + py + q` is `−4p³ − 27q² = −4x³ − 27x²`, and equals `± Res(f, f')`. -/

/-- The trigonal curve `f = y³ + x·y + x ∈ ℚ(x)[y]` (`a₀ = x`, `a₁ = x`, `a₂ = 0`, monic), the `CPolyG
(QFunNZG ℚ)` `[x, x, 0, 1]`. -/
def afTrigF : CPolyG (QFunNZG ℚ) :=
  [qxOfNum [0, 1], qxOfNum [0, 1], CField.zero, CField.one]

/-- **`Tr(1) = 3` on the trigonal curve** (`native_decide`): the trace of `1` is `n = 3` (the `3×3`
identity `M₁`), the `ℚ(x)` constant `3`. -/
theorem afTrig_trace_one_eq_three :
    CField.isZero (CField.sub (trace afTrigF [CField.one]) (qxOfNum [3])) = true := by native_decide

/-- **`Tr(y²) = −2x` on the trigonal curve** (`native_decide`): the Newton power-sum `Tr(y²) = a₂² − 2a₁
= −2x` for `f = y³ + xy + x` (`a₂ = 0`, `a₁ = x`), the `ℚ(x)` value `−2x`. A non-radical trace value (the
`y²` power sum), computed via the `3×3` multiplication matrix `M_{y²}`. -/
theorem afTrig_trace_ysq :
    CField.isZero (CField.sub (trace afTrigF (afMul afTrigF (afBasisElem 1) (afBasisElem 1)))
      (qxOfNum [0, -2])) = true := by native_decide

/-- **★ The trigonal discriminant is `−4x³ − 27x²`** (`native_decide`): `det[Tr(ωᵢωⱼ)]` for the `3×3`
power basis of `y³ + xy + x` is the depressed-cubic discriminant `−4p³ − 27q² = −4x³ − 27x²` (`p = q =
x`), the `ℚ(x)` value `−4x³ − 27x²`. Checked by `CField.isZero` of `discriminant f − (−4x³ − 27x²)`. THE
GENERAL DISCRIMINANT COMPUTES ON A CUBIC (`n = 3`) CURVE via the `3×3` trace-matrix Laplace determinant. -/
theorem afTrig_discriminant_eq :
    CField.isZero (CField.sub (discriminant afTrigF) (qxOfNum [0, 0, -27, -4])) = true := by
  native_decide

/-- **★ The trigonal discriminant equals `± Resultant(f, f')`** (`native_decide`): the `3×3`
trace-matrix determinant `discriminant f` and `Res(f, f') = cresultantG f f'` (eliminating `y`,
`f' = 3y² + x`) agree **up to sign** — `discriminant f + discResultant f = 0`, i.e.
`Res(f, f') = −disc(f)` (the `(−1)^{n(n−1)/2} = (−1)³ = −1` sign for `n = 3`). Checked by `CField.isZero`
of `discriminant f + discResultant f`. THE CUBIC TRACE-MATRIX DISCRIMINANT CROSS-CHECKS AGAINST THE
RESULTANT. -/
theorem afTrig_discriminant_eq_resultant :
    CField.isZero (CField.add (discriminant afTrigF) (discResultant afTrigF)) = true := by
  native_decide

/-! ### Conservativity: on a RADICAL curve `f = y² − ρ`, `Tr(y) = 0` (`native_decide`)

The general carrier must agree with the radical carrier `RadExt` on the radical special case. For
`f = y² − ρ` (here `ρ = x³ + 1`, the `RadExt` worked example), `a₁ = 0`, so `Tr(y) = −a₁ = 0` — matching
the radical fact `Tr(y) = 0` (a radical's generator is traceless: `y` and `−y` are conjugate). This
confirms `afMul`/`trace` are a strict generalization of `radMul`/the radical structure. -/

/-- The radical curve `f = y² − (x³ + 1) ∈ ℚ(x)[y]` (`a₁ = 0`, `a₀ = −(x³+1)`, monic), the `CPolyG
(QFunNZG ℚ)` `[−(x³+1), 0, 1]` — the `ComputableRadicalExtension` worked example `y = √(x³+1)`, now as a
general-carrier `afMul` curve. -/
def afRadF : CPolyG (QFunNZG ℚ) :=
  [qxOfNum [-1, 0, 0, -1], CField.zero, CField.one]

/-- **★ `Tr(y) = 0` on the radical curve** (conservativity, `native_decide`): for `f = y² − (x³+1)` the
general trace `trace f y` is `0 = −a₁` (the `y¹` coefficient of `f` vanishes), matching the `RadExt`
fact `Tr(y) = 0` — a radical generator is traceless. The general carrier `afMul`/`trace` agrees with the
radical carrier on the radical case, so it is a strict generalization. Checked by `CField.isZero` of
`trace f y`. -/
theorem afRad_trace_y_eq_zero :
    CField.isZero (trace afRadF (afBasisElem 1)) = true := by native_decide

/-- **`afMul` agrees with the radical relation `y² = ρ`** (`native_decide`): `afMul f y y mod f = ρ =
x³ + 1` for `f = y² − ρ` — the general Euclidean reduction `cmodWf · f` reproduces the radical fold
`y² → ρ` (cf. `RadElem.radGen_sq_eq_radicand`). Checked by `cisZeroG` of `afMul f y y − [ρ]`. -/
theorem afRad_y_sq_eq_radicand :
    cisZeroG (csubG (afMul afRadF (afBasisElem 1) (afBasisElem 1)) [qxOfNum [1, 0, 0, 1]])
      = true := by native_decide

/-! ### Ring sanity on the general carrier (`native_decide`) -/

/-- **`y · 1 = y` on the non-radical curve** (`native_decide`): `afMul f y 1 = y` — the multiplicative
identity holds in `ℚ(x)[y]/(f)` (the `mod f` reduction is a no-op below degree `n = 2`). -/
theorem afNonRad_mul_one :
    cisZeroG (csubG (afMul afNonRadF afNonRadY [CField.one]) afNonRadY) = true := by native_decide

/-- **`y · y² = y³ ≡ x²·y + … (mod f)` on the trigonal curve associativity** (`native_decide`):
`afMul f y (afMul f y y) = afMul f (afMul f y y) y` — multiplication in `ℚ(x)[y]/(y³+xy+x)` is
associative (both reduce `y³ ≡ −xy − x`). A general-carrier ring law on the cubic curve. -/
theorem afTrig_mul_assoc :
    cisZeroG (csubG
        (afMul afTrigF (afBasisElem 1) (afMul afTrigF (afBasisElem 1) (afBasisElem 1)))
        (afMul afTrigF (afMul afTrigF (afBasisElem 1) (afBasisElem 1)) (afBasisElem 1)))
      = true := by native_decide

/-! ### The NEXT pieces: p-trace-radical → idealizer → Round-2 integral basis (Trager Ch. 2)

With the general carrier `α[y]/(f)`, the trace `Tr`, the trace matrix, and the discriminant in hand
(plus `hermiteRowReduce` over `K[x]`), the remaining Ford–Zassenhaus Round-2 steps are:

1. **Bad primes.** Factor the squarefree part of `discriminant f` (`= ± discResultant f`) over `K[x]`.
   Each irreducible factor `p` is a prime where the equation order `O = K[x][y]/(f)` may be non-maximal;
   the maximal order (integral basis) differs from `O` only at these `p`. (`discriminant`/`discResultant`
   here are the inputs; the squarefree-factorization is the engine's `csquarefree*`.)

2. **The p-trace-radical** `I_p = { z ∈ O : Tr(z·O) ⊆ p·K[x] }` (the radical of `p·O`, char `0`
   Ford–Zassenhaus form). Build the `n×n` matrix `M` whose rows are the traces `Tr(ωᵢ·ωⱼ)` **mod p**
   (entries of `traceMatrix f` reduced mod `p`); the p-trace-radical is the solution lattice
   `{ ū : M·ū ≡ 0 (mod p) }`, computed as the kernel of `M mod p` by **`hermiteRowReduce`** over `K[x]`
   (the just-landed primitive — triangularize, read the null rows). `I_p ⊇ p·O` with `I_p/pO` the kernel.

3. **The idealizer (one Round-2 step).** The enlarged order is the *idealizer*
   `O' = (I_p : I_p) = { z ∈ K(x,y) : z·I_p ⊆ I_p }`. Represent `I_p` by a `K[x]`-basis (Hermite normal
   form of its generators), form the multiplication matrices `multMatrix f ωₖ` of the basis against
   `I_p`, stack them, and solve `z·I_p ⊆ I_p` again by `hermiteRowReduce` — a Hermite/kernel solve. `O'`
   is a strictly larger order whenever `O` was non-maximal at `p`.

4. **Iterate** steps 2–3 at each bad prime `p` until `O' = O` (the order stabilizes): the result is the
   **maximal order** `O_K(x,y)`, whose `K[x]`-basis is the **integral basis** of the curve. This is the
   Round-2 algorithm; the integral basis is the denominator data the algebraic Hermite reduction (the
   genus-`g` analogue of `cHermiteReduce`) and the divisor/logarithmic-part machinery consume.

Every step is `multMatrix`/`trace`/`traceMatrix`/`discriminant` (this file) + `hermiteRowReduce`
(`ComputableHermiteNormalForm`) + squarefree factorization (the engine) — the primitives are all in
place; what remains is the orchestration loop (steps 1–4) and its correctness. -/

/-! ### `#print axioms` — does the engine have the general algebraic-function-field carrier?

Each validation carries the standard `[propext, Classical.choice, Quot.sound]` plus the `native_decide`
compiler axiom — no `sorry`, no extra axiom. **The engine now has the general algebraic-function-field
carrier `K(x, y) = K(x)[y]/(f)` for arbitrary monic `f`, with the trace map, the trace matrix, and the
discriminant** (cross-checked against `Resultant(f, f')`) — the Round-2 integral-basis inputs for
arbitrary plane curves, beyond the radical `yⁿ = ρ` special case. Validated on the non-radical
`y² − xy − x³` (trace `Tr(y) = x ≠ 0`, discriminant `x² + 4x³`), the trigonal `y³ + xy + x` (discriminant
`−4x³ − 27x²`, `n = 3`), and conservatively on the radical `y² − (x³+1)` (`Tr(y) = 0`, matching
`RadExt`). -/

-- The non-radical curve `y² − xy − x³`: nonzero trace, trace matrix, discriminant, resultant cross-check.
#print axioms afNonRad_trace_y_eq_x
#print axioms afNonRad_traceMatrix_entries
#print axioms afNonRad_discriminant_eq
#print axioms afNonRad_discriminant_eq_neg_resultant

-- The trigonal cubic curve `y³ + xy + x` (`n = 3`): discriminant and resultant cross-check.
#print axioms afTrig_discriminant_eq
#print axioms afTrig_discriminant_eq_resultant

-- Conservativity on the radical curve `y² − (x³+1)`: `Tr(y) = 0`, agreeing with `RadExt`.
#print axioms afRad_trace_y_eq_zero
#print axioms afRad_y_sq_eq_radicand

end DeepWiki.SymbolicIntegration
