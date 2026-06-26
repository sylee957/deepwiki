import DeepWiki.SymbolicIntegration.ComputableAlgFunctionField
import DeepWiki.SymbolicIntegration.ComputableIntegralBasisFull

/-! # The GENERAL derivation on `K(x, y) = K(x)[y]/(f)` for an arbitrary monic curve, and a genus-0
NON-HYPERELLIPTIC integral (Trager, *Integration of Algebraic Functions*, Ch. 4 §2 "Algebraic functions",
p. 43–50)

`ComputableRadicalExtension` carries the derivation `radDeriv n ρ` on the **radical** carrier `RadExt`
(`yⁿ = ρ`), which is **diagonal** — Trager's `(ρ/y)' = (ρ'/(nρ))·y` insight — and works for the
hyperelliptic curve `y² = ρ` (the rational part is realized through it in
`ComputableGeneralRationalPart`). But the **general** carrier `K(x)[y]/(f)` (`afMul`/`afReduce`/`trace` in
`ComputableAlgFunctionField`), for an arbitrary monic `f(x, y) = 0` of degree `n` in `y`, has **no**
`radDeriv`: for a NON-radical (in particular non-hyperelliptic) curve the derivation is **not** diagonal,
so it must be built from the implicit-function-theorem total derivative.

This file builds that **general derivation `afDeriv f`** on `K(x)[y]/(f)`. For
`u = Σᵢ aᵢ(x)·yⁱ` (coordinates `aᵢ ∈ K(x)`), the product rule gives
`D(u) = Σᵢ aᵢ'·yⁱ + (Σᵢ aᵢ·i·yⁱ⁻¹)·y'`, where the implicit derivative is `y' = −f_x / f_y`
(`f_x = ∂f/∂x`, `f_y = ∂f/∂y`), reduced `mod f` in the field `K(x, y)`. Since `f` is **separable**
(`gcd(f, f_y) = 1`), `f_y` is a **unit** of `K(x)[y]/(f)`: its inverse `f_y⁻¹ ≡ s (mod f)` is the Bézout
cofactor `s·f_y + t·f = 1`, computed by the generic diophantine solver `cdiophantineG f_y f [1]`. So
`y' = afReduce f (−f_x · f_y⁻¹)`. This generalizes the hyperelliptic `radDeriv` (where `f = y² − ρ`,
`f_y = 2y`, `f_x = −ρ'`, so `y' = ρ'/(2y)` — the diagonal rule), and it is `radDeriv`-**conservative**:
on `f = y² − ρ`, `afDeriv` agrees with `radDeriv 2 ρ`.

* **`afFy`/`afFx`** — the partial derivatives of the curve `f` (a `y`-polynomial with `K(x)` coefficients):
  `afFy = cderivG f` (the formal `y`-derivative), `afFx = f.map CDiffField.cderiv` (the base `d/dx` on each
  `K(x)` coefficient).
* **`afYprime f`** — the implicit derivative `y' = −f_x · f_y⁻¹ mod f`, inverting `f_y` in the field via
  `cdiophantineG`.
* **`afDeriv f u`** — the general derivation: `afReduce f (u.map CDiffField.cderiv + cderivG u · y')`.

**Validations** (`native_decide`):
* **★ The genus-0 NON-HYPERELLIPTIC integral `∫ y dx = (3/5)·x·y` on the cuspidal cubic `y³ = x²`**
  (`f = y³ − x²`, degree 3 in `y`, genus 0, `y = x^{2/3}`, `∫ x^{2/3} dx = (3/5)x^{5/3} = (3/5)x·y`):
  `afDeriv (y³ − x²) ((3/5)x·y) = y`, validated through the GENERAL derivation. Here `f_y = 3y²`,
  `f_x = −2x`, `y' = 2x/(3y²) = (2/(3x))·y`, and `D((3/5)xy) = (3/5)(y + x·y') = (3/5)(y + (2/3)y) = y`.
* **A second non-hyperelliptic target `∫ y² dx = (3/7)·x·y²` on `y³ = x²`** (`y² = x^{4/3}`,
  `∫ x^{4/3} dx = (3/7)x^{7/3} = (3/7)x·x^{4/3} = (3/7)x·y²`): `afDeriv (y³ − x²) ((3/7)x·y²) = y²`.
* **`afDeriv f 1 = 0`** (a constant has zero derivative) and **`afDeriv (y² − ρ) = radDeriv 2 ρ`**
  conservativity on the hyperelliptic carrier.

**The engine now has the GENERAL carrier derivation `afDeriv`** (beyond the hyperelliptic `radDeriv`) and
integrates genus-0 NON-hyperelliptic curves (the cuspidal cubic `y³ = x²`). The next pieces — the coupled
eq.-11 Hermite reduction (Cramer/Bézout over the integral basis, the non-diagonal `Mᵢⱼ`) producing the
rational part `v` from the integrand, and the genus-`g > 0` logarithmic part — are documented at the end. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α]

/-! ### The partial derivatives of the curve `f` (`afFy`, `afFx`)

For a monic curve `f(x, y) = yⁿ + a_{n−1}(x)·yⁿ⁻¹ + … + a₀(x)` represented as a `CPolyG α = α[y]`
(`α = K(x)`), the two partial derivatives are:

* `f_y = ∂f/∂y` — the **formal `y`-derivative** of the polynomial: `cderivG f` (drop the constant
  coefficient, scale the `k`-th remaining coefficient by `k`). Needs only `[CField α]`.
* `f_x = ∂f/∂x` — the **base derivation `d/dx` applied to each coefficient**: `f.map CDiffField.cderiv`
  (the `K(x)`-derivation `CDiffField.cderiv` on every `aᵢ`, no `y`-power change). Needs `[CDiffField α]`. -/

/-- **`∂f/∂y` of the curve `f`** `afFy f = cderivG f` — the formal `y`-derivative of `f` as a polynomial in
`y` (`α = K(x)` coefficients): `f_y = n·yⁿ⁻¹ + (n−1)a_{n−1}yⁿ⁻² + …`. For a separable `f` this is a **unit**
of `K(x)[y]/(f)` (`gcd(f, f_y) = 1`). Needs only `[CField α]`. -/
def afFy (f : CPolyG α) : CPolyG α := cderivG f

/-- **`∂f/∂x` of the curve `f`** `afFx f = f.map CDiffField.cderiv` — the base derivation `d/dx` applied to
each `K(x)` coefficient of `f` (no `y`-power change, since `∂(aᵢ yⁱ)/∂x = aᵢ' yⁱ`). For `f = yⁿ + Σ aᵢ yⁱ`
this is `Σ aᵢ' yⁱ` (the `yⁿ` term has constant coefficient `1`, so `1' = 0`). Needs `[CDiffField α]`. -/
def afFx (f : CPolyG α) : CPolyG α := (f : List α).map CDiffField.cderiv

/-! ### The implicit derivative `y' = −f_x / f_y mod f` (`afYprime`)

Differentiating `f(x, y) = 0` totally gives `f_x + f_y·y' = 0`, so `y' = −f_x / f_y`. Since `f` is
separable, `gcd(f, f_y) = 1`, hence `f_y` is invertible in `K(x)[y]/(f)`: the Bézout identity
`s·f_y + t·f = 1` makes `f_y⁻¹ ≡ s (mod f)`, and `s` is exactly the first cofactor of
`cdiophantineG fuel f_y f [1]` (solving `b·f_y + c·f = 1` with `deg b < deg f`). Then
`y' = afReduce f (−f_x · s)`, a degree-`< n` representative. -/

/-- **`f_y⁻¹ mod f`** `afFyInv fuel f = ` the inverse of `∂f/∂y` in the field `K(x)[y]/(f)`: the first
Bézout cofactor `s` of `s·f_y + t·f = 1` (`cdiophantineG fuel (afFy f) f [1]`), valid because `f` is
separable (`gcd(f, f_y) = 1`, so `f_y` is a unit). Degree `< deg f`. -/
def afFyInv (fuel : ℕ) (f : CPolyG α) : CPolyG α :=
  (cdiophantineG fuel (afFy f) f [CField.one]).1

/-- **The implicit derivative `y' = −f_x · f_y⁻¹ mod f`** `afYprime fuel f`: from the total derivative
`f_x + f_y·y' = 0` of the curve `f(x, y) = 0`, the field element `y' = −(∂f/∂x)·(∂f/∂y)⁻¹` reduced `mod f`
(`afReduce f (cmulG (cnegG (afFx f)) (afFyInv fuel f))`). Generalizes the hyperelliptic diagonal rule
`y' = ρ'/(2y)` (`f = y² − ρ`, `f_y = 2y`, `f_x = −ρ'`); for `f = y³ − x²` it gives `y' = 2x/(3y²) =
(2/(3x))·y`. Fuel `≥ deg f` is safe. -/
def afYprime (fuel : ℕ) (f : CPolyG α) : CPolyG α :=
  afReduce f (cmulG (cnegG (afFx f)) (afFyInv fuel f))

/-! ### The general derivation `afDeriv` on `K(x)[y]/(f)`

For `u = Σᵢ aᵢ(x)·yⁱ ∈ K(x)[y]/(f)` (coordinates `aᵢ ∈ K(x)`), the product rule gives
`D(u) = Σᵢ aᵢ'·yⁱ + (Σᵢ aᵢ·i·yⁱ⁻¹)·y'`. The first sum is `u.map CDiffField.cderiv` (the base `d/dx` on
each coordinate, no `y`-power change). The second factor `Σᵢ aᵢ·i·yⁱ⁻¹` is the **formal `y`-derivative**
`cderivG u`. So `D(u) = afReduce f (u.map CDiffField.cderiv + cderivG u · y')`. This is the general
algebraic-function derivation; on a radical `f = yⁿ − ρ` it specializes to the diagonal `radDeriv n ρ`
(conservativity below). -/

/-- **The GENERAL derivation on `K(x)[y]/(f)`** `afDeriv fuel f u = D(u)` for `u = Σᵢ aᵢ·yⁱ`:
`afReduce f ((u.map CDiffField.cderiv) + (cderivG u)·(afYprime fuel f))`, i.e. the product rule
`D(u) = Σᵢ aᵢ'·yⁱ + (Σᵢ aᵢ·i·yⁱ⁻¹)·y'` with the implicit derivative `y' = −f_x/f_y mod f`. Generalizes
the hyperelliptic `radDeriv` (the diagonal `(ρ/y)'` rule) to an **arbitrary** monic curve `f` —
non-radical, non-hyperelliptic plane curves included. Needs `[CField α] [CDiffField α]`, so it
`native_decide`s; fuel `≥ deg f` for the `f_y`-inversion. -/
def afDeriv (fuel : ℕ) (f u : CPolyG α) : CPolyG α :=
  afReduce f (caddG ((u : List α).map CDiffField.cderiv) (cmulG (cderivG u) (afYprime fuel f)))

end CPolyG

/-! ### ★ The cuspidal cubic `y³ = x²` over `ℚ(x)` (genus 0, NON-hyperelliptic): the general derivation

`α = QFunNZG ℚ ≅ ℚ(x)`, the curve `f = y³ − x²` (degree `n = 3` in `y`, **non-hyperelliptic** — degree
`> 2`). It is the cuspidal cubic: `y = x^{2/3}` (a single branch, genus 0). The carrier `K(x)[y]/(f)`
has the power basis `[1, y, y²]`; `y³ ≡ x² (mod f)`. The implicit derivative:
`f_y = 3y²`, `f_x = −2x`, so `y' = −f_x/f_y = 2x/(3y²)`, and `(3y²)⁻¹ ≡ y/(3x²) (mod y³−x²)` (since
`3y²·y/(3x²) = y³/x² = x²/x² = 1`), giving `y' = 2x·y/(3x²) = (2/(3x))·y`. -/

open CPolyG

/-- The cuspidal cubic `f = y³ − x² ∈ ℚ(x)[y]` (`a₀ = −x²`, `a₁ = a₂ = 0`, monic, degree `n = 3`), the
`CPolyG (QFunNZG ℚ)` `[−x², 0, 0, 1]`. **Non-hyperelliptic** (degree `> 2`) and genus 0 (the cusp
`y = x^{2/3}`). The general derivation `afDeriv` integrates `∫ y dx = (3/5)x·y` on it. -/
def gcuspCubicF : CPolyG (QFunNZG ℚ) :=
  [qxOfNum [0, 0, -1], CField.zero, CField.zero, CField.one]

/-- The generator `y` of `ℚ(x)[y]/(y³ − x²)` (`afBasisElem 1 = [0, 1]`). -/
def gcuspCubicY : CPolyG (QFunNZG ℚ) := afBasisElem 1

/-- **★ The implicit derivative is `y' = (2/(3x))·y` on the cuspidal cubic** (`native_decide`):
`afYprime (y³ − x²) = 2x·(3y²)⁻¹ mod f = (2/(3x))·y` (the field-inverted `f_y = 3y²` gives `(3y²)⁻¹ =
y/(3x²)`, so `y' = 2x·y/(3x²) = (2/(3x))·y`). Checked by `cisZeroG` of `y' − [0, 2/(3x)]`. THE IMPLICIT
DERIVATIVE `y' = −f_x/f_y` COMPUTES IN THE FIELD `K(x)[y]/(f)` FOR A NON-HYPERELLIPTIC CURVE — the
`f_y`-inversion via `cdiophantineG` succeeds (`f` separable). -/
theorem gcuspCubic_yprime_eq :
    cisZeroG (csubG (afYprime 8 gcuspCubicF)
      [CField.zero, qxOfFrac [2] [0, 3] (by decide)]) = true := by native_decide

/-- **★★ The genus-0 NON-HYPERELLIPTIC integral `∫ y dx = (3/5)·x·y` on `y³ = x²`** (`native_decide`):
the GENERAL derivation `afDeriv (y³ − x²)` of the rational part `v = (3/5)·x·y = [0, (3/5)x]` equals the
integrand `y = [0, 1]` — `D((3/5)xy) = (3/5)(y + x·y') = (3/5)(y + x·(2/(3x))y) = (3/5)(y + (2/3)y) =
(3/5)(5/3)y = y`. Checked by `cisZeroG` of `afDeriv f v − y` over `ℚ(x)`. **THE GENUS-0 NON-HYPERELLIPTIC
INTEGRAL, VALIDATED THROUGH THE GENERAL CARRIER DERIVATION** — `∫ y dx = (3/5)xy` on the cuspidal cubic
`y³ = x²`, beyond the hyperelliptic `radDeriv`. -/
theorem gcuspCubic_intY :
    cisZeroG (csubG (afDeriv 8 gcuspCubicF [CField.zero, qxOfNum [0, 3/5]]) gcuspCubicY)
      = true := by native_decide

/-! ### A second non-hyperelliptic target: `∫ y² dx = (3/7)·x·y²` on `y³ = x²` (`native_decide`)

The integrand `y² = (x^{2/3})² = x^{4/3}`, so `∫ y² dx = (3/7)x^{7/3} = (3/7)x·x^{4/3} = (3/7)x·y²`. The
rational part is `v = (3/7)x·y² = [0, 0, (3/7)x]` (a genuine `y²`-component, unlike the first target's
pure-`y` part). The general derivation checks it: `D((3/7)x·y²) = (3/7)(y² + x·2y·y') = (3/7)(y² +
2x·y·(2/(3x))·y) = (3/7)(y² + (4/3)y²) = (3/7)(7/3)y² = y²` (using `y' = (2/(3x))y`, so
`2x·y·(2/(3x))·y = (4/3)y²`). -/

/-- The integrand `y²` of `∫ y² dx` on `y³ = x²` (`afBasisElem 2 = [0, 0, 1]`). -/
def gcuspCubicYsq : CPolyG (QFunNZG ℚ) := afBasisElem 2

/-- **★ The second genus-0 NON-HYPERELLIPTIC integral `∫ y² dx = (3/7)·x·y²` on `y³ = x²`**
(`native_decide`): the GENERAL derivation `afDeriv (y³ − x²)` of `v = (3/7)x·y² = [0, 0, (3/7)x]` equals
the integrand `y² = [0, 0, 1]` — `D((3/7)x y²) = (3/7)(y² + x·2y·y') = (3/7)(y² + 2xy·(2/(3x))y) =
(3/7)(y² + (4/3)y²) = (3/7)(7/3)y² = y²`. Checked by `cisZeroG` of `afDeriv f v − y²` over `ℚ(x)`. A
second non-hyperelliptic integral through the general carrier derivation, this one with a `y²`
component. -/
theorem gcuspCubic_intYsq :
    cisZeroG (csubG (afDeriv 8 gcuspCubicF [CField.zero, CField.zero, qxOfNum [0, 3/7]]) gcuspCubicYsq)
      = true := by native_decide

/-- **`afDeriv (y³ − x²) 1 = 0`: a constant has zero derivative** (`native_decide`): the general
derivation annihilates the constant `1 = [1]` (`D(1) = 1' + (cderivG [1])·y' = 0 + 0·y' = 0`). Checked by
`cisZeroG (afDeriv f [1])`. A derivation sanity law on the non-hyperelliptic carrier. -/
theorem gcuspCubic_deriv_one_eq_zero :
    cisZeroG (afDeriv 8 gcuspCubicF [CField.one]) = true := by native_decide

/-- **`afDeriv (y³ − x²) x = 1`: `D(x) = 1`** (`native_decide`): the general derivation on the constant-in-`y`
element `x = [x]` (a `K(x)`-scalar) is the base `d/dx`-derivative `x' = 1` (`D([x]) = [x'] + (cderivG
[x])·y' = [1] + 0·y' = [1]`). Checked by `cisZeroG (afDeriv f [x] − [1])`. The general derivation restricts
to the base `d/dx` on `K(x)`-scalars. -/
theorem gcuspCubic_deriv_x_eq_one :
    cisZeroG (csubG (afDeriv 8 gcuspCubicF [qxOfNum [0, 1]]) [CField.one]) = true := by native_decide

/-! ### ★ `afDeriv` is `radDeriv`-conservative on the hyperelliptic carrier `y² = ρ` (`native_decide`)

The general derivation must agree with the diagonal `radDeriv 2 ρ` on a hyperelliptic (radical, `n = 2`)
curve `f = y² − ρ`. For `f = y² − (x³ + 1)` (the `ComputableRadicalExtension` worked example `y =
√(x³+1)`): `f_y = 2y`, `f_x = −(x³+1)' = −3x²`, so `y' = −f_x/f_y = 3x²/(2y) = (3x²/(2(x³+1)))·y`
(`(2y)⁻¹ = y/(2(x³+1))` since `2y·y = 2y² = 2(x³+1)`), which is exactly `radDeriv`'s diagonal multiplier
`ℓ = ρ'/(2ρ) = 3x²/(2(x³+1))`. We check `afDeriv (y² − ρ) u = (radDeriv 2 ρ u as a free poly)` on the
generator `y` and on a mixed element `g₀ + g₁y`: the general derivation, with no diagonality assumption,
reproduces the radical derivation. -/

/-- The hyperelliptic radical curve `f = y² − (x³ + 1) ∈ ℚ(x)[y]` (`a₁ = 0`, `a₀ = −(x³+1)`, monic), the
`CPolyG (QFunNZG ℚ)` `[−(x³+1), 0, 1]` — the `ComputableRadicalExtension`/`ComputableAlgFunctionField`
worked example `y = √(x³+1)`, now a curve for the general `afDeriv` conservativity check. -/
def gcCarF : CPolyG (QFunNZG ℚ) :=
  [qxOfNum [-1, 0, 0, -1], CField.zero, CField.one]

/-- The radicand `ρ = x³ + 1 ∈ ℚ(x)` of `y² = ρ` (for `radDeriv 2 ρ`). -/
def gcCarRho : QFunNZG ℚ := qxOfNum [1, 0, 0, 1]

/-- **★ `afDeriv (y² − ρ) y = radDeriv 2 ρ y` (conservativity on the generator)** (`native_decide`): the
GENERAL derivation of `y = [0, 1]` on the hyperelliptic curve `y² − (x³+1)` equals the **diagonal**
`radDeriv 2 (x³+1)` of `y` — both give `(3x²/(2(x³+1)))·y` (the implicit `y' = −f_x/f_y` reduces to the
radical's diagonal `ℓ·y`). Checked by `cisZeroG` of the difference over `ℚ(x)`. THE GENERAL `afDeriv`
SPECIALIZES TO THE HYPERELLIPTIC `radDeriv` — a strict generalization. -/
theorem gcCar_afDeriv_y_eq_radDeriv :
    cisZeroG (csubG (afDeriv 8 gcCarF (afBasisElem 1))
      (RadElem.radDeriv 2 gcCarRho (RadElem.radGen : RadElem (QFunNZG ℚ)))) = true := by native_decide

/-- A mixed hyperelliptic element `g = g₀ + g₁y = (x³+1) + 3x²·y` (`g₀ = ρ`, `g₁ = ρ'`), the
conservativity test integrand over `y² − (x³+1)`. -/
def gcCarMixed : CPolyG (QFunNZG ℚ) := [qxOfNum [1, 0, 0, 1], qxOfNum [0, 0, 3]]

/-- **★ `afDeriv (y² − ρ) (g₀ + g₁y) = radDeriv 2 ρ (g₀ + g₁y)` (conservativity on a mixed element)**
(`native_decide`): the GENERAL derivation of `g = (x³+1) + 3x²·y` on the hyperelliptic curve equals the
diagonal `radDeriv 2 (x³+1)` of the same element — the general carrier derivation reproduces the radical
derivation on a full (non-pure-power) element, with no diagonality assumption. Checked by `cisZeroG` of
the difference over `ℚ(x)`. THE CONSERVATIVITY HOLDS ON A MIXED ELEMENT, not only the generator. -/
theorem gcCar_afDeriv_mixed_eq_radDeriv :
    cisZeroG (csubG (afDeriv 8 gcCarF gcCarMixed)
      (RadElem.radDeriv 2 gcCarRho (gcCarMixed : RadElem (QFunNZG ℚ)))) = true := by native_decide

/-! ### The NEXT pieces: the coupled eq.-11 Hermite reduction, and the genus-`g > 0` log part

`afDeriv` is the GENERAL carrier derivation on `K(x)[y]/(f)` for an arbitrary monic curve — built from the
implicit derivative `y' = −f_x/f_y` (field-inverted `f_y`), beyond the hyperelliptic diagonal `radDeriv`.
The validated genus-0 non-hyperelliptic integrals (`∫ y dx = (3/5)xy`, `∫ y² dx = (3/7)xy²` on the
cuspidal cubic `y³ = x²`) check the **forward** direction: given the rational part `v`, `afDeriv f v` =
integrand. Two pieces remain to close the loop (produce `v` from the integrand, and handle genus > 0):

1. **The coupled eq.-11 Hermite reduction (Trager Ch. 4 §2, p. 46–48).** To **derive** `v` from an
   integrand `Σ Aᵢ wᵢ / D` over the integral basis `[w₁,…,wₙ]` (= `integralBasis f`,
   `ComputableIntegralBasisFull`), Trager's algorithm squarefree-factors `D`, sets `V = D_{k+1}`, `U =
   D/V`, and solves the **coupled** congruence system (eq. 11)
   `Aᵢ ≡ −kUV'Bᵢ + T·Σⱼ BⱼMⱼᵢ (mod V)`, where `E·wᵢ' = Σⱼ Mᵢⱼ wⱼ` (`E` the lcm denominator of the basis
   derivatives `wᵢ'`, `TE = UV`). The basis derivatives `wᵢ' = afDeriv f wᵢ` (THIS file's general
   derivation) supply the structure matrix `Mᵢⱼ`; for a NON-diagonal `Mᵢⱼ` (a non-hyperelliptic curve,
   `K(x, y)` not a compositum of radicals) the system is a genuine coupled `n×n` linear solve over
   `K(x)/(V)`, done by **Cramer's rule** (the determinant is coprime to `V`, p. 48) or a Bézout/`matInvG`
   solve over the residue ring. The diagonal case (`Mᵢⱼ` diagonal ⟺ hyperelliptic `y² = ρ`) collapses to
   `Aᵢ ≡ −kUV'Bᵢ (mod V)`, the `radDeriv`-validated Case-1/2/3 reduction of
   `ComputableGeneralRationalPart`. So `afDeriv` (the basis-derivative oracle) is the missing input the
   coupled reduction needs; forming `Mᵢⱼ = afDeriv f wᵢ` over the integral basis, clearing `E`, and the
   Cramer/`matInvG` solve `mod V` is the non-diagonal analogue of `radIntegrateRational`.

2. **The genus-`g > 0` logarithmic part.** After the reduction, the residual has only **simple** finite
   poles (Trager's Theorem, p. 50). For genus 0 (the cuspidal cubic here, and the hyperelliptic genus-0
   cusp `y² = x³`) the residual is empty — the rational part is the whole integral. For genus `g > 0` the
   simple-pole residual feeds the logarithmic part: its residues (`genResidueResultant`,
   `ComputableGeneralResidues`) define a **divisor**, whose `K`-multiple being **principal** (a torsion
   condition in the Jacobian, the Ch. 6 decision, done for the hyperelliptic carrier in
   `ComputableTorsionLogTerm`) is exactly when the integral is elementary. The residue → divisor → torsion
   path, now over the general carrier with `afDeriv`, is the genus-`g > 0` continuation.

The **general carrier derivation `afDeriv`** (this file) is the keystone the whole general-curve reduction
turns on: it is the basis-derivative oracle `wᵢ' = afDeriv f wᵢ` that the coupled eq.-11 system and the
divisor/log machinery consume, for an arbitrary plane curve, beyond the hyperelliptic radical case. -/

/-! ### `#print axioms` — does the engine have the GENERAL carrier derivation, and integrate genus-0
non-hyperelliptic curves?

Each validation carries the standard `[propext, Classical.choice, Quot.sound]` plus the `native_decide`
compiler axiom — **no `sorry`, no `sorryAx`, no extra axiom** (`afDeriv`/`afYprime`/`afFy`/`afFx` are
non-recursive compositions over the fuel-bounded engine: `cderivG`/`cmulG`/`caddG`/`cnegG` are
`List`-folds, `cdiophantineG`/`afReduce` are `ℕ`-fuel-bounded). **The engine now has the GENERAL carrier
derivation `afDeriv` on `K(x)[y]/(f)` for an arbitrary monic curve** — built from the implicit derivative
`y' = −f_x/f_y` (field-inverted `f_y` via `cdiophantineG`, `f` separable), beyond the hyperelliptic
diagonal `radDeriv`. It **integrates genus-0 NON-hyperelliptic curves**: `∫ y dx = (3/5)·x·y`
(`gcuspCubic_intY`) and `∫ y² dx = (3/7)·x·y²` (`gcuspCubic_intYsq`) on the cuspidal cubic `y³ = x²`
(degree 3, non-hyperelliptic, genus 0), with the implicit derivative `y' = (2/(3x))y`
(`gcuspCubic_yprime_eq`); and it is `radDeriv`-**conservative** on the hyperelliptic carrier `y² = x³+1`
(`gcCar_afDeriv_y_eq_radDeriv`, `gcCar_afDeriv_mixed_eq_radDeriv`). -/

-- ★ The implicit derivative `y' = (2/(3x))y` on the non-hyperelliptic cuspidal cubic `y³ = x²`:
#print axioms gcuspCubic_yprime_eq

-- ★★ The genus-0 NON-HYPERELLIPTIC integrals through the GENERAL derivation:
#print axioms gcuspCubic_intY
#print axioms gcuspCubic_intYsq

-- Derivation sanity on the non-hyperelliptic carrier (`D(1) = 0`, `D(x) = 1`):
#print axioms gcuspCubic_deriv_one_eq_zero
#print axioms gcuspCubic_deriv_x_eq_one

-- ★ `radDeriv`-conservativity on the hyperelliptic carrier `y² = x³+1` (generator + mixed element):
#print axioms gcCar_afDeriv_y_eq_radDeriv
#print axioms gcCar_afDeriv_mixed_eq_radDeriv

end DeepWiki.SymbolicIntegration
