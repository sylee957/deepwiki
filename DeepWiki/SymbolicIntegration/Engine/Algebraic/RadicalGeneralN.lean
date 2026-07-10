import DeepWiki.SymbolicIntegration.Engine.TranscendentalOverAlgebraic
import DeepWiki.ComputableAlgebra.GenericBezout
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.RatFunc.Degree

/-! # General-`n` radical extensions: the `nth`-root inverse and a cube-root `CField`

The carrier `RadExt α n f = α[y]/(yⁿ − f)` is `n`-generic for its ring/derivation, but its inverse
`radInv2` is honest only at `n = 2`. This file lifts the inverse to arbitrary `n` via the extended
Euclidean algorithm in `α[y]` (`radInvN`), wraps it in a fresh field carrier `RadExtN α n f`, and
exhibits the engine differentiating/multiplying/inverting over the cube root `∛(x²+1)` over `ℚ(x)`
(`y³ − (x²+1)` is irreducible since `x²+1` is not a perfect cube). The derivation laws are inherited from
the `n`-generic additivity/Leibniz results. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem

namespace RadElem

variable {α : Type*} [CField α]

/-! ### The defining modulus `yⁿ − f` and the general-`n` inverse `radInvN`

By extended Euclid: solve `s·g + t·(yⁿ − f) = 1` and reduce `s` mod `yⁿ = f`. -/

/-- The defining modulus `radModulus n f = [−f, 0, …, 0, 1] = yⁿ − f` as a `DensePoly α`. -/
def radModulus (n : ℕ) (f : α) : DensePoly α :=
  DensePoly.csub (DensePoly.cshift n [CCommRing.one]) [f]

/-- The general-`n` inverse `radInvN n f g` of `g ∈ α[y]/(yⁿ − f)` via extended Euclid: from
`cbezoutOneWf g (yⁿ − f) = (s, _)` with `s·g + t·(yⁿ − f) = 1`, the inverse is `s` reduced mod `yⁿ = f`.
The honest field inverse whenever `yⁿ − f` is irreducible. -/
def radInvN (n : ℕ) (f : α) (g : RadElem α) : RadElem α :=
  let fuel := 2 * (n + (g : List α).length) + 2
  let (s, _) := DensePoly.cbezoutOneWf g (radModulus n f)
  radReduce n f fuel s

end RadElem

/-! ### Sanity: `radInvN` inverts, and agrees with `radInv2` at `n = 2`

Over `ℚ(x)`, `n = 2`, `f = x²+1`: `radInvN` produces a genuine inverse matching `radInv2`. -/

open RadElem

/-- `radInvN` inverts at `n = 2`: over `(CFrac ℚ)[y]/(y² − (x²+1))`, `radMul 2 (x²+1) u (radInvN 2 …) = 1`
for `u = x + y`. -/
theorem radInvN_mul_self_eq_one_at_two :
    DensePoly.cisZero (DensePoly.csub (radMul 2 fullRhoArcsinh fullUxPlusY
        (radInvN 2 fullRhoArcsinh fullUxPlusY)) radOne) = true := by native_decide

/-- `radInvN` agrees with `radInv2` at `n = 2`: `radInvN 2 ρ u = radInv2 ρ u` in
`(CFrac ℚ)[y]/(y² − (x²+1))` for `u = x + y`. -/
theorem radInvN_eq_radInv2_at_two :
    DensePoly.cisZero (DensePoly.csub (radInvN 2 fullRhoArcsinh fullUxPlusY)
        (radInv2 fullRhoArcsinh fullUxPlusY)) = true := by native_decide

/-! ### The fresh carrier `RadExtN α n f` — a field for every `n` via `radInvN`

A fresh one-field structure wrapping `RadElem α` whose `inv` is `radInvN` (so it is a field for every `n`
with `yⁿ − f` irreducible), avoiding an overlapping `CField` instance on `RadExt`; all other ops match. -/

/-- The general-`n` simple-radical carrier `RadExtN α n f = α[y]/(yⁿ − f)`: a one-field structure wrapping
`RadElem α`, with `n`/`f` on the type, whose `CField` inverse is `radInvN`. `ofRadN ::`/`toRadN` are the
constructor/projection. -/
structure RadExtN (α : Type*) [CField α] (n : ℕ) (f : α) where
  /-- The underlying coefficient list `[a₀,…,a_{n−1}]` for `Σ aᵢyⁱ ∈ α[y]/(yⁿ − f)`. -/
  ofRadN ::
  /-- The radical-extension element as a `RadElem α` coefficient list. -/
  toRadN : RadElem α

namespace RadExtN

variable {α : Type*} [CField α] {n : ℕ} {f : α}

/-- **Zero** of `RadExtN α n f` — the wrapped `radZero` (`[]`). -/
def zero : RadExtN α n f := ⟨radZero⟩

/-- **One** of `RadExtN α n f` — the wrapped `radOne` (`[1]`). -/
def one : RadExtN α n f := ⟨radOne⟩

/-- **The generator `y`** of `RadExtN α n f` — the wrapped `radGen` (`[0, 1]`). -/
def gen : RadExtN α n f := ⟨radGen⟩

/-- **Addition** in `RadExtN α n f` — componentwise `DensePoly.cadd`, canonicalized to degree `< n`. -/
def add (p q : RadExtN α n f) : RadExtN α n f := ⟨RadExt.radCanon n f (DensePoly.cadd p.toRadN q.toRadN)⟩

/-- **Negation** in `RadExtN α n f` — componentwise `DensePoly.cneg`, canonicalized to degree `< n`. -/
def neg (p : RadExtN α n f) : RadExtN α n f := ⟨RadExt.radCanon n f (DensePoly.cneg p.toRadN)⟩

/-- **Multiplication** in `RadExtN α n f` — `radMul n f` (poly-multiply in `y`, reduce `yⁿ → f`),
canonicalized. -/
def mul (p q : RadExtN α n f) : RadExtN α n f := ⟨RadExt.radCanon n f (radMul n f p.toRadN q.toRadN)⟩

/-- Inverse in `RadExtN α n f`: the canonicalized extended-Euclidean `radInvN` (reduce input, then output,
to degree `< n`). -/
def inv (p : RadExtN α n f) : RadExtN α n f :=
  ⟨RadExt.radCanon n f (radInvN n f (RadExt.radCanon n f p.toRadN))⟩

/-- **Zero test** in `RadExtN α n f` — reduce `mod yⁿ = f` first, then `DensePoly.cisZero`. -/
def isZero (p : RadExtN α n f) : Bool := DensePoly.cisZero (RadExt.radCanon n f p.toRadN)

end RadExtN

/-- `CField (RadExtN α n f)`: the extension `α[y]/(yⁿ − f)` as a computable field for arbitrary `n`, with
`inv := RadExtN.inv` the extended-Euclidean `radInvN`. -/
instance instCFieldRadExtN {α : Type*} [CField α] {n : ℕ} {f : α} : CField (RadExtN α n f) where
  zero := RadExtN.zero
  one := RadExtN.one
  add := RadExtN.add
  mul := RadExtN.mul
  neg := RadExtN.neg
  inv := RadExtN.inv
  isZero := RadExtN.isZero

/-- `CDiffField (RadExtN α n f)`: the radical extension as a computable differential field, with
`cderiv := radDeriv n f` the diagonal derivation `y' = (f'/(nf))·y`. -/
instance instCDiffFieldRadExtN {α : Type*} [CField α] [CDiffField α] {n : ℕ} {f : α} :
    CDiffField (RadExtN α n f) where
  cderiv p := ⟨radDeriv n f p.toRadN⟩

/-! ### The concrete cube root `∛(x²+1)` over `ℚ(x)` and its irreducibility

`α = ℚ(x)`, `n = 3`, `f = x²+1`: `y³ − (x²+1)` is irreducible over `ℚ(x)` since `x²+1` (intDegree `2`) is
not a perfect cube, so `RadX3root = RadExtN (CFrac ℚ) 3 (x²+1)` is an honest field. -/

/-- The cube radicand `f = x² + 1 ∈ ℚ(x)` (numerator `[1, 0, 1]`), `y = ∛(x²+1)`. -/
def cubeRadicand : CFrac ℚ := CFrac.ofPoly [1, 0, 1]

/-- The cube-root field `ℚ(x)[∛(x²+1)] = RadExtN (CFrac ℚ) 3 (x²+1)`. -/
abbrev RadX3root : Type := RadExtN (CFrac ℚ) 3 cubeRadicand

/-- The cube-root generator `y = ∛(x²+1)` as an element of `RadX3root` (through `RadExtN.gen`). -/
def cubeGen : RadX3root := RadExtN.gen

/-- The diagonal multiplier `ℓ = f'/(3f) = 2x/(3(x²+1)) ∈ ℚ(x)` for `D(y) = ℓ·y`, `y = ∛(x²+1)`. -/
def cubeLogDer : CFrac ℚ := logDerRadicand 3 cubeRadicand

/-- **`1 + x² ≠ 0` in `ℚ[X]`** (it has `natDegree 2`). -/
theorem X2p1_ne_zero : (1 + X ^ 2 : ℚ[X]) ≠ 0 := by
  intro h
  have := congrArg Polynomial.natDegree h
  rw [add_comm, Polynomial.natDegree_add_eq_left_of_natDegree_lt (by simp), natDegree_X_pow] at this
  simp at this

/-- **`natDegree (1 + x²) = 2`** in `ℚ[X]` (the leading `x²` dominates the constant `1`). -/
theorem natDeg_X2p1 : (1 + X ^ 2 : ℚ[X]).natDegree = 2 := by
  rw [add_comm, Polynomial.natDegree_add_eq_left_of_natDegree_lt (by simp), natDegree_X_pow]

open DensePoly in
/-- `toK cubeRadicand = algebraMap ℚ[X] (RatFunc ℚ) (1 + x²)`: the radicand reads through the tower bridge
as the algebra-map image of `1 + x²`. -/
theorem toK_cubeRadicand :
    CFieldSpec.toK (cubeRadicand : CFrac ℚ) = algebraMap (ℚ[X]) (RatFunc ℚ) (1 + X ^ 2) := by
  show CFrac.toCFrac cubeRadicand = _
  rw [CFrac.toCFrac]
  show CFrac.am ℚ (toPoly ([1, 0, 1] : DensePoly ℚ))
      / CFrac.am ℚ (toPoly ([CCommRing.one] : DensePoly ℚ)) = _
  have h1 : toPoly ([1, 0, 1] : DensePoly ℚ) = 1 + X ^ 2 := by
    simp only [denote]
    show C (1 : ℚ) + X * (C 0 + X * (C 1 + X * 0)) = _
    simp; ring
  have h2 : toPoly ([CCommRing.one] : DensePoly ℚ) = 1 := by
    show C (CFieldSpec.toK (CCommRing.one : ℚ)) + X * 0 = 1; simp [CFieldSpec.toK_one]
  rw [h1, h2]
  show CFrac.am ℚ (1 + X ^ 2) / CFrac.am ℚ 1 = _
  rw [map_one, div_one]; rfl

/-- `x²+1` is not a cube in `ℚ(x)`: `∀ b, b³ ≠ algebraMap (1 + x²)`, since a cube has `intDegree` divisible
by `3` but `1 + x²` has `intDegree 2`. -/
theorem not_cube_X2p1 :
    ∀ b : RatFunc ℚ, b ^ 3 ≠ algebraMap (ℚ[X]) (RatFunc ℚ) (1 + X ^ 2) := by
  intro b hb
  have hrhs_ne : algebraMap (ℚ[X]) (RatFunc ℚ) (1 + X ^ 2) ≠ 0 := RatFunc.algebraMap_ne_zero X2p1_ne_zero
  have hb_ne : b ≠ 0 := by rintro rfl; rw [zero_pow (by norm_num)] at hb; exact hrhs_ne hb.symm
  have hdeg : (b ^ 3).intDegree = (algebraMap (ℚ[X]) (RatFunc ℚ) (1 + X ^ 2)).intDegree := by rw [hb]
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, sq, RatFunc.intDegree_mul (mul_ne_zero hb_ne hb_ne) hb_ne,
    RatFunc.intDegree_mul hb_ne hb_ne, RatFunc.intDegree_polynomial, natDeg_X2p1] at hdeg
  omega

/-- `y³ − (x²+1)` is irreducible over `ℚ(x)`: `Irreducible (X³ − C(toK cubeRadicand))`, from
`X_pow_sub_C_irreducible_of_prime` (prime `3`) and `not_cube_X2p1`. -/
theorem irreducible_cubeRad :
    Irreducible (X ^ 3 - C (CFieldSpec.toK (cubeRadicand : CFrac ℚ))) := by
  rw [toK_cubeRadicand]
  exact X_pow_sub_C_irreducible_of_prime (by norm_num) not_cube_X2p1

/-- The cube-root irreducibility as a `Fact`, so `AdjoinRoot.instField` resolves the field
`ℚ(x)[∛(x²+1)]`. -/
instance fact_irreducible_cubeRad :
    Fact (Irreducible (X ^ 3 - C (CFieldSpec.toK (cubeRadicand : CFrac ℚ)))) :=
  ⟨irreducible_cubeRad⟩

/-- `ℚ(x)[∛(x²+1)]` is a field: `Field (AdjoinRoot (X³ − C(toK cubeRadicand)))`, from the irreducibility
`Fact`. -/
noncomputable example : Field (AdjoinRoot (X ^ 3 - C (CFieldSpec.toK (cubeRadicand : CFrac ℚ)))) :=
  inferInstance

/-! ### The engine differentiates/multiplies/inverts a cube root

Over `RadX3root = ℚ(x)[∛(x²+1)]`, through the typeclass projections: `y·y·y = f` (`radMul 3 f`),
`D(y) = (f'/(3f))·y` (`radDeriv 3 f`), and `u · u⁻¹ = 1` (`radInvN 3 f`). -/

/-- `y·y·y = f` in `RadX3root` through `CCommRing.mul`: the cube of `y = ∛(x²+1)` folds `y³ → f = x²+1`. -/
theorem cube_gen_cubed_eq_radicand :
    CCommRing.isZero (CField.sub (CCommRing.mul (CCommRing.mul cubeGen cubeGen) cubeGen)
      (⟨[cubeRadicand]⟩ : RadX3root)) = true := by native_decide

/-- `D(y) = (f'/(3f))·y` in `RadX3root` through `CDiffField.cderiv`: sends `y = ∛(x²+1)` to `ℓ·y`,
`ℓ = 2x/(3(x²+1))`. -/
theorem cube_cderiv_gen_eq :
    CCommRing.isZero (CField.sub (CDiffField.cderiv cubeGen)
      (⟨[CCommRing.zero, cubeLogDer]⟩ : RadX3root)) = true := by native_decide

/-- `u · u⁻¹ = 1` in `RadX3root` through `CCommRing.mul`/`CField.inv`: for `u = x + y`, the inverse
`radInvN 3 (x²+1)` satisfies `u · u⁻¹ = 1`. -/
theorem cube_mul_inv_eq_one :
    CCommRing.isZero (CField.sub (CCommRing.mul (⟨[CFrac.ofPoly [0, 1], CCommRing.one]⟩ : RadX3root)
      (CField.inv (⟨[CFrac.ofPoly [0, 1], CCommRing.one]⟩ : RadX3root))) CCommRing.one) = true := by
  native_decide

/-- A cube-root inverse with a genuine `y²`-component: for `u = 1 + y + y²`, `radInvN 3 (x²+1)` inverts,
`CCommRing.mul u u⁻¹ = 1` — a full-degree element the conjugate-norm `radInv2` could not handle. -/
theorem cube_mul_inv_eq_one_deg2 :
    CCommRing.isZero (CField.sub (CCommRing.mul (⟨[CCommRing.one, CCommRing.one, CCommRing.one]⟩ : RadX3root)
      (CField.inv (⟨[CCommRing.one, CCommRing.one, CCommRing.one]⟩ : RadX3root))) CCommRing.one) = true := by
  native_decide

/-- `D(1) = 0` and `D(0) = 0` in `RadX3root`: the cube-root derivation annihilates the unit and zero. -/
theorem cube_cderiv_one_zero :
    CCommRing.isZero (CDiffField.cderiv (CCommRing.one : RadX3root)) = true ∧
    CCommRing.isZero (CDiffField.cderiv (CCommRing.zero : RadX3root)) = true := by
  constructor <;> native_decide

/-! ### The general-`n` log-derivative `u'/u` and a cube-root integration check

`radLogDerivN n f u = (D u)·u⁻¹` uses the general-`n` inverse `radInvN`, so it is the honest `u'/u =
D(log u)` for every `n`; the integration soundness check is `∫ (radLogDerivN u) = log u`. -/

namespace RadElem
variable {α : Type*} [CField α] [CDiffField α]

/-- The general-`n` logarithmic derivative `radLogDerivN n f u = (radDeriv u)·u⁻¹` over `α[y]/(yⁿ − f)`,
the honest `u'/u = D(log u)` with inverse the extended-Euclid `radInvN n f`. -/
def radLogDerivN (n : ℕ) (f : α) (u : RadElem α) : RadElem α :=
  radMul n f (radDeriv n f u) (radInvN n f u)

end RadElem

/-- A cube-root log integrand `u'/u` for `u = x + ∛(x²+1)`: `radLogDerivN 3 (x²+1) u` is a nonzero element
of `ℚ(x)[∛(x²+1)]`, the integrand whose antiderivative is `log u`. -/
theorem cube_radLogDerivN_nonzero :
    DensePoly.cisZero (radLogDerivN 3 cubeRadicand (⟨[CFrac.ofPoly [0, 1], CCommRing.one]⟩ : RadX3root).toRadN)
      = false := by native_decide

/-- `D(log u) · u = D(u)` over the cube root: for `u = x + ∛(x²+1)`, `(radLogDerivN 3 f u)·u = D(u)`, i.e.
`(u'/u)·u = u'`, certifying `radLogDerivN` is the honest `u'/u`. -/
theorem cube_radLogDerivN_mul_eq_deriv :
    DensePoly.cisZero (DensePoly.csub
        (radMul 3 cubeRadicand (radLogDerivN 3 cubeRadicand
          (⟨[CFrac.ofPoly [0, 1], CCommRing.one]⟩ : RadX3root).toRadN) [CFrac.ofPoly [0, 1], CCommRing.one])
        (radDeriv 3 cubeRadicand [CFrac.ofPoly [0, 1], CCommRing.one])) = true := by native_decide

/-! ### A transcendental monomial over the cube-root base

`cmonomialDeriv` runs over `RadX3root[t]`, a transcendental monomial `t` over the cube-root base
`ℚ(x)[∛(x²+1)]`. With `y = ∛(x²+1)` (`D(y) = ℓ·y`, `ℓ = 2x/(3(x²+1))`) and `t = eˣ` (`Dt = t`),
`D(y·t) = (ℓ+1)·y·t`. -/

/-- The transcendental monomial `t = eˣ` over the cube-root base: `Dt = t`, as the
`RadX3root[t]`-polynomial `[0, 1] = t`. -/
def cubeDtExp : DensePoly RadX3root := [CCommRing.zero, CCommRing.one]

/-- The `RadX3root[t]`-polynomial `y·t = [0, y]` (cube-root generator `y = ∛(x²+1)` times `t = eˣ`). -/
def cubeGenT : DensePoly RadX3root := [CCommRing.zero, cubeGen]

/-- The `RadX3root[t]`-polynomial `(ℓ+1)·y·t = [0, (ℓ+1)·y]`, the expected `D(y·t)`
(`ℓ = f'/(3f) = 2x/(3(x²+1))`): `ℓ·y` the cube-root part `D(y)`, `y` the monomial part `y·Dt = y·t`. -/
def cubeGenTDeriv : DensePoly RadX3root :=
  [CCommRing.zero, CCommRing.mul (⟨[CCommRing.zero, CCommRing.add cubeLogDer CCommRing.one]⟩ : RadX3root) CCommRing.one]

/-- `D(y·t) = (ℓ+1)·y·t` over `RadX3root[t] = ℚ(x)[∛(x²+1)][eˣ]`: `cmonomialDeriv` runs both the cube-root
coefficient derivation (`ℓ·y`) and the `d/dt` part (`y`). -/
theorem cube_monomialDeriv_genT_eq :
    DensePoly.cisZero (DensePoly.csub
      (DensePoly.cmonomialDeriv cubeDtExp cubeGenT) cubeGenTDeriv) = true := by native_decide

/-- The mixed cube-root derivation runs the coefficient derivation: `D(y·t)` is neither zero nor equal to
the pure-`d/dt` result `y·t`, confirming the cube-root-base `cderiv` contributed the `ℓ·y·t` term. -/
theorem cube_monomialDeriv_genT_runs_coeff :
    (DensePoly.cisZero (DensePoly.cmonomialDeriv cubeDtExp cubeGenT) = false) ∧
    (DensePoly.cisZero (DensePoly.csub
      (DensePoly.cmonomialDeriv cubeDtExp cubeGenT) cubeGenT) = false) := by
  constructor <;> native_decide

end DeepWiki.SymbolicIntegration
