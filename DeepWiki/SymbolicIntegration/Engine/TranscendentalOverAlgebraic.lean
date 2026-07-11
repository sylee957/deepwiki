import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalExtension
import DeepWiki.SymbolicIntegration.Engine.Tower.RischDEInstance
import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalDerivationInvariant
import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalAssembly
import DeepWiki.SymbolicIntegration.Engine.Tower.Lvl2
import DeepWiki.SymbolicIntegration.Engine.Tower.Deriv
import DeepWiki.SymbolicIntegration.Engine.Tower.RischDE
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.RingTheory.AdjoinRoot

/-! # Transcendental monomials over an algebraic base: `RadExt` as a Risch base
Wraps the radical carrier `α[y]/(yⁿ − f)` in a type `RadExt α n f` and equips it with `CField`,
`CFieldDomain`, `CDiffField` (diagonal derivation `y' = (f'/(nf))·y`), and `CRischField` (RDE by scalar
decoupling), so a transcendental monomial `DenseFrac (RadExt α n f)` stacks on top. The worked base
`RadExt ℚ(x) 2 (x³+1)` gets a noncomputable `CFieldSpec` bridge into `AdjoinRoot (X² − C(toK f))`,
discharging `CFieldDomain` concretely. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem

/-! ### The carrier type `RadExt α n f` -/

/-- The simple-radical-extension carrier `RadExt α n f = α[y]/(yⁿ − f)`: a one-field structure
wrapping a `RadElem α` coefficient list, with degree `n` and radicand `f` carried by the type so
typeclass resolution dispatches the radical instances. `ofRad ::`/`toRad` construct/project. -/
structure RadExt (α : Type*) [CField α] (n : ℕ) (f : α) where
  /-- The underlying coefficient list `[a₀,…,a_{n−1}]` for `Σ aᵢyⁱ ∈ α[y]/(yⁿ − f)`. -/
  ofRad ::
  /-- The radical-extension element as a `RadElem α` coefficient list. -/
  toRad : RadElem α

namespace RadExt

variable {α : Type*} [CField α] {n : ℕ} {f : α}

/-- Zero of `RadExt α n f` — the wrapped `radZero` (`[]`). -/
def zero : RadExt α n f := ⟨radZero⟩

/-- One of `RadExt α n f` — the wrapped `radOne` (`[1]`). -/
def one : RadExt α n f := ⟨radOne⟩

/-- The generator `y` of `RadExt α n f` — the wrapped `radGen` (`[0, 1]`). -/
def gen : RadExt α n f := ⟨radGen⟩

/-- `radCanon n f u`: canonicalize a `RadElem` to a length-`≤ n` normalized rep — fold `yᵐ` (`m ≥ n`)
down by `yⁿ = f` and strip trailing zeros. A no-op on engine-produced values. -/
def radCanon (n : ℕ) (f : α) (u : RadElem α) : RadElem α :=
  DensePoly.cnorm (radReduce n f ((u : List α).length + 1) u)

/-- Addition in `RadExt α n f` — componentwise `DensePoly.cadd`, canonicalized to degree `< n`. -/
def add (p q : RadExt α n f) : RadExt α n f := ⟨radCanon n f (DensePoly.cadd p.toRad q.toRad)⟩

/-- Negation in `RadExt α n f` — componentwise `DensePoly.cneg`, canonicalized to degree `< n`. -/
def neg (p : RadExt α n f) : RadExt α n f := ⟨radCanon n f (DensePoly.cneg p.toRad)⟩

/-- Multiplication in `RadExt α n f` — `radMul n f` (poly-multiply in `y`, reduce `yⁿ → f`),
canonicalized (`radMul` already folds, so this is idempotent). -/
def mul (p q : RadExt α n f) : RadExt α n f := ⟨radCanon n f (radMul n f p.toRad q.toRad)⟩

/-- Inverse in `RadExt α n f` (for `n = 2`) — the canonicalized conjugate-norm reciprocal
`radCanon n f (radInv2 f (radCanon n f p))`; on the reduced rep `a + b·y`, `u⁻¹ = ū/(a² − b²f)`. -/
def inv (p : RadExt α n f) : RadExt α n f := ⟨radCanon n f (radInv2 f (radCanon n f p.toRad))⟩

/-- Zero test in `RadExt α n f` — reduce `mod yⁿ = f` first (`radCanon`), then `DensePoly.cisZero`, so the
test agrees with `AdjoinRoot (Xⁿ − f)` for every representative. -/
def isZero (p : RadExt α n f) : Bool := DensePoly.cisZero (radCanon n f p.toRad)

end RadExt

/-! ### `CField (RadExt α n f)` — the algebraic Risch base -/

/-- `CField (RadExt α n f)`: the radical extension `α[y]/(yⁿ − f)` as a computable field, with ops the
radical-carrier computations (`radZero`/…/`DensePoly.cisZero`, `inv` the conjugate-norm `radInv2`). -/
instance instCFieldRadExt {α : Type*} [CField α] [CFieldDomain α DensePoly] {n : ℕ} {f : α} :
    CField (RadExt α n f) where
  zero := RadExt.zero
  one := RadExt.one
  add := RadExt.add
  mul := RadExt.mul
  neg := RadExt.neg
  inv := RadExt.inv
  isZero := RadExt.isZero

/-! ### `CFieldDomain (RadExt α n f)` — the Prop-erased domain facts

The domain facts (`cisZero [1] = false`, no zero divisors) that let the next transcendental level stack;
being `Prop` they are erased at runtime. A concrete instance routes through the `CFieldSpec` bridge at the
end of this file; the composition section below carries `CFieldDomain RadX3` as a hypothesis. -/

/-! ### `CDiffField (RadExt α n f)` — the diagonal derivation makes it a differential base -/

/-- `CDiffField (RadExt α n f)`: the radical extension as a computable differential field, with
`cderiv := radDeriv n f` the diagonal derivation extending `α`'s `cderiv` by `y' = (f'/(nf))·y`. -/
instance instCDiffFieldRadExt {α : Type*} [CField α] [CFieldDomain α DensePoly] [CDiffField α] {n : ℕ} {f : α} :
    CDiffField (RadExt α n f) where
  cderiv p := ⟨radDeriv n f p.toRad⟩

/-! ### `CRischField (RadExt α n f)` — the algebraic-level RDE by scalar decoupling

The base Risch-DE solve `Dz + B·z = C` over the radical field. Because `radDeriv n f` is diagonal, a
scalar coefficient `B = b₀` decouples the equation into the `n` base RDEs `Dzᵢ + (b₀ + (i:α)·ℓ)·zᵢ = Cᵢ`
over `α` (`ℓ = f'/(nf)`), each solved by the base `CRischField α`; a non-scalar `B` (coupled system)
returns `none`. -/

/-- `RadExt.isScalar p = true` iff every `y`-component of `p` vanishes (`DensePoly.cisZero (p.toRad).tail`);
the decoupling base solve handles scalar coefficients, a non-scalar one is the coupled-system case. -/
def RadExt.isScalar {α : Type*} [CField α] {n : ℕ} {f : α} (p : RadExt α n f) : Bool :=
  DensePoly.cisZero ((p.toRad : List α).tail)

/-- `radExtRischDESolve B C : Option (RadExt α n f)`: the scalar-decoupling base RDE solve for
`Dz + B·z = C`. For scalar `B = b₀` it splits into the `n` base RDEs `Dzᵢ + (b₀ + (i:α)·ℓ)·zᵢ = Cᵢ`
over `α`, each solved by `CRischField.crischDESolve` and reassembled; a non-scalar `B` returns `none`. -/
def radExtRischDESolve {α : Type*} [CField α] [CDiffField α] [CRischField α] {n : ℕ} {f : α}
    (B C : RadExt α n f) : Option (RadExt α n f) :=
  if RadExt.isScalar B then
    let b₀ : α := (B.toRad : List α).headD CCommRing.zero
    let ℓ : α := RadElem.logDerRadicand n f
    (((List.range n).mapM fun i =>
      let coeff : α := CCommRing.add b₀ (CCommRing.mul (CField.natCast i) ℓ)
      let Ci : α := (C.toRad : List α).getD i CCommRing.zero
      CRischField.crischDESolve coeff Ci).map RadExt.ofRad)
  else none

/-- `CRischField (RadExt α n f)`: the base Risch-DE solver over the radical field, by scalar
decoupling (`radExtRischDESolve`). -/
instance instCRischFieldRadExt {α : Type*} [CField α] [CDiffField α] [CFieldDomain α DensePoly] [CRischField α]
    {n : ℕ} {f : α} : CRischField (RadExt α n f) where
  crischDESolve := radExtRischDESolve

/-! ### The base radical `√(x³+1)` over `ℚ(x)`, as a `CField`+`CDiffField`

`RadX3 := RadExt (DenseFrac ℚ) 2 radicandX3p1 = ℚ(x)[√(x³+1)]`; the ring, derivation, and inverse are
exhibited through the typeclass projections. -/

/-- The base radical field `ℚ(x)[√(x³+1)] = RadExt (DenseFrac ℚ) 2 (x³+1)`. -/
abbrev RadX3 : Type := RadExt (DenseFrac ℚ) 2 radicandX3p1

/-- `y·y = f` in `RadX3` through `CCommRing.mul`: squaring `y = √(x³+1)` reduces `y² → f = x³+1`. -/
theorem radX3_gen_sq_eq_radicand :
    CCommRing.isZero (CField.sub (CCommRing.mul (RadExt.gen : RadX3) RadExt.gen)
      (⟨[radicandX3p1]⟩ : RadX3)) = true := by
  ccompute

/-- `D(y) = (f'/(2f))·y` in `RadX3` through `CDiffField.cderiv`: the diagonal derivation sends
`y = √(x³+1)` to `ℓ·y` with `ℓ = 3x²/(2(x³+1))`. -/
theorem radX3_cderiv_gen_eq :
    CCommRing.isZero (CField.sub (CDiffField.cderiv (RadExt.gen : RadX3))
      (⟨[CCommRing.zero, radicandLogDer]⟩ : RadX3)) = true := by ccompute

/-- `u · u⁻¹ = 1` in `RadX3` through `CCommRing.mul`/`CField.inv`: for `u = x + y` the conjugate-norm
inverse is genuine, so `RadExt` is a field, not just a ring. -/
theorem radX3_mul_inv_eq_one :
    CCommRing.isZero (CField.sub (CCommRing.mul (⟨[CFrac.ofPoly [0, 1], CCommRing.one]⟩ : RadX3)
      (CField.inv (⟨[CFrac.ofPoly [0, 1], CCommRing.one]⟩ : RadX3))) CCommRing.one) = true := by ccompute

/-- `D(1) = 0` and `D(0) = 0` in `RadX3`: the derivation annihilates the unit and zero. -/
theorem radX3_cderiv_one_zero :
    CCommRing.isZero (CDiffField.cderiv (CCommRing.one : RadX3)) = true ∧
    CCommRing.isZero (CDiffField.cderiv (CCommRing.zero : RadX3)) = true := by
  constructor <;> ccompute

/-! ### The generic `CRischField (RadExt …)` solves a genuine algebraic RDE

Over `RadX3 = ℚ(x)[√(x³+1)]`, with scalar `B = 1` and `C` built from the target `z = x + 2·y` (so `C`
carries a genuine `y`-component), the solve decouples into two base RDEs over ℚ(x) and certifies
`radDeriv z + B·z = C`. -/

/-- The scalar coefficient `B = 1 ∈ RadX3` for the algebraic-RDE validation. -/
def radX3RischB : RadX3 := CCommRing.one

/-- The target solution `z = x + 2·y ∈ RadX3`, from which the right-hand side `C` is built. -/
def radX3RischZ : RadX3 := ⟨[CFrac.ofPoly [0, 1], CFrac.ofPoly [2]]⟩

/-- The right-hand side `C = radDeriv z + B·z ∈ RadX3` of the algebraic RDE, built from
`radX3RischZ`/`radX3RischB`; carries a genuine `y`-component. -/
def radX3RischC : RadX3 :=
  ⟨DensePoly.cadd (RadElem.radDeriv 2 radicandX3p1 radX3RischZ.toRad)
    (RadElem.radMul 2 radicandX3p1 radX3RischB.toRad radX3RischZ.toRad)⟩

/-- The right-hand side `C` has a genuine `y`-component (`DensePoly.cisZero (C.toRad.tail) = false`). -/
theorem radX3Risch_C_has_y_component :
    DensePoly.cisZero ((radX3RischC.toRad : List (DenseFrac ℚ)).tail) = false := by ccompute

/-- `CRischField.crischDESolve B C` returns `some` on the algebraic RDE over `RadX3` (`B = 1`, `C`
with a `y`-component). -/
theorem radX3Risch_solve_isSome :
    (CRischField.crischDESolve radX3RischB radX3RischC).isSome = true := by ccompute

/-- `CRischField (RadExt …)` solves a genuine algebraic RDE: `crischDESolve B C` over `RadX3` returns
`some z` satisfying `radDeriv z + B·z = C` exactly. -/
theorem radX3Risch_solves_rde :
    (match CRischField.crischDESolve radX3RischB radX3RischC with
      | some z => DensePoly.cisZero (DensePoly.csub
          (DensePoly.cadd (RadElem.radDeriv 2 radicandX3p1 z.toRad)
            (RadElem.radMul 2 radicandX3p1 radX3RischB.toRad z.toRad)) radX3RischC.toRad)
      | none => false) = true := by ccompute

/-- A non-scalar coefficient `B` returns `none`: with `B = y`, `crischDESolve B C` does not attempt the
coupled-system case, keeping the solver sound. -/
theorem radX3Risch_nonscalar_none :
    CRischField.crischDESolve (RadExt.gen : RadX3) radX3RischC = none := by ccompute

/-! ### A transcendental monomial over the algebraic base

A transcendental monomial `t` stacks on `RadX3 = ℚ(x)[√(x³+1)]`; `CPolyEngine.monomialDeriv` runs over
`RadX3[t]`, exhibited by `D(t²) = 2t²` (for `t = exp`) and the mixing `D(y·t) = (ℓ+1)·y·t`. -/

/-- The transcendental monomial `t = eˣ` over the radical base: its derivative `Dt = t`, as the
`RadX3[t]`-polynomial `[0, 1] = t` (the independent exponential, `Dt = t`). -/
def radX3DtExp : DensePoly RadX3 := [CCommRing.zero, CCommRing.one]

/-- The `RadX3[t]`-polynomial `t² = [0, 0, 1]` (a transcendental square over the radical base). -/
def radX3T2sq : DensePoly RadX3 := [CCommRing.zero, CCommRing.zero, CCommRing.one]

/-- The `RadX3[t]`-polynomial `2·t² = [0, 0, 2]` (`2 = 1 + 1`), the expected `D(t²)` for `t = eˣ`. -/
def radX3TwoT2sq : DensePoly RadX3 := [CCommRing.zero, CCommRing.zero, CCommRing.add CCommRing.one CCommRing.one]

/-- `D(t²) = 2t²` over `RadX3[t] = ℚ(x)[√(x³+1)][eˣ]`: `CPolyEngine.monomialDeriv` (with `t = eˣ`, `Dt = t`)
computes `D(t²) = 2t·t = 2t²` over the algebraic base. -/
theorem radX3_monomialDeriv_t2sq_eq_two_t2sq :
    DensePoly.cisZero (DensePoly.csub
      (CPolyEngine.monomialDeriv radX3DtExp radX3T2sq) radX3TwoT2sq) = true := by ccompute

/-- The `RadX3[t]`-polynomial `y·t = [0, y]` (the radical generator `y = √(x³+1)` times the monomial
`t = eˣ`): constant `t`-coefficient `0`, linear `t`-coefficient `y = RadExt.gen`. -/
def radX3GenT : DensePoly RadX3 := [CCommRing.zero, RadExt.gen]

/-- The `RadX3[t]`-polynomial `(ℓ+1)·y·t = [0, (ℓ+1)·y]`, the expected `D(y·t)` (`ℓ = f'/(2f)`). -/
def radX3GenTDeriv : DensePoly RadX3 :=
  [CCommRing.zero, CCommRing.mul (⟨[CCommRing.zero, CCommRing.add radicandLogDer CCommRing.one]⟩ : RadX3) CCommRing.one]

/-- `D(y·t) = (ℓ+1)·y·t` over `RadX3[t]`: the mixed tower derivation, with `D(y) = ℓ·y` (radical) and
`Dt = t` (monomial) both firing via the product rule. -/
theorem radX3_monomialDeriv_genT_eq :
    DensePoly.cisZero (DensePoly.csub
      (CPolyEngine.monomialDeriv radX3DtExp radX3GenT) radX3GenTDeriv) = true := by ccompute

/-- The mixed derivation genuinely runs the coefficient derivation: `D(y·t)` over `RadX3[t]` is neither
zero nor equal to the pure-`d/dt` result `y·t`, confirming the radical-base `cderiv` contributed. -/
theorem radX3_monomialDeriv_genT_runs_coeff :
    (DensePoly.cisZero (CPolyEngine.monomialDeriv radX3DtExp radX3GenT) = false) ∧
    (DensePoly.cisZero (DensePoly.csub
      (CPolyEngine.monomialDeriv radX3DtExp radX3GenT) radX3GenT) = false) := by
  constructor <;> ccompute

/-! ### The keystone composes: a transcendental level `DenseFrac (RadExt …)` over the algebraic base

Under `[CFieldDomain RadX3 DensePoly]`, `DenseFrac RadX3 ≅ ℚ(x)[√(x³+1)](t)` resolves its `CField` and `CDiffField`
automatically from the `RadExt` instances above. -/

section
variable [CFieldDomain RadX3 DensePoly]

/-- `DenseFrac RadX3` is a `CField` (given `[CFieldDomain RadX3 DensePoly]`) — the transcendental level
`ℚ(x)[√(x³+1)](t)` resolves automatically from the radical-base instance. -/
theorem cfield_qfunNZG_radX3 : Nonempty (CField (DenseFrac RadX3)) := ⟨inferInstance⟩

/-- `DenseFrac RadX3` is a `CDiffField` (given `[CFieldDomain RadX3 DensePoly]`) — the transcendental level inherits
the full tower derivation `d/dx + radical y' + ∂/∂t`. -/
theorem cdiffField_qfunNZG_radX3 : Nonempty (CDiffField (DenseFrac RadX3)) := ⟨inferInstance⟩

end

/-! ### Toward discharging `[CFieldDomain RadX3 DensePoly]`: irreducibility of `y² − (x³+1)` over ℚ(x)

`ℚ(x)[√(x³+1)] = ℚ(x)[y]/(y² − (x³+1))` is a field because `y² − (x³+1)` is irreducible over ℚ(x)
(`x³+1` is not a square — odd degree). Proven here as `irreducible_radX3` and registered as a `Fact`. -/

open DensePoly in
/-- `toK radicandX3p1 = algebraMap (1 + x³)` in `RatFunc ℚ`: the ℚ(x)-radicand of `RadX3` reads as the
rational function `algebraMap ℚ[X] (RatFunc ℚ) (1 + x³)`. -/
theorem toK_radicandX3p1 :
    CFieldSpec.toK (radicandX3p1 : DenseFrac ℚ) = algebraMap (ℚ[X]) (RatFunc ℚ) (1 + X ^ 3) := by
  show CFrac.toRatFunc radicandX3p1 = _
  rw [radicandX3p1, CFrac.toRatFunc_ofPoly, toPoly_list_eq]
  have h1 : toPoly ([1, 0, 0, 1] : DensePoly ℚ) = 1 + X ^ 3 := by
    simp only [denote]
    show C (1 : ℚ) + X * (C 0 + X * (C 0 + X * (C 1 + X * 0))) = _
    simp; ring
  rw [h1]
  rfl

/-- `1 + x³ ≠ 0` in `ℚ[X]` (it has `natDegree 3`). -/
theorem X3p1_ne_zero : (1 + X ^ 3 : ℚ[X]) ≠ 0 := by
  intro h
  have := congrArg Polynomial.natDegree h
  rw [add_comm, Polynomial.natDegree_add_eq_left_of_natDegree_lt (by simp), natDegree_X_pow] at this
  simp at this

/-- `natDegree (1 + x³) = 3` in `ℚ[X]` (the leading `x³` dominates the constant `1`). -/
theorem natDeg_X3p1 : (1 + X ^ 3 : ℚ[X]).natDegree = 3 := by
  rw [add_comm, Polynomial.natDegree_add_eq_left_of_natDegree_lt (by simp), natDegree_X_pow]

/-- `x³+1` is not a square in `ℚ(x)`: `∀ b : RatFunc ℚ, b² ≠ algebraMap (1 + x³)` — a square has even
`intDegree`, but `1 + x³` has odd `intDegree 3`. -/
theorem not_square_X3p1 :
    ∀ b : RatFunc ℚ, b ^ 2 ≠ algebraMap (ℚ[X]) (RatFunc ℚ) (1 + X ^ 3) := by
  intro b hb
  have hrhs_ne : algebraMap (ℚ[X]) (RatFunc ℚ) (1 + X ^ 3) ≠ 0 := RatFunc.algebraMap_ne_zero X3p1_ne_zero
  have hb_ne : b ≠ 0 := by rintro rfl; rw [zero_pow (by norm_num)] at hb; exact hrhs_ne hb.symm
  have hdeg : (b ^ 2).intDegree = (algebraMap (ℚ[X]) (RatFunc ℚ) (1 + X ^ 3)).intDegree := by rw [hb]
  rw [sq, RatFunc.intDegree_mul hb_ne hb_ne, RatFunc.intDegree_polynomial, natDeg_X3p1] at hdeg
  omega

/-- `y² − (x³+1)` is irreducible over `ℚ(x)` — `Irreducible (X² − C(toK radicandX3p1))`, from
`X_pow_sub_C_irreducible_of_prime` and `not_square_X3p1`. -/
theorem irreducible_radX3 :
    Irreducible (X ^ 2 - C (CFieldSpec.toK (radicandX3p1 : DenseFrac ℚ))) := by
  rw [toK_radicandX3p1]
  exact X_pow_sub_C_irreducible_of_prime Nat.prime_two not_square_X3p1

/-- The irreducibility as a `Fact`, so `AdjoinRoot.instField` resolves `Field (AdjoinRoot (X² −
C(toK radicandX3p1)))`. -/
instance fact_irreducible_radX3 :
    Fact (Irreducible (X ^ 2 - C (CFieldSpec.toK (radicandX3p1 : DenseFrac ℚ)))) :=
  ⟨irreducible_radX3⟩

/-- `ℚ(x)[√(x³+1)]` is a field — `Field (AdjoinRoot (X² − C(toK radicandX3p1)))`, resolved from the
irreducibility `Fact`. The genuine field the radical base `RadX3` represents; the integral-domain witness
that `CFieldDomain RadX3` asserts (the discharge is the residual below). -/
noncomputable example : Field (AdjoinRoot (X ^ 2 - C (CFieldSpec.toK (radicandX3p1 : DenseFrac ℚ)))) :=
  inferInstance

/-! ### The `CFieldSpec (RadExt α n f)` bridge into `AdjoinRoot (Xⁿ − C(toK f))`

The noncomputable correctness bridge, `toK p := AdjoinRoot.mk _ (toPoly (RadExt.radCanon n f p.toRad))`
on canonical reps. The crux lemmas are `isZero_iff` (length bound) and `toK_inv` (conjugate-norm
identity); restricted to `n = 2`. -/

namespace RadElem
variable {α : Type*} [CField α] {n : ℕ} {f : α}

/-- The inner `radReduce` reaches `cnorm`-length `≤ n` (`n ≥ 1`, `fuel ≥ cnorm`-length) — each fold
strictly drops the normalized length, so the loop hits the `length ≤ n` exit. -/
theorem cnormG_radReduce_length_le (hn : 1 ≤ n) : ∀ (fuel : ℕ) (u : DensePoly α),
    (DensePoly.cnorm u : List α).length ≤ fuel →
    (DensePoly.cnorm (radReduce n f fuel u) : List α).length ≤ n := by
  intro fuel
  induction fuel with
  | zero => intro u hub; rw [radReduce]; simp only [Nat.le_zero] at hub; omega
  | succ fuel ih =>
    intro u hub
    rw [radReduce]
    by_cases hlen : (DensePoly.cnorm u : List α).length ≤ n
    · simp only [hlen, if_true, DensePoly.cnormG_idem]
    · simp only [hlen, if_false]; replace hlen := Nat.lt_of_not_le hlen
      apply ih
      set q := DensePoly.cnorm u with hq
      have hstep : (DensePoly.cadd (q : List α).dropLast
        (DensePoly.cshift ((q : List α).length - 1 - n)
            [CCommRing.mul ((q : List α).getLast?.getD CCommRing.zero) f]) : List α).length
          < (q : List α).length := by
        rw [DensePoly.caddG_length, DensePoly.cshiftG_length]
        simp only [List.length_singleton, List.length_dropLast]; omega
      have := (DensePoly.cnormG_length_le _).trans_lt hstep; omega

/-- `RadExt.radCanon` has length `≤ n` (`n ≥ 1`), from `cnormG_radReduce_length_le` — the bound that
makes `isZero_iff` and `toK_inv` faithful. -/
theorem radCanon_length_le (hn : 1 ≤ n) (u : DensePoly α) :
    (RadExt.radCanon n f u : List α).length ≤ n := by
  rw [RadExt.radCanon]
  have := cnormG_radReduce_length_le (f := f) hn ((u : List α).length + 1) u (by
    have := DensePoly.cnormG_length_le u; omega)
  exact this

/-- `cnorm (RadExt.radCanon u)` has length `≤ n` — immediate from `radCanon_length_le` and
`DensePoly.cnormG_length_le` (the outer `cnorm` of `radCanon` is idempotent). -/
theorem cnormG_radCanon_length_le (hn : 1 ≤ n) (u : DensePoly α) :
    (DensePoly.cnorm (RadExt.radCanon n f u) : List α).length ≤ n :=
  (DensePoly.cnormG_length_le _).trans (radCanon_length_le hn u)

variable [CFieldSpec α]

/-- The bridge `toAdj p = mk (toPoly p.toRad)` into `AdjoinRoot (Xⁿ − C(toK f))` (`mk` *is*
`Ideal.Quotient.mk (radIdeal n f)`). The `toK` of the `CFieldSpec (RadExt …)` instance, on canonical reps. -/
noncomputable def toAdj (p : RadExt α n f) : AdjoinRoot (X ^ n - C (CFieldSpec.toK f)) :=
  AdjoinRoot.mk _ (DensePoly.toPoly p.toRad)

/-- `RadExt.radCanon` is absorbed by `mk` — `mk (toPoly (RadExt.radCanon n f u)) = mk (toPoly u)` (the reduction
changes the polynomial only by a multiple of `Xⁿ − C(toK f)`, `mk_toPolyG_radReduce`). -/
theorem mk_canon (u : RadElem α) :
    AdjoinRoot.mk (X ^ n - C (CFieldSpec.toK f)) (DensePoly.toPoly (RadExt.radCanon n f u))
      = AdjoinRoot.mk _ (DensePoly.toPoly u) := by
  show Ideal.Quotient.mk (radIdeal n f) _ = Ideal.Quotient.mk _ _
  simp only [RadExt.radCanon, denote]
  rw [mk_toPolyG_radReduce]

/-- `toAdj` sends `RadExt.zero` to `0`. -/
theorem toAdj_zero : toAdj (RadExt.zero : RadExt α n f) = 0 := by
  show AdjoinRoot.mk _ (DensePoly.toPoly ([] : RadElem α)) = 0
  rw [DensePoly.toPolyG_nil, map_zero]

/-- `toAdj` sends `RadExt.one` to `1`. -/
theorem toAdj_one : toAdj (RadExt.one : RadExt α n f) = 1 := by
  show AdjoinRoot.mk (X ^ n - C (CFieldSpec.toK f)) (DensePoly.toPoly ([CCommRing.one] : RadElem α)) = 1
  rw [show DensePoly.toPoly ([CCommRing.one] : RadElem α) = (1 : (CFieldSpec.K α)[X]) by
    simp only [denote]; simp]
  exact map_one _

/-- `toAdj` sends radical-extension addition to quotient-ring addition. -/
theorem toAdj_add (p q : RadExt α n f) : toAdj (RadExt.add p q) = toAdj p + toAdj q := by
  show AdjoinRoot.mk _ (DensePoly.toPoly (RadExt.radCanon n f (DensePoly.cadd p.toRad q.toRad))) = _
  rw [mk_canon]
  show AdjoinRoot.mk _ (DensePoly.toPoly (DensePoly.cadd _ _)) = _
  simp only [denote, map_add]
  rfl

/-- `toAdj` sends radical-extension negation to quotient-ring negation. -/
theorem toAdj_neg (p : RadExt α n f) : toAdj (RadExt.neg p) = - toAdj p := by
  show AdjoinRoot.mk _ (DensePoly.toPoly (RadExt.radCanon n f (DensePoly.cneg p.toRad))) = _
  rw [mk_canon]
  show AdjoinRoot.mk _ (DensePoly.toPoly (DensePoly.cneg _)) = _
  simp only [denote, map_neg]
  rfl

/-- `toAdj` sends radical-extension multiplication to quotient-ring multiplication. -/
theorem toAdj_mul (p q : RadExt α n f) : toAdj (RadExt.mul p q) = toAdj p * toAdj q := by
  show AdjoinRoot.mk _ (DensePoly.toPoly (RadExt.radCanon n f (radMul n f p.toRad q.toRad))) = _
  rw [mk_canon]; show Ideal.Quotient.mk (radIdeal n f) _ = _ * _
  rw [mk_toPolyG_radMul]; rfl

/-- `toAdj` identifies the computable zero test with quotient-ring equality to zero. -/
theorem isZero_iff (hn : 1 ≤ n) (p : RadExt α n f) : RadExt.isZero p = true ↔ toAdj p = 0 := by
  rw [RadExt.isZero, toAdj]
  constructor
  · intro h
    have h0 : DensePoly.toPoly (RadExt.radCanon n f p.toRad) = 0 := (DensePoly.cisZeroG_iff _).mp h
    rw [← mk_canon (f := f) p.toRad, h0, map_zero]
  · intro h
    by_contra hne
    have hcz : DensePoly.cisZero (RadExt.radCanon n f p.toRad) = false := by
      rw [Bool.eq_false_iff]; exact hne
    have hp0 : DensePoly.toPoly (RadExt.radCanon n f p.toRad) ≠ 0 := by
      rw [Ne, ← DensePoly.cisZeroG_iff, hcz]; exact Bool.false_ne_true
    have hdeg : (DensePoly.toPoly (RadExt.radCanon n f p.toRad)).natDegree < n := by
      have h1 := DensePoly.natDegree_toPolyG_le (RadExt.radCanon n f p.toRad)
      have h2 := cnormG_radCanon_length_le (f := f) hn p.toRad
      omega
    have hmono : (X ^ n - C (CFieldSpec.toK f)).Monic := monic_X_pow_sub_C _ (by omega)
    have := AdjoinRoot.mk_ne_zero_of_natDegree_lt hmono hp0 (by rw [natDegree_X_pow_sub_C]; exact hdeg)
    rw [← mk_canon (f := f) p.toRad] at h; exact this h

/-! #### The inverse law (`n = 2`): `toAdj (RadExt.inv p) = (toAdj p)⁻¹`

For `q = a + b·y` with conjugate norm `N = a² − b²f`, `radInv2 f q = [a/N, −b/N]` is `q⁻¹` when `N ≠ 0`
(both vanish when `q = 0`). -/

/-- `toPoly (radInv2 f q) = C(toK(a/N)) − C(toK(b/N))·X` in `K[X]` (`a, b` coefficients zero and one,
`N = radNorm2`). -/
theorem toPolyG_radInv2 (q : RadElem α) :
    DensePoly.toPoly (radInv2 f q)
      = C (CFieldSpec.toK (CField.div (CPoly.coeff q 0) (radNorm2 f q)))
        - C (CFieldSpec.toK (CField.div (CPoly.coeff q 1) (radNorm2 f q))) * X := by
  show DensePoly.toPoly [CField.div (CPoly.coeff q 0) (radNorm2 f q),
      CCommRing.neg (CField.div (CPoly.coeff q 1) (radNorm2 f q))] = _
  simp only [denote, mul_zero, add_zero]
  rw [map_neg]; ring

/-- `toPoly q = C(toK a) + C(toK b)·X` for a length-`≤ 2` `q` with coefficients `a` and `b`. -/
theorem toPolyG_of_len_le_two (q : RadElem α) (hq : (q : List α).length ≤ 2) :
    DensePoly.toPoly q = C (CFieldSpec.toK (CPoly.coeff q 0)) + C (CFieldSpec.toK (CPoly.coeff q 1)) * X := by
  match q, hq with
  | [], _ => simp [CPoly.coeff_dense_eq, CFieldSpec.toK_zero]
  | [a], _ =>
    show DensePoly.toPoly [a] = _
    rw [show CPoly.coeff ([a] : RadElem α) 0 = a from rfl,
      show CPoly.coeff ([a] : RadElem α) 1 = CCommRing.zero from rfl]
    simp only [denote, mul_zero, add_zero]
    rw [map_zero, zero_mul, add_zero]
  | [a, b], _ =>
    show DensePoly.toPoly [a, b] = _
    rw [show CPoly.coeff ([a, b] : RadElem α) 0 = a from rfl,
      show CPoly.coeff ([a, b] : RadElem α) 1 = b from rfl]
    simp only [denote, mul_zero, add_zero]; ring

/-- The conjugate-norm inverse identity (`n = 2`, length-`≤ 2` `q`, `N ≠ 0`): `mk (toPoly q) · mk
(toPoly (radInv2 f q)) = 1` in `AdjoinRoot (X² − C(toK f))`. -/
theorem inv_mul_gen (q : RadElem α) (hq : (q : List α).length ≤ 2)
    (hN : CFieldSpec.toK (radNorm2 f q) ≠ 0) :
    AdjoinRoot.mk (X ^ 2 - C (CFieldSpec.toK f)) (DensePoly.toPoly q)
      * AdjoinRoot.mk _ (DensePoly.toPoly (radInv2 f q)) = 1 := by
  set A := CFieldSpec.toK (CPoly.coeff q 0)
  set B := CFieldSpec.toK (CPoly.coeff q 1)
  set F := CFieldSpec.toK f
  set N := CFieldSpec.toK (radNorm2 f q) with hNdef
  have hNval : N = A * A - B * B * F := by
    rw [hNdef, radNorm2, CFieldSpec.toK_sub, CFieldSpec.toK_mul, CFieldSpec.toK_mul, CFieldSpec.toK_mul]
  have hq2 : DensePoly.toPoly q = C A + C B * X := toPolyG_of_len_le_two q hq
  have hinv : DensePoly.toPoly (radInv2 f q) = C (A / N) - C (B / N) * X := by
    rw [toPolyG_radInv2, CFieldSpec.toK_div, CFieldSpec.toK_div]
  rw [hq2, hinv, ← map_mul]
  rw [show (1 : AdjoinRoot (X ^ 2 - C F)) = AdjoinRoot.mk _ 1 from (map_one _).symm, AdjoinRoot.mk_eq_mk]
  have hconst : A * (A / N) - B * F * (B / N) = 1 := by field_simp; rw [hNval]; ring
  have hcross : B * (A / N) = A * (B / N) := by ring
  have hc : C A * C (A / N) - C B * C F * C (B / N) = 1 := by
    have := congrArg (C : CFieldSpec.K α → (CFieldSpec.K α)[X]) hconst
    rwa [map_sub, map_mul, map_mul, map_mul, map_one] at this
  have hcr : C B * C (A / N) = C A * C (B / N) := by
    have := congrArg (C : CFieldSpec.K α → (CFieldSpec.K α)[X]) hcross
    rwa [map_mul, map_mul] at this
  have key : (C A + C B * X) * (C (A / N) - C (B / N) * X) - 1
      = (- (C B * C (B / N))) * (X ^ 2 - C F) := by linear_combination hc + X * hcr
  rw [key]; exact dvd_mul_left _ _

/-- `N = 0` when a reduced `q` vanishes — `toPoly q = 0 → toK (radNorm2 f q) = 0` (the coefficients
`a, b` both vanish, so `N = a² − b²f = 0`). -/
theorem toK_radNorm2_eq_zero_of_toPolyG_zero (q : RadElem α) (hq : (q : List α).length ≤ 2)
    (h0 : DensePoly.toPoly q = 0) : CFieldSpec.toK (radNorm2 f q) = 0 := by
  rw [toPolyG_of_len_le_two q hq] at h0
  have hA : CFieldSpec.toK (CPoly.coeff q 0) = 0 := by
    have := congrArg (Polynomial.coeff · 0) h0; simpa [coeff_C, coeff_X] using this
  have hB : CFieldSpec.toK (CPoly.coeff q 1) = 0 := by
    have := congrArg (Polynomial.coeff · 1) h0; simpa [coeff_C, coeff_X, coeff_C_mul] using this
  rw [radNorm2, CFieldSpec.toK_sub, CFieldSpec.toK_mul, CFieldSpec.toK_mul, CFieldSpec.toK_mul, hA, hB]
  ring

/-- A reduced quadratic radical representative that maps to zero is the zero polynomial. -/
theorem toPolyG_eq_zero_of_mk_zero [Fact (Irreducible (X ^ 2 - C (CFieldSpec.toK f)))]
    (q : RadElem α) (hq : (q : List α).length ≤ 2)
    (h : AdjoinRoot.mk (X ^ 2 - C (CFieldSpec.toK f)) (DensePoly.toPoly q) = 0) :
    DensePoly.toPoly q = 0 := by
  by_contra h0
  have hdeg : (DensePoly.toPoly q).natDegree < 2 := by
    have := DensePoly.natDegree_toPolyG_le q
    have hcn := DensePoly.cnormG_length_le q
    omega
  have hmono : (X ^ 2 - C (CFieldSpec.toK f)).Monic := monic_X_pow_sub_C _ (by norm_num)
  exact AdjoinRoot.mk_ne_zero_of_natDegree_lt hmono h0 (by rw [natDegree_X_pow_sub_C]; exact hdeg) h

/-- A vanishing conjugate norm forces a canonical rep to `0` (`n = 2`, length-`≤ 2` `q`):
`toK (radNorm2 f q) = 0 → toPoly q = 0`, since `F` not a square (irreducibility `Fact`) forces
`b = 0` then `a = 0`. -/
theorem toPolyG_eq_zero_of_N_zero [Fact (Irreducible (X ^ 2 - C (CFieldSpec.toK f)))]
    (q : RadElem α) (hq : (q : List α).length ≤ 2)
    (hN : CFieldSpec.toK (radNorm2 f q) = 0) : DensePoly.toPoly q = 0 := by
  set A := CFieldSpec.toK (CPoly.coeff q 0)
  set B := CFieldSpec.toK (CPoly.coeff q 1)
  set F := CFieldSpec.toK f
  have hNval : A * A - B * B * F = 0 := by
    rw [← hN, radNorm2, CFieldSpec.toK_sub, CFieldSpec.toK_mul, CFieldSpec.toK_mul, CFieldSpec.toK_mul]
  have hnsq : ∀ c : CFieldSpec.K α, c ^ 2 ≠ F :=
    (X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two).mp (Fact.out)
  have hB : B = 0 := by
    by_contra hBne
    apply hnsq (A / B)
    rw [div_pow, sq, sq]
    field_simp
    linear_combination hNval
  have hA : A = 0 := by
    have : A * A = 0 := by rw [hB] at hNval; linear_combination hNval
    rcases mul_eq_zero.mp this with h | h <;> exact h
  rw [toPolyG_of_len_le_two q hq, show CFieldSpec.toK (CPoly.coeff q 0) = A from rfl,
    show CFieldSpec.toK (CPoly.coeff q 1) = B from rfl, hA, hB]
  simp

/-- `toAdj` intertwines `RadExt.inv` with `⁻¹` (`n = 2`): `toAdj (RadExt.inv p) = (toAdj p)⁻¹`, by
splitting on the conjugate norm `N` (`inv_mul_gen` when `N ≠ 0`, `q = 0` when `N = 0`). -/
theorem toAdj_inv [Fact (Irreducible (X ^ 2 - C (CFieldSpec.toK f)))] (p : RadExt α 2 f) :
    toAdj (RadExt.inv p) = (toAdj p)⁻¹ := by
  set q := RadExt.radCanon 2 f p.toRad with hq
  have hqlen : (q : List α).length ≤ 2 := by rw [hq]; exact radCanon_length_le (by norm_num) p.toRad
  have hpadj : toAdj p = AdjoinRoot.mk _ (DensePoly.toPoly q) := by rw [toAdj, hq, mk_canon]
  show AdjoinRoot.mk _ (DensePoly.toPoly (RadExt.radCanon 2 f (radInv2 f (RadExt.radCanon 2 f p.toRad)))) = _
  rw [mk_canon, ← hq]
  by_cases hN : CFieldSpec.toK (radNorm2 f q) = 0
  · -- `N = 0 ⟹ q = 0 ⟹ radInv2 f q = 0` and `toAdj p = 0`; `0 = 0⁻¹`.
    have hq0 : DensePoly.toPoly q = 0 := toPolyG_eq_zero_of_N_zero q hqlen hN
    have hinv0 : DensePoly.toPoly (radInv2 f q) = 0 := by
      rw [toPolyG_radInv2, CFieldSpec.toK_div, CFieldSpec.toK_div, hN, div_zero, div_zero, map_zero]
      simp
    rw [hinv0, map_zero, hpadj, hq0, map_zero, inv_zero]
  · rw [hpadj]
    exact eq_inv_of_mul_eq_one_right (inv_mul_gen q hqlen hN)

end RadElem

/-! ### `CFieldSpec (RadExt α 2 f)` and the concrete `CFieldDomain`

Assembling the bridge laws gives the noncomputable `CFieldSpec (RadExt α 2 f)`; the global
`instCFieldDomainOfCFieldSpec` then supplies `CFieldDomain (RadExt α 2 f)`, discharging the hypothesis
and making `DenseFrac (RadExt …)` an unconditional `CField` + `CDiffField`. -/

/-- `CFieldSpec (RadExt α 2 f)` — the field-homomorphism bridge into `K = AdjoinRoot (X² − C(toK f))`
with `toK := RadElem.toAdj`, all laws the `RadElem.toAdj_*` bridge theorems. Noncomputable. -/
noncomputable instance instCFieldSpecRadExt {α : Type*} [CField α] [CFieldDomain α DensePoly] [CFieldSpec α]
    {f : α} [Fact (Irreducible (X ^ 2 - C (CFieldSpec.toK f)))] : CFieldSpec (RadExt α 2 f) where
  K := AdjoinRoot (X ^ 2 - C (CFieldSpec.toK f))
  toK := RadElem.toAdj
  toK_zero := RadElem.toAdj_zero
  toK_one := RadElem.toAdj_one
  toK_add := RadElem.toAdj_add
  toK_mul := RadElem.toAdj_mul
  toK_neg := RadElem.toAdj_neg
  toK_inv := RadElem.toAdj_inv
  isZero_iff p := RadElem.isZero_iff (by norm_num) p

/-! ### Unconditional composition: `DenseFrac (RadExt ℚ(x) 2 (x³+1))` is a `CField` + `CDiffField`

`CFieldDomain RadX3` resolves concretely (no hypothesis), so `DenseFrac RadX3 ≅ ℚ(x)[√(x³+1)](t)` is an
unconditional `CField` and `CDiffField`. -/

noncomputable example : CFieldDomain RadX3 DensePoly := inferInstance

/-- `DenseFrac RadX3` has an unconditional computable-field structure. -/
theorem cfield_qfunNZG_radX3_unconditional : Nonempty (CField (DenseFrac RadX3)) := ⟨inferInstance⟩

/-- `DenseFrac RadX3` is a `CDiffField`, unconditionally — `ℚ(x)[√(x³+1)](t)` inheriting the full tower
derivation `d/dx + radical y' + ∂/∂t`. -/
theorem cdiffField_qfunNZG_radX3_unconditional : Nonempty (CDiffField (DenseFrac RadX3)) := ⟨inferInstance⟩

/-- The transcendental monomial `t ∈ DenseFrac RadX3 = ℚ(x)[√(x³+1)](t)` (numerator `[0, 1]`, denominator
`[1]`). -/
def tOverRadX3 : DenseFrac RadX3 := CFrac.ofPoly [CCommRing.zero, CCommRing.one]

/-- `D(t) = 1` over `ℚ(x)[√(x³+1)](t)` — the typeclass derivation `CDiffField.cderiv` on `DenseFrac RadX3`
sends the transcendental monomial `t` to `1` over the algebraic base. -/
theorem cderiv_tOverRadX3_eq_one :
    CCommRing.isZero (CField.sub (CDiffField.cderiv tOverRadX3) (CCommRing.one : DenseFrac RadX3)) = true := by
  ccompute

/-- `t · t⁻¹ = 1` over `ℚ(x)[√(x³+1)](t)` — the typeclass field operations of `DenseFrac RadX3` invert
the transcendental monomial `t` over the algebraic base. -/
theorem mul_inv_tOverRadX3_eq_one :
    CCommRing.isZero (CField.sub (CCommRing.mul tOverRadX3 (CField.inv tOverRadX3))
      (CCommRing.one : DenseFrac RadX3)) = true := by ccompute

end DeepWiki.SymbolicIntegration
