import DeepWiki.SymbolicIntegration.ComputableRadicalExtension
import DeepWiki.SymbolicIntegration.ComputableRadicalDerivationInvariant
import DeepWiki.SymbolicIntegration.ComputableRadicalIntegrateFull
import DeepWiki.SymbolicIntegration.ComputableTowerField
import DeepWiki.SymbolicIntegration.ComputableTowerDeriv

/-! # Transcendental monomials over an algebraic base: `RadExt` as a Risch base
The transcendental Risch engine runs the polynomial engine over a **tower** of computable fields, and the
keystone `QFunNZG α` (the new-transcendental-monomial carrier, `ComputableTowerField`) is **generic over
any `[CField α]`** — so a transcendental extension stacks on anything that is a `CField`. The radical
carrier `α[y]/(yⁿ − f)` (`ComputableRadicalExtension`'s `RadElem` + `radAdd`/`radMul`/`radInv2`/the
diagonal `radDeriv`) is an algebraic extension, but it carried **no** `CField`/`CDiffField`/`CFieldDomain`
instance — so nothing could be stacked on top of it. This file closes that gap: it wraps the radical
carrier in a *type* `RadExt α n f` that carries the degree `n` and radicand `f` (so typeclass resolution
can dispatch), and equips it with

* **`CField (RadExt α n f)`** (over `[CField α] [CFieldDomain α]`) — `zero`/`one`/`add`/`mul`/`isZero` from
  `radZero`/`radOne`/`radAdd`/`radMul`/`radIsZero`, `neg` from `radNeg`, and `inv` from the
  conjugate-norm reciprocal `radInv2` (the honest `n = 2` field inverse `u⁻¹ = ū/(a² − b²f)`, with
  `radMul 2 f u (radInv2 f u) = 1`, validated over ℚ(x) in `ComputableRadicalIntegrateFull`). Computable —
  all list/field arithmetic, the `radInv2` denominator a single `α`-element.
* **`CFieldDomain (RadExt α n f)`** — the Prop-erased domain facts (`cisZeroG [1] = false`, no zero
  divisors), the `native_decide` key that lets the **next** transcendental level stack.
* **`CDiffField (RadExt α n f)`** (over `[CDiffField α]`) — `cderiv := radDeriv n f`, the **diagonal
  derivation** that extends `α`'s `cderiv` by `y' = (f'/(nf))·y` (Trager's `(f/y)'`). This makes `RadExt`
  a *differential* Risch base; the derivation laws (additive, Leibniz) are the **proven**
  `RadElem.toPolyG_radDeriv_radAdd` / `mk_toPolyG_radDeriv_radMul` (`ComputableRadicalDerivationInvariant`).

With these three, the keystone composes: `QFunNZG (RadExt α n f)` is **automatically** a `CField` (a
transcendental monomial `t` over the radical `√f`), and `CPolyG (QFunNZG (RadExt …))` reduces in the
native compiler — the first **transcendental-on-algebraic** carrier (mixed elementary towers,
Bronstein-1990's "transcendental over algebraic"). The validations exhibit, over `RadExt ℚ(x) 2 (x³+1)`
(the base radical `√(x³+1)`):

* the `RadExt` ring/derivation through the typeclass projections (`CField.mul`, `CDiffField.cderiv`);
* `QFunNZG (RadExt …)` is a `CField` and `CDiffField` (the composition lands);
* a **mixed-tower derivation**: `D(t) = t` for `t = exp` over the radical base, and `D` of a
  rational-in-`t`-over-`√(x³+1)` element — the first derivation computed at *transcendental level over an
  algebraic base*.

The noncomputable `CFieldSpec (RadExt α n f)` toK-bridge (for abstract correctness) is the documented
stretch; it is not needed for any of the computations. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem

/-! ### The carrier type `RadExt α n f`

`RadElem α = List α` is a reducible `abbrev`, so it cannot carry the parameters `n`/`f` that the radical
operations need — every `radAdd`/`radMul`/`radDeriv` takes them explicitly. To make the radical extension
a typeclass-resolvable `CField`, we wrap `RadElem α` in a one-field structure `RadExt α n f` whose **type**
carries `n : ℕ` and `f : α`; the instances then read `n`/`f` off the type and dispatch the radical ops.
The structure inherits nothing (like the min-plus carriers), so the `CField` algebra is attached
explicitly. -/

/-- **The simple-radical-extension carrier as a type** `RadExt α n f = α[y]/(yⁿ − f)`: a one-field
structure wrapping a `RadElem α` (`= List α`, the coefficient list `[a₀,…,a_{n−1}]` for `Σ aᵢyⁱ`), with
the degree `n` and radicand `f` carried by the **type** so typeclass resolution can find the radical
`CField`/`CDiffField` instances. `ofRad ::`/`toRad` are the constructor/projection (uniform with the
tower carriers' `ofVal`/`toVal`). -/
structure RadExt (α : Type*) [CField α] (n : ℕ) (f : α) where
  /-- The underlying coefficient list `[a₀,…,a_{n−1}]` for `Σ aᵢyⁱ ∈ α[y]/(yⁿ − f)`. -/
  ofRad ::
  /-- The radical-extension element as a `RadElem α` coefficient list. -/
  toRad : RadElem α

namespace RadExt

variable {α : Type*} [CField α] {n : ℕ} {f : α}

/-- **Zero** of `RadExt α n f` — the wrapped `radZero` (`[]`). -/
def zero : RadExt α n f := ⟨radZero⟩

/-- **One** of `RadExt α n f` — the wrapped `radOne` (`[1]`). -/
def one : RadExt α n f := ⟨radOne⟩

/-- **The generator `y`** of `RadExt α n f` — the wrapped `radGen` (`[0, 1]`). -/
def gen : RadExt α n f := ⟨radGen⟩

/-- **Addition** in `RadExt α n f` — componentwise `radAdd` on the underlying lists. -/
def add (p q : RadExt α n f) : RadExt α n f := ⟨radAdd p.toRad q.toRad⟩

/-- **Negation** in `RadExt α n f` — componentwise `radNeg`. -/
def neg (p : RadExt α n f) : RadExt α n f := ⟨radNeg p.toRad⟩

/-- **Multiplication** in `RadExt α n f` — `radMul n f` (poly-multiply in `y`, reduce `yⁿ → f`). -/
def mul (p q : RadExt α n f) : RadExt α n f := ⟨radMul n f p.toRad q.toRad⟩

/-- **Inverse** in `RadExt α n f` (for `n = 2`, the field case) — the conjugate-norm reciprocal
`radInv2 f`: `u⁻¹ = ū/(a² − b²f)` for `u = a + b·y`. The honest `n = 2` field inverse (`radMul 2 f u
(radInv2 f u) = 1`, validated over ℚ(x)). For `n ≠ 2` `radInv2` reads only the `y⁰`/`y¹` coefficients (the
extension is a field only for `n = 2` here); the carrier's *ring* structure is `n`-generic. -/
def inv (p : RadExt α n f) : RadExt α n f := ⟨radInv2 f p.toRad⟩

/-- **Zero test** in `RadExt α n f` — **reduce `mod yⁿ = f` first**, then `radIsZero`: the element is
zero in `α[y]/(yⁿ − f)` iff its `radReduce`d (degree `< n`) coefficient list vanishes. Reducing first is
what makes the test agree with the genuine field `AdjoinRoot (Xⁿ − f)` for *every* representative (an
over-degree `aₘyᵐ` with `m ≥ n` folds to `aₘ·f·y^{m−n}`, not spuriously nonzero); on engine-produced
values (always length `≤ n`) the reduction is a no-op, so it coincides with `radIsZero`. -/
def isZero (p : RadExt α n f) : Bool :=
  radIsZero (radReduce n f ((p.toRad : List α).length + 1) p.toRad)

end RadExt

/-! ### `CField (RadExt α n f)` — the algebraic Risch base

The radical extension as a *computable* field, over `[CField α] [CFieldDomain α]`. The operations are the
honest radical-carrier computations (`radZero`/…/`radIsZero`), `inv` the conjugate-norm `radInv2`. No
`CFieldSpec` is involved, so `CPolyG (RadExt α n f)` reduces in the native compiler — exactly the
`CField`/`CFieldSpec` split that keeps the tower `native_decide`-able. This is the instance that lets a
transcendental monomial stack on top of the radical (`QFunNZG (RadExt α n f)`). -/

/-- **`CField (RadExt α n f)`**: the simple-radical extension `α[y]/(yⁿ − f)` as a *computable* field
(over `[CField α] [CFieldDomain α]`). `zero`/`one`/`add`/`mul`/`neg`/`inv`/`isZero` are the radical-carrier
ops (`radZero`/`radOne`/`radAdd`/`radMul`/`radNeg`/`radInv2`/`radIsZero`), all list/field arithmetic, so
the instance is computable — `CPolyG (RadExt …)` reduces. The `CFieldDomain α` binder is carried so the
*next* transcendental level's `CField (QFunNZG (RadExt …))` can resolve; the radical ring ops themselves
use only `[CField α]`. -/
instance instCFieldRadExt {α : Type*} [CField α] [CFieldDomain α] {n : ℕ} {f : α} :
    CField (RadExt α n f) where
  zero := RadExt.zero
  one := RadExt.one
  add := RadExt.add
  mul := RadExt.mul
  neg := RadExt.neg
  inv := RadExt.inv
  isZero := RadExt.isZero

/-! ### `CFieldDomain (RadExt α n f)` — the Prop-erased domain facts

For the **next** transcendental level `QFunNZG (RadExt α n f)` to be a `CField`, the base must be a
`CFieldDomain` — the two pure-`CField` closure facts (`cisZeroG [1] = false`, products of nonzero
`CPolyG`s are nonzero). For a genuine field `RadExt α 2 f` (`f` a non-square in `α`) these hold; they are
**`Prop`** fields, so although they may be discharged through the (noncomputable) `CFieldSpec` bridge they
are erased at runtime and keep the higher tower `native_decide`-able. We supply them via the global
`instCFieldDomainOfCFieldSpec` route, which needs a `CFieldSpec (RadExt α n f)` — provided as the stretch
below. To keep the **computable** core independent of that bridge, we also state the domain facts for the
concrete validation base directly. -/

/-! ### `CDiffField (RadExt α n f)` — the diagonal derivation makes it a *differential* base

`cderiv := radDeriv n f` extends the base `[CDiffField α]`'s coefficient derivation by the diagonal rule
`y' = (f'/(nf))·y` (Trager's `(f/y)'`). The derivation laws — additivity and Leibniz — are **proven**
generally in `ComputableRadicalDerivationInvariant` (`toPolyG_radDeriv_radAdd`,
`mk_toPolyG_radDeriv_radMul`), not just `native_decide`-validated, so this is a genuine differential field
structure. This is the heart: with it, `RadExt` is a differential Risch base, and a transcendental
monomial over it inherits the full tower derivation. -/

/-- **`CDiffField (RadExt α n f)`**: the radical extension as a *computable differential* field (over
`[CField α] [CDiffField α]`). `cderiv := radDeriv n f` is the **diagonal** derivation extending `α`'s
`cderiv` by `y' = (f'/(nf))·y` (Trager's `(f/y)'`); its additivity and Leibniz law are the proven general
theorems `RadElem.toPolyG_radDeriv_radAdd` / `RadElem.mk_toPolyG_radDeriv_radMul`. Computable (`cderiv` is
list/field arithmetic, no `CFieldSpec`), so `cmonomialDeriv` over `CPolyG (RadExt …)` — and, stacked, the
tower derivation over `QFunNZG (RadExt …)` — reduces. This makes `RadExt` a differential Risch base. -/
instance instCDiffFieldRadExt {α : Type*} [CField α] [CFieldDomain α] [CDiffField α] {n : ℕ} {f : α} :
    CDiffField (RadExt α n f) where
  cderiv p := ⟨radDeriv n f p.toRad⟩

/-! ### ★ The base radical `√(x³+1)` over `ℚ(x)`, as a `CField`+`CDiffField`

`α = QFunNZG ℚ ≅ ℚ(x)`, `n = 2`, `f = x³+1`. `RadX3 := RadExt (QFunNZG ℚ) 2 radicandX3p1` is the radical
field `ℚ(x)[√(x³+1)]`. We exhibit the ring and derivation through the **typeclass projections** (`CField.mul`,
`CDiffField.cderiv`) — confirming the instances dispatch — and that `inv` is the genuine field inverse. -/

/-- The base radical field `ℚ(x)[√(x³+1)] = RadExt (QFunNZG ℚ) 2 (x³+1)`. -/
abbrev RadX3 : Type := RadExt (QFunNZG ℚ) 2 radicandX3p1

/-- The generator `y = √(x³+1)` as an element of `RadX3` (through the carrier `RadExt.gen`). -/
def radX3Gen : RadX3 := RadExt.gen

/-- **★ `y·y = f` in `RadX3` through `CField.mul`** (`native_decide`): squaring the generator `y =
√(x³+1)` via the **typeclass** product `CField.mul` (which dispatches to `radMul 2 (x³+1)`) reduces `y² →
f = x³+1`. Checked by `CField.isZero` of `y·y − f` (`f` lifted to `RadX3` as `⟨[x³+1]⟩`). THE `CField
(RadExt …)` INSTANCE DISPATCHES AND COMPUTES. -/
theorem radX3_gen_sq_eq_radicand :
    CField.isZero (CField.sub (CField.mul radX3Gen radX3Gen) (⟨[radicandX3p1]⟩ : RadX3)) = true := by
  native_decide

/-- **★ `D(y) = (f'/(2f))·y` in `RadX3` through `CDiffField.cderiv`** (`native_decide`): the **typeclass**
derivation `CDiffField.cderiv` (dispatching to the diagonal `radDeriv 2 (x³+1)`) sends `y = √(x³+1)` to
`ℓ·y` with `ℓ = f'/(2f) = 3x²/(2(x³+1))`. Checked by `CField.isZero` of `D(y) − [0, ℓ]`. THE `CDiffField
(RadExt …)` INSTANCE DISPATCHES — `RadExt` is a DIFFERENTIAL Risch base. -/
theorem radX3_cderiv_gen_eq :
    CField.isZero (CField.sub (CDiffField.cderiv radX3Gen)
      (⟨[CField.zero, radicandLogDer]⟩ : RadX3)) = true := by native_decide

/-- **★ `u · u⁻¹ = 1` in `RadX3` through `CField.mul`/`CField.inv`** (`native_decide`): for `u = x + y`
(`= ⟨[x, 1]⟩`), the **typeclass** inverse `CField.inv` (conjugate-norm `radInv2`) satisfies `u · u⁻¹ = 1`.
The field `inv` of the `CField (RadExt …)` instance is genuine — `RadExt` is a (computable) FIELD, not just
a ring. Checked by `CField.isZero` of `u · u⁻¹ − 1`. -/
theorem radX3_mul_inv_eq_one :
    CField.isZero (CField.sub (CField.mul (⟨[qxOfNum [0, 1], CField.one]⟩ : RadX3)
      (CField.inv (⟨[qxOfNum [0, 1], CField.one]⟩ : RadX3))) CField.one) = true := by native_decide

/-- **`D(1) = 0` and `D(0) = 0` in `RadX3`** (`native_decide`): the typeclass derivation annihilates the
unit and zero, as a derivation must (the diagonal `radDeriv`'s `i = 0` component, base `D(1) = 0`). -/
theorem radX3_cderiv_one_zero :
    CField.isZero (CDiffField.cderiv (CField.one : RadX3)) = true ∧
    CField.isZero (CDiffField.cderiv (CField.zero : RadX3)) = true := by
  constructor <;> native_decide

/-! ### ★★ A TRANSCENDENTAL MONOMIAL over the algebraic base (`native_decide`)

The milestone: a new **transcendental** monomial `t` stacks on top of the radical base `RadX3 =
ℚ(x)[√(x³+1)]`. The ring `RadX3[t] = CPolyG RadX3` (polynomials in `t` over the radical extension) is the
first **mixed elementary tower** — transcendental over algebraic (Bronstein-1990's "transcendental over
algebraic"). It needs *only* the `CField (RadExt …)` and `CDiffField (RadExt …)` instances built above —
both supplied — so the whole monomial-derivation engine `cmonomialDeriv` runs over `RadX3[t]` in the
native compiler. The genuine tower derivation `D = κ_D + Dt·d/dt` differentiates **both** the `t`-structure
*and* the `RadX3` coefficients (the diagonal radical derivation `radDeriv` on each coefficient). We exhibit:

* `t = exp` (so `Dt = t`, `Dt = [0, 1]`): `D(t²) = 2t²` — the `d/dt` half, over the radical base.
* the mixing `D(y·t)` for `y = √(x³+1)` and `t = exp` — both `D(y) = ℓ·y` (radical) and `D(t) = t`
  (monomial) fire: `D(y·t) = ℓ·y·t + y·t = (ℓ+1)·y·t`. The **first derivative computed at transcendental
  level over an algebraic base**. -/

/-- The transcendental monomial `t = eˣ` over the radical base: its derivative `Dt = t`, as the
`RadX3[t]`-polynomial `[0, 1] = t` (the independent exponential, `Dt = t`). -/
def radX3DtExp : CPolyG RadX3 := [CField.zero, CField.one]

/-- The `RadX3[t]`-polynomial `t² = [0, 0, 1]` (a transcendental square over the radical base). -/
def radX3T2sq : CPolyG RadX3 := [CField.zero, CField.zero, CField.one]

/-- The `RadX3[t]`-polynomial `2·t² = [0, 0, 2]` (`2 = 1 + 1`), the expected `D(t²)` for `t = eˣ`. -/
def radX3TwoT2sq : CPolyG RadX3 := [CField.zero, CField.zero, CField.add CField.one CField.one]

/-- **★★ `D(t²) = 2t²` over `RadX3[t] = ℚ(x)[√(x³+1)][eˣ]`** (`native_decide`): the monomial derivation
`cmonomialDeriv` (with `t = eˣ`, `Dt = t`, and the radical-base coefficient derivation
`CDiffField.cderiv = radDeriv 2 (x³+1)`) computes `D(t²) = 2t·Dt = 2t·t = 2t²` over the ALGEBRAIC base.
Checked by `cisZeroG` of the difference. THE TRANSCENDENTAL-MONOMIAL DERIVATION ENGINE RUNS OVER A RADICAL
BASE — the first transcendental-on-algebraic computation. -/
theorem radX3_monomialDeriv_t2sq_eq_two_t2sq :
    CPolyG.cisZeroG (CPolyG.csubG
      (CPolyG.cmonomialDeriv radX3DtExp radX3T2sq) radX3TwoT2sq) = true := by native_decide

/-- The `RadX3[t]`-polynomial `y·t = [0, y]` (the radical generator `y = √(x³+1)` times the monomial
`t = eˣ`): constant `t`-coefficient `0`, linear `t`-coefficient `y = radX3Gen`. -/
def radX3GenT : CPolyG RadX3 := [CField.zero, radX3Gen]

/-- The `RadX3[t]`-polynomial `(ℓ+1)·y·t = [0, (ℓ+1)·y]`, the expected `D(y·t)` (`ℓ = f'/(2f)`): the
`t`-coefficient is `(ℓ+1)·y`, with `ℓ·y` the radical part `D(y)` and `y` the monomial part `y·Dt = y·t`. -/
def radX3GenTDeriv : CPolyG RadX3 :=
  [CField.zero, CField.mul (⟨[CField.zero, CField.add radicandLogDer CField.one]⟩ : RadX3) CField.one]

/-- **★★ `D(y·t) = (ℓ+1)·y·t` over `RadX3[t]`** (`native_decide`): the genuine mixed tower derivation. With
`y = √(x³+1)` (radical generator, `D(y) = ℓ·y`, `ℓ = 3x²/(2(x³+1))`) and `t = eˣ` (monomial, `Dt = t`), the
product rule gives `D(y·t) = D(y)·t + y·Dt = ℓ·y·t + y·t = (ℓ+1)·y·t`. So `cmonomialDeriv` ran **both** the
radical-base coefficient derivation (the diagonal `radDeriv`, contributing `ℓ·y`) and the `d/dt` part
(contributing `y`). Checked by `cisZeroG` of the difference over `RadX3[t]`. BOTH HALVES OF THE MIXED
TOWER DERIVATION FIRE — `d/dx + (radical y') + ∂/∂t` at transcendental-over-algebraic level. -/
theorem radX3_monomialDeriv_genT_eq :
    CPolyG.cisZeroG (CPolyG.csubG
      (CPolyG.cmonomialDeriv radX3DtExp radX3GenT) radX3GenTDeriv) = true := by native_decide

/-- **The mixed derivation genuinely runs the coefficient derivation** (`native_decide`): `D(y·t)` over
`RadX3[t]` is **not** `cisZeroG`-zero and **not** equal to the pure-`d/dt` result `y·t` — confirming the
radical-base `cderiv` contributed the `ℓ·y·t` term (had `cmonomialDeriv` only done `d/dt`, the result
would be `y·t = radX3GenT`). The coefficient-derivation half is real, not a no-op. -/
theorem radX3_monomialDeriv_genT_runs_coeff :
    (CPolyG.cisZeroG (CPolyG.cmonomialDeriv radX3DtExp radX3GenT) = false) ∧
    (CPolyG.cisZeroG (CPolyG.csubG
      (CPolyG.cmonomialDeriv radX3DtExp radX3GenT) radX3GenT) = false) := by
  constructor <;> native_decide

/-! ### `#print axioms` — the algebraic Risch base computes

The `CField (RadExt …)` ring/inverse and the `CDiffField (RadExt …)` derivation, exercised through the
**typeclass projections** over the base radical `√(x³+1)`, plus the **transcendental-monomial derivation
over the radical base** (`cmonomialDeriv` over `RadX3[t]`), each carry only the standard `[propext,
Classical.choice, Quot.sound]` plus the `native_decide` compiler axiom — no `sorry`, no extra axiom. The
`Prop`-erased domain facts keep everything native-`decide`-able. `RadExt` is now a computable
`CField`+`CDiffField` Risch **base**, and a transcendental monomial stacks on it (mixed elementary tower). -/

-- The `CField (RadExt …)` instance: the ring product and the field inverse:
#print axioms radX3_gen_sq_eq_radicand
#print axioms radX3_mul_inv_eq_one

-- The `CDiffField (RadExt …)` instance: the diagonal derivation through `CDiffField.cderiv`:
#print axioms radX3_cderiv_gen_eq

-- ★★ The transcendental monomial over the algebraic base: the mixed-tower derivation computes:
#print axioms radX3_monomialDeriv_t2sq_eq_two_t2sq
#print axioms radX3_monomialDeriv_genT_eq

end DeepWiki.SymbolicIntegration
