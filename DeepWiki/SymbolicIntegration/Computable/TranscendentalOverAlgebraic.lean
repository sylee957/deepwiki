import DeepWiki.SymbolicIntegration.Computable.Algebraic.RadicalExtension
import DeepWiki.SymbolicIntegration.Computable.Algebraic.RadicalDerivationInvariant
import DeepWiki.SymbolicIntegration.Computable.Algebraic.RadicalAssembly
import DeepWiki.SymbolicIntegration.Computable.Tower.Field
import DeepWiki.SymbolicIntegration.Computable.Tower.Deriv
import DeepWiki.SymbolicIntegration.Computable.Tower.RischDE
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.RingTheory.AdjoinRoot

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
  `radMul 2 f u (radInv2 f u) = 1`, validated over ℚ(x) in `ComputableRadicalAssembly`). Computable —
  all list/field arithmetic, the `radInv2` denominator a single `α`-element.
* **`CFieldDomain (RadExt α n f)`** — the Prop-erased domain facts (`cisZeroG [1] = false`, no zero
  divisors), the `native_decide` key that lets the **next** transcendental level stack.
* **`CDiffField (RadExt α n f)`** (over `[CDiffField α]`) — `cderiv := radDeriv n f`, the **diagonal
  derivation** that extends `α`'s `cderiv` by `y' = (f'/(nf))·y` (Trager's `(f/y)'`). This makes `RadExt`
  a *differential* Risch base; the derivation laws (additive, Leibniz) are the **proven**
  `RadElem.toPolyG_radDeriv_radAdd` / `mk_toPolyG_radDeriv_radMul` (`ComputableRadicalDerivationInvariant`).
* **`CRischField (RadExt α n f)`** (over `[CDiffField α] [CRischField α]`) — the base RDE-over-the-field
  solve `Dz + B·z = C` by **scalar decoupling** (`radExtRischDESolve`): the diagonal `radDeriv` splits a
  *scalar*-`B` equation into the `n` per-`y`-power base RDEs `Dzᵢ + (b₀ + (i:α)·ℓ)·zᵢ = Cᵢ` over `α`
  (`ℓ = f'/(nf)`), each solved by the base `[CRischField α]`; a non-scalar `B` is the coupled-system case
  (Bronstein Ch. 8) and returns `none`. This is the method the **§6.6 cancellation cases recurse into** — so
  the transcendental Risch integrator now recurses *through* the algebraic level, not merely over it. It
  **generalizes** the per-base `CRischField RadX3` stub into one instance for every `[CField α] …`.

With these three, the keystone composes: `QFunNZG (RadExt α n f)` is **automatically** a `CField` (a
transcendental monomial `t` over the radical `√f`), and `CPolyG (QFunNZG (RadExt …))` reduces in the
native compiler — the first **transcendental-on-algebraic** carrier (mixed elementary towers,
Bronstein-1990's "transcendental over algebraic"). The `CFieldDomain` hypothesis is **discharged
concretely** for the worked base `RadExt ℚ(x) 2 (x³+1)`: the noncomputable `CFieldSpec (RadExt α 2 f)`
toK-bridge into `K = AdjoinRoot (X² − C(toK f))` (a `Field` because `X² − (x³+1)` is **irreducible** over
ℚ(x) — `x³+1` is not a square, `irreducible_radX3`) feeds the global `instCFieldDomainOfCFieldSpec`, so
`CFieldDomain RadX3` resolves with **no hypothesis**. The validations exhibit, over `RadExt ℚ(x) 2 (x³+1)`:

* the `RadExt` ring/derivation through the typeclass projections (`CField.mul`, `CDiffField.cderiv`);
* a **mixed-tower derivation**: `D(t²) = 2t²` and `D(y·t) = (ℓ+1)·y·t` over the radical base — the first
  derivative computed at *transcendental level over an algebraic base*;
* unconditionally (no `[CFieldDomain]` assumption): `QFunNZG RadX3 ≅ ℚ(x)[√(x³+1)](t)` is a `CField`
  and `CDiffField`, and `D(t) = 1` / `t · t⁻¹ = 1` compute over it by `native_decide` (the `CFieldDomain`
  Prop-erasure keeps the tower native-compilable) — the first fully-discharged transcendental-on-algebraic
  computation.

The bridge is noncomputable (routes through `AdjoinRoot`), but only the `CFieldDomain` Prop is consumed, so
the tower stays `native_decide`-able. -/

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

/-- The simple-radical-extension carrier as a type `RadExt α n f = α[y]/(yⁿ − f)`: a one-field
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

/-- Zero of `RadExt α n f` — the wrapped `radZero` (`[]`). -/
def zero : RadExt α n f := ⟨radZero⟩

/-- One of `RadExt α n f` — the wrapped `radOne` (`[1]`). -/
def one : RadExt α n f := ⟨radOne⟩

/-- The generator `y` of `RadExt α n f` — the wrapped `radGen` (`[0, 1]`). -/
def gen : RadExt α n f := ⟨radGen⟩

/-- Canonicalize a `RadElem` to degree `< n` `radCanon n f u := cnormG (radReduce n f (len u + 1) u)`
— fold every `yᵐ` with `m ≥ n` down by `yⁿ = f` and strip trailing zeros, giving a **normalized**
representative of length `≤ n`. The outer `cnormG` guarantees the result length `≤ n` outright (so the `mk
∘ toPolyG` bridge into `AdjoinRoot (Xⁿ − f)` is faithful on it). On engine-produced values (already length
`≤ n`, no trailing zeros) it is a no-op. -/
def radCanon (n : ℕ) (f : α) (u : RadElem α) : RadElem α :=
  CPolyG.cnormG (radReduce n f ((u : List α).length + 1) u)

/-- Addition in `RadExt α n f` — componentwise `radAdd`, canonicalized to degree `< n`. -/
def add (p q : RadExt α n f) : RadExt α n f := ⟨radCanon n f (radAdd p.toRad q.toRad)⟩

/-- Negation in `RadExt α n f` — componentwise `radNeg`, canonicalized to degree `< n`. -/
def neg (p : RadExt α n f) : RadExt α n f := ⟨radCanon n f (radNeg p.toRad)⟩

/-- Multiplication in `RadExt α n f` — `radMul n f` (poly-multiply in `y`, reduce `yⁿ → f`),
canonicalized (`radMul` already folds, so this is idempotent). -/
def mul (p q : RadExt α n f) : RadExt α n f := ⟨radCanon n f (radMul n f p.toRad q.toRad)⟩

/-- Inverse in `RadExt α n f` (for `n = 2`, the field case) — the **canonicalized** conjugate-norm
reciprocal: `radInvCanon n f u := radCanon n f (radInv2 f (radCanon n f u))`, reducing the input to a
degree-`< n` rep `a + b·y` *before* `radInv2` and the output afterward. Canonicalizing the input is what
makes the inverse faithful — `radInv2` reads only `y⁰`/`y¹`, so it must see the *reduced* `a, b` (an
over-degree input would have its high terms silently dropped). On the reduced rep, `u⁻¹ = ū/(a² − b²f)` is
the honest `n = 2` field inverse (`radMul 2 f u (radInv2 f u) = 1`, validated over ℚ(x)). -/
def inv (p : RadExt α n f) : RadExt α n f := ⟨radCanon n f (radInv2 f (radCanon n f p.toRad))⟩

/-- Zero test in `RadExt α n f` — **reduce `mod yⁿ = f` first**, then `radIsZero`: the element is
zero in `α[y]/(yⁿ − f)` iff its `radReduce`d (degree `< n`) coefficient list vanishes. Reducing first is
what makes the test agree with the genuine field `AdjoinRoot (Xⁿ − f)` for *every* representative (an
over-degree `aₘyᵐ` with `m ≥ n` folds to `aₘ·f·y^{m−n}`, not spuriously nonzero); on engine-produced
values (always length `≤ n`) the reduction is a no-op, so it coincides with `radIsZero`. -/
def isZero (p : RadExt α n f) : Bool := radIsZero (radCanon n f p.toRad)

end RadExt

/-! ### `CField (RadExt α n f)` — the algebraic Risch base

The radical extension as a *computable* field, over `[CField α] [CFieldDomain α]`. The operations are the
honest radical-carrier computations (`radZero`/…/`radIsZero`), `inv` the conjugate-norm `radInv2`. No
`CFieldSpec` is involved, so `CPolyG (RadExt α n f)` reduces in the native compiler — exactly the
`CField`/`CFieldSpec` split that keeps the tower `native_decide`-able. This is the instance that lets a
transcendental monomial stack on top of the radical (`QFunNZG (RadExt α n f)`). -/

/-- `CField (RadExt α n f)`: the simple-radical extension `α[y]/(yⁿ − f)` as a *computable* field
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

/-! ### `CFieldDomain (RadExt α n f)` — the Prop-erased domain facts (the composition hypothesis)

For the **next** transcendental level `QFunNZG (RadExt α n f)` to be a `CField`, the base must be a
`CFieldDomain` — the two pure-`CField` closure facts (`cisZeroG [1] = false`, products of nonzero
`CPolyG`s are nonzero). For a genuine field `RadExt α 2 f` (`f` a non-square in `α`) these hold, and being
**`Prop`** fields they are erased at runtime, keeping a stacked tower `native_decide`-able. A *concrete*
`CFieldDomain (RadExt …)` instance routes through the global `instCFieldDomainOfCFieldSpec`, hence needs a
`CFieldSpec (RadExt α n f)` (the `AdjoinRoot` bridge — the documented stretch at the end of this file); it
is not shipped here. The composition section below instead carries `CFieldDomain RadX3` as an explicit
**hypothesis**, and shows the transcendental level resolves under it — the keystone-composes statement that
needs no concrete witness. -/

/-! ### `CDiffField (RadExt α n f)` — the diagonal derivation makes it a *differential* base

`cderiv := radDeriv n f` extends the base `[CDiffField α]`'s coefficient derivation by the diagonal rule
`y' = (f'/(nf))·y` (Trager's `(f/y)'`). The derivation laws — additivity and Leibniz — are **proven**
generally in `ComputableRadicalDerivationInvariant` (`toPolyG_radDeriv_radAdd`,
`mk_toPolyG_radDeriv_radMul`), not just `native_decide`-validated, so this is a genuine differential field
structure. This is the heart: with it, `RadExt` is a differential Risch base, and a transcendental
monomial over it inherits the full tower derivation. -/

/-- `CDiffField (RadExt α n f)`: the radical extension as a *computable differential* field (over
`[CField α] [CDiffField α]`). `cderiv := radDeriv n f` is the **diagonal** derivation extending `α`'s
`cderiv` by `y' = (f'/(nf))·y` (Trager's `(f/y)'`); its additivity and Leibniz law are the proven general
theorems `RadElem.toPolyG_radDeriv_radAdd` / `RadElem.mk_toPolyG_radDeriv_radMul`. Computable (`cderiv` is
list/field arithmetic, no `CFieldSpec`), so `cmonomialDeriv` over `CPolyG (RadExt …)` — and, stacked, the
tower derivation over `QFunNZG (RadExt …)` — reduces. This makes `RadExt` a differential Risch base. -/
instance instCDiffFieldRadExt {α : Type*} [CField α] [CFieldDomain α] [CDiffField α] {n : ℕ} {f : α} :
    CDiffField (RadExt α n f) where
  cderiv p := ⟨radDeriv n f p.toRad⟩

/-! ### `CRischField (RadExt α n f)` — the algebraic-level RDE by scalar decoupling

The base Risch-DE solve `crischDESolve B C : Option (RadExt α n f)` for `Dz + B·z = C` over the radical
field itself. This is **what lets the Risch integrator recurse *through* the algebraic level** — every §6.6
cancellation case over `RadExt α n f` (eq. 6.23 `RischDE(b, lc(c))`) now has a base solve, rather than a
transcendental integrator merely sitting on top of a fixed algebraic field.

The derivation `radDeriv n f` is **diagonal**: its `yⁱ`-component is `aᵢ ↦ D(aᵢ) + aᵢ·(i·ℓ)`,
`ℓ = logDerRadicand n f = f'/(nf)`. So when the coefficient `B` is a **scalar** (a `RadExt` whose `toRad`
is `[b₀]`-shaped — all `y`-components vanish), the product `B·z` is the diagonal scaling `b₀·zᵢ` per
component, and the RDE `Dz + B·z = C` **decouples** into the `n` independent **base** RDEs over `α`

`Dzᵢ + (b₀ + (i:α)·ℓ)·zᵢ = Cᵢ`   (`i = 0,…,n−1`),

each solved by `CRischField.crischDESolve` over the *base* field `α` — exactly the per-component
coefficient `b₀ + (cnatCastG i)·ℓ` that the diagonal `radDeriv`'s `i`-component carries. Reassembling
`z = RadExt.ofRad [z₀,…,z_{n−1}]` (`none` if any component fails) gives the radical-level solution.

A **non-scalar** `B` (genuine `y`-components) couples the components — the coupled-differential-system case
(Bronstein Ch. 8, `RischDECouple`). That is **honestly deferred**: `crischDESolve` returns `none` when `B`
is not scalar (its `y`-components do not all vanish), so the solver is *sound* (never returns a wrong
witness) and *complete on the decoupled (scalar-`B`) slice*. The §6.6 primitive/hyperexponential
cancellation cases call `crischDESolve b₀ (lc c)` / `crischDESolve (b₀ + m·η) (lc c)` with `b₀, η ∈ α`
lifted into `RadExt` as scalars, so the scalar branch is exactly the case those cancellations hit. -/

/-- Scalar test on a `RadExt` `RadExt.isScalar p`: `true` iff every `y`-component of `p` (everything
past the `y⁰` head) vanishes — `radIsZero (p.toRad).tail`. The decoupling base solve handles scalar
coefficients `B` (`b₀ + b₁y + … = b₀`); a non-scalar `B` is the coupled-system case. -/
def RadExt.isScalar {α : Type*} [CField α] {n : ℕ} {f : α} (p : RadExt α n f) : Bool :=
  RadElem.radIsZero ((p.toRad : List α).tail)

/-- Scalar-decoupling base RDE solve `radExtRischDESolve B C : Option (RadExt α n f)` for
`Dz + B·z = C` over `RadExt α n f`, using the diagonality of `radDeriv n f`. For a **scalar** `B`
(`RadExt.isScalar B`, so `B = b₀`), the equation decouples per `y`-power into the `n` base RDEs
`Dzᵢ + (b₀ + (i:α)·ℓ)·zᵢ = Cᵢ` over `α` (`ℓ = logDerRadicand n f = f'/(nf)`), each solved by
`CRischField.crischDESolve` — the coefficient `b₀ + (cnatCastG i)·ℓ` matches the diagonal `radDeriv`'s
`i`-component exactly (`CField.mul (CPolyG.cnatCastG i) ℓ`). The `n` solutions `z₀,…,z_{n−1}` (`Cᵢ` read by
`getD i CField.zero`) reassemble to `z = RadExt.ofRad [z₀,…]` via `List.mapM` over `Option` (`none` if any
component is unsolvable). A non-scalar `B` (genuine `y`-coupling) is the coupled-system case (Bronstein
Ch. 8) and returns `none`. The **abstract invariant** — `radExtRischDESolve B C = some z → radDeriv z + B·z
= C` for scalar `B`, from the diagonal `radDeriv` plus per-component `CRischField α` correctness — follows
the native_decide-validated tower's design (no `CRischFieldSpec` spec layer exists yet); it is
native_decide-validated here (`radX3Risch_solves_rde`) and the abstract proof is a follow-up. -/
def radExtRischDESolve {α : Type*} [CField α] [CDiffField α] [CRischField α] {n : ℕ} {f : α}
    (B C : RadExt α n f) : Option (RadExt α n f) :=
  if RadExt.isScalar B then
    let b₀ : α := (B.toRad : List α).headD CField.zero
    let ℓ : α := RadElem.logDerRadicand n f
    (((List.range n).mapM fun i =>
      let coeff : α := CField.add b₀ (CField.mul (CPolyG.cnatCastG i) ℓ)
      let Ci : α := (C.toRad : List α).getD i CField.zero
      CRischField.crischDESolve coeff Ci).map RadExt.ofRad)
  else none

/-- `CRischField (RadExt α n f)` — the base Risch-DE solver over the radical field, by **scalar
decoupling** (`radExtRischDESolve`). For a scalar coefficient `B = b₀`, the diagonal `radDeriv` makes
`Dz + B·z = C` split into the `n` base RDEs `Dzᵢ + (b₀ + (i:α)·ℓ)·zᵢ = Cᵢ` over `α`, each dispatched to
the base `[CRischField α]` solve; a non-scalar `B` (coupled system, Bronstein Ch. 8) returns `none`.
Computable (list/field arithmetic + the base `crischDESolve`), so the Risch integrator over `RadExt[t]`
recurses **through** the algebraic level in the native compiler. This **generalizes** the per-base ad-hoc
`CRischField RadX3` stub: it is the one instance supplying `CRischField (RadExt α n f)` for *every*
`[CField α] [CDiffField α] [CFieldDomain α] [CRischField α]`. -/
instance instCRischFieldRadExt {α : Type*} [CField α] [CDiffField α] [CFieldDomain α] [CRischField α]
    {n : ℕ} {f : α} : CRischField (RadExt α n f) where
  crischDESolve := radExtRischDESolve

/-! ### The base radical `√(x³+1)` over `ℚ(x)`, as a `CField`+`CDiffField`

`α = QFunNZG ℚ ≅ ℚ(x)`, `n = 2`, `f = x³+1`. `RadX3 := RadExt (QFunNZG ℚ) 2 radicandX3p1` is the radical
field `ℚ(x)[√(x³+1)]`. We exhibit the ring and derivation through the **typeclass projections** (`CField.mul`,
`CDiffField.cderiv`) — confirming the instances dispatch — and that `inv` is the genuine field inverse. -/

/-- The base radical field `ℚ(x)[√(x³+1)] = RadExt (QFunNZG ℚ) 2 (x³+1)`. -/
abbrev RadX3 : Type := RadExt (QFunNZG ℚ) 2 radicandX3p1

/-- The generator `y = √(x³+1)` as an element of `RadX3` (through the carrier `RadExt.gen`). -/
def radX3Gen : RadX3 := RadExt.gen

/-- `y·y = f` in `RadX3` through `CField.mul` (`native_decide`): squaring the generator `y =
√(x³+1)` via the typeclass product `CField.mul` (which dispatches to `radMul 2 (x³+1)`) reduces `y² →
f = x³+1`. Checked by `CField.isZero` of `y·y − f` (`f` lifted to `RadX3` as `⟨[x³+1]⟩`). -/
theorem radX3_gen_sq_eq_radicand :
    CField.isZero (CField.sub (CField.mul radX3Gen radX3Gen) (⟨[radicandX3p1]⟩ : RadX3)) = true := by
  native_decide

/-- `D(y) = (f'/(2f))·y` in `RadX3` through `CDiffField.cderiv` (`native_decide`): the typeclass
derivation `CDiffField.cderiv` (dispatching to the diagonal `radDeriv 2 (x³+1)`) sends `y = √(x³+1)` to
`ℓ·y` with `ℓ = f'/(2f) = 3x²/(2(x³+1))`. Checked by `CField.isZero` of `D(y) − [0, ℓ]`. -/
theorem radX3_cderiv_gen_eq :
    CField.isZero (CField.sub (CDiffField.cderiv radX3Gen)
      (⟨[CField.zero, radicandLogDer]⟩ : RadX3)) = true := by native_decide

/-- `u · u⁻¹ = 1` in `RadX3` through `CField.mul`/`CField.inv` (`native_decide`): for `u = x + y`
(`= ⟨[x, 1]⟩`), the typeclass inverse `CField.inv` (conjugate-norm `radInv2`) satisfies `u · u⁻¹ = 1`.
The field `inv` of the `CField (RadExt …)` instance is genuine — `RadExt` is a computable field, not just
a ring. Checked by `CField.isZero` of `u · u⁻¹ − 1`. -/
theorem radX3_mul_inv_eq_one :
    CField.isZero (CField.sub (CField.mul (⟨[qxOfNum [0, 1], CField.one]⟩ : RadX3)
      (CField.inv (⟨[qxOfNum [0, 1], CField.one]⟩ : RadX3))) CField.one) = true := by native_decide

/-- `D(1) = 0` and `D(0) = 0` in `RadX3` (`native_decide`): the typeclass derivation annihilates the
unit and zero, as a derivation must (the diagonal `radDeriv`'s `i = 0` component, base `D(1) = 0`). -/
theorem radX3_cderiv_one_zero :
    CField.isZero (CDiffField.cderiv (CField.one : RadX3)) = true ∧
    CField.isZero (CDiffField.cderiv (CField.zero : RadX3)) = true := by
  constructor <;> native_decide

/-! ### The generic `CRischField (RadExt …)` solves a genuine algebraic RDE (`native_decide`)

The validation that `instCRischFieldRadExt` does real algebraic-RDE work — not a trivial
`f = 0 ∧ g = 0 ↦ 0` passthrough. Over `RadX3 = ℚ(x)[√(x³+1)]` we take a nonzero scalar
coefficient `B = 1` and a right-hand side `C` carrying a genuine `y`-component, then solve the RDE
`Dz + B·z = C` by `CRischField.crischDESolve` (which dispatches to `radExtRischDESolve`'s scalar
decoupling) and certify `radDeriv z + B·z = C` exactly.

`C` is constructed from a chosen target `z = x + 2·y` (`z₀ = x ∈ ℚ(x)`, `z₁ = 2 ∈ ℚ`) as
`C := radDeriv z + B·z = [1 + x, 2ℓ + 2]` (`ℓ = f'/(2f) = 3x²/(2(x³+1))`, so the `y`-component
`2ℓ + 2 = 3x²/(x³+1) + 2 ≠ 0`). The decoupling splits the solve into the two **base** RDEs over ℚ(x):
`Dz₀ + 1·z₀ = 1 + x` (giving `z₀ = x`) and `Dz₁ + (1 + ℓ)·z₁ = 2ℓ + 2` (a genuine **non-constant**
-coefficient RDE over ℚ(x), giving `z₁ = 2`) — each run by the level-1 `CRischField (QFunNZG ℚ)`. The
solver returns `some` and the residual `radDeriv z + B·z − C` vanishes. The generic algebraic RDE solver
DECOUPLES AND SOLVES, with a nonzero `B` and a `y`-component in `C` — genuine work. -/

/-- The scalar coefficient `B = 1 ∈ RadX3` (a `RadExt` with no `y`-component) for the algebraic-RDE
validation. -/
def radX3RischB : RadX3 := CField.one

/-- The target solution `z = x + 2·y ∈ RadX3` (constant `y`-coefficient `2`), from which the right-hand
side `C` is built. `z₁ = 2 ≠ 0`, so `radDeriv`'s diagonal `y`-component makes `C` carry a genuine `y`-term. -/
def radX3RischZ : RadX3 := ⟨[qxOfNum [0, 1], qxOfNum [2]]⟩

/-- The right-hand side `C = radDeriv z + B·z = [1 + x, 2ℓ + 2] ∈ RadX3` of the algebraic RDE
`Dz + B·z = C`, constructed from `radX3RischZ`/`radX3RischB`. Carries a genuine `y`-component
`2ℓ + 2 ≠ 0` (`ℓ = 3x²/(2(x³+1))`). -/
def radX3RischC : RadX3 :=
  ⟨RadElem.radAdd (RadElem.radDeriv 2 radicandX3p1 radX3RischZ.toRad)
    (RadElem.radMul 2 radicandX3p1 radX3RischB.toRad radX3RischZ.toRad)⟩

/-- The right-hand side `C` has a genuine `y`-component (`native_decide`): `radIsZero (C.toRad.tail)
= false` — `C`'s `y¹`-coefficient `2ℓ + 2 ≠ 0`, so the solve is a *real* coupled-looking algebraic RDE
(not a scalar `α`-equation in disguise), exactly the case the scalar-`B` decoupling must dispose. -/
theorem radX3Risch_C_has_y_component :
    RadElem.radIsZero ((radX3RischC.toRad : List (QFunNZG ℚ)).tail) = false := by native_decide

/-- The generic `crischDESolve` returns `some` on the algebraic RDE (`native_decide`): over
`RadX3 = ℚ(x)[√(x³+1)]`, `CRischField.crischDESolve B C` (`B = 1`, `C` with a `y`-component) succeeds —
the scalar decoupling found a solution to both base RDEs over ℚ(x). -/
theorem radX3Risch_solve_isSome :
    (CRischField.crischDESolve radX3RischB radX3RischC).isSome = true := by native_decide

/-- The generic `CRischField (RadExt …)` solves a genuine algebraic RDE: `radDeriv z + B·z = C`
(`native_decide`). `CRischField.crischDESolve B C` over `RadX3 = ℚ(x)[√(x³+1)]` returns `some z`, and `z`
satisfies the algebraic RDE `Dz + B·z = C` exactly — checked by `radIsZero` of `radDeriv z + B·z − C` (the
diagonal radical derivation). The coefficient `B = 1` is a nonzero scalar and `C` carries a genuine
`y`-component, so the solve decouples the radical RDE into the two base RDEs over ℚ(x)
(`Dz₀ + z₀ = 1+x`, `Dz₁ + (1+ℓ)z₁ = 2ℓ+2`) and dispatches each to the level-1 `CRischField (QFunNZG ℚ)` —
the Risch integrator recursing through the algebraic level. -/
theorem radX3Risch_solves_rde :
    (match CRischField.crischDESolve radX3RischB radX3RischC with
      | some z => RadElem.radIsZero (RadElem.radSub
          (RadElem.radAdd (RadElem.radDeriv 2 radicandX3p1 z.toRad)
            (RadElem.radMul 2 radicandX3p1 radX3RischB.toRad z.toRad)) radX3RischC.toRad)
      | none => false) = true := by native_decide

/-- A non-scalar coefficient `B` is honestly deferred (`native_decide`): with `B = y` (a genuine
`y`-component, `B.toRad = [0, 1]`, so `RadExt.isScalar B = false`), `crischDESolve B C` returns `none` —
the coupled-differential-system case (Bronstein Ch. 8) is **not** attempted, keeping the solver sound. The
scalar branch (above) is exactly the slice the §6.6 cancellation cases hit (`b₀, η ∈ α` lifted as scalars). -/
theorem radX3Risch_nonscalar_none :
    CRischField.crischDESolve (radX3Gen : RadX3) radX3RischC = none := by native_decide

/-! ### A transcendental monomial over the algebraic base (`native_decide`)

A new transcendental monomial `t` stacks on top of the radical base `RadX3 = ℚ(x)[√(x³+1)]`. The ring
`RadX3[t] = CPolyG RadX3` (polynomials in `t` over the radical extension) is a mixed elementary tower —
transcendental over algebraic (Bronstein-1990's "transcendental over algebraic"). It needs only the
`CField (RadExt …)` and `CDiffField (RadExt …)` instances built above, so the whole monomial-derivation
engine `cmonomialDeriv` runs over `RadX3[t]` in the native compiler. The genuine tower derivation
`D = κ_D + Dt·d/dt` differentiates both the `t`-structure and the `RadX3` coefficients (the diagonal
radical derivation `radDeriv` on each coefficient). We exhibit:

* `t = exp` (so `Dt = t`, `Dt = [0, 1]`): `D(t²) = 2t²` — the `d/dt` half, over the radical base.
* the mixing `D(y·t)` for `y = √(x³+1)` and `t = exp` — both `D(y) = ℓ·y` (radical) and `D(t) = t`
  (monomial) fire: `D(y·t) = ℓ·y·t + y·t = (ℓ+1)·y·t`. -/

/-- The transcendental monomial `t = eˣ` over the radical base: its derivative `Dt = t`, as the
`RadX3[t]`-polynomial `[0, 1] = t` (the independent exponential, `Dt = t`). -/
def radX3DtExp : CPolyG RadX3 := [CField.zero, CField.one]

/-- The `RadX3[t]`-polynomial `t² = [0, 0, 1]` (a transcendental square over the radical base). -/
def radX3T2sq : CPolyG RadX3 := [CField.zero, CField.zero, CField.one]

/-- The `RadX3[t]`-polynomial `2·t² = [0, 0, 2]` (`2 = 1 + 1`), the expected `D(t²)` for `t = eˣ`. -/
def radX3TwoT2sq : CPolyG RadX3 := [CField.zero, CField.zero, CField.add CField.one CField.one]

/-- `D(t²) = 2t²` over `RadX3[t] = ℚ(x)[√(x³+1)][eˣ]` (`native_decide`): the monomial derivation
`cmonomialDeriv` (with `t = eˣ`, `Dt = t`, and the radical-base coefficient derivation
`CDiffField.cderiv = radDeriv 2 (x³+1)`) computes `D(t²) = 2t·Dt = 2t·t = 2t²` over the algebraic base.
Checked by `cisZeroG` of the difference. -/
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

/-- `D(y·t) = (ℓ+1)·y·t` over `RadX3[t]` (`native_decide`): the genuine mixed tower derivation. With
`y = √(x³+1)` (radical generator, `D(y) = ℓ·y`, `ℓ = 3x²/(2(x³+1))`) and `t = eˣ` (monomial, `Dt = t`), the
product rule gives `D(y·t) = D(y)·t + y·Dt = ℓ·y·t + y·t = (ℓ+1)·y·t`. So `cmonomialDeriv` ran both the
radical-base coefficient derivation (the diagonal `radDeriv`, contributing `ℓ·y`) and the `d/dt` part
(contributing `y`). Checked by `cisZeroG` of the difference over `RadX3[t]`. -/
theorem radX3_monomialDeriv_genT_eq :
    CPolyG.cisZeroG (CPolyG.csubG
      (CPolyG.cmonomialDeriv radX3DtExp radX3GenT) radX3GenTDeriv) = true := by native_decide

/-- The mixed derivation genuinely runs the coefficient derivation (`native_decide`): `D(y·t)` over
`RadX3[t]` is not `cisZeroG`-zero and not equal to the pure-`d/dt` result `y·t` — confirming the
radical-base `cderiv` contributed the `ℓ·y·t` term (had `cmonomialDeriv` only done `d/dt`, the result
would be `y·t = radX3GenT`). -/
theorem radX3_monomialDeriv_genT_runs_coeff :
    (CPolyG.cisZeroG (CPolyG.cmonomialDeriv radX3DtExp radX3GenT) = false) ∧
    (CPolyG.cisZeroG (CPolyG.csubG
      (CPolyG.cmonomialDeriv radX3DtExp radX3GenT) radX3GenT) = false) := by
  constructor <;> native_decide

/-! ### The keystone composes: a transcendental level `QFunNZG (RadExt …)` over the algebraic base

The payoff of the `CField`/`CDiffField (RadExt …)` instances: the transcendental-monomial carrier
`QFunNZG α` is generic over any `[CField α]` (`instCFieldQFunNZG` needs `[CField α] [CFieldDomain α]`;
`instCDiffFieldQFunNZG` adds `[CDiffField α]`). With `α := RadX3` the radical base, those binders are
exactly the instances built above plus a `CFieldDomain RadX3` — so `QFunNZG RadX3 ≅ ℚ(x)[√(x³+1)](t)`
(the fraction field of `RadX3[t]`) is automatically a `CField` and a `CDiffField`. We exhibit this by
instance resolution, under the one outstanding hypothesis `[CFieldDomain RadX3]` (the Prop-erased domain
facts for the radical base — a genuine field/domain since `X² − (x³+1)` is irreducible over ℚ(x); its
closed proof needs the `AdjoinRoot` bridge with canonical/reduced representatives, below). -/

section
variable [CFieldDomain RadX3]

/-- `QFunNZG RadX3` is a `CField` (given `[CFieldDomain RadX3]`) — the transcendental level
`ℚ(x)[√(x³+1)](t)` over the algebraic base resolves automatically from `instCFieldQFunNZG` (generic over
`[CField RadX3] [CFieldDomain RadX3]`), since `CField RadX3` is the radical-base instance built above. -/
theorem cfield_qfunNZG_radX3 : Nonempty (CField (QFunNZG RadX3)) := ⟨inferInstance⟩

/-- `QFunNZG RadX3` is a `CDiffField` (given `[CFieldDomain RadX3]`) — the transcendental level
inherits the *full* tower derivation (`d/dx + radical y' + ∂/∂t`) from `instCDiffFieldQFunNZG` (generic over
`[CField RadX3] [CDiffField RadX3] [CFieldDomain RadX3]`), since `CDiffField RadX3` is the diagonal-radical
derivation built above. The mixed elementary tower is a *differential* field — transcendental-over-algebraic
with a genuine derivation. -/
theorem cdiffField_qfunNZG_radX3 : Nonempty (CDiffField (QFunNZG RadX3)) := ⟨inferInstance⟩

end

/-! ### Toward discharging `[CFieldDomain RadX3]`: irreducibility of `y² − (x³+1)` over ℚ(x)

The `[CFieldDomain RadX3]` hypothesis says the radical base is an integral domain — which it is, because
`ℚ(x)[√(x³+1)] = ℚ(x)[y]/(y² − (x³+1))` is a **field**: the defining polynomial `y² − (x³+1)` is
**irreducible** over ℚ(x) (`x³+1` is not a square in ℚ(x) — it has odd `intDegree 3`, whereas every square
`b²` has even `intDegree 2·intDegree(b)`). That irreducibility is proven here (`irreducible_radX3`), and
registered as the `Fact` instance the `AdjoinRoot`-bridge route to `CFieldSpec (RadExt …)` (hence
`CFieldDomain`) consumes. The *concrete* `CFieldDomain RadX3` instance is the residual — see the note after.

`RadX3`'s base field is `CFieldSpec.K (QFunNZG ℚ) = RatFunc ℚ`; its radicand reads as
`CFieldSpec.toK radicandX3p1 = algebraMap ℚ[X] (RatFunc ℚ) (1 + x³)` (`toK_radicandX3p1`). -/

open CPolyG in
/-- `toK radicandX3p1 = algebraMap (1 + x³)` in `RatFunc ℚ`: the ℚ(x)-radicand of `RadX3` reads, through
the tower bridge `toQFunNZG`, as the rational function `algebraMap ℚ[X] (RatFunc ℚ) (1 + x³)` (numerator
`[1,0,0,1] ↦ 1 + x³`, denominator `[1] ↦ 1`). The identification feeding the irreducibility/degree
arguments. -/
theorem toK_radicandX3p1 :
    CFieldSpec.toK (radicandX3p1 : QFunNZG ℚ) = algebraMap (ℚ[X]) (RatFunc ℚ) (1 + X ^ 3) := by
  show QFunNZG.toQFunNZG radicandX3p1 = _
  rw [QFunNZG.toQFunNZG]
  show QFunNZG.amG ℚ (toPolyG ([1, 0, 0, 1] : CPolyG ℚ))
      / QFunNZG.amG ℚ (toPolyG ([CField.one] : CPolyG ℚ)) = _
  have h1 : toPolyG ([1, 0, 0, 1] : CPolyG ℚ) = 1 + X ^ 3 := by
    simp only [toPolyG_cons, toPolyG_nil]
    show C (1 : ℚ) + X * (C 0 + X * (C 0 + X * (C 1 + X * 0))) = _
    simp; ring
  have h2 : toPolyG ([CField.one] : CPolyG ℚ) = 1 := by
    show C (CFieldSpec.toK (CField.one : ℚ)) + X * 0 = 1; simp [CFieldSpec.toK_one]
  rw [h1, h2]
  show QFunNZG.amG ℚ (1 + X ^ 3) / QFunNZG.amG ℚ 1 = _
  rw [map_one, div_one]; rfl

/-- `1 + x³ ≠ 0` in `ℚ[X]` (it has `natDegree 3`). -/
theorem X3p1_ne_zero : (1 + X ^ 3 : ℚ[X]) ≠ 0 := by
  intro h
  have := congrArg Polynomial.natDegree h
  rw [add_comm, Polynomial.natDegree_add_eq_left_of_natDegree_lt (by simp), natDegree_X_pow] at this
  simp at this

/-- `natDegree (1 + x³) = 3` in `ℚ[X]` (the leading `x³` dominates the constant `1`). -/
theorem natDeg_X3p1 : (1 + X ^ 3 : ℚ[X]).natDegree = 3 := by
  rw [add_comm, Polynomial.natDegree_add_eq_left_of_natDegree_lt (by simp), natDegree_X_pow]

/-- `x³+1` is not a square in `ℚ(x)`: `∀ b : RatFunc ℚ, b² ≠ algebraMap (1 + x³)`. A square `b²` has
even `intDegree = 2·intDegree(b)`, but `algebraMap (1 + x³)` has `intDegree = natDegree(1 + x³) = 3` (odd).
The odd-degree obstruction to `x³+1` being a perfect square — the algebraic content that makes the radical
extension a field. -/
theorem not_square_X3p1 :
    ∀ b : RatFunc ℚ, b ^ 2 ≠ algebraMap (ℚ[X]) (RatFunc ℚ) (1 + X ^ 3) := by
  intro b hb
  have hrhs_ne : algebraMap (ℚ[X]) (RatFunc ℚ) (1 + X ^ 3) ≠ 0 := RatFunc.algebraMap_ne_zero X3p1_ne_zero
  have hb_ne : b ≠ 0 := by rintro rfl; rw [zero_pow (by norm_num)] at hb; exact hrhs_ne hb.symm
  have hdeg : (b ^ 2).intDegree = (algebraMap (ℚ[X]) (RatFunc ℚ) (1 + X ^ 3)).intDegree := by rw [hb]
  rw [sq, RatFunc.intDegree_mul hb_ne hb_ne, RatFunc.intDegree_polynomial, natDeg_X3p1] at hdeg
  omega

/-- `y² − (x³+1)` is irreducible over `ℚ(x)` — `Irreducible (X² − C(toK radicandX3p1))` in
`(RatFunc ℚ)[X]`. By `X_pow_sub_C_irreducible_of_prime` (prime `2`) and `x³+1` not-a-square
(`not_square_X3p1`). So `AdjoinRoot (X² − C(toK radicandX3p1)) = ℚ(x)[√(x³+1)]` is a genuine **field** — the
algebraic fact underwriting `CFieldDomain RadX3`. -/
theorem irreducible_radX3 :
    Irreducible (X ^ 2 - C (CFieldSpec.toK (radicandX3p1 : QFunNZG ℚ))) := by
  rw [toK_radicandX3p1]
  exact X_pow_sub_C_irreducible_of_prime Nat.prime_two not_square_X3p1

/-- The irreducibility as a `Fact` — registers `Irreducible (X² − C(toK radicandX3p1))` so Mathlib's
`AdjoinRoot.instField` resolves `Field (AdjoinRoot (X² − C(toK radicandX3p1)))`, the field
`ℚ(x)[√(x³+1)]`. The instance the `CFieldSpec (RadExt …)` bridge to that `AdjoinRoot` would consume. -/
instance fact_irreducible_radX3 :
    Fact (Irreducible (X ^ 2 - C (CFieldSpec.toK (radicandX3p1 : QFunNZG ℚ)))) :=
  ⟨irreducible_radX3⟩

/-- `ℚ(x)[√(x³+1)]` is a field — `Field (AdjoinRoot (X² − C(toK radicandX3p1)))`, resolved from the
irreducibility `Fact`. The genuine field the radical base `RadX3` represents; the integral-domain witness
that `CFieldDomain RadX3` asserts (the discharge is the residual below). -/
noncomputable example : Field (AdjoinRoot (X ^ 2 - C (CFieldSpec.toK (radicandX3p1 : QFunNZG ℚ)))) :=
  inferInstance

/-! ### The `CFieldSpec (RadExt α n f)` bridge into `AdjoinRoot (Xⁿ − C(toK f))`

The noncomputable correctness bridge that turns `irreducible_radX3` into a concrete `CFieldDomain`. The
target field is `K := AdjoinRoot (Xⁿ − C(toK f))` (Mathlib's `R[X]/(g)`, a `Field` under
`[Fact (Irreducible g)]`), and `toK p := AdjoinRoot.mk _ (toPolyG (RadExt.radCanon n f p.toRad))` — the **canonical**
representative, so every law lands on a degree-`< n` rep where `AdjoinRoot.mk ∘ toPolyG` is faithful. The
ring-hom laws are the proven `mk_toPolyG_radMul` / `toPolyG_caddG` of `ComputableRadicalDerivationInvariant`
(`AdjoinRoot.mk` *is* `Ideal.Quotient.mk (radIdeal n f)`), the new `RadExt.radCanon` absorbed by
`mk_toPolyG_radReduce`. The two crux lemmas: `isZero_iff` (the `radReduce` length bound +
`AdjoinRoot.mk_ne_zero_of_natDegree_lt`) and `toK_inv` (the conjugate-norm identity `q·(ā − b̄y) = N`, a
unit when `N ≠ 0 ↔ q ≠ 0`). Restricted to `n = 2` (the conjugate inverse `radInv2`). -/

namespace RadElem
variable {α : Type*} [CField α] {n : ℕ} {f : α}

/-- `cnormG` does not grow length — `(cnormG p).length ≤ p.length` (stripping trailing zeros). -/
theorem cnormG_length_le (p : CPolyG α) : (CPolyG.cnormG p : List α).length ≤ (p : List α).length := by
  induction p with
  | nil => simp [CPolyG.cnormG]
  | cons a as ih =>
    rw [CPolyG.cnormG]
    cases h : CPolyG.cnormG as with
    | nil => by_cases ha : CField.isZero a <;> simp [ha, List.length_cons]
    | cons b bs =>
      simp only [List.length_cons]
      have : (b :: bs : List α).length ≤ (as : List α).length := h ▸ ih
      simp only [List.length_cons] at this; omega

/-- `caddG` length is the `max` — `(caddG p q).length = max p.length q.length` (the shorter is
zero-extended). -/
theorem caddG_length (p q : CPolyG α) :
    (CPolyG.caddG p q : List α).length = max (p : List α).length (q : List α).length := by
  induction p generalizing q with
  | nil => simp [CPolyG.caddG]
  | cons a as ih =>
    cases q with
    | nil => simp [CPolyG.caddG]
    | cons b bs => simp only [CPolyG.caddG, List.length_cons, ih bs]; omega

/-- `cshiftG` length — `(cshiftG k p).length = k + p.length` (prepend `k` zeros). -/
theorem cshiftG_length (k : ℕ) (p : CPolyG α) :
    (CPolyG.cshiftG k p : List α).length = k + (p : List α).length := by
  induction k with
  | zero => simp [CPolyG.cshiftG]
  | succ m ih => rw [CPolyG.cshiftG]; simp only [List.length_cons, ih]; omega

/-- The inner `radReduce` reaches `cnormG`-length `≤ n` (`n ≥ 1`, `fuel ≥ cnormG-length`) — each fold
strictly drops the normalized length (it replaces a length-`L` list, `L > n`, by one of length `< L`:
`dropLast` is `L−1` and the `cshiftG (L−1−n)` term is `L−n ≤ L−1`), so the loop hits the `length ≤ n` exit.
The kernel of both `radCanon` length bounds. -/
theorem cnormG_radReduce_length_le (hn : 1 ≤ n) : ∀ (fuel : ℕ) (u : CPolyG α),
    (CPolyG.cnormG u : List α).length ≤ fuel →
    (CPolyG.cnormG (radReduce n f fuel u) : List α).length ≤ n := by
  intro fuel
  induction fuel with
  | zero => intro u hub; rw [radReduce]; simp only [Nat.le_zero] at hub; omega
  | succ fuel ih =>
    intro u hub
    rw [radReduce]
    by_cases hlen : (CPolyG.cnormG u : List α).length ≤ n
    · simp only [hlen, if_true, CPolyG.cnormG_idem]
    · simp only [hlen, if_false]; replace hlen := Nat.lt_of_not_le hlen
      apply ih
      set q := CPolyG.cnormG u with hq
      have hstep : (CPolyG.caddG (q : List α).dropLast
          (CPolyG.cshiftG ((q : List α).length - 1 - n)
            [CField.mul ((q : List α).getLast?.getD CField.zero) f]) : List α).length
          < (q : List α).length := by
        rw [caddG_length, cshiftG_length]
        simp only [List.length_singleton, List.length_dropLast]; omega
      have := (cnormG_length_le _).trans_lt hstep; omega

/-- `RadExt.radCanon` has length `≤ n` (`n ≥ 1`) — `radCanon = cnormG ∘ radReduce` with the inner
`radReduce` reaching `cnormG`-length `≤ n` (`cnormG_radReduce_length_le`). The length bound that makes
`isZero_iff` and `toK_inv` faithful: `toPolyG (RadExt.radCanon u)` has `natDegree < n = deg (Xⁿ − C(toK
f))`, and the inverse reads a degree-`< 2` rep. -/
theorem radCanon_length_le (hn : 1 ≤ n) (u : CPolyG α) :
    (RadExt.radCanon n f u : List α).length ≤ n := by
  rw [RadExt.radCanon]
  have := cnormG_radReduce_length_le (f := f) hn ((u : List α).length + 1) u (by
    have := cnormG_length_le u; omega)
  exact this

/-- `cnormG (RadExt.radCanon u)` has length `≤ n` — immediate from `radCanon_length_le` and
`cnormG_length_le` (the outer `cnormG` of `radCanon` is idempotent). -/
theorem cnormG_radCanon_length_le (hn : 1 ≤ n) (u : CPolyG α) :
    (CPolyG.cnormG (RadExt.radCanon n f u) : List α).length ≤ n :=
  (cnormG_length_le _).trans (radCanon_length_le hn u)

variable [CFieldSpec α]

/-- The bridge `toAdj p = mk (toPolyG p.toRad)` into `AdjoinRoot (Xⁿ − C(toK f))` (`mk` *is*
`Ideal.Quotient.mk (radIdeal n f)`). The `toK` of the `CFieldSpec (RadExt …)` instance, on canonical reps. -/
noncomputable def toAdj (p : RadExt α n f) : AdjoinRoot (X ^ n - C (CFieldSpec.toK f)) :=
  AdjoinRoot.mk _ (CPolyG.toPolyG p.toRad)

/-- `RadExt.radCanon` is absorbed by `mk` — `mk (toPolyG (RadExt.radCanon n f u)) = mk (toPolyG u)` (the reduction
changes the polynomial only by a multiple of `Xⁿ − C(toK f)`, `mk_toPolyG_radReduce`). -/
theorem mk_canon (u : RadElem α) :
    AdjoinRoot.mk (X ^ n - C (CFieldSpec.toK f)) (CPolyG.toPolyG (RadExt.radCanon n f u))
      = AdjoinRoot.mk _ (CPolyG.toPolyG u) := by
  show Ideal.Quotient.mk (radIdeal n f) _ = Ideal.Quotient.mk _ _
  rw [RadExt.radCanon, CPolyG.toPolyG_cnormG, mk_toPolyG_radReduce]

/-- `toAdj` sends `RadExt.zero` to `0`. -/
theorem toAdj_zero : toAdj (RadExt.zero : RadExt α n f) = 0 := by
  show AdjoinRoot.mk _ (CPolyG.toPolyG ([] : RadElem α)) = 0
  rw [CPolyG.toPolyG_nil, map_zero]

/-- `toAdj` sends `RadExt.one` to `1`. -/
theorem toAdj_one : toAdj (RadExt.one : RadExt α n f) = 1 := by
  show AdjoinRoot.mk (X ^ n - C (CFieldSpec.toK f)) (CPolyG.toPolyG ([CField.one] : RadElem α)) = 1
  rw [show CPolyG.toPolyG ([CField.one] : RadElem α) = (1 : (CFieldSpec.K α)[X]) by
    rw [CPolyG.toPolyG_cons, CPolyG.toPolyG_nil, mul_zero, add_zero, CFieldSpec.toK_one, map_one]]
  exact map_one _

/-- `toAdj` intertwines `RadExt.add` with `+` — via `toPolyG_caddG` and `RadExt.radCanon` absorption. -/
theorem toAdj_add (p q : RadExt α n f) : toAdj (RadExt.add p q) = toAdj p + toAdj q := by
  show AdjoinRoot.mk _ (CPolyG.toPolyG (RadExt.radCanon n f (radAdd p.toRad q.toRad))) = _
  rw [mk_canon]
  show AdjoinRoot.mk _ (CPolyG.toPolyG (CPolyG.caddG _ _)) = _
  rw [CPolyG.toPolyG_caddG, map_add]; rfl

/-- `toAdj` intertwines `RadExt.neg` with `-` — via `toPolyG_cnegG`. -/
theorem toAdj_neg (p : RadExt α n f) : toAdj (RadExt.neg p) = - toAdj p := by
  show AdjoinRoot.mk _ (CPolyG.toPolyG (RadExt.radCanon n f (radNeg p.toRad))) = _
  rw [mk_canon]
  show AdjoinRoot.mk _ (CPolyG.toPolyG (CPolyG.cnegG _)) = _
  rw [CPolyG.toPolyG_cnegG, map_neg]; rfl

/-- **`toAdj` intertwines `RadExt.mul` with `*`** — the radical product is the quotient product
(`mk_toPolyG_radMul`, the carrier ring structure `K[X] ⧸ (Xⁿ − C(toK f))`). -/
theorem toAdj_mul (p q : RadExt α n f) : toAdj (RadExt.mul p q) = toAdj p * toAdj q := by
  show AdjoinRoot.mk _ (CPolyG.toPolyG (RadExt.radCanon n f (radMul n f p.toRad q.toRad))) = _
  rw [mk_canon]; show Ideal.Quotient.mk (radIdeal n f) _ = _ * _
  rw [mk_toPolyG_radMul]; rfl

/-- `toAdj` reflects the zero test — `RadExt.isZero p = true ↔ toAdj p = 0` (`n ≥ 1`). `→`: the
canonical rep is `cisZeroG`, so `toPolyG (RadExt.radCanon p) = 0`. `←`: `toAdj p = 0` means `(Xⁿ − C(toK f)) ∣
toPolyG (RadExt.radCanon p)`, but `natDegree (toPolyG (RadExt.radCanon p)) < n` (`cnormG_radCanon_length_le`), so
`AdjoinRoot.mk_ne_zero_of_natDegree_lt` forces `toPolyG (RadExt.radCanon p) = 0`, i.e. `cisZeroG = true`. The
faithfulness that makes `toAdj` certify the computable zero test. -/
theorem isZero_iff (hn : 1 ≤ n) (p : RadExt α n f) : RadExt.isZero p = true ↔ toAdj p = 0 := by
  rw [RadExt.isZero, toAdj]
  constructor
  · intro h
    have h0 : CPolyG.toPolyG (RadExt.radCanon n f p.toRad) = 0 := (CPolyG.cisZeroG_iff _).mp h
    rw [← mk_canon (f := f) p.toRad, h0, map_zero]
  · intro h
    by_contra hne
    have hcz : CPolyG.cisZeroG (RadExt.radCanon n f p.toRad) = false := by
      rw [Bool.eq_false_iff]; exact hne
    have hp0 : CPolyG.toPolyG (RadExt.radCanon n f p.toRad) ≠ 0 := by
      rw [Ne, ← CPolyG.cisZeroG_iff, hcz]; exact Bool.false_ne_true
    have hdeg : (CPolyG.toPolyG (RadExt.radCanon n f p.toRad)).natDegree < n := by
      have h1 := CPolyG.natDegree_toPolyG_le (RadExt.radCanon n f p.toRad)
      have h2 := cnormG_radCanon_length_le (f := f) hn p.toRad
      omega
    have hmono : (X ^ n - C (CFieldSpec.toK f)).Monic := monic_X_pow_sub_C _ (by omega)
    have := AdjoinRoot.mk_ne_zero_of_natDegree_lt hmono hp0 (by rw [natDegree_X_pow_sub_C]; exact hdeg)
    rw [← mk_canon (f := f) p.toRad] at h; exact this h

/-! #### The inverse law (`n = 2`): `toAdj (RadExt.inv p) = (toAdj p)⁻¹`

`radInv2 f q = [a/N, −b/N]` for `q = a + b·y`, `N = a² − b²f` the conjugate norm. In `AdjoinRoot (X² −
C(toK f))`, `(a + b·root)·(a − b·root) = a² − b²·root² = a² − b²f = N`, so `radInv2 f q` is `q⁻¹` when
`N ≠ 0` (and both vanish when `N = 0`, i.e. `q = 0`). -/

/-- `toPolyG (radInv2 f q)` in `K[X]` — `C(toK(a/N)) − C(toK(b/N))·X` (`a, b` the `radCoeff0/1`,
`N = radNorm2`). `radInv2` reads only `y⁰`/`y¹`, so this holds for any `q`. -/
theorem toPolyG_radInv2 (q : RadElem α) :
    CPolyG.toPolyG (radInv2 f q)
      = C (CFieldSpec.toK (CField.div (radCoeff0 q) (radNorm2 f q)))
        - C (CFieldSpec.toK (CField.div (radCoeff1 q) (radNorm2 f q))) * X := by
  show CPolyG.toPolyG [CField.div (radCoeff0 q) (radNorm2 f q),
      CField.neg (CField.div (radCoeff1 q) (radNorm2 f q))] = _
  simp only [CPolyG.toPolyG_cons, CPolyG.toPolyG_nil, mul_zero, add_zero]
  rw [CFieldSpec.toK_neg, map_neg]; ring

/-- `toPolyG q = C(toK a) + C(toK b)·X` for a length-`≤ 2` `q` (`a, b` the `radCoeff0/1`). The Horner
form of a canonical `n = 2` rep. -/
theorem toPolyG_of_len_le_two (q : RadElem α) (hq : (q : List α).length ≤ 2) :
    CPolyG.toPolyG q = C (CFieldSpec.toK (radCoeff0 q)) + C (CFieldSpec.toK (radCoeff1 q)) * X := by
  match q, hq with
  | [], _ => simp [radCoeff0, radCoeff1, CFieldSpec.toK_zero]
  | [a], _ =>
    show CPolyG.toPolyG [a] = _
    rw [show radCoeff0 ([a] : RadElem α) = a from rfl,
      show radCoeff1 ([a] : RadElem α) = CField.zero from rfl]
    simp only [CPolyG.toPolyG_cons, CPolyG.toPolyG_nil, mul_zero, add_zero]
    rw [CFieldSpec.toK_zero, map_zero, zero_mul, add_zero]
  | [a, b], _ =>
    show CPolyG.toPolyG [a, b] = _
    rw [show radCoeff0 ([a, b] : RadElem α) = a from rfl, show radCoeff1 ([a, b] : RadElem α) = b from rfl]
    simp only [CPolyG.toPolyG_cons, CPolyG.toPolyG_nil, mul_zero, add_zero]; ring

/-- The conjugate-norm inverse identity (`n = 2`, length-`≤ 2` `q`, `N ≠ 0`): `mk (toPolyG q) · mk
(toPolyG (radInv2 f q)) = 1` in `AdjoinRoot (X² − C(toK f))`. The product `(C A + C B·X)(C(A/N) − C(B/N)·X)
− 1 = −(C B·C(B/N))·(X² − C F)` lies in the defining ideal (using `A·(A/N) − B·F·(B/N) = N/N = 1`). So
`radInv2 f q` *is* the field inverse of `q`. -/
theorem inv_mul_gen (q : RadElem α) (hq : (q : List α).length ≤ 2)
    (hN : CFieldSpec.toK (radNorm2 f q) ≠ 0) :
    AdjoinRoot.mk (X ^ 2 - C (CFieldSpec.toK f)) (CPolyG.toPolyG q)
      * AdjoinRoot.mk _ (CPolyG.toPolyG (radInv2 f q)) = 1 := by
  set A := CFieldSpec.toK (radCoeff0 q)
  set B := CFieldSpec.toK (radCoeff1 q)
  set F := CFieldSpec.toK f
  set N := CFieldSpec.toK (radNorm2 f q) with hNdef
  have hNval : N = A * A - B * B * F := by
    rw [hNdef, radNorm2, CFieldSpec.toK_sub, CFieldSpec.toK_mul, CFieldSpec.toK_mul, CFieldSpec.toK_mul]
  have hq2 : CPolyG.toPolyG q = C A + C B * X := toPolyG_of_len_le_two q hq
  have hinv : CPolyG.toPolyG (radInv2 f q) = C (A / N) - C (B / N) * X := by
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

/-- `N = 0` when a reduced `q` vanishes — `toPolyG q = 0 → toK (radNorm2 f q) = 0` (the coefficients
`a, b` both vanish, so `N = a² − b²f = 0`). -/
theorem toK_radNorm2_eq_zero_of_toPolyG_zero (q : RadElem α) (hq : (q : List α).length ≤ 2)
    (h0 : CPolyG.toPolyG q = 0) : CFieldSpec.toK (radNorm2 f q) = 0 := by
  rw [toPolyG_of_len_le_two q hq] at h0
  have hA : CFieldSpec.toK (radCoeff0 q) = 0 := by
    have := congrArg (Polynomial.coeff · 0) h0; simpa [coeff_C, coeff_X] using this
  have hB : CFieldSpec.toK (radCoeff1 q) = 0 := by
    have := congrArg (Polynomial.coeff · 1) h0; simpa [coeff_C, coeff_X, coeff_C_mul] using this
  rw [radNorm2, CFieldSpec.toK_sub, CFieldSpec.toK_mul, CFieldSpec.toK_mul, CFieldSpec.toK_mul, hA, hB]
  ring

/-- A canonical rep with `mk (toPolyG q) = 0` is `0` — `(q.length ≤ 2) → mk (toPolyG q) = 0 →
toPolyG q = 0` (degree `< 2 = deg (X² − C(toK f))`, so the only multiple of the defining polynomial of
that degree is `0`, `AdjoinRoot.mk_ne_zero_of_natDegree_lt`). Needs the irreducibility `Fact` (for the
`AdjoinRoot` field structure used downstream). -/
theorem toPolyG_eq_zero_of_mk_zero [Fact (Irreducible (X ^ 2 - C (CFieldSpec.toK f)))]
    (q : RadElem α) (hq : (q : List α).length ≤ 2)
    (h : AdjoinRoot.mk (X ^ 2 - C (CFieldSpec.toK f)) (CPolyG.toPolyG q) = 0) :
    CPolyG.toPolyG q = 0 := by
  by_contra h0
  have hdeg : (CPolyG.toPolyG q).natDegree < 2 := by
    have := CPolyG.natDegree_toPolyG_le q
    have hcn := cnormG_length_le q
    omega
  have hmono : (X ^ 2 - C (CFieldSpec.toK f)).Monic := monic_X_pow_sub_C _ (by norm_num)
  exact AdjoinRoot.mk_ne_zero_of_natDegree_lt hmono h0 (by rw [natDegree_X_pow_sub_C]; exact hdeg) h

/-- A vanishing conjugate norm forces a canonical rep to `0` (`n = 2`): for a length-`≤ 2` `q`,
`toK (radNorm2 f q) = 0 → toPolyG q = 0`. From `N = a² − b²·F = 0`: if `b ≠ 0` then `F = (a/b)²` is a
square in `K`, contradicting the not-a-square consequence of the irreducibility `Fact`; so `b = 0`, then
`a² = 0` forces `a = 0`, hence `toPolyG q = C a + C b·X = 0`. The non-degeneracy of the conjugate norm. -/
theorem toPolyG_eq_zero_of_N_zero [Fact (Irreducible (X ^ 2 - C (CFieldSpec.toK f)))]
    (q : RadElem α) (hq : (q : List α).length ≤ 2)
    (hN : CFieldSpec.toK (radNorm2 f q) = 0) : CPolyG.toPolyG q = 0 := by
  set A := CFieldSpec.toK (radCoeff0 q)
  set B := CFieldSpec.toK (radCoeff1 q)
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
  rw [toPolyG_of_len_le_two q hq, show CFieldSpec.toK (radCoeff0 q) = A from rfl,
    show CFieldSpec.toK (radCoeff1 q) = B from rfl, hA, hB]
  simp

/-- `toAdj` intertwines `RadExt.inv` with `⁻¹` (`n = 2`): `toAdj (RadExt.inv p) = (toAdj p)⁻¹`.
`RadExt.inv` canonicalizes its input to a length-`≤ 2` rep `q`, so `radInv2 f q` is the genuine inverse.
Split on the conjugate norm `N = radNorm2 f q`: when `N ≠ 0`, `inv_mul_gen` gives `mk q · mk (radInv2 f q)
= 1`, so `mk (radInv2 f q) = (mk q)⁻¹ = (toAdj p)⁻¹` (`eq_inv_of_mul_eq_one_right`); when `N = 0`, then
`q = 0` (`toPolyG_eq_zero_of_N_zero`, by not-a-square), so both `radInv2 f q = 0` and `toAdj p = 0`, and
`0 = 0⁻¹`. The field-inverse law of the bridge (needs the irreducibility `Fact`). -/
theorem toAdj_inv [Fact (Irreducible (X ^ 2 - C (CFieldSpec.toK f)))] (p : RadExt α 2 f) :
    toAdj (RadExt.inv p) = (toAdj p)⁻¹ := by
  set q := RadExt.radCanon 2 f p.toRad with hq
  have hqlen : (q : List α).length ≤ 2 := by rw [hq]; exact radCanon_length_le (by norm_num) p.toRad
  have hpadj : toAdj p = AdjoinRoot.mk _ (CPolyG.toPolyG q) := by rw [toAdj, hq, mk_canon]
  show AdjoinRoot.mk _ (CPolyG.toPolyG (RadExt.radCanon 2 f (radInv2 f (RadExt.radCanon 2 f p.toRad)))) = _
  rw [mk_canon, ← hq]
  by_cases hN : CFieldSpec.toK (radNorm2 f q) = 0
  · -- `N = 0 ⟹ q = 0 ⟹ radInv2 f q = 0` and `toAdj p = 0`; `0 = 0⁻¹`.
    have hq0 : CPolyG.toPolyG q = 0 := toPolyG_eq_zero_of_N_zero q hqlen hN
    have hinv0 : CPolyG.toPolyG (radInv2 f q) = 0 := by
      rw [toPolyG_radInv2, CFieldSpec.toK_div, CFieldSpec.toK_div, hN, div_zero, div_zero, map_zero]
      simp
    rw [hinv0, map_zero, hpadj, hq0, map_zero, inv_zero]
  · rw [hpadj]
    exact eq_inv_of_mul_eq_one_right (inv_mul_gen q hqlen hN)

end RadElem

/-! ### `CFieldSpec (RadExt α 2 f)` and the concrete `CFieldDomain`

Assembling the bridge laws gives the noncomputable `CFieldSpec (RadExt α 2 f)` — over `[CFieldSpec α]` and
the irreducibility `Fact` (so `K = AdjoinRoot (X² − C(toK f))` is a `Field`). Then the **global**
`instCFieldDomainOfCFieldSpec` supplies `CFieldDomain (RadExt α 2 f)` (a `Prop`-erased instance), which is
exactly what discharges the `[CFieldDomain RadX3]` hypothesis and makes `QFunNZG (RadExt …)` an
**unconditional** `CField` + `CDiffField`. -/

/-- `CFieldSpec (RadExt α 2 f)` — the field-homomorphism bridge into `K = AdjoinRoot (X² − C(toK f))`
(a `Field` under `[Fact (Irreducible (X² − C(toK f)))]`), with `toK := RadElem.toAdj`. All laws are the
`RadElem.toAdj_*` bridge theorems (ring-hom from `mk_toPolyG_radMul` / `toPolyG_caddG`, `isZero_iff` from
the `radCanon` length bound, `toK_inv` from the conjugate-norm identity). Noncomputable (routes through
`AdjoinRoot`); only the correctness layer depends on it. This certifies the computable `CField (RadExt α 2
f)` against the genuine field `α[y]/(y² − f)`. -/
noncomputable instance instCFieldSpecRadExt {α : Type*} [CField α] [CFieldDomain α] [CFieldSpec α]
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

/-! ### Unconditional composition: `QFunNZG (RadExt ℚ(x) 2 (x³+1))` is a `CField` + `CDiffField`

With `CFieldSpec (RadExt …)` in scope, `instCFieldDomainOfCFieldSpec` resolves `CFieldDomain RadX3`
**concretely** (no hypothesis) — `fact_irreducible_radX3` supplies the irreducibility. So the transcendental
level `QFunNZG RadX3 ≅ ℚ(x)[√(x³+1)](t)` is now an **unconditional** `CField` and `CDiffField`, and the
mixed-tower derivations re-validate with the resolved instances. The first fully-discharged
**transcendental-on-algebraic** carrier. -/

/-- `CFieldDomain RadX3` — discharged concretely (no hypothesis): from `instCFieldSpecRadExt` (with
`fact_irreducible_radX3`) via the global `instCFieldDomainOfCFieldSpec`. The integral-domain witness that
the radical base is a genuine field, the key that lets the transcendental level stack. -/
noncomputable example : CFieldDomain RadX3 := inferInstance

/-- `QFunNZG RadX3` is a `CField`, unconditionally — `ℚ(x)[√(x³+1)](t)` resolves its `CField`
outright (the `[CFieldDomain RadX3]` hypothesis of `cfield_qfunNZG_radX3` is now discharged). The
transcendental monomial `t` stacks on the algebraic base with no outstanding assumption. -/
theorem cfield_qfunNZG_radX3_unconditional : Nonempty (CField (QFunNZG RadX3)) := ⟨inferInstance⟩

/-- `QFunNZG RadX3` is a `CDiffField`, unconditionally — the mixed elementary tower
`ℚ(x)[√(x³+1)](t)` is a genuine differential field with no hypothesis, inheriting `d/dx + radical y' +
∂/∂t`. -/
theorem cdiffField_qfunNZG_radX3_unconditional : Nonempty (CDiffField (QFunNZG RadX3)) := ⟨inferInstance⟩

/-- The transcendental monomial `t ∈ QFunNZG RadX3 = ℚ(x)[√(x³+1)](t)` (numerator `[0, 1] = t` over the
radical base `RadX3`, denominator `[1]`). The new independent variable stacked on the algebraic extension;
its proof of denominator-nonzero is `native_decide` (the `CFieldDomain RadX3` Prop is erased). -/
def tOverRadX3 : QFunNZG RadX3 := ⟨([CField.zero, CField.one], [CField.one]), by native_decide⟩

/-- `D(t) = 1` over `ℚ(x)[√(x³+1)](t)`, fully `native_decide` — the **typeclass** derivation
`CDiffField.cderiv` on `QFunNZG RadX3` (the tower derivation `towerDerivQFunNZG [1]`, `Dt = 1`) sends the
new transcendental monomial `t` to `1`, computed in the native compiler over the **algebraic** base. The
first derivative computed at the transcendental level over an algebraic base with the **concrete**
(hypothesis-free) instances — the `CFieldDomain RadX3` Prop-erasure keeps it `native_decide`-able. -/
theorem cderiv_tOverRadX3_eq_one :
    CField.isZero (CField.sub (CDiffField.cderiv tOverRadX3) (CField.one : QFunNZG RadX3)) = true := by
  native_decide

/-- `t · t⁻¹ = 1` over `ℚ(x)[√(x³+1)](t)`, fully `native_decide` — the **typeclass** field
operations of `QFunNZG RadX3` (computable, over the now-concrete `CFieldDomain RadX3`) invert the
transcendental monomial `t` over the algebraic base. The mixed elementary tower is a genuine **field** that
computes, unconditionally. -/
theorem mul_inv_tOverRadX3_eq_one :
    CField.isZero (CField.sub (CField.mul tOverRadX3 (CField.inv tOverRadX3))
      (CField.one : QFunNZG RadX3)) = true := by native_decide

end DeepWiki.SymbolicIntegration
