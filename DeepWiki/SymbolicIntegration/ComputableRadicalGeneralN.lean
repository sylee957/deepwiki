import DeepWiki.SymbolicIntegration.ComputableTranscendentalOverAlgebraic
import DeepWiki.SymbolicIntegration.ComputableGenericBezout
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.RatFunc.Degree

/-! # General-`n` radical extensions: the `∛`/`nth`-root inverse and a cube-root `CField`

The simple-radical carrier `RadExt α n f = α[y]/(yⁿ − f)`
(`ComputableTranscendentalOverAlgebraic`) is `n`-generic for its ring/derivation
(`radAdd`/`radMul`/`radDeriv` all take `n`/`f` explicitly), but its **inverse** was the `n = 2`
conjugate-norm `radInv2` only (`u⁻¹ = ū/(a² − b²f)`), so `instCFieldRadExt` is an honest *field*
solely at `n = 2`. This file lifts the inverse to **arbitrary `n`** via the **extended Euclidean
algorithm** in `α[y]`, and exhibits the engine differentiating/integrating over a **cube root**.

* **`radInvN n f g`** — the general-`n` inverse of `g ∈ α[y]/(yⁿ − f)`. When `yⁿ − f` is irreducible,
  `g` is a unit, so `cbezoutOne` finds `s·g + t·(yⁿ − f) = 1` in `α[y]`; reducing `s` mod `yⁿ = f`
  gives `g⁻¹` (because `(yⁿ − f) ≡ 0`, so `s·g ≡ 1`). Reuses the engine's `cbezoutOne` (built on
  `cgcdExtG`). Generic over every `[CField α]` and every `n`. At `n = 2` it agrees with `radInv2`
  (the conjugate-norm reciprocal, `radInvN_eq_radInv2_at_two` over ℚ(x)).
* **`RadExtN α n f`** — a *fresh* carrier (mirroring `RadExt`) whose `CField` inverse is `radInvN`
  rather than `radInv2`, so it is an honest field for **every** `n` where `yⁿ − f` is irreducible
  (not just `n = 2`). `add`/`mul`/`neg`/`isZero` are the same radical-carrier ops, `cderiv` the same
  diagonal `radDeriv`. A fresh type (not a second instance on `RadExt`) avoids overlapping with the
  existing `radInv2`-based `instCFieldRadExt`.
* **`CFieldN3` / the cube root `∛(x²+1)` over ℚ(x)** — the concrete carrier
  `RadExtN (QFunNZG ℚ) 3 (x²+1)`, an honest computable field: `y³ − (x²+1)` is **irreducible** over
  ℚ(x) (`x²+1` is not a perfect cube — `intDegree 2` is not divisible by `3`), proven via
  `X_pow_sub_C_irreducible_of_prime` (prime `3`).
* **★ the milestone (`native_decide`)** — over the cube-root carrier, the diagonal derivation
  `D(y) = (f'/(3f))·y` for `y = ∛(x²+1)` fires through `CDiffField.cderiv`, the cube `y·y·y = f`
  folds (`radMul 3 f`), and `u · u⁻¹ = 1` holds with `u⁻¹ = radInvN 3 f u` — the engine
  differentiating/multiplying/inverting over a **cube** root, not just a square root.

**Soundness note.** `radDeriv`-is-a-derivation is already proven `n`-generic in
`ComputableRadicalDerivationInvariant` (`toPolyG_radDeriv_radAdd`, `mk_toPolyG_radDeriv_radMul` —
additivity and Leibniz over `α[y]/(yⁿ − f)` for every `n`), so the abstract derivation laws of the
cube-root carrier `RadExtN α 3 f` are *inherited* from that `n`-generic result: nothing in the
derivation soundness is `n = 2`-specific. What this file adds beyond `n = 2` is the **inverse**
(`radInvN`) and a fresh field carrier around it; the genuine-field justification is the `n`-generic
irreducibility criterion (`X_pow_sub_C_irreducible_of_prime`). The `radInvN` correctness itself —
`toK (radInvN g) = (toK g)⁻¹` from the `cbezoutOne` Bézout identity read through `toPolyG` modulo the
`radIdeal` — is the natural next abstract step (the Bézout helper's `toPolyG`-image identity already
lives in `ComputableCanonicalRepCorrect`); here it is `native_decide`-validated. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem

namespace RadElem

variable {α : Type*} [CField α]

/-! ### The defining modulus `yⁿ − f` and the general-`n` inverse `radInvN`

The modulus `yⁿ − f ∈ α[y]` as a dense coefficient list, then the inverse of `g` in `α[y]/(yⁿ − f)`
by extended Euclid: solve `s·g + t·(yⁿ − f) = 1` and reduce `s` mod `yⁿ = f`. -/

/-- **The defining modulus `yⁿ − f`** `radModulus n f = [−f, 0, …, 0, 1]` (constant `−f`, then `n − 1`
zeros, then `1` at index `n`) as a `CPolyG α`: `cshiftG n [1] − [f] = yⁿ − f`. The polynomial whose
quotient is `α[y]/(yⁿ − f) = RadExt α n f`. -/
def radModulus (n : ℕ) (f : α) : CPolyG α :=
  CPolyG.csubG (CPolyG.cshiftG n [CField.one]) [f]

/-- **The general-`n` inverse** `radInvN n f g` of `g ∈ α[y]/(yⁿ − f)` via the **extended Euclidean
algorithm** in `α[y]`: from `cbezoutOne fuel g (yⁿ − f) = (s, t)` with `s·g + t·(yⁿ − f) = 1` (valid
when `yⁿ − f` is irreducible, so `g` is a unit), the inverse is `s mod (yⁿ = f)` — because the
modulus `≡ 0`, `s·g ≡ 1`. The Bézout cofactor `s` is reduced to degree `< n` by `radReduce`. Fuel for
both `cbezoutOne` and `radReduce` is `2·(n + len g) + 2`, comfortably above the degrees involved
(`deg s < n`, the Euclid recursion length `≤ n + 1`). Generic over `[CField α]` and `n`; the honest
field inverse whenever `yⁿ − f` is irreducible (Trager's algebraic-extension reciprocal). -/
def radInvN (n : ℕ) (f : α) (g : RadElem α) : RadElem α :=
  let fuel := 2 * (n + (g : List α).length) + 2
  let (s, _) := CPolyG.cbezoutOne fuel g (radModulus n f)
  radReduce n f fuel s

end RadElem

/-! ### Sanity: `radInvN` inverts, and agrees with `radInv2` at `n = 2` (`native_decide`)

Over `ℚ(x)`, `n = 2`, `f = x²+1` (the `arcsinh` radical): `radInvN` produces a genuine inverse, and
it matches `radInv2` up to the canonical (reduced) representative. -/

open RadElem

/-- **★ `radInvN` inverts at `n = 2`** (`native_decide`): over `(QFunNZG ℚ)[y]/(y² − (x²+1))`, for
`u = x + y`, the extended-Euclid inverse `radInvN 2 (x²+1) u` satisfies `radMul 2 (x²+1) u (radInvN …)
= 1` (checked by `radIsZero` of the product minus `[1]`). THE GENERAL-`n` INVERSE COMPUTES AND
INVERTS — at `n = 2` it reproduces the conjugate-norm reciprocal through extended Euclid. -/
theorem radInvN_mul_self_eq_one_at_two :
    radIsZero (radSub (radMul 2 fullRhoArcsinh fullUxPlusY
        (radInvN 2 fullRhoArcsinh fullUxPlusY)) radOne) = true := by native_decide

/-- **`radInvN` agrees with `radInv2` at `n = 2`** (`native_decide`): the extended-Euclid inverse and
the conjugate-norm inverse are the **same** element of `(QFunNZG ℚ)[y]/(y² − (x²+1))` (both reduced),
for `u = x + y`. Checked by `radIsZero` of the difference `radInvN 2 ρ u − radInv2 ρ u`. The two
constructions coincide where both apply — `radInvN` is the honest generalization of `radInv2`. -/
theorem radInvN_eq_radInv2_at_two :
    radIsZero (radSub (radInvN 2 fullRhoArcsinh fullUxPlusY)
        (radInv2 fullRhoArcsinh fullUxPlusY)) = true := by native_decide

/-! ### The fresh carrier `RadExtN α n f` — a field for *every* `n` via `radInvN`

`RadExt α n f`'s `CField` instance (`instCFieldRadExt`) uses the conjugate-norm `radInv2`, an honest
inverse only at `n = 2`. To get a field for arbitrary `n` we wrap the same `RadElem α` in a **fresh**
one-field structure `RadExtN α n f` whose `inv` is `radInvN` — avoiding an overlapping `CField`
instance on `RadExt`. Everything else (`add`/`mul`/`neg`/`isZero`, `cderiv`) is the identical
radical-carrier computation; only the inverse differs. The structure inherits nothing, so the
algebra is attached explicitly. -/

/-- **The general-`n` simple-radical carrier as a type** `RadExtN α n f = α[y]/(yⁿ − f)`, a one-field
structure wrapping `RadElem α`, with `n`/`f` on the type so typeclass resolution dispatches the
radical `CField`/`CDiffField`. Distinct from `RadExt` so its `CField` inverse can be the general-`n`
`radInvN` (honest for every irreducible `yⁿ − f`) without overlapping `RadExt`'s `radInv2`-based
instance. `ofRadN ::`/`toRadN` are the constructor/projection. -/
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

/-- **Addition** in `RadExtN α n f` — componentwise `radAdd`, canonicalized to degree `< n`. -/
def add (p q : RadExtN α n f) : RadExtN α n f := ⟨RadExt.radCanon n f (radAdd p.toRadN q.toRadN)⟩

/-- **Negation** in `RadExtN α n f` — componentwise `radNeg`, canonicalized to degree `< n`. -/
def neg (p : RadExtN α n f) : RadExtN α n f := ⟨RadExt.radCanon n f (radNeg p.toRadN)⟩

/-- **Multiplication** in `RadExtN α n f` — `radMul n f` (poly-multiply in `y`, reduce `yⁿ → f`),
canonicalized. -/
def mul (p q : RadExtN α n f) : RadExtN α n f := ⟨RadExt.radCanon n f (radMul n f p.toRadN q.toRadN)⟩

/-- **Inverse** in `RadExtN α n f` (the general-`n` field case) — the **canonicalized**
extended-Euclidean inverse `radInvN`: reduce the input to a degree-`< n` rep before `radInvN` and
canonicalize the output. The honest field inverse whenever `yⁿ − f` is irreducible. -/
def inv (p : RadExtN α n f) : RadExtN α n f :=
  ⟨RadExt.radCanon n f (radInvN n f (RadExt.radCanon n f p.toRadN))⟩

/-- **Zero test** in `RadExtN α n f` — reduce `mod yⁿ = f` first, then `radIsZero`. -/
def isZero (p : RadExtN α n f) : Bool := radIsZero (RadExt.radCanon n f p.toRadN)

end RadExtN

/-- **`CField (RadExtN α n f)`**: the simple-radical extension `α[y]/(yⁿ − f)` as a *computable* field
for **arbitrary `n`** (over `[CField α]`). Identical to `RadExt`'s ring ops, but `inv := RadExtN.inv`
is the general-`n` extended-Euclidean `radInvN` (honest whenever `yⁿ − f` is irreducible), not the
`n = 2` conjugate-norm. Computable — all list/field arithmetic plus the engine's `cbezoutOne`. The
instance that makes a **cube** root (and any `nth` root) an honest computable field. -/
instance instCFieldRadExtN {α : Type*} [CField α] {n : ℕ} {f : α} : CField (RadExtN α n f) where
  zero := RadExtN.zero
  one := RadExtN.one
  add := RadExtN.add
  mul := RadExtN.mul
  neg := RadExtN.neg
  inv := RadExtN.inv
  isZero := RadExtN.isZero

/-- **`CDiffField (RadExtN α n f)`**: the general-`n` radical extension as a *computable differential*
field (over `[CField α] [CDiffField α]`). `cderiv := radDeriv n f` is the same **diagonal** derivation
extending `α`'s `cderiv` by `y' = (f'/(nf))·y`; its additivity/Leibniz laws are the `n`-generic
`RadElem.toPolyG_radDeriv_radAdd` / `RadElem.mk_toPolyG_radDeriv_radMul`
(`ComputableRadicalDerivationInvariant`), so the cube-root carrier is a genuine differential field
with **no** `n = 2` specialization. Computable, so the tower derivation reduces. -/
instance instCDiffFieldRadExtN {α : Type*} [CField α] [CDiffField α] {n : ℕ} {f : α} :
    CDiffField (RadExtN α n f) where
  cderiv p := ⟨radDeriv n f p.toRadN⟩

/-! ### ★ The concrete cube root `∛(x²+1)` over `ℚ(x)` and its irreducibility

`α = QFunNZG ℚ ≅ ℚ(x)`, `n = 3`, `f = x²+1`. `RadX3root := RadExtN (QFunNZG ℚ) 3 cubeRadicand` is the
cube-root field `ℚ(x)[∛(x²+1)]`. It is an honest field because `y³ − (x²+1)` is **irreducible** over
ℚ(x): `x²+1` is not a perfect cube in ℚ(x) — a cube `b³` has `intDegree = 3·intDegree(b)` (divisible
by `3`), but `x²+1` has `intDegree = 2`, not divisible by `3`. Hence
`X_pow_sub_C_irreducible_of_prime` (prime `3`) applies. -/

/-- The cube radicand `f = x² + 1 ∈ ℚ(x)` (numerator `[1, 0, 1]` = `1 + x²`), `y = ∛(x²+1)`. The
`natDegree 2` (not divisible by `3`) is what makes `x²+1` a non-cube, hence `y³ − (x²+1)` irreducible. -/
def cubeRadicand : QFunNZG ℚ := qxOfNum [1, 0, 1]

/-- The cube-root field `ℚ(x)[∛(x²+1)] = RadExtN (QFunNZG ℚ) 3 (x²+1)`. -/
abbrev RadX3root : Type := RadExtN (QFunNZG ℚ) 3 cubeRadicand

/-- The cube-root generator `y = ∛(x²+1)` as an element of `RadX3root` (through `RadExtN.gen`). -/
def cubeGen : RadX3root := RadExtN.gen

/-- The diagonal multiplier `ℓ = f'/(3f) = 2x/(3(x²+1)) ∈ ℚ(x)` for `D(y) = ℓ·y`, `y = ∛(x²+1)`. -/
def cubeLogDer : QFunNZG ℚ := logDerRadicand 3 cubeRadicand

/-- **`1 + x² ≠ 0` in `ℚ[X]`** (it has `natDegree 2`). -/
theorem X2p1_ne_zero : (1 + X ^ 2 : ℚ[X]) ≠ 0 := by
  intro h
  have := congrArg Polynomial.natDegree h
  rw [add_comm, Polynomial.natDegree_add_eq_left_of_natDegree_lt (by simp), natDegree_X_pow] at this
  simp at this

/-- **`natDegree (1 + x²) = 2`** in `ℚ[X]` (the leading `x²` dominates the constant `1`). -/
theorem natDeg_X2p1 : (1 + X ^ 2 : ℚ[X]).natDegree = 2 := by
  rw [add_comm, Polynomial.natDegree_add_eq_left_of_natDegree_lt (by simp), natDegree_X_pow]

open CPolyG in
/-- **`toK cubeRadicand = algebraMap (1 + x²)`** in `RatFunc ℚ`: the ℚ(x)-radicand of `RadX3root`
reads, through the tower bridge `toQFunNZG`, as `algebraMap ℚ[X] (RatFunc ℚ) (1 + x²)` (numerator
`[1,0,1] ↦ 1 + x²`, denominator `[1] ↦ 1`). Feeds the not-a-cube / irreducibility argument. -/
theorem toK_cubeRadicand :
    CFieldSpec.toK (cubeRadicand : QFunNZG ℚ) = algebraMap (ℚ[X]) (RatFunc ℚ) (1 + X ^ 2) := by
  show QFunNZG.toQFunNZG cubeRadicand = _
  rw [QFunNZG.toQFunNZG]
  show QFunNZG.amG ℚ (toPolyG ([1, 0, 1] : CPolyG ℚ))
      / QFunNZG.amG ℚ (toPolyG ([CField.one] : CPolyG ℚ)) = _
  have h1 : toPolyG ([1, 0, 1] : CPolyG ℚ) = 1 + X ^ 2 := by
    simp only [toPolyG_cons, toPolyG_nil]
    show C (1 : ℚ) + X * (C 0 + X * (C 1 + X * 0)) = _
    simp; ring
  have h2 : toPolyG ([CField.one] : CPolyG ℚ) = 1 := by
    show C (CFieldSpec.toK (CField.one : ℚ)) + X * 0 = 1; simp [CFieldSpec.toK_one]
  rw [h1, h2]
  show QFunNZG.amG ℚ (1 + X ^ 2) / QFunNZG.amG ℚ 1 = _
  rw [map_one, div_one]; rfl

/-- **★ `x²+1` is not a cube in `ℚ(x)`**: `∀ b : RatFunc ℚ, b³ ≠ algebraMap (1 + x²)`. A cube `b³` has
`intDegree = 3·intDegree(b)` (divisible by `3`), but `algebraMap (1 + x²)` has
`intDegree = natDegree(1 + x²) = 2`, not divisible by `3`. The degree obstruction that makes the
cube-root extension a field. -/
theorem not_cube_X2p1 :
    ∀ b : RatFunc ℚ, b ^ 3 ≠ algebraMap (ℚ[X]) (RatFunc ℚ) (1 + X ^ 2) := by
  intro b hb
  have hrhs_ne : algebraMap (ℚ[X]) (RatFunc ℚ) (1 + X ^ 2) ≠ 0 := RatFunc.algebraMap_ne_zero X2p1_ne_zero
  have hb_ne : b ≠ 0 := by rintro rfl; rw [zero_pow (by norm_num)] at hb; exact hrhs_ne hb.symm
  have hdeg : (b ^ 3).intDegree = (algebraMap (ℚ[X]) (RatFunc ℚ) (1 + X ^ 2)).intDegree := by rw [hb]
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, sq, RatFunc.intDegree_mul (mul_ne_zero hb_ne hb_ne) hb_ne,
    RatFunc.intDegree_mul hb_ne hb_ne, RatFunc.intDegree_polynomial, natDeg_X2p1] at hdeg
  omega

/-- **★ `y³ − (x²+1)` is irreducible over `ℚ(x)`** — `Irreducible (X³ − C(toK cubeRadicand))` in
`(RatFunc ℚ)[X]`. By `X_pow_sub_C_irreducible_of_prime` (prime `3`) and `x²+1` not-a-cube
(`not_cube_X2p1`). So `AdjoinRoot (X³ − C(toK cubeRadicand)) = ℚ(x)[∛(x²+1)]` is a genuine **field** —
the algebraic fact underwriting the honest cube-root carrier `RadX3root`. -/
theorem irreducible_cubeRad :
    Irreducible (X ^ 3 - C (CFieldSpec.toK (cubeRadicand : QFunNZG ℚ))) := by
  rw [toK_cubeRadicand]
  exact X_pow_sub_C_irreducible_of_prime (by norm_num) not_cube_X2p1

/-- **The cube-root irreducibility as a `Fact`** — registers `Irreducible (X³ − C(toK cubeRadicand))`
so Mathlib's `AdjoinRoot.instField` resolves `Field (AdjoinRoot (X³ − C(toK cubeRadicand)))`, the
field `ℚ(x)[∛(x²+1)]`. -/
instance fact_irreducible_cubeRad :
    Fact (Irreducible (X ^ 3 - C (CFieldSpec.toK (cubeRadicand : QFunNZG ℚ)))) :=
  ⟨irreducible_cubeRad⟩

/-- **`ℚ(x)[∛(x²+1)]` is a field** — `Field (AdjoinRoot (X³ − C(toK cubeRadicand)))`, resolved from the
irreducibility `Fact`. The genuine cube-root field the carrier `RadX3root` represents. -/
noncomputable example : Field (AdjoinRoot (X ^ 3 - C (CFieldSpec.toK (cubeRadicand : QFunNZG ℚ)))) :=
  inferInstance

/-! ### ★★ The milestone: the engine differentiates/multiplies/inverts a CUBE root (`native_decide`)

Over the cube-root carrier `RadX3root = ℚ(x)[∛(x²+1)]`, exercised **through the typeclass
projections** (`CField.mul`, `CField.inv`, `CDiffField.cderiv` — confirming `instCFieldRadExtN` /
`instCDiffFieldRadExtN` dispatch):

* `y·y·y = f` — the cube of `y = ∛(x²+1)` folds `y³ → f = x²+1` (`radMul 3 f`);
* `D(y) = (f'/(3f))·y` — the diagonal derivation fires for a **cube** root (`radDeriv 3 f`,
  `ℓ = 2x/(3(x²+1))`);
* `u · u⁻¹ = 1` — the general-`n` extended-Euclid inverse `radInvN 3 f` is a genuine field inverse.

This is the engine handling a cube root, not just a square root — Trager's algebraic extension at
`n = 3`. -/

/-- **★★ `y·y·y = f` in `RadX3root` through `CField.mul`** (`native_decide`): the cube of the generator
`y = ∛(x²+1)` via the **typeclass** product `CField.mul` (dispatching to `radMul 3 (x²+1)`) folds
`y³ → f = x²+1`. Checked by `CField.isZero` of `y·y·y − f` (`f` lifted to `RadX3root` as
`⟨[x²+1]⟩`). THE CUBE FOLDS — the `CField (RadExtN …)` instance computes over a cube root. -/
theorem cube_gen_cubed_eq_radicand :
    CField.isZero (CField.sub (CField.mul (CField.mul cubeGen cubeGen) cubeGen)
      (⟨[cubeRadicand]⟩ : RadX3root)) = true := by native_decide

/-- **★★ `D(y) = (f'/(3f))·y` in `RadX3root` through `CDiffField.cderiv`** (`native_decide`): the
**typeclass** derivation `CDiffField.cderiv` (dispatching to the diagonal `radDeriv 3 (x²+1)`) sends
`y = ∛(x²+1)` to `ℓ·y`, `ℓ = f'/(3f) = 2x/(3(x²+1))`. Checked by `CField.isZero` of `D(y) − [0, ℓ]`.
THE CUBE-ROOT CARRIER IS A DIFFERENTIAL FIELD — the diagonal derivation fires for `n = 3`. -/
theorem cube_cderiv_gen_eq :
    CField.isZero (CField.sub (CDiffField.cderiv cubeGen)
      (⟨[CField.zero, cubeLogDer]⟩ : RadX3root)) = true := by native_decide

/-- **★★ `u · u⁻¹ = 1` in `RadX3root` through `CField.mul`/`CField.inv`** (`native_decide`, the
milestone). For `u = x + y` (`= ⟨[x, 1]⟩`, `y = ∛(x²+1)`), the **typeclass** inverse `CField.inv`
(the general-`n` extended-Euclid `radInvN 3 (x²+1)`) satisfies `u · u⁻¹ = 1`. THE CUBE-ROOT
EXTENSION IS A COMPUTABLE FIELD — `radInvN` inverts at `n = 3`, not just `n = 2`. Checked by
`CField.isZero` of `u · u⁻¹ − 1`. -/
theorem cube_mul_inv_eq_one :
    CField.isZero (CField.sub (CField.mul (⟨[qxOfNum [0, 1], CField.one]⟩ : RadX3root)
      (CField.inv (⟨[qxOfNum [0, 1], CField.one]⟩ : RadX3root))) CField.one) = true := by
  native_decide

/-- **A cube-root inverse with a genuine `y²`-component** (`native_decide`): for `u = 1 + y + y²`
(`= ⟨[1, 1, 1]⟩`, degree `2` over the cube root), `radInvN 3 (x²+1)` still inverts —
`CField.mul u u⁻¹ = 1`. The extended-Euclid inverse handles a **full-degree** element of the cube-root
field, not only a binomial `a + by`; the conjugate-norm `radInv2` could not (it reads only `y⁰`/`y¹`). -/
theorem cube_mul_inv_eq_one_deg2 :
    CField.isZero (CField.sub (CField.mul (⟨[CField.one, CField.one, CField.one]⟩ : RadX3root)
      (CField.inv (⟨[CField.one, CField.one, CField.one]⟩ : RadX3root))) CField.one) = true := by
  native_decide

/-- **`D(1) = 0` and `D(0) = 0` in `RadX3root`** (`native_decide`): the cube-root derivation
annihilates the unit and zero (the diagonal `radDeriv`'s `i = 0` component, base `D(1) = 0`). -/
theorem cube_cderiv_one_zero :
    CField.isZero (CDiffField.cderiv (CField.one : RadX3root)) = true ∧
    CField.isZero (CDiffField.cderiv (CField.zero : RadX3root)) = true := by
  constructor <;> native_decide

end DeepWiki.SymbolicIntegration
