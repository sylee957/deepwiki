import DeepWiki.SymbolicIntegration.GenericPolyEngine
import DeepWiki.SymbolicIntegration.ComputableFieldGcd
import DeepWiki.SymbolicIntegration.ComputableLogPartTower

/-! # Arbitrary-depth differential towers: the generic fraction field `QFunNZG α`
The Risch algorithm runs the polynomial engine over a **tower** ℚ ⊂ ℚ(x) ⊂ ℚ(x)(t₁) ⊂ … . The
existing `QFunNZ` (`ComputableField`/`ComputableFieldGcd`) builds *one* level — ℚ(x) as a `CField`
over `CPoly = ℚ[x]`. This file makes that step **generic over the carrier**: given a level `[CField α]`,
`QFunNZG α` is the fraction field of `CPolyG α = α[t]` (denominator-nonzero fraction pairs), with a
*computable* `CField (QFunNZG α)` instance (the engine ops); adding `[CFieldSpec α]` gives a
noncomputable `CFieldSpec (QFunNZG α)` bridge into `RatFunc (CFieldSpec.K α)`. Iterating gives the
tower: `QFunNZG ℚ ≅ ℚ(x)`, `QFunNZG (QFunNZG ℚ) ≅ ℚ(x)(t₁)`, ….

The keystone `CField`/`CFieldSpec` split (`GenericPolyEngine`) is what makes this work, and the crucial
design point is that **the carrier `QFunNZG α` and its `CField` instance need only `[CField α]`** — the
denominator-nonzero condition is stated with the `[CField α]`-only `cisZeroG` test, NOT the `[CFieldSpec
α]`-valued `toPolyG`. So `QFunNZG (QFunNZG ℚ)` carries no noncomputable dependency, and `CPolyG (QFunNZG
(QFunNZG ℚ))` **reduces in the native compiler**: the headline `native_decide` here runs the generic
engine (`cgcdExtG`/`cresultantG`/`cmulG`/`cisZeroG`) at **tower level 2** over `ℚ(x)(t₁)[t₂]`. The
`CFieldSpec` bridge (and the homomorphism laws) is needed only by the correctness layer.

The QFunNZ-hardwired `cgcdFF` is *not* generic yet — generalizing it off
the concrete `QFunNZ` carrier is the next step; here the validation runs the **generic** engine ops,
which already accept any `[CField α]`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {α : Type*} [CField α]

/-! ### The generic fraction pair `QFunG α` and its computable arithmetic

`QFunG α := CPolyG α × CPolyG α` is a `(numerator, denominator)` fraction over `α[t]`, the generic
mirror of the concrete `Compute.QFun = CPoly × CPoly`. The arithmetic `qzeroG`/`qoneG`/`qaddG`/`qmulG`/
`qnegG`/`qinvG` cross-multiplies through the generic engine ops (`caddG`/`cmulG`/`cnegG`), using *no*
`toK`/`CFieldSpec`, so it stays computable. Fractions are kept **unreduced** (no gcd-cancel): correctness
over performance for the first tower step, matching `Compute.qadd`. -/

/-- **Generic fraction pair** `(numerator, denominator)` over `α[t] = CPolyG α`; the generic mirror of
`Compute.QFun`. `qzeroG = 0/1`. -/
abbrev QFunG (α : Type*) [CField α] := CPolyG α × CPolyG α

namespace QFunG

/-- **Generic zero fraction** `0/1` (numerator `[]`, denominator `[1]`). -/
def qzeroG : QFunG α := ([], [CField.one])

/-- **Generic one fraction** `1/1` (numerator `[1]`, denominator `[1]`). -/
def qoneG : QFunG α := ([CField.one], [CField.one])

/-- **Generic fraction addition** `a/b + c/d = (a·d + c·b)/(b·d)` (cross-multiply, no gcd reduction). -/
def qaddG (x y : QFunG α) : QFunG α :=
  let (a, b) := x
  let (c, d) := y
  (CPolyG.caddG (CPolyG.cmulG a d) (CPolyG.cmulG c b), CPolyG.cmulG b d)

/-- **Generic fraction multiplication** `(a/b)·(c/d) = (a·c)/(b·d)`. -/
def qmulG (x y : QFunG α) : QFunG α :=
  (CPolyG.cmulG x.1 y.1, CPolyG.cmulG x.2 y.2)

/-- **Generic fraction negation** `−(a/b) = (−a)/b` (denominator unchanged). -/
def qnegG (x : QFunG α) : QFunG α := (CPolyG.cnegG x.1, x.2)

/-- **Generic fraction inverse** `(a/b)⁻¹ = b/a`; if the numerator is the zero polynomial the result is
`qzeroG` (the `0⁻¹ = 0` field convention). -/
def qinvG (x : QFunG α) : QFunG α :=
  if CPolyG.cisZeroG x.1 then qzeroG else (x.2, x.1)

/-- **Generic fraction subtraction** `a/b − c/d := a/b + (−(c/d))`. -/
def qsubG (x y : QFunG α) : QFunG α := qaddG x (qnegG y)

end QFunG

/-! ### The denominator-nonzero subtype `QFunNZG α` (the tower-level carrier)

`QFunNZG α := { x : QFunG α // cisZeroG x.2 = false }` restricts to fractions whose denominator is a
**nonzero** polynomial. CRITICAL: the membership predicate uses the `[CField α]`-only zero test
`cisZeroG` (NOT the `[CFieldSpec α]`-valued `toPolyG`), so the *type* and its `CField` instance need
only `[CField α]` — no noncomputable dependency leaks into the carrier, and `CPolyG (QFunNZG (…))`
reduces in the native compiler. The predicate is also a `Prop` (erased at runtime). Den-nonzero is
preserved by `qaddNZG`/`qmulNZG`/`qnegNZG`/`qinvNZG` (the product denominators are nonzero — `cisZeroG
(cmulG b d) = false`, via the integral-domain fact `toPolyG_cmulG`, available once `[CFieldSpec α]` is
in scope). -/

/-- **Denominator-nonzero generic fractions**: the subtype of `QFunG α` whose denominator passes the
`[CField α]`-only nonzero test `cisZeroG _ = false`. The carrier of the next tower level — `QFunNZG ℚ ≅
ℚ(x)`, `QFunNZG (QFunNZG ℚ) ≅ ℚ(x)(t₁)`, …. The *type* needs only `[CField α]` (the predicate is the
`cisZeroG` test, not the `CFieldSpec`-valued `toPolyG`), so the level-2 carrier `QFunNZG (QFunNZG ℚ)`
carries no noncomputable dependency and `CPolyG (QFunNZG α)` reduces in the native compiler. -/
def QFunNZG (α : Type*) [CField α] : Type _ :=
  { x : QFunG α // CPolyG.cisZeroG x.2 = false }

/-! #### The pure-`CField` domain class `CFieldDomain`

The den-nonzero **closure facts** the ops need — `cisZeroG [1] = false` and `cisZeroG (cmulG b d) =
false` from nonzero factors — are NOT consequences of `[CField α]` alone (`CField` carries no law
linking `one`/`mul` with `isZero`; over a degenerate carrier they could fail). They ARE integral-domain
facts, true on every `[CFieldSpec α]` level. To keep the `CField (QFunNZG α)` instance **off the
noncomputable `CFieldSpec`** (so the tower `native_decide`s), they are packaged in a *separate
typeclass* `CFieldDomain α` stated in **pure `CField`/`CPolyG` terms** (no `toPolyG`/`CFieldSpec`). The
instance requires `[CFieldDomain α]`; the `CFieldDomain` instances (`ℚ`, and recursively `QFunNZG α`)
are *built* from `[CFieldSpec α]` but provide only `Prop` fields, which are erased — so no noncomputable
data reaches the native compiler. This is the `CField`/`CFieldSpec` split applied to the closure facts. -/

/-- **Polynomial-domain facts over a `CField`**, stated in pure `CField`/`CPolyG` terms: the constant
`[1]` is `cisZeroG`-nonzero, and the product of two `cisZeroG`-nonzero `CPolyG`s is `cisZeroG`-nonzero
(no zero divisors). Carries *no* `CFieldSpec` data, so it can gate the **computable** `CField (QFunNZG
α)` instance; its instances are built from `[CFieldSpec α]` but expose only `Prop` fields (erased at
runtime). The denominator-nonzero closure the fraction-field tower is built on. -/
class CFieldDomain (α : Type*) [CField α] where
  /-- The constant `[1]` is `cisZeroG`-nonzero. -/
  nz_one : CPolyG.cisZeroG ([CField.one] : CPolyG α) = false
  /-- The product of two `cisZeroG`-nonzero `CPolyG`s is `cisZeroG`-nonzero (no zero divisors). -/
  nz_mul : ∀ {b d : CPolyG α}, CPolyG.cisZeroG b = false → CPolyG.cisZeroG d = false →
    CPolyG.cisZeroG (CPolyG.cmulG b d) = false

/-- **Every `[CFieldSpec α]` level is a `CFieldDomain`** (a global `instance`): the two pure-`CField`
closure facts hold because `(CFieldSpec.K α)[X]` is an integral domain — `toPolyG [1] = 1 ≠ 0` and
`toPolyG (cmulG b d) = toPolyG b · toPolyG d` (no zero divisors). This is the recursive step: at every
tower level `QFunNZG α` (which has a `CFieldSpec`) it supplies the `CFieldDomain` the *next* level's
`CField` instance needs. It provides only `Prop` fields, so although it is built from the noncomputable
`CFieldSpec`, it is **erased at runtime** and does not block the tower's `native_decide`. There is no
resolution loop — `CFieldDomain` never appears as a `CFieldSpec` hypothesis. -/
noncomputable instance instCFieldDomainOfCFieldSpec {α : Type*} [CField α] [CFieldSpec α] :
    CFieldDomain α where
  nz_one := by
    rw [Bool.eq_false_iff, Ne, CPolyG.cisZeroG_iff, CPolyG.toPolyG_cons, CPolyG.toPolyG_nil,
      CFieldSpec.toK_one, mul_zero, add_zero, map_one]
    exact one_ne_zero
  nz_mul := by
    intro b d hb hd
    rw [Bool.eq_false_iff] at hb hd ⊢
    rw [Ne, CPolyG.cisZeroG_iff] at hb hd ⊢
    rw [CPolyG.toPolyG_cmulG]
    exact mul_ne_zero hb hd

namespace QFunNZG

variable [CFieldDomain α]

/-- **The constant `[1]` is `cisZeroG`-nonzero** (from `CFieldDomain`): the denominator-nonzero witness
for `qzeroNZG`/`qoneNZG`. -/
theorem cisZeroG_one_singleton : CPolyG.cisZeroG ([CField.one] : CPolyG α) = false :=
  CFieldDomain.nz_one

/-- **The product of two `cisZeroG`-nonzero generic polynomials is `cisZeroG`-nonzero** (from
`CFieldDomain`): keeps the den-nonzero subtype closed under `qaddNZG`/`qmulNZG`. -/
theorem cmulG_ne_zero_of {b d : CPolyG α} (hb : CPolyG.cisZeroG b = false)
    (hd : CPolyG.cisZeroG d = false) : CPolyG.cisZeroG (CPolyG.cmulG b d) = false :=
  CFieldDomain.nz_mul hb hd

/-- `qzeroNZG`: the zero fraction `0/1` as a `QFunNZG` (denominator `[1]` is nonzero). -/
def qzeroNZG : QFunNZG α := ⟨QFunG.qzeroG, cisZeroG_one_singleton⟩

/-- `qoneNZG`: the one fraction `1/1` as a `QFunNZG` (denominator `[1]` is nonzero). -/
def qoneNZG : QFunNZG α := ⟨QFunG.qoneG, cisZeroG_one_singleton⟩

/-- `qaddNZG`: addition on `QFunNZG` (the product denominator `b·d` is nonzero). -/
def qaddNZG (x y : QFunNZG α) : QFunNZG α :=
  ⟨QFunG.qaddG x.1 y.1, by
    obtain ⟨⟨a, b⟩, hb⟩ := x
    obtain ⟨⟨c, d⟩, hd⟩ := y
    exact cmulG_ne_zero_of hb hd⟩

/-- `qmulNZG`: multiplication on `QFunNZG` (the product denominator `b·d` is nonzero). -/
def qmulNZG (x y : QFunNZG α) : QFunNZG α :=
  ⟨QFunG.qmulG x.1 y.1, by
    obtain ⟨⟨a, b⟩, hb⟩ := x
    obtain ⟨⟨c, d⟩, hd⟩ := y
    exact cmulG_ne_zero_of hb hd⟩

/-- `qnegNZG`: negation on `QFunNZG` (denominator unchanged). -/
def qnegNZG (x : QFunNZG α) : QFunNZG α := ⟨QFunG.qnegG x.1, x.2⟩

/-- `qinvNZG`: inverse on `QFunNZG`. If the numerator's zero test holds, the result is `qzeroNZG` (the
`0⁻¹ = 0` convention); otherwise swap numerator and denominator (the new denominator is the old
numerator, nonzero exactly by `¬ cisZeroG`). -/
def qinvNZG (x : QFunNZG α) : QFunNZG α :=
  if h : CPolyG.cisZeroG x.1.1 then qzeroNZG
  else ⟨(x.1.2, x.1.1), Bool.not_eq_true _ ▸ h⟩

/-- `qsubNZG`: subtraction on `QFunNZG`, `x − y := x + (−y)`. -/
def qsubNZG (x y : QFunNZG α) : QFunNZG α := qaddNZG x (qnegNZG y)

/-- `isZeroNZG`: the zero test on `QFunNZG`, reading `cisZeroG` off the **numerator** (the denominator
is nonzero by membership, so `x = 0` iff its numerator vanishes). -/
def isZeroNZG (x : QFunNZG α) : Bool := CPolyG.cisZeroG x.1.1

end QFunNZG

/-! ### The computable `CField (QFunNZG α)` instance

The tower-level field operations are honest list computations through the generic engine
(`qaddNZG`/…/`isZeroNZG`), with the den-nonzero proofs `Prop`-erased. The membership proofs use only
`[CFieldDomain α]` (the pure-`CField` closure facts), so the instance is **computable** — `CPolyG
(QFunNZG (…))` reduces one level up. This is exactly the `CField`/`CFieldSpec` split, mirroring the
concrete `QFunNZ`. -/

section
variable [CFieldDomain α]

/-- **`CField (QFunNZG α)`**: the next tower level (the fraction field of `α[t]`) as a *computable*
field (over `[CField α] [CFieldDomain α]`, no `CFieldSpec`). `zero`/`one`/`add`/`mul`/`neg`/`inv` and
`isZero` are list computations through the generic engine, the membership proofs `Prop`-erased — so the
engine `caddG`/`cmulG`/`cgcdExtG`/… reduces over `CPolyG (QFunNZG α)` (`native_decide`). Iterating builds
the differential tower ℚ(x)(t₁)(t₂)…. -/
instance instCFieldQFunNZG : CField (QFunNZG α) where
  zero := QFunNZG.qzeroNZG
  one := QFunNZG.qoneNZG
  add := QFunNZG.qaddNZG
  mul := QFunNZG.qmulNZG
  neg := QFunNZG.qnegNZG
  inv := QFunNZG.qinvNZG
  isZero := QFunNZG.isZeroNZG

end

/-! ### The bridge `toQFunNZG` into `RatFunc (CFieldSpec.K α)` and its homomorphism laws

`toQFunNZG ⟨(a, b), _⟩ = am (toPolyG a) / am (toPolyG b)` with `am = algebraMap (CFieldSpec.K α)[X]
(RatFunc (CFieldSpec.K α))`, the generic mirror of `Compute.toQFun`. Each `CField (QFunNZG α)` operation
realizes the corresponding `RatFunc (CFieldSpec.K α)` field operation — the homomorphism laws below,
the generalizations of the `toQFunNZ_*` lemmas. The denominator-nonzero side-conditions are discharged
by subtype membership (`am` injective on `≠ 0`). `toQFunNZG` need NOT be injective (unreduced fractions
share images) — the engine tests `K`-equality through `isZero`, certified by `isZeroNZG_iff`. From here
the bridge `[CFieldSpec α]` is back in scope (the homomorphism laws reference `toPolyG`). -/

namespace QFunNZG

variable [CFieldSpec α] [CFieldDomain α]

omit [CFieldDomain α] in
/-- `amG = algebraMap (CFieldSpec.K α)[X] (RatFunc (CFieldSpec.K α))`, the polynomial-into-rational
embedding for the bridge. -/
noncomputable abbrev amG (α : Type*) [CField α] [CFieldSpec α] :
    (CFieldSpec.K α)[X] →+* RatFunc (CFieldSpec.K α) :=
  algebraMap (CFieldSpec.K α)[X] (RatFunc (CFieldSpec.K α))

omit [CFieldDomain α] in
/-- `amG (toPolyG p) ≠ 0` whenever `toPolyG p ≠ 0` (the embedding `algebraMap K[X] (RatFunc K)` is
injective). -/
theorem amG_toPolyG_ne_zero {p : CPolyG α} (hp : CPolyG.toPolyG p ≠ 0) :
    amG α (CPolyG.toPolyG p) ≠ 0 :=
  (map_ne_zero_iff _ (RatFunc.algebraMap_injective (CFieldSpec.K α))).mpr hp

omit [CFieldDomain α] in
/-- `cisZeroG b = false` reads as `toPolyG b ≠ 0` (the denominator nonzero criterion through the
bridge). -/
theorem toPolyG_ne_zero_of_cisZeroG_false {b : CPolyG α} (hb : CPolyG.cisZeroG b = false) :
    CPolyG.toPolyG b ≠ 0 := by
  rw [Bool.eq_false_iff, Ne, CPolyG.cisZeroG_iff] at hb; exact hb

/-- **`toQFunNZG` reads a `QFunNZG` into `RatFunc (CFieldSpec.K α)`**: `(num, den) ↦ amG (toPolyG num) /
amG (toPolyG den)`. The bridge `toK` of the next tower level. -/
noncomputable def toQFunNZG (x : QFunNZG α) : RatFunc (CFieldSpec.K α) :=
  amG α (CPolyG.toPolyG x.1.1) / amG α (CPolyG.toPolyG x.1.2)

/-- **`toQFunNZG` reads `qzeroNZG` as `0`**. -/
theorem toQFunNZG_qzeroNZG : toQFunNZG (qzeroNZG : QFunNZG α) = 0 := by
  rw [toQFunNZG]
  show amG α (CPolyG.toPolyG ([] : CPolyG α)) / _ = 0
  rw [CPolyG.toPolyG_nil, map_zero, zero_div]

/-- **`toQFunNZG` reads `qoneNZG` as `1`**. -/
theorem toQFunNZG_qoneNZG : toQFunNZG (qoneNZG : QFunNZG α) = 1 := by
  rw [toQFunNZG]
  show amG α (CPolyG.toPolyG ([CField.one] : CPolyG α))
      / amG α (CPolyG.toPolyG ([CField.one] : CPolyG α)) = 1
  have h1 : CPolyG.toPolyG ([CField.one] : CPolyG α) = 1 := by
    rw [CPolyG.toPolyG_cons, CPolyG.toPolyG_nil, CFieldSpec.toK_one, mul_zero, add_zero, map_one]
  rw [h1, map_one, div_self one_ne_zero]

/-- **`qaddNZG` realizes `+`** on `QFunNZG`: `toQFunNZG (qaddNZG x y) = toQFunNZG x + toQFunNZG y` (the
denominator-nonzero side-conditions discharged by membership). -/
theorem toQFunNZG_qaddNZG (x y : QFunNZG α) :
    toQFunNZG (qaddNZG x y) = toQFunNZG x + toQFunNZG y := by
  obtain ⟨⟨a, b⟩, hb⟩ := x
  obtain ⟨⟨c, d⟩, hd⟩ := y
  have hb' : amG α (CPolyG.toPolyG b) ≠ 0 :=
    amG_toPolyG_ne_zero (toPolyG_ne_zero_of_cisZeroG_false hb)
  have hd' : amG α (CPolyG.toPolyG d) ≠ 0 :=
    amG_toPolyG_ne_zero (toPolyG_ne_zero_of_cisZeroG_false hd)
  show amG α (CPolyG.toPolyG (CPolyG.caddG (CPolyG.cmulG a d) (CPolyG.cmulG c b)))
      / amG α (CPolyG.toPolyG (CPolyG.cmulG b d))
    = amG α (CPolyG.toPolyG a) / amG α (CPolyG.toPolyG b)
      + amG α (CPolyG.toPolyG c) / amG α (CPolyG.toPolyG d)
  rw [CPolyG.toPolyG_caddG, CPolyG.toPolyG_cmulG, CPolyG.toPolyG_cmulG, CPolyG.toPolyG_cmulG,
    map_add, map_mul, map_mul, map_mul, div_add_div _ _ hb' hd']
  ring

/-- **`qmulNZG` realizes `*`** on `QFunNZG`: `toQFunNZG (qmulNZG x y) = toQFunNZG x * toQFunNZG y`. -/
theorem toQFunNZG_qmulNZG (x y : QFunNZG α) :
    toQFunNZG (qmulNZG x y) = toQFunNZG x * toQFunNZG y := by
  obtain ⟨⟨a, b⟩, hb⟩ := x
  obtain ⟨⟨c, d⟩, hd⟩ := y
  show amG α (CPolyG.toPolyG (CPolyG.cmulG a c)) / amG α (CPolyG.toPolyG (CPolyG.cmulG b d))
    = amG α (CPolyG.toPolyG a) / amG α (CPolyG.toPolyG b)
      * (amG α (CPolyG.toPolyG c) / amG α (CPolyG.toPolyG d))
  rw [CPolyG.toPolyG_cmulG, CPolyG.toPolyG_cmulG, map_mul, map_mul, div_mul_div_comm]

omit [CFieldDomain α] in
/-- **`qnegNZG` realizes `-`** on `QFunNZG`: `toQFunNZG (qnegNZG x) = - toQFunNZG x`. -/
theorem toQFunNZG_qnegNZG (x : QFunNZG α) : toQFunNZG (qnegNZG x) = - toQFunNZG x := by
  obtain ⟨⟨a, b⟩, hb⟩ := x
  show amG α (CPolyG.toPolyG (CPolyG.cnegG a)) / amG α (CPolyG.toPolyG b)
    = - (amG α (CPolyG.toPolyG a) / amG α (CPolyG.toPolyG b))
  rw [CPolyG.toPolyG_cnegG, map_neg, neg_div]

/-- **`qinvNZG` realizes `⁻¹`** on `QFunNZG`: `toQFunNZG (qinvNZG x) = (toQFunNZG x)⁻¹` (the `0⁻¹ = 0`
convention matches `RatFunc`). -/
theorem toQFunNZG_qinvNZG (x : QFunNZG α) : toQFunNZG (qinvNZG x) = (toQFunNZG x)⁻¹ := by
  rw [qinvNZG]
  by_cases h : CPolyG.cisZeroG x.1.1
  · rw [dif_pos h, toQFunNZG_qzeroNZG]
    have hx0 : CPolyG.toPolyG x.1.1 = 0 := (CPolyG.cisZeroG_iff x.1.1).mp h
    have : toQFunNZG x = 0 := by
      rw [toQFunNZG, hx0, map_zero, zero_div]
    rw [this, inv_zero]
  · rw [dif_neg h]
    show amG α (CPolyG.toPolyG x.1.2) / amG α (CPolyG.toPolyG x.1.1)
      = (amG α (CPolyG.toPolyG x.1.1) / amG α (CPolyG.toPolyG x.1.2))⁻¹
    rw [inv_div]

/-- **`qsubNZG` realizes `-`** on `QFunNZG`: `toQFunNZG (qsubNZG x y) = toQFunNZG x - toQFunNZG y`. -/
theorem toQFunNZG_qsubNZG (x y : QFunNZG α) :
    toQFunNZG (qsubNZG x y) = toQFunNZG x - toQFunNZG y := by
  rw [qsubNZG, toQFunNZG_qaddNZG, toQFunNZG_qnegNZG, sub_eq_add_neg]

omit [CFieldDomain α] in
/-- **`isZeroNZG` is certified against `toQFunNZG = 0`**: `isZeroNZG x = true ↔ toQFunNZG x = 0` — the
numerator zero test agrees with vanishing in `RatFunc (CFieldSpec.K α)` (denominator nonzero by
membership). -/
theorem isZeroNZG_iff (x : QFunNZG α) : isZeroNZG x = true ↔ toQFunNZG x = 0 := by
  rw [isZeroNZG, CPolyG.cisZeroG_iff]
  obtain ⟨⟨a, b⟩, hb⟩ := x
  have hbm : amG α (CPolyG.toPolyG b) ≠ 0 :=
    amG_toPolyG_ne_zero (toPolyG_ne_zero_of_cisZeroG_false hb)
  show CPolyG.toPolyG a = 0 ↔ amG α (CPolyG.toPolyG a) / amG α (CPolyG.toPolyG b) = 0
  constructor
  · intro h; rw [h, map_zero, zero_div]
  · intro h
    rw [div_eq_zero_iff] at h
    rcases h with h | h
    · exact (map_eq_zero_iff _ (RatFunc.algebraMap_injective (CFieldSpec.K α))).mp h
    · exact absurd h hbm

end QFunNZG

variable [CFieldSpec α]

/-- **`CFieldSpec (QFunNZG α)`**: the field-homomorphism bridge for `CField (QFunNZG α)`, over `K =
RatFunc (CFieldSpec.K α)` with `toK = toQFunNZG`. The recursive step that builds the tower's
correctness layer: `CFieldSpec.K (QFunNZG α) = RatFunc (CFieldSpec.K α)`, so iterating gives
ℚ ↦ RatFunc ℚ ↦ RatFunc (RatFunc ℚ) ↦ …. Its `isZero` is the numerator zero test (no `toK`-injectivity
needed), generalizing the `QFunNZ` instance. Noncomputable (routes through `RatFunc`), but only the
correctness layer depends on it. -/
noncomputable instance instCFieldSpecQFunNZG : CFieldSpec (QFunNZG α) where
  K := RatFunc (CFieldSpec.K α)
  toK := QFunNZG.toQFunNZG
  toK_zero := QFunNZG.toQFunNZG_qzeroNZG
  toK_one := QFunNZG.toQFunNZG_qoneNZG
  toK_add := QFunNZG.toQFunNZG_qaddNZG
  toK_mul := QFunNZG.toQFunNZG_qmulNZG
  toK_neg := QFunNZG.toQFunNZG_qnegNZG
  toK_inv := QFunNZG.toQFunNZG_qinvNZG
  isZero_iff := QFunNZG.isZeroNZG_iff

/-! ### Tower level 1: `QFunNZG ℚ` and its relationship to the concrete `QFunNZ`

`QFunNZG ℚ` and the concrete `QFunNZ` (`ComputableField`) are **distinct but isomorphic** carriers of
ℚ(x): both are denominator-nonzero fraction pairs over `List ℚ`, but `QFunNZ` wraps `Compute.QFun =
CPoly × CPoly` with the *predicate* `toPoly den ≠ 0`, while `QFunNZG ℚ` wraps `QFunG ℚ = CPolyG ℚ ×
CPolyG ℚ` with the equivalent `[CField ℚ]`-only predicate `cisZeroG den = false`. Since `CPolyG ℚ` is
the reducible `abbrev` `List ℚ = CPoly`, the *underlying* pair types coincide (`QFunG ℚ = Compute.QFun`,
`rfl`); the predicates are equivalent by `cisZeroG (α := ℚ) = cisZero` and `cisZero_iff_toPoly_eq_zero`,
so the two subtypes carry the same fractions. The generic engine at `α = ℚ` agrees with the concrete one
by the coherence lemmas (`caddG_eq_cadd`/`cmulG_eq_cmul`/`toPolyG_eq_toPoly`). We keep `QFunNZG` as the
tower carrier (it iterates); `QFunNZ` remains the hand-built level-1 instance the existing pipeline uses. -/

/-- **Level-1 sanity**: the underlying pair type of `QFunG ℚ` is the concrete `Compute.QFun` (both are
`List ℚ × List ℚ`, since `CPolyG ℚ` is the `abbrev` `List ℚ = CPoly`). So `QFunNZG ℚ` and `QFunNZ`
fraction over the same pairs; they differ only by the (equivalent) den-nonzero predicate. -/
example : QFunG ℚ = Compute.QFun := rfl

/-- **Generic-to-concrete denominator coherence at `α = ℚ`**: `toPolyG (α := ℚ) = toPoly`, so the
`QFunNZG ℚ` predicate `cisZeroG den = false` is equivalent to the `QFunNZ` predicate `toPoly den ≠ 0`. -/
example (d : CPolyG ℚ) : CPolyG.toPolyG d = Compute.toPoly d :=
  congrFun CPolyG.toPolyG_eq_toPoly d

/-! ### ★ The key validation: the tower computes at LEVEL 2 (`ℚ(x)(t₁)[t₂]`)

These `native_decide` checks retire the "does the tower compute" risk. They run the **generic** engine
ops — `[CField α]`-generic, so they already accept any tower level — on concrete elements of
`CPolyG (QFunNZG (QFunNZG ℚ))` = `ℚ(x)(t₁)[t₂]` (level 2). The `CField (QFunNZG (QFunNZG ℚ))` instance
is `[CField …]`-computable (the carrier predicate is the `cisZeroG`-only test, no `CFieldSpec`) and the
subtype proofs are `Prop`-erased, so nothing noncomputable leaks into the native compiler. (The
QFunNZ-hardwired `cgcdFF` is not generic yet — that is the documented next step; the
validation here uses the already-generic `cgcdExtG`/`cresultantG`/`cmulG`/`cisZeroG`.) -/

/-- Tower level 2 abbreviation: `Lvl2 = QFunNZG (QFunNZG ℚ)`, the field ℚ(x)(t₁). The engine over
`CPolyG Lvl2 = ℚ(x)(t₁)[t₂]` is the second tower level. -/
abbrev Lvl2 : Type := QFunNZG (QFunNZG ℚ)

/-- **The scalar field operation reduces at level 2**: `1 + 1 ≠ 0` in `QFunNZG (QFunNZG ℚ) = ℚ(x)(t₁)`.
The `CField (QFunNZG (QFunNZG ℚ))` `add`/`isZero` run in the native compiler — two tower levels of
`Prop`-erased subtypes do not block reduction. -/
example : CField.isZero (CField.add (CField.one : Lvl2) CField.one) = false := by native_decide

/-- **`0 = 0` at level 2**: the level-2 scalar zero test reduces. -/
example : CField.isZero (CField.zero : Lvl2) = true := by native_decide

/-- **`1 ≠ 0` at level 2**. -/
example : CField.isZero (CField.one : Lvl2) = false := by native_decide

/-- **The polynomial product reduces over `CPolyG Lvl2` = `ℚ(x)(t₁)[t₂]`**: `(1 + t₂)·(1 + t₂) =
1 + 2t₂ + t₂²` is a degree-2 (length-3) normalized list — `native_decide` executes the whole `cmulG`
at **tower level 2**. -/
example :
    (CPolyG.cnormG (CPolyG.cmulG [(CField.one : Lvl2), CField.one] [CField.one, CField.one])
      : List Lvl2).length = 3 := by native_decide

/-- **The product is nonzero over `CPolyG Lvl2`** (the engine's `cisZeroG` reduces at level 2). -/
example :
    CPolyG.cisZeroG (CPolyG.cmulG [(CField.one : Lvl2), CField.one] [CField.one, CField.one])
      = false := by native_decide

/-- **★ The extended Euclidean algorithm reduces over `CPolyG Lvl2` = `ℚ(x)(t₁)[t₂]`**: `gcd(t₂, t₂) =
t₂` is nonzero, so its `cisZeroG` is `false` — `cgcdExtG` executes end to end at **tower level 2**.
This is the headline: the full gcd engine runs over `ℚ(x)(t₁)[t₂]`. -/
example :
    CPolyG.cisZeroG (CPolyG.cgcdExtG 8 [(CField.zero : Lvl2), CField.one]
      [(CField.zero : Lvl2), CField.one]).1 = false := by native_decide

/-- **★ The generic resultant reduces over `CPolyG Lvl2` = `ℚ(x)(t₁)[t₂]`**: `res(t₂, 1 + t₂) = 1`
(the resultant of `t₂` with the linear `1 + t₂`), evaluated as a level-2 scalar — `cresultantG`
executes end to end at **tower level 2**. -/
example :
    CField.isZero
      (CPolyG.cresultantG 8 [(CField.zero : Lvl2), CField.one] [CField.one, CField.one]) = false := by
  native_decide

/-- **The level-2 sum of two genuine ℚ(x)(t₁) scalars reduces**: building `c₁ + c₂` where `c₁ = 1/1`
and `c₂` is the inverse `(t₁)⁻¹ = 1/t₁` at level 2, the `add`/`isZero` engine runs natively — exercising
a non-trivial `QFunNZG (QFunNZG ℚ)` fraction, not just `0`/`1`. -/
example :
    CField.isZero
      (CField.add (CField.one : Lvl2)
        (CField.inv ⟨([(CField.zero : QFunNZG ℚ), CField.one], [CField.one]),
          QFunNZG.cisZeroG_one_singleton⟩))
      = false := by native_decide

end DeepWiki.SymbolicIntegration
