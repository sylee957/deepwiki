import DeepWiki.ComputableAlgebra.PolyReprDense
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! # The generic fraction field `CFrac α` (differential-tower carrier)
For a level `[CField α]`, `CFrac α` is the fraction field of `DensePoly α = α[t]` (denominator-nonzero
fraction pairs) with a computable `CField (CFrac α)` instance; `[CFieldSpec α]` adds a noncomputable
bridge into `RatFunc (CFieldSpec.K α)`. Iterating builds the tower `ℚ ⊂ ℚ(x) ⊂ ℚ(x)(t₁) ⊂ …`. The
carrier and its `CField` instance need only `[CField α]` (denominator-nonzero via `cisZero`, not the
`CFieldSpec`-valued `toPoly`), so the engine reduces in the native compiler at every tower level.

General computable-algebra layer: the fraction field of the computable polynomial ring, domain-neutral
(no symbolic-integration specifics). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-! ### The generic fraction pair `QFun α` and its computable arithmetic -/

/-- Generic fraction pair `(numerator, denominator)` over `α[t] = DensePoly α`. -/
abbrev QFun (α : Type*) [CField α] := DensePoly α × DensePoly α

namespace QFun

/-- Generic zero fraction `0/1` (numerator `[]`, denominator `[1]`). -/
def qzero {α : Type*} [CField α] : QFun α := ([], [CCommRing.one])

/-- Generic one fraction `1/1` (numerator `[1]`, denominator `[1]`). -/
def qone {α : Type*} [CField α] : QFun α := ([CCommRing.one], [CCommRing.one])

/-- Generic fraction addition `a/b + c/d = (a·d + c·b)/(b·d)` (cross-multiply, no gcd reduction). -/
def qadd {α : Type*} [CField α] (x y : QFun α) : QFun α :=
  let (a, b) := x
  let (c, d) := y
  (DensePoly.cadd (DensePoly.cmul a d) (DensePoly.cmul c b), DensePoly.cmul b d)

/-- Generic fraction multiplication `(a/b)·(c/d) = (a·c)/(b·d)`. -/
def qmul {α : Type*} [CField α] (x y : QFun α) : QFun α :=
  (DensePoly.cmul x.1 y.1, DensePoly.cmul x.2 y.2)

/-- Generic fraction negation `−(a/b) = (−a)/b` (denominator unchanged). -/
def qneg {α : Type*} [CField α] (x : QFun α) : QFun α := (DensePoly.cneg x.1, x.2)

/-- Generic fraction inverse `(a/b)⁻¹ = b/a`; `qzero` if the numerator is zero (`0⁻¹ = 0`). -/
def qinv {α : Type*} [CField α] (x : QFun α) : QFun α :=
  if DensePoly.cisZero x.1 then qzero else (x.2, x.1)

/-- Generic fraction subtraction `a/b − c/d := a/b + (−(c/d))`. -/
def qsub {α : Type*} [CField α] (x y : QFun α) : QFun α := qadd x (qneg y)

/-- Generic fraction division `x / y := x * y⁻¹`. -/
def qdiv {α : Type*} [CField α] (x y : QFun α) : QFun α := qmul x (qinv y)

/-- Generic natural power of a fraction pair. -/
def qpow {α : Type*} [CField α] (x : QFun α) : ℕ → QFun α
  | 0 => qone
  | n + 1 => qmul x (qpow x n)

/-- Generic formal derivative of a fraction pair by the quotient rule. -/
def qderiv {α : Type*} [CField α] (x : QFun α) : QFun α :=
  let (a, b) := x
  (DensePoly.csub (DensePoly.cmul (DensePoly.cderiv a) b)
    (DensePoly.cmul a (DensePoly.cderiv b)), DensePoly.cmul b b)

/-- Generic decidable equality test for fraction pairs by cross-multiplication. -/
def qeq {α : Type*} [CField α] (x y : QFun α) : Bool :=
  DensePoly.cisZero (DensePoly.csub (DensePoly.cmul x.1 y.2) (DensePoly.cmul y.1 x.2))

end QFun

/-! ### The denominator-nonzero subtype `CFrac α` (the tower-level carrier) -/

/-- Denominator-nonzero generic fractions: the subtype of `QFun α` with `cisZero den = false`. The
carrier of the next tower level (`CFrac ℚ ≅ ℚ(x)`, `CFrac (CFrac ℚ) ≅ ℚ(x)(t₁)`, …); needs only
`[CField α]`. -/
def CFrac (α : Type*) [CField α] : Type _ :=
  { x : QFun α // DensePoly.cisZero x.2 = false }

/-! #### The pure-`CField` domain class `CFieldDomain` -/

/-- Polynomial-domain facts in pure `CField`/`DensePoly` terms: `[1]` is `cisZero`-nonzero, and the product
of two `cisZero`-nonzero `DensePoly`s is `cisZero`-nonzero. Carries no `CFieldSpec` data, so it can gate
the computable `CField (CFrac α)` instance. -/
class CFieldDomain (α : Type*) [CField α] where
  /-- The constant `[1]` is `cisZero`-nonzero. -/
  nz_one : DensePoly.cisZero ([CCommRing.one] : DensePoly α) = false
  /-- The product of two `cisZero`-nonzero `DensePoly`s is `cisZero`-nonzero (no zero divisors). -/
  nz_mul : ∀ {b d : DensePoly α}, DensePoly.cisZero b = false → DensePoly.cisZero d = false →
    DensePoly.cisZero (DensePoly.cmul b d) = false

/-- Every `[CFieldSpec α]` level is a `CFieldDomain`, since `(CFieldSpec.K α)[X]` is an integral domain;
provides only `Prop` fields (erased at runtime). -/
noncomputable instance instCFieldDomainOfCFieldSpec {α : Type*} [CField α] [CFieldSpec α] :
    CFieldDomain α where
  nz_one := by
    rw [Bool.eq_false_iff, Ne, DensePoly.cisZeroG_iff]
    simp only [denote, mul_zero, add_zero, map_one]
    show (1 : (CFieldSpec.K α)[X]) ≠ 0
    exact one_ne_zero
  nz_mul := by
    intro b d hb hd
    rw [Bool.eq_false_iff] at hb hd ⊢
    rw [Ne, DensePoly.cisZeroG_iff] at hb hd ⊢
    simp only [denote]
    exact mul_ne_zero hb hd

namespace CFrac

/-- The constant `[1]` is `cisZero`-nonzero (from `CFieldDomain`). -/
theorem cisZeroG_one_singleton {α : Type*} [CField α] [CFieldDomain α] :
    DensePoly.cisZero ([CCommRing.one] : DensePoly α) = false :=
  CFieldDomain.nz_one

/-- The product of two `cisZero`-nonzero `DensePoly`s is `cisZero`-nonzero (from `CFieldDomain`). -/
theorem cmulG_ne_zero_of {α : Type*} [CField α] [CFieldDomain α] {b d : DensePoly α}
    (hb : DensePoly.cisZero b = false)
    (hd : DensePoly.cisZero d = false) : DensePoly.cisZero (DensePoly.cmul b d) = false :=
  CFieldDomain.nz_mul hb hd

/-- `qzeroNZ`: the zero fraction `0/1` as a `CFrac` (denominator `[1]` is nonzero). -/
def qzeroNZ {α : Type*} [CField α] [CFieldDomain α] : CFrac α :=
  ⟨QFun.qzero, cisZeroG_one_singleton⟩

/-- `qoneNZ`: the one fraction `1/1` as a `CFrac` (denominator `[1]` is nonzero). -/
def qoneNZ {α : Type*} [CField α] [CFieldDomain α] : CFrac α :=
  ⟨QFun.qone, cisZeroG_one_singleton⟩

/-- `qaddNZ`: addition on `CFrac` (the product denominator `b·d` is nonzero). -/
def qaddNZ {α : Type*} [CField α] [CFieldDomain α] (x y : CFrac α) : CFrac α :=
  ⟨QFun.qadd x.1 y.1, by
    obtain ⟨⟨a, b⟩, hb⟩ := x
    obtain ⟨⟨c, d⟩, hd⟩ := y
    exact cmulG_ne_zero_of hb hd⟩

/-- `qmulNZ`: multiplication on `CFrac` (the product denominator `b·d` is nonzero). -/
def qmulNZ {α : Type*} [CField α] [CFieldDomain α] (x y : CFrac α) : CFrac α :=
  ⟨QFun.qmul x.1 y.1, by
    obtain ⟨⟨a, b⟩, hb⟩ := x
    obtain ⟨⟨c, d⟩, hd⟩ := y
    exact cmulG_ne_zero_of hb hd⟩

/-- `qnegNZ`: negation on `CFrac` (denominator unchanged). -/
def qnegNZ {α : Type*} [CField α] (x : CFrac α) : CFrac α := ⟨QFun.qneg x.1, x.2⟩

/-- `qinvNZ`: inverse on `CFrac`. If the numerator's zero test holds, the result is `qzeroNZ` (the
`0⁻¹ = 0` convention); otherwise swap numerator and denominator (the new denominator is the old
numerator, nonzero exactly by `¬ cisZero`). -/
def qinvNZ {α : Type*} [CField α] [CFieldDomain α] (x : CFrac α) : CFrac α :=
  if h : DensePoly.cisZero x.1.1 then qzeroNZ
  else ⟨(x.1.2, x.1.1), Bool.not_eq_true _ ▸ h⟩

/-- `qsubNZ`: subtraction on `CFrac`, `x − y := x + (−y)`. -/
def qsubNZ {α : Type*} [CField α] [CFieldDomain α] (x y : CFrac α) : CFrac α :=
  qaddNZ x (qnegNZ y)

/-- `isZeroNZ`: the zero test on `CFrac`, reading `cisZero` off the **numerator** (the denominator
is nonzero by membership, so `x = 0` iff its numerator vanishes). -/
def isZeroNZ {α : Type*} [CField α] (x : CFrac α) : Bool := DensePoly.cisZero x.1.1

end CFrac

/-! ### The computable `CField (CFrac α)` instance -/

/-- `CField (CFrac α)`: the next tower level (fraction field of `α[t]`) as a computable field (over
`[CField α] [CFieldDomain α]`, no `CFieldSpec`), so the engine reduces over `DensePoly (CFrac α)`. -/
instance instCFieldCFrac {α : Type*} [CField α] [CFieldDomain α] : CField (CFrac α) where
  zero := CFrac.qzeroNZ
  one := CFrac.qoneNZ
  add := CFrac.qaddNZ
  mul := CFrac.qmulNZ
  neg := CFrac.qnegNZ
  inv := CFrac.qinvNZ
  isZero := CFrac.isZeroNZ

/-! ### The bridge `toCFrac` into `RatFunc (CFieldSpec.K α)` and its homomorphism laws -/

namespace CFrac

/-- `am = algebraMap (CFieldSpec.K α)[X] (RatFunc (CFieldSpec.K α))`, the polynomial-into-rational
embedding for the bridge. -/
noncomputable abbrev am (α : Type*) [CField α] [CFieldSpec α] :
    (CFieldSpec.K α)[X] →+* RatFunc (CFieldSpec.K α) :=
  algebraMap (CFieldSpec.K α)[X] (RatFunc (CFieldSpec.K α))

/-- `am (toPoly p) ≠ 0` whenever `toPoly p ≠ 0` (the embedding `algebraMap K[X] (RatFunc K)` is
injective). -/
theorem amG_toPolyG_ne_zero {α : Type*} [CField α] [CFieldSpec α] {p : DensePoly α}
    (hp : DensePoly.toPoly p ≠ 0) :
    am α (DensePoly.toPoly p) ≠ 0 :=
  (map_ne_zero_iff _ (RatFunc.algebraMap_injective (CFieldSpec.K α))).mpr hp

/-- `cisZero b = false` reads as `toPoly b ≠ 0` (the denominator nonzero criterion through the
bridge). -/
theorem toPolyG_ne_zero_of_cisZeroG_false {α : Type*} [CField α] [CFieldSpec α] {b : DensePoly α}
    (hb : DensePoly.cisZero b = false) :
    DensePoly.toPoly b ≠ 0 := by
  rw [Bool.eq_false_iff, Ne, DensePoly.cisZeroG_iff] at hb; exact hb

/-- `toCFrac (num, den) = am (toPoly num) / am (toPoly den)` in `RatFunc (CFieldSpec.K α)`; the
bridge `toK` of the next tower level. -/
noncomputable def toCFrac {α : Type*} [CField α] [CFieldSpec α] (x : CFrac α) :
    RatFunc (CFieldSpec.K α) :=
  am α (DensePoly.toPoly x.1.1) / am α (DensePoly.toPoly x.1.2)

/-- `toCFrac qzeroNZ = 0`. -/
theorem toCFracG_qzeroNZG {α : Type*} [CField α] [CFieldSpec α] [CFieldDomain α] :
    toCFrac (qzeroNZ : CFrac α) = 0 := by
  rw [toCFrac]
  show am α (DensePoly.toPoly ([] : DensePoly α)) / _ = 0
  rw [DensePoly.toPolyG_nil, map_zero, zero_div]

/-- `toCFrac qoneNZ = 1`. -/
theorem toCFracG_qoneNZG {α : Type*} [CField α] [CFieldSpec α] [CFieldDomain α] :
    toCFrac (qoneNZ : CFrac α) = 1 := by
  rw [toCFrac]
  show am α (DensePoly.toPoly ([CCommRing.one] : DensePoly α))
      / am α (DensePoly.toPoly ([CCommRing.one] : DensePoly α)) = 1
  have h1 : DensePoly.toPoly ([CCommRing.one] : DensePoly α) = 1 := by
    simp only [denote, mul_zero, add_zero, map_one]
  rw [h1, map_one, div_self one_ne_zero]

/-- `toCFrac (qaddNZ x y) = toCFrac x + toCFrac y`: `qaddNZ` realizes `+`. -/
theorem toCFracG_qaddNZG {α : Type*} [CField α] [CFieldSpec α] [CFieldDomain α] (x y : CFrac α) :
    toCFrac (qaddNZ x y) = toCFrac x + toCFrac y := by
  obtain ⟨⟨a, b⟩, hb⟩ := x
  obtain ⟨⟨c, d⟩, hd⟩ := y
  have hb' : am α (DensePoly.toPoly b) ≠ 0 :=
    amG_toPolyG_ne_zero (toPolyG_ne_zero_of_cisZeroG_false hb)
  have hd' : am α (DensePoly.toPoly d) ≠ 0 :=
    amG_toPolyG_ne_zero (toPolyG_ne_zero_of_cisZeroG_false hd)
  show am α (DensePoly.toPoly (DensePoly.cadd (DensePoly.cmul a d) (DensePoly.cmul c b)))
      / am α (DensePoly.toPoly (DensePoly.cmul b d))
    = am α (DensePoly.toPoly a) / am α (DensePoly.toPoly b)
      + am α (DensePoly.toPoly c) / am α (DensePoly.toPoly d)
  simp only [denote, map_add, map_mul]
  rw [div_add_div _ _ hb' hd']
  ring

/-- `toCFrac (qmulNZ x y) = toCFrac x * toCFrac y`: `qmulNZ` realizes `*`. -/
theorem toCFracG_qmulNZG {α : Type*} [CField α] [CFieldSpec α] [CFieldDomain α] (x y : CFrac α) :
    toCFrac (qmulNZ x y) = toCFrac x * toCFrac y := by
  obtain ⟨⟨a, b⟩, hb⟩ := x
  obtain ⟨⟨c, d⟩, hd⟩ := y
  show am α (DensePoly.toPoly (DensePoly.cmul a c)) / am α (DensePoly.toPoly (DensePoly.cmul b d))
    = am α (DensePoly.toPoly a) / am α (DensePoly.toPoly b)
      * (am α (DensePoly.toPoly c) / am α (DensePoly.toPoly d))
  simp only [denote, map_mul]
  rw [div_mul_div_comm]

/-- `toCFrac (qnegNZ x) = - toCFrac x`: `qnegNZ` realizes negation. -/
theorem toCFracG_qnegNZG {α : Type*} [CField α] [CFieldSpec α] (x : CFrac α) :
    toCFrac (qnegNZ x) = - toCFrac x := by
  obtain ⟨⟨a, b⟩, hb⟩ := x
  show am α (DensePoly.toPoly (DensePoly.cneg a)) / am α (DensePoly.toPoly b)
    = - (am α (DensePoly.toPoly a) / am α (DensePoly.toPoly b))
  simp only [denote, map_neg]
  rw [neg_div]

/-- `toCFrac (qinvNZ x) = (toCFrac x)⁻¹`: `qinvNZ` realizes `⁻¹` (`0⁻¹ = 0`). -/
theorem toCFracG_qinvNZG {α : Type*} [CField α] [CFieldSpec α] [CFieldDomain α] (x : CFrac α) :
    toCFrac (qinvNZ x) = (toCFrac x)⁻¹ := by
  rw [qinvNZ]
  by_cases h : DensePoly.cisZero x.1.1
  · rw [dif_pos h, toCFracG_qzeroNZG]
    have hx0 : DensePoly.toPoly x.1.1 = 0 := (DensePoly.cisZeroG_iff x.1.1).mp h
    have : toCFrac x = 0 := by
      rw [toCFrac, hx0, map_zero, zero_div]
    rw [this, inv_zero]
  · rw [dif_neg h]
    show am α (DensePoly.toPoly x.1.2) / am α (DensePoly.toPoly x.1.1)
      = (am α (DensePoly.toPoly x.1.1) / am α (DensePoly.toPoly x.1.2))⁻¹
    rw [inv_div]

/-- `toCFrac (qsubNZ x y) = toCFrac x - toCFrac y`: `qsubNZ` realizes subtraction. -/
theorem toCFracG_qsubNZG {α : Type*} [CField α] [CFieldSpec α] [CFieldDomain α] (x y : CFrac α) :
    toCFrac (qsubNZ x y) = toCFrac x - toCFrac y := by
  rw [qsubNZ, toCFracG_qaddNZG, toCFracG_qnegNZG, sub_eq_add_neg]

/-- `isZeroNZ x = true ↔ toCFrac x = 0`: the numerator zero test agrees with vanishing in
`RatFunc (CFieldSpec.K α)`. -/
theorem isZeroNZG_iff {α : Type*} [CField α] [CFieldSpec α] (x : CFrac α) :
    isZeroNZ x = true ↔ toCFrac x = 0 := by
  rw [isZeroNZ, DensePoly.cisZeroG_iff]
  obtain ⟨⟨a, b⟩, hb⟩ := x
  have hbm : am α (DensePoly.toPoly b) ≠ 0 :=
    amG_toPolyG_ne_zero (toPolyG_ne_zero_of_cisZeroG_false hb)
  show DensePoly.toPoly a = 0 ↔ am α (DensePoly.toPoly a) / am α (DensePoly.toPoly b) = 0
  constructor
  · intro h; rw [h, map_zero, zero_div]
  · intro h
    rw [div_eq_zero_iff] at h
    rcases h with h | h
    · exact (map_eq_zero_iff _ (RatFunc.algebraMap_injective (CFieldSpec.K α))).mp h
    · exact absurd h hbm

end CFrac

/-- `CFieldSpec (CFrac α)`: the field-homomorphism bridge over `K = RatFunc (CFieldSpec.K α)` with
`toK = toCFrac`. Noncomputable; only the correctness layer depends on it. -/
noncomputable instance instCFieldSpecCFrac {α : Type*} [CField α] [CFieldSpec α] :
    CFieldSpec (CFrac α) where
  K := RatFunc (CFieldSpec.K α)
  toK := CFrac.toCFrac
  toK_zero := CFrac.toCFracG_qzeroNZG
  toK_one := CFrac.toCFracG_qoneNZG
  toK_add := CFrac.toCFracG_qaddNZG
  toK_mul := CFrac.toCFracG_qmulNZG
  toK_neg := CFrac.toCFracG_qnegNZG
  toK_inv := CFrac.toCFracG_qinvNZG
  isZero_iff := CFrac.isZeroNZG_iff

end DeepWiki.SymbolicIntegration
