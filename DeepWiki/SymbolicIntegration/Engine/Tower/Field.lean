import DeepWiki.ComputableAlgebra.GenericPolyEngine
import DeepWiki.SymbolicIntegration.Engine.ConcreteCoherence
import DeepWiki.ComputableAlgebra.GenericBezout
import DeepWiki.SymbolicIntegration.Engine.FuelFreeResultant

/-! # The generic fraction field `QFunNZG α` (differential-tower carrier)
For a level `[CField α]`, `QFunNZG α` is the fraction field of `CPolyG α = α[t]` (denominator-nonzero
fraction pairs) with a computable `CField (QFunNZG α)` instance; `[CFieldSpec α]` adds a noncomputable
bridge into `RatFunc (CFieldSpec.K α)`. Iterating builds the tower `ℚ ⊂ ℚ(x) ⊂ ℚ(x)(t₁) ⊂ …`. The
carrier and its `CField` instance need only `[CField α]` (denominator-nonzero via `cisZeroG`, not the
`CFieldSpec`-valued `toPolyG`), so the engine reduces in the native compiler at every tower level. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-! ### The generic fraction pair `QFunG α` and its computable arithmetic -/

/-- Generic fraction pair `(numerator, denominator)` over `α[t] = CPolyG α`. -/
abbrev QFunG (α : Type*) [CField α] := CPolyG α × CPolyG α

namespace QFunG

/-- Generic zero fraction `0/1` (numerator `[]`, denominator `[1]`). -/
def qzeroG {α : Type*} [CField α] : QFunG α := ([], [CField.one])

/-- Generic one fraction `1/1` (numerator `[1]`, denominator `[1]`). -/
def qoneG {α : Type*} [CField α] : QFunG α := ([CField.one], [CField.one])

/-- Generic fraction addition `a/b + c/d = (a·d + c·b)/(b·d)` (cross-multiply, no gcd reduction). -/
def qaddG {α : Type*} [CField α] (x y : QFunG α) : QFunG α :=
  let (a, b) := x
  let (c, d) := y
  (CPolyG.caddG (CPolyG.cmulG a d) (CPolyG.cmulG c b), CPolyG.cmulG b d)

/-- Generic fraction multiplication `(a/b)·(c/d) = (a·c)/(b·d)`. -/
def qmulG {α : Type*} [CField α] (x y : QFunG α) : QFunG α :=
  (CPolyG.cmulG x.1 y.1, CPolyG.cmulG x.2 y.2)

/-- Generic fraction negation `−(a/b) = (−a)/b` (denominator unchanged). -/
def qnegG {α : Type*} [CField α] (x : QFunG α) : QFunG α := (CPolyG.cnegG x.1, x.2)

/-- Generic fraction inverse `(a/b)⁻¹ = b/a`; `qzeroG` if the numerator is zero (`0⁻¹ = 0`). -/
def qinvG {α : Type*} [CField α] (x : QFunG α) : QFunG α :=
  if CPolyG.cisZeroG x.1 then qzeroG else (x.2, x.1)

/-- Generic fraction subtraction `a/b − c/d := a/b + (−(c/d))`. -/
def qsubG {α : Type*} [CField α] (x y : QFunG α) : QFunG α := qaddG x (qnegG y)

end QFunG

/-! ### The denominator-nonzero subtype `QFunNZG α` (the tower-level carrier) -/

/-- Denominator-nonzero generic fractions: the subtype of `QFunG α` with `cisZeroG den = false`. The
carrier of the next tower level (`QFunNZG ℚ ≅ ℚ(x)`, `QFunNZG (QFunNZG ℚ) ≅ ℚ(x)(t₁)`, …); needs only
`[CField α]`. -/
def QFunNZG (α : Type*) [CField α] : Type _ :=
  { x : QFunG α // CPolyG.cisZeroG x.2 = false }

/-! #### The pure-`CField` domain class `CFieldDomain` -/

/-- Polynomial-domain facts in pure `CField`/`CPolyG` terms: `[1]` is `cisZeroG`-nonzero, and the product
of two `cisZeroG`-nonzero `CPolyG`s is `cisZeroG`-nonzero. Carries no `CFieldSpec` data, so it can gate
the computable `CField (QFunNZG α)` instance. -/
class CFieldDomain (α : Type*) [CField α] where
  /-- The constant `[1]` is `cisZeroG`-nonzero. -/
  nz_one : CPolyG.cisZeroG ([CField.one] : CPolyG α) = false
  /-- The product of two `cisZeroG`-nonzero `CPolyG`s is `cisZeroG`-nonzero (no zero divisors). -/
  nz_mul : ∀ {b d : CPolyG α}, CPolyG.cisZeroG b = false → CPolyG.cisZeroG d = false →
    CPolyG.cisZeroG (CPolyG.cmulG b d) = false

/-- Every `[CFieldSpec α]` level is a `CFieldDomain`, since `(CFieldSpec.K α)[X]` is an integral domain;
provides only `Prop` fields (erased at runtime). -/
noncomputable instance instCFieldDomainOfCFieldSpec {α : Type*} [CField α] [CFieldSpec α] :
    CFieldDomain α where
  nz_one := by
    rw [Bool.eq_false_iff, Ne, CPolyG.cisZeroG_iff]
    simp only [denote, mul_zero, add_zero, map_one]
    show (1 : (CFieldSpec.K α)[X]) ≠ 0
    exact one_ne_zero
  nz_mul := by
    intro b d hb hd
    rw [Bool.eq_false_iff] at hb hd ⊢
    rw [Ne, CPolyG.cisZeroG_iff] at hb hd ⊢
    simp only [denote]
    exact mul_ne_zero hb hd

namespace QFunNZG

/-- The constant `[1]` is `cisZeroG`-nonzero (from `CFieldDomain`). -/
theorem cisZeroG_one_singleton {α : Type*} [CField α] [CFieldDomain α] :
    CPolyG.cisZeroG ([CField.one] : CPolyG α) = false :=
  CFieldDomain.nz_one

/-- The product of two `cisZeroG`-nonzero `CPolyG`s is `cisZeroG`-nonzero (from `CFieldDomain`). -/
theorem cmulG_ne_zero_of {α : Type*} [CField α] [CFieldDomain α] {b d : CPolyG α}
    (hb : CPolyG.cisZeroG b = false)
    (hd : CPolyG.cisZeroG d = false) : CPolyG.cisZeroG (CPolyG.cmulG b d) = false :=
  CFieldDomain.nz_mul hb hd

/-- `qzeroNZG`: the zero fraction `0/1` as a `QFunNZG` (denominator `[1]` is nonzero). -/
def qzeroNZG {α : Type*} [CField α] [CFieldDomain α] : QFunNZG α :=
  ⟨QFunG.qzeroG, cisZeroG_one_singleton⟩

/-- `qoneNZG`: the one fraction `1/1` as a `QFunNZG` (denominator `[1]` is nonzero). -/
def qoneNZG {α : Type*} [CField α] [CFieldDomain α] : QFunNZG α :=
  ⟨QFunG.qoneG, cisZeroG_one_singleton⟩

/-- `qaddNZG`: addition on `QFunNZG` (the product denominator `b·d` is nonzero). -/
def qaddNZG {α : Type*} [CField α] [CFieldDomain α] (x y : QFunNZG α) : QFunNZG α :=
  ⟨QFunG.qaddG x.1 y.1, by
    obtain ⟨⟨a, b⟩, hb⟩ := x
    obtain ⟨⟨c, d⟩, hd⟩ := y
    exact cmulG_ne_zero_of hb hd⟩

/-- `qmulNZG`: multiplication on `QFunNZG` (the product denominator `b·d` is nonzero). -/
def qmulNZG {α : Type*} [CField α] [CFieldDomain α] (x y : QFunNZG α) : QFunNZG α :=
  ⟨QFunG.qmulG x.1 y.1, by
    obtain ⟨⟨a, b⟩, hb⟩ := x
    obtain ⟨⟨c, d⟩, hd⟩ := y
    exact cmulG_ne_zero_of hb hd⟩

/-- `qnegNZG`: negation on `QFunNZG` (denominator unchanged). -/
def qnegNZG {α : Type*} [CField α] (x : QFunNZG α) : QFunNZG α := ⟨QFunG.qnegG x.1, x.2⟩

/-- `qinvNZG`: inverse on `QFunNZG`. If the numerator's zero test holds, the result is `qzeroNZG` (the
`0⁻¹ = 0` convention); otherwise swap numerator and denominator (the new denominator is the old
numerator, nonzero exactly by `¬ cisZeroG`). -/
def qinvNZG {α : Type*} [CField α] [CFieldDomain α] (x : QFunNZG α) : QFunNZG α :=
  if h : CPolyG.cisZeroG x.1.1 then qzeroNZG
  else ⟨(x.1.2, x.1.1), Bool.not_eq_true _ ▸ h⟩

/-- `qsubNZG`: subtraction on `QFunNZG`, `x − y := x + (−y)`. -/
def qsubNZG {α : Type*} [CField α] [CFieldDomain α] (x y : QFunNZG α) : QFunNZG α :=
  qaddNZG x (qnegNZG y)

/-- `isZeroNZG`: the zero test on `QFunNZG`, reading `cisZeroG` off the **numerator** (the denominator
is nonzero by membership, so `x = 0` iff its numerator vanishes). -/
def isZeroNZG {α : Type*} [CField α] (x : QFunNZG α) : Bool := CPolyG.cisZeroG x.1.1

end QFunNZG

/-! ### The computable `CField (QFunNZG α)` instance -/

/-- `CField (QFunNZG α)`: the next tower level (fraction field of `α[t]`) as a computable field (over
`[CField α] [CFieldDomain α]`, no `CFieldSpec`), so the engine reduces over `CPolyG (QFunNZG α)`. -/
instance instCFieldQFunNZG {α : Type*} [CField α] [CFieldDomain α] : CField (QFunNZG α) where
  zero := QFunNZG.qzeroNZG
  one := QFunNZG.qoneNZG
  add := QFunNZG.qaddNZG
  mul := QFunNZG.qmulNZG
  neg := QFunNZG.qnegNZG
  inv := QFunNZG.qinvNZG
  isZero := QFunNZG.isZeroNZG

/-! ### The bridge `toQFunNZG` into `RatFunc (CFieldSpec.K α)` and its homomorphism laws -/

namespace QFunNZG

/-- `amG = algebraMap (CFieldSpec.K α)[X] (RatFunc (CFieldSpec.K α))`, the polynomial-into-rational
embedding for the bridge. -/
noncomputable abbrev amG (α : Type*) [CField α] [CFieldSpec α] :
    (CFieldSpec.K α)[X] →+* RatFunc (CFieldSpec.K α) :=
  algebraMap (CFieldSpec.K α)[X] (RatFunc (CFieldSpec.K α))

/-- `amG (toPolyG p) ≠ 0` whenever `toPolyG p ≠ 0` (the embedding `algebraMap K[X] (RatFunc K)` is
injective). -/
theorem amG_toPolyG_ne_zero {α : Type*} [CField α] [CFieldSpec α] {p : CPolyG α}
    (hp : CPolyG.toPolyG p ≠ 0) :
    amG α (CPolyG.toPolyG p) ≠ 0 :=
  (map_ne_zero_iff _ (RatFunc.algebraMap_injective (CFieldSpec.K α))).mpr hp

/-- `cisZeroG b = false` reads as `toPolyG b ≠ 0` (the denominator nonzero criterion through the
bridge). -/
theorem toPolyG_ne_zero_of_cisZeroG_false {α : Type*} [CField α] [CFieldSpec α] {b : CPolyG α}
    (hb : CPolyG.cisZeroG b = false) :
    CPolyG.toPolyG b ≠ 0 := by
  rw [Bool.eq_false_iff, Ne, CPolyG.cisZeroG_iff] at hb; exact hb

/-- `toQFunNZG (num, den) = amG (toPolyG num) / amG (toPolyG den)` in `RatFunc (CFieldSpec.K α)`; the
bridge `toK` of the next tower level. -/
noncomputable def toQFunNZG {α : Type*} [CField α] [CFieldSpec α] (x : QFunNZG α) :
    RatFunc (CFieldSpec.K α) :=
  amG α (CPolyG.toPolyG x.1.1) / amG α (CPolyG.toPolyG x.1.2)

/-- `toQFunNZG qzeroNZG = 0`. -/
theorem toQFunNZG_qzeroNZG {α : Type*} [CField α] [CFieldSpec α] [CFieldDomain α] :
    toQFunNZG (qzeroNZG : QFunNZG α) = 0 := by
  rw [toQFunNZG]
  show amG α (CPolyG.toPolyG ([] : CPolyG α)) / _ = 0
  rw [CPolyG.toPolyG_nil, map_zero, zero_div]

/-- `toQFunNZG qoneNZG = 1`. -/
theorem toQFunNZG_qoneNZG {α : Type*} [CField α] [CFieldSpec α] [CFieldDomain α] :
    toQFunNZG (qoneNZG : QFunNZG α) = 1 := by
  rw [toQFunNZG]
  show amG α (CPolyG.toPolyG ([CField.one] : CPolyG α))
      / amG α (CPolyG.toPolyG ([CField.one] : CPolyG α)) = 1
  have h1 : CPolyG.toPolyG ([CField.one] : CPolyG α) = 1 := by
    simp only [denote, mul_zero, add_zero, map_one]
  rw [h1, map_one, div_self one_ne_zero]

/-- `toQFunNZG (qaddNZG x y) = toQFunNZG x + toQFunNZG y`: `qaddNZG` realizes `+`. -/
theorem toQFunNZG_qaddNZG {α : Type*} [CField α] [CFieldSpec α] [CFieldDomain α] (x y : QFunNZG α) :
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
  simp only [denote, map_add, map_mul]
  rw [div_add_div _ _ hb' hd']
  ring

/-- `toQFunNZG (qmulNZG x y) = toQFunNZG x * toQFunNZG y`: `qmulNZG` realizes `*`. -/
theorem toQFunNZG_qmulNZG {α : Type*} [CField α] [CFieldSpec α] [CFieldDomain α] (x y : QFunNZG α) :
    toQFunNZG (qmulNZG x y) = toQFunNZG x * toQFunNZG y := by
  obtain ⟨⟨a, b⟩, hb⟩ := x
  obtain ⟨⟨c, d⟩, hd⟩ := y
  show amG α (CPolyG.toPolyG (CPolyG.cmulG a c)) / amG α (CPolyG.toPolyG (CPolyG.cmulG b d))
    = amG α (CPolyG.toPolyG a) / amG α (CPolyG.toPolyG b)
      * (amG α (CPolyG.toPolyG c) / amG α (CPolyG.toPolyG d))
  simp only [denote, map_mul]
  rw [div_mul_div_comm]

/-- `toQFunNZG (qnegNZG x) = - toQFunNZG x`: `qnegNZG` realizes negation. -/
theorem toQFunNZG_qnegNZG {α : Type*} [CField α] [CFieldSpec α] (x : QFunNZG α) :
    toQFunNZG (qnegNZG x) = - toQFunNZG x := by
  obtain ⟨⟨a, b⟩, hb⟩ := x
  show amG α (CPolyG.toPolyG (CPolyG.cnegG a)) / amG α (CPolyG.toPolyG b)
    = - (amG α (CPolyG.toPolyG a) / amG α (CPolyG.toPolyG b))
  simp only [denote, map_neg]
  rw [neg_div]

/-- `toQFunNZG (qinvNZG x) = (toQFunNZG x)⁻¹`: `qinvNZG` realizes `⁻¹` (`0⁻¹ = 0`). -/
theorem toQFunNZG_qinvNZG {α : Type*} [CField α] [CFieldSpec α] [CFieldDomain α] (x : QFunNZG α) :
    toQFunNZG (qinvNZG x) = (toQFunNZG x)⁻¹ := by
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

/-- `toQFunNZG (qsubNZG x y) = toQFunNZG x - toQFunNZG y`: `qsubNZG` realizes subtraction. -/
theorem toQFunNZG_qsubNZG {α : Type*} [CField α] [CFieldSpec α] [CFieldDomain α] (x y : QFunNZG α) :
    toQFunNZG (qsubNZG x y) = toQFunNZG x - toQFunNZG y := by
  rw [qsubNZG, toQFunNZG_qaddNZG, toQFunNZG_qnegNZG, sub_eq_add_neg]

/-- `isZeroNZG x = true ↔ toQFunNZG x = 0`: the numerator zero test agrees with vanishing in
`RatFunc (CFieldSpec.K α)`. -/
theorem isZeroNZG_iff {α : Type*} [CField α] [CFieldSpec α] (x : QFunNZG α) :
    isZeroNZG x = true ↔ toQFunNZG x = 0 := by
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

/-- `CFieldSpec (QFunNZG α)`: the field-homomorphism bridge over `K = RatFunc (CFieldSpec.K α)` with
`toK = toQFunNZG`. Noncomputable; only the correctness layer depends on it. -/
noncomputable instance instCFieldSpecQFunNZG {α : Type*} [CField α] [CFieldSpec α] :
    CFieldSpec (QFunNZG α) where
  K := RatFunc (CFieldSpec.K α)
  toK := QFunNZG.toQFunNZG
  toK_zero := QFunNZG.toQFunNZG_qzeroNZG
  toK_one := QFunNZG.toQFunNZG_qoneNZG
  toK_add := QFunNZG.toQFunNZG_qaddNZG
  toK_mul := QFunNZG.toQFunNZG_qmulNZG
  toK_neg := QFunNZG.toQFunNZG_qnegNZG
  toK_inv := QFunNZG.toQFunNZG_qinvNZG
  isZero_iff := QFunNZG.isZeroNZG_iff

/-! ### Tower level 1: `QFunNZG ℚ ≅ ℚ(x)` and its coherence with the concrete `Compute.*` engine -/

/-- The underlying pair type of `QFunG ℚ` is the concrete `Compute.QFun` (both `List ℚ × List ℚ`). -/
example : QFunG ℚ = Compute.QFun := rfl

/-- Generic-to-concrete coherence at `α = ℚ`: `toPolyG (α := ℚ) = toPoly` pointwise. -/
example (d : CPolyG ℚ) : CPolyG.toPolyG d = Compute.toPoly d :=
  congrFun CPolyG.toPolyG_eq_toPoly d

/-! ### The tower computes at level 2 (`ℚ(x)(t₁)[t₂]`) (`native_decide`) -/

/-- Tower level 2: `Lvl2 = QFunNZG (QFunNZG ℚ)`, the field ℚ(x)(t₁); `CPolyG Lvl2 = ℚ(x)(t₁)[t₂]`. -/
abbrev Lvl2 : Type := QFunNZG (QFunNZG ℚ)

/-- `1 + 1 ≠ 0` in `Lvl2 = ℚ(x)(t₁)`: the level-2 scalar `add`/`isZero` reduce. -/
example : CField.isZero (CField.add (CField.one : Lvl2) CField.one) = false := by native_decide

/-- `0 = 0` at level 2: the level-2 scalar zero test reduces. -/
example : CField.isZero (CField.zero : Lvl2) = true := by native_decide

/-- `1 ≠ 0` at level 2. -/
example : CField.isZero (CField.one : Lvl2) = false := by native_decide

/-- `(1 + t₂)·(1 + t₂)` over `CPolyG Lvl2` is a length-3 normalized list: `cmulG` reduces at level 2. -/
example :
    (CPolyG.cnormG (CPolyG.cmulG [(CField.one : Lvl2), CField.one] [CField.one, CField.one])
      : List Lvl2).length = 3 := by native_decide

/-- The product is nonzero over `CPolyG Lvl2`: `cisZeroG` reduces at level 2. -/
example :
    CPolyG.cisZeroG (CPolyG.cmulG [(CField.one : Lvl2), CField.one] [CField.one, CField.one])
      = false := by native_decide

/-- `gcd(t₂, t₂) = t₂` is nonzero over `CPolyG Lvl2`: `cgcdWf` reduces end to end at level 2. -/
example :
    CPolyG.cisZeroG (CPolyG.cgcdWf [(CField.zero : Lvl2), CField.one]
      [(CField.zero : Lvl2), CField.one]).1 = false := by native_decide

/-- `res(t₂, 1 + t₂) = 1` over `CPolyG Lvl2`: `cresultantWf` reduces end to end at level 2. -/
example :
    CField.isZero
      (CPolyG.cresultantWf [(CField.zero : Lvl2), CField.one] [CField.one, CField.one]) = false := by
  native_decide

/-- `1 + (t₁)⁻¹ ≠ 0` at level 2: the `add`/`isZero` engine reduces on a non-trivial `Lvl2` fraction. -/
example :
    CField.isZero
      (CField.add (CField.one : Lvl2)
        (CField.inv ⟨([(CField.zero : QFunNZG ℚ), CField.one], [CField.one]),
          QFunNZG.cisZeroG_one_singleton⟩))
      = false := by native_decide

end DeepWiki.SymbolicIntegration
