import DeepWiki.SymbolicIntegration.GenericPolyEngine
import DeepWiki.SymbolicIntegration.LogToAtanCompute
import DeepWiki.SymbolicIntegration.ComputeCorrectness
import DeepWiki.SymbolicIntegration.RationalFunctionCompute

/-! # Coherence of the generic polynomial engine with the concrete `CPoly := List ℚ` engine
The standalone generic engine (`CField`/`CFieldSpec`, `CPolyG`, the generic ops `caddG`/…, `toPolyG`,
the generic correctness, `CField ℚ`/`CFieldSpec ℚ`) lives upstream in `GenericPolyEngine`. This file
ties it to the concrete `Compute.*` engine (`LogToAtanCompute`, `ComputeCorrectness`) and the computable
ℚ(x) field `QFun` (`RationalFunctionCompute`): the **coherence lemmas** (`caddG (α := ℚ) = cadd`,
`toPolyG (α := ℚ) = toPoly`) show the generic engine specializes back to the concrete one, and the
denominator-nonzero subtype `QFunNZ` is the carrier on which a second `CField` instance lives. The
coherence equalities are what let a later stage migrate `CPoly := CPolyG ℚ` without breaking consumers. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace CPolyG

variable {α : Type*} [CField α]

/-! ### Coherence with the concrete `CPoly` engine at `α = ℚ`

The generic engine specialized at `ℚ` (via `CField ℚ`) agrees with the concrete `Compute.*` engine
of `LogToAtanCompute`/`ComputeCorrectness`. These equalities are what lets a later stage migrate
`CPoly := CPolyG ℚ` without breaking the existing consumers. `caddG`/`cnegG`/`cscaleG`/`cshiftG`/
`cmulG` agree **definitionally** (the `CField ℚ` operations unfold to the `ℚ` operations `cadd`/… use);
`cnormG`/`cisZeroG`/`toPolyG` agree up to a short proof (the `isZero`/`toK = id` indirection). -/

/-- `caddG` at `ℚ` is the concrete `cadd` (both add coefficientwise with `ℚ`'s `+`). -/
theorem caddG_eq_cadd : (caddG : CPolyG ℚ → CPolyG ℚ → CPolyG ℚ) = Compute.cadd := by
  funext p q
  induction p generalizing q with
  | nil => rfl
  | cons a as ih => cases q with
    | nil => rfl
    | cons b bs => show CField.add a b :: caddG as bs = _; rw [ih]; rfl

/-- `cnegG` at `ℚ` is the concrete `cneg`. -/
theorem cnegG_eq_cneg : (cnegG : CPolyG ℚ → CPolyG ℚ) = Compute.cneg := rfl

/-- `cscaleG` at `ℚ` is the concrete `cscale`. -/
theorem cscaleG_eq_cscale (c : ℚ) : (cscaleG c : CPolyG ℚ → CPolyG ℚ) = Compute.cscale c := rfl

/-- `cshiftG` at `ℚ` is the concrete `cshift`. -/
theorem cshiftG_eq_cshift (k : ℕ) : (cshiftG k : CPolyG ℚ → CPolyG ℚ) = Compute.cshift k := by
  funext p
  induction k generalizing p with
  | zero => rfl
  | succ n ih => show CField.zero :: cshiftG n p = _; rw [ih]; rfl

/-- `cmulG` at `ℚ` is the concrete `cmul`. -/
theorem cmulG_eq_cmul : (cmulG : CPolyG ℚ → CPolyG ℚ → CPolyG ℚ) = Compute.cmul := by
  funext p q
  induction p generalizing q with
  | nil => rfl
  | cons a as ih =>
    show caddG (cscaleG a q) (CField.zero :: cmulG as q) = Compute.cmul (a :: as) q
    rw [cscaleG_eq_cscale, ih, congrFun (congrFun caddG_eq_cadd _) _]; rfl

/-- `cnormG` at `ℚ` is the concrete `cnorm`. -/
theorem cnormG_eq_cnorm : (cnormG : CPolyG ℚ → CPolyG ℚ) = Compute.cnorm := by
  funext p
  induction p with
  | nil => rfl
  | cons a as ih =>
    rw [cnormG_cons_eq, Compute.cnorm_cons_eq, ih]
    cases Compute.cnorm as with
    | nil =>
      show (if (decide (a = 0) = true) then ([] : CPolyG ℚ) else [a]) = (if a = 0 then [] else [a])
      by_cases ha : a = 0 <;> simp [ha]
    | cons b bs => rfl

/-- `cisZeroG` at `ℚ` is the concrete `cisZero`. -/
theorem cisZeroG_eq_cisZero : (cisZeroG : CPolyG ℚ → Bool) = Compute.cisZero := by
  funext p
  rw [cisZeroG, cnormG_eq_cnorm, Compute.cisZero]
  cases h : Compute.cnorm p <;> simp

/-- `toPolyG` at `ℚ` is the concrete `toPoly` (`toK = id`, `CFieldSpec.K ℚ = ℚ`). -/
theorem toPolyG_eq_toPoly : (toPolyG : CPolyG ℚ → ℚ[X]) = Compute.toPoly := by
  funext p
  induction p with
  | nil => rfl
  | cons a as ih => show Polynomial.C (CFieldSpec.toK a) + X * toPolyG as = _; rw [ih]; rfl

end CPolyG

/-! ### The ℚ(x) layer: `CField QFun` and the injectivity obstruction

The second target instance is `CField QFun` over `K = RatFunc ℚ` with `toK = toQFun`. The
field-homomorphism *laws* are exactly the `toQFun_*` lemmas of `RationalFunctionCompute`; the
unconditional ones (`qone`/`qneg`/`qmul`/`qinv`/`qdiv`) hold on all of `QFun`, while
`qadd`/`qsub`/`qeq` carry a denominator-nonzero side-condition. Restricting to the **denominator-
nonzero subtype** `QFunNZ` clears those side-conditions: `qadd`/`qsub` of two den-nonzero pairs again
has nonzero denominator, so the laws become unconditional there.

`toQFun` is *not* injective on unreduced pairs (`(1,[1,1])` and `(2,[2,2])` — i.e. `1/(x+1)` and
`2/(2x+2)` — are distinct pairs with equal image, as are `qzero = (0,1)` and `(0,7)`). This is HARMLESS:
`CField` does not require `toK` injective — the engine works on representations and tests `K`-equality
through `isZero`, so `CField QFunNZ` lands with `isZero := cisZero ∘ num` (certified by the
numerator-zero criterion) without any lowest-terms-uniqueness theorem. The homomorphism laws below are
the proven core that instance is built from. -/

/-- **Denominator-nonzero rational functions**: the subtype of `QFun` whose denominator is a nonzero
polynomial. On it the `toQFun_*` homomorphism laws hold *unconditionally* (the den-≠-0 side-conditions
are discharged by membership). The carrier on which a faithful `CField` instance would live, modulo the
lowest-terms-uniqueness needed for injectivity. -/
def QFunNZ : Type := { x : Compute.QFun // Compute.toPoly x.2 ≠ 0 }

namespace QFunNZ

/-- `toQFunNZ` reads a `QFunNZ` into `RatFunc ℚ` (the underlying `toQFun`). -/
noncomputable def toQFunNZ (x : QFunNZ) : RatFunc ℚ := Compute.toQFun x.1

/-- `qaddNZ`: addition on `QFunNZ` (the product denominator is nonzero). -/
def qaddNZ (x y : QFunNZ) : QFunNZ :=
  ⟨Compute.qadd x.1 y.1, by
    obtain ⟨⟨a, b⟩, hb⟩ := x
    obtain ⟨⟨c, d⟩, hd⟩ := y
    show Compute.toPoly (Compute.cmul b d) ≠ 0
    rw [Compute.toPoly_cmul]; exact mul_ne_zero hb hd⟩

/-- `qmulNZ`: multiplication on `QFunNZ` (the product denominator is nonzero). -/
def qmulNZ (x y : QFunNZ) : QFunNZ :=
  ⟨Compute.qmul x.1 y.1, by
    obtain ⟨⟨a, b⟩, hb⟩ := x
    obtain ⟨⟨c, d⟩, hd⟩ := y
    show Compute.toPoly (Compute.cmul b d) ≠ 0
    rw [Compute.toPoly_cmul]; exact mul_ne_zero hb hd⟩

/-- `qnegNZ`: negation on `QFunNZ` (denominator unchanged). -/
def qnegNZ (x : QFunNZ) : QFunNZ := ⟨Compute.qneg x.1, x.2⟩

/-- **`qaddNZ` realizes `+`** on `QFunNZ` *unconditionally*: `toQFunNZ (qaddNZ x y) = toQFunNZ x +
toQFunNZ y` (the `toQFun_qadd` side-conditions are discharged by membership). -/
theorem toQFunNZ_qaddNZ (x y : QFunNZ) :
    toQFunNZ (qaddNZ x y) = toQFunNZ x + toQFunNZ y :=
  Compute.toQFun_qadd x.1 y.1 x.2 y.2

/-- **`qmulNZ` realizes `*`** on `QFunNZ`: `toQFunNZ (qmulNZ x y) = toQFunNZ x * toQFunNZ y`. -/
theorem toQFunNZ_qmulNZ (x y : QFunNZ) :
    toQFunNZ (qmulNZ x y) = toQFunNZ x * toQFunNZ y :=
  Compute.toQFun_qmul x.1 y.1

/-- **`qnegNZ` realizes `-`** on `QFunNZ`: `toQFunNZ (qnegNZ x) = - toQFunNZ x`. -/
theorem toQFunNZ_qnegNZ (x : QFunNZ) : toQFunNZ (qnegNZ x) = - toQFunNZ x :=
  Compute.toQFun_qneg x.1

end QFunNZ

end DeepWiki.SymbolicIntegration
