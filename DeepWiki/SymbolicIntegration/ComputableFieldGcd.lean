import DeepWiki.SymbolicIntegration.ComputableField

/-! # Generic division / gcd / derivative over a `CField`, and the `CField QFunNZ` instance
Stage B of the generic polynomial engine. Two layers sit on top of the `CField`/`CPolyG` keystone of
`ComputableField`:

* **`CField QFunNZ`** — the denominator-nonzero rational functions ℚ(x) as a *second* `CField`
  instance (over `K = RatFunc ℚ`, `toK = toQFunNZ`). It is the first non-trivial witness that the
  dropped-`toK`-injectivity design works: `isZero` is the numerator zero test (not a `K`-equality on
  a normal form), and every homomorphism law is discharged from the `toQFunNZ_*`/`toQFun_*` lemmas
  with the denominator-≠-0 side conditions cleared by subtype membership.

* **Generic `cdivmodG`/`cgcdExtG`/`cderivG`** — the `Compute.*` Euclidean division, extended
  Euclidean algorithm, and formal derivative, mirrored over an arbitrary `[CField α]` (ℚ-operations
  replaced by `CField.add`/`mul`/`neg`/`inv`/`isZero`, `toPoly` by `toPolyG`). Their correctness
  (`toPolyG_cdivmodG` Euclidean identity, `toPolyG_cgcdExtG` Bézout, `cgcdTerminatesG` +
  `toPolyG_cgcdExtG_dvd`, `toPolyG_cderivG`) is proven on all inputs over any `CField`. Coherence
  lemmas (`cdivmodG (α := ℚ) = cdivmod`, …) specialize back to the concrete engine so Stage C can
  migrate. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-! ### The `CField QFunNZ` instance (ℚ(x) as a computable field)

The denominator-nonzero subtype `QFunNZ` (`ComputableField`) already carries `qaddNZ`/`qmulNZ`/
`qnegNZ` and their `toQFunNZ_*` homomorphism lemmas. To build the `CField` instance we add `qoneNZ`,
`qzeroNZ`, `qinvNZ` (inverse: swap num/den when the numerator is nonzero, else `qzeroNZ`), and
`qsubNZ`, and read `isZero` off the **numerator** (`cisZero ∘ num`). This validates the design point
that `toK` need not be injective: `isZero` is a syntactic numerator test, certified against
`toQFunNZ x = 0` by `cisZero_iff_toPoly_eq_zero` together with the den-≠-0 membership. -/

namespace QFunNZ

/-- `qoneNZ`: the rational function `1 = 1/1` as a `QFunNZ` (denominator `[1]`, nonzero). -/
def qoneNZ : QFunNZ := ⟨Compute.qone, by simp [Compute.qone, Compute.toPoly_cons, Compute.toPoly_nil]⟩

/-- `qzeroNZ`: the rational function `0 = 0/1` as a `QFunNZ` (denominator `[1]`, nonzero). -/
def qzeroNZ : QFunNZ := ⟨Compute.qzero, by simp [Compute.qzero, Compute.toPoly_cons, Compute.toPoly_nil]⟩

/-- `qinvNZ`: inverse on `QFunNZ`. If the numerator is zero, the result is `qzeroNZ` (the `0⁻¹ = 0`
field convention); otherwise swap numerator and denominator (the new denominator is the old numerator,
nonzero by `¬ cisZero`). -/
def qinvNZ (x : QFunNZ) : QFunNZ :=
  if h : Compute.cisZero x.1.1 then qzeroNZ
  else ⟨(x.1.2, x.1.1), by
    show Compute.toPoly x.1.1 ≠ 0
    exact fun hz => h ((Compute.cisZero_iff_toPoly_eq_zero x.1.1).mpr hz)⟩

/-- `qsubNZ`: subtraction on `QFunNZ`, `x − y := x + (−y)`. -/
def qsubNZ (x y : QFunNZ) : QFunNZ := qaddNZ x (qnegNZ y)

/-- `isZeroNZ`: the zero test on `QFunNZ`, reading `cisZero` off the **numerator** (the denominator is
nonzero by membership, so `x = 0` iff its numerator vanishes). -/
def isZeroNZ (x : QFunNZ) : Bool := Compute.cisZero x.1.1

/-- **`toQFunNZ` reads `qoneNZ` as `1`**. -/
theorem toQFunNZ_qoneNZ : toQFunNZ qoneNZ = 1 := Compute.toQFun_qone

/-- **`toQFunNZ` reads `qzeroNZ` as `0`**. -/
theorem toQFunNZ_qzeroNZ : toQFunNZ qzeroNZ = 0 := Compute.toQFun_qzero

/-- **`qinvNZ` realizes `⁻¹`** on `QFunNZ`: `toQFunNZ (qinvNZ x) = (toQFunNZ x)⁻¹` (the `0⁻¹ = 0`
convention matches `RatFunc`). -/
theorem toQFunNZ_qinvNZ (x : QFunNZ) : toQFunNZ (qinvNZ x) = (toQFunNZ x)⁻¹ := by
  rw [qinvNZ]
  by_cases h : Compute.cisZero x.1.1
  · rw [dif_pos h, toQFunNZ_qzeroNZ]
    have hx0 : Compute.toPoly x.1.1 = 0 := (Compute.cisZero_iff_toPoly_eq_zero x.1.1).mp h
    rw [show toQFunNZ x = 0 from by
      rw [toQFunNZ, Compute.toQFun, hx0, map_zero, zero_div], inv_zero]
  · rw [dif_neg h]
    show Compute.toQFun (x.1.2, x.1.1) = (Compute.toQFun x.1)⁻¹
    obtain ⟨⟨a, b⟩, _⟩ := x
    rw [Compute.toQFun, Compute.toQFun, inv_div]

/-- **`qsubNZ` realizes `-`** on `QFunNZ`: `toQFunNZ (qsubNZ x y) = toQFunNZ x - toQFunNZ y`. -/
theorem toQFunNZ_qsubNZ (x y : QFunNZ) : toQFunNZ (qsubNZ x y) = toQFunNZ x - toQFunNZ y := by
  rw [qsubNZ, toQFunNZ_qaddNZ, toQFunNZ_qnegNZ, sub_eq_add_neg]

/-- **`isZeroNZ` is certified against `toQFunNZ = 0`**: `isZeroNZ x = true ↔ toQFunNZ x = 0` — the
numerator zero test agrees with vanishing in `RatFunc ℚ` (denominator nonzero by membership). -/
theorem isZeroNZ_iff (x : QFunNZ) : isZeroNZ x = true ↔ toQFunNZ x = 0 := by
  rw [isZeroNZ, Compute.cisZero_iff_toPoly_eq_zero]
  obtain ⟨⟨a, b⟩, hb⟩ := x
  rw [toQFunNZ, Compute.toQFun]
  have hbm : algebraMap ℚ[X] (RatFunc ℚ) (Compute.toPoly b) ≠ 0 := Compute.am_toPoly_ne_zero hb
  constructor
  · intro h; rw [h, map_zero, zero_div]
  · intro h
    rw [div_eq_zero_iff] at h
    rcases h with h | h
    · exact (map_eq_zero_iff _ (RatFunc.algebraMap_injective ℚ)).mp h
    · exact absurd h hbm

end QFunNZ

/-- **`CField QFunNZ`**: the denominator-nonzero rational functions ℚ(x) as a computable field over
`K = RatFunc ℚ` with `toK = toQFunNZ`. The first non-trivial `CField` instance — its `isZero` is the
numerator zero test (no `toK`-injectivity / lowest-terms normal form needed), validating the dropped-
injectivity design of `CField`. -/
noncomputable instance instCFieldQFunNZ : CField QFunNZ where
  zero := QFunNZ.qzeroNZ
  one := QFunNZ.qoneNZ
  add := QFunNZ.qaddNZ
  mul := QFunNZ.qmulNZ
  neg := QFunNZ.qnegNZ
  inv := QFunNZ.qinvNZ
  isZero := QFunNZ.isZeroNZ
  K := RatFunc ℚ
  toK := QFunNZ.toQFunNZ
  toK_zero := QFunNZ.toQFunNZ_qzeroNZ
  toK_one := QFunNZ.toQFunNZ_qoneNZ
  toK_add := QFunNZ.toQFunNZ_qaddNZ
  toK_mul := QFunNZ.toQFunNZ_qmulNZ
  toK_neg := QFunNZ.toQFunNZ_qnegNZ
  toK_inv := QFunNZ.toQFunNZ_qinvNZ
  isZero_iff := QFunNZ.isZeroNZ_iff

end DeepWiki.SymbolicIntegration
