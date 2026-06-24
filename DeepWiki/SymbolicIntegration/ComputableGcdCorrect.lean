import DeepWiki.SymbolicIntegration.ComputableSplitFactorFast
import DeepWiki.SymbolicIntegration.ComputableFieldGcd
import DeepWiki.SymbolicIntegration.SubresultantCorrectness

/-! # Abstract correctness of the fraction-free gcd `cgcdFF` over ℚ(x)[t]
The fraction-free monic gcd `cgcdFF` (`ComputableSplitFactorFast`) clears the ℚ(x)-denominators of its
inputs into ℚ[x][t] (`clearDenoms`), runs a **primitive polynomial-remainder sequence** `primPRSgcd`
over ℚ[x][t] (each step the primitive part of a pseudo-remainder, no field division), lifts the result
back to ℚ(x)[t] and monic-normalizes. It is validated *pointwise* by `native_decide` (Example 3.5.1 in
`ComputableSplitFactorFast`). This file proves the **abstract** correctness — for ALL inputs, axiom-clean
(no `native_decide`) — that `cgcdFF` computes the polynomial gcd over the field ℚ(x) = `RatFunc ℚ`.

Two carriers and two Horner bridges meet here, over the same indeterminate `t`:
* `toPolyG : CPolyG QFunNZ → (RatFunc ℚ)[X]` (`GenericPolyEngine`) — the honest ℚ(x)[t] polynomial of a
  `t`-list with ℚ(x)-coefficients.
* `toBPoly : BPoly → (ℚ[X])[X]` (`ComputeCorrectness`) — the honest ℚ[x][t] polynomial of a `t`-list
  with ℚ[x]-coefficients; composing with the coefficient ring embedding `algebraMap ℚ[X] (RatFunc ℚ)`
  re-reads it as a ℚ(x)[t] polynomial `toPolyB`.

The spine:
1. **`clearDenoms` bridge**: `toPolyB (clearDenoms p) = C s · toPolyG p` for the (nonzero) common
   denominator scalar `s ∈ RatFunc ℚ` — so the cleared ℚ[x][t] poly is, over the field ℚ(x), a
   **unit multiple** of `toPolyG p` (`Associated`).
2. **primitive-PRS ⇒ gcd**: each `primPRSgcd` step preserves `gcd(toPolyB·, toPolyB·)` up to associates
   over the field ℚ(x) — content stripping is a ℚ(x)-unit (`bprimitivePartX`), and a pseudo-remainder
   step is a Euclidean step up to a ℚ(x)-unit content factor. So `toPolyB (primPRSgcd P Q)` is
   `Associated` to `gcd (toPolyB P) (toPolyB Q)`.
3. **`cgcdFF` correct**: combine 1+2 — over ℚ(x), `toPolyG (cgcdFF p q)` is `Associated` to
   `gcd (toPolyG p) (toPolyG q)` in `(RatFunc ℚ)[X]`, the monic normalization fixing the unit. -/

open Polynomial Classical

namespace DeepWiki.SymbolicIntegration

open Compute

/-! ### The coefficient-ring lift `(ℚ[X])[X] → (RatFunc ℚ)[X]` and `toPolyB`
`liftRF` is the polynomial ring map induced by the field embedding `algebraMap ℚ[X] (RatFunc ℚ)`
(injective). `toPolyB p := liftRF (toBPoly p)` reads a `BPoly` (ℚ[x][t]) as a ℚ(x)[t] polynomial, in
the **same** indeterminate `t` as `toPolyG`. Its homomorphism / coefficient lemmas all descend from the
`toBPoly` bridge of `ComputeCorrectness`. -/

/-- The field embedding `algebraMap ℚ[X] (RatFunc ℚ)` (`ℚ[x] ↪ ℚ(x)`), abbreviated. -/
noncomputable abbrev amRF : ℚ[X] →+* RatFunc ℚ := algebraMap ℚ[X] (RatFunc ℚ)

/-- The induced coefficient-ring lift `(ℚ[X])[X] →+* (RatFunc ℚ)[X]` (`ℚ[x][t] → ℚ(x)[t]`), applying
`amRF` to every `t`-coefficient. -/
noncomputable abbrev liftRF : (ℚ[X])[X] →+* (RatFunc ℚ)[X] := Polynomial.mapRingHom amRF

/-- **The ℚ(x)[t] reading of a `BPoly`** `toPolyB p`: read the ℚ[x][t] polynomial `toBPoly p` over the
field ℚ(x) via the coefficient embedding `amRF`. Lives in the same `(RatFunc ℚ)[X]` as `toPolyG`. -/
noncomputable def toPolyB (p : BPoly) : (RatFunc ℚ)[X] := liftRF (toBPoly p)

/-- `toPolyB [] = 0`. -/
@[simp] theorem toPolyB_nil : toPolyB ([] : BPoly) = 0 := by simp [toPolyB]

/-- `amRF (toPoly c) ≠ 0` whenever `toPoly c ≠ 0` (the field embedding is injective). -/
theorem amRF_toPoly_ne_zero {c : CPoly} (hc : toPoly c ≠ 0) : amRF (toPoly c) ≠ 0 :=
  Compute.am_toPoly_ne_zero hc

/-- **`toPolyB` ignores normalization**: `toPolyB (bnorm p) = toPolyB p`. -/
@[simp] theorem toPolyB_bnorm (p : BPoly) : toPolyB (bnorm p) = toPolyB p := by
  simp [toPolyB]

/-- `toPolyB p = 0 ↔ toBPoly p = 0` (the lift is injective, `amRF` injective on coefficients). -/
theorem toPolyB_eq_zero_iff (p : BPoly) : toPolyB p = 0 ↔ toBPoly p = 0 := by
  rw [toPolyB, ← Polynomial.map_zero (amRF)]
  exact Polynomial.map_injective amRF (RatFunc.algebraMap_injective ℚ) |>.eq_iff

/-- `toPolyB p = 0 ↔ bisZero p = true`. -/
theorem toPolyB_eq_zero_iff_bisZero (p : BPoly) : toPolyB p = 0 ↔ bisZero p = true := by
  rw [toPolyB_eq_zero_iff, bisZero_iff_toBPoly_eq_zero]

/-- **Coefficient read**: `(toPolyB p).coeff i = amRF (toPoly (p.getD i []))`. -/
theorem toPolyB_coeff (p : BPoly) (i : ℕ) :
    (toPolyB p).coeff i = amRF (toPoly (p.getD i [])) := by
  rw [toPolyB, liftRF, Polynomial.coe_mapRingHom, Polynomial.coeff_map, toBPoly_coeff]

end DeepWiki.SymbolicIntegration
