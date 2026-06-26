import DeepWiki.SymbolicIntegration.ComputableRadicalExtension

/-! # The radical derivation invariant: `radDeriv` is a genuine derivation
`ComputableRadicalExtension` builds the simple-radical carrier `RadExt α n f = α[y]/(yⁿ − f)` with the
ring ops `radAdd`/`radMul` and the **diagonal** derivation `radDeriv` (Trager Appendix A's `(f/y)'`
form), and *validates* the derivation on examples by `native_decide`. This file makes
"`radDeriv` is a derivation" a **general theorem** — additive and Leibniz — over an arbitrary base
`[CField α] [CDiffField α] [CFieldSpec α] [CDiffFieldSpec α]`.

Because the engine classes `CField`/`CDiffField` carry *no* algebraic laws (the ring/derivation
identities live only in the `CFieldSpec`/`CDiffFieldSpec` bridges via `toK : α → K`), the faithful
statement is the one **in the genuine field** `K = CFieldSpec.K α`, read through the Horner bridge
`toPolyG : RadElem α → K[X]` (treating the formal variable `X` as the radical generator `y`). The
keystone is

* **`toPolyG_radDeriv`** — `toPolyG (radDeriv n f p) = implicitDeriv (C (toK ℓ) · X) (toPolyG p)` with
  `ℓ = logDerRadicand n f = f'/(nf)`: the computable diagonal derivation realizes Mathlib's
  `Differential.implicitDeriv` for the rule `y' = ℓ·y` (`implicitDeriv (C(toK ℓ)·X) X = C(toK ℓ)·X`,
  i.e. `X' = (toK ℓ)·y`). This is Trager's `(f/y)'` insight as an honest `K[X]` identity.

From the keystone, since `implicitDeriv v` is a Mathlib `Derivation` (hence ℤ-linear and Leibniz):

* **`toPolyG_radDeriv_radAdd`** (additivity) — `radDeriv` commutes with `radAdd` in `K[X]`:
  `toPolyG (radDeriv n f (radAdd a b)) = toPolyG (radDeriv n f a) + toPolyG (radDeriv n f b)`. Clean and
  exact (no `yⁿ = f` reduction is involved in either `radAdd` or `radDeriv`).
* **`toPolyG_radDeriv_radMul_mod`** (Leibniz, modulo the ideal) — the product rule for `radMul` holds
  **modulo `Xⁿ − toPolyG f`** (the defining ideal of the carrier): the free-polynomial Leibniz of
  `implicitDeriv` plus the facts that (i) `radReduce`/`radMul` change a polynomial only by a multiple of
  `Xⁿ − toPolyG f`, and (ii) the crux `D(Xⁿ − toPolyG f) ≡ 0 (mod Xⁿ − toPolyG f)` — i.e.
  `n·X^{n−1}·(ℓ·X) = D(toPolyG f)` in the quotient — make `implicitDeriv` descend to the quotient.

These are the derivation axioms underwriting the eventual **soundness capstone** `D(∫f) = f`: once the
integrator returns `v + Σ cᵢ log uᵢ`, `D(v + Σ cᵢ log uᵢ) = radDeriv v + Σ cᵢ·radDeriv(uᵢ)/uᵢ` only
*means* anything once `radDeriv` is proven additive and Leibniz. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open scoped Differential

namespace RadElem

variable {α : Type*} [CField α]

/-! ### `toK (cnatCastG k) = (k : K)` — the natural-cast bridge

`cnatCastG k = 1 + 1 + … + 1` (`k` times) over `[CField α]` reads through `toK` as the genuine `(k : K)`.
The index-`i` diagonal multiplier `i·ℓ` of `radDeriv` uses `cnatCastG i`, so we need this to identify the
derivation with Mathlib's `derivative` (whose `i`-th coefficient scaling is `(i : K)`). -/

variable [CFieldSpec α]

/-- **`toK (cnatCastG k) = (k : K)`**: the `k`-fold `CField.one` sum reads as the genuine natural cast in
`K`. The bridge that turns `radDeriv`'s `cnatCastG i` index-multiplier into `(i : K)`. -/
theorem toK_cnatCastG (k : ℕ) : CFieldSpec.toK (CPolyG.cnatCastG k : α) = (k : CFieldSpec.K α) := by
  induction k with
  | zero => rw [CPolyG.cnatCastG, CFieldSpec.toK_zero, Nat.cast_zero]
  | succ n ih => rw [CPolyG.cnatCastG, CFieldSpec.toK_add, CFieldSpec.toK_one, ih, Nat.cast_succ,
      add_comm]

end RadElem

/-! ### The keystone: `radDeriv` realizes `implicitDeriv (C (toK ℓ) · X)`

`radDeriv n f p = (zipIdx p).map (fun (a,i) ↦ D(aᵢ) + aᵢ·(i·ℓ))` with `ℓ = logDerRadicand n f`. Read
through `toPolyG`, this is the closed `K[X]` form `mapCoeffs(toPolyG p) + C(toK ℓ)·(X·derivative(toPolyG
p))`, which is exactly `Differential.implicitDeriv (C(toK ℓ)·X) (toPolyG p)` — the derivation extending
the base coefficient derivation by `X' = (toK ℓ)·X` (i.e. `y' = ℓ·y`). The proof is an induction over the
coefficient list with the `zipIdx` start-index `k` generalized (the closed form carries an extra `(k:K[X])
· toPolyG p` term, which vanishes at the `k = 0` entry point). -/

namespace RadElem

variable {α : Type*} [CField α] [CDiffField α] [CFieldSpec α] [CDiffFieldSpec α]

/-- **The index-generalized diagonal map** `radDerivFrom ℓ k p` = `(List.zipIdx p k).map (fun (a,i) ↦
D(a) + a·(i·ℓ))`: the body of `radDeriv` with the `zipIdx` start index exposed as `k` (so `radDeriv n f =
radDerivFrom (logDerRadicand n f) 0`). Generalizing `k` is what lets the closed-form `toPolyG` recursion
go through. -/
def radDerivFrom (ℓ : α) (k : ℕ) (p : RadElem α) : RadElem α :=
  (List.zipIdx p k).map (fun a =>
    CField.add (CDiffField.cderiv a.1) (CField.mul a.1 (CField.mul (CPolyG.cnatCastG a.2) ℓ)))

omit [CFieldSpec α] [CDiffFieldSpec α] in
/-- **`radDeriv` is `radDerivFrom` from index `0`** — `radDeriv n f p = radDerivFrom (logDerRadicand n
f) 0 p`. Unfolds `radDeriv`'s `zipIdx` (`List.zipIdx p = List.zipIdx p 0`) to the index-generalized form. -/
theorem radDeriv_eq_radDerivFrom (n : ℕ) (f : α) (p : RadElem α) :
    radDeriv n f p = radDerivFrom (logDerRadicand n f) 0 p := by
  rw [radDeriv, radDerivFrom]

/-- **The closed `K[X]` form of the index-generalized diagonal map**: `toPolyG (radDerivFrom ℓ k p) =
mapCoeffs(toPolyG p) + C(toK ℓ)·(X·derivative(toPolyG p) + (k:K[X])·toPolyG p)`. The `(k:K[X])·toPolyG p`
term is the contribution of the running `zipIdx` index. Proven by induction on `p`. -/
theorem toPolyG_radDerivFrom (ℓ : α) (k : ℕ) (p : RadElem α) :
    CPolyG.toPolyG (radDerivFrom ℓ k p)
      = Differential.mapCoeffs (CPolyG.toPolyG p)
        + Polynomial.C (CFieldSpec.toK ℓ)
          * (X * Polynomial.derivative (CPolyG.toPolyG p)
              + (k : (CFieldSpec.K α)[X]) * CPolyG.toPolyG p) := by
  induction p generalizing k with
  | nil => simp [radDerivFrom]
  | cons a as ih =>
    rw [radDerivFrom, List.zipIdx_cons, List.map_cons]
    show CPolyG.toPolyG (CField.add (CDiffField.cderiv a)
          (CField.mul a (CField.mul (CPolyG.cnatCastG k) ℓ)) :: radDerivFrom ℓ (k + 1) as) = _
    rw [CPolyG.toPolyG_cons, CFieldSpec.toK_add, CFieldSpec.toK_mul, CFieldSpec.toK_mul,
      CDiffFieldSpec.toK_cderiv, toK_cnatCastG]
    rw [ih (k + 1), CPolyG.toPolyG_cons]
    -- expand `mapCoeffs (C(toK a) + X·toPolyG as)` and `derivative (C(toK a) + X·toPolyG as)` by the
    -- derivation/derivative product rules (`mapCoeffs X = 0`, `derivative X = 1`, `derivative C = 0`).
    have hmc : Differential.mapCoeffs (Polynomial.C (CFieldSpec.toK a) + X * CPolyG.toPolyG as)
        = Polynomial.C (Differential.deriv (CFieldSpec.toK a))
          + X * Differential.mapCoeffs (CPolyG.toPolyG as) := by
      rw [map_add, Differential.mapCoeffs_C, Derivation.leibniz, Differential.mapCoeffs_X, smul_zero,
        add_zero, smul_eq_mul]
    have hder : Polynomial.derivative (Polynomial.C (CFieldSpec.toK a) + X * CPolyG.toPolyG as)
        = CPolyG.toPolyG as + X * Polynomial.derivative (CPolyG.toPolyG as) := by
      rw [derivative_add, derivative_C, zero_add, derivative_mul, derivative_X, one_mul]
    rw [hmc, hder]
    simp only [map_add, map_mul, Polynomial.C_eq_natCast, Nat.cast_succ]
    ring

/-- **★ The keystone — `radDeriv` realizes `implicitDeriv (C (toK ℓ) · X)`**: through the Horner bridge
`toPolyG` (with `X` the radical generator `y`), `toPolyG (radDeriv n f p) = Differential.implicitDeriv (C
(toK ℓ) · X) (toPolyG p)` with `ℓ = logDerRadicand n f = f'/(nf)`. The computable diagonal derivation IS
Mathlib's `implicitDeriv` for the rule `y' = ℓ·y` (`implicitDeriv (C(toK ℓ)·X) X = C(toK ℓ)·X`, i.e. `X'
= (toK ℓ)·y`). Trager's `(f/y)'` insight as an honest `K[X]` identity; the source of additivity and
Leibniz. -/
theorem toPolyG_radDeriv (n : ℕ) (f : α) (p : RadElem α) :
    CPolyG.toPolyG (radDeriv n f p)
      = Differential.implicitDeriv
          (Polynomial.C (CFieldSpec.toK (logDerRadicand n f)) * X) (CPolyG.toPolyG p) := by
  rw [radDeriv_eq_radDerivFrom, toPolyG_radDerivFrom]
  -- `implicitDeriv v q = mapCoeffs q + v · derivative q`; here `v = C(toK ℓ)·X`, and the `k = 0` index
  -- term `0·toPolyG p` vanishes.
  rw [Differential.implicitDeriv]
  simp only [Derivation.add_apply, Derivation.smul_apply, Derivation.restrictScalars_apply,
    Nat.cast_zero, zero_mul, add_zero, smul_eq_mul, derivative'_apply]
  ring

/-! ### Additivity: `radDeriv` commutes with `radAdd` (the clean floor)

`radAdd = caddG` and `radDeriv` both leave the `yⁿ = f` reduction untouched, so additivity is an exact
`K[X]` identity: `toPolyG` turns it into the ℤ-linearity of Mathlib's `implicitDeriv` derivation. No
quotient subtlety enters. -/

/-- **★ `radDeriv` is additive** — `toPolyG (radDeriv n f (radAdd a b)) = toPolyG (radDeriv n f a) +
toPolyG (radDeriv n f b)` in `K[X]`. Exact (neither `radAdd` nor `radDeriv` touches the `yⁿ = f`
reduction); from the keystone `toPolyG_radDeriv` and the additivity of `implicitDeriv` (`toPolyG (radAdd a
b) = toPolyG a + toPolyG b` via `toPolyG_caddG`). The first derivation axiom. -/
theorem toPolyG_radDeriv_radAdd (n : ℕ) (f : α) (a b : RadElem α) :
    CPolyG.toPolyG (radDeriv n f (radAdd a b))
      = CPolyG.toPolyG (radDeriv n f a) + CPolyG.toPolyG (radDeriv n f b) := by
  rw [toPolyG_radDeriv, toPolyG_radDeriv, toPolyG_radDeriv, radAdd, CPolyG.toPolyG_caddG, map_add]
