import DeepWiki.SymbolicIntegration.ComputablePolyPartTower
import DeepWiki.SymbolicIntegration.ComputableHermiteTowerCorrect

/-! # Abstract correctness of the polynomial-side §5 reductions (Bronstein §5.4, §5.8)

The polynomial-part reductions `cPolyReduceTower` (§5.4 `PolynomialReduce`) and
`cPrimitivePolyIntegrate` (§5.8 primitive-case `IntegratePrimitivePolynomial`, constant-coefficient
sub-case) each split a polynomial part `p ∈ ℚ(x)[t]` as `p = D(q) + r` with `D = cmonomialDeriv Dt`
the monomial derivation. They are validated *pointwise* by `native_decide` (`polyReduceTower_example`,
`primitivePolyIntegrate_example`, both checking `cisZeroG (csubG (caddG (D q) r) p) = true`). This file
proves the **abstract** correctness — for ALL inputs, axiom-clean (no `native_decide`) — the cleared
identity `D(q) + r = p` that those checks pin.

**Route — pure induction on fuel through the `implicitDeriv` derivation.** Unlike the Hermite residual
(§5.3, `cHermiteReduceTower_cleared_identity`), no exact division or fraction-clearing is needed: every
`q`, `r`, `p` here is a genuine `CPolyG QFunNZ` polynomial, and one reduction step subtracts `D(q₀)` and
recurses on `p' = p − D(q₀)`. Reading through `toPolyG` into `(RatFunc ℚ)[X]`, the monomial derivation
`D = cmonomialDeriv Dt` becomes `Differential.implicitDeriv (toPolyG Dt)` (`toPolyG_cmonomialDeriv`), a
`Derivation` and hence **additive** (`map_add`): `D(q₀ + q') = D(q₀) + D(q')`. So if the recursive call
returns `(q', r)` with `D(q') + r = p'`, then `D(q₀ + q') + r = D(q₀) + p' = D(q₀) + (p − D(q₀)) = p`.
The base cases return `([], cnormG p)` with `D(0) + p = p`. The whole identity is a clean induction on
`fuel`, gated on no preconditions at all (the degree/fuel hypotheses only govern *whether* `deg(r) <
δ(t)`, not whether `D(q) + r = p`). -/

open Polynomial Classical

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

/-! ### §5.4 — the cleared polynomial-reduction identity `D(q) + r = p` for ALL inputs

`cPolyReduceTower Dt fuel p = (q, r)` peels leading terms `q₀ = (lc(p)/(m·λ))·tᵐ`, subtracts `D(q₀)`,
and recurses. The cleared identity is `D(q) + r = p` over `(RatFunc ℚ)[X]`, i.e.
`implicitDeriv (toPolyG Dt) (toPolyG q) + toPolyG r = toPolyG p` — proved by induction on `fuel`, the
additivity of `implicitDeriv` gluing `q₀` to the recursive `q'`. -/

/-- **`cPolyReduceTower` satisfies the cleared reduction identity `D(q) + r = p`** (abstract, ALL
inputs) over the field ℚ(x). With `(q, r) = cPolyReduceTower Dt fuel p` and `D = cmonomialDeriv Dt`
the monomial derivation (`= Differential.implicitDeriv (toPolyG Dt)` through `toPolyG`), the §5.4
reduction reconstructs the polynomial part exactly:
`implicitDeriv (toPolyG Dt) (toPolyG q) + toPolyG r = toPolyG p` in `(RatFunc ℚ)[X]`. The all-inputs,
axiom-clean (no `native_decide`) generalization of `polyReduceTower_example`'s `cisZeroG`-check; gated
on no preconditions (the fuel/degree hypotheses bound the remainder degree, not the identity). Proved
by induction on `fuel`, the additivity of the `implicitDeriv` derivation gluing the peeled leading
term to the recursive reduction. -/
theorem cPolyReduceTower_cleared_identity (Dt : CPolyG QFunNZ) :
    ∀ (fuel : ℕ) (p : CPolyG QFunNZ),
      Differential.implicitDeriv (toPolyG Dt) (toPolyG (cPolyReduceTower Dt fuel p).1)
          + toPolyG (cPolyReduceTower Dt fuel p).2
        = toPolyG p := by
  intro fuel
  induction fuel with
  | zero =>
    intro p
    -- base case: `cPolyReduceTower Dt 0 p = ([], cnormG p)`, so `D(0) + p = p`
    show Differential.implicitDeriv (toPolyG Dt) (toPolyG ([] : CPolyG QFunNZ))
        + toPolyG (cnormG p) = toPolyG p
    rw [toPolyG_nil, map_zero, zero_add, toPolyG_cnormG]
  | succ fuel ih =>
    intro p
    -- unfold one reduction step
    rw [cPolyReduceTower]
    set delta := cdegG Dt with hdelta
    by_cases hcase : ((cnormG p : List QFunNZ).length ≤ delta)
    · -- done branch: returns `([], cnormG p)`
      simp only [hcase, if_true]
      show Differential.implicitDeriv (toPolyG Dt) (toPolyG ([] : CPolyG QFunNZ))
          + toPolyG (cnormG p) = toPolyG p
      rw [toPolyG_nil, map_zero, zero_add, toPolyG_cnormG]
    · -- recursion branch: peel `q₀`, recurse on `p' = cnormG p − D(q₀)`
      simp only [hcase, if_false]
      -- name the peeled leading term `q₀` and the residual `p'`
      set n := cdegG (cnormG p) with hn
      set m := n - delta + 1 with hm
      set lam := cleadG Dt with hlam
      set c := CField.div (cleadG (cnormG p)) (CField.mul (cnatCastG m) lam) with hc
      set q0 := cshiftG m [c] with hq0
      set p' := csubG (cnormG p) (cmonomialDeriv Dt q0) with hp'
      -- the recursive call result
      rcases hrec : cPolyReduceTower Dt fuel p' with ⟨q', r⟩
      simp only []
      -- the induction hypothesis on `p'`
      have ihp : Differential.implicitDeriv (toPolyG Dt) (toPolyG (cPolyReduceTower Dt fuel p').1)
          + toPolyG (cPolyReduceTower Dt fuel p').2 = toPolyG p' := ih p'
      rw [hrec] at ihp
      simp only at ihp
      -- `D(q₀ + q') + r = D(q₀) + (D(q') + r) = D(q₀) + p'`, and `p' = cnormG p − D(q₀)`
      rw [toPolyG_caddG, map_add, add_assoc, ihp, hp', toPolyG_csubG, toPolyG_cmonomialDeriv,
        toPolyG_cnormG]
      ring

-- `cPolyReduceTower Dt fuel p = (q, r)` reconstructs the polynomial part: `D(q) + r = p` over ℚ(x)[t].
example (Dt : CPolyG QFunNZ) (fuel : ℕ) (p : CPolyG QFunNZ) :
    Differential.implicitDeriv (toPolyG Dt) (toPolyG (cPolyReduceTower Dt fuel p).1)
        + toPolyG (cPolyReduceTower Dt fuel p).2
      = toPolyG p :=
  cPolyReduceTower_cleared_identity Dt fuel p

/-! ### The `cisZeroG`-Boolean form — directly bridging the §5.4 `native_decide` validation
`polyReduceTower_example` checks `cisZeroG (csubG (caddG (D q) r) p) = true` for the concrete
`(Dt, p)`. The abstract theorem makes that exact Boolean check provably `true` for ALL inputs: through
`cisZeroG_iff` (`cisZeroG x = true ↔ toPolyG x = 0`) and the `toPolyG` homomorphism lemmas, the
`(D q + r) − p` polynomial is `0` exactly when the cleared reduction identity holds. -/

/-- **The §5.4 `native_decide` cleared check holds for ALL inputs**: with `(q, r) = cPolyReduceTower
Dt fuel p` and `D = cmonomialDeriv Dt`, the exact Boolean check that `polyReduceTower_example` runs by
`native_decide` — `cisZeroG (csubG (caddG (D q) r) p) = true` — is a theorem for every `Dt fuel p`,
gated on no preconditions. The all-inputs, axiom-clean (no `native_decide`) generalization of the
pointwise §5.4 validation. -/
theorem cPolyReduceTower_cisZeroG_cleared (Dt : CPolyG QFunNZ) (fuel : ℕ) (p : CPolyG QFunNZ) :
    cisZeroG (csubG
      (caddG (cmonomialDeriv Dt (cPolyReduceTower Dt fuel p).1) (cPolyReduceTower Dt fuel p).2) p)
      = true := by
  rw [cisZeroG_iff, toPolyG_csubG, toPolyG_caddG, toPolyG_cmonomialDeriv, sub_eq_zero]
  exact cPolyReduceTower_cleared_identity Dt fuel p

/-! ### §5.8 — the cleared primitive-integration identity `D(q) + rem = p` for ALL inputs

`cPrimitivePolyIntegrate Dt fuel p = (q, rem)` (the degree-lowering loop of Bronstein's
`IntegratePrimitivePolynomial`, primitive case `Dt ∈ k`, constant-coefficient sub-case) peels
`q₀ = c·t^(m+1)` with `c = aₘ/((m+1)·Dt(0))`, subtracts `D(q₀)`, and recurses, stopping when only the
`t⁰` term remains. The reduction identity is identical in shape to §5.4 — `D(q) + rem = p` — and proved
by the *same* fuel induction through the additivity of `implicitDeriv`. (The §5.8 *integrability*
decision — whether the leftover `rem` is itself integrable, the general `LimitedIntegrate`/Chapter-7
solve — is a separate, deferred question; this is the cleared reconstruction identity only.) -/

/-- **`cPrimitivePolyIntegrate` satisfies the cleared integration identity `D(q) + rem = p`**
(abstract, ALL inputs) over the field ℚ(x). With `(q, rem) = cPrimitivePolyIntegrate Dt fuel p` and
`D = cmonomialDeriv Dt` the monomial derivation (`= Differential.implicitDeriv (toPolyG Dt)` through
`toPolyG`), the §5.8 primitive-case degree-lowering loop reconstructs the polynomial part exactly:
`implicitDeriv (toPolyG Dt) (toPolyG q) + toPolyG rem = toPolyG p` in `(RatFunc ℚ)[X]`. The all-inputs,
axiom-clean (no `native_decide`) generalization of `primitivePolyIntegrate_example`'s `cisZeroG`-check;
gated on no preconditions. Proved by the same induction on `fuel` as §5.4, the additivity of the
`implicitDeriv` derivation gluing the peeled `q₀ = c·t^(m+1)` to the recursive integration. (This is
the cleared reconstruction `D(q) + rem = p`; the §5.8 *integrability decision* on the leftover `rem` is
the deferred `LimitedIntegrate` oracle, a separate question.) -/
theorem cPrimitivePolyIntegrate_cleared_identity (Dt : CPolyG QFunNZ) :
    ∀ (fuel : ℕ) (p : CPolyG QFunNZ),
      Differential.implicitDeriv (toPolyG Dt) (toPolyG (cPrimitivePolyIntegrate Dt fuel p).1)
          + toPolyG (cPrimitivePolyIntegrate Dt fuel p).2
        = toPolyG p := by
  intro fuel
  induction fuel with
  | zero =>
    intro p
    -- base case: `cPrimitivePolyIntegrate Dt 0 p = ([], cnormG p)`, so `D(0) + p = p`
    show Differential.implicitDeriv (toPolyG Dt) (toPolyG ([] : CPolyG QFunNZ))
        + toPolyG (cnormG p) = toPolyG p
    rw [toPolyG_nil, map_zero, zero_add, toPolyG_cnormG]
  | succ fuel ih =>
    intro p
    -- unfold one integration step
    rw [cPrimitivePolyIntegrate]
    by_cases hcase : ((cnormG p : List QFunNZ).length ≤ 1)
    · -- done branch: only the `t⁰` term remains, returns `([], cnormG p)`
      simp only [hcase, if_true]
      show Differential.implicitDeriv (toPolyG Dt) (toPolyG ([] : CPolyG QFunNZ))
          + toPolyG (cnormG p) = toPolyG p
      rw [toPolyG_nil, map_zero, zero_add, toPolyG_cnormG]
    · -- recursion branch: peel `q₀ = c·t^(m+1)`, recurse on `p' = cnormG p − D(q₀)`
      simp only [hcase, if_false]
      -- name the peeled leading term `q₀` and the residual `p'`
      set m := cdegG (cnormG p) with hm
      set am := cleadG (cnormG p) with ham
      set mp1 : QFunNZ := cnatCastG (m + 1) with hmp1
      set dtConst := cleadG Dt with hdtConst
      set c := CField.div am (CField.mul mp1 dtConst) with hc
      set q0 := cshiftG (m + 1) [c] with hq0
      set p' := csubG (cnormG p) (cmonomialDeriv Dt q0) with hp'
      -- the recursive call result
      rcases hrec : cPrimitivePolyIntegrate Dt fuel p' with ⟨q', rem⟩
      simp only []
      -- the induction hypothesis on `p'`
      have ihp : Differential.implicitDeriv (toPolyG Dt)
            (toPolyG (cPrimitivePolyIntegrate Dt fuel p').1)
          + toPolyG (cPrimitivePolyIntegrate Dt fuel p').2 = toPolyG p' := ih p'
      rw [hrec] at ihp
      simp only at ihp
      -- `D(q₀ + q') + rem = D(q₀) + (D(q') + rem) = D(q₀) + p'`, and `p' = cnormG p − D(q₀)`
      rw [toPolyG_caddG, map_add, add_assoc, ihp, hp', toPolyG_csubG, toPolyG_cmonomialDeriv,
        toPolyG_cnormG]
      ring

-- `cPrimitivePolyIntegrate Dt fuel p = (q, rem)` reconstructs the polynomial part: `D(q) + rem = p`.
example (Dt : CPolyG QFunNZ) (fuel : ℕ) (p : CPolyG QFunNZ) :
    Differential.implicitDeriv (toPolyG Dt) (toPolyG (cPrimitivePolyIntegrate Dt fuel p).1)
        + toPolyG (cPrimitivePolyIntegrate Dt fuel p).2
      = toPolyG p :=
  cPrimitivePolyIntegrate_cleared_identity Dt fuel p

/-- **The §5.8 `native_decide` cleared check holds for ALL inputs**: with `(q, rem) =
cPrimitivePolyIntegrate Dt fuel p` and `D = cmonomialDeriv Dt`, the exact Boolean check that
`primitivePolyIntegrate_example` runs by `native_decide` — `cisZeroG (csubG (caddG (D q) rem) p) =
true` — is a theorem for every `Dt fuel p`, gated on no preconditions. The all-inputs, axiom-clean (no
`native_decide`) generalization of the pointwise §5.8 validation. -/
theorem cPrimitivePolyIntegrate_cisZeroG_cleared (Dt : CPolyG QFunNZ) (fuel : ℕ) (p : CPolyG QFunNZ) :
    cisZeroG (csubG
      (caddG (cmonomialDeriv Dt (cPrimitivePolyIntegrate Dt fuel p).1)
        (cPrimitivePolyIntegrate Dt fuel p).2) p)
      = true := by
  rw [cisZeroG_iff, toPolyG_csubG, toPolyG_caddG, toPolyG_cmonomialDeriv, sub_eq_zero]
  exact cPrimitivePolyIntegrate_cleared_identity Dt fuel p

#print axioms cPolyReduceTower_cleared_identity
#print axioms cPolyReduceTower_cisZeroG_cleared
#print axioms cPrimitivePolyIntegrate_cleared_identity
#print axioms cPrimitivePolyIntegrate_cisZeroG_cleared

end DeepWiki.SymbolicIntegration
