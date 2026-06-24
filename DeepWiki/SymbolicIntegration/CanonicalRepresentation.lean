import DeepWiki.SymbolicIntegration.MonomialExtensions
import DeepWiki.SymbolicIntegration.SquarefreeFactorization
import Mathlib.FieldTheory.RatFunc.Basic

/-! # The canonical representation (Bronstein §3.5)
For a monomial extension `(k(t), D)` with `Dt = v ∈ k[t]`, every `f ∈ k(t)` splits *uniquely* as
`f = fₚ + fₛ + fₙ` — a polynomial part `fₚ`, a *reduced* (special-denominator) part `fₛ ∈ k⟨t⟩`,
and a *simple* (normal-denominator) part `fₙ`. We give the classifying predicates (`IsSimple`,
`IsReduced`), the splitting-factorization routine `splitFactor` that separates the special and
normal parts of a polynomial denominator, the squarefree variant `splitSquarefreeFactor` built on
Yun's factorization, the `canonicalRepresentation` of a rational function, and the root
characterization (a splitting factor `pₛ`/`pₙ` collects the constant/nonconstant roots). The
derivation on `k[X]` is the monomial derivation `implicitDeriv v` (`Dt = v`). -/

open scoped Differential
open Polynomial

namespace DeepWiki.SymbolicIntegration

section Classify
variable {K : Type*} [Field K] [Differential K]

/-- **Definition 3.5.2** (§3.5, p.100): `f ∈ k(t)` is *simple* w.r.t. the monomial derivation
`D` (`Dt = v`) if its denominator is normal — coprime to its `D`-derivative `D(denom f)`. -/
def IsSimple (v : K[X]) (f : RatFunc K) : Prop :=
  IsCoprime f.denom (Differential.implicitDeriv v f.denom)

/-- **Definition 3.5.2** (§3.5, p.100): `f ∈ k(t)` is *reduced* w.r.t. the monomial derivation
`D` (`Dt = v`) if its denominator is special — it divides its `D`-derivative `D(denom f)`. The
reduced elements form the subfield `k⟨t⟩`. -/
def IsReduced (v : K[X]) (f : RatFunc K) : Prop :=
  f.denom ∣ Differential.implicitDeriv v f.denom

/-- `IsSimple` is exactly `IsNormal` of the denominator under the monomial derivation. -/
theorem isSimple_iff_isNormal_denom (v : K[X]) (f : RatFunc K) :
    IsSimple v f ↔ @IsNormal _ _ ⟨Differential.implicitDeriv v⟩ f.denom :=
  Iff.rfl

/-- `IsReduced` is exactly `IsSpecial` of the denominator under the monomial derivation. -/
theorem isReduced_iff_isSpecial_denom (v : K[X]) (f : RatFunc K) :
    IsReduced v f ↔ @IsSpecial _ _ ⟨Differential.implicitDeriv v⟩ f.denom :=
  Iff.rfl

/-- A polynomial `p ∈ k[t]` is simple: its denominator is `1`, which is normal. -/
theorem isSimple_algebraMap (v : K[X]) (p : K[X]) :
    IsSimple v (algebraMap K[X] (RatFunc K) p) := by
  rw [IsSimple, RatFunc.denom_algebraMap]
  exact (@isNormal_one _ _ ⟨Differential.implicitDeriv v⟩)

/-- A polynomial `p ∈ k[t]` is reduced: its denominator is `1`, which is special. -/
theorem isReduced_algebraMap (v : K[X]) (p : K[X]) :
    IsReduced v (algebraMap K[X] (RatFunc K) p) := by
  rw [IsReduced, RatFunc.denom_algebraMap]
  exact (@isSpecial_one _ _ ⟨Differential.implicitDeriv v⟩)

/-- `IsReduced` from a special denominator: if `denom f` divides its `D`-derivative, `f` is
reduced (the defining condition, stated as an intro rule). -/
theorem isReduced_of_dvd_implicitDeriv {v : K[X]} {f : RatFunc K}
    (h : f.denom ∣ Differential.implicitDeriv v f.denom) : IsReduced v f := h

/-- `IsSimple` from a normal denominator: if `denom f` is coprime to its `D`-derivative, `f` is
simple (the defining condition, stated as an intro rule). -/
theorem isSimple_of_isCoprime_implicitDeriv {v : K[X]} {f : RatFunc K}
    (h : IsCoprime f.denom (Differential.implicitDeriv v f.denom)) : IsSimple v f := h

/-- `0` is both simple and reduced (denominator `1`). -/
theorem isSimple_zero (v : K[X]) : IsSimple v (0 : RatFunc K) := by
  rw [IsSimple, RatFunc.denom_zero]
  exact (@isNormal_one _ _ ⟨Differential.implicitDeriv v⟩)

/-- `0` is reduced (denominator `1`). -/
theorem isReduced_zero (v : K[X]) : IsReduced v (0 : RatFunc K) := by
  rw [IsReduced, RatFunc.denom_zero]
  exact (@isSpecial_one _ _ ⟨Differential.implicitDeriv v⟩)

end Classify

section SplitFactor
variable {K : Type*} [Field K] [Differential K]

open Classical in
/-- The squarefree special factor extracted at one `SplitFactor` step:
`S = gcd(p, Dp) / gcd(p, dp/dt)` (`Dt = v`). By Theorem 3.5.1 this is the product of the
*distinct* special irreducible factors of `p`. -/
noncomputable def splitFactorStep (v p : K[X]) : K[X] :=
  gcd p (Differential.implicitDeriv v p) / gcd p (derivative p)

open Classical in
/-- `SplitFactor` recursion (§3.5, p.100), as a `fuel`-bounded computation. Each step extracts the
squarefree special factor `S = gcd(p,Dp)/gcd(p,dp/dt)`; if `deg S = 0` the polynomial is normal and
`(p, 1)` is returned, otherwise recurse on `p/S` and multiply `S` back into the special part. The
result is `(pₙ, pₛ)`: the normal part and the special part. -/
noncomputable def splitFactorAux (v : K[X]) : K[X] → ℕ → K[X] × K[X]
  | p, 0 => (p, 1)
  | p, (n + 1) =>
    let S := splitFactorStep v p
    if S.natDegree = 0 then (p, 1)
    else
      let q := splitFactorAux v (p / S) n
      (q.1, S * q.2)

open Classical in
/-- **`SplitFactor`** (§3.5, p.100): the splitting of `p` into its normal part `pₙ` and special
part `pₛ` w.r.t. the monomial derivation `D` (`Dt = v`), with `p = pₙ·pₛ`. Iterates
`S ← gcd(p, Dp)/gcd(p, dp/dt)` until the remaining factor is normal. -/
noncomputable def splitFactor (v p : K[X]) : K[X] × K[X] :=
  splitFactorAux v p p.natDegree

end SplitFactor

end DeepWiki.SymbolicIntegration
