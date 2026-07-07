import DeepWiki.SymbolicIntegration.MonomialExtensions
import Mathlib.FieldTheory.RatFunc.Basic

/-! # Canonical representation classifiers

Simple and reduced rational functions for monomial derivations. -/

open scoped Differential
open Polynomial

namespace DeepWiki.SymbolicIntegration

section Classify
variable {K : Type*} [Field K] [Differential K]

/-- `f ∈ k(t)` is *simple* w.r.t. the monomial derivation `D` (`Dt = v`) if its denominator is
normal — coprime to its `D`-derivative `D(denom f)`. -/
def IsSimple (v : K[X]) (f : RatFunc K) : Prop :=
  IsCoprime f.denom (Differential.implicitDeriv v f.denom)

/-- `f ∈ k(t)` is *reduced* w.r.t. the monomial derivation `D` (`Dt = v`) if its denominator is
special — it divides its `D`-derivative `D(denom f)`. The reduced elements form the subfield
`k⟨t⟩`. -/
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

end DeepWiki.SymbolicIntegration
