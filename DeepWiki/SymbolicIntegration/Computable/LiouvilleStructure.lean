import Mathlib.FieldTheory.Differential.Liouville
import Mathlib.RingTheory.Derivation.MapCoeffs
import DeepWiki.SymbolicIntegration.AlgebraicCompleteness.Frontier

/-! # Structural Liouville descent

The Weak Liouville Theorem over Mathlib's `Differential.IsLiouville`: for a Liouville extension
`L ⊇ F` with no new constants, `g ∈ L` with `g′ ∈ F` gives `g′ = v₀′ + Σ cᵢ · logDeriv vᵢ` over `F`.
Its contrapositive propagates base non-elementarity through Liouville towers and supplies the
`AlgebraicLiouvilleFrontier` bridge used by algebraic-completeness statements. -/

open scoped Differential
open Polynomial Differential

namespace DeepWiki.SymbolicIntegration.LiouvilleStructure

/-! ## The Weak-Liouville-form predicate -/

section Predicate

variable (F : Type*) (K : Type*) [Field F] [Field K] [Differential F] [Differential K]
variable [Algebra F K]

/-- `HasWeakLiouvilleForm F K g`: read in `K`, `↑g = ∑ᵢ ↑cᵢ · logDeriv uᵢ + v′` for constants
`cᵢ ∈ F`, `uᵢ ∈ K`, `v ∈ K`. -/
def HasWeakLiouvilleForm (g : F) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (c : ι → F) (_ : ∀ x, (c x)′ = 0) (u : ι → K) (v : K),
    (algebraMap F K g) = ∑ x, (algebraMap F K (c x)) * logDeriv (u x) + v′

end Predicate

/-! ## The structural core: the descent through a Liouville instance -/

section Core

variable (F : Type*) (K : Type*) [Field F] [Field K] [Differential F] [Differential K]
variable [Algebra F K]

/-- The descent: for a Liouville extension `K / F`, a base `g ∈ F` with a `K`-Liouville form has an
`F`-Liouville form. -/
theorem weakLiouville_descend [IsLiouville F K] (g : F) (h : HasWeakLiouvilleForm F K g) :
    HasWeakLiouvilleForm F F g := by
  obtain ⟨ι, _, c, hc, u, v, hrep⟩ := h
  obtain ⟨ι₀, _, c₀, hc₀, u₀, v₀, hrep₀⟩ := IsLiouville.isLiouville g ι c hc u v hrep
  exact ⟨ι₀, inferInstance, c₀, hc₀, u₀, v₀, by
    simpa only [Algebra.algebraMap_self_apply] using hrep₀⟩

/-- Non-elementarity propagates up a Liouville extension: no `F`-Liouville form for `g` gives no
`K`-Liouville form. -/
theorem weakLiouville_propagates [IsLiouville F K] (g : F)
    (h : ¬ HasWeakLiouvilleForm F F g) : ¬ HasWeakLiouvilleForm F K g :=
  fun hK => h (weakLiouville_descend F K g hK)

/-- `IsLiouville F K ↔` every base element with a `K`-Liouville form has an `F`-Liouville form. -/
theorem hasWeakLiouvilleForm_descends_iff :
    IsLiouville F K ↔ ∀ g : F, HasWeakLiouvilleForm F K g → HasWeakLiouvilleForm F F g := by
  constructor
  · intro inst g h
    exact weakLiouville_descend F K g h
  · intro hdesc
    refine ⟨fun g ι _ c hc u v hrep => ?_⟩
    obtain ⟨ι₀, _, c₀, hc₀, u₀, v₀, hrep₀⟩ := hdesc g ⟨ι, inferInstance, c, hc, u, v, hrep⟩
    refine ⟨ι₀, inferInstance, c₀, hc₀, u₀, v₀, ?_⟩
    simpa only [Algebra.algebraMap_self_apply] using hrep₀

end Core

/-! ## The Weak Liouville Theorem proper: `g ∈ L`, `g′ ∈ F` ⟹ the Liouville form over `F` -/

section Theorem

variable (F : Type*) (L : Type*) [Field F] [Field L] [Differential F] [Differential L]
variable [Algebra F L] [DifferentialAlgebra F L]

omit [DifferentialAlgebra F L] in
/-- A base element that is a derivative up the tower has the trivial `L`-Liouville form: `↑a = (↑g)′`
gives `HasWeakLiouvilleForm F L a` with empty constant family. -/
theorem hasWeakLiouvilleForm_tower_of_isDeriv (a : F) (g : L)
    (h : (algebraMap F L a) = g′) : HasWeakLiouvilleForm F L a :=
  ⟨Empty, inferInstance, Empty.elim, fun x => x.elim, Empty.elim, g, by
    simpa only [Finset.univ_eq_empty, Finset.sum_empty, zero_add] using h⟩

omit [DifferentialAlgebra F L] in
/-- Weak Liouville Theorem, descent form: for a Liouville extension `L / F`, `g ∈ L` with `g′ ∈ F`
(via `↑a = (↑g)′`) gives `HasWeakLiouvilleForm F F a`. -/
theorem weakLiouville_of_isLiouville [IsLiouville F L] (a : F) (g : L)
    (h : (algebraMap F L a) = g′) : HasWeakLiouvilleForm F F a :=
  weakLiouville_descend F L a (hasWeakLiouvilleForm_tower_of_isDeriv F L a g h)

end Theorem

/-! ## The algebraic case: via Mathlib's `isLiouville_of_finiteDimensional` -/

section CaseAlgebraic

variable (F : Type*) (L : Type*) [Field F] [Field L] [CharZero F] [Differential F] [Differential L]
variable [Algebra F L] [DifferentialAlgebra F L]

/-- The algebraic case: for a finite-dimensional extension `L / F` (char 0), `g ∈ L` with `g′ ∈ F`
gives `HasWeakLiouvilleForm F F a`. -/
theorem weakLiouville_finiteDimensional [FiniteDimensional F L] (a : F) (g : L)
    (h : (algebraMap F L a) = g′) : HasWeakLiouvilleForm F F a := by
  haveI : IsLiouville F L := isLiouville_of_finiteDimensional
  exact weakLiouville_of_isLiouville F L a g h

/-- Algebraic case, contrapositive: no `F`-Liouville form for `a` gives none over a finite-dimensional
extension `L / F`. -/
theorem not_weakElementary_finiteDimensional [FiniteDimensional F L] (a : F)
    (h : ¬ HasWeakLiouvilleForm F F a) : ¬ HasWeakLiouvilleForm F L a := by
  haveI : IsLiouville F L := isLiouville_of_finiteDimensional
  exact weakLiouville_propagates F L a h

end CaseAlgebraic

/-! ## The transcendental case: the degree lemmas on `K[θ]`

The degree behaviour of the monomial derivation `Differential.implicitDeriv v` on `K[θ]`, for the two
monomial kinds: the log monomial `θ′ = c ∈ K` (`v = C c`) and the exp monomial `θ′ = c·θ`
(`v = C c · X`). -/

section CaseTranscendental

variable {K : Type*} [Field K] [Differential K]

/-! ### The log monomial `θ′ = c ∈ K` (`v = C c`) -/

/-- The log-monomial derivation on `K[θ]`: `Differential.implicitDeriv (C c)`, with `θ′ = c ∈ K`. -/
noncomputable def logMonomialDeriv (c : K) : Derivation ℤ K[X] K[X] :=
  Differential.implicitDeriv (C c)

/-- `θ′ = C c` for the log monomial. -/
@[simp]
lemma logMonomialDeriv_X (c : K) : logMonomialDeriv c (X : K[X]) = C c := by
  simp [logMonomialDeriv]

/-- The log monomial extends `K`'s derivation on constants: `D (C b) = C b′`. -/
@[simp]
lemma logMonomialDeriv_C (c b : K) : logMonomialDeriv c (C b) = C b′ := by
  simp [logMonomialDeriv]

/-- Coefficient formula for the log monomial:
`(D p).coeff i = (p.coeff i)′ + c·(i+1)·p.coeff (i+1)`. -/
lemma coeff_logMonomialDeriv (c : K) (p : K[X]) (i : ℕ) :
    (logMonomialDeriv c p).coeff i = (p.coeff i)′ + c * ((i + 1) * p.coeff (i + 1)) := by
  simp only [logMonomialDeriv, implicitDeriv, Derivation.coe_add, Pi.add_apply,
    Derivation.coe_smul, Pi.smul_apply, Derivation.restrictScalars_apply,
    derivative'_apply, coeff_add, coeff_mapCoeffs, smul_eq_mul, coeff_C_mul,
    coeff_derivative]
  ring

/-- Log monomial, top coefficient: `(D p).coeff (natDegree p) = (leadingCoeff p)′` (the degree drop). -/
lemma coeff_natDegree_logMonomialDeriv (c : K) (p : K[X]) :
    (logMonomialDeriv c p).coeff p.natDegree = (p.leadingCoeff)′ := by
  rw [coeff_logMonomialDeriv]
  have h : p.coeff (p.natDegree + 1) = 0 := coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _)
  rw [h, leadingCoeff]
  simp

/-- The log monomial does not raise `θ`-degree: `natDegree (D p) ≤ natDegree p`. -/
lemma natDegree_logMonomialDeriv_le (c : K) (p : K[X]) :
    (logMonomialDeriv c p).natDegree ≤ p.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [coeff_logMonomialDeriv]
  rw [coeff_eq_zero_of_natDegree_lt hi,
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (le_of_lt hi) (Nat.lt_succ_self i))]
  simp

/-! ### The exp monomial `θ′/θ = c ∈ K` (`v = C c · X`) -/

/-- The exp-monomial derivation on `K[θ]`: `Differential.implicitDeriv (C c · X)`, with `θ′ = c·θ`. -/
noncomputable def expMonomialDeriv (c : K) : Derivation ℤ K[X] K[X] :=
  Differential.implicitDeriv (C c * X)

/-- `θ′ = c·θ` for the exp monomial. -/
@[simp]
lemma expMonomialDeriv_X (c : K) : expMonomialDeriv c (X : K[X]) = C c * X := by
  simp [expMonomialDeriv]

/-- The exp monomial extends `K`'s derivation on constants: `D (C b) = C b′`. -/
@[simp]
lemma expMonomialDeriv_C (c b : K) : expMonomialDeriv c (C b) = C b′ := by
  simp [expMonomialDeriv]

/-- Coefficient formula for the exp monomial: `(D p).coeff i = (p.coeff i)′ + c·i·p.coeff i`. -/
lemma coeff_expMonomialDeriv (c : K) (p : K[X]) (i : ℕ) :
    (expMonomialDeriv c p).coeff i = (p.coeff i)′ + c * (i * p.coeff i) := by
  have hXmul : ((X : K[X]) * derivative p).coeff i = i * p.coeff i := by
    cases i with
    | zero => simp
    | succ n => rw [coeff_X_mul, coeff_derivative]; push_cast; ring
  simp only [expMonomialDeriv, implicitDeriv, Derivation.coe_add, Pi.add_apply,
    Derivation.coe_smul, Pi.smul_apply, Derivation.restrictScalars_apply,
    derivative'_apply, coeff_add, coeff_mapCoeffs, smul_eq_mul]
  have hrw : C c * X * derivative p = C c * (X * derivative p) := by ring
  rw [hrw, coeff_C_mul, hXmul]

/-- Exp monomial, top coefficient:
`(D p).coeff (natDegree p) = (leadingCoeff p)′ + c·(natDegree p)·(leadingCoeff p)` (degree-preserving). -/
lemma coeff_natDegree_expMonomialDeriv (c : K) (p : K[X]) :
    (expMonomialDeriv c p).coeff p.natDegree
      = (p.leadingCoeff)′ + c * (p.natDegree * p.leadingCoeff) := by
  rw [coeff_expMonomialDeriv, leadingCoeff]

/-- The exp monomial does not raise `θ`-degree: `natDegree (D p) ≤ natDegree p`. -/
lemma natDegree_expMonomialDeriv_le (c : K) (p : K[X]) :
    (expMonomialDeriv c p).natDegree ≤ p.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [coeff_expMonomialDeriv, coeff_eq_zero_of_natDegree_lt hi]
  simp

end CaseTranscendental

/-! ## The tower assembly: iterated `IsLiouville.trans` -/

section TowerAssembly

variable (F : Type*) (M : Type*) (L : Type*)
variable [Field F] [Field M] [Field L]
variable [Differential F] [Differential M] [Differential L]
variable [Algebra F M] [Algebra M L] [Algebra F L]
variable [DifferentialAlgebra F M] [DifferentialAlgebra M L] [DifferentialAlgebra F L]
variable [IsScalarTower F M L] [Differential.ContainConstants F M]

omit [DifferentialAlgebra M L] [DifferentialAlgebra F L] in
/-- Tower step: `M / F` and `L / M` Liouville with `ContainConstants F M` give `IsLiouville F L`. -/
theorem isLiouville_tower [IsLiouville F M] [IsLiouville M L] : IsLiouville F L :=
  IsLiouville.trans F M ‹IsLiouville F M› ‹IsLiouville M L›

omit [DifferentialAlgebra M L] [DifferentialAlgebra F L] in
/-- Weak Liouville Theorem over a two-layer tower `F ⊆ M ⊆ L`: `g ∈ L` with `g′ ∈ F` gives
`HasWeakLiouvilleForm F F a`. -/
theorem weakLiouville_tower [IsLiouville F M] [IsLiouville M L] (a : F) (g : L)
    (h : (algebraMap F L a) = g′) : HasWeakLiouvilleForm F F a := by
  haveI : IsLiouville F L := isLiouville_tower F M L
  exact weakLiouville_of_isLiouville F L a g h

omit [DifferentialAlgebra M L] [DifferentialAlgebra F L] in
/-- Two-layer contrapositive: no `F`-Liouville form for `a` gives none over `L`. -/
theorem not_weakElementary_tower [IsLiouville F M] [IsLiouville M L] (a : F)
    (h : ¬ HasWeakLiouvilleForm F F a) : ¬ HasWeakLiouvilleForm F L a := by
  haveI : IsLiouville F L := isLiouville_tower F M L
  exact weakLiouville_propagates F L a h

end TowerAssembly

/-! ## The transcendental exponential-layer assumption -/

section ExpResidual

variable (F : Type*) [Field F] [Differential F] [CharZero F]

/-- Every transcendental exp monomial layer `K / F` carries an `IsLiouville F K` instance. -/
def ExponentialLayerResidual : Prop :=
  ∀ (K : Type) [Field K] [Differential K] [Algebra F K] [DifferentialAlgebra F K],
    Nonempty (IsLiouville F K)

omit [CharZero F] in
/-- Given `ExponentialLayerResidual F`, the Weak Liouville Theorem holds for an exp layer: `g ∈ K`
with `g′ ∈ F` gives `HasWeakLiouvilleForm F F a`. -/
theorem weakLiouville_of_expResidual (hexp : ExponentialLayerResidual F)
    (K : Type) [Field K] [Differential K] [Algebra F K] [DifferentialAlgebra F K]
    (a : F) (g : K) (h : (algebraMap F K a) = g′) : HasWeakLiouvilleForm F F a := by
  haveI : IsLiouville F K := (hexp K).some
  exact weakLiouville_of_isLiouville F K a g h

end ExpResidual

/-! ## `AlgebraicLiouvilleFrontier` over `HasWeakLiouvilleForm` -/

section DischargeFrontier

variable (F : Type*) [Field F] [Differential F]

/-- `AlgebraicLiouvilleFrontier` (as-stated form, over `HasWeakLiouvilleForm`): for every Liouville
extension `K / F`, base non-elementarity propagates up. -/
theorem algebraicLiouvilleFrontier_form :
    ∀ (K : Type) [Field K] [Differential K] [Algebra F K] [DifferentialAlgebra F K] [IsLiouville F K]
      (f : F), ¬ HasWeakLiouvilleForm F F f → ¬ HasWeakLiouvilleForm F K f := by
  intro K _ _ _ _ _ f h
  exact weakLiouville_propagates F K f h

end DischargeFrontier

section DischargeFrontierAlgebraic

variable (F : Type*) [Field F] [Differential F] [CharZero F]

/-- `AlgebraicLiouvilleFrontier` for the finite-dimensional case, with `[IsLiouville F K]` dropped:
for every finite-dimensional `K / F` (char 0), base non-elementarity propagates up. -/
theorem algebraicLiouvilleFrontier_finiteDimensional
    (K : Type) [Field K] [Differential K] [Algebra F K] [DifferentialAlgebra F K]
    [FiniteDimensional F K] (f : F) (h : ¬ HasWeakLiouvilleForm F F f) :
    ¬ HasWeakLiouvilleForm F K f := by
  haveI : IsLiouville F K := isLiouville_of_finiteDimensional
  exact weakLiouville_propagates F K f h

end DischargeFrontierAlgebraic

/-! ### Restatements and axiom audit -/

section Restatements

-- Weak Liouville descent: a tower derivative whose derivative lies in the base has base form.
example (F L : Type*) [Field F] [Field L] [Differential F] [Differential L] [Algebra F L]
    [DifferentialAlgebra F L] [IsLiouville F L] (a : F) (g : L) (h : (algebraMap F L a) = g′) :
    HasWeakLiouvilleForm F F a :=
  weakLiouville_of_isLiouville F L a g h

-- Finite-dimensional algebraic extensions satisfy the Weak Liouville form.
example (F L : Type*) [Field F] [Field L] [CharZero F] [Differential F] [Differential L]
    [Algebra F L] [DifferentialAlgebra F L] [FiniteDimensional F L] (a : F) (g : L)
    (h : (algebraMap F L a) = g′) : HasWeakLiouvilleForm F F a :=
  weakLiouville_finiteDimensional F L a g h

-- Finite-dimensional extensions preserve non-elementarity in the Weak Liouville form.
example (F : Type*) [Field F] [Differential F] [CharZero F]
    (K : Type) [Field K] [Differential K] [Algebra F K] [DifferentialAlgebra F K]
    [FiniteDimensional F K] (f : F) (h : ¬ HasWeakLiouvilleForm F F f) :
    ¬ HasWeakLiouvilleForm F K f :=
  algebraicLiouvilleFrontier_finiteDimensional F K f h

-- For log monomials, the top coefficient sees only the base derivation.
example (K : Type*) [Field K] [Differential K] (c : K) (p : K[X]) :
    (logMonomialDeriv c p).coeff p.natDegree = (p.leadingCoeff)′ :=
  coeff_natDegree_logMonomialDeriv c p

end Restatements

#print axioms weakLiouville_descend
#print axioms weakLiouville_of_isLiouville
#print axioms weakLiouville_finiteDimensional
#print axioms not_weakElementary_finiteDimensional
#print axioms isLiouville_tower
#print axioms coeff_natDegree_logMonomialDeriv
#print axioms coeff_natDegree_expMonomialDeriv
#print axioms algebraicLiouvilleFrontier_form
#print axioms algebraicLiouvilleFrontier_finiteDimensional

end DeepWiki.SymbolicIntegration.LiouvilleStructure
