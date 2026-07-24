import DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner
import DeepWiki.SymbolicIntegration.Residues
import DeepWiki.SymbolicIntegration.Core.Polynomial.Diophantine
import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.RothsteinTrager.RtResultant
import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.RothsteinTrager.ResidueMultiplicity
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Radical.Basic

/-! # Gröbner basis of `⟨A − z·D', D⟩` and its normal position

For `A, D ∈ K[x]` with `D` monic squarefree and `deg A < deg D`, the ideal
`I = ⟨A − z·D', D⟩ ⊂ K[x, z]` has reduced Gröbner basis `{D, z − T}` (residue polynomial
`T = A·(D'⁻¹ mod D) mod D`). This file proves `I = ⟨D, z − T⟩`, that `{D, z − T}` is a Gröbner
basis, zero-dimensionality via `K[x, z] ⧸ I ≃ₐ K[x] ⧸ (D)`, radicality, and identifies the
`z`-elimination ideal `I ∩ K[z]` with `(R₁)`, `R₁` the squarefree part of the Rothstein–Trager
resultant. Convention: `z = X 0` is the dominant lex variable, `x = X 1`. -/

open MvPolynomial MonomialOrder Polynomial UniqueFactorizationMonoid

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

/-! ## The lift `K[x] → K[x, z]` placing `x` at variable `1` -/

/-- The `x`-lift `K[X] → MvPolynomial (Fin 2) K`, embedding `p` as a `z`-degree-`0` bivariate
polynomial in `x = X 1`. -/
noncomputable def liftX : K[X] →+* MvPolynomial (Fin 2) K :=
  ((finSuccEquiv K 1).symm.toRingHom.comp Polynomial.C).comp
    (mvPolynomialFinOneEquivPolynomial K).symm.toRingHom

/-- `lazardView (liftX p) = Polynomial.C (e⁻¹ p)`: the `K[x][z]` view of an `x`-only polynomial is
constant in `z`. -/
theorem lazardView_liftX (p : K[X]) :
    lazardView (liftX p) = Polynomial.C ((mvPolynomialFinOneEquivPolynomial K).symm p) := by
  unfold lazardView liftX
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  exact (finSuccEquiv K 1).apply_symm_apply _

/-- The `K[x]`-equiv sends `C a ↦ Polynomial.C a` and `X 0 ↦ Polynomial.X`. -/
theorem mvPolynomialFinOneEquivPolynomial_C (a : K) :
    mvPolynomialFinOneEquivPolynomial K (C a) = Polynomial.C a := by
  rw [mvPolynomialFinOneEquivPolynomial]
  exact ((finSuccEquiv K 0).trans (Polynomial.mapAlgEquiv (isEmptyAlgEquiv K (Fin 0)))).commutes a

/-- The `K[x]`-equiv sends the only variable `X 0` to `Polynomial.X`. -/
theorem mvPolynomialFinOneEquivPolynomial_X :
    mvPolynomialFinOneEquivPolynomial K (X 0) = Polynomial.X := by
  rw [mvPolynomialFinOneEquivPolynomial]
  show Polynomial.map (isEmptyAlgEquiv K (Fin 0)).toRingEquiv.toRingHom
    ((finSuccEquiv K 0) (X 0)) = _
  rw [finSuccEquiv_X_zero]
  simp

/-- `liftX` sends constants to constants. -/
@[simp] theorem liftX_C (a : K) : liftX (Polynomial.C a) = (C a : MvPolynomial (Fin 2) K) := by
  apply lazardView_injective
  rw [lazardView_liftX, ← mvPolynomialFinOneEquivPolynomial_C a, RingEquiv.symm_apply_apply,
    lazardView, finSuccEquiv_apply]
  simp

/-- `liftX` sends the univariate variable to the bivariate `x = X 1`. -/
@[simp] theorem liftX_X : liftX (Polynomial.X : K[X]) = X (1 : Fin 2) := by
  apply lazardView_injective
  rw [lazardView_liftX, ← mvPolynomialFinOneEquivPolynomial_X, RingEquiv.symm_apply_apply,
    lazardView]
  exact (finSuccEquiv_X_succ (j := 0)).symm

/-- `liftX` is injective (composition of the ring isos `finSuccEquiv.symm`, the `K[x]`-equiv, and
`Polynomial.C`). -/
theorem liftX_injective : Function.Injective (liftX (K := K)) := by
  intro p q hpq
  have h := congrArg lazardView hpq
  rw [lazardView_liftX, lazardView_liftX] at h
  exact (mvPolynomialFinOneEquivPolynomial K).symm.injective (Polynomial.C_injective h)

/-- `liftX p = 0` iff `p = 0`. -/
@[simp] theorem liftX_eq_zero_iff {p : K[X]} : liftX p = 0 ↔ p = 0 :=
  map_eq_zero_iff _ liftX_injective

/-- The `z`-degree of a lift is `0`: `liftX p` has no `z`-dependence (`degreeOf 0 (liftX p) = 0`). -/
theorem degreeOf_zero_liftX (p : K[X]) : degreeOf 0 (liftX p) = 0 := by
  rw [← natDegree_lazardView, lazardView_liftX, Polynomial.natDegree_C]

/-! ## The residue polynomial `T = A · (D'⁻¹ mod D) mod D` -/

variable (A D : K[X])

/-- The modular inverse of `D'` mod `D` (the `B` of `D'·B + D·C = 1`), valid when `D` is
squarefree. -/
noncomputable def dDerivInv : K[X] := (diophantineSolve (derivative D) D 1).1

/-- The residue polynomial `T = (A · B) mod D`, `B = D'⁻¹ mod D`: the unique `deg < deg D`
polynomial with `A ≡ T·D' (mod D)`. -/
noncomputable def residuePoly : K[X] := (A * dDerivInv D) % D

/-- Bézout identity for `D'` mod `D`: for `D` squarefree, `D'·B + D·C = 1` with `B = dDerivInv D`. -/
theorem dDeriv_mul_dDerivInv_add (hD : D.Separable) :
    derivative D * dDerivInv D + D * (diophantineSolve (derivative D) D 1).2 = 1 := by
  have hcop : IsCoprime (derivative D) D := ((separable_def D).mp hD).symm
  exact diophantineSolve_spec hcop 1

/-- `deg (residuePoly A D) < deg D` for `D ≠ 0` (it is a remainder mod `D`). -/
theorem residuePoly_degree_lt (hD : D ≠ 0) : (residuePoly A D).degree < D.degree :=
  Polynomial.degree_mod_lt _ hD

/-- `A·B ≡ T (mod D)`: `A · dDerivInv D − residuePoly A D` is divisible by `D`. -/
theorem A_mul_dDerivInv_sub_residuePoly_dvd :
    D ∣ A * dDerivInv D - residuePoly A D := by
  refine ⟨A * dDerivInv D / D, ?_⟩
  rw [residuePoly, eq_comm, ← sub_eq_iff_eq_add'.mpr (EuclideanDomain.div_add_mod
    (A * dDerivInv D) D).symm]
  ring

/-! ## The ideal `I = ⟨A − z·D', D⟩` and the Gröbner basis `GB₁ = {D, z − T}` -/

/-- The dominant lex variable `z = X 0`. -/
noncomputable abbrev zVar : MvPolynomial (Fin 2) K := X 0

/-- The generator `A − z·D'` of `I`, lifted to `K[x, z]`. -/
noncomputable def czGen : MvPolynomial (Fin 2) K := liftX A - zVar * liftX (derivative D)

/-- The Gröbner-basis element `z − T`, the reduced generator replacing `A − z·D'`. -/
noncomputable def zMinusResidue : MvPolynomial (Fin 2) K := zVar - liftX (residuePoly A D)

/-- The ideal `I = ⟨A − z·D', D⟩ ⊂ K[x, z]`. -/
noncomputable def czIdeal : Ideal (MvPolynomial (Fin 2) K) :=
  Ideal.span {czGen A D, liftX D}

/-- `liftX D ∈ I` (the second generator). -/
theorem liftX_D_mem_czIdeal : liftX D ∈ czIdeal A D :=
  Ideal.subset_span (by simp)

/-- `czGen A D = A − z·D' ∈ I` (the first generator). -/
theorem czGen_mem_czIdeal : czGen A D ∈ czIdeal A D :=
  Ideal.subset_span (by simp)

/-- `z − T ∈ I`. -/
theorem zMinusResidue_mem_czIdeal (hD : D.Separable) :
    zMinusResidue A D ∈ czIdeal A D := by
  set B := dDerivInv D with hB
  set C := (diophantineSolve (derivative D) D 1).2 with hC
  -- lift the Bézout identity `D'·B + D·C = 1`
  have hbez : liftX (derivative D) * liftX B + liftX D * liftX C = 1 := by
    rw [← map_mul, ← map_mul, ← map_add, dDeriv_mul_dDerivInv_add D hD, map_one]
  -- `A·B − T = D·Q`
  obtain ⟨Q, hQ⟩ := A_mul_dDerivInv_sub_residuePoly_dvd A D
  have hAB : liftX A * liftX B - liftX (residuePoly A D) = liftX D * liftX Q := by
    rw [← map_mul, ← map_sub, hQ, map_mul]
  -- `z − T = (−liftX B)·czGen + (z·liftX C + liftX Q)·liftX D`
  have hmul : zMinusResidue A D
      = (- liftX B) * czGen A D + (zVar * liftX C + liftX Q) * liftX D := by
    rw [zMinusResidue, czGen]
    linear_combination (- zVar) * hbez + hAB
  rw [hmul]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (czGen_mem_czIdeal A D))
    (Ideal.mul_mem_left _ _ (liftX_D_mem_czIdeal A D))

/-- `A − z·D' = −D'·(z − T) + R·D`: the original generator lies in `⟨D, z − T⟩`. -/
theorem czGen_eq_combination (hD : D.Separable) :
    ∃ R : K[X], czGen A D = (- liftX (derivative D)) * zMinusResidue A D + liftX R * liftX D := by
  -- `A·B − T = D·Q`
  obtain ⟨Q, hQ⟩ := A_mul_dDerivInv_sub_residuePoly_dvd A D
  refine ⟨A * (diophantineSolve (derivative D) D 1).2 + derivative D * Q, ?_⟩
  set C := (diophantineSolve (derivative D) D 1).2 with hC
  -- `A − D'·T = D·(A·C + D'·Q)` in `K[X]`
  have hkey : A - derivative D * residuePoly A D
      = D * (A * C + derivative D * Q) := by
    have hbz : derivative D * dDerivInv D + D * C = 1 := dDeriv_mul_dDerivInv_add D hD
    have hTB : residuePoly A D = A * dDerivInv D - D * Q := by linear_combination - hQ
    rw [hTB]; linear_combination (- A) * hbz
  -- lift to `K[x, z]`
  have hkeyL : liftX A - liftX (derivative D) * liftX (residuePoly A D)
      = liftX D * liftX (A * C + derivative D * Q) := by
    rw [← map_mul, ← map_sub, hkey, map_mul]
  rw [czGen, zMinusResidue]
  linear_combination hkeyL

/-- `I = ⟨D, z − T⟩`: the ideal is generated by `D` and `z − T`. -/
theorem czIdeal_eq_span_gb (hD : D.Separable) :
    czIdeal A D = Ideal.span {liftX D, zMinusResidue A D} := by
  apply le_antisymm
  · -- `I ⊆ ⟨D, z − T⟩`: both generators of `I` lie in `⟨D, z − T⟩`
    rw [czIdeal, Ideal.span_le]
    rintro f (rfl | rfl)
    · obtain ⟨R, hR⟩ := czGen_eq_combination A D hD
      rw [hR]
      exact Ideal.add_mem _
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
    · exact Ideal.subset_span (by simp)
  · -- `⟨D, z − T⟩ ⊆ I`: both `D` and `z − T` lie in `I`
    rw [Ideal.span_le]
    rintro f (rfl | rfl)
    · exact liftX_D_mem_czIdeal A D
    · exact zMinusResidue_mem_czIdeal A D hD

/-! ## `{D, z − T}` is a Gröbner basis
The leading monomials `x^(deg D)` (of `D`) and `z` (of `z − T`) are coprime. -/

/-- The "substitute `z := T`" map `K[x, z] → K[x]` (`X 0 ↦ residuePoly A D`, `X 1 ↦ X`): a left
inverse of `liftX` that kills `z − T`. -/
noncomputable def evalAtResidue : MvPolynomial (Fin 2) K →+* K[X] :=
  (MvPolynomial.aeval (![residuePoly A D, Polynomial.X] : Fin 2 → K[X])).toRingHom

/-- Substituting `z := T` sends `X 0` to `residuePoly A D`. -/
@[simp] theorem evalAtResidue_X0 : evalAtResidue A D (X 0) = residuePoly A D := by
  simp [evalAtResidue]

/-- Substituting `z := T` sends `X 1` to `Polynomial.X`. -/
@[simp] theorem evalAtResidue_X1 : evalAtResidue A D (X 1) = Polynomial.X := by
  simp [evalAtResidue]

/-- Substituting `z := T` preserves constants. -/
@[simp] theorem evalAtResidue_C (a : K) : evalAtResidue A D (C a) = Polynomial.C a := by
  simp [evalAtResidue]

/-- `evalAtResidue` is a left inverse of `liftX`: `evalAtResidue (liftX p) = p`. -/
@[simp] theorem evalAtResidue_liftX (p : K[X]) : evalAtResidue A D (liftX p) = p := by
  refine Polynomial.induction_on p (fun a => by simp) (fun p q hp hq => by simp [hp, hq])
    (fun n a _ => by simp [pow_succ])

/-- `evalAtResidue` kills `z − T`. -/
@[simp] theorem evalAtResidue_zMinusResidue : evalAtResidue A D (zMinusResidue A D) = 0 := by
  rw [zMinusResidue, map_sub, evalAtResidue_X0, evalAtResidue_liftX, sub_self]

/-! ### Leading monomials of the two basis elements (lex `z > x`) -/

/-- A `z`-free polynomial's leading monomial has index-`0` exponent `0`. -/
theorem lex_degree_liftX_apply_zero (p : K[X]) :
    (MonomialOrder.lex.degree (liftX p)) 0 = 0 := by
  rcases eq_or_ne (liftX p) 0 with hp0 | hp0
  · rw [hp0, MonomialOrder.degree_zero]; simp
  · rw [lex_degree_apply_zero hp0, degreeOf_zero_liftX]

/-- A `z`-free polynomial's leading monomial is `≺[lex] z`: its index-`0` exponent is `0`,
strictly below the index-`0 = 1` of `m.degree (X 0) = single 0 1`. -/
theorem lex_degree_liftX_lt_X0 (p : K[X]) :
    MonomialOrder.lex.degree (liftX p) ≺[MonomialOrder.lex] Finsupp.single (0 : Fin 2) 1 := by
  rw [MonomialOrder.lex_lt_iff, Finsupp.Lex.lt_iff]
  refine ⟨0, fun i hi => absurd hi (by simp), ?_⟩
  simp only [ofLex_toLex, lex_degree_liftX_apply_zero, Finsupp.single_eq_same]
  exact Nat.zero_lt_one

/-- The leading monomial of `z − T` is `z` (lex `z > x`): `m.degree (zMinusResidue) = single 0 1`. -/
theorem degree_zMinusResidue :
    MonomialOrder.lex.degree (zMinusResidue A D) = Finsupp.single (0 : Fin 2) 1 := by
  have hX0 : MonomialOrder.lex.degree (X (0 : Fin 2) : MvPolynomial (Fin 2) K)
      = Finsupp.single 0 1 := degree_X
  rw [zMinusResidue, MonomialOrder.degree_sub_of_lt (g := liftX (residuePoly A D)), hX0]
  rw [hX0]; exact lex_degree_liftX_lt_X0 (residuePoly A D)

/-- The leading monomial of `D` is `x^(deg D)` (lex `z > x`): for `D ≠ 0`,
`m.degree (liftX D) = single 1 (D.natDegree)`. -/
theorem degree_liftX_D (hD : D ≠ 0) :
    MonomialOrder.lex.degree (liftX D) = Finsupp.single (1 : Fin 2) D.natDegree := by
  have hne : liftX D ≠ 0 := by rwa [Ne, liftX_eq_zero_iff]
  refine Finsupp.ext fun i => ?_
  match i with
  | 0 =>
    rw [lex_degree_apply_zero hne, degreeOf_zero_liftX, Finsupp.single_eq_of_ne (by decide)]
  | 1 =>
    rw [lex_degree_apply_one hne, Finsupp.single_eq_same]
    have hlyc : leadingYCoeff (liftX D) = (mvPolynomialFinOneEquivPolynomial K).symm D := by
      rw [leadingYCoeff, lazardView_liftX, Polynomial.leadingCoeff_C]
    rw [hlyc, ← natDegree_mvPolynomialFinOneEquivPolynomial, RingEquiv.apply_symm_apply]

/-! ### `{D, z − T}` is a Gröbner basis -/

/-- A `z`-free bivariate polynomial is a lift: `degreeOf 0 f = 0 → f = liftX (evalAtResidue f)`. -/
theorem eq_liftX_of_degreeOf_zero {f : MvPolynomial (Fin 2) K} (hf : degreeOf 0 f = 0) :
    f = liftX (evalAtResidue A D f) := by
  -- `lazardView f` has `natDegree 0`, hence is a constant `C c`
  have hnat : (lazardView f).natDegree = 0 := by rw [natDegree_lazardView, hf]
  have hC : lazardView f = Polynomial.C ((lazardView f).coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero hnat
  -- so `f = liftX (e ((lazardView f).coeff 0))`
  have hflift : f = liftX (mvPolynomialFinOneEquivPolynomial K ((lazardView f).coeff 0)) := by
    apply lazardView_injective
    rw [lazardView_liftX, RingEquiv.symm_apply_apply]
    rw [hC]; simp
  rw [hflift, evalAtResidue_liftX]

/-- `evalAtResidue` sends `A − z·D'` to a multiple of `D` (`= A − T·D' = D·(A·C + D'·Q)`). -/
theorem evalAtResidue_czGen_mem_span (hD : D.Separable) :
    evalAtResidue A D (czGen A D) ∈ Ideal.span {D} := by
  rw [czGen, map_sub, map_mul, evalAtResidue_X0, evalAtResidue_liftX, evalAtResidue_liftX]
  -- `A − T·D' = D·(A·C + D'·Q)` (the `hkey` of section C)
  obtain ⟨Q, hQ⟩ := A_mul_dDerivInv_sub_residuePoly_dvd A D
  set C := (diophantineSolve (derivative D) D 1).2 with hC
  have hkey : A - residuePoly A D * derivative D = D * (A * C + derivative D * Q) := by
    have hbz : derivative D * dDerivInv D + D * C = 1 := dDeriv_mul_dDerivInv_add D hD
    have hTB : residuePoly A D = A * dDerivInv D - D * Q := by linear_combination - hQ
    rw [hTB]; linear_combination (- A) * hbz
  rw [hkey, Ideal.mem_span_singleton]
  exact Dvd.intro _ rfl

/-- `evalAtResidue` sends every element of `I = ⟨A − z·D', D⟩` to a multiple of `D`. -/
theorem evalAtResidue_mem_span_of_mem_czIdeal (hD : D.Separable)
    {f : MvPolynomial (Fin 2) K} (hf : f ∈ czIdeal A D) :
    evalAtResidue A D f ∈ Ideal.span {D} := by
  rw [czIdeal] at hf
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
  · rintro g (rfl | rfl)
    · exact evalAtResidue_czGen_mem_span A D hD
    · rw [evalAtResidue_liftX]; exact Ideal.mem_span_singleton_self D
  · simp
  · intro x y _ _ hx hy; rw [map_add]; exact Ideal.add_mem _ hx hy
  · intro a x _ hx; rw [smul_eq_mul, map_mul]; exact Ideal.mul_mem_left _ _ hx

/-- `{D, z − T}` is a Gröbner basis of `I` for the lex ordering `z > x`. -/
theorem isGroebnerBasis_gb (hD : D.Separable) (hD0 : D ≠ 0) :
    IsGroebnerBasis MonomialOrder.lex (czIdeal A D) {liftX D, zMinusResidue A D} := by
  set m := MonomialOrder.lex (σ := Fin 2)
  -- the two basis elements lie in `I`, with unit (monic) leading coefficients
  have hmem : ∀ b ∈ ({liftX D, zMinusResidue A D} : Set (MvPolynomial (Fin 2) K)), b ∈ czIdeal A D := by
    rintro b (rfl | rfl)
    · exact liftX_D_mem_czIdeal A D
    · exact zMinusResidue_mem_czIdeal A D hD
  refine isGroebnerBasis_of_exists_leadingMonomial_le hmem ?_ ?_
  · -- unit leading coefficients (both basis elements are nonzero over a field)
    rintro b (rfl | rfl)
    · exact m.isUnit_leadingCoeff.mpr (by rwa [Ne, liftX_eq_zero_iff])
    · refine m.isUnit_leadingCoeff.mpr (fun h => ?_)
      have := degree_zMinusResidue A D
      rw [h, MonomialOrder.degree_zero] at this
      exact absurd this.symm (by simp)
  · -- divisibility of the leading monomial
    intro f hfI hf0
    by_cases hz : 1 ≤ (m.degree f) 0
    · -- `z ∣ LM(f)`
      refine ⟨zMinusResidue A D, by simp, ?_⟩
      rw [degree_zMinusResidue]
      intro i
      match i with
      | 0 => rwa [Finsupp.single_eq_same]
      | 1 => rw [Finsupp.single_eq_of_ne (by decide)]; exact Nat.zero_le _
    · -- `f` is `z`-free; substitute `z := T`
      have hz' : (m.degree f) 0 = 0 := by omega
      have hzdeg : degreeOf 0 f = 0 := by
        rw [← lex_degree_apply_zero hf0]; exact hz'
      have hflift : f = liftX (evalAtResidue A D f) := eq_liftX_of_degreeOf_zero A D hzdeg
      have hp0 : evalAtResidue A D f ≠ 0 := by
        intro h; rw [h, map_zero] at hflift; exact hf0 hflift
      -- `D ∣ evalAtResidue f`
      have hdvd : D ∣ evalAtResidue A D f := by
        have := evalAtResidue_mem_span_of_mem_czIdeal A D hD hfI
        rwa [Ideal.mem_span_singleton] at this
      refine ⟨liftX D, by simp, ?_⟩
      rw [degree_liftX_D D hD0]
      conv_rhs => rw [hflift]
      rw [degree_liftX_D _ hp0]
      intro i
      match i with
      | 0 => simp
      | 1 =>
        rw [Finsupp.single_eq_same, Finsupp.single_eq_same]
        exact Polynomial.natDegree_le_of_dvd hdvd hp0

/-! ## Zero-dimensionality of `I`
Eliminating `z = T` gives `K[x, z] ⧸ I ≃ₐ K[x] ⧸ (D)`, a finite `K`-module. -/

/-- `f − liftX (evalAtResidue f) ∈ I` for every `f`: reduction of `f` modulo `I` by `z := T`. -/
theorem sub_liftX_evalAtResidue_mem_czIdeal (hD : D.Separable)
    (f : MvPolynomial (Fin 2) K) : f - liftX (evalAtResidue A D f) ∈ czIdeal A D := by
  induction f using MvPolynomial.induction_on with
  | C a => rw [evalAtResidue_C, liftX_C, sub_self]; exact Ideal.zero_mem _
  | add p q hp hq =>
    rw [map_add, map_add]
    have : p + q - (liftX (evalAtResidue A D p) + liftX (evalAtResidue A D q))
        = (p - liftX (evalAtResidue A D p)) + (q - liftX (evalAtResidue A D q)) := by ring
    rw [this]; exact Ideal.add_mem _ hp hq
  | mul_X p n hp =>
    -- `p·Xn − liftX(eval(p·Xn)) = (p − liftX(eval p))·Xn + liftX(eval p)·(Xn − liftX(eval Xn))`
    have hXn : X n - liftX (evalAtResidue A D (X n)) ∈ czIdeal A D := by
      match n with
      | 0 => rw [evalAtResidue_X0]; exact zMinusResidue_mem_czIdeal A D hD
      | 1 => rw [evalAtResidue_X1, liftX_X, sub_self]; exact Ideal.zero_mem _
    rw [map_mul, map_mul]
    have hsplit : p * X n - liftX (evalAtResidue A D p) * liftX (evalAtResidue A D (X n))
        = (p - liftX (evalAtResidue A D p)) * X n
          + liftX (evalAtResidue A D p) * (X n - liftX (evalAtResidue A D (X n))) := by ring
    rw [hsplit]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_left _ _ hXn)

/-- `f ∈ I ⟺ D ∣ evalAtResidue f`: `I` is the kernel of `mod D ∘ evalAtResidue`. -/
theorem mem_czIdeal_iff_dvd_evalAtResidue (hD : D.Separable)
    {f : MvPolynomial (Fin 2) K} : f ∈ czIdeal A D ↔ D ∣ evalAtResidue A D f := by
  constructor
  · intro hf
    have := evalAtResidue_mem_span_of_mem_czIdeal A D hD hf
    rwa [Ideal.mem_span_singleton] at this
  · intro ⟨g, hg⟩
    -- `f = (f − liftX(eval f)) + liftX(D·g) = (…) + liftX D · liftX g ∈ I`
    have h1 : f - liftX (evalAtResidue A D f) ∈ czIdeal A D :=
      sub_liftX_evalAtResidue_mem_czIdeal A D hD f
    have h2 : liftX (evalAtResidue A D f) ∈ czIdeal A D := by
      rw [hg, map_mul]
      exact Ideal.mul_mem_right _ _ (liftX_D_mem_czIdeal A D)
    have : f = (f - liftX (evalAtResidue A D f)) + liftX (evalAtResidue A D f) := by ring
    rw [this]; exact Ideal.add_mem _ h1 h2

/-- The residue `K`-algebra map `K[x, z] →ₐ[K] K[x] ⧸ (D)`: substitute `z := T`, then reduce
`mod D`. -/
noncomputable def evalAtResidueQuot : MvPolynomial (Fin 2) K →ₐ[K] K[X] ⧸ Ideal.span {D} :=
  (Ideal.Quotient.mkₐ K (Ideal.span {D})).comp
    (MvPolynomial.aeval (![residuePoly A D, Polynomial.X] : Fin 2 → K[X]))

/-- `evalAtResidueQuot` is quotient reduction of `evalAtResidue`. -/
@[simp] theorem evalAtResidueQuot_apply (f : MvPolynomial (Fin 2) K) :
    evalAtResidueQuot A D f = Ideal.Quotient.mk (Ideal.span {D}) (evalAtResidue A D f) := rfl

/-- `evalAtResidueQuot` is surjective: `liftX p ↦ mk p`, and `mk` is surjective. -/
theorem evalAtResidueQuot_surjective : Function.Surjective (evalAtResidueQuot A D) := by
  intro y
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨liftX p, by rw [evalAtResidueQuot_apply, evalAtResidue_liftX]⟩

/-- The kernel of `evalAtResidueQuot` is exactly `I`. -/
theorem ker_evalAtResidueQuot (hD : D.Separable) :
    RingHom.ker (evalAtResidueQuot A D).toRingHom = czIdeal A D := by
  ext f
  rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, evalAtResidueQuot_apply,
    Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton,
    ← mem_czIdeal_iff_dvd_evalAtResidue A D hD]

/-- The eliminating iso `K[x, z] ⧸ I ≃ₐ[K] K[x] ⧸ (D)`, substituting `z = T`. -/
noncomputable def czIdealQuotEquiv (hD : D.Separable) :
    (MvPolynomial (Fin 2) K ⧸ czIdeal A D) ≃ₐ[K] K[X] ⧸ Ideal.span {D} :=
  (Ideal.quotientEquivAlgOfEq K (ker_evalAtResidueQuot A D hD).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (evalAtResidueQuot_surjective A D))

/-- Zero-dimensionality of `I`: for `D` monic squarefree, `K[x, z] ⧸ ⟨A − z·D', D⟩` is a finite
`K`-module. -/
theorem finite_quotient_czIdeal (hM : D.Monic) (hD : D.Separable) :
    Module.Finite K (MvPolynomial (Fin 2) K ⧸ czIdeal A D) :=
  haveI : Module.Finite K (K[X] ⧸ Ideal.span {D}) := hM.finite_adjoinRoot (R := K)
  Module.Finite.equiv (czIdealQuotEquiv A D hD).symm.toLinearEquiv

/-! ## `I` is radical (maximality w.r.t. its zero set)
For `D` separable, `K[x, z] ⧸ I` is reduced, so `I = √I`. -/

/-- For `D` separable, the quotient `K[X] ⧸ (D)` is reduced. -/
theorem isReduced_quotient_span_singleton (hD : D.Separable) :
    IsReduced (K[X] ⧸ Ideal.span {D}) :=
  (Ideal.isRadical_iff_quotient_reduced _).mp
    (isRadical_iff_span_singleton.mp hD.squarefree.isRadical)

/-- `K[x, z] ⧸ I` is reduced, transported from `K[X] ⧸ (D)` across `czIdealQuotEquiv`. -/
theorem isReduced_quotient_czIdeal (hD : D.Separable) :
    IsReduced (MvPolynomial (Fin 2) K ⧸ czIdeal A D) :=
  haveI := isReduced_quotient_span_singleton D hD
  isReduced_of_injective (czIdealQuotEquiv A D hD).toRingHom
    (czIdealQuotEquiv A D hD).injective

/-- For `D` separable, `I = ⟨A − z·D', D⟩` is a radical ideal (`I = √I`). -/
theorem czIdeal_isRadical (hD : D.Separable) : (czIdeal A D).IsRadical :=
  (Ideal.isRadical_iff_quotient_reduced _).mpr (isReduced_quotient_czIdeal A D hD)

/-- Over an algebraically closed `K`, `I = ⟨A − z·D', D⟩` equals the vanishing ideal of its zero
set, `I = I(V(I))`. -/
theorem czIdeal_eq_vanishingIdeal_zeroLocus [IsAlgClosed K] (hD : D.Separable) :
    vanishingIdeal K (zeroLocus K (czIdeal A D)) = czIdeal A D := by
  rw [vanishingIdeal_zeroLocus_eq_radical]
  exact (czIdeal_isRadical A D hD).radical

/-! ### The zeros of `I` and the residue value
The zeros of `I` are `(α, A(α)/D'(α))` over the distinct roots `α` of `D`. -/

/-- For a root `α` of a squarefree `D`, `T(α) = A(α)/D'(α)` (the Rothstein–Trager residue). -/
theorem eval_residuePoly_of_isRoot (hD : D.Separable) {α : K} (hα : D.IsRoot α) :
    (residuePoly A D).eval α = A.eval α / (derivative D).eval α := by
  have hDα : D.eval α = 0 := hα
  have hD'α : (derivative D).eval α ≠ 0 := by
    have := hD.eval₂_derivative_ne_zero (RingHom.id K)
      (by simpa [Polynomial.eval₂_eq_eval_map, Polynomial.map_id] using hα)
    simpa [Polynomial.eval₂_eq_eval_map, Polynomial.map_id] using this
  -- `D'(α)·B(α) = 1` (from `D'·B + D·C = 1` and `D(α) = 0`)
  have hBα : (derivative D).eval α * (dDerivInv D).eval α = 1 := by
    have h := congrArg (Polynomial.eval α) (dDeriv_mul_dDerivInv_add D hD)
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, hDα,
      Polynomial.eval_one] at h
    linear_combination h
  -- `A·B = D·Q + T`, so `T(α) = A(α)·B(α)` (since `D(α) = 0`)
  obtain ⟨Q, hQ⟩ := A_mul_dDerivInv_sub_residuePoly_dvd A D
  have hTα : (residuePoly A D).eval α = A.eval α * (dDerivInv D).eval α := by
    have h := congrArg (Polynomial.eval α) hQ
    rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul, hDα,
      zero_mul] at h
    linear_combination - h
  rw [hTα, eq_div_iff hD'α]
  linear_combination (A.eval α) * hBα

/-- Normal position: the roots of a separable `D` are distinct. -/
theorem nodup_roots_of_separable (hD : D.Separable) : D.roots.Nodup :=
  Polynomial.nodup_roots hD

/-- The two leading monomials are coprime: `x^(deg D) ⊓ z = 0` (disjoint exponent supports),
the structural reason `GB₁`'s single S-polynomial reduces to zero (Buchberger's first criterion). -/
example (D : K[X]) : (Finsupp.single (1 : Fin 2) D.natDegree) ⊓ (Finsupp.single (0 : Fin 2) 1) = 0 := by
  ext i; match i with | 0 => simp | 1 => simp

/-! ## The `z`-elimination ideal `I ∩ K[z] = (R₁)`
Over an algebraically closed field, `I ∩ K[z]` is generated by
`R₁ = ∏_{distinct residues}(z − a)`, the squarefree part of the Rothstein–Trager resultant. -/

/-- The `z`-embedding `K[z] → K[x, z]`, `z ↦ X 0`; the elimination ideal `I ∩ K[z]` is the comap
of `I` along it. -/
noncomputable def polyZ : K[X] →+* MvPolynomial (Fin 2) K :=
  (Polynomial.aeval (zVar : MvPolynomial (Fin 2) K)).toRingHom

/-- The `z`-embedding sends `Polynomial.X` to `zVar`. -/
@[simp] theorem polyZ_X : polyZ (Polynomial.X : K[X]) = zVar := by simp [polyZ]

/-- The `z`-embedding preserves constants. -/
@[simp] theorem polyZ_C (a : K) : polyZ (Polynomial.C a) = (C a : MvPolynomial (Fin 2) K) := by
  simp [polyZ, MvPolynomial.algebraMap_eq]

/-- Evaluating a lift reads off the `x`-coordinate: `aeval x (liftX p) = p.eval (x 1)`. -/
theorem aeval_liftX (x : Fin 2 → K) (p : K[X]) :
    MvPolynomial.aeval x (liftX p) = p.eval (x 1) := by
  refine Polynomial.induction_on p (fun a => by simp)
    (fun p q hp hq => by rw [map_add, map_add, hp, hq, Polynomial.eval_add])
    (fun n a _ => by simp [pow_succ])

/-- Evaluating a `z`-embedding reads off the `z`-coordinate: `aeval x (polyZ p) = p.eval (x 0)`. -/
theorem aeval_polyZ (x : Fin 2 → K) (p : K[X]) :
    MvPolynomial.aeval x (polyZ p) = p.eval (x 0) := by
  refine Polynomial.induction_on p (fun a => by simp [polyZ_C])
    (fun p q hp hq => by rw [map_add, map_add, hp, hq, Polynomial.eval_add])
    (fun n a _ => by simp [pow_succ, polyZ_C, zVar])

/-! ### The zero set `V(I) = {(residue, root)}` -/

/-- `aeval x` evaluated on the first generator `A − z·D'` reads `A(x₁) − x₀·D'(x₁)`. -/
theorem aeval_czGen (x : Fin 2 → K) :
    MvPolynomial.aeval x (czGen A D) = A.eval (x 1) - x 0 * (derivative D).eval (x 1) := by
  rw [czGen, map_sub, map_mul, aeval_liftX, aeval_liftX]
  simp [zVar]

/-- `x ∈ V(I)` iff `D(x₁) = 0` and `A(x₁) = x₀·D'(x₁)` (`x₁` a root of `D`, `x₀` its residue). -/
theorem mem_zeroLocus_czIdeal_iff (x : Fin 2 → K) :
    x ∈ zeroLocus K (czIdeal A D) ↔
      D.eval (x 1) = 0 ∧ A.eval (x 1) = x 0 * (derivative D).eval (x 1) := by
  rw [czIdeal, zeroLocus_span]
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · have := hx (liftX D) (by simp); rwa [aeval_liftX] at this
    · have := hx (czGen A D) (by simp); rw [aeval_czGen] at this; exact sub_eq_zero.mp this
  · rintro ⟨hD0, hA0⟩ p (rfl | rfl)
    · rw [aeval_czGen, hA0, sub_self]
    · rw [aeval_liftX, hD0]

/-- At a point of `V(I)` with `D` separable, `x₀ = A(x₁)/D'(x₁)` is the Rothstein–Trager residue. -/
theorem zeroLocus_coord_eq_residue (hD : D.Separable) {x : Fin 2 → K}
    (hx : x ∈ zeroLocus K (czIdeal A D)) :
    x 0 = A.eval (x 1) / (derivative D).eval (x 1) := by
  rw [mem_zeroLocus_czIdeal_iff] at hx
  have hD'0 : (derivative D).eval (x 1) ≠ 0 := by
    have := hD.eval₂_derivative_ne_zero (RingHom.id K)
      (by simpa [Polynomial.eval₂_eq_eval_map, Polynomial.map_id] using hx.1)
    simpa [Polynomial.eval₂_eq_eval_map, Polynomial.map_id] using this
  rw [eq_div_iff hD'0, hx.2]

/-- Over an algebraically closed field with `D` separable, `V(I)` is exactly `(A(α)/D'(α), α)` for
the roots `α` of `D`. -/
theorem mem_zeroLocus_czIdeal_iff_isRoot (hD : D.Separable) (x : Fin 2 → K) :
    x ∈ zeroLocus K (czIdeal A D) ↔
      D.IsRoot (x 1) ∧ x 0 = A.eval (x 1) / (derivative D).eval (x 1) := by
  constructor
  · intro hx
    exact ⟨(mem_zeroLocus_czIdeal_iff A D x).mp hx |>.1, zeroLocus_coord_eq_residue A D hD hx⟩
  · rintro ⟨hroot, hres⟩
    have hD'0 : (derivative D).eval (x 1) ≠ 0 := by
      have := hD.eval₂_derivative_ne_zero (RingHom.id K)
        (by simpa [Polynomial.eval₂_eq_eval_map, Polynomial.map_id] using hroot)
      simpa [Polynomial.eval₂_eq_eval_map, Polynomial.map_id] using this
    rw [mem_zeroLocus_czIdeal_iff]
    exact ⟨hroot, by rw [hres, div_mul_cancel₀ _ hD'0]⟩

/-! ### The `z`-elimination ideal and `R₁` -/

/-- The `z`-elimination ideal `I ∩ K[z]`, the pullback of `I` along `polyZ`. -/
noncomputable def elimZ : Ideal K[X] := Ideal.comap polyZ (czIdeal A D)

/-- Membership in `elimZ A D` is membership of `polyZ p` in `czIdeal A D`. -/
@[simp] theorem mem_elimZ_iff {p : K[X]} : p ∈ elimZ A D ↔ polyZ p ∈ czIdeal A D := Iff.rfl

open scoped Classical in
/-- `R₁ = ∏_{a ∈ distinct roots of R}(z − a)`, the monic squarefree part (radical) of the
Rothstein–Trager resultant `R = res_x(A − z·D', D)`, generating `I ∩ K[z]`. -/
noncomputable def czichowskiR1 : K[X] :=
  (rtResultant A D).roots.toFinset.prod (fun a => Polynomial.X - Polynomial.C a)

/-- `R₁` is monic (a product of monic linear factors `z − a`). -/
theorem czichowskiR1_monic : (czichowskiR1 A D).Monic := by
  classical
  exact monic_prod_of_monic _ _ (fun a _ => monic_X_sub_C a)

/-- `R₁ ≠ 0`. -/
theorem czichowskiR1_ne_zero : czichowskiR1 A D ≠ 0 := (czichowskiR1_monic A D).ne_zero

open scoped Classical in
/-- `R₁` is squarefree (a product of distinct linear factors). -/
theorem czichowskiR1_squarefree : Squarefree (czichowskiR1 A D) := by
  classical
  rw [czichowskiR1]
  exact (separable_prod_X_sub_C_iff' (f := id)).mpr (fun a _ b _ h => h) |>.squarefree

open scoped Classical in
/-- `a` is a root of `R₁` iff it is a root of the resultant `R` (same root set). -/
theorem isRoot_czichowskiR1_iff {a : K} :
    (czichowskiR1 A D).IsRoot a ↔ a ∈ (rtResultant A D).roots.toFinset := by
  classical
  rw [← Polynomial.mem_roots (czichowskiR1_ne_zero A D), czichowskiR1,
    Polynomial.roots_prod_X_sub_C, Finset.mem_val]

/-! ### `I ∩ K[z] = (R₁)` -/

open scoped Classical in
/-- Each root `a` of the resultant `R` is realized by a zero `(a, α)` of `I`. -/
theorem exists_mem_zeroLocus_of_root_rtResultant [IsAlgClosed K] (hD : D.Separable)
    (hA : A.natDegree < D.natDegree) {a : K} (ha : a ∈ (rtResultant A D).roots.toFinset) :
    ∃ x : Fin 2 → K, x ∈ zeroLocus K (czIdeal A D) ∧ x 0 = a := by
  classical
  rw [rtResultant_roots_toFinset A D hD hA, Finset.mem_image] at ha
  obtain ⟨α, hα, hres⟩ := ha
  refine ⟨![a, α], ?_, by simp⟩
  rw [mem_zeroLocus_czIdeal_iff_isRoot A D hD]
  refine ⟨Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp hα), ?_⟩
  simpa using hres.symm

open scoped Classical in
/-- `R₁ ∈ I ∩ K[z]`: the squarefree part of the resultant lies in the elimination ideal. -/
theorem czichowskiR1_mem_elimZ [IsAlgClosed K] (hD : D.Separable)
    (hA : A.natDegree < D.natDegree) : czichowskiR1 A D ∈ elimZ A D := by
  classical
  rw [mem_elimZ_iff, ← czIdeal_eq_vanishingIdeal_zeroLocus A D hD, mem_vanishingIdeal_iff]
  intro x hx
  rw [aeval_polyZ]
  -- `x 0` is a residue, hence a root of `R`, hence a root of `R₁`
  have hroot : D.IsRoot (x 1) := (mem_zeroLocus_czIdeal_iff_isRoot A D hD x).mp hx |>.1
  have hres : x 0 = A.eval (x 1) / (derivative D).eval (x 1) :=
    (mem_zeroLocus_czIdeal_iff_isRoot A D hD x).mp hx |>.2
  have hmem : x 0 ∈ (rtResultant A D).roots.toFinset := by
    rw [rtResultant_roots_toFinset A D hD hA, Finset.mem_image]
    exact ⟨x 1, Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hD.ne_zero).mpr hroot), hres.symm⟩
  exact (isRoot_czichowskiR1_iff A D).mpr hmem

open scoped Classical in
/-- `I ∩ K[z] ⊆ (R₁)`: every `p ∈ I ∩ K[z]` is a multiple of `R₁`. -/
theorem elimZ_le_span_czichowskiR1 [IsAlgClosed K] (hD : D.Separable)
    (hA : A.natDegree < D.natDegree) : elimZ A D ≤ Ideal.span {czichowskiR1 A D} := by
  classical
  intro p hp
  rw [Ideal.mem_span_singleton]
  rw [mem_elimZ_iff, ← czIdeal_eq_vanishingIdeal_zeroLocus A D hD, mem_vanishingIdeal_iff] at hp
  -- `p` vanishes at every distinct residue `a`
  have hpa : ∀ a ∈ (rtResultant A D).roots.toFinset, p.eval a = 0 := by
    intro a ha
    obtain ⟨x, hx, hx0⟩ := exists_mem_zeroLocus_of_root_rtResultant A D hD hA ha
    have := hp x hx
    rwa [aeval_polyZ, hx0] at this
  -- each `z − a` divides `p`; the distinct factors are pairwise coprime, so `R₁ ∣ p`
  rw [czichowskiR1]
  refine Finset.prod_dvd_of_coprime
    (fun a _ b _ hab => (pairwise_coprime_X_sub_C Function.injective_id hab)) ?_
  intro a ha
  exact (Polynomial.dvd_iff_isRoot).mpr (hpa a ha)

open scoped Classical in
/-- `I ∩ K[z] = (R₁)`: over an algebraically closed field, for `D` monic separable and
`deg A < deg D`, the `z`-elimination ideal of `I` is generated by `R₁`. -/
theorem elimZ_eq_span_czichowskiR1 [IsAlgClosed K] (hD : D.Separable)
    (hA : A.natDegree < D.natDegree) :
    elimZ A D = Ideal.span {czichowskiR1 A D} := by
  refine le_antisymm (elimZ_le_span_czichowskiR1 A D hD hA) ?_
  rw [Ideal.span_le, Set.singleton_subset_iff]
  exact SetLike.mem_coe.mpr (czichowskiR1_mem_elimZ A D hD hA)

/-! ### `R₁ = radical(resultant)`
Over an algebraically closed field, `R₁` equals Mathlib's `radical` of the resultant. -/

open scoped Classical in
/-- The radical of a nonzero polynomial over a field is monic. -/
theorem monic_radical {p : K[X]} (hp : p ≠ 0) : (radical p).Monic := by
  classical
  rw [radical]
  refine monic_prod_of_monic _ _ (fun r hr => ?_)
  rw [UniqueFactorizationMonoid.mem_primeFactors,
    Polynomial.mem_normalizedFactors_iff hp] at hr
  exact hr.2.1

open scoped Classical in
/-- Over `[IsAlgClosed K]`, if `q ≠ 0` and every root of `p` is a root of `q`, then `radical p ∣ q`. -/
theorem radical_dvd_of_roots_subset [IsAlgClosed K] {p q : K[X]} (hq : q ≠ 0)
    (hsub : ∀ a, p.IsRoot a → q.IsRoot a) : radical p ∣ q := by
  classical
  rw [UniqueFactorizationMonoid.radical_dvd_iff_primeFactors_subset hq]
  intro r hr
  rw [UniqueFactorizationMonoid.mem_primeFactors] at hr ⊢
  -- `r` is irreducible, monic, and `r ∣ p`
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [UniqueFactorizationMonoid.normalizedFactors_zero] at hr
    exact absurd hr (Multiset.notMem_zero r)
  rw [Polynomial.mem_normalizedFactors_iff hp0] at hr
  obtain ⟨hirr, hmon, hrp⟩ := hr
  -- alg-closed: `r` has degree 1, so `r = X − C a` with `a` a root of `r`, hence of `p`
  have hdeg : r.degree = 1 := (IsAlgClosed.splits r).degree_eq_one_of_irreducible hirr
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root r (by rw [hdeg]; decide)
  have harp : p.IsRoot a := by
    obtain ⟨s, rfl⟩ := hrp
    rw [Polynomial.IsRoot, Polynomial.eval_mul, ha, zero_mul]
  -- `a` is a root of `q`, so `X − C a ∣ q`; `r` is associated to `X − C a`, so `r ∣ q`
  have hraq : r ∣ q := by
    have hXa : (Polynomial.X - Polynomial.C a) ∣ r := Polynomial.dvd_iff_isRoot.mpr ha
    have hass : Associated r (Polynomial.X - Polynomial.C a) :=
      (Polynomial.associated_of_dvd_of_natDegree_le hXa hirr.ne_zero
        (by rw [Polynomial.natDegree_X_sub_C,
          Polynomial.natDegree_eq_of_degree_eq_some hdeg]; exact le_refl _)).symm
    exact hass.dvd.trans (Polynomial.dvd_iff_isRoot.mpr (hsub a harp))
  rw [Polynomial.mem_normalizedFactors_iff hq]
  exact ⟨hirr, hmon, hraq⟩

open scoped Classical in
/-- Over an algebraically closed field, `R₁ = radical (rtResultant A D)`, the squarefree part of the
Rothstein–Trager resultant. -/
theorem czichowskiR1_eq_radical_rtResultant [IsAlgClosed K] :
    czichowskiR1 A D = radical (rtResultant A D) := by
  classical
  by_cases hR0 : rtResultant A D = 0
  · -- degenerate: `R = 0` ⟹ no roots ⟹ `R₁ = 1 = radical 0`
    rw [hR0, radical_zero, czichowskiR1]
    simp [hR0]
  -- both monic; show they are associated, then equal
  have hR1dvd : czichowskiR1 A D ∣ rtResultant A D := by
    rw [czichowskiR1]; exact czichowskiR1_dvd_rtResultant A D
  -- `R₁ ∣ radical R` (R₁ radical, R ≠ 0)
  have h1 : czichowskiR1 A D ∣ radical (rtResultant A D) :=
    (UniqueFactorizationMonoid.dvd_radical_iff
      (czichowskiR1_squarefree A D).isRadical hR0).mpr hR1dvd
  -- `radical R ∣ R₁`: every root of `R` is a root of `R₁` (same root set)
  have h2 : radical (rtResultant A D) ∣ czichowskiR1 A D :=
    radical_dvd_of_roots_subset (czichowskiR1_ne_zero A D)
      (fun a ha => (isRoot_czichowskiR1_iff A D).mpr
        (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hR0).mpr ha)))
  -- associated + both monic ⟹ equal
  exact Polynomial.eq_of_monic_of_associated (czichowskiR1_monic A D) (monic_radical hR0)
    (associated_of_dvd_dvd h1 h2)

end DeepWiki.SymbolicIntegration
