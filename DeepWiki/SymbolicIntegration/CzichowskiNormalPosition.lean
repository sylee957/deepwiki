import DeepWiki.SymbolicIntegration.GroebnerBasis
import DeepWiki.SymbolicIntegration.Residues
import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms

/-! # Czichowski's Gröbner basis `GB₁` of `⟨A − z·D', D⟩` (Bronstein §2.6 / Czichowski Lemma 2.1)

Czichowski (1995, *A Note on Gröbner Bases and Integration of Rational Functions*) studies the
ideal `I = ⟨A(x) − z·D'(x), D(x)⟩ ⊂ K[x, z]` for `A, D ∈ K[x]` with `D` monic squarefree,
`deg A < deg D`, `gcd(A, D) = 1`. Lemma 2.1 asserts `I` is zero-dimensional, in normal position
w.r.t. `x`, and maximal w.r.t. its zero set; the concrete engine is the **reduced Gröbner basis**
`GB₁ = {D(x), z − T(x)}` w.r.t. the p.l. ordering `z > x`, where `T = A·(D'⁻¹ mod D) mod D` is the
*residue polynomial*.

Convention (matching `finSuccEquiv` / the Lazard bridge in `GroebnerBasis.lean`): `z = X 0` is the
dominant lex variable (`MonomialOrder.lex` on `Fin 2` makes index `0` most significant), `x = X 1`.
So `lazardView` reads `f` as a polynomial in `z` over `K[x] ≃ MvPolynomial (Fin 1) K`.

This file builds the concrete core: the residue polynomial `T` (`liftX`-ed into two variables),
`z − T ∈ I`, `I = ⟨D, z − T⟩`, and that `{D, z − T}` is a Gröbner basis (its leading monomials
`x^(deg D)` and `z` are coprime). The variety analysis (zero-dimensionality, normal position,
maximality) is the genuine research wall and is left to the §2.6 catalog marker. -/

open MvPolynomial MonomialOrder Polynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

/-! ## The lift `K[x] → K[x, z]` placing `x` at variable `1` -/

/-- **The `x`-lift** `K[X] → MvPolynomial (Fin 2) K`: read `K[X] ≃ MvPolynomial (Fin 1) K` (var `x`),
embed as a `z`-constant via `Polynomial.C`, and pull back through `finSuccEquiv` (which pulls out
`z = X 0`). The result is a `z`-degree-`0` bivariate polynomial in `x = X 1`. -/
noncomputable def liftX : K[X] →+* MvPolynomial (Fin 2) K :=
  ((finSuccEquiv K 1).symm.toRingHom.comp Polynomial.C).comp
    (mvPolynomialFinOneEquivPolynomial K).symm.toRingHom

/-- **`lazardView` of a lift is a `z`-constant**: `lazardView (liftX p) = Polynomial.C (e⁻¹ p)`,
the `K[x][z]` view of an `x`-only polynomial is the constant polynomial in `z`. -/
theorem lazardView_liftX (p : K[X]) :
    lazardView (liftX p) = Polynomial.C ((mvPolynomialFinOneEquivPolynomial K).symm p) := by
  unfold lazardView liftX
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  exact (finSuccEquiv K 1).apply_symm_apply _

/-- The `K[x]`-equiv sends `C a ↦ Polynomial.C a` and `X 0 ↦ Polynomial.X`. -/
theorem mvPolynomialFinOneEquivPolynomial_C (a : K) :
    mvPolynomialFinOneEquivPolynomial K (C a) = Polynomial.C a := by
  rw [mvPolynomialFinOneEquivPolynomial]
  show Polynomial.map (isEmptyAlgEquiv K (Fin 0)).toRingEquiv.toRingHom
    ((finSuccEquiv K 0) (C a)) = _
  rw [finSuccEquiv_apply]
  simp

theorem mvPolynomialFinOneEquivPolynomial_X :
    mvPolynomialFinOneEquivPolynomial K (X 0) = Polynomial.X := by
  rw [mvPolynomialFinOneEquivPolynomial]
  show Polynomial.map (isEmptyAlgEquiv K (Fin 0)).toRingEquiv.toRingHom
    ((finSuccEquiv K 0) (X 0)) = _
  rw [finSuccEquiv_X_zero]
  simp

@[simp] theorem liftX_C (a : K) : liftX (Polynomial.C a) = (C a : MvPolynomial (Fin 2) K) := by
  apply lazardView_injective
  rw [lazardView_liftX, ← mvPolynomialFinOneEquivPolynomial_C a, RingEquiv.symm_apply_apply,
    lazardView, finSuccEquiv_apply]
  simp

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

@[simp] theorem liftX_eq_zero_iff {p : K[X]} : liftX p = 0 ↔ p = 0 :=
  map_eq_zero_iff _ liftX_injective

/-- The `z`-degree of a lift is `0`: `liftX p` has no `z`-dependence (`degreeOf 0 (liftX p) = 0`). -/
theorem degreeOf_zero_liftX (p : K[X]) : degreeOf 0 (liftX p) = 0 := by
  rw [← natDegree_lazardView, lazardView_liftX, Polynomial.natDegree_C]

/-! ## The residue polynomial `T = A · (D'⁻¹ mod D) mod D` -/

variable (A D : K[X])

/-- **The modular inverse of `D'`** mod `D` (the `B` of `D'·B + D·C = 1`), from the Bézout solve
`diophantineSolve D' D 1`; valid when `D` is squarefree (`gcd(D', D) = 1`). -/
noncomputable def dDerivInv : K[X] := (diophantineSolve (derivative D) D 1).1

/-- **The residue polynomial** `T = (A · B) mod D`, `B = D'⁻¹ mod D`. Czichowski's `T(x)`: the
unique `deg < deg D` polynomial with `T ≡ A·D'⁻¹ (mod D)`, so `A ≡ T·D' (mod D)`. -/
noncomputable def residuePoly : K[X] := (A * dDerivInv D) % D

/-- **Bézout identity for `D'` mod `D`**: for `D` squarefree, `D'·B + D·C = 1` with `B = dDerivInv D`.
This is the separability witness that `gcd(D', D)` is a unit. -/
theorem dDeriv_mul_dDerivInv_add (hD : D.Separable) :
    derivative D * dDerivInv D + D * (diophantineSolve (derivative D) D 1).2 = 1 := by
  have hcop : IsCoprime (derivative D) D := ((separable_def D).mp hD).symm
  exact diophantineSolve_spec hcop 1

/-- **`T` is proper**: `deg (residuePoly A D) < deg D` (it is a remainder mod `D`), for `D ≠ 0`. -/
theorem residuePoly_degree_lt (hD : D ≠ 0) : (residuePoly A D).degree < D.degree :=
  Polynomial.degree_mod_lt _ hD

/-- **`A·B ≡ T (mod D)`**: `A · dDerivInv D − residuePoly A D` is divisible by `D`. -/
theorem A_mul_dDerivInv_sub_residuePoly_dvd :
    D ∣ A * dDerivInv D - residuePoly A D := by
  refine ⟨A * dDerivInv D / D, ?_⟩
  rw [residuePoly, eq_comm, ← sub_eq_iff_eq_add'.mpr (EuclideanDomain.div_add_mod
    (A * dDerivInv D) D).symm]
  ring

/-! ## The ideal `I = ⟨A − z·D', D⟩` and the Gröbner basis `GB₁ = {D, z − T}` -/

/-- The dominant lex variable `z = X 0`. -/
noncomputable abbrev zVar : MvPolynomial (Fin 2) K := X 0

/-- **Czichowski's generator** `A − z·D'`: the first generator of `I`, lifted to `K[x, z]`. -/
noncomputable def czGen : MvPolynomial (Fin 2) K := liftX A - zVar * liftX (derivative D)

/-- **The Gröbner-basis element** `z − T`: the reduced generator replacing `A − z·D'`. -/
noncomputable def zMinusResidue : MvPolynomial (Fin 2) K := zVar - liftX (residuePoly A D)

/-- **Czichowski's ideal** `I = ⟨A − z·D', D⟩ ⊂ K[x, z]`. -/
noncomputable def czIdeal : Ideal (MvPolynomial (Fin 2) K) :=
  Ideal.span {czGen A D, liftX D}

/-- `liftX D ∈ I` (the second generator). -/
theorem liftX_D_mem_czIdeal : liftX D ∈ czIdeal A D :=
  Ideal.subset_span (by simp)

/-- `czGen A D = A − z·D' ∈ I` (the first generator). -/
theorem czGen_mem_czIdeal : czGen A D ∈ czIdeal A D :=
  Ideal.subset_span (by simp)

/-- **`z − T ∈ I`** (deliverable B): from the Bézout identity `D'·B + D·C = 1`, `z` is a
combination of `A − z·D'` and `D`; reducing `A·B → T` mod `D` lands `z − T` in `I`. -/
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

/-- **`A − z·D' ≡ −D'·(z − T) (mod D)`** (deliverable C, forward): `czGen + D'·(z − T) = D·(A·C + D'·Q)`,
a multiple of `D` — so the original generator lies in `⟨D, z − T⟩`. -/
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

/-- **`I = ⟨D, z − T⟩ = GB₁`** (deliverable C): Czichowski's ideal is generated by `D` and `z − T`. -/
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

/-! ## `{D, z − T}` is a Gröbner basis (deliverable D)

The two leading monomials are `x^(deg D)` (of `D`, a `z`-free polynomial) and `z` (of `z − T`),
which are **coprime**. We show every nonzero `f ∈ I` has its leading monomial divisible by one of
them: either `f` has a `z` in its leading term (so `z ∣ LM(f)`), or `f` is `z`-free, in which case
substituting `z := T` (the ring map `evalAtResidue`, which kills `z − T` and fixes `liftX`) sends
`f ∈ I` to a multiple of `D`, forcing `x^(deg D) ∣ LM(f)`. -/

/-- **The "substitute `z := T`" map** `K[x, z] → K[x]`: `X 0 ↦ residuePoly A D`, `X 1 ↦ X`. It kills
`z − T` and is a left inverse of `liftX`, so `f ∈ ⟨D, z − T⟩ ↦` a multiple of `D`. -/
noncomputable def evalAtResidue : MvPolynomial (Fin 2) K →+* K[X] :=
  (MvPolynomial.aeval (![residuePoly A D, Polynomial.X] : Fin 2 → K[X])).toRingHom

@[simp] theorem evalAtResidue_X0 : evalAtResidue A D (X 0) = residuePoly A D := by
  simp [evalAtResidue]

@[simp] theorem evalAtResidue_X1 : evalAtResidue A D (X 1) = Polynomial.X := by
  simp [evalAtResidue]

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

/-- **The leading monomial of `z − T` is `z`** (lex `z > x`): `m.degree (zMinusResidue) = single 0 1`,
since `liftX T` (`z`-free) is strictly `≺[lex]` the `z` of `X 0`. -/
theorem degree_zMinusResidue :
    MonomialOrder.lex.degree (zMinusResidue A D) = Finsupp.single (0 : Fin 2) 1 := by
  have hX0 : MonomialOrder.lex.degree (X (0 : Fin 2) : MvPolynomial (Fin 2) K)
      = Finsupp.single 0 1 := degree_X
  rw [zMinusResidue, MonomialOrder.degree_sub_of_lt (g := liftX (residuePoly A D)), hX0]
  rw [hX0]; exact lex_degree_liftX_lt_X0 (residuePoly A D)

/-- **The leading monomial of `D` is `x^(deg D)`** (lex `z > x`): for `D ≠ 0`,
`m.degree (liftX D) = single 1 (D.natDegree)` (`z`-degree `0`, `x`-degree `D.natDegree`). -/
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

/-- **`GB₁ = {D, z − T}` is a Gröbner basis of `I`** (deliverable D), w.r.t. the p.l. ordering
`z > x`. Every nonzero `f ∈ I` has its leading monomial divisible by one of the two coprime
leading monomials `z` (of `z − T`) and `x^(deg D)` (of `D`): if `f` carries a `z` in its leading
term, then `z ∣ LM(f)`; otherwise `f` is `z`-free, so substituting `z := T` sends `f ∈ I` to a
multiple of `D`, forcing `deg_x ≥ deg D`, i.e. `x^(deg D) ∣ LM(f)`. -/
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

-- Restatements against Czichowski's wording.
example (A D : K[X]) (hD : D.Separable) :
    zVar - liftX (residuePoly A D) ∈ Ideal.span {liftX A - zVar * liftX (derivative D), liftX D} :=
  zMinusResidue_mem_czIdeal A D hD

example (A D : K[X]) (hD : D.Separable) :
    Ideal.span {liftX A - zVar * liftX (derivative D), liftX D}
      = Ideal.span {liftX D, zVar - liftX (residuePoly A D)} :=
  czIdeal_eq_span_gb A D hD

/-! ## Zero-dimensionality of `I` (Czichowski Lemma 2.1(i))

Eliminating `z = T` makes the quotient `K[x, z] ⧸ I` isomorphic to `K[x] ⧸ (D)`: the
surjective `K`-algebra map `evalAtResidue` (then `mod D`) has kernel exactly `I`, so the first
isomorphism theorem gives `K[x, z] ⧸ I ≃ₐ K[x] ⧸ (D)`. Since `D` is monic of degree `d`,
`K[x] ⧸ (D) = AdjoinRoot D` is a finite `K`-module (rank `d`), so `I` is **zero-dimensional**. -/

/-- **The reduction `f ≡ liftX (evalAtResidue f) (mod I)`**: for every `f`, the difference
`f − liftX (evalAtResidue f)` lies in `I` (substituting `z := T` changes `f` only by a multiple of
`z − T`, hence of `I`). Proved by `MvPolynomial` induction, using `z − T ∈ I`. -/
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

/-- **`I` is the kernel of `mod D ∘ evalAtResidue`**: `f ∈ I ⟺ D ∣ evalAtResidue f`. Combined with
the surjectivity of `evalAtResidue`, this realizes `K[x, z] ⧸ I ≃ K[x] ⧸ (D)`. -/
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

/-- **The residue `K`-algebra map** `K[x, z] →ₐ[K] K[x] ⧸ (D)`: substitute `z := T`, then reduce
`mod D`. Its kernel is `I` and it is surjective (`liftX` lifts back), giving the eliminating iso. -/
noncomputable def evalAtResidueQuot : MvPolynomial (Fin 2) K →ₐ[K] K[X] ⧸ Ideal.span {D} :=
  (Ideal.Quotient.mkₐ K (Ideal.span {D})).comp
    (MvPolynomial.aeval (![residuePoly A D, Polynomial.X] : Fin 2 → K[X]))

@[simp] theorem evalAtResidueQuot_apply (f : MvPolynomial (Fin 2) K) :
    evalAtResidueQuot A D f = Ideal.Quotient.mk (Ideal.span {D}) (evalAtResidue A D f) := rfl

/-- `evalAtResidueQuot` is surjective: `liftX p ↦ mk p`, and `mk` is surjective. -/
theorem evalAtResidueQuot_surjective : Function.Surjective (evalAtResidueQuot A D) := by
  intro y
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨liftX p, by rw [evalAtResidueQuot_apply, evalAtResidue_liftX]⟩

/-- **The kernel of `evalAtResidueQuot` is exactly `I`**. -/
theorem ker_evalAtResidueQuot (hD : D.Separable) :
    RingHom.ker (evalAtResidueQuot A D).toRingHom = czIdeal A D := by
  ext f
  rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, evalAtResidueQuot_apply,
    Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton,
    ← mem_czIdeal_iff_dvd_evalAtResidue A D hD]

/-- **The eliminating iso** `K[x, z] ⧸ I ≃ₐ[K] K[x] ⧸ (D)` (Czichowski Lemma 2.1(i), engine):
substituting `z = T` identifies the bivariate quotient with the univariate one. -/
noncomputable def czIdealQuotEquiv (hD : D.Separable) :
    (MvPolynomial (Fin 2) K ⧸ czIdeal A D) ≃ₐ[K] K[X] ⧸ Ideal.span {D} :=
  (Ideal.quotientEquivAlgOfEq K (ker_evalAtResidueQuot A D hD).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (evalAtResidueQuot_surjective A D))

/-- **Zero-dimensionality of Czichowski's ideal** (Lemma 2.1(i)): for `D` monic squarefree, the
quotient `K[x, z] ⧸ ⟨A − z·D', D⟩` is a finite `K`-module — eliminating `z = T` makes it
`K[x] ⧸ (D)`, finite of rank `deg D` since `D` is monic. -/
theorem finite_quotient_czIdeal (hM : D.Monic) (hD : D.Separable) :
    Module.Finite K (MvPolynomial (Fin 2) K ⧸ czIdeal A D) :=
  haveI : Module.Finite K (K[X] ⧸ Ideal.span {D}) := hM.finite_adjoinRoot (R := K)
  Module.Finite.equiv (czIdealQuotEquiv A D hD).symm.toLinearEquiv

/-! ## Maximality w.r.t. the zero set: `I` is radical (Czichowski Lemma 2.1(iii))

Czichowski's "`I` is maximal among the ideals with its zero set" is exactly that `I` is a
**radical** ideal (`I = √I`): by the Nullstellensatz `I(V(I)) = √I`, so `I = I(V(I)) ⟺ I` radical.
Since `D` is separable hence squarefree, `K[x] ⧸ (D)` is reduced; transporting through the
eliminating iso `K[x, z] ⧸ I ≃ₐ K[x] ⧸ (D)` makes `K[x, z] ⧸ I` reduced, i.e. `I` is radical. -/

/-- **`(D)` is reduced**: for `D` separable (hence squarefree), the quotient `K[X] ⧸ (D)` is reduced
(`D` squarefree `⟹ (D)` radical `⟹` reduced quotient). -/
theorem isReduced_quotient_span_singleton (hD : D.Separable) :
    IsReduced (K[X] ⧸ Ideal.span {D}) :=
  (Ideal.isRadical_iff_quotient_reduced _).mp
    (isRadical_iff_span_singleton.mp hD.squarefree.isRadical)

/-- **`K[x, z] ⧸ I` is reduced**: transport `IsReduced (K[X] ⧸ (D))` across the eliminating iso
`czIdealQuotEquiv` (an `AlgEquiv`, hence an injective monoid-with-zero hom). -/
theorem isReduced_quotient_czIdeal (hD : D.Separable) :
    IsReduced (MvPolynomial (Fin 2) K ⧸ czIdeal A D) :=
  haveI := isReduced_quotient_span_singleton D hD
  isReduced_of_injective (czIdealQuotEquiv A D hD).toRingHom
    (czIdealQuotEquiv A D hD).injective

/-- **Czichowski's ideal is radical** (Lemma 2.1(iii), maximality w.r.t. its zero set): for `D` monic
separable, `I = ⟨A − z·D', D⟩` is a radical ideal (`I = √I`). By the Nullstellensatz `I(V(I)) = √I`,
this is exactly that `I` is maximal among the ideals sharing its zero set. -/
theorem czIdeal_isRadical (hD : D.Separable) : (czIdeal A D).IsRadical :=
  (Ideal.isRadical_iff_quotient_reduced _).mpr (isReduced_quotient_czIdeal A D hD)

/-! ### Toward the variety analysis (deliverable E, partial): the residue value at a zero

The zeros of `I` are `(α, T(α))` for the roots `α` of `D`, and `T(α) = A(α)/D'(α)` is the
Rothstein–Trager residue. The `x`-parts are the roots of `D`, **distinct** since `D` is squarefree
(`Separable.nodup_roots`) — this is the *normal position* of Lemma 2.1(ii). The remaining claims
(zero-dimensionality, maximality w.r.t. the zero set) need `MvPolynomial`-variety / Nullstellensatz
dimension theory and are the genuine research wall; see the §2.6 catalog marker. -/

/-- **The residue value at a zero of `D`** (deliverable E, the `x`-parts of the zeros): for a root
`α` of `D` (squarefree, so `D'(α) ≠ 0`), `T(α) = A(α)/D'(α)` — the Rothstein–Trager residue. So the
zeros of `I` are `(α, A(α)/D'(α))` over the roots `α` of `D`. -/
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

/-- **Normal position (Lemma 2.1(ii))**: the `x`-parts of the zeros — the roots of `D` — are
distinct, since `D` is squarefree (`Separable ⟹ nodup roots`). -/
theorem nodup_roots_of_separable (hD : D.Separable) : D.roots.Nodup :=
  Polynomial.nodup_roots hD

/-- The two leading monomials are coprime: `x^(deg D) ⊓ z = 0` (disjoint exponent supports),
the structural reason `GB₁`'s single S-polynomial reduces to zero (Buchberger's first criterion). -/
example (D : K[X]) : (Finsupp.single (1 : Fin 2) D.natDegree) ⊓ (Finsupp.single (0 : Fin 2) 1) = 0 := by
  ext i; match i with | 0 => simp | 1 => simp

example (A D : K[X]) (hD : D.Separable) (hD0 : D ≠ 0) :
    IsGroebnerBasis MonomialOrder.lex (Ideal.span {liftX A - zVar * liftX (derivative D), liftX D})
      {liftX D, zVar - liftX (residuePoly A D)} :=
  isGroebnerBasis_gb A D hD hD0

-- The `x`-parts of the zeros are the roots of `D`, with residue `z`-part `A(α)/D'(α)`.
example (A D : K[X]) (hD : D.Separable) {α : K} (hα : D.IsRoot α) :
    (residuePoly A D).eval α = A.eval α / (derivative D).eval α :=
  eval_residuePoly_of_isRoot A D hD hα

-- Eliminating `z = T` identifies `K[x, z] ⧸ I` with `K[x] ⧸ (D)`.
noncomputable example (A D : K[X]) (hD : D.Separable) :
    (MvPolynomial (Fin 2) K ⧸ Ideal.span {liftX A - zVar * liftX (derivative D), liftX D})
      ≃ₐ[K] K[X] ⧸ Ideal.span {D} :=
  czIdealQuotEquiv A D hD

-- Lemma 2.1(i): `I = ⟨A − z·D', D⟩` is zero-dimensional (finite-dimensional quotient over `K`).
example (A D : K[X]) (hM : D.Monic) (hD : D.Separable) :
    Module.Finite K
      (MvPolynomial (Fin 2) K ⧸ Ideal.span {liftX A - zVar * liftX (derivative D), liftX D}) :=
  finite_quotient_czIdeal A D hM hD

-- Lemma 2.1(iii): `I = ⟨A − z·D', D⟩` is radical (maximal w.r.t. its zero set, by the Nullstellensatz).
example (A D : K[X]) (hD : D.Separable) :
    (Ideal.span {liftX A - zVar * liftX (derivative D), liftX D}).IsRadical :=
  czIdeal_isRadical A D hD

end DeepWiki.SymbolicIntegration
