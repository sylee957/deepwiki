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


end DeepWiki.SymbolicIntegration
