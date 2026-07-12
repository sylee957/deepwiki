import DeepWiki.Algebra.PolynomialDivisibility
import DeepWiki.SymbolicIntegration.Engine.IntegrateTowerCorrectG
import DeepWiki.SymbolicIntegration.Engine.PolynomialBranchSoundness

/-! # Tower Hermite step identities

Field identities for one tower Hermite reduction step and the accumulator fold
used by `cHermiteReduceTowerInnerWf`. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

/-- The tower derivation on a polynomial image: `D_tower(am p) = am (D p)` for
`D = implicitDeriv (toPoly Dt)` (the `den = 1` case of the quotient rule). -/
theorem towerFractionFieldDerivG_amG (Dt : DensePoly α) (p : (CFieldSpec.K α)[X]) :
    towerFractionFieldDeriv Dt (am α p)
      = am α (Differential.implicitDeriv (toPoly Dt) p) := by
  have h := towerFractionFieldDerivG_div Dt p 1
  simpa using h

/-- The tower Hermite lowering step for `cHermiteReduceTowerInnerWf`. With
`D = implicitDeriv (toPoly Dt)`, `U, V ≠ 0`, and the Diophantine relation
`B·(U·DV) + C·V = -A·C((j+1)⁻¹)`, one step drops the `V`-power by one and emits `B/V^(j+1)`:
`am A/(am U · am V^(j+2)) = D_tower(am B/am V^(j+1)) + am(-(C(j+1))·C - U·DB)/(am U·am V^(j+1))`. -/
theorem towerFractionFieldDerivG_hermite_step [CharZero (CFieldSpec.K α)] (Dt : DensePoly α)
    (A B C U V : (CFieldSpec.K α)[X]) (hU : U ≠ 0) (hV : V ≠ 0) (j : ℕ)
    (hrel : B * (U * Differential.implicitDeriv (toPoly Dt) V) + C * V
        = -A * Polynomial.C (((j : CFieldSpec.K α) + 1)⁻¹)) :
    am α A / (am α U * am α V ^ (j + 2))
      = towerFractionFieldDeriv Dt (am α B / am α V ^ (j + 1))
        + am α (-(Polynomial.C ((j : CFieldSpec.K α) + 1)) * C
              - U * Differential.implicitDeriv (toPoly Dt) B)
          / (am α U * am α V ^ (j + 1)) := by
  set D := Differential.implicitDeriv (toPoly Dt) with hDdef
  set am := am α with hamdef
  have hinj : Function.Injective am := RatFunc.algebraMap_injective (CFieldSpec.K α)
  have hu : am U ≠ 0 := (map_ne_zero_iff _ hinj).mpr hU
  have hv : am V ≠ 0 := (map_ne_zero_iff _ hinj).mpr hV
  have hvp : am V ^ (j + 1) ≠ 0 := pow_ne_zero _ hv
  have hn1 : ((j : CFieldSpec.K α) + 1) ≠ 0 := Nat.cast_add_one_ne_zero j
  -- constant casts: `am (C k) = algebraMap K (RatFunc K) k`, and `(j+1)·(j+1)⁻¹ = 1`.
  have e1 : ∀ k : CFieldSpec.K α, am (Polynomial.C k) = algebraMap (CFieldSpec.K α) (RatFunc _) k :=
    fun k => by
      rw [hamdef, CFrac.am, ← Polynomial.algebraMap_eq]
      exact (IsScalarTower.algebraMap_apply (CFieldSpec.K α) (CFieldSpec.K α)[X] (RatFunc _) k).symm
  have hc1 : am (Polynomial.C ((j : CFieldSpec.K α) + 1)) = (j : RatFunc (CFieldSpec.K α)) + 1 := by
    rw [e1, map_add, map_natCast, map_one]
  have hκ : ((j : RatFunc (CFieldSpec.K α)) + 1) * am (Polynomial.C ((j : CFieldSpec.K α) + 1)⁻¹) = 1 := by
    rw [e1, ← hc1, e1, ← map_mul, mul_inv_cancel₀ hn1, map_one]
  -- `am`-of-derivation rewrites (the `den = 1` quotient rule).
  have hdB : towerFractionFieldDeriv Dt (am B) = am (D B) := towerFractionFieldDerivG_amG Dt B
  have hdV : towerFractionFieldDeriv Dt (am V) = am (D V) := towerFractionFieldDerivG_amG Dt V
  -- map the polynomial Diophantine relation into the fraction field.
  have hbez : am B * (am U * am (D V)) + am C * am V
      = -am A * am (Polynomial.C ((j : CFieldSpec.K α) + 1)⁻¹) := by
    have h := congrArg am hrel
    rw [map_add, map_mul, map_mul, map_mul, map_mul, map_neg] at h
    exact h
  have hbez2 : ((j : RatFunc (CFieldSpec.K α)) + 1) * (am B * (am U * am (D V)) + am C * am V)
      = -am A := by
    rw [hbez]; linear_combination (-am A) * hκ
  -- the polynomial power rule, mapped into the fraction field.
  have hDVpoly : am (D (V ^ (j + 1)))
      = ((j : RatFunc (CFieldSpec.K α)) + 1) * am V ^ j * am (D V) := by
    rw [hDdef, Derivation.leibniz_pow, Nat.add_sub_cancel, map_nsmul, smul_eq_mul, map_mul,
      map_pow, nsmul_eq_mul]
    push_cast; ring
  -- expand the derivative term via the tower quotient rule.
  have hderiv : towerFractionFieldDeriv Dt (am B / am V ^ (j + 1))
      = (am (D B) * am V ^ (j + 1)
          - am B * (((j : RatFunc (CFieldSpec.K α)) + 1) * am V ^ j * am (D V)))
        / (am V ^ (j + 1)) ^ 2 := by
    have h := towerFractionFieldDerivG_div Dt B (V ^ (j + 1))
    rw [map_pow] at h
    rw [h, hDVpoly]
  rw [hderiv, map_sub, map_mul, map_mul, map_neg, hc1]
  have hA : am A = -((j : RatFunc (CFieldSpec.K α)) + 1) * (am B * (am U * am (D V)) + am C * am V) := by
    linear_combination hbez2
  rw [hA, pow_succ]
  field_simp
  ring

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
open CFrac in
/-- Cross-multiplied fraction-pair addition reads as the sum of the represented fractions. -/
theorem fracPair_add (a1 a2 b1 b2 : DensePoly α)
    (ha2 : toPoly a2 ≠ 0) (hb2 : toPoly b2 ≠ 0) :
    am α (toPoly (cadd (cmul a1 b2) (cmul b1 a2))) / am α (toPoly (cmul a2 b2))
      = am α (toPoly a1) / am α (toPoly a2) + am α (toPoly b1) / am α (toPoly b2) := by
  simp only [denote, map_add, map_mul]
  rw [div_add_div _ _ (am_ne_zero ha2) (am_ne_zero hb2)]
  ring

open CFrac in
/-- The inner Hermite loop invariant with a general accumulator. For `u, v ≠ 0`, the tower
derivation `D = implicitDeriv (toPoly Dt)`, and every step's `CPoly.diophantineReduced` cofactors satisfying
the Bézout relation `hbez`, the loop `cHermiteReduceTowerInnerWf Dt v u j A g` telescopes M1:
`⟦A/(u·v^(j+1))⟧ + D_tower(⟦g⟧) = D_tower(⟦result.g⟧) + ⟦result.a/(u·v)⟧`. -/
theorem cHermiteReduceTowerInnerWf_spec_acc [CharZero (CFieldSpec.K α)] (Dt v u : DensePoly α)
    (hu : toPoly u ≠ 0) (hv : toPoly v ≠ 0)
    (hbez : ∀ (j' : ℕ) (A' : DensePoly α),
      toPoly (CPoly.diophantineReduced (cmul u (CPolyEngine.monomialDeriv Dt v)) v
            (cscale (CCommRing.neg (CField.inv (CField.natCast (j' + 1)))) A')).1
          * (toPoly u * Differential.implicitDeriv (toPoly Dt) (toPoly v))
        + toPoly (CPoly.diophantineReduced (cmul u (CPolyEngine.monomialDeriv Dt v)) v
            (cscale (CCommRing.neg (CField.inv (CField.natCast (j' + 1)))) A')).2 * toPoly v
      = -toPoly A' * Polynomial.C (((j' : CFieldSpec.K α) + 1)⁻¹)) :
    ∀ (j : ℕ) (A : DensePoly α) (g : DensePoly α × DensePoly α), toPoly g.2 ≠ 0 →
      am α (toPoly A) / (am α (toPoly u) * am α (toPoly v) ^ (j + 1))
          + towerFractionFieldDeriv Dt (am α (toPoly g.1) / am α (toPoly g.2))
        = towerFractionFieldDeriv Dt
            (am α (toPoly (cHermiteReduceTowerInnerWf Dt v u j A g).1.1)
              / am α (toPoly (cHermiteReduceTowerInnerWf Dt v u j A g).1.2))
          + am α (toPoly (cHermiteReduceTowerInnerWf Dt v u j A g).2)
            / (am α (toPoly u) * am α (toPoly v)) := by
  intro j
  induction j with
  | zero =>
    intro A g hg
    simp only [cHermiteReduceTowerInnerWf, Nat.zero_add, pow_one]
    ring
  | succ j ih =>
    intro A g hg
    rw [cHermiteReduceTowerInnerWf]
    set jval : α := CField.natCast (j + 1) with hjval
    set Dv := CPolyEngine.monomialDeriv Dt v with hDv
    set p := cmul u Dv with hp
    set rhs := cscale (CCommRing.neg (CField.inv jval)) A with hrhs
    rcases hBC : CPoly.diophantineReduced p v rhs with ⟨B, C⟩
    simp only []
    set Vpow := cpow v (j + 1) with hVpow
    set A' := csub (cscale (CCommRing.neg jval) C) (cmul u (CPolyEngine.monomialDeriv Dt B)) with hA'
    have hVpow0 : toPoly Vpow ≠ 0 := by
      rw [hVpow]
      simp only [denote]
      exact pow_ne_zero _ hv
    have hgnew : toPoly (cmul g.2 Vpow) ≠ 0 := by
      simp only [denote]
      exact mul_ne_zero hg hVpow0
    -- the accumulator update reads as `⟦g⟧ + ⟦B/Vpow⟧`.
    have hstepadd := fracPair_add g.1 g.2 B Vpow hg hVpow0
    -- `Vpow = v^(j+1)`, `B/Vpow = am B / (am v)^(j+1)`.
    have hVpoweq : am α (toPoly Vpow) = am α (toPoly v) ^ (j + 1) := by
      rw [hVpow]
      simp only [denote, map_pow]
    -- the Bézout relation at `(j, A)`, matched to M1's `hrel`.
    have hb := hbez j A
    rw [← hjval, ← hrhs, hBC] at hb
    simp only [] at hb
    -- apply the single-step identity M1.
    have hstep := towerFractionFieldDerivG_hermite_step (α := α) Dt (toPoly A) (toPoly B)
      (toPoly C) (toPoly u) (toPoly v) hu hv j hb
    -- the recursion at counter `j` with the updated accumulator and numerator `A'`.
    have hgnew' : toPoly (cmul g.2 Vpow) ≠ 0 := hgnew
    have ihA := ih A' (cadd (cmul g.1 Vpow) (cmul B g.2), cmul g.2 Vpow) hgnew'
    simp only [] at ihA
    -- rewrite `A'` numerator and the accumulator fraction in the recursion hypothesis.
    have hA'eq : toPoly A'
        = -(Polynomial.C ((j : CFieldSpec.K α) + 1)) * toPoly C
          - toPoly u * Differential.implicitDeriv (toPoly Dt) (toPoly B) := by
      rw [hA']
      simp only [denote, CFieldSpec.toK_neg, hjval, CFieldSpec.toK_natCast, Nat.cast_add_one, map_neg]
    rw [hstepadd, hVpoweq] at ihA
    rw [map_add] at ihA
    rw [hA'eq] at ihA
    -- glue: M1 (power drop) + recursion tail.
    linear_combination hstep + ihA

/-! ### Whole-step field identity from exact division

`cHermiteReduceTower Dt a d = ((gnum,gden),(hNum,Dstar))` computes the residual `hNum/Dstar` so
that it equals `a/d - D(g)` by construction: `resNum/resDen = (a·gden² - d·gp)/(d·gden²)` with
`gp = D(gnum)·gden - gnum·D(gden)` the quotient numerator, and `hNum = (resNum·Dstar)/resDen`. So the
step identity `D(⟦g⟧) + ⟦hNum/Dstar⟧ = ⟦a/d⟧` is a clean algebraic assembly reducing to the single
exact-division relation `hNum·resDen = resNum·Dstar` (Hermite's pole-cancellation guarantee, which
M1/M2 + Yun discharge). Mirrors `canonicalReconstruction`. -/

/-- The whole-step Hermite field identity. For the tower derivation `D`, given `d, gden, Dstar ≠ 0`
and the exact-division relation `⟦hNum⟧·⟦d·gden²⟧ = ⟦resNum⟧·⟦Dstar⟧` (with `resNum = a·gden² - d·gp`,
`gp = D(gnum)·gden - gnum·D(gden)`), the reduced part telescopes:
`D_tower(⟦gnum/gden⟧) + ⟦hNum/Dstar⟧ = ⟦a/d⟧`. -/
theorem hermiteTowerStep_field_identity (Dt gnum gden a d hNum Dstar : DensePoly α)
    (hd : am α (toPoly d) ≠ 0) (hgden : am α (toPoly gden) ≠ 0)
    (hDstar : am α (toPoly Dstar) ≠ 0)
    (hexact : am α (toPoly hNum)
          * am α (toPoly (cmul d (cmul gden gden)))
        = am α (toPoly (csub (cmul a (cmul gden gden))
            (cmul d (csub (cmul (CPolyEngine.monomialDeriv Dt gnum) gden)
              (cmul gnum (CPolyEngine.monomialDeriv Dt gden))))))
          * am α (toPoly Dstar)) :
    towerFractionFieldDeriv Dt (am α (toPoly gnum) / am α (toPoly gden))
        + am α (toPoly hNum) / am α (toPoly Dstar)
      = am α (toPoly a) / am α (toPoly d) := by
  rw [towerFractionFieldDerivG_div]
  simp only [denote, map_sub, map_mul] at hexact ⊢
  set Dg := Differential.implicitDeriv (toPoly Dt)
  -- `⟦hNum/Dstar⟧ = ⟦resNum/resDen⟧` from the exact-division relation.
  have hgden2 : am α (toPoly gden) ^ 2 ≠ 0 := pow_ne_zero _ hgden
  have hkey : am α (toPoly hNum) / am α (toPoly Dstar)
      = (am α (toPoly a) * (am α (toPoly gden) * am α (toPoly gden))
          - am α (toPoly d) * (am α (Dg (toPoly gnum)) * am α (toPoly gden)
              - am α (toPoly gnum) * am α (Dg (toPoly gden))))
        / (am α (toPoly d) * (am α (toPoly gden) * am α (toPoly gden))) := by
    rw [div_eq_div_iff hDstar (mul_ne_zero hd (mul_ne_zero hgden hgden))]
    linear_combination hexact
  rw [hkey]
  field_simp
  ring

/-! ### Radical split for exact division

The exact-division `resDen ∣ resNum·Dstar` decomposes, by the pure field-algebra
`polynomial_dvd_cleared_identity_of_radical`, into two genuine sub-facts: `d = Dstar·W` (the squarefree radical
`Dstar` divides `d` with cofactor `W`, a Yun structural fact) and `W·gden² ∣ resNum` (Hermite
pole-cancellation: the reduced residual's `W`-poles cancel). Tower analog of
`hermiteReduce_residual_correct_of_radical`. -/

open CFrac in
/-- The whole-step Hermite field identity from the radical split. With `hNum` the exact quotient
`CPolyEuclidean.div (resNum·Dstar) (d·gden²)`, given `d = Dstar·W` (`hSD`) and `W·gden² ∣ resNum` (`hWgd`), the
reduced part telescopes: `D_tower(⟦gnum/gden⟧) + ⟦hNum/Dstar⟧ = ⟦a/d⟧`. -/
theorem hermiteTowerStep_field_identity_of_radical (Dt gnum gden a d Dstar W : DensePoly α)
    (hd : am α (toPoly d) ≠ 0) (hgden : am α (toPoly gden) ≠ 0)
    (hDstar : am α (toPoly Dstar) ≠ 0)
    (hresDen : cnorm (cmul d (cmul gden gden)) ≠ [])
    (hSD : toPoly d = toPoly Dstar * toPoly W)
    (hWgd : toPoly W * (toPoly gden * toPoly gden)
        ∣ toPoly (csub (cmul a (cmul gden gden))
            (cmul d (csub (cmul (CPolyEngine.monomialDeriv Dt gnum) gden)
              (cmul gnum (CPolyEngine.monomialDeriv Dt gden)))))) :
    towerFractionFieldDeriv Dt (am α (toPoly gnum) / am α (toPoly gden))
        + am α (toPoly (CPolyEuclidean.div (cmul (csub (cmul a (cmul gden gden))
            (cmul d (csub (cmul (CPolyEngine.monomialDeriv Dt gnum) gden)
              (cmul gnum (CPolyEngine.monomialDeriv Dt gden))))) Dstar) (cmul d (cmul gden gden))))
          / am α (toPoly Dstar)
      = am α (toPoly a) / am α (toPoly d) := by
  set resNum := csub (cmul a (cmul gden gden))
    (cmul d (csub (cmul (CPolyEngine.monomialDeriv Dt gnum) gden)
      (cmul gnum (CPolyEngine.monomialDeriv Dt gden)))) with hresNum
  set resDen := cmul d (cmul gden gden) with hresDen'
  -- the divisibility `resDen ∣ resNum·Dstar` from the radical split.
  have hdvd : toPoly resDen ∣ toPoly (cmul resNum Dstar) := by
    rw [hresDen']
    simp only [denote]
    exact DeepWiki.polynomial_dvd_cleared_identity_of_radical hSD hWgd
  -- the exact-division equation, mapped into the fraction field.
  have hexactP : toPoly (CPolyEuclidean.div (cmul resNum Dstar) resDen) * toPoly resDen
      = toPoly (cmul resNum Dstar) := toPolyG_div_exact _ _ hresDen hdvd
  have hexact : am α (toPoly (CPolyEuclidean.div (cmul resNum Dstar) resDen))
        * am α (toPoly resDen)
      = am α (toPoly resNum) * am α (toPoly Dstar) := by
    rw [← map_mul, hexactP]
    simp only [denote, map_mul]
  exact hermiteTowerStep_field_identity Dt gnum gden a d
    (CPolyEuclidean.div (cmul resNum Dstar) resDen) Dstar hd hgden hDstar hexact

end DeepWiki.SymbolicIntegration
