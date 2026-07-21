import DeepWiki.CAlgebra.Integrate.DerivData
import DeepWiki.CAlgebra.Integrate.LogPartSpec
import DeepWiki.CAlgebra.Integrate.RatIntegrate
import Mathlib.FieldTheory.Perfect

/-! # The computable-derivative square and the data-level spec

The denotation square of the resultant-deformation derivative — the generic coefficient
extraction of a `t`-linearly deformed product, the readings of the deformation's
construction into `K(x)[t]`, the per-pair square
`toRatFunc (rootSumDeriv Q S) = lrtPairTerm (Q, S)`, the record squares reading
`toRatFunc res.deriv` as the derivative of the represented antiderivative — and the
**primary data-level spec**:
`lrtIntegrate_sound`/`lrtIntegrate_complete` and the decidable
`ratIntegrate_sound : (ratIntegrate f).deriv = f` with `ratIntegrate_complete`. -/

namespace DeepWiki.CAlgebra

universe u v

section DeformedProduct

variable {A : Type u} [CommRing A] {ι : Type*} [DecidableEq ι]

open Polynomial

omit [DecidableEq ι] in
/-- Constant coefficient of a `t`-linearly deformed product: `∏ (aᵢ + bᵢ·t)` has
`coeff 0 = ∏ aᵢ`. -/
theorem coeff_zero_prod_C_add_C_mul_X (s : Finset ι) (a b : ι → A) :
    (∏ i ∈ s, (C (a i) + C (b i) * X)).coeff 0 = ∏ i ∈ s, a i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih =>
      rw [Finset.prod_cons, Finset.prod_cons, Polynomial.mul_coeff_zero, ih]
      simp

/-- Linear coefficient of a `t`-linearly deformed product: `∏ (aᵢ + bᵢ·t)` has
`coeff 1 = ∑ᵢ bᵢ · ∏_{j ≠ i} aⱼ`. -/
theorem coeff_one_prod_C_add_C_mul_X (s : Finset ι) (a b : ι → A) :
    (∏ i ∈ s, (C (a i) + C (b i) * X)).coeff 1
      = ∑ i ∈ s, b i * ∏ j ∈ s.erase i, a j := by
  induction s using Finset.cons_induction with
  | empty => simp [Polynomial.coeff_one]
  | cons i s hi ih =>
      have hX : (X * ∏ j ∈ s, (C (a j) + C (b j) * X)).coeff 1
          = (∏ j ∈ s, (C (a j) + C (b j) * X)).coeff 0 := by
        simp
      rw [Finset.prod_cons, Finset.sum_cons, add_mul, Polynomial.coeff_add,
        Polynomial.coeff_C_mul, ih, mul_assoc, Polynomial.coeff_C_mul, hX,
        coeff_zero_prod_C_add_C_mul_X, Finset.erase_cons, Finset.mul_sum, add_comm]
      congr 1
      refine Finset.sum_congr rfl fun k hk => ?_
      have hik : i ≠ k := fun h => hi (h ▸ hk)
      rw [Finset.cons_eq_insert, Finset.erase_insert_of_ne hik,
        Finset.prod_insert (fun h => hi (Finset.mem_of_mem_erase h))]
      ring

/-- Root-sum ratio: `(∑ᵢ bᵢ ∏_{j≠i} aⱼ) / ∏ aᵢ = ∑ᵢ bᵢ/aᵢ` when no `aᵢ` vanishes. -/
theorem sum_mul_prod_erase_div_prod {K : Type v} [Field K] (s : Finset ι) (a b : ι → K)
    (ha : ∀ i ∈ s, a i ≠ 0) :
    (∑ i ∈ s, b i * ∏ j ∈ s.erase i, a j) / (∏ i ∈ s, a i) = ∑ i ∈ s, b i / a i := by
  rw [eq_comm, eq_div_iff (Finset.prod_ne_zero_iff.mpr ha), Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← Finset.mul_prod_erase s a hi, div_mul_eq_mul_div, mul_comm (a i), ← mul_assoc,
    mul_div_cancel_right₀ _ (ha i hi)]

end DeformedProduct

namespace DensePoly

open Polynomial

variable {R : Type u} [Field R] [DecidableEq R]

open scoped Differential FormalDiff

/- The scoped `FormalDiff` instances are needed for the engine-level `′`; on `RatFunc`
itself the global `d/dx` instance (the one `lrtPairTerm` pins) must keep winning. -/
attribute [local instance 2000] SymbolicIntegration.instDifferentialRatFunc_deepWiki

/-- The coefficient reading `K[x][t] → K(x)[t]` of the deformation's coefficient ring. -/
noncomputable def tRead : DensePoly (DensePoly R) →+* Polynomial (RatFunc R) :=
  (Polynomial.mapRingHom (algebraMap (Polynomial R) (RatFunc R))).comp toPolynomial₂Hom

/-- `tRead` reads as the bridged bivariate polynomial with mapped coefficients. -/
theorem tRead_apply (d : DensePoly (DensePoly R)) :
    tRead d = (toPolynomial₂ d).map (algebraMap (Polynomial R) (RatFunc R)) := rfl

/-- The constant embedding `K[x] → K(x)[t]`. -/
noncomputable def xConst : Polynomial R →+* Polynomial (RatFunc R) :=
  (Polynomial.C).comp (algebraMap (Polynomial R) (RatFunc R))

omit [DecidableEq R] in
/-- `xConst` reads as the constant polynomial on the embedded rational function. -/
theorem xConst_apply (p : Polynomial R) :
    xConst p = Polynomial.C (algebraMap (Polynomial R) (RatFunc R) p) := rfl

/-- The scalar-constant embedding `K → K(x)[t]`. -/
noncomputable def kConst : R →+* Polynomial (RatFunc R) :=
  xConst.comp (Polynomial.C : R →+* Polynomial R)

omit [DecidableEq R] in
/-- `kConst` reads as the constant polynomial on the embedded scalar. -/
theorem kConst_apply (r : R) :
    kConst r = Polynomial.C (algebraMap (Polynomial R) (RatFunc R) (Polynomial.C r)) := rfl

/-- Coefficient reading of `tRead`. -/
theorem tRead_coeff (d : DensePoly (DensePoly R)) (k : ℕ) :
    (tRead d).coeff k = algebraMap (Polynomial R) (RatFunc R) (toPolynomial (d.coeff k)) := by
  rw [tRead_apply, Polynomial.coeff_map, toPolynomial₂_coeff]

/-- `tRead` sends inner constants to `xConst` of the bridged polynomial. -/
theorem tRead_C (c : DensePoly R) : tRead (C c) = xConst (toPolynomial c) := by
  rw [tRead_apply, toPolynomial₂_C, Polynomial.map_C, xConst_apply]

/-- `tRead` sends the linear-deformation coefficient `c·t` to `xConst c · t`. -/
theorem tRead_ofList_zero_single (c : DensePoly R) :
    tRead (ofList [0, c]) = xConst (toPolynomial c) * Polynomial.X := by
  refine Polynomial.ext fun k => ?_
  rw [tRead_coeff, xConst_apply, Polynomial.coeff_C_mul, coeff_ofList]
  rcases k with _ | _ | k <;> simp [Polynomial.coeff_X, List.getD]

/-- `DensePoly.C` of zero is zero. -/
private theorem C_zero' {S : Type v} [CommRing S] [DecidableEq S] :
    (C (0 : S) : DensePoly S) = 0 :=
  toPolynomial_injective (by rw [toPolynomial_C, Polynomial.C_0, toPolynomial_zero])

/-- The deformation's first resultant argument reads as the scalar-mapped `Q`. -/
theorem map_tRead_toPolynomial_CC (Q : DensePoly R) :
    (toPolynomial (ofList (Q.coeffs.map fun r => C (C r)) :
        DensePoly (DensePoly (DensePoly R)))).map tRead
      = (toPolynomial Q).map kConst := by
  have hf : (C (C (0 : R)) : DensePoly (DensePoly R)) = 0 := by rw [C_zero', C_zero']
  refine Polynomial.ext fun k => ?_
  rw [Polynomial.coeff_map, Polynomial.coeff_map, coeff_toPolynomial, coeff_toPolynomial,
    coeff_ofList_map _ hf, tRead_C, toPolynomial_C, xConst_apply, kConst_apply]

/-- The deformation's second resultant argument reads as `Sz + z·t·Sxz`. -/
theorem map_tRead_toPolynomial_deform (Sz Sxz : DensePoly (DensePoly R)) :
    (toPolynomial (ofList (Sz.coeffs.map fun c => C c)
        + ofList [0, 1] * ofList (Sxz.coeffs.map fun c => ofList [0, c]))).map tRead
      = (toPolynomial₂ Sz).map xConst
        + Polynomial.X * (Polynomial.C (Polynomial.X : Polynomial (RatFunc R))
            * ((toPolynomial₂ Sxz).map xConst)) := by
  have hOfZero : (ofList [0, (0 : DensePoly R)] : DensePoly (DensePoly R)) = 0 := by
    ext i
    rw [coeff_ofList, coeff_zero]
    rcases i with _ | _ | i <;> simp [List.getD]
  rw [toPolynomial_add, toPolynomial_mul, toPolynomial_X, Polynomial.map_add,
    Polynomial.map_mul, Polynomial.map_X]
  congr 1
  · refine Polynomial.ext fun k => ?_
    rw [Polynomial.coeff_map, Polynomial.coeff_map, coeff_toPolynomial, toPolynomial₂_coeff,
      coeff_ofList_map _ C_zero', tRead_C]
  · congr 1
    refine Polynomial.ext fun k => ?_
    rw [Polynomial.coeff_map, coeff_toPolynomial, coeff_ofList_map _ hOfZero,
      tRead_ofList_zero_single, Polynomial.coeff_C_mul, Polynomial.coeff_map,
      toPolynomial₂_coeff, xConst_apply]
    ring

/-- The scalar-embedded first argument keeps the degree of `Q`. -/
theorem natDegree_toPolynomial_map_CC (Q : DensePoly R) :
    (toPolynomial (ofList (Q.coeffs.map fun r => C (C r)) :
        DensePoly (DensePoly (DensePoly R)))).natDegree = (toPolynomial Q).natDegree := by
  have hf : (C (C (0 : R)) : DensePoly (DensePoly R)) = 0 := by rw [C_zero', C_zero']
  apply le_antisymm
  · refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun k hk => ?_
    have h0 : Q.coeff k = 0 := by
      rw [← coeff_toPolynomial]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt hk
    rw [coeff_toPolynomial, coeff_ofList_map _ hf, h0, hf]
  · refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun k hk => ?_
    have h0 : (C (C (Q.coeff k)) : DensePoly (DensePoly R)) = 0 := by
      rw [← coeff_ofList_map (fun r => C (C r)) hf Q k, ← coeff_toPolynomial]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt hk
    have h1 := congrArg (fun d : DensePoly (DensePoly R) =>
      (d.coeff 0).coeff 0) h0
    rw [coeff_toPolynomial]
    simpa [coeff_C, coeff_zero] using h1

/-- Evaluating the mapped transpose at an embedded scalar is the coefficient evaluation. -/
theorem eval_kConst_map_xConst (S : DensePoly (DensePoly R)) (α : R) :
    ((toPolynomial₂ (zSwap S)).map xConst).eval (kConst α)
      = xConst (toPolynomial (zEval α S)) := by
  rw [show kConst α = xConst (Polynomial.C α) from rfl, Polynomial.eval_map,
    Polynomial.eval₂_at_apply, toPolynomial₂_zSwap_eval]

/-- The bivariate bridge intertwines the outer formal derivative. -/
theorem toPolynomial₂_deriv (S : DensePoly (DensePoly R)) :
    toPolynomial₂ (S′) = Polynomial.derivative (toPolynomial₂ S) := by
  rw [toPolynomial₂, toPolynomial₂, toPolynomial_deriv, Polynomial.derivative_map]

section Closure

variable [CharZero R] [IsAlgClosed R]

/-- **The deformed resultant is a scaled product of per-root linear forms**:
`Res_z(Q, S + t·z·Sₓ)` reads in `K(x)[t]` as `lc^N · ∏_{Q(α)=0} (S(α,·) + t·α·Sₓ(α,·))`. -/
theorem tRead_resultant_deform (Q : DensePoly R) (S : DensePoly (DensePoly R))
    (hsf : Squarefree (toPolynomial Q)) :
    ∃ N : ℕ,
      tRead (DensePolyResultant.resultant
          (ofList (Q.coeffs.map fun r => C (C r)))
          (ofList ((zSwap S).coeffs.map fun c => C c)
            + ofList [0, 1] * ofList ((zSwap (S′)).coeffs.map fun c => ofList [0, c])))
        = kConst ((toPolynomial Q).leadingCoeff) ^ N
          * ∏ α ∈ (toPolynomial Q).roots.toFinset,
              (Polynomial.C (algebraMap (Polynomial R) (RatFunc R)
                  (toPolynomial (zEval α S)))
                + Polynomial.C (algebraMap (Polynomial R) (RatFunc R) (Polynomial.C α)
                    * algebraMap (Polynomial R) (RatFunc R) (toPolynomial (zEval α (S′))))
                  * Polynomial.X) := by
  classical
  set Adef := ofList ((zSwap S).coeffs.map fun c => C c)
    + ofList [0, 1] * ofList ((zSwap (S′)).coeffs.map fun c => ofList [0, c]) with hAdef
  refine ⟨(toPolynomial Adef).natDegree, ?_⟩
  set n₀ := (toPolynomial Adef).natDegree with hn₀
  have hPne : toPolynomial Q ≠ 0 := hsf.ne_zero
  have hsplits : (toPolynomial Q).Splits := IsAlgClosed.splits _
  have hnodup : (toPolynomial Q).roots.Nodup :=
    Polynomial.nodup_roots (PerfectField.separable_iff_squarefree.mpr hsf)
  -- multiset products over the roots collapse to finset products
  have hms : ∀ {M : Type u} [CommMonoid M] (f : R → M),
      ((toPolynomial Q).roots.map f).prod = ∏ α ∈ (toPolynomial Q).roots.toFinset, f α := by
    intro M _ f
    rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
      Multiset.dedup_eq_self.mpr hnodup]
  -- the mapped factorization of `Q`
  have hfactm : (toPolynomial Q).map kConst
      = Polynomial.C (kConst (toPolynomial Q).leadingCoeff)
        * ∏ α ∈ (toPolynomial Q).roots.toFinset,
            (Polynomial.X - Polynomial.C (kConst α)) := by
    conv_lhs => rw [hsplits.eq_prod_roots]
    rw [Polynomial.map_mul, Polynomial.map_C,
      ← hms fun α => Polynomial.X - Polynomial.C (kConst α)]
    congr 1
    have hmp := map_multiset_prod (Polynomial.mapRingHom kConst)
      ((toPolynomial Q).roots.map fun a => Polynomial.X - Polynomial.C a)
    rw [Polynomial.coe_mapRingHom] at hmp
    rw [hmp, Multiset.map_map]
    exact congrArg Multiset.prod (Multiset.map_congr rfl fun a _ => by
      rw [Function.comp_apply, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C])
  -- the degree of the split product
  have hcard : (toPolynomial Q).roots.toFinset.card = (toPolynomial Q).natDegree := by
    rw [Multiset.toFinset_card_of_nodup hnodup, ← hsplits.natDegree_eq_card_roots]
  have hdegprod : (∏ α ∈ (toPolynomial Q).roots.toFinset,
      ((Polynomial.X : Polynomial (Polynomial (RatFunc R))) - Polynomial.C (kConst α))).natDegree
      = (toPolynomial Q).natDegree := by
    rw [Polynomial.natDegree_prod _ _ (fun a _ => Polynomial.X_sub_C_ne_zero _),
      Finset.sum_congr rfl (fun a _ => Polynomial.natDegree_X_sub_C _),
      Finset.sum_const, smul_eq_mul, mul_one, hcard]
  -- the second argument's mapped degree bound
  have hnB : ((toPolynomial₂ (zSwap S)).map xConst
      + Polynomial.X * (Polynomial.C (Polynomial.X : Polynomial (RatFunc R))
          * ((toPolynomial₂ (zSwap (S′))).map xConst))).natDegree ≤ n₀ := by
    rw [← map_tRead_toPolynomial_deform]
    exact Polynomial.natDegree_map_le
  -- the resultant chain
  rw [DensePolyResultant.resultant_eq]
  rw [← Polynomial.resultant_map_map]
  rw [map_tRead_toPolynomial_CC, map_tRead_toPolynomial_deform]
  rw [natDegree_toPolynomial_map_CC]
  rw [hfactm]
  rw [Polynomial.resultant_C_mul_left]
  rw [← hdegprod]
  rw [Polynomial.resultant_prod_left ((toPolynomial Q).roots.toFinset)
    (fun α => Polynomial.X - Polynomial.C (kConst α)) _ n₀
    (by simp [Polynomial.leadingCoeff_X_sub_C]) hnB]
  have hfac : ∀ α ∈ (toPolynomial Q).roots.toFinset,
      Polynomial.resultant (Polynomial.X - Polynomial.C (kConst α))
        ((toPolynomial₂ (zSwap S)).map xConst
          + Polynomial.X * (Polynomial.C (Polynomial.X : Polynomial (RatFunc R))
              * ((toPolynomial₂ (zSwap (S′))).map xConst)))
        (Polynomial.X - Polynomial.C (kConst α)).natDegree n₀
      = Polynomial.C (algebraMap (Polynomial R) (RatFunc R) (toPolynomial (zEval α S)))
        + Polynomial.C (algebraMap (Polynomial R) (RatFunc R) (Polynomial.C α)
            * algebraMap (Polynomial R) (RatFunc R) (toPolynomial (zEval α (S′))))
          * Polynomial.X := by
    intro α hα
    rw [Polynomial.natDegree_X_sub_C]
    have h1 := Polynomial.resultant_X_sub_C_pow_left (kConst α)
      ((toPolynomial₂ (zSwap S)).map xConst
        + Polynomial.X * (Polynomial.C (Polynomial.X : Polynomial (RatFunc R))
            * ((toPolynomial₂ (zSwap (S′))).map xConst))) 1 n₀ hnB
    rw [pow_one, pow_one] at h1
    rw [h1, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_mul,
      Polynomial.eval_C, eval_kConst_map_xConst, eval_kConst_map_xConst, xConst_apply,
      xConst_apply, kConst_apply, Polynomial.C_mul]
    ring
  rw [Finset.prod_congr rfl hfac]

variable [DensePolyGcd R]

/-- **The per-pair square**: the resultant-deformation derivative denotes the RootSum
log-term derivative `∑_{Q(α)=0} α · Sₓ(α,·)/S(α,·)`. -/
theorem toRatFunc_rootSumDeriv (Q : DensePoly R) (S : DensePoly (DensePoly R))
    (hsf : Squarefree (toPolynomial Q))
    (hS : ∀ α ∈ (toPolynomial Q).roots,
      (toPolynomial₂ S).map (Polynomial.evalRingHom α) ≠ 0) :
    DenseFrac.toRatFunc (rootSumDeriv Q S) = lrtPairTerm (Q, S) := by
  classical
  obtain ⟨N, hN⟩ := tRead_resultant_deform Q S hsf
  have haane : ∀ α ∈ (toPolynomial Q).roots.toFinset,
      algebraMap (Polynomial R) (RatFunc R) (toPolynomial (zEval α S)) ≠ 0 := by
    intro α hα
    rw [toPolynomial_zEval]
    exact RatFunc.algebraMap_ne_zero (hS α (Multiset.mem_toFinset.mp hα))
  have hLrne : algebraMap (Polynomial R) (RatFunc R)
      (Polynomial.C (toPolynomial Q).leadingCoeff) ≠ 0 :=
    RatFunc.algebraMap_ne_zero
      (Polynomial.C_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hsf.ne_zero))
  simp only [rootSumDeriv]
  rw [DenseFrac.toRatFunc_normalize, ← tRead_coeff, ← tRead_coeff, hN, kConst_apply,
    ← Polynomial.C_pow, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
    coeff_zero_prod_C_add_C_mul_X, coeff_one_prod_C_add_C_mul_X,
    mul_div_mul_left _ _ (pow_ne_zero N hLrne),
    sum_mul_prod_erase_div_prod _ _ _ haane]
  simp only [lrtPairTerm, rootSum]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [← toPolynomial_zEval, mul_div_assoc]
  congr 1
  rw [Differential.logDeriv]
  congr 1
  show algebraMap (Polynomial R) (RatFunc R) (toPolynomial (zEval α (S′)))
      = SymbolicIntegration.ratFuncDeriv
          (algebraMap (Polynomial R) (RatFunc R) (toPolynomial (zEval α S)))
  rw [SymbolicIntegration.ratFuncDeriv_algebraMap]
  congr 1
  rw [toPolynomial_zEval, toPolynomial_zEval, Polynomial.derivative_map,
    ← toPolynomial₂_deriv]

/-- The denotation of a sum of root-sum derivatives is the sum of the pair terms. -/
private theorem toRatFunc_sum_rootSumDeriv
    (l : List (DensePoly R × DensePoly (DensePoly R)))
    (hsf : ∀ t ∈ l, Squarefree t.1)
    (hS : ∀ QS ∈ l, ∀ α ∈ (toPolynomial QS.1).roots,
      (toPolynomial₂ QS.2).map (Polynomial.evalRingHom α) ≠ 0) :
    DenseFrac.toRatFunc ((l.map (fun QS => rootSumDeriv QS.1 QS.2)).sum)
      = (l.map lrtPairTerm).sum := by
  induction l with
  | nil => simp
  | cons QS rest ih =>
      obtain ⟨Q, S⟩ := QS
      rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons,
        DenseFrac.toRatFunc_add,
        toRatFunc_rootSumDeriv Q S
          (squarefree_toPolynomial_iff.mpr (hsf (Q, S) List.mem_cons_self))
          (hS (Q, S) List.mem_cons_self),
        ih (fun t ht => hsf t (List.mem_cons_of_mem _ ht))
          (fun t ht => hS t (List.mem_cons_of_mem _ ht))]

/-- **The log-data square**: the computable derivative of an LRT record denotes the
derivative of the represented sum of logarithms, given the produced-pair nonvanishing
contract. -/
theorem ResultLrt.toRatFunc_deriv (res : ResultLrt R)
    (hS : ∀ QS ∈ res.terms, ∀ α ∈ (toPolynomial QS.1).roots,
      (toPolynomial₂ QS.2).map (Polynomial.evalRingHom α) ≠ 0) :
    DenseFrac.toRatFunc res.deriv = (res.terms.map lrtPairTerm).sum :=
  toRatFunc_sum_rootSumDeriv res.terms
    (fun t ht => (res.fst_squarefree t ht).1) hS

/-- **The integral-record square**: the computable derivative of a rational-integral
record denotes the derivative of the represented antiderivative
`rational + ∫poly + ∑ᵢ ∑_{Qᵢ(α)=0} α · log Sᵢ(α, x)`, given the log-data
nonvanishing contract. -/
theorem ResultRatIntegral.toRatFunc_deriv (res : ResultRatIntegral R)
    (hS : ∀ QS ∈ res.logs.terms, ∀ α ∈ (toPolynomial QS.1).roots,
      (toPolynomial₂ QS.2).map (Polynomial.evalRingHom α) ≠ 0) :
    DenseFrac.toRatFunc res.deriv
      = DenseFrac.toRatFunc (res.rational′) + toRatFuncHom (res.poly′)
        + (res.logs.terms.map lrtPairTerm).sum := by
  rw [ResultRatIntegral.deriv, DenseFrac.toRatFunc_add,
    DenseFrac.toRatFunc_add, DenseFrac.toRatFunc_ofPoly,
    ResultLrt.toRatFunc_deriv res.logs hS, toRatFuncHom_apply]

variable [DensePolySquarefree R]

/-- **The nonvanishing contract holds for the LRT stage's own output**: every produced
log argument is similar to a Rothstein–Trager residue gcd, hence nonzero. -/
theorem lrtIntegrate_pairs_ne_zero (g : DenseFrac R)
    (hsf : Squarefree g.den.toPoly)
    (hprop : RatFunc.IsProper (DenseFrac.toRatFunc g)) :
    ∀ QS ∈ (lrtIntegrate g).terms, ∀ α ∈ (toPolynomial QS.1).roots,
      (toPolynomial₂ QS.2).map (Polynomial.evalRingHom α) ≠ 0 := by
  intro QS hQS α hα
  have hnum : g.num ≠ 0 := by
    intro h0
    rw [(lrtIntegrate_terms_eq_nil_iff g hsf hprop).mpr h0] at hQS
    exact absurd hQS List.not_mem_nil
  have hden0 : g.den.toPoly ≠ 0 := g.den.ne_zero
  have hdeg := RatFunc.degree_lt_of_isProper_of_eq_div (toPolynomial_ne_zero hden0)
    (x := DenseFrac.toRatFunc g) rfl hprop
  have hbd : g.num.size < g.den.toPoly.size := by
    have hn0 : toPolynomial g.num ≠ 0 := toPolynomial_ne_zero hnum
    have hdeg' : (toPolynomial g.num).natDegree
        < (toPolynomial g.den.toPoly).natDegree :=
      Polynomial.natDegree_lt_natDegree hn0 hdeg
    rw [natDegree_toPolynomial_eq_size_sub_one, natDegree_toPolynomial_eq_size_sub_one]
      at hdeg'
    have h1 : g.num.size ≠ 0 := fun hz => hnum (eq_zero_of_size_zero hz)
    have h2 : g.den.toPoly.size ≠ 0 := fun hz => hden0 (eq_zero_of_size_zero hz)
    omega
  have hd2 : 2 ≤ g.den.toPoly.size := by
    have h1 : g.num.size ≠ 0 := fun hz => hnum (eq_zero_of_size_zero hz)
    omega
  have hsep : (toPolynomial g.den.toPoly).Separable :=
    (PerfectField.separable_iff_squarefree).mpr (squarefree_toPolynomial_iff.mpr hsf)
  obtain ⟨a, b, ha, hb, heq⟩ := lrtLogTerms_isSimilar_gcd g.num g.den.toPoly hd2 hbd hsep
    hQS (Polynomial.isRoot_of_mem_roots hα)
  have hA : (toPolynomial g.num).natDegree < (toPolynomial g.den.toPoly).natDegree := by
    rw [natDegree_toPolynomial_eq_size_sub_one, natDegree_toPolynomial_eq_size_sub_one]
    have h1 : g.num.size ≠ 0 := fun hz => hnum (eq_zero_of_size_zero hz)
    omega
  have hgne : SymbolicIntegration.rtLogGcd (toPolynomial g.num)
      (toPolynomial g.den.toPoly) α ≠ 0 :=
    SymbolicIntegration.rtData_gcdVal (toPolynomial g.num) (toPolynomial g.den.toPoly)
        hsep hA α ▸
      (SymbolicIntegration.rtData (toPolynomial g.num) (toPolynomial g.den.toPoly)
        hsep hA α).ne_zero
  intro hmap0
  rw [hmap0, mul_zero] at heq
  exact mul_ne_zero (Polynomial.C_ne_zero.mpr hb) hgne heq.symm

/-- **Soundness of the bundled LRT stage**, data-level: `D(∫ g) = g` as an equation
between canonical fractions. The hypotheses are exactly `hermiteReduce`'s exports; the
zero fraction is covered by the empty record. -/
theorem lrtIntegrate_sound (g : DenseFrac R)
    (hsf : Squarefree g.den.toPoly)
    (hprop : RatFunc.IsProper (DenseFrac.toRatFunc g)) :
    (lrtIntegrate g).deriv = g := by
  apply DenseFrac.toRatFunc_injective
  rw [ResultLrt.toRatFunc_deriv (lrtIntegrate g) (lrtIntegrate_pairs_ne_zero g hsf hprop)]
  rcases eq_or_ne g.num 0 with hnum0 | hnum0
  · have hnil := (lrtIntegrate_terms_eq_nil_iff g hsf hprop).mpr hnum0
    rw [hnil, List.map_nil, List.sum_nil, DenseFrac.eq_zero_of_num_eq_zero hnum0,
      DenseFrac.toRatFunc_zero]
  · exact lrtIntegrate_pairTerm_sum g hnum0 hsf hprop

/-- **Completeness of the bundled LRT stage**, data-level: every proper fraction with
squarefree denominator has a log-stage integration result whose computable derivative
is the fraction. -/
theorem lrtIntegrate_complete (g : DenseFrac R)
    (hsf : Squarefree g.den.toPoly)
    (hprop : RatFunc.IsProper (DenseFrac.toRatFunc g)) :
    ∃ res : ResultLrt R, res.deriv = g :=
  ⟨lrtIntegrate g, lrtIntegrate_sound g hsf hprop⟩

/-- **Soundness of rational integration**, hypothesis-free and decidable: the computable
derivative of the produced record recovers the input — `D(∫f) = f` as an equation
between canonical fractions. -/
theorem ratIntegrate_sound (f : DenseFrac R) :
    (ratIntegrate f).deriv = f := by
  apply DenseFrac.toRatFunc_injective
  rw [ResultRatIntegral.toRatFunc_deriv (ratIntegrate f)
      (lrtIntegrate_pairs_ne_zero (hermiteReduce f).logPart
        (hermiteReduce f).logPart_den_squarefree
        (hermiteReduce f).logPart_isProper)]
  have hsound := hermiteReduce_sound f
  show DenseFrac.toRatFunc (((hermiteReduce f).rational)′)
      + toRatFuncHom ((polyIntegrate (hermiteReduce f).poly)′)
      + ((lrtIntegrate (hermiteReduce f).logPart).terms.map lrtPairTerm).sum = _
  rw [polyIntegrate_deriv]
  rcases eq_or_ne (hermiteReduce f).logPart.num 0 with hnum0 | hnum0
  · have hnil : (lrtIntegrate (hermiteReduce f).logPart).terms = [] :=
      (lrtIntegrate_terms_eq_nil_iff _ (hermiteReduce f).logPart_den_squarefree
        (hermiteReduce f).logPart_isProper).mpr hnum0
    have hlp0 : DenseFrac.toRatFunc (hermiteReduce f).logPart = 0 := by
      rw [DenseFrac.eq_zero_of_num_eq_zero hnum0, DenseFrac.toRatFunc_zero]
    rw [hnil, List.map_nil, List.sum_nil, hsound, hlp0, add_zero]
  · rw [lrtIntegrate_pairTerm_sum _ hnum0 (hermiteReduce f).logPart_den_squarefree
      (hermiteReduce f).logPart_isProper]
    exact hsound.symm

/-- **Completeness of rational integration**, data-level: every canonical fraction has
an integration result whose computable derivative is the fraction — rational functions
never fail to integrate, and `ratIntegrate` produces the witness. -/
theorem ratIntegrate_complete (f : DenseFrac R) :
    ∃ res : ResultRatIntegral R, res.deriv = f :=
  ⟨ratIntegrate f, ratIntegrate_sound f⟩

end Closure

end DensePoly

end DeepWiki.CAlgebra
