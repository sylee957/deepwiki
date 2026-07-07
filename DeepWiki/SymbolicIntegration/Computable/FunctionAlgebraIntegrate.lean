import DeepWiki.SymbolicIntegration.Computable.Algebraic.GeneralIntegralSoundness

/-! # Integration on a reducible curve: function-algebra soundness

`D(∫f) = f` over a squarefree but possibly reducible curve `T`. A derivation kills the CRT
idempotent indicators, so the recombined integral `F = Σᵢ eᵢ·Fᵢ` satisfies `D(F) = f`
(`derivation_recombine_eq`, `afIntegrateFunctionAlgebra_sound`). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open scoped Differential

/-! ## The abstract framework: a derivation kills idempotents, so recombination is sound

A derivation `D` on any commutative ring kills idempotents, gives `D(e·F) = e·D(F)` for
idempotent `e`, and differentiates `Σ eᵢ·Fᵢ` over a partition of unity to `g`. -/

namespace FunctionAlgebra

variable {R Q : Type*} [CommRing R] [CommRing Q] [Algebra R Q] (D : Derivation R Q Q)

/-- A derivation kills an idempotent: for `D : Derivation R Q Q` and idempotent `e` (`e * e = e`),
`D e = 0`. -/
theorem derivation_idempotent_eq_zero (e : Q) (he : IsIdempotentElem e) : D e = 0 := by
  -- `D e = 2·(e·D e)`, i.e. `D e · (1 − 2e) = 0`
  have h1 : D (e * e) = e * D e + e * D e := by rw [Derivation.leibniz]; simp [smul_eq_mul]
  rw [he.eq] at h1
  have h2 : D e * (1 - 2 * e) = 0 := by linear_combination h1
  -- `(1 − 2e)² = 1`, so `1 − 2e` is its own inverse
  have hsq : (1 - 2 * e) * (1 - 2 * e) = 1 := by linear_combination (4 : Q) * he.eq
  calc D e = D e * ((1 - 2 * e) * (1 - 2 * e)) := by rw [hsq, mul_one]
    _ = (D e * (1 - 2 * e)) * (1 - 2 * e) := by ring
    _ = 0 := by rw [h2, zero_mul]

/-- `D(e·F) = e·D(F)` for an idempotent `e`. -/
theorem derivation_eIdx_mul (e F : Q) (he : IsIdempotentElem e) : D (e * F) = e * D F := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, derivation_idempotent_eq_zero D e he, mul_zero,
    add_zero]

/-- Abstract recombination soundness: over pairs `(eᵢ, Fᵢ)` with each `eᵢ` idempotent, per-component
`eᵢ·D(Fᵢ) = eᵢ·g`, and partition of unity `Σ eᵢ = 1`, the sum `F = Σ eᵢ·Fᵢ` satisfies `D(F) = g`. -/
theorem derivation_recombine_eq (pairs : List (Q × Q)) (g : Q)
    (hidem : ∀ p ∈ pairs, IsIdempotentElem p.1)
    (hcomp : ∀ p ∈ pairs, p.1 * D p.2 = p.1 * g)
    (hsum : (pairs.map (fun p => p.1)).sum = 1) :
    D ((pairs.map (fun p => p.1 * p.2)).sum) = g := by
  rw [map_list_sum]
  -- each `D(eᵢ Fᵢ) = eᵢ D Fᵢ = eᵢ g`
  rw [show (pairs.map (fun p => p.1 * p.2)).map (fun x => D x)
      = pairs.map (fun p => p.1 * g) from by
    rw [List.map_map]
    refine List.map_congr_left (fun p hp => ?_)
    simp only [Function.comp_apply]
    rw [derivation_eIdx_mul D p.1 p.2 (hidem p hp), hcomp p hp]]
  -- `Σ eᵢ g = (Σ eᵢ) g = 1·g = g`
  rw [show (fun p : Q × Q => p.1 * g)
      = (fun p : Q × Q => (fun p : Q × Q => p.1) p * g) from rfl,
    List.sum_map_mul_right, hsum, one_mul]

end FunctionAlgebra

/-! ## The concrete function algebra `K(x)[y]/(T)` and the engine derivation `afDerivWf`

Carrier quotient `Q = K[X] ⧸ afIdeal T`; the engine derivation `afDerivWf T` realizes a genuine
derivation in `Q`, so the abstract framework applies. -/

namespace CPolyG

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]

/-- Carrier-form idempotency `IsAfIdempotent T e`: `mk(toPolyG(afMul T e e)) = mk(toPolyG e)` in
`Q = K[X] ⧸ afIdeal T`, i.e. `e² = e` in `K(x)[y]/(T)`. -/
def IsAfIdempotent (f e : CPolyG α) : Prop :=
  Ideal.Quotient.mk (afIdeal f) (toPolyG (afMul f e e))
    = Ideal.Quotient.mk (afIdeal f) (toPolyG e)

omit [CDiffField α] [CDiffFieldSpec α] in
/-- `IsAfIdempotent T e` gives `IsIdempotentElem (mk(toPolyG e))` in `Q = K[X] ⧸ afIdeal T`. -/
theorem IsAfIdempotent.isIdempotentElem {f e : CPolyG α} (hf : cnormG f ≠ [])
    (he : IsAfIdempotent f e) :
    IsIdempotentElem (Ideal.Quotient.mk (afIdeal f) (toPolyG e)) := by
  rw [IsIdempotentElem, ← mk_toPolyG_afMul f e e hf, he]

/-- The engine's `afDerivWf` kills a carrier idempotent: for a separable curve `T` and idempotent
`e` (`IsAfIdempotent T e`), `mk(toPolyG(afDerivWf T e)) = 0` in `Q = K[X] ⧸ afIdeal T`. -/
theorem idempotent_isConstant (f e : CPolyG α) (hf : cnormG f ≠ [])
    (hgdeg : (toPolyG (cgcdWf (afFy f) f).1).natDegree = 0)
    (hgne : toPolyG (cgcdWf (afFy f) f).1 ≠ 0)
    (he : IsAfIdempotent f e) :
    Ideal.Quotient.mk (afIdeal f) (toPolyG (afDerivWf f e)) = 0 := by
  set ē : (CFieldSpec.K α)[X] ⧸ afIdeal f :=
    Ideal.Quotient.mk (afIdeal f) (toPolyG e) with hē
  set dē : (CFieldSpec.K α)[X] ⧸ afIdeal f :=
    Ideal.Quotient.mk (afIdeal f) (toPolyG (afDerivWf f e)) with hdē
  -- Leibniz at `afDerivWf`: `D(e·e) = e·D e + e·D e` (pushed through `mk`)
  have hleib := mk_toPolyG_afDerivWf_afMul f e e hf hgdeg hgne
  rw [mk_toPolyG_afMul _ _ _ hf, mk_toPolyG_afMul _ _ _ hf] at hleib
  -- `afDerivWf` descends through `e² ≡ e`.
  have hdesc : Ideal.Quotient.mk (afIdeal f) (toPolyG (afDerivWf f (afMul f e e)))
      = Ideal.Quotient.mk (afIdeal f) (toPolyG (afDerivWf f e)) := by
    rw [mk_toPolyG_afDerivWf f _ hf, mk_toPolyG_afDerivWf f e hf]
    exact mk_implicitDerivWf_congr f hf hgdeg hgne he
  rw [hdesc, ← hdē, ← hē] at hleib
  -- the idempotency `ē·ē = ē` in `Q`
  have hidem : ē * ē = ē := he.isIdempotentElem hf
  -- `dē·(1 − 2ē) = 0`, and `(1 − 2ē)² = 1`, so `dē = 0`
  have h2 : dē * (1 - 2 * ē) = 0 := by linear_combination hleib
  have hsq : (1 - 2 * ē) * (1 - 2 * ē) = 1 := by linear_combination (4 : (CFieldSpec.K α)[X] ⧸ afIdeal f) * hidem
  calc dē = dē * ((1 - 2 * ē) * (1 - 2 * ē)) := by rw [hsq, mul_one]
    _ = (dē * (1 - 2 * ē)) * (1 - 2 * ē) := by ring
    _ = 0 := by rw [h2, zero_mul]

/-! ### The recombination integrator and its soundness

The recombination `F = Σᵢ eᵢ·Fᵢ` is the `caddG`-fold of the products `afMul T eᵢ Fᵢ`; its
derivative reassembles to `D(F) = g`, the function-algebra `D(∫f) = f` on a reducible curve. -/

/-- The recombination integrator `afIntegrateFunctionAlgebra T es Fs = Σᵢ eᵢ·Fᵢ`: the `caddG`-fold
of the products `afMul T eᵢ Fᵢ` over the zipped indicators `es` and component integrals `Fs`. -/
def afIntegrateFunctionAlgebra (f : CPolyG α) (es Fs : List (CPolyG α)) : CPolyG α :=
  ((es.zip Fs).map (fun p => afMul f p.1 p.2)).foldl caddG ([] : CPolyG α)

/-- Function-algebra soundness `D(F) = integrand` over a reducible curve: for a separable curve `T`,
CRT indicators `es` each idempotent (`hidem`), per-component integrals `Fs` with
`eᵢ·D(Fᵢ) = eᵢ·integrand` (`hcomp`), and partition of unity `Σ eᵢ = 1` (`hsum`), the recombined
integral `afIntegrateFunctionAlgebra T es Fs` satisfies
`mk(toPolyG(afDerivWf T F)) = mk(toPolyG integrand)` in `Q = K[X] ⧸ afIdeal T`. -/
theorem afIntegrateFunctionAlgebra_sound (f integrand : CPolyG α)
    (es Fs : List (CPolyG α)) (hf : cnormG f ≠ [])
    (hgdeg : (toPolyG (cgcdWf (afFy f) f).1).natDegree = 0)
    (hgne : toPolyG (cgcdWf (afFy f) f).1 ≠ 0)
    (hidem : ∀ p ∈ es.zip Fs, IsAfIdempotent f p.1)
    (hcomp : ∀ p ∈ es.zip Fs,
      Ideal.Quotient.mk (afIdeal f) (toPolyG p.1)
          * Ideal.Quotient.mk (afIdeal f) (toPolyG (afDerivWf f p.2))
        = Ideal.Quotient.mk (afIdeal f) (toPolyG p.1)
          * Ideal.Quotient.mk (afIdeal f) (toPolyG integrand))
    (hsum : ((es.zip Fs).map (fun p => Ideal.Quotient.mk (afIdeal f) (toPolyG p.1))).sum = 1) :
    Ideal.Quotient.mk (afIdeal f) (toPolyG (afDerivWf f (afIntegrateFunctionAlgebra f es Fs)))
      = Ideal.Quotient.mk (afIdeal f) (toPolyG integrand) := by
  rw [afIntegrateFunctionAlgebra, mk_toPolyG_afDerivWf_foldlCaddG f hf]
  -- `afDerivWf` of the empty seed is `0` in the quotient
  rw [mk_toPolyG_afDerivWf_nil f hf, zero_add]
  -- fuse the `map ∘ map` over `es.zip Fs`
  rw [List.map_map]
  -- each term `mk(toPolyG(afDerivWf (afMul eᵢ Fᵢ))) = ēᵢ·integrand`  (Leibniz + `D eᵢ = 0` + `hcomp`)
  rw [List.map_congr_left (g := fun p =>
        Ideal.Quotient.mk (afIdeal f) (toPolyG p.1)
          * Ideal.Quotient.mk (afIdeal f) (toPolyG integrand)) (fun p hp => by
    simp only [Function.comp_apply]
    rw [mk_toPolyG_afDerivWf_afMul f p.1 p.2 hf hgdeg hgne,
      mk_toPolyG_afMul _ _ _ hf, mk_toPolyG_afMul _ _ _ hf,
      idempotent_isConstant f p.1 hf hgdeg hgne (hidem p hp), zero_mul, zero_add]
    exact hcomp p hp)]
  -- `Σ ēᵢ·integrand = (Σ ēᵢ)·integrand = 1·integrand = integrand`
  rw [show (fun p : CPolyG α × CPolyG α =>
        Ideal.Quotient.mk (afIdeal f) (toPolyG p.1)
          * Ideal.Quotient.mk (afIdeal f) (toPolyG integrand))
      = (fun p : CPolyG α × CPolyG α =>
        (fun p : CPolyG α × CPolyG α => Ideal.Quotient.mk (afIdeal f) (toPolyG p.1)) p
          * Ideal.Quotient.mk (afIdeal f) (toPolyG integrand)) from rfl,
    List.sum_map_mul_right, hsum, one_mul]

end CPolyG

/-! ## Worked example: `∫y dx` on the reducible curve `(y²−x)(y³−x) = 0`

The curve `T = (y²−x)(y³−x)` is squarefree but reducible, with components `y²−x` (`y = √x`) and
`y³−x` (`y = x^{1/3}`). The two component integrals `2xy/3` and `3xy/4` are validated by
`native_decide`; the recombination soundness is `afIntegrateFunctionAlgebra_sound`. -/

namespace CPolyG

open scoped Differential

/-- The square-root component curve `T₁ = y² − x ∈ ℚ(x)[y]`. -/
def sqrtComponentCurve : CPolyG (QFunNZG ℚ) := [qxOfNum [0, -1], CField.zero, CField.one]

/-- The square-root component integral `F₁ = (2/3)·x·y`. -/
def sqrtComponentIntegral : CPolyG (QFunNZG ℚ) := [CField.zero, qxOfNum [0, 2/3]]

/-- The cube-root component curve `T₂ = y³ − x ∈ ℚ(x)[y]`. -/
def cubeRootComponentCurve : CPolyG (QFunNZG ℚ) := [qxOfNum [0, -1], CField.zero, CField.zero, CField.one]

/-- The cube-root component integral `F₂ = (3/4)·x·y`. -/
def cubeRootComponentIntegral : CPolyG (QFunNZG ℚ) := [CField.zero, qxOfNum [0, 3/4]]

/-- The integrand `y = [0, 1]` (`afBasisElem 1`) of `∫y dx`. -/
def componentIntegrandY : CPolyG (QFunNZG ℚ) := afBasisElem 1

/-- Component 1 (`native_decide`): `∫y dx = (2/3)·x·y` on `y² − x = 0`, checked by
`cisZeroG (afDerivWf (y²−x) F₁ − y)`. -/
theorem sqrtComponentIntegral_deriv :
    cisZeroG (csubG (afDerivWf sqrtComponentCurve sqrtComponentIntegral) componentIntegrandY) = true := by
  native_decide

/-- Component 2 (`native_decide`): `∫y dx = (3/4)·x·y` on `y³ − x = 0`, checked by
`cisZeroG (afDerivWf (y³−x) F₂ − y)`. -/
theorem cubeRootComponentIntegral_deriv :
    cisZeroG (csubG (afDerivWf cubeRootComponentCurve cubeRootComponentIntegral) componentIntegrandY)
      = true := by
  native_decide

end CPolyG

/-! ### Restatements against the intended wording (anonymous `example`s) -/

-- ★ The keystone (abstract): a derivation kills any idempotent — "the indicators are constants".
example {R Q : Type*} [CommRing R] [CommRing Q] [Algebra R Q] (D : Derivation R Q Q)
    (e : Q) (he : IsIdempotentElem e) : D e = 0 :=
  FunctionAlgebra.derivation_idempotent_eq_zero D e he

-- ★ The recombination soundness (abstract): `D(Σ eᵢ Fᵢ) = g` over a partition of unity by idempotents
-- with the per-component soundness `eᵢ·D Fᵢ = eᵢ·g` — the irreducible-curve caveat removed abstractly.
example {R Q : Type*} [CommRing R] [CommRing Q] [Algebra R Q] (D : Derivation R Q Q)
    (pairs : List (Q × Q)) (g : Q)
    (hidem : ∀ p ∈ pairs, IsIdempotentElem p.1)
    (hcomp : ∀ p ∈ pairs, p.1 * D p.2 = p.1 * g)
    (hsum : (pairs.map (fun p => p.1)).sum = 1) :
    D ((pairs.map (fun p => p.1 * p.2)).sum) = g :=
  FunctionAlgebra.derivation_recombine_eq D pairs g hidem hcomp hsum

-- ★★ The concrete function-algebra (zero-divisor) soundness `D(F) = integrand` over a REDUCIBLE curve is
-- `CPolyG.afIntegrateFunctionAlgebra_sound` (stated above; its `#print axioms` below confirms it is
-- axiom-clean). The recombined integral `F = Σ eᵢ Fᵢ` of the function algebra `K(x)[y]/(T)` differentiates
-- to the integrand in the carrier quotient — the irreducible-curve caveat removed.

/-! ## `#print axioms` — the function-algebra soundness rests only on the kernel axioms

The abstract framework and the concrete carrier soundness carry only
`[propext, Classical.choice, Quot.sound]`; the worked-example component integrals additionally
carry the `native_decide` compiler axiom. -/

-- ★ The abstract keystone — a derivation kills idempotents (the indicators are constants):
#print axioms FunctionAlgebra.derivation_idempotent_eq_zero
-- ★ The abstract recombination soundness — `D(Σ eᵢ Fᵢ) = g` over a partition of unity by idempotents:
#print axioms FunctionAlgebra.derivation_recombine_eq
-- ★ The concrete keystone — the engine's `afDerivWf` kills a carrier idempotent:
#print axioms CPolyG.idempotent_isConstant
-- ★★ THE FUNCTION-ALGEBRA (ZERO-DIVISOR) SOUNDNESS — `D(F) = integrand` over a REDUCIBLE curve:
#print axioms CPolyG.afIntegrateFunctionAlgebra_sound

end DeepWiki.SymbolicIntegration
