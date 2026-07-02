import DeepWiki.SymbolicIntegration.Computable.Algebraic.GeneralIntegralSoundness

/-! # Integration on a reducible curve: function-algebra soundness

`D(∫f) = f` over a squarefree but possibly reducible curve `T` — the function algebra
`A = k(x)[y]/(T)`, an étale algebra with zero divisors. When `T = T₁···Tₘ`, CRT gives `A ≅ ∏ᵢ Aᵢ`
with idempotent indicators `eᵢ` (`Σ eᵢ = 1`); a derivation kills idempotents
(`derivation_idempotent_eq_zero`), so the recombined integral `F = Σᵢ eᵢ·Fᵢ` of per-component
integrals `Fᵢ` satisfies `D(F) = f` (`derivation_recombine_eq` abstractly,
`afIntegrateFunctionAlgebra_sound` for the engine's `afDerivWf` over `K[X] ⧸ afIdeal T`). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open scoped Differential

/-! ## The abstract framework: a derivation kills idempotents, so recombination is sound

Three facts about a derivation `D` on any commutative ring: a derivation kills any idempotent;
hence `D(e·F) = e·D(F)` for an idempotent `e`; and a sum `Σ eᵢ·Fᵢ` over a partition of unity by
idempotents with per-component soundness `eᵢ·D(Fᵢ) = eᵢ·g` differentiates to `g`. No field,
reducedness, or irreducibility hypotheses. -/

namespace FunctionAlgebra

variable {R Q : Type*} [CommRing R] [CommRing Q] [Algebra R Q] (D : Derivation R Q Q)

/-- A derivation kills an idempotent: for any `Derivation R Q Q` on a commutative ring `Q` and any
idempotent `e` (`e * e = e`), `D e = 0`. From `e² = e`, Leibniz gives `D e = 2·(e·D e)`, so
`D e · (1 − 2e) = 0`; and `(1 − 2e)² = 1`, so `1 − 2e` is a unit — no `1/2` and no reducedness
needed. The CRT indicator functions of a function algebra are idempotents, so this says the
indicators are constants. -/
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

/-- `D(e·F) = e·D(F)` for an idempotent `e`: Leibniz `D(e·F) = e·D F + F·D e` with `D e = 0`
(`derivation_idempotent_eq_zero`) drops the `F·D e` term — the indicator passes through `D` as a
constant scalar. -/
theorem derivation_eIdx_mul (e F : Q) (he : IsIdempotentElem e) : D (e * F) = e * D F := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, derivation_idempotent_eq_zero D e he, mul_zero,
    add_zero]

/-- Abstract recombination soundness: for a list of `(indicator, component-integral)` pairs over
`Q`, with each indicator `eᵢ` idempotent (`hidem`), the per-component soundness `eᵢ·D(Fᵢ) = eᵢ·g`
(`hcomp`), and the indicators a partition of unity `Σ eᵢ = 1` (`hsum`), the recombined integral
`F = Σ eᵢ·Fᵢ` satisfies `D(F) = g`:
`D(Σ eᵢ Fᵢ) = Σ D(eᵢ Fᵢ) = Σ eᵢ D Fᵢ = Σ eᵢ g = (Σ eᵢ) g = g`. Depends only on the indicators
being idempotent, never on the carrier being a field. -/
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

The carrier quotient is `Q = K[X] ⧸ afIdeal T` (the formal variable `X` is the generator `y`),
where `afIdeal T = (toPolyG T)`. For a squarefree `T` this is the function algebra `A = k(x)[y]/(T)`
(an étale algebra — `toPolyG T` squarefree makes `Q` reduced). The engine derivation `afDerivWf T`
realizes a genuine derivation in `Q` (`mk_toPolyG_afDerivWf`, `mk_toPolyG_afDerivWf_add`,
`mk_toPolyG_afDerivWf_afMul`), so the abstract framework applies. -/

namespace CPolyG

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]

/-- Carrier-form idempotency `IsAfIdempotent T e`: `mk(toPolyG(afMul T e e)) = mk(toPolyG e)` in
`Q = K[X] ⧸ afIdeal T`, i.e. `e² = e` in the function algebra `K(x)[y]/(T)`. The CRT indicator
functions satisfy this. -/
def IsAfIdempotent (f e : CPolyG α) : Prop :=
  Ideal.Quotient.mk (afIdeal f) (toPolyG (afMul f e e))
    = Ideal.Quotient.mk (afIdeal f) (toPolyG e)

omit [CDiffField α] [CDiffFieldSpec α] in
/-- `IsAfIdempotent T e` gives `IsIdempotentElem (mk(toPolyG e))` in `Q = K[X] ⧸ afIdeal T`, by
pushing `afMul` through `mk` (`mk_toPolyG_afMul`): the bridge from the carrier idempotency
predicate to the abstract framework. -/
theorem IsAfIdempotent.isIdempotentElem {f e : CPolyG α} (hf : cnormG f ≠ [])
    (he : IsAfIdempotent f e) :
    IsIdempotentElem (Ideal.Quotient.mk (afIdeal f) (toPolyG e)) := by
  rw [IsIdempotentElem, ← mk_toPolyG_afMul f e e hf, he]

/-- The engine's `afDerivWf` kills a carrier idempotent: for a separable curve `T` (the gcd
`cgcdWf (afFy T) T` is a nonzero constant, with `cnormG T ≠ []`) and an idempotent `e`
(`IsAfIdempotent T e`), `mk(toPolyG(afDerivWf T e)) = 0` in `Q = K[X] ⧸ afIdeal T` — the indicator
function is a constant. The concrete instance of
`FunctionAlgebra.derivation_idempotent_eq_zero` for the engine derivation. -/
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

The recombination `F = Σᵢ eᵢ·Fᵢ` over the CRT indicators `eᵢ` and per-component integrals `Fᵢ` is the
`caddG`-fold of the products `afMul T eᵢ Fᵢ`. Its derivative telescopes through the shared
`mk_toPolyG_afDerivWf_foldlCaddG` additivity theorem, and each per-term `D(eᵢ·Fᵢ) = eᵢ·D(Fᵢ)` by
`idempotent_isConstant` + Leibniz; the per-component soundness `eᵢ·D(Fᵢ) = eᵢ·g` and the partition of unity
`Σ eᵢ = 1` then reassemble `D(F) = g` — the function-algebra `D(∫f) = f`, valid on a **reducible** curve. -/

/-- **The recombination integrator** `afIntegrateFunctionAlgebra T es Fs` — the recombined integral
`F = Σᵢ eᵢ·Fᵢ` of a function algebra `K(x)[y]/(T)`: the `caddG`-fold of the products `afMul T eᵢ Fᵢ` over
the zipped list of CRT indicators `es = [eᵢ]` and per-component integrals `Fs = [Fᵢ]` (each `Fᵢ = ∫(f|_{Aᵢ})`
from the existing per-component integrator on the component function field `Aᵢ = K(x)[y]/(Tᵢ)`). Schultz
§7.2's "combining the component-wise results using the indicator functions". The `afLogSumNumWf`-style fold;
its soundness is `afIntegrateFunctionAlgebra_sound`. -/
def afIntegrateFunctionAlgebra (f : CPolyG α) (es Fs : List (CPolyG α)) : CPolyG α :=
  ((es.zip Fs).map (fun p => afMul f p.1 p.2)).foldl caddG ([] : CPolyG α)

/-- **★★ THE FUNCTION-ALGEBRA (ZERO-DIVISOR) SOUNDNESS — `afIntegrateFunctionAlgebra_sound`: `D(F) =
integrand` over a REDUCIBLE curve, the irreducible-curve caveat REMOVED.** For a **separable** curve `T`
(`hf` plus the fuel-free gcd of `T_y` and `T` being a nonzero constant) — squarefree but **possibly
reducible** (a function algebra, Def 7.1: an étale algebra with zero divisors) — with CRT indicators
`es = [eᵢ]` each idempotent (`hidem`: `IsAfIdempotent T eᵢ`),
per-component integrals `Fs = [Fᵢ]` satisfying the per-component soundness `eᵢ·D(Fᵢ) = eᵢ·integrand`
(`hcomp` — `Fᵢ = ∫(integrand|_{Aᵢ})` from the existing per-component integrator on the component function
field `Aᵢ`), and the indicators a **partition of unity** `Σ eᵢ = 1` (`hsum` — the CRT decomposition), the
recombined integral `F = afIntegrateFunctionAlgebra T es Fs = Σ eᵢ·Fᵢ` satisfies `D(F) = integrand` in the
carrier quotient `Q = K[X] ⧸ afIdeal T`: `mk(toPolyG(afDerivWf T F)) = mk(toPolyG integrand)`.

This is the §7.1–7.2 soundness `D(∫f) = f` over a curve with **zero divisors** — **removing the
"clean only when the extension is a field / the curve irreducible" caveat** of the irreducible-curve
integrator (`ComputableRadicalLogSoundness`). The proof is the concrete `FunctionAlgebra.derivation_recombine_eq`:
additivity over the fold (`mk_toPolyG_afDerivWf_foldlCaddG`), each per-term `D(eᵢ Fᵢ) = eᵢ·D Fᵢ` (Leibniz
`mk_toPolyG_afDerivWf_afMul` + the keystone `idempotent_isConstant` killing `D eᵢ`), the per-component match
`eᵢ·D Fᵢ = eᵢ·integrand` (`hcomp`), and the partition `Σ eᵢ = 1` factoring out `integrand`
(`List.sum_map_mul_right` + `hsum`). Axiom-clean (no `native_decide`). The honest `D(∫f) = f` on a
reducible curve. -/
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

/-! ## ★ Worked Example 7.2 (Schultz §7.2): `∫y dx` on the reducible curve `(y²−x)(y³−x) = 0`

The defining equation `T = (y²−x)(y³−x) = y⁵ − x·y³ − x·y² + x²` is **squarefree but reducible** — a
function algebra with two components, `A₁ = ℚ(x)[y]/(y²−x)` (`y = √x`) and `A₂ = ℚ(x)[y]/(y³−x)`
(`y = x^{1/3}`). To integrate `∫y dx`, Schultz integrates on each component:
`∫y dx = 2xy/3` on `y²−x` and `∫y dx = 3xy/4` on `y³−x`, then recombines via the indicator functions
(Schultz eq. 7.2) to `F = (9x²y + x² − xy³ − 8xy − y⁴)/(12(x−1))` with `D(F) = y mod (y²−x)(y³−x)`.

We validate the two **component integrals** by `native_decide` (the inputs to the recombination); the
recombination soundness `D(F) = y` is the *proven theorem* `afIntegrateFunctionAlgebra_sound` (the degree-5
Wf derivation of the recombined answer over un-reduced `ℚ(x)` is computationally infeasible for `native_decide`
— the honest boundary). -/

namespace CPolyG

open scoped Differential

/-- Component 1's curve `T₁ = y² − x ∈ ℚ(x)[y]` (the `CPolyG (QFunNZG ℚ)` `[−x, 0, 1]`), the function
field `ℚ(x)[√x]` — the first absolutely-irreducible factor of `(y²−x)(y³−x)`. -/
def fa72T1 : CPolyG (QFunNZG ℚ) := [qxOfNum [0, -1], CField.zero, CField.one]

/-- The component-1 integral `F₁ = (2/3)·x·y ∈ ℚ(x)[y]/(y²−x)` (the `CPolyG` `[0, (2/3)x]`): `∫y dx = 2xy/3`
on `y² = x` (`y = √x`, `∫√x dx = (2/3)x^{3/2} = (2/3)x·√x = (2/3)xy`). Schultz §7.2. -/
def fa72F1 : CPolyG (QFunNZG ℚ) := [CField.zero, qxOfNum [0, 2/3]]

/-- Component 2's curve `T₂ = y³ − x ∈ ℚ(x)[y]` (the `CPolyG (QFunNZG ℚ)` `[−x, 0, 0, 1]`), the function
field `ℚ(x)[x^{1/3}]` — the second absolutely-irreducible factor of `(y²−x)(y³−x)`. -/
def fa72T2 : CPolyG (QFunNZG ℚ) := [qxOfNum [0, -1], CField.zero, CField.zero, CField.one]

/-- The component-2 integral `F₂ = (3/4)·x·y ∈ ℚ(x)[y]/(y³−x)` (the `CPolyG` `[0, (3/4)x]`): `∫y dx = 3xy/4`
on `y³ = x` (`y = x^{1/3}`, `∫x^{1/3} dx = (3/4)x^{4/3} = (3/4)x·x^{1/3} = (3/4)xy`). Schultz §7.2. -/
def fa72F2 : CPolyG (QFunNZG ℚ) := [CField.zero, qxOfNum [0, 3/4]]

/-- The integrand `y = [0, 1]` (`afBasisElem 1`) of `∫y dx`. -/
def fa72Y : CPolyG (QFunNZG ℚ) := afBasisElem 1

/-- **★ Example 7.2, component 1 (`native_decide`): `∫y dx = (2/3)·x·y` on `y² − x = 0`** — the general
derivation `afDerivWf (y²−x)` of `F₁ = (2/3)x·y` equals the integrand `y` over `ℚ(x)`: `D((2/3)xy) =
(2/3)(y + x·y') = (2/3)(y + x·(1/(2x))y) = (2/3)(y + (1/2)y) = (2/3)(3/2)y = y` (with `y' = 1/(2y) =
(1/(2x))y` on `y²=x`). Checked by `cisZeroG (afDerivWf (y²−x) F₁ − y)`. The first **component** integral of
Schultz §7.2's function-algebra example — a genuine function-field integral, the input to recombination. -/
theorem fa72_component1 :
    cisZeroG (csubG (afDerivWf fa72T1 fa72F1) fa72Y) = true := by native_decide

/-- **★ Example 7.2, component 2 (`native_decide`): `∫y dx = (3/4)·x·y` on `y³ − x = 0`** — the general
derivation `afDerivWf (y³−x)` of `F₂ = (3/4)x·y` equals the integrand `y` over `ℚ(x)`: `D((3/4)xy) =
(3/4)(y + x·y') = (3/4)(y + x·(1/(3x))y) = (3/4)(y + (1/3)y) = (3/4)(4/3)y = y` (with `y' = 1/(3y²) =
(1/(3x))y` on `y³=x`). Checked by `cisZeroG (afDerivWf (y³−x) F₂ − y)`. The second **component** integral of
Schultz §7.2's function-algebra example. Together with `fa72_component1` and the *proven* recombination
`afIntegrateFunctionAlgebra_sound`, this gives Schultz eq. 7.2's `∫y dx = (9x²y + x² − xy³ − 8xy −
y⁴)/(12(x−1))` on the **reducible** curve `(y²−x)(y³−x)`. -/
theorem fa72_component2 :
    cisZeroG (csubG (afDerivWf fa72T2 fa72F2) fa72Y) = true := by native_decide

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

/-! ## `#print axioms` — the function-algebra (zero-divisor) soundness rests only on the kernel axioms

The abstract framework (the keystone `derivation_idempotent_eq_zero`, `derivation_eIdx_mul`, the
recombination `derivation_recombine_eq`) and the concrete carrier soundness (the keystone
`idempotent_isConstant`, the integrator `afIntegrateFunctionAlgebra`, the capstone
`afIntegrateFunctionAlgebra_sound`) carry **only** the standard `[propext, Classical.choice, Quot.sound]`
— no `native_decide` compiler axiom, no `sorry`. **The irreducible-curve caveat is removed**: `D(∫f) = f`
holds over a squarefree **reducible** curve (a function algebra with zero divisors), because the CRT
indicators are constants (`D(eᵢ) = 0`), which is unconditional in any commutative ring with a derivation.
The worked Example 7.2's component integrals carry the `native_decide` compiler axiom (the inherent
boundary for a concrete computation); the recombination itself is the proven `afIntegrateFunctionAlgebra_sound`. -/

-- ★ The abstract keystone — a derivation kills idempotents (the indicators are constants):
#print axioms FunctionAlgebra.derivation_idempotent_eq_zero
-- ★ The abstract recombination soundness — `D(Σ eᵢ Fᵢ) = g` over a partition of unity by idempotents:
#print axioms FunctionAlgebra.derivation_recombine_eq
-- ★ The concrete keystone — the engine's `afDerivWf` kills a carrier idempotent:
#print axioms CPolyG.idempotent_isConstant
-- ★★ THE FUNCTION-ALGEBRA (ZERO-DIVISOR) SOUNDNESS — `D(F) = integrand` over a REDUCIBLE curve:
#print axioms CPolyG.afIntegrateFunctionAlgebra_sound

end DeepWiki.SymbolicIntegration
