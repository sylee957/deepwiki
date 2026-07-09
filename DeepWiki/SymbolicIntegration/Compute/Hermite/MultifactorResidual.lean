import DeepWiki.Algebra.ListSums
import DeepWiki.SymbolicIntegration.Compute.Hermite.InnerCorrectness
import DeepWiki.SymbolicIntegration.Compute.Hermite.MultifactorIncrements
import DeepWiki.SymbolicIntegration.Compute.Hermite.ResidualCorrectness

/-! # Hermite multifactor residual skeleton
Reduces the multifactor Hermite `g`-fold residual to one polynomial fraction over the global
denominator and isolates the interference-clearing divisibility.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration.Compute

/-! ### The multi-factor `g`-fold interference invariant: toward an unconditional wrapper

The per-factor `gloc` increments and the conditional-fold normalization live in
`Compute.HermiteMultifactorIncrements`. This file starts from the residual identities those increments
satisfy and develops the interference divisibility that clears the global residual to `Dstar`. -/

/-! ### The per-factor residual identity: each increment reduces the *global* `A/D`

For a kept factor `(Vi, i)` (`i ≥ 2`, so `i = (i−1)+1`), with `U = D/Vi^i` reconciled exactly
(`am D = am U·am Vi^i`, from `Vi^i ∣ D`), `hermiteInner_spec_of` reads as
`(toQFun glocᵢ)′ = am A/am D − am Afinalᵢ/(am U·am Vi)`. So with `T = am A/am D`, each increment reduces
the *same* global `T`, leaving the per-factor residual `residᵢ = am Afinalᵢ/(am U·am Vi)` — exactly the
shape `foldl_residual_eq` consumes. The reconciliation `am D = am U·am Vi^i` is the exact-division
content `Vi^i ∣ D` (`am_eq_cdiv_mul_of_cmod_zero`), supplied here as a hypothesis. -/

/-- The `glocIncr` denominator `Uᵢ·Vi` (the per-factor residual denominator): for the kept factor
`(Vi, i)` with `Uᵢ = D/Vi^i`, the residual fraction `residᵢ` has denominator `am Uᵢ·am Vi`. -/
noncomputable def glocResidDen (fuel : ℕ) (D : CPolyQ) (Vi : CPolyQ × ℕ) : RatFunc ℚ :=
  let Vi_pow := (List.range Vi.2).foldl (fun acc _ => cmul acc Vi.1) [1]
  algebraMap ℚ[X] (RatFunc ℚ) (toPoly (cdiv fuel D Vi_pow))
    * algebraMap ℚ[X] (RatFunc ℚ) (toPoly Vi.1)

open scoped Differential in
/-- **The per-factor residual identity** in `RatFunc ℚ`: for a kept factor `(Vi, i)` with `i = j+2`
(so `i ≥ 2`), `Uᵢ = D/Vi^i` reconciled exactly (`hDrec : am D = am Uᵢ·am Vi^i`), and the Bézout/nonzero
side conditions of `hermiteInner_spec_of`, the increment derivative reduces the global `T = am A/am D`:
`(toQFun (glocIncr fuel A D (Vi, j+2)))′ = am A/am D − am Afinalᵢ/(am Uᵢ·am Vi)`, where `Afinalᵢ =
(hermiteInner fuel Vi Uᵢ (j+1) A qzero).2`. The single `hermiteInner_spec_of` term cast onto the global
denominator via the reconciliation. -/
theorem glocIncr_residual (fuel : ℕ) (A D : CPolyQ) (Vi : CPolyQ) (j : ℕ)
    (hU : toPoly (cdiv fuel D ((List.range (j + 2)).foldl (fun acc _ => cmul acc Vi) [1])) ≠ 0)
    (hV : toPoly Vi ≠ 0)
    (hbez : IsHermiteInnerBezoutInput fuel Vi
      (cdiv fuel D ((List.range (j + 2)).foldl (fun acc _ => cmul acc Vi) [1])))
    (hDrec : algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
      = algebraMap ℚ[X] (RatFunc ℚ) (toPoly (cdiv fuel D
          ((List.range (j + 2)).foldl (fun acc _ => cmul acc Vi) [1])))
        * algebraMap ℚ[X] (RatFunc ℚ) (toPoly Vi) ^ (j + 2)) :
    (toQFun (glocIncr fuel A D (Vi, j + 2)))′
      = algebraMap ℚ[X] (RatFunc ℚ) (toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
        - algebraMap ℚ[X] (RatFunc ℚ)
            (toPoly (hermiteInner fuel Vi (cdiv fuel D
              ((List.range (j + 2)).foldl (fun acc _ => cmul acc Vi) [1])) (j + 1) A qzero).2)
          / glocResidDen fuel D (Vi, j + 2) := by
  set U := cdiv fuel D ((List.range (j + 2)).foldl (fun acc _ => cmul acc Vi) [1]) with hUdef
  have hspec := hermiteInner_spec_of fuel Vi U hU hV hbez (j + 1) A
  -- `glocIncr fuel A D (Vi, j+2) = (hermiteInner fuel Vi U (j+1) A qzero).1` (since `(j+2)-1 = j+1`).
  have hgloc : glocIncr fuel A D (Vi, j + 2)
      = (hermiteInner fuel Vi U (j + 1) A qzero).1 := by
    show (hermiteInner fuel Vi U (j + 2 - 1) A qzero).1
        = (hermiteInner fuel Vi U (j + 1) A qzero).1
    rw [show j + 2 - 1 = j + 1 from rfl]
  rw [hgloc, glocResidDen]
  -- in `hspec`, `(j+1)+1 = j+2`; rewrite the global denominator via the reconciliation.
  rw [show j + 1 + 1 = j + 2 from rfl] at hspec
  rw [← hDrec] at hspec
  -- `hspec : A/D = gloc′ + Afinal/(U·Vi)`, so `gloc′ = A/D − Afinal/(U·Vi)`.
  rw [eq_sub_iff_add_eq, hUdef]
  linear_combination -hspec

/-! ### The total fold residual: `(1−n)·T + Σᵢ residᵢ` over the kept-factor list

Combining `foldl_cond_eq_foldl_glocList` (the conditional fold is a `qadd`-fold over `glocList`),
`deriv_toQFun_foldl_qadd` (the fold derivative is the sum of the increment derivatives), and
`glocIncr_residual` (each increment reduces the global `T`), the total residual `T − (toQFun g)′` of
the whole `g`-fold is `(1 − n)·T + Σᵢ residᵢ`, with `n` the number of kept factors and `residᵢ =
am Afinalᵢ/(am Uᵢ·am Vi)`. This is the honest `foldl_residual_eq` skeleton evaluated on `hermiteReduce`'s
actual `g`-fold; the remaining content (the interference clearing) is that this telescopes to a single
fraction over the squarefree radical `Dstar`. -/

open scoped Differential in
/-- **The total `g`-fold residual** in `RatFunc ℚ`: with `T = am A/am D`, if every kept factor `(Vi, i)`
of `factors` satisfies the per-factor residual identity `(toQFun (glocIncr fuel A D Vi))′ = T − resid Vi`
(the conclusion of `glocIncr_residual`, supplied as `hstep`), then the residual of the conditional
`g`-fold (`= (glocList fuel A D factors).foldl qadd qzero`) is
`T − (toQFun g)′ = T − (#kept)•T + Σ_{kept} resid Vi`. The exact overcounting skeleton: `#kept`
increments each reduce the whole `T`, so the fold overcounts by `(#kept − 1)` copies of `T`, which the
`Σ resid` interference must clear. -/
theorem total_fold_residual (fuel : ℕ) (A D : CPolyQ) (factors : List (CPolyQ × ℕ))
    (T : RatFunc ℚ) (resid : CPolyQ × ℕ → RatFunc ℚ)
    (hV : ∀ Vi ∈ factors, toPoly Vi.1 ≠ 0)
    (hstep : ∀ Vi ∈ factors, 2 ≤ Vi.2 →
      (toQFun (glocIncr fuel A D Vi))′ = T - resid Vi) :
    T - (toQFun ((glocList fuel A D factors).foldl qadd qzero))′
      = T - (factors.filter (fun Vi => decide (2 ≤ Vi.2))).length • T
        + ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).map resid).sum := by
  set kept := factors.filter (fun Vi => decide (2 ≤ Vi.2)) with hkept
  -- denominators of the increments are nonzero.
  have hden : ∀ g ∈ glocList fuel A D factors, toPoly g.2 ≠ 0 := by
    intro g hg
    rw [glocList, List.mem_map] at hg
    obtain ⟨Vi, hViMem, rfl⟩ := hg
    rw [← hkept] at hViMem
    have hViF : Vi ∈ factors := List.mem_of_mem_filter hViMem
    exact glocIncr_den_ne_zero fuel A D Vi (hV Vi hViF)
  -- the fold derivative is the sum of the increment derivatives.
  rw [deriv_toQFun_foldl_qadd (glocList fuel A D factors) hden]
  -- rewrite the increment-derivative list over the kept-factor list, applying `hstep`.
  rw [glocList, List.map_map]
  have hmapeq : kept.map ((fun g => (toQFun g)′) ∘ glocIncr fuel A D)
      = kept.map (fun Vi => T - resid Vi) := by
    refine List.map_congr_left (fun Vi hVi => ?_)
    have hViF : Vi ∈ factors := List.mem_of_mem_filter hVi
    have h2 : 2 ≤ Vi.2 := by simpa using (List.mem_filter.mp hVi).2
    simp only [Function.comp_apply]
    exact hstep Vi hViF h2
  rw [hmapeq, list_sum_map_const_sub]
  abel

/-! ### The per-factor residual over the *global* denominator `D`

`glocIncr_residual`'s `residᵢ = am Afinalᵢ/(am Uᵢ·am Vi)` is recast over the *common* denominator `am D`:
since `am D = am Uᵢ·am Vi^{i}` (`i = j+2`) and `am Vi^{i} = am Vi^{i−1}·am Vi`, the denominator
`am Uᵢ·am Vi = am D/am Vi^{i−1}`, so `residᵢ = am (Afinalᵢ·Vi^{i−1})/am D`. This lets the total residual
`(1−n)·T + Σᵢ residᵢ` be written as a *single* fraction `R/am D` with polynomial numerator `R =
(1−n)·A + Σᵢ Afinalᵢ·Vi^{i−1}` — the form whose numerator must be divisible by `am (D/Dstar)` for the
interference to clear to denominator `Dstar`. -/

open scoped Differential in
/-- **The per-factor residual over `D`**: for a kept factor `(Vi, i)` with `i = j+2`, the residual
`residᵢ = am Afinalᵢ/(am Uᵢ·am Vi)` of `glocIncr_residual` equals `am (Afinalᵢ·Vi^{i−1})/am D` over the
global denominator, given the reconciliation `am D = am Uᵢ·am Vi^{i}` and `D, Vi ≠ 0`. The numerator is
`Afinalᵢ` raised through the factor power `Vi^{j+1} = Vi^{i−1}` — the per-factor contribution to the
single-fraction-over-`D` numerator. -/
theorem glocResidDen_eq_over_D (fuel : ℕ) (D : CPolyQ) (Vi : CPolyQ) (j : ℕ)
    (Afinal : CPolyQ) (hD : toPoly D ≠ 0) (hV : toPoly Vi ≠ 0)
    (hU : toPoly (cdiv fuel D ((List.range (j + 2)).foldl (fun acc _ => cmul acc Vi) [1])) ≠ 0)
    (hDrec : algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
      = algebraMap ℚ[X] (RatFunc ℚ) (toPoly (cdiv fuel D
          ((List.range (j + 2)).foldl (fun acc _ => cmul acc Vi) [1])))
        * algebraMap ℚ[X] (RatFunc ℚ) (toPoly Vi) ^ (j + 2)) :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly Afinal) / glocResidDen fuel D (Vi, j + 2)
      = algebraMap ℚ[X] (RatFunc ℚ) (toPoly Afinal * toPoly Vi ^ (j + 1))
        / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D) := by
  have hinj := RatFunc.algebraMap_injective (K := ℚ)
  set am := algebraMap ℚ[X] (RatFunc ℚ) with hamdef
  set U := cdiv fuel D ((List.range (j + 2)).foldl (fun acc _ => cmul acc Vi) [1]) with hUdef
  have hd : am (toPoly D) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hD
  have hv : am (toPoly Vi) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hV
  have hu : am (toPoly U) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hU
  -- the residual denominator `am U·am Vi`; `glocResidDen (Vi, j+2)` uses exactly this `U`.
  have hresD : glocResidDen fuel D (Vi, j + 2) = am (toPoly U) * am (toPoly Vi) := by
    rw [glocResidDen, hUdef]
  rw [hresD]
  -- `am D = am U · am Vi^(j+2) = (am U·am Vi)·am Vi^(j+1)`.
  have hDfact : am (toPoly D) = (am (toPoly U) * am (toPoly Vi)) * am (toPoly Vi) ^ (j + 1) := by
    rw [hDrec]; ring
  rw [map_mul, map_pow, hDfact]
  have hVip : am (toPoly Vi) ^ (j + 1) ≠ 0 := pow_ne_zero _ hv
  field_simp

/-! ### The total residual as a single fraction over `D`

The kept-factor residuals all share the global denominator `am D` (`glocResidDen_eq_over_D`), so their
sum is a single fraction `am (Σᵢ Afinalᵢ·Vi^{i−1})/am D`, and the `(1−n)·T` overcounting term is
`am (C(1−n)·A)/am D`. Hence the *entire* fold residual is `am R/am D` with the polynomial numerator
`R = C(1−n)·A + Σᵢ Afinalᵢ·Vi^{i−1}` — the exact single-fraction-over-`D` form. The interference clears
to denominator `Dstar` precisely when `am (D/Dstar) ∣ am R`, the **named open divisibility** below. -/

/-- **The per-factor `Afinal`** of `hermiteReduce`'s `g`-fold: the residual numerator
`(hermiteInner fuel Vi Uᵢ (i−1) A qzero).2` left over the radical-reduced denominator after peeling. -/
def afinalIncr (fuel : ℕ) (A D : CPolyQ) (Vi : CPolyQ × ℕ) : CPolyQ :=
  let Vi_pow := (List.range Vi.2).foldl (fun acc _ => cmul acc Vi.1) [1]
  let U := cdiv fuel D Vi_pow
  (hermiteInner fuel Vi.1 U (Vi.2 - 1) A qzero).2

/-- **The per-factor residual numerator over `D`** `residNumIncr fuel A D (Vi, i) = Afinalᵢ·Vi^{i−1}`:
the polynomial numerator the factor `(Vi, i)` contributes to the single-fraction-over-`D` residual
`am (Σᵢ Afinalᵢ·Vi^{i−1})/am D`. -/
noncomputable def residNumIncr (fuel : ℕ) (A D : CPolyQ) (Vi : CPolyQ × ℕ) : ℚ[X] :=
  toPoly (afinalIncr fuel A D Vi) * toPoly Vi.1 ^ (Vi.2 - 1)

open scoped Differential in
/-- **The total `g`-fold residual as a single fraction over `D`**: under per-factor hypotheses
(`hstep`, the conclusion of `glocIncr_residual` recast over `D` by `glocResidDen_eq_over_D`) for every
kept factor `(Vi, i)`, the entire residual of `hermiteReduce`'s `g`-fold is
`am A/am D − (toQFun g)′ = am R/am D`, where `R = C(1−n)·A + Σ_{kept} residNumIncr` is a single
polynomial (`n` = #kept). This is the honest single-fraction-over-`D` form of the multi-factor
interference: the whole fold residual is one polynomial fraction over the global `D`; the remaining
content (clearing to denominator `Dstar`) is the divisibility `am (D/Dstar) ∣ am R`. -/
theorem total_fold_residual_over_D (fuel : ℕ) (A D : CPolyQ) (factors : List (CPolyQ × ℕ))
    (hD : toPoly D ≠ 0) (hV : ∀ Vi ∈ factors, toPoly Vi.1 ≠ 0)
    (hstep : ∀ Vi ∈ factors, 2 ≤ Vi.2 →
      (toQFun (glocIncr fuel A D Vi))′
        = algebraMap ℚ[X] (RatFunc ℚ) (toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
          - algebraMap ℚ[X] (RatFunc ℚ) (residNumIncr fuel A D Vi)
            / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)) :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
        - (toQFun ((glocList fuel A D factors).foldl qadd qzero))′
      = algebraMap ℚ[X] (RatFunc ℚ)
          (Polynomial.C (1 - ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).length : ℚ)) * toPoly A
            + ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).map (residNumIncr fuel A D)).sum)
        / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D) := by
  set am := algebraMap ℚ[X] (RatFunc ℚ) with hamdef
  set T := am (toPoly A) / am (toPoly D) with hT
  set kept := factors.filter (fun Vi => decide (2 ≤ Vi.2)) with hkept
  set n := kept.length with hn
  have hinj := RatFunc.algebraMap_injective (K := ℚ)
  have hd : am (toPoly D) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hD
  -- apply `total_fold_residual` with `resid Vi = am (residNumIncr Vi)/am D`.
  have htot := total_fold_residual fuel A D factors T
    (fun Vi => am (residNumIncr fuel A D Vi) / am (toPoly D)) hV
    (fun Vi hViF h2 => hstep Vi hViF h2)
  rw [← hkept, ← hn] at htot
  rw [htot]
  -- the residual sum over the common denominator `am D`.
  rw [ratFunc_list_sum_algebraMap_div_const kept (residNumIncr fuel A D) (am (toPoly D))]
  -- the `(1 − n)·T` overcounting term as a fraction over `am D`.
  rw [map_add]
  -- `am (C(1−n)·A) = (1 − n)·am A` and `n • T = n·am A/am D`.
  have hCcast : am (Polynomial.C (1 - (n : ℚ))) = 1 - (n : RatFunc ℚ) := by
    rw [hamdef, ← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply ℚ ℚ[X] (RatFunc ℚ),
      map_sub, map_one, map_natCast]
  have hC : am (Polynomial.C (1 - (n : ℚ)) * toPoly A) = (1 - (n : RatFunc ℚ)) * am (toPoly A) := by
    rw [map_mul, hCcast]
  rw [hC, show n • T = (n : RatFunc ℚ) * T from by rw [nsmul_eq_mul], hT]
  field_simp
  ring

/-! ### Clearing the over-`D` fraction to denominator `Dstar` (the interference divisibility)

`total_fold_residual_over_D` reduces the whole fold residual to `am R/am D`. Since the radical `Dstar`
divides `D` (`toPoly_Dstar_dvd_D`/the Yun radical clause), write `D = Dstar·W`. Then `am R/am D = am
(R/W)/am Dstar` **exactly when `W ∣ R`** — the single named interference divisibility. The lemma below
performs this final cancellation: given `D = Dstar·W` and `W ∣ R`, the over-`D` fraction collapses to a
polynomial fraction over `Dstar`. -/

/-- **Clearing `am R/am D` to `am (R/W)/am Dstar`** given `D = Dstar·W` and `W ∣ R` (`W = D/Dstar`):
the over-`D` residual fraction collapses to a fraction over the radical `Dstar`. The single divisibility
`W ∣ R` is the entire remaining interference-clearing content. -/
theorem am_div_D_eq_div_Dstar {R D Dstar W : ℚ[X]} (hD : D ≠ 0) (hDstar : Dstar ≠ 0)
    (hW : D = Dstar * W) (hWR : W ∣ R) :
    algebraMap ℚ[X] (RatFunc ℚ) R / algebraMap ℚ[X] (RatFunc ℚ) D
      = algebraMap ℚ[X] (RatFunc ℚ) (R / W) / algebraMap ℚ[X] (RatFunc ℚ) Dstar := by
  have hinj := RatFunc.algebraMap_injective (K := ℚ)
  set am := algebraMap ℚ[X] (RatFunc ℚ) with hamdef
  have hW0 : W ≠ 0 := by
    rintro rfl; rw [mul_zero] at hW; exact hD hW
  obtain ⟨S, hS⟩ := hWR
  have hRdivW : R / W = S := by rw [hS, mul_comm, mul_div_cancel_right₀ _ hW0]
  have hdstar : am Dstar ≠ 0 := (map_ne_zero_iff _ hinj).mpr hDstar
  have hw : am W ≠ 0 := (map_ne_zero_iff _ hinj).mpr hW0
  rw [hRdivW, hW, hS, map_mul, map_mul]
  field_simp

/-! ### The multi-factor wrapper, reduced to ONE interference divisibility

Assembling `total_fold_residual_over_D` (the whole residual as `am R/am D`) with `am_div_D_eq_div_Dstar`
(the clearing to `Dstar`) gives the residual identity `am A/am D = (toQFun g)′ + am (R/W)/am Dstar` for
the actual `g`-fold — from the per-factor residual identities (`hstep`, dischargeable by
`glocIncr_residual`), the **proven** radical clause `Dstar ∣ D` (`toPoly_Dstar_dvd_D`), and the **single
remaining** interference divisibility `W ∣ R` (`W = D/Dstar`). This is the cleanest multi-factor
wrapper: everything but `W ∣ R` is proven; that one divisibility is the genuine interference-clearing
content (decidably true per example, abstractly the open piece). -/

open scoped Differential in
/-- **Multi-factor `hermiteReduce` wrapper, reduced to the interference divisibility** in `RatFunc ℚ`:
for the actual `g`-fold `g = (glocList fuel A D factors).foldl qadd qzero`, given the per-factor residual
identities (`hstep`, the `glocIncr_residual` conclusion over `D`), the radical decomposition
`D = Dstar·W` (`Dstar ∣ D`, **proven** Yun radical clause), and the **single** interference divisibility
`W ∣ R` with `R = C(1−n)·A + Σ residNumIncr` and `n = #kept`, the reduction is correct:
`am A/am D = (toQFun g)′ + am (R/W)/am Dstar`. The residual integrand lives over the squarefree radical
`Dstar`. Only `W ∣ R` is unproven here — the abstract multi-factor interference-clearing content. -/
theorem hermiteReduce_residual_correct_multifactor (fuel : ℕ) (A D Dstar W : CPolyQ)
    (factors : List (CPolyQ × ℕ))
    (hD : toPoly D ≠ 0) (hDstar : toPoly Dstar ≠ 0)
    (hV : ∀ Vi ∈ factors, toPoly Vi.1 ≠ 0)
    (hstep : ∀ Vi ∈ factors, 2 ≤ Vi.2 →
      (toQFun (glocIncr fuel A D Vi))′
        = algebraMap ℚ[X] (RatFunc ℚ) (toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
          - algebraMap ℚ[X] (RatFunc ℚ) (residNumIncr fuel A D Vi)
            / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D))
    (hWdec : toPoly D = toPoly Dstar * toPoly W)
    (hWR : toPoly W ∣ Polynomial.C (1 - ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).length : ℚ))
        * toPoly A
        + ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).map (residNumIncr fuel A D)).sum) :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
      = (toQFun ((glocList fuel A D factors).foldl qadd qzero))′
        + algebraMap ℚ[X] (RatFunc ℚ)
            ((Polynomial.C (1 - ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).length : ℚ))
                * toPoly A
              + ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).map (residNumIncr fuel A D)).sum)
              / toPoly W)
          / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Dstar) := by
  set R := Polynomial.C (1 - ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).length : ℚ)) * toPoly A
    + ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).map (residNumIncr fuel A D)).sum with hR
  have hres := total_fold_residual_over_D fuel A D factors hD hV hstep
  rw [← hR] at hres
  -- `A/D − g′ = am R/am D = am (R/W)/am Dstar`.
  have hclear := am_div_D_eq_div_Dstar (R := R) (D := toPoly D) (Dstar := toPoly Dstar)
    (W := toPoly W) hD hDstar hWdec hWR
  linear_combination hres + hclear

/-! ### Discharging the per-factor `hstep` from the computable certificates

`glocIncr_residual` gives the per-factor identity over `glocResidDen`; `glocResidDen_eq_over_D` recasts
it over the global `D` numerator `residNumIncr`. Combined, one kept factor `(Vi, j+2)` satisfies the
`hstep` shape `total_fold_residual_over_D`/`hermiteReduce_residual_correct_multifactor` consume, from:
the factor's nonzero/`cnorm` conditions, its Bézout side conditions (`cgcdExt` of `U·Vi'` and `Vi` a
nonzero constant — the coprimality `Vi ⊥ U·Vi'`), and the reconciliation `am D = am U·am Vi^{i}`. -/

open scoped Differential in
/-- **One kept-factor `hstep` from the per-factor data**: for `(Vi, j+2)` with `Uᵢ = D/Vi^{j+2}`,
nonzero/`cnorm` conditions, the `hermiteInner` Bézout side conditions (`hg`/`hgc`), and the
reconciliation `hDrec : am D = am Uᵢ·am Vi^{j+2}` (the exactness `Vi^{j+2} ∣ D`), the increment satisfies
`(toQFun (glocIncr fuel A D (Vi, j+2)))′ = am A/am D − am (residNumIncr fuel A D (Vi, j+2))/am D`. The
`hstep` per-factor input to the multi-factor wrapper, discharged for one factor from `glocIncr_residual`
+ `glocResidDen_eq_over_D`. -/
theorem glocIncr_hstep (fuel : ℕ) (A D : CPolyQ) (Vi : CPolyQ) (j : ℕ) (hD : toPoly D ≠ 0)
    (hU : toPoly (cdiv fuel D ((List.range (j + 2)).foldl (fun acc _ => cmul acc Vi) [1])) ≠ 0)
    (hV : toPoly Vi ≠ 0)
    (hbez : IsHermiteInnerBezoutInput fuel Vi
      (cdiv fuel D ((List.range (j + 2)).foldl (fun acc _ => cmul acc Vi) [1])))
    (hDrec : algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
      = algebraMap ℚ[X] (RatFunc ℚ) (toPoly (cdiv fuel D
          ((List.range (j + 2)).foldl (fun acc _ => cmul acc Vi) [1])))
        * algebraMap ℚ[X] (RatFunc ℚ) (toPoly Vi) ^ (j + 2)) :
    (toQFun (glocIncr fuel A D (Vi, j + 2)))′
      = algebraMap ℚ[X] (RatFunc ℚ) (toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
        - algebraMap ℚ[X] (RatFunc ℚ) (residNumIncr fuel A D (Vi, j + 2))
          / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D) := by
  rw [glocIncr_residual fuel A D Vi j hU hV hbez hDrec]
  -- recast the `glocResidDen` fraction over the global `D` numerator `residNumIncr`.
  rw [glocResidDen_eq_over_D fuel D Vi j
    (hermiteInner fuel Vi (cdiv fuel D
      ((List.range (j + 2)).foldl (fun acc _ => cmul acc Vi) [1])) (j + 1) A qzero).2
    hD hV hU hDrec]
  -- `residNumIncr (Vi, j+2) = afinalIncr·Vi^{(j+2)-1} = Afinal·Vi^{j+1}`.
  rw [show residNumIncr fuel A D (Vi, j + 2)
      = toPoly (hermiteInner fuel Vi (cdiv fuel D
          ((List.range (j + 2)).foldl (fun acc _ => cmul acc Vi) [1])) (j + 1) A qzero).2
        * toPoly Vi ^ (j + 1) from rfl]

end DeepWiki.SymbolicIntegration.Compute
