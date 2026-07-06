import DeepWiki.Algebra.ListSums
import DeepWiki.Algebra.ListProducts
import DeepWiki.Algebra.PolynomialDivisibility
import DeepWiki.SymbolicIntegration.Compute.Correctness
import DeepWiki.SymbolicIntegration.Compute.Diophantine
import DeepWiki.SymbolicIntegration.Compute.HermiteInnerCorrectness
import DeepWiki.SymbolicIntegration.Compute.HermitePower
import DeepWiki.SymbolicIntegration.Compute.HermiteResidualCorrectness
import DeepWiki.SymbolicIntegration.Compute.LrtLogPart
import DeepWiki.SymbolicIntegration.Compute.RationalFunction
import DeepWiki.SymbolicIntegration.Compute.SquarefreeExact
import DeepWiki.SymbolicIntegration.Compute.SquarefreeYun
import DeepWiki.SymbolicIntegration.Core.Polynomial.RatFuncRegular
import DeepWiki.SymbolicIntegration.RationalFunctionDerivative
import DeepWiki.SymbolicIntegration.SquarefreeFactorization

/-! # Correctness of the computable Hermite reduction (`cdiophantine`/`hermiteInner`)
Proves the computable Hermite engine correct in `RatFunc ℚ` through the `toPoly : CPoly → ℚ[X]`
bridge: the Bézout solver `cdiophantine` realizes the abstract `diophantineSolveReduced`, the
`hermiteInner` loop and `hermiteReduce` wrapper reduce `A/D` to a residual over the squarefree
radical, and the multi-factor interference divisibility is discharged. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration.Compute

/-! ### The multi-factor `g`-fold interference invariant: toward an unconditional wrapper

`hermiteReduce`'s rational part is the *conditional* fold
`g = factors.foldl (fun gAcc (Vi,i) => if i ≤ 1 then gAcc else qadd gAcc glocᵢ) qzero`, where each kept
factor `(Vi, i)` (multiplicity `i ≥ 2`) contributes `glocᵢ = (hermiteInner fuel Vi Uᵢ (i−1) A qzero).1`
with `Uᵢ = D/Vi^i`. To run the `foldl_residual_eq` skeleton on it, the conditional fold is first
re-expressed as a plain `qadd`-fold over the *list of increments* `glocList` (one `glocᵢ` per kept
factor); then each increment's derivative reduces the **same** global `T = A/D` (via
`hermiteInner_spec_of` and the reconciliation `am Uᵢ·am Vi^i = am D`), so `foldl_residual_eq` expresses
the total residual as `(1−n)·T + Σᵢ residᵢ` — the overcounting skeleton. -/

/-- **The per-factor `gloc` increment** of `hermiteReduce`'s `g`-fold: for a kept factor `(Vi, i)`
(`i ≥ 2`), `glocIncr fuel A D (Vi, i) = (hermiteInner fuel Vi (D/Vi^i) (i−1) A qzero).1`, the rational
part `hermiteInner` peels from the global `A/D` against this factor. -/
def glocIncr (fuel : ℕ) (A D : CPoly) (Vi : CPoly × ℕ) : QFun :=
  let Vi_pow := (List.range Vi.2).foldl (fun acc _ => cmul acc Vi.1) [1]
  let U := cdiv fuel D Vi_pow
  (hermiteInner fuel Vi.1 U (Vi.2 - 1) A qzero).1

/-- **The list of `gloc` increments** for the kept factors (`i ≥ 2`) of `hermiteReduce`'s `g`-fold:
`glocList fuel A D factors` drops the simple factors (`i ≤ 1`) and maps each repeated factor to its
`glocIncr`. The plain increment list over which the conditional fold becomes a `qadd`-fold. -/
def glocList (fuel : ℕ) (A D : CPoly) (factors : List (CPoly × ℕ)) : List QFun :=
  (factors.filter (fun Vi => decide (2 ≤ Vi.2))).map (glocIncr fuel A D)

/-- **The conditional `g`-fold is the plain `qadd`-fold over the increment list**: the
`hermiteReduce` accumulation `factors.foldl (fun gAcc (Vi,i) => if i ≤ 1 then gAcc else qadd gAcc glocᵢ)
init` equals `(glocList fuel A D factors).foldl qadd init`. The `if i ≤ 1` drop is the `filter (2 ≤ i)`;
each kept step is a `qadd` of the matching `glocIncr`. -/
theorem foldl_cond_eq_foldl_glocList (fuel : ℕ) (A D : CPoly) (factors : List (CPoly × ℕ))
    (init : QFun) :
    factors.foldl
        (fun (gAcc : QFun) (Vi : CPoly × ℕ) =>
          if Vi.2 ≤ 1 then gAcc
          else
            let Vi_pow := (List.range Vi.2).foldl (fun acc _ => cmul acc Vi.1) [1]
            let U := cdiv fuel D Vi_pow
            let gloc := (hermiteInner fuel Vi.1 U (Vi.2 - 1) A qzero).1
            qadd gAcc gloc)
        init
      = (glocList fuel A D factors).foldl qadd init := by
  induction factors generalizing init with
  | nil => simp [glocList]
  | cons hd tl ih =>
    rw [List.foldl_cons, glocList, List.filter_cons]
    by_cases hhd : 2 ≤ hd.2
    · simp only [decide_eq_true_eq.mpr hhd, if_true, List.map_cons, List.foldl_cons]
      have hcond : ¬ hd.2 ≤ 1 := by omega
      rw [if_neg hcond]
      have := ih (qadd init (glocIncr fuel A D hd))
      rw [glocList] at this
      rw [show (hermiteInner fuel hd.1 (cdiv fuel D
            ((List.range hd.2).foldl (fun acc _ => cmul acc hd.1) [1])) (hd.2 - 1) A qzero).1
          = glocIncr fuel A D hd from rfl]
      exact this
    · have hcond : hd.2 ≤ 1 := by omega
      rw [if_neg (by simpa using hhd : ¬ (decide (2 ≤ hd.2) = true)), if_pos hcond]
      have := ih init
      rw [glocList] at this
      exact this

/-- **`hermiteInner` preserves nonzero accumulator denominator**: if `V ≠ 0` and the seed `g` has
nonzero denominator, then `(hermiteInner fuel V U j A g).1` does too. Each loop step `qadd`s
`(B, V^(j+1))` whose denominator `V^(j+1) ≠ 0`, so the denominator stays nonzero. -/
theorem hermiteInner_den_ne_zero (fuel : ℕ) (V U : CPoly) (hV : toPoly V ≠ 0) :
    ∀ (j : ℕ) (A : CPoly) (g : QFun), toPoly g.2 ≠ 0 →
      toPoly (hermiteInner fuel V U j A g).1.2 ≠ 0 := by
  intro j
  induction j with
  | zero => intro A g hg; simpa [hermiteInner] using hg
  | succ j ih =>
    intro A g hg
    rw [hermiteInner]
    rcases hBC : cdiophantine fuel (cmul U (cderiv V)) V (cscale (-((j : ℚ) + 1)⁻¹) A) with ⟨B, C⟩
    simp only []
    set Vpow := (List.range (j + 1)).foldl (fun acc _ => cmul acc V) [1] with hVpowdef
    have hVpow0 : toPoly Vpow ≠ 0 := by
      rw [toPoly_hermiteInner_Vpow]; exact pow_ne_zero _ hV
    have hgnew : toPoly (qadd g (B, Vpow)).2 ≠ 0 := by
      show toPoly (cmul g.2 Vpow) ≠ 0
      rw [toPoly_cmul]; exact mul_ne_zero hg hVpow0
    exact ih _ _ hgnew

/-- The `glocIncr` increment has nonzero denominator (when `V ≠ 0`): `hermiteInner` starts from `qzero`
(denominator `[1]`, nonzero) and `hermiteInner_den_ne_zero` preserves it. -/
theorem glocIncr_den_ne_zero (fuel : ℕ) (A D : CPoly) (Vi : CPoly × ℕ) (hV : toPoly Vi.1 ≠ 0) :
    toPoly (glocIncr fuel A D Vi).2 ≠ 0 :=
  hermiteInner_den_ne_zero fuel Vi.1 _ hV (Vi.2 - 1) A qzero (by simp [qzero, toPoly_cons])

/-! ### The per-factor residual identity: each increment reduces the *global* `A/D`

For a kept factor `(Vi, i)` (`i ≥ 2`, so `i = (i−1)+1`), with `U = D/Vi^i` reconciled exactly
(`am D = am U·am Vi^i`, from `Vi^i ∣ D`), `hermiteInner_spec_of` reads as
`(toQFun glocᵢ)′ = am A/am D − am Afinalᵢ/(am U·am Vi)`. So with `T = am A/am D`, each increment reduces
the *same* global `T`, leaving the per-factor residual `residᵢ = am Afinalᵢ/(am U·am Vi)` — exactly the
shape `foldl_residual_eq` consumes. The reconciliation `am D = am U·am Vi^i` is the exact-division
content `Vi^i ∣ D` (`am_eq_cdiv_mul_of_cmod_zero`), supplied here as a hypothesis. -/

/-- The `glocIncr` denominator `Uᵢ·Vi` (the per-factor residual denominator): for the kept factor
`(Vi, i)` with `Uᵢ = D/Vi^i`, the residual fraction `residᵢ` has denominator `am Uᵢ·am Vi`. -/
noncomputable def glocResidDen (fuel : ℕ) (D : CPoly) (Vi : CPoly × ℕ) : RatFunc ℚ :=
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
theorem glocIncr_residual (fuel : ℕ) (A D : CPoly) (Vi : CPoly) (j : ℕ)
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
theorem total_fold_residual (fuel : ℕ) (A D : CPoly) (factors : List (CPoly × ℕ))
    (T : RatFunc ℚ) (resid : CPoly × ℕ → RatFunc ℚ)
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
theorem glocResidDen_eq_over_D (fuel : ℕ) (D : CPoly) (Vi : CPoly) (j : ℕ)
    (Afinal : CPoly) (hD : toPoly D ≠ 0) (hV : toPoly Vi ≠ 0)
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
def afinalIncr (fuel : ℕ) (A D : CPoly) (Vi : CPoly × ℕ) : CPoly :=
  let Vi_pow := (List.range Vi.2).foldl (fun acc _ => cmul acc Vi.1) [1]
  let U := cdiv fuel D Vi_pow
  (hermiteInner fuel Vi.1 U (Vi.2 - 1) A qzero).2

/-- **The per-factor residual numerator over `D`** `residNumIncr fuel A D (Vi, i) = Afinalᵢ·Vi^{i−1}`:
the polynomial numerator the factor `(Vi, i)` contributes to the single-fraction-over-`D` residual
`am (Σᵢ Afinalᵢ·Vi^{i−1})/am D`. -/
noncomputable def residNumIncr (fuel : ℕ) (A D : CPoly) (Vi : CPoly × ℕ) : ℚ[X] :=
  toPoly (afinalIncr fuel A D Vi) * toPoly Vi.1 ^ (Vi.2 - 1)

open scoped Differential in
/-- **The total `g`-fold residual as a single fraction over `D`**: under per-factor hypotheses
(`hstep`, the conclusion of `glocIncr_residual` recast over `D` by `glocResidDen_eq_over_D`) for every
kept factor `(Vi, i)`, the entire residual of `hermiteReduce`'s `g`-fold is
`am A/am D − (toQFun g)′ = am R/am D`, where `R = C(1−n)·A + Σ_{kept} residNumIncr` is a single
polynomial (`n` = #kept). This is the honest single-fraction-over-`D` form of the multi-factor
interference: the whole fold residual is one polynomial fraction over the global `D`; the remaining
content (clearing to denominator `Dstar`) is the divisibility `am (D/Dstar) ∣ am R`. -/
theorem total_fold_residual_over_D (fuel : ℕ) (A D : CPoly) (factors : List (CPoly × ℕ))
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
theorem hermiteReduce_residual_correct_multifactor (fuel : ℕ) (A D Dstar W : CPoly)
    (factors : List (CPoly × ℕ))
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
theorem glocIncr_hstep (fuel : ℕ) (A D : CPoly) (Vi : CPoly) (j : ℕ) (hD : toPoly D ≠ 0)
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

/-! ### Bridging the two residual numerators: `R·gden² = resNum'`

The whole fold residual `A/D − g′` has two representations: the **per-factor** form `am R/am D`
(`total_fold_residual_over_D`, `R = C(1−n)·A + Σ residNumIncr`), and the **quotient-rule** form
`am resNum'/(am D·am gden²)` (`residual_numerator_ratFunc`, `g = gnum/gden`, `resNum' = A·gden² −
D·gprimeNum`). Equating them (both equal `A/D − g′`) pins `R·gden² = resNum'` as polynomials — the
consistency bridge linking the interference numerator `R` to the algorithm's computed residual numerator
`resNum'`, so the interference divisibility `W ∣ R` is equivalent to the algorithm's cleared-identity
divisibility on `resNum'`. -/

open scoped Differential in
/-- **The per-factor residual numerator agrees with the quotient-rule one**: if the fold `g = (gnum,
gden)` satisfies the per-factor identities (`hstep`), then `R·gden² = resNum'` in `ℚ[X]`, where `R =
C(1−n)·A + Σ residNumIncr` is the interference numerator and `resNum' = A·gden² − D·(gnum'·gden −
gnum·gden')` the quotient-rule residual numerator. Both equal the residual `A/D − g′` over their
denominators; cross-multiplying and `am`-injectivity pin the polynomial identity. -/
theorem residNum_eq_resNumPrime (fuel : ℕ) (A D gnum gden : CPoly) (factors : List (CPoly × ℕ))
    (hD : toPoly D ≠ 0) (hgden : toPoly gden ≠ 0)
    (hV : ∀ Vi ∈ factors, toPoly Vi.1 ≠ 0)
    (hg : toQFun ((glocList fuel A D factors).foldl qadd qzero) = toQFun (gnum, gden))
    (hstep : ∀ Vi ∈ factors, 2 ≤ Vi.2 →
      (toQFun (glocIncr fuel A D Vi))′
        = algebraMap ℚ[X] (RatFunc ℚ) (toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
          - algebraMap ℚ[X] (RatFunc ℚ) (residNumIncr fuel A D Vi)
            / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)) :
    (Polynomial.C (1 - ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).length : ℚ)) * toPoly A
        + ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).map (residNumIncr fuel A D)).sum)
        * (toPoly gden * toPoly gden)
      = toPoly A * (toPoly gden * toPoly gden)
        - toPoly D * (derivative (toPoly gnum) * toPoly gden - toPoly gnum * derivative (toPoly gden)) := by
  have hinj := RatFunc.algebraMap_injective (K := ℚ)
  set am := algebraMap ℚ[X] (RatFunc ℚ) with hamdef
  set R := Polynomial.C (1 - ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).length : ℚ)) * toPoly A
    + ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).map (residNumIncr fuel A D)).sum with hRdef
  set resNum' := toPoly A * (toPoly gden * toPoly gden)
    - toPoly D * (derivative (toPoly gnum) * toPoly gden - toPoly gnum * derivative (toPoly gden))
    with hresNum'def
  have hd : am (toPoly D) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hD
  have hgd : am (toPoly gden) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hgden
  -- per-factor form: `A/D − g′ = am R/am D`.
  have hres1 := total_fold_residual_over_D fuel A D factors hD hV hstep
  rw [← hRdef, hg] at hres1
  -- quotient-rule form: `A/D − (gnum/gden)′ = am resNum'/(am D·(am gden·am gden))`.
  have hres2 := residual_numerator_ratFunc (toPoly A) (toPoly D) (toPoly gnum) (toPoly gden) hD hgden
  rw [← hresNum'def] at hres2
  -- `(toQFun (gnum,gden))′ = (gnum/gden)′`.
  have htoQ : toQFun (gnum, gden) = am (toPoly gnum) / am (toPoly gden) := rfl
  rw [htoQ] at hres1
  -- both equal `A/D − g′`, so `am R/am D = am resNum'/(am D·am gden²)`.
  have heq : am R / am (toPoly D)
      = am resNum' / (am (toPoly D) * (am (toPoly gden) * am (toPoly gden))) := by
    rw [← hres1, ← hres2]
  -- cross-multiply: `am R · (am gden·am gden) = am resNum'`.
  have hRgd : am R * (am (toPoly gden) * am (toPoly gden)) = am resNum' := by
    have hstep1 : am R / am (toPoly D) * (am (toPoly D) * (am (toPoly gden) * am (toPoly gden)))
        = am R * (am (toPoly gden) * am (toPoly gden)) := by
      field_simp
    rw [heq, div_mul_cancel₀ _ (mul_ne_zero hd (mul_ne_zero hgd hgd))] at hstep1
    exact hstep1.symm
  -- the goal `R·gden² = resNum'` is `am`-injective image of `hRgd`.
  apply hinj
  rw [map_mul, map_mul]
  exact hRgd

/-- **`W ∣ R ⟺ W·gden² ∣ resNum'`** (cancel the common `gden²`): with `R·gden² = resNum'`
(`residNum_eq_resNumPrime`) and `gden ≠ 0`, the interference divisibility `W ∣ R` is *equivalent* to the
algorithm's cleared-identity divisibility `W·gden² ∣ resNum'`. So the abstract interference wall is
exactly the divisibility the existing radical wrapper (`hermiteReduce_residual_correct_of_radical`) and
per-example `native_decide` certs consume — confirming the reduction is consistent and the wall is the
single remaining piece. -/
theorem dvd_R_iff_dvd_resNumPrime {R resNum' gden W : ℚ[X]} (hgden : gden ≠ 0)
    (hRel : R * (gden * gden) = resNum') :
    W ∣ R ↔ W * (gden * gden) ∣ resNum' := by
  rw [← hRel]
  constructor
  · intro h; exact mul_dvd_mul h dvd_rfl
  · intro h
    have hg2 : gden * gden ≠ 0 := mul_ne_zero hgden hgden
    exact (mul_dvd_mul_iff_right hg2).mp h

/-! ### Summary: the multi-factor interference invariant, fully closed

The multi-factor `hermiteReduce` `g`-fold correctness is now **fully proven** (no remaining
divisibility hypothesis). The chain:

* `foldl_cond_eq_foldl_glocList` — the conditional `g`-fold is a plain `qadd`-fold over the kept-factor
  increment list `glocList`.
* `glocIncr_residual` / `glocIncr_hstep` — each kept factor's increment reduces the *global* `T = A/D`,
  leaving `residᵢ = am Afinalᵢ/(am Uᵢ·am Vi)` (over the global `D`: `am (Afinalᵢ·Vi^{i−1})/am D`), from
  the per-factor Bézout side conditions and the reconciliation `am D = am Uᵢ·am Vi^{i}`.
* `total_fold_residual` / `total_fold_residual_over_D` — the whole fold residual `A/D − g′` is the
  **single** polynomial fraction `am R/am D` with `R = C(1−n)·A + Σᵢ residNumIncrᵢ` (`n = #kept`): the
  exact `(1−n)·T + Σ residᵢ` overcounting skeleton collapsed onto the common denominator `D`.
* `am_div_D_eq_div_Dstar` — `am R/am D` clears to `am (R/W)/am Dstar` **iff** `W ∣ R`.
* **The interference divisibility `W ∣ R`** (`W = ∏_{kept} Vk^{ik−1} = D/Dstar`) is **proven** by a
  per-factor `Vk`-adic order argument:
  - `IsQRegular Q` — a `RatFunc` with no pole at the prime `Q` (denominator coprime to `Q`); closed
    under `+`, negation, list-sum, and the `RatFunc` derivative (`IsQRegular.add/.neg/.deriv`,
    `isQRegular_list_sum`), with `dvd_num_of_isQRegular` reading `Q^e ∣ r` off `am r/am D` `Q`-regular +
    `Q^e ∣ D`.
  - `glocIncr_den_eq_pow` ⟹ `glocIncr_toQFun_isQRegular`: each `glocᵢ` has denominator a pure power of
    `Vi`, so `glocᵢ′` is pole-free at every *other* factor `Vk`.
  - `deriv_fold_sub_glocIncr_isQRegular`: `g′ − glocₖ′ = Σ_{i≠k} glocᵢ′` is therefore `Vk`-regular, and
    `dvd_residNum_factor` reads `Vk^{ik−1} ∣ R` from `am (R − residNumIncrₖ)/am D = glocₖ′ − g′` being
    `Vk`-regular (with `Vk^{ik} ∣ D`) plus `Vk^{ik−1} ∣ residNumIncrₖ`.
  - `prod_dvd_residNum`: the per-factor bounds `Vk^{ik−1} ∣ R` assemble over the pairwise-coprime kept
    powers (`list_prod_dvd_of_pairwise`) to the product `W = ∏ Vk^{ik−1} ∣ R`.
* `hermiteReduce_residual_correct_multifactor` — the wrapper conditional on `W ∣ R`;
  **`hermiteReduce_residual_correct_uncond'`** — the **fully unconditional** wrapper
  `am A/am D = (toQFun g)′ + am (R/W)/am Dstar`, discharging `W ∣ R` internally via `prod_dvd_residNum`.
* `residNum_eq_resNumPrime` + `dvd_R_iff_dvd_resNumPrime` — `R·gden² = resNum'`, so `W ∣ R ⟺
  W·gden² ∣ resNum'` (the algorithm's own cleared-identity cert), confirming consistency.

The earlier worry that this cancellation is "not implied by the per-factor specifications alone" is
resolved: the order argument needs no per-factor `Afinalᵢ` divisibility — it confines each `Vk`-pole to
factor `k`'s own residual identity (`glocₖ′`) via the `IsQRegular` localization of the *other* factors'
derivatives. The single-repeated-factor case (`n = 1`, `W = 1`) is `hermiteReduce_residual_correct_single`. -/

open scoped Differential in
-- Hermite reduction, multi-factor wrapper (Bronstein §2.2/§2.5): the computable `hermiteReduce`
-- `g`-fold integrates the rational part `g`, leaving a residual over the squarefree radical `Dstar` —
-- conditional ONLY on the single interference divisibility `W ∣ R` (`W = D/Dstar`,
-- `R = C(1−n)·A + Σ Afinalᵢ·Vi^{i−1}`), everything else (the over-`D` residual skeleton, the radical
-- clause `Dstar ∣ D`) proven.
example (fuel : ℕ) (A D Dstar W : CPoly) (factors : List (CPoly × ℕ))
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
          / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Dstar) :=
  hermiteReduce_residual_correct_multifactor fuel A D Dstar W factors hD hDstar hV hstep hWdec hWR

/-! ### Toward an abstract `W ∣ R`: the increment `glocᵢ` has denominator a power of `Vi` only

The crux making the multi-factor interference *per-factor* tractable: each `glocᵢ = hermiteInner fuel Vi
Uᵢ … A qzero` accumulates **only** summands `B/Vi^{j+1}` (the inner loop `qadd`s `(B, Vi^{j+1})`), so its
denominator is a *power of `Vi` alone*. Hence `glocᵢ′` has poles **only** at `Vi`, and at any other
irreducible `Vk` (`k ≠ i`, coprime to `Vi`) `glocᵢ′` is regular. This localizes the pole-order of
`A/D − g′` at each `Vk` to the single factor `k`'s `hermiteInner_spec_of` — the structural fact behind a
future order/valuation proof of `W ∣ R`. The lemma below is the first step: `hermiteInner`'s denominator
is `(seed denominator)·Vi^m`. -/

/-- **`hermiteInner`'s denominator is the seed denominator times a power of `V`**: there is `m` with
`toPoly (hermiteInner fuel V U j A g).1.2 = toPoly g.2 · (toPoly V)^m`. Each loop step `qadd`s
`(B, V^{j+1})`, multiplying the denominator by `V^{j+1}`; so the accumulated denominator is the seed
times a power of `V`. The structural fact that `glocᵢ` has poles only at `Vi`. -/
theorem hermiteInner_den_eq_pow (fuel : ℕ) (V U : CPoly) :
    ∀ (j : ℕ) (A : CPoly) (g : QFun),
      ∃ m : ℕ, toPoly (hermiteInner fuel V U j A g).1.2 = toPoly g.2 * toPoly V ^ m := by
  intro j
  induction j with
  | zero => intro A g; exact ⟨0, by simp [hermiteInner]⟩
  | succ j ih =>
    intro A g
    rw [hermiteInner]
    rcases hBC : cdiophantine fuel (cmul U (cderiv V)) V (cscale (-((j : ℚ) + 1)⁻¹) A) with ⟨B, C⟩
    simp only []
    set Vpow := (List.range (j + 1)).foldl (fun acc _ => cmul acc V) [1] with hVpowdef
    obtain ⟨m, hm⟩ := ih (csub (cscale (-((j : ℚ) + 1)) C) (cmul U (cderiv B))) (qadd g (B, Vpow))
    refine ⟨m + (j + 1), ?_⟩
    rw [hm]
    show toPoly (qadd g (B, Vpow)).2 * toPoly V ^ m = toPoly g.2 * toPoly V ^ (m + (j + 1))
    show toPoly (cmul g.2 Vpow) * toPoly V ^ m = toPoly g.2 * toPoly V ^ (m + (j + 1))
    rw [toPoly_cmul, toPoly_hermiteInner_Vpow, pow_add]
    ring

/-- **`glocIncr`'s denominator is a pure power of `Vi`**: there is `m` with
`toPoly (glocIncr fuel A D Vi).2 = (toPoly Vi.1)^m`. From `hermiteInner_den_eq_pow` at the `qzero`
seed (denominator `1`). So `glocIncr Vi` (and its derivative) has poles only at `Vi` — regular at every
other irreducible factor. -/
theorem glocIncr_den_eq_pow (fuel : ℕ) (A D : CPoly) (Vi : CPoly × ℕ) :
    ∃ m : ℕ, toPoly (glocIncr fuel A D Vi).2 = toPoly Vi.1 ^ m := by
  obtain ⟨m, hm⟩ := hermiteInner_den_eq_pow fuel Vi.1
    (cdiv fuel D ((List.range Vi.2).foldl (fun acc _ => cmul acc Vi.1) [1]))
    (Vi.2 - 1) A qzero
  refine ⟨m, ?_⟩
  rw [show (glocIncr fuel A D Vi).2
      = (hermiteInner fuel Vi.1 (cdiv fuel D
          ((List.range Vi.2).foldl (fun acc _ => cmul acc Vi.1) [1])) (Vi.2 - 1) A qzero).1.2 from rfl,
    hm]
  simp [qzero, toPoly_cons]

/-- **`glocIncr` is `Vk`-regular for `k ≠ i`**: if `P` is coprime to `Vi`, then `P` does not divide the
denominator of `glocIncr fuel A D Vi` to any positive power beyond what `P ∣ Vi^m` allows — concretely,
`IsRelPrime P (toPoly (glocIncr fuel A D Vi).2)` whenever `IsRelPrime P (toPoly Vi.1)`. The denominator
is `Vi^m` (`glocIncr_den_eq_pow`), coprime to `P`. This is the regularity that localizes `g′`'s pole at
each `Vk` to the single factor `k`. -/
theorem glocIncr_den_isRelPrime (fuel : ℕ) (A D : CPoly) (Vi : CPoly × ℕ) (P : ℚ[X])
    (hP : IsRelPrime P (toPoly Vi.1)) :
    IsRelPrime P (toPoly (glocIncr fuel A D Vi).2) := by
  obtain ⟨m, hm⟩ := glocIncr_den_eq_pow fuel A D Vi
  rw [hm]
  exact hP.pow_right

/-! ### `Q`-regularity: a denominator-coprimality abstraction for the order argument

To prove the interference divisibility `W ∣ R` by a per-factor `Vk`-adic order argument, we track when a
`RatFunc ℚ` has **no pole at a prime `Q`** — i.e. is representable `am p/am q` with `q` coprime to `Q`.
This `IsQRegular Q` predicate is closed under `+` (common denominator stays coprime) and under the
`RatFunc` derivative (the quotient rule squares the denominator, keeping it coprime to `Q`), and the key
**extraction** lemma reads a divisibility off it: if `am r/am D` is `Q`-regular and `Q^e ∣ D`, then
`Q^e ∣ r` — the numerator carries the pole order the regular function refuses. -/

/-- **`Q`-regular**: a `RatFunc ℚ` representable `am p/am q` with `q ≠ 0` coprime to `Q` — no pole at
`Q`. The denominator-coprimality witness driving the per-factor order argument for `W ∣ R`. -/
abbrev IsQRegular (Q : ℚ[X]) (f : RatFunc ℚ) : Prop :=
  IsRatFuncRegular Q f

/-- `0` is `Q`-regular (denominator `1`). -/
theorem isQRegular_zero (Q : ℚ[X]) : IsQRegular Q 0 :=
  isRatFuncRegular_zero Q

/-- **`Q`-regular is closed under `+`**: over the common denominator `q₁·q₂` (coprime to `Q` since each
`qᵢ` is, by `IsRelPrime.mul_right`). The sum of two pole-free-at-`Q` functions is pole-free at `Q`. -/
theorem IsQRegular.add {Q : ℚ[X]} {f g : RatFunc ℚ} (hf : IsQRegular Q f) (hg : IsQRegular Q g) :
    IsQRegular Q (f + g) :=
  IsRatFuncRegular.add hf hg

/-- **Order extraction from `Q`-regularity**: if the fraction `am r/am D` is `Q`-regular, `D ≠ 0`, and
`Q^e ∣ D`, then `Q^e ∣ r`. Cross-multiplying `r·q = p·D` (the regular representation), `Q^e ∣ D ∣ p·D =
r·q`; coprimality `IsRelPrime (Q^e) q` then transfers the power onto `r`. The numerator absorbs the pole
order the `Q`-regular function declines to carry. -/
theorem dvd_num_of_isQRegular {Q r D : ℚ[X]} {e : ℕ} (hD : D ≠ 0) (hQe : Q ^ e ∣ D)
    (hf : IsQRegular Q (algebraMap ℚ[X] (RatFunc ℚ) r / algebraMap ℚ[X] (RatFunc ℚ) D)) :
    Q ^ e ∣ r :=
  dvd_num_of_isRatFuncRegular hD hQe hf

open scoped Differential in
/-- **`Q`-regular is closed under the `RatFunc` derivative**: if `f = am p/am q` has denominator `q`
coprime to `Q`, then `f′` has denominator `q²` (quotient rule `ratFuncDeriv_mk`), still coprime to `Q`
(`IsRelPrime.pow_right`). A pole-free-at-`Q` function differentiates to a pole-free-at-`Q` function. -/
theorem IsQRegular.deriv {Q : ℚ[X]} {f : RatFunc ℚ} (hf : IsQRegular Q f) :
    IsQRegular Q (f′) := by
  obtain ⟨p, q, hq, hQ, hfeq⟩ := hf
  refine ⟨derivative p * q - p * derivative q, q ^ 2, pow_ne_zero 2 hq, hQ.pow_right, ?_⟩
  rw [hfeq, ← RatFunc.mk_eq_div]
  show ratFuncDeriv (RatFunc.mk p q) = _
  rw [ratFuncDeriv_mk, RatFunc.mk_eq_div]

/-- **`glocᵢ` is `Q`-regular for `Q` coprime to `Vi`**: `toQFun (glocIncr fuel A D Vi)` has denominator
`(toPoly Vi.1)^m` (`glocIncr_den_eq_pow`), coprime to `Q` whenever `IsRelPrime Q (toPoly Vi.1)`. So the
increment's rational read has no pole at any other irreducible factor — the localization that confines
factor `i`'s pole to `Vi`. -/
theorem glocIncr_toQFun_isQRegular (fuel : ℕ) (A D : CPoly) (Vi : CPoly × ℕ) {Q : ℚ[X]}
    (hV : toPoly Vi.1 ≠ 0) (hQ : IsRelPrime Q (toPoly Vi.1)) :
    IsQRegular Q (toQFun (glocIncr fuel A D Vi)) := by
  obtain ⟨m, hm⟩ := glocIncr_den_eq_pow fuel A D Vi
  refine ⟨toPoly (glocIncr fuel A D Vi).1, toPoly Vi.1 ^ m, pow_ne_zero m hV, hQ.pow_right, ?_⟩
  rw [toQFun, hm]

/-- **`Q`-regular is closed under negation**: `−f = am(−p)/am q`, same `Q`-coprime denominator. -/
theorem IsQRegular.neg {Q : ℚ[X]} {f : RatFunc ℚ} (hf : IsQRegular Q f) : IsQRegular Q (-f) := by
  exact IsRatFuncRegular.neg hf

/-- **A `List`-sum of `Q`-regular summands is `Q`-regular**: by induction, folding `IsQRegular.add`
from `isQRegular_zero`. The interference sum over the *other* factors (each `glocᵢ′`, `i≠k`, pole-free at
`Vk`) is itself pole-free at `Vk`. -/
theorem isQRegular_list_sum {α : Type*} {Q : ℚ[X]} (L : List α)
    (f : α → RatFunc ℚ) (hreg : ∀ a ∈ L, IsQRegular Q (f a)) :
    IsQRegular Q (L.map f).sum :=
  isRatFuncRegular_list_sum L f hreg

open scoped Differential in
/-- **The interference derivative `g′ − glocₖ′` is `Vk`-regular**: the fold derivative `g′ = Σ_{i∈kept}
glocᵢ′` minus the `k`-term `glocₖ′` is the sum `Σ_{i∈kept.erase k} glocᵢ′` (`perm_cons_erase`), whose
every summand is `glocᵢ′` for `i ≠ k` — pole-free at `Vk` by `glocIncr_toQFun_isQRegular` +
`IsQRegular.deriv`. Hence the whole interference difference has no pole at `Vk`. The structural heart of
the per-factor order argument: removing factor `k`'s own contribution leaves a `Vk`-regular remainder. -/
theorem deriv_fold_sub_glocIncr_isQRegular (fuel : ℕ) (A D : CPoly)
    (factors : List (CPoly × ℕ)) (kelem : CPoly × ℕ)
    (hkmem : kelem ∈ factors.filter (fun Vi => decide (2 ≤ Vi.2)))
    (hnd : (factors.filter (fun Vi => decide (2 ≤ Vi.2))).Nodup)
    (hV : ∀ Vi ∈ factors, toPoly Vi.1 ≠ 0)
    (hcop : ∀ Vi ∈ factors.filter (fun Vi => decide (2 ≤ Vi.2)), Vi ≠ kelem →
      IsRelPrime (toPoly kelem.1) (toPoly Vi.1)) :
    IsQRegular (toPoly kelem.1)
      ((toQFun ((glocList fuel A D factors).foldl qadd qzero))′
        - (toQFun (glocIncr fuel A D kelem))′) := by
  classical
  set kept := factors.filter (fun Vi => decide (2 ≤ Vi.2)) with hkept
  -- denominators of the increments are nonzero (needed for `deriv_toQFun_foldl_qadd`).
  have hden : ∀ g ∈ glocList fuel A D factors, toPoly g.2 ≠ 0 := by
    intro g hg
    rw [glocList, ← hkept, List.mem_map] at hg
    obtain ⟨Vi, hViMem, rfl⟩ := hg
    exact glocIncr_den_ne_zero fuel A D Vi (hV Vi (List.mem_of_mem_filter hViMem))
  -- `g′ = Σ_{i∈kept} glocᵢ′`.
  rw [deriv_toQFun_foldl_qadd (glocList fuel A D factors) hden, glocList, ← hkept, List.map_map]
  set h := (fun g => (toQFun g)′) ∘ glocIncr fuel A D with hh
  -- `kept` permutes to `kelem :: kept.erase kelem`, so the mapped sum splits off the `k`-term.
  have hsum : (kept.map h).sum = h kelem + ((kept.erase kelem).map h).sum := by
    have hp : (kept.map h).Perm ((kelem :: kept.erase kelem).map h) :=
      (List.perm_cons_erase hkmem).map h
    rw [hp.sum_eq, List.map_cons, List.sum_cons]
  rw [hsum, hh]
  simp only [Function.comp_apply]
  -- `(glocₖ′ + Σ_{i≠k} glocᵢ′) − glocₖ′ = Σ_{i≠k} glocᵢ′`, which is `Vk`-regular.
  rw [add_sub_cancel_left]
  refine isQRegular_list_sum (kept.erase kelem) (fun g => (toQFun (glocIncr fuel A D g))′) ?_
  intro Vi hVi
  rw [(hkept ▸ hnd : kept.Nodup).mem_erase_iff] at hVi
  obtain ⟨hVine, hVimem⟩ := hVi
  have hVi0 : toPoly Vi.1 ≠ 0 := hV Vi (List.mem_of_mem_filter (hkept ▸ hVimem))
  exact (glocIncr_toQFun_isQRegular fuel A D Vi hVi0
    (hcop Vi (hkept ▸ hVimem) hVine)).deriv

/-! ### The per-factor interference divisibility `Vk^{ik−1} ∣ R`

The single-factor order bound. With `R = C(1−n)·A + Σ_{kept} residNumIncr` the whole-fold residual
numerator, fix a kept factor `(Vk, ik)`. Subtracting the factor-`k` residual identity (`hstep` at `k`,
`glocₖ′ = A/D − residNumIncrₖ/D`) from the total residual (`total_fold_residual_over_D`,
`A/D − g′ = R/D`) gives `am (R − residNumIncrₖ)/am D = glocₖ′ − g′`, which is `Vk`-regular
(`deriv_fold_sub_glocIncr_isQRegular`). With `Vk^{ik} ∣ D`, the order-extraction lemma
`dvd_num_of_isQRegular` yields `Vk^{ik} ∣ (R − residNumIncrₖ)`; and `residNumIncrₖ = Afinalₖ·Vk^{ik−1}`
already carries `Vk^{ik−1}`, so `Vk^{ik−1} ∣ R`. -/

open scoped Differential in
/-- **Per-factor interference divisibility `Vk^{ik−1} ∣ R`**: for a kept factor `kelem = (Vk, ik)`
(distinct kept factors, `hnd`), with the per-factor residual identities (`hstep`, the
`total_fold_residual_over_D` input), the localization coprimality `IsRelPrime Vk Vi` for every *other*
kept factor, and `Vk^{ik} ∣ D`, the whole-fold residual numerator
`R = C(1−n)·A + Σ residNumIncr` is divisible by `Vk^{ik−1}`. The order argument: `R − residNumIncrₖ`
over `D` is `Vk`-regular, so `Vk^{ik} ∣ (R − residNumIncrₖ)`, and `Vk^{ik−1} ∣ residNumIncrₖ`. -/
theorem dvd_residNum_factor (fuel : ℕ) (A D : CPoly) (factors : List (CPoly × ℕ))
    (kelem : CPoly × ℕ) (hkmem : kelem ∈ factors.filter (fun Vi => decide (2 ≤ Vi.2)))
    (hnd : (factors.filter (fun Vi => decide (2 ≤ Vi.2))).Nodup)
    (hD : toPoly D ≠ 0) (hV : ∀ Vi ∈ factors, toPoly Vi.1 ≠ 0)
    (hstep : ∀ Vi ∈ factors, 2 ≤ Vi.2 →
      (toQFun (glocIncr fuel A D Vi))′
        = algebraMap ℚ[X] (RatFunc ℚ) (toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
          - algebraMap ℚ[X] (RatFunc ℚ) (residNumIncr fuel A D Vi)
            / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D))
    (hcop : ∀ Vi ∈ factors.filter (fun Vi => decide (2 ≤ Vi.2)), Vi ≠ kelem →
      IsRelPrime (toPoly kelem.1) (toPoly Vi.1))
    (hpow : toPoly kelem.1 ^ kelem.2 ∣ toPoly D) :
    toPoly kelem.1 ^ (kelem.2 - 1)
      ∣ Polynomial.C (1 - ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).length : ℚ)) * toPoly A
        + ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).map (residNumIncr fuel A D)).sum := by
  set am := algebraMap ℚ[X] (RatFunc ℚ) with hamdef
  set R := Polynomial.C (1 - ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).length : ℚ)) * toPoly A
    + ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).map (residNumIncr fuel A D)).sum with hR
  -- the kept membership gives `2 ≤ kelem.2` and `kelem ∈ factors`.
  have hk2 : 2 ≤ kelem.2 := by simpa using (List.mem_filter.mp hkmem).2
  have hkF : kelem ∈ factors := List.mem_of_mem_filter hkmem
  -- total residual: `am A/am D − g′ = am R/am D`.
  have hres := total_fold_residual_over_D fuel A D factors hD hV hstep
  rw [← hR] at hres
  -- factor-`k` step.
  have hk := hstep kelem hkF hk2
  -- `glocₖ′ − g′ = am (R − residNumIncrₖ)/am D`.
  have hinj := RatFunc.algebraMap_injective (K := ℚ)
  have had : am (toPoly D) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hD
  have hdiff : (toQFun (glocIncr fuel A D kelem))′
      - (toQFun ((glocList fuel A D factors).foldl qadd qzero))′
      = am (R - residNumIncr fuel A D kelem) / am (toPoly D) := by
    rw [map_sub, sub_div]
    linear_combination hk + hres
  -- `Vk`-regularity of the difference, transported across `hdiff`.
  have hreg : IsQRegular (toPoly kelem.1)
      (am (R - residNumIncr fuel A D kelem) / am (toPoly D)) := by
    rw [← hdiff, ← neg_sub]
    exact (deriv_fold_sub_glocIncr_isQRegular fuel A D factors kelem hkmem hnd hV hcop).neg
  -- `Vk^{ik} ∣ (R − residNumIncrₖ)`.
  have hdvdSub : toPoly kelem.1 ^ kelem.2 ∣ R - residNumIncr fuel A D kelem :=
    dvd_num_of_isQRegular hD hpow hreg
  -- `Vk^{ik−1} ∣ residNumIncrₖ` (it is `Afinalₖ·Vk^{ik−1}`).
  have hdvdInc : toPoly kelem.1 ^ (kelem.2 - 1) ∣ residNumIncr fuel A D kelem := by
    rw [residNumIncr]; exact Dvd.intro_left _ rfl
  -- `Vk^{ik−1} ∣ Vk^{ik} ∣ (R − residNumIncrₖ)`, plus `Vk^{ik−1} ∣ residNumIncrₖ`, gives `Vk^{ik−1} ∣ R`.
  have hdvdSub' : toPoly kelem.1 ^ (kelem.2 - 1) ∣ R - residNumIncr fuel A D kelem :=
    (pow_dvd_pow _ (Nat.sub_le _ _)).trans hdvdSub
  have : toPoly kelem.1 ^ (kelem.2 - 1) ∣ (R - residNumIncr fuel A D kelem)
      + residNumIncr fuel A D kelem := dvd_add hdvdSub' hdvdInc
  simpa using this

/-! ### The product divisibility `W ∣ R` over the pairwise-coprime kept factors

The interference numerator `R` is divisible by each `Vk^{ik−1}` (`dvd_residNum_factor`). Since the kept
factors `Vk` are pairwise coprime (Yun's `csqfreeFactor_pairwise_isRelPrime`), so are the powers
`Vk^{ik−1}`, hence their product `W = ∏_{kept} Vk^{ik−1} = D/Dstar` divides `R` — the single remaining
interference divisibility, now proven by the per-factor order argument. -/

open scoped Differential in
/-- **The product interference divisibility `W ∣ R`**: with `W = ∏_{kept} Vk^{ik−1}` and `R =
C(1−n)·A + Σ residNumIncr`, given the per-factor residual identities (`hstep`), pairwise coprimality of
the kept factors `Vk` (`hpw`), each `Vk^{ik} ∣ D`, the product `∏_{kept} Vk^{ik−1}` divides `R`. The
per-factor order bounds `Vk^{ik−1} ∣ R` (`dvd_residNum_factor`) assemble over the coprime powers
(`list_prod_dvd_of_pairwise`): the entire multi-factor interference clears, the last remaining piece. -/
theorem prod_dvd_residNum (fuel : ℕ) (A D : CPoly) (factors : List (CPoly × ℕ))
    (hnd : (factors.filter (fun Vi => decide (2 ≤ Vi.2))).Nodup)
    (hD : toPoly D ≠ 0) (hV : ∀ Vi ∈ factors, toPoly Vi.1 ≠ 0)
    (hstep : ∀ Vi ∈ factors, 2 ≤ Vi.2 →
      (toQFun (glocIncr fuel A D Vi))′
        = algebraMap ℚ[X] (RatFunc ℚ) (toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
          - algebraMap ℚ[X] (RatFunc ℚ) (residNumIncr fuel A D Vi)
            / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D))
    (hpw : (factors.filter (fun Vi => decide (2 ≤ Vi.2))).Pairwise
      (fun a b => IsRelPrime (toPoly a.1) (toPoly b.1)))
    (hpow : ∀ Vi ∈ factors.filter (fun Vi => decide (2 ≤ Vi.2)),
      toPoly Vi.1 ^ Vi.2 ∣ toPoly D) :
    ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).map
        (fun Vi => toPoly Vi.1 ^ (Vi.2 - 1))).prod
      ∣ Polynomial.C (1 - ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).length : ℚ)) * toPoly A
        + ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).map (residNumIncr fuel A D)).sum := by
  set kept := factors.filter (fun Vi => decide (2 ≤ Vi.2)) with hkept
  -- the mapped powers are pairwise `IsRelPrime` (from pairwise coprimality of the `Vk`).
  have hpwpow : (kept.map (fun Vi => toPoly Vi.1 ^ (Vi.2 - 1))).Pairwise IsRelPrime := by
    rw [List.pairwise_map]
    exact hpw.imp (fun {a b} hab => (hab.pow_left).pow_right)
  refine list_prod_dvd_of_pairwise _ _ hpwpow ?_
  -- each mapped power `Vk^{ik−1}` divides `R` by the per-factor order bound.
  intro a ha
  rw [List.mem_map] at ha
  obtain ⟨kelem, hkelem, rfl⟩ := ha
  -- the localization coprimality for the OTHER kept factors at `kelem`.
  haveI hsymInst : Std.Symm (fun a b : CPoly × ℕ => IsRelPrime (toPoly a.1) (toPoly b.1)) :=
    ⟨fun {_ _} (h : IsRelPrime _ _) => h.symm⟩
  have hcop : ∀ Vi ∈ kept, Vi ≠ kelem → IsRelPrime (toPoly kelem.1) (toPoly Vi.1) := by
    intro Vi hVi hne
    -- from pairwise coprimality (symmetric): `kelem` and `Vi` distinct kept factors are coprime.
    exact (hkept ▸ hpw : kept.Pairwise _).forall hkelem hVi (Ne.symm hne)
  exact dvd_residNum_factor fuel A D factors kelem hkelem hnd hD hV hstep hcop
    (hpow kelem hkelem)

/-! ### The fully unconditional multi-factor `hermiteReduce` wrapper

With `W ∣ R` now *proven* (`prod_dvd_residNum`), the multi-factor wrapper
(`hermiteReduce_residual_correct_multifactor`) becomes fully unconditional. Taking the radical
decomposition `D = Dstar·W` with `W = ∏_{kept} Vk^{ik−1}` (the cofactor `D/Dstar`) and the per-factor
hypotheses (residual identities, pairwise coprimality, `Vk^{ik} ∣ D`), the `g`-fold residual identity
`am A/am D = (toQFun g)′ + am (R/W)/am Dstar` holds **with no remaining divisibility assumption** — the
integrand lives over the squarefree radical `Dstar`. This closes the multi-factor interference. -/

open scoped Differential in
/-- **Fully unconditional multi-factor `hermiteReduce` wrapper** in `RatFunc ℚ`: with `W =
∏_{kept} Vk^{ik−1}` the radical cofactor (`hWdec : am D = am Dstar · am W`), the per-factor residual
identities (`hstep`), pairwise-coprime kept factors (`hpw`), distinct kept factors (`hnd`), and
`Vk^{ik} ∣ D` for each kept factor (`hpow`), the `g`-fold residual is correct:
`am A/am D = (toQFun g)′ + am (R/W)/am Dstar` — **no `W ∣ R` hypothesis**, the interference divisibility
is discharged internally by `prod_dvd_residNum`. The residual integrand lives over the squarefree radical
`Dstar`. The unconditional multi-factor Hermite reduction (Bronstein §2.2/§2.5). -/
theorem hermiteReduce_residual_correct_uncond' (fuel : ℕ) (A D Dstar : CPoly)
    (factors : List (CPoly × ℕ))
    (W : ℚ[X]) (hWeq : W = ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).map
        (fun Vi => toPoly Vi.1 ^ (Vi.2 - 1))).prod)
    (hD : toPoly D ≠ 0) (hDstar : toPoly Dstar ≠ 0)
    (hnd : (factors.filter (fun Vi => decide (2 ≤ Vi.2))).Nodup)
    (hV : ∀ Vi ∈ factors, toPoly Vi.1 ≠ 0)
    (hstep : ∀ Vi ∈ factors, 2 ≤ Vi.2 →
      (toQFun (glocIncr fuel A D Vi))′
        = algebraMap ℚ[X] (RatFunc ℚ) (toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
          - algebraMap ℚ[X] (RatFunc ℚ) (residNumIncr fuel A D Vi)
            / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D))
    (hpw : (factors.filter (fun Vi => decide (2 ≤ Vi.2))).Pairwise
      (fun a b => IsRelPrime (toPoly a.1) (toPoly b.1)))
    (hpow : ∀ Vi ∈ factors.filter (fun Vi => decide (2 ≤ Vi.2)),
      toPoly Vi.1 ^ Vi.2 ∣ toPoly D)
    (hWdec : toPoly D = toPoly Dstar * W) :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
      = (toQFun ((glocList fuel A D factors).foldl qadd qzero))′
        + algebraMap ℚ[X] (RatFunc ℚ)
            ((Polynomial.C (1 - ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).length : ℚ))
                * toPoly A
              + ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).map (residNumIncr fuel A D)).sum)
              / W)
          / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Dstar) := by
  set R := Polynomial.C (1 - ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).length : ℚ)) * toPoly A
    + ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).map (residNumIncr fuel A D)).sum with hR
  -- the whole-fold residual `am A/am D − g′ = am R/am D`.
  have hres := total_fold_residual_over_D fuel A D factors hD hV hstep
  rw [← hR] at hres
  -- the interference divisibility `W ∣ R`, now proven.
  have hWR : W ∣ R := by
    rw [hWeq]; exact prod_dvd_residNum fuel A D factors hnd hD hV hstep hpw hpow
  -- clear `am R/am D` to `am (R/W)/am Dstar`.
  have hclear := am_div_D_eq_div_Dstar (R := R) (D := toPoly D) (Dstar := toPoly Dstar)
    (W := W) hD hDstar hWdec hWR
  linear_combination hres + hclear

open scoped Differential in
-- Hermite reduction, multi-factor, UNCONDITIONAL (Bronstein §2.2/§2.5): the computable `hermiteReduce`
-- `g`-fold integrates the rational part `g`, leaving a residual `(R/W)/Dstar` over the **squarefree
-- radical** `Dstar` — with NO interference-divisibility hypothesis (`W ∣ R` discharged internally). The
-- per-factor data alone (residual identities, pairwise-coprime kept factors, `Vk^{ik} ∣ D`, the radical
-- decomposition `D = Dstar·W`, `W = ∏ Vk^{ik−1}`) suffices.
example (fuel : ℕ) (A D Dstar : CPoly) (factors : List (CPoly × ℕ))
    (W : ℚ[X]) (hWeq : W = ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).map
        (fun Vi => toPoly Vi.1 ^ (Vi.2 - 1))).prod)
    (hD : toPoly D ≠ 0) (hDstar : toPoly Dstar ≠ 0)
    (hnd : (factors.filter (fun Vi => decide (2 ≤ Vi.2))).Nodup)
    (hV : ∀ Vi ∈ factors, toPoly Vi.1 ≠ 0)
    (hstep : ∀ Vi ∈ factors, 2 ≤ Vi.2 →
      (toQFun (glocIncr fuel A D Vi))′
        = algebraMap ℚ[X] (RatFunc ℚ) (toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
          - algebraMap ℚ[X] (RatFunc ℚ) (residNumIncr fuel A D Vi)
            / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D))
    (hpw : (factors.filter (fun Vi => decide (2 ≤ Vi.2))).Pairwise
      (fun a b => IsRelPrime (toPoly a.1) (toPoly b.1)))
    (hpow : ∀ Vi ∈ factors.filter (fun Vi => decide (2 ≤ Vi.2)),
      toPoly Vi.1 ^ Vi.2 ∣ toPoly D)
    (hWdec : toPoly D = toPoly Dstar * W) :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
      = (toQFun ((glocList fuel A D factors).foldl qadd qzero))′
        + algebraMap ℚ[X] (RatFunc ℚ)
            ((Polynomial.C (1 - ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).length : ℚ))
                * toPoly A
              + ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).map (residNumIncr fuel A D)).sum)
              / W)
          / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Dstar) :=
  hermiteReduce_residual_correct_uncond' fuel A D Dstar factors W hWeq hD hDstar hnd hV hstep
    hpw hpow hWdec
