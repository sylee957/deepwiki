import DeepWiki.SymbolicIntegration.ComputableResultantGenericCore
import DeepWiki.SymbolicIntegration.ComputableLogPartTower
import DeepWiki.SymbolicIntegration.ComputableIntegrate
import DeepWiki.SymbolicIntegration.ComputableResidueBridge
import Mathlib.LinearAlgebra.Lagrange

/-! # The §5.6 residue resultant realizes `rtResultantSeed`, and the `cIntegrate` capstone

The engine-only generic resultant/interpolation correctness lives in
`ComputableResultantGenericCore` (`toPolyG_cresultantG`, `eval_toPolyG_cinterpolateG`,
`rtResultantSeed`/`natDegree_rtResultantSeed_le`). This file is the **QFunNZ-specific** layer that
composes those with the §5.6 residue construction over the ℚ(x) tower:

* **`toPolyG_cResidueResultantTower`** — the computable `cResidueResultantTower Dt fuel a d` (built by
  evaluation + Lagrange interpolation over `ℚ(x)[z]`) reads under `toPolyG` as the abstract
  seed-generic RT-resultant `rtResultantSeed (toPolyG a) (toPolyG d) (Δd)`, `Δd = implicitDeriv (toPolyG
  Dt) (toPolyG d)`. Both are `K[z]`-polynomials of degree `≤ deg d` agreeing at the `deg d + 1` rational
  nodes, hence equal by Lagrange uniqueness.
* **`cLogPart_keys_nodup`/`cLogPart_keys_image`** — discharge the residue-set enumeration
  `hkeysImage`/`hkeysNodup` to transparent candidate-list facts.
* **`cIntegrate_checkIdentity_uncond`** — the `hkeys`-free `cIntegrate` capstone `D(cIntegrate f) = f`
  (primitive regime, residue-set enumeration discharged), gated only on transparent degree/fuel and
  concrete candidate-list facts.

Purely propositional (axioms `[propext, Classical.choice, Quot.sound]`). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-! ### The §5.6 residue resultant `cResidueResultantTower` realizes `rtResultantSeed`

Composing the generic resultant correctness (step 1) with the interpolation correctness (step 2): the
computable `cResidueResultantTower Dt fuel a d` (built by evaluation + Lagrange interpolation over the
tower `ℚ(x)[z]`) reads under `toPolyG` as the abstract seed-generic RT-resultant `rtResultantSeed
(toPolyG a) (toPolyG d) (Δd)`, with `Δd = implicitDeriv (toPolyG Dt) (toPolyG d)` the monomial seed.
Both are `K[z]`-polynomials of degree `≤ deg d` agreeing at the `deg d + 1` rational nodes `0, …, deg d`,
hence equal by Lagrange uniqueness. -/

namespace CPolyG

open QFunNZ

/-- **`cAmcDd` reads as `A − C c · Δd`** under `toPolyG`: the §5.6 sampled second polynomial realizes
the abstract `a − z·Δd` (with `Δd = implicitDeriv (toPolyG Dt) (toPolyG d)`). -/
theorem toPolyG_cAmcDd (Dt a d : CPolyG QFunNZ) (c : QFunNZ) :
    toPolyG (cAmcDd Dt a d c)
      = toPolyG a - Polynomial.C (CFieldSpec.toK c)
          * Differential.implicitDeriv (toPolyG Dt) (toPolyG d) := by
  rw [cAmcDd, cDd, toPolyG_csubG, toPolyG_cscaleG, toPolyG_cmonomialDeriv]

/-- **Node-agreement** (monic `toPolyG d`): the §5.6 resultant sample `cresultantG fuel d
(cAmcDd Dt a d (ofConstNZ k))` reads under `toK` as the specialization of the abstract seed-generic
RT-resultant `rtResultantSeed (toPolyG a)(toPolyG d)(Δd)` at `toK(ofConstNZ k)`. The §5.6 analogue of
`cresultant_sample_eq_eval`: the formal degrees `(cdegG d, cdegG amc)` (used by `cresultantG`) and
`(deg d, deg d)` (used by `rtResultantSeed`) are reconciled by `resultant_add_right_deg`; the
augmentation factor `lc(d)^k = 1` since `toPolyG d` is monic. Needs `deg amc ≤ deg d`. -/
theorem cresultantG_sample_eq_eval (Dt a d : CPolyG QFunNZ) (k : ℚ)
    (hdmonic : (toPolyG d).Monic)
    (hamc : (toPolyG (cAmcDd Dt a d (ofConstNZ k))).natDegree ≤ (toPolyG d).natDegree)
    (fuel : ℕ)
    (hfuel : (cnormG d : List QFunNZ).length
      + (cnormG (cAmcDd Dt a d (ofConstNZ k)) : List QFunNZ).length + 2 ≤ fuel) :
    CFieldSpec.toK (cresultantG fuel d (cAmcDd Dt a d (ofConstNZ k)))
      = (rtResultantSeed (toPolyG a) (toPolyG d)
          (Differential.implicitDeriv (toPolyG Dt) (toPolyG d))).eval
            (CFieldSpec.toK (ofConstNZ k)) := by
  set amc := cAmcDd Dt a d (ofConstNZ k) with hamcdef
  rw [toPolyG_cresultantG fuel d amc hfuel, cdegG_eq_natDegree d, cdegG_eq_natDegree amc,
    rtResultantSeed_eval, ← toPolyG_cAmcDd Dt a d (ofConstNZ k)]
  -- reconcile the RHS's second formal degree `deg d` down to actual `deg amc` (the LHS's slot)
  obtain ⟨j, hj⟩ : ∃ j, (toPolyG d).natDegree = (toPolyG amc).natDegree + j :=
    ⟨(toPolyG d).natDegree - (toPolyG amc).natDegree, by omega⟩
  conv_rhs => rw [show (toPolyG d).natDegree = (toPolyG amc).natDegree + j from hj]
  rw [Polynomial.resultant_add_right_deg (toPolyG d) (toPolyG amc) ((toPolyG amc).natDegree + j)
    (toPolyG amc).natDegree j le_rfl, ← hj,
    show (toPolyG d).coeff (toPolyG d).natDegree = (toPolyG d).leadingCoeff from rfl,
    hdmonic.leadingCoeff, one_pow, one_mul]

/-- The tower fraction field's `Algebra ℚ` (matching the keystone instances in
`ComputableIntegrateCorrect`/`towerLogPart_*`), so `algebraMap ℚ (CFieldSpec.K QFunNZ)` resolves. -/
noncomputable local instance : Algebra ℚ (CFieldSpec.K QFunNZ) :=
  inferInstanceAs (Algebra ℚ (RatFunc ℚ))

/-- **`toK (ofConstNZ n)` is the constant rational function `n`**: the tower bridge sends the rational
constant `ofConstNZ n` to `algebraMap ℚ (RatFunc ℚ) n` (the composite `ℚ → ℚ[x] → ℚ(x)`). -/
theorem toK_ofConstNZ (n : ℚ) :
    CFieldSpec.toK (ofConstNZ n) = algebraMap ℚ (CFieldSpec.K QFunNZ) n := by
  show toQFunNZ (ofConstNZ n) = _
  rw [toQFunNZ, ofConstNZ, ofNumDen, Compute.toQFun]
  have h1 : Compute.toPoly ([n] : Compute.CPoly) = Polynomial.C n := by
    rw [Compute.toPoly_cons, Compute.toPoly_nil]; simp
  have h2 : Compute.toPoly ([1] : Compute.CPoly) = 1 := by
    rw [Compute.toPoly_cons, Compute.toPoly_nil]; simp
  rw [h1, h2, map_one, div_one]
  show (algebraMap ℚ[X] (RatFunc ℚ)) (Polynomial.C n) = algebraMap ℚ (RatFunc ℚ) n
  rw [IsScalarTower.algebraMap_eq ℚ ℚ[X] (RatFunc ℚ), RingHom.comp_apply, Polynomial.algebraMap_eq]

/-- **`toK ∘ ofConstNZ` is injective**: distinct rational constants have distinct tower images
(`algebraMap ℚ (RatFunc ℚ)` is injective). -/
theorem toK_ofConstNZ_injective :
    Function.Injective (fun n : ℚ => CFieldSpec.toK (ofConstNZ n)) := by
  intro x y hxy
  simp only [toK_ofConstNZ] at hxy
  exact FaithfulSMul.algebraMap_injective ℚ (CFieldSpec.K QFunNZ) hxy

open scoped Classical in
/-- **The §5.6 residue resultant realizes the seed-generic abstract RT-resultant** (the polynomial match,
combining steps 1–3): for monic `toPolyG d` with `deg(a − k·Δd) ≤ deg d` at each integer node and
sufficient fuel, the computable `cResidueResultantTower Dt fuel a d` reads under `toPolyG` as the abstract
`rtResultantSeed (toPolyG a)(toPolyG d)(Δd)`, `Δd = implicitDeriv (toPolyG Dt)(toPolyG d)`. Both are
`K[z]`-polynomials of degree `≤ deg d` agreeing at the `deg d + 1` rational nodes `0, …, deg d`
(`cresultantG_sample_eq_eval`), hence equal by Lagrange uniqueness
(`Lagrange.eq_of_degrees_lt_of_eval_index_eq`). -/
theorem toPolyG_cResidueResultantTower (Dt a d : CPolyG QFunNZ) (fuel : ℕ)
    (hdmonic : (toPolyG d).Monic)
    (hamc : ∀ k ∈ Finset.range (cdegG d + 1),
      (toPolyG (cAmcDd Dt a d (ofConstNZ (k : ℚ)))).natDegree ≤ (toPolyG d).natDegree)
    (hfuel : ∀ k ∈ Finset.range (cdegG d + 1),
      (cnormG d : List QFunNZ).length
        + (cnormG (cAmcDd Dt a d (ofConstNZ (k : ℚ))) : List QFunNZ).length + 2 ≤ fuel) :
    toPolyG (cResidueResultantTower Dt fuel a d)
      = rtResultantSeed (toPolyG a) (toPolyG d)
          (Differential.implicitDeriv (toPolyG Dt) (toPolyG d)) := by
  classical
  -- the abscissa list `zs`, exactly as `cResidueResultantTower`'s inner `do`-block builds it
  set zs : List ℚ := (do let k ← List.range (cdegG d + 1); pure (k : ℚ)) with hzs
  -- the node points, exactly as `cResidueResultantTower` builds them
  set pts : List (QFunNZ × QFunNZ) := zs.map (fun k : ℚ =>
    (ofConstNZ k, cresultantG fuel d (cAmcDd Dt a d (ofConstNZ k)))) with hpts
  have hcompute : cResidueResultantTower Dt fuel a d = cinterpolateG pts := rfl
  -- `zs = (range (n+1)).map (↑·)`, a clean cast-mapped range
  have hzsmap : zs = (List.range (cdegG d + 1)).map (fun k : ℕ => (k : ℚ)) := by
    rw [hzs]; exact List.flatMap_pure_eq_map _ _
  have hzsnodup : zs.Nodup := by
    rw [hzsmap]
    exact (List.nodup_range (n := cdegG d + 1)).map (fun a' b' h => by exact_mod_cast h)
  have hfst : pts.map (fun p => CFieldSpec.toK p.1)
      = zs.map (fun k : ℚ => CFieldSpec.toK (ofConstNZ k)) := by
    rw [hpts, List.map_map]; rfl
  have hnodup : (pts.map (fun p => CFieldSpec.toK p.1)).Nodup := by
    rw [hfst]
    exact hzsnodup.map toK_ofConstNZ_injective
  have hne : pts ≠ [] := by rw [hpts, hzsmap]; simp [List.range_succ]
  have hlen : pts.length = cdegG d + 1 := by
    rw [hpts, List.length_map, hzsmap, List.length_map, List.length_range]
  -- `#zs.toFinset = cdegG d + 1` (zs nodup)
  have hcard : zs.toFinset.card = cdegG d + 1 := by
    rw [List.toFinset_card_of_nodup hzsnodup, hzsmap, List.length_map, List.length_range]
  rw [hcompute]
  symm
  refine Polynomial.eq_of_degrees_lt_of_eval_index_eq (R := CFieldSpec.K QFunNZ) (ι := ℚ)
    (s := zs.toFinset) (v := fun k => CFieldSpec.toK (ofConstNZ k))
    (f := rtResultantSeed (toPolyG a) (toPolyG d)
      (Differential.implicitDeriv (toPolyG Dt) (toPolyG d)))
    (g := toPolyG (cinterpolateG pts)) ?_ ?_ ?_ ?_
  · -- `Set.InjOn` of the node map on `zs.toFinset`
    intro a' _ b' _ h
    exact toK_ofConstNZ_injective h
  · -- `degree (rtResultantSeed) < #zs.toFinset`
    rw [hcard, Nat.cast_withBot]
    refine lt_of_le_of_lt (Polynomial.degree_le_natDegree) ?_
    rw [Nat.cast_withBot, WithBot.coe_lt_coe]
    have h1 := natDegree_rtResultantSeed_le (toPolyG a) (toPolyG d)
      (Differential.implicitDeriv (toPolyG Dt) (toPolyG d))
    have h2 := cdegG_eq_natDegree d
    omega
  · -- `degree (toPolyG (cinterpolateG pts)) < #zs.toFinset`
    rw [hcard, Nat.cast_withBot]
    have := degree_toPolyG_cinterpolateG_lt pts hne
    rw [hlen] at this
    simpa [Nat.cast_withBot] using this
  · -- agree at the nodes `i ∈ zs.toFinset`, i.e. `i = (k : ℚ)` for some `k ∈ range (n+1)`
    intro i hi
    rw [List.mem_toFinset, hzsmap, List.mem_map] at hi
    obtain ⟨k, hk, rfl⟩ := hi
    rw [List.mem_range] at hk
    have hmem : (ofConstNZ (k : ℚ), cresultantG fuel d (cAmcDd Dt a d (ofConstNZ (k : ℚ)))) ∈ pts := by
      rw [hpts, hzsmap, List.mem_map]
      exact ⟨(k : ℚ), List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩, rfl⟩
    rw [eval_toPolyG_cinterpolateG pts hnodup hmem]
    -- the sample equals the abstract eval
    exact (cresultantG_sample_eq_eval Dt a d (k : ℚ) hdmonic
      (hamc k (Finset.mem_range.mpr hk)) fuel (hfuel k (Finset.mem_range.mpr hk))).symm

open scoped Classical in
/-- Restatement: the §5.6 computable residue resultant `cResidueResultantTower` reads under `toPolyG` as
the abstract seed-generic Rothstein–Trager resultant `rtResultantSeed`. -/
example (Dt a d : CPolyG QFunNZ) (fuel : ℕ) (hdmonic : (toPolyG d).Monic)
    (hamc : ∀ k ∈ Finset.range (cdegG d + 1),
      (toPolyG (cAmcDd Dt a d (ofConstNZ (k : ℚ)))).natDegree ≤ (toPolyG d).natDegree)
    (hfuel : ∀ k ∈ Finset.range (cdegG d + 1),
      (cnormG d : List QFunNZ).length
        + (cnormG (cAmcDd Dt a d (ofConstNZ (k : ℚ))) : List QFunNZ).length + 2 ≤ fuel) :
    toPolyG (cResidueResultantTower Dt fuel a d)
      = rtResultantSeed (toPolyG a) (toPolyG d)
          (Differential.implicitDeriv (toPolyG Dt) (toPolyG d)) :=
  toPolyG_cResidueResultantTower Dt a d fuel hdmonic hamc hfuel

/-! ### Step 4: discharging the residue-set enumeration `hkeysImage`/`hkeysNodup`

The concrete `cRationalResidues Dt fuel a d cands` keeps a candidate `c ∈ cands` iff
`cevalG R (ofConstNZ c) = 0` (`R = cResidueResultantTower`), i.e. iff `R(toK(ofConstNZ c)) = 0` in `K`.
By step 3 `R` reads as `rtResultantSeed`, so `R(toK(ofConstNZ c)) = res_t(d, a − c·Δd)` (the parameter
resultant), and by Mathlib's `resultant_eq_zero_iff` + the split squarefree `toPolyG d = nodal s id`
this vanishes exactly when `c` is a residue of some root `α ∈ s`. Composing this per-candidate criterion
gives the residue-set match `hkeysImage`/`hkeysNodup` — provided the candidate list `cands` is
**complete** (contains every rational residue) and **nodup** under `toK ∘ ofConstNZ`. -/

section CEvalBridge

variable {α : Type*} [CField α] [CFieldSpec α]

/-- **`cevalG` realizes polynomial evaluation under `toK`**: `toK (cevalG p c) = (toPolyG p).eval
(toK c)`. The Horner evaluation in `α` agrees with the abstract `K`-evaluation through the bridge. -/
theorem toK_cevalG (p : CPolyG α) (c : α) :
    CFieldSpec.toK (cevalG p c) = (toPolyG p).eval (CFieldSpec.toK c) := by
  rw [cevalG]
  induction p with
  | nil => simp [CFieldSpec.toK_zero]
  | cons a' as ih =>
    rw [List.foldr_cons, CFieldSpec.toK_add, CFieldSpec.toK_mul, ih, toPolyG_cons, eval_add,
      eval_C, eval_mul, eval_X]

end CEvalBridge

end CPolyG

/-! ### The resultant-vanishing residue criterion over a split squarefree denominator

For `d = nodal s id` (split squarefree, monic) over a field `K` and a seed `Dd` nonzero at every root,
the parameter resultant `res_t(d, a − c·Dd)` (with formal degrees `(deg d, deg d)`) vanishes exactly
when some root `α ∈ s` has residue `a(α)/Dd(α) = c`. This is the base-field analogue of
`residue_iff_resultant_eq_zero` (which needs `IsAlgClosed`): here the roots already live in `K` because
`d` splits over `s`. The bridge from the §5.6 residue resultant (via step 3) to the residue set. -/

open scoped Classical in
/-- **Resultant-vanishing residue criterion** (split squarefree, base field): for `d = nodal s id` and a
seed `Dd` with `Dd(α) ≠ 0` at each `α ∈ s`, given `deg(a − C c·Dd) ≤ deg d`, the resultant
`res_t(d, a − C c·Dd)` (formal degrees `(deg d, deg d)`) is `0` iff some root `α ∈ s` has residue
`a(α)/Dd(α) = c`. Reduces the `(deg d, deg d)` resultant to the default-degree one (monic `d`), turns
`resultant = 0` into non-coprimality (`resultant_eq_zero_iff`), and—since `d` splits over `s`—into a
common root `α ∈ s` of `d` and `a − C c·Dd`, which the §5.6 residue criterion
`residue_eq_iff_isRoot_sub_seed` reads as the residue equation. -/
theorem resultant_split_eq_zero_iff_residue {K : Type*} [Field K] (s : Finset K) (a Dd : K[X])
    (hDd : ∀ α ∈ s, Dd.eval α ≠ 0) (c : K)
    (hEdeg : (a - C c * Dd).natDegree ≤ (Lagrange.nodal s id).natDegree) :
    Polynomial.resultant (Lagrange.nodal s id) (a - C c * Dd)
        (Lagrange.nodal s id).natDegree (Lagrange.nodal s id).natDegree = 0
      ↔ ∃ α ∈ s, a.eval α / Dd.eval α = c := by
  classical
  set d := Lagrange.nodal s id with hd
  set E := a - C c * Dd with hE
  have hd0 : d ≠ 0 := hd ▸ Lagrange.nodal_ne_zero
  have hdmonic : d.Monic := hd ▸ Lagrange.nodal_monic
  have hdprod : d = ∏ α ∈ s, (X - C α) := by simp [hd, Lagrange.nodal_eq, id]
  have hdroots : d.roots = s.val := by rw [hdprod, roots_prod_X_sub_C]
  -- reduce the `(deg d, deg d)` resultant to the default-degree resultant (monic `d`, `deg E ≤ deg d`)
  have hred : Polynomial.resultant d E d.natDegree d.natDegree = Polynomial.resultant d E := by
    obtain ⟨j, hj⟩ : ∃ j, d.natDegree = E.natDegree + j :=
      ⟨d.natDegree - E.natDegree, by omega⟩
    conv_lhs => rw [show d.natDegree = E.natDegree + j from hj]
    rw [Polynomial.resultant_add_right_deg d E (E.natDegree + j) E.natDegree j le_rfl, ← hj,
      show d.coeff d.natDegree = d.leadingCoeff from rfl, hdmonic.leadingCoeff, one_pow, one_mul]
  rw [hred, Polynomial.resultant_eq_zero_iff, and_iff_right (Or.inl hd0)]
  -- the §5.6 residue criterion at a root (inline): `a(α)/Dd(α) = c ↔ (a − C c·Dd).IsRoot α`
  have hrescrit : ∀ α ∈ s, (a.eval α / Dd.eval α = c ↔ E.IsRoot α) := by
    intro α hαs
    rw [hE, IsRoot.def, eval_sub, eval_mul, eval_C, sub_eq_zero, div_eq_iff (hDd α hαs)]
  -- `IsCoprime d E ↔ ∀ α ∈ s, ¬ E.IsRoot α` (split `d`, each factor `X − α` prime in the PID `K[X]`)
  have hcopiff : IsCoprime d E ↔ ∀ α ∈ s, a.eval α / Dd.eval α ≠ c := by
    rw [hdprod, IsCoprime.prod_left_iff]
    refine forall_congr' fun α => ?_
    refine imp_congr_right fun hαs => ?_
    rw [(prime_X_sub_C α).coprime_iff_not_dvd, dvd_iff_isRoot, ← hrescrit α hαs]
  rw [not_iff_comm, hcopiff, not_exists]
  simp only [not_and, ne_eq]

namespace CPolyG

open QFunNZ

open scoped Classical Differential in
/-- **The per-candidate residue criterion** (composing steps 1–4a): in the split squarefree primitive
regime `toPolyG d = Lagrange.nodal s id` with the monomial seed `Δd` nonzero at every root, a candidate
`c ∈ ℚ` passes `cRationalResidues`' test — `cisZeroG [cevalG R (ofConstNZ c)] = true` for
`R = cResidueResultantTower Dt fuel a d` — **iff** `c` is a residue, i.e.
`∃ α ∈ s, A(α)/(Δd)(α) = toK(ofConstNZ c)`. The vanishing of the residue resultant at `c` reads through
step 3 (`toPolyG_cResidueResultantTower` + `rtResultantSeed_eval`) as `res_t(d, a − c·Δd) = 0`, which
`resultant_split_eq_zero_iff_residue` turns into the residue equation. -/
theorem cisZeroG_cevalG_cResidueResultantTower_iff (Dt a d : CPolyG QFunNZ) (fuel : ℕ)
    (s : Finset (CFieldSpec.K QFunNZ)) (hden : toPolyG d = Lagrange.nodal s id)
    (hDd : ∀ α ∈ s, (Differential.implicitDeriv (toPolyG Dt) (toPolyG d)).eval α ≠ 0)
    (hadeg : (toPolyG a).natDegree ≤ (toPolyG d).natDegree)
    (hδdeg : (Differential.implicitDeriv (toPolyG Dt) (toPolyG d)).natDegree
      ≤ (toPolyG d).natDegree)
    (hamc : ∀ k ∈ Finset.range (cdegG d + 1),
      (toPolyG (cAmcDd Dt a d (ofConstNZ (k : ℚ)))).natDegree ≤ (toPolyG d).natDegree)
    (hfuel : ∀ k ∈ Finset.range (cdegG d + 1),
      (cnormG d : List QFunNZ).length
        + (cnormG (cAmcDd Dt a d (ofConstNZ (k : ℚ))) : List QFunNZ).length + 2 ≤ fuel) (c : ℚ) :
    cisZeroG [cevalG (cResidueResultantTower Dt fuel a d) (ofConstNZ c)] = true
      ↔ ∃ α ∈ s, (toPolyG a).eval α
          / (Differential.implicitDeriv (toPolyG Dt) (toPolyG d)).eval α
            = CFieldSpec.toK (ofConstNZ c) := by
  classical
  set δ := Differential.implicitDeriv (toPolyG Dt) (toPolyG d) with hδ
  have hdmonic : (toPolyG d).Monic := hden ▸ Lagrange.nodal_monic
  -- `cisZeroG [cevalG R c'] = true ↔ R(toK c') = 0`
  have hzero : cisZeroG [cevalG (cResidueResultantTower Dt fuel a d) (ofConstNZ c)] = true
      ↔ (toPolyG (cResidueResultantTower Dt fuel a d)).eval (CFieldSpec.toK (ofConstNZ c)) = 0 := by
    rw [cisZeroG_iff, toPolyG_cons, toPolyG_nil, mul_zero, add_zero, ← toK_cevalG,
      Polynomial.C_eq_zero]
  rw [hzero, toPolyG_cResidueResultantTower Dt a d fuel hdmonic hamc hfuel, ← hδ,
    rtResultantSeed_eval]
  -- `deg(a − C c·δ) ≤ deg d` (from `deg a ≤ deg d` and `deg δ ≤ deg d`)
  have hEdeg : (toPolyG a - C (CFieldSpec.toK (ofConstNZ c)) * δ).natDegree
      ≤ (toPolyG d).natDegree :=
    (natDegree_sub_le _ _).trans (max_le hadeg
      ((natDegree_C_mul_le _ _).trans hδdeg))
  rw [show (toPolyG d).natDegree = (Lagrange.nodal s id).natDegree from by rw [hden]] at hEdeg
  -- specialize the split-field criterion (with `d = nodal s id`)
  rw [hden, resultant_split_eq_zero_iff_residue s (toPolyG a) δ hDd
    (CFieldSpec.toK (ofConstNZ c)) hEdeg]

/-! ### Discharging `hkeysImage`/`hkeysNodup` — the residue-set enumeration

The `cLogPart Dt fuel a d cands` keys are exactly `cRationalResidues = cands.filter (residue test)`, and
by the per-candidate criterion a candidate passes the test iff it is a residue. So the keys' `toK`-images
are exactly `{toK(ofConstNZ c) | c ∈ cands, c a residue}`. Equating this with `s.image res`
(`hkeysImage`) and proving it nodup (`hkeysNodup`) requires two transparent facts about the candidate
list: it is **complete** (every residue value `res α`, `α ∈ s`, is `toK(ofConstNZ c)` for some `c ∈ cands`)
and **`toK`-distinct** (the residue-passing candidates have distinct `toK ∘ ofConstNZ` images). These are
exactly the residue-enumeration preconditions the §5.6 capstone needs. -/

open scoped Classical Differential in
/-- **`hkeysNodup` discharged**: if the residue-passing candidates have distinct `toK ∘ ofConstNZ`
images, the `cLogPart` keys are nodup under `toK ∘ ofConstNZ`. (Immediate from `cLogPart`'s keys being
`cRationalResidues` and the candidate-distinctness hypothesis.) -/
theorem cLogPart_keys_nodup (Dt a d : CPolyG QFunNZ) (fuel : ℕ) (cands : List ℚ)
    (hdistinct : (cands.filter (fun c =>
        cisZeroG [cevalG (cResidueResultantTower Dt fuel a d) (ofConstNZ c)])).map
        (fun c => CFieldSpec.toK (ofConstNZ c)) |>.Nodup) :
    ((cLogPart Dt fuel a d cands).map (fun cv => CFieldSpec.toK (ofConstNZ cv.1))).Nodup := by
  rw [cLogPart, cRationalResidues, List.map_map]
  exact hdistinct

open scoped Classical Differential in
/-- **`hkeysImage` discharged** (the residue-set enumeration, composing step 4b): in the split squarefree
primitive regime, if the candidate list `cands` is **complete** — every residue value `res α` (`α ∈ s`)
equals `toK(ofConstNZ c)` for some `c ∈ cands` — then the `toK`-images of the `cLogPart` keys are exactly
the distinct-residue set `s.image res`. Each `cLogPart` key is a residue (per-candidate criterion
`cisZeroG_cevalG_cResidueResultantTower_iff`), and conversely each residue is reached by a candidate
(completeness). This is exactly the `hkeysImage` hypothesis of the §5.6 capstone
`cIntegrate_checkIdentity_of_residueData`. -/
theorem cLogPart_keys_image (Dt a d : CPolyG QFunNZ) (fuel : ℕ) (cands : List ℚ)
    (s : Finset (CFieldSpec.K QFunNZ)) (hden : toPolyG d = Lagrange.nodal s id)
    (hDd : ∀ α ∈ s, (Differential.implicitDeriv (toPolyG Dt) (toPolyG d)).eval α ≠ 0)
    (hadeg : (toPolyG a).natDegree ≤ (toPolyG d).natDegree)
    (hδdeg : (Differential.implicitDeriv (toPolyG Dt) (toPolyG d)).natDegree
      ≤ (toPolyG d).natDegree)
    (hamc : ∀ k ∈ Finset.range (cdegG d + 1),
      (toPolyG (cAmcDd Dt a d (ofConstNZ (k : ℚ)))).natDegree ≤ (toPolyG d).natDegree)
    (hfuel : ∀ k ∈ Finset.range (cdegG d + 1),
      (cnormG d : List QFunNZ).length
        + (cnormG (cAmcDd Dt a d (ofConstNZ (k : ℚ))) : List QFunNZ).length + 2 ≤ fuel)
    (hcompl : ∀ α ∈ s, ∃ c ∈ cands, (toPolyG a).eval α
        / (Differential.implicitDeriv (toPolyG Dt) (toPolyG d)).eval α
          = CFieldSpec.toK (ofConstNZ c)) :
    ((cLogPart Dt fuel a d cands).map (fun cv => CFieldSpec.toK (ofConstNZ cv.1))).toFinset
      = s.image (fun α => (toPolyG a).eval α
          / (Differential.implicitDeriv (toPolyG Dt) (toPolyG d)).eval α) := by
  classical
  set res : CFieldSpec.K QFunNZ → CFieldSpec.K QFunNZ := fun α => (toPolyG a).eval α
    / (Differential.implicitDeriv (toPolyG Dt) (toPolyG d)).eval α with hres
  -- the key-image set is `{toK(ofConstNZ c) | c ∈ cands ∧ test c}`
  rw [cLogPart, cRationalResidues, List.map_map]
  ext v
  rw [List.mem_toFinset, List.mem_map, Finset.mem_image]
  constructor
  · rintro ⟨c, hc, rfl⟩
    rw [List.mem_filter] at hc
    obtain ⟨_, htest⟩ := hc
    -- `c` passes the test ⟹ `c` is a residue
    obtain ⟨α, hαs, hαres⟩ := (cisZeroG_cevalG_cResidueResultantTower_iff Dt a d fuel s hden hDd
      hadeg hδdeg hamc hfuel c).mp htest
    exact ⟨α, hαs, hαres⟩
  · rintro ⟨α, hαs, rfl⟩
    -- a residue `res α` is reached by some complete candidate `c`, which then passes the test
    obtain ⟨c, hcc, hceq⟩ := hcompl α hαs
    refine ⟨c, ?_, hceq.symm⟩
    rw [List.mem_filter]
    refine ⟨hcc, ?_⟩
    -- `c` is a residue (`res α = toK(ofConstNZ c)`), so it passes the test
    exact (cisZeroG_cevalG_cResidueResultantTower_iff Dt a d fuel s hden hDd hadeg hδdeg hamc hfuel
      c).mpr ⟨α, hαs, hceq⟩

end CPolyG

/-! ### The `hkeys`-free capstone — `D(cIntegrate f) = f` with the residue-set gap discharged

Feeding the residue-set discharge (`cLogPart_keys_image`/`cLogPart_keys_nodup`) into
`cIntegrate_checkIdentity_of_residueData` (`ComputableResidueBridge`) removes its last *opaque*
mathematical inputs `hkeysImage`/`hkeysNodup` (the residue-set enumeration), replacing them with the
**transparent, inspectable** candidate-list facts `hcompl` (completeness) and `hdistinct` (`toK`-distinct
residue-passing candidates) plus the transparent degree side-conditions. The headline `D(cIntegrate f) =
f` for all primitive-regime inputs, now gated only on the primitive split-squarefree regime and
inspectable, concrete preconditions — no opaque `hLog` *and* no opaque residue-set enumeration. -/

open DeepWiki.SymbolicIntegration.CPolyG QFunNZ in
open scoped Classical Differential in
/-- **The `hkeys`-free `cIntegrate` capstone** (`D(cIntegrate f) = f`, primitive regime, residue-set
*enumeration* discharged): `cIntegrate_checkIdentity_of_residueData` with its opaque residue-set inputs
`hkeysImage`/`hkeysNodup` **discharged** by `cLogPart_keys_image`/`cLogPart_keys_nodup` — replaced by the
transparent candidate-completeness `hcompl` (every residue value `res α`, `α ∈ s`, is some
`toK(ofConstNZ c)`, `c ∈ cands`), the candidate `toK`-distinctness `hdistinct`, and the degree
side-conditions `hadeg`/`hδdeg`/`hamc`/`hfuelR`. The lone remaining inputs are the primitive
split-squarefree regime data and these inspectable, concrete candidate/degree preconditions — no opaque
`hLog` and no opaque residue-set enumeration black box. -/
theorem cIntegrate_checkIdentity_uncond (Dt : CPolyG QFunNZ) {w₀ : CFieldSpec.K QFunNZ}
    (htop : toPolyG Dt = C w₀) (fuel : ℕ) (a d : CPolyG QFunNZ) (cands : List ℚ)
    (fp b ds cn dn : CPolyG QFunNZ)
    (hcanon : canonicalRepresentationFast Dt fuel a d = (fp, (b, ds), (cn, dn)))
    (gnumH gdenH hNum hDen : CPolyG QFunNZ)
    (hHermite : cHermiteReduceTower Dt fuel cn dn = ((gnumH, gdenH), (hNum, hDen)))
    (pq prem : CPolyG QFunNZ)
    (hpoly : cPrimitivePolyIntegrate Dt fuel fp = (pq, prem))
    (hpremZero : cisZeroG prem = true)
    (hcanreg : CCanonicalRepFastRegular Dt fuel a d)
    (hfs0 : towerAlg (toPolyG b) / towerAlg (toPolyG ds) = 0)
    (gprimeNum resNum resDen : CPolyG QFunNZ)
    (hgprimeE : gprimeNum
      = csubG (cmulG (cmonomialDeriv Dt gnumH) gdenH) (cmulG gnumH (cmonomialDeriv Dt gdenH)))
    (hresNum : resNum = csubG (cmulG cn (cmulG gdenH gdenH)) (cmulG dn gprimeNum))
    (hresDen : resDen = cmulG dn (cmulG gdenH gdenH))
    (hhNumE : hNum = cdivG fuel (cmulG resNum hDen) resDen)
    (hq0 : cnormG resDen ≠ [])
    (hfuelH : (cnormG (cmulG resNum hDen) : List QFunNZ).length ≤ fuel)
    (hdvd : toPolyG resDen ∣ toPolyG (cmulG resNum hDen))
    (hgdenHne : toPolyG gdenH ≠ 0) (hHDenne : toPolyG hDen ≠ 0) (hdnne : toPolyG dn ≠ 0)
    (hlognz : ∀ cv ∈ cLogPart Dt fuel hNum hDen cands, toPolyG cv.2 ≠ 0)
    -- the §5.6 primitive split-squarefree regime + transparent residue-enumeration data
    (s : Finset (CFieldSpec.K QFunNZ)) (hden : toPolyG hDen = Lagrange.nodal s id)
    (hAh : (toPolyG hNum).degree < s.card)
    (hb0 : ∀ α ∈ s, w₀ - α′ ≠ 0)
    (hDd : ∀ α ∈ s, (Differential.implicitDeriv (toPolyG Dt) (toPolyG hDen)).eval α ≠ 0)
    (hadeg : (toPolyG hNum).natDegree ≤ (toPolyG hDen).natDegree)
    (hδdeg : (Differential.implicitDeriv (toPolyG Dt) (toPolyG hDen)).natDegree
      ≤ (toPolyG hDen).natDegree)
    (hamc : ∀ k ∈ Finset.range (cdegG hDen + 1),
      (toPolyG (cAmcDd Dt hNum hDen (ofConstNZ (k : ℚ)))).natDegree ≤ (toPolyG hDen).natDegree)
    (hfuelR : ∀ k ∈ Finset.range (cdegG hDen + 1),
      (cnormG hDen : List QFunNZ).length
        + (cnormG (cAmcDd Dt hNum hDen (ofConstNZ (k : ℚ))) : List QFunNZ).length + 2 ≤ fuel)
    (hcompl : ∀ α ∈ s, ∃ c ∈ cands, (toPolyG hNum).eval α
        / (Differential.implicitDeriv (toPolyG Dt) (toPolyG hDen)).eval α
          = CFieldSpec.toK (ofConstNZ c))
    (hdistinct : (cands.filter (fun c =>
        cisZeroG [cevalG (cResidueResultantTower Dt fuel hNum hDen) (ofConstNZ c)])).map
        (fun c => CFieldSpec.toK (ofConstNZ c)) |>.Nodup)
    (hreg : ∀ c ∈ cRationalResidues Dt fuel hNum hDen cands, PrimPRSInputs fuel
      (if Compute.bdeg (clearDenoms hDen)
            < Compute.bdeg (clearDenoms (cAmcDd Dt hNum hDen (ofConstNZ c)))
        then clearDenoms (cAmcDd Dt hNum hDen (ofConstNZ c)) else clearDenoms hDen)
      (if Compute.bdeg (clearDenoms hDen)
            < Compute.bdeg (clearDenoms (cAmcDd Dt hNum hDen (ofConstNZ c)))
        then clearDenoms hDen else clearDenoms (cAmcDd Dt hNum hDen (ofConstNZ c)))) :
    ∃ res : IntegralResult, cIntegrate Dt fuel a d cands = some res
      ∧ IntegralResult.checkIdentity Dt res a d = true := by
  classical
  refine cIntegrate_checkIdentity_of_residueData Dt htop fuel a d cands fp b ds cn dn hcanon
    gnumH gdenH hNum hDen hHermite pq prem hpoly hpremZero hcanreg hfs0 gprimeNum resNum resDen
    hgprimeE hresNum hresDen hhNumE hq0 hfuelH hdvd hgdenHne hHDenne hdnne hlognz s hden hAh hb0 hDd
    ?_ ?_ hreg
  · -- `hkeysNodup` from candidate `toK`-distinctness
    exact cLogPart_keys_nodup Dt hNum hDen fuel cands hdistinct
  · -- `hkeysImage` from the residue-set discharge (the residue function uses `nodal s id = toPolyG hDen`)
    rw [← hden]
    exact cLogPart_keys_image Dt hNum hDen fuel cands s hden hDd hadeg hδdeg hamc hfuelR hcompl

open DeepWiki.SymbolicIntegration.CPolyG QFunNZ in
open scoped Classical Differential in
/-- Restatement: the `hkeys`-free `cIntegrate` capstone — `D(cIntegrate f) = f` in the primitive
split-squarefree regime, with the residue-set enumeration discharged to candidate completeness +
distinctness (no opaque `hLog`, no opaque `hkeysImage`/`hkeysNodup`). -/
example (Dt : CPolyG QFunNZ) {w₀ : CFieldSpec.K QFunNZ} (htop : toPolyG Dt = C w₀) (fuel : ℕ)
    (a d : CPolyG QFunNZ) (cands : List ℚ) (fp b ds cn dn : CPolyG QFunNZ)
    (hcanon : canonicalRepresentationFast Dt fuel a d = (fp, (b, ds), (cn, dn)))
    (gnumH gdenH hNum hDen : CPolyG QFunNZ)
    (hHermite : cHermiteReduceTower Dt fuel cn dn = ((gnumH, gdenH), (hNum, hDen)))
    (pq prem : CPolyG QFunNZ) (hpoly : cPrimitivePolyIntegrate Dt fuel fp = (pq, prem))
    (hpremZero : cisZeroG prem = true) (hcanreg : CCanonicalRepFastRegular Dt fuel a d)
    (hfs0 : towerAlg (toPolyG b) / towerAlg (toPolyG ds) = 0)
    (gprimeNum resNum resDen : CPolyG QFunNZ)
    (hgprimeE : gprimeNum
      = csubG (cmulG (cmonomialDeriv Dt gnumH) gdenH) (cmulG gnumH (cmonomialDeriv Dt gdenH)))
    (hresNum : resNum = csubG (cmulG cn (cmulG gdenH gdenH)) (cmulG dn gprimeNum))
    (hresDen : resDen = cmulG dn (cmulG gdenH gdenH))
    (hhNumE : hNum = cdivG fuel (cmulG resNum hDen) resDen) (hq0 : cnormG resDen ≠ [])
    (hfuelH : (cnormG (cmulG resNum hDen) : List QFunNZ).length ≤ fuel)
    (hdvd : toPolyG resDen ∣ toPolyG (cmulG resNum hDen))
    (hgdenHne : toPolyG gdenH ≠ 0) (hHDenne : toPolyG hDen ≠ 0) (hdnne : toPolyG dn ≠ 0)
    (hlognz : ∀ cv ∈ cLogPart Dt fuel hNum hDen cands, toPolyG cv.2 ≠ 0)
    (s : Finset (CFieldSpec.K QFunNZ)) (hden : toPolyG hDen = Lagrange.nodal s id)
    (hAh : (toPolyG hNum).degree < s.card) (hb0 : ∀ α ∈ s, w₀ - α′ ≠ 0)
    (hDd : ∀ α ∈ s, (Differential.implicitDeriv (toPolyG Dt) (toPolyG hDen)).eval α ≠ 0)
    (hadeg : (toPolyG hNum).natDegree ≤ (toPolyG hDen).natDegree)
    (hδdeg : (Differential.implicitDeriv (toPolyG Dt) (toPolyG hDen)).natDegree
      ≤ (toPolyG hDen).natDegree)
    (hamc : ∀ k ∈ Finset.range (cdegG hDen + 1),
      (toPolyG (cAmcDd Dt hNum hDen (ofConstNZ (k : ℚ)))).natDegree ≤ (toPolyG hDen).natDegree)
    (hfuelR : ∀ k ∈ Finset.range (cdegG hDen + 1),
      (cnormG hDen : List QFunNZ).length
        + (cnormG (cAmcDd Dt hNum hDen (ofConstNZ (k : ℚ))) : List QFunNZ).length + 2 ≤ fuel)
    (hcompl : ∀ α ∈ s, ∃ c ∈ cands, (toPolyG hNum).eval α
        / (Differential.implicitDeriv (toPolyG Dt) (toPolyG hDen)).eval α
          = CFieldSpec.toK (ofConstNZ c))
    (hdistinct : (cands.filter (fun c =>
        cisZeroG [cevalG (cResidueResultantTower Dt fuel hNum hDen) (ofConstNZ c)])).map
        (fun c => CFieldSpec.toK (ofConstNZ c)) |>.Nodup)
    (hreg : ∀ c ∈ cRationalResidues Dt fuel hNum hDen cands, PrimPRSInputs fuel
      (if Compute.bdeg (clearDenoms hDen)
            < Compute.bdeg (clearDenoms (cAmcDd Dt hNum hDen (ofConstNZ c)))
        then clearDenoms (cAmcDd Dt hNum hDen (ofConstNZ c)) else clearDenoms hDen)
      (if Compute.bdeg (clearDenoms hDen)
            < Compute.bdeg (clearDenoms (cAmcDd Dt hNum hDen (ofConstNZ c)))
        then clearDenoms hDen else clearDenoms (cAmcDd Dt hNum hDen (ofConstNZ c)))) :
    ∃ res : IntegralResult, cIntegrate Dt fuel a d cands = some res
      ∧ IntegralResult.checkIdentity Dt res a d = true :=
  cIntegrate_checkIdentity_uncond Dt htop fuel a d cands fp b ds cn dn hcanon gnumH gdenH hNum hDen
    hHermite pq prem hpoly hpremZero hcanreg hfs0 gprimeNum resNum resDen hgprimeE hresNum hresDen
    hhNumE hq0 hfuelH hdvd hgdenHne hHDenne hdnne hlognz s hden hAh hb0 hDd hadeg hδdeg hamc hfuelR
    hcompl hdistinct hreg

/-! ### Why the `fₛ = 0` gate is FAITHFUL — the engine `cIntegrate` discards the special part

The headline `cIntegrate_checkIdentity_uncond` is gated on `hfs0 : fₛ = b/dₛ = 0` (the canonical-split
**special** part is zero) and on the `prem = 0` branch. This gate is **not** an artifact of the proof — it
is forced by the *structure of the engine* `cIntegrate` (`ComputableIntegrate`), which one is forbidden to
modify. Reading the engine body (`canonicalRepresentationFast Dt fuel a d = (fp, (b, ds), (cn, dn))`,
then integrate `fp` via `cPrimitivePolyIntegrate` and `cn/dn` via `cIntegrateReduced`), the special-part
component `(b, ds)` is bound to **unused** `let`-binders `(_b, _ds)`: it is never passed to the §6 RDE
oracle `cRischDE`/`cRationalRDE`, never to any integration routine, never into the returned
`IntegralResult`. The engine integrates **only** `fₚ + fₙ`. Hence `D(cIntegrate f)` is the derivative of
`g + ∑ cᵢ·log vᵢ`, which (by `cIntegrate_field_identity`) recovers `fₚ + fₙ`, *not* `f = fₚ + fₛ + fₙ`.
The identity `D(cIntegrate f) = f` can therefore hold **iff** `fₛ = 0`; the `hfs0` gate is the exact
faithful boundary, and broadening to `fₛ ≠ 0` would require *editing the engine* to wire `(b, ds)` through
the RDE oracle — out of scope here. The two theorems below make this structural fact citable: (1)
`cIntegrate`'s output is **independent of the special part** `(b, ds)` (it is a closed form in
`fp, cn, dn, cands` alone), and (2) the nonzero-remainder branch returns `none` (so the
`checkIdentity` headline only ever lives in the `prem = 0` branch). -/

open DeepWiki.SymbolicIntegration.CPolyG QFunNZ in
/-- **`cIntegrate` discards the canonical-split special part `fₛ = b/dₛ`** (faithfulness of the `hfs0`
gate): given the canonical split `canonicalRepresentationFast Dt fuel a d = (fp, (b, ds), (cn, dn))`, the
engine's value is the closed form built from `fp`, `cn`, `dn`, `cands` **alone** — the special-part
component `(b, ds)` never appears. The reduced normal part `cIntegrateReduced … cn dn cands` and the
primitive polynomial part `cPrimitivePolyIntegrate … fp` are the only integrated pieces; `(b, ds)` is bound
to unused `let`-binders in the engine body, so `cIntegrate` does *not* integrate `fₛ`. This is exactly why
`cIntegrate_checkIdentity_uncond` must assume `fₛ = 0`: the engine returns the integral of `fₚ + fₙ`, so
`D(cIntegrate f) = f` only when the discarded `fₛ` vanishes. -/
theorem cIntegrate_indep_special (Dt : CPolyG QFunNZ) (fuel : ℕ) (a d : CPolyG QFunNZ)
    (cands : List ℚ) (fp b ds cn dn : CPolyG QFunNZ)
    (hcanon : canonicalRepresentationFast Dt fuel a d = (fp, (b, ds), (cn, dn))) :
    cIntegrate Dt fuel a d cands =
      (let nrm := cIntegrateReduced Dt fuel cn dn cands
       let (pq, prem) := cPrimitivePolyIntegrate Dt fuel fp
       if cisZeroG prem then
         some (⟨(caddG (cmulG nrm.rational.1 [CField.one]) (cmulG pq nrm.rational.2),
                 nrm.rational.2), nrm.logs⟩ : IntegralResult)
       else none) := by
  rw [cIntegrate, hcanon]

open DeepWiki.SymbolicIntegration.CPolyG QFunNZ in
/-- **The nonzero polynomial-remainder branch returns `none`** (faithfulness of the `prem = 0` gate): when
the primitive polynomial integration leaves a nonzero `t`-degree remainder
(`cisZeroG prem = false`), `cIntegrate` returns `none` — it produces no `IntegralResult` to check. So the
`checkIdentity` headline (`cIntegrate = some res ∧ checkIdentity res = true`) only ever lives in the
`prem = 0` branch; the `hpremZero` gate of `cIntegrate_checkIdentity_uncond` is the engine's own `if`, not
a proof artifact. A nonzero remainder is the engine's non-elementary report (the primitive sub-case did not
dispose of the polynomial part), so there is nothing to broaden off `prem ≠ 0`. -/
theorem cIntegrate_none_of_prem_ne (Dt : CPolyG QFunNZ) (fuel : ℕ) (a d : CPolyG QFunNZ)
    (cands : List ℚ) (fp b ds cn dn : CPolyG QFunNZ)
    (hcanon : canonicalRepresentationFast Dt fuel a d = (fp, (b, ds), (cn, dn)))
    (pq prem : CPolyG QFunNZ) (hpoly : cPrimitivePolyIntegrate Dt fuel fp = (pq, prem))
    (hprem : cisZeroG prem = false) :
    cIntegrate Dt fuel a d cands = none := by
  rw [cIntegrate, hcanon]
  simp only [hpoly, hprem, Bool.false_eq_true, if_false]

open DeepWiki.SymbolicIntegration.CPolyG QFunNZ in
/-- Restatement: `cIntegrate`'s result depends only on the polynomial and normal parts `fp, cn, dn` (and
`cands`) of the canonical split — the special part `fₛ = b/dₛ` is structurally discarded, so the `fₛ = 0`
gate of the headline `cIntegrate_checkIdentity_uncond` is faithful. -/
example (Dt : CPolyG QFunNZ) (fuel : ℕ) (a d : CPolyG QFunNZ) (cands : List ℚ)
    (fp b ds cn dn : CPolyG QFunNZ)
    (hcanon : canonicalRepresentationFast Dt fuel a d = (fp, (b, ds), (cn, dn))) :
    cIntegrate Dt fuel a d cands =
      (let nrm := cIntegrateReduced Dt fuel cn dn cands
       let (pq, prem) := cPrimitivePolyIntegrate Dt fuel fp
       if cisZeroG prem then
         some (⟨(caddG (cmulG nrm.rational.1 [CField.one]) (cmulG pq nrm.rational.2),
                 nrm.rational.2), nrm.logs⟩ : IntegralResult)
       else none) :=
  cIntegrate_indep_special Dt fuel a d cands fp b ds cn dn hcanon

-- Axiom audits for the headline deliverables (`[propext, Classical.choice, Quot.sound]` — no
-- `native_decide`, no `sorryAx`).
#print axioms cIntegrate_indep_special
#print axioms cIntegrate_none_of_prem_ne
#print axioms CPolyG.toPolyG_cresultantG
#print axioms CPolyG.eval_toPolyG_cinterpolateG
#print axioms CPolyG.toPolyG_cResidueResultantTower
#print axioms resultant_split_eq_zero_iff_residue
#print axioms CPolyG.cisZeroG_cevalG_cResidueResultantTower_iff
#print axioms CPolyG.cLogPart_keys_image
#print axioms cIntegrate_checkIdentity_uncond

end DeepWiki.SymbolicIntegration
