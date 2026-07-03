import DeepWiki.SymbolicIntegration.Computable.GenericBezout
import DeepWiki.SymbolicIntegration.Computable.FieldGcd
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! # Generic resultant/interpolation correctness over `CFieldSpec` (engine-only core)

The §2 ℚ-concrete templates `Compute.cresultant_eq` (`ComputeCorrectness`) and
`Compute.toPoly_cinterpolate_eval` (`RtResultantCorrectness`) certify the *computable* Euclidean-PRS
resultant `cresultant` and Lagrange interpolation `cinterpolate` against Mathlib's `Polynomial.resultant`
/ the two characterizing properties — but only over the **concrete** carrier `CPoly = List ℚ`. The
generic tower engine `cresultantG`/`cinterpolateG` (`ComputableGenericBezout`, over `[CField α]`) needs
the **same** correctness over any `[CFieldSpec α]`.

This file is the **engine-only core** of that correctness — everything that depends only on the generic
polynomial engine (`ComputableGenericBezout`/`ComputableFieldGcd`), so it can be imported by the
fuel-free `cresultantWf` (`ComputableFuelFreeResultant`) without pulling the §5.6 residue / `cgcdFF` layer.
The residue-resultant realizations and the `cIntegrateGFull` capstones live downstream in
`ComputableResultantGeneric`, which imports this core.

* **`toPolyG_cresultantG`** (the reusable foundation): `toPolyG (cresultantG fuel p q) =
  Polynomial.resultant (toPolyG p) (toPolyG q) (cdegG p) (cdegG q)` over `(CFieldSpec.K α)[X]`.
* **`eval_toPolyG_cinterpolateG`** / **`degree_toPolyG_cinterpolateG_lt`** (generic interpolation
  correctness): node evaluation `(toPolyG (cinterpolateG pts)).eval (toK zk) = toK yk` and the degree
  bound `degree (toPolyG (cinterpolateG pts)) < |pts|`.
* **`rtResultantSeed`** (the seed-generic abstract Rothstein–Trager resultant `R(z) = res_t(D, A − z·Dd)`)
  with its specialization `rtResultantSeed_eval` and degree bound `natDegree_rtResultantSeed_le`.

The deliverable is purely propositional (axioms `[propext, Classical.choice, Quot.sound]`, no
`native_decide`), reusable wherever the generic engine runs (§5.6 residues, §10 parallel Risch,
the fuel-free resultant `cresultantWf`). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace CPolyG

variable {α : Type*} [CField α] [CFieldSpec α]

/-! ### Generic quotient-degree and constant-power helpers -/

/-- **Generic constant power realizes `K`-power**: `toK (cfpow c n) = (toK c) ^ n`. -/
@[denote] theorem toK_cfpow (c : α) (n : ℕ) : CFieldSpec.toK (cfpow c n) = (CFieldSpec.toK c) ^ n := by
  induction n with
  | zero => simp [cfpow, CFieldSpec.toK_one]
  | succ n ih => rw [cfpow, CFieldSpec.toK_mul, ih, pow_succ']

/-- **Generic quotient degree**: for a non-constant divisor with `deg q ≤ deg p` and enough fuel,
`natDegree (cdivG …) + natDegree q = natDegree p` (the Euclidean quotient has degree `deg p − deg q`).
Supplies `resultant_add_mul_right`'s degree side-condition. The generic analogue of `cdiv_natDegree_add`. -/
theorem cdivG_natDegree_add (fuel : ℕ) (p q : CPolyG α) (hp : cnormG p ≠ []) (hq : cnormG q ≠ [])
    (hq2 : 2 ≤ (cnormG q : List α).length) (hpq : (cnormG q : List α).length ≤ (cnormG p : List α).length)
    (hfuel : (cnormG p : List α).length ≤ fuel) :
    (toPolyG (cdivG fuel p q)).natDegree + (toPolyG q).natDegree = (toPolyG p).natDegree := by
  have hP : toPolyG p ≠ 0 := fun h => hp ((cnormG_eq_nil_iff p).mpr h)
  have hQ : toPolyG q ≠ 0 := fun h => hq ((cnormG_eq_nil_iff q).mpr h)
  have hdiv : toPolyG p = toPolyG (cdivG fuel p q) * toPolyG q + toPolyG (cmodG fuel p q) := by
    have h := toPolyG_cdivmodG' fuel p q hq
    rw [cdivG, cmodG]; exact h
  have hr : (toPolyG (cmodG fuel p q)).natDegree < (toPolyG q).natDegree := by
    have hlen := cmodG_length_lt fuel p q hq hfuel
    have e1 := cdegG_eq_natDegree (cmodG fuel p q)
    have e2 := cdegG_eq_natDegree q
    simp only [cdegG] at e1 e2
    omega
  have hpq' : (toPolyG q).natDegree ≤ (toPolyG p).natDegree := by
    have e1 := cdegG_eq_natDegree p
    have e2 := cdegG_eq_natDegree q
    simp only [cdegG] at e1 e2
    omega
  have hquo : toPolyG (cdivG fuel p q) ≠ 0 := by
    intro h0
    rw [h0, zero_mul, zero_add] at hdiv
    rw [hdiv] at hpq'
    omega
  have key : (toPolyG (cdivG fuel p q) * toPolyG q).natDegree = (toPolyG p).natDegree := by
    have heq : toPolyG (cdivG fuel p q) * toPolyG q = toPolyG p - toPolyG (cmodG fuel p q) := by
      rw [hdiv]; ring
    rw [heq, natDegree_sub_eq_left_of_natDegree_lt (lt_of_lt_of_le hr hpq')]
  rwa [Polynomial.natDegree_mul hquo hQ] at key

/-! ### `cresultantG` invariances (mirroring `cresultant_cnorm`/`cdeg_cnorm`/`cmod_cnorm_both`) -/

omit [CFieldSpec α] in
theorem cmodG_cnormG_both (fuel : ℕ) (p q : CPolyG α) :
    cmodG fuel (cnormG p) (cnormG q) = cmodG fuel p q := by
  cases fuel with
  | zero => simp [cmodG, cdivmodG, cnormG_idem]
  | succ fuel => simp only [cmodG, cdivmodG, cnormG_idem]

/-- **`clagNumG` realizes `∏ (X − C (toK zⱼ))`**: the Horner bridge sends the generic basis numerator to
the abstract product of linear factors. -/
theorem toPolyG_clagNumG (zs : List α) :
    toPolyG (clagNumG zs) = (zs.map (fun z => Polynomial.X - Polynomial.C (CFieldSpec.toK z))).prod := by
  induction zs with
  | nil => simp [clagNumG, toPolyG_cons, CFieldSpec.toK_one]
  | cons z zs ih =>
    rw [clagNumG, toPolyG_cmulG, ih, List.map_cons, List.prod_cons]
    have hfac : toPolyG ([CField.neg z, CField.one] : CPolyG α)
        = Polynomial.X - Polynomial.C (CFieldSpec.toK z) := by
      rw [toPolyG_cons, toPolyG_cons, toPolyG_nil, CFieldSpec.toK_neg, CFieldSpec.toK_one, map_neg,
        map_one]; ring
    rw [hfac]

/-- **`toPolyG` of the `cinterpolateG` accumulator fold** is the running sum (generic analogue of
`toPoly_foldl_cadd`). -/
theorem toPolyG_foldl_caddG (f : α × α → CPolyG α) (pts : List (α × α)) (init : CPolyG α) :
    toPolyG (pts.foldl (fun acc p => caddG acc (f p)) init)
      = toPolyG init + (pts.map (fun p => toPolyG (f p))).sum := by
  induction pts generalizing init with
  | nil => simp
  | cons p ps ih =>
    rw [List.foldl_cons, ih, toPolyG_caddG, List.map_cons, List.sum_cons]
    ring

/-- The generic denominator fold `∏ acc·(zk − zⱼ)` equals `toK init · ∏ (toK zk − toK zⱼ)` under `toK`. -/
theorem toK_foldl_csub_mul (zk : α) (others : List α) (init : α) :
    CFieldSpec.toK (others.foldl (fun acc zj => CField.mul acc (CField.sub zk zj)) init)
      = CFieldSpec.toK init
        * (others.map (fun zj => CFieldSpec.toK zk - CFieldSpec.toK zj)).prod := by
  induction others generalizing init with
  | nil => simp
  | cons z zs ih =>
    rw [List.foldl_cons, ih, CFieldSpec.toK_mul, CFieldSpec.toK_sub, List.map_cons, List.prod_cons]
    ring

/-- The product `∏_{zⱼ ∈ others}(toK zk − toK zⱼ)` is nonzero when every `toK zⱼ ≠ toK zk`. -/
theorem prodG_sub_ne_zero {zk : α} {others : List α}
    (hne : ∀ zj ∈ others, CFieldSpec.toK zj ≠ CFieldSpec.toK zk) :
    (others.map (fun zj => CFieldSpec.toK zk - CFieldSpec.toK zj)).prod ≠ 0 := by
  rw [Ne, List.prod_eq_zero_iff]
  intro hy
  rw [List.mem_map] at hy
  obtain ⟨zj, hzj, hzeq⟩ := hy
  exact hne zj hzj (sub_eq_zero.mp hzeq).symm

/-- **The generic Lagrange term as a polynomial**: `toPolyG` of a single interpolation term
`cscaleG (yk/denom) (clagNumG others)`. -/
theorem toPolyG_termG (zk yk : α) (others : List α) :
    toPolyG (cscaleG (CField.div yk
        (others.foldl (fun acc zj => CField.mul acc (CField.sub zk zj)) CField.one))
        (clagNumG others))
      = Polynomial.C (CFieldSpec.toK yk
          / (others.map (fun zj => CFieldSpec.toK zk - CFieldSpec.toK zj)).prod)
        * (others.map (fun z => Polynomial.X - Polynomial.C (CFieldSpec.toK z))).prod := by
  rw [toPolyG_cscaleG, toPolyG_clagNumG, CFieldSpec.toK_div, toK_foldl_csub_mul, CFieldSpec.toK_one,
    one_mul]

/-- **Eval of a generic Lagrange term at a value** `x`. -/
theorem eval_toPolyG_termG (zk yk : α) (others : List α) (x : CFieldSpec.K α) :
    (toPolyG (cscaleG (CField.div yk
        (others.foldl (fun acc zj => CField.mul acc (CField.sub zk zj)) CField.one))
        (clagNumG others))).eval x
      = (CFieldSpec.toK yk / (others.map (fun zj => CFieldSpec.toK zk - CFieldSpec.toK zj)).prod)
        * (others.map (fun zj => x - CFieldSpec.toK zj)).prod := by
  rw [toPolyG_termG, eval_mul, eval_C]
  congr 1
  rw [eval_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro zj _
  simp [Function.comp, eval_sub, eval_X, eval_C]

/-- **Eval of a generic Lagrange term at its own node** `toK zk`: evaluates to `toK yk` (the denominator
matches the numerator product, nonzero since each `toK zⱼ ≠ toK zk`). -/
theorem eval_toPolyG_termG_at_self (zk yk : α) (others : List α)
    (hne : ∀ zj ∈ others, CFieldSpec.toK zj ≠ CFieldSpec.toK zk) :
    (toPolyG (cscaleG (CField.div yk
        (others.foldl (fun acc zj => CField.mul acc (CField.sub zk zj)) CField.one))
        (clagNumG others))).eval (CFieldSpec.toK zk) = CFieldSpec.toK yk := by
  rw [eval_toPolyG_termG, div_mul_cancel₀]
  exact prodG_sub_ne_zero hne

/-- **Eval of a generic Lagrange term at another node** `toK x` with `x ∈ others` is `0`: the numerator
product contains the vanishing factor `(toK x − toK x)`. -/
theorem eval_toPolyG_termG_at_other (zk yk x : α) (others : List α) (hx : x ∈ others) :
    (toPolyG (cscaleG (CField.div yk
        (others.foldl (fun acc zj => CField.mul acc (CField.sub zk zj)) CField.one))
        (clagNumG others))).eval (CFieldSpec.toK x) = 0 := by
  rw [eval_toPolyG_termG]
  have : (others.map (fun zj => CFieldSpec.toK x - CFieldSpec.toK zj)).prod = 0 := by
    rw [List.prod_eq_zero_iff, List.mem_map]
    exact ⟨x, hx, sub_self _⟩
  rw [this, mul_zero]

/-- The `cinterpolateG` local `term` function for a points list with abscissas `zs`. -/
private def cinterpTermG (zs : List α) (p : α × α) : CPolyG α :=
  cscaleG (CField.div p.2 ((zs.filter (fun zj => CField.isZero (CField.sub zj p.1) = false)).foldl
      (fun acc zj => CField.mul acc (CField.sub p.1 zj)) CField.one))
    (clagNumG (zs.filter (fun zj => CField.isZero (CField.sub zj p.1) = false)))

/-- **`cinterpolateG` as a normalized sum of terms** (under `toPolyG`). -/
theorem toPolyG_cinterpolateG (pts : List (α × α)) :
    toPolyG (cinterpolateG pts)
      = (pts.map (fun p => toPolyG (cinterpTermG (pts.map Prod.fst) p))).sum := by
  rw [cinterpolateG, toPolyG_cnormG, toPolyG_foldl_caddG]
  simp [cinterpTermG]

open scoped Classical in
/-- Summing `if toK p.1 = toK zk then toK p.2 else 0` over a points list whose abscissa images
`pts.map (toK ∘ fst)` are nodup picks out the unique entry `(zk, yk)` (`toK`-keyed). -/
theorem sum_ite_eq_of_nodup_toK_fst (pts : List (α × α))
    (hnodup : (pts.map (fun p => CFieldSpec.toK p.1)).Nodup)
    {zk yk : α} (hmem : (zk, yk) ∈ pts) :
    (pts.map (fun p => if CFieldSpec.toK p.1 = CFieldSpec.toK zk
        then CFieldSpec.toK p.2 else 0)).sum = CFieldSpec.toK yk := by
  induction pts with
  | nil => simp at hmem
  | cons p ps ih =>
    rw [List.map_cons, List.sum_cons]
    rw [List.map_cons, List.nodup_cons] at hnodup
    obtain ⟨hpnotin, hpsnodup⟩ := hnodup
    rcases List.mem_cons.mp hmem with hpeq | hpps
    · obtain rfl := hpeq
      rw [if_pos rfl]
      have hzero : (ps.map (fun q => if CFieldSpec.toK q.1 = CFieldSpec.toK zk
          then CFieldSpec.toK q.2 else 0)).sum = 0 := by
        apply List.sum_eq_zero
        intro w hw
        rw [List.mem_map] at hw
        obtain ⟨q, hq, rfl⟩ := hw
        rw [if_neg]
        intro hqzk
        exact hpnotin (by rw [List.mem_map]; exact ⟨q, hq, hqzk⟩)
      rw [hzero, add_zero]
    · have hp1 : CFieldSpec.toK p.1 ≠ CFieldSpec.toK zk := by
        intro h
        exact hpnotin (by rw [h, List.mem_map]; exact ⟨(zk, yk), hpps, rfl⟩)
      rw [if_neg hp1, zero_add]
      exact ih hpsnodup hpps

open scoped Classical in
/-- **`cinterpolateG` evaluation correctness**: when the abscissa images `pts.map (toK ∘ fst)` are
**distinct in `K`**, the interpolant evaluates to `toK yk` at each node `toK zk` —
`R(toK zk) = toK yk` for `(zk, yk) ∈ pts`. The generic analogue of `toPoly_cinterpolate_eval`: the
on-node term contributes `toK yk`, every off-node term vanishes. -/
theorem eval_toPolyG_cinterpolateG (pts : List (α × α))
    (hnodup : (pts.map (fun p => CFieldSpec.toK p.1)).Nodup)
    {zk yk : α} (hmem : (zk, yk) ∈ pts) :
    (toPolyG (cinterpolateG pts)).eval (CFieldSpec.toK zk) = CFieldSpec.toK yk := by
  rw [toPolyG_cinterpolateG]
  rw [show (List.map (fun p => toPolyG (cinterpTermG (pts.map Prod.fst) p)) pts).sum.eval
        (CFieldSpec.toK zk)
      = (Polynomial.evalRingHom (CFieldSpec.toK zk))
          (List.map (fun p => toPolyG (cinterpTermG (pts.map Prod.fst) p)) pts).sum from rfl,
    map_list_sum, List.map_map]
  set zs := pts.map Prod.fst with hzs
  have key : ∀ p ∈ pts,
      ((Polynomial.evalRingHom (CFieldSpec.toK zk)) ∘
          fun p => toPolyG (cinterpTermG zs p)) p
        = if CFieldSpec.toK p.1 = CFieldSpec.toK zk then CFieldSpec.toK p.2 else 0 := by
    rintro ⟨a, b⟩ hp
    simp only [Function.comp_apply, Polynomial.coe_evalRingHom, cinterpTermG]
    by_cases hak : CFieldSpec.toK a = CFieldSpec.toK zk
    · rw [if_pos hak, ← hak]
      apply eval_toPolyG_termG_at_self
      intro zj hzj
      rw [List.mem_filter] at hzj
      have hzj2 : CField.isZero (CField.sub zj a) = false := by
        have := hzj.2; simpa using this
      rw [Bool.eq_false_iff, Ne, CFieldSpec.isZero_iff, CFieldSpec.toK_sub, sub_eq_zero] at hzj2
      exact hzj2
    · rw [if_neg hak]
      apply eval_toPolyG_termG_at_other
      rw [List.mem_filter]
      refine ⟨by rw [hzs, List.mem_map]; exact ⟨(zk, yk), hmem, rfl⟩, ?_⟩
      have hgoal : CField.isZero (CField.sub zk a) = false := by
        rw [Bool.eq_false_iff, Ne, CFieldSpec.isZero_iff, CFieldSpec.toK_sub, sub_eq_zero]
        exact fun h => hak h.symm
      simpa using hgoal
  rw [List.map_congr_left key]
  exact sum_ite_eq_of_nodup_toK_fst pts hnodup hmem

/-- **Per-term degree bound** (generic): each `cinterpolateG` term has `natDegree ≤ |others|` (the
numerator is a product of `|others|` linear factors). -/
theorem natDegree_toPolyG_cinterpTermG_le (zs : List α) (p : α × α) :
    (toPolyG (cinterpTermG zs p)).natDegree
      ≤ (zs.filter (fun zj => CField.isZero (CField.sub zj p.1) = false)).length := by
  obtain ⟨a, b⟩ := p
  rw [cinterpTermG, toPolyG_termG]
  refine (natDegree_C_mul_le _ _).trans ?_
  refine (natDegree_list_prod_le _).trans ?_
  rw [List.map_map]
  refine (List.sum_le_card_nsmul _ 1 ?_).trans ?_
  · intro x hx
    rw [List.mem_map] at hx
    obtain ⟨zj, _, rfl⟩ := hx
    simp only [Function.comp_apply]
    exact natDegree_X_sub_C_le _
  · simp

/-- **`cinterpolateG` degree bound**: the interpolant has degree `< |pts|`. Each term has degree
`≤ |others| ≤ |pts| − 1` (the abscissa `zk`'s image is filtered out). The generic analogue of
`degree_toPoly_cinterpolate_lt`; the degree side of interpolation uniqueness. -/
theorem degree_toPolyG_cinterpolateG_lt (pts : List (α × α)) (hne : pts ≠ []) :
    (toPolyG (cinterpolateG pts)).degree < (pts.length : WithBot ℕ) := by
  rw [toPolyG_cinterpolateG]
  have hlen : 1 ≤ pts.length := List.length_pos_iff.mpr hne
  refine lt_of_le_of_lt (degree_list_sum_le_of_forall_degree_le _ ((pts.length : ℕ) - 1 : ℕ) ?_) ?_
  · intro p hp
    rw [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    apply Polynomial.degree_le_of_natDegree_le
    refine le_trans (natDegree_toPolyG_cinterpTermG_le (pts.map Prod.fst) q) ?_
    have hq1 : q.1 ∈ pts.map Prod.fst := List.mem_map.mpr ⟨q, hq, rfl⟩
    have hfilt : ((pts.map Prod.fst).filter
          (fun zj => CField.isZero (CField.sub zj q.1) = false)).length
        < (pts.map Prod.fst).length := by
      apply List.length_filter_lt_length_iff_exists.mpr
      refine ⟨q.1, hq1, ?_⟩
      -- the predicate `isZero (q.1 − q.1) = false` is itself `false` at `q.1`
      have hz : CField.isZero (CField.sub q.1 q.1) = true := by
        rw [CFieldSpec.isZero_iff, CFieldSpec.toK_sub, sub_self]
      simp [hz]
    rw [List.length_map] at hfilt
    omega
  · rw [Nat.cast_lt]; omega

/-- Restatement: generic interpolation evaluates to `toK yk` at each node `toK zk` when the node images
are distinct in `K`. -/
example (pts : List (α × α)) (hnodup : (pts.map (fun p => CFieldSpec.toK p.1)).Nodup)
    {zk yk : α} (hmem : (zk, yk) ∈ pts) :
    (toPolyG (cinterpolateG pts)).eval (CFieldSpec.toK zk) = CFieldSpec.toK yk :=
  eval_toPolyG_cinterpolateG pts hnodup hmem

end CPolyG

/-! ### The seed-generic abstract Rothstein–Trager resultant `R(z) = res_t(d, a − z·Dd)`

The §5.6 residue construction uses the **monomial seed** `Dd = Δd` rather than `derivative d`, so the
abstract bivariate resultant `R(z) = res_t(d, a − z·Dd) ∈ K[z]` needs to be seed-generic (the
`RationalIntegrationAlgorithms.rtResultant` fixes `Dd = derivative d`). `rtResultantSeed A D Dd` lifts
`D, A, Dd` to `(K[z])[t]` (constant `z = C z`) and eliminates `t`; `rtResultantSeed_eval` recovers the
parameter resultant `res_t(d, a − c·Dd)` at `z = c` (same formal `t`-degrees). The polynomial structure
the §5.6 residue resultant `cResidueResultantTower` realizes. -/

variable {K : Type*} [Field K]

/-- **Seed-generic abstract Rothstein–Trager resultant** `R(z) = res_t(D, A − z·Dd) ∈ K[z]`: `D, A, Dd`
lifted to `(K[z])[t]` (coefficients embedded by `C : K → K[z]`, the parameter `z` becoming the constant
`C X`), the resultant eliminating `t`. Formal `t`-degrees `(deg D, deg D)` — the §5.6 monomial seed `Δd`
has the *same* `t`-degree as `D` (`mapCoeffs d` preserves degree), unlike the d/dx seed `derivative D`
(degree `deg D − 1`), so the second formal degree is `deg D` here. The seed-generic analogue of
`rtResultant`. -/
noncomputable def rtResultantSeed (A D Dd : K[X]) : K[X] :=
  Polynomial.resultant (D.map (C : K →+* K[X]))
    (A.map (C : K →+* K[X]) - C Polynomial.X * Dd.map (C : K →+* K[X]))
    D.natDegree D.natDegree

/-- **Specialization of `rtResultantSeed`**: evaluating `R(z)` at `z = c` recovers the parameter
resultant `res_t(D, A − c·Dd)` (same formal `t`-degrees `(deg D, deg D)`). The seed-generic analogue
of `rtResultant_eval`. -/
theorem rtResultantSeed_eval (A D Dd : K[X]) (c : K) :
    (rtResultantSeed A D Dd).eval c
      = Polynomial.resultant D (A - C c * Dd) D.natDegree D.natDegree := by
  have hcomp : (Polynomial.evalRingHom c).comp (C : K →+* K[X]) = RingHom.id K := by
    ext k; simp
  show Polynomial.evalRingHom c (rtResultantSeed A D Dd) = _
  rw [rtResultantSeed, ← Polynomial.resultant_map_map]
  congr 1
  · rw [Polynomial.map_map, hcomp, Polynomial.map_id]
  · simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_map, Polynomial.map_C, hcomp,
      Polynomial.map_id]
    simp

/-- Restatement: the seed-generic abstract RT-resultant specializes at `z = c` to the parameter
resultant `res_t(D, A − c·Dd)`. -/
example (A D Dd : K[X]) (c : K) :
    (rtResultantSeed A D Dd).eval c
      = Polynomial.resultant D (A - C c * Dd) D.natDegree D.natDegree :=
  rtResultantSeed_eval A D Dd c

open Polynomial in
/-- **`natDegree` of a `K[X]`-matrix determinant** is bounded by the sum of per-column degree bounds:
if every entry of column `j` has `natDegree ≤ b j`, then `natDegree (det M) ≤ ∑ j, b j`. The `K`-generic
analogue of `natDegree_det_le_sum_col`. -/
theorem natDegree_det_le_sum_col {ι : Type*} [DecidableEq ι] [Fintype ι]
    (M : Matrix ι ι K[X]) (b : ι → ℕ) (hb : ∀ i j, (M i j).natDegree ≤ b j) :
    (M.det).natDegree ≤ ∑ j, b j := by
  rw [Matrix.det_apply]
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, ?_⟩
  intro σ _
  rw [Function.comp_apply]
  refine (natDegree_smul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  exact Finset.sum_le_sum (fun i _ => hb (σ i) i)

open Polynomial in
/-- **The `t`-coefficients of `rtResultantSeed`'s second polynomial have `z`-degree `≤ 1`**: each
`t`-coefficient of `A.map C − C z · Dd.map C` is `C (A.coeff k) − z · C (Dd.coeff k)`, degree `≤ 1`. -/
theorem natDegree_coeff_rtResultantSeed_g_le (A Dd : K[X]) (k : ℕ) :
    ((A.map (C : K →+* K[X]) - C Polynomial.X * Dd.map (C : K →+* K[X])).coeff k).natDegree ≤ 1 := by
  rw [Polynomial.coeff_sub, Polynomial.coeff_map, Polynomial.coeff_C_mul, Polynomial.coeff_map]
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · rw [Polynomial.natDegree_C]; exact Nat.zero_le 1
  · refine (Polynomial.natDegree_mul_le (p := (Polynomial.X : K[X]))
      (q := Polynomial.C (Dd.coeff k))).trans ?_
    rw [Polynomial.natDegree_X, Polynomial.natDegree_C]

open Polynomial in
/-- **`rtResultantSeed` has degree `≤ deg D` in `z`**: the Sylvester matrix of `D.map C` (constant
`z`-entries) and `A.map C − C z · Dd.map C` (degree-`≤ 1` `z`-entries) has only the `deg D` columns from
the second polynomial carrying a `z`, so its determinant has `z`-degree `≤ deg D`. The degree side of the
interpolation uniqueness (`deg D + 1` nodes determine `R(z)`). The seed-generic analogue of
`natDegree_rtResultant_le`. -/
theorem natDegree_rtResultantSeed_le (A D Dd : K[X]) :
    (rtResultantSeed A D Dd).natDegree ≤ D.natDegree := by
  rw [rtResultantSeed, resultant]
  refine le_trans (natDegree_det_le_sum_col _
    (fun j => j.addCases (fun _ => 1) (fun _ => 0)) ?_) ?_
  · intro i j
    rw [Polynomial.sylvester, Matrix.of_apply]
    refine j.addCases (fun j₁ => ?_) (fun j₁ => ?_)
    · simp only [Fin.addCases_left]
      split_ifs with h
      · exact natDegree_coeff_rtResultantSeed_g_le A Dd _
      · simp
    · simp only [Fin.addCases_right]
      split_ifs with h
      · rw [Polynomial.coeff_map, Polynomial.natDegree_C]
      · simp
  · rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      mul_one]
    rw [Finset.sum_eq_zero (fun i _ => by rw [Fin.addCases_right])]
    omega

end DeepWiki.SymbolicIntegration
