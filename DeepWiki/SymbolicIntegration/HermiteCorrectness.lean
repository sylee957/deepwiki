import DeepWiki.SymbolicIntegration.ComputeCorrectness
import DeepWiki.SymbolicIntegration.RationalFunctionDerivative

/-! # Correctness of the computable Hermite reduction (`cdiophantine`/`hermiteInner`)
The computable Hermite engine of `HermiteCompute` (`cdiophantine`, `hermiteInner`, `hermiteReduce`) is
validated *pointwise* by `native_decide` on Example 2.2.1. This file upgrades the **Bézout/Diophantine
solver** step to *proven on all inputs*: through the `toPoly : CPoly → ℚ[X]` bridge the computable
`cdiophantine` realizes the noncomputable `diophantineSolveReduced` of `RationalIntegrationAlgorithms`.

The spine is a **uniqueness** lemma: the reduced Bézout solution `(B, C)` of `B·p + C·q = rhs` with
`deg B < deg q` is unique for coprime `p, q` (the standard `(B₁−B₂)·p = (C₂−C₁)·q` + coprimality +
degree argument). Both `cdiophantine` (via `toPoly_cdiophantine` and the remainder-degree bound
`cmod_length_lt`) and `diophantineSolveReduced` (via `diophantineSolveReduced_spec` and
`diophantineSolveReduced_fst_degree_lt`) produce such a solution, so their `toPoly`-images agree. From
the cofactor `B` the partner `C` is then pinned by the Bézout equation, giving the full agreement. This
transfers `hermiteReducePower_spec`'s per-power Hermite correctness onto the computable side. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration.Compute

/-! ### Uniqueness of the reduced Bézout cofactor -/

/-- **Reduced-Bézout cofactor uniqueness**: for coprime `p, q` with `q ≠ 0`, if two cofactors `B₁, B₂`
both have a partner `C₁, C₂` solving `Bᵢ·p + Cᵢ·q = rhs` and both are proper (`deg Bᵢ < deg q`), then
`B₁ = B₂`. The standard argument: `(B₁−B₂)·p = (C₂−C₁)·q`, so `q ∣ (B₁−B₂)·p`; coprimality gives
`q ∣ B₁−B₂`, and `deg(B₁−B₂) < deg q` forces `B₁−B₂ = 0`. -/
theorem reduced_bezout_fst_unique {p q B₁ C₁ B₂ C₂ rhs : ℚ[X]} (hpq : IsCoprime p q)
    (h₁ : B₁ * p + C₁ * q = rhs) (h₂ : B₂ * p + C₂ * q = rhs)
    (hd₁ : B₁.degree < q.degree) (hd₂ : B₂.degree < q.degree) :
    B₁ = B₂ := by
  have hcross : (B₁ - B₂) * p = (C₂ - C₁) * q := by linear_combination h₁ - h₂
  have hdvd : q ∣ (B₁ - B₂) * p := ⟨C₂ - C₁, by rw [hcross]; ring⟩
  have hqB : q ∣ (B₁ - B₂) := (hpq.symm).dvd_of_dvd_mul_right hdvd
  have hsub : B₁ - B₂ = 0 := by
    by_contra hne
    have hle : q.degree ≤ (B₁ - B₂).degree := Polynomial.degree_le_of_dvd hqB hne
    have hlt : (B₁ - B₂).degree < q.degree :=
      lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hd₁ hd₂)
    exact absurd (lt_of_le_of_lt hle hlt) (lt_irrefl _)
  exact sub_eq_zero.mp hsub

/-- **Reduced-Bézout partner uniqueness**: once the first cofactor `B` agrees, the partner `C` is
pinned by the Bézout equation `B·p + C·q = rhs` (cancel the nonzero `q` in the integral domain). -/
theorem reduced_bezout_snd_unique {p q B C₁ C₂ rhs : ℚ[X]} (hq : q ≠ 0)
    (h₁ : B * p + C₁ * q = rhs) (h₂ : B * p + C₂ * q = rhs) :
    C₁ = C₂ := by
  have : C₁ * q = C₂ * q := by linear_combination h₁ - h₂
  exact mul_right_cancel₀ hq this

/-! ### `cdiophantine` realizes `diophantineSolveReduced` (degree bound for `B`)

The computable cofactor `B = (cdiophantine fuel p q rhs).1` is the remainder `cnorm (cmod fuel S q)`
with `S = cscale (clead g)⁻¹ (cmul rhs s)`, so it is degree-reduced just like `diophantineSolveReduced`'s
`% b`. -/

/-- The first computable cofactor `(cdiophantine fuel p q rhs).1` is the normalized remainder
`cnorm (cmod fuel (cscale (clead (cgcdExt fuel p q).1)⁻¹ (cmul rhs (cgcdExt fuel p q).2.1)) q)`. -/
theorem cdiophantine_fst_eq (fuel : ℕ) (p q rhs : CPoly) :
    (cdiophantine fuel p q rhs).1
      = cnorm (cmod fuel
          (cscale (clead (cgcdExt fuel p q).1)⁻¹ (cmul rhs (cgcdExt fuel p q).2.1)) q) := by
  rcases hgst : cgcdExt fuel p q with ⟨g, s, t⟩
  simp only [cdiophantine, hgst, cmod]

/-- **Degree bound for the computable cofactor `B`**: with enough fuel and a nonzero divisor `q`,
`(toPoly (cdiophantine fuel p q rhs).1).natDegree < (toPoly q).natDegree`. From `cmod_length_lt`
(the remainder is properly reduced) transported to `natDegree` via `cdeg_eq_natDegree`. -/
theorem cdiophantine_fst_degree_lt (fuel : ℕ) (p q rhs : CPoly) (hq : cnorm q ≠ [])
    (hfuel : (cnorm (cscale (clead (cgcdExt fuel p q).1)⁻¹
        (cmul rhs (cgcdExt fuel p q).2.1))).length ≤ fuel) :
    (toPoly (cdiophantine fuel p q rhs).1).degree < (toPoly q).degree := by
  set S := cscale (clead (cgcdExt fuel p q).1)⁻¹ (cmul rhs (cgcdExt fuel p q).2.1) with hS
  rw [cdiophantine_fst_eq, ← hS]
  have hlen : (cnorm (cmod fuel S q)).length < (cnorm q).length :=
    cmod_length_lt fuel S q hq hfuel
  rw [toPoly_cnorm]
  have hqne0 : toPoly q ≠ 0 := fun h => hq ((cnorm_eq_nil_iff q).mpr h)
  rcases eq_or_ne (cnorm (cmod fuel S q)) [] with h0 | h0
  · have hz : toPoly (cmod fuel S q) = 0 := by rw [← toPoly_cnorm, h0, toPoly_nil]
    rw [hz, Polynomial.degree_zero]
    exact bot_lt_iff_ne_bot.mpr (fun h => hqne0 (Polynomial.degree_eq_bot.mp h))
  · have e1 : (cnorm (cmod fuel S q)).length = (toPoly (cmod fuel S q)).natDegree + 1 :=
      length_cnorm_of_ne _ h0
    have e2 : (cnorm q).length = (toPoly q).natDegree + 1 := length_cnorm_of_ne q hq
    have hndlt : (toPoly (cmod fuel S q)).natDegree < (toPoly q).natDegree := by omega
    have hne1 : toPoly (cmod fuel S q) ≠ 0 := fun h => h0 ((cnorm_eq_nil_iff _).mpr h)
    rw [Polynomial.degree_eq_natDegree hne1, Polynomial.degree_eq_natDegree hqne0, Nat.cast_lt]
    exact hndlt

/-! ### The agreement `cdiophantine ↔ diophantineSolveReduced`

Both solvers return a degree-reduced Bézout solution of `B·p + C·q = rhs` for coprime `p, q`. The
computable one is correct (`toPoly_cdiophantine`) and degree-reduced (`cdiophantine_fst_degree_lt`);
the abstract one is correct (`diophantineSolveReduced_spec`) and degree-reduced
(`diophantineSolveReduced_fst_degree_lt`). By the uniqueness lemmas they agree under `toPoly`. -/

open Classical in
/-- **First-cofactor agreement** `toPoly (cdiophantine fuel p q rhs).1 = (diophantineSolveReduced
(toPoly p) (toPoly q) (toPoly rhs)).1`: the computable Bézout solver's degree-reduced `B` equals the
abstract `diophantineSolveReduced`'s. Hypotheses: `p, q` coprime in `ℚ[X]`, `q ≠ 0` (`cnorm q ≠ []`),
the computable gcd `(cgcdExt fuel p q).1` is a nonzero constant (the coprimality the Hermite call sites
guarantee, as in `toPoly_cdiophantine`), and enough fuel for the remainder to be properly reduced.
Proved by `reduced_bezout_fst_unique` from the two correctness + degree facts. -/
theorem toPoly_cdiophantine_fst_eq (fuel : ℕ) (p q rhs : CPoly)
    (hq : cnorm q ≠ []) (hcop : IsCoprime (toPoly p) (toPoly q))
    (hg : toPoly (cgcdExt fuel p q).1 = Polynomial.C (clead (cgcdExt fuel p q).1))
    (hgc : clead (cgcdExt fuel p q).1 ≠ 0)
    (hfuel : (cnorm (cscale (clead (cgcdExt fuel p q).1)⁻¹
        (cmul rhs (cgcdExt fuel p q).2.1))).length ≤ fuel) :
    toPoly (cdiophantine fuel p q rhs).1
      = (diophantineSolveReduced (toPoly p) (toPoly q) (toPoly rhs)).1 := by
  have hq0 : toPoly q ≠ 0 := fun h => hq ((cnorm_eq_nil_iff q).mpr h)
  -- computable side: correctness + degree bound
  have hc_eq := toPoly_cdiophantine fuel p q rhs hq hg hgc
  have hc_deg := cdiophantine_fst_degree_lt fuel p q rhs hq hfuel
  -- abstract side: correctness + degree bound
  have ha_eq := diophantineSolveReduced_spec hcop (toPoly rhs)
  have ha_deg := diophantineSolveReduced_fst_degree_lt (a := toPoly p) hq0 (toPoly rhs)
  -- both solve `B·p + C·q = rhs` (rewrite the abstract `p·B + q·C` to `B·p + C·q`)
  refine reduced_bezout_fst_unique (C₁ := toPoly (cdiophantine fuel p q rhs).2)
    (C₂ := (diophantineSolveReduced (toPoly p) (toPoly q) (toPoly rhs)).2)
    (rhs := toPoly rhs) hcop ?_ ?_ hc_deg ha_deg
  · linear_combination hc_eq
  · linear_combination ha_eq

open Classical in
/-- **Second-cofactor agreement** `toPoly (cdiophantine fuel p q rhs).2 = (diophantineSolveReduced
(toPoly p) (toPoly q) (toPoly rhs)).2`: once the first cofactor `B` agrees, the partner `C` is pinned
by the Bézout equation `B·p + C·q = rhs` (`reduced_bezout_snd_unique`, cancelling the nonzero `q`). -/
theorem toPoly_cdiophantine_snd_eq (fuel : ℕ) (p q rhs : CPoly)
    (hq : cnorm q ≠ []) (hcop : IsCoprime (toPoly p) (toPoly q))
    (hg : toPoly (cgcdExt fuel p q).1 = Polynomial.C (clead (cgcdExt fuel p q).1))
    (hgc : clead (cgcdExt fuel p q).1 ≠ 0)
    (hfuel : (cnorm (cscale (clead (cgcdExt fuel p q).1)⁻¹
        (cmul rhs (cgcdExt fuel p q).2.1))).length ≤ fuel) :
    toPoly (cdiophantine fuel p q rhs).2
      = (diophantineSolveReduced (toPoly p) (toPoly q) (toPoly rhs)).2 := by
  have hq0 : toPoly q ≠ 0 := fun h => hq ((cnorm_eq_nil_iff q).mpr h)
  have hfst := toPoly_cdiophantine_fst_eq fuel p q rhs hq hcop hg hgc hfuel
  have hc_eq := toPoly_cdiophantine fuel p q rhs hq hg hgc
  have ha_eq := diophantineSolveReduced_spec hcop (toPoly rhs)
  -- with `B` equal, the two Bézout equations have the same `B·p` term; cancel `q`.
  refine reduced_bezout_snd_unique (p := toPoly p)
    (B := (diophantineSolveReduced (toPoly p) (toPoly q) (toPoly rhs)).1)
    (rhs := toPoly rhs) hq0 ?_ ?_
  · rw [← hfst]; linear_combination hc_eq
  · linear_combination ha_eq

open Classical in
/-- **Full `cdiophantine ↔ diophantineSolveReduced` agreement** (both cofactors): under `toPoly`, the
computable Bézout solver realizes the abstract `diophantineSolveReduced` pair. This is the bridge that
transfers `hermiteReducePower_spec`'s per-power Hermite correctness onto the computable Hermite engine —
the computable inner loop's Bézout step computes (under `toPoly`) exactly the polynomial the abstract
correctness proof uses. -/
theorem toPoly_cdiophantine_eq (fuel : ℕ) (p q rhs : CPoly)
    (hq : cnorm q ≠ []) (hcop : IsCoprime (toPoly p) (toPoly q))
    (hg : toPoly (cgcdExt fuel p q).1 = Polynomial.C (clead (cgcdExt fuel p q).1))
    (hgc : clead (cgcdExt fuel p q).1 ≠ 0)
    (hfuel : (cnorm (cscale (clead (cgcdExt fuel p q).1)⁻¹
        (cmul rhs (cgcdExt fuel p q).2.1))).length ≤ fuel) :
    (toPoly (cdiophantine fuel p q rhs).1, toPoly (cdiophantine fuel p q rhs).2)
      = diophantineSolveReduced (toPoly p) (toPoly q) (toPoly rhs) :=
  Prod.ext (toPoly_cdiophantine_fst_eq fuel p q rhs hq hcop hg hgc hfuel)
    (toPoly_cdiophantine_snd_eq fuel p q rhs hq hcop hg hgc hfuel)

-- The reduced-Bézout cofactor of `cdiophantine` equals the abstract `diophantineSolveReduced`'s.
example (fuel : ℕ) (p q rhs : CPoly)
    (hq : cnorm q ≠ []) (hcop : IsCoprime (toPoly p) (toPoly q))
    (hg : toPoly (cgcdExt fuel p q).1 = Polynomial.C (clead (cgcdExt fuel p q).1))
    (hgc : clead (cgcdExt fuel p q).1 ≠ 0)
    (hfuel : (cnorm (cscale (clead (cgcdExt fuel p q).1)⁻¹
        (cmul rhs (cgcdExt fuel p q).2.1))).length ≤ fuel) :
    toPoly (cdiophantine fuel p q rhs).1
      = (diophantineSolveReduced (toPoly p) (toPoly q) (toPoly rhs)).1 :=
  toPoly_cdiophantine_fst_eq fuel p q rhs hq hcop hg hgc hfuel

/-! ### The `hermiteInner` step identity and inner-loop invariant (in `RatFunc ℚ`)

`hermiteInner` peels rational pieces `B/Vʲ` from a *global* fraction `A/(U·Vᵏ)` (`U = D/Vⁱ`), one
power at a time, so its per-step identity carries the extra `U` factor that `hermite_reduction_step`
does not. The identity below is a pure `RatFunc ℚ` calculation from the Bézout relation
`B·(U·V') + C·V = −A/(j+1)` the computable `cdiophantine` produces. -/

open scoped Differential in
/-- **The `hermiteInner` step identity** in `RatFunc ℚ`: with `am = algebraMap ℚ[X] (RatFunc ℚ)`, if
`B·(U·V') + C·V = −A·(1/(j+1))` (the Bézout relation `cdiophantine` solves at counter `j+1`), then
writing the next numerator `A' = −(j+1)·C − U·B'`, `am A/(am U·am V^(j+2)) = (am B/am V^(j+1))′ +
am A'/(am U·am V^(j+1))` — the global fraction's `V`-power drops by one, emitting the rational summand
`B/V^(j+1)`. The `U`-factor analog of `hermite_reduction_step`; a pure `RatFunc ℚ` calculation. -/
theorem hermiteInner_step_ratFunc (A B C U V : ℚ[X]) (hU : U ≠ 0) (hV : V ≠ 0) (j : ℕ)
    (hrel : B * (U * derivative V) + C * V = -A * Polynomial.C (((j : ℚ) + 1)⁻¹)) :
    algebraMap ℚ[X] (RatFunc ℚ) A
        / (algebraMap ℚ[X] (RatFunc ℚ) U * algebraMap ℚ[X] (RatFunc ℚ) V ^ (j + 2))
      = (algebraMap ℚ[X] (RatFunc ℚ) B / algebraMap ℚ[X] (RatFunc ℚ) V ^ (j + 1))′
        + algebraMap ℚ[X] (RatFunc ℚ) (-(Polynomial.C ((j : ℚ) + 1)) * C - U * derivative B)
          / (algebraMap ℚ[X] (RatFunc ℚ) U * algebraMap ℚ[X] (RatFunc ℚ) V ^ (j + 1)) := by
  have hinj := RatFunc.algebraMap_injective (K := ℚ)
  set am := algebraMap ℚ[X] (RatFunc ℚ) with hamdef
  have hu : am U ≠ 0 := (map_ne_zero_iff _ hinj).mpr hU
  have hv : am V ≠ 0 := (map_ne_zero_iff _ hinj).mpr hV
  have hvp : am V ^ (j + 1) ≠ 0 := pow_ne_zero _ hv
  have hn1 : ((j : ℚ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero j
  -- constant casts: `am (C k) = algebraMap ℚ (RatFunc ℚ) k`, and `(j+1)·(j+1)⁻¹ = 1`.
  have e1 : ∀ k : ℚ, am (Polynomial.C k) = algebraMap ℚ (RatFunc ℚ) k := fun k => by
    rw [hamdef, ← Polynomial.algebraMap_eq]
    exact (IsScalarTower.algebraMap_apply ℚ ℚ[X] (RatFunc ℚ) k).symm
  have hc1 : am (Polynomial.C ((j : ℚ) + 1)) = (j : RatFunc ℚ) + 1 := by
    rw [e1, map_add, map_natCast, map_one]
  have hκ : ((j : RatFunc ℚ) + 1) * am (Polynomial.C (((j : ℚ) + 1)⁻¹)) = 1 := by
    rw [e1, ← hc1, e1, ← map_mul, mul_inv_cancel₀ hn1, map_one]
  -- `am`-of-derivative rewrites (defeq to `ratFuncDeriv_algebraMap`).
  have hdB : (am B)′ = am (derivative B) := ratFuncDeriv_algebraMap B
  have hdV : (am V)′ = am (derivative V) := ratFuncDeriv_algebraMap V
  -- map the polynomial Bézout relation into `RatFunc ℚ`, then clear the `(j+1)⁻¹` constant.
  have hbez : am B * (am U * am (derivative V)) + am C * am V
      = -am A * am (Polynomial.C (((j : ℚ) + 1)⁻¹)) := by
    have h := congrArg am hrel
    rw [map_add, map_mul, map_mul, map_mul, map_mul, map_neg] at h
    exact h
  -- multiply through by `(j+1)`: the inverse constant cancels via `hκ`, leaving an inverse-free relation.
  have hbez2 : ((j : RatFunc ℚ) + 1) * (am B * (am U * am (derivative V)) + am C * am V) = -am A := by
    rw [hbez]; linear_combination (-am A) * hκ
  -- expand the derivative term `(am B / am V^(j+1))′`.
  have hderiv : (am B / am V ^ (j + 1))′
      = (am V ^ (j + 1) * am (derivative B)
          - am B * ((j + 1 : RatFunc ℚ) * am V ^ j * am (derivative V))) / (am V ^ (j + 1)) ^ 2 := by
    rw [deriv_div, hdB, deriv_pow, hdV, Nat.add_sub_cancel]
    push_cast; ring_nf
  rw [hderiv, map_sub, map_mul, map_mul, map_neg, hc1]
  -- eliminate `am A` using the inverse-free Bézout relation, then it is a pure field identity.
  have hA : am A = -((j : RatFunc ℚ) + 1) * (am B * (am U * am (derivative V)) + am C * am V) := by
    linear_combination hbez2
  rw [hA, pow_succ]
  field_simp
  ring

/-! ### The `hermiteInner` loop power `Vpow = V^(j+1)` -/

/-- The repeated-multiplication fold `foldl (·* V) init` over `range n` realizes `init · V^n` under
`toPoly`. -/
theorem toPoly_foldl_cmul (V : CPoly) (n : ℕ) (init : CPoly) :
    toPoly ((List.range n).foldl (fun acc _ => cmul acc V) init)
      = toPoly init * toPoly V ^ n := by
  induction n generalizing init with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_concat, toPoly_cmul, ih, pow_succ]
    ring

/-- The `hermiteInner` per-step power `Vpow = V^(j+1)` (the fold over `range (j+1)` from `[1]`). -/
theorem toPoly_hermiteInner_Vpow (V : CPoly) (j : ℕ) :
    toPoly ((List.range (j + 1)).foldl (fun acc _ => cmul acc V) [1])
      = toPoly V ^ (j + 1) := by
  rw [toPoly_foldl_cmul]; simp [toPoly_cons]

/-! ### The `hermiteInner` loop correctness (in `RatFunc ℚ`)

The inner loop `hermiteInner fuel V U j A qzero` peels `B/Vⱼ` pieces, lowering the global fraction
`A/(U·V^(j+1))` to `A_final/(U·V)`. The correctness identity is the `j`-fold gluing of
`hermiteInner_step_ratFunc`. The per-step Bézout relation is supplied as a hypothesis `hbez` (the
computable `cdiophantine` discharges it via `toPoly_cdiophantine`; see `hermiteInner_bezout_of`). -/

/-- The `hermiteInner` per-step quantities, named for the invariant proof: at counter `j+1` with
numerator `A`, `cdiophantine` returns `(B, C)`, the next numerator is `A' = −(j+1)·C − U·B'`, the
emitted piece is `B/V^(j+1)`, and the recursion continues at counter `j`. -/
private def hbezPred (fuel : ℕ) (V U : CPoly) (j' : ℕ) (A' : CPoly) : Prop :=
  toPoly (cdiophantine fuel (cmul U (cderiv V)) V (cscale (-((j' : ℚ) + 1)⁻¹) A')).1
      * (toPoly U * derivative (toPoly V))
    + toPoly (cdiophantine fuel (cmul U (cderiv V)) V (cscale (-((j' : ℚ) + 1)⁻¹) A')).2
      * toPoly V
    = -toPoly A' * Polynomial.C (((j' : ℚ) + 1)⁻¹)

open scoped Differential in
/-- **`hermiteInner` loop invariant** (accumulator-general form) in `RatFunc ℚ`: with `am =
algebraMap ℚ[X] (RatFunc ℚ)`, for `U, V ≠ 0`, if every reachable Bézout step satisfies its defining
relation (`hbez`), then for any accumulator `g` with nonzero denominator,
`am A/(am U·am V^(j+1)) + (toQFun g)′ = (toQFun (hermiteInner fuel V U j A g).1)′ +
am A_final/(am U·am V)`. So the *new* rational pieces the loop adds to `g` integrate exactly the
power-drop from `V^(j+1)` to `V`. Induction on the counter `j`, each step the
`hermiteInner_step_ratFunc` identity glued to the tail (with `toQFun_qadd` realizing `qadd`). -/
theorem hermiteInner_spec_acc (fuel : ℕ) (V U : CPoly) (hU : toPoly U ≠ 0) (hV : toPoly V ≠ 0)
    (hbez : ∀ (j' : ℕ) (A' : CPoly), hbezPred fuel V U j' A') :
    ∀ (j : ℕ) (A : CPoly) (g : QFun), toPoly g.2 ≠ 0 →
      algebraMap ℚ[X] (RatFunc ℚ) (toPoly A)
          / (algebraMap ℚ[X] (RatFunc ℚ) (toPoly U)
              * algebraMap ℚ[X] (RatFunc ℚ) (toPoly V) ^ (j + 1))
        + (toQFun g)′
        = (toQFun (hermiteInner fuel V U j A g).1)′
          + algebraMap ℚ[X] (RatFunc ℚ) (toPoly (hermiteInner fuel V U j A g).2)
            / (algebraMap ℚ[X] (RatFunc ℚ) (toPoly U) * algebraMap ℚ[X] (RatFunc ℚ) (toPoly V)) := by
  set am := algebraMap ℚ[X] (RatFunc ℚ) with hamdef
  intro j
  induction j with
  | zero =>
    intro A g hg
    -- base case: `hermiteInner fuel V U 0 A g = (g, A)`, power `V^1 = V`.
    simp only [hermiteInner]
    rw [pow_one]; ring
  | succ j ih =>
    intro A g hg
    -- unfold one step (loop body at counter `j+1`, `jval = (j:ℚ)+1`); destructure `cdiophantine`.
    rw [hermiteInner]
    rcases hBC : cdiophantine fuel (cmul U (cderiv V)) V (cscale (-((j : ℚ) + 1)⁻¹) A)
      with ⟨B, C⟩
    simp only []
    set Vpow := (List.range (j + 1)).foldl (fun acc _ => cmul acc V) [1] with hVpowdef
    set A' := csub (cscale (-((j : ℚ) + 1)) C) (cmul U (cderiv B)) with hA'def
    -- the emitted summand `B/Vpow` is `B/V^(j+1)`.
    have hVpow : toPoly Vpow = toPoly V ^ (j + 1) := toPoly_hermiteInner_Vpow V j
    have hVpow0 : toPoly Vpow ≠ 0 := by rw [hVpow]; exact pow_ne_zero _ hV
    -- `qadd g (B, Vpow)` realizes `toQFun g + toQFun (B, Vpow)`.
    have hqadd : toQFun (qadd g (B, Vpow)) = toQFun g + toQFun (B, Vpow) :=
      toQFun_qadd g (B, Vpow) hg hVpow0
    -- the new accumulator denominator is nonzero.
    have hgnew : toPoly (qadd g (B, Vpow)).2 ≠ 0 := by
      show toPoly (cmul g.2 Vpow) ≠ 0
      rw [toPoly_cmul]; exact mul_ne_zero hg hVpow0
    have hcdB : toPoly (cderiv B) = derivative (toPoly B) := toPoly_cderiv B
    -- the Bézout relation at this step (`hbez` specialized to `(j, A)`, with `(B,C)` substituted).
    have hb : hbezPred fuel V U j A := hbez j A
    rw [hbezPred, hBC] at hb
    -- apply the step identity (`J = j`: input power `V^(j+2)`, emitted `B/V^(j+1)`).
    have hstep := hermiteInner_step_ratFunc (toPoly A) (toPoly B) (toPoly C) (toPoly U) (toPoly V)
      hU hV j ?_
    · -- recursion hypothesis at counter `j` with the new accumulator and numerator `A'`.
      have ihA := ih A' (qadd g (B, Vpow)) hgnew
      have hBVpow : toQFun (B, Vpow) = am (toPoly B) / am (toPoly V) ^ (j + 1) := by
        rw [toQFun, hVpow, map_pow]
      have hA'eq : toPoly A'
          = -(Polynomial.C ((j : ℚ) + 1)) * toPoly C - toPoly U * derivative (toPoly B) := by
        rw [hA'def, toPoly_csub, toPoly_cscale, toPoly_cmul, hcdB, map_neg]
      rw [hqadd, map_add, hBVpow, hA'eq] at ihA
      -- glue: power-drop step + recursive tail.
      rw [show (j + 1 + 1) = (j + 2) from rfl]
      linear_combination hstep + ihA
    · -- the step's Bézout premise is exactly `hb` (with `(B,C).1 = B`, `(B,C).2 = C`).
      exact hb

/-- `toQFun qzero = 0`: the zero rational function reads as `0` in `RatFunc ℚ`. -/
theorem toQFun_qzero : toQFun qzero = 0 := by
  simp [toQFun, qzero, toPoly_nil]

open scoped Differential in
/-- **`hermiteInner` loop correctness** (the public `qzero`-start form) in `RatFunc ℚ`: with `am =
algebraMap ℚ[X] (RatFunc ℚ)`, for `U, V ≠ 0`, if every reachable computable Bézout step satisfies its
defining relation (`hbez`, discharged by `toPoly_cdiophantine`), then `hermiteInner fuel V U j A qzero
= (gloc, A_final)` realizes `am A/(am U·am V^(j+1)) = (toQFun gloc)′ + am A_final/(am U·am V)`: the
emitted rational part `gloc` integrates the global fraction's power-drop from `V^(j+1)` to the
squarefree `V`. The computable analog of `hermiteReducePower_spec`. Specializes
`hermiteInner_spec_acc` at the empty accumulator (`toQFun_qzero`). -/
theorem hermiteInner_spec (fuel : ℕ) (V U : CPoly) (hU : toPoly U ≠ 0) (hV : toPoly V ≠ 0)
    (hbez : ∀ (j' : ℕ) (A' : CPoly), hbezPred fuel V U j' A') (j : ℕ) (A : CPoly) :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly A)
        / (algebraMap ℚ[X] (RatFunc ℚ) (toPoly U)
            * algebraMap ℚ[X] (RatFunc ℚ) (toPoly V) ^ (j + 1))
      = (toQFun (hermiteInner fuel V U j A qzero).1)′
        + algebraMap ℚ[X] (RatFunc ℚ) (toPoly (hermiteInner fuel V U j A qzero).2)
          / (algebraMap ℚ[X] (RatFunc ℚ) (toPoly U) * algebraMap ℚ[X] (RatFunc ℚ) (toPoly V)) := by
  have h := hermiteInner_spec_acc fuel V U hU hV hbez j A qzero (by simp [qzero, toPoly_cons])
  rw [toQFun_qzero, map_zero, add_zero] at h
  -- `(0)′ = 0`.
  simpa using h

/-- **The per-step Bézout relation `hbezPred` holds**, discharged from `toPoly_cdiophantine`: at every
counter `j'` and numerator `A'`, the computable `cdiophantine` step satisfies its defining relation,
provided `V ≠ 0` (`cnorm V ≠ []`), the gcd of `cmul U (cderiv V)` and `V` is a nonzero constant (the
coprimality the Hermite call sites guarantee), and there is enough fuel for the proper remainder. This
is the bridge that lets `hermiteInner_spec`'s abstract `hbez` premise be satisfied by the actual
computable engine. -/
theorem hermiteInner_bezout_of (fuel : ℕ) (V U : CPoly) (j' : ℕ) (A' : CPoly)
    (hq : cnorm V ≠ [])
    (hg : toPoly (cgcdExt fuel (cmul U (cderiv V)) V).1
      = Polynomial.C (clead (cgcdExt fuel (cmul U (cderiv V)) V).1))
    (hgc : clead (cgcdExt fuel (cmul U (cderiv V)) V).1 ≠ 0) :
    hbezPred fuel V U j' A' := by
  rw [hbezPred]
  have h := toPoly_cdiophantine fuel (cmul U (cderiv V)) V
    (cscale (-((j' : ℚ) + 1)⁻¹) A') hq hg hgc
  rw [toPoly_cmul, toPoly_cderiv, toPoly_cscale] at h
  rw [h]
  rw [show Polynomial.C (-((j' : ℚ) + 1)⁻¹) = -Polynomial.C (((j' : ℚ) + 1)⁻¹) from by rw [map_neg]]
  ring

open scoped Differential in
/-- **`hermiteInner` correctness from the computable engine** (the fully-discharged form): for `U, V`
with nonzero `toPoly`, `cnorm V ≠ []`, and the gcd of `cmul U (cderiv V)` and `V` a nonzero constant (the
coprimality `V ⊥ U·V'` that holds when `V` is squarefree and coprime to `U`), the computable inner loop
satisfies `am A/(am U·am V^(j+1)) = (toQFun gloc)′ + am A_final/(am U·am V)`. Combines `hermiteInner_spec`
with `hermiteInner_bezout_of` — this is the computable counterpart of `hermiteReducePower_spec`, with the
extra global `U`-denominator the `#eval`-able `hermiteInner` carries. -/
theorem hermiteInner_spec_of (fuel : ℕ) (V U : CPoly) (hU : toPoly U ≠ 0) (hV : toPoly V ≠ 0)
    (hq : cnorm V ≠ [])
    (hg : toPoly (cgcdExt fuel (cmul U (cderiv V)) V).1
      = Polynomial.C (clead (cgcdExt fuel (cmul U (cderiv V)) V).1))
    (hgc : clead (cgcdExt fuel (cmul U (cderiv V)) V).1 ≠ 0) (j : ℕ) (A : CPoly) :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly A)
        / (algebraMap ℚ[X] (RatFunc ℚ) (toPoly U)
            * algebraMap ℚ[X] (RatFunc ℚ) (toPoly V) ^ (j + 1))
      = (toQFun (hermiteInner fuel V U j A qzero).1)′
        + algebraMap ℚ[X] (RatFunc ℚ) (toPoly (hermiteInner fuel V U j A qzero).2)
          / (algebraMap ℚ[X] (RatFunc ℚ) (toPoly U) * algebraMap ℚ[X] (RatFunc ℚ) (toPoly V)) :=
  hermiteInner_spec fuel V U hU hV
    (fun j' A' => hermiteInner_bezout_of fuel V U j' A' hq hg hgc) j A

open scoped Differential in
-- The computable `hermiteInner` loop integrates the rational part of `A/(U·V^(j+1))` exactly,
-- leaving the squarefree-denominator residual `A_final/(U·V)` — the computable `hermiteReducePower_spec`.
example (fuel : ℕ) (V U : CPoly) (hU : toPoly U ≠ 0) (hV : toPoly V ≠ 0) (hq : cnorm V ≠ [])
    (hg : toPoly (cgcdExt fuel (cmul U (cderiv V)) V).1
      = Polynomial.C (clead (cgcdExt fuel (cmul U (cderiv V)) V).1))
    (hgc : clead (cgcdExt fuel (cmul U (cderiv V)) V).1 ≠ 0) (j : ℕ) (A : CPoly) :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly A)
        / (algebraMap ℚ[X] (RatFunc ℚ) (toPoly U)
            * algebraMap ℚ[X] (RatFunc ℚ) (toPoly V) ^ (j + 1))
      = (toQFun (hermiteInner fuel V U j A qzero).1)′
        + algebraMap ℚ[X] (RatFunc ℚ) (toPoly (hermiteInner fuel V U j A qzero).2)
          / (algebraMap ℚ[X] (RatFunc ℚ) (toPoly U) * algebraMap ℚ[X] (RatFunc ℚ) (toPoly V)) :=
  hermiteInner_spec_of fuel V U hU hV hq hg hgc j A

/-! ### Exact division through `toPoly`

When the computable Euclidean division `cdiv fuel p q` is *exact* (the remainder `cmod fuel p q`
reads to `0`), it realizes honest division in `ℚ[X]`: `toPoly p = toPoly (cdiv fuel p q) · toPoly q`.
This is the certificate the `hermiteReduce` residual recovery needs — `Bres = cdiv … (resNum·Dstar)
resDen` divides exactly because the difference `A/D − g′` is a genuine polynomial fraction over
`Dstar`. -/

/-- **Exact-division bridge**: if the remainder `cmod fuel p q` reads to `0` in `ℚ[X]`, then `cdiv`
realizes honest division: `toPoly p = toPoly (cdiv fuel p q) · toPoly q`. (From the Euclidean-division
identity `toPoly_cdivmod'` with a zero remainder; needs `cnorm q ≠ []`.) -/
theorem toPoly_cdiv_of_cmod_zero (fuel : ℕ) (p q : CPoly) (hq : cnorm q ≠ [])
    (hrem : toPoly (cmod fuel p q) = 0) :
    toPoly p = toPoly (cdiv fuel p q) * toPoly q := by
  have h := toPoly_cdivmod' fuel p q hq
  rw [show (cdivmod fuel p q).1 = cdiv fuel p q from rfl,
      show (cdivmod fuel p q).2 = cmod fuel p q from rfl, hrem, add_zero] at h
  exact h

/-- **Divisibility ⟹ exact remainder**: if `toPoly q ∣ toPoly p` in `ℚ[X]` (and `q ≠ 0`, enough
fuel), then the computable remainder reads to `0`: `toPoly (cmod fuel p q) = 0`. The remainder
`r = cmod fuel p q` satisfies `toPoly p = toPoly (cdiv …)·toPoly q + toPoly r` with `deg (toPoly r) <
deg (toPoly q)` (`cmod_length_lt` + the degree bridge); since `toPoly q ∣ toPoly p` it also divides
`toPoly r`, and a polynomial of degree `< deg q` divisible by `q` is `0`. Converts the exact-division
certificate from a `cmod`-computation into an honest `ℚ[X]` divisibility hypothesis. -/
theorem cmod_eq_zero_of_dvd (fuel : ℕ) (p q : CPoly) (hq : cnorm q ≠ [])
    (hfuel : (cnorm p).length ≤ fuel) (hdvd : toPoly q ∣ toPoly p) :
    toPoly (cmod fuel p q) = 0 := by
  have hq0 : toPoly q ≠ 0 := fun h => hq ((cnorm_eq_nil_iff q).mpr h)
  -- Euclidean identity: `toPoly p = toPoly (cdiv …)·toPoly q + toPoly (cmod …)`.
  have hdiv := toPoly_cdivmod' fuel p q hq
  rw [show (cdivmod fuel p q).1 = cdiv fuel p q from rfl,
      show (cdivmod fuel p q).2 = cmod fuel p q from rfl] at hdiv
  -- `toPoly q ∣ toPoly (cmod …)`: it divides `p` and `(cdiv …)·q`, hence the difference.
  have hqr : toPoly q ∣ toPoly (cmod fuel p q) := by
    have hd2 : toPoly q ∣ toPoly (cdiv fuel p q) * toPoly q := Dvd.intro_left _ rfl
    have : toPoly (cmod fuel p q) = toPoly p - toPoly (cdiv fuel p q) * toPoly q := by
      rw [hdiv]; ring
    rw [this]; exact dvd_sub hdvd hd2
  -- degree of the remainder is below `deg q`.
  have hlen : (cnorm (cmod fuel p q)).length < (cnorm q).length := cmod_length_lt fuel p q hq hfuel
  by_contra hne
  have hrne : toPoly (cmod fuel p q) ≠ 0 := hne
  have hdeg : (toPoly q).degree ≤ (toPoly (cmod fuel p q)).degree :=
    Polynomial.degree_le_of_dvd hqr hrne
  -- but the length bound gives the strict reverse inequality.
  have e1 : (cnorm (cmod fuel p q)).length = (toPoly (cmod fuel p q)).natDegree + 1 :=
    length_cnorm_of_ne _ (fun h => hrne ((cnorm_eq_nil_iff _).mp h))
  have e2 : (cnorm q).length = (toPoly q).natDegree + 1 := length_cnorm_of_ne q hq
  have hndlt : (toPoly (cmod fuel p q)).natDegree < (toPoly q).natDegree := by omega
  rw [Polynomial.degree_eq_natDegree hrne, Polynomial.degree_eq_natDegree hq0, Nat.cast_le] at hdeg
  omega

open Classical in
/-- **Exact-division cross-multiplication in `RatFunc ℚ`**: when `cdiv fuel p q` is exact
(`toPoly (cmod fuel p q) = 0`) and `q ≠ 0`, the fraction `am p / am q` equals `am (cdiv fuel p q)`
as a `RatFunc ℚ` element. -/
theorem am_cdiv_of_cmod_zero (fuel : ℕ) (p q : CPoly) (hq : cnorm q ≠ [])
    (hrem : toPoly (cmod fuel p q) = 0) :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly p) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly q)
      = algebraMap ℚ[X] (RatFunc ℚ) (toPoly (cdiv fuel p q)) := by
  have hq0 : toPoly q ≠ 0 := fun h => hq ((cnorm_eq_nil_iff q).mpr h)
  have hqm : algebraMap ℚ[X] (RatFunc ℚ) (toPoly q) ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective ℚ)).mpr hq0
  rw [toPoly_cdiv_of_cmod_zero fuel p q hq hrem, map_mul, mul_div_assoc,
    div_self hqm, mul_one]

/-! ### The residual-recovery identity (in `RatFunc ℚ`)

`hermiteReduce` computes the residual log-part numerator `Bres` by clearing denominators in
`A/D − g′ = Bres/Dstar`: with `g = gnum/gden`, the quotient rule gives `A/D − g′ = resNum/resDen`
where `resNum = A·gden² − D·(gnum'·gden − gnum·gden')` and `resDen = D·gden²`. The lemma below is the
pure `RatFunc ℚ` calculation of that subtraction; `am_cdiv_of_cmod_zero` then folds the exact division
`Bres = (resNum·Dstar)/resDen` into the squarefree-denominator form `Bres/Dstar`. -/

open scoped Differential in
/-- **The residual-recovery numerator identity** in `RatFunc ℚ`: with `am = algebraMap ℚ[X]
(RatFunc ℚ)`, for `D, gden ≠ 0`, the difference of `A/D` and the derivative of the rational part
`gnum/gden` is `resNum/(D·gden²)` where `resNum = A·gden² − D·(gnum'·gden − gnum·gden')`. The
quotient-rule numerator of `(gnum/gden)′` cleared over the common denominator `D·gden²`. -/
theorem residual_numerator_ratFunc (A D gnum gden : ℚ[X]) (hD : D ≠ 0) (hgden : gden ≠ 0) :
    algebraMap ℚ[X] (RatFunc ℚ) A / algebraMap ℚ[X] (RatFunc ℚ) D
        - (algebraMap ℚ[X] (RatFunc ℚ) gnum / algebraMap ℚ[X] (RatFunc ℚ) gden)′
      = algebraMap ℚ[X] (RatFunc ℚ)
          (A * (gden * gden) - D * (derivative gnum * gden - gnum * derivative gden))
        / (algebraMap ℚ[X] (RatFunc ℚ) D * (algebraMap ℚ[X] (RatFunc ℚ) gden
            * algebraMap ℚ[X] (RatFunc ℚ) gden)) := by
  have hinj := RatFunc.algebraMap_injective (K := ℚ)
  set am := algebraMap ℚ[X] (RatFunc ℚ) with hamdef
  have hd : am D ≠ 0 := (map_ne_zero_iff _ hinj).mpr hD
  have hgd : am gden ≠ 0 := (map_ne_zero_iff _ hinj).mpr hgden
  -- `am`-of-derivative rewrites (defeq to `ratFuncDeriv_algebraMap`).
  have hdgnum : (am gnum)′ = am (derivative gnum) := ratFuncDeriv_algebraMap gnum
  have hdgden : (am gden)′ = am (derivative gden) := ratFuncDeriv_algebraMap gden
  -- the quotient rule for `(gnum/gden)′`.
  have hderiv : (am gnum / am gden)′
      = (am gden * am (derivative gnum) - am gnum * am (derivative gden)) / (am gden ^ 2) := by
    rw [deriv_div, hdgnum, hdgden]
  rw [hderiv]
  simp only [map_sub, map_mul]
  rw [pow_two]
  field_simp

/-! ### The full `hermiteReduce` wrapper correctness (in `RatFunc ℚ`)

The previous pieces combine into the public correctness theorem for the computable wrapper
`hermiteReduce`. Its residual numerator `Bres = cdiv … (resNum·Dstar) resDen` is computed by exact
division, so as a `RatFunc ℚ` element it equals `resNum·Dstar / resDen`. Folding that through
`residual_numerator_ratFunc` (the quotient-rule identity `A/D − g′ = resNum/resDen`) and cancelling
`Dstar` against `resDen = D·gden²` (using `Dstar ∣ D`, witnessed by the exact-division certificate)
gives `am A/am D = (toQFun g)′ + am Bres/am Dstar`. The single hypothesis is the exact-division
certificate — exactly the polynomial **cleared identity** `resNum·Dstar = Bres·resDen` that
`hermite_ex221_cleared_identity` validates by `native_decide`. -/

open scoped Differential in
/-- **Full `hermiteReduce` wrapper correctness** in `RatFunc ℚ`: writing
`hermiteReduce fuel A D = ((gnum, gden), (Bres, Dstar))` with `am = algebraMap ℚ[X] (RatFunc ℚ)`,
under the *exact-division certificate* — the residual numerator `Bres = cdiv fuel (resNum·Dstar)
resDen` divides exactly (`toPoly (cmod fuel (resNum·Dstar) resDen) = 0`), where
`resNum = A·gden² − D·(gnum'·gden − gnum·gden')` and `resDen = D·gden²` — and with `D, gden ≠ 0`,
`Dstar ≠ 0`, the computed reduction satisfies `am A/am D = (toQFun (gnum,gden))′ + am Bres/am Dstar`.
I.e. `∫ A/D = gnum/gden + ∫ Bres/Dstar`: the rational part is `gnum/gden` and the residual integrand
is `Bres/Dstar`. The certificate is precisely the polynomial cleared identity
`resNum·Dstar = Bres·resDen`. Combines `residual_numerator_ratFunc` (the quotient-rule numerator) with
`am_cdiv_of_cmod_zero` (the exact division), cancelling `Dstar` in `am Bres/am Dstar`. -/
theorem hermiteReduce_residual_correct (fuel : ℕ) (A D : CPoly)
    (gnum gden Dstar : CPoly)
    (hD : toPoly D ≠ 0) (hgden : toPoly gden ≠ 0)
    (hDstar : cnorm Dstar ≠ [])
    (hexact : toPoly (cmod fuel
        (cmul (csub (cmul A (cmul gden gden))
            (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))) Dstar)
        (cmul D (cmul gden gden))) = 0) :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
      = (toQFun (gnum, gden))′
        + algebraMap ℚ[X] (RatFunc ℚ)
            (toPoly (cdiv fuel
              (cmul (csub (cmul A (cmul gden gden))
                  (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))) Dstar)
              (cmul D (cmul gden gden))))
          / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Dstar) := by
  have hinj := RatFunc.algebraMap_injective (K := ℚ)
  set am := algebraMap ℚ[X] (RatFunc ℚ) with hamdef
  -- abbreviations matching `hermiteReduce`'s `let`-bindings.
  set resNum := cmul (csub (cmul A (cmul gden gden))
      (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))) Dstar with hresNum
  set resDen := cmul D (cmul gden gden) with hresDen
  have hDstar0 : toPoly Dstar ≠ 0 := fun h => hDstar ((cnorm_eq_nil_iff Dstar).mpr h)
  have hresDenPoly0 : toPoly resDen ≠ 0 := by
    rw [hresDen, toPoly_cmul, toPoly_cmul]
    exact mul_ne_zero hD (mul_ne_zero hgden hgden)
  have hresDen0 : cnorm resDen ≠ [] := fun h => hresDenPoly0 ((cnorm_eq_nil_iff resDen).mp h)
  have hdstar : am (toPoly Dstar) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hDstar0
  -- `toQFun (gnum, gden) = am (toPoly gnum) / am (toPoly gden)`.
  have htoQ : toQFun (gnum, gden) = am (toPoly gnum) / am (toPoly gden) := rfl
  -- the residual numerator identity.
  have hresid := residual_numerator_ratFunc (toPoly A) (toPoly D) (toPoly gnum) (toPoly gden) hD hgden
  -- the exact division `am (resNum) / am (resDen) = am (cdiv … resNum resDen)`.
  have hcdiv := am_cdiv_of_cmod_zero fuel resNum resDen hresDen0 hexact
  -- compute `toPoly resNum` and `toPoly resDen` through the homomorphism.
  have hresNumPoly : toPoly resNum
      = (toPoly A * (toPoly gden * toPoly gden)
          - toPoly D * (derivative (toPoly gnum) * toPoly gden
              - toPoly gnum * derivative (toPoly gden))) * toPoly Dstar := by
    rw [hresNum, toPoly_cmul, toPoly_csub, toPoly_cmul, toPoly_cmul, toPoly_cmul, toPoly_csub,
      toPoly_cmul, toPoly_cmul, toPoly_cderiv, toPoly_cderiv]
  have hresDenPoly : toPoly resDen = toPoly D * (toPoly gden * toPoly gden) := by
    rw [hresDen, toPoly_cmul, toPoly_cmul]
  -- `am Bres / am Dstar = resNum'/(am D·(am gden·am gden))`: cancel `Dstar` against the exact division.
  have hd : am (toPoly D) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hD
  have hgd : am (toPoly gden) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hgden
  have hkey : am (toPoly (cdiv fuel resNum resDen)) / am (toPoly Dstar)
      = am (toPoly A * (toPoly gden * toPoly gden)
            - toPoly D * (derivative (toPoly gnum) * toPoly gden - toPoly gnum * derivative (toPoly gden)))
          / (am (toPoly D) * (am (toPoly gden) * am (toPoly gden))) := by
    rw [← hcdiv, hresNumPoly, hresDenPoly, map_mul, map_mul, map_mul, div_div,
      mul_comm (am (toPoly D) * (am (toPoly gden) * am (toPoly gden))) (am (toPoly Dstar)),
      mul_comm (am _) (am (toPoly Dstar)), mul_div_mul_left _ _ hdstar]
  -- assemble: `A/D = g′ + Bres/Dstar` from the residual identity `A/D − g′ = resNum'/(...)`.
  rw [htoQ, hkey]
  linear_combination hresid

/-- `toQFun` is invariant under `cnorm` of both components (`toPoly_cnorm`). -/
theorem toQFun_cnorm (gnum gden : CPoly) :
    toQFun (cnorm gnum, cnorm gden) = toQFun (gnum, gden) := by
  simp only [toQFun, toPoly_cnorm]

open scoped Differential in
/-- **`hermiteReduce` wrapper correctness, residual form** in `RatFunc ℚ`, stated with the residual
`Bres` taken as the `cnorm`-wrapped exact division (the algorithm's output shape): under the
exact-division certificate `hexact` and `D, gden ≠ 0`, `Dstar ≠ 0`, the rational part `gnum/gden`
together with `Bres/Dstar` gives `am A/am D = (toQFun (gnum,gden))′ + am Bres/am Dstar`. A direct
`cnorm`-fold of `hermiteReduce_residual_correct` — the form matching how `hermiteReduce` returns its
residual numerator `Bres = cnorm (cdiv … (resNum·Dstar) (D·gden²))`. -/
theorem hermiteReduce_spec_cnorm (fuel : ℕ) (A D gnum gden Dstar : CPoly)
    (hD : toPoly D ≠ 0) (hgden : toPoly gden ≠ 0) (hDstar : cnorm Dstar ≠ [])
    (hexact : toPoly (cmod fuel
        (cmul (csub (cmul A (cmul gden gden))
            (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))) Dstar)
        (cmul D (cmul gden gden))) = 0) :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
      = (toQFun (gnum, gden))′
        + algebraMap ℚ[X] (RatFunc ℚ)
            (toPoly (cnorm (cdiv fuel
              (cmul (csub (cmul A (cmul gden gden))
                  (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))) Dstar)
              (cmul D (cmul gden gden)))))
          / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Dstar) := by
  rw [toPoly_cnorm]
  exact hermiteReduce_residual_correct fuel A D gnum gden Dstar hD hgden hDstar hexact

open scoped Differential in
/-- **`hermiteReduce` wrapper correctness from an algebraic divisibility certificate** in `RatFunc ℚ`:
the exact-division premise as an honest `ℚ[X]` *divisibility* `toPoly (D·gden²) ∣ toPoly (resNum·Dstar)`
(plus a fuel bound), rather than a `cmod`-computation. Under `D, gden ≠ 0`, `Dstar ≠ 0`, and the
divisibility certificate, `am A/am D = (toQFun (gnum,gden))′ + am Bres/am Dstar`. The divisibility is
the genuine mathematical content: it holds because `A/D − g′` is a polynomial fraction over `Dstar`
(equivalently `Dstar ∣ D` and the numerator clears). Discharges the `cmod` certificate via
`cmod_eq_zero_of_dvd`. -/
theorem hermiteReduce_residual_correct_of_dvd (fuel : ℕ) (A D gnum gden Dstar : CPoly)
    (hD : toPoly D ≠ 0) (hgden : toPoly gden ≠ 0) (hDstar : cnorm Dstar ≠ [])
    (hfuel : (cnorm (cmul (csub (cmul A (cmul gden gden))
        (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))) Dstar)).length ≤ fuel)
    (hdvd : toPoly (cmul D (cmul gden gden))
      ∣ toPoly (cmul (csub (cmul A (cmul gden gden))
          (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))) Dstar)) :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
      = (toQFun (gnum, gden))′
        + algebraMap ℚ[X] (RatFunc ℚ)
            (toPoly (cdiv fuel
              (cmul (csub (cmul A (cmul gden gden))
                  (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))) Dstar)
              (cmul D (cmul gden gden))))
          / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Dstar) := by
  have hresDenP : toPoly (cmul D (cmul gden gden)) ≠ 0 := by
    rw [toPoly_cmul, toPoly_cmul]
    exact mul_ne_zero hD (mul_ne_zero hgden hgden)
  have hresDen : cnorm (cmul D (cmul gden gden)) ≠ [] :=
    fun h => hresDenP ((cnorm_eq_nil_iff _).mp h)
  exact hermiteReduce_residual_correct fuel A D gnum gden Dstar hD hgden hDstar
    (cmod_eq_zero_of_dvd fuel _ _ hresDen hfuel hdvd)

/-! ### Example 2.2.1: the certificate is real

The exact-division certificate `hexact` is not vacuous: on Example 2.2.1 the residual `cdiv`
divides exactly (`hermite_ex221_exact_division`, `native_decide`). Feeding it to
`hermiteReduce_residual_correct` gives the *rational-function* correctness identity
`am A/am D = (toQFun g)′ + am Bres/am Dstar` for the concrete computed reduction — upgrading the
`native_decide` polynomial cleared identity to an honest `RatFunc ℚ` equality. -/

/-- **Example 2.2.1: the residual division is exact** — the remainder of `(resNum·Dstar)` by
`(D·gden²)` reads to `0` (`cnorm … = []`), so `Bres = cdiv …` is honest `ℚ[X]` division. The
computed rational part is `gnum = [8,12,20,12,8,3]`, `gden = [0,8,0,12,0,6,0,1]`, and the squarefree
radical `Dstar = [0,2,0,1] = x³+2x`. Proved by `native_decide`. -/
theorem hermite_ex221_exact_division :
    cnorm (cmod 40
      (cmul (csub (cmul cA221 (cmul [0, 8, 0, 12, 0, 6, 0, 1] [0, 8, 0, 12, 0, 6, 0, 1]))
          (cmul cD221 (csub (cmul (cderiv [8, 12, 20, 12, 8, 3]) [0, 8, 0, 12, 0, 6, 0, 1])
            (cmul [8, 12, 20, 12, 8, 3] (cderiv [0, 8, 0, 12, 0, 6, 0, 1]))))) [0, 2, 0, 1])
      (cmul cD221 (cmul [0, 8, 0, 12, 0, 6, 0, 1] [0, 8, 0, 12, 0, 6, 0, 1]))) = [] := by
  native_decide

open scoped Differential in
/-- **Example 2.2.1: the Hermite reduction is correct as a `RatFunc ℚ` identity** (§2.2, p.41):
`am A/am D = (toQFun (gnum,gden))′ + am Bres/am Dstar` for the concrete computed `gnum, gden, Dstar`
of Example 2.2.1, with `Bres = cdiv … (resNum·Dstar) (D·gden²)`. Honest `ℚ(x)` equality (not just the
cleared polynomial certificate), obtained from `hermiteReduce_residual_correct` with the exact-division
certificate discharged by `hermite_ex221_exact_division`. The nonzero hypotheses (`D, gden, Dstar`)
hold since their `toPoly`/`cnorm` are nonzero (checked by `native_decide`/`decide`). -/
example :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly cA221) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly cD221)
      = (toQFun ([8, 12, 20, 12, 8, 3], [0, 8, 0, 12, 0, 6, 0, 1]))′
        + algebraMap ℚ[X] (RatFunc ℚ)
            (toPoly (cdiv 40
              (cmul (csub (cmul cA221 (cmul [0, 8, 0, 12, 0, 6, 0, 1] [0, 8, 0, 12, 0, 6, 0, 1]))
                  (cmul cD221 (csub (cmul (cderiv [8, 12, 20, 12, 8, 3]) [0, 8, 0, 12, 0, 6, 0, 1])
                    (cmul [8, 12, 20, 12, 8, 3] (cderiv [0, 8, 0, 12, 0, 6, 0, 1]))))) [0, 2, 0, 1])
              (cmul cD221 (cmul [0, 8, 0, 12, 0, 6, 0, 1] [0, 8, 0, 12, 0, 6, 0, 1]))))
          / algebraMap ℚ[X] (RatFunc ℚ) (toPoly [0, 2, 0, 1]) := by
  have hD : toPoly cD221 ≠ 0 := fun h => by
    have : cnorm cD221 = [] := (cnorm_eq_nil_iff cD221).mpr h
    revert this; decide
  have hgden : toPoly [0, 8, 0, 12, 0, 6, 0, 1] ≠ 0 := fun h => by
    have : cnorm [0, 8, 0, 12, 0, 6, 0, 1] = [] := (cnorm_eq_nil_iff _).mpr h
    revert this; decide
  have hDstar : cnorm [0, 2, 0, 1] ≠ [] := by decide
  have hexact : toPoly (cmod 40
      (cmul (csub (cmul cA221 (cmul [0, 8, 0, 12, 0, 6, 0, 1] [0, 8, 0, 12, 0, 6, 0, 1]))
          (cmul cD221 (csub (cmul (cderiv [8, 12, 20, 12, 8, 3]) [0, 8, 0, 12, 0, 6, 0, 1])
            (cmul [8, 12, 20, 12, 8, 3] (cderiv [0, 8, 0, 12, 0, 6, 0, 1]))))) [0, 2, 0, 1])
      (cmul cD221 (cmul [0, 8, 0, 12, 0, 6, 0, 1] [0, 8, 0, 12, 0, 6, 0, 1]))) = 0 := by
    rw [← cnorm_eq_nil_iff, hermite_ex221_exact_division]
  exact hermiteReduce_residual_correct 40 cA221 cD221 [8, 12, 20, 12, 8, 3]
    [0, 8, 0, 12, 0, 6, 0, 1] [0, 2, 0, 1] hD hgden hDstar hexact
