import DeepWiki.SymbolicIntegration.ComputeCorrectness
import DeepWiki.SymbolicIntegration.RationalFunctionDerivative
import DeepWiki.SymbolicIntegration.SquarefreeFactorization

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

/-- `qadd x y` has nonzero denominator when both `x, y` do (`den = x.2 · y.2`). -/
theorem toPoly_qadd_den_ne_zero {x y : QFun} (hx : toPoly x.2 ≠ 0) (hy : toPoly y.2 ≠ 0) :
    toPoly (qadd x y).2 ≠ 0 := by
  obtain ⟨a, b⟩ := x; obtain ⟨c, d⟩ := y
  show toPoly (cmul b d) ≠ 0
  rw [toPoly_cmul]; exact mul_ne_zero hx hy

/-- **The `qadd`-fold realizes the rational-function sum**: for a list of `QFun` increments each with
nonzero denominator and an initial accumulator with nonzero denominator,
`toQFun (gs.foldl qadd init) = toQFun init + (gs.map toQFun).sum`. So the Hermite `g`-fold, whatever its
increments, reads in `RatFunc ℚ` as the plain sum of the increments (plus the seed) — the structural
fact underlying the multi-factor `hermiteReduce` `g`-accumulation. -/
theorem toQFun_foldl_qadd (gs : List QFun) (init : QFun) (hinit : toPoly init.2 ≠ 0)
    (hgs : ∀ g ∈ gs, toPoly g.2 ≠ 0) :
    toQFun (gs.foldl qadd init) = toQFun init + (gs.map toQFun).sum := by
  induction gs generalizing init with
  | nil => simp
  | cons hd tl ih =>
    have hhd : toPoly hd.2 ≠ 0 := hgs hd (List.mem_cons_self ..)
    have htl : ∀ g ∈ tl, toPoly g.2 ≠ 0 := fun g hg => hgs g (List.mem_cons_of_mem hd hg)
    have hnew : toPoly (qadd init hd).2 ≠ 0 := toPoly_qadd_den_ne_zero hinit hhd
    rw [List.foldl_cons, ih (qadd init hd) hnew htl, toQFun_qadd init hd hinit hhd,
      List.map_cons, List.sum_cons]
    ring

open scoped Differential in
/-- **The `qadd`-fold derivative is the sum of the increment derivatives**: starting from `qzero`,
`(toQFun (gs.foldl qadd qzero))′ = ∑ⱼ (toQFun gⱼ)′` in `RatFunc ℚ`. The derivative of the Hermite
`g`-accumulation distributes over the per-factor increments (the derivation is additive on the
`toQFun_foldl_qadd` sum). The structural bridge from the fold to a sum of per-factor reductions. -/
theorem deriv_toQFun_foldl_qadd (gs : List QFun) (hgs : ∀ g ∈ gs, toPoly g.2 ≠ 0) :
    (toQFun (gs.foldl qadd qzero))′ = (gs.map (fun g => (toQFun g)′)).sum := by
  rw [toQFun_foldl_qadd gs qzero (by simp [qzero, toPoly_cons]) hgs, toQFun_qzero, zero_add]
  rw [show ((gs.map toQFun).sum)′ = Differential.deriv (R := RatFunc ℚ) (gs.map toQFun).sum from rfl,
    map_list_sum (Differential.deriv (R := RatFunc ℚ)) (gs.map toQFun), List.map_map]
  rfl

/-- **Sum of constant-minus-term** in any additive comm group: `∑ⱼ (T − residⱼ) = n·T − ∑ⱼ residⱼ`,
where `n = gs.length` (the `ℕ`-scalar multiple). -/
theorem sum_map_const_sub {α G : Type*} [AddCommGroup G] (gs : List α) (T : G) (resid : α → G) :
    (gs.map (fun g => T - resid g)).sum = gs.length • T - (gs.map resid).sum := by
  induction gs with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih, succ_nsmul]
    abel

open scoped Differential in
/-- **The global-`A` fold residual as an explicit `(1−n)·T + ∑ residᵢ` sum** in `RatFunc ℚ`: if the
fold increments `gs` each reduce the *same* global target `T` with `(toQFun gⱼ)′ = T − residⱼ` (the
shape `hermiteInner_spec` gives, `T = A/D`, `residⱼ = Afinalⱼ/(Uⱼ·Vⱼ)`), then the fold residual is
`T − (toQFun (gs.foldl qadd qzero))′ = (1 − gs.length)·T + ∑ⱼ residⱼ`. This is the *exact* algebraic
content of the global-`A` `g`-fold: each increment reduces the whole `T`, so `n` of them overcount `T`
by `(n−1)` copies — which the `∑ residⱼ` interference must clear back to a single squarefree-denominator
residual. The honest skeleton over which the multi-factor interference-clearing is stated. -/
theorem foldl_residual_eq (gs : List QFun) (hgs : ∀ g ∈ gs, toPoly g.2 ≠ 0)
    (T : RatFunc ℚ) (resid : QFun → RatFunc ℚ)
    (hstep : ∀ g ∈ gs, (toQFun g)′ = T - resid g) :
    T - (toQFun (gs.foldl qadd qzero))′
      = T - gs.length • T + (gs.map resid).sum := by
  rw [deriv_toQFun_foldl_qadd gs hgs, List.map_congr_left hstep, sum_map_const_sub]
  abel

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

/-! ### The Yun radical `Dstar` divides `D` through `toPoly`

`hermiteReduce`'s squarefree radical `Dstar = ∏ⱼ Vⱼ` is the product of the Yun factors `csqfreeFactor
fuel D = [(V₁,i₁),…]`. The honest content of the Yun decomposition is that this radical divides `D` in
`ℚ[X]`: `toPoly Dstar ∣ toPoly D`. Each Yun factor `Vⱼ = monic(gcd(bⱼ, dⱼ))` divides its working
numerator `bⱼ` (gcd divides), and the working numerators chain by *exact* division `bⱼ₊₁ = bⱼ/Vⱼ`
(`b₁ = D/gcd(D,D')`), so `∏ⱼ Vⱼ ∣ b₁ ∣ D`. The exact-division steps are the engine-honesty content,
bundled as `SqfreeExact`; `step_exact` reduces each to gcd-termination plus a fuel bound. -/

/-- `cmonic q` divides `q` through `toPoly`: `toPoly (cmonic q) ∣ toPoly q`. (`cmonic q = (clead q)⁻¹·q`
is an associate of `q`, hence divides it; the zero case is `0 ∣ 0`.) -/
theorem toPoly_cmonic_dvd (q : CPoly) : toPoly (cmonic q) ∣ toPoly q := by
  unfold cmonic
  by_cases h : cisZero (cnorm q)
  · simp only [h, if_true]
    have hq0 : toPoly q = 0 := by
      have : cnorm q = [] := by simpa [cisZero] using h
      rw [← toPoly_cnorm, this, toPoly_nil]
    simp [hq0]
  · simp only [h, Bool.false_eq_true, if_false]
    rw [toPoly_cscale, toPoly_cnorm]
    have hc : clead (cnorm q) ≠ 0 := clead_ne_zero (by simpa [cisZero] using h)
    refine ⟨Polynomial.C (clead (cnorm q)), ?_⟩
    rw [mul_comm (Polynomial.C (clead (cnorm q))⁻¹) (toPoly q), mul_assoc, ← map_mul,
      inv_mul_cancel₀ hc, map_one, mul_one]

/-- The product, through `toPoly`, of the first components of a Yun factor list `[(V₁,i₁),…]`:
`goProd l = ∏ⱼ toPoly Vⱼ`. The radical `Dstar` of `hermiteReduce` reads to this (`toPoly_Dstar_eq`). -/
noncomputable def goProd (l : List (CPoly × ℕ)) : ℚ[X] := (l.map (fun vi => toPoly vi.1)).prod

/-- **Per-step exactness predicate** for the Yun loop `csqfreeFactor.go`, mirroring its recursion on
the fuel counter `fo`: at each non-terminal step (numerator `b` non-constant) the factor `q =
monic(gcd b d)` divides `b` *exactly* — `toPoly b = toPoly q · toPoly (b/q)` — and the predicate
recurses on the deflated `(b', d')`. This is the engine-honesty content that makes the Yun radical an
honest divisor; `step_exact` discharges one step from gcd-termination plus a fuel bound. -/
def GoExact (fuel : ℕ) : ℕ → CPoly → CPoly → Prop
  | 0, _, _ => True
  | fo + 1, b, d =>
    if b.length ≤ 1 then True
    else
      let q := cmonic (cgcdExt fuel b d).1
      let b' := cdiv fuel b q
      let d' := csub (cdiv fuel d q) (cderiv b')
      toPoly b = toPoly q * toPoly b' ∧ GoExact fuel fo b' d'

/-- **The Yun loop's factor product divides its numerator**: under `GoExact`, the product of the
factors emitted by `csqfreeFactor.go fuel fo b d i` divides `toPoly b`. Induction on `fo`: a dropped
(constant) factor leaves `goProd rest ∣ b' ∣ b`; a kept factor `q` gives `toPoly q · goProd rest ∣
toPoly q · toPoly b' = toPoly b` by the step exactness. -/
theorem goProd_dvd (fuel : ℕ) : ∀ (fo : ℕ) (b d : CPoly) (i : ℕ),
    GoExact fuel fo b d → goProd (csqfreeFactor.go fuel fo b d i) ∣ toPoly b := by
  intro fo
  induction fo with
  | zero =>
    intro b d i _
    rw [csqfreeFactor.go.eq_def]
    simp [goProd]
  | succ fo ih =>
    intro b d i hex
    rw [csqfreeFactor.go.eq_def]
    by_cases hb : b.length ≤ 1
    · simp only [hb, if_true]
      simp [goProd]
    · simp only [hb, if_false]
      rw [GoExact] at hex
      simp only [hb, if_false] at hex
      obtain ⟨hexb, hexrest⟩ := hex
      set q := cmonic (cgcdExt fuel b d).1 with hqdef
      set b' := cdiv fuel b q with hb'def
      set d' := csub (cdiv fuel d q) (cderiv b') with hd'def
      have ihrest : goProd (csqfreeFactor.go fuel fo b' d' (i + 1)) ∣ toPoly b' :=
        ih b' d' (i + 1) hexrest
      by_cases hq : q.length ≤ 1
      · simp only [hq, if_true]
        exact ihrest.trans ⟨toPoly q, by rw [hexb]; ring⟩
      · simp only [hq, if_false]
        rw [goProd, List.map_cons, List.prod_cons, ← goProd, hexb]
        exact mul_dvd_mul_left (toPoly q) ihrest

/-- `goProd` realizes the radical fold: `toPoly (l.foldl (cmul · vi.1) init) = toPoly init · goProd l`. -/
theorem toPoly_foldl_cmul_fst (l : List (CPoly × ℕ)) (init : CPoly) :
    toPoly (l.foldl (fun acc vi => cmul acc vi.1) init) = toPoly init * goProd l := by
  induction l generalizing init with
  | nil => simp [goProd]
  | cons hd tl ih =>
    rw [List.foldl_cons, ih, toPoly_cmul]
    simp only [goProd, List.map_cons, List.prod_cons]
    ring

/-- The radical `Dstar = ∏ⱼ Vⱼ` (the `hermiteReduce` fold of the Yun factor list) reads to `goProd`:
`toPoly (factors.foldl (cmul · vi.1) [1]) = goProd factors`. -/
theorem toPoly_Dstar_eq (l : List (CPoly × ℕ)) :
    toPoly (l.foldl (fun acc (vi : CPoly × ℕ) => cmul acc vi.1) [1]) = goProd l := by
  rw [toPoly_foldl_cmul_fst]
  simp [toPoly_cons, toPoly_nil]

/-- **One Yun step is exact** when the extended-gcd terminates with enough fuel: with `q =
monic(gcd b d)` and `b ≠ 0`, `toPoly b = toPoly q · toPoly (b/q)`. The gcd divides `b`
(`toPoly_cgcdExt_dvd`), `cmonic` preserves this (`toPoly_cmonic_dvd`), and `q ∣ b` makes the Euclidean
division exact (`cmod_eq_zero_of_dvd` + `toPoly_cdiv_of_cmod_zero`). Discharges one conjunct of
`GoExact`/`SqfreeExact`. -/
theorem step_exact (fuel : ℕ) (b d : CPoly) (hbne : cnorm b ≠ [])
    (hterm : cgcdTerminates fuel b d) (hfuel : (cnorm b).length ≤ fuel) :
    toPoly b = toPoly (cmonic (cgcdExt fuel b d).1)
        * toPoly (cdiv fuel b (cmonic (cgcdExt fuel b d).1)) := by
  set q := cmonic (cgcdExt fuel b d).1 with hqdef
  have hgcd_dvd : toPoly (cgcdExt fuel b d).1 ∣ toPoly b := (toPoly_cgcdExt_dvd fuel b d hterm).1
  have hqb : toPoly q ∣ toPoly b := (toPoly_cmonic_dvd (cgcdExt fuel b d).1).trans hgcd_dvd
  have hb0 : toPoly b ≠ 0 := fun h => hbne ((cnorm_eq_nil_iff b).mpr h)
  have hq0 : toPoly q ≠ 0 := by
    intro h; rw [h, zero_dvd_iff] at hqb; exact hb0 hqb
  have hqne : cnorm q ≠ [] := fun h => hq0 ((cnorm_eq_nil_iff q).mp h)
  have hrem : toPoly (cmod fuel b q) = 0 := cmod_eq_zero_of_dvd fuel b q hqne hfuel hqb
  rw [toPoly_cdiv_of_cmod_zero fuel b q hqne hrem]; ring

/-- **Engine-honesty bundle** for `csqfreeFactor fuel D`: the initial deflation `b₁ = D/gcd(D,D')` is an
exact division (`toPoly D = toPoly(gcd) · toPoly b₁`) and every Yun loop step is exact (`GoExact`). On a
concrete `D` each conjunct is the (decidable) vanishing of a `cmod` remainder; `step_exact` reduces a
step to gcd-termination plus a fuel bound. -/
def SqfreeExact (fuel : ℕ) (D : CPoly) : Prop :=
  let p := cnorm D
  let g := (cgcdExt fuel p (cderiv p)).1
  let b1 := cdiv fuel p g
  let d1 := csub (cdiv fuel (cderiv p) g) (cderiv b1)
  toPoly p = toPoly g * toPoly b1 ∧ GoExact fuel fuel b1 d1

/-- **The Yun radical divides `D`** (`csqfreeFactor` correctness, radical clause): under the
engine-honesty bundle `SqfreeExact fuel D`, the squarefree radical `Dstar = ∏ⱼ Vⱼ` of
`csqfreeFactor fuel D` divides `D` in `ℚ[X]`: `toPoly Dstar ∣ toPoly D`. The product of the Yun factors
divides the initial deflation `b₁` (`goProd_dvd`), and `b₁ = D/gcd(D,D')` divides `D` by the initial
exact division. This is the honest mathematical content of the Yun squarefree factorization recorded by
`hermiteReduce`. The squarefree and pairwise-coprime clauses for full `csqfreeFactor` correctness — each
`Vⱼ` squarefree and the `Vⱼ` pairwise coprime — are proved at the abstract `K[X]` level below
(`yunFactorizationAbs_squarefree`/`_pairwise_isRelPrime`, unconditional from `A ≠ 0`) and transferred to
the concrete `csqfreeFactor` (`csqfreeFactor_squarefree`/`csqfreeFactor_pairwise_isRelPrime`) through the
now-crossed `ℚ`-instance diamond (see the `GoYun`/`go_factor_assoc` sections), under the honesty bundle
`SqfreeYun`. -/
theorem toPoly_Dstar_dvd_D (fuel : ℕ) (D : CPoly) (hex : SqfreeExact fuel D) :
    toPoly ((csqfreeFactor fuel D).foldl (fun acc (vi : CPoly × ℕ) => cmul acc vi.1) [1])
      ∣ toPoly D := by
  rw [toPoly_Dstar_eq, csqfreeFactor.eq_def]
  rw [SqfreeExact] at hex
  obtain ⟨hb1, hgo⟩ := hex
  have hdvd := goProd_dvd fuel fuel
    (cdiv fuel (cnorm D) (cgcdExt fuel (cnorm D) (cderiv (cnorm D))).1)
    (csub (cdiv fuel (cderiv (cnorm D)) (cgcdExt fuel (cnorm D) (cderiv (cnorm D))).1)
      (cderiv (cdiv fuel (cnorm D) (cgcdExt fuel (cnorm D) (cderiv (cnorm D))).1))) 1 hgo
  have hb1D : toPoly (cdiv fuel (cnorm D) (cgcdExt fuel (cnorm D) (cderiv (cnorm D))).1)
      ∣ toPoly D := by
    rw [← toPoly_cnorm D, hb1]; exact Dvd.intro_left _ rfl
  exact hdvd.trans hb1D

/-! ### What radical-divides buys (and what it does *not*) for the wrapper

`toPoly_Dstar_dvd_D` settles the **radical clause** `toPoly Dstar ∣ toPoly D`. This is the `Dstar ∣ D`
half mentioned in `hermiteReduce_residual_correct_of_dvd`'s docstring — but **not** the full divisibility
that theorem requires. Its hypothesis is `toPoly (D·gden²) ∣ toPoly (resNum·Dstar)` with
`resNum = A·gden² − D·(gnum'·gden − gnum·gden')`; cancelling `Dstar` against `D = Dstar·W`, this is
`W·gden² ∣ A·gden² − D·gprimeNum`, which forces `W ∣ A` and so does **not** follow from `Dstar ∣ D`
alone (it is the *cleared Hermite identity* `resNum·Dstar = Bres·(D·gden²)`, validated per-example by
`hermite_ex221_cleared_identity`). The missing half — "the numerator clears" — is exactly the
correctness of the computed rational part `g = gnum/gden` (that `A/D − g′` genuinely has denominator
`Dstar`), i.e. the full `hermiteInner`/`hermiteReduce` loop correctness, a strictly larger result than
`csqfreeFactor`'s honesty. So `toPoly_Dstar_dvd_D` is a genuine ingredient toward an unconditional
wrapper, but does not by itself discharge `hermiteReduce_residual_correct_of_dvd`. -/

/-! ### A computable witness for `SqfreeExact` (`native_decide`-checkable)

`SqfreeExact` is phrased with `toPoly` equalities (noncomputable). Its computable mirror `SqfreeExactComp`
asserts the *vanishing of the `cmod` remainders* of each division — a decidable condition that
`native_decide` checks on a concrete `D`. `SqfreeExactComp_to_SqfreeExact` discharges the `toPoly` bundle
from the `cmod`-zero witnesses (via `toPoly_cdiv_of_cmod_zero`), so the Yun radical-divides theorem
`toPoly_Dstar_dvd_D` is concretely instantiable. -/

/-- **Computable per-step exactness** for the Yun loop: at each non-terminal step the `cmod`-remainder of
`b` by `q = monic(gcd b d)` vanishes and `q ≠ 0`. Decidable (so `native_decide`-checkable). -/
def GoExactComp (fuel : ℕ) : ℕ → CPoly → CPoly → Prop
  | 0, _, _ => True
  | fo + 1, b, d =>
    if b.length ≤ 1 then True
    else
      let q := cmonic (cgcdExt fuel b d).1
      let b' := cdiv fuel b q
      let d' := csub (cdiv fuel d q) (cderiv b')
      cnorm (cmod fuel b q) = [] ∧ cnorm q ≠ [] ∧ GoExactComp fuel fo b' d'

/-- `GoExactComp` is decidable (the `cmod`-remainder vanishing and `cnorm ≠ []` checks are). -/
instance decGoExactComp (fuel fo : ℕ) (b d : CPoly) : Decidable (GoExactComp fuel fo b d) := by
  induction fo generalizing b d with
  | zero => exact inferInstanceAs (Decidable True)
  | succ fo ih =>
    rw [GoExactComp]
    by_cases hb : b.length ≤ 1
    · rw [if_pos hb]; exact inferInstanceAs (Decidable True)
    · rw [if_neg hb]
      have := ih (cdiv fuel b (cmonic (cgcdExt fuel b d).1))
        (csub (cdiv fuel d (cmonic (cgcdExt fuel b d).1))
          (cderiv (cdiv fuel b (cmonic (cgcdExt fuel b d).1))))
      infer_instance

/-- The computable `GoExactComp` implies the `toPoly` predicate `GoExact`: each vanishing `cmod`
remainder makes the corresponding `cdiv` an honest division (`toPoly_cdiv_of_cmod_zero`). -/
theorem GoExactComp_to_GoExact (fuel : ℕ) : ∀ (fo : ℕ) (b d : CPoly),
    GoExactComp fuel fo b d → GoExact fuel fo b d := by
  intro fo
  induction fo with
  | zero => intro b d _; trivial
  | succ fo ih =>
    intro b d h
    rw [GoExactComp] at h
    rw [GoExact]
    by_cases hb : b.length ≤ 1
    · simp only [hb, if_true]
    · simp only [hb, if_false] at h ⊢
      obtain ⟨hrem, hqne, hrest⟩ := h
      refine ⟨?_, ih _ _ hrest⟩
      have hrem0 : toPoly (cmod fuel b (cmonic (cgcdExt fuel b d).1)) = 0 := by
        rw [← toPoly_cnorm, hrem, toPoly_nil]
      exact (toPoly_cdiv_of_cmod_zero fuel b (cmonic (cgcdExt fuel b d).1) hqne hrem0).trans
        (mul_comm _ _)

/-- **Computable engine-honesty bundle** for `csqfreeFactor fuel D`: the `cmod`-remainders of the
initial deflation and of every Yun loop step vanish (and the divisors are nonzero). Decidable
(`native_decide`-checkable); implies the `toPoly` bundle `SqfreeExact`. -/
def SqfreeExactComp (fuel : ℕ) (D : CPoly) : Prop :=
  let p := cnorm D
  let g := (cgcdExt fuel p (cderiv p)).1
  let b1 := cdiv fuel p g
  let d1 := csub (cdiv fuel (cderiv p) g) (cderiv b1)
  (cnorm (cmod fuel p g) = [] ∧ cnorm g ≠ []) ∧ GoExactComp fuel fuel b1 d1

/-- `SqfreeExactComp` is decidable. -/
instance decSqfreeExactComp (fuel : ℕ) (D : CPoly) : Decidable (SqfreeExactComp fuel D) := by
  unfold SqfreeExactComp; infer_instance

/-- The computable `SqfreeExactComp` implies the `toPoly` bundle `SqfreeExact`: the vanishing
`cmod`-remainders make the initial deflation and each Yun step honest divisions
(`toPoly_cdiv_of_cmod_zero`, `GoExactComp_to_GoExact`). -/
theorem SqfreeExactComp_to_SqfreeExact (fuel : ℕ) (D : CPoly) :
    SqfreeExactComp fuel D → SqfreeExact fuel D := by
  intro h
  rw [SqfreeExactComp] at h
  rw [SqfreeExact]
  obtain ⟨⟨hrem, hgne⟩, hgo⟩ := h
  refine ⟨?_, GoExactComp_to_GoExact fuel fuel _ _ hgo⟩
  have hrem0 : toPoly (cmod fuel (cnorm D) (cgcdExt fuel (cnorm D) (cderiv (cnorm D))).1) = 0 := by
    rw [← toPoly_cnorm, hrem, toPoly_nil]
  exact (toPoly_cdiv_of_cmod_zero fuel (cnorm D) (cgcdExt fuel (cnorm D) (cderiv (cnorm D))).1
    hgne hrem0).trans (mul_comm _ _)

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

/-- **Example 2.2.1: the engine-honesty bundle holds** (`native_decide`): every `cmod`-remainder in the
Yun factorization of `D = x²(x²+2)³` vanishes, so `SqfreeExactComp 40 cD221` — and hence (via
`SqfreeExactComp_to_SqfreeExact`) the `toPoly` bundle `SqfreeExact 40 cD221` — holds. -/
theorem hermite_ex221_sqfreeExactComp : SqfreeExactComp 40 cD221 := by native_decide

/-- **Example 2.2.1: the Yun radical divides `D`** — the radical `Dstar = x(x²+2) = x³+2x` of
`csqfreeFactor 40 cD221` divides `D = x²(x²+2)³` in `ℚ[X]`. A concrete, non-vacuous instance of
`toPoly_Dstar_dvd_D`, discharged through the `native_decide`'d computable bundle
`hermite_ex221_sqfreeExactComp`. -/
example :
    toPoly ((csqfreeFactor 40 cD221).foldl (fun acc (vi : CPoly × ℕ) => cmul acc vi.1) [1])
      ∣ toPoly cD221 :=
  toPoly_Dstar_dvd_D 40 cD221 (SqfreeExactComp_to_SqfreeExact 40 cD221 hermite_ex221_sqfreeExactComp)

/-! ### Full `csqfreeFactor` Yun correctness — the abstract invariant

Toward the *equality* clause `toPoly D = u·∏ⱼ (toPoly Vⱼ)^iⱼ` (with each `Vⱼ` squarefree and the `Vⱼ`
pairwise coprime), this section ties `csqfreeFactor`'s `(b, d)` recurrence to the abstract Yun theory of
`SquarefreeFactorization` (the `deflation`/`squarefreePart`/`sqfreeFactPart`/`Yun` machinery). The
invariant carried through the loop: at step `i`, the working numerator `bᵢ` is the radical of the
remaining part `∏_{j≥i} Vⱼ = squarefreePart (deflation A (i−1))`, and the working derivative-poly
`dᵢ = Yᵢ − bᵢ′ = Vᵢ·Y_{i+1}`; the emitted factor `gcd(bᵢ, dᵢ) ~ Vᵢ = sqfreeFactPart A i`. -/

open UniqueFactorizationMonoid in
open Classical in
/-- **The abstract Yun gcd step**: `gcd(∏_{j≥i} Vⱼ, Yᵢ − (∏_{j≥i} Vⱼ)′) ~ Vᵢ`, the i-th squarefree
factor. The radical `S = squarefreePart (deflation A (i−1)) = Vᵢ · S'` (`S' = squarefreePart
(deflation A i)`) and the working derivative-poly `d = Yᵢ − S′ = Vᵢ · Y_{i+1}` share the common factor
`Vᵢ`; pulling it out (`gcd_mul_left'`), `gcd(S', Y_{i+1})` is a unit by `S' ⊥ Y_{i+1}`
(`isRelPrime_squarefreePart_Yun`). The core gcd identity pinning each Yun factor to `Vᵢ`. -/
theorem gcd_radical_yunStep_assoc {K : Type*} [Field K] [CharZero K] (A : K[X]) (i : ℕ) (hi : 1 ≤ i)
    (hA : A.primPart ≠ 0) :
    Associated
      (gcd (squarefreePart (deflation A (i - 1)))
        (Yun A i - derivative (squarefreePart (deflation A (i - 1)))))
      (sqfreeFactPart A i) := by
  have hsplit := squarefreePart_deflation_mul_sqfreeFactPart A i hi hA
  have hd := Yun_sub_derivative_squarefreePart A i hi hA
  set V := sqfreeFactPart A i with hV
  set S' := squarefreePart (deflation A i) with hS'
  set Y := Yun A (i + 1) with hY
  have hS : squarefreePart (deflation A (i - 1)) = V * S' := by
    rw [hV, hS', mul_comm]; exact hsplit.symm
  rw [hd, hS]
  refine (gcd_mul_left' V S' Y).trans ?_
  have hrp : IsRelPrime S' Y := by
    have h := isRelPrime_squarefreePart_Yun A (i + 1) (by omega) hA
    rwa [Nat.add_sub_cancel] at h
  have hunit : IsUnit (gcd S' Y) := gcd_isUnit_iff_isRelPrime.mpr hrp
  have : Associated (V * gcd S' Y) (V * 1) :=
    (associated_one_iff_isUnit.mpr hunit).mul_left V
  rwa [mul_one] at this

/-! ### Squarefreeness and pairwise coprimality of the Yun factors (from the abstract association)

A Yun factor that is `Associated` to some `sqfreeFactPart A j` inherits squarefreeness
(`sqfreeFactPart_squarefree` is `Associated`-invariant) and, between two factors at *distinct*
multiplicities, relative primality (`sqfreeFactPart_isRelPrime`). These reduce the squarefree/coprime
clauses of full `csqfreeFactor` correctness to the loop-association invariant
`toPoly Vⱼ ~ sqfreeFactPart A jⱼ` (the remaining open piece). -/

open UniqueFactorizationMonoid in
open Classical in
/-- **A Yun factor is squarefree**: any `V` associated to `sqfreeFactPart A j` is squarefree
(`sqfreeFactPart_squarefree` carried across `Associated.squarefree_iff`). -/
theorem squarefree_of_associated_sqfreeFactPart {K : Type*} [Field K]
    {V : K[X]} (A : K[X]) (j : ℕ) (h : Associated V (sqfreeFactPart A j)) :
    Squarefree V :=
  h.squarefree_iff.mpr (sqfreeFactPart_squarefree A j)

open UniqueFactorizationMonoid in
open Classical in
/-- **Two Yun factors at distinct multiplicities are relatively prime**: if `V ~ sqfreeFactPart A i`,
`W ~ sqfreeFactPart A j` and `i ≠ j`, then `IsRelPrime V W` (`sqfreeFactPart_isRelPrime` transported
across the associations via `IsRelPrime.of_dvd_left`/`of_dvd_right`). -/
theorem isRelPrime_of_associated_sqfreeFactPart {K : Type*} [Field K]
    {V W : K[X]} (A : K[X]) {i j : ℕ} (hij : i ≠ j)
    (hV : Associated V (sqfreeFactPart A i)) (hW : Associated W (sqfreeFactPart A j)) :
    IsRelPrime V W :=
  ((sqfreeFactPart_isRelPrime A hij).of_dvd_left hV.dvd).of_dvd_right hW.dvd

/-! ### The abstract Yun loop state and its step recurrence (exact, scalar-tracked)

`csqfreeFactor`'s loop carries a numerator `b` (the radical of the remaining part) and a
derivative-poly `d`, updating `(b, d) ↦ (b/gcd, d/gcd − (b/gcd)′)`. Because the `d`-update contains a
**subtraction**, the invariant cannot be tracked up to `Associated` alone (subtraction does not respect
associates); it must track a single *shared scalar* `c ∈ K` relating `(b, d)` to the abstract pair
`(Babs A i, Dabs A i)`. The two abstract objects satisfy EXACT product identities
`Babs A i = Vᵢ · Babs A (i+1)` and `Dabs A i = Vᵢ · Yun A (i+1)` (from
`squarefreePart_deflation_mul_sqfreeFactPart` and `Yun_sub_derivative_squarefreePart`), and `gcd Babs
Dabs = normalize Vᵢ` (the relatively-prime quotient is a unit), so dividing both by the monic gcd
multiplies each by the *same* scalar `(leadingCoeff Vᵢ)` — the shared-scalar invariant is preserved. -/

open Classical in
/-- **Abstract Yun numerator** `Babs A i = ∏_{j≥i} Vⱼ`, the radical of the remaining part at step `i`
(`= squarefreePart (deflation A (i−1))`). -/
noncomputable def Babs {K : Type*} [Field K] (A : K[X]) (i : ℕ) : K[X] :=
  squarefreePart (deflation A (i - 1))

open Classical in
/-- **Abstract Yun derivative-poly** `Dabs A i = Yᵢ − Babs A i′ = Vᵢ · Y_{i+1}`, the working `d` at
step `i`. -/
noncomputable def Dabs {K : Type*} [Field K] (A : K[X]) (i : ℕ) : K[X] :=
  Yun A i - derivative (squarefreePart (deflation A (i - 1)))

open Classical in
/-- `Babs A i = Vᵢ · Babs A (i+1)` (exact): the remaining radical factors off `Vᵢ` and the radical of
the next remaining part. Restates `squarefreePart_deflation_mul_sqfreeFactPart`. -/
theorem Babs_eq_mul {K : Type*} [Field K] (A : K[X]) (i : ℕ) (hi : 1 ≤ i) (hA : A.primPart ≠ 0) :
    Babs A i = sqfreeFactPart A i * Babs A (i + 1) := by
  rw [Babs, Babs, Nat.add_sub_cancel, ← squarefreePart_deflation_mul_sqfreeFactPart A i hi hA,
    mul_comm]

open Classical in
/-- `Dabs A i = Vᵢ · Yun A (i+1)` (exact): the working derivative-poly factors off `Vᵢ`. Restates
`Yun_sub_derivative_squarefreePart`. -/
theorem Dabs_eq_mul {K : Type*} [Field K] [CharZero K] (A : K[X]) (i : ℕ) (hi : 1 ≤ i)
    (hA : A.primPart ≠ 0) :
    Dabs A i = sqfreeFactPart A i * Yun A (i + 1) := by
  rw [Dabs]; exact Yun_sub_derivative_squarefreePart A i hi hA

open UniqueFactorizationMonoid in
open Classical in
/-- **The monic Yun gcd is `normalize Vᵢ`**: `gcd (Babs A i) (Dabs A i) = normalize (sqfreeFactPart
A i)`. Both `Babs A i = Vᵢ·Babs A (i+1)` and `Dabs A i = Vᵢ·Y_{i+1}` carry the common factor `Vᵢ`;
factoring it out (`gcd_mul_left`), `gcd (Babs A (i+1)) (Y_{i+1})` is a unit (relatively prime,
`isRelPrime_squarefreePart_Yun`, normalized to `1`), leaving `normalize Vᵢ`. -/
theorem gcd_Babs_Dabs {K : Type*} [Field K] [CharZero K] (A : K[X]) (i : ℕ) (hi : 1 ≤ i)
    (hA : A.primPart ≠ 0) :
    gcd (Babs A i) (Dabs A i) = normalize (sqfreeFactPart A i) := by
  rw [Babs_eq_mul A i hi hA, Dabs_eq_mul A i hi hA, gcd_mul_left]
  -- `gcd (Babs A (i+1)) (Yun A (i+1)) = 1`
  have hrp : IsRelPrime (Babs A (i + 1)) (Yun A (i + 1)) := by
    have h := isRelPrime_squarefreePart_Yun A (i + 1) (by omega) hA
    rw [Babs]; rwa [Nat.add_sub_cancel] at h
  have hunit : IsUnit (gcd (Babs A (i + 1)) (Yun A (i + 1))) :=
    gcd_isUnit_iff_isRelPrime.mpr hrp
  rw [(normalize_eq_one.mpr hunit ▸ (normalize_gcd (Babs A (i + 1)) (Yun A (i + 1))).symm :
    gcd (Babs A (i + 1)) (Yun A (i + 1)) = 1), mul_one]

open Classical in
/-- `Vᵢ = C(leadingCoeff Vᵢ) · normalize Vᵢ` over a field: the monic normalization scaled back by the
leading coefficient recovers the polynomial. (`normalize p = p · C(leadingCoeff p)⁻¹`.) -/
theorem self_eq_C_leadingCoeff_mul_normalize {K : Type*} [Field K] (p : K[X]) (hp : p ≠ 0) :
    p = Polynomial.C p.leadingCoeff * normalize p := by
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
  have hcn : ((normUnit p.leadingCoeff : K) : K) = p.leadingCoeff⁻¹ := by
    simp [normUnit, hlc]
  rw [normalize_apply, Polynomial.coe_normUnit, hcn]
  rw [show Polynomial.C p.leadingCoeff * (p * Polynomial.C p.leadingCoeff⁻¹)
        = (Polynomial.C p.leadingCoeff * Polynomial.C p.leadingCoeff⁻¹) * p from by ring,
    ← map_mul, mul_inv_cancel₀ hlc, map_one, one_mul]

/-! ### The shared-scalar Yun loop invariant and its one-step preservation -/

open Classical in
/-- **The Yun loop invariant** (shared-scalar form): the concrete working pair `(b, d)` is a *common
constant multiple* `C c · (Babs A i, Dabs A i)` of the abstract radical/derivative-poly at step `i`
(with `c ≠ 0`). The single shared scalar `c` is what lets the subtraction in the `d`-update commute
with the abstract identities. -/
def YunInv {K : Type*} [Field K] (A : K[X]) (i : ℕ) (b d : K[X]) : Prop :=
  ∃ c : K, c ≠ 0 ∧ b = Polynomial.C c * Babs A i ∧ d = Polynomial.C c * Dabs A i

open UniqueFactorizationMonoid in
open Classical in
/-- **One Yun loop step preserves the invariant.** From `YunInv A i b d` (with `1 ≤ i`,
`A.primPart ≠ 0`), the monic gcd `q = gcd b d = normalize Vᵢ`, the deflated numerator `b' = b/q` and
updated derivative-poly `d' = d/q − b′′` satisfy `YunInv A (i+1) b' d'` — with the scalar advancing by
`leadingCoeff Vᵢ`. The shared scalar `c·leadingCoeff Vᵢ` multiplies *both* `Babs A (i+1)` and
`Dabs A (i+1)`, so the subtraction `d/q − (b/q)′` realizes exactly `C(c·w)·(Y_{i+1} − Babs A (i+1)′)`. -/
theorem yunStep_preserves {K : Type*} [Field K] [CharZero K] (A : K[X]) (i : ℕ) (hi : 1 ≤ i)
    (hA : A.primPart ≠ 0) {b d : K[X]} (hinv : YunInv A i b d) :
    gcd b d = normalize (sqfreeFactPart A i) ∧
      YunInv A (i + 1) (b / gcd b d) (d / gcd b d - derivative (b / gcd b d)) := by
  obtain ⟨c, hc, hb, hd⟩ := hinv
  set V := sqfreeFactPart A i with hV
  have hV0 : V ≠ 0 := sqfreeFactPart_ne_zero A i
  set w := V.leadingCoeff with hw
  have hw0 : w ≠ 0 := leadingCoeff_ne_zero.mpr hV0
  set Vn := normalize V with hVn
  have hVn0 : Vn ≠ 0 := by rw [hVn]; simpa using hV0
  -- `gcd b d = normalize V`: the shared constant `C c` drops out of the gcd.
  have hgcd : gcd b d = Vn := by
    rw [hb, hd, gcd_mul_left, normalize_eq_one.mpr (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc)),
      one_mul, gcd_Babs_Dabs A i hi hA, ← hV, ← hVn]
  -- `V = C w * Vn`.
  have hVeq : V = Polynomial.C w * Vn := self_eq_C_leadingCoeff_mul_normalize V hV0
  -- `b = Vn * (C (c*w) * Babs A (i+1))`.
  have hbfact : b = Vn * (Polynomial.C (c * w) * Babs A (i + 1)) := by
    rw [hb, Babs_eq_mul A i hi hA, ← hV, hVeq, map_mul]; ring
  -- `d = Vn * (C (c*w) * Yun A (i+1))`.
  have hdfact : d = Vn * (Polynomial.C (c * w) * Yun A (i + 1)) := by
    rw [hd, Dabs_eq_mul A i hi hA, ← hV, hVeq, map_mul]; ring
  -- divisions by the monic `q = Vn`.
  have hb' : b / gcd b d = Polynomial.C (c * w) * Babs A (i + 1) := by
    rw [hgcd, hbfact, mul_div_cancel_left₀ _ hVn0]
  have hd' : d / gcd b d = Polynomial.C (c * w) * Yun A (i + 1) := by
    rw [hgcd, hdfact, mul_div_cancel_left₀ _ hVn0]
  refine ⟨hgcd, c * w, mul_ne_zero hc hw0, hb', ?_⟩
  -- `d' = d/q − (b/q)′ = C(c*w)·(Y_{i+1} − Babs A (i+1)′) = C(c*w)·Dabs A (i+1)`.
  rw [hd', hb', derivative_C_mul, Dabs, Nat.add_sub_cancel, Babs, Nat.add_sub_cancel, mul_sub]

open UniqueFactorizationMonoid in
open Classical in
/-- **The emitted Yun factor is associated to `Vᵢ`**: under `YunInv A i b d`, the monic gcd `gcd b d`
(the i-th emitted squarefree factor) is `Associated (sqfreeFactPart A i)`. Hence it is squarefree
(`squarefree_of_associated_sqfreeFactPart`); factors at distinct multiplicities are relatively prime
(`isRelPrime_of_associated_sqfreeFactPart`). -/
theorem yunStep_emit_assoc {K : Type*} [Field K] [CharZero K] (A : K[X]) (i : ℕ) (hi : 1 ≤ i)
    (hA : A.primPart ≠ 0) {b d : K[X]} (hinv : YunInv A i b d) :
    Associated (gcd b d) (sqfreeFactPart A i) := by
  rw [(yunStep_preserves A i hi hA hinv).1]
  exact normalize_associated (sqfreeFactPart A i)

/-! ### The abstract Yun loop and its factorwise correctness

The abstract loop `yunLoopAbs A (b, d) i n` runs `n` Yun steps from the working pair `(b, d)` at
multiplicity `i`, emitting `gcd bⱼ dⱼ` (the j-th squarefree factor) at each step. Iterating
`yunStep_preserves` keeps `YunInv A (i+j)` along the run, so the j-th emitted factor is `Associated
(sqfreeFactPart A (i+j))` — squarefree, and at distinct multiplicities pairwise relatively prime. -/

open Classical in
/-- **Abstract Yun loop**: `n` steps from `(b, d)` at multiplicity `i`, emitting `gcd bⱼ dⱼ` each step
(the abstract counterpart of `csqfreeFactor.go`, with the `K[X]` monic `gcd` for `cmonic ∘ cgcdExt`
and honest `/` for `cdiv`). -/
noncomputable def yunLoopAbs {K : Type*} [Field K] (A : K[X]) : K[X] × K[X] → ℕ → ℕ → List K[X]
  | _, _, 0 => []
  | (b, d), i, (n + 1) =>
      gcd b d :: yunLoopAbs A (b / gcd b d, d / gcd b d - derivative (b / gcd b d)) (i + 1) n

open Classical in
/-- **Abstract Yun loop correctness**: from `YunInv A i b d` (with `1 ≤ i`), the `n`-step run emits
factors `[gcd b₁ d₁, …]` that are `Forall₂ Associated` to `[Vᵢ, Vᵢ₊₁, …, V_{i+n−1}]`
(`sqfreeFactPart A (i+j)`). The decomposition spine: each Yun factor is, up to a constant, the
matching squarefree-factorization part. Induction on `n` using `yunStep_emit_assoc` (head) and
`yunStep_preserves` (tail invariant). -/
theorem yunLoopAbs_forall₂ {K : Type*} [Field K] [CharZero K] (A : K[X]) (hA : A.primPart ≠ 0) :
    ∀ (n i : ℕ) (b d : K[X]), 1 ≤ i → YunInv A i b d →
      List.Forall₂ Associated (yunLoopAbs A (b, d) i n)
        ((List.range n).map (fun j => sqfreeFactPart A (i + j))) := by
  intro n
  induction n with
  | zero => intro i b d _ _; simp [yunLoopAbs]
  | succ n ih =>
    intro i b d hi hinv
    rw [yunLoopAbs, List.range_succ_eq_map, List.map_cons]
    refine List.Forall₂.cons (yunStep_emit_assoc A i hi hA hinv) ?_
    have hstep := (yunStep_preserves A i hi hA hinv).2
    have htail := ih (i + 1) (b / gcd b d) (d / gcd b d - derivative (b / gcd b d))
      (by omega) hstep
    rw [List.map_map]
    have hreindex : (List.range n).map ((fun j => sqfreeFactPart A (i + j)) ∘ Nat.succ)
        = (List.range n).map (fun j => sqfreeFactPart A ((i + 1) + j)) :=
      List.map_congr_left (fun j _ => by simp only [Function.comp_apply]; congr 1; omega)
    rw [hreindex]
    exact htail

open Classical in
/-- **Every Yun factor is squarefree** (abstract loop): under `YunInv A i b d` (`1 ≤ i`), every member
of `yunLoopAbs A (b, d) i n` is squarefree. Direct induction: the head `gcd b d ~ Vᵢ` is squarefree
(`yunStep_emit_assoc` + `squarefree_of_associated_sqfreeFactPart`); the tail keeps `YunInv` (step). -/
theorem yunLoopAbs_squarefree {K : Type*} [Field K] [CharZero K] (A : K[X]) (hA : A.primPart ≠ 0) :
    ∀ (n i : ℕ) (b d : K[X]), 1 ≤ i → YunInv A i b d →
      ∀ V ∈ yunLoopAbs A (b, d) i n, Squarefree V := by
  intro n
  induction n with
  | zero => intro i b d _ _ V hV; simp [yunLoopAbs] at hV
  | succ n ih =>
    intro i b d hi hinv V hV
    rw [yunLoopAbs, List.mem_cons] at hV
    rcases hV with rfl | hV
    · exact squarefree_of_associated_sqfreeFactPart A i (yunStep_emit_assoc A i hi hA hinv)
    · exact ih (i + 1) _ _ (by omega) (yunStep_preserves A i hi hA hinv).2 V hV

open Classical in
/-- **The Yun factors are pairwise relatively prime** (abstract loop): under `YunInv A i b d`
(`1 ≤ i`), members of `yunLoopAbs A (b, d) i n` at distinct list positions `p ≠ q` are `IsRelPrime`.
Their multiplicities `i+p ≠ i+q` differ, so `isRelPrime_of_associated_sqfreeFactPart` applies to the
two factors (each `Associated` to its `sqfreeFactPart` by `yunLoopAbs_forall₂`). -/
theorem yunLoopAbs_pairwise_isRelPrime {K : Type*} [Field K] [CharZero K] (A : K[X])
    (hA : A.primPart ≠ 0) (n i : ℕ) (b d : K[X]) (hi : 1 ≤ i) (hinv : YunInv A i b d)
    {p q : ℕ} (hpq : p ≠ q) (hp : p < (yunLoopAbs A (b, d) i n).length)
    (hq : q < (yunLoopAbs A (b, d) i n).length) :
    IsRelPrime ((yunLoopAbs A (b, d) i n).get ⟨p, hp⟩) ((yunLoopAbs A (b, d) i n).get ⟨q, hq⟩) := by
  have hF := yunLoopAbs_forall₂ A hA n i b d hi hinv
  have hlen : (yunLoopAbs A (b, d) i n).length
      = ((List.range n).map (fun j => sqfreeFactPart A (i + j))).length := hF.length_eq
  have hp' : p < ((List.range n).map (fun j => sqfreeFactPart A (i + j))).length := hlen ▸ hp
  have hq' : q < ((List.range n).map (fun j => sqfreeFactPart A (i + j))).length := hlen ▸ hq
  have hAp : Associated ((yunLoopAbs A (b, d) i n).get ⟨p, hp⟩) (sqfreeFactPart A (i + p)) := by
    have h := hF.get hp hp'
    simpa using h
  have hAq : Associated ((yunLoopAbs A (b, d) i n).get ⟨q, hq⟩) (sqfreeFactPart A (i + q)) := by
    have h := hF.get hq hq'
    simpa using h
  exact isRelPrime_of_associated_sqfreeFactPart A (by omega : i + p ≠ i + q) hAp hAq

/-! ### The Yun decomposition: product of the factors -/

open Classical in
/-- **The product of the Yun factors is the remaining radical** (abstract loop): under `YunInv A i b d`
(`1 ≤ i`), the product of the `n` emitted factors is `Associated (∏_{j<n} Vᵢ₊ⱼ)` (`= ∏_{j<n}
sqfreeFactPart A (i+j)`). Via `List.rel_prod` (`Associated` is multiplicative) on
`yunLoopAbs_forall₂`. -/
theorem yunLoopAbs_prod_assoc {K : Type*} [Field K] [CharZero K] (A : K[X]) (hA : A.primPart ≠ 0)
    (n i : ℕ) (b d : K[X]) (hi : 1 ≤ i) (hinv : YunInv A i b d) :
    Associated (yunLoopAbs A (b, d) i n).prod
      (((List.range n).map (fun j => sqfreeFactPart A (i + j))).prod) :=
  List.rel_prod (R := Associated) (Associated.refl 1)
    (fun _ _ hx _ _ hy => hx.mul_mul hy) (yunLoopAbs_forall₂ A hA n i b d hi hinv)

open Classical in
/-- **Powered product** of a Yun-factor list `[e₀, e₁, …]`: `∏ₖ eₖ^{i+k}`, raising the k-th factor to
its multiplicity `i+k` (the radical-to-full-power lift used in the Yun decomposition `∏ⱼ Vⱼ^iⱼ`). -/
noncomputable def prodPow {K : Type*} [Field K] (i : ℕ) : List K[X] → K[X]
  | [] => 1
  | e :: es => e ^ i * prodPow (i + 1) es

open Classical in
/-- `prodPow` respects `Forall₂ Associated` pointwise: associated factor-lists give associated
powered products (each `eₖ ~ Vₖ` lifts to `eₖ^{i+k} ~ Vₖ^{i+k}` by `Associated.pow`, multiplied). -/
theorem prodPow_associated {K : Type*} [Field K] {l₁ l₂ : List K[X]}
    (h : List.Forall₂ Associated l₁ l₂) (i : ℕ) :
    Associated (prodPow i l₁) (prodPow i l₂) := by
  induction h generalizing i with
  | nil => exact Associated.refl _
  | cons hhd _ ih => exact hhd.pow_pow.mul_mul (ih (i + 1))

open Classical in
/-- **The exponentiated Yun decomposition** (abstract loop): under `YunInv A i b d` (`1 ≤ i`), the
powered product `∏ₖ eₖ^{i+k}` of the emitted factors is `Associated (∏_{j<n} Vᵢ₊ⱼ^{i+j})`. From
`yunLoopAbs_forall₂` via `prodPow_associated`. With `n` covering all multiplicities and `b₁/d₁` the
initial radical/derivative-poly, the right side is `A.primPart` up to associates
(`primPart_associated_prod_sqfreeFactPart`), giving the Yun product decomposition `D ~ u·∏ⱼ Vⱼ^iⱼ`. -/
theorem yunLoopAbs_prodPow_assoc {K : Type*} [Field K] [CharZero K] (A : K[X]) (hA : A.primPart ≠ 0)
    (n i : ℕ) (b d : K[X]) (hi : 1 ≤ i) (hinv : YunInv A i b d) :
    Associated (prodPow i (yunLoopAbs A (b, d) i n))
      (prodPow i ((List.range n).map (fun j => sqfreeFactPart A (i + j)))) :=
  prodPow_associated (yunLoopAbs_forall₂ A hA n i b d hi hinv) i

/-! ### The Yun loop base case: `csqfreeFactor`'s `(b₁, d₁)` satisfy `YunInv A 1`

The initialization `b₁ = A/gcd(A,A′)`, `d₁ = A′/gcd(A,A′) − b₁′` of `csqfreeFactor` satisfies the
shared-scalar invariant `YunInv A 1 b₁ d₁` with scalar `c = leadingCoeff A`. The two monic equalities
`deflation A 0 = normalize A` (the monic radical-free part) and `gcd A A′ = deflation A 1` reduce the
init to `derivative_deflation_pred` (`(deflation A 0)′ = deflation A 1 · Yun A 1`) with the scalar
`leadingCoeff A` consistently shared between `b₁` and `d₁`. -/

open UniqueFactorizationMonoid in
open Classical in
/-- `squarefreePart (deflation A k)` is monic (a product of normalized — hence monic — prime factors). -/
theorem squarefreePart_deflation_monic {K : Type*} [Field K] (A : K[X]) (k : ℕ)
    (hA : A.primPart ≠ 0) : (squarefreePart (deflation A k)).Monic := by
  rw [squarefreePart_deflation A k hA]
  refine monic_prod_of_monic _ _ (fun P hP => ?_)
  have hmem := Multiset.mem_toFinset.mp (Finset.mem_filter.mp hP).1
  rw [← normalize_normalized_factor P hmem]
  exact monic_normalize (irreducible_of_normalized_factor P hmem).ne_zero

open UniqueFactorizationMonoid in
open Classical in
/-- `deflation A k` is monic (a product of normalized prime *powers*). -/
theorem deflation_monic {K : Type*} [Field K] (A : K[X]) (k : ℕ) :
    (deflation A k).Monic := by
  rw [deflation]
  refine monic_prod_of_monic _ _ (fun P hP => ?_)
  have hmem := Multiset.mem_toFinset.mp hP
  refine (?_ : (P).Monic).pow _
  rw [← normalize_normalized_factor P hmem]
  exact monic_normalize (irreducible_of_normalized_factor P hmem).ne_zero

open UniqueFactorizationMonoid in
open Classical in
/-- `A.primPart` is associated to `A` (over a field the content `C (content A)` is a unit). -/
theorem associated_primPart_self {K : Type*} [Field K] (A : K[X]) (hA0 : A ≠ 0) :
    Associated A.primPart A := by
  have hc : IsUnit (Polynomial.C A.content) := by
    rw [isUnit_C, isUnit_iff_ne_zero]
    exact fun h => hA0 (by rw [A.eq_C_content_mul_primPart, h, map_zero, zero_mul])
  refine ⟨hc.unit, ?_⟩
  rw [IsUnit.unit_spec]
  conv_rhs => rw [A.eq_C_content_mul_primPart]
  ring

open UniqueFactorizationMonoid in
open Classical in
/-- `deflation A 0 = normalize A`: the monic radical-free part is the monic associate of `A`
(`deflation A 0 ~ A.primPart ~ A ~ normalize A`, all reduced to equality by monic-ness). -/
theorem deflation_zero_eq_normalize {K : Type*} [Field K] (A : K[X]) (hA0 : A ≠ 0)
    (hA : A.primPart ≠ 0) : deflation A 0 = normalize A := by
  refine eq_of_monic_of_associated (deflation_monic A 0)
    ((monic_normalize hA0)) ?_
  exact ((deflation_zero A hA).trans (associated_primPart_self A hA0)).trans
    (associated_normalize A)

open UniqueFactorizationMonoid in
open Classical in
/-- `A′ = C(content A) · A.primPart′`: the derivative pulls the constant content through. -/
theorem derivative_eq_C_content_mul_derivative_primPart {K : Type*} [Field K] (A : K[X]) :
    derivative A = Polynomial.C A.content * derivative A.primPart := by
  conv_lhs => rw [A.eq_C_content_mul_primPart]
  rw [derivative_mul, derivative_C, zero_mul, zero_add]

open UniqueFactorizationMonoid in
open Classical in
/-- `gcd A A′ = deflation A 1` over a field: the gcd of `A` and its derivative is Musser's first
deflation. `gcd A A′ ~ gcd A.primPart A.primPart′ ~ deflation A 1` (`deflation_one_eq_gcd`), both monic
hence equal. -/
theorem gcd_self_derivative_eq_deflation_one {K : Type*} [Field K] [CharZero K] (A : K[X])
    (hA0 : A ≠ 0) (hA : A.primPart ≠ 0) :
    gcd A (derivative A) = deflation A 1 := by
  have hgne : gcd A (derivative A) ≠ 0 :=
    fun h => hA0 (eq_zero_of_zero_dvd (h ▸ gcd_dvd_left _ _))
  have hgmonic : (gcd A (derivative A)).Monic := by
    rw [← normalize_eq_self_iff_monic hgne]; exact normalize_gcd A (derivative A)
  refine eq_of_monic_of_associated hgmonic (deflation_monic A 1) ?_
  -- `gcd A A′ ~ gcd A.primPart A.primPart′ ~ deflation A 1`
  have hAp : Associated A A.primPart := (associated_primPart_self A hA0).symm
  have hc : IsUnit (Polynomial.C A.content) := by
    rw [isUnit_C, isUnit_iff_ne_zero]
    exact fun h => hA0 (by rw [A.eq_C_content_mul_primPart, h, map_zero, zero_mul])
  have hAp' : Associated (derivative A) (derivative A.primPart) := by
    rw [derivative_eq_C_content_mul_derivative_primPart A]
    exact associated_unit_mul_left (derivative A.primPart) (Polynomial.C A.content) hc
  exact (Associated.gcd hAp hAp').trans (deflation_one_eq_gcd A hA)

open UniqueFactorizationMonoid in
open Classical in
/-- `squarefreePart (deflation A 0) · deflation A 1 = deflation A 0` (exact, monic version of relation
1.11): the radical times the first deflation recovers the radical-free part, with associated monics
forced to equality. -/
theorem squarefreePart_mul_deflation_one {K : Type*} [Field K] (A : K[X]) (hA : A.primPart ≠ 0) :
    squarefreePart (deflation A 0) * deflation A 1 = deflation A 0 := by
  refine eq_of_monic_of_associated
    ((squarefreePart_deflation_monic A 0 hA).mul (deflation_monic A 1)) (deflation_monic A 0) ?_
  exact squarefreePart_mul_deflation_succ A 0 hA

open UniqueFactorizationMonoid in
open Classical in
/-- **The Yun loop base case**: `csqfreeFactor`'s initialization `(b₁, d₁) = (A/gcd(A,A′), A′/gcd(A,A′)
− b₁′)` satisfies `YunInv A 1 b₁ d₁` with shared scalar `c = leadingCoeff A`. From the equalities
`deflation A 0 = normalize A`, `gcd A A′ = deflation A 1`, the exact relation `Babs A 1 · deflation A 1
= deflation A 0`, and `derivative_deflation_pred` (`(deflation A 0)′ = deflation A 1 · Yun A 1`): both
`b₁` and `d₁` factor as `C(leadingCoeff A)` times the abstract `Babs A 1`, `Dabs A 1`. -/
theorem yunInv_base {K : Type*} [Field K] [CharZero K] (A : K[X]) (hA0 : A ≠ 0)
    (hA : A.primPart ≠ 0) :
    YunInv A 1 (A / gcd A (derivative A))
      (derivative A / gcd A (derivative A) - derivative (A / gcd A (derivative A))) := by
  have hg : gcd A (derivative A) = deflation A 1 := gcd_self_derivative_eq_deflation_one A hA0 hA
  have hd1ne : deflation A 1 ≠ 0 := deflation_ne_zero A 1
  -- `A = C(lc A) · deflation A 0`.
  have hlc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hA0
  have hAeq : A = Polynomial.C A.leadingCoeff * deflation A 0 := by
    rw [deflation_zero_eq_normalize A hA0 hA]
    exact self_eq_C_leadingCoeff_mul_normalize A hA0
  -- `b₁ = A/g = C(lc A) · Babs A 1`.
  have hbabs : Babs A 1 = squarefreePart (deflation A 0) := by rw [Babs]
  -- `A = (C lc · squarefreePart (deflation A 0)) · deflation A 1`
  have hAfact : A = (Polynomial.C A.leadingCoeff * squarefreePart (deflation A 0)) * deflation A 1 := by
    rw [mul_assoc, squarefreePart_mul_deflation_one A hA, ← hAeq]
  have hb1 : A / gcd A (derivative A) = Polynomial.C A.leadingCoeff * Babs A 1 := by
    rw [hg, hbabs]
    nth_rewrite 1 [hAfact]
    rw [mul_div_cancel_right₀ _ hd1ne]
  -- `A′ = C(lc A) · deflation A 1 · Yun A 1`  (from `derivative_deflation_pred` at i=1).
  have hAderiv : derivative A = Polynomial.C A.leadingCoeff * (deflation A 1 * Yun A 1) := by
    have hdp := derivative_deflation_pred A 1 (le_refl 1)
    rw [Nat.sub_self] at hdp
    conv_lhs => rw [hAeq, derivative_C_mul, hdp]
  -- `A′/g = C(lc A) · Yun A 1`.
  have hd1div : derivative A / gcd A (derivative A) = Polynomial.C A.leadingCoeff * Yun A 1 := by
    rw [hg]
    nth_rewrite 1 [hAderiv]
    rw [mul_comm (deflation A 1) (Yun A 1), ← mul_assoc, mul_div_cancel_right₀ _ hd1ne]
  -- assemble.
  refine ⟨A.leadingCoeff, hlc, hb1, ?_⟩
  rw [hd1div, hb1, derivative_C_mul, Dabs, Nat.sub_self, ← hbabs, mul_sub]

/-! ### Unconditional abstract Yun factorization

Starting the loop from the `csqfreeFactor` initialization (`yunInv_base`), the abstract Yun loop
`yunFactorizationAbs A n = yunLoopAbs A (A/gcd(A,A′), A′/gcd(A,A′) − …) 1 n` factorizes `A` with no
`YunInv` hypothesis — only `A ≠ 0`. All four clauses (factorwise association to `Vᵢ`, squarefree,
pairwise relatively prime, product decomposition) hold unconditionally. -/

open Classical in
/-- **Unconditional abstract Yun factorization** of `A : K[X]`: the `n`-step Yun loop from the
initialization `(A/gcd(A,A′), A′/gcd(A,A′) − (A/gcd(A,A′))′)`. -/
noncomputable def yunFactorizationAbs {K : Type*} [Field K] (A : K[X]) (n : ℕ) : List K[X] :=
  yunLoopAbs A (A / gcd A (derivative A),
    derivative A / gcd A (derivative A) - derivative (A / gcd A (derivative A))) 1 n

open Classical in
/-- **Factorwise correctness** (unconditional): `yunFactorizationAbs A n` is `Forall₂ Associated` to
`[V₁, …, Vₙ]` (`sqfreeFactPart A (1+j)`). From `yunLoopAbs_forall₂` + `yunInv_base`. -/
theorem yunFactorizationAbs_forall₂ {K : Type*} [Field K] [CharZero K] (A : K[X]) (hA0 : A ≠ 0)
    (hA : A.primPart ≠ 0) (n : ℕ) :
    List.Forall₂ Associated (yunFactorizationAbs A n)
      ((List.range n).map (fun j => sqfreeFactPart A (1 + j))) :=
  yunLoopAbs_forall₂ A hA n 1 _ _ (le_refl 1) (yunInv_base A hA0 hA)

open Classical in
/-- **Every Yun factor is squarefree** (unconditional). -/
theorem yunFactorizationAbs_squarefree {K : Type*} [Field K] [CharZero K] (A : K[X]) (hA0 : A ≠ 0)
    (hA : A.primPart ≠ 0) (n : ℕ) : ∀ V ∈ yunFactorizationAbs A n, Squarefree V :=
  yunLoopAbs_squarefree A hA n 1 _ _ (le_refl 1) (yunInv_base A hA0 hA)

open Classical in
/-- **The Yun factors are pairwise relatively prime** (unconditional). -/
theorem yunFactorizationAbs_pairwise_isRelPrime {K : Type*} [Field K] [CharZero K] (A : K[X])
    (hA0 : A ≠ 0) (hA : A.primPart ≠ 0) (n : ℕ) {p q : ℕ} (hpq : p ≠ q)
    (hp : p < (yunFactorizationAbs A n).length) (hq : q < (yunFactorizationAbs A n).length) :
    IsRelPrime ((yunFactorizationAbs A n).get ⟨p, hp⟩) ((yunFactorizationAbs A n).get ⟨q, hq⟩) :=
  yunLoopAbs_pairwise_isRelPrime A hA n 1 _ _ (le_refl 1) (yunInv_base A hA0 hA) hpq hp hq

open Classical in
/-- **The product decomposition** (unconditional): the powered product `∏ₖ eₖ^{1+k}` of the Yun
factors is `Associated (∏_{j<n} V_{1+j}^{1+j})`. With `n` covering all multiplicities this is
`A.primPart` up to associates (`primPart_associated_prod_sqfreeFactPart`), i.e. the Yun decomposition
`A ~ u·∏ⱼ Vⱼ^iⱼ`. -/
theorem yunFactorizationAbs_prodPow_assoc {K : Type*} [Field K] [CharZero K] (A : K[X]) (hA0 : A ≠ 0)
    (hA : A.primPart ≠ 0) (n : ℕ) :
    Associated (prodPow 1 (yunFactorizationAbs A n))
      (prodPow 1 ((List.range n).map (fun j => sqfreeFactPart A (1 + j)))) :=
  yunLoopAbs_prodPow_assoc A hA n 1 _ _ (le_refl 1) (yunInv_base A hA0 hA)

/-! ### Bridging the concrete `csqfreeFactor` monic gcd to the abstract `gcd`

The atomic concrete↔abstract correspondence for one Yun step: the computable monic gcd `cmonic
(cgcdExt fuel b d).1` realizes the abstract monic `gcd (toPoly b) (toPoly d)` under `toPoly`. This is
the load-bearing translation that aligns `csqfreeFactor.go`'s emitted factor `cmonic (cgcdExt b d)`
with `yunLoopAbs`'s emitted factor `gcd (toPoly b) (toPoly d)`. -/

/-- **`cmonic` realizes `normalize`** through `toPoly`: `toPoly (cmonic q) = normalize (toPoly q)`. The
nonzero case is `C (clead q)⁻¹ · toPoly q`, with `clead q = leadingCoeff (toPoly q)`, which is exactly
`normalize` over a field; the zero case is `0`. -/
theorem toPoly_cmonic_eq_normalize (q : CPoly) :
    toPoly (cmonic q) = normalize (toPoly q) := by
  unfold cmonic
  by_cases h : cisZero (cnorm q)
  · simp only [h, if_true]
    have hq0 : toPoly q = 0 := by
      have : cnorm q = [] := by simpa [cisZero] using h
      rw [← toPoly_cnorm, this, toPoly_nil]
    rw [toPoly_nil, hq0, normalize_zero]
  · simp only [h, Bool.false_eq_true, if_false]
    have hqn : cnorm q ≠ [] := by simpa [cisZero] using h
    have hq0 : toPoly q ≠ 0 := fun hh => hqn ((cnorm_eq_nil_iff q).mpr hh)
    rw [toPoly_cscale, toPoly_cnorm, clead_eq_leadingCoeff, normalize_apply,
      Polynomial.coe_normUnit]
    have hlc : (toPoly q).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hq0
    rw [show ((normUnit (toPoly q).leadingCoeff : ℚ) : ℚ) = (toPoly q).leadingCoeff⁻¹ from by
          simp [hlc], toPoly_cnorm, mul_comm]

/-- **The concrete monic gcd realizes the abstract `gcd`** (under gcd-termination): `toPoly (cmonic
(cgcdExt fuel b d).1) = gcd (toPoly b) (toPoly d)`. The computable gcd is `~ gcd (toPoly b) (toPoly d)`
(divides both by `toPoly_cgcdExt_dvd`, greatest by `toPoly_dvd_cgcdExt`); `cmonic` normalizes it, and
`gcd` is already normalized, so the monic associates are equal. -/
theorem toPoly_cmonic_cgcdExt (fuel : ℕ) (b d : CPoly) (hterm : cgcdTerminates fuel b d) :
    toPoly (cmonic (cgcdExt fuel b d).1) = gcd (toPoly b) (toPoly d) := by
  rw [toPoly_cmonic_eq_normalize]
  -- `toPoly (cgcdExt b d).1 ~ gcd (toPoly b) (toPoly d)`, so their normalizations agree.
  obtain ⟨hgb, hgd⟩ := toPoly_cgcdExt_dvd fuel b d hterm
  have hassoc : Associated (toPoly (cgcdExt fuel b d).1) (gcd (toPoly b) (toPoly d)) :=
    associated_of_dvd_dvd (dvd_gcd hgb hgd) (toPoly_dvd_cgcdExt fuel b d (gcd_dvd_left _ _)
      (gcd_dvd_right _ _))
  rw [← normalize_gcd (toPoly b) (toPoly d)]
  exact normalize_eq_normalize_iff.mpr (hassoc.dvd_dvd)

/-! ### The concrete `csqfreeFactor.go` carries the abstract `YunInv` — squarefree emitted factors

Under a per-step **honesty bundle** `GoYun` (gcd-termination, and both `b/q` and `d/q` exact divisions
realized under `toPoly`), the concrete loop `csqfreeFactor.go` maps under `toPoly` onto the abstract
`yunLoopAbs` step: the working pair `(toPoly b, toPoly d)` satisfies `YunInv (toPoly A) i`, the monic
gcd `cmonic (cgcdExt b d).1` realizes `gcd (toPoly b) (toPoly d)`, and `(b', d')` advance the
invariant (`yunStep_preserves`). Hence every (kept) emitted factor is `~ sqfreeFactPart`, so squarefree
(`yunStep_emit_assoc` + `squarefree_of_associated_sqfreeFactPart`). -/

/-- **Per-step honesty bundle** for `csqfreeFactor.go` to realize the abstract Yun step: at each
non-terminal step (`b` non-constant) the gcd terminates, the monic divisor `q = cmonic (cgcdExt b d).1`
divides both `b` and `d` exactly (`toPoly b = toPoly q · toPoly b′`, `toPoly d = toPoly q · toPoly
(d/q)`), and the predicate recurses on `(b′, d′)`. The honest content making the concrete loop a faithful
realization of `yunLoopAbs`. -/
def GoYun (fuel : ℕ) : ℕ → CPoly → CPoly → Prop
  | 0, _, _ => True
  | fo + 1, b, d =>
    if b.length ≤ 1 then True
    else
      let q := cmonic (cgcdExt fuel b d).1
      let b' := cdiv fuel b q
      let d' := csub (cdiv fuel d q) (cderiv b')
      cgcdTerminates fuel b d ∧
        toPoly b = toPoly q * toPoly b' ∧
        toPoly d = toPoly q * toPoly (cdiv fuel d q) ∧
        GoYun fuel fo b' d'

/-! ### The `ℚ`-instance diamond in the concrete bridge — RESOLVED

The concrete↔abstract step correspondence (`csqfreeFactor.go`'s `(b′, d′)` maps to `yunLoopAbs`'s
`(b/gcd, d/gcd − (b/gcd)′)`) is provable per step from `toPoly_cmonic_cgcdExt`, `GoYun`'s exact
divisions, and `toPoly_cderiv`. Carrying the abstract invariant `YunInv (A : ℚ[X]) i …` through the
loop and applying `yunStep_preserves`/`yunStep_emit_assoc` at `ℚ[X]` once appeared blocked by a
**`CommRing ℚ` instance diamond**: the abstract theory (stated over `{K} [Field K]`) derives
`CommRing ℚ` as `Field.toCommRing`, while `csqfreeFactor`/`Babs`/`normalizedFactors` use `ℚ`'s ambient
`Rat.commRing` (with `instDecidableEqRat` rather than `Classical.dec` for the `NormalizedGCDMonoid`).
The two `primPart`/`gcd`/`squarefreePart` instances are *defeq* but not syntactically equal. The
resolution (next sections): the diamond reduces — through `convert`/the `rw`-trick — to two residual
instance equalities, the `CommRing ℚ` halves being `rfl`-defeq and the `NormalizedGCDMonoid ℚ` halves
differing only in a `Subsingleton (DecidableEq ℚ)` argument. This crosses the gap: the ambient-`ℚ` step
bridges (`yunInv_base_rat`/`yunStep_emit_assoc_rat`/`yunStep_preserves_rat`) carry the abstract spine
through the concrete loop (`go_factor_assoc`), yielding the concrete `csqfreeFactor` **squarefree** and
**pairwise-coprime** clauses (`csqfreeFactor_squarefree`/`csqfreeFactor_pairwise_isRelPrime`) under the
engine-honesty bundle `SqfreeYun`. -/

/-! ### Crossing the `ℚ`-instance diamond by `convert`

The wall above is **not** a wall: `convert hX using 2` reduces an abstract-theory hypothesis/conclusion
about `A : ℚ[X]` stated with the field-derived `CommRing`/`NormalizedGCDMonoid` to two residual instance
equalities — the `CommRing ℚ` halves are *defeq* (`rfl`), and the two `NormalizedGCDMonoid ℚ` instances
differ only in their `DecidableEq ℚ` argument (`instDecidableEqRat` vs `Classical.propDecidable`), a
`Subsingleton`. So the abstract Yun spine *does* transfer to the concrete `ℚ`-ambient instances. The
`ratInst%`-tactic below packages the discharge; the `_rat` specializations apply it. -/

open Classical in
/-- Bridge the `ℚ`-instance diamond on a `primPart ≠ 0` hypothesis: the ambient `Rat.commRing`-flavored
`A.primPart ≠ 0` coerces to the `Classical`/`Field.toCommRing`-flavored one the abstract theory expects.
`primPart`, `gcd`, `squarefreePart` over `ℚ` are *defeq* between the two instance paths (the `CommRing`
halves are `rfl`, the `NormalizedGCDMonoid` halves differ only in a `Subsingleton (DecidableEq ℚ)`),
so `convert` closes the gap. -/
theorem primPart_ne_zero_rat (A : ℚ[X]) : A.primPart ≠ 0 := A.primPart_ne_zero

/-- **Every Yun factor is squarefree** over `ℚ` (ambient instances): for `A : ℚ[X]`, `A ≠ 0`, every
member of `yunFactorizationAbs A n` is squarefree. The ambient-instance specialization of
`yunFactorizationAbs_squarefree`, with the `ℚ`-instance diamond discharged by `convert` (the residual
`CommRing ℚ` equality is `rfl`, the `NormalizedGCDMonoid ℚ` one a `Subsingleton (DecidableEq ℚ)`). -/
theorem yunFactorizationAbs_squarefree_rat (A : ℚ[X]) (hA0 : A ≠ 0) (n : ℕ) :
    ∀ V ∈ yunFactorizationAbs A n, Squarefree V := by
  convert yunFactorizationAbs_squarefree A hA0 ?_ n using 2
  convert A.primPart_ne_zero using 2
  · rfl
  · congr 1
    exact Subsingleton.elim _ _

/-- The ambient `NormalizedGCDMonoid ℚ[X]` instance equals the `Classical`-derived one used by the
abstract Yun theory: both are `Polynomial`'s UFD-derived monoid built over `NormalizedGCDMonoid ℚ`, and
the two `NormalizedGCDMonoid ℚ` instances differ only in a `Subsingleton (DecidableEq ℚ)` argument. The
propositional-`Eq` form lets `sqfreeFactPart`/`yunFactorizationAbs` over `ℚ[X]` agree across the diamond
by substitution rather than fragile deep `convert`. -/
theorem sqfreeFactPart_rat_eq (A : ℚ[X]) (i : ℕ) :
    @sqfreeFactPart ℚ Rat.commRing Rat.isDomain _ _ A i
      = @sqfreeFactPart ℚ Rat.instField.toCommRing _ _
          (@CommGroupWithZero.instNormalizedGCDMonoid ℚ Field.toSemifield.toCommGroupWithZero
            (fun a b => Classical.propDecidable (a = b))) A i := by
  have hinst : @CommGroupWithZero.instNormalizedGCDMonoid ℚ Rat.commGroupWithZero instDecidableEqRat
      = @CommGroupWithZero.instNormalizedGCDMonoid ℚ Field.toSemifield.toCommGroupWithZero
          (fun a b => Classical.propDecidable (a = b)) := by
    congr 1
    exact Subsingleton.elim _ _
  rw [show @sqfreeFactPart ℚ Rat.commRing Rat.isDomain _ _ A i
        = @sqfreeFactPart ℚ Rat.commRing Rat.isDomain _
            (@CommGroupWithZero.instNormalizedGCDMonoid ℚ Rat.commGroupWithZero instDecidableEqRat)
            A i from rfl, hinst]

/-- **Factorwise correctness** over `ℚ` (ambient instances): `yunFactorizationAbs A n` is `Forall₂
Associated` to the squarefree-factorization parts `[V₁, …, Vₙ]`. Ambient specialization of
`yunFactorizationAbs_forall₂` through the `convert` instance bridge. -/
theorem yunFactorizationAbs_forall₂_rat (A : ℚ[X]) (hA0 : A ≠ 0) (n : ℕ) :
    List.Forall₂ Associated (yunFactorizationAbs A n)
      ((List.range n).map (fun j => sqfreeFactPart A (1 + j))) := by
  rw [List.map_congr_left fun j _ => sqfreeFactPart_rat_eq A (1 + j)]
  refine yunFactorizationAbs_forall₂ A hA0 ?_ n
  convert A.primPart_ne_zero using 2
  · rfl
  · congr 1
    exact Subsingleton.elim _ _

/-- **Pairwise relative primality** over `ℚ` (ambient instances): distinct-position factors of
`yunFactorizationAbs A n` are `IsRelPrime`. Ambient specialization of
`yunFactorizationAbs_pairwise_isRelPrime` through the `convert` instance bridge. -/
theorem yunFactorizationAbs_pairwise_isRelPrime_rat (A : ℚ[X]) (hA0 : A ≠ 0) (n : ℕ) {p q : ℕ}
    (hpq : p ≠ q) (hp : p < (yunFactorizationAbs A n).length)
    (hq : q < (yunFactorizationAbs A n).length) :
    IsRelPrime ((yunFactorizationAbs A n).get ⟨p, hp⟩) ((yunFactorizationAbs A n).get ⟨q, hq⟩) := by
  convert yunFactorizationAbs_pairwise_isRelPrime A hA0 ?_ n hpq hp hq using 2
  convert A.primPart_ne_zero using 2
  · rfl
  · congr 1
    exact Subsingleton.elim _ _

/-- **The product decomposition** over `ℚ` (ambient instances): the powered product `∏ₖ eₖ^{1+k}` of
the Yun factors is `Associated (∏_{j<n} V_{1+j}^{1+j})`. Ambient specialization of
`yunFactorizationAbs_prodPow_assoc` through the `convert` instance bridge. -/
theorem yunFactorizationAbs_prodPow_assoc_rat (A : ℚ[X]) (hA0 : A ≠ 0) (n : ℕ) :
    Associated (prodPow 1 (yunFactorizationAbs A n))
      (prodPow 1 ((List.range n).map (fun j => sqfreeFactPart A (1 + j)))) := by
  rw [List.map_congr_left fun j _ => sqfreeFactPart_rat_eq A (1 + j)]
  refine yunFactorizationAbs_prodPow_assoc A hA0 ?_ n
  convert A.primPart_ne_zero using 2
  · rfl
  · congr 1
    exact Subsingleton.elim _ _

/-! ### Concrete-loop step bridges: the abstract Yun step over ambient `ℚ` instances

To carry the abstract `YunInv`/`yunStep_*` apparatus through the concrete `csqfreeFactor.go` loop —
whose `toPoly`-image lives in `ℚ[X]` with *ambient* instances — the abstract step lemmas are
specialized to ambient `ℚ`. The recipe (instance-bridge through the `DecidableEq ℚ` subsingleton):
`primPart` discharged by `convert A.primPart_ne_zero using 2`; the `gcd`/`sqfreeFactPart` value-level
diamond rewritten away by `gcd_rat_eq`/`sqfreeFactPart_rat_eq`; the abstract conclusion then closed by
`exact` (whnf-bridging the residual `Babs`/`Dabs` reading inside `YunInv`). -/

/-- The ambient `gcd` over `ℚ[X]` equals the `Classical`-derived one used by the abstract Yun theory:
both are `Polynomial.normalizedGcdMonoid` over `NormalizedGCDMonoid ℚ`, which differ only in a
`Subsingleton (DecidableEq ℚ)` argument. The value-level companion of `sqfreeFactPart_rat_eq`. -/
theorem gcd_rat_eq (a b : ℚ[X]) :
    @gcd ℚ[X] _ (@Polynomial.normalizedGcdMonoid ℚ Rat.commRing _).toGCDMonoid a b
      = @gcd ℚ[X] _ (@Polynomial.normalizedGcdMonoid ℚ Rat.instField.toCommRing
          (@CommGroupWithZero.instNormalizedGCDMonoid ℚ Field.toSemifield.toCommGroupWithZero
            (fun x y => Classical.propDecidable (x = y)))).toGCDMonoid a b := by
  have hinst : @CommGroupWithZero.instNormalizedGCDMonoid ℚ Rat.commGroupWithZero instDecidableEqRat
      = @CommGroupWithZero.instNormalizedGCDMonoid ℚ Field.toSemifield.toCommGroupWithZero
          (fun x y => Classical.propDecidable (x = y)) := by
    congr 1; exact Subsingleton.elim _ _
  rw [show @gcd ℚ[X] _ (@Polynomial.normalizedGcdMonoid ℚ Rat.commRing _).toGCDMonoid a b
        = @gcd ℚ[X] _ (@Polynomial.normalizedGcdMonoid ℚ Rat.commRing
            (@CommGroupWithZero.instNormalizedGCDMonoid ℚ Rat.commGroupWithZero instDecidableEqRat)).toGCDMonoid
          a b from rfl, hinst]

/-- **Yun loop base case** over ambient `ℚ` (`yunInv_base` specialized): `csqfreeFactor`'s
initialization `(A/gcd(A,A′), A′/gcd(A,A′) − …)` satisfies `YunInv A 1 …` with ambient instances. -/
theorem yunInv_base_rat (A : ℚ[X]) (hA0 : A ≠ 0) :
    YunInv A 1 (A / gcd A (derivative A))
      (derivative A / gcd A (derivative A) - derivative (A / gcd A (derivative A))) := by
  have key := yunInv_base A hA0
    (by convert A.primPart_ne_zero using 2 <;> first | rfl | (congr 1; exact Subsingleton.elim _ _))
  rw [gcd_rat_eq A (derivative A)]
  exact key

/-- **Scaled Yun loop base case** over ambient `ℚ`: if the initial pair is a common constant multiple
`(C u·(A/gcd(A,A′)), C u·(A′/gcd) − (C u·(A/gcd))′)` of the monic-gcd initialization (with `u ≠ 0`),
then it satisfies `YunInv A 1` with scalar `u·(leadingCoeff A)`. This absorbs the unit discrepancy when
the concrete `csqfreeFactor` init divides by the *raw* (non-monic) extended-gcd output `g ~ gcd(A,A′)`
rather than the monic gcd: `A/g = C(leadingCoeff g)⁻¹·(A/gcd)`, so `u = (leadingCoeff g)⁻¹`. The shared
scalar `u·(leadingCoeff A)` multiplies both `Babs A 1` and `Dabs A 1`, keeping the subtraction in the
`d`-update consistent. -/
theorem yunInv_base_scaled_rat (A : ℚ[X]) (hA0 : A ≠ 0) (u : ℚ) (hu : u ≠ 0) (b1 d1 : ℚ[X])
    (hb1 : b1 = Polynomial.C u * (A / gcd A (derivative A)))
    (hd1 : d1 = Polynomial.C u * (derivative A / gcd A (derivative A))
              - derivative (Polynomial.C u * (A / gcd A (derivative A)))) :
    YunInv A 1 b1 d1 := by
  obtain ⟨c, hc, hbb, hdd⟩ := yunInv_base_rat A hA0
  rw [hbb] at hb1 hd1
  have hDgcd : derivative A / gcd A (derivative A)
      = Polynomial.C c * Dabs A 1 + derivative (Polynomial.C c * Babs A 1) := by
    rw [← hbb]; exact eq_add_of_sub_eq hdd
  rw [hDgcd] at hd1
  simp only [derivative_C_mul] at hd1
  refine ⟨u * c, mul_ne_zero hu hc, ?_, ?_⟩
  · rw [hb1, map_mul]; ring
  · rw [hd1, map_mul]; ring

/-- **The emitted Yun factor is associated to `Vᵢ`** over ambient `ℚ` (`yunStep_emit_assoc`
specialized): under `YunInv A i b d` (`1 ≤ i`), `gcd b d` is `Associated (sqfreeFactPart A i)`. -/
theorem yunStep_emit_assoc_rat (A : ℚ[X]) (i : ℕ) (hi : 1 ≤ i) (b d : ℚ[X]) (hinv : YunInv A i b d) :
    Associated (gcd b d) (sqfreeFactPart A i) := by
  have key := yunStep_emit_assoc A i hi
    (by convert A.primPart_ne_zero using 2 <;> first | rfl | (congr 1; exact Subsingleton.elim _ _)) hinv
  rw [sqfreeFactPart_rat_eq A i, gcd_rat_eq b d]
  exact key

/-- **One Yun loop step advances the invariant** over ambient `ℚ` (`yunStep_preserves` specialized,
second conjunct): from `YunInv A i b d` (`1 ≤ i`), the deflated pair `(b/gcd, d/gcd − (b/gcd)′)`
satisfies `YunInv A (i+1)`. The invariant carried through the concrete loop. -/
theorem yunStep_preserves_rat (A : ℚ[X]) (i : ℕ) (hi : 1 ≤ i) (b d : ℚ[X]) (hinv : YunInv A i b d) :
    YunInv A (i + 1) (b / gcd b d) (d / gcd b d - derivative (b / gcd b d)) := by
  have key := (yunStep_preserves A i hi
    (by convert A.primPart_ne_zero using 2 <;> first | rfl | (congr 1; exact Subsingleton.elim _ _))
    hinv).2
  rw [gcd_rat_eq b d]
  exact key

/-! ### The concrete `csqfreeFactor.go` loop carries the abstract `YunInv` (factorwise association)

Under the per-step honesty bundle `GoYun` and the loop invariant `YunInv (toPoly A) i`, the concrete
loop `csqfreeFactor.go` maps onto the abstract `yunStep`: each non-terminal step's monic gcd
`q = cmonic (cgcdExt b d).1` realizes `gcd (toPoly b) (toPoly d)` (`toPoly_cmonic_cgcdExt`), the exact
divisions of `GoYun` make the deflated `(b′, d′)` realize `(b/gcd, d/gcd − (b/gcd)′)`, and
`yunStep_preserves_rat` advances `YunInv`. So every *kept* emitted factor `(V, m)` has
`toPoly V ~ sqfreeFactPart (toPoly A) m` (`yunStep_emit_assoc_rat`), with the recorded multiplicity `m`
its abstract index (`i ≤ m`, strictly increasing per recursion). This is the concrete realization that
transfers the abstract squarefree/coprime clauses onto `csqfreeFactor`. -/

/-- `Babs A i ≠ 0` over `ℚ` (`squarefreePart (deflation A (i−1))` is monic, hence nonzero). -/
theorem Babs_ne_zero_rat (A : ℚ[X]) (i : ℕ) : Babs A i ≠ 0 := by
  rw [Babs]
  exact (squarefreePart_deflation_monic A (i - 1)
    (by convert A.primPart_ne_zero using 2 <;>
      first | rfl | (congr 1; exact Subsingleton.elim _ _))).ne_zero

/-- The working numerator of a `YunInv` state is nonzero: `b = C c · Babs A i` with `c ≠ 0` and
`Babs A i ≠ 0`. -/
theorem ne_zero_of_yunInv_rat (A : ℚ[X]) (i : ℕ) (b d : ℚ[X]) (hinv : YunInv A i b d) : b ≠ 0 := by
  obtain ⟨c, hc, hb, _⟩ := hinv
  rw [hb]
  exact mul_ne_zero ((map_ne_zero_iff _ Polynomial.C_injective).mpr hc) (Babs_ne_zero_rat A i)

/-- `b = a / c` from the exact factorization `a = c · b` (`c ≠ 0`). -/
private theorem eq_div_of_eq_mul {a b c : ℚ[X]} (hc : c ≠ 0) (h : a = c * b) : b = a / c := by
  rw [h, mul_div_cancel_left₀ _ hc]

/-- **The concrete Yun loop's kept factors are factorwise associated to the squarefree parts**: under
`GoYun fuel fo b d` and `YunInv (toPoly A) i (toPoly b) (toPoly d)` (`1 ≤ i`), every emitted factor
`(V, m) ∈ csqfreeFactor.go fuel fo b d i` satisfies `toPoly V ~ sqfreeFactPart (toPoly A) m` and
`i ≤ m`. Induction on the fuel counter: each step's monic gcd realizes `gcd (toPoly b) (toPoly d)`
(`toPoly_cmonic_cgcdExt`), `GoYun`'s exact divisions give the deflated pair as `(b/gcd, d/gcd − (b/gcd)′)`,
`yunStep_preserves_rat` advances the invariant, and the head factor is `~ sqfreeFactPart (toPoly A) i`
(`yunStep_emit_assoc_rat`); dropped (unit) factors leave the tail unchanged. -/
theorem go_factor_assoc (fuel : ℕ) (A : CPoly) :
    ∀ (fo : ℕ) (b d : CPoly) (i : ℕ), 1 ≤ i → GoYun fuel fo b d →
      YunInv (toPoly A) i (toPoly b) (toPoly d) →
      ∀ (Vm : CPoly × ℕ), Vm ∈ csqfreeFactor.go fuel fo b d i →
        Associated (toPoly Vm.1) (sqfreeFactPart (toPoly A) Vm.2) ∧ i ≤ Vm.2 := by
  intro fo
  induction fo with
  | zero =>
    intro b d i _ _ _ Vm hVm
    rw [csqfreeFactor.go.eq_def] at hVm; simp at hVm
  | succ fo ih =>
    intro b d i hi hgo hinv Vm hVm
    rw [csqfreeFactor.go.eq_def] at hVm
    by_cases hb : b.length ≤ 1
    · simp only [hb, if_true] at hVm; simp at hVm
    · simp only [hb, if_false] at hVm
      rw [GoYun] at hgo
      simp only [hb, if_false] at hgo
      obtain ⟨hterm, hexb, hexd, hgorest⟩ := hgo
      set q := cmonic (cgcdExt fuel b d).1 with hqdef
      set b' := cdiv fuel b q with hb'def
      set d' := csub (cdiv fuel d q) (cderiv b') with hd'def
      have hgcd : toPoly q = gcd (toPoly b) (toPoly d) := toPoly_cmonic_cgcdExt fuel b d hterm
      have hbne : toPoly b ≠ 0 := ne_zero_of_yunInv_rat (toPoly A) i (toPoly b) (toPoly d) hinv
      have hgcd0 : gcd (toPoly b) (toPoly d) ≠ 0 :=
        fun h => hbne (eq_zero_of_zero_dvd (h ▸ gcd_dvd_left _ _))
      have hbfact : toPoly b = gcd (toPoly b) (toPoly d) * toPoly b' := hgcd ▸ hexb
      have hdfact : toPoly d = gcd (toPoly b) (toPoly d) * toPoly (cdiv fuel d q) := hgcd ▸ hexd
      have hb'eq : toPoly b' = toPoly b / gcd (toPoly b) (toPoly d) := eq_div_of_eq_mul hgcd0 hbfact
      have hd'eq : toPoly d' = toPoly d / gcd (toPoly b) (toPoly d) - derivative (toPoly b') := by
        rw [hd'def, toPoly_csub, toPoly_cderiv]
        congr 1
        exact eq_div_of_eq_mul hgcd0 hdfact
      have hinv' : YunInv (toPoly A) (i + 1) (toPoly b') (toPoly d') := by
        rw [hb'eq, hd'eq, hb'eq]
        exact yunStep_preserves_rat (toPoly A) i hi (toPoly b) (toPoly d) hinv
      have hhead : Associated (toPoly q) (sqfreeFactPart (toPoly A) i) := by
        rw [hgcd]; exact yunStep_emit_assoc_rat (toPoly A) i hi (toPoly b) (toPoly d) hinv
      by_cases hq : q.length ≤ 1
      · simp only [hq, if_true] at hVm
        exact (ih b' d' (i + 1) (by omega) hgorest hinv' Vm hVm).imp id (by omega)
      · simp only [hq, if_false, List.mem_cons] at hVm
        rcases hVm with rfl | hVm
        · exact ⟨hhead, le_refl i⟩
        · exact (ih b' d' (i + 1) (by omega) hgorest hinv' Vm hVm).imp id (by omega)

/-! ### Concrete `csqfreeFactor` Yun correctness: squarefree and pairwise-coprime factors

Bundling the loop correspondence (`go_factor_assoc`) with the start of the loop, every factor `(V, m)`
the concrete `csqfreeFactor fuel D` emits is `Associated (sqfreeFactPart (toPoly D) m)` — squarefree
(`squarefree_of_associated_sqfreeFactPart_rat`), and at distinct list positions (distinct recorded
multiplicities) pairwise relatively prime (`isRelPrime_of_associated_sqfreeFactPart_rat`). The single
hypothesis is the engine-honesty bundle `SqfreeYun fuel D` — the initialization satisfies the loop
invariant `YunInv (toPoly D) 1` and every step is exact (`GoYun`) — the concrete analog of
`SqfreeExact`; on a concrete `D` it reduces to decidable `cmod`-vanishings (cf. `SqfreeExactComp`). This
discharges the two clauses the documented wall blocked: **squarefree** and **pairwise coprime** of the
computable `csqfreeFactor`, transferred from the abstract Yun spine through the `ℚ`-instance bridge. -/

/-- **Associated to a squarefree part ⟹ squarefree** over ambient `ℚ` (`squarefree_of_associated_
sqfreeFactPart` with the `sqfreeFactPart_rat_eq` instance rewrite). -/
theorem squarefree_of_associated_sqfreeFactPart_rat (A : ℚ[X]) (V : ℚ[X]) (j : ℕ)
    (h : Associated V (sqfreeFactPart A j)) : Squarefree V := by
  apply squarefree_of_associated_sqfreeFactPart A j
  rw [← sqfreeFactPart_rat_eq A j]; exact h

/-- **Associated to distinct-multiplicity squarefree parts ⟹ relatively prime** over ambient `ℚ`
(`isRelPrime_of_associated_sqfreeFactPart` with the `sqfreeFactPart_rat_eq` instance rewrites). -/
theorem isRelPrime_of_associated_sqfreeFactPart_rat (A : ℚ[X]) (V W : ℚ[X]) (i j : ℕ) (hij : i ≠ j)
    (hV : Associated V (sqfreeFactPart A i)) (hW : Associated W (sqfreeFactPart A j)) :
    IsRelPrime V W := by
  apply isRelPrime_of_associated_sqfreeFactPart A hij
  · rw [← sqfreeFactPart_rat_eq A i]; exact hV
  · rw [← sqfreeFactPart_rat_eq A j]; exact hW

/-- **Engine-honesty bundle** for `csqfreeFactor fuel D`: the initialization `(b₁, d₁) =
(D/gcd(D,D′), D′/gcd(D,D′) − b₁′)` satisfies the loop invariant `YunInv (toPoly D) 1` and every Yun loop
step is exact (`GoYun`). The concrete analog of `SqfreeExact` for the Yun loop association. The `GoYun`
conjunct is the per-step exact-division content (decidable mirror as in `SqfreeExactComp`); the
`YunInv` start conjunct ties `(b₁, d₁)` to the abstract radical/derivative-poly `Babs`/`Dabs` up to a
shared scalar — constructible by `yunInv_base_scaled_rat` from the init exactness `toPoly D = toPoly g ·
toPoly b₁` (the raw extended-gcd output `g ~ gcd`, absorbing the unit `(leadingCoeff g)⁻¹`). -/
def SqfreeYun (fuel : ℕ) (D : CPoly) : Prop :=
  let p := cnorm D
  let g := (cgcdExt fuel p (cderiv p)).1
  let b1 := cdiv fuel p g
  let d1 := csub (cdiv fuel (cderiv p) g) (cderiv b1)
  YunInv (toPoly D) 1 (toPoly b1) (toPoly d1) ∧ GoYun fuel fuel b1 d1

/-- **Every `csqfreeFactor` factor is associated to a squarefree part**: under `SqfreeYun fuel D`, each
`(V, m) ∈ csqfreeFactor fuel D` has `toPoly V ~ sqfreeFactPart (toPoly D) m` and `1 ≤ m`. From
`go_factor_assoc` started at the loop base. -/
theorem csqfreeFactor_factor_assoc (fuel : ℕ) (D : CPoly) (hex : SqfreeYun fuel D)
    (Vm : CPoly × ℕ) (hVm : Vm ∈ csqfreeFactor fuel D) :
    Associated (toPoly Vm.1) (sqfreeFactPart (toPoly D) Vm.2) ∧ 1 ≤ Vm.2 := by
  rw [SqfreeYun] at hex
  obtain ⟨hinv, hgo⟩ := hex
  rw [csqfreeFactor.eq_def] at hVm
  exact go_factor_assoc fuel D fuel _ _ 1 (le_refl 1) hgo hinv Vm hVm

/-- **Every `csqfreeFactor` factor is squarefree** (concrete Yun correctness, squarefree clause): under
`SqfreeYun fuel D`, `toPoly V` is squarefree for every `(V, m) ∈ csqfreeFactor fuel D`. -/
theorem csqfreeFactor_squarefree (fuel : ℕ) (D : CPoly) (hex : SqfreeYun fuel D)
    (Vm : CPoly × ℕ) (hVm : Vm ∈ csqfreeFactor fuel D) :
    Squarefree (toPoly Vm.1) :=
  squarefree_of_associated_sqfreeFactPart_rat (toPoly D) _ Vm.2
    (csqfreeFactor_factor_assoc fuel D hex Vm hVm).1

/-- The recorded multiplicity of every factor emitted by `csqfreeFactor.go fuel fo b d i` is `≥ i`. -/
theorem go_mult_ge (fuel : ℕ) : ∀ (fo : ℕ) (b d : CPoly) (i : ℕ) (Vm : CPoly × ℕ),
    Vm ∈ csqfreeFactor.go fuel fo b d i → i ≤ Vm.2 := by
  intro fo
  induction fo with
  | zero => intro b d i Vm hVm; rw [csqfreeFactor.go.eq_def] at hVm; simp at hVm
  | succ fo ih =>
    intro b d i Vm hVm
    rw [csqfreeFactor.go.eq_def] at hVm
    by_cases hb : b.length ≤ 1
    · simp only [hb, if_true] at hVm; simp at hVm
    · simp only [hb, if_false] at hVm
      set q := cmonic (cgcdExt fuel b d).1
      set b' := cdiv fuel b q
      set d' := csub (cdiv fuel d q) (cderiv b')
      by_cases hq : q.length ≤ 1
      · simp only [hq, if_true] at hVm
        exact le_trans (Nat.le_succ i) (ih b' d' (i + 1) Vm hVm)
      · simp only [hq, if_false, List.mem_cons] at hVm
        rcases hVm with rfl | hVm
        · exact le_refl i
        · exact le_trans (Nat.le_succ i) (ih b' d' (i + 1) Vm hVm)

/-- **The recorded multiplicities are pairwise distinct** (strictly increasing) across the factors of
`csqfreeFactor.go fuel fo b d i`. Each kept head has multiplicity `i`; every tail factor has
multiplicity `≥ i+1` (`go_mult_ge`), so all differ. -/
theorem go_mult_pairwise (fuel : ℕ) : ∀ (fo : ℕ) (b d : CPoly) (i : ℕ),
    List.Pairwise (fun x y : CPoly × ℕ => x.2 ≠ y.2) (csqfreeFactor.go fuel fo b d i) := by
  intro fo
  induction fo with
  | zero => intro b d i; rw [csqfreeFactor.go.eq_def]; simp
  | succ fo ih =>
    intro b d i
    rw [csqfreeFactor.go.eq_def]
    by_cases hb : b.length ≤ 1
    · simp only [hb, if_true]; simp
    · simp only [hb, if_false]
      set q := cmonic (cgcdExt fuel b d).1
      set b' := cdiv fuel b q
      set d' := csub (cdiv fuel d q) (cderiv b')
      by_cases hq : q.length ≤ 1
      · simp only [hq, if_true]; exact ih b' d' (i + 1)
      · simp only [hq, if_false, List.pairwise_cons]
        refine ⟨fun Vm hVm => ?_, ih b' d' (i + 1)⟩
        have := go_mult_ge fuel fo b' d' (i + 1) Vm hVm
        omega

/-- **The `csqfreeFactor` factors have pairwise-distinct multiplicities**. -/
theorem csqfreeFactor_mult_pairwise (fuel : ℕ) (D : CPoly) :
    List.Pairwise (fun x y : CPoly × ℕ => x.2 ≠ y.2) (csqfreeFactor fuel D) := by
  rw [csqfreeFactor.eq_def]; exact go_mult_pairwise fuel fuel _ _ 1

/-- **The `csqfreeFactor` factors are pairwise relatively prime** (concrete Yun correctness, coprimality
clause): under `SqfreeYun fuel D`, factors at distinct list positions `p ≠ q` of `csqfreeFactor fuel D`
have `IsRelPrime (toPoly Vₚ) (toPoly V_q)`. Distinct positions carry distinct recorded multiplicities
(`csqfreeFactor_mult_pairwise`), and each factor is `~ sqfreeFactPart (toPoly D)` at its multiplicity, so
`isRelPrime_of_associated_sqfreeFactPart_rat` applies. -/
theorem csqfreeFactor_pairwise_isRelPrime (fuel : ℕ) (D : CPoly) (hex : SqfreeYun fuel D)
    (p q : ℕ) (hpq : p ≠ q) (hp : p < (csqfreeFactor fuel D).length)
    (hq : q < (csqfreeFactor fuel D).length) :
    IsRelPrime (toPoly ((csqfreeFactor fuel D).get ⟨p, hp⟩).1)
      (toPoly ((csqfreeFactor fuel D).get ⟨q, hq⟩).1) := by
  have hpw := csqfreeFactor_mult_pairwise fuel D
  have hmne : ((csqfreeFactor fuel D).get ⟨p, hp⟩).2 ≠ ((csqfreeFactor fuel D).get ⟨q, hq⟩).2 := by
    rcases lt_or_gt_of_ne hpq with h | h
    · exact List.pairwise_iff_get.mp hpw ⟨p, hp⟩ ⟨q, hq⟩ h
    · exact (List.pairwise_iff_get.mp hpw ⟨q, hq⟩ ⟨p, hp⟩ h).symm
  exact isRelPrime_of_associated_sqfreeFactPart_rat (toPoly D) _ _ _ _ hmne
    (csqfreeFactor_factor_assoc fuel D hex _ ((csqfreeFactor fuel D).get_mem _)).1
    (csqfreeFactor_factor_assoc fuel D hex _ ((csqfreeFactor fuel D).get_mem _)).1

/-! ### Restatements against the intended Yun-correctness wording -/

open Classical in
-- Yun factorization, factor identification (Geddes–Czapor–Labahn §8.2 / Bronstein §1.7): the `n`-step
-- abstract Yun loop on `A` produces, factor-by-factor, the squarefree-factorization parts `Vⱼ` of `A`.
example {K : Type*} [Field K] [CharZero K] (A : K[X]) (hA0 : A ≠ 0) (hA : A.primPart ≠ 0) (n : ℕ) :
    List.Forall₂ Associated (yunFactorizationAbs A n)
      ((List.range n).map (fun j => sqfreeFactPart A (1 + j))) :=
  yunFactorizationAbs_forall₂ A hA0 hA n

open Classical in
-- Yun correctness, squarefreeness clause: every factor the loop produces is squarefree.
example {K : Type*} [Field K] [CharZero K] (A : K[X]) (hA0 : A ≠ 0) (hA : A.primPart ≠ 0) (n : ℕ) :
    ∀ V ∈ yunFactorizationAbs A n, Squarefree V :=
  yunFactorizationAbs_squarefree A hA0 hA n

open Classical in
-- Yun correctness, coprimality clause: factors at distinct positions are relatively prime.
example {K : Type*} [Field K] [CharZero K] (A : K[X]) (hA0 : A ≠ 0) (hA : A.primPart ≠ 0) (n : ℕ)
    {p q : ℕ} (hpq : p ≠ q) (hp : p < (yunFactorizationAbs A n).length)
    (hq : q < (yunFactorizationAbs A n).length) :
    IsRelPrime ((yunFactorizationAbs A n).get ⟨p, hp⟩) ((yunFactorizationAbs A n).get ⟨q, hq⟩) :=
  yunFactorizationAbs_pairwise_isRelPrime A hA0 hA n hpq hp hq

open Classical in
-- Yun correctness, decomposition clause: the powered product of the factors `∏ₖ eₖ^{1+k}` is, up to
-- associates, `∏ⱼ Vⱼ^iⱼ` — the squarefree factorization of `A`.
example {K : Type*} [Field K] [CharZero K] (A : K[X]) (hA0 : A ≠ 0) (hA : A.primPart ≠ 0) (n : ℕ) :
    Associated (prodPow 1 (yunFactorizationAbs A n))
      (prodPow 1 ((List.range n).map (fun j => sqfreeFactPart A (1 + j)))) :=
  yunFactorizationAbs_prodPow_assoc A hA0 hA n

-- Concrete Yun correctness (squarefree clause): every factor the computable `csqfreeFactor` emits is
-- squarefree, under the engine-honesty bundle `SqfreeYun`.
example (fuel : ℕ) (D : CPoly) (hex : SqfreeYun fuel D)
    (Vm : CPoly × ℕ) (hVm : Vm ∈ csqfreeFactor fuel D) :
    Squarefree (toPoly Vm.1) :=
  csqfreeFactor_squarefree fuel D hex Vm hVm

-- Concrete Yun correctness (coprimality clause): factors of `csqfreeFactor` at distinct positions are
-- relatively prime, under `SqfreeYun`.
example (fuel : ℕ) (D : CPoly) (hex : SqfreeYun fuel D)
    (p q : ℕ) (hpq : p ≠ q) (hp : p < (csqfreeFactor fuel D).length)
    (hq : q < (csqfreeFactor fuel D).length) :
    IsRelPrime (toPoly ((csqfreeFactor fuel D).get ⟨p, hp⟩).1)
      (toPoly ((csqfreeFactor fuel D).get ⟨q, hq⟩).1) :=
  csqfreeFactor_pairwise_isRelPrime fuel D hex p q hpq hp hq

/-! ### Toward the UNCONDITIONAL `hermiteReduce` wrapper (no exact-division certificate)

`hermiteReduce_residual_correct_of_dvd` still assumes the cleared-identity divisibility
`toPoly (D·gden²) ∣ toPoly (resNum·Dstar)`. The remaining work removes that hypothesis: the
divisibility is a *consequence* of `A/D − g′` genuinely having denominator `Dstar`, which is the
loop correctness of the per-factor `hermiteInner` reductions glued through `hermiteReduce`'s `g`-fold.

The engine reduces the **global** fraction `A/D` once per repeated factor `(Vᵢ, iᵢ)`: with
`U = D/Vᵢ^{iᵢ}` (exact, since `Vᵢ^{iᵢ} ∣ D`), `hermiteInner_spec_of` gives
`am A/am D = (toQFun glocᵢ)′ + am A_finalᵢ/(am U·am Vᵢ)`, i.e. the residual fraction
`am A/am D − (toQFun glocᵢ)′` has denominator `am U·am Vᵢ = am (D/Vᵢ^{iᵢ−1})`, whose squarefree
*radical* is dominated by `Dstar`. The composition tracks these per-factor residuals through the fold. -/

/-- **Exact reading of the global denominator** through a factor power: if `cmod fuel D Vpow` reads to
`0` (i.e. `Vpow ∣ D` exactly) and `Vpow ≠ 0`, then `am D = am (cdiv fuel D Vpow) · am Vpow` in
`RatFunc ℚ`. This is the certificate making `hermiteInner`'s global denominator `U·Vᵢ^{iᵢ}` equal to
`D` (so each factor's inner loop reduces the genuine `A/D`). -/
theorem am_D_eq_cdiv_mul (fuel : ℕ) (D Vpow : CPoly) (hVpow : cnorm Vpow ≠ [])
    (hrem : toPoly (cmod fuel D Vpow) = 0) :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
      = algebraMap ℚ[X] (RatFunc ℚ) (toPoly (cdiv fuel D Vpow))
        * algebraMap ℚ[X] (RatFunc ℚ) (toPoly Vpow) := by
  rw [← map_mul, toPoly_cdiv_of_cmod_zero fuel D Vpow hVpow hrem]

/-! ### The single-repeated-factor wrapper: `U·V` is the radical `Dstar`

When `D` has a **single** repeated factor `(V, m)` (every other irreducible factor of `D` is simple),
the `hermiteReduce` `g`-fold reduces to the *one* `hermiteInner` term `g = gloc`, and the global
denominator `U·V^m = D` deflates to `U·V = Dstar` exactly (the radical: `V` at power `1`, every other
factor already simple). Then `hermiteInner_spec_of`'s residual identity `A/(U·V^m) = gloc′ +
Afinal/(U·V)` is *directly* the wrapper conclusion `A/D = gloc′ + Afinal/Dstar`, with **no** divisibility
certificate — the residual denominator is already `Dstar`. This is the fully-unconditional wrapper for the
single-repeated-factor shape (the abstract composition is below; the general multi-factor `g`-fold needs
the per-factor interference clearing, recorded in `## NOT YET FORMALIZED`). -/

open scoped Differential in
/-- **Single-repeated-factor wrapper correctness** in `RatFunc ℚ`: for one repeated factor `(V, j+1)`
with `U = D/V^{j+1}` (so `am D = am U · am V^{j+1}`) and `Dstar = U·V` the radical (`am Dstar =
am U · am V`), the `hermiteInner` reduction of the global `A/D` is *directly* the wrapper:
`am A/am D = (toQFun gloc)′ + am Afinal/am Dstar`, where `(gloc, Afinal) = hermiteInner fuel V U j A
qzero`. No divisibility certificate — the residual denominator `U·V` is already the radical. The single
`hermiteInner` term of the `g`-fold when `D` has exactly one repeated factor; composes
`hermiteInner_spec_of` with the two denominator reconciliations. -/
theorem hermiteReduce_residual_correct_single (fuel : ℕ) (V U A Dstar D : CPoly)
    (hU : toPoly U ≠ 0) (hV : toPoly V ≠ 0)
    (hq : cnorm V ≠ [])
    (hg : toPoly (cgcdExt fuel (cmul U (cderiv V)) V).1
      = Polynomial.C (clead (cgcdExt fuel (cmul U (cderiv V)) V).1))
    (hgc : clead (cgcdExt fuel (cmul U (cderiv V)) V).1 ≠ 0) (j : ℕ)
    (hD : algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
      = algebraMap ℚ[X] (RatFunc ℚ) (toPoly U) * algebraMap ℚ[X] (RatFunc ℚ) (toPoly V) ^ (j + 1))
    (hDstar : algebraMap ℚ[X] (RatFunc ℚ) (toPoly Dstar)
      = algebraMap ℚ[X] (RatFunc ℚ) (toPoly U) * algebraMap ℚ[X] (RatFunc ℚ) (toPoly V)) :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
      = (toQFun (hermiteInner fuel V U j A qzero).1)′
        + algebraMap ℚ[X] (RatFunc ℚ) (toPoly (hermiteInner fuel V U j A qzero).2)
          / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Dstar) := by
  rw [hD, hDstar]
  exact hermiteInner_spec_of fuel V U hU hV hq hg hgc j A

/-! ### Reducing the cleared-identity divisibility to two structural divisibilities

The monolithic premise of `hermiteReduce_residual_correct_of_dvd` is `D·gden² ∣ resNum'·Dstar` (with
`resNum' = A·gden² − D·gprimeNum`, the un-`Dstar`'d residual numerator). The genuine loop content
factors this into two *cleaner* divisibilities, each a `cmod`-vanishing the engine can `native_decide`:

* **`D ∣ resNum'`** — the global denominator `D` divides the residual numerator (equivalently
  `D ∣ A·gden²`, since `D ∣ D·gprimeNum` trivially). Writing `resNum' = D·M`,
* **`gden² ∣ M·Dstar`** with `M = resNum'/D` — what remains after cancelling `D`.

Then `D·gden² ∣ resNum'·Dstar` since `resNum'·Dstar = D·(M·Dstar)` and `gden² ∣ M·Dstar`. This is the
algebraic skeleton of "`A/D − g′` clears to denominator `Dstar`": the first divisibility says the global
fraction's numerator reduces, the second that the leftover `gden²` cancels against `M·Dstar`. -/

/-- **The cleared-identity divisibility from two cleaner ones** (`ℚ[X]` level): if `D ∣ R` (so
`R = D·M`) and `gd2 ∣ M·S`, then `D·gd2 ∣ R·S`. The algebraic reduction of
`hermiteReduce_residual_correct_of_dvd`'s monolithic premise to the loop's two structural
divisibilities (`D ∣ resNum'`, `gden² ∣ (resNum'/D)·Dstar`). -/
theorem dvd_clearedIdentity_of_split {R D gd2 S : ℚ[X]} (hD : D ≠ 0)
    (hDR : D ∣ R) (hgd : gd2 ∣ (R / D) * S) :
    D * gd2 ∣ R * S := by
  obtain ⟨M, hM⟩ := hDR
  have hMeq : R / D = M := by rw [hM, mul_div_cancel_left₀ _ hD]
  rw [hMeq] at hgd
  obtain ⟨N, hN⟩ := hgd
  exact ⟨N, by rw [hM]; linear_combination D * hN⟩

/-- **The cleared-identity divisibility from `Dstar ∣ D` plus one cleaner divisibility** (`ℚ[X]`
level): if `S ∣ D` (so `D = S·W`, the radical clause `Dstar ∣ D`) and `W·gd2 ∣ R` (the single residual
cert), then `D·gd2 ∣ R·S`. Cancelling the common `S`: `D·gd2 = S·(W·gd2)` and `R·S = S·R`, so the
claim is `W·gd2 ∣ R`. Folds the **proven** radical-divides fact (`toPoly_Dstar_dvd_D`) into the
divisibility, leaving a *single* `cmod`-cert `(D/Dstar)·gden² ∣ resNum'` to discharge. -/
theorem dvd_clearedIdentity_of_radical {R D gd2 S W : ℚ[X]}
    (hSD : D = S * W) (hWgd : W * gd2 ∣ R) :
    D * gd2 ∣ R * S := by
  obtain ⟨N, hN⟩ := hWgd
  exact ⟨N, by rw [hSD]; linear_combination S * hN⟩

/-- **Divisibility from a vanishing `cmod` remainder**: if `cmod fuel p q` reads to `0` and `q ≠ 0`
(`cnorm q ≠ []`), then `toPoly q ∣ toPoly p`. The honest-division reading of an exact computable
remainder (`toPoly_cdiv_of_cmod_zero`). -/
theorem toPoly_dvd_of_cmod_zero (fuel : ℕ) (p q : CPoly) (hq : cnorm q ≠ [])
    (hrem : toPoly (cmod fuel p q) = 0) :
    toPoly q ∣ toPoly p :=
  ⟨toPoly (cdiv fuel p q), by rw [toPoly_cdiv_of_cmod_zero fuel p q hq hrem, mul_comm]⟩

open scoped Differential in
/-- **`hermiteReduce` wrapper correctness from the two split divisibility certificates** in `RatFunc ℚ`:
the cleared-identity premise factored into the loop's two structural `cmod`-vanishings —
`hresD : D ∣ resNum'` (the global denominator divides the residual numerator `resNum' = A·gden² −
D·gprimeNum`) and `hg2 : gden² ∣ (resNum'/D)·Dstar` (what remains after cancelling `D`) — under
`D, gden ≠ 0`, `Dstar ≠ 0`, and a fuel bound. Concludes
`am A/am D = (toQFun (gnum,gden))′ + am Bres/am Dstar`. These two certificates are the genuine
loop content (`A/D − g′` clears to denominator `Dstar`), each decidably `cmod`-checkable on a
concrete `D` — strictly cleaner than the monolithic `hermiteReduce_residual_correct_of_dvd`
premise, which they assemble via `dvd_clearedIdentity_of_split`. -/
theorem hermiteReduce_residual_correct_of_split (fuel : ℕ) (A D gnum gden Dstar : CPoly)
    (hD : toPoly D ≠ 0) (hgden : toPoly gden ≠ 0) (hDstar : cnorm Dstar ≠ [])
    (hfuel : (cnorm (cmul (csub (cmul A (cmul gden gden))
        (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))) Dstar)).length ≤ fuel)
    (hresD : toPoly (cmod fuel
        (csub (cmul A (cmul gden gden))
          (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))) D) = 0)
    (hg2 : toPoly (cmod fuel
        (cmul (cdiv fuel
            (csub (cmul A (cmul gden gden))
              (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))) D) Dstar)
        (cmul gden gden)) = 0) :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
      = (toQFun (gnum, gden))′
        + algebraMap ℚ[X] (RatFunc ℚ)
            (toPoly (cdiv fuel
              (cmul (csub (cmul A (cmul gden gden))
                  (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))) Dstar)
              (cmul D (cmul gden gden))))
          / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Dstar) := by
  set resNum' := csub (cmul A (cmul gden gden))
    (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden)))) with hresNum'
  -- nonzero divisors as `cnorm ≠ []`.
  have hDne : cnorm D ≠ [] := fun h => hD ((cnorm_eq_nil_iff D).mp h)
  have hgden2 : toPoly (cmul gden gden) ≠ 0 := by rw [toPoly_cmul]; exact mul_ne_zero hgden hgden
  have hgden2ne : cnorm (cmul gden gden) ≠ [] := fun h => hgden2 ((cnorm_eq_nil_iff _).mp h)
  -- cert 1: `D ∣ resNum'`.
  have hDR : toPoly D ∣ toPoly resNum' := toPoly_dvd_of_cmod_zero fuel resNum' D hDne hresD
  -- cert 2: `gden² ∣ (cdiv resNum' D)·Dstar`, and `toPoly (cdiv resNum' D) = resNum'/D`.
  have hMeq : toPoly (cdiv fuel resNum' D) = toPoly resNum' / toPoly D := by
    rw [toPoly_cdiv_of_cmod_zero fuel resNum' D hDne hresD, mul_div_cancel_right₀ _ hD]
  have hg2dvd : toPoly (cmul gden gden) ∣ toPoly (cmul (cdiv fuel resNum' D) Dstar) :=
    toPoly_dvd_of_cmod_zero fuel _ _ hgden2ne hg2
  rw [toPoly_cmul, toPoly_cmul, hMeq] at hg2dvd
  -- assemble the monolithic divisibility via the split lemma.
  have hdvd : toPoly (cmul D (cmul gden gden)) ∣ toPoly (cmul resNum' Dstar) := by
    rw [toPoly_cmul, toPoly_cmul, toPoly_cmul]
    exact dvd_clearedIdentity_of_split hD hDR hg2dvd
  exact hermiteReduce_residual_correct_of_dvd fuel A D gnum gden Dstar hD hgden hDstar hfuel hdvd

open scoped Differential in
/-- **`hermiteReduce` wrapper correctness from the radical clause plus one cert** in `RatFunc ℚ`: the
cleared-identity premise reduced using the **proven** radical-divides fact `Dstar ∣ D`
(`hDstarD`, from `toPoly_Dstar_dvd_D`/`SqfreeYun` when `Dstar` is the computed radical). With
`W = D/Dstar`, the single residual cert `hWgd : W·gden² ∣ resNum'` (a `cmod`-vanishing) then suffices.
Under `D, gden ≠ 0`, `Dstar ≠ 0` and a fuel bound, `am A/am D = (toQFun (gnum,gden))′ + am Bres/am
Dstar`. This is the cleanest divisibility input: the *abstract* radical content folded in, leaving one
decidable cert. -/
theorem hermiteReduce_residual_correct_of_radical (fuel : ℕ) (A D gnum gden Dstar : CPoly)
    (hD : toPoly D ≠ 0) (hgden : toPoly gden ≠ 0) (hDstar : cnorm Dstar ≠ [])
    (hfuel : (cnorm (cmul (csub (cmul A (cmul gden gden))
        (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))) Dstar)).length ≤ fuel)
    (hfuelD : (cnorm D).length ≤ fuel)
    (hDstarD : toPoly Dstar ∣ toPoly D)
    (hWgd : toPoly (cmod fuel
        (csub (cmul A (cmul gden gden))
          (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden)))))
        (cmul (cdiv fuel D Dstar) (cmul gden gden))) = 0) :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
      = (toQFun (gnum, gden))′
        + algebraMap ℚ[X] (RatFunc ℚ)
            (toPoly (cdiv fuel
              (cmul (csub (cmul A (cmul gden gden))
                  (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))) Dstar)
              (cmul D (cmul gden gden))))
          / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Dstar) := by
  set resNum' := csub (cmul A (cmul gden gden))
    (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden)))) with hresNum'
  have hWeq : toPoly D = toPoly Dstar * toPoly (cdiv fuel D Dstar) := by
    have hrem : toPoly (cmod fuel D Dstar) = 0 := cmod_eq_zero_of_dvd fuel D Dstar hDstar hfuelD hDstarD
    rw [toPoly_cdiv_of_cmod_zero fuel D Dstar hDstar hrem, mul_comm]
  -- the single residual cert: `(cdiv D Dstar)·gden² ∣ resNum'`.
  have hWgdne : cnorm (cmul (cdiv fuel D Dstar) (cmul gden gden)) ≠ [] := by
    intro h
    have h0 : toPoly (cmul (cdiv fuel D Dstar) (cmul gden gden)) = 0 := (cnorm_eq_nil_iff _).mp h
    rw [toPoly_cmul, toPoly_cmul] at h0
    rcases mul_eq_zero.mp h0 with h1 | h2
    · rw [hWeq, h1, mul_zero] at hD; exact hD rfl
    · rcases mul_eq_zero.mp h2 with hh | hh <;> exact hgden hh
  have hWgddvd : toPoly (cmul (cdiv fuel D Dstar) (cmul gden gden)) ∣ toPoly resNum' :=
    toPoly_dvd_of_cmod_zero fuel _ _ hWgdne hWgd
  rw [toPoly_cmul, toPoly_cmul] at hWgddvd
  -- assemble the monolithic divisibility through the radical reduction.
  have hdvd : toPoly (cmul D (cmul gden gden)) ∣ toPoly (cmul resNum' Dstar) := by
    rw [toPoly_cmul, toPoly_cmul, toPoly_cmul]
    exact dvd_clearedIdentity_of_radical (W := toPoly (cdiv fuel D Dstar)) hWeq hWgddvd
  exact hermiteReduce_residual_correct_of_dvd fuel A D gnum gden Dstar hD hgden hDstar hfuel hdvd

/-! ### The decidable residual-honesty bundle and the unconditional wrapper

The split certificates of `hermiteReduce_residual_correct_of_split` are two `cmod`-vanishings — a
**decidable** condition `HermiteResComp` (the residual-recovery analog of `SqfreeExactComp` for the Yun
loop). Bundling it with `D, gden, Dstar ≠ 0` and a fuel bound, the wrapper conclusion holds with **no**
exact-division certificate as a hypothesis: the certificate is *computed and checked* by the engine.
On a concrete `D` this is `native_decide`-discharged (Example 2.2.1 below). The remaining theoretical
gap — proving `HermiteResComp` from `SqfreeYun` *abstractly* — is the global-`A` `hermiteReduce`
`g`-fold composition (each repeated factor reduces the full `A/D`; the residuals' multi-factor
interference clearing to denominator `Dstar` is the genuine loop-correctness content, decidably true
per example, abstractly open). -/

/-- **Decidable residual-recovery honesty bundle** for `hermiteReduce`'s computed rational part
`(gnum, gden)` and radical `Dstar`: the two split `cmod`-remainders vanish — `D ∣ resNum'` and
`gden² ∣ (resNum'/D)·Dstar`, with `resNum' = A·gden² − D·(gnum'·gden − gnum·gden')`. Decidable
(`cnorm … = []` checks), hence `native_decide`-checkable; implies the divisibility certificate
`hermiteReduce_residual_correct_of_split` consumes. -/
def HermiteResComp (fuel : ℕ) (A D gnum gden Dstar : CPoly) : Prop :=
  let resNum' := csub (cmul A (cmul gden gden))
    (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))
  cnorm (cmod fuel resNum' D) = [] ∧
    cnorm (cmod fuel (cmul (cdiv fuel resNum' D) Dstar) (cmul gden gden)) = []

/-- `HermiteResComp` is decidable (both conjuncts are `cnorm … = []` equality checks). -/
instance decHermiteResComp (fuel : ℕ) (A D gnum gden Dstar : CPoly) :
    Decidable (HermiteResComp fuel A D gnum gden Dstar) := by
  unfold HermiteResComp; infer_instance

open scoped Differential in
/-- **Unconditional `hermiteReduce` wrapper correctness** in `RatFunc ℚ` (no exact-division certificate
as a hypothesis): from the *decidable* residual-honesty bundle `HermiteResComp fuel A D gnum gden Dstar`
(the two split `cmod`-vanishings, computed and checked by the engine) plus `D, gden ≠ 0`, `Dstar ≠ 0`
and a fuel bound, `am A/am D = (toQFun (gnum,gden))′ + am Bres/am Dstar` with
`Bres = cdiv fuel (resNum'·Dstar) (D·gden²)`. I.e. `∫ A/D = gnum/gden + ∫ Bres/Dstar`. The honest
`RatFunc ℚ` correctness of the computable Hermite reduction with the certificate discharged from the
engine's own decidable `cmod`-computations (`HermiteResComp_to_split`), rather than supplied as an
algebraic divisibility hypothesis. -/
theorem hermiteReduce_residual_correct_uncond (fuel : ℕ) (A D gnum gden Dstar : CPoly)
    (hD : toPoly D ≠ 0) (hgden : toPoly gden ≠ 0) (hDstar : cnorm Dstar ≠ [])
    (hfuel : (cnorm (cmul (csub (cmul A (cmul gden gden))
        (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))) Dstar)).length ≤ fuel)
    (hcomp : HermiteResComp fuel A D gnum gden Dstar) :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
      = (toQFun (gnum, gden))′
        + algebraMap ℚ[X] (RatFunc ℚ)
            (toPoly (cdiv fuel
              (cmul (csub (cmul A (cmul gden gden))
                  (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))) Dstar)
              (cmul D (cmul gden gden))))
          / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Dstar) := by
  obtain ⟨hresD, hg2⟩ := hcomp
  rw [cnorm_eq_nil_iff] at hresD hg2
  exact hermiteReduce_residual_correct_of_split fuel A D gnum gden Dstar hD hgden hDstar hfuel
    hresD hg2

/-! ### Example 2.2.1: the unconditional wrapper, certificate `native_decide`d

The decidable residual-honesty bundle `HermiteResComp` holds on Example 2.2.1 (`native_decide`), so the
**unconditional** wrapper applies with *no* exact-division hypothesis supplied: the certificate is the
engine's own `cmod`-computation, checked by `native_decide`. This is the honest `RatFunc ℚ` correctness
of the computed Hermite reduction for `f = (x⁷−24x⁴−4x²+8x−8)/(x⁸+6x⁶+12x⁴+8x²)` with the certificate
fully internal. -/

/-- **Example 2.2.1: the residual-honesty bundle holds** (`native_decide`): both split `cmod`-remainders
of the computed `(gnum, gden, Dstar) = ([8,12,20,12,8,3], [0,8,0,12,0,6,0,1], [0,2,0,1])` vanish, so
`HermiteResComp 40 cA221 cD221 gnum gden Dstar` — the engine certifies its own residual recovery. -/
theorem hermite_ex221_resComp :
    HermiteResComp 40 cA221 cD221 [8, 12, 20, 12, 8, 3] [0, 8, 0, 12, 0, 6, 0, 1] [0, 2, 0, 1] := by
  native_decide

open scoped Differential in
/-- **Example 2.2.1: the unconditional Hermite reduction is correct as a `RatFunc ℚ` identity** (§2.2,
p.41): `am A/am D = (toQFun (gnum,gden))′ + am Bres/am Dstar` for the computed `gnum, gden, Dstar` of
Example 2.2.1, with **no** exact-division certificate as a hypothesis — the certificate is discharged by
the `native_decide`'d residual-honesty bundle `hermite_ex221_resComp` through
`hermiteReduce_residual_correct_uncond`. The nonzero hypotheses hold by `decide`; the fuel bound by
`native_decide`. -/
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
  have hfuel : (cnorm (cmul (csub (cmul cA221 (cmul [0, 8, 0, 12, 0, 6, 0, 1] [0, 8, 0, 12, 0, 6, 0, 1]))
      (cmul cD221 (csub (cmul (cderiv [8, 12, 20, 12, 8, 3]) [0, 8, 0, 12, 0, 6, 0, 1])
        (cmul [8, 12, 20, 12, 8, 3] (cderiv [0, 8, 0, 12, 0, 6, 0, 1]))))) [0, 2, 0, 1])).length ≤ 40 := by
    native_decide
  exact hermiteReduce_residual_correct_uncond 40 cA221 cD221 [8, 12, 20, 12, 8, 3]
    [0, 8, 0, 12, 0, 6, 0, 1] [0, 2, 0, 1] hD hgden hDstar hfuel hermite_ex221_resComp

open scoped Differential in
-- Hermite reduction (Bronstein §2.2/§2.5): `∫ A/D = g + ∫ Bres/Dstar` with `g = gnum/gden` the
-- rational part and `Bres/Dstar` the residual (squarefree-denominator) integrand — the computable
-- `hermiteReduce`'s output, certified in `RatFunc ℚ` from only the decidable residual-honesty bundle
-- (no exact-division hypothesis).
example (fuel : ℕ) (A D gnum gden Dstar : CPoly)
    (hD : toPoly D ≠ 0) (hgden : toPoly gden ≠ 0) (hDstar : cnorm Dstar ≠ [])
    (hfuel : (cnorm (cmul (csub (cmul A (cmul gden gden))
        (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))) Dstar)).length ≤ fuel)
    (hcomp : HermiteResComp fuel A D gnum gden Dstar) :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
      = (toQFun (gnum, gden))′
        + algebraMap ℚ[X] (RatFunc ℚ)
            (toPoly (cdiv fuel
              (cmul (csub (cmul A (cmul gden gden))
                  (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))) Dstar)
              (cmul D (cmul gden gden))))
          / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Dstar) :=
  hermiteReduce_residual_correct_uncond fuel A D gnum gden Dstar hD hgden hDstar hfuel hcomp

/-! ### Example 2.2.1 via the radical wrapper: `Dstar ∣ D` from the proven Yun radical clause

The radical wrapper `hermiteReduce_residual_correct_of_radical` consumes `Dstar ∣ D` as a hypothesis,
which for Example 2.2.1 is discharged not by `native_decide` but by the **proven** Yun radical-divides
theorem `toPoly_Dstar_dvd_D` (through the `native_decide`'d honesty bundle `hermite_ex221_sqfreeExactComp`),
transported to the literal radical `[0,2,0,1]` by the computed fold equality. Only the *single* residual
cert remains `native_decide`'d — the abstract radical content is genuinely proven. -/

/-- **Example 2.2.1: the radical `[0,2,0,1]` divides `D`** with the *proven* Yun radical clause: the
computed radical `Dstar = x³+2x` (the `csqfreeFactor 40 cD221` fold) divides `D`, transported to the
literal `[0,2,0,1]` (`native_decide` fold-equality + `toPoly_Dstar_dvd_D`). -/
theorem hermite_ex221_Dstar_dvd : toPoly [0, 2, 0, 1] ∣ toPoly cD221 := by
  have hfold : ((csqfreeFactor 40 cD221).foldl (fun acc (vi : CPoly × ℕ) => cmul acc vi.1) [1])
      = [0, 2, 0, 1] := by native_decide
  have := toPoly_Dstar_dvd_D 40 cD221
    (SqfreeExactComp_to_SqfreeExact 40 cD221 hermite_ex221_sqfreeExactComp)
  rwa [hfold] at this

open scoped Differential in
/-- **Example 2.2.1: the unconditional Hermite reduction via the radical wrapper** (§2.2, p.41):
`am A/am D = (toQFun (gnum,gden))′ + am Bres/am Dstar` with the radical clause `Dstar ∣ D` discharged
by the *proven* `hermite_ex221_Dstar_dvd` (Yun radical-divides), and only the single residual cert
`native_decide`'d. The cleanest split — abstract radical content proven, one residual cert checked. -/
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
  have hfuel : (cnorm (cmul (csub (cmul cA221 (cmul [0, 8, 0, 12, 0, 6, 0, 1] [0, 8, 0, 12, 0, 6, 0, 1]))
      (cmul cD221 (csub (cmul (cderiv [8, 12, 20, 12, 8, 3]) [0, 8, 0, 12, 0, 6, 0, 1])
        (cmul [8, 12, 20, 12, 8, 3] (cderiv [0, 8, 0, 12, 0, 6, 0, 1]))))) [0, 2, 0, 1])).length ≤ 40 := by
    native_decide
  have hfuelD : (cnorm cD221).length ≤ 40 := by decide
  have hWgd : toPoly (cmod 40
      (csub (cmul cA221 (cmul [0, 8, 0, 12, 0, 6, 0, 1] [0, 8, 0, 12, 0, 6, 0, 1]))
        (cmul cD221 (csub (cmul (cderiv [8, 12, 20, 12, 8, 3]) [0, 8, 0, 12, 0, 6, 0, 1])
          (cmul [8, 12, 20, 12, 8, 3] (cderiv [0, 8, 0, 12, 0, 6, 0, 1])))))
      (cmul (cdiv 40 cD221 [0, 2, 0, 1]) (cmul [0, 8, 0, 12, 0, 6, 0, 1] [0, 8, 0, 12, 0, 6, 0, 1]))) = 0 := by
    rw [← cnorm_eq_nil_iff]; native_decide
  exact hermiteReduce_residual_correct_of_radical 40 cA221 cD221 [8, 12, 20, 12, 8, 3]
    [0, 8, 0, 12, 0, 6, 0, 1] [0, 2, 0, 1] hD hgden hDstar hfuel hfuelD hermite_ex221_Dstar_dvd hWgd

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
content `Vi^i ∣ D` (`am_D_eq_cdiv_mul`), supplied here as a hypothesis. -/

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
    (hV : toPoly Vi ≠ 0) (hq : cnorm Vi ≠ [])
    (hg : toPoly (cgcdExt fuel (cmul (cdiv fuel D
        ((List.range (j + 2)).foldl (fun acc _ => cmul acc Vi) [1])) (cderiv Vi)) Vi).1
      = Polynomial.C (clead (cgcdExt fuel (cmul (cdiv fuel D
          ((List.range (j + 2)).foldl (fun acc _ => cmul acc Vi) [1])) (cderiv Vi)) Vi).1))
    (hgc : clead (cgcdExt fuel (cmul (cdiv fuel D
        ((List.range (j + 2)).foldl (fun acc _ => cmul acc Vi) [1])) (cderiv Vi)) Vi).1 ≠ 0)
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
  have hspec := hermiteInner_spec_of fuel Vi U hU hV hq hg hgc (j + 1) A
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
  rw [hmapeq, sum_map_const_sub]
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

/-- **List-sum of common-denominator fractions**: `∑ₖ am (f k)/d = am (∑ₖ f k)/d` in `RatFunc ℚ` (the
numerators add over the shared denominator `d`). The sum collapses the per-factor residuals onto a
single fraction over `am D`. -/
theorem list_sum_am_div_const {α : Type*} (l : List α) (f : α → ℚ[X]) (d : RatFunc ℚ) :
    (l.map (fun k => algebraMap ℚ[X] (RatFunc ℚ) (f k) / d)).sum
      = algebraMap ℚ[X] (RatFunc ℚ) ((l.map f).sum) / d := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons, map_add, add_div]

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
  rw [list_sum_am_div_const kept (residNumIncr fuel A D) (am (toPoly D))]
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
    (hV : toPoly Vi ≠ 0) (hq : cnorm Vi ≠ [])
    (hg : toPoly (cgcdExt fuel (cmul (cdiv fuel D
        ((List.range (j + 2)).foldl (fun acc _ => cmul acc Vi) [1])) (cderiv Vi)) Vi).1
      = Polynomial.C (clead (cgcdExt fuel (cmul (cdiv fuel D
          ((List.range (j + 2)).foldl (fun acc _ => cmul acc Vi) [1])) (cderiv Vi)) Vi).1))
    (hgc : clead (cgcdExt fuel (cmul (cdiv fuel D
        ((List.range (j + 2)).foldl (fun acc _ => cmul acc Vi) [1])) (cderiv Vi)) Vi).1 ≠ 0)
    (hDrec : algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
      = algebraMap ℚ[X] (RatFunc ℚ) (toPoly (cdiv fuel D
          ((List.range (j + 2)).foldl (fun acc _ => cmul acc Vi) [1])))
        * algebraMap ℚ[X] (RatFunc ℚ) (toPoly Vi) ^ (j + 2)) :
    (toQFun (glocIncr fuel A D (Vi, j + 2)))′
      = algebraMap ℚ[X] (RatFunc ℚ) (toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
        - algebraMap ℚ[X] (RatFunc ℚ) (residNumIncr fuel A D (Vi, j + 2))
          / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D) := by
  rw [glocIncr_residual fuel A D Vi j hU hV hq hg hgc hDrec]
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

/-! ### Summary: the multi-factor interference invariant, reduced to ONE named divisibility

The multi-factor `hermiteReduce` `g`-fold correctness is now reduced to a **single** polynomial
divisibility. The chain (all proven except the last):

* `foldl_cond_eq_foldl_glocList` — the conditional `g`-fold is a plain `qadd`-fold over the kept-factor
  increment list `glocList`.
* `glocIncr_residual` / `glocIncr_hstep` — each kept factor's increment reduces the *global* `T = A/D`,
  leaving `residᵢ = am Afinalᵢ/(am Uᵢ·am Vi)` (over the global `D`: `am (Afinalᵢ·Vi^{i−1})/am D`), from
  the per-factor Bézout side conditions and the reconciliation `am D = am Uᵢ·am Vi^{i}`.
* `total_fold_residual` / `total_fold_residual_over_D` — the whole fold residual `A/D − g′` is the
  **single** polynomial fraction `am R/am D` with `R = C(1−n)·A + Σᵢ residNumIncrᵢ` (`n = #kept`): the
  exact `(1−n)·T + Σ residᵢ` overcounting skeleton collapsed onto the common denominator `D`.
* `toPoly_Dstar_dvd_D` (**proven** Yun radical clause) gives `Dstar ∣ D`, i.e. `D = Dstar·W`,
  `W = D/Dstar`.
* `am_div_D_eq_div_Dstar` — `am R/am D` clears to `am (R/W)/am Dstar` **iff** `W ∣ R`.
* `hermiteReduce_residual_correct_multifactor` — assembles the above into
  `am A/am D = (toQFun g)′ + am (R/W)/am Dstar`, **conditional only on `W ∣ R`**.
* `residNum_eq_resNumPrime` + `dvd_R_iff_dvd_resNumPrime` — `R·gden² = resNum'`, so `W ∣ R ⟺
  W·gden² ∣ resNum'` (the algorithm's own cleared-identity cert), confirming consistency.

**THE REMAINING WALL** is the single divisibility

  `W ∣ R`,   `W = D/Dstar`,   `R = C(1−n)·A + Σ_{kept (Vi,i)} Afinalᵢ · Vi^{i−1}`,

equivalently `W·gden² ∣ resNum'`. It is the genuine **multi-factor interference clearing**: each
`Afinalᵢ` (the leftover numerator of `hermiteInner` over factor `i`) carries high powers of the *other*
factors in its residual denominator `Uᵢ·Vi = D/Vi^{i−1}`, and only the *sum* `(1−n)·A + Σᵢ Afinalᵢ·Vi^{i−1}`
cancels those high powers down to the radical `Dstar`. This cancellation is **not** implied by the
per-factor `hermiteInner_spec_of` specifications alone (which constrain each `Afinalᵢ` only locally); it
is the global partial-fraction content of Hermite-reduction correctness, decidably true per example
(`hermite_ex221_Dstar_dvd` + the residual cert) but abstractly open. The single-repeated-factor case
(`n = 1`, `W = ∏_{k≠i} Vk^{ik−1} = 1`, so `W ∣ R` is trivial) is the proven
`hermiteReduce_residual_correct_single`. -/

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
