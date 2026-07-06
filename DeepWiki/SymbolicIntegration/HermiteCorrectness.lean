import DeepWiki.Algebra.ListSums
import DeepWiki.Algebra.ListProducts
import DeepWiki.Algebra.PolynomialDivisibility
import DeepWiki.SymbolicIntegration.Compute.Correctness
import DeepWiki.SymbolicIntegration.Compute.LrtLogPart
import DeepWiki.SymbolicIntegration.Compute.RationalFunction
import DeepWiki.SymbolicIntegration.Compute.SquarefreeExact
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

/-! ### Uniqueness of the reduced Bézout cofactor -/

/-- Reduced-Bézout cofactor uniqueness: for coprime `p, q` (`q ≠ 0`), proper cofactors `B₁, B₂`
(`deg Bᵢ < deg q`) with partners solving `Bᵢ·p + Cᵢ·q = rhs` satisfy `B₁ = B₂`. -/
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

/-- Reduced-Bézout partner uniqueness: with `B` fixed and `q ≠ 0`, `B·p + Cᵢ·q = rhs` pins `C₁ = C₂`. -/
theorem reduced_bezout_snd_unique {p q B C₁ C₂ rhs : ℚ[X]} (hq : q ≠ 0)
    (h₁ : B * p + C₁ * q = rhs) (h₂ : B * p + C₂ * q = rhs) :
    C₁ = C₂ := by
  have : C₁ * q = C₂ * q := by linear_combination h₁ - h₂
  exact mul_right_cancel₀ hq this

/-! ### `cdiophantine` realizes `diophantineSolveReduced` (degree bound for `B`) -/

/-- The first computable cofactor `(cdiophantine fuel p q rhs).1` is the normalized remainder
`cnorm (cmod fuel (cscale (clead (cgcdExt fuel p q).1)⁻¹ (cmul rhs (cgcdExt fuel p q).2.1)) q)`. -/
theorem cdiophantine_fst_eq (fuel : ℕ) (p q rhs : CPoly) :
    (cdiophantine fuel p q rhs).1
      = cnorm (cmod fuel
          (cscale (clead (cgcdExt fuel p q).1)⁻¹ (cmul rhs (cgcdExt fuel p q).2.1)) q) := by
  rcases hgst : cgcdExt fuel p q with ⟨g, s, t⟩
  simp only [cdiophantine, hgst, cmod]

/-- Degree bound for the computable cofactor `B`: with enough fuel and `q ≠ 0`,
`(toPoly (cdiophantine fuel p q rhs).1).degree < (toPoly q).degree`. -/
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

/-! ### The agreement `cdiophantine ↔ diophantineSolveReduced` -/

/-- `cdiophantine fuel p q rhs` has the reduced coprime input certificates. -/
structure IsCDiophantineInput (fuel : ℕ) (p q rhs : CPoly) : Prop where
  /-- The computable denominator is nonzero. -/
  q_ne : cnorm q ≠ []
  /-- The abstract inputs are coprime. -/
  coprime : IsCoprime (toPoly p) (toPoly q)
  /-- The computable gcd reads as its leading constant. -/
  gcd_const : toPoly (cgcdExt fuel p q).1 = Polynomial.C (clead (cgcdExt fuel p q).1)
  /-- The leading coefficient of the computed gcd is nonzero. -/
  gcd_lead_ne : clead (cgcdExt fuel p q).1 ≠ 0
  /-- The modulus fuel bound is large enough for the scaled right-hand side. -/
  fuel_bound : (cnorm (cscale (clead (cgcdExt fuel p q).1)⁻¹
    (cmul rhs (cgcdExt fuel p q).2.1))).length ≤ fuel

open Classical in
/-- First-cofactor agreement: `toPoly (cdiophantine fuel p q rhs).1 = (diophantineSolveReduced
(toPoly p) (toPoly q) (toPoly rhs)).1`, for coprime `p, q`, `q ≠ 0`, computable gcd a nonzero
constant, and enough fuel. -/
theorem toPoly_cdiophantine_fst_eq (fuel : ℕ) (p q rhs : CPoly)
    (hinput : IsCDiophantineInput fuel p q rhs) :
    toPoly (cdiophantine fuel p q rhs).1
      = (diophantineSolveReduced (toPoly p) (toPoly q) (toPoly rhs)).1 := by
  obtain ⟨hq, hcop, hg, hgc, hfuel⟩ := hinput
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
/-- Second-cofactor agreement: `toPoly (cdiophantine fuel p q rhs).2 = (diophantineSolveReduced
(toPoly p) (toPoly q) (toPoly rhs)).2`, pinned once the first cofactor agrees. -/
theorem toPoly_cdiophantine_snd_eq (fuel : ℕ) (p q rhs : CPoly)
    (hinput : IsCDiophantineInput fuel p q rhs) :
    toPoly (cdiophantine fuel p q rhs).2
      = (diophantineSolveReduced (toPoly p) (toPoly q) (toPoly rhs)).2 := by
  have hq := hinput.q_ne
  have hcop := hinput.coprime
  have hg := hinput.gcd_const
  have hgc := hinput.gcd_lead_ne
  have hq0 : toPoly q ≠ 0 := fun h => hq ((cnorm_eq_nil_iff q).mpr h)
  have hfst := toPoly_cdiophantine_fst_eq fuel p q rhs hinput
  have hc_eq := toPoly_cdiophantine fuel p q rhs hq hg hgc
  have ha_eq := diophantineSolveReduced_spec hcop (toPoly rhs)
  -- with `B` equal, the two Bézout equations have the same `B·p` term; cancel `q`.
  refine reduced_bezout_snd_unique (p := toPoly p)
    (B := (diophantineSolveReduced (toPoly p) (toPoly q) (toPoly rhs)).1)
    (rhs := toPoly rhs) hq0 ?_ ?_
  · rw [← hfst]; linear_combination hc_eq
  · linear_combination ha_eq

open Classical in
/-- Full `cdiophantine ↔ diophantineSolveReduced` agreement (both cofactors): under `toPoly`, the
computable Bézout solver realizes the abstract `diophantineSolveReduced` pair. -/
theorem toPoly_cdiophantine_eq (fuel : ℕ) (p q rhs : CPoly)
    (hinput : IsCDiophantineInput fuel p q rhs) :
    (toPoly (cdiophantine fuel p q rhs).1, toPoly (cdiophantine fuel p q rhs).2)
      = diophantineSolveReduced (toPoly p) (toPoly q) (toPoly rhs) :=
  Prod.ext (toPoly_cdiophantine_fst_eq fuel p q rhs hinput)
    (toPoly_cdiophantine_snd_eq fuel p q rhs hinput)

-- The reduced-Bézout cofactor of `cdiophantine` equals the abstract `diophantineSolveReduced`'s.
example (fuel : ℕ) (p q rhs : CPoly)
    (hq : cnorm q ≠ []) (hcop : IsCoprime (toPoly p) (toPoly q))
    (hg : toPoly (cgcdExt fuel p q).1 = Polynomial.C (clead (cgcdExt fuel p q).1))
    (hgc : clead (cgcdExt fuel p q).1 ≠ 0)
    (hfuel : (cnorm (cscale (clead (cgcdExt fuel p q).1)⁻¹
        (cmul rhs (cgcdExt fuel p q).2.1))).length ≤ fuel) :
    toPoly (cdiophantine fuel p q rhs).1
      = (diophantineSolveReduced (toPoly p) (toPoly q) (toPoly rhs)).1 :=
  toPoly_cdiophantine_fst_eq fuel p q rhs ⟨hq, hcop, hg, hgc, hfuel⟩

/-! ### The `hermiteInner` step identity and inner-loop invariant (in `RatFunc ℚ`) -/

open scoped Differential in
/-- The `hermiteInner` step identity in `RatFunc ℚ`: from `B·(U·V') + C·V = −A·(1/(j+1))`, with next
numerator `A' = −(j+1)·C − U·B'`, `am A/(am U·am V^(j+2)) = (am B/am V^(j+1))′ + am A'/(am U·am V^(j+1))`,
dropping the `V`-power by one and emitting `B/V^(j+1)`. -/
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

/-- `foldl (·* V) init` over `range n` realizes `init · V^n` under `toPoly`. -/
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

/-! ### The `hermiteInner` loop correctness (in `RatFunc ℚ`) -/

/-- The per-step Bézout relation of `hermiteInner` at counter `j'` with numerator `A'`: the
`cdiophantine` cofactors `(B, C)` satisfy `B·(U·V') + C·V = −A'·(1/(j'+1))` under `toPoly`. -/
private def hbezPred (fuel : ℕ) (V U : CPoly) (j' : ℕ) (A' : CPoly) : Prop :=
  toPoly (cdiophantine fuel (cmul U (cderiv V)) V (cscale (-((j' : ℚ) + 1)⁻¹) A')).1
      * (toPoly U * derivative (toPoly V))
    + toPoly (cdiophantine fuel (cmul U (cderiv V)) V (cscale (-((j' : ℚ) + 1)⁻¹) A')).2
      * toPoly V
    = -toPoly A' * Polynomial.C (((j' : ℚ) + 1)⁻¹)

/-- The Hermite-inner Bézout call has a nonzero denominator and constant gcd. -/
structure IsHermiteInnerBezoutInput (fuel : ℕ) (V U : CPoly) : Prop where
  /-- The inner denominator is nonzero. -/
  den_ne : cnorm V ≠ []
  /-- The computed gcd reads as its leading constant. -/
  gcd_const : toPoly (cgcdExt fuel (cmul U (cderiv V)) V).1
    = Polynomial.C (clead (cgcdExt fuel (cmul U (cderiv V)) V).1)
  /-- The leading coefficient of the computed gcd is nonzero. -/
  gcd_lead_ne : clead (cgcdExt fuel (cmul U (cderiv V)) V).1 ≠ 0

open scoped Differential in
/-- `hermiteInner` loop invariant (accumulator-general form) in `RatFunc ℚ`: for `U, V ≠ 0` and every
Bézout step satisfying `hbez`, and any accumulator `g` with nonzero denominator,
`am A/(am U·am V^(j+1)) + (toQFun g)′ = (toQFun (hermiteInner fuel V U j A g).1)′ + am A_final/(am U·am V)`. -/
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

open scoped Differential in
/-- The `qadd`-fold derivative is the sum of the increment derivatives: from `qzero`,
`(toQFun (gs.foldl qadd qzero))′ = ∑ⱼ (toQFun gⱼ)′` in `RatFunc ℚ`. -/
theorem deriv_toQFun_foldl_qadd (gs : List QFun) (hgs : ∀ g ∈ gs, toPoly g.2 ≠ 0) :
    (toQFun (gs.foldl qadd qzero))′ = (gs.map (fun g => (toQFun g)′)).sum := by
  rw [toQFun_foldl_qadd gs qzero (by simp [qzero, toPoly_cons]) hgs, toQFun_qzero, zero_add]
  rw [show ((gs.map toQFun).sum)′ = Differential.deriv (R := RatFunc ℚ) (gs.map toQFun).sum from rfl,
    map_list_sum (Differential.deriv (R := RatFunc ℚ)) (gs.map toQFun), List.map_map]
  rfl

open scoped Differential in
/-- The global-`A` fold residual as `(1−n)·T + ∑ residᵢ` in `RatFunc ℚ`: if each increment satisfies
`(toQFun gⱼ)′ = T − residⱼ`, then `T − (toQFun (gs.foldl qadd qzero))′ = T − gs.length • T + ∑ⱼ residⱼ`. -/
theorem foldl_residual_eq (gs : List QFun) (hgs : ∀ g ∈ gs, toPoly g.2 ≠ 0)
    (T : RatFunc ℚ) (resid : QFun → RatFunc ℚ)
    (hstep : ∀ g ∈ gs, (toQFun g)′ = T - resid g) :
    T - (toQFun (gs.foldl qadd qzero))′
      = T - gs.length • T + (gs.map resid).sum := by
  rw [deriv_toQFun_foldl_qadd gs hgs, List.map_congr_left hstep, list_sum_map_const_sub]
  abel

open scoped Differential in
/-- `hermiteInner` loop correctness (public `qzero`-start form) in `RatFunc ℚ`: for `U, V ≠ 0` and
every Bézout step satisfying `hbez`, `am A/(am U·am V^(j+1)) = (toQFun gloc)′ + am A_final/(am U·am V)`
where `(gloc, A_final) = hermiteInner fuel V U j A qzero`. -/
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

/-- The per-step Bézout relation `hbezPred` holds for every `j', A'`, given `V ≠ 0` and the gcd of
`cmul U (cderiv V)` and `V` a nonzero constant. Discharges `hermiteInner_spec`'s `hbez` premise. -/
theorem hermiteInner_bezout_of (fuel : ℕ) (V U : CPoly) (j' : ℕ) (A' : CPoly)
    (hbez : IsHermiteInnerBezoutInput fuel V U) :
    hbezPred fuel V U j' A' := by
  obtain ⟨hq, hg, hgc⟩ := hbez
  rw [hbezPred]
  have h := toPoly_cdiophantine fuel (cmul U (cderiv V)) V
    (cscale (-((j' : ℚ) + 1)⁻¹) A') hq hg hgc
  rw [toPoly_cmul, toPoly_cderiv, toPoly_cscale] at h
  rw [h]
  rw [show Polynomial.C (-((j' : ℚ) + 1)⁻¹) = -Polynomial.C (((j' : ℚ) + 1)⁻¹) from by rw [map_neg]]
  ring

open scoped Differential in
/-- `hermiteInner` correctness from the computable engine (fully-discharged form): for `U, V` with
nonzero `toPoly`, `cnorm V ≠ []`, and the gcd of `cmul U (cderiv V)` and `V` a nonzero constant, the
inner loop satisfies `am A/(am U·am V^(j+1)) = (toQFun gloc)′ + am A_final/(am U·am V)`. -/
theorem hermiteInner_spec_of (fuel : ℕ) (V U : CPoly) (hU : toPoly U ≠ 0) (hV : toPoly V ≠ 0)
    (hbez : IsHermiteInnerBezoutInput fuel V U) (j : ℕ) (A : CPoly) :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly A)
        / (algebraMap ℚ[X] (RatFunc ℚ) (toPoly U)
            * algebraMap ℚ[X] (RatFunc ℚ) (toPoly V) ^ (j + 1))
      = (toQFun (hermiteInner fuel V U j A qzero).1)′
        + algebraMap ℚ[X] (RatFunc ℚ) (toPoly (hermiteInner fuel V U j A qzero).2)
          / (algebraMap ℚ[X] (RatFunc ℚ) (toPoly U) * algebraMap ℚ[X] (RatFunc ℚ) (toPoly V)) :=
  hermiteInner_spec fuel V U hU hV
    (fun j' A' => hermiteInner_bezout_of fuel V U j' A' hbez) j A

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
  hermiteInner_spec_of fuel V U hU hV ⟨hq, hg, hgc⟩ j A

/-! ### The residual-recovery identity (in `RatFunc ℚ`) -/

/-- The denominators of a Hermite residual wrapper are nonzero. -/
structure IsHermiteResidualInput (D gden Dstar : CPoly) : Prop where
  /-- The original denominator reads nonzero. -/
  den_ne : toPoly D ≠ 0
  /-- The rational-part denominator reads nonzero. -/
  gden_ne : toPoly gden ≠ 0
  /-- The squarefree residual denominator is nonzero. -/
  radical_ne : cnorm Dstar ≠ []

open scoped Differential in
/-- The residual-recovery numerator identity in `RatFunc ℚ`: for `D, gden ≠ 0`,
`am A/am D − (am gnum/am gden)′ = am resNum/(am D·(am gden·am gden))` with
`resNum = A·gden² − D·(gnum'·gden − gnum·gden')`. -/
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

/-! ### The full `hermiteReduce` wrapper correctness (in `RatFunc ℚ`) -/

open scoped Differential in
/-- Full `hermiteReduce` wrapper correctness in `RatFunc ℚ`: under the exact-division certificate
`hexact` and `D, gden ≠ 0`, `Dstar ≠ 0`, the reduction satisfies
`am A/am D = (toQFun (gnum,gden))′ + am Bres/am Dstar` with `Bres = cdiv fuel (resNum·Dstar) (D·gden²)`
and `resNum = A·gden² − D·(gnum'·gden − gnum·gden')`. -/
theorem hermiteReduce_residual_correct (fuel : ℕ) (A D : CPoly)
    (gnum gden Dstar : CPoly)
    (hden : IsHermiteResidualInput D gden Dstar)
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
  have hD := hden.den_ne
  have hgden := hden.gden_ne
  have hDstar := hden.radical_ne
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
/-- `hermiteReduce` wrapper correctness, residual form with `Bres` the `cnorm`-wrapped exact division:
under `hexact` and `D, gden ≠ 0`, `Dstar ≠ 0`,
`am A/am D = (toQFun (gnum,gden))′ + am Bres/am Dstar`. -/
theorem hermiteReduce_spec_cnorm (fuel : ℕ) (A D gnum gden Dstar : CPoly)
    (hden : IsHermiteResidualInput D gden Dstar)
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
  exact hermiteReduce_residual_correct fuel A D gnum gden Dstar hden hexact

open scoped Differential in
/-- `hermiteReduce` wrapper correctness from an algebraic divisibility certificate in `RatFunc ℚ`: with
the premise `toPoly (D·gden²) ∣ toPoly (resNum·Dstar)` (plus a fuel bound), and `D, gden ≠ 0`,
`Dstar ≠ 0`, `am A/am D = (toQFun (gnum,gden))′ + am Bres/am Dstar`. -/
theorem hermiteReduce_residual_correct_of_dvd (fuel : ℕ) (A D gnum gden Dstar : CPoly)
    (hden : IsHermiteResidualInput D gden Dstar)
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
  have hD := hden.den_ne
  have hgden := hden.gden_ne
  have hresDenP : toPoly (cmul D (cmul gden gden)) ≠ 0 := by
    rw [toPoly_cmul, toPoly_cmul]
    exact mul_ne_zero hD (mul_ne_zero hgden hgden)
  have hresDen : cnorm (cmul D (cmul gden gden)) ≠ [] :=
    fun h => hresDenP ((cnorm_eq_nil_iff _).mp h)
  exact hermiteReduce_residual_correct fuel A D gnum gden Dstar hden
    (cmod_eq_zero_of_dvd fuel _ _ hresDen hfuel hdvd)

/-! ### Bridging the concrete `csqfreeFactor` monic gcd to the abstract `gcd` -/

/-- `cmonic` realizes `normalize` through `toPoly`: `toPoly (cmonic q) = normalize (toPoly q)`. -/
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

/-- The concrete monic gcd realizes the abstract `gcd` (under gcd-termination):
`toPoly (cmonic (cgcdExt fuel b d).1) = gcd (toPoly b) (toPoly d)`. -/
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

/-! ### The concrete `csqfreeFactor.go` carries the abstract `YunInv` — squarefree emitted factors -/

/-- Per-step honesty bundle for `csqfreeFactor.go` to realize the abstract Yun step: at each
non-terminal step the gcd terminates and `q = cmonic (cgcdExt b d).1` divides both `b` and `d` exactly,
recursing on `(b′, d′)`. -/
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

/-! ### Crossing the `ℚ`-instance diamond by `convert`

The abstract Yun theory is stated over `{K} [Field K]` (deriving `CommRing`/`NormalizedGCDMonoid` from
`Field`), while the concrete loop uses `ℚ`'s ambient instances. `convert … using 2` reduces the gap to
`rfl` on the `CommRing ℚ` halves and a `Subsingleton (DecidableEq ℚ)` on the `NormalizedGCDMonoid` ones;
the `_rat` specializations below package this discharge. -/

open Classical in
/-- `A.primPart ≠ 0` for `A : ℚ[X]`. -/
theorem primPart_ne_zero_rat (A : ℚ[X]) : A.primPart ≠ 0 := A.primPart_ne_zero

/-- Every Yun factor is squarefree over `ℚ` (ambient instances): for `A : ℚ[X]`, `A ≠ 0`, every member
of `yunFactorizationAbs A n` is squarefree. -/
theorem yunFactorizationAbs_squarefree_rat (A : ℚ[X]) (hA0 : A ≠ 0) (n : ℕ) :
    ∀ V ∈ yunFactorizationAbs A n, Squarefree V := by
  convert yunFactorizationAbs_squarefree A hA0 ?_ n using 2
  convert A.primPart_ne_zero using 2
  · rfl
  · congr 1
    exact Subsingleton.elim _ _

/-- `sqfreeFactPart A i` over `ℚ[X]` agrees across the ambient/`Classical` instance paths (they differ
only in a `Subsingleton (DecidableEq ℚ)` argument), stated as a propositional `Eq`. -/
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

/-- Factorwise correctness over `ℚ` (ambient instances): `yunFactorizationAbs A n` is `Forall₂
Associated` to `(List.range n).map (fun j => sqfreeFactPart A (1+j))`. -/
theorem yunFactorizationAbs_forall₂_rat (A : ℚ[X]) (hA0 : A ≠ 0) (n : ℕ) :
    List.Forall₂ Associated (yunFactorizationAbs A n)
      ((List.range n).map (fun j => sqfreeFactPart A (1 + j))) := by
  rw [List.map_congr_left fun j _ => sqfreeFactPart_rat_eq A (1 + j)]
  refine yunFactorizationAbs_forall₂ A hA0 ?_ n
  convert A.primPart_ne_zero using 2
  · rfl
  · congr 1
    exact Subsingleton.elim _ _

/-- Pairwise relative primality over `ℚ` (ambient instances): distinct-position factors of
`yunFactorizationAbs A n` are `IsRelPrime`. -/
theorem yunFactorizationAbs_pairwise_isRelPrime_rat (A : ℚ[X]) (hA0 : A ≠ 0) (n : ℕ) {p q : ℕ}
    (hpq : p ≠ q) (hp : p < (yunFactorizationAbs A n).length)
    (hq : q < (yunFactorizationAbs A n).length) :
    IsRelPrime ((yunFactorizationAbs A n).get ⟨p, hp⟩) ((yunFactorizationAbs A n).get ⟨q, hq⟩) := by
  convert yunFactorizationAbs_pairwise_isRelPrime A hA0 ?_ n hpq hp hq using 2
  convert A.primPart_ne_zero using 2
  · rfl
  · congr 1
    exact Subsingleton.elim _ _

/-- The product decomposition over `ℚ` (ambient instances): the powered product `∏ₖ eₖ^{1+k}` of the
Yun factors is `Associated (∏_{j<n} sqfreeFactPart A (1+j)^{1+j})`. -/
theorem yunFactorizationAbs_prodPow_assoc_rat (A : ℚ[X]) (hA0 : A ≠ 0) (n : ℕ) :
    Associated (prodPow 1 (yunFactorizationAbs A n))
      (prodPow 1 ((List.range n).map (fun j => sqfreeFactPart A (1 + j)))) := by
  rw [List.map_congr_left fun j _ => sqfreeFactPart_rat_eq A (1 + j)]
  refine yunFactorizationAbs_prodPow_assoc A hA0 ?_ n
  convert A.primPart_ne_zero using 2
  · rfl
  · congr 1
    exact Subsingleton.elim _ _

/-! ### Concrete-loop step bridges: the abstract Yun step over ambient `ℚ` instances -/

/-- The ambient `gcd` over `ℚ[X]` equals the `Classical`-derived one (differing only in a
`Subsingleton (DecidableEq ℚ)` argument). Value-level companion of `sqfreeFactPart_rat_eq`. -/
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

/-- Yun loop base case over ambient `ℚ`: `csqfreeFactor`'s initialization satisfies `YunInv A 1`. -/
theorem yunInv_base_rat (A : ℚ[X]) (hA0 : A ≠ 0) :
    YunInv A 1 (A / gcd A (derivative A))
      (derivative A / gcd A (derivative A) - derivative (A / gcd A (derivative A))) := by
  have key := yunInv_base A hA0
    (by convert A.primPart_ne_zero using 2 <;> first | rfl | (congr 1; exact Subsingleton.elim _ _))
  rw [gcd_rat_eq A (derivative A)]
  exact key

/-- Scaled Yun loop base case over ambient `ℚ`: if the initial pair is a common constant multiple
`C u·` of the monic-gcd initialization (`u ≠ 0`), it satisfies `YunInv A 1` with scalar
`u·(leadingCoeff A)`. Absorbs the unit from dividing by the raw (non-monic) extended-gcd output. -/
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

/-- The emitted Yun factor is associated to `Vᵢ` over ambient `ℚ`: under `YunInv A i b d` (`1 ≤ i`),
`gcd b d` is `Associated (sqfreeFactPart A i)`. -/
theorem yunStep_emit_assoc_rat (A : ℚ[X]) (i : ℕ) (hi : 1 ≤ i) (b d : ℚ[X]) (hinv : YunInv A i b d) :
    Associated (gcd b d) (sqfreeFactPart A i) := by
  have key := yunStep_emit_assoc A i hi
    (by convert A.primPart_ne_zero using 2 <;> first | rfl | (congr 1; exact Subsingleton.elim _ _)) hinv
  rw [sqfreeFactPart_rat_eq A i, gcd_rat_eq b d]
  exact key

/-- One Yun loop step advances the invariant over ambient `ℚ`: from `YunInv A i b d` (`1 ≤ i`), the
deflated `(b/gcd, d/gcd − (b/gcd)′)` satisfies `YunInv A (i+1)`. -/
theorem yunStep_preserves_rat (A : ℚ[X]) (i : ℕ) (hi : 1 ≤ i) (b d : ℚ[X]) (hinv : YunInv A i b d) :
    YunInv A (i + 1) (b / gcd b d) (d / gcd b d - derivative (b / gcd b d)) := by
  have key := (yunStep_preserves A i hi
    (by convert A.primPart_ne_zero using 2 <;> first | rfl | (congr 1; exact Subsingleton.elim _ _))
    hinv).2
  rw [gcd_rat_eq b d]
  exact key

/-! ### The concrete `csqfreeFactor.go` loop carries the abstract `YunInv` (factorwise association) -/

/-- `Babs A i ≠ 0` over `ℚ`. -/
theorem Babs_ne_zero_rat (A : ℚ[X]) (i : ℕ) : Babs A i ≠ 0 := by
  rw [Babs]
  exact (squarefreePart_deflation_monic A (i - 1)
    (by convert A.primPart_ne_zero using 2 <;>
      first | rfl | (congr 1; exact Subsingleton.elim _ _))).ne_zero

/-- The working numerator `b` of a `YunInv A i b d` state is nonzero. -/
theorem ne_zero_of_yunInv_rat (A : ℚ[X]) (i : ℕ) (b d : ℚ[X]) (hinv : YunInv A i b d) : b ≠ 0 := by
  obtain ⟨c, hc, hb, _⟩ := hinv
  rw [hb]
  exact mul_ne_zero ((map_ne_zero_iff _ Polynomial.C_injective).mpr hc) (Babs_ne_zero_rat A i)

/-- `b = a / c` from the exact factorization `a = c · b` (`c ≠ 0`). -/
private theorem eq_div_of_eq_mul {a b c : ℚ[X]} (hc : c ≠ 0) (h : a = c * b) : b = a / c := by
  rw [h, mul_div_cancel_left₀ _ hc]

/-- The concrete Yun loop's kept factors are factorwise associated to the squarefree parts: under
`GoYun fuel fo b d` and `YunInv (toPoly A) i (toPoly b) (toPoly d)` (`1 ≤ i`), every
`(V, m) ∈ csqfreeFactor.go fuel fo b d i` has `toPoly V ~ sqfreeFactPart (toPoly A) m` and `i ≤ m`. -/
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
    (hbez : IsHermiteInnerBezoutInput fuel V U) (j : ℕ)
    (hD : algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
      = algebraMap ℚ[X] (RatFunc ℚ) (toPoly U) * algebraMap ℚ[X] (RatFunc ℚ) (toPoly V) ^ (j + 1))
    (hDstar : algebraMap ℚ[X] (RatFunc ℚ) (toPoly Dstar)
      = algebraMap ℚ[X] (RatFunc ℚ) (toPoly U) * algebraMap ℚ[X] (RatFunc ℚ) (toPoly V)) :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
      = (toQFun (hermiteInner fuel V U j A qzero).1)′
        + algebraMap ℚ[X] (RatFunc ℚ) (toPoly (hermiteInner fuel V U j A qzero).2)
          / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Dstar) := by
  rw [hD, hDstar]
  exact hermiteInner_spec_of fuel V U hU hV hbez j A

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
    (hden : IsHermiteResidualInput D gden Dstar)
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
  have hD := hden.den_ne
  have hgden := hden.gden_ne
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
    exact DeepWiki.polynomial_dvd_clearedIdentity_of_split hD hDR hg2dvd
  exact hermiteReduce_residual_correct_of_dvd fuel A D gnum gden Dstar hden hfuel hdvd

open scoped Differential in
/-- **`hermiteReduce` wrapper correctness from the radical clause plus one cert** in `RatFunc ℚ`: the
cleared-identity premise reduced using the **proven** radical-divides fact `Dstar ∣ D`
(`hDstarD`, from `toPoly_Dstar_dvd_D`/`SqfreeYun` when `Dstar` is the computed radical). With
`W = D/Dstar`, the single residual cert `hWgd : W·gden² ∣ resNum'` (a `cmod`-vanishing) then suffices.
Under `D, gden ≠ 0`, `Dstar ≠ 0` and a fuel bound, `am A/am D = (toQFun (gnum,gden))′ + am Bres/am
Dstar`. This is the cleanest divisibility input: the *abstract* radical content folded in, leaving one
decidable cert. -/
theorem hermiteReduce_residual_correct_of_radical (fuel : ℕ) (A D gnum gden Dstar : CPoly)
    (hden : IsHermiteResidualInput D gden Dstar)
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
  have hD := hden.den_ne
  have hgden := hden.gden_ne
  have hDstar := hden.radical_ne
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
    exact DeepWiki.polynomial_dvd_clearedIdentity_of_radical
      (W := toPoly (cdiv fuel D Dstar)) hWeq hWgddvd
  exact hermiteReduce_residual_correct_of_dvd fuel A D gnum gden Dstar hden hfuel hdvd

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
    (hden : IsHermiteResidualInput D gden Dstar)
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
  exact hermiteReduce_residual_correct_of_split fuel A D gnum gden Dstar hden hfuel
    hresD hg2

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
  hermiteReduce_residual_correct_uncond fuel A D gnum gden Dstar ⟨hD, hgden, hDstar⟩ hfuel hcomp

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
