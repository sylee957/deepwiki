import DeepWiki.SymbolicIntegration.Computable.LogPartTowerSoundness
import DeepWiki.SymbolicIntegration.ComputableRadicalLogSoundness
import DeepWiki.SymbolicIntegration.PartialFraction
import DeepWiki.SymbolicIntegration.ResidueMultiplicity
import DeepWiki.SymbolicIntegration.MonomialExtensions

/-! # The Rothstein–Trager residue-MATCH correctness (Bronstein Thm 5.6.1, abstract)

`ComputableLogPartTowerSoundness` reduced the checker-free normal-part one-shot to a single hypothesis
`hmatch` — the **residue match**: that the integrator's logarithmic part `∑ᵢ cᵢ·D(log vᵢ)` (over the tower
with the monomial derivation `D = cmonomialDeriv Dt`, so `D(t−α) = Dt − α′`, NOT `1`) sums to the simple
integrand `a/d` over `RatFunc (CFieldSpec.K α)`. The residues `cᵢ` are the roots of the Rothstein–Trager
resultant `R(z) = res_t(d, a − z·Dd)` (PROVEN: `roots_residueResultantTowerG_eq_residues`) and each
`vᵢ = gcd_t(d, a − cᵢ·Dd)`.

The base-field analogue is `ratFunc_eq_sum_residue_grouped` (`PartialFraction`): for `D = ∏(X−α)`
squarefree and the *standard* polynomial derivative (`(X−α)′ = 1`),
`A/D = ∑_a a·logDeriv(∏_{res(α)=a}(X−α))`. The ★ subtlety the prompt flags (the same gap as the algebraic
`isRadicalLogIntegral_of_residue_match`): over a monomial `D(t−α) = Dt − α′ ≠ 1`, so the Lagrange
identity does NOT transport verbatim — the residue `c` at `α` must **absorb** the `Dt − α′` factor
(Bronstein Thm 5.6.1, the *differentiated* RT criterion).

This file builds the residue-match identity incrementally — small, individually-committed lemmas — toward
discharging the `hmatch` hypothesis of `logResidueSumG_eq_of_residue_match`. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

namespace ResidueMatchTower

/-! ### Step 1 (reused): the monomial derivative of a linear factor `t − C α`

Over the tower derivation `D = extendDeriv (implicitDeriv v)` with `v = toPolyG Dt`, the implicit
derivative of a linear factor is `implicitDeriv v (X − C α) = v − C α′` — `MonomialExtensions`'
`implicitDeriv_X_sub_C` (the §3.4 root-characterization crux). This is the structural source of the ★
absorption: the log-derivative of `t − α` is `(v − C α′)/(t − α)`, NOT `1/(t − α)`. -/

variable {K : Type*} [Field K] [Differential K]

/-! ### Step 2: the monomial log-derivative of a linear factor in `K(t)`

Under the extended monomial derivation `extendDeriv (implicitDeriv v)`, the log-derivative of the linear
factor `t − α` reads `(v − C α′)/(t − α)` over `RatFunc K` — the ★ absorption made explicit: it is
`(Dt − α′)/(t − α)`, NOT `1/(t − α)`. Combines `extendDeriv_logDeriv` with `implicitDeriv_X_sub_C`. -/

/-- **The monomial log-derivative of a linear factor** — over `extendDeriv (implicitDeriv v)`,
`D(t−α)/(t−α) = algebraMap(v − C α′) / algebraMap(t − α)` in `RatFunc K`. The Rothstein–Trager monomial
absorption made explicit at the per-factor level: the log-derivative is `(Dt − α′)/(t − α)`, not `1/(t − α)`.
By `extendDeriv_logDeriv` (the generic logarithmic-derivative reading) and `implicitDeriv_X_sub_C`. -/
theorem extendDeriv_implicitDeriv_logDeriv_X_sub_C [Algebra ℚ K] (v : K[X]) (α : K) :
    extendDeriv (Differential.implicitDeriv v) (algebraMap K[X] (RatFunc K) (X - C α))
        / algebraMap K[X] (RatFunc K) (X - C α)
      = algebraMap K[X] (RatFunc K) (v - C (α′)) / algebraMap K[X] (RatFunc K) (X - C α) := by
  rw [extendDeriv_logDeriv, implicitDeriv_X_sub_C]

/-! ### Step 3a: the ★ absorption identity at a simple root of `d`

The crux of Bronstein Thm 5.6.1. At a root `α` of the (squarefree) denominator `d`, the monomial
derivative `Dd = implicitDeriv v d` evaluates to `(Dd)(α) = d′(α)·(v(α) − α′)` — the `v(α) − α′` factor
that the residue `cᵢ = a(α)/(Dd)(α)` divides out is exactly what makes `cᵢ·D(t−α)/(t−α)` carry residue
`a(α)/d′(α)` at the place `t−α`, so the monomial RT sum telescopes to `a/d` despite `D(t−α) ≠ 1`.

Proof: `implicitDeriv v d = mapCoeffs d + v·(derivative d)`, so `(Dd)(α) = (mapCoeffs d)(α) +
v(α)·d′(α)`. Mathlib's `deriv_aeval_eq` gives `(d(α))′ = (mapCoeffs d)(α) + d′(α)·α′`; since `d(α) = 0`
its LHS is `0′ = 0`, so `(mapCoeffs d)(α) = −d′(α)·α′`, and the two combine to `d′(α)·(v(α) − α′)`. -/

/-- **`eval` of `mapCoeffs d` at a root of `d`** — for `d(α) = 0`, `(mapCoeffs d)(α) = −d′(α)·α′` over a
differential field `K`. From Mathlib's `deriv_aeval_eq` `(d(α))′ = (mapCoeffs d)(α) + d′(α)·α′` with the
LHS `(0)′ = 0`. The half of the absorption coming from the coefficient derivation `κ_D`. -/
theorem eval_mapCoeffs_of_isRoot (d : K[X]) (α : K) (hα : d.eval α = 0) :
    (Differential.mapCoeffs d).eval α = -((derivative d).eval α * α′) := by
  have h := Differential.deriv_aeval_eq (A := K) (R := K) α d
  simp only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id] at h
  rw [hα] at h
  -- `(0)′ = 0` since the derivation is additive
  rw [show (0 : K)′ = 0 from map_zero _] at h
  -- `0 = (mapCoeffs d)(α) + d′(α)·α′`, so `(mapCoeffs d)(α) = −d′(α)·α′`
  linear_combination -h

/-- **★ The absorption identity at a simple root** (Bronstein Thm 5.6.1) — for `d(α) = 0`, the monomial
derivative `Dd = implicitDeriv v d` evaluates to `(Dd)(α) = d′(α)·(v(α) − α′)`. The residue
`cᵢ = a(α)/(Dd)(α)` divides out this `v(α) − α′`, so `cᵢ·(v − C α′)/(t−α)` carries residue `a(α)/d′(α)`
at `t−α` — the place-wise content making the monomial RT sum reassemble `a/d`. From
`implicitDeriv = mapCoeffs + v·derivative` and `eval_mapCoeffs_of_isRoot`. -/
theorem eval_implicitDeriv_of_isRoot (v d : K[X]) (α : K) (hα : d.eval α = 0) :
    (Differential.implicitDeriv v d).eval α = (derivative d).eval α * (v.eval α - α′) := by
  rw [Differential.implicitDeriv]
  simp only [Derivation.add_apply, Derivation.coe_smul, Pi.smul_apply, smul_eq_mul,
    Derivation.coe_restrictScalars, derivative'_apply, eval_add, eval_mul]
  rw [eval_mapCoeffs_of_isRoot d α hα]
  ring

/-! ### Step 3b: the per-place residue value matches the standard residue

The RT residue at the place `t−α` is `c_α = a(α)/(Dd)(α)`. By the absorption identity, multiplying back
the monomial-log-derivative residue `v(α) − α′` recovers the *standard* residue `a(α)/d′(α)` of `a/d` at
that place: `c_α·(v(α) − α′) = a(α)/d′(α)`. This is the per-place equality that makes the monomial RT sum
have the same poles-and-residues as `a/d`. -/

/-- **The RT residue recovers the standard residue at a simple root** — for `d(α) = 0` with
`v(α) ≠ α′` (the factor is *normal*, so `(Dd)(α) ≠ 0`), the RT residue `c_α = a(α)/(Dd)(α)` satisfies
`c_α·(v(α) − α′) = a(α)/d′(α)` — the standard residue of `a/d` at `t−α`. The place-wise content of
Bronstein Thm 5.6.1: the monomial log-derivative `(v − Cα′)/(t−α)` weighted by `c_α` contributes exactly
the standard residue `a(α)/d′(α)`. From `eval_implicitDeriv_of_isRoot`. -/
theorem residue_mul_eval_sub_eq (a v d : K[X]) (α : K) (hα : d.eval α = 0)
    (hvα : v.eval α ≠ α′) :
    (a.eval α / (Differential.implicitDeriv v d).eval α) * (v.eval α - α′)
      = a.eval α / (derivative d).eval α := by
  rw [eval_implicitDeriv_of_isRoot v d α hα]
  rw [div_mul_eq_mul_div, mul_comm ((derivative d).eval α), ← div_div,
    mul_div_assoc, div_self (sub_ne_zero.mpr hvα), mul_one]

/-! ### Step 4: the monomial RT partial fraction over a PRIMITIVE monomial (`Dt = C w` ∈ base field)

For a **primitive** monomial — `Dt = v = C w` with `w ∈ K` (e.g. `t = log η`, `Dt = η′/η ∈ k`) — the
monomial derivative of a linear factor is the *constant* `D(t−α) = C(w − α′)`, so the log-derivative
`D(t−α)/(t−α) = C(w − α′)/(t−α)` has NO polynomial part and the ★ absorption collapses to a constant
factor. The RT sum then matches `a/d` **term by term** (no high-degree cancellation): each
`c_α·C(w−α′)/(t−α)` is `C(a(α)/d′(α))/(t−α)`, and `ratFunc_eq_sum_residue_div` reassembles `a/d`.

This is the unconditional primitive-case `hmatch`. (The hyperexponential / hypertangent cases have
`deg_t v ≥ 1`, where the per-term polynomial parts `c_α·(v /ₘ (t−α))` must cancel in aggregate — the
genuinely-harder regime, isolated below.) -/

variable [Algebra ℚ K]

/-- **The monomial log-derivative of `t−α` over a primitive monomial** `Dt = C w` reads as the constant
`C(w − α′)` over `t−α`: `D(t−α)/(t−α) = algebraMap(C(w − α′))/algebraMap(t−α)` in `RatFunc K`. The
primitive specialization of `extendDeriv_implicitDeriv_logDeriv_X_sub_C` (`v − Cα′ = C w − Cα′ =
C(w − α′)`). -/
theorem extendDeriv_implicitDeriv_C_logDeriv_X_sub_C (w α : K) :
    extendDeriv (Differential.implicitDeriv (C w)) (algebraMap K[X] (RatFunc K) (X - C α))
        / algebraMap K[X] (RatFunc K) (X - C α)
      = algebraMap K[X] (RatFunc K) (C (w - α′)) / algebraMap K[X] (RatFunc K) (X - C α) := by
  rw [extendDeriv_implicitDeriv_logDeriv_X_sub_C, ← C_sub]

/-- **★ The primitive-case monomial Rothstein–Trager partial fraction** (Bronstein Thm 5.6.1, primitive
monomial) — for a squarefree denominator `d = ∏_{α∈s}(t−α)`, `deg a < #s`, a primitive monomial `Dt = C w`,
and every root `α∈s` *normal* (`w ≠ α′`), the monomial RT residue sum over the roots equals `a/d`:
`∑_{α∈s} C(c_α)·(D(t−α)/(t−α)) = a/d` with `c_α = a(α)/(Dd)(α)` the RT residue and `D = extendDeriv
(implicitDeriv (C w))`. Term by term: `D(t−α)/(t−α) = C(w−α′)/(t−α)` (primitive ⇒ constant numerator),
`c_α·(w−α′) = a(α)/d′(α)` (`residue_mul_eval_sub_eq`), and `ratFunc_eq_sum_residue_div` reassembles `a/d`.
The unconditional residue match for primitive (logarithmic) tower extensions. -/
theorem primitive_monomial_residue_match (s : Finset K) (a : K[X]) (w : K)
    (hA : a.degree < s.card) (hnorm : ∀ α ∈ s, w ≠ α′) :
    ∑ α ∈ s, algebraMap K[X] (RatFunc K)
          (C (a.eval α / (Differential.implicitDeriv (C w) (Lagrange.nodal s id)).eval α))
        * (extendDeriv (Differential.implicitDeriv (C w))
              (algebraMap K[X] (RatFunc K) (X - C α))
            / algebraMap K[X] (RatFunc K) (X - C α))
      = algebraMap K[X] (RatFunc K) a / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id) := by
  rw [ratFunc_eq_sum_residue_div s a hA]
  refine Finset.sum_congr rfl fun α hα => ?_
  -- per-term: monomial log-derivative is the constant `C(w−α′)/(t−α)`
  rw [extendDeriv_implicitDeriv_C_logDeriv_X_sub_C]
  -- fold the residue coefficient into the constant numerator
  rw [← mul_div_assoc, ← map_mul, ← C_mul]
  -- `c_α·(w − α′) = a(α)/d′(α)` via residue_mul_eval_sub_eq (with `v = C w`, `v.eval α = w`)
  have hroot : (Lagrange.nodal s id).eval α = 0 := by
    have := Lagrange.eval_nodal_at_node (s := s) (v := (id : K → K)) hα
    simpa using this
  have h := residue_mul_eval_sub_eq a (C w) (Lagrange.nodal s id) α hroot
    (by simpa using hnorm α hα)
  rw [eval_C] at h
  -- both sides are `algebraMap (C ·) / algebraMap (t − α)`; the constants agree by `h`
  rw [h]

/-! ### Step 5: the general monomial RT partial fraction (modulo the polynomial-part cancellation)

For a NON-primitive monomial (`deg_t v ≥ 1`, e.g. hyperexponential `Dt = η′·t` or hypertangent), the
monomial log-derivative `D(t−α)/(t−α) = (v − Cα′)/(t−α)` has a *polynomial part* `q_α = v /ₘ (t−α)`
(degree `deg v − 1 ≥ 0`). Splitting `(v − Cα′)/(t−α) = q_α + (v(α)−α′)/(t−α)` (polynomial division),
the RT sum becomes `(∑_α c_α·q_α) + a/d` — the second summand by the per-place residue match
(`residue_mul_eval_sub_eq`) and `ratFunc_eq_sum_residue_div`. So the full identity `∑ c_α D(t−α)/(t−α) =
a/d` holds **iff the polynomial parts cancel**, `∑_α c_α·q_α = 0`.

This `∑ c_α q_α = 0` is the genuinely-harder content (and is FALSE without an integrability/structure
condition — e.g. for `Dt = η′·t` it reduces to `∑_α c_α·η′ = 0`, i.e. `∑ c_α = 0`, which is the
exponential-case correction that holds exactly when `a/d` is integrable in the log part alone). We isolate
it as an explicit hypothesis `hcancel` and prove the reduction. -/

omit [Differential K] [Algebra ℚ K] in
/-- **Polynomial over a linear factor splits off its quotient and a simple pole** — in `RatFunc K`,
`algebraMap p / algebraMap (X − C α) = algebraMap(p /ₘ (X − C α)) + algebraMap(C(p.eval α))/algebraMap(X
− C α)`. From `modByMonic_add_div` (`p = C(p.eval α) + (X−Cα)·(p /ₘ (X−Cα))`, using
`modByMonic_X_sub_C_eq_C_eval`). The euclidean split of a proper-or-improper `p/(t−α)` into its polynomial
part and its residue-over-pole. -/
theorem algebraMap_div_X_sub_C_split (p : K[X]) (α : K) :
    algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) (X - C α)
      = algebraMap K[X] (RatFunc K) (p /ₘ (X - C α))
        + algebraMap K[X] (RatFunc K) (C (p.eval α)) / algebraMap K[X] (RatFunc K) (X - C α) := by
  have hsplit : (p : K[X]) = (X - C α) * (p /ₘ (X - C α)) + C (p.eval α) := by
    have := modByMonic_add_div p (X - C α)
    rw [modByMonic_X_sub_C_eq_C_eval] at this
    linear_combination -this
  have hXα : algebraMap K[X] (RatFunc K) (X - C α) ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr (X_sub_C_ne_zero α)
  have hmap : algebraMap K[X] (RatFunc K) p
      = algebraMap K[X] (RatFunc K) (X - C α) * algebraMap K[X] (RatFunc K) (p /ₘ (X - C α))
        + algebraMap K[X] (RatFunc K) (C (p.eval α)) := by
    rw [← map_mul, ← map_add]; exact congrArg _ hsplit
  rw [hmap]
  field_simp

/-- **★★ The general monomial Rothstein–Trager partial fraction, modulo polynomial-part cancellation**
(Bronstein Thm 5.6.1, general monomial) — for a squarefree `d = ∏_{α∈s}(t−α)`, `deg a < #s`, an arbitrary
monomial `Dt = v`, every root normal (`v(α) ≠ α′`), **and** the polynomial parts cancelling
(`hcancel : ∑_{α∈s} C(c_α)·((v − Cα′) /ₘ (t−α)) = 0`), the monomial RT residue sum equals `a/d`:
`∑_{α∈s} C(c_α)·(D(t−α)/(t−α)) = a/d`, `c_α = a(α)/(Dd)(α)`, `D = extendDeriv (implicitDeriv v)`. Per term,
`algebraMap_div_X_sub_C_split` separates the polynomial part `C(c_α)·((v−Cα′)/ₘ(t−α))` from the residue
`C(c_α·(v(α)−α′))/(t−α) = C(a(α)/d′(α))/(t−α)` (`residue_mul_eval_sub_eq`); the residues reassemble `a/d`
(`ratFunc_eq_sum_residue_div`) and the polynomial parts vanish by `hcancel`. The `hcancel` hypothesis is
the genuine extra content for non-primitive (hyperexp/hypertangent) monomials — it is the
integrability-encoding cancellation, automatic only in the primitive case (where each quotient is `0`). -/
theorem monomial_residue_match_of_cancel (s : Finset K) (a v : K[X])
    (hA : a.degree < s.card) (hnorm : ∀ α ∈ s, v.eval α ≠ α′)
    (hcancel : ∑ α ∈ s, algebraMap K[X] (RatFunc K)
        (C (a.eval α / (Differential.implicitDeriv v (Lagrange.nodal s id)).eval α)
          * ((v - C (α′)) /ₘ (X - C α))) = 0) :
    ∑ α ∈ s, algebraMap K[X] (RatFunc K)
          (C (a.eval α / (Differential.implicitDeriv v (Lagrange.nodal s id)).eval α))
        * (extendDeriv (Differential.implicitDeriv v)
              (algebraMap K[X] (RatFunc K) (X - C α))
            / algebraMap K[X] (RatFunc K) (X - C α))
      = algebraMap K[X] (RatFunc K) a / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id) := by
  -- abbreviation for the RT residue at `α`
  set c : K → K := fun α => a.eval α / (Differential.implicitDeriv v (Lagrange.nodal s id)).eval α
    with hc
  -- rewrite each summand: monomial log-derivative, then euclidean split
  have hterm : ∀ α ∈ s,
      algebraMap K[X] (RatFunc K) (C (c α))
          * (extendDeriv (Differential.implicitDeriv v) (algebraMap K[X] (RatFunc K) (X - C α))
              / algebraMap K[X] (RatFunc K) (X - C α))
        = algebraMap K[X] (RatFunc K) (C (c α) * ((v - C (α′)) /ₘ (X - C α)))
          + algebraMap K[X] (RatFunc K) (C (a.eval α / (derivative (Lagrange.nodal s id)).eval α))
              / algebraMap K[X] (RatFunc K) (X - C α) := by
    intro α hα
    rw [extendDeriv_implicitDeriv_logDeriv_X_sub_C, algebraMap_div_X_sub_C_split (v - C (α′)) α,
      mul_add, ← map_mul]
    congr 1
    -- the residue term: `C(c_α)·C((v−Cα′)(α))/(t−α) = C(a(α)/d′(α))/(t−α)`
    rw [eval_sub, eval_C, ← mul_div_assoc, ← map_mul, ← C_mul]
    have hroot : (Lagrange.nodal s id).eval α = 0 := by
      simpa using Lagrange.eval_nodal_at_node (s := s) (v := (id : K → K)) hα
    rw [hc]
    rw [residue_mul_eval_sub_eq a v (Lagrange.nodal s id) α hroot (hnorm α hα)]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← map_sum, hc] at *
  rw [hcancel, zero_add, ← ratFunc_eq_sum_residue_div s a hA]

/-! ### Step 6: the primitive case as a corollary — the cancellation is automatic

For a primitive monomial `Dt = C w`, the polynomial part of each term vanishes: `(C w − Cα′) /ₘ (X−Cα) =
C(w−α′) /ₘ (X−Cα) = 0` (degree `0 < 1`). So `hcancel` holds termwise and `monomial_residue_match_of_cancel`
applies unconditionally — recovering `primitive_monomial_residue_match`. This exhibits the primitive case
as the regime where the genuinely-extra `hcancel` content is free. -/

omit [Algebra ℚ K] in
/-- **Primitive monomials cancel automatically** — for `Dt = C w`, each polynomial part `(C w − Cα′) /ₘ
(X−Cα)` is `0` (a degree-`0` polynomial over the degree-`1` `X − Cα`), so the cancellation hypothesis
`hcancel` of `monomial_residue_match_of_cancel` is satisfied termwise. The primitive case is the regime
where the non-primitive `hcancel` content is automatic. -/
theorem primitive_cancel (s : Finset K) (a : K[X]) (w : K) :
    ∑ α ∈ s, algebraMap K[X] (RatFunc K)
        (C (a.eval α / (Differential.implicitDeriv (C w) (Lagrange.nodal s id)).eval α)
          * ((C w - C (α′)) /ₘ (X - C α))) = 0 := by
  apply Finset.sum_eq_zero
  intro α _
  have hdeg : (C w - C (α′)).degree < (X - C α).degree := by
    rw [degree_X_sub_C]
    calc (C w - C (α′)).degree ≤ max (C w).degree (C (α′)).degree := degree_sub_le _ _
      _ ≤ 0 := max_le degree_C_le degree_C_le
      _ < 1 := by decide
  rw [(divByMonic_eq_zero_iff (monic_X_sub_C α)).mpr hdeg, mul_zero, map_zero]

end ResidueMatchTower

/-! ### Step 7: the primitive RT residue match in the ENGINE's vocabulary

The engine phrases the residue sum over `amG α = algebraMap (CFieldSpec.K α)[X] (RatFunc (CFieldSpec.K α))`
and `towerFractionFieldDerivG Dt = extendDeriv (implicitDeriv (toPolyG Dt))`. Since `amG` is *definitionally*
that `algebraMap` and `towerFractionFieldDerivG` unfolds to the extended derivation, the `K[X]`-level
primitive theorem restates directly over the tower carrier `K = CFieldSpec.K α` with `v = toPolyG Dt`. This
is the Rothstein–Trager residue match in exactly the form the engine's `logResidueSumG_eq_of_residue_match`
consumes — for a *primitive* monomial (`toPolyG Dt = C w`) and the squarefree denominator factored as
`∏(t−α)` over its roots. -/

open Compute CPolyG QFunNZG

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

/-- **★ The primitive RT residue match in the engine's `amG`/`towerFractionFieldDerivG` vocabulary** — for
a primitive monomial with `toPolyG Dt = C w` (`w ∈ CFieldSpec.K α`), a squarefree `d = ∏_{α∈s}(t−α)`,
`deg a < #s`, and every root normal, the engine-shaped residue sum `∑_{α∈s} amG(C(c_α))·(D(t−α)/(t−α)) =
a/d` over `RatFunc (CFieldSpec.K α)`, with `D = towerFractionFieldDerivG Dt`. The `K[X]`-level
`primitive_monomial_residue_match` transported verbatim through the definitional `amG = algebraMap` and the
`towerFractionFieldDerivG` unfolding — the unconditional `hmatch` for primitive (logarithmic) tower
extensions, phrased exactly as the engine consumes it. -/
theorem primitive_monomial_residue_match_engine (Dt : CPolyG α) (s : Finset (CFieldSpec.K α))
    (a : (CFieldSpec.K α)[X]) (w : CFieldSpec.K α) (hDt : toPolyG Dt = C w)
    (hA : a.degree < s.card) (hnorm : ∀ β ∈ s, w ≠ β′) :
    ∑ β ∈ s, amG α
          (C (a.eval β / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β))
        * (towerFractionFieldDerivG Dt (amG α (X - C β)) / amG α (X - C β))
      = amG α a / amG α (Lagrange.nodal s id) := by
  show ∑ β ∈ s, algebraMap (CFieldSpec.K α)[X] (RatFunc (CFieldSpec.K α))
          (C (a.eval β / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β))
        * (extendDeriv (Differential.implicitDeriv (toPolyG Dt))
              (algebraMap _ (RatFunc (CFieldSpec.K α)) (X - C β))
            / algebraMap _ (RatFunc (CFieldSpec.K α)) (X - C β))
      = _
  rw [hDt]
  exact ResidueMatchTower.primitive_monomial_residue_match s a w hA hnorm

/-! ### ★ Status — what is proven, and the precise remaining obstruction

PROVEN (axiom-clean `[propext, Classical.choice, Quot.sound]`, no `native_decide`):
* The ★ Rothstein–Trager **absorption identity** `(Dd)(α) = d′(α)·(v(α) − α′)` at a simple root
  (`ResidueMatchTower.eval_implicitDeriv_of_isRoot`) — the monomial-derivation crux (Bronstein Thm 5.6.1),
  the same gap as the algebraic `isRadicalLogIntegral_of_residue_match`.
* The **primitive-case `hmatch`** unconditionally: `∑ c_α·D(t−α)/(t−α) = a/d` for `Dt = C w`
  (`ResidueMatchTower.primitive_monomial_residue_match`, and in engine vocabulary
  `primitive_monomial_residue_match_engine`). This discharges `hmatch` for primitive (logarithmic) tower
  extensions.
* The **general-case `hmatch` modulo cancellation** (`ResidueMatchTower.monomial_residue_match_of_cancel`):
  for ANY monomial, `∑ c_α·D(t−α)/(t−α) = a/d` GIVEN the polynomial-part cancellation
  `hcancel : ∑ c_α·((v−Cα′) /ₘ (t−α)) = 0`, with `hcancel` automatic in the primitive case
  (`ResidueMatchTower.primitive_cancel`).

PRECISE REMAINING OBSTRUCTION (for the FULL unconditional `hmatch`, all monomials):
1. **The non-primitive polynomial cancellation `∑ c_α·((v−Cα′) /ₘ (t−α)) = 0`** is genuinely extra content,
   NOT a free identity: for `Dt = η′·t` (hyperexponential) it reduces to `∑_α c_α = 0`, the
   exponential-case correction that holds *exactly when* `a/d` is integrable in the log part alone. The
   isolated lemma `monomial_residue_match_of_cancel` pins it; proving it needs the integrability witness the
   engine carries (the resultant having all roots rational AND the leftover proper), routed through a
   degree/`t`-power argument — the analogue of Bronstein's reduction of the hyperexp case.
2. **Engine list↔Finset + grouped-GCD bridge:** the engine's `logResidueSumG_eq_of_residue_match` `hmatch` is
   a `List` sum over grouped args `vᵢ = gcd(d, a−cᵢDd)` (products of equal-residue factors), vs. the
   Finset-over-roots form here. Mathlib's `Finset.sum_fiberwise` regrouping (as in
   `PartialFraction.ratFunc_eq_sum_residue_grouped`) bridges the grouping; the list↔Finset and
   `d = nodal (roots d)` (splitting-field factorization) are mechanical but unwritten. -/

#print axioms ResidueMatchTower.eval_implicitDeriv_of_isRoot
#print axioms ResidueMatchTower.primitive_monomial_residue_match
#print axioms ResidueMatchTower.monomial_residue_match_of_cancel
#print axioms ResidueMatchTower.primitive_cancel
#print axioms primitive_monomial_residue_match_engine

end DeepWiki.SymbolicIntegration
