import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalIntegralSoundness
import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalLogIntegral
import DeepWiki.SymbolicIntegration.Engine.RefinesPolyG
import DeepWiki.ComputableAlgebra.GenericBezout
import DeepWiki.SymbolicIntegration.PartialFraction
import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalAssembly

/-! # Log-part soundness for the radical integrator: `D(Σ cᵢ log uᵢ) = logpart`

The integrator returns `∫f = v + Σ cᵢ log uᵢ`; the log part is sound when
`Σ cᵢ · radDeriv(uᵢ)/uᵢ = logpart`. Since `D(log u) = radDeriv(u)/u`, this is a statement
about residues read in the carrier quotient `K[X] ⧸ radIdeal n ρ = K[X] ⧸ (Xⁿ − C(toK ρ))`,
the coordinate ring of the curve `yⁿ = ρ` (`K = CFieldSpec.K α`). This file provides the
single- and multi-term log-soundness predicates, the certificate-to-predicate bridge, the
additivity of the log-derivative sum, and reduces the residue-correctness core (that the
integrator's log args carry the Rothstein–Trager residues) to named obligations. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open scoped Differential

namespace RadElem

variable {α : Type*} [CField α] [CDiffField α] [CFieldSpec α] [CDiffFieldSpec α]

/-! ### The single-log soundness predicate `IsRadicalLogTerm` and the certificate bridge

`log u` is sound for integrand `g` iff `D(log u) = g`, cross-multiplied to the quotient
identity `mk(toPoly(radDeriv u)) = mk(toPoly u)·mk(toPoly g)` — the genuine-field reading
of the engine's division-free certificate `radIsLogIntegral n ρ u g`. -/

/-- The single-log soundness predicate `IsRadicalLogTerm n ρ u integrand`: `u` is a correct
log argument for `integrand` over `α[y]/(yⁿ − ρ)`, i.e. `D(log u) = integrand` as
`mk(toPoly(radDeriv n ρ u)) = mk(toPoly u)·mk(toPoly integrand)` in `K[X] ⧸ radIdeal n ρ`. -/
def IsRadicalLogTerm (n : ℕ) (ρ : α) (u integrand : RadElem α) : Prop :=
  Ideal.Quotient.mk (radIdeal n ρ) (CPoly.toPoly (radDeriv n ρ u))
    = Ideal.Quotient.mk (radIdeal n ρ) (CPoly.toPoly u)
      * Ideal.Quotient.mk (radIdeal n ρ) (CPoly.toPoly integrand)

omit [CDiffFieldSpec α] in
/-- The engine's log-derivative certificate implies the single-log soundness predicate. -/
theorem isRadicalLogTerm_of_radIsLogIntegral (n : ℕ) (ρ : α) (u integrand : RadElem α)
    (h : radIsLogIntegral n ρ u integrand = true) :
    IsRadicalLogTerm n ρ u integrand := by
  rw [radIsLogIntegral, radIsZero, radSub] at h
  have hderiv :
      CPoly.toPoly (radDeriv n ρ u) = CPoly.toPoly (radMul n ρ u integrand) :=
    RefinesPolyG.eq_of_csub_cisZero (refinesPolyG_self _) (refinesPolyG_self _) h
  -- `toPoly(radDeriv u) = toPoly(radMul u integrand)` in `K[X]`; push through `mk` and read
  -- `mk(toPoly(radMul u integrand)) = mk(toPoly u)·mk(toPoly integrand)` (the quotient product).
  rw [IsRadicalLogTerm, hderiv, mk_toPolyG_radMul]

/-! ### The log-derivative sum is `radDeriv`-additive

`D(Σ cᵢ log uᵢ) = Σ cᵢ · radDeriv(uᵢ)/uᵢ`. The numerator-sum `radDeriv` distributes over the
`radAdd`-fold of the scaled contributions, the additivity floor for the multi-term log sum. -/

/-- The scaled `radDeriv`-contribution of one log term `radLogTermDeriv n ρ (c, u) =
radScale c (radDeriv n ρ u)` — the numerator of `c · radDeriv(u)/u` before dividing by `u`. -/
def radLogTermDeriv (n : ℕ) (ρ : α) (cu : α × RadElem α) : RadElem α :=
  radScale cu.1 (radDeriv n ρ cu.2)

/-- `radDeriv` distributes over a scaled `radAdd`-fold: `toPoly (radDeriv n ρ
(cs.foldl radAdd acc)) = toPoly (radDeriv n ρ acc) + Σ_{c∈cs} toPoly (radDeriv n ρ c)`. -/
theorem toPolyG_radDeriv_logFold (n : ℕ) (ρ : α) (acc : RadElem α) (cs : List (RadElem α)) :
    CPoly.toPoly (radDeriv n ρ (cs.foldl radAdd acc))
      = CPoly.toPoly (radDeriv n ρ acc)
        + (cs.map (fun c => CPoly.toPoly (radDeriv n ρ c))).sum :=
  toPolyG_radDeriv_foldlRadAdd n ρ acc cs

/-! ### The two-term log-derivative sum over the common denominator `u₁ u₂`

The numerator of `c₁·radDeriv(u₁)/u₁ + c₂·radDeriv(u₂)/u₂` over `u₁·u₂` is
`c₁·radDeriv(u₁)·u₂ + c₂·u₁·radDeriv(u₂)`, the two-term head of the residue sum. -/

/-- The two-term log-derivative numerator `radLogSum2 n ρ c₁ u₁ c₂ u₂ =
radAdd (radMul (radScale c₁ (radDeriv u₁)) u₂) (radMul (radScale c₂ (radDeriv u₂)) u₁)`: the
numerator of `c₁·D(log u₁) + c₂·D(log u₂)` over the common denominator `u₁·u₂`. -/
def radLogSum2 (n : ℕ) (ρ : α) (c₁ : α) (u₁ : RadElem α) (c₂ : α) (u₂ : RadElem α) : RadElem α :=
  radAdd (radMul n ρ (radScale c₁ (radDeriv n ρ u₁)) u₂)
    (radMul n ρ (radScale c₂ (radDeriv n ρ u₂)) u₁)

omit [CDiffFieldSpec α] in
/-- Two log residues add (quotient form): `mk(toPoly(radLogSum2 c₁ u₁ c₂ u₂)) =
c₁·mk(radDeriv u₁)·mk(u₂) + c₂·mk(radDeriv u₂)·mk(u₁)` in `K[X] ⧸ radIdeal n ρ` (`cᵢ` read as
`C(toK cᵢ)`). -/
theorem mk_toPolyG_radLogSum2 (n : ℕ) (ρ : α) (c₁ : α) (u₁ : RadElem α) (c₂ : α) (u₂ : RadElem α) :
    Ideal.Quotient.mk (radIdeal n ρ) (CPoly.toPoly (radLogSum2 n ρ c₁ u₁ c₂ u₂))
      = Polynomial.C (CFieldSpec.toK c₁)
          * Ideal.Quotient.mk (radIdeal n ρ) (CPoly.toPoly (radDeriv n ρ u₁))
          * Ideal.Quotient.mk (radIdeal n ρ) (CPoly.toPoly u₂)
        + Polynomial.C (CFieldSpec.toK c₂)
          * Ideal.Quotient.mk (radIdeal n ρ) (CPoly.toPoly (radDeriv n ρ u₂))
          * Ideal.Quotient.mk (radIdeal n ρ) (CPoly.toPoly u₁) := by
  simp only [radLogSum2, radAdd, denote, map_add, mk_toPolyG_radMul, radScale, map_mul]

end RadElem

/-! ### A concrete single-log integral: `D(log √f) = f'/(nf)`

The generator `u = radGen = √f = [0,1]` has `radDeriv radGen = ℓ·y` (`ℓ = logDerRadicand n f`)
and `radGen = y`, so `D(log √f) = ℓ = f'/(nf)`, the constant integrand `[ℓ]`. -/

namespace RadElem

variable {α : Type*} [CField α] [CDiffField α] [CFieldSpec α] [CDiffFieldSpec α]

/-- `toPoly (radDeriv n f radGen) = C(toK ℓ)·X`: the generator's derivative is `ℓ·y`
(`ℓ = logDerRadicand n f`), read through `toPoly`. -/
@[denote] theorem toPolyG_radDeriv_radGen_eq (n : ℕ) (f : α) :
    CPoly.toPoly (radDeriv n f (radGen : RadElem α))
      = Polynomial.C (CFieldSpec.toK (logDerRadicand n f)) * X := by
  rw [toPolyG_radDeriv_radGen, toPolyG_zero_cons]

/-- `D(log √f) = f'/(nf)` as a single-log soundness instance:
`IsRadicalLogTerm n [f].headD radGen [ℓ]` with `ℓ = logDerRadicand n f` — `u = √f = [0,1]` is a
correct log argument for the constant integrand `[ℓ]` in `K[X] ⧸ radIdeal n f`, unconditionally. -/
theorem isRadicalLogTerm_radGen (n : ℕ) (f : α) :
    IsRadicalLogTerm n (([f] : RadElem α).headD CField.zero) (radGen : RadElem α)
      ([logDerRadicand n f] : RadElem α) := by
  rw [IsRadicalLogTerm, List.headD_cons]
  -- the integrand `[ℓ]` reads as `C(toK ℓ)`; `radGen` reads as `X`; `radDeriv radGen` reads as `C(toK ℓ)·X`
  have hint : CPoly.toPoly ([logDerRadicand n f] : RadElem α) = Polynomial.C (CFieldSpec.toK
      (logDerRadicand n f)) := by
    simp only [denote, mul_zero, add_zero]
  rw [toPolyG_radDeriv_radGen_eq, toPolyG_radGen, hint, ← map_mul]
  -- `C(toK ℓ)·X = X·C(toK ℓ)` in `K[X]`, pushed through `mk` (commutativity)
  rw [mul_comm X]

end RadElem

/-! ### The residue-correctness core

The residue-correctness core `Σ cᵢ radDeriv(uᵢ)/uᵢ = logpart` (that the integrator's log args
carry the residues `cAlgResidueResultant` computes) is organized around three ingredients, all proven
below:

1. the residue-resultant root ↔ residue correspondence — the roots of the double resultant are
   the two-sheet residues `(g₀(α) ± g₁(α)√ρ(α))/D'(α)` (`roots_residueResultant_eq_residues`),
   with the engine compute-bridge `toPolyG_cAlgResidueResultant_eq_of_eval`;
2. the logarithmic-derivative residue equals the vanishing order
   (`logDeriv_residue_eq_multiplicity`);
3. the residue-sum numerator distributes over the args list
   (`mk_toPolyG_radLogSumNum_eq_sum`), composing to `isRadicalLogIntegral_of_residue_match`
   with the per-term match discharged by the algebraic partial fraction
   (`ratFunc_eq_sum_residue_logDeriv`).

`isAlgebraicIntegral_of_parts` then composes the rational and log parts into the full
`D(∫f) = f`, with the integrand split discharged for the driver by
`toPolyG_algDeriv_eq_of_roundtrip`. -/

namespace RadElem

variable {α : Type*} [CField α] [CDiffField α] [CFieldSpec α] [CDiffFieldSpec α]

/-- The residue-sum numerator over a cofactor list `radLogSumNum n ρ args cofs` — the numerator
of `Σᵢ cᵢ·radDeriv(uᵢ)/uᵢ` over `∏ⱼ uⱼ`: the `radAdd`-fold of the per-term contributions
`cᵢ·radDeriv(uᵢ)·cofᵢ` (`cofᵢ = ∏_{j≠i} uⱼ`). -/
def radLogSumNum (n : ℕ) (ρ : α) (args : List (α × RadElem α)) (cofs : List (RadElem α)) : RadElem α :=
  ((args.zip cofs).map (fun p =>
    radMul n ρ (radScale p.1.1 (radDeriv n ρ p.1.2)) p.2)).foldl radAdd radZero

/-- The multi-term log-soundness predicate `IsRadicalLogIntegral n ρ logpart args cofs` — the
log-derivative sum `Σ cᵢ·radDeriv(uᵢ)/uᵢ` equals `logpart` over `α[y]/(yⁿ − ρ)`, cross-
multiplied by `commonDenomQ = ∏ⱼ uⱼ`: `mk(radLogSumNum) = mk(logpart·commonDenomQ)`. -/
def IsRadicalLogIntegral (n : ℕ) (ρ : α) (logpart commonDenomQ : RadElem α)
    (args : List (α × RadElem α)) (cofs : List (RadElem α)) : Prop :=
  Ideal.Quotient.mk (radIdeal n ρ) (CPoly.toPoly (radLogSumNum n ρ args cofs))
    = Ideal.Quotient.mk (radIdeal n ρ) (CPoly.toPoly (radMul n ρ logpart commonDenomQ))

omit [CDiffFieldSpec α] in
/-- The residue-sum numerator of the empty log part is `0` in the quotient:
`mk(toPoly(radLogSumNum n ρ [] cofs)) = 0`. -/
theorem mk_toPolyG_radLogSumNum_nil (n : ℕ) (ρ : α) (cofs : List (RadElem α)) :
    Ideal.Quotient.mk (radIdeal n ρ) (CPoly.toPoly (radLogSumNum n ρ [] cofs)) = 0 := by
  -- `[].zip cofs = []`, so the fold collapses to the seed `radZero = []` (definitional)
  show Ideal.Quotient.mk (radIdeal n ρ) (CPoly.toPoly (radZero : RadElem α)) = 0
  show Ideal.Quotient.mk (radIdeal n ρ) (CPoly.toPoly ([] : RadElem α)) = 0
  rw [CPoly.toPolyG_nil, map_zero]

end RadElem

/-! ### Logarithmic-derivative residues at the base-field level

The residue of `u'/u` at a root equals the vanishing order (the logarithmic-derivative residue
theorem). Its algebraic heart is a `K[X]` fact: for `u = (X − a)^m · v` with `v(a) ≠ 0`, the
residue of `u'/u` at `a` is `m`. Landed in two forms: the derivative factorization and the
residue value. -/

namespace LogResidue

variable {K : Type*} [Field K]

/-- The derivative factorization at a root of multiplicity `m`: for `u = (X − a)^m·v` with
`m ≥ 1`, `derivative u = (X − a)^{m−1}·(C m·v + (X − a)·derivative v)`. -/
theorem derivative_X_sub_C_pow_mul (a : K) (m : ℕ) (hm : 1 ≤ m) (v : K[X]) :
    derivative ((Polynomial.X - Polynomial.C a) ^ m * v)
      = (Polynomial.X - Polynomial.C a) ^ (m - 1)
        * (Polynomial.C (m : K) * v + (Polynomial.X - Polynomial.C a) * derivative v) := by
  rw [derivative_mul, derivative_X_sub_C_pow]
  -- `(X−a)^m = (X−a)·(X−a)^{m−1}`, then factor `(X−a)^{m−1}` out of both summands
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel, pow_succ]
  ring

/-- The logarithmic-derivative residue is the multiplicity: for `u = (X − a)^m·v` with `m ≥ 1`
and `v(a) ≠ 0`, `(C m·v + (X − a)·v').eval a / v.eval a = (m : K)`. -/
theorem logDeriv_residue_eq_multiplicity (a : K) (m : ℕ) (v : K[X])
    (hv : v.eval a ≠ 0) :
    (Polynomial.C (m : K) * v + (Polynomial.X - Polynomial.C a) * derivative v).eval a / v.eval a
      = (m : K) := by
  -- evaluate the residue numerator `C m·v + (X−a)·v'` at `a`: the `(X−a)` term vanishes
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, sub_self, zero_mul, add_zero]
  rw [mul_div_assoc, div_self hv, mul_one]

/-! #### The norm quadratic factors into the two-sheet residues

Each per-root norm factor `norm(α, Z) = (Z·D'(α) − g₀(α))² − g₁(α)²·ρ(α)` is a quadratic in `Z`
that splits into the two-sheet residues; we prove that `K[Z]`-factoring here. -/

/-- The residue-norm quadratic factors into the two-sheet residues: over `K` with `c ≠ 0` and
`s² = h²·r`, `(Z·c − g)² − h²·r = C(c)²·(Z − C r₊)·(Z − C r₋)` with `r± = (g ± s)/c` (the two
residues `(g₀(α) ± g₁(α)√ρ(α))/D'(α)`). -/
theorem residueNorm_factor (c g h r s : K) (hc : c ≠ 0) (hs : s ^ 2 = h ^ 2 * r) :
    (Polynomial.X * Polynomial.C c - Polynomial.C g) ^ 2 - Polynomial.C (h ^ 2 * r)
      = Polynomial.C c ^ 2
        * (Polynomial.X - Polynomial.C ((g + s) / c))
        * (Polynomial.X - Polynomial.C ((g - s) / c)) := by
  -- the two residue roots `r± = (g ± s)/c` satisfy `c·r± = g ± s` (clearing `c`)
  have hr1 : c * ((g + s) / c) = g + s := by rw [mul_div_cancel₀ _ hc]
  have hr2 : c * ((g - s) / c) = g - s := by rw [mul_div_cancel₀ _ hc]
  -- read `C (h²·r) = C (s²)`; the whole identity becomes a `C`-image of a base-field quadratic identity
  rw [← hs]
  -- introduce the abbreviations `p₊ = C((g+s)/c)`, `p₋ = C((g-s)/c)` and the products `C c · p± = C(c·r±)`
  have hcp1 : Polynomial.C c * Polynomial.C ((g + s) / c) = Polynomial.C (g + s) := by
    rw [← map_mul, hr1]
  have hcp2 : Polynomial.C c * Polynomial.C ((g - s) / c) = Polynomial.C (g - s) := by
    rw [← map_mul, hr2]
  -- `C c² · (X − p₊)(X − p₋) = X²·C c² − X·C c·(C c·p₊ + C c·p₋) + (C c·p₊)(C c·p₋)`
  have expand : Polynomial.C c ^ 2
      * (Polynomial.X - Polynomial.C ((g + s) / c))
      * (Polynomial.X - Polynomial.C ((g - s) / c))
    = Polynomial.X ^ 2 * Polynomial.C c ^ 2
      - Polynomial.X * Polynomial.C c
          * (Polynomial.C c * Polynomial.C ((g + s) / c)
            + Polynomial.C c * Polynomial.C ((g - s) / c))
      + (Polynomial.C c * Polynomial.C ((g + s) / c))
          * (Polynomial.C c * Polynomial.C ((g - s) / c)) := by ring
  rw [expand, hcp1, hcp2]
  -- now a pure `C`-image identity: `(X·C c − C g)² − C(s²) = X²·C c² − X·C c·(C(g+s)+C(g-s)) + C(g+s)·C(g-s)`
  simp only [map_add, map_sub, map_pow]
  ring

/-! #### Per-root and product root-sets

`roots_residueNorm` reads off the per-root root multiset `{r₊, r₋}`;
`roots_residueResultant_eq_residues` assembles them over all roots `α` of `D` from the
`resultant_eq_prod_eval` product form. -/

/-- The per-root residue-norm has root multiset `{r₊, r₋}`: for `c ≠ 0` and `s² = h²·r`, the
roots of `(Z·c − g)² − h²·r` are `{(g + s)/c, (g − s)/c}`. -/
theorem roots_residueNorm (c g h r s : K) (hc : c ≠ 0) (hs : s ^ 2 = h ^ 2 * r) :
    ((Polynomial.X * Polynomial.C c - Polynomial.C g) ^ 2 - Polynomial.C (h ^ 2 * r)).roots
      = {(g + s) / c, (g - s) / c} := by
  rw [residueNorm_factor c g h r s hc hs, mul_assoc]
  -- `(C c²)·((Z − r₊)·(Z − r₋))`: read `C c ^ 2 = C (c²)`, drop the leading scalar (nonzero)
  rw [show (Polynomial.C c : K[X]) ^ 2 = Polynomial.C (c ^ 2) from (map_pow _ _ _).symm,
    Polynomial.roots_C_mul _ (pow_ne_zero 2 hc)]
  -- split the product of two monic linear factors
  rw [Polynomial.roots_mul (by
    refine mul_ne_zero ?_ ?_ <;> exact Polynomial.X_sub_C_ne_zero _),
    Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C]
  rfl

/-- The residue resultant's roots are the two-sheet residues: given the product form
`R = C(lc)^N · ∏_{α ∈ Droots} norm(α, Z)` (with `sqrtρ α` a square root of `g₁(α)²·ρ(α)` and
`D'(α) ≠ 0`), `R.roots = Droots.bind (fun α => {r₊(α), r₋(α)})` with
`r±(α) = (g₀(α) ± g₁(α)√ρ(α))/D'(α)`. -/
theorem roots_residueResultant_eq_residues (lc : K) (N : ℕ) (Droots : Multiset K)
    (Dprime g0 g1 rho : K → K) (sqrtρ : K → K)
    (hlc : lc ≠ 0)
    (hsqrt : ∀ α ∈ Droots, (sqrtρ α) ^ 2 = (g1 α) ^ 2 * rho α)
    (hDp : ∀ α ∈ Droots, Dprime α ≠ 0)
    (R : K[X])
    (hR : R = Polynomial.C lc ^ N
      * (Droots.map (fun α =>
          (Polynomial.X * Polynomial.C (Dprime α) - Polynomial.C (g0 α)) ^ 2
            - Polynomial.C ((g1 α) ^ 2 * rho α))).prod) :
    R.roots = Droots.bind (fun α =>
      {(g0 α + sqrtρ α) / Dprime α, (g0 α - sqrtρ α) / Dprime α}) := by
  subst hR
  -- drop the nonzero leading scalar `C lc^N` (`C lc ≠ 0`, `lc ≠ 0`)
  rw [show (Polynomial.C lc : K[X]) ^ N = Polynomial.C (lc ^ N) from (map_pow _ _ _).symm,
    Polynomial.roots_C_mul _ (pow_ne_zero N hlc)]
  -- the product's roots are the `bind` of the per-factor roots (no factor is `0`: each is a degree-2 poly)
  rw [Polynomial.roots_multiset_prod _ (by
    -- `0 ∉ map (norm ·) Droots`: each norm factor is nonzero (its roots are 2 residues, so it ≠ 0)
    rw [Multiset.mem_map]
    rintro ⟨α, hα, hα0⟩
    -- if `norm α = 0` its root multiset would be `0`, contradicting `roots_residueNorm = {r₊,r₋}`
    have hroots := roots_residueNorm (Dprime α) (g0 α) (g1 α) (rho α) (sqrtρ α)
      (hDp α hα) (hsqrt α hα)
    rw [hα0, Polynomial.roots_zero] at hroots
    exact absurd hroots.symm (by simp [Multiset.insert_eq_cons]))]
  -- per-factor: `roots(norm α) = {r₊(α), r₋(α)}` (the two residues)
  rw [Multiset.bind_map]
  refine Multiset.bind_congr (fun α hα => ?_)
  exact roots_residueNorm (Dprime α) (g0 α) (g1 α) (rho α) (sqrtρ α) (hDp α hα) (hsqrt α hα)

end LogResidue

/-! ### Input (a): the compute-bridge `cAlgResidueResultant`-node ↔ `Polynomial.resultant`

Connecting the abstract product form to the engine's `cAlgResidueResultant` (which interpolates
over `Z`-nodes): at each node `Z = c` the engine's univariate resultant reads through `toK` as
`Polynomial.resultant (toPoly (cAlgResidueNorm …)) (toPoly D)`. Interpolation-uniqueness over
the nodes then assembles the full bridge. -/

namespace CPoly

variable {α : Type*} [CField α] [CDiffField α] [CFieldSpec α] [CDiffFieldSpec α]

omit [CDiffField α] [CDiffFieldSpec α] in
/-- The residue-norm reads through `toPoly` as the abstract norm: `toPoly (cAlgResidueNorm D'
ρ g₀ g₁ c) = (C(toK c)·toPoly D' − toPoly g₀)² − toPoly g₁²·toPoly ρ` in `K[X]`. -/
theorem toPolyG_cAlgResidueNorm (Dprime rho g0 g1 : CPoly α) (c : α) :
    CPoly.toPoly (CPoly.cAlgResidueNorm Dprime rho g0 g1 c)
      = (Polynomial.C (CFieldSpec.toK c) * CPoly.toPoly Dprime - CPoly.toPoly g0) ^ 2
        - CPoly.toPoly g1 ^ 2 * CPoly.toPoly rho := by
  simp only [cAlgResidueNorm, denote]
  ring

omit [CDiffField α] [CDiffFieldSpec α] in
/-- Compute-bridge, per node: at a node `Z = c`, the engine's univariate resultant of the
residue-norm against `D` reads through `toK` as `Polynomial.resultant (toPoly (cAlgResidueNorm
…)) (toPoly D) (cdeg (cAlgResidueNorm …)) (cdeg D)`. -/
theorem toK_cresultantG_cAlgResidueNorm (Dprime rho g0 g1 D : CPoly α) (c : α) :
    CFieldSpec.toK (CPoly.cresultantWf (CPoly.cAlgResidueNorm Dprime rho g0 g1 c) D)
      = Polynomial.resultant (CPoly.toPoly (CPoly.cAlgResidueNorm Dprime rho g0 g1 c))
          (CPoly.toPoly D) (CPoly.cdeg (CPoly.cAlgResidueNorm Dprime rho g0 g1 c))
          (CPoly.cdeg D) :=
  CPoly.toPolyG_cresultantWf (CPoly.cAlgResidueNorm Dprime rho g0 g1 c) D

/-! #### Input (a): the interpolation-uniqueness characterization of `cAlgResidueResultant`

The engine `cAlgResidueResultant` interpolates the values `res_X(cAlgResidueNorm D' ρ g₀ g₁ k, D)`
over the `Z`-nodes `k = 0, …, 2·deg D`, so by Lagrange uniqueness it is the unique polynomial of
degree `< 2·deg D + 2` with those node values. -/

omit [CDiffField α] [CDiffFieldSpec α] in
/-- The interpolation-uniqueness characterization of `cAlgResidueResultant`: if `R : K[Z]` has
`degree < 2·(toPoly D).natDegree + 2` and its value at each node `k` is the per-node abstract
resultant, then `toPoly (cAlgResidueResultant fuel D ρ g₀ g₁) = R`. -/
theorem toPolyG_cAlgResidueResultant_eq_of_eval (D rho g0 g1 : CPoly α)
    (R : (CFieldSpec.K α)[X])
    (hRdeg : R.degree < (2 * (CPoly.toPoly D).natDegree + 2 : ℕ))
    (hinj : Set.InjOn (fun k : ℕ => CFieldSpec.toK (CPoly.cnatCast (α := α) k))
      (Finset.range (2 * CPoly.cdeg D + 1 + 1)))
    (hnode : ∀ k ∈ Finset.range (2 * CPoly.cdeg D + 1 + 1),
      R.eval (CFieldSpec.toK (CPoly.cnatCast (α := α) k))
        = CFieldSpec.toK (CPoly.cresultantWf
            (CPoly.cAlgResidueNorm (CPoly.cderiv D) rho g0 g1 (CPoly.cnatCast k)) D)) :
    CPoly.toPoly (CPoly.cAlgResidueResultant D rho g0 g1) = R := by
  classical
  -- the engine builds `cAlgResidueResultant = cinterpolate pts` over the `Z`-nodes
  set Dprime := CPoly.cderiv D with hDp
  set pts : List (α × α) :=
    (List.range (2 * CPoly.cdeg D + 1 + 1)).map (fun k =>
      (CPoly.cnatCast (α := α) k,
        CPoly.cresultantWf (CPoly.cAlgResidueNorm Dprime rho g0 g1 (CPoly.cnatCast k)) D))
    with hpts
  have hcompute : CPoly.cAlgResidueResultant D rho g0 g1 = CPoly.cinterpolate pts := rfl
  -- node-image list and its distinctness
  have hfst : pts.map (fun p => CFieldSpec.toK p.1)
      = (List.range (2 * CPoly.cdeg D + 1 + 1)).map
          (fun k => CFieldSpec.toK (CPoly.cnatCast (α := α) k)) := by
    rw [hpts, List.map_map]; rfl
  have hnodup : (pts.map (fun p => CFieldSpec.toK p.1)).Nodup := by
    rw [hfst]
    rw [List.nodup_map_iff_inj_on (List.nodup_range)]
    intro a ha b hb hab
    exact hinj (by simpa using ha) (by simpa using hb) hab
  have hne : pts ≠ [] := by rw [hpts]; simp [List.range_succ]
  have hlen : pts.length = 2 * CPoly.cdeg D + 1 + 1 := by
    rw [hpts, List.length_map, List.length_range]
  rw [hcompute]
  -- Lagrange uniqueness: degree `< #nodes` both sides, and they agree at the nodes
  refine Polynomial.eq_of_degrees_lt_of_eval_index_eq (R := CFieldSpec.K α) (ι := ℕ)
    (s := Finset.range (2 * CPoly.cdeg D + 1 + 1))
    (v := fun k => CFieldSpec.toK (CPoly.cnatCast (α := α) k))
    (f := CPoly.toPoly (CPoly.cinterpolate pts)) (g := R) hinj ?_ ?_ ?_
  · -- `degree (toPoly (cinterpolate pts)) < #nodes`
    rw [Finset.card_range, Nat.cast_withBot]
    have := CPoly.degree_toPolyG_cinterpolateG_lt pts hne
    rw [hlen] at this
    simpa [Nat.cast_withBot] using this
  · -- `degree R < #nodes`: `2·deg D + 2 = #nodes` (`cdeg D = (toPoly D).natDegree`)
    rw [Finset.card_range, Nat.cast_withBot]
    have hcd : CPoly.cdeg D = (CPoly.toPoly D).natDegree := CPoly.cdegG_eq_natDegree D
    have hcard : (2 * CPoly.cdeg D + 1 + 1 : ℕ) = (2 * (CPoly.toPoly D).natDegree + 2 : ℕ) := by
      rw [hcd]
    rw [hcard]
    exact hRdeg
  · -- agree at the nodes: `toPoly(cinterpolate pts)(k) = node value = R(k)`
    intro k hk
    have hmem : (CPoly.cnatCast (α := α) k,
        CPoly.cresultantWf (CPoly.cAlgResidueNorm Dprime rho g0 g1 (CPoly.cnatCast k)) D)
        ∈ pts := by
      rw [hpts, List.mem_map]; exact ⟨k, by simpa using hk, rfl⟩
    rw [CPoly.eval_toPolyG_cinterpolateG pts hnodup hmem]
    exact (hnode k hk).symm

end CPoly

/-! ### Input (b): the per-term match is the algebraic partial fraction

The claim `logpart = Σᵢ cᵢ·radDeriv(uᵢ)/uᵢ` is the Bernoulli/Lagrange partial-fraction
decomposition, available as the algebraic identity `PartialFraction.ratFunc_eq_sum_residue_logDeriv`
over `K(x)`: `A/D = Σ_{α∈s} (A(α)/D'(α)) · logDeriv(X − α)` for squarefree `D`, `deg A < #s`.
After rationalizing the radical log part to `ℚ(x)`, the residue sum is exactly its partial
fraction, with the `cᵢ` the partial-fraction coefficients. -/

/-! ### Residue-sum telescoping over the pole list

The structural half of obligation 3: the residue-sum numerator `radLogSumNum` is a `radAdd`-fold
of per-term contributions, so `mk(radLogSumNum)` distributes over the args list as a sum of the
per-term `mk(cᵢ·radDeriv(uᵢ)·cofᵢ)`, leaving the per-term partial-fraction match as the isolated
hypothesis. -/

namespace RadElem

variable {α : Type*} [CField α] [CDiffField α] [CFieldSpec α] [CDiffFieldSpec α]

omit [CDiffFieldSpec α] in
/-- The residue-sum numerator distributes over the args list:
`mk(toPoly(radLogSumNum n ρ args cofs)) = Σ_{(cu,cof) ∈ args.zip cofs}
mk(toPoly(cᵢ·radDeriv(uᵢ)·cofᵢ))` in `K[X] ⧸ radIdeal n ρ`. -/
theorem mk_toPolyG_radLogSumNum_eq_sum (n : ℕ) (ρ : α) (args : List (α × RadElem α))
    (cofs : List (RadElem α)) :
    Ideal.Quotient.mk (radIdeal n ρ) (CPoly.toPoly (radLogSumNum n ρ args cofs))
      = ((args.zip cofs).map (fun p =>
          Ideal.Quotient.mk (radIdeal n ρ)
            (CPoly.toPoly (radMul n ρ (radScale p.1.1 (radDeriv n ρ p.1.2)) p.2)))).sum := by
  rw [radLogSumNum]
  -- the fold of `radAdd` maps, under `mk ∘ toPoly`, to the sum of the per-term `mk(toPoly ·)`
  set terms := (args.zip cofs).map (fun p =>
    radMul n ρ (radScale p.1.1 (radDeriv n ρ p.1.2)) p.2) with hterms
  -- generalize: `mk(toPoly(terms.foldl radAdd acc)) = mk(toPoly acc) + Σ mk(toPoly ·)`
  have hfold : ∀ (ts : List (RadElem α)) (acc : RadElem α),
      Ideal.Quotient.mk (radIdeal n ρ) (CPoly.toPoly (ts.foldl radAdd acc))
        = Ideal.Quotient.mk (radIdeal n ρ) (CPoly.toPoly acc)
          + (ts.map (fun t => Ideal.Quotient.mk (radIdeal n ρ) (CPoly.toPoly t))).sum := by
    intro ts
    induction ts with
    | nil => intro acc; simp
    | cons t ts ih =>
      intro acc
      rw [List.foldl_cons, ih (radAdd acc t), radAdd]
      simp only [denote, map_add, List.map_cons, List.sum_cons]
      ring
  rw [hfold terms radZero]
  show Ideal.Quotient.mk (radIdeal n ρ) (CPoly.toPoly (radZero : RadElem α)) + _ = _
  rw [show (radZero : RadElem α) = ([] : RadElem α) from rfl, CPoly.toPolyG_nil, map_zero, zero_add,
    hterms, List.map_map]
  rfl

/-! ### Composing to `IsRadicalLogIntegral` soundness

Given the per-term residue match (the sum of per-term quotient values equals
`mk(logpart·commonDenomQ)`, the algebraic partial fraction), the structural fold composes to the
integrator's log-part soundness `IsRadicalLogIntegral`. -/

omit [CDiffFieldSpec α] in
/-- The log-part soundness composes from the per-term residue match: given the residue-match
hypothesis `hmatch` (the per-term sum equals `mk(logpart·commonDenomQ)`), the integrator's log
part is log-sound (`IsRadicalLogIntegral n ρ logpart commonDenomQ args cofs`). -/
theorem isRadicalLogIntegral_of_residue_match (n : ℕ) (ρ : α)
    (logpart commonDenomQ : RadElem α) (args : List (α × RadElem α)) (cofs : List (RadElem α))
    (hmatch : ((args.zip cofs).map (fun p =>
          Ideal.Quotient.mk (radIdeal n ρ)
            (CPoly.toPoly (radMul n ρ (radScale p.1.1 (radDeriv n ρ p.1.2)) p.2)))).sum
        = Ideal.Quotient.mk (radIdeal n ρ) (CPoly.toPoly (radMul n ρ logpart commonDenomQ))) :
    IsRadicalLogIntegral n ρ logpart commonDenomQ args cofs := by
  rw [IsRadicalLogIntegral, mk_toPolyG_radLogSumNum_eq_sum, hmatch]

omit [CDiffFieldSpec α] in
/-- A single-log instance composes to `IsRadicalLogIntegral`: for `args = [(c, u)]`, `cofs =
[cof]`, if `c·radDeriv(u)·cof = logpart·commonDenomQ` in the quotient, then the log part is
log-sound. -/
theorem isRadicalLogIntegral_singleton (n : ℕ) (ρ : α)
    (logpart commonDenomQ : RadElem α) (c : α) (u cof : RadElem α)
    (hmatch : Ideal.Quotient.mk (radIdeal n ρ)
          (CPoly.toPoly (radMul n ρ (radScale c (radDeriv n ρ u)) cof))
        = Ideal.Quotient.mk (radIdeal n ρ) (CPoly.toPoly (radMul n ρ logpart commonDenomQ))) :
    IsRadicalLogIntegral n ρ logpart commonDenomQ [(c, u)] [cof] := by
  apply isRadicalLogIntegral_of_residue_match
  -- `[(c,u)].zip [cof] = [((c,u), cof)]`, so the sum is the single term
  simpa using hmatch

/-! ### Composing rational + log into the full algebraic integral soundness `D(∫f) = f`

The integrator returns `⟨v, args⟩`, so `∫f = v + Σ cᵢ log uᵢ` and the full soundness splits into
the rational part (`radDeriv(v) = ratPart(f)`, telescoping) and the log part
(`Σ cᵢ·radDeriv(uᵢ)/uᵢ = logPart(f)`, `IsRadicalLogIntegral`). Cross-multiplied by
`commonDenomQ = ∏ uⱼ`, the full identity is the sum of the two halves. -/

/-- The full algebraic-integral soundness predicate `IsAlgebraicIntegral n ρ f v commonDenomQ args
cofs` — `D(v + Σ cᵢ log uᵢ) = f` over `α[y]/(yⁿ − ρ)`, cross-multiplied by `commonDenomQ = ∏ uⱼ`:
`mk(toPoly(radDeriv v · commonDenomQ)) + mk(toPoly(radLogSumNum args cofs)) =
mk(toPoly(f · commonDenomQ))`. -/
def IsAlgebraicIntegral (n : ℕ) (ρ : α) (f v commonDenomQ : RadElem α)
    (args : List (α × RadElem α)) (cofs : List (RadElem α)) : Prop :=
  Ideal.Quotient.mk (radIdeal n ρ) (CPoly.toPoly (radMul n ρ (radDeriv n ρ v) commonDenomQ))
    + Ideal.Quotient.mk (radIdeal n ρ) (CPoly.toPoly (radLogSumNum n ρ args cofs))
  = Ideal.Quotient.mk (radIdeal n ρ) (CPoly.toPoly (radMul n ρ f commonDenomQ))

omit [CDiffFieldSpec α] in
/-- The full algebraic integral `D(∫f) = f` composes from the rational + log soundness: given
`hrat` (rational-part soundness), `hlog` (`IsRadicalLogIntegral`), and `hsplit` (the integrand
split `f = ratPart + logPart`), the output satisfies `IsAlgebraicIntegral n ρ f v commonDenomQ
args cofs`. -/
theorem isAlgebraicIntegral_of_parts (n : ℕ) (ρ : α)
    (f v ratPart logPart commonDenomQ : RadElem α)
    (args : List (α × RadElem α)) (cofs : List (RadElem α))
    (hrat : Ideal.Quotient.mk (radIdeal n ρ)
          (CPoly.toPoly (radMul n ρ (radDeriv n ρ v) commonDenomQ))
        = Ideal.Quotient.mk (radIdeal n ρ) (CPoly.toPoly (radMul n ρ ratPart commonDenomQ)))
    (hlog : IsRadicalLogIntegral n ρ logPart commonDenomQ args cofs)
    (hsplit : Ideal.Quotient.mk (radIdeal n ρ) (CPoly.toPoly (radMul n ρ ratPart commonDenomQ))
        + Ideal.Quotient.mk (radIdeal n ρ) (CPoly.toPoly (radMul n ρ logPart commonDenomQ))
      = Ideal.Quotient.mk (radIdeal n ρ) (CPoly.toPoly (radMul n ρ f commonDenomQ))) :
    IsAlgebraicIntegral n ρ f v commonDenomQ args cofs := by
  -- `radDeriv(v)·cd = ratPart·cd` (rational) and `radLogSumNum = logPart·cd` (log); sum = `f·cd` (split)
  rw [IsAlgebraicIntegral, hrat, hlog, hsplit]

end RadElem

/-! ### Input (b): discharging the integrand split for the `cIntegrateAlgebraic` driver

For the actual driver, the `hsplit` hypothesis is not an extra assumption: the engine's own
round-trip certificate `algDeriv ρ F = integrand` (in `radIsZero`-tested form) is the integrand
split un-cross-multiplied, since `algDeriv ρ F = radDeriv(v) + Σ cᵢ·radLogDeriv(uᵢ)`. -/

/-- The engine round-trip certificate is the integrand split (un-cross-multiplied): for output
`F : AlgIntegralResult` over `y² = ρ`, `radIsZero (radSub (algDeriv ρ F) integrand) = true`
yields `toPoly (algDeriv ρ F) = toPoly integrand` in `K[X]`. -/
theorem toPolyG_algDeriv_eq_of_roundtrip (ρ : QFunNZG ℚ) (F : AlgIntegralResult)
    (integrand : RadElem (QFunNZG ℚ))
    (hrt : RadElem.radIsZero (RadElem.radSub (algDeriv ρ F) integrand) = true) :
    CPoly.toPoly (algDeriv ρ F) = CPoly.toPoly integrand := by
  rw [RadElem.radIsZero, RadElem.radSub] at hrt
  exact RefinesPolyG.eq_of_csub_cisZero (refinesPolyG_self _) (refinesPolyG_self _) hrt

/-! ### Axiom audit

The log-part predicates, certificate bridge, additivity floor, obligation lemmas, and
compositions below carry only `[propext, Classical.choice, Quot.sound]` — no `native_decide`,
no `sorry`. -/

-- The certificate-to-predicate bridge: every `radIsLogIntegral` certificate gives abstract single-log soundness.
#print axioms RadElem.isRadicalLogTerm_of_radIsLogIntegral

-- The additivity floor: `radDeriv` distributes over the log-numerator fold:
#print axioms RadElem.toPolyG_radDeriv_logFold

-- Two log residues add (the structural core of the multi-term residue sum):
#print axioms RadElem.mk_toPolyG_radLogSum2

-- The concrete abstract single-log integral `D(log √f) = f'/(nf)`:
#print axioms RadElem.isRadicalLogTerm_radGen

-- The residue-sum numerator base case (empty log part contributes nothing):
#print axioms RadElem.mk_toPolyG_radLogSumNum_nil

-- Logarithmic-residue input: the derivative factorization at a multiplicity-`m` root:
#print axioms LogResidue.derivative_X_sub_C_pow_mul

-- Logarithmic-residue input: the residue equals the vanishing order:
#print axioms LogResidue.logDeriv_residue_eq_multiplicity

-- Residue-resultant input: the residue-norm quadratic factors into the two-sheet residues:
#print axioms LogResidue.residueNorm_factor

-- Residue-resultant input: the per-root norm's roots are the two-sheet residues:
#print axioms LogResidue.roots_residueNorm

-- Residue-resultant input: the residue resultant's roots are the two-sheet residues:
#print axioms LogResidue.roots_residueResultant_eq_residues

-- Residue-sum input: the numerator distributes over the args list:
#print axioms RadElem.mk_toPolyG_radLogSumNum_eq_sum

-- Residue-sum composition: the log part is log-sound given the per-term residue match:
#print axioms RadElem.isRadicalLogIntegral_of_residue_match

-- The single-log instance of the composed log-part soundness:
#print axioms RadElem.isRadicalLogIntegral_singleton

-- Compute bridge: the residue-norm reads through `toPoly` as the abstract norm:
#print axioms CPoly.toPolyG_cAlgResidueNorm

-- Compute bridge: the engine's norm-resultant is the abstract `Polynomial.resultant` under `toK`:
#print axioms CPoly.toK_cresultantG_cAlgResidueNorm

-- Partial-fraction input: the rational log-part per-term match is algebraic:
#print axioms ratFunc_eq_sum_residue_logDeriv

-- Partial-fraction input: the residues are the partial-fraction coefficients:
#print axioms residue_of_partialFraction

-- Full composition: the algebraic integral `D(∫f) = f` follows from rational and log soundness:
#print axioms RadElem.isAlgebraicIntegral_of_parts

-- Compute bridge: interpolation uniqueness characterizes the engine's `cAlgResidueResultant`:
#print axioms CPoly.toPolyG_cAlgResidueResultant_eq_of_eval

-- Driver bridge: the engine round-trip certificate is the un-cross-multiplied integrand split:
#print axioms toPolyG_algDeriv_eq_of_roundtrip

end DeepWiki.SymbolicIntegration
