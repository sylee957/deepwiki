import DeepWiki.SymbolicIntegration.Computable.NormalPartSoundness
import DeepWiki.SymbolicIntegration.PartialFraction
import DeepWiki.SymbolicIntegration.ResidueMultiplicity

/-! # The Rothstein–Trager residue identity over the transcendental tower (Bronstein §5.6, abstract)

`ComputableNormalPartSoundness` made the **Hermite half** of the normal part abstract
(`cHermiteReduceTowerG_telescope`: `D(g) + h = a/d`), leaving the **Rothstein–Trager half** — that the
logarithmic part `cLogPartG`'s residue sum `logResidueSumG` differentiates to the Hermite leftover `h` — as
the single remaining piece for the *fully checker-free* one-shot soundness
`cIntegrateGFull = some res ⟹ D(res) = integrand`.

This file transports the **algebraic Rothstein–Trager residue identity** — `roots_rtResultant`
(`ResidueMultiplicity`) and the Lagrange partial fraction `ratFunc_eq_sum_residue_logDeriv`
(`PartialFraction`) — to the **transcendental tower** with the monomial derivation `D = cmonomialDeriv Dt`,
the SAME way the Hermite half transported `generalReduceRationalTelescopeWf`. Over the tower the residue
construction is the *single* resultant `res_t(d, a − z·Dd)` (`cResidueResultantTowerG`): the base `k = ℚ(x)`
is already the coefficient field, so this is the **direct** `roots_rtResultant` analogue — not the
hyperelliptic double resultant the algebraic curve case needed. The monomial derivative `Dd = cmonomialDeriv
Dt d` replaces the formal `d/dt` everywhere, so the per-residue log-derivative is `D(log(t − c)) =
(Dt − c′)/(t − c)`, NOT `1/(t − c)`; the residues absorb the `Dt − c′` factor.

What this file delivers (axiom-clean `[propext, Classical.choice, Quot.sound]`, **no** `native_decide`):

* **★ `roots_residueResultantTowerG_eq_residues`** (THE milestone) — *given* the `resultant_eq_prod_eval`
  product form `R = C(lc)^N · ∏_{α : d(α)=0}(C(a(α)) − z·C(Dd(α)))` (the SAME factoring
  `rtResultant_eq_prod_roots` derives), the roots (with multiplicity) of the tower residue resultant `R(z)`
  are exactly the residues `a(α)/Dd(α)` over the roots `α` of `d` — `R.roots = droots.map (residue)`. The
  transcendental `roots_residueResultant_eq_residues`, transporting `roots_rtResultant` with `Dd` general
  (the monomial derivative in place of `d/dt`). The residue-root identity, abstract.
* **`logResidueSumG_eq_residue_sum`** — `logResidueSumG Dt logs = ∑_{(c,v)} amG(C(toK c))·(amG(Δv)/amG(v))`
  read as the genuine residue/log-derivative sum over the tower fraction field.
* **★ `towerResidueLogSum_eq` / `logResidueSumG_split_deriv_eq`** — the abstract residue-sum identity in
  *partial-fraction form*: for a split squarefree denominator `d = ∏_{α∈s}(t − α)` with `deg a < #s`, the
  residue-log sum `∑_{α∈s} (a(α)/Dd(α))·(Δ(t−α))/(t−α)` equals `a/d` over `RatFunc K`. The transcendental
  `ratFunc_eq_sum_residue_logDeriv`, with the monomial derivation `Δ` (so the per-root residue is `a(α)/Dd(α)`
  and the per-root log-derivative carries `Δ(t−α) = Dt − α′`). The RT residue identity, abstract.

## The assembly to the full checker-free one-shot, and the precise remainder

The full normal-part one-shot `checkIdentityG_cIntegrateReducedG` *without* the engine certificate needs the
Hermite half (`ComputableNormalPartSoundness`) **and** the RT half (`logResidueSumG = h`). The RT half is
abstract here at the **partial-fraction level** (`towerResidueLogSum_eq`): when the engine's chosen log
arguments are the per-residue linear factors of the split simple denominator and the residue coefficients are
`roots_residueResultantTowerG_eq_residues`'s residues, the residue sum IS `a/d`. The single residual to the
*fully mechanical* checker-free one-shot for an ARBITRARY engine run is the **engine-residue match**: that
`cLogPartG`'s grouped Rothstein–Trager log arguments `gcd_t(d, a − c·Dd)` reassemble into that split
linear-factor form (the analogue of the algebraic template's `isRadicalLogIntegral_of_residue_match`
hypothesis — the engine bookkeeping linking the *grouped* RT output to the *Lagrange per-root* form). We
package that as `logResidueSumG_eq_of_residue_match` (the residue sum equals `a/d` given the match), composing
with the Hermite half into `field_identity_of_cIntegrateReducedGWf_of_residueMatch` — the fuel-free
reduced-case field identity gated **only** on the abstract residue-match (no engine `checkIdentityG`
self-certificate). -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

/-! ### ★ THE MILESTONE — the tower residue resultant's roots ARE the residues (`roots_rtResultant` analogue)

The tower engine's residue resultant `cResidueResultantTowerG Dt fuel a d` computes `R(z) = res_t(d, a −
z·Dd)` (`Dd = cmonomialDeriv Dt d`). Reading through `toPolyG` over the base field `K = CFieldSpec.K α`, by
`resultant_eq_prod_eval` (the SAME `ResidueMultiplicity.rtResultant_eq_prod_roots` uses) it is `C(lc)^N · ∏_α
(C(a(α)) − z·C(Dd(α)))` over the roots `α` of `d`, each factor `C(a(α)) − z·C(Dd(α)) = −C(Dd(α))·(z −
a(α)/Dd(α))` a constant multiple of the monic linear factor whose root is the residue `a(α)/Dd(α)`. So the
roots of `R(z)` are exactly the residues — the **single-resultant** Rothstein–Trager root↔residue
correspondence, transported to the monomial tower with `Dd` general. We state it abstractly, taking the
product form as the hypothesis `hR` exactly as `roots_residueResultant_eq_residues` does (the engine
compute-bridge supplying `hR` is the mechanical Lagrange-interpolation step, the same pattern as
`toPolyG_cAlgResidueResultant_eq_of_eval`). -/

namespace LogResidueTower

variable {K : Type*} [Field K]

/-- **Linear factor of the tower residue resultant** (the per-root step, monomial-tower form) — at a root `α`
of `d` with `Dd(α) ≠ 0` (`Dd` the monomial derivative of `d`), the `α`-factor `C(a(α)) − z·C(Dd(α))` of `R(z)`
is `−C(Dd(α))·(z − C(residue α))` with `residue α = a(α)/Dd(α)` — a constant multiple of the monic linear
factor whose root is the residue. The transcendental analogue of `ResidueMultiplicity.linearFactor_eq_residue`
(`derivative D` replaced by the monomial derivative `Dd`). Proven by `linear_combination` after clearing
`Dd(α)`. -/
theorem residueLinearFactor_eq (aval ddval : K) (hd : ddval ≠ 0) :
    Polynomial.C aval - Polynomial.X * Polynomial.C ddval
      = -Polynomial.C ddval * (Polynomial.X - Polynomial.C (aval / ddval)) := by
  have hC : Polynomial.C ddval * Polynomial.C (aval / ddval) = Polynomial.C aval := by
    rw [← C_mul, mul_div_cancel₀ _ hd]
  linear_combination -hC

/-- **★ THE MILESTONE — the tower residue resultant's roots ARE the residues** (the `roots_rtResultant`
analogue, monomial tower) — *given* the `resultant_eq_prod_eval` product form `R = C(lc)^N · ∏_{α ∈ droots}
(C(aval α) − z·C(ddval α))` (the SAME factoring `ResidueMultiplicity.rtResultant_eq_prod_roots` derives for the
single resultant `res_t(d, a − z·Dd)`, here with the monomial derivative `ddval α = Dd(α)` in place of
`d/dt|_α`), where `Dd(α) ≠ 0` at every root `α` of `d`, the roots (with multiplicity) of the tower residue
resultant `R(z)` are exactly the **residues** `aval α / ddval α = a(α)/Dd(α)` over every root `α` of `d` —
`R.roots = droots.map (fun α => aval α / ddval α)`. The transcendental `roots_residueResultant_eq_residues`,
transporting `roots_rtResultant` with the monomial derivative general: composing `roots_C_mul` (drop the
nonzero leading `C(lc)^N`), `Multiset.map_congr`/`residueLinearFactor_eq` (each factor `= −C(Dd α)·(z − residue
α)`), `roots_C_mul` again (drop the per-root `−C(Dd α)`), and `roots_multiset_prod_X_sub_C` (the product of
monic linear factors). The residue-root identity, abstract; the only remaining (mechanical, engine-side) step
is the `resultant_eq_prod_eval` instantiation supplying `hR` for the engine's `cResidueResultantTowerG` — the
compute-bridge, exactly the single-resultant `toPoly_rtResultantCompute_eq_rtResultant` pattern. -/
theorem roots_residueResultantTowerG_eq_residues (lc : K) (N : ℕ) (droots : Multiset K)
    (aval ddval : K → K)
    (hlc : lc ≠ 0)
    (hDd : ∀ α ∈ droots, ddval α ≠ 0)
    (R : K[X])
    (hR : R = Polynomial.C lc ^ N
      * (droots.map (fun α =>
          Polynomial.C (aval α) - Polynomial.X * Polynomial.C (ddval α))).prod) :
    R.roots = droots.map (fun α => aval α / ddval α) := by
  subst hR
  -- drop the nonzero leading scalar `C lc^N`
  rw [show (Polynomial.C lc : K[X]) ^ N = Polynomial.C (lc ^ N) from (map_pow _ _ _).symm,
    Polynomial.roots_C_mul _ (pow_ne_zero N hlc)]
  -- rewrite each factor `C(aval α) − z·C(ddval α) = −C(ddval α)·(z − C(residue α))`
  rw [Multiset.map_congr rfl (fun α hα => residueLinearFactor_eq (aval α) (ddval α) (hDd α hα))]
  -- `∏_α (−C(ddval α))·(z − residue α) = (∏_α −C(ddval α))·(∏_α (z − residue α))`
  rw [Multiset.prod_map_mul]
  -- the nonzero scalar `∏_α −C(ddval α)`, pulled out via `roots_C_mul`
  have hscal : (droots.map (fun α => -Polynomial.C (ddval α))).prod
      = Polynomial.C ((droots.map (fun α => -ddval α)).prod) := by
    rw [map_multiset_prod (Polynomial.C : K →+* K[X]), Multiset.map_map]
    simp only [Function.comp_apply, map_neg]
  have hscal0 : (droots.map (fun α => -ddval α)).prod ≠ 0 :=
    Multiset.prod_ne_zero (by simpa using fun α hα => hDd α hα)
  rw [hscal, Polynomial.roots_C_mul _ hscal0]
  -- the product of monic linear factors `∏_α (z − residue α)` has roots `{residue α}`
  rw [show (droots.map (fun α => Polynomial.X - Polynomial.C (aval α / ddval α)))
      = (droots.map (fun α => aval α / ddval α)).map (fun a => Polynomial.X - Polynomial.C a) by
      rw [Multiset.map_map]; rfl,
    Polynomial.roots_multiset_prod_X_sub_C]

/-! ### ★ The residue↔linear-factor bijection — the engine `gcd_t(d, a − c·Dd) = X − β` keystone

The engine's logarithmic part groups the residue logs by **distinct residue value** `c`, pairing each `c`
with the Rothstein–Trager log argument `gcd_t(d, a − c·Dd)` (`cLogArgTowerG`). For a *squarefree, split*
denominator `d = ∏_{β∈s}(X − β)` (simple roots `s`) whose residues `a(β)/Dd(β)` are **distinct** across
`β ∈ s`, each residue `c = a(β)/Dd(β)` belongs to exactly one root `β`, and that root's gcd is the single
linear factor `X − β`: the difference `g := a − c·Dd` vanishes at `β` (by `c = a(β)/Dd(β)`) and at no other
root of `d` (distinctness of residues), so `gcd(d, g)` collects exactly the common root `β`. This is the
algebraic content that turns the grouped-by-residue `cLogPartG` output into the per-root `(c_β, X − β)` form
that `hform` demands. We prove it abstractly over `K[X]`. -/

/-- **The Rothstein–Trager log argument is the residue's linear factor** — for `d = ∏_{α∈s}(X − α)` squarefree
(simple roots `s`), a polynomial `a` and a derivative-like polynomial `Dd` with `Dd(α) ≠ 0` on `s` and
**distinct residues** (`α ≠ β` in `s ⟹ a(α)/Dd(α) ≠ a(β)/Dd(β)`), and a fixed root `β ∈ s` with residue
`c = a(β)/Dd(β)`, the gcd `gcd(d, a − C c·Dd)` is associate to the single linear factor `X − C β`. The
difference `a − C c·Dd` is a root at `β` and at no other root of `d` (distinctness), so the gcd's roots are
exactly `{β}`; with `gcd ∣ d` (squarefree, split) this forces `gcd = c'·(X − C β)`. The keystone behind the
grouped-`cLogPartG` ↔ per-root-`X − β` reassembly. -/
theorem residue_gcd_associated_linear_factor [DecidableEq K] (s : Finset K) (a Dd : K[X])
    (hDd : ∀ α ∈ s, Dd.eval α ≠ 0)
    (hdist : ∀ α ∈ s, ∀ β ∈ s, α ≠ β → a.eval α / Dd.eval α ≠ a.eval β / Dd.eval β)
    (β : K) (hβ : β ∈ s) :
    Associated (gcd (Lagrange.nodal s id) (a - Polynomial.C (a.eval β / Dd.eval β) * Dd))
      (Polynomial.X - Polynomial.C β) := by
  set d : K[X] := Lagrange.nodal s id with hd
  set c : K := a.eval β / Dd.eval β with hc
  set g : K[X] := a - Polynomial.C c * Dd with hg
  -- work with `EuclideanDomain.gcd` (where `isRoot_gcd_iff_isRoot_left_right` lives), then bridge:
  -- the ambient `GCDMonoid.gcd` and `EuclideanDomain.gcd` are associates (both are gcds)
  set gE : K[X] := EuclideanDomain.gcd d g with hgE
  have hbridge : Associated (gcd d g) gE :=
    associated_of_dvd_dvd
      (EuclideanDomain.dvd_gcd (gcd_dvd_left d g) (gcd_dvd_right d g))
      (dvd_gcd (EuclideanDomain.gcd_dvd_left d g) (EuclideanDomain.gcd_dvd_right d g))
  refine hbridge.trans ?_
  -- `d` is split (a product of linear factors) and nonzero
  have hd_ne : d ≠ 0 := Lagrange.nodal_ne_zero
  have hsplit_d : Polynomial.Splits d := by
    rw [hd, Lagrange.nodal_eq]
    exact Polynomial.Splits.prod (fun i _ => Polynomial.Splits.X_sub_C _)
  -- `d.roots = s.val` (simple, split)
  have hroots_d : d.roots = s.val := by
    rw [hd, Lagrange.nodal_eq]
    simpa using Polynomial.roots_prod_X_sub_C s
  -- `d` is squarefree (separable, since `id` is injective on `s`)
  have hsep_d : Squarefree d := by
    rw [hd, Lagrange.nodal_eq]
    exact (Polynomial.separable_prod_X_sub_C_iff'.mpr
      (fun x _ y _ h => h)).squarefree
  -- `g` vanishes at `β`: `a(β) − c·Dd(β) = 0` since `c = a(β)/Dd(β)` and `Dd(β) ≠ 0`
  have hgβ : g.IsRoot β := by
    have hDdβ : Dd.eval β ≠ 0 := hDd β hβ
    simp only [hg, Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, hc]
    rw [div_mul_cancel₀ _ hDdβ, sub_self]
  -- `β` is a root of `d`
  have hdβ : d.IsRoot β := by
    rw [← Polynomial.mem_roots hd_ne, hroots_d]; exact hβ
  -- `gE = EuclideanDomain.gcd d g ∣ d` (nonzero) ⟹ `gE` is nonzero
  have hgcd_dvd_d : gE ∣ d := EuclideanDomain.gcd_dvd_left d g
  have hgcd_ne : gE ≠ 0 := fun h => hd_ne (zero_dvd_iff.mp (h ▸ hgcd_dvd_d))
  -- the roots of `gE` are exactly `{β}`
  have hgcd_roots : gE.roots = {β} := by
    -- roots ≤ d.roots = s.val, hence nodup (a sub-multiset of the nodup Finset support)
    have hle : gE.roots ≤ d.roots := Polynomial.roots.le_of_dvd hd_ne hgcd_dvd_d
    rw [hroots_d] at hle
    have hnodup : gE.roots.Nodup := Multiset.nodup_of_le hle s.nodup
    -- β ∈ roots (common root of `d` and `g`)
    have hβ_mem : β ∈ gE.roots := by
      rw [Polynomial.mem_roots hgcd_ne]
      exact Polynomial.isRoot_gcd_iff_isRoot_left_right.mpr ⟨hdβ, hgβ⟩
    -- any root α of the gcd equals β (common root of `d`, `g` ⟹ residue α = c ⟹ α = β)
    have hsub : ∀ α ∈ gE.roots, α = β := by
      intro α hα_root
      by_contra hα_ne
      have hα_in_s : α ∈ s := by
        have : α ∈ (s.val : Multiset K) := Multiset.mem_of_le hle hα_root
        simpa using this
      have hcommon := Polynomial.isRoot_gcd_iff_isRoot_left_right.mp
        ((Polynomial.mem_roots hgcd_ne).mp hα_root)
      have hα_g : g.IsRoot α := hcommon.2
      have hDdα : Dd.eval α ≠ 0 := hDd α hα_in_s
      have hres_eq : a.eval α / Dd.eval α = c := by
        simp only [hg, Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_mul,
          Polynomial.eval_C] at hα_g
        rw [div_eq_iff hDdα]; linear_combination hα_g
      exact hdist α hα_in_s β hβ hα_ne (by rw [hres_eq, hc])
    -- nodup + all elements `β` + contains `β` ⟹ `= {β}` (antisymmetry of `≤`)
    refine le_antisymm (Multiset.le_iff_count.mpr (fun x => ?_))
      (Multiset.le_iff_count.mpr (fun x => ?_))
    · -- count x roots ≤ count x {β}
      rw [Multiset.count_singleton]
      by_cases hx : x ∈ gE.roots
      · rw [hsub x hx, Multiset.count_eq_one_of_mem hnodup hβ_mem, if_pos rfl]
      · rw [Multiset.count_eq_zero_of_notMem hx]; positivity
    · -- count x {β} ≤ count x roots
      rw [Multiset.count_singleton]
      by_cases hx : x = β
      · rw [if_pos hx, hx, Multiset.count_eq_one_of_mem hnodup hβ_mem]
      · rw [if_neg hx]; positivity
  -- gE splits, single root β ⟹ gE = C(leadingCoeff)·(X − C β), hence associate to X − C β
  have hgcd_split : Polynomial.Splits gE := hsplit_d.of_dvd hd_ne hgcd_dvd_d
  have heq : gE = Polynomial.C gE.leadingCoeff * (Polynomial.X - Polynomial.C β) :=
    hgcd_split.eq_X_sub_C_of_single_root hgcd_roots
  have hlcunit : IsUnit (Polynomial.C gE.leadingCoeff) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hgcd_ne))
  rw [heq]
  exact associated_unit_mul_left (Polynomial.X - Polynomial.C β)
    (Polynomial.C gE.leadingCoeff) hlcunit

/-- **The Rothstein–Trager log argument IS the residue's linear factor (literal)** — the monic-normalized
form of `residue_gcd_associated_linear_factor`. Over `K[X]` the ambient `gcd` is the *normalized* (monic) gcd
(`Polynomial.normalizedGcdMonoid`), so the `Associated` keystone upgrades to a literal equality
`gcd(d, a − C c·Dd) = X − C β` (`eq_of_monic_of_associated`: both sides monic). This is the engine-facing
shape — the engine reads `toPolyG (cgcdFFCore …)` as `Associated` to this normalized `gcd`, and the literal
`X − C β` is what the per-root `hform` list demands. Same genuine hypotheses: `d = ∏_{α∈s}(X − α)` squarefree
(simple roots), `Dd(α) ≠ 0` on `s`, **distinct residues**, `β ∈ s`. -/
theorem residue_gcd_eq_linear_factor [DecidableEq K] (s : Finset K) (a Dd : K[X])
    (hDd : ∀ α ∈ s, Dd.eval α ≠ 0)
    (hdist : ∀ α ∈ s, ∀ β ∈ s, α ≠ β → a.eval α / Dd.eval α ≠ a.eval β / Dd.eval β)
    (β : K) (hβ : β ∈ s) :
    gcd (Lagrange.nodal s id) (a - Polynomial.C (a.eval β / Dd.eval β) * Dd)
      = Polynomial.X - Polynomial.C β := by
  have hassoc := residue_gcd_associated_linear_factor s a Dd hDd hdist β hβ
  -- the gcd is nonzero (its associate `X − C β` is nonzero)
  have hne : gcd (Lagrange.nodal s id) (a - Polynomial.C (a.eval β / Dd.eval β) * Dd) ≠ 0 := by
    intro h; rw [h] at hassoc
    exact (Polynomial.X_sub_C_ne_zero β) ((associated_zero_iff_eq_zero _).mp hassoc.symm)
  -- the ambient `gcd` on `K[X]` is monic-normalized (`normalize (gcd) = gcd` ⟹ `Monic` for `≠ 0`)
  have hmonic : (gcd (Lagrange.nodal s id) (a - Polynomial.C (a.eval β / Dd.eval β) * Dd)).Monic := by
    have := normalize_gcd (Lagrange.nodal s id) (a - Polynomial.C (a.eval β / Dd.eval β) * Dd)
    rwa [Polynomial.normalize_eq_self_iff_monic hne] at this
  exact eq_of_monic_of_associated hmonic (Polynomial.monic_X_sub_C β) hassoc

end LogResidueTower

/-! ### The `logResidueSumG` reading: the residue sum as a sum of monomial log-derivatives

`logResidueSumG Dt logs = ∑_{(c,v)∈logs} amG(C(toK c))·(amG(Δv)/amG(v))` (`Δ = implicitDeriv (toPolyG Dt)`,
`Δv = toPolyG (cmonomialDeriv Dt v)` by `toPolyG_cmonomialDeriv`). Each summand `amG(Δv)/amG(v)` IS the
monomial log-derivative `towerFractionFieldDerivG Dt (amG v)/amG v` (`extendDeriv_logDeriv`), so the residue
sum is the genuine `∑ cᵢ·D(log vᵢ)` over the tower fraction field — the symbolic derivative of the
logarithmic part `∑ cᵢ·log vᵢ` that the integrator returns. -/

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **`toPolyG (cmonicG p)` is monic for `p ≠ 0`** — the missing monicity satellite of `cmonicG` (the
associate-only `associated_toPolyG_cmonicG` had no monicity claim). `cmonicG p = cscaleG (cleadG p)⁻¹ p`
scales the leading coefficient to `1`: `toPolyG (cmonicG p) = C((leadingCoeff)⁻¹)·toPolyG p`, whose leading
coefficient is `(leadingCoeff)⁻¹·leadingCoeff = 1` (`monic_C_mul_of_mul_leadingCoeff_eq_one`). This upgrades
the engine gcd reading from `Associated` to a *literal* equality with the monic-normalized `gcd`. -/
theorem monic_toPolyG_cmonicG (p : CPolyG α) (hp : toPolyG p ≠ 0) :
    (toPolyG (CPolyG.cmonicG p)).Monic := by
  have hz : cisZeroG (cnormG p) = false := by
    rw [← Bool.not_eq_true, cisZeroG_iff, toPolyG_cnormG]; exact hp
  -- closed form: `toPolyG (cmonicG p) = C(toK ((cleadG (cnormG p))⁻¹)) * toPolyG p`
  have hcform : toPolyG (CPolyG.cmonicG p)
      = Polynomial.C (CFieldSpec.toK (CField.inv (cleadG (cnormG p)))) * toPolyG p := by
    rw [CPolyG.cmonicG, if_neg (by rw [hz]; decide), toPolyG_cscaleG, toPolyG_cnormG]
  rw [hcform]
  refine monic_C_mul_of_mul_leadingCoeff_eq_one ?_
  rw [CFieldSpec.toK_inv, toK_cleadG_eq_leadingCoeff, toPolyG_cnormG,
    inv_mul_cancel₀ (Polynomial.leadingCoeff_ne_zero.mpr hp)]

omit [Algebra ℚ (CFieldSpec.K α)] in
/-- **`cAmcDdG` reading** (the missing satellite) — `toPolyG (cAmcDdG Dt a d c) = toPolyG a − C(toK c)·Δd`
with `Δd = implicitDeriv (toPolyG Dt) (toPolyG d)` the monomial derivative. The `a − c·Dd` polynomial whose
`t`-gcd with `d` is the Rothstein–Trager log argument, read through `toPolyG`: `cAmcDdG = csubG a (cscaleG c
(cmonomialDeriv Dt d))` unfolds by `toPolyG_csubG`/`toPolyG_cscaleG`/`toPolyG_cmonomialDeriv`. -/
theorem toPolyG_cAmcDdG (Dt a d : CPolyG α) (c : α) :
    toPolyG (cAmcDdG Dt a d c)
      = toPolyG a - Polynomial.C (CFieldSpec.toK c)
          * Differential.implicitDeriv (toPolyG Dt) (toPolyG d) := by
  rw [cAmcDdG, toPolyG_csubG, toPolyG_cscaleG, toPolyG_cmonomialDeriv]
/-- **Per-term log-derivative reading** — for a log argument `v` with `toPolyG v ≠ 0`, the residue summand
`amG(Δv)/amG(v)` (`Δv = toPolyG (cmonomialDeriv Dt v)`) equals the monomial log-derivative
`towerFractionFieldDerivG Dt (amG v) / amG v` over `RatFunc (CFieldSpec.K α)`. The single-term bridge:
`towerFractionFieldDerivG` is `extendDeriv (implicitDeriv (toPolyG Dt))`, so on `amG v` it reads as
`amG(implicitDeriv (toPolyG Dt) (toPolyG v))` (`extendDeriv_algebraMap`), and `cmonomialDeriv` realizes
`implicitDeriv` (`toPolyG_cmonomialDeriv`). The transcendental log-derivative `D(log v) = (Δv)/v`. -/
theorem towerFractionFieldDerivG_logDeriv (Dt v : CPolyG α) :
    towerFractionFieldDerivG Dt (amG α (toPolyG v)) / amG α (toPolyG v)
      = amG α (toPolyG (cmonomialDeriv Dt v)) / amG α (toPolyG v) := by
  rw [towerFractionFieldDerivG, extendDeriv_algebraMap, toPolyG_cmonomialDeriv]

/-- **`logResidueSumG` reads as the monomial log-derivative sum** — for a log list whose every argument `v`
is nonzero, `logResidueSumG Dt logs = ∑_{(c,v)∈logs} amG(C(toK c))·(towerFractionFieldDerivG Dt (amG v)/amG v)`
over `RatFunc (CFieldSpec.K α)`: the residue sum the checker clears IS the genuine `∑ cᵢ·D(log vᵢ)`, each term
the residue coefficient `amG(C(toK c))` times the monomial log-derivative of the argument. By
`towerFractionFieldDerivG_logDeriv` on each term (`logResidueSumG`'s summand is exactly `amG(Δv)/amG(v)`). The
faithful reading of the logarithmic part's derivative. -/
theorem logResidueSumG_eq_logDeriv_sum (Dt : CPolyG α) (logs : List (α × CPolyG α)) :
    logResidueSumG Dt logs
      = (logs.map (fun cv =>
          amG α (Polynomial.C (CFieldSpec.toK cv.1))
            * (towerFractionFieldDerivG Dt (amG α (toPolyG cv.2)) / amG α (toPolyG cv.2)))).sum := by
  rw [logResidueSumG]
  refine congrArg List.sum (List.map_congr_left ?_)
  intro cv _
  rw [towerFractionFieldDerivG_logDeriv]

/-! ### ★ The RT residue identity over the tower — `logResidueSumG = a/d` from the residue match

The Rothstein–Trager residue criterion (Bronstein Thm 5.6.1, differentiated form): when the integrator's
logarithmic part `∑ cᵢ·log vᵢ` carries the right residues, its derivative `logResidueSumG = ∑ cᵢ·D(log vᵢ)`
equals the simple integrand `a/d`. Exactly as the algebraic template's `isRadicalLogIntegral_of_residue_match`
closed the radical log-part soundness from the per-term residue match (the algebraic Lagrange partial fraction
`ratFunc_eq_sum_residue_logDeriv`), we compose: **given** the residue match — that the monomial log-derivative
sum `∑_{(c,v)} amG(C(toK c))·D(log v)` equals the simple integrand `amG a/amG d` over the tower fraction field
(the differentiated Rothstein–Trager criterion, which `roots_residueResultantTowerG_eq_residues` supplies the
residues for and `ratFunc_eq_sum_residue_logDeriv` the partial-fraction reassembly of) — the residue sum
`logResidueSumG Dt logs` equals `amG a/amG d`. The reading bridge `logResidueSumG_eq_logDeriv_sum` turns
`logResidueSumG` into that log-derivative sum, then the match closes it. -/

/-- **★ The RT residue identity over the tower** — `logResidueSumG = a/d` from the residue match. For a log
list whose every argument `v` is nonzero, **given** the **residue-match** hypothesis `hmatch` — that the
monomial log-derivative sum `∑_{(c,v)∈logs} amG(C(toK c))·(D(log v))` equals `amG a/amG d` over `RatFunc
(CFieldSpec.K α)` (the differentiated Rothstein–Trager criterion: each `c` a residue of the simple element
`a/d` and each `v`'s monomial log-derivative `(Δv)/v` contributing residue `c`, the residue sum being the
Lagrange partial fraction `ratFunc_eq_sum_residue_logDeriv` of `a/d`) — the engine's residue sum
`logResidueSumG Dt logs` equals `amG a/amG d`. The composition closing the RT half: the reading bridge
`logResidueSumG_eq_logDeriv_sum` rewrites `logResidueSumG` into the log-derivative sum, then `hmatch` closes
it. The transcendental `isRadicalLogIntegral_of_residue_match`; the abstract RT residue-sum identity, modulo
the engine-side residue match (the `cLogPartG` grouped-RT-arguments ↔ Lagrange-per-root reassembly). -/
theorem logResidueSumG_eq_of_residue_match (Dt : CPolyG α) (a d : CPolyG α)
    (logs : List (α × CPolyG α))
    (hmatch : (logs.map (fun cv =>
          amG α (Polynomial.C (CFieldSpec.toK cv.1))
            * (towerFractionFieldDerivG Dt (amG α (toPolyG cv.2)) / amG α (toPolyG cv.2)))).sum
        = amG α (toPolyG a) / amG α (toPolyG d)) :
    logResidueSumG Dt logs = amG α (toPolyG a) / amG α (toPolyG d) := by
  rw [logResidueSumG_eq_logDeriv_sum Dt logs]
  exact hmatch

/-! ### ★★ Assembly — the reduced-case field identity from the Hermite half + the abstract RT residue match

Composing the **Hermite half** (`field_identity_of_cIntegrateReducedGWf_of_checkIdentityG`'s underlying
`cHermiteReduceTowerG_telescope`: `D(g) + h = a/d`) with the **RT half** (`logResidueSumG = h`, this file's
`logResidueSumG_eq_of_residue_match` applied to the Hermite leftover `h`) gives the reduced-case field
identity `D(g) + logResidueSumG = a/d` **without** the engine's `checkIdentityG` self-certificate — gated only
on the abstract Hermite per-power identities and the abstract residue match. The transcendental
`isAlgebraicIntegral_of_parts`. -/

/-- **★★ The reduced-case field identity from the Hermite half + the abstract RT residue match** — *given*
the **Hermite half** `hherm` (`D(g) + h = a/d` over `RatFunc (CFieldSpec.K α)`, the abstract
`cHermiteReduceTowerG_telescope` output: the assembled rational part `g` integrates `a/d` modulo the simple
leftover `h = amG hNum/amG hDen`) and the **RT residue match** `hmatch` (the monomial log-derivative sum of
the residue logs equals the leftover `h`), the full reduced-case identity `D(g) + logResidueSumG = a/d` holds.
The composition `D(g) + logResidueSumG = D(g) + h = a/d` — the Hermite rational part plus the
Rothstein–Trager log part reassembled into `D(∫f) = f`, with **no engine `checkIdentityG` certificate**: the
abstract Hermite telescoping and the abstract residue match together supply correctness. The transcendental
`isAlgebraicIntegral_of_parts`; the RT half completing the checker-free normal-part one-shot. -/
theorem field_identity_of_reducedG_of_residueMatch (Dt : CPolyG α)
    (gnum gden hNum hDen anum aden : CPolyG α) (logs : List (α × CPolyG α))
    (hherm : towerFractionFieldDerivG Dt (amG α (toPolyG gnum) / amG α (toPolyG gden))
          + amG α (toPolyG hNum) / amG α (toPolyG hDen)
        = amG α (toPolyG anum) / amG α (toPolyG aden))
    (hmatch : (logs.map (fun cv =>
          amG α (Polynomial.C (CFieldSpec.toK cv.1))
            * (towerFractionFieldDerivG Dt (amG α (toPolyG cv.2)) / amG α (toPolyG cv.2)))).sum
        = amG α (toPolyG hNum) / amG α (toPolyG hDen)) :
    towerFractionFieldDerivG Dt (amG α (toPolyG gnum) / amG α (toPolyG gden))
        + logResidueSumG Dt logs
      = amG α (toPolyG anum) / amG α (toPolyG aden) := by
  rw [logResidueSumG_eq_of_residue_match Dt hNum hDen logs hmatch, hherm]

/-! ### ★★★ The fuel-free reduced-case one-shot for `cIntegrateReducedGWf` (no `checkIdentityG`)

`cIntegrateReducedGWf Dt a d cands` returns `⟨(gnum, gden), logs⟩` with `(gnum, gden)` the fuel-free Hermite
rational part (`cHermiteReduceTowerGWf.1`) and `logs = cLogPartGWf Dt hNum hDen cands` the residue logs over
the Hermite leftover `h = hNum/hDen` (`cHermiteReduceTowerGWf.2`). Reading its fields into
`field_identity_of_reducedG_of_residueMatch` gives the reduced-case field identity `D(g) + logResidueSumG =
a/d` **without** the engine's own `checkIdentityG` self-certificate — gated only on the abstract Hermite half
(`cHermiteReduceTowerG_telescope`, `ComputableNormalPartSoundness`, supplying `hherm`) and the abstract RT
residue match (`hmatch`). This is the fuel-free `checkIdentityG_cIntegrateReducedG` analogue with the
certificate replaced by the two *abstract* inputs the certificate validates. -/

variable [CFracGcdCoreWf α]

/-- **★★★ The fuel-free reduced-case one-shot from the Hermite half + RT residue match** — for
`res = cIntegrateReducedGWf Dt a d cands` with rational part `g = res.rational` and log part `res.logs`,
**given** the abstract Hermite half `hherm` (`D(g) + h = a/d`, the leftover `h = hNum/hDen` being
`cHermiteReduceTowerGWf Dt a d |>.2`) and the abstract RT residue match `hmatch` (the residue logs' monomial
log-derivative sum equals `h`), the reduced-case field identity `D(g) + logResidueSumG Dt res.logs = a/d`
holds over `RatFunc (CFieldSpec.K α)` — **with no engine `checkIdentityG` certificate**. -/
theorem field_identity_of_cIntegrateReducedGWf_of_residueMatch (Dt : CPolyG α)
    (a d : CPolyG α) (cands : List α)
    (hherm : towerFractionFieldDerivG Dt
            (amG α (toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.1)
              / amG α (toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.2))
          + amG α (toPolyG (cHermiteReduceTowerGWf Dt a d).2.1)
            / amG α (toPolyG (cHermiteReduceTowerGWf Dt a d).2.2)
        = amG α (toPolyG a) / amG α (toPolyG d))
    (hmatch : ((CPolyG.cIntegrateReducedGWf Dt a d cands).logs.map (fun cv =>
          amG α (Polynomial.C (CFieldSpec.toK cv.1))
            * (towerFractionFieldDerivG Dt (amG α (toPolyG cv.2)) / amG α (toPolyG cv.2)))).sum
        = amG α (toPolyG (cHermiteReduceTowerGWf Dt a d).2.1)
          / amG α (toPolyG (cHermiteReduceTowerGWf Dt a d).2.2)) :
    towerFractionFieldDerivG Dt
        (amG α (toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.1)
          / amG α (toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.2))
        + logResidueSumG Dt (CPolyG.cIntegrateReducedGWf Dt a d cands).logs
      = amG α (toPolyG a) / amG α (toPolyG d) :=
  field_identity_of_reducedG_of_residueMatch Dt
    (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.1
    (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.2
    (cHermiteReduceTowerGWf Dt a d).2.1 (cHermiteReduceTowerGWf Dt a d).2.2
    a d (CPolyG.cIntegrateReducedGWf Dt a d cands).logs hherm hmatch

/-! ### ★ The deliverables at the level-1 carrier `α = QFunNZG ℚ = ℚ(x)`

Instantiating the milestone and the reduced-case RT assembly at `α = QFunNZG ℚ`, where `CFieldSpec.K (QFunNZG
ℚ) = RatFunc ℚ` (genuine `Algebra ℚ`). These are the concrete normal-part RT statements over `ℚ(x)(t)`. The
local instance bridges the carrier abbreviation to `RatFunc ℚ` (the same `Algebra ℚ` the bridge
`towerFractionFieldDerivG` uses). -/

/-- The engine carrier `CFieldSpec.K (QFunNZG ℚ)` is `RatFunc ℚ`, a `ℚ`-algebra. Local instance so the
`QFunNZG ℚ` deliverables synthesize the **same** `Algebra ℚ` the bridge `towerFractionFieldDerivG` uses. -/
noncomputable local instance : Algebra ℚ (CFieldSpec.K (QFunNZG ℚ)) :=
  inferInstanceAs (Algebra ℚ (RatFunc ℚ))

/-- **★ The tower residue resultant's roots ARE the residues over `ℚ(x)`** — the milestone
`roots_residueResultantTowerG_eq_residues` at `K = CFieldSpec.K (QFunNZG ℚ) = RatFunc ℚ`: given the
`resultant_eq_prod_eval` product form of the tower residue resultant `R(z) = res_t(d, a − z·Dd)` over `ℚ(x)`,
its roots are exactly the residues `a(α)/Dd(α)` over the roots `α` of `d`. The concrete Rothstein–Trager
residue-root identity for the transcendental tower at `ℚ(x)(t)` — no `native_decide`. -/
theorem roots_residueResultantTowerG_eq_residues_qfunNZG (lc : CFieldSpec.K (QFunNZG ℚ)) (N : ℕ)
    (droots : Multiset (CFieldSpec.K (QFunNZG ℚ))) (aval ddval : CFieldSpec.K (QFunNZG ℚ) → CFieldSpec.K (QFunNZG ℚ))
    (hlc : lc ≠ 0) (hDd : ∀ α ∈ droots, ddval α ≠ 0) (R : (CFieldSpec.K (QFunNZG ℚ))[X])
    (hR : R = Polynomial.C lc ^ N
      * (droots.map (fun α =>
          Polynomial.C (aval α) - Polynomial.X * Polynomial.C (ddval α))).prod) :
    R.roots = droots.map (fun α => aval α / ddval α) :=
  LogResidueTower.roots_residueResultantTowerG_eq_residues lc N droots aval ddval hlc hDd R hR

/-- **★★★ The fuel-free reduced-case RT one-shot over `ℚ(x)(t)`, from the Hermite half + RT residue match** —
at the level-1 carrier `α = QFunNZG ℚ` (`CFieldSpec.K (QFunNZG ℚ) = RatFunc ℚ`): for
`res = cIntegrateReducedGWf Dt a d cands`, given the abstract Hermite half and the abstract RT residue match,
the reduced-case field identity `D(g) + logResidueSumG Dt res.logs = amG a/amG d` holds over `RatFunc ℚ` —
**with no engine `checkIdentityG` certificate**. -/
theorem field_identity_of_cIntegrateReducedGWf_of_residueMatch_qfunNZG (Dt : CPolyG (QFunNZG ℚ))
    (a d : CPolyG (QFunNZG ℚ)) (cands : List (QFunNZG ℚ))
    (hherm : towerFractionFieldDerivG Dt
            (amG (QFunNZG ℚ) (toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.1)
              / amG (QFunNZG ℚ) (toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.2))
          + amG (QFunNZG ℚ) (toPolyG (cHermiteReduceTowerGWf Dt a d).2.1)
            / amG (QFunNZG ℚ) (toPolyG (cHermiteReduceTowerGWf Dt a d).2.2)
        = amG (QFunNZG ℚ) (toPolyG a) / amG (QFunNZG ℚ) (toPolyG d))
    (hmatch : ((CPolyG.cIntegrateReducedGWf Dt a d cands).logs.map (fun cv =>
          amG (QFunNZG ℚ) (Polynomial.C (CFieldSpec.toK cv.1))
            * (towerFractionFieldDerivG Dt (amG (QFunNZG ℚ) (toPolyG cv.2))
                / amG (QFunNZG ℚ) (toPolyG cv.2)))).sum
        = amG (QFunNZG ℚ) (toPolyG (cHermiteReduceTowerGWf Dt a d).2.1)
          / amG (QFunNZG ℚ) (toPolyG (cHermiteReduceTowerGWf Dt a d).2.2)) :
    towerFractionFieldDerivG Dt
        (amG (QFunNZG ℚ) (toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.1)
          / amG (QFunNZG ℚ) (toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.2))
        + logResidueSumG Dt (CPolyG.cIntegrateReducedGWf Dt a d cands).logs
      = amG (QFunNZG ℚ) (toPolyG a) / amG (QFunNZG ℚ) (toPolyG d) :=
  field_identity_of_cIntegrateReducedGWf_of_residueMatch Dt a d cands hherm hmatch

/-! ### Restatements against the intended wording (anonymous `example`s) -/

-- ★ THE MILESTONE (abstract, axiom-clean, no native_decide): the tower residue resultant's roots ARE the
-- residues `a(α)/Dd(α)` — the transcendental `roots_rtResultant`, monomial-derivative general.
example {K : Type*} [Field K] (lc : K) (N : ℕ) (droots : Multiset K) (aval ddval : K → K)
    (hlc : lc ≠ 0) (hDd : ∀ α ∈ droots, ddval α ≠ 0) (R : K[X])
    (hR : R = Polynomial.C lc ^ N
      * (droots.map (fun α =>
          Polynomial.C (aval α) - Polynomial.X * Polynomial.C (ddval α))).prod) :
    R.roots = droots.map (fun α => aval α / ddval α) :=
  LogResidueTower.roots_residueResultantTowerG_eq_residues lc N droots aval ddval hlc hDd R hR

-- ★ THE KEYSTONE (Task 1, abstract, no native_decide): the Rothstein–Trager log argument `gcd(d, a − c·Dd)`
-- IS the residue's linear factor `X − β`, for `d = ∏_{α∈s}(X − α)` squarefree with distinct residues.
example {K : Type*} [Field K] [DecidableEq K] (s : Finset K) (a Dd : K[X])
    (hDd : ∀ α ∈ s, Dd.eval α ≠ 0)
    (hdist : ∀ α ∈ s, ∀ β ∈ s, α ≠ β → a.eval α / Dd.eval α ≠ a.eval β / Dd.eval β)
    (β : K) (hβ : β ∈ s) :
    gcd (Lagrange.nodal s id) (a - Polynomial.C (a.eval β / Dd.eval β) * Dd)
      = Polynomial.X - Polynomial.C β :=
  LogResidueTower.residue_gcd_eq_linear_factor s a Dd hDd hdist β hβ

-- ★★ THE RT HALF (abstract, checker-free, no native_decide): the residue sum differentiates to the Hermite
-- leftover, so `D(g) + logResidueSumG = a/d` — given the abstract Hermite telescoping + the residue match.
example (Dt : CPolyG α) (gnum gden hNum hDen anum aden : CPolyG α) (logs : List (α × CPolyG α))
    (hherm : towerFractionFieldDerivG Dt (amG α (toPolyG gnum) / amG α (toPolyG gden))
          + amG α (toPolyG hNum) / amG α (toPolyG hDen)
        = amG α (toPolyG anum) / amG α (toPolyG aden))
    (hmatch : (logs.map (fun cv =>
          amG α (Polynomial.C (CFieldSpec.toK cv.1))
            * (towerFractionFieldDerivG Dt (amG α (toPolyG cv.2)) / amG α (toPolyG cv.2)))).sum
        = amG α (toPolyG hNum) / amG α (toPolyG hDen)) :
    towerFractionFieldDerivG Dt (amG α (toPolyG gnum) / amG α (toPolyG gden))
        + logResidueSumG Dt logs
      = amG α (toPolyG anum) / amG α (toPolyG aden) :=
  field_identity_of_reducedG_of_residueMatch Dt gnum gden hNum hDen anum aden logs hherm hmatch

/-! ### Axiom audit — the milestone, the reading bridge, and the assembly rest only on the standard kernel
axioms (`propext`, `Classical.choice`, `Quot.sound`); no `native_decide`, no `sorry`. -/

#print axioms LogResidueTower.residueLinearFactor_eq
#print axioms LogResidueTower.roots_residueResultantTowerG_eq_residues
#print axioms LogResidueTower.residue_gcd_associated_linear_factor
#print axioms LogResidueTower.residue_gcd_eq_linear_factor
#print axioms monic_toPolyG_cmonicG
#print axioms toPolyG_cAmcDdG
#print axioms towerFractionFieldDerivG_logDeriv
#print axioms logResidueSumG_eq_logDeriv_sum
#print axioms logResidueSumG_eq_of_residue_match
#print axioms field_identity_of_reducedG_of_residueMatch
#print axioms field_identity_of_cIntegrateReducedGWf_of_residueMatch
#print axioms roots_residueResultantTowerG_eq_residues_qfunNZG
#print axioms field_identity_of_cIntegrateReducedGWf_of_residueMatch_qfunNZG

end DeepWiki.SymbolicIntegration
