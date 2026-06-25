import DeepWiki.SymbolicIntegration.ComputableIntegrate
import DeepWiki.SymbolicIntegration.ComputableCanonicalRepCorrect
import DeepWiki.SymbolicIntegration.ComputableHermiteTowerCorrect
import DeepWiki.SymbolicIntegration.ComputablePolyPartTowerCorrect
import DeepWiki.SymbolicIntegration.ComputableLogPartTowerCorrect

/-! # Abstract correctness of the end-to-end transcendental integrator `cIntegrate` (Bronstein Ch. 5)
The capstone `cIntegrate` (`ComputableIntegrate`) assembles the whole transcendental Risch integration
loop — canonical split `f = fₚ + fₛ + fₙ` (§3.5), Hermite rational part of `fₙ` (§5.3), the
Rothstein–Trager rational-residue logarithmic part (§5.6), and the primitive polynomial integration of
`fₚ` (§5.8) — into the elementary antiderivative `∫ f = g + ∑ᵢ cᵢ·log(vᵢ)`. It is validated *pointwise*
by `native_decide` (`integrate_example`, the exact `IntegralResult.checkIdentity` cleared identity
`D(∫f) = f` on Bronstein's Example 5.6.2).

This file proves the **abstract** correctness — for ALL inputs, axiom-clean (no `native_decide`) — the
*field-level* antiderivative identity `D(g + ∑ᵢ cᵢ·log(vᵢ)) = f` over the genuine tower fraction field
`RatFunc (RatFunc ℚ)`, with `D = towerFractionFieldDeriv Dt` the keystone derivation (extending the
monomial derivation `Δ = implicitDeriv (toPolyG Dt)` by the quotient rule), in the **primitive regime**
`toPolyG Dt = C w₀` (`Dt ∈ k = ℚ(x)`, e.g. Example 5.6.2's `Dt = 1/x`). The hyperexponential regime
(`Dt ∉ k`) is out of scope — the §5.6 residue match only holds for primitive `Dt`.

**The composition.** Writing `cIntegrate` as `g + (the log sum)` and `f = fₚ + fₛ + fₙ`, the identity
`D(g + ∑ cᵢ log vᵢ) = f` is `D(g_rat) + D(∑ cᵢ log vᵢ) = f`, split by the linearity of the derivation
(`map_add`) into three composing sub-identities, each from a proven sub-piece:

* **The rational (Hermite + poly) part** `D(g_rat) = fₚ + (fₙ − hₛ)` — the integrated piece — from the
  cleared Hermite identity `cHermiteReduceTower_cleared_identity` and the polynomial reductions
  `cPrimitivePolyIntegrate_cleared_identity`, both read at the **field level** through `toPolyG` and the
  quotient rule for `towerFractionFieldDeriv`.
* **The logarithmic part** `D(∑ᵢ cᵢ log vᵢ) = hₛ` — the simple residual of `fₙ` — from
  `towerLogPart_eq_div_of_const_seed` (the §5.6 Rothstein–Trager log-part identity in the primitive
  regime). Here `hₛ = ∑ᵢ cᵢ·(Δvᵢ)/vᵢ` is the residue sum; matching it to the concrete `cLogPart` output
  of the Hermite simple residual is the **documented bridge gap** (the concrete-`cLogArgTower`-to-abstract-
  `Lagrange.nodal` residue match), taken here as the named hypothesis `hLog`.
* **The split** `fₚ + fₛ + fₙ = f` — from `canonicalRepFast_reconstructs` (§3.5).

The field-level identity is the all-inputs generalization of `checkIdentity`'s `cisZeroG` check (which
clears the same fractions over `(RatFunc ℚ)[X]`); the `checkIdentity ↔ field-identity` clearing bridge is
recorded for the rational part. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZ

/-- The engine carrier `CFieldSpec.K QFunNZ` is `RatFunc ℚ`, a `ℚ`-algebra. Re-declared as a local
instance (matching the keystone's) so this file synthesizes the **same** `Algebra ℚ` as
`towerFractionFieldDeriv`/`towerLogPart_*`, avoiding an instance-mismatch detour. -/
noncomputable local instance : Algebra ℚ (CFieldSpec.K QFunNZ) :=
  inferInstanceAs (Algebra ℚ (RatFunc ℚ))

/-! ### Field-level reading of the proven cleared identities

Each proven sub-piece is the cleared polynomial identity over `(RatFunc ℚ)[X]` (e.g. Hermite's
`(D(gnum)·gden − gnum·D(gden))·Dstar + hNum·gden²)·d = a·(gden²·Dstar)`). Dividing through the nonzero
common denominator lands the **field** identity over the tower fraction field `RatFunc (RatFunc ℚ)`,
where the monomial derivation reads as `towerFractionFieldDeriv Dt` via the quotient rule. We use the
abbreviation `A := algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ))` throughout (the embedding of the
tower polynomial ring into its fraction field). -/

/-- Shorthand: the embedding `(RatFunc ℚ)[X] → RatFunc (RatFunc ℚ)` of the tower polynomial ring into
its fraction field — the carrier on which the field-level antiderivative identity lives. -/
noncomputable abbrev towerAlg : (CFieldSpec.K QFunNZ)[X] →+* RatFunc (CFieldSpec.K QFunNZ) :=
  algebraMap (CFieldSpec.K QFunNZ)[X] (RatFunc (CFieldSpec.K QFunNZ))

/-- `towerAlg p ≠ 0` for `p ≠ 0` (the tower polynomial-ring embedding is injective). -/
theorem towerAlg_ne_zero {p : (CFieldSpec.K QFunNZ)[X]} (hp : p ≠ 0) : towerAlg p ≠ 0 :=
  (map_ne_zero_iff _ (RatFunc.algebraMap_injective _)).mpr hp

/-- **Quotient-rule reading of `D(gnum/gden)` over the tower field**: with `g = towerAlg(gnum)/towerAlg(gden)`
(`gden ≠ 0`), `towerFractionFieldDeriv Dt g = (towerAlg(Δ gnum)·towerAlg(gden) − towerAlg(gnum)·towerAlg(Δ gden))
/ (towerAlg(gden))²` where `Δ = implicitDeriv (toPolyG Dt)`. The quotient rule for the keystone derivation,
applied to a fraction of polynomial images. -/
theorem towerFractionFieldDeriv_div (Dt : CPolyG QFunNZ) (gnum gden : (CFieldSpec.K QFunNZ)[X]) :
    towerFractionFieldDeriv Dt (towerAlg gnum / towerAlg gden)
      = (towerAlg (Differential.implicitDeriv (toPolyG Dt) gnum) * towerAlg gden
          - towerAlg gnum * towerAlg (Differential.implicitDeriv (toPolyG Dt) gden))
        / (towerAlg gden) ^ 2 := by
  rw [← RatFunc.mk_eq_div, towerFractionFieldDeriv_mk, RatFunc.mk_eq_div, map_sub, map_mul, map_mul,
    map_pow]

/-! ### The Hermite reduction as a field identity `D(g) + hₛ = fₙ`

The proven `cHermiteReduceTower_cleared_identity` is the cleared polynomial identity
`(P·Dstar + hNum·gden²)·d = a·(gden²·Dstar)` (with `P = Δgnum·gden − gnum·Δgden`). Dividing through the
nonzero `gden²·Dstar·d` lands the field identity `D(gnum/gden) + hNum/Dstar = a/d` over the tower fraction
field. The clearing step is generic ring algebra over the field. -/

/-- **Field clearing of the Hermite cleared identity** (generic field): from the polynomial cleared
identity `(P·Dstar + hNum·gden²)·d = a·(gden²·Dstar)` with `gden, Dstar, d ≠ 0` (read into the fraction
field via the injective `algebraMap`), the field fraction identity `P/gden² + hNum/Dstar = a/d` holds.
Pure field-arithmetic clearing (`field_simp` + `linear_combination` of the polynomial witness). -/
theorem hermite_field_div_of_cleared {K : Type*} [Field K] (P Dstar gden hNum d a : K[X])
    (hden : gden ≠ 0) (hDstar : Dstar ≠ 0) (hd : d ≠ 0)
    (hcleared : (P * Dstar + hNum * (gden * gden)) * d = a * ((gden * gden) * Dstar)) :
    (algebraMap K[X] (RatFunc K) P) / (algebraMap K[X] (RatFunc K) gden) ^ 2
        + (algebraMap K[X] (RatFunc K) hNum) / (algebraMap K[X] (RatFunc K) Dstar)
      = (algebraMap K[X] (RatFunc K) a) / (algebraMap K[X] (RatFunc K) d) := by
  set A := algebraMap K[X] (RatFunc K) with hA
  have hAd : A d ≠ 0 := (map_ne_zero_iff _ (RatFunc.algebraMap_injective _)).mpr hd
  have hAden : A gden ≠ 0 := (map_ne_zero_iff _ (RatFunc.algebraMap_injective _)).mpr hden
  have hADstar : A Dstar ≠ 0 := (map_ne_zero_iff _ (RatFunc.algebraMap_injective _)).mpr hDstar
  have hcl : (A P * A Dstar + A hNum * (A gden * A gden)) * A d
      = A a * (A gden * A gden * A Dstar) := by
    have := congrArg A hcleared
    simpa only [map_mul, map_add] using this
  rw [div_add_div _ _ (pow_ne_zero 2 hAden) hADstar, div_eq_div_iff
    (mul_ne_zero (pow_ne_zero 2 hAden) hADstar) hAd]
  ring_nf
  ring_nf at hcl
  linear_combination hcl

/-- **The Hermite reduction as a field identity** `D(gₕ) + hₛ = fₙ` over the tower fraction field
`RatFunc (RatFunc ℚ)`: writing `((gnum, gden), (hNum, Dstar)) = cHermiteReduceTower Dt fuel a d`, the
rational part `gₕ = towerAlg(gnum)/towerAlg(gden)` and the simple residual `hₛ = towerAlg(hNum)/towerAlg(Dstar)`
satisfy `towerFractionFieldDeriv Dt gₕ + hₛ = towerAlg(a)/towerAlg(d)`. Composes the proven cleared
polynomial identity `cHermiteReduceTower_cleared_identity` with the field clearing
`hermite_field_div_of_cleared` and the quotient rule `towerFractionFieldDeriv_div`. Gated on the same
transparent exact-division/nonzero-divisor/fuel preconditions the proven cleared identity carries, plus
nonzero `gden, Dstar, d`. -/
theorem cHermiteReduceTower_field_identity (Dt : CPolyG QFunNZ) (fuel : ℕ) (a d : CPolyG QFunNZ)
    (gnumR gdenR DstarR gprimeNum resNum resDen hNumR : CPolyG QFunNZ)
    (hgnum : gnumR = (cHermiteReduceTower Dt fuel a d).1.1)
    (hgden : gdenR = (cHermiteReduceTower Dt fuel a d).1.2)
    (hDstar : DstarR = (cHermiteReduceTower Dt fuel a d).2.2)
    (hgprime : gprimeNum
      = csubG (cmulG (cmonomialDeriv Dt gnumR) gdenR) (cmulG gnumR (cmonomialDeriv Dt gdenR)))
    (hresNum : resNum = csubG (cmulG a (cmulG gdenR gdenR)) (cmulG d gprimeNum))
    (hresDen : resDen = cmulG d (cmulG gdenR gdenR))
    (hhNum : hNumR = cdivG fuel (cmulG resNum DstarR) resDen)
    (hq0 : cnormG resDen ≠ [])
    (hfuel : (cnormG (cmulG resNum DstarR) : List QFunNZ).length ≤ fuel)
    (hdvd : toPolyG resDen ∣ toPolyG (cmulG resNum DstarR))
    (hgdenne : toPolyG gdenR ≠ 0) (hDstarne : toPolyG DstarR ≠ 0) (hdne : toPolyG d ≠ 0) :
    towerFractionFieldDeriv Dt (towerAlg (toPolyG gnumR) / towerAlg (toPolyG gdenR))
        + towerAlg (toPolyG hNumR) / towerAlg (toPolyG DstarR)
      = towerAlg (toPolyG a) / towerAlg (toPolyG d) := by
  -- the proven cleared polynomial identity over `(RatFunc ℚ)[X]`
  have hcleared := cHermiteReduceTower_cleared_identity Dt fuel a d gnumR gdenR DstarR gprimeNum
    resNum resDen hNumR hgnum hgden hDstar hgprime hresNum hresDen hhNum hq0 hfuel hdvd
  -- the quotient-rule numerator `P = Δgnum·gden − gnum·Δgden`, with `Δ = implicitDeriv (toPolyG Dt)`
  rw [towerFractionFieldDeriv_div]
  set P : (CFieldSpec.K QFunNZ)[X] :=
    Differential.implicitDeriv (toPolyG Dt) (toPolyG gnumR) * toPolyG gdenR
      - toPolyG gnumR * Differential.implicitDeriv (toPolyG Dt) (toPolyG gdenR) with hP
  -- the cleared polynomial identity in `Δ`-form, matching `P`
  have hcleared' : (P * toPolyG DstarR + toPolyG hNumR * (toPolyG gdenR * toPolyG gdenR)) * toPolyG d
      = toPolyG a * (toPolyG gdenR * toPolyG gdenR * toPolyG DstarR) := by
    rw [hP, ← toPolyG_cmonomialDeriv, ← toPolyG_cmonomialDeriv]
    linear_combination hcleared
  rw [show towerAlg (Differential.implicitDeriv (toPolyG Dt) (toPolyG gnumR)) * towerAlg (toPolyG gdenR)
        - towerAlg (toPolyG gnumR) * towerAlg (Differential.implicitDeriv (toPolyG Dt) (toPolyG gdenR))
      = towerAlg P by rw [hP, map_sub, map_mul, map_mul]]
  exact hermite_field_div_of_cleared P (toPolyG DstarR) (toPolyG gdenR) (toPolyG hNumR) (toPolyG d)
    (toPolyG a) hgdenne hDstarne hdne hcleared'

/-! ### The polynomial part — field-level primitive-poly reconstruction `D(pq) + prem = fₚ`

`cPrimitivePolyIntegrate Dt fuel fp = (pq, prem)` reconstructs the polynomial part `fₚ` exactly:
`Δ(pq) + prem = fp` (the proven `cPrimitivePolyIntegrate_cleared_identity`). At the field level, every
term is a polynomial image (denominator `1`), so the identity reads
`towerFractionFieldDeriv Dt (towerAlg pq) + towerAlg prem = towerAlg fp` via the keystone's
`towerFractionFieldDeriv_algebraMap` (the tower derivation extends the monomial derivation on polynomial
images). -/

/-- **The primitive polynomial integration as a field identity** `D(pq) + prem = fₚ` over the tower
fraction field: with `(pq, prem) = cPrimitivePolyIntegrate Dt fuel fp`,
`towerFractionFieldDeriv Dt (towerAlg (toPolyG pq)) + towerAlg (toPolyG prem) = towerAlg (toPolyG fp)`.
Composes the proven cleared polynomial identity `cPrimitivePolyIntegrate_cleared_identity` with
`towerFractionFieldDeriv_algebraMap`; gated on no preconditions. -/
theorem cPrimitivePolyIntegrate_field_identity (Dt : CPolyG QFunNZ) (fuel : ℕ) (fp : CPolyG QFunNZ) :
    towerFractionFieldDeriv Dt (towerAlg (toPolyG (cPrimitivePolyIntegrate Dt fuel fp).1))
        + towerAlg (toPolyG (cPrimitivePolyIntegrate Dt fuel fp).2)
      = towerAlg (toPolyG fp) := by
  rw [towerFractionFieldDeriv_algebraMap, ← map_add]
  exact congrArg towerAlg (cPrimitivePolyIntegrate_cleared_identity Dt fuel fp)

/-! ### The logarithmic part — the residue sum `∑ᵢ cᵢ·(Δvᵢ)/vᵢ` as a field element

`checkIdentity` differentiates the logarithmic part `∑ᵢ cᵢ·log(vᵢ)` symbolically to the **residue sum**
`∑ᵢ cᵢ·(Δvᵢ)/vᵢ` (the log-derivative `D(log v) = (Δv)/v`), accumulated as a single fraction `(Lnum, Lden)`
over `∏ᵢ vᵢ` by the `foldl`. We give the residue sum as a genuine field element `logResidueSum` over
`RatFunc (RatFunc ℚ)` and prove the fold computes it (the field reading of `(Lnum, Lden)`), so the
field-level identity `D(g) + logResidueSum = f` is the all-inputs generalization of `checkIdentity`'s
cleared `cisZeroG`. -/

/-- **The logarithmic-part residue sum** `logResidueSum Dt logs = ∑_{(c,v)∈logs} C(toK(ofConstNZ c))·(Δv)/v`
over the tower fraction field `RatFunc (RatFunc ℚ)`, with `Δ = implicitDeriv (toPolyG Dt)` (so `Δv =
toPolyG (cmonomialDeriv Dt v)`). This is the symbolic derivative of `∑ᵢ cᵢ·log(vᵢ)` — exactly the residue
sum `checkIdentity` clears against `f`. -/
noncomputable def logResidueSum (Dt : CPolyG QFunNZ) (logs : List (ℚ × CPolyG QFunNZ)) :
    RatFunc (CFieldSpec.K QFunNZ) :=
  (logs.map (fun cv =>
    towerAlg (Polynomial.C (CFieldSpec.toK (ofConstNZ cv.1)))
      * (towerAlg (toPolyG (cmonomialDeriv Dt cv.2)) / towerAlg (toPolyG cv.2)))).sum

/-- `logResidueSum` of the empty list is `0`. -/
@[simp] theorem logResidueSum_nil (Dt : CPolyG QFunNZ) : logResidueSum Dt [] = 0 := rfl

/-- `logResidueSum` peels the head: `logResidueSum Dt ((c,v) :: rest) = C(toK(ofConstNZ c))·(Δv)/v
+ logResidueSum Dt rest`. -/
theorem logResidueSum_cons (Dt : CPolyG QFunNZ) (cv : ℚ × CPolyG QFunNZ)
    (rest : List (ℚ × CPolyG QFunNZ)) :
    logResidueSum Dt (cv :: rest)
      = towerAlg (Polynomial.C (CFieldSpec.toK (ofConstNZ cv.1)))
          * (towerAlg (toPolyG (cmonomialDeriv Dt cv.2)) / towerAlg (toPolyG cv.2))
        + logResidueSum Dt rest := by
  simp only [logResidueSum, List.map_cons, List.sum_cons]

/-! ### The `checkIdentity` fold computes the residue sum

`checkIdentity`'s `foldl` accumulates the residue sum `∑ cᵢ·(Δvᵢ)/vᵢ` as one fraction `(Lnum, Lden)` over
`∏ᵢ vᵢ`, starting at `([0], [1])` and combining `acc.1/acc.2 + (c·Δv)/v = (acc.1·v + c·Δv·acc.2)/(acc.2·v)`.
Reading through `towerAlg` over the field, the fold's running fraction is the partial `logResidueSum` plus
the seed; with all `vᵢ` nonzero the seed contributes `0`, so the final `Lnum/Lden = logResidueSum`. -/

/-- **The `checkIdentity` fold computes the residue sum** (field reading): folding from a seed
`(snum, sden)` (with `sden ≠ 0` as a polynomial) over a log list whose every argument `v` is nonzero,
the running fraction `towerAlg(Lnum)/towerAlg(Lden)` equals the seed fraction plus `logResidueSum`, and
the running denominator `Lden = sden·∏ᵢ vᵢ` stays nonzero. By induction on the list. -/
theorem checkIdentity_fold_eq (Dt : CPolyG QFunNZ) :
    ∀ (logs : List (ℚ × CPolyG QFunNZ)) (snum sden : CPolyG QFunNZ),
      toPolyG sden ≠ 0 →
      (∀ cv ∈ logs, toPolyG cv.2 ≠ 0) →
      let res := logs.foldl
        (fun (acc : CPolyG QFunNZ × CPolyG QFunNZ) (cv : ℚ × CPolyG QFunNZ) =>
          let c := cv.1
          let v := cv.2
          let Dv := cmonomialDeriv Dt v
          let termNum := cscaleG (ofConstNZ c) Dv
          (caddG (cmulG acc.1 v) (cmulG termNum acc.2), cmulG acc.2 v))
        (snum, sden)
      toPolyG res.2 ≠ 0 ∧
        towerAlg (toPolyG res.1) / towerAlg (toPolyG res.2)
          = towerAlg (toPolyG snum) / towerAlg (toPolyG sden) + logResidueSum Dt logs := by
  intro logs
  induction logs with
  | nil =>
    intro snum sden hsden _
    refine ⟨hsden, ?_⟩
    simp only [logResidueSum_nil, add_zero, List.foldl_nil]
  | cons cv rest ih =>
    intro snum sden hsden hv
    -- the head argument `v` is nonzero
    have hvne : toPolyG cv.2 ≠ 0 := hv cv List.mem_cons_self
    -- one fold step: new accumulator
    set newnum := caddG (cmulG snum cv.2) (cmulG (cscaleG (ofConstNZ cv.1) (cmonomialDeriv Dt cv.2)) sden)
      with hnewnum
    set newden := cmulG sden cv.2 with hnewden
    have hnewden_ne : toPolyG newden ≠ 0 := by
      rw [hnewden, toPolyG_cmulG]; exact mul_ne_zero hsden hvne
    -- the IH applied to the rest with the new seed
    have hrest : ∀ cv' ∈ rest, toPolyG cv'.2 ≠ 0 := fun cv' hcv' => hv cv' (List.mem_cons_of_mem _ hcv')
    obtain ⟨hden, heq⟩ := ih newnum newden hnewden_ne hrest
    refine ⟨?_, ?_⟩
    · -- the running denominator after the head step is `(newnum, newden)`
      simp only [List.foldl_cons]
      exact hden
    simp only [List.foldl_cons]
    rw [heq, logResidueSum_cons]
    -- the field algebra: `snum/sden + C(c)·(Δv)/v = newnum/newden`
    have hAsden : towerAlg (toPolyG sden) ≠ 0 := towerAlg_ne_zero hsden
    have hAv : towerAlg (toPolyG cv.2) ≠ 0 := towerAlg_ne_zero hvne
    have hstep : towerAlg (toPolyG newnum) / towerAlg (toPolyG newden)
        = towerAlg (toPolyG snum) / towerAlg (toPolyG sden)
          + towerAlg (Polynomial.C (CFieldSpec.toK (ofConstNZ cv.1)))
              * (towerAlg (toPolyG (cmonomialDeriv Dt cv.2)) / towerAlg (toPolyG cv.2)) := by
      rw [hnewnum, hnewden, toPolyG_caddG, toPolyG_cmulG, toPolyG_cmulG, toPolyG_cscaleG,
        toPolyG_cmulG, map_add, map_mul, map_mul, map_mul]
      field_simp
      simp only [map_mul]
      ring
    rw [hstep]; ring

/-! ### The `checkIdentity` ↔ field-identity bridge

`checkIdentity Dt res anum aden = true` is (via `cisZeroG_iff`) the cleared polynomial identity
`(GP·LD + LN·GD²)·AD = AN·(GD²·LD)` over `(RatFunc ℚ)[X]`, where `GP = toPolyG gprimeNum`,
`(LN, LD) = fold-result`, etc. Dividing through the nonzero `GD²·LD·AD` and reading `D(gnum/gden) =
GP/GD²` (quotient rule) and `LN/LD = logResidueSum` (the fold bridge), this is exactly the field
identity `D(gnum/gden) + logResidueSum = anum/aden`. The forward direction — *field identity ⟹
`checkIdentity = true`* — is what lets the composed proven pieces conclude the engine's `checkIdentity`. -/

open IntegralResult in
/-- **Field identity ⟹ `checkIdentity = true`**: if the field-level antiderivative identity
`towerFractionFieldDeriv Dt (towerAlg gnum / towerAlg gden) + logResidueSum Dt res.logs = towerAlg anum /
towerAlg aden` holds over the tower fraction field, with `res.rational = (gnum, gden)`, the denominators
`gden, aden` nonzero, and every log argument `vᵢ` nonzero, then `checkIdentity Dt res anum aden = true`.
The clearing converts the field fraction identity back to the cleared `cisZeroG` polynomial identity the
engine checks. -/
theorem checkIdentity_of_field_identity (Dt : CPolyG QFunNZ) (res : IntegralResult)
    (anum aden : CPolyG QFunNZ)
    (hgden : toPolyG res.rational.2 ≠ 0) (haden : toPolyG aden ≠ 0)
    (hlogs : ∀ cv ∈ res.logs, toPolyG cv.2 ≠ 0)
    (hfield : towerFractionFieldDeriv Dt (towerAlg (toPolyG res.rational.1) / towerAlg (toPolyG res.rational.2))
        + logResidueSum Dt res.logs
      = towerAlg (toPolyG anum) / towerAlg (toPolyG aden)) :
    IntegralResult.checkIdentity Dt res anum aden = true := by
  -- names matching `checkIdentity`
  set gnum := res.rational.1 with hgnum
  set gden := res.rational.2 with hgdenE
  set gprimeNum := csubG (cmulG (cmonomialDeriv Dt gnum) gden) (cmulG gnum (cmonomialDeriv Dt gden))
    with hgp
  set gden2 := cmulG gden gden with hgden2
  -- the fold result `(Lnum, Lden)`
  set folded := res.logs.foldl
    (fun (acc : CPolyG QFunNZ × CPolyG QFunNZ) (cv : ℚ × CPolyG QFunNZ) =>
      let c := cv.1
      let v := cv.2
      let Dv := cmonomialDeriv Dt v
      let termNum := cscaleG (ofConstNZ c) Dv
      (caddG (cmulG acc.1 v) (cmulG termNum acc.2), cmulG acc.2 v))
    ([CField.zero], [CField.one]) with hfolded
  -- the fold computes `logResidueSum` over the field, with nonzero `Lden`
  have hseedden : toPolyG ([CField.one] : CPolyG QFunNZ) ≠ 0 := by
    rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_one, mul_zero, add_zero]; exact one_ne_zero
  obtain ⟨hLden_ne, hLfield⟩ := checkIdentity_fold_eq Dt res.logs [CField.zero] [CField.one]
    hseedden hlogs
  rw [← hfolded] at hLden_ne hLfield
  -- the seed fraction `0/1 = 0`
  have hseed0 : towerAlg (toPolyG ([CField.zero] : CPolyG QFunNZ))
      / towerAlg (toPolyG ([CField.one] : CPolyG QFunNZ)) = 0 := by
    rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_zero, map_zero, mul_zero, add_zero, map_zero,
      zero_div]
  rw [hseed0, zero_add] at hLfield
  -- abbreviations over the field
  set GP := towerAlg (toPolyG gprimeNum) with hGP
  set LN := towerAlg (toPolyG folded.1) with hLN
  set LD := towerAlg (toPolyG folded.2) with hLD
  set AN := towerAlg (toPolyG anum) with hAN
  set AD := towerAlg (toPolyG aden) with hAD
  set GD := towerAlg (toPolyG gden) with hGD
  -- nonzero readings
  have hGDne : GD ≠ 0 := by rw [hGD]; exact towerAlg_ne_zero hgden
  have hLDne : LD ≠ 0 := by rw [hLD]; exact towerAlg_ne_zero hLden_ne
  have hADne : AD ≠ 0 := by rw [hAD]; exact towerAlg_ne_zero haden
  -- `D(gnum/gden) = GP/GD²` (quotient rule); `logResidueSum = LN/LD` (fold bridge)
  have hquot : towerFractionFieldDeriv Dt (towerAlg (toPolyG gnum) / towerAlg (toPolyG gden))
      = GP / GD ^ 2 := by
    rw [towerFractionFieldDeriv_div, hGP, hgp, toPolyG_csubG, toPolyG_cmulG, toPolyG_cmulG,
      toPolyG_cmonomialDeriv, toPolyG_cmonomialDeriv, map_sub, map_mul, map_mul, hGD]
  have hLfield' : logResidueSum Dt res.logs = LN / LD := by rw [← hLfield, hLN, hLD]
  -- the field identity, rewritten with the readings: `GP/GD² + LN/LD = AN/AD`
  rw [hquot, hLfield'] at hfield
  -- the cleared polynomial equation `(GP·LD + LN·GD²)·AD = AN·(GD²·LD)`
  have hclear : (GP * LD + LN * (GD * GD)) * AD = AN * (GD * GD * LD) := by
    have hh := hfield
    field_simp at hh
    linear_combination hh
  -- unfold `checkIdentity` to its `cisZeroG` and convert to the cleared `toPolyG` polynomial equation
  show IntegralResult.checkIdentity Dt res anum aden = true
  rw [IntegralResult.checkIdentity]
  simp only [← hgnum, ← hgdenE, ← hgp, ← hgden2, ← hfolded]
  rw [cisZeroG_iff, toPolyG_csubG, sub_eq_zero, toPolyG_cmulG, toPolyG_cmulG, toPolyG_caddG,
    toPolyG_cmulG, toPolyG_cmulG, toPolyG_cmulG]
  -- lift the cleared polynomial equation into the tower fraction field (towerAlg injective)
  rw [← (RatFunc.algebraMap_injective (CFieldSpec.K QFunNZ)).eq_iff]
  simp only [map_mul, map_add, hgden2, toPolyG_cmulG]
  -- the goal is now the cleared field equation, matching `hclear` term-by-term
  rw [← hGP, ← hLN, ← hLD, ← hAN, ← hAD, ← hGD]
  linear_combination hclear

/-! ### The composed field-level capstone — `D(g) + ∑ᵢ cᵢ·(Δvᵢ)/vᵢ = f`

In the **primitive regime** (`Dt ∈ k`), with the special part absent (`fₛ = 0`) and the polynomial
remainder vanishing (`prem = 0`, the `if cisZeroG prem` branch), the assembled `cIntegrate` output
`g + ∑ᵢ cᵢ·log(vᵢ)` differentiates back to `f = a/d` over the tower fraction field. The composition:
the Hermite field identity `D(gₕ) + hₛ = fₙ`, the primitive-poly field identity `D(pq) = fₚ`, the
canonical reconstruction `fₚ + fₙ = f` (`fₛ = 0`), and the **log-part residue match**
`hLog : logResidueSum Dt logs = hₛ` (the §5.6 Rothstein–Trager identity for the concrete `cLogPart`
output — proved abstractly in the primitive regime by `towerLogPart_eq_div_of_const_seed`; matching it
to the concrete residues is the documented bridge gap). -/

/-- **The composed field-level antiderivative identity** `D(g) + ∑ᵢ cᵢ·(Δvᵢ)/vᵢ = a/d` (the headline,
field form). In the primitive regime (`prem = 0`), writing `cn/dn = fₙ` the normal part and
`gₕ = nrm.rational.1/nrm.rational.2` the Hermite rational part of `fₙ`, `hₛ = hNum/hDen` its simple
residual, `pq` the integrated polynomial part of `fₚ`, the assembled rational part
`g = (nrm.rational.1 + pq·gden_H)/gden_H` and the log residue sum satisfy
`towerFractionFieldDeriv Dt g + logResidueSum Dt nrm.logs = towerAlg(a)/towerAlg(d)`. Composes the proven
field identities for Hermite (`cHermiteReduceTower_field_identity`, the exact-division/nonzero-divisor
preconditions `hHermite*`), the primitive polynomial part (`cPrimitivePolyIntegrate_field_identity` with
`prem = 0`), the canonical reconstruction (`canonicalRepFast_reconstructs`, special part `fₛ = 0` via
`hfs0`), and the **log-part residue match** `hLog`. -/
theorem cIntegrate_field_identity (Dt : CPolyG QFunNZ) (fuel : ℕ) (a d : CPolyG QFunNZ)
    (cands : List ℚ)
    -- canonical-split names
    (fp b ds cn dn : CPolyG QFunNZ)
    (hcanon : canonicalRepresentationFast Dt fuel a d = (fp, (b, ds), (cn, dn)))
    -- Hermite on the normal part `cn/dn`
    (gnumH gdenH hNum hDen : CPolyG QFunNZ)
    (hHermite : cHermiteReduceTower Dt fuel cn dn = ((gnumH, gdenH), (hNum, hDen)))
    -- the integrated polynomial part of `fp`
    (pq prem : CPolyG QFunNZ)
    (hpoly : cPrimitivePolyIntegrate Dt fuel fp = (pq, prem))
    (hprem0 : toPolyG prem = 0)
    -- the residue-grouped logs of the simple residual `hNum/hDen`
    (logs : List (ℚ × CPolyG QFunNZ))
    (_hlogsdef : logs = cLogPart Dt fuel hNum hDen cands)
    -- the assembled rational part `g = gnum/gden`
    (gnum gden : CPolyG QFunNZ)
    (hgnum : gnum = caddG (cmulG gnumH [CField.one]) (cmulG pq gdenH))
    (hgden : gden = gdenH)
    -- regularity: canonical-rep reconstructs, Hermite cleared, all denominators nonzero, fₛ = 0
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
    -- the §5.6 log-part residue match for the concrete logs (primitive regime; documented bridge gap)
    (hLog : logResidueSum Dt logs = towerAlg (toPolyG hNum) / towerAlg (toPolyG hDen)) :
    towerFractionFieldDeriv Dt (towerAlg (toPolyG gnum) / towerAlg (toPolyG gden))
        + logResidueSum Dt logs
      = towerAlg (toPolyG a) / towerAlg (toPolyG d) := by
  -- 1. canonical reconstruction `fp + b/ds + cn/dn = a/d`, with `fₛ = b/ds = 0`
  have hrecon := canonicalRepFast_reconstructs Dt fuel a d hcanreg
  simp only [hcanon] at hrecon
  -- `towerAlg = algebraMap (CFieldSpec.K QFunNZ)[X] …` is the same map `hrecon` uses; `fₛ = b/ds = 0`
  rw [show (algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (toPolyG b))
        / (algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (toPolyG ds))
      = towerAlg (toPolyG b) / towerAlg (toPolyG ds) from rfl, hfs0, add_zero] at hrecon
  -- 2. Hermite field identity `D(gₕ) + hₛ = cn/dn`
  have hHerm := cHermiteReduceTower_field_identity Dt fuel cn dn gnumH gdenH hDen gprimeNum resNum
    resDen hNum (by rw [hHermite]) (by rw [hHermite]) (by rw [hHermite]) hgprimeE hresNum hresDen
    hhNumE hq0 hfuelH hdvd hgdenHne hHDenne hdnne
  -- 3. primitive-poly field identity `D(pq) + prem = fp`, with `prem = 0`
  have hPoly := cPrimitivePolyIntegrate_field_identity Dt fuel fp
  rw [hpoly] at hPoly
  simp only [hprem0, map_zero, add_zero] at hPoly
  -- the combined rational part `g = gₕ + pq` over the field
  have hgsplit : towerAlg (toPolyG gnum) / towerAlg (toPolyG gden)
      = towerAlg (toPolyG gnumH) / towerAlg (toPolyG gdenH)
        + towerAlg (toPolyG pq) := by
    rw [hgnum, hgden, toPolyG_caddG, toPolyG_cmulG, toPolyG_cmulG, map_add, map_mul, map_mul]
    have hone : toPolyG ([CField.one] : CPolyG QFunNZ) = 1 := by
      rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_one, mul_zero, add_zero, map_one]
    rw [hone, map_one, mul_one]
    have hAgdenH : towerAlg (toPolyG gdenH) ≠ 0 := towerAlg_ne_zero hgdenHne
    field_simp
  -- the derivative splits by additivity
  rw [hgsplit, map_add]
  -- assemble: `(D(gₕ) + D(pq)) + logResidueSum = D(gₕ) + hₛ + D(pq)` and chase the identities
  rw [hLog]
  -- now: `D(gₕ) + D(pq) + hₛ = a/d`
  -- from Hermite: `D(gₕ) + hₛ = cn/dn`; from poly: `D(pq) = fp`; from canon: `fp + cn/dn = a/d`
  have hgoal : towerFractionFieldDeriv Dt (towerAlg (toPolyG gnumH) / towerAlg (toPolyG gdenH))
        + towerFractionFieldDeriv Dt (towerAlg (toPolyG pq))
        + towerAlg (toPolyG hNum) / towerAlg (toPolyG hDen)
      = towerAlg (toPolyG a) / towerAlg (toPolyG d) := by
    rw [hPoly]
    -- `D(gₕ) + fp + hₛ = (D(gₕ) + hₛ) + fp = cn/dn + fp = a/d`
    rw [show towerFractionFieldDeriv Dt (towerAlg (toPolyG gnumH) / towerAlg (toPolyG gdenH))
          + towerAlg (toPolyG fp) + towerAlg (toPolyG hNum) / towerAlg (toPolyG hDen)
        = (towerFractionFieldDeriv Dt (towerAlg (toPolyG gnumH) / towerAlg (toPolyG gdenH))
            + towerAlg (toPolyG hNum) / towerAlg (toPolyG hDen)) + towerAlg (toPolyG fp) by ring]
    rw [hHerm]
    -- `cn/dn + fp = a/d`, from the canonical reconstruction `fp + cn/dn = a/d`
    rw [add_comm]
    exact hrecon
  exact hgoal