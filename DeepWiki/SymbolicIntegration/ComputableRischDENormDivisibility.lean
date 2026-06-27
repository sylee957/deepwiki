import DeepWiki.SymbolicIntegration.ComputableRischDENormCompleteness

/-! # §6.1 Theorem 6.1.2 / Cor 6.1.1(ii) — the normal-pole divisibility necessity (`hdvd`)

`ComputableRischDENormCompleteness` collapsed the §6.2 completeness clause `hnorm` to the single
mathematical divisibility `eₙ ∣ dₙh²` (Bronstein **Corollary 6.1.1(ii)**, the necessity of the
normal-denominator condition at the normal poles), bundled as `RdeNormalDivisibilityResidual.hdvd`. This
file develops that divisibility — the valuation-theoretic argument of §6.1 — splitting it into a **fully
proven polynomial-ring layer** (the per-pole order ⟹ divisibility reduction, the Mathlib derivative
order-drop kernel) and a **precisely isolated tower-valuation residual** (the per-pole order *bound*
itself).

**Bronstein Cor 6.1.1(ii) (book p.185).** *If `Dy + fy = g` has a solution in `k(t)` then `eₙ ∣ dₙh²`*,
where `dₙ`/`eₙ` are the §3.5 normal parts of the denominators of `f`/`g`, `c = gcd(dₙ, eₙ)`, and
`h = gcd(eₙ, eₙ')/gcd(c, c')`. The book's proof: equation (6.2) `dₙhDq + (dₙhf − dₙDh)q = dₙh²g` has a
solution `q = yh ∈ k⟨t⟩` (Thm 6.1.2(i)); the left side lies in the differential subring `k⟨t⟩` (no normal
poles), so `dₙh²g ∈ k⟨t⟩`; hence for every irreducible normal `p ∣ eₙ`, `νₚ(dₙh²) ≥ −νₚ(g) = νₚ(eₙ)`,
giving `eₙ ∣ dₙh²`.

**The two layers (this file).**

* **The polynomial-ring layer is fully reachable** (axiom-clean, NO `native_decide`/`sorry`):
  - `dvd_of_emultiplicity_le_at_factors` — the pure-UFD reduction: in `K[X]`, `a ∣ b` if `a ≠ 0` and at
    every prime `p ∣ a`, `emultiplicity p a ≤ emultiplicity p b` (the "divisibility from the per-pole
    order bound" step, Mathlib `dvd_iff_emultiplicity_le` restricted to the relevant primes).
  - `multiplicity_gcd_derivative_of_root` / `rootMultiplicity_gcd_derivative_eq_sub_one` — the **Mathlib
    route**: at a root `a` of `e` (char zero), the derivative drops the order by exactly one
    (`derivative_rootMultiplicity_of_root`), so `gcd(e, e')` has order `νₐ(e) − 1` — the per-pole behaviour
    the §6.1 `h`-formula is built on.

* **The per-pole order bound is the precise tower-valuation residual** (isolated, NEVER `sorry`).
  The bound `νₚ(dₙh²) ≥ νₚ(eₙ)` at each normal pole `p ∣ eₙ` is the genuinely deep step — it consumes
  `νₚ(g) = −νₚ(eₙ)` (`eₙ` is the normal denominator of `g`) and the differential-subring fact about
  `k⟨t⟩` (no normal poles), neither of which is a bare `K[X]` statement. It is bundled as
  `RdeNormalPoleOrderResidual`, and `hdvd` is produced modulo it (`hdvd_of_poleOrderResidual`).

So `hdvd` reduces — through the fully proven polynomial-ring layer — to the single per-pole order bound
(Bronstein Cor 6.1.1(ii)'s valuation step), the precise §6.1 frontier. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

/-! ## The polynomial-ring layer (1): divisibility from the per-pole order bound

In a UFD, `a ∣ b` iff `emultiplicity p a ≤ emultiplicity p b` at every prime `p`
(`UniqueFactorizationMonoid.dvd_iff_emultiplicity_le`). For the §6.1 divisibility we only ever bound the
order at primes that actually divide `a = eₙ` (at the others `emultiplicity p a = 0`), so we package the
reduction in that restricted, directly usable form. Pure UFD algebra; no §6 mathematics, no `K[X]`
specifics beyond `UniqueFactorizationMonoid`. -/

section PolyRingReduction

variable {R : Type*} [CommMonoidWithZero R] [UniqueFactorizationMonoid R]

/-- **Divisibility from the per-pole order bound** (`dvd_of_emultiplicity_le_at_factors`): in a UFD, if
`a ≠ 0` and for every prime `p` *dividing* `a` the order does not increase
(`emultiplicity p a ≤ emultiplicity p b`), then `a ∣ b`. The reduction of a divisibility to a per-pole
(per-prime-factor) order comparison — Mathlib's `dvd_iff_emultiplicity_le` restricted to the primes that
matter (at a prime `p ∤ a`, `emultiplicity p a = 0`, so the bound is automatic). This is the exact shape
Bronstein Cor 6.1.1(ii) needs: it bounds `νₚ(dₙh²) ≥ νₚ(eₙ)` only at the normal poles `p ∣ eₙ`. -/
theorem dvd_of_emultiplicity_le_at_factors {a b : R} (ha : a ≠ 0)
    (hle : ∀ p : R, Prime p → p ∣ a → emultiplicity p a ≤ emultiplicity p b) :
    a ∣ b := by
  rw [UniqueFactorizationMonoid.dvd_iff_emultiplicity_le ha]
  intro p hp
  by_cases hpa : p ∣ a
  · exact hle p hp hpa
  · -- `p ∤ a` ⟹ `emultiplicity p a = 0 ≤ anything`.
    rw [emultiplicity_eq_zero.2 hpa]
    exact zero_le

/-- **The per-pole bound from the cleared product** (`emultiplicity_le_of_dvd_cleared`): the arithmetic
heart of Bronstein Cor 6.1.1(ii) at one normal pole `p`. From the book's three facts — `νₚ(gden) = νₚ(eₙ)`
(`gden`'s special part has no normal factor), `νₚ(gnum) = 0` (lowest terms: `p ∣ gden` and
`gcd(gnum, gden) = 1`), and `νₚ(dₙh²·gnum) ≥ νₚ(gden)` (the (6.2) RHS `dₙh²g = dₙh²gnum/gden` lies in the
differential subring `k⟨t⟩`, so its `p`-order is `≥ 0`) — the per-pole order bound
`emultiplicity p eₙ ≤ emultiplicity p (dₙh²)` follows by `emultiplicity_mul`: the `gnum` order cancels and
`νₚ(gden) = νₚ(eₙ)` shifts the bound onto `dₙh²`. Pure `emultiplicity` arithmetic over a UFD; this is what
turns the differential-subring fact `νₚ(dₙh²g) ≥ 0` into the divisibility-relevant `νₚ(dₙh²) ≥ νₚ(eₙ)`. -/
theorem emultiplicity_le_of_dvd_cleared {en gden gnum dnh2 : R} {p : R} (hp : Prime p)
    (hgden : emultiplicity p gden = emultiplicity p en)
    (hgnum : emultiplicity p gnum = 0)
    (hcleared : emultiplicity p gden ≤ emultiplicity p (dnh2 * gnum)) :
    emultiplicity p en ≤ emultiplicity p dnh2 := by
  rw [emultiplicity_mul hp, hgnum, add_zero] at hcleared
  rwa [hgden] at hcleared

end PolyRingReduction

/-! ## The polynomial-ring layer (2): the Mathlib derivative order-drop at a pole

The §6.1 multiplicity factor `h = gcd(eₙ, eₙ')/gcd(c, c')` rests on the fact that *the derivative lowers a
root's multiplicity by exactly one* — so `gcd(eₙ, eₙ')` carries order `νₚ(eₙ) − 1` at each pole, peeling
exactly one order. We record that fact, the Mathlib route the prior `hnorm` work flagged, over a `CharZero`
field at the level of linear factors `X − a` (`rootMultiplicity`/`multiplicity (X − C a)`), which is where
Mathlib's `derivative_rootMultiplicity_of_root` applies directly. -/

section DerivativeOrderDrop

variable {K : Type*} [Field K] [CharZero K]

/-- **The per-root derivative order-drop** (`rootMultiplicity_gcd_derivative_eq_sub_one`): at a root `a` of
`e ≠ 0` over a characteristic-zero field, `rootMultiplicity a (gcd e e') = rootMultiplicity a e − 1`. The
derivative drops the root's multiplicity by exactly one (`derivative_rootMultiplicity_of_root`), and the gcd
takes the min of the two, which (since `νₐ(e') = νₐ(e) − 1 < νₐ(e)`) is `νₐ(e) − 1`. The exact per-pole
behaviour the §6.1 `h = gcd(eₙ, eₙ')/gcd(c, c')` formula is built on — the Mathlib route flagged for
Bronstein Cor 6.1.1(ii). -/
theorem rootMultiplicity_gcd_derivative_eq_sub_one {e : K[X]} (he : e ≠ 0) {a : K}
    (ha : e.IsRoot a) :
    rootMultiplicity a (gcd e (derivative e)) = rootMultiplicity a e - 1 := by
  -- `gcd e e' ≠ 0`, so its root multiplicity is the min of those of `e` and `e'`.
  have hgne : gcd e (derivative e) ≠ 0 := by
    intro h
    exact he (eq_zero_of_zero_dvd (h ▸ gcd_dvd_left e (derivative e)))
  -- `νₐ(e') = νₐ(e) − 1` by the Mathlib derivative drop.
  have hderiv : rootMultiplicity a (derivative e) = rootMultiplicity a e - 1 :=
    derivative_rootMultiplicity_of_root ha
  -- `e` has a root, so `deg e ≥ 1`; in char zero this forces `e' ≠ 0`.
  have hdne : derivative e ≠ 0 := by
    rw [Polynomial.derivative_ne_zero]
    exact (Polynomial.natDegree_pos_iff_degree_pos.mpr
      (Polynomial.degree_pos_of_root he ha)).ne'
  -- multiplicity of the gcd = min of multiplicities (root multiplicity is monotone under `∣`,
  -- and `gcd e e' ∣ e`, `gcd e e' ∣ e'`, with the min attained at `e'`).
  refine le_antisymm ?_ ?_
  · -- `gcd ∣ e'`, so `νₐ(gcd) ≤ νₐ(e') = νₐ(e) − 1`.
    calc rootMultiplicity a (gcd e (derivative e))
        ≤ rootMultiplicity a (derivative e) :=
          rootMultiplicity_le_rootMultiplicity_of_dvd hdne (gcd_dvd_right e (derivative e)) a
      _ = rootMultiplicity a e - 1 := hderiv
  · -- `(X − a)^(νₐ(e)−1) ∣ e` and `∣ e'`, so it divides the gcd, giving `νₐ(e)−1 ≤ νₐ(gcd)`.
    rw [le_rootMultiplicity_iff hgne, dvd_gcd_iff]
    constructor
    · exact (pow_dvd_pow _ (Nat.sub_le _ 1)).trans (pow_rootMultiplicity_dvd e a)
    · rw [← hderiv]; exact pow_rootMultiplicity_dvd (derivative e) a

end DerivativeOrderDrop

/-! ## ★ The per-pole order bound residual (Bronstein Cor 6.1.1(ii)'s valuation step), and `hdvd`

The polynomial-ring layer reduced `eₙ ∣ dₙh²` to the per-pole order bound `emultiplicity p eₙ ≤
emultiplicity p (dₙh²)` at each prime `p ∣ eₙ` (`dvd_of_emultiplicity_le_at_factors`). That bound is the
genuine valuation-theoretic content of Bronstein Cor 6.1.1(ii): it needs `νₚ(g) = −νₚ(eₙ)` (`eₙ` the normal
denominator of `g`) and the differential-subring fact (`dₙh²g` has no normal poles, since the cleared left
side of (6.2) lies in `k⟨t⟩`). Neither is a bare `K[X]` statement — they live in the tower's
valuation/derivation theory — so the per-pole bound is the precise irreducible residual, bundled here as
`RdeNormalPoleOrderResidual`, with `hdvd` produced modulo it. -/

section PoleOrderResidual

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCore α]
  [CRischField α]

/-- **★ The per-pole order bound residual** `RdeNormalPoleOrderResidual Dt fnum fden gnum gden`: the
valuation step of Bronstein Cor 6.1.1(ii), in solvability-implies form. `hbound`: a `cRischDEG`-polynomial
solution forces, at every prime `p` of the §6.2 normal part `eₙ` (`= toPolyG (rdeNormEn …)`), the per-pole
order bound `emultiplicity p (toPolyG eₙ) ≤ emultiplicity p (toPolyG (dₙ·h²))` — the valuation inequality
`νₚ(dₙh²) ≥ νₚ(eₙ)` at the normal poles, which the book derives from `νₚ(g) = −νₚ(eₙ)` and `dₙh²g ∈ k⟨t⟩`
(the differential subring). `hen0`: `eₙ ≠ 0` (benign, free for weakly-normalized `gden ≠ 0`). This is the
single genuinely tower-deep piece of `hdvd`: the order bound at each pole, NOT derivable in bare `K[X]`. A
`Prop`-bundle of stated assumptions, NO `sorry`; `hbound` is the keystone. -/
structure RdeNormalPoleOrderResidual (Dt fnum fden gnum gden : CPolyG α) : Prop where
  /-- ★ Bronstein Cor 6.1.1(ii) valuation step: a polynomial solution forces, at every prime `p` of `eₙ`,
  `emultiplicity p eₙ ≤ emultiplicity p (dₙ·h²)` — the per-pole order bound `νₚ(dₙh²) ≥ νₚ(eₙ)`. -/
  hbound : (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
    ∀ p : (CFieldSpec.K α)[X], Prime p → p ∣ toPolyG (rdeNormEn Dt towerRischDEFuel gden) →
      emultiplicity p (toPolyG (rdeNormEn Dt towerRischDEFuel gden))
        ≤ emultiplicity p (toPolyG (rdeNormDnh2 Dt towerRischDEFuel fden gden))
  /-- The §6.2 normal part `eₙ` of `gden` is nonzero (benign — free for weakly-normalized `gden ≠ 0`). -/
  hen0 : toPolyG (rdeNormEn Dt towerRischDEFuel gden) ≠ 0

omit [CRischField α] in
/-- **★ `hdvd` from the per-pole order bound residual** (`hdvd_of_poleOrderResidual`): given a polynomial
solution and the per-pole order bound at every prime of `eₙ` (`RdeNormalPoleOrderResidual`), the §6.2
divisibility `toPolyG eₙ ∣ toPolyG (dₙ·h²)` follows — by the fully proven UFD reduction
`dvd_of_emultiplicity_le_at_factors` (a divisibility is exactly a per-pole order comparison). This is the
keystone of `RdeNormalDivisibilityResidual.hdvd` (**Bronstein Cor 6.1.1(ii)**), reduced to its valuation
step through the proven polynomial-ring layer. -/
theorem hdvd_of_poleOrderResidual (Dt fnum fden gnum gden : CPolyG α)
    (hres : RdeNormalPoleOrderResidual Dt fnum fden gnum gden)
    (hsol : ∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) :
    toPolyG (rdeNormEn Dt towerRischDEFuel gden)
      ∣ toPolyG (rdeNormDnh2 Dt towerRischDEFuel fden gden) :=
  dvd_of_emultiplicity_le_at_factors hres.hen0 (hres.hbound hsol)

end PoleOrderResidual

/-! ## ★ The cleared-form residual: shrinking `hbound` to the differential-subring fact

The per-pole bound `νₚ(dₙh²) ≥ νₚ(eₙ)` is itself derivable, by the proven arithmetic
`emultiplicity_le_of_dvd_cleared`, from the book's three per-pole facts:

* `νₚ(gden) = νₚ(eₙ)` — `gden = eₛeₙ` and the special part `eₛ` has no normal factor (`p ∣ eₙ` normal);
* `νₚ(gnum) = 0` — lowest terms (`p ∣ gden`, `gcd(gnum, gden) = 1`);
* `νₚ(dₙh²gnum) ≥ νₚ(gden)` — ★ the **only genuinely deep step**: `dₙh²g = dₙh²gnum/gden` lies in the
  differential subring `k⟨t⟩` (the cleared left side of (6.2) does), so its `p`-order is `≥ 0`.

The first two are structural normal-part / lowest-terms facts; the third is the differential-subring
content. We bundle exactly these as `RdeNormalClearedResidual`, *derive* the per-pole bound from it (so the
`emultiplicity`-bound residual is no longer assumed but produced), and thereby reduce `hdvd` to this
sharper, more faithful residual whose single deep clause is `dₙh²g ∈ k⟨t⟩`. -/

section ClearedResidual

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCore α]
  [CRischField α]

/-- **★ The cleared-form per-pole residual** `RdeNormalClearedResidual Dt fnum fden gnum gden`: Bronstein
Cor 6.1.1(ii) decomposed into its three per-pole facts (in solvability-implies form), at every prime `p` of
the §6.2 normal part `eₙ` (`= toPolyG (rdeNormEn …)`). `hgden`: `νₚ(gden) = νₚ(eₙ)` — the special part `eₛ`
contributes no `p` (structural normal-part fact). `hgnum`: `νₚ(gnum) = 0` — lowest terms (structural).
`hcleared`: ★ `νₚ(gden) ≤ νₚ(dₙh²·gnum)` — the **single genuinely deep step**, the differential-subring fact
`dₙh²g ∈ k⟨t⟩` (the cleared (6.2) RHS has nonnegative order at every normal pole). `hen0`: `eₙ ≠ 0`
(benign). Sharper than `RdeNormalPoleOrderResidual`: the per-pole order bound is no longer assumed but
*derived* from these (`poleOrderResidual_of_clearedResidual`), isolating the deep content to `hcleared`. -/
structure RdeNormalClearedResidual (Dt fnum fden gnum gden : CPolyG α) : Prop where
  /-- Normal-part: `νₚ(gden) = νₚ(eₙ)` at each prime `p ∣ eₙ` (special part has no normal factor). -/
  hgden : (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
    ∀ p : (CFieldSpec.K α)[X], Prime p → p ∣ toPolyG (rdeNormEn Dt towerRischDEFuel gden) →
      emultiplicity p (toPolyG gden) = emultiplicity p (toPolyG (rdeNormEn Dt towerRischDEFuel gden))
  /-- Lowest terms: `νₚ(gnum) = 0` at each prime `p ∣ eₙ` (`p ∣ gden`, `gcd(gnum, gden) = 1`). -/
  hgnum : (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
    ∀ p : (CFieldSpec.K α)[X], Prime p → p ∣ toPolyG (rdeNormEn Dt towerRischDEFuel gden) →
      emultiplicity p (toPolyG gnum) = 0
  /-- ★ Differential subring: `νₚ(gden) ≤ νₚ(dₙh²·gnum)` — `dₙh²g ∈ k⟨t⟩` (the deep step). -/
  hcleared : (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
    ∀ p : (CFieldSpec.K α)[X], Prime p → p ∣ toPolyG (rdeNormEn Dt towerRischDEFuel gden) →
      emultiplicity p (toPolyG gden)
        ≤ emultiplicity p (toPolyG (rdeNormDnh2 Dt towerRischDEFuel fden gden) * toPolyG gnum)
  /-- The §6.2 normal part `eₙ` of `gden` is nonzero (benign). -/
  hen0 : toPolyG (rdeNormEn Dt towerRischDEFuel gden) ≠ 0

omit [CRischField α] in
/-- **★ The per-pole bound residual from the cleared residual** (`poleOrderResidual_of_clearedResidual`):
the sharper `RdeNormalClearedResidual` (whose deep clause is the differential-subring fact `dₙh²g ∈ k⟨t⟩`)
*produces* the per-pole order bound residual `RdeNormalPoleOrderResidual`. At each prime `p ∣ eₙ` the proven
arithmetic `emultiplicity_le_of_dvd_cleared` turns the three facts (`νₚ(gden) = νₚ(eₙ)`, `νₚ(gnum) = 0`,
`νₚ(gden) ≤ νₚ(dₙh²gnum)`) into the bound `νₚ(eₙ) ≤ νₚ(dₙh²)`. So the `emultiplicity`-bound layer is not
assumed but derived — the divisibility `hdvd` reduces to this sharper residual. -/
theorem poleOrderResidual_of_clearedResidual (Dt fnum fden gnum gden : CPolyG α)
    (hres : RdeNormalClearedResidual Dt fnum fden gnum gden) :
    RdeNormalPoleOrderResidual Dt fnum fden gnum gden where
  hbound hsol p hp hpdvd :=
    emultiplicity_le_of_dvd_cleared hp (hres.hgden hsol p hp hpdvd) (hres.hgnum hsol p hp hpdvd)
      (hres.hcleared hsol p hp hpdvd)
  hen0 := hres.hen0

omit [CRischField α] in
/-- **★ `hdvd` from the cleared-form residual** (`hdvd_of_clearedResidual`): composing
`poleOrderResidual_of_clearedResidual` with `hdvd_of_poleOrderResidual`, the sharper cleared residual
(deep clause: `dₙh²g ∈ k⟨t⟩`) yields the §6.2 divisibility `toPolyG eₙ ∣ toPolyG (dₙ·h²)` on a polynomial
solution. The keystone `RdeNormalDivisibilityResidual.hdvd` (**Bronstein Cor 6.1.1(ii)**) reduced — through
the fully proven polynomial-ring + arithmetic layers — to a residual carrying only the differential-subring
fact (plus structural normal-part / lowest-terms / nonzero side conditions). -/
theorem hdvd_of_clearedResidual (Dt fnum fden gnum gden : CPolyG α)
    (hres : RdeNormalClearedResidual Dt fnum fden gnum gden)
    (hsol : ∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) :
    toPolyG (rdeNormEn Dt towerRischDEFuel gden)
      ∣ toPolyG (rdeNormDnh2 Dt towerRischDEFuel fden gden) :=
  hdvd_of_poleOrderResidual Dt fnum fden gnum gden
    (poleOrderResidual_of_clearedResidual Dt fnum fden gnum gden hres) hsol

end ClearedResidual

/-! ## ★ Discharging `RdeNormalDivisibilityResidual` from the cleared residual, and `hnorm`

`RdeNormalDivisibilityResidual` (`ComputableRischDENormCompleteness`) is the bundle `hnorm` was reduced to:
its keystone `hdvd` is exactly `solution ⟹ eₙ ∣ dₙh²` (Bronstein Cor 6.1.1(ii)), plus the benign `hen0`
(`eₙ ≠ 0`) and `hfuel` (per-run fuel). We now *build* that bundle from the sharper `RdeNormalClearedResidual`
(whose deep clause is only `dₙh²g ∈ k⟨t⟩`) together with the benign fuel bound — discharging `hdvd` through
the fully proven polynomial-ring + arithmetic layers. Composing with
`hnorm_of_divisibilityResidual`, the §6.2 completeness clause `hnorm` is produced from the cleared
residual; the deep §6.2 content is now exactly the differential-subring fact `dₙh²g ∈ k⟨t⟩`. -/

section Discharge

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCore α]
  [CRischField α]

omit [CRischField α] in
/-- **★ `RdeNormalDivisibilityResidual` from the cleared residual** (`divisibilityResidual_of_cleared`):
build the §6.2 divisibility residual (whose keystone `hdvd` is Bronstein Cor 6.1.1(ii)) from the sharper
`RdeNormalClearedResidual` plus the benign fuel bound `hfuel`. `hdvd` is discharged by
`hdvd_of_clearedResidual` (the proven polynomial-ring + arithmetic layers); `hen0` is the cleared residual's
nonzero clause transported across `cnormG_eq_nil_iff`; `hfuel` is passed through. This routes
`RdeNormalDivisibilityResidual.hdvd` — previously the single deep §6.2 gap — down to the cleared residual's
differential-subring clause `hcleared`. -/
theorem divisibilityResidual_of_cleared (Dt fnum fden gnum gden : CPolyG α)
    (hres : RdeNormalClearedResidual Dt fnum fden gnum gden)
    (hfuel : (CPolyG.cnormG (rdeNormDnh2 Dt towerRischDEFuel fden gden) : List α).length
      ≤ towerRischDEFuel) :
    RdeNormalDivisibilityResidual Dt fnum fden gnum gden where
  hdvd hsol := hdvd_of_clearedResidual Dt fnum fden gnum gden hres hsol
  hen0 := fun h => hres.hen0 ((CPolyG.cnormG_eq_nil_iff _).mp h)
  hfuel := hfuel

omit [CRischField α] in
/-- **★ `hnorm` from the cleared residual** (`hnorm_of_clearedResidual`): the §6.2 normal-denominator step
preserves solvability — a polynomial solution makes `cRdeNormalDenominatorG` return `some` — given the
cleared residual `RdeNormalClearedResidual` and the benign fuel bound. Composes
`divisibilityResidual_of_cleared` with the §6.2 completeness bridge `hnorm_of_divisibilityResidual`. This is
the **exact** `hnorm` clause of `RischDEInnerCompleteness`, now produced from a residual whose only deep
clause is the differential-subring fact `dₙh²g ∈ k⟨t⟩`. -/
theorem hnorm_of_clearedResidual (Dt fnum fden gnum gden : CPolyG α)
    (hres : RdeNormalClearedResidual Dt fnum fden gnum gden)
    (hfuel : (CPolyG.cnormG (rdeNormDnh2 Dt towerRischDEFuel fden gden) : List α).length
      ≤ towerRischDEFuel) :
    (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
      (cRdeNormalDenominatorG Dt towerRischDEFuel fnum fden gnum gden).isSome = true :=
  hnorm_of_divisibilityResidual Dt fnum fden gnum gden
    (divisibilityResidual_of_cleared Dt fnum fden gnum gden hres hfuel)

end Discharge

/-! ### Restatement against `RdeNormalDivisibilityResidual.hdvd`'s field type (anonymous `example`) -/

-- ★ The produced `hdvd` (`divisibilityResidual_of_cleared … |>.hdvd`) has exactly
-- `RdeNormalDivisibilityResidual.hdvd`'s field type — confirmed by using it as that field's value through a
-- full residual built from the cleared residual + a benign fuel bound.
example {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCore α]
    [CRischField α] (Dt fnum fden gnum gden : CPolyG α)
    (hres : RdeNormalClearedResidual Dt fnum fden gnum gden)
    (hfuel : (CPolyG.cnormG (rdeNormDnh2 Dt towerRischDEFuel fden gden) : List α).length
      ≤ towerRischDEFuel) :
    (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
      toPolyG (rdeNormEn Dt towerRischDEFuel gden)
        ∣ toPolyG (rdeNormDnh2 Dt towerRischDEFuel fden gden) :=
  (divisibilityResidual_of_cleared Dt fnum fden gnum gden hres hfuel).hdvd

/-! ### Final verdict (stated precisely)

**Is `hdvd` discharged?** **YES — modulo a single, precisely isolated tower-valuation fact (the
differential-subring step `dₙh²g ∈ k⟨t⟩`).** `divisibilityResidual_of_cleared` *builds* the full
`RdeNormalDivisibilityResidual` (the bundle `hnorm` reduced to) from `RdeNormalClearedResidual` + the benign
fuel bound, discharging the keystone `hdvd` (Bronstein Cor 6.1.1(ii)) through the fully proven layers. So
`hdvd` is no longer an *assumed* residual: it is *produced* from the sharper cleared residual.

**What is closed unconditionally (the polynomial-ring + arithmetic layers; NO `native_decide`/`sorry`):**
* `dvd_of_emultiplicity_le_at_factors` — the pure-UFD reduction: a divisibility is exactly the per-pole
  order bound at the primes dividing the divisor (`dvd_iff_emultiplicity_le` restricted);
* `rootMultiplicity_gcd_derivative_eq_sub_one` — the **Mathlib route**: the derivative drops a root's
  multiplicity by exactly one, so `gcd(e, e')` peels exactly one order — the per-pole behaviour the §6.1
  `h`-formula rests on (`derivative_rootMultiplicity_of_root`);
* `emultiplicity_le_of_dvd_cleared` — the arithmetic heart: the per-pole bound `νₚ(eₙ) ≤ νₚ(dₙh²)` follows
  from `νₚ(gden) = νₚ(eₙ)`, `νₚ(gnum) = 0`, and `νₚ(dₙh²gnum) ≥ νₚ(gden)` (the cleared product), via
  `emultiplicity_mul`;
* `poleOrderResidual_of_clearedResidual` / `hdvd_of_clearedResidual` / `divisibilityResidual_of_cleared` —
  the assembly producing `hdvd` (and the full divisibility residual) from the cleared residual.

**The single remaining residual** (`RdeNormalClearedResidual`, NEVER `sorry`): its three per-pole clauses,
of which `hgden` (`νₚ(gden) = νₚ(eₙ)`, normal-part structural) and `hgnum` (`νₚ(gnum) = 0`, lowest-terms
structural) are structural, and `hcleared` (`νₚ(gden) ≤ νₚ(dₙh²gnum)`) is the **one genuinely deep step** —
the differential-subring fact `dₙh²g ∈ k⟨t⟩` (the cleared (6.2) RHS has nonnegative order at every normal
pole). This is what the tower's valuation/derivation theory supplies and bare `K[X]` does not.

**Frontier effect.** With `hdvd` discharged modulo `RdeNormalClearedResidual`, the §6.2 completeness clause
`hnorm` is produced (`hnorm_of_clearedResidual`); `RischDEInnerCompleteness` reduces to `hbound` (nearly
done) + `hsolve` (the deep SPDE core) — the third residual `hdvd` is now down to the precisely isolated
differential-subring step, the genuine remaining §6.1 valuation content. -/

/-! ### Axiom audit (the polynomial-ring + arithmetic layers and the discharge assembly are axiom-clean;
NO `native_decide`, NO `sorry`) -/

#print axioms dvd_of_emultiplicity_le_at_factors
#print axioms rootMultiplicity_gcd_derivative_eq_sub_one
#print axioms emultiplicity_le_of_dvd_cleared
#print axioms hdvd_of_poleOrderResidual
#print axioms hdvd_of_clearedResidual
#print axioms divisibilityResidual_of_cleared
#print axioms hnorm_of_clearedResidual

end DeepWiki.SymbolicIntegration
