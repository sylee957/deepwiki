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

end DeepWiki.SymbolicIntegration
