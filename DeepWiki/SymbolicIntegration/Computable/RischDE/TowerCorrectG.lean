import DeepWiki.SymbolicIntegration.Computable.Tower.RischDE
import DeepWiki.SymbolicIntegration.Computable.RischDE.TowerGlue
import DeepWiki.SymbolicIntegration.Computable.SplitFactorTowerCorrectG

/-! # §6 RDE cleared-identity building blocks (carrier-generic)

This file collects the carrier-generic, gcd-agnostic §6 RDE building blocks consumed by the fuel-free RDE
cleared-identity development (`RischDE/Structural.lean`) and the `RatFunc ℚ` valuation lift
(`RischDE/RatFuncValuation.lean`):

* **Generic helper lemmas** — the `cgcdWf`-unit / exact-division / SPDE-peel helpers, stated
  `{α} [CField α] [CFieldSpec α]`-generic (their bodies are gcd-agnostic, taking the gcd `g`
  abstractly): `cgcdWf_isUnit_of_divided_gen`, `cdivWf_a_exact_of_gcd`, `cdivWf_b_exact_of_gcd`,
  `cdivWf_c_exact_of_cdvdGWf`, `cSPDE_peel_cleared_gen`, `toPolyG_cdivWf_exact_mul_gen`.
* **★ The derivation-generic pole order-drop** — the polynomial kernel of Bronstein Lemma 6.1.1 /
  Theorem 4.4.2: a derivation lowers the order of a pole at a **normal** irreducible by exactly one
  (`pow_sub_one_dvd_deriv_of_pow_dvd`, `not_pow_dvd_deriv_of_normal`,
  `emultiplicity_deriv_eq_sub_one_of_normal`), and its Wronskian-numerator valuation lift
  `emultiplicity_wronskian_numerator_eq_of_normal`. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

/-! ### Generic helper lemmas (the §6.4 helpers at any tower level)

The §6.4 SPDE certificate discharge needs five engine facts whose proofs only ever touch the gcd `g`
**abstractly** (through an `Associated (toPolyG g) (gcd …)` hypothesis and the generic
`cgcdWf`/`cdivWf`/`cdvdG`/`cdvdGWf` API). We state them generically over `{α} [CField α] [CFieldSpec α]`, so they
apply at `QFunNZG ℚ` (and any level). Each reuses the already generic `toPolyG_cgcdWf_dvd` /
`toPolyG_cdivWf_exact` / divisibility read-offs / `spde_const_base` / `spde_step_glue`. -/

/-- **The divided coefficients' fuel-free gcd is a unit** (generic): after dividing `a,b` by a nonzero gcd
`g`, the Wf gcd of `bd, ad` is a unit. -/
theorem cgcdWf_isUnit_of_divided_gen {α : Type*} [CField α] [CFieldSpec α]
    (a b ad bd g : CPolyG α) (hgne : toPolyG g ≠ 0)
    (hgassoc : Associated (toPolyG g) (gcd (toPolyG a) (toPolyG b)))
    (hdiva : toPolyG ad * toPolyG g = toPolyG a)
    (hdivb : toPolyG bd * toPolyG g = toPolyG b) :
    IsUnit (toPolyG (cgcdWf bd ad).1) := by
  obtain ⟨hGbd, hGad⟩ := toPolyG_cgcdWf_dvd bd ad
  set G := toPolyG (cgcdWf bd ad).1 with hGdef
  have hGg_a : G * toPolyG g ∣ toPolyG a := by rw [← hdiva]; exact mul_dvd_mul_right hGad _
  have hGg_b : G * toPolyG g ∣ toPolyG b := by rw [← hdivb]; exact mul_dvd_mul_right hGbd _
  have hGg_gcd : G * toPolyG g ∣ gcd (toPolyG a) (toPolyG b) := dvd_gcd hGg_a hGg_b
  have hGg_g : G * toPolyG g ∣ toPolyG g := hGg_gcd.trans hgassoc.symm.dvd
  obtain ⟨k, hk⟩ := hGg_g
  have hcancel : toPolyG g * 1 = toPolyG g * (G * k) := by rw [mul_one]; nth_rewrite 1 [hk]; ring
  have hG1 : G ∣ 1 := ⟨k, mul_left_cancel₀ hgne hcancel⟩
  exact isUnit_of_dvd_one hG1

/-- **The `a`-exact-division witness** (generic) `toPolyG (cdivWf a g) · toPolyG g = toPolyG a` from
`g ~ gcd(a, b)` (`g ∣ a`) and `g ≠ 0`. Generic mirror of `cdivFF_a_exact_of_gcd`
(`cdivFF := cdivWf`). -/
theorem cdivWf_a_exact_of_gcd {α : Type*} [CField α] [CFieldSpec α] (a b g : CPolyG α)
    (hg0 : cnormG g ≠ [])
    (hgassoc : Associated (toPolyG g) (gcd (toPolyG a) (toPolyG b))) :
    toPolyG (cdivWf a g) * toPolyG g = toPolyG a := by
  have hgdvd : toPolyG g ∣ toPolyG a := hgassoc.dvd.trans (gcd_dvd_left _ _)
  exact toPolyG_cdivWf_exact a g hg0 hgdvd

/-- **The `b`-exact-division witness** (generic) `toPolyG (cdivWf b g) · toPolyG g = toPolyG b` from
`g ~ gcd(a, b)` (`g ∣ b`). Generic mirror of `cdivFF_b_exact_of_gcd`. -/
theorem cdivWf_b_exact_of_gcd {α : Type*} [CField α] [CFieldSpec α] (a b g : CPolyG α)
    (hg0 : cnormG g ≠ [])
    (hgassoc : Associated (toPolyG g) (gcd (toPolyG a) (toPolyG b))) :
    toPolyG (cdivWf b g) * toPolyG g = toPolyG b := by
  have hgdvd : toPolyG g ∣ toPolyG b := hgassoc.dvd.trans (gcd_dvd_right _ _)
  exact toPolyG_cdivWf_exact b g hg0 hgdvd

/-- **The Wf `c`-exact-division witness** (generic) `toPolyG (cdivWf c g) · toPolyG g = toPolyG c`
from the fuel-free `cdvdGWf g c = true` branch (`g ∣ c`). -/
theorem cdivWf_c_exact_of_cdvdGWf {α : Type*} [CField α] [CFieldSpec α] (c g : CPolyG α)
    (hg0 : cnormG g ≠ [])
    (hdvd : cdvdGWf g c = true) :
    toPolyG (cdivWf c g) * toPolyG g = toPolyG c := by
  have hgdvd : toPolyG g ∣ toPolyG c := dvd_of_cdvdGWf g c hg0 hdvd
  exact toPolyG_cdivWf_exact c g hg0 hgdvd

/-- **One `cSPDEG` peel's cleared lifting** (generic) at `D = cmonomialDeriv Dt = implicitDeriv (toPolyG
Dt)`. Given the divided coefficients `ad, bd, cd`, the Bézout cofactors `r, z` with the certificate
`toPolyG bd · toPolyG r + toPolyG ad · toPolyG z = toPolyG cd`, and any `h` solving the reduced equation,
the reconstruction `q = ad·h + r` solves `ad·D(q) + bd·q = cd` over `(CFieldSpec.K α)[X]`. Generic mirror of
`cSPDE_peel_cleared` (carrier-agnostic, via `spde_step_glue`). -/
theorem cSPDE_peel_cleared_gen {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    (Dt ad bd cd r z h : CPolyG α)
    (hbez : toPolyG bd * toPolyG r + toPolyG ad * toPolyG z = toPolyG cd)
    (hred : toPolyG ad * Differential.implicitDeriv (toPolyG Dt) (toPolyG h)
        + (toPolyG bd + Differential.implicitDeriv (toPolyG Dt) (toPolyG ad)) * toPolyG h
      = toPolyG z - Differential.implicitDeriv (toPolyG Dt) (toPolyG r)) :
    toPolyG ad * Differential.implicitDeriv (toPolyG Dt) (toPolyG (caddG (cmulG ad h) r))
        + toPolyG bd * toPolyG (caddG (cmulG ad h) r)
      = toPolyG cd := by
  rw [toPolyG_caddG, toPolyG_cmulG]
  exact spde_step_glue (Differential.implicitDeriv (toPolyG Dt))
    (toPolyG ad) (toPolyG bd) (toPolyG cd) (toPolyG r) (toPolyG z) (toPolyG h) hbez hred

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]

/-! ### §6.2 — the generic normal-denominator cleared lifting and special-denominator primitive case -/

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **Generic exact-division reorientation** `toPolyG (cdivWf p q) · toPolyG q = toPolyG p` from `toPolyG
q ∣ toPolyG p` (nonzero divisor). Carrier-generic mirror of `toPolyG_cdivG_exact_mul`
(reorienting the already-generic `toPolyG_cdivWf_exact`). -/
theorem toPolyG_cdivWf_exact_mul_gen (p q : CPolyG α)
    (hq0 : cnormG q ≠ [])
    (hQdvd : toPolyG q ∣ toPolyG p) :
    toPolyG (cdivWf p q) * toPolyG q = toPolyG p :=
  toPolyG_cdivWf_exact p q hq0 hQdvd

/-! #### ★ The derivation-generic pole order-drop — the polynomial kernel of Bronstein Lemma 6.1.1 / Thm 4.4.2

The §6.1 normal-denominator necessity (Theorem 6.1.2(i) / Corollary 6.1.1) rests on the valuation fact that
*a derivation lowers the order of a pole at a **normal** irreducible by exactly one* — `νₚ(D y) = νₚ(y) − 1`
when `νₚ(y) < 0` and `p ∤ D p` (Bronstein Lemma 6.1.1, via Theorem 4.4.2). Its polynomial kernel — stated for
an arbitrary `Derivation` `D`, not just `Polynomial.derivative` — is recorded here in two halves:

* `pow_sub_one_dvd_deriv_of_pow_dvd` — the universally-true LOWER bound `q^n ∣ p ⟹ q^{n−1} ∣ D p` (no
  primality/normality/characteristic needed): the order drops by **at most** one. The `Derivation`-generic
  analogue of Mathlib's `pow_sub_one_dvd_derivative_of_pow_dvd`.
* `not_pow_dvd_deriv_of_normal` — the EXACT half at a normal prime: if `pⁿ ∥ f` (`n ≥ 1`, `p ∤ r` for
  `f = pⁿ·r`), `p` prime, `p ∤ D p` (normal), over a characteristic-zero field, then `pⁿ ∤ D f` — so the
  order is *exactly* `n − 1`. The Leibniz expansion `D f = p^{n−1}·(n·(Dp)·r + p·Dr)` has `p ∤ n·(Dp)·r`.

Assembled, `emultiplicity_deriv_eq_sub_one_of_normal` gives `emultiplicity p (D f) = emultiplicity p f − 1`
for a normal prime `p ∣ f`. These are the reusable §6.1 order-drop kernel; the genuine *fractional*-solution
necessity additionally needs the `K(t)`-valuation lift, weak normalization, and the `k⟨t⟩` differential
subring (see `hnormalize`'s remaining-obligation note in `ComputableRischDESolveExhaustiveness`). -/

section DerivationPoleOrderDrop

variable {R : Type*} [CommRing R]

/-- **Derivation-generic order-drop, lower bound** (`pow_sub_one_dvd_deriv_of_pow_dvd`): for any
`Derivation ℤ R R` and `q^n ∣ p`, `q^(n-1) ∣ D p`. The Leibniz expansion of `p = qⁿ·r` is
`D p = qⁿ·D r + (n • q^{n−1} • D q)·r`, both summands divisible by `q^{n−1}`. The `Derivation`-generic
analogue of Mathlib's `pow_sub_one_dvd_derivative_of_pow_dvd` (which is pinned to `Polynomial.derivative`) —
"a derivation drops a pole's order by at most one", needing no primality, normality, or characteristic. -/
theorem pow_sub_one_dvd_deriv_of_pow_dvd (D : Derivation ℤ R R) {p q : R} {n : ℕ}
    (hdvd : q ^ n ∣ p) : q ^ (n - 1) ∣ D p := by
  obtain ⟨r, rfl⟩ := hdvd
  rw [Derivation.leibniz, Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul, smul_eq_mul]
  -- `D(qⁿ·r) = qⁿ·D r + r·(n·q^{n−1}·D q)`, both divisible by `q^{n−1}`.
  refine dvd_add ((pow_dvd_pow q (Nat.sub_le n 1)).mul_right _) ?_
  exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) _

end DerivationPoleOrderDrop

section DerivationNormalOrderDrop

variable {K : Type*} [Field K] [CharZero K]

/-- **Derivation-generic order-drop, exact half at a normal prime** (`not_pow_dvd_deriv_of_normal`): over a
characteristic-zero field, for a prime `p` that is normal for the derivation (`¬ p ∣ D p`), if `f = pⁿ·r` with
`n ≥ 1` and `p ∤ r` (i.e. `pⁿ ∥ f` exactly), then `pⁿ ∤ D f`. Leibniz gives `D f = p^{n−1}·(n·(Dp)·r + p·Dr)`;
dividing a hypothetical `pⁿ ∣ D f` by `p^{n−1}` forces `p ∣ n·(Dp)·r`, but `p` is prime, `p ∤ Dp` (normal),
`p ∤ r`, and `(n : K) ≠ 0` (char zero) is a unit — contradiction. With the lower bound, this pins the order
at exactly `n − 1`: the heart of Bronstein Lemma 6.1.1 / Theorem 4.4.2. -/
theorem not_pow_dvd_deriv_of_normal (D : Derivation ℤ K[X] K[X]) {p r : K[X]} {n : ℕ}
    (hp : Prime p) (hnormal : ¬ p ∣ D p) (hn : 1 ≤ n) (hr : ¬ p ∣ r) :
    ¬ p ^ n ∣ D (p ^ n * r) := by
  -- write `n = m + 1`; Leibniz gives `D(p^{m+1}·r) = pᵐ·((m+1)·(Dp)·r + p·D r)`.
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  simp only [Nat.zero_add] at *
  have hexp : D (p ^ (m + 1) * r)
      = p ^ m * ((m + 1 : ℕ) • (D p * r) + p * D r) := by
    rw [Derivation.leibniz, Derivation.leibniz_pow, Nat.add_sub_cancel]
    rw [nsmul_eq_mul, nsmul_eq_mul, smul_eq_mul, pow_succ]
    push_cast; ring
  intro hdvd
  -- cancel `pᵐ` (`K[X]` a domain): `p ∣ (m+1)·(Dp)·r + p·D r`, hence `p ∣ (m+1)·(Dp)·r`.
  have hpm0 : p ^ m ≠ 0 := pow_ne_zero m hp.ne_zero
  rw [hexp, pow_succ, mul_dvd_mul_iff_left hpm0] at hdvd
  have hp_dvd : p ∣ (m + 1 : ℕ) • (D p * r) + p * D r := hdvd
  have hp_smul : p ∣ (m + 1 : ℕ) • (D p * r) :=
    (dvd_add_right (dvd_mul_right p (D r))).mp (by rwa [add_comm] at hp_dvd)
  -- `(m+1 : K) ≠ 0` (char zero) is a unit constant, so `p ∣ Dp·r`.
  rw [nsmul_eq_mul] at hp_smul
  have hunit : IsUnit ((m + 1 : ℕ) : K[X]) := by
    rw [← Polynomial.C_eq_natCast]
    exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by exact_mod_cast Nat.succ_ne_zero m))
  have hp_DpR : p ∣ D p * r := hunit.dvd_mul_left.mp hp_smul
  -- `p` prime ⟹ `p ∣ Dp` (contradicts normality) or `p ∣ r` (contradicts exactness).
  rcases (hp.dvd_mul.mp hp_DpR) with h | h
  · exact hnormal h
  · exact hr h

/-- **Derivation-generic exact pole order-drop** (`emultiplicity_deriv_eq_sub_one_of_normal`): over a
characteristic-zero field, for a prime `p` normal for the derivation (`¬ p ∣ D p`), if `f = pⁿ·r` with `n ≥ 1`
and `p ∤ r` (so `emultiplicity p f = n`), then `emultiplicity p (D f) = n − 1`. Both bounds combine: the
universal lower bound `p^{n−1} ∣ D f` (`pow_sub_one_dvd_deriv_of_pow_dvd`) and the normal exact bound
`pⁿ ∤ D f` (`not_pow_dvd_deriv_of_normal`). This is the polynomial-ring statement of Bronstein Lemma 6.1.1 /
Theorem 4.4.2 — "a derivation drops the order at a normal pole by exactly one" — the kernel the §6.1
fractional-solution denominator necessity (`hnormalize`) rests on, once lifted to `K(t)` valuations. -/
theorem emultiplicity_deriv_eq_sub_one_of_normal (D : Derivation ℤ K[X] K[X]) {p r : K[X]} {n : ℕ}
    (hp : Prime p) (hnormal : ¬ p ∣ D p) (hn : 1 ≤ n) (hr : ¬ p ∣ r) :
    emultiplicity p (D (p ^ n * r)) = (n - 1 : ℕ) := by
  apply emultiplicity_eq_of_dvd_of_not_dvd
  · exact pow_sub_one_dvd_deriv_of_pow_dvd D (Dvd.intro r rfl)
  · rw [Nat.sub_add_cancel hn]; exact not_pow_dvd_deriv_of_normal D hp hnormal hn hr

/-! #### ★ The Wronskian-numerator order-drop — the `K(t)`-valuation lift of Bronstein Lemma 6.1.1

For `y = a/b ∈ K(t)` the derivative is `Dy = (D a·b − a·D b)/b²`, so the `p`-adic valuation
`νₚ(Dy) = νₚ(D a·b − a·D b) − 2·νₚ(b)`. The fractional Lemma 6.1.1 (`νₚ(Dy) = νₚ(y) − 1` at a normal
pole `νₚ(y) < 0`) therefore reduces to the **polynomial** identity `νₚ(D a·b − a·D b) = νₚ(a) + νₚ(b) − 1`
when `p` is normal and `νₚ(a) < νₚ(b)` (a genuine pole). Writing `a = pᵐ·a'`, `b = pᵏ·b'` (`p ∤ a',b'`,
`m < k`), the Leibniz expansion is `D a·b − a·D b = p^{m+k−1}·((m−k)·(Dp)·a'·b' + p·(Da'·b' − a'·Db'))`,
whose cofactor is `p`-coprime: mod `p` it is `(m−k)·(Dp)·a'·b'`, a product of `p`-non-divisors
(`(m−k : K) ≠ 0` char zero, `p ∤ Dp` normal, `p ∤ a'`, `p ∤ b'`). This is the `K(t)`-valuation lift's
numerator core — Bronstein Lemma 6.1.1 lifted off `K[X]` to the fraction field `K(t) = RatFunc K`. -/
theorem emultiplicity_wronskian_numerator_eq_of_normal (D : Derivation ℤ K[X] K[X]) {p a' b' : K[X]}
    {m k : ℕ} (hp : Prime p) (hnormal : ¬ p ∣ D p) (hlt : m < k) (ha' : ¬ p ∣ a') (hb' : ¬ p ∣ b') :
    emultiplicity p (D (p ^ m * a') * (p ^ k * b') - (p ^ m * a') * D (p ^ k * b'))
      = (m + k - 1 : ℕ) := by
  -- `k ≥ 1`, so `m + k - 1` is honest; set `j := k - 1` with `k = j + 1`.
  have hk1 : 1 ≤ k := Nat.one_le_of_lt hlt
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one hk1)
  simp only [Nat.zero_add] at *
  -- Leibniz: `D(pⁿ·s) = pⁿ·D s + n·pⁿ⁻¹·(Dp)·s`.
  have hleib : ∀ (n : ℕ) (s : K[X]),
      D (p ^ n * s) = p ^ n * D s + (n : ℤ) • (p ^ (n - 1) * (D p * s)) := by
    intro n s
    rw [Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      nsmul_eq_mul, zsmul_eq_mul]
    push_cast; ring
  -- The combination factors as `p^{m+j}·W` with `W = (m−(j+1))·(Dp)·a'·b' + p·(Da'·b' − a'·Db')`.
  set W : K[X] := ((m : ℤ) - (j + 1 : ℕ)) • (D p * (a' * b')) + p * (D a' * b' - a' * D b') with hW
  have hfactor : D (p ^ m * a') * (p ^ (j + 1) * b') - (p ^ m * a') * D (p ^ (j + 1) * b')
      = p ^ (m + j) * W := by
    rw [hleib m a', hleib (j + 1) b', hW, Nat.add_sub_cancel]
    -- expand: cancel the `pᵐ·D a'·pʲ⁺¹·b'` and `pᵐ·a'·pʲ⁺¹·D b'` symmetric terms, leaving the `Dp` terms.
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0; simp only [pow_zero, one_mul, Nat.cast_zero, zero_sub, Nat.zero_add, zsmul_eq_mul]
      push_cast; ring
    · obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hmpos.ne'
      simp only [Nat.succ_sub_one, zsmul_eq_mul]
      push_cast
      rw [show m' + 1 + j = (m' + j) + 1 by ring, pow_succ]
      ring
  rw [hfactor]
  -- `νₚ(p^{m+j}·W) = (m+j) + νₚ(W)`, and `p ∤ W` gives `νₚ(W) = 0`.
  have hpne : (p : K[X]) ≠ 0 := hp.ne_zero
  have hWne : ¬ p ∣ W := by
    -- mod `p`: `W ≡ (m − (j+1))·(Dp)·(a'·b')`, a product of `p`-non-divisors.
    rw [hW]
    intro hdvd
    have hp_lead : p ∣ ((m : ℤ) - (j + 1 : ℕ)) • (D p * (a' * b')) :=
      (dvd_add_right (dvd_mul_right p _)).mp (by rwa [add_comm] at hdvd)
    rw [zsmul_eq_mul] at hp_lead
    -- the integer constant `m − (j+1) ≠ 0` (char zero, `m < j+1`) is a unit in `K[X]`.
    have hconstK : ((m : ℤ) - (j + 1 : ℕ) : K) ≠ 0 := by
      have hmj : ((m : ℤ) - (j + 1 : ℕ) : ℤ) ≠ 0 := by omega
      simpa using (Int.cast_ne_zero (α := K)).mpr hmj
    have hcast : (((m : ℤ) - (j + 1 : ℕ) : ℤ) : K[X]) = Polynomial.C ((m : ℤ) - (j + 1 : ℕ) : K) := by
      simp
    have hunit : IsUnit (((m : ℤ) - (j + 1 : ℕ) : ℤ) : K[X]) := by
      rw [hcast]; exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hconstK)
    have hp_DpAB : p ∣ D p * (a' * b') := hunit.dvd_mul_left.mp hp_lead
    rcases hp.dvd_mul.mp hp_DpAB with h | h
    · exact hnormal h
    · rcases hp.dvd_mul.mp h with h' | h'
      · exact ha' h'
      · exact hb' h'
  rw [emultiplicity_mul hp, emultiplicity_pow_self_of_prime hp, emultiplicity_eq_zero.mpr hWne,
    add_zero, show m + (j + 1) - 1 = m + j from by omega]

end DerivationNormalOrderDrop

/-! ### Restatements against the intended wording (anonymous `example`s) -/

-- ★ Derivation-generic pole order-drop, lower bound: `q^n ∣ p ⟹ q^{n−1} ∣ D p` (the §6.1 νₚ kernel half).
example {R : Type*} [CommRing R] (D : Derivation ℤ R R) {p q : R} {n : ℕ} (hdvd : q ^ n ∣ p) :
    q ^ (n - 1) ∣ D p :=
  pow_sub_one_dvd_deriv_of_pow_dvd D hdvd

-- ★ Derivation-generic pole order-drop, exact at a normal prime: `νₚ(D(pⁿ·r)) = n − 1` (Bronstein Lem 6.1.1).
example {K : Type*} [Field K] [CharZero K] (D : Derivation ℤ K[X] K[X]) {p r : K[X]} {n : ℕ}
    (hp : Prime p) (hnormal : ¬ p ∣ D p) (hn : 1 ≤ n) (hr : ¬ p ∣ r) :
    emultiplicity p (D (p ^ n * r)) = (n - 1 : ℕ) :=
  emultiplicity_deriv_eq_sub_one_of_normal D hp hnormal hn hr

/-! ### Axiom audit (the `QFunNZG ℚ` §6 RDE correctness rests only on the standard kernel axioms) -/

#print axioms pow_sub_one_dvd_deriv_of_pow_dvd
#print axioms not_pow_dvd_deriv_of_normal
#print axioms emultiplicity_deriv_eq_sub_one_of_normal

end DeepWiki.SymbolicIntegration
