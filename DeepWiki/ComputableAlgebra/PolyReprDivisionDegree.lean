import DeepWiki.ComputableAlgebra.PolyReprDivision

/-! # The reduction step strictly decreases degree (division termination heart)

Over a computable *field*, one Euclidean-division cancellation step against `q` sends `p` to a
polynomial of strictly smaller `degree` (the zero polynomial's `degree = ⊥` handled by `WithBot`), by
leading-coefficient cancellation. This is what a fuel bound of `cdeg p + 1` needs to guarantee the
`cdivmod` remainder is fully reduced — the missing piece for a full generic gcd correctness.

The declarations here take `[CField α] [CFieldSpec α]` (with `CCommRing`/`CRingSpec` coming from the
field path, so `CRingSpec.toR = CFieldSpec.toK` definitionally), *not* the ambient `[CCommRing α]` the
rest of the file uses — hence the fresh `variable` block. See `docs/representation-independent-poly.md`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration.CPolyRepr

variable {P : Type u → Type u} [CPolyRepr P] {α : Type u} [CField α] [CFieldSpec α]

/-- **One division step strictly lowers degree:** with `p, q ≠ 0` and `cdeg q ≤ cdeg p`, cancelling
`p`'s leading term against `q` gives a polynomial of strictly smaller `degree`. -/
theorem degree_reduce_step_lt (p q : P α)
    (hp : ¬ cisZero (P := P) p = true) (hq : ¬ cisZero (P := P) q = true) (hle : cdeg q ≤ cdeg p) :
    (toPoly (csub p (mul
        (cmonomial (P := P) (CField.div (clead p) (clead q)) (cdeg p - cdeg q)) q))).degree
      < (toPoly p).degree := by
  have hP : toPoly p ≠ 0 := fun h => hp ((cisZero_iff p).mpr h)
  have hQ : toPoly q ≠ 0 := fun h => hq ((cisZero_iff q).mpr h)
  have hlcP : (toPoly p).leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  have hlcQ : (toPoly q).leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ
  rw [toPoly_csub, toPoly_mul, toPoly_cmonomial]
  set c := CRingSpec.toR (CField.div (clead p) (clead q)) with hc
  set k := cdeg p - cdeg q with hk
  have hcval : c = (toPoly p).leadingCoeff / (toPoly q).leadingCoeff := by
    rw [hc, show CRingSpec.toR (CField.div (clead p) (clead q))
          = CFieldSpec.toK (CField.div (clead p) (clead q)) from rfl, CFieldSpec.toK_div,
      show CFieldSpec.toK (clead p) = CRingSpec.toR (clead p) from rfl,
      show CFieldSpec.toK (clead q) = CRingSpec.toR (clead q) from rfl,
      toR_clead_eq_leadingCoeff, toR_clead_eq_leadingCoeff]
  have hcne : c ≠ 0 := by rw [hcval]; exact div_ne_zero hlcP hlcQ
  have hCc : Polynomial.C c ≠ 0 := by rwa [Ne, Polynomial.C_eq_zero]
  have hdegR : (Polynomial.C c * X ^ k * toPoly q).degree = (toPoly p).degree := by
    rw [Polynomial.degree_mul, Polynomial.degree_mul, Polynomial.degree_C hcne,
      Polynomial.degree_X_pow, Polynomial.degree_eq_natDegree hQ, Polynomial.degree_eq_natDegree hP,
      ← cdeg_eq_natDegree, ← cdeg_eq_natDegree, hk, zero_add, ← Nat.cast_add]
    norm_cast; omega
  have hlcR : (Polynomial.C c * X ^ k * toPoly q).leadingCoeff = (toPoly p).leadingCoeff := by
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      Polynomial.leadingCoeff_X_pow, mul_one, hcval, div_mul_cancel₀ _ hlcQ]
  exact Polynomial.degree_sub_lt hdegR.symm hP hlcR.symm

omit [CFieldSpec α] in
/-- A division by a zero dividend leaves a zero remainder (the algorithm returns the dividend). -/
theorem cisZero_cdivmod_snd (fuel : ℕ) (p q : P α) (h : cisZero (P := P) p = true) :
    cisZero (P := P) (cdivmod fuel p q).2 = true := by
  cases fuel with
  | zero => rw [cdivmod]; exact h
  | succ n => rw [cdivmod, if_pos (Or.inr h)]; exact h

/-- **The remainder is fully reduced with enough fuel:** if `q ≠ 0` and `fuel > cdeg p`, then the
`cdivmod` remainder is either zero or of honest degree `< cdeg q` — the Euclidean remainder property.
Proven by threading `degree_reduce_step_lt` through the fuel recursion. -/
theorem cdivmod_remainder_reduced :
    ∀ (fuel : ℕ) (p q : P α), ¬ cisZero (P := P) q = true → cdeg p < fuel →
      cisZero (P := P) (cdivmod fuel p q).2 = true ∨ cdeg (cdivmod fuel p q).2 < cdeg q
  | 0, p, _, _, hlt => absurd hlt (by omega)
  | fuel + 1, p, q, hq, hlt => by
    rw [cdivmod]
    by_cases h : cdeg p < cdeg q ∨ cisZero (P := P) p = true
    · rw [if_pos h]
      rcases h with h1 | h2
      · exact Or.inr h1
      · exact Or.inl h2
    · rw [if_neg h]
      obtain ⟨hnlt, hnz⟩ := not_or.mp h
      set p' := csub p (mul
        (cmonomial (P := P) (CField.div (clead p) (clead q)) (cdeg p - cdeg q)) q) with hp'
      by_cases hz' : cisZero (P := P) p' = true
      · exact Or.inl (cisZero_cdivmod_snd fuel p' q hz')
      · have hdeg : (toPoly p').degree < (toPoly p).degree :=
          hp' ▸ degree_reduce_step_lt p q hnz hq (not_lt.mp hnlt)
        have hp'ne : toPoly p' ≠ 0 := fun hh => hz' ((cisZero_iff p').mpr hh)
        have hcdeg : cdeg p' < cdeg p := by
          rw [cdeg_eq_natDegree, cdeg_eq_natDegree]
          exact Polynomial.natDegree_lt_natDegree hp'ne hdeg
        exact cdivmod_remainder_reduced fuel p' q hq (by omega)

omit [CFieldSpec α] in
/-- When the second argument is zero, `cgcd` returns the first. -/
theorem cgcd_of_cisZero_snd (fuel : ℕ) (a b : P α) (h : cisZero (P := P) b = true) :
    cgcd fuel a b = a := by
  cases fuel with
  | zero => rw [cgcd]
  | succ n => rw [cgcd, if_pos h]

/-- **Full gcd correctness (converse direction):** with `cdeg b < fuel`, `cgcd fuel a b` divides both
`toPoly a` and `toPoly b`. Together with `dvd_cgcd` this makes `cgcd` a genuine gcd. Proven by fuel
induction using `cdivmod_remainder_reduced` for the strictly-decreasing measure. -/
theorem cgcd_dvd :
    ∀ (fuel : ℕ) (a b : P α), cdeg b < fuel →
      toPoly (cgcd fuel a b) ∣ toPoly a ∧ toPoly (cgcd fuel a b) ∣ toPoly b
  | 0, _, _, h => absurd h (by omega)
  | fuel + 1, a, b, hfuel => by
    rw [cgcd]
    by_cases hb : cisZero (P := P) b = true
    · rw [if_pos hb]
      exact ⟨dvd_refl _, by rw [(cisZero_iff b).mp hb]; exact dvd_zero _⟩
    · rw [if_neg hb]
      set rem := (cdivmod (cdeg a + 1) a b).2 with hremdef
      have hid := toPoly_cdivmod (cdeg a + 1) a b
      have hreduced := cdivmod_remainder_reduced (cdeg a + 1) a b hb (by omega)
      rw [← hremdef] at hid hreduced
      rcases hreduced with hz | hlt
      · rw [cgcd_of_cisZero_snd fuel b rem hz]
        rw [(cisZero_iff rem).mp hz, add_zero] at hid
        exact ⟨by rw [hid]; exact dvd_mul_of_dvd_left (dvd_refl _) _, dvd_refl _⟩
      · have ih := cgcd_dvd fuel b rem (by omega)
        exact ⟨by rw [hid]; exact dvd_add (Dvd.dvd.mul_right ih.1 _) ih.2, ih.1⟩

/-- **`cgcd` is a genuine gcd:** it divides both inputs and is divisible by every common divisor
(the universal property of a greatest common divisor), assembling `cgcd_dvd` and `dvd_cgcd`. This is
the instance-free statement — no `DecidableEq`/`GCDMonoid` on the abstract field needed. -/
theorem cgcd_isGCD (fuel : ℕ) (a b : P α) (h : cdeg b < fuel) :
    toPoly (cgcd fuel a b) ∣ toPoly a ∧ toPoly (cgcd fuel a b) ∣ toPoly b ∧
      ∀ e, e ∣ toPoly a → e ∣ toPoly b → e ∣ toPoly (cgcd fuel a b) :=
  ⟨(cgcd_dvd fuel a b h).1, (cgcd_dvd fuel a b h).2, fun e hea heb => dvd_cgcd fuel a b e hea heb⟩

/-- **Exact division:** if `q ∣ p` (and `q ≠ 0`, `fuel > cdeg p`), the `cdivmod` remainder is zero.
The reduced remainder is a multiple of `q` of degree `< cdeg q`, hence zero. Gateway to exact quotients
(cofactors, squarefree parts). -/
theorem cdivmod_exact (fuel : ℕ) (p q : P α) (hq : ¬ cisZero (P := P) q = true)
    (hfuel : cdeg p < fuel) (hdvd : toPoly q ∣ toPoly p) :
    cisZero (P := P) (cdivmod fuel p q).2 = true := by
  rcases cdivmod_remainder_reduced fuel p q hq hfuel with hz | hlt
  · exact hz
  · have hqR : toPoly q ∣ toPoly (cdivmod fuel p q).2 := by
      have hid := toPoly_cdivmod fuel p q
      have : toPoly (cdivmod fuel p q).2
          = toPoly p - toPoly q * toPoly (cdivmod fuel p q).1 := by rw [hid]; ring
      rw [this]; exact dvd_sub hdvd (dvd_mul_right _ _)
    by_cases hR0 : toPoly (cdivmod fuel p q).2 = 0
    · exact (cisZero_iff _).mpr hR0
    · exfalso
      have hle := Polynomial.natDegree_le_natDegree (Polynomial.degree_le_of_dvd hqR hR0)
      rw [← cdeg_eq_natDegree, ← cdeg_eq_natDegree] at hle
      omega

/-- **Exact quotient recovers the dividend:** if `q ∣ p` then `p = q · (p / q)` — the cofactor
factorization. Direct from the division identity with a zero remainder (`cdivmod_exact`). -/
theorem toPoly_mul_cdiv_of_dvd (fuel : ℕ) (p q : P α) (hq : ¬ cisZero (P := P) q = true)
    (hfuel : cdeg p < fuel) (hdvd : toPoly q ∣ toPoly p) :
    toPoly p = toPoly q * toPoly (cdivmod fuel p q).1 := by
  have hid := toPoly_cdivmod fuel p q
  rw [(cisZero_iff _).mp (cdivmod_exact fuel p q hq hfuel hdvd), add_zero] at hid
  exact hid

/-! ### Monic normalization (the canonical associate) -/

/-- Scale a polynomial to monic by its inverse leading coefficient. -/
def cmonic (p : P α) : P α := scale (CField.inv (clead p)) p

/-- `toPoly (cmonic p) = C (leadingCoeff⁻¹) · toPoly p` — the associate scaled to be monic. -/
theorem toPoly_cmonic (p : P α) :
    toPoly (cmonic p) = Polynomial.C ((toPoly p).leadingCoeff)⁻¹ * toPoly p := by
  rw [cmonic, toPoly_scale]
  congr 2
  show CFieldSpec.toK (CField.inv (clead p)) = _
  rw [CFieldSpec.toK_inv, show CFieldSpec.toK (clead p) = CRingSpec.toR (clead p) from rfl,
    toR_clead_eq_leadingCoeff]

/-- `cmonic p` is monic for nonzero `p` (its leading coefficient is `1`). -/
theorem cmonic_monic (p : P α) (hp : ¬ cisZero (P := P) p = true) : (toPoly (cmonic p)).Monic := by
  have hP : toPoly p ≠ 0 := fun h => hp ((cisZero_iff p).mpr h)
  have hlcP : (toPoly p).leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  rw [Polynomial.Monic, toPoly_cmonic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
    inv_mul_cancel₀ hlcP]

/-- `cmonic` reduces (dense): `2 + 4x` scales to the monic `1/2 + x`. -/
example : cmonic ([2, 4] : List ℚ) = ([1/2, 1] : List ℚ) := by native_decide

end DeepWiki.SymbolicIntegration.CPolyRepr
