import DeepWiki.ComputableAlgebra.PolyReprDivision

/-! # The reduction step strictly decreases degree (division termination heart)

Over a computable *field*, one Euclidean-division cancellation step against `q` sends `p` to a
polynomial of strictly smaller `degree` (the zero polynomial's `degree = ⊥` handled by `WithBot`), by
leading-coefficient cancellation. This is what a fuel bound of `cdeg p + 1` needs to guarantee the
`cdivmodCore` remainder is fully reduced — the missing piece for a full generic gcd correctness.

The declarations here take `[CField α] [CFieldSpec α]` (with `CCommRing`/`CRingSpec` coming from the
field path, so `CRingSpec.toR = CFieldSpec.toK` definitionally), *not* the ambient `[CCommRing α]` the
rest of the file uses — hence the fresh `variable` block. See `docs/representation-independent-poly.md`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration.CPoly

variable {P : Type u → Type u} [CPoly P] {α : Type u} [CField α] [CFieldSpec α]

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
theorem cisZero_cdivmodCore_snd (fuel : ℕ) (p q : P α) (h : cisZero (P := P) p = true) :
    cisZero (P := P) (cdivmodCore fuel p q).2 = true := by
  cases fuel with
  | zero => rw [cdivmodCore]; exact h
  | succ n => rw [cdivmodCore, if_pos (Or.inr h)]; exact h

/-- **The remainder is fully reduced with enough fuel:** if `q ≠ 0` and `fuel > cdeg p`, then the
`cdivmodCore` remainder is either zero or of honest degree `< cdeg q` — the Euclidean remainder property.
Proven by threading `degree_reduce_step_lt` through the fuel recursion. -/
theorem cdivmodCore_remainder_reduced :
    ∀ (fuel : ℕ) (p q : P α), ¬ cisZero (P := P) q = true → cdeg p < fuel →
      cisZero (P := P) (cdivmodCore fuel p q).2 = true ∨ cdeg (cdivmodCore fuel p q).2 < cdeg q
  | 0, p, _, _, hlt => absurd hlt (by omega)
  | fuel + 1, p, q, hq, hlt => by
    rw [cdivmodCore]
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
      · exact Or.inl (cisZero_cdivmodCore_snd fuel p' q hz')
      · have hdeg : (toPoly p').degree < (toPoly p).degree :=
          hp' ▸ degree_reduce_step_lt p q hnz hq (not_lt.mp hnlt)
        have hp'ne : toPoly p' ≠ 0 := fun hh => hz' ((cisZero_iff p').mpr hh)
        have hcdeg : cdeg p' < cdeg p := by
          rw [cdeg_eq_natDegree, cdeg_eq_natDegree]
          exact Polynomial.natDegree_lt_natDegree hp'ne hdeg
        exact cdivmodCore_remainder_reduced fuel p' q hq (by omega)

/-- **The remainder is fully reduced** (fuel-less): if `q ≠ 0` the `cdivmod` remainder is zero or of
honest degree `< cdeg q` — the Euclidean remainder property, now hypothesis-free. -/
theorem cdivmod_remainder_reduced (p q : P α) (hq : ¬ cisZero (P := P) q = true) :
    cisZero (P := P) (cdivmod p q).2 = true ∨ cdeg (cdivmod p q).2 < cdeg q :=
  cdivmodCore_remainder_reduced (cdeg p + 1) p q hq (by omega)

omit [CFieldSpec α] in
/-- When the second argument is zero, `cgcdCore` returns the first. -/
theorem cgcdCore_of_cisZero_snd (fuel : ℕ) (a b : P α) (h : cisZero (P := P) b = true) :
    cgcdCore fuel a b = a := by
  cases fuel with
  | zero => rw [cgcdCore]
  | succ n => rw [cgcdCore, if_pos h]

/-- **Full gcd correctness (converse direction):** with `cdeg b < fuel`, `cgcdCore fuel a b` divides both
`toPoly a` and `toPoly b`. Together with `dvd_cgcdCore` this makes `cgcdCore` a genuine gcd. Proven by fuel
induction using `cdivmodCore_remainder_reduced` for the strictly-decreasing measure. -/
theorem cgcdCore_dvd :
    ∀ (fuel : ℕ) (a b : P α), cdeg b < fuel →
      toPoly (cgcdCore fuel a b) ∣ toPoly a ∧ toPoly (cgcdCore fuel a b) ∣ toPoly b
  | 0, _, _, h => absurd h (by omega)
  | fuel + 1, a, b, hfuel => by
    rw [cgcdCore]
    by_cases hb : cisZero (P := P) b = true
    · rw [if_pos hb]
      exact ⟨dvd_refl _, by rw [(cisZero_iff b).mp hb]; exact dvd_zero _⟩
    · rw [if_neg hb]
      set rem := (cdivmodCore (cdeg a + 1) a b).2 with hremdef
      have hid := toPoly_cdivmodCore (cdeg a + 1) a b
      have hreduced := cdivmodCore_remainder_reduced (cdeg a + 1) a b hb (by omega)
      rw [← hremdef] at hid hreduced
      rcases hreduced with hz | hlt
      · rw [cgcdCore_of_cisZero_snd fuel b rem hz]
        rw [(cisZero_iff rem).mp hz, add_zero] at hid
        exact ⟨by rw [hid]; exact dvd_mul_of_dvd_left (dvd_refl _) _, dvd_refl _⟩
      · have ih := cgcdCore_dvd fuel b rem (by omega)
        exact ⟨by rw [hid]; exact dvd_add (Dvd.dvd.mul_right ih.1 _) ih.2, ih.1⟩

/-- **Full gcd correctness** (fuel-less): `cgcd a b` divides both `a` and `b` — hypothesis-free. -/
theorem cgcd_dvd (a b : P α) :
    toPoly (cgcd a b) ∣ toPoly a ∧ toPoly (cgcd a b) ∣ toPoly b :=
  cgcdCore_dvd (cdeg b + 1) a b (by omega)

/-- **`cgcd` is a genuine gcd** (fuel-less): it divides both inputs and every common divisor divides it
(the universal property), assembling `cgcd_dvd` and `dvd_cgcd`. Instance-free. -/
theorem cgcd_isGCD (a b : P α) :
    toPoly (cgcd a b) ∣ toPoly a ∧ toPoly (cgcd a b) ∣ toPoly b ∧
      ∀ e, e ∣ toPoly a → e ∣ toPoly b → e ∣ toPoly (cgcd a b) :=
  ⟨(cgcd_dvd a b).1, (cgcd_dvd a b).2, fun e hea heb => dvd_cgcd a b e hea heb⟩

/-! ### Degree of products and powers (over a field the coefficient ring is a domain) -/

/-- `cdeg (p·q) = cdeg p + cdeg q` for nonzero `p, q` (field coefficients ⇒ no zero divisors). -/
theorem cdeg_cmul (p q : P α) (hp : ¬ cisZero (P := P) p = true) (hq : ¬ cisZero (P := P) q = true) :
    cdeg (mul p q) = cdeg p + cdeg q := by
  have hP : toPoly p ≠ 0 := fun h => hp ((cisZero_iff p).mpr h)
  have hQ : toPoly q ≠ 0 := fun h => hq ((cisZero_iff q).mpr h)
  rw [cdeg_eq_natDegree, toPoly_mul, Polynomial.natDegree_mul hP hQ, ← cdeg_eq_natDegree,
    ← cdeg_eq_natDegree]

/-- `cdeg (pⁿ) = n · cdeg p` for nonzero `p`. -/
theorem cdeg_cpow (p : P α) (n : ℕ) (hp : ¬ cisZero (P := P) p = true) :
    cdeg (cpow p n) = n * cdeg p := by
  have hP : toPoly p ≠ 0 := fun h => hp ((cisZero_iff p).mpr h)
  rw [cdeg_eq_natDegree, toPoly_cpow, Polynomial.natDegree_pow, ← cdeg_eq_natDegree]

/-- **Exact division** (fuel-less): if `q ∣ p` (and `q ≠ 0`), the `cdivmod` remainder is zero.
The reduced remainder is a multiple of `q` of degree `< cdeg q`, hence zero. Gateway to exact quotients
(cofactors, squarefree parts). -/
theorem cdivmod_exact (p q : P α) (hq : ¬ cisZero (P := P) q = true)
    (hdvd : toPoly q ∣ toPoly p) : cisZero (P := P) (cdivmod p q).2 = true := by
  rcases cdivmod_remainder_reduced p q hq with hz | hlt
  · exact hz
  · have hqR : toPoly q ∣ toPoly (cdivmod p q).2 := by
      have hid := toPoly_cdivmod p q
      have : toPoly (cdivmod p q).2
          = toPoly p - toPoly q * toPoly (cdivmod p q).1 := by rw [hid]; ring
      rw [this]; exact dvd_sub hdvd (dvd_mul_right _ _)
    by_cases hR0 : toPoly (cdivmod p q).2 = 0
    · exact (cisZero_iff _).mpr hR0
    · exfalso
      have hle := Polynomial.natDegree_le_natDegree (Polynomial.degree_le_of_dvd hqR hR0)
      rw [← cdeg_eq_natDegree, ← cdeg_eq_natDegree] at hle
      omega

/-- **Exact quotient recovers the dividend** (fuel-less): if `q ∣ p` then `p = q · (p / q)` — the
cofactor factorization. Direct from the division identity with a zero remainder (`cdivmod_exact`). -/
theorem toPoly_mul_cdiv_of_dvd (p q : P α) (hq : ¬ cisZero (P := P) q = true)
    (hdvd : toPoly q ∣ toPoly p) : toPoly p = toPoly q * toPoly (cdivmod p q).1 := by
  have hid := toPoly_cdivmod p q
  rw [(cisZero_iff _).mp (cdivmod_exact p q hq hdvd), add_zero] at hid
  exact hid

/-! ### The Diophantine solver (adopts the fuel-less `cgcdExt` + `cdivmod`)

`cdiophantine a b c` solves `s·a + t·b = c` whenever `gcd(a, b) ∣ c`: take the Bézout pair
`(g, s₀, t₀) = cgcdExt a b` (so `s₀·a + t₀·b = g`), scale by `k = c / g` — the fuel-less exact quotient —
to get `(k·s₀, k·t₀)`. Built entirely on the fuel-less generic engine. -/

/-- Solve `s·a + t·b = c` (requires `gcd(a,b) ∣ c`): scale the Bézout pair by `c / gcd(a,b)`. -/
def cdiophantine (a b c : P α) : P α × P α :=
  let r := cgcdExt a b
  let k := (cdivmod c r.1).1
  (mul k r.2.1, mul k r.2.2)

/-- **Diophantine correctness:** `s·a + t·b = c` for `(s, t) = cdiophantine a b c`, when the gcd
divides `c`. -/
theorem toPoly_cdiophantine (a b c : P α) (hg : ¬ cisZero (P := P) (cgcdExt a b).1 = true)
    (hdvd : toPoly (cgcdExt a b).1 ∣ toPoly c) :
    toPoly (cdiophantine a b c).1 * toPoly a + toPoly (cdiophantine a b c).2 * toPoly b = toPoly c := by
  have hbez := toPoly_cgcdExt a b
  have hexact := toPoly_mul_cdiv_of_dvd c (cgcdExt a b).1 hg hdvd
  simp only [cdiophantine, toPoly_mul]
  calc toPoly (cdivmod c (cgcdExt a b).1).1 * toPoly (cgcdExt a b).2.1 * toPoly a
        + toPoly (cdivmod c (cgcdExt a b).1).1 * toPoly (cgcdExt a b).2.2 * toPoly b
      = toPoly (cdivmod c (cgcdExt a b).1).1 *
          (toPoly (cgcdExt a b).2.1 * toPoly a + toPoly (cgcdExt a b).2.2 * toPoly b) := by ring
    _ = toPoly (cdivmod c (cgcdExt a b).1).1 * toPoly (cgcdExt a b).1 := by rw [hbez]
    _ = toPoly c := by rw [mul_comm]; exact hexact.symm

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

/-- `cmonic g` is an associate of `g` (they differ by the unit `C (leadingCoeff)`). -/
theorem cmonic_associated (g : P α) (hg : ¬ cisZero (P := P) g = true) :
    Associated (toPoly (cmonic g)) (toPoly g) := by
  have hG : toPoly g ≠ 0 := fun h => hg ((cisZero_iff g).mpr h)
  have hlc : (toPoly g).leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hG
  refine ⟨(isUnit_C.mpr (isUnit_iff_ne_zero.mpr hlc)).unit, ?_⟩
  rw [IsUnit.unit_spec, toPoly_cmonic, mul_right_comm, ← Polynomial.C_mul, inv_mul_cancel₀ hlc,
    Polynomial.C_1, one_mul]

/-- The canonical (monic) gcd `cmonic (cgcd a b)`. -/
def cmonicGcd (a b : P α) : P α := cmonic (cgcd a b)

/-- **The canonical monic gcd** (fuel-less): `cmonicGcd a b` is monic and divides both `a` and `b` —
the unique monic greatest common divisor. -/
theorem cmonicGcd_isGCD (a b : P α) (hg : ¬ cisZero (P := P) (cgcd a b) = true) :
    (toPoly (cmonicGcd a b)).Monic ∧
      toPoly (cmonicGcd a b) ∣ toPoly a ∧ toPoly (cmonicGcd a b) ∣ toPoly b := by
  have hassoc := cmonic_associated (cgcd a b) hg
  exact ⟨cmonic_monic _ hg, (hassoc.dvd_iff_dvd_left).mpr (cgcd_dvd a b).1,
    (hassoc.dvd_iff_dvd_left).mpr (cgcd_dvd a b).2⟩

/-! ### Squarefree part

`csquarefreePart p = p / gcd(p, p')` — the Risch/integration entry point. Its **cofactor
factorization** `p = gcd(p, p') · csquarefreePart p` is proven here (from the exact-quotient lemma);
the fact that the quotient is genuinely squarefree is the deeper property left as a frontier. -/

/-- The gcd of `p` and its derivative — the repeated-factor content, cofactor of the squarefree part. -/
def csquarefreeCofactor (p : P α) : P α := cgcd p (cderiv p)

/-- The squarefree part `p / gcd(p, p')`. -/
def csquarefreePart (p : P α) : P α := (cdivmod p (csquarefreeCofactor p)).1

/-- `gcd(p, p')` divides `p`. -/
theorem csquarefreeCofactor_dvd (p : P α) : toPoly (csquarefreeCofactor p) ∣ toPoly p :=
  (cgcd_dvd p (cderiv p)).1

/-- **Cofactor factorization:** `toPoly p = toPoly (gcd(p, p')) · toPoly (squarefreePart p)` for
nonzero `p`. -/
theorem toPoly_squarefree_factor (p : P α) (hp : ¬ cisZero (P := P) p = true) :
    toPoly p = toPoly (csquarefreeCofactor p) * toPoly (csquarefreePart p) := by
  have hdvd := csquarefreeCofactor_dvd p
  have hg : ¬ cisZero (P := P) (csquarefreeCofactor p) = true := fun hz => by
    rw [(cisZero_iff _).mp hz, zero_dvd_iff] at hdvd
    exact hp ((cisZero_iff p).mpr hdvd)
  exact toPoly_mul_cdiv_of_dvd p (csquarefreeCofactor p) hg hdvd

end DeepWiki.SymbolicIntegration.CPoly
