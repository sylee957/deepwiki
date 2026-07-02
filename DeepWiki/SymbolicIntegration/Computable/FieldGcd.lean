import DeepWiki.SymbolicIntegration.Computable.Field

/-! # Generic division / gcd / derivative over a `CField`
Stage B of the generic polynomial engine: **generic `cdivmodG`/`cgcdExtG`/`cderivG`** — the `Compute.*`
Euclidean division, extended Euclidean algorithm, and formal derivative, mirrored over an arbitrary
`[CField α]` (ℚ-operations replaced by `CField.add`/`mul`/`neg`/`inv`/`isZero`, `toPoly` by `toPolyG`).
Their correctness (`toPolyG_cdivmodG` Euclidean identity, `toPolyG_cgcdExtG` Bézout, `cgcdTerminatesG` +
`toPolyG_cgcdExtG_dvd`, `toPolyG_cderivG`) is proven on all inputs over any `CField`. Coherence lemmas
(`cdivmodG (α := ℚ) = cdivmod`, …) specialize back to the concrete engine. The level-1 ℚ(x) field
instance is the generic `QFunNZG ℚ` (`ComputableTowerField`), the bottom of the recursive tower. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-! ### Generic formal derivative `cderivG` over a `CField`

`cderivG [a₀, a₁, a₂, …] = [1·a₁, 2·a₂, 3·a₃, …]`: drop the constant coefficient and scale the `k`-th
remaining coefficient by `k`. The natural-number scaling `k · a` is built from `CField.add` by the
helper `nsmulG`, whose `toK` is the field `k • _ = (k : K) * _`. The correctness `toPolyG_cderivG`
realizes `Polynomial.derivative` exactly, mirroring the concrete `toPoly_cderiv`. -/

namespace CPolyG

variable {α : Type*} [CField α]
variable [CFieldSpec α]

/-- **Generic `ℕ`-scaling** `nsmulG k a` = `a + a + … + a` (`k` times), built from `CField.add`. The
coefficient-degree multiplier for the formal derivative; `toK` reads it as `k • _ = (k : K) * _`. -/
def nsmulG : ℕ → α → α
  | 0, _ => CField.zero
  | k + 1, a => CField.add a (nsmulG k a)

/-- `toK (nsmulG k a) = k • toK a` in `K`. -/
@[denote] theorem toK_nsmulG (k : ℕ) (a : α) : CFieldSpec.toK (nsmulG k a) = k • CFieldSpec.toK a := by
  induction k with
  | zero => rw [nsmulG, CFieldSpec.toK_zero, zero_smul]
  | succ n ih => rw [nsmulG, CFieldSpec.toK_add, ih, succ_nsmul']

/-- **Generic formal derivative** `cderivG [a₀,a₁,a₂,…] = [1·a₁, 2·a₂, 3·a₃, …]`: drop the constant
coefficient, scale the `k`-th remaining coefficient by `k`. -/
def cderivG : CPolyG α → CPolyG α
  | [] => []
  | _ :: as => go 1 as
where
  /-- Auxiliary: from degree `k`, emit `nsmulG k a` for each coefficient `a` (the derivative tail). -/
  go : ℕ → CPolyG α → CPolyG α
  | _, [] => []
  | k, a :: as => nsmulG k a :: go (k + 1) as

/-- **`cderivG` realizes the `K[X]` derivative**: `toPolyG (cderivG p) = Polynomial.derivative
(toPolyG p)`. -/
@[denote] theorem toPolyG_cderivG (p : CPolyG α) :
    toPolyG (cderivG p) = Polynomial.derivative (toPolyG p) := by
  suffices h : ∀ (as : CPolyG α) (k : ℕ),
      toPolyG (cderivG.go k as)
        = (k : (CFieldSpec.K α)[X]) * toPolyG as + X * Polynomial.derivative (toPolyG as) by
    cases p with
    | nil => simp [cderivG]
    | cons a as =>
      show toPolyG (cderivG.go 1 as) = Polynomial.derivative (toPolyG (a :: as))
      rw [h as 1, toPolyG_cons, derivative_add, derivative_C, derivative_mul, derivative_X]
      push_cast; ring
  intro as
  induction as with
  | nil => intro k; simp [cderivG.go]
  | cons b bs ih =>
    intro k
    show toPolyG (nsmulG k b :: cderivG.go (k + 1) bs) = _
    rw [toPolyG_cons, ih (k + 1), toPolyG_cons, derivative_add, derivative_C, derivative_mul,
      derivative_X]
    have hk : Polynomial.C (CFieldSpec.toK (nsmulG k b)) = (k : (CFieldSpec.K α)[X]) * Polynomial.C (CFieldSpec.toK b) := by
      rw [toK_nsmulG, nsmul_eq_mul, map_mul, map_natCast]
    rw [hk]; push_cast; ring

/-! ### Correctness of the generic Euclidean division `cdivmodG`

`cdivmodG`/`cdivG`/`cmodG`/`cdvdG`/`cgcdExtG` are defined upstream (engine, `[CField α]`-only,
`GenericPolyEngine`); here we prove their correctness with the bridge `[CFieldSpec α]` in scope:
`toPolyG p = toPolyG q · toPolyG (cdivG…) + toPolyG (cmodG…)` and a strict normalized-length / degree
drop. The leading-term match `c = clead p / clead q` is `CField.div`. -/

/-- **Euclidean-division identity through `toPolyG`** (`q` already normalized and nonzero, any fuel):
`toPolyG p = toPolyG (quotient) · toPolyG q + toPolyG (remainder)`. -/
theorem toPolyG_cdivmodG (fuel : ℕ) (p q : CPolyG α) (hqn : cnormG q = q) (hq0 : q ≠ []) :
    toPolyG p
      = toPolyG (cdivmodG fuel p q).1 * toPolyG q + toPolyG (cdivmodG fuel p q).2 := by
  induction fuel generalizing p with
  | zero => simp [cdivmodG, toPolyG_cnormG]
  | succ fuel ih =>
    have hcz : cisZeroG q = false := by
      rw [cisZeroG, hqn]; exact List.isEmpty_eq_false_iff.mpr hq0
    rw [cdivmodG]
    simp only [hqn, hcz, Bool.false_eq_true, if_false]
    by_cases hlen : (cnormG p : List α).length < (q : List α).length
    · simp [hlen, toPolyG_cnormG]
    · simp only [hlen, if_false]
      rcases hqr : cdivmodG fuel (cnormG (csubG (cnormG p)
          (cmulG (cshiftG ((cnormG p : List α).length - (q : List α).length)
            [CField.div (cleadG (cnormG p)) (cleadG q)]) q))) q
        with ⟨quo, rem⟩
      have hih := ih (cnormG (csubG (cnormG p)
          (cmulG (cshiftG ((cnormG p : List α).length - (q : List α).length)
            [CField.div (cleadG (cnormG p)) (cleadG q)]) q)))
      rw [hqr] at hih
      simp only [denote] at hih ⊢
      linear_combination hih

omit [CFieldSpec α] in
/-- `cdivmodG` **normalizes its divisor**: `cdivmodG fuel p q = cdivmodG fuel p (cnormG q)`. -/
theorem cdivmodG_cnormG_right (fuel : ℕ) (p q : CPolyG α) :
    cdivmodG fuel p q = cdivmodG fuel p (cnormG q) := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp only [cdivmodG, cnormG_idem]

/-- **Euclidean-division identity through `toPolyG`** for an arbitrary nonzero divisor (`cnormG q ≠ []`,
any fuel): `toPolyG p = toPolyG (quotient) · toPolyG q + toPolyG (remainder)`. -/
theorem toPolyG_cdivmodG' (fuel : ℕ) (p q : CPolyG α) (hq0 : cnormG q ≠ []) :
    toPolyG p
      = toPolyG (cdivmodG fuel p q).1 * toPolyG q + toPolyG (cdivmodG fuel p q).2 := by
  rw [cdivmodG_cnormG_right]
  simpa [toPolyG_cnormG] using toPolyG_cdivmodG fuel p (cnormG q) (cnormG_idem q) hq0

/-- **`cdvdG` reads as remainder-zero**: `cdvdG fuel q p = true ↔ toPolyG (cmodG fuel p q) = 0`. -/
theorem cdvdG_iff (fuel : ℕ) (q p : CPolyG α) :
    cdvdG fuel q p = true ↔ toPolyG (cmodG fuel p q) = 0 := by
  rw [cdvdG, cisZeroG_iff]

/-! #### Degree-drop / termination for `cdivmodG`

The remainder loop strictly shortens the normalized list (`stepG_length_lt`), so `cmodG fuel p q`
is properly reduced (`cmodG_length_lt`). The single-step degree drop is a field fact about
`(CFieldSpec.K α)[X]` (`degreeG_reduce_step_lt`), proven exactly as the concrete `degree_reduce_step_lt`. -/

/-- For a nonzero generic polynomial, the normalized list length is `natDegree + 1`. -/
theorem length_cnormG_of_ne (p : CPolyG α) (h : cnormG p ≠ []) :
    (cnormG p : List α).length = (toPolyG p).natDegree + 1 := by
  have hd := cdegG_eq_natDegree p
  rw [cdegG] at hd
  have hlen : 1 ≤ (cnormG p : List α).length := List.length_pos_iff.mpr h
  omega

/-- **One Euclidean-division step strictly drops the degree** in `(CFieldSpec.K α)[X]`: subtracting the
leading-term-matching multiple `C (lcP/lcQ)·X^(degP−degQ)·Q` cancels the top coefficient. -/
theorem degreeG_reduce_step_lt {P Q : (CFieldSpec.K α)[X]} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree ≤ P.natDegree) :
    (P - C (P.leadingCoeff / Q.leadingCoeff)
        * X ^ (P.natDegree - Q.natDegree) * Q).degree < P.degree := by
  have hQlc : Q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ
  have hPlc : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  have hc0 : P.leadingCoeff / Q.leadingCoeff ≠ 0 := div_ne_zero hPlc hQlc
  have hCc : (C (P.leadingCoeff / Q.leadingCoeff)) ≠ 0 := by rwa [Ne, Polynomial.C_eq_zero]
  have hXk : (X ^ (P.natDegree - Q.natDegree) : (CFieldSpec.K α)[X]) ≠ 0 :=
    pow_ne_zero _ Polynomial.X_ne_zero
  set T := C (P.leadingCoeff / Q.leadingCoeff) * X ^ (P.natDegree - Q.natDegree) * Q with hT
  have hT0 : T ≠ 0 := mul_ne_zero (mul_ne_zero hCc hXk) hQ
  have hTnd : T.natDegree = P.natDegree := by
    rw [hT, Polynomial.natDegree_mul (mul_ne_zero hCc hXk) hQ,
      Polynomial.natDegree_mul hCc hXk, Polynomial.natDegree_C, Polynomial.natDegree_X_pow]
    omega
  have hTlc : T.leadingCoeff = P.leadingCoeff := by
    rw [hT, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      Polynomial.leadingCoeff_X_pow, mul_one, div_mul_cancel₀ _ hQlc]
  exact Polynomial.degree_sub_lt
    (by rw [Polynomial.degree_eq_natDegree hP, Polynomial.degree_eq_natDegree hT0, hTnd]) hP
    hTlc.symm

omit [CFieldSpec α] in
/-- `cleadG` is invariant under `cnormG`: `cleadG (cnormG p) = cleadG p`. -/
theorem cleadG_cnormG (p : CPolyG α) : cleadG (cnormG p) = cleadG p := by
  simp only [cleadG, cnormG_idem]

omit [CFieldSpec α] in
/-- `cisZeroG` is invariant under `cnormG`. -/
theorem cisZeroG_cnormG (q : CPolyG α) : cisZeroG (cnormG q) = cisZeroG q := by
  simp only [cisZeroG, cnormG_idem]

omit [CFieldSpec α] in
/-- `cdegG` is invariant under `cnormG`. -/
theorem cdegG_cnormG (p : CPolyG α) : cdegG (cnormG p) = cdegG p := by
  simp only [cdegG, cnormG_idem]

/-- **One `cdivmodG` step strictly shortens the normalized list** (the termination measure): the
remainder-loop replacement `cnormG (p − (lcP/lcQ)·xᵏ·q)` has strictly smaller normalized length than
`p`. -/
theorem stepG_length_lt (p q : CPolyG α) (hp : cnormG p ≠ []) (hq : cnormG q ≠ [])
    (hpq : (cnormG q : List α).length ≤ (cnormG p : List α).length) :
    (cnormG (csubG (cnormG p)
        (cmulG (cshiftG ((cnormG p : List α).length - (cnormG q : List α).length)
          [CField.div (cleadG p) (cleadG q)])
          (cnormG q))) : List α).length < (cnormG p : List α).length := by
  have hP : toPolyG p ≠ 0 := fun h => hp ((cnormG_eq_nil_iff p).mpr h)
  have hQ : toPolyG q ≠ 0 := fun h => hq ((cnormG_eq_nil_iff q).mpr h)
  have hk : (cnormG p : List α).length - (cnormG q : List α).length
      = (toPolyG p).natDegree - (toPolyG q).natDegree := by
    rw [length_cnormG_of_ne p hp, length_cnormG_of_ne q hq]; omega
  have hc : CFieldSpec.toK (CField.div (cleadG p) (cleadG q))
      = (toPolyG p).leadingCoeff / (toPolyG q).leadingCoeff := by
    rw [CFieldSpec.toK_div, toK_cleadG_eq_leadingCoeff, toK_cleadG_eq_leadingCoeff]
  set step := csubG (cnormG p)
    (cmulG (cshiftG ((cnormG p : List α).length - (cnormG q : List α).length)
      [CField.div (cleadG p) (cleadG q)]) (cnormG q))
    with hstepdef
  have hstep : toPolyG step
      = toPolyG p - C ((toPolyG p).leadingCoeff / (toPolyG q).leadingCoeff)
          * X ^ ((toPolyG p).natDegree - (toPolyG q).natDegree) * toPolyG q := by
    rw [hstepdef, toPolyG_csubG, toPolyG_cnormG, toPolyG_cmulG, toPolyG_cshiftG, toPolyG_cnormG, hk]
    simp only [toPolyG_cons, toPolyG_nil, mul_zero, add_zero, hc]
    ring
  have hpq' : (toPolyG q).natDegree ≤ (toPolyG p).natDegree := by
    have e1 := length_cnormG_of_ne p hp
    have e2 := length_cnormG_of_ne q hq
    omega
  have hdeg : (toPolyG step).degree < (toPolyG p).degree := by
    rw [hstep]; exact degreeG_reduce_step_lt hP hQ hpq'
  by_cases hs0 : toPolyG step = 0
  · rw [(cnormG_eq_nil_iff _).mpr hs0, List.length_nil]
    exact List.length_pos_iff.mpr hp
  · have hne : cnormG step ≠ [] := fun h => hs0 ((cnormG_eq_nil_iff _).mp h)
    have hlt := Polynomial.natDegree_lt_natDegree hs0 hdeg
    rw [length_cnormG_of_ne _ hne, length_cnormG_of_ne p hp]
    omega

/-- **Generic remainder degree bound**: with enough fuel and a nonzero divisor, `cmodG fuel p q` has
strictly smaller normalized length than `q` — the Euclidean remainder is properly reduced. -/
theorem cmodG_length_lt (fuel : ℕ) (p q : CPolyG α) (hq : cnormG q ≠ [])
    (hfuel : (cnormG p : List α).length ≤ fuel) :
    (cnormG (cmodG fuel p q) : List α).length < (cnormG q : List α).length := by
  induction fuel generalizing p with
  | zero =>
    have hp0 : cnormG p = [] := List.length_eq_zero_iff.mp (by omega)
    have h2 : cmodG 0 p q = [] := by simp [cmodG, cdivmodG, hp0]
    rw [h2]; simpa using List.length_pos_iff.mpr hq
  | succ fuel ih =>
    have hcz : cisZeroG (cnormG q) = false := by
      rw [cisZeroG_cnormG, cisZeroG]; exact List.isEmpty_eq_false_iff.mpr hq
    by_cases hlen : (cnormG p : List α).length < (cnormG q : List α).length
    · have h2 : cmodG (fuel + 1) p q = cnormG p := by
        rw [cmodG, cdivmodG]
        simp only [hcz, Bool.false_eq_true, if_false, if_pos hlen]
      rw [h2, cnormG_idem]; exact hlen
    · have hp : cnormG p ≠ [] := by
        rintro h
        rw [h, List.length_nil] at hlen
        exact hlen (List.length_pos_iff.mpr hq)
      have hstep := stepG_length_lt p q hp hq (by omega)
      have key : cmodG (fuel + 1) p q
          = cmodG fuel (cnormG (csubG (cnormG p)
              (cmulG (cshiftG ((cnormG p : List α).length - (cnormG q : List α).length)
                [CField.div (cleadG p) (cleadG q)])
                (cnormG q)))) q := by
        rw [cmodG, cdivmodG]
        simp only [hcz, Bool.false_eq_true, if_false, if_neg hlen, cleadG_cnormG, cmodG,
          ← cdivmodG_cnormG_right]
      rw [key]
      apply ih
      rw [cnormG_idem]
      omega

/-! ### Coherence of the generic ops with the concrete `Compute.*` engine at `α = ℚ` -/

/-- `csubG` at `ℚ` is the concrete `csub`. -/
theorem csubG_eq_csub : (csubG : CPolyG ℚ → CPolyG ℚ → CPolyG ℚ) = Compute.csub := by
  funext p q
  rw [csubG, Compute.csub, cnegG_eq_cneg, congrFun (congrFun caddG_eq_cadd _) _]

/-- `cleadG` at `ℚ` is the concrete `clead`. -/
theorem cleadG_eq_clead : (cleadG : CPolyG ℚ → ℚ) = Compute.clead := by
  funext p
  rw [cleadG, Compute.clead, cnormG_eq_cnorm]
  rfl

/-- `CField.div` at `ℚ` is ordinary division. -/
theorem div_eq_div_rat (a b : ℚ) : CField.div a b = a / b := by
  rw [CField.div]; show a * b⁻¹ = a / b; rw [div_eq_mul_inv]

/-! ### Correctness of the generic extended Euclidean algorithm `cgcdExtG`

`cgcdExtG fuel a b = (g, s, t)` with the Bézout relation `s·a + t·b = g` over `K`, mirroring
`Compute.cgcdExt` (defined upstream in `GenericPolyEngine`, engine `[CField α]`-only). The two
correctness halves: `toPolyG_cgcdExtG` (Bézout, fuel-independent) and `toPolyG_cgcdExtG_dvd` (the gcd
divides both inputs, under the termination predicate `cgcdTerminatesG`). An inverse modulo `R`
(`c⁻¹ mod R`, `c` a unit mod `R`) reads off the Bézout cofactor `s/g`. -/

/-- **Bézout identity through `toPolyG`** for the generic extended Euclidean algorithm (any fuel):
with `(g, s, t) = cgcdExtG fuel a b`, `toPolyG s · toPolyG a + toPolyG t · toPolyG b = toPolyG g`. -/
theorem toPolyG_cgcdExtG (fuel : ℕ) (a b : CPolyG α) :
    toPolyG (cgcdExtG fuel a b).2.1 * toPolyG a + toPolyG (cgcdExtG fuel a b).2.2 * toPolyG b
      = toPolyG (cgcdExtG fuel a b).1 := by
  induction fuel generalizing a b with
  | zero => simp [cgcdExtG, toPolyG_cnormG, toPolyG_cons, CFieldSpec.toK_one]
  | succ fuel ih =>
    rw [cgcdExtG]
    cases hb : cisZeroG b with
    | true => simp [toPolyG_cnormG, toPolyG_cons, CFieldSpec.toK_one]
    | false =>
      simp only [Bool.false_eq_true, if_false]
      rcases hqr : cdivmodG (fuel + 1) a b with ⟨q, r⟩
      rcases hg : cgcdExtG fuel b (cmodG (fuel + 1) a b) with ⟨g, s, t⟩
      have hrmod : cmodG (fuel + 1) a b = r := by rw [cmodG, hqr]
      have hdiv : toPolyG a = toPolyG q * toPolyG b + toPolyG (cmodG (fuel + 1) a b) := by
        have h := toPolyG_cdivmodG' (fuel + 1) a b
          (by intro hc; rw [cisZeroG, hc] at hb; simp at hb)
        rw [hqr] at h; rw [hrmod]; exact h
      have hih := ih b (cmodG (fuel + 1) a b)
      rw [hg] at hih
      simp only [denote]
      linear_combination hih + toPolyG t * hdiv

/-- **`cgcdExtG`'s gcd is greatest among common divisors**: any `d` dividing both `toPolyG a` and
`toPolyG b` divides `toPolyG (cgcdExtG fuel a b).1` (immediate from Bézout). Fuel-independent. -/
theorem toPolyG_dvd_cgcdExtG {d : (CFieldSpec.K α)[X]} (fuel : ℕ) (a b : CPolyG α)
    (ha : d ∣ toPolyG a) (hb : d ∣ toPolyG b) :
    d ∣ toPolyG (cgcdExtG fuel a b).1 := by
  rw [← toPolyG_cgcdExtG fuel a b]
  exact dvd_add (ha.mul_left _) (hb.mul_left _)

/-- **Termination predicate** for `cgcdExtG`: the remainder sequence reaches `0` within `fuel`. -/
def cgcdTerminatesG : ℕ → CPolyG α → CPolyG α → Prop
  | 0, _, b => cisZeroG b = true
  | fuel + 1, a, b => cisZeroG b = true ∨ cgcdTerminatesG fuel b (cmodG (fuel + 1) a b)

/-- **`cgcdExtG`'s gcd divides both inputs** when the algorithm terminates: under `cgcdTerminatesG`,
`toPolyG (cgcdExtG fuel a b).1` divides `toPolyG a` and `toPolyG b`. With `toPolyG_dvd_cgcdExtG`
(greatest) and Bézout this characterizes `g` as an honest gcd of `a, b` in `K[X]`. -/
theorem toPolyG_cgcdExtG_dvd : ∀ (fuel : ℕ) (a b : CPolyG α), cgcdTerminatesG fuel a b →
    toPolyG (cgcdExtG fuel a b).1 ∣ toPolyG a ∧ toPolyG (cgcdExtG fuel a b).1 ∣ toPolyG b := by
  intro fuel
  induction fuel with
  | zero =>
    intro a b hterm
    simp only [cgcdTerminatesG] at hterm
    rw [cgcdExtG]
    have hb0 : toPolyG b = 0 := (cisZeroG_iff b).mp hterm
    exact ⟨by simp [toPolyG_cnormG], by simp [hb0]⟩
  | succ fuel ih =>
    intro a b hterm
    rw [cgcdExtG]
    cases hb : cisZeroG b with
    | true =>
      have hb0 : toPolyG b = 0 := (cisZeroG_iff b).mp hb
      exact ⟨by simp [toPolyG_cnormG], by simp [hb0]⟩
    | false =>
      simp only [Bool.false_eq_true, if_false]
      rcases hqr : cdivmodG (fuel + 1) a b with ⟨q, r⟩
      rcases hg : cgcdExtG fuel b (cmodG (fuel + 1) a b) with ⟨g, s, t⟩
      have hterm' : cgcdTerminatesG fuel b (cmodG (fuel + 1) a b) := by
        rw [cgcdTerminatesG] at hterm
        rcases hterm with h | h
        · rw [hb] at h; simp at h
        · exact h
      obtain ⟨hgb, hgr⟩ := ih b (cmodG (fuel + 1) a b) hterm'
      rw [hg] at hgb hgr
      have hrmod : cmodG (fuel + 1) a b = r := by rw [cmodG, hqr]
      have hdiv : toPolyG a = toPolyG q * toPolyG b + toPolyG (cmodG (fuel + 1) a b) := by
        have h := toPolyG_cdivmodG' (fuel + 1) a b
          (by intro hc; rw [cisZeroG, hc] at hb; simp at hb)
        rw [hqr] at h; rw [hrmod]; exact h
      refine ⟨?_, hgb⟩
      rw [hdiv]
      exact dvd_add (hgb.mul_left _) hgr

/-- `nsmulG` at `ℚ` is multiplication by the natural-number cast: `nsmulG k a = (k : ℚ) * a`. -/
theorem nsmulG_eq_natCast_mul (k : ℕ) (a : ℚ) : (nsmulG k a : ℚ) = (k : ℚ) * a := by
  induction k with
  | zero => show (CField.zero : ℚ) = _; rw [show (CField.zero : ℚ) = 0 from rfl]; simp
  | succ n ih => rw [nsmulG]; show a + nsmulG n a = _; rw [ih]; push_cast; ring

/-- `cderivG` at `ℚ` is the concrete `cderiv`. -/
theorem cderivG_eq_cderiv : (cderivG : CPolyG ℚ → CPolyG ℚ) = Compute.cderiv := by
  have hgo : ∀ (k : ℕ) (as : CPolyG ℚ), cderivG.go k as = Compute.cderiv.go k as := by
    intro k as
    induction as generalizing k with
    | nil => rfl
    | cons b bs ih =>
      show nsmulG k b :: cderivG.go (k + 1) bs = ((k : ℚ) * b) :: Compute.cderiv.go (k + 1) bs
      rw [ih, nsmulG_eq_natCast_mul]
  funext p
  cases p with
  | nil => rfl
  | cons a as => show cderivG.go 1 as = Compute.cderiv.go 1 as; rw [hgo]

end CPolyG

open CPolyG in
/-- **Monic-normalization is a unit-scaling**: over a field, `cmonicG p` differs from `p` (read by
`toPolyG`) by the unit `C ((cleadG)⁻¹)`, so they are associates in `K[X]`. -/
theorem associated_toPolyG_cmonicG {α : Type*} [CField α] [CFieldSpec α] (p : CPolyG α) :
    Associated (toPolyG (CPolyG.cmonicG p)) (toPolyG p) := by
  rw [CPolyG.cmonicG]
  split_ifs with h
  · rw [toPolyG_nil]
    have hz : toPolyG p = 0 := (cisZeroG_iff p).mp (by rwa [cisZeroG_cnormG] at h)
    rw [hz]
  · rw [toPolyG_cscaleG, toPolyG_cnormG]
    have hne : cnormG (cnormG p) ≠ [] := by
      rw [cnormG_idem]; intro he
      exact h (by rw [cisZeroG_cnormG, cisZeroG_iff, ← toPolyG_cnormG, he, toPolyG_nil])
    exact associated_unit_mul_left _ _
      (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr
        (by rw [CFieldSpec.toK_inv]; exact inv_ne_zero (toK_cleadG_ne_zero hne))))

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

end DeepWiki.SymbolicIntegration
