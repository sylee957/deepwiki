import DeepWiki.SymbolicIntegration.ComputableField

/-! # Generic division / gcd / derivative over a `CField`, and the `CField QFunNZ` instance
Stage B of the generic polynomial engine. Two layers sit on top of the `CField`/`CPolyG` keystone of
`ComputableField`:

* **`CField QFunNZ`** — the denominator-nonzero rational functions ℚ(x) as a *second* `CField`
  instance (over `K = RatFunc ℚ`, `toK = toQFunNZ`). It is the first non-trivial witness that the
  dropped-`toK`-injectivity design works: `isZero` is the numerator zero test (not a `K`-equality on
  a normal form), and every homomorphism law is discharged from the `toQFunNZ_*`/`toQFun_*` lemmas
  with the denominator-≠-0 side conditions cleared by subtype membership.

* **Generic `cdivmodG`/`cgcdExtG`/`cderivG`** — the `Compute.*` Euclidean division, extended
  Euclidean algorithm, and formal derivative, mirrored over an arbitrary `[CField α]` (ℚ-operations
  replaced by `CField.add`/`mul`/`neg`/`inv`/`isZero`, `toPoly` by `toPolyG`). Their correctness
  (`toPolyG_cdivmodG` Euclidean identity, `toPolyG_cgcdExtG` Bézout, `cgcdTerminatesG` +
  `toPolyG_cgcdExtG_dvd`, `toPolyG_cderivG`) is proven on all inputs over any `CField`. Coherence
  lemmas (`cdivmodG (α := ℚ) = cdivmod`, …) specialize back to the concrete engine so Stage C can
  migrate. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-! ### The `CField QFunNZ` instance (ℚ(x) as a computable field)

The denominator-nonzero subtype `QFunNZ` (`ComputableField`) already carries `qaddNZ`/`qmulNZ`/
`qnegNZ` and their `toQFunNZ_*` homomorphism lemmas. To build the `CField` instance we add `qoneNZ`,
`qzeroNZ`, `qinvNZ` (inverse: swap num/den when the numerator is nonzero, else `qzeroNZ`), and
`qsubNZ`, and read `isZero` off the **numerator** (`cisZero ∘ num`). This validates the design point
that `toK` need not be injective: `isZero` is a syntactic numerator test, certified against
`toQFunNZ x = 0` by `cisZero_iff_toPoly_eq_zero` together with the den-≠-0 membership. -/

namespace QFunNZ

/-- `qoneNZ`: the rational function `1 = 1/1` as a `QFunNZ` (denominator `[1]`, nonzero). -/
def qoneNZ : QFunNZ := ⟨Compute.qone, by simp [Compute.qone, Compute.toPoly_cons, Compute.toPoly_nil]⟩

/-- `qzeroNZ`: the rational function `0 = 0/1` as a `QFunNZ` (denominator `[1]`, nonzero). -/
def qzeroNZ : QFunNZ := ⟨Compute.qzero, by simp [Compute.qzero, Compute.toPoly_cons, Compute.toPoly_nil]⟩

/-- `qinvNZ`: inverse on `QFunNZ`. If the numerator is zero, the result is `qzeroNZ` (the `0⁻¹ = 0`
field convention); otherwise swap numerator and denominator (the new denominator is the old numerator,
nonzero by `¬ cisZero`). -/
def qinvNZ (x : QFunNZ) : QFunNZ :=
  if h : Compute.cisZero x.1.1 then qzeroNZ
  else ⟨(x.1.2, x.1.1), by
    show Compute.toPoly x.1.1 ≠ 0
    exact fun hz => h ((Compute.cisZero_iff_toPoly_eq_zero x.1.1).mpr hz)⟩

/-- `qsubNZ`: subtraction on `QFunNZ`, `x − y := x + (−y)`. -/
def qsubNZ (x y : QFunNZ) : QFunNZ := qaddNZ x (qnegNZ y)

/-- `isZeroNZ`: the zero test on `QFunNZ`, reading `cisZero` off the **numerator** (the denominator is
nonzero by membership, so `x = 0` iff its numerator vanishes). -/
def isZeroNZ (x : QFunNZ) : Bool := Compute.cisZero x.1.1

/-- **`toQFunNZ` reads `qoneNZ` as `1`**. -/
theorem toQFunNZ_qoneNZ : toQFunNZ qoneNZ = 1 := Compute.toQFun_qone

/-- **`toQFunNZ` reads `qzeroNZ` as `0`**. -/
theorem toQFunNZ_qzeroNZ : toQFunNZ qzeroNZ = 0 := Compute.toQFun_qzero

/-- **`qinvNZ` realizes `⁻¹`** on `QFunNZ`: `toQFunNZ (qinvNZ x) = (toQFunNZ x)⁻¹` (the `0⁻¹ = 0`
convention matches `RatFunc`). -/
theorem toQFunNZ_qinvNZ (x : QFunNZ) : toQFunNZ (qinvNZ x) = (toQFunNZ x)⁻¹ := by
  rw [qinvNZ]
  by_cases h : Compute.cisZero x.1.1
  · rw [dif_pos h, toQFunNZ_qzeroNZ]
    have hx0 : Compute.toPoly x.1.1 = 0 := (Compute.cisZero_iff_toPoly_eq_zero x.1.1).mp h
    rw [show toQFunNZ x = 0 from by
      rw [toQFunNZ, Compute.toQFun, hx0, map_zero, zero_div], inv_zero]
  · rw [dif_neg h]
    show Compute.toQFun (x.1.2, x.1.1) = (Compute.toQFun x.1)⁻¹
    obtain ⟨⟨a, b⟩, _⟩ := x
    rw [Compute.toQFun, Compute.toQFun, inv_div]

/-- **`qsubNZ` realizes `-`** on `QFunNZ`: `toQFunNZ (qsubNZ x y) = toQFunNZ x - toQFunNZ y`. -/
theorem toQFunNZ_qsubNZ (x y : QFunNZ) : toQFunNZ (qsubNZ x y) = toQFunNZ x - toQFunNZ y := by
  rw [qsubNZ, toQFunNZ_qaddNZ, toQFunNZ_qnegNZ, sub_eq_add_neg]

/-- **`isZeroNZ` is certified against `toQFunNZ = 0`**: `isZeroNZ x = true ↔ toQFunNZ x = 0` — the
numerator zero test agrees with vanishing in `RatFunc ℚ` (denominator nonzero by membership). -/
theorem isZeroNZ_iff (x : QFunNZ) : isZeroNZ x = true ↔ toQFunNZ x = 0 := by
  rw [isZeroNZ, Compute.cisZero_iff_toPoly_eq_zero]
  obtain ⟨⟨a, b⟩, hb⟩ := x
  rw [toQFunNZ, Compute.toQFun]
  have hbm : algebraMap ℚ[X] (RatFunc ℚ) (Compute.toPoly b) ≠ 0 := Compute.am_toPoly_ne_zero hb
  constructor
  · intro h; rw [h, map_zero, zero_div]
  · intro h
    rw [div_eq_zero_iff] at h
    rcases h with h | h
    · exact (map_eq_zero_iff _ (RatFunc.algebraMap_injective ℚ)).mp h
    · exact absurd h hbm

end QFunNZ

/-- **`CField QFunNZ`**: the denominator-nonzero rational functions ℚ(x) as a computable field over
`K = RatFunc ℚ` with `toK = toQFunNZ`. The first non-trivial `CField` instance — its `isZero` is the
numerator zero test (no `toK`-injectivity / lowest-terms normal form needed), validating the dropped-
injectivity design of `CField`. -/
noncomputable instance instCFieldQFunNZ : CField QFunNZ where
  zero := QFunNZ.qzeroNZ
  one := QFunNZ.qoneNZ
  add := QFunNZ.qaddNZ
  mul := QFunNZ.qmulNZ
  neg := QFunNZ.qnegNZ
  inv := QFunNZ.qinvNZ
  isZero := QFunNZ.isZeroNZ
  K := RatFunc ℚ
  toK := QFunNZ.toQFunNZ
  toK_zero := QFunNZ.toQFunNZ_qzeroNZ
  toK_one := QFunNZ.toQFunNZ_qoneNZ
  toK_add := QFunNZ.toQFunNZ_qaddNZ
  toK_mul := QFunNZ.toQFunNZ_qmulNZ
  toK_neg := QFunNZ.toQFunNZ_qnegNZ
  toK_inv := QFunNZ.toQFunNZ_qinvNZ
  isZero_iff := QFunNZ.isZeroNZ_iff

/-! ### Generic formal derivative `cderivG` over a `CField`

`cderivG [a₀, a₁, a₂, …] = [1·a₁, 2·a₂, 3·a₃, …]`: drop the constant coefficient and scale the `k`-th
remaining coefficient by `k`. The natural-number scaling `k · a` is built from `CField.add` by the
helper `nsmulG`, whose `toK` is the field `k • _ = (k : K) * _`. The correctness `toPolyG_cderivG`
realizes `Polynomial.derivative` exactly, mirroring the concrete `toPoly_cderiv`. -/

namespace CPolyG

variable {α : Type*} [CField α]

/-- **Generic `ℕ`-scaling** `nsmulG k a` = `a + a + … + a` (`k` times), built from `CField.add`. The
coefficient-degree multiplier for the formal derivative; `toK` reads it as `k • _ = (k : K) * _`. -/
def nsmulG : ℕ → α → α
  | 0, _ => CField.zero
  | k + 1, a => CField.add a (nsmulG k a)

/-- `toK (nsmulG k a) = k • toK a` in `K`. -/
theorem toK_nsmulG (k : ℕ) (a : α) : CField.toK (nsmulG k a) = k • CField.toK a := by
  induction k with
  | zero => rw [nsmulG, CField.toK_zero, zero_smul]
  | succ n ih => rw [nsmulG, CField.toK_add, ih, succ_nsmul']

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
theorem toPolyG_cderivG (p : CPolyG α) :
    toPolyG (cderivG p) = Polynomial.derivative (toPolyG p) := by
  suffices h : ∀ (as : CPolyG α) (k : ℕ),
      toPolyG (cderivG.go k as)
        = (k : (CField.K α)[X]) * toPolyG as + X * Polynomial.derivative (toPolyG as) by
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
    have hk : Polynomial.C (CField.toK (nsmulG k b)) = (k : (CField.K α)[X]) * Polynomial.C (CField.toK b) := by
      rw [toK_nsmulG, nsmul_eq_mul, map_mul, map_natCast]
    rw [hk]; push_cast; ring

/-! ### Generic Euclidean division `cdivmodG` over a `CField`

`cdivmodG fuel p q = (quotient, remainder)` by fuel-bounded long division over the field `K`, with
`toPolyG p = toPolyG q · toPolyG (cdivG…) + toPolyG (cmodG…)` and a strict normalized-length / degree
drop. Mirrors `Compute.cdivmod`; the leading-term match `c = clead p / clead q` is `CField.div`. -/

/-- **Generic Euclidean division** of `CPolyG`s, fuel-bounded: `cdivmodG fuel p q = (quotient,
remainder)` with `p = quotient · q + remainder` over the field `K` (`q ≠ 0`; one step per degree drop). -/
def cdivmodG : ℕ → CPolyG α → CPolyG α → CPolyG α × CPolyG α
  | 0, p, _ => ([], cnormG p)
  | fuel + 1, p, q =>
    let p := cnormG p
    let q := cnormG q
    if cisZeroG q then ([], [])
    else if (p : List α).length < (q : List α).length then ([], p)
    else
      let c := CField.div (cleadG p) (cleadG q)
      let k := (p : List α).length - (q : List α).length
      let term := cshiftG k [c]
      let p' := cnormG (csubG p (cmulG term q))
      let (quo, rem) := cdivmodG fuel p' q
      (caddG term quo, rem)

/-- **Quotient** of generic Euclidean division (`cdivmodG`'s first component). -/
def cdivG (fuel : ℕ) (p q : CPolyG α) : CPolyG α := (cdivmodG fuel p q).1

/-- **Remainder** of generic Euclidean division (`cdivmodG`'s second component). -/
def cmodG (fuel : ℕ) (p q : CPolyG α) : CPolyG α := (cdivmodG fuel p q).2

/-- **Generic divisibility test** `cdvdG fuel q p`: `true` iff `q ∣ p` (remainder of `p` by `q` is
zero). -/
def cdvdG (fuel : ℕ) (q p : CPolyG α) : Bool := cisZeroG (cmodG fuel p q)

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
      simp only [toPolyG_caddG, toPolyG_cnormG, toPolyG_csubG, toPolyG_cmulG] at hih ⊢
      linear_combination hih

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
`(CField.K α)[X]` (`degreeG_reduce_step_lt`), proven exactly as the concrete `degree_reduce_step_lt`. -/

/-- For a nonzero generic polynomial, the normalized list length is `natDegree + 1`. -/
theorem length_cnormG_of_ne (p : CPolyG α) (h : cnormG p ≠ []) :
    (cnormG p : List α).length = (toPolyG p).natDegree + 1 := by
  have hd := cdegG_eq_natDegree p
  rw [cdegG] at hd
  have hlen : 1 ≤ (cnormG p : List α).length := List.length_pos_iff.mpr h
  omega

/-- **One Euclidean-division step strictly drops the degree** in `(CField.K α)[X]`: subtracting the
leading-term-matching multiple `C (lcP/lcQ)·X^(degP−degQ)·Q` cancels the top coefficient. -/
theorem degreeG_reduce_step_lt {P Q : (CField.K α)[X]} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree ≤ P.natDegree) :
    (P - C (P.leadingCoeff / Q.leadingCoeff)
        * X ^ (P.natDegree - Q.natDegree) * Q).degree < P.degree := by
  have hQlc : Q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ
  have hPlc : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  have hc0 : P.leadingCoeff / Q.leadingCoeff ≠ 0 := div_ne_zero hPlc hQlc
  have hCc : (C (P.leadingCoeff / Q.leadingCoeff)) ≠ 0 := by rwa [Ne, Polynomial.C_eq_zero]
  have hXk : (X ^ (P.natDegree - Q.natDegree) : (CField.K α)[X]) ≠ 0 :=
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

/-- `cleadG` is invariant under `cnormG`: `cleadG (cnormG p) = cleadG p`. -/
theorem cleadG_cnormG (p : CPolyG α) : cleadG (cnormG p) = cleadG p := by
  simp only [cleadG, cnormG_idem]

/-- `cisZeroG` is invariant under `cnormG`. -/
theorem cisZeroG_cnormG (q : CPolyG α) : cisZeroG (cnormG q) = cisZeroG q := by
  simp only [cisZeroG, cnormG_idem]

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
  have hc : CField.toK (CField.div (cleadG p) (cleadG q))
      = (toPolyG p).leadingCoeff / (toPolyG q).leadingCoeff := by
    rw [CField.toK_div, toK_cleadG_eq_leadingCoeff, toK_cleadG_eq_leadingCoeff]
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

/-- `cdivmodG` at `ℚ` is the concrete `cdivmod`. -/
theorem cdivmodG_eq_cdivmod (fuel : ℕ) :
    (cdivmodG fuel : CPolyG ℚ → CPolyG ℚ → CPolyG ℚ × CPolyG ℚ) = Compute.cdivmod fuel := by
  induction fuel with
  | zero =>
    funext p q
    show (([], cnormG p) : CPolyG ℚ × CPolyG ℚ) = ([], Compute.cnorm p)
    have : (cnormG p : CPolyG ℚ) = Compute.cnorm p := congrFun cnormG_eq_cnorm p
    rw [this]
    rfl
  | succ fuel ih =>
    funext p q
    show (let p := cnormG p; let q := cnormG q;
        if cisZeroG q then ([], [])
        else if (p : List ℚ).length < (q : List ℚ).length then ([], p)
        else
          let c := CField.div (cleadG p) (cleadG q)
          let k := (p : List ℚ).length - (q : List ℚ).length
          let term := cshiftG k [c]
          let p' := cnormG (csubG p (cmulG term q))
          let (quo, rem) := cdivmodG fuel p' q
          (caddG term quo, rem)) = _
    rw [Compute.cdivmod]
    simp only [cnormG_eq_cnorm, cisZeroG_eq_cisZero, cleadG_eq_clead, div_eq_div_rat,
      cshiftG_eq_cshift, cmulG_eq_cmul, csubG_eq_csub, congrFun (congrFun caddG_eq_cadd _) _, ih]

/-- `cdivG` at `ℚ` is the concrete `cdiv`. -/
theorem cdivG_eq_cdiv (fuel : ℕ) :
    (cdivG fuel : CPolyG ℚ → CPolyG ℚ → CPolyG ℚ) = Compute.cdiv fuel := by
  funext p q; rw [cdivG, Compute.cdiv, cdivmodG_eq_cdivmod]

/-- `cmodG` at `ℚ` is the concrete `cmod`. -/
theorem cmodG_eq_cmod (fuel : ℕ) :
    (cmodG fuel : CPolyG ℚ → CPolyG ℚ → CPolyG ℚ) = Compute.cmod fuel := by
  funext p q; rw [cmodG, Compute.cmod, cdivmodG_eq_cdivmod]



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

end DeepWiki.SymbolicIntegration
