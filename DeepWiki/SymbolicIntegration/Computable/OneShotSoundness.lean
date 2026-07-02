import DeepWiki.SymbolicIntegration.Computable.IntegrateTowerCorrectG
import DeepWiki.SymbolicIntegration.Computable.Tower.RischDEWellFounded

/-! # Checker-free soundness of the integrator's polynomial branch

Abstract correctness of the `b = 0` primitive-integration arm and the §6.6 cancellation cases of the
poly-Risch-DE dispatcher: the antiderivative `cIntegratePolyG` differentiates back to its integrand,
the output passes `checkIdentityG` provably (never executed), and the field-level identity
`D(∫fₚ) = fₚ` follows through `field_identity_of_checkIdentityG`. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]

omit [CDiffField α] [CDiffFieldSpec α] in
/-- `toK (cnatCastG k) = (k : K)`: the engine's `ℕ`-cast reads as the natural cast in
`K = CFieldSpec.K α`. -/
theorem toK_cnatCastG_oneShot (k : ℕ) :
    CFieldSpec.toK (CPolyG.cnatCastG k : α) = (k : CFieldSpec.K α) := by
  induction k with
  | zero => rw [CPolyG.cnatCastG, CFieldSpec.toK_zero, Nat.cast_zero]
  | succ n ih => rw [CPolyG.cnatCastG, CFieldSpec.toK_add, CFieldSpec.toK_one, ih, Nat.cast_succ,
      add_comm]

omit [CDiffField α] [CDiffFieldSpec α] in
/-- Shifted antiderivative-tail derivative law: for the index-`k`-started integration tail
`L_k = (c.zipIdx k).map (fun (a,i) => a/(i+1))`, `D(X^{k+1} · toPolyG L_k) = X^k · toPolyG c`. -/
theorem derivative_Xpow_mul_toPolyG_integrateTail [CharZero (CFieldSpec.K α)] (c : CPolyG α) :
    ∀ k : ℕ, Polynomial.derivative
        (X ^ (k + 1) *
          toPolyG ((c.zipIdx k).map (fun ai => CField.div ai.1 (cnatCastG (ai.2 + 1)))))
      = X ^ k * toPolyG c := by
  induction c with
  | nil => intro k; simp
  | cons a as ih =>
    intro k
    -- `(a :: as).zipIdx k = (a, k) :: as.zipIdx (k+1)`; map and read `toPolyG`
    simp only [List.zipIdx_cons, List.map_cons, toPolyG_cons]
    -- `X^{k+1} · (C(toK (a/(k+1))) + X · toPolyG(tail)) = C(..)·X^{k+1} + X^{k+2}·toPolyG(tail)`
    rw [mul_add, derivative_add]
    -- the head term: `D(C(toK (a/(k+1)))·X^{k+1}) = (k+1)·C(toK (a/(k+1)))·X^k`
    have hhead : Polynomial.derivative
        (X ^ (k + 1) * Polynomial.C (CFieldSpec.toK (CField.div a (cnatCastG (k + 1)))))
        = Polynomial.C (CFieldSpec.toK a) * X ^ k := by
      rw [mul_comm, derivative_C_mul, derivative_X_pow, add_tsub_cancel_right, ← mul_assoc, ← C_mul]
      congr 1
      -- `(toK (a/(k+1))) · (k+1 : K) = toK a`, since `toK (cnatCast (k+1)) = (k+1 : K)`
      rw [CFieldSpec.toK_div, toK_cnatCastG_oneShot]
      have hk1 : ((k : CFieldSpec.K α) + 1) ≠ 0 := by
        have : ((k : CFieldSpec.K α) + 1) = ((k + 1 : ℕ) : CFieldSpec.K α) := by push_cast; ring
        rw [this, Nat.cast_ne_zero]; omega
      push_cast
      field_simp
    -- the tail term: regroup `X^{k+1}·(X·toPolyG tail) = X^{(k+1)+1}·toPolyG tail`, apply IH at `k+1`
    have htail : Polynomial.derivative
        (X ^ (k + 1) * (X * toPolyG
          ((as.zipIdx (k + 1)).map (fun ai => CField.div ai.1 (cnatCastG (ai.2 + 1))))))
        = X ^ (k + 1) * toPolyG as := by
      have hrw : X ^ (k + 1) * (X * toPolyG
            ((as.zipIdx (k + 1)).map (fun ai => CField.div ai.1 (cnatCastG (ai.2 + 1)))))
          = X ^ ((k + 1) + 1) * toPolyG
            ((as.zipIdx (k + 1)).map (fun ai => CField.div ai.1 (cnatCastG (ai.2 + 1)))) := by
        rw [pow_succ]; ring
      rw [hrw, ih (k + 1)]
    rw [hhead, htail, mul_add]
    ring

/-! ### The `cIntegratePolyG` formal-derivative correctness

`cIntegratePolyG c = 0 :: (c.zipIdx.map (fun (a,i) => a/(i+1)))` is the engine's term-by-term
antiderivative `∫ Σ cᵢtⁱ = Σ (cᵢ/(i+1)) t^{i+1}`; its formal derivative inverts it exactly.
Needs only characteristic zero (to divide by `i+1`). -/

omit [CDiffField α] [CDiffFieldSpec α] in
/-- `D(toPolyG (cIntegratePolyG c)) = toPolyG c` over `(CFieldSpec.K α)[X]`,
`D = Polynomial.derivative`: the term-by-term antiderivative differentiates back to its integrand. -/
theorem derivative_toPolyG_cIntegratePolyG [CharZero (CFieldSpec.K α)] (c : CPolyG α) :
    Polynomial.derivative (toPolyG (CPolyG.cIntegratePolyG c)) = toPolyG c := by
  have h := derivative_Xpow_mul_toPolyG_integrateTail c 0
  simpa only [CPolyG.cIntegratePolyG, toPolyG_cons, CFieldSpec.toK_zero, map_zero, zero_add,
    pow_zero, pow_one, one_mul, List.zipIdx] using h

/-! ### The `cmonomialDeriv [1]` (monomial-derivation) form over a constant base

For the primitive monomial `Dt = [CField.one]`, `implicitDeriv 1 = mapCoeffs + derivative`, so the
antiderivative differentiates back exactly when the coefficient-derivation term `mapCoeffs` vanishes;
that constant-base regime is carried as the explicit hypothesis `hconst`. -/

/-- `cIntegratePolyG` differentiates back under the primitive monomial derivation (`Dt = 1`): if
`mapCoeffs (toPolyG (cIntegratePolyG c)) = 0` (constant base), then
`toPolyG (cmonomialDeriv [CField.one] (cIntegratePolyG c)) = toPolyG c` over `(CFieldSpec.K α)[X]`. -/
theorem toPolyG_cmonomialDeriv_cIntegratePolyG_const [CharZero (CFieldSpec.K α)] (c : CPolyG α)
    (hconst : Differential.mapCoeffs (toPolyG (CPolyG.cIntegratePolyG c)) = 0) :
    toPolyG (CPolyG.cmonomialDeriv ([CField.one] : CPolyG α) (CPolyG.cIntegratePolyG c))
      = toPolyG c := by
  rw [toPolyG_cmonomialDeriv]
  -- `toPolyG [CField.one] = 1`, so `implicitDeriv 1 = mapCoeffs + derivative`
  have hDt : toPolyG ([CField.one] : CPolyG α) = 1 := by
    rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_one, map_one, mul_zero, add_zero]
  rw [hDt, Differential.implicitDeriv, Derivation.add_apply, hconst, zero_add]
  -- the `v • derivative'` part is `1 • derivative = derivative`
  rw [Derivation.smul_apply, one_smul, Derivation.restrictScalars_apply]
  exact derivative_toPolyG_cIntegratePolyG c

/-! ### The field identity `D(∫ fₚ) = fₚ` for the polynomial part -/

/-- Field-level polynomial-part identity: over a constant base (`hconst`), the tower fraction-field
derivation sends the antiderivative to the integrand,
`towerFractionFieldDerivG [CField.one] (amG (toPolyG (cIntegratePolyG c))) = amG (toPolyG c)` over
`RatFunc (CFieldSpec.K α)`. -/
theorem towerFractionFieldDerivG_amG_cIntegratePolyG_const [CharZero (CFieldSpec.K α)]
    [Algebra ℚ (CFieldSpec.K α)] (c : CPolyG α)
    (hconst : Differential.mapCoeffs (toPolyG (CPolyG.cIntegratePolyG c)) = 0) :
    towerFractionFieldDerivG ([CField.one] : CPolyG α)
        (amG α (toPolyG (CPolyG.cIntegratePolyG c)))
      = amG α (toPolyG c) := by
  -- the tower field derivation on a polynomial image is the image of the monomial derivation
  rw [towerFractionFieldDerivG, extendDeriv_algebraMap, ← toPolyG_cmonomialDeriv]
  -- which the abstract atom identifies with `toPolyG c`
  rw [toPolyG_cmonomialDeriv_cIntegratePolyG_const c hconst]

/-! ### The polynomial-branch output passes `checkIdentityG` abstractly -/

/-- `toPolyG (cmonomialDeriv [CField.one] [CField.one]) = 0`: the primitive monomial derivation
annihilates the constant `1`. -/
theorem toPolyG_cmonomialDeriv_one : toPolyG
    (CPolyG.cmonomialDeriv ([CField.one] : CPolyG α) ([CField.one] : CPolyG α)) = 0 := by
  rw [toPolyG_cmonomialDeriv]
  have hone : toPolyG ([CField.one] : CPolyG α) = 1 := by
    rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_one, map_one, mul_zero, add_zero]
  rw [hone]
  exact Derivation.map_one_eq_zero _

/-- Over a constant base (`hconst`), the pure-polynomial result
`⟨(cIntegratePolyG c, [CField.one]), []⟩` satisfies
`checkIdentityG [CField.one] · c [CField.one] = true`, proven abstractly with no runtime check
executed: the `b = 0` integration branch always passes its own check. -/
theorem checkIdentityG_cIntegratePolyG_const [CharZero (CFieldSpec.K α)] (c : CPolyG α)
    (hconst : Differential.mapCoeffs (toPolyG (CPolyG.cIntegratePolyG c)) = 0) :
    CPolyG.checkIdentityG ([CField.one] : CPolyG α)
        ⟨(CPolyG.cIntegratePolyG c, ([CField.one] : CPolyG α)), []⟩ c ([CField.one] : CPolyG α)
      = true := by
  -- unfold the check; the empty-log fold is just the seed `([0], [1])`
  rw [CPolyG.checkIdentityG]
  simp only [List.foldl_nil]
  -- the check is `cisZeroG (csubG lhs rhs)`; clear to the polynomial identity `toPolyG lhs = toPolyG rhs`
  rw [cisZeroG_iff, toPolyG_csubG, sub_eq_zero]
  -- push `toPolyG` through everything
  have hone : toPolyG ([CField.one] : CPolyG α) = 1 := by
    rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_one, map_one, mul_zero, add_zero]
  have hzero : toPolyG ([CField.zero] : CPolyG α) = 0 := by
    rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_zero, map_zero, mul_zero, add_zero]
  simp only [toPolyG_cmulG, toPolyG_caddG, toPolyG_csubG, hone, hzero]
  -- the rational-part numerator derivative `D(q)·1 − q·D(1)`, with `D(1) = 0`
  rw [toPolyG_cmonomialDeriv_one,
    toPolyG_cmonomialDeriv_cIntegratePolyG_const c hconst]
  ring

/-! ### ★★★ THE ONE-SHOT (checker-free): compose the crux with the field bridge

Composing `checkIdentityG_cIntegratePolyG_const` (the algorithm self-discharges its check) with
`field_identity_of_checkIdentityG` (check ⟹ field identity) yields the genuine one-shot the campaign
targets: the polynomial-branch antiderivative satisfies `D(∫f) = f` **with the runtime check provably
redundant**. The `checkIdentityG = true` fact is supplied by the abstract atom — it is *never executed*.
This is exactly the `algorithm = some res → D(res) = integrand` (no checker) for the reachable
polynomial branch. -/

/-- **★★★ Checker-free one-shot `D(∫ fₚ) = fₚ` via the field bridge** (polynomial branch). Over a
constant base (`hconst`), the pure-polynomial antiderivative `g = amG(toPolyG (cIntegratePolyG c))/amG 1`
satisfies the field-level identity `towerFractionFieldDerivG [1] g + logResidueSumG [1] [] = amG(toPolyG
c)/amG 1` over `RatFunc (CFieldSpec.K α)` — obtained by feeding the *abstractly-proven*
`checkIdentityG = true` (the crux `checkIdentityG_cIntegratePolyG_const`) into the bridge
`field_identity_of_checkIdentityG`. The `checkIdentityG` guard is **never run**: the algorithm output is
proven correct. The genuine one-shot algorithm-soundness for the polynomial branch, routed through the
existing bridge to show it is redundant with the check. -/
theorem field_identity_cIntegratePolyG_const [CharZero (CFieldSpec.K α)] [Algebra ℚ (CFieldSpec.K α)]
    (c : CPolyG α) (hconst : Differential.mapCoeffs (toPolyG (CPolyG.cIntegratePolyG c)) = 0) :
    towerFractionFieldDerivG ([CField.one] : CPolyG α)
        (amG α (toPolyG (CPolyG.cIntegratePolyG c)) / amG α (toPolyG ([CField.one] : CPolyG α)))
        + logResidueSumG ([CField.one] : CPolyG α)
            (⟨(CPolyG.cIntegratePolyG c, ([CField.one] : CPolyG α)), []⟩ : IntegralResultG α).logs
      = amG α (toPolyG c) / amG α (toPolyG ([CField.one] : CPolyG α)) := by
  have hone_ne : toPolyG ([CField.one] : CPolyG α) ≠ 0 := by
    rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_one, map_one, mul_zero, add_zero]; exact one_ne_zero
  exact field_identity_of_checkIdentityG ([CField.one] : CPolyG α)
    ⟨(CPolyG.cIntegratePolyG c, ([CField.one] : CPolyG α)), []⟩ c ([CField.one] : CPolyG α)
    hone_ne hone_ne (by simp) (checkIdentityG_cIntegratePolyG_const c hconst)

/-! ### ★ Keyed on the actual algorithm function `cPolyRischDEG`

The result above is for the directly-built pure-polynomial result; here we key it on the genuine
algorithm `cPolyRischDEG [CField.one] fuel [] c n` (the `b = 0` integration branch of the Poly-Risch-DE
dispatcher), which — when the degree budget admits (`deg c + 1 ≤ n`, the branch condition) — returns
exactly `some (cIntegratePolyG c)`. So the field identity holds for whatever the algorithm emits, with no
check executed. -/

omit [CDiffFieldSpec α] in
/-- **`cPolyRischDEGWf` `b = 0` branch returns `cIntegratePolyGWf c`** (for nonzero `c` within the degree
budget). When `cisZeroG c = false` and `deg c + 1 ≤ n`, `cPolyRischDEGWf Dt [] c n = some
(cIntegratePolyGWf c)`: the pure-integration arm of the fuel-free dispatcher. Pins the algorithm's output
shape. -/
theorem cPolyRischDEGWf_nil_eq [CRischField α] (Dt : CPolyG α) (c : CPolyG α) (n : ℤ)
    (hc : CPolyG.cisZeroG c = false) (hdeg : (CPolyG.cdegG c : ℤ) + 1 ≤ n) :
    CPolyG.cPolyRischDEGWf Dt ([] : CPolyG α) c n = some (CPolyG.cIntegratePolyGWf c) := by
  have hb : CPolyG.cisZeroG ([] : CPolyG α) = true := by rw [cisZeroG_iff, toPolyG_nil]
  simp only [CPolyG.cPolyRischDEGWf, hb, if_true, hc, Bool.false_eq_true, if_false]
  rw [if_neg (by omega : ¬ (CPolyG.cdegG c : ℤ) + 1 > n)]

/-- **★★★ Checker-free one-shot keyed on `cPolyRischDEGWf`**: if the Poly-Risch-DE dispatcher's `b = 0`
integration branch returns `some q` (`cPolyRischDEGWf [CField.one] [] c n = some q`, nonzero `c`
within the degree budget, constant base), then the field-level antiderivative identity
`towerFractionFieldDerivG [1] (amG(toPolyG q)/amG 1) + … = amG(toPolyG c)/amG 1` holds — **no
`checkIdentityG` executed**. The genuine `algorithm = some res → D(res) = integrand` for the polynomial
branch: the runtime guard is provably redundant. (`q = cIntegratePolyGWf c` by `cPolyRischDEGWf_nil_eq`,
then `field_identity_cIntegratePolyG_const`.) -/
theorem field_identity_of_cPolyRischDEGWf [CharZero (CFieldSpec.K α)] [Algebra ℚ (CFieldSpec.K α)]
    [CRischField α]
    (c q : CPolyG α) (n : ℤ)
    (hc : CPolyG.cisZeroG c = false) (hdeg : (CPolyG.cdegG c : ℤ) + 1 ≤ n)
    (hsome : CPolyG.cPolyRischDEGWf ([CField.one] : CPolyG α) ([] : CPolyG α) c n = some q)
    (hconst : Differential.mapCoeffs (toPolyG q) = 0) :
    towerFractionFieldDerivG ([CField.one] : CPolyG α)
        (amG α (toPolyG q) / amG α (toPolyG ([CField.one] : CPolyG α)))
      = amG α (toPolyG c) / amG α (toPolyG ([CField.one] : CPolyG α)) := by
  -- the algorithm output is exactly `cIntegratePolyGWf c`
  have hq : q = CPolyG.cIntegratePolyGWf c := by
    rw [cPolyRischDEGWf_nil_eq ([CField.one] : CPolyG α) c n hc hdeg] at hsome
    exact (Option.some.injEq _ _ ▸ hsome).symm
  subst hq
  have hconst' : Differential.mapCoeffs (toPolyG (CPolyG.cIntegratePolyG c)) = 0 := by
    rwa [show CPolyG.cIntegratePolyGWf c = CPolyG.cIntegratePolyG c by rfl] at hconst
  -- empty logs ⇒ `logResidueSumG … [] = 0`, so the field-identity is exactly the bridge output
  have h := field_identity_cIntegratePolyG_const (α := α) c hconst'
  rw [show CPolyG.cIntegratePolyGWf c = CPolyG.cIntegratePolyG c by rfl]
  rwa [logResidueSumG_nil, add_zero] at h

/-! ### ★ Discharging the constant-base hypothesis: `mapCoeffs` is inherited from integrand to antiderivative

`field_identity_of_cPolyRischDEGWf` carries `hconst : mapCoeffs (toPolyG q) = 0` on the algorithm *output*.
That output-side hypothesis is **not** automatic, but it *is* implied by the corresponding *input*-side
fact `mapCoeffs (toPolyG c) = 0` (the integrand's coefficients being differential constants): the
antiderivative's degree-`i+1` coefficient is `cᵢ/(i+1)`, whose base derivative `(cᵢ)′/(i+1)` vanishes
exactly when `(cᵢ)′` does. So the constant-base condition transports from integrand to antiderivative
(`cIntegratePolyG_const_coeff`), letting the poly-RDE soundness be keyed on the *input* (the natural
form). The conduit is the commutation of the two polynomial derivations `mapCoeffs` and `derivative`. -/

/-- **`mapCoeffs` and `derivative` commute on `(CFieldSpec.K α)[X]`**:
`mapCoeffs (derivative r) = derivative (mapCoeffs r)`. Both are derivations; the coefficientwise check
(`coeff_mapCoeffs`, `coeff_derivative`) reduces to `(x·(n+1))′ = x′·(n+1)`, true since the nat-cast
`(n+1 : K)` is a differential constant (`map_natCast`). The conduit for transporting the constant-base
condition through the antiderivative `cIntegratePolyG`. -/
theorem mapCoeffs_derivative_commute (r : (CFieldSpec.K α)[X]) :
    Differential.mapCoeffs (Polynomial.derivative r) =
      Polynomial.derivative (Differential.mapCoeffs r) := by
  ext n
  rw [Differential.coeff_mapCoeffs, coeff_derivative, coeff_derivative,
    Differential.coeff_mapCoeffs, Derivation.leibniz]
  have hc : ((↑n + 1 : (CFieldSpec.K α)))′ = 0 := by
    rw [show ((↑n + 1 : (CFieldSpec.K α))) = ((n + 1 : ℕ) : (CFieldSpec.K α)) by push_cast; ring,
      Derivation.map_natCast]
  rw [hc, smul_zero, zero_add, smul_eq_mul, mul_comm]

/-- **★ Constant-base condition transports through `cIntegratePolyG`** (conditional, *not*
unconditional): if the integrand's coefficients are differential constants
(`mapCoeffs (toPolyG c) = 0`), then so are the antiderivative's
(`mapCoeffs (toPolyG (cIntegratePolyG c)) = 0`). NOT free: the converse-style reading shows the output
condition is *equivalent* to the input one (each output coefficient `cᵢ/(i+1)` is constant iff `cᵢ` is),
so the hypothesis is genuinely needed. Proof: `Q := mapCoeffs (toPolyG (cIntegratePolyG c))` has
`derivative Q = mapCoeffs (derivative (toPolyG (cIntegratePolyG c))) = mapCoeffs (toPolyG c) = 0`
(commute + the atom `derivative_toPolyG_cIntegratePolyG` + hypothesis) and zero constant term
(`cIntegratePolyG` starts `0 :: …`), so `Q = 0` (`derivative_eq_zero` ⟹ `natDegree 0` ⟹ `C (coeff 0)`). -/
theorem cIntegratePolyG_const_coeff [CharZero (CFieldSpec.K α)] (c : CPolyG α)
    (hc : Differential.mapCoeffs (toPolyG c) = 0) :
    Differential.mapCoeffs (toPolyG (CPolyG.cIntegratePolyG c)) = 0 := by
  set Q := Differential.mapCoeffs (toPolyG (CPolyG.cIntegratePolyG c)) with hQ
  -- `derivative Q = 0` by commuting `mapCoeffs`/`derivative` and the formal-derivative atom
  have hderiv : Polynomial.derivative Q = 0 := by
    rw [hQ, ← mapCoeffs_derivative_commute, derivative_toPolyG_cIntegratePolyG, hc]
  -- `coeff Q 0 = 0`: `cIntegratePolyG` has zero constant term (`0 :: …`)
  have hcoeff0 : Q.coeff 0 = 0 := by
    rw [hQ, Differential.coeff_mapCoeffs]
    have : (toPolyG (CPolyG.cIntegratePolyG c)).coeff 0 = 0 := by
      rw [CPolyG.cIntegratePolyG, toPolyG_cons, coeff_add, coeff_C_zero, CFieldSpec.toK_zero,
        coeff_X_mul_zero, add_zero]
    rw [this, map_zero]
  -- `derivative Q = 0` ⟹ `natDegree Q = 0` ⟹ `Q = C (coeff Q 0) = 0`
  have hdeg : Q.natDegree = 0 := Polynomial.derivative_eq_zero.mp hderiv
  rw [eq_C_of_natDegree_eq_zero hdeg, hcoeff0, map_zero]

/-- **★★★ Fuel-free Poly-RDE soundness on the `b = 0` branch, keyed on the integrand** (the honest strongest
form): if `cPolyRischDEGWf [CField.one] [] c n = some q` (nonzero `c` within the degree budget,
primitive base `Dt = 1`) and the integrand is over a **constant base** (`mapCoeffs (toPolyG c) = 0`),
then the field-level antiderivative identity `towerFractionFieldDerivG [1] (amG(toPolyG q)/amG 1)
= amG(toPolyG c)/amG 1` holds — **no `checkIdentityG`, no `native_decide`**. Strengthens
`field_identity_of_cPolyRischDEGWf` by replacing its *output*-side `mapCoeffs (toPolyG q) = 0` with the
natural *input*-side `mapCoeffs (toPolyG c) = 0` (via `cIntegratePolyG_const_coeff`). **Regime
boundary**: `Dt = [CField.one]` is required — the `b = []` branch integrates by the term-by-term
`cIntegratePolyG`, which inverts the monomial derivation `D(tⁱ) = i·tⁱ⁻¹` only when `D(t) = 1`; for a
general monomial `D(tⁱ) = i·tⁱ⁻¹·Dt`, so term-by-term integration is no longer the inverse and this
branch is unreachable (the dispatcher routes `b = 0` here only in the primitive case `δ = 0`). -/
theorem cPolyRischDEGWf_nil_field_identity [CharZero (CFieldSpec.K α)] [Algebra ℚ (CFieldSpec.K α)]
    [CRischField α]
    (c q : CPolyG α) (n : ℤ)
    (hc : CPolyG.cisZeroG c = false) (hdeg : (CPolyG.cdegG c : ℤ) + 1 ≤ n)
    (hsome : CPolyG.cPolyRischDEGWf ([CField.one] : CPolyG α) ([] : CPolyG α) c n = some q)
    (hconst : Differential.mapCoeffs (toPolyG c) = 0) :
    towerFractionFieldDerivG ([CField.one] : CPolyG α)
        (amG α (toPolyG q) / amG α (toPolyG ([CField.one] : CPolyG α)))
      = amG α (toPolyG c) / amG α (toPolyG ([CField.one] : CPolyG α)) := by
  -- `q = cIntegratePolyGWf c`, so the output-side `mapCoeffs` follows from the input-side via the transport
  have hq : q = CPolyG.cIntegratePolyGWf c := by
    rw [cPolyRischDEGWf_nil_eq ([CField.one] : CPolyG α) c n hc hdeg] at hsome
    exact (Option.some.injEq _ _ ▸ hsome).symm
  subst hq
  exact field_identity_of_cPolyRischDEGWf c (CPolyG.cIntegratePolyGWf c) n hc hdeg
    (cPolyRischDEGWf_nil_eq ([CField.one] : CPolyG α) c n hc hdeg)
    (by
      rw [show CPolyG.cIntegratePolyGWf c = CPolyG.cIntegratePolyG c by rfl]
      exact cIntegratePolyG_const_coeff c hconst)

/-! ### ★ THE DELIVERABLE at the level-1 carrier `α = QFunNZG ℚ = ℚ(x)`

Instantiating the checker-free polynomial-branch one-shot at the generic level-1 carrier
`α = QFunNZG ℚ`, where `CFieldSpec.K (QFunNZG ℚ) = RatFunc ℚ` (genuine `Algebra ℚ` and `CharZero`).
This is the concrete `cPolyRischDEGWf = some res → D(res) = integrand` (no checker, no `native_decide`)
for the polynomial branch over `ℚ(x)(t)`. The two local instances bridge the carrier abbreviation to
`RatFunc ℚ`, the standard carrier-specialization pattern for the generic `field_identity_of_checkIdentityG`
bridge at `α = QFunNZG ℚ`. -/

/-- `CharZero (CFieldSpec.K (QFunNZG ℚ)) = CharZero (RatFunc ℚ)`: re-declared locally so the deliverable
synthesizes the `CharZero` the polynomial-branch one-shot needs over the carrier abbreviation. -/
noncomputable local instance : CharZero (CFieldSpec.K (QFunNZG ℚ)) :=
  inferInstanceAs (CharZero (RatFunc ℚ))

/-- The engine carrier `CFieldSpec.K (QFunNZG ℚ)` is `RatFunc ℚ`, a `ℚ`-algebra. Local instance so the
deliverable synthesizes the **same** `Algebra ℚ` the bridge `towerFractionFieldDerivG` uses. -/
noncomputable local instance : Algebra ℚ (CFieldSpec.K (QFunNZG ℚ)) :=
  inferInstanceAs (Algebra ℚ (RatFunc ℚ))

/-- **★★★ Fuel-free checker-free one-shot at `α = QFunNZG ℚ`** — the deliverable: if the Poly-Risch-DE
dispatcher's `b = 0` integration branch returns `some q` over the level-1 carrier `ℚ(x) = QFunNZG ℚ`
(`cPolyRischDEGWf [CField.one] [] c n = some q`, nonzero `c` within the degree budget, constant
base), then the field-level antiderivative identity `towerFractionFieldDerivG [1] (amG(toPolyG q)/amG 1)
= amG(toPolyG c)/amG 1` holds over `RatFunc ℚ` — with **no `checkIdentityG` executed**, no
`native_decide`. The genuine `algorithm = some res → D(res) = integrand` for the polynomial branch at
ℚ(x): the runtime guard is provably redundant. The `QFunNZG ℚ` instance of
`field_identity_of_cPolyRischDEGWf`. -/
theorem field_identity_of_cPolyRischDEGWf_qfunNZG (c q : CPolyG (QFunNZG ℚ)) (n : ℤ)
    (hc : CPolyG.cisZeroG c = false) (hdeg : (CPolyG.cdegG c : ℤ) + 1 ≤ n)
    (hsome : CPolyG.cPolyRischDEGWf ([CField.one] : CPolyG (QFunNZG ℚ)) ([] : CPolyG (QFunNZG ℚ)) c n
        = some q)
    (hconst : Differential.mapCoeffs (toPolyG q) = 0) :
    towerFractionFieldDerivG ([CField.one] : CPolyG (QFunNZG ℚ))
        (amG (QFunNZG ℚ) (toPolyG q) / amG (QFunNZG ℚ) (toPolyG ([CField.one] : CPolyG (QFunNZG ℚ))))
      = amG (QFunNZG ℚ) (toPolyG c)
          / amG (QFunNZG ℚ) (toPolyG ([CField.one] : CPolyG (QFunNZG ℚ))) :=
  field_identity_of_cPolyRischDEGWf c q n hc hdeg hsome hconst

/-! ### Restatements against the intended wording (anonymous `example`s) -/

-- ★ THE FORMAL-DERIVATIVE ATOM (UNCONDITIONAL, abstract, checker-free): the engine's term-by-term
-- antiderivative `cIntegratePolyG` differentiates back to its integrand, `D(toPolyG (cIntegratePolyG c))
-- = toPolyG c` over `(CFieldSpec.K α)[X]` — proven, no runtime check.
example [CharZero (CFieldSpec.K α)] (c : CPolyG α) :
    Polynomial.derivative (toPolyG (CPolyG.cIntegratePolyG c)) = toPolyG c :=
  derivative_toPolyG_cIntegratePolyG c

-- ★ THE CRUX (checker self-discharge): the polynomial-branch output PASSES `checkIdentityG` abstractly
-- (no check executed) — the missing link `algorithm-output ⟹ check-passes` for the reachable branch.
example [CharZero (CFieldSpec.K α)] (c : CPolyG α)
    (hconst : Differential.mapCoeffs (toPolyG (CPolyG.cIntegratePolyG c)) = 0) :
    CPolyG.checkIdentityG ([CField.one] : CPolyG α)
        ⟨(CPolyG.cIntegratePolyG c, ([CField.one] : CPolyG α)), []⟩ c ([CField.one] : CPolyG α)
      = true :=
  checkIdentityG_cIntegratePolyG_const c hconst

-- ★ THE DELIVERABLE at `α = QFunNZG ℚ`: `cPolyRischDEGWf = some q ⟹ D(res) = integrand` over `RatFunc ℚ`,
-- checker-free (the `checkIdentityG` guard is never run; no native_decide).
example (c q : CPolyG (QFunNZG ℚ)) (n : ℤ)
    (hc : CPolyG.cisZeroG c = false) (hdeg : (CPolyG.cdegG c : ℤ) + 1 ≤ n)
    (hsome : CPolyG.cPolyRischDEGWf ([CField.one] : CPolyG (QFunNZG ℚ)) ([] : CPolyG (QFunNZG ℚ)) c n
        = some q)
    (hconst : Differential.mapCoeffs (toPolyG q) = 0) :
    towerFractionFieldDerivG ([CField.one] : CPolyG (QFunNZG ℚ))
        (amG (QFunNZG ℚ) (toPolyG q) / amG (QFunNZG ℚ) (toPolyG ([CField.one] : CPolyG (QFunNZG ℚ))))
      = amG (QFunNZG ℚ) (toPolyG c)
          / amG (QFunNZG ℚ) (toPolyG ([CField.one] : CPolyG (QFunNZG ℚ))) :=
  field_identity_of_cPolyRischDEGWf_qfunNZG c q n hc hdeg hsome hconst

-- ★ CONSTANT-BASE TRANSPORT (conditional): integrand coefficients differential-constant ⟹ antiderivative
-- coefficients differential-constant (`mapCoeffs (toPolyG c) = 0 → mapCoeffs (toPolyG (cIntegratePolyG c))
-- = 0`) — the hypothesis is genuinely needed (the two conditions are equivalent).
example [CharZero (CFieldSpec.K α)] (c : CPolyG α)
    (hc : Differential.mapCoeffs (toPolyG c) = 0) :
    Differential.mapCoeffs (toPolyG (CPolyG.cIntegratePolyG c)) = 0 :=
  cIntegratePolyG_const_coeff c hc

-- ★ POLY-RDE SOUNDNESS keyed on the INTEGRAND (`b = 0` branch, primitive base): `cPolyRischDEGWf = some q`
-- with `mapCoeffs (toPolyG c) = 0` ⟹ `D(amG q/amG 1) = amG c/amG 1`, checker-free.
example [CharZero (CFieldSpec.K α)] [Algebra ℚ (CFieldSpec.K α)] [CRischField α]
    (c q : CPolyG α) (n : ℤ)
    (hc : CPolyG.cisZeroG c = false) (hdeg : (CPolyG.cdegG c : ℤ) + 1 ≤ n)
    (hsome : CPolyG.cPolyRischDEGWf ([CField.one] : CPolyG α) ([] : CPolyG α) c n = some q)
    (hconst : Differential.mapCoeffs (toPolyG c) = 0) :
    towerFractionFieldDerivG ([CField.one] : CPolyG α)
        (amG α (toPolyG q) / amG α (toPolyG ([CField.one] : CPolyG α)))
      = amG α (toPolyG c) / amG α (toPolyG ([CField.one] : CPolyG α)) :=
  cPolyRischDEGWf_nil_field_identity c q n hc hdeg hsome hconst

/-! ## ★★ The §6.6 CANCELLATION-case soundness (the broader poly-RDE, `b ≠ 0`, `deg b = 0`)

The `b = []` arc above is the *non-cancellation* `b = 0` pure-integration branch. The genuinely harder
reachable arms of `cPolyRischDEG` are the §6.6 **cancellation** cases (Bronstein p.212/213): when `deg(b) = 0`
(a degree-0 `t`-polynomial `b ∈ α*`) the leading terms of `Dq` and `b·q` cancel, so the solve recurses
degree-by-degree into the base RDE `crischDESolve b₀ (lc c)` (eq. 6.23, primitive) /
`crischDESolve (b₀ + m·η) (lc c)` (eq. 6.24, hyperexponential). These are `cPolyRischDECancelPrimG` /
`cPolyRischDECancelExpG`, which the dispatcher routes the primitive (`δ = 0`) / hyperexponential (`δ = 1`)
regimes into — the full-Risch poly-RDE beyond the `cIntegrateGFull` driver (which only hits `b = []`).

★ **The soundness needs NO base-oracle correctness.** The base solve `crischDESolve b₀ (lc c) = some s`
returns *some* `s`; the algorithm then subtracts `c ← c − b·(s·tᵐ) − D(s·tᵐ)` and recurses. Whatever `s`
is, this per-step subtraction makes the assembled `Dq + b·q = c` **telescope exactly** — the base solve's
correctness (the abstract `CRischFieldSpec.crischDESolve_spec`) only governs *whether* the recursion makes
progress (termination/completeness), not the soundness of the identity it returns. So the cancellation-case
soundness is a clean fuel induction over `toPolyG`, NO `[CRischFieldSpec α]` hypothesis needed — the base
solve enters as an opaque `some s`. This is the same shape as `derivative_toPolyG_cIntegratePolyG` (an
unconditional algorithm-correctness atom), now for the cancellation recursion. -/

section Cancellation

variable [CRischField α]

/-- **★ Primitive cancellation poly-RDE is sound** (`toPolyG_cmonomialDeriv_cPolyRischDECancelPrim`),
checker-free and base-oracle-free: if `cPolyRischDECancelPrimG Dt fuel b c n = some q` then the assembled
`q` solves `Dq + b·q = c` at the polynomial level — `toPolyG (cmonomialDeriv Dt q) + toPolyG b · toPolyG q
= toPolyG c` over `(CFieldSpec.K α)[X]`. Fuel induction: the base (`cisZeroG c`, `q = []`) gives
`0 = toPolyG c` (`cisZeroG_iff`); the step assembles `q = s·tᵐ + q'` with the IH `Dq' + b·q' = c'` and
`c' = c − b·(s·tᵐ) − D(s·tᵐ)`, telescoping to `Dq + b·q = c` by `linear_combination` (the derivation
`cmonomialDeriv = implicitDeriv` is additive). The base solve `crischDESolve b₀ (lc c) = some s` enters as
an OPAQUE witness — its correctness is irrelevant to the identity (only to termination), so NO
`[CRischFieldSpec α]`. -/
theorem toPolyG_cmonomialDeriv_cPolyRischDECancelPrim (Dt b : CPolyG α) :
    ∀ (fuel : ℕ) (c : CPolyG α) (n : ℤ) (q : CPolyG α),
      CPolyG.cPolyRischDECancelPrimG Dt fuel b c n = some q →
      toPolyG (CPolyG.cmonomialDeriv Dt q) + toPolyG b * toPolyG q = toPolyG c := by
  intro fuel
  induction fuel with
  | zero =>
    intro c n q hsolve
    rw [CPolyG.cPolyRischDECancelPrimG] at hsolve
    exact absurd hsolve (by simp)
  | succ fuel ih =>
    intro c n q hsolve
    rw [CPolyG.cPolyRischDECancelPrimG] at hsolve
    simp only at hsolve
    by_cases hc : CPolyG.cisZeroG c = true
    · rw [if_pos hc, Option.some.injEq] at hsolve
      subst hsolve
      rw [(cisZeroG_iff c).mp hc, toPolyG_cmonomialDeriv, toPolyG_nil, map_zero, mul_zero, add_zero]
    · rw [if_neg hc] at hsolve
      by_cases hn : n < (CPolyG.cdegG c : ℤ)
      · rw [if_pos hn] at hsolve; exact absurd hsolve (by simp)
      · rw [if_neg hn] at hsolve
        split at hsolve
        · exact absurd hsolve (by simp)
        · rename_i s _hbase
          split at hsolve
          · exact absurd hsolve (by simp)
          · rename_i q' hrec
            rw [Option.some.injEq] at hsolve
            subst hsolve
            have hih := ih _ _ q' hrec
            simp only [toPolyG_cmonomialDeriv, toPolyG_caddG, toPolyG_csubG, toPolyG_cmulG,
              map_add] at hih ⊢
            linear_combination hih

/-- **★ Hyperexponential cancellation poly-RDE is sound** (`toPolyG_cmonomialDeriv_cPolyRischDECancelExp`),
checker-free and base-oracle-free: if `cPolyRischDECancelExpG Dt fuel b c n = some q` then `Dq + b·q = c`
at the polynomial level — `toPolyG (cmonomialDeriv Dt q) + toPolyG b · toPolyG q = toPolyG c` over
`(CFieldSpec.K α)[X]`. Identical telescoping fuel induction to the primitive case
(`toPolyG_cmonomialDeriv_cPolyRischDECancelPrim`); the only algorithmic difference is the base RDE's shifted
coefficient `b₀ + m·η` (eq. 6.24), but the returned `s` again enters opaquely, so the per-step subtraction
`c ← c − b·(s·tᵐ) − D(s·tᵐ)` telescopes the same way. NO `[CRischFieldSpec α]` hypothesis. -/
theorem toPolyG_cmonomialDeriv_cPolyRischDECancelExp (Dt b : CPolyG α) :
    ∀ (fuel : ℕ) (c : CPolyG α) (n : ℤ) (q : CPolyG α),
      CPolyG.cPolyRischDECancelExpG Dt fuel b c n = some q →
      toPolyG (CPolyG.cmonomialDeriv Dt q) + toPolyG b * toPolyG q = toPolyG c := by
  intro fuel
  induction fuel with
  | zero =>
    intro c n q hsolve
    rw [CPolyG.cPolyRischDECancelExpG] at hsolve
    exact absurd hsolve (by simp)
  | succ fuel ih =>
    intro c n q hsolve
    rw [CPolyG.cPolyRischDECancelExpG] at hsolve
    simp only at hsolve
    by_cases hc : CPolyG.cisZeroG c = true
    · rw [if_pos hc, Option.some.injEq] at hsolve
      subst hsolve
      rw [(cisZeroG_iff c).mp hc, toPolyG_cmonomialDeriv, toPolyG_nil, map_zero, mul_zero, add_zero]
    · rw [if_neg hc] at hsolve
      by_cases hn : n < (CPolyG.cdegG c : ℤ)
      · rw [if_pos hn] at hsolve; exact absurd hsolve (by simp)
      · rw [if_neg hn] at hsolve
        split at hsolve
        · exact absurd hsolve (by simp)
        · rename_i s _hbase
          split at hsolve
          · exact absurd hsolve (by simp)
          · rename_i q' hrec
            rw [Option.some.injEq] at hsolve
            subst hsolve
            have hih := ih _ _ q' hrec
            simp only [toPolyG_cmonomialDeriv, toPolyG_caddG, toPolyG_csubG, toPolyG_cmulG,
              map_add] at hih ⊢
            linear_combination hih

/-- **★ Fuel-free primitive cancellation poly-RDE is sound**: if `cPolyRischDECancelPrimGWf Dt b c n =
some q`, then `q` solves `Dq + b·q = c` at the polynomial level. This is the direct Wf analogue of
`toPolyG_cmonomialDeriv_cPolyRischDECancelPrim`; the runtime length guard only adds terminal `none` cases. -/
theorem toPolyG_cmonomialDeriv_cPolyRischDECancelPrimGWf (Dt b c q : CPolyG α) (n : ℤ)
    (hsolve : CPolyG.cPolyRischDECancelPrimGWf Dt b c n = some q) :
    toPolyG (CPolyG.cmonomialDeriv Dt q) + toPolyG b * toPolyG q = toPolyG c := by
  fun_induction CPolyG.cPolyRischDECancelPrimGWf Dt b c n generalizing q with
  | case1 c _n hc =>
      rw [Option.some.injEq] at hsolve
      subst q
      rw [(cisZeroG_iff c).mp hc, toPolyG_cmonomialDeriv, toPolyG_nil, map_zero, mul_zero, add_zero]
  | case2 =>
      exact absurd hsolve (by simp)
  | case3 =>
      exact absurd hsolve (by simp)
  | case4 =>
      exact absurd hsolve (by simp)
  | case5 _c _n _b0 _hc _hn _m _s _hs _stm c' _hguard q' hrec ih =>
      rw [Option.some.injEq] at hsolve
      subst q
      have hih := ih q' hrec
      simp only [c', toPolyG_cmonomialDeriv, toPolyG_caddG, toPolyG_csubG, toPolyG_cmulG,
        map_add] at hih ⊢
      linear_combination hih
  | case6 =>
      exact absurd hsolve (by simp)

/-- **★ Fuel-free hyperexponential cancellation poly-RDE is sound**: if `cPolyRischDECancelExpGWf Dt b c n =
some q`, then `q` solves `Dq + b·q = c` at the polynomial level. This is the direct Wf analogue of
`toPolyG_cmonomialDeriv_cPolyRischDECancelExp`. -/
theorem toPolyG_cmonomialDeriv_cPolyRischDECancelExpGWf (Dt b c q : CPolyG α) (n : ℤ)
    (hsolve : CPolyG.cPolyRischDECancelExpGWf Dt b c n = some q) :
    toPolyG (CPolyG.cmonomialDeriv Dt q) + toPolyG b * toPolyG q = toPolyG c := by
  fun_induction CPolyG.cPolyRischDECancelExpGWf Dt b c n generalizing q with
  | case1 c _n hc =>
      rw [Option.some.injEq] at hsolve
      subst q
      rw [(cisZeroG_iff c).mp hc, toPolyG_cmonomialDeriv, toPolyG_nil, map_zero, mul_zero, add_zero]
  | case2 =>
      exact absurd hsolve (by simp)
  | case3 =>
      exact absurd hsolve (by simp)
  | case4 =>
      exact absurd hsolve (by simp)
  | case5 _c _n _b0 _eta _hc _hn _m _coeff _s _hs _stm c' _hguard q' hrec ih =>
      rw [Option.some.injEq] at hsolve
      subst q
      have hih := ih q' hrec
      simp only [c', toPolyG_cmonomialDeriv, toPolyG_caddG, toPolyG_csubG, toPolyG_cmulG,
        map_add] at hih ⊢
      linear_combination hih
  | case6 =>
      exact absurd hsolve (by simp)

/-! ### The dispatcher routes the cancellation regimes (Lemma 6.5.1)

`cPolyRischDEGWf` routes by `δ = deg(Dt)` and `deg(b)`. With `b ≠ 0` of degree `0`: the primitive regime
(`δ = 0`) goes to `cPolyRischDECancelPrimGWf`, the hyperexponential regime (`δ = 1`) to
`cPolyRischDECancelExpGWf`. The fuel-free soundness proofs inline this case split; named route lemmas remain
only for the still-fueled structural `cRischDEG` layer. -/

omit [CFieldSpec α] [CDiffFieldSpec α] in
/-- **The §6.5/§6.6 dispatcher reduces to the primitive cancellation solve** in the primitive regime with
`deg(b) = 0`, `b ≠ 0`: if `cdegG Dt = 0`, `cdegG b = 0`, `cisZeroG b = false` then
`cPolyRischDEG Dt fuel b c m = cPolyRischDECancelPrimG Dt fuel b c m`. The `δ = 0 ∧ deg(b) = 0` routing arm
of Lemma 6.5.1. -/
theorem cPolyRischDEG_eq_cancelPrim (Dt : CPolyG α) (fuel : ℕ) (b c : CPolyG α) (m : ℤ)
    (hδ : CPolyG.cdegG Dt = 0) (hdb : CPolyG.cdegG b = 0) (hb : CPolyG.cisZeroG b = false) :
    CPolyG.cPolyRischDEG Dt fuel b c m = CPolyG.cPolyRischDECancelPrimG Dt fuel b c m := by
  rw [CPolyG.cPolyRischDEG]
  simp only [hb, Bool.false_eq_true, if_false, hδ, hdb, Nat.cast_zero]
  rw [if_neg (by norm_num), if_pos ⟨trivial, trivial⟩]

omit [CFieldSpec α] [CDiffFieldSpec α] in
/-- **The §6.5/§6.6 dispatcher reduces to the hyperexponential cancellation solve** in the
hyperexponential regime with `deg(b) = 0`, `b ≠ 0`: if `cdegG Dt = 1`, `cdegG b = 0`, `cisZeroG b = false`
then `cPolyRischDEG Dt fuel b c m = cPolyRischDECancelExpG Dt fuel b c m`. The `δ = 1 ∧ deg(b) = 0` routing
arm of Lemma 6.5.1. -/
theorem cPolyRischDEG_eq_cancelExp (Dt : CPolyG α) (fuel : ℕ) (b c : CPolyG α) (m : ℤ)
    (hδ : CPolyG.cdegG Dt = 1) (hdb : CPolyG.cdegG b = 0) (hb : CPolyG.cisZeroG b = false) :
    CPolyG.cPolyRischDEG Dt fuel b c m = CPolyG.cPolyRischDECancelExpG Dt fuel b c m := by
  rw [CPolyG.cPolyRischDEG]
  simp only [hb, Bool.false_eq_true, if_false, hδ, hdb, Nat.cast_zero, Nat.cast_one]
  rw [if_neg (by norm_num), if_neg (by norm_num), if_pos ⟨trivial, trivial⟩]

/-- **★ Dispatcher-keyed primitive-cancellation soundness** (`cPolyRischDEG_cancelPrim_sound`): in the
primitive regime (`cdegG Dt = 0`, `deg(b) = 0`, `b ≠ 0`), a dispatcher success
`cPolyRischDEG Dt fuel b c m = some q` solves `Dq + b·q = c` at the polynomial level. Composes the routing
`cPolyRischDEG_eq_cancelPrim` with the cancellation soundness
`toPolyG_cmonomialDeriv_cPolyRischDECancelPrim`. -/
theorem cPolyRischDEG_cancelPrim_sound (Dt b c q : CPolyG α) (fuel : ℕ) (m : ℤ)
    (hδ : CPolyG.cdegG Dt = 0) (hdb : CPolyG.cdegG b = 0) (hb : CPolyG.cisZeroG b = false)
    (hsome : CPolyG.cPolyRischDEG Dt fuel b c m = some q) :
    toPolyG (CPolyG.cmonomialDeriv Dt q) + toPolyG b * toPolyG q = toPolyG c := by
  rw [cPolyRischDEG_eq_cancelPrim Dt fuel b c m hδ hdb hb] at hsome
  exact toPolyG_cmonomialDeriv_cPolyRischDECancelPrim Dt b fuel c m q hsome

/-- **★ Dispatcher-keyed hyperexponential-cancellation soundness** (`cPolyRischDEG_cancelExp_sound`): in
the hyperexponential regime (`cdegG Dt = 1`, `deg(b) = 0`, `b ≠ 0`), a dispatcher success
`cPolyRischDEG Dt fuel b c m = some q` solves `Dq + b·q = c` at the polynomial level. Composes the routing
`cPolyRischDEG_eq_cancelExp` with `toPolyG_cmonomialDeriv_cPolyRischDECancelExp`. -/
theorem cPolyRischDEG_cancelExp_sound (Dt b c q : CPolyG α) (fuel : ℕ) (m : ℤ)
    (hδ : CPolyG.cdegG Dt = 1) (hdb : CPolyG.cdegG b = 0) (hb : CPolyG.cisZeroG b = false)
    (hsome : CPolyG.cPolyRischDEG Dt fuel b c m = some q) :
    toPolyG (CPolyG.cmonomialDeriv Dt q) + toPolyG b * toPolyG q = toPolyG c := by
  rw [cPolyRischDEG_eq_cancelExp Dt fuel b c m hδ hdb hb] at hsome
  exact toPolyG_cmonomialDeriv_cPolyRischDECancelExp Dt b fuel c m q hsome

/-- **★ Fuel-free dispatcher-keyed primitive-cancellation soundness**: in the primitive regime
(`cdegG Dt = 0`, `deg(b) = 0`, `b ≠ 0`), a `cPolyRischDEGWf` success solves `Dq + b·q = c` at the
polynomial level. -/
theorem cPolyRischDEGWf_cancelPrim_sound (Dt b c q : CPolyG α) (m : ℤ)
    (hδ : CPolyG.cdegG Dt = 0) (hdb : CPolyG.cdegG b = 0) (hb : CPolyG.cisZeroG b = false)
    (hsome : CPolyG.cPolyRischDEGWf Dt b c m = some q) :
    toPolyG (CPolyG.cmonomialDeriv Dt q) + toPolyG b * toPolyG q = toPolyG c := by
  have hbranch : CPolyG.cPolyRischDECancelPrimGWf Dt b c m = some q := by
    rw [CPolyG.cPolyRischDEGWf] at hsome
    simp only [hb, Bool.false_eq_true, if_false, hδ, hdb, Nat.cast_zero] at hsome
    rw [if_neg (by norm_num), if_pos ⟨trivial, trivial⟩] at hsome
    exact hsome
  exact toPolyG_cmonomialDeriv_cPolyRischDECancelPrimGWf Dt b c q m hbranch

/-- **★ Fuel-free dispatcher-keyed hyperexponential-cancellation soundness**: in the hyperexponential regime
(`cdegG Dt = 1`, `deg(b) = 0`, `b ≠ 0`), a `cPolyRischDEGWf` success solves `Dq + b·q = c` at the polynomial
level. -/
theorem cPolyRischDEGWf_cancelExp_sound (Dt b c q : CPolyG α) (m : ℤ)
    (hδ : CPolyG.cdegG Dt = 1) (hdb : CPolyG.cdegG b = 0) (hb : CPolyG.cisZeroG b = false)
    (hsome : CPolyG.cPolyRischDEGWf Dt b c m = some q) :
    toPolyG (CPolyG.cmonomialDeriv Dt q) + toPolyG b * toPolyG q = toPolyG c := by
  have hbranch : CPolyG.cPolyRischDECancelExpGWf Dt b c m = some q := by
    rw [CPolyG.cPolyRischDEGWf] at hsome
    simp only [hb, Bool.false_eq_true, if_false, hδ, hdb, Nat.cast_zero, Nat.cast_one] at hsome
    rw [if_neg (by norm_num), if_neg (by norm_num), if_pos ⟨trivial, trivial⟩] at hsome
    exact hsome
  exact toPolyG_cmonomialDeriv_cPolyRischDECancelExpGWf Dt b c q m hbranch

/-! ### ★ The field-level lift of the cancellation soundness

The polynomial identity `Dq + b·q = c` over `(CFieldSpec.K α)[X]` lifts to the tower fraction field
`RatFunc (CFieldSpec.K α)` by pushing `towerFractionFieldDerivG` onto the polynomial image
(`extendDeriv_algebraMap`) and using that `amG` is a ring hom. This mirrors
`towerFractionFieldDerivG_amG_cIntegratePolyG_const` for the `b = []` branch — but with the genuine
`b ≠ 0` term carried through. -/

variable [Algebra ℚ (CFieldSpec.K α)]

omit [CRischField α] in
/-- **★ Field-level lift of a polynomial Risch-DE identity**
(`towerFractionFieldDerivG_amG_of_polyIdentity`): from `Dq + b·q = c` over `(CFieldSpec.K α)[X]` (the
`cmonomialDeriv`/`toPolyG` form), the tower fraction-field identity `towerFractionFieldDerivG Dt (amG q)
+ amG b · amG q = amG c` over `RatFunc (CFieldSpec.K α)`. `extendDeriv_algebraMap` pushes the field
derivation onto the polynomial image (`= amG (cmonomialDeriv Dt q)`), and `amG`'s ring-hom
`map_add`/`map_mul` collapse the cleared identity. The generic bridge under which both cancellation
soundnesses become field-level `D(q) + b·q = c`. -/
theorem towerFractionFieldDerivG_amG_of_polyIdentity (Dt b c q : CPolyG α)
    (hpoly : toPolyG (CPolyG.cmonomialDeriv Dt q) + toPolyG b * toPolyG q = toPolyG c) :
    towerFractionFieldDerivG Dt (amG α (toPolyG q))
        + amG α (toPolyG b) * amG α (toPolyG q)
      = amG α (toPolyG c) := by
  rw [towerFractionFieldDerivG, extendDeriv_algebraMap, ← toPolyG_cmonomialDeriv,
    ← map_mul, ← map_add, hpoly]

/-- **★★ Fuel-free field-level primitive-cancellation soundness** (`cPolyRischDEGWf_cancelPrim_field`): the headline
cancellation-case deliverable. In the primitive regime (`cdegG Dt = 0`, `deg(b) = 0`, `b ≠ 0`), a
dispatcher success `cPolyRischDEGWf Dt b c m = some q` solves the field-level Risch DE
`towerFractionFieldDerivG Dt (amG q) + amG b · amG q = amG c` over `RatFunc (CFieldSpec.K α)` — **no
`checkIdentityG`, no `native_decide`, no base-oracle correctness `[CRischFieldSpec α]`**. Composes
`cPolyRischDEGWf_cancelPrim_sound` (polynomial soundness) with `towerFractionFieldDerivG_amG_of_polyIdentity`
(field lift). The §6.6 primitive cancellation case bridged to the field level, base-oracle-free. -/
theorem cPolyRischDEGWf_cancelPrim_field (Dt b c q : CPolyG α) (m : ℤ)
    (hδ : CPolyG.cdegG Dt = 0) (hdb : CPolyG.cdegG b = 0) (hb : CPolyG.cisZeroG b = false)
    (hsome : CPolyG.cPolyRischDEGWf Dt b c m = some q) :
    towerFractionFieldDerivG Dt (amG α (toPolyG q))
        + amG α (toPolyG b) * amG α (toPolyG q)
      = amG α (toPolyG c) :=
  towerFractionFieldDerivG_amG_of_polyIdentity Dt b c q
    (cPolyRischDEGWf_cancelPrim_sound Dt b c q m hδ hdb hb hsome)

/-- **★★ Fuel-free field-level hyperexponential-cancellation soundness** (`cPolyRischDEGWf_cancelExp_field`): in the
hyperexponential regime (`cdegG Dt = 1`, `deg(b) = 0`, `b ≠ 0`), a dispatcher success
`cPolyRischDEGWf Dt b c m = some q` solves the field-level Risch DE `towerFractionFieldDerivG Dt (amG q)
+ amG b · amG q = amG c` over `RatFunc (CFieldSpec.K α)` — no `checkIdentityG`, no `native_decide`, no
`[CRischFieldSpec α]`. Composes `cPolyRischDEGWf_cancelExp_sound` with
`towerFractionFieldDerivG_amG_of_polyIdentity`. The §6.6 hyperexponential cancellation case at the field
level, base-oracle-free. -/
theorem cPolyRischDEGWf_cancelExp_field (Dt b c q : CPolyG α) (m : ℤ)
    (hδ : CPolyG.cdegG Dt = 1) (hdb : CPolyG.cdegG b = 0) (hb : CPolyG.cisZeroG b = false)
    (hsome : CPolyG.cPolyRischDEGWf Dt b c m = some q) :
    towerFractionFieldDerivG Dt (amG α (toPolyG q))
        + amG α (toPolyG b) * amG α (toPolyG q)
      = amG α (toPolyG c) :=
  towerFractionFieldDerivG_amG_of_polyIdentity Dt b c q
    (cPolyRischDEGWf_cancelExp_sound Dt b c q m hδ hdb hb hsome)

/-! ### Restatements against the intended wording (anonymous `example`s) -/

-- ★ Primitive cancellation poly-RDE soundness, checker-free and base-oracle-free: `cPolyRischDECancelPrimG
-- = some q ⟹ Dq + b·q = c` over `(CFieldSpec.K α)[X]`, NO `[CRischFieldSpec α]`.
example (Dt b : CPolyG α) (fuel : ℕ) (c : CPolyG α) (n : ℤ) (q : CPolyG α)
    (h : CPolyG.cPolyRischDECancelPrimG Dt fuel b c n = some q) :
    toPolyG (CPolyG.cmonomialDeriv Dt q) + toPolyG b * toPolyG q = toPolyG c :=
  toPolyG_cmonomialDeriv_cPolyRischDECancelPrim Dt b fuel c n q h

-- ★★ Field-level primitive-cancellation soundness via the fuel-free dispatcher, checker-free,
-- base-oracle-free: `cPolyRischDEGWf = some q` ⟹ `D(amG q) + amG b · amG q = amG c`.
example (Dt b c q : CPolyG α) (m : ℤ)
    (hδ : CPolyG.cdegG Dt = 0) (hdb : CPolyG.cdegG b = 0) (hb : CPolyG.cisZeroG b = false)
    (hsome : CPolyG.cPolyRischDEGWf Dt b c m = some q) :
    towerFractionFieldDerivG Dt (amG α (toPolyG q))
        + amG α (toPolyG b) * amG α (toPolyG q)
      = amG α (toPolyG c) :=
  cPolyRischDEGWf_cancelPrim_field Dt b c q m hδ hdb hb hsome

end Cancellation

/-! ### Axiom audit — the one-shot rests only on the standard kernel axioms
(`propext`, `Classical.choice`, `Quot.sound`); no `native_decide`, no `sorry`. -/

#print axioms derivative_toPolyG_cIntegratePolyG
#print axioms toPolyG_cmonomialDeriv_cIntegratePolyG_const
#print axioms towerFractionFieldDerivG_amG_cIntegratePolyG_const
#print axioms checkIdentityG_cIntegratePolyG_const
#print axioms field_identity_cIntegratePolyG_const
#print axioms field_identity_of_cPolyRischDEGWf
#print axioms field_identity_of_cPolyRischDEGWf_qfunNZG
#print axioms mapCoeffs_derivative_commute
#print axioms cIntegratePolyG_const_coeff
#print axioms cPolyRischDEGWf_nil_field_identity
#print axioms toPolyG_cmonomialDeriv_cPolyRischDECancelPrim
#print axioms toPolyG_cmonomialDeriv_cPolyRischDECancelExp
#print axioms toPolyG_cmonomialDeriv_cPolyRischDECancelPrimGWf
#print axioms toPolyG_cmonomialDeriv_cPolyRischDECancelExpGWf
#print axioms cPolyRischDEGWf_cancelPrim_field
#print axioms cPolyRischDEGWf_cancelExp_field

end DeepWiki.SymbolicIntegration
