import DeepWiki.SymbolicIntegration.Engine.IntegrateTowerCorrectG
import DeepWiki.SymbolicIntegration.Engine.Tower.RischDEWellFounded
import DeepWiki.SymbolicIntegration.Engine.Tower.RischDEInstance

/-! # Checker-free soundness of the integrator's polynomial branch

Abstract correctness of the `b = 0` primitive-integration arm and the cancellation cases of the
poly-Risch-DE dispatcher: the antiderivative `cIntegratePoly` differentiates back to its integrand,
the output passes `checkIdentity` provably (never executed), and the field-level identity
`D(∫fₚ) = fₚ` follows through `field_identity_of_checkIdentityG`. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open CPoly CFrac

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]

omit [CDiffField α] [CDiffFieldSpec α] in
/-- Shifted antiderivative-tail derivative law: for the index-`k`-started integration tail
`L_k = (c.zipIdx k).map (fun (a,i) => a/(i+1))`, `D(X^{k+1} · toPoly L_k) = X^k · toPoly c`. -/
theorem derivative_Xpow_mul_toPolyG_integrateTail [CharZero (CFieldSpec.K α)] (c : CPoly α) :
    ∀ k : ℕ, Polynomial.derivative
        (X ^ (k + 1) *
          toPoly ((c.zipIdx k).map (fun ai => CField.div ai.1 (cnatCast (ai.2 + 1)))))
      = X ^ k * toPoly c := by
  induction c with
  | nil => intro k; simp
  | cons a as ih =>
    intro k
    -- `(a :: as).zipIdx k = (a, k) :: as.zipIdx (k+1)`; map and read `toPoly`
    simp only [List.zipIdx_cons, List.map_cons, toPolyG_cons, toR_eq_toK]
    -- `X^{k+1} · (C(toK (a/(k+1))) + X · toPoly(tail)) = C(..)·X^{k+1} + X^{k+2}·toPoly(tail)`
    rw [mul_add, derivative_add]
    -- the head term: `D(C(toK (a/(k+1)))·X^{k+1}) = (k+1)·C(toK (a/(k+1)))·X^k`
    have hhead : Polynomial.derivative
        (X ^ (k + 1) * Polynomial.C (CFieldSpec.toK (CField.div a (cnatCast (k + 1)))))
        = Polynomial.C (CFieldSpec.toK a) * X ^ k := by
      rw [mul_comm, derivative_C_mul, derivative_X_pow, add_tsub_cancel_right, ← mul_assoc, ← C_mul]
      congr 1
      -- `(toK (a/(k+1))) · (k+1 : K) = toK a`, since `toK (cnatCast (k+1)) = (k+1 : K)`
      rw [CFieldSpec.toK_div, CPoly.toK_cnatCastG]
      have hk1 : ((k : CFieldSpec.K α) + 1) ≠ 0 := by
        have : ((k : CFieldSpec.K α) + 1) = ((k + 1 : ℕ) : CFieldSpec.K α) := by push_cast; ring
        rw [this, Nat.cast_ne_zero]; omega
      push_cast
      field_simp
    -- the tail term: regroup `X^{k+1}·(X·toPoly tail) = X^{(k+1)+1}·toPoly tail`, apply IH at `k+1`
    have htail : Polynomial.derivative
        (X ^ (k + 1) * (X * toPoly
          ((as.zipIdx (k + 1)).map (fun ai => CField.div ai.1 (cnatCast (ai.2 + 1))))))
        = X ^ (k + 1) * toPoly as := by
      have hrw : X ^ (k + 1) * (X * toPoly
            ((as.zipIdx (k + 1)).map (fun ai => CField.div ai.1 (cnatCast (ai.2 + 1)))))
          = X ^ ((k + 1) + 1) * toPoly
            ((as.zipIdx (k + 1)).map (fun ai => CField.div ai.1 (cnatCast (ai.2 + 1)))) := by
        rw [pow_succ]; ring
      rw [hrw, ih (k + 1)]
    rw [hhead, htail, mul_add]
    ring

/-! ### The `cIntegratePoly` formal-derivative correctness

`cIntegratePoly c = 0 :: (c.zipIdx.map (fun (a,i) => a/(i+1)))` is the engine's term-by-term
antiderivative `∫ Σ cᵢtⁱ = Σ (cᵢ/(i+1)) t^{i+1}`; its formal derivative inverts it exactly.
Needs only characteristic zero (to divide by `i+1`). -/

omit [CDiffField α] [CDiffFieldSpec α] in
/-- `D(toPoly (cIntegratePoly c)) = toPoly c` over `(CFieldSpec.K α)[X]`,
`D = Polynomial.derivative`: the term-by-term antiderivative differentiates back to its integrand. -/
theorem derivative_toPolyG_cIntegratePolyG [CharZero (CFieldSpec.K α)] (c : CPoly α) :
    Polynomial.derivative (toPoly (CPoly.cIntegratePoly c)) = toPoly c := by
  have h := derivative_Xpow_mul_toPolyG_integrateTail c 0
  simpa only [CPoly.cIntegratePoly, toPolyG_cons, toR_eq_toK, CFieldSpec.toK_zero, map_zero, zero_add,
    pow_zero, pow_one, one_mul, List.zipIdx] using h

/-! ### The `cmonomialDeriv [1]` (monomial-derivation) form over a constant base

For the primitive monomial `Dt = [CField.one]`, `implicitDeriv 1 = mapCoeffs + derivative`, so the
antiderivative differentiates back exactly when the coefficient-derivation term `mapCoeffs` vanishes;
that constant-base regime is carried as the explicit hypothesis `hconst`. -/

/-- `cIntegratePoly` differentiates back under the primitive monomial derivation (`Dt = 1`): if
`mapCoeffs (toPoly (cIntegratePoly c)) = 0` (constant base), then
`toPoly (cmonomialDeriv [CField.one] (cIntegratePoly c)) = toPoly c` over `(CFieldSpec.K α)[X]`. -/
theorem toPolyG_cmonomialDeriv_cIntegratePolyG_const [CharZero (CFieldSpec.K α)] (c : CPoly α)
    (hconst : Differential.mapCoeffs (toPoly (CPoly.cIntegratePoly c)) = 0) :
    toPoly (CPoly.cmonomialDeriv ([CField.one] : CPoly α) (CPoly.cIntegratePoly c))
      = toPoly c := by
  rw [toPolyG_cmonomialDeriv]
  -- `toPoly [CField.one] = 1`, so `implicitDeriv 1 = mapCoeffs + derivative`
  have hDt : toPoly ([CField.one] : CPoly α) = 1 := by
    simp only [denote]
    simp
  rw [hDt, Differential.implicitDeriv, Derivation.add_apply, hconst, zero_add]
  -- the `v • derivative'` part is `1 • derivative = derivative`
  rw [Derivation.smul_apply, one_smul, Derivation.restrictScalars_apply]
  exact derivative_toPolyG_cIntegratePolyG c

/-! ### The field identity `D(∫ fₚ) = fₚ` for the polynomial part -/

/-- Field-level polynomial-part identity: over a constant base (`hconst`), the tower fraction-field
derivation sends the antiderivative to the integrand,
`towerFractionFieldDeriv [CField.one] (am (toPoly (cIntegratePoly c))) = am (toPoly c)` over
`RatFunc (CFieldSpec.K α)`. -/
theorem towerFractionFieldDerivG_amG_cIntegratePolyG_const [CharZero (CFieldSpec.K α)]
    [Algebra ℚ (CFieldSpec.K α)] (c : CPoly α)
    (hconst : Differential.mapCoeffs (toPoly (CPoly.cIntegratePoly c)) = 0) :
    towerFractionFieldDeriv ([CField.one] : CPoly α)
        (am α (toPoly (CPoly.cIntegratePoly c)))
      = am α (toPoly c) := by
  -- the tower field derivation on a polynomial image is the image of the monomial derivation
  rw [towerFractionFieldDeriv, extendDeriv_algebraMap, ← toPolyG_cmonomialDeriv]
  -- which the abstract atom identifies with `toPoly c`
  rw [toPolyG_cmonomialDeriv_cIntegratePolyG_const c hconst]

/-! ### The polynomial-branch output passes `checkIdentity` abstractly -/

/-- `toPoly (cmonomialDeriv [CField.one] [CField.one]) = 0`: the primitive monomial derivation
annihilates the constant `1`. -/
theorem toPolyG_cmonomialDeriv_one : toPoly
    (CPoly.cmonomialDeriv ([CField.one] : CPoly α) ([CField.one] : CPoly α)) = 0 := by
  rw [toPolyG_cmonomialDeriv]
  have hone : toPoly ([CField.one] : CPoly α) = 1 := by
    simp only [denote]
    simp
  rw [hone]
  exact Derivation.map_one_eq_zero _

/-- Over a constant base (`hconst`), the pure-polynomial result
`⟨(cIntegratePoly c, [CField.one]), []⟩` satisfies
`checkIdentity [CField.one] · c [CField.one] = true`, proven abstractly with no runtime check
executed: the `b = 0` integration branch always passes its own check. -/
theorem checkIdentityG_cIntegratePolyG_const [CharZero (CFieldSpec.K α)] (c : CPoly α)
    (hconst : Differential.mapCoeffs (toPoly (CPoly.cIntegratePoly c)) = 0) :
    CPoly.checkIdentity ([CField.one] : CPoly α)
        ⟨(CPoly.cIntegratePoly c, ([CField.one] : CPoly α)), []⟩ c ([CField.one] : CPoly α)
      = true := by
  -- unfold the check; the empty-log fold is just the seed `([0], [1])`
  rw [CPoly.checkIdentity]
  simp only [List.foldl_nil]
  -- the check is `cisZero (csub lhs rhs)`; clear to the polynomial identity `toPoly lhs = toPoly rhs`
  rw [cisZeroG_iff, toPolyG_csubG, sub_eq_zero]
  -- push `toPoly` through everything
  have hone : toPoly ([CField.one] : CPoly α) = 1 := by
    simp only [denote]
    simp
  have hzero : toPoly ([CField.zero] : CPoly α) = 0 := by
    simp only [denote, map_zero, mul_zero, add_zero]
  simp only [denote, hone, hzero]
  -- the rational-part numerator derivative `D(q)·1 − q·D(1)`, with `D(1) = 0`
  rw [Differential.implicitDeriv, Derivation.add_apply, hconst, zero_add,
    Derivation.smul_apply, one_smul, Derivation.restrictScalars_apply,
    Polynomial.derivative'_apply, derivative_toPolyG_cIntegratePolyG c,
    Derivation.map_one_eq_zero]
  ring

/-! ### The one-shot: compose the crux with the field bridge -/

/-- Checker-free one-shot `D(∫ fₚ) = fₚ` (polynomial branch): over a constant base, the antiderivative
`g = am(toPoly (cIntegratePoly c))/am 1` satisfies
`towerFractionFieldDeriv [1] g + logResidueSum [1] [] = am(toPoly c)/am 1`, obtained by feeding the
abstractly-proven `checkIdentity = true` into `field_identity_of_checkIdentityG`. -/
theorem field_identity_cIntegratePolyG_const [CharZero (CFieldSpec.K α)] [Algebra ℚ (CFieldSpec.K α)]
    (c : CPoly α) (hconst : Differential.mapCoeffs (toPoly (CPoly.cIntegratePoly c)) = 0) :
    towerFractionFieldDeriv ([CField.one] : CPoly α)
        (am α (toPoly (CPoly.cIntegratePoly c)) / am α (toPoly ([CField.one] : CPoly α)))
        + logResidueSum ([CField.one] : CPoly α)
            (⟨(CPoly.cIntegratePoly c, ([CField.one] : CPoly α)), []⟩ : IntegralResult α).logs
      = am α (toPoly c) / am α (toPoly ([CField.one] : CPoly α)) := by
  have hone_ne : toPoly ([CField.one] : CPoly α) ≠ 0 := by
    simp only [denote, map_one, mul_zero, add_zero]
    exact one_ne_zero
  exact field_identity_of_checkIdentityG ([CField.one] : CPoly α)
    ⟨(CPoly.cIntegratePoly c, ([CField.one] : CPoly α)), []⟩ c ([CField.one] : CPoly α)
    hone_ne hone_ne (by simp) (checkIdentityG_cIntegratePolyG_const c hconst)

/-! ### Keyed on the algorithm function `cPolyRischDE` -/

omit [CDiffFieldSpec α] in
/-- `cPolyRischDE` returns `cIntegratePoly c` on the nonzero `b = 0` branch within budget. -/
theorem cPolyRischDEG_nil_eq [CRischField α] (Dt : CPoly α) (c : CPoly α) (n : ℤ)
    (hc : CPoly.cisZero c = false) (hdeg : (CPoly.cdeg c : ℤ) + 1 ≤ n) :
    CPoly.cPolyRischDE Dt ([] : CPoly α) c n = some (CPoly.cIntegratePoly c) := by
  have hb : CPoly.cisZero ([] : CPoly α) = true := by rw [cisZeroG_iff, toPolyG_nil]
  simp only [CPoly.cPolyRischDE, hb, if_true, hc, Bool.false_eq_true, if_false]
  rw [if_neg (by omega : ¬ (CPoly.cdeg c : ℤ) + 1 > n)]

/-- Checker-free one-shot keyed on `cPolyRischDE`: if `cPolyRischDE [CField.one] [] c n = some q`
(nonzero `c` within the degree budget, constant base), then
`towerFractionFieldDeriv [1] (am(toPoly q)/am 1) = am(toPoly c)/am 1` holds, no `checkIdentity`
executed. -/
theorem field_identity_of_cPolyRischDEG [CharZero (CFieldSpec.K α)] [Algebra ℚ (CFieldSpec.K α)]
    [CRischField α]
    (c q : CPoly α) (n : ℤ)
    (hc : CPoly.cisZero c = false) (hdeg : (CPoly.cdeg c : ℤ) + 1 ≤ n)
    (hsome : CPoly.cPolyRischDE ([CField.one] : CPoly α) ([] : CPoly α) c n = some q)
    (hconst : Differential.mapCoeffs (toPoly q) = 0) :
    towerFractionFieldDeriv ([CField.one] : CPoly α)
        (am α (toPoly q) / am α (toPoly ([CField.one] : CPoly α)))
      = am α (toPoly c) / am α (toPoly ([CField.one] : CPoly α)) := by
  -- the algorithm output is exactly `cIntegratePoly c`
  have hq : q = CPoly.cIntegratePoly c := by
    rw [cPolyRischDEG_nil_eq ([CField.one] : CPoly α) c n hc hdeg] at hsome
    exact (Option.some.injEq _ _ ▸ hsome).symm
  subst hq
  -- empty logs ⇒ `logResidueSum … [] = 0`, so the field-identity is exactly the bridge output
  have h := field_identity_cIntegratePolyG_const (α := α) c hconst
  rwa [logResidueSumG_nil, add_zero] at h

/-! ### Discharging the constant-base hypothesis from integrand to antiderivative -/

/-- `mapCoeffs` commutes with `Polynomial.derivative` on `(CFieldSpec.K α)[X]`. -/
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

/-- Constant-base condition transports through `cIntegratePoly`: if `mapCoeffs (toPoly c) = 0` then
`mapCoeffs (toPoly (cIntegratePoly c)) = 0` (the two conditions are equivalent). -/
theorem cIntegratePolyG_const_coeff [CharZero (CFieldSpec.K α)] (c : CPoly α)
    (hc : Differential.mapCoeffs (toPoly c) = 0) :
    Differential.mapCoeffs (toPoly (CPoly.cIntegratePoly c)) = 0 := by
  set Q := Differential.mapCoeffs (toPoly (CPoly.cIntegratePoly c)) with hQ
  -- `derivative Q = 0` by commuting `mapCoeffs`/`derivative` and the formal-derivative atom
  have hderiv : Polynomial.derivative Q = 0 := by
    rw [hQ, ← mapCoeffs_derivative_commute, derivative_toPolyG_cIntegratePolyG, hc]
  -- `coeff Q 0 = 0`: `cIntegratePoly` has zero constant term (`0 :: …`)
  have hcoeff0 : Q.coeff 0 = 0 := by
    rw [hQ, Differential.coeff_mapCoeffs]
    have : (toPoly (CPoly.cIntegratePoly c)).coeff 0 = 0 := by
      rw [CPoly.cIntegratePoly, toPolyG_cons, coeff_add, coeff_C_zero, toR_eq_toK, CFieldSpec.toK_zero,
        coeff_X_mul_zero, add_zero]
    rw [this, map_zero]
  -- `derivative Q = 0` ⟹ `natDegree Q = 0` ⟹ `Q = C (coeff Q 0) = 0`
  have hdeg : Q.natDegree = 0 := Polynomial.derivative_eq_zero.mp hderiv
  rw [eq_C_of_natDegree_eq_zero hdeg, hcoeff0, map_zero]

/-- Fuel-free Poly-RDE soundness on the `b = 0` branch, keyed on the integrand: if
`cPolyRischDE [CField.one] [] c n = some q` (nonzero `c` within the degree budget, primitive base
`Dt = 1`) and `mapCoeffs (toPoly c) = 0`, then `towerFractionFieldDeriv [1] (am(toPoly q)/am 1)
= am(toPoly c)/am 1`. Requires `Dt = [CField.one]`: term-by-term integration inverts the monomial
derivation only when `D(t) = 1`. -/
theorem cPolyRischDEG_nil_field_identity [CharZero (CFieldSpec.K α)] [Algebra ℚ (CFieldSpec.K α)]
    [CRischField α]
    (c q : CPoly α) (n : ℤ)
    (hc : CPoly.cisZero c = false) (hdeg : (CPoly.cdeg c : ℤ) + 1 ≤ n)
    (hsome : CPoly.cPolyRischDE ([CField.one] : CPoly α) ([] : CPoly α) c n = some q)
    (hconst : Differential.mapCoeffs (toPoly c) = 0) :
    towerFractionFieldDeriv ([CField.one] : CPoly α)
        (am α (toPoly q) / am α (toPoly ([CField.one] : CPoly α)))
      = am α (toPoly c) / am α (toPoly ([CField.one] : CPoly α)) := by
  -- `q = cIntegratePoly c`, so the output-side `mapCoeffs` follows from the input-side via the transport
  have hq : q = CPoly.cIntegratePoly c := by
    rw [cPolyRischDEG_nil_eq ([CField.one] : CPoly α) c n hc hdeg] at hsome
    exact (Option.some.injEq _ _ ▸ hsome).symm
  subst hq
  exact field_identity_of_cPolyRischDEG c (CPoly.cIntegratePoly c) n hc hdeg
    (cPolyRischDEG_nil_eq ([CField.one] : CPoly α) c n hc hdeg)
    (cIntegratePolyG_const_coeff c hconst)

/-! ### The deliverable at the level-1 carrier `α = CFrac ℚ = ℚ(x)` -/

/-- `CharZero (CFieldSpec.K (CFrac ℚ))` via `RatFunc ℚ`: local instance for the polynomial-branch
one-shot over the carrier abbreviation. -/
noncomputable local instance : CharZero (CFieldSpec.K (CFrac ℚ)) :=
  inferInstanceAs (CharZero (RatFunc ℚ))

/-- Local `ℚ`-algebra structure on `CFieldSpec.K (CFrac ℚ)` via `RatFunc ℚ`. -/
noncomputable local instance : Algebra ℚ (CFieldSpec.K (CFrac ℚ)) :=
  inferInstanceAs (Algebra ℚ (RatFunc ℚ))

/-- Fuel-free checker-free one-shot at `α = CFrac ℚ`: if `cPolyRischDE [CField.one] [] c n = some q`
over `ℚ(x) = CFrac ℚ` (nonzero `c` within the degree budget, constant base), then
`towerFractionFieldDeriv [1] (am(toPoly q)/am 1) = am(toPoly c)/am 1` over `RatFunc ℚ`. The
`CFrac ℚ` instance of `field_identity_of_cPolyRischDEG`. -/
theorem field_identity_of_cPolyRischDEG_qfunNZG (c q : CPoly (CFrac ℚ)) (n : ℤ)
    (hc : CPoly.cisZero c = false) (hdeg : (CPoly.cdeg c : ℤ) + 1 ≤ n)
    (hsome : CPoly.cPolyRischDE ([CField.one] : CPoly (CFrac ℚ)) ([] : CPoly (CFrac ℚ)) c n
        = some q)
    (hconst : Differential.mapCoeffs (toPoly q) = 0) :
    towerFractionFieldDeriv ([CField.one] : CPoly (CFrac ℚ))
        (am (CFrac ℚ) (toPoly q) / am (CFrac ℚ) (toPoly ([CField.one] : CPoly (CFrac ℚ))))
      = am (CFrac ℚ) (toPoly c)
          / am (CFrac ℚ) (toPoly ([CField.one] : CPoly (CFrac ℚ))) :=
  field_identity_of_cPolyRischDEG c q n hc hdeg hsome hconst

/-! ### Restatements of the polynomial-branch identities -/

-- The term-by-term antiderivative `cIntegratePoly` differentiates back to its integrand.
example [CharZero (CFieldSpec.K α)] (c : CPoly α) :
    Polynomial.derivative (toPoly (CPoly.cIntegratePoly c)) = toPoly c :=
  derivative_toPolyG_cIntegratePolyG c

-- The polynomial-branch output satisfies `checkIdentity` abstractly, with no runtime check.
example [CharZero (CFieldSpec.K α)] (c : CPoly α)
    (hconst : Differential.mapCoeffs (toPoly (CPoly.cIntegratePoly c)) = 0) :
    CPoly.checkIdentity ([CField.one] : CPoly α)
        ⟨(CPoly.cIntegratePoly c, ([CField.one] : CPoly α)), []⟩ c ([CField.one] : CPoly α)
      = true :=
  checkIdentityG_cIntegratePolyG_const c hconst

-- At `α = CFrac ℚ`, a successful polynomial RDE solve differentiates back to the integrand.
example (c q : CPoly (CFrac ℚ)) (n : ℤ)
    (hc : CPoly.cisZero c = false) (hdeg : (CPoly.cdeg c : ℤ) + 1 ≤ n)
    (hsome : CPoly.cPolyRischDE ([CField.one] : CPoly (CFrac ℚ)) ([] : CPoly (CFrac ℚ)) c n
        = some q)
    (hconst : Differential.mapCoeffs (toPoly q) = 0) :
    towerFractionFieldDeriv ([CField.one] : CPoly (CFrac ℚ))
        (am (CFrac ℚ) (toPoly q) / am (CFrac ℚ) (toPoly ([CField.one] : CPoly (CFrac ℚ))))
      = am (CFrac ℚ) (toPoly c)
          / am (CFrac ℚ) (toPoly ([CField.one] : CPoly (CFrac ℚ))) :=
  field_identity_of_cPolyRischDEG_qfunNZG c q n hc hdeg hsome hconst

-- Differential-constant integrand coefficients give differential-constant antiderivative coefficients.
example [CharZero (CFieldSpec.K α)] (c : CPoly α)
    (hc : Differential.mapCoeffs (toPoly c) = 0) :
    Differential.mapCoeffs (toPoly (CPoly.cIntegratePoly c)) = 0 :=
  cIntegratePolyG_const_coeff c hc

-- Polynomial RDE soundness for the `b = 0` branch, keyed on the integrand.
example [CharZero (CFieldSpec.K α)] [Algebra ℚ (CFieldSpec.K α)] [CRischField α]
    (c q : CPoly α) (n : ℤ)
    (hc : CPoly.cisZero c = false) (hdeg : (CPoly.cdeg c : ℤ) + 1 ≤ n)
    (hsome : CPoly.cPolyRischDE ([CField.one] : CPoly α) ([] : CPoly α) c n = some q)
    (hconst : Differential.mapCoeffs (toPoly c) = 0) :
    towerFractionFieldDeriv ([CField.one] : CPoly α)
        (am α (toPoly q) / am α (toPoly ([CField.one] : CPoly α)))
      = am α (toPoly c) / am α (toPoly ([CField.one] : CPoly α)) :=
  cPolyRischDEG_nil_field_identity c q n hc hdeg hsome hconst

/-! ## The cancellation-case soundness (`b ≠ 0`, `deg b = 0`)

When `deg(b) = 0` the leading terms of `Dq` and `b·q` cancel, so the solve recurses degree-by-degree into
the base RDE — `cPolyRischDECancelPrim` (primitive) / `cPolyRischDECancelExp` (hyperexponential). The
soundness needs no base-oracle correctness: the per-step subtraction `c ← c − b·(s·tᵐ) − D(s·tᵐ)` makes
`Dq + b·q = c` telescope exactly whatever `s` the base solve returns, so it is a clean fuel induction over
`toPoly` with no `[CRischFieldSpec α]` hypothesis. -/

section Cancellation

variable [CRischField α]

/-- Fuel-free primitive cancellation poly-RDE is sound: if `cPolyRischDECancelPrim Dt b c n = some q`,
then `q` solves `Dq + b·q = c` at the polynomial level. -/
theorem toPolyG_cmonomialDeriv_cPolyRischDECancelPrimG (Dt b c q : CPoly α) (n : ℤ)
    (hsolve : CPoly.cPolyRischDECancelPrim Dt b c n = some q) :
    toPoly (CPoly.cmonomialDeriv Dt q) + toPoly b * toPoly q = toPoly c := by
  fun_induction CPoly.cPolyRischDECancelPrim Dt b c n generalizing q with
  | case1 c _n hc =>
      rw [Option.some.injEq] at hsolve
      subst q
      simp only [(cisZeroG_iff c).mp hc, denote, toPolyG_nil, map_zero, mul_zero, add_zero]
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
      simp only [c', denote, map_add] at hih ⊢
      linear_combination hih
  | case6 =>
      exact absurd hsolve (by simp)

/-- Fuel-free hyperexponential cancellation poly-RDE is sound: if `cPolyRischDECancelExp Dt b c n =
some q`, then `q` solves `Dq + b·q = c` at the polynomial level. -/
theorem toPolyG_cmonomialDeriv_cPolyRischDECancelExpG (Dt b c q : CPoly α) (n : ℤ)
    (hsolve : CPoly.cPolyRischDECancelExp Dt b c n = some q) :
    toPoly (CPoly.cmonomialDeriv Dt q) + toPoly b * toPoly q = toPoly c := by
  fun_induction CPoly.cPolyRischDECancelExp Dt b c n generalizing q with
  | case1 c _n hc =>
      rw [Option.some.injEq] at hsolve
      subst q
      simp only [(cisZeroG_iff c).mp hc, denote, toPolyG_nil, map_zero, mul_zero, add_zero]
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
      simp only [c', denote, map_add] at hih ⊢
      linear_combination hih
  | case6 =>
      exact absurd hsolve (by simp)

/-! ### The dispatcher routes the cancellation regimes

`cPolyRischDE` routes by `deg(Dt)` and `deg(b)`: with `b ≠ 0` of degree `0`, the primitive regime goes
to `cPolyRischDECancelPrim`, the hyperexponential regime to `cPolyRischDECancelExp`. -/

/-- Fuel-free dispatcher-keyed primitive-cancellation soundness: in the primitive regime (`cdeg Dt = 0`,
`deg(b) = 0`, `b ≠ 0`), a `cPolyRischDE` success solves `Dq + b·q = c` at the polynomial level. -/
theorem cPolyRischDEG_cancelPrim_sound (Dt b c q : CPoly α) (m : ℤ)
    (hδ : CPoly.cdeg Dt = 0) (hdb : CPoly.cdeg b = 0) (hb : CPoly.cisZero b = false)
    (hsome : CPoly.cPolyRischDE Dt b c m = some q) :
    toPoly (CPoly.cmonomialDeriv Dt q) + toPoly b * toPoly q = toPoly c := by
  have hbranch : CPoly.cPolyRischDECancelPrim Dt b c m = some q := by
    rw [CPoly.cPolyRischDE] at hsome
    simp only [hb, Bool.false_eq_true, if_false, hδ, hdb, Nat.cast_zero] at hsome
    rw [if_neg (by norm_num), if_pos ⟨trivial, trivial⟩] at hsome
    exact hsome
  exact toPolyG_cmonomialDeriv_cPolyRischDECancelPrimG Dt b c q m hbranch

/-- Fuel-free dispatcher-keyed hyperexponential-cancellation soundness: in the hyperexponential regime
(`cdeg Dt = 1`, `deg(b) = 0`, `b ≠ 0`), a `cPolyRischDE` success solves `Dq + b·q = c` at the
polynomial level. -/
theorem cPolyRischDEG_cancelExp_sound (Dt b c q : CPoly α) (m : ℤ)
    (hδ : CPoly.cdeg Dt = 1) (hdb : CPoly.cdeg b = 0) (hb : CPoly.cisZero b = false)
    (hsome : CPoly.cPolyRischDE Dt b c m = some q) :
    toPoly (CPoly.cmonomialDeriv Dt q) + toPoly b * toPoly q = toPoly c := by
  have hbranch : CPoly.cPolyRischDECancelExp Dt b c m = some q := by
    rw [CPoly.cPolyRischDE] at hsome
    simp only [hb, Bool.false_eq_true, if_false, hδ, hdb, Nat.cast_zero, Nat.cast_one] at hsome
    rw [if_neg (by norm_num), if_neg (by norm_num), if_pos ⟨trivial, trivial⟩] at hsome
    exact hsome
  exact toPolyG_cmonomialDeriv_cPolyRischDECancelExpG Dt b c q m hbranch

/-! ### The field-level lift of the cancellation soundness -/

variable [Algebra ℚ (CFieldSpec.K α)]

omit [CRischField α] in
/-- Field-level lift of a polynomial Risch-DE identity: from `Dq + b·q = c` over `(CFieldSpec.K α)[X]`
(the `cmonomialDeriv`/`toPoly` form), `towerFractionFieldDeriv Dt (am q) + am b · am q = am c` over
`RatFunc (CFieldSpec.K α)`. -/
theorem towerFractionFieldDerivG_amG_of_polyIdentity (Dt b c q : CPoly α)
    (hpoly : toPoly (CPoly.cmonomialDeriv Dt q) + toPoly b * toPoly q = toPoly c) :
    towerFractionFieldDeriv Dt (am α (toPoly q))
        + am α (toPoly b) * am α (toPoly q)
      = am α (toPoly c) := by
  rw [towerFractionFieldDeriv, extendDeriv_algebraMap, ← toPolyG_cmonomialDeriv,
    ← map_mul, ← map_add, hpoly]

/-- Fuel-free field-level primitive-cancellation soundness: in the primitive regime (`cdeg Dt = 0`,
`deg(b) = 0`, `b ≠ 0`), a dispatcher success `cPolyRischDE Dt b c m = some q` solves
`towerFractionFieldDeriv Dt (am q) + am b · am q = am c` over `RatFunc (CFieldSpec.K α)`,
base-oracle-free. -/
theorem cPolyRischDEG_cancelPrim_field (Dt b c q : CPoly α) (m : ℤ)
    (hδ : CPoly.cdeg Dt = 0) (hdb : CPoly.cdeg b = 0) (hb : CPoly.cisZero b = false)
    (hsome : CPoly.cPolyRischDE Dt b c m = some q) :
    towerFractionFieldDeriv Dt (am α (toPoly q))
        + am α (toPoly b) * am α (toPoly q)
      = am α (toPoly c) :=
  towerFractionFieldDerivG_amG_of_polyIdentity Dt b c q
    (cPolyRischDEG_cancelPrim_sound Dt b c q m hδ hdb hb hsome)

/-- Fuel-free field-level hyperexponential-cancellation soundness: in the hyperexponential regime
(`cdeg Dt = 1`, `deg(b) = 0`, `b ≠ 0`), a dispatcher success `cPolyRischDE Dt b c m = some q` solves
`towerFractionFieldDeriv Dt (am q) + am b · am q = am c` over `RatFunc (CFieldSpec.K α)`,
base-oracle-free. -/
theorem cPolyRischDEG_cancelExp_field (Dt b c q : CPoly α) (m : ℤ)
    (hδ : CPoly.cdeg Dt = 1) (hdb : CPoly.cdeg b = 0) (hb : CPoly.cisZero b = false)
    (hsome : CPoly.cPolyRischDE Dt b c m = some q) :
    towerFractionFieldDeriv Dt (am α (toPoly q))
        + am α (toPoly b) * am α (toPoly q)
      = am α (toPoly c) :=
  towerFractionFieldDerivG_amG_of_polyIdentity Dt b c q
    (cPolyRischDEG_cancelExp_sound Dt b c q m hδ hdb hb hsome)

/-! ### Restatements of the cancellation identities -/

-- Field-level primitive-cancellation soundness via the fuel-free dispatcher.
example (Dt b c q : CPoly α) (m : ℤ)
    (hδ : CPoly.cdeg Dt = 0) (hdb : CPoly.cdeg b = 0) (hb : CPoly.cisZero b = false)
    (hsome : CPoly.cPolyRischDE Dt b c m = some q) :
    towerFractionFieldDeriv Dt (am α (toPoly q))
        + am α (toPoly b) * am α (toPoly q)
      = am α (toPoly c) :=
  cPolyRischDEG_cancelPrim_field Dt b c q m hδ hdb hb hsome

end Cancellation

/-! ### Axiom audit — rests only on the standard kernel axioms
(`propext`, `Classical.choice`, `Quot.sound`). -/

#print axioms derivative_toPolyG_cIntegratePolyG
#print axioms toPolyG_cmonomialDeriv_cIntegratePolyG_const
#print axioms towerFractionFieldDerivG_amG_cIntegratePolyG_const
#print axioms checkIdentityG_cIntegratePolyG_const
#print axioms field_identity_cIntegratePolyG_const
#print axioms field_identity_of_cPolyRischDEG
#print axioms field_identity_of_cPolyRischDEG_qfunNZG
#print axioms mapCoeffs_derivative_commute
#print axioms cIntegratePolyG_const_coeff
#print axioms cPolyRischDEG_nil_field_identity
#print axioms toPolyG_cmonomialDeriv_cPolyRischDECancelPrimG
#print axioms toPolyG_cmonomialDeriv_cPolyRischDECancelExpG
#print axioms cPolyRischDEG_cancelPrim_field
#print axioms cPolyRischDEG_cancelExp_field

end DeepWiki.SymbolicIntegration
