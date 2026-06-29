import DeepWiki.SymbolicIntegration.ComputableTowerGcdFFCorrect
import DeepWiki.SymbolicIntegration.ComputableTowerUnify

/-! # §5 split-factor / canonical-representation correctness at the level-1 carrier `α = QFunNZG ℚ`
This file establishes the §5 split-factor / canonical-representation correctness at the **level-1 carrier**
`α = QFunNZG ℚ = Frac(ℚ[x])`, discharging the loop's gcd-correctness obligation through the **generic**
theorem `associated_toPolyG_cgcdFFCore` (`ComputableTowerGcdFFCorrect`), which reads the flat fraction-free
gcd `CFracGcdCore.cgcdFFCore` over `β(s)[t]` to the polynomial gcd up to associates — at the recursive tower
instance `instCFracGcdCoreQFunNZG`. The carrier `QFunNZG ℚ` reads through `toPolyG` into the field `RatFunc
ℚ = CFieldSpec.K (QFunNZG ℚ)`, so the abstract polynomial ring `(RatFunc ℚ)[X]` — and hence the conclusion
`IsSplittingFactorizationGen` / the reconstruction `f = a/d` — lives over that field.

With the generic gcd correctness in hand, the §5 split-factor / canonical-representation correctness threads
at `QFunNZG ℚ` through the generic engine's fraction-free gcd `cgcdFFCore`.

* **`cstepGQ`** — the generic `SplitFactor` step `S = cdivG (cgcdFFCore p Dp) (cgcdFFCore p dp/dt)` at
  `QFunNZG ℚ` (the inner `S` of `cSplitFactorFastG`), associated to the abstract `splitFactorStep`.
* **`cSplitFactorFastG_isSplittingFactorizationGen_qfunNZG`** — the loop output is a book-faithful splitting
  factorization, threaded through the generic gcd correctness.
* **`canonicalRepresentationFastG_reconstructs_qfunNZG`** — the §3.5 reconstruction with the
  denominator-split hypothesis DISCHARGED, at `QFunNZG ℚ`. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

/-! ### The differential-spec bridge `CDiffFieldSpec (QFunNZG ℚ)` (the genuine new ingredient)

The step proof identifies the second argument of `cgcdFFCore p (cmonomialDeriv Dt p)` with `implicitDeriv
(toPolyG Dt) (toPolyG p)` through `toPolyG_cmonomialDeriv`, which needs `[CDiffFieldSpec α]`. No
`CDiffFieldSpec (QFunNZG ℚ)` instance existed (the tower derivation's *spec* bridge — that the computable
`towerDerivQFunNZG [1]` agrees with a Mathlib `Differential` on `RatFunc ℚ` — was never built). We build it
here: the genuine Mathlib derivation is `fractionFieldDifferential (implicitDeriv (toPolyG 1))` — the
fraction-field derivation of the base `implicitDeriv (toPolyG ([1] : CPolyG ℚ))` on `ℚ[X]` — and
`toK_cderiv` is *exactly* the existing abstract bridge `toQFunNZG_towerDerivQFunNZG [1]` (no extra
agreement proof). This is the level-1 `CDiffFieldSpec (QFunNZG ℚ)` differential-spec bridge. -/

/-- **The base derivation `implicitDeriv (toPolyG 1)` on `(CFieldSpec.K ℚ)[X] = ℚ[X]`** (`= d/dx`, since
the base `Differential ℚ` is the zero derivation of constants): the `Derivation ℤ ℚ[X] ℚ[X]` whose
fraction-field extension is the `d/dx` derivation realizing the level-1 tower derivation
`towerDerivQFunNZG [1]` on `RatFunc ℚ`. -/
noncomputable def baseDerivQ : Derivation ℤ (CFieldSpec.K ℚ)[X] (CFieldSpec.K ℚ)[X] :=
  Differential.implicitDeriv (CPolyG.toPolyG ([CField.one] : CPolyG ℚ))

/-- **`CDiffFieldSpec (QFunNZG ℚ)`** (the genuine new ingredient): the differential-spec bridge for the
generic ℚ(x) carrier. The Mathlib derivation on `CFieldSpec.K (QFunNZG ℚ) = RatFunc ℚ` is
`fractionFieldDifferential baseDerivQ` (the fraction-field extension of `implicitDeriv (toPolyG 1)` on
`ℚ[X]`), and the intertwining `toK_cderiv` — `toQFunNZG (towerDerivQFunNZG [1] a) = (toQFunNZG a)′` — is
exactly the abstract bridge `toQFunNZG_towerDerivQFunNZG [1]` (`ComputableTowerDeriv`). Noncomputable
(routes through `RatFunc`), but only the correctness layer depends on it; the engine stays computable. The
level-1 ℚ(x) differential-spec bridge. -/
noncomputable instance instCDiffFieldSpecQFunNZG : CDiffFieldSpec (QFunNZG ℚ) where
  diffK := fractionFieldDifferential baseDerivQ
  toK_cderiv a := by
    show toQFunNZG (towerDerivQFunNZG [CField.one] a)
      = @Differential.deriv _ _ (fractionFieldDifferential baseDerivQ) (toQFunNZG a)
    rw [toQFunNZG_towerDerivQFunNZG [CField.one] a]
    rfl

/-! ### The gcd-correctness obligation at `QFunNZG ℚ`, packaged as a per-call regularity bundle

The split loop discharges, at each `cgcdFFCore` call, the obligation `Associated (toPolyG (cgcdFFCore fuel
p q)) (gcd (toPolyG p) (toPolyG q))`. At `QFunNZG ℚ` the **generic** `associated_toPolyG_cgcdFFCore`
discharges it from a `CPrimPRSGenAssocReg` regularity on the `gbdegCore`-ordered cleared pair. We package
that regularity as `CgcdFFCoreRegQ fuel p q` and restate the discharger as
`associated_toPolyG_cgcdFFCore_reg`. -/

/-- **Per-`cgcdFFCore`-call regularity bundle at `QFunNZG ℚ`** `CgcdFFCoreRegQ fuel p q`: the
`CPrimPRSGenAssocReg` regularity of the primitive PRS on the `gbdegCore`-ordered cleared pair of `p`, `q`,
with content-gcd `CFracGcdCore.cgcdFFRawCore fuel` at level `ℚ` — exactly the hypothesis the generic
`associated_toPolyG_cgcdFFCore` consumes. It captures the per-step content-exactness of the fraction-free
PRS that holds on real runs. -/
def CgcdFFCoreRegQ (fuel : ℕ) (p q : CPolyG (QFunNZG ℚ)) : Prop :=
  CPrimPRSGenAssocReg (CFracGcdCore.cgcdFFRawCore fuel) fuel
    (if GBPolyCore.gbdegCore (CPolyG.cclearDenomsCoreG p)
        < GBPolyCore.gbdegCore (CPolyG.cclearDenomsCoreG q)
      then CPolyG.cclearDenomsCoreG q else CPolyG.cclearDenomsCoreG p)
    (if GBPolyCore.gbdegCore (CPolyG.cclearDenomsCoreG p)
        < GBPolyCore.gbdegCore (CPolyG.cclearDenomsCoreG q)
      then CPolyG.cclearDenomsCoreG p else CPolyG.cclearDenomsCoreG q)

/-- **The generic `cgcdFFCore` is associated to the abstract gcd at `QFunNZG ℚ`**, from a `CgcdFFCoreRegQ`
bundle: `toPolyG (cgcdFFCore fuel p q)` is `Associated` to `gcd (toPolyG p) (toPolyG q)` in `(RatFunc ℚ)[X]
= (CFieldSpec.K (QFunNZG ℚ))[X]`. The thin wrapper over the generic theorem
`associated_toPolyG_cgcdFFCore`, instantiated at the level-1 carrier `QFunNZG ℚ`. -/
theorem associated_toPolyG_cgcdFFCore_reg (fuel : ℕ) (p q : CPolyG (QFunNZG ℚ))
    (hreg : CgcdFFCoreRegQ fuel p q) :
    Associated (toPolyG (CFracGcdCore.cgcdFFCore fuel p q)) (gcd (toPolyG p) (toPolyG q)) :=
  associated_toPolyG_cgcdFFCore fuel p q hreg

/-! ### The generic step `cstepGQ` is associated to the abstract `splitFactorStep` at `QFunNZG ℚ`

`cstepGQ Dt fuel p = cdivG (cgcdFFCore p Dp) (cgcdFFCore p dp/dt)` is the inner `S` of `cSplitFactorFastG`
at `QFunNZG ℚ`. The proof uses the generic gcd bridge `associated_toPolyG_cgcdFFCore_reg` for the two
`cgcdFFCore` calls and the generic exact division `toPolyG_cdivG_exact` to cancel the denominator gcd. -/

/-- **The generic computable `SplitFactor` step at `QFunNZG ℚ`** `cstepGQ Dt fuel p = cdivG (cgcdFFCore p
(cmonomialDeriv Dt p)) (cgcdFFCore p (cderivG p))` — the special-factor candidate `S = gcd(p, Dp)/gcd(p,
dp/dt)` computed with the generic flat fraction-free gcd `CFracGcdCore.cgcdFFCore` and the generic exact
division `cdivG` (the inner `S` of `cSplitFactorFastG` at `QFunNZG ℚ`). -/
def cstepGQ (Dt : CPolyG (QFunNZG ℚ)) (fuel : ℕ) (p : CPolyG (QFunNZG ℚ)) : CPolyG (QFunNZG ℚ) :=
  cdivG fuel (CFracGcdCore.cgcdFFCore fuel p (cmonomialDeriv Dt p))
    (CFracGcdCore.cgcdFFCore fuel p (cderivG p))

/-- **Per-step regularity bundle** `CStepGRegularQ Dt fuel p` for `cstepGQ`: node-regularity of both
`cgcdFFCore` calls (numerator `gcd(p, Dp)`, denominator `gcd(p, dp/dt)`, via `CgcdFFCoreRegQ`) and a fuel
bound on the numerator gcd's length so the exact Euclidean division `cdivG` is fully reduced. The
per-step regularity bundle at the level-1 carrier `QFunNZG ℚ`. -/
def CStepGRegularQ (Dt : CPolyG (QFunNZG ℚ)) (fuel : ℕ) (p : CPolyG (QFunNZG ℚ)) : Prop :=
  CgcdFFCoreRegQ fuel p (cmonomialDeriv Dt p) ∧
  CgcdFFCoreRegQ fuel p (cderivG p) ∧
  (cnormG (CFracGcdCore.cgcdFFCore fuel p (cmonomialDeriv Dt p)) : List (QFunNZG ℚ)).length ≤ fuel

/-- **The generic step is associated to the abstract `splitFactorStep` at `QFunNZG ℚ`**: for `toPolyG p ≠
0` and a regular generic step (`CStepGRegularQ`), `toPolyG (cstepGQ Dt fuel p)` is `Associated` to
`splitFactorStep (toPolyG Dt) (toPolyG p)` in `(RatFunc ℚ)[X]`. The two `cgcdFFCore` calls land the
numerator/denominator gcds up to associates (the GENERIC gcd correctness, no `cgcdFF`); exact division
cancels the (nonzero) denominator gcd, which divides the numerator gcd
(`gcd_derivative_dvd_gcd_implicitDeriv`). The `QFunNZG ℚ` mirror of `associated_toPolyG_cstepG`. -/
theorem associated_toPolyG_cstepGQ (Dt : CPolyG (QFunNZG ℚ)) (fuel : ℕ) (p : CPolyG (QFunNZG ℚ))
    (hp : toPolyG p ≠ 0) (hreg : CStepGRegularQ Dt fuel p) :
    Associated (toPolyG (cstepGQ Dt fuel p))
      (splitFactorStep (toPolyG Dt) (toPolyG p)) := by
  haveI : CharZero (CFieldSpec.K (QFunNZG ℚ)) := inferInstanceAs (CharZero (RatFunc ℚ))
  obtain ⟨hregN, hregD, hfuelN⟩ := hreg
  set v := toPolyG Dt with hv
  set P := toPolyG p with hP
  set N := CFracGcdCore.cgcdFFCore fuel p (cmonomialDeriv Dt p) with hN
  set Dn := CFracGcdCore.cgcdFFCore fuel p (cderivG p) with hDn
  -- the two gcd associations, with the second arguments identified by the bridges
  have aN : Associated (toPolyG N) (gcd P (Differential.implicitDeriv v P)) := by
    have h := associated_toPolyG_cgcdFFCore_reg fuel p (cmonomialDeriv Dt p) hregN
    rwa [toPolyG_cmonomialDeriv, ← hP, ← hv] at h
  have aD : Associated (toPolyG Dn) (gcd P (derivative P)) := by
    have h := associated_toPolyG_cgcdFFCore_reg fuel p (cderivG p) hregD
    rwa [toPolyG_cderivG, ← hP] at h
  -- the abstract gcds, the divisibility, and the exact factorization of the numerator gcd
  set gN := gcd P (Differential.implicitDeriv v P) with hgN
  set gD := gcd P (derivative P) with hgD
  have hgDdvd : gD ∣ gN := gcd_derivative_dvd_gcd_implicitDeriv v hp
  have hgDne : gD ≠ 0 := fun h => hp (eq_zero_of_zero_dvd (h ▸ gcd_dvd_left _ _))
  have hstepmul : splitFactorStep v P * gD = gN := by
    rw [splitFactorStep, ← hgN, ← hgD, mul_comm, EuclideanDomain.mul_div_cancel' hgDne hgDdvd]
  -- the denominator gcd divides the numerator gcd in the computable readings
  have hDn0 : toPolyG Dn ≠ 0 := fun h => hgDne (aD.eq_zero_iff.mp h)
  have hDncn : cnormG Dn ≠ [] := fun h => hDn0 ((cnormG_eq_nil_iff Dn).mp h)
  have hDnNdvd : toPolyG Dn ∣ toPolyG N :=
    (aD.dvd.trans hgDdvd).trans aN.symm.dvd
  -- exact division: toPolyG N = toPolyG (cstepGQ …) · toPolyG Dn (cstepGQ = cdivG N Dn)
  have hexact : toPolyG N = toPolyG (cstepGQ Dt fuel p) * toPolyG Dn := by
    have hNcn : cnormG Dn ≠ [] := hDncn
    have := toPolyG_cdivG_exact fuel N Dn hNcn hfuelN hDnNdvd
    rw [show cstepGQ Dt fuel p = cdivG fuel N Dn from rfl]
    exact this.symm
  -- cancel the denominator gcd: toPolyG (cstepGQ) · toPolyG Dn ~ splitFactorStep · gD, toPolyG Dn ~ gD
  have hmul : Associated (toPolyG (cstepGQ Dt fuel p) * toPolyG Dn) (splitFactorStep v P * gD) := by
    rw [← hexact, hstepmul]; exact aN
  exact Associated.of_mul_right hmul aD hDn0

/-! ### The generic loop output is a book-faithful splitting factorization at `QFunNZG ℚ`

By induction on fuel: at each non-terminal node the generic `S = cstepGQ` divides `toPolyG p` exactly
(the abstract step divides, transported through `associated_toPolyG_cstepGQ`), exact division keeps the
product invariant, and the abstract step facts supply `IsSpecial`/`IsNormalSqfree`. The per-node
regularity is `CgcdFFCoreRegQ` (via the generic gcd correctness) and the exact division is
`toPolyG_cdivG_exact`. -/

/-- **Recursive loop-regularity bundle** `CSplitFactorFastGRegularQ Dt fuel p` for `cSplitFactorFastG` at
`QFunNZG ℚ`: mirrors the recursion — at each node the generic step is regular (`CStepGRegularQ`) and the
dividend `t`-list is short enough that exact division `cdivG (fuel+1) p S` is fully reduced
(`(cnormG p).length ≤ fuel + 1`); if the step is non-constant, the same holds recursively on `p/S`. The
`QFunNZG ℚ` mirror of `CSplitFactorFastGRegular`. -/
def CSplitFactorFastGRegularQ (Dt : CPolyG (QFunNZG ℚ)) : ℕ → CPolyG (QFunNZG ℚ) → Prop
  | 0, _ => True
  | fuel + 1, p =>
    CStepGRegularQ Dt (fuel + 1) p ∧
      (cnormG p : List (QFunNZG ℚ)).length ≤ fuel + 1 ∧
      (cdegG (cstepGQ Dt (fuel + 1) p) = 0 ∨
        CSplitFactorFastGRegularQ Dt fuel
          (cdivG (fuel + 1) p (cstepGQ Dt (fuel + 1) p)))

/-- `toPolyG [CField.one] = 1` over `QFunNZG ℚ`: the computable unit reads as the polynomial `1`. -/
theorem toPolyG_cone_qfunNZG : toPolyG ([CField.one] : CPolyG (QFunNZG ℚ)) = 1 := by
  rw [toPolyG_cons, toPolyG_nil, mul_zero, add_zero, CFieldSpec.toK_one, map_one]

open Classical in
/-- **The GENERIC loop output is a book-faithful splitting factorization at `α = QFunNZG ℚ`** (the
assembly): for `toPolyG p ≠ 0`, fuel exceeding the `t`-degree (`(toPolyG p).natDegree ≤ fuel`), and a
regular run (`CSplitFactorFastGRegularQ`), the generic loop output `(pₙ, pₛ) = cSplitFactorFastG Dt fuel
p`, read through `toPolyG` over the field ℚ(x) = `RatFunc ℚ`, satisfies `IsSplittingFactorizationGen
(toPolyG p) (toPolyG pₛ) (toPolyG pₙ)` w.r.t. the monomial derivation `D` (`Dt = toPolyG Dt`). Same
conclusion shape as `cSplitFactorFastG_isSplittingFactorizationGen`, but threaded through the GENERIC gcd
correctness `associated_toPolyG_cgcdFFCore` (`associated_toPolyG_cstepGQ`) — with NO `cgcdFF`. The
de-risking result: §5 split-factor correctness holds at the generic ℚ(x) carrier. -/
theorem cSplitFactorFastG_isSplittingFactorizationGen_qfunNZG :
    ∀ (Dt : CPolyG (QFunNZG ℚ)) (fuel : ℕ) (p : CPolyG (QFunNZG ℚ)), toPolyG p ≠ 0 →
      (toPolyG p).natDegree ≤ fuel →
      CSplitFactorFastGRegularQ Dt fuel p →
      @IsSplittingFactorizationGen _ _ ⟨Differential.implicitDeriv (toPolyG Dt)⟩
        (toPolyG p)
        (toPolyG (CPolyG.cSplitFactorFastG Dt fuel p).2)
        (toPolyG (CPolyG.cSplitFactorFastG Dt fuel p).1) := by
  intro Dt fuel
  haveI : CharZero (CFieldSpec.K (QFunNZG ℚ)) := inferInstanceAs (CharZero (RatFunc ℚ))
  letI : Differential (CFieldSpec.K (QFunNZG ℚ))[X] := ⟨Differential.implicitDeriv (toPolyG Dt)⟩
  induction fuel with
  | zero =>
    intro p hp hdegp _
    -- fuel 0 ⇒ p constant; cSplitFactorFastG 0 p = (p, [one]); a constant is normal-sqfree
    have hpdeg0 : (toPolyG p).natDegree = 0 := Nat.le_zero.mp hdegp
    show IsSplittingFactorizationGen (toPolyG p)
      (toPolyG ([CField.one] : CPolyG (QFunNZG ℚ))) (toPolyG p)
    refine ⟨by rw [toPolyG_cone_qfunNZG, one_mul], by rw [toPolyG_cone_qfunNZG]; exact isSpecial_one, ?_⟩
    have hunit : IsUnit (toPolyG p) := Polynomial.isUnit_iff_degree_eq_zero.mpr
      (by rw [Polynomial.degree_eq_natDegree hp, hpdeg0]; rfl)
    exact (isNormal_of_isUnit hunit).isNormalSqfree
  | succ fuel ih =>
    intro p hp hdegp hreg
    obtain ⟨hstepreg, hpfuel, hbranch⟩ := hreg
    set S := cstepGQ Dt (fuel + 1) p with hSdef
    -- the generic step is associated to the abstract `splitFactorStep`
    have haS0 : Associated (toPolyG S) (splitFactorStep (toPolyG Dt) (toPolyG p)) :=
      associated_toPolyG_cstepGQ Dt (fuel + 1) p hp hstepreg
    have hcdeg0 : cdegG S = (toPolyG S).natDegree := cdegG_eq_natDegree S
    have hScn0 : (toPolyG S = 0) ↔ (cnormG S = []) := (cnormG_eq_nil_iff S).symm
    -- abstract the (giant) computable `toPolyG S` behind an OPAQUE variable `T`
    obtain ⟨T, hT⟩ : ∃ T, toPolyG S = T := ⟨toPolyG S, rfl⟩
    rw [hT] at haS0 hcdeg0 hScn0
    have haS : Associated T (splitFactorStep (toPolyG Dt) (toPolyG p)) := haS0
    have hstepne : splitFactorStep (toPolyG Dt) (toPolyG p) ≠ 0 := by
      have hdvd := splitFactorStep_dvd (toPolyG Dt) hp
      intro h0
      exact hp (eq_zero_of_zero_dvd (h0 ▸ hdvd))
    have hSne : T ≠ 0 := fun h => hstepne (eq_zero_of_zero_dvd (h ▸ haS.dvd))
    have hSnd : T.natDegree = (splitFactorStep (toPolyG Dt) (toPolyG p)).natDegree :=
      natDegree_eq_of_associated haS
    -- the computable generic loop step matches `S`
    have hloop : CPolyG.cSplitFactorFastG Dt (fuel + 1) p
        = (if cdegG S = 0 then (p, [CField.one])
           else ((CPolyG.cSplitFactorFastG Dt fuel (cdivG (fuel + 1) p S)).1,
                 cmulG S (CPolyG.cSplitFactorFastG Dt fuel (cdivG (fuel + 1) p S)).2)) := by
      conv_lhs => rw [CPolyG.cSplitFactorFastG]
      rfl
    have hcdeg : cdegG S = T.natDegree := hcdeg0
    by_cases hdeg : cdegG S = 0
    · -- terminal: (p, [one]); p is normal-sqfree (the abstract step is constant)
      rw [hloop, if_pos hdeg]
      have hSdeg0 : (splitFactorStep (toPolyG Dt) (toPolyG p)).natDegree = 0 := by
        rw [← hSnd, ← hcdeg]; exact hdeg
      show IsSplittingFactorizationGen (toPolyG p)
        (toPolyG ([CField.one] : CPolyG (QFunNZG ℚ))) (toPolyG p)
      refine ⟨by rw [toPolyG_cone_qfunNZG, one_mul], by rw [toPolyG_cone_qfunNZG]; exact isSpecial_one, ?_⟩
      exact isNormalSqfree_of_splitFactorStep_natDegree_zero (toPolyG Dt) hp hSdeg0
    · -- recursive step
      rw [hloop, if_neg hdeg]
      have hSpos : 0 < (splitFactorStep (toPolyG Dt) (toPolyG p)).natDegree := by
        rw [← hSnd, ← hcdeg]; exact Nat.pos_of_ne_zero hdeg
      have hSdvd : T ∣ toPolyG p :=
        haS.dvd.trans (splitFactorStep_dvd (toPolyG Dt) hp)
      have hSspec : @IsSpecial _ _ ⟨Differential.implicitDeriv (toPolyG Dt)⟩ T :=
        IsSpecial.of_associated haS.symm (isSpecial_splitFactorStep (toPolyG Dt) hp)
      -- exact division: `toPolyG p = toPolyG (cdivG p S) · T`
      have hScn : cnormG S ≠ [] := fun h => hSne (hScn0.mpr h)
      have hSdvd' : toPolyG S ∣ toPolyG p := by rw [hT]; exact hSdvd
      have hexact : toPolyG p = toPolyG (cdivG (fuel + 1) p S) * T := by
        have h : toPolyG (cdivG (fuel + 1) p S) * toPolyG S = toPolyG p :=
          toPolyG_cdivG_exact (fuel + 1) p S hScn hpfuel hSdvd'
        rw [hT] at h
        exact h.symm
      have hqne : toPolyG (cdivG (fuel + 1) p S) ≠ 0 := by
        intro h0; rw [h0, zero_mul] at hexact; exact hp hexact
      have hqdeg : (toPolyG (cdivG (fuel + 1) p S)).natDegree ≤ fuel := by
        have hdegdrop : (toPolyG (cdivG (fuel + 1) p S)).natDegree + T.natDegree
            = (toPolyG p).natDegree := by
          rw [hexact, Polynomial.natDegree_mul hqne hSne]
        have hSposc : 0 < T.natDegree := by rw [hSnd]; exact hSpos
        omega
      -- the recursive regularity branch (non-terminal: `cdegG S ≠ 0`)
      have hrecreg : CSplitFactorFastGRegularQ Dt fuel
          (cdivG (fuel + 1) p (cstepGQ Dt (fuel + 1) p)) :=
        hbranch.resolve_left hdeg
      rw [← hSdef] at hrecreg
      have hih := ih (cdivG (fuel + 1) p S) hqne hqdeg hrecreg
      obtain ⟨heq, hq2spec, hq1norm⟩ := hih
      refine ⟨?_, ?_, hq1norm⟩
      · -- `toPolyG p = toPolyG (cmulG S qs) · toPolyG qn`
        rw [toPolyG_cmulG, hT, mul_assoc, ← heq, mul_comm, hexact, mul_comm]
      · -- `S · qs` special
        rw [toPolyG_cmulG, hT]
        exact hSspec.mul hq2spec

/-! ### Discharging the probe hypothesis: `canonicalRepresentationFastG` reconstructs `f` at `QFunNZG ℚ`

The probe `canonicalRepresentationFastG_reconstructs` (`ComputableTowerUnify`) is **already generic over
`[CField α] [CDiffField α] [CFracGcdCore α] [CFieldSpec α]`** and so applies at `α = QFunNZG ℚ`; it took
the denominator split `toPolyG d = toPolyG dₛ·dₙ` as a hypothesis. The split is exactly the first component
(`.1`) of `cSplitFactorFastG_isSplittingFactorizationGen_qfunNZG` applied to `d`. We bundle the per-node
regularity and discharge the hypothesis — the deliverable proving the §5 correctness threads at `QFunNZG ℚ`
via the generic gcd correctness. -/

/-- **Per-run regularity bundle** `CCanonicalRepFastGRegularQ Dt fuel a d` for
`canonicalRepresentationFastG` at `QFunNZG ℚ`: the per-node preconditions for the GENERIC
`canonicalRepresentationFastG` to reconstruct `f = a/d` — the denominator split `cSplitFactorFastG Dt fuel
d` is a regular run (`CSplitFactorFastGRegularQ`), fuel exceeds the denominator `t`-degree, and the Bézout
gcd of the split parts is a nonzero constant (the coprime case). The `QFunNZG ℚ` mirror of
`CCanonicalRepFastGRegular`. -/
structure CCanonicalRepFastGRegularQ (Dt : CPolyG (QFunNZG ℚ)) (fuel : ℕ)
    (a d : CPolyG (QFunNZG ℚ)) : Prop where
  /-- `d` is nonzero. -/
  hd : toPolyG d ≠ 0
  /-- fuel exceeds the denominator `t`-degree (so `cSplitFactorFastG`/`cdivmodG` are reduced). -/
  hdeg : (toPolyG d).natDegree ≤ fuel
  /-- the denominator split is a regular `cSplitFactorFastG` run. -/
  hsplitreg : CSplitFactorFastGRegularQ Dt fuel d
  /-- the Bézout gcd of the split parts `(dₙ, dₛ)` is a **constant** (coprime case). -/
  hgdeg : (toPolyG (cgcdExtG fuel (CPolyG.cSplitFactorFastG Dt fuel d).1
    (CPolyG.cSplitFactorFastG Dt fuel d).2).1).natDegree = 0
  /-- the Bézout gcd is nonzero. -/
  hgne : toPolyG (cgcdExtG fuel (CPolyG.cSplitFactorFastG Dt fuel d).1
    (CPolyG.cSplitFactorFastG Dt fuel d).2).1 ≠ 0

open RatFunc in
/-- **★ `canonicalRepresentationFastG` reconstructs `f` at `α = QFunNZG ℚ`**: the probe's generic
reconstruction with the denominator-split hypothesis DISCHARGED at the generic ℚ(x) carrier. With the
generic output `(q, (b, dₛ), (c, dₙ)) = canonicalRepresentationFastG Dt fuel a d`, under the per-node
regularity bundle `CCanonicalRepFastGRegularQ`, the three pieces recombine to `f = a/d` in
`RatFunc (CFieldSpec.K (QFunNZG ℚ)) = RatFunc (RatFunc ℚ)` — `q + b/dₛ + c/dₙ = a/d`. The split fact the
probe assumed is supplied by `cSplitFactorFastG_isSplittingFactorizationGen_qfunNZG` (its `.1`), which is
threaded through the GENERIC gcd correctness — so this is the **unconditional** version, with NO `cgcdFF`.
The deliverable: the §5 split-factor / canonical-representation correctness threads at `QFunNZG ℚ` via the
generic gcd correctness (de-risking the carrier-migration sweep). -/
theorem canonicalRepresentationFastG_reconstructs_qfunNZG (Dt : CPolyG (QFunNZG ℚ)) (fuel : ℕ)
    (a d : CPolyG (QFunNZG ℚ)) (hreg : CCanonicalRepFastGRegularQ Dt fuel a d) :
    (let res := CPolyG.canonicalRepresentationFastG Dt fuel a d
      let q := res.1
      let b := res.2.1.1
      let ds := res.2.1.2
      let c := res.2.2.1
      let dn := res.2.2.2
      (algebraMap (CFieldSpec.K (QFunNZG ℚ))[X] (RatFunc (CFieldSpec.K (QFunNZG ℚ))) (toPolyG q))
          + algebraMap (CFieldSpec.K (QFunNZG ℚ))[X] (RatFunc (CFieldSpec.K (QFunNZG ℚ))) (toPolyG b)
              / algebraMap (CFieldSpec.K (QFunNZG ℚ))[X] (RatFunc (CFieldSpec.K (QFunNZG ℚ))) (toPolyG ds)
          + algebraMap (CFieldSpec.K (QFunNZG ℚ))[X] (RatFunc (CFieldSpec.K (QFunNZG ℚ))) (toPolyG c)
              / algebraMap (CFieldSpec.K (QFunNZG ℚ))[X] (RatFunc (CFieldSpec.K (QFunNZG ℚ))) (toPolyG dn)
        = algebraMap (CFieldSpec.K (QFunNZG ℚ))[X] (RatFunc (CFieldSpec.K (QFunNZG ℚ))) (toPolyG a)
            / algebraMap (CFieldSpec.K (QFunNZG ℚ))[X] (RatFunc (CFieldSpec.K (QFunNZG ℚ))) (toPolyG d)) := by
  obtain ⟨hd, hdeg, hsplitreg, hgdeg, hgne⟩ := hreg
  -- the denominator split, from the generic loop correctness (threaded through the generic gcd)
  have hsplit := cSplitFactorFastG_isSplittingFactorizationGen_qfunNZG Dt fuel d hd hdeg hsplitreg
  have hsplit_eq : toPolyG d
      = toPolyG (CPolyG.cSplitFactorFastG Dt fuel d).2 * toPolyG (CPolyG.cSplitFactorFastG Dt fuel d).1 :=
    hsplit.1
  -- both split parts nonzero, from the split product and `d ≠ 0`
  have hsplit_dn_ne : toPolyG (CPolyG.cSplitFactorFastG Dt fuel d).1 ≠ 0 := by
    intro h0; exact hd (by rw [hsplit_eq, h0, mul_zero])
  have hsplit_ds_ne : toPolyG (CPolyG.cSplitFactorFastG Dt fuel d).2 ≠ 0 := by
    intro h0; exact hd (by rw [hsplit_eq, h0, zero_mul])
  -- discharge the probe's split hypothesis and apply it (the probe is already generic)
  exact canonicalRepresentationFastG_reconstructs Dt fuel a d hd
    (fun _ _ => hsplit_eq) hsplit_dn_ne hsplit_ds_ne hgdeg hgne

/-! ### ★ The simple part `cₙ/dₙ` is proper at `α = QFunNZG ℚ` — split hypothesis DISCHARGED

`canonicalRepresentationFastG_simple_proper` (`ComputableTowerUnify`) gives `deg cₙ < deg dₙ` generic over
`α`, carrying the denominator split `d = dₛ·dₙ` as a hypothesis. At `α = QFunNZG ℚ` that split is supplied
by `cSplitFactorFastG_isSplittingFactorizationGen_qfunNZG` (its `.1`), so the simple-part properness becomes
**unconditional** (modulo only the fuel/regularity bundle) at the integrator's actual carrier — exactly the
last open dependency of `hproper` for `deg Dt ≤ 1`. -/

/-- **★ The canonical split's simple part `cₙ/dₙ` is proper at `α = QFunNZG ℚ`** — `deg cₙ < deg dₙ`, with
the denominator-split hypothesis DISCHARGED: for `canonicalRepresentationFastG Dt fuel a d = (q, (b, dₛ),
(cₙ, dₙ))` over ℚ(x)(t), under the per-node regularity bundle `CCanonicalRepFastGRegularQ` and enough fuel
for `a` (`hfuelA`) and the rescaled dividend `u·r` (`hfuelUR`), the simple-part numerator `cₙ` has degree
below `dₙ`. The split `d = dₛ·dₙ` feeding `canonicalRepresentationFastG_simple_proper` is supplied by
`cSplitFactorFastG_isSplittingFactorizationGen_qfunNZG` (its `.1`) — so this is the **unconditional**
version. It closes `hproper`/`haProper` of `cHermiteReduceTowerG_residual_proper_of_degree_le_one`, the
last open dependency of the §3.5 split-correctness frontier for `deg Dt ≤ 1`. -/
theorem canonicalRepresentationFastG_simple_proper_qfunNZG (Dt : CPolyG (QFunNZG ℚ)) (fuel : ℕ)
    (a d : CPolyG (QFunNZG ℚ)) (hreg : CCanonicalRepFastGRegularQ Dt fuel a d)
    (hfuelA : (cnormG a : List (QFunNZG ℚ)).length ≤ fuel)
    (hfuelUR : (cnormG (cmulG (CPolyG.cbezoutOne fuel (CPolyG.cSplitFactorFastG Dt fuel d).1
      (CPolyG.cSplitFactorFastG Dt fuel d).2).1 (cdivmodG fuel a d).2) : List (QFunNZG ℚ)).length
        ≤ fuel) :
    (toPolyG (CPolyG.canonicalRepresentationFastG Dt fuel a d).2.2.1).degree
      < (toPolyG (CPolyG.canonicalRepresentationFastG Dt fuel a d).2.2.2).degree := by
  obtain ⟨hd, hdeg, hsplitreg, hgdeg, hgne⟩ := hreg
  have hsplit := cSplitFactorFastG_isSplittingFactorizationGen_qfunNZG Dt fuel d hd hdeg hsplitreg
  have hsplit_eq : toPolyG d
      = toPolyG (CPolyG.cSplitFactorFastG Dt fuel d).2 * toPolyG (CPolyG.cSplitFactorFastG Dt fuel d).1 :=
    hsplit.1
  have hsplit_dn_ne : toPolyG (CPolyG.cSplitFactorFastG Dt fuel d).1 ≠ 0 := by
    intro h0; exact hd (by rw [hsplit_eq, h0, mul_zero])
  have hsplit_ds_ne : toPolyG (CPolyG.cSplitFactorFastG Dt fuel d).2 ≠ 0 := by
    intro h0; exact hd (by rw [hsplit_eq, h0, zero_mul])
  exact canonicalRepresentationFastG_simple_proper Dt fuel a d hd hsplit_eq hsplit_dn_ne
    hsplit_ds_ne hgdeg hgne hfuelA hfuelUR

/-! ### Restatements against the intended wording (anonymous `example`s) -/

-- The headline: the GENERIC fraction-free `cSplitFactorFastG` loop at `α = QFunNZG ℚ`, read over
-- ℚ(x) = `RatFunc ℚ`, returns a book-faithful splitting factorization of `toPolyG p` w.r.t. the monomial
-- derivation `Dt = toPolyG Dt` — threaded through the GENERIC gcd correctness (NO `cgcdFF`).
example (Dt : CPolyG (QFunNZG ℚ)) (fuel : ℕ) (p : CPolyG (QFunNZG ℚ)) (hp : toPolyG p ≠ 0)
    (hdegp : (toPolyG p).natDegree ≤ fuel) (hreg : CSplitFactorFastGRegularQ Dt fuel p) :
    @IsSplittingFactorizationGen _ _ ⟨Differential.implicitDeriv (toPolyG Dt)⟩
      (toPolyG p)
      (toPolyG (CPolyG.cSplitFactorFastG Dt fuel p).2)
      (toPolyG (CPolyG.cSplitFactorFastG Dt fuel p).1) :=
  cSplitFactorFastG_isSplittingFactorizationGen_qfunNZG Dt fuel p hp hdegp hreg

-- The deliverable: the generic `canonicalRepresentationFastG Dt fuel a d = (q, (b, dₛ), (c, dₙ))` at
-- `α = QFunNZG ℚ`, read over ℚ(x)(t), reconstructs `f = a/d` — `q + b/dₛ + c/dₙ = a/d` — with NO split
-- hypothesis (supplied internally via the generic gcd correctness), under the per-node preconditions.
example (Dt : CPolyG (QFunNZG ℚ)) (fuel : ℕ) (a d : CPolyG (QFunNZG ℚ))
    (hreg : CCanonicalRepFastGRegularQ Dt fuel a d) :
    (algebraMap (CFieldSpec.K (QFunNZG ℚ))[X] (RatFunc (CFieldSpec.K (QFunNZG ℚ)))
          (toPolyG (CPolyG.canonicalRepresentationFastG Dt fuel a d).1))
        + algebraMap (CFieldSpec.K (QFunNZG ℚ))[X] (RatFunc (CFieldSpec.K (QFunNZG ℚ)))
              (toPolyG (CPolyG.canonicalRepresentationFastG Dt fuel a d).2.1.1)
            / algebraMap (CFieldSpec.K (QFunNZG ℚ))[X] (RatFunc (CFieldSpec.K (QFunNZG ℚ)))
              (toPolyG (CPolyG.canonicalRepresentationFastG Dt fuel a d).2.1.2)
        + algebraMap (CFieldSpec.K (QFunNZG ℚ))[X] (RatFunc (CFieldSpec.K (QFunNZG ℚ)))
              (toPolyG (CPolyG.canonicalRepresentationFastG Dt fuel a d).2.2.1)
            / algebraMap (CFieldSpec.K (QFunNZG ℚ))[X] (RatFunc (CFieldSpec.K (QFunNZG ℚ)))
              (toPolyG (CPolyG.canonicalRepresentationFastG Dt fuel a d).2.2.2)
      = algebraMap (CFieldSpec.K (QFunNZG ℚ))[X] (RatFunc (CFieldSpec.K (QFunNZG ℚ))) (toPolyG a)
          / algebraMap (CFieldSpec.K (QFunNZG ℚ))[X] (RatFunc (CFieldSpec.K (QFunNZG ℚ))) (toPolyG d) :=
  canonicalRepresentationFastG_reconstructs_qfunNZG Dt fuel a d hreg

-- The simple-part properness: the canonical split `f = q + b/dₛ + cₙ/dₙ` at `α = QFunNZG ℚ` has a PROPER
-- simple part — `deg cₙ < deg dₙ` — with the denominator-split hypothesis discharged internally via the
-- generic split correctness; the last open dependency of `hproper` for `deg Dt ≤ 1`.
example (Dt : CPolyG (QFunNZG ℚ)) (fuel : ℕ) (a d : CPolyG (QFunNZG ℚ))
    (hreg : CCanonicalRepFastGRegularQ Dt fuel a d)
    (hfuelA : (cnormG a : List (QFunNZG ℚ)).length ≤ fuel)
    (hfuelUR : (cnormG (cmulG (CPolyG.cbezoutOne fuel (CPolyG.cSplitFactorFastG Dt fuel d).1
      (CPolyG.cSplitFactorFastG Dt fuel d).2).1 (cdivmodG fuel a d).2) : List (QFunNZG ℚ)).length
        ≤ fuel) :
    (toPolyG (CPolyG.canonicalRepresentationFastG Dt fuel a d).2.2.1).degree
      < (toPolyG (CPolyG.canonicalRepresentationFastG Dt fuel a d).2.2.2).degree :=
  canonicalRepresentationFastG_simple_proper_qfunNZG Dt fuel a d hreg hfuelA hfuelUR

/-! ### Axiom audit (the `QFunNZG ℚ` §5 correctness rests only on the standard kernel axioms) -/

#print axioms cSplitFactorFastG_isSplittingFactorizationGen_qfunNZG
#print axioms canonicalRepresentationFastG_reconstructs_qfunNZG
#print axioms canonicalRepresentationFastG_simple_proper_qfunNZG

end DeepWiki.SymbolicIntegration
