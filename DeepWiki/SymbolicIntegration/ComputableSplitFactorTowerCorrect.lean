import DeepWiki.SymbolicIntegration.ComputableSplitFactorCorrect
import DeepWiki.SymbolicIntegration.ComputableCanonicalRepCorrect
import DeepWiki.SymbolicIntegration.ComputableTowerUnify

/-! # Abstract correctness of the GENERIC tower `splitFactorFast` at the level-1 carrier ℚ(x)
The generic tower engine's splitting-factorization loop `cSplitFactorFastG Dt fuel p`
(`ComputableTowerIntegrate`) is the `[CField α] [CDiffField α] [CFracGcdCore α]`-generic mirror of the
QFunNZ-specific `cSplitFactorFast`: same recursion, but with the flat fraction-free gcd
`CFracGcdCore.cgcdFFCore` (instead of the QFunNZ-hand-built `cgcdFF`) for the two gcds `gcd(p, Dp)` and
`gcd(p, dp/dt)`. `canonicalRepresentationFastG` — the §3.5 capstone used inside `cIntegrateG` — calls it
for the denominator split `d = dₛ·dₙ`. The unification probe (`ComputableTowerUnify`) proved
`canonicalRepresentationFastG_reconstructs` **modulo** that split, taking `toPolyG d = toPolyG dₛ·dₙ` as a
hypothesis, because `cSplitFactorFastG` had no abstract correctness lemma — only `native_decide`. This
file fills exactly that nucleus, **at the level-1 carrier `α = QFunNZ` the engine collapse instantiates**.

The collapse is at `α = QFunNZ`, where `CFracGcdCore.cgcdFFRawCore = cgcdFF` (`instCFracGcdCoreQFunNZ`),
so the public `cgcdFFCore fuel p q = cmonicG (cgcdFF fuel p q)` — the QFunNZ kernel with one extra monic
normalization. Monic normalization is a unit-scaling (`associated_toPolyG_cmonicG`), so the generic
`cgcdFFCore` reads through `toPolyG` to the **same** polynomial gcd up to associates as `cgcdFF`. Every
QFunNZ split-factor fact then transports through that single `associated_toPolyG_cmonicG.trans`:

1. **The differential bridge** `toPolyG_cmonomialDeriv` is `[CDiffFieldSpec α]`-GENERIC and **already
   exists** (`ComputableMonomialDeriv`): `toPolyG (cmonomialDeriv Dt p) = implicitDeriv (toPolyG Dt)
   (toPolyG p)`. We restate it as an `example` to pin that the probe's named bridge is in place.

2. **`associated_toPolyG_cstepG`** — the generic step `S = cdivG (cgcdFFCore p Dp) (cgcdFFCore p dp/dt)`
   read over ℚ(x) is `Associated` to `splitFactorStep`: the two `cgcdFFCore` calls land the numerator /
   denominator gcds up to associates (`cgcdFF` correctness + the monic bridge + `toPolyG_cmonomialDeriv`),
   exact division cancels the denominator gcd (which divides the numerator gcd,
   `gcd_derivative_dvd_gcd_implicitDeriv`). The `cstep` proof of `ComputableSplitFactorCorrect`,
   `cgcdFF ⤳ cgcdFFCore`.

3. **`cSplitFactorFastG_isSplittingFactorizationGen`** — the loop output is a book-faithful splitting
   factorization, by the same fuel induction as `cSplitFactorFast_isSplittingFactorizationGen`.

4. **`canonicalRepresentationFastG_reconstructs_qfunNZ`** — the probe's reconstruction with the split
   hypothesis DISCHARGED, the deliverable proving the nucleus is filled and the rest of the collapse is
   mechanical. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

/-! ### Task 1 — the `[CDiffFieldSpec α]` differential bridge (pre-existing, restated)

The probe named the polynomial-level differential bridge `toPolyG (cmonomialDeriv Dt p) = implicitDeriv
(toPolyG Dt) (toPolyG p)` as the one genuinely new ingredient. It **already exists** generically over
`[CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]` as `toPolyG_cmonomialDeriv`
(`ComputableMonomialDeriv`, the Stage-D key bridge), proved from `toPolyG`'s ring-hom lemmas
(`toPolyG_caddG`/`cmulG`/`cmapDeriv`/`cderivG`) and `implicitDeriv`'s definition. We restate it here as an
anonymous `example` to confirm it discharges the bridge the nucleus needs. -/

-- The `[CDiffFieldSpec α]` differential bridge (Task 1): the computable monomial derivation on `CPolyG α`
-- agrees with Mathlib's abstract `implicitDeriv` on `(CFieldSpec.K α)[X]`. Already proved generically as
-- `toPolyG_cmonomialDeriv`; no new work, the probe's bridge is in place.
example {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] (Dt p : CPolyG α) :
    toPolyG (cmonomialDeriv Dt p) = Differential.implicitDeriv (toPolyG Dt) (toPolyG p) :=
  CPolyG.toPolyG_cmonomialDeriv Dt p

/-! ### The generic `cgcdFFCore` at `α = QFunNZ` is associated to the polynomial gcd

At `α = QFunNZ` the instance `instCFracGcdCoreQFunNZ` makes the raw gcd `cgcdFFRawCore = cgcdFF`, so the
public `cgcdFFCore fuel p q = cmonicG (cgcdFF fuel p q)` (`rfl`). Monic normalization is a unit-scaling
(`associated_toPolyG_cmonicG`), and `cgcdFF` is associated to the polynomial gcd on a node-regular call
(`associated_toPolyG_cgcdFF_node`); composing the two associations gives `cgcdFFCore ~ gcd`. -/

/-- **`cgcdFFCore` reduces to `cmonicG ∘ cgcdFF` at `QFunNZ`** (`rfl`): the level-1 carrier's
`CFracGcdCore` instance has `cgcdFFRawCore = cgcdFF` (`instCFracGcdCoreQFunNZ`), so the public monic
wrapper `cgcdFFCore fuel p q = cmonicG (cgcdFF fuel p q)`. -/
theorem cgcdFFCore_eq_cmonicG_cgcdFF (fuel : ℕ) (p q : CPolyG QFunNZ) :
    CFracGcdCore.cgcdFFCore fuel p q = CPolyG.cmonicG (CPolyG.cgcdFF fuel p q) := rfl

/-- **The generic `cgcdFFCore` is associated to the abstract gcd at `QFunNZ`**, from a `CgcdFFNodeReg`
bundle: `toPolyG (cgcdFFCore fuel p q)` is `Associated` to `gcd (toPolyG p) (toPolyG q)` in
`(RatFunc ℚ)[X]`. Composes the monic unit-scaling (`associated_toPolyG_cmonicG`) with the QFunNZ `cgcdFF`
correctness (`associated_toPolyG_cgcdFF_node`); the extra `cmonicG` of the generic wrapper is the only
difference from `associated_toPolyG_cgcdFF_node` and it is associate-transparent. -/
theorem associated_toPolyG_cgcdFFCore_node (fuel : ℕ) (p q : CPolyG QFunNZ)
    (hreg : CgcdFFNodeReg fuel p q) :
    Associated (toPolyG (CFracGcdCore.cgcdFFCore fuel p q)) (gcd (toPolyG p) (toPolyG q)) := by
  rw [cgcdFFCore_eq_cmonicG_cgcdFF]
  exact (associated_toPolyG_cmonicG _).trans (associated_toPolyG_cgcdFF_node fuel p q hreg)

/-! ### Task 2 — the generic step `cstepG` is associated to the abstract `splitFactorStep`

`cstepG Dt fuel p = cdivG (cgcdFFCore p Dp) (cgcdFFCore p dp/dt)` is the inner `S` of `cSplitFactorFastG`
at `QFunNZ`. The proof mirrors `associated_toPolyG_cstep` (`ComputableSplitFactorCorrect`) verbatim, with
`cgcdFF ⤳ cgcdFFCore` (`associated_toPolyG_cgcdFFCore_node`) and `cdivFF ⤳ cdivG` (definitionally equal,
`cdivFF := cdivG`). -/

/-- **The generic computable `SplitFactor` step at `QFunNZ`** `cstepG Dt fuel p = cdivG (cgcdFFCore p
(cmonomialDeriv Dt p)) (cgcdFFCore p (cderivG p))` — the special-factor candidate `S = gcd(p, Dp)/gcd(p,
dp/dt)` computed with the generic flat fraction-free gcd `CFracGcdCore.cgcdFFCore` and the generic exact
division `cdivG` (the inner `S` of `cSplitFactorFastG` at `QFunNZ`). -/
def cstepG (Dt : CPolyG QFunNZ) (fuel : ℕ) (p : CPolyG QFunNZ) : CPolyG QFunNZ :=
  cdivG fuel (CFracGcdCore.cgcdFFCore fuel p (cmonomialDeriv Dt p))
    (CFracGcdCore.cgcdFFCore fuel p (cderivG p))

/-- **Per-step regularity bundle** `CStepGRegular Dt fuel p` for `cstepG`: the transparent preconditions
for the generic step `cstepG Dt fuel p` to match the abstract `splitFactorStep` — node-regularity of both
`cgcdFFCore` calls (numerator `gcd(p, Dp)`, denominator `gcd(p, dp/dt)`) and a fuel bound on the numerator
gcd's length so the exact Euclidean division `cdivG` is fully reduced. The same shape as `CStepRegular`,
with the numerator length-bound stated on `cgcdFFCore` (the divisor the generic step divides by lands
through `cmonicG`, so the bound is on the monic gcd). -/
def CStepGRegular (Dt : CPolyG QFunNZ) (fuel : ℕ) (p : CPolyG QFunNZ) : Prop :=
  CgcdFFNodeReg fuel p (cmonomialDeriv Dt p) ∧
  CgcdFFNodeReg fuel p (cderivG p) ∧
  (cnormG (CFracGcdCore.cgcdFFCore fuel p (cmonomialDeriv Dt p)) : List QFunNZ).length ≤ fuel

/-- **Task 2 — the generic step is associated to the abstract `splitFactorStep`**: for `toPolyG p ≠ 0`
and a regular generic step (`CStepGRegular`), `toPolyG (cstepG Dt fuel p)` is `Associated` to
`splitFactorStep (toPolyG Dt) (toPolyG p)` in `(RatFunc ℚ)[X]`. The two `cgcdFFCore` calls land the
numerator/denominator gcds up to associates (the monic bridge); exact division cancels the (nonzero)
denominator gcd, which divides the numerator gcd (`gcd_derivative_dvd_gcd_implicitDeriv`). The generic
mirror of `associated_toPolyG_cstep`. -/
theorem associated_toPolyG_cstepG (Dt : CPolyG QFunNZ) (fuel : ℕ) (p : CPolyG QFunNZ)
    (hp : toPolyG p ≠ 0) (hreg : CStepGRegular Dt fuel p) :
    Associated (toPolyG (cstepG Dt fuel p))
      (splitFactorStep (toPolyG Dt) (toPolyG p)) := by
  haveI : CharZero (CFieldSpec.K QFunNZ) := inferInstanceAs (CharZero (RatFunc ℚ))
  obtain ⟨hregN, hregD, hfuelN⟩ := hreg
  set v := toPolyG Dt with hv
  set P := toPolyG p with hP
  set N := CFracGcdCore.cgcdFFCore fuel p (cmonomialDeriv Dt p) with hN
  set Dn := CFracGcdCore.cgcdFFCore fuel p (cderivG p) with hDn
  -- the two gcd associations, with the second arguments identified by the bridges
  have aN : Associated (toPolyG N) (gcd P (Differential.implicitDeriv v P)) := by
    have h := associated_toPolyG_cgcdFFCore_node fuel p (cmonomialDeriv Dt p) hregN
    rwa [toPolyG_cmonomialDeriv, ← hP, ← hv] at h
  have aD : Associated (toPolyG Dn) (gcd P (derivative P)) := by
    have h := associated_toPolyG_cgcdFFCore_node fuel p (cderivG p) hregD
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
  -- exact division: toPolyG N = toPolyG (cstepG …) · toPolyG Dn
  have hexact : toPolyG N = toPolyG (cstepG Dt fuel p) * toPolyG Dn := by
    have := toPolyG_cdivFF_exact fuel N Dn hDncn hfuelN hDnNdvd
    rwa [show cstepG Dt fuel p = CPolyG.cdivFF fuel N Dn from rfl]
  -- cancel the denominator gcd: toPolyG (cstepG) · toPolyG Dn ~ splitFactorStep · gD, toPolyG Dn ~ gD
  have hmul : Associated (toPolyG (cstepG Dt fuel p) * toPolyG Dn) (splitFactorStep v P * gD) := by
    rw [← hexact, hstepmul]; exact aN
  exact Associated.of_mul_right hmul aD hDn0

/-! ### Task 2 — the generic loop output is a book-faithful splitting factorization

By induction on fuel mirroring `cSplitFactorFast_isSplittingFactorizationGen` (and hence
`splitFactorAux_isSplittingFactorizationGen`): at each non-terminal node the generic `S = cstepG` divides
`toPolyG p` exactly (the abstract step divides, transported through `associated_toPolyG_cstepG`), exact
division keeps the product invariant `toPolyG p = toPolyG S · toPolyG (p/S)`, and the abstract step facts
pushed across the association supply `IsSpecial`/`IsNormalSqfree`. -/

/-- **Recursive loop-regularity bundle** `CSplitFactorFastGRegular Dt fuel p` for `cSplitFactorFastG`:
mirrors the `cSplitFactorFastG` recursion — at each node the generic step is regular (`CStepGRegular`) and
the dividend `t`-list is short enough that exact division `cdivG (fuel+1) p S` is fully reduced
(`(cnormG p).length ≤ fuel + 1`); if the step is non-constant, the same holds recursively on `p/S`. The
generic mirror of `CSplitFactorFastRegular` (with `cstepG`/`cdivG` for `cstep`/`cdivFF`). -/
def CSplitFactorFastGRegular (Dt : CPolyG QFunNZ) : ℕ → CPolyG QFunNZ → Prop
  | 0, _ => True
  | fuel + 1, p =>
    CStepGRegular Dt (fuel + 1) p ∧
      (cnormG p : List QFunNZ).length ≤ fuel + 1 ∧
      (cdegG (cstepG Dt (fuel + 1) p) = 0 ∨
        CSplitFactorFastGRegular Dt fuel
          (cdivG (fuel + 1) p (cstepG Dt (fuel + 1) p)))

open Classical in
/-- **Task 2 — the GENERIC loop output is a book-faithful splitting factorization** (the assembly): for
`toPolyG p ≠ 0`, fuel exceeding the `t`-degree (`(toPolyG p).natDegree ≤ fuel`), and a regular run
(`CSplitFactorFastGRegular`), the generic loop output `(pₙ, pₛ) = cSplitFactorFastG Dt fuel p`, read
through `toPolyG` over the field ℚ(x) = `RatFunc ℚ`, satisfies `IsSplittingFactorizationGen (toPolyG p)
(toPolyG pₛ) (toPolyG pₙ)` w.r.t. the monomial derivation `D` (`Dt = toPolyG Dt`). The generic analog of
`cSplitFactorFast_isSplittingFactorizationGen`, transported `QFunNZ → cgcdFFCore` through the monic bridge
(`associated_toPolyG_cstepG`); the non-differential induction transports verbatim. -/
theorem cSplitFactorFastG_isSplittingFactorizationGen :
    ∀ (Dt : CPolyG QFunNZ) (fuel : ℕ) (p : CPolyG QFunNZ), toPolyG p ≠ 0 →
      (toPolyG p).natDegree ≤ fuel →
      CSplitFactorFastGRegular Dt fuel p →
      @IsSplittingFactorizationGen _ _ ⟨Differential.implicitDeriv (toPolyG Dt)⟩
        (toPolyG p)
        (toPolyG (CPolyG.cSplitFactorFastG Dt fuel p).2)
        (toPolyG (CPolyG.cSplitFactorFastG Dt fuel p).1) := by
  intro Dt fuel
  haveI : CharZero (CFieldSpec.K QFunNZ) := inferInstanceAs (CharZero (RatFunc ℚ))
  letI : Differential (CFieldSpec.K QFunNZ)[X] := ⟨Differential.implicitDeriv (toPolyG Dt)⟩
  induction fuel with
  | zero =>
    intro p hp hdegp _
    -- fuel 0 ⇒ p constant; cSplitFactorFastG 0 p = (p, [one]); a constant is normal-sqfree
    have hpdeg0 : (toPolyG p).natDegree = 0 := Nat.le_zero.mp hdegp
    show IsSplittingFactorizationGen (toPolyG p) (toPolyG ([CField.one] : CPolyG QFunNZ)) (toPolyG p)
    refine ⟨by rw [toPolyG_cone, one_mul], by rw [toPolyG_cone]; exact isSpecial_one, ?_⟩
    have hunit : IsUnit (toPolyG p) := Polynomial.isUnit_iff_degree_eq_zero.mpr
      (by rw [Polynomial.degree_eq_natDegree hp, hpdeg0]; rfl)
    exact (isNormal_of_isUnit hunit).isNormalSqfree
  | succ fuel ih =>
    intro p hp hdegp hreg
    obtain ⟨hstepreg, hpfuel, hbranch⟩ := hreg
    set S := cstepG Dt (fuel + 1) p with hSdef
    -- the generic step is associated to the abstract `splitFactorStep`
    have haS0 : Associated (toPolyG S) (splitFactorStep (toPolyG Dt) (toPolyG p)) :=
      associated_toPolyG_cstepG Dt (fuel + 1) p hp hstepreg
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
      show IsSplittingFactorizationGen (toPolyG p) (toPolyG ([CField.one] : CPolyG QFunNZ)) (toPolyG p)
      refine ⟨by rw [toPolyG_cone, one_mul], by rw [toPolyG_cone]; exact isSpecial_one, ?_⟩
      exact isNormalSqfree_of_splitFactorStep_natDegree_zero (toPolyG Dt) hp hSdeg0
    · -- recursive step
      rw [hloop, if_neg hdeg]
      have hSpos : 0 < (splitFactorStep (toPolyG Dt) (toPolyG p)).natDegree := by
        rw [← hSnd, ← hcdeg]; exact Nat.pos_of_ne_zero hdeg
      have hSdvd : T ∣ toPolyG p :=
        haS.dvd.trans (splitFactorStep_dvd (toPolyG Dt) hp)
      have hSspec : @IsSpecial _ _ ⟨Differential.implicitDeriv (toPolyG Dt)⟩ T :=
        IsSpecial.of_associated haS.symm (isSpecial_splitFactorStep (toPolyG Dt) hp)
      -- exact division: `toPolyG p = toPolyG (cdivG p S) · T` (cdivG = cdivFF)
      have hScn : cnormG S ≠ [] := fun h => hSne (hScn0.mpr h)
      -- the divisibility in the literal `toPolyG S ∣ toPolyG p` shape (controlled goal-`rw`, no
      -- motive-unification whnf blowup over the giant `cstepG` term)
      have hSdvd' : toPolyG S ∣ toPolyG p := by rw [hT]; exact hSdvd
      have hexact : toPolyG p = toPolyG (cdivG (fuel + 1) p S) * T := by
        have h : toPolyG p = toPolyG (CPolyG.cdivFF (fuel + 1) p S) * toPolyG S :=
          toPolyG_cdivFF_exact (fuel + 1) p S hScn hpfuel hSdvd'
        rw [show CPolyG.cdivFF (fuel + 1) p S = cdivG (fuel + 1) p S from rfl, hT] at h
        exact h
      have hqne : toPolyG (cdivG (fuel + 1) p S) ≠ 0 := by
        intro h0; rw [h0, zero_mul] at hexact; exact hp hexact
      have hqdeg : (toPolyG (cdivG (fuel + 1) p S)).natDegree ≤ fuel := by
        have hdegdrop : (toPolyG (cdivG (fuel + 1) p S)).natDegree + T.natDegree
            = (toPolyG p).natDegree := by
          rw [hexact, Polynomial.natDegree_mul hqne hSne]
        have hSposc : 0 < T.natDegree := by rw [hSnd]; exact hSpos
        omega
      -- the recursive regularity branch (non-terminal: `cdegG S ≠ 0`)
      have hrecreg : CSplitFactorFastGRegular Dt fuel
          (cdivG (fuel + 1) p (cstepG Dt (fuel + 1) p)) :=
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

/-! ### Task 3 — discharging the probe hypothesis: `canonicalRepresentationFastG` reconstructs `f`

The probe `canonicalRepresentationFastG_reconstructs` (`ComputableTowerUnify`) took the denominator split
`toPolyG d = toPolyG dₛ·dₙ` as a hypothesis. The split is exactly the first component (`.1`) of
`cSplitFactorFastG_isSplittingFactorizationGen` applied to `d`. We bundle the per-node regularity and
discharge the hypothesis — the deliverable proving the nucleus is filled. -/

/-- **Per-run regularity bundle** `CCanonicalRepFastGRegular Dt fuel a d` for `canonicalRepresentationFastG`:
the transparent per-node preconditions for the GENERIC `canonicalRepresentationFastG` to reconstruct
`f = a/d` at `QFunNZ` — the denominator split `cSplitFactorFastG Dt fuel d` is a regular run
(`CSplitFactorFastGRegular`), fuel exceeds the denominator `t`-degree, and the Bézout gcd of the split
parts is a nonzero constant (the coprime case). The generic mirror of `CCanonicalRepFastRegular`. -/
structure CCanonicalRepFastGRegular (Dt : CPolyG QFunNZ) (fuel : ℕ) (a d : CPolyG QFunNZ) : Prop where
  /-- `d` is nonzero. -/
  hd : toPolyG d ≠ 0
  /-- fuel exceeds the denominator `t`-degree (so `cSplitFactorFastG`/`cdivmodG` are reduced). -/
  hdeg : (toPolyG d).natDegree ≤ fuel
  /-- the denominator split is a regular `cSplitFactorFastG` run. -/
  hsplitreg : CSplitFactorFastGRegular Dt fuel d
  /-- the Bézout gcd of the split parts `(dₙ, dₛ)` is a **constant** (coprime case). -/
  hgdeg : (toPolyG (cgcdExtG fuel (CPolyG.cSplitFactorFastG Dt fuel d).1
    (CPolyG.cSplitFactorFastG Dt fuel d).2).1).natDegree = 0
  /-- the Bézout gcd is nonzero. -/
  hgne : toPolyG (cgcdExtG fuel (CPolyG.cSplitFactorFastG Dt fuel d).1
    (CPolyG.cSplitFactorFastG Dt fuel d).2).1 ≠ 0

open RatFunc in
/-- **★ Task 3 — `canonicalRepresentationFastG` reconstructs `f` at `QFunNZ`, NUCLEUS FILLED**: the probe's
generic reconstruction with the denominator-split hypothesis DISCHARGED. With the generic output
`(q, (b, dₛ), (c, dₙ)) = canonicalRepresentationFastG Dt fuel a d`, under the per-node regularity bundle
`CCanonicalRepFastGRegular`, the three pieces recombine to `f = a/d` in `RatFunc (CFieldSpec.K QFunNZ) =
RatFunc (RatFunc ℚ)` — `q + b/dₛ + c/dₙ = a/d`. The split fact the probe assumed is now supplied by
`cSplitFactorFastG_isSplittingFactorizationGen` (its `.1`), so this is the **unconditional** version. The
deliverable: with the generic `cSplitFactorFastG` correctness in hand, the whole high-level reconstruction
(and so the rest of the engine collapse at `QFunNZ`) is mechanical. -/
theorem canonicalRepresentationFastG_reconstructs_qfunNZ (Dt : CPolyG QFunNZ) (fuel : ℕ)
    (a d : CPolyG QFunNZ) (hreg : CCanonicalRepFastGRegular Dt fuel a d) :
    (let res := CPolyG.canonicalRepresentationFastG Dt fuel a d
      let q := res.1
      let b := res.2.1.1
      let ds := res.2.1.2
      let c := res.2.2.1
      let dn := res.2.2.2
      (algebraMap (CFieldSpec.K QFunNZ)[X] (RatFunc (CFieldSpec.K QFunNZ)) (toPolyG q))
          + algebraMap (CFieldSpec.K QFunNZ)[X] (RatFunc (CFieldSpec.K QFunNZ)) (toPolyG b)
              / algebraMap (CFieldSpec.K QFunNZ)[X] (RatFunc (CFieldSpec.K QFunNZ)) (toPolyG ds)
          + algebraMap (CFieldSpec.K QFunNZ)[X] (RatFunc (CFieldSpec.K QFunNZ)) (toPolyG c)
              / algebraMap (CFieldSpec.K QFunNZ)[X] (RatFunc (CFieldSpec.K QFunNZ)) (toPolyG dn)
        = algebraMap (CFieldSpec.K QFunNZ)[X] (RatFunc (CFieldSpec.K QFunNZ)) (toPolyG a)
            / algebraMap (CFieldSpec.K QFunNZ)[X] (RatFunc (CFieldSpec.K QFunNZ)) (toPolyG d)) := by
  obtain ⟨hd, hdeg, hsplitreg, hgdeg, hgne⟩ := hreg
  -- the denominator split, from the generic loop correctness
  have hsplit := cSplitFactorFastG_isSplittingFactorizationGen Dt fuel d hd hdeg hsplitreg
  have hsplit_eq : toPolyG d
      = toPolyG (CPolyG.cSplitFactorFastG Dt fuel d).2 * toPolyG (CPolyG.cSplitFactorFastG Dt fuel d).1 :=
    hsplit.1
  -- both split parts nonzero, from the split product and `d ≠ 0`
  have hsplit_dn_ne : toPolyG (CPolyG.cSplitFactorFastG Dt fuel d).1 ≠ 0 := by
    intro h0; exact hd (by rw [hsplit_eq, h0, mul_zero])
  have hsplit_ds_ne : toPolyG (CPolyG.cSplitFactorFastG Dt fuel d).2 ≠ 0 := by
    intro h0; exact hd (by rw [hsplit_eq, h0, zero_mul])
  -- discharge the probe's split hypothesis and apply it
  exact canonicalRepresentationFastG_reconstructs Dt fuel a d hd
    (fun _ _ => hsplit_eq) hsplit_dn_ne hsplit_ds_ne hgdeg hgne

/-! ### Restatements against the intended wording (anonymous `example`s) -/

-- Task 2 headline: the GENERIC fraction-free `cSplitFactorFastG` loop at `α = QFunNZ`, read over
-- ℚ(x) = `RatFunc ℚ`, returns a book-faithful splitting factorization of `toPolyG p` w.r.t. the monomial
-- derivation `Dt = toPolyG Dt` — `toPolyG p = toPolyG pₛ · toPolyG pₙ`, `pₛ` special, every squarefree
-- factor of `pₙ` normal — under the transparent per-node preconditions a real run satisfies.
example (Dt : CPolyG QFunNZ) (fuel : ℕ) (p : CPolyG QFunNZ) (hp : toPolyG p ≠ 0)
    (hdegp : (toPolyG p).natDegree ≤ fuel) (hreg : CSplitFactorFastGRegular Dt fuel p) :
    @IsSplittingFactorizationGen _ _ ⟨Differential.implicitDeriv (toPolyG Dt)⟩
      (toPolyG p)
      (toPolyG (CPolyG.cSplitFactorFastG Dt fuel p).2)
      (toPolyG (CPolyG.cSplitFactorFastG Dt fuel p).1) :=
  cSplitFactorFastG_isSplittingFactorizationGen Dt fuel p hp hdegp hreg

-- Task 3 deliverable: the generic `canonicalRepresentationFastG Dt fuel a d = (q, (b, dₛ), (c, dₙ))` at
-- `α = QFunNZ`, read over ℚ(x)(t), reconstructs `f = a/d` — `q + b/dₛ + c/dₙ = a/d` — with NO split
-- hypothesis (it is supplied internally), under the per-node regularity preconditions a real run satisfies.
example (Dt : CPolyG QFunNZ) (fuel : ℕ) (a d : CPolyG QFunNZ)
    (hreg : CCanonicalRepFastGRegular Dt fuel a d) :
    (algebraMap (CFieldSpec.K QFunNZ)[X] (RatFunc (CFieldSpec.K QFunNZ))
          (toPolyG (CPolyG.canonicalRepresentationFastG Dt fuel a d).1))
        + algebraMap (CFieldSpec.K QFunNZ)[X] (RatFunc (CFieldSpec.K QFunNZ))
              (toPolyG (CPolyG.canonicalRepresentationFastG Dt fuel a d).2.1.1)
            / algebraMap (CFieldSpec.K QFunNZ)[X] (RatFunc (CFieldSpec.K QFunNZ))
              (toPolyG (CPolyG.canonicalRepresentationFastG Dt fuel a d).2.1.2)
        + algebraMap (CFieldSpec.K QFunNZ)[X] (RatFunc (CFieldSpec.K QFunNZ))
              (toPolyG (CPolyG.canonicalRepresentationFastG Dt fuel a d).2.2.1)
            / algebraMap (CFieldSpec.K QFunNZ)[X] (RatFunc (CFieldSpec.K QFunNZ))
              (toPolyG (CPolyG.canonicalRepresentationFastG Dt fuel a d).2.2.2)
      = algebraMap (CFieldSpec.K QFunNZ)[X] (RatFunc (CFieldSpec.K QFunNZ)) (toPolyG a)
          / algebraMap (CFieldSpec.K QFunNZ)[X] (RatFunc (CFieldSpec.K QFunNZ)) (toPolyG d) :=
  canonicalRepresentationFastG_reconstructs_qfunNZ Dt fuel a d hreg

end DeepWiki.SymbolicIntegration
