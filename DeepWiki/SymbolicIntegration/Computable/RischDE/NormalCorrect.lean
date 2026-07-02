import DeepWiki.SymbolicIntegration.Computable.SoundnessCapstone

/-! # Reducing the recursive RDE residual to its weak-normalization crux

Discharges the provable clauses of `RischDESuccessResidual` for the recursive instance
(`Dt = [CField.one]`) — denominator-nonzero from the `QFunNZG β` subtype, `hyden` from the solve
guard, `hprim` from the gcd witness — and reduces `hdvdB`/`hdvdC` to two product-divisibilities
(`fden ∣ dₙh`, `gden ∣ dₙh²`), the weak-normalization precondition on the RDE input. The remainder
is bundled as `RischDESuccessResidualCrux`, with the field identity `crischDESolve_field_of_crux`. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG GBPolyCore

/-! ## The input denominator-nonzero clauses, from the `QFunNZG β` subtype invariant -/

section Nonzero

variable {β : Type*} [CField β] [CFieldSpec β]

/-- `cisZeroG p = false` gives `toPolyG p ≠ 0` — the contrapositive of `cisZeroG_iff`. -/
theorem toPolyG_ne_zero_of_cisZeroG_false {p : CPolyG β} (h : CPolyG.cisZeroG p = false) :
    toPolyG p ≠ 0 := by
  intro h0
  rw [(CPolyG.cisZeroG_iff p).mpr h0] at h
  exact absurd h (by simp)

/-- `cisZeroG p = false` gives `cnormG p ≠ []` — the list-level form of nonzero. -/
theorem cnormG_ne_nil_of_cisZeroG_false {p : CPolyG β} (h : CPolyG.cisZeroG p = false) :
    CPolyG.cnormG p ≠ [] := by
  intro he
  exact toPolyG_ne_zero_of_cisZeroG_false h ((CPolyG.cnormG_eq_nil_iff p).mp he)

/-- The denominator of a `QFunNZG β`-fraction is nonzero: `toPolyG f.1.2 ≠ 0`, from the subtype
proof `f.2 : cisZeroG f.1.2 = false`. -/
theorem qfunNZG_den_toPolyG_ne_zero (f : QFunNZG β) : toPolyG f.1.2 ≠ 0 :=
  toPolyG_ne_zero_of_cisZeroG_false f.2

/-- The denominator of a `QFunNZG β`-fraction has nonempty normal form: `cnormG f.1.2 ≠ []`. -/
theorem qfunNZG_den_cnormG_ne_nil (f : QFunNZG β) : CPolyG.cnormG f.1.2 ≠ [] :=
  cnormG_ne_nil_of_cisZeroG_false f.2

end Nonzero

/-! ## The output denominator (`hyden`), from the `crischDESolve` success guard -/

section OutputNonzero

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFieldDomain β]
  [CFracGcdCore β] [CRischField β]

/-- A successful recursive solve forces `toPolyG yden ≠ 0`: the `dif_pos` guard wrapping the inner
`cRischDEG` output pair into a `QFunNZG β` value is `cisZeroG yden = false`. Discharges the `hyden`
clause of `RischDESuccessResidual`. -/
theorem crischDESolve_yden_ne_zero (f g y : QFunNZG β)
    (hsolve : CRischField.crischDESolve f g = some y) (ynum yden : CPolyG β)
    (hsucc : cRischDEG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2 g.1.1 g.1.2
      = some (ynum, yden)) :
    toPolyG yden ≠ 0 := by
  -- the §6.1 gate passed (a `some` result), so the gated `crischDESolve` reduces to its `cRischDEG`-then-guard
  -- form (mirrors the capstone)
  have hgate : cdenomNormalGateG f = true := cdenomNormalGateG_of_crischDESolve_isSome f g y hsolve
  rw [crischDESolve_eq_solve_of_normal f g hgate] at hsolve
  rw [hsucc] at hsolve
  simp only at hsolve
  by_cases hyz : CPolyG.cisZeroG yden = false
  · exact toPolyG_ne_zero_of_cisZeroG_false hyz
  · rw [dif_neg hyz] at hsolve; exact absurd hsolve (by simp)

end OutputNonzero

/-! ## `hprim` for the recursive monomial `Dt = [CField.one]`

Under the tower-gcd witness `[CTowerGcdWitness β]`, the gcds of the unit `[1]` are units, the
`cSplitFactorFastG` step is constant, so the special part of `[1]` is the constant `[1]`. -/

section Hprim

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFracGcdCore β] [CTowerGcdWitness β]

omit [CDiffField β] [CFracGcdCore β] [CTowerGcdWitness β] in
/-- `toPolyG [CField.one] = 1`: the constant `[1]` reads as the polynomial `1`. -/
theorem toPolyG_cone_eq_one : toPolyG ([CField.one] : CPolyG β) = 1 := by
  rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_one, mul_zero, add_zero, map_one]

omit [CDiffField β] in
/-- Under the tower-gcd witness, `toPolyG (cgcdFFCore fuel [1] z)` is a unit for any `z`: the raw
gcd is `Associated` to `gcd 1 _ = 1`, and `cgcdFFCore = cmonicG ∘ raw` preserves associates. -/
theorem cgcdFFCore_one_isUnit (fuel : ℕ) (z : CPolyG β) :
    IsUnit (toPolyG (CFracGcdCore.cgcdFFCore (α := β) fuel [CField.one] z)) := by
  have hcorr := CTowerGcdWitness.gcdBCorrect (α := β) fuel [CField.one] z
  rw [toPolyG_cone_eq_one, gcd_one_left] at hcorr
  have hraw : IsUnit (toPolyG (CFracGcdCore.cgcdFFRawCore (α := β) fuel [CField.one] z)) :=
    associated_one_iff_isUnit.mp hcorr
  rw [CFracGcdCore.cgcdFFCore]
  exact (associated_toPolyG_cmonicG _).symm.isUnit hraw

omit [CDiffField β] [CFracGcdCore β] [CTowerGcdWitness β] in
/-- Division by a nonzero degree-0 divisor keeps degree 0: if `cdegG c = 0`, `cnormG d ≠ []`, and
`cdegG d = 0`, then `cdegG (cdivWf c d) = 0`. -/
theorem cdegG_cdivWf_zero_of_unit_divisor (c d : CPolyG β)
    (hc : cdegG c = 0) (hd0 : CPolyG.cnormG d ≠ []) (hd : cdegG d = 0) :
    cdegG (CPolyG.cdivWf c d) = 0 := by
  have hdlen : (CPolyG.cnormG d : List β).length = 1 := by
    rw [cdegG] at hd
    have : 0 < (CPolyG.cnormG d : List β).length := List.length_pos_iff.mpr hd0
    omega
  have hrem := CPolyG.cmodWf_length_lt c d hd0
  rw [hdlen] at hrem
  have hremnil : CPolyG.cnormG (CPolyG.cmodWf c d) = [] := List.length_eq_zero_iff.mp (by omega)
  have hrem0 : toPolyG (CPolyG.cdivmodWf c d).2 = 0 := by
    rw [show ((CPolyG.cdivmodWf c d).2) = CPolyG.cmodWf c d from rfl]
    exact (CPolyG.cnormG_eq_nil_iff _).mp hremnil
  have hid := CPolyG.toPolyG_cdivmodWf c d hd0
  rw [show CPolyG.cdivWf c d = (CPolyG.cdivmodWf c d).1 from rfl]
  rw [hrem0, add_zero] at hid
  have hdne : toPolyG d ≠ 0 := fun h => hd0 ((CPolyG.cnormG_eq_nil_iff d).mpr h)
  have hdnd0 : (toPolyG d).natDegree = 0 := by rw [← cdegG_eq_natDegree]; exact hd
  have hcnd0 : (toPolyG c).natDegree = 0 := by rw [← cdegG_eq_natDegree]; exact hc
  rw [cdegG_eq_natDegree]
  by_cases hquo0 : toPolyG (CPolyG.cdivmodWf c d).1 = 0
  · rw [hquo0]; simp
  · have hnd := congrArg Polynomial.natDegree hid
    rw [Polynomial.natDegree_mul hquo0 hdne, hdnd0, hcnd0, add_zero] at hnd
    omega

/-- The `cSplitFactorFastG` step on the unit input `[1]` has degree `0`: both gcds are units
(`cgcdFFCore_one_isUnit`), so the step is a unit-by-unit division. A constant step stops the split
recursion. -/
theorem cdegG_step_one (n : ℕ) :
    cdegG (CPolyG.cdivWf
        (CFracGcdCore.cgcdFFCore (n + 1) ([CField.one] : CPolyG β)
          (CPolyG.cmonomialDeriv [CField.one] [CField.one]))
        (CFracGcdCore.cgcdFFCore (n + 1) ([CField.one] : CPolyG β)
          (CPolyG.cderivG [CField.one]))) = 0 := by
  set g1 := CFracGcdCore.cgcdFFCore (n + 1) ([CField.one] : CPolyG β)
    (CPolyG.cmonomialDeriv [CField.one] [CField.one]) with hg1
  set g2 := CFracGcdCore.cgcdFFCore (n + 1) ([CField.one] : CPolyG β)
    (CPolyG.cderivG [CField.one]) with hg2
  have hd1 : cdegG g1 = 0 := by
    rw [hg1, cdegG_eq_natDegree]; exact natDegree_eq_zero_of_isUnit (cgcdFFCore_one_isUnit _ _)
  have hd2 : cdegG g2 = 0 := by
    rw [hg2, cdegG_eq_natDegree]; exact natDegree_eq_zero_of_isUnit (cgcdFFCore_one_isUnit _ _)
  have hg2u : IsUnit (toPolyG g2) := by rw [hg2]; exact cgcdFFCore_one_isUnit _ _
  have hg20 : CPolyG.cnormG g2 ≠ [] := by
    intro he; have hz : toPolyG g2 = 0 := (CPolyG.cnormG_eq_nil_iff g2).mp he
    rw [hz] at hg2u; exact not_isUnit_zero hg2u
  exact cdegG_cdivWf_zero_of_unit_divisor g1 g2 hd1 hg20 hd2

/-- `cSplitFactorFastG [1] fuel [1] = ([1], [1])`: the split factorization of the unit `[1]` is
trivial at every fuel (the step is constant, so the recursion never fires). -/
theorem cSplitFactorFastG_one_eq (fuel : ℕ) :
    CPolyG.cSplitFactorFastG ([CField.one] : CPolyG β) fuel [CField.one]
      = ([CField.one], [CField.one]) := by
  cases fuel with
  | zero => rfl
  | succ n => rw [CPolyG.cSplitFactorFastG, if_pos (cdegG_step_one n)]

/-- `cdegG (cSpecialPolyG [1] fuel) = 0`: the special part of the primitive monomial `[1]` is
constant, discharging the `hprim` clause of `RischDESuccessResidual` for the recursive instance. -/
theorem cdegG_cSpecialPolyG_one_eq_zero (fuel : ℕ) :
    cdegG (CPolyG.cSpecialPolyG ([CField.one] : CPolyG β) fuel) = 0 := by
  rw [CPolyG.cSpecialPolyG, cSplitFactorFastG_one_eq, cdegG_eq_natDegree]
  have hassoc := associated_toPolyG_cmonicG ([CField.one] : CPolyG β)
  rw [toPolyG_cone_eq_one] at hassoc
  exact natDegree_eq_zero_of_isUnit (associated_one_iff_isUnit.mp hassoc)

end Hprim

/-! ### Restatement -/

example {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFracGcdCore β] [CTowerGcdWitness β]
    (fuel : ℕ) : cdegG (CPolyG.cSpecialPolyG ([CField.one] : CPolyG β) fuel) = 0 :=
  cdegG_cSpecialPolyG_one_eq_zero fuel

/-! ## The divisibility clauses, reduced to the weak-normalization product-divisibilities

`cRdeNormalDenominatorG` computes the `B`/`C` clearing `cdivWf` unconditionally, so `hdvdB`/`hdvdC`
are not self-certified by a `some` result. Each reduces to a single product-divisibility of the
denominator into the normal-part·`h` block (`fden ∣ dₙh`, `gden ∣ dₙh²`) — the weak-normalization
precondition on the RDE input, which the recursive `crischDESolve` does not establish for a raw
argument. -/

section Divisibility

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFracGcdCore β]

omit [CDiffFieldSpec β] in
/-- If `fden ∣ dₙ·h0` (`dₙ = (cSplitFactorFastG Dt fuel fden).1`), then `fden` divides the full
`B`-numerator `dₙh·fnum − dₙ·Dh·fden` — the sufficient condition for the `cdivWf` `B`-clearing to
be exact. -/
theorem hdvdB_of_dvd (Dt : CPolyG β) (fuel : ℕ) (fnum fden h0 : CPolyG β)
    (hdvd : toPolyG fden ∣ toPolyG (CPolyG.cmulG (CPolyG.cSplitFactorFastG Dt fuel fden).1 h0)) :
    toPolyG fden ∣ toPolyG (CPolyG.csubG
        (CPolyG.cmulG (CPolyG.cmulG (CPolyG.cSplitFactorFastG Dt fuel fden).1 h0) fnum)
        (CPolyG.cmulG (CPolyG.cmulG (CPolyG.cSplitFactorFastG Dt fuel fden).1
          (CPolyG.cmonomialDeriv Dt h0)) fden)) := by
  simp only [CPolyG.toPolyG_csubG, CPolyG.toPolyG_cmulG]
  apply dvd_sub
  · rw [CPolyG.toPolyG_cmulG] at hdvd
    exact hdvd.mul_right _
  · exact Dvd.intro_left _ rfl

omit [CDiffFieldSpec β] in
/-- If `gden ∣ dₙ·h0·h0`, then `gden` divides the full `C`-numerator `dₙh²·gnum` — the sufficient
condition for the `cdivWf` `C`-clearing to be exact. -/
theorem hdvdC_of_dvd (Dt : CPolyG β) (fuel : ℕ) (gnum fden gden h0 : CPolyG β)
    (hdvd : toPolyG gden ∣ toPolyG (CPolyG.cmulG
      (CPolyG.cmulG (CPolyG.cSplitFactorFastG Dt fuel fden).1 h0) h0)) :
    toPolyG gden ∣ toPolyG (CPolyG.cmulG
        (CPolyG.cmulG (CPolyG.cmulG (CPolyG.cSplitFactorFastG Dt fuel fden).1 h0) h0) gnum) := by
  simp only [denote] at hdvd ⊢
  exact hdvd.mul_right _

/-! ### When the `B`-divisibility is free: normal or polynomial denominators -/

omit [CDiffFieldSpec β] in
/-- `fden ∣ dₙh` holds when `fden` equals its own normal part
(`toPolyG (cSplitFactorFastG Dt fuel fden).1 = toPolyG fden`, i.e. `fden` weakly normalized). -/
theorem dvd_dn_h_of_normal (Dt : CPolyG β) (fuel : ℕ) (fden h0 : CPolyG β)
    (hnormal : toPolyG (CPolyG.cSplitFactorFastG Dt fuel fden).1 = toPolyG fden) :
    toPolyG fden ∣ toPolyG (CPolyG.cmulG (CPolyG.cSplitFactorFastG Dt fuel fden).1 h0) := by
  rw [CPolyG.toPolyG_cmulG, hnormal]; exact Dvd.intro _ rfl

omit [CDiffFieldSpec β] in
/-- `fden ∣ dₙh` holds for the polynomial-RDE shape `fden = [1]`: the normal part of the unit `[1]`
is `[1]`, so the divisibility is `1 ∣ _`. -/
theorem dvd_dn_h_one [CTowerGcdWitness β] (fuel : ℕ) (h0 : CPolyG β) :
    toPolyG ([CField.one] : CPolyG β)
      ∣ toPolyG (CPolyG.cmulG
        (CPolyG.cSplitFactorFastG ([CField.one] : CPolyG β) fuel [CField.one]).1 h0) := by
  rw [cSplitFactorFastG_one_eq, CPolyG.toPolyG_cmulG, toPolyG_cone_eq_one]; exact one_dvd _

end Divisibility

/-! ## The reduced crux residual, its builder, and the field corollary -/

section Crux

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
  [CFracGcdCore β] [CRischField β] [CTowerGcdWitness β]

/-- The reduced RDE residual crux `RischDESuccessResidualCrux f g`: the clauses of
`RischDESuccessResidual` that remain after the discharges of this file — per normal-denominator
output `(a0,b0,c0,h0)`, the weak-normalization product-divisibilities `hdvdB_dn_h` (`fden ∣ dₙh`)
and `hdvdC_dn_h2` (`gden ∣ dₙh²`), the normal-part-nonzero `hdn`, and the non-gcd
`CSPDEGClearedInputsGen` chain `hin`; plus the dispatcher side-condition `hdb`. -/
structure RischDESuccessResidualCrux (f g : QFunNZG β) : Prop where
  /-- The normal part `dₙ = (cSplitFactorFastG [1] _ fden).1` of `fden` is nonzero. -/
  hdn : ∀ a0 b0 c0 h0 : CPolyG β,
    cRdeNormalDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2 g.1.1 g.1.2
        = some (a0, b0, c0, h0) →
      toPolyG (CPolyG.cSplitFactorFastG ([CField.one] : CPolyG β) towerRischDEFuel f.1.2).1 ≠ 0
  /-- §6.1 weak-normalization `B`-divisibility: `fden ∣ dₙ·h0`. -/
  hdvdB_dn_h : ∀ a0 b0 c0 h0 : CPolyG β,
    cRdeNormalDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2 g.1.1 g.1.2
        = some (a0, b0, c0, h0) →
      toPolyG f.1.2 ∣ toPolyG (CPolyG.cmulG
        (CPolyG.cSplitFactorFastG ([CField.one] : CPolyG β) towerRischDEFuel f.1.2).1 h0)
  /-- §6.1 weak-normalization `C`-divisibility: `gden ∣ dₙ·h0²`. -/
  hdvdC_dn_h2 : ∀ a0 b0 c0 h0 : CPolyG β,
    cRdeNormalDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2 g.1.1 g.1.2
        = some (a0, b0, c0, h0) →
      toPolyG g.1.2 ∣ toPolyG (CPolyG.cmulG (CPolyG.cmulG
        (CPolyG.cSplitFactorFastG ([CField.one] : CPolyG β) towerRischDEFuel f.1.2).1 h0) h0)
  /-- The §6.4 per-level transparent-input chain `CSPDEGClearedInputsGen` (gcd clauses via the witness). -/
  hin : ∀ a0 b0 c0 h0 : CPolyG β,
    cRdeNormalDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2 g.1.1 g.1.2
        = some (a0, b0, c0, h0) →
      CSPDEGClearedInputsGen ([CField.one] : CPolyG β) towerRischDEFuel
        (cRdeSpecialDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel a0 b0 c0).1
        (cRdeSpecialDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel a0 b0 c0).2.1
        (cRdeSpecialDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel a0 b0 c0).2.2.1
        (cRdeBoundDegreeG ([CField.one] : CPolyG β)
          (cRdeSpecialDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel a0 b0 c0).1
          (cRdeSpecialDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel a0 b0 c0).2.1
          (cRdeSpecialDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel a0 b0 c0).2.2.1 : ℤ)
  /-- The positive-`deg(bbar)` dispatcher side-condition (Lemma 6.5.1 non-cancellation routing). -/
  hdb : ∀ a0 b0 c0 bbar cbar : CPolyG β, ∀ m : ℤ, ∀ α' β' : CPolyG β,
    cSPDEG ([CField.one] : CPolyG β) towerRischDEFuel
        (cRdeSpecialDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel a0 b0 c0).1
        (cRdeSpecialDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel a0 b0 c0).2.1
        (cRdeSpecialDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel a0 b0 c0).2.2.1
        (cRdeBoundDegreeG ([CField.one] : CPolyG β)
          (cRdeSpecialDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel a0 b0 c0).1
          (cRdeSpecialDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel a0 b0 c0).2.1
          (cRdeSpecialDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel a0 b0 c0).2.2.1 : ℤ)
      = some (bbar, cbar, m, α', β') → 0 < cdegG bbar

omit [CDiffFieldSpec β] in
/-- A successful recursive solve plus the reduced crux `RischDESuccessResidualCrux f g` rebuilds the
full `RischDESuccessResidual f g`: `hprim` from `cdegG_cSpecialPolyG_one_eq_zero`, `hyden` from
`crischDESolve_yden_ne_zero`, the denominator clauses from the subtype, and `hdvdB`/`hdvdC` via
`hdvdB_of_dvd`/`hdvdC_of_dvd`. -/
theorem residual_of_crux (f g y : QFunNZG β)
    (hsolve : CRischField.crischDESolve f g = some y)
    (hcrux : RischDESuccessResidualCrux f g) :
    RischDESuccessResidual f g where
  hres a0 b0 c0 h0 hnorm := {
    hprim := cdegG_cSpecialPolyG_one_eq_zero towerRischDEFuel
    hdn := hcrux.hdn a0 b0 c0 h0 hnorm
    hfden0 := qfunNZG_den_cnormG_ne_nil f
    hgden0 := qfunNZG_den_cnormG_ne_nil g
    hdvdB := hdvdB_of_dvd ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2 h0
      (hcrux.hdvdB_dn_h a0 b0 c0 h0 hnorm)
    hdvdC := hdvdC_of_dvd ([CField.one] : CPolyG β) towerRischDEFuel g.1.1 f.1.2 g.1.2 h0
      (hcrux.hdvdC_dn_h2 a0 b0 c0 h0 hnorm)
    hin := hcrux.hin a0 b0 c0 h0 hnorm
  }
  hdb := hcrux.hdb
  hyden ynum yden hsucc := crischDESolve_yden_ne_zero f g y hsolve ynum yden hsucc
  hfden := qfunNZG_den_toPolyG_ne_zero f
  hgden := qfunNZG_den_toPolyG_ne_zero g

section FieldCorollary

variable [Algebra ℚ (CFieldSpec.K β)]

/-- The recursive RDE-oracle field identity from the reduced crux: a successful solve
`crischDESolve f g = some y` over `QFunNZG β`, with `[CTowerGcdWitness β]` and
`RischDESuccessResidualCrux f g`, yields `towerFractionFieldDerivG [1] Y + F·Y = G` over
`RatFunc (CFieldSpec.K β)` (`Y = amG y.1.1/amG y.1.2`, etc.). Composes `residual_of_crux` with the
capstone `crischDESolve_field_of_witness_residual`; no `native_decide`. -/
theorem crischDESolve_field_of_crux (f g y : QFunNZG β)
    (hsolve : CRischField.crischDESolve f g = some y)
    (hcrux : RischDESuccessResidualCrux f g) :
    towerFractionFieldDerivG ([CField.one] : CPolyG β)
          (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
        + amG β (toPolyG f.1.1) / amG β (toPolyG f.1.2)
          * (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
      = amG β (toPolyG g.1.1) / amG β (toPolyG g.1.2) :=
  crischDESolve_field_of_witness_residual f g y hsolve (residual_of_crux f g y hsolve hcrux)

end FieldCorollary

end Crux

/-! ### Restatement -/

example {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
    [CFracGcdCore β] [CRischField β] [CTowerGcdWitness β] [Algebra ℚ (CFieldSpec.K β)]
    (f g y : QFunNZG β) (hsolve : CRischField.crischDESolve f g = some y)
    (hcrux : RischDESuccessResidualCrux f g) :
    towerFractionFieldDerivG ([CField.one] : CPolyG β)
          (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
        + amG β (toPolyG f.1.1) / amG β (toPolyG f.1.2)
          * (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
      = amG β (toPolyG g.1.1) / amG β (toPolyG g.1.2) :=
  crischDESolve_field_of_crux f g y hsolve hcrux

/-! ## ★ VERDICT — is the recursive `CRischFieldSpec (QFunNZG β)` now UNCONDITIONAL?

**No — but the residual is now SHARP and most of it is discharged.** The recursive RDE-oracle field identity
holds for a successful `crischDESolve f g = some y` over `QFunNZG β` modulo exactly the reduced crux
`RischDESuccessResidualCrux` (`crischDESolve_field_of_crux`), which is strictly smaller than the prior
`RischDESuccessResidual`: this file discharges six of its clauses and reduces two more.

### What is now DISCHARGED (axiom-clean `[propext, Classical.choice, Quot.sound]`, NO `native_decide`)

* **`hprim`** (`cdegG_cSpecialPolyG_one_eq_zero`) — a theorem for the recursive monomial `Dt = [1]`, via the
  gcd witness (the gcd of the unit `[1]` is a unit ⟹ the split of `[1]` is trivial ⟹ the special part is the
  constant `[1]`). NOT "true by construction" cheaply — it genuinely uses `CTowerGcdWitness β`.
* **`hyden`** (`crischDESolve_yden_ne_zero`) — from the `cisZeroG yden = false` guard a successful
  `crischDESolve` already passes.
* **`hfden`/`hgden`/`hfden0`/`hgden0`** (`qfunNZG_den_*`) — from the `QFunNZG β` subtype proof.
* **`hdvdB`/`hdvdC`** REDUCED (`hdvdB_of_dvd`/`hdvdC_of_dvd`) to the single product-divisibilities
  `fden ∣ dₙh` and `gden ∣ dₙh²` — the algebraic essence of §6.1 weak normalization.

### The SHARPENED TRUE residual (the precise remaining crux, in `RischDESuccessResidualCrux`)

1. **The §6.1 weak-normalization product-divisibilities** `hdvdB_dn_h` (`fden ∣ dₙh`) and `hdvdC_dn_h2`
   (`gden ∣ dₙh²`). These are the **crux**, and they are genuinely NOT theorems for arbitrary `f g`: with
   `fden = dₙ·dₛ` (normal × special), `fden ∣ dₙh ⟺ dₛ ∣ h`, which FAILS for an un-weakly-normalized `f`
   (e.g. `dₛ` a nontrivial special factor coprime to `h`). They hold for the **post-Hermite,
   weakly-normalized** RDE input the algorithm assumes; the recursive `crischDESolve` does NOT weak-normalize
   its raw argument (`cWeakNormalizerG` is the missing pre-step), so the engine computes the `cdivWf` clearing
   unconditionally and never re-validates exactness. **This is the genuine obstruction — a missing
   precondition, NOT engine self-certification.**
2. **`hdn`** (normal part nonzero) — rests on the splitting-factorization product `fden = dₙ·dₛ`, which
   `cSplitFactorFastG` is documented not to establish abstractly (`ComputableTowerUnify`); per-run regularity.
3. **The non-gcd `CSPDEGClearedInputsGen` chain** `hin`
   (per-level fuel, `cdvdG`, `cgcdTerminatesG`) — per-run termination/fuel, NOT unconditional (the gcd
   clauses *inside* `hin` ARE supplied by `CTowerGcdWitness β`; only the non-gcd ones remain).
4. **`hdb`** (positive `deg(bbar)`) — the dispatcher routing side-condition.

### Bottom line — is the wall illusory?

**Partly.** The user's two hints were *almost* right and the file acts on them: `hprim` IS dischargeable
(hint 1 — though it needs the gcd witness, not "construction"); the §6.2 divisibility IS the weak-normalization
invariant (hint 2). But the divisibility is **not** "a theorem of weak-normalization the engine produces by
construction" — the engine does NOT weak-normalize, so for the recursive instance (raw `f`) the divisibility
is a genuine **precondition** that can fail. The TRUE residual is therefore the **§6.1 weak-normalization
product-divisibilities** (`hdvdB_dn_h`/`hdvdC_dn_h2`) plus per-run termination/fuel — sharper than the prior
"self-certification wall", and reachable only by *adding the `cWeakNormalizerG` pre-step to the recursive
`crischDESolve`* (an engine change, out of this file's scope) or by carrying the crux as the residual. The
recursive `CRischFieldSpec (QFunNZG β)` is **not** unconditional; the boundary is now exactly the named crux. -/

/-! ### Axiom audit (the discharges + the crux corollary are axiom-clean, NO `native_decide`) -/

#print axioms cdegG_cSpecialPolyG_one_eq_zero
#print axioms crischDESolve_yden_ne_zero
#print axioms hdvdB_of_dvd
#print axioms hdvdC_of_dvd
#print axioms residual_of_crux
#print axioms crischDESolve_field_of_crux

end DeepWiki.SymbolicIntegration
