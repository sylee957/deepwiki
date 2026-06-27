import DeepWiki.SymbolicIntegration.ComputableSoundnessCapstone

/-! # Discharging the recursive RDE residual `RischDESuccessResidual` — what falls, and the sharpened crux

`ComputableSoundnessCapstone.crischDESolve_field_of_witness_residual` closes the recursive RDE-oracle field
identity over `QFunNZG β` *up to* the explicit `RischDESuccessResidual` bundle. This file re-attacks that
bundle clause by clause for the recursive instance (`Dt = [CField.one]`, the primitive monomial), separating
the clauses that are genuine theorems from those that are a real precondition the recursive oracle does not
establish — sharpening the prior "self-certification wall" into its precise mathematical content.

* **The denominator-nonzero clauses are theorems**: `hfden`/`hgden` and the `cnormG _ ≠ []` clauses
  `hfden0`/`hgden0` come directly from the `QFunNZG β` subtype proof `cisZeroG _ = false`; `hyden` comes
  from the `cisZeroG yden = false` guard a successful `crischDESolve` already passes
  (`crischDESolve_yden_ne_zero`).
* **The §6.2 divisibility / fuel / `CSPDEGClearedInputsGen` clauses are NOT theorems for arbitrary `f g`**
  (the sharpened crux): `hdvdB`/`hdvdC` (`fden ∣ B`, `gden ∣ C`) are the **weak-normalization invariant** of
  Bronstein §6.1–§6.2 — they hold for the *post-Hermite, weakly-normalized* RDE input, but the recursive
  `crischDESolve` feeds its raw argument straight into `cRischDEG` without weak-normalizing it, and the engine
  computes the clearing `cdivG` unconditionally (truncating on non-divisibility). `hdn` likewise rests on the
  splitting-factorization product `fden = dₙ·dₛ`, which `cSplitFactorFastG` is documented not to establish
  abstractly. The fuel bounds (`hfbB`/`hfbC`) and the non-gcd `CSPDEGClearedInputsGen` clauses are per-run
  regularity. So the recursive `RischDESuccessResidual` is **not** an unconditional `∀ f g` — its precise true
  content is the §6.1 weak-normalization precondition plus per-run termination/fuel, NOT engine
  self-certification.

The verdict at the end states precisely which clauses fall and why the rest is a genuine precondition. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG GBPolyCore

/-! ## The denominator-nonzero clauses (`hfden`/`hgden`/`hfden0`/`hgden0`/`hyden`) — genuine theorems

These four-plus-one clauses of `RischDESuccessResidual` are NOT part of the crux: they follow from the
`QFunNZG β` subtype invariant `cisZeroG _ = false` (for the input denominators `f.1.2`, `g.1.2`) and from the
`cisZeroG yden = false` guard a successful `crischDESolve` passes (for the output denominator). We discharge
all of them here. -/

section Nonzero

variable {β : Type*} [CField β] [CFieldSpec β]

/-- **`cisZeroG p = false` reads as `toPolyG p ≠ 0`** — the contrapositive of `cisZeroG_iff`. The bridge
turning the `QFunNZG β` subtype's denominator-nonzero proof into the `≠ 0` polynomial fact the field bridge
wants. -/
theorem toPolyG_ne_zero_of_cisZeroG_false {p : CPolyG β} (h : CPolyG.cisZeroG p = false) :
    toPolyG p ≠ 0 := by
  intro h0
  rw [(CPolyG.cisZeroG_iff p).mpr h0] at h
  exact absurd h (by simp)

/-- **`cisZeroG p = false` gives `cnormG p ≠ []`** — the list-level form of denominator-nonzero. From
`toPolyG_ne_zero_of_cisZeroG_false` via `cnormG_eq_nil_iff`. -/
theorem cnormG_ne_nil_of_cisZeroG_false {p : CPolyG β} (h : CPolyG.cisZeroG p = false) :
    CPolyG.cnormG p ≠ [] := by
  intro he
  exact toPolyG_ne_zero_of_cisZeroG_false h ((CPolyG.cnormG_eq_nil_iff p).mp he)

/-- **The input denominator of a `QFunNZG β`-fraction is nonzero** (`hfden`/`hgden`): for `f : QFunNZG β`,
`toPolyG f.1.2 ≠ 0` — directly from the subtype proof `f.2 : cisZeroG f.1.2 = false`. -/
theorem qfunNZG_den_toPolyG_ne_zero (f : QFunNZG β) : toPolyG f.1.2 ≠ 0 :=
  toPolyG_ne_zero_of_cisZeroG_false f.2

/-- **The input denominator of a `QFunNZG β`-fraction has nonempty normal form** (`hfden0`/`hgden0`):
`cnormG f.1.2 ≠ []` — from the subtype proof. -/
theorem qfunNZG_den_cnormG_ne_nil (f : QFunNZG β) : CPolyG.cnormG f.1.2 ≠ [] :=
  cnormG_ne_nil_of_cisZeroG_false f.2

end Nonzero

/-! ## The output denominator (`hyden`) — from the `crischDESolve` success guard

A successful recursive solve `crischDESolve f g = some y` unfolds (over `QFunNZG β`,
`instCRischFieldQFunNZG`) to `cRischDEG [1] fuel f.1.1 f.1.2 g.1.1 g.1.2 = some (ynum, yden)` *together with*
the boolean guard `cisZeroG yden = false` (the `dif_pos` branch that wraps the pair into the `QFunNZG β`
output). So the output denominator `yden` is nonzero — `hyden` is forced by the success, not a residual. -/

section OutputNonzero

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFieldDomain β]
  [CFracGcdCore β] [CRischField β]

/-- **A successful recursive solve forces `cisZeroG yden = false`** (and hence `toPolyG yden ≠ 0`): if
`crischDESolve f g = some y` over `QFunNZG β` and the inner oracle returned `(ynum, yden)`, then the boolean
guard wrapping the pair into the `QFunNZG β` output was `cisZeroG yden = false`, so `toPolyG yden ≠ 0`. This
discharges the `hyden` clause of `RischDESuccessResidual` from the bare success — no residual. -/
theorem crischDESolve_yden_ne_zero (f g y : QFunNZG β)
    (hsolve : CRischField.crischDESolve f g = some y) (ynum yden : CPolyG β)
    (hsucc : cRischDEG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2 g.1.1 g.1.2
      = some (ynum, yden)) :
    toPolyG yden ≠ 0 := by
  -- unfold the recursive `crischDESolve` to its `cRischDEG`-then-guard form (mirrors the capstone)
  rw [show CRischField.crischDESolve f g
      = (match cRischDEG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2 g.1.1 g.1.2 with
         | none => none
         | some (ynum, yden) =>
           if h : CPolyG.cisZeroG yden = false then some ⟨(ynum, yden), h⟩ else none) from rfl] at hsolve
  rw [hsucc] at hsolve
  simp only at hsolve
  by_cases hyz : CPolyG.cisZeroG yden = false
  · exact toPolyG_ne_zero_of_cisZeroG_false hyz
  · rw [dif_neg hyz] at hsolve; exact absurd hsolve (by simp)

end OutputNonzero

/-! ## Task 1 — `hprim` for the recursive monomial `Dt = [CField.one]` (using the gcd witness)

`hprim` asks `cdegG (cSpecialPolyG Dt fuel) = 0` (the primitive special regime). For the recursive instance
`Dt = [CField.one]` the monomial is primitive, so its special part is the constant `[1]`. This is **not**
"true by construction" cheaply: `cSpecialPolyG [1] fuel = cmonicG (cSplitFactorFastG [1] fuel [1]).2`, and the
`cSplitFactorFastG` step computes `S = cdivG (cgcdFFCore [1] (cmonomialDeriv [1] [1])) (cgcdFFCore [1]
(cderivG [1]))` whose first gcd argument is the unit `[1]` but whose degree we can only pin via the gcd
correctness. With the tower-gcd witness `[CTowerGcdWitness β]` in hand (the same witness the capstone already
carries), the gcd of the unit `[1]` is associated to `gcd 1 _ = 1`, hence a unit of degree `0`; the step `S`
is then a constant, the `cSplitFactorFastG` recursion never fires, and the special part is `[1]`. So `hprim`
**is** a theorem for the recursive instance — given the gcd witness. -/

section Hprim

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFracGcdCore β] [CTowerGcdWitness β]

omit [CDiffField β] [CFracGcdCore β] [CTowerGcdWitness β] in
/-- **`toPolyG [CField.one] = 1`** — the constant `[1]` reads as the polynomial `1`. -/
theorem toPolyG_cone_eq_one : toPolyG ([CField.one] : CPolyG β) = 1 := by
  rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_one, mul_zero, add_zero, map_one]

omit [CDiffField β] in
/-- **The public tower gcd of the unit `[1]` is a unit** (`cgcdFFCore_one_isUnit`): under the tower-gcd
witness, `toPolyG (cgcdFFCore fuel [1] z)` is a unit for any `z`. The raw gcd is `Associated` to
`gcd (toPolyG [1]) (toPolyG z) = gcd 1 _ = 1` (`CTowerGcdWitness.gcdBCorrect` + `gcd_one_left`), so it is a
unit; `cgcdFFCore = cmonicG ∘ raw` is `Associated` to the raw via `associated_toPolyG_cmonicG`, hence also a
unit. -/
theorem cgcdFFCore_one_isUnit (fuel : ℕ) (z : CPolyG β) :
    IsUnit (toPolyG (CFracGcdCore.cgcdFFCore (α := β) fuel [CField.one] z)) := by
  have hcorr := CTowerGcdWitness.gcdBCorrect (α := β) fuel [CField.one] z
  rw [toPolyG_cone_eq_one, gcd_one_left] at hcorr
  have hraw : IsUnit (toPolyG (CFracGcdCore.cgcdFFRawCore (α := β) fuel [CField.one] z)) :=
    associated_one_iff_isUnit.mp hcorr
  rw [CFracGcdCore.cgcdFFCore]
  exact (associated_toPolyG_cmonicG _).symm.isUnit hraw

omit [CDiffField β] [CFracGcdCore β] [CTowerGcdWitness β] in
/-- **Division by a degree-0 unit divisor keeps degree 0**: if `cdegG c = 0`, `d` is nonzero of degree `0`,
and the fuel covers `c`, then `cdegG (cdivG fuel c d) = 0`. The unit divisor has normalized length `1`, so the
Euclidean remainder is properly reduced to length `< 1`, i.e. `0` (`cmodG_length_lt`); the division identity
`c = q·d + 0` then forces `natDegree q = natDegree c − natDegree d = 0`. -/
theorem cdegG_cdivG_zero_of_unit_divisor (fuel : ℕ) (c d : CPolyG β)
    (hc : cdegG c = 0) (hd0 : CPolyG.cnormG d ≠ []) (hd : cdegG d = 0)
    (hfuel : (CPolyG.cnormG c : List β).length ≤ fuel) :
    cdegG (CPolyG.cdivG fuel c d) = 0 := by
  have hdlen : (CPolyG.cnormG d : List β).length = 1 := by
    rw [cdegG] at hd
    have : 0 < (CPolyG.cnormG d : List β).length := List.length_pos_iff.mpr hd0
    omega
  have hrem := CPolyG.cmodG_length_lt fuel c d hd0 hfuel
  rw [hdlen] at hrem
  have hremnil : CPolyG.cnormG (CPolyG.cmodG fuel c d) = [] := List.length_eq_zero_iff.mp (by omega)
  have hrem0 : toPolyG (CPolyG.cdivmodG fuel c d).2 = 0 := by
    rw [show ((CPolyG.cdivmodG fuel c d).2) = CPolyG.cmodG fuel c d from rfl]
    exact (CPolyG.cnormG_eq_nil_iff _).mp hremnil
  have hid := CPolyG.toPolyG_cdivmodG' fuel c d hd0
  rw [show CPolyG.cdivG fuel c d = (CPolyG.cdivmodG fuel c d).1 from rfl]
  rw [hrem0, add_zero] at hid
  have hdne : toPolyG d ≠ 0 := fun h => hd0 ((CPolyG.cnormG_eq_nil_iff d).mpr h)
  have hdnd0 : (toPolyG d).natDegree = 0 := by rw [← cdegG_eq_natDegree]; exact hd
  have hcnd0 : (toPolyG c).natDegree = 0 := by rw [← cdegG_eq_natDegree]; exact hc
  rw [cdegG_eq_natDegree]
  by_cases hquo0 : toPolyG (CPolyG.cdivmodG fuel c d).1 = 0
  · rw [hquo0]; simp
  · have hnd := congrArg Polynomial.natDegree hid
    rw [Polynomial.natDegree_mul hquo0 hdne, hdnd0, hcnd0, add_zero] at hnd
    omega

/-- **The `cSplitFactorFastG` step value is constant on the unit input `[1]`** (`cdegG_step_one`): the step
`S = cdivG (cgcdFFCore [1] (cmonomialDeriv [1] [1])) (cgcdFFCore [1] (cderivG [1]))` has degree `0`. Both
gcds are units (`cgcdFFCore_one_isUnit`), so `S` is a unit-by-unit division — degree `0`
(`cdegG_cdivG_zero_of_unit_divisor`). The step never being non-constant is what stops the split recursion. -/
theorem cdegG_step_one (n : ℕ) :
    cdegG (CPolyG.cdivG (n + 1)
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
  have hfuel : (CPolyG.cnormG g1 : List β).length ≤ n + 1 := by
    rw [cdegG] at hd1; omega
  exact cdegG_cdivG_zero_of_unit_divisor (n + 1) g1 g2 hd1 hg20 hd2 hfuel

/-- **The split factorization of `[1]` is trivial** (`cSplitFactorFastG_one_eq`): `cSplitFactorFastG [1] fuel
[1] = ([1], [1])`. At fuel `0` it is `([1], [1])` definitionally; at `fuel+1` the step `S` is constant
(`cdegG_step_one`), so the `if cdegG S = 0` branch fires and returns `([1], [1])` without recursing. -/
theorem cSplitFactorFastG_one_eq (fuel : ℕ) :
    CPolyG.cSplitFactorFastG ([CField.one] : CPolyG β) fuel [CField.one]
      = ([CField.one], [CField.one]) := by
  cases fuel with
  | zero => rfl
  | succ n => rw [CPolyG.cSplitFactorFastG, if_pos (cdegG_step_one n)]

/-- **★ `hprim` for the recursive monomial** (`cdegG_cSpecialPolyG_one_eq_zero`): `cdegG (cSpecialPolyG [1]
fuel) = 0`. The special part of the primitive monomial `[1]` is `cmonicG (cSplitFactorFastG [1] fuel [1]).2 =
cmonicG [1]` (`cSplitFactorFastG_one_eq`), which is `Associated` to `[1]` (`toPolyG = 1`, a unit), hence of
degree `0`. The `hprim` clause of `RischDESuccessResidual` is a theorem for the recursive instance — discharged
from the gcd witness, NOT carried as a residual. -/
theorem cdegG_cSpecialPolyG_one_eq_zero (fuel : ℕ) :
    cdegG (CPolyG.cSpecialPolyG ([CField.one] : CPolyG β) fuel) = 0 := by
  rw [CPolyG.cSpecialPolyG, cSplitFactorFastG_one_eq, cdegG_eq_natDegree]
  have hassoc := associated_toPolyG_cmonicG ([CField.one] : CPolyG β)
  rw [toPolyG_cone_eq_one] at hassoc
  exact natDegree_eq_zero_of_isUnit (associated_one_iff_isUnit.mp hassoc)

end Hprim

/-! ### Restatement against the intended wording (anonymous `example`) -/

-- ★ Task 1: the primitive-regime clause `hprim` is a theorem for the recursive monomial `Dt = [1]`,
-- given the gcd witness.
example {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFracGcdCore β] [CTowerGcdWitness β]
    (fuel : ℕ) : cdegG (CPolyG.cSpecialPolyG ([CField.one] : CPolyG β) fuel) = 0 :=
  cdegG_cSpecialPolyG_one_eq_zero fuel

/-! ## ★ Task 3 — the §6.2 divisibility crux: reduced to the weak-normalization product-divisibilities

`hdvdB`/`hdvdC` are the two clauses a bare `cRischDEG … = some _` does NOT self-certify, because
`cRdeNormalDenominatorG` computes the `B`/`C` clearing `cdivG` **unconditionally** (it checks only one
`cdvdG`, on `en ∣ dₙh²`, before returning `some` — never the `fden ∣ B` / `gden ∣ C` exactness the cleared
identity needs). We make their precise content explicit: each reduces to a single product-divisibility of the
*denominator* into the `normal-part·h` block — the algebraic essence of Bronstein §6.1 **weak normalization**.

With `dₙ = (cSplitFactorFastG Dt fuel fden).1` the normal part of `fden`:

* `hdvdB` (`fden ∣ B = dₙh·fnum − dₙ·Dh·fden`) follows from `fden ∣ dₙh` — the `−dₙ·Dh·fden` summand is
  divisible by `fden` outright, and `fden ∣ dₙh ⟹ fden ∣ dₙh·fnum` (`hdvdB_of_dvd`).
* `hdvdC` (`gden ∣ C = dₙh²·gnum`) follows from `gden ∣ dₙh²` (`hdvdC_of_dvd`).

So the §6.2 divisibility crux is **exactly** these two product-divisibilities — NOT engine self-certification,
but the genuine §6.1 weak-normalization precondition on the (raw, un-normalized) RDE input. For a
**weakly-normalized** `f` (the post-Hermite RDE input the algorithm assumes) the normal part absorbs the
denominator and both hold; the recursive `crischDESolve` does not weak-normalize its argument, so they are NOT
unconditional in `f g`. These are the sharpened TRUE residual. -/

section Divisibility

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFracGcdCore β]

omit [CDiffFieldSpec β] in
/-- **`hdvdB` reduces to `fden ∣ dₙh`** (the §6.2 `B`-divisibility essence): if the denominator `fden`
divides the normal-part·h block `dₙ·h0` (`dₙ = (cSplitFactorFastG Dt fuel fden).1`), then it divides the full
`B`-numerator `dₙh·fnum − dₙ·Dh·fden`. The second summand is `fden`-divisible outright; the first is
`(dₙh)·fnum`, divisible by `fden` from the hypothesis. The clean sufficient condition for the `cdivG`
`B`-clearing to be exact. -/
theorem hdvdB_of_dvd (Dt : CPolyG β) (fuel : ℕ) (fnum fden h0 : CPolyG β)
    (hdvd : toPolyG fden ∣ toPolyG (CPolyG.cmulG (CPolyG.cSplitFactorFastG Dt fuel fden).1 h0)) :
    toPolyG fden ∣ toPolyG (CPolyG.csubG
        (CPolyG.cmulG (CPolyG.cmulG (CPolyG.cSplitFactorFastG Dt fuel fden).1 h0) fnum)
        (CPolyG.cmulG (CPolyG.cmulG (CPolyG.cSplitFactorFastG Dt fuel fden).1
          (CPolyG.cmonomialDeriv Dt h0)) fden)) := by
  rw [CPolyG.toPolyG_csubG, CPolyG.toPolyG_cmulG, CPolyG.toPolyG_cmulG, CPolyG.toPolyG_cmulG,
    CPolyG.toPolyG_cmulG]
  apply dvd_sub
  · rw [CPolyG.toPolyG_cmulG] at hdvd
    exact hdvd.mul_right _
  · exact Dvd.intro_left _ rfl

omit [CDiffFieldSpec β] in
/-- **`hdvdC` reduces to `gden ∣ dₙh²`** (the §6.2 `C`-divisibility essence): if the denominator `gden`
divides the normal-part·h² block `dₙ·h0·h0` (`dₙ = (cSplitFactorFastG Dt fuel fden).1`), then it divides the
full `C`-numerator `dₙh²·gnum`. Multiplying the hypothesis by `gnum`. The clean sufficient condition for the
`cdivG` `C`-clearing to be exact. -/
theorem hdvdC_of_dvd (Dt : CPolyG β) (fuel : ℕ) (gnum fden gden h0 : CPolyG β)
    (hdvd : toPolyG gden ∣ toPolyG (CPolyG.cmulG
      (CPolyG.cmulG (CPolyG.cSplitFactorFastG Dt fuel fden).1 h0) h0)) :
    toPolyG gden ∣ toPolyG (CPolyG.cmulG
        (CPolyG.cmulG (CPolyG.cmulG (CPolyG.cSplitFactorFastG Dt fuel fden).1 h0) h0) gnum) := by
  rw [CPolyG.toPolyG_cmulG]
  rw [CPolyG.toPolyG_cmulG, CPolyG.toPolyG_cmulG] at hdvd ⊢
  exact hdvd.mul_right _

/-! ### When the `B`-divisibility crux VANISHES — normal / polynomial denominators

The `B`-divisibility `fden ∣ dₙh` is the crux's essence; here is exactly when it is *free*. -/

omit [CDiffFieldSpec β] in
/-- **`fden ∣ dₙh` is free when `fden` is normal** (`dvd_dn_h_of_normal`): if `fden` equals its own normal
part (`toPolyG (cSplitFactorFastG Dt fuel fden).1 = toPolyG fden`, i.e. the special part is a unit — `fden`
weakly normalized), then `fden ∣ dₙ·h0` for any `h0`, since `dₙ·h0 = fden·h0`. The precise condition under
which the §6.2 `B`-divisibility crux disappears: weak normalization of `fden`. -/
theorem dvd_dn_h_of_normal (Dt : CPolyG β) (fuel : ℕ) (fden h0 : CPolyG β)
    (hnormal : toPolyG (CPolyG.cSplitFactorFastG Dt fuel fden).1 = toPolyG fden) :
    toPolyG fden ∣ toPolyG (CPolyG.cmulG (CPolyG.cSplitFactorFastG Dt fuel fden).1 h0) := by
  rw [CPolyG.toPolyG_cmulG, hnormal]; exact Dvd.intro _ rfl

omit [CDiffFieldSpec β] in
/-- **`fden ∣ dₙh` is free for the polynomial-RDE shape `fden = [1]`** (`dvd_dn_h_one`): when the input
denominator is the unit `[1]`, the normal part is `[1]` (`cSplitFactorFastG_one_eq`), so the `B`-divisibility
`[1] ∣ dₙh` is `1 ∣ _` — trivially true. The polynomial RDE (`Dy + f·y = g` with `f` a polynomial) needs no
weak normalization on `f`'s side. -/
theorem dvd_dn_h_one [CTowerGcdWitness β] (fuel : ℕ) (h0 : CPolyG β) :
    toPolyG ([CField.one] : CPolyG β)
      ∣ toPolyG (CPolyG.cmulG
        (CPolyG.cSplitFactorFastG ([CField.one] : CPolyG β) fuel [CField.one]).1 h0) := by
  rw [cSplitFactorFastG_one_eq, CPolyG.toPolyG_cmulG, toPolyG_cone_eq_one]; exact one_dvd _

end Divisibility

/-! ## ★ Task 5 — assembling the sharpened residual: the reduced crux + builder + field corollary

The clauses fall into two groups: the **discharged** ones (`hprim` via the gcd witness, `hyden` via the
solve guard, `hfden`/`hgden`/`hfden0`/`hgden0` via the subtype, `hdvdB`/`hdvdC` reduced to the two
product-divisibilities) and the **genuinely remaining** ones (the two product-divisibilities themselves
`hdvdB_dn_h`/`hdvdC_dn_h2`, the normal-part-nonzero `hdn`, the fuel bounds `hfbB`/`hfbC`, the non-gcd
`CSPDEGClearedInputsGen` chain `hin`, and the dispatcher `hdb`). We bundle exactly the latter as the
**reduced crux residual** `RischDESuccessResidualCrux`, give a builder `residual_of_crux` rebuilding the full
`RischDESuccessResidual` from it (discharging the former group), and compose to the field identity
`crischDESolve_field_of_crux`. The crux is the precise sharpened TRUE residual — the §6.1
weak-normalization product-divisibilities + per-run termination/fuel, with everything else discharged. -/

section Crux

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
  [CFracGcdCore β] [CRischField β] [CTowerGcdWitness β]

/-- **★ The reduced RDE residual crux** `RischDESuccessResidualCrux f g`: exactly the clauses of
`RischDESuccessResidual` a successful recursive solve does NOT yield — with the discharged clauses
(`hprim`/`hyden`/`hfden`/`hgden`/`hfden0`/`hgden0`) removed and `hdvdB`/`hdvdC` reduced to their
product-divisibility essence. Carries, per normal-denominator output `(a0,b0,c0,h0)`: the §6.1
weak-normalization product-divisibilities `hdvdB_dn_h` (`fden ∣ dₙh`) and `hdvdC_dn_h2` (`gden ∣ dₙh²`), the
normal-part-nonzero `hdn`, the fuel bounds `hfbB`/`hfbC`, and the non-gcd `CSPDEGClearedInputsGen` chain `hin`
(whose per-level `Associated`-gcd clauses are supplied separately by `CTowerGcdWitness β`); plus the
dispatcher `hdb`. The sharpened TRUE residual: NOT engine self-certification, but the genuine §6.1
weak-normalization precondition + per-run termination/fuel. -/
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
  /-- §6.2 fuel bound on the `B`-numerator. -/
  hfbB : ∀ a0 b0 c0 h0 : CPolyG β,
    cRdeNormalDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2 g.1.1 g.1.2
        = some (a0, b0, c0, h0) →
      (CPolyG.cnormG (CPolyG.csubG
        (CPolyG.cmulG (CPolyG.cmulG
          (CPolyG.cSplitFactorFastG ([CField.one] : CPolyG β) towerRischDEFuel f.1.2).1 h0) f.1.1)
        (CPolyG.cmulG (CPolyG.cmulG
          (CPolyG.cSplitFactorFastG ([CField.one] : CPolyG β) towerRischDEFuel f.1.2).1
            (CPolyG.cmonomialDeriv ([CField.one] : CPolyG β) h0)) f.1.2)) : List β).length
        ≤ towerRischDEFuel
  /-- §6.2 fuel bound on the `C`-numerator. -/
  hfbC : ∀ a0 b0 c0 h0 : CPolyG β,
    cRdeNormalDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2 g.1.1 g.1.2
        = some (a0, b0, c0, h0) →
      (CPolyG.cnormG (CPolyG.cmulG (CPolyG.cmulG (CPolyG.cmulG
        (CPolyG.cSplitFactorFastG ([CField.one] : CPolyG β) towerRischDEFuel f.1.2).1 h0) h0)
        g.1.1) : List β).length ≤ towerRischDEFuel
  /-- The §6.4 per-level transparent-input chain `CSPDEGClearedInputsGen` (gcd clauses via the witness). -/
  hin : ∀ a0 b0 c0 h0 : CPolyG β,
    cRdeNormalDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2 g.1.1 g.1.2
        = some (a0, b0, c0, h0) →
      CSPDEGClearedInputsGen ([CField.one] : CPolyG β) towerRischDEFuel
        (cRdeSpecialDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel a0 b0 c0).1
        (cRdeSpecialDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel a0 b0 c0).2.1
        (cRdeSpecialDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel a0 b0 c0).2.2.1
        (cRdeBoundDegreeG ([CField.one] : CPolyG β) towerRischDEFuel
          (cRdeSpecialDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel a0 b0 c0).1
          (cRdeSpecialDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel a0 b0 c0).2.1
          (cRdeSpecialDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel a0 b0 c0).2.2.1 : ℤ)
  /-- The positive-`deg(bbar)` dispatcher side-condition (Lemma 6.5.1 non-cancellation routing). -/
  hdb : ∀ a0 b0 c0 bbar cbar : CPolyG β, ∀ m : ℤ, ∀ α' β' : CPolyG β,
    cSPDEG ([CField.one] : CPolyG β) towerRischDEFuel
        (cRdeSpecialDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel a0 b0 c0).1
        (cRdeSpecialDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel a0 b0 c0).2.1
        (cRdeSpecialDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel a0 b0 c0).2.2.1
        (cRdeBoundDegreeG ([CField.one] : CPolyG β) towerRischDEFuel
          (cRdeSpecialDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel a0 b0 c0).1
          (cRdeSpecialDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel a0 b0 c0).2.1
          (cRdeSpecialDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel a0 b0 c0).2.2.1 : ℤ)
      = some (bbar, cbar, m, α', β') → 0 < cdegG bbar

omit [CDiffFieldSpec β] in
/-- **★ The full residual from the reduced crux** (`residual_of_crux`): given a successful recursive solve
`crischDESolve f g = some y`, the gcd witness `[CTowerGcdWitness β]`, and the reduced crux
`RischDESuccessResidualCrux f g`, the full `RischDESuccessResidual f g` holds. The builder discharges the
removed clauses — `hprim` from `cdegG_cSpecialPolyG_one_eq_zero`, `hyden` from `crischDESolve_yden_ne_zero`,
`hfden`/`hgden`/`hfden0`/`hgden0` from the subtype, and `hdvdB`/`hdvdC` from the crux's product-divisibilities
via `hdvdB_of_dvd`/`hdvdC_of_dvd` — and threads the genuinely-remaining clauses through. So the capstone's
residual hypothesis is exactly the sharpened crux. -/
theorem residual_of_crux (f g y : QFunNZG β)
    (hsolve : CRischField.crischDESolve f g = some y)
    (hcrux : RischDESuccessResidualCrux f g) :
    RischDESuccessResidual f g where
  hres a0 b0 c0 h0 hnorm := {
    hprim := cdegG_cSpecialPolyG_one_eq_zero towerRischDEFuel
    hdn := hcrux.hdn a0 b0 c0 h0 hnorm
    hfden0 := qfunNZG_den_cnormG_ne_nil f
    hgden0 := qfunNZG_den_cnormG_ne_nil g
    hfbB := hcrux.hfbB a0 b0 c0 h0 hnorm
    hdvdB := hdvdB_of_dvd ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2 h0
      (hcrux.hdvdB_dn_h a0 b0 c0 h0 hnorm)
    hfbC := hcrux.hfbC a0 b0 c0 h0 hnorm
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

/-- **★★ The recursive RDE-oracle field identity from the sharpened crux** (`crischDESolve_field_of_crux`): a
successful recursive solve `crischDESolve f g = some y` over `QFunNZG β`, with the gcd witness
`[CTowerGcdWitness β]` and the reduced crux `RischDESuccessResidualCrux f g`, yields the field-level Risch-DE
identity `towerFractionFieldDerivG [1] (Y) + F·Y = G` over `RatFunc (CFieldSpec.K β)`
(`Y = amG y.1.1/amG y.1.2`, etc.). Composes `residual_of_crux` (rebuild the full residual, discharging the
provable clauses) with the capstone `crischDESolve_field_of_witness_residual`. **No `native_decide`** — the
discharged clauses are theorems, the gcd half the witness's tower induction, and the only hypothesis is the
sharpened crux. This is the capstone result with its residual reduced to exactly the §6.1
weak-normalization product-divisibilities plus per-run termination/fuel. -/
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

/-! ### Restatement against the intended wording (anonymous `example`) -/

-- ★ Task 5: the recursive RDE field identity from the sharpened crux + the gcd witness — no native_decide.
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
   its raw argument (`cWeakNormalizerG` is the missing pre-step), so the engine computes the `cdivG` clearing
   unconditionally and never re-validates exactness. **This is the genuine obstruction — a missing
   precondition, NOT engine self-certification.**
2. **`hdn`** (normal part nonzero) — rests on the splitting-factorization product `fden = dₙ·dₛ`, which
   `cSplitFactorFastG` is documented not to establish abstractly (`ComputableTowerUnify`); per-run regularity.
3. **The fuel bounds** `hfbB`/`hfbC` (`length ≤ 60`) and the **non-gcd `CSPDEGClearedInputsGen` chain** `hin`
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
