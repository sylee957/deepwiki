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

end DeepWiki.SymbolicIntegration
