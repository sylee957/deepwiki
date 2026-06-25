import DeepWiki.SymbolicIntegration.ComputableWellFounded2
import DeepWiki.SymbolicIntegration.ComputableGcdCorrect
import DeepWiki.SymbolicIntegration.ComputableSplitFactorCorrect

/-! # Fuel-free (well-founded) §3.5 ops — `cdivFFWf`, `cgcdFFWf`, `cSplitFactorFastWf`

This continues the fuel-free conversion of `ComputableWellFounded`/`ComputableWellFounded2` from the
leaf ops to the §3.5 (Bronstein splitting-factorization) layer over the tower ℚ(x)[t]:

* **`cdivFFWf` / `cgcdFFWf`** — fuel-free companions of the §3.5 exact division `cdivFF` and the
  fraction-free monic gcd `cgcdFF` (`ComputableSplitFactorFast`). These are *compositions*: `cdivFF` is
  just `cdivG`, so `cdivFFWf := cdivWf` (the leaf fuel-free quotient); `cgcdFF` clears denominators and
  monic-normalizes the primitive-PRS gcd `primPRSgcd`, with the fuel going **only** to `primPRSgcd`, so
  `cgcdFFWf` substitutes the leaf `primPRSgcdWf` and the rest of the pipeline is fuel-free already. Their
  abstract correctness (`toPolyG_cdivmodWf`, `associated_toPolyG_cgcdFF…`) transports through the bridges.

* **`cSplitFactorFastWf`** — the fuel-free companion of Bronstein's splitting-factorization loop
  `cSplitFactorFast` (`ComputableSplitFactorFast`), an **own-loop**. The recursion peels a special factor
  `S = gcd(p, Dp)/gcd(p, dp/dt)` each step and recurses on `p/S`, whose normalized `t`-length strictly
  drops (the special factor is non-constant when the loop continues). The well-founded measure is the
  normalized list length `(cnormG p).length`, with the structural runtime guard `(cnormG (p/S)).length <
  (cnormG p).length`, so `decreasing_by` is `assumption` and the def stays fuel-free. The book-faithful
  splitting-factorization correctness `cSplitFactorFast_isSplittingFactorizationGen` transports through
  the bridge `cSplitFactorFastWf_eq`, under the same `CSplitFactorFastRegular` gate, fuel-free.

As in `ComputableWellFounded`, the fuel bounds live only in the bridge proofs; the runtime WF ops carry
no fuel. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

namespace CPolyG

/-! ### Target A.1 — the fuel-free exact division `cdivFFWf` (composition over `cdivWf`)

`cdivFF fuel p q = cdivG fuel p q` (`ComputableSplitFactorFast`), so its fuel-free companion is simply the
leaf fuel-free quotient `cdivWf` (`ComputableWellFounded`): `cdivFFWf p q = cdivWf p q`. No bridge proof is
needed — the leaf `toPolyG_cdivmodWf`/`toPolyG_cmodWf` already give the (fuel-free) Euclidean identity. -/

/-- **Fuel-free exact division over ℚ(x)[t]** `cdivFFWf p q = p / q`: the fuel-free companion of `cdivFF`
(`= cdivG`), defined as the leaf fuel-free quotient `cdivWf` (true well-founded recursion, no fuel at
runtime). At the `splitFactor` call sites `q` divides `p`, so this is the exact quotient. -/
def cdivFFWf (p q : CPolyG QFunNZ) : CPolyG QFunNZ := cdivWf p q

/-- **`cdivFFWf` is the fuel'd `cdivFF` at any sufficient fuel**: for `(cnormG p).length ≤ fuel`,
`cdivFFWf p q = cdivFF fuel p q`. Both are the quotient of generic Euclidean division; the leaf bridge
`cdivmodWf_eq_of_fuel` supplies the agreement. -/
theorem cdivFFWf_eq_of_fuel (fuel : ℕ) (p q : CPolyG QFunNZ)
    (hfuel : (cnormG p : List QFunNZ).length ≤ fuel) :
    cdivFFWf p q = CPolyG.cdivFF fuel p q := by
  rw [cdivFFWf, CPolyG.cdivFF, cdivG, cdivWf, cdivmodWf_eq_of_fuel fuel p q hfuel]

/-- **Euclidean-division identity through `toPolyG`** for the fuel-free `cdivFFWf` (nonzero divisor,
**no fuel hypothesis**): `toPolyG p = toPolyG (cdivFFWf p q) · toPolyG q + toPolyG (cmodWf p q)`.
Transported from the leaf `toPolyG_cmodWf`. -/
theorem toPolyG_cdivFFWf (p q : CPolyG QFunNZ) (hq0 : cnormG q ≠ []) :
    toPolyG p = toPolyG (cdivFFWf p q) * toPolyG q + toPolyG (cmodWf p q) := by
  rw [cdivFFWf]; exact toPolyG_cmodWf p q hq0

/-! ### Target A.2 — the fuel-free fraction-free monic gcd `cgcdFFWf`

`cgcdFF fuel p q = cmonicG (liftBPolyToQFunNZ (primPRSgcd fuel P Q))` with `(P, Q)` the `bdeg`-ordered pair
of `clearDenoms p`, `clearDenoms q` — the fuel goes **only** to `primPRSgcd`. So the fuel-free companion
substitutes the leaf `primPRSgcdWf` (`ComputableWellFounded2`): `cgcdFFWf p q = cmonicG (liftBPolyToQFunNZ
(primPRSgcdWf P Q))`, with the `clearDenoms`/ordering/lift/monic-normalize all fuel-free already. -/

/-- **Fuel-free fraction-free monic gcd over ℚ(x)[t]** `cgcdFFWf p q`: the fuel-free companion of `cgcdFF`.
Clears denominators of both inputs into ℚ[x][t], `bdeg`-orders them (larger first), runs the **fuel-free**
primitive PRS `primPRSgcdWf`, lifts the result back to ℚ(x)[t] and monic-normalizes — **no fuel at
runtime**. `native_decide`-able over the noncomputable-`CFieldSpec` tower `QFunNZ`. -/
def cgcdFFWf (p q : CPolyG QFunNZ) : CPolyG QFunNZ :=
  let P := CPolyG.clearDenoms p
  let Q := CPolyG.clearDenoms q
  let (P, Q) := if Compute.bdeg P < Compute.bdeg Q then (Q, P) else (P, Q)
  cmonicG (CPolyG.liftBPolyToQFunNZ (primPRSgcdWf P Q))

/-- **Bridge — `cgcdFFWf` equals `cgcdFF` at any sufficient fuel.** With the smaller (divisor) cleared
poly's normalized `t`-length bounded by `fuel`, `deg(smaller) ≤ deg(larger)`, and the larger cleared
poly's `t`-length `≤ 60` (the per-node pseudo-remainder bound a real run meets), `cgcdFFWf p q =
cgcdFF fuel p q`. The bounds live only here; `cgcdFFWf` carries no fuel. The `primPRSgcd` argument is
bridged by `primPRSgcdWf_eq_of_fuel`; the rest of the `cgcdFF` pipeline is fuel-free. -/
theorem cgcdFFWf_eq_of_fuel (fuel : ℕ) (p q : CPolyG QFunNZ)
    (hfuel : (Compute.bnorm (if Compute.bdeg (CPolyG.clearDenoms p) < Compute.bdeg (CPolyG.clearDenoms q)
        then CPolyG.clearDenoms p else CPolyG.clearDenoms q)).length ≤ fuel)
    (hdeg : (Compute.bnorm (if Compute.bdeg (CPolyG.clearDenoms p) < Compute.bdeg (CPolyG.clearDenoms q)
        then CPolyG.clearDenoms p else CPolyG.clearDenoms q)).length
      ≤ (Compute.bnorm (if Compute.bdeg (CPolyG.clearDenoms p) < Compute.bdeg (CPolyG.clearDenoms q)
        then CPolyG.clearDenoms q else CPolyG.clearDenoms p)).length)
    (hP60 : (Compute.bnorm (if Compute.bdeg (CPolyG.clearDenoms p) < Compute.bdeg (CPolyG.clearDenoms q)
        then CPolyG.clearDenoms q else CPolyG.clearDenoms p)).length ≤ 60) :
    cgcdFFWf p q = CPolyG.cgcdFF fuel p q := by
  rw [cgcdFFWf, CPolyG.cgcdFF]
  by_cases hlt : Compute.bdeg (CPolyG.clearDenoms p) < Compute.bdeg (CPolyG.clearDenoms q)
  · simp only [if_pos hlt] at hfuel hdeg hP60 ⊢
    rw [primPRSgcdWf_eq_of_fuel fuel _ _ hfuel hdeg hP60]
  · simp only [if_neg hlt] at hfuel hdeg hP60 ⊢
    rw [primPRSgcdWf_eq_of_fuel fuel _ _ hfuel hdeg hP60]

/-! ### Transported correctness of `cgcdFFWf`

Over the field ℚ(x) = `RatFunc ℚ`, `cgcdFFWf p q` computes the polynomial gcd of the inputs, gated on the
same regularity the fuel'd `cgcdFF` carries. The bridge `cgcdFFWf_eq_of_fuel` extracts the `≤ 60` per-node
bound and the `≤ fuel`, `deg`-ordering hypotheses from the node-regularity gate (`PrimPRSNodeRegular.head`,
`bnorm_idem`), and `associated_toPolyG_cgcdFF_of_nodeRegular` then transports. -/

/-- **`cgcdFFWf` correct from per-node degree bounds — fuel-free** (the transported headline): over
ℚ(x) = `RatFunc ℚ`, `toPolyG (cgcdFFWf p q)` is `Associated` to `gcd (toPolyG p) (toPolyG q)` in
`(RatFunc ℚ)[X]`, gated on `PrimPRSNodeRegular` of the `bdeg`-ordered cleared pair plus `fuel ≥ deg` and
`deg Q ≤ deg P` — the SAME gate the fuel'd `associated_toPolyG_cgcdFF_of_nodeRegular` carries; the WF
bridge only removes the explicit `fuel` from the runtime. The `≤ 60` pseudo-remainder bound for the bridge
is read off `PrimPRSNodeRegular.head` (the larger cleared poly's `deg_t ≤ 60`). -/
theorem associated_toPolyG_cgcdFFWf_of_nodeRegular (fuel : ℕ) (p q : CPolyG QFunNZ)
    (hfuel : (Compute.bnorm (if Compute.bdeg (CPolyG.clearDenoms p) < Compute.bdeg (CPolyG.clearDenoms q)
        then CPolyG.clearDenoms p else CPolyG.clearDenoms q)).length ≤ fuel)
    (hdeg : (Compute.bnorm (if Compute.bdeg (CPolyG.clearDenoms p) < Compute.bdeg (CPolyG.clearDenoms q)
        then CPolyG.clearDenoms p else CPolyG.clearDenoms q)).length
      ≤ (Compute.bnorm (if Compute.bdeg (CPolyG.clearDenoms p) < Compute.bdeg (CPolyG.clearDenoms q)
        then CPolyG.clearDenoms q else CPolyG.clearDenoms p)).length)
    (hnode : PrimPRSNodeRegular fuel
      (if Compute.bdeg (CPolyG.clearDenoms p) < Compute.bdeg (CPolyG.clearDenoms q)
        then CPolyG.clearDenoms q else CPolyG.clearDenoms p)
      (if Compute.bdeg (CPolyG.clearDenoms p) < Compute.bdeg (CPolyG.clearDenoms q)
        then CPolyG.clearDenoms p else CPolyG.clearDenoms q)) :
    Associated (toPolyG (cgcdFFWf p q)) (gcd (toPolyG p) (toPolyG q)) := by
  -- the `≤ 60` bound for the bridge comes from the larger cleared poly's head bounds
  have hP60 : (Compute.bnorm (if Compute.bdeg (CPolyG.clearDenoms p) < Compute.bdeg (CPolyG.clearDenoms q)
      then CPolyG.clearDenoms q else CPolyG.clearDenoms p)).length ≤ 60 := by
    have := (hnode.head fuel _ _).2.2
    rwa [Compute.bnorm_idem] at this
  rw [cgcdFFWf_eq_of_fuel fuel p q hfuel hdeg hP60]
  exact associated_toPolyG_cgcdFF_of_nodeRegular fuel p q hfuel hdeg hnode

end CPolyG

-- The fuel-free §3.5 division/gcd headlines carry only the standard axioms (no `native` axiom): the
-- `native_decide` smoke tests below carry `Lean.ofReduceBool` separately.
#print axioms CPolyG.toPolyG_cdivFFWf
#print axioms CPolyG.associated_toPolyG_cgcdFFWf_of_nodeRegular

/-! ### `native_decide` smoke tests for `cdivFFWf` / `cgcdFFWf`

These reduce over the *noncomputable*-`CFieldSpec` tower `QFunNZ` (ℚ(x)) — the well-founded structure
carries no fuel and no noncomputable bridge into the compiled body. -/

namespace CPolyG

open QFunNZ

/-- `cdivFFWf` over the ℚ(x)[t] tower: `(t² − 1)/(t − 1) = t + 1` is degree `1`. -/
example :
    CPolyG.cdegG (CPolyG.cdivFFWf [QFunNZ.ofConstNZ (-1), QFunNZ.ofConstNZ 0, QFunNZ.ofConstNZ 1]
      [QFunNZ.ofConstNZ (-1), QFunNZ.ofConstNZ 1]) = 1 := by native_decide

/-- `cgcdFFWf` over the ℚ(x)[t] tower: `gcd(t² − 1, t − 1)` is degree `1` (a `t − 1` associate) — the
whole fuel-free fraction-free PRS gcd executes in native code over `QFunNZ`. -/
example :
    CPolyG.cdegG (CPolyG.cgcdFFWf [QFunNZ.ofConstNZ (-1), QFunNZ.ofConstNZ 0, QFunNZ.ofConstNZ 1]
      [QFunNZ.ofConstNZ (-1), QFunNZ.ofConstNZ 1]) = 1 := by native_decide

/-- `cgcdFFWf` agrees with the fuel'd `cgcdFF` (monic-normalized difference is zero over ℚ(x)[t]). -/
example :
    CPolyG.cisZeroG (CPolyG.csubG
      (CPolyG.cmonicG (CPolyG.cgcdFFWf [QFunNZ.ofConstNZ (-1), QFunNZ.ofConstNZ 0, QFunNZ.ofConstNZ 1]
        [QFunNZ.ofConstNZ (-1), QFunNZ.ofConstNZ 1]))
      (CPolyG.cmonicG (CPolyG.cgcdFF 4 [QFunNZ.ofConstNZ (-1), QFunNZ.ofConstNZ 0, QFunNZ.ofConstNZ 1]
        [QFunNZ.ofConstNZ (-1), QFunNZ.ofConstNZ 1]))) = true := by native_decide

end CPolyG

/-! ### Target B — the fuel-free splitting-factorization loop `cSplitFactorFastWf`

`cSplitFactorFast Dt fuel p = (pₙ, pₛ)` (Bronstein §3.5) peels a special factor
`S = gcd(p, Dp)/gcd(p, dp/dt)` each step and recurses on `p/S`. The recursion measure is the normalized
`t`-list length `(cnormG p).length`: when the loop continues (`cdegG S ≠ 0`), the special factor `S` is
non-constant and divides `p` exactly, so the quotient `p/S` has strictly smaller `t`-degree, hence strictly
shorter normalized list. The fuel-free companion `cSplitFactorFastWf` runs the **own-loop** by well-founded
recursion on `(cnormG p).length`, with the structural runtime guard `(cnormG (p/S)).length <
(cnormG p).length`, so `decreasing_by` is `assumption` and no fuel is computed or passed at runtime. The
fuel-free leaves `cgcdFFWf`/`cdivFFWf` (Target A) compute the step `S` and the quotient. -/

namespace CPolyG

/-- **The fuel-free `SplitFactor` step** `cstepWf Dt p = cdivFFWf (cgcdFFWf p (cmonomialDeriv Dt p))
(cgcdFFWf p (cderivG p))` — the special-factor candidate `S = gcd(p, Dp)/gcd(p, dp/dt)` computed with the
fuel-free fraction-free gcd and fuel-free exact Euclidean division (the fuel-free companion of `cstep`). -/
def cstepWf (Dt : CPolyG QFunNZ) (p : CPolyG QFunNZ) : CPolyG QFunNZ :=
  cdivFFWf (cgcdFFWf p (cmonomialDeriv Dt p)) (cgcdFFWf p (cderivG p))

/-- **Fuel-free splitting-factorization loop** (Bronstein §3.5) `cSplitFactorFastWf Dt p = (pₙ, pₛ)`: the
fuel-free companion of `cSplitFactorFast`. One step extracts `S = cstepWf Dt p`; a constant `S` (`cdegG S =
0`) ⇒ `p` is normal, else recurse on the exact quotient `p/S = cdivFFWf p S` and accumulate `S` into the
special part. True well-founded recursion on `(cnormG p).length` — **no fuel at runtime**. The recursion is
taken only under the structural guard `(cnormG (cdivFFWf p S)).length < (cnormG p).length`, so
`decreasing_by` is `assumption`. Over a real run the guard never fails (the non-constant special factor
strictly drops the `t`-degree), so `cSplitFactorFastWf` agrees with `cSplitFactorFast`
(`cSplitFactorFastWf_eq`). -/
def cSplitFactorFastWf (Dt : CPolyG QFunNZ) (p : CPolyG QFunNZ) : CPolyG QFunNZ × CPolyG QFunNZ :=
  let S := cstepWf Dt p
  if cdegG S = 0 then (p, [CField.one])
  else
    let pq := cdivFFWf p S
    if (cnormG pq : List QFunNZ).length < (cnormG p : List QFunNZ).length then
      let (qn, qs) := cSplitFactorFastWf Dt pq
      (qn, cmulG S qs)
    else (p, [CField.one])   -- unreachable on a real run (the special factor drops the degree)
termination_by (cnormG p).length
decreasing_by assumption

end CPolyG

/-! ### Bridge of `cSplitFactorFastWf` to the fuel'd `cSplitFactorFast`, and transported correctness

Under a regular run (`CSplitFactorFastRegular`, the same gate `cSplitFactorFast_isSplittingFactorizationGen`
carries) the step `cstepWf` matches `cstep` and the non-constant special factor strictly drops the degree,
so `cSplitFactorFastWf`'s structural guard never fails and it coincides with `cSplitFactorFast fuel`. The
fuel bounds live only in the bridge proof; the runtime `cSplitFactorFastWf` carries no fuel. The
book-faithful splitting-factorization correctness is then transported, fuel-free. -/

/-- **`cgcdFFWf` equals the fuel'd `cgcdFF` from a `CgcdFFNodeReg` bundle** — the wrapper of
`cgcdFFWf_eq_of_fuel` with its `hfuel`/`hdeg` taken from the bundle and the `≤ 60` bound read off
`PrimPRSNodeRegular.head` (mirrors `associated_toPolyG_cgcdFF_node`). -/
theorem cgcdFFWf_eq_node (fuel : ℕ) (p q : CPolyG QFunNZ) (hreg : CgcdFFNodeReg fuel p q) :
    CPolyG.cgcdFFWf p q = CPolyG.cgcdFF fuel p q := by
  obtain ⟨hfuel, hdeg, hnode⟩ := hreg
  have hP60 : (Compute.bnorm (if Compute.bdeg (CPolyG.clearDenoms p) < Compute.bdeg (CPolyG.clearDenoms q)
      then CPolyG.clearDenoms q else CPolyG.clearDenoms p)).length ≤ 60 := by
    have := (hnode.head fuel _ _).2.2
    rwa [Compute.bnorm_idem] at this
  exact CPolyG.cgcdFFWf_eq_of_fuel fuel p q hfuel hdeg hP60

/-- **The fuel-free step matches the fuel'd step** `cstepWf Dt p = cstep Dt (fuel+1) p`, under a regular
step (`CStepRegular Dt (fuel+1) p`). Both `cgcdFF` calls are bridged by `cgcdFFWf_eq_node`, and the exact
division `cdivFFWf = cdivFF (fuel+1)` by `cdivFFWf_eq_of_fuel` with the numerator-gcd length bound from
`CStepRegular`'s third clause. -/
theorem cstepWf_eq (Dt : CPolyG QFunNZ) (fuel : ℕ) (p : CPolyG QFunNZ)
    (hreg : CStepRegular Dt (fuel + 1) p) :
    CPolyG.cstepWf Dt p = cstep Dt (fuel + 1) p := by
  obtain ⟨hregN, hregD, hfuelN⟩ := hreg
  rw [CPolyG.cstepWf, cstep]
  -- the two cgcdFF calls
  rw [cgcdFFWf_eq_node (fuel + 1) p (cmonomialDeriv Dt p) hregN,
    cgcdFFWf_eq_node (fuel + 1) p (cderivG p) hregD]
  -- the exact division: the numerator gcd's normalized length is bounded by `fuel+1`
  rw [CPolyG.cdivFFWf_eq_of_fuel (fuel + 1) _ _ hfuelN]

open Classical in
/-- **Bridge — `cSplitFactorFastWf` equals `cSplitFactorFast` at any sufficient fuel.** For `toPolyG p ≠ 0`,
fuel *strictly* exceeding the `t`-degree (`(toPolyG p).natDegree < fuel`), and a regular run
(`CSplitFactorFastRegular Dt fuel p`), `cSplitFactorFastWf Dt p = cSplitFactorFast Dt fuel p`. The fuel
bound appears only here; `cSplitFactorFastWf` carries none. By induction on `fuel`, mirroring
`cSplitFactorFast_isSplittingFactorizationGen`: at each node `cstepWf` matches `cstep` (`cstepWf_eq`); a
constant step (`cdegG S = 0`) terminates both, else the non-constant special factor `S` divides `p` exactly,
so the quotient `p/S` is nonzero with strictly smaller `t`-degree (`toPolyG_cdivFF_exact` +
`splitFactorStep_dvd`), discharging the structural length guard and supplying the IH's preconditions. The
*strict* `< fuel` keeps the recursion strictly above the fuel-exhaustion base case (which `cSplitFactorFast`
short-circuits but `cSplitFactorFastWf` does not): the `fuel = 0` case is vacuous (`natDegree < 0`). -/
theorem cSplitFactorFastWf_eq :
    ∀ (Dt : CPolyG QFunNZ) (fuel : ℕ) (p : CPolyG QFunNZ), toPolyG p ≠ 0 →
      (toPolyG p).natDegree < fuel → CSplitFactorFastRegular Dt fuel p →
      CPolyG.cSplitFactorFastWf Dt p = CPolyG.cSplitFactorFast Dt fuel p := by
  intro Dt fuel
  induction fuel with
  | zero =>
    -- vacuous: `(toPolyG p).natDegree < 0` is impossible
    intro p _ hdegp _
    exact absurd hdegp (Nat.not_lt_zero _)
  | succ fuel ih =>
    intro p hp hdegp hreg
    obtain ⟨hstepreg, hpfuel, hbranch⟩ := hreg
    haveI : CharZero (CFieldSpec.K QFunNZ) := inferInstanceAs (CharZero (RatFunc ℚ))
    set S := cstep Dt (fuel + 1) p with hSdef
    -- the fuel-free step matches the fuel'd step
    have hstepeq : CPolyG.cstepWf Dt p = S := cstepWf_eq Dt fuel p hstepreg
    -- the abstract step facts
    have haS : Associated (toPolyG S) (splitFactorStep (toPolyG Dt) (toPolyG p)) :=
      associated_toPolyG_cstep Dt (fuel + 1) p hp hstepreg
    have hstepne : splitFactorStep (toPolyG Dt) (toPolyG p) ≠ 0 := by
      have hdvd := splitFactorStep_dvd (toPolyG Dt) hp
      intro h0; exact hp (eq_zero_of_zero_dvd (h0 ▸ hdvd))
    have hSne : toPolyG S ≠ 0 := fun h => hstepne (eq_zero_of_zero_dvd (h ▸ haS.dvd))
    have hSnd : (toPolyG S).natDegree = (splitFactorStep (toPolyG Dt) (toPolyG p)).natDegree :=
      natDegree_eq_of_associated haS
    have hcdeg : cdegG S = (toPolyG S).natDegree := cdegG_eq_natDegree S
    -- the fuel'd loop step shape (its inline `let S := cdivFF (cgcdFF…) (cgcdFF…)` is defeq to `cstep`)
    have hloop : CPolyG.cSplitFactorFast Dt (fuel + 1) p
        = (if cdegG S = 0 then (p, [CField.one])
           else ((CPolyG.cSplitFactorFast Dt fuel (CPolyG.cdivFF (fuel + 1) p S)).1,
                 cmulG S (CPolyG.cSplitFactorFast Dt fuel (CPolyG.cdivFF (fuel + 1) p S)).2)) := by
      conv_lhs => rw [CPolyG.cSplitFactorFast]
      rfl
    -- the WF loop step shape, with `cstepWf` rewritten to `S`
    have hloopWf : CPolyG.cSplitFactorFastWf Dt p
        = (if cdegG S = 0 then (p, [CField.one])
           else (if (cnormG (CPolyG.cdivFFWf p S) : List QFunNZ).length
                    < (cnormG p : List QFunNZ).length
                 then ((CPolyG.cSplitFactorFastWf Dt (CPolyG.cdivFFWf p S)).1,
                       cmulG S (CPolyG.cSplitFactorFastWf Dt (CPolyG.cdivFFWf p S)).2)
                 else (p, [CField.one]))) := by
      conv_lhs => rw [CPolyG.cSplitFactorFastWf]
      simp only [hstepeq]
    rw [hloop, hloopWf]
    -- abstract the (giant) `cstep`-defined `S` behind an opaque local so the projections below never
    -- `whnf` the `cdivFF`/`cgcdFF` term (the loop shapes `hloop`/`hloopWf` are already fixed).
    clear_value S
    by_cases hdeg : cdegG S = 0
    · -- terminal: both return (p, [one])
      simp only [if_pos hdeg]
    · -- recursive step
      simp only [if_neg hdeg]
      -- the step is non-constant and divides `p` exactly
      have hSpos : 0 < (splitFactorStep (toPolyG Dt) (toPolyG p)).natDegree := by
        rw [← hSnd, ← hcdeg]; exact Nat.pos_of_ne_zero hdeg
      have hSdvd : toPolyG S ∣ toPolyG p :=
        haS.dvd.trans (splitFactorStep_dvd (toPolyG Dt) hp)
      have hScn : cnormG S ≠ [] := fun h => hSne ((cnormG_eq_nil_iff S).mp h)
      have hexact : toPolyG p = toPolyG (CPolyG.cdivFF (fuel + 1) p S) * toPolyG S :=
        toPolyG_cdivFF_exact (fuel + 1) p S hScn hpfuel hSdvd
      -- the quotient is nonzero with strictly smaller degree
      have hqne : toPolyG (CPolyG.cdivFF (fuel + 1) p S) ≠ 0 := by
        intro h0; rw [h0, zero_mul] at hexact; exact hp hexact
      have hqdeg : (toPolyG (CPolyG.cdivFF (fuel + 1) p S)).natDegree < fuel := by
        have hdegdrop : (toPolyG (CPolyG.cdivFF (fuel + 1) p S)).natDegree + (toPolyG S).natDegree
            = (toPolyG p).natDegree := by
          rw [hexact, Polynomial.natDegree_mul hqne hSne]
        have hSposc : 0 < (toPolyG S).natDegree := by rw [hSnd]; exact hSpos
        omega
      -- bridge the quotient: `cdivFFWf p S = cdivFF (fuel+1) p S`
      have hdiveq : CPolyG.cdivFFWf p S = CPolyG.cdivFF (fuel + 1) p S :=
        CPolyG.cdivFFWf_eq_of_fuel (fuel + 1) p S hpfuel
      -- the structural length guard holds (strict degree drop)
      have hguard : (cnormG (CPolyG.cdivFFWf p S) : List QFunNZ).length
          < (cnormG p : List QFunNZ).length := by
        rw [hdiveq]
        have hqcn : cnormG (CPolyG.cdivFF (fuel + 1) p S) ≠ [] :=
          fun h => hqne ((cnormG_eq_nil_iff _).mp h)
        have hpcn : cnormG p ≠ [] := fun h => hp ((cnormG_eq_nil_iff p).mp h)
        rw [length_cnormG_of_ne _ hqcn, length_cnormG_of_ne p hpcn]
        have hSposc : 0 < (toPolyG S).natDegree := by rw [hSnd]; exact hSpos
        have hdegdrop : (toPolyG (CPolyG.cdivFF (fuel + 1) p S)).natDegree + (toPolyG S).natDegree
            = (toPolyG p).natDegree := by
          rw [hexact, Polynomial.natDegree_mul hqne hSne]
        omega
      rw [if_pos hguard]
      -- the recursive regularity branch (non-terminal: `cdegG S ≠ 0`); `S` is opaque, matching `hbranch`
      have hrecreg : CSplitFactorFastRegular Dt fuel (CPolyG.cdivFF (fuel + 1) p S) :=
        hbranch.resolve_left hdeg
      -- apply the IH on the quotient (matched through the division bridge)
      have hih := ih (CPolyG.cdivFF (fuel + 1) p S) hqne hqdeg hrecreg
      rw [hdiveq, hih]

/-- **The fuel-free `cSplitFactorFastWf` loop output is a book-faithful splitting factorization** (the
transported headline): for `toPolyG p ≠ 0`, fuel strictly exceeding the `t`-degree
(`(toPolyG p).natDegree < fuel`), and a regular run (`CSplitFactorFastRegular Dt fuel p`), the WF loop
output `(pₙ, pₛ) = cSplitFactorFastWf Dt p`, read through `toPolyG` over the field ℚ(x) = `RatFunc ℚ`,
satisfies `IsSplittingFactorizationGen (toPolyG p) (toPolyG pₛ) (toPolyG pₙ)` w.r.t. the monomial
derivation `D` (`Dt = toPolyG Dt`). The same `CSplitFactorFastRegular` gate as the fuel'd
`cSplitFactorFast_isSplittingFactorizationGen`; the WF bridge `cSplitFactorFastWf_eq` only removes the
explicit `fuel` from the runtime, fuel-free. -/
theorem cSplitFactorFastWf_isSplittingFactorizationGen (Dt : CPolyG QFunNZ) (fuel : ℕ)
    (p : CPolyG QFunNZ) (hp : toPolyG p ≠ 0) (hdegp : (toPolyG p).natDegree < fuel)
    (hreg : CSplitFactorFastRegular Dt fuel p) :
    @IsSplittingFactorizationGen _ _ ⟨Differential.implicitDeriv (toPolyG Dt)⟩
      (toPolyG p)
      (toPolyG (CPolyG.cSplitFactorFastWf Dt p).2)
      (toPolyG (CPolyG.cSplitFactorFastWf Dt p).1) := by
  rw [cSplitFactorFastWf_eq Dt fuel p hp hdegp hreg]
  exact cSplitFactorFast_isSplittingFactorizationGen Dt fuel p hp (le_of_lt hdegp) hreg

-- The fuel-free splitting-factorization headline (`CSplitFactorFastRegular`-gated, as the fuel'd version)
-- carries only the standard axioms.
#print axioms cSplitFactorFastWf_isSplittingFactorizationGen

/-! ### Restatement against the intended wording (anonymous `example`) -/

-- The headline: the fuel-free `cSplitFactorFastWf` loop, read over ℚ(x) = `RatFunc ℚ`, returns a
-- book-faithful splitting factorization of `toPolyG p` w.r.t. the monomial derivation `Dt = toPolyG Dt`
-- — `toPolyG p = toPolyG pₛ · toPolyG pₙ`, `pₛ` special, every squarefree factor of `pₙ` normal — under
-- the same regularity gate the fuel'd version carries, **with no fuel at runtime**.
example (Dt : CPolyG QFunNZ) (fuel : ℕ) (p : CPolyG QFunNZ) (hp : toPolyG p ≠ 0)
    (hdegp : (toPolyG p).natDegree < fuel) (hreg : CSplitFactorFastRegular Dt fuel p) :
    @IsSplittingFactorizationGen _ _ ⟨Differential.implicitDeriv (toPolyG Dt)⟩
      (toPolyG p)
      (toPolyG (CPolyG.cSplitFactorFastWf Dt p).2)
      (toPolyG (CPolyG.cSplitFactorFastWf Dt p).1) :=
  cSplitFactorFastWf_isSplittingFactorizationGen Dt fuel p hp hdegp hreg

/-! ### `native_decide` smoke tests for `cSplitFactorFastWf`

The whole fuel-free splitting-factorization loop executes in native code over the noncomputable-`CFieldSpec`
tower `QFunNZ` (ℚ(x)) — `cSplitFactorFastWf` carries no fuel and no noncomputable bridge into the compiled
body. Bronstein's degree-5 Example 3.5.1 (where the naive ℚ(x)-Euclidean kernel did not finish) computes
the book's `(deg pₙ, deg pₛ) = (3, 2)`. -/

namespace CPolyG

/-- `cSplitFactorFastWf` on `(t−1)(t−2)` over ℚ(x)[t]: degree-1 normal part. -/
example :
    CPolyG.cdegG (CPolyG.cSplitFactorFastWf cSplitFactorExampleDt cSplitFactorExampleP).1 = 1 := by
  native_decide

/-- `cSplitFactorFastWf` on `(t−1)(t−2)`: degree-1 special part. -/
example :
    CPolyG.cdegG (CPolyG.cSplitFactorFastWf cSplitFactorExampleDt cSplitFactorExampleP).2 = 1 := by
  native_decide

/-- **Example 3.5.1** (Bronstein §3.5, p.101) COMPUTES fuel-free: `cSplitFactorFastWf` on the degree-5 `p`
returns `(deg pₙ, deg pₛ) = (3, 2)`, the book's worked answer — the own-loop runs end-to-end with **no fuel
at runtime**, where the naive ℚ(x)-Euclidean kernel did not finish in budget. -/
example :
    (CPolyG.cdegG (CPolyG.cSplitFactorFastWf splitFastExample351Dt splitFastExample351P).1,
     CPolyG.cdegG (CPolyG.cSplitFactorFastWf splitFastExample351Dt splitFastExample351P).2) = (3, 2) := by
  native_decide

/-- **Example 3.5.1 fuel-free split matches the book's `pₙ`/`pₛ`** — the monic-normalized normal and special
parts of the fuel-free `cSplitFactorFastWf` split equal Bronstein's `pₙ = 4x⁴t³−4x³(x+2)t²+4x²(2x+1)t−4x²`
and `pₛ = t²+(1/x)t−(2x−1)/(4x²)`, checked by `cisZeroG` of the differences over ℚ(x)[t]. -/
example :
    CPolyG.cisZeroG (CPolyG.csubG
      (CPolyG.cmonicG (CPolyG.cSplitFactorFastWf splitFastExample351Dt splitFastExample351P).1)
      (CPolyG.cmonicG splitFastExample351Pn)) = true
    ∧ CPolyG.cisZeroG (CPolyG.csubG
      (CPolyG.cmonicG (CPolyG.cSplitFactorFastWf splitFastExample351Dt splitFastExample351P).2)
      (CPolyG.cmonicG splitFastExample351Ps)) = true := by native_decide

end CPolyG

end DeepWiki.SymbolicIntegration
