import DeepWiki.SymbolicIntegration.ComputableWellFounded3
import DeepWiki.SymbolicIntegration.ComputableCanonicalRepCorrect

/-! # Fuel-free (well-founded) §3.5 ops — Yun squarefree split, `SplitSquarefreeFactor`, canonical rep

This completes the fuel-free conversion of the §3.5 (Bronstein splitting-factorization) layer begun in
`ComputableWellFounded3`. The three remaining §3.5 ops over the tower ℚ(x)[t]:

* **`cSqfreeYunFFWf`** — the fuel-free companion of Yun's squarefree factorization in `t`
  `cSqfreeYunFF` (`ComputableSplitSquarefree`), an **own-loop**. Yun peels the monic squarefree part
  `pᵢ = gcd(bᵢ, dᵢ)` of multiplicity `i` each step and recurses on `bᵢ₊₁ = bᵢ/pᵢ`, `dᵢ₊₁ = dᵢ/pᵢ −
  bᵢ₊₁'`; when the loop continues, the emitted `pᵢ` is non-constant, so the running `bᵢ₊₁` has strictly
  smaller `t`-degree. The well-founded measure is the running poly's normalized list length
  `(cnormG b).length`, with the structural runtime guard `(cnormG b').length < (cnormG b).length`, so
  `decreasing_by` is `assumption` and the loop carries no fuel. The fuel-free leaves `cgcdFFWf`/`cdivWf`
  (Target A of `ComputableWellFounded3`) compute each `pᵢ` and the quotients. The bridge
  `cSqfreeYunFFgoWf_eq` to the fuel'd `cSqfreeYunFFgo` is a clean induction on the outer Yun counter
  (mirroring `primPRSgcdWf_eq_of_fuel`), under a per-step `CSqfreeYunRegular` run-regularity bundle.

* **`cSplitSquarefreeFactorFastWf`** — the fuel-free companion of `cSplitSquarefreeFactorFast`: the
  composition `(p₁,…,pₘ) ← cSqfreeYunFFWf p`, then per factor `Sᵢ = cgcdFFWf pᵢ (cmonomialDeriv Dt pᵢ)`
  (special) and `Nᵢ = cdivWf pᵢ Sᵢ` (normal), via a fuel-free `.map`. The per-Yun-factor split
  correctness `cSqfreeFactor_isSplittingFactorizationGen` (`ComputableCanonicalRepCorrect`) applies to
  each output factor unchanged (fuel-free, through `csqfreeSpecial`/`csqfreeNormal` agreement).

* **`canonicalRepresentationFastWf`** — the fuel-free companion of the §3.5 capstone
  `canonicalRepresentationFast` (`ComputableCanonicalRep`) that `cIntegrate` consumes: divide
  `a = q·d + r` (`cdivmodWf`), split `d = dₛ·dₙ` (`cSplitFactorFastWf`, Target B of
  `ComputableWellFounded3`), and Bézout-split `r` over the coprime `(dₙ, dₛ)`
  (`cextendedEuclideanSplitWf`/`cbezoutOneWf`, using the fuel-free extended-Euclid `cgcdWf`). Every
  sub-op is a WF leaf, so the capstone is fuel-free end-to-end. The abstract reconstruction
  `canonicalRepFast_reconstructs` (`ComputableCanonicalRepCorrect`) transports through the bridge
  `canonicalRepresentationFastWf_eq`, under the same `CCanonicalRepFastRegular` gate, fuel-free.

As in `ComputableWellFounded`, the fuel bounds live only in the bridge proofs; the runtime WF ops carry
no fuel. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

namespace CPolyG

/-! ### Target A — the fuel-free Yun squarefree factorization `cSqfreeYunFFWf` (own-loop)

`cSqfreeYunFFgo fuel fo b d` (`ComputableSplitSquarefree`) is Yun's main loop: stop when `b` is constant
(`cdegG b = 0`), else emit `p = cmonicG (cgcdFF fuel b d)`, recurse on `b' = b/p`, `d' = d/p − b'`. The
running poly is `b`, whose normalized list length `(cnormG b).length` strictly drops when the loop
continues (the emitted `p` is non-constant — multiplicity `≥ 1` — so `b/p` has strictly smaller
`t`-degree). The fuel-free companion runs the **own-loop** by well-founded recursion on `(cnormG b).length`
with the structural runtime guard `(cnormG b').length < (cnormG b).length`, computing each `p`/`b'`/`d'`
with the fuel-free leaves `cgcdFFWf`/`cdivWf`. -/

/-- **Fuel-free Yun main loop** (fraction-free) `cSqfreeYunFFgoWf b d`: the fuel-free companion of
`cSqfreeYunFFgo`. Stops when `b` is constant (`cdegG b = 0`), else emits `p = cmonicG (cgcdFFWf b d)`,
recurses on `b' = cdivWf b p`, `d' = cdivWf d p − b'`. True well-founded recursion on `(cnormG b).length`
— **no fuel at runtime**; the recursion is taken only under the structural guard `(cnormG b').length <
(cnormG b).length`, so `decreasing_by` is `assumption`. Over a real run the guard never fails (the emitted
`p` is non-constant, so `b/p` drops the `t`-degree), so `cSqfreeYunFFgoWf` agrees with `cSqfreeYunFFgo`
(`cSqfreeYunFFgoWf_eq`). -/
def cSqfreeYunFFgoWf (b d : CPolyG QFunNZ) : List (CPolyG QFunNZ) :=
  if cdegG b = 0 then []
  else
    let p := cmonicG (cgcdFFWf b d)
    let b' := cdivWf b p
    let d' := csubG (cdivWf d p) (cderivG b')
    if (cnormG b' : List QFunNZ).length < (cnormG b : List QFunNZ).length then
      p :: cSqfreeYunFFgoWf b' d'
    else [p]   -- unreachable on a real run (the non-constant `p` drops the `t`-degree)
termination_by (cnormG b).length
decreasing_by assumption

/-- **Fuel-free Yun squarefree factorization over ℚ(x)[t]** `cSqfreeYunFFWf p = [p₁, p₂, …, pₘ]`: the
fuel-free companion of `cSqfreeYunFF`. With `g = cgcdFFWf p (cderivG p)`, `b₁ = cdivWf p g`, `d₁ = cderivG
p/g − b₁'`, runs the fuel-free Yun loop `cSqfreeYunFFgoWf b₁ d₁`. `p` is associate to `∏ᵢ pᵢ^i`. Every gcd
is the fuel-free fraction-free `cgcdFFWf`, every exact division the fuel-free `cdivWf` — **no fuel at
runtime**, `native_decide`-able over the noncomputable-`CFieldSpec` tower `QFunNZ` (ℚ(x)). -/
def cSqfreeYunFFWf (p : CPolyG QFunNZ) : List (CPolyG QFunNZ) :=
  let g := cgcdFFWf p (cderivG p)
  let b1 := cdivWf p g
  let d1 := csubG (cdivWf (cderivG p) g) (cderivG b1)
  cSqfreeYunFFgoWf b1 d1

end CPolyG

/-! ### Bridge of `cSqfreeYunFFWf` to the fuel'd `cSqfreeYunFF`

`cSqfreeYunFFgo fuel fo b d`/`cSqfreeYunFF fuel p` call `cgcdFF fuel`/`cdivG fuel` for the per-step
gcd/divisions, with the outer Yun counter `fo` budgeting the multiplicities. The fuel-free companions
substitute the WF leaves `cgcdFFWf`/`cdivWf`. The bridge needs, at each Yun step, that those WF leaves
match `cgcdFF fuel`/`cdivG fuel` (a `CSqfreeYunStepReg fuel b d` node bundle — the `cgcdFF fuel b d` call
is node-regular and the dividend lengths are bounded by `fuel` for the exact divisions), and that the
running poly strictly drops (the structural guard, from the non-constant emitted `p`). These hold along a
real Yun descent; the bundle `CSqfreeYunGoRegular fo fuel b d` packages them, recursing on the outer Yun
counter `fo` exactly as `cSqfreeYunFFgo` (so the regularity is a plain structural recursion, no
well-founded measure). -/

/-- **Per-Yun-step node-regularity bundle** `CSqfreeYunStepReg fuel b d`: the transparent preconditions for
one Yun step's fuel-free leaves to match the fuel'd ops at the global step fuel `fuel` — the gcd call
`cgcdFF fuel b d` is node-regular (`CgcdFFNodeReg`), the running `b` is short enough for the exact division
`cdivWf b p = cdivG fuel b p` (`(cnormG b).length ≤ fuel`), and the auxiliary `d/p` division is reduced
(`(cnormG d).length ≤ fuel`). -/
structure CSqfreeYunStepReg (fuel : ℕ) (b d : CPolyG QFunNZ) : Prop where
  /-- the gcd call `cgcdFF fuel b d` is node-regular. -/
  hgcd : CgcdFFNodeReg fuel b d
  /-- the running poly `b` is short enough for its exact division to be reduced. -/
  hblen : (cnormG b : List QFunNZ).length ≤ fuel
  /-- the auxiliary dividend `d` is short enough for its exact division to be reduced. -/
  hdlen : (cnormG d : List QFunNZ).length ≤ fuel

/-- **Per-run Yun-loop regularity bundle** `CSqfreeYunGoRegular fuel b d`: mirrors the `cSqfreeYunFFgo`
recursion as an inductive predicate — `stop` at a constant running poly `b` (`cdegG b = 0`, the loop ends),
or `step` when the step is node-regular (`CSqfreeYunStepReg fuel b d`), the running poly strictly drops,
and the same holds recursively on the quotient `b' = cdivWf b (cmonicG (cgcdFF fuel b d))` and the updated
`d'`. The transparent per-node preconditions a real Yun run on a squarefree-decomposable input satisfies. -/
inductive CSqfreeYunGoRegular (fuel : ℕ) : CPolyG QFunNZ → CPolyG QFunNZ → Prop
  /-- terminal node: the running poly `b` is constant, the loop stops. -/
  | stop {b d : CPolyG QFunNZ} (hdeg : cdegG b = 0) : CSqfreeYunGoRegular fuel b d
  /-- recursive node: the step is node-regular, the running poly strictly drops, recurse on the quotient. -/
  | step {b d : CPolyG QFunNZ} (hstep : CSqfreeYunStepReg fuel b d)
      (hguard : (cnormG (CPolyG.cdivWf b (cmonicG (CPolyG.cgcdFF fuel b d))) : List QFunNZ).length
        < (cnormG b : List QFunNZ).length)
      (hrec : CSqfreeYunGoRegular fuel (CPolyG.cdivWf b (cmonicG (CPolyG.cgcdFF fuel b d)))
        (csubG (CPolyG.cdivWf d (cmonicG (CPolyG.cgcdFF fuel b d)))
          (cderivG (CPolyG.cdivWf b (cmonicG (CPolyG.cgcdFF fuel b d)))))) :
      CSqfreeYunGoRegular fuel b d

namespace CPolyG

/-- **Bridge — `cSqfreeYunFFgoWf` equals `cSqfreeYunFFgo` at any sufficient outer fuel.** For an outer Yun
counter `fo` *strictly* exceeding the running poly's `t`-length (`(cnormG b).length < fo`) and a regular
Yun run (`CSqfreeYunGoRegular fuel b d`), `cSqfreeYunFFgoWf b d = cSqfreeYunFFgo fuel fo b d`. The fuel
bounds live only here; `cSqfreeYunFFgoWf` carries none. By induction on the outer counter `fo`, mirroring
`cSplitFactorFastWf_eq`: at a constant `b` both stop; else the step's WF leaves match the fuel'd ops
(`cgcdFFWf_eq_node`, `cdivWf_eq_cdivmodG_succ`), the structural guard holds, and the *strict* `< fo` keeps
the recursion strictly above the fuel-exhaustion base case (`fo = 0` is vacuous, `(cnormG b).length < 0`).
The IH applies to the quotient `b'` (its strictly smaller length keeps `< fo` after one decrement). -/
theorem cSqfreeYunFFgoWf_eq : ∀ (fo fuel : ℕ) (b d : CPolyG QFunNZ),
    (cnormG b : List QFunNZ).length < fo → CSqfreeYunGoRegular fuel b d →
      cSqfreeYunFFgoWf b d = cSqfreeYunFFgo fuel fo b d := by
  intro fo
  induction fo with
  | zero =>
    -- vacuous: `(cnormG b).length < 0` is impossible
    intro _ b _ hlen _
    exact absurd hlen (Nat.not_lt_zero _)
  | succ fo ih =>
    intro fuel b d hlen hreg
    rw [cSqfreeYunFFgoWf.eq_def, cSqfreeYunFFgo]
    by_cases hdeg : cdegG b = 0
    · -- constant running poly: both return `[]`
      simp only [if_pos hdeg]
    · -- recursive step: extract the per-step regularity
      rcases hreg with hc | ⟨hstep, hguardReg, hrecReg⟩
      · exact absurd hc hdeg
      obtain ⟨hgcd, hblen, hdlen⟩ := hstep
      -- the gcd's WF leaf matches the fuel'd `cgcdFF`
      have hgeq : cgcdFFWf b d = CPolyG.cgcdFF fuel b d := cgcdFFWf_eq_node fuel b d hgcd
      -- abbreviate the emitted factor (the fuel'd `cgcdFF`-shape, which the WF guard/rec already use)
      set p := cmonicG (CPolyG.cgcdFF fuel b d) with hp
      -- the running and auxiliary quotients' WF leaves match the fuel'd `cdivG`
      have hbq : cdivWf b p = CPolyG.cdivG fuel b p := by
        rw [cdivWf, cdivmodWf_eq_of_fuel fuel b p hblen, cdivG]
      have hdq : cdivWf d p = CPolyG.cdivG fuel d p := by
        rw [cdivWf, cdivmodWf_eq_of_fuel fuel d p hdlen, cdivG]
      -- the WF loop's `cmonicG (cgcdFFWf b d)` is the fuel'd `p`; rewrite both sides into `cdivWf`/`p` form
      simp only [if_neg hdeg, hgeq, ← hp, ← hbq, ← hdq]
      -- the structural guard holds (running poly strictly drops); `hguardReg` already in `cdivWf b p` form
      rw [if_pos hguardReg]
      -- apply the IH on the quotient (length strictly drops, so `< fo` after the decrement)
      have hlen' : (cnormG (CPolyG.cdivWf b p) : List QFunNZ).length < fo := by omega
      rw [ih fuel (CPolyG.cdivWf b p)
        (csubG (CPolyG.cdivWf d p) (cderivG (CPolyG.cdivWf b p))) hlen' hrecReg]

end CPolyG

/-! ### Entry-level bridge `cSqfreeYunFFWf = cSqfreeYunFF` and transported correctness

`cSqfreeYunFF fuel p` runs the preamble `g = cgcdFF fuel p (cderivG p)`, `b₁ = cdivG fuel p g`, `d₁ =
cderivG p/g − b₁'`, then `cSqfreeYunFFgo fuel fuel b₁ d₁`. The fuel-free `cSqfreeYunFFWf p` substitutes
`cgcdFFWf`/`cdivWf` in the preamble and the fuel-free loop. The entry bundle `CSqfreeYunRegular fuel p`
covers the preamble's node-regularity (the `cgcdFF p (cderivG p)` call and the two `cdivG` lengths) plus
the loop run-regularity `CSqfreeYunGoRegular fuel b₁ d₁`. The bridge feeds the loop bridge with the
self-sufficient outer fuel `fo = fuel` (strict, since `(cnormG b₁).length < fuel`). -/

/-- **Per-run Yun entry regularity bundle** `CSqfreeYunRegular fuel p`: the preamble node-regularity for
`cSqfreeYunFFWf p` to match `cSqfreeYunFF fuel p` — the gcd call `cgcdFF fuel p (cderivG p)` is node-regular,
the two preamble divisions `cdivG fuel p g` / `cdivG fuel (cderivG p) g` are reduced (`(cnormG p).length ≤
fuel`, `(cnormG (cderivG p)).length ≤ fuel`), the running list `b₁ = cdivG fuel p g` is strictly shorter
than the outer fuel (`(cnormG b₁).length < fuel`), and the resulting loop is a regular run
(`CSqfreeYunGoRegular fuel b₁ d₁`). -/
structure CSqfreeYunRegular (fuel : ℕ) (p : CPolyG QFunNZ) : Prop where
  /-- the preamble gcd `cgcdFF fuel p (cderivG p)` is node-regular. -/
  hgcd : CgcdFFNodeReg fuel p (cderivG p)
  /-- `p` is short enough for the running division `cdivG fuel p g` to be reduced. -/
  hplen : (cnormG p : List QFunNZ).length ≤ fuel
  /-- `cderivG p` is short enough for the auxiliary division `cdivG fuel (cderivG p) g` to be reduced. -/
  hdplen : (cnormG (cderivG p) : List QFunNZ).length ≤ fuel
  /-- the running list `b₁ = cdivG fuel p g` is strictly shorter than the outer fuel. -/
  hb1len : (cnormG (CPolyG.cdivWf p (cgcdFFWf p (cderivG p))) : List QFunNZ).length < fuel
  /-- the loop on `(b₁, d₁)` is a regular run. -/
  hloop : CSqfreeYunGoRegular fuel (CPolyG.cdivWf p (cgcdFFWf p (cderivG p)))
    (csubG (CPolyG.cdivWf (cderivG p) (cgcdFFWf p (cderivG p)))
      (cderivG (CPolyG.cdivWf p (cgcdFFWf p (cderivG p)))))

namespace CPolyG

/-- **Bridge — `cSqfreeYunFFWf` equals `cSqfreeYunFF` at any sufficient fuel.** Under a regular Yun run
(`CSqfreeYunRegular fuel p`), `cSqfreeYunFFWf p = cSqfreeYunFF fuel p`. The fuel bounds live only here;
`cSqfreeYunFFWf` carries none. The preamble's WF leaves (`cgcdFFWf`/`cdivWf`) match the fuel'd ops
(`cgcdFFWf_eq_node`, `cdivmodWf_eq_of_fuel`), and the loop bridge `cSqfreeYunFFgoWf_eq` runs at the
self-sufficient outer fuel `fo = fuel`. -/
theorem cSqfreeYunFFWf_eq (fuel : ℕ) (p : CPolyG QFunNZ) (hreg : CSqfreeYunRegular fuel p) :
    cSqfreeYunFFWf p = CPolyG.cSqfreeYunFF fuel p := by
  obtain ⟨hgcd, hplen, hdplen, hb1len, hloop⟩ := hreg
  rw [cSqfreeYunFFWf, CPolyG.cSqfreeYunFF]
  -- the preamble gcd `g` matches
  have hgeq : cgcdFFWf p (cderivG p) = CPolyG.cgcdFF fuel p (cderivG p) :=
    cgcdFFWf_eq_node fuel p (cderivG p) hgcd
  set g := CPolyG.cgcdFF fuel p (cderivG p) with hg
  -- the two preamble divisions match
  have hb1q : cdivWf p g = CPolyG.cdivG fuel p g := by
    rw [cdivWf, cdivmodWf_eq_of_fuel fuel p g hplen, cdivG]
  have hdivdpq : cdivWf (cderivG p) g = CPolyG.cdivG fuel (cderivG p) g := by
    rw [cdivWf, cdivmodWf_eq_of_fuel fuel (cderivG p) g hdplen, cdivG]
  -- rewrite the WF entry into the fuel'd `(b₁, d₁)`
  rw [hgeq]
  -- the loop bridge at the self-sufficient outer fuel `fo = fuel`
  have hb1len' : (cnormG (cdivWf p g) : List QFunNZ).length < fuel := by rw [hgeq] at hb1len; exact hb1len
  rw [hgeq] at hloop
  rw [cSqfreeYunFFgoWf_eq fuel fuel (cdivWf p g)
    (csubG (cdivWf (cderivG p) g) (cderivG (cdivWf p g))) hb1len' hloop, hb1q, hdivdpq]

end CPolyG

-- The fuel-free Yun-loop/entry bridges carry only the standard axioms (no `native` axiom): the
-- `native_decide` smoke tests below carry `Lean.ofReduceBool` separately.
#print axioms CPolyG.cSqfreeYunFFgoWf_eq
#print axioms CPolyG.cSqfreeYunFFWf_eq

/-! ### `native_decide` smoke tests for `cSqfreeYunFFWf`

The whole fuel-free Yun squarefree factorization loop executes in native code over the
noncomputable-`CFieldSpec` tower `QFunNZ` (ℚ(x)) — `cSqfreeYunFFWf` carries no fuel and no noncomputable
bridge into the compiled body. Re-runs the engine's `(t−1)²(t−2)` sanity and Bronstein Example 3.5.2. -/

namespace CPolyG

open QFunNZ

/-- **Sanity (fuel-free Yun factorization)**: the squarefree factorization in `t` of `(t−1)²(t−2)` is two
factors `[p₁, p₂]` of `t`-degrees `[1, 1]` (multiplicities `1, 2`) — the fuel-free own-loop runs
end-to-end over ℚ(x)[t]. -/
example : (CPolyG.cSqfreeYunFFWf sqfreeSanityP).map CPolyG.cdegG = [1, 1] := by native_decide

/-- `cSqfreeYunFFWf` agrees with the fuel'd `cSqfreeYunFF` on `(t−1)²(t−2)` (the factor-degree lists
match). -/
example :
    (CPolyG.cSqfreeYunFFWf sqfreeSanityP).map CPolyG.cdegG
      = (CPolyG.cSqfreeYunFF 8 sqfreeSanityP).map CPolyG.cdegG := by native_decide

/-- **Example 3.5.2** (Bronstein §3.5, p.102) Yun split COMPUTES fuel-free: `cSqfreeYunFFWf` on the
degree-5 `p` returns the squarefree factorization `p = p₁ p₂²` with `t`-degrees `[3, 1]` — the own-loop
runs end-to-end with **no fuel at runtime**. -/
example :
    (CPolyG.cSqfreeYunFFWf splitFastExample351P).map CPolyG.cdegG = [3, 1] := by native_decide

end CPolyG

/-! ### Target B — the fuel-free `SplitSquarefreeFactor` `cSplitSquarefreeFactorFastWf`

`cSplitSquarefreeFactorFast Dt fuel p` (Bronstein §3.5, p.102) composes `cSqfreeYunFF` with a per-factor
split: `(p₁,…,pₘ) ← cSqfreeYunFF p`, then for each `pᵢ` the special part `Sᵢ = cgcdFF pᵢ (cmonomialDeriv
Dt pᵢ)` and the normal part `Nᵢ = pᵢ/Sᵢ`. The fuel-free companion substitutes `cSqfreeYunFFWf` (Target A)
and the fuel-free leaves `cgcdFFWf`/`cdivWf` for the per-factor work; the outer `.map` is structural
(fuel-free already). The per-Yun-factor split correctness `cSqfreeFactor_isSplittingFactorizationGen`
(`ComputableCanonicalRepCorrect`) applies to each output factor unchanged (the WF `(Nᵢ, Sᵢ)` reads through
`toPolyG` as `csqfreeNormal`/`csqfreeSpecial` exactly, since `cdivWf = cdivG` and `cgcdFFWf = cgcdFF`). -/

namespace CPolyG

/-- **Fuel-free per-Yun-factor split step** `csqfreeSplitStepWf Dt pi = (Nᵢ, Sᵢ)`: the special part
`Sᵢ = cgcdFFWf pi (cmonomialDeriv Dt pi)` (via the DIFFERENTIAL `cmonomialDeriv`) and the normal part
`Nᵢ = cdivWf pi Sᵢ`, both fuel-free. The fuel-free companion of one `cSplitSquarefreeFactorFast` map step. -/
def csqfreeSplitStepWf (Dt : CPolyG QFunNZ) (pi : CPolyG QFunNZ) : CPolyG QFunNZ × CPolyG QFunNZ :=
  let Si := cgcdFFWf pi (cmonomialDeriv Dt pi)
  let Ni := cdivWf pi Si
  (Ni, Si)

/-- **Fuel-free `SplitSquarefreeFactor`** (Bronstein §3.5, p.102) `cSplitSquarefreeFactorFastWf Dt p =
((N₁,…,Nₘ), (S₁,…,Sₘ))`: the fuel-free companion of `cSplitSquarefreeFactorFast`. First `(p₁,…,pₘ) ←
cSqfreeYunFFWf p` (fuel-free Yun squarefree factorization); then per factor the fuel-free split step
`csqfreeSplitStepWf`. The outer `.map` is structural — **no fuel at runtime**, `native_decide`-able over
the noncomputable-`CFieldSpec` tower `QFunNZ` (ℚ(x)). -/
def cSplitSquarefreeFactorFastWf (Dt : CPolyG QFunNZ) (p : CPolyG QFunNZ) :
    List (CPolyG QFunNZ) × List (CPolyG QFunNZ) :=
  let ps := cSqfreeYunFFWf p
  let parts := ps.map (csqfreeSplitStepWf Dt)
  (parts.map Prod.fst, parts.map Prod.snd)

/-- **The fuel-free per-factor split step matches the fuel'd one** `csqfreeSplitStepWf Dt pi = (csqfreeNormal
Dt fuel pi, csqfreeSpecial Dt fuel pi)`, under a per-factor split-regular node (`CSqfreeFactorRegular Dt
fuel pi`): the special `cgcdFFWf` matches `cgcdFF fuel` (`cgcdFFWf_eq_node`) and the normal `cdivWf` matches
`cdivG fuel` (`cdivmodWf_eq_of_fuel` with the dividend length bound). -/
theorem csqfreeSplitStepWf_eq (Dt : CPolyG QFunNZ) (fuel : ℕ) (pi : CPolyG QFunNZ)
    (hreg : CSqfreeFactorRegular Dt fuel pi) :
    csqfreeSplitStepWf Dt pi = (csqfreeNormal Dt fuel pi, csqfreeSpecial Dt fuel pi) := by
  obtain ⟨hgcdreg, hfuel⟩ := hreg
  rw [csqfreeSplitStepWf]
  -- the special part
  have hSeq : cgcdFFWf pi (cmonomialDeriv Dt pi) = csqfreeSpecial Dt fuel pi :=
    cgcdFFWf_eq_node fuel pi (cmonomialDeriv Dt pi) hgcdreg
  -- the normal part: `cdivWf pi Si = cdivG fuel pi Si`
  rw [hSeq]
  have hNeq : cdivWf pi (csqfreeSpecial Dt fuel pi)
      = CPolyG.cdivG fuel pi (csqfreeSpecial Dt fuel pi) := by
    rw [cdivWf, cdivmodWf_eq_of_fuel fuel pi (csqfreeSpecial Dt fuel pi) hfuel, cdivG]
  rw [hNeq]

end CPolyG

/-- **Bridge — `cSplitSquarefreeFactorFastWf` equals `cSplitSquarefreeFactorFast` at any sufficient fuel.**
Under a regular Yun entry (`CSqfreeYunRegular fuel p`) and per-factor split-regularity of every Yun factor
(`∀ pi ∈ cSqfreeYunFFWf p, CSqfreeFactorRegular Dt fuel pi`), `cSplitSquarefreeFactorFastWf Dt p =
cSplitSquarefreeFactorFast Dt fuel p`. The fuel bounds live only here; the WF op carries none. The Yun list
matches (Target A `cSqfreeYunFFWf_eq`) and each per-factor split step matches (`csqfreeSplitStepWf_eq`),
folded over the `.map`. -/
theorem cSplitSquarefreeFactorFastWf_eq (Dt : CPolyG QFunNZ) (fuel : ℕ) (p : CPolyG QFunNZ)
    (hyun : CSqfreeYunRegular fuel p)
    (hfac : ∀ pi ∈ CPolyG.cSqfreeYunFFWf p, CSqfreeFactorRegular Dt fuel pi) :
    CPolyG.cSplitSquarefreeFactorFastWf Dt p = CPolyG.cSplitSquarefreeFactorFast Dt fuel p := by
  rw [CPolyG.cSplitSquarefreeFactorFastWf, CPolyG.cSplitSquarefreeFactorFast]
  -- the Yun lists match (Target A)
  have hyuneq : CPolyG.cSqfreeYunFFWf p = CPolyG.cSqfreeYunFF fuel p :=
    CPolyG.cSqfreeYunFFWf_eq fuel p hyun
  -- the per-factor split maps agree element-wise on the (shared) Yun list
  have hmapeq : (CPolyG.cSqfreeYunFFWf p).map (CPolyG.csqfreeSplitStepWf Dt)
      = (CPolyG.cSqfreeYunFF fuel p).map (fun pi =>
          let Si := CPolyG.cgcdFF fuel pi (cmonomialDeriv Dt pi)
          let Ni := CPolyG.cdivG fuel pi Si
          (Ni, Si)) := by
    rw [hyuneq]
    refine List.map_congr_left (fun pi hpi => ?_)
    -- `pi` lies in the WF Yun list (= the fuel'd one), so it is split-regular
    have hpireg : CSqfreeFactorRegular Dt fuel pi := hfac pi (by rw [hyuneq]; exact hpi)
    have := CPolyG.csqfreeSplitStepWf_eq Dt fuel pi hpireg
    rw [this]
  rw [hmapeq]

-- The fuel-free `SplitSquarefreeFactor` bridge carries only the standard axioms (no `native` axiom).
#print axioms cSplitSquarefreeFactorFastWf_eq

/-! ### Per-Yun-factor splitting-factorization correctness of `cSplitSquarefreeFactorFastWf`

For a **squarefree** Yun factor `pᵢ`, the fuel-free per-factor split `csqfreeSplitStepWf Dt pᵢ = (Nᵢ, Sᵢ)`
is a book-faithful splitting factorization `IsSplittingFactorizationGen (toPolyG pᵢ) (toPolyG Sᵢ) (toPolyG
Nᵢ)` — directly from `cSqfreeFactor_isSplittingFactorizationGen` (`ComputableCanonicalRepCorrect`), since
`csqfreeSplitStepWf` reads through `toPolyG` as `(csqfreeNormal, csqfreeSpecial)` (`csqfreeSplitStepWf_eq`),
fuel-free. -/

/-- **The fuel-free per-Yun-factor split is a book-faithful splitting factorization** over ℚ(x): for a
**squarefree** `toPolyG pᵢ ≠ 0` and a split-regular factor (`CSqfreeFactorRegular`), the fuel-free
`(Nᵢ, Sᵢ) = csqfreeSplitStepWf Dt pᵢ` satisfies `IsSplittingFactorizationGen (toPolyG pᵢ) (toPolyG Sᵢ)
(toPolyG Nᵢ)` w.r.t. the monomial derivation `D` (`Dt = toPolyG Dt`). Transported from
`cSqfreeFactor_isSplittingFactorizationGen` through `csqfreeSplitStepWf_eq`; the WF version only removes the
fuel from the runtime. -/
theorem csqfreeSplitStepWf_isSplittingFactorizationGen (Dt : CPolyG QFunNZ) (fuel : ℕ) (pi : CPolyG QFunNZ)
    (hp : toPolyG pi ≠ 0) (hsf : Squarefree (toPolyG pi)) (hreg : CSqfreeFactorRegular Dt fuel pi) :
    @IsSplittingFactorizationGen _ _ ⟨Differential.implicitDeriv (toPolyG Dt)⟩
      (toPolyG pi)
      (toPolyG (CPolyG.csqfreeSplitStepWf Dt pi).2)
      (toPolyG (CPolyG.csqfreeSplitStepWf Dt pi).1) := by
  rw [CPolyG.csqfreeSplitStepWf_eq Dt fuel pi hreg]
  exact cSqfreeFactor_isSplittingFactorizationGen Dt fuel pi hp hsf hreg

#print axioms csqfreeSplitStepWf_isSplittingFactorizationGen

/-! ### Restatement against the intended wording (anonymous `example`) -/

-- The headline (Target B): for one **squarefree** Yun factor `pᵢ`, the fuel-free split
-- `csqfreeSplitStepWf Dt pᵢ = (Nᵢ, Sᵢ)`, read over ℚ(x) = `RatFunc ℚ`, returns a book-faithful splitting
-- factorization of `toPolyG pᵢ` — `pᵢ = Sᵢ·Nᵢ`, `Sᵢ` special, every squarefree factor of `Nᵢ` normal —
-- under the same per-node preconditions a real run satisfies, **with no fuel at runtime**.
example (Dt : CPolyG QFunNZ) (fuel : ℕ) (pi : CPolyG QFunNZ) (hp : toPolyG pi ≠ 0)
    (hsf : Squarefree (toPolyG pi)) (hreg : CSqfreeFactorRegular Dt fuel pi) :
    @IsSplittingFactorizationGen _ _ ⟨Differential.implicitDeriv (toPolyG Dt)⟩
      (toPolyG pi)
      (toPolyG (CPolyG.csqfreeSplitStepWf Dt pi).2)
      (toPolyG (CPolyG.csqfreeSplitStepWf Dt pi).1) :=
  csqfreeSplitStepWf_isSplittingFactorizationGen Dt fuel pi hp hsf hreg

/-! ### `native_decide` smoke tests for `cSplitSquarefreeFactorFastWf` (Bronstein Example 3.5.2) -/

namespace CPolyG

/-- **Example 3.5.2 factor degrees, fuel-free** — `cSplitSquarefreeFactorFastWf` on the degree-5 `p`
returns `N`-factor `t`-degrees `[1, 1]` and `S`-factor `t`-degrees `[2, 0]`, matching Bronstein's
`N₁ = 4x²(t−1)`, `N₂ = xt−1`, `S₁ = t²+(1/x)t−(2x−1)/(4x²)`, `S₂ = 1` — the whole composition runs with
**no fuel at runtime**. -/
example :
    (((CPolyG.cSplitSquarefreeFactorFastWf splitFastExample351Dt splitFastExample351P).1).map
        CPolyG.cdegG,
     ((CPolyG.cSplitSquarefreeFactorFastWf splitFastExample351Dt splitFastExample351P).2).map
        CPolyG.cdegG) = ([1, 1], [2, 0]) := by native_decide

/-- **Example 3.5.2 normal part is the book's `pₙ`, fuel-free** — the `N`-factors recombine (by
multiplicity) to `4x²(t−1)(xt−1)²` (monic), via `cisZeroG` of the difference over ℚ(x)[t]. -/
example :
    CPolyG.cisZeroG (CPolyG.csubG
      (CPolyG.cmonicG (splitSquarefreeFastRecombine
        (CPolyG.cSplitSquarefreeFactorFastWf splitFastExample351Dt splitFastExample351P).1))
      (CPolyG.cmonicG splitSquarefreeFastEx352Pn)) = true := by native_decide

/-- **Example 3.5.2 special part is the book's `pₛ`, fuel-free** — the `S`-factors recombine (by
multiplicity) to `t²+(1/x)t−(2x−1)/(4x²)` (monic), via `cisZeroG` of the difference over ℚ(x)[t]. -/
example :
    CPolyG.cisZeroG (CPolyG.csubG
      (CPolyG.cmonicG (splitSquarefreeFastRecombine
        (CPolyG.cSplitSquarefreeFactorFastWf splitFastExample351Dt splitFastExample351P).2))
      (CPolyG.cmonicG splitSquarefreeFastEx352Ps)) = true := by native_decide

/-- `cSplitSquarefreeFactorFastWf` agrees with the fuel'd `cSplitSquarefreeFactorFast` on Example 3.5.2's
`p` (the `N`/`S` factor-degree lists match). -/
example :
    (((CPolyG.cSplitSquarefreeFactorFastWf splitFastExample351Dt splitFastExample351P).1).map
        CPolyG.cdegG,
     ((CPolyG.cSplitSquarefreeFactorFastWf splitFastExample351Dt splitFastExample351P).2).map
        CPolyG.cdegG)
      = (((CPolyG.cSplitSquarefreeFactorFast splitFastExample351Dt 8 splitFastExample351P).1).map
          CPolyG.cdegG,
         ((CPolyG.cSplitSquarefreeFactorFast splitFastExample351Dt 8 splitFastExample351P).2).map
          CPolyG.cdegG) := by native_decide

end CPolyG

/-! ### Target C — the fuel-free canonical representation `canonicalRepresentationFastWf`

`canonicalRepresentationFast Dt fuel a d` (Bronstein §3.5, p.103) — the §3.5 capstone `cIntegrate`
consumes — composes the Euclidean division `cdivmodG fuel a d`, the denominator split `cSplitFactorFast Dt
fuel d`, the Bézout cofactors `cbezoutOne fuel dₙ dₛ` (via `cgcdExtG fuel`), and the Bézout split
`cextendedEuclideanSplit fuel dₙ dₛ r u w` (via `cdivmodG fuel`). The fuel-free companion substitutes the
WF leaves throughout: `cdivmodWf`, `cSplitFactorFastWf` (Target B of `ComputableWellFounded3`), the
fuel-free Bézout helpers `cbezoutOneWf`/`cextendedEuclideanSplitWf` (via the fuel-free extended-Euclid
`cgcdWf`). Every sub-op is a WF leaf, so the capstone is **fuel-free end-to-end**. The abstract
reconstruction `canonicalRepFast_reconstructs` (`ComputableCanonicalRepCorrect`) transports through the
bridge. -/

namespace CPolyG

variable {α : Type*} [CField α]

/-- **Fuel-free Bézout cofactors** `cbezoutOneWf a b = (u, w)` with `u·a + w·b = 1` for coprime `a, b`: the
fuel-free companion of `cbezoutOne`. Runs the **fuel-free** extended-Euclid `cgcdWf` to get `(g, s, t)` with
`s·a + t·b = g` (a nonzero constant, since `a, b` coprime), then rescales by `g⁻¹` — **no fuel at runtime**. -/
def cbezoutOneWf (a b : CPolyG α) : CPolyG α × CPolyG α :=
  let (g, s, t) := cgcdWf a b
  let ginv := CField.inv (cleadG g)
  (cscaleG ginv s, cscaleG ginv t)

/-- **Fuel-free Bézout split** `cextendedEuclideanSplitWf dₙ dₛ r u w = (b, c)`: the fuel-free companion of
`cextendedEuclideanSplit`. With a Bézout pair `u·dₙ + w·dₛ = 1`, returns `b = (u·r) mod dₛ` and `c = w·r +
(u·r div dₛ)·dₙ` via the **fuel-free** `cdivmodWf` — **no fuel at runtime**. -/
def cextendedEuclideanSplitWf (dn ds r u w : CPolyG α) : CPolyG α × CPolyG α :=
  let ur := cmulG u r
  let (quo, rem) := cdivmodWf ur ds
  (rem, caddG (cmulG w r) (cmulG quo dn))

variable [CFieldSpec α]

/-- **`cbezoutOneWf` equals the fuel'd `cbezoutOne` at any sufficient fuel** — with `(cnormG a).length ≤
fuel` and `(cnormG b).length < fuel`, `cbezoutOneWf a b = cbezoutOne fuel a b`, since the only fuel'd
sub-op `cgcdExtG` is bridged by `cgcdWf_eq_of_fuel`. -/
theorem cbezoutOneWf_eq_of_fuel (fuel : ℕ) (a b : CPolyG α)
    (ha : (cnormG a : List α).length ≤ fuel) (hb : (cnormG b : List α).length < fuel) :
    cbezoutOneWf a b = CPolyG.cbezoutOne fuel a b := by
  rw [cbezoutOneWf, CPolyG.cbezoutOne, cgcdWf_eq_of_fuel fuel a b ha hb]

/-- **`cextendedEuclideanSplitWf` equals the fuel'd `cextendedEuclideanSplit` at any sufficient fuel** —
with `(cnormG (cmulG u r)).length ≤ fuel`, `cextendedEuclideanSplitWf dn ds r u w = cextendedEuclideanSplit
fuel dn ds r u w`, since the only fuel'd sub-op `cdivmodG` is bridged by `cdivmodWf_eq_of_fuel`. -/
theorem cextendedEuclideanSplitWf_eq_of_fuel (fuel : ℕ) (dn ds r u w : CPolyG α)
    (hur : (cnormG (cmulG u r) : List α).length ≤ fuel) :
    cextendedEuclideanSplitWf dn ds r u w = CPolyG.cextendedEuclideanSplit fuel dn ds r u w := by
  rw [cextendedEuclideanSplitWf, CPolyG.cextendedEuclideanSplit,
    cdivmodWf_eq_of_fuel fuel (cmulG u r) ds hur]

end CPolyG

namespace CPolyG

/-- **Fuel-free `CanonicalRepresentation`** (Bronstein §3.5, p.103) over the tower ℚ(x)[t] — the §3.5
capstone `cIntegrate` consumes — `canonicalRepresentationFastWf Dt a d = (fₚ, fₛ, fₙ) = (q, (b, dₛ), (c,
dₙ))` for `f = a/d` (`d` monic). The fuel-free companion of `canonicalRepresentationFast`: divide
`a = q·d + r` (`cdivmodWf`); split the denominator `d = dₛ·dₙ` (`cSplitFactorFastWf`, fraction-free);
Bézout-split `r` over the coprime `(dₙ, dₛ)` (`cextendedEuclideanSplitWf` with `cbezoutOneWf`). Every sub-op
is a WF leaf — **no fuel at runtime**, `native_decide`-able over the tower `QFunNZ`. Stated with `.1`/`.2`
projections (no `let`-destructuring) so the bridge `canonicalRepresentationFastWf_eq` rewrites cleanly. -/
def canonicalRepresentationFastWf (Dt : CPolyG QFunNZ) (a d : CPolyG QFunNZ) :
    CPolyG QFunNZ × (CPolyG QFunNZ × CPolyG QFunNZ) × (CPolyG QFunNZ × CPolyG QFunNZ) :=
  let qr := cdivmodWf a d
  let dnds := cSplitFactorFastWf Dt d
  let uw := cbezoutOneWf dnds.1 dnds.2
  let bc := cextendedEuclideanSplitWf dnds.1 dnds.2 qr.2 uw.1 uw.2
  (qr.1, (bc.1, dnds.2), (bc.2, dnds.1))

end CPolyG

/-! ### Bridge of `canonicalRepresentationFastWf` to `canonicalRepresentationFast`, and transported reconstruction

The bridge substitutes each WF leaf for the fuel'd op: `cdivmodWf = cdivmodG fuel` (length bound),
`cSplitFactorFastWf = cSplitFactorFast fuel` (the WF3 bridge `cSplitFactorFastWf_eq`, *strict* `< fuel`),
`cbezoutOneWf = cbezoutOne fuel` (`cgcdWf` descent bounds), and `cextendedEuclideanSplitWf =
cextendedEuclideanSplit fuel` (the `u·r` length bound). The Wf-run bundle `CCanonicalRepFastWfRegular`
extends the abstract `CCanonicalRepFastRegular` (the gate `canonicalRepFast_reconstructs` carries) with the
transparent WF-leaf length bounds a real run meets. The reconstruction headline then transports
unconditionally over the bridge. -/

/-- **Per-run Wf bundle** `CCanonicalRepFastWfRegular Dt fuel a d`: the abstract reconstruction gate
`CCanonicalRepFastRegular` plus the transparent WF-leaf length bounds for `canonicalRepresentationFastWf` to
match `canonicalRepresentationFast fuel` — the dividend `a` is short enough for `cdivmodWf` (`(cnormG
a).length ≤ fuel`), fuel *strictly* exceeds the denominator `t`-degree (`(toPolyG d).natDegree < fuel`, the
`cSplitFactorFastWf_eq` strict bound), the split parts are short enough for `cgcdWf`'s descent
(`(cnormG dₙ).length ≤ fuel`, `(cnormG dₛ).length < fuel`), and the Bézout product `u·r` is short enough for
`cdivmodWf` (`(cnormG (cmulG u r)).length ≤ fuel`, with `(u, w) = cbezoutOneWf dₙ dₛ`, `r` the division
remainder). -/
structure CCanonicalRepFastWfRegular (Dt : CPolyG QFunNZ) (fuel : ℕ) (a d : CPolyG QFunNZ) : Prop where
  /-- the abstract reconstruction gate. -/
  habs : CCanonicalRepFastRegular Dt fuel a d
  /-- `a` is short enough for the Euclidean division `cdivmodWf a d` to be reduced. -/
  halen : (cnormG a : List QFunNZ).length ≤ fuel
  /-- fuel strictly exceeds the denominator `t`-degree (the `cSplitFactorFastWf_eq` strict bound). -/
  hdstrict : (toPolyG d).natDegree < fuel
  /-- the split normal part `dₙ` is short enough for `cgcdWf`'s descent. -/
  hdnlen : (cnormG (cSplitFactorFastWf Dt d).1 : List QFunNZ).length ≤ fuel
  /-- the split special part `dₛ` is *strictly* short enough for `cgcdWf`'s descent. -/
  hdslen : (cnormG (cSplitFactorFastWf Dt d).2 : List QFunNZ).length < fuel
  /-- the Bézout product `u·r` is short enough for the Bézout split's `cdivmodWf`. -/
  hurlen : (cnormG (cmulG (cbezoutOneWf (cSplitFactorFastWf Dt d).1 (cSplitFactorFastWf Dt d).2).1
    (cdivmodWf a d).2) : List QFunNZ).length ≤ fuel

namespace CPolyG

/-- **Bridge — `canonicalRepresentationFastWf` equals `canonicalRepresentationFast` at any sufficient
fuel.** Under a regular Wf run (`CCanonicalRepFastWfRegular Dt fuel a d`), `canonicalRepresentationFastWf Dt
a d = canonicalRepresentationFast Dt fuel a d`. The fuel bounds live only here; the WF capstone carries
none. Each WF leaf is bridged: `cdivmodWf` (`cdivmodWf_eq_of_fuel`), `cSplitFactorFastWf`
(`cSplitFactorFastWf_eq`), `cbezoutOneWf` (`cbezoutOneWf_eq_of_fuel`), `cextendedEuclideanSplitWf`
(`cextendedEuclideanSplitWf_eq_of_fuel`). -/
theorem canonicalRepresentationFastWf_eq (Dt : CPolyG QFunNZ) (fuel : ℕ) (a d : CPolyG QFunNZ)
    (hreg : CCanonicalRepFastWfRegular Dt fuel a d) :
    canonicalRepresentationFastWf Dt a d = CPolyG.canonicalRepresentationFast Dt fuel a d := by
  obtain ⟨habs, halen, hdstrict, hdnlen, hdslen, hurlen⟩ := hreg
  obtain ⟨hd, _, hsplitreg, _, _⟩ := habs
  -- the four WF-leaf bridges, each at the concrete fuel'd sub-results
  have hdiv : cdivmodWf a d = CPolyG.cdivmodG fuel a d := cdivmodWf_eq_of_fuel fuel a d halen
  have hsplit : cSplitFactorFastWf Dt d = CPolyG.cSplitFactorFast Dt fuel d :=
    cSplitFactorFastWf_eq Dt fuel d hd hdstrict hsplitreg
  have hbez : cbezoutOneWf (CPolyG.cSplitFactorFast Dt fuel d).1 (CPolyG.cSplitFactorFast Dt fuel d).2
      = CPolyG.cbezoutOne fuel (CPolyG.cSplitFactorFast Dt fuel d).1
          (CPolyG.cSplitFactorFast Dt fuel d).2 :=
    cbezoutOneWf_eq_of_fuel fuel _ _ (hsplit ▸ hdnlen) (hsplit ▸ hdslen)
  have hsplitSplit : cextendedEuclideanSplitWf (CPolyG.cSplitFactorFast Dt fuel d).1
        (CPolyG.cSplitFactorFast Dt fuel d).2 (CPolyG.cdivmodG fuel a d).2
        (CPolyG.cbezoutOne fuel (CPolyG.cSplitFactorFast Dt fuel d).1
          (CPolyG.cSplitFactorFast Dt fuel d).2).1
        (CPolyG.cbezoutOne fuel (CPolyG.cSplitFactorFast Dt fuel d).1
          (CPolyG.cSplitFactorFast Dt fuel d).2).2
      = CPolyG.cextendedEuclideanSplit fuel (CPolyG.cSplitFactorFast Dt fuel d).1
          (CPolyG.cSplitFactorFast Dt fuel d).2 (CPolyG.cdivmodG fuel a d).2
          (CPolyG.cbezoutOne fuel (CPolyG.cSplitFactorFast Dt fuel d).1
            (CPolyG.cSplitFactorFast Dt fuel d).2).1
          (CPolyG.cbezoutOne fuel (CPolyG.cSplitFactorFast Dt fuel d).1
            (CPolyG.cSplitFactorFast Dt fuel d).2).2 :=
    cextendedEuclideanSplitWf_eq_of_fuel fuel _ _ _ _ _
      (by
        -- `hurlen` is in WF-leaf form; carry it to the fuel'd `cbezoutOne`/`cdivmodG` form
        rw [hdiv] at hurlen; rw [hsplit] at hurlen; rw [hbez] at hurlen; exact hurlen)
  -- unfold MY def and rewrite every WF leaf to its fuel'd value (so MY side is pure fuel'd-op form)
  rw [canonicalRepresentationFastWf, hdiv, hsplit, hbez, hsplitSplit]
  -- now MY side is the fuel'd ops in `.1`/`.2` projection form; the fuel'd def's `let (q,r) := …`
  -- matches collapse to the same projection form (`Prod.eta`), so `rw` closes the goal by `rfl`.
  rw [CPolyG.canonicalRepresentationFast]

end CPolyG

open RatFunc in
/-- **`canonicalRepresentationFastWf` reconstructs `f`** (the §3.5 capstone, fuel-free), abstract
correctness over ℚ(x)(t): with the output `(q, (b, dₛ), (c, dₙ)) = canonicalRepresentationFastWf Dt a d`,
the three pieces recombine to `f = a/d` — `(q : ℚ(x)(t)) + b/dₛ + c/dₙ = a/d`. The same
`CCanonicalRepFastRegular` reconstruction gate the fuel'd `canonicalRepFast_reconstructs` carries (here
carried inside the Wf bundle `CCanonicalRepFastWfRegular`); the WF bridge `canonicalRepresentationFastWf_eq`
only removes the explicit `fuel` from the runtime. This is the §3.5 layer's payoff: the fuel-free capstone
`cIntegrate` consumes genuinely reconstructs `f`. -/
theorem canonicalRepFastWf_reconstructs (Dt : CPolyG QFunNZ) (fuel : ℕ) (a d : CPolyG QFunNZ)
    (hreg : CCanonicalRepFastWfRegular Dt fuel a d) :
    (let res := CPolyG.canonicalRepresentationFastWf Dt a d
      let q := res.1
      let b := res.2.1.1
      let ds := res.2.1.2
      let c := res.2.2.1
      let dn := res.2.2.2
      (algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (toPolyG q))
          + algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (toPolyG b)
              / algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (toPolyG ds)
          + algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (toPolyG c)
              / algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (toPolyG dn)
        = algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (toPolyG a)
            / algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (toPolyG d)) := by
  simp only [canonicalRepresentationFastWf_eq Dt fuel a d hreg]
  exact canonicalRepFast_reconstructs Dt fuel a d hreg.habs

-- The fuel-free §3.5 capstone reconstruction headline (`CCanonicalRepFastRegular`-gated, as the fuel'd
-- version) carries only the standard axioms (no `native` axiom).
#print axioms canonicalRepFastWf_reconstructs

/-! ### Restatement against the intended wording (anonymous `example`) -/

-- The headline (Target C, the payoff): `canonicalRepresentationFastWf Dt a d = (q, (b, dₛ), (c, dₙ))`,
-- read over ℚ(x)(t) = `RatFunc (RatFunc ℚ)`, reconstructs `f = a/d` — `q + b/dₛ + c/dₙ = a/d` — under the
-- transparent per-node Wf regularity a real run satisfies, **with no fuel at runtime**.
example (Dt : CPolyG QFunNZ) (fuel : ℕ) (a d : CPolyG QFunNZ)
    (hreg : CCanonicalRepFastWfRegular Dt fuel a d) :
    (algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ))
          (toPolyG (CPolyG.canonicalRepresentationFastWf Dt a d).1))
        + algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ))
              (toPolyG (CPolyG.canonicalRepresentationFastWf Dt a d).2.1.1)
            / algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ))
              (toPolyG (CPolyG.canonicalRepresentationFastWf Dt a d).2.1.2)
        + algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ))
              (toPolyG (CPolyG.canonicalRepresentationFastWf Dt a d).2.2.1)
            / algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ))
              (toPolyG (CPolyG.canonicalRepresentationFastWf Dt a d).2.2.2)
      = algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (toPolyG a)
          / algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (toPolyG d) :=
  canonicalRepFastWf_reconstructs Dt fuel a d hreg

/-! ### `native_decide` smoke test for `canonicalRepresentationFastWf`

The whole fuel-free canonical-representation capstone executes in native code over the
noncomputable-`CFieldSpec` tower `QFunNZ` (ℚ(x)) — `canonicalRepresentationFastWf` carries no fuel and no
noncomputable bridge into the compiled body. Re-runs the engine's `f = t³/((t−1)(t−2))` validation. -/

namespace CPolyG

open QFunNZ

/-- **`canonicalRepresentationFastWf` recombines to `f`, fuel-free** (`native_decide`): for `f =
t³/((t−1)(t−2))` over ℚ(x)(t) with `Dt = t − 1`, the computed parts `(q, (b, dₛ), (c, dₙ))` satisfy the
canonical identity `q + b/dₛ + c/dₙ = a/d` — checked, after clearing denominators, as
`(q·dₛ·dₙ + b·dₙ + c·dₛ)·d = a·(dₛ·dₙ)` via `cisZeroG` of the difference over ℚ(x)[t]. The whole fuel-free
§3.5 capstone runs end-to-end with **no fuel at runtime**. -/
example :
    (let res := CPolyG.canonicalRepresentationFastWf canonicalRepFastExampleDt
        canonicalRepFastExampleA canonicalRepFastExampleD
      let q := res.1
      let b := res.2.1.1
      let ds := res.2.1.2
      let c := res.2.2.1
      let dn := res.2.2.2
      let dsdn := CPolyG.cmulG ds dn
      let num := CPolyG.caddG (CPolyG.caddG (CPolyG.cmulG q dsdn) (CPolyG.cmulG b dn))
        (CPolyG.cmulG c ds)
      CPolyG.cisZeroG (CPolyG.csubG (CPolyG.cmulG num canonicalRepFastExampleD)
        (CPolyG.cmulG canonicalRepFastExampleA dsdn))) = true := by native_decide

/-- `canonicalRepresentationFastWf` agrees with the fuel'd `canonicalRepresentationFast` on the validation
`f` (the reduced-part denominator `dₛ` and simple-part denominator `dₙ` degree lists match). -/
example :
    ((CPolyG.cdegG (CPolyG.canonicalRepresentationFastWf canonicalRepFastExampleDt
        canonicalRepFastExampleA canonicalRepFastExampleD).2.1.2,
      CPolyG.cdegG (CPolyG.canonicalRepresentationFastWf canonicalRepFastExampleDt
        canonicalRepFastExampleA canonicalRepFastExampleD).2.2.2))
      = ((CPolyG.cdegG (CPolyG.canonicalRepresentationFast canonicalRepFastExampleDt 8
          canonicalRepFastExampleA canonicalRepFastExampleD).2.1.2,
        CPolyG.cdegG (CPolyG.canonicalRepresentationFast canonicalRepFastExampleDt 8
          canonicalRepFastExampleA canonicalRepFastExampleD).2.2.2)) := by native_decide

end CPolyG

end DeepWiki.SymbolicIntegration
