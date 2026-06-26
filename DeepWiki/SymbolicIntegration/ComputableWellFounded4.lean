import DeepWiki.SymbolicIntegration.ComputableWellFounded3
import DeepWiki.SymbolicIntegration.ComputableWellFoundedDioph
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

/-! ### Target A — the fuel-free Yun squarefree factorization `cSqfreeYunFFWf` (structural-counter loop)

`cSqfreeYunFFgo fuel fo b d` (`ComputableSplitSquarefree`) is Yun's main loop: stop when `b` is constant
(`cdegG b = 0`), else emit `p = cmonicG (cgcdFF fuel b d)`, recurse on `b' = b/p`, `d' = d/p − b'`. The
loop counts down on the **outer multiplicity counter** `fo`, **not** on a polynomial degree: at a *skipped*
multiplicity (e.g. `d = tⁿ`, whose squarefree factorization is `[1, …, 1, t]` with `n−1` *unit* factors)
the emitted `p` is the constant `[1]` and the running `b` and `d` are **unchanged** for several steps —
so there is no strictly-decreasing polynomial witness, and a degree-guarded well-founded loop would
**stop early** and return a *wrong* (truncated) factorization (e.g. `t² → [1]` instead of `[1, t]`).

The honest fuel-free companion therefore keeps the genuine termination measure — the multiplicity counter
— but computes a **sufficient bound for it once, internally, from the input** (`yunBound`), so the caller
still passes **no fuel**. The loop `cSqfreeYunFFgoWf fo b d` recurses *structurally* on `fo` (so
`decreasing_by` is automatic), threading the fuel-free leaves `cgcdFFWf`/`cdivWf` for each `p`/`b'`/`d'`;
the entry `cSqfreeYunFFWf p` instantiates `fo := yunBound p` (`= (cnormG p).length`, which bounds the max
multiplicity `≤ deg p` with slack, and also every intermediate `t`-length for the inner gcds/divisions). -/

/-- **Sufficient internal multiplicity-counter bound** `yunBound p := (cnormG p).length`: a provably
sufficient outer Yun counter for `cSqfreeYunFFgoWf` on `p`. Yun's outer loop runs one step per
multiplicity slot, and the max multiplicity of the squarefree factorization of `p` is `≤ deg p =
(cnormG p).length − 1 < (cnormG p).length`, so `(cnormG p).length` outer steps suffice; it also bounds
every intermediate `t`-length (all running polys have `t`-degree `≤ deg p`), hence the inner fraction-free
gcds/exact divisions. Computed once from the input, so the caller passes **no fuel**. -/
def yunBound (p : CPolyG QFunNZ) : ℕ := (cnormG p : List QFunNZ).length

/-- **Fuel-free Yun main loop** (fraction-free) `cSqfreeYunFFgoWf fo b d`: the fuel-free companion of
`cSqfreeYunFFgo`, recursing **structurally on the outer multiplicity counter** `fo` (so `decreasing_by`
is automatic and the loop never stops early — unlike a degree-guarded loop, which truncates at skipped
multiplicities). Stops when `b` is constant (`cdegG b = 0`) or the counter is exhausted, else emits
`p = cmonicG (cgcdFFWf b d)`, recurses on `b' = cdivWf b p`, `d' = cdivWf d p − b'` with `fo` decremented.
The inner gcd/division leaves are the fuel-free `cgcdFFWf`/`cdivWf` — **no fuel at runtime**; the counter
`fo` is supplied once by the entry `cSqfreeYunFFWf` as `yunBound`. Agrees with `cSqfreeYunFFgo` at the same
counter `fo` (`cSqfreeYunFFgoWf_eq`). -/
def cSqfreeYunFFgoWf : ℕ → CPolyG QFunNZ → CPolyG QFunNZ → List (CPolyG QFunNZ)
  | 0, _, _ => []
  | fo + 1, b, d =>
    if cdegG b = 0 then []
    else
      let p := cmonicG (cgcdFFWf b d)
      let b' := cdivWf b p
      let d' := csubG (cdivWf d p) (cderivG b')
      p :: cSqfreeYunFFgoWf fo b' d'

/-- **Fuel-free Yun squarefree factorization over ℚ(x)[t]** `cSqfreeYunFFWf p = [p₁, p₂, …, pₘ]`: the
fuel-free companion of `cSqfreeYunFF`. With `g = cgcdFFWf p (cderivG p)`, `b₁ = cdivWf p g`, `d₁ = cderivG
p/g − b₁'`, runs the fuel-free Yun loop `cSqfreeYunFFgoWf (yunBound p) b₁ d₁` — the outer counter is the
internally-computed `yunBound p`, so the caller passes **no fuel**. `p` is associate to `∏ᵢ pᵢ^i`. Every
gcd is the fuel-free fraction-free `cgcdFFWf`, every exact division the fuel-free `cdivWf` — **no fuel at
runtime**, `native_decide`-able over the noncomputable-`CFieldSpec` tower `QFunNZ` (ℚ(x)). Correct even at
skipped multiplicities (`t² ↦ [1, t]`), where a degree-guarded loop would truncate. -/
def cSqfreeYunFFWf (p : CPolyG QFunNZ) : List (CPolyG QFunNZ) :=
  let g := cgcdFFWf p (cderivG p)
  let b1 := cdivWf p g
  let d1 := csubG (cdivWf (cderivG p) g) (cderivG b1)
  cSqfreeYunFFgoWf (yunBound p) b1 d1

end CPolyG

/-! ### Bridge of `cSqfreeYunFFWf` to the fuel'd `cSqfreeYunFF`

`cSqfreeYunFFgo fuel fo b d`/`cSqfreeYunFF fuel p` call `cgcdFF fuel`/`cdivG fuel` for the per-step
gcd/divisions, with the outer Yun counter `fo` budgeting the multiplicities. The fuel-free companions
substitute the WF leaves `cgcdFFWf`/`cdivWf` and recurse on the same outer counter `fo` (`yunBound` at the
entry). The bridge needs, at each Yun step, that those WF leaves match `cgcdFF fuel`/`cdivG fuel` (a
`CSqfreeYunStepReg fuel b d` node bundle — the `cgcdFF fuel b d` call is node-regular and the dividend
lengths are bounded by `fuel` for the exact divisions). These hold along a real Yun descent; the bundle
`CSqfreeYunGoRegular fuel n b d` packages them with a **step budget** `n` (the number of remaining outer
Yun steps before the running poly is constant), recursing on `n` exactly as `cSqfreeYunFFgo` recurses on
`fo` — so the regularity is a plain structural recursion, no well-founded degree measure (which Yun's loop
genuinely lacks across skipped multiplicities). -/

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

/-- **Per-run Yun-loop regularity bundle** `CSqfreeYunGoRegular fuel n b d`: mirrors the `cSqfreeYunFFgo`
recursion as an inductive predicate **with a step budget** `n` — `stop` (any budget) at a constant running
poly `b` (`cdegG b = 0`, the loop ends), or `step` (budget `n+1`) when the step is node-regular
(`CSqfreeYunStepReg fuel b d`) and the same holds recursively on the quotient `b' = cdivWf b (cmonicG
(cgcdFF fuel b d))` and the updated `d'` within budget `n`. So `CSqfreeYunGoRegular fuel n b d` certifies
that the regular Yun run from `(b, d)` reaches a constant within `n` outer steps — the genuine termination
witness (the *multiplicity counter*), since at skipped multiplicities the running poly does **not** drop in
degree. Unlike a degree guard, this is sound at skipped multiplicities (`t² ↦ [1, t]`). -/
inductive CSqfreeYunGoRegular (fuel : ℕ) : ℕ → CPolyG QFunNZ → CPolyG QFunNZ → Prop
  /-- terminal node: the running poly `b` is constant, the loop stops (any remaining budget). -/
  | stop {n : ℕ} {b d : CPolyG QFunNZ} (hdeg : cdegG b = 0) : CSqfreeYunGoRegular fuel n b d
  /-- recursive node: `b` is non-constant, the step is node-regular, recurse on the quotient within
  budget `n`. -/
  | step {n : ℕ} {b d : CPolyG QFunNZ} (hne : cdegG b ≠ 0) (hstep : CSqfreeYunStepReg fuel b d)
      (hrec : CSqfreeYunGoRegular fuel n (CPolyG.cdivWf b (cmonicG (CPolyG.cgcdFF fuel b d)))
        (csubG (CPolyG.cdivWf d (cmonicG (CPolyG.cgcdFF fuel b d)))
          (cderivG (CPolyG.cdivWf b (cmonicG (CPolyG.cgcdFF fuel b d)))))) :
      CSqfreeYunGoRegular fuel (n + 1) b d

namespace CPolyG

/-- **Bridge — `cSqfreeYunFFgoWf` equals `cSqfreeYunFFgo` at the same outer counter.** For any outer Yun
counter `fo` at least the step budget `n` of a regular run (`n ≤ fo`, `CSqfreeYunGoRegular fuel n b d`),
`cSqfreeYunFFgoWf fo b d = cSqfreeYunFFgo fuel fo b d`. The fuel bounds live only here; `cSqfreeYunFFgoWf`
carries none. By induction on the regularity predicate (its step budget is the genuine termination witness,
the multiplicity counter — not a polynomial degree), generalizing `fo`: at a constant `b` both stop; else
(budget `≥ 1`, so `fo ≥ 1`) the step's WF leaves match the fuel'd ops (`cgcdFFWf_eq_node`,
`cdivmodWf_eq_of_fuel`), and the IH applies to the quotient with `n ≤ fo − 1`. -/
theorem cSqfreeYunFFgoWf_eq (fuel : ℕ) : ∀ (n : ℕ) (b d : CPolyG QFunNZ),
    CSqfreeYunGoRegular fuel n b d → ∀ (fo : ℕ), n ≤ fo →
      cSqfreeYunFFgoWf fo b d = cSqfreeYunFFgo fuel fo b d := by
  intro n b d hreg
  induction hreg with
  | @stop n b d hdeg =>
    -- constant running poly: both stop (either `fo = 0` or the `cdegG b = 0` branch)
    intro fo _
    cases fo with
    | zero => rfl
    | succ fo => rw [cSqfreeYunFFgoWf, cSqfreeYunFFgo, if_pos hdeg, if_pos hdeg]
  | @step n b d hne hstep hrec ih =>
    intro fo hfo
    -- budget `n + 1 ≤ fo`, so `fo = fo' + 1`
    cases fo with
    | zero => exact absurd hfo (Nat.not_succ_le_zero n)
    | succ fo =>
      obtain ⟨hgcd, hblen, hdlen⟩ := hstep
      rw [cSqfreeYunFFgoWf, cSqfreeYunFFgo, if_neg hne, if_neg hne]
      -- the gcd's WF leaf matches the fuel'd `cgcdFF`
      have hgeq : cgcdFFWf b d = CPolyG.cgcdFF fuel b d := cgcdFFWf_eq_node fuel b d hgcd
      set p := cmonicG (CPolyG.cgcdFF fuel b d) with hp
      -- the running and auxiliary quotients' WF leaves match the fuel'd `cdivG`
      have hbq : cdivWf b p = CPolyG.cdivG fuel b p := by
        rw [cdivWf, cdivmodWf_eq_of_fuel fuel b p hblen, cdivG]
      have hdq : cdivWf d p = CPolyG.cdivG fuel d p := by
        rw [cdivWf, cdivmodWf_eq_of_fuel fuel d p hdlen, cdivG]
      simp only [hgeq, ← hp, ← hbq, ← hdq]
      -- the IH applies to the quotient within budget `n ≤ fo`
      rw [ih fo (Nat.le_of_succ_le_succ hfo)]

/-- **Saturation of the fuel'd Yun loop above its step budget.** For a regular run
(`CSqfreeYunGoRegular fuel n b d`) and any two outer counters `fo₁, fo₂` both at least the step budget `n`,
`cSqfreeYunFFgo fuel fo₁ b d = cSqfreeYunFFgo fuel fo₂ b d` — once the run reaches a constant within the
budget, extra outer counter is unused. By induction on the regularity predicate, generalizing both
counters; the entry bridge uses it to reconcile the internal `yunBound` counter with the downstream `fuel`. -/
theorem cSqfreeYunFFgo_saturate (fuel : ℕ) : ∀ (n : ℕ) (b d : CPolyG QFunNZ),
    CSqfreeYunGoRegular fuel n b d → ∀ (fo₁ fo₂ : ℕ), n ≤ fo₁ → n ≤ fo₂ →
      cSqfreeYunFFgo fuel fo₁ b d = cSqfreeYunFFgo fuel fo₂ b d := by
  intro n b d hreg
  induction hreg with
  | @stop n b d hdeg =>
    intro fo₁ fo₂ _ _
    cases fo₁ with
    | zero =>
      cases fo₂ with
      | zero => rfl
      | succ fo₂ => rw [cSqfreeYunFFgo, cSqfreeYunFFgo, if_pos hdeg]
    | succ fo₁ =>
      cases fo₂ with
      | zero => rw [cSqfreeYunFFgo, cSqfreeYunFFgo, if_pos hdeg]
      | succ fo₂ => rw [cSqfreeYunFFgo, cSqfreeYunFFgo, if_pos hdeg, if_pos hdeg]
  | @step n b d hne hstep hrec ih =>
    intro fo₁ fo₂ hfo₁ hfo₂
    cases fo₁ with
    | zero => exact absurd hfo₁ (Nat.not_succ_le_zero n)
    | succ fo₁ =>
      cases fo₂ with
      | zero => exact absurd hfo₂ (Nat.not_succ_le_zero n)
      | succ fo₂ =>
        obtain ⟨_, hblen, hdlen⟩ := hstep
        -- both loop bodies use the fuel'd `cdivG`; the IH/predicate use `cdivWf`, equal under the bounds
        have hbq : cdivWf b (cmonicG (CPolyG.cgcdFF fuel b d))
            = CPolyG.cdivG fuel b (cmonicG (CPolyG.cgcdFF fuel b d)) := by
          rw [cdivWf, cdivmodWf_eq_of_fuel fuel b _ hblen, cdivG]
        have hdq : cdivWf d (cmonicG (CPolyG.cgcdFF fuel b d))
            = CPolyG.cdivG fuel d (cmonicG (CPolyG.cgcdFF fuel b d)) := by
          rw [cdivWf, cdivmodWf_eq_of_fuel fuel d _ hdlen, cdivG]
        rw [cSqfreeYunFFgo, cSqfreeYunFFgo, if_neg hne, if_neg hne]
        simp only []   -- zeta-reduce the `let p/b'/d'` bindings so the `cdivG fuel …` heads are exposed
        rw [← hbq, ← hdq, ih fo₁ fo₂ (Nat.le_of_succ_le_succ hfo₁) (Nat.le_of_succ_le_succ hfo₂)]

end CPolyG

/-! ### Entry-level bridge `cSqfreeYunFFWf = cSqfreeYunFF` and transported correctness

`cSqfreeYunFF fuel p` runs the preamble `g = cgcdFF fuel p (cderivG p)`, `b₁ = cdivG fuel p g`, `d₁ =
cderivG p/g − b₁'`, then `cSqfreeYunFFgo fuel fuel b₁ d₁`. The fuel-free `cSqfreeYunFFWf p` substitutes
`cgcdFFWf`/`cdivWf` in the preamble and runs the structural-counter loop at `fo = yunBound p`. The entry
bundle `CSqfreeYunRegular fuel p` covers the preamble's node-regularity (the `cgcdFF p (cderivG p)` call
and the two `cdivG` lengths) plus the loop run-regularity with a **step budget** `n`
(`CSqfreeYunGoRegular fuel n b₁ d₁`) bounded both by the downstream `fuel` and by the internal
`yunBound p`. The bridge runs the loop bridge at the internal counter `fo = yunBound p`, then *saturates*
the fuel'd loop from `yunBound p` up to `fuel` (both at least the budget `n`). -/

/-- **Per-run Yun entry regularity bundle** `CSqfreeYunRegular fuel p`: the preamble node-regularity for
`cSqfreeYunFFWf p` to match `cSqfreeYunFF fuel p` — the gcd call `cgcdFF fuel p (cderivG p)` is node-regular,
the two preamble divisions `cdivG fuel p g` / `cdivG fuel (cderivG p) g` are reduced (`(cnormG p).length ≤
fuel`, `(cnormG (cderivG p)).length ≤ fuel`), and the loop on `(b₁, d₁)` is a regular run within a step
budget `nbudget` (the max multiplicity) that is at most both the downstream `fuel` (`hnfuel`) and the
internal counter `yunBound p` (`hnbound`). The budget is the genuine termination witness; both counters
exceed it on a real run. -/
structure CSqfreeYunRegular (fuel : ℕ) (p : CPolyG QFunNZ) : Prop where
  /-- the preamble gcd `cgcdFF fuel p (cderivG p)` is node-regular. -/
  hgcd : CgcdFFNodeReg fuel p (cderivG p)
  /-- `p` is short enough for the running division `cdivG fuel p g` to be reduced. -/
  hplen : (cnormG p : List QFunNZ).length ≤ fuel
  /-- `cderivG p` is short enough for the auxiliary division `cdivG fuel (cderivG p) g` to be reduced. -/
  hdplen : (cnormG (cderivG p) : List QFunNZ).length ≤ fuel
  /-- the loop on `(b₁, d₁)` is a regular run within some step budget `n` (the max multiplicity, the
  genuine termination witness) that is at most both the downstream `fuel` and the internal counter
  `yunBound p`; both counters exceed it on a real run. -/
  hloop : ∃ n : ℕ, n ≤ fuel ∧ n ≤ CPolyG.yunBound p ∧
    CSqfreeYunGoRegular fuel n (CPolyG.cdivWf p (cgcdFFWf p (cderivG p)))
      (csubG (CPolyG.cdivWf (cderivG p) (cgcdFFWf p (cderivG p)))
        (cderivG (CPolyG.cdivWf p (cgcdFFWf p (cderivG p)))))

namespace CPolyG

/-- **Bridge — `cSqfreeYunFFWf` equals `cSqfreeYunFF` at any sufficient fuel.** Under a regular Yun run
(`CSqfreeYunRegular fuel p`), `cSqfreeYunFFWf p = cSqfreeYunFF fuel p`. The fuel bounds live only here;
`cSqfreeYunFFWf` carries none. The preamble's WF leaves (`cgcdFFWf`/`cdivWf`) match the fuel'd ops
(`cgcdFFWf_eq_node`, `cdivmodWf_eq_of_fuel`); the loop bridge `cSqfreeYunFFgoWf_eq` runs at the internal
counter `fo = yunBound p` (budget `≤ yunBound p`), and the fuel'd loop saturates from `yunBound p` to the
downstream `fuel` (`cSqfreeYunFFgo_saturate`, both counters `≥` the budget). -/
theorem cSqfreeYunFFWf_eq (fuel : ℕ) (p : CPolyG QFunNZ) (hreg : CSqfreeYunRegular fuel p) :
    cSqfreeYunFFWf p = CPolyG.cSqfreeYunFF fuel p := by
  obtain ⟨hgcd, hplen, hdplen, nbudget, hnfuel, hnbound, hloop⟩ := hreg
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
  -- rewrite the WF entry into the fuel'd `(b₁, d₁)` preamble
  rw [hgeq]
  rw [hgeq] at hloop
  -- the WF loop bridge at the internal counter `fo = yunBound p`
  rw [cSqfreeYunFFgoWf_eq fuel nbudget (cdivWf p g)
    (csubG (cdivWf (cderivG p) g) (cderivG (cdivWf p g))) hloop (yunBound p) hnbound,
    hb1q, hdivdpq]
  -- the fuel'd loop saturates from `yunBound p` up to the downstream `fuel`
  rw [hb1q, hdivdpq] at hloop
  rw [cSqfreeYunFFgo_saturate fuel nbudget (CPolyG.cdivG fuel p g)
    (csubG (CPolyG.cdivG fuel (cderivG p) g) (cderivG (CPolyG.cdivG fuel p g))) hloop
    (yunBound p) fuel hnbound hnfuel]

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

/-- The monomial `t²` over ℚ(x)[t] (ℚ-constant coefficients): the *skipped-multiplicity* witness whose
squarefree factorization is `[1, t]` (multiplicity `1` absent, multiplicity `2` present). -/
def sqfreeYunTsq : CPolyG QFunNZ := [ofConstNZ 0, ofConstNZ 0, ofConstNZ 1]

/-- The monomial `t³` over ℚ(x)[t] (ℚ-constant coefficients): the `3,3,2,1`-measure witness whose
squarefree factorization is `[1, 1, t]` (multiplicities `1, 2` absent, multiplicity `3` present). -/
def sqfreeYunTcube : CPolyG QFunNZ := [ofConstNZ 0, ofConstNZ 0, ofConstNZ 0, ofConstNZ 1]

/-- **★ Bug-fix verification (skipped multiplicity)**: `cSqfreeYunFFWf t² = [1, t]`, i.e. its factor
`t`-degree list is `[0, 1]` — multiplicity `1` is the unit `[1]` (degree `0`) and multiplicity `2` is the
real factor `t` (degree `1`). The earlier degree-guarded loop stopped early here and returned the WRONG
`[1]` (degree list `[0]`); the structural-multiplicity-counter loop now factors correctly. -/
example : (CPolyG.cSqfreeYunFFWf CPolyG.sqfreeYunTsq).map CPolyG.cdegG = [0, 1] := by native_decide

/-- **★ Bug-fix verification (`t³`, the `3,3,2,1`-measure case)**: `cSqfreeYunFFWf t³ = [1, 1, t]`, factor
`t`-degree list `[0, 0, 1]` — multiplicities `1, 2` are units `[1]`, multiplicity `3` is `t`. The running
poly's normalized-list-length measure stalls (`3, 3, 2, 1`) across the two skipped multiplicities, so a
pure-degree well-founded loop cannot terminate correctly; the multiplicity counter does. -/
example : (CPolyG.cSqfreeYunFFWf CPolyG.sqfreeYunTcube).map CPolyG.cdegG = [0, 0, 1] := by native_decide

/-- The skipped-multiplicity factorization `t²` recombines to the input: `1¹ · t² = t²` (monic), via
`cisZeroG` of the difference over ℚ(x)[t] — the fuel-free Yun factors are genuinely correct, not merely the
right length. -/
example :
    CPolyG.cisZeroG (CPolyG.csubG
      (splitSquarefreeFastRecombine (CPolyG.cSqfreeYunFFWf CPolyG.sqfreeYunTsq))
      CPolyG.sqfreeYunTsq) = true := by native_decide

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

open QFunNZ in
/-- Monomial derivative `Dt = t² + 1` (`t = tan x`) for the skipped-multiplicity split smoke test. -/
def sqfreeSplitTanDt : CPolyG QFunNZ := [ofConstNZ 1, ofConstNZ 0, ofConstNZ 1]

/-- **★ Bug-fix verification (skipped-multiplicity split)** — `cSplitSquarefreeFactorFastWf` on `d = t²`
(only multiplicity `2` present) under `Dt = t² + 1` returns `N`-factor `t`-degrees `[0, 1]` and `S`-factor
`t`-degrees `[0, 0]`: the multiplicity-`1` slot is the unit pair `(1, 1)` and the multiplicity-`2` factor
`t` is fully normal (`S = gcd(t, t²+1) = 1`, `N = t`). The earlier degree-guarded Yun truncated `t²`, so
this composition was wrong; it now runs correctly with **no fuel at runtime**. -/
example :
    (((CPolyG.cSplitSquarefreeFactorFastWf CPolyG.sqfreeSplitTanDt CPolyG.sqfreeYunTsq).1).map
        CPolyG.cdegG,
     ((CPolyG.cSplitSquarefreeFactorFastWf CPolyG.sqfreeSplitTanDt CPolyG.sqfreeYunTsq).2).map
        CPolyG.cdegG) = ([0, 1], [0, 0]) := by native_decide

/-- The skipped-multiplicity normal part recombines (by multiplicity) to `d = t²` (monic): `1¹ · t² = t²`,
so `d` is entirely normal under `Dt = t² + 1`, via `cisZeroG` of the difference over ℚ(x)[t]. -/
example :
    CPolyG.cisZeroG (CPolyG.csubG
      (CPolyG.cmonicG (splitSquarefreeFastRecombine
        (CPolyG.cSplitSquarefreeFactorFastWf CPolyG.sqfreeSplitTanDt CPolyG.sqfreeYunTsq).1))
      (CPolyG.cmonicG CPolyG.sqfreeYunTsq)) = true := by native_decide

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
