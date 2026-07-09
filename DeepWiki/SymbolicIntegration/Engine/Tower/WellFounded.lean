import DeepWiki.SymbolicIntegration.Engine.Tower.GcdFFCore
import DeepWiki.SymbolicIntegration.Engine.Tower.Integrate
import DeepWiki.SymbolicIntegration.Engine.FuelFreeGcd
import DeepWiki.SymbolicIntegration.Engine.FuelFreeDiophantine
import DeepWiki.SymbolicIntegration.Engine.FuelFreeResultant

/-! # Well-founded generic tower integration engine

The generic tower integration pipeline, by well-founded recursion. Three recursive bottoms — the
fraction-free gcd kernel `cprimPRSgcdGenCoreWf`, the split loop `cSplitFactorFast`, and Yun's main loop
`cSqfreeYunFFGgoWf` — and a flat composition (`canonicalRepresentationFast`, `cHermiteReduceTower`, the
logarithmic part) over those leaves. `[CField α]`-only on the runtime fragment (plus
`[CDiffField α]`/`[CFracGcdCoreWf α]` where needed), so it `native_decide`s over the noncomputable tower. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration


/-! ## The fraction-free gcd `cgcdFFCoreWf`

`cgcdFFCoreWf := cmonic ∘ cgcdFFRawCoreWf` is the public monic fraction-free gcd; the recursive work is
`cprimPRSgcdGenCoreWf`, the primitive PRS kernel over the GCD-domain. -/

/-! ### The primitive-PRS kernel `cprimPRSgcdGenCoreWf`

`(P, Q) → (Q, r)` with `r = gbprimitivePartCore (gbpsremainder P Q)`; the normalized `t`-length
`(gbnormCore Q).length` strictly drops each step, under the structural runtime guard
`(gbnormCore r).length < (gbnormCore Q).length` (`decreasing_by := assumption`). -/

namespace GBPolyCore

variable {B : Type*} [CField B]

/-- `gbnormCore` is idempotent: `gbnormCore (gbnormCore p) = gbnormCore p`. The bivariate analogue of
`cnormG_idem`; discharges the `decreasing_by` of `cprimPRSgcdGenCoreWf`. -/
@[simp] theorem gbnormCore_idem (p : GBPolyCore B) : gbnormCore (gbnormCore p) = gbnormCore p := by
  induction p with
  | nil => rfl
  | cons a as ih =>
    rw [gbnormCore]
    cases hr : gbnormCore as with
    | nil =>
      by_cases ha : CPoly.cisZero (CPoly.cnorm a)
      · simp only [ha, if_true]; rfl
      · simp only [ha, Bool.false_eq_true, if_false]
        show gbnormCore [CPoly.cnorm a] = [CPoly.cnorm a]
        rw [gbnormCore, show gbnormCore ([] : GBPolyCore B) = [] from rfl]
        simp only [CPoly.cnormG_idem, ha, Bool.false_eq_true, if_false]
    | cons r rs =>
      have hih : gbnormCore (r :: rs) = r :: rs := by rw [← hr]; exact ih
      rw [gbnormCore, hih, CPoly.cnormG_idem]

/-- Generic primitive polynomial-remainder-sequence gcd `cprimPRSgcdGenCoreWf cgcdB P Q ∈ GBPolyCore B`:
the gcd of `P, Q` in `t` (over the coefficient ring `CPoly B = B[s]`), up to a `B[s]`-content factor.
Normalize `P, Q`; if `Q = 0` return the primitive part of `P`, else take the next PRS node
`r = gbprimitivePartCore cgcdB (gbpsremainderCore 60 P Q)` and recurse on `(Q, r)` under the structural
guard `(gbnormCore r).length < (gbnormCore Q).length`. `[CField B]`-only. The content-gcd `cgcdB` is passed
in. -/
def cprimPRSgcdGenCoreWf (cgcdB : CPoly B → CPoly B → CPoly B) (P Q : GBPolyCore B) :
    GBPolyCore B :=
  let P := gbnormCore P
  let Q := gbnormCore Q
  if gbisZeroCore Q then gbprimitivePartCore cgcdB P
  else
    let r := gbprimitivePartCore cgcdB (gbpsremainderCore 60 P Q)
    if (gbnormCore r).length < (gbnormCore Q).length then
      cprimPRSgcdGenCoreWf cgcdB Q r
    else gbprimitivePartCore cgcdB P   -- unreachable on a real run (PRS `t`-degree drop)
termination_by (gbnormCore Q).length
decreasing_by exact Nat.lt_of_lt_of_le ‹_ < _› (le_of_eq (by rw [gbnormCore_idem]))

end GBPolyCore

/-! ### Primitive-PRS termination predicate

There is no abstract `gbpsremainderCore` length-drop lemma over the generic GCD-domain `CPoly B = B[s]`,
so the correctness layer uses a fuel-regularity predicate `CPrimPRSGenRegular` mirroring the fuel-recursive
`cprimPRSgcdGenCore` with the per-step length-drop guard built in. -/

/-- Per-run primitive-PRS-kernel fuel-regularity `CPrimPRSGenRegular cgcdB fuel P Q`: mirrors the
`cprimPRSgcdGenCore` fuel recursion as an inductive predicate over the structural fuel counter — `stop`
(any fuel) when the next divisor is zero (`gbisZeroCore (gbnormCore Q)`), or `step` (fuel `n+1`) when `Q`
is nonzero, the next PRS node `r = gbprimitivePartCore cgcdB (gbpsremainderCore 60 (gbnormCore P)
(gbnormCore Q))` strictly drops the normalized `t`-length, and the same holds recursively on
`(gbnormCore Q, r)` at one less fuel. -/
inductive CPrimPRSGenRegular {B : Type*} [CField B] (cgcdB : CPoly B → CPoly B → CPoly B) :
    ℕ → GBPolyCore B → GBPolyCore B → Prop
  /-- terminal node: the next divisor is zero, the loop stops (any fuel). -/
  | stop {fuel : ℕ} {P Q : GBPolyCore B} (hz : GBPolyCore.gbisZeroCore (GBPolyCore.gbnormCore Q) = true) :
      CPrimPRSGenRegular cgcdB fuel P Q
  /-- recursive node: `Q` nonzero, the next PRS node drops the `t`-length, recurse on `(gbnormCore Q, r)`. -/
  | step {fuel : ℕ} {P Q : GBPolyCore B} (hz : GBPolyCore.gbisZeroCore (GBPolyCore.gbnormCore Q) = false)
      (hguard : (GBPolyCore.gbnormCore (GBPolyCore.gbprimitivePartCore cgcdB
          (GBPolyCore.gbpsremainderCore 60 (GBPolyCore.gbnormCore P) (GBPolyCore.gbnormCore Q)))).length
        < (GBPolyCore.gbnormCore Q).length)
      (hrec : CPrimPRSGenRegular cgcdB fuel (GBPolyCore.gbnormCore Q)
        (GBPolyCore.gbprimitivePartCore cgcdB
          (GBPolyCore.gbpsremainderCore 60 (GBPolyCore.gbnormCore P) (GBPolyCore.gbnormCore Q)))) :
      CPrimPRSGenRegular cgcdB (fuel + 1) P Q

/-! ### `class CFracGcdCoreWf α` — the recursive fraction-free gcd over `α[t]`

* `class CFracGcdCoreWf α` (one method `cgcdFFRawCoreWf`, the *raw* content-normalized gcd).
* Base `instance CFracGcdCoreWf ℚ` — `ℚ[t]`'s raw fraction-free gcd is the generic Euclidean gcd
  `(cgcdWf p q).1`.
* Recursive `instance CFracGcdCoreWf (CFrac β) [CFracGcdCoreWf β]` — clear denominators into
  `GBPolyCore β`, run the kernel `cprimPRSgcdGenCoreWf` with the level-`β` `cgcdFFRawCoreWf` as
  content-gcd, lift back. Bottoms at `CFracGcdCoreWf ℚ`.

The public monic gcd is `cgcdFFCoreWf := cmonic ∘ cgcdFFRawCoreWf`. Every method is `[CField α]`-only
(plus the recursion's `[CFieldDomain β]`/`[CFracGcdCoreWf β]`) — no `[CFieldSpec α]`, so the whole gcd
`native_decide`s over the noncomputable tower. -/

/-- Recursive fraction-free gcd over a tower level: the *raw* (content-normalized, non-monic) gcd
`cgcdFFRawCoreWf p q` of `p, q ∈ CPoly α = α[t]`. Monic normalization is applied only at the top, by
`cgcdFFCoreWf`. Bottoms at `CFracGcdCoreWf ℚ`. -/
class CFracGcdCoreWf (α : Type*) [CField α] where
  /-- The *raw* (content-normalized, non-monic) FUEL-FREE fraction-free gcd over `α[t]`. -/
  cgcdFFRawCoreWf : CPoly α → CPoly α → CPoly α

namespace CFracGcdCoreWf

variable {α : Type*} [CField α] [CFracGcdCoreWf α]

/-- The public monic fraction-free gcd `cgcdFFCoreWf p q := cmonic (cgcdFFRawCoreWf p q)` over `α[t]`:
monic-normalize the raw recursive gcd, once at the top, never inside the recursion. -/
def cgcdFFCoreWf (p q : CPoly α) : CPoly α := CPoly.cmonic (cgcdFFRawCoreWf p q)

end CFracGcdCoreWf

/-- Base `CFracGcdCoreWf ℚ` — the bottom of the tower. `ℚ[t]`'s raw fraction-free gcd is the generic
Euclidean gcd `(CPoly.cgcdWf p q).1`. -/
instance instCFracGcdCoreWfQ : CFracGcdCoreWf ℚ where
  cgcdFFRawCoreWf p q := (CPoly.cgcdWf p q).1

section
variable {β : Type*} [CField β] [CFieldDomain β] [CFracGcdCoreWf β]

/-- `CFracGcdCoreWf (CFrac β)` — the *raw* fraction-free gcd over `β(s)[t]`, built by running the kernel
`cprimPRSgcdGenCoreWf` over the GCD-domain `CPoly β = β[s]` with the level-`β` `cgcdFFRawCoreWf` as
content-gcd. Clear denominators of both inputs into `GBPolyCore β = (β[s])[t]`, order them by `t`-degree
(the PRS needs the larger first), run the primitive PRS with `cgcdB := CFracGcdCoreWf.cgcdFFRawCoreWf`
recursing one level down, and lift back to `β(s)[t]` — no `cmonic` (this is the raw method). Recurses
strictly one level down, bottoming at `CFracGcdCoreWf ℚ`. -/
instance instCFracGcdCoreWfCFrac : CFracGcdCoreWf (CFrac β) where
  cgcdFFRawCoreWf p q :=
    let P := CPoly.cclearDenomsCore p
    let Q := CPoly.cclearDenomsCore q
    let (P, Q) := if GBPolyCore.gbdegCore P < GBPolyCore.gbdegCore Q then (Q, P) else (P, Q)
    CPoly.liftGBPolyCore (GBPolyCore.cprimPRSgcdGenCoreWf CFracGcdCoreWf.cgcdFFRawCoreWf P Q)

end

/-! ## The remaining recursive bottoms: the §3.5 split and Yun's main loop

The §3.5 split loop `cSplitFactorFast` (`t`-degree drop) and Yun's main loop `cSqfreeYunFFGgoWf`
(multiplicity counter), generic and `[CField α]`-only. -/

namespace CPoly

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCoreWf α]

/-- The generic `SplitFactor` step `cstep Dt p = cdivWf (cgcdFFCoreWf p (cmonomialDeriv Dt p))
(cgcdFFCoreWf p (cderiv p))` — the special-factor candidate `S = gcd(p, Dp)/gcd(p, dp/dt)`. -/
def cstep (Dt : CPoly α) (p : CPoly α) : CPoly α :=
  cdivWf (CFracGcdCoreWf.cgcdFFCoreWf p (cmonomialDeriv Dt p))
    (CFracGcdCoreWf.cgcdFFCoreWf p (cderiv p))

/-- Generic splitting-factorization loop `cSplitFactorFast Dt p = (pₙ, pₛ)`: one step extracts
`S = cstep Dt p`; a constant `S` (`cdeg S = 0`) ⇒ `p` is normal, else recurse on the exact quotient
`p/S = cdivWf p S` and accumulate `S` into the special part. Well-founded on `(cnorm p).length`.
`[CField α] [CDiffField α] [CFracGcdCoreWf α]`-generic. -/
def cSplitFactorFast (Dt : CPoly α) (p : CPoly α) : CPoly α × CPoly α :=
  let S := cstep Dt p
  if cdeg S = 0 then (p, [CField.one])
  else
    let pq := cdivWf p S
    if (cnorm pq : List α).length < (cnorm p : List α).length then
      let (qn, qs) := cSplitFactorFast Dt pq
      (qn, cmul S qs)
    else (p, [CField.one])   -- unreachable on a real run (the special factor drops the degree)
termination_by (cnorm p).length
decreasing_by assumption

end CPoly

namespace CPoly

variable {α : Type*} [CField α] [CFracGcdCoreWf α]

/-- Generic Yun main loop (fraction-free) `cSqfreeYunFFGgoWf fo b d`: recurses structurally on the outer
multiplicity counter `fo` (so the loop never stops early — unlike a degree-guarded loop, which truncates
at skipped multiplicities). Stops when `b` is constant (`cdeg b = 0`) or the counter is exhausted, else
emits `p = cmonic (cgcdFFCoreWf b d)`, recurses on `b' = cdivWf b p`, `d' = cdivWf d p − b'` with `fo`
decremented. The counter `fo` is supplied once by the entry `cSqfreeYunFF` as `cyunBound`.
`[CField α] [CFracGcdCoreWf α]`-generic. -/
def cSqfreeYunFFGgoWf : ℕ → CPoly α → CPoly α → List (CPoly α)
  | 0, _, _ => []
  | fo + 1, b, d =>
    if cdeg b = 0 then []
    else
      let p := cmonic (CFracGcdCoreWf.cgcdFFCoreWf b d)
      let b' := cdivWf b p
      let d' := csub (cdivWf d p) (cderiv b')
      p :: cSqfreeYunFFGgoWf fo b' d'

/-- Sufficient internal multiplicity-counter bound `cyunBound p := (cnorm p).length`: Yun's outer loop
runs one step per multiplicity slot, and the max multiplicity is `≤ deg p < (cnorm p).length`. Computed
once from the input. The generic analogue of `yunBound`. -/
def cyunBound (p : CPoly α) : ℕ := (cnorm p : List α).length

/-- Generic Yun squarefree factorization in `t` `cSqfreeYunFF p = [p₁, …, pₘ]`: with
`g = cgcdFFCoreWf p (cderiv p)`, `b₁ = cdivWf p g`, `d₁ = cderiv p/g − b₁'`, runs the Yun loop
`cSqfreeYunFFGgoWf (cyunBound p) b₁ d₁` with the internally-computed counter `cyunBound p`. `p` is
associate to `∏ᵢ pᵢ^i`. Correct even at skipped multiplicities. `[CField α] [CFracGcdCoreWf α]`-generic. -/
def cSqfreeYunFF (p : CPoly α) : List (CPoly α) :=
  let g := CFracGcdCoreWf.cgcdFFCoreWf p (cderiv p)
  let b1 := cdivWf p g
  let d1 := csub (cdivWf (cderiv p) g) (cderiv b1)
  cSqfreeYunFFGgoWf (cyunBound p) b1 d1

/-- Generic split-squarefree-factor over the tower `cSplitSquarefreeFactorFast Dt p =
((N₁,…,Nₘ), (S₁,…,Sₘ))`. Yun-factor `p` in `t` (`cSqfreeYunFF`); per factor `pᵢ`,
`Sᵢ = cgcdFFCoreWf pᵢ (cmonomialDeriv Dt pᵢ)` (the special part) and `Nᵢ = cdivWf pᵢ Sᵢ` (normal part). -/
def cSplitSquarefreeFactorFast [CDiffField α] (Dt : CPoly α) (p : CPoly α) :
    List (CPoly α) × List (CPoly α) :=
  let ps := cSqfreeYunFF p
  let parts := ps.map (fun pf =>
    let si := CFracGcdCoreWf.cgcdFFCoreWf pf (cmonomialDeriv Dt pf)
    let ni := cdivWf pf si
    (ni, si))
  (parts.map Prod.fst, parts.map Prod.snd)

end CPoly

/-! ## The flat-composition pipeline

Everything past the three recursive bottoms is a flat composition over the leaves above plus the generic
`cbezoutOneWf`, `cextendedEuclideanSplitWf`, `cdiophantine`, `cHermiteReduceTowerInnerWf`,
`cPrimitivePolyIntegrateWf`, `cdivWf`, and the §5.6 `cresultantWf`/`cinterpolate`/`cHorner`. -/

namespace CPoly

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCoreWf α]

/-- Generic canonical representation over the tower:
`canonicalRepresentationFast Dt a d = (fₚ, fₛ, fₙ) = (q, (b, dₛ), (c, dₙ))` for `f = a/d` (`d` monic).
Divide `a = q·d + r` (`cdivmodWf`); split the denominator `d = dₛ·dₙ` (`cSplitFactorFast`); Bézout-split
`r` over the coprime `(dₙ, dₛ)` (`cextendedEuclideanSplitWf` with `cbezoutOneWf`). Stated with `.1`/`.2`
projections. -/
def canonicalRepresentationFast (Dt : CPoly α) (a d : CPoly α) :
    CPoly α × (CPoly α × CPoly α) × (CPoly α × CPoly α) :=
  let qr := cdivmodWf a d
  let dnds := cSplitFactorFast Dt d
  let uw := cbezoutOneWf dnds.1 dnds.2
  let bc := cextendedEuclideanSplitWf dnds.1 dnds.2 qr.2 uw.1 uw.2
  (qr.1, (bc.1, dnds.2), (bc.2, dnds.1))

/-- Generic transcendental Hermite reduction `cHermiteReduceTower Dt a d = ((gnum, gden),
(h_num, h_den))` over the tower: squarefree-factor `d` with `cSqfreeYunFF`; for each factor `(v, i)` of
multiplicity `i ≥ 2`, run the inner loop `cHermiteReduceTowerInnerWf` (with `u = d/vⁱ` via `cdivWf`); recover
`h_num` over the squarefree radical `Dstar` via `cdivWf`. Stated with `.1`/`.2` projections. -/
def cHermiteReduceTower (Dt : CPoly α) (a d : CPoly α) :
    (CPoly α × CPoly α) × (CPoly α × CPoly α) :=
  let factors := cSqfreeYunFF d                          -- `[v₁, …, vₘ]`, vᵢ of multiplicity i
  let Dstar := factors.foldl (fun acc vi => cmul acc vi) [CField.one]   -- squarefree radical ∏ᵢ vᵢ
  let g : CPoly α × CPoly α := factors.zipIdx.foldl
    (fun (gAcc : CPoly α × CPoly α) (vi, idx) =>
      let i := idx + 1
      if i ≤ 1 then gAcc
      else
        let Vi_pow := cpow vi i
        let u := cdivWf d Vi_pow
        let (gloc, _) := cHermiteReduceTowerInnerWf Dt vi u (i - 1) a ([CField.zero], [CField.one])
        (cadd (cmul gAcc.1 gloc.2) (cmul gloc.1 gAcc.2), cmul gAcc.2 gloc.2))  -- gAcc + gloc
    ([CField.zero], [CField.one])
  let gprimeNum := csub (cmul (cmonomialDeriv Dt g.1) g.2) (cmul g.1 (cmonomialDeriv Dt g.2))
  let gden2 := cmul g.2 g.2
  let resNum := csub (cmul a gden2) (cmul d gprimeNum)
  let resDen := cmul d gden2
  let hNum := cdivWf (cmul resNum Dstar) resDen
  ((cnorm g.1, cnorm g.2), (cnorm hNum, cnorm Dstar))

/-! ### The generic logarithmic part (Rothstein–Trager)

`cResidueResultantTower`/`cLogArgTower`/`cRationalResidues`/`cLogPart`, taking the residue
candidates as `α` elements; the resultant runs through `cresultantWf`, the log argument through
`cgcdFFCoreWf`. -/

/-- Generic residue resultant `cResidueResultantTower Dt a d = R(z) = res_t(d, a − z·Dd)`. Sample
`R(zₖ) = res_t(d, a − zₖ·Dd)` at the natural nodes `zₖ = cnatCast k` (`k = 0…deg_t d`) with the
Euclidean-PRS resultant `cresultantWf`, then Lagrange-interpolate (`cinterpolate`). -/
def cResidueResultantTower (Dt : CPoly α) (a d : CPoly α) : CPoly α :=
  let n := cdeg d
  let pts : List (α × α) := (List.range (n + 1)).map (fun k =>
    let zk : α := cnatCast k
    (zk, cresultantWf d (cAmcDd Dt a d zk)))
  cinterpolate pts

/-- Generic log argument `cLogArgTower Dt a d c = gcd_t(d, a − c·Dd)` for a residue `c : α`: the
fraction-free gcd `cgcdFFCoreWf` of `d` and `a − c·Dd`. -/
def cLogArgTower (Dt : CPoly α) (a d : CPoly α) (c : α) : CPoly α :=
  CFracGcdCoreWf.cgcdFFCoreWf d (cAmcDd Dt a d c)

/-- Generic rational/field residues `cRationalResidues Dt a d cands`: keep the candidates
`c ∈ cands : List α` that are roots of the residue resultant `R(z) = cResidueResultantTower Dt a d`,
i.e. `R(c) = 0` (tested by `CField.isZero (cHorner R c)`). -/
def cRationalResidues (Dt : CPoly α) (a d : CPoly α) (cands : List α) : List α :=
  let R := cResidueResultantTower Dt a d
  cands.filter (fun c => CField.isZero (cHorner R c))

/-- Generic logarithmic part `cLogPart Dt a d cands = [(c, gcd_t(d, a − c·Dd)) | c ∈ residues]`: pair
each residue `c : α` (from `cRationalResidues`) with its log argument `cLogArgTower Dt a d c`. -/
def cLogPart (Dt : CPoly α) (a d : CPoly α) (cands : List α) : List (α × CPoly α) :=
  (cRationalResidues Dt a d cands).map (fun c => (c, cLogArgTower Dt a d c))

/-- The generic reduced-case integration capstone `cIntegrateReduced Dt a d cands`: for `f = a/d`
reduced/normal, `∫ f = g + ∑ c·log(v)`. Hermite-reduce (`cHermiteReduceTower`) to the rational part
`g = gnum/gden` and the simple residual `h = h_num/h_den`, then take the residue log part of `h`
(`cLogPart`, residues drawn from `cands : List α`). Returns the `IntegralResult` `⟨(gnum, gden),
[(c, v)]⟩`. -/
def cIntegrateReduced (Dt : CPoly α) (a d : CPoly α) (cands : List α) :
    IntegralResult α :=
  let H := cHermiteReduceTower Dt a d
  let logs := cLogPart Dt H.2.1 H.2.2 cands
  ⟨(H.1.1, H.1.2), logs⟩

end CPoly

/-! ### Validation — a full elementary tower integral at level 2

Over `CPoly Lvl2 = ℚ(x)(t₁)[t₂]` (`Dt₂ = 1`), the integrand `f = (1/2)/(t₂+1) − (1/2)/(t₂−1)` (as `a/d`,
`d = t₂² − 1`) has antiderivative `(1/2)log(t₂+1) − (1/2)log(t₂−1)`; the residues `±1/2` have log arguments
`t₂ ± 1`. The generic tower integrator — canonical split, Hermite rational part, Rothstein–Trager residue
logs — computes over the tower at level 2 and the returned `g + ∑ cᵢ·log(vᵢ)` differentiates back to `f`. -/

/-- The Hermite reducer computes the rational part at level 2: for `f = 1/t₂²` over `ℚ(x)(t₁)[t₂]` with
`Dt₂ = t₂² + 1`, the returned rational part and residual satisfy the cleared Hermite identity. -/
theorem towerHermiteLvl2_rationalPartWf :
    (let res := CPoly.cHermiteReduceTower towerHermiteLvl2Dt
        towerHermiteLvl2A towerHermiteLvl2D
      let gnum := res.1.1
      let gden := res.1.2
      let hNum := res.2.1
      let hDen := res.2.2
      let Dgnum := CPoly.cmonomialDeriv towerHermiteLvl2Dt gnum
      let Dgden := CPoly.cmonomialDeriv towerHermiteLvl2Dt gden
      let gprimeNum := CPoly.csub (CPoly.cmul Dgnum gden) (CPoly.cmul gnum Dgden)
      let gden2 := CPoly.cmul gden gden
      let lhs := CPoly.cmul
        (CPoly.cadd (CPoly.cmul gprimeNum hDen) (CPoly.cmul hNum gden2)) towerHermiteLvl2D
      let rhs := CPoly.cmul towerHermiteLvl2A (CPoly.cmul gden2 hDen)
      CPoly.cisZero (CPoly.csub lhs rhs)) = true := by native_decide

/-- The level-2 residual denominator has degree 1. -/
theorem towerHermiteLvl2_residual_degreeWf :
    CPoly.cdeg (CPoly.cHermiteReduceTower towerHermiteLvl2Dt
      towerHermiteLvl2A towerHermiteLvl2D).2.2 = 1 := by native_decide

/-- The canonical representation recombines to `f` at level 2. -/
theorem towerCanRepLvl2_recombinesWf :
    (let res := CPoly.canonicalRepresentationFast towerCanRepLvl2Dt
        towerCanRepLvl2A towerCanRepLvl2D
      let q := res.1
      let b := res.2.1.1
      let ds := res.2.1.2
      let c := res.2.2.1
      let dn := res.2.2.2
      let dsdn := CPoly.cmul ds dn
      let num := CPoly.cadd (CPoly.cadd (CPoly.cmul q dsdn) (CPoly.cmul b dn))
        (CPoly.cmul c ds)
      CPoly.cisZero (CPoly.csub (CPoly.cmul num towerCanRepLvl2D)
        (CPoly.cmul towerCanRepLvl2A dsdn))) = true := by native_decide

/-- The recovered level-2 logarithmic part has length 2: the residue scan over `ℚ(x)(t₁)[t₂]` finds
exactly the two rational residues `±1/2` (log arguments `t₂ ± 1`). -/
theorem towerIntLvl2_logs_lengthWf :
    (CPoly.cIntegrateReduced towerIntLvl2Dt towerIntLvl2Num towerIntLvl2Den
      towerIntLvl2Cands).logs.length = 2 := by native_decide

/-- A full elementary tower integral at level 2 with `D(∫f) = f`. For
`f = (1/2)/(t₂+1) − (1/2)/(t₂−1)` over ℚ(x)(t₁)(t₂), the capstone `cIntegrateReduced` returns an
`IntegralResult` whose antiderivative identity `D(rational) + ∑ᵢ cᵢ·(D(vᵢ)/vᵢ) = f` holds exactly
(`checkIdentity`). -/
theorem towerIntLvl2_fullIntegralWf :
    CPoly.checkIdentity towerIntLvl2Dt
      (CPoly.cIntegrateReduced towerIntLvl2Dt towerIntLvl2Num towerIntLvl2Den
        towerIntLvl2Cands)
      towerIntLvl2Num towerIntLvl2Den = true := by native_decide

/-! ## The remaining RDE (PolyRischDE / SPDE) recursive bottoms

Two more `[CField α]`-generic degree-recursion bottoms of the RDE pipeline — the non-cancellation solve
`cPolyRischDENoCancel` and the SPDE `cSPDE`. The cancellation cases and the top driver `cRischDE`
continue in `Tower/RischDEWellFounded`. -/

namespace CPoly

variable {α : Type*} [CField α] [CDiffField α]

/-- Generic non-cancellation Poly-Risch-DE `cPolyRischDENoCancel Dt b c n`: solves `Dq + b·q = c` for
`q ∈ α[t]` with `deg(q) ≤ n` (`n : ℤ`), top-down — `p = (lc(c)/lc(b))·tᵐ` (`m = deg(c) − deg(b)`), recurse on
`c' = c − D(p) − b·p` (`D = cmonomialDeriv Dt`). Returns `none` or `some q`. Well-founded on
`(cnorm c).length`. `[CField α] [CDiffField α]`-generic. -/
def cPolyRischDENoCancel (Dt : CPoly α) (b c : CPoly α) (n : ℤ) :
    Option (CPoly α) :=
  if cisZero c then some []
  else
    let m : ℤ := (cdeg c : ℤ) - (cdeg b : ℤ)
    if n < 0 ∨ m < 0 ∨ m > n then none
    else
      let coeff := CField.div (clead c) (clead b)
      let p := cshift m.toNat [coeff]
      let c' := csub (csub c (cmonomialDeriv Dt p)) (cmul b p)
      if (cnorm c' : List α).length < (cnorm c : List α).length then
        match cPolyRischDENoCancel Dt b c' (m - 1) with
        | none => none
        | some q => some (cadd p q)
      else none   -- unreachable on a non-cancellation run (the leading term cancels, degree drops)
termination_by (cnorm c).length
decreasing_by assumption

end CPoly

namespace CPoly

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCoreWf α]

/-- Generic SPDE `cSPDE Dt a b c n`: the `g = gcd(a, b)`-peel reducing the degree-bounded
`a·Dq + b·q = c` to one with `a = 1`. Returns `none` or `some (b̄, c̄, m, α', β)` so any solution is
`q = α'·h + β` with `h` solving `Dh + b̄·h = c̄`, `deg(h) ≤ m`. Peels `g = cgcdFFCoreWf a b`; the constant
`a/g` base case returns the identity reconstruction, else solves the Bézout `cdiophantine b̄ ā c̄` and
recurses on `ā = a/g` at `n − deg(ā)`. Well-founded on `(n+1).toNat`. `[CField α] [CDiffField α]
[CFracGcdCoreWf α]`-generic. -/
def cSPDE (Dt : CPoly α) (a b c : CPoly α) (n : ℤ) :
    Option (CPoly α × CPoly α × ℤ × CPoly α × CPoly α) :=
  if n < 0 then
    if cisZero c then some ([], [], 0, [], []) else none
  else
    let g := CFracGcdCoreWf.cgcdFFCoreWf a b
    if cdvd g c then
      let a' := cdivWf a g
      let b' := cdivWf b g
      let c' := cdivWf c g
      if cdeg a' = 0 then
        let ainv := CField.inv (clead a')
        some (cscale ainv b', cscale ainv c', n, [CField.one], [])
      else
        let (r, z) := cdiophantine b' a' c'
        let Da := cmonomialDeriv Dt a'
        let Dr := cmonomialDeriv Dt r
        if (n - (cdeg a' : ℤ) + 1).toNat < (n + 1).toNat then
          match cSPDE Dt a' (cadd b' Da) (csub z Dr) (n - (cdeg a' : ℤ)) with
          | none => none
          | some (bbar, cbar, m, α', β) =>
              some (bbar, cbar, m, cmul a' α', cadd (cmul a' β) r)
        else none   -- unreachable on a real run (`deg ā ≥ 1`, so the bound `n − deg ā` strictly drops)
    else none
termination_by (n + 1).toNat
decreasing_by assumption

end CPoly

end DeepWiki.SymbolicIntegration
