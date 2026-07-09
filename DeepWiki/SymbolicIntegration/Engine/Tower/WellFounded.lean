import DeepWiki.SymbolicIntegration.Engine.Tower.GcdFFCore
import DeepWiki.SymbolicIntegration.Engine.Tower.Integrate
import DeepWiki.SymbolicIntegration.Engine.FuelFreeGcd
import DeepWiki.SymbolicIntegration.Engine.FuelFreeDiophantine
import DeepWiki.SymbolicIntegration.Engine.FuelFreeResultant

/-! # Well-founded generic tower integration engine

The generic tower integration pipeline, by well-founded recursion. Three recursive bottoms — the
fraction-free gcd kernel `cprimPRSgcdGenCoreWf`, the split loop `cSplitFactorFastG`, and Yun's main loop
`cSqfreeYunFFGgoWf` — and a flat composition (`canonicalRepresentationFastG`, `cHermiteReduceTowerG`, the
logarithmic part) over those leaves. `[CField α]`-only on the runtime fragment (plus
`[CDiffField α]`/`[CFracGcdCoreWf α]` where needed), so it `native_decide`s over the noncomputable tower. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open Compute

/-! ## The fraction-free gcd `cgcdFFCoreWf`

`cgcdFFCoreWf := cmonicG ∘ cgcdFFRawCoreWf` is the public monic fraction-free gcd; the recursive work is
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
      by_cases ha : CPolyG.cisZeroG (CPolyG.cnormG a)
      · simp only [ha, if_true]; rfl
      · simp only [ha, Bool.false_eq_true, if_false]
        show gbnormCore [CPolyG.cnormG a] = [CPolyG.cnormG a]
        rw [gbnormCore, show gbnormCore ([] : GBPolyCore B) = [] from rfl]
        simp only [CPolyG.cnormG_idem, ha, Bool.false_eq_true, if_false]
    | cons r rs =>
      have hih : gbnormCore (r :: rs) = r :: rs := by rw [← hr]; exact ih
      rw [gbnormCore, hih, CPolyG.cnormG_idem]

/-- Generic primitive polynomial-remainder-sequence gcd `cprimPRSgcdGenCoreWf cgcdB P Q ∈ GBPolyCore B`:
the gcd of `P, Q` in `t` (over the coefficient ring `CPolyG B = B[s]`), up to a `B[s]`-content factor.
Normalize `P, Q`; if `Q = 0` return the primitive part of `P`, else take the next PRS node
`r = gbprimitivePartCore cgcdB (gbpsremainderCore 60 P Q)` and recurse on `(Q, r)` under the structural
guard `(gbnormCore r).length < (gbnormCore Q).length`. `[CField B]`-only. The content-gcd `cgcdB` is passed
in. -/
def cprimPRSgcdGenCoreWf (cgcdB : CPolyG B → CPolyG B → CPolyG B) (P Q : GBPolyCore B) :
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

There is no abstract `gbpsremainderCore` length-drop lemma over the generic GCD-domain `CPolyG B = B[s]`,
so the correctness layer uses a fuel-regularity predicate `CPrimPRSGenRegular` mirroring the fuel-recursive
`cprimPRSgcdGenCore` with the per-step length-drop guard built in. -/

/-- Per-run primitive-PRS-kernel fuel-regularity `CPrimPRSGenRegular cgcdB fuel P Q`: mirrors the
`cprimPRSgcdGenCore` fuel recursion as an inductive predicate over the structural fuel counter — `stop`
(any fuel) when the next divisor is zero (`gbisZeroCore (gbnormCore Q)`), or `step` (fuel `n+1`) when `Q`
is nonzero, the next PRS node `r = gbprimitivePartCore cgcdB (gbpsremainderCore 60 (gbnormCore P)
(gbnormCore Q))` strictly drops the normalized `t`-length, and the same holds recursively on
`(gbnormCore Q, r)` at one less fuel. -/
inductive CPrimPRSGenRegular {B : Type*} [CField B] (cgcdB : CPolyG B → CPolyG B → CPolyG B) :
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
* Recursive `instance CFracGcdCoreWf (QFunNZG β) [CFracGcdCoreWf β]` — clear denominators into
  `GBPolyCore β`, run the kernel `cprimPRSgcdGenCoreWf` with the level-`β` `cgcdFFRawCoreWf` as
  content-gcd, lift back. Bottoms at `CFracGcdCoreWf ℚ`.

The public monic gcd is `cgcdFFCoreWf := cmonicG ∘ cgcdFFRawCoreWf`. Every method is `[CField α]`-only
(plus the recursion's `[CFieldDomain β]`/`[CFracGcdCoreWf β]`) — no `[CFieldSpec α]`, so the whole gcd
`native_decide`s over the noncomputable tower. -/

/-- Recursive fraction-free gcd over a tower level: the *raw* (content-normalized, non-monic) gcd
`cgcdFFRawCoreWf p q` of `p, q ∈ CPolyG α = α[t]`. Monic normalization is applied only at the top, by
`cgcdFFCoreWf`. Bottoms at `CFracGcdCoreWf ℚ`. -/
class CFracGcdCoreWf (α : Type*) [CField α] where
  /-- The *raw* (content-normalized, non-monic) FUEL-FREE fraction-free gcd over `α[t]`. -/
  cgcdFFRawCoreWf : CPolyG α → CPolyG α → CPolyG α

namespace CFracGcdCoreWf

variable {α : Type*} [CField α] [CFracGcdCoreWf α]

/-- The public monic fraction-free gcd `cgcdFFCoreWf p q := cmonicG (cgcdFFRawCoreWf p q)` over `α[t]`:
monic-normalize the raw recursive gcd, once at the top, never inside the recursion. -/
def cgcdFFCoreWf (p q : CPolyG α) : CPolyG α := CPolyG.cmonicG (cgcdFFRawCoreWf p q)

end CFracGcdCoreWf

/-- Base `CFracGcdCoreWf ℚ` — the bottom of the tower. `ℚ[t]`'s raw fraction-free gcd is the generic
Euclidean gcd `(CPolyG.cgcdWf p q).1`. -/
instance instCFracGcdCoreWfQ : CFracGcdCoreWf ℚ where
  cgcdFFRawCoreWf p q := (CPolyG.cgcdWf p q).1

section
variable {β : Type*} [CField β] [CFieldDomain β] [CFracGcdCoreWf β]

/-- `CFracGcdCoreWf (QFunNZG β)` — the *raw* fraction-free gcd over `β(s)[t]`, built by running the kernel
`cprimPRSgcdGenCoreWf` over the GCD-domain `CPolyG β = β[s]` with the level-`β` `cgcdFFRawCoreWf` as
content-gcd. Clear denominators of both inputs into `GBPolyCore β = (β[s])[t]`, order them by `t`-degree
(the PRS needs the larger first), run the primitive PRS with `cgcdB := CFracGcdCoreWf.cgcdFFRawCoreWf`
recursing one level down, and lift back to `β(s)[t]` — no `cmonicG` (this is the raw method). Recurses
strictly one level down, bottoming at `CFracGcdCoreWf ℚ`. -/
instance instCFracGcdCoreWfQFunNZG : CFracGcdCoreWf (QFunNZG β) where
  cgcdFFRawCoreWf p q :=
    let P := CPolyG.cclearDenomsCoreG p
    let Q := CPolyG.cclearDenomsCoreG q
    let (P, Q) := if GBPolyCore.gbdegCore P < GBPolyCore.gbdegCore Q then (Q, P) else (P, Q)
    CPolyG.liftGBPolyCoreG (GBPolyCore.cprimPRSgcdGenCoreWf CFracGcdCoreWf.cgcdFFRawCoreWf P Q)

end

/-! ## The remaining recursive bottoms: the §3.5 split and Yun's main loop

The §3.5 split loop `cSplitFactorFastG` (`t`-degree drop) and Yun's main loop `cSqfreeYunFFGgoWf`
(multiplicity counter), generic and `[CField α]`-only. -/

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCoreWf α]

/-- The generic `SplitFactor` step `cstepG Dt p = cdivWf (cgcdFFCoreWf p (cmonomialDeriv Dt p))
(cgcdFFCoreWf p (cderivG p))` — the special-factor candidate `S = gcd(p, Dp)/gcd(p, dp/dt)`. -/
def cstepG (Dt : CPolyG α) (p : CPolyG α) : CPolyG α :=
  cdivWf (CFracGcdCoreWf.cgcdFFCoreWf p (cmonomialDeriv Dt p))
    (CFracGcdCoreWf.cgcdFFCoreWf p (cderivG p))

/-- Generic splitting-factorization loop `cSplitFactorFastG Dt p = (pₙ, pₛ)`: one step extracts
`S = cstepG Dt p`; a constant `S` (`cdegG S = 0`) ⇒ `p` is normal, else recurse on the exact quotient
`p/S = cdivWf p S` and accumulate `S` into the special part. Well-founded on `(cnormG p).length`.
`[CField α] [CDiffField α] [CFracGcdCoreWf α]`-generic. -/
def cSplitFactorFastG (Dt : CPolyG α) (p : CPolyG α) : CPolyG α × CPolyG α :=
  let S := cstepG Dt p
  if cdegG S = 0 then (p, [CField.one])
  else
    let pq := cdivWf p S
    if (cnormG pq : List α).length < (cnormG p : List α).length then
      let (qn, qs) := cSplitFactorFastG Dt pq
      (qn, cmulG S qs)
    else (p, [CField.one])   -- unreachable on a real run (the special factor drops the degree)
termination_by (cnormG p).length
decreasing_by assumption

end CPolyG

namespace CPolyG

variable {α : Type*} [CField α] [CFracGcdCoreWf α]

/-- Generic Yun main loop (fraction-free) `cSqfreeYunFFGgoWf fo b d`: recurses structurally on the outer
multiplicity counter `fo` (so the loop never stops early — unlike a degree-guarded loop, which truncates
at skipped multiplicities). Stops when `b` is constant (`cdegG b = 0`) or the counter is exhausted, else
emits `p = cmonicG (cgcdFFCoreWf b d)`, recurses on `b' = cdivWf b p`, `d' = cdivWf d p − b'` with `fo`
decremented. The counter `fo` is supplied once by the entry `cSqfreeYunFFG` as `cyunBoundG`.
`[CField α] [CFracGcdCoreWf α]`-generic. -/
def cSqfreeYunFFGgoWf : ℕ → CPolyG α → CPolyG α → List (CPolyG α)
  | 0, _, _ => []
  | fo + 1, b, d =>
    if cdegG b = 0 then []
    else
      let p := cmonicG (CFracGcdCoreWf.cgcdFFCoreWf b d)
      let b' := cdivWf b p
      let d' := csubG (cdivWf d p) (cderivG b')
      p :: cSqfreeYunFFGgoWf fo b' d'

/-- Sufficient internal multiplicity-counter bound `cyunBoundG p := (cnormG p).length`: Yun's outer loop
runs one step per multiplicity slot, and the max multiplicity is `≤ deg p < (cnormG p).length`. Computed
once from the input. The generic analogue of `yunBound`. -/
def cyunBoundG (p : CPolyG α) : ℕ := (cnormG p : List α).length

/-- Generic Yun squarefree factorization in `t` `cSqfreeYunFFG p = [p₁, …, pₘ]`: with
`g = cgcdFFCoreWf p (cderivG p)`, `b₁ = cdivWf p g`, `d₁ = cderivG p/g − b₁'`, runs the Yun loop
`cSqfreeYunFFGgoWf (cyunBoundG p) b₁ d₁` with the internally-computed counter `cyunBoundG p`. `p` is
associate to `∏ᵢ pᵢ^i`. Correct even at skipped multiplicities. `[CField α] [CFracGcdCoreWf α]`-generic. -/
def cSqfreeYunFFG (p : CPolyG α) : List (CPolyG α) :=
  let g := CFracGcdCoreWf.cgcdFFCoreWf p (cderivG p)
  let b1 := cdivWf p g
  let d1 := csubG (cdivWf (cderivG p) g) (cderivG b1)
  cSqfreeYunFFGgoWf (cyunBoundG p) b1 d1

/-- Generic split-squarefree-factor over the tower `cSplitSquarefreeFactorFastG Dt p =
((N₁,…,Nₘ), (S₁,…,Sₘ))`. Yun-factor `p` in `t` (`cSqfreeYunFFG`); per factor `pᵢ`,
`Sᵢ = cgcdFFCoreWf pᵢ (cmonomialDeriv Dt pᵢ)` (the special part) and `Nᵢ = cdivWf pᵢ Sᵢ` (normal part). -/
def cSplitSquarefreeFactorFastG [CDiffField α] (Dt : CPolyG α) (p : CPolyG α) :
    List (CPolyG α) × List (CPolyG α) :=
  let ps := cSqfreeYunFFG p
  let parts := ps.map (fun pf =>
    let si := CFracGcdCoreWf.cgcdFFCoreWf pf (cmonomialDeriv Dt pf)
    let ni := cdivWf pf si
    (ni, si))
  (parts.map Prod.fst, parts.map Prod.snd)

end CPolyG

/-! ## The flat-composition pipeline

Everything past the three recursive bottoms is a flat composition over the leaves above plus the generic
`cbezoutOneWf`, `cextendedEuclideanSplitWf`, `cdiophantineG`, `cHermiteReduceTowerInnerWf`,
`cPrimitivePolyIntegrateWf`, `cdivWf`, and the §5.6 `cresultantWf`/`cinterpolateG`/`cHornerG`. -/

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCoreWf α]

/-- Generic canonical representation over the tower:
`canonicalRepresentationFastG Dt a d = (fₚ, fₛ, fₙ) = (q, (b, dₛ), (c, dₙ))` for `f = a/d` (`d` monic).
Divide `a = q·d + r` (`cdivmodWf`); split the denominator `d = dₛ·dₙ` (`cSplitFactorFastG`); Bézout-split
`r` over the coprime `(dₙ, dₛ)` (`cextendedEuclideanSplitWf` with `cbezoutOneWf`). Stated with `.1`/`.2`
projections. -/
def canonicalRepresentationFastG (Dt : CPolyG α) (a d : CPolyG α) :
    CPolyG α × (CPolyG α × CPolyG α) × (CPolyG α × CPolyG α) :=
  let qr := cdivmodWf a d
  let dnds := cSplitFactorFastG Dt d
  let uw := cbezoutOneWf dnds.1 dnds.2
  let bc := cextendedEuclideanSplitWf dnds.1 dnds.2 qr.2 uw.1 uw.2
  (qr.1, (bc.1, dnds.2), (bc.2, dnds.1))

/-- Generic transcendental Hermite reduction `cHermiteReduceTowerG Dt a d = ((gnum, gden),
(h_num, h_den))` over the tower: squarefree-factor `d` with `cSqfreeYunFFG`; for each factor `(v, i)` of
multiplicity `i ≥ 2`, run the inner loop `cHermiteReduceTowerInnerWf` (with `u = d/vⁱ` via `cdivWf`); recover
`h_num` over the squarefree radical `Dstar` via `cdivWf`. Stated with `.1`/`.2` projections. -/
def cHermiteReduceTowerG (Dt : CPolyG α) (a d : CPolyG α) :
    (CPolyG α × CPolyG α) × (CPolyG α × CPolyG α) :=
  let factors := cSqfreeYunFFG d                          -- `[v₁, …, vₘ]`, vᵢ of multiplicity i
  let Dstar := factors.foldl (fun acc vi => cmulG acc vi) [CField.one]   -- squarefree radical ∏ᵢ vᵢ
  let g : CPolyG α × CPolyG α := factors.zipIdx.foldl
    (fun (gAcc : CPolyG α × CPolyG α) (vi, idx) =>
      let i := idx + 1
      if i ≤ 1 then gAcc
      else
        let Vi_pow := cpowG vi i
        let u := cdivWf d Vi_pow
        let (gloc, _) := cHermiteReduceTowerInnerWf Dt vi u (i - 1) a ([CField.zero], [CField.one])
        (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2), cmulG gAcc.2 gloc.2))  -- gAcc + gloc
    ([CField.zero], [CField.one])
  let gprimeNum := csubG (cmulG (cmonomialDeriv Dt g.1) g.2) (cmulG g.1 (cmonomialDeriv Dt g.2))
  let gden2 := cmulG g.2 g.2
  let resNum := csubG (cmulG a gden2) (cmulG d gprimeNum)
  let resDen := cmulG d gden2
  let hNum := cdivWf (cmulG resNum Dstar) resDen
  ((cnormG g.1, cnormG g.2), (cnormG hNum, cnormG Dstar))

/-! ### The generic logarithmic part (Rothstein–Trager)

`cResidueResultantTowerG`/`cLogArgTowerG`/`cRationalResiduesG`/`cLogPartG`, taking the residue
candidates as `α` elements; the resultant runs through `cresultantWf`, the log argument through
`cgcdFFCoreWf`. -/

/-- Generic residue resultant `cResidueResultantTowerG Dt a d = R(z) = res_t(d, a − z·Dd)`. Sample
`R(zₖ) = res_t(d, a − zₖ·Dd)` at the natural nodes `zₖ = cnatCastG k` (`k = 0…deg_t d`) with the
Euclidean-PRS resultant `cresultantWf`, then Lagrange-interpolate (`cinterpolateG`). -/
def cResidueResultantTowerG (Dt : CPolyG α) (a d : CPolyG α) : CPolyG α :=
  let n := cdegG d
  let pts : List (α × α) := (List.range (n + 1)).map (fun k =>
    let zk : α := cnatCastG k
    (zk, cresultantWf d (cAmcDdG Dt a d zk)))
  cinterpolateG pts

/-- Generic log argument `cLogArgTowerG Dt a d c = gcd_t(d, a − c·Dd)` for a residue `c : α`: the
fraction-free gcd `cgcdFFCoreWf` of `d` and `a − c·Dd`. -/
def cLogArgTowerG (Dt : CPolyG α) (a d : CPolyG α) (c : α) : CPolyG α :=
  CFracGcdCoreWf.cgcdFFCoreWf d (cAmcDdG Dt a d c)

/-- Generic rational/field residues `cRationalResiduesG Dt a d cands`: keep the candidates
`c ∈ cands : List α` that are roots of the residue resultant `R(z) = cResidueResultantTowerG Dt a d`,
i.e. `R(c) = 0` (tested by `CField.isZero (cHornerG R c)`). -/
def cRationalResiduesG (Dt : CPolyG α) (a d : CPolyG α) (cands : List α) : List α :=
  let R := cResidueResultantTowerG Dt a d
  cands.filter (fun c => CField.isZero (cHornerG R c))

/-- Generic logarithmic part `cLogPartG Dt a d cands = [(c, gcd_t(d, a − c·Dd)) | c ∈ residues]`: pair
each residue `c : α` (from `cRationalResiduesG`) with its log argument `cLogArgTowerG Dt a d c`. -/
def cLogPartG (Dt : CPolyG α) (a d : CPolyG α) (cands : List α) : List (α × CPolyG α) :=
  (cRationalResiduesG Dt a d cands).map (fun c => (c, cLogArgTowerG Dt a d c))

/-- The generic reduced-case integration capstone `cIntegrateReducedG Dt a d cands`: for `f = a/d`
reduced/normal, `∫ f = g + ∑ c·log(v)`. Hermite-reduce (`cHermiteReduceTowerG`) to the rational part
`g = gnum/gden` and the simple residual `h = h_num/h_den`, then take the residue log part of `h`
(`cLogPartG`, residues drawn from `cands : List α`). Returns the `IntegralResultG` `⟨(gnum, gden),
[(c, v)]⟩`. -/
def cIntegrateReducedG (Dt : CPolyG α) (a d : CPolyG α) (cands : List α) :
    IntegralResultG α :=
  let H := cHermiteReduceTowerG Dt a d
  let logs := cLogPartG Dt H.2.1 H.2.2 cands
  ⟨(H.1.1, H.1.2), logs⟩

end CPolyG

/-! ### Validation — a full elementary tower integral at level 2

Over `CPolyG Lvl2 = ℚ(x)(t₁)[t₂]` (`Dt₂ = 1`), the integrand `f = (1/2)/(t₂+1) − (1/2)/(t₂−1)` (as `a/d`,
`d = t₂² − 1`) has antiderivative `(1/2)log(t₂+1) − (1/2)log(t₂−1)`; the residues `±1/2` have log arguments
`t₂ ± 1`. The generic tower integrator — canonical split, Hermite rational part, Rothstein–Trager residue
logs — computes over the tower at level 2 and the returned `g + ∑ cᵢ·log(vᵢ)` differentiates back to `f`. -/

/-- The Hermite reducer computes the rational part at level 2: for `f = 1/t₂²` over `ℚ(x)(t₁)[t₂]` with
`Dt₂ = t₂² + 1`, the returned rational part and residual satisfy the cleared Hermite identity. -/
theorem towerHermiteLvl2_rationalPartWf :
    (let res := CPolyG.cHermiteReduceTowerG towerHermiteLvl2Dt
        towerHermiteLvl2A towerHermiteLvl2D
      let gnum := res.1.1
      let gden := res.1.2
      let hNum := res.2.1
      let hDen := res.2.2
      let Dgnum := CPolyG.cmonomialDeriv towerHermiteLvl2Dt gnum
      let Dgden := CPolyG.cmonomialDeriv towerHermiteLvl2Dt gden
      let gprimeNum := CPolyG.csubG (CPolyG.cmulG Dgnum gden) (CPolyG.cmulG gnum Dgden)
      let gden2 := CPolyG.cmulG gden gden
      let lhs := CPolyG.cmulG
        (CPolyG.caddG (CPolyG.cmulG gprimeNum hDen) (CPolyG.cmulG hNum gden2)) towerHermiteLvl2D
      let rhs := CPolyG.cmulG towerHermiteLvl2A (CPolyG.cmulG gden2 hDen)
      CPolyG.cisZeroG (CPolyG.csubG lhs rhs)) = true := by native_decide

/-- The level-2 residual denominator has degree 1. -/
theorem towerHermiteLvl2_residual_degreeWf :
    CPolyG.cdegG (CPolyG.cHermiteReduceTowerG towerHermiteLvl2Dt
      towerHermiteLvl2A towerHermiteLvl2D).2.2 = 1 := by native_decide

/-- The canonical representation recombines to `f` at level 2. -/
theorem towerCanRepLvl2_recombinesWf :
    (let res := CPolyG.canonicalRepresentationFastG towerCanRepLvl2Dt
        towerCanRepLvl2A towerCanRepLvl2D
      let q := res.1
      let b := res.2.1.1
      let ds := res.2.1.2
      let c := res.2.2.1
      let dn := res.2.2.2
      let dsdn := CPolyG.cmulG ds dn
      let num := CPolyG.caddG (CPolyG.caddG (CPolyG.cmulG q dsdn) (CPolyG.cmulG b dn))
        (CPolyG.cmulG c ds)
      CPolyG.cisZeroG (CPolyG.csubG (CPolyG.cmulG num towerCanRepLvl2D)
        (CPolyG.cmulG towerCanRepLvl2A dsdn))) = true := by native_decide

/-- The recovered level-2 logarithmic part has length 2: the residue scan over `ℚ(x)(t₁)[t₂]` finds
exactly the two rational residues `±1/2` (log arguments `t₂ ± 1`). -/
theorem towerIntLvl2_logs_lengthWf :
    (CPolyG.cIntegrateReducedG towerIntLvl2Dt towerIntLvl2Num towerIntLvl2Den
      towerIntLvl2Cands).logs.length = 2 := by native_decide

/-- A full elementary tower integral at level 2 with `D(∫f) = f`. For
`f = (1/2)/(t₂+1) − (1/2)/(t₂−1)` over ℚ(x)(t₁)(t₂), the capstone `cIntegrateReducedG` returns an
`IntegralResultG` whose antiderivative identity `D(rational) + ∑ᵢ cᵢ·(D(vᵢ)/vᵢ) = f` holds exactly
(`checkIdentityG`). -/
theorem towerIntLvl2_fullIntegralWf :
    CPolyG.checkIdentityG towerIntLvl2Dt
      (CPolyG.cIntegrateReducedG towerIntLvl2Dt towerIntLvl2Num towerIntLvl2Den
        towerIntLvl2Cands)
      towerIntLvl2Num towerIntLvl2Den = true := by native_decide

/-! ## The remaining RDE (PolyRischDE / SPDE) recursive bottoms

Two more `[CField α]`-generic degree-recursion bottoms of the RDE pipeline — the non-cancellation solve
`cPolyRischDENoCancelG` and the SPDE `cSPDEG`. The cancellation cases and the top driver `cRischDEG`
continue in `Tower/RischDEWellFounded`. -/

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α]

/-- Generic non-cancellation Poly-Risch-DE `cPolyRischDENoCancelG Dt b c n`: solves `Dq + b·q = c` for
`q ∈ α[t]` with `deg(q) ≤ n` (`n : ℤ`), top-down — `p = (lc(c)/lc(b))·tᵐ` (`m = deg(c) − deg(b)`), recurse on
`c' = c − D(p) − b·p` (`D = cmonomialDeriv Dt`). Returns `none` or `some q`. Well-founded on
`(cnormG c).length`. `[CField α] [CDiffField α]`-generic. -/
def cPolyRischDENoCancelG (Dt : CPolyG α) (b c : CPolyG α) (n : ℤ) :
    Option (CPolyG α) :=
  if cisZeroG c then some []
  else
    let m : ℤ := (cdegG c : ℤ) - (cdegG b : ℤ)
    if n < 0 ∨ m < 0 ∨ m > n then none
    else
      let coeff := CField.div (cleadG c) (cleadG b)
      let p := cshiftG m.toNat [coeff]
      let c' := csubG (csubG c (cmonomialDeriv Dt p)) (cmulG b p)
      if (cnormG c' : List α).length < (cnormG c : List α).length then
        match cPolyRischDENoCancelG Dt b c' (m - 1) with
        | none => none
        | some q => some (caddG p q)
      else none   -- unreachable on a non-cancellation run (the leading term cancels, degree drops)
termination_by (cnormG c).length
decreasing_by assumption

end CPolyG

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCoreWf α]

/-- Generic SPDE `cSPDEG Dt a b c n`: the `g = gcd(a, b)`-peel reducing the degree-bounded
`a·Dq + b·q = c` to one with `a = 1`. Returns `none` or `some (b̄, c̄, m, α', β)` so any solution is
`q = α'·h + β` with `h` solving `Dh + b̄·h = c̄`, `deg(h) ≤ m`. Peels `g = cgcdFFCoreWf a b`; the constant
`a/g` base case returns the identity reconstruction, else solves the Bézout `cdiophantineG b̄ ā c̄` and
recurses on `ā = a/g` at `n − deg(ā)`. Well-founded on `(n+1).toNat`. `[CField α] [CDiffField α]
[CFracGcdCoreWf α]`-generic. -/
def cSPDEG (Dt : CPolyG α) (a b c : CPolyG α) (n : ℤ) :
    Option (CPolyG α × CPolyG α × ℤ × CPolyG α × CPolyG α) :=
  if n < 0 then
    if cisZeroG c then some ([], [], 0, [], []) else none
  else
    let g := CFracGcdCoreWf.cgcdFFCoreWf a b
    if cdvdG g c then
      let a' := cdivWf a g
      let b' := cdivWf b g
      let c' := cdivWf c g
      if cdegG a' = 0 then
        let ainv := CField.inv (cleadG a')
        some (cscaleG ainv b', cscaleG ainv c', n, [CField.one], [])
      else
        let (r, z) := cdiophantineG b' a' c'
        let Da := cmonomialDeriv Dt a'
        let Dr := cmonomialDeriv Dt r
        if (n - (cdegG a' : ℤ) + 1).toNat < (n + 1).toNat then
          match cSPDEG Dt a' (caddG b' Da) (csubG z Dr) (n - (cdegG a' : ℤ)) with
          | none => none
          | some (bbar, cbar, m, α', β) =>
              some (bbar, cbar, m, cmulG a' α', caddG (cmulG a' β) r)
        else none   -- unreachable on a real run (`deg ā ≥ 1`, so the bound `n − deg ā` strictly drops)
    else none
termination_by (n + 1).toNat
decreasing_by assumption

end CPolyG

end DeepWiki.SymbolicIntegration
