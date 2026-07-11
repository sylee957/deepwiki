import DeepWiki.SymbolicIntegration.Engine.Tower.GcdFFCore
import DeepWiki.SymbolicIntegration.Engine.Tower.Integrate
import DeepWiki.ComputableAlgebra.PolyEuclideanDense
import DeepWiki.SymbolicIntegration.Engine.FuelFreeDiophantine
import DeepWiki.ComputableAlgebra.PolyResultantDense
import DeepWiki.SymbolicIntegration.Engine.PolySplitFactor
import DeepWiki.ComputableAlgebra.PolyInterpolateDense
import DeepWiki.ComputableAlgebra.PolyInterpolateSparse

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
      by_cases ha : DensePoly.cisZero (DensePoly.cnorm a)
      · simp only [ha, if_true]; rfl
      · simp only [ha, Bool.false_eq_true, if_false]
        show gbnormCore [DensePoly.cnorm a] = [DensePoly.cnorm a]
        rw [gbnormCore, show gbnormCore ([] : GBPolyCore B) = [] from rfl]
        simp only [DensePoly.cnormG_idem, ha, Bool.false_eq_true, if_false]
    | cons r rs =>
      have hih : gbnormCore (r :: rs) = r :: rs := by rw [← hr]; exact ih
      rw [gbnormCore, hih, DensePoly.cnormG_idem]

/-- Generic primitive polynomial-remainder-sequence gcd `cprimPRSgcdGenCoreWf cgcdB P Q ∈ GBPolyCore B`:
the gcd of `P, Q` in `t` (over the coefficient ring `DensePoly B = B[s]`), up to a `B[s]`-content factor.
Normalize `P, Q`; if `Q = 0` return the primitive part of `P`, else take the next PRS node
`r = gbprimitivePartCore cgcdB (gbpsremainderCore 60 P Q)` and recurse on `(Q, r)` under the structural
guard `(gbnormCore r).length < (gbnormCore Q).length`. `[CField B]`-only. The content-gcd `cgcdB` is passed
in. -/
def cprimPRSgcdGenCoreWf (cgcdB : DensePoly B → DensePoly B → DensePoly B) (P Q : GBPolyCore B) :
    GBPolyCore B :=
  let P := gbnormCore P
  let Q := gbnormCore Q
  if DensePoly.cisZero Q then gbprimitivePartCore cgcdB P
  else
    let r := gbprimitivePartCore cgcdB (gbpsremainderCore 60 P Q)
    if (gbnormCore r).length < (gbnormCore Q).length then
      cprimPRSgcdGenCoreWf cgcdB Q r
    else gbprimitivePartCore cgcdB P   -- unreachable on a real run (PRS `t`-degree drop)
termination_by (gbnormCore Q).length
decreasing_by exact Nat.lt_of_lt_of_le ‹_ < _› (le_of_eq (by rw [gbnormCore_idem]))

end GBPolyCore

/-! ### Primitive-PRS termination predicate

There is no abstract `gbpsremainderCore` length-drop lemma over the generic GCD-domain `DensePoly B = B[s]`,
so the correctness layer uses a fuel-regularity predicate `CPrimPRSGenRegular` mirroring the fuel-recursive
`cprimPRSgcdGenCore` with the per-step length-drop guard built in. -/

/-- Per-run primitive-PRS-kernel fuel-regularity `CPrimPRSGenRegular cgcdB fuel P Q`: mirrors the
`cprimPRSgcdGenCore` fuel recursion as an inductive predicate over the structural fuel counter — `stop`
(any fuel) when the next divisor is zero (`DensePoly.cisZero (gbnormCore Q)`), or `step` (fuel `n+1`) when `Q`
is nonzero, the next PRS node `r = gbprimitivePartCore cgcdB (gbpsremainderCore 60 (gbnormCore P)
(gbnormCore Q))` strictly drops the normalized `t`-length, and the same holds recursively on
`(gbnormCore Q, r)` at one less fuel. -/
inductive CPrimPRSGenRegular {B : Type*} [CField B] (cgcdB : DensePoly B → DensePoly B → DensePoly B) :
    ℕ → GBPolyCore B → GBPolyCore B → Prop
  /-- terminal node: the next divisor is zero, the loop stops (any fuel). -/
  | stop {fuel : ℕ} {P Q : GBPolyCore B} (hz : DensePoly.cisZero (GBPolyCore.gbnormCore Q) = true) :
      CPrimPRSGenRegular cgcdB fuel P Q
  /-- recursive node: `Q` nonzero, the next PRS node drops the `t`-length, recurse on `(gbnormCore Q, r)`. -/
  | step {fuel : ℕ} {P Q : GBPolyCore B} (hz : DensePoly.cisZero (GBPolyCore.gbnormCore Q) = false)
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
  the gcd component selected by `CPolyEuclidean.gcdExt`.
* Recursive `instance CFracGcdCoreWf (DenseFrac β) [CFracGcdCoreWf β]` — clear denominators into
  `GBPolyCore β`, run the kernel `cprimPRSgcdGenCoreWf` with the level-`β` `cgcdFFRawCoreWf` as
  content-gcd, lift back. Bottoms at `CFracGcdCoreWf ℚ`.

The public monic gcd is `cgcdFFCoreWf := cmonic ∘ cgcdFFRawCoreWf`. Every method is `[CField α]`-only
(plus the recursion's `[CFieldDomain β DensePoly]`/`[CFracGcdCoreWf β]`) — no `[CFieldSpec α]`, so the whole gcd
`native_decide`s over the noncomputable tower. -/

/-- Recursive fraction-free gcd over a tower level: the *raw* (content-normalized, non-monic) gcd
`cgcdFFRawCoreWf p q` of `p, q ∈ DensePoly α = α[t]`. Monic normalization is applied only at the top, by
`cgcdFFCoreWf`. Bottoms at `CFracGcdCoreWf ℚ`. -/
class CFracGcdCoreWf (α : Type*) [CField α] where
  /-- The *raw* (content-normalized, non-monic) FUEL-FREE fraction-free gcd over `α[t]`. -/
  cgcdFFRawCoreWf : DensePoly α → DensePoly α → DensePoly α

namespace CFracGcdCoreWf

variable {α : Type*} [CField α] [CFracGcdCoreWf α]

/-- The public monic fraction-free gcd `cgcdFFCoreWf p q := cmonic (cgcdFFRawCoreWf p q)` over `α[t]`:
monic-normalize the raw recursive gcd, once at the top, never inside the recursion. -/
def cgcdFFCoreWf (p q : DensePoly α) : DensePoly α := DensePoly.cmonic (cgcdFFRawCoreWf p q)

end CFracGcdCoreWf

/-- Dense tower polynomials select the fraction-free gcd for their coefficient field. -/
instance (priority := high) instCPolyGcdDenseWf {α : Type*} [CField α] [CFracGcdCoreWf α] :
    CPolyGcd DensePoly α where
  compute := CFracGcdCoreWf.cgcdFFCoreWf

namespace CPolyGcd

/-- Dense tower gcd selection unfolds to the fraction-free implementation. -/
@[simp] theorem compute_dense_wf_eq {α : Type*} [CField α] [CFracGcdCoreWf α]
    (p q : DensePoly α) :
    CPolyGcd.compute p q = CFracGcdCoreWf.cgcdFFCoreWf p q := rfl

end CPolyGcd

/-- Base `CFracGcdCoreWf ℚ` — the bottom of the tower. `ℚ[t]`'s raw fraction-free gcd is the generic
Euclidean gcd `(CPolyEuclidean.gcdExt p q).1`. -/
instance instCFracGcdCoreWfQ : CFracGcdCoreWf ℚ where
  cgcdFFRawCoreWf p q := (CPolyEuclidean.gcdExt p q).1

/-- The selected fraction-free gcd over `ℚ` satisfies the lawful gcd interface. -/
instance (priority := high) instLawfulCPolyGcdDenseWfQ : LawfulCPolyGcd DensePoly ℚ where
  compute_isGCD := by
    intro _ p q
    have hcompute : CPolyGcd.compute p q = DensePoly.cgcdMonicWf p q := rfl
    rw [hcompute]
    obtain ⟨hp, hq⟩ := DensePoly.toPolyG_cgcdMonicWf_dvd p q
    refine ⟨by simpa only [toPoly_list_eq] using hp,
      by simpa only [toPoly_list_eq] using hq, ?_⟩
    intro d hdp hdq
    have hraw : d ∣ DensePoly.toPoly (DensePoly.cgcdWf p q).1 :=
      DensePoly.toPolyG_dvd_cgcdWf p q
        (by simpa only [toPoly_list_eq] using hdp)
        (by simpa only [toPoly_list_eq] using hdq)
    have hassoc : Associated (DensePoly.toPoly (DensePoly.cgcdMonicWf p q))
        (DensePoly.toPoly (DensePoly.cgcdWf p q).1) := by
      rw [DensePoly.cgcdMonicWf]
      exact DensePoly.associated_toPolyG_cmonicG _
    simpa only [toPoly_list_eq] using hraw.trans hassoc.symm.dvd

section
variable {β : Type*} [CField β] [CFieldDomain β DensePoly] [CFracGcdCoreWf β]

/-- `CFracGcdCoreWf (DenseFrac β)` — the *raw* fraction-free gcd over `β(s)[t]`, built by running the kernel
`cprimPRSgcdGenCoreWf` over the GCD-domain `DensePoly β = β[s]` with the level-`β` `cgcdFFRawCoreWf` as
content-gcd. Clear denominators of both inputs into `GBPolyCore β = (β[s])[t]`, order them by `t`-degree
(the PRS needs the larger first), run the primitive PRS with `cgcdB := CFracGcdCoreWf.cgcdFFRawCoreWf`
recursing one level down, and lift back to `β(s)[t]` — no `cmonic` (this is the raw method). Recurses
strictly one level down, bottoming at `CFracGcdCoreWf ℚ`. -/
instance instCFracGcdCoreWfCFrac : CFracGcdCoreWf (DenseFrac β) where
  cgcdFFRawCoreWf p q :=
    let P := DensePoly.cclearDenomsCore p
    let Q := DensePoly.cclearDenomsCore q
    let (P, Q) := if DensePoly.cdeg P < DensePoly.cdeg Q then (Q, P) else (P, Q)
    DensePoly.liftGBPolyCore (GBPolyCore.cprimPRSgcdGenCoreWf CFracGcdCoreWf.cgcdFFRawCoreWf P Q)

end

/-! ## The remaining recursive bottoms: the §3.5 split and Yun's main loop

The §3.5 split loop `cSplitFactorFast` (`t`-degree drop) and Yun's main loop `cSqfreeYunFFGgoWf`
(multiplicity counter), generic and `[CField α]`-only. -/

namespace DensePoly

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCoreWf α]

/-- The generic `SplitFactor` step `cstep Dt p = CPolyEuclidean.div (cgcdFFCoreWf p (CPolyEngine.monomialDeriv Dt p))
(cgcdFFCoreWf p (cderiv p))` — the special-factor candidate `S = gcd(p, Dp)/gcd(p, dp/dt)`. -/
def cstep (Dt : DensePoly α) (p : DensePoly α) : DensePoly α :=
  CPolyEuclidean.div (CPolyGcd.compute p (CPolyEngine.monomialDeriv Dt p))
    (CPolyGcd.compute p (cderiv p))

/-- Generic splitting-factorization loop `cSplitFactorFast Dt p = (pₙ, pₛ)`: one step extracts
`S = cstep Dt p`; a constant `S` (`cdeg S = 0`) ⇒ `p` is normal, else recurse on the exact quotient
`p/S = CPolyEuclidean.div p S` and accumulate `S` into the special part. Well-founded on `(cnorm p).length`.
`[CField α] [CDiffField α] [CFracGcdCoreWf α]`-generic. -/
def cSplitFactorFast (Dt : DensePoly α) (p : DensePoly α) : DensePoly α × DensePoly α :=
  let S := cstep Dt p
  if cdeg S = 0 then (p, [CCommRing.one])
  else
    let pq := CPolyEuclidean.div p S
    if (cnorm pq : List α).length < (cnorm p : List α).length then
      let (qn, qs) := cSplitFactorFast Dt pq
      (qn, cmul S qs)
    else (p, [CCommRing.one])   -- unreachable on a real run (the special factor drops the degree)
termination_by (cnorm p).length
decreasing_by assumption

end DensePoly

/-- Dense polynomials select the established well-founded differential split implementation. -/
instance instCPolySplitFactorDense {α : Type*} [CField α] [CDiffField α]
    [CFracGcdCoreWf α] : CPolySplitFactor DensePoly α where
  compute := DensePoly.cSplitFactorFast

namespace CPoly

/-- Dense selected splitting is the established well-founded implementation. -/
theorem splitFactor_dense_eq {α : Type*} [CField α] [CDiffField α]
    [CFracGcdCoreWf α] (Dt p : DensePoly α) :
    CPoly.splitFactor Dt p = DensePoly.cSplitFactorFast Dt p := rfl

end CPoly

namespace DensePoly

variable {α : Type*} [CField α] [CFracGcdCoreWf α]

/-- Generic Yun main loop (fraction-free) `cSqfreeYunFFGgoWf fo b d`: recurses structurally on the outer
multiplicity counter `fo` (so the loop never stops early — unlike a degree-guarded loop, which truncates
at skipped multiplicities). Stops when `b` is constant (`cdeg b = 0`) or the counter is exhausted, else
emits `p = cmonic (cgcdFFCoreWf b d)`, recurses on `b' = CPolyEuclidean.div b p`, `d' = CPolyEuclidean.div d p − b'` with `fo`
decremented. The counter `fo` is supplied once by the entry `cSqfreeYunFF` as `cyunBound`.
`[CField α] [CFracGcdCoreWf α]`-generic. -/
def cSqfreeYunFFGgoWf : ℕ → DensePoly α → DensePoly α → List (DensePoly α)
  | 0, _, _ => []
  | fo + 1, b, d =>
    if cdeg b = 0 then []
    else
      let p := cmonic (CPolyGcd.compute b d)
      let b' := CPolyEuclidean.div b p
      let d' := csub (CPolyEuclidean.div d p) (cderiv b')
      p :: cSqfreeYunFFGgoWf fo b' d'

/-- Sufficient internal multiplicity-counter bound `cyunBound p := (cnorm p).length`: Yun's outer loop
runs one step per multiplicity slot, and the max multiplicity is `≤ deg p < (cnorm p).length`. Computed
once from the input. The generic analogue of `yunBound`. -/
def cyunBound (p : DensePoly α) : ℕ := (cnorm p : List α).length

/-- Generic Yun squarefree factorization in `t` `cSqfreeYunFF p = [p₁, …, pₘ]`: with
`g = cgcdFFCoreWf p (cderiv p)`, `b₁ = CPolyEuclidean.div p g`, `d₁ = cderiv p/g − b₁'`, runs the Yun loop
`cSqfreeYunFFGgoWf (cyunBound p) b₁ d₁` with the internally-computed counter `cyunBound p`. `p` is
associate to `∏ᵢ pᵢ^i`. Correct even at skipped multiplicities. `[CField α] [CFracGcdCoreWf α]`-generic. -/
def cSqfreeYunFF (p : DensePoly α) : List (DensePoly α) :=
  let g := CPolyGcd.compute p (cderiv p)
  let b1 := CPolyEuclidean.div p g
  let d1 := csub (CPolyEuclidean.div (cderiv p) g) (cderiv b1)
  cSqfreeYunFFGgoWf (cyunBound p) b1 d1

/-- Dense tower polynomials select the established fraction-free Yun decomposition. -/
instance (priority := high) instCPolySquarefreeDenseWf : CPolySquarefree DensePoly α where
  compute := cSqfreeYunFF

/-- Dense tower squarefree selection is the established fraction-free Yun implementation. -/
@[simp] theorem squarefreeYun_dense_wf_eq (p : DensePoly α) :
    CPoly.squarefreeYun p = cSqfreeYunFF p := rfl

/-- Nonconstant Yun factors paired with their one-based multiplicities. -/
def cSqfreeYunFactors (p : DensePoly α) : List (DensePoly α × ℕ) :=
  (cSqfreeYunFF p).zipIdx.filterMap fun (q, i) =>
    if cdeg q = 0 then none else some (q, i + 1)

/-- Generic split-squarefree-factor over the tower `cSplitSquarefreeFactorFast Dt p =
((N₁,…,Nₘ), (S₁,…,Sₘ))`. Yun-factor `p` in `t` (`cSqfreeYunFF`); per factor `pᵢ`,
`Sᵢ = cgcdFFCoreWf pᵢ (CPolyEngine.monomialDeriv Dt pᵢ)` (the special part) and `Nᵢ = CPolyEuclidean.div pᵢ Sᵢ` (normal part). -/
def cSplitSquarefreeFactorFast [CDiffField α] (Dt : DensePoly α) (p : DensePoly α) :
    List (DensePoly α) × List (DensePoly α) :=
  let ps := CPoly.squarefreeYun p
  let parts := ps.map (fun pf =>
    let si := CPolyGcd.compute pf (CPolyEngine.monomialDeriv Dt pf)
    let ni := CPolyEuclidean.div pf si
    (ni, si))
  (parts.map Prod.fst, parts.map Prod.snd)

end DensePoly

/-! ## The flat-composition pipeline

Everything past the three recursive bottoms is a flat composition over the leaves above plus the generic
`CPoly.bezoutOne`, `CPoly.extendedEuclideanSplit`, `CPoly.diophantineReduced`, `cHermiteReduceTowerInnerWf`,
`cPrimitivePolyIntegrateWf`, `CPolyEuclidean.div`, the selected resultant, and interpolation/evaluation routines. -/

namespace DensePoly

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCoreWf α]
  [CPolyResultant DensePoly]

/-- Generic canonical representation over the tower:
`canonicalRepresentationFast Dt a d = (fₚ, fₛ, fₙ) = (q, (b, dₛ), (c, dₙ))` for `f = a/d` (`d` monic).
Divide `a = q·d + r` (`CPolyEuclidean.divmod`); split the denominator `d = dₛ·dₙ` (`CPoly.splitFactor`); Bézout-split
`r` over the coprime `(dₙ, dₛ)` (`CPoly.extendedEuclideanSplit` with `CPoly.bezoutOne`). Stated with `.1`/`.2`
projections. -/
def canonicalRepresentationFast (Dt : DensePoly α) (a d : DensePoly α) :
    DensePoly α × (DensePoly α × DensePoly α) × (DensePoly α × DensePoly α) :=
  let qr := CPolyEuclidean.divmod a d
  let dnds := CPoly.splitFactor Dt d
  let uw := CPoly.bezoutOne dnds.1 dnds.2
  let bc := CPoly.extendedEuclideanSplit dnds.1 dnds.2 qr.2 uw.1 uw.2
  (qr.1, (bc.1, dnds.2), (bc.2, dnds.1))

/-- Generic transcendental Hermite reduction `cHermiteReduceTower Dt a d = ((gnum, gden),
(h_num, h_den))` over the tower: squarefree-factor `d` with `CPoly.squarefreeYun`; for each factor `(v, i)` of
multiplicity `i ≥ 2`, run the inner loop `cHermiteReduceTowerInnerWf` (with `u = d/vⁱ` via `CPolyEuclidean.div`); recover
`h_num` over the squarefree radical `Dstar` via `CPolyEuclidean.div`. Stated with `.1`/`.2` projections. -/
def cHermiteReduceTower (Dt : DensePoly α) (a d : DensePoly α) :
    (DensePoly α × DensePoly α) × (DensePoly α × DensePoly α) :=
  let factors := CPoly.squarefreeYun d                   -- `[v₁, …, vₘ]`, vᵢ of multiplicity i
  let Dstar := factors.foldl (fun acc vi => cmul acc vi) [CCommRing.one]   -- squarefree radical ∏ᵢ vᵢ
  let g : DensePoly α × DensePoly α := factors.zipIdx.foldl
    (fun (gAcc : DensePoly α × DensePoly α) (vi, idx) =>
      let i := idx + 1
      if i ≤ 1 then gAcc
      else
        let Vi_pow := cpow vi i
        let u := CPolyEuclidean.div d Vi_pow
        let (gloc, _) := cHermiteReduceTowerInnerWf Dt vi u (i - 1) a ([CCommRing.zero], [CCommRing.one])
        (cadd (cmul gAcc.1 gloc.2) (cmul gloc.1 gAcc.2), cmul gAcc.2 gloc.2))  -- gAcc + gloc
    ([CCommRing.zero], [CCommRing.one])
  let gprimeNum := csub (cmul (CPolyEngine.monomialDeriv Dt g.1) g.2) (cmul g.1 (CPolyEngine.monomialDeriv Dt g.2))
  let gden2 := cmul g.2 g.2
  let resNum := csub (cmul a gden2) (cmul d gprimeNum)
  let resDen := cmul d gden2
  let hNum := CPolyEuclidean.div (cmul resNum Dstar) resDen
  ((cnorm g.1, cnorm g.2), (cnorm hNum, cnorm Dstar))

/-! ### The generic logarithmic part (Rothstein–Trager)

`cResidueResultantTower`/`cLogArgTower`/`cRationalResidues`/`cLogPart`, taking the residue
candidates as `α` elements; the resultant runs through `CPolyResultant`, the log argument through
`cgcdFFCoreWf`. -/

/-- Representation-independent residue resultant with independently selected inner and outer polynomial
representations. -/
def cResidueResultantTowerWith {P Q : Type u → Type u}
    [CPoly P] [CPolyEngine P] [CPolyResultant P]
    [CPoly Q] [CPolyEngine Q] [CPolyInterpolate Q]
    {β : Type u} [CField β] [CDiffField β] (Dt a d : P β) : Q β :=
  let n := CPolyEngine.cdeg d
  let pts : List (β × β) := (List.range (n + 1)).map (fun k =>
    let zk : β := CField.natCast k
    (zk, CPolyResultant.compute d (cAmcDd Dt a d zk)))
  CPoly.interpolate pts

/-- Dense residue resultant `R(z) = res_t(d, a − z·Dd)`, selected through `CPolyResultant`. -/
def cResidueResultantTower [CPolyResultant DensePoly]
    (Dt : DensePoly α) (a d : DensePoly α) : DensePoly α :=
  cResidueResultantTowerWith Dt a d

example :
    cResidueResultantTowerWith
      (CPoly.SparsePoly.ofList [(0, 1)] : CPoly.SparsePoly ℚ)
      (CPoly.SparsePoly.ofList [(0, 1)])
      (CPoly.SparsePoly.ofList [(0, -1), (2, 1)]) = [1, 0, -4] := by
  native_decide

/-- The residue resultant can use sparse storage for both the eliminated and interpolation variables. -/
example :
    cResidueResultantTowerWith (Q := CPoly.SparsePoly)
      (CPoly.SparsePoly.ofList [(0, 1)] : CPoly.SparsePoly ℚ)
      (CPoly.SparsePoly.ofList [(0, 1)])
      (CPoly.SparsePoly.ofList [(0, -1), (2, 1)]) =
        CPoly.SparsePoly.ofList [(0, 1), (1, 0), (2, -4)] := by
  native_decide

/-- Generic log argument `cLogArgTower Dt a d c = gcd_t(d, a − c·Dd)` for a residue `c : α`: the
fraction-free gcd `cgcdFFCoreWf` of `d` and `a − c·Dd`. -/
def cLogArgTower (Dt : DensePoly α) (a d : DensePoly α) (c : α) : DensePoly α :=
  CPolyGcd.compute d (cAmcDd Dt a d c)

/-- Generic rational/field residues `cRationalResidues Dt a d cands`: keep the candidates
`c ∈ cands : List α` that are roots of the residue resultant `R(z) = cResidueResultantTower Dt a d`,
i.e. `R(c) = 0` (tested by `CCommRing.isZero (ceval R c)`). -/
def cRationalResidues (Dt : DensePoly α) (a d : DensePoly α) (cands : List α) : List α :=
  let R := cResidueResultantTower Dt a d
  cands.filter (fun c => CCommRing.isZero (ceval R c))

/-- Generic logarithmic part `cLogPart Dt a d cands = [(c, gcd_t(d, a − c·Dd)) | c ∈ residues]`: pair
each residue `c : α` (from `cRationalResidues`) with its log argument `cLogArgTower Dt a d c`. -/
def cLogPart (Dt : DensePoly α) (a d : DensePoly α) (cands : List α) : List (α × DensePoly α) :=
  (cRationalResidues Dt a d cands).map (fun c => (c, cLogArgTower Dt a d c))

/-- The generic reduced-case integration capstone `cIntegrateReduced Dt a d cands`: for `f = a/d`
reduced/normal, `∫ f = g + ∑ c·log(v)`. Hermite-reduce (`cHermiteReduceTower`) to the rational part
`g = gnum/gden` and the simple residual `h = h_num/h_den`, then take the residue log part of `h`
(`cLogPart`, residues drawn from `cands : List α`). Returns the `IntegralResult` `⟨(gnum, gden),
[(c, v)]⟩`. -/
def cIntegrateReduced (Dt : DensePoly α) (a d : DensePoly α) (cands : List α) :
    IntegralResult α :=
  let H := cHermiteReduceTower Dt a d
  let logs := cLogPart Dt H.2.1 H.2.2 cands
  ⟨(H.1.1, H.1.2), logs⟩

end DensePoly

/-! ### Validation — a full elementary tower integral at level 2

Over `DensePoly Lvl2 = ℚ(x)(t₁)[t₂]` (`Dt₂ = 1`), the integrand `f = (1/2)/(t₂+1) − (1/2)/(t₂−1)` (as `a/d`,
`d = t₂² − 1`) has antiderivative `(1/2)log(t₂+1) − (1/2)log(t₂−1)`; the residues `±1/2` have log arguments
`t₂ ± 1`. The generic tower integrator — canonical split, Hermite rational part, Rothstein–Trager residue
logs — computes over the tower at level 2 and the returned `g + ∑ cᵢ·log(vᵢ)` differentiates back to `f`. -/

/-- The Hermite reducer computes the rational part at level 2: for `f = 1/t₂²` over `ℚ(x)(t₁)[t₂]` with
`Dt₂ = t₂² + 1`, the returned rational part and residual satisfy the cleared Hermite identity. -/
theorem towerHermiteLvl2_rationalPartWf :
    (let res := DensePoly.cHermiteReduceTower towerHermiteLvl2Dt
        towerHermiteLvl2A towerHermiteLvl2D
      let gnum := res.1.1
      let gden := res.1.2
      let hNum := res.2.1
      let hDen := res.2.2
      let Dgnum := CPolyEngine.monomialDeriv towerHermiteLvl2Dt gnum
      let Dgden := CPolyEngine.monomialDeriv towerHermiteLvl2Dt gden
      let gprimeNum := DensePoly.csub (DensePoly.cmul Dgnum gden) (DensePoly.cmul gnum Dgden)
      let gden2 := DensePoly.cmul gden gden
      let lhs := DensePoly.cmul
        (DensePoly.cadd (DensePoly.cmul gprimeNum hDen) (DensePoly.cmul hNum gden2)) towerHermiteLvl2D
      let rhs := DensePoly.cmul towerHermiteLvl2A (DensePoly.cmul gden2 hDen)
      DensePoly.cisZero (DensePoly.csub lhs rhs)) = true := by native_decide

/-- The level-2 residual denominator has degree 1. -/
theorem towerHermiteLvl2_residual_degreeWf :
    DensePoly.cdeg (DensePoly.cHermiteReduceTower towerHermiteLvl2Dt
      towerHermiteLvl2A towerHermiteLvl2D).2.2 = 1 := by native_decide

/-- The canonical representation recombines to `f` at level 2. -/
theorem towerCanRepLvl2_recombinesWf :
    (let res := DensePoly.canonicalRepresentationFast towerCanRepLvl2Dt
        towerCanRepLvl2A towerCanRepLvl2D
      let q := res.1
      let b := res.2.1.1
      let ds := res.2.1.2
      let c := res.2.2.1
      let dn := res.2.2.2
      let dsdn := DensePoly.cmul ds dn
      let num := DensePoly.cadd (DensePoly.cadd (DensePoly.cmul q dsdn) (DensePoly.cmul b dn))
        (DensePoly.cmul c ds)
      DensePoly.cisZero (DensePoly.csub (DensePoly.cmul num towerCanRepLvl2D)
        (DensePoly.cmul towerCanRepLvl2A dsdn))) = true := by native_decide

/-- The recovered level-2 logarithmic part has length 2: the residue scan over `ℚ(x)(t₁)[t₂]` finds
exactly the two rational residues `±1/2` (log arguments `t₂ ± 1`). -/
theorem towerIntLvl2_logs_lengthWf :
    (DensePoly.cIntegrateReduced towerIntLvl2Dt towerIntLvl2Num towerIntLvl2Den
      towerIntLvl2Cands).logs.length = 2 := by native_decide

/-- A full elementary tower integral at level 2 with `D(∫f) = f`. For
`f = (1/2)/(t₂+1) − (1/2)/(t₂−1)` over ℚ(x)(t₁)(t₂), the capstone `cIntegrateReduced` returns an
`IntegralResult` whose antiderivative identity `D(rational) + ∑ᵢ cᵢ·(D(vᵢ)/vᵢ) = f` holds exactly
(`checkIdentity`). -/
theorem towerIntLvl2_fullIntegralWf :
    DensePoly.checkIdentity towerIntLvl2Dt
      (DensePoly.cIntegrateReduced towerIntLvl2Dt towerIntLvl2Num towerIntLvl2Den
        towerIntLvl2Cands)
      towerIntLvl2Num towerIntLvl2Den = true := by native_decide

/-! ## The remaining RDE (PolyRischDE / SPDE) recursive bottoms

Two more `[CField α]`-generic degree-recursion bottoms of the RDE pipeline — the non-cancellation solve
`cPolyRischDENoCancel` and the SPDE `cSPDE`. The cancellation cases and the top driver `cRischDE`
continue in `Tower/RischDEWellFounded`. -/

namespace DensePoly

variable {α : Type*} [CField α] [CDiffField α]

/-- Generic non-cancellation Poly-Risch-DE `cPolyRischDENoCancel Dt b c n`: solves `Dq + b·q = c` for
`q ∈ α[t]` with `deg(q) ≤ n` (`n : ℤ`), top-down — `p = (lc(c)/lc(b))·tᵐ` (`m = deg(c) − deg(b)`), recurse on
`c' = c − D(p) − b·p` (`D = CPolyEngine.monomialDeriv Dt`). Returns `none` or `some q`. Well-founded on
`(cnorm c).length`. `[CField α] [CDiffField α]`-generic. -/
def cPolyRischDENoCancel (Dt : DensePoly α) (b c : DensePoly α) (n : ℤ) :
    Option (DensePoly α) :=
  if cisZero c then some []
  else
    let m : ℤ := (cdeg c : ℤ) - (cdeg b : ℤ)
    if n < 0 ∨ m < 0 ∨ m > n then none
    else
      let coeff := CField.div (clead c) (clead b)
      let p := cshift m.toNat [coeff]
      let c' := csub (csub c (CPolyEngine.monomialDeriv Dt p)) (cmul b p)
      if (cnorm c' : List α).length < (cnorm c : List α).length then
        match cPolyRischDENoCancel Dt b c' (m - 1) with
        | none => none
        | some q => some (cadd p q)
      else none   -- unreachable on a non-cancellation run (the leading term cancels, degree drops)
termination_by (cnorm c).length
decreasing_by assumption

end DensePoly

namespace DensePoly

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCoreWf α]

/-- Generic SPDE `cSPDE Dt a b c n`: the `g = gcd(a, b)`-peel reducing the degree-bounded
`a·Dq + b·q = c` to one with `a = 1`. Returns `none` or `some (b̄, c̄, m, α', β)` so any solution is
`q = α'·h + β` with `h` solving `Dh + b̄·h = c̄`, `deg(h) ≤ m`. Peels `g = cgcdFFCoreWf a b`; the constant
`a/g` base case returns the identity reconstruction, else solves the Bézout `CPoly.diophantineReduced b̄ ā c̄` and
recurses on `ā = a/g` at `n − deg(ā)`. Well-founded on `(n+1).toNat`. `[CField α] [CDiffField α]
[CFracGcdCoreWf α]`-generic. -/
def cSPDE (Dt : DensePoly α) (a b c : DensePoly α) (n : ℤ) :
    Option (DensePoly α × DensePoly α × ℤ × DensePoly α × DensePoly α) :=
  if n < 0 then
    if cisZero c then some ([], [], 0, [], []) else none
  else
    let g := CPolyGcd.compute a b
    if CPolyEuclidean.dvd g c then
      let a' := CPolyEuclidean.div a g
      let b' := CPolyEuclidean.div b g
      let c' := CPolyEuclidean.div c g
      if cdeg a' = 0 then
        let ainv := CField.inv (clead a')
        some (cscale ainv b', cscale ainv c', n, [CCommRing.one], [])
      else
        let (r, z) := CPoly.diophantineReduced b' a' c'
        let Da := CPolyEngine.monomialDeriv Dt a'
        let Dr := CPolyEngine.monomialDeriv Dt r
        if (n - (cdeg a' : ℤ) + 1).toNat < (n + 1).toNat then
          match cSPDE Dt a' (cadd b' Da) (csub z Dr) (n - (cdeg a' : ℤ)) with
          | none => none
          | some (bbar, cbar, m, α', β) =>
              some (bbar, cbar, m, cmul a' α', cadd (cmul a' β) r)
        else none   -- unreachable on a real run (`deg ā ≥ 1`, so the bound `n − deg ā` strictly drops)
    else none
termination_by (n + 1).toNat
decreasing_by assumption

end DensePoly

end DeepWiki.SymbolicIntegration
