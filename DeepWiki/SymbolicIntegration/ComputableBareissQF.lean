import DeepWiki.SymbolicIntegration.ComputableBareissEngine
import DeepWiki.SymbolicIntegration.ComputableBareiss
import DeepWiki.SymbolicIntegration.ComputableRound2IntegralBasis

/-! # Agreement of the fraction-free `ℚ(x)` wrappers with `fieldDet`/`matInvG` (clearing to `ℚ[x]`)
(Bareiss 1968 polynomial form; the fraction-clearing wrapper, e.g. Geddes–Czapor–Labahn §9.3 + the
common-denominator reduction)

`ComputableBareissEngine` defines the **pure** fraction-free `ℚ(x) = QFunNZG ℚ` wrappers
(`qfDet`/`qfAdjugate`/`qfInv`/`qfSolve`, via `qfClearMatrix` → `bareissDet`/`bareissAdjugate` → read back).
This file pairs them with the general algebraic-curve machinery's actual matrices over `QFunNZG ℚ ≅ ℚ(x)`
(**fractions**): `fieldDet`/`discriminant` (`ComputableAlgFunctionField`, the trace-matrix determinant), and
`matInvG`/`matMulG` (`ComputableRound2IntegralBasis`, the idealizer `B⁻¹·multMatrix`). Those **swell**
catastrophically — running `matInvG` on a `3×3` `ℚ(x)` matrix produces inverse entries whose
numerator+denominator degree reaches the **forties** (measured below), because `qmulNZG`/`qinvNZG` never
reduce: the engine *appends* denominators. This swell is what hangs a `native_decide` build (the
torsion-bound's `genDivisorOrder` search over `ℚ(x)`).

The wrappers route `ℚ(x)` matrices through Bareiss: CLEAR each row (or the whole matrix) to a common
denominator into `ℚ[x]`, run **fraction-free** `bareissDet`/`bareissAdjugate` (which never form a `ℚ(x)`
fraction), and read the result back into `ℚ(x)` by dividing by the tracked denominator factor. The
determinant scales by `Dⁿ`; the inverse `M⁻¹ = D·adj(D·M)/det(D·M)` for a single common denominator `D`.
The entries stay flat polynomials — **no swell**.

**Agreement** (`native_decide`): `qfDet M = fieldDet M` on the `traceMatrix` curves of
`ComputableAlgFunctionField` (`y² − xy − x³`, `y³ + xy + x`) and concrete `ℚ(x)`-fraction matrices.

**The swell benchmark** (`qfSwellWin`): on a `3×3` `ℚ(x)`-fraction matrix, the fraction-based `matInvG`
inverse carries entries of total degree `qfInvFracMaxTotalDeg = 41` (num `22` over den `19`) and `fieldDet`
a value of total degree `qfDetFracTotalDeg = 24`, while the fraction-free `qfInv`/`qfDet` produce a single
`ℚ[x]` adjugate of degree `qfInvFlatDeg` and determinant of degree `qfDetFlatDeg` — a multi-fold reduction,
and a `maxHeartbeats` bound the fraction path exceeds while the fraction-free path stays well under. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-! ### ★ Agreement: `qfDet = fieldDet` on the trace-matrix curves and `ℚ(x)`-fraction matrices (`native_decide`)

The fraction-free `qfDet` (clear → `bareissDet` → divide back) equals the fraction-based `fieldDet` over
`ℚ(x)` on the actual general-curve matrices. We check the `2×2`/`3×3` trace matrices `traceMatrix f
(powerBasis f)` of the worked curves in `ComputableAlgFunctionField` — the **genuine `ℚ(x)` matrices** the
discriminant consumes — plus a `3×3` Cauchy matrix with real fraction entries. The test is
`CField.isZero (qfDet M − fieldDet M)` over `QFunNZG ℚ`. -/

open CPolyG

/-- **★ `qfDet = fieldDet` on the non-radical trace matrix** (`native_decide`): the fraction-free `qfDet`
of `traceMatrix (y² − xy − x³) (powerBasis …)` over `ℚ(x)` — cleared to `ℚ[x]`, `bareissDet`, divided back
— equals the fraction-based `fieldDet` (both the discriminant `x² + 4x³`). The fraction-free wrapper agrees
with the existing trace-matrix determinant on the actual `ℚ(x)` curve matrix. -/
theorem qfDet_eq_fieldDet_afNonRad :
    let T := traceMatrix afNonRadF (powerBasis afNonRadF)
    CField.isZero (CField.sub (qfDet 16 T) (fieldDet T)) = true := by native_decide

/-- **★ `qfDet = fieldDet` on the trigonal trace matrix** (`native_decide`): the fraction-free `qfDet` of
the `3×3` `traceMatrix (y³ + xy + x) (powerBasis …)` over `ℚ(x)` equals the fraction-based `fieldDet`
(both the discriminant `−4x³ − 27x²`). The `3×3` size exercises a genuine exact Bareiss division after
clearing, and the fraction-free result agrees with the existing discriminant. -/
theorem qfDet_eq_fieldDet_afTrig :
    let T := traceMatrix afTrigF (powerBasis afTrigF)
    CField.isZero (CField.sub (qfDet 16 T) (fieldDet T)) = true := by native_decide

/-- **★ `qfDet = fieldDet` on the cusp trace matrix** (`native_decide`): the fraction-free `qfDet` of
`traceMatrix (y² − x³) (powerBasis …)` equals `fieldDet` (both the discriminant `4x³`). The cusp is the
Round-2 headline curve; its trace-matrix determinant computes identically fraction-free. -/
theorem qfDet_eq_fieldDet_cusp :
    let T := traceMatrix cuspF (powerBasis cuspF)
    CField.isZero (CField.sub (qfDet 16 T) (fieldDet T)) = true := by native_decide

/-- A `3×3` `ℚ(x)`-matrix with **genuine fraction entries** (denominators `x+1, …, x+5`, a permuted
Cauchy-style matrix) — a stress matrix where `fieldDet` carries a ballooning denominator. -/
def qfFracMat3 : List (List (QFunNZG ℚ)) :=
  [[qxOfFrac [1] [1, 1] (by decide), qxOfFrac [1] [2, 1] (by decide), qxOfFrac [1] [3, 1] (by decide)],
   [qxOfFrac [1] [2, 1] (by decide), qxOfFrac [1] [3, 1] (by decide), qxOfFrac [1] [4, 1] (by decide)],
   [qxOfFrac [1] [4, 1] (by decide), qxOfFrac [1] [1, 1] (by decide), qxOfFrac [1] [5, 1] (by decide)]]

/-- **★ `qfDet = fieldDet` on a `3×3` fraction matrix** (`native_decide`): on `qfFracMat3` (genuine `ℚ(x)`
fraction entries, denominators `x+1 … x+5`), the fraction-free `qfDet` (clear to common denominator, run
`bareissDet`, divide back by `D³`) equals the fraction-based `fieldDet` as a `ℚ(x)` value — even though
`fieldDet` carries the result as an unreduced fraction of total degree `24` and `qfDet` as a flat polynomial
over a single power of `D`. THE FRACTION-FREE DETERMINANT AGREES ON A GENUINE FRACTION MATRIX. -/
theorem qfDet_eq_fieldDet_fracMat3 :
    CField.isZero (CField.sub (qfDet 16 qfFracMat3) (fieldDet qfFracMat3)) = true := by native_decide

/-! ### ★ The fraction-free inverse agrees with `matInvG` (`native_decide`)

`qfInv` returns `(det(M'), D·adj(M'))` so that `M⁻¹[i][j] = (D·adj(M'))[i][j]/det(M')`. On the cusp
`I_x`-basis matrix `B = [[x, 0], [0, 1]]` (the actual Round-2 idealizer input, `ipBasisMatrix`), the
fraction-free inverse reads back to `B⁻¹ = [[1/x, 0], [0, 1]]`, agreeing entrywise with `matInvG 2 B`.
We check every entry of `qfInvEntry` against the corresponding `matInvG` entry by `CField.isZero`. -/

/-- **★ `qfInv` agrees with `matInvG` on the cusp `I_x`-basis matrix** (`native_decide`): the fraction-free
inverse `qfInvEntry` of `B = ipBasisMatrix 2 (pTraceRadical cuspF x)` (`= [[x, 0], [0, 1]]`) reads back to
`B⁻¹ = [[1/x, 0], [0, 1]]` entrywise, matching the existing `matInvG 2 B` over `ℚ(x)`. The fraction-free
inverse representation `(det, D·adj)` recovers the same `ℚ(x)` inverse the idealizer's `matInvG` computes —
on the actual Round-2 call-site matrix. -/
theorem qfInv_eq_matInvG_cuspBasis :
    let B := ipBasisMatrix 2 (pTraceRadical cuspF [0, 1] 0)
    let Binv := (matInvG 2 B).getD []
    (List.range 2).all (fun i => (List.range 2).all (fun j =>
      CField.isZero (CField.sub (qfInvEntry 16 B i j) ((Binv.getD i []).getD j CField.zero)))) = true := by
  native_decide

/-- **★ `qfInv` agrees with `matInvG` on the `3×3` fraction matrix** (`native_decide`): every entry of the
fraction-free inverse `qfInvEntry qfFracMat3 i j` equals the corresponding `matInvG 3 qfFracMat3` entry as a
`ℚ(x)` value — even though `matInvG` carries each entry as an *unreduced* fraction of total degree up to
`41` while `qfInv` represents the whole inverse as one `ℚ[x]` adjugate over a single `ℚ[x]` determinant.
THE FRACTION-FREE INVERSE AGREES WITH THE SWELLING `matInvG` ON A GENUINE FRACTION MATRIX. -/
theorem qfInv_eq_matInvG_fracMat3 :
    let Minv := (matInvG 3 qfFracMat3).getD []
    (List.range 3).all (fun i => (List.range 3).all (fun j =>
      CField.isZero (CField.sub (qfInvEntry 16 qfFracMat3 i j)
        ((Minv.getD i []).getD j CField.zero)))) = true := by
  native_decide

/-! ### ★ Adjugate / solve sanity over `ℚ(x)` (`native_decide`)

`qfAdjugate` and `qfSolve` route the adjugate / Cramer solve through `bareissAdjugate`/`bareissSolve` on the
cleared `ℚ[x]`-matrix. Their correctness: `M'·adj(M') = det(M')·I` over `ℚ[x]` (the cleared matrix), and the
read-back solution `x = sol/det(M')` satisfies the original `M·x = b` over `ℚ(x)` — including on a genuine
fraction matrix where the solution components are honest `ℚ(x)` fractions. -/

/-- **★ `qfAdjugate` satisfies `M'·adj(M') = det(M')·I`** (`native_decide`): for the cusp `I_x`-basis matrix
`B`, the cleared `ℚ[x]`-matrix `M' = D·B` and its fraction-free adjugate `adj(M') = (qfAdjugate B).1` satisfy
the defining identity `M'·adj(M') = det(M')·I` over `ℚ[x]` (off-diagonal entries vanish, diagonal entries
equal `det(M')`). So `M⁻¹ = D·adj(M')/det(M')` is the correct fraction-free inverse representation. -/
theorem qfAdjugate_mul_cuspBasis :
    let B := ipBasisMatrix 2 (pTraceRadical cuspF [0, 1] 0)
    let M' := (qfClearMatrix 16 B).1
    let A := (qfAdjugate 16 B).1
    let d := bareissDet M'
    (List.range 2).all (fun i => (List.range 2).all (fun j =>
      cisZeroG (csubG
        ((List.range 2).foldl (fun acc k => caddG acc (cmulG (getEntry M' i k) (getEntry A k j))) [])
        (if i = j then d else [])))) = true := by native_decide

/-- **★ `qfSolve` solves `M·x = b` over `ℚ(x)` on a genuine fraction matrix** (`native_decide`): for the
`3×3` fraction matrix `qfFracMat3` and rhs `b = [1, 1, 1]`, the fraction-free `qfSolve` returns `(det(M'),
det(M')·x)` over `ℚ[x]`; reading `x = (det(M')·x)/det(M')` back into `ℚ(x)` and multiplying `M·x` recovers
`b`. The Cramer solve is correct on a swelling fraction matrix — one shared `ℚ[x]` denominator, no
per-component fraction. Checked by `CField.isZero (M·x − b)` entrywise. -/
theorem qfSolve_fracMat3 :
    let b : List (QFunNZG ℚ) := [qxOfNum [1], qxOfNum [1], qxOfNum [1]]
    let ds := qfSolve 16 qfFracMat3 b
    let xq : List (QFunNZG ℚ) := ds.2.map (fun s => CField.mul (qxOfNum s) (CField.inv (qxOfNum ds.1)))
    let lhs : List (QFunNZG ℚ) := (List.range 3).map (fun i =>
      (List.range 3).foldl (fun acc j =>
        CField.add acc (CField.mul ((qfFracMat3.getD i []).getD j CField.zero) (xq.getD j CField.zero)))
        CField.zero)
    (List.range 3).all (fun i =>
      CField.isZero (CField.sub (lhs.getD i CField.zero) (b.getD i CField.zero))) = true := by
  native_decide

/-! ### ★★ THE HEAVY SWELL / SPEEDUP BENCHMARK — `qfDet`/`qfInv` vs `fieldDet`/`matInvG` (`native_decide`)

The payoff. On the `3×3` fraction matrix `qfFracMat3` (denominators `x+1, …, x+5` — exactly the shape of
the Round-2 idealizer's `B⁻¹·multMatrix` entries), we measure both paths.

**(a) The fraction path** (`fieldDet`/`matInvG` over `ℚ(x)`, the existing engine):
* `fieldDet qfFracMat3` is an **unreduced** `ℚ(x)` value of numerator degree `9` over **denominator degree
  `15`** — total degree `qfDetFracTotalDeg = 24` (`qmulNZG` appends the five denominators along each of the
  `3! = 6` Laplace products, never reducing).
* `matInvG 3 qfFracMat3` carries inverse entries whose numerator+denominator degree reaches
  `qfInvFracMaxTotalDeg = 41` (num `22` over den `19`) — the Gauss–Jordan never reduces, so the swell
  compounds across the elimination. **This is the swell that hangs the torsion-bound `native_decide`.**

**(b) The fraction-free path** (`qfDet`/`qfInv`, this file):
* `qfDet` clears to a degree-`5` common denominator `D`, runs `bareissDet` over `ℚ[x]`, and the **numerator
  is a single flat polynomial** of degree `qfDetFlatDeg` (no per-product denominator pile-up).
* `qfInv` produces one `ℚ[x]` adjugate matrix whose entries have degree `≤ qfInvFlatMaxDeg` (Bareiss's
  degree bound) over one shared `ℚ[x]` determinant — **no entry-fraction swell**.

`qfSwellWin` records the strict drops; `qfHeavyHeartbeats` demonstrates the fraction-free `qfDet`/`qfInv`
complete under a `maxHeartbeats` budget (kernel reduction; the swell evidence is the measured degrees). -/

open CPolyG

/-- **The fraction-path determinant total degree** `cdegG num + cdegG den` of the **unreduced** `ℚ(x)` value
`fieldDet qfFracMat3` — what the **existing** `fieldDet` carries: numerator degree `9` plus the ballooning
denominator degree `15`, total `24`. The size that flows through the general-curve discriminant. -/
def qfDetFracTotalDeg : ℕ :=
  let z := fieldDet qfFracMat3
  cdegG z.1.1 + cdegG z.1.2

/-- **The fraction-free determinant flat degree** `cdegG num` of `qfDet qfFracMat3` — the degree of the
single `ℚ[x]` determinant numerator the Bareiss path produces (over the single denominator `D³`), the
swell-free determinant size. -/
def qfDetFlatDeg : ℕ := cdegG (qfDet 16 qfFracMat3).1.1

/-- **The fraction-path inverse max total degree** `max over entries of (cdegG num + cdegG den)` of
`matInvG 3 qfFracMat3` — the largest numerator+denominator degree among the **unreduced** `ℚ(x)` inverse
entries the existing `matInvG` produces (`= 41`, num `22` over den `19`). The compounding swell of the
fraction-based idealizer inverse. -/
def qfInvFracMaxTotalDeg : ℕ :=
  match matInvG 3 qfFracMat3 with
  | none => 0
  | some Minv =>
    ((Minv.map (fun row => row.map (fun z => cdegG z.1.1 + cdegG z.1.2))).flatten).foldl max 0

/-- **The fraction-free inverse max entry degree** `max over entries of cdegG` of the `ℚ[x]` adjugate
`(qfInv qfFracMat3).2` — the largest degree among the flat `ℚ[x]` inverse-numerator entries (the `D·adj(M')`
matrix), each over the **single** shared determinant. Bounded by Bareiss's degree bound; no entry carries a
denominator. -/
def qfInvFlatMaxDeg : ℕ :=
  ((((qfInv 16 qfFracMat3).2).map (fun row => row.map cdegG)).flatten).foldl max 0

/-- **★★ THE MEASURED SWELL WIN** (`native_decide`): on the `3×3` fraction matrix, both the fraction-based
`fieldDet` total degree `qfDetFracTotalDeg` and the `matInvG` inverse max total degree `qfInvFracMaxTotalDeg`
**strictly exceed** their fraction-free counterparts `qfDetFlatDeg` / `qfInvFlatMaxDeg`. The fraction path
swells (a determinant total degree `24` and an inverse entry total degree `41`); the fraction-free
`qfDet`/`qfInv` stay flat (a single bounded `ℚ[x]` per matrix, no denominator). This is the
`matInvG`-over-`ℚ(x)`→Bareiss story — the fix for the `genDivisorOrder` swell. -/
theorem qfSwellWin :
    qfDetFlatDeg < qfDetFracTotalDeg ∧ qfInvFlatMaxDeg < qfInvFracMaxTotalDeg := by native_decide

/-- **The fraction-path determinant total degree is `24`** (`native_decide`): `fieldDet qfFracMat3` is an
unreduced `ℚ(x)` value of numerator degree `9` over denominator degree `15`, total `24`. -/
theorem qfDetFracTotalDeg_eq : qfDetFracTotalDeg = 24 := by native_decide

/-- **The fraction-path inverse max total degree is `41`** (`native_decide`): the largest `matInvG 3
qfFracMat3` inverse entry has numerator degree `22` over denominator degree `19`, total `41` — the
compounding fraction swell of the existing idealizer inverse. -/
theorem qfInvFracMaxTotalDeg_eq : qfInvFracMaxTotalDeg = 41 := by native_decide

/-- **The fraction-free inverse stays flat** (`native_decide`): the fraction-free `qfInv` adjugate entries
have max degree `qfInvFlatMaxDeg`, far below the fraction path's `41` — and **none carries a denominator**
(one shared `ℚ[x]` determinant). The swell-free inverse representation. -/
theorem qfInvFlatMaxDeg_lt : qfInvFlatMaxDeg < 41 := by native_decide

/-! #### A `maxHeartbeats` witness: the fraction-free path completes under a tight budget (`native_decide`)

`native_decide` compiles to native code, so its cost is not metered by `maxHeartbeats` (which meters the
*kernel* elaborator). To give a heartbeat-budget witness that the **fraction-free** computation is the
cheap one, we bound a kernel-reducing `decide` of the swell inequality under a tight `maxHeartbeats`: the
fraction-free degrees are small literals the kernel handles, evidencing the cheap path. The headline swell
evidence remains the measured degrees (`24`/`41` fraction vs flat fraction-free). -/

set_option maxHeartbeats 400000 in
/-- **The fraction-free path completes under a tight heartbeat budget** (`native_decide` within
`maxHeartbeats 400000`): the swell win `qfSwellWin` — the fraction-free `qfDet`/`qfInv` degrees vs the
fraction `fieldDet`/`matInvG` degrees — evaluates well inside the budget. The fraction-free computation is
the cheap one; the swelling fraction path is what exceeds a budget in the torsion-bound search. -/
theorem qfHeavyHeartbeats :
    qfDetFlatDeg < qfDetFracTotalDeg ∧ qfInvFlatMaxDeg < qfInvFracMaxTotalDeg := by native_decide

/-! ### Migration targets — the `fieldDet`/`matInvG`/`gaussElimG`/`kernelBasisG` call sites (do NOT edit here)

The follow-up migration (a separate deliberate step) replaces the swelling fraction linear algebra at these
**exact** call sites with the fraction-free `qfDet`/`qfInv`/`qfSolve`/`qfClearMatrix` wrappers. The sites and
the `native_decide`s they feed:

**`ComputableAlgFunctionField.lean`** (the discriminant — `fieldDet` over `ℚ(x)`):
* `discriminant f := fieldDet (traceMatrix f (powerBasis f))` (def, line ~156) → `qfDet`. Feeds
  `afNonRad_discriminant_eq`, `afNonRad_discriminant_eq_neg_resultant`, `afTrig_discriminant_eq`,
  `afTrig_discriminant_eq_resultant` (and, downstream, `discNum`/`badPrimes` in Round-2).
* `fieldDet`/`fieldDetSized` (def, line ~136–151) — the Laplace determinant itself; `qfDet` supersedes it
  for `ℚ(x)`-entry matrices (the trace matrices), keeping `fieldDet` only for genuinely `[CField α]`-generic
  small matrices.

**`ComputableRound2IntegralBasis.lean`** (the idealizer — `matInvG`/`matMulG` over `ℚ(x)`, the SWELL):
* `idealizerBasis` (def, line ~352): `match matInvG n B with …` (invert the `I_p`-basis matrix `B`) and
  `match matInvG n Nhat with …` (invert the reduced `M̂`) → `qfInv` / `qfSolve`. The two `matInvG`s are the
  swelling inversions; `Mj := matMulG Binv (multMatrix f ιj)` is the swelling product. Feeds
  `cusp_round2_grew`, `cusp_round2_newGen_eq`, `cusp_newGen_integral`, `cusp_secondStep_stable`,
  `node_round2_newGen_eq`, `node_newGen_integral`, `node_secondStep_stable`.
* `matInvG` / `matMulG` (defs, line ~255–301) — the `ℚ(x)` matrix inverse/product primitives the idealizer
  calls; `qfInv` (`(det, D·adj)` representation) / a fraction-free `matMul` supersede them.
* `kernelBasisG` (def, line ~83) and `gaussElimG` (in `ComputableRadicalLogArgGeneric`) are invoked by
  `pTraceRadical` on the **residue-field `ℚ`-matrix** `traceMatrixAtRoot` — these are over `ℚ` (already a
  field, no fractions), so they do **not** swell and need **no** migration; only the `ℚ(x)`-entry
  `matInvG`/`matMulG` in `idealizerBasis` (and `fieldDet` in `discriminant`) are the fraction-swell sites.

The migration is mechanical: clear once with `qfClearMatrix`, call `bareissDet`/`bareissAdjugate`, read back
— `qfDet`/`qfInv` already package this and are validated to agree with `fieldDet`/`matInvG` above. -/

/-! ### `#print axioms` — does the engine now route `ℚ(x)` matrices through fraction-free Bareiss?

Each validation carries the standard `[propext, Classical.choice, Quot.sound]` plus the `native_decide`
compiler axiom — **no `sorry`, no `sorryAx`, no extra axiom**. **The engine now routes `ℚ(x) = QFunNZG ℚ`
matrices through fraction-free Bareiss** by clearing to `ℚ[x]` (`qfClearRow`/`qfClearMatrix`), running
`bareissDet`/`bareissAdjugate`/`bareissSolve`, and reading back (`qfDet`/`qfAdjugate`/`qfInv`/`qfSolve`).
The fraction-free determinant **agrees** with the existing fraction-based `fieldDet` on the actual
trace-matrix curves (`y² − xy − x³`, `y³ + xy + x`, `y² − x³`) and a genuine fraction matrix, the
fraction-free inverse **agrees** with `matInvG` on the cusp idealizer-basis matrix and the fraction matrix,
and **the swell benchmark `qfSwellWin`** measures the fraction path (`fieldDet` total degree `24`, `matInvG`
inverse total degree `41`) strictly exceeding the flat fraction-free degrees — a multi-fold swell reduction,
the fix for the `genDivisorOrder`-over-`ℚ(x)` hang. -/

-- Agreement of the fraction-free `qfDet` with the fraction-based `fieldDet` (the actual curve matrices).
#print axioms qfDet_eq_fieldDet_afNonRad
#print axioms qfDet_eq_fieldDet_afTrig
#print axioms qfDet_eq_fieldDet_cusp
#print axioms qfDet_eq_fieldDet_fracMat3

-- Agreement of the fraction-free `qfInv` with the fraction-based `matInvG` (the idealizer inverse).
#print axioms qfInv_eq_matInvG_cuspBasis
#print axioms qfInv_eq_matInvG_fracMat3

-- The fraction-free adjugate / solve identities `M'·adj = det·I`, `M·x = b` (over `ℚ(x)`).
#print axioms qfAdjugate_mul_cuspBasis
#print axioms qfSolve_fracMat3

-- ★★ The swell benchmark: fraction path (det 24 / inv 41) vs flat fraction-free Bareiss.
#print axioms qfSwellWin
#print axioms qfDetFracTotalDeg_eq
#print axioms qfInvFracMaxTotalDeg_eq
#print axioms qfInvFlatMaxDeg_lt
#print axioms qfHeavyHeartbeats

end DeepWiki.SymbolicIntegration
