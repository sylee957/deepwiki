import DeepWiki.NetworkCalculus.PwlBreakpoints
import DeepWiki.NetworkCalculus.Deviations

/-! # Finiteness of the maximal uncertainty (Definition 4.4)
The §4.4.2 maximal uncertainty of a container is **finite** once the two bounds
come from the canonical form: both are convex PWL `convexSegEval` curves sharing
the same final/asymptotic slope `fs` (the asymptotic typing `ρ_{f̲} = ρ_{f̄}`).

For `f̄ = convexSegEval a fs segA` and `f̲ = convexSegEval b fs segB` with the
same final slope `fs`, past the rank `R = max (pwlRank segA) (pwlRank segB)` both
curves are affine of slope `fs`, so the vertical gap `f̄ t − f̲ t` is **constant**
for `t ≥ R` (`convexSegEval_past_rank` on both, then `add_tsub_add_eq_tsub_right`).
Before `R` the gap is bounded by the monotone value `f̄ R`. Hence the vertical
deviation `vDev f̄ f̲ = ⨆ₜ (f̄ t − f̲ t)` (taken on the `ℝ≥0∞` readings, the
`Deviation.backlog` reading) is finite: `< ⊤`, with explicit bound `↑(f̄ R)`.

This realizes the catalog's note that Def 4.4's finiteness from the canonical
form "needs an intrinsic rank/last-segment layer" — `pwlRank` is that layer. -/

namespace DeepWiki

open scoped NNReal ENNReal

namespace MaxUncertaintyFinite

/-- The `ℝ≥0∞` reading of a convex PWL `convexSegEval a fs segs`, on which the
vertical deviation `vDev` is taken (so an unbounded gap would read `⊤`). -/
noncomputable abbrev coeENN (a fs : ℝ≥0) (segs : List (ℝ≥0 × ℝ≥0)) : ℝ≥0 → ℝ≥0∞ :=
  fun t => (convexSegEval a fs segs t : ℝ≥0∞)

/-- The shared finiteness rank of two convex PWL curves: the larger of the two
abscissae where the semi-infinite (slope `fs`) segments begin,
`R = max (pwlRank segA) (pwlRank segB)`. Past `R` both curves are affine. -/
noncomputable def jointRank (segA segB : List (ℝ≥0 × ℝ≥0)) : ℝ≥0 :=
  max (pwlRank segA) (pwlRank segB)

@[simp] theorem pwlRank_le_jointRank_left (segA segB : List (ℝ≥0 × ℝ≥0)) :
    pwlRank segA ≤ jointRank segA segB := le_max_left _ _

@[simp] theorem pwlRank_le_jointRank_right (segA segB : List (ℝ≥0 × ℝ≥0)) :
    pwlRank segB ≤ jointRank segA segB := le_max_right _ _

/-! ## Past-rank constant gap -/

/-- **Past the rank a convex PWL grows at pure slope `fs`.** For `pwlRank seg ≤
t' ≤ t`, the increment is `convexSegEval c fs seg t = convexSegEval c fs seg t' +
fs · (t − t')` — past the rank the curve is affine, so increments are pure
slope. -/
theorem convexSegEval_sub_past_rank (c fs : ℝ≥0) (seg : List (ℝ≥0 × ℝ≥0))
    {t t' : ℝ≥0} (ht' : pwlRank seg ≤ t') (htt' : t' ≤ t) :
    convexSegEval c fs seg t = convexSegEval c fs seg t' + fs * (t - t') := by
  have ht : pwlRank seg ≤ t := le_trans ht' htt'
  rw [convexSegEval_past_rank c fs seg ht, convexSegEval_past_rank c fs seg ht']
  rw [add_assoc, ← mul_add]
  congr 2
  rw [add_comm (t' - pwlRank seg) (t - t'),
    tsub_add_tsub_cancel htt' ht']

/-- **The vertical gap is constant past the joint rank.** For curves of the same
final slope `fs`, `R ≤ t` gives `f̄ t − f̲ t = f̄ R − f̲ R` (`R = jointRank segA
segB`): past `R` both curves grow by the same `fs · (t − R)`, which cancels in the
truncated subtraction (`add_tsub_add_eq_tsub_right`). -/
theorem vDevAt_eq_past_jointRank (a b fs : ℝ≥0) (segA segB : List (ℝ≥0 × ℝ≥0))
    {t : ℝ≥0} (ht : jointRank segA segB ≤ t) :
    convexSegEval a fs segA t - convexSegEval b fs segB t
      = convexSegEval a fs segA (jointRank segA segB)
          - convexSegEval b fs segB (jointRank segA segB) := by
  rw [convexSegEval_sub_past_rank a fs segA (le_max_left _ _) ht,
    convexSegEval_sub_past_rank b fs segB (le_max_right _ _) ht]
  exact add_tsub_add_eq_tsub_right _ _ _

/-- **Past-rank vertical-deviation stabilization** (`ℝ≥0∞` reading). For `R ≤ t`,
`vDevAt f̄ f̲ t = vDevAt f̄ f̲ R` with `R = jointRank segA segB`: the `ℝ≥0∞`
vertical gap stabilizes at the rank value. -/
theorem vDevAt_coeENN_eq_past_jointRank (a b fs : ℝ≥0)
    (segA segB : List (ℝ≥0 × ℝ≥0)) {t : ℝ≥0} (ht : jointRank segA segB ≤ t) :
    vDevAt (coeENN a fs segA) (coeENN b fs segB) t
      = vDevAt (coeENN a fs segA) (coeENN b fs segB) (jointRank segA segB) := by
  unfold vDevAt coeENN
  rw [← ENNReal.coe_sub, ← ENNReal.coe_sub]
  exact congrArg _ (vDevAt_eq_past_jointRank a b fs segA segB ht)

/-! ## A uniform finite bound on the vertical deviation -/

/-- **Uniform per-point bound.** At every `t` the vertical gap of two convex PWLs
with the same final slope is bounded by the upper curve's value at the joint
rank: `f̄ t − f̲ t ≤ f̄ R` (`R = jointRank segA segB`). Before `R` the gap is at
most `f̄ t ≤ f̄ R` (monotone); past `R` it is the constant `f̄ R − f̲ R ≤ f̄ R`. -/
theorem vDevAt_le_apply_jointRank (a b fs : ℝ≥0) (segA segB : List (ℝ≥0 × ℝ≥0))
    (t : ℝ≥0) :
    convexSegEval a fs segA t - convexSegEval b fs segB t
      ≤ convexSegEval a fs segA (jointRank segA segB) := by
  rcases le_total (jointRank segA segB) t with ht | ht
  · -- past the rank: gap is the constant `f̄ R − f̲ R ≤ f̄ R`
    rw [vDevAt_eq_past_jointRank a b fs segA segB ht]
    exact tsub_le_self
  · -- before the rank: `f̄ t − f̲ t ≤ f̄ t ≤ f̄ R`
    exact le_trans tsub_le_self ((monotone_convexSegEval fs segA a) ht)

/-- **Uniform per-point bound, `ℝ≥0∞` reading.**
`vDevAt f̄ f̲ t ≤ ↑(f̄ R)` for every `t`. -/
theorem vDevAt_coeENN_le_coe (a b fs : ℝ≥0) (segA segB : List (ℝ≥0 × ℝ≥0))
    (t : ℝ≥0) :
    vDevAt (coeENN a fs segA) (coeENN b fs segB) t
      ≤ (convexSegEval a fs segA (jointRank segA segB) : ℝ≥0∞) := by
  unfold vDevAt coeENN
  rw [← ENNReal.coe_sub]
  exact_mod_cast vDevAt_le_apply_jointRank a b fs segA segB t

/-! ## Finiteness of `Bmax` -/

/-- **The vertical deviation is bounded by the corner value at the joint rank.**
`vDev f̄ f̲ ≤ ↑(f̄ R)` — the explicit finite upper bound on the data-domain
maximal uncertainty `Bmax` of a canonical container (curves of equal final slope
`fs`). -/
theorem vDev_coeENN_le_coe (a b fs : ℝ≥0) (segA segB : List (ℝ≥0 × ℝ≥0)) :
    vDev (coeENN a fs segA) (coeENN b fs segB)
      ≤ (convexSegEval a fs segA (jointRank segA segB) : ℝ≥0∞) :=
  vDev_le fun t => vDevAt_coeENN_le_coe a b fs segA segB t

/-- **Definition 4.4 finiteness — `Bmax` is finite.** When both container bounds
come from the canonical form (convex PWL `convexSegEval` curves sharing the same
final slope `fs`), the data-domain maximal uncertainty `Bmax = vDev (f̄, f̲)` is
finite: `vDev f̄ f̲ ≠ ⊤`. -/
theorem vDev_coeENN_ne_top (a b fs : ℝ≥0) (segA segB : List (ℝ≥0 × ℝ≥0)) :
    vDev (coeENN a fs segA) (coeENN b fs segB) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.coe_ne_top (vDev_coeENN_le_coe a b fs segA segB)

/-- **Definition 4.4 finiteness — `Bmax < ⊤`.** The strict-inequality form: the
data-domain maximal uncertainty of a canonical container is strictly below `⊤`. -/
theorem vDev_coeENN_lt_top (a b fs : ℝ≥0) (segA segB : List (ℝ≥0 × ℝ≥0)) :
    vDev (coeENN a fs segA) (coeENN b fs segB) < ⊤ :=
  lt_of_le_of_lt (vDev_coeENN_le_coe a b fs segA segB) ENNReal.coe_lt_top

/-- **Definition 4.4 finiteness — `Bmax` is a real number.** There is an `ℝ≥0`
value `B` with `Bmax = ↑B`: the data-domain maximal uncertainty of a canonical
container is an honest finite number, not `⊤`. -/
theorem exists_coe_vDev_coeENN (a b fs : ℝ≥0) (segA segB : List (ℝ≥0 × ℝ≥0)) :
    ∃ B : ℝ≥0, vDev (coeENN a fs segA) (coeENN b fs segB) = (B : ℝ≥0∞) :=
  ⟨_, (ENNReal.coe_toNNReal (vDev_coeENN_ne_top a b fs segA segB)).symm⟩

/-! ## Faithfulness checks (against §4.4, book p. 89) -/

/-- Faithfulness: past the joint rank the vertical gap is the constant rank-value
gap (the asymptotes are parallel, slope `fs`). -/
example (a b fs : ℝ≥0) (segA segB : List (ℝ≥0 × ℝ≥0)) {t : ℝ≥0}
    (ht : jointRank segA segB ≤ t) :
    convexSegEval a fs segA t - convexSegEval b fs segB t
      = convexSegEval a fs segA (jointRank segA segB)
          - convexSegEval b fs segB (jointRank segA segB) :=
  vDevAt_eq_past_jointRank a b fs segA segB ht

/-- Faithfulness: `Bmax = vDev(f̄, f̲)` of a canonical container (equal final
slope) is finite, `< ⊤`. -/
example (a b fs : ℝ≥0) (segA segB : List (ℝ≥0 × ℝ≥0)) :
    vDev (coeENN a fs segA) (coeENN b fs segB) < ⊤ :=
  vDev_coeENN_lt_top a b fs segA segB

end MaxUncertaintyFinite

end DeepWiki
