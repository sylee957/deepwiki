import Book.ArrivalCurveShaper

/-! # Greedy shapers
The greedy shaper outputs exactly `A ∗ σ`: the relation `greedyRel σ`, its
server status for `σ 0 ≤ 0`, and — for sub-additive nonnegative `σ` — that a
greedy shaper is a `σ`-shaper. -/

namespace DeepWiki

open scoped Classical NNReal

/-- `S` is a greedy shaper for `sigma`: every output is exactly `A ∗ sigma`. -/
def IsGreedyShaper (sigma : ℝ≥0 → EReal) (S : Curve → Curve → Prop) : Prop :=
  ∀ A D : Curve, S A D → curveE D = minConv (curveE A) sigma

/-- The greedy-shaper relation: the output is exactly `A ∗ sigma`. -/
def greedyRel (sigma : ℝ≥0 → EReal) : Curve → Curve → Prop :=
  fun A D => curveE D = minConv (curveE A) sigma

/-- `greedyRel sigma A D` unfolds to `D = A ∗ sigma` (via `curveE`). -/
theorem mem_greedyRel_iff {sigma : ℝ≥0 → EReal} {A D : Curve} :
    greedyRel sigma A D ↔ curveE D = minConv (curveE A) sigma :=
  Iff.rfl

/-- `IsGreedyShaper sigma S` iff `S ≤ greedyRel sigma`. -/
theorem isGreedyShaper_iff_subset {S : Curve → Curve → Prop}
    {sigma : ℝ≥0 → EReal} :
    IsGreedyShaper sigma S ↔
      ∀ A D : Curve, S A D → greedyRel sigma A D :=
  Iff.rfl

/-- When `sigma 0 ≤ 0`, `greedyRel sigma` is a server: causality is
`A ∗ sigma ≤ A` (`minConv_self_le`), left-totality is the supplied witness
`htot` (the convolution must again be a `Curve`). -/
theorem isServer_greedyRel {sigma : ℝ≥0 → EReal} (h0 : sigma 0 ≤ 0)
    (htot : ∀ A : Curve, ∃ D : Curve, greedyRel sigma A D) :
    IsServer (greedyRel sigma) :=
  ⟨fun A D hp => curveE_le_iff.mp
      (le_trans (le_of_eq (hp : curveE D = _)) (minConv_self_le h0 A)),
    htot⟩

/-- A sub-additive `sigma` allows itself as an arrival curve. -/
theorem isMaximalArrivalCurve_self_of_subadditive {sigma : ℝ≥0 → EReal}
    (hsub : IsSubadditive sigma) :
    IsMaximalArrivalCurve sigma sigma :=
  (isMaximalArrivalCurve_iff_increment sigma sigma).mpr hsub

/-- For nonnegative `f` and sub-additive nonnegative `sigma`, the greedy
output `f ∗ sigma` allows `sigma`. -/
theorem isMaximalArrivalCurve_minConv_of_subadditive
    {f sigma : ℝ≥0 → EReal} (hf : IsNonneg f) (hnn : IsNonneg sigma)
    (hsub : IsSubadditive sigma) :
    IsMaximalArrivalCurve (minConv f sigma) sigma := by
  refine (isMaximalArrivalCurve_iff_increment _ _).mpr (fun u s => ?_)
  show minConv f sigma (u + s) ≤ minConv f sigma u + sigma s
  have hbot : (⨅ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = u},
      f p.1.1 + sigma p.1.2) ≠ ⊥ :=
    ne_bot_of_nonneg (le_iInf (fun p =>
      add_nonneg (hf p.1.1) (hnn p.1.2)))
  have hexch :
      (⨅ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = u},
          sigma s + (f p.1.1 + sigma p.1.2))
        ≤ sigma s + minConv f sigma u :=
    iInf_add_le_add_iInf (ne_bot_of_nonneg (hnn s)) hbot
  rw [add_comm (minConv f sigma u) (sigma s)]
  refine le_trans (le_iInf ?_) hexch
  rintro ⟨⟨a, b⟩, (hab : a + b = u)⟩
  show minConv f sigma (u + s) ≤ sigma s + (f a + sigma b)
  have hterm : minConv f sigma (u + s) ≤ f a + sigma (b + s) :=
    iInf_le _ (⟨(a, b + s), by rw [← hab, add_assoc]⟩ :
      {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = u + s})
  refine le_trans hterm ?_
  calc f a + sigma (b + s)
      ≤ f a + (sigma b + sigma s) := add_le_add le_rfl (hsub b s)
    _ = sigma s + (f a + sigma b) := by
        rw [← add_assoc, add_comm (f a + sigma b) (sigma s)]

/-- A greedy shaper for sub-additive nonnegative `sigma` is a `sigma`-shaper:
its outputs `A ∗ sigma` allow `sigma`. -/
theorem IsGreedyShaper.isShaper {S : Curve → Curve → Prop}
    {sigma : ℝ≥0 → EReal} (hnn : IsNonneg sigma) (hsub : IsSubadditive sigma)
    (hS : IsGreedyShaper sigma S) : IsShaper sigma S := by
  intro A D hp
  rw [show curveE D = minConv (curveE A) sigma from hS A D hp]
  exact isMaximalArrivalCurve_minConv_of_subadditive
    (curveE_nonneg A) hnn hsub

end DeepWiki
