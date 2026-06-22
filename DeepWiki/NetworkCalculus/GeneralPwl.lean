import DeepWiki.NetworkCalculus.ConvexSegmentMerge
import DeepWiki.NetworkCalculus.ConvexConvByLine
import DeepWiki.NetworkCalculus.ConvexSegEvalSplit

/-! # General piecewise-linear curves (`Pwl`)
A first-class wrapper around the general arbitrary-slope PWL evaluator `convexSegEval`: a
`Pwl` bundles a `base` value, a list of `(slope, length)` `segs`, and an asymptotic `tail`
slope, evaluated piecewise by `convexSegEval`. Over `ℝ≥0` every slope is `≥ 0`, so the
evaluator is **always** monotone with no sorting hypothesis — the "convex" in
`convexSegEval` is a usage convention, not a requirement, and `Pwl` is named generally.
This is the foundational general-PWL layer; the pointwise-min lower-envelope merge is built
on top in a sibling. -/

namespace DeepWiki

open scoped NNReal

/-- A general piecewise-linear curve over `ℝ≥0`: a base value, a list of `(slope, length)`
segments, and an asymptotic `tail` slope reached past the last segment. Arbitrary slopes
allowed (no sorting); evaluated by `convexSegEval`. -/
structure Pwl where
  /-- Value at `0` (the base). -/
  base : ℝ≥0
  /-- The finite `(slope, length)` segments, in order. -/
  segs : List (ℝ≥0 × ℝ≥0)
  /-- Asymptotic slope past the last segment. -/
  tail : ℝ≥0

/-- Evaluate a `Pwl` as an `ℝ≥0`-valued function via `convexSegEval`. -/
noncomputable def Pwl.eval (p : Pwl) : ℝ≥0 → ℝ≥0 := convexSegEval p.base p.tail p.segs

/-- The `EReal` reading of `p.eval`, used by the convolution layer. -/
noncomputable def Pwl.evalE (p : Pwl) : ℝ≥0 → EReal := fun t => (((p.eval t : ℝ≥0) : ℝ) : EReal)

@[simp] theorem Pwl.eval_def (p : Pwl) (t : ℝ≥0) :
    p.eval t = convexSegEval p.base p.tail p.segs t := rfl

@[simp] theorem Pwl.evalE_def (p : Pwl) (t : ℝ≥0) :
    p.evalE t = (((p.eval t : ℝ≥0) : ℝ) : EReal) := rfl

/-- `p.eval 0 = p.base`: a `Pwl` starts at its base value. -/
@[simp] theorem Pwl.eval_zero (p : Pwl) : p.eval 0 = p.base := convexSegEval_zero _ _ _

/-- `Monotone p.eval` for ANY segments — the generality point: over `ℝ≥0` all slopes are
`≥ 0`, so no sorting/convexity hypothesis is needed. -/
theorem Pwl.monotone (p : Pwl) : Monotone p.eval := monotone_convexSegEval _ _ _

/-- `evalE` is monotone (in the `EReal` reading). -/
theorem Pwl.monotone_evalE (p : Pwl) : Monotone p.evalE := by
  intro a b hab
  simp only [Pwl.evalE_def]
  exact_mod_cast p.monotone hab

/-- With no segments, a `Pwl` is the affine line `base + tail·t`. -/
theorem Pwl.eval_nil (base tail t : ℝ≥0) :
    Pwl.eval ⟨base, [], tail⟩ t = base + tail * t := convexSegEval_nil _ _ _

/-- Cons reading of `Pwl.eval`, mirroring `convexSegEval_cons`: on the leading segment of
slope `s`, length `ℓ`, the value is `base + s·t`; past it the curve restarts from the corner
`base + s·ℓ` over the remaining segments. -/
theorem Pwl.eval_cons (base tail s ℓ : ℝ≥0) (rest : List (ℝ≥0 × ℝ≥0)) (t : ℝ≥0) :
    Pwl.eval ⟨base, (s, ℓ) :: rest, tail⟩ t
      = if t ≤ ℓ then base + s * t
        else Pwl.eval ⟨base + s * ℓ, rest, tail⟩ (t - ℓ) := convexSegEval_cons _ _ _ _ _ _

/-- Peel the leading segment of a `Pwl`: past its length `ℓ`, the curve restarts from the
corner `base + s·ℓ`, mirroring `convexSegEval_cons_peel`. -/
theorem Pwl.eval_cons_peel (base tail s ℓ r : ℝ≥0) (rest : List (ℝ≥0 × ℝ≥0)) :
    Pwl.eval ⟨base, (s, ℓ) :: rest, tail⟩ (ℓ + r)
      = Pwl.eval ⟨base + s * ℓ, rest, tail⟩ r := convexSegEval_cons_peel _ _ _ _ _ _

/-- The affine `Pwl` `t ↦ a + r·t`: base `a`, no segments, asymptote `r`. -/
def Pwl.affine (a r : ℝ≥0) : Pwl := ⟨a, [], r⟩

/-- `(Pwl.affine a r).eval t = a + r·t`. -/
@[simp] theorem Pwl.affine_eval (a r t : ℝ≥0) : (Pwl.affine a r).eval t = a + r * t :=
  convexSegEval_nil _ _ _

/-- A single-segment `Pwl` evaluates as the leading line `base + s·t` below the breakpoint
`ℓ`, and continues from the corner `base + s·ℓ` at slope `tail` above it. -/
theorem Pwl.eval_singleton (base tail s ℓ t : ℝ≥0) :
    Pwl.eval ⟨base, [(s, ℓ)], tail⟩ t
      = if t ≤ ℓ then base + s * t
        else base + s * ℓ + tail * (t - ℓ) := by
  rw [Pwl.eval_cons]
  split
  · rfl
  · rw [Pwl.eval_def, convexSegEval_nil]

/-- Lift a `Pwl` up by a constant `c` (add `c` to the base). -/
def Pwl.shiftUp (p : Pwl) (c : ℝ≥0) : Pwl := ⟨p.base + c, p.segs, p.tail⟩

/-- `(p.shiftUp c).eval t = p.eval t + c`: shifting the base by `c` shifts the whole curve
by `c`, via `convexSegEval_base_shift`. -/
@[simp] theorem Pwl.shiftUp_eval (p : Pwl) (c t : ℝ≥0) :
    (p.shiftUp c).eval t = p.eval t + c := by
  simp only [Pwl.shiftUp, Pwl.eval_def]
  rw [add_comm p.base c, convexSegEval_base_shift, add_comm]

/-- `(p.shiftUp c).base = p.base + c`. -/
@[simp] theorem Pwl.shiftUp_base (p : Pwl) (c : ℝ≥0) : (p.shiftUp c).base = p.base + c := rfl

/-- Shifting up by `0` is the identity on the value. -/
theorem Pwl.shiftUp_zero_eval (p : Pwl) (t : ℝ≥0) : (p.shiftUp 0).eval t = p.eval t := by
  rw [Pwl.shiftUp_eval, add_zero]

/-- Append two `Pwl` segment lists, keeping the second curve's `tail` as the asymptote:
`q`'s segments are appended after `p`'s, with base from `p` and asymptote from `q`. -/
def Pwl.concat (p q : Pwl) : Pwl := ⟨p.base, p.segs ++ q.segs, q.tail⟩

/-- `(p.concat q).segs = p.segs ++ q.segs`. -/
@[simp] theorem Pwl.concat_segs (p q : Pwl) : (p.concat q).segs = p.segs ++ q.segs := rfl

/-- `(p.concat q).base = p.base`. -/
@[simp] theorem Pwl.concat_base (p q : Pwl) : (p.concat q).base = p.base := rfl

/-- `(p.concat q).tail = q.tail`. -/
@[simp] theorem Pwl.concat_tail (p q : Pwl) : (p.concat q).tail = q.tail := rfl

/-- **Concat append-peel.** Evaluating `p.concat q` past `p`'s cumulative segment length
`segLenSum p.segs` peels the whole prefix: the value at `segLenSum p.segs + d` is `q`'s
segment list (asymptote `q.tail`) restarted from the corner
`convexSegEval p.base q.tail p.segs (segLenSum p.segs)`. (From `convexSegEval_append_peel`,
which fixes one shared asymptote — here `q.tail` — across both halves.) -/
theorem Pwl.concat_eval_peel (p q : Pwl) (d : ℝ≥0) :
    (p.concat q).eval (segLenSum p.segs + d)
      = convexSegEval (convexSegEval p.base q.tail p.segs (segLenSum p.segs)) q.tail q.segs d := by
  simp only [Pwl.concat, Pwl.eval_def]
  exact convexSegEval_append_peel q.tail p.segs q.segs p.base d

-- Faithfulness checks: each statement says what the API claims.
example (p : Pwl) : p.eval 0 = p.base := p.eval_zero
example (p : Pwl) : Monotone p.eval := p.monotone
example (a r t : ℝ≥0) : (Pwl.affine a r).eval t = a + r * t := Pwl.affine_eval a r t
example (p : Pwl) (c t : ℝ≥0) : (p.shiftUp c).eval t = p.eval t + c := p.shiftUp_eval c t
example (p q : Pwl) (d : ℝ≥0) :
    (p.concat q).eval (segLenSum p.segs + d)
      = convexSegEval (convexSegEval p.base q.tail p.segs (segLenSum p.segs)) q.tail q.segs d :=
  p.concat_eval_peel q d

end DeepWiki
