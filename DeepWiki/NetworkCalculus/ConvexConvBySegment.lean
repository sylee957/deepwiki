import DeepWiki.NetworkCalculus.ConvexConvByLine
import DeepWiki.NetworkCalculus.BoundedSegment
import DeepWiki.NetworkCalculus.ConvexConcaveReadback
import DeepWiki.NetworkCalculus.ConvexConcaveThreePart

/-! # Lemma 4.1 with a *bounded-support* affine factor — the genuine three-case `min(g¹,gᶜ,g²)`
[BOU 16a] = Bouillard–Faou–Zavidovique, *Fast weak-KAM integrators for separable Hamiltonian
systems*, Math. Comp. 85 (2016) 85–117, **Lemma 4.1** (p.14).

`ConvexConvByLine` computes a convex PWL convolved by an *unbounded* line (two regimes). The paper's
Lemma 4.1, however, takes the affine factor `g` on a **bounded** interval `[c,d]` (`g(v) = gc + q·(v−c)`,
`+∞` outside — exactly `segE c d gc q`). The bounded support is precisely what creates the *third*
convex part `g²`: beyond `x = α + d` the cheapest split is forced to use the right endpoint `v = d`,
so the result runs at `f`'s slope again. This file formalizes that genuine three-case form for the
**affine base case** of the induction — `f` a single line `convexSegEval f0 fs []` (`α = 0`, since a
line's only slope `fs ≥ q`) convolved by `segE c d gc q` with `q ≤ fs`:

```
              ⊤                              x < c                 (off the support [c,b+d])
(f ∗ g)(x) =  f0 + gc + q·(x − c)           c ≤ x ≤ d             (gᶜ:  f(0) + g(x), affine)
              f0 + fs·(x − d) + gc + q·(d−c) d ≤ x                 (g²:  f(x−d) + g(d), slope fs)
```

The middle piece `gᶜ` is the affine `g` shifted up by `f0`; the right piece `g²` is `f` shifted by the
segment's right end `d` and bumped by `g(d)`. These are the paper's `gᶜ` and `g²` (with `g¹` trivial
because `α = 0` for a single-line `f`). Everything is on the `ℝ≥0` value level (no `⊤`-collision: the
algebra stays on the WithTop/WithBot reading, the `⊤` only marking off-support). Nothing is sorried. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-! ## The affine value of a bounded segment, as an `ℝ≥0` quantity -/

/-- `coeadd`: the `ℝ≥0 → ℝ → EReal` cast turns dioid `+` into addition (the standard idiom). -/
private theorem coeadd_seg (x y : ℝ≥0) :
    (((x : ℝ) : EReal)) + (((y : ℝ) : EReal)) = (((x + y : ℝ≥0) : ℝ) : EReal) := by
  rw [← EReal.coe_add, ← NNReal.coe_add]

/-- A bounded segment is bounded below by `0` (its value is either a nonneg coe or `⊤`). -/
theorem segE_nonneg (c d gc q : ℝ≥0) (v : ℝ≥0) : (0 : EReal) ≤ segE c d gc q v := by
  by_cases hmem : c ≤ v ∧ v ≤ d
  · rw [segE_apply_mem c d gc q v hmem]; positivity
  · rw [segE_apply_not_mem c d gc q v hmem]; exact le_top

/-- The convolution of a line `f = convexSegEval f0 fs []` by a bounded affine segment is `≥ 0`
(every split `f u + g v` has both summands `≥ 0`), in particular never `⊥`. -/
theorem zero_le_minConv_line_segE (f0 fs c d gc q : ℝ≥0) (x : ℝ≥0) :
    (0 : EReal) ≤ minConv (fun u => (((convexSegEval f0 fs [] u : ℝ≥0) : ℝ) : EReal))
      (segE c d gc q) x := by
  refine le_minConv fun u v _ => ?_
  have h1 : (0 : EReal) ≤ (((convexSegEval f0 fs [] u : ℝ≥0) : ℝ) : EReal) := by positivity
  exact add_nonneg h1 (segE_nonneg c d gc q v)

/-! ## Case `x < c` — off the support `[c, b+d]`, value `⊤` (the `g¹` part is empty for a line) -/

/-- **Lemma 4.1, off-support.** Below the left end `c` of the segment's support, no split `u + v = x`
can place `v` in `[c,d]` (as `v ≤ x < c`), so every term is `⊤`: `(f ∗ segE c d gc q)(x) = ⊤` for
`x < c`. (For a single-line `f`, `a = 0`, so the convolution's support starts at `a + c = c`.) -/
theorem minConv_line_segE_top_below (f0 fs c d gc q : ℝ≥0) {x : ℝ≥0} (hx : x < c) :
    minConv (fun u => (((convexSegEval f0 fs [] u : ℝ≥0) : ℝ) : EReal)) (segE c d gc q) x = ⊤ := by
  rw [eq_top_iff]
  refine le_minConv fun u v huv => ?_
  -- `v ≤ x < c`, so `v < c` and the segment is `⊤`
  have hvc : v < c := lt_of_le_of_lt (huv ▸ le_add_self) hx
  rw [segE_of_lt_left c d gc q v hvc, EReal.add_top_of_ne_bot (by exact EReal.coe_ne_bot _)]

/-! ## Case `c ≤ x ≤ d` — the concave/affine middle part `gᶜ = f(0) + g(x)`

On `[c,d]` the cheapest split uses the largest feasible `v = x` (the term `f0 + fs·(x−v) + gc + q·(v−c)`
decreases in `v` because `q ≤ fs`), so the convolution is `f0 + g(x)` — `g` shifted up by `f(0) = f0`.
This is the paper's affine middle part `gᶜ` (slope `q`). -/

/-- **Lemma 4.1, middle part `gᶜ`.** For `c ≤ x ≤ d` the convolution of a line `f` by the bounded
affine segment is `f(0) + g(x) = f0 + gc + q·(x − c)` — the affine `g` lifted by `f0`, the paper's
concave/affine central piece (slope `q ≤ fs`). -/
theorem minConv_line_segE_middle (f0 fs c d gc q : ℝ≥0) (hqf : q ≤ fs)
    {x : ℝ≥0} (hc : c ≤ x) (hd : x ≤ d) :
    minConv (fun u => (((convexSegEval f0 fs [] u : ℝ≥0) : ℝ) : EReal)) (segE c d gc q) x
      = (((f0 + gc + q * (x - c) : ℝ≥0) : ℝ) : EReal) := by
  apply le_antisymm
  · -- (≤): the split `(0, x)` — place all the time on the segment, `f(0) + g(x)`
    refine le_trans (minConv_le_add _ _ (u := 0) (s := x) (zero_add x)) (le_of_eq ?_)
    rw [convexSegEval_zero, segE_mem c d gc q x hc hd, coeadd_seg]
    norm_num [add_assoc]
  · -- (≥): every split `u + v = x` costs at least `f0 + g(x)`
    refine le_minConv fun u v huv => ?_
    by_cases hmem : c ≤ v ∧ v ≤ d
    · rw [convexSegEval_nil, segE_apply_mem c d gc q v hmem, coeadd_seg, EReal.coe_le_coe_iff,
        NNReal.coe_le_coe]
      -- `v ≤ x` from `u + v = x`
      have hvx : v ≤ x := huv ▸ le_add_self
      -- `q·(x−c) ≤ fs·u + q·(v−c)` since `u = x − v` and `q·(x−v) ≤ fs·(x−v)`
      have hu : u = x - v := by rw [← huv, add_tsub_cancel_right]
      have hkey : q * (x - c) ≤ fs * u + q * (v - c) := by
        rw [hu]
        have hq : q * (x - v) ≤ fs * (x - v) := by gcongr
        -- `q·(x−c) = q·(x−v) + q·(v−c)` (telescoping with `c ≤ v ≤ x`)
        have htel : q * (x - c) = q * (x - v) + q * (v - c) := by
          rw [← mul_add, tsub_add_tsub_cancel hvx hmem.1]
        rw [htel]
        exact add_le_add hq le_rfl
      calc f0 + gc + q * (x - c) ≤ f0 + gc + (fs * u + q * (v - c)) := by gcongr
        _ = f0 + fs * u + (gc + q * (v - c)) := by ring
    · -- off the segment support: `g v = ⊤`, RHS is `⊤`
      rw [segE_apply_not_mem c d gc q v hmem,
        EReal.add_top_of_ne_bot (by exact EReal.coe_ne_bot _)]
      exact le_top

/-! ## Case `x ≥ d` — the right convex part `g² = f(x − d) + g(d)`

Beyond the segment's right end the cheapest split is forced to the right endpoint `v = d` (the term
decreases in `v` but `v ≤ d`), so the convolution runs at `f`'s slope `fs` again: `g²(x) = f(x−d) + g(d)`.
This is the third part, present precisely *because* `g` has bounded support `[c,d]` — for a single-line
`f`, `g²` is itself a line of slope `fs`. -/

/-- **Lemma 4.1, right part `g²`.** For `x ≥ d` (with `c ≤ d`) the convolution of a line `f` by the
bounded affine segment is `f(x − d) + g(d) = f0 + fs·(x − d) + gc + q·(d − c)` — `f` shifted by the
segment's right end `d` and lifted by `g(d)`, the paper's right convex piece (slope `fs ≥ q`). -/
theorem minConv_line_segE_right (f0 fs c d gc q : ℝ≥0) (hqf : q ≤ fs) (hcd : c ≤ d)
    {x : ℝ≥0} (hx : d ≤ x) :
    minConv (fun u => (((convexSegEval f0 fs [] u : ℝ≥0) : ℝ) : EReal)) (segE c d gc q) x
      = (((f0 + fs * (x - d) + gc + q * (d - c) : ℝ≥0) : ℝ) : EReal) := by
  apply le_antisymm
  · -- (≤): the split `(x − d, d)` — use the right endpoint of the segment, `f(x−d) + g(d)`
    refine le_trans (minConv_le_add _ _ (u := x - d) (s := d) (tsub_add_cancel_of_le hx))
      (le_of_eq ?_)
    rw [convexSegEval_nil, segE_mem c d gc q d hcd le_rfl, coeadd_seg]
    norm_num [add_assoc]
  · -- (≥): every split `u + v = x` costs at least `f(x−d) + g(d)`
    refine le_minConv fun u v huv => ?_
    by_cases hmem : c ≤ v ∧ v ≤ d
    · rw [convexSegEval_nil, segE_apply_mem c d gc q v hmem, coeadd_seg, EReal.coe_le_coe_iff,
        NNReal.coe_le_coe]
      have hvx : v ≤ x := huv ▸ le_add_self
      have hu : u = x - v := by rw [← huv, add_tsub_cancel_right]
      -- telescope: `fs·(x−v) = fs·(x−d) + fs·(d−v)` and `q·(d−c) = q·(d−v) + q·(v−c)`
      have htel1 : fs * (x - v) = fs * (x - d) + fs * (d - v) := by
        rw [← mul_add, tsub_add_tsub_cancel hx hmem.2]
      have htel2 : q * (d - c) = q * (d - v) + q * (v - c) := by
        rw [← mul_add, tsub_add_tsub_cancel hmem.2 hmem.1]
      have hq : q * (d - v) ≤ fs * (d - v) := by gcongr
      rw [hu]
      calc f0 + fs * (x - d) + gc + q * (d - c)
          = f0 + fs * (x - d) + (q * (d - v)) + (gc + q * (v - c)) := by rw [htel2]; ring
        _ ≤ f0 + fs * (x - d) + (fs * (d - v)) + (gc + q * (v - c)) := by gcongr
        _ = f0 + fs * (x - v) + (gc + q * (v - c)) := by rw [htel1]; ring
    · rw [segE_apply_not_mem c d gc q v hmem,
        EReal.add_top_of_ne_bot (by exact EReal.coe_ne_bot _)]
      exact le_top

/-! ## The unified three-case form and the breakpoint agreements -/

/-- **Lemma 4.1 (p.14), the affine base case, unified.** The `(min,plus)` convolution of a line
`f = convexSegEval f0 fs []` by the bounded affine segment `g = segE c d gc q` (`q ≤ fs`, `c ≤ d`) is
the paper's three-case curve `min(g¹, gᶜ, g²)` with `g¹` empty (`α = 0` for a line):
`⊤` for `x < c`; the affine middle `gᶜ = f0 + g(x)` for `c ≤ x ≤ d`; the convex right
`g² = f(x − d) + g(d)` for `x ≥ d`. -/
theorem minConv_line_segE (f0 fs c d gc q : ℝ≥0) (hqf : q ≤ fs) (hcd : c ≤ d) (x : ℝ≥0) :
    minConv (fun u => (((convexSegEval f0 fs [] u : ℝ≥0) : ℝ) : EReal)) (segE c d gc q) x
      = if x < c then ⊤
        else if x ≤ d then (((f0 + gc + q * (x - c) : ℝ≥0) : ℝ) : EReal)
        else (((f0 + fs * (x - d) + gc + q * (d - c) : ℝ≥0) : ℝ) : EReal) := by
  by_cases h1 : x < c
  · rw [if_pos h1, minConv_line_segE_top_below f0 fs c d gc q h1]
  · rw [if_neg h1]
    rw [not_lt] at h1
    by_cases h2 : x ≤ d
    · rw [if_pos h2, minConv_line_segE_middle f0 fs c d gc q hqf h1 h2]
    · rw [if_neg h2]
      rw [not_le] at h2
      exact minConv_line_segE_right f0 fs c d gc q hqf hcd h2.le

/-- At the left end `x = c` the convolution starts at `f(0) + g(c) = f0 + gc` (the `q·(c − c) = 0`
term drops); the off-support and middle regimes meet here. -/
theorem minConv_line_segE_at_left (f0 fs c d gc q : ℝ≥0) (hqf : q ≤ fs) (hcd : c ≤ d) :
    minConv (fun u => (((convexSegEval f0 fs [] u : ℝ≥0) : ℝ) : EReal)) (segE c d gc q) c
      = (((f0 + gc : ℝ≥0) : ℝ) : EReal) := by
  rw [minConv_line_segE_middle f0 fs c d gc q hqf le_rfl hcd, tsub_self, mul_zero, add_zero]

/-- At the right end `x = d` the middle and right regimes agree: `f0 + g(d) = f0 + gc + q·(d − c)`
equals `f(d − d) + g(d)` (the `fs·(d − d) = 0` term drops). The single slope switch `q → fs` of the
convex PWL `f ∗ g` happens exactly at `x = d`. -/
theorem minConv_line_segE_middle_eq_right_at_d (f0 fs c d gc q : ℝ≥0) :
    (((f0 + gc + q * (d - c) : ℝ≥0) : ℝ) : EReal)
      = (((f0 + fs * (d - d) + gc + q * (d - c) : ℝ≥0) : ℝ) : EReal) := by
  rw [tsub_self, mul_zero, add_zero]

/-! ## Restatements (verification against the intended wording) -/

-- Lemma 4.1, the affine base case: the three-case `min(g¹, gᶜ, g²)` with `g¹` empty (`α = 0`).
example (f0 fs c d gc q x : ℝ≥0) (hqf : q ≤ fs) (hcd : c ≤ d) :
    minConv (fun u => (((convexSegEval f0 fs [] u : ℝ≥0) : ℝ) : EReal)) (segE c d gc q) x
      = if x < c then ⊤
        else if x ≤ d then (((f0 + gc + q * (x - c) : ℝ≥0) : ℝ) : EReal)
        else (((f0 + fs * (x - d) + gc + q * (d - c) : ℝ≥0) : ℝ) : EReal) :=
  minConv_line_segE f0 fs c d gc q hqf hcd x

-- The middle part `gᶜ` is the affine `g` lifted by `f(0) = f0` (slope `q`).
example (f0 fs c d gc q : ℝ≥0) (hqf : q ≤ fs) {x : ℝ≥0} (hc : c ≤ x) (hd : x ≤ d) :
    minConv (fun u => (((convexSegEval f0 fs [] u : ℝ≥0) : ℝ) : EReal)) (segE c d gc q) x
      = (((f0 : ℝ≥0) : ℝ) : EReal) + segE c d gc q x := by
  rw [minConv_line_segE_middle f0 fs c d gc q hqf hc hd, segE_mem c d gc q x hc hd, coeadd_seg,
    add_assoc]

/-! ## Lemma 4.4 / 4.5 (pp.16–17) — the slope-surgery ordering, lifted to the convolutions

The paper's Lemmas 4.4/4.5 order two *consecutive* convolutions `f ∗ gⱼ` and `f ∗ gⱼ₋₁` (the segments
of the concave function): they cross exactly once, with the flatter-segment convolution below before
the crossing and above after. In the token-bucket reading a concave segment of slope `gⱼ'` is
`γ_{rⱼ,bⱼ}`, and as `j` grows the concave function flattens so the rate decreases (`rⱼ < rⱼ₋₁`) and
the burst increases (`bⱼ ≥ bⱼ₋₁`). The bucket-level single crossing is already settled
(`tb_le_of_le_cross` / `tb_ge_of_cross_le`, crossing time `tbCross`); here it is lifted through the
convolution by a common convex `f`, giving the genuine Lemma 4.4 ordering of `f ∗ γ`.

We give the affine base (`f` a single line): the convolution value is the explicit meet
`(f0 + b + r·t) ⊓ (f0 + fs·t)` (`minConv_tbEReal_line`), so the bucket ordering transports through
`inf_le_inf` with the common cap `f0 + fs·t`. -/

/-- **Lemma 4.4, first ordering (`x ≤ crossing`).** For `f` a single line of slope `fs`, with a flatter
higher-burst bucket `(r,b)` and a steeper lower-burst bucket `(r',b')` (`r' < r`, `b ≤ b'`, both
`≤ fs`): up to the crossing time `tbCross r b r' b'` the flatter-bucket convolution dominates,
`f ∗ γ_{r,b} t ≤ f ∗ γ_{r',b'} t`. (The bucket lines obey `γ_{r,b} ≤ γ_{r',b'}` there
`tb_le_of_le_cross`, and the meet with the common `f` cap preserves it.) -/
theorem minConv_tbEReal_line_le_of_le_cross (f0 fs r b r' b' : ℝ≥0)
    (hrf : r ≤ fs) (hr'f : r' ≤ fs) (hr : r' < r) (hb : b ≤ b')
    {t : ℝ≥0} (ht : t ≤ tbCross r b r' b') :
    minConv (fun v => (((convexSegEval f0 fs [] v : ℝ≥0) : ℝ) : EReal)) (tbEReal r b) t
      ≤ minConv (fun v => (((convexSegEval f0 fs [] v : ℝ≥0) : ℝ) : EReal)) (tbEReal r' b') t := by
  rw [minConv_tbEReal_line f0 fs r b hrf, minConv_tbEReal_line f0 fs r' b' hr'f]
  -- the bucket-line values share the common cap `f0 + fs·t`, so it suffices to compare the lines
  refine inf_le_inf ?_ le_rfl
  rw [EReal.coe_le_coe_iff, NNReal.coe_le_coe, ← NNReal.coe_le_coe]
  -- `f0 + b + r·t ≤ f0 + b' + r'·t` from `t ≤ (b'−b)/(r−r')`, a direct real inequality
  have hrr : (0 : ℝ) < (r : ℝ) - r' := by
    have : (r' : ℝ) < r := by exact_mod_cast hr
    linarith
  have htr : (t : ℝ) ≤ ((b' : ℝ) - b) / ((r : ℝ) - r') := by
    have := NNReal.coe_le_coe.mpr ht
    rwa [tbCross, NNReal.coe_div, NNReal.coe_sub hb, NNReal.coe_sub hr.le] at this
  rw [le_div_iff₀ hrr, mul_sub] at htr
  push_cast
  nlinarith [htr, mul_comm (t : ℝ) r, mul_comm (t : ℝ) r']

/-- **Lemma 4.4, second ordering (`x ≥ crossing`).** Symmetric to the first: for `f` a single line,
beyond the crossing time the *steeper* lower-burst bucket `(r',b')` dominates,
`f ∗ γ_{r',b'} t ≤ f ∗ γ_{r,b} t` for `t ≥ tbCross r b r' b'`. With the first ordering this is the
genuine Lemma 4.4 — the two convolutions cross exactly once, swapping which is the minimum. -/
theorem minConv_tbEReal_line_ge_of_cross_le (f0 fs r b r' b' : ℝ≥0)
    (hrf : r ≤ fs) (hr'f : r' ≤ fs) (hr : r' < r) (hb : b ≤ b')
    {t : ℝ≥0} (ht : tbCross r b r' b' ≤ t) :
    minConv (fun v => (((convexSegEval f0 fs [] v : ℝ≥0) : ℝ) : EReal)) (tbEReal r' b') t
      ≤ minConv (fun v => (((convexSegEval f0 fs [] v : ℝ≥0) : ℝ) : EReal)) (tbEReal r b) t := by
  rw [minConv_tbEReal_line f0 fs r b hrf, minConv_tbEReal_line f0 fs r' b' hr'f]
  refine inf_le_inf ?_ le_rfl
  rw [EReal.coe_le_coe_iff, NNReal.coe_le_coe, ← NNReal.coe_le_coe]
  -- `f0 + b' + r'·t ≤ f0 + b + r·t` from `t ≥ (b'−b)/(r−r')`
  have hrr : (0 : ℝ) < (r : ℝ) - r' := by
    have : (r' : ℝ) < r := by exact_mod_cast hr
    linarith
  have htr : ((b' : ℝ) - b) / ((r : ℝ) - r') ≤ (t : ℝ) := by
    have := NNReal.coe_le_coe.mpr ht
    rwa [tbCross, NNReal.coe_div, NNReal.coe_sub hb, NNReal.coe_sub hr.le] at this
  rw [div_le_iff₀ hrr, mul_sub] at htr
  push_cast
  nlinarith [htr, mul_comm (t : ℝ) r, mul_comm (t : ℝ) r']

/-! ## Theorem 4.6 — the affine base realizes the real-level three-part shape

The genuine three-part conclusion `IsThreePartOnIcc` (Mathlib `ConvexOn`/`ConcaveOn` on `Icc`, the
paper's `[a,b] → ℝ` setting). For the affine base, the convolution value as a *real* function on
`[c, ∞)` is the two affine pieces `gᶜ` (slope `q`) on `[c,d]` and `g²` (slope `fs`) on `[d, ∞)`,
agreeing at `d`. This realizes the paper's three-part decomposition with `g¹` trivial (`α = 0`): the
concave middle is the affine `gᶜ`, the convex right is the affine `g²`. -/

/-- The real-valued convolution result of a line `f` by the bounded segment `g`, on `[c, ∞)`:
`f0 + gc + q·(x − c)` while `x ≤ d` (the affine `gᶜ`), then `f0 + g(d) + fs·(x − d)` (the affine `g²`,
steeper slope `fs`). The two pieces agree at `x = d`. -/
noncomputable def convLineSegReal (f0 fs c d gc q : ℝ) : ℝ → ℝ := fun x =>
  if x ≤ d then f0 + gc + q * (x - c)
  else f0 + gc + q * (d - c) + fs * (x - d)

/-- An affine function `x ↦ a₀ + s·(x − c)` is convex on any convex set: the chord holds with
*equality* (affine), so `≤` is immediate. -/
theorem convexOn_affineReal (a₀ s c : ℝ) {S : Set ℝ} (hS : Convex ℝ S) :
    ConvexOn ℝ S (fun x => a₀ + s * (x - c)) := by
  refine ⟨hS, fun x _ y _ p q hp hq hpq => ?_⟩
  simp only [smul_eq_mul]
  have hid : p * (a₀ + s * (x - c)) + q * (a₀ + s * (y - c))
      = a₀ + s * ((p * x + q * y) - c) := by
    linear_combination a₀ * hpq - (s * c) * hpq
  rw [hid]

/-- An affine function `x ↦ a₀ + s·(x − c)` is concave on any convex set: the chord holds with
*equality*, so `≥` is immediate. -/
theorem concaveOn_affineReal (a₀ s c : ℝ) {S : Set ℝ} (hS : Convex ℝ S) :
    ConcaveOn ℝ S (fun x => a₀ + s * (x - c)) := by
  refine ⟨hS, fun x _ y _ p q hp hq hpq => ?_⟩
  simp only [smul_eq_mul]
  have hid : p * (a₀ + s * (x - c)) + q * (a₀ + s * (y - c))
      = a₀ + s * ((p * x + q * y) - c) := by
    linear_combination a₀ * hpq - (s * c) * hpq
  rw [hid]

/-- On `[c,d]` the real result is the affine `gᶜ` of slope `q`, hence concave (and convex). -/
theorem concaveOn_convLineSegReal_middle (f0 fs c d gc q : ℝ) :
    ConcaveOn ℝ (Set.Icc c d) (convLineSegReal f0 fs c d gc q) := by
  refine (concaveOn_affineReal (f0 + gc) q c (convex_Icc c d)).congr (fun x hx => ?_)
  simp only [Set.mem_Icc] at hx
  rw [convLineSegReal, if_pos hx.2]

/-- On `[d,D]` the real result is the affine `g²` of slope `fs`, hence convex (and concave). -/
theorem convexOn_convLineSegReal_right (f0 fs c d gc q D : ℝ) :
    ConvexOn ℝ (Set.Icc d D) (convLineSegReal f0 fs c d gc q) := by
  refine (convexOn_affineReal (f0 + gc + q * (d - c)) fs d (convex_Icc d D)).congr (fun x hx => ?_)
  simp only [Set.mem_Icc] at hx
  rcases eq_or_lt_of_le hx.1 with hxd | hxd
  · rw [convLineSegReal, ← hxd, if_pos le_rfl]; ring
  · rw [convLineSegReal, if_neg (not_le.mpr hxd)]

/-- The first (convex) part is trivial: on the degenerate `[c,c]` the result is convex (any function
on a singleton is convex). -/
theorem convexOn_convLineSegReal_left (f0 fs c d gc q : ℝ) (hcd : c ≤ d) :
    ConvexOn ℝ (Set.Icc c c) (convLineSegReal f0 fs c d gc q) := by
  refine (convexOn_affineReal (f0 + gc) q c (convex_Icc c c)).congr (fun x hx => ?_)
  simp only [Set.mem_Icc] at hx
  have hxc : x = c := le_antisymm hx.2 hx.1
  rw [convLineSegReal, if_pos (hxc ▸ hcd)]

/-- **Theorem 4.6 (p.18), the affine base instance.** The convolution result `convLineSegReal` is a
genuine three-part `convex–concave–convex` function on `[c, c, d, D]` (any `c ≤ d ≤ D`): the first
convex part is trivial (`α = 0`, so `g¹` is the degenerate `[c,c]`), the concave middle is the affine
`gᶜ` (slope `q`) on `[c,d]`, the convex right is the affine `g²` (slope `fs`) on `[d,D]`. This is the
paper's three-part conclusion `IsThreePartOnIcc` realized by the affine base case of Lemma 4.1. -/
theorem isThreePartOnIcc_convLineSegReal (f0 fs c d gc q D : ℝ) (hcd : c ≤ d) :
    IsThreePartOnIcc (convLineSegReal f0 fs c d gc q) c c d D :=
  ⟨convexOn_convLineSegReal_left f0 fs c d gc q hcd,
    concaveOn_convLineSegReal_middle f0 fs c d gc q,
    convexOn_convLineSegReal_right f0 fs c d gc q D⟩

/-- The real result `convLineSegReal` agrees with the `(min,plus)` convolution value on `[c, ∞)`: at
any `x ≥ c`, its `ℝ≥0` coe is `minConv (line) (segE) x`. (Bridges the real three-part shape back to
the dioid convolution — the `ℝ≥0` arguments are read through the nonneg reals.) -/
theorem convLineSegReal_eq_minConv (f0 fs c d gc q : ℝ≥0) (hqf : q ≤ fs) (hcd : c ≤ d)
    {x : ℝ≥0} (hx : c ≤ x) :
    ((convLineSegReal f0 fs c d gc q x : ℝ) : EReal)
      = minConv (fun u => (((convexSegEval f0 fs [] u : ℝ≥0) : ℝ) : EReal)) (segE c d gc q) x := by
  by_cases hd : x ≤ d
  · rw [convLineSegReal, if_pos (by exact_mod_cast hd),
      minConv_line_segE_middle f0 fs c d gc q hqf hx hd, EReal.coe_eq_coe_iff]
    push_cast [NNReal.coe_sub hx]
    ring
  · rw [not_le] at hd
    rw [convLineSegReal, if_neg (by exact_mod_cast not_le.mpr hd),
      minConv_line_segE_right f0 fs c d gc q hqf hcd hd.le, EReal.coe_eq_coe_iff]
    push_cast [NNReal.coe_sub hd.le, NNReal.coe_sub hcd]
    ring

/-! ## Faithfulness checks (Lemma 4.4 ordering) -/

/-- Faithfulness: at the crossing time the two convolutions are equal (the orderings meet) —
`f ∗ γ_{r,b} = f ∗ γ_{r',b'}` at `t = tbCross r b r' b'`. -/
example (f0 fs r b r' b' : ℝ≥0) (hrf : r ≤ fs) (hr'f : r' ≤ fs) (hr : r' < r) (hb : b ≤ b') :
    minConv (fun v => (((convexSegEval f0 fs [] v : ℝ≥0) : ℝ) : EReal)) (tbEReal r b)
        (tbCross r b r' b')
      = minConv (fun v => (((convexSegEval f0 fs [] v : ℝ≥0) : ℝ) : EReal)) (tbEReal r' b')
        (tbCross r b r' b') :=
  le_antisymm
    (minConv_tbEReal_line_le_of_le_cross f0 fs r b r' b' hrf hr'f hr hb le_rfl)
    (minConv_tbEReal_line_ge_of_cross_le f0 fs r b r' b' hrf hr'f hr hb le_rfl)

/-! ## Theorem 4.6 induction step (the two-segment reassembly, line base)

The induction engine: `f ∗ (g_{j-1} ⊓ g_j) = (f ∗ g_{j-1}) ⊓ (f ∗ g_j)` (Lemma 4.3 distribution),
and the meet of two consecutive convolutions is a *single switch* (Lemma 4.4): the flatter one wins
below the crossing, the steeper above. For two concave token-bucket segments convolved against a line
`f`, this gives the reassembled value explicitly. This is exactly how the paper's induction adds one
concave segment at a time without recomputing the whole convolution. -/

/-- **Theorem 4.6 induction step (line base), the meet reassembles to a single switch.** For two
consecutive concave segments `(r,b)` (flatter, higher burst) and `(r',b')` (steeper, lower burst,
`r' < r`, `b ≤ b'`, both `≤ fs`), the meet of the two convolutions of a line `f` is the *flatter*
one below the crossing `tbCross r b r' b'` and the *steeper* one above — `f ∗ (γ_{r,b} ⊓ γ_{r',b'})`
is a single-switch curve, never both. (This is the genuine consequence of Lemma 4.4: only the two
extremal segments and the crossing matter.) -/
theorem minConv_line_inf_tb_eq_switch (f0 fs r b r' b' : ℝ≥0)
    (hrf : r ≤ fs) (hr'f : r' ≤ fs) (hr : r' < r) (hb : b ≤ b') (t : ℝ≥0) :
    minConv (fun v => (((convexSegEval f0 fs [] v : ℝ≥0) : ℝ) : EReal)) (tbEReal r b ⊓ tbEReal r' b') t
      = if t ≤ tbCross r b r' b'
        then minConv (fun v => (((convexSegEval f0 fs [] v : ℝ≥0) : ℝ) : EReal)) (tbEReal r b) t
        else minConv (fun v => (((convexSegEval f0 fs [] v : ℝ≥0) : ℝ) : EReal)) (tbEReal r' b') t := by
  rw [minConv_distrib_inf, Pi.inf_apply]
  by_cases ht : t ≤ tbCross r b r' b'
  · rw [if_pos ht]
    exact inf_of_le_left (minConv_tbEReal_line_le_of_le_cross f0 fs r b r' b' hrf hr'f hr hb ht)
  · rw [if_neg ht]
    rw [not_le] at ht
    exact inf_of_le_right
      (minConv_tbEReal_line_ge_of_cross_le f0 fs r b r' b' hrf hr'f hr hb ht.le)

/-! ## Faithfulness checks (Theorem 4.6 affine base) -/

-- The affine base convolution result is a genuine three-part curve on `[c,c,d,D]`.
example (f0 fs c d gc q D : ℝ) (hcd : c ≤ d) :
    IsThreePartOnIcc (convLineSegReal f0 fs c d gc q) c c d D :=
  isThreePartOnIcc_convLineSegReal f0 fs c d gc q D hcd

-- The real three-part shape is the actual `(min,plus)` convolution value on `[c, ∞)`.
example (f0 fs c d gc q : ℝ≥0) (hqf : q ≤ fs) (hcd : c ≤ d) {x : ℝ≥0} (hx : c ≤ x) :
    ((convLineSegReal f0 fs c d gc q x : ℝ) : EReal)
      = minConv (fun u => (((convexSegEval f0 fs [] u : ℝ≥0) : ℝ) : EReal)) (segE c d gc q) x :=
  convLineSegReal_eq_minConv f0 fs c d gc q hqf hcd hx

-- Theorem 4.6 induction step: the meet of two consecutive convolutions is a single switch
-- (Lemma 4.3 distribution + Lemma 4.4 crossing), exactly the paper's add-one-segment step.
example (f0 fs r b r' b' : ℝ≥0) (hrf : r ≤ fs) (hr'f : r' ≤ fs) (hr : r' < r) (hb : b ≤ b')
    {t : ℝ≥0} (ht : t ≤ tbCross r b r' b') :
    minConv (fun v => (((convexSegEval f0 fs [] v : ℝ≥0) : ℝ) : EReal))
        (tbEReal r b ⊓ tbEReal r' b') t
      = minConv (fun v => (((convexSegEval f0 fs [] v : ℝ≥0) : ℝ) : EReal)) (tbEReal r b) t := by
  rw [minConv_line_inf_tb_eq_switch f0 fs r b r' b' hrf hr'f hr hb, if_pos ht]

end DeepWiki