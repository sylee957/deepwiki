import Leanproofs.MinPlus.FunctionDioid

/-!
# Main subsets of (min,plus) functions (Definition 2.8) and their stability (Lemma 2.3)

The network-calculus functions of interest are *restricted* classes of the (min,plus) functions
`F` (`Leanproofs.MinPlus.FunctionDioid`). Following Definition 2.8 we single out:

* `Fplus` — the **non-negative** functions `F⁺` (values in `ℝ⁺ ∪ {+∞}`);
* `Fzero` — the non-negative functions with `f(0) = 0` (`F₀`);
* `Fnondecr` — the non-negative **non-decreasing** functions (`F↑`);
* `FnondecrZero` — the non-negative non-decreasing functions with `f(0) = 0` (`F↑₀ = F₀ ∩ F↑`).

These are sets of `FunDioid`. The defining predicates are stated on the *underlying numeric values*
(`.toFun _ |>.toDual` in `R̄min = WithTop (WithBot ℝ)`), since "non-negative" and "non-decreasing"
refer to the **natural** order on the values, not the dioid order.

**Lemma 2.3** then says each of these four sets is *stable* under the dioid sum `⊕ = ∧` (pointwise
minimum) and the product `⊗ = ∗` (convolution).
-/

namespace NetworkCalculus

open scoped Computability NNReal

namespace FunDioid

/-! ### The defining predicates (Definition 2.8) -/

/-- A function is **non-negative** if each value is `≥ 0` (numerically, in `R̄min`). -/
def IsNonneg (f : FunDioid) : Prop := ∀ t, (0 : Rbar) ≤ (f.toFun t).toDual

/-- A function **vanishes at `0`**: `f(0) = 0` (numerically). -/
def IsZeroAtZero (f : FunDioid) : Prop := (f.toFun 0).toDual = 0

/-- A function is **non-decreasing** (in the natural order on the values): `x ≤ y → f x ≤ f y`. -/
def IsNondecr (f : FunDioid) : Prop :=
  ∀ x y, x ≤ y → (f.toFun x).toDual ≤ (f.toFun y).toDual

/-! ### The four subsets (Definition 2.8) -/

/-- `F⁺`: the non-negative functions. -/
def Fplus : Set FunDioid := {f | IsNonneg f}

/-- `F₀`: the non-negative functions with `f(0) = 0`. -/
def Fzero : Set FunDioid := {f | IsNonneg f ∧ IsZeroAtZero f}

/-- `F↑`: the non-negative non-decreasing functions. -/
def Fnondecr : Set FunDioid := {f | IsNonneg f ∧ IsNondecr f}

/-- `F↑₀ = F₀ ∩ F↑`: the non-negative non-decreasing functions with `f(0) = 0`. -/
def FnondecrZero : Set FunDioid := Fzero ∩ Fnondecr

/-! ### Stability of the predicates under `∧` and `∗` (towards Lemma 2.3)

The dioid sum `f + g` is the pointwise minimum of the values (`(f + g).toFun t |>.toDual =
min (f.toFun t).toDual (g.toFun t).toDual`), and the product `f * g` is the convolution. We prove
each predicate is preserved by both. -/

/-- A convenient lower bound: convolution values are `≥ 0` once both factors are. -/
private theorem conv_apply_nonneg {f g : FunDioid} (hf : IsNonneg f) (hg : IsNonneg g) (t : ℝ≥0) :
    (0 : Rbar) ≤ ((f.toFun ∗ g.toFun) t).toDual :=
  conv_le f.toFun g.toFun (b := MinPlus.D.ofDual (0 : Rbar)) fun u s _ => by
    show (0 : Rbar) ≤ (f.toFun u).toDual + (g.toFun s).toDual
    calc (0 : Rbar) = 0 + 0 := (add_zero 0).symm
      _ ≤ (f.toFun u).toDual + (g.toFun s).toDual := by gcongr <;> [exact hf u; exact hg s]

theorem IsNonneg.inf {f g : FunDioid} (hf : IsNonneg f) (hg : IsNonneg g) : IsNonneg (f + g) :=
  fun t => le_min (hf t) (hg t)

theorem IsNonneg.conv {f g : FunDioid} (hf : IsNonneg f) (hg : IsNonneg g) : IsNonneg (f * g) :=
  fun t => conv_apply_nonneg hf hg t

theorem IsZeroAtZero.inf {f g : FunDioid} (hf : IsZeroAtZero f) (hg : IsZeroAtZero g) :
    IsZeroAtZero (f + g) := by
  show min (f.toFun 0).toDual (g.toFun 0).toDual = 0
  rw [hf, hg, min_self]

theorem IsZeroAtZero.conv {f g : FunDioid} (hf : IsZeroAtZero f) (hg : IsZeroAtZero g)
    (hfn : IsNonneg f) (hgn : IsNonneg g) : IsZeroAtZero (f * g) := by
  show ((f.toFun ∗ g.toFun) 0).toDual = 0
  apply le_antisymm
  · have h2 : ((f.toFun ∗ g.toFun) 0).toDual ≤ (f.toFun 0).toDual + (g.toFun 0).toDual :=
      conv_ge f.toFun g.toFun (u := 0) (s := 0) (add_zero 0)
    rwa [hf, hg, add_zero] at h2
  · exact conv_apply_nonneg hfn hgn 0

theorem IsNondecr.inf {f g : FunDioid} (hf : IsNondecr f) (hg : IsNondecr g) : IsNondecr (f + g) := by
  intro x y hxy
  show min (f.toFun x).toDual (g.toFun x).toDual ≤ min (f.toFun y).toDual (g.toFun y).toDual
  exact min_le_min (hf x y hxy) (hg x y hxy)

/-- Non-decreasing-ness is preserved by convolution. For a decomposition `u + s = y`, the values
`u' = x - min s x` and `s' = min s x` give a decomposition of `x` with `u' ≤ u`, `s' ≤ s`, so
`f(u') + g(s') ≤ f(u) + g(s)` by monotonicity; taking the infimum over `y`'s decompositions yields
`(f ∗ g)(x) ≤ (f ∗ g)(y)`. -/
theorem IsNondecr.conv {f g : FunDioid} (hf : IsNondecr f) (hg : IsNondecr g) :
    IsNondecr (f * g) := by
  intro x y hxy
  show ((f.toFun ∗ g.toFun) x).toDual ≤ ((f.toFun ∗ g.toFun) y).toDual
  refine conv_le f.toFun g.toFun (t := y) (b := (f.toFun ∗ g.toFun) x) ?_
  intro u s hus
  set s' := min s x
  have hs'x : s' ≤ x := min_le_right s x
  have hs's : s' ≤ s := min_le_left s x
  have hu's' : (x - s') + s' = x := tsub_add_cancel_of_le hs'x
  have hu'u : x - s' ≤ u := by
    rcases le_total s x with h | h
    · rw [show s' = s from min_eq_left h]; exact tsub_le_iff_right.mpr (hus ▸ hxy)
    · rw [show s' = x from min_eq_right h, tsub_self]; exact zero_le'
  refine le_trans ?_ (conv_ge f.toFun g.toFun (u := x - s') (s := s') hu's')
  show (f.toFun (x - s')).toDual + (g.toFun s').toDual ≤ (f.toFun u).toDual + (g.toFun s).toDual
  gcongr
  · exact hf _ u hu'u
  · exact hg s' s hs's

/-! ### Lemma 2.3 — the four subsets are stable under `∧` and `∗` -/

theorem Fplus.inf_mem {f g : FunDioid} (hf : f ∈ Fplus) (hg : g ∈ Fplus) : f + g ∈ Fplus :=
  hf.inf hg
theorem Fplus.conv_mem {f g : FunDioid} (hf : f ∈ Fplus) (hg : g ∈ Fplus) : f * g ∈ Fplus :=
  hf.conv hg

theorem Fzero.inf_mem {f g : FunDioid} (hf : f ∈ Fzero) (hg : g ∈ Fzero) : f + g ∈ Fzero :=
  ⟨hf.1.inf hg.1, hf.2.inf hg.2⟩
theorem Fzero.conv_mem {f g : FunDioid} (hf : f ∈ Fzero) (hg : g ∈ Fzero) : f * g ∈ Fzero :=
  ⟨hf.1.conv hg.1, hf.2.conv hg.2 hf.1 hg.1⟩

theorem Fnondecr.inf_mem {f g : FunDioid} (hf : f ∈ Fnondecr) (hg : g ∈ Fnondecr) :
    f + g ∈ Fnondecr := ⟨hf.1.inf hg.1, hf.2.inf hg.2⟩
theorem Fnondecr.conv_mem {f g : FunDioid} (hf : f ∈ Fnondecr) (hg : g ∈ Fnondecr) :
    f * g ∈ Fnondecr := ⟨hf.1.conv hg.1, hf.2.conv hg.2⟩

theorem FnondecrZero.inf_mem {f g : FunDioid} (hf : f ∈ FnondecrZero) (hg : g ∈ FnondecrZero) :
    f + g ∈ FnondecrZero :=
  ⟨Fzero.inf_mem hf.1 hg.1, Fnondecr.inf_mem hf.2 hg.2⟩
theorem FnondecrZero.conv_mem {f g : FunDioid} (hf : f ∈ FnondecrZero) (hg : g ∈ FnondecrZero) :
    f * g ∈ FnondecrZero :=
  ⟨Fzero.conv_mem hf.1 hg.1, Fnondecr.conv_mem hf.2 hg.2⟩

end FunDioid

end NetworkCalculus
