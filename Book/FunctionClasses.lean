import VersoManual
import Book.Convolution

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Main subsets of functions" =>
Network calculus restricts attention to special classes of (min,plus)
functions. This chapter formalizes the four subsets, their stability
under $`\wedge` and $`\ast`, and the consequences: $`\mathcal{F}^+` and
$`\mathcal{F}^\uparrow` are complete dioids with the constant-$`0`
function as top, while $`\mathcal{F}_0` and $`\mathcal{F}^\uparrow_0` are
not dioids.

```lean
namespace NetworkCalculus

open scoped Computability NNReal

namespace FunDioid
```

# The predicates and subsets
The defining predicates are stated on the underlying numeric values
(via `.toDual` in $`\overline{R}_{\min}`), since _non-negative_ and
_non-decreasing_ refer to the natural order on values, not the dioid
order.

```lean
/-- Non-negative: each value is `≥ 0` numerically. -/
def IsNonneg (f : FunDioid) : Prop :=
  ∀ t, (0 : Rbar) ≤ (f.toFun t).toDual

/-- Vanishes at `0`: `f(0) = 0` numerically. -/
def IsZeroAtZero (f : FunDioid) : Prop :=
  (f.toFun 0).toDual = 0

/-- Non-decreasing in the natural order. -/
def IsNondecr (f : FunDioid) : Prop :=
  ∀ x y, x ≤ y →
    (f.toFun x).toDual ≤ (f.toFun y).toDual
```

The four subsets of `FunDioid` are $`\mathcal{F}^+` (non-negative),
$`\mathcal{F}_0` (non-negative with $`f(0) = 0`), $`\mathcal{F}^\uparrow`
(non-negative non-decreasing), and
$`\mathcal{F}^\uparrow_0 = \mathcal{F}_0 \cap \mathcal{F}^\uparrow`:

```lean
/-- `F⁺`: the non-negative functions. -/
def Fplus : Set FunDioid := {f | IsNonneg f}

/-- `F₀`: non-negative functions with `f(0) = 0`. -/
def Fzero : Set FunDioid :=
  {f | IsNonneg f ∧ IsZeroAtZero f}

/-- `F↑`: non-negative non-decreasing functions. -/
def Fnondecr : Set FunDioid :=
  {f | IsNonneg f ∧ IsNondecr f}

/-- `F↑₀ = F₀ ∩ F↑`. -/
def FnondecrZero : Set FunDioid := Fzero ∩ Fnondecr
```

# Stability under `∧` and `∗`
The dioid sum `f + g` is the pointwise minimum of the values, and the
product `f * g` is the convolution. A convenient lower bound: a
convolution value is $`\ge 0` once both factors are.

```lean
private theorem conv_apply_nonneg {f g : FunDioid}
    (hf : IsNonneg f) (hg : IsNonneg g) (t : ℝ≥0) :
    (0 : Rbar) ≤ ((f.toFun ∗ g.toFun) t).toDual :=
  conv_le f.toFun g.toFun
    (b := MinPlus.Dual.ofDual (0 : Rbar))
    fun u s _ => by
      show (0 : Rbar)
        ≤ (f.toFun u).toDual + (g.toFun s).toDual
      calc (0 : Rbar) = 0 + 0 := (add_zero 0).symm
        _ ≤ (f.toFun u).toDual + (g.toFun s).toDual :=
          by gcongr <;> [exact hf u; exact hg s]
```

*Proof.* By `conv_le`, each term is $`\ge 0`: $`0 = 0 + 0 \le f(u) + g(s)` from $`f, g \ge 0`. $`\quad\blacksquare`

Each predicate is preserved by both `∧` and `∗`. Non-negativity:

```lean
theorem IsNonneg.inf {f g : FunDioid}
    (hf : IsNonneg f) (hg : IsNonneg g) :
    IsNonneg (f + g) := fun t => le_min (hf t) (hg t)
```

*Proof.* $`0 \le \min(f(t), g(t))` from $`0 \le f(t)`, $`0 \le g(t)` (`le_min`). $`\quad\blacksquare`

```lean
theorem IsNonneg.conv {f g : FunDioid}
    (hf : IsNonneg f) (hg : IsNonneg g) :
    IsNonneg (f * g) :=
  fun t => conv_apply_nonneg hf hg t
```

*Proof.* `conv_apply_nonneg`: $`0 \le ((f \ast g)(t))_{\mathrm{dual}}`. $`\quad\blacksquare`

Vanishing at zero:

```lean
theorem IsZeroAtZero.inf {f g : FunDioid}
    (hf : IsZeroAtZero f) (hg : IsZeroAtZero g) :
    IsZeroAtZero (f + g) := by
  show min (f.toFun 0).toDual (g.toFun 0).toDual = 0
  rw [hf, hg, min_self]
```

*Proof.* $`\min(f(0), g(0)) = \min(0, 0) = 0`. $`\quad\blacksquare`

```lean
theorem IsZeroAtZero.conv {f g : FunDioid}
    (hf : IsZeroAtZero f) (hg : IsZeroAtZero g)
    (hfn : IsNonneg f) (hgn : IsNonneg g) :
    IsZeroAtZero (f * g) := by
  show ((f.toFun ∗ g.toFun) 0).toDual = 0
  apply le_antisymm
  · have h2 : ((f.toFun ∗ g.toFun) 0).toDual
        ≤ (f.toFun 0).toDual + (g.toFun 0).toDual :=
      conv_ge f.toFun g.toFun
        (u := 0) (s := 0) (add_zero 0)
    rwa [hf, hg, add_zero] at h2
  · exact conv_apply_nonneg hfn hgn 0
```

*Proof.* $`\le`: term $`0+0` gives $`(f\ast g)(0) \le f(0)+g(0) = 0`. $`\ge`: `conv_apply_nonneg`. $`\quad\blacksquare`

Non-decreasing-ness. For $`\wedge` it is pointwise; for $`\ast`, given a
decomposition $`u + s = y`, the values $`u' = x - \min(s, x)` and
$`s' = \min(s, x)` give a decomposition of $`x` with $`u' \le u`,
$`s' \le s`, so monotonicity bounds $`(f \ast g)(x)` below
$`f(u) + g(s)`.

```lean
theorem IsNondecr.inf {f g : FunDioid}
    (hf : IsNondecr f) (hg : IsNondecr g) :
    IsNondecr (f + g) := by
  intro x y hxy
  show min (f.toFun x).toDual (g.toFun x).toDual
     ≤ min (f.toFun y).toDual (g.toFun y).toDual
  exact min_le_min (hf x y hxy) (hg x y hxy)
```

*Proof.* $`\min(f(x), g(x)) \le \min(f(y), g(y))` from $`f(x) \le f(y)`, $`g(x) \le g(y)` (`min_le_min`). $`\quad\blacksquare`

```lean
theorem IsNondecr.conv {f g : FunDioid}
    (hf : IsNondecr f) (hg : IsNondecr g) :
    IsNondecr (f * g) := by
  intro x y hxy
  show ((f.toFun ∗ g.toFun) x).toDual
     ≤ ((f.toFun ∗ g.toFun) y).toDual
  refine conv_le f.toFun g.toFun (t := y)
    (b := (f.toFun ∗ g.toFun) x) ?_
  intro u s hus
  set s' := min s x
  have hs'x : s' ≤ x := min_le_right s x
  have hs's : s' ≤ s := min_le_left s x
  have hu's' : (x - s') + s' = x :=
    tsub_add_cancel_of_le hs'x
  have hu'u : x - s' ≤ u := by
    rcases le_total s x with h | h
    · rw [show s' = s from min_eq_left h]
      exact tsub_le_iff_right.mpr (hus ▸ hxy)
    · rw [show s' = x from min_eq_right h, tsub_self]
      exact zero_le'
  refine le_trans ?_
    (conv_ge f.toFun g.toFun
      (u := x - s') (s := s') hu's')
  show (f.toFun (x - s')).toDual
        + (g.toFun s').toDual
     ≤ (f.toFun u).toDual + (g.toFun s).toDual
  gcongr
  · exact hf _ u hu'u
  · exact hg s' s hs's
```

*Proof.* For $`x \le y` and any decomposition $`u + s = y`, set $`s' = \min(s,x)`, $`u' = x - s'`. Then $`u' + s' = x`, $`u' \le u`, $`s' \le s`, so by `conv_ge` and monotonicity:
$$`(f \ast g)(x) \le f(u') + g(s') \le f(u) + g(s). \quad\blacksquare`

The four subsets are stable under both operations:

```lean
theorem Fplus.inf_mem {f g : FunDioid}
    (hf : f ∈ Fplus) (hg : g ∈ Fplus) :
    f + g ∈ Fplus := hf.inf hg
theorem Fplus.conv_mem {f g : FunDioid}
    (hf : f ∈ Fplus) (hg : g ∈ Fplus) :
    f * g ∈ Fplus := hf.conv hg

theorem Fzero.inf_mem {f g : FunDioid}
    (hf : f ∈ Fzero) (hg : g ∈ Fzero) :
    f + g ∈ Fzero := ⟨hf.1.inf hg.1, hf.2.inf hg.2⟩
theorem Fzero.conv_mem {f g : FunDioid}
    (hf : f ∈ Fzero) (hg : g ∈ Fzero) :
    f * g ∈ Fzero :=
  ⟨hf.1.conv hg.1, hf.2.conv hg.2 hf.1 hg.1⟩

theorem Fnondecr.inf_mem {f g : FunDioid}
    (hf : f ∈ Fnondecr) (hg : g ∈ Fnondecr) :
    f + g ∈ Fnondecr :=
  ⟨hf.1.inf hg.1, hf.2.inf hg.2⟩
theorem Fnondecr.conv_mem {f g : FunDioid}
    (hf : f ∈ Fnondecr) (hg : g ∈ Fnondecr) :
    f * g ∈ Fnondecr :=
  ⟨hf.1.conv hg.1, hf.2.conv hg.2⟩

theorem FnondecrZero.inf_mem {f g : FunDioid}
    (hf : f ∈ FnondecrZero) (hg : g ∈ FnondecrZero) :
    f + g ∈ FnondecrZero :=
  ⟨Fzero.inf_mem hf.1 hg.1,
    Fnondecr.inf_mem hf.2 hg.2⟩
theorem FnondecrZero.conv_mem {f g : FunDioid}
    (hf : f ∈ FnondecrZero) (hg : g ∈ FnondecrZero) :
    f * g ∈ FnondecrZero :=
  ⟨Fzero.conv_mem hf.1 hg.1,
    Fnondecr.conv_mem hf.2 hg.2⟩
```

*Proof.* Each class is a conjunction of basic predicates; stability is the corresponding predicate lemmas paired: $`\mathcal{F}^+` uses `IsNonneg.{inf,conv}`; $`\mathcal{F}_0` adds `IsZeroAtZero.{inf,conv}`; $`\mathcal{F}^\uparrow` adds `IsNondecr.{inf,conv}`; $`\mathcal{F}^\uparrow_0 = \mathcal{F}_0 \cap \mathcal{F}^\uparrow` pairs the two. $`\quad\blacksquare`

# `F⁺` and `F↑` are complete dioids
A consequence of the stability results and completeness of
$`R^+_{\min}` is that $`\mathcal{F}^+` and $`\mathcal{F}^\uparrow` are
complete dioids. The top element differs from the ambient `FunDioid` top
$`\top : t \mapsto -\infty` (which is not non-negative): it is the
constant-$`0` function `const0`. It is itself non-negative and
non-decreasing (`const0_isNonneg`, `const0_isNondecr`), and being
non-negative is exactly lying below it in the dioid order,
$`\mathtt{IsNonneg}(f) \iff f \preceq \mathtt{const0}`, so that
$`\mathcal{F}^+ = \{\, f \mid f \preceq \mathtt{const0} \,\}` is the
order-interval below `const0` (`isNonneg_iff_le_const0`, `Fplus_eq_Iic`):

```lean
/-- The constant function equal to numeric `0`. -/
noncomputable def const0 : FunDioid :=
  FunDioid.ofFun
    (fun _ => MinPlus.Dual.ofDual (0 : Rbar))

theorem const0_isNonneg : IsNonneg const0 :=
  fun _ => le_rfl

theorem const0_isNondecr : IsNondecr const0 :=
  fun _ _ _ => le_rfl
```

*Proof.* The value is constant $`0`, so both $`0 \le 0` (non-negativity) and $`0 \le 0` (monotonicity) hold by reflexivity. $`\quad\blacksquare`

```lean
theorem isNonneg_iff_le_const0 {f : FunDioid} :
    IsNonneg f ↔ f ≤ const0 := Iff.rfl

theorem Fplus_eq_Iic : Fplus = Set.Iic const0 := rfl
```

The numeric value of an arbitrary dioid supremum is the pointwise
numeric _infimum_ (the dioid `sSup` is the pointwise
$`\overline{R}_{\min}` supremum, whose `.toDual` is the numeric
infimum):

```lean
theorem sSup_toFun_toDual (T : Set FunDioid)
    (t : ℝ≥0) :
    ((sSup T).toFun t).toDual
      = ⨅ f : T, ((f : FunDioid).toFun t).toDual := by
  rw [toFun_sSup,
    ← iSup_subtype'' T (fun a : FunDioid => a.toFun),
    iSup_apply]
  exact MinPlus.Dual.toDual_iSup_eq
    (fun a : T => (a : FunDioid).toFun t)
```

Each class is closed under arbitrary dioid sums: `const0` is an upper
bound, and for $`\mathcal{F}^\uparrow` the pointwise infimum of
non-decreasing functions is non-decreasing:

```lean
theorem Fplus.sSup_mem {T : Set FunDioid}
    (hT : ∀ f ∈ T, f ∈ Fplus) : sSup T ∈ Fplus :=
  isNonneg_iff_le_const0.mpr
    (sSup_le fun f hf =>
      isNonneg_iff_le_const0.mp (hT f hf))
```

*Proof.* $`\sup T \in \mathcal{F}^+ \iff \sup T \preceq \mathtt{const0} \iff \forall f \in T,\ f \preceq \mathtt{const0}` (`sSup_le`), which is the hypothesis. $`\quad\blacksquare`

```lean
theorem Fnondecr.sSup_mem {T : Set FunDioid}
    (hT : ∀ f ∈ T, f ∈ Fnondecr) :
    sSup T ∈ Fnondecr := by
  refine ⟨?_, ?_⟩
  · show sSup T ≤ const0
    exact sSup_le fun f hf => (hT f hf).1
  · intro x y hxy
    rw [sSup_toFun_toDual, sSup_toFun_toDual]
    exact iInf_mono fun f =>
      (hT (f : FunDioid) f.2).2 x y hxy
```

*Proof.* Non-negativity as above. Monotonicity: the dioid sup is numerically the pointwise infimum, $`((\sup T)(t))_{\mathrm{dual}} = \inf_{f \in T} (f(t))_{\mathrm{dual}}`, monotone in $`t` by `iInf_mono` since each $`f` is. $`\quad\blacksquare`

The neutrals lie in both classes:

```lean
theorem zero_isNonneg : IsNonneg (0 : FunDioid) :=
  fun _ => le_top

theorem one_isNonneg : IsNonneg (1 : FunDioid) :=
  fun t => by
    show (0 : Rbar) ≤ ((1 : FunDioid).toFun t).toDual
    show (0 : Rbar)
      ≤ ((if t = 0 then (1 : RbarMin)
            else 0).toDual)
    by_cases h : t = 0
    · rw [if_pos h]; exact le_rfl
    · rw [if_neg h]; exact le_top

theorem zero_mem_Fnondecr :
    (0 : FunDioid) ∈ Fnondecr :=
  ⟨zero_isNonneg, fun _ _ _ => le_rfl⟩

theorem one_mem_Fnondecr :
    (1 : FunDioid) ∈ Fnondecr := ⟨one_isNonneg, by
  intro x y hxy
  show (if x = 0 then (1 : RbarMin) else 0).toDual
     ≤ (if y = 0 then (1 : RbarMin) else 0).toDual
  by_cases hy : y = 0
  · rw [if_pos hy,
      if_pos (le_antisymm (hy ▸ hxy)
        (zero_le' (a := x)))]
  · rw [if_neg hy]; exact le_top⟩
```

*Proof.* $`\varepsilon \equiv +\infty = \top`, so $`0 \le \top` and $`\top \le \top` (`le_top`): non-negative, non-decreasing. $`e` has value $`0` at $`0` and $`+\infty` else: non-negative ($`0 \le 0`, $`0 \le \top`), and non-decreasing since $`x \le y = 0 \Rightarrow x = 0` and otherwise the codomain value is $`\top`. $`\quad\blacksquare`

Both $`\mathcal{F}^+` and $`\mathcal{F}^\uparrow` are then
`SubCompleteDioid FunDioid`: the closure data feeds the generic builder
of the previous chapter, supplying the complete dioid structure with the
adjusted top `sSup carrier`.

```lean
noncomputable def SfPlus : SubCompleteDioid FunDioid where
  carrier := Fplus
  zero_mem := zero_isNonneg
  one_mem := one_isNonneg
  add_mem := Fplus.inf_mem
  mul_mem := Fplus.conv_mem
  sSup_mem := Fplus.sSup_mem

noncomputable def SfNondecr :
    SubCompleteDioid FunDioid where
  carrier := Fnondecr
  zero_mem := zero_mem_Fnondecr
  one_mem := one_mem_Fnondecr
  add_mem := Fnondecr.inf_mem
  mul_mem := Fnondecr.conv_mem
  sSup_mem := Fnondecr.sSup_mem

end FunDioid
```

The carrier of $`\mathcal{F}^+` as a complete dioid is the subtype of
non-negative functions. Its top is the constant-$`0` function — a
subtle point, since it is _not_ the ambient `FunDioid` top:

```lean
open FunDioid in
abbrev FPlus : Type := SfPlus.Sub

namespace FPlus

open FunDioid SubCompleteDioid

noncomputable def val (x : FPlus) : FunDioid :=
  SubCompleteDioid.val SfPlus x

noncomputable def mk (f : FunDioid)
    (hf : IsNonneg f) : FPlus :=
  SubCompleteDioid.pack SfPlus f hf

theorem top_eq_const0 :
    (⊤ : FPlus).val = const0 := by
  rw [show (⊤ : FPlus).val = sSup SfPlus.carrier from
      SubCompleteDioid.val_top SfPlus,
    show SfPlus.carrier = Set.Iic const0 from
      Fplus_eq_Iic]
  exact csSup_Iic
```

*Proof.* $`(\top).\mathtt{val} = \sup \mathcal{F}^+ = \sup(\mathrm{Iic}\,\mathtt{const0}) = \mathtt{const0}` (`val_top`, `Fplus_eq_Iic`, `csSup_Iic`). $`\quad\blacksquare`

```lean
noncomputable example :
    CompleteDioid FPlus := inferInstance

end FPlus
```

The carrier of $`\mathcal{F}^\uparrow` is the subtype of non-negative
non-decreasing functions. Unlike $`\mathcal{F}^+` it is not an
order-interval, but it has the same adjusted top `const0` (its greatest
element):

```lean
open FunDioid in
abbrev FNondecr : Type := SfNondecr.Sub

namespace FNondecr

open FunDioid SubCompleteDioid

noncomputable def val (x : FNondecr) : FunDioid :=
  SubCompleteDioid.val SfNondecr x

noncomputable def mk (f : FunDioid)
    (hf : f ∈ Fnondecr) : FNondecr :=
  SubCompleteDioid.pack SfNondecr f hf

theorem top_eq_const0 :
    (⊤ : FNondecr).val = const0 := by
  rw [show (⊤ : FNondecr).val
      = sSup SfNondecr.carrier from
      SubCompleteDioid.val_top SfNondecr]
  refine le_antisymm
    (sSup_le fun f hf => hf.1) (le_sSup ?_)
  exact ⟨const0_isNonneg, const0_isNondecr⟩
```

*Proof.* $`(\top).\mathtt{val} = \sup \mathcal{F}^\uparrow = \mathtt{const0}` by antisymmetry: $`\le` since every $`f \in \mathcal{F}^\uparrow` has $`f \preceq \mathtt{const0}` (`sSup_le`); $`\ge` since $`\mathtt{const0} \in \mathcal{F}^\uparrow` (`le_sSup`). $`\quad\blacksquare`

```lean
noncomputable example :
    CompleteDioid FNondecr := inferInstance

end FNondecr
```

# `F₀` and `F↑₀` are not dioids
A dioid must contain its zero $`\mathbf{0} = \varepsilon : t \mapsto +\infty`.
But $`\varepsilon(0) = +\infty \ne 0`, whereas every element of
$`\mathcal{F}_0` and $`\mathcal{F}^\uparrow_0` satisfies $`f(0) = 0`.
So $`\varepsilon` is not a member of either set, and neither is a dioid:

```lean
namespace FunDioid

theorem eps_not_zeroAtZero :
    ¬ IsZeroAtZero (0 : FunDioid) := by
  intro h
  have : (⊤ : Rbar) = 0 := h
  simp at this
```

*Proof.* $`\varepsilon(0) = +\infty = \top \ne 0`. $`\quad\blacksquare`

```lean
theorem eps_not_mem_Fzero :
    (0 : FunDioid) ∉ Fzero :=
  fun h => eps_not_zeroAtZero h.2
```

*Proof.* $`\mathcal{F}_0`-membership would force $`\varepsilon(0) = 0`, contradicting `eps_not_zeroAtZero`. $`\quad\blacksquare`

```lean
theorem eps_not_mem_FnondecrZero :
    (0 : FunDioid) ∉ FnondecrZero :=
  fun h => eps_not_zeroAtZero h.1.2

end FunDioid

end NetworkCalculus
```

*Proof.* $`\mathcal{F}^\uparrow_0 \subseteq \mathcal{F}_0` would force $`\varepsilon(0) = 0`, contradicting `eps_not_zeroAtZero`. $`\quad\blacksquare`

This is why $`\mathcal{F}^+` and $`\mathcal{F}^\uparrow`, which _do_
contain $`\varepsilon`, are the complete dioids.
