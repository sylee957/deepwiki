import Leanproofs.MinPlus.FunctionClasses
import Leanproofs.MinPlus.SubDioid

/-!
# `F⁺` and `F↑` are complete dioids, and `F₀`, `F↑₀` are not dioids (after Lemma 2.3)

> *A consequence of [Lemma 2.3] and of the fact that `R⁺min` is a complete dioid is that `F↑` and
> `F⁺` are complete dioids. Note that the top element of `F⁺` differs: it is the constant function
> equal to zero. Also, note that `F₀` and `F↑₀` are not dioids, as `ε` is not an element of these
> sets.* — Bouillard, Boyer, Le Corronc, after Lemma 2.3.

This module formalizes the three claims of that paragraph.

## `F⁺` and `F↑` via the generic sub-complete-dioid builder

Both `F⁺` (non-negative functions) and `F↑` (non-negative non-decreasing functions) are
*sub-complete-dioids* of `FunDioid`: subsets containing `𝟘, 𝟙`, closed under `⊕, ⊗` (Lemma 2.3) and
under arbitrary dioid `sSup`. `Leanproofs.MinPlus.SubDioid` packages exactly this data
(`SubCompleteDioid`) and produces the complete commutative dioid on the subtype generically, with
the **adjusted top `sSup carrier`**. So here each class is just the carrier plus its six closure
proofs (`SfPlus`, `SfNondecr`), and the dioid structure is inherited.

The adjusted top is the constant-`0` function `const0` for both classes — the subtle point the book
flags, since it differs from the ambient `FunDioid` top `⊤ : t ↦ −∞` (which is not non-negative):

* `F⁺ = Set.Iic const0`, and `sSup (Set.Iic const0) = const0`;
* `F↑` is not an interval, but `const0` is its greatest element, so `sSup Fnondecr = const0`.

## `F₀` and `F↑₀` are not dioids

A dioid must contain its zero `𝟘 = ε : t ↦ +∞`. But `ε(0) = +∞ ≠ 0`, so `ε ∉ F₀` and `ε ∉ F↑₀`
(both require `f(0) = 0`). Hence neither set is a dioid.
-/

namespace NetworkCalculus

open scoped Computability NNReal

namespace FunDioid

/-! ### The adjusted top: the constant-`0` function -/

/-- The constant function equal to (numeric) `0`: `t ↦ 0` in `R̄min`. In the dioid order it is the
greatest non-negative function, and it is the **top element of `F⁺` and `F↑`** — the point the book
flags, since it differs from the ambient `FunDioid` top `⊤ : t ↦ −∞`. -/
noncomputable def const0 : FunDioid := FunDioid.ofFun (fun _ => MinPlus.D.ofDual (0 : Rbar))

/-- `const0` is non-negative (its values are numerically `0 ≥ 0`). -/
theorem const0_isNonneg : IsNonneg const0 := fun _ => le_rfl

/-- `const0` is non-decreasing (it is constant). -/
theorem const0_isNondecr : IsNondecr const0 := fun _ _ _ => le_rfl

/-- A function is non-negative (`Fplus`) iff it lies `≼ const0` in the dioid order: non-negativity
is the principal down-set of `const0`. -/
theorem isNonneg_iff_le_const0 {f : FunDioid} : IsNonneg f ↔ f ≤ const0 := Iff.rfl

/-- **`F⁺` is the dioid order-interval `(-∞, const0]`.** -/
theorem Fplus_eq_Iic : Fplus = Set.Iic const0 := rfl

/-! ### Closure of `Fplus`/`Fnondecr` under arbitrary dioid sums -/

/-- The numeric value of an arbitrary dioid supremum is the pointwise numeric **infimum**:
`(sSup T)(t)` (numerically) `= ⨅_{f ∈ T} f(t)`. (The dioid `sSup` is the pointwise `R̄min`
supremum, whose `.toDual` is the numeric infimum.) -/
theorem sSup_toFun_toDual (T : Set FunDioid) (t : ℝ≥0) :
    ((sSup T).toFun t).toDual = ⨅ f : T, ((f : FunDioid).toFun t).toDual := by
  rw [toFun_sSup, ← iSup_subtype'' T (fun a : FunDioid => a.toFun), iSup_apply]
  exact MinPlus.D.toDual_iSup_eq (fun a : T => (a : FunDioid).toFun t)

/-- **`F⁺` is closed under arbitrary dioid sums.** `const0` is an upper bound of any
`T ⊆ Fplus`, so `sSup T ≼ const0`, i.e. `sSup T` is non-negative. -/
theorem Fplus.sSup_mem {T : Set FunDioid} (hT : ∀ f ∈ T, f ∈ Fplus) : sSup T ∈ Fplus :=
  isNonneg_iff_le_const0.mpr (sSup_le fun f hf => isNonneg_iff_le_const0.mp (hT f hf))

/-- **`F↑` is closed under arbitrary dioid sums.** The pointwise numeric infimum of non-negative
functions is non-negative (`const0` bounds them) and the infimum of non-decreasing functions is
non-decreasing (`iInf_mono`), so `sSup T ∈ Fnondecr` whenever every element is. -/
theorem Fnondecr.sSup_mem {T : Set FunDioid} (hT : ∀ f ∈ T, f ∈ Fnondecr) :
    sSup T ∈ Fnondecr := by
  refine ⟨?_, ?_⟩
  · -- non-negativity: `const0` is an upper bound of `T`, so `sSup T ≼ const0`.
    show sSup T ≤ const0
    exact sSup_le fun f hf => (hT f hf).1
  · -- non-decreasing: pointwise infimum of non-decreasing functions.
    intro x y hxy
    rw [sSup_toFun_toDual, sSup_toFun_toDual]
    exact iInf_mono fun f => (hT (f : FunDioid) f.2).2 x y hxy

/-- `𝟘 = ε` is non-negative (it is the dioid `⊥`, hence `≼ const0`). -/
theorem zero_isNonneg : IsNonneg (0 : FunDioid) := fun _ => le_top

/-- `𝟙 = e` is non-negative. -/
theorem one_isNonneg : IsNonneg (1 : FunDioid) := fun t => by
  show (0 : Rbar) ≤ ((1 : FunDioid).toFun t).toDual
  show (0 : Rbar) ≤ ((if t = 0 then (1 : RbarMin) else 0).toDual)
  by_cases h : t = 0
  · rw [if_pos h]; exact le_rfl
  · rw [if_neg h]; exact le_top

/-- `𝟘 = ε` is non-negative and non-decreasing, so it lies in `F↑`. -/
theorem zero_mem_Fnondecr : (0 : FunDioid) ∈ Fnondecr := ⟨zero_isNonneg, fun _ _ _ => le_rfl⟩

/-- `𝟙 = e` is non-negative and non-decreasing, so it lies in `F↑`. -/
theorem one_mem_Fnondecr : (1 : FunDioid) ∈ Fnondecr := ⟨one_isNonneg, by
  intro x y hxy
  show (if x = 0 then (1 : RbarMin) else 0).toDual ≤ (if y = 0 then (1 : RbarMin) else 0).toDual
  by_cases hy : y = 0
  · -- `x ≤ y = 0` forces `x = 0`, so both values agree.
    rw [if_pos hy, if_pos (le_antisymm (hy ▸ hxy) (zero_le' (a := x)))]
  · rw [if_neg hy]; exact le_top⟩

/-! ### `F⁺` and `F↑` as sub-complete-dioids of `FunDioid`

Both are `SubCompleteDioid FunDioid`: the closure data feeds the generic builder of
`Leanproofs.MinPlus.SubDioid`, which supplies the complete commutative dioid structure with the
adjusted top `sSup carrier`. -/

/-- The non-negative functions `F⁺ = Set.Iic const0` as a sub-complete-dioid of `FunDioid`
(Lemma 2.3 closure under `⊕`/`⊗`; `const0` bounds every member, so `sSup` stays inside). -/
noncomputable def SfPlus : SubCompleteDioid FunDioid where
  carrier := Fplus
  zero_mem := zero_isNonneg
  one_mem := one_isNonneg
  add_mem := Fplus.inf_mem
  mul_mem := Fplus.conv_mem
  sSup_mem := Fplus.sSup_mem

/-- The non-negative non-decreasing functions `F↑ = Fnondecr` as a sub-complete-dioid of `FunDioid`
(Lemma 2.3 closure under `⊕`/`⊗`; the pointwise infimum of members stays in `F↑`). -/
noncomputable def SfNondecr : SubCompleteDioid FunDioid where
  carrier := Fnondecr
  zero_mem := zero_mem_Fnondecr
  one_mem := one_mem_Fnondecr
  add_mem := Fnondecr.inf_mem
  mul_mem := Fnondecr.conv_mem
  sSup_mem := Fnondecr.sSup_mem

end FunDioid

/-! ## `F⁺` as a complete dioid -/

open FunDioid in
/-- The carrier of `F⁺` as a complete dioid: the dioid order-interval `Set.Iic const0` of
non-negative functions, as the subtype `{f // IsNonneg f}` of `FunDioid`. -/
abbrev FPlus : Type := SfPlus.Sub

namespace FPlus

open FunDioid SubCompleteDioid

/-- The underlying `FunDioid` of an element of `F⁺`. -/
noncomputable def val (x : FPlus) : FunDioid := SubCompleteDioid.val SfPlus x

/-- Package a non-negative function as an element of `F⁺`. -/
noncomputable def mk (f : FunDioid) (hf : IsNonneg f) : FPlus := SubCompleteDioid.pack SfPlus f hf

/-- **The top element of `F⁺` is the constant-`0` function** — the subtle point the book flags. It
is *not* the ambient `FunDioid` top `⊤ : t ↦ −∞` (which is not even non-negative). The builder's
adjusted top is `sSup (Set.Iic const0) = const0`. -/
theorem top_eq_const0 : (⊤ : FPlus).val = const0 := by
  rw [show (⊤ : FPlus).val = sSup SfPlus.carrier from SubCompleteDioid.val_top SfPlus,
    show SfPlus.carrier = Set.Iic const0 from Fplus_eq_Iic]
  exact csSup_Iic

noncomputable example : CompleteDioid FPlus := inferInstance

end FPlus

/-! ## `F↑` as a complete dioid -/

open FunDioid in
/-- The carrier of `F↑` as a complete dioid: the non-negative non-decreasing functions, as the
subtype `{f // f ∈ Fnondecr}` of `FunDioid`. Unlike `F⁺` it is not an order-interval, but it is
closed under all the dioid and lattice operations and has the same adjusted top `const0`. -/
abbrev FNondecr : Type := SfNondecr.Sub

namespace FNondecr

open FunDioid SubCompleteDioid

/-- The underlying `FunDioid` of an element of `F↑`. -/
noncomputable def val (x : FNondecr) : FunDioid := SubCompleteDioid.val SfNondecr x

/-- Package a non-negative non-decreasing function as an element of `F↑`. -/
noncomputable def mk (f : FunDioid) (hf : f ∈ Fnondecr) : FNondecr :=
  SubCompleteDioid.pack SfNondecr f hf

/-- **The top element of `F↑` is the constant-`0` function** `const0` — the same adjusted top as
`F⁺`, since `const0` is non-decreasing as well as non-negative. The builder's adjusted top is
`sSup Fnondecr`, which is `const0` because `const0` is the greatest element of `F↑`. -/
theorem top_eq_const0 : (⊤ : FNondecr).val = const0 := by
  rw [show (⊤ : FNondecr).val = sSup SfNondecr.carrier from SubCompleteDioid.val_top SfNondecr]
  refine le_antisymm (sSup_le fun f hf => hf.1) (le_sSup ?_)
  exact ⟨const0_isNonneg, const0_isNondecr⟩

noncomputable example : CompleteDioid FNondecr := inferInstance

end FNondecr

/-! ## `F₀` and `F↑₀` are not dioids

The dioid zero is `𝟘 = ε : t ↦ +∞` (the constant `+∞`). A dioid must contain its `𝟘`. But every
element of `F₀` and `F↑₀` satisfies `f(0) = 0` (numerically), whereas `ε(0) = +∞ ≠ 0`. So `ε ∉ F₀`
and `ε ∉ F↑₀`, and therefore **neither set is a dioid** — they lack the additive neutral. (This is
why the book singles out `F⁺` and `F↑`, which *do* contain `ε`, as the complete dioids.) -/

namespace FunDioid

/-- `ε = 𝟘` does *not* vanish at `0`: `ε(0) = +∞ ≠ 0`. -/
theorem eps_not_zeroAtZero : ¬ IsZeroAtZero (0 : FunDioid) := by
  intro h
  have : (⊤ : Rbar) = 0 := h
  simp at this

/-- `ε ∉ F₀`: hence `F₀` is **not a dioid** (it lacks the dioid zero `ε`). -/
theorem eps_not_mem_Fzero : (0 : FunDioid) ∉ Fzero := fun h => eps_not_zeroAtZero h.2

/-- `ε ∉ F↑₀`: hence `F↑₀` is **not a dioid** (it lacks the dioid zero `ε`). -/
theorem eps_not_mem_FnondecrZero : (0 : FunDioid) ∉ FnondecrZero := fun h => eps_not_zeroAtZero h.1.2

end FunDioid

end NetworkCalculus
