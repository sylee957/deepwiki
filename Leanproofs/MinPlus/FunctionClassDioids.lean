import Leanproofs.MinPlus.FunctionClasses
import Mathlib.Order.CompleteLatticeIntervals
import Mathlib.Order.LatticeIntervals

/-!
# `F⁺` and `F↑` are complete dioids, and `F₀`, `F↑₀` are not dioids (after Lemma 2.3)

> *A consequence of [Lemma 2.3] and of the fact that `R⁺min` is a complete dioid is that `F↑` and
> `F⁺` are complete dioids. Note that the top element of `F⁺` differs: it is the constant function
> equal to zero. Also, note that `F₀` and `F↑₀` are not dioids, as `ε` is not an element of these
> sets.* — Bouillard, Boyer, Le Corronc, after Lemma 2.3.

This module formalizes the three claims of that paragraph.

## `F⁺` is a complete dioid with top `const0` (the constant-`0` function)

In the dioid order `≼` on `FunDioid` (the *reverse* of the pointwise numeric order on `R̄min`), a
function is non-negative (`Fplus`) exactly when it is `≼ const0`, where `const0 : t ↦ 0`. Hence

  `F⁺ = Fplus = Set.Iic const0`  (`Fplus_eq_Iic`),

a principal down-set in the dioid order. Mathlib equips `Set.Iic const0` with a `CompleteLattice`
(`Set.Iic.instCompleteLattice`) whose top is `const0` itself (`Set.Iic.coe_top`). The dioid sum
`⊕ = ⊔`, product `⊗ = ∗`, neutrals `𝟘 = ε`, `𝟙 = e`, and arbitrary `sSup` all restrict to this
interval (Lemma 2.3 for `⊕`/`⊗`; the supremum stays `≼ const0` since `const0` is an upper bound),
so `F⁺` is a complete commutative dioid — but with **top `const0`**, not the ambient `FunDioid` top
`⊤ : t ↦ −∞` (which is *not* non-negative).

## `F↑` is a complete dioid with the same top `const0`

`F↑ = Fnondecr` is *not* an order-interval, but it is closed under `⊕`, `⊗` (Lemma 2.3), under
arbitrary dioid `sSup` (the pointwise infimum of non-decreasing functions is non-decreasing, and the
supremum stays `≼ const0`), and it contains `const0` (constant, hence non-decreasing). So it is a
sub-complete-lattice of `FunDioid` *with the adjusted top* `const0`, and a complete dioid.

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

end FunDioid

/-! ## `F⁺` as a complete dioid -/

/-- The carrier of `F⁺` as a complete dioid: the dioid order-interval `Set.Iic const0` of
non-negative functions. As a subtype of `FunDioid` it is `{f // f ≼ const0} = {f // IsNonneg f}`. -/
def FPlus : Type := Set.Iic (FunDioid.const0)

namespace FPlus

open FunDioid

instance : CoeOut FPlus FunDioid := ⟨fun x => (x : Set.Iic FunDioid.const0).1⟩

/-- The underlying `FunDioid` of an element of `F⁺`. -/
def val (x : FPlus) : FunDioid := (x : Set.Iic FunDioid.const0).1

theorem val_le_const0 (x : FPlus) : x.val ≤ const0 := (x : Set.Iic FunDioid.const0).2

theorem val_isNonneg (x : FPlus) : IsNonneg x.val := x.val_le_const0

@[ext] theorem ext {x y : FPlus} (h : x.val = y.val) : x = y := Subtype.ext h

/-- Package a non-negative function as an element of `F⁺`. -/
def mk (f : FunDioid) (hf : IsNonneg f) : FPlus := ⟨f, hf⟩

@[simp] theorem val_mk (f : FunDioid) (hf : IsNonneg f) : (mk f hf).val = f := rfl

/-! ### The complete lattice on `F⁺`, transported from `Set.Iic const0`

`Set.Iic.instCompleteLattice` gives the complete lattice, with `⊤ = const0` (`Set.Iic.coe_top`),
`⊥ = ε` (`Set.Iic.coe_bot`), `⊔`/`sSup` the ambient ones restricted (`Set.Iic.coe_sup`/`coe_sSup`).
-/

noncomputable instance instCompleteLattice : CompleteLattice FPlus :=
  (inferInstance : CompleteLattice (Set.Iic FunDioid.const0))

theorem val_top : (⊤ : FPlus).val = const0 := Set.Iic.coe_top _
theorem val_sup (x y : FPlus) : (x ⊔ y).val = x.val ⊔ y.val := Set.Iic.coe_sup
theorem val_bot : (⊥ : FPlus).val = (⊥ : FunDioid) := Set.Iic.coe_bot _
theorem val_sSup (S : Set FPlus) : (sSup S).val = sSup ((·.val) '' S) := Set.Iic.coe_sSup _

theorem val_iSup {ι : Sort*} (f : ι → FPlus) : (⨆ i, f i).val = ⨆ i, (f i).val :=
  Set.Iic.coe_iSup f

theorem val_biSup {ι : Sort*} (f : ι → FPlus) (p : ι → Prop) :
    (⨆ i, ⨆ (_ : p i), f i).val = ⨆ i, ⨆ (_ : p i), (f i).val := Set.Iic.coe_biSup f p

/-! ### The dioid operations on `F⁺`

`F⁺` is closed under `⊕ = ⊔` (`Fplus.inf_mem`), `⊗ = ∗` (`Fplus.conv_mem`), and contains `𝟘 = ε`
(non-negative as the dioid `⊥`) and `𝟙 = e`. The operations are the ambient `FunDioid` ones, so all
semiring laws follow from those on `FunDioid` via `Subtype.ext`. -/

theorem zero_isNonneg : IsNonneg (0 : FunDioid) := fun _ => le_top
theorem one_isNonneg : IsNonneg (1 : FunDioid) := fun t => by
  show (0 : Rbar) ≤ ((1 : FunDioid).toFun t).toDual
  show (0 : Rbar) ≤ ((if t = 0 then (1 : RbarMin) else 0).toDual)
  by_cases h : t = 0
  · rw [if_pos h]; exact le_rfl
  · rw [if_neg h]; exact le_top

noncomputable instance : Zero FPlus := ⟨mk 0 zero_isNonneg⟩
noncomputable instance : One FPlus := ⟨mk 1 one_isNonneg⟩
noncomputable instance : Add FPlus := ⟨fun x y => mk (x.val + y.val) (x.val_isNonneg.inf y.val_isNonneg)⟩
noncomputable instance : Mul FPlus := ⟨fun x y => mk (x.val * y.val) (x.val_isNonneg.conv y.val_isNonneg)⟩

@[simp] theorem val_zero : (0 : FPlus).val = 0 := rfl
@[simp] theorem val_one : (1 : FPlus).val = 1 := rfl
@[simp] theorem val_add (x y : FPlus) : (x + y).val = x.val + y.val := rfl
@[simp] theorem val_mul (x y : FPlus) : (x * y).val = x.val * y.val := rfl

/-- The idempotent scalar action stays non-negative: `n • f` is a finite dioid sum of `f`
(or `ε`), so it is `≼ const0` whenever `f` is. -/
theorem nsmul_isNonneg (n : ℕ) {f : FunDioid} (hf : IsNonneg f) : IsNonneg (n • f) := by
  induction n with
  | zero => rw [zero_smul]; exact zero_isNonneg
  | succ k ih => rw [succ_nsmul]; exact ih.inf hf

/-- Idempotent scalar action on `F⁺`, inherited from `FunDioid`. -/
noncomputable instance : SMul ℕ FPlus :=
  ⟨fun n x => mk (n • x.val) (nsmul_isNonneg n x.val_isNonneg)⟩

@[simp] theorem val_nsmul (n : ℕ) (x : FPlus) : (n • x).val = n • x.val := rfl

/-- The natural-number cast stays non-negative: `↑n` is `ε` or `e`, both non-negative. -/
theorem natCast_isNonneg (n : ℕ) : IsNonneg ((n : ℕ) : FunDioid) := by
  cases n with
  | zero => rw [Nat.cast_zero]; exact zero_isNonneg
  | succ k => rw [Nat.cast_succ]; exact (natCast_isNonneg k).inf one_isNonneg

/-- The natural-number cast on `F⁺`, inherited from `FunDioid`. -/
noncomputable instance : NatCast FPlus := ⟨fun n => mk (n : FunDioid) (natCast_isNonneg n)⟩

@[simp] theorem val_natCast (n : ℕ) : (NatCast.natCast n : FPlus).val = (n : FunDioid) := rfl

/-! ### The complete dioid on `F⁺`

Every semiring law is the ambient `FunDioid` law projected through `val` (`FPlus.ext`). The lattice
is `Set.Iic const0`'s, so `add_eq_sup` is `FunDioid.add_eq_sup'` projected, and `mul_sSup` is
`FunDioid.completeDioid.mul_sSup` projected (the supremum coercions agree, `Set.Iic.coe_sSup`). -/

/-- The (min,plus) commutative semiring on `F⁺`, with every law inherited from `FunDioid`. -/
noncomputable instance commSemiring : CommSemiring FPlus where
  add_assoc a b c := ext <| by rw [val_add, val_add, val_add, val_add, add_assoc]
  add_comm a b := ext <| by rw [val_add, val_add, add_comm]
  zero_add a := ext <| by rw [val_add, val_zero, zero_add]
  add_zero a := ext <| by rw [val_add, val_zero, add_zero]
  nsmul := (· • ·)
  nsmul_zero a := ext <| by rw [val_nsmul, val_zero, zero_smul]
  nsmul_succ n a := ext <| by rw [val_nsmul, val_add, val_nsmul, succ_nsmul]
  mul_assoc a b c := ext <| by rw [val_mul, val_mul, val_mul, val_mul, mul_assoc]
  mul_comm a b := ext <| by rw [val_mul, val_mul, mul_comm]
  one_mul a := ext <| by rw [val_mul, val_one, one_mul]
  mul_one a := ext <| by rw [val_mul, val_one, mul_one]
  zero_mul a := ext <| by rw [val_mul, val_zero, zero_mul]
  mul_zero a := ext <| by rw [val_mul, val_zero, mul_zero]
  natCast := fun n => (n : FPlus)
  natCast_zero := ext <| by rw [val_natCast, val_zero, Nat.cast_zero]
  natCast_succ n := ext <| by rw [val_natCast, val_add, val_natCast, val_one, Nat.cast_succ]
  left_distrib a b c := ext <| by rw [val_mul, val_add, val_add, val_mul, val_mul, left_distrib]
  right_distrib a b c := ext <| by rw [val_mul, val_add, val_add, val_mul, val_mul, right_distrib]

/-- The dioid sum `⊕` on `F⁺` is the lattice join `⊔` (of `Set.Iic const0`). -/
theorem add_eq_sup' (x y : FPlus) : x + y = x ⊔ y :=
  ext (by rw [val_add, val_sup, FunDioid.add_eq_sup'])

/-- The (min,plus) **dioid** on `F⁺`: the canonical order is the restriction of `FunDioid`'s, with
join `⊕ = ⊔` and bottom `𝟘 = ε`. -/
noncomputable instance dioid : Dioid FPlus :=
  { commSemiring, (inferInstance : CompleteLattice FPlus) with
    add_eq_sup := add_eq_sup' }

/-- The dioid product `⊗` on `F⁺` distributes over an arbitrary dioid `sSup`. The lattice `sSup` of
`Set.Iic const0` coerces to the ambient `FunDioid` `sSup` (`Set.Iic.coe_sSup`), so this is
`FunDioid.completeDioid.mul_sSup` projected through `val`. -/
theorem mul_sSup' (a : FPlus) (S : Set FPlus) : a * sSup S = ⨆ b ∈ S, a * b := by
  apply ext
  rw [val_mul, val_sSup, CompleteDioid.mul_sSup a.val ((·.val) '' S), iSup_image,
    val_biSup]
  exact iSup_congr fun b => iSup_congr fun _ => (val_mul a b).symm

/-- **`F⁺` is a complete commutative dioid** (after Lemma 2.3), with the **adjusted top `const0`**
(the constant-`0` function), *not* the ambient `FunDioid` top `⊤ : t ↦ −∞`. -/
noncomputable instance completeDioid : CompleteDioid FPlus :=
  { dioid, (inferInstance : CompleteLattice FPlus) with
    mul_sSup := mul_sSup' }

/-- **The top element of `F⁺` is the constant-`0` function** — the subtle point the book flags. It
is *not* the ambient `FunDioid` top `⊤ : t ↦ −∞` (which is not even non-negative). -/
theorem top_eq_const0 : (⊤ : FPlus).val = const0 := val_top

noncomputable example : CompleteDioid FPlus := inferInstance

end FPlus

/-! ## `F↑` as a complete dioid -/

namespace FunDioid

/-- The numeric value of an arbitrary dioid supremum is the pointwise numeric **infimum**:
`(sSup T)(t)` (numerically) `= ⨅_{f ∈ T} f(t)`. (The dioid `sSup` is the pointwise `R̄min`
supremum, whose `.toDual` is the numeric infimum.) -/
theorem sSup_toFun_toDual (T : Set FunDioid) (t : ℝ≥0) :
    ((sSup T).toFun t).toDual = ⨅ f : T, ((f : FunDioid).toFun t).toDual := by
  rw [toFun_sSup, ← iSup_subtype'' T (fun a : FunDioid => a.toFun), iSup_apply]
  exact MinPlus.D.toDual_iSup_eq (fun a : T => (a : FunDioid).toFun t)

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

end FunDioid

/-- The carrier of `F↑` as a complete dioid: the non-negative non-decreasing functions, as a subtype
of `FunDioid`. Unlike `F⁺` it is not an order-interval, but it is closed under all the dioid and
lattice operations and contains the adjusted top `const0`. -/
def FNondecr : Type := {f : FunDioid // f ∈ FunDioid.Fnondecr}

namespace FNondecr

open FunDioid

/-- The underlying `FunDioid` of an element of `F↑`. -/
def val (x : FNondecr) : FunDioid := x.1

theorem property (x : FNondecr) : x.val ∈ Fnondecr := x.2

theorem val_isNonneg (x : FNondecr) : IsNonneg x.val := x.2.1
theorem val_le_const0 (x : FNondecr) : x.val ≤ const0 := x.2.1

@[ext] theorem ext {x y : FNondecr} (h : x.val = y.val) : x = y := Subtype.ext h

/-- Package a non-negative non-decreasing function as an element of `F↑`. -/
def mk (f : FunDioid) (hf : f ∈ Fnondecr) : FNondecr := ⟨f, hf⟩

@[simp] theorem val_mk (f : FunDioid) (hf : f ∈ Fnondecr) : (mk f hf).val = f := rfl

noncomputable instance : PartialOrder FNondecr := Subtype.partialOrder _

theorem le_def (x y : FNondecr) : x ≤ y ↔ x.val ≤ y.val := Iff.rfl

/-! ### The complete lattice on `F↑`

`F↑` is closed under arbitrary ambient dioid `sSup` (`Fnondecr.sSup_mem`). Restricting that `sSup`
to the subtype is still the least upper bound, so `completeLatticeOfSup` produces the complete
lattice. Its top is `sSup univ`, which is `const0`. -/

/-- The supremum on `F↑` is the ambient `FunDioid` `sSup`, which stays in `Fnondecr`. -/
noncomputable instance : SupSet FNondecr :=
  ⟨fun S => mk (sSup ((·.val) '' S)) (Fnondecr.sSup_mem fun f hf => by
    obtain ⟨x, _, rfl⟩ := hf; exact x.property)⟩

@[simp] theorem val_sSup (S : Set FNondecr) : (sSup S).val = sSup ((·.val) '' S) := rfl

/-- The restricted `sSup` is the least upper bound in `F↑` (inherited from `FunDioid`). -/
theorem isLUB_sSup (S : Set FNondecr) : IsLUB S (sSup S) := by
  constructor
  · intro x hx
    rw [le_def, val_sSup]
    exact le_sSup ⟨x, hx, rfl⟩
  · intro b hb
    rw [le_def, val_sSup]
    refine sSup_le ?_
    rintro f ⟨x, hx, rfl⟩
    exact hb hx

noncomputable instance instCompleteLattice : CompleteLattice FNondecr :=
  completeLatticeOfSup FNondecr isLUB_sSup

/-- **The top element of `F↑` is the constant-`0` function** `const0` — the same adjusted top as
`F⁺`, since `const0` is non-decreasing as well as non-negative. -/
theorem top_eq_const0 : (⊤ : FNondecr).val = const0 := by
  -- `⊤ = sSup univ`; its value is the least upper bound of all of `F↑`, namely `const0`.
  have h : IsLUB (Set.univ : Set FNondecr) (⊤ : FNondecr) :=
    show IsLUB Set.univ (sSup Set.univ) from isLUB_sSup Set.univ
  refine le_antisymm ?_ ?_
  · -- `⊤ ≼ const0` since `const0 ∈ F↑` is an upper bound of `univ`.
    have hub : mk const0 ⟨const0_isNonneg, const0_isNondecr⟩ ∈ upperBounds (Set.univ : Set FNondecr) :=
      fun x _ => (le_def x _).mpr (val_le_const0 x)
    exact (le_def _ _).mp (h.2 hub)
  · -- `const0 ≼ ⊤` since `const0 ∈ F↑` and `⊤` bounds everything.
    exact (le_def (mk const0 ⟨const0_isNonneg, const0_isNondecr⟩) ⊤).mp le_top

theorem val_top : (⊤ : FNondecr).val = const0 := top_eq_const0

/-- The lattice join `⊔` on `F↑` (which is `sSup {x, y}`) restricts to the ambient join. -/
theorem val_sup (x y : FNondecr) : (x ⊔ y).val = x.val ⊔ y.val := by
  -- `completeLatticeOfSup` defines `x ⊔ y = sSup {x, y}`.
  show (sSup ({x, y} : Set FNondecr)).val = x.val ⊔ y.val
  rw [val_sSup, Set.image_pair, sSup_pair]

theorem val_biSup {ι : Sort*} (f : ι → FNondecr) (p : ι → Prop) :
    (⨆ i, ⨆ (_ : p i), f i).val = ⨆ i, ⨆ (_ : p i), (f i).val := by
  rw [iSup_subtype', iSup_subtype']
  rw [show (⨆ i : {i // p i}, f i.1) = sSup (Set.range fun i : {i // p i} => f i.1) from
    (sSup_range).symm, val_sSup, ← Set.range_comp, sSup_range]
  rfl

/-! ### The dioid operations on `F↑`

`F↑` is closed under `⊕` (`Fnondecr.inf_mem`), `⊗` (`Fnondecr.conv_mem`), and contains `𝟘 = ε`,
`𝟙 = e` (both non-negative and non-decreasing). All semiring laws are the ambient `FunDioid` ones
projected through `val`. -/

theorem zero_mem : (0 : FunDioid) ∈ Fnondecr := ⟨FPlus.zero_isNonneg, fun _ _ _ => le_rfl⟩
theorem one_mem : (1 : FunDioid) ∈ Fnondecr := ⟨FPlus.one_isNonneg, by
  intro x y hxy
  show (if x = 0 then (1 : RbarMin) else 0).toDual ≤ (if y = 0 then (1 : RbarMin) else 0).toDual
  by_cases hy : y = 0
  · -- `x ≤ y = 0` forces `x = 0`, so both values agree.
    rw [if_pos hy, if_pos (le_antisymm (hy ▸ hxy) (zero_le' (a := x)))]
  · rw [if_neg hy]; exact le_top⟩

noncomputable instance : Zero FNondecr := ⟨mk 0 zero_mem⟩
noncomputable instance : One FNondecr := ⟨mk 1 one_mem⟩
noncomputable instance : Add FNondecr :=
  ⟨fun x y => mk (x.val + y.val) (Fnondecr.inf_mem x.property y.property)⟩
noncomputable instance : Mul FNondecr :=
  ⟨fun x y => mk (x.val * y.val) (Fnondecr.conv_mem x.property y.property)⟩

@[simp] theorem val_zero : (0 : FNondecr).val = 0 := rfl
@[simp] theorem val_one : (1 : FNondecr).val = 1 := rfl
@[simp] theorem val_add (x y : FNondecr) : (x + y).val = x.val + y.val := rfl
@[simp] theorem val_mul (x y : FNondecr) : (x * y).val = x.val * y.val := rfl

/-- The idempotent scalar action stays in `F↑`: `n • f` is a finite dioid sum of `f` (or `ε`). -/
theorem nsmul_mem (n : ℕ) {f : FunDioid} (hf : f ∈ Fnondecr) : n • f ∈ Fnondecr := by
  induction n with
  | zero => rw [zero_smul]; exact zero_mem
  | succ k ih => rw [succ_nsmul]; exact Fnondecr.inf_mem ih hf

noncomputable instance : SMul ℕ FNondecr := ⟨fun n x => mk (n • x.val) (nsmul_mem n x.property)⟩

@[simp] theorem val_nsmul (n : ℕ) (x : FNondecr) : (n • x).val = n • x.val := rfl

/-- The natural-number cast stays in `F↑`: `↑n` is `ε` or `e`. -/
theorem natCast_mem (n : ℕ) : ((n : ℕ) : FunDioid) ∈ Fnondecr := by
  cases n with
  | zero => rw [Nat.cast_zero]; exact zero_mem
  | succ k => rw [Nat.cast_succ]; exact Fnondecr.inf_mem (natCast_mem k) one_mem

noncomputable instance : NatCast FNondecr := ⟨fun n => mk (n : FunDioid) (natCast_mem n)⟩

@[simp] theorem val_natCast (n : ℕ) : (NatCast.natCast n : FNondecr).val = (n : FunDioid) := rfl

/-- The (min,plus) commutative semiring on `F↑`, with every law inherited from `FunDioid`. -/
noncomputable instance commSemiring : CommSemiring FNondecr where
  add_assoc a b c := ext <| by rw [val_add, val_add, val_add, val_add, add_assoc]
  add_comm a b := ext <| by rw [val_add, val_add, add_comm]
  zero_add a := ext <| by rw [val_add, val_zero, zero_add]
  add_zero a := ext <| by rw [val_add, val_zero, add_zero]
  nsmul := (· • ·)
  nsmul_zero a := ext <| by rw [val_nsmul, val_zero, zero_smul]
  nsmul_succ n a := ext <| by rw [val_nsmul, val_add, val_nsmul, succ_nsmul]
  mul_assoc a b c := ext <| by rw [val_mul, val_mul, val_mul, val_mul, mul_assoc]
  mul_comm a b := ext <| by rw [val_mul, val_mul, mul_comm]
  one_mul a := ext <| by rw [val_mul, val_one, one_mul]
  mul_one a := ext <| by rw [val_mul, val_one, mul_one]
  zero_mul a := ext <| by rw [val_mul, val_zero, zero_mul]
  mul_zero a := ext <| by rw [val_mul, val_zero, mul_zero]
  natCast := fun n => (n : FNondecr)
  natCast_zero := ext <| by rw [val_natCast, val_zero, Nat.cast_zero]
  natCast_succ n := ext <| by rw [val_natCast, val_add, val_natCast, val_one, Nat.cast_succ]
  left_distrib a b c := ext <| by rw [val_mul, val_add, val_add, val_mul, val_mul, left_distrib]
  right_distrib a b c := ext <| by rw [val_mul, val_add, val_add, val_mul, val_mul, right_distrib]

/-- The dioid sum `⊕` on `F↑` is the lattice join `⊔`. -/
theorem add_eq_sup' (x y : FNondecr) : x + y = x ⊔ y :=
  ext (by rw [val_add, val_sup, FunDioid.add_eq_sup'])

/-- The (min,plus) **dioid** on `F↑`: the canonical order is the restriction of `FunDioid`'s. -/
noncomputable instance dioid : Dioid FNondecr :=
  { commSemiring, (inferInstance : CompleteLattice FNondecr) with
    add_eq_sup := add_eq_sup' }

/-- The dioid product `⊗` on `F↑` distributes over an arbitrary dioid `sSup`: the supremum
restricts to the ambient one (`val_sSup`), so this is `FunDioid.completeDioid.mul_sSup` projected. -/
theorem mul_sSup' (a : FNondecr) (S : Set FNondecr) : a * sSup S = ⨆ b ∈ S, a * b := by
  apply ext
  rw [val_mul, val_sSup, CompleteDioid.mul_sSup a.val ((·.val) '' S), iSup_image, val_biSup]
  exact iSup_congr fun b => iSup_congr fun _ => (val_mul a b).symm

/-- **`F↑` is a complete commutative dioid** (after Lemma 2.3), with the **same adjusted top
`const0`** as `F⁺`. -/
noncomputable instance completeDioid : CompleteDioid FNondecr :=
  { dioid, (inferInstance : CompleteLattice FNondecr) with
    mul_sSup := mul_sSup' }

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
