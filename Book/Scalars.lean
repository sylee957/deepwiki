import VersoManual
import Book.Dioids
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Ring.WithTop
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Hom.WithTopBot
import Mathlib.Algebra.Order.Monoid.Basic
import Mathlib.Order.CompleteLatticeIntervals
import Mathlib.Order.LatticeIntervals
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Push

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "The (min,plus) scalar dioids" =>
The scalar carriers of network calculus are obtained by _reversing_ the
numeric order. In a dioid the sum $`\oplus` is the lattice join and the
neutral $`\mathbf{0}` is the least element; choosing $`\oplus = \min` and $`\mathbf{0} = +\infty`
forces the canonical order $`a \preceq b \;:\Leftrightarrow\; \min(a, b) = b \iff b \le a` to be the
_reverse_ of the numeric order, with $`+\infty` as the bottom and the product
$`\otimes` ordinary addition with unit $`\mathbf{1} = 0`. This chapter exhibits three
concrete carriers as dioid instances.

# A reusable builder
All three carriers are the order-dual of a linearly ordered additive
monoid with a top, equipped with $`\oplus = \min` and $`\otimes = {+}`. That shared
construction is factored once. The class `MinPlus.Carrier` packages the
data for the _dioid_ layer: a `LinearOrder` with `OrderTop` and an
`AddCommMonoid` whose top is absorbing and whose addition is monotone.

```lean
namespace NetworkCalculus

open scoped Computability

namespace MinPlus

class Carrier (M : Type*) extends
    LinearOrder M, OrderTop M, AddCommMonoid M where
  /-- `⊤` (the dioid neutral `𝟘`) is absorbing
  for `+` (the dioid product). -/
  add_top' : ∀ a : M, a + ⊤ = ⊤
  /-- Addition is monotone (the product is
  isotone). -/
  add_le_add_left' :
    ∀ {a b : M}, a ≤ b → ∀ c : M, c + a ≤ c + b
```

The two derived monotonicity facts:

```lean
namespace Carrier
variable {M : Type*} [Carrier M]

theorem top_add' (a : M) : ⊤ + a = ⊤ := by
  rw [add_comm]; exact add_top' a

theorem add_le_add_right' {a b : M}
    (h : a ≤ b) (c : M) : a + c ≤ b + c := by
  rw [add_comm a, add_comm b]
  exact add_le_add_left' h c

end Carrier
```

The newtype `MinPlus.D M` wraps the underlying `M` and inherits _none_
of its algebra except the transported order; the dioid product $`\otimes` is
the only multiplication on it. The order on `D M` is the reverse of the
numeric order: `a ≤ b ↔ b.toDual ≤ a.toDual`, so $`\oplus = \min` is the join
and $`\mathbf{0} = \top` is the bottom.

```lean
structure D (M : Type*) where ofDual ::
  /-- The underlying element of `M` (reversed
  order). -/
  toDual : M

namespace D

/-- The defining equivalence `D M ≃ Mᵒᵈ`. -/
def toDualEquiv {M : Type*} : D M ≃ Mᵒᵈ :=
  ⟨fun x => OrderDual.toDual x.toDual,
   fun y => ⟨OrderDual.ofDual y⟩,
   fun ⟨_⟩ => rfl, fun _ => rfl⟩

theorem toDual_injective {M : Type*} :
    Function.Injective (toDual (M := M)) :=
  fun a b h => by cases a; cases b; cases h; rfl

@[simp] theorem ofDual_toDual {M : Type*}
    (a : D M) : D.ofDual a.toDual = a := rfl
@[simp] theorem toDual_ofDual {M : Type*}
    (a : M) : (D.ofDual a).toDual = a := rfl
```

The order/lattice on `D M` is transported from `Mᵒᵈ` through the
equivalence: its join $`\sqcup = \min` and its bottom $`\bot = \top`.

```lean
noncomputable instance instCompleteLattice
    {M : Type*} [CompleteLattice M] :
    CompleteLattice (D M) :=
  Equiv.completeLattice toDualEquiv

noncomputable instance instLattice
    {M : Type*} [Lattice M] : Lattice (D M) :=
  Equiv.lattice toDualEquiv

variable {M : Type*} [Carrier M]

/-- The canonical (reversed) order on `D M`. -/
theorem le_def (a b : D M) :
    a ≤ b ↔ b.toDual ≤ a.toDual := Iff.rfl

instance instOrderBot : OrderBot (D M) where
  bot := D.ofDual ⊤
  bot_le _ := (le_def _ _).mpr le_top
```

# The dioid operations
$`\oplus = \min`, $`\otimes = {+}`, $`\mathbf{0} = \top`, $`\mathbf{1} = 0`, plus the idempotent
`nsmul`/`natCast`.

```lean
/-- The dioid sum `⊕ = min`. -/
def add (a b : D M) : D M :=
  D.ofDual (min a.toDual b.toDual)
/-- The dioid product `⊗ = +`. -/
def mul (a b : D M) : D M :=
  D.ofDual (a.toDual + b.toDual)
/-- The additive neutral `𝟘 = ⊤`. -/
def zero : D M := D.ofDual ⊤
/-- The multiplicative neutral `𝟙 = 0`. -/
def one : D M := D.ofDual 0
/-- Idempotent scalar action. -/
def nsmul (n : ℕ) (a : D M) : D M :=
  D.ofDual (if n = 0 then ⊤ else a.toDual)
/-- The collapsed natural-number cast. -/
def natCast (n : ℕ) : D M :=
  D.ofDual (if n = 0 then ⊤ else (0 : M))
```

Each semiring law is a named theorem about these operations. $`\oplus = \min`
carries its commutative-monoid laws from $`\min` on `M`; $`\otimes = {+}` carries
its monoid laws from $`+`; $`\mathbf{0} = \top` is neutral for $`\min` and absorbing
for $`+`; the `nsmul`/`natCast` recursions collapse by idempotency of
$`\min`.

```lean
theorem add_assoc' (a b c : D M) :
    add (add a b) c = add a (add b c) :=
  toDual_injective (min_assoc _ _ _)

theorem add_comm' (a b : D M) :
    add a b = add b a :=
  toDual_injective (min_comm _ _)

theorem zero_add' (a : D M) : add zero a = a :=
  toDual_injective (min_eq_right le_top)

theorem add_zero' (a : D M) : add a zero = a :=
  toDual_injective (min_eq_left le_top)

theorem nsmul_zero' (a : D M) : nsmul 0 a = zero := by
  show D.ofDual (if (0 : ℕ) = 0 then ⊤ else _)
     = D.ofDual ⊤
  rw [if_pos rfl]

theorem nsmul_succ' (n : ℕ) (a : D M) :
    nsmul (n + 1) a = add (nsmul n a) a := by
  apply toDual_injective
  show (if n + 1 = 0 then ⊤ else a.toDual)
     = min (if n = 0 then ⊤ else a.toDual) a.toDual
  rw [if_neg (Nat.succ_ne_zero n)]
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; rw [if_pos rfl]
    exact (min_eq_right le_top).symm
  · rw [if_neg h.ne']; exact (min_self _).symm

theorem mul_assoc' (a b c : D M) :
    mul (mul a b) c = mul a (mul b c) :=
  toDual_injective (add_assoc _ _ _)

theorem mul_comm' (a b : D M) :
    mul a b = mul b a :=
  toDual_injective (add_comm _ _)

theorem one_mul' (a : D M) : mul one a = a :=
  toDual_injective (zero_add a.toDual)

theorem mul_one' (a : D M) : mul a one = a :=
  toDual_injective (add_zero a.toDual)

theorem zero_mul' (a : D M) : mul zero a = zero :=
  toDual_injective (Carrier.top_add' a.toDual)

theorem mul_zero' (a : D M) : mul a zero = zero :=
  toDual_injective (Carrier.add_top' a.toDual)

theorem natCast_zero' : (natCast 0 : D M) = zero := by
  show D.ofDual (if (0 : ℕ) = 0 then ⊤ else (0 : M))
     = D.ofDual ⊤
  rw [if_pos rfl]

theorem natCast_succ' (n : ℕ) :
    (natCast (n + 1) : D M) = add (natCast n) one := by
  apply toDual_injective
  show (if n + 1 = 0 then ⊤ else (0 : M))
     = min (if n = 0 then ⊤ else (0 : M)) (0 : M)
  rw [if_neg (Nat.succ_ne_zero n)]
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; rw [if_pos rfl]
    exact (min_eq_right le_top).symm
  · rw [if_neg h.ne']; exact (min_self _).symm
```

Distributivity of $`\otimes = {+}` over $`\oplus = \min` follows from monotonicity of
addition:

```lean
theorem left_distrib' (a b c : D M) :
    mul a (add b c) = add (mul a b) (mul a c) :=
  toDual_injective <|
    (Monotone.map_min
      (f := fun x : M => a.toDual + x)
      fun _ _ h => Carrier.add_le_add_left' h _)

theorem right_distrib' (a b c : D M) :
    mul (add a b) c = add (mul a c) (mul b c) :=
  toDual_injective <|
    (Monotone.map_min
      (f := fun x : M => x + c.toDual)
      fun _ _ h => Carrier.add_le_add_right' h _)
```

The `CommSemiring` instance is a flat assembly of these laws:

```lean
noncomputable instance commSemiring :
    CommSemiring (D M) where
  add := add
  add_assoc := add_assoc'
  add_comm := add_comm'
  zero := zero
  zero_add := zero_add'
  add_zero := add_zero'
  nsmul := nsmul
  nsmul_zero := nsmul_zero'
  nsmul_succ := nsmul_succ'
  mul := mul
  mul_assoc := mul_assoc'
  mul_comm := mul_comm'
  one := one
  one_mul := one_mul'
  mul_one := mul_one'
  zero_mul := zero_mul'
  mul_zero := mul_zero'
  natCast := natCast
  natCast_zero := natCast_zero'
  natCast_succ := natCast_succ'
  left_distrib := left_distrib'
  right_distrib := right_distrib'
```

The transported join $`\sqcup` equals $`\oplus = \min`, so the dioid sum is the
lattice join. This delivers the (min,plus) _dioid_ on `D M`:

```lean
theorem sup_eq_add (a b : D M) : a ⊔ b = add a b := rfl

theorem add_eq_sup' (a b : D M) : add a b = a ⊔ b :=
  (sup_eq_add a b).symm

noncomputable instance dioid : Dioid (D M) :=
  { commSemiring,
    (inferInstance : Lattice (D M)),
    (inferInstance : OrderBot (D M)) with
    add_eq_sup := add_eq_sup' }

end D
```

# The complete dioid carrier
`MinPlus.CompleteCarrier` adds a complete order and lower
semi-continuity of $`+`: addition distributes over arbitrary numeric
infima (`add_sInf'`). The field is phrased over a `Set M` so the class
stays in `M`'s single universe; the indexed `add_iInf'` form is derived.

```lean
class CompleteCarrier (M : Type*) extends
    Carrier M, CompleteLinearOrder M where
  /-- Lower semi-continuity: `+` distributes over
  the infimum of an arbitrary set. -/
  add_sInf' : ∀ (a : M) (s : Set M),
    (a + sInf s) = ⨅ b ∈ s, a + b

namespace CompleteCarrier
variable {M : Type*} [CompleteCarrier M]

theorem add_iInf' {ι : Sort*} (a : M) (f : ι → M) :
    (a + ⨅ i, f i) = ⨅ i, a + f i := by
  rw [iInf, add_sInf', iInf_range]

end CompleteCarrier
```

Transporting the bounded supremum on `D M` through the order dual turns
it into the numeric bounded infimum:

```lean
namespace D

variable {M : Type*}

theorem toDual_sSup_bdd [CompleteLattice M]
    (s : Set (D M)) :
    (sSup s).toDual = ⨅ a ∈ s, (a : D M).toDual := by
  show (toDualEquiv.symm
      (⨆ a ∈ s, toDualEquiv a)).toDual = _
  rfl

theorem toDual_iSup_eq [CompleteLattice M]
    {ι : Sort*} (g : ι → D M) :
    (⨆ i, g i).toDual = ⨅ i, (g i).toDual := by
  rw [iSup, toDual_sSup_bdd, iInf_range]

theorem toDual_sSup_eq [CompleteLattice M]
    (s : Set (D M)) :
    (sSup s).toDual = ⨅ b : s, (b : D M).toDual := by
  rw [toDual_sSup_bdd, iInf_subtype]

theorem toDual_biSup_eq [CompleteLattice M]
    (s : Set (D M)) (f : D M → D M) :
    (⨆ b ∈ s, f b).toDual
      = ⨅ b : s, (f (b : D M)).toDual := by
  rw [iSup_subtype']; exact toDual_iSup_eq _
```

The lower-semicontinuity field `mul_sSup` is the carrier's `add_iInf'`
transported through the order dual; it is given inline since the
higher-order rewrite only resolves with the field's expected type
guiding unification:

```lean
noncomputable instance completeDioid
    [CompleteCarrier M] : CompleteDioid (D M) :=
  { dioid,
    (inferInstance : CompleteLattice (D M)) with
    mul_sSup := fun a s => toDual_injective (by
      show a.toDual + (sSup s).toDual
         = (⨆ b ∈ s, a * b).toDual
      rw [toDual_sSup_eq, toDual_biSup_eq,
        CompleteCarrier.add_iInf']
      rfl) }

end D

end MinPlus
```

# `Rmin = ℝ ∪ {+∞}` is a dioid
`WithTop ℝ` is a (min,plus) dioid carrier: $`+\infty = \top` is absorbing for
$`+`, and addition is monotone.

```lean
noncomputable instance : MinPlus.Carrier (WithTop ℝ) where
  add_top' a := by simp
  add_le_add_left' h c := by gcongr
```

`Rmin` is then the (min,plus) dioid carried by `WithTop ℝ` under the
reversed order, with $`\oplus = \min`, $`\mathbf{0} = +\infty = \bot`, $`\otimes = {+}`, $`\mathbf{1} = 0`:

```lean
abbrev Rmin := MinPlus.D (WithTop ℝ)

noncomputable example : Dioid Rmin := inferInstance
```

It is the _non-complete_ layer: an idempotent commutative semiring with
the canonical order, but not a complete dioid. Indeed `WithTop ℝ` is not
a complete lattice ($`\mathbb{R}` is unbounded below), and adjoining $`-\infty` to fix
that would break lower semi-continuity. The canonical dioid order is
literally the reverse of the numeric order:

```lean
example (a b : Rmin) :
    a ≤ b ↔ b.toDual ≤ a.toDual := Iff.rfl
```

# `R⁺min = ℝ≥0 ∪ {+∞}` is complete
The canonical _complete_ (min,plus) dioid is $`R^+_{\min}`, carried by
Mathlib's `ENNReal` ($`\overline{\mathbb{R}}_{\ge 0}`). This carrier is the sweet spot: it is a
complete lattice ($`0 = \bot`, $`+\infty = \top`) and is $`-\infty`-free, so $`\mathbf{0} = +\infty`
stays absorbing and there are no $`(+\infty) + (-\infty)` indeterminate forms. The
single concrete input is `ENNReal.add_iInf`, the lower-semicontinuity
field.

```lean
open scoped ENNReal in
noncomputable instance :
    MinPlus.CompleteCarrier ℝ≥0∞ where
  add_top' a := by simp
  add_le_add_left' h c := by gcongr
  add_sInf' a s := by
    rw [sInf_eq_iInf, ENNReal.add_iInf]
    exact iInf_congr fun _ => ENNReal.add_iInf

open scoped ENNReal in
abbrev RplusMin := MinPlus.D ℝ≥0∞

noncomputable example :
    CompleteDioid RplusMin := inferInstance

example (a b : RplusMin) :
    a ≤ b ↔ b.toDual ≤ a.toDual := Iff.rfl
```

# `R̄min = ℝ ∪ {±∞}` is complete
We first make `Rmin` a dioid, then _complete_ it by adjoining a
top $`\top = -\infty`, giving $`\overline{R}_{\min}`. The decisive convention is

$$`(+\infty) + (-\infty) = +\infty, \quad\text{i.e.}\quad \varepsilon + \top = \varepsilon,`

so that the dioid zero $`\varepsilon = +\infty` stays _absorbing_ for the product
$`\otimes = {+}`. Mathlib's `WithTop (WithBot ℝ)` realizes exactly this: its
outer $`\top` is absorbing for $`+`, including $`\bot + \top = \top`. Here the
outer $`\top = +\infty` is the dioid zero $`\varepsilon`, the inner $`\bot = -\infty` is
the dioid top, and $`\otimes` is the `WithTop`/`WithBot` addition. This is
_not_ Mathlib's `EReal`, whose opposite convention $`(+\infty) + (-\infty) = -\infty`
would make $`\varepsilon` non-absorbing and break the dioid.

```lean
abbrev Rbar := WithTop (WithBot ℝ)

namespace Rbar

/-- Adding a fixed real `r` is an order iso of
`R̄min` (a shift). -/
noncomputable def shift (r : ℝ) : Rbar ≃o Rbar :=
  ((OrderIso.addLeft r).withBotCongr).withTopCongr

theorem shift_eq (r : ℝ) (x : Rbar) :
    shift r x = (((r : WithBot ℝ) : Rbar)) + x := by
  induction x using WithTop.recTopCoe with
  | top => simp [shift]
  | coe d =>
    induction d using WithBot.recBotCoe with
    | bot =>
      simp only [shift, OrderIso.withTopCongr_apply,
        WithTop.map_coe,
        OrderIso.withBotCongr_apply, WithBot.map_bot]
      rw [show ((⊥ : WithBot ℝ) : Rbar)
          = ((↑r : WithBot ℝ) : Rbar)
            + ((⊥ : WithBot ℝ) : Rbar) from ?_]
      · rfl
      · rw [← WithTop.coe_add, WithBot.add_bot]
    | coe s =>
      simp only [shift, OrderIso.withTopCongr_apply,
        WithTop.map_coe,
        OrderIso.withBotCongr_apply, WithBot.map_coe,
        OrderIso.addLeft_apply]
      rw [← WithTop.coe_add, ← WithBot.coe_add]
```

The heart of the construction is _lower semi-continuity of $`+`_:
addition distributes over an arbitrary infimum, true precisely because
$`+\infty = \top` is absorbing. The finite case uses the shift order-isomorphism
(which preserves infima); the $`\pm\infty` and empty-index cases are handled by
the absorbing top.

```lean
theorem add_iInf {ι : Sort*} (a : Rbar) (f : ι → Rbar) :
    (a + ⨅ i, f i) = ⨅ i, a + f i := by
  refine le_antisymm
    (le_iInf fun i => by gcongr; exact iInf_le _ i) ?_
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [iInf_of_empty]
  · induction a using WithTop.recTopCoe with
    | top => simp
    | coe b =>
      induction b using WithBot.recBotCoe with
      | coe r =>
        have hmap : (shift r) (⨅ i, f i)
            = ⨅ i, (shift r) (f i) :=
          OrderIso.map_iInf _ _
        simp only [shift_eq] at hmap
        exact hmap.ge
      | bot =>
        by_cases htop : (⨅ i, f i) = ⊤
        · have hall : ∀ i, f i = ⊤ := fun i =>
            top_le_iff.mp (htop ▸ iInf_le f i)
          simp only [hall, WithTop.add_top,
            ciInf_const, le_refl]
        · obtain ⟨c, hc⟩ :=
            Option.ne_none_iff_exists'.mp htop
          rw [show (⨅ i, f i) = (c : Rbar) from hc,
            ← WithTop.coe_add]
          have hex : ∃ j, f j ≠ ⊤ := by
            by_contra h
            push Not at h
            exact htop (by simp [h])
          obtain ⟨j, hj⟩ := hex
          rw [show ((⊥ : WithBot ℝ) + c : WithBot ℝ)
              = ⊥ from WithBot.bot_add c]
          refine iInf_le_of_le j ?_
          obtain ⟨d, hd⟩ :=
            Option.ne_none_iff_exists'.mp hj
          rw [show f j = (d : Rbar) from hd,
            ← WithTop.coe_add, WithBot.bot_add]

end Rbar
```

`WithTop (WithBot ℝ)` is therefore a complete (min,plus) carrier, and
$`\overline{R}_{\min}` is the dioid carried by it under the reversed order:

```lean
noncomputable instance :
    MinPlus.CompleteCarrier Rbar where
  add_top' a := by simp
  add_le_add_left' h c := by gcongr
  add_sInf' a s := by
    rw [sInf_eq_iInf, Rbar.add_iInf]
    exact iInf_congr fun _ => Rbar.add_iInf _ _

abbrev RbarMin := MinPlus.D Rbar
```

$`\overline{R}_{\min}` is therefore a complete commutative dioid with zero
$`\varepsilon = +\infty`, unit $`e = 0`, and top $`\top = -\infty`:

```lean
noncomputable example :
    CompleteDioid RbarMin := inferInstance

example (a b : RbarMin) :
    a ≤ b ↔ b.toDual ≤ a.toDual := Iff.rfl
```

# A sub-complete-dioid builder
Two function classes of the next chapter — $`\mathcal{F}^+` and $`\mathcal{F}^\uparrow` — are both
_sub-complete-dioids_ of an ambient complete dioid: subsets closed
under the dioid operations and under arbitrary dioid sums `sSup`, on
which the restricted structure is again a complete commutative dioid.
We factor that pattern out once. The closure data:

```lean
structure SubCompleteDioid (α : Type*)
    [CompleteDioid α] where
  /-- The underlying subset of `α`. -/
  carrier : Set α
  /-- The dioid zero `𝟘 = 0` lies in carrier. -/
  zero_mem : (0 : α) ∈ carrier
  /-- The dioid one `𝟙 = 1` lies in carrier. -/
  one_mem : (1 : α) ∈ carrier
  /-- Closed under the dioid sum `⊕ = (+)`. -/
  add_mem : ∀ {a b},
    a ∈ carrier → b ∈ carrier → a + b ∈ carrier
  /-- Closed under the dioid product `⊗ = (*)`. -/
  mul_mem : ∀ {a b},
    a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  /-- Closed under arbitrary dioid sums `sSup`. -/
  sSup_mem : ∀ {T : Set α},
    (∀ a ∈ T, a ∈ carrier) → sSup T ∈ carrier

namespace SubCompleteDioid

variable {α : Type*} [CompleteDioid α]
  (S : SubCompleteDioid α)

/-- The carrier as a subtype. -/
def Sub : Type _ := {a : α // a ∈ S.carrier}

/-- The underlying element of `α`. -/
def val (x : S.Sub) : α := x.1

theorem property (x : S.Sub) :
    x.val ∈ S.carrier := x.2

@[ext] theorem ext {x y : S.Sub}
    (h : x.val = y.val) : x = y := Subtype.ext h

/-- Package a carrier element as a sub-dioid one. -/
def pack (a : α) (ha : a ∈ S.carrier) : S.Sub :=
  ⟨a, ha⟩

@[simp] theorem val_pack (a : α)
    (ha : a ∈ S.carrier) :
    (S.pack a ha).val = a := rfl
```

Closure under `n • _` and `↑n` is _derived_ by induction from the sum
and the neutrals:

```lean
theorem nsmul_mem (n : ℕ) {a : α}
    (ha : a ∈ S.carrier) : n • a ∈ S.carrier := by
  induction n with
  | zero => rw [zero_nsmul]; exact S.zero_mem
  | succ k ih => rw [succ_nsmul]; exact S.add_mem ih ha

theorem natCast_mem (n : ℕ) :
    ((n : ℕ) : α) ∈ S.carrier := by
  cases n with
  | zero => rw [Nat.cast_zero]; exact S.zero_mem
  | succ k =>
    rw [Nat.cast_succ]
    exact S.add_mem (natCast_mem k) S.one_mem
```

The supremum is the ambient `sSup` restricted to the carrier; it is
still the least upper bound, so `completeLatticeOfSup` produces the
complete lattice. Its top is `sSup carrier` — the _adjusted top_.

```lean
instance instPartialOrder : PartialOrder S.Sub :=
  Subtype.partialOrder _

theorem le_def (x y : S.Sub) :
    x ≤ y ↔ x.val ≤ y.val := Iff.rfl

noncomputable instance instSupSet : SupSet S.Sub :=
  ⟨fun T => S.pack (sSup (S.val '' T))
    (S.sSup_mem fun a ha => by
      obtain ⟨x, _, rfl⟩ := ha; exact x.property)⟩

@[simp] theorem val_sSup (T : Set S.Sub) :
    (sSup T).val = sSup (S.val '' T) := rfl

theorem isLUB_sSup (T : Set S.Sub) :
    IsLUB T (sSup T) := by
  constructor
  · intro x hx
    rw [le_def, val_sSup]
    exact le_sSup ⟨x, hx, rfl⟩
  · intro b hb
    rw [le_def, val_sSup]
    refine sSup_le ?_
    rintro f ⟨x, hx, rfl⟩
    exact hb hx

noncomputable instance instCompleteLattice :
    CompleteLattice S.Sub :=
  completeLatticeOfSup S.Sub S.isLUB_sSup
```

The adjusted top: `⊤ = sSup univ`, whose value is the supremum of the
whole carrier, _not_ the ambient `⊤`. The join restricts to the
ambient join.

```lean
theorem val_top :
    (⊤ : S.Sub).val = sSup S.carrier := by
  show (sSup (Set.univ : Set S.Sub)).val
     = sSup S.carrier
  rw [val_sSup]
  congr 1
  apply Set.eq_of_subset_of_subset
  · rintro a ⟨x, _, rfl⟩; exact x.property
  · intro a ha
    exact ⟨S.pack a ha, Set.mem_univ _, rfl⟩

theorem val_sup (x y : S.Sub) :
    (x ⊔ y).val = x.val ⊔ y.val := by
  show (sSup ({x, y} : Set S.Sub)).val
     = x.val ⊔ y.val
  rw [val_sSup, Set.image_pair, sSup_pair]; rfl

theorem val_biSup {ι : Sort*}
    (f : ι → S.Sub) (p : ι → Prop) :
    (⨆ i, ⨆ (_ : p i), f i).val
      = ⨆ i, ⨆ (_ : p i), (f i).val := by
  rw [iSup_subtype', iSup_subtype']
  rw [show (⨆ i : {i // p i}, f i.1)
      = sSup (Set.range fun i : {i // p i} => f i.1)
      from (sSup_range).symm,
    val_sSup, ← Set.range_comp, sSup_range]
  rfl
```

Each operation is the ambient one applied through `val`, kept in the
carrier by the closure fields:

```lean
noncomputable instance instZero : Zero S.Sub :=
  ⟨S.pack 0 S.zero_mem⟩
noncomputable instance instOne : One S.Sub :=
  ⟨S.pack 1 S.one_mem⟩
noncomputable instance instAdd : Add S.Sub :=
  ⟨fun x y => S.pack (x.val + y.val)
    (S.add_mem x.property y.property)⟩
noncomputable instance instMul : Mul S.Sub :=
  ⟨fun x y => S.pack (x.val * y.val)
    (S.mul_mem x.property y.property)⟩
noncomputable instance instSMul : SMul ℕ S.Sub :=
  ⟨fun n x => S.pack (n • x.val)
    (S.nsmul_mem n x.property)⟩
noncomputable instance instNatCast : NatCast S.Sub :=
  ⟨fun n => S.pack (n : α) (S.natCast_mem n)⟩

@[simp] theorem val_zero : (0 : S.Sub).val = 0 := rfl
@[simp] theorem val_one : (1 : S.Sub).val = 1 := rfl
@[simp] theorem val_add (x y : S.Sub) :
    (x + y).val = x.val + y.val := rfl
@[simp] theorem val_mul (x y : S.Sub) :
    (x * y).val = x.val * y.val := rfl
@[simp] theorem val_nsmul (n : ℕ) (x : S.Sub) :
    (n • x).val = n • x.val := rfl
@[simp] theorem val_natCast (n : ℕ) :
    (NatCast.natCast n : S.Sub).val = (n : α) := rfl
```

The semiring, dioid and complete-dioid structures then project the
ambient laws through `val`:

```lean
noncomputable instance instCommSemiring :
    CommSemiring S.Sub where
  add_assoc a b c := S.ext <| by
    rw [val_add, val_add, val_add, val_add, add_assoc]
  add_comm a b := S.ext <| by
    rw [val_add, val_add, add_comm]
  zero_add a := S.ext <| by
    rw [val_add, val_zero, zero_add]
  add_zero a := S.ext <| by
    rw [val_add, val_zero, add_zero]
  nsmul := (· • ·)
  nsmul_zero a := S.ext <| by
    rw [val_nsmul, val_zero, zero_nsmul]
  nsmul_succ n a := S.ext <| by
    rw [val_nsmul, val_add, val_nsmul, succ_nsmul]
  mul_assoc a b c := S.ext <| by
    rw [val_mul, val_mul, val_mul, val_mul, mul_assoc]
  mul_comm a b := S.ext <| by
    rw [val_mul, val_mul, mul_comm]
  one_mul a := S.ext <| by
    rw [val_mul, val_one, one_mul]
  mul_one a := S.ext <| by
    rw [val_mul, val_one, mul_one]
  zero_mul a := S.ext <| by
    rw [val_mul, val_zero, zero_mul]
  mul_zero a := S.ext <| by
    rw [val_mul, val_zero, mul_zero]
  natCast := fun n => (n : S.Sub)
  natCast_zero := S.ext <| by
    rw [val_natCast, val_zero, Nat.cast_zero]
  natCast_succ n := S.ext <| by
    rw [val_natCast, val_add, val_natCast, val_one,
      Nat.cast_succ]
  left_distrib a b c := S.ext <| by
    rw [val_mul, val_add, val_add, val_mul, val_mul,
      left_distrib]
  right_distrib a b c := S.ext <| by
    rw [val_mul, val_add, val_add, val_mul, val_mul,
      right_distrib]

theorem add_eq_sup' (x y : S.Sub) : x + y = x ⊔ y :=
  S.ext (by rw [val_add, val_sup, add_eq_sup])

noncomputable instance instDioid : Dioid S.Sub :=
  { instCommSemiring S,
    (instCompleteLattice S : CompleteLattice S.Sub)
    with add_eq_sup := S.add_eq_sup' }

theorem mul_sSup' (a : S.Sub) (T : Set S.Sub) :
    a * sSup T = ⨆ b ∈ T, a * b := by
  apply S.ext
  rw [val_mul, val_sSup,
    CompleteDioid.mul_sSup a.val (S.val '' T),
    iSup_image, S.val_biSup]
  exact iSup_congr fun b =>
    iSup_congr fun _ => (val_mul S a b).symm

noncomputable instance instCompleteDioid :
    CompleteDioid S.Sub :=
  { instDioid S,
    (instCompleteLattice S : CompleteLattice S.Sub)
    with mul_sSup := S.mul_sSup' }

end SubCompleteDioid

end NetworkCalculus
```
