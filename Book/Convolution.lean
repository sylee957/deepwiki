import VersoManual
import Book.Scalars
import Mathlib.Data.NNReal.Basic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "The (min,plus) convolution and the function dioid" =>
This chapter formalizes the (min,plus) convolution, its algebraic
properties, and the resulting function dioid. The convolution $`\ast` is
defined generically over a complete dioid `α`; all of its core
properties hold at that generality, and the setting $`\mathcal{F} = \mathbb{R}^+ \to \overline{R}_{\min}` is
the specialization.

```lean
namespace NetworkCalculus

open scoped Computability NNReal
```

# The generic convolution
The convolution is defined over an arbitrary additive index monoid `T`
valued in an arbitrary complete dioid `α`. In the dioid interface the
sum $`\oplus` is $`\bigsqcup` and the product $`\otimes` is $`{*}`, so
$`\inf_{u+s=t} (f(u) + g(s))` becomes a least upper bound of products over
the decompositions of $`t`.

```lean
section Generic

/-- The (min,plus) convolution. -/
noncomputable def conv {T : Type*} [AddCommMonoid T]
    {α : Type*} [CompleteDioid α]
    (f g : T → α) : T → α :=
  fun t => ⨆ p : {p : T × T // p.1 + p.2 = t},
    f p.val.1 * g p.val.2

@[inherit_doc] scoped infixl:70 " ∗ " => conv

theorem conv_apply {T : Type*} [AddCommMonoid T]
    {α : Type*} [CompleteDioid α]
    (f g : T → α) (t : T) :
    (f ∗ g) t = ⨆ p : {p : T × T // p.1 + p.2 = t},
      f p.val.1 * g p.val.2 := rfl
```

The convolution is the least upper bound of the decomposition values,
$$`(f \ast g)(t) = \bigsqcup_{u+s=t} f(u) \otimes g(s) :`
every decomposition gives a lower bound (`conv_ge`), and it is below any
common upper bound (`conv_le`).

```lean
theorem conv_ge {T : Type*} [AddCommMonoid T]
    {α : Type*} [CompleteDioid α]
    (f g : T → α) {t u s : T}
    (h : u + s = t) : f u * g s ≤ (f ∗ g) t :=
  le_iSup (fun p : {p : T × T // p.1 + p.2 = t} =>
    f p.val.1 * g p.val.2) ⟨(u, s), h⟩

theorem conv_le {T : Type*} [AddCommMonoid T]
    {α : Type*} [CompleteDioid α]
    (f g : T → α) {t : T} {b : α}
    (h : ∀ u s, u + s = t → f u * g s ≤ b) :
    (f ∗ g) t ≤ b :=
  iSup_le fun p => h p.val.1 p.val.2 p.property

end Generic
```

# Properties of the convolution
Commutativity, associativity, distributivity over the dioid sum $`\oplus`,
and addition by a constant — all in the dioid order $`\preceq`, over an
arbitrary complete dioid.

```lean
section Generic
```

_Commutativity_ $`f \ast g = g \ast f` (reindex decompositions
$`(u,s) \mapsto (s,u)` and use commutativity of $`\otimes`):

```lean
theorem conv_comm {T : Type*} [AddCommMonoid T]
    {α : Type*} [CompleteDioid α]
    (f g : T → α) : f ∗ g = g ∗ f := by
  funext t
  apply le_antisymm
  · exact conv_le f g fun u s h => by
      rw [mul_comm]
      exact conv_ge g f (by rw [add_comm]; exact h)
  · exact conv_le g f fun u s h => by
      rw [mul_comm]
      exact conv_ge f g (by rw [add_comm]; exact h)
```

_Distributivity over the dioid sum_
$$`f \ast (g \oplus h) = (f \ast g) \oplus (f \ast h),`
where $`\oplus = \sqcup` (for $`\overline{R}_{\min}`, the pointwise minimum
$`\wedge`), from binary distributivity of $`\otimes` over $`\sqcup`:

```lean
theorem conv_sup {T : Type*} [AddCommMonoid T]
    {α : Type*} [CompleteDioid α] (f g h : T → α) :
    (f ∗ fun x => g x ⊔ h x)
      = fun t => (f ∗ g) t ⊔ (f ∗ h) t := by
  funext t
  rw [conv_apply, conv_apply, conv_apply,
    ← iSup_sup_eq]
  congr 1; funext p
  exact CompleteDioid.mul_sup _ _ _
```

_Addition by a constant_ $`(f \ast g) \otimes K = f \ast (g \otimes K)`
(the $`{+}\,K` is multiplication by the constant $`K \in \alpha`):

```lean
theorem conv_mul_const {T : Type*} [AddCommMonoid T]
    {α : Type*} [CompleteDioid α]
    (f g : T → α) (K : α) :
    (fun t => (f ∗ g) t * K)
      = f ∗ (fun s => g s * K) := by
  funext t
  rw [conv_apply, conv_apply, CompleteDioid.iSup_mul]
  congr 1; funext p
  rw [mul_assoc]
```

_Associativity_: both $`(f \ast g) \ast h` and $`f \ast (g \ast h)` equal
the ternary convolution
$$`\bigsqcup_{u+v+w=t} f(u) \otimes g(v) \otimes h(w);`
we bound each by the other via the symmetric ternary lower bounds.

```lean
theorem conv_conv_ge {T : Type*} [AddCommMonoid T]
    {α : Type*} [CompleteDioid α]
    (f g h : T → α) {t u v w : T}
    (e : u + v + w = t) :
    f u * g v * h w ≤ ((f ∗ g) ∗ h) t :=
  le_trans
    (Dioid.mul_le_mul_right'
      (conv_ge f g (u := u) (s := v) rfl) _)
    (conv_ge (f ∗ g) h (u := u + v) (s := w) e)

theorem le_conv_conv {T : Type*} [AddCommMonoid T]
    {α : Type*} [CompleteDioid α]
    (f g h : T → α) {t u v w : T}
    (e : u + (v + w) = t) :
    f u * (g v * h w) ≤ (f ∗ (g ∗ h)) t :=
  le_trans
    (Dioid.mul_le_mul_left'
      (conv_ge g h (u := v) (s := w) rfl) _)
    (conv_ge f (g ∗ h) (u := u) (s := v + w) e)

theorem conv_assoc {T : Type*} [AddCommMonoid T]
    {α : Type*} [CompleteDioid α] (f g h : T → α) :
    (f ∗ g) ∗ h = f ∗ (g ∗ h) := by
  funext t
  apply le_antisymm
  · apply conv_le
    intro a w haw
    rw [conv_apply (f := f) (g := g),
      CompleteDioid.iSup_mul]
    refine iSup_le fun p => ?_
    obtain ⟨⟨u, v⟩, huv⟩ := p
    rw [mul_assoc]
    refine le_conv_conv f g h
      (u := u) (v := v) (w := w) ?_
    rw [← add_assoc, huv, haw]
  · apply conv_le
    intro u b hub
    rw [conv_apply (f := g) (g := h),
      CompleteDioid.mul_iSup]
    refine iSup_le fun p => ?_
    obtain ⟨⟨v, w⟩, hvw⟩ := p
    rw [← mul_assoc]
    refine conv_conv_ge f g h
      (u := u) (v := v) (w := w) ?_
    rw [add_assoc, hvw, hub]

end Generic
```

# The (min,plus) functions
$`\mathcal{F}` is the set of functions from the non-negative reals
$`\mathbb{R}^+ = \mathbb{R}_{\ge 0}` into the complete (min,plus) dioid
$`\overline{R}_{\min}`:

```lean
abbrev F := ℝ≥0 → RbarMin
```

The $`0 \le s \le t` form re-indexes the convolution via
truncated subtraction on `ℝ≥0`:

```lean
theorem conv_eq_sub (f g : F) (t : ℝ≥0) :
    (f ∗ g) t
      = ⨆ s : {s : ℝ≥0 // s ≤ t},
          f (t - s.val) * g s.val := by
  apply le_antisymm
  · refine iSup_le fun p => ?_
    obtain ⟨⟨u, s⟩, hus⟩ := p
    refine le_iSup_of_le ⟨s, hus ▸ le_add_self⟩ ?_
    have hu : t - s = u := by
      rw [← hus, add_tsub_cancel_right]
    rw [hu]
  · refine iSup_le fun p => ?_
    obtain ⟨s, hs⟩ := p
    exact le_iSup_of_le
      ⟨(t - s, s), tsub_add_cancel_of_le hs⟩ le_rfl
```

# Bounds at zero
These bounds are stated in the _natural_ (numeric) order, which on
$`\overline{R}_{\min}` is the reverse of the dioid order $`\preceq`; we
express it directly on the underlying numeric values via `.toDual`. If
$`f(0) \le 0` then $`f \ast g \le g` pointwise (the decomposition
$`t = 0 + t` gives $`(f \ast g)(t) \le f(0) + g(t) \le g(t)`):

```lean
theorem conv_le_right_of_apply_zero_le {f g : F}
    (hf : (f 0).toDual ≤ 0) (t : ℝ≥0) :
    ((f ∗ g) t).toDual ≤ (g t).toDual :=
  calc ((f ∗ g) t).toDual
      ≤ (f 0 * g t).toDual := conv_ge f g (zero_add t)
    _ = (f 0).toDual + (g t).toDual := rfl
    _ ≤ 0 + (g t).toDual := by gcongr
    _ = (g t).toDual := zero_add _
```

If $`f(0) = 0` and $`g(0) = 0` then $`f \ast g \le f \wedge g`
pointwise: the decomposition $`t = t + 0` bounds it by $`f(t)`, and
$`t = 0 + t` by $`g(t)`.

```lean
theorem conv_le_inf_of_apply_zero {f g : F}
    (hf : (f 0).toDual = 0) (hg : (g 0).toDual = 0)
    (t : ℝ≥0) :
    ((f ∗ g) t).toDual
      ≤ min ((f t).toDual) ((g t).toDual) := by
  refine le_min ?_ ?_
  · calc ((f ∗ g) t).toDual
        ≤ (f t * g 0).toDual :=
          conv_ge f g (add_zero t)
      _ = (f t).toDual + (g 0).toDual := rfl
      _ = (f t).toDual := by rw [hg, add_zero]
  · calc ((f ∗ g) t).toDual
        ≤ (f 0 * g t).toDual :=
          conv_ge f g (zero_add t)
      _ = (f 0).toDual + (g t).toDual := rfl
      _ = (g t).toDual := by rw [hf, zero_add]
```

# The function dioid
Equipping $`\mathcal{F}` with the pointwise minimum $`\oplus = \wedge` and
the convolution $`\otimes = \ast` gives a _complete commutative dioid_. The
single piece of completeness content is lower semi-continuity of
$`\ast`: convolution distributes over an arbitrary _pointwise_ supremum
of functions in $`\mathcal{F}`.

```lean
theorem conv_iSup {ι : Sort*} (f : F) (g : ι → F) :
    (f ∗ ⨆ i, g i) = ⨆ i, (f ∗ g i) := by
  funext t
  rw [iSup_apply, conv_apply]
  calc
    (⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
        f p.val.1 * (⨆ i, g i) p.val.2)
        = ⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
            ⨆ i, f p.val.1 * g i p.val.2 := by
          refine iSup_congr fun p => ?_
          rw [iSup_apply, CompleteDioid.mul_iSup]
      _ = ⨆ i, ⨆ p :
            {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
            f p.val.1 * g i p.val.2 := iSup_comm
      _ = ⨆ i, (f ∗ g i) t := by
          refine iSup_congr fun i => ?_
          rw [conv_apply]
```

Since the bare function space already carries a pointwise product, the
construction wraps `F` in the newtype `FunDioid`, whose only
multiplication is convolution. The complete lattice is transported
pointwise from `F`, whose join $`\sqcup` is precisely the dioid sum
$`\wedge`.

```lean
structure FunDioid where ofFun ::
  /-- The underlying (min,plus) function in `F`. -/
  toFun : F

namespace FunDioid

/-- The defining equivalence `FunDioid ≃ F`. -/
def toFunEquiv : FunDioid ≃ F :=
  ⟨toFun, ofFun, fun ⟨_⟩ => rfl, fun _ => rfl⟩

theorem toFun_injective :
    Function.Injective toFun :=
  fun a b h => by cases a; cases b; cases h; rfl

@[simp] theorem ofFun_toFun (a : FunDioid) :
    FunDioid.ofFun a.toFun = a := rfl
@[simp] theorem toFun_ofFun (a : F) :
    (FunDioid.ofFun a).toFun = a := rfl

noncomputable instance instCompleteLattice :
    CompleteLattice FunDioid :=
  Equiv.completeLattice toFunEquiv

theorem le_def (a b : FunDioid) :
    a ≤ b ↔ a.toFun ≤ b.toFun := Iff.rfl
```

The dioid operations: $`\oplus = \wedge` (pointwise $`\overline{R}_{\min}`
sum), $`\otimes = \ast` (convolution), $`\mathbf{0} = \varepsilon`,
$`\mathbf{1} = e`, plus the idempotent `nsmul`/`natCast`.

```lean
/-- The dioid sum `⊕ = ∧`. -/
noncomputable def add (a b : FunDioid) : FunDioid :=
  FunDioid.ofFun (fun t => a.toFun t + b.toFun t)
/-- The dioid product `⊗ = ∗`: the convolution. -/
noncomputable def mul (a b : FunDioid) : FunDioid :=
  FunDioid.ofFun (a.toFun ∗ b.toFun)
/-- The additive neutral `𝟘 = ε : t ↦ +∞`. -/
noncomputable def zero : FunDioid :=
  FunDioid.ofFun (fun _ => (0 : RbarMin))
/-- The neutral `𝟙 = e : 0 ↦ 0, t > 0 ↦ +∞`. -/
noncomputable def one : FunDioid :=
  FunDioid.ofFun (fun t =>
    if t = 0 then (1 : RbarMin) else (0 : RbarMin))
/-- Idempotent scalar action. -/
noncomputable def nsmul (n : ℕ) (a : FunDioid) :
    FunDioid :=
  FunDioid.ofFun
    (if n = 0 then (fun _ => (0 : RbarMin))
      else a.toFun)
/-- The collapsed natural-number cast. -/
noncomputable def natCast (n : ℕ) : FunDioid :=
  FunDioid.ofFun
    (if n = 0 then (fun _ => (0 : RbarMin))
      else (fun t =>
        if t = 0 then (1 : RbarMin)
          else (0 : RbarMin)))
```

The semiring laws: $`\oplus = \wedge` carries its laws pointwise from
$`\overline{R}_{\min}`; $`\otimes = \ast` carries its monoid laws from
`conv_assoc`/`conv_comm`; $`\mathbf{0} = \varepsilon` is neutral for
$`\wedge` and absorbing for $`\ast`.

```lean
theorem add_assoc' (a b c : FunDioid) :
    add (add a b) c = add a (add b c) :=
  toFun_injective (funext fun _ => add_assoc _ _ _)

theorem add_comm' (a b : FunDioid) :
    add a b = add b a :=
  toFun_injective (funext fun _ => add_comm _ _)

theorem zero_add' (a : FunDioid) : add zero a = a :=
  toFun_injective (funext fun _ => zero_add _)

theorem add_zero' (a : FunDioid) : add a zero = a :=
  toFun_injective (funext fun _ => add_zero _)

theorem nsmul_zero' (a : FunDioid) :
    nsmul 0 a = zero := by
  apply toFun_injective
  show (if (0 : ℕ) = 0 then (fun _ => (0 : RbarMin))
      else a.toFun) = fun _ => (0 : RbarMin)
  rw [if_pos rfl]

theorem nsmul_succ' (n : ℕ) (a : FunDioid) :
    nsmul (n + 1) a = add (nsmul n a) a := by
  apply toFun_injective
  show (if n + 1 = 0 then (fun _ => (0 : RbarMin))
      else a.toFun)
     = fun t =>
        (if n = 0 then (fun _ => (0 : RbarMin))
          else a.toFun) t + a.toFun t
  rw [if_neg (Nat.succ_ne_zero n)]
  funext t
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; rw [if_pos rfl]; exact (zero_add _).symm
  · rw [if_neg h.ne']; exact (add_idem _).symm

theorem mul_assoc' (a b c : FunDioid) :
    mul (mul a b) c = mul a (mul b c) :=
  toFun_injective (conv_assoc _ _ _)

theorem mul_comm' (a b : FunDioid) :
    mul a b = mul b a :=
  toFun_injective (conv_comm _ _)

theorem one_mul' (a : FunDioid) : mul one a = a := by
  apply toFun_injective
  show one.toFun ∗ a.toFun = a.toFun
  funext t
  apply le_antisymm
  · apply conv_le
    intro u s hus
    by_cases hu : u = 0
    · subst hu; rw [zero_add] at hus; subst hus
      show (if (0 : ℝ≥0) = 0 then (1 : RbarMin)
          else 0) * a.toFun s ≤ a.toFun s
      rw [if_pos rfl, one_mul]
    · show (if u = 0 then (1 : RbarMin) else 0)
          * a.toFun s ≤ a.toFun t
      rw [if_neg hu, zero_mul]; exact bot_le
  · have := conv_ge one.toFun a.toFun
      (u := 0) (s := t) (zero_add t)
    show a.toFun t ≤ (one.toFun ∗ a.toFun) t
    have e : one.toFun 0 = 1 := if_pos rfl
    rw [e, one_mul] at this; exact this

theorem mul_one' (a : FunDioid) : mul a one = a := by
  rw [mul_comm']; exact one_mul' a

theorem zero_mul' (a : FunDioid) :
    mul zero a = zero := by
  apply toFun_injective
  show zero.toFun ∗ a.toFun = zero.toFun
  funext t
  apply le_antisymm
  · apply conv_le
    intro u s hus
    show (0 : RbarMin) * a.toFun s ≤ (0 : RbarMin)
    rw [zero_mul]
  · show zero.toFun t ≤ (zero.toFun ∗ a.toFun) t
    exact bot_le

theorem mul_zero' (a : FunDioid) :
    mul a zero = zero := by
  rw [mul_comm']; exact zero_mul' a

theorem natCast_zero' : (natCast 0 : FunDioid) = zero := by
  apply toFun_injective
  show (if (0 : ℕ) = 0 then (fun _ => (0 : RbarMin))
      else (fun _ => (1 : RbarMin)))
     = fun _ => (0 : RbarMin)
  rw [if_pos rfl]

theorem natCast_succ' (n : ℕ) :
    (natCast (n + 1) : FunDioid)
      = add (natCast n) one := by
  apply toFun_injective
  show (if n + 1 = 0 then (fun _ => (0 : RbarMin))
        else (fun t =>
          if t = 0 then (1 : RbarMin)
            else (0 : RbarMin)))
     = fun t =>
        (if n = 0 then (fun _ => (0 : RbarMin))
          else (fun t =>
            if t = 0 then (1 : RbarMin)
              else (0 : RbarMin))) t + one.toFun t
  rw [if_neg (Nat.succ_ne_zero n)]
  funext t
  show one.toFun t
     = (if n = 0 then (fun _ => (0 : RbarMin))
        else (fun t =>
          if t = 0 then (1 : RbarMin)
            else (0 : RbarMin))) t + one.toFun t
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; rw [if_pos rfl]; exact (zero_add _).symm
  · rw [if_neg h.ne']; exact (add_idem _).symm
```

Distributivity of $`\otimes = \ast` over $`\oplus = \wedge` is `conv_sup`
(the dioid sum is the pointwise $`\overline{R}_{\min}` sum $`= \sqcup`);
the right form follows by commutativity:

```lean
theorem left_distrib' (a b c : FunDioid) :
    mul a (add b c) = add (mul a b) (mul a c) := by
  apply toFun_injective
  show a.toFun ∗ (fun t => b.toFun t + c.toFun t)
     = fun t =>
        (a.toFun ∗ b.toFun) t
          + (a.toFun ∗ c.toFun) t
  simp_rw [add_eq_sup]
  exact conv_sup a.toFun b.toFun c.toFun

theorem right_distrib' (a b c : FunDioid) :
    mul (add a b) c = add (mul a c) (mul b c) := by
  rw [mul_comm', left_distrib',
    mul_comm' a c, mul_comm' b c]
```

The `CommSemiring`, `Dioid` and `CompleteDioid` structures assemble
these. The transported join is the pointwise $`\overline{R}_{\min}` join,
which equals the dioid sum $`\wedge`:

```lean
noncomputable instance commSemiring :
    CommSemiring FunDioid where
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

theorem add_eq_sup' (a b : FunDioid) :
    a + b = a ⊔ b := by
  apply toFun_injective
  show (fun t => a.toFun t + b.toFun t)
     = (a ⊔ b).toFun
  funext t
  show a.toFun t + b.toFun t = (a ⊔ b).toFun t
  rw [add_eq_sup]
  rfl

noncomputable instance dioid : Dioid FunDioid :=
  { commSemiring,
    (inferInstance : CompleteLattice FunDioid) with
    add_eq_sup := add_eq_sup' }
```

Completeness: the product $`\otimes = \ast` distributes over an arbitrary
dioid sum $`\bigsqcup`. The transported `sSup` on `FunDioid` is the
pointwise $`\overline{R}_{\min}` supremum, so this is `conv_iSup`
transported through the equivalence.

```lean
theorem mul_toFun (a b : FunDioid) :
    (a * b).toFun = a.toFun ∗ b.toFun := rfl

theorem toFun_sSup (s : Set FunDioid) :
    (sSup s).toFun
      = ⨆ a ∈ s, (a : FunDioid).toFun := rfl

theorem toFun_iSup {ι : Sort*} (g : ι → FunDioid) :
    (⨆ i, g i).toFun = ⨆ i, (g i).toFun := by
  rw [iSup, toFun_sSup, iSup_range]

noncomputable instance completeDioid :
    CompleteDioid FunDioid :=
  { dioid,
    (inferInstance : CompleteLattice FunDioid) with
    mul_sSup := fun a s => by
      apply toFun_injective
      rw [mul_toFun, toFun_sSup,
        ← iSup_subtype'' s
          (fun b : FunDioid => b.toFun),
        conv_iSup]
      rw [show (⨆ b ∈ s, a * b)
          = ⨆ b : s, a * (b : FunDioid) from
        (iSup_subtype'' s
          (fun b : FunDioid => a * b)).symm,
        toFun_iSup]
      refine iSup_congr fun b => ?_
      rw [mul_toFun] }

noncomputable example :
    CompleteDioid FunDioid := inferInstance
```

# Isotony
The isotony of $`\wedge` and $`\ast` is a direct consequence
of the dioid order relation — the generic dioid isotony specialized to
`FunDioid`:

```lean
theorem inf_le_inf_left' {f g : FunDioid}
    (h : f ≤ g) (k : FunDioid) : f + k ≤ g + k :=
  Dioid.add_le_add_right' h k

theorem conv_le_conv_right {f g : FunDioid}
    (h : f ≤ g) (k : FunDioid) : f * k ≤ g * k :=
  Dioid.mul_le_mul_right' h k

end FunDioid

end NetworkCalculus
```
