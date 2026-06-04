import VersoManual
import Book.CompleteDioids
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Ring.WithTop
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Hom.WithTopBot
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Push

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Scalar dioids" =>
The abstract dioid tower is realized by concrete number systems. This
chapter exhibits four. Three are _(min,plus)_, taking
$`\oplus = \min`, $`\otimes = {+}`, with the canonical order the
_reverse_ of the usual numeric order: the reals with $`+\infty`, a
dioid; the extended reals with $`\pm\infty`, a complete dioid; and the
_non-negative_ reals with $`+\infty`, also a complete dioid. The fourth
is the order-_dual_ _(max,plus)_ complete dioid on the non-negative
reals with $`\pm\infty`, taking $`\oplus = \max`, $`\otimes = {+}`,
with the canonical order _agreeing_ with the numeric one.

```lean
namespace VerifiedWiki

open scoped Algebra.Bridge
open scoped ENNReal NNReal Classical
```

# The carriers

Three concrete number systems realize the _(min,plus)_ tower, each
taking $`\oplus = \min`, $`\otimes = {+}`, sum neutral
$`\varepsilon = +\infty`, and product neutral $`e = 0`:

- the _reals with infinity_ $`\overline{\mathbb{R}}
  = \mathbb{R} \cup \{+\infty\}`, carried by `WithTop ℝ` — a dioid, but
  not complete (unbounded below);
- the _extended reals_ $`\overline{\mathbb{R}}
  = \mathbb{R} \cup \{\pm\infty\}`, carried by `WithTop (WithBot ℝ)`
  with the top-absorbing addition $`(+\infty) + (-\infty) = +\infty` — a
  complete dioid;
- the _non-negative reals_ $`\overline{\mathbb{R}}_{\ge 0}
  = \mathbb{R}_{\ge 0} \cup \{+\infty\}`, carried by `ℝ≥0∞` — the
  cleanest complete dioid, bounded below by $`0`.

A fourth carrier realizes the order-_dual_ _(max,plus)_ algebra, with
$`\oplus = \max`, $`\otimes = {+}`, sum neutral
$`\varepsilon = -\infty`, and product neutral $`e = 0`:

- the _non-negative reals with_ $`\pm\infty`, carried by `WithBot ℝ≥0∞`
  (so $`-\infty = \bot`) — a complete dioid whose canonical order
  _agrees_ with the numeric one.

Each numeric value is carried under a one-field wrapper, so the dioid
operations are attached freshly rather than colliding with any numeric
algebra already on the underlying type. For the _(min,plus)_ carriers
the canonical order $`a \preceq b \iff \min(a, b) = b` is the _reverse_
of the usual numeric order; for the _(max,plus)_ carrier
$`a \preceq b \iff \max(a, b) = b` _agrees_ with it.

*Definition:* the five carriers, each wrapping its number system

```lean
structure MinPlus where ofVal ::
  toVal : WithTop ℝ

structure MinPlusExt where ofVal ::
  toVal : WithTop (WithBot ℝ)

structure MinPlusNN where ofVal ::
  toVal : ℝ≥0∞

structure MaxPlusNN where ofVal ::
  toVal : WithBot ℝ≥0∞

structure MaxPlusExt where ofVal ::
  toVal : WithBot (WithTop ℝ)
```

Each wrapper gets a coercion to its underlying value and an
extensionality lemma lifting equality through it.

```lean
namespace MinPlus
instance : Coe MinPlus (WithTop ℝ) := ⟨toVal⟩
@[ext] theorem ext {a b : MinPlus}
    (h : (a : WithTop ℝ) = b) : a = b := by
  cases a; cases b; exact congrArg ofVal h
end MinPlus

namespace MinPlusExt
instance : Coe MinPlusExt (WithTop (WithBot ℝ)) := ⟨toVal⟩
@[ext] theorem ext {a b : MinPlusExt}
    (h : (a : WithTop (WithBot ℝ)) = b) : a = b := by
  cases a; cases b; exact congrArg ofVal h
end MinPlusExt

namespace MinPlusNN
instance : Coe MinPlusNN ℝ≥0∞ := ⟨toVal⟩
@[ext] theorem ext {a b : MinPlusNN}
    (h : (a : ℝ≥0∞) = b) : a = b := by
  cases a; cases b; exact congrArg ofVal h
end MinPlusNN

namespace MaxPlusNN
instance : Coe MaxPlusNN (WithBot ℝ≥0∞) := ⟨toVal⟩
@[ext] theorem ext {a b : MaxPlusNN}
    (h : (a : WithBot ℝ≥0∞) = b) : a = b := by
  cases a; cases b; exact congrArg ofVal h
end MaxPlusNN

namespace MaxPlusExt
instance : Coe MaxPlusExt (WithBot (WithTop ℝ)) := ⟨toVal⟩
@[ext] theorem ext {a b : MaxPlusExt}
    (h : (a : WithBot (WithTop ℝ)) = b) : a = b := by
  cases a; cases b; exact congrArg ofVal h
end MaxPlusExt
```

# The reals with infinity

The abstract tower is realized by the _(min,plus)_ algebra on
$`\overline{\mathbb{R}} = \mathbb{R} \cup \{+\infty\}`. The dioid sum is
the numeric _minimum_, the product is numeric _addition_, the sum
neutral is $`+\infty` (absorbing for $`\min`, since $`\min(+\infty, a)
= a` forces nothing larger), and the product neutral is $`0`. The
canonical order $`a \preceq b \iff \min(a, b) = b` is then the _reverse_
of the usual numeric order.

The carrier `MinPlus` wraps `WithTop ℝ` (with $`+\infty = \top`), so the
dioid operations are attached freshly rather than colliding with any
numeric algebra on `WithTop ℝ`.

## The carrier and its dioid

Two arithmetic facts on `WithTop ℝ` carry the distributive laws:
addition distributes over the minimum on each side, because addition is
monotone.

*Theorem:* $`a + \min(b, c) = \min(a + b, a + c)` and $`\min(a, b) + c = \min(a + c, b + c)`

```lean
namespace MinPlusAux

theorem add_min (a b c : WithTop ℝ) :
    a + min b c = min (a + b) (a + c) := by
  rcases le_total b c with h | h
  · rw [min_eq_left h, min_eq_left (by gcongr)]
  · rw [min_eq_right h, min_eq_right (by gcongr)]

theorem min_add (a b c : WithTop ℝ) :
    min a b + c = min (a + c) (b + c) := by
  rw [add_comm, add_min, add_comm a c, add_comm b c]

end MinPlusAux
```

Each dioid axiom is a fact about `WithTop ℝ`, lifted through the wrapper
by `ext`: the monoid laws from `min` and `+`, the distributive laws from
`MinPlusAux.add_min`/`MinPlusAux.min_add`, absorption of $`+\infty`, and
idempotency of $`\min`. The operations use the $`\uparrow` coercion to
the underlying value.

*Definition:* $`\overline{\mathbb{R}}` is an `Algebra.Dioid` with $`\oplus = \min`, $`\otimes = {+}`, $`\varepsilon = +\infty`, $`e = 0`

```lean
namespace MinPlus
open Algebra

instance : Algebra.Dioid MinPlus where
  add a b := ⟨min ↑a ↑b⟩
  zero := ⟨⊤⟩
  mul a b := ⟨↑a + ↑b⟩
  one := ⟨0⟩
  oplus_assoc _ _ _ := ext (min_assoc _ _ _)
  eps_oplus _ := ext (min_eq_right le_top)
  oplus_eps _ := ext (min_eq_left le_top)
  oplus_comm _ _ := ext (min_comm _ _)
  otimes_assoc _ _ _ := ext (add_assoc _ _ _)
  one_otimes _ := ext (zero_add _)
  otimes_one _ := ext (add_zero _)
  left_distrib _ _ _ := ext (MinPlusAux.add_min _ _ _)
  right_distrib _ _ _ := ext (MinPlusAux.min_add _ _ _)
  eps_otimes _ := ext (WithTop.top_add _)
  otimes_eps _ := ext (WithTop.add_top _)
  otimes_comm _ _ := ext (add_comm _ _)
  oplus_idem _ := ext (min_self _)

end MinPlus
```

## The canonical order

The dioid order on the wrapper is the reverse of the numeric order.

*Theorem:* $`a \preceq b \iff \uparrow b \le \uparrow a`

```lean
namespace MinPlus

theorem le_iff (a b : MinPlus) :
    a ≼ₒ b ↔ (b : WithTop ℝ) ≤ a := by
  have h1 : a ≼ₒ b
      ↔ (⟨min ↑a ↑b⟩ : MinPlus) = b := Iff.rfl
  rw [h1]
  constructor
  · intro h
    have : min (↑a : WithTop ℝ) ↑b = ↑b :=
      congrArg toVal h
    rw [← this]; exact min_le_left _ _
  · intro h; exact ext (min_eq_right h)

end MinPlus
```

## Worked arithmetic

In the _(min,plus)_ reading the dioid sum $`\oplus` is the minimum and
the dioid product $`\otimes` is numeric addition.

The four essential arithmetic cases of $`\overline{\mathbb{R}}`:

```lean
namespace MinPlus
open Algebra
```

*Theorem:* finite $`\wedge` finite stays in $`\mathbb{R}`

```lean
example (x y : ℝ) :
    ∃ z : ℝ, (⟨x⟩ : MinPlus) ⊕ₒ ⟨y⟩ = ⟨z⟩ :=
  ⟨min x y, rfl⟩
```

*Theorem:* $`a \wedge {+\infty} = a`

```lean
example (a : MinPlus) :
    a ⊕ₒ ⟨⊤⟩ = a := add_zero a
```

*Theorem:* finite $`+` finite stays in $`\mathbb{R}`

```lean
example (x y : ℝ) :
    ∃ z : ℝ, (⟨x⟩ : MinPlus) ⊗ₒ ⟨y⟩ = ⟨z⟩ :=
  ⟨x + y, rfl⟩
```

*Theorem:* $`a + {+\infty} = {+\infty}` ($`+\infty` absorbing)

```lean
example (a : MinPlus) :
    a ⊗ₒ ⟨⊤⟩ = ⟨⊤⟩ := mul_zero a

end MinPlus
```

Because the instance is found by resolution, every result of the tower
— the order $`\preceq`, its reflexivity, transitivity, antisymmetry,
and the isotony of $`\oplus` and $`\otimes` — now holds for
$`\overline{\mathbb{R}}` with no further work.

*Theorem:* $`a \preceq a` on $`\overline{\mathbb{R}}`

```lean
example (a : MinPlus) :
    a ≼ₒ a :=
  le_rfl
```

# The extended reals

The carrier $`\overline{\mathbb{R}} = \mathbb{R} \cup \{+\infty\}` is
_not_ complete: it is unbounded below, so a set of reals decreasing
without bound has no infimum inside it, and the dioid supremum (the
numeric infimum, since the order is reversed) is undefined. Adjoining
$`-\infty` repairs this. The _extended reals_ $`\overline{\mathbb{R}}
= \mathbb{R} \cup \{\pm\infty\}` form a complete lattice, and with the
top-absorbing addition $`(+\infty) + (-\infty) = +\infty` — which keeps
$`+\infty = \varepsilon` absorbing for $`\otimes` — they carry a
_complete_ (min,plus) dioid.

The carrier `MinPlusExt` wraps `WithTop (WithBot ℝ)`, so that
$`+\infty = \top` and $`-\infty = \bot`, with the top-absorbing
addition built in.

## The carrier and its dioid

The crux is _lower semi-continuity_ of $`+`: addition distributes over
an arbitrary infimum. The proof translates by a fixed real through an
order isomorphism (a shift), reducing the general case to the
finite, $`-\infty`, and $`+\infty` cases.

*Definition:* the shift $`x \mapsto r + x`, an order isomorphism

```lean
namespace RbarX

noncomputable def shift (r : ℝ) :
    WithTop (WithBot ℝ) ≃o WithTop (WithBot ℝ) :=
  ((OrderIso.addLeft r).withBotCongr).withTopCongr
```

*Theorem:* $`\mathtt{shift}\,r\,(x) = r + x`

```lean
theorem shift_eq (r : ℝ) (x : WithTop (WithBot ℝ)) :
    shift r x
      = (((r : WithBot ℝ) : WithTop (WithBot ℝ)))
        + x := by
  induction x using WithTop.recTopCoe with
  | top => simp [shift]
  | coe d =>
    induction d using WithBot.recBotCoe with
    | bot =>
      simp only [shift, OrderIso.withTopCongr_apply,
        WithTop.map_coe, OrderIso.withBotCongr_apply,
        WithBot.map_bot]
      rw [show ((⊥ : WithBot ℝ)
            : WithTop (WithBot ℝ))
          = ((↑r : WithBot ℝ)
              : WithTop (WithBot ℝ))
            + ((⊥ : WithBot ℝ)
                : WithTop (WithBot ℝ)) from ?_]
      · rfl
      · rw [← WithTop.coe_add, WithBot.add_bot]
    | coe s =>
      simp only [shift, OrderIso.withTopCongr_apply,
        WithTop.map_coe, OrderIso.withBotCongr_apply,
        WithBot.map_coe, OrderIso.addLeft_apply]
      rw [← WithTop.coe_add, ← WithBot.coe_add]
```

*Theorem:* $`a + \bigwedge_i f(i) = \bigwedge_i (a + f(i))`

```lean
theorem add_iInf {ι : Sort*} (a : WithTop (WithBot ℝ))
    (f : ι → WithTop (WithBot ℝ)) :
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
          rw [show (⨅ i, f i)
              = (c : WithTop (WithBot ℝ)) from hc,
            ← WithTop.coe_add]
          have hex : ∃ j, f j ≠ ⊤ := by
            by_contra h; push Not at h
            exact htop (by simp [h])
          obtain ⟨j, hj⟩ := hex
          rw [show ((⊥ : WithBot ℝ) + c : WithBot ℝ)
              = ⊥ from WithBot.bot_add c]
          refine iInf_le_of_le j ?_
          obtain ⟨d, hd⟩ :=
            Option.ne_none_iff_exists'.mp hj
          rw [show f j
              = (d : WithTop (WithBot ℝ)) from hd,
            ← WithTop.coe_add, WithBot.bot_add]
```

The two distributive facts about $`\min` and $`+` carry the dioid
distributive laws, as before.

*Theorem:* $`a + \min(b, c) = \min(a + b, a + c)` and $`\min(a, b) + c = \min(a + c, b + c)`

```lean
theorem add_min (a b c : WithTop (WithBot ℝ)) :
    a + min b c = min (a + b) (a + c) := by
  rcases le_total b c with h | h
  · rw [min_eq_left h, min_eq_left (by gcongr)]
  · rw [min_eq_right h, min_eq_right (by gcongr)]

theorem min_add (a b c : WithTop (WithBot ℝ)) :
    min a b + c = min (a + c) (b + c) := by
  rw [add_comm, add_min, add_comm a c, add_comm b c]

end RbarX
```

The complete (min,plus) carrier `MinPlusExt` wraps `WithTop (WithBot ℝ)`,
with the dioid sum the numeric minimum and the product numeric addition.

*Definition:* $`\overline{\mathbb{R}}` is an `Algebra.Dioid` with $`\oplus = \min`, $`\otimes = {+}`, $`\varepsilon = +\infty`, $`e = 0`

```lean
namespace MinPlusExt

instance : Algebra.Dioid MinPlusExt where
  add a b := ⟨min ↑a ↑b⟩
  zero := ⟨⊤⟩
  mul a b := ⟨↑a + ↑b⟩
  one := ⟨0⟩
  oplus_assoc _ _ _ := ext (min_assoc _ _ _)
  eps_oplus _ := ext (min_eq_right le_top)
  oplus_eps _ := ext (min_eq_left le_top)
  oplus_comm _ _ := ext (min_comm _ _)
  otimes_assoc _ _ _ := ext (add_assoc _ _ _)
  one_otimes _ := ext (zero_add _)
  otimes_one _ := ext (add_zero _)
  left_distrib _ _ _ := ext (RbarX.add_min _ _ _)
  right_distrib _ _ _ := ext (RbarX.min_add _ _ _)
  eps_otimes _ := ext (WithTop.top_add _)
  otimes_eps _ := ext (WithTop.add_top _)
  otimes_comm _ _ := ext (add_comm _ _)
  oplus_idem _ := ext (min_self _)
```

## The canonical order

The dioid order on the wrapper is the reverse of the numeric order.

*Theorem:* $`a \preceq b \iff \uparrow b \le \uparrow a`

```lean
theorem le_iff (a b : MinPlusExt) :
    a ≼ₒ b ↔ (b : WithTop (WithBot ℝ)) ≤ a := by
  have h1 : a ≼ₒ b
      ↔ (⟨min ↑a ↑b⟩ : MinPlusExt) = b := Iff.rfl
  rw [h1]
  constructor
  · intro h
    have : min (↑a : WithTop (WithBot ℝ)) ↑b = ↑b :=
      congrArg toVal h
    rw [← this]; exact min_le_left _ _
  · intro h; exact ext (min_eq_right h)
```

The dioid supremum is the numeric infimum of the underlying values.
Membership and least-upper-bound for $`\preceq` reduce to the numeric
greatest-lower-bound, and lower semi-continuity is `RbarX.add_iInf`.

*Definition:* $`\overline{\mathbb{R}}` is an `Algebra.CompleteDioid` with $`\bigsqcup s = \inf\,\{\,\uparrow x \mid x \in s\,\}`

```lean
noncomputable instance :
    Algebra.CompleteDioid MinPlusExt where
  iSup f := ⟨⨅ i, ↑(f i)⟩
  le_iSup f i := (le_iff _ _).mpr (iInf_le _ i)
  iSup_le f b hb := (le_iff _ _).mpr (le_iInf (by
    intro i
    exact (le_iff _ _).mp (hb i)))
  mul_iSup a f := by
    refine ext ?_
    show (↑a : WithTop (WithBot ℝ)) + ⨅ i, ↑(f i)
       = ⨅ i, ((↑a : WithTop (WithBot ℝ)) + ↑(f i))
    exact RbarX.add_iInf _ _

end MinPlusExt
```

So $`\overline{\mathbb{R}}` realizes the _complete_ dioid: every set
has a dioid supremum (its numeric infimum), and the product is lower
semi-continuous. The top element $`\top = \bigsqcup_x x` and its
absorbing laws, and the whole order theory, follow from the tower.

## Worked arithmetic

The four essential arithmetic cases of
$`\overline{\mathbb{R}} = \mathbb{R} \cup \{\pm\infty\}`:

```lean
namespace MinPlusExt
open Algebra
```

*Theorem:* finite $`\wedge` finite stays in $`\mathbb{R}`

```lean
example (x y : ℝ) :
    ∃ z : ℝ, (⟨↑↑x⟩ : MinPlusExt) ⊕ₒ ⟨↑↑y⟩
      = ⟨↑↑z⟩ :=
  ⟨min x y, by
    refine ext ?_
    show min (↑↑x : WithTop (WithBot ℝ)) ↑↑y
        = ↑↑(min x y)
    rw [WithBot.coe_min, WithTop.coe_min]⟩
```

*Theorem:* $`a \wedge {+\infty} = a`

```lean
example (a : MinPlusExt) :
    a ⊕ₒ ⟨⊤⟩ = a := add_zero a
```

*Theorem:* finite $`+` finite stays in $`\mathbb{R}`

```lean
example (x y : ℝ) :
    ∃ z : ℝ, (⟨↑↑x⟩ : MinPlusExt) ⊗ₒ ⟨↑↑y⟩
      = ⟨↑↑z⟩ :=
  ⟨x + y, by
    refine ext ?_
    show (↑↑x : WithTop (WithBot ℝ)) + ↑↑y
        = ↑↑(x + y)
    rw [WithBot.coe_add, WithTop.coe_add]⟩
```

*Theorem:* $`a + {+\infty} = {+\infty}` ($`+\infty` absorbing)

```lean
example (a : MinPlusExt) :
    a ⊗ₒ ⟨⊤⟩ = ⟨⊤⟩ := mul_zero a

end MinPlusExt
```

# The non-negative reals

The non-negative extended reals $`\overline{\mathbb{R}}_{\ge 0}
= \mathbb{R}_{\ge 0} \cup \{+\infty\}` are the cleanest complete
(min,plus) carrier. Being bounded below by $`0`, they form a complete
lattice with $`0 = \bot` and $`+\infty = \top` and no $`-\infty`, so
$`+\infty = \varepsilon` stays absorbing and there are no
$`(+\infty) + (-\infty)` indeterminacies. The carrier `MinPlusNN` wraps
Mathlib's $`\mathbb{R}_{\ge 0}^{\infty}` (`ℝ≥0∞`), whose lower
semi-continuity of $`+` is available off the shelf.

## The carrier and its dioid

The two distributive facts and lower semi-continuity, on `ℝ≥0∞`.

*Theorem:* $`a + \min(b, c) = \min(a + b, a + c)`, $`\min(a, b) + c = \min(a + c, b + c)`, and $`a + \bigwedge_i f(i) = \bigwedge_i (a + f(i))`

```lean
namespace RplusX

theorem add_min (a b c : ℝ≥0∞) :
    a + min b c = min (a + b) (a + c) := by
  rcases le_total b c with h | h
  · rw [min_eq_left h, min_eq_left (by gcongr)]
  · rw [min_eq_right h, min_eq_right (by gcongr)]

theorem min_add (a b c : ℝ≥0∞) :
    min a b + c = min (a + c) (b + c) := by
  rw [add_comm, add_min, add_comm a c, add_comm b c]

theorem add_iInf {ι : Sort*} (a : ℝ≥0∞) (f : ι → ℝ≥0∞) :
    a + ⨅ i, f i = ⨅ i, a + f i := ENNReal.add_iInf

end RplusX
```

*Definition:* $`\overline{\mathbb{R}}_{\ge 0}` is an `Algebra.Dioid` with $`\oplus = \min`, $`\otimes = {+}`, $`\varepsilon = +\infty`, $`e = 0`

```lean
namespace MinPlusNN

instance : Algebra.Dioid MinPlusNN where
  add a b := ⟨min ↑a ↑b⟩
  zero := ⟨⊤⟩
  mul a b := ⟨↑a + ↑b⟩
  one := ⟨0⟩
  oplus_assoc _ _ _ := ext (min_assoc _ _ _)
  eps_oplus _ := ext (min_eq_right le_top)
  oplus_eps _ := ext (min_eq_left le_top)
  oplus_comm _ _ := ext (min_comm _ _)
  otimes_assoc _ _ _ := ext (add_assoc _ _ _)
  one_otimes _ := ext (zero_add _)
  otimes_one _ := ext (add_zero _)
  left_distrib _ _ _ := ext (RplusX.add_min _ _ _)
  right_distrib _ _ _ := ext (RplusX.min_add _ _ _)
  eps_otimes _ := ext (WithTop.top_add _)
  otimes_eps _ := ext (WithTop.add_top _)
  otimes_comm _ _ := ext (add_comm _ _)
  oplus_idem _ := ext (min_self _)
```

## The canonical order

The dioid order on the wrapper is the reverse of the numeric order.

*Theorem:* $`a \preceq b \iff \uparrow b \le \uparrow a`

```lean
theorem le_iff (a b : MinPlusNN) :
    a ≼ₒ b ↔ (b : ℝ≥0∞) ≤ a := by
  have h1 : a ≼ₒ b
      ↔ (⟨min ↑a ↑b⟩ : MinPlusNN) = b := Iff.rfl
  rw [h1]
  constructor
  · intro h
    have : min (↑a : ℝ≥0∞) ↑b = ↑b := congrArg toVal h
    rw [← this]; exact min_le_left _ _
  · intro h; exact ext (min_eq_right h)
```

*Definition:* $`\overline{\mathbb{R}}_{\ge 0}` is an `Algebra.CompleteDioid` with $`\bigsqcup s = \inf\,\{\,\uparrow x \mid x \in s\,\}`

```lean
noncomputable instance :
    Algebra.CompleteDioid MinPlusNN where
  iSup f := ⟨⨅ i, ↑(f i)⟩
  le_iSup f i := (le_iff _ _).mpr (iInf_le _ i)
  iSup_le f b hb := (le_iff _ _).mpr (le_iInf (by
    intro i
    exact (le_iff _ _).mp (hb i)))
  mul_iSup a f := by
    refine ext ?_
    show (↑a : ℝ≥0∞) + ⨅ i, ↑(f i)
       = ⨅ i, ((↑a : ℝ≥0∞) + ↑(f i))
    exact RplusX.add_iInf _ _

end MinPlusNN
```

Of the three carriers, $`\overline{\mathbb{R}}_{\ge 0}` is the
canonical complete (min,plus) dioid: complete and free of the sign
pathologies, with lower semi-continuity inherited directly from
$`\mathbb{R}_{\ge 0}^{\infty}`.

## Worked arithmetic

The four essential arithmetic cases of
$`\overline{\mathbb{R}}_{\ge 0} = \mathbb{R}_{\ge 0} \cup \{+\infty\}`:

```lean
namespace MinPlusNN
open Algebra
```

*Theorem:* finite $`\wedge` finite stays in $`\mathbb{R}_{\ge 0}`

```lean
example (x y : ℝ≥0) :
    ∃ z : ℝ≥0, (⟨↑x⟩ : MinPlusNN) ⊕ₒ ⟨↑y⟩
      = ⟨↑z⟩ :=
  ⟨min x y, by
    refine ext ?_
    show min (↑x : ℝ≥0∞) ↑y = ↑(min x y)
    rw [ENNReal.coe_min]⟩
```

*Theorem:* $`a \wedge {+\infty} = a`

```lean
example (a : MinPlusNN) :
    a ⊕ₒ ⟨⊤⟩ = a := add_zero a
```

*Theorem:* finite $`+` finite stays in $`\mathbb{R}_{\ge 0}`

```lean
example (x y : ℝ≥0) :
    ∃ z : ℝ≥0, (⟨↑x⟩ : MinPlusNN) ⊗ₒ ⟨↑y⟩
      = ⟨↑z⟩ :=
  ⟨x + y, by
    refine ext ?_
    show (↑x : ℝ≥0∞) + ↑y = ↑(x + y)
    rw [ENNReal.coe_add]⟩
```

*Theorem:* $`a + {+\infty} = {+\infty}` ($`+\infty` absorbing)

```lean
example (a : MinPlusNN) :
    a ⊗ₒ ⟨⊤⟩ = ⟨⊤⟩ := mul_zero a

end MinPlusNN
```

# The non-negative reals (max,plus)

The order-_dual_ carrier realizes the _(max,plus)_ algebra: the dioid
sum is the numeric _maximum_, the product is numeric _addition_, the
sum neutral is $`-\infty` (identity of $`\max` and absorbing for
$`+`), and the product neutral is $`0`. The carrier `MaxPlusNN` wraps
`WithBot ℝ≥0∞` so that $`-\infty = \bot` is the dioid zero. Unlike the
_(min,plus)_ carriers, the dioid order _agrees_ with the numeric one,
so the dioid supremum is the numeric supremum.

## The carrier and its dioid

The crux, as for _(min,plus)_, is _lower semi-continuity_: addition
distributes over an arbitrary supremum. We prove it through a bridge to
$`\mathbb{R}_{\ge 0}^{\infty}`, where `ENNReal.add_iSup` is available:
a non-$`\bot` supremum over `WithBot ℝ≥0∞` is the coercion of the
supremum of the under-values (reading $`\bot` as $`0`).

```lean
namespace MaxX

theorem coe_unbotD_eq {x : WithBot ℝ≥0∞} (h : x ≠ ⊥) :
    ((x.unbotD 0 : ℝ≥0∞) : WithBot ℝ≥0∞) = x := by
  obtain ⟨d, rfl⟩ := (WithBot.ne_bot_iff_exists).mp h
  rw [WithBot.unbotD_coe]

theorem bridge {ι : Sort*} (f : ι → WithBot ℝ≥0∞)
    (j : ι) (hj : f j ≠ ⊥) :
    (⨆ i, f i)
      = ((⨆ i, (f i).unbotD 0 : ℝ≥0∞)
          : WithBot ℝ≥0∞) := by
  have : Nonempty ι := ⟨j⟩
  rw [WithBot.coe_iSup (OrderTop.bddAbove
    (Set.range fun i => (f i).unbotD 0))]
  refine le_antisymm (iSup_le fun i => ?_)
    (iSup_le fun i => ?_)
  · rcases eq_or_ne (f i) ⊥ with h0 | h0
    · exact h0 ▸ bot_le
    · exact le_iSup_of_le i (by rw [coe_unbotD_eq h0])
  · rcases eq_or_ne (f i) ⊥ with h0 | h0
    · rw [h0]; refine le_iSup_of_le j ?_
      obtain ⟨d, hd⟩ := (WithBot.ne_bot_iff_exists).mp hj
      rw [← hd, WithBot.unbotD_bot, WithBot.coe_le_coe]
      exact bot_le
    · exact le_iSup_of_le i (by rw [coe_unbotD_eq h0])
```

*Theorem:* $`a + \bigsqcup_i f(i) = \bigsqcup_i (a + f(i))`

```lean
theorem add_iSup {ι : Sort*} (a : WithBot ℝ≥0∞)
    (f : ι → WithBot ℝ≥0∞) :
    a + ⨆ i, f i = ⨆ i, a + f i := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  · induction a using WithBot.recBotCoe with
    | bot => simp
    | coe e =>
      by_cases hb : ∃ j, f j ≠ ⊥
      · obtain ⟨j, hj⟩ := hb
        have hgj : (e : WithBot ℝ≥0∞) + f j ≠ ⊥ := by
          obtain ⟨d, hd⟩ :=
            (WithBot.ne_bot_iff_exists).mp hj
          rw [← hd, ← WithBot.coe_add]
          exact WithBot.coe_ne_bot
        have hv : ∀ i,
            ((e : WithBot ℝ≥0∞) + f i).unbotD 0
            = if f i = ⊥ then 0
              else e + (f i).unbotD 0 := by
          intro i
          rcases eq_or_ne (f i) ⊥ with h0 | h0
          · simp [h0]
          · obtain ⟨d, hd⟩ :=
              (WithBot.ne_bot_iff_exists).mp h0
            simp [← hd, ← WithBot.coe_add]
        rw [bridge f j hj,
          bridge (fun i => (e : WithBot ℝ≥0∞) + f i)
            j hgj,
          ← WithBot.coe_add, ENNReal.add_iSup]
        congr 1
        refine le_antisymm (iSup_le fun i => ?_)
          (iSup_le fun i => ?_)
        · rcases eq_or_ne (f i) ⊥ with h0 | h0
          · refine le_iSup_of_le j ?_
            rw [hv j, if_neg hj, h0,
              WithBot.unbotD_bot, add_zero]
            exact le_self_add
          · exact le_iSup_of_le i
              (by rw [hv i, if_neg h0])
        · rw [hv i]
          rcases eq_or_ne (f i) ⊥ with h0 | h0
          · simp [h0]
          · rw [if_neg h0]
            exact le_iSup_of_le i (le_refl _)
      · push Not at hb; simp [hb]
```

The two distributive facts about $`\max` and $`+`, mirroring those for
$`\min` on _(min,plus)_.

*Theorem:* $`a + \max(b, c) = \max(a + b, a + c)` and $`\max(a, b) + c = \max(a + c, b + c)`

```lean
theorem add_max (a b c : WithBot ℝ≥0∞) :
    a + max b c = max (a + b) (a + c) := by
  rcases le_total b c with h | h
  · rw [max_eq_right h, max_eq_right (by gcongr)]
  · rw [max_eq_left h, max_eq_left (by gcongr)]

theorem max_add (a b c : WithBot ℝ≥0∞) :
    max a b + c = max (a + c) (b + c) := by
  rw [add_comm, add_max, add_comm a c, add_comm b c]

end MaxX
```

Each axiom is a fact about `WithBot ℝ≥0∞`, lifted through the wrapper
by `ext`: the monoid laws from `max` and `+`, the distributive laws
from `MaxX.add_max`/`MaxX.max_add`, absorption of $`-\infty`, and
idempotency of $`\max`.

*Definition:* $`\overline{\mathbb{R}}_{\ge 0}` is an `Algebra.Dioid` with $`\oplus = \max`, $`\otimes = {+}`, $`\varepsilon = -\infty`, $`e = 0`

```lean
namespace MaxPlusNN

instance : Algebra.Dioid MaxPlusNN where
  add a b := ⟨max ↑a ↑b⟩
  zero := ⟨⊥⟩
  mul a b := ⟨↑a + ↑b⟩
  one := ⟨0⟩
  oplus_assoc _ _ _ := ext (max_assoc _ _ _)
  eps_oplus _ := ext (max_eq_right bot_le)
  oplus_eps _ := ext (max_eq_left bot_le)
  oplus_comm _ _ := ext (max_comm _ _)
  otimes_assoc _ _ _ := ext (add_assoc _ _ _)
  one_otimes _ := ext (zero_add _)
  otimes_one _ := ext (add_zero _)
  left_distrib _ _ _ := ext (MaxX.add_max _ _ _)
  right_distrib _ _ _ := ext (MaxX.max_add _ _ _)
  eps_otimes _ := ext (WithBot.bot_add _)
  otimes_eps _ := ext (WithBot.add_bot _)
  otimes_comm _ _ := ext (add_comm _ _)
  oplus_idem _ := ext (max_self _)
```

## The canonical order

Dual to the _(min,plus)_ carriers, the dioid order agrees with the
numeric order.

*Theorem:* $`a \preceq b \iff \uparrow a \le \uparrow b`

```lean
theorem le_iff (a b : MaxPlusNN) :
    a ≼ₒ b ↔ (a : WithBot ℝ≥0∞) ≤ b := by
  have h1 : a ≼ₒ b
      ↔ (⟨max ↑a ↑b⟩ : MaxPlusNN) = b := Iff.rfl
  rw [h1]
  constructor
  · intro h
    have : max (↑a : WithBot ℝ≥0∞) ↑b = ↑b :=
      congrArg toVal h
    rw [← this]; exact le_max_left _ _
  · intro h; exact ext (max_eq_right h)
```

The dioid supremum is the numeric supremum of the underlying values,
and lower semi-continuity is `MaxX.add_iSup`.

*Definition:* $`\overline{\mathbb{R}}_{\ge 0}` is an `Algebra.CompleteDioid` with $`\bigsqcup s = \sup\,\{\,\uparrow x \mid x \in s\,\}`

```lean
noncomputable instance :
    Algebra.CompleteDioid MaxPlusNN where
  iSup f := ⟨⨆ i, ↑(f i)⟩
  le_iSup f i :=
    (le_iff _ _).mpr
      (le_iSup (fun i => (f i : WithBot ℝ≥0∞)) i)
  iSup_le f b hb := (le_iff _ _).mpr (iSup_le (by
    intro i; exact (le_iff _ _).mp (hb i)))
  mul_iSup a f := by
    refine ext ?_
    show (↑a : WithBot ℝ≥0∞) + ⨆ i, ↑(f i)
       = ⨆ i, ((↑a : WithBot ℝ≥0∞) + ↑(f i))
    exact MaxX.add_iSup _ _

end MaxPlusNN
```

So `MaxPlusNN` realizes the _(max,plus)_ complete dioid, the order-dual
of `MinPlusNN`: $`\max` in place of $`\min`, $`-\infty` in place of
$`+\infty` for $`\varepsilon`, and the dioid supremum the numeric
supremum.

# The extended reals (max,plus)

The order-dual of `MinPlusExt` on the _same_ extended reals
$`\mathbb{R} \cup \{\pm\infty\}`: a _complete (max,plus) dioid_ with
$`\oplus = \max`, $`\otimes = {+}`, sum neutral
$`\varepsilon = -\infty`, and product neutral $`e = 0`. The carrier is
`WithBot (WithTop ℝ)`, so $`-\infty = \bot` and $`+\infty = \top`, with
the _bottom-absorbing_ addition $`(-\infty) + (+\infty) = -\infty` —
which keeps $`-\infty = \varepsilon` absorbing for $`\otimes`. It is the
mirror image of `MinPlusExt` under $`x \mapsto -x`, and together they give
symmetric min-plus and max-plus dioids on one carrier.

## The carrier and its dioid

The crux is again _lower semi-continuity_, now of $`+` over an arbitrary
_supremum_; the proof mirrors `MinPlusExt`'s, translating by a shift and
reducing to the finite, $`-\infty`, and $`+\infty` cases.

*Definition:* the shift $`x \mapsto r + x`, an order isomorphism

```lean
namespace MaxPlusExtAux

noncomputable def shift (r : ℝ) :
    WithBot (WithTop ℝ) ≃o WithBot (WithTop ℝ) :=
  ((OrderIso.addLeft r).withTopCongr).withBotCongr
```

*Theorem:* $`\mathtt{shift}\,r\,(x) = r + x`

```lean
theorem shift_eq (r : ℝ) (x : WithBot (WithTop ℝ)) :
    shift r x
      = (((r : WithTop ℝ) : WithBot (WithTop ℝ)))
        + x := by
  induction x using WithBot.recBotCoe with
  | bot => simp [shift]
  | coe d =>
    induction d using WithTop.recTopCoe with
    | top =>
      simp only [shift, OrderIso.withBotCongr_apply,
        WithBot.map_coe, OrderIso.withTopCongr_apply,
        WithTop.map_top]
      rw [show ((⊤ : WithTop ℝ)
            : WithBot (WithTop ℝ))
          = ((↑r : WithTop ℝ)
              : WithBot (WithTop ℝ))
            + ((⊤ : WithTop ℝ)
                : WithBot (WithTop ℝ)) from ?_]
      · rfl
      · rw [← WithBot.coe_add, WithTop.add_top]
    | coe s =>
      simp only [shift, OrderIso.withBotCongr_apply,
        WithBot.map_coe, OrderIso.withTopCongr_apply,
        WithTop.map_coe, OrderIso.addLeft_apply]
      rw [← WithBot.coe_add, ← WithTop.coe_add]
```

*Theorem:* $`a + \bigvee_i f(i) = \bigvee_i (a + f(i))`

```lean
theorem add_iSup {ι : Sort*} (a : WithBot (WithTop ℝ))
    (f : ι → WithBot (WithTop ℝ)) :
    (a + ⨆ i, f i) = ⨆ i, a + f i := by
  refine le_antisymm ?_
    (iSup_le fun i => by gcongr; exact le_iSup _ i)
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  · induction a using WithBot.recBotCoe with
    | bot => simp
    | coe b =>
      induction b using WithTop.recTopCoe with
      | coe r =>
        have hmap : (shift r) (⨆ i, f i)
            = ⨆ i, (shift r) (f i) :=
          OrderIso.map_iSup _ _
        simp only [shift_eq] at hmap
        exact hmap.le
      | top =>
        by_cases hbot : (⨆ i, f i) = ⊥
        · have hall : ∀ i, f i = ⊥ := fun i =>
            le_bot_iff.mp (hbot ▸ le_iSup f i)
          simp only [hall, WithBot.add_bot,
            ciSup_const, le_refl]
        · obtain ⟨c, hc⟩ :=
            Option.ne_none_iff_exists'.mp hbot
          rw [show (⨆ i, f i)
              = (c : WithBot (WithTop ℝ)) from hc,
            ← WithBot.coe_add]
          have hex : ∃ j, f j ≠ ⊥ := by
            by_contra h; push Not at h
            exact hbot (by simp [h])
          obtain ⟨j, hj⟩ := hex
          rw [show ((⊤ : WithTop ℝ) + c : WithTop ℝ)
              = ⊤ from WithTop.top_add c]
          refine le_iSup_of_le j ?_
          obtain ⟨d, hd⟩ :=
            Option.ne_none_iff_exists'.mp hj
          rw [show f j
              = (d : WithBot (WithTop ℝ)) from hd,
            ← WithBot.coe_add, WithTop.top_add]
```

The two distributive facts about $`\max` and $`+`, mirroring the
$`\min` ones.

*Theorem:* $`a + \max(b, c) = \max(a + b, a + c)` and $`\max(a, b) + c = \max(a + c, b + c)`

```lean
theorem add_max (a b c : WithBot (WithTop ℝ)) :
    a + max b c = max (a + b) (a + c) := by
  rcases le_total b c with h | h
  · rw [max_eq_right h, max_eq_right (by gcongr)]
  · rw [max_eq_left h, max_eq_left (by gcongr)]

theorem max_add (a b c : WithBot (WithTop ℝ)) :
    max a b + c = max (a + c) (b + c) := by
  rw [add_comm, add_max, add_comm a c, add_comm b c]

end MaxPlusExtAux
```

The complete (max,plus) carrier `MaxPlusExt` wraps `WithBot (WithTop ℝ)`,
with the dioid sum the numeric maximum and the product numeric
addition.

*Definition:* $`\overline{\mathbb{R}}` is an `Algebra.Dioid` with $`\oplus = \max`, $`\otimes = {+}`, $`\varepsilon = -\infty`, $`e = 0`

```lean
namespace MaxPlusExt

instance : Algebra.Dioid MaxPlusExt where
  add a b := ⟨max ↑a ↑b⟩
  zero := ⟨⊥⟩
  mul a b := ⟨↑a + ↑b⟩
  one := ⟨0⟩
  oplus_assoc _ _ _ := ext (max_assoc _ _ _)
  eps_oplus _ := ext (max_eq_right bot_le)
  oplus_eps _ := ext (max_eq_left bot_le)
  oplus_comm _ _ := ext (max_comm _ _)
  otimes_assoc _ _ _ := ext (add_assoc _ _ _)
  one_otimes _ := ext (zero_add _)
  otimes_one _ := ext (add_zero _)
  left_distrib _ _ _ := ext (MaxPlusExtAux.add_max _ _ _)
  right_distrib _ _ _ := ext (MaxPlusExtAux.max_add _ _ _)
  eps_otimes _ := ext (WithBot.bot_add _)
  otimes_eps _ := ext (WithBot.add_bot _)
  otimes_comm _ _ := ext (add_comm _ _)
  oplus_idem _ := ext (max_self _)
```

## The canonical order

Dual to `MinPlusExt`, the dioid order agrees with the numeric order.

*Theorem:* $`a \preceq b \iff \uparrow a \le \uparrow b`

```lean
theorem le_iff (a b : MaxPlusExt) :
    a ≼ₒ b ↔ (a : WithBot (WithTop ℝ)) ≤ b := by
  have h1 : a ≼ₒ b
      ↔ (⟨max ↑a ↑b⟩ : MaxPlusExt) = b := Iff.rfl
  rw [h1]
  constructor
  · intro h
    have : max (↑a : WithBot (WithTop ℝ)) ↑b = ↑b :=
      congrArg toVal h
    rw [← this]; exact le_max_left _ _
  · intro h; exact ext (max_eq_right h)
```

The dioid supremum is the numeric supremum of the underlying values,
and lower semi-continuity is `MaxPlusExtAux.add_iSup`.

*Definition:* $`\overline{\mathbb{R}}` is an `Algebra.CompleteDioid` with $`\bigsqcup s = \sup\,\{\,\uparrow x \mid x \in s\,\}`

```lean
noncomputable instance :
    Algebra.CompleteDioid MaxPlusExt where
  iSup f := ⟨⨆ i, ↑(f i)⟩
  le_iSup f i :=
    (le_iff _ _).mpr
      (le_iSup (fun i => (f i : WithBot (WithTop ℝ))) i)
  iSup_le f b hb := (le_iff _ _).mpr (iSup_le (by
    intro i; exact (le_iff _ _).mp (hb i)))
  mul_iSup a f := by
    refine ext ?_
    show (↑a : WithBot (WithTop ℝ)) + ⨆ i, ↑(f i)
       = ⨆ i, ((↑a : WithBot (WithTop ℝ)) + ↑(f i))
    exact MaxPlusExtAux.add_iSup _ _

end MaxPlusExt
```

So `MaxPlusExt` realizes the _(max,plus)_ complete dioid on
$`\mathbb{R} \cup \{\pm\infty\}`, the exact order-dual of `MinPlusExt`.

```lean
end VerifiedWiki
```
