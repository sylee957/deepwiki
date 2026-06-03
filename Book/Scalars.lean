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

#doc (Manual) "The (min,plus) scalar dioids" =>
The abstract dioid tower is realized by concrete number systems. This
chapter exhibits three: the reals with $`+\infty`, a dioid; the
extended reals with $`\pm\infty`, a complete dioid; and the
_non-negative_ reals with $`+\infty`, also a complete dioid. All take
$`\oplus = \min`, $`\otimes = {+}`, with the canonical order the
reverse of the usual numeric order.

```lean
namespace VerifiedWiki

open scoped Algebra.Bridge
```

# A concrete dioid: the reals with infinity

The abstract tower is realized by the _(min,plus)_ algebra on
$`\overline{\mathbb{R}} = \mathbb{R} \cup \{+\infty\}`. The dioid sum is
the numeric _minimum_, the product is numeric _addition_, the sum
neutral is $`+\infty` (absorbing for $`\min`, since $`\min(+\infty, a)
= a` forces nothing larger), and the product neutral is $`0`. The
canonical order $`a \preceq b \iff \min(a, b) = b` is then the _reverse_
of the usual numeric order.

We carry the numeric value in `WithTop ℝ` (with $`+\infty = \top`) under
a one-field wrapper, so the dioid operations are attached freshly rather
than colliding with any numeric algebra on `WithTop ℝ`.

*Definition:* the carrier $`\overline{\mathbb{R}} = \mathbb{R} \cup \{+\infty\}`

```lean
structure Rmin where ofR ::
  toR : WithTop ℝ

namespace Rmin

open Algebra

instance : Coe Rmin (WithTop ℝ) := ⟨toR⟩

@[ext] theorem ext {a b : Rmin}
    (h : (a : WithTop ℝ) = b) : a = b := by
  cases a; cases b; exact congrArg ofR h
```

Two arithmetic facts on `WithTop ℝ` carry the distributive laws:
addition distributes over the minimum on each side, because addition is
monotone.

*Theorem:* $`a + \min(b, c) = \min(a + b, a + c)`

```lean
theorem add_min (a b c : WithTop ℝ) :
    a + min b c = min (a + b) (a + c) := by
  rcases le_total b c with h | h
  · rw [min_eq_left h, min_eq_left (by gcongr)]
  · rw [min_eq_right h, min_eq_right (by gcongr)]

theorem min_add (a b c : WithTop ℝ) :
    min a b + c = min (a + c) (b + c) := by
  rw [add_comm, add_min, add_comm a c, add_comm b c]
```

Each dioid axiom is now a fact about `WithTop ℝ`: associativity and
commutativity of $`\min` and $`+`, the neutrals $`+\infty` and $`0`,
the two distributive laws, that $`+\infty` is absorbing for $`+`, and
idempotency $`\min(a, a) = a`.

Each axiom is a fact about `WithTop ℝ`, lifted through the wrapper by
`ext`: the monoid laws from `min` and `+`, the distributive laws from
`add_min`/`min_add`, absorption of $`+\infty`, and idempotency of
$`\min`. The operations use the $`\uparrow` coercion to the underlying
value.

*Definition:* $`\overline{\mathbb{R}}` is an `Algebra.Dioid` with $`\oplus = \min`, $`\otimes = {+}`, $`\varepsilon = +\infty`, $`e = 0`

```lean
instance : Algebra.Dioid Rmin where
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
  left_distrib _ _ _ := ext (add_min _ _ _)
  right_distrib _ _ _ := ext (min_add _ _ _)
  eps_otimes _ := ext (top_add _)
  otimes_eps _ := ext (add_top _)
  otimes_comm _ _ := ext (add_comm _ _)
  oplus_idem _ := ext (min_self _)

end Rmin
```

In the _(min,plus)_ reading the dioid sum is the minimum and the dioid
product is numeric addition. We offer carrier-tagged `scoped` notation
spelling that out — `∧[Rmin]` for the sum, `+[Rmin]` for the product —
so it reads as min-plus without clashing with the bare `+` (which on a
dioid already denotes the sum). It is dormant until
`open scoped VerifiedWiki.Rmin`.

```lean
namespace Rmin
open Algebra

scoped notation:65 a:65 " ∧[Rmin] " b:66 =>
  (a ⊕ₒ b : Rmin)
scoped notation:70 a:70 " +[Rmin] " b:71 =>
  (a ⊗ₒ b : Rmin)

end Rmin
```

The four essential arithmetic cases of $`\overline{\mathbb{R}}`:

```lean
namespace Rmin
open Algebra
```

*Theorem:* finite $`\wedge` finite stays in $`\mathbb{R}`

```lean
example (x y : ℝ) :
    ∃ z : ℝ, (⟨x⟩ : Rmin) ∧[Rmin] ⟨y⟩ = ⟨z⟩ :=
  ⟨min x y, rfl⟩
```

*Theorem:* $`a \wedge {+\infty} = a`

```lean
example (a : Rmin) :
    a ∧[Rmin] ⟨⊤⟩ = a := add_zero a
```

*Theorem:* finite $`+` finite stays in $`\mathbb{R}`

```lean
example (x y : ℝ) :
    ∃ z : ℝ, (⟨x⟩ : Rmin) +[Rmin] ⟨y⟩ = ⟨z⟩ :=
  ⟨x + y, rfl⟩
```

*Theorem:* $`a + {+\infty} = {+\infty}` ($`+\infty` absorbing)

```lean
example (a : Rmin) :
    a +[Rmin] ⟨⊤⟩ = ⟨⊤⟩ := mul_zero a

end Rmin
```

Because the instance is found by resolution, every result of the tower
— the order $`\preceq`, its reflexivity, transitivity, antisymmetry,
and the isotony of $`\oplus` and $`\otimes` — now holds for
$`\overline{\mathbb{R}}` with no further work.

*Theorem:* $`a \preceq a` on $`\overline{\mathbb{R}}`

```lean
example (a : Rmin) :
    a ≼ₒ a :=
  le_rfl
```

# A complete dioid: the extended reals

The carrier $`\overline{\mathbb{R}} = \mathbb{R} \cup \{+\infty\}` is
_not_ complete: it is unbounded below, so a set of reals decreasing
without bound has no infimum inside it, and the dioid supremum (the
numeric infimum, since the order is reversed) is undefined. Adjoining
$`-\infty` repairs this. The _extended reals_ $`\overline{\mathbb{R}}
= \mathbb{R} \cup \{\pm\infty\}` form a complete lattice, and with the
top-absorbing addition $`(+\infty) + (-\infty) = +\infty` — which keeps
$`+\infty = \varepsilon` absorbing for $`\otimes` — they carry a
_complete_ (min,plus) dioid.

We use `WithTop (WithBot ℝ)` for the carrier, so that $`+\infty = \top`
and $`-\infty = \bot`, with the top-absorbing addition built in.

```lean
open scoped Classical

abbrev Rb := WithTop (WithBot ℝ)
```

The crux is _lower semi-continuity_ of $`+`: addition distributes over
an arbitrary infimum. The proof translates by a fixed real through an
order isomorphism (a shift), reducing the general case to the
finite, $`-\infty`, and $`+\infty` cases.

*Definition:* the shift $`x \mapsto r + x`, an order isomorphism

```lean
namespace RbarX

noncomputable def shift (r : ℝ) : Rb ≃o Rb :=
  ((OrderIso.addLeft r).withBotCongr).withTopCongr
```

*Theorem:* $`\mathtt{shift}\,r\,(x) = r + x`

```lean
theorem shift_eq (r : ℝ) (x : Rb) :
    shift r x = (((r : WithBot ℝ) : Rb)) + x := by
  induction x using WithTop.recTopCoe with
  | top => simp [shift]
  | coe d =>
    induction d using WithBot.recBotCoe with
    | bot =>
      simp only [shift, OrderIso.withTopCongr_apply,
        WithTop.map_coe, OrderIso.withBotCongr_apply,
        WithBot.map_bot]
      rw [show ((⊥ : WithBot ℝ) : Rb)
          = ((↑r : WithBot ℝ) : Rb)
            + ((⊥ : WithBot ℝ) : Rb) from ?_]
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
theorem add_iInf {ι : Sort*} (a : Rb) (f : ι → Rb) :
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
          rw [show (⨅ i, f i) = (c : Rb) from hc,
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
          rw [show f j = (d : Rb) from hd,
            ← WithTop.coe_add, WithBot.bot_add]
```

The two distributive facts about $`\min` and $`+` carry the dioid
distributive laws, as before.

*Theorem:* $`a + \min(b, c) = \min(a + b, a + c)` and $`\min(a, b) + c = \min(a + c, b + c)`

```lean
theorem add_min (a b c : Rb) :
    a + min b c = min (a + b) (a + c) := by
  rcases le_total b c with h | h
  · rw [min_eq_left h, min_eq_left (by gcongr)]
  · rw [min_eq_right h, min_eq_right (by gcongr)]

theorem min_add (a b c : Rb) :
    min a b + c = min (a + c) (b + c) := by
  rw [add_comm, add_min, add_comm a c, add_comm b c]

end RbarX
```

The complete (min,plus) carrier wraps `Rb`, with the dioid sum the
numeric minimum and the product numeric addition.

*Definition:* the carrier $`\overline{\mathbb{R}} = \mathbb{R} \cup \{\pm\infty\}`

```lean
structure RbarMin where ofB ::
  toB : Rb

namespace RbarMin

instance : Coe RbarMin Rb := ⟨toB⟩

@[ext] theorem ext {a b : RbarMin}
    (h : (a : Rb) = b) : a = b := by
  cases a; cases b; exact congrArg ofB h

instance : Algebra.Dioid RbarMin where
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
  eps_otimes a :=
    ext (show (⊤ : Rb) + ↑a = ⊤ by simp)
  otimes_eps a :=
    ext (show (↑a : Rb) + ⊤ = ⊤ by simp)
  otimes_comm _ _ := ext (add_comm _ _)
  oplus_idem _ := ext (min_self _)
```

The dioid order on the wrapper is the reverse of the numeric order.

*Theorem:* $`a \preceq b \iff \uparrow b \le \uparrow a`

```lean
theorem le_iff (a b : RbarMin) :
    a ≼ₒ b ↔ (b : Rb) ≤ a := by
  have h1 : a ≼ₒ b
      ↔ (⟨min ↑a ↑b⟩ : RbarMin) = b := Iff.rfl
  rw [h1]
  constructor
  · intro h
    have : min (↑a : Rb) ↑b = ↑b := congrArg toB h
    rw [← this]; exact min_le_left _ _
  · intro h; exact ext (min_eq_right h)
```

The dioid supremum is the numeric infimum of the underlying values.
Membership and least-upper-bound for $`\preceq` reduce to the numeric
greatest-lower-bound, and lower semi-continuity is `RbarX.add_iInf`.

*Definition:* $`\overline{\mathbb{R}}` is an `Algebra.CompleteDioid` with $`\bigsqcup s = \inf\,\{\,\uparrow x \mid x \in s\,\}`

```lean
noncomputable instance :
    Algebra.CompleteDioid RbarMin where
  iSup f := ⟨⨅ i, ↑(f i)⟩
  le_iSup f i := (le_iff _ _).mpr (iInf_le _ i)
  iSup_le f b hb := (le_iff _ _).mpr (le_iInf (by
    intro i
    exact (le_iff _ _).mp (hb i)))
  mul_iSup a f := by
    refine ext ?_
    show (↑a : Rb) + ⨅ i, ↑(f i)
       = ⨅ i, ((↑a : Rb) + ↑(f i))
    exact RbarX.add_iInf _ _

end RbarMin
```

So $`\overline{\mathbb{R}}` realizes the _complete_ dioid: every set
has a dioid supremum (its numeric infimum), and the product is lower
semi-continuous. The top element $`\top = \bigsqcup_x x` and its
absorbing laws, and the whole order theory, follow from the tower.

# A complete dioid: the non-negative reals

The non-negative extended reals $`\overline{\mathbb{R}}_{\ge 0}
= \mathbb{R}_{\ge 0} \cup \{+\infty\}` are the cleanest complete
(min,plus) carrier. Being bounded below by $`0`, they form a complete
lattice with $`0 = \bot` and $`+\infty = \top` and no $`-\infty`, so
$`+\infty = \varepsilon` stays absorbing and there are no
$`(+\infty) + (-\infty)` indeterminacies. We use Mathlib's
$`\mathbb{R}_{\ge 0}^{\infty}` (`ℝ≥0∞`), whose lower semi-continuity of
$`+` is available off the shelf.

```lean
open scoped ENNReal
```

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

*Definition:* the carrier $`\overline{\mathbb{R}}_{\ge 0} = \mathbb{R}_{\ge 0} \cup \{+\infty\}`

```lean
structure RplusMin where ofE ::
  toE : ℝ≥0∞

namespace RplusMin

instance : Coe RplusMin ℝ≥0∞ := ⟨toE⟩

@[ext] theorem ext {a b : RplusMin}
    (h : (a : ℝ≥0∞) = b) : a = b := by
  cases a; cases b; exact congrArg ofE h

instance : Algebra.Dioid RplusMin where
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
  eps_otimes a :=
    ext (show (⊤ : ℝ≥0∞) + ↑a = ⊤ by simp)
  otimes_eps a :=
    ext (show (↑a : ℝ≥0∞) + ⊤ = ⊤ by simp)
  otimes_comm _ _ := ext (add_comm _ _)
  oplus_idem _ := ext (min_self _)
```

*Theorem:* $`a \preceq b \iff \uparrow b \le \uparrow a`

```lean
theorem le_iff (a b : RplusMin) :
    a ≼ₒ b ↔ (b : ℝ≥0∞) ≤ a := by
  have h1 : a ≼ₒ b
      ↔ (⟨min ↑a ↑b⟩ : RplusMin) = b := Iff.rfl
  rw [h1]
  constructor
  · intro h
    have : min (↑a : ℝ≥0∞) ↑b = ↑b := congrArg toE h
    rw [← this]; exact min_le_left _ _
  · intro h; exact ext (min_eq_right h)
```

*Definition:* $`\overline{\mathbb{R}}_{\ge 0}` is an `Algebra.CompleteDioid` with $`\bigsqcup s = \inf\,\{\,\uparrow x \mid x \in s\,\}`

```lean
noncomputable instance :
    Algebra.CompleteDioid RplusMin where
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

end RplusMin
```

Of the three carriers, $`\overline{\mathbb{R}}_{\ge 0}` is the
canonical complete (min,plus) dioid: complete and free of the sign
pathologies, with lower semi-continuity inherited directly from
$`\mathbb{R}_{\ge 0}^{\infty}`.

```lean
end VerifiedWiki
```
