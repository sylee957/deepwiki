import VersoManual
import Book.Dioids
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
namespace NetworkCalculus

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

*Definition:* $`\overline{\mathbb{R}}` is an `Algebra.Dioid` with $`\oplus = \min`, $`\otimes = {+}`, $`\varepsilon = +\infty`, $`e = 0`

```lean
instance : Algebra.Dioid Rmin where
  add a b := ⟨min a.toR b.toR⟩
  zero := ⟨⊤⟩
  mul a b := ⟨a.toR + b.toR⟩
  one := ⟨0⟩
  oplus_assoc a b c :=
    congrArg ofR (min_assoc _ _ _)
  eps_oplus a := congrArg ofR (min_eq_right le_top)
  oplus_eps a := congrArg ofR (min_eq_left le_top)
  oplus_comm a b := congrArg ofR (min_comm _ _)
  otimes_assoc a b c :=
    congrArg ofR (add_assoc _ _ _)
  one_otimes a := congrArg ofR (zero_add _)
  otimes_one a := congrArg ofR (add_zero _)
  left_distrib a b c := congrArg ofR (add_min _ _ _)
  right_distrib a b c := congrArg ofR (min_add _ _ _)
  eps_otimes a := congrArg ofR (top_add _)
  otimes_eps a := congrArg ofR (add_top _)
  otimes_comm a b := congrArg ofR (add_comm _ _)
  oplus_idem a := congrArg ofR (min_self _)

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

instance : Algebra.Dioid RbarMin where
  add a b := ⟨min a.toB b.toB⟩
  zero := ⟨⊤⟩
  mul a b := ⟨a.toB + b.toB⟩
  one := ⟨0⟩
  oplus_assoc a b c := congrArg ofB (min_assoc _ _ _)
  eps_oplus a := congrArg ofB (min_eq_right le_top)
  oplus_eps a := congrArg ofB (min_eq_left le_top)
  oplus_comm a b := congrArg ofB (min_comm _ _)
  otimes_assoc a b c :=
    congrArg ofB (add_assoc _ _ _)
  one_otimes a := congrArg ofB (zero_add _)
  otimes_one a := congrArg ofB (add_zero _)
  left_distrib a b c :=
    congrArg ofB (RbarX.add_min _ _ _)
  right_distrib a b c :=
    congrArg ofB (RbarX.min_add _ _ _)
  eps_otimes a :=
    congrArg ofB (by simp : (⊤ : Rb) + a.toB = ⊤)
  otimes_eps a :=
    congrArg ofB (by simp : a.toB + (⊤ : Rb) = ⊤)
  otimes_comm a b := congrArg ofB (add_comm _ _)
  oplus_idem a := congrArg ofB (min_self _)
```

The dioid order on the wrapper is the reverse of the numeric order.

*Theorem:* $`a \preceq b \iff b.\mathtt{toB} \le a.\mathtt{toB}`

```lean
theorem le_iff (a b : RbarMin) :
    a ≼ₒ b ↔ b.toB ≤ a.toB := by
  have h1 : a ≼ₒ b
      ↔ (⟨min a.toB b.toB⟩ : RbarMin) = b := Iff.rfl
  rw [h1]
  constructor
  · intro h
    have : min a.toB b.toB = b.toB := congrArg toB h
    rw [← this]; exact min_le_left _ _
  · intro h; exact congrArg ofB (min_eq_right h)
```

The dioid supremum is the numeric infimum of the underlying values.
Membership and least-upper-bound for $`\preceq` reduce to the numeric
greatest-lower-bound, and lower semi-continuity is `RbarX.add_iInf`.

*Definition:* $`\overline{\mathbb{R}}` is an `Algebra.CompleteDioid` with $`\bigsqcup s = \inf\,\{\,x.\mathtt{toB} \mid x \in s\,\}`

```lean
noncomputable instance :
    Algebra.CompleteDioid RbarMin where
  sSup s := ⟨sInf (RbarMin.toB '' s)⟩
  le_sSup s a ha :=
    (le_iff _ _).mpr (sInf_le ⟨a, ha, rfl⟩)
  sSup_le s b hb := (le_iff _ _).mpr (le_sInf (by
    rintro x ⟨y, hy, rfl⟩
    exact (le_iff _ _).mp (hb y hy)))
  mul_sSup a s := by
    have key : a.toB + sInf (toB '' s)
        = sInf (toB '' ((fun b =>
            (⟨a.toB + b.toB⟩ : RbarMin)) '' s)) := by
      rw [Set.image_image]
      show a.toB + sInf (toB '' s)
         = sInf ((fun b => a.toB + b.toB) '' s)
      rw [sInf_image, sInf_image, RbarX.add_iInf]
      refine iInf_congr fun b => ?_
      rw [RbarX.add_iInf]
    exact congrArg ofB key

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

instance : Algebra.Dioid RplusMin where
  add a b := ⟨min a.toE b.toE⟩
  zero := ⟨⊤⟩
  mul a b := ⟨a.toE + b.toE⟩
  one := ⟨0⟩
  oplus_assoc a b c := congrArg ofE (min_assoc _ _ _)
  eps_oplus a := congrArg ofE (min_eq_right le_top)
  oplus_eps a := congrArg ofE (min_eq_left le_top)
  oplus_comm a b := congrArg ofE (min_comm _ _)
  otimes_assoc a b c :=
    congrArg ofE (add_assoc _ _ _)
  one_otimes a := congrArg ofE (zero_add _)
  otimes_one a := congrArg ofE (add_zero _)
  left_distrib a b c :=
    congrArg ofE (RplusX.add_min _ _ _)
  right_distrib a b c :=
    congrArg ofE (RplusX.min_add _ _ _)
  eps_otimes a :=
    congrArg ofE (by simp : (⊤ : ℝ≥0∞) + a.toE = ⊤)
  otimes_eps a :=
    congrArg ofE (by simp : a.toE + (⊤ : ℝ≥0∞) = ⊤)
  otimes_comm a b := congrArg ofE (add_comm _ _)
  oplus_idem a := congrArg ofE (min_self _)
```

*Theorem:* $`a \preceq b \iff b.\mathtt{toE} \le a.\mathtt{toE}`

```lean
theorem le_iff (a b : RplusMin) :
    a ≼ₒ b ↔ b.toE ≤ a.toE := by
  have h1 : a ≼ₒ b
      ↔ (⟨min a.toE b.toE⟩ : RplusMin) = b := Iff.rfl
  rw [h1]
  constructor
  · intro h
    have : min a.toE b.toE = b.toE := congrArg toE h
    rw [← this]; exact min_le_left _ _
  · intro h; exact congrArg ofE (min_eq_right h)
```

*Definition:* $`\overline{\mathbb{R}}_{\ge 0}` is an `Algebra.CompleteDioid` with $`\bigsqcup s = \inf\,\{\,x.\mathtt{toE} \mid x \in s\,\}`

```lean
noncomputable instance :
    Algebra.CompleteDioid RplusMin where
  sSup s := ⟨sInf (RplusMin.toE '' s)⟩
  le_sSup s a ha :=
    (le_iff _ _).mpr (sInf_le ⟨a, ha, rfl⟩)
  sSup_le s b hb := (le_iff _ _).mpr (le_sInf (by
    rintro x ⟨y, hy, rfl⟩
    exact (le_iff _ _).mp (hb y hy)))
  mul_sSup a s := by
    have key : a.toE + sInf (toE '' s)
        = sInf (toE '' ((fun b =>
            (⟨a.toE + b.toE⟩ : RplusMin)) '' s)) := by
      rw [Set.image_image]
      show a.toE + sInf (toE '' s)
         = sInf ((fun b => a.toE + b.toE) '' s)
      rw [sInf_image, sInf_image, RplusX.add_iInf]
      refine iInf_congr fun b => ?_
      rw [RplusX.add_iInf]
    exact congrArg ofE key

end RplusMin
```

Of the three carriers, $`\overline{\mathbb{R}}_{\ge 0}` is the
canonical complete (min,plus) dioid: complete and free of the sign
pathologies, with lower semi-continuity inherited directly from
$`\mathbb{R}_{\ge 0}^{\infty}`.

```lean
end NetworkCalculus
```
