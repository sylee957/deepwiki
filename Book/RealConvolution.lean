import VersoManual
import Book.Convolution
import Mathlib.Topology.Instances.NNReal.Lemmas

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Real convolutions of curves" =>
The service curves of network calculus compare a server's output to
_convolutions_ of real curves $`\mathbb{R}^{+} \to \mathbb{R}_{\ge 0}`.
This chapter defines those operators — the infimal convolution and the
super-convolution — by _computing in a dioid_: a real curve is embedded
into a complete (min,plus) or (max,plus) dioid, the dioid product (the
convolution) is taken there, and the finite result is projected back to
$`\mathbb{R}_{\ge 0}`. Each operator then comes with a theorem
re-expressing it as the expected real $`\bigsqcap` / $`\bigsqcup` over
the splits of $`t`. The non-decreasing and super-additive _closures_
they generate close the chapter.

```lean
namespace VerifiedWiki

open Algebra
open scoped Classical NNReal ENNReal Algebra.Bridge
```

# A supremum-absorption lemma

A constant added to a conditionally-complete supremum is absorbed into
a bound: if $`c + f(i) \le y` for every `i`, then $`c + \bigsqcup_i f(i)
\le y`. This is the workhorse for the closure bounds below.

*Theorem:* $`(\forall i,\ c + f(i) \le y) \implies c + \bigsqcup_i f(i) \le y`

```lean
theorem add_ciSup_le {ι : Type} [Nonempty ι]
    (c y : ℝ≥0) (f : ι → ℝ≥0)
    (h : ∀ i, c + f i ≤ y) : c + ⨆ i, f i ≤ y := by
  have hcy : c ≤ y :=
    le_trans le_self_add (h (Classical.arbitrary ι))
  have hsup : ⨆ i, f i ≤ y - c :=
    ciSup_le (fun i => le_tsub_of_add_le_left (h i))
  calc c + ⨆ i, f i ≤ c + (y - c) := by gcongr
    _ = y := add_tsub_cancel_of_le hcy
```

# The dual: a (max,plus) complete dioid

The infimal convolution lives in the (min,plus) dioid
$`\overline{\mathbb{R}}_{\ge 0}` (`RplusMin`) of an earlier chapter. The
super-convolution is its mirror image: a _supremum_ of sums, which is
the product of the _dual_ (max,plus) dioid. Its carrier is
$`\mathbb{R}_{\ge 0} \cup \{+\infty, -\infty\}`, realized as
`WithBot ℝ≥0∞` so that $`-\infty = \bot` is the dioid zero — the
identity of $`\oplus = \max` and absorbing for $`\otimes = +`.

```lean
abbrev Rp := WithBot ℝ≥0∞
```

The crux, as for (min,plus), is _lower semi-continuity_: addition
distributes over an arbitrary supremum. We prove it through a bridge to
$`\mathbb{R}_{\ge 0}^{\infty}`, where `ENNReal.add_iSup` is available:
a non-$`\bot` supremum over `WithBot ℝ≥0∞` is the coercion of the
supremum of the under-values (reading $`\bot` as $`0`).

```lean
namespace MaxX

theorem coe_unbotD_eq {x : Rp} (h : x ≠ ⊥) :
    ((x.unbotD 0 : ℝ≥0∞) : Rp) = x := by
  obtain ⟨d, rfl⟩ := (WithBot.ne_bot_iff_exists).mp h
  rw [WithBot.unbotD_coe]

theorem bridge {ι : Sort*} (f : ι → Rp)
    (j : ι) (hj : f j ≠ ⊥) :
    (⨆ i, f i)
      = ((⨆ i, (f i).unbotD 0 : ℝ≥0∞) : Rp) := by
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
theorem add_iSup {ι : Sort*} (a : Rp) (f : ι → Rp) :
    a + ⨆ i, f i = ⨆ i, a + f i := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  · induction a using WithBot.recBotCoe with
    | bot => simp
    | coe e =>
      by_cases hb : ∃ j, f j ≠ ⊥
      · obtain ⟨j, hj⟩ := hb
        have hgj : (e : Rp) + f j ≠ ⊥ := by
          obtain ⟨d, hd⟩ :=
            (WithBot.ne_bot_iff_exists).mp hj
          rw [← hd, ← WithBot.coe_add]
          exact WithBot.coe_ne_bot
        have hv : ∀ i, ((e : Rp) + f i).unbotD 0
            = if f i = ⊥ then 0
              else e + (f i).unbotD 0 := by
          intro i
          rcases eq_or_ne (f i) ⊥ with h0 | h0
          · simp [h0]
          · obtain ⟨d, hd⟩ :=
              (WithBot.ne_bot_iff_exists).mp h0
            simp [← hd, ← WithBot.coe_add]
        rw [bridge f j hj,
          bridge (fun i => (e : Rp) + f i) j hgj,
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
$`\min` on (min,plus).

*Theorem:* $`a + \max(b, c) = \max(a + b, a + c)` and $`\max(a, b) + c = \max(a + c, b + c)`

```lean
theorem add_max (a b c : Rp) :
    a + max b c = max (a + b) (a + c) := by
  rcases le_total b c with h | h
  · rw [max_eq_right h, max_eq_right (by gcongr)]
  · rw [max_eq_left h, max_eq_left (by gcongr)]

theorem max_add (a b c : Rp) :
    max a b + c = max (a + c) (b + c) := by
  rw [add_comm, add_max, add_comm a c, add_comm b c]

end MaxX
```

The (max,plus) carrier wraps `Rp`, with the dioid sum the numeric
maximum and the product numeric addition. Unlike (min,plus), the dioid
order coincides with the _numeric_ order, so the dioid supremum is the
numeric supremum.

*Definition:* the (max,plus) carrier $`\mathbb{R}_{\ge 0} \cup \{\pm\infty\}` with $`\oplus = \max`, $`\otimes = +`

```lean
structure RplusMax where ofW ::
  toW : Rp

namespace RplusMax

instance : Coe RplusMax Rp := ⟨toW⟩

@[ext] theorem ext {a b : RplusMax}
    (h : (a : Rp) = b) : a = b := by
  cases a; cases b; exact congrArg ofW h

instance : Algebra.Dioid RplusMax where
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
  eps_otimes a :=
    ext (show (⊥ : Rp) + ↑a = ⊥ from WithBot.bot_add _)
  otimes_eps a :=
    ext (show (↑a : Rp) + ⊥ = ⊥ from WithBot.add_bot _)
  otimes_comm _ _ := ext (add_comm _ _)
  oplus_idem _ := ext (max_self _)
```

*Theorem:* $`a \preceq b \iff \uparrow a \le \uparrow b`

```lean
theorem le_iff (a b : RplusMax) :
    a ≼ₒ b ↔ (a : Rp) ≤ b := by
  have h1 : a ≼ₒ b
      ↔ (⟨max ↑a ↑b⟩ : RplusMax) = b := Iff.rfl
  rw [h1]
  constructor
  · intro h
    have : max (↑a : Rp) ↑b = ↑b := congrArg toW h
    rw [← this]; exact le_max_left _ _
  · intro h; exact ext (max_eq_right h)
```

*Definition:* the (max,plus) carrier is an `Algebra.CompleteDioid` with $`\bigsqcup s = \sup\,\{\,\uparrow x \mid x \in s\,\}`

```lean
noncomputable instance :
    Algebra.CompleteDioid RplusMax where
  iSup f := ⟨⨆ i, ↑(f i)⟩
  le_iSup f i :=
    (le_iff _ _).mpr (le_iSup (fun i => (f i : Rp)) i)
  iSup_le f b hb := (le_iff _ _).mpr (iSup_le (by
    intro i; exact (le_iff _ _).mp (hb i)))
  mul_iSup a f := by
    refine ext ?_
    show (↑a : Rp) + ⨆ i, ↑(f i)
       = ⨆ i, ((↑a : Rp) + ↑(f i))
    exact MaxX.add_iSup _ _

end RplusMax
```

# Embedding and projecting curves

A real curve embeds into either dioid by wrapping each value; the
finite result of a dioid convolution projects back to
$`\mathbb{R}_{\ge 0}`. For (min,plus) the embedding is into `RplusMin`
and the projection reads off the underlying $`\mathbb{R}_{\ge 0}^{\infty}`;
for (max,plus) it is into `RplusMax`, projecting through `Rp`.

*Definition:* the (min,plus) and (max,plus) embeddings of a real curve

```lean
def embMin (g : ℝ≥0 → ℝ≥0) : F :=
  fun t => ⟨(g t : ℝ≥0∞)⟩

def embMax (g : ℝ≥0 → ℝ≥0) : ℝ≥0 → RplusMax :=
  fun t => ⟨((g t : ℝ≥0∞) : Rp)⟩
```

Every split of `t` into $`u + s` is a nonempty set — the split
$`t + 0` — so the convolution's $`\bigsqcap` / $`\bigsqcup` is over a
nonempty index.

```lean
instance splitNonempty (t : ℝ≥0) :
    Nonempty {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t} :=
  ⟨⟨(t, 0), by simp⟩⟩
```

# The infimal convolution

The _infimal convolution_ $`g \ast h` is the (min,plus) convolution of
the embedded curves, read back into $`\mathbb{R}_{\ge 0}`. Because the
product on $`\overline{\mathbb{R}}_{\ge 0}` is numeric addition and the
dioid supremum is the numeric infimum, the convolution at `t` is finite
(the split $`t + 0` gives $`g(t) + h(0)`), so the projection is exact.

*Definition:* the real infimal convolution, computed in (min,plus)

```lean
noncomputable def infConvR (g h : ℝ≥0 → ℝ≥0) :
    ℝ≥0 → ℝ≥0 :=
  fun t =>
    (conv (embMin g) (embMin h) t
      : RplusMin).toE.toNNReal
```

The underlying $`\mathbb{R}_{\ge 0}^{\infty}` value of the dioid
convolution is exactly the infimum of $`g(u) + h(s)` over the splits:
the dioid supremum unfolds to the numeric infimum, and the product
$`\otimes` to numeric $`+`.

*Theorem:* $`\uparrow(g \ast h)(t) = \bigsqcap_{u + s = t} (g(u) + h(s))` in $`\mathbb{R}_{\ge 0}^{\infty}`

```lean
theorem embMin_mul (g h : ℝ≥0 → ℝ≥0) (u s : ℝ≥0) :
    ((embMin g u ⊗ₒ embMin h s : RplusMin) : ℝ≥0∞)
      = (g u : ℝ≥0∞) + (h s : ℝ≥0∞) := rfl

theorem conv_embMin_toE (g h : ℝ≥0 → ℝ≥0) (t : ℝ≥0) :
    ((conv (embMin g) (embMin h) t : RplusMin) : ℝ≥0∞)
      = ⨅ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
          ((g p.1.1 + h p.1.2 : ℝ≥0) : ℝ≥0∞) := by
  rw [conv_apply]
  show (⨅ x : {x : RplusMin //
        ∃ u s, u + s = t ∧ x = embMin g u ⊗ₒ embMin h s},
        (x.val : ℝ≥0∞)) = _
  apply le_antisymm
  · refine le_iInf (fun p => ?_)
    refine iInf_le_of_le
      ⟨embMin g p.1.1 ⊗ₒ embMin h p.1.2,
        p.1.1, p.1.2, p.2, rfl⟩ ?_
    show ((embMin g p.1.1 ⊗ₒ embMin h p.1.2 : RplusMin)
        : ℝ≥0∞) ≤ _
    rw [embMin_mul]; push_cast; rfl
  · refine le_iInf (fun x => ?_)
    obtain ⟨u, s, hus, hx⟩ := x.2
    refine iInf_le_of_le ⟨(u, s), hus⟩ ?_
    rw [show (x.val : ℝ≥0∞)
          = ((embMin g u ⊗ₒ embMin h s : RplusMin)
              : ℝ≥0∞) from congrArg _ hx, embMin_mul]
    push_cast; rfl
```

Projecting back, the infimal convolution is the expected real infimum.

*Theorem:* $`(g \ast h)(t) = \bigsqcap_{u + s = t} (g(u) + h(s))`

```lean
theorem infConvR_eq (g h : ℝ≥0 → ℝ≥0) (t : ℝ≥0) :
    infConvR g h t
      = ⨅ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
          (g p.1.1 + h p.1.2) := by
  rw [infConvR, conv_embMin_toE,
    ← ENNReal.coe_iInf
      (fun p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t} =>
        g p.1.1 + h p.1.2),
    ENNReal.toNNReal_coe]
```

The infimal convolution is _isotone_ in each curve: raising a curve
raises the convolution.

*Theorem:* $`\beta \le \beta' \implies A \ast \beta \le A \ast \beta'`

```lean
theorem infConvR_mono_right (A : ℝ≥0 → ℝ≥0)
    {beta beta' : ℝ≥0 → ℝ≥0} (h : beta ≤ beta') :
    infConvR A beta ≤ infConvR A beta' := by
  intro t
  rw [infConvR_eq, infConvR_eq]
  refine ciInf_mono (OrderBot.bddBelow _) (fun p => ?_)
  gcongr
  exact h p.1.2
```

# The super-convolution

The _super-convolution_ $`\beta \boxplus \beta` is the (max,plus)
convolution of `beta` with itself, read back into
$`\mathbb{R}_{\ge 0}`. It is the supremal mirror of the infimal
convolution, over the same splits.

*Definition:* the super-convolution, computed in (max,plus)

```lean
noncomputable def superConv (beta : ℝ≥0 → ℝ≥0) :
    ℝ≥0 → ℝ≥0 :=
  fun t =>
    (conv (embMax beta) (embMax beta) t
      : RplusMax).toW.unbotD 0 |>.toNNReal
```

As for the infimal convolution, the underlying value of the dioid
product is the supremum of $`\beta(a) + \beta(b)` over the splits.

*Theorem:* $`(\beta \boxplus \beta)(\tau) = \bigsqcup_{a + b = \tau} (\beta(a) + \beta(b))`

```lean
theorem embMax_mul (beta : ℝ≥0 → ℝ≥0) (a b : ℝ≥0) :
    ((embMax beta a ⊗ₒ embMax beta b : RplusMax) : Rp)
      = (((beta a : ℝ≥0∞) : Rp))
        + (((beta b : ℝ≥0∞) : Rp)) := rfl

theorem conv_embMax_toW (beta : ℝ≥0 → ℝ≥0) (t : ℝ≥0) :
    ((conv (embMax beta) (embMax beta) t : RplusMax)
        : Rp)
      = ⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
          (((beta p.1.1 + beta p.1.2 : ℝ≥0)
            : ℝ≥0∞) : Rp) := by
  rw [conv_apply]
  show (⨆ x : {x : RplusMax //
        ∃ u s, u + s = t ∧
          x = embMax beta u ⊗ₒ embMax beta s},
        (x.val : Rp)) = _
  apply le_antisymm
  · refine iSup_le (fun x => ?_)
    obtain ⟨u, s, hus, hx⟩ := x.2
    refine le_iSup_of_le ⟨(u, s), hus⟩ ?_
    rw [show (x.val : Rp)
          = ((embMax beta u ⊗ₒ embMax beta s : RplusMax)
              : Rp) from congrArg _ hx, embMax_mul]
    push_cast; rfl
  · refine iSup_le (fun p => ?_)
    refine le_iSup_of_le
      ⟨embMax beta p.1.1 ⊗ₒ embMax beta p.1.2,
        p.1.1, p.1.2, p.2, rfl⟩ ?_
    show _ ≤ ((embMax beta p.1.1 ⊗ₒ embMax beta p.1.2
        : RplusMax) : Rp)
    rw [embMax_mul]; push_cast; rfl
```

Projecting back, the super-convolution is the expected real supremum,
provided the values are bounded so the supremum is finite.

*Theorem:* $`\uparrow(\beta \boxplus \beta)(\tau) = \bigsqcup_{a + b = \tau} (\beta(a) + \beta(b))` when finite

```lean
theorem superConv_coe (beta : ℝ≥0 → ℝ≥0) (t : ℝ≥0)
    (hfin : (⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
        ((beta p.1.1 + beta p.1.2 : ℝ≥0) : ℝ≥0∞)) ≠ ⊤) :
    ((superConv beta t : ℝ≥0) : ℝ≥0∞)
      = ⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
          ((beta p.1.1 + beta p.1.2 : ℝ≥0) : ℝ≥0∞) := by
  have hcoe : (⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
        (((beta p.1.1 + beta p.1.2 : ℝ≥0) : ℝ≥0∞) : Rp))
      = (((⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
          ((beta p.1.1 + beta p.1.2 : ℝ≥0) : ℝ≥0∞))
          : ℝ≥0∞) : Rp) :=
    (WithBot.coe_iSup (OrderTop.bddAbove _)).symm
  rw [superConv, conv_embMax_toW, hcoe]
  rw [WithBot.unbotD_coe, ENNReal.coe_toNNReal hfin]
```

The super-convolution obeys an _unconditional_ upper bound: if every
split term is below `c`, so is the result. No finiteness is needed —
when the dioid supremum is $`+\infty` the projection floors to `0`,
which is below `c` anyway, and otherwise the bound is the genuine
supremum's. This is the bound the strict-service proofs use.

*Theorem:* $`(\forall a + b = t,\ \beta(a) + \beta(b) \le c) \implies (\beta \boxplus \beta)(t) \le c`

```lean
theorem superConv_le (beta : ℝ≥0 → ℝ≥0) (t c : ℝ≥0)
    (h : ∀ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
      beta p.1.1 + beta p.1.2 ≤ c) :
    superConv beta t ≤ c := by
  rw [superConv, conv_embMax_toW]
  have hcoe :
      (⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
        (((beta p.1.1 + beta p.1.2 : ℝ≥0)
          : ℝ≥0∞) : Rp))
      = (((⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
          ((beta p.1.1 + beta p.1.2 : ℝ≥0) : ℝ≥0∞))
          : ℝ≥0∞) : Rp) :=
    (WithBot.coe_iSup (OrderTop.bddAbove _)).symm
  rw [hcoe, WithBot.unbotD_coe]
  have hb : (⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
        ((beta p.1.1 + beta p.1.2 : ℝ≥0) : ℝ≥0∞))
        ≤ (c : ℝ≥0∞) :=
    iSup_le (fun p => by exact_mod_cast h p)
  have := ENNReal.toNNReal_mono (by simp) hb
  simpa using this
```

Adding a constant absorbs into that bound, exactly as the supremum
absorption lemma did for an explicit $`\bigsqcup`: this is the shape the
strict-service-curve proofs invoke, with `c` a departure value.

*Theorem:* $`(\forall a + b = t,\ c + \beta(a) + \beta(b) \le y) \implies c + (\beta \boxplus \beta)(t) \le y`

```lean
theorem add_superConv_le
    (beta : ℝ≥0 → ℝ≥0) (t c y : ℝ≥0)
    (h : ∀ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
      c + (beta p.1.1 + beta p.1.2) ≤ y) :
    c + superConv beta t ≤ y := by
  have hcy : c ≤ y :=
    le_trans le_self_add (h ⟨(t, 0), by simp⟩)
  have hsup : superConv beta t ≤ y - c :=
    superConv_le beta t (y - c)
      (fun p => le_tsub_of_add_le_left (h p))
  calc c + superConv beta t ≤ c + (y - c) := by gcongr
    _ = y := add_tsub_cancel_of_le hcy
```

# Super-convolution as a conjugated infimal convolution

The (max,plus) computation is not a separate world: it is the
(min,plus) infimal convolution _conjugated by negation_. The
order-reversing involution $`x \mapsto -x` is the isomorphism between
the two dioids, turning $`\max` into $`\min` and a sum into the
negated sum. Concretely, over the reals,
$$`\sup_{a + b = t}\big(\beta(a) + \beta(b)\big) = -\inf_{a + b = t}\big((-\beta(a)) + (-\beta(b))\big),`
the right-hand infimum being an infimal convolution of $`-\beta`. We
record this duality as one theorem; the standalone (max,plus) dioid
above is kept as the computational engine, while this lemma is the
honest statement of _why_ it is the right one. The supremal conjugation
$`\sup g = -\inf(-g)` holds for any family bounded above.

*Theorem:* $`\sup_i g(i) = -\inf_i (-g(i))` for a family bounded above

```lean
theorem neg_ciInf_neg {ι : Type} [Nonempty ι]
    (g : ι → ℝ) (hbdd : BddAbove (Set.range g)) :
    (⨆ i, g i) = - ⨅ i, - g i := by
  have hbb : BddBelow (Set.range (fun i => - g i)) := by
    obtain ⟨c, hc⟩ := hbdd
    exact ⟨-c, by
      rintro _ ⟨i, rfl⟩; simpa using hc ⟨i, rfl⟩⟩
  apply le_antisymm
  · refine ciSup_le (fun i => ?_)
    rw [le_neg]; exact ciInf_le_of_le hbb i (le_refl _)
  · rw [neg_le]; refine le_ciInf (fun i => ?_)
    rw [le_neg, neg_neg]; exact le_ciSup hbdd i
```

*Theorem:* $`(\beta \boxplus \beta)(t) = -\inf_{a + b = t} ((-\beta(a)) + (-\beta(b)))`, when finite

```lean
theorem superConv_eq_neg_iInf
    (beta : ℝ≥0 → ℝ≥0) (t : ℝ≥0)
    (hfin : (⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
        ((beta p.1.1 + beta p.1.2 : ℝ≥0) : ℝ≥0∞))
        ≠ ⊤) :
    ((superConv beta t : ℝ≥0) : ℝ)
      = - ⨅ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
            (- ((beta p.1.1 : ℝ) + (beta p.1.2 : ℝ))) := by
  have hsc : ((superConv beta t : ℝ≥0) : ℝ≥0∞)
      = ⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
          ((beta p.1.1 + beta p.1.2 : ℝ≥0) : ℝ≥0∞) :=
    superConv_coe beta t hfin
  have hbN : BddAbove (Set.range
      (fun p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t} =>
        (beta p.1.1 + beta p.1.2 : ℝ≥0))) := by
    refine ⟨superConv beta t, ?_⟩
    rintro _ ⟨p, rfl⟩
    have hle :
        ((beta p.1.1 + beta p.1.2 : ℝ≥0) : ℝ≥0∞)
        ≤ ((superConv beta t : ℝ≥0) : ℝ≥0∞) := by
      rw [hsc]
      exact le_iSup
        (fun q : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t} =>
          ((beta q.1.1 + beta q.1.2 : ℝ≥0)
            : ℝ≥0∞)) p
    exact_mod_cast hle
  have hr : superConv beta t
      = ⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
          (beta p.1.1 + beta p.1.2) := by
    rw [← ENNReal.coe_iSup hbN] at hsc
    exact_mod_cast hsc
  have hbR : BddAbove (Set.range
      (fun p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t} =>
        ((beta p.1.1 + beta p.1.2 : ℝ≥0) : ℝ))) := by
    obtain ⟨c, hc⟩ := hbN
    refine ⟨(c : ℝ), ?_⟩
    rintro _ ⟨p, rfl⟩
    exact_mod_cast hc ⟨p, rfl⟩
  simp only [← NNReal.coe_add]
  rw [← neg_ciInf_neg _ hbR,
    show (((superConv beta t : ℝ≥0)) : ℝ)
        = ((⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
            (beta p.1.1 + beta p.1.2) : ℝ≥0) : ℝ)
        from congrArg _ hr,
    NNReal.coe_iSup]
```

# The non-decreasing closure

The _non-decreasing closure_ $`\beta_{\uparrow}(t) = \sup_{u \le t}
\beta(u)` is the least non-decreasing curve above `beta`.

*Definition:* the non-decreasing closure $`\beta_{\uparrow}(t) = \sup_{u \le t} \beta(u)`

```lean
noncomputable def ndClosure (beta : ℝ≥0 → ℝ≥0) :
    ℝ≥0 → ℝ≥0 :=
  fun t => ⨆ u : {u : ℝ≥0 // u ≤ t}, beta u

instance subLeNonempty (t : ℝ≥0) :
    Nonempty {u : ℝ≥0 // u ≤ t} :=
  ⟨⟨0, by positivity⟩⟩
```

The closure dominates the curve (it is the $`u = t` term), provided the
values are bounded on each initial interval so the supremum is genuine.

*Theorem:* $`\beta \le \beta_{\uparrow}`

```lean
theorem le_ndClosure (beta : ℝ≥0 → ℝ≥0)
    (hbdd : ∀ t, BddAbove
      (Set.range (fun u : {u // u ≤ t} => beta u.1)))
    (t : ℝ≥0) : beta t ≤ ndClosure beta t := by
  unfold ndClosure
  exact le_ciSup (hbdd t) (⟨t, le_refl t⟩ : {u // u ≤ t})
```

# The super-additive closure

The _super-additive closure_ $`\bar\beta^{*}` is the supremum of all
finite iterates of the super-convolution: $`\beta^{(0)} = \beta` and
$`\beta^{(n+1)} = \beta^{(n)} \boxplus \beta^{(n)}`.

*Definition:* the iterates $`\beta^{(n)}` and the closure $`\bar\beta^{*} = \sup_n \beta^{(n)}`

```lean
noncomputable def superPow (beta : ℝ≥0 → ℝ≥0) :
    ℕ → (ℝ≥0 → ℝ≥0)
  | 0 => beta
  | n + 1 => superConv (superPow beta n)

noncomputable def saClosure (beta : ℝ≥0 → ℝ≥0) :
    ℝ≥0 → ℝ≥0 :=
  fun t => ⨆ n : ℕ, superPow beta n t
```

The closure dominates the curve (it is the $`n = 0` iterate), provided
the iterates are bounded at each point.

*Theorem:* $`\beta \le \bar\beta^{*}`

```lean
theorem le_saClosure (beta : ℝ≥0 → ℝ≥0)
    (hbdd : ∀ t,
      BddAbove (Set.range (fun n => superPow beta n t)))
    (t : ℝ≥0) : beta t ≤ saClosure beta t := by
  unfold saClosure
  exact le_ciSup (hbdd t) 0
```

```lean
end VerifiedWiki
```
