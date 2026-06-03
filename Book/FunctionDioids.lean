import VersoManual
import Book.DioidFunctions
import Mathlib.Topology.Instances.NNReal.Lemmas

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Function dioids of real curves" =>
The function dioid $`\mathbb{R}^{+} \to T` of the previous chapter is
generic. This chapter specializes it to the two scalar carriers of
network calculus and presents the real convolution operators it yields.

Cumulative functions $`\mathbb{R}^{+} \to \mathbb{R}_{\ge 0}` embed into
two complete dioids: the _(min,plus)_ carrier
$`\overline{\mathbb{R}}_{\ge 0}` (`RplusMin`), whose function dioid
$`\mathcal{F}` carries the _infimal convolution_; and the dual
_(max,plus)_ carrier (`RplusMax`), whose function dioid
$`\mathcal{F}_{\max}` carries the _super-convolution_. Both convolutions
are the dioid product `conv` of the generic chapter, read back into
$`\mathbb{R}_{\ge 0}`. We name the two function dioids, fix the natural
order used to compare cumulative functions, define the embeddings, and
prove that each real operator equals the expected $`\bigsqcap` /
$`\bigsqcup` over the splits of $`t`.

```lean
namespace VerifiedWiki

open Algebra
open scoped Classical NNReal ENNReal Algebra.Bridge
```

# The two function dioids

Each is the generic function dioid `funCompleteDioid` instantiated at a
scalar carrier: $`\mathcal{F}` at `RplusMin`, $`\mathcal{F}_{\max}` at
`RplusMax`. The min-plus space $`\mathcal{F}` is the carrier for the
rest of the development.

*Definition:* the _(min,plus)_ function space $`\mathcal{F} = \mathbb{R}^{+} \to \overline{\mathbb{R}}_{\ge 0}`

```lean
abbrev F := ℝ≥0 → RplusMin
```

*Definition:* the _(max,plus)_ function space $`\mathcal{F}_{\max} = \mathbb{R}^{+} \to \overline{\mathbb{R}}_{\ge 0}^{\pm}`

```lean
abbrev Fmax := ℝ≥0 → RplusMax
```

# The natural order

Cumulative functions are compared in the _natural_ order: the ordinary
pointwise numeric order on their values. On $`\mathcal{F}` this is the
_reverse_ of the dioid order — for _(min,plus)_ the dioid order is the
reversed numeric order — so the two must be kept apart. The relation
`NatLe f g` looks through the `RplusMin` wrapper to the underlying
$`\overline{\mathbb{R}}_{\ge 0}^\infty` values.

*Definition:* $`f \le_n g \iff \forall t,\ f(t) \le g(t)` numerically

```lean
def NatLe (f g : F) : Prop :=
  ∀ t, (f t : ℝ≥0∞) ≤ g t

scoped notation:50 f:51 " ≤ₙ " g:51 => NatLe f g
```

The natural order is the opposite of the dioid order on each value:
$`f \le_n g` exactly when $`g(t) \preceq f(t)` for every `t`.

*Theorem:* $`f \le_n g \iff \forall t,\ g(t) \preceq f(t)`

```lean
theorem natLe_iff (f g : F) :
    f ≤ₙ g ↔ ∀ t, g t ≼ₒ f t := by
  constructor
  · intro h t
    exact (RplusMin.le_iff (g t) (f t)).mpr (h t)
  · intro h t
    exact (RplusMin.le_iff (g t) (f t)).mp (h t)
```

It is reflexive and transitive — a preorder.

*Theorem:* $`f \le_n f`

```lean
theorem NatLe.refl (f : F) : f ≤ₙ f :=
  fun _ => le_rfl
```

*Theorem:* $`f \le_n g \land g \le_n h \implies f \le_n h`

```lean
theorem NatLe.trans {f g h : F}
    (hfg : f ≤ₙ g) (hgh : g ≤ₙ h) : f ≤ₙ h :=
  fun t => le_trans (hfg t) (hgh t)
```

# A supremum-absorption lemma

A constant added to a conditionally-complete supremum is absorbed into
a bound: if $`c + f(i) \le y` for every `i`, then $`c + \bigsqcup_i f(i)
\le y`. This is the workhorse for the super-convolution bounds below.

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

# Embedding and projecting curves

A real curve embeds into either dioid by wrapping each value; the
finite result of a dioid convolution projects back to
$`\mathbb{R}_{\ge 0}`. For _(min,plus)_ the embedding is into
$`\mathcal{F}` (reading off the underlying
$`\mathbb{R}_{\ge 0}^{\infty}`); for _(max,plus)_ it is into
$`\mathcal{F}_{\max}`, projecting through `WithBot ℝ≥0∞`. We abbreviate
that underlying _(max,plus)_ type.

```lean
abbrev Rp := WithBot ℝ≥0∞
```

*Definition:* the _(min,plus)_ and _(max,plus)_ embeddings of a real curve

```lean
def embMin (g : ℝ≥0 → ℝ≥0) : F :=
  fun t => ⟨(g t : ℝ≥0∞)⟩

def embMax (g : ℝ≥0 → ℝ≥0) : Fmax :=
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

The _infimal convolution_ $`g \ast h` is the _(min,plus)_ convolution of
the embedded curves, read back into $`\mathbb{R}_{\ge 0}`. Because the
product on $`\overline{\mathbb{R}}_{\ge 0}` is numeric addition and the
dioid supremum is the numeric infimum, the convolution at `t` is finite
(the split $`t + 0` gives $`g(t) + h(0)`), so the projection is exact.

*Definition:* $`(g \ast h)(t) = \big((\mathrm{emb}\,g \ast \mathrm{emb}\,h)(t)\big)\!\downarrow_{\mathbb{R}_{\ge 0}}`

```lean
noncomputable def infConvR (g h : ℝ≥0 → ℝ≥0) :
    ℝ≥0 → ℝ≥0 :=
  fun t =>
    (conv (embMin g) (embMin h) t
      : RplusMin).toE.toNNReal
```

The underlying $`\mathbb{R}_{\ge 0}^{\infty}` value of the dioid product
is the sum of the embedded values.

*Theorem:* $`\uparrow(\mathrm{emb}\,g(u) \otimes \mathrm{emb}\,h(s)) = g(u) + h(s)`

```lean
theorem embMin_mul (g h : ℝ≥0 → ℝ≥0) (u s : ℝ≥0) :
    ((embMin g u ⊗ₒ embMin h s : RplusMin) : ℝ≥0∞)
      = (g u : ℝ≥0∞) + (h s : ℝ≥0∞) := rfl
```

The dioid convolution unfolds to the numeric infimum over the splits:
the dioid supremum is the numeric infimum, and the product $`\otimes` is
numeric $`+`.

*Theorem:* $`\uparrow(g \ast h)(t) = \bigsqcap_{u + s = t} (g(u) + h(s))` in $`\mathbb{R}_{\ge 0}^{\infty}`

```lean
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

The _super-convolution_ $`\beta \boxplus \beta` is the _(max,plus)_
convolution of `beta` with itself, read back into
$`\mathbb{R}_{\ge 0}`. It is the supremal mirror of the infimal
convolution, over the same splits.

*Definition:* $`(\beta \boxplus \beta)(t) = \big((\mathrm{emb}_{\max}\beta \ast \mathrm{emb}_{\max}\beta)(t)\big)\!\downarrow_{\mathbb{R}_{\ge 0}}`

```lean
noncomputable def superConv (beta : ℝ≥0 → ℝ≥0) :
    ℝ≥0 → ℝ≥0 :=
  fun t =>
    (conv (embMax beta) (embMax beta) t
      : RplusMax).toW.unbotD 0 |>.toNNReal
```

The underlying value of the dioid product is the sum of the embedded
values.

*Theorem:* $`\uparrow(\mathrm{emb}_{\max}\beta(a) \otimes \mathrm{emb}_{\max}\beta(b)) = \beta(a) + \beta(b)`

```lean
theorem embMax_mul (beta : ℝ≥0 → ℝ≥0) (a b : ℝ≥0) :
    ((embMax beta a ⊗ₒ embMax beta b : RplusMax) : Rp)
      = (((beta a : ℝ≥0∞) : Rp))
        + (((beta b : ℝ≥0∞) : Rp)) := rfl
```

The dioid convolution unfolds to the supremum of $`\beta(a) + \beta(b)`
over the splits.

*Theorem:* $`\uparrow(\beta \boxplus \beta)(t) = \bigsqcup_{a + b = t} (\beta(a) + \beta(b))` in `WithBot ℝ≥0∞`

```lean
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

*Theorem:* $`\uparrow(\beta \boxplus \beta)(t) = \bigsqcup_{a + b = t} (\beta(a) + \beta(b))` when finite

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

The _(max,plus)_ computation is not a separate world: it is the
_(min,plus)_ infimal convolution _conjugated by negation_. The
order-reversing involution $`x \mapsto -x` is the isomorphism between
the two dioids, turning $`\max` into $`\min` and a sum into the
negated sum. Concretely, over the reals,
$$`\sup_{a + b = t}\big(\beta(a) + \beta(b)\big) = -\inf_{a + b = t}\big((-\beta(a)) + (-\beta(b))\big),`
the right-hand infimum being an infimal convolution of $`-\beta`. We
record this duality as one theorem; the standalone _(max,plus)_ dioid
is kept as the computational engine, while this lemma is the honest
statement of _why_ it is the right one. The supremal conjugation
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

```lean
end VerifiedWiki
```
