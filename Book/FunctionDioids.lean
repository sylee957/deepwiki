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
$`\overline{\mathbb{R}}_{\ge 0}` (`MinPlusNN`), whose function dioid
$`\mathcal{F}_{\min}` carries the _(min,plus) convolution_; and the
dual _(max,plus)_ carrier (`MaxPlusNN`), whose function dioid
$`\mathcal{F}_{\max}` carries the _(max,plus) convolution_. Both
convolutions are the dioid product `conv` of the generic chapter, read
back into
$`\mathbb{R}_{\ge 0}`. We name the two function dioids, define the
embeddings, and prove that each real operator equals the expected
$`\inf` / $`\sup` over the splits of $`t`.

```lean
namespace VerifiedWiki

open Algebra
open scoped Classical NNReal ENNReal Algebra.Bridge
```

# The two function dioids

Each is the generic function dioid `funCompleteDioid` instantiated at a
scalar carrier: $`\mathcal{F}_{\min}` at `MinPlusNN`, $`\mathcal{F}_{\max}`
at `MaxPlusNN`. The min-plus space $`\mathcal{F}_{\min}` is the carrier
for the rest of the development.

*Definition:* the _(min,plus)_ function space $`\mathcal{F}_{\min} = \mathbb{R}^{+} \to \overline{\mathbb{R}}_{\ge 0}`

```lean
abbrev Fmin := ℝ≥0 → MinPlusNN
```

*Definition:* the _(max,plus)_ function space $`\mathcal{F}_{\max} = \mathbb{R}^{+} \to \overline{\mathbb{R}}_{\ge 0}^{\pm}`

```lean
abbrev Fmax := ℝ≥0 → MaxPlusNN
```

# The (min,plus) convolution on the function class

The _(min,plus) convolution_ $`f \ast g` of two functions of
$`\mathcal{F}_{\min}` is their dioid product — the generic convolution
`conv` of the previous chapter, specialized to the carrier `MinPlusNN`.
Its value at $`t` is the dioid sum, over all splits $`u + s = t`, of
the product $`f(u) \otimes g(s)`; since on
$`\overline{\mathbb{R}}_{\ge 0}` the dioid sum is the numeric infimum
and the product is numeric addition, this is the familiar infimal
convolution
$$`(f \ast g)(t) = \inf_{u + s = t}\,(f(u) + g(s)).`
No new definition is needed; `conv` already _is_ this convolution on
$`\mathcal{F}_{\min}`.

*Theorem:* $`(f \ast g)(t) = \bigsqcup\,\{\, f(u) \otimes g(s) \mid u + s = t \,\}` on $`\mathcal{F}_{\min}`

```lean
example (f g : Fmin) (t : ℝ≥0) :
    conv f g t
      = CompleteDioid.sSup
          { x | ∃ u s, u + s = t ∧ x = f u ⊗ₒ g s } :=
  conv_apply f g t
```

The decomposition $`u + s = t` is the single variable $`s \le t` with
$`u = t - s`, giving the equivalent _single-variable_ form.

*Theorem:* $`(f \ast g)(t) = \bigsqcup\,\{\, f(t - s) \otimes g(s) \mid s \le t \,\}`

```lean
example (f g : Fmin) (t : ℝ≥0) :
    conv f g t
      = CompleteDioid.sSup
          { x | ∃ s : ℝ≥0,
              s ≤ t ∧ x = f (t - s) ⊗ₒ g s } :=
  conv_eq_sub f g t
```

The unit for the convolution is the impulse `convUnit`; it is a
two-sided identity on $`\mathcal{F}_{\min}`.

*Theorem:* $`\delta_0 \ast f = f`

```lean
example (f : Fmin) : conv convUnit f = f :=
  convUnit_left f
```

# A supremum-absorption lemma

A constant added to a conditionally-complete supremum is absorbed into
a bound: if $`c + f(i) \le y` for every `i`, then $`c + \bigsqcup_i f(i)
\le y`. This is the workhorse for the (max,plus) convolution bounds
below.

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
$`\mathcal{F}_{\min}` (reading off the underlying
$`\mathbb{R}_{\ge 0}^{\infty}`); for _(max,plus)_ it is into
$`\mathcal{F}_{\max}`, projecting through its underlying
`WithBot ℝ≥0∞`.

*Definition:* the _(min,plus)_ and _(max,plus)_ embeddings of a real curve

```lean
def embMin (g : ℝ≥0 → ℝ≥0) : Fmin :=
  fun t => ⟨(g t : ℝ≥0∞)⟩

def embMax (g : ℝ≥0 → ℝ≥0) : Fmax :=
  fun t => ⟨((g t : ℝ≥0∞) : WithBot ℝ≥0∞)⟩
```

Every split of `t` into $`u + s` is a nonempty set — the split
$`t + 0` — so the convolution's $`\inf` / $`\sup` is over a
nonempty index.

```lean
instance splitNonempty (t : ℝ≥0) :
    Nonempty {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t} :=
  ⟨⟨(t, 0), by simp⟩⟩
```

# The (min,plus) convolution

The _(min,plus) convolution_ $`g \ast h` (the _infimal convolution_) is
the dioid product of the embedded curves, read back into
$`\mathbb{R}_{\ge 0}`. Because the
product on $`\overline{\mathbb{R}}_{\ge 0}` is numeric addition and the
dioid supremum is the numeric infimum, the convolution at `t` is finite
(the split $`t + 0` gives $`g(t) + h(0)`), so the projection is exact.

*Definition:* $`(g \ast h)(t) = \big((\mathrm{emb}\,g \ast \mathrm{emb}\,h)(t)\big)\!\downarrow_{\mathbb{R}_{\ge 0}}`

```lean
noncomputable def minConv (g h : ℝ≥0 → ℝ≥0) :
    ℝ≥0 → ℝ≥0 :=
  fun t =>
    (conv (embMin g) (embMin h) t
      : MinPlusNN).toVal.toNNReal
```

The underlying $`\mathbb{R}_{\ge 0}^{\infty}` value of the dioid product
is the sum of the embedded values.

*Theorem:* $`\uparrow(\mathrm{emb}\,g(u) \otimes \mathrm{emb}\,h(s)) = g(u) + h(s)`

```lean
theorem embMin_mul (g h : ℝ≥0 → ℝ≥0) (u s : ℝ≥0) :
    ((embMin g u ⊗ₒ embMin h s : MinPlusNN) : ℝ≥0∞)
      = (g u : ℝ≥0∞) + (h s : ℝ≥0∞) := rfl
```

The dioid convolution unfolds to the numeric infimum over the splits:
the dioid supremum is the numeric infimum, and the product $`\otimes` is
numeric $`+`.

*Theorem:* $`\uparrow(g \ast h)(t) = \inf_{u + s = t} (g(u) + h(s))` in $`\mathbb{R}_{\ge 0}^{\infty}`

```lean
theorem conv_embMin_toE (g h : ℝ≥0 → ℝ≥0) (t : ℝ≥0) :
    ((conv (embMin g) (embMin h) t : MinPlusNN) : ℝ≥0∞)
      = ⨅ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
          ((g p.1.1 + h p.1.2 : ℝ≥0) : ℝ≥0∞) := by
  rw [conv_apply]
  show (⨅ x : {x : MinPlusNN //
        ∃ u s, u + s = t ∧ x = embMin g u ⊗ₒ embMin h s},
        (x.val : ℝ≥0∞)) = _
  apply le_antisymm
  · refine le_iInf (fun p => ?_)
    refine iInf_le_of_le
      ⟨embMin g p.1.1 ⊗ₒ embMin h p.1.2,
        p.1.1, p.1.2, p.2, rfl⟩ ?_
    show ((embMin g p.1.1 ⊗ₒ embMin h p.1.2 : MinPlusNN)
        : ℝ≥0∞) ≤ _
    rw [embMin_mul]; push_cast; rfl
  · refine le_iInf (fun x => ?_)
    obtain ⟨u, s, hus, hx⟩ := x.2
    refine iInf_le_of_le ⟨(u, s), hus⟩ ?_
    rw [show (x.val : ℝ≥0∞)
          = ((embMin g u ⊗ₒ embMin h s : MinPlusNN)
              : ℝ≥0∞) from congrArg _ hx, embMin_mul]
    push_cast; rfl
```

Projecting back, the (min,plus) convolution is the expected real
infimum.

*Theorem:* $`(g \ast h)(t) = \inf_{u + s = t} (g(u) + h(s))`

```lean
theorem minConv_eq (g h : ℝ≥0 → ℝ≥0) (t : ℝ≥0) :
    minConv g h t
      = ⨅ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
          (g p.1.1 + h p.1.2) := by
  rw [minConv, conv_embMin_toE,
    ← ENNReal.coe_iInf
      (fun p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t} =>
        g p.1.1 + h p.1.2),
    ENNReal.toNNReal_coe]
```

The (min,plus) convolution is _isotone_ in each curve: raising a curve
raises the convolution.

*Theorem:* $`g \le g' \implies A \ast g \le A \ast g'`

```lean
theorem minConv_mono_right (A : ℝ≥0 → ℝ≥0)
    {g g' : ℝ≥0 → ℝ≥0} (h : g ≤ g') :
    minConv A g ≤ minConv A g' := by
  intro t
  rw [minConv_eq, minConv_eq]
  refine ciInf_mono (OrderBot.bddBelow _) (fun p => ?_)
  gcongr
  exact h p.1.2
```

# The (max,plus) convolution

The _(max,plus) convolution_ $`g \mathbin{\overline{\ast}} h`
is the dioid product of the two embedded curves, read back into
$`\mathbb{R}_{\ge 0}`. It is the supremal mirror of the (min,plus)
convolution, over the same splits; convolving a curve with itself,
$`g \mathbin{\overline{\ast}} g` (the _super-convolution_),
generates the super-additive closure.

*Definition:* $`(g \mathbin{\overline{\ast}} h)(t) = \big((\mathrm{emb}_{\max}g \ast \mathrm{emb}_{\max}h)(t)\big)\!\downarrow_{\mathbb{R}_{\ge 0}}`

```lean
noncomputable def maxConv (g h : ℝ≥0 → ℝ≥0) :
    ℝ≥0 → ℝ≥0 :=
  fun t =>
    (conv (embMax g) (embMax h) t
      : MaxPlusNN).toVal.unbotD 0 |>.toNNReal
```

The underlying value of the dioid product is the sum of the embedded
values.

*Theorem:* $`\uparrow(\mathrm{emb}_{\max}g(a) \otimes \mathrm{emb}_{\max}h(b)) = g(a) + h(b)`

```lean
theorem embMax_mul (g h : ℝ≥0 → ℝ≥0) (a b : ℝ≥0) :
    ((embMax g a ⊗ₒ embMax h b : MaxPlusNN)
        : WithBot ℝ≥0∞)
      = (((g a : ℝ≥0∞) : WithBot ℝ≥0∞))
        + (((h b : ℝ≥0∞) : WithBot ℝ≥0∞)) := rfl
```

The dioid convolution unfolds to the supremum of
$`g(a) + h(b)` over the splits.

*Theorem:* $`\uparrow(g \mathbin{\overline{\ast}} h)(t) = \bigsqcup_{a + b = t} (g(a) + h(b))` in `WithBot ℝ≥0∞`

```lean
theorem conv_embMax_toW (g h : ℝ≥0 → ℝ≥0)
    (t : ℝ≥0) :
    ((conv (embMax g) (embMax h) t : MaxPlusNN)
        : WithBot ℝ≥0∞)
      = ⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
          (((g p.1.1 + h p.1.2 : ℝ≥0)
            : ℝ≥0∞) : WithBot ℝ≥0∞) := by
  rw [conv_apply]
  show (⨆ x : {x : MaxPlusNN //
        ∃ u s, u + s = t ∧
          x = embMax g u ⊗ₒ embMax h s},
        (x.val : WithBot ℝ≥0∞)) = _
  apply le_antisymm
  · refine iSup_le (fun x => ?_)
    obtain ⟨u, s, hus, hx⟩ := x.2
    refine le_iSup_of_le ⟨(u, s), hus⟩ ?_
    rw [show (x.val : WithBot ℝ≥0∞)
          = ((embMax g u ⊗ₒ embMax h s
                : MaxPlusNN) : WithBot ℝ≥0∞)
            from congrArg _ hx, embMax_mul]
    push_cast; rfl
  · refine iSup_le (fun p => ?_)
    refine le_iSup_of_le
      ⟨embMax g p.1.1 ⊗ₒ embMax h p.1.2,
        p.1.1, p.1.2, p.2, rfl⟩ ?_
    show _ ≤ ((embMax g p.1.1 ⊗ₒ embMax h p.1.2
        : MaxPlusNN) : WithBot ℝ≥0∞)
    rw [embMax_mul]; push_cast; rfl
```

Projecting back, the (max,plus) convolution is the expected real
supremum,
provided the values are bounded so the supremum is finite.

*Theorem:* $`\uparrow(g \mathbin{\overline{\ast}} h)(t) = \bigsqcup_{a + b = t} (g(a) + h(b))` when finite

```lean
theorem maxConv_coe (g h : ℝ≥0 → ℝ≥0) (t : ℝ≥0)
    (hfin : (⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
        ((g p.1.1 + h p.1.2 : ℝ≥0) : ℝ≥0∞)) ≠ ⊤) :
    ((maxConv g h t : ℝ≥0) : ℝ≥0∞)
      = ⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
          ((g p.1.1 + h p.1.2 : ℝ≥0) : ℝ≥0∞) := by
  have hcoe : (⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
        (((g p.1.1 + h p.1.2 : ℝ≥0) : ℝ≥0∞)
          : WithBot ℝ≥0∞))
      = (((⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
          ((g p.1.1 + h p.1.2 : ℝ≥0) : ℝ≥0∞))
          : ℝ≥0∞) : WithBot ℝ≥0∞) :=
    (WithBot.coe_iSup (OrderTop.bddAbove _)).symm
  rw [maxConv, conv_embMax_toW, hcoe]
  rw [WithBot.unbotD_coe, ENNReal.coe_toNNReal hfin]
```

The (max,plus) convolution obeys an _unconditional_ upper bound: if
every
split term is below `c`, so is the result. No finiteness is needed —
when the dioid supremum is $`+\infty` the projection floors to `0`,
which is below `c` anyway, and otherwise the bound is the genuine
supremum's. This is the bound the strict-service proofs use.

*Theorem:* $`(\forall a + b = t,\ g(a) + h(b) \le c) \implies (g \mathbin{\overline{\ast}} h)(t) \le c`

```lean
theorem maxConv_le (g h : ℝ≥0 → ℝ≥0) (t c : ℝ≥0)
    (hsplit : ∀ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
      g p.1.1 + h p.1.2 ≤ c) :
    maxConv g h t ≤ c := by
  rw [maxConv, conv_embMax_toW]
  have hcoe :
      (⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
        (((g p.1.1 + h p.1.2 : ℝ≥0)
          : ℝ≥0∞) : WithBot ℝ≥0∞))
      = (((⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
          ((g p.1.1 + h p.1.2 : ℝ≥0) : ℝ≥0∞))
          : ℝ≥0∞) : WithBot ℝ≥0∞) :=
    (WithBot.coe_iSup (OrderTop.bddAbove _)).symm
  rw [hcoe, WithBot.unbotD_coe]
  have hb : (⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
        ((g p.1.1 + h p.1.2 : ℝ≥0) : ℝ≥0∞))
        ≤ (c : ℝ≥0∞) :=
    iSup_le (fun p => by exact_mod_cast hsplit p)
  have := ENNReal.toNNReal_mono (by simp) hb
  simpa using this
```

Adding a constant absorbs into that bound, exactly as the supremum
absorption lemma did for an explicit $`\bigsqcup`: this is the shape the
strict-service-curve proofs invoke, with `c` a departure value.

*Theorem:* $`(\forall a + b = t,\ c + g(a) + g(b) \le y) \implies c + (g \mathbin{\overline{\ast}} g)(t) \le y`

```lean
theorem add_maxConv_le
    (g : ℝ≥0 → ℝ≥0) (t c y : ℝ≥0)
    (h : ∀ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
      c + (g p.1.1 + g p.1.2) ≤ y) :
    c + maxConv g g t ≤ y := by
  have hcy : c ≤ y :=
    le_trans le_self_add (h ⟨(t, 0), by simp⟩)
  have hsup : maxConv g g t ≤ y - c :=
    maxConv_le g g t (y - c)
      (fun p => le_tsub_of_add_le_left (h p))
  calc c + maxConv g g t ≤ c + (y - c) := by gcongr
    _ = y := add_tsub_cancel_of_le hcy
```

# The (max,plus) convolution as a conjugated (min,plus) convolution

The _(max,plus)_ computation is not a separate world: it is the
_(min,plus)_ convolution _conjugated by negation_. The
order-reversing involution $`x \mapsto -x` is the isomorphism between
the two dioids, turning $`\max` into $`\min` and a sum into the
negated sum. Concretely, over the reals,
$$`\sup_{a + b = t}\big(g(a) + g(b)\big) = -\inf_{a + b = t}\big((-g(a)) + (-g(b))\big),`
the right-hand infimum being a (min,plus) convolution of $`-g`. We
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

*Theorem:* $`(g \mathbin{\overline{\ast}} g)(t) = -\inf_{a + b = t} ((-g(a)) + (-g(b)))`, when finite

```lean
theorem maxConv_eq_neg_iInf
    (g : ℝ≥0 → ℝ≥0) (t : ℝ≥0)
    (hfin : (⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
        ((g p.1.1 + g p.1.2 : ℝ≥0) : ℝ≥0∞))
        ≠ ⊤) :
    ((maxConv g g t : ℝ≥0) : ℝ)
      = - ⨅ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
            (- ((g p.1.1 : ℝ) + (g p.1.2 : ℝ))) := by
  have hsc : ((maxConv g g t : ℝ≥0) : ℝ≥0∞)
      = ⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
          ((g p.1.1 + g p.1.2 : ℝ≥0) : ℝ≥0∞) :=
    maxConv_coe g g t hfin
  have hbN : BddAbove (Set.range
      (fun p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t} =>
        (g p.1.1 + g p.1.2 : ℝ≥0))) := by
    refine ⟨maxConv g g t, ?_⟩
    rintro _ ⟨p, rfl⟩
    have hle :
        ((g p.1.1 + g p.1.2 : ℝ≥0) : ℝ≥0∞)
        ≤ ((maxConv g g t : ℝ≥0) : ℝ≥0∞) := by
      rw [hsc]
      exact le_iSup
        (fun q : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t} =>
          ((g q.1.1 + g q.1.2 : ℝ≥0)
            : ℝ≥0∞)) p
    exact_mod_cast hle
  have hr : maxConv g g t
      = ⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
          (g p.1.1 + g p.1.2) := by
    rw [← ENNReal.coe_iSup hbN] at hsc
    exact_mod_cast hsc
  have hbR : BddAbove (Set.range
      (fun p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t} =>
        ((g p.1.1 + g p.1.2 : ℝ≥0) : ℝ))) := by
    obtain ⟨c, hc⟩ := hbN
    refine ⟨(c : ℝ), ?_⟩
    rintro _ ⟨p, rfl⟩
    exact_mod_cast hc ⟨p, rfl⟩
  simp only [← NNReal.coe_add]
  rw [← neg_ciInf_neg _ hbR,
    show (((maxConv g g t : ℝ≥0)) : ℝ)
        = ((⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
            (g p.1.1 + g p.1.2) : ℝ≥0) : ℝ)
        from congrArg _ hr,
    NNReal.coe_iSup]
```

# The real convolutions, self-contained

The operators above are _defined_ by computing in a dioid and projecting
back. For a reader who wants the real convolutions on their own terms,
here are the direct definitions on $`\mathbb{R}_{\ge 0}`: the _(min,plus)
convolution_ as a numeric infimum and the _(max,plus) convolution_ as a
numeric supremum, over the splits of $`t`. We then bridge each to its
dioid-backed counterpart.

*Definition:* $`(g \ast h)(t) = \inf_{u + s = t} (g(u) + h(s))`, directly on $`\mathbb{R}_{\ge 0}`

```lean
noncomputable def minConvR (g h : ℝ≥0 → ℝ≥0) :
    ℝ≥0 → ℝ≥0 :=
  fun t =>
    ⨅ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
      (g p.1.1 + h p.1.2)
```

The direct definition agrees with the dioid-backed `minConv`: this is
exactly `minConv_eq`, read as an equality of functions.

*Theorem:* $`g \ast h = \mathrm{minConv}(g, h)`

```lean
theorem minConvR_eq_minConv (g h : ℝ≥0 → ℝ≥0) :
    minConvR g h = minConv g h := by
  funext t
  rw [minConvR, minConv_eq]
```

The _(max,plus)_ convolution is the dual numeric supremum. Over
$`\mathbb{R}_{\ge 0}` an unbounded supremum is not finite, so this
direct form floors to $`0` there; the dioid-backed `maxConv`, valued in
$`\mathbb{R}_{\ge 0} \cup \{\pm\infty\}`, is the canonical operator, and
the two agree wherever the supremum is finite.

*Definition:* $`(g \mathbin{\overline{\ast}} h)(t) = \sup_{a + b = t} (g(a) + h(b))`, directly on $`\mathbb{R}_{\ge 0}`

```lean
noncomputable def maxConvR (g h : ℝ≥0 → ℝ≥0) :
    ℝ≥0 → ℝ≥0 :=
  fun t =>
    ⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
      (g p.1.1 + h p.1.2)
```

When the supremum is finite, the direct definition agrees with the
dioid-backed `maxConv`.

*Theorem:* $`g \mathbin{\overline{\ast}} h = \mathrm{maxConv}(g, h)` at $`t`, when finite

```lean
theorem maxConvR_eq_maxConv
    (g h : ℝ≥0 → ℝ≥0) (t : ℝ≥0)
    (hfin : (⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
        ((g p.1.1 + h p.1.2 : ℝ≥0) : ℝ≥0∞))
        ≠ ⊤) :
    maxConvR g h t = maxConv g h t := by
  have hbdd : BddAbove (Set.range
      (fun p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t} =>
        g p.1.1 + h p.1.2)) := by
    by_contra hub
    exact hfin (ENNReal.iSup_coe_eq_top.mpr hub)
  have h : ((maxConvR g h t : ℝ≥0) : ℝ≥0∞)
      = ((maxConv g h t : ℝ≥0) : ℝ≥0∞) := by
    rw [maxConvR, ENNReal.coe_iSup hbdd,
      maxConv_coe _ _ _ hfin]
  exact_mod_cast h
```

```lean
end VerifiedWiki
```
