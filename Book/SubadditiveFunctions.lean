import VersoManual
import Book.SubadditiveClosure

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Sub-additive functions" =>
A (min,plus) function is _sub-additive_ when its value on a sum is no
larger than the sum of its values. This chapter formalizes that
predicate and proves its two stability properties: sub-additivity is
preserved by the pointwise numeric sum of functions and by the
convolution. The order at play throughout is the _natural_ (numeric)
order on $`\overline{R}_{\min}`, which is the reverse of the dioid order
$`\preceq`; we state every inequality directly on the underlying
numeric values via `.toDual`, with numeric addition $`+` on
$`\overline{R} = \mathbb{R} \cup \{\pm\infty\}`.

```lean
namespace NetworkCalculus

open scoped Computability NNReal
```

# The sub-additivity predicate
A function $`f \in \mathcal{F}` is _sub-additive_ when
$`f(s + t) \le f(s) + f(t)` for all $`s, t \ge 0`, where $`\le` and
$`+` are the natural numeric order and numeric addition. Recording this
on `.toDual` values keeps the statement in the natural order rather than
the reversed dioid order.

```lean
/-- Sub-additive: `f(s+t) ≤ f(s) + f(t)` numerically. -/
def IsSubadditive (f : F) : Prop :=
  ∀ s t, (f (s + t)).toDual
    ≤ (f s).toDual + (f t).toDual
```

Many functions of interest are sub-additive. A constant function
$`f : t \mapsto c` is sub-additive exactly when $`0 \le c`, since the
condition reduces to $`c \le c + c`. The affine _rate-latency_ shapes
$`f : t \mapsto \sigma + \rho t` with $`\sigma \ge 0` are sub-additive,
as is the ceiling function $`t \mapsto \lceil t \rceil`.

Sub-additivity is _not_ stable under the dioid sum $`\wedge` (pointwise
minimum). For instance, both $`t \mapsto \lceil t \rceil` and
$`t \mapsto 2t` are sub-additive, but their minimum
$`t \mapsto \min(\lceil t \rceil, 2t)` is not: evaluating at well-chosen
points (such as $`s = t = \tfrac12`) makes the value on the sum exceed
the sum of the values, so the sub-additive inequality fails. This is in
sharp contrast with the stability under the pointwise numeric sum and
under the convolution proved below.

# Stability under the pointwise numeric sum
The _pointwise numeric sum_ of two functions adds their underlying
numeric values point by point; it is the function-space addition $`+`
read in the natural order, _not_ the dioid sum $`\wedge`. We name it
`padd` to keep it distinct from the dioid `+`.

```lean
/-- Pointwise numeric sum `(f + g)(t) = f(t) + g(t)`. -/
noncomputable def padd (f g : F) : F :=
  fun t => MinPlus.D.ofDual ((f t).toDual + (g t).toDual)
```

The pointwise numeric sum of two sub-additive functions is again
sub-additive. Unfolding `padd` on `.toDual`, the goal becomes
$`f(s+t) + g(s+t) \le (f(s) + f(t)) + (g(s) + g(t))`; bounding each
summand by sub-additivity and commuting the four terms finishes it. The
carrier $`\overline{R}` is not a ring, so the rearrangement uses
`add_add_add_comm` rather than `ring`.

```lean
theorem padd_subadditive {f g : F}
    (hf : IsSubadditive f) (hg : IsSubadditive g) :
    IsSubadditive (padd f g) := by
  intro s t
  show ((f (s+t)).toDual + (g (s+t)).toDual)
     ≤ ((f s).toDual + (g s).toDual)
       + ((f t).toDual + (g t).toDual)
  calc (f (s+t)).toDual + (g (s+t)).toDual
      ≤ ((f s).toDual + (f t).toDual)
        + ((g s).toDual + (g t).toDual) := by
        gcongr <;> [exact hf s t; exact hg s t]
    _ = ((f s).toDual + (g s).toDual)
        + ((f t).toDual + (g t).toDual) :=
        add_add_add_comm _ _ _ _
```

# Stability under the convolution
The convolution of two sub-additive functions is sub-additive. The
cleanest route works in the _dioid_ order. Because the natural order is
the reverse of $`\preceq` and numeric addition is the dioid product
$`\otimes`, the natural-order goal
$$`(f \ast g)(s+t) \le (f \ast g)(s) + (f \ast g)(t)`
is the same as the dioid inequality
$$`(f \ast g)(s) \otimes (f \ast g)(t) \preceq (f \ast g)(s+t).`

We prove the dioid inequality first. Both convolution values are least
upper bounds over decompositions, so by lower semi-continuity their
product expands to a least upper bound over _pairs_ of decompositions;
it suffices to bound each such term by $`(f \ast g)(s+t)`. Writing
$`s = u + v` and $`t = w + z`, the relevant rearrangement is
$$`(f(u) \otimes g(v)) \otimes (f(w) \otimes g(z)) = (f(u) \otimes f(w)) \otimes (g(v) \otimes g(z)).`
Sub-additivity of $`f` and $`g`, read in the dioid order, gives
$`f(u) \otimes f(w) \preceq f(u+w)` and
$`g(v) \otimes g(z) \preceq g(v+z)`; isotony of $`\otimes` then bounds
the product by $`f(u+w) \otimes g(v+z)`, which is below
$`(f \ast g)(s+t)` via the decomposition $`(u+w) + (v+z) = s+t`.

The first ingredient is the dioid form of sub-additivity: numeric
$`f(s+t) \le f(s) + f(t)` is, on the reversed order, the dioid bound
$`f(s) \otimes f(t) \preceq f(s+t)`.

```lean
theorem subadditive_mul_le {f : F}
    (hf : IsSubadditive f) (s t : ℝ≥0) :
    f s * f t ≤ f (s + t) :=
  (MinPlus.D.le_def _ _).mpr (hf s t)
```

The single-pair bound: for decompositions $`s = u + v` and
$`t = w + z`, the term $`(f(u) \otimes g(v)) \otimes (f(w) \otimes g(z))`
lies below $`(f \ast g)(s+t)`.

```lean
theorem conv_term_le {f g : F}
    (hf : IsSubadditive f) (hg : IsSubadditive g)
    {s t u v w z : ℝ≥0}
    (hs : u + v = s) (ht : w + z = t) :
    (f u * g v) * (f w * g z) ≤ (f ∗ g) (s + t) := by
  have hdec : (u + w) + (v + z) = s + t := by
    rw [← hs, ← ht]; ac_rfl
  calc (f u * g v) * (f w * g z)
      = (f u * f w) * (g v * g z) := by ac_rfl
    _ ≤ f (u + w) * g (v + z) := by
        exact le_trans
          (Dioid.mul_le_mul_right'
            (subadditive_mul_le hf u w) _)
          (Dioid.mul_le_mul_left'
            (subadditive_mul_le hg v z) _)
    _ ≤ (f ∗ g) (s + t) := conv_ge f g hdec
```

Expanding the product of the two convolution values over all pairs of
decompositions and applying the single-pair bound term by term gives
the dioid inequality.

```lean
theorem conv_mul_conv_le {f g : F}
    (hf : IsSubadditive f) (hg : IsSubadditive g)
    (s t : ℝ≥0) :
    (f ∗ g) s * (f ∗ g) t ≤ (f ∗ g) (s + t) := by
  rw [conv_apply f g s, conv_apply f g t,
    CompleteDioid.iSup_mul]
  refine iSup_le fun p => ?_
  obtain ⟨⟨u, v⟩, huv⟩ := p
  rw [CompleteDioid.mul_iSup]
  refine iSup_le fun q => ?_
  obtain ⟨⟨w, z⟩, hwz⟩ := q
  exact conv_term_le hf hg huv hwz
```

Converting the dioid inequality back to the natural order — through
`MinPlus.D.le_def` and the identity
$`(a \otimes b).\mathtt{toDual} = a.\mathtt{toDual} + b.\mathtt{toDual}`
— yields sub-additivity of the convolution.

```lean
theorem conv_subadditive {f g : F}
    (hf : IsSubadditive f) (hg : IsSubadditive g) :
    IsSubadditive (f ∗ g) := by
  intro s t
  exact (MinPlus.D.le_def _ _).mp
    (conv_mul_conv_le hf hg s t)
```

# Adding a non-negative constant
A constant function $`t \mapsto k` is sub-additive precisely when its
value is non-negative: the defining inequality reduces to
$`k \le k + k`, equivalent to $`0 \le k`.

```lean
theorem const_subadditive {k : RbarMin}
    (hk : 0 ≤ k.toDual) :
    IsSubadditive (fun _ => k) := by
  intro _ _
  show k.toDual ≤ k.toDual + k.toDual
  calc k.toDual = 0 + k.toDual := (zero_add _).symm
    _ ≤ k.toDual + k.toDual := by gcongr
```

Adding such a non-negative constant to a sub-additive function keeps it
sub-additive: this is stability under the pointwise numeric sum, with
the second summand a non-negative constant. Modelling $`f + k` as
`padd f (fun _ => k)` makes it an immediate corollary.

```lean
theorem padd_const_subadditive {f : F} {k : RbarMin}
    (hf : IsSubadditive f) (hk : 0 ≤ k.toDual) :
    IsSubadditive (padd f (fun _ => k)) :=
  padd_subadditive hf (const_subadditive hk)

end NetworkCalculus
```

These two stability results — under the pointwise numeric sum and under
the convolution — together with the constant corollary, are the
structural facts that make the sub-additive functions a well-behaved
family in the (min,plus) algebra.
