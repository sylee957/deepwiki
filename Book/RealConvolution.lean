import VersoManual
import Book.FunctionDioids

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Closures of real curves" =>
The super-convolution of the previous chapter _generates_ two closures
of a real curve: the _non-decreasing closure_, the least monotone curve
above it, and the _super-additive closure_, the least super-additive
curve above it (the supremum of all finite super-convolution iterates).
Both are suprema of the curve's own values, so each dominates the curve.

```lean
namespace VerifiedWiki

open Algebra
open scoped Classical NNReal ENNReal Algebra.Bridge
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
$`\beta^{(n+1)} = \beta^{(n)} \mathbin{\overline{\ast}} \beta^{(n)}`.

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
