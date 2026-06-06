import VersoManual
import Book.FunctionDioids

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Closures of real curves" =>
The (max,plus) convolution of the previous chapter _generates_ two
closures of a real curve: the _non-decreasing closure_ $`\beta \mathbin{\overline{\ast}} 0`, the least
monotone curve above it, and the _super-additive closure_, the least
super-additive curve above it (the supremum of all finite (max,plus)
convolution iterates).
Both are suprema of the curve's own values, so each dominates the curve.

```lean
namespace DeepWiki

open Algebra
open scoped Classical NNReal ENNReal Algebra.Bridge
```

# The non-decreasing closure

The _non-decreasing closure_ $`\beta_{\uparrow}(t) = \sup_{u \le t}
\beta(u)` is the least non-decreasing curve above `beta`. It is the
generic closure `ndClosure` of the function-dioid chapter, read on the
carrier $`\mathbb{R}_{\ge 0}`: the same supremum over the initial
segment $`\{u \le t\}`, only now the values are real. Unlike the
extended reals, $`\mathbb{R}_{\ge 0}` is _conditionally_ complete, so
the suprema are genuine only where the curve is bounded on each
initial interval — every theorem here carries that hypothesis,
exactly the generic `ClosureBddAbove`. The generic `le_ndClosure`,
`ndClosure_mono`, and `ndClosure_le` instantiate directly at
$`\mathbb{R}_{\ge 0}`, so the only real-curve-specific fact to record
is the algebraic one below.

The closure is exactly the _(max,plus) convolution with the zero
curve_, $`\beta_{\uparrow} = \beta \mathbin{\overline{\ast}} 0`: a split
$`u + s = t` contributes $`\beta(u) + 0 = \beta(u)`, so ranging over the
splits of $`t` is ranging over all $`u \le t`. This is the algebraic
face of the closure — the same supremum, _generated_ by the (max,plus)
convolution rather than written out by hand. The two index sets carry
the identical range, so the equality needs no boundedness hypothesis:
where the supremum is infinite both sides floor to $`0` alike.

*Theorem:* $`\beta_{\uparrow} = \beta \mathbin{\overline{\ast}} 0`

```lean
theorem ndClosure_eq_maxConvR (beta : ℝ≥0 → ℝ≥0) :
    ndClosure beta = maxConvR beta 0 := by
  funext t
  have hrange :
      Set.range
          (fun u : {u : ℝ≥0 // u ≤ t} => beta u.1)
        = Set.range
          (fun p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t} =>
            beta p.1.1) := by
    ext x
    constructor
    · rintro ⟨⟨u, hu⟩, rfl⟩
      exact ⟨⟨(u, t - u),
        add_tsub_cancel_of_le hu⟩, rfl⟩
    · rintro ⟨⟨⟨u, s⟩, hus⟩, rfl⟩
      exact ⟨⟨u, hus ▸ le_self_add⟩, rfl⟩
  unfold ndClosure maxConvR maxConvGen
  simp only [Pi.zero_apply, add_zero]
  exact congrArg sSup hrange
```

The closure is itself non-decreasing — this is what makes it the _least
monotone curve above_ `beta`, and not merely some upper bound. Raising
the argument widens the initial interval $`\{u \le t\}` over which the
supremum is taken, so the supremum can only grow. This is exactly the
generic `ndClosure_mono`, read on $`\mathbb{R}_{\ge 0}`.

The textbook also pairs this with the _non-negative closure_
$`[\beta]^{+} = \beta \vee 0` and their composite, the non-negative
non-decreasing closure
$`[\beta]_{\uparrow}^{+} = [\beta_{\uparrow}]^{+}`. Here the curves are
valued in $`\mathbb{R}_{\ge 0}` — non-negative by construction — so
$`\beta \vee 0` is just $`\beta`, the non-negative closure adds nothing,
and the composite collapses to $`\beta_{\uparrow}`. We record the one
fact that makes this so.

*Theorem:* $`\beta \vee 0 = \beta`

```lean
theorem sup_zero_eq_self (beta : ℝ≥0 → ℝ≥0) :
    (fun t => beta t ⊔ 0) = beta := by
  funext t
  exact sup_eq_left.mpr zero_le'
```

# The super-additive closure

The _super-additive closure_ $`\bar\beta^{*}` is the supremum of all
finite iterates of the (max,plus) convolution: $`\beta^{(0)} = \beta`
and $`\beta^{(n+1)} = \beta^{(n)} \mathbin{\overline{\ast}} \beta^{(n)}`.

*Definition:* the iterates $`\beta^{(n)}` and the closure $`\bar\beta^{*} = \sup_n \beta^{(n)}`

```lean
noncomputable def maxConvPow (beta : ℝ≥0 → ℝ≥0) :
    ℕ → (ℝ≥0 → ℝ≥0)
  | 0 => beta
  | n + 1 =>
      maxConv (maxConvPow beta n) (maxConvPow beta n)

noncomputable def saClosure (beta : ℝ≥0 → ℝ≥0) :
    ℝ≥0 → ℝ≥0 :=
  fun t => ⨆ n : ℕ, maxConvPow beta n t
```

The closure dominates the curve (it is the $`n = 0` iterate), provided
the iterates are bounded at each point.

*Theorem:* $`\beta \le \bar\beta^{*}`

```lean
theorem le_saClosure (beta : ℝ≥0 → ℝ≥0)
    (hbdd : ∀ t,
      BddAbove (Set.range (fun n => maxConvPow beta n t)))
    (t : ℝ≥0) : beta t ≤ saClosure beta t := by
  unfold saClosure
  exact le_ciSup (hbdd t) 0
```

```lean
end DeepWiki
```
