import VersoManual
import Book.SubadditiveFunctions

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "The sub-additive closure" =>
The _sub-additive closure_ of a (min,plus) function $`f` collects all of
its convolution powers into a single pointwise infimum. This is exactly
the Kleene star read inside the function dioid
$`(\mathcal{F}, \wedge, \ast)`: with $`\wedge` the dioid sum and
$`\ast` the dioid product, the closure $`f^{\ast}` is the star of $`f`
in that complete dioid. As a
consequence it inherits, for free, every property already established
generically — monotonicity, idempotence, and the least-fixed-point
characterization — applied to `FunDioid.ofFun f`.

```lean
namespace NetworkCalculus

open scoped Computability NNReal
```

# The sub-additive closure operator
The convolution powers of $`f` are $`f^0 = e`, the neutral for $`\ast`,
and $`f^{i+1} = f \ast f^i`. The _sub-additive closure_ is the pointwise
infimum of all of them,

$$`f^{\ast} = \bigwedge_{i \ge 0} f^i,`

where $`\bigwedge` is the dioid sum (the pointwise minimum of values).
Unwinding the convolution, the value of the $`n`-th power at a point is
the infimum, over all ways of writing $`t` as a sum of $`n`
sub-arguments, of the total cost:

$$`f^n(t) = \inf\Bigl\{\, \textstyle\sum_{j=1}^{n} f(u_j) \;\Big|\; \textstyle\sum_{j=1}^{n} u_j = t \,\Bigr\},`

and the closure value is the infimum of these over all $`n`,

$$`f^{\ast}(t) = \inf_{n \ge 0}\ \inf\Bigl\{\, \textstyle\sum_{j=1}^{n} f(u_j) \;\Big|\; \textstyle\sum_{j=1}^{n} u_j = t \,\Bigr\}.`

Rather than carry the $`n`-ary decomposition explicitly, the closure is
defined as the Kleene star `kstar` taken in the function dioid, on the
wrapped function `FunDioid.ofFun f`, and then read back as an ordinary
function with `.toFun`.

```lean
/-- The sub-additive closure `f* = ⨅_{i ≥ 0} fⁱ`,
    i.e. the Kleene star in the function dioid. -/
noncomputable def subClosure (f : F) : F :=
  (kstar (FunDioid.ofFun f)).toFun
```

By definition this is the star in the dioid, so the defining equation
holds by reflexivity.

```lean
theorem subClosure_eq (f : F) :
    subClosure f = (kstar (FunDioid.ofFun f)).toFun :=
  rfl

theorem subClosure_ofFun (f : F) :
    FunDioid.ofFun (subClosure f)
      = kstar (FunDioid.ofFun f) := by
  rw [subClosure_eq, FunDioid.ofFun_toFun]
```

# Inherited Kleene-star properties
Because $`f^{\ast}` is literally `kstar (FunDioid.ofFun f)`, every
generic fact about the star specializes to it by rewriting with
`subClosure_ofFun`. We record the ones that read most cleanly at the
level of `FunDioid`.

The split $`a^{\star} = e \oplus a^+` becomes, for the closure, the
identity in the function dioid, where $`f^+` is the strict closure
$`\bigwedge_{i \ge 1} f^i`.

*Theorem:* $`f^{\ast} = e \wedge f^+`

```lean
theorem subClosure_eq_one_add_kplus (f : F) :
    FunDioid.ofFun (subClosure f)
      = 1 + kplus (FunDioid.ofFun f) := by
  rw [subClosure_ofFun, kstar_eq_one_add_kplus]
```

The closure is _monotone_ for the dioid order: a smaller function has a
smaller closure.

*Theorem:* $`f \preceq g \;\Rightarrow\; f^{\ast} \preceq g^{\ast}`

```lean
theorem subClosure_mono {f g : F}
    (h : FunDioid.ofFun f ≤ FunDioid.ofFun g) :
    FunDioid.ofFun (subClosure f)
      ≤ FunDioid.ofFun (subClosure g) := by
  rw [subClosure_ofFun, subClosure_ofFun]
  exact kstar_mono h
```

The closure is _idempotent_, a closure operator in the
order-theoretic sense: applying it twice gives nothing new.

*Theorem:* $`(f^{\ast})^{\ast} = f^{\ast}`

```lean
theorem subClosure_idem (f : F) :
    subClosure (subClosure f) = subClosure f := by
  rw [subClosure_eq (subClosure f), subClosure_ofFun,
    kstar_idem, subClosure_eq]
```

Adjoining the neutral leaves the closure unchanged.

*Theorem:* $`(f \wedge e)^{\ast} = f^{\ast}`

```lean
theorem subClosure_add_one (f : F) :
    subClosure ((FunDioid.ofFun f + 1).toFun)
      = subClosure f := by
  rw [subClosure_eq, subClosure_eq,
    FunDioid.ofFun_toFun, add_one_kstar]
```

Finally, the Kleene star theorem specializes: for any $`b`, the function
$`f^{\ast} \ast b` is the _least_ solution of the affine fixed-point
equation $`x = f \ast x \wedge b`.

*Theorem:* $`f \ast (f^{\ast} \ast b) \wedge b = f^{\ast} \ast b`

```lean
theorem subClosure_mul_is_solution (f : F) (b : FunDioid) :
    FunDioid.ofFun f * (kstar (FunDioid.ofFun f) * b) + b
      = kstar (FunDioid.ofFun f) * b :=
  kstar_mul_is_solution (FunDioid.ofFun f) b
```

*Theorem:* $`f \ast x \wedge b = x \;\Rightarrow\; f^{\ast} \ast b \preceq x`

```lean
theorem subClosure_mul_least (f : F) {b x : FunDioid}
    (h : FunDioid.ofFun f * x + b = x) :
    kstar (FunDioid.ofFun f) * b ≤ x :=
  kstar_mul_le_of_solution h
```

Reading these back through `subClosure_ofFun`, the function
$`f^{\ast} \ast b` (which is `(FunDioid.ofFun (subClosure f) * b)`)
solves $`x = f \ast x \wedge b` and lies below every solution, so it is
the least one. Every property proved generically for the star thus holds
verbatim for the sub-additive closure, since the closure _is_ that star.

```lean
end NetworkCalculus
```

# The sign constraint for a strictly negative value at zero
A sub-additive function is sharply constrained once it takes a strictly
negative value at the origin. The natural numeric value at the origin is
$`f(0) = (f\,0).\mathtt{toDual}` living in $`\overline{R} = \mathbb{R}
\cup \{\pm\infty\}`, with $`-\infty` the bottom and $`+\infty` the top.
If $`f` is sub-additive and $`f(0) < 0`, then in fact $`f(0) = -\infty`,
and at every later point the value is _infinite_: either $`-\infty` or
$`+\infty`.

```lean
namespace NetworkCalculus

open scoped Computability NNReal
```

The core arithmetic fact lives in $`\overline{R}` alone: a value below
$`0` that is at most its own double must be $`-\infty`.

*Theorem:* $`x < 0 \;\wedge\; x \le x + x \;\Rightarrow\; x = -\infty` (in $`\overline{R}`)

```lean
private theorem rbar_lt_zero_self_le_add {x : Rbar}
    (hlt : x < 0) (hsub : x ≤ x + x) : x = ⊥ := by
  induction x using WithTop.recTopCoe with
  | top => exact absurd hlt (by simp)
  | coe b =>
    induction b using WithBot.recBotCoe with
    | bot => rfl
    | coe r =>
      exfalso
      rw [← WithTop.coe_add, ← WithBot.coe_add] at hsub
      have hr : r ≤ r + r := by exact_mod_cast hsub
      have hr0 : (0:ℝ) ≤ r := by linarith
      have h0 : ¬ (((r:WithBot ℝ):Rbar) < 0) := by
        simp only [not_lt]; exact_mod_cast hr0
      exact h0 hlt
```

Sub-additivity at $`(0, 0)` reads $`f(0) \le f(0) + f(0)`. Combined with
$`f(0) < 0`, the arithmetic fact gives $`f(0) = -\infty`.

*Theorem:* $`f` sub-additive $`\wedge\; f(0) < 0 \;\Rightarrow\; f(0) = -\infty`

```lean
theorem subadditive_apply_zero_neg {f : F}
    (hf : IsSubadditive f)
    (h : (f 0).toDual < 0) : (f 0).toDual = ⊥ := by
  have hsub : (f 0).toDual
      ≤ (f 0).toDual + (f 0).toDual := by
    have := hf 0 0
    rwa [add_zero] at this
  exact rbar_lt_zero_self_le_add h hsub
```

For a point $`t`, sub-additivity at $`(t, 0)` gives
$`f(t) \le f(t) + f(0) = f(t) + (-\infty)`, collapsing $`f(t)` to an
infinity.

*Theorem:* $`f` sub-additive $`\wedge\; f(0) < 0 \;\wedge\; 0 < t \;\Rightarrow\; f(t) = -\infty \;\vee\; f(t) = +\infty`

```lean
theorem subadditive_apply_pos {f : F}
    (hf : IsSubadditive f)
    (h : (f 0).toDual < 0) {t : ℝ≥0} (ht : 0 < t) :
    (f t).toDual = ⊥ ∨ (f t).toDual = ⊤ := by
  have h0 : (f 0).toDual = ⊥ :=
    subadditive_apply_zero_neg hf h
  have hsub : (f t).toDual
      ≤ (f t).toDual + (f 0).toDual := by
    have := hf t 0
    rwa [add_zero] at this
  rw [h0] at hsub
  induction hft : (f t).toDual using WithTop.recTopCoe with
  | top => exact Or.inr rfl
  | coe b =>
    induction b using WithBot.recBotCoe with
    | bot => exact Or.inl rfl
    | coe r =>
      exfalso
      rw [hft] at hsub
      rw [show ((⊥ : Rbar))
          = (((⊥ : WithBot ℝ)) : Rbar) from rfl,
        ← WithTop.coe_add, WithBot.add_bot] at hsub
      exact absurd hsub (by simp)
```

```lean
end NetworkCalculus
```

For $`t = 0` the first result already pins the value to $`-\infty`, so
together the two statements describe the whole function: a sub-additive
$`f` with $`f(0) < 0` has $`f(0) = -\infty` and is infinite everywhere,
taking only the two values $`-\infty` and $`+\infty` on $`\mathbb{R}^+`.
