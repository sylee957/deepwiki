import VersoManual
import Book.FunctionDioids

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "The sub-additive closure" =>
The _sub-additive closure_ of a curve `σ` is its Kleene star in the
function dioid: the dioid sum of all convolution powers,
$$`\sigma^{\star} = \bigsqcup_{n \ge 0} \sigma^{(n)}, \qquad \sigma^{(0)} = \delta_0,\ \ \sigma^{(n+1)} = \sigma^{(n)} \ast \sigma.`
Since the dioid sum is the numeric infimum on
$`\overline{\mathbb{R}}_{\ge 0}`, this is the familiar $`(\min, +)`
star $`\sigma^{\star} = \inf_n \sigma^{(n)}`. This chapter builds it and
develops its Kleene-star theory: the closure lies below `σ`, the powers
add under convolution, and the closure is _idempotent_ — a fixed point
of self-convolution, hence itself sub-additive.

```lean
namespace VerifiedWiki

open Algebra
open scoped Classical NNReal ENNReal Algebra.Bridge
```

# Convolution powers and the closure

The convolution unit `convUnit` — the impulse, $`e` at time `0` and
$`\varepsilon` elsewhere — is the multiplicative unit of the function
dioid. The $`n`-th convolution power iterates the convolution against
`σ`, starting from this unit; the closure is the dioid supremum over
all powers.

*Definition:* convolution powers $`\sigma^{(n)}` and the closure $`\sigma^{\star}`

```lean
noncomputable def convPow (sigma : Fmin) : ℕ → Fmin
  | 0 => convUnit
  | n + 1 => conv (convPow sigma n) sigma

noncomputable def subadditiveClosure
    (sigma : Fmin) : Fmin :=
  fun t =>
    CompleteDioid.iSup
      (fun n : ℕ => convPow sigma n t)

scoped notation:max sigma:90 "⋆" =>
  subadditiveClosure sigma
```

The first power is the curve itself.

*Theorem:* $`\sigma^{(1)} = \sigma`

```lean
theorem convPow_one (sigma : Fmin) :
    convPow sigma 1 = sigma := by
  change conv convUnit sigma = sigma
  exact convUnit_left sigma
```

# Each power lies below the closure

Each power is one of the terms of the supremum, so it lies below the
closure in the dioid order.

*Theorem:* $`\sigma^{(k)} \preceq \sigma^{\star}` pointwise

```lean
theorem convPow_le_closure
    (sigma : Fmin) (k : ℕ) (t : ℝ≥0) :
    convPow sigma k t ≼ₒ subadditiveClosure sigma t :=
  CompleteDioid.le_iSup
    (fun n : ℕ => convPow sigma n t) k
```

# Powers add under convolution

Convolving the $`m`-th and $`n`-th powers gives the $`(m+n)`-th, by
associativity of the convolution and the unit law.

*Theorem:* $`\sigma^{(m)} \ast \sigma^{(n)} = \sigma^{(m+n)}`

```lean
theorem convPow_add (sigma : Fmin) (m n : ℕ) :
    conv (convPow sigma m) (convPow sigma n)
      = convPow sigma (m + n) := by
  induction n with
  | zero =>
      show conv (convPow sigma m) convUnit
          = convPow sigma (m + 0)
      rw [convUnit_right, Nat.add_zero]
  | succ n ih =>
      show conv (convPow sigma m)
              (conv (convPow sigma n) sigma)
          = convPow sigma (m + (n + 1))
      rw [← conv_assoc, ih]
      show convPow sigma (m + n + 1) = _
      ring_nf
```

A single product of powers therefore lies below the closure: the term
$`\sigma^{(m)}(u) \otimes \sigma^{(n)}(s)` is one of the products
forming $`\sigma^{(m+n)}(u + s)`, which is below the closure.

*Theorem:* $`\sigma^{(m)}(u) \otimes \sigma^{(n)}(s) \preceq \sigma^{\star}(u + s)`

```lean
theorem convPow_term_le_closure
    (sigma : Fmin) (m n : ℕ) (u s : ℝ≥0) :
    convPow sigma m u ⊗ₒ convPow sigma n s
      ≼ₒ subadditiveClosure sigma (u + s) := by
  refine le_trans ?_
    (CompleteDioid.le_iSup
      (fun k => convPow sigma k (u + s)) (m + n))
  rw [← convPow_add, conv_apply]
  exact CompleteDioid.le_sSup _ _ ⟨u, s, rfl, rfl⟩
```

# Idempotence

The Kleene star is _idempotent_: the closure is a fixed point of
self-convolution, $`\sigma^{\star} \ast \sigma^{\star} = \sigma^{\star}`.
The inequality below distributes the convolution over the two suprema —
each cross-term $`\sigma^{(m)}(u) \otimes \sigma^{(n)}(s)` lies below
$`\sigma^{\star}(u + s)` by the previous theorem. The reverse uses the
$`u + 0` split with $`\sigma^{\star}(0) \succeq e`.

*Theorem:* $`\sigma^{\star} \ast \sigma^{\star} = \sigma^{\star}`

```lean
theorem closure_idem (sigma : Fmin) :
    conv (subadditiveClosure sigma)
        (subadditiveClosure sigma)
      = subadditiveClosure sigma := by
  funext t
  apply le_antisymm
  · rw [conv_apply]
    refine CompleteDioid.sSup_le _ _ ?_
    rintro x ⟨u, s, hus, rfl⟩
    show subadditiveClosure sigma u
        ⊗ₒ subadditiveClosure sigma s
      ≼ₒ subadditiveClosure sigma t
    dsimp only [subadditiveClosure]
    rw [CompleteDioid.mul_iSup]
    refine CompleteDioid.iSup_le _ _ (fun m => ?_)
    rw [mul_comm, CompleteDioid.mul_iSup]
    refine CompleteDioid.iSup_le _ _ (fun n => ?_)
    rw [mul_comm, ← hus]
    exact convPow_term_le_closure sigma n m u s
  · rw [conv_apply]
    refine le_trans ?_
      (CompleteDioid.le_sSup _ _
        ⟨t, 0, add_zero t, rfl⟩)
    show subadditiveClosure sigma t
      ≼ₒ subadditiveClosure sigma t
          ⊗ₒ subadditiveClosure sigma 0
    have he : eₒ ≼ₒ subadditiveClosure sigma 0 := by
      have h00 : convPow sigma 0 0 = eₒ := by
        show convUnit 0 = eₒ
        rw [convUnit, if_pos rfl]
      rw [← h00]
      exact CompleteDioid.le_iSup
        (fun n => convPow sigma n 0) 0
    calc subadditiveClosure sigma t
        = subadditiveClosure sigma t ⊗ₒ eₒ :=
          (MulMonoid.otimes_one _).symm
      _ ≼ₒ subadditiveClosure sigma t
            ⊗ₒ subadditiveClosure sigma 0 :=
          mul_le_mul_left he _
```

Idempotence says exactly that the closure is _sub-additive_ in the
dioid: a split-term of $`\sigma^{\star}(u + s)` already bounds
$`\sigma^{\star}(u) \otimes \sigma^{\star}(s)`.

*Theorem:* the closure is sub-additive, $`\sigma^{\star}(u) \otimes \sigma^{\star}(s) \preceq \sigma^{\star}(u + s)`

```lean
theorem closure_subadditive (sigma : Fmin) (u s : ℝ≥0) :
    subadditiveClosure sigma u
        ⊗ₒ subadditiveClosure sigma s
      ≼ₒ subadditiveClosure sigma (u + s) := by
  have hterm :
      subadditiveClosure sigma u
          ⊗ₒ subadditiveClosure sigma s
        ≼ₒ conv (subadditiveClosure sigma)
            (subadditiveClosure sigma) (u + s) := by
    rw [conv_apply]
    exact CompleteDioid.le_sSup _ _ ⟨u, s, rfl, rfl⟩
  rwa [closure_idem sigma] at hterm
```

```lean
end VerifiedWiki
```
