import VersoManual
import Book.FunctionDioids
import Book.Additivity

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Closures" =>
The _closure_ of a curve `σ` is its Kleene star in a function dioid: the
dioid sum of all convolution powers,
$$`\sigma^{\star} = \bigsqcup_{n \ge 0} \sigma^{(n)}, \qquad \sigma^{(0)} = \delta_0,\ \ \sigma^{(n+1)} = \sigma^{(n)} \ast \sigma.`
The Kleene-star theory is purely dioidal, so we develop it once,
generically: the closure relates to `σ`, the powers add under
convolution, and the closure is _idempotent_ — a fixed point of
self-convolution.

Read on the (min,plus) dioid this is the _sub-additive closure_ (the
dioid sum is the numeric infimum, so $`\sigma^{\star} = \inf_n
\sigma^{(n)}`, and idempotence makes it sub-additive); read on the
order-dual (max,plus) dioid it is the _super-additive closure_. We then
unwrap each onto the bare values — the (min,plus) closure onto
$`\overline{\mathbb{R}}_{\ge 0}` and the (max,plus) closure onto
`WithBot ℝ≥0∞` — through the coincidence of the dioid product with the
numeric convolution.

```lean
namespace DeepWiki

open Algebra
open scoped Classical NNReal ENNReal Algebra.Bridge
```

# Convolution powers and the closure

The Kleene-star theory is purely dioidal: it uses only the convolution,
its associativity, and the unit. So we develop it _generically_ over any
function dioid $`\mathbb{R}^{+} \to T` (`T` a complete dioid, supplied
inline at each declaration), then read it on the two carriers of
interest — the (min,plus) `Fmin` for the _sub-additive_ closure, and its
order-dual (max,plus) `Fmax` for the _super-additive_ closure.

The convolution unit `convUnit` — the impulse, $`e` at time `0` and
$`\varepsilon` elsewhere — is the multiplicative unit of the function
dioid. The $`n`-th convolution power iterates the convolution against
`σ`, starting from this unit; the closure is the dioid supremum over
all powers.

*Definition:* convolution powers $`\sigma^{(n)}` and the closure $`\sigma^{\star}`

```lean
noncomputable def convPow {T : Type} [CompleteDioid T]
    (sigma : ℝ≥0 → T) : ℕ → (ℝ≥0 → T)
  | 0 => convUnit
  | n + 1 => conv (convPow sigma n) sigma

noncomputable def subadditiveClosure
    {T : Type} [CompleteDioid T]
    (sigma : ℝ≥0 → T) : ℝ≥0 → T :=
  fun t =>
    CompleteDioid.iSup
      (fun n : ℕ => convPow sigma n t)

scoped notation:max sigma:90 "⋆" =>
  subadditiveClosure sigma
```

The first power is the curve itself.

*Theorem:* $`\sigma^{(1)} = \sigma`

```lean
theorem convPow_one {T : Type} [CompleteDioid T]
    (sigma : ℝ≥0 → T) :
    convPow sigma 1 = sigma := by
  change conv convUnit sigma = sigma
  exact convUnit_left sigma
```

# Each power lies below the closure

Each power is one of the terms of the supremum, so it lies below the
closure in the dioid order.

*Theorem:* $`\sigma^{(k)} \preceq \sigma^{\star}` pointwise

```lean
theorem convPow_le_closure {T : Type} [CompleteDioid T]
    (sigma : ℝ≥0 → T) (k : ℕ) (t : ℝ≥0) :
    convPow sigma k t ≼ₒ subadditiveClosure sigma t :=
  CompleteDioid.le_iSup
    (fun n : ℕ => convPow sigma n t) k
```

# Powers add under convolution

Convolving the $`m`-th and $`n`-th powers gives the $`(m+n)`-th, by
associativity of the convolution and the unit law.

*Theorem:* $`\sigma^{(m)} \ast \sigma^{(n)} = \sigma^{(m+n)}`

```lean
theorem convPow_add {T : Type} [CompleteDioid T]
    (sigma : ℝ≥0 → T) (m n : ℕ) :
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
theorem convPow_term_le_closure {T : Type} [CompleteDioid T]
    (sigma : ℝ≥0 → T) (m n : ℕ) (u s : ℝ≥0) :
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
theorem closure_idem {T : Type} [CompleteDioid T]
    (sigma : ℝ≥0 → T) :
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
theorem closure_subadditive {T : Type} [CompleteDioid T]
    (sigma : ℝ≥0 → T) (u s : ℝ≥0) :
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

# A sub-complete-dioid is closed under the closure

The closure is assembled entirely from sub-complete-dioid operations:
the zeroth power is the unit $`e`, each next power convolves by `σ`
(the product), and the closure is the supremum of the powers. So any
subset cut out as a sub-complete-dioid — closed under the unit, the
product, and arbitrary suprema — is closed under the Kleene star too.
We prove this generically; reading it on $`\mathcal{F}^{\uparrow}`
gives that the sub-additive closure of a non-negative, non-decreasing
curve is again non-negative and non-decreasing.

*Theorem:* a sub-complete-dioid is closed under the closure

```lean
theorem Algebra.IsSubCompleteDioid.closure {T : Type}
    [CompleteDioid T] {P : (ℝ≥0 → T) → Prop}
    (h : IsSubCompleteDioid P) {sigma : ℝ≥0 → T}
    (hs : P sigma) : P (subadditiveClosure sigma) := by
  have hpow : ∀ n, P (convPow sigma n) := by
    intro n
    induction n with
    | zero => exact h.one
    | succ n ih => exact h.mul ih hs
  exact h.iSup (fun n => convPow sigma n) hpow
```

Reading this on $`\mathcal{F}^{\uparrow}` (the sub-complete-dioid
carved by non-negativity and non-decrease) gives the closure entry of
the table: $`f \in \mathcal{F}^{\uparrow} \implies f^{\star} \in
\mathcal{F}^{\uparrow}`.

*Theorem:* $`\mathcal{F}^{\uparrow}` is closed under the closure

```lean
theorem closure_mem_FNondecr (a : FminBar)
    (hn : IsNonneg (fun t => (a t).toVal))
    (hm : Monotone (fun t => (a t).toVal)) :
    IsNonneg (fun t => (subadditiveClosure a t).toVal)
      ∧ Monotone
          (fun t => (subadditiveClosure a t).toVal) :=
  isSubCompleteDioid_FNondecr.closure ⟨hn, hm⟩
```

# A closed curve is its own closure

The converse direction is the one the named curves need: a curve that is
_already closed_ — a fixed point of self-convolution dominating the unit
— equals its own Kleene-star closure. Every power then collapses onto
`σ` (by induction, using $`\sigma \ast \sigma = \sigma`), so the supremum
of the powers is `σ` itself.

*Theorem:* every power of a self-convolution fixed point lies below it

```lean
theorem convPow_le_self {T : Type} [CompleteDioid T]
    (sigma : ℝ≥0 → T) (hidem : conv sigma sigma = sigma)
    (hunit : ∀ t, convUnit (T := T) t ≼ₒ sigma t)
    (n : ℕ) (t : ℝ≥0) :
    convPow sigma n t ≼ₒ sigma t := by
  induction n generalizing t with
  | zero => exact hunit t
  | succ k ih =>
      show conv (convPow sigma k) sigma t ≼ₒ sigma t
      rw [conv_apply]
      refine CompleteDioid.sSup_le _ _ ?_
      rintro x ⟨u, s, hus, rfl⟩
      calc convPow sigma k u ⊗ₒ sigma s
          ≼ₒ sigma u ⊗ₒ sigma s := mul_le_mul_right (ih u) _
        _ ≼ₒ conv sigma sigma t := by
            rw [conv_apply, ← hus]
            exact CompleteDioid.le_sSup _ _ ⟨u, s, rfl, rfl⟩
        _ = sigma t := by rw [hidem]
```

*Theorem:* a self-convolution fixed point above the unit equals its closure

```lean
theorem subadditiveClosure_eq_self {T : Type}
    [CompleteDioid T] (sigma : ℝ≥0 → T)
    (hidem : conv sigma sigma = sigma)
    (hunit : ∀ t, convUnit (T := T) t ≼ₒ sigma t) :
    subadditiveClosure sigma = sigma := by
  funext t
  apply le_antisymm
  · exact CompleteDioid.iSup_le _ _
      (fun n => convPow_le_self sigma hidem hunit n t)
  · have := convPow_le_closure sigma 1 t
    rwa [convPow_one] at this
```

# Monotonicity of the closure

The closure is _monotone_ in its argument: a larger curve has a larger
closure. Each power is monotone in the curve (the convolution is), so
the supremum of the powers is too.

*Theorem:* $`\sigma \preceq \tau` pointwise $`\Rightarrow \sigma^{(n)} \preceq \tau^{(n)}`

```lean
theorem convPow_mono {T : Type} [CompleteDioid T]
    (sigma tau : ℝ≥0 → T)
    (h : ∀ r, sigma r ≼ₒ tau r) (n : ℕ) (t : ℝ≥0) :
    convPow sigma n t ≼ₒ convPow tau n t := by
  induction n generalizing t with
  | zero => exact le_refl _
  | succ k ih =>
      show conv (convPow sigma k) sigma t
          ≼ₒ conv (convPow tau k) tau t
      rw [conv_apply, conv_apply]
      refine CompleteDioid.sSup_le _ _ ?_
      rintro x ⟨u, s, hus, rfl⟩
      exact le_trans (mul_le_mul' (ih u) (h s))
        (CompleteDioid.le_sSup _ _ ⟨u, s, hus, rfl⟩)
```

*Theorem:* $`\sigma \preceq \tau \Rightarrow \sigma^{\star} \preceq \tau^{\star}`

```lean
theorem subadditiveClosure_mono {T : Type}
    [CompleteDioid T] (sigma tau : ℝ≥0 → T)
    (h : ∀ r, sigma r ≼ₒ tau r) (t : ℝ≥0) :
    subadditiveClosure sigma t
      ≼ₒ subadditiveClosure tau t :=
  CompleteDioid.iSup_le _ _ (fun n =>
    le_trans (convPow_mono sigma tau h n t)
      (convPow_le_closure tau n t))
```

# The sub-additive closure on the extended reals

The dioid closure above lives on `Fmin`. Read back onto the bare
extended-real values $`\overline{\mathbb{R}}_{\ge 0}` (`ℝ≥0∞`), it is
the _(min,plus)_ closure of a numeric curve $`g`: unwrap the dioid
closure of the lifted curve $`\uparrow\!g` (here `toF g`). Every
property transports through the lift `toF`, whose product coincides with
the numeric convolution `minConv` (the chapter `Additivity`).

*Definition:* the numeric sub-additive closure $`g^{\star}` on $`\overline{\mathbb{R}}_{\ge 0}`

```lean
noncomputable def subadditiveClosureE
    (g : ℝ≥0 → ℝ≥0∞) : ℝ≥0 → ℝ≥0∞ :=
  fun t => (subadditiveClosure (toF g) t).toVal
```

Lifting the numeric closure recovers the dioid closure — the bridge
that carries the theory across.

*Theorem:* $`\uparrow\!(g^{\star}) = (\uparrow\!g)^{\star}`

```lean
theorem toF_subadditiveClosureE (g : ℝ≥0 → ℝ≥0∞) :
    toF (subadditiveClosureE g)
      = subadditiveClosure (toF g) := by
  funext t; apply MinPlusNN.ext; rfl
```

The closure lies below the curve — the numeric reading of "the dioid
closure dominates `σ`" (the dioid order is the reverse of the numeric
one). It is the power-one term.

*Theorem:* $`g^{\star} \le g`

```lean
theorem subadditiveClosureE_le (g : ℝ≥0 → ℝ≥0∞)
    (t : ℝ≥0) : subadditiveClosureE g t ≤ g t := by
  have h := convPow_le_closure (toF g) 1 t
  rw [convPow_one, MinPlusNN.le_iff] at h
  exact h
```

The closure is a fixed point of (min,plus) self-convolution —
idempotence, transported through `conv_toF`.

*Theorem:* $`g^{\star} \ast g^{\star} = g^{\star}`

```lean
theorem subadditiveClosureE_idem (g : ℝ≥0 → ℝ≥0∞) :
    minConv (subadditiveClosureE g)
        (subadditiveClosureE g)
      = subadditiveClosureE g := by
  have h := closure_idem (toF g)
  rw [← toF_subadditiveClosureE, conv_toF] at h
  funext t
  exact congrArg MinPlusNN.toVal (congrFun h t)
```

Hence the closure is itself sub-additive.

*Theorem:* $`g^{\star}` is sub-additive

```lean
theorem subadditiveClosureE_subadditive
    (g : ℝ≥0 → ℝ≥0∞) :
    IsSubadditive (subadditiveClosureE g) := by
  intro u s
  have h := closure_subadditive (toF g) u s
  rw [MinPlusNN.le_iff] at h
  calc subadditiveClosureE g (u + s)
      = (subadditiveClosure (toF g) (u + s)).toVal := rfl
    _ ≤ (subadditiveClosure (toF g) u
          ⊗ₒ subadditiveClosure (toF g) s).toVal := h
    _ = subadditiveClosureE g u
          + subadditiveClosureE g s := rfl
```

Conversely, a curve that is _already_ sub-additive and null at the
origin is its own closure — the closure operator fixes exactly the
sub-additive curves. The lift `toF g` is then a self-convolution fixed
point (by `minConvE_self_of_subadditive`) above the unit, so the general
lemma applies.

*Theorem:* if $`g` is sub-additive and $`g(0) = 0` then $`g^{\star} = g`

```lean
theorem subadditiveClosureE_eq_self (g : ℝ≥0 → ℝ≥0∞)
    (hsub : IsSubadditive g) (h0 : g 0 = 0) :
    subadditiveClosureE g = g := by
  have hidem : conv (toF g) (toF g) = toF g := by
    rw [conv_toF, minConvE_self_of_subadditive g hsub h0]
  have hunit : ∀ t,
      convUnit (T := MinPlusNN) t ≼ₒ toF g t := by
    intro t
    rcases eq_or_ne t 0 with ht | ht
    · subst ht
      rw [convUnit, if_pos rfl, MinPlusNN.le_iff]
      show (toF g 0).toVal ≤ (eₒ : MinPlusNN).toVal
      simp [toF, h0]
    · rw [convUnit, if_neg ht]; exact OrderBot.bot_le _
  have hself :=
    subadditiveClosure_eq_self (toF g) hidem hunit
  funext t
  show (subadditiveClosure (toF g) t).toVal = g t
  rw [hself]; rfl
```

The numeric closure is monotone too (the dioid closure is, and the
`MinPlusNN` order reverses the numeric one, hence the lift swaps the
inequality before applying `subadditiveClosure_mono`).

*Theorem:* $`g \le h \Rightarrow g^{\star} \le h^{\star}`

```lean
theorem subadditiveClosureE_mono (g h : ℝ≥0 → ℝ≥0∞)
    (hgh : ∀ t, g t ≤ h t) (t : ℝ≥0) :
    subadditiveClosureE g t ≤ subadditiveClosureE h t := by
  show (subadditiveClosure (toF g) t).toVal
      ≤ (subadditiveClosure (toF h) t).toVal
  rw [← MinPlusNN.le_iff]
  refine subadditiveClosure_mono (toF h) (toF g) ?_ t
  intro r; rw [MinPlusNN.le_iff]; exact hgh r
```

# The super-additive closure on the dual carrier

The _super-additive_ closure is the same Kleene star, read on the
order-_dual_ (max,plus) function dioid `Fmax` — values in
`WithBot ℝ≥0∞`, where the dioid zero is $`-\infty = \bot` (the (max,plus)
convolution's identity). On the bare (min,plus) extended reals
$`\overline{\mathbb{R}}_{\ge 0}` there is no such closure, because the
(max,plus) convolution there has no identity (a curve decreasing from a
positive value at the origin would force the would-be unit below $`0`);
the $`-\infty` bottom of `WithBot ℝ≥0∞` is exactly what supplies it.

Because the generic Kleene-star theory above already applies to `Fmax`,
the super-additive closure is just `subadditiveClosure` instantiated
there, read back onto the values; the dual carrier's canonical order
_agrees_ with the numeric one, so the same theorem now reads as
_super_-additivity.

*Definition:* the lift of a `WithBot ℝ≥0∞`-valued curve into `Fmax`

```lean
def toFmax (g : ℝ≥0 → WithBot ℝ≥0∞) : Fmax :=
  fun s => ⟨g s⟩
```

*Definition:* the super-additive closure $`g^{\overline{\star}}` on the dual carrier

```lean
noncomputable def superadditiveClosure
    (g : ℝ≥0 → WithBot ℝ≥0∞) : ℝ≥0 → WithBot ℝ≥0∞ :=
  fun t => (subadditiveClosure (toFmax g) t).toVal
```

Lifting recovers the dioid closure, the bridge that carries the theory.

*Theorem:* $`\uparrow\!(g^{\overline{\star}}) = (\uparrow\!g)^{\star}` in `Fmax`

```lean
theorem toFmax_superadditiveClosure
    (g : ℝ≥0 → WithBot ℝ≥0∞) :
    toFmax (superadditiveClosure g)
      = subadditiveClosure (toFmax g) := by
  funext t; apply MaxPlusNN.ext; rfl
```

The closure lies _above_ the curve — the numeric reading of "the dioid
closure dominates `σ`", now in the dual order, which agrees with the
numeric one.

*Theorem:* $`g \le g^{\overline{\star}}`

```lean
theorem le_superadditiveClosure
    (g : ℝ≥0 → WithBot ℝ≥0∞) (t : ℝ≥0) :
    g t ≤ superadditiveClosure g t := by
  have h := convPow_le_closure (toFmax g) 1 t
  rw [convPow_one, MaxPlusNN.le_iff] at h
  exact h
```

It is a fixed point of (max,plus) self-convolution — idempotence,
instantiated at `Fmax`.

*Theorem:* $`g^{\overline{\star}} \mathbin{\overline{\ast}} g^{\overline{\star}} = g^{\overline{\star}}` in `Fmax`

```lean
theorem superadditiveClosure_idem
    (g : ℝ≥0 → WithBot ℝ≥0∞) :
    conv (subadditiveClosure (toFmax g))
        (subadditiveClosure (toFmax g))
      = subadditiveClosure (toFmax g) :=
  closure_idem (toFmax g)
```

Hence the closure is super-additive — `closure_subadditive` at `Fmax`,
whose dual order makes it the reverse inequality on the values.

*Theorem:* $`g^{\overline{\star}}` is super-additive

```lean
theorem superadditiveClosure_superadditive
    (g : ℝ≥0 → WithBot ℝ≥0∞) (u s : ℝ≥0) :
    superadditiveClosure g u + superadditiveClosure g s
      ≤ superadditiveClosure g (u + s) := by
  have h := closure_subadditive (toFmax g) u s
  rw [MaxPlusNN.le_iff] at h
  exact h
```

And conversely a curve that is already super-additive and null at the
origin is its own super-additive closure. Super-additivity here is the
`WithBot ℝ≥0∞`-valued analogue.

*Definition:* $`g` is super-additive (on `WithBot ℝ≥0∞`)

```lean
def IsSuperadditiveW (g : ℝ≥0 → WithBot ℝ≥0∞) : Prop :=
  ∀ u s : ℝ≥0, g u + g s ≤ g (u + s)
```

A super-additive curve null at the origin is a fixed point of (max,plus)
self-convolution: every split-term $`g(u) + g(s)` lies below $`g(u + s)`
by super-additivity, and the $`0 + t` split attains $`g(t)` using
$`g(0) = 0`.

*Theorem:* if $`g` is super-additive and $`g(0) = 0` then $`\uparrow\!g` is a $`\overline{\ast}`-fixed point

```lean
theorem conv_toFmax_self (g : ℝ≥0 → WithBot ℝ≥0∞)
    (hsup : IsSuperadditiveW g) (h0 : g 0 = 0) :
    conv (toFmax g) (toFmax g) = toFmax g := by
  funext t
  apply MaxPlusNN.ext
  show ((conv (toFmax g) (toFmax g) t : MaxPlusNN)
      : WithBot ℝ≥0∞) = g t
  rw [conv_apply]
  apply le_antisymm
  · rw [← MaxPlusNN.le_iff]
    refine CompleteDioid.sSup_le _ _ ?_
    rintro x ⟨u, s, hus, rfl⟩
    rw [MaxPlusNN.le_iff]
    show g u + g s ≤ g t
    rw [← hus]; exact hsup u s
  · rw [← MaxPlusNN.le_iff]
    refine le_trans ?_
      (CompleteDioid.le_sSup _ _ ⟨0, t, zero_add t, rfl⟩)
    rw [MaxPlusNN.le_iff]
    show g t ≤ g 0 + g t
    rw [h0, zero_add]
```

*Theorem:* if $`g` is super-additive and $`g(0) = 0` then $`g^{\overline{\star}} = g`

```lean
theorem superadditiveClosure_eq_self
    (g : ℝ≥0 → WithBot ℝ≥0∞)
    (hsup : IsSuperadditiveW g) (h0 : g 0 = 0) :
    superadditiveClosure g = g := by
  have hidem := conv_toFmax_self g hsup h0
  have hunit : ∀ t,
      convUnit (T := MaxPlusNN) t ≼ₒ toFmax g t := by
    intro t
    rcases eq_or_ne t 0 with ht | ht
    · subst ht
      rw [convUnit, if_pos rfl, MaxPlusNN.le_iff]
      show (eₒ : MaxPlusNN).toVal ≤ (toFmax g 0).toVal
      show (eₒ : MaxPlusNN).toVal ≤ g 0
      rw [h0]
      show (eₒ : MaxPlusNN).toVal ≤ (0 : WithBot ℝ≥0∞)
      rfl
    · rw [convUnit, if_neg ht]; exact OrderBot.bot_le _
  have hself :=
    subadditiveClosure_eq_self (toFmax g) hidem hunit
  funext t
  show (subadditiveClosure (toFmax g) t).toVal = g t
  rw [hself]; rfl
```

```lean
end DeepWiki
```
