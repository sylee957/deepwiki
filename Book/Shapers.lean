import VersoManual
import Book.LeftContinuity
import Book.SubadditiveClosure

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Shapers" =>
A shaper is a server whose output is constrained by an arrival
curve. In the concrete min-plus setting, cumulative functions use the
ordinary numeric order on their values, while the scalar dioid order is
the reverse order. This chapter keeps that distinction explicit.

```lean
namespace NetworkCalculus

open Algebra
open scoped Classical NNReal ENNReal Algebra.Bridge
```

# Cumulative functions and servers

The ambient function dioid is `F`. Cumulative functions — the arrivals
and departures of a server — are honest real curves
$`\mathbb{R}^{+} \to \mathbb{R}_{\ge 0}`, coerced into `F` when the
convolution is needed. The relation `NatLe f g` is the ordinary
pointwise numeric order, obtained by looking through the `RplusMin`
wrapper.

*Definition:* cumulative functions as real curves, and their natural order

A _cumulative function_ — the arrival or departure of a server — is an
honest real curve $`\mathbb{R}^{+} \to \mathbb{R}_{\ge 0}`. We name the
type `Curve`. Its values are non-negative reals, so it is automatically
finite; the network-calculus regularity — monotone, left-continuous,
zero at the origin — is carried as explicit hypotheses on the results
that need it, rather than bundled into the carrier.

```lean
abbrev Curve := ℝ≥0 → ℝ≥0
```

A curve coerces into the function dioid `F` by wrapping each value into
`RplusMin`; this is how the convolution-based statements reach it.

*Definition:* a real curve as a dioid function

```lean
instance : Coe Curve F where
  coe := fun A t => ⟨(A t : ℝ≥0∞)⟩

def IsFiniteFunction (f : F) : Prop :=
  ∀ t, (f t : ℝ≥0∞) ≠ ⊤

theorem curve_finite (A : Curve) :
    IsFiniteFunction (↑A : F) := by
  intro t
  show ((A t : ℝ≥0∞)) ≠ ⊤
  simp
```

The natural-order relation `NatLe f g` is the ordinary pointwise
numeric order on `F`, obtained by looking through the `RplusMin`
wrapper.

```lean
def NatLe (f g : F) : Prop :=
  ∀ t, (f t : ℝ≥0∞) ≤ g t

scoped notation:50 f:51 " ≤ₙ " g:51 => NatLe f g
```

The natural order is the opposite of the dioid order on each value.

*Theorem:* $`f \le_n g \iff \forall t,\ g(t) \preceq f(t)`, with $`\le_n` reflexive and transitive

```lean
theorem natLe_iff (f g : F) :
    f ≤ₙ g ↔ ∀ t, g t ≼ₒ f t := by
  constructor
  · intro h t
    exact (RplusMin.le_iff (g t) (f t)).mpr (h t)
  · intro h t
    exact (RplusMin.le_iff (g t) (f t)).mp (h t)

theorem NatLe.refl (f : F) : f ≤ₙ f :=
  fun _ => le_rfl

theorem NatLe.trans {f g h : F}
    (hfg : f ≤ₙ g) (hgh : g ≤ₙ h) : f ≤ₙ h :=
  fun t => le_trans (hfg t) (hgh t)
```

An output cumulative function allows `sigma` as an arrival curve when
it lies below its convolution with `sigma`.

*Definition:* `D` allows `sigma` as an arrival curve

```lean
def AllowsArrivalCurve (D sigma : F) : Prop :=
  D ≤ₙ conv D sigma
```

The defining inequality is equivalent to a kernel inequality for every
split `u + s = t`. This form is the workhorse for the closure result.

*Theorem:* $`D \text{ allows } \sigma \iff \forall\, u+s=t,\ D(u) \otimes \sigma(s) \preceq D(t)`

```lean
theorem allowsArrivalCurve_iff_kernel
    (D sigma : F) :
    AllowsArrivalCurve D sigma ↔
      ∀ u s t, u + s = t →
        D u ⊗ₒ sigma s ≼ₒ D t := by
  constructor
  · intro h u s t hus
    have hc : conv D sigma t ≼ₒ D t :=
      (natLe_iff D (conv D sigma)).mp h t
    have hterm :
        D u ⊗ₒ sigma s ≼ₒ conv D sigma t := by
      rw [conv_apply]
      exact CompleteDioid.le_sSup _ _
        ⟨u, s, hus, rfl⟩
    exact le_trans hterm hc
  · intro h
    unfold AllowsArrivalCurve
    rw [natLe_iff]
    intro t
    rw [conv_apply]
    refine CompleteDioid.sSup_le _ _ ?_
    rintro x ⟨u, s, hus, rfl⟩
    exact h u s t hus
```

Monotonicity is stated in the natural order: increasing the arrival
curve can only increase the convolution.

*Theorem:* $`\sigma \le_n \sigma' \implies D \ast \sigma \le_n D \ast \sigma'`

```lean
theorem conv_natLe_right (D : F) {sigma sigma' : F}
    (h : sigma ≤ₙ sigma') :
    conv D sigma ≤ₙ conv D sigma' := by
  rw [natLe_iff]
  intro t
  rw [conv_apply]
  refine CompleteDioid.sSup_le _ _ ?_
  rintro x ⟨u, s, hus, rfl⟩
  rw [conv_apply]
  refine le_trans ?_
    (CompleteDioid.le_sSup _ _
      ⟨u, s, hus, rfl⟩)
  exact mul_le_mul_left
    ((natLe_iff sigma sigma').mp h s) (D u)
```

A server is a set of admissible input-output pairs of cumulative
functions, _bundled with_ its causality proof: every pair has its
departure below its arrival, `D ≤ A`. Causality is thus intrinsic to
being a server. Left-totality and the shaper condition are stated
separately.

*Definition:* servers and sigma-shapers

A `Server` bundles the input-output relation with the _causality_
proof: every admissible pair has its departure below its arrival,
$`D \le_n A`. Causality is thus part of being a server, not a separate
predicate — a `Server` is causal by construction.

```lean
structure Server where
  rel : Set (Curve × Curve)
  causal : ∀ p ∈ rel, (↑p.2 : F) ≤ₙ (↑p.1 : F)

instance : Membership (Curve × Curve) Server where
  mem S p := p ∈ S.rel

def Serves (S : Server) (A D : Curve) : Prop :=
  (A, D) ∈ S

scoped notation:50 A:51 " ⟶[" S "] " D:51 =>
  Serves S A D

theorem causal_of_mem (S : Server)
    {p : Curve × Curve} (hp : p ∈ S) :
    (↑p.2 : F) ≤ₙ (↑p.1 : F) :=
  S.causal p hp

def IsLeftTotalServer (S : Server) : Prop :=
  ∀ A : Curve, ∃ D : Curve, A ⟶[S] D

def IsShaper (S : Server) (sigma : F) : Prop :=
  ∀ p ∈ S, AllowsArrivalCurve (↑p.2 : F) sigma
```

The largest causal server satisfying the shaper constraint is the set
of all pairs whose output is below the input and whose output allows
`sigma` as an arrival curve.

*Definition:* the largest `sigma`-shaper server

```lean
def shaperServer (sigma : F) : Server where
  rel := { p | (↑p.2 : F) ≤ₙ (↑p.1 : F) ∧
      AllowsArrivalCurve (↑p.2 : F) sigma }
  causal p hp := hp.1

theorem mem_shaperServer_iff
    {sigma : F} {p : Curve × Curve} :
    p ∈ shaperServer sigma ↔
      (↑p.2 : F) ≤ₙ (↑p.1 : F) ∧
        AllowsArrivalCurve (↑p.2 : F) sigma :=
  Iff.rfl
```

A server lies inside the largest `sigma`-shaper exactly when it is a
`sigma`-shaper — the causality conjunct is automatic, since a server is
causal by construction.

*Theorem:* $`S \subseteq S_{\mathrm{sh}}(\sigma) \iff S` is a $`\sigma`-shaper

```lean
theorem subset_shaperServer_iff
    {S : Server} {sigma : F} :
    (∀ p ∈ S, p ∈ shaperServer sigma) ↔
      IsShaper S sigma := by
  constructor
  · intro h p hp
    exact (h p hp).2
  · intro h p hp
    exact ⟨causal_of_mem S hp, h p hp⟩
```

# Shaping closure

The _sub-additive closure_ $`\sigma^{\star}`, its convolution powers
`convPow`, and the Kleene-star theory were developed in the chapter
`The sub-additive closure`. Here we relate the closure to the shaper
constructions through the natural order and the arrival-curve kernel.

The closure is below the original curve in the natural order because
the original curve is one of the powers.

*Theorem:* $`\sigma^\star \le_n \sigma`

```lean
theorem subadditiveClosure_natLe_self
    (sigma : F) : sigma⋆ ≤ₙ sigma := by
  intro t
  have h :
      sigma t ≼ₒ subadditiveClosure sigma t := by
    dsimp [subadditiveClosure]
    have h1 :
        convPow sigma 1 t ≼ₒ
          CompleteDioid.iSup
            (fun n : ℕ => convPow sigma n t) :=
      CompleteDioid.le_iSup
        (fun n : ℕ => convPow sigma n t) 1
    simpa [convPow_one] using h1
  exact (RplusMin.le_iff (sigma t)
    (subadditiveClosure sigma t)).mp h
```

The kernel inequality propagates along every convolution power.

*Theorem:* if $`D` allows $`\sigma`, then $`\forall\, u+s=t,\ D(u) \otimes \sigma^{\ast n}(s) \preceq D(t)`

```lean
theorem kernel_convUnit (D : F) :
    ∀ u s t, u + s = t →
      D u ⊗ₒ convUnit s ≼ₒ D t := by
  intro u s t hus
  by_cases hs : s = 0
  · have hu : u = t := by
      rw [← hus, hs, add_zero]
    rw [convUnit, if_pos hs, hu]
    exact le_of_eq
      (Algebra.MulMonoid.otimes_one (D t))
  · rw [convUnit, if_neg hs]
    rw [Algebra.Semiring.otimes_eps]
    exact bot_le

theorem kernel_convPow_of_allows
    {D sigma : F}
    (hD : AllowsArrivalCurve D sigma) :
    ∀ n u s t, u + s = t →
      D u ⊗ₒ convPow sigma n s ≼ₒ D t := by
  have hsigma :=
    (allowsArrivalCurve_iff_kernel D sigma).mp hD
  intro n
  induction n with
  | zero =>
      exact kernel_convUnit D
  | succ n ih =>
      intro u s t hus
      rw [convPow, conv_apply,
        CompleteDioid.mul_sSup]
      refine CompleteDioid.sSup_le _ _ ?_
      rintro x ⟨y, ⟨a, b, hab, rfl⟩, rfl⟩
      change D u ⊗ₒ
          (convPow sigma n a ⊗ₒ sigma b) ≼ₒ D t
      rw [← Algebra.MulMonoid.otimes_assoc]
      have hleft :
          (D u ⊗ₒ convPow sigma n a) ⊗ₒ
              sigma b ≼ₒ
            D (u + a) ⊗ₒ sigma b :=
        mul_le_mul_right (ih u a (u + a) rfl)
          (sigma b)
      have hsum : (u + a) + b = t := by
        rw [add_assoc, hab, hus]
      exact le_trans hleft
        (hsigma (u + a) b t hsum)
```

Therefore allowing `sigma` and allowing its closure are equivalent.

*Theorem:* $`D \text{ allows } \sigma^\star \iff D \text{ allows } \sigma`

```lean
theorem allowsArrivalCurve_closure_iff
    (D sigma : F) :
    AllowsArrivalCurve D sigma⋆ ↔
      AllowsArrivalCurve D sigma := by
  constructor
  · intro h
    exact NatLe.trans h
      (conv_natLe_right D
        (subadditiveClosure_natLe_self sigma))
  · intro h
    rw [allowsArrivalCurve_iff_kernel]
    intro u s t hus
    rw [subadditiveClosure,
      CompleteDioid.mul_iSup]
    refine CompleteDioid.iSup_le _ _ ?_
    intro n
    exact kernel_convPow_of_allows h n u s t hus
```

# Properties of shapers

The largest `sigma`-shaper is unchanged by replacing `sigma` with its
closure.

*Theorem:* $`S_{\mathrm{sh}}(\sigma) = S_{\mathrm{sh}}(\sigma^\star)`

```lean
theorem shaperServer_closure
    (sigma : F) :
    (shaperServer sigma).rel =
      (shaperServer sigma⋆).rel := by
  ext p
  constructor
  · intro hp
    exact ⟨hp.1,
      (allowsArrivalCurve_closure_iff
        (↑p.2 : F) sigma).2 hp.2⟩
  · intro hp
    exact ⟨hp.1,
      (allowsArrivalCurve_closure_iff
        (↑p.2 : F) sigma).1 hp.2⟩

theorem IsShaper.closure
    {S : Server} {sigma : F}
    (hS : IsShaper S sigma) :
    IsShaper S sigma⋆ := by
  intro p hp
  exact (allowsArrivalCurve_closure_iff
    (↑p.2 : F) sigma).2 (hS p hp)

example
    (sigma : F) :
    (shaperServer sigma).rel =
      (shaperServer sigma⋆).rel :=
  shaperServer_closure sigma

example
    {S : Server} {sigma : F}
    (hS : IsShaper S sigma) :
    IsShaper S sigma⋆ :=
  IsShaper.closure hS
```

Larger arrival curves preserve the shaper property, and their largest
servers contain the smaller-curve largest server.

*Theorem:* if $`\sigma \le_n \sigma'`, then $`S_{\mathrm{sh}}(\sigma) \subseteq S_{\mathrm{sh}}(\sigma')`

```lean
theorem IsShaper.of_natLe
    {S : Server}
    {sigma sigma' : F}
    (hS : IsShaper S sigma)
    (h : sigma ≤ₙ sigma') :
    IsShaper S sigma' := by
  intro p hp
  exact NatLe.trans (hS p hp)
    (conv_natLe_right (↑p.2 : F) h)

theorem shaperServer_mono
    {sigma sigma' : F}
    (h : sigma ≤ₙ sigma') :
    (shaperServer sigma).rel ⊆
      (shaperServer sigma').rel := by
  intro p hp
  exact ⟨hp.1,
    NatLe.trans hp.2
      (conv_natLe_right (↑p.2 : F) h)⟩

example
    {sigma sigma' : F}
    (h : sigma ≤ₙ sigma') :
    (shaperServer sigma).rel ⊆
      (shaperServer sigma').rel :=
  shaperServer_mono h

example
    {S : Server} {sigma sigma' : F}
    (hS : IsShaper S sigma)
    (h : sigma ≤ₙ sigma') :
    IsShaper S sigma' :=
  IsShaper.of_natLe hS h
```

# The greedy shaper

A _shaper_ constrains its output to allow `sigma` as an arrival curve.
A _greedy_ shaper does more: it shapes the output as tightly as
possible, fixing it to be exactly the convolution of the input with
`sigma`. Each output is then `sigma`-constrained by construction, and
the shaper is _greedy_ in that it delays the input no more than
forced.

The relation itself places no constraint on `sigma`: a server is a
`sigma`-greedy shaper when every admissible pair has output exactly the
convolution of the input with `sigma`. The regularity of `sigma` —
sub-additivity, left-continuity, nullity at the origin — enters only
where it is needed: to make the greedy shaper a well-defined _server_
(its output causal and a valid cumulative function).

A server is a `sigma`-greedy shaper when every admissible pair has
output exactly the convolution of the input with `sigma`.

*Definition:* $`S \text{ is a } \sigma\text{-greedy shaper} \iff \forall (A, D) \in S,\ D = A \ast \sigma`

```lean
def IsGreedyShaper
    (S : Server) (sigma : F) : Prop :=
  ∀ p ∈ S, (↑p.2 : F) = conv (↑p.1 : F) sigma
```

To form the greedy shaper _as a server_, its output must be causal —
the departure below the arrival, $`A \ast \sigma \le_n A`. This holds
exactly when `sigma` is null at the origin: the split $`t = t + 0`
contributes the term $`A(t) \otimes \sigma(0) = A(t)`, so the
convolution never exceeds `A`. Sub-additivity and left-continuity are
not needed for causality; nullity at the origin is.

*Theorem:* if $`\sigma(0) = e` then $`A \ast \sigma \le_n A`

```lean
theorem conv_natLe_self_of_zeroAtOrigin
    (A sigma : F) (h0 : sigma 0 = eₒ) :
    conv A sigma ≤ₙ A := by
  rw [natLe_iff]
  intro t
  rw [conv_apply]
  refine le_trans ?_
    (CompleteDioid.le_sSup _ _
      ⟨t, 0, add_zero t, rfl⟩)
  show A t ≼ₒ A t ⊗ₒ sigma 0
  rw [h0]
  exact le_of_eq (MulMonoid.otimes_one (A t)).symm
```

The greedy shaper is the set of all greedy pairs. It is a server — its
causality field discharged by the lemma above — precisely because the
curve is null at the origin, which is therefore required to form it.

*Definition:* $`S_{\mathrm{gsh}}(\sigma) = \{\,(A, D) \mid D = A \ast \sigma\,\}`

```lean
def greedyShaper
    (sigma : F) (h0 : sigma 0 = eₒ) : Server where
  rel := { p | (↑p.2 : F) = conv (↑p.1 : F) sigma }
  causal p hp := by
    show (↑p.2 : F) ≤ₙ (↑p.1 : F)
    rw [(hp : (↑p.2 : F) = conv (↑p.1 : F) sigma)]
    exact conv_natLe_self_of_zeroAtOrigin (↑p.1) sigma h0

theorem mem_greedyShaper_iff
    {sigma : F} {h0 : sigma 0 = eₒ} {p : Curve × Curve} :
    p ∈ greedyShaper sigma h0 ↔
      (↑p.2 : F) = conv (↑p.1 : F) sigma :=
  Iff.rfl

theorem isGreedyShaper_greedyShaper
    (sigma : F) (h0 : sigma 0 = eₒ) :
    IsGreedyShaper (greedyShaper sigma h0) sigma :=
  fun _ hp => hp
```

A `sigma`-greedy shaper is a server whose every member equals its own
convolution; the greedy shaper is the largest such set.

*Theorem:* $`S \text{ greedy} \iff S \subseteq S_{\mathrm{gsh}}(\sigma)`

```lean
theorem isGreedyShaper_iff_subset
    {S : Server} {sigma : F} {h0 : sigma 0 = eₒ} :
    IsGreedyShaper S sigma ↔
      ∀ p ∈ S, p ∈ greedyShaper sigma h0 :=
  Iff.rfl
```

# The greedy shaper is a sigma-shaper

A sub-additive curve allows itself as an arrival curve: the kernel
inequality $`\sigma(u) \otimes \sigma(s) \preceq \sigma(u + s)` is
exactly the condition for $`\sigma` to allow $`\sigma`.

*Definition:* dioid sub-additivity of a curve, $`\sigma(u) \otimes \sigma(s) \preceq \sigma(u + s)`

```lean
def IsSubadditiveF (sigma : F) : Prop :=
  ∀ u s : ℝ≥0, sigma u ⊗ₒ sigma s ≼ₒ sigma (u + s)
```

*Theorem:* a sub-additive curve allows itself

```lean
theorem allowsArrivalCurve_self_of_subadd
    {sigma : F} (hsub : IsSubadditiveF sigma) :
    AllowsArrivalCurve sigma sigma := by
  rw [allowsArrivalCurve_iff_kernel]
  intro u s t hus
  rw [← hus]
  exact hsub u s
```

The point of the construction is that the output is `sigma`-shaped.
Under sub-additivity the convolution `A ∗ sigma` allows `sigma`:
shifting the constraint through associativity and monotonicity,
$`A \ast \sigma \le_n A \ast (\sigma \ast \sigma) = (A \ast \sigma) \ast \sigma`.

*Theorem:* if $`\sigma` is sub-additive then $`A \ast \sigma` allows $`\sigma`

```lean
theorem allowsArrivalCurve_conv_of_subadd
    (A : F) {sigma : F} (hsub : IsSubadditiveF sigma) :
    AllowsArrivalCurve (conv A sigma) sigma := by
  have h : conv A sigma ≤ₙ conv A (conv sigma sigma) :=
    conv_natLe_right A
      (allowsArrivalCurve_self_of_subadd hsub)
  rw [← conv_assoc] at h
  exact h
```

Hence every output of a greedy shaper over a sub-additive curve is a
`sigma`-shaper output.

*Theorem:* a greedy shaper over a sub-additive curve is a $`\sigma`-shaper

```lean
theorem IsGreedyShaper.isShaper
    {S : Server} {sigma : F}
    (hsub : IsSubadditiveF sigma)
    (hS : IsGreedyShaper S sigma) :
    IsShaper S sigma := by
  intro p hp
  rw [hS p hp]
  exact allowsArrivalCurve_conv_of_subadd (↑p.1) hsub
```

```lean
end NetworkCalculus
```
