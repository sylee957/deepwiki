import VersoManual
import Book.Convolution

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

The ambient function dioid is `F`. A concrete class of cumulative
functions is represented by a type whose values coerce into `F`; this
leaves room to add non-decreasingness, nullity at the origin, or
continuity assumptions as fields of specialized structures later. The
relation `NatLe f g` is the ordinary pointwise numeric order, obtained
by looking through the `RplusMin` wrapper.

*Definition:* cumulative-function classes and their natural order

```lean
class CumulativeClass (C : Type*) where
  toF : C → F

instance {C : Type*} [CumulativeClass C] : CoeOut C F where
  coe := CumulativeClass.toF

def IsFiniteFunction (f : F) : Prop :=
  ∀ t, (f t : ℝ≥0∞) ≠ ⊤

structure FiniteCumulativeFunction where
  toF : F
  finite : IsFiniteFunction toF

instance : CumulativeClass FiniteCumulativeFunction where
  toF := FiniteCumulativeFunction.toF

def ofNNRealFunction
    (f : ℝ≥0 → ℝ≥0) :
    FiniteCumulativeFunction where
  toF := fun t => ⟨(f t : ℝ≥0∞)⟩
  finite := by
    intro t
    simp

theorem ofNNRealFunction_finite
    (f : ℝ≥0 → ℝ≥0) :
    IsFiniteFunction (↑(ofNNRealFunction f) : F) :=
  (ofNNRealFunction f).finite

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

A server relation is a set of admissible input-output pairs inside a
chosen cumulative-function class. It is a server in the book's sense
when it is left-total and causal. Causality is the constraint `D ≤ A`;
the shaper condition is the output-arrival constraint.

*Definition:* servers and sigma-shapers

```lean
abbrev Server (C : Type*) [CumulativeClass C] :=
  Set (C × C)

def Serves {C : Type*} [CumulativeClass C]
    (S : Server C) (A D : C) : Prop :=
  (A, D) ∈ S

scoped notation:50 A:51 " ⟶[" S "] " D:51 =>
  Serves S A D

def IsLeftTotalServer {C : Type*}
    [CumulativeClass C] (S : Server C) : Prop :=
  ∀ A : C, ∃ D : C, A ⟶[S] D

def IsCausalServer {C : Type*}
    [CumulativeClass C] (S : Server C) : Prop :=
  ∀ p ∈ S, (↑p.2 : F) ≤ₙ (↑p.1 : F)

def IsServer {C : Type*}
    [CumulativeClass C] (S : Server C) : Prop :=
  IsLeftTotalServer S ∧ IsCausalServer S

def IsShaper {C : Type*} [CumulativeClass C]
    (S : Server C) (sigma : F) : Prop :=
  ∀ p ∈ S, AllowsArrivalCurve (↑p.2 : F) sigma
```

The largest causal server satisfying the shaper constraint is the set
of all pairs whose output is below the input and whose output allows
`sigma` as an arrival curve.

*Definition:* the largest `sigma`-shaper server

```lean
def shaperServer (C : Type*) [CumulativeClass C]
    (sigma : F) : Server C :=
  { p | (↑p.2 : F) ≤ₙ (↑p.1 : F) ∧
      AllowsArrivalCurve (↑p.2 : F) sigma }

theorem mem_shaperServer_iff
    {C : Type*} [CumulativeClass C]
    {sigma : F} {p : C × C} :
    p ∈ shaperServer C sigma ↔
      (↑p.2 : F) ≤ₙ (↑p.1 : F) ∧
        AllowsArrivalCurve (↑p.2 : F) sigma :=
  Iff.rfl

theorem subset_shaperServer_iff
    {C : Type*} [CumulativeClass C]
    {S : Server C} {sigma : F} :
    S ⊆ shaperServer C sigma ↔
      IsCausalServer S ∧ IsShaper S sigma := by
  constructor
  · intro h
    constructor
    · intro p hp
      exact (h hp).1
    · intro p hp
      exact (h hp).2
  · rintro ⟨hcausal, hshape⟩ p hp
    exact ⟨hcausal p hp, hshape p hp⟩

theorem server_subset_shaperServer_iff
    {C : Type*} [CumulativeClass C]
    {S : Server C} {sigma : F}
    (hS : IsServer S) :
    S ⊆ shaperServer C sigma ↔
      IsShaper S sigma := by
  constructor
  · intro h p hp
    exact (h hp).2
  · intro h
    exact (subset_shaperServer_iff).2
      ⟨hS.2, h⟩
```

# Shaping closure

The convolution unit `convUnit` — the impulse, $`e` at time `0` and
$`\varepsilon` elsewhere — is the multiplicative unit of the function
dioid, established with its two identity laws `convUnit_left` and
`convUnit_right` when that dioid was assembled. The closure built here
reuses it directly.

The closure is the dioid supremum of all convolution powers. Since the
dioid supremum is numeric infimum in the min-plus model, this is the
usual min-plus star construction.

*Definition:* convolution powers and closure

```lean
noncomputable def convPow (sigma : F) : ℕ → F
  | 0 => convUnit
  | n + 1 => conv (convPow sigma n) sigma

noncomputable def subadditiveClosure (sigma : F) : F :=
  fun t =>
    CompleteDioid.iSup
      (fun n : ℕ => convPow sigma n t)

scoped notation:max sigma:90 "⋆" =>
  subadditiveClosure sigma
```

The first nontrivial power is the original function.

*Theorem:* $`\sigma^{\ast 1} = \sigma`

```lean
theorem convPow_one (sigma : F) :
    convPow sigma 1 = sigma := by
  change conv convUnit sigma = sigma
  exact convUnit_left sigma
```

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
    (C : Type*) [CumulativeClass C]
    (sigma : F) :
    shaperServer C sigma =
      shaperServer C sigma⋆ := by
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
    {C : Type*} [CumulativeClass C]
    {S : Server C} {sigma : F}
    (hS : IsShaper S sigma) :
    IsShaper S sigma⋆ := by
  intro p hp
  exact (allowsArrivalCurve_closure_iff
    (↑p.2 : F) sigma).2 (hS p hp)

example (C : Type*) [CumulativeClass C]
    (sigma : F) :
    shaperServer C sigma =
      shaperServer C sigma⋆ :=
  shaperServer_closure C sigma

example {C : Type*} [CumulativeClass C]
    {S : Server C} {sigma : F}
    (hS : IsShaper S sigma) :
    IsShaper S sigma⋆ :=
  IsShaper.closure hS
```

Larger arrival curves preserve the shaper property, and their largest
servers contain the smaller-curve largest server.

*Theorem:* if $`\sigma \le_n \sigma'`, then $`S_{\mathrm{sh}}(\sigma) \subseteq S_{\mathrm{sh}}(\sigma')`

```lean
theorem IsShaper.of_natLe
    {C : Type*} [CumulativeClass C]
    {S : Server C}
    {sigma sigma' : F}
    (hS : IsShaper S sigma)
    (h : sigma ≤ₙ sigma') :
    IsShaper S sigma' := by
  intro p hp
  exact NatLe.trans (hS p hp)
    (conv_natLe_right (↑p.2 : F) h)

theorem shaperServer_mono
    {C : Type*} [CumulativeClass C]
    {sigma sigma' : F}
    (h : sigma ≤ₙ sigma') :
    shaperServer C sigma ⊆
      shaperServer C sigma' := by
  intro p hp
  exact ⟨hp.1,
    NatLe.trans hp.2
      (conv_natLe_right (↑p.2 : F) h)⟩

example {C : Type*} [CumulativeClass C]
    {sigma sigma' : F}
    (h : sigma ≤ₙ sigma') :
    shaperServer C sigma ⊆
      shaperServer C sigma' :=
  shaperServer_mono h

example {C : Type*} [CumulativeClass C]
    {S : Server C} {sigma sigma' : F}
    (hS : IsShaper S sigma)
    (h : sigma ≤ₙ sigma') :
    IsShaper S sigma' :=
  IsShaper.of_natLe hS h
```

```lean
end NetworkCalculus
```
