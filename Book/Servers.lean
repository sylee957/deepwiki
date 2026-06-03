import VersoManual
import Book.LeftContinuity
import Book.PiecewiseContinuous
import Book.FunctionDioids

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Cumulative functions and servers" =>
The objects of network calculus are _cumulative functions_ — the
arrivals and departures of a server — and the _servers_ that relate
them. A cumulative function is an honest real curve, and a server is a
causal input-output relation between curves. This chapter defines both;
the arrival-curve and shaper constructions build on them.

```lean
namespace VerifiedWiki

open Algebra
open scoped Classical NNReal ENNReal Algebra.Bridge
```

# Cumulative functions

The ambient function dioid is `Fmin`. Cumulative functions — the arrivals
and departures of a server — are honest real curves
$`\mathbb{R}^{+} \to \mathbb{R}_{\ge 0}`, coerced into `Fmin` when the
convolution is needed. They are compared in the natural order `≤ₙ` of
the previous chapter, the pointwise numeric order on `Fmin`.

A _cumulative function_ — the arrival or departure of a server — is a
real curve $`\mathbb{R}^{+} \to \mathbb{R}_{\ge 0}` carrying the
network-calculus regularity: it is non-decreasing, null at the origin,
piecewise continuous, and left-continuous. We bundle the underlying
function with these four axioms into the type `Curve`, the
formalization of the curve set $`\mathcal{C}`.

Piecewise continuity — the discontinuities being locally finite — was
developed in the chapter `Piecewise continuity`; we reuse
`IsPiecewiseContinuous` here.

*Definition:* the curve set $`\mathcal{C}` — non-decreasing, null, piecewise- and left-continuous

```lean
structure Curve where
  toFun : ℝ≥0 → ℝ≥0
  mono : Monotone toFun
  zero : toFun 0 = 0
  pwc : IsPiecewiseContinuous toFun
  leftCont : IsLeftContinuousReal toFun
```

A curve applies as its underlying function, and coerces into the
function dioid `Fmin` by wrapping each value into `RplusMin`; this is how
the convolution-based statements reach it.

*Definition:* a curve as a function and as a dioid function

```lean
instance : CoeFun Curve (fun _ => ℝ≥0 → ℝ≥0) where
  coe := Curve.toFun

instance : Coe Curve Fmin where
  coe := fun A => fun t => ⟨(A.toFun t : ℝ≥0∞)⟩
```

Curves are compared in the ordinary _pointwise_ order on their real
values — directly on $`\mathbb{R}_{\ge 0}`, with no detour through the
dioid. This is the `≤` used to state causality.

*Definition:* the pointwise order on curves, $`D \le A \iff \forall t,\ D(t) \le A(t)`

```lean
instance : LE Curve where
  le D A := ∀ t, D.toFun t ≤ A.toFun t

theorem Curve.le_def {D A : Curve} :
    D ≤ A ↔ ∀ t, D.toFun t ≤ A.toFun t :=
  Iff.rfl
```

The pointwise curve order is exactly the natural order `≤ₙ` of the
coerced dioid functions, so the two are interchangeable wherever the
convolution-based statements need the dioid form.

*Theorem:* $`D \le A \iff \uparrow\!D \le_n \uparrow\!A`

```lean
theorem Curve.le_iff_natLe {D A : Curve} :
    D ≤ A ↔ (↑D : Fmin) ≤ₙ (↑A : Fmin) := by
  constructor
  · intro h t
    show ((D.toFun t : ℝ≥0∞)) ≤ (A.toFun t : ℝ≥0∞)
    exact_mod_cast h t
  · intro h t
    have ht := h t
    show D.toFun t ≤ A.toFun t
    have : ((D.toFun t : ℝ≥0∞)) ≤ (A.toFun t : ℝ≥0∞) := ht
    exact_mod_cast this
```

# Servers

A server is a set of admissible input-output pairs of cumulative
functions, _bundled with_ its causality proof: every pair has its
departure below its arrival, `D ≤ A`. Causality is thus intrinsic to
being a server. Left-totality is stated separately.

*Definition:* a server is a causal input-output relation on curves

A `Server` bundles the input-output relation with two proofs, matching
the classical definition of a server as a _left-total causal_ relation:

- _causality_ — for every arrival `A` and departure `D` it relates, the
  departure lies below the arrival, $`D \le_n A`;
- _left-totality_ — every arrival `A` has at least one departure.

Both are thus part of being a server, not separate predicates. The pair
components are named: `A` is the arrival, `D` the departure.

```lean
structure Server where
  rel : Set (Curve × Curve)
  causal : ∀ A D : Curve, (A, D) ∈ rel → D ≤ A
  leftTotal : ∀ A : Curve, ∃ D : Curve, (A, D) ∈ rel

instance : Membership (Curve × Curve) Server where
  mem S p := p ∈ S.rel

def Serves (S : Server) (A D : Curve) : Prop :=
  (A, D) ∈ S

scoped notation:50 A:51 " ⟶[" S "] " D:51 =>
  Serves S A D
```

```lean
end VerifiedWiki
```
