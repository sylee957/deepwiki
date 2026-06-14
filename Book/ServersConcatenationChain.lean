import Book.ServersConcatenation

/-! # Concatenation of a chain of servers
A flow crossing a path of servers `h₁, …, hₙ` — each output feeding the
next — is offered the convolution of their min-plus service curves,
`β^(h₁) ∗ ⋯ ∗ β^(hₙ)`. The path is a `List` of server indices;
`concatComp` is the relation composition along it (`δ₀`'s identity
relation for the empty path) and `concatConv` the convolution fold (the
unit `δ₀` for the empty path). This is the `n`-server form of
`IsMinimalServiceCurve.comp`, and the end-to-end-service step used by
separated-flow analysis. -/

namespace DeepWiki

open scoped Classical NNReal

/-- Relation composition of servers along a path: the empty path is the
identity relation, and `h :: hs` feeds server `h`'s output into the rest
of the chain. -/
def concatComp {ι : Type*} (S : ι → Curve → Curve → Prop) :
    List ι → Curve → Curve → Prop
  | [] => (· = ·)
  | h :: hs => Relation.Comp (S h) (concatComp S hs)

/-- `concatComp S [] = (· = ·)`: the empty path is the identity server. -/
@[simp] theorem concatComp_nil {ι : Type*} (S : ι → Curve → Curve → Prop) :
    concatComp S [] = (· = ·) := rfl

/-- `concatComp S (h :: hs)` composes server `h` onto the rest of the
chain. -/
theorem concatComp_cons {ι : Type*} (S : ι → Curve → Curve → Prop)
    (h : ι) (hs : List ι) :
    concatComp S (h :: hs) = Relation.Comp (S h) (concatComp S hs) := rfl

/-- Convolution fold of service curves along a path: the empty path is
the unit `δ₀` (`convUnitEReal`), and `h :: hs` convolves `β h` with the
rest. -/
noncomputable def concatConv {ι : Type*} (β : ι → ℝ≥0 → EReal) :
    List ι → ℝ≥0 → EReal
  | [] => convUnitEReal
  | h :: hs => minConv (β h) (concatConv β hs)

/-- `concatConv β [] = δ₀`. -/
@[simp] theorem concatConv_nil {ι : Type*} (β : ι → ℝ≥0 → EReal) :
    concatConv β [] = convUnitEReal := rfl

/-- `concatConv β (h :: hs) = β h ∗ concatConv β hs`. -/
theorem concatConv_cons {ι : Type*} (β : ι → ℝ≥0 → EReal)
    (h : ι) (hs : List ι) :
    concatConv β (h :: hs) = minConv (β h) (concatConv β hs) := rfl

/-- A single-server path offers exactly that server's service curve. -/
@[simp] theorem concatConv_singleton {ι : Type*} (β : ι → ℝ≥0 → EReal)
    (h : ι) (hb : IsBddBelowReal (β h)) :
    concatConv β [h] = β h := by
  rw [concatConv_cons, concatConv_nil, minConv_convUnitEReal_right hb.isNeverBot]

/-- The convolution fold of bounded-below curves is bounded below. -/
theorem isBddBelowReal_concatConv {ι : Type*} {β : ι → ℝ≥0 → EReal}
    (hb : ∀ h, IsBddBelowReal (β h)) (hs : List ι) :
    IsBddBelowReal (concatConv β hs) := by
  induction hs with
  | nil => exact isBddBelowReal_convUnitEReal
  | cons h hs ih => exact (hb h).minConv ih

/-- The convolution fold of nonnegative curves is nonnegative. -/
theorem isNonneg_concatConv {ι : Type*} {β : ι → ℝ≥0 → EReal}
    (hnn : ∀ h, IsNonneg (β h)) (hs : List ι) :
    IsNonneg (concatConv β hs) := by
  induction hs with
  | nil => exact isNonneg_convUnitEReal
  | cons h hs ih => exact (hnn h).conv ih

/-- The identity relation offers the convolution unit `δ₀` as its
min-plus service curve. -/
theorem isMinimalServiceCurve_eq_convUnitEReal :
    IsMinimalServiceCurve convUnitEReal (· = · : Curve → Curve → Prop) := by
  intro A D h
  subst h
  rw [minConv_convUnitEReal_right (isBddBelowReal_curveEReal A).isNeverBot]

/-- **Concatenation of a chain of servers**: if every server `S h` offers
the bounded-below min-plus service curve `β h`, the path `concatComp S hs`
offers the convolution `concatConv β hs = ∗_{h∈hs} β h`. -/
theorem IsMinimalServiceCurve.concatComp {ι : Type*}
    {S : ι → Curve → Curve → Prop} {β : ι → ℝ≥0 → EReal}
    (hb : ∀ h, IsBddBelowReal (β h))
    (hS : ∀ h, IsMinimalServiceCurve (β h) (S h)) (hs : List ι) :
    IsMinimalServiceCurve (concatConv β hs) (concatComp S hs) := by
  induction hs with
  | nil => exact isMinimalServiceCurve_eq_convUnitEReal
  | cons h hs ih =>
    exact (hS h).comp ih (hb h) (isBddBelowReal_concatConv hb hs)

/-! ## Book restatement (concatenation of `n` servers)
A flow crossing a path of servers, the `h`-th offering the min-plus
service curve `β h`, is globally offered the convolution
`∗_{h ∈ path} β h` of those service curves — the `n`-server form of the
two-server concatenation theorem. -/
example {ι : Type*}
    {S : ι → Curve → Curve → Prop} {β : ι → ℝ≥0 → EReal}
    (hb : ∀ h, IsBddBelowReal (β h))
    (hS : ∀ h, IsMinimalServiceCurve (β h) (S h)) (path : List ι) :
    IsMinimalServiceCurve (concatConv β path) (concatComp S path) :=
  IsMinimalServiceCurve.concatComp hb hS path

end DeepWiki
