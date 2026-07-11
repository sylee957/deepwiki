import DeepWiki.ComputableAlgebra.PolyEngineLawful

/-! # Representation-selected polynomial interpolation

`CPolyInterpolate` selects an executable interpolation algorithm for a polynomial representation.
`LawfulCPolyInterpolate` characterizes the selected interpolant by evaluation at distinct nodes and
the usual strict degree bound. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

universe u v

/-- Executable interpolation selected by a computable polynomial representation. -/
class CPolyInterpolate (P : Type u → Type u) [CPoly P] [CPolyEngine P] where
  /-- Interpolate a polynomial through the supplied coefficient-field points. -/
  compute : {α : Type u} → [CField α] → List (α × α) → P α

/-- Laws characterizing a representation-selected interpolation algorithm. -/
class LawfulCPolyInterpolate (P : Type u → Type u) [CPoly P] [CPolyEngine P]
    [CPolyInterpolate P] : Prop where
  /-- The selected interpolant evaluates to every sampled value when the denoted nodes are distinct. -/
  eval_compute : ∀ {α : Type u} [CField α] [CFieldSpec.{u,v} α]
    (pts : List (α × α)),
    (pts.map (fun p => (CFieldSpec.toK p.1 : CFieldSpec.K α))).Nodup →
    ∀ {zk yk : α}, (zk, yk) ∈ pts →
      (CPoly.toPoly (CPolyInterpolate.compute (P := P) pts)).eval (CFieldSpec.toK zk) =
        CFieldSpec.toK yk
  /-- A nonempty selected interpolant has degree strictly below the number of samples. -/
  degree_compute_lt : ∀ {α : Type u} [CField α] [CFieldSpec.{u,v} α]
    (pts : List (α × α)), pts ≠ [] →
      (CPoly.toPoly (CPolyInterpolate.compute (P := P) pts)).degree < (pts.length : WithBot ℕ)

namespace CPoly

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P] [CPolyInterpolate P]

/-- Interpolate using the algorithm selected by polynomial representation `P`. -/
def interpolate {α : Type u} [CField α] (pts : List (α × α)) : P α :=
  CPolyInterpolate.compute pts

variable [LawfulCPolyInterpolate.{u,v} P]

/-- Selected interpolation evaluates to the sampled value at each distinct node. -/
theorem eval_toPoly_interpolate {α : Type u} [CField α] [CFieldSpec.{u,v} α]
    (pts : List (α × α))
    (hnodup : (pts.map (fun p => (CFieldSpec.toK p.1 : CFieldSpec.K α))).Nodup)
    {zk yk : α} (hmem : (zk, yk) ∈ pts) :
    (toPoly (interpolate (P := P) pts)).eval (CFieldSpec.toK zk) = CFieldSpec.toK yk := by
  exact LawfulCPolyInterpolate.eval_compute pts hnodup hmem

/-- A nonempty selected interpolant has degree strictly below the number of samples. -/
theorem degree_toPoly_interpolate_lt {α : Type u} [CField α] [CFieldSpec.{u,v} α]
    (pts : List (α × α)) (hne : pts ≠ []) :
    (toPoly (interpolate (P := P) pts)).degree < (pts.length : WithBot ℕ) := by
  exact LawfulCPolyInterpolate.degree_compute_lt pts hne

end CPoly

end DeepWiki.SymbolicIntegration
