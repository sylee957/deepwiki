import DeepWiki.SymbolicIntegration.Computable.MonomialDeriv
import Lean

/-! # The `transfer` elaborator (the Lean Trocq analog)

A metaprogram that synthesizes the abstract denotation of a computable expression. The CoqEAL
`⟹`/`refines_apply` pure-typeclass kernel cannot decompose in Lean (the composition instance needs a
metavariable function-head unification `?g ?b =?= cop x y` that TC will not solve), so — like Trocq's
Coq-Elpi plugin — transfer is done by a metaprogram. `simp only [denote]` performs the recursive
decomposition; this layer orchestrates it to hand back the abstract term as *first-class data* (the
proof's RHS is computed, not hand-written), which solves the `= _` hole problem that `simp`/TC hit.

* `transfer% e` — a term producing a proof of `e = <abstract>`, with `<abstract>` computed by pushing
  the denotation through the computable operations.
-/

open Lean Meta Elab Term

namespace DeepWiki.Transfer

/-- Normalize `e` through the `denote` simp set: returns `(a, proof?)` where `a` is the abstract form
and `proof? : e = a` (or `none` when `e` is already normal). -/
def denoteNormalize (e : Expr) : MetaM (Expr × Option Expr) := do
  let some ext ← getSimpExtension? `denote
    | throwError "transfer: the `denote` simp set is not registered"
  let thms ← ext.getTheorems
  let ctx ← Simp.mkContext {} (simpTheorems := #[thms])
    (congrTheorems := ← getSimpCongrTheorems)
  let (r, _) ← simp e ctx
  return (r.expr, r.proof?)

/-- `transfer% e` : normalize the computable expression `e` through the `denote` set to its abstract
form `a`, producing a proof term of `e = a` with `a` computed. -/
elab "transfer% " t:term : term => do
  let e ← elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let (_, proof?) ← denoteNormalize e
  match proof? with
  | some pf => return pf
  | none => mkEqRefl e

section Test
open DeepWiki.SymbolicIntegration CPolyG Polynomial

variable {α : Type*} [CField α] [CFieldSpec α]

/-- The abstract side is *computed* by `transfer%`, not written — this is what `simp`/TC could not do
(elaboration fills the RHS before a tactic runs). -/
example (p q r : CPolyG α) :
    toPolyG (cmulG (caddG p q) r) = (toPolyG p + toPolyG q) * toPolyG r :=
  transfer% (toPolyG (cmulG (caddG p q) r))

/-- Synthesis into a hole: `h`'s RHS is filled by the elaborator. -/
example (p q : CPolyG α) : True := by
  have h := transfer% (toPolyG (cmulG p q))
  -- h : toPolyG (cmulG p q) = toPolyG p * toPolyG q
  guard_hyp h : toPolyG (cmulG p q) = toPolyG p * toPolyG q
  trivial

end Test

end DeepWiki.Transfer
