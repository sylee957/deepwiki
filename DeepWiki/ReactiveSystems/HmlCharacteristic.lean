import DeepWiki.ReactiveSystems.Bisimulation
import Mathlib.Order.FixedPoints

/-! # Characteristic formulae
For each state of an LTS, a recursive (largest-fixed-point) property `X_p` that
captures it up to strong bisimilarity. We work with the property's semantic
functional directly: `q ⊨ X_p` exactly when `(p, q)` passes the bisimulation
transfer test relative to the candidate solution, so the greatest fixed point
assigns to each `p` its bisimilarity class. On a finite LTS this functional is the
denotation of the explicit characteristic HML-with-recursion formula;
here we capture its semantic content for every LTS. -/

namespace DeepWiki.ReactiveSystems

namespace LTS

variable {Proc Act : Type*}

/-- The characteristic-property functional: `q ∈ charFun ρ p` when every move of `p`
is matched by a move of `q` into `ρ` and vice versa — the bisimulation transfer
conditions relative to `ρ`. -/
def charFun (L : LTS Proc Act) : (Proc → Set Proc) →o (Proc → Set Proc) where
  toFun ρ := fun p => {q |
    (∀ a p', L.step p a p' → ∃ q', L.step q a q' ∧ q' ∈ ρ p') ∧
    (∀ a q', L.step q a q' → ∃ p', L.step p a p' ∧ q' ∈ ρ p')}
  monotone' := fun _ _ hρσ _ _ hq =>
    ⟨fun a p' hstep => (hq.1 a p' hstep).imp fun _ h => ⟨h.1, hρσ p' h.2⟩,
     fun a q' hstep => (hq.2 a q' hstep).imp fun p' h => ⟨h.1, hρσ p' h.2⟩⟩

/-- The characteristic property of each state: the greatest fixed point of
`charFun`. -/
def charProp (L : LTS Proc Act) : Proc → Set Proc := (charFun L).gfp

/-- The witnessing relation `{(p,q) | q ⊨ X_p}` is a strong bisimulation. -/
theorem charProp_isBisimulation (L : LTS Proc Act) :
    IsBisimulation L (fun p q => q ∈ charProp L p) := by
  intro p q hq
  rw [show charProp L = charFun L (charProp L) from (OrderHom.map_gfp (charFun L)).symm] at hq
  exact hq

/-- From `q ⊨ X_p` to bisimilarity. -/
theorem charProp_imp_bisimilar (L : LTS Proc Act) {p q : Proc} (h : q ∈ charProp L p) :
    Bisimilar L p q := (charProp_isBisimulation L).le_bisimilar h

/-- Bisimilarity is below the characteristic property: each state satisfies its own
characteristic formula, and so does any bisimilar state. -/
theorem bisimilar_le_charProp (L : LTS Proc Act) :
    (fun p => {q | Bisimilar L p q}) ≤ charProp L := by
  refine (charFun L).le_gfp ?_
  intro p q hq
  exact (bisimilar_iff p q).mp hq

/-- The characteristic property of `p` is exactly its strong-bisimilarity class:
`q ⊨ X_p` iff `p ~ q`. -/
theorem charProp_eq_bisimilar (L : LTS Proc Act) (p q : Proc) :
    q ∈ charProp L p ↔ Bisimilar L p q :=
  ⟨charProp_imp_bisimilar L, fun h => bisimilar_le_charProp L p h⟩

/-- `⟦X_p⟧ = [p]_∼`: the denotation of the characteristic formula is the
bisimilarity class of `p`. -/
theorem charProp_eq (L : LTS Proc Act) (p : Proc) :
    charProp L p = {q | Bisimilar L p q} := Set.ext (charProp_eq_bisimilar L p)

end LTS

end DeepWiki.ReactiveSystems
