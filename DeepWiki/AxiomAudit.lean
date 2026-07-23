import Lean.Attributes
import Lean.Util.CollectAxioms

/-! # Axiom audits

Checked declaration attributes for enforcing kernel axiom budgets during elaboration.
-/

open Lean

namespace DeepWiki

/-- `@[choice_free]` certifies that a declaration does not transitively use `Classical.choice`. -/
initialize choiceFreeAttr : TagAttribute ←
  registerTagAttribute `choice_free
    "Certifies that a declaration does not transitively depend on Classical.choice."
    (validate := fun decl => do
      let axioms ← Lean.collectAxioms decl
      if axioms.contains ``Classical.choice then
        throwError
          "declaration '{decl}' is marked `choice_free`, but transitively depends on \
          `Classical.choice`")

end DeepWiki
