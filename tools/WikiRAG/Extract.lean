import Lean
import WikiRAG.Basic

/-! # WikiRAG extractor: walk the loaded environment into a graph
Iterates `Environment.constants`, keeps user declarations in our libraries
(`DeepWiki`/`Sources`), and emits node metadata + intra-library `uses` edges
from `ConstantInfo.getUsedConstantsAsSet` (type and value). -/

namespace WikiRAG
open Lean Lean.Meta

/-- A module belongs to one of our wiki libraries. -/
def isOurModule (m : Name) : Bool :=
  let s := m.toString
  s == "DeepWiki" || s.startsWith "DeepWiki." || s == "Sources" || s.startsWith "Sources."

/-- The defining module of a declaration (imported only — we load, not elaborate). -/
def moduleOf? (env : Environment) (n : Name) : Option Name :=
  match env.getModuleIdxFor? n with
  | none => none
  | some idx => env.header.moduleNames[idx.toNat]?

/-- The last (string) component of a name, for display/search. -/
def lastComp (n : Name) : String :=
  match n with
  | .str _ s => s
  | _ => n.toString

/-- A coarse declaration kind for display. -/
def kindOf (env : Environment) (n : Name) (ci : ConstantInfo) : String :=
  if isClass env n then "class"
  else if isStructure env n then "structure"
  else match ci with
    | .axiomInfo _ => "axiom"
    | .thmInfo _ => "theorem"
    | .opaqueInfo _ => "opaque"
    | .quotInfo _ => "quot"
    | .inductInfo _ => "inductive"
    | .ctorInfo _ => "ctor"
    | .recInfo _ => "rec"
    | .defnInfo _ => "def"

/-- Walk the loaded environment; collect our decl metadata and intra-library use-edges. -/
def gather : MetaM (Array DeclMeta × Array (String × String)) := do
  let env ← getEnv
  let mut metas : Array DeclMeta := #[]
  let mut edges : Array (String × String) := #[]
  for (name, ci) in env.constants.map₁.toList do
    if name.isInternal then continue
    let some mod := moduleOf? env name | continue
    unless isOurModule mod do continue
    let some ranges ← findDeclarationRanges? name | continue
    let sig := squeeze (toString (← ppExpr ci.type))
    let doc := (← findDocString? env name).getD ""
    metas := metas.push {
      name := name.toString
      short := lastComp name
      kind := kindOf env name ci
      module := mod.toString
      line := ranges.range.pos.line
      signature := sig
      doc := squeeze doc }
    for u in ci.getUsedConstantsAsSet do
      if u == name || u.isInternal then continue
      match moduleOf? env u with
      | some um => if isOurModule um then edges := edges.push (name.toString, u.toString)
      | none => pure ()
  return (metas, edges)

end WikiRAG
