import VersoManual
import Tutorial.Risch

open Verso.Genre Manual

/-!
Render entry point for the Risch-algorithm tutorial Manual.

`lake exe tutorial --output _out` renders the document; the multi-file HTML
lands in `_out/html-multi/`. This is a standalone Verso target, out of
`defaultTargets` — the math library stays plain Lean + doc-gen4.
-/

/-- Render configuration: emit the multi-file HTML used for the Pages site. -/
def config : Config where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 2

/-- Entry point: render the Risch tutorial Manual to HTML. -/
def main := manualMain (%doc Tutorial.Risch) (config := { config with })
