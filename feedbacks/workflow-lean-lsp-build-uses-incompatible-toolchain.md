# Stale Lean LSP rebuild writes incompatible project artifacts

- **Date:** 2026-07-24
- **Tool/step:** `lean-lsp` `lean_build`
- **Expected:** After the repository toolchain is updated, rebuilding or restarting the language
  server uses the pinned Lean `v4.32.1` toolchain and terminates any superseded build.
- **Actual:** `lean_build` timed out after 300 seconds, but its descendant build remained active.
  An older IDE/LSP server still running Lean `v4.32.0` continued executing `lake setup-file`
  against the upgraded repository and overwrote dependency artifacts. Subsequent `v4.32.1`
  checks reported incompatible headers and missing `.olean` files.
- **Why it's a limitation:** A long-lived language server retains its original toolchain across a
  repository pin change, and a timed-out build does not necessarily terminate its descendants.
  The stale server can therefore keep writing incompatible artifacts after the caller has returned.
- **Workaround used:** Identify and terminate only the stale `v4.32.0` process groups, clean the
  affected dependency outputs, rebuild them with `v4.32.1`, and ensure only one full gate runs at a
  time.
- **Suggested fix:** Have `lean_build` validate the active server toolchain against
  `lean-toolchain`, terminate descendant processes on timeout, and advise restarting the language
  server whenever the repository pin changes.
- **Status:** open
