# Toolchain guidance is one release behind the repository

- **Date:** 2026-07-19
- **Tool/step:** local Lean validation
- **Expected:** The toolchain version in the repository guidance matches `lean-toolchain` and the dependency pins.
- **Actual:** The guidance specifies Lean, Mathlib, and doc-gen4 `v4.31.0`, while `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` pin `v4.32.0`.
- **Why it's a limitation:** Agents may test with or report the wrong compiler version when following the documented workflow literally.
- **Workaround used:** Treat the checked-in toolchain and dependency files as authoritative and validate with `v4.32.0`.
- **Suggested fix:** Update the toolchain paragraph in the repository guidance when its owning instructions are next revised.
- **Status:** resolved on 2026-07-24 by synchronizing the guidance with Lean `v4.32.1`
  and the compatible Mathlib/doc-gen4 `v4.32.0` tags.
