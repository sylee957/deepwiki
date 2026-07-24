# Gate loses a freshly built Lean artifact

- **Date:** 2026-07-10
- **Tool/step:** `scripts/check.sh`
- **Expected:** A successful build of `DeepWiki.SymbolicIntegration.Engine.Tower.Deriv` leaves its
  `.olean` available to downstream jobs in the same gate run.
- **Actual:** The gate built `Tower.Deriv`, then multiple downstream jobs failed with `failed to open
  file '.../Tower/Deriv.olean': No such file or directory`. The same disappearance previously hit
  `RadicalCase2.olean` during a scoped gate. It recurred while another commit landed: six downstream
  targets simultaneously lost the freshly available `Engine/LinearSolve.olean`. On 2026-07-24 a
  catalog gate similarly failed to produce `Engine/Tower/Integrate.olean` and
  `Engine/PolySplitFactor.olean` (`error code: 4294967294`); explicitly building those targets and
  immediately rerunning the unchanged gate succeeded.
- **Why it's a limitation:** A build artifact appears to be removed or replaced while the parallel
  Lake build still has downstream readers, so a source-correct worktree can fail nondeterministically.
- **Workaround used:** Rebuild the missing module serially with a scoped `scripts/check.sh`, then rerun
  the full gate.
- **Suggested fix:** Investigate concurrent Lake/cache writers and make `scripts/check.sh` serialize
  conflicting builds or lock the build directory for the duration of a gate.
- **Status:** open
