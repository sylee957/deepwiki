# Graph refresh can see a missing root object after a clean gate

- **Date:** 2026-07-11
- **Tool/step:** `scripts/check.sh` followed by `scripts/wiki build`.
- **Expected:** a successful full gate leaves `DeepWiki.olean` available for the graph refresh.
- **Actual:** `scripts/wiki build` reported `object file .../DeepWiki.olean ... does not exist`; `lake build DeepWiki` restored it.
- **Why it's a limitation:** the gate command returned without output and did not leave the root object available to the graph tool.
- **Workaround used:** run `lake build DeepWiki` before retrying `scripts/wiki build`.
- **Suggested fix:** make `scripts/check.sh` verify the default-target root artifacts before returning success, or have `scripts/wiki build` invoke the necessary target when it is absent.
- **Status:** open
