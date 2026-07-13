# `scripts/wiki build` transiently missed `Sources.olean`

- **Date:** 2026-07-13
- **Tool/step:** `scripts/wiki build`
- **Expected:** Graph extraction starts after the full gate has built `Sources`.
- **Actual:** The first run reported that `.lake/build/lib/lean/Sources.olean` did not exist, although the file was visible immediately afterward and a retry succeeded.
- **Why it's a limitation:** The wrapper can expose a transient artifact-availability race instead of retrying environment loading.
- **Workaround used:** Confirm the object exists and rerun `scripts/wiki build`.
- **Suggested fix:** Retry once when environment loading reports a missing root-library object that appears after the failure.
- **Status:** open
