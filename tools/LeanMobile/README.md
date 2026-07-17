# Lean Mobile

Lean Mobile is a read-only, phone-friendly repository browser for Lean files. It serves the full
Git repository tree while excluding ignored files and private/generated folders, then forwards
semantic highlighting, tap-to-hover, goals, and definition requests to the project's own Lean
language server.

The backend and tests use Bun with strict TypeScript. The mobile interface is React 19 + TypeScript
and is compiled with Bun's bundler.

## Run locally

From the repository root:

```sh
cd tools/LeanMobile
bun install
bun start
```

Open <http://127.0.0.1:3210>.

The default repository is the DeepWiki root. To serve a different Lean repository:

```sh
bun start -- --root /path/to/repository --port 3210
```

## Open it from an iPhone

Keep the viewer bound to localhost and publish it only inside a private Tailscale network:

```sh
tailscale serve --bg http://127.0.0.1:3210
```

Open the HTTPS URL printed by Tailscale in Safari. Stop that publication with:

```sh
tailscale serve reset
```

Alternatively, binding to the Mac's network interfaces makes it available on the local network:

```sh
bun start -- --host 0.0.0.0
```

That mode has no application-level authentication. Use it only on a trusted network protected by
the Mac firewall; do not forward the port from a router or expose it to the public internet.

## Behavior and security boundary

- The tree comes from `git ls-files --cached --others --exclude-standard`, so tracked files and
  unignored working-tree files are visible throughout the repository.
- `.git`, `.lake`, `.wiki`, `.tlts`, `references`, build output, dependency directories, and PDFs
  ignored by the repository remain hidden.
- Text files up to 5 MiB can be read. Binary files are rejected.
- Canonical paths must stay inside the repository; symlinks cannot escape it.
- There are no edit, upload, delete, command-execution, or terminal endpoints.
- Lean semantic highlighting, hover/goals, and go-to-definition are available only for `.lean`
  files. The server starts with `lake env lean --server`, so it uses the repository's pinned
  toolchain and dependencies. Semantic colors stream in as Lean elaborates the file.

## Test

```sh
cd tools/LeanMobile
bun run typecheck
bun test
bun run build
```

To exercise the HTTP service and a real Lean hover request:

```sh
bun run smoke
```
