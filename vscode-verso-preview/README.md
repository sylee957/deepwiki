# Verso Preview

A **native, theme-matched** in-editor preview for the Verso book documents
(`Book/*.lean`). Everything is delegated to the real Lean tools — **no
hand-rolled parser**:

- **Markup parsing → Verso's own parser**, via a small Lean sidecar
  (`verso-parse`). The extension never re-implements the Verso grammar in
  TypeScript; it runs the real parser and renders the resulting block/inline
  tree.
- **Code intelligence → Lean language server** (hover, go-to-definition),
  proxied at exact source positions.

It renders, in VSCode's own colors:

- **Prose** — paragraphs, headings, `_italic_` / `*bold*`, inline `` `code` ``,
  blockquotes (whatever Verso's parser emits)
- **KaTeX math** — inline `` $`…` `` and display `` $$`…` ``
- **Code blocks** — ` ```lean ` fences (coloring via LSP semantic tokens — WIP)

## The sidecar

`verso-parse` is a `lean_exe` target in the repo's `lakefile.toml` (root
`VersoParse.lean`). It runs Verso's `Verso.Parser.document` on the file with an
empty environment — **parse-only, no elaboration, no Mathlib** — so it completes
in ~25–40 ms even on the largest chapter, and emits the block+inline tree as
JSON. The extension spawns it on each render (passing the current buffer via a
temp file, so unsaved edits are honored) and posts the tree to the webview.

Build it once with `lake build verso-parse` (or `lake build`). If the binary
isn't present, the preview shows a "run `lake build verso-parse`" message — there
is **no TypeScript-parser fallback**, by design (single source of markup truth).

Then, for the linking you actually want:

- **Hover anywhere in a code block** → the extension asks the Lean server (via
  `executeHoverProvider`) for the hover *at the exact source column under the
  cursor*, and shows it in a theme-styled tooltip. This works on **everything the
  LSP resolves** — identifiers, operators, notation (`⨆`, `≤`, `∗`), and unicode
  like `ℝ≥0` — not just word tokens. Same info as hovering in the editor.
- **Cmd/Ctrl-click anywhere in a code block** → go to the definition at that
  column (via `executeDefinitionProvider`), jumping the editor to the real
  `def`/`theorem`/notation, across chapters and into Mathlib.

The column is resolved from the cursor with `caretPositionFromPoint`: each code
line is rendered so its `textContent` equals the source line exactly, so the
caret offset *is* the UTF-16 column — which is precisely what the Lean LSP and
`vscode.Position` expect (Lean uses UTF-16 columns; all Lean math symbols are
single UTF-16 units, so JS string indices map 1:1, no conversion). Verified: all
9,876 code lines across the 17 chapters render with exactly source-matching text.

## Why this design

Verso's published HTML has token tooltips because `generate-book` *elaborates*
the code. Re-running that on every edit is slow (~8 s) and the book's CSS doesn't
match your editor theme. But the Lean server is **already elaborating the open
file** — it has the exact same hover/definition data. So we render the prose/math
natively (instant, theme-matched) and borrow the *real* elaborated info from the
LSP on demand. Best of both: editor-native look, genuine tooltips.

The linchpin is position mapping: the parser tracks each identifier's true
`(line, column)` in the source so the LSP query hits the right token. This is
verified — all 18,293 identifier tokens across the 17 chapters map exactly to
their source positions.

## Usage

1. Open a `Book/*.lean` file. (The Lean server must have finished elaborating it —
   wait for the "Lean is loading" indicator to clear, or hovers come back empty.)
2. `Cmd+K V`, the preview icon in the editor title bar, or Command Palette →
   **"Verso: Open Preview to the Side"**.
3. Hover identifiers for types/docstrings; **Cmd-click** to jump to a definition.
   The preview updates live as you type and follows the active `.lean` file.

## Limits / notes

- Hovers need the Lean server ready and the file elaborated; before that, a token
  hover shows nothing (same as the editor not being ready).
- Highlighting is lexical (keyword/identifier/string/number/comment) — the
  *coloring* is approximate, but the hover/definition data is exact (it's the
  LSP's).
- Math renders via KaTeX from a CDN, so the preview needs network access for math.
- This is a content preview, not the faithful published render. For the exact
  deployed look, use the `lake exe generate-book` HTML.

## Hover indicator

While hovering inside a code block the run under the cursor is highlighted (a
faint box + underline) so you can see exactly where the LSP query will land, and
the cursor changes to a pointer. The tooltip appears just below.

## Project layout (React + TypeScript)

```
src/
  extension.ts        # host: panel, active-editor tracking, LSP dispatch
  verso.ts            # shared Verso markup parser → block AST + Lean tokenizer
  types.ts            # host ⇄ webview message protocol
  webview/
    index.tsx         # React root: hover/click state, indicator, tooltip
    Preview.tsx       # renders the block AST (prose, math, code lines)
    hover.ts          # caret → exact source (line, col) resolution
    styles.css        # theme-matched styles (bundled into dist/webview.css)
esbuild.mjs           # bundles host (node/cjs) + webview (browser/iife) + css
```

The webview is a React app bundled by esbuild; the host is TypeScript. The Verso
parser is shared between them. The build produces `dist/extension.js`,
`dist/webview.js`, `dist/webview.css`.

## Build & develop

```
npm install
npm run build       # one-shot build
npm run watch       # rebuild host + webview on change
npm run typecheck   # tsc --noEmit (strict)
npm run package     # build + produce a .vsix (vsce)
```

After a build, reload the window (`Cmd+Shift+P` → "Developer: Reload Window") to
pick up the new bundle. The extension is symlinked into `~/.vscode/extensions/`;
its `main` is `dist/extension.js`, so reloading after `npm run build` is enough.
Alternatively install the packaged `.vsix` via "Extensions: Install from VSIX…".
