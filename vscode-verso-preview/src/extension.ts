import * as vscode from "vscode";
import * as path from "path";
import * as os from "os";
import * as fs from "fs";
import { execFile } from "child_process";
import { marked } from "marked";
import { tokenizeGrammar } from "./textmate";
import type { WebviewToHost, HostToWebview } from "./types";
import type { VersoDoc } from "./doc";

// Hover content is GitHub-flavored Markdown from the Lean server. Render it
// with `marked` (handles ***-separators, nested emphasis, code spans, lists,
// links — everything our hand-rolled converter missed). Inline source is the
// trusted Lean server, and the webview enforces a strict CSP.
marked.setOptions({ gfm: true, breaks: false });

let panel: vscode.WebviewPanel | undefined;
let trackedDoc: vscode.TextDocument | undefined;
let updateTimer: ReturnType<typeof setTimeout> | undefined;
/** Repo root (workspace folder) — where the verso-parse binary lives. */
let repoRoot = "";
/** Extension's dist/ dir — where the grammar + WASM assets live. */
let distDir = "";
/** Per-render counter so a stale async parse result can be discarded. */
let renderSeq = 0;

// Browser-style preview history: a stack of previewed document URIs with a
// cursor. Tracking a NEW doc truncates any forward entries and pushes; Back/
// Forward move the cursor without pushing.
const history: string[] = [];
let histIndex = -1;
/** Suppresses history push while we ourselves drive navigation. */
let navigating = false;

export function activate(context: vscode.ExtensionContext) {
  repoRoot = vscode.workspace.workspaceFolders?.[0]?.uri.fsPath ?? process.cwd();
  distDir = path.join(context.extensionPath, "dist");

  context.subscriptions.push(
    vscode.commands.registerCommand("versoPreview.show", () => {
      const editor = vscode.window.activeTextEditor;
      if (editor && isVersoDoc(editor.document)) {
        showPreview(context, editor.document);
      } else if (panel) {
        panel.reveal(vscode.ViewColumn.Beside, true);
      } else {
        vscode.window.showInformationMessage(
          "Verso Preview: open a Verso document first " +
            "(a .lean file with a #doc (…) \"…\" => header)."
        );
      }
    }),
    vscode.commands.registerCommand("versoPreview.back", () => navigate(-1)),
    vscode.commands.registerCommand("versoPreview.forward", () => navigate(1))
  );

  context.subscriptions.push(
    vscode.workspace.onDidChangeTextDocument((e) => {
      if (
        panel &&
        trackedDoc &&
        e.document.uri.toString() === trackedDoc.uri.toString()
      ) {
        scheduleUpdate(e.document);
      }
    })
  );

  context.subscriptions.push(
    vscode.window.onDidChangeActiveTextEditor((editor) => {
      // Only retarget when switching to ANOTHER Verso doc; leave the preview
      // on the last one for non-Verso files (Mathlib, plain .lean, …).
      if (
        panel &&
        editor &&
        isVersoDoc(editor.document) &&
        editor.document.uri.toString() !== trackedDoc?.uri.toString()
      ) {
        track(editor.document);
        update(editor.document);
      }
    })
  );

  // After a window reload VSCode restores the panel (retainContextWhenHidden);
  // re-wire it so it reconnects and the webview's `ready` message gets content.
  context.subscriptions.push(
    vscode.window.registerWebviewPanelSerializer("versoPreview", {
      async deserializeWebviewPanel(p: vscode.WebviewPanel) {
        p.webview.options = webviewOptions(context);
        wirePanel(context, p);
      },
    })
  );
}

// A renderable Verso doc: a lean4 file with a `#doc (…)` header near the top.
function isVersoDoc(document: vscode.TextDocument): boolean {
  if (document.languageId !== "lean4") return false;
  const max = Math.min(document.lineCount, 60);
  for (let i = 0; i < max; i++) {
    if (/^\s*#doc\s*\(/.test(document.lineAt(i).text)) return true;
  }
  return false;
}

function showPreview(
  context: vscode.ExtensionContext,
  document: vscode.TextDocument
) {
  const column = vscode.ViewColumn.Beside;
  if (panel) {
    panel.reveal(column, true);
  } else {
    panel = vscode.window.createWebviewPanel(
      "versoPreview",
      "Verso Preview",
      { viewColumn: column, preserveFocus: true },
      webviewOptions(context)
    );
    wirePanel(context, panel);
  }
  track(document);
  update(document);
}

function webviewOptions(
  context: vscode.ExtensionContext
): vscode.WebviewPanelOptions & vscode.WebviewOptions {
  return {
    enableScripts: true,
    retainContextWhenHidden: true,
    localResourceRoots: [
      vscode.Uri.file(path.join(context.extensionPath, "dist")),
    ],
  };
}

// Attach lifecycle + message handlers and load the HTML. Shared by initial
// open and by the serializer that restores the panel after a window reload.
function wirePanel(context: vscode.ExtensionContext, p: vscode.WebviewPanel) {
  panel = p;
  p.onDidDispose(() => {
    panel = undefined;
    trackedDoc = undefined;
    if (updateTimer) clearTimeout(updateTimer); // don't fire a render post-dispose
  });
  p.webview.html = getHtml(context, p.webview);
  p.webview.onDidReceiveMessage((msg: WebviewToHost) => handleMessage(msg));
}

function track(document: vscode.TextDocument) {
  trackedDoc = document;
  if (panel) panel.title = "Verso: " + path.basename(document.fileName);

  // Record in history unless this tracking was itself driven by Back/Forward.
  if (!navigating) {
    const uri = document.uri.toString();
    if (history[histIndex] !== uri) {
      history.splice(histIndex + 1); // drop forward entries
      history.push(uri);
      histIndex = history.length - 1;
    }
  }
}

function scheduleUpdate(document: vscode.TextDocument) {
  if (updateTimer) clearTimeout(updateTimer);
  updateTimer = setTimeout(() => update(document), 150);
}

function post(msg: HostToWebview) {
  panel?.webview.postMessage(msg);
}

// The #doc title if present, else the filename — used in the history bar.
function docTitle(document: vscode.TextDocument): string {
  const max = Math.min(document.lineCount, 60);
  for (let i = 0; i < max; i++) {
    const m = document.lineAt(i).text.match(/#doc\s*\([^)]*\)\s*"([^"]*)"/);
    if (m) return m[1];
  }
  return path.basename(document.fileName);
}

// Path to the built verso-parse binary, or null if it isn't built yet. Searches
// every workspace folder (not just the first) for `.lake/build/bin/verso-parse`,
// so the extension works when the Lean project is one of several open folders.
function sidecarPath(): string | null {
  const rel = path.join(".lake", "build", "bin", "verso-parse");
  const roots = (vscode.workspace.workspaceFolders ?? []).map((f) => f.uri.fsPath);
  if (repoRoot && !roots.includes(repoRoot)) roots.unshift(repoRoot);
  for (const root of roots) {
    const p = path.join(root, rel);
    if (fs.existsSync(p)) return p;
  }
  return null;
}

// Monotonic id for temp-file uniqueness across concurrent renders.
let tmpSeq = 0;

// Run the sidecar on `text` (written to a temp file so unsaved edits are
// honored) and return the parsed document tree.
function runSidecar(text: string): Promise<VersoDoc> {
  return new Promise((resolve, reject) => {
    const bin = sidecarPath();
    if (!bin) {
      reject(new Error("verso-parse not built. Run: lake build verso-parse"));
      return;
    }
    // Unique per call — overlapping renders must not share/clobber one file.
    const tmp = path.join(
      os.tmpdir(),
      `verso-preview-${process.pid}-${tmpSeq++}.lean`
    );
    try {
      fs.writeFileSync(tmp, text, "utf8");
    } catch (e) {
      reject(e as Error);
      return;
    }
    // Timeout guards against a hung sidecar freezing all future previews.
    execFile(
      bin,
      [tmp],
      { maxBuffer: 1 << 26, timeout: 10000, killSignal: "SIGKILL" },
      (err, stdout, stderr) => {
        fs.rm(tmp, () => {});
        if (err) {
          reject(new Error(stderr || err.message));
          return;
        }
        try {
          resolve(JSON.parse(stdout) as VersoDoc);
        } catch (e) {
          reject(new Error("verso-parse: invalid JSON — " + (e as Error).message));
        }
      }
    );
  });
}

function update(document: vscode.TextDocument) {
  const seq = ++renderSeq;
  const title = docTitle(document);
  const canBack = histIndex > 0;
  const canForward = histIndex < history.length - 1;
  runSidecar(document.getText()).then(
    (doc) => {
      if (seq !== renderSeq) return; // a newer render superseded this one
      post({ type: "render", blocks: doc.blocks, title, canBack, canForward });
      // Coloring comes from the Lean server's semantic tokens — fetched
      // separately because they need the file elaborated (may lag the render).
      void sendTokens(document, seq);
    },
    (e: Error) => {
      if (seq !== renderSeq) return;
      post({ type: "error", message: e.message });
    }
  );
}

// Coloring is two layers, merged: the TextMate grammar (keywords/syntax/
// comments — the Lean LSP omits these) as the base, refined by the LSP's
// semantic tokens (elaborated identifiers/types) where they overlap. The
// grammar layer is synchronous and always available; the LSP layer lags until
// the file elaborates, so we post the grammar layer first, then upgrade.
async function sendTokens(document: vscode.TextDocument, seq: number) {
  // Layer 1: grammar (fast, no server needed).
  let base: import("./types").SemTok[] = [];
  try {
    base = await tokenizeGrammar(distDir, document.getText());
    if (seq !== renderSeq) return;
    if (base.length) post({ type: "tokens", tokens: base });
  } catch {
    /* grammar engine failed to load — fall through to LSP-only */
  }
  // Layer 2: LSP semantic tokens, merged over the grammar base.
  try {
    const legend = await vscode.commands.executeCommand<vscode.SemanticTokensLegend>(
      "vscode.provideDocumentSemanticTokensLegend",
      document.uri
    );
    const sem = await vscode.commands.executeCommand<vscode.SemanticTokens>(
      "vscode.provideDocumentSemanticTokens",
      document.uri
    );
    if (seq !== renderSeq || !legend || !sem) return;
    const lsp = decodeTokens(sem.data, legend.tokenTypes);
    post({ type: "tokens", tokens: mergeTokens(base, lsp) });
  } catch {
    /* server not ready — grammar layer already shown; refine on next render */
  }
}

// Merge LSP tokens over a grammar base. LSP tokens win on overlap (they carry
// elaboration info); grammar tokens fill everything else. Both are absolute
// (document-line) ranges.
function mergeTokens(
  base: import("./types").SemTok[],
  lsp: import("./types").SemTok[]
): import("./types").SemTok[] {
  if (!lsp.length) return base;
  const lspCovers = (t: import("./types").SemTok) =>
    lsp.some(
      (l) => l.line === t.line && t.col < l.col + l.len && l.col < t.col + t.len
    );
  return base.filter((t) => !lspCovers(t)).concat(lsp);
}

// Decode the LSP packed format: groups of 5 ints
// [deltaLine, deltaStartChar, length, tokenTypeIndex, tokenModifiers],
// each relative to the previous token. See the LSP semantic-tokens spec.
function decodeTokens(data: Uint32Array, types: string[]): import("./types").SemTok[] {
  const out: import("./types").SemTok[] = [];
  let line = 0;
  let col = 0;
  for (let i = 0; i + 4 < data.length; i += 5) {
    const dLine = data[i];
    const dCol = data[i + 1];
    const len = data[i + 2];
    const typeIdx = data[i + 3];
    if (dLine > 0) {
      line += dLine;
      col = dCol;
    } else {
      col += dCol;
    }
    const type = types[typeIdx] ?? "";
    if (type) out.push({ line, col, len, type });
  }
  return out;
}

// Move the history cursor by delta (-1 back, +1 forward), re-render + reveal.
async function navigate(delta: number) {
  const target = histIndex + delta;
  if (target < 0 || target >= history.length) return;
  const prevIndex = histIndex;
  histIndex = target;
  const uri = vscode.Uri.parse(history[histIndex]);
  navigating = true;
  try {
    const doc = await vscode.workspace.openTextDocument(uri);
    trackedDoc = doc;
    if (panel) panel.title = "Verso: " + path.basename(doc.fileName);
    update(doc);
    // Reveal in the editor (the preview follows the doc you navigate to).
    await vscode.window.showTextDocument(doc, {
      viewColumn: vscode.ViewColumn.One,
      preserveFocus: true,
    });
  } catch {
    // Target doc gone (deleted/renamed): drop the dead entry and restore.
    history.splice(target, 1);
    histIndex = prevIndex <= target ? prevIndex : prevIndex - 1;
  } finally {
    navigating = false;
  }
}

async function handleMessage(msg: WebviewToHost) {
  // The webview just mounted (initial load OR after a window reload) and is now
  // listening. Re-send the current content so it never sits empty due to a
  // message sent before the listener was attached.
  if (msg.type === "ready") {
    const doc = trackedDoc ?? vscode.window.activeTextEditor?.document;
    if (doc && isVersoDoc(doc)) {
      // Re-send content without mutating history: a reload/restore shouldn't
      // truncate forward entries or re-push the current doc. If history is
      // empty (fresh load), seed it with this doc.
      if (history.length === 0) track(doc);
      else trackedDoc = doc;
      update(doc);
    }
    return;
  }

  if (msg.type === "back") {
    await navigate(-1);
    return;
  }
  if (msg.type === "forward") {
    await navigate(1);
    return;
  }

  if (!trackedDoc) return;
  const uri = trackedDoc.uri;

  if (msg.type === "hover") {
    const pos = new vscode.Position(msg.line, msg.col);
    let html = "";
    try {
      const hovers = await vscode.commands.executeCommand<vscode.Hover[]>(
        "vscode.executeHoverProvider",
        uri,
        pos
      );
      html = renderHovers(hovers);
    } catch {
      /* server not ready / no hover */
    }
    post({ type: "hoverResult", html, line: msg.line, col: msg.col, token: msg.token });
    return;
  }

  if (msg.type === "goto") {
    const pos = new vscode.Position(msg.line, msg.col);
    try {
      const defs = await vscode.commands.executeCommand<
        Array<vscode.Location | vscode.LocationLink>
      >("vscode.executeDefinitionProvider", uri, pos);
      const target = Array.isArray(defs) ? defs[0] : defs;
      if (target) {
        const loc =
          "targetUri" in target
            ? {
                uri: target.targetUri,
                range: target.targetSelectionRange ?? target.targetRange,
              }
            : { uri: (target as vscode.Location).uri, range: (target as vscode.Location).range };
        const doc = await vscode.workspace.openTextDocument(loc.uri);
        await vscode.window.showTextDocument(doc, {
          viewColumn: vscode.ViewColumn.One,
          selection: loc.range,
          preserveFocus: false,
        });
      }
    } catch {
      /* no definition */
    }
    return;
  }
}

// Verso's own markup-directive docstrings leak into hovers at the edges of a
// ```lean block (column 0 of the first line resolves to the surrounding code-
// block syntax node). They describe the *markup*, not the Lean code, so drop
// them — the user is hovering code, not documentation about code fences.
function isVersoMarkupDoc(value: string): boolean {
  return (
    /code block that contains literal code/i.test(value) ||
    /Code blocks have the following syntax/i.test(value) ||
    /^A (block|inline|directive)\b/i.test(value.trim())
  );
}

function renderHovers(hovers: vscode.Hover[] | undefined): string {
  if (!hovers || !hovers.length) return "";
  const parts: string[] = [];
  for (const h of hovers) {
    for (const c of h.contents) {
      const value = typeof c === "string" ? c : (c as vscode.MarkdownString).value;
      if (value && !isVersoMarkupDoc(value)) parts.push(value);
    }
  }
  if (!parts.length) return "";
  // Join sections with an explicit thematic break, then render with marked.
  const md = parts.join("\n\n---\n\n");
  return marked.parse(md, { async: false }) as string;
}

function getHtml(context: vscode.ExtensionContext, webview: vscode.Webview): string {
  const scriptUri = webview.asWebviewUri(
    vscode.Uri.file(path.join(context.extensionPath, "dist", "webview.js"))
  );
  const styleUri = webview.asWebviewUri(
    vscode.Uri.file(path.join(context.extensionPath, "dist", "webview.css"))
  );
  const csp = webview.cspSource;
  const nonce = makeNonce();
  return `<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8" />
<meta http-equiv="Content-Security-Policy" content="default-src 'none';
  img-src ${csp} https: data:;
  style-src ${csp} 'unsafe-inline' https://cdn.jsdelivr.net;
  font-src ${csp} https://cdn.jsdelivr.net;
  script-src 'nonce-${nonce}' https://cdn.jsdelivr.net;" />
<link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/katex@0.16.9/dist/katex.min.css" />
<link rel="stylesheet" href="${styleUri}" />
<script defer nonce="${nonce}" src="https://cdn.jsdelivr.net/npm/katex@0.16.9/dist/katex.min.js"></script>
</head>
<body>
<div id="root"></div>
<script nonce="${nonce}" src="${scriptUri}"></script>
</body>
</html>`;
}

function makeNonce(): string {
  let s = "";
  const chars = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789";
  for (let i = 0; i < 32; i++) s += chars.charAt(Math.floor(Math.random() * chars.length));
  return s;
}

export function deactivate() {}
