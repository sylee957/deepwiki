// TextMate-grammar tokenization of Lean code blocks, host-side. This colors
// keywords/syntax exactly like the editor (the Lean LSP semantic-token layer
// omits keywords — they come from the grammar). The two layers are merged:
// grammar tokens give the base coloring, LSP semantic tokens refine identifiers.

import * as path from "path";
import * as fs from "fs";
import * as oniguruma from "vscode-oniguruma";
import * as vsctm from "vscode-textmate";
import type { SemTok } from "./types";

let registry: vsctm.Registry | null = null;
let grammarPromise: Promise<vsctm.IGrammar | null> | null = null;

// Initialize the oniguruma WASM engine + a registry that serves the bundled
// Lean grammar. Idempotent; assets live in dist/ (copied at build time).
function getRegistry(distDir: string): vsctm.Registry {
  if (registry) return registry;
  const wasmPath = path.join(distDir, "onig.wasm");
  // Pass the Buffer (a Uint8Array view) directly — NOT `.buffer`, whose raw
  // ArrayBuffer may be a larger shared pool buffer with a nonzero byteOffset
  // for small reads, corrupting the WASM load.
  const wasmBin = fs.readFileSync(wasmPath);
  const onigLib = oniguruma.loadWASM(wasmBin).then(() => ({
    createOnigScanner: (sources: string[]) => new oniguruma.OnigScanner(sources),
    createOnigString: (s: string) => new oniguruma.OnigString(s),
  }));
  registry = new vsctm.Registry({
    onigLib,
    loadGrammar: async (scopeName: string) => {
      if (scopeName !== "source.lean4") return null;
      const raw = fs.readFileSync(path.join(distDir, "lean4.json"), "utf8");
      return vsctm.parseRawGrammar(raw, "lean4.json");
    },
  });
  return registry;
}

function getGrammar(distDir: string): Promise<vsctm.IGrammar | null> {
  if (!grammarPromise) {
    // On failure, null out the cached promise + registry so a later render can
    // retry instead of being permanently stuck on a poisoned rejected promise.
    grammarPromise = getRegistry(distDir)
      .loadGrammar("source.lean4")
      .catch(() => {
        grammarPromise = null;
        registry = null;
        return null;
      });
  }
  return grammarPromise;
}

// Map a TextMate scope stack to one of our CSS-class token type names. We test
// the most specific (innermost) scope first and fall back outward. The names
// returned match the keys used by the webview's TOK_CLASS.
function scopeToType(scopes: string[]): string | null {
  // innermost scope is last
  for (let i = scopes.length - 1; i >= 0; i--) {
    const s = scopes[i];
    if (s.startsWith("comment")) return "comment";
    if (s.startsWith("string")) return "string";
    if (s.startsWith("constant.numeric")) return "number";
    if (s.startsWith("keyword")) return "keyword";
    if (s.startsWith("storage")) return "keyword"; // storage.type etc.
    if (s.startsWith("support.type") || s.startsWith("entity.name.type"))
      return "type";
    if (s.startsWith("entity.name.function")) return "function";
    if (s.startsWith("entity.name.namespace") || s.startsWith("entity.name.section"))
      return "namespace";
    if (s.startsWith("variable")) return "variable";
    if (s.startsWith("punctuation.definition.comment")) return "comment";
  }
  return null;
}

// Tokenize `text` with the Lean grammar and return per-line SemTok spans
// (line is 0-based, relative to the text; the caller offsets by the block's
// source line). Returns [] if the engine isn't ready yet.
export async function tokenizeGrammar(
  distDir: string,
  text: string
): Promise<SemTok[]> {
  let grammar: vsctm.IGrammar | null;
  try {
    grammar = await getGrammar(distDir);
  } catch {
    return []; // engine failed to load — degrade to no grammar coloring
  }
  if (!grammar) return [];
  const lines = text.split("\n");
  const out: SemTok[] = [];
  let ruleStack = vsctm.INITIAL;
  for (let line = 0; line < lines.length; line++) {
    const r = grammar.tokenizeLine(lines[line], ruleStack);
    for (const tok of r.tokens) {
      const type = scopeToType(tok.scopes);
      if (type) {
        out.push({
          line,
          col: tok.startIndex,
          len: tok.endIndex - tok.startIndex,
          type,
        });
      }
    }
    ruleStack = r.ruleStack;
  }
  return out;
}
