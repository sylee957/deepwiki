// The document tree emitted by the `verso-parse` Lean sidecar (Verso's own
// parser). The webview renders this directly — there is no TS markup parser.

/** Source range: 1-based line, 0-based column. */
export interface Range {
  sl: number;
  sc: number;
  el: number;
  ec: number;
}

export type Inline =
  | { t: "text"; s: string }
  | { t: "break" }
  | { t: "code"; s: string }
  | { t: "math"; display: boolean; s: string }
  | { t: "emph"; kids: Inline[] }
  | { t: "bold"; kids: Inline[] }
  | { t: "link"; kids: Inline[] };

export type Block =
  | { kind: "para"; range: Range; kids: Inline[] }
  | { kind: "header"; range: Range; level: number; kids: Inline[] }
  | { kind: "code"; range: Range; text: string }
  | { kind: "blockquote"; range: Range; kids: Block[] }
  | { kind: "list"; range: Range; ordered: boolean; items: Block[][] };

/** The full sidecar payload. */
export interface VersoDoc {
  blocks: Block[];
  errors: number;
}
