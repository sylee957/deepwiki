// Message protocol between the extension host and the webview.

import type { Block } from "./doc";

/** Host → webview: render this parsed document tree (from the sidecar). */
export interface RenderMsg {
  type: "render";
  blocks: Block[];
  /** Short title for the history bar (e.g. the file's #doc title). */
  title: string;
  /** Whether Back / Forward navigation is currently available. */
  canBack: boolean;
  canForward: boolean;
}

/** Host → webview: parsing failed (sidecar missing / errored). */
export interface ErrorMsg {
  type: "error";
  message: string;
}

/** Host → webview: user-configured code token colors (token type → CSS color).
 * Applied as CSS custom properties; missing keys fall back to the CSS default. */
export interface ColorsMsg {
  type: "colors";
  colors: Record<string, string>;
}

/** One decoded semantic token: a colored span on a source line. */
export interface SemTok {
  line: number; // 0-based source line
  col: number; // 0-based UTF-16 start column
  len: number; // length in UTF-16 units
  type: string; // legend name, e.g. "keyword", "function"
}

/** Host → webview: semantic tokens for the tracked doc (code coloring). */
export interface TokensMsg {
  type: "tokens";
  tokens: SemTok[];
}

/** Host → webview: result of an LSP hover query. */
export interface HoverResultMsg {
  type: "hoverResult";
  /** Sanitized HTML of the hover, or "" if none. */
  html: string;
  line: number;
  col: number;
  /** Echoes the request token so the webview can drop stale results. */
  token: number;
}

export type HostToWebview =
  | RenderMsg
  | HoverResultMsg
  | ErrorMsg
  | TokensMsg
  | ColorsMsg;

/** Webview → host: query a hover at a source position. */
export interface HoverReqMsg {
  type: "hover";
  line: number;
  col: number;
  token: number;
}

/** Webview → host: go to definition at a source position. */
export interface GotoMsg {
  type: "goto";
  line: number;
  col: number;
}

/** Webview → host: the React app has mounted and is listening; send content. */
export interface ReadyMsg {
  type: "ready";
}

/** Webview → host: navigate the preview history. */
export interface NavMsg {
  type: "back" | "forward";
}

export type WebviewToHost = HoverReqMsg | GotoMsg | ReadyMsg | NavMsg;
