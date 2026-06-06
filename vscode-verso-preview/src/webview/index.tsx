import { useEffect, useMemo, useRef, useState, useCallback } from "react";
import { createRoot } from "react-dom/client";
import { Preview } from "./Preview";
import { Toc } from "./Toc";
import { buildToc } from "./tocData";
import { posFromPoint, rectForCols, isQueryable } from "./hover";
import type { HostToWebview, WebviewToHost, SemTok } from "../types";
import type { Block } from "../doc";
import "./styles.css";

interface VsCodeApi {
  postMessage: (msg: WebviewToHost) => void;
}
declare function acquireVsCodeApi(): VsCodeApi;
const vscode = acquireVsCodeApi();

interface TipState {
  visible: boolean;
  html: string;
  x: number;
  y: number;
  line: number;
  col: number;
}

const HIDDEN: TipState = { visible: false, html: "", x: 0, y: 0, line: -1, col: -1 };

function App() {
  const [blocks, setBlocks] = useState<Block[]>([]);
  // Semantic tokens indexed by source line → colored spans for that line.
  const [tokens, setTokens] = useState<Map<number, SemTok[]>>(new Map());
  const [error, setError] = useState<string>("");
  const [nav, setNav] = useState({ title: "", canBack: false, canForward: false });
  const [tip, setTip] = useState<TipState>(HIDDEN);
  // Highlight rectangle for the hovered identifier (the "indicator").
  const [mark, setMark] = useState<DOMRect | null>(null);
  const [tocOpen, setTocOpen] = useState(false);
  // Table-of-contents entries derived from the document's headers.
  const toc = useMemo(() => buildToc(blocks), [blocks]);

  const tokenRef = useRef(0);
  const hoverTimer = useRef<ReturnType<typeof setTimeout> | undefined>(undefined);
  const hideTimer = useRef<ReturnType<typeof setTimeout> | undefined>(undefined);
  // The token currently shown/queried: line, start col, and end col (exclusive).
  const pendingRef = useRef<{ line: number; col: number; end: number }>({
    line: -1,
    col: -1,
    end: -1,
  });
  // Latest tokens, readable from the (memoized) mouse handler without re-binding.
  const tokensRef = useRef<Map<number, SemTok[]>>(new Map());
  // Where the tooltip will appear once (if) the LSP returns content.
  const anchorRef = useRef<{ x: number; y: number }>({ x: 0, y: 0 });

  // Receive messages from the extension host.
  useEffect(() => {
    const onMsg = (e: MessageEvent<HostToWebview>) => {
      const msg = e.data;
      if (msg.type === "render") {
        setBlocks(msg.blocks);
        tokensRef.current = new Map();
        setTokens(tokensRef.current); // cleared until fresh tokens arrive
        setError("");
        setNav({ title: msg.title, canBack: msg.canBack, canForward: msg.canForward });
        // Re-render is a navigation/content change — clear any open hover and
        // close the TOC (its anchors point at the previous document).
        setTip(HIDDEN);
        setMark(null);
        setTocOpen(false);
      } else if (msg.type === "tokens") {
        const byLine = new Map<number, SemTok[]>();
        for (const t of msg.tokens) {
          const arr = byLine.get(t.line);
          if (arr) arr.push(t);
          else byLine.set(t.line, [t]);
        }
        tokensRef.current = byLine;
        setTokens(byLine);
      } else if (msg.type === "colors") {
        // Apply configured token colors as CSS custom properties (--tok-*);
        // the stylesheet's hex values remain the fallback for unset keys.
        const root = document.documentElement.style;
        for (const [key, val] of Object.entries(msg.colors)) {
          root.setProperty(`--tok-${key}`, val);
        }
      } else if (msg.type === "error") {
        setError(msg.message);
        setBlocks([]);
        setTip(HIDDEN);
        setMark(null);
      } else if (msg.type === "hoverResult") {
        if (msg.token !== tokenRef.current) return; // stale
        if (
          pendingRef.current.line !== msg.line ||
          pendingRef.current.col !== msg.col
        )
          return;
        // Show the tooltip ONLY now that the LSP has responded with content,
        // at the anchor recorded when the hover started. Empty → stay hidden
        // (no "…" placeholder, no flicker while the server is loading).
        if (!msg.html) {
          setTip(HIDDEN);
        } else {
          setTip({
            visible: true,
            html: msg.html,
            x: anchorRef.current.x,
            y: anchorRef.current.y,
            line: msg.line,
            col: msg.col,
          });
        }
      }
    };
    window.addEventListener("message", onMsg);
    // Tell the host we're listening so it (re)sends content — covers both the
    // initial mount and restoration after a window reload, with no timing race.
    vscode.postMessage({ type: "ready" });
    return () => window.removeEventListener("message", onMsg);
  }, []);

  const dismiss = useCallback(() => {
    if (hoverTimer.current) clearTimeout(hoverTimer.current);
    setTip(HIDDEN);
    setMark(null);
    pendingRef.current = { line: -1, col: -1, end: -1 };
  }, []);

  // The overlays are fixed-positioned at viewport coords captured on hover, so
  // they'd "float" if the content scrolled under them. Dismiss on any scroll
  // (capture phase catches nested scrollers too) — matches editor hovers.
  useEffect(() => {
    const onScroll = () => dismiss();
    window.addEventListener("scroll", onScroll, true);
    return () => window.removeEventListener("scroll", onScroll, true);
  }, [dismiss]);

  // Schedule the tooltip to fade after a short grace period. Re-entering a
  // token (which cancels hideTimer at the top of onMouseMove / on tip enter)
  // aborts the pending hide, so moving across a gap stays flicker-free.
  const scheduleHide = useCallback(() => {
    if (hoverTimer.current) clearTimeout(hoverTimer.current);
    if (hideTimer.current) clearTimeout(hideTimer.current);
    hideTimer.current = setTimeout(() => {
      setTip(HIDDEN);
      setMark(null);
      pendingRef.current = { line: -1, col: -1, end: -1 };
    }, 220);
  }, []);

  const onMouseMove = useCallback((e: React.MouseEvent) => {
    const target = e.target as HTMLElement;
    // Off any code line (prose, gaps between blocks): let the tooltip fade.
    if (!target.closest(".cline")) return scheduleHide();
    if (hideTimer.current) clearTimeout(hideTimer.current);
    const x = e.clientX;
    const y = e.clientY;
    const p = posFromPoint(x, y);
    // Margin / whitespace / past line end: not on a token, so dismiss it.
    if (!p || !isQueryable(p)) return scheduleHide();
    // The unit of "same thing" is the TOKEN, not the exact column. Moving the
    // cursor within the token already shown does nothing — no re-query, no
    // hide, no flicker. Re-query only when entering a DIFFERENT token.
    const lineToks = tokensRef.current.get(p.line) ?? [];
    const tok = lineToks.find((t) => p.col >= t.col && p.col < t.col + t.len);
    // Token range if known; otherwise fall back to the single caret column
    // (so hovers still work before semantic tokens have loaded).
    const startCol = tok ? tok.col : p.col;
    const endCol = tok ? tok.col + tok.len : p.col + 1;
    const cur = pendingRef.current;
    if (cur.line === p.line && p.col >= cur.col && p.col < cur.end) {
      return; // still inside the current token/position — no flicker
    }
    pendingRef.current = { line: p.line, col: startCol, end: endCol };
    // Indicator highlights the exact token range when known.
    const rect = tok ? rectForCols(p.cline, startCol, endCol) : null;
    setMark(rect);
    // Record where the tooltip will appear. We do NOT hide the current tooltip
    // here — it stays until the new content arrives, avoiding a blank flash.
    const anchor = rect ?? p.cline.getBoundingClientRect();
    anchorRef.current = { x: anchor.left, y: anchor.bottom + 6 };
    if (hoverTimer.current) clearTimeout(hoverTimer.current);
    const my = ++tokenRef.current;
    const queryCol = startCol; // token start when known, else the caret column
    hoverTimer.current = setTimeout(() => {
      vscode.postMessage({ type: "hover", line: p.line, col: queryCol, token: my });
    }, 60);
  }, [scheduleHide]);

  const onMouseLeave = useCallback(() => scheduleHide(), [scheduleHide]);

  const onClick = useCallback((e: React.MouseEvent) => {
    const target = e.target as HTMLElement;
    if (!target.closest(".cline")) return;
    if (e.metaKey || e.ctrlKey) {
      e.preventDefault();
      const p = posFromPoint(e.clientX, e.clientY);
      if (p && isQueryable(p)) {
        vscode.postMessage({ type: "goto", line: p.line, col: p.col });
      }
    }
  }, []);

  return (
    <>
      <div className="histbar">
        <button
          className="navbtn"
          disabled={!nav.canBack}
          title="Back (Alt+←)"
          onClick={() => vscode.postMessage({ type: "back" })}
        >
          ←
        </button>
        <button
          className="navbtn"
          disabled={!nav.canForward}
          title="Forward (Alt+→)"
          onClick={() => vscode.postMessage({ type: "forward" })}
        >
          →
        </button>
        <button
          className={"navbtn toc-toggle" + (tocOpen ? " active" : "")}
          disabled={toc.length === 0}
          title="Table of contents"
          aria-expanded={tocOpen}
          onClick={() => setTocOpen((v) => !v)}
        >
          ☰
        </button>
        <span className="histtitle">{nav.title}</span>
      </div>
      <Toc entries={toc} open={tocOpen} onClose={() => setTocOpen(false)} />
      <div
        className="doc"
        onMouseMove={onMouseMove}
        onMouseLeave={onMouseLeave}
        onClick={onClick}
      >
        {error ? (
          <div className="parse-error">{error}</div>
        ) : (
          <Preview blocks={blocks} tokens={tokens} />
        )}
      </div>
      {mark && (
        <div
          className="hover-mark"
          style={{
            left: mark.left,
            top: mark.top,
            width: mark.width,
            height: mark.height,
          }}
        />
      )}
      {tip.visible && tip.html && (
        <div
          className="tip"
          style={{ left: Math.max(8, Math.min(tip.x, window.innerWidth - 580)), top: tip.y }}
          onMouseEnter={() => hideTimer.current && clearTimeout(hideTimer.current)}
          onMouseLeave={onMouseLeave}
          dangerouslySetInnerHTML={{ __html: tip.html }}
        />
      )}
    </>
  );
}

const root = createRoot(document.getElementById("root")!);
root.render(<App />);
