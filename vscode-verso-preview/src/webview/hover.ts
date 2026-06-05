// Resolve the exact source (line, column) under a screen point inside a
// `.cline` element whose textContent equals the source line verbatim. The
// column is the UTF-16 offset from the line start to the caret — exactly what
// the Lean LSP and vscode.Position expect (Lean uses UTF-16 columns; Lean math
// symbols are single UTF-16 units, so JS string indices map 1:1).

export interface SourcePos {
  line: number;
  col: number;
  cline: HTMLElement;
  /** The caret hit used to resolve this position (reused to draw the mark). */
  hit: CaretHit;
}

export interface CaretHit {
  node: Node;
  offset: number;
}

/**
 * True only if the resolved column sits on a non-whitespace character of the
 * line — i.e. an actual token worth querying. Hovering the margin, the padding
 * between lines, or past a line's end snaps the caret to whitespace / out of
 * bounds; querying those returns junk (e.g. the code-fence's own help text), so
 * we skip them.
 */
export function isQueryable(pos: SourcePos): boolean {
  const text = pos.cline.textContent ?? "";
  if (pos.col < 0 || pos.col >= text.length) return false;
  const ch = text[pos.col];
  return !!ch && !/\s/.test(ch);
}

/**
 * Client rect for a [startCol, endCol) span on the line element `cline`,
 * measured via a DOM Range over the line's text. Used to draw the hover
 * indicator over the exact token range the LSP reports (not a guessed run).
 */
export function rectForCols(
  cline: HTMLElement,
  startCol: number,
  endCol: number
): DOMRect | null {
  // Walk text nodes to translate absolute columns → (node, offset) endpoints.
  const walker = document.createTreeWalker(cline, NodeFilter.SHOW_TEXT);
  let acc = 0;
  let startNode: Node | null = null;
  let startOff = 0;
  let endNode: Node | null = null;
  let endOff = 0;
  let t: Node | null;
  while ((t = walker.nextNode())) {
    const len = (t.nodeValue || "").length;
    if (!startNode && startCol <= acc + len) {
      startNode = t;
      startOff = startCol - acc;
    }
    if (endCol <= acc + len) {
      endNode = t;
      endOff = endCol - acc;
      break;
    }
    acc += len;
  }
  if (!startNode || !endNode) return null;
  const r = document.createRange();
  r.setStart(startNode, startOff);
  r.setEnd(endNode, endOff);
  return r.getBoundingClientRect();
}

function caretFromPoint(x: number, y: number): CaretHit | null {
  const anyDoc = document as unknown as {
    caretPositionFromPoint?: (
      x: number,
      y: number
    ) => { offsetNode: Node; offset: number } | null;
    caretRangeFromPoint?: (x: number, y: number) => Range | null;
  };
  if (anyDoc.caretPositionFromPoint) {
    const cp = anyDoc.caretPositionFromPoint(x, y);
    if (!cp) return null;
    return { node: cp.offsetNode, offset: cp.offset };
  }
  if (anyDoc.caretRangeFromPoint) {
    const r = anyDoc.caretRangeFromPoint(x, y);
    if (!r) return null;
    return { node: r.startContainer, offset: r.startOffset };
  }
  return null;
}

export function posFromPoint(x: number, y: number): SourcePos | null {
  const hit = caretFromPoint(x, y);
  if (!hit) return null;
  const startEl =
    hit.node.nodeType === Node.TEXT_NODE
      ? (hit.node.parentNode as HTMLElement | null)
      : (hit.node as HTMLElement);
  const cline = startEl?.closest(".cline") as HTMLElement | null;
  if (!cline) return null;
  const line = parseInt(cline.getAttribute("data-l") || "-1", 10);
  if (line < 0) return null;

  let col = 0;
  const walker = document.createTreeWalker(cline, NodeFilter.SHOW_TEXT);
  let t: Node | null;
  while ((t = walker.nextNode())) {
    if (t === hit.node) {
      col += hit.offset;
      return { line, col, cline, hit };
    }
    col += (t.nodeValue || "").length;
  }
  return { line, col, cline, hit };
}
