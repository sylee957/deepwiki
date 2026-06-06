// Build the Table of Contents from the parsed document tree. Headers carry a
// level and inline children; we flatten the inlines to plain text for the TOC
// label and reuse the same source-line-derived id the renderer assigns, so a
// click can scroll to the matching heading element.

import type { Block, Inline } from "../doc";
import { headerId } from "./Preview";

export interface TocEntry {
  id: string;
  level: number;
  text: string;
}

/** Flatten inline nodes to their visible text (TOC labels are plain text). */
function inlineText(nodes: Inline[]): string {
  let out = "";
  for (const n of nodes) {
    switch (n.t) {
      case "text":
      case "code":
      case "math":
        out += n.s;
        break;
      case "break":
        out += " ";
        break;
      case "emph":
      case "bold":
      case "link":
        out += inlineText(n.kids);
        break;
    }
  }
  return out;
}

/** Collect every header (any nesting depth) into a flat, in-order TOC list. */
export function buildToc(blocks: Block[]): TocEntry[] {
  const entries: TocEntry[] = [];
  const visit = (bs: Block[]) => {
    for (const b of bs) {
      if (b.kind === "header") {
        const text = inlineText(b.kids).trim();
        if (text) entries.push({ id: headerId(b.range.sl), level: b.level, text });
      } else if (b.kind === "blockquote") {
        visit(b.kids);
      } else if (b.kind === "list") {
        for (const item of b.items) visit(item);
      }
    }
  };
  visit(blocks);
  return entries;
}
