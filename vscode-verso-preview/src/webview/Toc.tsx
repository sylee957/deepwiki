import { useEffect, useRef, useState } from "react";
import type { TocEntry } from "./tocData";

// The fixed history bar height (see styles.css .histbar) — scroll targets are
// offset by this much so a heading lands below the bar, not under it.
const BAR = 34;
// Min header level present, used to indent relative to the shallowest heading
// (so a doc whose top level is h2 doesn't start deeply indented).

/**
 * Toggle-overlay Table of Contents. A panel floating below the history bar;
 * clicking an entry scrolls its heading into view. Tracks the active section
 * via scroll position and highlights it. Closes on entry click, Escape, or an
 * outside click.
 */
export function Toc({
  entries,
  open,
  onClose,
}: {
  entries: TocEntry[];
  open: boolean;
  onClose: () => void;
}) {
  const [active, setActive] = useState<string>("");
  const panelRef = useRef<HTMLDivElement>(null);

  // Scroll-spy: the active entry is the last heading whose top is at/above the
  // bar line. Runs on scroll and on open (to sync when first shown).
  useEffect(() => {
    if (!open || entries.length === 0) return;
    const recompute = () => {
      let current = entries[0].id;
      for (const e of entries) {
        const el = document.getElementById(e.id);
        if (!el) continue;
        if (el.getBoundingClientRect().top - BAR <= 1) current = e.id;
        else break;
      }
      setActive(current);
    };
    recompute();
    window.addEventListener("scroll", recompute, true);
    return () => window.removeEventListener("scroll", recompute, true);
  }, [open, entries]);

  // Dismiss on Escape or a click outside the panel (but not the toggle button,
  // which manages its own toggle).
  useEffect(() => {
    if (!open) return;
    const onKey = (e: KeyboardEvent) => {
      if (e.key === "Escape") onClose();
    };
    const onDown = (e: MouseEvent) => {
      const t = e.target as HTMLElement;
      if (panelRef.current && !panelRef.current.contains(t) && !t.closest(".toc-toggle")) {
        onClose();
      }
    };
    window.addEventListener("keydown", onKey);
    window.addEventListener("mousedown", onDown, true);
    return () => {
      window.removeEventListener("keydown", onKey);
      window.removeEventListener("mousedown", onDown, true);
    };
  }, [open, onClose]);

  if (!open) return null;

  const minLevel = entries.reduce((m, e) => Math.min(m, e.level), Infinity);

  const go = (id: string) => {
    const el = document.getElementById(id);
    if (!el) return;
    const y = el.getBoundingClientRect().top + window.scrollY - BAR - 8;
    window.scrollTo({ top: Math.max(0, y), behavior: "smooth" });
    setActive(id);
    onClose();
  };

  return (
    <div className="toc-panel" ref={panelRef} role="navigation" aria-label="Table of contents">
      {entries.length === 0 ? (
        <div className="toc-empty">No headings</div>
      ) : (
        <ul className="toc-list">
          {entries.map((e) => (
            <li
              key={e.id}
              className={"toc-item" + (e.id === active ? " active" : "")}
              style={{ paddingLeft: 10 + (e.level - minLevel) * 14 }}
              title={e.text}
              onClick={() => go(e.id)}
            >
              {e.text}
            </li>
          ))}
        </ul>
      )}
    </div>
  );
}
