#!/usr/bin/env python3
"""Regenerate (or --check) the `#L<n>` source-line anchors in docs/*.md.

Every tutorial link of the form

    [`declName`](../DeepWiki/.../File.lean#L123)

has its line number rewritten to wherever `declName` is *currently* defined in
that file, so the local source links never go stale. The link text (the
backticked name) is the lookup key; the path is resolved relative to the .md.

    python3 scripts/regen-doc-links.py            # rewrite in place
    python3 scripts/regen-doc-links.py --check    # report staleness; exit 1 if any

Exit status is non-zero if any link is stale (--check) or unresolvable, so this
doubles as a CI guard.
"""
import re
import sys
import pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
DOCS = ROOT / "docs"

# [`name`](some/relative/path.lean) optionally followed by #L<n>
LINK = re.compile(r'\[`([^`]+)`\]\(([^)#]+\.lean)(#L\d+)?\)')

DECL_KW = r'(?:def|theorem|lemma|abbrev|structure|class|instance|inductive)'
MODIFIERS = r'(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|scoped\s+|local\s+)*'
ATTRS = r'(?:@\[[^\]]*\]\s*)*'


def find_line(lean: pathlib.Path, name: str):
    pat = re.compile(rf'^\s*{ATTRS}{MODIFIERS}{DECL_KW}\s+{re.escape(name)}\b')
    for i, line in enumerate(lean.read_text().splitlines(), 1):
        if pat.search(line):
            return i
    return None


def main() -> int:
    check = "--check" in sys.argv
    if not DOCS.is_dir():
        print(f"no docs/ directory at {DOCS}")
        return 0

    stale: list[str] = []
    missing: list[str] = []

    for md in sorted(DOCS.glob("*.md")):
        src = md.read_text()

        def repl(m: re.Match) -> str:
            name, rel, anchor = m.group(1), m.group(2), m.group(3) or ""
            lean = (md.parent / rel).resolve()
            if not lean.exists():
                missing.append(f"{md.name}: `{name}` -> {rel} (file not found)")
                return m.group(0)
            ln = find_line(lean, name)
            if ln is None:
                missing.append(f"{md.name}: `{name}` not found in {rel}")
                return m.group(0)
            new_anchor = f"#L{ln}"
            if anchor != new_anchor:
                stale.append(f"{md.name}: `{name}` {anchor or '(none)'} -> {new_anchor}")
            return f'[`{name}`]({rel}{new_anchor})'

        new_src = LINK.sub(repl, src)
        if not check and new_src != src:
            md.write_text(new_src)

    for s in stale:
        print(("STALE " if check else "updated ") + s)
    for s in missing:
        print(("MISSING " if check else "WARNING ") + s)

    if check:
        if stale or missing:
            print(f"{len(stale)} stale, {len(missing)} unresolved")
            return 1
        print("all source-line links current")
        return 0

    print(f"{len(stale)} link(s) updated; {len(missing)} unresolved")
    return 1 if missing else 0


if __name__ == "__main__":
    sys.exit(main())
