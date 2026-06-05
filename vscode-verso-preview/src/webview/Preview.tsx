import { Fragment } from "react";
import type { Block, Inline } from "../doc";
import type { SemTok } from "../types";

// Lean semantic-token type → CSS class. Lean emits keyword/variable/property/
// function plus the standard string/number/comment/operator/type.
const TOK_CLASS: Record<string, string> = {
  keyword: "k",
  function: "fn",
  property: "pr",
  variable: "va",
  type: "t",
  namespace: "ns",
  string: "s",
  number: "n",
  comment: "c",
  operator: "op",
  leanSorryLike: "sorry",
};

// Split one source line into colored spans using the semantic tokens on that
// line. The concatenated text MUST equal `line` exactly (the position layer
// depends on .cline.textContent === source line), so gaps between tokens are
// emitted as plain text.
function colorLine(line: string, toks: SemTok[] | undefined) {
  if (!toks || toks.length === 0) return line;
  const sorted = [...toks].sort((a, b) => a.col - b.col);
  const parts: React.ReactNode[] = [];
  let pos = 0;
  let key = 0;
  for (const t of sorted) {
    if (t.col < pos) continue; // overlap guard
    if (t.col > pos) parts.push(<Fragment key={key++}>{line.slice(pos, t.col)}</Fragment>);
    const end = Math.min(t.col + t.len, line.length);
    const cls = TOK_CLASS[t.type];
    const text = line.slice(t.col, end);
    parts.push(
      cls ? (
        <span className={cls} key={key++}>
          {text}
        </span>
      ) : (
        <Fragment key={key++}>{text}</Fragment>
      )
    );
    pos = end;
  }
  if (pos < line.length) parts.push(<Fragment key={key++}>{line.slice(pos)}</Fragment>);
  return <>{parts}</>;
}

declare const katex:
  | {
      renderToString: (tex: string, opts: object) => string;
    }
  | undefined;

function MathSpan({ tex, display }: { tex: string; display: boolean }) {
  let html = tex;
  if (typeof katex !== "undefined") {
    try {
      html = katex.renderToString(tex, { displayMode: display, throwOnError: false });
    } catch {
      return <span className="render-error">{tex}</span>;
    }
  }
  const Tag = display ? "div" : "span";
  return <Tag dangerouslySetInnerHTML={{ __html: html }} />;
}

function Inlines({ nodes }: { nodes: Inline[] }) {
  return (
    <>
      {nodes.map((n, i) => {
        switch (n.t) {
          case "text":
            return <Fragment key={i}>{n.s}</Fragment>;
          case "break":
            return <Fragment key={i}> </Fragment>;
          case "code":
            return (
              <code className="inline" key={i}>
                {n.s}
              </code>
            );
          case "math":
            return <MathSpan key={i} tex={n.s} display={n.display} />;
          case "emph":
            return (
              <em key={i}>
                <Inlines nodes={n.kids} />
              </em>
            );
          case "bold":
            return (
              <strong key={i}>
                <Inlines nodes={n.kids} />
              </strong>
            );
          case "link":
            return (
              <a key={i} className="doclink">
                <Inlines nodes={n.kids} />
              </a>
            );
        }
      })}
    </>
  );
}

// A code block. Each source line is wrapped in a `.cline` whose textContent
// equals the source line verbatim and whose data-l is its true source line, so
// the hover layer can map cursor → (line, col) for LSP queries. The block's
// range.sl is the source line of its FIRST content line.
function CodeBlock({
  text,
  startLine,
  tokens,
}: {
  text: string;
  startLine: number;
  tokens: Map<number, SemTok[]>;
}) {
  const lines = text.replace(/\n$/, "").split("\n");
  return (
    <pre className="lean">
      {lines.map((line, rel) => {
        // `startLine` (range.sl) is the OPENING FENCE line (1-based); the first
        // content line is the next one. So this content line's 1-based source
        // line is startLine + 1 + rel.
        const srcLine = startLine + 1 + rel;
        // Tokens (and data-l for hovers) use 0-based lines.
        const lineToks = tokens.get(srcLine - 1);
        return (
          <Fragment key={rel}>
            <span className="cline" data-l={srcLine - 1}>
              {colorLine(line, lineToks)}
            </span>
            {rel < lines.length - 1 ? "\n" : null}
          </Fragment>
        );
      })}
    </pre>
  );
}

function BlockView({ block, tokens }: { block: Block; tokens: Map<number, SemTok[]> }) {
  switch (block.kind) {
    case "header": {
      const H = `h${block.level}` as "h1" | "h2" | "h3" | "h4";
      return (
        <H>
          <Inlines nodes={block.kids} />
        </H>
      );
    }
    case "code":
      return <CodeBlock text={block.text} startLine={block.range.sl} tokens={tokens} />;
    case "blockquote":
      return (
        <blockquote>
          {block.kids.map((b, i) => (
            <BlockView key={i} block={b} tokens={tokens} />
          ))}
        </blockquote>
      );
    case "list": {
      const items = block.items.map((blocks, i) => (
        <li key={i}>
          {blocks.map((b, j) => (
            <BlockView key={j} block={b} tokens={tokens} />
          ))}
        </li>
      ));
      return block.ordered ? <ol>{items}</ol> : <ul>{items}</ul>;
    }
    case "para":
      return (
        <p>
          <Inlines nodes={block.kids} />
        </p>
      );
  }
}

export function Preview({
  blocks,
  tokens,
}: {
  blocks: Block[];
  tokens: Map<number, SemTok[]>;
}) {
  return (
    <>
      {blocks.map((b, i) => (
        <BlockView key={i} block={b} tokens={tokens} />
      ))}
    </>
  );
}
