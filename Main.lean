import VersoManual
import Book

open Verso.Genre Manual
open Verso.Output (Html)
open Verso.Output.Html

/-!
Render entry point plus SEO configuration for GitHub Pages.

The book is deployed at `https://sylee957.github.io/deepwiki/`. Verso's page
template fixes `<title>` and emits a `<base href="./">`, so per-page titles and
canonical tags aren't reachable from here; what *is* reachable is site-wide
`<head>` metadata (`extraHead`) and arbitrary output files (via an `extraStep`,
which can also walk the rendered tree to build a sitemap).
-/

/-- Canonical deployment root, with trailing slash. -/
def siteURL : String := "https://sylee957.github.io/deepwiki/"

/-- One-line site description reused across `<meta>` and Open Graph tags. -/
def siteDescription : String :=
  "DeepWiki — an AI-generated wiki of autoformalized mathematics in Lean 4 " ++
  "and Mathlib. First entry: the (min,plus) dioid algebra behind " ++
  "deterministic network calculus."

/-- Site-wide `<head>` elements: description, author, and social-card metadata.
These are identical on every page (Verso applies `extraHead` globally). -/
def extraHead : Array Html := #[
  {{ <meta name="description" content={{siteDescription}} /> }},
  {{ <meta name="author" content="Sangyub Lee" /> }},
  {{ <meta name="theme-color" content="#ffffff" /> }},
  -- Open Graph (used by Slack/Discord/Facebook link previews)
  {{ <meta property="og:type" content="website" /> }},
  {{ <meta property="og:site_name" content="DeepWiki" /> }},
  {{ <meta property="og:title" content="DeepWiki" /> }},
  {{ <meta property="og:description" content={{siteDescription}} /> }},
  {{ <meta property="og:url" content={{siteURL}} /> }},
  -- Twitter card
  {{ <meta name="twitter:card" content="summary" /> }},
  {{ <meta name="twitter:title" content="DeepWiki" /> }},
  {{ <meta name="twitter:description" content={{siteDescription}} /> }}
]

/-- robots.txt: allow everything, point crawlers at the sitemap. -/
def robotsTxt : String :=
  "User-agent: *\nAllow: /\nSitemap: " ++ siteURL ++ "sitemap.xml\n"

/-- Collect every `index.html` under `root` and return its directory path
relative to `root` (the URL path segment), `""` for the root page itself. -/
partial def pageDirs (root : System.FilePath) : IO (Array String) := do
  let rec go (rel : System.FilePath) (acc : Array String) : IO (Array String) := do
    let dir := root.join rel
    let mut acc := acc
    if (← (dir.join "index.html").pathExists) then
      acc := acc.push (rel.toString)
    for entry in (← dir.readDir) do
      if (← entry.path.isDir) then
        let childRel := if rel.toString == "." then
            (entry.fileName : System.FilePath)
          else rel.join entry.fileName
        acc ← go childRel acc
    return acc
  go (System.FilePath.mk ".") #[]

/-- Render a `<url>` entry. `seg` is `"."` for the root or a relative dir. -/
def sitemapEntry (seg : String) : String :=
  let loc :=
    if seg == "." then siteURL
    else siteURL ++ seg.replace "\\" "/" ++ "/"
  "  <url><loc>" ++ loc ++ "</loc></url>\n"

/-- After rendering, write robots.txt and a sitemap into `html-multi/`.
Runs only for multi-page HTML output; single-page/TeX runs are skipped. -/
def seoFiles : ExtraStep := fun mode _log config _state _text => do
  match mode with
  | .multi =>
    let root := config.destination.join "html-multi"
    IO.FS.writeFile (root.join "robots.txt") robotsTxt
    let dirs := (← pageDirs root).qsort (· < ·)
    let body := String.join (dirs.map sitemapEntry).toList
    let sitemap :=
      "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" ++
      "<urlset xmlns=\"http://www.sitemaps.org/schemas/sitemap/0.9\">\n" ++
      body ++ "</urlset>\n"
    IO.FS.writeFile (root.join "sitemap.xml") sitemap
  | .single => pure ()

/-- Entry point for rendering the book to HTML: `lake exe generate-book`. -/
def main : List String → IO UInt32 :=
  manualMain (%doc Book) (config := { extraHead }) (extraSteps := [seoFiles])
