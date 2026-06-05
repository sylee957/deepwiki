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

/-- Anti-flash theme bootstrap: runs synchronously in `<head>`, before first
paint, setting `data-theme` on `<html>` from a saved choice or the OS
preference. Without this the page would flash light before the toggle script
runs. -/
def themeInitScript : String :=
  "(function(){try{" ++
    "var s=localStorage.getItem('deepwiki-theme');" ++
    "var d=s?s==='dark':matchMedia('(prefers-color-scheme: dark)').matches;" ++
    "if(d)document.documentElement.setAttribute('data-theme','dark');" ++
  "}catch(e){}})();"

/-- Dark-theme CSS via whole-page colour inversion. Rather than re-theming
each of Verso's many colours individually (variables, hardcoded rules, code
highlighting, KaTeX), we invert the entire document and rotate the hue back so
blues stay blue — the classic robust dark mode. KaTeX math renders as HTML
here (no images/SVG), so it inverts cleanly along with the text; there is no
media to counter-invert. The toggle button is inverted a second time so it
keeps its own colours. -/
def darkModeCss : String :=
  "html[data-theme=\"dark\"]{" ++
    "background:#fff;" ++
    "filter:invert(1) hue-rotate(180deg);" ++
  "}" ++
  -- code-block panels read better with a touch less contrast once inverted
  "html[data-theme=\"dark\"] .hl.lean.block{" ++
    "background:#f2f2f2;}" ++
  -- the floating toggle button: invert again to cancel the page inversion
  "#deepwiki-theme-toggle{position:fixed;right:1rem;bottom:1rem;" ++
    "z-index:1000;width:2.6rem;height:2.6rem;border-radius:50%;" ++
    "border:1px solid #8888;background:#fff;color:#222;cursor:pointer;" ++
    "font-size:1.2rem;line-height:1;box-shadow:0 1px 5px #0003;}" ++
  "html[data-theme=\"dark\"] #deepwiki-theme-toggle{" ++
    "filter:invert(1) hue-rotate(180deg);}"

/-- The toggle button's behaviour: flip `data-theme` on `<html>`, persist the
choice, and swap the glyph. Wired up on `DOMContentLoaded`. -/
def themeToggleScript : String :=
  "(function(){function setGlyph(b){" ++
    "b.textContent=document.documentElement.getAttribute('data-theme')" ++
    "==='dark'?'☀':'☾';}" ++
  "function init(){var b=document.createElement('button');" ++
    "b.id='deepwiki-theme-toggle';" ++
    "b.setAttribute('aria-label','Toggle dark mode');" ++
    "setGlyph(b);" ++
    "b.addEventListener('click',function(){" ++
      "var dark=document.documentElement.getAttribute('data-theme')==='dark';" ++
      "if(dark){document.documentElement.removeAttribute('data-theme');" ++
        "localStorage.setItem('deepwiki-theme','light');}" ++
      "else{document.documentElement.setAttribute('data-theme','dark');" ++
        "localStorage.setItem('deepwiki-theme','dark');}" ++
      "setGlyph(b);});" ++
    "document.body.appendChild(b);}" ++
  "if(document.readyState!=='loading')init();" ++
  "else document.addEventListener('DOMContentLoaded',init);})();"

/-- Site-wide `<head>` elements: description, author, social-card metadata, and
the dark-mode theme (anti-flash bootstrap, CSS, and toggle script). These are
identical on every page (Verso applies `extraHead` globally). -/
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
  {{ <meta name="twitter:description" content={{siteDescription}} /> }},
  -- Dark mode: bootstrap (anti-flash) + theme CSS + toggle wiring
  {{ <script>{{Html.text false themeInitScript}}</script> }},
  {{ <style>{{Html.text false darkModeCss}}</style> }},
  {{ <script>{{Html.text false themeToggleScript}}</script> }}
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
