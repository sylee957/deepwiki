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
paint. The saved choice is one of `'light'`, `'dark'`, or `'system'` (default
when nothing is saved). In `'system'` mode the effective theme follows the OS
`prefers-color-scheme`. We set `data-theme="dark"` on `<html>` exactly when the
effective theme is dark, so the inversion CSS keys on a single attribute. -/
def themeInitScript : String :=
  "(function(){try{" ++
    "var s=localStorage.getItem('deepwiki-theme')||'system';" ++
    "var sysDark=matchMedia('(prefers-color-scheme: dark)').matches;" ++
    "var d=s==='dark'||(s==='system'&&sysDark);" ++
    "if(d)document.documentElement.setAttribute('data-theme','dark');" ++
  "}catch(e){}})();"

/-- Dark theme: a VS Code "Dark High Contrast"–style neon palette, keyed on
`html[data-theme="dark"]`. We theme Verso's colour variables directly so the
Lean syntax highlighting gets a deliberate magenta-keyword / cyan-identifier /
gold-binder palette on a near-black background, with cyan neon accents and
glows on headings, links, the ToC, the header rule, and code-block borders. On
the near-black background any element not explicitly themed stays dark rather
than glaring, so coverage gaps are benign. -/
def darkModeCss : String :=
  -- Verso colour variables
  "html[data-theme=\"dark\"]{" ++
    "--verso-text-color:#e6f1ff;" ++
    "--verso-code-color:#d4d4d4;" ++
    "--verso-structure-color:#e6f1ff;" ++
    "--verso-selected-color:#163a5f;" ++
    "--verso-info-color:#9cdcfe;" ++
    "--verso-warning-color:#dcdcaa;" ++
    "--verso-error-color:#ff5f87;" ++
    "--verso-toc-background-color:#000;" ++
    "--verso-toc-text-color:#c8d3e0;" ++
    "--verso-burger-toc-hidden-color:#4ec9ff;" ++
    "--verso-burger-toc-hidden-shadow-color:#000;" ++
    "--verso-burger-toc-visible-shadow-color:#000;" ++
    "--verso-code-keyword-color:#ff7ad9;" ++
    "--verso-code-const-color:#4ec9ff;" ++
    "--verso-code-var-color:#dcdcaa;" ++
  "}" ++
  "html[data-theme=\"dark\"] body," ++
  "html[data-theme=\"dark\"] main{" ++
    "background:#08080c;color:#e6f1ff;}" ++
  "html[data-theme=\"dark\"] .header{" ++
    "background:#000;box-shadow:0 1px 0 #4ec9ff,0 2px 12px #4ec9ff55;}" ++
  "html[data-theme=\"dark\"] .header-title{" ++
    "color:#4ec9ff;text-shadow:0 0 8px #4ec9ff88;}" ++
  "html[data-theme=\"dark\"] .toc-bottom-link{color:#4ec9ff;}" ++
  "html[data-theme=\"dark\"] #toc{" ++
    "background:#000;border-right:1px solid #4ec9ff33;}" ++
  "html[data-theme=\"dark\"] #toc a{color:#c8d3e0;}" ++
  "html[data-theme=\"dark\"] #toc a:hover{" ++
    "color:#4ec9ff;text-shadow:0 0 6px #4ec9ff99;}" ++
  "html[data-theme=\"dark\"] #toc .split-toc " ++
    "label.toggle-split-toc::before{background-color:#4ec9ff;}" ++
  "html[data-theme=\"dark\"] h1," ++
  "html[data-theme=\"dark\"] h2," ++
  "html[data-theme=\"dark\"] h3{" ++
    "color:#e6f1ff;text-shadow:0 0 10px #4ec9ff44;}" ++
  "html[data-theme=\"dark\"] main a{color:#4ec9ff;}" ++
  "html[data-theme=\"dark\"] main a:hover{" ++
    "text-shadow:0 0 6px #4ec9ff99;}" ++
  "html[data-theme=\"dark\"] .hl.lean.block," ++
  "html[data-theme=\"dark\"] pre," ++
  "html[data-theme=\"dark\"] code{" ++
    "background:#000;color:#d4d4d4;" ++
    "border:1px solid #4ec9ff44;border-radius:6px;" ++
    "box-shadow:0 0 14px #4ec9ff22;}" ++
  "html[data-theme=\"dark\"] .hl.lean .keyword.token{" ++
    "color:#ff7ad9;text-shadow:0 0 6px #ff7ad955;}" ++
  "html[data-theme=\"dark\"] .hl.lean .unknown.token{color:#9cdcfe;}" ++
  "html[data-theme=\"dark\"] .tippy-box{" ++
    "background:#0d0d12;color:#d4d4d4;border:1px solid #4ec9ff55;}" ++
  "#deepwiki-theme-toggle{position:fixed;right:1rem;bottom:1rem;" ++
    "z-index:1000;width:2.6rem;height:2.6rem;border-radius:50%;" ++
    "border:1px solid #8888;background:#fff;color:#222;cursor:pointer;" ++
    "font-size:1.2rem;line-height:1;box-shadow:0 1px 5px #0003;}" ++
  "html[data-theme=\"dark\"] #deepwiki-theme-toggle{" ++
    "background:#0d0d12;color:#4ec9ff;border-color:#4ec9ff;" ++
    "box-shadow:0 0 10px #4ec9ff66;}"

/-- The toggle button cycles the saved choice `system → light → dark → system`,
persists it, re-applies the effective theme (consulting the OS in `'system'`
mode), and swaps the glyph to show the _current selection_ (🖥/☀/☾). A live
`matchMedia` listener keeps the page in sync with the OS while in `'system'`
mode. -/
def themeToggleScript : String :=
  "(function(){" ++
  "var mq=matchMedia('(prefers-color-scheme: dark)');" ++
  "function pref(){return localStorage.getItem('deepwiki-theme')||'system';}" ++
  "function apply(){" ++
    "var p=pref();" ++
    "var dark=p==='dark'||(p==='system'&&mq.matches);" ++
    "if(dark)document.documentElement.setAttribute('data-theme','dark');" ++
    "else document.documentElement.removeAttribute('data-theme');}" ++
  "function glyph(){var p=pref();" ++
    "return p==='system'?'🖥':p==='dark'?'☾':'☀';}" ++
  "function init(){var b=document.createElement('button');" ++
    "b.id='deepwiki-theme-toggle';" ++
    "b.setAttribute('aria-label','Theme: system / light / dark');" ++
    "function refresh(){b.textContent=glyph();" ++
      "b.title='Theme: '+pref();}" ++
    "refresh();" ++
    "b.addEventListener('click',function(){" ++
      "var p=pref();" ++
      "var next=p==='system'?'light':p==='light'?'dark':'system';" ++
      "localStorage.setItem('deepwiki-theme',next);" ++
      "apply();refresh();});" ++
    "mq.addEventListener('change',function(){apply();refresh();});" ++
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
