import WikiRAG.Query

/-! # WikiRAG visualization: Graphviz DOT + Mermaid export
Renders subgraphs of the library to DOT (pipe to `dot`/`sfdp`) or Mermaid (inline
in Markdown/IDEs). Two scales: a decl neighborhood and the module graph. -/

namespace WikiRAG
open SQLite

/-- Escape a string for a DOT double-quoted attribute. -/
def dotEscape (s : String) : String := (s.replace "\\" "\\\\").replace "\"" "\\\""

/-- Fill colour by declaration kind. -/
def kindColor : String → String
  | "theorem" => "#cfe8ff"
  | "def" => "#fff2cc"
  | "abbrev" => "#fde9d9"
  | "structure" | "class" | "inductive" | "ctor" => "#d5f5e3"
  | _ => "#eeeeee"

/-- Strip the common library prefixes from a module name for display. -/
def moduleLabel (m : String) : String :=
  ((m.replace "DeepWiki.NetworkCalculus." "").replace "DeepWiki." "").replace "Sources." ""

/-- Graphviz DOT for a decl neighborhood: nodes labelled by short name (full signature in
the tooltip), the focus node highlighted, edges = `uses` among the node set. -/
def neighborhoodDot (root : String) (nodes : Array Hit) (edges : Array (String × String)) : String := Id.run do
  let mut out := "digraph wiki {\n  rankdir=LR;\n  node [shape=box, style=\"rounded,filled\", fontname=\"monospace\", fontsize=10];\n  edge [color=\"#888888\", arrowsize=0.7];\n"
  for h in nodes do
    let color := if h.name == root then "#ffcc66" else kindColor h.kind
    out := out ++ s!"  \"{h.name}\" [label=\"{dotEscape h.short}\", fillcolor=\"{color}\", tooltip=\"{dotEscape h.signature}\"];\n"
  for (a, b) in edges do
    out := out ++ s!"  \"{a}\" -> \"{b}\";\n"
  return out ++ "}\n"

/-- Mermaid `graph` for a decl neighborhood (for inline rendering in Markdown/IDEs). -/
def neighborhoodMermaid (root : String) (nodes : Array Hit) (edges : Array (String × String)) : String := Id.run do
  let names := nodes.map (·.name)
  let idOf (n : String) : String := s!"N{(names.findIdx? (· == n)).getD 0}"
  let mut out := "graph LR\n"
  for h in nodes do
    let cls := if h.name == root then ":::root" else ""
    out := out ++ s!"  {idOf h.name}[\"{h.short}\"]{cls}\n"
  for (a, b) in edges do
    out := out ++ s!"  {idOf a} --> {idOf b}\n"
  return out ++ "  classDef root fill:#ffcc66,stroke:#cc8800;\n"

/-- Graphviz DOT for the module dependency graph; edge thickness grows with √(use count). -/
def moduleDot (nodes : Array String) (edges : Array (String × String × Nat)) : String := Id.run do
  let mut out := "digraph modules {\n  rankdir=LR;\n  node [shape=box, style=filled, fillcolor=\"#eef3fb\", fontname=\"monospace\", fontsize=10];\n  edge [color=\"#9aa7b8\"];\n"
  for m in nodes do
    out := out ++ s!"  \"{m}\" [label=\"{dotEscape (moduleLabel m)}\"];\n"
  for (a, b, w) in edges do
    let pw := 1.0 + Float.sqrt (Float.ofNat w) / 3.0
    out := out ++ s!"  \"{a}\" -> \"{b}\" [penwidth={pw}];\n"
  return out ++ "}\n"

/-- Escape a string for a JS double-quoted literal. -/
def jsEscape (s : String) : String :=
  ((s.replace "\\" "\\\\").replace "\"" "\\\"").replace "\n" " "

/-- Self-contained interactive HTML page (vis-network via CDN) wrapping node/edge JS arrays. -/
def graphHtml (title nodesJS edgesJS : String) : String :=
  "<!DOCTYPE html>\n<html><head><meta charset=\"utf-8\"><title>" ++ title ++ "</title>\n" ++
  "<script src=\"https://unpkg.com/vis-network/standalone/umd/vis-network.min.js\"></script>\n" ++
  "<style>body{margin:0;font-family:monospace}#h{position:fixed;top:8px;left:12px;z-index:1;background:#fffd;padding:4px 8px;border-radius:4px}#net{width:100vw;height:100vh}</style></head>\n" ++
  "<body><div id=\"h\">" ++ title ++ "</div><div id=\"net\"></div>\n<script>\n" ++
  "const nodes=new vis.DataSet([" ++ nodesJS ++ "]);\n" ++
  "const edges=new vis.DataSet([" ++ edgesJS ++ "]);\n" ++
  "new vis.Network(document.getElementById('net'),{nodes,edges}," ++
  "{nodes:{shape:'box',font:{face:'monospace',size:14}},edges:{arrows:'to',color:'#aaa'}," ++
  "physics:{stabilization:true,barnesHut:{springLength:130,gravitationalConstant:-3000}}});\n" ++
  "</script></body></html>\n"

/-- Interactive HTML for a decl neighborhood (node colour by kind, signature on hover). -/
def neighborhoodHtml (root : String) (nodes : Array Hit) (edges : Array (String × String)) : String := Id.run do
  let mut ns := ""
  for h in nodes do
    let color := if h.name == root then "#ffcc66" else kindColor h.kind
    ns := ns ++ "{id:\"" ++ jsEscape h.name ++ "\",label:\"" ++ jsEscape h.short
      ++ "\",title:\"" ++ jsEscape (h.kind ++ "  " ++ h.signature) ++ "\",color:\"" ++ color ++ "\"},"
  let mut es := ""
  for (a, b) in edges do
    es := es ++ "{from:\"" ++ jsEscape a ++ "\",to:\"" ++ jsEscape b ++ "\"},"
  return graphHtml ("uses-graph: " ++ root) ns es

/-- Interactive HTML for the module dependency graph. -/
def moduleHtml (nodes : Array String) (edges : Array (String × String × Nat)) : String := Id.run do
  let mut ns := ""
  for m in nodes do
    ns := ns ++ "{id:\"" ++ jsEscape m ++ "\",label:\"" ++ jsEscape (moduleLabel m) ++ "\",color:\"#aecbf0\"},"
  let mut es := ""
  for (a, b, w) in edges do
    es := es ++ "{from:\"" ++ jsEscape a ++ "\",to:\"" ++ jsEscape b ++ "\",value:" ++ toString w ++ "},"
  return graphHtml "module dependency graph" ns es

/-- Self-contained 3D force-graph page (Three.js via `3d-force-graph`, CDN). -/
def graph3dHtml (title nodesJS linksJS : String) : String :=
  "<!DOCTYPE html>\n<html><head><meta charset=\"utf-8\"><title>" ++ title ++ "</title>\n" ++
  "<script src=\"https://unpkg.com/3d-force-graph\"></script>\n" ++
  "<style>body{margin:0;background:#0b0e14}#h{position:fixed;top:8px;left:12px;z-index:1;color:#9aa7b8;font-family:monospace}#g{width:100vw;height:100vh}</style></head>\n" ++
  "<body><div id=\"h\">" ++ title ++ "</div><div id=\"g\"></div>\n<script>\n" ++
  "const data={nodes:[" ++ nodesJS ++ "],links:[" ++ linksJS ++ "]};\n" ++
  "ForceGraph3D()(document.getElementById('g')).backgroundColor('#0b0e14').graphData(data)" ++
  ".nodeLabel('name').nodeColor('color').nodeVal('val')" ++
  ".linkColor(()=>'#44506a').linkOpacity(0.45).linkDirectionalArrowLength(2.5).linkDirectionalArrowRelPos(1);\n" ++
  "</script></body></html>\n"

/-- Interactive 3D graph for a decl neighborhood (node colour by kind, focus enlarged). -/
def neighborhood3d (root : String) (nodes : Array Hit) (edges : Array (String × String)) : String := Id.run do
  let mut ns := ""
  for h in nodes do
    let color := if h.name == root then "#ffcc66" else kindColor h.kind
    let val := if h.name == root then "10" else "3"
    ns := ns ++ "{id:\"" ++ jsEscape h.name ++ "\",name:\"" ++ jsEscape (h.kind ++ " " ++ h.short ++ " — " ++ h.signature)
      ++ "\",color:\"" ++ color ++ "\",val:" ++ val ++ "},"
  let mut es := ""
  for (a, b) in edges do
    es := es ++ "{source:\"" ++ jsEscape a ++ "\",target:\"" ++ jsEscape b ++ "\"},"
  return graph3dHtml ("uses-graph 3D: " ++ root) ns es

/-- Interactive 3D graph for the module dependency graph. -/
def module3d (nodes : Array String) (edges : Array (String × String × Nat)) : String := Id.run do
  let mut ns := ""
  for m in nodes do
    ns := ns ++ "{id:\"" ++ jsEscape m ++ "\",name:\"" ++ jsEscape (moduleLabel m) ++ "\",color:\"#7fb0ff\",val:3},"
  let mut es := ""
  for (a, b, w) in edges do
    es := es ++ "{source:\"" ++ jsEscape a ++ "\",target:\"" ++ jsEscape b ++ "\",value:" ++ toString w ++ "},"
  return graph3dHtml "module dependency graph 3D" ns es

end WikiRAG
