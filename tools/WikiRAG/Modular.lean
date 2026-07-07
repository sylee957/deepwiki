import WikiRAG.Query
import WikiRAG.Cochange
import Std.Data.HashMap

/-! # Modularity analytics over the `uses` graph

Turns the exact `uses` dependency graph into **quantified, ranked** refactoring signals — a
decision-support engine (it scores and ranks; the agent validates). Every signal is a *continuous
score*, never a hard threshold: modules/decls/pairs are ranked and the top ones shown. The only knobs
are `--top=N` and `--prefix=NS`.

Signals: **split** (internal Newman modularity `Q`), **misplacement** (`uses`-affinity to another
module), **coupling** (size-normalised cross-directory), **directory granularity**, **conceptual
cohesion** (docstring-embedding), the **multi-objective regroup** — a Pareto view over
`(structural, conceptual, evolutionary, disturbance)`, no weighting — and the **community
partition-diff**: the global `uses`-community structure diffed against the directory tree, surfacing
*scattered themes* (one community spread over many directories → regroup) and *grab-bag directories*
(one directory fractured into many communities → split). The local signals answer "does this decl/file
belong here?"; the partition-diff answers "what modules *should* exist?" — the module-scale question. -/

namespace WikiRAG
open Std SQLite SQLite.Blob

/-! ### Small numeric + graph helpers -/

/-- The namespace directory of a module = its path minus the last component. -/
def directory (m : String) : String :=
  let parts := m.splitOn "."
  if parts.length ≤ 1 then m else ".".intercalate parts.dropLast

/-- Last path component of a dotted module name. -/
@[inline] def leaf (m : String) : String := m.splitOn "." |>.getLastD m

@[inline] def bump (m : HashMap String Nat) (k : String) : HashMap String Nat :=
  m.insert k ((m.getD k 0) + 1)

/-- Percent (0–100) of a [0,1] score, for display. -/
@[inline] def pct (x : Float) : Int := (x * 100.0).round.toUInt64.toNat

/-- Signed percent, for objectives that can be negative (e.g. conceptual disagreement). -/
@[inline] def pctS (x : Float) : Int :=
  let n : Int := (x.abs * 100.0).round.toUInt64.toNat
  if x < 0.0 then -n else n

/-- Unordered key `"a||b"` (lexicographically sorted) for a module pair. -/
@[inline] def pairKey (a b : String) : String := if a < b then s!"{a}||{b}" else s!"{b}||{a}"

/-- Componentwise sum of two equal-length vectors (for embedding centroids). -/
def vadd (a b : Array Float) : Array Float :=
  if a.size == b.size then (Array.range a.size).map (fun i => a[i]! + b[i]!) else b

/-- Label propagation on an undirected subgraph, returning each node's community label. -/
def labelProp (nodes : Array String) (adj : HashMap String (Array String)) :
    HashMap String Nat := Id.run do
  let mut label : HashMap String Nat := {}
  let mut i := 0
  for n in nodes do label := label.insert n i; i := i + 1
  for _ in [0:6] do
    let mut changed := false
    for n in nodes do
      let nbrs := adj.getD n #[]
      if nbrs.isEmpty then continue
      let mut cnt : HashMap Nat Nat := {}
      for x in nbrs do
        let l := label.getD x 0
        cnt := cnt.insert l ((cnt.getD l 0) + 1)
      let mut best := label.getD n 0; let mut bestC := 0
      for (l, c) in cnt.toArray do if c > bestC then best := l; bestC := c
      if label.getD n 0 != best then label := label.insert n best; changed := true
    if !changed then break
  return label

/-- **Newman modularity `Q`** of the label-propagation partition of an undirected subgraph.
High `Q` ⇒ genuine sub-community structure (a candidate to split); a flat bag scores ~0. Returns
`(Q, #communities)`. -/
def modularityQ (nodes : Array String) (adj : HashMap String (Array String)) : Float × Nat := Id.run do
  let label := labelProp nodes adj
  let mut twoE := 0
  for n in nodes do twoE := twoE + (adj.getD n #[]).size
  if twoE == 0 then return (0.0, 0)
  let E2 := twoE.toFloat
  let mut ec : HashMap Nat Nat := {}    -- 2 · (edges inside community)
  let mut degc : HashMap Nat Nat := {}
  for n in nodes do
    let ln := label.getD n 0
    let nbrs := adj.getD n #[]
    degc := degc.insert ln ((degc.getD ln 0) + nbrs.size)
    for x in nbrs do
      if label.getD x 0 == ln then ec := ec.insert ln ((ec.getD ln 0) + 1)
  let mut q := 0.0
  for (c, e) in ec.toArray do
    let a := (degc.getD c 0).toFloat / E2
    q := q + e.toFloat / E2 - a * a
  return (q, ec.toArray.size)

/-! ### The loaded graph (built once, shared by every analysis) -/

/-- The `uses` graph restricted to a prefix, plus cohesion accumulators and co-change weights —
everything the analyses read, loaded once. -/
structure Graph where
  d2m : HashMap String String              -- decl → module
  short : HashMap String String            -- decl → short name
  sizeM : HashMap String Nat               -- module → #decls
  members : HashMap String (Array String)  -- module → its decl names
  adj : HashMap String (Array String)      -- undirected `uses` adjacency
  intraM : HashMap String Nat              -- module → intra-module edges
  extM : HashMap String Nat                -- module → inter-module edge endpoints
  intraD : HashMap String Nat              -- directory → intra-directory edges
  extD : HashMap String Nat                -- directory → inter-directory edge endpoints
  pairX : HashMap String Nat               -- module-pair (a<b) → cross edges
  cc : HashMap String Nat                  -- module-pair (a<b) → co-change count
  ccMax : Float                            -- max co-change weight, for normalisation

/-- Module cohesion `C(m) = intra / (intra + inter)` ∈ [0,1]. -/
def Graph.cohesion (g : Graph) (m : String) : Float :=
  let i := g.intraM.getD m 0; let e := g.extM.getD m 0
  if i + e == 0 then 1.0 else i.toFloat / (i + e).toFloat

/-- Directory cohesion `intra / (intra + inter)` ∈ [0,1]. -/
def Graph.dirCohesion (g : Graph) (d : String) : Float :=
  let i := g.intraD.getD d 0; let e := g.extD.getD d 0
  if i + e == 0 then 1.0 else i.toFloat / (i + e).toFloat

/-- Evolutionary pull: normalised co-change weight of two modules. -/
def Graph.evoPull (g : Graph) (x y : String) : Float :=
  (g.cc.getD (pairKey x y) 0).toFloat / g.ccMax

/-- Load the graph restricted to modules under `pfx`. -/
def loadGraph (db : SQLite) (pfx : String) : IO Graph := do
  let cc ← loadCochange db
  let ccMax := (cc.toArray.foldl (fun m (kw : String × Nat) => Nat.max m kw.2) 1).toFloat
  let decls ← allDecls db
  let mut d2m : HashMap String String := {}
  let mut short : HashMap String String := {}
  let mut sizeM : HashMap String Nat := {}
  let mut members : HashMap String (Array String) := {}
  for h in decls do
    if h.module.startsWith pfx then
      d2m := d2m.insert h.name h.module
      short := short.insert h.name h.short
      sizeM := bump sizeM h.module
      members := members.insert h.module ((members.getD h.module #[]).push h.name)
  let edges := (← allEdges db).filter (fun (a, b) => a != b && d2m.contains a && d2m.contains b)
  let mut adj : HashMap String (Array String) := {}
  let mut intraM : HashMap String Nat := {}; let mut extM : HashMap String Nat := {}
  let mut intraD : HashMap String Nat := {}; let mut extD : HashMap String Nat := {}
  let mut pairX : HashMap String Nat := {}
  for (a, b) in edges do
    adj := adj.insert a ((adj.getD a #[]).push b)
    adj := adj.insert b ((adj.getD b #[]).push a)
    let ma := d2m.getD a ""; let mb := d2m.getD b ""
    if ma == mb then intraM := bump intraM ma
    else
      extM := bump extM ma; extM := bump extM mb
      pairX := bump pairX (pairKey ma mb)
    let da := directory ma; let dbb := directory mb
    if da == dbb then intraD := bump intraD da else extD := bump extD da; extD := bump extD dbb
  return { d2m, short, sizeM, members, adj, intraM, extM, intraD, extD, pairX, cc, ccMax }

/-! ### Structural analyses -/

/-- SPLIT: rank modules by internal Newman modularity `Q` (genuine sub-community structure). -/
def reportSplit (g : Graph) (top : Nat) : IO Unit := do
  let mut rows : Array (String × Float × Float × Nat × Nat) := #[]
  for (m, sz) in g.sizeM.toArray do
    let members := g.members.getD m #[]
    let memberSet := HashSet.ofArray members
    let mut subAdj : HashMap String (Array String) := {}
    for n in members do subAdj := subAdj.insert n ((g.adj.getD n #[]).filter memberSet.contains)
    let (q, ncomm) := modularityQ members subAdj
    rows := rows.push (m, q, g.cohesion m, ncomm, sz)
  IO.println "\n== SPLIT (score = internal modularity Q; #communities = the split axis) =="
  for (m, q, c, ncomm, sz) in (rows.qsort (fun a b => a.2.1 > b.2.1)).toList.take top do
    IO.println s!"  Q={pct q}  {m}  size={sz} cohesion={pct c}% communities={ncomm}"

/-- MISPLACED: rank decls by structural pull toward another module `(bestOther − home)·(1−1/deg)`. -/
def reportMisplaced (g : Graph) (top : Nat) : IO Unit := do
  let mut rows : Array (String × Float × String × String × Nat) := #[]
  for (n, nbrs) in g.adj.toArray do
    let deg := nbrs.size
    if deg == 0 then continue
    let home := g.d2m.getD n ""
    let mut byMod : HashMap String Nat := {}
    for x in nbrs do byMod := bump byMod (g.d2m.getD x "")
    let mut alt := home; let mut cnt := 0
    for (mm, c) in byMod.toArray do if mm != home && c > cnt then alt := mm; cnt := c
    if alt == home then continue
    let score := (cnt.toFloat / deg.toFloat - (byMod.getD home 0).toFloat / deg.toFloat)
      * (1.0 - 1.0 / deg.toFloat)
    rows := rows.push (g.short.getD n n, score, home, alt, deg)
  IO.println "\n== MISPLACED (score = (bestOtherAffinity − homeAffinity)·(1−1/deg)) =="
  for (s, sc, home, alt, deg) in (rows.qsort (fun a b => a.2.1 > b.2.1)).toList.take top do
    IO.println s!"  {pct sc}  {s}  [{leaf home}]→[{leaf alt}] deg={deg}"

/-- COUPLING: rank cross-directory module pairs by `cross / √(size₁·size₂)`. -/
def reportCoupling (g : Graph) (top : Nat) : IO Unit := do
  let mut rows : Array (String × String × Float × Nat) := #[]
  for (k, w) in g.pairX.toArray do
    let ps := k.splitOn "||"; let m1 := ps.getD 0 ""; let m2 := ps.getD 1 ""
    if directory m1 != directory m2 then
      let denom := Float.sqrt ((g.sizeM.getD m1 1) * (g.sizeM.getD m2 1)).toFloat
      rows := rows.push (m1, m2, w.toFloat / denom, w)
  IO.println "\n== COUPLING (score = cross / √(size₁·size₂); cross-directory) =="
  for (m1, m2, sc, w) in (rows.qsort (fun a b => a.2.2.1 > b.2.2.1)).toList.take top do
    IO.println s!"  {pct sc}  ({w} edges)  {m1}  ⇄  {m2}"

/-- DIRECTORY granularity: cohesion + module-size distribution per directory (numbers, no flags). -/
def reportDirectory (g : Graph) (top : Nat) : IO Unit := do
  let mut dirMods : HashMap String (Array Nat) := {}
  for (m, sz) in g.sizeM.toArray do
    dirMods := dirMods.insert (directory m) ((dirMods.getD (directory m) #[]).push sz)
  IO.println "\n== DIRECTORY granularity (cohesion, module count, mean size — no thresholds) =="
  let rows := dirMods.toArray.map (fun (d, ss) =>
    let n := ss.size
    let avg := if n == 0 then 0 else (ss.foldl (·+·) 0) / n
    (d, g.dirCohesion d, n, avg, ss.foldl Nat.max 0))
  for (d, c, n, avg, mx) in (rows.qsort (fun a b => a.2.1 < b.2.1)).toList.take top do
    IO.println s!"  cohesion={pct c}%  modules={n} mean={avg} max={mx}  {d}"

/-! ### Conceptual (NL) layer — over the Ollama docstring embeddings -/

/-- Loaded docstring embeddings under a prefix, with per-module centroids and member vectors. -/
structure Embeds where
  rows : Array (String × String × Array Float)          -- (decl, module, vector)
  sums : HashMap String (Array Float)                   -- module → centroid (unnormalised sum)
  modVecs : HashMap String (Array (Array Float))         -- module → its decls' vectors

/-- Load the embeddings under `pfx`; `none` if the graph has not been indexed. -/
def loadEmbeds (db : SQLite) (pfx : String) : IO (Option Embeds) := do
  let s ← db.prepare s!"SELECT name, module, embedding FROM decls WHERE embedding IS NOT NULL AND module LIKE '{pfx}%'"
  let mut rows : Array (String × String × Array Float) := #[]
  while (← s.step) do
    match (fromBinary (← s.columnBlob 2) : Except String (Array Float)) with
    | .ok v => rows := rows.push (← s.columnText 0, ← s.columnText 1, v)
    | .error _ => pure ()
  if rows.isEmpty then return none
  let mut sums : HashMap String (Array Float) := {}
  let mut modVecs : HashMap String (Array (Array Float)) := {}
  for (_, md, v) in rows do
    sums := sums.insert md (vadd (sums.getD md #[]) v)
    modVecs := modVecs.insert md ((modVecs.getD md #[]).push v)
  return some { rows, sums, modVecs }

/-- CONCEPTUAL cohesion: rank modules by mean docstring-cosine of their decls to the module centroid. -/
def reportConceptual (e : Embeds) (top : Nat) : IO Unit := do
  let mut chS : HashMap String Float := {}; let mut chN : HashMap String Nat := {}
  for (_, md, v) in e.rows do
    chS := chS.insert md ((chS.getD md 0.0) + cosine v (e.sums.getD md #[])); chN := bump chN md
  IO.println s!"\n== CONCEPTUAL cohesion (mean docstring-cosine of a module's decls; {e.rows.size} embedded) =="
  let rows := e.sums.toArray.map (fun (md, _) => (md, (chS.getD md 0.0) / (chN.getD md 1).toFloat))
  for (md, sc) in (rows.qsort (fun a b => a.2 < b.2)).toList.take top do
    IO.println s!"  {pct sc}  {md}"

/-! ### Multi-objective regroup (NSGA-style Pareto, no weighting) -/

/-- A regroup candidate `home → alt` with its multi-objective vector (maximise `str`/`con`/`evo`,
minimise `dis`). -/
structure Regroup where
  short : String
  home : String
  alt : String
  str : Float    -- structural pull (dependency affinity toward `alt`)
  con : Float    -- conceptual agreement (docstring cosine: alt − home)
  evo : Float    -- evolutionary pull (co-change of home & alt)
  dis : Float    -- disturbance (bond to nearest home sibling) — a cost

/-- `c` is Pareto-dominated by `d` on `(str↑, con↑, evo↑, dis↓)`. -/
def Regroup.dominatedBy (c d : Regroup) : Bool :=
  d.str ≥ c.str && d.con ≥ c.con && d.evo ≥ c.evo && d.dis ≤ c.dis &&
    (d.str > c.str || d.con > c.con || d.evo > c.evo || d.dis < c.dis)

/-- MULTI-OBJECTIVE regroup: each move-candidate carries `(str, con, evo, dis)`; keep the Pareto
non-dominated set. The LLM judge picks — a high `dis` means the move would split a bonded pair (the
`mul_left`/`mul_right` guard), made visible rather than hidden in a weighted sum. -/
def reportRegroup (g : Graph) (e : Embeds) (top : Nat) : IO Unit := do
  let mut cand : Array Regroup := #[]
  for (nm, home, v) in e.rows do
    let nbrs := g.adj.getD nm #[]
    let deg := nbrs.size
    if deg == 0 then continue
    let mut byMod : HashMap String Nat := {}
    for x in nbrs do byMod := bump byMod (g.d2m.getD x "")
    let mut alt := home; let mut cnt := 0
    for (mm, c) in byMod.toArray do if mm != home && c > cnt then alt := mm; cnt := c
    if alt == home then continue
    let mut dis := 0.0
    for sv in e.modVecs.getD home #[] do
      let s := cosine v sv
      if s < 0.999 && s > dis then dis := s   -- nearest home sibling (excluding self ≈ 1)
    cand := cand.push
      { short := g.short.getD nm nm, home, alt
        str := (cnt.toFloat / deg.toFloat - (byMod.getD home 0).toFloat / deg.toFloat)
          * (1.0 - 1.0 / deg.toFloat)
        con := cosine v (e.sums.getD alt #[]) - cosine v (e.sums.getD home #[])
        evo := g.evoPull home alt
        dis }
  let front := cand.filter (fun c => !cand.any c.dominatedBy)
  IO.println s!"\n== MULTI-OBJECTIVE regroup — Pareto front {front.size}/{cand.size} (str=structural, con=conceptual, evo=co-change, dis=disturbance; high dis = splits a bonded pair) =="
  for c in (front.qsort (fun a b => a.str > b.str)).toList.take top do
    IO.println s!"  str={pctS c.str} con={pctS c.con} evo={pct c.evo} dis={pct c.dis}  {c.short}  [{leaf c.home}]→[{leaf c.alt}]"

/-! ### Community partition-diff (global clustering vs. the directory tree)

The local reports above all ask "does *this* decl/file belong where it sits?". This one asks the
module-scale question: cluster the **whole** in-scope `uses` graph (label propagation, ignoring
module/directory boundaries), then **diff the clustering against the directory tree**. A community
spanning many directories is a theme the current layout scattered; a directory holding many
communities is a grab-bag. These are the *reorganization projects* — whole clusters to regroup or
split — that no per-file patrol surfaces. -/

/-- A scattered-theme community: one `uses`-community whose decls live in ≥2 directories. -/
structure Community where
  size : Nat            -- #decls in the community
  mods : Nat            -- #distinct modules it touches
  dirs : Nat            -- #distinct directories it spans (≥2 ⇒ scattered)
  coh : Float           -- fraction of the community's edge endpoints staying inside it
  con : Float           -- conceptual cohesion (mean docstring-cosine to centroid); <0 = not embedded
  score : Float         -- (dirs−1)·coh·concept·module-scale-prior — a *liftable* scattered theme
                        --   ranks first; the graph backbone (a mega-community) is scored ~0
  dirList : Array String
  sample : Array String -- a few member short names, to name the theme

/-- A fractured directory: one directory whose decls fall into several `uses`-communities. -/
structure DirFracture where
  dir : String
  total : Nat           -- #decls in the directory
  comms : Nat           -- #communities they scatter into
  purity : Float        -- largest community's share of the directory (low ⇒ grab-bag)

/-- Compiler-generated declarations (recursors, `noConfusion`, projections, match/proof helpers) that
carry no design intent — excluded so they don't form spurious "themes". -/
def isStructuralNoise (short : String) : Bool :=
  #["casesOn", "noConfusion", "noConfusionType", "rec", "recAux", "below", "brecOn", "binductionOn",
    "ndrec", "mk", "injEq", "toCtorIdx", "ofNat", "sizeOf"].contains short
  || short.startsWith "match_" || short.startsWith "proof_" || short.startsWith "eq_"

/-- COMMUNITIES + FRACTURE: cluster the whole in-scope graph and diff it against the directory tree —
scattered themes to regroup and grab-bag directories to split. -/
def reportCommunities (g : Graph) (eOpt : Option Embeds) (top : Nat) : IO Unit := do
  let nodes := g.d2m.toArray.filterMap fun (n, _) =>
    if isStructuralNoise (g.short.getD n n) then none else some n
  if nodes.isEmpty then return
  let label := labelProp nodes g.adj
  let vmap : HashMap String (Array Float) :=
    match eOpt with
    | none => {}
    | some e => e.rows.foldl (fun m r => m.insert r.1 r.2.2) {}
  -- community → members
  let mut mem : HashMap Nat (Array String) := {}
  for n in nodes do
    let c := label.getD n 0
    mem := mem.insert c ((mem.getD c #[]).push n)
  -- module-scale prior: peaks at the mean module size τ, so a *liftable* module-sized theme
  -- outscores the graph backbone (a mega-community, size ≫ τ, decays to ~0) — data-driven, no cutoff.
  let tau := nodes.size.toFloat / (Nat.max 1 g.sizeM.size).toFloat
  -- scattered-theme communities (span ≥2 directories)
  let mut rows : Array Community := #[]
  for (c, members) in mem.toArray do
    if members.size < 3 then continue
    let modsArr := members.map (fun n => g.d2m.getD n "")
    let dirSet := HashSet.ofArray (modsArr.map directory)
    if dirSet.size < 2 then continue
    let mut intra := 0; let mut inter := 0
    for n in members do
      for x in g.adj.getD n #[] do
        if label.getD x 0 == c then intra := intra + 1 else inter := inter + 1
    let coh := if intra + inter == 0 then 0.0 else intra.toFloat / (intra + inter).toFloat
    let con : Float := Id.run do
      if vmap.isEmpty then return -1.0
      let mut cen : Array Float := #[]; let mut k := 0
      for n in members do
        match vmap.get? n with
        | some v => cen := vadd cen v; k := k + 1
        | none => pure ()
      if k == 0 then return -1.0
      let mut s := 0.0
      for n in members do
        match vmap.get? n with
        | some v => s := s + cosine v cen
        | none => pure ()
      return s / k.toFloat
    let conW := if con < 0.0 then 1.0 else con
    let sz := members.size.toFloat
    let sizePrior := sz * Float.exp (-sz / tau)   -- peaks at τ; ~0 for the backbone
    let score := (dirSet.size - 1).toFloat * coh * conW * sizePrior
    let sample := ((members.qsort (· < ·)).toList.take 4).map (fun n => g.short.getD n n) |>.toArray
    rows := rows.push
      { size := members.size, mods := (HashSet.ofArray modsArr).size, dirs := dirSet.size,
        coh, con, score, dirList := dirSet.toArray.map leaf, sample }
  IO.println "\n== COMMUNITIES (scattered themes: a uses-community spanning ≥2 directories → regroup) =="
  IO.println s!"   score = (dirs−1)·cohesion·concept·module-scale-prior (τ≈{tau.round.toUInt64.toNat} decls) ;  con<0 = not embedded"
  for r in (rows.qsort (fun a b => a.score > b.score)).toList.take top do
    IO.println s!"  score={pct r.score} size={r.size} mods={r.mods} dirs={r.dirs} coh={pct r.coh}% con={pctS r.con}"
    IO.println s!"      dirs: {", ".intercalate r.dirList.toList}"
    IO.println s!"      e.g.: {", ".intercalate r.sample.toList}"
  -- directory fracture: how many communities each directory scatters into
  let mut dpart : HashMap String (HashMap Nat Nat) := {}
  for n in nodes do
    let d := directory (g.d2m.getD n "")
    let c := label.getD n 0
    let inner := dpart.getD d {}
    dpart := dpart.insert d (inner.insert c ((inner.getD c 0) + 1))
  let mut fr : Array DirFracture := #[]
  for (d, inner) in dpart.toArray do
    let total := inner.toArray.foldl (fun s kv => s + kv.2) 0
    if total < 4 || inner.size < 2 then continue
    let maj := inner.toArray.foldl (fun m kv => Nat.max m kv.2) 0
    fr := fr.push { dir := d, total, comms := inner.size, purity := maj.toFloat / total.toFloat }
  IO.println "\n== DIRECTORY FRACTURE (a directory split across many communities → grab-bag, split) =="
  IO.println "   purity = largest community's share of the directory's decls (low = fractured)"
  for r in (fr.qsort (fun a b => a.purity < b.purity)).toList.take top do
    IO.println s!"  purity={pct r.purity}% communities={r.comms} decls={r.total}  {r.dir}"

/-! ### The command -/

/-- Run the scored modularity report on the graph restricted to modules under `--prefix`. -/
def modularityCmd (args : List String) : IO Unit := do
  let argv := args.toArray
  let pfx := (argv.find? (·.startsWith "--prefix=")).map (·.drop 9 |>.toString)
    |>.getD "DeepWiki.SymbolicIntegration"
  let top := (argv.find? (·.startsWith "--top=")).bind (·.drop 6 |>.toString.toNat?) |>.getD 15
  let db ← openDb ((← IO.getEnv "WIKI_DB").getD defaultDbPath)
  let g ← loadGraph db pfx
  let eOpt ← loadEmbeds db pfx
  reportSplit g top
  reportMisplaced g top
  reportCoupling g top
  reportDirectory g top
  reportCommunities g eOpt top
  match eOpt with
  | none => IO.println "\n(no embeddings — run `scripts/wiki index` for the conceptual/NL layer)"
  | some e => reportConceptual e top; reportRegroup g e top

end WikiRAG
