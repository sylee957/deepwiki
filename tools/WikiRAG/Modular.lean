import WikiRAG.Query
import Std.Data.HashMap

/-! # Modularity analytics over the `uses` graph

Turns the exact `uses` dependency graph into **quantified, ranked** refactoring signals — a
decision-support engine (it scores and ranks; the agent validates). Every signal is a *continuous
score*, never a hard threshold: modules/decls/pairs are ranked by the score and the top ones shown.
The only knobs are `--top=N` (how many to display) and `--prefix=NS` (scope).

Scores (all derived from the graph, no magic cutoffs):
* **cohesion** `C(m) = intra / (intra + inter)` ∈ [0,1] — internal-edge fraction of a module.
* **split** `S(m) = (1 − C(m)) · fragmentation(m)`, `fragmentation = 1 − maxCommunity / size` from
  label-propagation communities on the module's own subgraph — high ⇒ the module wants to decompose.
* **misplacement** `M(d) = (bestOtherAffinity − homeAffinity) · (1 − 1/deg)` ∈ [−1,1] — a decl pulled
  toward another module, degree-discounted so low-degree noise self-attenuates (no degree cutoff).
* **coupling** `K(m₁,m₂) = cross / √(size₁·size₂)` — size-normalised cross-directory coupling.
* **granularity** per directory: cohesion + mean module size, reported as numbers, not flags. -/

namespace WikiRAG
open Std SQLite SQLite.Blob

/-- The namespace directory of a module = its path minus the last component. -/
def directory (m : String) : String :=
  let parts := m.splitOn "."
  if parts.length ≤ 1 then m else ".".intercalate parts.dropLast

@[inline] def bump (m : HashMap String Nat) (k : String) : HashMap String Nat :=
  m.insert k ((m.getD k 0) + 1)

/-- Percent (0–100) of a [0,1] score, for display. -/
@[inline] def pct (x : Float) : Int := (x * 100.0).round.toUInt64.toNat

/-- Signed percent, for objectives that can be negative (e.g. conceptual disagreement). -/
@[inline] def pctS (x : Float) : Int :=
  let n : Int := (x.abs * 100.0).round.toUInt64.toNat
  if x < 0.0 then -n else n

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

/-- **Newman modularity `Q`** of the community partition of an undirected subgraph.
`Q = Σ_c [ e_c / (2E) − (deg_c / 2E)² ]` where `e_c` = twice the intra-community edge count,
`deg_c` = total degree of community `c`, `E` = edge count. High `Q` ⇒ genuine sub-community
structure (a candidate to split); a flat bag of independent decls scores ~0. Returns `(Q, #communities)`. -/
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

/-- Componentwise sum of two equal-length vectors (for embedding centroids). -/
def vadd (a b : Array Float) : Array Float :=
  if a.size == b.size then (Array.range a.size).map (fun i => a[i]! + b[i]!) else b

/-- Run the scored modularity report on the graph restricted to modules under `--prefix`. -/
def modularityCmd (args : List String) : IO Unit := do
  let argv := args.toArray
  let pfx := (argv.find? (·.startsWith "--prefix=")).map (·.drop 9 |>.toString)
    |>.getD "DeepWiki.SymbolicIntegration"
  let top := (argv.find? (·.startsWith "--top=")).bind (·.drop 6 |>.toString.toNat?) |>.getD 15
  let path := (← IO.getEnv "WIKI_DB").getD defaultDbPath
  let db ← openDb path
  let decls ← allDecls db
  let mut d2m : HashMap String String := {}
  let mut short : HashMap String String := {}
  let mut sizeM : HashMap String Nat := {}
  for h in decls do
    if h.module.startsWith pfx then
      d2m := d2m.insert h.name h.module
      short := short.insert h.name h.short
      sizeM := bump sizeM h.module
  let edgesAll ← allEdges db
  let edges := edgesAll.filter (fun (a, b) => a != b && d2m.contains a && d2m.contains b)
  let mut adj : HashMap String (Array String) := {}
  for (a, b) in edges do
    adj := adj.insert a ((adj.getD a #[]).push b)
    adj := adj.insert b ((adj.getD b #[]).push a)
  -- cohesion accumulators (per module, per directory)
  let mut intraM : HashMap String Nat := {}; let mut extM : HashMap String Nat := {}
  let mut intraD : HashMap String Nat := {}; let mut extD : HashMap String Nat := {}
  let mut pairX : HashMap String Nat := {}
  for (a, b) in edges do
    let ma := d2m.getD a ""; let mb := d2m.getD b ""
    if ma == mb then intraM := bump intraM ma
    else
      extM := bump extM ma; extM := bump extM mb
      let key := if ma < mb then s!"{ma}||{mb}" else s!"{mb}||{ma}"
      pairX := bump pairX key
    let da := directory ma; let dbb := directory mb
    if da == dbb then intraD := bump intraD da else extD := bump extD da; extD := bump extD dbb
  let cohM := fun m => let i := intraM.getD m 0; let e := extM.getD m 0
                       if i + e == 0 then 1.0 else i.toFloat / (i + e).toFloat
  -- SPLIT score = internal Newman modularity Q (genuine sub-community structure)
  let mut splits : Array (String × Float × Float × Nat × Nat) := #[]
  for (m, sz) in sizeM.toArray do
    let members := decls.filterMap (fun h => if h.module == m then some h.name else none)
    let memberSet := HashSet.ofArray members
    let mut subAdj : HashMap String (Array String) := {}
    for n in members do subAdj := subAdj.insert n ((adj.getD n #[]).filter memberSet.contains)
    let (q, ncomm) := modularityQ members subAdj
    splits := splits.push (m, q, cohM m, ncomm, sz)
  IO.println "\n== SPLIT (score = internal modularity Q; #communities = the split axis) =="
  for (m, q, c, ncomm, sz) in (splits.qsort (fun a b => a.2.1 > b.2.1)).toList.take top do
    IO.println s!"  Q={pct q}  {m}  size={sz} cohesion={pct c}% communities={ncomm}"
  -- MISPLACEMENT score M(d) = (bestOther − home) · (1 − 1/deg)
  let mut misp : Array (String × Float × String × String × Nat) := #[]
  for (n, nbrs) in adj.toArray do
    let deg := nbrs.size
    if deg == 0 then continue
    let home := d2m.getD n ""
    let mut byMod : HashMap String Nat := {}
    for x in nbrs do byMod := bump byMod (d2m.getD x "")
    let mut alt := home; let mut cnt := 0
    for (mm, c) in byMod.toArray do if mm != home && c > cnt then alt := mm; cnt := c
    let bestOther := cnt.toFloat / deg.toFloat
    let homeAff := (byMod.getD home 0).toFloat / deg.toFloat
    let score := (bestOther - homeAff) * (1.0 - 1.0 / deg.toFloat)
    if alt != home then misp := misp.push (short.getD n n, score, home, alt, deg)
  IO.println "\n== MISPLACED (score = (bestOtherAffinity − homeAffinity)·(1−1/deg)) =="
  for (s, sc, home, alt, deg) in (misp.qsort (fun a b => a.2.1 > b.2.1)).toList.take top do
    IO.println s!"  {pct sc}  {s}  [{home.splitOn "." |>.getLastD home}]→[{alt.splitOn "." |>.getLastD alt}] deg={deg}"
  -- COUPLING score K = cross / √(size₁·size₂), cross-directory pairs
  let mut coup : Array (String × String × Float × Nat) := #[]
  for (k, w) in pairX.toArray do
    let ps := k.splitOn "||"; let m1 := ps.getD 0 ""; let m2 := ps.getD 1 ""
    if directory m1 != directory m2 then
      let denom := Float.sqrt ((sizeM.getD m1 1) * (sizeM.getD m2 1)).toFloat
      coup := coup.push (m1, m2, w.toFloat / denom, w)
  IO.println "\n== COUPLING (score = cross / √(size₁·size₂); cross-directory) =="
  for (m1, m2, sc, w) in (coup.qsort (fun a b => a.2.2.1 > b.2.2.1)).toList.take top do
    IO.println s!"  {pct sc}  ({w} edges)  {m1}  ⇄  {m2}"
  -- DIRECTORY granularity (numbers, no flags)
  let mut dirMods : HashMap String (Array Nat) := {}
  for (m, sz) in sizeM.toArray do
    let d := directory m; dirMods := dirMods.insert d ((dirMods.getD d #[]).push sz)
  IO.println "\n== DIRECTORY granularity (cohesion, module count, mean size — no thresholds) =="
  let dirs := dirMods.toArray.map (fun (d, ss) =>
    let n := ss.size; let mx := ss.foldl Nat.max 0
    let avg := if n == 0 then 0 else (ss.foldl (·+·) 0) / n
    let i := intraD.getD d 0; let e := extD.getD d 0
    let c := if i + e == 0 then 1.0 else i.toFloat / (i+e).toFloat
    (d, c, n, avg, mx))
  for (d, c, n, avg, mx) in (dirs.qsort (fun a b => a.2.1 < b.2.1)).toList.take top do
    IO.println s!"  cohesion={pct c}%  modules={n} mean={avg} max={mx}  {d}"
  -- ===== CONCEPTUAL (NL) layer: cosine over the Ollama docstring embeddings =====
  let es ← db.prepare s!"SELECT name, module, embedding FROM decls WHERE embedding IS NOT NULL AND module LIKE '{pfx}%'"
  let mut embs : Array (String × String × Array Float) := #[]
  while (← es.step) do
    match (fromBinary (← es.columnBlob 2) : Except String (Array Float)) with
    | .ok v => embs := embs.push (← es.columnText 0, ← es.columnText 1, v)
    | .error _ => pure ()
  if embs.isEmpty then
    IO.println "\n(no embeddings — run `scripts/wiki index` for the conceptual/NL layer)"
  else
    -- module centroids (unnormalised sums; `cosine` normalises)
    let mut sums : HashMap String (Array Float) := {}
    for (_, md, v) in embs do sums := sums.insert md (vadd (sums.getD md #[]) v)
    let mods := sums.toArray.map (·.1)
    -- CONCEPTUAL cohesion: mean cosine of a module's decls to its docstring centroid
    let mut chS : HashMap String Float := {}; let mut chN : HashMap String Nat := {}
    for (_, md, v) in embs do
      chS := chS.insert md ((chS.getD md 0.0) + cosine v (sums.getD md #[])); chN := bump chN md
    IO.println s!"\n== CONCEPTUAL cohesion (mean docstring-cosine of a module's decls; {embs.size} embedded) =="
    let ccoh := mods.map (fun md => (md, (chS.getD md 0.0) / (chN.getD md 1).toFloat))
    for (md, sc) in (ccoh.qsort (fun a b => a.2 < b.2)).toList.take top do
      IO.println s!"  {pct sc}  {md}"
    -- MULTI-OBJECTIVE regroup (NSGA-style, no weighting): each move-candidate carries a vector
    -- (structural pull, conceptual agreement, disturbance = bond to a home sibling). Keep the Pareto
    -- non-dominated set on (str↑, con↑, dis↓); the LLM judge picks. `dis` high ⇒ the move would
    -- split a conceptually-bonded pair (the `mul_left`/`mul_right` guard) — visible, not hidden.
    let mut modVecs : HashMap String (Array (Array Float)) := {}
    for (_, md, v) in embs do modVecs := modVecs.insert md ((modVecs.getD md #[]).push v)
    let mut cand : Array (String × String × String × Float × Float × Float) := #[]
    for (nm, home, v) in embs do
      let nbrs := adj.getD nm #[]
      let deg := nbrs.size
      if deg == 0 then continue
      let mut byMod : HashMap String Nat := {}
      for x in nbrs do byMod := bump byMod (d2m.getD x "")
      let mut alt := home; let mut cnt := 0
      for (mm, c) in byMod.toArray do if mm != home && c > cnt then alt := mm; cnt := c
      if alt == home then continue
      let str := (cnt.toFloat / deg.toFloat - (byMod.getD home 0).toFloat / deg.toFloat)
        * (1.0 - 1.0 / deg.toFloat)
      let con := cosine v (sums.getD alt #[]) - cosine v (sums.getD home #[])
      let mut dis := 0.0
      for sv in modVecs.getD home #[] do
        let s := cosine v sv
        if s < 0.999 && s > dis then dis := s   -- nearest home sibling (excluding self ≈ 1)
      cand := cand.push (short.getD nm nm, home, alt, str, con, dis)
    -- Pareto front: drop candidates dominated on (str↑, con↑, dis↓)
    let front := cand.filter (fun (_, _, _, si, ci, di) =>
      !cand.any (fun (_, _, _, sj, cj, dj) =>
        sj ≥ si && cj ≥ ci && dj ≤ di && (sj > si || cj > ci || dj < di)))
    IO.println s!"\n== MULTI-OBJECTIVE regroup — Pareto front {front.size}/{cand.size} (str=structural pull, con=conceptual agreement, dis=disturbance; high dis = move splits a bonded pair) =="
    for (s, home, alt, st, cn, ds) in (front.qsort (fun a b => a.2.2.2.1 > b.2.2.2.1)).toList.take top do
      IO.println s!"  str={pctS st} con={pctS cn} dis={pct ds}  {s}  [{home.splitOn "." |>.getLastD home}]→[{alt.splitOn "." |>.getLastD alt}]"

end WikiRAG
