import WikiRAG.Query
import WikiRAG.Cochange
import Std.Data.HashMap

/-! # `recommend` — one sampled Pareto action over the `uses` graph

Turns the exact `uses` dependency graph into **one concrete, Codex-ready recommendation**. Each action
type is a Pareto front over its own objective vector (**no weighting**, `dominatesVec` / `paretoFront`):
- **regroup-theme** — a `uses`-community spanning ≥2 directories (a scattered theme → one module);
- **split-dir** — a directory fractured across many communities (a grab-bag → split);
- **merge** — a thin module whose `uses` concentrate on one neighbour (absorb it — inverse of split);
- **move-decl** — a declaration whose dependencies favour another module.

Communities cluster with weighted Louvain over `uses` edges reinforced by conceptual agreement
(`--wcon`·docstring-cosine) and module co-change (`--wevo`·evolutionary pull). Since within a front no
candidate dominates another, the selector is **randomized**: `recommend` stratified-samples `--k`
action(s) — a bucket (action type) then a member — so the loop rotates across action types instead of
hammering one. `--seed=N` (the loop passes a fresh seed) makes any run reproducible.

Knobs: `--prefix=NS`, `--k=N`, `--seed=N`, `--wcon=`, `--wevo=` — weights and sampling, never cutoffs. -/

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

/-! ### Generic Pareto core (shared by every ranked report)

Every recommendation type ranks its candidates by **Pareto non-domination over its own objective
vector**, never a weighted scalar — the framework is the method, the axes are per report. An objective
is `(value, isCost)`: `isCost = false` is maximised, `true` is minimised. Fronts are *not* compared
across report types (a split is not an alternative to a merge) — each report keeps its own front. -/

/-- `d` Pareto-dominates `c`: weakly better on every objective, strictly better on at least one. -/
def dominatesVec (d c : Array (Float × Bool)) : Bool :=
  (Array.zip d c).all (fun p => if p.1.2 then p.1.1 ≤ p.2.1 else p.1.1 ≥ p.2.1)
  && (Array.zip d c).any (fun p => if p.1.2 then p.1.1 < p.2.1 else p.1.1 > p.2.1)

/-- The Pareto-non-dominated subset of `xs` under the objective vector `vec`. -/
def paretoFront {α : Type} (xs : Array α) (vec : α → Array (Float × Bool)) : Array α :=
  xs.filter (fun c => !xs.any (fun d => dominatesVec (vec d) (vec c)))

/-- Maximise-objective helper: `(value, isCost := false)`. -/
@[inline] def maxObj (x : Float) : Float × Bool := (x, false)
/-- Minimise-objective (cost) helper: `(value, isCost := true)`. -/
@[inline] def costObj (x : Float) : Float × Bool := (x, true)
/-- Conceptual objective value: fold "not embedded" (`con < 0`) to a neutral `0`. -/
@[inline] def conObj (con : Float) : Float := if con < 0.0 then 0.0 else con

/-- Parse a non-negative decimal (`"1.5"`, `"2"`) for a CLI weight; `d` on any parse failure. -/
def parseFloatD (s : String) (d : Float) : Float :=
  match s.splitOn "." with
  | [i] => (i.toNat?).map (·.toFloat) |>.getD d
  | [i, f] =>
    match i.toNat?, f.toNat? with
    | some ip, some fp => ip.toFloat + fp.toFloat / (Nat.pow 10 f.length).toFloat
    | _, _ => d
  | _ => d

/-- Componentwise sum of two equal-length vectors (for embedding centroids). -/
def vadd (a b : Array Float) : Array Float :=
  if a.size == b.size then (Array.range a.size).map (fun i => a[i]! + b[i]!) else b


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

/-- Regroup's objective vector: `(str↑, con↑, evo↑, dis↓)` for the shared `paretoFront`. -/
@[inline] def Regroup.vec (c : Regroup) : Array (Float × Bool) :=
  #[maxObj c.str, maxObj c.con, maxObj c.evo, costObj c.dis]

/-- MOVE-DECL candidates: each carries `(str, con, evo, dis)`; return the Pareto non-dominated front.
A high `dis` means the move would split a bonded pair (the `mul_left`/`mul_right` guard), visible as an
objective rather than hidden in a weighted sum. -/
def regroupCands (g : Graph) (e : Embeds) : Array Regroup := Id.run do
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
  return paretoFront cand Regroup.vec

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

/-- One level of **weighted Louvain** local-moving from singletons: greedily move each node to the
neighbouring community with the largest modularity gain `kᵢ,in(c) − Σtot(c)·kᵢ/2m` until stable.
Unlike label propagation, the degree penalty `Σtot·kᵢ/2m` makes merging into an already-large
community costly, so it resists the giant-community collapse and yields balanced, module-sized
communities. Single level *by design* — Louvain's aggregation phase coarsens communities, the
opposite of what surfacing liftable themes needs. -/
def louvain (nodes : Array String) (wadj : HashMap String (Array (String × Float)))
    (kdeg : HashMap String Float) (twoM : Float) : HashMap String Nat := Id.run do
  let mut comm : HashMap String Nat := {}
  let mut sigmaTot : HashMap Nat Float := {}
  let mut i := 0
  for n in nodes do
    comm := comm.insert n i
    sigmaTot := sigmaTot.insert i (kdeg.getD n 0.0)
    i := i + 1
  let m2 := if twoM == 0.0 then 1.0 else twoM
  for _ in [0:12] do
    let mut moved := false
    for n in nodes do
      let cn := comm.getD n 0
      let kn := kdeg.getD n 0.0
      -- total weight from n to each neighbouring community
      let mut kin : HashMap Nat Float := {}
      for (x, w) in wadj.getD n #[] do
        if x != n then
          let cx := comm.getD x 0
          kin := kin.insert cx ((kin.getD cx 0.0) + w)
      -- isolate n, then choose the community (incl. staying) with the largest gain
      sigmaTot := sigmaTot.insert cn ((sigmaTot.getD cn 0.0) - kn)
      let mut best := cn
      let mut bestGain := (kin.getD cn 0.0) - (sigmaTot.getD cn 0.0) * kn / m2
      for (c, kic) in kin.toArray do
        let gain := kic - (sigmaTot.getD c 0.0) * kn / m2
        if gain > bestGain then best := c; bestGain := gain
      sigmaTot := sigmaTot.insert best ((sigmaTot.getD best 0.0) + kn)
      if best != cn then comm := comm.insert n best; moved := true
    if !moved then break
  return comm

/-- COMMUNITIES + FRACTURE: cluster the whole in-scope graph and diff it against the directory tree —
scattered themes to regroup and grab-bag directories to split. Clusters with weighted Louvain over a
graph whose `uses` edges are reinforced by conceptual agreement (`wcon`·docstring-cosine) and module
co-change (`wevo`·evolutionary pull) — so the partition reflects meaning and history, not just calls. -/
def clusterAnalysis (g : Graph) (eOpt : Option Embeds) (wcon wevo : Float) :
    Array Community × Array DirFracture := Id.run do
  let nodes := g.d2m.toArray.filterMap fun (n, _) =>
    if isStructuralNoise (g.short.getD n n) then none else some n
  if nodes.isEmpty then return (#[], #[])
  let vmap : HashMap String (Array Float) :=
    match eOpt with
    | none => {}
    | some e => e.rows.foldl (fun m r => m.insert r.1 r.2.2) {}
  -- weighted undirected graph: structural multiplicity, reinforced by concept cosine + co-change
  let nodeSet := HashSet.ofArray nodes
  let mut ew : HashMap String Float := {}
  for (n, nbrs) in g.adj.toArray do
    if nodeSet.contains n then
      for x in nbrs do
        if x != n && nodeSet.contains x then
          let k := pairKey n x
          ew := ew.insert k ((ew.getD k 0.0) + 1.0)
  let mut wadj : HashMap String (Array (String × Float)) := {}
  let mut kdeg : HashMap String Float := {}
  let mut twoM := 0.0
  for (k, sw) in ew.toArray do
    let ps := k.splitOn "||"; let a := ps.getD 0 ""; let b := ps.getD 1 ""
    let cw := match vmap.get? a, vmap.get? b with
      | some va, some vb => let c := cosine va vb; if c > 0.0 then wcon * c else 0.0
      | _, _ => 0.0
    let w := sw + cw + wevo * g.evoPull (g.d2m.getD a "") (g.d2m.getD b "")
    wadj := wadj.insert a ((wadj.getD a #[]).push (b, w))
    wadj := wadj.insert b ((wadj.getD b #[]).push (a, w))
    kdeg := kdeg.insert a ((kdeg.getD a 0.0) + w)
    kdeg := kdeg.insert b ((kdeg.getD b 0.0) + w)
    twoM := twoM + 2.0 * w
  let label := louvain nodes wadj kdeg twoM
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
  -- Pareto front over native axes (dispersion↑, cohesion↑, concept↑, module-scale fit↑); no weighting
  let commFront := paretoFront rows (fun r =>
    #[maxObj (r.dirs - 1).toFloat, maxObj r.coh, maxObj (conObj r.con),
      maxObj (r.size.toFloat * Float.exp (-r.size.toFloat / tau))])
  -- directory fracture: how many communities each directory scatters into (a grab-bag → split)
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
  -- fracture front: low purity (cost) and many decls (a bigger grab-bag matters more)
  let frFront := paretoFront fr (fun r => #[costObj r.purity, maxObj r.total.toFloat])
  return (commFront, frFront)

/-! ### Merge (thin-file absorption — the inverse of split) -/

/-- A thin module that should be absorbed into another: small, weakly self-cohesive, and with its
outward `uses` concentrated on one neighbour (its natural home). -/
structure MergeCand where
  m : String        -- the thin module
  target : String   -- the module to merge it into
  size : Nat        -- #decls in the thin module
  cohesion : Float  -- internal cohesion (low ⇒ doesn't earn a standalone file)
  conc : Float      -- share of the module's external `uses` endpoints going to `target`
  con : Float       -- conceptual cosine of the two module centroids (<0 = not embedded)
  score : Float     -- conc·(1−cohesion)·smallness-prior·concept — a clear absorption candidate

/-- MERGE: rank thin modules that should be absorbed into a single neighbour. A module scores high when
it is small, has little internal structure to justify a standalone file, and most of its outward
dependencies point at one other module — so it reads as a fragment of that module. Catches the
1-declaration "thin file" that adds a navigation hop with no cohesion gain. (Zero-declaration
re-export shim *files* carry no `uses` edges, so they are invisible here — those are the retire-shim
guardrail's job, found by grep, not this graph signal.) -/
def mergeCands (g : Graph) (eOpt : Option Embeds) : Array MergeCand := Id.run do
  let totalDecls := g.sizeM.toArray.foldl (fun s kv => s + kv.2) 0
  let tau := totalDecls.toFloat / (Nat.max 1 g.sizeM.size).toFloat
  let sums : HashMap String (Array Float) := match eOpt with | some e => e.sums | none => {}
  let mut rows : Array MergeCand := #[]
  for (m, size) in g.sizeM.toArray do
    -- distribution of this module's outward `uses` over other modules
    let mut byT : HashMap String Nat := {}
    for n in g.members.getD m #[] do
      for x in g.adj.getD n #[] do
        let mt := g.d2m.getD x ""
        if mt != m && mt != "" then byT := bump byT mt
    let ext := byT.toArray.foldl (fun s kv => s + kv.2) 0
    if ext == 0 then continue     -- self-contained; not a merge-by-coupling case
    let mut target := ""; let mut tc := 0
    for (t, c) in byT.toArray do if c > tc then target := t; tc := c
    let coh := g.cohesion m
    let con := match sums.get? m, sums.get? target with
      | some a, some b => cosine a b
      | _, _ => -1.0
    let conW := if con < 0.0 then 1.0 else if con > 0.0 then con else 0.0
    let score := (tc.toFloat / ext.toFloat) * (1.0 - coh) * Float.exp (-size.toFloat / tau) * conW
    rows := rows.push
      { m, target, size, cohesion := coh, conc := tc.toFloat / ext.toFloat, con, score }
  -- Pareto front over native axes (absorb-need↑, smallness↑, target-concentration↑, concept↑)
  return paretoFront rows (fun r =>
    #[maxObj (1.0 - r.cohesion), maxObj (Float.exp (-r.size.toFloat / tau)),
      maxObj r.conc, maxObj (conObj r.con)])

/-! ### One sampled recommendation (Pareto fronts → stratified random draw) -/

/-- A single concrete, Codex-ready recommendation: its action kind, a headline, and detail lines. -/
structure Action where
  kind : String
  head : String
  lines : Array String
deriving Inhabited

/-- Render an action as a card. -/
def Action.render (a : Action) : String :=
  s!"ACTION [{a.kind}]  {a.head}\n" ++ String.intercalate "\n" (a.lines.toList.map ("    " ++ ·))

/-- Regroup a scattered theme (a `uses`-community spanning ≥2 directories) into one module. -/
def Community.action (r : Community) : Action :=
  { kind := "regroup-theme"
    head := s!"gather a scattered theme — {r.size} decls across {r.dirs} directories → one module"
    lines := #[
      s!"why (Pareto-nondominated): dispersion {r.dirs} dirs · cohesion {pct r.coh}% · concept {pctS r.con}%",
      s!"dirs:  {", ".intercalate r.dirList.toList}",
      s!"e.g.:  {", ".intercalate r.sample.toList}",
      "plan:  git mv these into one module + aggregator; unify near-duplicate lemmas (wiki rdeps first)"] }

/-- Split a grab-bag directory (its decls scatter across many communities). -/
def DirFracture.action (r : DirFracture) : Action :=
  { kind := "split-dir"
    head := s!"split a grab-bag directory — {r.comms} communities across {r.total} decls"
    lines := #[
      s!"why (Pareto-nondominated): purity {pct r.purity}% (largest community's share — low = fractured)",
      s!"dir:   {r.dir}",
      "plan:  split along the community axis into concept subdirectories + aggregator"] }

/-- Absorb a thin module into the neighbour its `uses` concentrate on (the inverse of split). -/
def MergeCand.action (r : MergeCand) : Action :=
  { kind := "merge"
    head := s!"absorb a thin module ({r.size} decls) into one neighbour"
    lines := #[
      s!"why (Pareto-nondominated): absorb-need {pct (1.0 - r.cohesion)}% · concentration {pct r.conc}% · concept {pctS r.con}%",
      s!"{leaf r.m}  ⇒  {leaf r.target}   ({r.m})",
      "plan:  wiki rdeps first; move the decls in; git rm the emptied file; gate"] }

/-- Move a misplaced declaration to the module its dependencies favour. -/
def Regroup.action (r : Regroup) : Action :=
  { kind := "move-decl"
    head := s!"move a misplaced declaration to its natural home"
    lines := #[
      s!"why (Pareto-nondominated): structural-pull {pctS r.str}% · concept {pctS r.con}% · co-change {pct r.evo}% · disturbance {pct r.dis}%",
      s!"{r.short}:  [{leaf r.home}] → [{leaf r.alt}]",
      "plan:  wiki rdeps first; move the decl; fix imports; gate  (skip if disturbance high — a bonded sibling)"] }

/-- A tiny LCG step for seeded, reproducible sampling (no global RNG needed). -/
@[inline] def lcgNext (s : Nat) : Nat := (6364136223846793005 * s + 1442695040888963407) % 18446744073709551616

/-! ### The command -/

/-- `recommend`: compute every action type's Pareto front, pool them, and **stratified-sample** `--k`
concrete action(s) to hand Codex. Randomization is the principled selector: within a Pareto front no
candidate dominates another, so sampling (not argmax over a re-weighted scalar) is how you pick one —
and stratifying by action type rotates Codex across regroup/split/merge/move over the loop rather than
hammering one report. `--seed=N` makes a run reproducible (the loop passes a fresh seed each iteration). -/
def recommendCmd (args : List String) : IO Unit := do
  let argv := args.toArray
  let pfx := (argv.find? (·.startsWith "--prefix=")).map (·.drop 9 |>.toString)
    |>.getD "DeepWiki.SymbolicIntegration"
  let k := (argv.find? (·.startsWith "--k=")).bind (·.drop 4 |>.toString.toNat?) |>.getD 1
  let flt (flag : String) (d : Float) : Float :=
    parseFloatD ((argv.find? (·.startsWith flag)).map (·.drop flag.length |>.toString) |>.getD "") d
  let wcon := flt "--wcon=" 1.5   -- conceptual reinforcement of clustering edges
  let wevo := flt "--wevo=" 1.0   -- co-change reinforcement of clustering edges
  let seed0 ← match (argv.find? (·.startsWith "--seed=")).bind (·.drop 7 |>.toString.toNat?) with
    | some n => pure n
    | none   => IO.monoNanosNow
  let db ← openDb ((← IO.getEnv "WIKI_DB").getD defaultDbPath)
  let g ← loadGraph db pfx
  let eOpt ← loadEmbeds db pfx
  let (comms, frs) := clusterAnalysis g eOpt wcon wevo
  let merges := mergeCands g eOpt
  let moves := match eOpt with | some e => regroupCands g e | none => #[]
  let buckets : Array (Array Action) := (#[
      comms.map Community.action,
      frs.map DirFracture.action,
      merges.map MergeCand.action,
      moves.map Regroup.action]).filter (!·.isEmpty)
  if buckets.isEmpty then
    IO.println "no recommendation — nothing non-dominated in scope (already well-organized?)"
    return
  IO.println s!"# {buckets.size} action type(s) live under {pfx}; sampling {k} (seed {seed0})"
  let mut seed := seed0
  for _ in [0:k] do
    seed := lcgNext seed
    let acts := buckets[seed % buckets.size]!
    seed := lcgNext seed
    IO.println ("\n" ++ (acts[seed % acts.size]!).render)

end WikiRAG
