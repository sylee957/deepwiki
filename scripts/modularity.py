#!/usr/bin/env python3
"""Modularization analytics over WikiRAG's `.wiki/graph.db`.

Turns the exact `uses` dependency graph into *quantified, ranked* refactoring suggestions —
a decision-support engine for an agent, not an automatic rewriter. Structural analyses only
(no embeddings needed); a semantic layer can be added once `scripts/wiki index` has run.

Analyses (each maps to one of the four concerns):
  1. cohesion / coupling per module + per directory (MQ-style)  -> where to split / health
  2. split candidates: large low-cohesion modules + their internal communities (the split axis)
  3. misplaced decls: a decl whose `uses`/used-by neighbours live mostly in another module -> regroup
  4. co-locate candidates: tightly-coupled module pairs sitting in different directories -> regroup
  5. duplicate / unifiable decls: identical signatures (up to name) in different modules -> retire

Over- vs under-refactoring is surfaced explicitly: under = large low-cohesion modules with several
internal communities (split); over = directories of many tiny mutually-coupled modules (merge).

Usage:  python3 scripts/modularity.py [--json] [--top N] [--db .wiki/graph.db]
"""
import argparse, json, os, re, sqlite3, sys
from collections import defaultdict, Counter

def load(db):
    con = sqlite3.connect(db)
    decls = {name: module for name, module in con.execute("SELECT name, module FROM decls")}
    sig = {name: (s or "") for name, s in con.execute("SELECT name, signature FROM decls")}
    kind = {name: (k or "") for name, k in con.execute("SELECT name, kind FROM decls")}
    edges = [(s, d) for s, d in con.execute("SELECT src, dst FROM edges")
             if s in decls and d in decls and s != d]
    con.close()
    return decls, sig, kind, edges

def directory(module):
    # the namespace directory = module path minus its last component
    return module.rsplit(".", 1)[0] if "." in module else module

def cohesion(decls, edges):
    """intra/inter edge counts per module and per directory."""
    intra_m, ext_m, size_m = Counter(), Counter(), Counter()
    intra_d, ext_d = Counter(), Counter()
    for n, m in decls.items():
        size_m[m] += 1
    for s, d in edges:
        ms, md = decls[s], decls[d]
        if ms == md: intra_m[ms] += 1
        else: ext_m[ms] += 1; ext_m[md] += 1
        ds, dd = directory(ms), directory(md)
        if ds == dd: intra_d[ds] += 1
        else: ext_d[ds] += 1; ext_d[dd] += 1
    return intra_m, ext_m, size_m, intra_d, ext_d

def coh_ratio(intra, ext):
    tot = intra + ext
    return (intra / tot) if tot else 1.0

def communities(nodes, adj, passes=6):
    """Label propagation on an undirected subgraph — cheap community detection."""
    label = {n: i for i, n in enumerate(nodes)}
    order = list(nodes)
    for _ in range(passes):
        changed = False
        for n in order:
            if not adj[n]: continue
            cnt = Counter(label[x] for x in adj[n])
            best = max(cnt.items(), key=lambda kv: (kv[1], -kv[0]))[0]
            if label[n] != best:
                label[n] = best; changed = True
        if not changed: break
    groups = defaultdict(list)
    for n, l in label.items(): groups[l].append(n)
    return sorted(groups.values(), key=len, reverse=True)

def normalize_sig(name, s):
    # strip the decl's own short name + whitespace so "up to name" duplicates collide
    short = name.rsplit(".", 1)[-1]
    s = s.replace(short, "∎")
    return re.sub(r"\s+", " ", s).strip()

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--db", default=".wiki/graph.db")
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--top", type=int, default=15)
    ap.add_argument("--prefix", default="DeepWiki.SymbolicIntegration",
                    help="restrict analysis to modules under this namespace")
    a = ap.parse_args()
    if not os.path.exists(a.db):
        sys.exit(f"no graph at {a.db} — run `scripts/wiki build` first")

    decls, sig, kind, edges = load(a.db)
    # restrict to the area of interest
    decls = {n: m for n, m in decls.items() if m.startswith(a.prefix)}
    edges = [(s, d) for s, d in edges if s in decls and d in decls]
    intra_m, ext_m, size_m, intra_d, ext_d = cohesion(decls, edges)

    # undirected adjacency (decl-level), for community detection
    adj = defaultdict(set)
    for s, d in edges: adj[s].add(d); adj[d].add(s)

    report = {}

    # (1)+(2) split candidates: large, low-cohesion modules with >1 internal community
    splits = []
    for m, sz in size_m.items():
        if sz < 40: continue
        c = coh_ratio(intra_m[m], ext_m[m])
        members = [n for n in decls if decls[n] == m]
        sub_adj = {n: (adj[n] & set(members)) for n in members}
        comms = communities(members, sub_adj)
        big = [g for g in comms if len(g) >= 5]
        if len(big) >= 2:
            splits.append({"module": m, "size": sz, "cohesion": round(c, 2),
                           "communities": len(big),
                           "sizes": [len(g) for g in big[:6]]})
    splits.sort(key=lambda x: (-x["size"], x["cohesion"]))
    report["split_candidates"] = splits[:a.top]

    # (3) misplaced decls: neighbours mostly in another module
    misplaced = []
    for n in decls:
        nb = adj[n]
        if len(nb) < 4: continue
        home = decls[n]
        by_mod = Counter(decls[x] for x in nb)
        alt, cnt = by_mod.most_common(1)[0]
        frac = cnt / len(nb)
        if alt != home and frac >= 0.75 and by_mod[home] <= cnt // 2:
            misplaced.append({"decl": n.rsplit(".",1)[-1], "home": home,
                              "belongs": alt, "frac": round(frac, 2), "deg": len(nb)})
    misplaced.sort(key=lambda x: (-x["frac"], -x["deg"]))
    report["misplaced_decls"] = misplaced[:a.top]

    # (4) co-locate: tightly coupled module pairs in different directories
    pair = Counter()
    for s, d in edges:
        ms, md = decls[s], decls[d]
        if ms != md:
            pair[tuple(sorted((ms, md)))] += 1
    colocate = []
    for (m1, m2), w in pair.items():
        if w >= 15 and directory(m1) != directory(m2):
            colocate.append({"a": m1, "b": m2, "weight": w})
    colocate.sort(key=lambda x: -x["weight"])
    report["colocate_candidates"] = colocate[:a.top]

    # (5) duplicate / unifiable: identical signature-up-to-name in different modules.
    # Restrict to genuine reusable decls (theorem/lemma/def that TAKE arguments) and skip
    # example modules — otherwise same-typed worked-examples flood the result. The precise
    # version (distinguishing same-type from same-meaning) needs the embedding layer.
    by_sig = defaultdict(list)
    for n in decls:
        s = sig.get(n, "")
        m = decls[n]
        if len(s) < 20 or "→" not in s and "->" not in s: continue
        if "Example" in m or kind.get(n, "") not in ("theorem", "lemma", "def", "abbrev"): continue
        by_sig[normalize_sig(n, s)].append(n)
    dups = []
    for s, names in by_sig.items():
        mods = {decls[n] for n in names}
        if len(names) >= 2 and len(mods) >= 2:
            dups.append({"count": len(names), "modules": sorted(mods),
                         "decls": [n.rsplit(".",1)[-1] for n in names]})
    dups.sort(key=lambda x: -x["count"])
    report["duplicate_candidates"] = dups[:a.top]

    # over/under refactoring health, per directory
    dirs = defaultdict(list)
    for m, sz in size_m.items(): dirs[directory(m)].append(sz)
    health = []
    for d, sizes in dirs.items():
        n = len(sizes); avg = sum(sizes)/n
        c = coh_ratio(intra_d[d], ext_d[d])
        flag = ("under (split)" if (max(sizes) > 120 and c < 0.55)
                else "over (merge)" if (n >= 8 and avg < 6)
                else "ok")
        health.append({"dir": d, "modules": n, "avg_size": round(avg,1),
                       "max": max(sizes), "cohesion": round(c,2), "flag": flag})
    health.sort(key=lambda x: (x["flag"] == "ok", -x["max"]))
    report["directory_health"] = health[:a.top]

    if a.json:
        print(json.dumps(report, indent=2)); return
    # human report
    def sec(t): print(f"\n\033[1m{t}\033[0m")
    sec(f"SPLIT candidates (large, low-cohesion, ≥2 internal communities)")
    for x in report["split_candidates"]:
        print(f"  {x['module']}  size={x['size']} cohesion={x['cohesion']} "
              f"→ {x['communities']} communities {x['sizes']}")
    sec("MISPLACED decls (neighbours mostly in another module → regroup)")
    for x in report["misplaced_decls"]:
        print(f"  {x['decl']}  [{x['home'].split('.')[-1]}] → {x['belongs'].split('.')[-1]} "
              f"({x['frac']*100:.0f}% of {x['deg']} deps)")
    sec("CO-LOCATE candidates (tightly coupled, different directories)")
    for x in report["colocate_candidates"]:
        print(f"  {x['weight']:4d}  {x['a']}  ⇄  {x['b']}")
    sec("DUPLICATE / unifiable (identical signature up-to-name, different modules → retire)")
    for x in report["duplicate_candidates"]:
        print(f"  ×{x['count']}  {x['decls']}  in {[m.split('.')[-1] for m in x['modules']]}")
    sec("DIRECTORY health (over- vs under-refactoring)")
    for x in report["directory_health"]:
        mark = "" if x["flag"] == "ok" else f"  ⚠ {x['flag']}"
        print(f"  {x['dir']}  modules={x['modules']} avg={x['avg_size']} "
              f"max={x['max']} cohesion={x['cohesion']}{mark}")

if __name__ == "__main__":
    main()
