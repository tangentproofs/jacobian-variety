#!/usr/bin/env python3
"""Build learn/data/decls.json and learn/data/xref.json from the Lean source text, WITHOUT a Lean build.

The reference sites (star-height and others) extract declarations from a compiled build
(ExtractDecls.lean) and identifier references from Lean's .ilean files. This site reads the source
text instead (no Lean build on the shared machines), as rakesieve and subexponential-sat do:

  * files: the import closure of Jacobian.lean (the library's root module), in import order.
    Jacobian/Challenge.lean is not in that closure (it is the frozen spec the comparator checks
    Solution.lean against); it is rendered as source but contributes no declarations;
  * declarations: `def/theorem/lemma/abbrev/structure/class/inductive/instance` lines, with namespace,
    line range and verbatim header text; ids drop the `JacobianChallenge.` prefix;
  * anonymous instances get the name Lean would most likely generate (inst + class + type heads),
    except the public Jacobian instances, whose real names are listed in comparator/jacobian.json;
  * mentions (meaningDeps) / proof uses (proofDeps): identifier tokens of the statement (and of a
    definition's body) / of a theorem's proof, resolved against the declarations found here using the
    enclosing namespaces and the file's `open` lines;
  * Mathlib links: tokens on the hand-checked list MATHLIB below.

Every declaration is marked `"extracted": false` so the site and its Trust page say so.
"""
import hashlib, json, os, re

LEARN = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ROOT = os.path.dirname(LEARN)
OUT = os.path.join(LEARN, "data")
NS_PREFIX = "JacobianChallenge."


def mod_file(m):
    return m.replace(".", "/") + ".lean"


def built_files():
    """Import closure of Jacobian.lean over project modules, dependencies first."""
    order, seen = [], set()
    def visit(m):
        if m in seen: return
        seen.add(m)
        text = open(os.path.join(ROOT, mod_file(m)), encoding="utf-8").read()
        for i in re.findall(r"^import\s+(\S+)", text, re.M):
            if i.split(".")[0] == "Jacobian" and os.path.exists(os.path.join(ROOT, mod_file(i))): visit(i)
        order.append(mod_file(m))
    visit("Jacobian")
    return order


def headlines():
    """The headline list lives in one place, assets/app.js (HEADLINES)."""
    app = open(os.path.join(LEARN, "assets", "app.js"), encoding="utf-8").read()
    return json.loads(re.search(r"const HEADLINES = (\[[^\]]*\]);", app, re.S).group(1))


FILES = built_files()
HEADS = headlines()

# Mathlib / core names that appear in the statements this site explains (checked against the Mathlib docs).
MATHLIB = """TopologicalSpace T2Space CompactSpace ConnectedSpace ChartedSpace IsManifold ContMDiff ContMDiffAt
ContMDiffOn Module.finrank Module.Free Module.Finite FiniteDimensional Metric.sphere EuclideanSpace Nonempty Homeomorph
AddCommGroup LieAddGroup modelWithCornersSelf ModelWithCorners ULift ULift.up ULift.down Function.Injective Fin
ContinuousAddMonoidHom AddSubgroup Submodule Submodule.span Module.Basis Basis LinearMap AddMonoidHom
QuotientAddGroup DiscreteTopology IsZLattice ZLattice Complex Real Nat Int Set Finset Finset.sum
OpenPartialHomeomorph PartialHomeomorph chartAt extChartAt mfderiv MDifferentiable DifferentiableAt
DifferentiableOn AnalyticAt AnalyticOn ContinuousLinearMap Classical.choose Function.Surjective Function.Bijective
OnePoint IsOpen IsCompact Continuous ContinuousOn intervalIntegral MeasureTheory.integral Path ContinuousMap
Subtype Prop Type Membership HasSum tsum Filter Filter.Tendsto nhds Dual Module.Dual Matrix Polynomial
AddEquiv LinearEquiv ContinuousLinearEquiv HSMul SMul Zero Add Neg Sub""".split()
ALIASES = {n: n for n in MATHLIB}
for n in list(MATHLIB):
    if "." in n: ALIASES.setdefault(n.rsplit(".", 1)[1], n)

# Lean's real names for the anonymous instances of Solution.lean's public interface
# (comparator/jacobian.json lists them under definition_names).
REAL_INST = {("Jacobian/Solution.lean", "AddCommGroup"): "Jacobian.instAddCommGroup",
             ("Jacobian/Solution.lean", "TopologicalSpace"): "Jacobian.instTopologicalSpace",
             ("Jacobian/Solution.lean", "ChartedSpace"): "Jacobian.instChartedSpaceForallFinGenusComplex"}

DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*(def|theorem|lemma|abbrev|structure|inductive|class|instance)\b\s*(?:\([^)]*priority[^)]*\)\s*)?([^\s:({\[]*)")
TOK = re.compile(r"[A-Za-z_\u00c0-\u024f\u0370-\u03ff\u1d00-\u1dbf\u2080-\u209f\u2100-\u214f][\w.'\u00c0-\u024f\u0370-\u03ff\u1d00-\u1dbf\u2080-\u209f\u2100-\u214f!?₀-₉]*")
OPEN, CLOSE = "([{⟨⦃", ")]}⟩⦄"


def cut(text, kind):
    """Header up to the top-level ':=' (or ' where' / first top-level '|'). Whole text for types."""
    if kind in ("structure", "inductive", "class"): return text.rstrip(), ""
    depth, i = 0, 0
    while i < len(text):
        c = text[i]
        if c in OPEN: depth += 1
        elif c in CLOSE: depth = max(0, depth - 1)
        elif depth == 0 and text.startswith(":=", i): return text[:i].rstrip(), text[i:]
        elif depth == 0 and re.match(r"\swhere\b", text[i:i + 7]): return text[:i].rstrip(), text[i:]
        elif depth == 0 and kind != "theorem" and c == "\n" and re.match(r"\n\s*\|", text[i:]): return text[:i].rstrip(), text[i:]
        i += 1
    return text.rstrip(), ""


def inst_parts(header, ns=()):
    """Approximate Lean's generated instance name parts: constant heads in order, ℂ → Complex,
    `→` → Forall, lower-case constants capitalised; bound variables (single letters) and the
    enclosing namespaces are skipped (Lean drops a namespace prefix it is already inside)."""
    depth, cut_at = 0, None
    for i, c in enumerate(header):  # the type starts after the first top-level ':'
        if c in OPEN: depth += 1
        elif c in CLOSE: depth -= 1
        elif c == ":" and depth == 0 and header[i:i + 2] != ":=": cut_at = i; break
    h = header[cut_at + 1:] if cut_at is not None else header
    h = re.split(r"\swhere\b|:=", h)[0]
    h = re.sub(r"\([^()]*:=[^()]*\)", "", h)
    h = h.replace("ℂ", " Complex ").replace("ℝ", " Real ").replace("ℕ", " Nat ").replace("ℤ", " Int ").replace("→", " Forall ")
    out = []
    for t in TOK.findall(h):
        last = t.split(".")[-1]
        if len(last) <= 1 or last in ns or last in ("ω", "Type"): continue
        out.append(last[0].upper() + last[1:])
    return out


def strip_comments(lines):
    """Blank out comment text (keeping line structure) so scanning ignores commented-out code."""
    text = "\n".join(lines)
    out, i, depth, n = [], 0, 0, len(text)
    while i < n:
        if text.startswith("/-", i): depth += 1; i += 2; out.append("  "); continue
        if depth and text.startswith("-/", i): depth -= 1; i += 2; out.append("  "); continue
        if depth: out.append("\n" if text[i] == "\n" else " "); i += 1; continue
        if text.startswith("--", i):
            j = text.find("\n", i); j = n if j < 0 else j
            out.append(" " * (j - i)); i = j; continue
        out.append(text[i]); i += 1
    return "".join(out).split("\n")


def scan(file):
    raw = open(os.path.join(ROOT, file), encoding="utf-8").read().split("\n")
    lines = strip_comments(raw)
    scopes = [("file", "", [])]  # (kind, name, variables)
    opens = []
    starts = []
    def ns(): return [s[1] for s in scopes if s[0] == "ns" for s in [s]]
    for k, ln in enumerate(lines):
        if not ln.strip(): continue
        if m := re.match(r"^(?:noncomputable\s+)?namespace\s+(\S+)", ln):
            for part in m.group(1).split("."): scopes.append(("ns", part, []))
            starts.append(("other", k)); continue
        if m := re.match(r"^(?:noncomputable\s+)?section\b\s*(\S*)", ln):
            scopes.append(("sec", m.group(1), [])); starts.append(("other", k)); continue
        if m := re.match(r"^end\b\s*(\S*)\s*$", ln):
            name = m.group(1)
            if name and "." in name and all(s[0] == "ns" for s in scopes[-len(name.split(".")):]):
                for _ in name.split("."): scopes.pop()
            elif len(scopes) > 1: scopes.pop()
            starts.append(("other", k)); continue
        if m := re.match(r"^open\s+(?!scoped)(.*?)(\s+in\s*)?$", ln):
            if not m.group(2):
                for o in re.findall(r"[A-Z][\w.]*", re.sub(r"\([^)]*\)|hiding.*", "", m.group(1))): opens.append(o)
            starts.append(("other", k)); continue
        if re.match(r"^variable\b", ln):
            j = k; text = raw[k]
            while j + 1 < len(lines) and lines[j + 1].startswith((" ", "\t")) and lines[j + 1].strip(): j += 1; text += "\n" + raw[j]
            scopes[-1][2].append(text.strip()); starts.append(("other", k)); continue
        if re.match(r"^(universe|set_option|elab|macro|syntax|macro_rules|attribute|initialize|notation|infix|infixl|infixr|local|scoped|open|#|example|private\s+lemma\s*$)\b", ln) or ln.startswith("#"):
            starts.append(("other", k)); continue
        if m := DECL.match(ln):
            if ln[0] in " \t" and m.group(1) not in ("instance",) and not re.match(r"^\s+(theorem|lemma|def|abbrev|instance|structure|class|inductive|private|protected|noncomputable|@\[)", ln):
                continue
            if ln[0] in " \t": continue  # indented decls are local (where-clauses, mutual blocks are rare here)
            kind, name = m.group(1), m.group(2)
            anon = kind == "instance" and (not name or name.startswith("(") )
            if anon:
                hdr = " ".join(lines[k:k + 4])
                parts = inst_parts(hdr, ns())
                real = REAL_INST.get((file, parts[0] if parts else ""))
                full = real or ".".join(ns() + ["inst" + "".join(parts)])
            else:
                if not name: continue
                full = name[7:] if name.startswith("_root_.") else ".".join(ns() + [name])
            vars_ = [v for s in scopes for v in s[2]]
            starts.append(("decl", k, kind, full, anon, list(opens), vars_, ".".join(ns())))
            continue
    out = []
    for j, st in enumerate(starts):
        if st[0] != "decl": continue
        k, kind, full, anon, ops, vars_, nsname = st[1:]
        end = (starts[j + 1][1] if j + 1 < len(starts) else len(raw)) - 1
        while end > k and not lines[end].strip(): end -= 1
        # back up over a docstring/attribute that belongs to the next declaration
        text = "\n".join(lines[k:end + 1])
        out.append({"name": full, "kind": "theorem" if kind == "lemma" else kind, "file": file,
                    "line": k + 1, "endLine": end + 1, "text": text, "rawText": "\n".join(raw[k:end + 1]),
                    "anonInstance": anon and full not in REAL_INST.values(), "ns": nsname, "opens": ops, "vars": vars_})
    return out


def short(name):
    return name[len(NS_PREFIX):] if name.startswith(NS_PREFIX) else name


def main():
    decls = []
    for f in FILES: decls.extend(scan(f))
    # duplicate full names (e.g. the same name in two files): keep the first, rename later ones
    seen = {}
    for d in decls:
        if d["name"] in seen:
            seen[d["name"]] += 1; d["name"] = f'{d["name"]}#{seen[d["name"]]}'
        else: seen[d["name"]] = 1
    by_full = {d["name"]: d for d in decls}
    by_last = {}
    for d in decls:
        if not d["anonInstance"]:
            parts = d["name"].split(".")
            for i in range(1, len(parts)):
                by_last.setdefault(".".join(parts[i:]), []).append(d)
    for d in decls: d["id"] = short(d["name"])
    ids_seen = {}
    for d in decls:
        assert d["id"] not in ids_seen, f"id clash: {d['id']} ({d['name']} vs {ids_seen[d['id']]})"
        ids_seen[d["id"]] = d["name"]

    def resolve(tok, d):
        if tok.startswith("_root_."): tok = tok[7:]
        if tok in by_full: return by_full[tok]
        ns = d["ns"].split(".") if d["ns"] else []
        for i in range(len(ns), 0, -1):
            c = ".".join(ns[:i] + [tok])
            if c in by_full: return by_full[c]
        for o in d.get("opens", []):
            for c in (o + "." + tok, NS_PREFIX + o + "." + tok):
                if c in by_full: return by_full[c]
        # last resort, for qualified names only (`Foo.bar` written from outside Foo's namespace):
        # a bare short token such as `g`, `L` or `Q` is almost always a local variable
        if "." not in tok: return None
        cands = by_last.get(tok, [])
        return cands[0] if len(cands) == 1 else None

    for d in decls:
        stmt, proof = cut(d["text"], d["kind"])
        rstmt, _ = cut(d["rawText"], d["kind"])
        d["statement"] = d["rawText"].rstrip() if d["kind"] in ("def", "abbrev") and d["rawText"].count("\n") < 8 else rstmt
        meaning_text = stmt if d["kind"] in ("theorem", "instance") else d["text"]
        if d["kind"] in ("def", "abbrev", "instance") and d["kind"] != "instance":
            meaning_text = d["text"]
        bound = {b for grp in re.findall(r"[({⦃\[]\s*([^():{}\[\]⦃⦄]+?)\s*:(?!=)", stmt) for b in grp.split()}

        def deps(text):
            out = []
            for m in TOK.finditer(text):
                if m.start() and text[m.start() - 1] == ".": continue
                # the declared name itself (`def genus …`) is not a use of anything
                if re.search(r"\b(def|abbrev|theorem|lemma|instance|structure|class|inductive)\s+$", text[max(0, m.start() - 20):m.start()]): continue
                t = m.group(0).rstrip(".")
                if t in bound: continue
                cands = [t]
                if "." in t: cands.append(t.split(".", 1)[1])  # x.foo where x is a variable: try the field
                for cand in cands:
                    e = resolve(cand, d)
                    if e and e is not d and not e["anonInstance"]:
                        if e["id"] not in out: out.append(e["id"])
                        break
            return out
        d["_mt"] = meaning_text
        d["meaningDeps"] = deps(meaning_text)
        d["proofDeps"] = [x for x in deps(proof) if x not in d["meaningDeps"]] if d["kind"] in ("theorem", "instance") else []
    kinds = {d["id"]: d["kind"] for d in decls}
    for d in decls:
        # A theorem named inside a definition's body is a proof obligation being discharged (e.g. the
        # discreteness proof packed into `genuinePeriodLattice`), not part of what the definition means:
        # count it as a proof use, so the "statement set" holds only the definitions a reader must know.
        if d["kind"] != "theorem":
            thm = [x for x in d["meaningDeps"] if kinds.get(x) == "theorem"]
            d["meaningDeps"] = [x for x in d["meaningDeps"] if x not in thm]
            d["proofDeps"] = d["proofDeps"] + [x for x in thm if x not in d["proofDeps"]]
        ml = []
        for t in TOK.findall(d["_mt"]):
            n = ALIASES.get(t)
            if n and n not in ml and n not in by_full: ml.append(n)
        d["mathlib"] = ml
    ids = {d["id"]: d for d in decls}
    # Instances are found by type-class search, not by name. Solution.lean's global instance
    # (finite-dimensionality of the holomorphic 1-forms, Solution.lean line 32) is what lets the public
    # signatures elaborate; the public Jacobian instances are part of what `Jacobian X` means.
    sol_inst = [d["id"] for d in decls if d["file"] == "Jacobian/Solution.lean" and d["kind"] == "instance"]
    for d in decls:
        if d["file"] == "Jacobian/Solution.lean" and d["kind"] == "theorem" and d["ns"] in ("Jacobian", ""):
            for v in sol_inst:
                if v not in d["meaningDeps"] and ids[v]["file"] == d["file"] and (v.startswith("Jacobian.inst") and "Jacobian" in d["text"]):
                    d["meaningDeps"].append(v)
    for d in decls:
        d["meaningDeps"] = [x for x in d["meaningDeps"] if x != d["id"]]
    used = {d["id"]: [] for d in decls}
    for e in decls:
        for x in e["meaningDeps"] + e["proofDeps"]: used[x].append(e["id"])
    missing = [h for h in HEADS if h not in ids]
    assert not missing, f"assets/app.js HEADLINES not found in the scan: {missing}"
    dist = {h: 0 for h in HEADS}
    frontier = list(dist)
    while frontier:
        nxt = []
        for i in frontier:
            for j in ids[i]["meaningDeps"] + ids[i]["proofDeps"]:
                if j not in dist: dist[j] = dist[i] + 1; nxt.append(j)
        frontier = nxt
    out = []
    for d in sorted(decls, key=lambda d: (FILES.index(d["file"]), d["line"])):
        out.append({"id": d["id"], "name": d["name"], "kind": d["kind"], "file": d["file"],
                    "module": d["file"][:-5].replace("/", "."), "line": d["line"], "endLine": d["endLine"],
                    "statement": d["statement"], "variables": d["vars"], "truncated": False,
                    "mathlib": d["mathlib"], "meaningDeps": d["meaningDeps"], "proofDeps": d["proofDeps"],
                    "usedBy": sorted(used[d["id"]]), "depth": dist.get(d["id"]), "extracted": False,
                    **({"autoName": True} if d["anonInstance"] else {})})
    json.dump(out, open(os.path.join(OUT, "decls.json"), "w", encoding="utf-8"), indent=1, ensure_ascii=False)

    # Heuristic xref (same format as build_xref.py) for every rendered .lean file.
    names, mods, ni, mi = [], [], {}, {}
    def nix(n):
        if n not in ni: ni[n] = len(names); names.append(n)
        return ni[n]
    def mix(m):
        if m not in mi: mi[m] = len(mods); mods.append(m)
        return mi[m]
    files = {}
    for rel in FILES + ["Jacobian/Challenge.lean"]:
        raw = open(os.path.join(ROOT, rel), "rb").read()
        text = raw.decode("utf-8")
        here = sorted((d for d in decls if d["file"] == rel), key=lambda d: d["line"])
        refs = []
        clean = strip_comments(text.split("\n"))
        hi = 0
        for l0, code in enumerate(clean):
            while hi < len(here) and here[hi]["line"] <= l0 + 1: hi += 1
            ctx = here[hi - 1] if hi else {"ns": "", "opens": []}
            for m in TOK.finditer(code):
                if m.start() and code[m.start() - 1] == ".": continue
                t = m.group(0).rstrip(".")
                c0 = len(text.split("\n")[l0][:m.start()].encode("utf-16-le")) // 2 if False else len(code[:m.start()].encode("utf-16-le")) // 2
                c1 = c0 + len(t.encode("utf-16-le")) // 2
                target, mod = None, None
                e = resolve(t, ctx) if rel != "Jacobian/Challenge.lean" else None
                if e and not e["anonInstance"] and not (e["file"] == rel and e["line"] == l0 + 1):
                    target, mod = e["name"], "project"
                elif t in ALIASES:
                    target, mod = ALIASES[t], "Mathlib"
                if target: refs.append([l0, c0, c1, nix(target), mix(mod)])
        files[rel] = {"sha256": hashlib.sha256(raw).hexdigest(),
                      "decls": [[nix(d["name"]), d["line"] - 1, d["endLine"] - 1] for d in here],
                      "refs": refs}
    json.dump({"version": 1, "heuristic": True, "names": names, "mods": mods, "files": files},
              open(os.path.join(OUT, "xref.json"), "w", encoding="utf-8"), separators=(",", ":"), ensure_ascii=False)
    print(f"files: {len(FILES)}; decls: {len(out)} ({sum(1 for d in out if d['depth'] is not None)} reachable); xref: {len(files)} files, {sum(len(v['refs']) for v in files.values())} refs")


if __name__ == "__main__":
    main()
