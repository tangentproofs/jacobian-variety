# Contributing to "Jacobian, explained" (learn/)

This folder is a plain-English explainer for the Lean library in this repository
(a tangentproofs informalization site; conventions:
[tangentproofs.github.io/docs/proof-sites](https://github.com/tangentproofs/tangentproofs.github.io/tree/main/docs/proof-sites)).
The Lean is the ground truth. The site builds with Node and Python only; no Lean build is needed.

## Nodes

One file per explained declaration: `learn/nodes/<id>.md`, where `<id>` is the Lean name with the
`JacobianChallenge.` prefix dropped (see `learn/data/decls.json`).

- YAML front matter, checked against `learn/schema/node.schema.json`: `id`, `title` (3–80 chars),
  `summary` (one sentence that leads with the key takeaway), `review: draft`, `authors`, optional
  `caveats`, and a `quiz` of 3–6 questions (`q`, `type`, `choices`, `answer`, `explain`).
- A Markdown body with a `## Plain English` section.
- Faithful to the Lean as written. Anything looser goes under `caveats`. If a definition is not the
  classical object, or a hypothesis does the hard part, say so.
- Link declarations as `[name](#/node/<id>)`. Cite Lean by full repo path and exact lines,
  e.g. `Jacobian/Solution.lean lines 74–78`; these become links to the rendered source.
- Keep `review: draft` unless a person has checked the text and the quiz key against the Lean.

## Commands

```sh
cd learn
npm ci
python3 tools/scan_decls.py         # after any Lean change: refresh data/decls.json and data/xref.json
python3 tools/srcrefs_lock.py --lock  # after writing new "File.lean lines a–b" references (check them first)
python3 tools/srcrefs_lock.py --remap # after a Lean change moved cited lines
npm test                            # schema, ids, quiz keys, locked line references, shared modules
npm run serve                       # http://localhost:8765/
```

CI (`.github/workflows/pages.yml`) runs `npm test`, re-runs `scan_decls.py` and fails if `data/` is
stale, then publishes the site at <https://tangentproofs.github.io/jacobian-variety/learn/>.
