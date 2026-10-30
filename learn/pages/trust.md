# Trust: what has and hasn't been checked

This site **explains** a Lean library. It does not re-prove it. Here is exactly what rests on what, for `main` @ `6b3d4f4b` (2026-10-30).

## Lean checking

| | jacobian-variety @ 6b3d4f4b |
|---|---|
| Toolchain | `leanprover/lean4:v4.31.0-rc1`, Mathlib `v4.31.0-rc1` (`lean-toolchain`, `lakefile.toml`, and `README.md` all agree). Some file-level comments inside `Jacobian/` still reason about what Mathlib v4.28.0 did or did not provide; read those as rationale from when they were written |
| Builds publicly | **yes.** GitHub CI "Solution linter check" builds `Jacobian.Solution` on every push to `main`; it passed at `6b3d4f4b` ([run 41000926350](https://github.com/tangentproofs/jacobian-variety/actions/runs/41000926350)) |
| Statements match the challenge | **yes, at this commit.** CI runs the official [comparator](https://github.com/leanprover/comparator) (pinned at `3afea23`) with `comparator/jacobian-smoketest.json`, which checks that each of the eleven theorems and nine definitions has exactly the type it has in `Jacobian/Challenge.lean`. It passed at `6b3d4f4b` ([run 41000926329](https://github.com/tangentproofs/jacobian-variety/actions/runs/41000926329)). The smoketest config still *permits* `sorryAx`, so it does not check axioms |
| Strict comparator (no `sorry` allowed) | **reported passing on 2026-10-28** by the repair's progress log (`ref/independent-repair-progress.md`, `ref/axiom-audit.md` §0): "Lean default kernel accepts the solution. Your solution is okay!". Not run in CI; `main` has a few later commits (CI fixes) |
| `#print axioms` | **re-run here at `6b3d4f4b`: only `propext`, `Classical.choice`, `Quot.sound`.** On 2026-10-30 this site built `Jacobian.Solution` at `6b3d4f4b` and ran `#print axioms` on all twenty challenge declarations (the eleven theorems and nine definitions) plus the `T2Space`, `CompactSpace`, `IsManifold` and `LieAddGroup` instances on `Jacobian X`. Every one depends on exactly those three standard axioms, with no `sorryAx`. This agrees with `ref/axiom-audit.md` §0 and the strict comparator run of 2026-10-28 |
| `sorry` | three, all in `Jacobian/Periods/Hurewicz.lean` (lines 1354, 1625, 5007), used only inside that file. That file is in the library's import closure, but importing is not depending: no public declaration uses them (source reading by the audit, and the `#print axioms` re-check above) |
| `axiom`, `opaque`, `unsafe`, `native_decide`, `implemented_by`, `extern` | none in `Jacobian/` (grep; the matches are in comments) |
| Not built | `Attic/` (retired code, outside the library roots) |

## What the comparator does and does not certify

- It certifies that the eleven theorem **statements** and the nine definition **types** in `Solution.lean` are exactly those of `Challenge.lean`, and (strict config) that the proofs use only `propext`, `Quot.sound` and `Classical.choice`.
- It compares a definition's **type**, not its body. So it cannot tell a genuine `Jacobian` from a fake one with the same type. The [review](#/review) is what checks the bodies.
- It does **not** list the `T2Space`, `CompactSpace`, `IsManifold` and `LieAddGroup` instances on `Jacobian X` that the challenge also asks for. They are proved in `Jacobian/Solution.lean` lines 96–103 and covered by the `#print axioms` re-check above, but the harness does not compare them with the challenge.

## The honesty audit

An independent model (Claude) read the Lean, without building it, and compared every headline and every challenge definition with the classical theory. Verdict **PASS WITH CAVEATS**; summary on the [review](#/review) page, full report in [learn/JACOBIAN_CLAUDE_AUDIT.md](https://github.com/tangentproofs/jacobian-variety/blob/main/learn/JACOBIAN_CLAUDE_AUDIT.md). It also found vacuous declarations with classical names (for example `periodPairing`, which is the zero map, and `riemannRoch_formula_general`) in two imported-but-unused files. They are not on the public path and this site does not cite them.

## This site's own data

- **Declarations were read from the source text, not from a Lean build.** `learn/tools/scan_decls.py` follows the imports of `Jacobian.lean` and finds the declarations in those 160 files with exact lines and text. Every declaration carries `"extracted": false`. The "mentions" edges are matched by name, using each file's namespaces and `open` lines, so some edges may be missing or wrong. A theorem named inside a definition's body is counted as a proof use, not a mention.
- **Anonymous instances** get the name Lean most likely generates. The three listed in `comparator/jacobian.json` (`Jacobian.instAddCommGroup`, `Jacobian.instTopologicalSpace`, `Jacobian.instChartedSpaceForallFinGenusComplex`) are Lean's real names; the others are approximations.
- **Identifier links on the source pages are matched by name** (`data/xref.json` is marked `"heuristic": true`).
- **Line references are locked.** Every "File.lean lines a–b" on this site is recorded in `learn/data/srcrefs.lock.json` with the text of those lines, and `npm test` fails if the Lean under a reference changes.
- **Explanations** are drafts written by Claude for Grok Bot (`review: draft`), checked against the audit by a second Claude pass, not reviewed by a person.
- **Widgets and outlines** are summaries, never evidence.
