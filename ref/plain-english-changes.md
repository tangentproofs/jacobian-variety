# Plain-English changes log

Every plain-English block (blueprint `tex/`, `blueprint/`, prose docstrings that carry the
owner's blueprint voice) touched on branch `independent-repair`, with the old text, the new
text and the reason. Edits are kept minimal and in the original voice. Purely technical
Lean docstrings written during the repair (new declarations, GAP labels) are not listed
here; they are listed in `ref/independent-repair-progress.md`.

---

## 1. `tex/statements/challenge-statement.tex` — `lem:stable-chart-at-instance`

**Why.** The block said the `StableChartAt` instance "currently stands as an open
obligation". It was never open: chart stability is false on every compact connected
Riemann surface (`not_chartStable_of_compactSpace`, compiled). The class and instance are
deleted (goal (a)).

**Old.**
> Chart-stability adapter instance (open). The `StableChartAt` adapter instance threaded
> through the public manifold / Lie structure of Jac(X). It currently stands as an open
> obligation (`sorry`) in `Jacobian/Solution.lean`; the honest route replaces it with
> genuine chart-overlap-derivative continuity (worker jc3). Tracking: #237.
> `\lean{…instStableChartAt…}`

**New.**
> Chart-stability adapter instance (retired: refuted). The `StableChartAt` adapter
> instance used to be threaded through the public manifold / Lie structure of Jac(X). It
> is not an open obligation but a false one: no compact connected Riemann surface has
> chart stability, and this is now a proved theorem (`not_chartStable_of_compactSpace`).
> The instance and the class are deleted; the few places that really used them now carry
> honest, labelled gaps, and the honest route is genuine chart-overlap-derivative
> continuity (worker jc3). Tracking: #237. `\lean{…not_chartStable_of_compactSpace}`
> `\leanok`

The sentence "the honest route replaces it with genuine chart-overlap-derivative
continuity" is kept in substance.

## 2. `scripts/audit-leanok-axioms.py:8-9` (docstring example)

**Why.** The example named "the open `StableChartAt` instance", which no longer exists.

**Old.** `… -> the open \`StableChartAt\` instance).`
**New.** `… -> an open \`sorry\` declaration).`
