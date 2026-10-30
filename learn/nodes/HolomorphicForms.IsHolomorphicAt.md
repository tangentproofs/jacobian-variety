---
id: HolomorphicForms.IsHolomorphicAt
title: Holomorphic at a point, defined by hand
summary: 'Rather than reuse a Mathlib predicate for "holomorphic map of complex manifolds", the project defines one from scratch: analyticity of the map read in the canonical chart at each end.'
review: draft
authors:
- claude
caveats:
- 'Written in the *canonical* charts `chartAt ℂ p` and `chartAt ℂ (f p)`, not in an arbitrary pair of charts. Independence of the atlas is not part of the definition; for the order of vanishing it is a separate theorem, and continuity of `f` is a hypothesis there.'
- 'The predicate carries no continuity. `AnalyticAt` constrains the composite on a whole neighbourhood, including values where the chart at `f p` is applied outside its source and so returns junk, so for a map that is wildly discontinuous at `p` the predicate is a statement about junk values rather than about `f`. In practice every consumer pairs it with continuity.'
- 'It is a point-wise condition only. "Holomorphic" as a global notion is `IsHolomorphicBasic` (continuity plus this at every point).'
- 'The file header''s stated reason for rolling this predicate by hand — "Mathlib `v4.28.0` does not provide a manifold-level analytic predicate" — is a stale note: the project is pinned to `v4.31.0-rc1` (`lean-toolchain`, `lakefile.toml` line 15). Read it as the file''s rationale when it was written, not as a check against the current pin.'
quiz:
- q: 'What does `IsHolomorphicAt f p` unfold to?'
  type: choice
  choices:
  - '`AnalyticAt ℂ (chartLocalAt f p) (chartAt ℂ p p)`'
  - '`DifferentiableAt ℂ f p`'
  - '`ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f p`'
  answer: 0
  explain: 'That is the definition verbatim (Jacobian/HolomorphicForms/HolomorphicMap.lean lines 36–37): the chart-local presentation is analytic at the coordinate of `p`.'
- q: What reason does the file give for defining this instead of using a Mathlib predicate?
  type: choice
  choices:
  - Mathlib''s version is too slow
  - 'That Mathlib provided no manifold-level analytic predicate — no `MAnalyticAt`, no `Holomorphic*` — at the version the file was written against'
  - To avoid the axiom of choice
  answer: 1
  explain: 'The file header says exactly this (Jacobian/HolomorphicForms/HolomorphicMap.lean lines 10–19) and names `chartAt ℂ` plus `AnalyticAt ℂ` as the replacement; the version it names, `v4.28.0`, is older than the project''s current pin.'
- q: How does this relate to Mathlib's `ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω`?
  type: choice
  choices:
  - They are unrelated
  - '`ContMDiff` implies it at every point, and conversely holding at every point plus continuity implies `ContMDiff`'
  - It is strictly weaker, with no converse
  answer: 1
  explain: '`IsHolomorphicAt.of_contMDiff` (Jacobian/HolomorphicForms/HolomorphicMap.lean lines 496–510) gives one direction and `ContMDiff.of_isHolomorphic_and_continuous` (Jacobian/HolomorphicForms/HolomorphicMap.lean lines 525–544) the other.'
- q: 'Does `IsHolomorphicAt f p` by itself say `f` is continuous at `p`?'
  type: choice
  choices:
  - 'Yes, analytic functions are continuous'
  - 'No; the structure `IsHolomorphicBasic` adds continuity as a separate field'
  - 'Only if `X` is compact'
  answer: 1
  explain: 'The analyticity is about the chart-local composite, not about `f`; `IsHolomorphicBasic` (Jacobian/HolomorphicForms/HolomorphicMap.lean lines 164–166) lists `continuous` as its own field.'
---
## Plain English

Mathlib knows what it means for a map of manifolds to be smooth (`ContMDiff`). The file header records that it had no predicate for "holomorphic map of complex manifolds" — no `MAnalyticAt`, no `Holomorphic` — and rolls its own (Jacobian/HolomorphicForms/HolomorphicMap.lean lines 10–19). That header names Mathlib `v4.28.0`, while the project is now pinned to `v4.31.0-rc1`, so treat it as the file's rationale rather than a current fact about Mathlib.

The definition is the obvious one. `f : X → Y` is holomorphic at `p` when the map ℂ → ℂ you get by reading `f` in the canonical chart at `p` and the canonical chart at `f p` is complex-analytic at the coordinate of `p`:

```
IsHolomorphicAt f p  ↔  AnalyticAt ℂ (chartLocalAt f p) (chartAt ℂ p p)
```

See [chartLocalAt](#/node/HolomorphicForms.chartLocalAt) for the composite. `AnalyticAt ℂ g z` is Mathlib's "`g` is the sum of a convergent power series on a neighbourhood of `z`", which for complex functions is the same as being complex-differentiable there.

## Is it the right notion?

Two theorems say yes, measured against Mathlib's own standard. `IsHolomorphicAt.of_contMDiff` (Jacobian/HolomorphicForms/HolomorphicMap.lean lines 496–510) shows a map that is `ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω` (complex-analytically smooth as a map of manifolds) is holomorphic at every point in this sense. `ContMDiff.of_isHolomorphic_and_continuous` (Jacobian/HolomorphicForms/HolomorphicMap.lean lines 525–544) goes back: point-wise chart-local analyticity plus global continuity gives `ContMDiff`. Both directions assume `X` and `Y` are complex manifolds (`[IsManifold 𝓘(ℂ) ω …]`), which is where the chart transitions are known to be analytic. So the project's predicate and Mathlib's agree, with continuity kept separate.

That separation is deliberate and it matters. On its own, `IsHolomorphicAt f p` is a condition on a composite that involves applying the chart at `f p` to values of `f` that may lie outside that chart's source, where a partial homeomorphism returns an unspecified value. Once `f` is continuous at `p` the composite genuinely describes `f` near `p`. Every consumer in the project supplies continuity, either as a field of `IsHolomorphicBasic` or as an explicit hypothesis.

## How it is used

Closure properties are proved directly: sums, scalar multiples, finite linear combinations, and composition (with a continuity side condition) — Jacobian/HolomorphicForms/HolomorphicMap.lean lines 40–129. The global notions [IsHolomorphicBasic](#/node/HolomorphicForms.IsHolomorphicBasic) and [IsHolomorphic](#/node/HolomorphicForms.IsHolomorphic) are built on it, and `BranchedCoverData.RamificationIndexCompatible` (Jacobian/HolomorphicForms/BranchedCover.lean lines 91–95) uses it as the side condition under which a combinatorial ramification index must match the analytic one.
