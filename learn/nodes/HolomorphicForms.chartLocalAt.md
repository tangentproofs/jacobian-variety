---
id: HolomorphicForms.chartLocalAt
title: Writing a map in local coordinates
summary: '"`f` in local coordinates at `p`" is built from one specific chart at each end, and away from those charts'' domains the formula returns junk values rather than describing `f`.'
review: draft
authors:
- claude
caveats:
- 'The definition uses `chartAt ℂ p` and `chartAt ℂ (f p)`: the *canonical* chart at each point, not an arbitrary chart of the atlas. So the composite depends on that canonical choice. Chart-independence of what is computed from it is a separate theorem, not built into the definition.'
- 'A chart in Mathlib is a partial homeomorphism. Applying `chartAt ℂ (f p)` to a point outside its source is legal but returns a junk value, and `(chartAt ℂ p).symm` likewise outside its target. The composite is therefore only guaranteed to describe `f` near `p`, and only when `f` carries a neighbourhood of `p` into the chart source — which needs continuity of `f` at `p`.'
- 'This is a plain composition of functions. It asserts nothing: no continuity, no analyticity, no fact about `f`.'
quiz:
- q: 'What is `chartLocalAt f p`?'
  type: choice
  choices:
  - 'The composite `chartAt ℂ (f p) ∘ f ∘ (chartAt ℂ p).symm`, a function from ℂ to ℂ'
  - The restriction of `f` to a small open set around `p`
  - The derivative of `f` at `p`
  answer: 0
  explain: 'That composite is the whole definition (Jacobian/HolomorphicForms/HolomorphicMap.lean lines 32–33): go up from ℂ into `X`, apply `f`, come back down to ℂ.'
- q: Which charts does it use?
  type: choice
  choices:
  - An arbitrary pair of charts containing `p` and `f p`
  - 'The canonical charts `chartAt ℂ p` and `chartAt ℂ (f p)`'
  - A global coordinate on each surface
  answer: 1
  explain: 'Jacobian/HolomorphicForms/HolomorphicMap.lean lines 32–33 names `chartAt` explicitly; compact Riemann surfaces have no global coordinate, so there is nothing else available without extra hypotheses.'
- q: 'What does `chartLocalAt f p (chartAt ℂ p p)` evaluate to?'
  type: choice
  choices:
  - '`chartAt ℂ (f p) (f p)`, the coordinate of `f p` in its own canonical chart'
  - '0'
  - 'An unspecified junk value'
  answer: 0
  explain: '`chartLocalAt_chartAt_self` (Jacobian/HolomorphicForms/HolomorphicMap.lean lines 238–244) proves it, using that `(chartAt ℂ p).symm (chartAt ℂ p p) = p`.'
- q: Why do the proofs in this file keep needing continuity of `f` at `p`?
  type: choice
  choices:
  - To make the composite differentiable
  - 'To know that `f` maps a neighbourhood of `p` into the source of `chartAt ℂ (f p)`, where that chart is not junk'
  - Because charts are not continuous
  answer: 1
  explain: 'For example `IsHolomorphicAt.comp` (Jacobian/HolomorphicForms/HolomorphicMap.lean lines 96–129) uses `hf_cont` exactly to get `∀ᶠ z, f ((chartAt ℂ p).symm z) ∈ (chartAt ℂ (f p)).source` before rewriting the chart round trip.'
---
## Plain English

A Riemann surface has no global coordinate. To say anything calculus-like about a map `f : X → Y`, you pick a coordinate patch around a point `p`, a coordinate patch around its image `f p`, and look at the map those coordinates see. That is all `chartLocalAt` is:

```
chartLocalAt f p = chartAt ℂ (f p) ∘ f ∘ (chartAt ℂ p).symm
```

Read it right to left. Start with a complex number, push it up into `X` with the inverse of the chart at `p`, apply `f`, then read the answer off in the chart at `f p`. The result is an ordinary function ℂ → ℂ, which Mathlib's complex analysis can talk about.

Two things are worth being precise about.

First, *which* charts. `chartAt ℂ p` is the canonical chart that the `ChartedSpace ℂ X` instance attaches to `p`; this is not a choice the definition leaves open. Everything built on top — [IsHolomorphicAt](#/node/HolomorphicForms.IsHolomorphicAt) and [mapAnalyticOrderAt](#/node/HolomorphicForms.mapAnalyticOrderAt) — is therefore phrased in terms of that canonical chart, and the fact that any other chart of the atlas would give the same answer has to be proved. It is: `mapAnalyticOrderAt_congr_of_maximalAtlas` (Jacobian/HolomorphicForms/HolomorphicMap.lean lines 395–477) shows the order of vanishing computed in any charts from the maximal atlas agrees with the canonical one.

Second, where the formula is meaningful. A Mathlib chart is a *partial* homeomorphism, defined on a `source` and landing in a `target`; applied outside those it returns an unspecified value. So `chartLocalAt f p` is a function defined on all of ℂ, but it describes `f` only near the coordinate of `p`, and only once you know `f` sends a neighbourhood of `p` into the source of `chartAt ℂ (f p)`. That is why continuity of `f` turns up as a hypothesis throughout the file, even in statements that look purely local.

## How it is used

Everything in the project's local theory of holomorphic maps is stated through this composite: "`f` is holomorphic at `p`" means `chartLocalAt f p` is analytic at the coordinate of `p`, and the ramification index at `p` is the order of vanishing of `chartLocalAt f p` minus its value at that coordinate. The anchor lemma `chartLocalAt_chartAt_self` (Jacobian/HolomorphicForms/HolomorphicMap.lean lines 238–244) records that the composite sends the coordinate of `p` to the coordinate of `f p`, which is what makes "minus its value at the point" the right normalisation.
