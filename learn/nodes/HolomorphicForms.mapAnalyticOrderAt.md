---
id: HolomorphicForms.mapAnalyticOrderAt
title: The ramification index as an order of vanishing
summary: 'The multiplicity of `f` at `p` is the order of vanishing of `f` minus `f p` in local coordinates, and because that order is truncated to ℕ it reads 0 rather than ∞ when `f` is locally constant at `p`.'
review: draft
authors:
- claude
caveats:
- '`analyticOrderNatAt` is the ℕ truncation of an ℕ∞-valued order, so order ⊤ — the function vanishing identically near the point — also reads as 0. Since the value at the base point is subtracted off, that is exactly the case where `f` is locally constant at `p`, which is why positivity needs a nonconstancy hypothesis. For an `f` that is not holomorphic at `p` the number is whatever Mathlib''s convention yields; nothing in the project pins it down.'
- 'The definition is written in the canonical charts at `p` and `f p`. That it does not depend on the charts is a separate theorem (`mapAnalyticOrderAt_congr_of_maximalAtlas`), proved for charts in the maximal atlas, using holomorphy and continuity of `f` at `p`.'
- 'Nothing in the definition requires `f` to be holomorphic. For an arbitrary `f` the number is whatever Mathlib''s junk convention yields.'
quiz:
- q: 'What exactly is `mapAnalyticOrderAt f p`?'
  type: choice
  choices:
  - 'The order of vanishing at `chartAt ℂ p p` of `t ↦ chartLocalAt f p t − chartLocalAt f p (chartAt ℂ p p)`'
  - The number of preimages of `f p`
  - 'The order of the zero of `f` itself at `p`'
  answer: 0
  explain: 'Jacobian/HolomorphicForms/HolomorphicMap.lean lines 154–157: the value at the base point is subtracted off first, so the function being measured vanishes there by construction.'
- q: 'If `f` is constant near `p`, what is `mapAnalyticOrderAt f p`?'
  type: choice
  choices:
  - '1'
  - '0'
  - Undefined
  answer: 1
  explain: 'The difference is identically zero near the point, so the ℕ∞-valued order is ⊤ and `analyticOrderNatAt` truncates ⊤ to 0 — see the `horder_ne_top` step of `mapAnalyticOrderAt_pos` at Jacobian/HolomorphicForms/HolomorphicMap.lean lines 812–857.'
- q: What is needed to know the index is at least 1 at every point?
  type: choice
  choices:
  - Nothing; it holds by definition
  - 'That `f` is holomorphic and nonconstant, with `X` preconnected and `Y` Hausdorff'
  - That `f` is injective
  answer: 1
  explain: 'Those are exactly the hypotheses of `mapAnalyticOrderAt_pos` (Jacobian/HolomorphicForms/HolomorphicMap.lean lines 812–857); connectedness upgrades "locally constant at one point" to "globally constant", contradicting nonconstancy.'
- q: 'An index of 1 at `p` corresponds to what classical statement?'
  type: choice
  choices:
  - '`f` is injective on all of `X`'
  - 'The derivative of `f` in local coordinates is nonzero at `p`, so `f` is a local biholomorphism there'
  - '`p` is a branch point'
  answer: 1
  explain: 'For `f` holomorphic at `x` the project proves the equivalence `mapAnalyticOrderAt f x = 1 ↔ deriv (chartLocalAt f x) (chartAt ℂ x x) ≠ 0` (Jacobian/TraceDegree/TraceDefinition.lean lines 100–124), and `localInverseAt_holomorphic` (Jacobian/TraceDegree/TraceDefinition.lean lines 127–218) shows the local inverse there is holomorphic.'
---
## Plain English

In one complex variable, a holomorphic map near a point looks like `w = z^k` after a change of coordinates. That `k` is the multiplicity, or ramification index: one preimage for `k = 1`, `k` sheets colliding for `k > 1`.

`mapAnalyticOrderAt f p` computes `k` the direct way. Write `f` in local coordinates ([chartLocalAt](#/node/HolomorphicForms.chartLocalAt)), subtract off its value at the coordinate of `p` so that the resulting function vanishes there, and ask Mathlib for the order of that zero:

```
mapAnalyticOrderAt f p =
  analyticOrderNatAt (fun t => chartLocalAt f p t - chartLocalAt f p (chartAt ℂ p p)) (chartAt ℂ p p)
```

## The convention to watch

`analyticOrderNatAt` is a natural number, obtained by truncating an ℕ∞-valued order. Two different situations come out as 0:

- the function does not vanish at the point — impossible here, since we subtracted the value off;
- the function vanishes identically near the point — order ⊤, truncated to 0.

So for a holomorphic `f`, "index 0" means "`f` is locally constant at `p`". That is why `mapAnalyticOrderAt_pos` (Jacobian/HolomorphicForms/HolomorphicMap.lean lines 812–857) needs real hypotheses: `f` holomorphic, `f` not globally constant, `X` preconnected, `Y` Hausdorff. The proof rules out the ⊤ case by showing that local constancy at one point spreads over a connected surface.

## Why this is a legitimate ramification index

Two theorems do the work that makes the name honest.

Chart-independence: `mapAnalyticOrderAt_congr_of_maximalAtlas` (Jacobian/HolomorphicForms/HolomorphicMap.lean lines 395–477) shows that computing the order in any charts drawn from the maximal atlas gives the same number. The proof uses that chart transitions are analytic with nonvanishing derivative, so composing with them multiplies the order by 1.

The derivative criterion: for `f` holomorphic at `x`, index 1 at `x` is equivalent to the local derivative being nonzero (Jacobian/TraceDegree/TraceDefinition.lean lines 100–124). This is what lets the project invert the differential at unramified points and so define the pushforward of forms.

## How it is used

It is the ramification index: [branchedCoverData_of_nonconstant_holomorphic](#/node/Blueprint.branchedCoverData_of_nonconstant_holomorphic) takes `ramificationIndex := mapAnalyticOrderAt f`, and `BranchedCoverData.RamificationIndexCompatible` (Jacobian/HolomorphicForms/BranchedCover.lean lines 91–95) is the predicate demanding that any other hand-built datum agree with it. That predicate is what makes the public [ContMDiff.degree](#/node/ContMDiff.degree) well defined.
