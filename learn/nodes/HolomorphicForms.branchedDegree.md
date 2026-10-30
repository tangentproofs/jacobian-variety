---
id: HolomorphicForms.branchedDegree
title: The degree, read off at an arbitrary point
summary: 'The degree is the weighted fibre count over one point picked by `Classical.arbitrary`, which is harmless only because constancy of that count was already assumed.'
review: draft
authors:
- claude
caveats:
- 'The base point is `Classical.arbitrary Y`: an unspecified point supplied by the axiom of choice from `[Nonempty Y]`. Nothing is known about it, and nothing needs to be, because the independence lemma covers every point.'
- 'The value is a function of the *data*, not of `f` alone. Two different `BranchedCoverData` on the same `f` could give different numbers; what rules that out is `RamificationIndexCompatible` plus `branchedDegree_eq_of_compatibleU`, separate declarations — and the latter additionally assumes `f` is holomorphic.'
- 'Nothing here says the degree is positive. `branchedDegree_pos` needs surjectivity of `f` as an explicit hypothesis, and no theorem on the public path proves "nonconstant ⇒ degree > 0".'
quiz:
- q: Which point of `Y` does `branchedDegree` count the fibre over?
  type: choice
  choices:
  - A point where `f` is unramified
  - 'An arbitrary point handed over by `Classical.arbitrary Y`'
  - Every point at once, as a maximum
  answer: 1
  explain: 'The body is `h.weightedFiberCard (Classical.arbitrary Y)` (Jacobian/HolomorphicForms/BranchedCover.lean lines 163–166), which needs only the `[Nonempty Y]` instance.'
- q: Why does the arbitrary choice not matter?
  type: choice
  choices:
  - 'Because `branchedDegree_eq_weightedFiberCard` rewrites it to the count over any `y`, using the `fiberSum_const` field'
  - Because `Classical.arbitrary` returns the same point every time
  - Because the fibre over the chosen point is always unramified
  answer: 0
  explain: 'Jacobian/HolomorphicForms/BranchedCover.lean lines 173–178 proves `branchedDegree h = h.weightedFiberCard y` for every `y`, directly from the structure field.'
- q: 'What does `weightedFiberCard h y` add up?'
  type: choice
  choices:
  - The number of points in the fibre over `y`
  - The ramification indices of all the preimages of `y`
  - The ramification indices of all the ramified points of `X`
  answer: 1
  explain: 'It is `((h.finite_fiber y).toFinset).sum h.ramificationIndex` (Jacobian/HolomorphicForms/BranchedCover.lean lines 152–155). It coincides with the plain count only on an unramified fibre.'
- q: Does the file prove that a nonconstant map has positive degree?
  type: choice
  choices:
  - 'Yes, unconditionally'
  - 'Only under an explicit surjectivity hypothesis (`branchedDegree_pos`)'
  - 'No, degree is always 0 for data built this way'
  answer: 1
  explain: '`branchedDegree_pos` at Jacobian/HolomorphicForms/BranchedCover.lean lines 197–208 takes `hsurj : Function.Surjective f` as an argument.'
---
## Plain English

Given a package of branched-cover facts ([BranchedCoverData](#/node/HolomorphicForms.BranchedCoverData)), the degree ought to be "the number of preimages of a point, counted with multiplicity". The catch is that you have to name a point to count over.

The Lean does the blunt thing. It takes `Classical.arbitrary Y` — an unnamed point of `Y`, produced from the bare assumption that `Y` is nonempty — and returns the weighted fibre count there:

```
branchedDegree h = h.weightedFiberCard (Classical.arbitrary Y)
```

and `weightedFiberCard h y` is the sum of `ramificationIndex x` over the finitely many `x` with `f x = y` (Jacobian/HolomorphicForms/BranchedCover.lean lines 152–155).

That looks reckless, and it would be if the structure did not already carry `fiberSum_const`, the assumption that this weighted sum is the same over every point of `Y`. Because it does, `branchedDegree_eq_weightedFiberCard` (Jacobian/HolomorphicForms/BranchedCover.lean lines 173–178) immediately upgrades the definition: for *any* `y : Y`, `branchedDegree h = h.weightedFiberCard y`. The file tells downstream code to use that rewrite and never unfold the `Classical.arbitrary` choice (Jacobian/HolomorphicForms/BranchedCover.lean lines 20–24).

## Why it is defined this way

Defining a degree properly would mean first proving that the weighted fibre count is constant — which requires the open mapping theorem and the local normal form of a holomorphic map. Putting the constancy in the structure lets the combinatorial half of the theory be written and proved first, with the analytic half supplied later by [branchedCoverData_of_nonconstant_holomorphic](#/node/Blueprint.branchedCoverData_of_nonconstant_holomorphic).

## What it does and does not give you

Positive results that follow immediately: a degree-one cover has exactly one preimage over every point and it is unramified (`branchedDegree_one_fiber_unique`, Jacobian/HolomorphicForms/BranchedCover.lean lines 272–286), hence `f` is a bijection (`degree_one_bijective`, Jacobian/HolomorphicForms/BranchedCover.lean lines 316–340). On a fibre with no ramification the degree is the plain number of points (Jacobian/HolomorphicForms/BranchedCover.lean lines 216–230).

What is *not* here: positivity. `branchedDegree_pos` (Jacobian/HolomorphicForms/BranchedCover.lean lines 197–208) assumes `f` is surjective. That hypothesis is not vacuous bookkeeping in the structure itself — `fiberSum_const` equates all fibre sums including empty ones, so a map missing a point of `Y` could carry data only if every fibre were empty — but the public [ContMDiff.degree](#/node/ContMDiff.degree) inherits the gap: it returns the weighted fibre count, and no theorem on that path says the count is nonzero for a nonconstant map.
