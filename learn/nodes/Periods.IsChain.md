---
id: Periods.IsChain
title: When a list of segments is a path
summary: 'A path from P to Q is just a list of chart segments whose endpoints match up, with the empty list counting as a path from P to P.'
review: draft
authors:
- claude
caveats:
- 'A chain carries no parametrisation and no continuity data. It is a list, and `IsChain` is a statement about equalities of points of X.'
- 'There is no reversal operation on chains in this file. To go backwards you build a new list with `a` and `b` swapped in each segment, as `exists_nhds_chain` does for a single segment at Jacobian/Periods/ChartChain.lean lines 263–276.'
- 'The gluing condition is exact equality of points in X, not "the endpoints are close" or "there is an overlap".'
- 'Order matters: `IsChain` recurses down the list, so a chain is directed from P to Q.'
quiz:
- q: 'When does `IsChain [] P Q` hold?'
  type: choice
  choices:
  - 'Never, since an empty list is not a path'
  - 'Exactly when P and Q are equal'
  - 'Always, for any P and Q'
  answer: 1
  explain: 'The first branch of the definition at Jacobian/Periods/ChartChain.lean lines 213–215 is `[], P, Q => P = Q`.'
- q: 'For a non-empty chain `s :: l` from P to Q, what does the definition require?'
  type: choice
  choices:
  - 'That `s.start = P` and that `l` is a chain from `s.stop` to Q'
  - 'That `s.start = P` and `s.stop = Q`, with `l` unconstrained'
  - 'That every segment in the list uses the same chart'
  answer: 0
  explain: 'The second branch at Jacobian/Periods/ChartChain.lean lines 213–215 is `s :: l, P, Q => s.start = P ∧ IsChain l s.stop Q`, which chains the condition down the list.'
- q: 'Do all segments of one chain have to live in the same chart?'
  type: choice
  choices:
  - 'Yes, the chart is fixed for the whole chain'
  - 'No, each segment carries its own point `p` and therefore its own chart'
  - 'Yes, unless the chain is empty'
  answer: 1
  explain: 'Each `ChartSegment` has its own field `p` (Jacobian/Periods/ChartChain.lean lines 143–156), and `IsChain` only compares `start` and `stop`, which are points of X, so charts may change from one segment to the next.'
- q: 'What does `exists_chain` add on a connected surface?'
  type: choice
  choices:
  - 'That any two points are joined by some chart chain'
  - 'That any two points are joined by a unique chart chain'
  - 'That any two points are joined by a chain of at most two segments'
  answer: 0
  explain: 'Jacobian/Periods/ChartChain.lean lines 280–298 prove existence only, by showing that the set of points reachable from P is open, closed and non-empty, hence everything.'
---
## Plain English

[Chart segments](#/node/Periods.ChartSegment) are the atoms. `IsChain` says how to glue them into something that behaves like a path.

The definition is a two-line recursion (`Jacobian/Periods/ChartChain.lean` lines 213–215). The empty list is a chain from P to Q exactly when P and Q are the same point. A list `s :: l` is a chain from P to Q when the first segment starts at P, and the rest of the list is a chain from where that segment stopped to Q. Unfolding, a chain is a list whose segments match end to end, starting at P and finishing at Q.

Two things are worth noticing. First, each segment carries its own chart, so a chain can walk across many charts; only the points of X where consecutive segments meet have to agree. Second, a chain has no parametrisation at all. It is a finite list. There is no map out of an interval anywhere in the construction, which is precisely why this combinatorial stand-in is easier to work with than an honest piecewise-smooth path.

## What is proved about chains

Chains concatenate: if `l₁` runs from P to Q and `l₂` from Q to R, then the list append `l₁ ++ l₂` runs from P to R (Jacobian/Periods/ChartChain.lean lines 222–226). That one lemma, plus a local statement that every point has a neighbourhood whose points are joined to it in both directions (Jacobian/Periods/ChartChain.lean lines 263–276), gives [exists_chain](#/node/Periods.exists_chain): on a connected surface any two points are joined by a chain (Jacobian/Periods/ChartChain.lean lines 280–298). The proof is the standard clopen argument, and it is why connectedness of X appears as a hypothesis later on.

There is deliberately no uniqueness. Many chains join P to Q, and the whole point of the [period lattice](#/node/Periods.genuinePeriodSubgroup) is to measure by how much their integrals can differ.
