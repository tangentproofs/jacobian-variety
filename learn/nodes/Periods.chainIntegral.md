---
id: Periods.chainIntegral
title: Integrating a form along a chain
summary: 'The integral along a chain is literally a finite sum of chart-side segment integrals, and it is defined for any list of segments, whether or not the segments glue together.'
review: draft
authors:
- claude
caveats:
- '`chainIntegral` takes an arbitrary `List (ChartSegment X)`. It does not require `IsChain`, so it also assigns a number to lists whose segments do not meet. The gluing condition only enters in the lemmas that use it.'
- 'No invariance theorem is proved here. The Lean does not state that two different chains tracing the same curve, or a chain and a subdivision of it, give the same number. What is proved instead is that two chains with the same endpoints have period vectors differing by a period, in Jacobian/Periods/GenuinePeriodLattice.lean lines 91–94.'
- 'The value depends on the chart choices recorded inside each segment, not only on the curve in X.'
quiz:
- q: 'How is `chainIntegral ω l` computed?'
  type: choice
  choices:
  - 'As the sum of the segment integrals of the segments in `l`'
  - 'As a limit of Riemann sums along a parametrisation of the chain'
  - 'As the difference of a global primitive at the two ends of the chain'
  answer: 0
  explain: 'The definition at Jacobian/Periods/ChartChain.lean lines 229–230 is `(l.map fun s => s.integral ω).sum`, a plain list sum.'
- q: 'Does `chainIntegral` require its list to be a chain?'
  type: choice
  choices:
  - 'Yes, the hypothesis `IsChain l P Q` is part of the definition'
  - 'No, it is defined for every list of segments'
  - 'Only when the list is non-empty'
  answer: 1
  explain: 'The definition at Jacobian/Periods/ChartChain.lean lines 229–230 takes `l : List (ChartSegment X)` with no gluing hypothesis. `IsChain` is a separate predicate at Jacobian/Periods/ChartChain.lean lines 213–215.'
- q: 'In which variables is the chain integral additive?'
  type: choice
  choices:
  - 'Only in the form ω'
  - 'Only in the chain'
  - 'In both: list append adds the integrals, and the integral is ℂ-linear in ω'
  answer: 2
  explain: '`chainIntegral_append` at Jacobian/Periods/ChartChain.lean lines 235–237 gives additivity in the chain, and `chainIntegralLM` at Jacobian/Periods/ChartChain.lean lines 245–256 bundles ω-linearity as a linear map.'
- q: 'What is `chainIntegral ω []`?'
  type: choice
  choices:
  - 'Zero'
  - 'Undefined'
  - 'The value of ω at the base point'
  answer: 0
  explain: '`chainIntegral_nil` at Jacobian/Periods/ChartChain.lean lines 232–233 proves it is 0, by `rfl`, since the sum over an empty list is 0.'
---
## Plain English

Given a holomorphic 1-form ω and a list of [chart segments](#/node/Periods.ChartSegment), `chainIntegral ω l` is the sum of the segment integrals (`Jacobian/Periods/ChartChain.lean` lines 229–230). Each term is a curve integral in ℂ of the chart reading of ω along a straight line, so the whole thing is a finite sum of ordinary one-variable integrals. This is the classical ∫ ω(γ(t))(γ'(t)) dt, written out chart by chart.

Two formal properties carry the weight downstream.

Appending lists adds integrals: `chainIntegral ω (l₁ ++ l₂) = chainIntegral ω l₁ + chainIntegral ω l₂` (Jacobian/Periods/ChartChain.lean lines 235–237). Since appending lists is how chains are concatenated ([IsChain.append](#/node/Periods.IsChain), Jacobian/Periods/ChartChain.lean lines 222–226), this is the usual "integral over a concatenated path" rule, and it is true by list arithmetic alone.

The integral is ℂ-linear in the form. This is packaged as [chainIntegralLM](#/node/Periods.chainIntegralLM) (Jacobian/Periods/ChartChain.lean lines 245–256), a linear map from holomorphic 1-forms to ℂ. That is the right way to see a chain: it is a linear functional on H⁰(X, Ω¹). Reading that functional in a chosen basis of forms is what produces the [period vector](#/node/Periods.periodVector) in ℂ^g.

## What is not claimed

The definition is attached to the list, not to a curve. Nothing in this file says that two lists describing the same geometric curve give the same number, and nothing says that subdividing a segment leaves the value alone. The project does not need those statements. It needs only that two chains with the same two endpoints differ by an element of the [period lattice](#/node/Periods.genuinePeriodSubgroup), and the lattice is defined so that this holds immediately.
