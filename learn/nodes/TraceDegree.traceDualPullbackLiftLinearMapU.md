---
id: TraceDegree.traceDualPullbackLiftLinearMapU
title: A name for the same map
summary: 'This declaration has no mathematical content at all: its body is just `traceDualPullbackLiftU f hf`, kept to match a naming convention from a file that has been retired out of the build.'
review: draft
authors:
- claude
caveats:
- 'This is a definitional alias, not a new construction. The docstring says so: "alias for `traceDualPullbackLiftU`, mirroring the Type-0 `traceDualPullbackLiftLinearMap`". That declaration lived in `PullbackBasis.lean`, which the module docstring describes as "retired; now `Attic/FalseGaps/PullbackBasis.lean`, not built", so inside the built library the alias mirrors nothing.'
- 'Every caveat on [traceDualPullbackLiftU](#/node/TraceDegree.traceDualPullbackLiftU) applies verbatim, including the non-canonical basis and the `Classical.choose`-selected trace form upstream.'
quiz:
- q: 'What does `traceDualPullbackLiftLinearMapU f hf` compute?'
  type: choice
  choices:
  - 'A different dual map, using a different basis'
  - 'Exactly `traceDualPullbackLiftU f hf`'
  - 'The composition of pullback and pushforward'
  answer: 1
  explain: 'The body in `Jacobian/TraceDegree/PullbackTraceLiftU.lean` lines 77–80 is literally `traceDualPullbackLiftU f hf`.'
- q: 'Why does this alias exist?'
  type: choice
  choices:
  - 'To match a naming convention from the earlier Type-0 version of the layer'
  - 'To add continuity to the map'
  - 'To change the universe of the map'
  answer: 0
  explain: 'The docstring states it mirrors the Type-0 `traceDualPullbackLiftLinearMap`; continuity is added separately by [traceDualPullbackLiftCLMU](#/node/TraceDegree.traceDualPullbackLiftCLMU).'
- q: 'Is anything proved about this declaration?'
  type: choice
  choices:
  - 'Yes, that it preserves the period lattice'
  - 'Yes, that it is continuous'
  - 'No, it is a `noncomputable def` with no accompanying lemma of its own'
  answer: 2
  explain: 'Lattice preservation is stated about the continuous version in `Jacobian/TraceDegree/AnalyticPullbackU.lean` lines 65–91, not here.'
---
## Plain English

`traceDualPullbackLiftLinearMapU f hf` is defined to be `traceDualPullbackLiftU f hf` (`Jacobian/TraceDegree/PullbackTraceLiftU.lean` lines 77–80). Same type, same value, different name.

The reason is bookkeeping. According to the module docstring, an earlier version of this layer worked only for surfaces in universe 0 and gave the transposed trace map two names, a raw one and a `…LinearMap` one. When the layer was rewritten for arbitrary universes, both names were carried across. The earlier version has since been retired to `Attic/FalseGaps/PullbackBasis.lean` and is not built, so the convention being matched no longer exists in the library.

If you are reading the chain of definitions, you can skip this step. The real content is in [traceDualPullbackLiftU](#/node/TraceDegree.traceDualPullbackLiftU): the matrix transpose of the trace of holomorphic 1-forms in basis coordinates, which is the ambient version of the Jacobian pullback.

## How it is used

Exactly once, as the argument to [traceDualPullbackLiftCLMU](#/node/TraceDegree.traceDualPullbackLiftCLMU), which bundles it as a continuous ℂ-linear map so it can be pushed through the period-lattice quotient.
