---
id: AbelJacobi.chosenChain
title: One path per pair of points, picked arbitrarily
summary: 'For each pair of points the Lean picks a connecting path out of thin air with Classical.choose, with no compatibility at all between the choices made for nearby points.'
review: draft
authors:
- claude
caveats:
- 'This is `Classical.choose` applied to `exists_chain P Q`. Nothing characterises the chosen chain beyond the fact that it is a chain from P to Q (`chosenChain_isChain`, Jacobian/AbelJacobi/PathIntegralFunctionalU.lean lines 40–42).'
- 'There is no continuity, no smallness and no coherence between the choices for different pairs. As Q moves slightly, the chosen chain can change completely.'
- 'The choice makes the definition noncomputable and uses `Classical.choice`. You cannot run it to produce a list of segments; you can only reason about it.'
- 'The existence theorem it draws on needs X connected (Jacobian/Periods/ChartChain.lean lines 280–298), which is why `ConnectedSpace X` is a hypothesis.'
quiz:
- q: 'What does `chosenChain X P Q` give you?'
  type: choice
  choices:
  - 'The shortest chain from P to Q'
  - 'Some chain from P to Q, with no further properties'
  - 'All chains from P to Q'
  answer: 1
  explain: 'At Jacobian/AbelJacobi/PathIntegralFunctionalU.lean lines 36–42 the body is `(exists_chain P Q).choose`, and the only accompanying fact is `chosenChain_isChain`.'
- q: 'Which hypothesis on X makes the choice possible?'
  type: choice
  choices:
  - 'Compactness'
  - 'Connectedness'
  - 'Hausdorffness'
  answer: 1
  explain: '`exists_chain` at Jacobian/Periods/ChartChain.lean lines 280–298 is proved by a clopen argument that needs `ConnectedSpace X`.'
- q: 'Is the map sending Q to `chosenChain X P Q` continuous in any sense?'
  type: choice
  choices:
  - 'Yes, that is proved alongside the definition'
  - 'No such statement exists, and the chains for nearby points are unrelated'
  - 'Yes, because chains are built from chart balls'
  answer: 1
  explain: 'Nothing in Jacobian/AbelJacobi/PathIntegralFunctionalU.lean constrains the choice beyond its endpoints. Continuity of the resulting map only appears after passing to the quotient, in `analyticOfCurve_contMDiffU`.'
- q: 'Why is such a crude choice acceptable here?'
  type: choice
  choices:
  - 'Because only the class of the resulting integral modulo the period lattice is used'
  - 'Because any two chains from P to Q have the same integral'
  - 'Because the chains can be shown to be unique up to reparametrisation'
  answer: 0
  explain: '`pathIntegralFunctionalU_sub_mem` at Jacobian/AbelJacobi/PathIntegralFunctionalU.lean lines 53–60 shows the dependence on the chain is exactly by an element of Λ, and the Abel–Jacobi map only ever uses the class modulo Λ.'
---
## Plain English

To define the Abel–Jacobi map you have to integrate from a base point P to a point Q, which means you need a path. On a connected surface paths exist: [exists_chain](#/node/Periods.exists_chain) proves that any two points are joined by a [chart chain](#/node/Periods.IsChain). But existence is not the same as a choice, and Lean needs a specific chain to compute with.

`chosenChain X P Q` is that specific chain, obtained by applying `Classical.choose` to the existence proof (`Jacobian/AbelJacobi/PathIntegralFunctionalU.lean` lines 36–38). The only thing known about it is that it is a chain from P to Q (Jacobian/AbelJacobi/PathIntegralFunctionalU.lean lines 40–42). It is not the shortest chain, nor a canonical one, nor one that varies nicely with Q. Different pairs of points get chains chosen with no relation to one another.

## Why this is not a problem

It would be a problem if the project needed the integral itself. It does not. The [path integral](#/node/AbelJacobi.pathIntegralFunctionalU) built from this chain is only ever used modulo the [period lattice](#/node/Periods.genuinePeriodSubgroup), and by the way the lattice was defined, any two chains with the same endpoints give integrals differing by a lattice element (Jacobian/AbelJacobi/PathIntegralFunctionalU.lean lines 53–60). The arbitrariness is quotiented away.

There is also a reason not to hope for a nicer choice. The file's history note (Jacobian/AbelJacobi/PathIntegralFunctionalU.lean lines 17–22) records that an earlier version of this code declared the path integral `opaque`, over a specification demanding that `Q ↦ ∫_P^Q ω` be smooth. No genuine integral can satisfy that when the genus is at least 1, because a single-valued holomorphic map from a compact surface into ℂ^g is constant; the only thing satisfying the specification was the zero function. Replacing it with an honest `Classical.choose` is what unblocked the construction.
