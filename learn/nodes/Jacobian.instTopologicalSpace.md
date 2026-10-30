---
id: Jacobian.instTopologicalSpace
title: The topology on the Jacobian
summary: The topology is the quotient topology of ℂ^g, inherited for free, and it is the only topology on the Jacobian that any later theorem is allowed to use.
review: draft
authors:
- claude
caveats:
- 'The instance is anonymous in the source — `noncomputable instance : TopologicalSpace (Jacobian X) := inferInstanceAs (TopologicalSpace (ULift _))` at Jacobian/Solution.lean line 95. The id used on this site, `Jacobian.instTopologicalSpace`, is the name Lean generates for it; it is recorded in `comparator/jacobian.json`.'
- 'Nothing is proved. The line certifies that `Jacobian X` unfolds to a type Lean already topologizes.'
- 'The challenge marks this requirement "data" (Jacobian/Challenge.lean lines 68–70), so a hack answer could in principle have supplied any topology at all. What rules that out is not this instance but the ones after it: Hausdorff, compact, and charted on ℂ^g.'
quiz:
- q: Which topology does `Jacobian X` carry?
  type: choice
  choices:
  - The quotient topology from ℂ^g, transported through `ULift`
  - The discrete topology
  - The topology induced by a metric chosen with `Classical.choice`
  answer: 0
  explain: Jacobian/Solution.lean line 95 resolves to Mathlib's `ULift` topology over `quotient_topologicalSpace` at Jacobian/ComplexTorus/Defs.lean lines 79–80, which is the quotient topology on `V ⧸ Λ.subgroup`.
- q: Why is a bare `TopologicalSpace` instance not enough to rule out a fake Jacobian?
  type: choice
  choices:
  - Because any type admits topologies; the content is in the Hausdorff, compactness and charted-space instances that follow
  - Because `TopologicalSpace` is a `Prop`
  - Because the topology is not used anywhere
  answer: 0
  explain: Jacobian/Challenge.lean line 68 marks it `-- data`. The constraining declarations are the `T2Space`, `CompactSpace`, `ChartedSpace`, `IsManifold` and `LieAddGroup` instances at Jacobian/Challenge.lean lines 73–87.
- q: What makes the quotient topology the right choice here?
  type: choice
  choices:
  - It is the topology for which the projection from ℂ^g is continuous and open, which is what the chart construction needs
  - It is the coarsest topology on any set
  - It makes the Jacobian discrete, simplifying proofs
  answer: 0
  explain: The torus layer proves [mk_continuous](#/node/ComplexTorus.mk_continuous) and [mk_isOpenMap](#/node/ComplexTorus.mk_isOpenMap) for this topology (Jacobian/ComplexTorus/Basic.lean lines 16–17 and 24–25), and the charts at Jacobian/ComplexTorus/Chart.lean lines 29–45 use `mk_image_isOpen` for their open source.
---
## Plain English

A point of the Jacobian is a tuple in ℂ^g taken modulo the period lattice. Two Jacobian points are close when you can choose representatives in ℂ^g that are close. That is the quotient topology, and it is what the Lean uses.

The line is (Jacobian/Solution.lean line 95):

```
noncomputable instance : TopologicalSpace (Jacobian X) := inferInstanceAs (TopologicalSpace (ULift _))
```

Lean unfolds [Jacobian](#/node/Jacobian) to a `ULift` of the torus quotient, finds Mathlib's topology on a `ULift`, which sits over the quotient topology from the torus layer (Jacobian/ComplexTorus/Defs.lean lines 79–80), and is done.

## Why this topology and not another

The specification asks only for *some* topology. What makes this one load-bearing is everything built on it. Two properties of the quotient projection matter:

- it is an open map, so the image of a small ball in ℂ^g is an open neighbourhood in the Jacobian — this is what makes the charts open (Jacobian/ComplexTorus/Chart.lean lines 29–45);
- it is not merely continuous but analytic for the resulting manifold structure, `contMDiff_mk` (Jacobian/ComplexTorus/MkSmooth.lean line 32) — this is what lets [ofCurve](#/node/Jacobian.ofCurve) and the group law be smooth.

Once the topology is fixed, the surrounding instances can say something real about it: the Jacobian is Hausdorff because the lattice is closed, compact because the lattice has a compact fundamental domain, and locally modelled on ℂ^g because the lattice is discrete. Those are the [T2Space](#/node/Jacobian.instT2Space), [CompactSpace](#/node/Jacobian.instCompactSpace) and [ChartedSpace](#/node/Jacobian.instChartedSpaceForallFinGenusComplex) instances.
