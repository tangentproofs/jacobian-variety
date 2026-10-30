---
id: ComplexTorus.quotient
title: The complex torus, as a one-line quotient
summary: The definition is just the quotient group V ⧸ Λ.subgroup; everything that makes it a torus rather than a bare group comes from separate instances, four of them immediately below it and the rest in the chart and manifold files.
review: draft
authors:
- claude
caveats:
- 'Nothing in this definition makes the quotient a *complex* torus. It is an `abbrev` for an additive-group quotient. The group, topology, Hausdorff and compactness instances sit just below it in the same file; the charts, manifold and Lie-group structure live in Jacobian/ComplexTorus/ChartedSpace.lean, Jacobian/ComplexTorus/IsManifold.lean and Jacobian/ComplexTorus/LieAddGroup.lean.'
- 'The quotient is only a quotient of additive groups, not of ℂ-vector spaces. Scalar multiplication by ℂ does not descend (a lattice is not a ℂ-subspace), and the Lean does not claim it does.'
- 'The lattice conditions are not weak: [FullComplexLattice](#/node/ComplexTorus.FullComplexLattice) requires the subgroup to be closed, discrete, and to have a compact fundamental domain whose translates cover `V` (Jacobian/ComplexTorus/Defs.lean lines 57–69). What it does *not* require is `FiniteDimensional ℂ V`, and no field records a rank; "complex torus of dimension g" is earned only once a particular `V` and `Λ` are plugged in.'
quiz:
- q: What is `quotient V Λ`, literally?
  type: choice
  choices:
  - An abbreviation for the additive quotient group `V ⧸ Λ.subgroup`
  - A structure with chart fields
  - A product of circles
  answer: 0
  explain: 'Jacobian/ComplexTorus/Defs.lean line 74 reads `abbrev quotient (Λ : FullComplexLattice V) : Type _ := V ⧸ Λ.subgroup`.'
- q: Which field of the lattice makes the quotient Hausdorff?
  type: choice
  choices:
  - '`isClosed`'
  - '`isDiscrete`'
  - '`fundamentalDomain_isCompact`'
  answer: 0
  explain: '`quotient_t2Space` at Jacobian/ComplexTorus/Defs.lean lines 86–88 introduces `Λ.isClosed` and then lets instance search finish.'
- q: Does the quotient inherit multiplication by complex scalars from `V`?
  type: choice
  choices:
  - No; only the additive group structure is quotiented, and the Lean registers only `AddCommGroup`
  - Yes, it is a ℂ-vector space of dimension g
  - Yes, but only for real scalars
  answer: 0
  explain: The instance at Jacobian/ComplexTorus/Defs.lean lines 76–77 is `AddCommGroup (quotient V Λ)`. No `Module ℂ` instance is declared, and none descends from `V`, because scaling a lattice vector by a complex number leaves the lattice.
- q: Where does compactness of the quotient come from?
  type: choice
  choices:
  - The lattice's compact fundamental domain, pushed forward by the projection, which covers everything
  - Compactness of `V`
  - The discreteness of the lattice
  answer: 0
  explain: '`compactSpace_quotient_of_cover` at Jacobian/ComplexTorus/Defs.lean lines 97–112 shows the image of the compact set `K` under `QuotientAddGroup.mk` is all of the quotient, then uses `hK.image`.'
---
## Plain English

Take a complex vector space `V` and a lattice `Λ` inside it. Glue together any two points of `V` that differ by a lattice vector. What is left is the complex torus. In one complex dimension, `V = ℂ` and `Λ` a grid, this is the classical doughnut: a square with opposite sides identified.

In Lean this is one line (Jacobian/ComplexTorus/Defs.lean line 74):

```
abbrev quotient (Λ : FullComplexLattice V) : Type _ := V ⧸ Λ.subgroup
```

`V ⧸ Λ.subgroup` is Mathlib's quotient of an additive group by a subgroup, with its quotient topology. Written as an `abbrev`, so Lean unfolds it freely and instances found for `V ⧸ Λ.subgroup` apply to `quotient V Λ` without any transport.

## What the surrounding instances add

The definition alone gives a set with a group law. The four instances right after it supply the rest of the torus:

- `quotient_addCommGroup` (Jacobian/ComplexTorus/Defs.lean lines 76–77) — addition, inherited from `V`.
- `quotient_topologicalSpace` (Jacobian/ComplexTorus/Defs.lean lines 79–80) — the quotient topology.
- [quotient_t2Space](#/node/ComplexTorus.quotient_t2Space) (Jacobian/ComplexTorus/Defs.lean lines 86–88) — points are separated, because `Λ.subgroup` is closed.
- [quotient_compactSpace](#/node/ComplexTorus.quotient_compactSpace) (Jacobian/ComplexTorus/Defs.lean lines 118–121) — the torus is compact, because the lattice has a compact fundamental domain whose translates cover `V`.

Charts, analyticity and smoothness of the group law are built in other files, on top of this type.

## Where it is used

`Jacobian X` is this quotient for `V = Fin (genus X) → ℂ`, that is ℂ^g, and `Λ` the period lattice, wrapped in a `ULift` to land in the right universe (Jacobian/Solution.lean lines 76–79). So every statement about a general complex torus in this layer is a statement about the Jacobian once the lattice is specialised. See [Jacobian](#/node/Jacobian).

One caution about reading the name. The definition takes a `Λ` whose three conditions — closed, discrete, compact fundamental domain — already force the quotient to be a compact Hausdorff group with charts, and already prevent it from collapsing to a point when `V` is nonzero. What the definition does not fix is the dimension: `V` is any complex normed space, and the real content of "the Jacobian is a torus of dimension `g`" is in which `V` and which lattice get plugged in.
