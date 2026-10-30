---
id: Periods.genuinePeriodLattice
title: Bundling Λ as a full lattice
summary: 'The bundle carries a chosen compact set whose translates cover ℂ^g, so "fundamental domain" here means covering only, not tiling without overlap.'
review: draft
authors:
- claude
caveats:
- 'The `fundamentalDomain` field is picked by `Classical.choose` from an existence theorem, so the set itself is not pinned down (Jacobian/Periods/GenuinePeriodLatticeDiscrete.lean lines 85–87).'
- '`fundamentalDomain_covers` only says every vector is congruent modulo Λ to a point of D. It does not say the translates are disjoint, so D is not a strict fundamental domain. The witness used, the closure of a parallelepiped, really does overlap its translates on the boundary.'
- 'The structure `FullComplexLattice` (Jacobian/ComplexTorus/Defs.lean lines 57–69) demands that the subgroup be closed and discrete and come with a compact set whose translates cover the space. What it does not have is a field asserting that the subgroup spans. Fullness is carried indirectly, by the compact covering set; the span theorem is still needed, and is used to get the ℤ-basis that builds D.'
- 'Everything lives in the basis-aligned ℂ^g, which depends on the arbitrary chosen basis of holomorphic 1-forms.'
quiz:
- q: 'What does the `fundamentalDomain_covers` field actually assert?'
  type: choice
  choices:
  - 'That the Λ-translates of D tile ℂ^g with no overlap'
  - 'That for every v there is some g in Λ with v - g in D'
  - 'That D is a single parallelepiped'
  answer: 1
  explain: 'The field at Jacobian/ComplexTorus/Defs.lean lines 65–69 is `∀ v : V, ∃ g ∈ subgroup, v - g ∈ fundamentalDomain`. Nothing about uniqueness.'
- q: 'How is the compact covering set produced?'
  type: choice
  choices:
  - 'As the closed unit ball of ℂ^g'
  - 'As the closure of the parallelepiped spanned by a chosen ℤ-basis of Λ'
  - 'As the image of a compact fundamental domain on X'
  answer: 1
  explain: '`exists_compact_genuinePeriodFundamentalDomain` at Jacobian/Periods/GenuinePeriodLatticeDiscrete.lean lines 50–72 takes `Module.Free.chooseBasis` of Λ as a ℤ-module, forms `ZSpan.fundamentalDomain`, and takes its closure, which is compact because the parallelepiped is bounded.'
- q: 'Where does closedness of Λ in ℂ^g come from?'
  type: choice
  choices:
  - 'From compactness of X'
  - 'From discreteness, via `AddSubgroup.isClosed_of_discrete`'
  - 'It is assumed as a separate classical input'
  answer: 1
  explain: 'Line 83 of Jacobian/Periods/GenuinePeriodLatticeDiscrete.lean fills the `isClosed` field with `AddSubgroup.isClosed_of_discrete`.'
- q: 'What does the bundle buy immediately?'
  type: choice
  choices:
  - 'That the quotient ℂ^g/Λ is Hausdorff and compact'
  - 'That the quotient is a projective algebraic variety'
  - 'That the quotient is isomorphic to a product of circles as a complex manifold'
  answer: 0
  explain: 'The instances at Jacobian/ComplexTorus/Defs.lean lines 82–121 derive T2 from `isClosed` and `CompactSpace` from the compact covering set. Projectivity is never claimed anywhere in the project.'
---
## Plain English

[Λ](#/node/Periods.genuinePeriodSubgroup) is discrete and spans ℂ^g over ℝ. To hand it to the complex-torus machinery, those facts have to be packaged in the shape that machinery expects, which is [FullComplexLattice](#/node/ComplexTorus.FullComplexLattice). This definition does the packaging (`Jacobian/Periods/GenuinePeriodLatticeDiscrete.lean` lines 74–87).

The six fields get filled as follows:

- `subgroup` is Λ itself;
- `isDiscrete` is the [discreteness instance](#/node/Periods.genuinePeriodSubgroup_discrete);
- `isClosed` follows from discreteness, by a Mathlib lemma (Jacobian/Periods/GenuinePeriodLatticeDiscrete.lean line 83);
- `fundamentalDomain`, with its compactness and covering proofs, comes from an existence theorem at Jacobian/Periods/GenuinePeriodLatticeDiscrete.lean lines 50–72, read off with `Classical.choose`.

That existence theorem is where the span result is used. Because Λ is discrete and spans, Mathlib recognises it as a ℤ-lattice (Jacobian/Periods/GenuinePeriodLatticeDiscrete.lean lines 44–48), hence free and finitely generated. Choose a ℤ-basis, form the parallelepiped it spans, take its closure: that is a compact set, and the floor function for the lattice shows every vector is congruent to a point of it.

## Reading the name honestly

Two words in this bundle promise more than the Lean delivers, and both are harmless once you know.

"Fundamental domain" classically means a set that meets each orbit exactly once. The field only says the translates cover (`Jacobian/ComplexTorus/Defs.lean` lines 65–69). The set chosen here, a closed parallelepiped, overlaps its own translates along faces. That is fine, because the only use of the field is to prove the quotient compact, and covering is all that needs (Jacobian/ComplexTorus/Defs.lean lines 114–121).

"Full" is not a field either. The structure has no span condition. In a finite-dimensional space, discrete plus cocompact forces full rank, so the content is there, but it is carried by the compact covering set rather than stated.
