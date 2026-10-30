---
id: Jacobian.instCompactSpace
title: The Jacobian is compact
summary: Compactness follows from a chosen compact fundamental domain whose translates cover ℂ^g, and that domain is produced by Classical.choose from an existence proof.
review: draft
authors:
- claude
caveats:
- 'The instance is anonymous in the source — `instance : CompactSpace (Jacobian X) := inferInstanceAs (CompactSpace (ULift _))` at Jacobian/Solution.lean line 97. The id used on this site is the name Lean is expected to generate, not a name written in the file.'
- 'This instance is not listed in `comparator/jacobian.json` and does not occur in any checked statement, so the harness that compares the solution with the frozen spec does not certify it. The proof is real; it is just checked by reading.'
- 'The fundamental domain is a *chosen* set. `genuinePeriodLattice` fills the field with `(exists_compact_genuinePeriodFundamentalDomain X).choose` (Jacobian/Periods/GenuinePeriodLatticeDiscrete.lean lines 85–87), and the existence proof itself picks a ℤ-basis of the lattice by `Module.Free.chooseBasis` (Jacobian/Periods/GenuinePeriodLatticeDiscrete.lean line 60). So the domain is some closed parallelepiped, not a canonical one.'
- 'The covering condition in the lattice bundle is "every `v` has a lattice element `g` with `v - g` in the domain" (Jacobian/ComplexTorus/Defs.lean lines 68–69). It does not say the translates are disjoint, so "fundamental domain" is used loosely: it is a compact set of representatives, possibly overlapping.'
quiz:
- q: What makes the Jacobian compact?
  type: choice
  choices:
  - The period lattice has a compact set whose translates cover ℂ^g, and the quotient is its continuous image
  - ℂ^g is compact
  - The period lattice is finite
  answer: 0
  explain: '`compactSpace_quotient_of_cover` at Jacobian/ComplexTorus/Defs.lean lines 97–112 shows the image of `K` under the projection is all of the quotient, then applies `hK.image`.'
- q: How is the compact fundamental domain for the period lattice obtained?
  type: choice
  choices:
  - As the closure of the parallelepiped spanned by a chosen ℤ-basis of the lattice
  - As a chart domain on the surface
  - As the unit ball of ℂ^g
  answer: 0
  explain: Jacobian/Periods/GenuinePeriodLatticeDiscrete.lean lines 60–63 take `Module.Free.chooseBasis`, convert it to an ℝ-basis, and use `closure (ZSpan.fundamentalDomain bR)`.
- q: Does the Lean require the translates of the fundamental domain to be disjoint?
  type: choice
  choices:
  - No; the field only asks that every vector lands in some translate
  - Yes, the field states a partition
  - Yes, disjointness is proved separately
  answer: 0
  explain: '`fundamentalDomain_covers` at Jacobian/ComplexTorus/Defs.lean lines 68–69 reads `∀ v : V, ∃ g ∈ subgroup, v - g ∈ fundamentalDomain`, an existence statement with no uniqueness.'
- q: Why does the existence of a ℤ-basis of the period lattice need the spanning theorem?
  type: choice
  choices:
  - Because the ZLattice machinery that yields a free finite basis is applied to a discrete subgroup whose ℝ-span is everything
  - Because every subgroup of ℂ^g is free
  - Because the genus is finite
  answer: 0
  explain: Jacobian/Periods/GenuinePeriodLatticeDiscrete.lean lines 47–48 register `IsZLattice ℝ (genuinePeriodSubmodule X)` with `span_top` from [periodLattice_span](#/node/Periods.periodLattice_span), and Jacobian/Periods/GenuinePeriodLatticeDiscrete.lean lines 58–59 then invoke `ZLattice.module_free` and `ZLattice.module_finite`.
---
## Plain English

A torus is compact: it is a bounded square with its edges glued, and gluing does not add room. The same argument works in ℂ^g. If you can find one compact chunk `K` of ℂ^g such that every vector differs from something in `K` by a lattice vector, then the projection maps `K` onto the whole quotient. A continuous image of a compact set is compact, so the quotient is compact.

That is exactly the proof in the Lean (Jacobian/ComplexTorus/Defs.lean lines 97–112): show `mk '' K = Set.univ`, then apply `hK.image`. The lattice bundle carries `K` as a field, so the instance for the Jacobian is one line (Jacobian/Solution.lean line 97).

## Where the chunk comes from

For the period lattice the chunk has to be produced. The argument runs (Jacobian/Periods/GenuinePeriodLatticeDiscrete.lean lines 38–72):

1. View the period subgroup as a ℤ-submodule of ℂ^g.
2. It is discrete and spans ℂ^g over ℝ, so it is a `ZLattice` — Mathlib's notion of a lattice of full rank.
3. A `ZLattice` is free and finite over ℤ, so it has a ℤ-basis. Pick one.
4. That basis spans a parallelepiped. Its closure is bounded and closed, hence compact, and `ZSpan.floor`/`ZSpan.fract` show every vector is congruent to a point of it.

Steps 3 and 4 both use choice: the basis is whatever `Module.Free.chooseBasis` returns, and the lattice bundle then stores the domain as `(…).choose` of the existence theorem. Nothing canonical is selected, which is fine — compactness does not depend on which domain you use.

## Why it matters

Compactness is part of one of the challenge's anti-hack requirements: together with the complex charts and the smooth group law it forces the Jacobian to be torus-like, a compact complex Lie group. A hack answer like "the Jacobian is ℂ^g" would satisfy the group and manifold requirements but fail here.
