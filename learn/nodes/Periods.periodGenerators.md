---
id: Periods.periodGenerators
title: Periods as differences of two paths
summary: 'Periods are defined as differences of the integrals of two chains with the same endpoints, not as integrals around loops, which makes path-independence modulo periods true by construction.'
review: draft
authors:
- claude
caveats:
- 'The English "integral over the closed curve l₁ then l₂ backwards" is a reading, not a Lean statement. No reversal or concatenation of `l₁` with a reverse of `l₂` is constructed anywhere, and no theorem says that the set of differences equals the set of loop integrals.'
- 'One inclusion is proved: loop integrals are periods, by taking `l₂ = []` (Jacobian/Periods/GenuinePeriodLattice.lean lines 96–100). The reverse inclusion is not stated.'
- 'There is no reference to H₁(X, ℤ) in the Lean here. The file docstring (Jacobian/Periods/GenuinePeriodLattice.lean lines 30–36) notes that classically this subgroup is the image of first homology under integration, and flags it as the classical picture. No theorem in the project proves that identification.'
- 'The set quantifies over all pairs of endpoints P and Q, so it is a union over base points, not a set attached to one base point.'
quiz:
- q: 'Which vectors belong to `periodGenerators X`?'
  type: choice
  choices:
  - 'Integrals of the basis forms over loops based at one fixed point'
  - 'Differences `periodVector l₁ - periodVector l₂` for any two chains `l₁`, `l₂` sharing both endpoints'
  - 'All vectors with integer coordinates'
  answer: 1
  explain: 'The set-builder at Jacobian/Periods/GenuinePeriodLattice.lean lines 72–78 quantifies over P, Q, l₁, l₂ with `IsChain l₁ P Q`, `IsChain l₂ P Q` and `v = periodVector X l₁ - periodVector X l₂`.'
- q: 'How does the Lean see that loop integrals are periods?'
  type: choice
  choices:
  - 'By reversing one of the two chains'
  - 'By taking the second chain to be the empty list'
  - 'It does not; loops are not covered'
  answer: 1
  explain: '`periodVector_mem_of_loop` at Jacobian/Periods/GenuinePeriodLattice.lean lines 96–100 applies the difference construction with the empty chain from P to P, whose period vector is 0.'
- q: 'What does this definitional choice buy?'
  type: choice
  choices:
  - 'That the Abel–Jacobi integral is well defined modulo periods, immediately'
  - 'That the period subgroup is discrete, immediately'
  - 'That the period subgroup has rank 2g, immediately'
  answer: 0
  explain: '`periodVector_sub_mem` at Jacobian/Periods/GenuinePeriodLattice.lean lines 91–94 is a one-liner, `AddSubgroup.subset_closure` applied to the witness, and that is the lemma Abel–Jacobi needs. Discreteness and rank are proved separately and with real work.'
- q: 'Why can this choice not be used to game the construction?'
  type: choice
  choices:
  - 'Because the set of generators is finite'
  - 'Because making the subgroup larger would break the separately proved discreteness'
  - 'Because the definition is checked against H₁(X, ℤ)'
  answer: 1
  explain: 'A too-generous period set would collapse the quotient and contradict `periodLattice_discrete` at Jacobian/Periods/GenuinePeriodLatticeDiscrete.lean lines 21–28, which is proved independently.'
---
## Plain English

Classically a period is the integral of a holomorphic 1-form around a closed loop. The Lean takes a slightly different starting point. A generator of the period lattice is the difference of the [period vectors](#/node/Periods.periodVector) of two [chains](#/node/Periods.IsChain) with the same start and the same end (`Jacobian/Periods/GenuinePeriodLattice.lean` lines 72–78):

  periodGenerators X = { periodVector l₁ − periodVector l₂ : l₁ and l₂ are chains from P to Q }

with P and Q ranging over all of X. Geometrically that difference is the integral around the closed curve that goes out along l₁ and back along l₂, which is why calling these periods is fair. But the Lean does not build that closed curve. It never reverses a chain.

Loops are included as a special case: take l₂ to be the empty chain from P to P, and the difference is the loop integral itself (Jacobian/Periods/GenuinePeriodLattice.lean lines 96–100).

## Why it is defined this way

Phrasing periods as differences makes the central well-definedness fact trivial. "The Abel–Jacobi integral from P to Q does not depend on the path, modulo periods" is exactly the statement `periodVector l₁ − periodVector l₂ ∈ Λ`, and that holds by membership in the generating set (Jacobian/Periods/GenuinePeriodLattice.lean lines 91–94). The proof is one line.

If that were the whole story it would be suspicious: you can always make a quotient well behaved by quotienting by more. The check is that this group must also be small. The project separately proves that the generated subgroup is [discrete](#/node/Periods.genuinePeriodSubgroup_discrete) in ℂ^g, which fails outright if the periods are too plentiful, and that [Abel–Jacobi is injective](#/node/Jacobian.ofCurve) when the genus is positive, which fails if distinct points get identified. Neither follows from the definition. Both are theorems with analytic content.
