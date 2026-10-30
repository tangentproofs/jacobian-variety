---
id: Jacobian.instAddCommGroup
title: Adding points of the Jacobian
summary: The group law is not constructed; it is the addition of ℂ^g read through the quotient and the ULift wrapper, found by instance search in one line.
review: draft
authors:
- claude
caveats:
- 'The instance is anonymous in the source — `noncomputable instance : AddCommGroup (Jacobian X) := inferInstanceAs (AddCommGroup (ULift _))` at Jacobian/Solution.lean line 94. The id used on this site, `Jacobian.instAddCommGroup`, is the name Lean generates for it; it is recorded in `comparator/jacobian.json`, which checks this definition against the frozen spec.'
- 'Nothing is proved here. `inferInstanceAs` asks Lean to find an instance for a type it already knows, so this line only certifies that unfolding [Jacobian](#/node/Jacobian) reaches a type with a known `AddCommGroup`.'
- 'It is marked `noncomputable`, which is incidental: the data it points at is the quotient group structure, and `Jacobian` itself is noncomputable through the chosen period lattice.'
- 'The group is additive and commutative, nothing more. No ℂ-action, no ring structure, and in particular no claim that the Jacobian is an abelian *variety* — that would need a projective embedding, which this repository does not build.'
quiz:
- q: Where does the addition on `Jacobian X` come from?
  type: choice
  choices:
  - Addition in ℂ^g, descended to the quotient by the period lattice, then transported through `ULift`
  - A group law defined by the Abel–Jacobi map
  - A chart-by-chart construction
  answer: 0
  explain: Jacobian/Solution.lean line 94 is `inferInstanceAs (AddCommGroup (ULift _))`, which resolves to Mathlib's `ULift` instance over `quotient_addCommGroup` at Jacobian/ComplexTorus/Defs.lean lines 76–77.
- q: What does `inferInstanceAs` do in this line?
  type: choice
  choices:
  - Asks Lean to locate an existing instance for an equivalent presentation of the type, proving nothing new
  - Constructs the group axioms from scratch
  - Declares the group structure as an axiom
  answer: 0
  explain: '`inferInstanceAs (AddCommGroup (ULift _))` triggers ordinary instance search; the group axioms were already discharged by Mathlib for quotient groups and for `ULift`.'
- q: Does this instance say the Jacobian is an abelian variety?
  type: choice
  choices:
  - No; it provides an additive commutative group, and nothing about projective embeddings
  - Yes, that is what `AddCommGroup` means for a torus
  - Yes, together with `CompactSpace`
  answer: 0
  explain: The instance at Jacobian/Solution.lean line 94 is only `AddCommGroup (Jacobian X)`. Nothing in Jacobian/Challenge.lean or Jacobian/Solution.lean mentions projective space or algebraicity.
- q: In classical terms, what does adding two Jacobian points amount to?
  type: choice
  choices:
  - Adding the two tuples of period integrals coordinatewise, and reading the result modulo the period lattice
  - Concatenating the two paths used to define them
  - Multiplying the corresponding divisors
  answer: 0
  explain: Points of `Jacobian X` are classes of vectors in `Fin (genus X) → ℂ` (Jacobian/Solution.lean lines 76–79), and the group law is the quotient of coordinatewise addition.
---
## Plain English

The challenge specification asks for the Jacobian to be an additive commutative group, and marks that requirement "data" — it is part of the structure, not a theorem about it (Jacobian/Challenge.lean lines 64–66).

In the solution it costs one line (Jacobian/Solution.lean line 94):

```
noncomputable instance : AddCommGroup (Jacobian X) := inferInstanceAs (AddCommGroup (ULift _))
```

`inferInstanceAs` is Lean's way of saying "this type is, after unfolding, a type you already know how to handle; go find the instance". Since `Jacobian X` unfolds to a `ULift` of a quotient group, Lean composes Mathlib's `ULift` group instance with the quotient-group instance from the torus layer (Jacobian/ComplexTorus/Defs.lean lines 76–77). Nothing is checked by hand.

## What the group law is

Concretely: a point of the Jacobian is a tuple of `g` complex numbers, considered up to adding a period vector. Two points add by adding their tuples. The sum is well defined because the period lattice is a subgroup — if you change either representative by a period, the sum changes by a period.

This is the structure that makes the Abel–Jacobi story work. Integrals add when you concatenate chains — that is `periodVector_append` (Jacobian/Periods/GenuinePeriodLattice.lean lines 67–70) — so going from `P` to `Q` and then from `Q` to `R` adds in the group. It is also what [pushforward](#/node/Jacobian.pushforward) and [pullback](#/node/Jacobian.pullback) have to respect: both are typed as continuous additive homomorphisms, so additivity is part of their statement rather than a separate lemma.

## What it does not say

An additive commutative group is a weak structure. The Jacobian being *compact* and a *complex Lie group* comes from the neighbouring instances ([CompactSpace](#/node/Jacobian.instCompactSpace), [LieAddGroup](#/node/Jacobian.instLieAddGroupModelWithCornersSelfComplexFinGenusForallComplex)). That it is an abelian variety — a group with a projective algebraic embedding — is not formalized anywhere in this repository and must not be inferred from this line.
