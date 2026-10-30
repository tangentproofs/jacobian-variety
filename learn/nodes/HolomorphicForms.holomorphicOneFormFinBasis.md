---
id: HolomorphicForms.holomorphicOneFormFinBasis
title: A chosen basis of holomorphic 1-forms
summary: The basis ω₁, …, ω_g that puts coordinates on the Jacobian is not canonical; it comes out of the axiom of choice, and no normalization condition is imposed on it.
review: draft
authors:
- claude
caveats:
- 'This is an arbitrary basis, obtained from `Module.finBasis`, which calls `Module.Free.chooseBasis`, which uses `Classical.choice`. No property distinguishes it. It is not a normalized basis with respect to a symplectic basis of H₁(X, ℤ), and no such normalization appears anywhere near this declaration.'
- 'Because the basis is a choice, everything built on it is too: the identification of the dual of the form space with `Fin g → ℂ`, the coordinates of the period lattice, and so the literal set `Λ ⊆ ℂ^g` used to build the Jacobian. The file''s own header (Jacobian/HolomorphicForms/BasisAlignedDualEquiv.lean lines 23–29) says this and claims the abstract isomorphism class is unaffected. That claim is prose in a comment, not a theorem proved in this file.'
- 'The index type is `Fin (analyticGenus E X)`, so the declaration needs `[FiniteDimensionalHolomorphicOneForms E X]`. Without a finite basis there would be nothing to choose.'
- 'The declaration is `noncomputable`: you cannot run it to get actual forms. It only guarantees that a basis exists and lets later definitions refer to "the" chosen one consistently.'
quiz:
- q: Where does this basis come from?
  type: choice
  choices:
  - '`Module.finBasis`, which chooses a basis using the axiom of choice'
  - An explicit construction of g independent 1-forms on X
  - The normalized basis dual to a symplectic basis of H₁(X, ℤ)
  answer: 0
  explain: The body is literally `Module.finBasis ℂ (HolomorphicOneForm E X)` (Jacobian/HolomorphicForms/BasisAlignedDualEquiv.lean lines 50–52), and the docstring at Jacobian/HolomorphicForms/BasisAlignedDualEquiv.lean lines 45–49 says it goes through `Module.Free.chooseBasis` and is non-canonical.
- q: How many basis vectors are there?
  type: choice
  choices:
  - '`analyticGenus E X`, the genus'
  - '`2 * analyticGenus E X`'
  - One for each point of X
  answer: 0
  explain: The index type is `Fin (analyticGenus E X)` (Jacobian/HolomorphicForms/BasisAlignedDualEquiv.lean lines 50–52), and [analyticGenus](#/node/HolomorphicForms.analyticGenus) is the ℂ-dimension of the form space.
- q: Does the Jacobian built from this basis depend on which basis was chosen?
  type: choice
  choices:
  - The concrete lattice in ℂ^g does; the file claims the isomorphism class does not, but that claim is a comment rather than a theorem here
  - No, the basis is canonical
  - Yes, and the file says this is a problem
  answer: 0
  explain: Jacobian/HolomorphicForms/BasisAlignedDualEquiv.lean lines 23–29 states that the resulting subgroup depends on the basis while its abstract isomorphism class does not; nothing in this file proves the second half.
- q: Why is a basis needed for the Jacobian at all?
  type: choice
  choices:
  - It turns a chain into g numbers, the integrals of ω₁, …, ω_g, which is the ℂ^g the period lattice sits inside
  - It makes the 1-forms holomorphic
  - It proves the period lattice is discrete
  answer: 0
  explain: '[periodVector](#/node/Periods.periodVector) at Jacobian/Periods/GenuinePeriodLattice.lean lines 60–61 is `fun i => chainIntegral (holomorphicOneFormFinBasis ℂ X i) l`, so the basis is exactly what gives the period lattice coordinates.'
---
## Plain English

To write the Jacobian as `ℂ^g / Λ` you need coordinates, and coordinates on the space of holomorphic 1-forms mean a basis ω₁, …, ω_g. This declaration supplies one:

```
holomorphicOneFormFinBasis : Module.Basis (Fin (analyticGenus E X)) ℂ (HolomorphicOneForm E X)
  := Module.finBasis ℂ (HolomorphicOneForm E X)
```

Defined at Jacobian/HolomorphicForms/BasisAlignedDualEquiv.lean lines 50–52.

The honest description is: *some* basis, no one in particular. `Module.finBasis` produces a basis of a finite-dimensional space indexed by `Fin (finrank)`, and it does that by calling `Module.Free.chooseBasis`, which is the axiom of choice. The declaration's own docstring (Jacobian/HolomorphicForms/BasisAlignedDualEquiv.lean lines 45–49) says "The choice is non-canonical". Nothing is proved about these particular forms beyond their being a basis.

That matters when you compare with the classical account. Textbooks often fix a basis *normalized* against a symplectic basis a₁, …, a_g, b₁, …, b_g of H₁(X, ℤ), so that ∫_{a_i} ω_j = δ_ij and the period matrix has the shape (I | τ) with τ symmetric with positive-definite imaginary part. No such normalization exists here. Nothing in this file knows about H₁ at all.

## What depends on the choice

The use is direct. [periodVector](#/node/Periods.periodVector) (Jacobian/Periods/GenuinePeriodLattice.lean lines 60–61) sends a chain `l` to `(∫_l ω₁, …, ∫_l ω_g)`, reading the chain's integral against each basis form in turn. That is how a chain becomes a point of ℂ^g, which is how the [period lattice](#/node/Periods.genuinePeriodSubgroup) and hence the Jacobian get a concrete model. The same basis supplies the coordinates in which the pushforward and pullback maps on Jacobians are written.

Change the basis and you change the literal subgroup of ℂ^g. The file's header (Jacobian/HolomorphicForms/BasisAlignedDualEquiv.lean lines 23–29) argues that only *some* basis is needed, because the abstract isomorphism class and all the topological and discreteness properties are unaffected. That is a reasonable design argument and it is written as a comment; it is not a theorem in this file.

The rest of the file dualizes the basis into a linear equivalence `(HolomorphicOneForm E X →ₗ[ℂ] ℂ) ≃ₗ[ℂ] (Fin g → ℂ)` (Jacobian/HolomorphicForms/BasisAlignedDualEquiv.lean lines 69–72), with the expected compatibility: applying it to a functional φ and reading off coordinate i gives φ(ω_i) (Jacobian/HolomorphicForms/BasisAlignedDualEquiv.lean lines 119–123). That equivalence is the "functional on forms" view of the same coordinates; the genuine period lattice does not go through it.
