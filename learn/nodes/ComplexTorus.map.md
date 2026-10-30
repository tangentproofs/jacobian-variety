---
id: ComplexTorus.map
title: Pushing an additive map down to the tori
summary: An additive map of the ambient spaces descends to the tori as soon as it sends one lattice into the other, and that one hypothesis is all the definition asks for — no continuity, no complex linearity.
review: draft
authors:
- claude
caveats:
- 'The docstring reads "A continuous additive map preserving lattices descends to a map of complex tori" (Jacobian/ComplexTorus/Defs.lean line 132), but it overstates the definition: the hypothesis `f : V →+ W` is a bare additive monoid homomorphism (Jacobian/ComplexTorus/Defs.lean line 133), there is no continuity or ℂ-linearity hypothesis, and the result is an `→+`, not a continuous map. Continuity is added separately by [map_continuous](#/node/ComplexTorus.map_continuous), which takes `Continuous f` as an argument.'
- 'The lattice-preservation hypothesis is one-directional: `f` maps `Λ.subgroup` into `Γ.subgroup`. It is not required to map it onto, or to be injective on it, so the induced map of tori need be neither injective nor surjective.'
- 'The definition is a thin renaming of Mathlib''s `QuotientAddGroup.map`; the only project content is the choice to phrase it in terms of `FullComplexLattice`.'
quiz:
- q: What does `map` actually assume about `f`?
  type: choice
  choices:
  - 'Only that `f : V →+ W` is additive and sends `Λ.subgroup` into `Γ.subgroup`'
  - That `f` is continuous and ℂ-linear
  - That `f` is a homeomorphism matching the lattices exactly
  answer: 0
  explain: 'The signature at Jacobian/ComplexTorus/Defs.lean lines 133–136 lists `f : V →+ W` and `hf : ∀ v ∈ Λ.subgroup, f v ∈ Γ.subgroup`, nothing more, even though the docstring says "continuous".'
- q: What is the computational content of `map`?
  type: choice
  choices:
  - It sends the class of `v` to the class of `f v`, which `map_mk` proves by `rfl`
  - It integrates `f` over the fundamental domain
  - It chooses a representative using `Classical.choice`
  answer: 0
  explain: '`map_mk` at Jacobian/ComplexTorus/Defs.lean lines 138–141 states `map Λ Γ f hf (mk V Λ v) = mk W Γ (f v)` and the proof is `rfl`.'
- q: Must a map of tori produced by `map` be injective?
  type: choice
  choices:
  - No; the hypothesis only says the source lattice lands inside the target lattice
  - Yes, because quotient maps are injective
  - Yes, provided both lattices are full
  answer: 0
  explain: 'The only hypothesis is `hf : ∀ v ∈ Λ.subgroup, f v ∈ Γ.subgroup` (Jacobian/ComplexTorus/Defs.lean line 134). The zero map satisfies it and induces the zero map of tori.'
- q: What do `map_id` and `map_comp` establish?
  type: choice
  choices:
  - That the construction is functorial — identity goes to identity, composites to composites
  - That `map` is injective
  - That `map` is continuous
  answer: 0
  explain: Jacobian/ComplexTorus/Defs.lean lines 145–147 and 149–157 prove exactly those two equations, each by passing to the corresponding Mathlib lemma about `QuotientAddGroup.map`.
---
## Plain English

Suppose you have two complex tori: `V` modulo a lattice `Λ`, and `W` modulo a lattice `Γ`. A map `f : V → W` of the vector spaces gives a well-defined map of the tori exactly when it does not tear the gluing: whenever two vectors differ by a lattice vector of `Λ`, their images must differ by a lattice vector of `Γ`. For an additive `f` that is the same as saying `f` sends `Λ.subgroup` inside `Γ.subgroup`.

That is precisely the Lean statement (Jacobian/ComplexTorus/Defs.lean lines 133–136): given `f : V →+ W` and `hf : ∀ v ∈ Λ.subgroup, f v ∈ Γ.subgroup`, you get an additive homomorphism `quotient V Λ →+ quotient W Γ`. The body is Mathlib's `QuotientAddGroup.map`.

The companion `map_mk` (Jacobian/ComplexTorus/Defs.lean lines 138–141) says what the map does, and says it by `rfl`: the class of `v` goes to the class of `f v`. Nothing is chosen and nothing is integrated.

## What the docstring overstates

The docstring says "continuous additive map". The hypothesis is not continuous. `f : V →+ W` is additivity and nothing else, and the conclusion `→+` carries no topology either. Continuity of the descended map is a separate lemma, [map_continuous](#/node/ComplexTorus.map_continuous), which takes `Continuous f` as an explicit argument. So the definition is more general than its prose, and anything about topology has to be asked for.

## Functoriality

Two lemmas record that this is a functor, not just a construction:

- `map_id` (Jacobian/ComplexTorus/Defs.lean lines 145–147): the identity map of `V` induces the identity of the torus.
- `map_comp` (Jacobian/ComplexTorus/Defs.lean lines 149–157): `g ∘ f` induces the composite of the induced maps.

Both are discharged by the matching Mathlib lemmas.

This is the descent step the Jacobian actually uses. The continuous-linear wrapper [mapClm](#/node/ComplexTorus.mapClm) is `map` applied to the additive homomorphism underlying a continuous linear map, and that is what builds [pushforward](#/node/Jacobian.pushforward) and [pullback](#/node/Jacobian.pullback) on the period quotient.
