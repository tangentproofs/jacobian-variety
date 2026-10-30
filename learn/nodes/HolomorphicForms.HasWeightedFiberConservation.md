---
id: HolomorphicForms.HasWeightedFiberConservation
title: The weighted fibre count is locally constant
summary: 'A one-field predicate carrying the hardest analytic fact in the degree story, stated locally and conditionally — and then proved for every complex-smooth map, so it is not a smuggled assumption.'
review: draft
authors:
- claude
caveats:
- 'The statement is *local*: the sums agree for `y` in some neighbourhood of `y₀` (`∀ᶠ y in 𝓝 y₀`). Global constancy over `Y` is a separate step that needs `Y` preconnected (`isHolomorphic_weightedFiberSum_const`).'
- 'The finiteness of the fibres is an argument of the field, named `finite_fiber`, not a conclusion. The sum is taken over the `Finset` built from exactly that proof.'
- 'The field''s type quantifies over its own instance arguments (`∀ [IsManifold …] [CompactSpace X] …`). This keeps the structure usable in contexts without those instances; the content only applies when they are available.'
- 'The nonconstancy hypothesis `¬ ∃ y₀, ∀ x, f x = y₀` is inside the field, so the predicate says nothing at all about constant maps.'
- 'Being a `Prop`-valued structure with one field, it is logically just that implication. It carries no data and, on its own, proves nothing.'
quiz:
- q: 'What quantity does this predicate say is locally constant?'
  type: choice
  choices:
  - The number of points in the fibre
  - '`∑ x ∈ f⁻¹{y}, mapAnalyticOrderAt f x`, the fibre count weighted by ramification index'
  - The genus of `Y`
  answer: 1
  explain: 'The field sums `mapAnalyticOrderAt f` over `(finite_fiber y).toFinset` (Jacobian/HolomorphicForms/HolomorphicMap.lean lines 198–206).'
- q: 'Is the conclusion "equal for all `y`" or "equal near `y₀`"?'
  type: choice
  choices:
  - Equal for all `y`
  - 'Equal for `y` in a neighbourhood of `y₀`, for every `y₀`'
  - Equal for `y` in the regular locus
  answer: 1
  explain: 'The field concludes `∀ y₀ : Y, ∀ᶠ y in 𝓝 y₀, …` (Jacobian/HolomorphicForms/HolomorphicMap.lean lines 198–206) — local constancy at every point, not global equality.'
- q: Where does global constancy come from?
  type: choice
  choices:
  - 'From a connectedness argument: a locally constant function on a preconnected space is constant'
  - From compactness of `X`
  - It is assumed as a second field
  answer: 0
  explain: '`isHolomorphic_weightedFiberSum_const` (Jacobian/Blueprint/Sec02/WeightedFiberCardConst.lean lines 713–726) applies `apply_eq_of_preconnectedSpace` with `[PreconnectedSpace Y]`.'
- q: Does assuming this predicate smuggle in the result the project wants?
  type: choice
  choices:
  - 'Yes, nothing proves it'
  - 'No: `hasWeightedFiberConservation_of_contMDiff` derives it from complex smoothness alone'
  - 'It is an axiom'
  answer: 1
  explain: 'Jacobian/HolomorphicForms/HolomorphicMap.lean lines 1340–1345 builds the structure from `hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f`, delegating to the long proof whose statement is Jacobian/HolomorphicForms/HolomorphicMap.lean lines 1178–1187.'
---
## Plain English

Here is the fact that makes "degree" mean anything. Take a nonconstant holomorphic map `f : X → Y` of compact Riemann surfaces and a point `y` of `Y`. Count its preimages, but count a point where `k` sheets collide as `k` points. The claim is that this weighted count is the same number no matter which `y` you picked. Sheets can merge and split as `y` moves, but the total is conserved.

`HasWeightedFiberConservation f` is the local half of that claim, packaged as a predicate with a single field. Spelled out, the field says: assuming `X` and `Y` are complex 1-manifolds, `X` is compact, Hausdorff and preconnected and `Y` is Hausdorff; assuming `f` is not constant; and given a proof that every fibre of `f` is finite — then for every `y₀`, the weighted fibre sum over `y` equals the weighted fibre sum over `y₀` for all `y` near `y₀`.

Three details of how it is stated matter.

It is local, not global. `∀ᶠ y in 𝓝 y₀` means "for all `y` in some neighbourhood of `y₀`". Local constancy becomes global constancy only after a connectedness argument, carried out in `isHolomorphic_weightedFiberSum_const` (Jacobian/Blueprint/Sec02/WeightedFiberCardConst.lean lines 713–726) using that `Y` is preconnected.

Finiteness of fibres is an input, not an output. The field takes a proof `finite_fiber : ∀ y, (f ⁻¹' {y}).Finite` as an argument and sums over the finite set that proof produces. Finiteness itself is proved elsewhere, from the identity principle plus compactness (`isHolomorphic_finite_fiber`, Jacobian/HolomorphicForms/HolomorphicMap.lean lines 627–631).

The typeclass assumptions sit *inside* the field type, written `∀ [IsManifold 𝓘(ℂ) ω X] …`. That is a Lean device: the predicate can be stated and passed around in contexts lacking those instances, and the content is only usable once they are supplied.

## Why this is not a smuggled hypothesis

A predicate that assumes the hard theorem is only honest if something proves it. `hasWeightedFiberConservation_of_contMDiff` (Jacobian/HolomorphicForms/HolomorphicMap.lean lines 1340–1345) produces the structure from nothing more than complex smoothness of `f`. The real work is in `weightedFiberConservation_of_contMDiff` (Jacobian/HolomorphicForms/HolomorphicMap.lean lines 1178–1187 for the statement), whose proof separates the finitely many points of the fibre over `y₀` by disjoint open sets, uses the local `k`-to-1 normal form in each of them, and uses compactness of `X` to show nearby fibres cannot escape that union.

## How it is used

It is one of the two analytic inputs to [branchedCoverData_of_nonconstant_holomorphic](#/node/Blueprint.branchedCoverData_of_nonconstant_holomorphic), where it supplies the `fiberSum_const` field of [BranchedCoverData](#/node/HolomorphicForms.BranchedCoverData) — the field that allows [branchedDegree](#/node/HolomorphicForms.branchedDegree) to read the degree off at an arbitrary point. The other input is [IsHolomorphic](#/node/HolomorphicForms.IsHolomorphic).
