---
id: HolomorphicForms.IsHolomorphic
title: Holomorphic, plus the local k-to-1 picture
summary: 'Extends plain holomorphy with the local mapping theorem as an extra assumed field — a field that is then discharged for every complex-smooth map, so nothing is left assumed.'
review: draft
authors:
- claude
caveats:
- 'The local `k`-to-1 normal form is a structure *field*, i.e. an assumption of anyone who supplies `IsHolomorphic f`. It is a real theorem about holomorphic maps, and `hasLocalKfoldRamification_of_contMDiff` proves it from smoothness; but a reader should know it is assumed at this point in the file, not proved.'
- 'The field asserts the `k` simple preimages only for `y ∈ V` with `y ≠ f x`. At `y = f x` it says nothing, which is right: there the `k` sheets have collided.'
- 'The field is conditional on `0 < k` and `mapAnalyticOrderAt f x = k`, so for a locally constant `f` (where the order reads 0) it is vacuous.'
- 'Like `HasWeightedFiberConservation`, the field quantifies over its own `[IsManifold …]` instances, so the structure can be stated without them in scope.'
- 'The preimages are listed as a `Finset X` with `s.card = k`, so they are genuinely `k` *distinct* points, each unramified.'
quiz:
- q: 'What does `IsHolomorphic f` have that `IsHolomorphicBasic f` does not?'
  type: choice
  choices:
  - Conservation of the weighted fibre count
  - 'A field giving the local `k`-to-1 structure of `f` near each point'
  - Compactness of the source
  answer: 1
  explain: 'It `extends IsHolomorphicBasic f` and adds `local_kfold_ramified` (Jacobian/HolomorphicForms/HolomorphicMap.lean lines 186–195); the docstring says global conservation is kept out on purpose.'
- q: 'Near a point `x` of multiplicity `k`, what does the field say about a nearby `y ≠ f x`?'
  type: choice
  choices:
  - 'It has at least one preimage near `x`'
  - 'Its preimages inside a fixed neighbourhood `U` of `x` are exactly `k` distinct points, each of multiplicity 1'
  - 'It has exactly `k` preimages in all of `X`'
  answer: 1
  explain: 'The field produces `s : Finset X` with `s.card = k`, `↑s ⊆ U`, every element mapping to `y` with order 1, and every point of `U` over `y` lying in `s` (Jacobian/HolomorphicForms/HolomorphicMap.lean lines 186–195).'
- q: 'Why does the statement exclude `y = f x`?'
  type: choice
  choices:
  - 'An oversight'
  - 'Because at `y = f x` the `k` sheets meet at the single point `x`, so there are not `k` distinct preimages'
  - Because `f x` has no preimage
  answer: 1
  explain: 'The hypothesis `y ≠ f x` appears in the field (Jacobian/HolomorphicForms/HolomorphicMap.lean lines 186–195); the classical picture `w = z^k` has `k` distinct roots for every `w ≠ 0` and one for `w = 0`.'
- q: Is the extra field an assumption the project never pays for?
  type: choice
  choices:
  - 'No: `hasLocalKfoldRamification_of_contMDiff` derives it from complex smoothness'
  - 'Yes, it is assumed everywhere'
  - 'It is an axiom in a production file'
  answer: 0
  explain: 'Jacobian/HolomorphicForms/HolomorphicMap.lean lines 1151–1156 builds `HasLocalKfoldRamification f` from `hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f`, and `isHolomorphic_of_contMDiff` (Jacobian/HolomorphicForms/HolomorphicMap.lean lines 1138–1143) combines it with the basic package.'
---
## Plain English

In one complex variable, a nonconstant holomorphic map near a point looks like `z ↦ z^k` in suitable coordinates. One consequence is the picture that the whole degree story rests on: every value close to `f x`, other than `f x` itself, has exactly `k` preimages close to `x`, and each of those is a simple (unramified) preimage.

`IsHolomorphic f` is [IsHolomorphicBasic](#/node/HolomorphicForms.IsHolomorphicBasic) — continuity and chart-local analyticity — plus that picture as an extra field, `local_kfold_ramified`. Unwound, the field says: if `k > 0` and the local multiplicity [mapAnalyticOrderAt](#/node/HolomorphicForms.mapAnalyticOrderAt) at `x` is `k`, then there are an open `U ∋ x` and an open `V ∋ f x` such that for every `y ∈ V` with `y ≠ f x` there is a finite set `s` of exactly `k` points, all inside `U`, each mapping to `y` with multiplicity 1, and containing every point of `U` that maps to `y`.

That last clause is what makes it useful: `s` is not just `k` preimages, it is *all* of them inside `U`. Counting fibres locally becomes exact arithmetic rather than an inequality.

## Why it is a field and not a theorem here

The file is laid out so that each layer assumes only what it needs. Phrasing the local mapping theorem as a field lets the combinatorial arguments be written before the analysis is in place, and lets a statement advertise whether it needs it. The same file then pays the bill: `hasLocalKfoldRamification_of_contMDiff` (Jacobian/HolomorphicForms/HolomorphicMap.lean lines 1151–1156) proves the package from complex smoothness alone, and `isHolomorphic_of_contMDiff` (Jacobian/HolomorphicForms/HolomorphicMap.lean lines 1138–1143) assembles the whole structure for any `ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω` map. So nowhere in the public path is this left as an unproved hypothesis.

Note what is *not* in here. Conservation of the weighted fibre count is kept out deliberately — the structure's own docstring says so (Jacobian/HolomorphicForms/HolomorphicMap.lean lines 180–185) — and must be requested separately as [HasWeightedFiberConservation](#/node/HolomorphicForms.HasWeightedFiberConservation) (Jacobian/HolomorphicForms/HolomorphicMap.lean lines 198–206).

## How it is used

`IsHolomorphic` is the analytic input to [branchedCoverData_of_nonconstant_holomorphic](#/node/Blueprint.branchedCoverData_of_nonconstant_holomorphic): it gives positivity of the ramification index, finiteness of fibres, finiteness of the branch locus, and local bijectivity at unramified points. It is also the hypothesis under which two branched-cover data are shown to have the same degree (Jacobian/TraceDegree/AnalyticDegreeU.lean lines 92–108), and under which the differential of `f` is inverted at unramified points (Jacobian/TraceDegree/TraceDefinition.lean lines 254–300).
