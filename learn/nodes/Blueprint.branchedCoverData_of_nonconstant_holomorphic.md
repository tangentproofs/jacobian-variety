---
id: Blueprint.branchedCoverData_of_nonconstant_holomorphic
title: Turning a holomorphic map into a branched cover
summary: 'This is the construction that earns the degree: it fills every assumed field of the branched-cover package from a genuine nonconstant holomorphic map, taking the ramification index to be the local order of vanishing.'
review: draft
authors:
- claude
caveats:
- 'It is a `def`, not a theorem: it produces the data structure. The mathematical content lives in the four named lemmas it cites, each proved elsewhere, plus one inline argument built on `IsHolomorphicAt.exists_local_inj_of_unramified`.'
- 'Its two analytic inputs, `IsHolomorphic f` and `HasWeightedFiberConservation f`, are themselves structures with assumed fields. Both are proved from `ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f`, so on the public path nothing is assumed — but the chain is three files long.'
- 'The hypotheses are not quite "compact Riemann surfaces": `X` must be compact, Hausdorff and preconnected, `Y` Hausdorff and preconnected, and both complex 1-manifolds. Compactness of `Y` is not required.'
- '`fiberSum_const` is filled by a lemma that takes the *same* finiteness proof used for the `finite_fiber` field, so the two fields are matched by construction rather than by a coincidence of proofs.'
quiz:
- q: What does this definition take as the ramification index?
  type: choice
  choices:
  - The constant function 1
  - '`mapAnalyticOrderAt f`, the chart-local order of vanishing'
  - The number of points in the fibre
  answer: 1
  explain: 'The first field is `ramificationIndex := mapAnalyticOrderAt f` (Jacobian/Blueprint/Sec02/BranchedDegreeFromHolomorphic.lean lines 61–91).'
- q: 'Why is the companion lemma `branchedCoverData_of_nonconstant_holomorphic_compatible` provable by `rfl`?'
  type: choice
  choices:
  - 'Because the ramification index field *is* `mapAnalyticOrderAt f` by definition'
  - Because `rfl` proves anything about structures
  - Because compatibility is assumed
  answer: 0
  explain: 'Compatibility asks `h.ramificationIndex x = mapAnalyticOrderAt f x`; since the field was defined to be that function, the proof is `intro x _hfx; rfl` (Jacobian/Blueprint/Sec02/BranchedDegreeFromHolomorphic.lean lines 97–107).'
- q: Which hypothesis is used to get the weighted fibre count constant on all of `Y` rather than just locally?
  type: choice
  choices:
  - Compactness of `X`
  - '`PreconnectedSpace Y`'
  - Hausdorffness of `Y`
  answer: 1
  explain: 'The `fiberSum_const` field is filled by `isHolomorphic_weightedFiberSum_const`, which turns local constancy into global constancy using `[PreconnectedSpace Y]` (Jacobian/Blueprint/Sec02/WeightedFiberCardConst.lean lines 713–726).'
- q: What does this definition contribute to the honesty of the public degree?
  type: choice
  choices:
  - 'Nothing; the degree is defined independently'
  - 'It shows the branched-cover data the degree chooses actually exists, so the `else 0` fallback never fires'
  - It proves the degree is positive
  answer: 1
  explain: '`ContMDiff.exists_branchedCoverData` (Jacobian/Solution.lean lines 254–263) calls this definition to produce the existence witness that `ContMDiff.degree` tests for.'
---
## Plain English

[BranchedCoverData](#/node/HolomorphicForms.BranchedCoverData) is a package that *assumes* the hard facts about a branched cover. This definition is where the bill is paid: given an honest nonconstant holomorphic map, it builds such a package.

The inputs are `f : X → Y` between complex 1-manifolds with `X` compact, Hausdorff and preconnected and `Y` Hausdorff and preconnected, a proof that `f` is holomorphic with the local `k`-to-1 package ([IsHolomorphic](#/node/HolomorphicForms.IsHolomorphic)), a proof of local conservation of the weighted fibre count ([HasWeightedFiberConservation](#/node/HolomorphicForms.HasWeightedFiberConservation)), and a proof that `f` is not constant.

The output fills every field, each from a named lemma (Jacobian/Blueprint/Sec02/BranchedDegreeFromHolomorphic.lean lines 61–91):

- `ramificationIndex := mapAnalyticOrderAt f` — the index *is* the local order of vanishing, by definition, not by some later identification;
- `ramificationIndex_pos` from `mapAnalyticOrderAt_pos`, which needs nonconstancy and preconnectedness of `X`;
- `finite_fiber` from `isHolomorphic_finite_fiber`, the identity principle plus compactness;
- `fiberSum_const` from `isHolomorphic_weightedFiberSum_const`, local conservation upgraded by preconnectedness of `Y`;
- `ramified_finite` from `mapAnalyticOrderAt_ramified_finite`, the branch locus is finite;
- `local_bijective_unramified` is proved inline, by shrinking the local injectivity witness to `U ∩ f⁻¹(V)` so that it maps *onto* `V`.

## Why it matters that the index is the order of vanishing

The whole definition would be worthless if `ramificationIndex` were allowed to be any positive function satisfying the fields. The companion lemma `branchedCoverData_of_nonconstant_holomorphic_compatible` (Jacobian/Blueprint/Sec02/BranchedDegreeFromHolomorphic.lean lines 97–107) says this datum satisfies `RamificationIndexCompatible`, and its proof is `rfl` — the index is literally [mapAnalyticOrderAt](#/node/HolomorphicForms.mapAnalyticOrderAt). Compatibility is what makes the degree independent of which datum you chose (Jacobian/TraceDegree/AnalyticDegreeU.lean lines 92–108).

## How it is used

`ContMDiff.exists_branchedCoverData` (Jacobian/Solution.lean lines 254–263) derives the two analytic inputs from a `ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω` hypothesis and calls this definition. That is the existence statement the public [ContMDiff.degree](#/node/ContMDiff.degree) tests for, so the degree's `else 0` branch is provably dead for every nonconstant holomorphic map of compact Riemann surfaces.
