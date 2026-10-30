---
id: ContMDiff.degree
title: The degree of a holomorphic map, by case split
summary: 'The public degree is a three-way classical case split with two `else 0` branches, and separate theorems prove that neither of those branches can ever fire.'
review: draft
authors:
- claude
caveats:
- 'The body never mentions `hf`. The holomorphy proof is an argument of the definition (so you cannot even write `degree f hf` without it), but the *value* depends on `f` alone; `set_option linter.unusedVariables false` at Jacobian/Solution.lean line 209 silences the warning about that.'
- 'The branched-cover datum is `Classical.choose`n from an existence statement. Independence of that choice is a separate theorem (`branchedDegree_eq_of_compatibleU`), not part of the definition.'
- 'The degree is 0 for constant maps by fiat, matching the challenge docstring. The Solution path does *not* prove that a nonconstant map has degree ≥ 1; positivity of `branchedDegree` is only available with an explicit surjectivity hypothesis.'
- 'The two `else 0` branches are proved unreachable in the Riemann-surface setting only. `ContMDiff.exists_branchedCoverData` uses that `X` is compact, Hausdorff and connected and that `Y` is Hausdorff and connected.'
quiz:
- q: 'How many branches does the body of `ContMDiff.degree` have, and what are they?'
  type: choice
  choices:
  - 'Two: 0 for constant maps, the weighted fibre count otherwise'
  - 'Four: 0 if constant, 0 if `Y` is empty, 0 if no compatible branched-cover datum exists, else the branched degree'
  - 'One: always the weighted fibre count'
  answer: 1
  explain: 'Jacobian/Solution.lean lines 210–222 nests three `if`s: `∃ y₀, ∀ x, f x = y₀`, then `Nonempty Y`, then `∃ hbc, hbc.RamificationIndexCompatible`.'
- q: Why is the `Nonempty Y` test there at all, when `Y` is a connected Riemann surface?
  type: choice
  choices:
  - 'Because the declaration''s signature does not record `[ConnectedSpace Y]` — Lean only includes the hypotheses the statement mentions — so nonemptiness has to be decided inside the body'
  - Because `Y` really might be empty
  - 'To make the definition computable'
  answer: 0
  explain: 'The comment at Jacobian/Solution.lean lines 231–235 explains this, and `ContMDiff.degree_eq_analyticDegreeU` (Jacobian/Solution.lean lines 236–240) collapses the wrapper using the ambient `Nonempty Y`.'
- q: What rules out the `else 0` for "no compatible branched-cover datum"?
  type: choice
  choices:
  - 'Nothing; it is a genuine fallback'
  - '`ContMDiff.exists_branchedCoverData`, which builds a compatible datum for every nonconstant complex-smooth map of compact Riemann surfaces'
  - An axiom asserting existence
  answer: 1
  explain: 'Jacobian/Solution.lean lines 254–263 constructs the datum from `branchedCoverData_of_nonconstant_holomorphic`, with the holomorphy and conservation packages derived from `hf`.'
- q: 'For a nonconstant `f`, what number does `degree f hf` equal?'
  type: choice
  choices:
  - The number of points in some fibre
  - 'The `branchedDegree` of *any* ramification-compatible branched-cover datum for `f`'
  - The genus difference between `X` and `Y`
  answer: 1
  explain: '`ContMDiff.degree_eq_branchedDegree` (Jacobian/Solution.lean lines 271–280) states exactly that, and well-definedness comes from `branchedDegree_eq_of_compatibleU` (Jacobian/TraceDegree/AnalyticDegreeU.lean lines 92–108), which assumes `f` is holomorphic.'
- q: Does the value of `degree f hf` depend on which proof `hf` you supply?
  type: choice
  choices:
  - 'Yes, different proofs can give different degrees'
  - 'No, the body does not use `hf` at all'
  - 'Only for ramified maps'
  answer: 1
  explain: 'The body at Jacobian/Solution.lean lines 210–222 branches only on `f`. `hf` is bound but unused, which is why the unused-variable linter is switched off at Jacobian/Solution.lean line 209.'
---
## Plain English

This is the challenge's `degree`: for a holomorphic map `f : X → Y` between compact Riemann surfaces, the number of preimages of a typical point, counted with multiplicity. The specification asks for 0 when `f` is constant and "the usual degree" otherwise (Jacobian/Challenge.lean lines 146–150).

The Lean definition is a nest of three classical decisions (Jacobian/Solution.lean lines 210–222):

1. Is `f` constant, i.e. `∃ y₀, ∀ x, f x = y₀`? Then 0.
2. Otherwise, is `Y` nonempty? If not, 0.
3. Otherwise, is there a [BranchedCoverData](#/node/HolomorphicForms.BranchedCoverData) for `f` whose ramification indices agree with the chart-local order of vanishing? If so, return the [branchedDegree](#/node/HolomorphicForms.branchedDegree) of one such datum, chosen by `Classical.choose`. If not, 0.

Branch 1 is the intended answer, not a fallback. Branches 2 and 3 are fallbacks, and a fallback that silently returns 0 is exactly the kind of thing that can fake a theorem. So the file proves that neither one fires.

## Why the fallbacks never fire

Branch 2: in the Riemann-surface setting `Y` is connected, hence nonempty. The test is only there because this declaration's signature does not mention `[ConnectedSpace Y]` — Lean includes a section hypothesis only when the statement needs it, and the frozen `Challenge.lean` signature must be matched exactly. `ContMDiff.degree_eq_analyticDegreeU` (Jacobian/Solution.lean lines 236–240) discharges it and identifies the public degree with the internal `analyticDegreeU` (Jacobian/TraceDegree/AnalyticDegreeU.lean lines 59–67).

Branch 3: `ContMDiff.exists_branchedCoverData` (Jacobian/Solution.lean lines 254–263) builds the datum. It derives the holomorphy package and the weighted-fibre-conservation package from `hf` and feeds them to [branchedCoverData_of_nonconstant_holomorphic](#/node/Blueprint.branchedCoverData_of_nonconstant_holomorphic).

## Why the choice does not matter

`Classical.choose` picks one datum out of possibly many. `branchedDegree_eq_of_compatibleU` (Jacobian/TraceDegree/AnalyticDegreeU.lean lines 92–108) shows that for a holomorphic `f` any two *compatible* data give the same `branchedDegree`: compatibility pins each ramification index to [mapAnalyticOrderAt](#/node/HolomorphicForms.mapAnalyticOrderAt), which is determined by `f`. So `ContMDiff.degree_eq_branchedDegree` (Jacobian/Solution.lean lines 271–280) can characterise the value against any datum you like.

This is the degree that appears on the right of the push-pull identity `pushforward f hf (pullback f hf P) = degree f hf • P` (Jacobian/Solution.lean lines 282–291).
