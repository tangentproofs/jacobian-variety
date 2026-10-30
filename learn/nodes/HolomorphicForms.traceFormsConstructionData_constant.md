---
id: HolomorphicForms.traceFormsConstructionData_constant
title: Trace along a constant map
summary: 'The trace along a constant map is set to zero, and the specification survives by a case split: off the image point the fibre is empty, and at the image point a branched-cover datum would make a one-point set open in Y.'
review: draft
authors:
- claude
caveats:
- 'Defined, not computed. Classically a constant map carries no `BranchedCoverData` at all (the fibre over the image point is all of X, which is infinite, while `finite_fiber` demands finiteness), so the regular-value requirement has nothing to range over and `traceForm := 0` is a convention rather than a derived value. The Lean does not state that; it proves the requirement by case split against a hypothetical datum.'
- 'The convention matches the rest of the project: `ContMDiff.degree` of a constant map is 0 (Jacobian/Solution.lean lines 210–222), so the degree identity for a constant map reads "trace of the pullback = 0".'
- 'The case y = y₀ is settled by contradiction, so nothing is computed there. The case y ≠ y₀ does carry content: the fiber is empty and the empty sum is 0.'
- 'The hypothesis `hη : η ≠ 0` is used only to discharge `map_zero_spec` by contradiction; the regular-value proof never looks at it.'
- 'This is a `private` declaration, reachable only through the provider.'
quiz:
- q: What is the trace form along a constant map, in this Lean?
  type: choice
  choices:
  - The zero form on Y
  - The form η transported to the image point
  - A delta-like form supported at the image point
  answer: 0
  explain: 'The field is `traceForm := 0` (Jacobian/HolomorphicForms/TraceSpec.lean line 171).'
- q: How is the case y = y₀ (the image point) handled?
  type: choice
  choices:
  - By deriving a contradiction from the existence of a branched-cover datum with y₀ regular
  - By summing over the infinite fiber
  - By extending across the branch point with Riemann's theorem
  answer: 0
  explain: 'The branch opens with `exfalso` and ends in a contradiction with the punctured-neighbourhood filter (Jacobian/HolomorphicForms/TraceSpec.lean lines 182–214).'
- q: Which property of Y produces that contradiction?
  type: choice
  choices:
  - Y has no isolated points, so the one-point set {y₀} cannot be open
  - Y is compact
  - Y is connected
  answer: 0
  explain: 'Local bijectivity at an unramified point forces the open set V to be {y₀}, and `PerfectSpace.not_isolated` then contradicts its openness (Jacobian/HolomorphicForms/TraceSpec.lean lines 204–214).'
- q: Does the case y ≠ y₀ carry real mathematical content?
  type: choice
  choices:
  - Yes; the fiber over y is empty and the empty sum is zero, which matches the zero form
  - No; it is also a contradiction
  - No; it is proved by Classical.choice
  answer: 0
  explain: 'The Lean shows `f ⁻¹'' {y} = ∅`, rewrites the finite set to `∅` and finishes with `Finset.sum_empty` (Jacobian/HolomorphicForms/TraceSpec.lean lines 215–229).'
---
## Plain English

A constant map f : X → Y is not a covering of anything, and classically its trace on 1-forms is zero. This leaf makes that official: it supplies an element of [TraceFormsConstructionData](#/node/HolomorphicForms.TraceFormsConstructionData) whose global form is the zero form on Y, and it checks the two requirements (`Jacobian/HolomorphicForms/TraceSpec.lean` lines 166–230).

The regular-value requirement splits on whether the point y of Y is the image point y₀.

If y is not y₀, the fiber over y is empty. The fiber sum is an empty sum, which is zero, and the zero form is zero at y. Both sides agree.

If y is y₀, the Lean shows the situation cannot arise. Suppose some branched-cover datum has y₀ as a regular value. Pick any point x of X; it lies in the fiber, so its ramification index is 1, so the datum's `local_bijective_unramified` field hands over open sets U containing x and V containing y₀ with f a bijection from U onto V. But f is constant, so the image of U is the single point {y₀}, forcing V = {y₀}. A one-point set in Y cannot be open. The Lean gets that from `PerfectSpace Y`, synthesised once Y is known to be nontrivial, and nontriviality comes from the fact that a space with ℂ-valued charts has at least two points ([exists_two_distinct_points_of_chartedSpaceComplex](#/node/HolomorphicForms.exists_two_distinct_points_of_chartedSpaceComplex), `Jacobian/HolomorphicForms/ChartedSpaceComplexPoints.lean` lines 38–65). The project also proves the no-isolated-points statement directly for such spaces ([punctured_nhds_neBot_of_chartedSpaceComplex](#/node/HolomorphicForms.punctured_nhds_neBot_of_chartedSpaceComplex), `Jacobian/HolomorphicForms/ChartedSpaceComplexPoints.lean` lines 8–36).

So the requirement is satisfied, but it was never going to constrain anything: classically a constant map admits no branched-cover datum in the first place, since the fibre over y₀ is the whole infinite surface X and the datum demands finite fibres. (That argument is not in the Lean — the case split above is.) The value 0 is therefore a choice of convention.

It is the right convention, and the project is consistent about it. The public degree of a constant map is 0 ([ContMDiff.degree](#/node/ContMDiff.degree), `Jacobian/Solution.lean` lines 210–222), so the identity "the trace of a pullback is the degree times the form" reads `0 = 0` here. Downstream, [traceFormsBundled_eq_zero_of_constant](#/node/HolomorphicForms.traceFormsBundled_eq_zero_of_constant) (`Jacobian/HolomorphicForms/TraceSpec.lean` lines 2859–2873) turns this leaf into the usable statement that the bundled trace vanishes for constant maps, and that statement is what makes the linearity proof in [traceFormsBundledLM](#/node/HolomorphicForms.traceFormsBundledLM) work in the constant case.

One curiosity: the hypothesis that the input form is nonzero does no work in the regular-value proof. It is used only in the last line, to rule out the `map_zero_spec` requirement by contradiction, which is why the zero input needs its own leaf ([traceFormsConstructionData_zero](#/node/HolomorphicForms.traceFormsConstructionData_zero)).
