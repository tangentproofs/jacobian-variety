---
id: HolomorphicForms.TraceFormsConstructionData
title: What counts as a global trace form
summary: A record saying what a global trace form must satisfy; its main requirement is empty for a constant map, which is why it carries a second requirement at all.
review: draft
authors:
- claude
caveats:
- This is a data definition, not a theorem. By itself it asserts nothing; all content is in the providers that produce an element of it.
- 'The smoothness hypothesis `hf` is an index of the structure and appears in neither field, so the record constrains nothing about smoothness. It is there so that producers can use it and so that downstream maps can be indexed by it.'
- 'For a constant `f`, `regular_spec` has no force: no `BranchedCoverData` for a constant map can exist (the fibre over the image point is all of `X`, and `finite_fiber` demands a finite fibre), so there is nothing to quantify over. That inference is not formalised; the Lean''s constant-map leaf instead discharges `regular_spec` against a hypothetical datum. Either way `traceForm := 0` is a convention there, not a derived value.'
quiz:
- q: Is TraceFormsConstructionData a theorem or a definition?
  type: choice
  choices:
  - A structure definition; it only says what a solution looks like
  - A theorem asserting that the trace form exists
  - A theorem asserting that the trace form is unique
  answer: 0
  explain: 'It is declared `structure … where` with one data field and two proof fields (Jacobian/HolomorphicForms/TraceSpec.lean lines 71–85); existence comes later, from the providers.'
- q: What does regular_spec quantify over?
  type: choice
  choices:
  - Every compatible branched-cover datum on f and every regular value of it
  - One canonical branched-cover datum chosen in advance
  - Every point of Y
  answer: 0
  explain: 'The field begins `∀ (hbc : BranchedCoverData X Y f) (_hcompat : hbc.RamificationIndexCompatible) (y : Y) (hy : isRegularValue hbc y)` (Jacobian/HolomorphicForms/TraceSpec.lean lines 80–83).'
- q: What does map_zero_spec add that regular_spec does not?
  type: choice
  choices:
  - A direct guarantee that a zero input gives a zero trace form, which regular_spec cannot give when there is no branched-cover datum to quantify over
  - Linearity of the trace in the input form
  - Holomorphy of the trace form
  answer: 0
  explain: 'regular_spec constrains `traceForm` only at regular values of branched-cover data on f; a constant map admits none, so without `map_zero_spec` nothing would pin the trace down there. `traceFormsBundled_eq_zero_of_constant` (Jacobian/HolomorphicForms/TraceSpec.lean lines 2858–2872) is where `map_zero_spec` is cashed in.'
- q: For a nonconstant f, does the record determine traceForm uniquely?
  type: choice
  choices:
  - Yes, because the regular values are dense and holomorphic 1-forms agreeing on a dense set are equal
  - No, two different trace forms can satisfy both fields
  - Only up to adding a constant form
  answer: 0
  explain: 'Uniqueness follows from regularLocus_dense (Jacobian/HolomorphicForms/TraceSpec.lean lines 278–287) and holomorphicOneForm_ext_on (Jacobian/HolomorphicForms/TraceSpec.lean lines 2789–2831), though the record itself does not state it.'
---
## Plain English

[traceAtRegularValue](#/node/HolomorphicForms.traceAtRegularValue) only defines the trace at regular values of f. Finitely many points of Y are branch values ([branchLocus_finite](#/node/HolomorphicForms.branchLocus_finite), `Jacobian/HolomorphicForms/TraceSpec.lean` lines 237–251), and the fiber-sum formula breaks down there, because the derivative is not invertible at a ramification point. The classical theorem is that the fiber sum nevertheless extends to a holomorphic 1-form on the whole of Y.

This structure states what such an extension is. It has one piece of data and two requirements.

`traceForm` — a holomorphic 1-form on Y.

`regular_spec` — for every branched-cover datum on f whose ramification indices agree with the chart-local analytic order of f, and for every regular value y of that datum, `traceForm` at y equals the fiber sum at y. Quantifying over *all* compatible data, rather than one chosen datum, is what keeps the requirement free of a hidden choice.

`map_zero_spec` — if the input form is 0, then `traceForm` is 0.

The second requirement looks redundant, and for nonconstant maps it is: regular values are dense, so `regular_spec` already determines `traceForm` completely. It is needed because `regular_spec` can say nothing at all. A constant map f carries no branched-cover datum, since the `finite_fiber` field would require the fiber over the image point — all of X — to be finite. With no datum to quantify over, `regular_spec` is vacuous, and the trace along a constant map would be entirely unconstrained. (The Lean does not state "a constant map has no datum"; its constant-map leaf discharges `regular_spec` against a hypothetical one instead. See [traceFormsConstructionData_constant](#/node/HolomorphicForms.traceFormsConstructionData_constant).)

## Why it is set up this way

The structure is an interface. It lets the project put all the analysis in one place: the only hard step is producing an element of this type for a nonconstant map and a nonzero form, which is [traceFormsConstructionData_nonconstant_nonzero_provider](#/node/HolomorphicForms.traceFormsConstructionData_nonconstant_nonzero_provider). Everything else reads the fields.

Note that the smoothness hypothesis `hf` sits in the structure's type but in neither of its fields. The record therefore makes no claim involving smoothness; `hf` is there so that providers can use it, and so that the resulting maps can be indexed by the same hypothesis the public API uses.

What the record does *not* contain: linearity in the input form. That has to be recovered afterwards, in [traceFormsBundledLM](#/node/HolomorphicForms.traceFormsBundledLM).
