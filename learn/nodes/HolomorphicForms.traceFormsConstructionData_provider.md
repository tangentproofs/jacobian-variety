---
id: HolomorphicForms.traceFormsConstructionData_provider
title: Trace data for every map and every form
summary: Three branches cover every smooth map and every holomorphic 1-form, and two of the three are degenerate cases that contain no analysis at all.
review: draft
authors:
- claude
caveats:
- 'The definition is assembled by tactic-level case analysis (`by_cases`) on classically decidable propositions, so it is noncomputable and has no single uniform formula: its value is whichever leaf applies.'
- 'Two of the three branches are degenerate. The zero-form branch is arithmetic, and the constant-map branch is a convention whose specification is discharged by a case split. All analytic content is in the third branch.'
- 'The branches can still be reasoned through: traceFormsBundled_eq_zero_of_constant unfolds this definition and selects the constant branch with `simp [hη, hconst]` (Jacobian/HolomorphicForms/TraceSpec.lean lines 2858–2872).'
quiz:
- q: How does the provider split the problem?
  type: choice
  choices:
  - First on whether η is zero, then on whether f is constant
  - First on whether f is constant, then on the genus of X
  - On whether y is a regular value
  answer: 0
  explain: 'The body is `by_cases hη : η = 0` followed by `by_cases hconst : ∃ y₀, ∀ x, f x = y₀` (Jacobian/HolomorphicForms/TraceSpec.lean lines 2768–2774).'
- q: Which branch contains the analysis?
  type: choice
  choices:
  - The nonconstant, nonzero branch
  - The zero-form branch
  - The constant-map branch
  answer: 0
  explain: 'That branch delegates to traceFormsConstructionData_nonconstant_nonzero_provider, which wraps the holomorphic extension theorem (Jacobian/HolomorphicForms/TraceSpec.lean line 2774).'
- q: What hypotheses does the provider itself demand about f?
  type: choice
  choices:
  - Only smoothness; it produces data for constant and nonconstant maps alike
  - That f is nonconstant
  - That f admits a compatible branched-cover datum
  answer: 0
  explain: 'Its signature takes `f` and `hf : ContMDiff …` and nothing else (Jacobian/HolomorphicForms/TraceSpec.lean lines 2763–2766).'
- q: Why is the result noncomputable?
  type: choice
  choices:
  - The case split uses classical decidability and the hard branch uses Classical.choose
  - Because fiber sums are infinite
  - Because HolomorphicOneForm has no decidable equality
  answer: 0
  explain: 'The proof opens with `classical` and the third leaf extracts a witness with `Classical.choose`.'
---
## Plain English

This is the single entry point for the trace construction. Given any smooth map f : X → Y between compact Riemann surfaces and any holomorphic 1-form η on X, it produces an element of [TraceFormsConstructionData](#/node/HolomorphicForms.TraceFormsConstructionData): a global trace form on Y together with proofs of the two requirements.

It works by a three-way case split (`Jacobian/HolomorphicForms/TraceSpec.lean` lines 2763–2774).

If η is zero, the trace is zero, by [traceFormsConstructionData_zero](#/node/HolomorphicForms.traceFormsConstructionData_zero). The Lean uses `cases hη` to replace η by the literal zero form so the types match.

If η is nonzero and f is constant, the trace is zero, by [traceFormsConstructionData_constant](#/node/HolomorphicForms.traceFormsConstructionData_constant). That leaf is a convention: it discharges the regular-value requirement by a case split — off the image point the fibre is empty, and at the image point a branched-cover datum would make a singleton open in Y.

Otherwise f is nonconstant and η is nonzero, and the work is handed to [traceFormsConstructionData_nonconstant_nonzero_provider](#/node/HolomorphicForms.traceFormsConstructionData_nonconstant_nonzero_provider), which wraps the holomorphic extension theorem.

## Why it is organised this way

The project's stated policy is to keep each piece of analysis in the smallest possible declaration. Splitting the construction here means the one genuinely analytic obligation is a single leaf with narrow hypotheses, and the two easy cases cannot hide behind it.

The price is that this definition is noncomputable and case-dependent: it is not a formula, it is "whichever of three leaves applies". That is normally awkward to reason about, but downstream proofs can still see through it. [traceFormsBundled_eq_zero_of_constant](#/node/HolomorphicForms.traceFormsBundled_eq_zero_of_constant) (`Jacobian/HolomorphicForms/TraceSpec.lean` lines 2858–2872) unfolds the provider and picks out the constant branch with `simp [hη, hconst]`, which is how the constant-map case gets used later.

Everything above this point in the project reads only the fields. [traceFormsBundled](#/node/HolomorphicForms.traceFormsBundled) is literally the `traceForm` field of this provider.
