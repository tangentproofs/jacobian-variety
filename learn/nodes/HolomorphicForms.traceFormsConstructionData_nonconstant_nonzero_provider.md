---
id: HolomorphicForms.traceFormsConstructionData_nonconstant_nonzero_provider
title: The analytic case of the trace construction
summary: The one case with real analysis in it is a four-line wrapper that picks a witness out of an existence theorem with Classical.choose.
review: draft
authors:
- claude
caveats:
- 'The trace form here is `Classical.choose`n from an existence statement. The specification does determine it uniquely (regular values are dense and holomorphic 1-forms agreeing on a dense set are equal), but this definition does not use that; a separate theorem identifies the chosen form with an explicit construction.'
- 'The hypothesis `η ≠ 0` is not used by the analytic theorem: its binder there is written `_hη` (Jacobian/HolomorphicForms/TraceSpec.lean line 2712). In this wrapper it serves only to make `map_zero_spec` vacuous, so the word "nonzero" in the name reflects the caller''s case split, not a real condition.'
- 'A step inside the existence proof, traceForm_extension_at_branch_of_canonical_BCD (Jacobian/HolomorphicForms/TraceSpec.lean lines 2665–2693), is proved by showing its hypotheses are contradictory, even though its docstring describes a continuity argument. The conclusion is still correct, but the docstring does not describe the proof.'
quiz:
- q: Where does this definition get its trace form?
  type: choice
  choices:
  - From Classical.choose applied to the existence theorem traceForm_global_extension
  - By summing over the fiber at every point of Y
  - By setting it to zero away from the branch locus
  answer: 0
  explain: 'The body is `hext.choose` with `regular_spec := hext.choose_spec` (Jacobian/HolomorphicForms/TraceSpec.lean lines 2748–2750).'
- q: What is the analytic heart of the existence theorem it wraps?
  type: choice
  choices:
  - Riemann's removable singularity theorem, applied to the fiber sum of local primitives of η near a branch value
  - The Riemann–Roch theorem
  - The residue theorem on the branch locus
  answer: 0
  explain: 'The per-datum step builds traceHolomorphicForm in Jacobian/HolomorphicForms/TraceLocal.lean lines 899–900, by extending the fiber sum of primitives across the branch point and differentiating.'
- q: Is the hypothesis η ≠ 0 needed for the construction to work?
  type: choice
  choices:
  - No; the existence theorem ignores it, and here it only makes the zero-input requirement vacuous
  - Yes; the fiber sum diverges for the zero form
  - Yes; the extension across branch points needs a nonzero form
  answer: 0
  explain: 'traceForm_global_extension takes it as `_hη` and never uses it (Jacobian/HolomorphicForms/TraceSpec.lean lines 2710–2713).'
- q: How does the existence theorem handle branched-cover data other than the canonical one?
  type: choice
  choices:
  - It transfers the agreement, using that compatible data all have the same ramification indices
  - It assumes there is only one such datum
  - It re-runs the whole extension argument for each datum
  answer: 0
  explain: 'At a regular value of the canonical datum it uses traceAtRegularValue_BCD_invariance; otherwise it shows the hypotheses cannot both hold (Jacobian/HolomorphicForms/TraceSpec.lean lines 2729–2735).'
---
## Plain English

Of the three cases of the trace construction, this is the only one with analysis in it, and the definition itself is four lines (`Jacobian/HolomorphicForms/TraceSpec.lean` lines 2743–2751). All the work sits in the theorem it quotes.

That theorem, [traceForm_global_extension](#/node/HolomorphicForms.traceForm_global_extension) (`Jacobian/HolomorphicForms/TraceSpec.lean` lines 2710–2735), says: for a smooth nonconstant f : X → Y between compact Riemann surfaces and a holomorphic 1-form η on X, *there exists* a holomorphic 1-form τ on Y that agrees with the fiber sum [traceAtRegularValue](#/node/HolomorphicForms.traceAtRegularValue) at every regular value of every compatible branched-cover datum. This definition takes that existence statement, pulls out a witness with `Classical.choose`, and uses `choose_spec` as the `regular_spec` field of [TraceFormsConstructionData](#/node/HolomorphicForms.TraceFormsConstructionData). The `map_zero_spec` field is discharged by contradiction, from the assumption that η is nonzero.

## Where the content is

The existence proof runs in two steps.

First, it fixes one branched-cover datum, the canonical one built from the fact that a nonconstant holomorphic map between compact Riemann surfaces is a finite branched cover ([branchedCoverData_of_nonconstant_holomorphic](#/node/Blueprint.branchedCoverData_of_nonconstant_holomorphic), `Jacobian/Blueprint/Sec02/BranchedDegreeFromHolomorphic.lean` lines 61–91). A private per-datum theorem then produces the form. In a chart at any point y₀ of Y, it takes local primitives of η on the fiber and sums them; that sum is holomorphic away from y₀, and continuous at y₀, so Riemann's removable singularity theorem makes it holomorphic at y₀ as well. Differentiating gives the trace ([traceHolomorphicForm](#/node/HolomorphicForms.traceHolomorphicForm), `Jacobian/HolomorphicForms/TraceLocal.lean` lines 899–900).

Second, it moves from the canonical datum to all compatible data. At a value that is regular for both, the fiber sums coincide ([traceAtRegularValue_BCD_invariance](#/node/HolomorphicForms.traceAtRegularValue_BCD_invariance)). At a value that is a branch value of the canonical datum but regular for another one, the Lean shows that cannot happen: compatibility ties each datum's ramification index to the analytic order of f, so the two data have the same branch points.

## Honesty notes

The form is chosen, not constructed, at this point in the file. That is not a gap: the specification pins it down, because regular values are dense and two holomorphic 1-forms agreeing on a dense set are equal. The project also proves separately that the chosen form *is* the explicit one, [traceFormsBundled_eq_traceHolomorphicForm](#/node/HolomorphicForms.traceFormsBundled_eq_traceHolomorphicForm) (`Jacobian/HolomorphicForms/TraceSpec.lean` lines 2971–2995), given a fibre-finiteness witness and nonconstancy of f as explicit arguments.

The "nonzero" in the name is bookkeeping. The analytic theorem never uses it.
