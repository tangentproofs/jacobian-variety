---
id: HolomorphicForms.traceFormsConstructionData_zero
title: Trace of the zero 1-form
summary: The trace of the zero form is the zero form, and the proof uses no branch structure at all because every summand of every fiber sum is already zero.
review: draft
authors:
- claude
caveats:
- 'This is a `private` declaration: it is not part of the project''s public API and is reachable only through the provider.'
- 'It is stated for the literal form `(0 : HolomorphicOneForm ℂ X)`, not for an arbitrary `η` with a proof that `η = 0`. The provider has to substitute (`cases hη`) before it can use this leaf.'
- The smoothness hypothesis `hf` is taken as an argument because it indexes the result type `TraceFormsConstructionData f hf 0`, but it plays no part in either proof.
quiz:
- q: What global form does this leaf supply?
  type: choice
  choices:
  - The zero holomorphic 1-form on Y
  - The fiber sum extended by continuity
  - A form chosen with Classical.choose
  answer: 0
  explain: 'The field is `traceForm := 0` (Jacobian/HolomorphicForms/TraceSpec.lean line 128).'
- q: How is regular_spec proved here?
  type: choice
  choices:
  - Every summand of the fiber sum is the pushforward of the zero covector, which is zero
  - By Riemann's removable singularity theorem
  - By showing that no regular value exists
  answer: 0
  explain: 'It reduces to traceAtRegularValue_zero (Jacobian/HolomorphicForms/TraceSpec.lean lines 102–110), which applies cotangentPushforward_zero to each summand.'
- q: Does this leaf cover an arbitrary form η that happens to equal zero?
  type: choice
  choices:
  - Not directly; it is typed at the literal zero form, so the caller must substitute first
  - Yes, it takes η and a proof that η = 0
  - Yes, it covers every η
  answer: 0
  explain: 'Its type is `TraceFormsConstructionData f hf (0 : HolomorphicOneForm ℂ X)` (Jacobian/HolomorphicForms/TraceSpec.lean line 127), and the provider uses `cases hη` to get there.'
- q: Which hypothesis about f does this leaf need?
  type: choice
  choices:
  - None beyond the ambient compact Riemann surface assumptions; even the smoothness argument is unused
  - That f is nonconstant
  - That f has a compatible branched-cover datum
  answer: 0
  explain: 'Both fields are proved without touching `hf` (Jacobian/HolomorphicForms/TraceSpec.lean lines 125–148).'
---
## Plain English

This is the easiest of the three cases of the trace construction: the input form is zero.

It supplies an element of [TraceFormsConstructionData](#/node/HolomorphicForms.TraceFormsConstructionData) whose global form is the zero 1-form on Y, and it checks both requirements.

`regular_spec` says the zero form on Y agrees with the fiber sum at every regular value of every compatible branched-cover datum. That holds summand by summand: pushing the zero covector forward gives the zero covector, in both branches of the `if` inside [cotangentPushforward](#/node/HolomorphicForms.cotangentPushforward) (`Jacobian/HolomorphicForms/TraceSpec.lean` lines 90–97), so the whole finite sum is zero ([traceAtRegularValue_zero](#/node/HolomorphicForms.traceAtRegularValue_zero), `Jacobian/HolomorphicForms/TraceSpec.lean` lines 102–110). No property of f, no branch locus, no analysis.

`map_zero_spec` says that a zero input gives a zero output. Here the output is already the zero form, so the proof is `rfl`.

Most of the Lean in this declaration is bookkeeping: `HolomorphicOneForm` is a bundled section type, so the proof has to unfold "the zero section evaluated at a point" into "the zero covector" before `simp` can finish (`Jacobian/HolomorphicForms/TraceSpec.lean` lines 125–148).

## How it is used

[traceFormsConstructionData_provider](#/node/HolomorphicForms.traceFormsConstructionData_provider) splits on whether the input form is zero. In the zero branch it rewrites the form to the literal `0` and hands over to this leaf. Because the leaf is typed at the literal zero form rather than at an arbitrary form together with a proof that it vanishes, the provider needs `cases hη` to make the types line up.

Splitting the zero case off is what lets the two harder leaves assume the input form is nonzero. In fact neither of them really needs that assumption: the constant-map leaf uses it only to discharge `map_zero_spec` by contradiction, and the analytic existence theorem ignores it entirely. So this leaf exists mostly to keep the case split clean.
