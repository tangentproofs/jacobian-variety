---
id: Jacobian.pullback_comp_apply
title: Pullback respects composition, contravariantly
summary: 'Pulling back along g ∘ f is pulling back along g then along f, and the underlying fact about traces of 1-forms needs a three-way case split with a branched-cover argument in the main case.'
review: draft
authors:
- claude
caveats:
- 'Stated pointwise for each `P : Jacobian Z`, not as an equality of homomorphisms.'
- 'The file docstring at Jacobian/TraceDegree/AnalyticPullbackFunctorialU.lean lines 31–41 still calls `traceFormsBundledLM_compU` a tracked frontier obligation and one of "the only sorries in this file", and the declaration''s own docstring at lines 85–87 still says "Frontier obligation (comp)". Stale: it is discharged at Jacobian/TraceDegree/AnalyticPullbackFunctorialU.lean lines 88–94 by `TraceFormsBundledCompU.traceFormsBundledLM_comp_genuineU`, and neither file has a `sorry` outside its comments.'
- 'The three surfaces X, Y, Z sit in three independent universes, pinned by hand at Jacobian/Solution.lean lines 88–90, Jacobian/Solution.lean lines 125–127 and Jacobian/Solution.lean lines 158–160, which is why [pullback](#/node/Jacobian.pullback) is built with the universe-heterogeneous lift [ULiftContinuousAddMonoidHom''](#/node/ComplexTorus.ULiftContinuousAddMonoidHom'') (Jacobian/ComplexTorus/ULiftTransport.lean lines 429–443).'
quiz:
- q: 'Which order does the law put the two pullbacks in?'
  type: choice
  choices:
  - '`pullback (g ∘ f) P = pullback f hf (pullback g hg P)`'
  - '`pullback (g ∘ f) P = pullback g hg (pullback f hf P)`'
  - 'Both, since the two composites are equal'
  answer: 0
  explain: 'Jacobian/Solution.lean lines 196–197 state the contravariant order: a point of `Jacobian Z` goes first to `Jacobian Y`, then to `Jacobian X`.'
- q: 'What is the underlying statement about 1-forms?'
  type: choice
  choices:
  - 'The trace along `g ∘ f` equals the trace along `g` of the trace along `f`'
  - 'The pullback along `g ∘ f` equals the pullback along `f` of the pullback along `g`'
  - 'The degree of `g ∘ f` is the product of the degrees'
  answer: 0
  explain: '`traceFormsBundledLM_compU` (Jacobian/TraceDegree/AnalyticPullbackFunctorialU.lean lines 88–94) states exactly the trace composition law.'
- q: 'How does the genuine proof of that trace law proceed?'
  type: choice
  choices:
  - 'By a case split: the form is zero, or one of the two maps is constant (both sides 0), or both are nonconstant, where branched-cover data for `f`, `g` and `g ∘ f` are compared at a common regular value and the identity principle extends the result'
  - 'By induction on the genus'
  - 'By assuming it as a structure field'
  answer: 0
  explain: 'Jacobian/TraceDegree/TraceFormsBundledCompU.lean lines 194–234 run exactly that case analysis; the nonconstant case delegates to `traceFormsBundled_comp_of_nonconstantU` at Jacobian/TraceDegree/TraceFormsBundledCompU.lean line 234.'
---
## Plain English

Let `f : X → Y` and `g : Y → Z` be holomorphic maps of compact Riemann surfaces. This lemma says the [pullback](#/node/Jacobian.pullback) of the composite is the composite of the pullbacks, in the reversed order: for every `P : Jacobian Z`,

  `pullback (g ∘ f) (hg.comp hf) P = pullback f hf (pullback g hg P)`

(Jacobian/Solution.lean lines 196–201). Starting at a point of J(Z), you can pull it back to J(X) directly along `g ∘ f`, or go via J(Y). The answers agree. This is the contravariant direction.

## Why it matters

The specification lists it as functoriality (Jacobian/Challenge.lean lines 143–144). With [the identity law](#/node/Jacobian.pullback_id_apply) it makes pullback a contravariant functor into complex Lie groups, which is the structure a Jacobian construction is supposed to have.

It also constrains what `pullback` can be: the composition law for traces is not something an arbitrary assignment of homomorphisms satisfies.

## How the proof goes

Jacobian/Solution.lean lines 198–201: unfold both sides past the `ULift` wrapper and rewrite with [analyticPullback_comp_applyU](#/node/TraceDegree.analyticPullback_comp_applyU) (Jacobian/TraceDegree/AnalyticPullbackFunctorialU.lean lines 164–184).

That lemma takes a representative by `QuotientAddGroup.induction_on`, applies the descent identity [analyticPullback_mk_spec_rawU](#/node/TraceDegree.analyticPullback_mk_spec_rawU) three times, and reduces to [traceDualPullbackLiftU_comp](#/node/TraceDegree.traceDualPullbackLiftU_comp) (Jacobian/TraceDegree/AnalyticPullbackFunctorialU.lean lines 132–143). A matrix transpose turns that into [traceFormsCoordU_comp](#/node/TraceDegree.traceFormsCoordU_comp) (Jacobian/TraceDegree/AnalyticPullbackFunctorialU.lean lines 114–123), whose content is [traceFormsBundledLM_compU](#/node/TraceDegree.traceFormsBundledLM_compU) (Jacobian/TraceDegree/AnalyticPullbackFunctorialU.lean lines 88–94): the trace of 1-forms composes.

That law is **proved in this repository**, by [traceFormsBundledLM_comp_genuineU](#/node/TraceDegree.TraceFormsBundledCompU.traceFormsBundledLM_comp_genuineU) (Jacobian/TraceDegree/TraceFormsBundledCompU.lean lines 194–234). The proof splits on three conditions. If the form is zero, all three traces are zero by linearity. If `f` is constant then so is `g ∘ f`, and [the trace along a constant map is zero](#/node/HolomorphicForms.traceFormsBundled_eq_zero_of_constant), so both sides vanish; the same argument covers `g` constant. If both maps are nonconstant, [traceFormsBundled_comp_of_nonconstantU](#/node/TraceDegree.TraceFormsBundledCompU.traceFormsBundled_comp_of_nonconstantU) (Jacobian/TraceDegree/TraceFormsBundledCompU.lean lines 32–191) builds branched-cover data for `f`, `g` and `g ∘ f` out of the smoothness proofs, shows the points simultaneously regular for all three are dense (the complement is covered by three finite sets), compares the traces there, and extends to all of Z by [the identity principle for holomorphic 1-forms](#/node/HolomorphicForms.holomorphicOneForm_ext_on).

Contrast [the pushforward composition law](#/node/Jacobian.pushforward_comp_apply), which reduces to the chain rule and costs nothing. The asymmetry is explained in the file docstring at Jacobian/TraceDegree/AnalyticPullbackFunctorialU.lean lines 18–29.

## What it does not say

- Not an equality of bundled homomorphisms, only pointwise.
- Nothing about degrees: `deg (g ∘ f) = deg g · deg f` is not in the public interface.
- Nothing about divisors, and no compatibility with [ofCurve](#/node/Jacobian.ofCurve).
