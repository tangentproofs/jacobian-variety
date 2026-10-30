---
id: HolomorphicForms.cotangentPushforward
title: Pushing a covector forward through the derivative
summary: Pushing a cotangent vector forward needs the derivative to be invertible, so the definition quietly returns zero at every point where it is not.
review: draft
authors:
- claude
caveats:
- 'The inverse of the derivative is produced by `Classical.choice` from a nonempty `IsIso`. The choice does not matter, and the same file proves it: `IsIso.inv_unique_local` (Jacobian/TraceDegree/TraceDefinition.lean lines 240–250) shows any two witnesses carry the same `inv`.'
- 'The `else` branch returns the zero covector whenever the derivative is not invertible. The classical pushforward is undefined there, so a use at a ramification point reads as 0 rather than as an error.'
- No holomorphy, smoothness or nonconstancy of `f` is assumed. The definition accepts any function `X → Y`; the invertibility test is made on `mfderiv` inside the body.
quiz:
- q: At a point where the derivative of f is not invertible, what does cotangentPushforward return?
  type: choice
  choices:
  - The zero covector
  - The covector ωx unchanged
  - Nothing; the definition does not apply there
  answer: 0
  explain: 'The body is `if h : Nonempty (IsIso …) then ωx.comp … else 0` in Jacobian/TraceDegree/TraceDefinition.lean lines 84–87.'
- q: How is the pushed-forward covector built out of ωx?
  type: choice
  choices:
  - By composing ωx with the inverse of the derivative of f at x
  - By composing ωx with the derivative of f at x
  - By integrating ωx over the fiber through x
  answer: 0
  explain: 'The Lean writes `ωx.comp (Classical.choice h).inv`, so a tangent vector at f x is first carried back to x.'
- q: Why does the use of Classical.choice not leave the value ambiguous?
  type: choice
  choices:
  - A two-sided inverse of a linear map is unique, and the choice depends only on the proposition that one exists
  - Because the fallback value is 0
  - Because Lean's choice operator is computable
  answer: 0
  explain: 'All witnesses of `IsIso` (Jacobian/TraceDegree/TraceDefinition.lean lines 70–74) carry the same `inv` — proved as `IsIso.inv_unique_local` (Jacobian/TraceDegree/TraceDefinition.lean lines 240–250) — and `Nonempty …` is a proposition, so the picked witness does not depend on how invertibility was proved.'
- q: Which hypothesis on f does this definition require?
  type: choice
  choices:
  - None; f is an arbitrary function from X to Y
  - That f is holomorphic
  - That f is a nonconstant branched cover
  answer: 0
  explain: 'The signature in Jacobian/TraceDegree/TraceDefinition.lean lines 81–83 takes a bare `f : X → Y`; the invertibility test is made on `mfderiv` inside the body.'
---
## Plain English

A cotangent vector, or covector, at a point x of X is a continuous ℂ-linear map from the tangent line at x to ℂ: see [CotangentSpace](#/node/HolomorphicForms.CotangentSpace) (`Jacobian/HolomorphicForms/CotangentBundle.lean` lines 78–82). A holomorphic 1-form is a covector at every point, varying analytically ([HolomorphicOneForm](#/node/HolomorphicForms.HolomorphicOneForm), `Jacobian/HolomorphicForms/Defs.lean` lines 23–29).

Covectors move backwards along maps for free. Given f : X → Y and a covector at f x, composing with the derivative of f at x gives a covector at x. Pushing a covector *forward* goes against the grain, and it only works when the derivative can be inverted. This definition does exactly that:

(f∗ω)(v) = ω(df_x⁻¹ v) for a tangent vector v at f x.

In Lean the derivative is `mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x`, and invertibility means that the structure [IsIso](#/node/HolomorphicForms.IsIso) is nonempty: a continuous linear map back, with both composites the identity (`Jacobian/TraceDegree/TraceDefinition.lean` lines 70–74). `Classical.choice` picks a witness, and the definition composes ω with its `inv`.

Two honest observations.

The choice is harmless. A two-sided inverse of a linear map is unique, so every witness carries the same `inv`; the same file proves it as `IsIso.inv_unique_local` (`Jacobian/TraceDegree/TraceDefinition.lean` lines 240–250). And the witness depends only on the proposition `Nonempty (IsIso …)`, not on how invertibility was established.

The fallback is real. If the derivative is not invertible, the answer is the zero covector. That happens at a ramification point, where f looks like z ↦ z^k with k ≥ 2 in charts and the derivative vanishes. So the definition never fails, but at such a point it returns 0 rather than the (nonexistent) classical pushforward.

Callers avoid the fallback deliberately: [mfderiv_isIso_of_ramificationIndex_one](#/node/HolomorphicForms.mfderiv_isIso_of_ramificationIndex_one) (`Jacobian/TraceDegree/TraceDefinition.lean` lines 254–300) proves the derivative is invertible at an unramified point of a compatible branched cover.

## How it is used

This is one summand of the fiber sum in [traceAtRegularValue](#/node/HolomorphicForms.traceAtRegularValue), the local form of the trace. Two small facts about it get used repeatedly: it sends the zero covector to zero ([cotangentPushforward_zero](#/node/HolomorphicForms.cotangentPushforward_zero), `Jacobian/HolomorphicForms/TraceSpec.lean` lines 90–97), and it is additive and ℂ-homogeneous in ω in *both* branches of the `if`, which is what makes the trace sum linear (`Jacobian/TraceDegree/TraceDefinition.lean` lines 504–539).
