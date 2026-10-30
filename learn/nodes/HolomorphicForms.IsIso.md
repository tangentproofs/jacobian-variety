---
id: HolomorphicForms.IsIso
title: An invertible linear map, carrying its inverse
summary: 'Despite the `Is` prefix this is data, not a proposition: it holds the inverse map, which is why the code has to pick one by choice and then prove the pick did not matter.'
review: draft
authors:
- claude
caveats:
- 'Not a `Prop`. `IsIso f` is a structure whose first field is an actual map `inv : F →L[ℂ] E`, so two witnesses are different terms even though `IsIso.inv_unique_local` proves their `inv` fields agree.'
- 'It duplicates something Mathlib already has in bundled form (a continuous linear equivalence). The project uses its own unbundled version so the predicate can be applied directly to `mfderiv …`, whose fibre types are non-reducible synonyms for ℂ.'
- 'Consumers test `Nonempty (IsIso …)` with `if` and fall back to `0` when it fails. In `cotangentPushforward` that fallback does fire — at ramified points, where the differential is not invertible. The surrounding theory only uses the function at regular values, where it does not.'
- 'The name says nothing about holomorphy; it is pure linear algebra on complex normed spaces.'
quiz:
- q: 'What are the fields of `IsIso f`?'
  type: choice
  choices:
  - 'A map `inv`, plus proofs that `inv ∘ f` and `f ∘ inv` are the identity'
  - A proof that `f` is injective and surjective
  - 'A proof that `f ≠ 0`'
  answer: 0
  explain: 'Jacobian/TraceDegree/TraceDefinition.lean lines 70–74: `inv : F →L[ℂ] E`, `left_inv`, `right_inv`, both stated as equations between composites and `ContinuousLinearMap.id`.'
- q: Why do proofs need `IsIso.inv_unique_local`?
  type: choice
  choices:
  - 'Because the structure carries data, so a definition that picks a witness by `Classical.choice` must be shown not to depend on the pick'
  - Because inverses need not be unique
  - To prove the inverse is continuous
  answer: 0
  explain: '`cotangentPushforward` uses `Classical.choice` on `Nonempty (IsIso …)` (Jacobian/TraceDegree/TraceDefinition.lean lines 81–87); `inv_unique_local` (lines 240–250) shows any two witnesses have the same `inv`, by the usual two-sided-inverse argument.'
- q: What happens in `cotangentPushforward` when no `IsIso` witness exists?
  type: choice
  choices:
  - It is an error
  - 'It returns 0'
  - It returns the identity
  answer: 1
  explain: 'The `else` branch is `0` (Jacobian/TraceDegree/TraceDefinition.lean lines 81–87). That branch is reached at ramified points, which is why the trace is only summed over regular fibres.'
- q: 'Where does an `IsIso` witness for the differential of `f` come from?'
  type: choice
  choices:
  - It is assumed
  - 'From ramification index 1 at the point, which forces the local derivative to be nonzero; the inverse is multiplication by its reciprocal'
  - From compactness of `X`
  answer: 1
  explain: '`mfderiv_isIso_of_ramificationIndex_one` (Jacobian/TraceDegree/TraceDefinition.lean lines 254–300) builds the witness with `inv := toSpanSingleton ℂ a⁻¹`, where `a` is the chart-local derivative.'
---
## Plain English

To carry a cotangent vector from `x` down to `f x` you need to undo the differential of `f` at `x`. So the code needs a way to say "this continuous linear map has a continuous linear inverse".

`IsIso φ` is that, written out by hand for maps `φ : E →L[ℂ] F` between complex normed spaces. It has three fields: a map `inv : F →L[ℂ] E`, a proof that `inv ∘ φ` is the identity on `E`, and a proof that `φ ∘ inv` is the identity on `F`.

The `Is` prefix is misleading. This is not a proposition — it holds an actual map. That has a practical consequence everywhere it is used. A definition cannot just say "if `φ` is invertible, use its inverse"; it has to test `Nonempty (IsIso φ)`, pull a witness out with `Classical.choice`, and then face the question of whether the answer depended on which witness came out. `IsIso.inv_unique_local` (Jacobian/TraceDegree/TraceDefinition.lean lines 240–250) answers it: any two witnesses have equal `inv` fields, by the standard calculation that a left inverse and a right inverse of the same map coincide.

Mathlib has a bundled notion of continuous linear equivalence that would serve. The project uses its own because the maps in question are differentials `mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x`, whose source and target are tangent-space types that are only definitionally — not reducibly — equal to ℂ; the file sets up scoped normed-space instances on those types just so this predicate can be stated (Jacobian/TraceDegree/TraceDefinition.lean lines 43–51).

## The fallback branch

`cotangentPushforward` (Jacobian/TraceDegree/TraceDefinition.lean lines 81–87) reads:

```
if h : Nonempty (IsIso (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x)) then ωx.comp (Classical.choice h).inv else 0
```

The `else 0` is a real branch, not dead code: at a ramified point the differential vanishes and there is no inverse. It is harmless because every theorem that uses `cotangentPushforward` sums it over a fibre consisting of unramified points — see [isRegularValue](#/node/HolomorphicForms.isRegularValue). A reader should know the zero is there, and know why it is never summed.

## Where the witnesses come from

`mfderiv_isIso_of_ramificationIndex_one` (Jacobian/TraceDegree/TraceDefinition.lean lines 254–300) is the bridge from analysis to linear algebra. Ramification index 1 at `x` means [mapAnalyticOrderAt](#/node/HolomorphicForms.mapAnalyticOrderAt) is 1 there, which is equivalent to the chart-local derivative `a` being nonzero; the differential is then multiplication by `a`, and the witness takes `inv` to be multiplication by `1/a`. The explicit form feeds `cotangentPushforward_apply_one` (Jacobian/TraceDegree/TraceDefinition.lean lines 380–403), which turns the pushforward of a form into the concrete scalar `ω(1)/a` — the classical change-of-variables factor in the trace of a 1-form.
