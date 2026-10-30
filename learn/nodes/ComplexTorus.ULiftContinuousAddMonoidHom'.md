---
id: "ComplexTorus.ULiftContinuousAddMonoidHom'"
title: Universe plumbing for maps between Jacobians
summary: This definition carries no mathematics at all; it exists because the challenge spec demands that the Jacobian of a surface in universe u live in universe u.
review: draft
authors:
- claude
caveats:
- 'There is no mathematical content here. The map is `a ↦ ULift.up (φ a.down)`: unwrap, apply, rewrap. `map_zero''` and `map_add''` are `simp` plus `rfl`; continuity is a composition of three continuous maps.'
- 'It is stated for `AddMonoid`, not `AddCommGroup`, and for arbitrary topological spaces — nothing about tori, lattices or Riemann surfaces appears in the signature. The `ComplexTorus` namespace is where it happens to live.'
- 'It is marked `noncomputable` even though every component computes. That is incidental, not meaningful.'
- 'The prime distinguishes it from `ULiftContinuousAddMonoidHom` (Jacobian/ComplexTorus/ULiftTransport.lean lines 405–419), which forces source and target to the *same* universe level. The primed version allows two independent levels, which is what `pushforward` and `pullback` need; the unprimed version is defined but used nowhere in `Jacobian/`.'
quiz:
- q: What does `ULiftContinuousAddMonoidHom'` do to a continuous additive homomorphism φ?
  type: choice
  choices:
  - Wraps it so it acts on `ULift` copies of its source and target, at two independent universe levels
  - Extends it from a torus to its universal cover
  - Makes it complex-linear
  answer: 0
  explain: Jacobian/ComplexTorus/ULiftTransport.lean lines 432–433 give the type `ULift.{u} A →ₜ+ ULift.{v} B` and the function `fun a => ULift.up (φ a.down)`.
- q: Why does the project need the primed, two-level version at all?
  type: choice
  choices:
  - 'Because `pushforward` and `pullback` relate two curves `X : Type u_1` and `Y : Type u_2` in independent universes'
  - Because the unprimed version is unsound
  - Because the Jacobian is infinite-dimensional
  answer: 0
  explain: The docstring at Jacobian/ComplexTorus/ULiftTransport.lean lines 425–428 says the public functorial block "has its source and target curves in independent universes", and the solution pins them as `u_1`, `u_2` and `u_3` at Jacobian/Solution.lean line 88, Jacobian/Solution.lean line 125 and Jacobian/Solution.lean line 158.
- q: Does this definition assume the spaces are groups?
  type: choice
  choices:
  - No; the hypotheses are `AddMonoid A`, `AddMonoid B` and topologies on each
  - Yes; `AddCommGroup` on both
  - Yes; it requires both to be complex tori
  answer: 0
  explain: The binders at Jacobian/ComplexTorus/ULiftTransport.lean lines 430–431 are `[AddMonoid A] [AddMonoid B] [TopologicalSpace A] [TopologicalSpace B]`.
- q: How is continuity of the lifted map proved?
  type: choice
  choices:
  - By composing `continuous_uliftUp`, `φ.continuous` and `continuous_uliftDown`
  - By compactness of the torus
  - It is assumed as a field
  answer: 0
  explain: Jacobian/ComplexTorus/ULiftTransport.lean lines 442–443 read `continuous_toFun := continuous_uliftUp.comp (φ.continuous.comp continuous_uliftDown)`.
---
## Plain English

Lean sorts types into a hierarchy of universes. The challenge specification insists that for a surface `X : Type u`, its Jacobian is also in `Type u` (Jacobian/Challenge.lean lines 56–60). But the thing the project actually builds — ℂ^g modulo the period lattice — sits in the lowest universe, because ℂ and `Fin g` do. So [Jacobian](#/node/Jacobian) is defined as a `ULift` of that quotient: a one-field wrapper that carries the same data up to the universe Lean demands (Jacobian/Solution.lean lines 74–77).

Having wrapped the Jacobian, every map between Jacobians has to be wrapped too. That is all this definition does (Jacobian/ComplexTorus/ULiftTransport.lean lines 429–443): take a continuous additive homomorphism `φ : A →ₜ+ B`, and produce the homomorphism between the wrapped versions that unwraps its input, applies `φ`, and wraps the result.

```
toFun a := ULift.up (φ a.down)
```

The three things that have to be checked — that it sends zero to zero, that it is additive, and that it is continuous — each hold because unwrapping and wrapping are themselves additive and continuous. The first two are a `simp` and a `rfl`; the third composes three continuous maps.

## The prime

There are two versions in the file. The unprimed [ULiftContinuousAddMonoidHom](#/node/ComplexTorus.ULiftContinuousAddMonoidHom) (Jacobian/ComplexTorus/ULiftTransport.lean lines 405–419) sends `ULift.{u} A` to `ULift.{u} B`, the same level on both sides. The primed one (Jacobian/ComplexTorus/ULiftTransport.lean lines 429–443) allows `ULift.{u} A → ULift.{v} B`, two unrelated levels.

The primed version is the one the public interface needs. `pushforward` goes from the Jacobian of `X : Type u_1` to the Jacobian of `Y : Type u_2`, and those are different universe parameters by design — the comparator that checks the solution against the frozen spec compares universe parameter *names* literally, so the solution pins them (Jacobian/Solution.lean lines 82–88).

## Where it is used

Exactly twice: to define [pushforward](#/node/Jacobian.pushforward) (Jacobian/Solution.lean lines 132–136) and [pullback](#/node/Jacobian.pullback) (Jacobian/Solution.lean lines 172–176). The real content of those maps sits inside the `analyticPushforwardU` and `analyticPullbackU` arguments: pulling 1-forms back along `f` for the first, taking the trace of 1-forms along `f` for the second, each transposed into coordinates. This definition only moves them to the right floor of the universe hierarchy.
