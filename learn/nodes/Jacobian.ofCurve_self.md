---
id: Jacobian.ofCurve_self
title: The base point lands on zero
summary: 'The base point maps to the identity of the Jacobian not because the integral from P to P is zero, but because the chosen loop''s integral is a period and periods are zero in the quotient.'
review: draft
authors:
- claude
caveats:
- 'The underlying vector `pathIntegralFunctionalU X P P` is in general **not** the zero vector. The chain from P to P is chosen by `Classical.choose` and may be any closed chart chain, so its integral is some lattice element. The theorem is about the class, and the proof is `mk_eq_zero_iff`, not `rfl`.'
- 'This says nothing about where any other point goes, and nothing about the map being a group homomorphism. X carries no group structure.'
quiz:
- q: Why is `ofCurve P P = 0` not true by definitional unfolding?
  type: choice
  choices:
  - 'Because the chosen chain from P to P can be a nontrivial loop, whose integral is a period rather than the zero vector'
  - 'Because the Jacobian has no zero element'
  - 'Because integration is not defined at a single point'
  answer: 0
  explain: 'Jacobian/AbelJacobi/AnalyticOfCurveU.lean lines 57–58 prove it through `mk_eq_zero_iff` and `pathIntegralFunctionalU_self_mem`: the self-integral lies in the period subgroup.'
- q: Which property of the period lattice does the proof use?
  type: choice
  choices:
  - That it is discrete
  - 'That the period vector of a closed chain is a member of it'
  - That it has rank 2g
  answer: 1
  explain: '`pathIntegralFunctionalU_self_mem` (Jacobian/AbelJacobi/PathIntegralFunctionalU.lean lines 66–68) is `periodVector_mem_of_loop` applied to the chosen chain from P to P.'
- q: 'What is the `0` on the right-hand side?'
  type: choice
  choices:
  - The real number zero
  - 'The identity element of the additive group `Jacobian X`'
  - The empty chain
  answer: 1
  explain: '`Jacobian X` is an `AddCommGroup` (Jacobian/Solution.lean line 94), lifted from the quotient group ℂ^g/Λ, so `0` is its neutral element.'
---
## Plain English

The [Abel–Jacobi map](#/node/Jacobian.ofCurve) with base point P sends a point Q to the integrals from P to Q, modulo periods. This lemma says that the base point itself is sent to the zero element of the Jacobian:

  `ofCurve P P = 0`

(Jacobian/Solution.lean lines 115–117).

The interesting part is why this is not automatic. To compute `ofCurve P P` the definition needs a chain from P to P, and it gets one by [Classical choice](#/node/AbelJacobi.chosenChain). There is no reason for that choice to be the empty chain. It can be a loop that wraps around the surface, and then the raw vector of integrals is a nonzero element of ℂ^g. What the lemma really says is that whatever loop was chosen, its integral vector is a *period*, and periods are exactly the elements that become zero in the quotient.

## Why it matters

It is one of the three properties the specification asks of `ofCurve` (Jacobian/Challenge.lean line 95). Together with holomorphy and injectivity it fixes the normalisation: the map is not just injective, it is injective and pointed, sending the base point to the group identity. Classically that is what makes the Abel–Jacobi map a map of pointed spaces, the first step towards the divisor-level statement.

## How the proof goes

Two steps (Jacobian/Solution.lean lines 115–117): rewrite the goal through the `ULift` wrapper, then apply [analyticOfCurve_selfU](#/node/AbelJacobi.analyticOfCurve_selfU) (Jacobian/AbelJacobi/AnalyticOfCurveU.lean lines 57–58), and close with `rfl` because `ULift.up 0` is `0`.

The analytic lemma is `(mk_eq_zero_iff Λ).mpr` applied to [pathIntegralFunctionalU_self_mem](#/node/AbelJacobi.pathIntegralFunctionalU_self_mem) (Jacobian/AbelJacobi/PathIntegralFunctionalU.lean lines 66–68). That in turn is `periodVector_mem_of_loop` applied to `chosenChain_isChain X P P`: the chosen chain starts and ends at P, so it is a loop, and the [period subgroup](#/node/Periods.genuinePeriodSubgroup) contains the period vector of every loop by construction (closed chains are the generators with the second chain empty).

So the whole content is the design of the lattice. It was built to contain exactly the ambiguities of path integration, and the self-integral is one of those ambiguities.

## What it does not say

- Not that the integral from P to P is literally zero. Only its class is.
- Nothing about `ofCurve P Q` for `Q ≠ P`, and nothing about `ofCurve P` being additive or a homomorphism.
- No relation between `ofCurve P` and `ofCurve P'` for a second base point.
