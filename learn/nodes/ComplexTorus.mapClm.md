---
id: ComplexTorus.mapClm
title: Lattice-preserving linear maps between tori
summary: A continuous ℂ-linear map that sends one lattice into the other descends to the tori as a plain additive homomorphism, because ℂ-scaling cannot survive the quotient; continuity is restored by a separate lemma.
review: draft
authors:
- claude
caveats:
- 'The result type is `quotient V Λ →+ quotient W Γ`, an additive homomorphism. Continuity is not part of the bundle; it is [mapClm_continuous](#/node/ComplexTorus.mapClm_continuous) (Jacobian/ComplexTorus/OfClm.lean lines 30–33). Complex linearity is not part of the bundle either, and cannot be: the tori are not ℂ-vector spaces.'
- 'The lattice hypothesis `hf : ∀ v ∈ Λ.subgroup, f v ∈ Γ.subgroup` is one-directional, so the induced map need be neither injective nor surjective. The zero map qualifies.'
- 'The body is `map Λ Γ f.toAddMonoidHom hf` — the construction is entirely [map](#/node/ComplexTorus.map); `mapClm` only changes which kind of map you hand in.'
quiz:
- q: What does `mapClm` return?
  type: choice
  choices:
  - An additive homomorphism `quotient V Λ →+ quotient W Γ`, with continuity proved separately
  - A continuous ℂ-linear map between the tori
  - A homeomorphism between the tori
  answer: 0
  explain: The signature at Jacobian/ComplexTorus/OfClm.lean lines 24–27 ends in `quotient V Λ →+ quotient W Γ`; continuity is the separate lemma at Jacobian/ComplexTorus/OfClm.lean lines 30–33.
- q: Why can the induced map not be ℂ-linear as a bundled fact?
  type: choice
  choices:
  - Because a torus is a quotient by a lattice, which is not a ℂ-subspace, so no ℂ-scalar action descends
  - Because Lean has no `→L[ℂ]` type for quotients
  - Because `f` is not assumed linear
  answer: 0
  explain: '`quotient V Λ` is `V ⧸ Λ.subgroup` as additive groups (Jacobian/ComplexTorus/Defs.lean line 74). Only `AddCommGroup` is registered on it (Jacobian/ComplexTorus/Defs.lean lines 76–77), because scaling a lattice vector by a complex number leaves the lattice.'
- q: How is the continuity of `mapClm f hf` proved?
  type: choice
  choices:
  - From `f.continuous` via the generic `map_continuous`
  - From compactness of the torus
  - By a chart computation
  answer: 0
  explain: Jacobian/ComplexTorus/OfClm.lean lines 30–33 prove it as `map_continuous f.continuous hf`.
- q: Where does `mapClm` enter the Jacobian construction?
  type: choice
  choices:
  - It is the descent step for both `pushforward` and `pullback` on the period quotient
  - It builds the charts on the Jacobian
  - It proves the period lattice is discrete
  answer: 0
  explain: Jacobian/TraceDegree/AnalyticPushforwardU.lean line 130 and Jacobian/TraceDegree/AnalyticPullbackU.lean line 102 both set `toFun := ComplexTorus.mapClm (…)`.
---
## Plain English

[map](#/node/ComplexTorus.map) descends any additive map that respects the lattices. `mapClm` is the version you reach for in practice: you start from a continuous complex-linear map `f : V →L[ℂ] W`, check that it sends the lattice `Λ` into the lattice `Γ`, and get a map of the two tori (Jacobian/ComplexTorus/OfClm.lean lines 24–27).

```
def mapClm (f : V →L[ℂ] W)
    (hf : ∀ v ∈ Λ.subgroup, f v ∈ Γ.subgroup) :
    quotient V Λ →+ quotient W Γ :=
  map Λ Γ f.toAddMonoidHom hf
```

The body throws away everything about `f` except its additivity, by calling `f.toAddMonoidHom`. So the output is only an additive homomorphism. That is not a loss: the torus genuinely has no complex scalar multiplication, because scaling a lattice vector by a complex number leaves the lattice. Additive is the right amount of structure to keep.

Continuity is restored immediately afterwards, as its own lemma (Jacobian/ComplexTorus/OfClm.lean lines 30–33), from `f.continuous`.

## Why it exists separately

The point of the wrapper is to be the shape downstream code wants. Both of the Jacobian's functorial maps are built exactly this way: an operation on holomorphic 1-forms is transposed into a continuous linear map on ℂ^g, that map is shown to carry periods to periods, and `mapClm` turns it into a map of Jacobians. The two inputs are different. For [pushforward](#/node/Jacobian.pushforward) the linear map is `pushforwardTraceLiftCLMU`, the transpose in basis coordinates of pullback of forms `f^*` (Jacobian/TraceDegree/AnalyticPushforwardU.lean lines 90–91 and 130). For [pullback](#/node/Jacobian.pullback) it is `traceDualPullbackLiftCLMU`, the transpose of the trace of forms along `f` (Jacobian/TraceDegree/PullbackTraceLiftU.lean lines 62–70; Jacobian/TraceDegree/AnalyticPullbackU.lean line 102). In each case the result is repackaged as a *continuous* additive homomorphism using `mapClm_continuous`.

## Functoriality

The two lemmas after it re-prove functoriality at the `mapClm` level (Jacobian/ComplexTorus/OfClm.lean lines 45–49 and 52–60): the identity continuous linear map induces the identity, and composition of continuous linear maps becomes composition of induced maps. Both are thin wrappers over [map_id](#/node/ComplexTorus.map_id) and [map_comp](#/node/ComplexTorus.map_comp).

Note what is *not* here: nothing says `mapClm` is injective, or that it is a covering, or that it respects degrees. Those are statements about particular `f`, and they live in the trace-and-degree layer.
