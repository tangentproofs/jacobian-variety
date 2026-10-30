---
id: HolomorphicForms.IsHolomorphicBasic
title: Holomorphic, with nothing extra attached
summary: 'Continuity plus chart-local analyticity at every point — exactly equivalent to Mathlib''s complex-analytic smoothness, and deliberately carrying no branched-cover baggage.'
review: draft
authors:
- claude
caveats:
- 'A two-field `Prop` structure, so it is just the conjunction "continuous and holomorphic at each point". It carries no data.'
- 'The point-wise field is `IsHolomorphicAt`, which is stated in the canonical charts. Atlas-independence is a separate theorem rather than part of this definition.'
- 'Equivalence with `ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω` is proved by two theorems in opposite directions, not stated as an `iff` in the file.'
quiz:
- q: 'What are the two fields of `IsHolomorphicBasic f`?'
  type: choice
  choices:
  - '`continuous : Continuous f` and `holomorphicAt : ∀ p, IsHolomorphicAt f p`'
  - Analyticity and injectivity
  - Continuity and a ramification index
  answer: 0
  explain: 'Jacobian/HolomorphicForms/HolomorphicMap.lean lines 164–166 lists exactly those two.'
- q: Why is continuity a field rather than a consequence?
  type: choice
  choices:
  - 'Because `IsHolomorphicAt` constrains the chart-local composite, not `f` itself, so it does not force `f` to be continuous'
  - Because continuity is undecidable
  - Because Mathlib has no `Continuous` predicate for manifolds
  answer: 0
  explain: '`IsHolomorphicAt f p` (Jacobian/HolomorphicForms/HolomorphicMap.lean lines 36–37) is analyticity of a composite built with partial charts; proofs in the file need continuity separately to know `f` lands in the chart source near `p`.'
- q: What does the docstring say this structure deliberately omits?
  type: choice
  choices:
  - Branched-cover and weighted-fibre data
  - The genus
  - Compactness of the source
  answer: 0
  explain: 'Jacobian/HolomorphicForms/HolomorphicMap.lean lines 159–163: "This intentionally carries no branched-cover or weighted-fiber data."'
- q: 'If you have `hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f`, can you get `IsHolomorphicBasic f`?'
  type: choice
  choices:
  - 'No, extra hypotheses are needed'
  - 'Yes, by `isHolomorphicBasic_of_contMDiff`'
  - Only when `f` is nonconstant
  answer: 1
  explain: 'Jacobian/HolomorphicForms/HolomorphicMap.lean lines 1124–1130 assembles the two fields from `hf.continuous` and `IsHolomorphicAt.of_contMDiff`.'
---
## Plain English

This is the project's plain notion of a holomorphic map `f : X → Y` between spaces charted on ℂ. It has exactly two fields:

- `continuous : Continuous f`;
- `holomorphicAt : ∀ p, IsHolomorphicAt f p` — see [IsHolomorphicAt](#/node/HolomorphicForms.IsHolomorphicAt).

Nothing else. The docstring stresses the point: it "intentionally carries no branched-cover or weighted-fiber data" (Jacobian/HolomorphicForms/HolomorphicMap.lean lines 159–163).

Continuity has to be listed separately because the point-wise condition does not imply it. `IsHolomorphicAt f p` is analyticity of a composite built from partial charts, and away from the chart sources that composite says nothing about `f`. With continuity in hand, the composite really is `f` in local coordinates near `p`.

## Why it is defined this way

The project's degree machinery needs more than holomorphy: it needs a local `k`-to-1 normal form and global conservation of the weighted fibre count. Earlier versions bundled those into one "holomorphic" structure, which makes it hard to tell what a theorem actually assumes. Splitting them out means a statement that only needs holomorphy can say so. [IsHolomorphic](#/node/HolomorphicForms.IsHolomorphic) extends this structure with the local ramification package, and [HasWeightedFiberConservation](#/node/HolomorphicForms.HasWeightedFiberConservation) is kept outside both.

## How it relates to Mathlib

The two directions are proved separately:

- `isHolomorphicBasic_of_contMDiff` (Jacobian/HolomorphicForms/HolomorphicMap.lean lines 1124–1130): complex-analytic smoothness gives this structure.
- `ContMDiff.of_isHolomorphic_and_continuous` (Jacobian/HolomorphicForms/HolomorphicMap.lean lines 525–544): the two fields give back `ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f`.

Taken together — for `X` and `Y` complex manifolds, which both theorems assume — `IsHolomorphicBasic f` and `ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f` are interchangeable. That is what lets the public API take its hypotheses in Mathlib's vocabulary — the challenge asks for `hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f` throughout — while the proofs work in the project's own.
