---
id: ComplexTorus.mk
title: Wrapping a vector into the torus
summary: The projection from the vector space to its torus is a bare function, not a bundled homomorphism; its additivity, continuity, openness and analyticity are all separate lemmas.
review: draft
authors:
- claude
caveats:
- 'The name `mk` collides with Lean''s own structure-constructor convention. This `mk` is the quotient projection `V → quotient V Λ`, not the constructor of [FullComplexLattice](#/node/ComplexTorus.FullComplexLattice).'
- '`mk` is typed `V → quotient V Λ`, a plain function. It is definitionally `QuotientAddGroup.mk`, so every fact about Mathlib''s projection applies, but the Lean does not bundle it as an `AddMonoidHom` or a continuous map here.'
- 'The definition sits inside a `noncomputable section` (Jacobian/ComplexTorus/Defs.lean line 26); the underlying `QuotientAddGroup.mk` itself computes.'
quiz:
- q: What is `mk V Λ`?
  type: choice
  choices:
  - The quotient projection `V → quotient V Λ`, defined as `QuotientAddGroup.mk`
  - The constructor of the `FullComplexLattice` structure
  - A chart on the torus
  answer: 0
  explain: 'Jacobian/ComplexTorus/Defs.lean lines 124–125 define `mk (Λ : FullComplexLattice V) : V → quotient V Λ := QuotientAddGroup.mk`.'
- q: Is `mk` surjective, and how is that known?
  type: choice
  choices:
  - Yes; `mk_surjective` passes straight to Mathlib's `QuotientAddGroup.mk_surjective`
  - Yes, but only when the lattice is discrete
  - No; the projection misses the points outside the fundamental domain
  answer: 0
  explain: Jacobian/ComplexTorus/Defs.lean lines 127–128 prove `Function.Surjective (mk V Λ)` by `QuotientAddGroup.mk_surjective`, with no extra hypotheses.
- q: Does the type of `mk` record that it is additive?
  type: choice
  choices:
  - No; it is a plain function type, and additivity is a separate lemma
  - Yes; it is typed `V →+ quotient V Λ`
  - Yes; it is typed `V →L[ℂ] quotient V Λ`
  answer: 0
  explain: The declared type at Jacobian/ComplexTorus/Defs.lean line 124 is `V → quotient V Λ`. Facts such as `mk_add` and `mk_zero` are proved as named lemmas elsewhere in the layer.
- q: Why is surjectivity of `mk` load-bearing for the charts?
  type: choice
  choices:
  - Every torus point needs a representative vector to build its chart around, obtained by `Function.surjInv` of `mk_surjective`
  - It proves the torus is compact
  - It proves the lattice is discrete
  answer: 0
  explain: '`chartAtPoint` at Jacobian/ComplexTorus/ChartedSpace.lean lines 32–40 begins `let v : V := Function.surjInv (mk_surjective V Λ) q`.'
---
## Plain English

A point of the torus is a whole family of vectors in `V`, all differing by lattice vectors. `mk` is the map that takes one vector and hands back the family it belongs to. On the classical doughnut, `mk` is "take a complex number and remember only where it lands after you fold the plane up".

In Lean (Jacobian/ComplexTorus/Defs.lean lines 124–125):

```
def mk (Λ : FullComplexLattice V) : V → quotient V Λ :=
  QuotientAddGroup.mk
```

That is the whole definition. It is Mathlib's quotient-group projection under a project-local name, so it needs no proof of anything, and every lemma Mathlib has about `QuotientAddGroup.mk` transfers by definitional unfolding. The companion lemma right below it records surjectivity (Jacobian/ComplexTorus/Defs.lean lines 127–128): every point of the torus comes from some vector.

## Why it is a bare function

`mk` is not bundled as an additive homomorphism or as a continuous map. The project instead proves the individual facts it needs as named lemmas in this layer: `mk_zero` (Jacobian/ComplexTorus/Mk.lean line 12), `mk_eq_iff` (Jacobian/ComplexTorus/Mk.lean lines 18–20), `mk_add` (Jacobian/ComplexTorus/Add.lean lines 17–18), `mk_neg` (Jacobian/ComplexTorus/Neg.lean line 17), [mk_continuous](#/node/ComplexTorus.mk_continuous) and [mk_isOpenMap](#/node/ComplexTorus.mk_isOpenMap) (Jacobian/ComplexTorus/Basic.lean lines 16–17 and 24–25), and [contMDiff_mk](#/node/ComplexTorus.contMDiff_mk) (Jacobian/ComplexTorus/MkSmooth.lean line 32). Keeping the type plain means a chart-building argument can treat `mk` as an ordinary function and apply exactly the property it needs at each step.

## How it is used

Two uses matter for the Jacobian story.

First, the charts. A chart at a torus point `q` works by picking a representative vector for `q` and inverting `mk` on a small ball around it. The representative comes from surjectivity, via `Function.surjInv` (Jacobian/ComplexTorus/ChartedSpace.lean lines 32–40). This is the step where `Classical.choice` enters the construction: no canonical representative is chosen, just some representative.

Second, compactness. The proof that the torus is compact pushes the compact fundamental domain forward along `mk` and shows the image is everything (Jacobian/ComplexTorus/Defs.lean lines 97–112).

Both uses go through [mk_surjective](#/node/ComplexTorus.mk_surjective).
