---
id: genus
title: genus — the public declaration
summary: This is the one-line declaration that fills in the challenge's `genus` stub, and the number it produces also fixes the dimension of the Jacobian.
review: draft
authors:
- claude
caveats:
- 'This declaration adds no mathematics. It is a wrapper: its body is `JacobianChallenge.Solution.genus (X := X)` (Jacobian/Solution.lean lines 59–62). All the content is in [Solution.genus](#/node/Solution.genus).'
- 'It exists to match the frozen specification exactly. Jacobian/Challenge.lean lines 43–45 declares `genus` with the same signature and body `sorry`; the solution must present a declaration with that name, in the root namespace, with those binders in that order.'
- 'The genus here is the analytic genus, the ℂ-dimension of the space of holomorphic 1-forms. The project proves its topological meaning only at zero, via [genus_eq_zero_iff_homeo](#/node/genus_eq_zero_iff_homeo): genus 0 iff X is homeomorphic to the 2-sphere. No statement relating this number to handles or to H₁(X, ℤ) is proved for positive genus.'
- 'The solution''s declaration is `noncomputable def` where the challenge stub is a plain `def`. That is a compilation attribute, not a change of statement or type.'
quiz:
- q: What does this `genus` declaration do?
  type: choice
  choices:
  - It delegates to `JacobianChallenge.Solution.genus`, which is the `finrank` of the space of holomorphic 1-forms
  - It computes the number of handles from a triangulation
  - It is still a `sorry`
  answer: 0
  explain: The body at Jacobian/Solution.lean lines 59–62 is `JacobianChallenge.Solution.genus (X := X)`, defined at Jacobian/Solution.lean lines 43–45.
- q: Why is there both a `Solution.genus` and a bare `genus`?
  type: choice
  choices:
  - The bare name, binders and namespace must match the frozen challenge file exactly
  - They compute different numbers
  - The bare one is faster
  answer: 0
  explain: Jacobian/Challenge.lean lines 43–45 declares `genus` in the root namespace with body `sorry`; the solution mirrors that signature and delegates.
- q: Besides naming a number, what does `genus X` control in the rest of the specification?
  type: choice
  choices:
  - The dimension of the Jacobian, which is built as a quotient of `Fin (genus X) → ℂ`
  - The number of charts on X
  - The degree of a holomorphic map out of X
  answer: 0
  explain: '[Jacobian](#/node/Jacobian) at Jacobian/Solution.lean lines 74–77 is a quotient of `Fin (genus X) → ℂ`, and the charted-space and Lie-group instances at Jacobian/Solution.lean lines 96–101 are stated over that same model space.'
- q: Does the project prove that this number equals the topological genus of X?
  type: choice
  choices:
  - Only in the case genus 0, where it is equivalent to X being homeomorphic to a sphere
  - Yes, for every compact Riemann surface
  - No, not even at genus 0
  answer: 0
  explain: '[genus_eq_zero_iff_homeo](#/node/genus_eq_zero_iff_homeo) at Jacobian/Solution.lean lines 68–70 is the only tie to topology in the specification, and it is an iff at zero only.'
---
## Plain English

```
genus X = JacobianChallenge.Solution.genus (X := X)
```

That is the whole body (Jacobian/Solution.lean lines 59–62). This declaration is the public face of the genus: the name, namespace and argument list that Kevin Buzzard's challenge file asks for. Jacobian/Challenge.lean lines 43–45 declares exactly this signature with `sorry` as the body, and the solution has to supply a declaration that matches it so a comparator can line the two up.

The mathematics is one level down, in [Solution.genus](#/node/Solution.genus): the ℂ-dimension of the space of holomorphic 1-forms on X. Read that node for what the number means and what it does not.

## Why this one declaration matters more than it looks

`genus X` is not just a reported number; it is load-bearing in the rest of the specification. The Jacobian is defined as a quotient of `Fin (genus X) → ℂ`, that is, of ℂ^g (Jacobian/Solution.lean lines 74–77), and the charted-space, manifold and Lie-group instances on it are all stated over that model space (Jacobian/Solution.lean lines 96–101). So the genus fixes the dimension of the torus the Abel–Jacobi map lands in.

This coupling is what defeats the obvious hacks. Setting `genus X := 0` would collapse the Jacobian to a point, and then [ofCurve_inj](#/node/Jacobian.ofCurve_inj), which asserts injectivity of Abel–Jacobi whenever `0 < genus X`, would be vacuous — but [genus_eq_zero_iff_homeo](#/node/genus_eq_zero_iff_homeo) (Jacobian/Solution.lean lines 68–70) forbids it, because it forces any genus-0 surface to be homeomorphic to the 2-sphere.
