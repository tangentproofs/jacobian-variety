---
id: HolomorphicForms.pullbackFormsBundled
title: f*η as an honest holomorphic 1-form
summary: 'The file header still says this is exposed as `opaque` with a section-extraction axiom, but it is not: the definition is a plain structure literal and the smoothness field is a proved theorem.'
review: draft
authors:
- claude
caveats:
- 'The module header of `Jacobian/HolomorphicForms/PullbackBundled.lean` lines 23–29 says the bundled pullback is exposed as `opaque` with `pullbackFormsBundledLM_apply_fun` as a "section extraction axiom". That is stale. The definition is concrete, `pullbackFormsBundledLM_apply_fun` (`Jacobian/HolomorphicForms/PullbackBundled.lean` lines 174–177) is proved by `rfl`, and there is no `opaque` or `axiom` anywhere in `Jacobian/`.'
- 'The docstring on `pullbackFormsFunFiber_contMDiff_section` (`Jacobian/HolomorphicForms/PullbackBundled.lean` lines 66–96) likewise calls the smoothness of this section "the documented project gap", pending a Mathlib lemma `clm_bundle_compose`. That is stale too: the proof at `Jacobian/HolomorphicForms/PullbackBundled.lean` lines 104–126 is complete, and it calls `clm_compose_of_inCoordinates`, which the project supplies itself in `Jacobian/HolomorphicForms/CLMBundleCompose.lean`.'
- 'Both of those docstrings reason about Mathlib v4.28.0. The project is pinned to `v4.31.0-rc1` (`lean-toolchain` and `lakefile.toml`), so their claims about what Mathlib does and does not provide are not claims about the Mathlib actually being built against.'
- 'The smoothness hypothesis is `ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f`, the analytic class. The underlying function, [pullbackFormsFunFiber](#/node/HolomorphicForms.pullbackFormsFunFiber), takes no hypothesis; `hf` is used only to supply the section-smoothness field.'
- 'Holomorphicity of the result is encoded as `ContMDiff` smoothness of a section at the top smoothness exponent, which for charted ℂ-spaces modelled on ℂ is the project''s notion of holomorphic. No separate Cauchy–Riemann check appears.'
quiz:
- q: 'What are the two fields of this structure?'
  type: choice
  choices:
  - 'The underlying function and a proof that it is a smooth section'
  - 'A chart and a transition map'
  - 'A real part and an imaginary part'
  answer: 0
  explain: '`Jacobian/HolomorphicForms/PullbackBundled.lean` lines 134–139 set `toFun := pullbackFormsFunFiber f η` and `contMDiff_toFun := pullbackFormsFunFiber_contMDiff_section f hf η`.'
- q: 'Is this definition opaque, as its file header claims?'
  type: choice
  choices:
  - 'Yes, it is `opaque` with a characterising axiom'
  - 'No, it is a concrete structure literal; the header is out of date'
  - 'It is opaque only in universe 0'
  answer: 1
  explain: 'The declaration is a `noncomputable def` with explicit fields, and its own docstring says "Concrete (non-opaque)".'
- q: 'What is `hf` actually used for?'
  type: choice
  choices:
  - 'To define the pointwise values of f*η'
  - 'Only to prove that the pointwise values form a smooth section'
  - 'To prove that f is surjective'
  answer: 1
  explain: 'The pointwise values come from `pullbackFormsFunFiber`, which takes no hypothesis on f.'
- q: 'Why is proving smoothness of this section nontrivial?'
  type: choice
  choices:
  - 'Because the pullback is only defined on a dense open set'
  - 'Because it is the composition of two smooth sections of continuous-linear-map bundles, and that needs a composition lemma in bundle coordinates'
  - 'Because the chain rule fails at branch points'
  answer: 1
  explain: 'The proof decomposes via `contMDiffAt_hom_bundle` and finishes with `clm_compose_of_inCoordinates` applied to `mfderiv f` and `η ∘ f`.'
---
## Plain English

[pullbackFormsFunFiber](#/node/HolomorphicForms.pullbackFormsFunFiber) gives the pullback of a 1-form at each point separately. To call the result a holomorphic 1-form on X you also need the whole family to vary smoothly with the point. `pullbackFormsBundled f hf η` packages both (`Jacobian/HolomorphicForms/PullbackBundled.lean` lines 134–139):

```lean
toFun := pullbackFormsFunFiber f η
contMDiff_toFun := pullbackFormsFunFiber_contMDiff_section f hf η
```

The output has type `HolomorphicOneForm ℂ X`. So f\*η is a genuine object of the same kind as η, and can be integrated, added, scaled, or fed to the period lattice.

## Why the smoothness field is work

A holomorphic 1-form is a section of the cotangent bundle, which is a bundle of continuous linear maps. The pullback at x is the composition of two such sections: the derivative `mfderiv f` (a section of maps from the tangent space of X to the tangent space of Y, along f) and η read along f (a section of maps from the tangent space of Y to ℂ). Each is smooth, but "composition of two smooth bundle-of-linear-maps sections is smooth" is not free in bundle coordinates. Mathlib has the version where a linear-map section is *applied* to a vector section; the project's own notes record that it did not ship the version where two linear-map sections are *composed*.

So the project proves that lemma itself, `ContMDiffAt.clm_compose_of_inCoordinates` in `Jacobian/HolomorphicForms/CLMBundleCompose.lean`, and the proof of `pullbackFormsFunFiber_contMDiff_section` (`Jacobian/HolomorphicForms/PullbackBundled.lean` lines 97–126) decomposes the section with `contMDiffAt_hom_bundle` and applies it. The file header still describes this as an open gap. It is not; the header predates the lemma.

## How it is used

Linearity in η is proved one level up, in [pullbackFormsBundledLM](#/node/HolomorphicForms.pullbackFormsBundledLM). That linear map is what gets written in basis coordinates by [holomorphicTraceCoordU](#/node/TraceDegree.holomorphicTraceCoordU) and then transposed to give the Jacobian pushforward. It is also the form appearing in the change-of-variables statement `∫_{f∘γ} η = ∫_γ f*η` used to prove that the pushforward respects the period lattice.
