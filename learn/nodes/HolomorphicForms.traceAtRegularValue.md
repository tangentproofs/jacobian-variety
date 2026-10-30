---
id: HolomorphicForms.traceAtRegularValue
title: The trace of a 1-form at a regular value
summary: The regularity hypothesis is never used in the body; the definition is simply the sum of pushed-forward covectors over the finite fiber.
review: draft
authors:
- claude
caveats:
- 'The hypothesis `_hy : isRegularValue h y` is marked unused. The body is the fiber sum for whatever `y` is given; regularity only records when that sum deserves the name "trace".'
- Finiteness of the fiber is a *field* of the supplied `BranchedCoverData`, not something proved at this point. A caller who hands over a bad datum gets a bad sum.
- At a ramified preimage the summand would be 0, through the fallback branch of `cotangentPushforward`. That is another reason the regularity hypothesis matters to callers.
quiz:
- q: What does the definition sum?
  type: choice
  choices:
  - The pushed-forward covectors of ω over the preimages of y
  - The values of ω along a path ending at y
  - The residues of ω at the branch points
  answer: 0
  explain: 'The body is `Finset.sum s.attach (fun x => cotangentPushforward f x.1 (ω x.1))` where `s` is the fiber over y (Jacobian/TraceDegree/TraceDefinition.lean lines 94–95).'
- q: What role does the regularity hypothesis play in the body?
  type: choice
  choices:
  - None; it is unused and only constrains who may call the definition
  - It restricts the sum to the unramified preimages
  - It is what proves the fiber finite
  answer: 0
  explain: 'The binder is written `_hy` (Jacobian/TraceDegree/TraceDefinition.lean line 93) and does not appear in the two body lines.'
- q: Where does the finiteness of the fiber come from?
  type: choice
  choices:
  - The `finite_fiber` field of the BranchedCoverData argument
  - It is proved here from compactness of X
  - It follows from Riemann's removable singularity theorem
  answer: 0
  explain: '`(h.finite_fiber y).toFinset` reads off a field of the structure in Jacobian/HolomorphicForms/BranchedCover.lean lines 56–83.'
- q: Are the summands weighted by ramification index?
  type: choice
  choices:
  - No, and at a regular value every index is 1 anyway
  - Yes, each summand is multiplied by its index
  - Yes, each summand is divided by its index
  answer: 0
  explain: 'The sum in Jacobian/TraceDegree/TraceDefinition.lean lines 94–95 mentions `ramificationIndex` nowhere; regularity means every index in the fiber is 1.'
---
## Plain English

The classical trace of a 1-form ω along a branched cover f : X → Y assigns to a point y of Y the sum, over the preimages of y, of ω pushed forward:

(Tr ω)_y = Σ over x with f x = y of ω_x ∘ (df_x)⁻¹.

This definition is that sum, taken literally, with three ingredients.

The fiber. The sum ranges over `(h.finite_fiber y).toFinset`: the set of preimages of y, turned into a finite set. That the fiber is finite is an assumption carried by the branched-cover datum h ([BranchedCoverData](#/node/HolomorphicForms.BranchedCoverData), `Jacobian/HolomorphicForms/BranchedCover.lean` lines 56–83), not a fact proved here. `.attach` is a Lean device for summing over the elements of a finite set together with their membership proofs; the body only uses the element itself.

The summand. Each preimage contributes [cotangentPushforward](#/node/HolomorphicForms.cotangentPushforward) of ω at that point.

The hypothesis. `isRegularValue h y` says every preimage of y has ramification index 1 ([isRegularValue](#/node/HolomorphicForms.isRegularValue), `Jacobian/TraceDegree/TraceDefinition.lean` lines 62–63). In the Lean it is written `_hy` and is never used. It is a gate on callers rather than part of the computation, and it is the gate that makes the sum honest: at a regular value every preimage is unramified, so every derivative is invertible and every summand is a genuine pushforward. At a branch value, ramified preimages would silently contribute 0.

There is no weighting by ramification index, and none is wanted: at a regular value every index is 1, so the unweighted fiber has exactly deg f points (`branchedDegree_eq_card_toFinset_of_unramified_fiber`, `Jacobian/HolomorphicForms/BranchedCover.lean` lines 216–230) and the plain sum is the classical trace.

## What is proved about it

The sum is additive and ℂ-homogeneous in ω ([traceAtRegularValue_add](#/node/HolomorphicForms.traceAtRegularValue_add) and [traceAtRegularValue_smul](#/node/HolomorphicForms.traceAtRegularValue_smul), `Jacobian/TraceDegree/TraceDefinition.lean` lines 504–539), it sends the zero form to 0 ([traceAtRegularValue_zero](#/node/HolomorphicForms.traceAtRegularValue_zero), `Jacobian/HolomorphicForms/TraceSpec.lean` lines 102–110), and it gives the same answer for *any* two branched-cover data on the same f, with no compatibility hypothesis needed ([traceAtRegularValue_BCD_invariance](#/node/HolomorphicForms.traceAtRegularValue_BCD_invariance), `Jacobian/HolomorphicForms/TraceSpec.lean` lines 2576–2588). That last one matters: the datum h is a choice, and the trace must not depend on it. The proof is cheap — the two `finite_fiber` fields are proofs of the same proposition, so the `Finset` summed over is literally the same, and the summands never mention h.

Extending this local formula across the finitely many branch values is the job of [TraceFormsConstructionData](#/node/HolomorphicForms.TraceFormsConstructionData).
