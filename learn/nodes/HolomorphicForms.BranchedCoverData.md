---
id: HolomorphicForms.BranchedCoverData
title: Branched cover data, bundled as hypotheses
summary: 'Everything hard about a branched cover — finite fibres, a constant weighted fibre count — is a field you hand over, not something this structure proves.'
review: draft
authors:
- claude
caveats:
- 'Not a theorem and not a definition of "branched cover": it is a record of data plus assumptions. Anyone can write one down for a silly `f` if they can prove the fields; the honesty of the degree rests entirely on the analytic constructor that builds one from a real holomorphic map.'
- 'No holomorphy anywhere in the signature. `X` and `Y` are bare topological spaces and `f` is any function, so `ramificationIndex` is an arbitrary positive-integer-valued function until a separate predicate (`BranchedCoverData.RamificationIndexCompatible`) ties it to the analytic order of vanishing.'
- '`local_bijective_unramified` asks only for `Set.BijOn f U V` on some open `U`, `V`. It does not say the set-theoretic inverse is continuous, let alone holomorphic; that is proved separately where it is needed.'
- '`fiberSum_const` is stated for every pair `y₁ y₂`, and every index is positive, so the fields are jointly quite strong: if one fibre is empty its sum is 0, forcing every fibre sum to 0, hence every fibre to be empty. With `X` nonempty that is impossible, so a non-surjective `f` carries no `BranchedCoverData` at all.'
- 'A stale docstring later in the file (Jacobian/HolomorphicForms/BranchedCover.lean lines 299–305) still calls the analytic constructor `branchedCoverData_of_nonconstant_holomorphic` "still-open". It is not: it is proved.'
quiz:
- q: 'Which of these does `BranchedCoverData` *prove*?'
  type: choice
  choices:
  - That every fibre of `f` is finite
  - That the weighted fibre count is the same over every point of `Y`
  - None of them; both are fields the user of the structure must supply
  answer: 2
  explain: '`finite_fiber` and `fiberSum_const` are structure fields (Jacobian/HolomorphicForms/BranchedCover.lean lines 56–83). The docstring calls bundling the constancy field "the load-bearing trick".'
- q: What does the structure assume about `f`, `X` and `Y`?
  type: choice
  choices:
  - 'Only that `X` and `Y` are topological spaces and `f : X → Y` is a function'
  - That `f` is holomorphic between compact Riemann surfaces
  - That `f` is continuous and surjective
  answer: 0
  explain: 'The binders are `(X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)` (Jacobian/HolomorphicForms/BranchedCover.lean lines 56–58). No continuity, no charts, no holomorphy.'
- q: 'Why is `weightedFiberCard` a separate definition rather than a sixth field?'
  type: choice
  choices:
  - So consumers can always unfold it to the fibre sum, with no risk of a user-supplied override
  - Because it is not computable
  - Because it needs `Y` to be nonempty
  answer: 0
  explain: 'The docstring at Jacobian/HolomorphicForms/BranchedCover.lean lines 50–54 says exactly this, and `fiberSum_const` is stated in terms of the same fibre sum so the rewrite lemma is unconditional.'
- q: 'If `f` misses some point of `Y` and `X` is nonempty, what do the fields force?'
  type: choice
  choices:
  - Nothing; empty fibres are exempt
  - 'That the weighted count is 0 everywhere, but the data still exists'
  - 'A contradiction: no `BranchedCoverData` for such an `f` can exist'
  answer: 2
  explain: '`fiberSum_const` equates the fibre sums over *any* two points (Jacobian/HolomorphicForms/BranchedCover.lean lines 73–76), so the missed point forces every sum to 0; but `ramificationIndex_pos` (Jacobian/HolomorphicForms/BranchedCover.lean line 62) makes the sum over a nonempty fibre at least 1.'
---
## Plain English

A holomorphic map `f : X → Y` between compact Riemann surfaces is a *branched cover*: away from finitely many points it looks like `d` disjoint copies of a small disc mapping down, and at the exceptional points several sheets collide. The number `d` is the degree.

`BranchedCoverData X Y f` is a filing cabinet for the facts that make that picture work. Its fields are:

- `ramificationIndex : X → ℕ` — how many sheets come together at each point of `X`, with `ramificationIndex_pos` saying it is at least 1;
- `finite_fiber` — every fibre `f⁻¹{y}` is a finite set;
- `fiberSum_const` — the weighted count `∑ x ∈ f⁻¹{y}, ramificationIndex x` is the same for every `y : Y`;
- `ramified_finite` — only finitely many points of `X` have index ≠ 1;
- `local_bijective_unramified` — near a point of index 1, `f` is a bijection from some open set onto some open set.

The honest thing to say is that this structure *assumes* the hard theorems rather than proving them. `X` and `Y` are bare topological spaces here and `f` is any function at all. The docstring is upfront about it: bundling the constancy of the weighted count as a field "is the load-bearing trick that lets [branchedDegree](#/node/HolomorphicForms.branchedDegree) exist before the analytic open-mapping theorem is in place" (Jacobian/HolomorphicForms/BranchedCover.lean lines 42–48).

## Why that is not cheating

Assuming the hard facts in a structure would be cheating if nothing ever built one. Two declarations close the loop. [branchedCoverData_of_nonconstant_holomorphic](#/node/Blueprint.branchedCoverData_of_nonconstant_holomorphic) constructs the data for a genuine nonconstant holomorphic map, taking `ramificationIndex` to be the local order of vanishing [mapAnalyticOrderAt](#/node/HolomorphicForms.mapAnalyticOrderAt) and proving each remaining field. And `ContMDiff.exists_branchedCoverData` (Jacobian/Solution.lean lines 252–261) shows that for every nonconstant complex-smooth map of compact Riemann surfaces such data exists, so the public [ContMDiff.degree](#/node/ContMDiff.degree) never has to fall back on a default value.

## How it is used

Downstream code is told to go through `branchedDegree_eq_weightedFiberCard` (Jacobian/HolomorphicForms/BranchedCover.lean lines 173–178) rather than unfold the definition. The structure also supports the combinatorial end of the theory: `degree_one_bijective` (Jacobian/HolomorphicForms/BranchedCover.lean lines 316–340) shows degree one forces `f` to be a bijection, and [isRegularValue](#/node/HolomorphicForms.isRegularValue) reads off which points of `Y` have no ramified preimage.
