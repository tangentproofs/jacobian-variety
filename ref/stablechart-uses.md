# `StableChartAt`: complete classification of every mention

**Date:** 2026-10-27 (America/New_York) · **Branch:** `independent-repair` · **Deliverable:** first milestone, item 1 of `ref/independent-repair-brief.md` §6.

> **Status (2026-10-27, cloud session): done.** The class, its instance and all 895 mentions are
> gone from live Lean code (`f48acda`). How each real use was resolved — two reproved honestly,
> three cut to labelled gaps, the rest retired to `Attic/StableChartRetired/` — is in
> `ref/independent-repair-progress.md`. The plan in §6 below is the historical plan.

**Purpose.** Goal (a) of the brief is to delete the class `JacobianChallenge.Periods.StableChartAt`.
This file is the inventory that makes that deletion plannable: every one of the **895** mentions in
**120** `.lean` files, classified *real use* / *pass-through binder* / *comment*, with `file:line`.

**Method.** `grep -rn StableChartAt --include=*.lean .`, then a mechanical classifier
(block-comment / line-comment tracking, `omit` detection, binder-bracket detection, projection-application
detection). Because three real uses go through the *derived* lemma `achart_eq_of_mem_source` and therefore
never mention `StableChartAt` textually, the derived lemmas were grepped separately
(`achart_eq_of_mem_source`, `mfderiv_chartAt_eq_id_of_stable`, `mfderiv_chartAt_continuousOn_of_stable`,
`mfderiv_chartAt_continuousOn_of_finiteDim`) and folded in by hand. Nothing here required a build.

---

## 0. Headline counts

| class | count | what it is |
|---|---|---|
| **pass-through binder** | 809 | `[StableChartAt ℂ X]` in a `variable` line or a declaration signature, never used in the body |
| **comment / docstring** | 42 | prose only |
| **`omit` line** | 25 | `omit [… StableChartAt ℂ X] in` — a *proof that the binder is unused* by the next declaration |
| **class definition + derived lemmas** | 7 | all in `Jacobian/Periods/TrivializationContinuousLinearMapAt.lean` |
| **real use (textual)** | 7 | applications of `StableChartAt.chartAt_eq_of_mem_source` |
| **no-op instance shuffle** | 4 | `haveI _stableX : StableChartAt ℂ X := inferInstance` — re-derives the ambient binder, deletable |
| **the `sorry` instance** | 1 | `Jacobian/Solution.lean:37` |
| total | **895** | |

Adding the three derived-lemma consumers that are textually invisible, the **real
content-consumption sites number 10, in 5 files** — plus the `Solution.lean` instance that feeds them.
So `StableChartAt` is a *binder virus*: 809 of 895 mentions carry it through files whose mathematics
never touches it.

### The class is refutable, not merely unproven

Before classifying, it is worth recording *why* all of this has to go. The class is

```lean
class StableChartAt : Prop where
  chartAt_eq_of_mem_source :
    ∀ p : M, ∀ q ∈ (chartAt H p).source, chartAt H q = chartAt H p
```
(`Jacobian/Periods/TrivializationContinuousLinearMapAt.lean:52-55`)

and it is **inconsistent** with `[CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]`.
I did not take this on trust from `ref/rkirov-gap-comparison.md`; it is now a compiled,
sorry-free, axiom-clean theorem in the tree:

```lean
theorem not_chartStable_of_compactSpace
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X] :
    ¬ ChartStable ℂ X
```
(`Jacobian/Periods/ChartStabilityRefutation.lean`, built green; `#print axioms` →
`[propext, Classical.choice, Quot.sound]`)

The proof: chart stability makes chart sources pairwise equal-or-disjoint, hence clopen; connectedness
promotes one source to all of `X`; so a single chart is a homeomorphism of `X` onto an *open* subset of
`ℂ`; compactness makes that subset compact hence clopen hence `= ℂ`; but `ℂ` is not compact.

The refutation is stated about a **predicate** `ChartStable`, not about the class, precisely so that it
survives the class's deletion as the permanent record of why the class cannot come back.

Consequence, and the reason the brief ranks this first: because `Jacobian/Solution.lean:37` supplies the
instance by `sorry`, every theorem in the `Periods` / `AbelJacobi` / `HolomorphicForms` / `TraceDegree`
layers whose binders pair `[StableChartAt ℂ X]` with compactness and connectedness is **vacuously true**,
and the public theorems type-check through `sorryAx` for a *false* lemma. That is strictly worse than an
open obligation.

---

## 1. The 10 real use sites

These are the only places where the mathematics consumes the hypothesis. They fall into two kinds — the
same two kinds `ref/rkirov-gap-comparison.md:422` identifies, which I confirmed by reading each site.

### Kind (i) — "the chart at a nearby point is literally the same chart" (6 sites)

Each uses `StableChartAt.chartAt_eq_of_mem_source` to rewrite `chartAt q` into `chartAt p`.

| file:line | what it concludes |
|---|---|
| `Jacobian/HolomorphicForms/TraceSpec.lean:1091` | `chartAt ℂ x = chartAt ℂ x₀`, to get `chartLocalAt f x = chartLocalAt f x₀` |
| `Jacobian/HolomorphicForms/TraceSpec.lean:1093` | `chartAt ℂ (f x) = chartAt ℂ (f x₀)`, same goal, target side |
| `Jacobian/HolomorphicForms/TraceSpec.lean:3613` | `chartAt ℂ y = chart` in a regular-value argument |
| `Jacobian/HolomorphicForms/CompactRiemannSurface.lean:885` | `chartAt_symm_chartAt_eq_of_mem_ball`: pulling a coordinate-ball point back keeps the chart |
| `Jacobian/TraceDegree/TraceDefinition.lean:649` | `chartAt ℂ x' = chartAt ℂ x` along a local inverse branch |
| `Jacobian/TraceDegree/TraceDefinition.lean:661` | `chartAt ℂ (f x') = chartAt ℂ (f x)`, same, target side |

**Repair shape.** Each of these needs a *single instance* of the stability fact, about two specific
points already known to share a chart source. "These two points are served by the same chart" is an
honest, satisfiable hypothesis — it is simply not derivable, and must become an explicit argument,
visible in the statement. Where the surrounding theorem universally quantifies the point, the honest
hypothesis has to be hoisted into the statement, which is where the sorry count will legitimately grow.

### Kind (ii) — "therefore `coordChange` / `symmL` is the identity" (3 sites)

Each uses the derived `achart_eq_of_mem_source` to collapse a tangent-bundle coordinate change to the
identity. **This is the parallelizability error**: it asserts the tangent bundle is trivialized by the
atlas, which for a compact Riemann surface of genus `≠ 1` is false (a nowhere-zero continuous tangent
section would force `χ(X) = 2 - 2g = 0`).

| file:line | what it collapses | honest status |
|---|---|---|
| `Jacobian/HolomorphicForms/EvalAtOneHelper.lean:38` | `contMDiff_tangentSection_one` — the constant-`1` tangent section is smooth | **false for `g ≠ 1`**: it is a nowhere-zero smooth vector field |
| `Jacobian/HolomorphicForms/TraceSpec.lean:4073` | `tT.symmL ℂ y = 1` | false in the same way |
| `Jacobian/HolomorphicForms/CompactRiemannSurface.lean:736` | `symmL … = id` inside an `inCoordinates` computation | false in the same way |

**Repair shape.** These cannot become hypotheses, because the hypothesis would be a parallelization and
the downstream statements are meant to hold for all genera. They have to be rebuilt the `inCoordinates`
way: never read a bundle element through a *global* frame, only through the trivialization at the point
being examined, and carry a transformation law instead of an agreement assumption. This is the one part
of goal (a) that is genuinely new mathematics rather than re-plumbing.

A note on scope, which matters for sequencing. `EvalAtOneHelper.lean`'s own binders are
`[TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold … X] [StableChartAt ℂ X]` — **no** compactness,
**no** connectedness. So its two theorems are *not* vacuous in their own file (`ℂ` itself satisfies the
class, via the `StableChartAt H H` instance) and they are honestly proved there. They become false only
on instantiation at a compact connected `X`, which is what `Solution.lean:37` does. The defect is
therefore not "a wrong proof in `EvalAtOneHelper`" but "a class whose only inhabitants are the spaces the
project is not about", and the fix is to restate the theorems so they say something about the spaces the
project *is* about.

### And the instance that makes it all vacuous

| file:line | |
|---|---|
| `Jacobian/Solution.lean:37` | `instance … : JacobianChallenge.Periods.StableChartAt ℂ X := sorry`, under `[T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]` — refuted by `not_chartStable_of_compactSpace` |

---

## 2. The definition site

All of `Jacobian/Periods/TrivializationContinuousLinearMapAt.lean` (176 lines) exists to serve the class.

| line | declaration | disposition |
|---|---|---|
| 52-55 | `class StableChartAt` | **delete** |
| 58-61 | `instance : StableChartAt H H` | **delete** (true, but only about the model space) |
| 66-70 | `theorem achart_eq_of_mem_source` | **delete**; its 3 consumers are the kind-(ii) sites |
| 92-106 | `theorem mfderiv_chartAt_eq_id_of_stable` | **delete** — zero consumers outside this file |
| 112-121 | `theorem mfderiv_chartAt_continuousOn_of_stable` | **delete** — zero consumers outside this file |
| 137-150 | `theorem mfderiv_chartAt_continuousOn_of_finiteDim` | **delete** — zero consumers anywhere |
| 152-173 | the Mathlib-upstreaming plan comment | **delete**; it is unachievable (see below) |

The upstreaming plan at `:152-173` proposes instances for "`Sphere`, `Icc`". That is not merely
optimistic, it is impossible: Mathlib's `Mathlib/Geometry/Manifold/Instances/Sphere.lean` sets
`chartAt v := stereographic' n (-v)` with source `{v}ᶜ`, so any `w ∉ {v, -v}` sits in `(chartAt v).source`
with `chartAt w ≠ chartAt v`. **The sphere violates the class** — and the sphere is the space named in
the challenge's own `genus_eq_zero_iff_homeo`. Three of the four lemmas in this file have no consumer
outside it at all, so the file deletes almost cleanly.

---

## 3. The 25 `omit` lines — free evidence

`omit [… StableChartAt ℂ X] in` tells Lean the binder is unused by the following declaration, and Lean
*checks* it. So these 25 lines are machine-verified proof that the surrounding mathematics is independent
of chart stability, and they delete along with the binder at zero risk.

| file | `omit` lines |
|---|---|
| `Jacobian/HolomorphicForms/TraceSpec.lean` | 11 |
| `Jacobian/TraceDegree/AnalyticPushforwardFunctorialU.lean` | 4 (`49,60,75,83`) |
| `Jacobian/HolomorphicForms/MeromorphicFunctionVector.lean` | 1 (`238`) |
| remaining `HolomorphicForms` / `TraceDegree` files | 9 |

---

## 4. Per-file table — all 120 files

`binder` = count of pass-through binder mentions · `omit` = `omit`-line numbers · `real use` = content
consumption · `other` = no-op `haveI` shuffles and the `sorry` instance · `comment` = prose mentions.

| file | binder | omit | real use | other | comment |
|---|---|---|---|---|---|
| `Jacobian/HolomorphicForms/DeRhamComparisonMap.lean` | 180 | — | — | — | — |
| `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` | 102 | — | 885 | — | — |
| `Jacobian/HolomorphicForms/TraceSpec.lean` | 61 | 11 lines | 1091,1093,3613 | — | 8 |
| `Jacobian/HolomorphicForms/GenusZeroClassification.lean` | 81 | — | — | — | — |
| `Jacobian/HolomorphicForms/MeromorphicToBranchedCover.lean` | 46 | — | — | — | — |
| `Jacobian/Periods/PeriodFunctional.lean` | 32 | — | — | — | — |
| `Jacobian/Periods/TrivializationContinuousLinearMapAt.lean` | — | — | 70 (defn) | — | 17 |
| `Jacobian/HolomorphicForms/MeromorphicFunctionVector.lean` | 19 | 238 | — | — | — |
| `Jacobian/HolomorphicForms/MeromorphicDegree.lean` | 16 | — | — | — | — |
| `Jacobian/Blueprint/Sec03/PeriodHomologyInvariance.lean` | 15 | — | — | — | — |
| `Jacobian/HolomorphicForms/HodgeProjection.lean` | 15 | — | — | — | — |
| `Jacobian/HolomorphicForms/RiemannRoch.lean` | 15 | — | — | — | — |
| `Jacobian/HolomorphicForms/MeromorphicToCp1.lean` | 12 | — | — | — | — |
| `Jacobian/TraceDegree/AnalyticPushforwardFunctorialU.lean` | 7 | 49,60,75,83 | — | — | — |
| `Jacobian/HolomorphicForms/HodgeLaplacian.lean` | 10 | — | — | — | — |
| `Jacobian/HolomorphicForms/SmoothDifferentialForm.lean` | 9 | — | — | — | — |
| `Jacobian/Periods/CellularHomologyRS.lean` | 8 | — | — | — | — |
| `Jacobian/TraceDegree/TraceDefinition.lean` | 5 | — | 649,661 | — | 1 |
| `Jacobian/HolomorphicForms/DeRhamCohomology.lean` | 7 | — | — | — | — |
| `Jacobian/Periods/ChartedFormPullbackContinuous.lean` | — | — | — | — | 7 |
| `Jacobian/Periods/PullbackNaturality.lean` | 7 | — | — | — | — |
| `Jacobian/TraceDegree/PullbackBasis.lean` | 7 | — | — | — | — |
| `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` | 5 | — | — | — | 1 |
| `Jacobian/Periods/ChartedFormPullbackChainRule.lean` | 2 | — | — | 65,66,148,149— | — |
| `Jacobian/TraceDegree/TraceFormsIdU.lean` | 1 | 40,78,147,153,161 | — | — | — |
| `Jacobian/Periods/ChartOverlapDerivContinuous.lean` | — | — | — | — | 5 |
| `Jacobian/TraceDegree/AnalyticDegreeU.lean` | 4 | — | — | — | 1 |
| `Jacobian/Blueprint/Sec03/HolomorphicFormIsClosed.lean` | 4 | — | — | — | — |
| `Jacobian/HolomorphicForms/HodgeDecomposition.lean` | 4 | — | — | — | — |
| `Jacobian/HolomorphicForms/HodgeStarRS.lean` | 4 | — | — | — | — |
| `Jacobian/HolomorphicForms/Meromorphic.lean` | 3 | 223 | — | — | — |
| `Jacobian/TraceDegree/AnalyticDegree.lean` | 4 | — | — | — | — |
| `Jacobian/AnalyticJacobian/EvalJacobianClassOps.lean` | 3 | — | — | — | — |
| `Jacobian/AnalyticJacobian/EvalJacobianClassSmul.lean` | 3 | — | — | — | — |
| `Jacobian/HolomorphicForms/AntiHolomorphicOneForm.lean` | 3 | — | — | — | — |
| `Jacobian/HolomorphicForms/DeRhamSingular.lean` | 3 | — | — | — | — |
| `Jacobian/HolomorphicForms/SinglePoleLift.lean` | 1 | 157,171 | — | — | — |
| `Jacobian/Periods/H1BasisU.lean` | 3 | — | — | — | — |
| `Jacobian/Periods/PathIntegralViaCoverWithRefinementInvariant.lean` | 2 | — | — | — | 1 |
| `Jacobian/Periods/PeriodFunctionalU.lean` | 3 | — | — | — | — |
| `Jacobian/TraceDegree/AnalyticPullbackFunctorialU.lean` | 3 | — | — | — | — |
| `Jacobian/TraceDegree/PushforwardBasis.lean` | 3 | — | — | — | — |
| `Jacobian/TraceDegree/RegularValueCompU.lean` | 3 | — | — | — | — |
| `Jacobian/TraceDegree/TraceFormsBundledCompU.lean` | 3 | — | — | — | — |
| `Jacobian/TraceDegree/TracePullbackProviderU.lean` | 2 | 66 | — | — | — |
| `Jacobian/AbelJacobi/PathIntegralFunctionalU.lean` | 2 | — | — | — | — |
| `Jacobian/AnalyticJacobian/Defs.lean` | 2 | — | — | — | — |
| `Jacobian/AnalyticJacobian/Mk.lean` | 2 | — | — | — | — |
| `Jacobian/HolomorphicForms/DeRhamComplex.lean` | 2 | — | — | — | — |
| `Jacobian/HolomorphicForms/EvalAtOneHelper.lean` | 1 | — | — | — | 1 |
| `Jacobian/HolomorphicForms/HolomorphicCompactConstant.lean` | 2 | — | — | — | — |
| `Jacobian/HolomorphicForms/RealComplexDeRham.lean` | 2 | — | — | — | — |
| `Jacobian/Periods/IntegralOneCycleRank.lean` | 2 | — | — | — | — |
| `Jacobian/Periods/PathIntegralViaChartCorrectPullback.lean` | 2 | — | — | — | — |
| `Jacobian/Periods/RealHomologyTensor.lean` | 2 | — | — | — | — |
| `Jacobian/TraceDegree/AnalyticPullbackContMDiffU.lean` | 2 | — | — | — | — |
| `Jacobian/TraceDegree/AnalyticPullbackU.lean` | 2 | — | — | — | — |
| `Jacobian/TraceDegree/AnalyticPushPullU.lean` | 2 | — | — | — | — |
| `Jacobian/TraceDegree/AnalyticPushforwardContMDiffU.lean` | 2 | — | — | — | — |
| `Jacobian/TraceDegree/AnalyticPushforwardU.lean` | 2 | — | — | — | — |
| `Jacobian/TraceDegree/PullbackTraceLiftU.lean` | 2 | — | — | — | — |
| `Jacobian/AbelJacobi/AnalyticOfCurveInjectiveU.lean` | 1 | — | — | — | — |
| `Jacobian/AbelJacobi/AnalyticOfCurveU.lean` | 1 | — | — | — | — |
| `Jacobian/AbelJacobi/BaseChange.lean` | 1 | — | — | — | — |
| `Jacobian/AbelJacobi/Composition.lean` | 1 | — | — | — | — |
| `Jacobian/AbelJacobi/Coset.lean` | 1 | — | — | — | — |
| `Jacobian/AbelJacobi/Defs.lean` | 1 | — | — | — | — |
| `Jacobian/AbelJacobi/GenusWitness.lean` | 1 | — | — | — | — |
| `Jacobian/AbelJacobi/Identities.lean` | 1 | — | — | — | — |
| `Jacobian/AbelJacobi/Nontrivial.lean` | 1 | — | — | — | — |
| `Jacobian/AbelJacobi/Smul.lean` | 1 | — | — | — | — |
| `Jacobian/AbelJacobi/Specialize.lean` | 1 | — | — | — | — |
| `Jacobian/AbelJacobi/Sum.lean` | 1 | — | — | — | — |
| `Jacobian/AbelJacobi/Symmetry.lean` | 1 | — | — | — | — |
| `Jacobian/AbelJacobi/Telescoping.lean` | 1 | — | — | — | — |
| `Jacobian/AbelJacobi/WitnessEqIff.lean` | 1 | — | — | — | — |
| `Jacobian/AbelJacobi/WitnessMk.lean` | 1 | — | — | — | — |
| `Jacobian/AbelJacobi/WitnessMkPeriodPairing.lean` | 1 | — | — | — | — |
| `Jacobian/AbelJacobi/WitnessSubArith.lean` | 1 | — | — | — | — |
| `Jacobian/AbelJacobi/WitnessZeroIff.lean` | 1 | — | — | — | — |
| `Jacobian/AbelJacobi/WitnessZeroSmul.lean` | 1 | — | — | — | — |
| `Jacobian/AnalyticJacobian/EvalJacobianClass.lean` | 1 | — | — | — | — |
| `Jacobian/AnalyticJacobian/EvalJacobianClassEq.lean` | 1 | — | — | — | — |
| `Jacobian/AnalyticJacobian/EvalJacobianClassEqSubMem.lean` | 1 | — | — | — | — |
| `Jacobian/AnalyticJacobian/EvalJacobianClassMember.lean` | 1 | — | — | — | — |
| `Jacobian/AnalyticJacobian/EvalJacobianClassMkBridge.lean` | 1 | — | — | — | — |
| `Jacobian/AnalyticJacobian/EvalJacobianClassPeriodPairing.lean` | 1 | — | — | — | — |
| `Jacobian/AnalyticJacobian/EvalJacobianClassZero.lean` | 1 | — | — | — | — |
| `Jacobian/AnalyticJacobian/MkArith.lean` | 1 | — | — | — | — |
| `Jacobian/AnalyticJacobian/MkExt.lean` | 1 | — | — | — | — |
| `Jacobian/AnalyticJacobian/MkMembership.lean` | 1 | — | — | — | — |
| `Jacobian/AnalyticJacobian/MkOps.lean` | 1 | — | — | — | — |
| `Jacobian/AnalyticJacobian/MkPeriodPairing.lean` | 1 | — | — | — | — |
| `Jacobian/AnalyticJacobian/MkPeriodPairingCycle.lean` | 1 | — | — | — | — |
| `Jacobian/AnalyticJacobian/MkPeriodPairingCycleSmul.lean` | 1 | — | — | — | — |
| `Jacobian/AnalyticJacobian/MkPeriodPairingSmul.lean` | 1 | — | — | — | — |
| `Jacobian/AnalyticJacobian/MkSubArith.lean` | 1 | — | — | — | — |
| `Jacobian/AnalyticJacobian/NontrivialWitness.lean` | 1 | — | — | — | — |
| `Jacobian/HolomorphicForms/HodgeDeRhamRank.lean` | 1 | — | — | — | — |
| `Jacobian/HolomorphicForms/MeromorphicDegreeRefinement.lean` | 1 | — | — | — | — |
| `Jacobian/HolomorphicForms/MeromorphicFunction.lean` | 1 | — | — | — | — |
| `Jacobian/HolomorphicForms/SheafCohomologyRS.lean` | 1 | — | — | — | — |
| `Jacobian/Periods/BasisAlignedAnalyticJacobianEquiv.lean` | 1 | — | — | — | — |
| `Jacobian/Periods/BasisAlignedPeriodPairing.lean` | 1 | — | — | — | — |
| `Jacobian/Periods/BasisAlignedPeriodSubgroup.lean` | 1 | — | — | — | — |
| `Jacobian/Periods/BasisAlignedPeriodSubgroupU.lean` | 1 | — | — | — | — |
| `Jacobian/Periods/ComplexManifoldOrientable.lean` | 1 | — | — | — | — |
| `Jacobian/Periods/PeriodFullComplexLatticeU.lean` | 1 | — | — | — | — |
| `Jacobian/Periods/PeriodFunctionalApi.lean` | 1 | — | — | — | — |
| `Jacobian/Periods/PeriodFunctionalIntSmul.lean` | 1 | — | — | — | — |
| `Jacobian/Periods/PeriodFundamentalDomainU.lean` | 1 | — | — | — | — |
| `Jacobian/Periods/PeriodLattice.lean` | 1 | — | — | — | — |
| `Jacobian/Periods/PeriodSubgroupApi.lean` | 1 | — | — | — | — |
| `Jacobian/Periods/PeriodSubgroupClosure.lean` | 1 | — | — | — | — |
| `Jacobian/Periods/PeriodSubgroupExt.lean` | 1 | — | — | — | — |
| `Jacobian/Periods/PeriodSubgroupNeg.lean` | 1 | — | — | — | — |
| `Jacobian/Periods/PeriodSubgroupRange.lean` | 1 | — | — | — | — |
| `Jacobian/Periods/PeriodSubgroupZLatticeU.lean` | 1 | — | — | — | — |
| `Jacobian/Periods/PeriodVectorsLIU.lean` | 1 | — | — | — | — |
| `Jacobian/Solution.lean` | — | — | — | —37 | — |

**Layer roll-up.**

| layer | files | binder | omit | real use | comment |
|---|---|---|---|---|---|
| `HolomorphicForms` | 27 | 602 | 15 | 4 (+3 derived) | 9 |
| `Periods` | 30 | 80 | 0 | 1 (+6 defn) | 30 |
| `TraceDegree` | 17 | 54 | 10 | 2 | 2 |
| `AbelJacobi` | 22 | 27 | 0 | 0 | 1 |
| `AnalyticJacobian` | 21 | 27 | 0 | 0 | 0 |
| `Blueprint` | 2 | 19 | 0 | 0 | 0 |
| `Solution.lean` | 1 | 0 | 0 | 1 (the `sorry` instance) | 0 |
| **total** | **120** | **809** | **25** | **10** | **42** |

`Jacobian/HolomorphicForms/DeRhamComparisonMap.lean` alone carries **180** pass-through binders and
**zero** real uses — the single clearest illustration of the virus.

---

## 5. Mentions outside `.lean` files

These are not blockers but must be updated so the record stops asserting the class is merely open.

| file:line | mention | disposition |
|---|---|---|
| `tex/statements/challenge-statement.tex:103-111` | `lem:stable-chart-at-instance`, "currently stands as an open obligation (`sorry`)" | **rewrite**: the class is *refutable*, not open. Minimal edit, logged in `ref/plain-english-changelog.md` |
| `tex/statements/challenge-statement.tex:110` | `\lean{…instStableChartAt…}` pointer | **delete** with the instance |
| `sorries.jsonl:262` | blueprint sorry record for that instance | regenerated artifact; refreshes itself |
| `scripts/audit-leanok-axioms.py:8` | docstring example naming "the open `StableChartAt`" | **reword** |
| `Jacobian/Blueprint/Sec03/PeriodHomologyInvariance.lean.bak:×15` | stale backup, not a build target | **delete the `.bak`** |
| `ref/rkirov-gap-comparison.md`, `ref/axiom-audit.md`, `ref/independent-repair-brief.md` | analysis prose | leave; they are the historical record |

---

## 6. Resulting plan for goal (a)

Ordered so that each step is independently buildable, cheapest and safest first.

1. ✅ **Land the refutation** (`Jacobian/Periods/ChartStabilityRefutation.lean`) so the justification is
   in-tree and compiled, before anything is deleted. *Done, green.*
2. **Rebuild the 3 kind-(ii) sites** the `inCoordinates` way, starting with `EvalAtOneHelper.lean`
   (66 lines, 2 importers, shallow imports — the smallest real-use cluster in the tree). This is the
   only step with real mathematical content, so it goes early while attention is cheap.
3. **Convert the 6 kind-(i) sites** to explicit shared-chart hypotheses, visible in each statement.
4. **Delete the class, its instance and its 4 derived lemmas**, i.e. retire
   `TrivializationContinuousLinearMapAt.lean`.
5. **Strip the 809 pass-through binders and 25 `omit` lines** — mechanical, one layer per commit,
   `HolomorphicForms` (602) last because it is largest.
6. **Delete `Jacobian/Solution.lean:37`.** Note this is the one edit that cannot be verified here:
   `lake build Jacobian.Solution` is forbidden by the brief §4, so it lands as "pending build machine".
7. **Update the prose** (`tex`, `scripts/audit-leanok-axioms.py`) and log it in
   `ref/plain-english-changelog.md`.

Steps 2 and 3 will raise the sorry count. Per brief §2 that is the correct outcome: the statements that
lose their proofs were vacuous, and an honest `sorry` with a `-- GAP:` comment beats a proof that routes
through a refuted lemma.

**Build-coverage caveat.** Everything above is reachable by narrow module builds except step 6 and the
`HolomorphicForms` bulk of step 5, whose natural check is a whole-tree build. Those are recorded as
"pending build machine" in `ref/independent-repair-progress.md` rather than claimed as verified.
