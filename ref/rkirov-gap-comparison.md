# Per-gap comparison: this project's plan vs. rkirov/jacobian-claude

**Date:** 2026-10-27 · **Branch:** `rkirov-comparison` · **Status:** plan/research only — no Lean was compiled, no file outside this one was changed.

**Repos compared**

| | this project | reference |
|---|---|---|
| repo | `tangentproofs/jacobian-variety` (clone dir still `JacobianChallenge`; the GitHub URLs in `README.md:9-11` and `tex/macros.tex:109-110` still say `tangentstorm/JacobianChallenge` and need updating) | [`rkirov/jacobian-claude`](https://github.com/rkirov/jacobian-claude) |
| spec | Buzzard v0.3 (`Jacobian/Challenge.lean:7`) | Buzzard v0.4 (`Jacobian_challenge.lean`); v0.4 is syntactically identical to v0.3 apart from `𝓘(ℂ, E)` notation (`Jacobians.lean:69-70`) |
| toolchain | `leanprover/lean4:v4.31.0-rc1`; Mathlib `rev = "v4.31.0-rc1"` (`lakefile.toml`) | `leanprover/lean4:v4.30.0`; Mathlib commit `c5ea003` (`lakefile.lean:15-17`) |
| licence | MIT (`LICENSE:1-3`, © Michal J Wallace) | Apache-2.0 (`LICENSE:1-3`); no `NOTICE` file |
| size | **81,459** lines / **513** files under `Jacobian/` | **72,403** lines / **251** files under `Jacobians/` |
| sorries | 20 engine sorries + 1 instance sorry (+ 24 in the frozen spec file) | **0** — the only `sorry` string in his `Jacobians/` tree is the word inside an attribution comment (`Jacobians/PlanarStokes/PlanarCompactSupportStokes.lean:13`) |
| custom axioms | 1 — `HolomorphicForms.localPullbackAt_holomorphic` (`Jacobian/TraceDegree/TraceDefinition.lean:220`, per `ref/axiom-audit.md:47-74`) | 0 — `grep -rn "^axiom " Jacobians/` returns nothing |

Every code claim below cites a `file:line` that was actually opened. Line numbers are at current `HEAD` (`c353873`).

**Method note.** An independent repo-wide sweep for `sorry` in term position (excluding `Jacobian/Challenge.lean`'s 24 frozen spec sorries) returns exactly the 21 sites the task list names — **no missed sorry**. But the sorry count is the wrong single metric for this project: §6 lists four classes of unsoundness that the ledger does not count, including placeholder *definitions* (`:= 0`, `:= True`, `opaque`) under which several of the sorries are unprovable or false. Nothing in this report was verified by compiling Lean; where a claim depends on term-level reachability or on a statement being false, the report says so and names the check to run.

---

## 0. Executive summary

Five findings, in descending order of how much they should change the plan.

**(1) The two repos converged on the *same* architecture.** This is the headline good news. rkirov's final `Jacobian` is

```
JacobianTorus X := (Fin (genus X) → ℂ) ⧸ (periodLattice X).toAddSubgroup   -- Jacobians.lean:127-129
Jacobian X      := ULift.{u} (JacobianTorus X)                             -- Jacobians.lean:651-653
genus X         := Module.finrank ℂ (HolomorphicOneForms X)                 -- Jacobians/Forms/Genus.lean:62-64
```

and this project's is

```
Jacobian X := ULift.{u} (ComplexTorus.quotient (Fin (genus X) → ℂ) (periodFullComplexLatticeU X))  -- Solution.lean:89-92
genus X    := HolomorphicForms.analyticGenus ℂ X = Module.finrank ℂ (HolomorphicOneForm ℂ X)       -- Solution.lean:45-47
```

Same analytic period-lattice route, same basis-aligned `Fin g → ℂ` carrier (not the abstract dual), same `ULift` universe bridge, same analytic genus, even the same auxiliary lemma names (`contMDiff_uliftUp` vs `contMDiff_uLift_up`). `ref/plan.md:28-44` ("Use the analytic period-lattice construction") was the right call, and an independent complete solution confirms it. The blueprint's architectural prose — `tex/sections/07-complex-tori-and-jacobians.tex`, `tex/sections/10-main-theorem-assembly.tex`, `tex/statements/challenge-statement.tex` — describes rkirov's object as accurately as it describes ours.

**(2) The divergence is not in the architecture, it is in which layer got built.** The allocation of effort is almost disjoint:

| layer | this project | rkirov |
|---|---|---|
| polygon model / Hurewicz / Tietze / surface classification | ~8.5k lines in the four gap-bearing files, plus `EdgeWord`/`SurfaceClassification*`/`Polygon4g*`/`RadoTriangulation`/`Cellular*` (inside `Jacobian/Periods/`, 29,695 total) | **0** — explicitly retired after being costed at "≥10k LoC … **Rejected**" (`docs/walls_bc_plan_2026-06-10.md:254-258`; see also `README.md:52`, `formalization.yaml:204-208`, `docs/RETRO.md:25-27`) |
| de Rham / Hodge | `DeRhamComparisonMap.lean` 3,358 + `HodgeProjection.lean` 315 + `HodgeStarRS.lean` 122 | **0** — named as "the de Rham / Hodge wall" and routed around (`Jacobians/SphereTopology/GenusSphereBackward.lean:45-49`) |
| Čech / Dolbeault / finiteness | **0** | ~15.5k lines (`Cech/` 1,742 + `Dbar/` 2,127 + `DolbeaultComparison/` 3,977 + `Finiteness/` 9,752) |
| Riemann–Roch / Serre duality | deprioritized `wontdo` (`ref/plan.md:265-271`) | 4,300 lines (`LaurentTail/` 1,164 + `TailDuality/` 3,136), proven **unconditionally in every genus** (`TailDuality/RiemannRochUnconditional.lean:63-70`) |
| residue theorem / planar Stokes | vacuous (see §Honesty) | 3,482 lines (`ResidueTheorem/` 2,293 + `PlanarStokes/` 1,189) |
| mapping degree / fibre counting | `BranchedCoverData` + `branchedDegree`, existence unproven | 8,587 lines (`MappingDegree/`), ported from Brsanch, with **unconditional** witness existence |
| line integral / path machinery | `opaque` placeholder | 4,595 lines (`Path/`), real `∫ t in 0..1, α (γ t) (γ' t)` |
| complex torus / ULift | 2,653 lines, done and sound | 514 lines (`Surface/`) |

**(3) The sorry count badly understates the gap, in both directions.** Two distinct problems:

- **Eleven of the twenty engine sorries are vacuous as stated** — they carry `[JacobianChallenge.Periods.StableChartAt ℂ X]` alongside `[CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]`, and that hypothesis set is **contradictory** (§Gap 21). They can be "closed" by deriving `False`, which is not progress. Gaps 1, 2, 3, 4, 14, 15, 16, 17, 18, 19, 20 are all in this class. The other nine (5–13, the polygon tower) do *not* carry it — verified: `grep -c StableChartAt` returns 0 for `Hurewicz.lean`, `TietzeReduction.lean`, `DualGraphCut.lean`, `HandleSwapHomeo.lean` — but **four of those nine are provably false as stated** (5, 6, 8, 9; counterexamples in §Gaps 5–13), and the tower they belong to appears to be **unreachable from `Solution.lean` at the term level**: a declaration-level dependency sweep from the public API finds 0 reachable declarations in `TietzeReduction.lean`, `DualGraphCut.lean`, `HandleSwapHomeo.lean`, `SurfaceClassification.lean` and `Polygon4gCellular.lean`. So of twenty engine sorries, **one (gap 7) is both non-vacuous, true, and cheap**; three (11, 12, 13) are true, hard, and apparently off the critical path; and sixteen need restating or retiring before any of them is worth proving.
- **Several load-bearing *definitions* are placeholders, so the sorries above them are not the real frontier.** The period pairing is literally the zero map (`Periods/PeriodFunctionalU.lean:75`, `:95`), so the period lattice is `⊥` — proved in-tree as `basisAlignedPeriodSubgroupConcreteU_eq_bot` (`Periods/PeriodSubgroupZLatticeU.lean:82-85`). The Abel–Jacobi map is extracted from `opaque pathIntegralFunctionalBundleU` whose spec is satisfied by the identically-zero functional (`AbelJacobi/PathIntegralFunctionalU.lean:61-69`). The exterior derivative is `0` (`HolomorphicForms/SmoothDifferentialForm.lean:68-73`). "Global Stokes on a compact 2-manifold with corners" reduces to `0 = 0` (`Blueprint/Sec03/StokesOnRSWithBoundary.lean:92-113`, `:448-479`). Four of the gaps (14, 15, 16, 17) are therefore **false under their intended reading**, independently of the vacuity.

**(4) What rkirov has that is most worth taking is the *bottom* of his stack, not the top.** The lowest layers — `Path/LineIntegral.lean` (527 lines, a real line integral), `Path/SmoothPathCore.lean` (970), `Path/CotangentCoeff.lean` (700, the correct treatment of chart-dependence and the direct replacement for `StableChartAt`), `exists_smoothPath_family` (`JacobianConstruction/PeriodLattice.lean:936`), `PeriodLattice/PeriodLatticeNondegenerate.lean` (294), `Surface/ULiftManifold.lean` (163) — are self-contained, sorry-free, and are exactly what is missing underneath our placeholders: ~2,200–3,000 lines that would make our Jacobian a real torus and our Abel–Jacobi map a real map. The *top* layers (Abel's sufficiency, Riemann–Roch, period-lattice discreteness) each sit on 10–20k lines of Čech/Dolbeault substrate and cannot be lifted piecemeal. His degree layer (`MappingDegree/`, 8,587 lines) is **not** worth taking — our own degree turns out to need a 10-line fix, not a port (§Gap 22).

**(5) He already ported from us.** `Jacobians/PlanarStokes/PlanarCompactSupportStokes.lean:10-14` credits our `Jacobian/Blueprint/Sec03/StokesOnRSWithBoundary.lean` rectangle Green's theorem, MIT, © Michal J Wallace. The traffic can go both ways, and the attribution precedent is already set in his file headers.

---

## 1. Summary table

Legend — **match?** SAME = same mathematical route · DIFF = different route · N/A = rkirov never needed the lemma. **portable?** refers to discharging *our statement as written*.

| # | decl (file:line) | our route (short) | rkirov counterpart | match? | portable as stated? | est. size | rec. |
|---|---|---|---|---|---|---|---|
| 1 | `analyticOfCurve_injective` (`AbelJacobi/AnalyticOfCurveBasis.lean:1965`) | separation obligation ⇒ injectivity, Type-0 | `JacobianTorus.ofCurve_inj` (`Jacobians.lean:281-298`) | N/A (dead code: zero call sites) | no — vacuous binder; nothing consumes it | −20 lines | **DELETE** |
| 2 | `pathIntegralFunctional_separates_pointsU` (`AbelJacobi/AnalyticOfCurveInjectiveU.lean:75`) | named Abel point-separation obligation | `abelJacobi_twoPoint_ne_zero` (`Abel/AbelFinal.lean:44-72`) | SAME route, utterly different granularity | **no** — subject is `opaque` with a zero witness; binder vacuous | 10k–30k (engine + substrate) | **RESTATE then ADAPT** |
| 3 | `stageA_surface_CW_basisU` (`Periods/H1BasisU.lean:73`) | Radó + Tietze + cellular H₁ at `Type u` | none | N/A | true but ≥1.5k lines; binder vacuous | retire | **RESTATE / retire** |
| 4 | `stageB_analytic_eq_topologicalGenusU` (`Periods/H1BasisU.lean:89`) | de Rham + Hodge rank comparison | comment only (`Forms/Genus.lean:11-14`) | N/A | true but ≥1k lines; binder vacuous | retire | **RESTATE / retire** |
| 5 | `orientable_letterPair_opposite_orientation` (`Periods/TietzeReduction.lean:89`) | Brahana handle separation | none | N/A | **no — FALSE** (counterexample below) | retire | **RETIRE** |
| 6 | `orientable_handleSwap_grouping` (`Periods/TietzeReduction.lean:97`) | group reduced word into handle blocks | none | N/A | **no — FALSE** (`TietzeEq` cannot introduce new letters) | retire | **RETIRE** |
| 7 | `handleSwap_index_ordering` (`Periods/TietzeReduction.lean:103`) | permuted blocks ≈ standard word | none | N/A | **yes** — true and cheap, pure list combinatorics | ~40 lines | **KEEP** |
| 8 | `wordQuotient_homeomorph_of_inverseCancel_step` (`Periods/TietzeReduction.lean:171`) | cancellation is a quotient homeomorphism | none | N/A | **no — FALSE** (disk vs S² at `w = [a,a⁻¹]`) | retire or add length guard | **RESTATE / RETIRE** |
| 9 | `tailRotate_geometric_maps` (`Periods/HandleSwapHomeo.lean:294`) | rigid disk rotation conjugates side pairings | none | N/A | **no — FALSE** (dihedral-orbit obstruction) | retire or restate at quotient level | **RESTATE / RETIRE** |
| 10 | `cut_along_nonTree_yields_unfoldedDisk` (`Periods/DualGraphCut.lean:142`) | Radó + dual spanning tree ⇒ 4g-gon | none — he priced this at "≥10k LoC … **Rejected**" (`docs/walls_bc_plan_2026-06-10.md:254-258`) | N/A | no; hypotheses are `PUnit`-vacuous, and likely false without `Orientable` | retire | **RETIRE** |
| 11 | `polygon4g_quotient_path_finite_lift_subdivision` (`Periods/Hurewicz.lean:1696`) | Lebesgue subdivision + local disk lifts | none | N/A | true but hard; not reachable from `Solution.lean` | retire | **RETIRE** |
| 12 | `polygon4g_partial_side_arc_homologous_to_edge_chain` (`Periods/Hurewicz.lean:2001`) | side-strip 2-chain repair | none | N/A | true but hard; not reachable | retire | **RETIRE** |
| 13 | `edgeChain_sum_singular_boundary_scalar_coefficient_zero` (`Periods/Hurewicz.lean:5826`) | edge chains are a free H₁ basis | none — he gets rank 2g from `ZLattice.rank ℝ` (`PeriodLattice/PeriodLatticeBasis.lean:71-72`) | N/A | true; not reachable | retire | **RETIRE** |
| 14 | `h1_basis_periodCoordinate_linearIndependent` (`Periods/PeriodFunctional.lean:599`) | symplectic basis + 4g-gon Stokes + Riemann bilinear + Hodge positivity | `span_real_truePeriodLattice_eq_top` (`PeriodLattice/PeriodLatticeNondegenerate.lean:104`) | DIFF (he uses the planar maximum principle) | **no — false for g ≥ 1** (`periodPairing = 0`) | 6k–9k to port the route | **ADAPT** |
| 15 | `h1_basis_riemannClassicalPeriodBasisU` (`Periods/PeriodVectorsLIU.lean:69`) | as 14, at `Type u` | `IsZLattice ℝ (truePeriodLattice X)` (`PeriodLattice/PeriodLatticeBasis.lean:54-55`) | DIFF; he needs no `Type u` twin | **no — false for g ≥ 1** | as 14 + ~300 | **PORT + RESTATE** (load-bearing) |
| 16 | `deRhamComparisonMap1_zero_period_closed_form_vanishing_provider` (`HolomorphicForms/DeRhamComparisonMap.lean:1112`) | de Rham comparison has trivial kernel | none (he calls it "the de Rham / Hodge wall") | N/A | **no — false**: unfolds to `H⁰(X,Ω¹) = 0` | 1.5k–2.5k from scratch | **RESTATE** |
| 17 | `hodgeRemainder_periodPayload_exact` (`HolomorphicForms/HodgeProjection.lean:170`) | harmonic projection has exact kernel | none; he gets `2g = rank H₁` via Čech+RR+Dolbeault | N/A | **no — false**: unfolds to `H₁(X,ℤ) = 0` | 5k+ (route change) | **RESTATE** |
| 18 | `exists_biholomorph_onePoint_of_genus_zero` (`HolomorphicForms/GenusZeroClassification.lean:912`) | Montel patch-gluing uniformization | none — he proves S² ⇒ g=0 by monodromy + Liouville | DIFF | no — he has no such theorem; our stated route is unsound | 8k–11k to replace its role | **RESTATE + ADAPT** |
| 19 | `complexSimplePolePrincipalPart_of_biholomorph_onePoint` (`HolomorphicForms/MeromorphicToBranchedCover.lean:3010`) | pull back `1/z` along the biholomorphism | `toSphere` lemmas, opposite direction (`ProperDegree/DegreeOneSphere.lean:327`, `:386`) | DIFF direction | yes, but cheaper to prove locally | 150–300 lines | **KEEP (prove) or drop** |
| 20 | `exists_biholomorph_onePoint_of_analyticGenus_zero` (`HolomorphicForms/MeromorphicToBranchedCover.lean:3061`) | "packaging" of gap 18 — **the `\uses` edge is circular** | `exists_singleSimplePole_of_genus_zero_of_rr` (`RiemannRoch.lean:73-162`) + RR | DIFF (he uses Riemann–Roch) | no — but the node one level down is | ~700 to isolate RR; ~14k to close it | **ADAPT** |
| 21 | `StableChartAt ℂ X` instance (`Solution.lean:37`) | assume `chartAt` is locally constant | none — zero occurrences in his repo | N/A | **no — the hypothesis set is contradictory** | ~125 files touched, +500–1000 / −400 | **RESTATE (delete class)** |
| 22 | `ContMDiff.degree` fallback (`Solution.lean:223-235`) | weighted fibre sum via `BranchedCoverData` | `degreeFiber` = regular-fibre card (`Jacobians.lean:443-444`) | DIFF (weighted-at-any-fibre vs unweighted-at-regular-fibre) | **not a hack** — the `else 0` is unreachable in context; only a *named* existence lemma is missing | **5–10 lines** (+60–120 for `degree_pos`) | **KEEP** (+ ADAPT his surjectivity lemma) |

---

## 2. Architecture comparison, definition by definition

### 2.1 What matches

**`genus` — identical notion.** rkirov: `genus X := Module.finrank ℂ (Jacobians.HolomorphicOneForms X)` (`Jacobians/Forms/Genus.lean:62-64`), with `HolomorphicOneForms X := ContMDiffSection 𝓘(ℂ) (ℂ →L[ℂ] ℂ) ω (fun x => TangentSpace 𝓘(ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)` (`:30-33`). Ours: `analyticGenus E X := Module.finrank ℂ (HolomorphicOneForm E X)` (`HolomorphicForms/FiniteDimensional.lean:27-32`) with `HolomorphicOneForm` a `ContMDiffSection` of the cotangent bundle (`HolomorphicForms/Defs.lean:23-29`). Both are the **analytic** genus. Worth noting: rkirov's own early design doc proposed the *topological* genus `finrank ℤ H₁ / 2` (`docs/DESIGN.md:27-28`) and the shipped code does not use it — the same conclusion `ref/plan.md:39` reached.

One difference: rkirov takes `finrank` unconditionally (it returns 0 for infinite-dimensional modules — he says so at `Forms/Genus.lean:56-61`), whereas `analyticGenus` is gated on `[FiniteDimensionalHolomorphicOneForms E X]`, discharged globally at `Solution.lean:39-42`. His is the lighter convention; ours is more informative. Not a porting obstacle either way, but his signature has fewer instance arguments, which matters when porting statements.

**Carrier and universes — identical strategy.** Both run the construction on `Fin g → ℂ` rather than on `H⁰(X,Ω¹)^∨`, and both `ULift` a `Type 0` torus into `Type u`. Both independently built the ULift manifold transport that Mathlib lacks: his `Jacobians/Surface/ULiftManifold.lean` (163 lines, generic in the model/space — `instChartedSpace:54`, `instIsManifold:75`, `contMDiff_uliftDown:88`, `contMDiff_uliftUp:108`, `instLieAddGroup:142`); ours `Jacobian/ComplexTorus/ULiftTransport.lean` (445 lines, specialised to the torus — `complexTorusULift_chartedSpace:79`, `complexTorusULift_isManifold:134`, `complexTorusULift_lieAddGroup:365`, `contMDiff_uLift_up:380`, `ULiftContinuousAddMonoidHom':429`). Our note in `ref/plan.md:286-296` that "the universe gap is a false wall" is vindicated; `tex/sections/07-complex-tori-and-jacobians.tex:106-112` describes both implementations correctly.

**The complex-torus package.** `tex/sections/07-complex-tori-and-jacobians.tex:54-62` (`prop:complex-torus-package`) is architecture-level prose that applies verbatim to rkirov's `JacobianConstruction/ZLatticeQuotient.lean` (765 lines). Our `Jacobian/ComplexTorus/` (2,653 lines) is the one layer where we are ahead in generality and sound throughout.

**`pushforward`/`pullback` shape.** Both descend an ambient linear map through the lattice quotient: his `ZLatticeQuotient.pushforward` / `.pullback` (`JacobianConstruction/ZLatticeQuotient.lean:597`, `:609`) applied to `ambientPhi` / `ambientPullbackJac` (`Jacobians.lean:318-323`, `:383-388`); ours `ComplexTorus.ULiftContinuousAddMonoidHom'` applied to `TraceDegree.analyticPushforwardU` / `analyticPullbackU` (`Solution.lean:147-152`, `:187-191`). `tex/sections/09-degree-trace-push-pull.tex`'s trace framing matches his `MeromorphicTrace/` (5,823 lines).

### 2.2 What does not match — and this is where porting cost lives

**The period lattice is generated differently.** This is the single most consequential definitional mismatch.

- rkirov: `truePeriodLattice X := Submodule.span ℤ (closedLoopPeriods X)` (`JacobianConstruction/PeriodLattice.lean:573-577`), where `closedLoopPeriods X := {v | ∃ γ, IsClosedSmoothLoop γ ∧ v = periodVec γ}` (`Path/SmoothPathCore.lean:127-130`), `periodVec γ i := lineIntegral (periodBasisForm X i) γ` (`:94-97`), and `lineIntegral α γ := ∫ t in (0:ℝ)..1, α.toFun (γ t) (pathSpeed γ t)` (`Path/LineIntegral.lean:49-52`). The forms basis comes from `ambientIso X : (Fin (genus X) → ℂ) ≃ₗ[ℂ] HolomorphicOneForms X` (`Forms/HolomorphicForms.lean:231-236`). **No singular homology anywhere.**
- ours: the image of singular `H₁` under a period pairing — `IntegralOneCycleU X` from Mathlib's `singularHomologyFunctor` (`Periods/IntegralOneCycleU.lean:53-56`), `periodPairingComplexU : IntegralOneCycleU X →+ (HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ)` (`Periods/PeriodFunctionalU.lean:89-108`), range transported to `Fin g → ℂ`, bundled at `Periods/PeriodFullComplexLatticeU.lean:67-75`.

Consequences: (i) the *entire* `H₁`-basis / Hurewicz / polygon chain exists only to make our generating set computable, and is unnecessary under his definition; (ii) his statement is already `{X : Type*}` (`PeriodLattice/PeriodLatticeBasis.lean:30-31`), so the whole `…U` mirror layer we built to work around the `Type 0` pin in `IntegralOneCycle` (`Periods/IntegralOneCycleU.lean:10-17`) disappears; (iii) `tex/statements/dependency-index.tex:17-18` ("`thm:period-lattice` ← Riemann bilinear relations, symplectic basis of `H₁(X,ℤ)`") would be rewritten, and `tex/sections/06-periods-and-riemann-bilinear.tex`'s `\uses{input:riemann-bilinear}` edge at `:818` dropped.

**He has no chart-stability hypothesis; we have a contradictory one.** Zero occurrences of `StableChartAt` in his 72k lines. Where we assume `chartAt` is locally constant, he takes the chart *at the moving point* and carries pointwise differentiability per lemma: `lineIntegral` uses `chartAt (γ t)`, and lemmas carry e.g. `hγ_diff : ∀ t ∈ Set.uIcc 0 1, DifferentiableAt ℝ ((chartAt (H := ℂ) (γ t)).toFun ∘ γ) t` (`Path/LineIntegral.lean:517-518`). He records the decision explicitly (`Path/LineIntegral.lean:25-28`: chart-independence "is not formalized; every development downstream uses this one fixed chart-based definition, so no compatibility lemma is needed") and diagnoses our exact error (`Path/CotangentCoeff.lean:12-19`: the naive global coefficient "is **discontinuous** in general … continuous iff the tangent bundle is trivialized by the atlas, i.e. parallelizable — false for genus ≥ 2", dated `:30` to 2026-05-30). See §Gap 21.

**Degree.** His `ContMDiff.degree f hf := Jacobians.degreeFiber f hf` (`Jacobians.lean:443-444`), unweighted cardinality of a *regular* fibre, with a **named** unconditional witness-existence lemma (`regularValueWitnessReg_nonempty_of_nonConstantMap`, `ProperDegree/Degree.lean:37-46`) and `ContMDiff.degree_pos` (`Jacobians.lean:449-461`). Ours is a *weighted* fibre sum over **any** fibre, with constancy bundled into `BranchedCoverData.fiberSum_const`. Both match the blueprint's prose; the difference is only that he names the existence lemma and we don't. See §Gap 22 — this one turned out well.

**Toolchain.** One minor release apart (v4.30.0 / `c5ea003` vs v4.31.0-rc1). Porting cost is ordinary — lemma renames, `simp` set drift, `WithTop ℕ∞` / `ContDiff` churn — but note his development is stated at smoothness `ω` while our `HolomorphicForms`/`Periods` layers are stated at `(⊤ : WithTop ℕ∞)`. `Solution.lean` works at `ω`, so ported statements are most comfortably restated at `ω` too.

---

## 3. Gap-by-gap

Ordered thematically rather than numerically, because several gaps only make sense together: 1–2 (Abel–Jacobi injectivity), 3–4 and 14–15 (the H₁-basis / period-coordinate chain), 16–17 (the de Rham/Hodge double-count), 18–20 (genus-zero classification), 21 (`StableChartAt`), then 5–13 as one block (the polygon tower) and 22 (degree). The summary table in §1 is in numeric order.

### Gap 1 — `analyticOfCurve_injective` (`Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean:1965`)

**(a) Our planned route.** `ref/plan.md:491-498`: "Injectivity is now isolated as a single named obligation, `pathIntegralFunctional_separates_points` (period-congruent integrals at distinct points force the points equal), consumed by `Solution.ofCurve_inj`. The Abel two-point construction feeding it is sorry-free in `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean`." Blueprint: `tex/sections/08-abel-jacobi-map.tex:482-490`, `lem:analytic-of-curve-injective`, `\uses{thm:abel-point-separation}`, GitHub #224 — "Open obligation (`sorry`) until the genus-zero single-pole route lands." The in-file plan (`:1952-1956`) is to forward from the sorry-free `analyticOfCurve_injective_with_meromorphicData` (`:1916-1927`) once route data can be manufactured.

**(b) rkirov's counterpart.** `JacobianTorus.ofCurve_inj` (`Jacobians.lean:281-298`) — 18 lines: basepoint change (`ofCurve_basepoint_change`, `:259-262`) + `abelJacobi_twoPointDivisor` + `abelJacobi_twoPoint_ne_zero` (`Abel/AbelFinal.lean:44-72`).

**(c) Match verdict: N/A — rkirov never needed this, and neither do we.** This declaration has **zero call sites** in our repo (grep: only its own docstrings mention it). The public `Jacobian.ofCurve_inj` (`Solution.lean:132-135`) routes through the `…U` branch (gap 2) instead. It is a Type-0 duplicate.

**(d) Portability.** Nothing to port — there is a declaration to delete. Its docstring claim that it "matches the frozen public `ofCurve_inj` signature" is stale: the frozen public decl consumes `analyticOfCurve_injectiveU`.

**(e) Plain-English impact.** `lem:analytic-of-curve-injective` has no `layman` block of its own; the narration covering it is the section opener (`tex/sections/08-abel-jacobi-map.tex:19-33`) and the `thm:abel-point-separation` block (`:454-469`). Deleting the Lean decl costs no prose — but the blueprint currently shows **two** open obligations where only one exists, which should be fixed.

**(f) Recommendation: DELETE** (or restate as `:= analyticOfCurve_injectiveU` specialised to `Type 0`, so there is exactly one obligation in the repo).

### Gap 2 — `pathIntegralFunctional_separates_pointsU` (`Jacobian/AbelJacobi/AnalyticOfCurveInjectiveU.lean:75`)

```lean
theorem pathIntegralFunctional_separates_pointsU
    (P : X) (h : 0 < analyticGenus ℂ X) (Q₁ Q₂ : X)
    (hperiod : -pathIntegralFunctionalU X P Q₁ + pathIntegralFunctionalU X P Q₂ ∈
        basisAlignedPeriodSubgroupConcreteU X) :
    Q₁ = Q₂ := sorry
```

**(a) Our planned route.** `tex/sections/08-abel-jacobi-map.tex:493-500`, `lem:path-integral-functional-separates-points-u`, GitHub #225. The section opener states the classical argument we intend (`:19-33`): "Equality of Abel–Jacobi images would force a principal divisor of the form 'one point minus another' … That function is a degree-one map to the Riemann sphere — and section 4 already proved that any degree-one holomorphic map from a compact Riemann surface to the sphere is a homeomorphism. So the surface is the sphere, but the sphere has genus zero, contradicting our positive-genus assumption." The module docstring (`AnalyticOfCurveInjectiveU.lean:21-40`) explains the decision to isolate it rather than re-thread the Type-0 chain at `Type u`.

**(b) rkirov's counterpart.** `Jacobians.abelJacobi_twoPoint_ne_zero` (`Abel/AbelFinal.lean:44-72`):

```lean
theorem abelJacobi_twoPoint_ne_zero (h : 0 < genus X) {P Q : X} (hPQ : P ≠ Q) :
    abelJacobi ⟨twoPointDivisor X P Q, twoPointDivisor_mem_degZero X P Q⟩ ≠ 0
```

Route (Forster 19.10 / 20.7, dissection-free): a 1-chain with all basis periods zero admits a `∂̄`-potential (`Abel/AbelEngineSigma.lean:390-396` `exists_dbar_potential_of_oneChain`), from which `F := e^{−u}·G` is genuinely meromorphic with the centred local normal form `f̂ = H·(w−w₀)^{∂c(a)}`, `AnalyticAt ℂ H`, `H ≠ 0` (`Abel/AbelEngineMeromorphic.lean:70-76`); that gives a degree-one map to the sphere, hence genus 0, contradiction. The `∂̄`-solvability criterion needs `dim_ℝ H^{0,1} = 2·h¹(𝒪) = 2g`, i.e. the Dolbeault comparison plus `FiniteCover.h1Dim_zero_eq_genus` (`H1Genus/CechH1Genus.lean:119-120`). Engine size: `Meromorphic/Abel.lean` 586 + `Abel/` 3,087 + `AbelWeak/` 2,144 + `H1Genus/` 1,079 + `ProperDegree/DegreeOneSphere.lean` 673 ≈ **7,600 lines**, over a further ~20k of Čech/Dolbeault/Stokes/residue substrate.

**(c) Match verdict: SAME ROUTE, radically different granularity.** `tex:19-33` is a prose description of `Abel/AbelFinal.lean:13-20`. He built it; we named it.

**(d) Portability as stated: NO, for two independent reasons.**

1. **The subject does not exist yet.** `pathIntegralFunctionalU P Q := (pathIntegralFunctionalBundleU X).val P Q` (`AbelJacobi/PathIntegralFunctionalU.lean:76-77`), and `pathIntegralFunctionalBundleU` is `opaque` (`:69`) over a structure whose only fields are `val`, `self_spec : ∀ P, val P P = 0`, and `contMDiff_endpoint` (`:40-53`) — with an `Inhabited` instance witnessed by `fun _ _ => 0` (`:61-62`). An `opaque` constant has no defining equation, so nothing beyond those three fields is derivable about it, and point-separation *fails* for the zero witness whenever `0 < analyticGenus ℂ X` and `X` has two points. **This is an open definition obligation masquerading as an open proof obligation**, and the blueprint should say so.
2. **The binder list is contradictory** (`:50-54` includes `[StableChartAt ℂ X]` with `[CompactSpace X] [ConnectedSpace X]`) — see §Gap 21. So the statement is simultaneously vacuously true and useless.

Definition mismatches if the engine is ported: statement level (our path-integral-coordinate separation vs his divisor-level non-vanishing — bridgeable via `abelJacobi_twoPointDivisor`, `Meromorphic/Abel.lean:537`, with `JacobianTorus.ofCurve_inj` as the 18-line template); the integral (blocking — must be built first, ~1.5k lines modelled on `Path/SmoothPathCore.lean` 970 + `Path/LineIntegral.lean` 527 + `Path/CotangentCoeff.lean` 700); the path family (his `exists_smoothPath_family`, `JacobianConstruction/PeriodLattice.lean:936-978`, is a real proof via chart-ball chains); the lattice/ambient transport (~100–200 lines, our dual-equiv layer already exists at `Periods/BasisAlignedPeriodSubgroupU.lean:65-71`); universes (**no mismatch** — he is `Type*` already, which deletes our `…U` duplication); extra binders (`[StableChartAt]` must go; his `[Nonempty X]` comes free from `[ConnectedSpace X]`). **Realistic total: 10k–30k lines, i.e. adopting his lower layers, not a patch.**

A further honesty note on the chain that feeds this. `ref/plan.md:496-497` says "The Abel two-point construction feeding it is sorry-free". Literally true, but the chain is vacuous scaffolding: `structure LogPeriodVanishing` has the single field `witness : Unit` (`AnalyticOfCurveBasis.lean:341-347`), so does `SingleValuedLogPrimitive` (`:1127-1134`); `glue_local_extensions_to_global` has hypotheses `(_hHol : True) (_hZero : True) (_hPole : True)`, conclusion `True`, proof `trivial` (`:1322-1335`); `construct_toMap_global` is `∃ (_ : X → OnePoint ℂ), True` discharged by `fun _ => OnePoint.infty` (`:1341-1345`). So `abelJacobi_image_zero_implies_principal` (`:1524-1533`) — the `\leanok` backing `thm:abel-basis-aligned-two-point` — carries no analytic content, and the `\leanok` marks on `lem:abel-two-point-form` (`tex:292-300`) and `lem:two-point-principal-packaging` (`tex:333-343`) are misleading.

**(e) Plain-English impact.** The prose at `tex:454-469` ("This is the headline anti-hack theorem… It rules out trivial fake constructions like `Jacobian X := PUnit`") is **correct mathematics and should be kept verbatim** — it describes rkirov's route accurately. What must change is the honesty framing: `input:abel-theorem` (`tex:503-510`, layman `:513-525`, "the deepest classical ingredient the project consumes") is the right node; the `\leanok` marks beneath it (S19/S19a/S19b) should be withdrawn until the `Unit`/`True` scaffolding is replaced.

**(f) Recommendation: RESTATE, then ADAPT.** In order: (i) replace `opaque pathIntegralFunctionalBundleU` with a real line integral along a real path family — port `pathSpeed`/`lineIntegral`/`periodVec` (`Path/LineIntegral.lean:41-52`, `Path/SmoothPathCore.lean:94-97`) and `exists_smoothPath_family`; (ii) drop `[StableChartAt ℂ X]`; (iii) restate at divisor level following `abelJacobi_twoPointDivisor` + `JacobianTorus.ofCurve_inj`, keeping the path-integral form as a derived corollary; (iv) then either port the Abel engine (~7.6k + substrate) or keep it as one clearly-labelled classical input — which `tex:502-511` already does honestly.

### Gap 3 — `stageA_surface_CW_basisU` (`Jacobian/Periods/H1BasisU.lean:73`)

**(a) Our planned route.** Docstring, `H1BasisU.lean:57-65`: "**Universe-`u` Stage-A surface classification + cellular H₁ provider.** … This is the genuinely missing bridge: re-running the surface-classification, cellular-homology, and singular-vs-cellular comparison for Mathlib's `singularHomologyFunctor.{u}` with `ULift.{u} ℤ` coefficients." Statement: `Nonempty (Module.Basis (Fin (2 * topologicalGenusU X)) ℤ (IntegralOneCycleU X))`. The Type-0 analogue **is** proved — `stageA_surface_CW_basis` (`Periods/PeriodFunctional.lean:218-230`) via `singularH1_basis_of_compactOrientableSurface` (`Periods/SurfaceClassification.lean:357-366`) ← `compactOrientableSurface_homeomorph_polygon4g_topologicalGenus` (`:295-308`) ← `polygon4g_singularH1_iso_freeZ` (`:243-246`). So this gap is the universe/coefficient re-run, not new mathematics. Blueprint: `tex/sections/05-polygonal-model.tex:242` (`\subsection{The polygonal model theorem (Stage A)}`) with the layman block at `:246-274`; `ref/plan.md:310-313` calls this cluster "the current heavy edge".

**(b) rkirov's counterpart: none.** No H₁ basis, no cellular homology, no `singularHomology` in the lattice construction. The decision is on record, `docs/walls_bc_plan_2026-06-10.md:148-151`: "`CutSurface` should be **retired, not constructed**. Its sole consumer is `exists_periodLattice_realBasis`; Forster 21.4 proves that statement (same signature, via Mathlib's ZLattice API) with no dissection, no R1/R2, no boundary words." And on the state of Mathlib (`:161-163`): "`Topology/CWComplex/` has bare definitions only … no triangulations, no surface classification … Route B-I's topology is fully greenfield."

**(c) Match verdict: N/A.**

**(d) Portability.** Nothing to port. The statement is *true* (H₁(X; ULift ℤ) ≅ ℤ^{2g}) but expensive — it needs free + finitely-generated-ness of the `ULift.{u} ℤ`-coefficient `H₁` functor, which is not a reindexing; the docstring itself calls it "substantial deferred infrastructure, well beyond a single commit" (`H1BasisU.lean:30-33`). Realistically 1.5k–4k lines. It is also vacuously provable from the contradictory binder.

**Can it be skipped?** Yes. Consumers of `stageA_surface_CW_basisU`: only `h1_basis_of_compact_riemann_surfaceU` (`H1BasisU.lean:109`), whose only consumers are `symplectic_basis_of_cyclesU` (`PeriodVectorsLIU.lean:142`) and `symplectic_basis_of_cycles_riemannClassicalPeriodBasisU` (`:152`) — both existing solely to feed `periodSubgroup_spans_realU`. Under rkirov's loop-span lattice, gaps 3, 4, 14, 15 all vanish together. No other file reads these four declarations.

**(e) Plain-English impact.** Orphaned if the route is replaced: `tex/sections/05-polygonal-model.tex:4-56` (chapter opener), `:246-274` (Stage A layman), `:204-220` (Radó), `:222-240` (Tietze), `:562`, and the "Analysis on the polygon" blocks at `:610`, `:623`, `:637`, `:650`, whose stated purpose is the bilinear-from-Stokes fold. The claim at `:34-39` that "Without this bridge, the genus-zero classification of section 4 would be circular" needs separate checking — `genus_eq_zero_iff_homeo` (`Solution.lean:63-66`) routes through `analyticGenus_eq_zero_iff_homeomorphic_sphere`, not through the polygon.

**(f) Recommendation: RESTATE / retire.** Replace the lattice definition with the loop-span one; delete `H1BasisU.lean` and the `symplectic_basis_of_cycles*U` scaffolding. If the polygon route is kept for its own sake, relabel this from "narrow Stage-A obligation" (`H1BasisU.lean:35-36`) to the multi-thousand-line item it is.

### Gap 4 — `stageB_analytic_eq_topologicalGenusU` (`Jacobian/Periods/H1BasisU.lean:89`)

**(a) Our planned route.** `H1BasisU.lean:75-81`: "**Universe-`u` Stage-B Hodge bridge.** The analytic genus agrees with the topological genus measured by `IntegralOneCycleU`." The Type-0 version is proved (`PeriodFunctional.lean:268-281`) via `two_analyticGenus_eq_finrank_intH1` (`HolomorphicForms/HodgeDeRhamRank.lean:36-45`) ← `realDimDeRhamH1_eq_two_analyticGenus` (Hodge) ∘ `realDim_deRhamH1_eq_finrank_intH1` (de Rham + UCT, `HolomorphicForms/DeRhamSingular.lean:75-82`) — i.e. it rests on gaps 16 and 17. Blueprint: `tex/sections/05-polygonal-model.tex:420-446` (`thm:analytic-eq-topological-genus`), `:314-342` (`def:topological-genus` + layman), `:360-418` (de Rham / Hodge laymans), classical input `input:hodge-deRham` at `tex/sections/06-periods-and-riemann-bilinear.tex:695-701`.

**(b) rkirov's counterpart: none as a theorem.** He records the fact only as a comment — `Forms/Genus.lean:11-14`: "This matches the analytic definition; with real content (`FiniteDimensional ℂ (HOF X)` from Cartan–Serre) it agrees with the topological definition `finrank ℤ (H₁(X, ℤ)) / 2` by Riemann–Roch / Dolbeault." He never states or uses it; every downstream theorem is phrased in the analytic genus only.

**(c) Match verdict: N/A** — he avoided topological genus by defining genus analytically and never comparing.

**(d) Portability.** Nothing to port. **And it is not needed:** our `genus` is already `analyticGenus` and the lattice ambient is already `Fin (analyticGenus ℂ X) → ℂ`; topological genus enters *only* as the index of the H₁ basis. Delete the basis and the comparison is unreferenced. (His `finrank ℂ (cechH1 0) = genus X`, `H1Genus/CechH1Genus.lean:119`, is a *Čech*-side count for the Abel engine, not a singular-homology comparison.)

**(e) Plain-English impact.** The topological-genus and de Rham/Hodge laymans (`05:328-342`, `:360-377`, `:379-396`, `:398-418`) become orphaned *from the lattice argument* but should **not** be deleted: `genus_eq_zero_iff_homeo` still ties genus to topology, so the "analytic = topological" narrative can be re-scoped from §5/§6 to §4. Needs rewording, not removal. The `input:hodge-deRham` umbrella loses its `\uses` edge from `thm:period-lattice` (`06:818`).

**(f) Recommendation: RESTATE.** Retire together with gap 3; demote the analytic-vs-topological narrative from "period-lattice prerequisite" to "genus-zero-classification context".

### Gap 14 — `h1_basis_periodCoordinate_linearIndependent` (`Jacobian/Periods/PeriodFunctional.lean:599`)

**(a) Our planned route.** Docstring `:579-587`: "A concrete `Module.Basis` supplied by the surface-classification/H₁ construction has basis-aligned period-coordinate rows that are ℝ-linearly independent … only for an H₁ basis carrying the missing classical symplectic/Stokes/Hodge structure." The intended proof is spelled out at `:628-642`: period matrix `a_ij`, `riemann_bilinear_identity`, `hodge_form_posDef_on_periods`, then `real_linearIndependent_of_quadratic_pos_def` — with the honest caveat "needs Stokes on the fundamental polygon … An arbitrary injective family of cycles need not have nondegenerate period pairings." Note the supporting pieces are themselves stand-ins: `wedge_integration_pairing_exists` (`:379-387`) is discharged with `⟨fun _ _ => 0, …⟩`, and `riemann_bilinear_identity` (`:404-428`) is proved by *defining* `Q` to be the period sum. Blueprint: `tex/sections/06-periods-and-riemann-bilinear.tex:360-365`, `:494-517` (`thm:period-vectors-full-real-rank`, `lem:riemann-classical-real-li-input`, GitHub #227), `:543-551` (`input:riemann-bilinear`), laymans at `:370-385`, `:387-404`, `:445-461`, `:519-538`.

**(b) rkirov's counterpart.** `Jacobians.span_real_truePeriodLattice_eq_top` (`PeriodLattice/PeriodLatticeNondegenerate.lean:104-292`, ~190 lines of proof in a 294-line file), Forster 21.4(c). File header `:6-21`, verbatim:

> If a nonzero real-linear functional vanished on `truePeriodLattice X`, writing it as `v ↦ Re (∑ⱼ dⱼ·vⱼ)` would give `d ∈ ℂ^g ∖ {0}` with `Re ∫_γ ∑ dⱼωⱼ = 0` for every closed smooth loop `γ`. Then `u(x) := Re (∑ⱼ dⱼ·periodVec (smoothPath x₀ x)ⱼ)` is … **locally the real part of an analytic function** … At a maximum of `u` (compactness) the open-mapping dichotomy forces `H` locally constant, so `{u = max}` is clopen, `u` is constant, every chart derivative … vanishes, and `∑ dⱼωⱼ = 0` … No harmonic theory, no surface integration: the only analysis is Mathlib's planar open-mapping dichotomy (`AnalyticAt.eventually_constant_or_nhds_le_map_nhds`).

Atoms: `eventually_const_of_re_le` (`:37-55`), `exists_re_dotProduct_repr` (`:61-95`), with `localLiftChart_analyticAt` / `localLiftChart_hasDerivAt_center` from `PeriodLattice/JacobiLocalMap.lean:56`, `:101`. Then `IsZLattice ℝ (truePeriodLattice X)` (`PeriodLattice/PeriodLatticeBasis.lean:54-55`), `DiscreteTopology` (`:35-50`, from `truePeriodLattice_isolated_zero`, `PeriodLattice/PeriodLatticeDiscrete.lean:115`, 554-line file, Forster 21.4(b) via the Abel engine + residue theorem), headline `exists_periodLattice_realBasis` (`:63-79`).

Note: his own hint doc says the cheapest route is "Riemann cut-surface + Green's-theorem flavor of period nondegeneracy, **not** Hodge / de Rham" (`docs/clean_room_blueprint.md:293-294`). That line is **stale relative to the shipped code**, which uses the maximum principle. Read the Lean, not the hint.

**(c) Match verdict: DIFF.** We plan symplectic H₁ basis + 4g-gon Stokes + Riemann bilinear + Hodge positivity. He uses no basis, no Stokes, no bilinear relations — one maximum-principle argument against an arbitrary killing functional. His route also **reverses the dependency**: his lattice theorem consumes Abel's sufficiency (`docs/walls_bc_plan_2026-06-10.md:112-115`), and the symplectic basis comes out as a *consequence* (Forster 21.5 Remark), not an input.

**(d) Portability as stated: NO — the statement is false for g ≥ 1.** `periodPairing ℂ X` is the descent of `let I := 0` (`PeriodFunctional.lean:109-112`), hence the zero homomorphism; the conclusion asserts ℝ-linear independence of a constant-zero family indexed by `Fin (2g)`. Our own tree proves the corresponding `U` fact (`periodPairingComplexU_eq_zero`, `Periods/PeriodSubgroupZLatticeU.lean:54`), and the module docstring says it outright (`:11-14`): "while the integration map of the period pairing is the placeholder `0`, the period pairing is the zero homomorphism and the '2g independent period vectors' claim is vacuously unavailable."

After repairing the pairing, rkirov's result is a near-drop-in for the downstream *goal* (`periodSubgroup_spans_real`), not for this lemma. Bridges: (i) replace `AddSubgroup.map dualEquiv (periodPairing.range)` by `Submodule.span ℤ {periodVec γ | IsClosedSmoothLoop γ}` (~60 lines, but a definitional change rippling through `BasisAlignedPeriodSubgroup{,U}.lean`, `PeriodSubgroupZLatticeU.lean`, `PeriodFundamentalDomain{,U}.lean`, `AbelJacobi/AnalyticOfCurveInjectiveU.lean:73`, `TraceDegree/AnalyticP{ull,ush}backU.lean:68-75`); (ii) coordinate frame — our `holomorphicOneFormDualEquiv` vs his `ambientIso ∘ Pi.basisFun`, both arbitrary, related by a `LinearEquiv` of `Fin g → ℂ` under which `IsZLattice` is invariant (~80–150 lines, or 0 if we adopt his frame); (iii) universes — he is `Type*`, which *removes* our `…U` layer; (iv) `StableChartAt` must go; (v) the real cost is his upstream — nondegeneracy needs `PeriodLattice/OfCurveAnalyticitySkeleton.lean` (1,360) + `JacobianConstruction/PeriodLattice.lean` (1,509) + `Dolbeault.exists_localRep_self_ne_zero`, and *discreteness* needs the whole Abel engine + residue theorem. **Estimate: nondegeneracy ≈ 0.6–1.2k lines; discreteness ≈ 5–8k; total ≈ 6–9k** — still far cheaper than Radó + Tietze + cellular homology + manifold de Rham + Hodge, which our route needs and for which there is no Lean precedent.

**(e) Plain-English impact.** Survives verbatim: `06:519-538` (the full-rank layman — "inside a 2g-real-dimensional space we have 2g independent vectors; they form a basis … their integer combinations form a **full lattice**"), `:788-813` (period pairing), `:826-862` (period lattice). Needs rewording: `:360-365` (the "cutting along a symplectic basis" preamble), `:370-385` (symplectic basis becomes a consequence), `:387-404` (bilinear identity), `:445-461` (Hermitian positivity — "No positivity, no lattice" becomes false under Forster's route). Orphaned: `lem:riemann-classical-real-li-input` (`:506`), `input:riemann-bilinear` (`:543`), `lem:period-pairing-satisfies-bilinear-identity` (`:656`), `lem:hodge-form-pos-def-on-periods` (`:673`), the `\uses` edge at `:818`, and the polygon "Analysis" laymans (`05:610`, `:623`, `:637`, `:650`).

**(f) Recommendation: ADAPT (port the route, not the statement).** (1) Mark this **unsound as stated** in the ledger and delete rather than attempt; (2) fix `periodPairing`'s `I := 0`; (3) redefine the lattice as the ℤ-span of closed-smooth-loop period vectors; (4) port `PeriodLatticeNondegenerate.lean` as the new `periodSubgroup_spans_real`; (5) drop `StableChartAt`. Discreteness is currently "proved" on the `⊥` lattice (`PeriodSubgroupZLatticeU.lean:92-95`) and is the largest honest item in this layer.

### Gap 15 — `h1_basis_riemannClassicalPeriodBasisU` (`Jacobian/Periods/PeriodVectorsLIU.lean:69`)

**(a) Our planned route.** `PeriodVectorsLIU.lean:60-64`: "the narrow remaining Riemann-bilinear frontier: a concrete H₁ basis is the classical/symplectic period basis with nondegenerate basis-aligned coordinates." Blueprint `tex/sections/06-periods-and-riemann-bilinear.tex:841-847` (`lem:riemann-classical-real-li-input-u`, GitHub #241), a `\uses` of `thm:period-lattice` (`:816-818`).

**This is the load-bearing gap of the Periods layer.** It is the sole frontier sorry on the critical path to the public Jacobian's compactness: `:149-154` → `:173-181` `periodVectors_linearIndependentU` → `:189-201` `periodSubgroup_spans_realU` → `PeriodFundamentalDomainU.lean:69-72` `basisAlignedPeriodSubmoduleℤU_isZLattice` → `:82-120` `exists_compact_periodFundamentalDomainU` → `PeriodFullComplexLatticeU.lean:67-75` → `Solution.lean:89-92` `Jacobian X` → `CompactSpace (Jacobian X)` (`Solution.lean:110`). Gaps 3 + 4 are load-bearing only because they supply the basis this consumes.

**(b) rkirov's counterpart.** As gap 14: `span_real_truePeriodLattice_eq_top` + `IsZLattice ℝ (truePeriodLattice X)` + `exists_periodLattice_realBasis`. Crucially his is already `{X : Type*}` (`PeriodLatticeBasis.lean:30-31`) — there is **no `Type u` gap at all** in his development, so the entire motivation for our `…U` mirror layer disappears.

**(c) Match verdict: DIFF**, and no `Type u` companion needed.

**(d) Portability as stated: NO — false for g ≥ 1** (`periodPairingComplexU = 0` is proved at `PeriodSubgroupZLatticeU.lean:54`), and vacuously provable from the binder. His `IsZLattice ℝ (truePeriodLattice X)` *does* directly discharge what we actually want downstream once the lattice is redefined; `RiemannClassicalPeriodBasisU` and the transports `riemann_classical_real_LI_inputU` / `period_functionals_ℝ_linearIndependentU` / `period_vectors_linearIndependent_of_symplecticU` (`PeriodVectorsLIU.lean:77-132`, all currently sorry-free) become dead code. Bridge ≈ 150–300 lines of restatement on top of gap 14's 6–9k upstream port. **Universe bonus:** porting his `Type*` statement lets us delete `IntegralOneCycleU.lean`, `PeriodFunctionalU.lean`, `H1BasisU.lean`, `PeriodVectorsLIU.lean`, `BasisAlignedPeriodSubgroupU.lean`, `PeriodSubgroupZLatticeU.lean`, `PeriodFundamentalDomainU.lean` and simplify `PeriodFullComplexLatticeU.lean` — the whole "Option C / C2a–C3" containment layer described at `PeriodFullComplexLatticeU.lean:14-32`.

**(e) Plain-English impact.** As gap 14. Additionally the two universe-`u` blueprint lemmas at `06:833-847` are orphaned outright (neither has a layman block — they are bare lemmas with `\ghissue{240}`/`\ghissue{241}`), and `thm:period-lattice`'s `\uses` list (`06:818`) trims from five entries to one.

**(f) Recommendation: PORT (route) + RESTATE (statement).** This is where porting pays for itself: the gap is simultaneously (i) the sole load-bearing frontier for `IsZLattice`/compactness, (ii) false as stated, and (iii) the reason an entire parallel `…U` file layer exists.

### Gap 16 — `deRhamComparisonMap1_zero_period_closed_form_vanishing_provider` (`Jacobian/HolomorphicForms/DeRhamComparisonMap.lean:1112`)

**The substrate first.** `HolomorphicForms/SmoothDifferentialForm.lean` (146 lines) defines `SmoothDiffForm 1 X := SmoothDiffFormCoeff 1 X × SmoothDiffFormPeriodPayload 1 X` (`:47-56`) `= (Fin 2 → HolomorphicOneForm ℂ X) × (IntegralOneCycle X →ₗ[ℤ] ℂ)` (`:31-39`) — a **bare product with no compatibility constraint** — and `exteriorDerivative n X := 0` (`:68-73`), whence `ClosedForm 1 X = ⊤` (`:84-89`) and `ExactForm 0 X = ⊥` (`:92-97`). `deRhamComparisonMap1 X ω := ω.2` (`DeRhamComparisonMap.lean:43-55`) is the projection onto the payload; `HarmonicOneForm X := Fin 2 → HolomorphicOneForm ℂ X` (`HodgeStarRS.lean:45-48`) is *definitionally* the other factor and `harmonicProjection1 X ω := ω.1` (`HodgeProjection.lean:40-41`) projects onto it. The surrogate `H¹_dR` therefore has complex dimension `2g + 2g = 4g`, and gaps 16 and 17 each patch the excess by annihilating the *other* factor:

| gap | asserted | unfolds to | true iff |
|---|---|---|---|
| 16 | `ker(deRhamComparisonMap1) = ⊥` | `ω.2 = 0 → ω.1 = 0` | `H⁰(X,Ω¹) = 0` ⟺ **g = 0** |
| 17 | `ker(harmonicProjection1) = ⊥` | `ω.1 = 0 → ω.2 = 0` | `H₁(X,ℤ) = 0` |

Jointly they would force `genus X = 0` and `H₁(X,ℤ) = 0` for **every** compact Riemann surface, contradicting `ofCurve_inj`'s `0 < genus X`. **They are not two independent gaps; they are one double-count, and it cannot be discharged, only restated.** The blueprint already says they are one node: `input:hodge-deRham` has `\uses{lem:de-rham-zero-period-exactness-assembly, lem:hodge-zero-projection-exactness-assembly}` (`tex/sections/06-periods-and-riemann-bilinear.tex:695-701`).

**(a) Our planned route.** The docstring (`DeRhamComparisonMap.lean:1077-1103`) is candid that the statement is substrate-dependent: "in the present period-carrying `SmoothDiffForm` substrate, where `exteriorDerivative := 0`, an exact form *is* the zero form, so the honest analytic leaf is exactly this equality" (`:1086-1090`), and "this equality becomes fully true once `exteriorDerivative`/`deRhamComparisonMap1` are given their real chartwise/period content" (`:1098-1102`). The leaf has **no blueprint label**; the blueprint labels its sorry-free wrapper instead (`tex:728-734`, `lem:de-rham-comparison-map1-zero-period-primitive-exists-provider`, GitHub #242, "A closed 1-form whose de Rham comparison image (all periods) vanishes admits a global primitive, hence is exact. Open obligation (`sorry`)") — but `..._primitiveExists_provider` (`:1131-1142`) is sorry-free, being `refine ⟨0, ?_⟩; rw [...]`. That is blueprint drift: the English describes the true classical theorem while the Lean statement carrying the sorry is strictly stronger and false.

**On the `c89e833` / `e94a1a2` episode** (the brief's question). The commit message of `c89e833` diagnosed the falsity correctly: the leaf "was only valid because the surrogate `exteriorDerivative 0 := 0` makes `ExactForm 0 X = {0}`, conflating 'exact' with 'zero'. A zero-period closed 1-form is classically exact, not zero … so that leaf was mathematically false — an artifact of the `d = 0` collapse." It then moved the obligation into `SmoothDifferentialForm.lean` as `zeroPeriodPayload_isExact_provider … (hω : ω.2 = 0) : ω ∈ ExactForm 0 X`, advertised as "an existence statement that does not collapse to falsity". **That replacement was wrong on its own terms:** `ExactForm 0 X = LinearMap.range 0 = ⊥`, so `ω ∈ ExactForm 0 X` unfolds to `ω = 0` and the "fix" is the identical false claim relocated and disguised. The same file proves the collapse three lines away (`DeRhamComparisonMap.lean:1043-1044` discharges `η = 0` from `η ∈ ExactForm 0 X` by `simpa [ExactForm, exteriorDerivative]`). `e94a1a2` reverted it 2h13m later with only the boilerplate `git revert` message and no recorded rationale. **Verdict: the revert was correct, and the statement at line 1112 is false as written** (true only for g = 0; its hypothesis is satisfiable, so it is false-not-vacuous under the intended reading — and separately vacuous under the `StableChartAt` binder).

**Reach.** One direct call site (`:1141`), then `:1170` → `:2696` / `:2886` → `:2892-2900` → `:3295` → `:3336` → `:3349`, then `HolomorphicForms/DeRhamSingular.lean:48-54` → `:75-82` → `HodgeDeRhamRank.lean:36-45` → `Periods/PeriodFunctional.lean:268-281` → `analyticGenus_eq_topologicalGenus` → `thm:period-lattice` → `Solution.lean:91-92`. **It reaches the public Jacobian.**

**(b) rkirov's counterpart: none, by design.** `Jacobians/SphereTopology/GenusSphereBackward.lean:45-49`, verbatim:

> **Step 4 — closed-not-exact ⟹ nonzero period**: **absent** from both Mathlib (no manifold de Rham / no homotopy-invariance of curve integrals over manifold loops; the convex-set Poincaré lemma in `Mathlib/MeasureTheory/Integral/CurveIntegral/Poincare.lean` does not lift) and this repo (`Jacobians/Path/LineIntegral.lean` explicitly removed even a *local* version for lack of a `Convex`/`SimplyConnected` hypothesis). This is the de Rham / Hodge wall.

What he built instead is a holomorphic Poincaré lemma hypothesised on **simple connectivity**, not on vanishing periods: `HasHolomorphicPrimitives X := SimplyConnectedSpace X → ∀ η, ∃ F, MDifferentiable F ∧ ∀ x v, η.toFun x v = mfderiv F x v` (`SphereTopology/GenusZeroOfSphere.lean:87-95`), proved as `hasHolomorphicPrimitives` (`Monodromy/HolomorphicPrimitives.lean:241`) by **discrete analytic continuation with no integration** — `Monodromy/HolomorphicPrimitiveChain.lean:8-11`: "a `PrimitiveChain` is a partition `0 = t₀ ≤ … ≤ tₙ = 1` together with local primitives `Fᵢ` on opens `Uᵢ ⊇ γ([tᵢ, tᵢ₊₁])`; its `value` is the telescoping sum `∑ᵢ Fᵢ(γ(tᵢ₊₁)) − Fᵢ(γ(tᵢ))` — classically `∫_γ η`." Tower: `Monodromy/` 1,109 lines. His closest period-vanishing hypothesis has a *Dolbeault* conclusion, not a primitive: `exists_dbar_potential_of_oneChain` (`Abel/AbelEngineSigma.lean:390-396`).

He also states the policy: `formalization.yaml:145-159` — "Deliberately PDE-free and integration-light where Mathlib lacks foundations … the monodromy theorem (holomorphic Poincaré lemma) uses discrete analytic continuation along chains with no integration at all … Junk-free encodings replace naive ones: `Filter.Germ` (codiscreteWithin) for Čech `𝒪_D` cochains, germ-quotient linear systems, and the value-wise `dF = η` formulation for primitives."

**(c) Match verdict: N/A — no match and no counterpart.** Three independent mismatches: hypothesis (period-vanishing vs π₁-trivial), form class (smooth ℂ-valued vs *holomorphic* only), conclusion shape (membership in a `Submodule` vs an existential over a value-wise `mfderiv` equation). He never forms a de Rham complex: repo-wide grep for `deRham|Hodge|harmonic|Laplac|ExactForm|ClosedForm` returns **zero declarations**, only prose; his only form type is `SmoothCOneForms X` and his only operators are `differential` and `dbar` (`Jacobians/Dbar/RealForms.lean`, 181 lines) — no `d` on 1-forms, no 2-forms, no Hodge star, no Laplacian.

**(d) Portability: zero.** You cannot port a true theorem onto a false statement, and the definitional distance is total (real 1-form type, real chartwise `d`, exactness as an `mfderiv` equation, and — unbridgeably — his `SimplyConnectedSpace X` hypothesis, which gives nothing on a genus ≥ 1 surface). Porting his primitive machinery is ~1,100 lines and **would not discharge this gap**. A genuine "periods vanish ⇒ exact" additionally needs a real `SmoothDiffForm`/`d` substrate (~400–800 lines, invalidating the existing `…_exact_form_vanishes…` lemma web and hitting the coefficient-arity mismatch `c89e833` also flagged), line integration over singular 1-chains with homotopy invariance (~600+; he explicitly declined to build this), and universal-cover globalisation. **Realistic: 1,500–2,500 lines from scratch, nothing portable.**

**(e) Plain-English impact.** No layman block covers this lemma. The impact surfaces one hop up at `tex/sections/05-polygonal-model.tex:398-417`: "The Hodge / de Rham bridge is the deep input that makes the analytic and topological notions of genus agree … **Two of the four anti-hack theorems hinge on this rank computation** … Mathlib lacks the entire Hodge / de Rham apparatus on manifolds, making this the third major classical-analysis gap on the path, alongside Riemann-Roch and Stokes." By the blueprint's own account, these two gaps sit directly under two anti-hack theorems.

**(f) Recommendation: RESTATE** (then re-plan the route). (1) Retire the false statement — correctly this time: do not phrase the replacement as `∈ ExactForm 0 X` while `exteriorDerivative = 0`, which was precisely `c89e833`'s error; park it as the honest classical statement over a *real* form type that does not yet exist, so it cannot be silently discharged. (2) Fix the double-count first — it is upstream of both gaps. (3) Sync the blueprint: `tex:728-734` marks an open obligation against a sorry-free decl while the real sorry is unlabelled.

### Gap 17 — `hodgeRemainder_periodPayload_exact` (`Jacobian/HolomorphicForms/HodgeProjection.lean:170`)

```lean
theorem hodgeRemainder_periodPayload_exact
    (X : Type) [...] [JacobianChallenge.Periods.StableChartAt ℂ X]
    (ω : SmoothDiffForm 1 X) (hclosed : exteriorDerivative 1 X ω = 0) :
    ((0 : SmoothDiffFormCoeff 1 X), ω.2) ∈ ExactForm 0 X := by sorry
```

**(a) Our planned route.** File purpose (`HodgeProjection.lean:7-27`): "Harmonic projection: `H¹_dR ≃ Harm¹` … Mathlib v4.28.0 lacks the entire elliptic-operator / harmonic-projection apparatus", decomposed into existence of the projection, orthogonality (Hodge identity), surjectivity. The docstring **already concedes the statement is false** (`:157-162`): "NOTE (substrate frontier): on the current zero-differential `SmoothDiffForm` surrogate `exteriorDerivative := 0`, so `ExactForm 0 X = ⊥` and this root collapses to `ω.2 = 0`, which is not yet true for the period-only forms the surrogate admits." Blueprint: `tex/sections/06-periods-and-riemann-bilinear.tex:762-768` (`lem:hodge-remainder-period-payload-exact`, GitHub #243, "A closed 1-form with zero harmonic projection is exact") + assembly at `:770-781`.

Note how cheap the rest of the Hodge story is made: `analyticHarmonicGenus X := finrank ℂ (HarmonicOneForm X)` with `HarmonicOneForm X := Fin 2 → HolomorphicOneForm ℂ X`, so `= 2g` is pure `Module.finrank_pi_fintype` (`HodgeStarRS.lean:45-57`, `:83-93`). The Hodge decomposition is built into the *definition* of the form type; this gap is the sole thing that would make the quotient match it.

**Reach.** One direct call site (`:198`), then `:213` → `:236` → `:248` → `:279` → `:296` → `:306`, then `HodgeDecomposition.lean:46-52` → `:76-84` → `:93-101` → `HodgeDeRhamRank.lean:36-45` → `PeriodFunctional.lean:275` → `thm:period-lattice` → `Solution.lean:91-92`. Shares its last five hops with gap 16. **Reaches the public Jacobian.**

**(b) rkirov's counterpart: none — he has no Hodge theory at all.** What he uses to reach `2g = rank H₁`:

- Čech: `cocycles1` / `coboundaries1` / `cechH1` / `h1Dim` (`Cech/CechComplex.lean:124`, `:130`, `:138`, `:156`), cochains as germ classes (`MGerm`, `:135-137`).
- Dolbeault: `OneFormsZeroOne := LinearMap.range proj01L` (`DolbeaultComparison/DolbeaultComparison.lean:108`), `DolbeaultH01 X := ↥(OneFormsZeroOne X) ⧸ dbarImageInZeroOne X` (`:143`) — literally a `∂̄`-cokernel; `dbarL` (`DolbeaultComparison/DolbeaultH01.lean:47`) built from `mfderiv_add` / `const_smul_mfderiv`, no PDE.
- Comparison: `comparison_linearEquiv : DolbeaultH01 X ≃ₗ[ℝ] cechH1 0` (`DolbeaultComparison/DolbeaultComparisonEquiv.lean:669-673`) with dimension form `finrank ℝ (DolbeaultH01 X) = 2 * finrank ℂ (cechH1 0)` (`:681-683`).
- `h¹(𝒪) = g`: `FiniteCover.h1Dim_zero_eq_genus` (`H1Genus/CechH1Genus.lean:119-120`), proved from Riemann–Roch twice plus a cup-product kill, closed by `omega`.
- Assembly: `finrank_dolbeaultH01 : finrank ℝ (DolbeaultH01 X) = 2 * genus X` (`Abel/AbelDbarKill.lean:212-217`).

**(c) Match verdict: N/A** — no counterpart is needed; his derivation never forms a de Rham group.

**(d) Portability: zero. The statement is false** (and its hypothesis is vacuous, since `exteriorDerivative = 0` makes `hclosed` hold by `rfl`): the conclusion unfolds to `ω.2 = 0` for every `ω`, i.e. `Hom_ℤ(H₁(X,ℤ), ℂ) = 0`, false for every genus ≥ 1 — and `IntegralOneCycle X` is the genuine `H₁` (`Periods/IntegralOneCycle.lean:31-34`, from Mathlib's `singularHomologyFunctor`). Replacing gaps 16+17 together with his route costs **~3,300 lines for the Dolbeault↔Čech comparison alone** (`DolbeaultComparisonProof` 1,468 + `DolbeaultComparisonInverse` 735 + `DolbeaultComparisonEquiv` 707 + `LocalRealization` 529 + `LerayCoverExists` 208 + `DolbeaultComparison` 180 + `GoodCover` 96 + `DolbeaultH01` 54), on top of a Čech germ-cochain substrate and the Riemann–Roch tower beneath it. Also note his `DolbeaultH01` is an **ℝ**-module and the comparison is `≃ₗ[ℝ]` with the factor 2 explicit — scalar bookkeeping we would inherit. **Realistic: 5,000+ lines, i.e. a route change, not a port.**

**(e) Plain-English impact.** Same node as gap 16 (`input:hodge-deRham`), narrated at `05:388-394` and `:398-417`. The lemma itself has no layman block. Note again the drift: the blueprint's English name — "A closed 1-form with zero harmonic projection is exact" (`06:764-765`) — is the true classical statement, while the Lean statement it labels is the false payload-vanishing claim.

**(f) Recommendation: RESTATE, then ADAPT at the node level.** (1) Retire, with the same discipline as gap 16. (2) Treat `input:hodge-deRham` as one node: over this substrate its two children are mutually contradictory, so any fix must address them jointly. (3) If `2g = rank H₁` is wanted at all, adopt his derivation (Čech → RR → `h¹(𝒪)=g` → Dolbeault comparison), which reaches the same arithmetic with no elliptic theory — a plan-level decision, not an Aristotle-sized job.

### Gap 18 — `exists_biholomorph_onePoint_of_genus_zero` (`Jacobian/HolomorphicForms/GenusZeroClassification.lean:912`)

**(a) Our planned route.** `ref/plan.md:559-574` (Phase 7.5) lists uniformization first. Blueprint `tex/sections/04-branched-covers-genus-zero.tex:897-924` (`thm:exists-biholomorph-one-point-of-genus-zero`, GitHub #232), with the route stated in the chapter `formalizationnote` (`:445-485`): "the forward direction is instead built from a self-contained *local analytic uniformization substrate*: (1) local chart-ball power series …; (2) open-mapping / inverse-function local charts …; (3) a normal-family (Montel / Arzelà–Ascoli) extraction selecting compatible normalized local coordinate patches; (4) gluing the patches through the two-chart ℂℙ¹ atlas." The statement takes a *topological* `X ≃ₜ OnePoint ℂ` and produces a complex-smooth one — i.e. uniqueness of the complex structure on S², and it serves the **backward** direction (`:2147` → `:2118` → `:2086` → `:2040` → `:503` + gap 18).

Two problems worth recording. First, the ~1,900-line "Montel" tower above it is a restatement, not progress: `GenusZeroNormalizedMontelPatchSelector` (`:852-874`) has fields `uniformization : X ≃ₜ OnePoint ℂ`, `uniformization_contMDiff`, `inverse_uniformization_contMDiff` — inhabiting it *is* the theorem — and the stack above (`:949`, `:997`, `:1016`, `:1041`) only adds bookkeeping. Second, `grep` for `Montel|ArzelaAscoli|equicontinuous|TendstoUniformly|extremal` over that file matches **only the string "Montel" inside structure and field names**: there is no equicontinuity, no Arzelà–Ascoli, no uniform convergence, no extremal problem. Classical Montel enters uniformization through an extremal problem over injective maps on a simply connected *plane domain*, not by gluing normalized patches on an abstract compact surface. **The stated route is unsound as written.**

**(b) rkirov's counterpart: none — he never proves this, because he never needs it.** His backward direction: S² ⟹ simply connected (`SphereTopology/VanKampen.lean`, 427 lines, proving `SimplyConnectedSpace S²` in-repo — Mathlib has only a `proof_wanted`; plus `simplyConnectedSpace_of_homeo`, `GenusSphereBackward.lean:92-94`) ⟹ global holomorphic primitives (`Monodromy/HolomorphicPrimitives.lean:241`) ⟹ Liouville via Mathlib's `MDifferentiable.exists_eq_const_of_compactSpace` (`GenusZeroOfSphere.lean:103-122`) ⟹ every form is 0 ⟹ `finrank = 0` (`:126-132`), assembled at `:143-152` and exposed as `genus_zero_of_nonempty_homeo_sphere` (`ProperDegree/DegreeOneSphere.lean:668-673`). **No complex-structure uniqueness, no biholomorphism, no uniformization.**

**(c) Match verdict: DIFF — and our route is strictly harder than necessary.** Gap 18 is a genuine classical theorem, but it is *not needed* for the backward implication.

**(d) Portability.** The statement cannot be ported (he has no such theorem); what ports is the *replacement of the backward direction*. Mismatches: `OnePoint ℂ` vs `Metric.sphere` is a non-issue — our backward direction already starts at `Nonempty (X ≃ₜ Metric.sphere …)` (`:2147-2152`) and our `onePointCx_homeomorph_sphere` is his `RiemannSphere.homeoSphere` (`ProjectiveLine.lean:315`); genus is definitionally aligned; his statements are at `ω` while our `HolomorphicForms` layer is at `⊤`, so a port is most comfortably restated at `ω` (which `Solution.lean` supplies anyway); he needs neither `[StableChartAt]` nor `[FiniteDimensionalHolomorphicOneForms]` (the backward direction needs no finite-dimensionality at all — `finrank = 0` follows from triviality). Infrastructure to bring over: the VanKampen closure (**19 files / 8,462 lines**) plus `Monodromy/` (**1,109**) plus ~1k of bridge adaptation onto our chart-coefficient layer (we already have `ContMDiffSection_localRepr_identityChart_contDiff`). **Estimate ~8,000–11,000 lines.**

**Status call: not false, not circular, but awkward and probably unreachable on the stated route.**

**(e) Plain-English impact.** Under the replacement, `lem:holomorphic-one-form-equiv-of-homeo-sphere` (`tex:624-630`) and `thm:homeo-sphere-holomorphic-one-form-vanishing` (`:644-650`) become provable without uniformization, and the narration improves: *"a sphere has no holes, so every holomorphic 1-form on it can be integrated to a global function; on a compact surface such a function must be constant, so the form was zero all along"* replaces *"every complex structure on the 2-sphere is the standard one."* The `sec:uniformization-lite` (`:621`) and `sec:uniformization-lite-iter3` (`:879`) subsections would be retired.

**(f) Recommendation: RESTATE + ADAPT.** Remove gap 18 from the reachable set; restate the backward direction as his (VanKampen + monodromy + Liouville). Both of his towers are sorry-free, self-contained, and independent of Riemann–Roch — the cleanest available port in either direction. Park gap 18 as a statement of independent interest if wanted.

### Gap 19 — `complexSimplePolePrincipalPart_of_biholomorph_onePoint` (`Jacobian/HolomorphicForms/MeromorphicToBranchedCover.lean:3010`)

**(a) Our planned route.** `tex/sections/04-branched-covers-genus-zero.tex:940-943` (`lem:complex-simple-pole-principal-part-of-biholomorph-one-point`, GitHub #234): pull the standard simple-pole coordinate on `OnePoint ℂ` back along the biholomorphism. The four obligations are listed in the proof comment (`:3006-3009`), matching the fields of `HasComplexSimplePolePrincipalPart` (`:940-949`): `meromorphic_everywhere`, `continuous_extension`, `orderAt_pole = 1`, `modulus_tendsto`.

**(b) rkirov's counterpart.** The field-by-field content exists but on the *opposite* side of the arrow — he goes function ⟹ map-to-sphere, not biholomorphism ⟹ function: `contMDiff_toSphere` (`ProperDegree/DegreeOneSphere.lean:327`), `toSphere_regular_at_pole` (`:386`), `toSphere_preimage_infty` (`:87`), `contMDiffAt_toSphere_at_pole` (`:183`), with `holoRepr` (`Meromorphic/MeromorphicLiouville.lean:65`) as the limit-repaired finite lift.

**(c) Match verdict: DIFF direction — and under the gap-20 port this becomes dead code.**

**(d) Portability.** This is the **least problematic of the three**: honest local computation, no hidden classification. It is provable directly from our own `OnePoint ℂ` chart API (`identityChart`/`inversionChart`, `identityChartCoeff_contDiff`, `lem:inversion-chart-coeff-continuous-at-zero` at `tex:686` — all `\leanok`), **estimate 150–300 lines**, no port needed. If his lemmas were used instead, the bridges are a `holoRepr`-vs-`onePointExtend` agreement lemma and a `mapAnalyticOrderAt`-vs-`orderAtPoint` chart-convention bridge (we already have `extChartAt_symm_eq_chartAt_symm`, used at `:2934`; for `modelWithCornersSelf ℂ ℂ` the two coincide). Not false, not circular — just unfinished. (It is, however, vacuous under the `StableChartAt` binder like the rest.)

**(e) Plain-English impact.** Low stakes: *"if you already know the surface is a sphere in disguise, then '1/z with the pole moved to P' is a perfectly good meromorphic function on it with exactly one simple pole."* Bookkeeping between two descriptions of the same object.

**(f) Recommendation: KEEP (prove locally) — or drop if gap 20 is ported.** If the forward direction is taken from rkirov, delete this together with `singlePoleAnalyticData_of_biholomorph_onePoint` (`:3022`) and `genusZero_singlePoleMeromorphicAnalyticData_nonempty` (`:3076`). Otherwise it is the only one of the three that is a genuinely Aristotle-sized job.

### Gap 20 — `exists_biholomorph_onePoint_of_analyticGenus_zero` (`Jacobian/HolomorphicForms/MeromorphicToBranchedCover.lean:3061`)

**(a) Our planned route.** `tex/sections/04-branched-covers-genus-zero.tex:928-933` (GitHub #233) claims this is a thin packaging of gap 18, via `\uses{thm:exists-biholomorph-one-point-of-genus-zero}`. **That edge is circular**: gap 18 requires a *topological* `X ≃ₜ OnePoint ℂ` as input, and the only producer of one from `analyticGenus ℂ X = 0` in our tree is `genus_zero_homeomorph_onePointCx` (`GenusZeroClassification.lean:2755-2765`), which depends on gap 20. Our own file says so, `MeromorphicToBranchedCover.lean:3068-3071`: "The proof deliberately routes through the explicit biholomorphic uniformization frontier and not through `genusZero_pointRRSection_outside_constants_exists` or its downstream fixed-pole RR-section chain, **which depends on this theorem**." So gap 20 is irreducibly the whole hard content of the forward direction, with no decomposition anywhere in the repo. (Relatedly, the eleven-step "RR-section" ladder above it, `:3085`–`:3299`, contains **no** Riemann–Roch; the names are vestigial.)

Plan context: `ref/plan.md:261-284` ("Architectural Shortcut", 2026-05-13) deprioritized general Riemann–Roch and Serre duality as `wontdo`, keeping only "a **genus-zero-restricted** Riemann-Roch leaf".

**(b) rkirov's counterpart.** `exists_singleSimplePole_of_genus_zero` (`GenusSphereHeadline.lean:26-30`) → `exists_singleSimplePole_of_genus_zero_of_rr` (`RiemannRoch.lean:73-162`, ~95 lines) → `exists_riemannRoch_divisor` (`RiemannRoch.lean:31-35`) → `exists_riemannRoch_divisor_unconditional` (`TailDuality/RiemannRochUnconditional.lean:63-70`); then `nonempty_homeo_sphere_of_singleSimplePole` (`ProperDegree/DegreeOneSphere.lean:629-642`). Route: Miranda Ch. VI Laurent-tail RR — RR-I on Mittag-Leffler tail spaces, tail Serre duality in the meromorphic pair frame `ω = h·dg₀`, `l(K) = g` from the Forster §17.4 canonical-form isomorphism. At `g = 0`: `deg(K−P) = −3 < 0` ⟹ `l(K−P) = 0` ⟹ `l(P) = 2` ⟹ a non-germ-constant element of `L(P)` ⟹ order exactly `−1` at `P`, `≥ 0` elsewhere. His headline `genus_eq_zero_iff_homeo` (`GenusSphereHeadline.lean:41-48`) is **statement-compatible with ours** (same `Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1`, same instance bundle).

**(c) Match verdict: DIFF — and ours is the route the blueprint itself says is unavailable, and it is self-blocking.**

**(d) Portability.** Not portable as stated, **but the node we actually need is one level down and is directly portable.** The first sorry-free node above the gaps is `genusZero_fixedPole_complexPrincipalPart_nonempty` (`MeromorphicToBranchedCover.lean:3221-3232`), `∃ F : X → ℂ, HasComplexSimplePolePrincipalPart F P`; everything from there up to the forward half of `genus_eq_zero_iff_homeo` is **already sorry-free** in our tree. We already have his Steps 2–4: `properDegreeOneMapOfSimplePole_nonempty` (`GenusZeroClassification.lean:2572-2590`) and `proper_degreeOne_meromorphicMap_biholomorphic` (`:2628-2642`). We are missing only **Step 1**: an honest single-simple-pole meromorphic function at a prescribed point.

Bridges: his `MeromorphicFunction := {toFun, meromorphic}` (`Meromorphic/Abel.lean:111-114`) is minimal where our `MeromorphicMapToSphere` (`HolomorphicForms/Meromorphic.lean:26-70`) is a 15-field bundle — port his lightweight type alongside rather than retrofitting ours (~30 lines for the `MeromorphicAtX`/`IsMeromorphic` chart-convention bridge, which we already have). Divisors are **identical**: `Divisor X := X →₀ ℤ` (`HolomorphicForms/Divisor.lean:19` vs `Meromorphic/Abel.lean:41`), `degree` both `Finsupp.degree`. But `linearSystem` / `lDim` / `germZeroSubmodule` are **absent** from our repo and must be ported (~400–600 lines). The RR supply chain itself is the expensive part: the incremental closure of `Jacobians.RiemannRoch` over `Jacobians.ProperDegree.DegreeOneSphere` is **50 files / 13,736 lines** (all of `LaurentTail/`, nearly all of `TailDuality/`, `ResidueTheorem/*`, `PlanarStokes/*`, `SerrePairing/SerreDuality`, `CanonicalForms/FormRemovableSingularity`, parts of `ProperDegree/` and `MeromorphicTrace/`).

**A decisive planning datum:** his RR is proved **unconditionally in every genus** (`TailDuality/RiemannRochUnconditional.lean:63-70`). There is no cheaper "genus-zero-only RR" to port — so `ref/plan.md:265-271`'s hoped-for genus-0-restricted RR leaf has **no counterpart in the complete repo**. That is the strongest available evidence that the Architectural Shortcut did not save work on `genus_eq_zero_iff_homeo`; it relocated the work into gap 20.

**(e) Plain-English impact.** Under the port the narrative becomes the classical one the blueprint *already tells* at `tex:434-442`: *"no holomorphic 1-forms means Riemann–Roch hands you a function with exactly one simple pole; that function wraps the surface once around the sphere; a once-around map is a homeomorphism."* The chapter opener's punch line (`:4-30`) and the classification layman (`:418-432`) survive verbatim. What disappears is the `formalizationnote` (`:445-485`) that currently has to explain why we *cannot* tell that story — and whose substitute is unsound.

**(f) Recommendation: ADAPT (restructure the target, then port selectively).**
1. Immediately: retarget the forward direction at `MeromorphicToBranchedCover.lean:3221` and mark gaps 19 and 20 for deletion; remove the circular `\uses` on `tex:929`.
2. Port his `Divisor`/`linearSystem`/`lDim`/`MeromorphicFunction` algebra (~400–600 lines) and `exists_singleSimplePole_of_genus_zero_of_rr` (~95 lines) **as consumers of an `exists_riemannRoch_divisor` hypothesis** — isolating RR the way he isolated `HasHolomorphicPrimitives` (`GenusZeroOfSphere.lean:91`). That reduces the forward direction to **one named, honestly-stated, non-circular obligation** for ~700 lines, replacing two unroutable sorries and ~1,900 lines of tautological selector scaffolding. This is strictly better bookkeeping even if RR is never closed.
3. Only then decide on the 13,736-line Laurent-tail / Serre-duality / Čech increment.

### Gap 21 — the `StableChartAt` instance (`Jacobian/Solution.lean:37`)

```lean
class StableChartAt : Prop where
  chartAt_eq_of_mem_source :
    ∀ p : M, ∀ q ∈ (chartAt H p).source, chartAt H q = chartAt H p
```
(`Jacobian/Periods/TrivializationContinuousLinearMapAt.lean:52-55`)

**(a) Our planned route.** The docstring (`:39-50`) asserts "This holds for every concrete manifold one cares about (the model space, products, open submanifolds, Riemann surfaces with explicit finite atlases, etc.) — it is the 'natural' chart-selection property", and `:152-173` proposes upstreaming it to Mathlib with instances for products, open submanifolds, "`Sphere`, `Icc`". Blueprint: `tex/statements/challenge-statement.tex:103-111` (`lem:stable-chart-at-instance`, GitHub #237) — "It currently stands as an open obligation (`sorry`) in `Jacobian/Solution.lean`; the honest route replaces it with genuine chart-overlap-derivative continuity." Only one instance exists: `StableChartAt H H` (`:58-61`, by `rfl`).

**(b) rkirov's counterpart: none.** Zero occurrences of `StableChartAt` in 72,403 lines. His `chartAt _ = chartAt _` facts are all either Mathlib's `Opens.chartAt_eq` (subtype restriction of the *same* chart) or consequences of the *points* being equal. What he uses instead:

| need | his solution | file:line |
|---|---|---|
| path velocity without a global frame | `pathSpeed γ t := fderiv ℝ ((chartAt ℂ (γ t)).toFun ∘ γ) t 1` — chart at the **moving point** | `Path/LineIntegral.lean:41-43` |
| no chart-independence lemma | documented decision: "Chart-independence of the line integral … is not formalized; every development downstream uses this one fixed chart-based definition, so no compatibility lemma is needed." | `Path/LineIntegral.lean:25-28` |
| continuity of the form coefficient | `continuousAt_inCoordinates` via `contMDiffAt_hom_bundle` | `Path/CotangentCoeff.lean:42-49` |
| coefficient as a number | `continuousAt_localCoeff` (reads `inCoordinates (α x) 1`, explicitly **not** `α x 1`) | `Path/CotangentCoeff.lean:55-60` |
| intrinsic ↔ fixed-frame bridge | `apply_eq_inCoordinates` (`Trivialization.symmL_continuousLinearMapAt`) | `Path/CotangentCoeff.lean:68-81` |
| integrand continuity on `[0,1]` | `continuousOn_form_pathSpeed`, driven by `(hγ s₀ hs₀).eventually ((chartAt ℂ x₀).open_source.mem_nhds hx₀src)` — the **eventually-in-source** filter argument that replaces chart stability | `Path/CotangentCoeff.lean:95-140` (filter step `:111-112`) |
| frame-indexed `(0,1)`-form reads | `read01` + a **transformation law** `read01_transform` (`read_y = conj(T′)·read_{y′}`) rather than an assumption that frames agree | `Abel/AbelFormRead.lean:17-26` |

And he names the trap, `Path/CotangentCoeff.lean:12-19`: the naive global coefficient "is **discontinuous** in general … continuous iff the tangent bundle is trivialized by the atlas, i.e. parallelizable — false for genus ≥ 2", dated at `:30` ("Found 2026-05-30; corrects the earlier false 'global coefficient' target"). Total for his chart-handling layer: `CotangentCoeff` 700 + `LineIntegral` 527 + `SmoothPathCore` 970 + `OfCurveAnalyticitySkeleton` 1,360 + `ChartedSpaceOfLocalHomeomorph` 57 = **3,614 lines, zero chart-stability assumptions**.

**(c) Match verdict: N/A — and he independently identified our assumption as the specific false step.**

**(d) Portability: the statement is not merely unprovable, it is *inconsistent* with the surrounding binders.** Proof, from the Mathlib `ChartedSpace` axioms alone:

- `p ∈ (chartAt H p).source` (`ChartedSpace.mem_chart_source`); write `S_p := (chartAt H p).source`, open by `open_source`.
- If `q ∈ S_p` then `chartAt q = chartAt p`, hence `S_q = S_p`. So for any `p, p'`, either `S_p = S_{p'}` or `S_p ∩ S_{p'} = ∅`.
- So `{S_p}` is a partition of `X` into nonempty open sets, i.e. each is clopen. With `[ConnectedSpace X]` (which also gives `Nonempty X`), `S_p = X` for every `p`.
- Hence `chartAt ℂ p` is a homeomorphism from `X` onto `(chartAt ℂ p).target`, an **open** subset of `ℂ`.
- With `[CompactSpace X]`: that target is a nonempty compact *open* subset of `ℂ`, hence clopen, hence `= ℂ` by connectedness of `ℂ`. But `ℂ` is not compact. **Contradiction.**

Independently refuted by a concrete Mathlib instance, contradicting our own upstreaming plan: `Mathlib/Geometry/Manifold/Instances/Sphere.lean:356` sets `chartAt v := stereographic' n (-v)` with `(stereographic' n v).source = {v}ᶜ` (`:344-345`); for `w ∉ {v, -v}` we get `w ∈ (chartAt v).source` but `chartAt w ≠ chartAt v`. **The sphere — the very space in `genus_eq_zero_iff_homeo` — violates `StableChartAt`**, so the plan item at `TrivializationContinuousLinearMapAt.lean:162` ("Specific instances for `Sphere`, `Icc`") is unachievable, and the class is not upstreamable.

Consequences: (i) the instance can never be closed; (ii) every theorem whose binders contain `[StableChartAt ℂ X]` together with `[CompactSpace X] [ConnectedSpace X]` is **vacuously true** — that is 11 of the 20 engine sorries plus everything already "proved" in those layers; (iii) because `Solution.lean:35-37` supplies the instance by `sorry`, the public theorems type-check with proofs routing through `sorryAx` for a *false* lemma — strictly worse than an honest open obligation.

**Blast radius.** 120 files mention `StableChartAt`: 30 `Periods`, 27 `HolomorphicForms`, 22 `AbelJacobi`, 21 `AnalyticJacobian`, 17 `TraceDegree`, 2 `Blueprint`, 1 `Solution.lean`. But **actual content consumption is only 10 sites in 5 files**:

| file:line | purpose |
|---|---|
| `HolomorphicForms/TraceSpec.lean:1091, 1093` | rewrite `chartLocalAt f x = chartLocalAt f x₀` |
| `HolomorphicForms/TraceSpec.lean:3613` | identify `chartAt ℂ y = chart` in a regular-value argument |
| `HolomorphicForms/TraceSpec.lean:4073` | collapse `symmL (trivializationAt …)` to `1` |
| `HolomorphicForms/CompactRiemannSurface.lean:736` | collapse `symmL` to `id` in an `inCoordinates` computation |
| `HolomorphicForms/CompactRiemannSurface.lean:885` | `chartAt_symm_chartAt_eq_of_mem_ball` |
| `HolomorphicForms/EvalAtOneHelper.lean:38` | `contMDiff_tangentSection_one` — smoothness of the constant-`1` tangent section |
| `TraceDegree/TraceDefinition.lean:649, 661` | identify charts along a local inverse branch |

So the class is a **binder virus** propagated through 120 files, with mathematics touching it at only ten places, of two kinds: (i) "the chart is literally the same at a nearby point" (6 sites), (ii) "therefore `coordChange`/`symmL` is the identity" (4 sites). Kind (ii) is exactly the parallelizability error he diagnosed; `EvalAtOneHelper.contMDiff_tangentSection_one` is the most dangerous, being *false* in general rather than merely unproven.

**Refactor size.** Strip the binder from ~120 files (mechanical, ~150–250 edited lines); delete the class and its five lemmas (−177) and the `Solution.lean` instance (−3); rebuild the 4 kind-(ii) sites the `inCoordinates` way (**+300–600** new Lean; the model, `Path/CotangentCoeff.lean`, is 700 lines for exactly this job); rebuild the 6 kind-(i) sites with explicit shared charts (**+150–350**). **Total: ~125 files touched, ~500–1,000 lines of genuinely new Lean, ~400 deleted.**

**(e) Plain-English impact.** `lem:stable-chart-at-instance` (`tex/statements/challenge-statement.tex:103-111`) is the only prose node, and its honest route ("genuine chart-overlap-derivative continuity") is right in spirit — but the node should say the class is *refutable*, not merely open. Indirectly it invalidates every `\leanok` downstream of `Solution.lean:37`, i.e. the whole Abel chain (`tex/sections/08-abel-jacobi-map.tex:60-66`, `:91-96`, `:118-123`, `:238-252`, `:292-300`, `:333-343`, `:447-452`, `:503-510` and their laymans) and the trace/degree section — those marks currently certify statements about an empty class of types. No layman *prose* is wrong; what is wrong is the claim that it is formalized.

**(f) Recommendation: RESTATE — delete the class, rebuild the 10 sites his way.** Withdraw the Mathlib-upstreaming plan at `:152-173`. **This is the single highest-value item in the whole comparison:** it is bounded, mostly mechanical, and until it is done no statement in the `Periods` / `AbelJacobi` / `HolomorphicForms` layers means what it appears to mean.

### Gaps 5–13 — the polygonal-model / combinatorial-surface tower

Treated as one block, because they stand or fall together.

| file | lines |
|---|---|
| `Jacobian/Periods/Hurewicz.lean` | **7,663** |
| `Jacobian/Periods/HandleSwapHomeo.lean` | 350 |
| `Jacobian/Periods/TietzeReduction.lean` | 307 |
| `Jacobian/Periods/DualGraphCut.lean` | 187 |
| four gap-bearing files | **8,507** |

plus the rest of the subsystem in the same directory: `EdgeWord.lean`, `SurfaceClassification.lean`, `SurfaceClassificationData.lean`, `Polygon4g.lean`, `Polygon4gCellular.lean`, `RadoTriangulation.lean`, `CellularChainComplex.lean`, `CellularHomologyRS.lean`.

**(a) Our planned route.** `ref/plan.md:310-313`: "**Periods — polygonal-model homology — `Periods/{Hurewicz (3), DualGraphCut, HandleSwapHomeo, TietzeReduction (2)}`.** The Polygon_4g H₁ basis, dual-graph-cut-to-disk, and Brahana normal-form reduction. **This is the current heavy edge.**" Blueprint: `tex/sections/05-polygonal-model.tex`, labels `lem:cut-along-non-tree-yields-unfolded-disk` (`:450-457`, #226), `lem:polygon4g-quotient-path-finite-lift-subdivision` (`:473-480`, #228), `lem:polygon4g-partial-side-arc-homologous-to-edge-chain` (`:515-522`, #229), `lem:edge-chain-sum-singular-boundary-scalar-coefficient-zero` (`:543-551`, #230), `lem:handleprefix-tailrotate-homeomorph` (`:553-560`, #239). The four `TietzeReduction.lean` sorries (gaps 5–8) have **no blueprint label at all** — they are blueprint-invisible.

**(b) rkirov's counterpart: none, by deliberate retirement, with the decision documented and costed.**

- `docs/walls_bc_plan_2026-06-10.md:254-258`: "**B-I (build `exists_cutSurface`).** Radó-style triangulation …, classification of surfaces to the 4g-gon normal form … No Mathlib support, no Lean precedent for the classification … **Estimate ≥ 10k LoC, VERY HIGH risk, months. Rejected.**"
- `:146-151`: "`CutSurface` should be **retired, not constructed**. Its sole consumer is `exists_periodLattice_realBasis`; Forster 21.4 proves that statement (same signature, via Mathlib's ZLattice API) with no dissection, no R1/R2, no boundary words."
- `:112-115`: "**Note the dependency reversal: Forster's lattice theorem (Wall B) CONSUMES Abel's sufficiency (Wall C's engine), not vice versa.** (21.5 Remark, p. 170: the symplectic basis is a *consequence*, not an input.)"
- `:358-360`: "The Riemann bilinear relations are NOT proven by the new route and are NOT needed by the challenge."
- `docs/RETRO.md:25-27`: "**Retiring work instead of doing it.** The 4g-gon cut surface — long expected to be the worst wall … was never built: a books pass showed its lone consumer provable dissection-free (Forster 21.4)."

His replacement is `Jacobians/PeriodLattice/` (2,713 lines): `JacobiBasePoints.lean` 199 (Forster 21.3), `JacobiLocalMap.lean` 225 (21.4(a), IFT), `PeriodLatticeDiscrete.lean` 554 (21.4(b), via the Abel engine + residue theorem — `truePeriodLattice_isolated_zero` at `:115` with a 440-line proof), `PeriodLatticeNondegenerate.lean` 294 (21.4(c), maximum principle), `PeriodLatticeBasis.lean` **81** (assembly), `OfCurveAnalyticitySkeleton.lean` 1,360 (chart primitives). The crucial point: **the rank `2g` is linear algebra, not topology** — `PeriodLatticeBasis.lean:71-72`:

```lean
have hrank : Module.finrank ℤ (truePeriodLattice X) = 2 * genus X := by
  rw [ZLattice.rank ℝ, finrank_real_of_complex, Module.finrank_pi, Fintype.card_fin]
```

The index set `Fin (2 * genus X)` is *manufactured* by `Fintype.equivFinOfCardEq` + `Basis.reindex` + `Basis.ofZLatticeBasis` (`:73-79`), never found as a cycle basis. Grep over `Jacobians/PeriodLattice/` for `H₁|homology|SingularHomology|triangul|Tietze|Hurewicz|polygon|4g-gon|CutSurface`: **0 hits each**.

(For completeness: `Jacobians/SphereTopology/VanKampen.lean` (427 lines) is *not* reusable here — it is the abstract two-open van Kampen corollary for simple connectivity only, with no amalgamated free product, no group presentation, no CW gluing; grep for `genus|surface|polygon|CW|4g` on that file returns nothing. Its only consumer is the genus-0 ⟺ sphere statement.)

**(c) Match verdict: N/A for all nine — and worse, the tower appears not to be load-bearing for us either.**

A declaration-level dependency graph over all of `Jacobian/**/*.lean` (comments and docstrings stripped, projection notation resolved), with reachability run from every public declaration of `Solution.lean` (696 reachable decls), finds:

- **All nine gaps: NOT reachable.**
- Reachable decls per file: `TietzeReduction.lean` **0**, `DualGraphCut.lean` **0**, `HandleSwapHomeo.lean` **0**, `SurfaceClassification.lean` **0**, `SurfaceClassificationData.lean` **0**, `Polygon4gCellular.lean` **0**, `RadoTriangulation.lean` **0**. `Hurewicz.lean` **13**, and those thirteen are only the sorry-free data structures `Polygon4gCellularSingular*Data` (`:63`, `:81`, `:99`, `:124`, `:161`, `:190`), `Polygon4gSingularC1` (`:266`) and `singularChainComplexZ` (`:363`), consumed by `CellularChainComplex.lean` — not by the nine sorries.
- Also **out**: `h1_free_of_compact_surface` (`PeriodFunctional.lean:238`), `analyticGenus_eq_topologicalGenus` (`:293`), `h1_basis_of_compact_riemann_surface` (`:310`), `existsHomeoToPolygon4g` (`SurfaceClassification.lean:220`), `polygon4g_singularH1_basis` (`Polygon4gCellular.lean:117`), `periodFullComplexLattice` (`PeriodLattice.lean:270`).

The route `Solution.lean` actually takes is the universe-`u` one, and it **short-circuits the tower with its own standalone sorries**: `stageA_surface_CW_basisU` (`H1BasisU.lean:73`) is a *bare* `sorry` that calls nothing. Its own docstring admits the duplication (`H1BasisU.lean:7-13`: the Type-0 proof "runs the full surface-classification chain") and explains why it was not reused (`:27-33`): "`IntegralOneCycleU X` is built from the singular-homology functor instantiated at universe `u` with `ULift.{u} ℤ` coefficients — a genuinely *different* object from the Type-0 `IntegralOneCycle X` … with no cheap isomorphism bridge." **So the tower was built to serve a Type-0 `h1_basis_of_compact_riemann_surface` that the public API abandoned when it went universe-polymorphic. It is now a dead parallel route.**

Why our ledger disagrees: `sorries.jsonl` marks all nine `"r":1`, but `scripts/list-sorries.py:134-154` computes `r` by scraping `lake build Jacobian.Solution` warnings — that is *import-closure* reachability (all four files are in Solution's import closure), not logical dependency. Corroboration that the flag is build-log noise: `Polygon4gCellular.lean:polygon4g_succ_hurewicz_iso_freeZ` is marked `"r":0` (`sorries.jsonl:3`) despite sitting in the same tower and the same import closure. **Caveat: no `lake build` was run for this report, so this is static analysis, not an `#print axioms` confirmation — though four whole files at zero reachable decls is a very wide margin. Confirm with `#print axioms` before acting.**

**(d) Portability: nothing to port. But four of the nine are provably false, which matters regardless of the retirement decision.**

The lever for gaps 6 and 9 is that `TietzeStep` has exactly three constructors — `cancel` (length −2), `swap` (length-preserving block exchange), `rotate` (length-preserving) (`EdgeWord.lean:292`, `:320`, `:329`) — so **`TietzeEq w v` implies `v.length ≤ w.length` and `v` uses no letter absent from `w`.**

- **Gap 5 is FALSE.** `Orientable` carries no information: `class Orientable (M) : Prop where existsConsistentChartChoice : Nonempty Unit := ⟨()⟩` (`Periods/Orientable.lean:14-16`) — every space is `Orientable`. And `EdgeWordPresentation` (`SurfaceClassificationData.lean:73`+) requires only a continuous surjective `proj : DiskC → M` with `kernel : proj z = proj w ↔ sidePairingRel g word z w`. Take `g = 1`, `word = [Letter.a 0]`, `M := EdgeWord.wordQuotient 1 [Letter.a 0]`, `proj := Quotient.mk`: all fields hold (`kernel` by `Quotient.eq`), `Orientable M` is free, `hw := WordEq.refl`. Then `Letter.a 0 ∈ w` but `Letter.aInv 0 ∉ w`. No manifold/compactness/connectedness hypothesis is present to exclude this.
- **Gap 6 is FALSE.** `g = 2`, `w := handleBlock (0 : Fin 2) ++ handleBlock (0 : Fin 2)` = `[a₀,b₀,a₀⁻¹,b₀⁻¹,a₀,b₀,a₀⁻¹,b₀⁻¹]`, length 8. Both hypotheses hold (every letter's inverse is present; `InverseCancel` matches only *adjacent* inverse pairs, and none of the adjacent pairs here is one). But any admissible `v` has `{perm 0, perm 1} = {0,1}`, so `Letter.a 1 ∈ v` — and `w` contains no `Letter.a 1`, which no `TietzeStep` can introduce. (Second, independent counterexample: `g = 2`, `w := handleBlock (0 : Fin 2)`, length 4, while every candidate `v` has length 8 > 4.)
- **Gap 8 is FALSE.** `InverseCancel.ax_aInv (0 : Fin 1) [] []` gives `w = [Letter.a 0, Letter.aInv 0]`, `v = []`. For `v = []`, `Fin 0` is empty so `SideGen 1 []` has no constructors, `sidePairingRel = Eq`, and `wordQuotient 1 [] ≃ₜ DiskC` — the **closed disk**. For `w` of length 2 the two boundary arcs are glued with reversal, giving **S²**. A closed disk is not homeomorphic to a 2-sphere. The classical treatment makes `aa⁻¹` the sphere *base case* rather than cancelling it; the statement needs `v ≠ []` (equivalently `2 < w.length`). Note the in-body comment already warns of the pattern (`TietzeReduction.lean:169-171`: "This replaces the false disk-lift `inverseCancel_geometric_maps`").
- **Gap 9 is FALSE**, by the same structural error the file already records. `g = 1`, `i = 0`, `u = [a₀, b₀]`, `m = 1`: `w₁ = [a,b,a⁻¹,b⁻¹,a,b]`, `w₂ = [a,b,a⁻¹,b⁻¹,b,a]`, both length 6. `SideGen` relates arc `i` to arc `j` iff `(w.get i).inv = w.get j`, so the arc classes are `{0,2,4}`/`{1,3,5}` for `w₁` and `{0,2,5}`/`{1,3,4}` for `w₂`. A self-homeomorphism of the closed disk maps `∂DiskC` onto `∂DiskC` and must carry the unique size-6 vertex class onto itself, hence permutes the six arcs by an element of the dihedral group on ℤ/6 — and for any such `σ`, `σ({0,2,4}) ∈ {{0,2,4},{1,3,5}}` (rotations give `{k,k+2,k+4}`, reflections `{c,c+2,c+4}` — always the even or odd coset). Neither equals `{0,2,5}` or `{1,3,4}`. The *quotients* may be homeomorphic; a relation-conjugating self-homeomorphism of the disk does not exist.
- **Gap 7 is true and cheap** — the only one of the nine in that category. Both sides have length `4g` and the same block multiset; `HandleSwap.move` with `xs = B₁`, `h = B₂`, `ys = []` gives adjacent block transpositions, which generate `Equiv.Perm (Fin g)`. ~40 lines by induction on `Equiv.Perm` via adjacent transpositions. Pure list combinatorics — no topology, no `Orientable`, no `DiskC`.
- **Gap 10** has `PUnit`-vacuous hypotheses (`Triangulation := PUnit`, `SurfaceClassificationData.lean:62-63`; `DualGraph`/`DualSpanningTree := PUnit`, `DualGraphCut.lean:19-25`), so as stated it is the entire existence half of the surface-classification theorem with zero inputs. It is also likely false without `[Orientable M]`: `SideGen` can only express orientation-reversing arc pairings (`EdgeWord.lean:97-103`), yet ℝP² satisfies every stated hypothesis including the `PUnit` triangulation. The other eleven theorems in that file are `Nonempty Unit := ⟨()⟩` placeholders (`:38`, `:43`, `:61`, `:72`, `:80`, `:87`, `:114`, `:123`, `:145`).
- **Gaps 11, 12, 13 are true but hard**, and 13 is the most self-contained — it is the one to keep if a `Polygon4g` H₁ computation is ever wanted for its own sake. Its docstring (`Hurewicz.lean:5804-5816`) is a model of honesty: it explains that it "replaces the previously circular substrate axiom `signedFaceTargetEdgeCoefficient_zero_of_singular_boundary`: `d ∘ d = 0` only proves the signed face one-chain is a cycle, not that a particular edge coefficient in that cycle is zero."

**What retiring the tower costs and saves.** Saves: `TietzeReduction.lean` 307 + `HandleSwapHomeo.lean` 350 + `DualGraphCut.lean` 187 + `SurfaceClassification*.lean` + `RadoTriangulation.lean` + `Polygon4gCellular.lean` + ~95% of `Hurewicz.lean` (7,663), retaining the 13 reachable `Hurewicz.lean` decls and `EdgeWord.lean`'s sorry-free data layer. Costs: **nothing on the critical path.** The frontier stays exactly where it already is — `H1BasisU.lean:73`, `H1BasisU.lean:89`, `PeriodVectorsLIU.lean:69` (gaps 3, 4, 15) — three bare sorries that currently invoke nothing. And those are precisely where rkirov's Forster-21.4 route lands, needing no ℤ-basis of H₁ at all: **~1,150 lines of new analysis replacing ~8,500 lines of combinatorial topology that contains four false statements.**

**(e) Plain-English impact.** Orphaned, and ideal "alternative classical route" appendix material: `tex/sections/05-polygonal-model.tex` subsections "Classical inputs for surface classification" (`:200-240`, including the Radó layman at `:204-218` — "Without Radó's theorem the entire Stage-A machinery has no input … the project carries a thin `rado_triangulation` stub naming the classical result") and "The polygonal model theorem (Stage A)" (`:242-274`); labels `lem:cut-along-non-tree-yields-unfolded-disk`, `lem:polygon4g-quotient-path-finite-lift-subdivision`, `lem:polygon4g-singular-simplex-subdivision-lifts-to-disk`, `lem:polygon4g-partial-side-arc-homologous-to-edge-chain`, `lem:edge-chain-sum-singular-boundary-scalar-coefficient-zero`, `lem:handleprefix-tailrotate-homeomorph`; and the three `\leanok` substrate lemmas at `:459-471`, `:494-513`, `:524-541`, which become stranded (true, proved, and pointing nowhere). Retained and unaffected: `def:topological-genus` (`:313`), `def:smooth-real-structure` (`:285`), `lem:polygon4g-eq-standard-word-quotient` (`:162`, `\leanok`), and the "Analysis on the polygon" subsection (`:594`+).

**A prose inconsistency to fix either way.** `05-polygonal-model.tex` already tells both stories about the genus bridge. The layman block at `:562-575` says "The proof factors through the polygonal model: the homeomorphism `X ≅ Polygon4g(g)` lets us compute `H₁(X)` on the combinatorially explicit polygon." The `proofsketch` eleven lines later (`:577-592`) says the opposite about the actual Lean: "Apply Hodge / de Rham to compute `rank_ℤ H₁(X,ℤ) = 2 g_an(X)`, then divide by two … delegating to two named sub-obligations." **The Lean matches the proofsketch** — `analyticGenus_eq_topologicalGenus` never touches the polygon. Same pattern in §06: the Riemann-bilinear laymans (`:370-404`) narrate Stokes on the 4g-gon, while the proofsketch (`:417-438`) admits the Lean target runs on "the project-internal stand-in `stokesPolygonFold`", and `thm:period-lattice`'s `\uses` list (`:817`) names no polygon label at all. **The blueprint's own dependency graph already agrees with the code analysis: the polygon tower is an alternative classical route, not the one this Jacobian is built on.**

**(f) Recommendation.** **RETIRE the tower**, after confirming non-reachability with `#print axioms` on the `Solution.lean` decls. Exceptions: **KEEP gap 7** (true, ~40 lines, self-contained) and optionally keep gap 13 with its tower if a standalone `H₁(Polygon_4g)` computation is wanted as an independent contribution. Before retiring, **record the four falsity counterexamples in the files** so the statements are never handed to a prover: gaps 5, 6, 8, 9 would burn budget on unprovable goals. Preserve the §05 prose as an appendix on the classical route, with a note that the project took Forster's dissection-free route instead.

### Gap 22 — `ContMDiff.degree`'s `else 0` fallback (`Jacobian/Solution.lean:223-235`)

**This one turned out well: it is not the hack the gap list feared.**

**(a) Our planned route.** `ref/plan.md:500-536` (Phase 6): "constant maps have degree `0`; **nonconstant maps have positive finite degree**; degree is computed by generic fiber cardinality with ramification multiplicity", with "functoriality of degree under composition" among the needed API, and "The trace-of-forms route is preferred because it makes the final identity structural." `ref/plan.md:538-557` (Phase 7): "The final identity is a serious classical compatibility theorem, **not a formal consequence of the map definitions alone**."

Blueprint: `tex/sections/09-degree-trace-push-pull.tex` has five labels — `sec:degree-trace` (`:2`), `lem:pullback-forms` (`:60`, `\leanok`), `lem:trace-forms` (`:95`, `\leanok`), `lem:push-pull-descend` (`:153`, `\leanok`), `thm:trace-pullback` (`:215`, `\leanok`) — and **no `\begin{definition}`**. The degree definition is bare prose at `:55-57`: "If `f` is constant, define `deg(f) = 0`. Otherwise `f` is a finite branched covering, and `deg(f)` is the cardinality of a generic fiber counted with multiplicity." The *labelled* definition is elsewhere and says something different: `tex/statements/challenge-statement.tex:194-212` (`def:degree-trace`) says "otherwise **the topological degree** of the associated branched covering". Two unreconciled definitions in two files, with nothing proving them equal.

The three named decls: `BranchedCoverData` (`HolomorphicForms/BranchedCover.lean:56-83`; six fields, the nontrivial one being `fiberSum_const`, the weighted fibre sum being constant on `Y`, `:68-72`); `RamificationIndexCompatible` (`:91-95`, `∀ x, IsHolomorphicAt f x → h.ramificationIndex x = mapAnalyticOrderAt f x`, deliberately a predicate — `:87-89`); `branchedDegree` (`:163-166`, `h.weightedFiberCard (Classical.arbitrary Y)`, with base-point independence `branchedDegree_eq_weightedFiberCard` at `:173-178` as an unconditional corollary of `fiberSum_const`).

**Is witness existence proved?** *Not as a named lemma — but the witness is unconditionally constructible, through a sorry-free chain, in exactly the instance context where `ContMDiff.degree` is declared.* The constructor is `Blueprint.branchedCoverData_of_nonconstant_holomorphic` (`Jacobian/Blueprint/Sec02/BranchedDegreeFromHolomorphic.lean:61-91`), with compatibility companion at `:97-107` (proved by `rfl`, since `ramificationIndex := mapAnalyticOrderAt f` definitionally). Its two extra hypotheses are discharged unconditionally from `ContMDiff`: `isHolomorphic_of_contMDiff` (`HolomorphicForms/HolomorphicMap.lean:1138-1143`), `hasLocalKfoldRamification_of_contMDiff` (`:1151-1156`, via a real chart-local proof at `:1061-1073`), `hasWeightedFiberConservation_of_contMDiff` (`:1340-1345`, via ~155 lines of genuine proof at `:1178-1334`). `ConnectedSpace → PreconnectedSpace`, so every hypothesis is in scope at `Solution.lean:104-105`/`:141`. **So the `else 0` branch is provably unreachable in context; it is simply not *named* as such.** The 3-line fix is already written elsewhere in our own tree — `TraceDegree/TracePullbackProviderU.lean:105-111` builds exactly this term inside the push-pull proof.

**Is `branchedDegree` choice-independent?** **Yes, proved**: `branchedDegree_eq_of_compatibleU` (`TraceDegree/AnalyticDegreeU.lean:94-110`), with the Type-0 twin at `AnalyticDegree.lean:90`; consumed by `analyticDegree_eq_canonical_branchedDegreeU` (`AnalyticDegreeU.lean:116-129`). (Relatedly, the trace value is also `hbc`-independent: `TraceSpec.lean:4229-4241`.)

**What is genuinely missing.** (i) A named existence lemma. (ii) `degree_pos` — it does not exist; the only candidate, `branchedDegree_pos` (`BranchedCover.lean:197-208`), *takes* `Function.Surjective f` as a hypothesis, and there is no "nonconstant holomorphic on a compact surface ⇒ surjective" lemma anywhere in our tree. So `ref/plan.md:506`'s "nonconstant maps have positive finite degree" is unfulfilled. (iii) No `degree_comp` / functoriality of degree (`plan.md:510`).

Sorry census for this layer: `HolomorphicMap.lean`, `BranchedCover.lean`, all of `Blueprint/Sec02/*.lean` and **all of `TraceDegree/*.lean` contain zero `sorry` tokens and zero `axiom` declarations.** `ref/axiom-audit.md:165-169` independently records `ContMDiff.degree` as "sorry-free and axiom-clean … the only public top-level decl currently free of `sorryAx`". `analyticPushforward_analyticPullbackU` (`TraceDegree/AnalyticPushPullU.lean:133-153`) has no local sorry either, and its chain is genuine: `traceFormsBundledLM_pullbackFormsBundledLM_eq_degree_smul_genuineU` (`TracePullbackProviderU.lean:125-134`) ← `trace_pullback_providerU` (`:80-117`, a real branched-cover/regular-locus identity-principle argument) ← matrix level (`AnalyticPushPullU.lean:82`) ← vector level (`:103`) ← quotient descent (`:133`).

**(b) rkirov's counterpart.** `ContMDiff.degree := Jacobians.degreeFiber f hf` (`Jacobians.lean:443-444`), the real definition at `MappingDegree/Degree.lean:225-236`, same `if constant then 0 else if ∃ witness then … else 0` shape. The differences:

| | this project | rkirov |
|---|---|---|
| witness | `BranchedCoverData` + `RamificationIndexCompatible` (6 fields + a predicate) | `RegularValueWitnessReg` (`MappingDegree/Degree.lean:151-161`; 2 fields + `is_regular`: chart-pullback `deriv ≠ 0` at every preimage) |
| named unconditional existence | **absent** (constructible — above) | **`regularValueWitnessReg_nonempty_of_nonConstantMap`** (`ProperDegree/Degree.lean:37-46` → `MappingDegree/RegularValueExistsRegUnconditional.lean:319-369`) |
| choice-independence | `branchedDegree_eq_of_compatibleU` | `degreeFiber_eq_card_of_regularWitness` (`ProperDegree/Degree.lean:51-59` → `MappingDegree/DegreeWellDefined.lean:33-61`, Hurwitz patching) |
| `degree_pos` | **absent** | `ContMDiff.degree_pos` (`Jacobians.lean:449-461`) via `surjective_of_nonconstant` (`JacobianConstruction/PeriodLattice.lean:452`) |

His push-pull chain (`Jacobians.lean:463-631`) is also worth reading as a comparison: keystone on one period vector (`:481-496`), the join `exists_preimageCycle_sheets_eq_degree` (`:514-541`), ℤ-linear extension to the lattice (`:560-572`, `Submodule.span_induction`), off-lattice extension via `exists_periodLattice_realBasis` (`:588-618`). Notably **he never builds a trace-of-forms map on the push-pull path** — `ambientPhi` (`Forms/HolomorphicForms.lean:263-268`) is the *transpose* of the pullback matrix, and the degree factor comes from orbit counting on monodromy lifts (`MeromorphicTrace/TracePullback.lean:2464-2501`). That is `plan.md:556`'s "equivalent statement on homology/period pairings" alternative, not our preferred trace route. Our trace route is the more faithful one to the classical statement.

**(c) Match verdict: DIFF — weighted-at-any-fibre vs unweighted-at-regular-fibre — but structurally parallel, and both match our blueprint prose.** Our `weightedFiberCard` is literally "cardinality of a generic fibre counted with multiplicity" (`09:55-57`); his is the same thing at a regular fibre, where all weights are 1. Our own `branchedDegree_eq_card_toFinset_of_unramified_fiber` (`BranchedCover.lean:216-230`) is exactly the bridge between the two formulations.

**(d) Portability: possible but the wrong trade.** Swapping in `RegularValueWitnessReg` means editing the `degree` *body*, which breaks `degree_eq_analyticDegreeU` (`Solution.lean:249-253`), `analyticDegree_eq_canonical_branchedDegreeU`, and the whole `TracePullbackProviderU → AnalyticPushPullU` chain that currently proves `pushforward_pullback`. Keeping `branchedDegree` and bridging instead needs `branchedDegree hbc = w.card`, i.e. "at a regular value all ramification indices are 1" plus fibre-set agreement — ~40–80 lines, but requiring `mapAnalyticOrderAt f x = 1 ↔ deriv (chart-pullback) ≠ 0`, a bridge that exists on neither side. The dependency weight is ~9.5k lines (`MappingDegree/` 48 files / 8,587 + `LocalMultiplicity/` 4 / 794 + `Surface/ContMDiffOmegaAnalytic.lean` 103 + `ProperDegree/Degree.lean` 61) with its own Mathlib import surface, across a minor Mathlib bump. Universes are *not* a problem (his `degreeFiber` is `{X : Type u} {Y : Type v}`). **Against that: the actual fix is 5–10 lines of our own code.**

**(e) Plain-English impact.** All five §09 layman blocks **survive unchanged** under the named-lemma fix: `:4-53` (section — "every point of `Y` has the same finite number of preimages … with multiplicities" is exactly `fiberSum_const`), `:70-84`, `:107-124` (the trace block, which genuinely describes our `BranchedCoverData.localInverseAt` / `trace_pullback_at_regular_value` route), `:164-178`, `:228-241`. Under a *wholesale* rkirov swap, `:107-124` would be **orphaned** — his push-pull path has no trace-on-forms map — and `:55-57`'s "counted with multiplicity" would become misleading. Three fixes needed regardless: reconcile `09:55-57` with `challenge-statement.tex:198`; `09:225` references a nonexistent `thm:trace-pullback-identity` (renders `??`); there is a stray bare `...` at `09:109`. And nothing in §09 explains *why the fallback cannot fire* — add one sentence, on the model of rkirov's `Jacobians.lean:434-437`, plus a positivity sentence once `degree_pos` lands.

One caveat the layman text cannot currently support: `lem:push-pull-descend`'s "both maps descend to homomorphisms on the lattice quotients" (`09:164-178`) is **vacuous on our side today**, because the lattice is `⊥`. That is a lattice problem (gaps 14/15), not a degree problem.

**(f) Recommendation: KEEP, plus two small additions. Do not port.**
1. Add the named existence lemma (5–10 lines; the proof is already written at `TracePullbackProviderU.lean:105-111`), then `ContMDiff.degree_eq_branchedDegree_of_nonconstant` with no `∃`-hypothesis. **This closes gap 22 outright.**
2. ADAPT rkirov's `surjective_of_nonconstant` (`JacobianConstruction/PeriodLattice.lean:452`) as a *model* for a new surjectivity lemma, then get `ContMDiff.degree_pos` free from `branchedDegree_pos`. ~60–120 lines. A genuine gap, and on our own plan at `plan.md:506`.
3. RESTATE the tex per (e).
4. If the Sanchez degree material is ever wanted, go to `Brsanch/jacobian-lean-challenge` directly — see §Licence.

---

## 4. The whole-swap option

The question Michal asked is "does it make sense to fit his formalization in there". The honest answer depends on *where*, so here are the three options priced separately.

### Option A — per-gap porting (what §3 costs if done gap by gap)

Adding up the per-gap estimates: gap 7 ~40 lines; gap 19 ~150–300; gap 21 ~500–1,000 new / ~400 deleted across ~125 files; gap 22 ~70–130. Those four are tractable and together are **under ~1,500 lines of new Lean**. Everything else in the table is either a retirement (gaps 1, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 16, 17) or a route change costing thousands of lines (gaps 2, 14, 15, 18, 20). **Per-gap porting works for exactly the small gaps and fails for exactly the large ones** — because each large one sits on a different 10–20k-line substrate of his.

### Option B — swap the engine wholesale behind `Solution.lean`, keep our blueprint as the narrative layer

This is more attractive than it first looks, for one specific reason: **the two `Solution.lean`s are already shaped the same.** Compare

```
-- ours (Solution.lean:89-92, :119-120, :147-152, :223-235)
Jacobian X := ULift.{u} (ComplexTorus.quotient (Fin (genus X) → ℂ) (periodFullComplexLatticeU X))
ofCurve P  := fun Q => ULift.up (AbelJacobi.analyticOfCurveU X P Q)

-- his (Jacobians.lean:651-653, :682, :703-706, :443-444)
Jacobian X := ULift.{u} (JacobianTorus X)
ofCurve P  := fun Q => ULift.up (JacobianTorus.ofCurve P Q)
```

A swap means replacing the right-hand sides, not the left. Concretely:

**What it costs.**
1. **Licence and provenance work** (§5) — mandatory, and the Sanchez sub-provenance needs resolving before anything is copied.
2. **A Mathlib bump of his whole tree**: v4.30.0 / `c5ea003` → v4.31.0-rc1. 72,403 lines, 251 files. Most of it is renames and `simp` drift, but at that volume it is a sustained effort, not an afternoon. His `verify.sh` / `comparator/` harness would need re-pinning too.
3. **Smoothness-index reconciliation**: his statements are at `ω`; our `HolomorphicForms`/`Periods` layers are at `(⊤ : WithTop ℕ∞)`. `Solution.lean` already works at `ω`, so the public surface is fine, but any *mixing* of his engine with our retained layers needs care.
4. **Deleting, not adapting, most of our two biggest layers.** `Periods/` (29,695 lines) and the de Rham/Hodge part of `HolomorphicForms/` would be superseded outright. That is the real cost, and it is emotional as much as technical.

**What it saves.** The five classical theorems we have not got and he has: Riemann–Roch unconditionally in every genus, Serre duality, the residue theorem, Abel's theorem, and period-lattice full rank — plus a sound `StableChartAt`-free chart discipline, a real line integral, a real degree with `degree_pos`, and zero sorries and zero custom axioms. Our remaining sorry count would go to zero and our one custom axiom (`localPullbackAt_holomorphic`) would be eliminated along with the trace layer that needs it.

**What we keep.** This is the part worth stressing, because it is most of what Michal said he cares about:
- **The entire blueprint and all 100 `layman` blocks are a narrative layer over an architecture rkirov shares.** `tex/sections/07-complex-tori-and-jacobians.tex` (the complex-torus package), `tex/sections/10-main-theorem-assembly.tex` (the slot-filling narrative), `tex/statements/challenge-statement.tex`, and `tex/statements/dependency-index.tex` describe his object as accurately as ours. Nine of the eleven rows of the dependency index stand unchanged; only `thm:period-lattice`'s dependencies (`:17-18`) and `thm:abel-jacobi-injective`'s (`:23-24`) get rewritten.
- `Jacobian/ComplexTorus/` (2,653 lines) is ours, sound, and more general than his `ZLatticeQuotient.lean`. Keep it; it is a better Mathlib contribution than his.
- `Jacobian/ComplexTorus/ULiftTransport.lean` works. His is shorter and more general, but there is no reason to swap a working sound file.
- `ref/plan.md`'s Phase 0–4 and Phase 8 (the Mathlib-integration layering) remain correct.
- Our `tex/` blueprint infrastructure — `\lean{}` annotations, dep-graph build, Plain-English toggle, the two PDF entry points — has no counterpart in his repo. He has `docs/clean_room_blueprint.md` (315 lines of prose) and a literate site, but nothing with per-node Lean linkage. **Our narrative layer is strictly better than his and is the thing worth preserving.**

**The `\lean{}` re-pointing is the mechanical core of a swap.** 100 `\lean{...}` targets across `tex/sections/*.tex` (per file: 00:0, 01:1, 02:0, 04:41, 05:13, 06:26, 07:1, 08:11, 09:6, 10:1) plus those in `tex/statements/`. Under a swap, the §04/§05/§06 targets (80 of them) mostly re-point or retire; §07–§10 (19) mostly survive.

### Option C — port the bottom, keep our top (recommended)

The asymmetry found in §3 suggests a third path, and it is the one I would take:

**Port his lowest four layers, where our placeholders are, and keep our own upper layers and blueprint.**

| port | lines | replaces our |
|---|---|---|
| `Path/LineIntegral.lean` + `Path/SmoothPathCore.lean` + `Path/CotangentCoeff.lean` | 2,197 | `opaque pathIntegralFunctionalBundle{,U}`, the `I := 0` period pairing, **and** the `StableChartAt` class (his `CotangentCoeff.lean` is precisely the right way to do what that class was faking) |
| `exists_smoothPath_family` + chart-ball chain machinery (`JacobianConstruction/PeriodLattice.lean:930-1015`) | ~300 | nothing — pure addition |
| `Surface/ULiftManifold.lean` (optional) | 163 | nothing; ours works |
| the lattice redefinition (loop span) + `PeriodLatticeNondegenerate.lean` | ~400 | gaps 3, 4, 14, 15 and the whole `…U` mirror layer |

**~3,000 lines ported, and it closes or retires gaps 1, 2 (partially), 3, 4, 14, 15, 21 and makes the Jacobian a real torus.** What it does *not* get you is the five big classical theorems: Abel's sufficiency (needs his 7.6k-line engine + Čech substrate), period-lattice *discreteness* (Forster 21.4(b), needs the Abel engine), Riemann–Roch (13.7k incremental), and the genus-0 classification in both directions. Those stay open — but they would be open as **four honestly-stated classical inputs** rather than twenty sorries of which eleven are vacuous and four are false. That is a dramatically better position to be in, and it is the position `ref/methodology.md` is trying to reach ("every leaf is either (a) directly in Mathlib or (b) a precise stand-alone 'missing-from-Mathlib' statement").

**Recommendation: Option C, then re-decide.** Option C is reversible and makes the project honest. After it, the remaining question is narrow and answerable: do we want to spend ~20k lines porting his Čech/Dolbeault/RR tower (Option B's substance, without its bookkeeping), or keep those four as declared classical inputs and present the project as "the analytic Jacobian modulo four named classical theorems"? That is a scope decision, not a technical one, and it should be made *after* the engine is real.

---

## 5. Licence and credit

**The two licences.** Ours is MIT (`LICENSE:1-3`, "Copyright (c) 2026 Michal J Wallace"). His is Apache-2.0 (`LICENSE:1-3`, stock text); **there is no `NOTICE` file** in his repo.

**Apache-2.0 → MIT is permitted**, but Apache-2.0 §4 attaches conditions that MIT does not, and they apply to any ported file:

1. **§4(a)** — retain the Apache-2.0 licence text with the copied work. In practice: add `licenses/Apache-2.0.txt` (or `LICENSE-Apache-2.0`) to our repo and reference it from the ported files' headers.
2. **§4(b)** — "cause any modified files to carry prominent notices stating that You changed the files." Every ported file needs a **statement of changes**, not just a credit line.
3. **§4(c)** — retain all copyright, patent, trademark and attribution notices from the source. Keep `Copyright (c) 2026 Rado Kirov. All rights reserved.` and the `Authors:` line.
4. **§4(d)** — if the source has a `NOTICE` file, carry its contents. His has none, so nothing to carry.
5. **§5** — contributions back to his repo are licensed under Apache-2.0 unless stated otherwise. Relevant if we send fixes upstream (we should: the stale docstring at `MappingDegree/Degree.lean:52-57` and the dead doc-only names `cechH1_dolbeault_comparison'` and `exists_lerayCover` are worth a PR).
6. **Repo-level**: a mixed MIT + Apache-2.0 tree should say so in `README.md` and `LICENSE` ("Portions © 2026 Rado Kirov, licensed under Apache-2.0; see `licenses/`"). The combined work can still be distributed under MIT terms *for our parts*; the Apache parts remain Apache.

His own per-file header is the template to mirror — `PeriodLattice/PeriodLatticeNondegenerate.lean:1-4`:

```
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
```

and the model for how to do a *port* properly is in his tree, in the file he took from us — `Jacobians/PlanarStokes/PlanarCompactSupportStokes.lean:10-14`:

> PORTED (with adaptations to this repo's Mathlib pin) from the MIT-licensed tangentstorm/JacobianChallenge, file `Jacobian/Blueprint/Sec03/StokesOnRSWithBoundary.lean` (sub-leaf #5 `stokes_local_euclidean` + helpers), Copyright (c) 2026 Michal J Wallace, https://github.com/tangentstorm/JacobianChallenge — inspection-verified sorry-free at port time.

That is exactly the shape a reverse port should take: upstream repo, upstream file, upstream decl, upstream copyright, upstream licence, and what was adapted.

### What rkirov himself borrowed, and the one provenance problem

From `README.md:171-186` and `formalization.yaml:18-25`, `:215-220`:

| source | licence per his docs | what | survives? |
|---|---|---|---|
| [Brsanch/jacobian-lean-challenge](https://github.com/Brsanch/jacobian-lean-challenge) | **MIT** (`README.md:176-178`, `formalization.yaml:19-21`) | degree / fibre / Hurwitz well-definedness, now `MappingDegree/` | yes |
| [tangentstorm/JacobianChallenge](https://github.com/tangentstorm/JacobianChallenge) — **this project** | **MIT** (`README.md:179-181`) | the rectangle Green's theorem seeding the planar Stokes atom; "whose design notes also flagged pitfalls we then avoided" | yes, `PlanarStokes/PlanarCompactSupportStokes.lean` |
| [mrdouglasny/jacobian-challenge](https://github.com/mrdouglasny/jacobian-challenge) | Apache-2.0 (`README.md:182-185`) | contour deformation, integrated then superseded; "their axiom inventory served as a map of the genuine analytic obstacles" | **no** — not in the final tree |
| Forster GTM 81, Miranda GSM 5, Griffiths–Harris | textbooks | the mathematics | — |

**The provenance problem, stated precisely because it affects us if we port the degree material.** His README and `formalization.yaml` call the Brsanch upstream **MIT**. But the ported files in his tree carry an **Apache-2.0** header — e.g. `MappingDegree/Degree.lean:1-5`, identical in `RegularValueExistsRegUnconditional.lean:1-5` and `DegreeWellDefined.lean:1-5`:

```
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
```

49 files / 9,078 lines repo-wide carry that header (44 of them, 8,176 lines, under `MappingDegree/`). The only in-tree MIT statement is a one-liner at `ProperDegree/Degree.lean:9` ("Original code MIT-licensed by Bryan Sanchez (2026)"). His `LICENSE` is stock Apache-2.0 with no MIT, no `Portions`, no Sanchez text, and there is no `NOTICE`. The strings `Brsanch`, `jacobian-lean-challenge`, `Portions` and `Adapted from` appear nowhere in `Jacobians/*.lean`. So the ported files assert a licence for third-party code that the project's own documentation says is governed by a different one, with no upstream URL in any header.

Also worth knowing if the numbers are quoted: `README.md:163-166` says the Sanchez port is "3,296 lines across 22 surviving files"; `MappingDegree/` is **48 files / 8,587 lines**. The charitable reading is that 3,296 was the as-received size and the directory grew around it — but the README asserts the *surviving* count.

**Consequence for us: do not route the Sanchez material through his repo.** If any of the degree/fibre machinery is ever wanted, take it from `Brsanch/jacobian-lean-challenge` directly, read that repo's own `LICENSE`, and build the provenance chain from there. (Per §Gap 22 this is moot — the fix is 5–10 lines of our own code.) For *rkirov's own* code (`Path/`, `PeriodLattice/`, `Abel/`, `Monodromy/`, `SphereTopology/`, `Surface/`, `JacobianConstruction/`, `DolbeaultComparison/`, `Cech/`, `LaurentTail/`, `TailDuality/`, …) the Apache-2.0 chain is clean and Option C is unproblematic.

**Credit we should give regardless of whether we port a line.** This comparison itself is derived from his repo: his routing decisions (`docs/clean_room_blueprint.md`, `docs/walls_bc_plan_2026-06-10.md`, `docs/RETRO.md`) are what let us identify four false statements, a contradictory typeclass, and a dead 8.5k-line tower. `docs/clean_room_blueprint.md` is explicitly written as a hint document ("a 'modulo hint': the path to the whole proof, the genuinely hard steps, the routing decisions that are not obvious from the textbooks … deliberately gives no Lean"). Its "⚠ the trap" lines are worth reading in full before any further route decision; three of them contradict routes we took:

- `:254-255` "Use Miranda's concrete tail duality, **not** Hodge symmetry … This is *the* key routing decision of the project."
- `:276-277` "Avoid the cut-surface/dissection route; it forces a `∃ cutSurface` obligation that is hard and unnecessary. Forster 20.7 routes around it."
- `:312-315` "the genus definition, the `L(D)` model, and the multiplicity normal form must all be junk-free representations. Those three choices are where a clean-room attempt most easily goes silently wrong (a `toFun`-junk `L(D)` makes `l(D) ≡ 0` and RR false, etc.)."

One caution: `:293-294` ("Cheapest formal path is the **Riemann cut-surface + Green's-theorem** flavor of period nondegeneracy, **not** Hodge / de Rham") is **stale relative to his shipped code**, which uses the planar maximum principle (`PeriodLatticeNondegenerate.lean:6-21`). Read the Lean, not the hint.

A courtesy note, since his README already cites us: it would be worth telling him this comparison exists, and that his `MappingDegree/` headers have a licence discrepancy. He has a disclaimer inviting exactly this kind of review (`README.md:30-39`: "a subject-expert review is still welcome").

---

## 6. Formalization-honesty notes

This is the section to act on first, independent of any porting decision. Nothing here was found by reading rkirov; it was found by reading our own tree with his as a control.

### 6.1 Things that would smuggle hypotheses, in severity order

1. **`StableChartAt ℂ X` is refutable under the challenge's own hypotheses** (proof in §Gap 21), yet it is supplied as a *global instance* by `sorry` at `Solution.lean:35-37` and threaded through **120 files**. Every theorem in `Periods` / `AbelJacobi` / `HolomorphicForms` / `TraceDegree` / `AnalyticJacobian` whose binders contain it alongside `[CompactSpace X] [ConnectedSpace X]` is **vacuously true**. This includes eleven of the twenty engine sorries (gaps 1, 2, 3, 4, 14, 15, 16, 17, 18, 19, 20) *and everything in those layers already marked `\leanok`*. A `sorry` for a false proposition is strictly worse than an open obligation, because it silently makes downstream statements meaningless rather than merely unproved. **Fix first.**

2. **The period pairing is the zero map, so the period lattice is `⊥` and `Jacobian X` is `ℂ^g`, not a torus.** `Periods/PeriodFunctionalU.lean:75`, `:95` (`let I := 0`); proved in-tree at `Periods/PeriodSubgroupZLatticeU.lean:54` (`periodPairingComplexU_eq_zero`), `:73`, `:82-85` (`basisAlignedPeriodSubgroupConcreteU_eq_bot`). Root cause: `Blueprint/Sec03/PeriodHomologyInvariance.lean:322-329`, `singularChain_integration_from_simplex … : ∃ _ : SingularOneChain X →ₗ[ℤ] …, True := ⟨0, trivial⟩`. Consequence: `CompactSpace (Jacobian X)` (`Solution.lean:110`) is asserted of a non-compact object behind the gap-15 sorry, and `lem:push-pull-descend`'s plain-English claim that the maps "descend to homomorphisms on the lattice quotients" (`tex/sections/09-degree-trace-push-pull.tex:164-178`) is currently vacuous.

3. **The Abel–Jacobi map is an `opaque` whose spec the zero function satisfies.** `AbelJacobi/PathIntegralFunctionalU.lean:40-53` (three fields: `val`, `val P P = 0`, smooth), `:61-62` (`Inhabited` witness `fun _ _ => 0`), `:69` (`opaque`). Nothing about `ofCurve` beyond "sends `P` to `0`" and "is smooth" is derivable. `ofCurve_inj` — one of the four anti-hack theorems — is therefore not merely unproved but **unprovable until the definition is made real**. The blueprint should reclassify gap 2 from an open *proof* obligation to an open *definition* obligation.

4. **`exteriorDerivative := 0` makes the de Rham layer's umbrella theorems vacuous or false.** `HolomorphicForms/SmoothDifferentialForm.lean:68-73`, with `ClosedForm = ⊤` (`:84-89`) and `ExactForm = ⊥` (`:92-97`). Gaps 16 and 17 are the two halves of a 4g-vs-2g double-count over a free product `coeff × payload`, and they are **jointly contradictory**: together they would force `genus X = 0` and `H₁(X,ℤ) = 0` for every compact Riemann surface. The `c89e833` / `e94a1a2` episode is instructive: the commit correctly diagnosed the falsity in prose and then re-introduced it in Lean behind `∈ ExactForm 0 X` (which is `⊥`). The revert was right.

5. **Vacuous umbrella theorems from placeholder definitions.** `Blueprint/Sec03/StokesOnRSWithBoundary.lean`: `IsExteriorDerivativeAux _ _ : Prop := True` (`:42-43`), `integrateTwoForm … : ℝ := 0` (`:92-96`), `integrateOneFormBoundary … : ℝ := 0` (`:109-113`), so `stokes_partition_unity` is `by rfl` (`:448-455`) and `stokes_on_rs_with_boundary` (`:471-479`) is `0 = 0`. "Global Stokes on a compact 2-manifold with corners" is not proved; the only real content in that file is `stokes_local_euclidean` (`:325`) — the rectangle Green's theorem, which is genuine and which rkirov ported. Similarly `Periods/RiemannBilinearRefinement.lean:219-229` (`… _obligation : Prop := True` / `:= trivial`). Placeholder density (`Nonempty Unit` / `:= trivial` / `⟨()⟩`): `Blueprint/Sec03` 25, `Periods` 34, `HolomorphicForms` 14.

6. **`Orientable` is information-free.** `Periods/Orientable.lean:14-16`: `existsConsistentChartChoice : Nonempty Unit := ⟨()⟩` — every space is `Orientable`, so gap 5's and gap 10's orientability hypotheses carry nothing. Likewise `Triangulation := PUnit` (`SurfaceClassificationData.lean:62-63`), `DualGraph`/`DualSpanningTree := PUnit` (`DualGraphCut.lean:19-25`). This is how gaps 5 and 10 became false.

7. **The `Unit`/`True` scaffolding under the Abel two-point construction.** `AbelJacobi/AnalyticOfCurveBasis.lean`: `LogPeriodVanishing` has one field `witness : Unit` (`:341-347`), as does `SingleValuedLogPrimitive` (`:1127-1134`); `glue_local_extensions_to_global` has hypotheses `(_hHol : True) (_hZero : True) (_hPole : True)`, conclusion `True`, proof `trivial` (`:1322-1335`); `construct_toMap_global : ∃ (_ : X → OnePoint ℂ), True := ⟨fun _ => OnePoint.infty, trivial⟩` (`:1341-1345`). So `ref/plan.md:496-497`'s "The Abel two-point construction feeding it is sorry-free" is literally true and substantively empty, and the `\leanok` marks on `thm:abel-basis-aligned-two-point` (`tex:238-252`), `lem:abel-two-point-form` (`:292-300`) and `lem:two-point-principal-packaging` (`:333-343`) should be withdrawn.

8. **One custom axiom.** `HolomorphicForms.localPullbackAt_holomorphic` (`TraceDegree/TraceDefinition.lean:220`, catalogued at `ref/axiom-audit.md:47-74`): "the remaining local analytic section-regularity obligation for the trace-pullback construction." rkirov has none. It should be a `sorry`-backed theorem, not an axiom, so it shows up in the ledger and in `#print axioms`.

9. **A circular blueprint edge.** `tex/sections/04-branched-covers-genus-zero.tex:929` gives gap 20 `\uses{thm:exists-biholomorph-one-point-of-genus-zero}`, but gap 18 needs a topological `X ≃ₜ OnePoint ℂ` that only gap 20 can produce. Our own file says so (`MeromorphicToBranchedCover.lean:3068-3071`: "which depends on this theorem"). The dep graph is therefore wrong as drawn.

10. **Blueprint `\leanok` drift in both directions.** `lem:de-rham-comparison-map1-zero-period-primitive-exists-provider` (`tex:728-734`) is marked "Open obligation (`sorry`)" against a decl that is sorry-free, while the actual sorry one level below is unlabelled. Conversely the Abel S19 chain is `\leanok` over `Unit`/`True` scaffolding. And in two places the blueprint's *English* states the true classical theorem while its `\lean{}` target is a false surrogate (`tex:728-734`, `tex:762-768`).

11. **`sorries.jsonl`'s reachability flag measures the wrong thing.** `scripts/list-sorries.py:134-154` derives `r` from `lake build` warnings, i.e. import-closure reachability. All nine polygon gaps are marked `"r":1` but appear term-level unreachable from `Solution.lean`; `Polygon4gCellular.lean:polygon4g_succ_hurewicz_iso_freeZ` is marked `"r":0` from the same closure. This has been steering effort: `ref/plan.md:310-313` calls the polygon tower "the current heavy edge" on the strength of that flag.

### 6.2 What a final audit must check

1. **`#print axioms` on every public declaration of `Solution.lean`**, and separately `#print axioms` on each of the nine polygon gaps' consumers, to confirm or refute the term-level reachability result in §Gaps 5–13 before anything is deleted. No build was run for this report.
2. **A refutation sweep**: for every typeclass the project introduces, check it is inhabited in the intended setting. `StableChartAt` was not. A one-line `example : StableChartAt ℂ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by infer_instance` would have failed from the start. The same discipline applies to `Orientable`, `FiniteDimensionalHolomorphicOneForms`, `PiecewiseC1PathRegularity`.
3. **A placeholder sweep**: grep for `:= 0`, `:= True`, `:= trivial`, `:= PUnit`, `Nonempty Unit`, `⟨()⟩`, `opaque`, and `∃ _, True` in *definition* position, and record each as an open **definition** obligation in the ledger, distinct from open proof obligations. The sorry count is the wrong single number; this project needs two.
4. **A vacuity check per sorry**: for each remaining `sorry`, ask whether its binder list is satisfiable. Eleven of twenty currently are not.
5. **An honest frontier statement** in `README.md` and the blueprint: four classical theorems (Abel's sufficiency, period-lattice full rank, Riemann–Roch for the genus-0 case, and the genus-0 classification's backward direction) plus a real path-integral definition, rather than "20 sorries".
6. **`#print axioms` on the trace layer** specifically, to confirm `localPullbackAt_holomorphic` is the only axiom and that it has not spread.

---

## 7. Open questions needing Michal's decision

1. **Do you want the project to remain fully independent, or to consume rkirov's engine?** This is the top-level fork, and it is a values question, not a technical one. His repo is AI-produced and unreviewed by a mathematician (`README.md:30-39`); ours is too. Consuming it trades independence for soundness. Option C in §4 is the middle path I would take.
2. **Will you retire the polygon tower?** ~8,500 lines, four of its nine open statements provably false, apparently unreachable from `Solution.lean`. Retiring it is the largest single simplification available. If you keep it, it should be relabelled as an independent contribution (a `Polygon_4g` H₁ computation and a Tietze normal-form development), not as the Jacobian's critical path. **Confirm reachability with `#print axioms` first.**
3. **`StableChartAt`: delete, or keep and quarantine?** Deleting means ~125 files touched and ~500–1,000 lines of new Lean at 10 sites. Keeping it means every statement in five layers stays vacuous. I see no third option, but the sequencing is yours — it is also a prerequisite for anything else being meaningful, so it is hard to defer.
4. **Is the de Rham / Hodge layer worth repairing, or should `2g = rank H₁` be reached another way?** Repairing means building a real 1-form type with a real `d` (~400–800 lines) and then the periods-vanish-⇒-exact theorem (~1,500–2,500 more), with no portable code from anywhere. The alternative is rkirov's Čech + Riemann–Roch + Dolbeault derivation (~5,000+ lines ported). A third option: since our `genus` is already analytic, drop the comparison from the critical path entirely and keep it as context for §4.
5. **Riemann–Roch: is the "Architectural Shortcut" still the right call?** The evidence says it did not save work, it relocated it into gap 20 — and rkirov's RR is proved *unconditionally in every genus*, so there is no cheaper genus-0-only RR to port. The cheap intermediate move (~700 lines) is to isolate `exists_riemannRoch_divisor` as one named hypothesis, the way he isolated `HasHolomorphicPrimitives`, which converts two unroutable sorries and a circular edge into one honest frontier statement without committing to the 13.7k-line tower.
6. **How much plain-English rewriting are you willing to do?** Concretely: under Option C, roughly 22 `layman` blocks in `tex/sections/05-polygonal-model.tex` and 6–8 in `tex/sections/06-periods-and-riemann-bilinear.tex` become orphaned or need rewording, and ~30 of the 100 `\lean{}` targets re-point. Everything in §07–§10 and `tex/statements/` survives. The architecture-level prose — which is the best writing in the project — is unaffected either way, because rkirov's architecture is ours.
7. **Licence posture.** Are you willing to carry Apache-2.0 material in an MIT repo (with `licenses/`, statement-of-changes headers, and a `README` note)? And do you want to raise the Sanchez licence discrepancy with him before porting anything that touches `MappingDegree/`?
8. **Should we tell him?** His README already credits this project, and his disclaimer invites review. A short note pointing at this file — plus the two small upstream bugs found (the stale `degree_pos` docstring at `MappingDegree/Degree.lean:52-57`, the doc-only names `cechH1_dolbeault_comparison'` and `exists_lerayCover` with no corresponding declarations) — would be reciprocal and cheap.
9. **Housekeeping, independent of everything above:** `README.md:9-11` and `tex/macros.tex:109-110` still point at `tangentstorm/JacobianChallenge`; `README.md:40` still says the toolchain is `v4.28.0` when `lean-toolchain` says `v4.31.0-rc1`; `Jacobian/Challenge.lean:7` says v0.3 while the current spec is v0.4 (syntactically identical, so this is cosmetic).

### The one-sentence version

The architecture was right and an independent complete solution confirms it; what this comparison found is that the *engine underneath it* is placeholder in four load-bearing places and that one of its typeclass assumptions is refutable — so the highest-value next move is not to port a proof, it is to delete `StableChartAt`, make the path integral real (rkirov's `Path/` layer, ~2,200 lines, is exactly the missing piece), and re-count the frontier honestly.
