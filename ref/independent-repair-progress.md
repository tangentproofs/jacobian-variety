# Independent repair — progress log

Working log for `ref/independent-repair-brief.md`. Branch `independent-repair`, cut from
`rkirov-comparison` (84c7d95). Until 03b303b: local commits only. **From the 2026-10-27
cloud session on, the owner's updated instruction supersedes brief §0 and §4:** push to
`independent-repair` (only), and run the full build and comparator check here (a cloud
container, not the shared box).

Times are America/New_York. Nothing is recorded as compiling unless it was actually built here.

## Build environment (established 2026-10-27 17:10 EDT)

| item | state |
|---|---|
| toolchain | `leanprover/lean4:v4.31.0-rc1` installed with elan (was absent; box had 4.28.0 / 4.34.0-rc2 / 4.35.0-rc1) |
| Mathlib | `lake exe cache get` → exit 0, 8477 files downloaded, **8119 oleans** present. No source build. |
| build command | `nice -n 19 taskset -c 0-2 lake build Jacobian.<Module>` — narrow modules only, per brief §4 |
| forbidden here | `lake build`, `lake build Jacobian`, `lake build Jacobian.Solution`, comparator, any whole-tree build |
| disk | 19 GB free at start; `.elan` 8.6 GB. Shared box, 8 cores, capped to cores 0-2. |

## Baseline counts (2026-10-27 17:28 EDT, commit 84c7d95)

Counted with a comment-aware scanner (`sorry` in term position only), not raw grep:

| metric | value |
|---|---|
| engine sorries (outside `Jacobian/Challenge.lean`) | **21** (20 engine + the `Solution.lean:37` instance) |
| frozen-spec sorries in `Jacobian/Challenge.lean` | 24 (untouched, frozen) |
| declared custom axioms (`^axiom`) in `Jacobian/` | **0** |
| `StableChartAt` mentions / files | 895 / 120 |

This matches `ref/rkirov-gap-comparison.md`'s independent count, so the two sweeps agree.

---

## 2026-10-27 17:35 EDT — milestone 1 + 2 complete

**Commit:** `<filled in below>` — see the commit-hash table at the end of this file.

### What changed

1. **`ref/stablechart-uses.md`** (new, 358 lines) — milestone 1. Complete classification of all 895
   `StableChartAt` mentions across 120 `.lean` files: 809 pass-through binders, 42 comments, 25 `omit`
   lines, 7 definition-site lines, 7 textual real uses, 4 no-op `haveI` shuffles, 1 `sorry` instance.
   Folding in the three real uses that go through the derived lemma `achart_eq_of_mem_source` (and so
   never mention `StableChartAt` textually) gives **10 real content-consumption sites in 5 files**,
   split into kind (i) "nearby point has the same chart" (6) and kind (ii) "therefore `coordChange` is
   the identity" (3, the parallelizability error) — plus `Solution.lean:37`.
   The file ends with a 7-step ordered plan for goal (a).

2. **`Jacobian/Periods/ChartStabilityRefutation.lean`** (new, 118 lines) — I did not take the
   inconsistency claim on trust from `ref/rkirov-gap-comparison.md`; it is now a compiled theorem:

   ```lean
   theorem not_chartStable_of_compactSpace
       (X : Type*) [TopologicalSpace X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X] :
       ¬ ChartStable ℂ X
   ```

   with `ChartStable` the predicate form of the class's single field. Proof: chart stability makes chart
   sources pairwise equal-or-disjoint hence clopen; connectedness promotes one to all of `X`; so one
   chart is a homeomorphism onto an *open* subset of `ℂ`; compactness makes it compact hence clopen
   hence `= ℂ`; but `ℂ` is not compact. Two supporting lemmas,
   `chartStable_isClopen_source` and `chartStable_source_eq_univ`, are stated separately.

   It is stated about a **predicate, not the class**, deliberately: it must survive the class's deletion
   as the permanent record of why the class cannot return.

### Builds run (both green)

| command | result |
|---|---|
| `lake build Jacobian.HolomorphicForms.EvalAtOneHelper` | **exit 0**, 2373 jobs — milestone 2 baseline, a module with a real `StableChartAt` use, green *before* any edit |
| `lake build Jacobian.Periods.ChartStabilityRefutation` | **exit 0**, 2072 jobs |

Axioms verified by `lake env lean` + `#print axioms` on all three new theorems:
`[propext, Classical.choice, Quot.sound]` — exactly the `comparator/jacobian.json` allowlist, no
`sorryAx`, no new axioms.

### Counts after

Unchanged: 21 engine sorries, 0 custom axioms. The new file adds 3 sorry-free theorems.

### Next step

Milestone 3: first commit removing `StableChartAt` from one real-use cluster. Target is
`Jacobian/HolomorphicForms/EvalAtOneHelper.lean` — 66 lines, 2 importers, shallow imports, and it holds
the kind-(ii) site that `ref/rkirov-gap-comparison.md:422` calls the most dangerous of the ten
(`contMDiff_tangentSection_one`, a nowhere-zero smooth vector field, false for genus `≠ 1`).

### Blockers

None. One standing limitation, not a blocker: `Solution.lean:37`'s removal and the
`HolomorphicForms` bulk binder strip cannot be verified here (they need a whole-tree build, forbidden by
brief §4) and will be recorded as **pending build machine**.

---

## 2026-10-27 20:40 EDT — cloud session: goal (a) done, `StableChartAt` deleted

Session moved to a Claude Code cloud container (4 cores, 15 GB). Full builds take ~5½ min
with the Mathlib cache, so whole-tree builds are used freely from here on.

### Found on arrival

* **03b303b did not build.** It removed `contMDiff_tangentSection_one` but three callers
  (`CompactRiemannSurface.lean:776`, `TraceSpec.lean:2635`, `TraceDefinition.lean:472`) and
  one argument order (`CompactRiemannSurface.lean:260`) were not updated:
  `lake build Jacobian.Solution` → 2 failed modules. Baseline below is measured at 40f287b
  with 03b303b's `EvalAtOneHelper.lean` reverted (green, 4043 jobs, 21 engine sorries).
* **`lake build Jacobian` had 7 pre-existing failures** outside `Solution`'s closure, all
  Mathlib-migration drift (`map_zsmul`/`map_nsmul` argument order, a `Path.map'` rewrite, a
  `Fin.revPerm` HEq, a `simp` zero case): `AnalyticJacobian/MkOps`,
  `HolomorphicForms/EvalLinearMap{VecExtra,Zsmul}`, `Periods/PathLiftSimp`,
  `Periods/PathIntegralViaCoverSymm`, `Periods/PeriodFunctionalIntSmul`,
  `TraceDegree/PullbackFormsLinearMapIntSmul`. Fixed (one-line each).
* **Dependency tool fix.** `scripts/DepGraph.lean` skips internal names, which drops every
  `private` declaration and every `_proof_n` auxiliary — and with them the edges through
  them. With those included (scratch copy), the reachable set from the public API grows from
  993 to 1272 declarations, and it shows that the *trace map on forms* (`traceFormsBundled`,
  hence `pullback` and `pushforward_pullback`) also depended on chart stability, through
  private helpers in `TraceSpec.lean`. (Reachable sorries at baseline: gaps 2, 3, 4, 15, 18,
  19, 20 and the instance; gaps 1, 14, 16, 17 and the whole polygon tower are **not**
  reachable — `ref/rkirov-gap-comparison.md`'s claim that 16/17 reach the Jacobian is wrong
  at the declaration level.)

### What changed (goal (a))

1. Deleted `Jacobian/Periods/TrivializationContinuousLinearMapAt.lean` (the class, its
   `StableChartAt H H` instance, `achart_eq_of_mem_source` and three unused `mfderiv` lemmas)
   and the `sorry` instance at `Solution.lean:35-37`.
2. Stripped 837 mentions mechanically in 115 files: 809 pass-through binders, the `omit`
   lines, the 4 no-op `haveI _stable… := inferInstance` lines. 95 imports of the deleted file
   were replaced by its two Mathlib imports.
3. Real uses, by dependency closure (stopping at true statements):
   * **Reproved honestly** (no chart stability):
     `analyticAt_chart_symm_of_isHolomorphicAt_of_mem_ball` (now via analyticity of chart
     transitions; gains an `[IsManifold 𝓘(ℂ) ⊤ X]` binder, as do its 3 callers) and
     `holomorphicOneForm_ext_on` (identity principle on a dense set, now read through the
     bundle trivialization at the point instead of the frame-dependent fibre norm).
   * **Cut to labelled gaps** (true statements whose only proofs used chart stability):
     - `compactRiemannSurface_finiteDimensionalHolomorphicOneForms_frontier` — now a
       **named classical input** (finiteness, Forster §14);
     - `traceForm_extension_per_BCD` (TraceSpec) — trace of a form extends over branch values;
     - `meromorphic_no_poles_holomorphic_representative` (MeromorphicToBranchedCover) —
       removable singularities.
   * **Retired** (moved verbatim, unbuilt, to `Attic/StableChartRetired/`): the 70 top-level
     declarations (83 constants with auxiliaries) whose statements are false without a
     global frame or vacuous with it — the eval-at-`1` sup-norm Montel chain in
     `CompactRiemannSurface.lean` (51), the eval-at-`1` trace helpers in `TraceSpec.lean`
     (16) and `TraceDefinition.lean` (3). None is reachable from the public API once the
     three cuts are in place; checked with the fixed dependency graph.
4. Prose: `tex/statements/challenge-statement.tex` `lem:stable-chart-at-instance` rewritten
   (refuted, not open), `scripts/audit-leanok-axioms.py` example reworded — both logged in
   `ref/plain-english-changes.md`. Stale `PeriodHomologyInvariance.lean.bak` deleted.

`ChartStable` (the predicate) and `not_chartStable_of_compactSpace` stay, as the permanent
record; `EvalAtOneHelper.lean`'s explicit-hypothesis lemmas stay (honest, satisfiable).

### Builds

| command | result |
|---|---|
| `lake build Jacobian.Solution` | **green**, 4043 jobs |
| `lake build Jacobian` | **green**, 4351 jobs (first time on this branch) |

### Counts

| metric | before (40f287b) | after |
|---|---|---|
| engine `sorry` declarations (`declaration uses sorry`, whole `Jacobian`) | 21 | **23** (−1 refuted instance, +3 labelled gaps) |
| frozen spec `Jacobian/Challenge.lean` | 24 | 24 (untouched) |
| custom axioms | 0 | 0 |
| `StableChartAt` in live Lean code (non-comment) | 895 mentions | **0** |

### Next

Goal (b): real line integral and period lattice.

---

## 2026-10-27 — goals (b) and (c): genuine period lattice, genuine Abel–Jacobi map

### What changed

1. **`Jacobian/Periods/GenuinePeriodLattice.lean`** (new). Built on the project's existing,
   sorry-free multi-chart line integral `pathIntegralViaCover` (chart pullback
   `ω(c⁻¹ e) ∘ D(c⁻¹)(e)` integrated with Mathlib's `curveIntegral` on each segment of a
   chart-cover subdivision; independent of subdivision and charts for `C¹` paths, by
   `pathIntegralViaCoverWith_refinement_invariant'`). Defines
   * `IsC1Path γ` (C¹ in every chart), `isC1Path_refl`;
   * `lineIntegral ω γ := pathIntegralViaCover ω γ`;
   * `periodVector X γ := (∫_γ ω₁, …, ∫_γ ω_g)` for the project basis `holomorphicOneFormFinBasis`;
   * `genuinePeriodSubgroup X := AddSubgroup.closure {periodVector γ₁ - periodVector γ₂ |
     γ₁ γ₂ : Path P Q C¹}` — integrals over closed `C¹` curves `γ₁·γ₂⁻¹` (closed loops are
     the case `γ₂ = refl`, `periodVector_mem_of_loop`);
   * **named classical input** `periodLattice_discrete_and_span` (discrete + `ℝ`-spanning;
     Riemann bilinear relations, Forster §21);
   * the compact fundamental domain (proved from the classical input via `ZSpan`) and the
     bundled `genuinePeriodLattice X : FullComplexLattice (Fin g → ℂ)`.
2. **`periodFullComplexLatticeU X := genuinePeriodLattice X`** — so the public
   `Jacobian X = ULift (ℂ^g / Λ)` with `Λ` the genuine period lattice, no longer `ℂ^g / ⊥`.
3. **Abel–Jacobi** (`AbelJacobi/PathIntegralFunctionalU.lean`, `AnalyticOfCurveU.lean`):
   the `opaque pathIntegralFunctionalBundleU` (spec satisfied by `0`) is deleted.
   `pathIntegralFunctionalU X P Q := periodVector X γ` for a chosen `C¹` path `γ : P → Q`
   (`if … then … else 0`; the `else` never fires given `exists_isC1Path`). Proved:
   well-definedness modulo periods (`pathIntegralFunctionalU_sub_mem`), `ofCurve P P = 0`
   (`analyticOfCurve_selfU`, now a real proof: the self-integral is a period), and
   `analyticOfCurveU_eq_mk_periodVector` (value = class of the period vector of **any**
   `C¹` path). Labelled gap: `analyticOfCurve_contMDiffU` (holomorphy, via local
   primitives). Gap `exists_isC1Path` (C¹ path-connectedness; not on the public path).
4. **Injectivity**: `pathIntegralFunctional_separates_pointsU` restated over the genuine
   functional and lattice; now labelled as the **named classical input** "Abel's theorem,
   two-point form" (Forster 20.7, §21).
5. **Pushforward / pullback descent**: the "`⊥` shortcut" proofs of
   `pushforwardTraceLift_preserves_latticeU` and `traceDualPullbackLift_preserves_latticeU`
   are gone; both are now true, labelled gaps (change of variables `∫_{f∘γ}ω = ∫_γ f^*ω`;
   lifting closed curves through the branched cover).
6. **Retired** to `Attic/ZeroPeriodPairingU/` (unbuilt): the six files of the universe-`u`
   zero-pairing chain — `PeriodFunctionalU` (pairing `:= 0`), `PeriodSubgroupZLatticeU`
   (incl. `basisAlignedPeriodSubgroupConcreteU_eq_bot`), `BasisAlignedPeriodSubgroupU`,
   `PeriodFundamentalDomainU`, `PeriodVectorsLIU` (gap 15, false), `H1BasisU` (gaps 3, 4).
   After step 2 nothing imported them.

### Builds and counts

`lake build Jacobian.Solution` and `lake build Jacobian`: **green** (4344 jobs).

| metric | after (a) | after (b)+(c) |
|---|---|---|
| engine sorry declarations (whole `Jacobian`) | 23 | **25** |
| reachable from the public API (decl-level graph, private/aux included) | 10 | **11** |
| custom axioms | 0 | 0 |

Sorries added: `periodLattice_discrete_and_span` (classical input),
`analyticOfCurve_contMDiffU`, `exists_isC1Path`, the two lattice-preservation gaps.
Removed with the retired chain: gaps 3, 4, 15. Gap 2 restated (count unchanged).

### Neighbouring cases of the same class (zero / spec-only placeholders), ledgered

All **unreachable** from the public API (decl-level graph), so ledgered rather than fixed:

| placeholder | where | status |
|---|---|---|
| Type-0 `periodPairing` with chain integration `:= 0` | `Periods/PeriodFunctional.lean` | unreachable; feeds the Type-0 `AnalyticJacobian/*`, `PullbackBasis`/`PushforwardBasis`, Type-0 Abel chain |
| `opaque pathIntegralFunctionalBundle` (Type-0, spec satisfied by `0`) | `AbelJacobi/AnalyticOfCurveBasis.lean` | unreachable |
| `LogPeriodVanishing`, `SingleValuedLogPrimitive` (`witness : Unit`), `True`-valued gluing lemmas | `AbelJacobi/AnalyticOfCurveBasis.lean` | unreachable scaffolding |
| `exteriorDerivative := 0` | `HolomorphicForms/SmoothDifferentialForm.lean` | unreachable (de Rham/Hodge layer) — see goal (d) |
| "global Stokes" reducing to `0 = 0` | `Blueprint/Sec03/StokesOnRSWithBoundary.lean` | unreachable |
| `Orientable := Nonempty Unit`, `Triangulation`/`DualGraph := PUnit` | `Periods/Orientable.lean`, `SurfaceClassificationData.lean`, `DualGraphCut.lean` | unreachable (polygon tower) — see goal (d) |
| `wedge_integration_pairing_exists` witnessed by `0` | `Periods/PeriodFunctional.lean` | unreachable |

---

## 2026-10-27 — goal (d): false gaps retired, gap 7 proved

### What changed

1. **Retired** (dependency closure, verbatim, to `Attic/FalseGaps/`, unbuilt): gaps 5, 6, 8
   (`TietzeReduction`), 9 (`HandleSwapHomeo`), 10 (`DualGraphCut`), 16
   (`DeRhamComparisonMap`), 17 (`HodgeProjection`), and — same class, root-cause rule —
   gap 14 (`PeriodFunctional`, false because the Type-0 pairing is `0`). 227 constants left
   18 source files with them (the Type-0 de Rham/Hodge rank chain, the Type-0
   `periodFullComplexLattice`, the Type-0 analytic Jacobian push/pull in
   `PullbackBasis`/`PushforwardBasis`/`AnalyticDegree`, the polygon classification
   assembly in `SurfaceClassification`/`CellularHomologyRS`). **None was reachable** from
   the public API (checked on the fixed graph before moving). Counterexamples recorded in
   `Attic/FalseGaps/README.md`.
2. **Gap 7 proved**: `handleSwap_index_ordering` (`Periods/TietzeReduction.lean`), via two new
   lemmas `handleBlock_moveToEnd` (swap + rotate carries a block past any word) and
   `flatMap_handleBlock_perm` (any permutation of blocks). `#print axioms` →
   `[propext, Classical.choice, Quot.sound]`.
3. **Blueprint**: 22 `\lean{}` pointers went dangling with the retirements (and 3 were already
   dangling before this branch). All 25 fixed — re-pointed where a genuine successor exists
   (`thm:period-lattice` → `genuinePeriodLattice`; `lem:aj-path-independence` →
   `pathIntegralFunctionalU_sub_mem`, now actually proved; injectivity → `…injectiveU`;
   trace identity → `…U`), otherwise one honest sentence added and `\lean`/`\leanok` removed.
   Checked: every `\lean{}` name in `tex/` resolves in the compiled `Jacobian` environment.
   All 19 block edits logged in `ref/plain-english-changes.md` §3–21.
4. Kept, true, unreachable, still open: gaps 11, 12, 13 (`Periods/Hurewicz.lean`).

### Builds and counts

`lake build Jacobian` and `lake build Jacobian.Solution`: **green**.
Engine sorry declarations: **25 → 15** (−7 retired false gaps 5,6,8,9,10,16,17; −1 gap 14;
−1 gap 7 proved). *(Corrected: the commit message of 3492fa3 says 14; the build says 15.)*

---

## 2026-10-27 — goal (e): degree fallback lemma; comparator; `genus` axiom-clean

### What changed

1. **`ContMDiff.exists_branchedCoverData`** (`Solution.lean`): for nonconstant `f` a
   ramification-compatible `BranchedCoverData` exists (built from `f` itself, all inputs
   derived from `ContMDiff`). **`ContMDiff.degree_eq_branchedDegree`**: for nonconstant `f`,
   `degree = branchedDegree hbc` for *any* compatible datum. Docstring states exactly when
   each branch of `degree` fires: constant ↦ `0` (intended), nonconstant ↦ weighted fibre
   count; the two inner `else 0` branches are unreachable (`Y` connected; this lemma).
   Both `#print axioms` → `[propext, Classical.choice, Quot.sound]`. **Gap 22 closed.**
2. **`genus`** is now `Module.finrank ℂ (HolomorphicOneForm ℂ X)` directly (definitionally
   `analyticGenus ℂ X`), so its value no longer depends on the finiteness proof:
   `#print axioms genus` → clean (was `sorryAx`). Comparator statements unaffected.
3. **Comparator.** Built the official comparator. HEAD now targets Lean v4.35 and its
   `lean4export` rejects v4.31 oleans (`incompatible header`) — CI would hit this too.
   Pinned to `leanprover/comparator@3afea23` (last commit on `v4.31.0-rc1`), also in
   `.github/workflows/comparator-smoketest.yml`. Results:
   * `scripts/mini-comparator.sh`: ALL MATCH (11/11).
   * `comparator/jacobian-smoketest.json`: **pass** — "Lean default kernel accepts the
     solution. Your solution is okay!"
   * `comparator/jacobian.json` (strict): **fail** — `Illegal axiom detected: 'sorryAx'`
     (expected: classical inputs and gaps remain).
4. Classical inputs relabelled in code with references (C1–C5); `ref/axiom-audit.md` §0 added
   (classical inputs table, labelled gaps table, retirements).

### `#print axioms` on the public API

`genus`, `ContMDiff.degree`: **clean**. All other public declarations: `sorryAx` (through
C1–C5 and the labelled gaps).

---

## 2026-10-27 — final sweep for placeholders of the same classes

Declaration-level check (fixed dependency graph, private/aux included) of every
placeholder-shaped declaration still in the live tree against the set reachable from the
public API: **0 reachable**. What remains, all unreachable, all ledgered:

| class | where | count |
|---|---|---|
| `opaque` | `AbelJacobi/AnalyticOfCurveBasis.lean` (Type-0 `pathIntegralFunctionalBundle`), `Periods/Polygon4gCellular.lean` (3 group placeholders) | 4 |
| `… : True := trivial` "theorems" | mostly `HolomorphicForms/CompactRiemannSurface.lean` (19), spread over the Type-0 / polygon layers | 218 |
| `Unit` / `Nonempty Unit` / `PUnit` fields and statements | `AbelJacobi/AnalyticOfCurveBasis.lean`, `Periods/DualGraphCut.lean`, `Periods/RadoTriangulation.lean`, `Periods/SingularH1Homotopy.lean`, `Periods/Orientable.lean`, `Periods/SurfaceClassificationData.lean` | ~25 |
| zero placeholders | Type-0 `periodPairing` (`Periods/PeriodFunctional.lean`), `exteriorDerivative := 0` (`HolomorphicForms/SmoothDifferentialForm.lean`), Stokes `0 = 0` (`Blueprint/Sec03/StokesOnRSWithBoundary.lean`) | 3 |

They are dead weight rather than a soundness problem for the public API; a later pass
could retire the whole Type-0 mirror layer and the polygon tower to `Attic/`.

---

## 2026-10-28 — every labelled gap on the public path closed

Four commits (`c1bbbf6`, `268fb9f`, `eac1735`, and this one). After them the only `sorry`s
reachable from the public API are the five named classical inputs C1–C5.

### What changed

1. **Chart chains** (`Periods/ChartChain.lean`, new, axiom-clean). The chart reading
   `chartForm p ω` of a holomorphic 1-form is holomorphic on the chart target, and on any
   ball inside it the form is exact (Mathlib's Poincaré lemma; a one-variable holomorphic
   form is closed). A chart chain is a list of segments, each inside a ball in one chart,
   glued end to end; integrals are additive and linear in the form; a connected surface is
   chain-connected (`exists_chain`). The period lattice and the Abel–Jacobi integral now run
   on chart chains, so the `C¹`-path gap **`exists_isC1Path` is gone** (not needed).
2. **Abel–Jacobi holomorphy** — `analyticOfCurve_contMDiffU` **proved**: near `Q₀`, the map
   is `[v₀ + G(chart Q)]` with `G` the vector of local primitives.
3. **Pushforward preserves periods** — `pushforwardTraceLift_preserves_latticeU` **proved**
   (`Periods/ChainPushforward.lean`, new): chain rule in charts for `f^*`, local change of
   variables on balls, Lebesgue-number subdivision; every chain `l` of `X` has an image chain
   `l'` of `Y` with `∫_{l'} η = ∫_l f^*η` for all `η`.
4. **Removable singularities on a surface** — `meromorphic_no_poles_holomorphic_representative`
   **proved** (the normal-form value is the punctured limit, hence chart-independent). The
   genus-zero route now uses classical input C5 directly; gap 19 is off the public path.
5. **Trace extends across branch values** — `traceForm_extension_per_BCD` **proved**
   (`HolomorphicForms/TraceLocal.lean`, new). Near any `y₀`, in the chart at `y₀`, the
   trace is the derivative of `Tr H(w) = Σ_{x' ∈ f⁻¹(w)} m(x') H_x(x')`, the multiplicity-
   weighted fibre sum of local primitives `H_x` on disjoint coordinate balls around the
   fibre points of `y₀`. `Tr H` is holomorphic off `y₀` (inverse branches at unramified
   points) and continuous at `y₀` (the fibre collapses onto the fibre of `y₀`), so holomorphic
   on the whole ball by Riemann's removable-singularity theorem. The global form
   `traceHolomorphicForm` is the fibre sum at unramified values and `d(Tr H)` at branch
   values; its section is read through the cotangent trivialization at each point (no
   global frame, no chart stability). `traceFormsBundled_eq_traceHolomorphicForm` ties it
   to the existing linear trace map. Constant `f`: no value is regular, `τ = 0`.
6. **Pullback preserves periods** — `traceDualPullbackLift_preserves_latticeU` **proved**
   (`TraceDegree/TracePeriods.lean`, new), *without lifting curves*. Fix `x₀ ∈ X` and chosen
   chains from `x₀`; let `Φ(y) = Σ_{f x' = y} m(x') · (∫_{x₀}^{x'} ω_j)_j`. For every chain
   `l` from `P` to `Q` in `Y`, `(∫_l Tr ω_j)_j − (Φ(Q) − Φ(P))` is a period of `X`:
   locally `∫ Tr ω` is a difference of `Tr H`, `H_x(x') ≡ ∫_{x₀}^{x'} − ∫_{x₀}^{x}` mod
   periods, and the fibre points in each ball number `m(x)` with multiplicity at every
   point of the ball (`sum_order_S`), so `Tr H − Φ` is constant mod periods. A loop gives a
   period.

### Builds and counts

`lake build Jacobian`: **green** (4354 jobs). `lake build Jacobian.Solution`: green.

| metric | after (e) | now |
|---|---|---|
| engine sorry declarations (whole `Jacobian`, excl. `Challenge.lean`) | 15 | **9** |
| reachable from the public API (decl-level graph, private/aux included) | 11 | **5** (= C1–C5) |
| custom axioms | 0 | 0 |

The 9: C1–C5 (reachable), gap 19 `complexSimplePolePrincipalPart_of_biholomorph_onePoint`
and gaps 11–13 in `Periods/Hurewicz.lean` (true, **unreachable**). The new files are
axiom-clean (`#print axioms traceHolomorphicForm`, `traceDualPullbackLift_genuinePeriods`,
`traceFormsBundled_eq_traceHolomorphicForm` → `[propext, Classical.choice, Quot.sound]`).

### Public API: which classical inputs each declaration rests on

| declaration | inputs |
|---|---|
| `genus`, `ContMDiff.degree` | none (axiom-clean) |
| `Jacobian` and its instances, `ofCurve`, `pushforward`, `pullback`, `ofCurve_self`, `ofCurve_contMDiff`, `pushforward_contMDiff`, `pullback_contMDiff`, `pushforward_id_apply`, `pushforward_comp_apply`, `pullback_id_apply`, `pullback_comp_apply`, `pushforward_pullback` | C1 (finite-dimensionality), C2 (lattice discreteness/fullness) |
| `ofCurve_inj` | C1, C2, C3 (Abel) |
| `genus_eq_zero_iff_homeo` | C1, C4, C5 (genus-0 uniformization) |

### Comparator

* `comparator/jacobian-smoketest.json`: **pass** ("Lean default kernel accepts the solution.
  Your solution is okay!").
* `comparator/jacobian.json` (strict): **fail**, `Illegal axiom detected: 'sorryAx'` — from
  C1–C5 only.

### Plain-English blocks

None touched in this round (no `tex/` edits; the closed gaps had no `\lean{}` pointers).

---

## 2026-10-28 — cleanup pass: unused placeholders and dead code dropped

Owner request: drop the placeholders if unused, and a general cleanup.

### Rule

Keep = everything the public API (`Jacobian/Solution.lean`) depends on, plus everything a
blueprint `\lean{}` pointer depends on, **minus** anything built on a placeholder.
Placeholders (found in the compiled environment, not by grep): 270 theorems whose
statement is `True`, 4 `opaque`s, 17 definitions whose value is `Unit`/`PUnit`/`True`-typed,
8 definitions whose value is `0` (`exteriorDerivative`, `dStarOperator1/2`,
`integrateOneFormBoundary`, `integrateTwoForm`, the Type-0 meromorphic `zeros`/`poles`, …), and
two `witness : Unit` structures. Removed = the placeholders, every declaration depending on
one (they are vacuous too), every module with nothing kept, and whatever depended on those
modules. None of it was reachable from the public API (checked on the declaration graph
before deleting).

### What changed

* **384 Lean files deleted** (the Type-0 mirror layer `AnalyticJacobian/*`, the Type-0
  Abel/period/push-pull chains, the polygon/cellular/prism tower, the de Rham/Hodge
  surrogates, Stokes `0 = 0`, …), plus 6 files that no build imported (never compiled:
  `HarmonicConjugate`, `HarmonicDipole`, `CMfldBumpStub`, `ChartOverlapDerivContinuous`,
  `IntegralOneCycleU`, `SingularChainComplexZU`).
* **Surviving files trimmed** by declaration source range (Lean's recorded ranges, with
  docstrings and `omit … in` prefixes): `Periods/Hurewicz.lean` (−2.5k lines),
  `HolomorphicForms/CompactRiemannSurface.lean` (−1.3k, including its 19 `True` lemmas),
  `GenusZeroClassification`, `AnalyticOfCurveBasis` (Unit-witness Abel scaffold,
  `PathIntegralFunctionalBundle` and its zero `Inhabited` witness),
  `MeromorphicToBranchedCover`, `PeriodHomologyInvariance`, `AnalyticDegree`, and three
  small ones. Orphaned "retained docstring" comment blocks removed.
* **Imports**: imports of deleted modules replaced by the surviving modules they provided,
  then every import implied by another import of the same file dropped (485 lines).
  Empty umbrellas `Jacobian/AbelJacobi.lean`, `Jacobian/AnalyticJacobian.lean` deleted.
* README-only plan directories `Jacobian/Analysis/`, `Jacobian/StageA/`, `Jacobian/StageB/`
  deleted (they described build targets that do not exist and a tex section 12 that is
  not in `tex/`); one-off script `scripts/apply_jc2_proof.py` (patched a deleted file)
  deleted. `Attic/` and `sorries.jsonl` (the owner's tracker) left as they are.
* **Blueprint**: 6 `\lean{}` pointers targeted removed declarations; 10 edits in
  `tex/sections/06-…` and `08-…` (pointer moved to the live classical input C3, or
  `\lean`/`\leanok` dropped with one sentence saying why), logged in
  `ref/plain-english-changes.md` §22–31. All 93 `\lean{}` names resolve.

### Builds and counts

`lake build Jacobian`: **green** (3975 jobs, was 4354).

| metric | before | after |
|---|---|---|
| Lean files under `Jacobian/` | 512 | **128** |
| lines | ~76k | **36.5k** |
| placeholder declarations (`True` statements, `opaque`, `Unit`/`0` values) | 301 | **0** |
| engine `sorry` declarations | 9 | 9 |
| reachable from the public API | 5 (C1–C5) | 5 (C1–C5) |

The public API is untouched (same 911 reachable declarations). The four unreachable gaps
(19; 11–13 in `Hurewicz.lean`) remain because blueprint pointers depend on them.

---

## 2026-10-28 — C1 proved: holomorphic 1-forms are finite-dimensional

`HolomorphicForms/Finiteness.lean` (new, axiom-clean): the Montel–Riesz argument.
Finitely many chart discs `K_i = closedBall(z_i, r_i)` whose interiors cover `X`, with
`closedBall(z_i, 3r_i)` inside the chart target; coefficients `a_i(ω) = chartForm p_i ω · 1`.

* `chartForm_transition` / `chartCoeff_transition`: readings in two charts differ by the
  derivative of the transition map.
* `exists_discCoeffs_bound`: `sup_{L} |a| ≤ C · sup_{K} |a|` (`L_i` = radius `2r_i`); the
  transition derivative is bounded on the compact sets `c_i⁻¹(L_i) ∩ c_j⁻¹(K_j)`.
* `chartCoeff_lipschitz`: Cauchy estimate ⇒ uniformly Lipschitz on `K_i`.
* `finiteDimensional_holomorphicOneForm`: Arzelà–Ascoli + Tychonoff give a totally bounded
  ball in the image of `ω ↦ (a_i(ω)|K_i)_i`; Riesz (`of_totallyBounded_nhds_zero`, no
  completeness needed) makes the image finite-dimensional; the map is injective.

`compactRiemannSurface_finiteDimensionalHolomorphicOneForms_frontier` now delegates to it.
Reachable `sorry`s: **4** (C2–C5).

---

## 2026-10-28 — C2 split; the spanning half proved

* `Periods/RealPeriods.lean` (new, axiom-clean): `eq_zero_of_re_chainIntegral_eq` — a
  holomorphic 1-form whose chain integrals have path-independent real part is zero.
  `u = Re ∫_{P₀} ω` is continuous (locally `u(Q₀) + Re H`), attains its maximum; at a maximum
  `exp ∘ H` has maximal modulus at the centre of a chart ball, so it is constant there
  (Mathlib's maximum modulus principle); the set of maximum points is clopen, so `H' = 0`
  everywhere and every chart coefficient vanishes.
* `periodLattice_span` (proved): a real functional `φ` killing all periods is
  `Re Σ c_j v_j`; `Σ c_j ω_j` then satisfies the lemma, so `c = 0`, `φ = 0`.
* The classical input is narrowed to `periodLattice_discrete`;
  `periodLattice_discrete_and_span` is now assembled from the two.

---

## 2026-10-28 — "homeomorphic to S² ⇒ genus 0" without uniformization; C4 removed

`Periods/PrimitiveCovering.lean` (new, axiom-clean):

* `IsPrim`, `hasFDerivAt_chartChange`, `exists_isPrim`, `IsPrim.eventually_sub_eq`: local
  primitives of a holomorphic form, chart-independent, locally unique up to constants.
* `PrimSpace ω` (`X × ℂ` topologised by graphs of local primitives) and
  `isCoveringMap_primProj`: the étalé space of primitives is a covering space (explicit
  trivialisations `trivOfPrim` with discrete fibre `ℂ`).
* `exists_isPrim_of_simplyConnected`: Mathlib's lifting theorem for covering maps gives a
  primitive on any simply connected open set.
* `IsPrim.segment_integral` / `IsPrim.chainIntegral_eq`: chain integrals inside the domain of
  a primitive are differences of the primitive (convex thickening of the segment).
* `interior_segment_complex`, `exists_not_mem_segments`: finitely many chart segments miss a
  point (Baire).
* `simplyConnectedSpace_compl_of_homeomorph_sphere`: `X ∖ {z} ≅ S² ∖ {pt} ≅ ℝ²`
  (Mathlib's stereographic projection), hence simply connected.
* `holomorphicOneForm_eq_zero_of_homeomorph_sphere`: any two chains miss a common point, so
  their integrals agree, so `ω = 0` by `eq_zero_of_re_chainIntegral_eq`.

`analyticGenus_eq_zero_of_homeomorphic_sphere`, `holomorphicOneForm_linearEquiv_of_homeoSphere_exists`
and `holomorphicOneForm_linearEquiv_of_biholo_to_OnePointCx` are re-proved from it. The
classical input C4 (genus-zero uniformization) and the ten declarations that only it
supported are removed. Blueprint: 3 edits in `04-…` (logged §32–34).

Reachable `sorry`s: **3** — C2 (discreteness), C3 (Abel), C5 (analytic genus 0 ⇒ `ℂ̂`).

---

## Commit hashes

| time (EDT) | hash | summary |
|---|---|---|
| 2026-10-27 17:3x | `40f287b` | refutation theorem + classification (previous session) |
| 2026-10-27 17:34 | `03b303b` | EvalAtOneHelper frame assumption (previous session; did not build) |
| 2026-10-27 20:4x | `f48acda` | goal (a): `StableChartAt` deleted (author shows "Claude": committed before the identity fix; amending needs a force-push, which was not permitted) |
| 2026-10-27 | `839601f` | goals (b), (c): genuine period lattice and Abel–Jacobi map |
| 2026-10-27 | `3492fa3` | goal (d): false gaps retired, gap 7 proved |
| 2026-10-27 | `cec6833` | goal (e): degree fallback lemma; comparator pinned; `genus` clean |
| 2026-10-27 | `219e033` | ledger the remaining unreachable placeholders |
| 2026-10-28 | `c1bbbf6` | chart chains; Abel–Jacobi holomorphy proved |
| 2026-10-28 | `268fb9f` | pushforward preserves the period lattice |
| 2026-10-28 | `eac1735` | removable singularities on surfaces; genus-zero short-circuit |
| 2026-10-28 | `99ce6d7` | trace extends across branch values; pullback preserves the period lattice |
