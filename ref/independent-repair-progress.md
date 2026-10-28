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

## Commit hashes

| time (EDT) | hash | summary |
|---|---|---|
