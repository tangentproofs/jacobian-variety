# Independent repair — progress log

Working log for `ref/independent-repair-brief.md`. Branch `independent-repair`, cut from
`rkirov-comparison` (84c7d95). **Local commits only — nothing pushed, no remote touched.**

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

## Commit hashes

| time (EDT) | hash | summary |
|---|---|---|
