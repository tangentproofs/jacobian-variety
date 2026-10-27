# Brief: independent repair of jacobian-variety

**For:** Claude Code session in tmux `jacobian-repair` on the shared box, cwd `/home/box/ver/JacobianChallenge`.
**Written:** 2026-10-27 (America/New_York) by Grok Bot for Michal Wallace.
**Decision behind it:** Michal chose the *stay independent* route. Do **not** port rkirov's code. You may read
`rkirov/jacobian-claude` for ideas, but copy no proofs, files or declarations from it.

Read first: `CLAUDE.md`, `ref/rkirov-gap-comparison.md` (the gap analysis; gap numbers below refer to it),
`ref/axiom-audit.md`, `ref/plan.md`, and the plain-English blueprint under `tex/` and `blueprint/`.

## 0. Git rules (hard)

1. You are on branch `independent-repair`, cut from `rkirov-comparison` (84c7d95). Stay on it.
2. Commit locally, in small reviewable commits. **Never push. Never merge to main. Never touch remotes.**
   The push URL is `DISABLED-no-push` on purpose. Leave it so.
3. `Jacobian/Challenge.lean` is the frozen spec. Do not change it in any way.
4. Clean up tmp files you create.

## 1. Goals, in order

**(a) Delete `StableChartAt`.** The instance `Jacobian/Solution.lean:37` is `sorry` and the class is
self-contradictory with `[CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]` (gap 21). About 120
files mention it, about 10 really use it. Remove the class and the instance. For each real use, replace it
with either an honest, *satisfiable* hypothesis (stated where it is used, visibly) or a genuine definition.
Every theorem that was only true because the context was contradictory must either be reproved honestly or
turned back into a clearly labelled gap (`sorry` with a `-- GAP:` comment and a ledger entry). Start by
producing `ref/stablechart-uses.md`: every mention, classified *real use* / *pass-through binder* /
*comment*, with file:line.

**(b) Make the period map a real definition.** Today the period pairing is the zero map
(`Periods/PeriodFunctionalU.lean:75,95`) so the lattice is `⊥` and the Jacobian is all of `ℂ^g`. Define
periods as integration of holomorphic 1-forms over a homology basis (cycles as piecewise-smooth loops, a
real line integral `∫ t in 0..1, ω(γ t)(γ' t)`), so that `Jacobian X = ℂ^g / Λ` with `Λ` the image of
`H₁(X, ℤ)`. Delete or rewrite the in-tree `…_eq_bot` lemma accordingly.

**(c) Make Abel–Jacobi a real definition.** `opaque pathIntegralFunctionalBundleU`
(`AbelJacobi/PathIntegralFunctionalU.lean:61-69`) has a spec satisfied by zero. Replace it with an actual
path integral from the base point, well defined modulo periods. No `opaque`, no spec-only definition.

**(d) The gaps that are false as stated.** Polygon tower gaps 5, 6, 8, 9, 10 and de Rham/Hodge gaps 16,
17. For each: if it is unreachable from `Jacobian.Solution` (check with a declaration-level dependency
sweep), retire it (delete, or move to a clearly marked `Attic/` that is not imported) and record that.
Otherwise give it a corrected, true statement.

**(e) Add the degree-fallback lemma** (gap 22, `Solution.lean:223-235`): show the `else 0` branch of
`ContMDiff.degree` is never taken where it matters (or state exactly when it is), so the fallback is not a
silent hack.

**Classical inputs.** Big classical results — Abel's theorem, Riemann–Roch, genus-0 uniformization,
discreteness/fullness of the period lattice — may stand as **named classical inputs**: a single, clearly
named `sorry`'d theorem each (never an `axiom`, never a typeclass, never a hidden binder), listed in a
"Classical inputs" table in `ref/axiom-audit.md` with its literature reference. Nothing else may be
assumed.

## 2. Honesty rules

- No smuggled hypotheses: no typeclass or binder whose only role is to make a proof go through.
- No vacuous definitions: no `:= 0`, `:= True`, `opaque`, or spec-only structure standing in for a real
  mathematical object.
- Label every conditional result in its docstring ("conditional on <classical input X>").
- Root-cause rule: for every root-cause fix, list the neighbouring cases of the same class (other zero
  placeholders, other contradictory instances, e.g. `d := 0` in `HolomorphicForms/SmoothDifferentialForm.lean:68-73`,
  the `0 = 0` Stokes in `Blueprint/Sec03/StokesOnRSWithBoundary.lean`) and fix or explicitly ledger them too.
- The strict check `comparator/jacobian.json` allows only `propext`, `Quot.sound`, `Classical.choice`.
  Sorries are expected for now; new axioms are forbidden.
- Prefer an honest `sorry` to a dishonest proof. Regressing the sorry count is fine and expected.

## 3. Michal's plain English

Preserve Michal's original plain-English blueprint text (`tex/`, `blueprint/`, docstrings) as much as
possible. When a statement changes, edit minimally and keep his voice. Keep
`ref/plain-english-changelog.md`: one entry per block touched — file:line, old text, new text, and why.

## 4. Builds (hard limits)

There is **no dedicated build machine** for this project. This box is shared; tcode is off limits.
Allowed:
- Install the pinned toolchain `leanprover/lean4:v4.31.0-rc1` with elan (a download).
- `lake exe cache get` for prebuilt Mathlib oleans (a download). If it fails, **stop and report**; never
  build Mathlib from source.
- Narrow single-module builds only, low priority and capped CPUs:
  `nice -n 19 taskset -c 0-2 lake build Jacobian.<Some.Module>`
  Pick the narrowest module that checks your edit.
Forbidden here: `lake build`, `lake build Jacobian`, `lake build Jacobian.Solution`, the comparator, and any
other whole-tree build. Record those as "pending build machine" in the progress file instead.
Grep/static analysis needs no build; use it freely.

## 5. Progress notes

Append to `ref/independent-repair-progress.md` at least after every commit and every hour: date/time
(America/New_York), what changed, commit hash, what was built and its result, sorry/axiom counts, next
step, blockers. Never claim something compiles unless you built it.

## 6. First milestone

1. `ref/stablechart-uses.md` (classification of every `StableChartAt` mention).
2. Toolchain + Mathlib cache in place; one narrow module containing a real use of `StableChartAt` built
   green *before* your edit, as a baseline.
3. First commit removing `StableChartAt` from one real-use cluster, with that module rebuilt.
Then continue down the goal list.
