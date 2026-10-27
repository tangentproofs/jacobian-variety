import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Chart stability is refutable on a compact connected charted space

This file records, as a theorem, *why* the project cannot assume that
`chartAt` is constant on the source of each chart.

The property in question is

```
∀ p : M, ∀ q ∈ (chartAt H p).source, chartAt H q = chartAt H p
```

which the project previously carried as a typeclass
(`JacobianChallenge.Periods.StableChartAt`) and supplied for a compact
connected Riemann surface by `sorry`. That instance can never be
supplied: `not_chartStable_of_compactSpace` below shows the property is
**false** for every compact connected space charted on `ℂ`, which is
exactly the class of spaces the Jacobian challenge is about.

The argument is elementary and uses nothing but the `ChartedSpace`
axioms:

1. If chart sources are stability classes, then `q ∈ (chartAt H p).source`
   forces `chartAt H q = chartAt H p` and hence equal sources. So any
   two chart sources are equal or disjoint, and each one is clopen
   (`chartStable_isClopen_source`).
2. Connectedness upgrades one chart source to all of `M`, so a single
   chart is a homeomorphism from `M` onto an open subset of `ℂ`.
3. Compactness makes that open subset compact, hence clopen in `ℂ`,
   hence all of `ℂ` by connectedness of `ℂ` — but `ℂ` is not compact.

Step 3 is where the contradiction bites, and it is not an artifact of
working over `ℂ`: the same proof refutes chart stability for any compact
connected space charted on a connected noncompact model.

Independently of this proof, Mathlib's own sphere atlas is a concrete
counterexample: `Mathlib/Geometry/Manifold/Instances/Sphere.lean` sets
`chartAt v := stereographic' n (-v)`, whose source is `{v}ᶜ`, so for
`w ∉ {v, -v}` we have `w ∈ (chartAt v).source` while
`chartAt w ≠ chartAt v`. The sphere is the very space named in the
challenge's `genus_eq_zero_iff_homeo`.
-/

namespace JacobianChallenge.Periods

open Set Topology

variable {H : Type*} [TopologicalSpace H]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/--
The chart-stability property: `chartAt H` is constant on the source of
each of its charts.

This is stated as a plain predicate rather than a typeclass on purpose —
see `not_chartStable_of_compactSpace`, which refutes it in the setting
the project cares about. Nothing in the project may assume it.
-/
def ChartStable (H : Type*) [TopologicalSpace H]
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] : Prop :=
  ∀ p : M, ∀ q ∈ (chartAt H p).source, chartAt H q = chartAt H p

/--
Under chart stability, distinct chart sources are disjoint, so every
chart source is closed as well as open.
-/
theorem chartStable_isClopen_source (hs : ChartStable H M) (p : M) :
    IsClopen (chartAt H p).source := by
  refine ⟨?_, (chartAt H p).open_source⟩
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro q hq
  refine ⟨(chartAt H q).source, ?_, (chartAt H q).open_source, mem_chart_source H q⟩
  intro r hr
  simp only [mem_compl_iff] at hq ⊢
  intro hrS
  -- `r` lies in both sources, so the two charts agree, so `q` lies in `p`'s source.
  have h1 : chartAt H r = chartAt H q := hs q r hr
  have h2 : chartAt H r = chartAt H p := hs p r hrS
  exact hq ((h1 ▸ h2 : chartAt H q = chartAt H p) ▸ mem_chart_source H q)

/--
Under chart stability, connectedness forces a single chart to be defined
on all of `M`.
-/
theorem chartStable_source_eq_univ [ConnectedSpace M] (hs : ChartStable H M) (p : M) :
    (chartAt H p).source = univ :=
  (chartStable_isClopen_source hs p).eq_univ ⟨p, mem_chart_source H p⟩

/--
**Chart stability is false on a compact connected space charted on `ℂ`.**

This is the refutation of the retired `StableChartAt` typeclass: the
hypothesis set `[CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]`
plus chart stability is contradictory, so every theorem proved under it
was vacuous.
-/
theorem not_chartStable_of_compactSpace
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] :
    ¬ ChartStable ℂ X := by
  intro hs
  obtain ⟨p⟩ := (inferInstance : Nonempty X)
  have hsrc : (chartAt ℂ p).source = univ := chartStable_source_eq_univ hs p
  -- The chart image is compact (image of all of the compact `X`) …
  have htgt : IsCompact (chartAt ℂ p).target := by
    rw [← (chartAt ℂ p).image_source_eq_target, hsrc]
    exact isCompact_univ.image_of_continuousOn
      (by simpa [hsrc] using (chartAt ℂ p).continuousOn)
  -- … and open, hence clopen, hence all of `ℂ` by connectedness.
  have hne : ((chartAt ℂ p).target).Nonempty :=
    ⟨chartAt ℂ p p, (chartAt ℂ p).map_source (mem_chart_source ℂ p)⟩
  have huniv : (chartAt ℂ p).target = univ :=
    (IsClopen.eq_univ ⟨htgt.isClosed, (chartAt ℂ p).open_target⟩ hne)
  -- But `ℂ` is not compact.
  exact NoncompactSpace.noncompact_univ (X := ℂ) (huniv ▸ htgt)

end JacobianChallenge.Periods
