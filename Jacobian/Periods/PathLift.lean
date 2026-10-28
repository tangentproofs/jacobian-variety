import Mathlib.Topology.Path
import Jacobian.HolomorphicForms.Defs
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic

/-!
# Lifting a path-on-`X` through a chart for integration

* `chartLift c γ h` — takes a `γ : Path (a b : X)` whose range is
  contained in `c.source`, and returns the chart-coordinate path
  `Path (c a) (c b)` in the model space `E`. Uses Mathlib's
  `Path.map'`, which already accepts `ContinuousOn f (range γ)` —
  so `c.continuousOn_toFun.mono h` is the only continuity input.

* `pathIntegralViaChart c ω γ h` — the from-`X` wrapper around
  `pathIntegralInChart`. Lifts the path through the chart and
  applies the chart-local integral.
-/

namespace JacobianChallenge.Periods

open Set
open JacobianChallenge.HolomorphicForms

/--
Lift a path that stays inside a chart's source to a path in
the model space.
-/
noncomputable def chartLift
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
    (c : OpenPartialHomeomorph X E)
    {a b : X} (γ : Path a b)
    (h : range γ ⊆ c.source) :
    Path (c a) (c b) :=
  γ.map' (c.continuousOn_toFun.mono h)


end JacobianChallenge.Periods
