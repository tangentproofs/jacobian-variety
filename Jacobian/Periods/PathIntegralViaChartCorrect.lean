import Jacobian.Periods.PathLift
import Jacobian.Periods.PathIntegralChartCorrect

namespace JacobianChallenge.Periods

open Set
open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/--
From-`X` corrected chart-local path integral: lift the path
through the chart and integrate using the genuine chart pullback.
-/
noncomputable def pathIntegralViaChartCorrect
    (c : OpenPartialHomeomorph X E)
    (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b)
    (h : range γ ⊆ c.source) : ℂ :=
  pathIntegralInChartCorrect c ω (chartLift c γ h)


end JacobianChallenge.Periods
