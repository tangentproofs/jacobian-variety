import Jacobian.Periods.PathLift
import Jacobian.Periods.ChartLiftSymm
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- The from-`X` chart-local path integral over a constant path is `0`. -/
@[simp] theorem pathIntegralViaChart_refl
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X) (a : X)
    (h : range (Path.refl a) ⊆ c.source) :
    pathIntegralViaChart c ω (Path.refl a) h = 0 := by
  unfold pathIntegralViaChart chartLift
  convert pathIntegralInChart_refl c ω (c a) using 2

/-- The from-`X` chart-local path integral reverses sign under path symmetry. -/
theorem pathIntegralViaChart_symm
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b) (h : range γ ⊆ c.source)
    (h' : range γ.symm ⊆ c.source) :
    pathIntegralViaChart c ω γ.symm h' = - pathIntegralViaChart c ω γ h := by
  unfold pathIntegralViaChart
  rw [chartLift_symm c γ h h']
  exact pathIntegralInChart_symm c ω (chartLift c γ h)

end JacobianChallenge.Periods
