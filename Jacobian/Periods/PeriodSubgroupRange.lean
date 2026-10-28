import Jacobian.Periods.PeriodFunctional
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# `periodSubgroup` is the range of `periodPairing`

`periodSubgroup E X` is *defined* as `(periodPairing E X).range`,
so the equality is `rfl`. This file makes that statement available
as a named lemma for downstream rewrites.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
  [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/-- `periodSubgroup E X` equals `(periodPairing E X).range`. -/
theorem periodSubgroup_eq_range :
    periodSubgroup E X = (periodPairing E X).range :=
  rfl

end JacobianChallenge.Periods
