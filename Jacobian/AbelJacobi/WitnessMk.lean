import Jacobian.AbelJacobi.Specialize
import Jacobian.AnalyticJacobian.MkPeriodPairing
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# `witnessAbelJacobi` ↔ `mk` explicit-form bridges

Spells out `witnessAbelJacobi basePoint P v` in terms of the
quotient projection `mk`, plus a few periodPairing-invariance
corollaries.
-/

namespace JacobianChallenge.AbelJacobi

open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods
open JacobianChallenge.AnalyticJacobian

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
  [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/--
`witnessAbelJacobi` is the `mk`-image of the difference of
`evalLinearMap` values.
-/
theorem witnessAbelJacobi_eq_mk_sub
    (basePoint P : X) (v : E) :
    witnessAbelJacobi (E := E) (X := X) basePoint P v =
      mk E X (evalLinearMap P v - evalLinearMap basePoint v) := by
  unfold witnessAbelJacobi
  rw [evalJacobianClass_def, evalJacobianClass_def, ← mk_sub]

/--
Witness reformulated as `mk` of the difference of two
`evalJacobianClass` representatives.
-/
theorem witnessAbelJacobi_eq_mk_evalLinearMap_sub
    (basePoint P : X) (v : E) :
    witnessAbelJacobi (E := E) (X := X) basePoint P v =
      mk E X (evalLinearMap P v) - mk E X (evalLinearMap basePoint v) := by
  unfold witnessAbelJacobi
  rfl

/-- Witness factors through `mk` of an explicit difference. -/
theorem witnessAbelJacobi_eq_mk_neg_basePoint_add_endpoint
    (basePoint P : X) (v : E) :
    witnessAbelJacobi (E := E) (X := X) basePoint P v =
      mk E X (-evalLinearMap basePoint v + evalLinearMap P v) := by
  rw [witnessAbelJacobi_eq_mk_sub]
  congr 1
  abel

/--
Witness through `mk_eq_zero_iff`: vanishes iff endpoint diff lies
in the period subgroup.
-/
theorem witnessAbelJacobi_eq_zero_iff_endpoint_diff_mem
    (basePoint P : X) (v : E) :
    witnessAbelJacobi (E := E) (X := X) basePoint P v = 0 ↔
      evalLinearMap P v - evalLinearMap basePoint v ∈ periodSubgroup E X := by
  rw [witnessAbelJacobi_eq_mk_sub, mk_eq_zero_iff_mem_periodSubgroup]

end JacobianChallenge.AbelJacobi
