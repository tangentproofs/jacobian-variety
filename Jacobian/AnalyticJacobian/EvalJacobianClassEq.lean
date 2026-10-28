import Jacobian.AnalyticJacobian.EvalJacobianClassPeriodPairing
import Jacobian.AnalyticJacobian.MkExt
import Jacobian.Periods.PeriodSubgroupApi
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Equality characterizations for `evalJacobianClass`

Two `evalJacobianClass` values agree iff their underlying
`evalLinearMap` representatives differ (up to sign) by an element of
`periodSubgroup` — equivalently, by a `periodPairing` value.
-/

namespace JacobianChallenge.AnalyticJacobian

open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
  [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/--
`evalJacobianClass P v = evalJacobianClass Q w` iff the difference
`-evalLinearMap P v + evalLinearMap Q w` lies in `periodSubgroup`.
-/
theorem evalJacobianClass_eq_iff_mem
    (P Q : X) (v w : E) :
    evalJacobianClass (E := E) (X := X) P v =
        evalJacobianClass Q w ↔
      -evalLinearMap P v + evalLinearMap Q w ∈ periodSubgroup E X := by
  unfold evalJacobianClass
  exact mk_eq_mk_iff _ _

/-- `evalJacobianClass` equality characterized by a witness 1-cycle. -/
theorem evalJacobianClass_eq_iff_exists_cycle
    (P Q : X) (v w : E) :
    evalJacobianClass (E := E) (X := X) P v =
        evalJacobianClass Q w ↔
      ∃ σ : IntegralOneCycle X,
        periodPairing E X σ = -evalLinearMap P v + evalLinearMap Q w := by
  rw [evalJacobianClass_eq_iff_mem, mem_periodSubgroup_iff]

/--
Sufficient condition: `evalJacobianClass P v = evalJacobianClass Q w`
when their representative difference equals `periodPairing E X σ`.
-/
theorem evalJacobianClass_eq_of_diff_eq_periodPairing
    (P Q : X) (v w : E) (σ : IntegralOneCycle X)
    (h : -evalLinearMap P v + evalLinearMap Q w = periodPairing E X σ) :
    evalJacobianClass (E := E) (X := X) P v =
        evalJacobianClass Q w := by
  rw [evalJacobianClass_eq_iff_mem, h]
  exact periodPairing_mem_periodSubgroup σ

/-- `evalJacobianClass x v = 0` iff `evalLinearMap x v ∈ periodSubgroup`. -/
theorem evalJacobianClass_eq_zero_iff_mem
    (x : X) (v : E) :
    evalJacobianClass (E := E) (X := X) x v = 0 ↔
      evalLinearMap x v ∈ periodSubgroup E X := by
  unfold evalJacobianClass
  exact mk_eq_zero_iff (evalLinearMap x v)

end JacobianChallenge.AnalyticJacobian
