import Jacobian.AbelJacobi.WitnessMkPeriodPairing
import Jacobian.Periods.PeriodSubgroupApi
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Characterizations of `witnessAbelJacobi … = 0`

Several iff/of-form characterizations of when the witness vanishes,
by combining the existing `_eq_zero_iff_endpoint_diff_mem` with
`mem_periodSubgroup_iff` (cycle witness) and the
`evalJacobianClass`-difference shape.
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
Witness is zero iff the endpoint `evalLinearMap` difference is
the `periodPairing` image of some integer 1-cycle.
-/
theorem witnessAbelJacobi_eq_zero_iff_exists_cycle
    (basePoint P : X) (v : E) :
    witnessAbelJacobi (E := E) (X := X) basePoint P v = 0 ↔
      ∃ σ : IntegralOneCycle X,
        periodPairing E X σ = evalLinearMap P v - evalLinearMap basePoint v := by
  rw [witnessAbelJacobi_eq_zero_iff_endpoint_diff_mem,
      mem_periodSubgroup_iff]

/--
Sufficient condition: if the endpoint diff equals some
`periodPairing E X σ`, the witness vanishes.
-/
theorem witnessAbelJacobi_eq_zero_of_endpoint_diff_eq_periodPairing
    (basePoint P : X) (v : E) (σ : IntegralOneCycle X)
    (h : evalLinearMap P v - evalLinearMap basePoint v = periodPairing E X σ) :
    witnessAbelJacobi (E := E) (X := X) basePoint P v = 0 := by
  rw [witnessAbelJacobi_eq_mk_sub, h, mk_periodPairing_eq_zero]

/-- Witness is zero iff the two endpoint Jacobian classes agree. -/
theorem witnessAbelJacobi_eq_zero_iff_evalJacobianClass_eq
    (basePoint P : X) (v : E) :
    witnessAbelJacobi (E := E) (X := X) basePoint P v = 0 ↔
      evalJacobianClass (E := E) (X := X) P v =
        evalJacobianClass basePoint v := by
  unfold witnessAbelJacobi
  exact sub_eq_zero

/--
Sufficient condition: equal endpoint Jacobian classes ⇒ witness
vanishes.
-/
theorem witnessAbelJacobi_eq_zero_of_evalJacobianClass_eq
    (basePoint P : X) (v : E)
    (h : evalJacobianClass (E := E) (X := X) P v =
        evalJacobianClass basePoint v) :
    witnessAbelJacobi (E := E) (X := X) basePoint P v = 0 :=
  (witnessAbelJacobi_eq_zero_iff_evalJacobianClass_eq basePoint P v).mpr h

end JacobianChallenge.AbelJacobi
