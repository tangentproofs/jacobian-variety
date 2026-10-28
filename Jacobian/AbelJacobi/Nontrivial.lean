import Jacobian.AbelJacobi.Coset
import Jacobian.AnalyticJacobian.NontrivialWitness
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Non-triviality criteria via `witnessAbelJacobi`

A witness `(basePoint, P, v)` whose `witnessAbelJacobi` is non-zero
forces `AnalyticJacobianGroup E X` to be `Nontrivial`. This gives an
Abel-Jacobi-style sufficient condition for non-trivial Jacobians.
-/

namespace JacobianChallenge.AbelJacobi

open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods
open JacobianChallenge.AnalyticJacobian

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
  [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/-- A non-zero witness produces a `Nontrivial` analytic Jacobian. -/
theorem nontrivial_analyticJacobian_of_witness_ne_zero
    (basePoint P : X) (v : E)
    (h : witnessAbelJacobi (E := E) (X := X) basePoint P v ≠ 0) :
    Nontrivial (AnalyticJacobianGroup E X) :=
  ⟨witnessAbelJacobi basePoint P v, 0, h⟩

/-- A non-zero witness implies the endpoint Jacobian classes differ. -/
theorem evalJacobianClass_ne_of_witness_ne_zero
    (basePoint P : X) (v : E)
    (h : witnessAbelJacobi (E := E) (X := X) basePoint P v ≠ 0) :
    evalJacobianClass P v ≠ evalJacobianClass basePoint v :=
  fun heq => h ((witnessAbelJacobi_eq_zero_iff_class_eq basePoint P v).mpr heq)

/--
A non-zero witness rules out `evalLinearMap`-equality (modulo
`periodSubgroup`).
-/
theorem evalLinearMap_diff_notMem_of_witness_ne_zero
    (basePoint P : X) (v : E)
    (h : witnessAbelJacobi (E := E) (X := X) basePoint P v ≠ 0) :
    -evalLinearMap P v + evalLinearMap basePoint v ∉ periodSubgroup E X := by
  intro hin
  apply h
  show evalJacobianClass P v - evalJacobianClass basePoint v = 0
  rw [sub_eq_zero]
  rw [evalJacobianClass_def, evalJacobianClass_def, mk_eq_mk_iff]
  exact hin

/--
Contrapositive: if all witnesses for the chosen base point vanish,
the analytic Jacobian is `Subsingleton` on the orbit visible to that
base point (formally just the existing zero-class characterization).
-/
theorem witness_zero_iff_evalJacobianClass_eq
    (basePoint P : X) (v : E) :
    witnessAbelJacobi (E := E) (X := X) basePoint P v = 0 ↔
      evalJacobianClass P v = evalJacobianClass basePoint v :=
  witnessAbelJacobi_eq_zero_iff_class_eq basePoint P v

end JacobianChallenge.AbelJacobi
