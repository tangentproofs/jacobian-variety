import Jacobian.AnalyticJacobian.EvalJacobianClassZero
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Non-triviality witness for `AnalyticJacobianGroup`

If a witness `(x, v, η)` produces an `evalLinearMap` value *outside*
the period subgroup, the analytic Jacobian quotient is `Nontrivial`
— the corresponding `evalJacobianClass` is a non-zero class.
-/

namespace JacobianChallenge.AnalyticJacobian

open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
  [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/--
A witness `(x, v)` whose `evalLinearMap` value is outside the
period subgroup produces a non-zero analytic Jacobian class.
-/
theorem evalJacobianClass_ne_zero
    (x : X) (v : E) (h : evalLinearMap x v ∉ periodSubgroup E X) :
    evalJacobianClass (E := E) (X := X) x v ≠ 0 :=
  fun heq => h ((evalJacobianClass_eq_zero_iff x v).mp heq)

/-- Such a witness produces a `Nontrivial` instance. -/
theorem nontrivial_analyticJacobianGroup_of_evalLinearMap_ne_periodSubgroup
    (x : X) (v : E) (h : evalLinearMap x v ∉ periodSubgroup E X) :
    Nontrivial (AnalyticJacobianGroup E X) :=
  ⟨evalJacobianClass x v, 0, evalJacobianClass_ne_zero x v h⟩

/--
Sufficient condition specialized via `evalLinearMap` values: the
contrapositive of `evalJacobianClass_eq_zero_iff`.
-/
theorem evalLinearMap_notMem_of_evalJacobianClass_ne_zero
    (x : X) (v : E)
    (h : evalJacobianClass (E := E) (X := X) x v ≠ 0) :
    evalLinearMap x v ∉ periodSubgroup E X :=
  fun hin => h ((evalJacobianClass_eq_zero_iff x v).mpr hin)

/--
Contrapositive criterion: any non-zero analytic Jacobian
witness rules out membership in `periodSubgroup`.
-/
theorem evalLinearMap_notMem_iff_evalJacobianClass_ne_zero
    (x : X) (v : E) :
    evalLinearMap x v ∉ periodSubgroup E X ↔
      evalJacobianClass (E := E) (X := X) x v ≠ 0 :=
  ⟨evalJacobianClass_ne_zero x v, evalLinearMap_notMem_of_evalJacobianClass_ne_zero x v⟩

end JacobianChallenge.AnalyticJacobian
