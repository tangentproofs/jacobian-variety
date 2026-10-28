import Jacobian.AnalyticJacobian.MkOps
import Jacobian.HolomorphicForms.EvalLinearMap
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Extensionality, surjectivity, and `evalLinearMap` lift for `mk`

Continues `MkOps` with surjectivity of the quotient projection,
extensionality through cosets, and a `mk ∘ evalLinearMap` lift that
sends `(x, v)` directly to a class in the analytic Jacobian.
-/

namespace JacobianChallenge.AnalyticJacobian

open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
  [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/-- `mk` is surjective. -/
theorem mk_surjective : Function.Surjective (mk E X) :=
  Quot.mk_surjective

/--
Two functionals project to the same Jacobian class iff their
difference lies in the period subgroup.
-/
theorem mk_eq_mk_iff (φ ψ : HolomorphicOneForm E X →ₗ[ℂ] ℂ) :
    mk E X φ = mk E X ψ ↔ -φ + ψ ∈ periodSubgroup E X :=
  QuotientAddGroup.eq

/--
Concrete witness lift: a point/vector pair determines a Jacobian
class via `mk ∘ evalLinearMap`. Concretely:
`evalJacobianClass x v` is the analytic Jacobian class of the
ℂ-linear functional `η ↦ η.toFun x v`.
-/
noncomputable def evalJacobianClass
    (x : X) (v : E) : AnalyticJacobianGroup E X :=
  mk E X (evalLinearMap x v)

@[simp] theorem evalJacobianClass_def (x : X) (v : E) :
    evalJacobianClass (E := E) (X := X) x v =
      mk E X (evalLinearMap x v) := rfl

end JacobianChallenge.AnalyticJacobian
