import Jacobian.AnalyticJacobian.MkPeriodPairingSmul
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# `mk` ∘ `periodPairing` on cycle-arithmetic combinations

Continues `MkPeriodPairing(Smul)` with cycle-side arithmetic. Each
lemma combines `periodPairing_{add,sub}` with the existing
`mk_periodPairing_eq_zero` trivialization.
-/

namespace JacobianChallenge.AnalyticJacobian

open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
  [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/-- `mk` of `periodPairing (σ + τ)` is `0`. -/
@[simp] theorem mk_periodPairing_add_cycle
    (σ τ : IntegralOneCycle X) :
    mk E X (periodPairing E X (σ + τ)) = 0 :=
  mk_periodPairing_eq_zero (σ + τ)

/-- `mk` of `periodPairing (σ - τ)` is `0`. -/
@[simp] theorem mk_periodPairing_sub_cycle
    (σ τ : IntegralOneCycle X) :
    mk E X (periodPairing E X (σ - τ)) = 0 :=
  mk_periodPairing_eq_zero (σ - τ)

/--
`mk` of the sum of two `periodPairing` images is `0`. Proof via
`periodPairing_add` and `mk_periodPairing_eq_zero`.
-/
@[simp] theorem mk_periodPairing_add_periodPairing
    (σ τ : IntegralOneCycle X) :
    mk E X (periodPairing E X σ + periodPairing E X τ) = 0 := by
  rw [← periodPairing_add, mk_periodPairing_eq_zero]

/--
`mk` of the difference of two `periodPairing` images is `0`. Proof
via `periodPairing_sub` and `mk_periodPairing_eq_zero`.
-/
@[simp] theorem mk_periodPairing_sub_periodPairing
    (σ τ : IntegralOneCycle X) :
    mk E X (periodPairing E X σ - periodPairing E X τ) = 0 := by
  rw [← periodPairing_sub, mk_periodPairing_eq_zero]

end JacobianChallenge.AnalyticJacobian
