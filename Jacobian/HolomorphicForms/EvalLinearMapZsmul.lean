import Jacobian.HolomorphicForms.EvalLinearMapApi

/-!
# Integer-scalar `evalLinearMap` and a few smul-related extras

The ℤ-action variant of `evalLinearMap_smul`, plus a small extra
companion `nsmul_toFun_apply_vec_alt` and an `evalLinearMap_neg_neg`
collapse.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- `evalLinearMap` distributes over integer scalar multiplication. -/
theorem evalLinearMap_zsmul
    (x : X) (v : E) (n : ℤ) (η : HolomorphicOneForm E X) :
    evalLinearMap x v (n • η) = n • evalLinearMap x v η :=
  (evalLinearMap x v).toAddMonoidHom.map_zsmul n η

/-- `evalLinearMap` distributes over `Nat.cast • _`. -/
theorem evalLinearMap_natCast_smul
    (x : X) (v : E) (n : ℕ) (η : HolomorphicOneForm E X) :
    evalLinearMap x v ((n : ℤ) • η) = (n : ℤ) • evalLinearMap x v η :=
  evalLinearMap_zsmul x v n η

/-- Negation collapse. -/
theorem evalLinearMap_neg_neg
    (x : X) (v : E) (η : HolomorphicOneForm E X) :
    evalLinearMap x v (- -η) = evalLinearMap x v η := by
  rw [neg_neg]

/-- Integer-scalar variant of `nsmul_toFun_apply`. -/
theorem zsmul_toFun_apply
    (n : ℤ) (η : HolomorphicOneForm E X) (x : X) :
    (n • η).toFun x = n • (η.toFun x) := by
  change ((n • η : HolomorphicOneForm E X) : ∀ x, _) x =
    n • (η : ∀ x, _) x
  rw [ContMDiffSection.coe_zsmul]; rfl

end JacobianChallenge.HolomorphicForms
