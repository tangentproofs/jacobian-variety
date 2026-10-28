import Jacobian.HolomorphicForms.EvalLinearMapVec

/-!
# Sub/nsmul/zsmul on the tangent-vector slot of `evalLinearMap`

Companion to `EvalLinearMapVec`: closes out subtraction and integer
scalar multiplication in the vector slot, plus a small toFun-side
distributive lemma.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

@[simp] theorem evalLinearMap_sub_vec
    (x : X) (v w : E) (η : HolomorphicOneForm E X) :
    evalLinearMap x (v - w) η = evalLinearMap x v η - evalLinearMap x w η := by
  rw [evalLinearMap_apply, evalLinearMap_apply, evalLinearMap_apply]
  exact (η.toFun x).map_sub v w

@[simp] theorem evalLinearMap_nsmul_vec
    (x : X) (n : ℕ) (v : E) (η : HolomorphicOneForm E X) :
    evalLinearMap x (n • v) η = n • evalLinearMap x v η := by
  induction n with
  | zero => rw [zero_smul, zero_smul, evalLinearMap_apply]; exact map_zero _
  | succ n ih => rw [succ_nsmul, succ_nsmul, evalLinearMap_add_vec, ih]

@[simp] theorem evalLinearMap_zsmul_vec
    (x : X) (n : ℤ) (v : E) (η : HolomorphicOneForm E X) :
    evalLinearMap x (n • v) η = n • evalLinearMap x v η := by
  rw [evalLinearMap_apply, evalLinearMap_apply]
  exact (η.toFun x).toLinearMap.toAddMonoidHom.map_zsmul n v

/-- Pointwise alias: applying the toFun to a sum vector. -/
theorem toFun_apply_add_vec
    (η : HolomorphicOneForm E X) (x : X) (v w : E) :
    η.toFun x (v + w) = η.toFun x v + η.toFun x w :=
  (η.toFun x).map_add v w

end JacobianChallenge.HolomorphicForms
