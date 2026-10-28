import Jacobian.TraceDegree.PullbackFormsLinearMapApply
import Jacobian.TraceDegree.PullbackFormsLinearMapSmul

/-!
# Integer-scalar form-slot linearity for bundled `pullbackFormsLinearMap`

`pullbackFormsLinearMap` is a `HolomorphicOneForm →ₗ[ℂ] _`-bundled
LinearMap, so it commutes with `ℕ`- and `ℤ`-scalar multiplication
on the form. Function-level + bundled vec-applied facade lemmas.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace E X]
  [TopologicalSpace Y] [ChartedSpace E Y]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) Y]

/-- Bundled pullback distributes over `ℕ`-scalar form mult. -/
theorem pullbackFormsLinearMap_nsmul
    (f : X → Y) (n : ℕ) (η : HolomorphicOneForm E Y) :
    pullbackFormsLinearMap f (n • η) =
      n • pullbackFormsLinearMap f η :=
  (pullbackFormsLinearMap (E := E) f).toAddMonoidHom.map_nsmul n η

/-- Bundled pullback distributes over `ℤ`-scalar form mult. -/
theorem pullbackFormsLinearMap_zsmul
    (f : X → Y) (n : ℤ) (η : HolomorphicOneForm E Y) :
    pullbackFormsLinearMap f (n • η) =
      n • pullbackFormsLinearMap f η :=
  (pullbackFormsLinearMap (E := E) f).toAddMonoidHom.map_zsmul n η

/-- At-point + vec-applied: bundled pullback `ℕ`-smul. -/
theorem pullbackFormsLinearMap_nsmul_apply_vec
    (f : X → Y) (n : ℕ) (η : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsLinearMap f (n • η) x v =
      n • pullbackFormsLinearMap f η x v := by
  rw [pullbackFormsLinearMap_nsmul]; rfl

/-- At-point + vec-applied: bundled pullback `ℤ`-smul. -/
theorem pullbackFormsLinearMap_zsmul_apply_vec
    (f : X → Y) (n : ℤ) (η : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsLinearMap f (n • η) x v =
      n • pullbackFormsLinearMap f η x v := by
  rw [pullbackFormsLinearMap_zsmul]; rfl

end JacobianChallenge.TraceDegree
