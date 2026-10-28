import Jacobian.HolomorphicForms.SmoothDifferentialForm
import Jacobian.HolomorphicForms.DeRhamCohomology
import Jacobian.HolomorphicForms.RealComplexDeRham
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Bridge between de Rham cohomology dimensions and the explicit complex

`Jacobian/HolomorphicForms/DeRhamCohomology.lean` now exposes
`complexDimDeRhamH1ℂ X : ℕ` as the finrank of the explicit quotient:
H¹_dR is closed 1-forms modulo exact 1-forms.

## What this file provides

* `complexDimDeRhamH1ℂ_eq_finrank_cocycle` — definitional bridge from the
  dimension symbol to the explicit quotient model.

## TOPDOWN role

This file keeps the previous bridge name available for downstream
assembly files.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

/--
`complexDimDeRhamH1ℂ X` is definitionally the ℂ-finrank of the
explicit closed-mod-exact quotient model.
-/
theorem complexDimDeRhamH1ℂ_eq_finrank_cocycle
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    complexDimDeRhamH1ℂ X = Module.finrank ℂ (deRhamH1Cocycle X) := by
  rfl


theorem realDimDeRhamH1_eq_finrank_cocycleℝ
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    realDimDeRhamH1 X = Module.finrank ℂ (deRhamH1Cocycle X) := by
  rw [realDim_deRhamH1_eq_complexDim_deRhamH1ℂ X,
      complexDimDeRhamH1ℂ_eq_finrank_cocycle X]

end JacobianChallenge.HolomorphicForms
