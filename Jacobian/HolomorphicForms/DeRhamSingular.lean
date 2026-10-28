import Jacobian.HolomorphicForms.DeRhamCohomology
import Jacobian.HolomorphicForms.RealSingularH1
import Jacobian.HolomorphicForms.DeRhamComparisonMap
import Jacobian.Periods.IntegralOneCycle
import Jacobian.Periods.RealHomologyTensor
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# De Rham theorem and singular bridge

The de Rham theorem identifies the de Rham cohomology of a smooth
manifold with the singular cohomology over ℝ:

H^k_dR(X, ℝ) ≅ H^k_sing(X, ℝ) = Hom_ℤ(H_k(X, ℤ), ℝ).

Combined with the universal-coefficient theorem (over ℝ, hence the
torsion in `H_{k-1}(X, ℤ)` does not appear), this links

dim_ℝ H¹_dR(X, ℝ) = rank_ℤ H₁(X, ℤ)

for any compact connected smooth manifold whose H₁ is finitely generated.

## Mathlib v4.28.0 status

ABSENT (de Rham complex on manifolds, de Rham theorem).
`Mathlib.AlgebraicTopology.SingularHomology.Basic` provides
`singularHomologyFunctor`, but no comparison map to a de Rham complex
exists — the project uses the resulting `IntegralOneCycle X` purely as
the integer-cycle module.

## What this file provides

## TOPDOWN role

This is the *de Rham side* of the rank chain. It is the first of two
named obligations (the other being the *Hodge side*) that the top-down
refinement of `hodge_deRham_rank_eq` delegates to.
-/

namespace JacobianChallenge.HolomorphicForms

open JacobianChallenge.Periods

open scoped Manifold


theorem realDim_deRhamH1_eq_realDim_singularH1
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    realDimDeRhamH1 X = realDimSingularH1 X :=
  realDimDeRhamH1_eq_realDimSingularH1_via_cocycle X

/--
Refinement direction: split into
`(a) IntegralOneCycle_finiteFree X : Module.Free ℤ (IntegralOneCycle X) ∧ Module.Finite ℤ _`
and
`(b) finrank_homℤℝ_of_free : ∀ M [Module.Free ℤ M] [Module.Finite ℤ M], Module.finrank ℝ (M →ₗ[ℤ] ℝ) = Module.finrank ℤ M`.
Both are pure linear-algebra obligations.  See `IntegralOneCycleRank.lean`.
-/
theorem realDim_singularH1_eq_finrank_intH1
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    realDimSingularH1 X = Module.finrank ℤ (IntegralOneCycle X) :=
  realDim_singularH1_eq_finrank_intH1_via_uct X

/--
This is the **de Rham side** of the top-level `hodge_deRham_rank_eq`
assembly.
-/
theorem realDim_deRhamH1_eq_finrank_intH1
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    realDimDeRhamH1 X = Module.finrank ℤ (IntegralOneCycle X) := by
  rw [realDim_deRhamH1_eq_realDim_singularH1 X,
      realDim_singularH1_eq_finrank_intH1 X]

end JacobianChallenge.HolomorphicForms
