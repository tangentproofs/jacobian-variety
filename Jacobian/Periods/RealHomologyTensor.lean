import Jacobian.Periods.IntegralOneCycle
import Jacobian.Periods.IntegralOneCycleRank
import Jacobian.HolomorphicForms.RealSingularH1
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Universal-coefficient bridge: `H¹_sing(X, ℝ) ≃ Hom_ℤ(H₁(X, ℤ), ℝ)`

For a topological space whose `H₁` is finitely generated, the
universal-coefficient theorem (UCT) gives

H^k_sing(X, ℝ) ≃ Hom_ℤ(H_k(X, ℤ), ℝ)

(no torsion contribution since ℝ is divisible).  The chain of
identities

realDimSingularH1 X
    = dim_ℝ Hom_ℤ(H₁(X, ℤ), ℝ)
    = rank_ℤ H₁(X, ℤ)

uses both UCT (first equality) and the algebra of `Hom_ℤ(_, ℝ)` for
finitely generated free ℤ-modules (second equality).

## What this file provides

## TOPDOWN role
-/

namespace JacobianChallenge.Periods

open scoped Manifold

open JacobianChallenge.HolomorphicForms

/--
Bottom-up content: the universal-coefficient theorem with ℝ
coefficients. Since ℝ is divisible (so `Ext_ℤ¹(_, ℝ) = 0`), the UCT
short exact sequence collapses to an isomorphism:
`H^k(X, ℝ) ≃ Hom_ℤ(H_k(X, ℤ), ℝ)`.
-/
theorem realDimSingularH1_eq_finrank_intHom1
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    realDimSingularH1 X = Module.finrank ℝ (IntegralOneCycle X →ₗ[ℤ] ℝ) := by
  unfold realDimSingularH1
  rfl


end JacobianChallenge.Periods
