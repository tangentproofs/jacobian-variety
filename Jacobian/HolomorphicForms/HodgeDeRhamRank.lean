import Jacobian.HolomorphicForms.HodgeDecomposition
import Jacobian.HolomorphicForms.DeRhamSingular
import Jacobian.Periods.IntegralOneCycleRank
import Jacobian.HolomorphicForms.CompactRiemannSurface
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Top-level assembly: `2g = rank ℤ H₁(X, ℤ)` (Hodge / de Rham bridge)

* `Jacobian.HolomorphicForms.HodgeDecomposition`
  (`realDimDeRhamH1_eq_two_analyticGenus`):
  `realDimDeRhamH1 X = 2 * analyticGenus ℂ X` — Hodge side.

* `Jacobian.HolomorphicForms.DeRhamSingular`
  (`realDim_deRhamH1_eq_finrank_intH1`):
  `realDimDeRhamH1 X = Module.finrank ℤ (IntegralOneCycle X)` —
  de Rham + UCT side.

Both equalities have `realDimDeRhamH1 X` on the LHS, so transitivity
gives `2 * analyticGenus ℂ X = Module.finrank ℤ (IntegralOneCycle X)`,
which is exactly the body of
`JacobianChallenge.Periods.hodge_deRham_rank_eq`.

## TOPDOWN role
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

/--
Combines:

The chain is `2g = realDim H¹_dR = rank ℤ H₁`.
-/
theorem two_analyticGenus_eq_finrank_intH1
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X] :
    2 * analyticGenus ℂ X
      = Module.finrank ℤ (JacobianChallenge.Periods.IntegralOneCycle X) := by
  rw [← realDimDeRhamH1_eq_two_analyticGenus X,
      realDim_deRhamH1_eq_finrank_intH1 X]

end JacobianChallenge.HolomorphicForms
