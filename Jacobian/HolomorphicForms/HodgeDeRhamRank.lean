import Jacobian.HolomorphicForms.DeRhamSingular
import Jacobian.HolomorphicForms.CompactRiemannSurface
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Jacobian.HolomorphicForms.AnalyticGenus

/-!
# Top-level assembly: `2g = rank ℤ H₁(X, ℤ)` (Hodge / de Rham bridge)

**Status: plan only.** This file declares nothing, and none of the names cited
below (`realDimDeRhamH1_eq_two_analyticGenus`,
`realDim_deRhamH1_eq_finrank_intH1`, `hodge_deRham_rank_eq`) exists in the
tree; the `HodgeDecomposition` module was retired to `Attic/FalseGaps/`. The
public solution does not use this bridge — period-lattice fullness is proved
directly in `Jacobian/Periods/GenuinePeriodLattice*.lean`.

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


end JacobianChallenge.HolomorphicForms
