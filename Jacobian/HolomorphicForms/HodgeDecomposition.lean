import Jacobian.HolomorphicForms.HodgeStarRS
import Jacobian.HolomorphicForms.AntiHolomorphicOneForm
import Jacobian.HolomorphicForms.DeRhamCohomology
import Jacobian.HolomorphicForms.HodgeProjection
import Jacobian.HolomorphicForms.RealComplexDeRham
import Jacobian.HolomorphicForms.AnalyticGenus
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Hodge decomposition dimension formula on a Riemann surface

dim_ℂ H¹_dR(X, ℂ) = 2 g.

The classical proof routes through the *harmonic decomposition*:

H¹_dR(X, ℂ) ≅ Harm¹(X)
              = Ω¹(X)_holo ⊕ Ω¹(X)_anti
              ≅ ℂ^g ⊕ ℂ^g.

The conjugation isomorphism on `Ω¹(X)_anti ≃ Ω¹(X)_holo` (as ℝ-vector
spaces) gives `dim_ℂ Ω¹_anti = g`, so the total dim is `2g`.

## Mathlib v4.28.0 status

* harmonic projection (`HodgeStarRS.lean`),
* anti-holomorphic conjugation (`AntiHolomorphicOneForm.lean`),
* `\bar Ω¹` finite-dim (`AntiHolomorphicOneForm.lean`).

## What this file provides

* `complexDim_deRhamH1ℂ_eq_two_analyticGenus_via_harmonic` — the same
  identity stated as the explicit `2 * analyticGenus ℂ X` (RHS form
  consumed by the top-level `hodge_deRham_rank_eq` assembly).

## TOPDOWN role

This is the **Hodge side** of the dimension chain:
`2g = dim_ℂ Ω¹ + dim_ℂ \bar Ω¹ = dim_ℂ Harm¹ = dim_ℂ H¹_dR`.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold



/--
analyticHarmonicGenus X = 2 * analyticGenus ℂ X.

Combines `analyticHarmonicGenus_eq_analyticGenus_add_anti` and
`analyticAntiGenus_eq_analyticGenus`. Pure `omega` after rewriting.
-/
theorem analyticHarmonicGenus_eq_two_analyticGenus
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X] :
    analyticHarmonicGenus X = 2 * analyticGenus ℂ X := by
  rw [analyticHarmonicGenus_eq_analyticGenus_add_anti X,
      analyticAntiGenus_eq_analyticGenus X]
  ring



end JacobianChallenge.HolomorphicForms
