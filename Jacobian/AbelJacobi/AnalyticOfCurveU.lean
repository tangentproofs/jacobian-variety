import Jacobian.AbelJacobi.PathIntegralFunctionalU
import Jacobian.Periods.PeriodFullComplexLatticeU
import Jacobian.ComplexTorus.Defs
import Jacobian.ComplexTorus.MkSmooth

/-!
# Universe-polymorphic analytic Abel-Jacobi map

`Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` defines the Type-0 analytic
Abel-Jacobi map `analyticOfCurve (P : X) : X → BasisAnalyticJacobian X` as the
quotient projection of the path-integral functional, where
`BasisAnalyticJacobian X = quotient (Fin (analyticGenus ℂ X) → ℂ)
(periodFullComplexLattice X)`.

This file provides the universe-polymorphic companion `analyticOfCurveU`
(D1 of the Abel-Jacobi "D-chain"), landing in the universe-`u` quotient
`BasisAnalyticJacobianU X = quotient (Fin (analyticGenus ℂ X) → ℂ)
(periodFullComplexLatticeU X)` — which, under `ULift.{u}`, is precisely the
public `Jacobian X` carrier wired in `Jacobian/Solution.lean` (Milestone A). It
is built on the D0 `pathIntegralFunctionalU` and the universe-polymorphic complex
-torus quotient machinery (`ComplexTorus.mk` / `contMDiff_mk`, both stated over
`{V : Type*}` with a `FullComplexLattice` parameter).

Every declaration is a verbatim mirror of its Type-0 original
(`analyticOfCurve` / `analyticOfCurve_self` / `analyticOfCurve_contMDiff`). No
new sorry is introduced: smoothness and the base-point identity are genuine; the
only `sorryAx` dependence is transitive, through `periodFullComplexLatticeU`'s
inherited Periods layer-frontier obligations — exactly as on the Type-0 side. The
public `ofCurve` / `ofCurve_self` / `ofCurve_contMDiff` (Milestone B) will wrap
these via `ULift.up` and `contMDiff_uLift_up`.
-/

namespace JacobianChallenge.AbelJacobi

open scoped Manifold
open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods JacobianChallenge.ComplexTorus

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [FiniteDimensionalHolomorphicOneForms ℂ X]

/--
The universe-`u` basis-aligned analytic Jacobian carrier: the complex-torus
quotient of the basis-aligned model by the universe-`u` period lattice.
Universe-polymorphic companion to `BasisAnalyticJacobian`. Under `ULift.{u}` this
is the public `Jacobian X` carrier.
-/
abbrev BasisAnalyticJacobianU : Type :=
  quotient (Fin (analyticGenus ℂ X) → ℂ) (periodFullComplexLatticeU X)

/--
The universe-`u` analytic Abel-Jacobi map on the basis-aligned carrier.
Universe-polymorphic companion to `analyticOfCurve`; lifts `pathIntegralFunctionalU`
through the universe-`u` period quotient.
-/
noncomputable def analyticOfCurveU (P : X) : X → BasisAnalyticJacobianU X :=
  fun Q => mk (Fin (analyticGenus ℂ X) → ℂ)
    (periodFullComplexLatticeU X) (pathIntegralFunctionalU X P Q)

/--
The universe-`u` Abel-Jacobi map sends the base point to zero.
Universe-polymorphic companion to `analyticOfCurve_self`.
-/
lemma analyticOfCurve_selfU (P : X) : analyticOfCurveU X P P = 0 := by
  unfold analyticOfCurveU
  rw [pathIntegralFunctionalU_self]
  rfl

/--
Holomorphicity of the universe-`u` analytic Abel-Jacobi map. Universe-polymorphic
companion to `analyticOfCurve_contMDiff`: the quotient projection `mk` is smooth
(`ComplexTorus.contMDiff_mk`) and composes with the smooth path-integral
functional (`pathIntegralFunctionalU_contMDiff`, D0).
-/
theorem analyticOfCurve_contMDiffU (P : X) :
    ContMDiff 𝓘(ℂ)
      (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
      (⊤ : WithTop ℕ∞) (analyticOfCurveU X P) :=
  (ComplexTorus.contMDiff_mk (periodFullComplexLatticeU X)).comp
    (pathIntegralFunctionalU_contMDiff X P)

end JacobianChallenge.AbelJacobi
