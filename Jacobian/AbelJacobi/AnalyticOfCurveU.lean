import Jacobian.AbelJacobi.PathIntegralFunctionalU
import Jacobian.Periods.PeriodFullComplexLatticeU
import Jacobian.ComplexTorus.Defs
import Jacobian.ComplexTorus.MkSmooth

/-!
# Universe-polymorphic analytic Abel-Jacobi map

The analytic Abel–Jacobi map of a compact Riemann surface `X : Type u` with base point
`P`,

  `analyticOfCurveU X P Q = [(∫_P^Q ω₁, …, ∫_P^Q ω_g)] ∈ ℂ^g / Λ`,

landing in `BasisAnalyticJacobianU X = quotient (Fin (analyticGenus ℂ X) → ℂ)
(periodFullComplexLatticeU X)` — which, under `ULift.{u}`, is the public `Jacobian X`
carrier of `Jacobian/Solution.lean`. The integral is the genuine path integral
`pathIntegralFunctionalU` (period vector of a chosen `C¹` path); its class does not
depend on the path (`pathIntegralFunctionalU_sub_mem`).

* `analyticOfCurve_selfU` (`P ↦ 0`) is **proved**: the integral from `P` to `P` along
  the chosen path is a period.
* `analyticOfCurve_contMDiffU` (holomorphicity) is a **labelled gap**: classically, near
  any `Q₀` the map is `Q ↦ [c + (F₁(Q), …, F_g(Q))]` with `Fᵢ` local holomorphic
  primitives of `ωᵢ` in a chart ball, which is holomorphic. Formalizing it needs the
  local fundamental theorem of calculus for `pathIntegralViaCover`.
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
The universe-`u` basis-aligned analytic Jacobian carrier: the complex torus
`ℂ^g / Λ` for the genuine period lattice `Λ`. Under `ULift.{u}` this is the public
`Jacobian X` carrier.
-/
abbrev BasisAnalyticJacobianU : Type :=
  quotient (Fin (analyticGenus ℂ X) → ℂ) (periodFullComplexLatticeU X)

/--
The analytic Abel–Jacobi map `Q ↦ [∫_P^Q ω]` on the basis-aligned carrier: the class
modulo periods of the genuine path integral from `P` to `Q`.
-/
noncomputable def analyticOfCurveU (P : X) : X → BasisAnalyticJacobianU X :=
  fun Q => mk (Fin (analyticGenus ℂ X) → ℂ)
    (periodFullComplexLatticeU X) (pathIntegralFunctionalU X P Q)

/-- The Abel–Jacobi map sends the base point to zero (the self-integral is a period). -/
lemma analyticOfCurve_selfU (P : X) : analyticOfCurveU X P P = 0 :=
  (mk_eq_zero_iff (periodFullComplexLatticeU X)).mpr (pathIntegralFunctionalU_self_mem P)

/--
The value of the Abel–Jacobi map is the class of the period vector of **any** `C¹`
path from `P` to `Q`.
-/
lemma analyticOfCurveU_eq_mk_periodVector (P Q : X) {γ : Path P Q} (hγ : IsC1Path γ) :
    analyticOfCurveU X P Q =
      mk (Fin (analyticGenus ℂ X) → ℂ) (periodFullComplexLatticeU X) (periodVector X γ) := by
  unfold analyticOfCurveU
  exact QuotientAddGroup.eq.mpr (by
    have h := pathIntegralFunctionalU_sub_mem (X := X) hγ
    rw [← neg_mem_iff, neg_sub, sub_eq_neg_add] at h
    exact h)

/--
**Holomorphicity of the Abel–Jacobi map.**

GAP (`sorry`), a true classical statement: near any point the map is a constant plus
local holomorphic primitives of the basis forms, read modulo `Λ` (Forster,
*Lectures on Riemann Surfaces*, §21). Needs the local fundamental theorem of calculus for
`pathIntegralViaCover`; see the module docstring.
-/
theorem analyticOfCurve_contMDiffU (P : X) :
    ContMDiff 𝓘(ℂ)
      (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
      (⊤ : WithTop ℕ∞) (analyticOfCurveU X P) := by
  -- GAP: local primitives ⇒ holomorphic; see docstring.
  sorry

end JacobianChallenge.AbelJacobi
