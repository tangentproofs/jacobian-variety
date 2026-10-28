import Jacobian.Periods.GenuinePeriodLattice

/-!
# Universe-polymorphic path-integral functional (the Abel–Jacobi integral)

The Abel–Jacobi map of a compact Riemann surface sends `Q` to
`(∫_P^Q ω₁, …, ∫_P^Q ω_g)` modulo periods. This file defines the integral
`pathIntegralFunctionalU X P Q : Fin (analyticGenus ℂ X) → ℂ` as the period vector
(`Periods.periodVector`) of a chosen chart chain from `P` to `Q`; such a chain exists
because `X` is connected (`Periods.exists_chain`).

The vector depends on the chosen chain; its class modulo the period lattice does not:
any two chains with the same endpoints have period vectors differing by a period,
**by the definition of the period lattice** (`Periods.periodVector_sub_mem`). That is
`pathIntegralFunctionalU_sub_mem` below.

**History.** This file used to declare `opaque pathIntegralFunctionalBundleU` over a
structure whose only fields were `val`, `val P P = 0` and smoothness of `val P`, with an
`Inhabited` witness `fun _ _ => 0`: a spec satisfied by the zero functional, standing in
for the integral. (Its smoothness field was in fact unsatisfiable by a genuine path
integral for `g ≥ 1`: a single-valued holomorphic map `X → ℂ^g` on a compact surface is
constant.) The `opaque` is gone; the functional is now a definition.
-/

namespace JacobianChallenge.AbelJacobi

open scoped Manifold
open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods

universe u

variable (X : Type u) [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] [ConnectedSpace X]
  [FiniteDimensionalHolomorphicOneForms ℂ X]

/-- A chosen chart chain from `P` to `Q` (exists since `X` is connected). -/
noncomputable def chosenChain (P Q : X) : List (ChartSegment X) :=
  (exists_chain P Q).choose

theorem chosenChain_isChain (P Q : X) : IsChain (chosenChain X P Q) P Q :=
  (exists_chain P Q).choose_spec

/--
The path-integral coordinates `(∫_P^Q ω₁, …, ∫_P^Q ω_g)` along a chosen chart chain from
`P` to `Q`. Well defined modulo periods: `pathIntegralFunctionalU_sub_mem`.
-/
noncomputable def pathIntegralFunctionalU (P Q : X) : Fin (analyticGenus ℂ X) → ℂ :=
  periodVector X (chosenChain X P Q)

variable {X}

/--
**Independence of the path, modulo periods.** For *every* chart chain `l` from `P` to `Q`,
the functional differs from `periodVector l` by a period.
-/
theorem pathIntegralFunctionalU_sub_mem {P Q : X} {l : List (ChartSegment X)}
    (hl : IsChain l P Q) :
    pathIntegralFunctionalU X P Q - periodVector X l ∈ genuinePeriodSubgroup X :=
  periodVector_sub_mem (chosenChain_isChain X P Q) hl

/--
At the base point the functional is a period (the integral over a closed chain), so its
class in the Jacobian is zero.
-/
theorem pathIntegralFunctionalU_self_mem (P : X) :
    pathIntegralFunctionalU X P P ∈ genuinePeriodSubgroup X :=
  periodVector_mem_of_loop (chosenChain_isChain X P P)

end JacobianChallenge.AbelJacobi
