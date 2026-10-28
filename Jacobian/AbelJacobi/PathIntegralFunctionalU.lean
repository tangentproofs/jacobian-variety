import Jacobian.Periods.GenuinePeriodLattice

/-!
# Universe-polymorphic path-integral functional (the Abel–Jacobi integral)

The Abel–Jacobi map of a compact Riemann surface sends `Q` to
`(∫_P^Q ω₁, …, ∫_P^Q ω_g)` modulo periods. This file defines the integral
`pathIntegralFunctionalU X P Q : Fin (analyticGenus ℂ X) → ℂ` as the period vector
(`Periods.periodVector`, built on the genuine multi-chart line integral
`pathIntegralViaCover`) of a chosen `C¹` path from `P` to `Q`.

The vector depends on the chosen path; its class modulo the period lattice does not:
any two `C¹` paths with the same endpoints have period vectors differing by a period,
**by the definition of the period lattice** (`Periods.periodVector_sub_mem`). That is
`pathIntegralFunctionalU_sub_mem` below.

**History.** This file used to declare `opaque pathIntegralFunctionalBundleU` over a
structure whose only fields were `val`, `val P P = 0` and smoothness of `val P`, with an
`Inhabited` witness `fun _ _ => 0`: a spec satisfied by the zero functional, standing in
for the integral. (Its smoothness field was in fact unsatisfiable by a genuine path
integral for `g ≥ 1`: a single-valued holomorphic map `X → ℂ^g` on a compact surface is
constant.) The `opaque` is gone; the functional is now a definition.

## The one remaining choice

`C¹` paths between two points of a connected manifold always exist; that fact
(`exists_isC1Path`) is a labelled gap here (standard, provable from chart-ball chains;
not a classical theorem, just not yet formalized). The definition does not depend on
it: it uses `if h : ∃ γ, IsC1Path γ then … else 0`, and the `else` branch is never
taken once `exists_isC1Path` is proved (`pathIntegralFunctionalU_eq_periodVector`).
-/

namespace JacobianChallenge.AbelJacobi

open scoped Manifold
open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/--
**`C¹` path-connectedness of a connected Riemann surface.** Any two points are joined by
a path that is `C¹` in every chart.

GAP (`sorry`): true and elementary (the set of points reachable from `P` by a `C¹` path
is open — extend by a straight segment in a chart ball — and closed, so it is everything
by connectedness; junctions are smoothed by a reparametrization flat at the endpoints),
but not yet formalized.
-/
theorem exists_isC1Path [ConnectedSpace X] (P Q : X) : ∃ γ : Path P Q, IsC1Path γ := by
  -- GAP: C¹ path-connectedness of a connected manifold; see docstring.
  sorry

variable (X) [FiniteDimensionalHolomorphicOneForms ℂ X]

/--
The path-integral coordinates `(∫_P^Q ω₁, …, ∫_P^Q ω_g)` along a chosen `C¹` path from
`P` to `Q` (`0` if there is none; see `exists_isC1Path` — that branch never occurs on a
connected surface). Well defined modulo periods: `pathIntegralFunctionalU_sub_mem`.
-/
noncomputable def pathIntegralFunctionalU (P Q : X) : Fin (analyticGenus ℂ X) → ℂ :=
  open Classical in
  if h : ∃ γ : Path P Q, IsC1Path γ then periodVector X h.choose else 0

variable {X}

/-- On a connected surface the functional is the period vector of the chosen path. -/
theorem pathIntegralFunctionalU_eq_periodVector [ConnectedSpace X] (P Q : X) :
    ∃ γ : Path P Q, IsC1Path γ ∧ pathIntegralFunctionalU X P Q = periodVector X γ := by
  have h := exists_isC1Path P Q
  refine ⟨h.choose, h.choose_spec, ?_⟩
  unfold pathIntegralFunctionalU
  rw [dif_pos h]

/--
**Independence of the path, modulo periods.** If a `C¹` path from `P` to `Q` exists (which
is always the case on a connected surface), then for *every* `C¹` path `γ` from `P` to
`Q`, the functional differs from `periodVector γ` by a period.
-/
theorem pathIntegralFunctionalU_sub_mem {P Q : X} {γ : Path P Q} (hγ : IsC1Path γ) :
    pathIntegralFunctionalU X P Q - periodVector X γ ∈ genuinePeriodSubgroup X := by
  have h : ∃ γ : Path P Q, IsC1Path γ := ⟨γ, hγ⟩
  unfold pathIntegralFunctionalU
  rw [dif_pos h]
  exact periodVector_sub_mem h.choose_spec hγ

/--
At the base point the functional is a period (the integral over a closed `C¹` curve),
so its class in the Jacobian is zero.
-/
theorem pathIntegralFunctionalU_self_mem (P : X) :
    pathIntegralFunctionalU X P P ∈ genuinePeriodSubgroup X := by
  have h := pathIntegralFunctionalU_sub_mem (X := X) (isC1Path_refl P)
  rwa [periodVector_refl, sub_zero] at h

end JacobianChallenge.AbelJacobi
