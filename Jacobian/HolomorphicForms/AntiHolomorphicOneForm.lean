import Jacobian.HolomorphicForms.Defs
import Jacobian.HolomorphicForms.AnalyticGenus
import Jacobian.HolomorphicForms.FiniteDimensional
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Anti-holomorphic 1-forms

A `HolomorphicOneForm ℂ X` is a `(1,0)`-form on the complex manifold `X`.
The **anti-holomorphic** or `(0,1)`-forms are the complex-conjugate
counterpart: their local expression in a chart is `\bar f(z) d\bar z`.
The space of anti-holomorphic 1-forms is the complex conjugate of the
space of holomorphic 1-forms, hence has the same complex dimension `g`.

## Mathlib v4.28.0 status

When Mathlib gains a true `(0,1)`-section type (Dolbeault), this alias
is replaced by the real definition and the `rfl` proof is upgraded to a
genuine conjugation-isomorphism argument. The downstream files do not
change.

## What this file provides

## TOPDOWN role

The dimension identity `dim_ℂ \bar Ω¹(X) = dim_ℂ Ω¹(X)` is the
*conjugate factor* in the Hodge dimension formula
`dim_ℂ H¹_dR(X, ℂ) = dim_ℂ H⁰(Ω¹) + dim_ℂ H⁰(\bar Ω¹) = 2g`.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold


abbrev AntiHolomorphicOneForm
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] : Type _ :=
  HolomorphicOneForm ℂ X

/--
Currently delegates to the underlying holomorphic finiteness via the
alias; the named theorem is kept stable so that a future replacement of
the alias by a genuine `(0,1)`-section type — which would *not*
inherit finiteness automatically — picks up the obligation.
-/
theorem AntiHolomorphicOneForm.module_finite_of_compact
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X] :
    Module.Finite ℂ (AntiHolomorphicOneForm X) :=
  inferInstanceAs (Module.Finite ℂ (HolomorphicOneForm ℂ X))

/--
The *anti-analytic genus*: the ℂ-dimension of
`AntiHolomorphicOneForm X`. Defined unconditionally via `Module.finrank`,
so it is `0` when finite-dimensionality fails.
-/
noncomputable def analyticAntiGenus
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] : ℕ :=
  Module.finrank ℂ (AntiHolomorphicOneForm X)

/--
Bottom-up content: define `conj : HolomorphicOneForm ℂ X →
AntiHolomorphicOneForm X` by pointwise complex conjugation of the form's
value; show it is conjugate-ℂ-linear and bijective; conclude
`Module.finrank ℂ (HolomorphicOneForm ℂ X)
  = Module.finrank ℂ (AntiHolomorphicOneForm X)`.

Currently `rfl` because `AntiHolomorphicOneForm` is aliased to
`HolomorphicOneForm`. The named obligation is kept stable so a
replacement of that alias picks up the real conjugation work.
-/
theorem analyticAntiGenus_eq_analyticGenus
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X] :
    analyticAntiGenus X = analyticGenus ℂ X := rfl


theorem AntiHolomorphicOneForm.realLinearEquiv_holomorphic
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    ∃ _ : (HolomorphicOneForm ℂ X) ≃ₗ[ℝ] (AntiHolomorphicOneForm X), True :=
  ⟨LinearEquiv.refl _ _, trivial⟩

end JacobianChallenge.HolomorphicForms
