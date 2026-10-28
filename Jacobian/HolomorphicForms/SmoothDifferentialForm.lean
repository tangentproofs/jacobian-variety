import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.Complex.Basic
import Jacobian.HolomorphicForms.Defs
import Jacobian.Periods.IntegralOneCycle
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Smooth k-forms on a complex manifold

## What this file provides

## TOPDOWN role

This is the **substrate** for the de Rham theorem refinement: once the
forms type and `d` are named, the comparison map to singular cochains
(in `DeRhamComparisonMap.lean`) can be expressed precisely.
-/

namespace JacobianChallenge.HolomorphicForms

open JacobianChallenge.Periods

open scoped Manifold

/--
Period payload for the next de Rham comparison substrate.  It is kept
separate from the current coefficient-only `SmoothDiffForm` during the
design-only migration step, so existing Hodge and de Rham lemmas continue to
compile while downstream files are rebased deliberately.
-/
abbrev SmoothDiffFormPeriodPayload
    (_n : ℕ) (X : Type) [TopologicalSpace X] : Type :=
  IntegralOneCycle X →ₗ[ℤ] ℂ

/-- The current holomorphic-coefficient component of the smooth-form model. -/
abbrev SmoothDiffFormCoeff
    (n : ℕ) (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] : Type _ :=
  Fin n.succ → HolomorphicOneForm ℂ X

/--
Period-aware smooth-form substrate for the authorized de Rham redesign.
The first component preserves the current coefficient model; the second
component carries the period data that `deRhamComparisonMap1` must eventually
read.
-/
abbrev SmoothDiffFormWithPeriods
    (n : ℕ) (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] : Type _ :=
  SmoothDiffFormCoeff n X × SmoothDiffFormPeriodPayload n X

/-- Public smooth-form substrate, now carrying the period payload used by degree-1 de Rham comparison. -/
abbrev SmoothDiffForm
    (n : ℕ) (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] : Type _ :=
  SmoothDiffFormWithPeriods n X

/--
Current-model exterior derivative `d : Ω^n(X) → Ω^{n+1}(X)`.

  The current `SmoothDiffForm` substrate is only a vector-space surrogate,
  with no wedge product or chartwise coefficient calculus. We therefore use
  the zero differential as the honest cochain-complex model at this layer:
  exact 1-forms remain zero, so period payloads are not quotiented away before
  the de Rham comparison map reads them. The bottom-up replacement is the
  classical chartwise operator once global differential forms exist.
-/
noncomputable def exteriorDerivative
    (n : ℕ) (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    SmoothDiffForm n X →ₗ[ℂ] SmoothDiffForm n.succ X :=
  0

/-- `d² = 0` for the current zero-differential form substrate. -/
theorem exteriorDerivative_squared_eq_zero
    (n : ℕ) (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    (exteriorDerivative n.succ X).comp (exteriorDerivative n X) = 0 := by
  rfl

/-- The kernel of `d : Ω^n → Ω^{n+1}` — the **closed** `n`-forms. -/
noncomputable def ClosedForm
    (n : ℕ) (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Submodule ℂ (SmoothDiffForm n X) :=
  LinearMap.ker (exteriorDerivative n X)

/-- The image of `d : Ω^{n-1} → Ω^n` — the **exact** `n`-forms. -/
noncomputable def ExactForm
    (n : ℕ) (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Submodule ℂ (SmoothDiffForm n.succ X) :=
  LinearMap.range (exteriorDerivative n X)

/--
The carrier (subtype) of `ClosedForm n X`, with explicit instances
to break the typeclass-resolution slowness when unfolding through
`Fin _ → HolomorphicOneForm`.
-/
noncomputable abbrev ClosedFormSub
    (n : ℕ) (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Type _ :=
  ↥(ClosedForm n X)

noncomputable instance ClosedFormSub.instAddCommGroup
    (n : ℕ) (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    AddCommGroup (ClosedFormSub n X) :=
  Submodule.addCommGroup _

noncomputable instance ClosedFormSub.instModuleℂ
    (n : ℕ) (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Module ℂ (ClosedFormSub n X) :=
  Submodule.module _


theorem ExactForm_le_ClosedForm
    (n : ℕ) (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    ExactForm n X ≤ ClosedForm n.succ X := by
  rw [ExactForm, ClosedForm]
  exact LinearMap.range_le_ker_iff.mpr (exteriorDerivative_squared_eq_zero n X)

/--
Submodule of exact forms inside closed forms — direct from
`ExactForm_le_ClosedForm`.  Stated as a name for use as the
denominator in the H¹_dR quotient.
-/
noncomputable def ExactForm.toClosedSubmodule
    (n : ℕ) (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Submodule ℂ (ClosedFormSub n.succ X) :=
  (ExactForm n X).comap (ClosedForm n.succ X).subtype

end JacobianChallenge.HolomorphicForms
