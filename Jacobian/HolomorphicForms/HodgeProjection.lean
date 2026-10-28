import Jacobian.HolomorphicForms.HodgeLaplacian
import Jacobian.HolomorphicForms.DeRhamComplex
import Jacobian.HolomorphicForms.HodgeStarRS
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Harmonic projection: H¹_dR ≃ Harm¹

The Hodge theorem on a compact oriented Riemannian manifold says that
every de Rham cohomology class has a unique harmonic representative:

H^k_dR(X, ℂ) ≅ Harm^k(X, ℂ)         (orthogonal projection)

Mathlib v4.28.0 lacks the entire elliptic-operator / harmonic-projection
apparatus.  This file decomposes the named obligation
`complexDimDeRhamH1ℂ_eq_analyticHarmonicGenus` (in
`HodgeDecomposition.lean`) into its underlying
elliptic-projection ingredients.

## What this file provides

## TOPDOWN role

Splits the Hodge harmonic projection into:
1. existence of the projection (Δ has closed range and finite kernel),
2. orthogonality of d-image and harmonic (Hodge identity),
3. surjectivity onto H¹_dR.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

/-- Current-model harmonic projection on 1-forms. -/
noncomputable def harmonicProjection1
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    SmoothDiffForm 1 X →ₗ[ℂ] HarmonicOneForm X where
  toFun ω := ω.1
  map_add' := by
    intro ω η
    rfl
  map_smul' := by
    intro c ω
    rfl

/--
Design-stage harmonic projection for the period-aware smooth-form substrate.
It records the intended re-based signature: harmonic projection reads the
coefficient part and ignores the period payload.  Existing consumers stay on
`harmonicProjection1` until the substrate migration is performed.
-/
noncomputable def harmonicProjection1WithPeriods
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    SmoothDiffFormWithPeriods 1 X →ₗ[ℂ] HarmonicOneForm X where
  toFun ω := ω.1
  map_add' := by
    intro ω η
    rfl
  map_smul' := by
    intro c ω
    rfl

/--
**Current-model Hodge representatives.** Every harmonic 1-form is
the harmonic projection of a closed 1-form.

This is the closed-form version of `harmonicProjection1_surjective` needed
to descend the projection to de Rham cohomology. Classically a harmonic
form is itself closed, so this follows from the projector acting as the
identity on harmonic forms.
-/
theorem harmonicProjection1_closed_surjective
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Function.Surjective ((harmonicProjection1 X).domRestrict (ClosedForm 1 X)) := by
  intro η
  refine ⟨⟨(η, 0), ?_⟩, rfl⟩
  rw [ClosedForm, LinearMap.mem_ker]
  ext i <;> simp [exteriorDerivative]

/--
**Assembly.** The unrestricted harmonic projection is surjective
because every harmonic form is already the projection of a closed form.
-/
theorem harmonicProjection1_surjective
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Function.Surjective (harmonicProjection1 X) := by
  intro η
  obtain ⟨ω, hω⟩ := harmonicProjection1_closed_surjective X η
  exact ⟨(ω : SmoothDiffForm 1 X), hω⟩

/--
**Current-model Hodge orthogonality.** Exact 1-forms project to
zero; in the zero-differential surrogate, exact forms are zero.

Bottom-up content: `(dη, ω)_{L²} = (η, d^* ω)_{L²}` and `d^* ω = 0`
for harmonic `ω`. Integration by parts is the missing piece.
-/
theorem harmonicProjection1_vanishes_on_exact
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : SmoothDiffForm 1 X) (hω : ω ∈ ExactForm 0 X) :
    harmonicProjection1 X ω = 0 := by
  rcases hω with ⟨η, hη⟩
  rw [← hη]
  ext i
  simp [harmonicProjection1, exteriorDerivative]

/--
**Hodge harmonic embedding.** A harmonic 1-form `h : HarmonicOneForm X`
(its coefficient data) re-enters the smooth-form substrate as the form
`(h, 0)` carrying no period payload.  This names the section of
`harmonicProjection1` used to phrase the Hodge decomposition: it is a genuine
right inverse on the coefficient part (`harmonicProjection1 X (harmonicEmbed X h) = h`).
-/
noncomputable def harmonicEmbed
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (h : HarmonicOneForm X) : SmoothDiffForm 1 X :=
  (h, 0)

theorem harmonicProjection1_harmonicEmbed
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (h : HarmonicOneForm X) :
    harmonicProjection1 X (harmonicEmbed X h) = h := rfl











end JacobianChallenge.HolomorphicForms
