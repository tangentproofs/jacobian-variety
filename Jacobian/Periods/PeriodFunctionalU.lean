import Jacobian.HolomorphicForms.Defs
import Jacobian.Periods.IntegralOneCycleU
import Jacobian.Blueprint.Sec03.SingularChainComplexZU
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Universe-polymorphic period functional

`Jacobian/Periods/PeriodFunctional.lean` defines the period pairing
`periodPairing : IntegralOneCycle X →+ (HolomorphicOneForm E X →ₗ[ℂ] ℂ)` at
universe 0, as the `descHomology` of the degree-1 short complex of the Type-0
singular chain complex `Blueprint.Sec03.singularChainComplexZ X`, with the
chain-level integration map taken to be the placeholder `0` (the nonzero
integration content is a separate open frontier,
`singularChain_integration_from_simplex`).

This file adds the **universe-polymorphic** companion `periodPairingU` (and its
complex-model specialisation `periodPairingComplexU`, plus the range subgroup
`periodSubgroupU`), built identically on the universe-`u` chain complex
`Blueprint.Sec03.singularChainComplexZU X` (C1a) — whose degree-1 homology is
the universe-`u` `IntegralOneCycleU X` (C0). This is step C1b of the authorized
full `Type u` generalization of the period lattice (Option C containment): with
`periodSubgroupU` available, the basis-aligned period subgroup and hence
`periodFullComplexLattice` can be widened to `X : Type u` (steps C2/C3), so the
public `Jacobian (X : Type u)` type-checks — without disturbing the Type-0
period/homology subsystem (the rank/de-Rham/Hurewicz proofs).

The integration map is kept as the same `0` placeholder as the Type-0 original;
this step is purely the universe transport of the pairing's *shape*, not the
introduction of the (still-open) nonzero integration.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms CategoryTheory

universe u

/--
**Descent proof helper (universe-polymorphic).** Universe-`u` analogue of
`periodPairing_descent_aux`: if a morphism `Im` on degree-2 chains kills the
image of the short-complex boundary `S.f`, then
`S.toCycles ≫ S.iCycles ≫ Im = 0`. Proof identical to the Type-0 version.
-/
theorem periodPairing_descent_auxU
    {C : ModuleCat.{u} ℤ}
    (S : CategoryTheory.ShortComplex (ModuleCat.{u} ℤ))
    (Im : S.X₂ ⟶ C)
    (hI : ∀ (s : ↑S.X₁), Im.hom (S.f.hom s) = 0) :
    S.toCycles ≫ S.iCycles ≫ Im = 0 := by
  suffices h : S.f ≫ Im = 0 by rw [← CategoryTheory.Category.assoc, S.toCycles_i]; exact h
  apply ModuleCat.hom_ext
  ext s
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
              LinearMap.zero_apply]
  exact hI s

/--
The period pairing for `X : Type u`:
`IntegralOneCycleU X →+ (HolomorphicOneForm E X →ₗ[ℂ] ℂ)`.

Universe-polymorphic companion to `periodPairing`, built on the universe-`u`
chain complex `singularChainComplexZU` with the same `0` integration placeholder.
-/
noncomputable def periodPairingU
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (X : Type u) [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    IntegralOneCycleU X →+ (HolomorphicOneForm E X →ₗ[ℂ] ℂ) :=
  let I_E : JacobianChallenge.Blueprint.Sec03.SingularOneChainU X →ₗ[ℤ]
             (HolomorphicOneForm E X →ₗ[ℂ] ℂ) := 0
  let K := JacobianChallenge.Blueprint.Sec03.singularChainComplexZU X
  let S := K.sc 1
  let Im : S.X₂ ⟶ ModuleCat.of ℤ (HolomorphicOneForm E X →ₗ[ℂ] ℂ) :=
    ModuleCat.ofHom I_E
  have hI_sc : ∀ (s : ↑S.X₁), Im.hom (S.f.hom s) = 0 := by
    intro s; ext ω; exact rfl
  (S.descHomology (S.iCycles ≫ Im)
    (periodPairing_descent_auxU S Im hI_sc)).hom.toAddMonoidHom

/--
Complex-model period pairing for `X : Type u`. Universe-polymorphic companion to
`periodPairingComplex`; keeps all forms in the `ℂ` model.
-/
noncomputable def periodPairingComplexU
    (X : Type u) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    IntegralOneCycleU X →+ (HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ) :=
  let I : JacobianChallenge.Blueprint.Sec03.SingularOneChainU X →ₗ[ℤ]
            (HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ) := 0
  let K := JacobianChallenge.Blueprint.Sec03.singularChainComplexZU X
  let S := K.sc 1
  let Im : S.X₂ ⟶ ModuleCat.of ℤ (HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ) :=
    ModuleCat.ofHom I
  have hI_sc : ∀ (s : ↑S.X₁), Im.hom (S.f.hom s) = 0 := by
    intro s; ext ω; exact rfl
  (S.descHomology (S.iCycles ≫ Im)
    (periodPairing_descent_auxU S Im hI_sc)).hom.toAddMonoidHom

/--
The period subgroup for `X : Type u`: the image of `periodPairingU`, as an
additive subgroup of the linear dual of holomorphic 1-forms.
Universe-polymorphic companion to `periodSubgroup`.
-/
noncomputable def periodSubgroupU
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (X : Type u) [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    AddSubgroup (HolomorphicOneForm E X →ₗ[ℂ] ℂ) :=
  (periodPairingU E X).range

end JacobianChallenge.Periods
