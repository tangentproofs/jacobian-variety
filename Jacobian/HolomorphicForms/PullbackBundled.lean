import Jacobian.HolomorphicForms.Defs
import Jacobian.HolomorphicForms.CLMBundleCompose
import Jacobian.TraceDegree.PullbackFun
import Jacobian.TraceDegree.PullbackFunId
import Jacobian.TraceDegree.PullbackFunComp
import Jacobian.TraceDegree.PullbackFormsLinearMap
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Bundled smooth pullback of holomorphic 1-forms

This file upgrades `pullbackFormsFun f η` (a function `X → ℂ →L[ℂ] ℂ`,
defined in `Jacobian/TraceDegree/PullbackFun.lean`) to a genuine
holomorphic 1-form `HolomorphicOneForm ℂ X`, given that `f` is `ContMDiff ω`.

The construction requires section-level smoothness through chart
trivializations of the cotangent bundle (a `Bundle.ContinuousLinearMap`
bundle). Mathlib lacks user-facing chart-transition / `localCoeff` API for
such sections; the needed composition lemma is supplied project-locally by
`Jacobian/HolomorphicForms/CLMBundleCompose.lean`.

The bundled pullback is a plain definition (it was `opaque` at one point; it
no longer is). Its underlying function is `pullbackFormsFunFiber`, so

* `pullbackFormsBundledLM_apply_fun` — the underlying function of the
  bundled pullback equals `pullbackFormsFun f η` — holds by `rfl`. It is not
  an axiom.

## API exposed
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold ContDiff
open JacobianChallenge.TraceDegree

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y]
variable {Z : Type*} [TopologicalSpace Z] [ChartedSpace ℂ Z]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Z]

/--
The chain-rule pullback of a holomorphic 1-form's value at a point,
typed natively as a section value in the cotangent fiber of `X` over `x`.

The composition `η.toFun (f x) ∘L mfderiv f x` is *natively* a continuous
linear map `TangentSpace 𝓘(ℂ,ℂ) x →L[ℂ] TangentSpace 𝓘(ℂ,ℂ) (f x)`, and
since `(Bundle.Trivial Y ℂ) (f x) = ℂ = (Bundle.Trivial X ℂ) x` (the trivial
bundle's fiber is the constant `ℂ`), this is precisely the cotangent fiber
type at `x`.
-/
noncomputable def pullbackFormsFunFiber
    (f : X → Y) (η : HolomorphicOneForm ℂ Y) (x : X) :
    CotangentSpace ℂ X x :=
  (η.toFun (f x)).comp
    (mfderiv (modelWithCornersSelf ℂ ℂ)
             (modelWithCornersSelf ℂ ℂ) f x)

/--
Section-level smoothness of the chain-rule pullback.

This was the lone bottom-up obligation of the `PullbackBundled` module —
smoothness of a `Bundle.ContinuousLinearMap`-valued section formed by
composing two smooth CLM-bundle sections. It is now proved (see
`#### Project status` below).

Specifically `pullbackFormsFunFiber f η x = (η.toFun (f x)).comp (mfderiv f x)`
is the composition (in `→L[ℂ]`) of:

* `mfderiv 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) f x : TangentSpace 𝓘(ℂ,ℂ) x →L[ℂ] TangentSpace 𝓘(ℂ,ℂ) (f x)`
  — smooth in tangent coordinates via `ContMDiffAt.mfderiv_const`.
* `η.toFun (f x) : TangentSpace 𝓘(ℂ,ℂ) (f x) →L[ℂ] (Bundle.Trivial Y ℂ) (f x)`
  — smooth as a section of the cotangent bundle along `f`, by
  composition of `η`'s smoothness with `f`'s smoothness.

Mathlib provides `ContMDiff.clm_bundle_apply` (CLM-section applied
to a vector-section is a vector-section) and the underlying
`ContMDiffWithinAt.clm_apply_of_inCoordinates` primitive, but it lacks
the dual-position analogue **`ContMDiff.clm_bundle_compose`** (CLM-section
composed with a CLM-section is a CLM-section), and likewise lacks
`ContMDiffWithinAt.clm_compose_of_inCoordinates`.

#### Project status

Closed. The missing Mathlib lemma was built project-locally as
`ContMDiffAt.clm_compose_of_inCoordinates` in
`Jacobian/HolomorphicForms/CLMBundleCompose.lean`, and the proof below
applies it directly. No gap remains here.
-/
theorem pullbackFormsFunFiber_contMDiff_section
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ Y) :
    ContMDiff 𝓘(ℂ, ℂ) (𝓘(ℂ, ℂ).prod 𝓘(ℂ, CotangentModelFiber ℂ))
      (⊤ : WithTop ℕ∞)
      (fun x => Bundle.TotalSpace.mk' (CotangentModelFiber ℂ) x
        (pullbackFormsFunFiber f η x)) := by
  intro x
  -- Decompose the section's smoothness into base smoothness + in-coords smoothness.
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  -- Inner factor: mfderiv f, smooth in tangent coordinates.
  -- Need (⊤ : WithTop ℕ∞) + 1 ≤ ⊤; in WithTop, ⊤ + 1 = ⊤.
  have htop : (⊤ : WithTop ℕ∞) + 1 ≤ (⊤ : WithTop ℕ∞) := by
    rw [WithTop.top_add]
  have hψ_raw := ContMDiffAt.mfderiv_const (I := 𝓘(ℂ, ℂ)) (I' := 𝓘(ℂ, ℂ))
    (f := f) (n := (⊤ : WithTop ℕ∞)) (hf x) htop
  -- hψ_raw : ContMDiffAt _ 𝓘(ℂ, ℂ →L[ℂ] ℂ) _
  --   (inTangentCoordinates 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) id f (mfderiv ...) x) x
  -- inTangentCoordinates is exactly the inCoordinates form we need.
  -- Outer factor: η.toFun (f m), smooth as a section of cotangent bundle of Y over f.
  have hηf : ContMDiffAt 𝓘(ℂ, ℂ) (𝓘(ℂ, ℂ).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ))
      (⊤ : WithTop ℕ∞)
      (fun m => Bundle.TotalSpace.mk' (CotangentModelFiber ℂ) (f m)
        ((η.toFun (f m) : CotangentSpace ℂ Y (f m)))) x :=
    ((η.contMDiff).comp hf) x
  rw [contMDiffAt_hom_bundle] at hηf
  -- hηf.2 : in-coords smoothness of m ↦ η.toFun (f m), with both source/target bases = f.
  -- Apply the new clm_compose_of_inCoordinates.
  exact hηf.2.clm_compose_of_inCoordinates hψ_raw contMDiffAt_id (hf x) (hf x)

/--
Bundled pullback of a holomorphic 1-form along a smooth map.
Concrete (non-opaque): the underlying function is `pullbackFormsFunFiber`
(natively in the cotangent fiber); smoothness is supplied by
`pullbackFormsFunFiber_contMDiff_section`.
-/
noncomputable def pullbackFormsBundled
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ Y) :
    HolomorphicOneForm ℂ X where
  toFun := pullbackFormsFunFiber f η
  contMDiff_toFun := pullbackFormsFunFiber_contMDiff_section f hf η

/--
The pullback of holomorphic 1-forms as a ℂ-linear map between the
form spaces. Concrete (non-opaque).
-/
noncomputable def pullbackFormsBundledLM
    (X Y : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f) :
    HolomorphicOneForm ℂ Y →ₗ[ℂ] HolomorphicOneForm ℂ X where
  toFun η := pullbackFormsBundled f hf η
  map_add' η ζ := by
    apply ContMDiffSection.coe_inj
    funext x
    show pullbackFormsFunFiber f (η + ζ) x =
      pullbackFormsFunFiber f η x + pullbackFormsFunFiber f ζ x
    unfold pullbackFormsFunFiber
    have hcoe : ((η + ζ) : ∀ y, _) (f x) = (η : ∀ y, _) (f x) + (ζ : ∀ y, _) (f x) := by
      rw [ContMDiffSection.coe_add]; rfl
    rw [show (η + ζ).toFun (f x) = η.toFun (f x) + ζ.toFun (f x) from hcoe]
    exact ContinuousLinearMap.add_comp _ _ _
  map_smul' k η := by
    apply ContMDiffSection.coe_inj
    funext x
    show pullbackFormsFunFiber f (k • η) x = k • pullbackFormsFunFiber f η x
    unfold pullbackFormsFunFiber
    have hcoe : ((k • η) : ∀ y, _) (f x) = k • (η : ∀ y, _) (f x) := by
      rw [ContMDiffSection.coe_smul]; rfl
    rw [show (k • η).toFun (f x) = k • η.toFun (f x) from hcoe]
    exact ContinuousLinearMap.smul_comp k _ _


@[simp] theorem pullbackFormsBundledLM_apply_fun
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ Y) (x : X) :
    (pullbackFormsBundledLM X Y f hf η).toFun x = pullbackFormsFun f η x := rfl


theorem pullbackFormsBundledLM_id :
    pullbackFormsBundledLM X X (id : X → X) contMDiff_id = LinearMap.id := by
  refine LinearMap.ext fun η => ?_
  apply ContMDiffSection.coe_inj
  funext x
  change (pullbackFormsBundledLM X X (id : X → X) contMDiff_id η).toFun x =
    (LinearMap.id η).toFun x
  rw [pullbackFormsBundledLM_apply_fun, pullbackFormsFun_id]
  rfl


theorem pullbackFormsBundledLM_comp
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) g) :
    pullbackFormsBundledLM X Z (g ∘ f) (hg.comp hf) =
      (pullbackFormsBundledLM X Y f hf).comp
        (pullbackFormsBundledLM Y Z g hg) := by
  refine LinearMap.ext fun η => ?_
  apply ContMDiffSection.coe_inj
  funext x
  have htop : (⊤ : WithTop ℕ∞) ≠ 0 := by decide
  -- Step into .toFun on both sides.
  change (pullbackFormsBundledLM X Z (g ∘ f) (hg.comp hf) η).toFun x =
    (((pullbackFormsBundledLM X Y f hf).comp
      (pullbackFormsBundledLM Y Z g hg)) η).toFun x
  rw [pullbackFormsBundledLM_apply_fun (g ∘ f) (hg.comp hf) η x]
  rw [pullbackFormsFun_comp_apply f g η x
    (hg.mdifferentiable htop _) (hf.mdifferentiable htop _)]
  -- LHS: (η.toFun (g (f x)) ∘L mfderiv g (f x)) ∘L mfderiv f x
  -- RHS: ((B_f.comp B_g) η).toFun x where B_? := pullbackFormsBundledLM ...
  change _ = (pullbackFormsBundledLM X Y f hf
    (pullbackFormsBundledLM Y Z g hg η)).toFun x
  rw [pullbackFormsBundledLM_apply_fun f hf
    (pullbackFormsBundledLM Y Z g hg η) x]
  show ((η.toFun (g (f x))).comp _).comp _ =
    pullbackFormsFun f (pullbackFormsBundledLM Y Z g hg η) x
  unfold pullbackFormsFun
  rw [pullbackFormsBundledLM_apply_fun g hg η (f x)]
  show ((η.toFun (g (f x))).comp _).comp _ =
    (pullbackFormsFun g η (f x)).comp _
  unfold pullbackFormsFun
  rfl

end JacobianChallenge.HolomorphicForms
