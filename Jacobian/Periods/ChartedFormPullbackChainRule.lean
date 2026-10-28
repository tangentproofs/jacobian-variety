import Jacobian.Periods.ChartedFormPullback
import Jacobian.HolomorphicForms.PullbackBundled
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Chart-level chain rule for the form-pullback

The genuine analytic content of the path-integral naturality.

For a smooth `f : X → Y`, holomorphic 1-form `η` on `Y`, charts
`cX = chartAt ℂ p` and `cY = chartAt ℂ q`, and a point
`e ∈ cX.target` with `f (cX.symm e) ∈ cY.source`, the chart-pullback
of `pullbackFormsBundledLM f hf η` at `e` factors as the chart-pullback
of `η` at `ψ e := cY (f (cX.symm e))` precomposed with the manifold
derivative of the smooth chart-transition `ψ`:

`chartedFormPullback cX (pullbackFormsBundledLM f hf η) e
   = (chartedFormPullback cY η (ψ e)).comp (mfderiv ψ e)`

This is the **mfderiv chain rule** packaged for the `chartedFormPullback`
infrastructure: the algebraic identity that justifies the substitution
`γ_Y = ψ ∘ γ_X` at the level of integrands.

The proof is purely algebraic: chain rule for `mfderiv` plus the
inverse-function identity `mfderiv cY.symm ∘L mfderiv cY = id`.
-/

namespace JacobianChallenge.Periods

open scoped Manifold ContDiff
open JacobianChallenge.HolomorphicForms
open JacobianChallenge.TraceDegree

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y]

set_option linter.unusedSectionVars false in
/--
**Chart-level chain rule (algebraic).** For a smooth `f : X → Y`
between complex manifolds, holomorphic 1-form `η` on `Y`, charts
`cX = chartAt ℂ p` and `cY = chartAt ℂ q`, and `e ∈ cX.target` with
`f (cX.symm e) ∈ cY.source`, the chart-pullback of the form-pullback
factors through the manifold derivative of the chart-transition
`ψ := cY ∘ f ∘ cX.symm`:

`chartedFormPullback cX (pullbackFormsBundledLM f hf η) e
   = (chartedFormPullback cY η ((cY ∘ f ∘ cX.symm) e)).comp
       (mfderiv (cY ∘ f ∘ cX.symm) e)`.
-/
theorem chartedFormPullback_pullbackFormsBundledLM_eq
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (η : HolomorphicOneForm ℂ Y) (p : X) (q : Y)
    (e : ℂ) (he_target : e ∈ (chartAt ℂ p).target)
    (he_source : f ((chartAt ℂ p).symm e) ∈ (chartAt ℂ q).source) :
    chartedFormPullback (chartAt ℂ p) (pullbackFormsBundledLM X Y f hf η) e =
      (chartedFormPullback (chartAt ℂ q) η
          ((chartAt ℂ q) (f ((chartAt ℂ p).symm e)))).comp
        (mfderiv 𝓘(ℂ) 𝓘(ℂ)
          (fun e' => (chartAt ℂ q) (f ((chartAt ℂ p).symm e'))) e) := by
  set cX := chartAt ℂ p
  set cY := chartAt ℂ q
  -- Manifold differentiability hypotheses
  have htop : (⊤ : WithTop ℕ∞) ≠ 0 := by decide
  have hf_diff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f (cX.symm e) :=
    hf.mdifferentiable htop _
  have hcXsymm_diff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) cX.symm e :=
    (mdifferentiable_chart p).mdifferentiableAt_symm he_target
  have hcY_diff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) cY (f (cX.symm e)) :=
    (mdifferentiable_chart q).mdifferentiableAt he_source
  have hfcX_diff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (f ∘ cX.symm) e :=
    hf_diff.comp _ hcXsymm_diff
  -- The inverse-function identity at the chart cY.
  have hY_invDeriv :
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) cY.symm (cY (f (cX.symm e)))).comp
        (mfderiv 𝓘(ℂ) 𝓘(ℂ) cY (f (cX.symm e)))
      = ContinuousLinearMap.id ℂ ℂ :=
    (mdifferentiable_chart q).symm_comp_deriv he_source
  -- The chain rule for ψ := cY ∘ f ∘ cX.symm
  have hpsi_chain :
      mfderiv 𝓘(ℂ) 𝓘(ℂ) (fun e' => cY (f (cX.symm e'))) e =
        ((mfderiv 𝓘(ℂ) 𝓘(ℂ) cY (f (cX.symm e))).comp
          (mfderiv 𝓘(ℂ) 𝓘(ℂ) f (cX.symm e))).comp
            (mfderiv 𝓘(ℂ) 𝓘(ℂ) cX.symm e) := by
    have hψ_eq : (fun e' => cY (f (cX.symm e'))) = cY ∘ (f ∘ cX.symm) := rfl
    rw [hψ_eq, mfderiv_comp e hcY_diff hfcX_diff,
      mfderiv_comp e hf_diff hcXsymm_diff]
    rfl
  -- Use ContinuousLinearMap.ext to reduce to pointwise equality on a vector v.
  refine ContinuousLinearMap.ext (fun v => ?_)
  -- Unfold both sides via show.
  show ((pullbackFormsBundledLM X Y f hf η).toFun (cX.symm e)).comp
        (mfderiv 𝓘(ℂ) 𝓘(ℂ) cX.symm e) v =
      ((η.toFun (cY.symm (cY (f (cX.symm e))))).comp
        (mfderiv 𝓘(ℂ) 𝓘(ℂ) cY.symm (cY (f (cX.symm e))))).comp
        (mfderiv 𝓘(ℂ) 𝓘(ℂ) (fun e' => cY (f (cX.symm e'))) e) v
  -- pullbackFormsBundledLM_apply_fun: .toFun = pullbackFormsFun.
  rw [show (pullbackFormsBundledLM X Y f hf η).toFun (cX.symm e) =
      pullbackFormsFun f η (cX.symm e) from rfl]
  -- pullbackFormsFun f η x = (η.toFun (f x)).comp (mfderiv f x).
  show ((η.toFun (f (cX.symm e))).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) f (cX.symm e))).comp
        (mfderiv 𝓘(ℂ) 𝓘(ℂ) cX.symm e) v =
      ((η.toFun (cY.symm (cY (f (cX.symm e))))).comp
        (mfderiv 𝓘(ℂ) 𝓘(ℂ) cY.symm (cY (f (cX.symm e))))).comp
        (mfderiv 𝓘(ℂ) 𝓘(ℂ) (fun e' => cY (f (cX.symm e'))) e) v
  -- Substitute cY.symm (cY (f (cX.symm e))) = f (cX.symm e).
  rw [cY.left_inv he_source]
  -- Substitute the chain rule for ψ.
  rw [hpsi_chain]
  -- Now compare using inverse-function identity.
  set z := f (cX.symm e) with hz
  set w := (mfderiv 𝓘(ℂ) 𝓘(ℂ) f (cX.symm e)) ((mfderiv 𝓘(ℂ) 𝓘(ℂ) cX.symm e) v) with hw
  show (η.toFun z) w =
      (η.toFun z) ((mfderiv 𝓘(ℂ) 𝓘(ℂ) cY.symm (cY z))
        ((mfderiv 𝓘(ℂ) 𝓘(ℂ) cY z) w))
  congr 1
  have step :
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) cY.symm (cY z)) ((mfderiv 𝓘(ℂ) 𝓘(ℂ) cY z) w) =
        ((mfderiv 𝓘(ℂ) 𝓘(ℂ) cY.symm (cY z)).comp
          (mfderiv 𝓘(ℂ) 𝓘(ℂ) cY z)) w := rfl
  rw [step, hY_invDeriv]
  rfl

/--
**Vector form of the chart-level chain rule.** Pointwise on a
vector `v : ℂ`, the X-side integrand factors via the smooth
chart-transition `ψ := cY ∘ f ∘ cX.symm`:

`chartedFormPullback cX (pullbackFormsBundledLM f hf η) e v
   = chartedFormPullback cY η (ψ e) (mfderiv ψ e v)`.
-/
theorem chartedFormPullback_pullbackFormsBundledLM_apply
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (η : HolomorphicOneForm ℂ Y) (p : X) (q : Y)
    (e : ℂ) (he_target : e ∈ (chartAt ℂ p).target)
    (he_source : f ((chartAt ℂ p).symm e) ∈ (chartAt ℂ q).source) (v : ℂ) :
    chartedFormPullback (chartAt ℂ p) (pullbackFormsBundledLM X Y f hf η) e v =
      chartedFormPullback (chartAt ℂ q) η
        ((chartAt ℂ q) (f ((chartAt ℂ p).symm e)))
        (mfderiv 𝓘(ℂ) 𝓘(ℂ)
          (fun e' => (chartAt ℂ q) (f ((chartAt ℂ p).symm e'))) e v) := by
  rw [chartedFormPullback_pullbackFormsBundledLM_eq f hf η p q e he_target he_source]
  rfl

end JacobianChallenge.Periods
