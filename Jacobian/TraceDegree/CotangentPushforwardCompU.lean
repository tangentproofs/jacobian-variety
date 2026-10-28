import Jacobian.AbelJacobi.AnalyticOfCurveBasis
import Jacobian.ComplexTorus.OfClm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Jacobian.HolomorphicForms.TraceSpec

set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped Manifold ContDiff Topology
open JacobianChallenge.TraceDegree
open JacobianChallenge.HolomorphicForms

namespace JacobianChallenge.TraceDegree.CotangentPushforwardCompU

universe u v w
variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
variable {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
variable {Z : Type w} [TopologicalSpace Z] [ChartedSpace ℂ Z]

/-- Composition of two `IsIso` witnesses for a continuous linear map. -/
private noncomputable def IsIso.composeU
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    {φ : E →L[ℂ] F} {ψ : F →L[ℂ] G}
    (hφ : IsIso φ) (hψ : IsIso ψ) :
    IsIso (ψ.comp φ) where
  inv := hφ.inv.comp hψ.inv
  left_inv := by
    -- (hφ.inv ∘ hψ.inv) ∘ (ψ ∘ φ) = hφ.inv ∘ (hψ.inv ∘ ψ) ∘ φ = hφ.inv ∘ φ = id
    ext x
    simp [ContinuousLinearMap.comp_apply, show hψ.inv (ψ (φ x)) = φ x from by
      have := congr_arg (fun (m : F →L[ℂ] F) => m (φ x)) hψ.left_inv
      simpa [ContinuousLinearMap.comp_apply] using this,
      show hφ.inv (φ x) = x from by
        have := congr_arg (fun (m : E →L[ℂ] E) => m x) hφ.left_inv
        simpa [ContinuousLinearMap.comp_apply] using this]
  right_inv := by
    -- (ψ ∘ φ) ∘ (hφ.inv ∘ hψ.inv) = ψ ∘ (φ ∘ hφ.inv) ∘ hψ.inv = ψ ∘ hψ.inv = id
    ext z
    simp [ContinuousLinearMap.comp_apply, show φ (hφ.inv (hψ.inv z)) = hψ.inv z from by
      have := congr_arg (fun (m : F →L[ℂ] F) => m (hψ.inv z)) hφ.right_inv
      simpa [ContinuousLinearMap.comp_apply] using this,
      show ψ (hψ.inv z) = z from by
        have := congr_arg (fun (m : G →L[ℂ] G) => m z) hψ.right_inv
        simpa [ContinuousLinearMap.comp_apply] using this]

/--
**Chain rule for the cotangent pushforward.** At a point `x` where
both `mfderiv f x` and `mfderiv g (f x)` are isomorphisms, the
cotangent pushforward along the composition `g ∘ f` factors as the
composition of the individual cotangent pushforwards.
-/
theorem cotangentPushforward_compU
    (f : X → Y) (g : Y → Z)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hg : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω g)
    (x : X)
    (hf_iso : Nonempty (IsIso (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x)))
    (hg_iso : Nonempty (IsIso (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) g (f x))))
    (ωx : CotangentSpace ℂ X x) :
    cotangentPushforward (g ∘ f) x ωx =
      cotangentPushforward g (f x) (cotangentPushforward f x ωx) := by
  classical
  -- The chain rule: mfderiv (g ∘ f) x = mfderiv g (f x) ∘L mfderiv f x.
  have hω_ne : (ω : WithTop ℕ∞) ≠ 0 := by decide
  have hmf_comp :
      mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (g ∘ f) x =
        (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) g (f x)).comp
          (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x) :=
    mfderiv_comp x (hg.mdifferentiableAt hω_ne) (hf.mdifferentiableAt hω_ne)
  -- The composition is an isomorphism via IsIso.composeU.
  have hgf_iso :
      Nonempty (IsIso (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (g ∘ f) x)) := by
    refine ⟨?_⟩
    -- Cast IsIso along the mfderiv equality.
    rw [hmf_comp]
    exact IsIso.composeU (Classical.choice hf_iso) (Classical.choice hg_iso)
  -- Unfold both sides; both branches use the dif_pos with their iso witnesses.
  unfold cotangentPushforward
  simp only [dif_pos hgf_iso, dif_pos hg_iso, dif_pos hf_iso]
  -- LHS = ωx.comp (Classical.choice hgf_iso).inv
  -- RHS = (ωx.comp (Classical.choice hf_iso).inv).comp (Classical.choice hg_iso).inv
  --     = ωx.comp ((Classical.choice hf_iso).inv.comp (Classical.choice hg_iso).inv)
  -- We compare the two `inv` maps. By IsIso.inv_unique:
  set hgf := Classical.choice hgf_iso
  set hf' := Classical.choice hf_iso
  set hg' := Classical.choice hg_iso
  have hcomp_iso : IsIso ((mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) g (f x)).comp
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x)) :=
    IsIso.composeU hf' hg'
  -- After hmf_comp rewrite, hgf is an IsIso for the composed CLM; uniqueness:
  -- LHS inv = (hf'.inv.comp hg'.inv).
  -- Approach: use uniqueness of inverses at the level of left-inverse equality.
  -- We show hgf.inv = hf'.inv.comp hg'.inv directly: it suffices to verify
  -- (hf'.inv.comp hg'.inv).comp (mfderiv (g∘f) x) = id, which uses hmf_comp.
  have hinv_eq : hgf.inv = hf'.inv.comp hg'.inv := by
    -- Strategy: compute hgf.inv via its uniqueness as inverse of mfderiv (g∘f) x.
    -- (hf'.inv.comp hg'.inv) ∘ (mfderiv (g∘f) x)
    --   = hf'.inv ∘ (hg'.inv ∘ (mfderiv g (f x) ∘ mfderiv f x))     [by hmf_comp]
    --   = hf'.inv ∘ ((hg'.inv ∘ mfderiv g (f x)) ∘ mfderiv f x)
    --   = hf'.inv ∘ (id ∘ mfderiv f x)
    --   = hf'.inv ∘ mfderiv f x
    --   = id
    -- So hf'.inv.comp hg'.inv is a left-inverse of mfderiv (g∘f) x.
    -- Combined with hgf.inv being a left-inverse, by uniqueness, they coincide.
    have hL : (hf'.inv.comp hg'.inv).comp (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (g ∘ f) x) =
        ContinuousLinearMap.id ℂ (TangentSpace 𝓘(ℂ, ℂ) x) := by
      rw [hmf_comp]
      -- ((hf'.inv ∘ hg'.inv) ∘ (Dg ∘ Df))
      --   = (hf'.inv ∘ ((hg'.inv ∘ Dg) ∘ Df))  by associativity
      --   = (hf'.inv ∘ (id ∘ Df))              by hg'.left_inv
      --   = (hf'.inv ∘ Df) = id                by hf'.left_inv
      rw [show (hf'.inv.comp hg'.inv).comp
          ((mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) g (f x)).comp
            (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x)) =
          hf'.inv.comp ((hg'.inv.comp (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) g (f x))).comp
            (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x)) from by
        ext; simp [ContinuousLinearMap.comp_apply]]
      rw [hg'.left_inv]
      rw [ContinuousLinearMap.id_comp]
      exact hf'.left_inv
    -- Now invoke uniqueness: any two left-inverses agree (here `hgf.inv` is one
    -- via hgf.left_inv, and `hf'.inv.comp hg'.inv` is another via hL).
    have hgf_left : hgf.inv.comp (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (g ∘ f) x) =
        ContinuousLinearMap.id ℂ (TangentSpace 𝓘(ℂ, ℂ) x) := hgf.left_inv
    -- A left inverse of an isomorphism (hgf has a two-sided inverse) is unique.
    -- m₁ = m₁ ∘ id = m₁ ∘ (f ∘ hgf.inv) = (m₁ ∘ f) ∘ hgf.inv = id ∘ hgf.inv = hgf.inv.
    -- Direct argument: hgf.inv = id_x.comp hgf.inv = (hL_inv ∘ d(g∘f)).comp hgf.inv
    --                          = hL_inv.comp (d(g∘f) ∘ hgf.inv) = hL_inv.comp id = hL_inv.
    have hgf_right : (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (g ∘ f) x).comp hgf.inv =
        ContinuousLinearMap.id ℂ (TangentSpace 𝓘(ℂ, ℂ) ((g ∘ f) x)) := hgf.right_inv
    have hkey :
        ((hf'.inv.comp hg'.inv).comp (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (g ∘ f) x)).comp hgf.inv =
          hf'.inv.comp hg'.inv := by
      rw [ContinuousLinearMap.comp_assoc, hgf_right]
      ext; simp
    calc hgf.inv
        = (ContinuousLinearMap.id ℂ (TangentSpace 𝓘(ℂ, ℂ) x)).comp hgf.inv := by
          ext; simp
      _ = ((hf'.inv.comp hg'.inv).comp (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (g ∘ f) x)).comp hgf.inv := by
          rw [hL]
      _ = hf'.inv.comp hg'.inv := hkey
  rw [hinv_eq]
  ext
  simp [ContinuousLinearMap.comp_apply]

/-- Additivity of `cotangentPushforward` over a finite attached sum. -/
theorem cotangentPushforward_sum_attachU
    (g : Y → Z) (y : Y) {α : Type*} (s : Finset α)
    (φ : α → CotangentSpace ℂ Y y) :
    cotangentPushforward g y (∑ a ∈ s, φ a) =
      ∑ a ∈ s, cotangentPushforward g y (φ a) := by
  classical
  unfold cotangentPushforward
  by_cases h : Nonempty (IsIso (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) g y))
  · simp only [dif_pos h]
    -- (∑ a, φ a).comp inv = ∑ a, (φ a).comp inv
    induction s using Finset.induction_on with
    | empty => simp
    | insert _ _ hni ih =>
      rw [Finset.sum_insert hni, Finset.sum_insert hni, ← ih]
      ext
      simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply]
  · simp only [dif_neg h]
    rw [Finset.sum_const_zero]

end JacobianChallenge.TraceDegree.CotangentPushforwardCompU
