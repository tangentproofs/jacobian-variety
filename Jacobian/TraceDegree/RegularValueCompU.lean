import Jacobian.TraceDegree.CotangentPushforwardCompU

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped Manifold ContDiff Topology
open JacobianChallenge.TraceDegree
open JacobianChallenge.TraceDegree.CotangentPushforwardCompU
open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods
open Classical

namespace JacobianChallenge.TraceDegree.RegularValueCompU

universe u v w
variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [FiniteDimensionalHolomorphicOneForms ℂ X]

variable {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [ConnectedSpace Y] [ChartedSpace ℂ Y]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y]
  [FiniteDimensionalHolomorphicOneForms ℂ Y]

variable {Z : Type w} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z]
  [ConnectedSpace Z] [ChartedSpace ℂ Z]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Z]
  [FiniteDimensionalHolomorphicOneForms ℂ Z]

theorem regularValue_comp_traceAtRegularValueU
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (η : HolomorphicOneForm ℂ X)
    (hbc_f : BranchedCoverData X Y f) (hcompat_f : hbc_f.RamificationIndexCompatible)
    (hbc_g : BranchedCoverData Y Z g) (hcompat_g : hbc_g.RamificationIndexCompatible)
    (hbc_gf : BranchedCoverData X Z (g ∘ f)) (hcompat_gf : hbc_gf.RamificationIndexCompatible)
    (hHol_f : IsHolomorphic f) (hHol_g : IsHolomorphic g)
    (hHol_gf : IsHolomorphic (g ∘ f))
    (z : Z)
    (hz_gf : isRegularValue hbc_gf z)
    (hz_g : isRegularValue hbc_g z)
    (hz_g_inv_regular : ∀ y ∈ g ⁻¹' {z}, isRegularValue hbc_f y) :
    traceAtRegularValue hbc_gf (fun x => η.toFun x) z hz_gf =
      traceAtRegularValue hbc_g
        (fun y => (JacobianChallenge.HolomorphicForms.traceFormsBundled f hf η).toFun y)
        z hz_g := by
  classical
  -- Iso of mfderiv at every x ∈ (g∘f)⁻¹{z}.
  have hiso_gf : ∀ x ∈ (g ∘ f) ⁻¹' ({z} : Set Z),
      Nonempty (IsIso (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (g ∘ f) x)) := by
    intro x hx
    exact mfderiv_isIso_of_ramificationIndex_one hbc_gf hcompat_gf hHol_gf (hz_gf x hx)
  -- Iso of mfderiv g at every y ∈ g⁻¹{z}.
  have hiso_g : ∀ y ∈ g ⁻¹' ({z} : Set Z),
      Nonempty (IsIso (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) g y)) := by
    intro y hy
    exact mfderiv_isIso_of_ramificationIndex_one hbc_g hcompat_g hHol_g (hz_g y hy)
  -- Iso of mfderiv f at every x ∈ f⁻¹{y} for y ∈ g⁻¹{z}.
  have hiso_f : ∀ y ∈ g ⁻¹' ({z} : Set Z), ∀ x ∈ f ⁻¹' ({y} : Set Y),
      Nonempty (IsIso (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x)) := by
    intro y hy x hx
    exact mfderiv_isIso_of_ramificationIndex_one hbc_f hcompat_f hHol_f
      (hz_g_inv_regular y hy x hx)
  -- Rewrite RHS inner trace via `regular_spec`.
  -- For each y ∈ g⁻¹{z}, (traceFormsBundled f hf η).toFun y = traceAtRegularValue hbc_f ...
  have hinner_eq : ∀ y, ∀ (hy : y ∈ g ⁻¹' ({z} : Set Z)),
      (JacobianChallenge.HolomorphicForms.traceFormsBundled f hf η).toFun y =
        traceAtRegularValue hbc_f (fun x => η.toFun x) y (hz_g_inv_regular y hy) := by
    intro y hy
    exact (JacobianChallenge.HolomorphicForms.traceFormsConstructionData_provider
      f hf η).regular_spec hbc_f hcompat_f y (hz_g_inv_regular y hy)
  -- Unfold both sides.
  unfold traceAtRegularValue
  -- LHS = ∑_{x ∈ ((g∘f)⁻¹{z}).toFinset.attach} cotangentPushforward (g∘f) x.1 (η.toFun x.1)
  -- RHS = ∑_{y ∈ (g⁻¹{z}).toFinset.attach} cotangentPushforward g y.1
  --         ((traceFormsBundled f hf η).toFun y.1)
  -- After rewriting the inner trace and pushing cotangentPushforward g over the sum,
  -- RHS becomes a double sum that matches LHS via the fiber bijection.
  set Sgf := (hbc_gf.finite_fiber z).toFinset with hSgf_def
  set Sg := (hbc_g.finite_fiber z).toFinset with hSg_def
  -- Rewrite RHS using hinner_eq and cotangentPushforward_sum_attachU.
  -- Annotate result type with the bundle's trivial fiber `ℂ →L[ℂ] ℂ` so the
  -- outer sum sees a non-dependent codomain.
  have hRHS_step :
      (Sg.attach.sum (fun y =>
        (cotangentPushforward g y.1
          ((JacobianChallenge.HolomorphicForms.traceFormsBundled f hf η).toFun y.1)
          : ℂ →L[ℂ] ℂ))) =
      Sg.attach.sum (fun y =>
        ((((hbc_f.finite_fiber y.1).toFinset).attach.sum (fun x =>
          (cotangentPushforward g y.1
            (cotangentPushforward f x.1 (η.toFun x.1)) : ℂ →L[ℂ] ℂ)))
          : ℂ →L[ℂ] ℂ)) := by
    refine Finset.sum_congr rfl ?_
    rintro ⟨y, hy_mem⟩ _
    have hy : y ∈ g ⁻¹' ({z} : Set Z) :=
      (Set.Finite.mem_toFinset _).mp hy_mem
    rw [hinner_eq y hy]
    exact cotangentPushforward_sum_attachU g y _ _
  rw [hRHS_step]
  -- Now we want to show the LHS (single sum over Sgf.attach) equals the RHS (double sum).
  -- Apply Finset.sum_sigma' to flatten the RHS, then Finset.sum_bij from Sgf.attach to the sigma.
  rw [Finset.sum_sigma' (β := (ℂ →L[ℂ] ℂ)) Sg.attach
    (fun y => ((hbc_f.finite_fiber y.1).toFinset).attach)
    (fun y x => (cotangentPushforward g y.1
      (cotangentPushforward f x.1 (η.toFun x.1)) : ℂ →L[ℂ] ℂ))]
  -- LHS (now): single sum over x ∈ Sgf.attach
  -- RHS: sigma sum
  -- Apply Finset.sum_bij with forward x ↦ ⟨⟨f x.1, _⟩, ⟨x.1, _⟩⟩.
  refine Finset.sum_bij
    (fun (x : { a // a ∈ Sgf })
        (_hx : x ∈ Sgf.attach) =>
      let hxz : (g ∘ f) x.1 = z := by
        have : x.1 ∈ (g ∘ f) ⁻¹' ({z} : Set Z) :=
          (Set.Finite.mem_toFinset _).mp x.2
        exact this
      let hy_mem : f x.1 ∈ Sg := by
        rw [hSg_def, Set.Finite.mem_toFinset]
        show g (f x.1) = z
        exact hxz
      let hx_mem : x.1 ∈ (hbc_f.finite_fiber (f x.1)).toFinset := by
        rw [Set.Finite.mem_toFinset]
        show f x.1 = f x.1
        rfl
      (⟨⟨f x.1, hy_mem⟩, ⟨x.1, hx_mem⟩⟩ :
        (y : { y // y ∈ Sg }) ×
          { a // a ∈ ((hbc_f.finite_fiber y.1).toFinset) }))
    ?_ ?_ ?_ ?_
  · -- maps into target
    intro x _
    simp [Finset.mem_sigma, Finset.mem_attach]
  · -- injective
    intro x _ x' _ hxx
    have h2 : x.1 = x'.1 := by
      have := congr_arg
        (fun (p : (y : { y // y ∈ Sg }) ×
            { a // a ∈ ((hbc_f.finite_fiber y.1).toFinset) }) => p.2.1) hxx
      simpa using this
    exact Subtype.ext h2
  · -- surjective
    rintro ⟨⟨y, hy_mem⟩, ⟨x, hx_mem⟩⟩ hmem
    have hy : g y = z :=
      (show y ∈ g ⁻¹' ({z} : Set Z) from
        (Set.Finite.mem_toFinset (hbc_g.finite_fiber z)).mp hy_mem)
    have hxy : f x = y :=
      (show x ∈ f ⁻¹' ({y} : Set Y) from
        (Set.Finite.mem_toFinset (hbc_f.finite_fiber y)).mp hx_mem)
    have hxz : x ∈ Sgf := by
      show x ∈ (hbc_gf.finite_fiber z).toFinset
      rw [Set.Finite.mem_toFinset]
      show g (f x) = z
      rw [hxy]
      exact hy
    refine ⟨⟨x, hxz⟩, Finset.mem_attach _ _, ?_⟩
    -- Show forward map sends ⟨x, hxz⟩ to ⟨⟨y, hy_mem⟩, ⟨x, hx_mem⟩⟩.
    refine Sigma.subtype_ext ?_ ?_
    · simp [hxy]
    · simp
  · -- values match: chain rule
    intro x _
    have hxz : (g ∘ f) x.1 = z :=
      (show x.1 ∈ (g ∘ f) ⁻¹' ({z} : Set Z) from
        (Set.Finite.mem_toFinset (hbc_gf.finite_fiber z)).mp x.2)
    have hfx_mem : f x.1 ∈ g ⁻¹' ({z} : Set Z) := hxz
    have hx_mem_ff : x.1 ∈ f ⁻¹' ({f x.1} : Set Y) := rfl
    have hf_iso : Nonempty (IsIso (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x.1)) :=
      hiso_f (f x.1) hfx_mem x.1 hx_mem_ff
    have hg_iso : Nonempty (IsIso (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) g (f x.1))) :=
      hiso_g (f x.1) hfx_mem
    -- Unfold the forward map's let-bindings via `show`, then apply chain rule.
    show cotangentPushforward (g ∘ f) x.1 ((fun x => η.toFun x) x.1) =
      cotangentPushforward g (f x.1)
        (cotangentPushforward f x.1 (η.toFun x.1))
    exact (cotangentPushforward_compU f g hf hg x.1 hf_iso hg_iso (η.toFun x.1))

end JacobianChallenge.TraceDegree.RegularValueCompU
