import Jacobian.TraceDegree.RegularValueCompU

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped Manifold ContDiff Topology
open JacobianChallenge.TraceDegree
open JacobianChallenge.TraceDegree.RegularValueCompU
open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods
open Classical

namespace JacobianChallenge.TraceDegree.TraceFormsBundledCompU

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

theorem traceFormsBundled_comp_of_nonconstantU
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (η : HolomorphicOneForm ℂ X)
    (_hη : η ≠ 0)
    (hf_nonconst : ¬ ∃ y₀, ∀ x, f x = y₀)
    (hg_nonconst : ¬ ∃ z₀, ∀ y, g y = z₀) :
    traceFormsBundled (g ∘ f) (hg.comp hf) η =
      traceFormsBundled g hg (traceFormsBundled f hf η) := by
  classical
  -- Construct canonical branched-cover data for f, g, and g∘f.
  set hkfold_f := hasLocalKfoldRamification_of_contMDiff hf
  set hw_f := hasWeightedFiberConservation_of_contMDiff hf
  set hHol_f := isHolomorphic_of_contMDiff hf hkfold_f
  set hbc_f := JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic
    hHol_f hw_f hf_nonconst
  set hkfold_g := hasLocalKfoldRamification_of_contMDiff hg
  set hw_g := hasWeightedFiberConservation_of_contMDiff hg
  set hHol_g := isHolomorphic_of_contMDiff hg hkfold_g
  set hbc_g := JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic
    hHol_g hw_g hg_nonconst
  -- (g ∘ f) is nonconstant.
  have hgf_nonconst : ¬ ∃ w₀, ∀ x, (g ∘ f) x = w₀ := by
    rintro ⟨w₀, hw⟩
    -- If g∘f is constant w₀, then f(x) ∈ g⁻¹{w₀} for all x : X.
    -- g⁻¹{w₀} is finite (g nonconstant holomorphic on compact connected source);
    -- so range f is finite. range f is connected (X connected, f continuous).
    -- A connected finite set in a T1 space is a singleton.
    have hgw_finite : (g ⁻¹' {w₀}).Finite :=
      isHolomorphic_finite_fiber hHol_g hg_nonconst w₀
    have hfX_sub : Set.range f ⊆ g ⁻¹' {w₀} := by
      rintro y ⟨x, rfl⟩
      show g (f x) = w₀
      exact hw x
    have hfX_finite : (Set.range f).Finite :=
      hgw_finite.subset hfX_sub
    have hfX_preconnected : IsPreconnected (Set.range f) :=
      (isConnected_range hHol_f.continuous).isPreconnected
    -- Subsingleton via closed separation `isPreconnected_closed_iff`.
    have hfX_subsingleton : (Set.range f).Subsingleton := by
      intro a ha b hb
      by_contra hab
      -- t = {a}, t' = (range f) \ {a}; both closed in Y (T1 + finite).
      have hT1 : T1Space Y := inferInstance
      have ht_closed : IsClosed ({a} : Set Y) := isClosed_singleton
      have ht'_closed : IsClosed ((Set.range f) \ ({a} : Set Y)) :=
        (hfX_finite.subset Set.diff_subset).isClosed
      have hsub : Set.range f ⊆ ({a} : Set Y) ∪ ((Set.range f) \ ({a} : Set Y)) := by
        intro y hy
        by_cases h : y = a
        · left; exact h
        · right; exact ⟨hy, fun heq => h (Set.mem_singleton_iff.mp heq)⟩
      have ha_nonempty : (Set.range f ∩ ({a} : Set Y)).Nonempty := ⟨a, ha, rfl⟩
      have hb_nonempty : (Set.range f ∩ ((Set.range f) \ ({a} : Set Y))).Nonempty :=
        ⟨b, hb, hb, fun heq => hab (Set.mem_singleton_iff.mp heq).symm⟩
      have hjoint :=
        (isPreconnected_closed_iff.mp hfX_preconnected) _ _
          ht_closed ht'_closed hsub ha_nonempty hb_nonempty
      -- But ({a}) ∩ ((range f) \ {a}) = ∅.
      obtain ⟨y, _, hy_a, _, hy_ne⟩ := hjoint
      exact hy_ne hy_a
    apply hf_nonconst
    refine ⟨f (Classical.arbitrary X), fun x => ?_⟩
    exact hfX_subsingleton ⟨x, rfl⟩ ⟨Classical.arbitrary X, rfl⟩
  set hkfold_gf := hasLocalKfoldRamification_of_contMDiff (hg.comp hf)
  set hw_gf := hasWeightedFiberConservation_of_contMDiff (hg.comp hf)
  set hHol_gf := isHolomorphic_of_contMDiff (hg.comp hf) hkfold_gf
  set hbc_gf := JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic
    hHol_gf hw_gf hgf_nonconst
  -- The joint dense locus: z is regular for hbc_gf, regular for hbc_g, and
  -- each y ∈ g⁻¹(z) is regular for hbc_f.
  let S : Set Z := {z | isRegularValue hbc_gf z ∧ isRegularValue hbc_g z
    ∧ ∀ y ∈ g ⁻¹' {z}, isRegularValue hbc_f y}
  -- Density of S: complement is union of three finite sets.
  have hS_dense : Dense S := by
    -- S = (regularLocus hbc_gf) ∩ (regularLocus hbc_g) ∩ {z | ∀ y ∈ g⁻¹{z}, isRegularValue hbc_f y}
    -- The third set has complement equal to g '' (branchLocus hbc_f), which is finite.
    have h1_compl_finite : {z : Z | ¬ isRegularValue hbc_gf z}.Finite :=
      branchLocus_finite hbc_gf
    have h2_compl_finite : {z : Z | ¬ isRegularValue hbc_g z}.Finite :=
      branchLocus_finite hbc_g
    have h3_compl_finite :
        {z : Z | ¬ ∀ y ∈ g ⁻¹' {z}, isRegularValue hbc_f y}.Finite := by
      -- Complement = {z | ∃ y, g y = z ∧ ¬ isRegularValue hbc_f y}
      --           = g '' {y | ¬ isRegularValue hbc_f y}
      have heq : {z : Z | ¬ ∀ y ∈ g ⁻¹' {z}, isRegularValue hbc_f y} =
          g '' {y : Y | ¬ isRegularValue hbc_f y} := by
        ext z
        constructor
        · intro hz
          simp only [Set.mem_setOf_eq, not_forall, Set.mem_preimage,
            Set.mem_singleton_iff] at hz
          obtain ⟨y, hgy, hyne⟩ := hz
          exact ⟨y, hyne, hgy⟩
        · rintro ⟨y, hyne, hgy⟩
          simp only [Set.mem_setOf_eq, not_forall, Set.mem_preimage,
            Set.mem_singleton_iff]
          exact ⟨y, hgy, hyne⟩
      rw [heq]
      exact (branchLocus_finite hbc_f).image g
    -- S = (S₁ᶜ)ᶜ \ ... — use complement decomposition.
    have hcompl : Sᶜ ⊆ {z : Z | ¬ isRegularValue hbc_gf z} ∪
        {z : Z | ¬ isRegularValue hbc_g z} ∪
        {z : Z | ¬ ∀ y ∈ g ⁻¹' {z}, isRegularValue hbc_f y} := by
      intro z hz
      by_contra hcontra
      -- hcontra : z ∉ (... ∪ ... ∪ ...). So z is in none of the three complements.
      have hn1 : isRegularValue hbc_gf z := by
        by_contra h
        exact hcontra (Or.inl (Or.inl h))
      have hn2 : isRegularValue hbc_g z := by
        by_contra h
        exact hcontra (Or.inl (Or.inr h))
      have hn3 : ∀ y ∈ g ⁻¹' {z}, isRegularValue hbc_f y := by
        by_contra h
        exact hcontra (Or.inr h)
      exact hz ⟨hn1, hn2, hn3⟩
    have hSc_finite : Sᶜ.Finite :=
      Set.Finite.subset ((h1_compl_finite.union h2_compl_finite).union
        h3_compl_finite) hcompl
    -- Dense complement of finite set in perfect target.
    haveI : Nontrivial Z := by
      obtain ⟨p, q, hpq⟩ := exists_two_distinct_points_of_chartedSpaceComplex (X := Z)
      exact ⟨⟨p, q, hpq⟩⟩
    haveI : PerfectSpace Z := inferInstance
    have hSc_compl_dense : Dense ((Sᶜ : Set Z)ᶜ) :=
      dense_compl_of_finite_of_perfect hSc_finite
    simpa [compl_compl] using hSc_compl_dense
  -- Compatibility witnesses for each of the three canonical BCDs.
  have hcompat_f : hbc_f.RamificationIndexCompatible :=
    JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic_compatible
      hHol_f hw_f hf_nonconst
  have hcompat_g : hbc_g.RamificationIndexCompatible :=
    JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic_compatible
      hHol_g hw_g hg_nonconst
  have hcompat_gf : hbc_gf.RamificationIndexCompatible :=
    JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic_compatible
      hHol_gf hw_gf hgf_nonconst
  -- Identity principle on S.
  apply holomorphicOneForm_ext_on hS_dense
  rintro z ⟨hz_gf, hz_g, hz_g_inv⟩
  -- LHS: trace at z via hbc_gf.
  have hLHS_reg :=
    (traceFormsConstructionData_provider (g ∘ f) (hg.comp hf) η).regular_spec
      hbc_gf hcompat_gf z hz_gf
  -- RHS: trace at z via hbc_g, applied to (traceFormsBundled f hf η).
  have hRHS_reg :=
    (traceFormsConstructionData_provider g hg
      (traceFormsBundled f hf η)).regular_spec hbc_g hcompat_g z hz_g
  -- Translate to traceFormsBundled.
  change (traceFormsBundled (g ∘ f) (hg.comp hf) η).toFun z =
    (traceFormsBundled g hg (traceFormsBundled f hf η)).toFun z
  -- Unfold using the provider's traceForm.
  show (traceFormsConstructionData_provider (g ∘ f) (hg.comp hf) η).traceForm.toFun z =
    (traceFormsConstructionData_provider g hg
      (traceFormsBundled f hf η)).traceForm.toFun z
  rw [hLHS_reg, hRHS_reg]
  exact regularValue_comp_traceAtRegularValueU f hf g hg η
    hbc_f hcompat_f hbc_g hcompat_g hbc_gf hcompat_gf hHol_f hHol_g hHol_gf
    z hz_gf hz_g hz_g_inv

/-- **Form-level composition functoriality of the bundled trace.** -/
theorem traceFormsBundledLM_comp_genuineU
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) :
    traceFormsBundledLM (X := X) (Y := Z) (g ∘ f) (hg.comp hf) =
      (traceFormsBundledLM (X := Y) (Y := Z) g hg).comp
        (traceFormsBundledLM (X := X) (Y := Y) f hf) := by
  apply LinearMap.ext
  intro η
  show traceFormsBundled (g ∘ f) (hg.comp hf) η =
    traceFormsBundled g hg (traceFormsBundled f hf η)
  -- Case split on η = 0.
  by_cases hη : η = 0
  · subst hη
    show traceFormsBundledLM (g ∘ f) (hg.comp hf) 0 =
      traceFormsBundledLM g hg (traceFormsBundledLM f hf 0)
    rw [(traceFormsBundledLM (g ∘ f) (hg.comp hf)).map_zero,
        (traceFormsBundledLM f hf).map_zero,
        (traceFormsBundledLM g hg).map_zero]
  · -- η ≠ 0. Case split on f constant.
    by_cases hf_const : ∃ y₀, ∀ x, f x = y₀
    · -- f constant ⇒ g ∘ f constant; trace along constant map is 0.
      obtain ⟨y₀, hf_eq⟩ := hf_const
      have hgf_const : ∃ z₀, ∀ x, (g ∘ f) x = z₀ :=
        ⟨g y₀, fun x => by show g (f x) = g y₀; rw [hf_eq x]⟩
      rw [traceFormsBundled_eq_zero_of_constant
            (f := g ∘ f) (hf := hg.comp hf) η hgf_const,
          traceFormsBundled_eq_zero_of_constant (f := f) (hf := hf) η ⟨y₀, hf_eq⟩]
      show (0 : HolomorphicOneForm ℂ Z) = traceFormsBundledLM g hg 0
      rw [(traceFormsBundledLM g hg).map_zero]
    · -- f nonconstant. Case split on g constant.
      by_cases hg_const : ∃ z₀, ∀ y, g y = z₀
      · -- g constant ⇒ g ∘ f constant; both sides 0.
        obtain ⟨z₀, hg_eq⟩ := hg_const
        have hgf_const : ∃ z₀, ∀ x, (g ∘ f) x = z₀ :=
          ⟨z₀, fun x => hg_eq (f x)⟩
        rw [traceFormsBundled_eq_zero_of_constant
              (f := g ∘ f) (hf := hg.comp hf) η hgf_const,
            traceFormsBundled_eq_zero_of_constant (f := g) (hf := hg)
              (traceFormsBundled f hf η) ⟨z₀, hg_eq⟩]
      · 
        exact traceFormsBundled_comp_of_nonconstantU f hf g hg η hη hf_const hg_const

end JacobianChallenge.TraceDegree.TraceFormsBundledCompU
