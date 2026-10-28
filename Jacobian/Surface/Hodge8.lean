import Jacobian.Surface.Hodge7

/-!
# Hodge decomposition, part 8: the global solution

* `reg_compat`: the local smooth solutions agree across charts.
* `exists_dbar_solution`: a smooth `(0,1)`-form in the `L²` closure of `{∂̄u}` is `∂̄u` for a smooth
  `u`.
* **`hodge_decomp`**: every smooth `(0,1)`-form on a compact connected Riemann surface is
  `∂̄u + ν̄` with `u` smooth and `ν` a holomorphic 1-form.
-/

set_option linter.unusedSectionVars false

namespace JacobianChallenge.Surface

open JacobianChallenge.Analysis JacobianChallenge.Periods JacobianChallenge.HolomorphicForms
  MeasureTheory Set Metric Filter Topology Complex
open scoped Manifold ContDiff InnerProductSpace

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] [T2Space X]

namespace DiscAtlas

variable (A : DiscAtlas X)

/-- **Compatibility** of the local solutions across charts. -/
theorem reg_compat (k l : Fin A.N) {u : ℕ → X → ℂ} (hu : ∀ n, IsSmooth (u n)) (c : ℕ → ℂ)
    {Vk Vl Sk Sl : ℂ → ℂ} (hVki : IntegrableOn Vk (A.Q k)) (hVli : IntegrableOn Vl (A.Q l))
    (hVk : L1Conv (fun n w => rd (u n) (A.p k) w - c n) Vk (A.Q k))
    (hVl : L1Conv (fun n w => rd (u n) (A.p l) w - c n) Vl (A.Q l))
    (hSk : ContDiffOn ℝ ∞ Sk (A.Qo k)) (hSl : ContDiffOn ℝ ∞ Sl (A.Qo l))
    (hk : ∀ᵐ w, w ∈ A.Qo k → Vk w = Sk w) (hl : ∀ᵐ w, w ∈ A.Qo l → Vl w = Sl w)
    {w : ℂ} (hw : w ∈ A.Qo k) (hwo : w ∈ overlap (A.p k) (A.p l))
    (hwl : trans (A.p k) (A.p l) w ∈ A.Qo l) :
    Sk w = Sl (trans (A.p k) (A.p l) w) := by
  set τ := trans (A.p k) (A.p l)
  have hτco : ContinuousOn τ (overlap (A.p k) (A.p l)) := fun v hv =>
    (trans_differentiableAt hv).continuousAt.continuousWithinAt
  set W := A.Qo k ∩ (overlap (A.p k) (A.p l) ∩ τ ⁻¹' A.Qo l)
  have hWo : IsOpen W := (A.isOpen_Qo k).inter (hτco.isOpen_inter_preimage (isOpen_overlap _ _)
    (A.isOpen_Qo l))
  obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp hWo w ⟨hw, hwo, hwl⟩
  set B := closedBall w (ε / 2)
  have hBW : B ⊆ W := (closedBall_subset_ball (by linarith)).trans hεW
  have hBc : IsCompact B := isCompact_closedBall _ _
  have hBm : MeasurableSet B := measurableSet_closedBall
  have hBo : ∀ v ∈ B, v ∈ overlap (A.p k) (A.p l) := fun v hv => (hBW hv).2.1
  have hBQo : B ⊆ A.Qo k := fun v hv => (hBW hv).1
  have hτd : ∀ v ∈ B, DifferentiableAt ℂ τ v := fun v hv => trans_differentiableAt (hBo v hv)
  have hτ'c : ContinuousOn (deriv τ) B := fun v hv =>
    (deriv_trans_differentiableAt (hBo v hv)).continuousAt.continuousWithinAt
  have hτB : τ '' B ⊆ A.Qo l := by rintro _ ⟨v, hv, rfl⟩; exact (hBW hv).2.2
  have hτBc : IsCompact (τ '' B) :=
    hBc.image_of_continuousOn fun v hv => (hτd v hv).continuousAt.continuousWithinAt
  have hQkt : A.Q k ⊆ (chartAt ℂ (A.p k)).target :=
    (A.Q_subset_D k).trans (A.D_subset_target k)
  have hQlt : A.Q l ⊆ (chartAt ℂ (A.p l)).target :=
    (A.Q_subset_D l).trans (A.D_subset_target l)
  have hfk : ∀ n, IntegrableOn (fun z => rd (u n) (A.p k) z - c n) (A.Q k) := fun n =>
    ((((hu n) (A.p k)).continuousOn.sub continuousOn_const).mono hQkt).integrableOn_compact
      (A.isCompact_Q k)
  have hfl : ∀ n, IntegrableOn (fun z => rd (u n) (A.p l) z - c n) (A.Q l) := fun n =>
    ((((hu n) (A.p l)).continuousOn.sub continuousOn_const).mono hQlt).integrableOn_compact
      (A.isCompact_Q l)
  have hBQ : B ⊆ A.Q k := hBQo.trans (A.Qo_subset_Q k)
  have hτBQ : τ '' B ⊆ A.Q l := hτB.trans (A.Qo_subset_Q l)
  -- chart `k`
  have h1 : L1Conv (fun n z => rd (u n) (A.p k) z - c n) Sk B :=
    (hVk.mono hBQ hfk hVki).congr hBm (fun _ _ _ => rfl) (by
      filter_upwards [hk] with z hz hzB using hz (hBQo hzB))
  -- chart `l`, on the image of `B`
  have h2 : L1Conv (fun n z => rd (u n) (A.p l) z - c n) Sl (τ '' B) :=
    (hVl.mono hτBQ hfl hVli).congr hτBc.measurableSet (fun _ _ _ => rfl) (by
      filter_upwards [hl] with z hz hzB using hz (hτB hzB))
  have hSlc : ContinuousOn Sl (A.Qo l) := hSl.continuousOn
  have hlt : ∀ n, ContinuousOn (fun v => rd (u n) (A.p l) (τ v)) B := fun n =>
    ((hu n) (A.p l)).continuousOn.comp (fun v hv => (hτd v hv).continuousAt.continuousWithinAt)
      fun v hv => (trans_mem_overlap (hBo v hv)).1
  have hSlt : ContinuousOn (fun v => Sl (τ v)) B :=
    hSlc.comp (fun v hv => (hτd v hv).continuousAt.continuousWithinAt) fun v hv => (hBW hv).2.2
  have h3 := L1Conv.comp_holo (f := fun n z => rd (u n) (A.p l) z - c n) hBc hBm hτd hτ'c
    ((trans_injOn _ _).mono hBo) (fun v hv => deriv_trans_ne_zero (hBo v hv)) subset_rfl
    (fun n => ((hlt n).sub continuousOn_const).sub hSlt)
    (fun n => ((((hu n) (A.p l)).continuousOn.mono (hτB.trans ((A.Qo_subset_Q l).trans hQlt))).sub
      continuousOn_const |>.sub (hSlc.mono hτB)).norm.integrableOn_compact hτBc) h2
  have h4 : L1Conv (fun n z => rd (u n) (A.p k) z - c n) (Sl ∘ τ) B :=
    h3.congr hBm (fun n z hz => by
      simp only [Function.comp_apply]; rw [rd_trans (hBo z hz)]) (ae_of_all _ fun _ _ => rfl)
  have hSkc : ContinuousOn Sk B := hSk.continuousOn.mono hBQo
  have hae := L1Conv.ae_eq (fun n => (hfk n).mono_set hBQ) (hSkc.integrableOn_compact hBc)
    (hSlt.integrableOn_compact hBc) h1 h4
  exact Measure.eqOn_open_of_ae_eq (μ := volume) (U := ball w (ε / 2))
    (ae_restrict_of_ae_restrict_of_subset ball_subset_closedBall hae) isOpen_ball
    (hSkc.mono ball_subset_closedBall) (hSlt.mono ball_subset_closedBall)
    (mem_ball_self (by linarith))

theorem mem_U_iff {k : Fin A.N} {x : X} :
    x ∈ A.U k ↔ x ∈ (chartAt ℂ (A.p k)).source ∧
      chartAt ℂ (A.p k) x ∈ ball (A.ctr k) (A.r k) := Iff.rfl

/-- **Solving `∂̄u = e`** for a smooth `(0,1)`-form `e` in the `L²` closure of `{∂̄u}`. -/
theorem exists_dbar_solution [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    {e : X → ℂ → ℂ} (he : Is01 e) (hes : SmoothFam e) (hE : A.toL2 e hes.contFam ∈ A.E) :
    ∃ u : X → ℂ, IsSmooth u ∧ ∀ q : X, ∀ w ∈ (chartAt ℂ q).target, dbar (rd u q) w = e q w := by
  -- an approximating sequence
  have hE' : A.toL2 e hes.contFam ∈ closure (LinearMap.range A.dbarL : Set A.L2) := by
    rw [← Submodule.topologicalClosure_coe]; exact hE
  obtain ⟨s, hsmem, hslim⟩ := mem_closure_iff_seq_limit.mp hE'
  choose uu huu using hsmem
  set u : ℕ → X → ℂ := fun n => (uu n).1
  have hu : ∀ n, IsSmooth (u n) := fun n => (uu n).2
  have hlim : Tendsto (fun n => A.toL2 (dbarF (u n)) (smoothFam_dbarF (hu n)).contFam) atTop
      (𝓝 (A.toL2 e hes.contFam)) := by
    refine hslim.congr fun n => ?_
    rw [← huu n]; rfl
  -- a base chart
  obtain ⟨x₀⟩ := ‹Nonempty X›
  obtain ⟨k₀, hk₀s, hk₀b⟩ := A.cover x₀
  have hk₀ : (A.U k₀).Nonempty := ⟨x₀, hk₀s, hk₀b⟩
  set c : ℕ → ℂ := fun n => A.mean k₀ (u n)
  -- local data on every chart meeting `X`
  have hdata : ∀ k, (A.U k).Nonempty → ∃ S : ℂ → ℂ, ∃ V : ℂ → ℂ,
      ContDiffOn ℝ ∞ S (A.Qo k) ∧ (∀ w ∈ A.Qo k, dbar S w = e (A.p k) w) ∧
      IntegrableOn V (A.Q k) ∧ L1Conv (fun n w => rd (u n) (A.p k) w - c n) V (A.Q k) ∧
      ∀ᵐ w, w ∈ A.Qo k → V w = S w := by
    intro k hk
    obtain ⟨V, hVi, hV⟩ := A.reg_limit k₀ hk₀ k hk hu hlim
    obtain ⟨S, hS1, hS2, hS3⟩ := A.reg_smooth k he hes hu hlim hVi hV
    exact ⟨S, V, hS1, hS2, hVi, hV, hS3⟩
  choose S V hS1 hS2 hVi hV hS3 using hdata
  -- the compatibility of the local solutions
  have hcomp : ∀ k l (hk : (A.U k).Nonempty) (hl : (A.U l).Nonempty), ∀ w ∈ A.Qo k,
      w ∈ overlap (A.p k) (A.p l) → trans (A.p k) (A.p l) w ∈ A.Qo l →
      S k hk w = S l hl (trans (A.p k) (A.p l) w) := fun k l hk hl w hw hwo hwl =>
    A.reg_compat k l hu c (hVi k hk) (hVi l hl) (hV k hk) (hV l hl) (hS1 k hk) (hS1 l hl)
      (hS3 k hk) (hS3 l hl) hw hwo hwl
  -- the global function
  choose kx hkx using fun x => A.cover x
  have hgood : ∀ x, (A.U (kx x)).Nonempty := fun x => ⟨x, hkx x⟩
  set U : X → ℂ := fun x => S (kx x) (hgood x) (chartAt ℂ (A.p (kx x)) x)
  have hUloc : ∀ x k (hk : x ∈ A.U k), U x = S k ⟨x, hk⟩ (chartAt ℂ (A.p k) x) := by
    intro x k hk
    have h1 : chartAt ℂ (A.p (kx x)) x ∈ A.Qo (kx x) := A.ball_subset_Qo _ (hkx x).2
    have hov : chartAt ℂ (A.p (kx x)) x ∈ overlap (A.p (kx x)) (A.p k) :=
      ⟨(chartAt ℂ (A.p (kx x))).map_source (hkx x).1, by
        show (chartAt ℂ (A.p (kx x))).symm (chartAt ℂ (A.p (kx x)) x) ∈ (chartAt ℂ (A.p k)).source
        rw [(chartAt ℂ (A.p (kx x))).left_inv (hkx x).1]; exact hk.1⟩
    have htr : trans (A.p (kx x)) (A.p k) (chartAt ℂ (A.p (kx x)) x) = chartAt ℂ (A.p k) x := by
      show chartAt ℂ (A.p k) ((chartAt ℂ (A.p (kx x))).symm (chartAt ℂ (A.p (kx x)) x)) = _
      rw [(chartAt ℂ (A.p (kx x))).left_inv (hkx x).1]
    have := hcomp (kx x) k (hgood x) ⟨x, hk⟩ _ h1 hov (by rw [htr]; exact A.ball_subset_Qo k hk.2)
    rw [htr] at this
    exact this
  -- `rd U (p k) = S k` near the chart image of `U k`
  have hrd : ∀ x k (hk : x ∈ A.U k),
      rd U (A.p k) =ᶠ[𝓝 (chartAt ℂ (A.p k) x)] S k ⟨x, hk⟩ := by
    intro x k hk
    have hxt := (chartAt ℂ (A.p k)).map_source hk.1
    have hopen : IsOpen ((chartAt ℂ (A.p k)).target ∩ (chartAt ℂ (A.p k)).symm ⁻¹' A.U k) :=
      (chartAt ℂ (A.p k)).isOpen_inter_preimage_symm (A.isOpen_U k)
    have hmem : chartAt ℂ (A.p k) x ∈
        (chartAt ℂ (A.p k)).target ∩ (chartAt ℂ (A.p k)).symm ⁻¹' A.U k := by
      refine ⟨hxt, ?_⟩
      rw [mem_preimage, (chartAt ℂ (A.p k)).left_inv hk.1]
      exact hk
    filter_upwards [hopen.mem_nhds hmem] with v hv
    rw [rd_apply, hUloc _ k hv.2, (chartAt ℂ (A.p k)).right_inv hv.1]
  have hUs : IsSmooth U := by
    refine isSmooth_of_local fun x => ⟨A.p (kx x), (hkx x).1, ?_⟩
    have hQo : chartAt ℂ (A.p (kx x)) x ∈ A.Qo (kx x) := A.ball_subset_Qo _ (hkx x).2
    exact ((hS1 _ (hgood x)).contDiffAt ((A.isOpen_Qo _).mem_nhds hQo)).congr_of_eventuallyEq
      (hrd x (kx x) (hkx x))
  refine ⟨U, hUs, fun q w hw => ?_⟩
  set x := (chartAt ℂ q).symm w
  set k := kx x
  have hwo : w ∈ overlap q (A.p k) := ⟨hw, (hkx x).1⟩
  have h1 := dbarF_is01 hUs q (A.p k) w hwo
  simp only [dbarF] at h1
  rw [h1, he q (A.p k) w hwo]
  congr 1
  have htr : trans q (A.p k) w = chartAt ℂ (A.p k) x := rfl
  rw [htr, dbar_congr (hrd x k (hkx x)), hS2 _ (hgood x) _ (A.ball_subset_Qo _ (hkx x).2)]

include A in
/-- **Hodge decomposition of `(0,1)`-forms.** On a compact connected Riemann surface every smooth
`(0,1)`-form `θ` is `∂̄u + ν̄`, with `u` smooth and `ν` a holomorphic 1-form. -/
theorem hodge_decomp [CompactSpace X] [ConnectedSpace X] {θ : X → ℂ → ℂ} (hθ : Is01 θ)
    (hθs : SmoothFam θ) :
    ∃ u : X → ℂ, IsSmooth u ∧ ∃ ν : HolomorphicOneForm ℂ X,
      ∀ q : X, ∀ w ∈ (chartAt ℂ q).target,
        θ q w = dbar (rd u q) w + (starRingEnd ℂ) (chartCoeff q ν w) := by
  obtain ⟨ν, hc, hmem⟩ := A.exists_holo_residue hθ hθs
  rcases isEmpty_or_nonempty X with hX | hX
  · exact ⟨0, isSmooth_const 0, ν, fun q => (hX.false q).elim⟩
  have he : Is01 (θ - conjF (holoF ν)) := hθ.sub (holoF_is10 ν).conjF
  have hes : SmoothFam (θ - conjF (holoF ν)) := hθs.sub (smoothFam_holoF ν).conjF
  obtain ⟨u, hu, hdu⟩ := A.exists_dbar_solution he hes hmem
  refine ⟨u, hu, ν, fun q w hw => ?_⟩
  rw [hdu q w hw]
  simp [conjF, holoF]

end DiscAtlas

/-- **Hodge decomposition of `(0,1)`-forms** (atlas-free statement). -/
theorem hodge_decomp [CompactSpace X] [ConnectedSpace X] {θ : X → ℂ → ℂ} (hθ : Is01 θ)
    (hθs : SmoothFam θ) :
    ∃ u : X → ℂ, IsSmooth u ∧ ∃ ν : HolomorphicOneForm ℂ X,
      ∀ q : X, ∀ w ∈ (chartAt ℂ q).target,
        θ q w = dbar (rd u q) w + (starRingEnd ℂ) (chartCoeff q ν w) :=
  (exists_discAtlas (X := X)).some.hodge_decomp hθ hθs

end JacobianChallenge.Surface
