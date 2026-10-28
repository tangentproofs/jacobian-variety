import Jacobian.Surface.Forms

/-!
# Holomorphic 1-forms from compatible chart coefficients

`mkHoloForm`: a `(1,0)`-family `g` (`g_p = τ' g_q ∘ τ`) whose readings are holomorphic on the
chart targets defines a holomorphic 1-form with `chartCoeff p ν = g p` (`chartCoeff_mkHoloForm`).

`exists_holoForm_of_atlas`: compatible holomorphic coefficients on open sets of finitely many
charts covering `X` come from a holomorphic 1-form.
-/

set_option linter.unusedSectionVars false

namespace JacobianChallenge.Surface

open JacobianChallenge.Analysis JacobianChallenge.Periods JacobianChallenge.HolomorphicForms
  MeasureTheory Set Metric Filter Topology Complex
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] [T2Space X]

/-- The covector field `x ↦ g_x(c_x x) dz`. -/
noncomputable def mkSection (g : X → ℂ → ℂ) (x : X) : CotangentSpace ℂ X x :=
  coordCovector x (g x (chartAt ℂ x x))

theorem mkSection_read {g : X → ℂ → ℂ} (hg : Is10 g) (q : X) {w : ℂ}
    (hw : w ∈ (chartAt ℂ q).target) :
    toLc (mkSection g ((chartAt ℂ q).symm w))
      (toL (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (chartAt ℂ q).symm w) 1) = g q w := by
  set x := (chartAt ℂ q).symm w with hx
  have hxs : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  have hwo : w ∈ overlap q x := ⟨hw, hxs⟩
  have hid : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) (id : X → X) := contMDiff_id
  have hfd : fderiv ℂ (trans q x) w 1 =
      toL (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (chartAt ℂ x) x)
        (toL (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (chartAt ℂ q).symm w) 1) := by
    rw [chartMap_fderiv hid hw hxs, mfderiv_id]; rfl
  have htx : trans q x w = chartAt ℂ x x := rfl
  rw [hg q x w hwo, htx, ← fderiv_apply_one_eq_deriv, hfd]
  show (g x (chartAt ℂ x x) • ContinuousLinearMap.id ℂ ℂ)
      (toL (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (chartAt ℂ x) x)
        (toL (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (chartAt ℂ q).symm w) 1)) = _
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
  ring

theorem mkSection_contMDiff {g : X → ℂ → ℂ} (hg : Is10 g)
    (hh : ∀ p : X, DifferentiableOn ℂ (g p) (chartAt ℂ p).target) :
    ContMDiff 𝓘(ℂ, ℂ) (𝓘(ℂ, ℂ).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) (⊤ : WithTop ℕ∞)
      (fun y => Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ) y (mkSection g y)) := by
  intro y₀
  set cq := chartAt ℂ y₀
  set triv := trivializationAt (ℂ →L[ℂ] ℂ) (CotangentSpace ℂ X) y₀
  have hb : y₀ ∈ triv.baseSet := FiberBundle.mem_baseSet_trivializationAt' y₀
  rw [triv.contMDiffAt_section_iff hb]
  have hc : cq y₀ ∈ cq.target := cq.map_source (mem_chart_source ℂ y₀)
  have han : AnalyticAt ℂ (g y₀) (cq y₀) :=
    (hh y₀).analyticAt (cq.open_target.mem_nhds hc)
  have hG : ContDiffAt ℂ (⊤ : WithTop ℕ∞)
      (fun a : ℂ => g y₀ a • ContinuousLinearMap.id ℂ ℂ) (cq y₀) :=
    (han.smul analyticAt_const).contDiffAt
  have hF : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) (⊤ : WithTop ℕ∞)
      (fun y => g y₀ (cq y) • ContinuousLinearMap.id ℂ ℂ) y₀ :=
    hG.comp_contMDiffAt ((contMDiffOn_chart (I := 𝓘(ℂ, ℂ)) (x := y₀)).contMDiffAt
      (cq.open_source.mem_nhds (mem_chart_source ℂ y₀)))
  have hread : ∀ e ∈ cq.target,
      (triv ⟨cq.symm e, mkSection g (cq.symm e)⟩).2 = g y₀ e • ContinuousLinearMap.id ℂ ℂ := by
    intro e he
    rw [trivCT_read_eq_comp_symmL, ← ChartedFormPullbackContinuous.mfderiv_chartSymm_eq_symmL y₀ he]
    refine ContinuousLinearMap.ext fun v => ?_
    have h := clm_apply_eq_mul ((toLc (mkSection g (cq.symm e))).comp
      (toL (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) cq.symm e))) v
    refine h.trans ?_
    rw [ContinuousLinearMap.comp_apply, mkSection_read hg y₀ he]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    exact mul_comm _ _
  have heq : (fun y => (triv ⟨y, mkSection g y⟩).2) =ᶠ[𝓝 y₀]
      (fun y => g y₀ (cq y) • ContinuousLinearMap.id ℂ ℂ) := by
    filter_upwards [cq.open_source.mem_nhds (mem_chart_source ℂ y₀)] with y hy
    have h := hread (cq y) (cq.map_source hy)
    rw [cq.left_inv hy] at h
    exact h
  exact hF.congr_of_eventuallyEq heq

/-- The holomorphic 1-form with chart readings `g`. -/
noncomputable def mkHoloForm (g : X → ℂ → ℂ) (hg : Is10 g)
    (hh : ∀ p : X, DifferentiableOn ℂ (g p) (chartAt ℂ p).target) : HolomorphicOneForm ℂ X :=
  ⟨mkSection g, mkSection_contMDiff hg hh⟩

theorem chartCoeff_mkHoloForm (g : X → ℂ → ℂ) (hg : Is10 g)
    (hh : ∀ p : X, DifferentiableOn ℂ (g p) (chartAt ℂ p).target) (q : X) {w : ℂ}
    (hw : w ∈ (chartAt ℂ q).target) : chartCoeff q (mkHoloForm g hg hh) w = g q w :=
  mkSection_read hg q hw

theorem deriv_trans_comp {p q r : X} {w : ℂ} (hw : w ∈ overlap p q) (hw' : w ∈ overlap p r) :
    deriv (trans p r) w = deriv (trans q r) (trans p q w) * deriv (trans p q) w := by
  have h1 := trans_differentiableAt hw
  have hq : trans p q w ∈ overlap q r := by
    refine ⟨(trans_mem_overlap hw).1, ?_⟩
    show (chartAt ℂ q).symm (trans p q w) ∈ (chartAt ℂ r).source
    rw [trans_symm_eq hw]; exact hw'.2
  have h2 := trans_differentiableAt hq
  rw [← ((h2.hasDerivAt.comp w h1.hasDerivAt).congr_of_eventuallyEq
    (trans_comp_eventuallyEq hw hw').symm).deriv]

theorem trans_self_eventuallyEq {p : X} {w : ℂ} (hw : w ∈ (chartAt ℂ p).target) :
    trans p p =ᶠ[𝓝 w] id := by
  filter_upwards [(chartAt ℂ p).open_target.mem_nhds hw] with v hv
  exact (chartAt ℂ p).right_inv hv

theorem deriv_trans_self {p : X} {w : ℂ} (hw : w ∈ (chartAt ℂ p).target) :
    deriv (trans p p) w = 1 := by
  rw [(trans_self_eventuallyEq hw).deriv_eq, deriv_id]

/-- Compatible holomorphic chart coefficients on open sets of charts covering `X` come from a
holomorphic 1-form. -/
theorem exists_holoForm_of_local {ι : Type*} (p : ι → X) (O : ι → Set ℂ)
    (hO : ∀ k, IsOpen (O k)) (hOt : ∀ k, O k ⊆ (chartAt ℂ (p k)).target)
    (hcov : ∀ x, ∃ k, x ∈ (chartAt ℂ (p k)).source ∧ chartAt ℂ (p k) x ∈ O k)
    (g : ι → ℂ → ℂ) (hg : ∀ k, DifferentiableOn ℂ (g k) (O k))
    (hcompat : ∀ k l, ∀ w ∈ O k, w ∈ overlap (p k) (p l) → trans (p k) (p l) w ∈ O l →
      g k w = deriv (trans (p k) (p l)) w * g l (trans (p k) (p l) w)) :
    ∃ ν : HolomorphicOneForm ℂ X, ∀ k, ∀ w ∈ O k, chartCoeff (p k) ν w = g k w := by
  choose kx hkx using hcov
  set G : X → ℂ → ℂ := fun q w =>
    deriv (trans q (p (kx ((chartAt ℂ q).symm w)))) w *
      g (kx ((chartAt ℂ q).symm w)) (trans q (p (kx ((chartAt ℂ q).symm w))) w) with hGdef
  -- the local formula, in any admissible chart
  have key : ∀ q w, w ∈ (chartAt ℂ q).target → ∀ k,
      (chartAt ℂ q).symm w ∈ (chartAt ℂ (p k)).source → trans q (p k) w ∈ O k →
      G q w = deriv (trans q (p k)) w * g k (trans q (p k) w) := by
    intro q w hw k hk hkO
    set x := (chartAt ℂ q).symm w
    set k' := kx x
    have hwk' : w ∈ overlap q (p k') := ⟨hw, (hkx x).1⟩
    have hwk : w ∈ overlap q (p k) := ⟨hw, hk⟩
    set v := trans q (p k') w
    have hvO : v ∈ O k' := (hkx x).2
    have hvo : v ∈ overlap (p k') (p k) := by
      refine ⟨(trans_mem_overlap hwk').1, ?_⟩
      show (chartAt ℂ (p k')).symm v ∈ (chartAt ℂ (p k)).source
      rw [trans_symm_eq hwk']; exact hk
    have hvv : trans (p k') (p k) v = trans q (p k) w := by
      show chartAt ℂ (p k) ((chartAt ℂ (p k')).symm v) = chartAt ℂ (p k) x
      rw [trans_symm_eq hwk']
    have hc := hcompat k' k v hvO hvo (by rw [hvv]; exact hkO)
    show deriv (trans q (p k')) w * g k' v = _
    rw [hc, hvv, deriv_trans_comp hwk' hwk]
    ring
  have hIs10 : Is10 G := by
    intro q₁ q₂ w hw
    set x := (chartAt ℂ q₁).symm w
    set k := kx x
    have hwk : w ∈ overlap q₁ (p k) := ⟨hw.1, (hkx x).1⟩
    have h2 : trans q₁ q₂ w ∈ (chartAt ℂ q₂).target := (trans_mem_overlap hw).1
    have h2s : (chartAt ℂ q₂).symm (trans q₁ q₂ w) = x := trans_symm_eq hw
    have h2o : trans q₁ q₂ w ∈ overlap q₂ (p k) := ⟨h2, by
      show (chartAt ℂ q₂).symm (trans q₁ q₂ w) ∈ (chartAt ℂ (p k)).source
      rw [h2s]; exact (hkx x).1⟩
    have htt : trans q₂ (p k) (trans q₁ q₂ w) = trans q₁ (p k) w := by
      show chartAt ℂ (p k) ((chartAt ℂ q₂).symm (trans q₁ q₂ w)) = chartAt ℂ (p k) x
      rw [h2s]
    rw [key q₂ _ h2 k (by rw [h2s]; exact (hkx x).1) (by rw [htt]; exact (hkx x).2), htt]
    show deriv (trans q₁ (p k)) w * g k (trans q₁ (p k) w) = _
    rw [deriv_trans_comp hw hwk]
    ring
  have hhol : ∀ q : X, DifferentiableOn ℂ (G q) (chartAt ℂ q).target := by
    intro q w hw
    set x := (chartAt ℂ q).symm w
    set k := kx x
    have hwk : w ∈ overlap q (p k) := ⟨hw, (hkx x).1⟩
    have hnb : ∀ᶠ w' in 𝓝 w, w' ∈ overlap q (p k) ∧ trans q (p k) w' ∈ O k := by
      have hcont : ContinuousAt (trans q (p k)) w :=
        (trans_differentiableAt hwk).continuousAt
      filter_upwards [(isOpen_overlap q (p k)).mem_nhds hwk,
        hcont.preimage_mem_nhds ((hO k).mem_nhds (hkx x).2)] with w' h1 h2
      exact ⟨h1, h2⟩
    have heq : G q =ᶠ[𝓝 w] fun w' => deriv (trans q (p k)) w' * g k (trans q (p k) w') := by
      filter_upwards [hnb] with w' hw'
      exact key q w' hw'.1.1 k hw'.1.2 hw'.2
    have hd : DifferentiableAt ℂ (fun w' => deriv (trans q (p k)) w' * g k (trans q (p k) w')) w :=
      (deriv_trans_differentiableAt hwk).mul
        (((hg k).differentiableAt ((hO k).mem_nhds (hkx x).2)).comp w
          (trans_differentiableAt hwk))
    exact (hd.congr_of_eventuallyEq heq).differentiableWithinAt
  refine ⟨mkHoloForm G hIs10 hhol, fun k w hw => ?_⟩
  have hwt := hOt k hw
  rw [chartCoeff_mkHoloForm G hIs10 hhol (p k) hwt,
    key (p k) w hwt k ((chartAt ℂ (p k)).map_target hwt)
      (by rw [show trans (p k) (p k) w = w from (chartAt ℂ (p k)).right_inv hwt]; exact hw),
    deriv_trans_self hwt, one_mul, show trans (p k) (p k) w = w from (chartAt ℂ (p k)).right_inv hwt]

end JacobianChallenge.Surface
