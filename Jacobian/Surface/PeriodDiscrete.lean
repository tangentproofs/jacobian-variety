import Jacobian.Surface.Abel

/-!
# Discreteness of the period lattice

For a closed formal chain `Γ` (boundary `0`), the function `F Γ` extends smoothly across the
vertices to a nowhere-vanishing smooth function (`Fs`). With the Hodge decomposition
`θ Γ = ∂̄u + ν̄`, the function `F' = Fs · e^{-u}` has `d log F' = ν̄ - ν + β` with `β` a
holomorphic 1-form. Following `F'` along chart chains (`Fp_chain`) shows that
`exp(∫_{l₁} - ∫_{l₂})(β - ν + ν̄) = 1` for chains with common ends; the real part forces
`β = 0`, the imaginary part gives `Im(∫_{l₁} ν - ∫_{l₂} ν) ∈ π ℤ`.

The form `ν = ν_Γ` is determined by the periods of `Γ` (`∫ ν̄ ∧ ω = π ∫_Γ ω`), which yields a
real bilinear form `B` on `ℂ^g` that is non-degenerate and takes values in `π ℤ` on the period
lattice; hence the lattice is discrete (`periodLattice_discrete'`).
-/

set_option linter.unusedSectionVars false

namespace JacobianChallenge.Surface

open JacobianChallenge.Analysis JacobianChallenge.Periods JacobianChallenge.HolomorphicForms
  MeasureTheory Set Metric Filter Topology Complex
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] [T2Space X]

/-! ### Extending an atlas does not change integrals -/

theorem DiscAtlas.extend_U_castAdd (A : DiscAtlas X) {m : ℕ} (e : Fin m → X) (i : Fin A.N) :
    (A.extend e).U (Fin.castAdd m i) = A.U i := by
  simp only [DiscAtlas.U, DiscAtlas.ctr, DiscAtlas.extend, Fin.append_left]

theorem DiscAtlas.extend_piece_castAdd (A : DiscAtlas X) {m : ℕ} (e : Fin m → X)
    (i : Fin A.N) : (A.extend e).piece (Fin.castAdd m i) = A.piece i := by
  unfold DiscAtlas.piece
  rw [A.extend_U_castAdd e i]
  congr 1
  ext x
  simp only [mem_iUnion, mem_Iio, exists_prop]
  constructor
  · rintro ⟨j, hj, hx⟩
    have hjN : (j : ℕ) < A.N := lt_trans hj (Fin.castAdd_lt m i)
    refine ⟨⟨j, hjN⟩, ?_, ?_⟩
    · exact Fin.mk_lt_of_lt_val hj
    · have : j = Fin.castAdd m ⟨j, hjN⟩ := Fin.ext rfl
      rw [this, A.extend_U_castAdd e] at hx
      exact hx
  · rintro ⟨j, hj, hx⟩
    exact ⟨Fin.castAdd m j, (show (j : ℕ) < i from hj), by rw [A.extend_U_castAdd e]; exact hx⟩

theorem DiscAtlas.extend_piece_natAdd (A : DiscAtlas X) {m : ℕ} (e : Fin m → X)
    (j : Fin m) : (A.extend e).piece (Fin.natAdd A.N j) = ∅ := by
  ext x
  simp only [DiscAtlas.piece, mem_diff, mem_iUnion, mem_Iio, exists_prop, mem_empty_iff_false,
    iff_false, not_and, not_not]
  intro _
  obtain ⟨i, h1, h2⟩ := A.cover x
  refine ⟨Fin.castAdd m i, (show (i : ℕ) < A.N + j by omega), ?_⟩
  rw [A.extend_U_castAdd e]
  exact ⟨h1, h2⟩

/-- **The integral of a density does not depend on adjoining discs.** -/
theorem DiscAtlas.integral_extend (A : DiscAtlas X) {m : ℕ} (e : Fin m → X)
    (σ : X → ℂ → ℂ) : (A.extend e).integral σ = A.integral σ := by
  unfold DiscAtlas.integral
  show ∑ i : Fin (A.N + m), _ = _
  rw [Fin.sum_univ_add]
  have h2 : ∀ j : Fin m, ∫ w in (A.extend e).S (Fin.natAdd A.N j),
      σ ((A.extend e).p (Fin.natAdd A.N j)) w = 0 := fun j => by
    rw [DiscAtlas.S, A.extend_piece_natAdd e j, image_empty, Measure.restrict_empty,
      integral_zero_measure]
  rw [Finset.sum_eq_zero fun j _ => h2 j, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hp : (A.extend e).p (Fin.castAdd m i) = A.p i := by
    show Fin.append A.p e (Fin.castAdd m i) = A.p i
    rw [Fin.append_left]
  rw [DiscAtlas.S, A.extend_piece_castAdd e i, hp]
  rfl

namespace FChain

/-- Near any point of a chart target, the punctured neighbourhood avoids the vertices. -/
theorem eventually_notMem_V' (C : FChain X) {q : X} {w : ℂ} (hw : w ∈ (chartAt ℂ q).target) :
    ∀ᶠ v in 𝓝[≠] w, v ∈ (chartAt ℂ q).target ∧ (chartAt ℂ q).symm v ∉ V C := by
  set x := (chartAt ℂ q).symm w
  have hcl : IsClosed (V C \ {x}) := ((V_finite C).diff).isClosed
  have hx : x ∉ V C \ {x} := fun h => h.2 rfl
  have hT := (chartAt ℂ q).open_target.mem_nhds hw
  have hs : ∀ᶠ v in 𝓝 w, (chartAt ℂ q).symm v ∉ V C \ {x} :=
    ((chartAt ℂ q).continuousAt_symm hw).preimage_mem_nhds (hcl.isOpen_compl.mem_nhds hx)
  rw [eventually_nhdsWithin_iff]
  filter_upwards [hT, hs] with v hv1 hv2 hne
  refine ⟨hv1, fun hV => hv2 ⟨hV, fun hvx => hne ?_⟩⟩
  have := (chartAt ℂ q).symm.injOn hv1 hw hvx
  exact this

theorem eventually_notMem_V_nhds (C : FChain X) {q : X} {w : ℂ} (hw : w ∈ (chartAt ℂ q).target)
    (hV : (chartAt ℂ q).symm w ∉ V C) :
    ∀ᶠ v in 𝓝 w, v ∈ (chartAt ℂ q).target ∧ (chartAt ℂ q).symm v ∉ V C := by
  have hT := (chartAt ℂ q).open_target.mem_nhds hw
  have hs : ∀ᶠ v in 𝓝 w, (chartAt ℂ q).symm v ∉ V C :=
    ((chartAt ℂ q).continuousAt_symm hw).preimage_mem_nhds
      ((V_finite C).isClosed.isOpen_compl.mem_nhds hV)
  filter_upwards [hT, hs] with v h1 h2 using ⟨h1, h2⟩

open Classical in
/-- `F C`, corrected at the vertices (for a closed chain, a smooth function). -/
noncomputable def Fs (C : FChain X) (x : X) : ℂ :=
  if x ∈ V C then (F_vertex C x).choose (chartAt ℂ x x) else F C x

theorem rd_Fs_eq_F (C : FChain X) {q : X} {w : ℂ} (hw : w ∈ (chartAt ℂ q).target)
    (hV : (chartAt ℂ q).symm w ∉ V C) : rd (Fs C) q =ᶠ[𝓝 w] rd (F C) q := by
  filter_upwards [eventually_notMem_V_nhds C hw hV] with v hv
  simp only [rd_apply, Fs, if_neg hv.2]

/-- For a closed chain, `Fs` agrees near each vertex with the smooth factor `K`. -/
theorem rd_Fs_eq_K (C : FChain X) (hC : ∀ v, ord C v = 0) {x : X} (hx : x ∈ V C) :
    rd (Fs C) x =ᶠ[𝓝 (chartAt ℂ x x)] (F_vertex C x).choose := by
  obtain ⟨-, -, hev⟩ := (F_vertex C x).choose_spec
  have h1 : ∀ᶠ w in 𝓝[≠] (chartAt ℂ x x), rd (Fs C) x w = (F_vertex C x).choose w := by
    filter_upwards [eventually_notMem_V' C (mem_chart_target ℂ x), hev] with w hw h2
    simp only [rd_apply, Fs, if_neg hw.2]
    have hp : (w - chartAt ℂ x x) ^ (ord C x) = 1 := by rw [hC, zpow_zero]
    rw [show F C ((chartAt ℂ x).symm w) = rd (F C) x w from rfl, h2, hp, one_mul]
    rfl
  rw [eventually_nhdsWithin_iff] at h1
  filter_upwards [h1] with w hw
  by_cases hw0 : w = chartAt ℂ x x
  · rw [hw0, rd_apply, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
    simp only [Fs, if_pos hx]
  · exact hw hw0

theorem isSmooth_Fs (C : FChain X) (hC : ∀ v, ord C v = 0) : IsSmooth (Fs C) := by
  refine isSmooth_of_local fun x => ⟨x, mem_chart_source ℂ x, ?_⟩
  by_cases hx : x ∈ V C
  · obtain ⟨hK, -, -⟩ := (F_vertex C x).choose_spec
    exact hK.self_of_nhds.congr_of_eventuallyEq (rd_Fs_eq_K C hC hx)
  · have hV : (chartAt ℂ x).symm (chartAt ℂ x x) ∉ V C := by
      rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]; exact hx
    exact (F_local C (mem_chart_target ℂ x) hV).1.congr_of_eventuallyEq
      (rd_Fs_eq_F C (mem_chart_target ℂ x) hV)

theorem Fs_ne_zero (C : FChain X) (x : X) : Fs C x ≠ 0 := by
  unfold Fs
  split_ifs
  · exact (F_vertex C x).choose_spec.2.1
  · exact F_ne_zero C x

/-- Values of continuous functions agreeing on a punctured neighbourhood agree. -/
theorem eq_of_punctured {f g : ℂ → ℂ} {z : ℂ} (hf : ContinuousAt f z) (hg : ContinuousAt g z)
    (h : ∀ᶠ w in 𝓝[≠] z, f w = g w) : f z = g z := by
  have t1 : Tendsto f (𝓝[≠] z) (𝓝 (f z)) := hf.tendsto.mono_left nhdsWithin_le_nhds
  have t2 : Tendsto g (𝓝[≠] z) (𝓝 (g z)) := hg.tendsto.mono_left nhdsWithin_le_nhds
  have h' : g =ᶠ[𝓝[≠] z] f := h.mono fun _ hw => hw.symm
  exact tendsto_nhds_unique t1 (t2.congr' h')

/-- `∂̄ Fs = Fs · θ` everywhere. -/
theorem dbar_Fs (C : FChain X) (hC : ∀ v, ord C v = 0) {q : X} {w : ℂ}
    (hw : w ∈ (chartAt ℂ q).target) :
    dbar (rd (Fs C) q) w = rd (Fs C) q w * θ C q w := by
  have hs := isSmooth_Fs C hC
  have hc1 : ContinuousAt (dbar (rd (Fs C) q)) w :=
    ((contDiffOn_dbar (chartAt ℂ q).open_target (hs q)).continuousOn).continuousAt
      ((chartAt ℂ q).open_target.mem_nhds hw)
  have hc2 : ContinuousAt (fun v => rd (Fs C) q v * θ C q v) w :=
    (((hs q).continuousOn).mul (smoothFam_θ C q).continuousOn).continuousAt
      ((chartAt ℂ q).open_target.mem_nhds hw)
  have hoff : ∀ v ∈ (chartAt ℂ q).target, (chartAt ℂ q).symm v ∉ V C →
      dbar (rd (Fs C) q) v = rd (Fs C) q v * θ C q v := fun v hv hV => by
    have he := rd_Fs_eq_F C hv hV
    rw [dbar_congr he, (F_local C hv hV).2, he.self_of_nhds]
  by_cases hV : (chartAt ℂ q).symm w ∈ V C
  · refine eq_of_punctured hc1 hc2 ?_
    filter_upwards [eventually_notMem_V' C hw] with v hv using hoff v hv.1 hv.2
  · exact hoff w hw hV

/-! ### Monodromy -/

/-- `∂` of `exp ∘ g`. -/
theorem dz_cexp {g : ℂ → ℂ} {z : ℂ} (hg : DifferentiableAt ℝ g z) :
    dz (fun w => Complex.exp (g w)) z = Complex.exp (g z) * dz g z := by
  unfold dz
  rw [(hg.hasFDerivAt.cexp).fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- `∂ f = f'` for a holomorphic `f`. -/
theorem dz_eq_fderiv_one {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z) :
    dz f z = fderiv ℂ f z 1 := by
  unfold dz
  rw [hf.fderiv_restrictScalars ℝ]
  simp only [ContinuousLinearMap.coe_restrictScalars']
  have : fderiv ℂ f z I = I * fderiv ℂ f z 1 := by
    rw [← smul_eq_mul, ← (fderiv ℂ f z).map_smul, smul_eq_mul, mul_one]
  rw [this]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- A real-differentiable function with `∂ = ∂̄ = 0` has zero derivative. -/
theorem fderiv_eq_zero_of_dz_dbar {f : ℂ → ℂ} {z : ℂ} (h1 : dz f z = 0) (h2 : dbar f z = 0) :
    fderiv ℝ f z = 0 := by
  refine ContinuousLinearMap.ext fun a => ?_
  rw [clm_apply_eq_wirtinger]
  have e1 : (fderiv ℝ f z 1 - I * fderiv ℝ f z I) / 2 = 0 := h1
  have e2 : (fderiv ℝ f z 1 + I * fderiv ℝ f z I) / 2 = 0 := h2
  rw [e1, e2]; simp

variable [CompactSpace X] [ConnectedSpace X]

section Closed

variable {Γ : FChain X} (hΓ : ∀ v, ord Γ v = 0) {u : X → ℂ} (hu : IsSmooth u)
  {ν : HolomorphicOneForm ℂ X}
  (hν : ∀ q : X, ∀ w ∈ (chartAt ℂ q).target,
    θ Γ q w = dbar (rd u q) w + (starRingEnd ℂ) (chartCoeff q ν w))

/-- `Fs · e^{-u}`. -/
noncomputable def Fp (Γ : FChain X) (u : X → ℂ) (x : X) : ℂ := Fs Γ x * Complex.exp (-u x)

include hΓ hu in
theorem isSmooth_Fp : IsSmooth (Fp Γ u) := by
  have he : IsSmooth fun x => Complex.exp (-u x) := fun q =>
    ((Complex.contDiff_exp (𝕜 := ℂ) (n := ∞)).restrict_scalars ℝ).comp_contDiffOn (hu q).neg
  exact (isSmooth_Fs Γ hΓ).mul he

theorem Fp_ne_zero (x : X) : Fp Γ u x ≠ 0 :=
  mul_ne_zero (Fs_ne_zero Γ x) (Complex.exp_ne_zero _)

include hΓ hu hν in
theorem dbar_Fp {q : X} {w : ℂ} (hw : w ∈ (chartAt ℂ q).target) :
    dbar (rd (Fp Γ u) q) w = rd (Fp Γ u) q w * (starRingEnd ℂ) (chartCoeff q ν w) := by
  have hs := (isSmooth_Fs Γ hΓ).contDiffAt hw
  have hu' := hu.contDiffAt hw
  have hrd : rd (Fp Γ u) q = fun v => rd (Fs Γ) q v * Complex.exp (-rd u q v) := rfl
  have hneg : dbar (fun v => -rd u q v) w = -dbar (rd u q) w := by
    have := dbar_const_mul (-1) (hu'.differentiableAt (by simp)) (z := w)
    simpa using this
  have he : DifferentiableAt ℝ (fun v => Complex.exp (-rd u q v)) w :=
    ((Complex.differentiableAt_exp (𝕜 := ℂ) (x := -rd u q w)).restrictScalars ℝ).comp w
      (hu'.differentiableAt (by simp)).neg
  rw [hrd, dbar_mul (hs.differentiableAt (by simp)) he,
    dbar_cexp (hu'.neg.differentiableAt (by simp)), hneg, dbar_Fs Γ hΓ hw, hν q w hw]
  ring

/-- The `(1,0)`-family `∂F'/F' + ν`. -/
noncomputable def bfam (Γ : FChain X) (u : X → ℂ) (ν : HolomorphicOneForm ℂ X) : X → ℂ → ℂ :=
  smulF (fun x => (Fp Γ u x)⁻¹) (dzF (Fp Γ u)) + holoF ν

include hΓ hu in
theorem bfam_is10 : Is10 (bfam Γ u ν) :=
  ((dzF_is10 (isSmooth_Fp hΓ hu)).smulF _).add (holoF_is10 ν)

include hΓ hu hν in
theorem bfam_holo (q : X) : DifferentiableOn ℂ (bfam Γ u ν q) (chartAt ℂ q).target := by
  intro w hw
  have hT := (chartAt ℂ q).open_target.mem_nhds hw
  set F := rd (Fp Γ u) q
  set h := chartCoeff q ν
  have hFs : ContDiffAt ℝ ∞ F w := (isSmooth_Fp hΓ hu).contDiffAt hw
  have hF0 : F w ≠ 0 := Fp_ne_zero _
  have hh : DifferentiableAt ℂ h w := (chartCoeff_differentiableOn q ν).differentiableAt hT
  have hdzF : ContDiffAt ℝ ∞ (dz F) w :=
    (contDiffOn_dz (chartAt ℂ q).open_target ((isSmooth_Fp hΓ hu) q)).contDiffAt hT
  have hFi : ContDiffAt ℝ ∞ (fun v => (F v)⁻¹) w := hFs.inv hF0
  have hb : bfam Γ u ν q = fun v => (F v)⁻¹ * dz F v + h v := rfl
  have hdiff : DifferentiableAt ℝ (bfam Γ u ν q) w := by
    rw [hb]
    exact ((hFi.differentiableAt (by simp)).mul (hdzF.differentiableAt (by simp))).add
      (hh.restrictScalars ℝ)
  refine (differentiableAt_of_dbar_eq_zero hdiff ?_).differentiableWithinAt
  -- `∂̄ (∂F/F) = 0`
  have hevd : dbar F =ᶠ[𝓝 w] fun v => F v * (starRingEnd ℂ) (h v) := by
    filter_upwards [hT] with v hv using dbar_Fp hΓ hu hν hv
  have hhc : DifferentiableAt ℝ (fun v => (starRingEnd ℂ) (h v)) w :=
    differentiableAt_conj_comp (hh.restrictScalars ℝ)
  have h1 : dbar (dz F) w = (starRingEnd ℂ) (h w) * dz F w := by
    rw [← dz_dbar_comm (hFs.of_le (WithTop.coe_le_coe.mpr le_top)), dz_congr hevd,
      dz_mul (hFs.differentiableAt (by simp)) hhc, dz_conj (hh.restrictScalars ℝ),
      dbar_eq_zero_of_differentiableAt hh, map_zero, mul_zero, zero_add]
  have h2 : dbar (fun v => (F v)⁻¹) w = -((F w)⁻¹ * (F w)⁻¹) * (F w * (starRingEnd ℂ) (h w)) := by
    rw [dbar_inv (hFs.differentiableAt (by simp)) hF0, hevd.self_of_nhds]
  have hadd := dbar_add (f := fun v => (F v)⁻¹ * dz F v) (g := h) (z := w)
    ((hFi.differentiableAt (by simp)).mul (hdzF.differentiableAt (by simp)))
    (hh.restrictScalars ℝ)
  rw [hb, hadd, dbar_mul (hFi.differentiableAt (by simp))
      (hdzF.differentiableAt (by simp)), h1, h2, dbar_eq_zero_of_differentiableAt hh]
  field_simp
  ring

include hΓ hu hν in
/-- The holomorphic form `β = ∂F'/F' + ν`. -/
theorem exists_β : ∃ β : HolomorphicOneForm ℂ X,
    ∀ q : X, ∀ w ∈ (chartAt ℂ q).target, chartCoeff q β w = bfam Γ u ν q w := by
  obtain ⟨β, hβ⟩ := exists_holoForm_of_local (ι := X) id (fun q => (chartAt ℂ q).target)
    (fun q => (chartAt ℂ q).open_target) (fun q => subset_rfl)
    (fun x => ⟨x, mem_chart_source ℂ x, mem_chart_target ℂ x⟩) (bfam Γ u ν)
    (fun q => bfam_holo hΓ hu hν q)
    (fun k l w _ hwo _ => bfam_is10 hΓ hu k l w hwo)
  exact ⟨β, fun q w hw => hβ q w hw⟩

include hΓ hu hν in
/-- **Monodromy along a segment.** -/
theorem Fp_segment {β : HolomorphicOneForm ℂ X}
    (hβ : ∀ q : X, ∀ w ∈ (chartAt ℂ q).target, chartCoeff q β w = bfam Γ u ν q w)
    (s : ChartSegment X) :
    Fp Γ u s.stop = Fp Γ u s.start *
      Complex.exp (s.integral β - s.integral ν + (starRingEnd ℂ) (s.integral ν)) := by
  set p := s.p
  set B := ball s.center s.radius
  have hB := s.ball_subset
  set Pβ : ℂ → ℂ := fun z => ∫ᶜ x in Path.segment s.center z, chartForm p β x
  set Pν : ℂ → ℂ := fun z => ∫ᶜ x in Path.segment s.center z, chartForm p ν x
  have hPβ : ∀ z ∈ B, HasFDerivAt Pβ (chartForm p β z) z := fun z hz =>
    chartForm_hasFDerivAt_primitive p β hB hz
  have hPν : ∀ z ∈ B, HasFDerivAt Pν (chartForm p ν z) z := fun z hz =>
    chartForm_hasFDerivAt_primitive p ν hB hz
  set Φ : ℂ → ℂ := fun z => Pβ z - Pν z + (starRingEnd ℂ) (Pν z)
  set F := rd (Fp Γ u) p
  set Ψ : ℂ → ℂ := fun z => F z * Complex.exp (-Φ z)
  have hdiffΦ : ∀ z ∈ B, DifferentiableAt ℝ Φ z := fun z hz =>
    (((hPβ z hz).differentiableAt.restrictScalars ℝ).sub
      ((hPν z hz).differentiableAt.restrictScalars ℝ)).add
      (differentiableAt_conj_comp ((hPν z hz).differentiableAt.restrictScalars ℝ))
  have hdiffF : ∀ z ∈ B, DifferentiableAt ℝ F z := fun z hz =>
    ((isSmooth_Fp hΓ hu).contDiffAt (hB hz)).differentiableAt (by simp)
  have hdiffE : ∀ z ∈ B, DifferentiableAt ℝ (fun z => Complex.exp (-Φ z)) z := fun z hz =>
    ((Complex.differentiableAt_exp (𝕜 := ℂ) (x := -Φ z)).restrictScalars ℝ).comp z (hdiffΦ z hz).neg
  have hdΨ : ∀ z ∈ B, fderiv ℝ Ψ z = 0 := by
    intro z hz
    have hzt := hB hz
    have hdPβ : DifferentiableAt ℂ Pβ z := (hPβ z hz).differentiableAt
    have hdPν : DifferentiableAt ℂ Pν z := (hPν z hz).differentiableAt
    have ezβ : dz Pβ z = chartCoeff p β z := by
      rw [dz_eq_fderiv_one hdPβ, (hPβ z hz).fderiv]; rfl
    have ezν : dz Pν z = chartCoeff p ν z := by
      rw [dz_eq_fderiv_one hdPν, (hPν z hz).fderiv]; rfl
    have hdc : DifferentiableAt ℝ (fun w => (starRingEnd ℂ) (Pν w)) z :=
      differentiableAt_conj_comp (hdPν.restrictScalars ℝ)
    have hdsub : DifferentiableAt ℂ (fun w => Pβ w - Pν w) z := hdPβ.sub hdPν
    have dsubz : dz (fun w => Pβ w - Pν w) z = chartCoeff p β z - chartCoeff p ν z := by
      rw [dz_eq_fderiv_one hdsub, fderiv_fun_sub hdPβ hdPν, ContinuousLinearMap.sub_apply,
        ← dz_eq_fderiv_one hdPβ, ← dz_eq_fderiv_one hdPν, ezβ, ezν]
    have dΦz : dz Φ z = chartCoeff p β z - chartCoeff p ν z := by
      have := dz_add (f := fun w => Pβ w - Pν w) (g := fun w => (starRingEnd ℂ) (Pν w)) (z := z)
        (hdsub.restrictScalars ℝ) hdc
      rw [show Φ = fun w => (Pβ w - Pν w) + (starRingEnd ℂ) (Pν w) from rfl, this,
        dz_conj (hdPν.restrictScalars ℝ), dbar_eq_zero_of_differentiableAt hdPν, map_zero,
        add_zero, dsubz]
    have dΦb : dbar Φ z = (starRingEnd ℂ) (chartCoeff p ν z) := by
      have := dbar_add (f := fun w => Pβ w - Pν w) (g := fun w => (starRingEnd ℂ) (Pν w))
        (z := z) (hdsub.restrictScalars ℝ) hdc
      rw [show Φ = fun w => (Pβ w - Pν w) + (starRingEnd ℂ) (Pν w) from rfl, this,
        dbar_conj (hdPν.restrictScalars ℝ), ezν, dbar_eq_zero_of_differentiableAt hdsub, zero_add]
    have hF0 : F z ≠ 0 := Fp_ne_zero _
    have dFz : dz F z = F z * (chartCoeff p β z - chartCoeff p ν z) := by
      rw [hβ p z hzt]
      show dz F z = F z * ((F z)⁻¹ * dz F z + chartCoeff p ν z - chartCoeff p ν z)
      field_simp
      ring
    have dFb : dbar F z = F z * (starRingEnd ℂ) (chartCoeff p ν z) := dbar_Fp hΓ hu hν hzt
    have hnegΦ : DifferentiableAt ℝ (fun z => -Φ z) z := (hdiffΦ z hz).neg
    have dnz : dz (fun z => -Φ z) z = -dz Φ z := by unfold dz; rw [fderiv_fun_neg]; simp; ring
    have dnb : dbar (fun z => -Φ z) z = -dbar Φ z := by unfold dbar; rw [fderiv_fun_neg]; simp; ring
    refine fderiv_eq_zero_of_dz_dbar ?_ ?_
    · rw [show Ψ = fun z => F z * Complex.exp (-Φ z) from rfl,
        dz_mul (hdiffF z hz) (hdiffE z hz), dz_cexp hnegΦ, dnz, dΦz, dFz]
      ring
    · rw [show Ψ = fun z => F z * Complex.exp (-Φ z) from rfl,
        dbar_mul (hdiffF z hz) (hdiffE z hz), dbar_cexp hnegΦ, dnb, dΦb, dFb]
      ring
  have hdiffΨ : DifferentiableOn ℝ Ψ B := fun z hz =>
    ((hdiffF z hz).mul (hdiffE z hz)).differentiableWithinAt
  have hconst : Ψ s.b = Ψ s.a :=
    (convex_ball s.center s.radius).is_const_of_fderivWithin_eq_zero hdiffΨ
      (fun z hz => by rw [fderivWithin_of_isOpen isOpen_ball hz, hdΨ z hz]) s.b_mem s.a_mem
  have hFb : F s.b = Fp Γ u s.stop := rfl
  have hFa : F s.a = Fp Γ u s.start := rfl
  have hint : ∀ η : HolomorphicOneForm ℂ X, s.integral η =
      (∫ᶜ x in Path.segment s.center s.b, chartForm p η x) -
        ∫ᶜ x in Path.segment s.center s.a, chartForm p η x := fun η => s.integral_eq_sub η
  simp only [Ψ, hFb, hFa] at hconst
  have key : Φ s.b - Φ s.a = s.integral β - s.integral ν + (starRingEnd ℂ) (s.integral ν) := by
    rw [hint β, hint ν, map_sub]
    simp only [Φ, Pβ, Pν]
    ring
  rw [← key, Complex.exp_sub]
  have he : Complex.exp (Φ s.b) ≠ 0 := Complex.exp_ne_zero _
  rw [Complex.exp_neg, Complex.exp_neg] at hconst
  field_simp at hconst ⊢
  linear_combination hconst

include hΓ hu hν in
/-- **Monodromy along a chain.** -/
theorem Fp_chain {β : HolomorphicOneForm ℂ X}
    (hβ : ∀ q : X, ∀ w ∈ (chartAt ℂ q).target, chartCoeff q β w = bfam Γ u ν q w)
    {l : List (ChartSegment X)} {P Q : X} (hl : IsChain l P Q) :
    Fp Γ u Q = Fp Γ u P * Complex.exp (chainIntegral β l - chainIntegral ν l +
      (starRingEnd ℂ) (chainIntegral ν l)) := by
  induction l generalizing P with
  | nil =>
    simp only [isChain_nil] at hl
    subst hl
    simp
  | cons s l ih =>
    obtain ⟨h1, h2⟩ := hl
    rw [ih h2, Fp_segment hΓ hu hν hβ s, h1, chainIntegral_cons, chainIntegral_cons, map_add,
      mul_assoc, ← Complex.exp_add]
    ring_nf

/-- Splitting `∫ (∂̄u + ν̄) ω`. -/
theorem integral_hodge_split (A : DiscAtlas X) {θ : X → ℂ → ℂ} {u : X → ℂ} (hu : IsSmooth u)
    {ν : HolomorphicOneForm ℂ X}
    (hν : ∀ q : X, ∀ w ∈ (chartAt ℂ q).target,
      θ q w = dbar (rd u q) w + (starRingEnd ℂ) (chartCoeff q ν w))
    (η : HolomorphicOneForm ℂ X) :
    A.integral (fun q w => θ q w * holoF η q w) =
      A.integral (fun p w => (starRingEnd ℂ) (holoF ν p w) * holoF η p w) := by
  have hc1 : ∀ q, ContinuousOn (fun w => dbar (rd u q) w * holoF η q w) (chartAt ℂ q).target :=
    fun q => ((contDiffOn_dbar (chartAt ℂ q).open_target (hu q)).continuousOn).mul
      ((smoothFam_holoF η q).continuousOn)
  have hc2 : ∀ q, ContinuousOn (fun w => (starRingEnd ℂ) (holoF ν q w) * holoF η q w)
      (chartAt ℂ q).target := fun q =>
    (Complex.continuous_conj.comp_continuousOn (smoothFam_holoF ν q).continuousOn).mul
      (smoothFam_holoF η q).continuousOn
  have e : A.integral (fun q w => θ q w * holoF η q w) =
      A.integral (fun q w => dbar (rd u q) w * holoF η q w +
        (starRingEnd ℂ) (holoF ν q w) * holoF η q w) :=
    A.integral_congr fun i w hw => by rw [hν (A.p i) w hw]; simp only [holoF]; ring
  rw [e, A.integral_add' hc1 hc2, integral_dbar_mul_holo A hu η, zero_add]

include hΓ in
/-- **The data of a closed chain.** The Hodge form `ν` of `θ Γ` represents the periods of `Γ`,
and its periods over closed chains have imaginary parts in `π ℤ`. -/
theorem closed_chain_data :
    ∃ ν : HolomorphicOneForm ℂ X,
      (∀ A : DiscAtlas X, (∀ c ∈ Γ, ∃ k, A.p k = c.1.p) → ∀ η : HolomorphicOneForm ℂ X,
        A.integral (fun p w => (starRingEnd ℂ) (holoF ν p w) * holoF η p w) =
          (Real.pi : ℂ) * integral Γ η) ∧
      ∀ (P Q : X) (l₁ l₂ : List (ChartSegment X)), IsChain l₁ P Q → IsChain l₂ P Q →
        ∃ n : ℤ, (chainIntegral ν l₁ - chainIntegral ν l₂).im = Real.pi * n := by
  obtain ⟨u, hu, ν, hν⟩ := hodge_decomp (θ_is01 Γ) (smoothFam_θ Γ)
  refine ⟨ν, fun A hA η => ?_, ?_⟩
  · rw [← integral_hodge_split A hu hν η, integral_θ_mul A Γ hA η]
  obtain ⟨β, hβ⟩ := exists_β hΓ hu hν
  -- comparing two chains with the same ends
  have key : ∀ (P Q : X) (l₁ l₂ : List (ChartSegment X)), IsChain l₁ P Q → IsChain l₂ P Q →
      ∃ n : ℤ, (chainIntegral β l₁ - chainIntegral ν l₁ + (starRingEnd ℂ) (chainIntegral ν l₁)) -
        (chainIntegral β l₂ - chainIntegral ν l₂ + (starRingEnd ℂ) (chainIntegral ν l₂)) =
          n * (2 * Real.pi * I) := by
    intro P Q l₁ l₂ h₁ h₂
    have e1 := Fp_chain hΓ hu hν hβ h₁
    have e2 := Fp_chain hΓ hu hν hβ h₂
    rw [e1] at e2
    have hP := Fp_ne_zero (Γ := Γ) (u := u) P
    have hexp : Complex.exp ((chainIntegral β l₁ - chainIntegral ν l₁ +
        (starRingEnd ℂ) (chainIntegral ν l₁)) - (chainIntegral β l₂ - chainIntegral ν l₂ +
        (starRingEnd ℂ) (chainIntegral ν l₂))) = 1 := by
      rw [Complex.exp_sub, div_eq_one_iff_eq (Complex.exp_ne_zero _)]
      exact mul_left_cancel₀ hP e2
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp
    exact ⟨n, hn⟩
  have hβ0 : β = 0 := by
    refine eq_zero_of_re_chainIntegral_eq β fun P Q l₁ l₂ h₁ h₂ => ?_
    obtain ⟨n, hn⟩ := key P Q l₁ l₂ h₁ h₂
    have := congrArg Complex.re hn
    simp only [Complex.sub_re, Complex.add_re, Complex.conj_re, Complex.mul_re,
      Complex.intCast_re, Complex.intCast_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat] at this
    linarith
  intro P Q l₁ l₂ h₁ h₂
  obtain ⟨n, hn⟩ := key P Q l₁ l₂ h₁ h₂
  refine ⟨-n, ?_⟩
  have h0 : ∀ l : List (ChartSegment X), chainIntegral β l = 0 := fun l => by
    rw [hβ0, ← chainIntegralLM_apply, map_zero]
  have := congrArg Complex.im hn
  simp only [h0, Complex.sub_im, Complex.add_im, Complex.conj_im, Complex.zero_im,
    Complex.mul_im, Complex.intCast_re, Complex.intCast_im, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat] at this
  rw [Complex.sub_im]
  push_cast
  ring_nf at this ⊢
  linarith

end Closed

/-! ### The bilinear form and discreteness -/

section Lattice

variable [FiniteDimensionalHolomorphicOneForms ℂ X]

theorem integral_const_mul_atlas (A : DiscAtlas X) (c : ℂ) (σ : X → ℂ → ℂ) :
    A.integral (fun q w => c * σ q w) = c * A.integral σ := by
  unfold DiscAtlas.integral
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => MeasureTheory.integral_const_mul _ _

/-- The `L²` pairing of holomorphic forms. -/
noncomputable def gram (A : DiscAtlas X) (ν η : HolomorphicOneForm ℂ X) : ℂ :=
  A.integral (fun p w => (starRingEnd ℂ) (holoF ν p w) * holoF η p w)

theorem gram_add_right (A : DiscAtlas X) (ν η₁ η₂ : HolomorphicOneForm ℂ X) :
    gram A ν (η₁ + η₂) = gram A ν η₁ + gram A ν η₂ := by
  have hc : ∀ η : HolomorphicOneForm ℂ X, ∀ q, ContinuousOn
      (fun w => (starRingEnd ℂ) (holoF ν q w) * holoF η q w) (chartAt ℂ q).target := fun η q =>
    (Complex.continuous_conj.comp_continuousOn (smoothFam_holoF ν q).continuousOn).mul
      (smoothFam_holoF η q).continuousOn
  unfold gram
  rw [← A.integral_add' (hc η₁) (hc η₂)]
  refine A.integral_congr fun i w _ => ?_
  simp only [holoF, chartCoeff_add]; ring

theorem gram_smul_right (A : DiscAtlas X) (ν η : HolomorphicOneForm ℂ X) (c : ℂ) :
    gram A ν (c • η) = c * gram A ν η := by
  unfold gram
  rw [← integral_const_mul_atlas A]
  refine A.integral_congr fun i w _ => ?_
  simp only [holoF, chartCoeff_smul]; ring

theorem gram_add_left (A : DiscAtlas X) (ν₁ ν₂ η : HolomorphicOneForm ℂ X) :
    gram A (ν₁ + ν₂) η = gram A ν₁ η + gram A ν₂ η := by
  have hc : ∀ ν : HolomorphicOneForm ℂ X, ∀ q, ContinuousOn
      (fun w => (starRingEnd ℂ) (holoF ν q w) * holoF η q w) (chartAt ℂ q).target := fun ν q =>
    (Complex.continuous_conj.comp_continuousOn (smoothFam_holoF ν q).continuousOn).mul
      (smoothFam_holoF η q).continuousOn
  unfold gram
  rw [← A.integral_add' (hc ν₁) (hc ν₂)]
  refine A.integral_congr fun i w _ => ?_
  simp only [holoF, chartCoeff_add, map_add]; ring

theorem gram_smul_left (A : DiscAtlas X) (ν η : HolomorphicOneForm ℂ X) (c : ℂ) :
    gram A (c • ν) η = (starRingEnd ℂ) c * gram A ν η := by
  unfold gram
  rw [← integral_const_mul_atlas A]
  refine A.integral_congr fun i w _ => ?_
  simp only [holoF, chartCoeff_smul, map_mul]; ring

theorem gram_extend (A : DiscAtlas X) {m : ℕ} (e : Fin m → X) (ν η : HolomorphicOneForm ℂ X) :
    gram (A.extend e) ν η = gram A ν η := A.integral_extend e _

/-- `gram A ν` as a linear functional. -/
noncomputable def gramR (A : DiscAtlas X) (ν : HolomorphicOneForm ℂ X) :
    HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ where
  toFun := gram A ν
  map_add' := gram_add_right A ν
  map_smul' c η := gram_smul_right A ν η c

local notation "bas" => holomorphicOneFormFinBasis ℂ X

/-- `ν ↦ (⟨ν, ω_j⟩)_j`, a real-linear map. -/
noncomputable def gramT (A : DiscAtlas X) :
    HolomorphicOneForm ℂ X →ₗ[ℝ] (Fin (analyticGenus ℂ X) → ℂ) where
  toFun ν := fun j => gram A ν (bas j)
  map_add' ν₁ ν₂ := funext fun j => gram_add_left A ν₁ ν₂ _
  map_smul' r ν := funext fun j => by
    simp only [RingHom.id_apply, Pi.smul_apply]
    rw [← Complex.coe_smul, gram_smul_left, Complex.conj_ofReal, Complex.real_smul]

theorem gramT_injective (A : DiscAtlas X) : Function.Injective (gramT A) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro ν hν
  have hz : gramR A ν = 0 := (bas).ext fun j => congrFun hν j
  exact eq_zero_of_integral_conj_mul_self A ν (LinearMap.congr_fun hz ν)

theorem gramT_bijective (A : DiscAtlas X) : Function.Bijective (gramT A) := by
  refine ⟨gramT_injective A, ?_⟩
  have h : Module.finrank ℝ (HolomorphicOneForm ℂ X) =
      Module.finrank ℝ (Fin (analyticGenus ℂ X) → ℂ) := by
    rw [finrank_real_of_complex, finrank_real_of_complex, Module.finrank_fin_fun]
    rfl
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h).mp (gramT_injective A)

/-- The real-linear equivalence `ν ↦ (⟨ν, ω_j⟩)_j`. -/
noncomputable def gramE (A : DiscAtlas X) :
    HolomorphicOneForm ℂ X ≃ₗ[ℝ] (Fin (analyticGenus ℂ X) → ℂ) :=
  LinearEquiv.ofBijective (gramT A) (gramT_bijective A)

/-- Evaluation of a period vector on a form: `∑ y_j c_j(ν)`. -/
noncomputable def ev (y : Fin (analyticGenus ℂ X) → ℂ) : HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ :=
  ∑ j, y j • (bas).coord j

theorem ev_apply (y : Fin (analyticGenus ℂ X) → ℂ) (ν : HolomorphicOneForm ℂ X) :
    ev y ν = ∑ j, y j * (bas).repr ν j := by
  simp only [ev, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
    Module.Basis.coord_apply, smul_eq_mul]

theorem ev_basis (y : Fin (analyticGenus ℂ X) → ℂ) (k : Fin (analyticGenus ℂ X)) :
    ev y (bas k) = y k := by
  rw [ev_apply, Module.Basis.repr_self]
  simp only [Finsupp.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

theorem ev_chain (l : List (ChartSegment X)) (ν : HolomorphicOneForm ℂ X) :
    ev (periodVector X l) ν = chainIntegral ν l := by
  rw [ev_apply]
  conv_rhs => rw [← (bas).sum_repr ν, ← chainIntegralLM_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, chainIntegralLM_apply, smul_eq_mul, mul_comm]
  rfl

theorem ev_add (y₁ y₂ : Fin (analyticGenus ℂ X) → ℂ) (ν : HolomorphicOneForm ℂ X) :
    ev (y₁ + y₂) ν = ev y₁ ν + ev y₂ ν := by
  simp only [ev_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem ev_neg (y : Fin (analyticGenus ℂ X) → ℂ) (ν : HolomorphicOneForm ℂ X) :
    ev (-y) ν = -ev y ν := by
  simp only [ev_apply, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

theorem ev_zero (ν : HolomorphicOneForm ℂ X) : ev 0 ν = 0 := by simp [ev_apply]

theorem continuous_ev (ν : HolomorphicOneForm ℂ X) :
    Continuous fun y : Fin (analyticGenus ℂ X) → ℂ => ev y ν := by
  simp only [ev_apply]
  exact continuous_finsetSum _ fun j _ => (continuous_apply j).mul continuous_const

/-- The real bilinear form `B(x, y) = Im ⟨y, ν_x⟩`. -/
noncomputable def Bf (A : DiscAtlas X) (x y : Fin (analyticGenus ℂ X) → ℂ) : ℝ :=
  (ev y ((gramE A).symm (Real.pi • x))).im

/-- `B(·, y)` as a real-linear functional. -/
noncomputable def BL (A : DiscAtlas X) (y : Fin (analyticGenus ℂ X) → ℂ) :
    (Fin (analyticGenus ℂ X) → ℂ) →ₗ[ℝ] ℝ :=
  Complex.imLm ∘ₗ ((ev y).restrictScalars ℝ) ∘ₗ (gramE A).symm.toLinearMap ∘ₗ
    (Real.pi • LinearMap.id)

theorem BL_apply (A : DiscAtlas X) (x y : Fin (analyticGenus ℂ X) → ℂ) :
    BL A y x = Bf A x y := rfl

/-- **Integrality.** `B(Λ, Λ) ⊆ π ℤ`. -/
theorem Bf_mem (A : DiscAtlas X)
    {x : Fin (analyticGenus ℂ X) → ℂ} (hx : x ∈ genuinePeriodSubgroup X)
    {y : Fin (analyticGenus ℂ X) → ℂ} (hy : y ∈ genuinePeriodSubgroup X) :
    ∃ n : ℤ, Bf A x y = Real.pi * n := by
  obtain ⟨Γ, hΓ, hΓi⟩ := exists_closed_fchain hx
  obtain ⟨ν, hpair, him⟩ := closed_chain_data hΓ
  -- `ν` is the form attached to `x`
  have hA : ∀ c ∈ Γ, ∃ k, (A.extend fun i : Fin Γ.length => (Γ.get i).1.p).p k = c.1.p := by
    intro c hc
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hc
    exact ⟨Fin.natAdd A.N i, A.extend_p _ i⟩
  have hT : gramT A ν = Real.pi • x := funext fun j => by
    show gram A ν (bas j) = Real.pi • x j
    rw [← gram_extend A (fun i : Fin Γ.length => (Γ.get i).1.p), gram, hpair _ hA, hΓi,
      Complex.real_smul]
  have hν : (gramE A).symm (Real.pi • x) = ν := by
    rw [← hT]; exact (gramE A).symm_apply_apply ν
  unfold Bf
  rw [hν]
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨P, Q, l₁, l₂, h₁, h₂, rfl⟩ := hy
    rw [sub_eq_add_neg, ev_add, ev_neg, ev_chain, ev_chain, ← sub_eq_add_neg]
    exact him P Q l₁ l₂ h₁ h₂
  | zero => exact ⟨0, by rw [ev_zero]; simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨n₁, h1⟩ := hy
    obtain ⟨n₂, h2⟩ := hz
    exact ⟨n₁ + n₂, by rw [ev_add, Complex.add_im, h1, h2]; push_cast; ring⟩
  | neg y _ hy =>
    obtain ⟨n, h⟩ := hy
    exact ⟨-n, by rw [ev_neg, Complex.neg_im, h]; push_cast; ring⟩

/-- **Non-degeneracy.** -/
theorem eq_zero_of_Bf (A : DiscAtlas X) {y : Fin (analyticGenus ℂ X) → ℂ}
    (h : ∀ x, Bf A x y = 0) : y = 0 := by
  have him : ∀ ν, (ev y ν).im = 0 := fun ν => by
    have := h ((Real.pi)⁻¹ • gramE A ν)
    rw [Bf, smul_smul, mul_inv_cancel₀ Real.pi_ne_zero, one_smul,
      (gramE A).symm_apply_apply] at this
    exact this
  have h0 : ∀ ν, ev y ν = 0 := fun ν => by
    have h1 := him ν
    have h2 := him (Complex.I • ν)
    rw [map_smul, smul_eq_mul, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
      zero_add] at h2
    exact Complex.ext h2 h1
  funext k
  rw [← ev_basis y k, h0]
  rfl

/-- **The period lattice is discrete.** -/
theorem periodLattice_discrete' :
    DiscreteTopology (genuinePeriodSubgroup X) := by
  obtain ⟨A⟩ := exists_discAtlas (X := X)
  obtain ⟨t, htΛ, hspan, hli⟩ :=
    exists_linearIndependent ℝ (genuinePeriodSubgroup X : Set (Fin (analyticGenus ℂ X) → ℂ))
  have htop : Submodule.span ℝ t = ⊤ := hspan.trans (periodLattice_span X)
  have hfin : t.Finite := hli.setFinite
  set U : Set (Fin (analyticGenus ℂ X) → ℂ) := ⋂ x ∈ t, {y | |Bf A x y| < Real.pi}
  have hU : IsOpen U := hfin.isOpen_biInter fun x _ =>
    isOpen_lt (continuous_abs.comp (Complex.continuous_im.comp (continuous_ev _)))
      continuous_const
  have hU0 : ∀ y ∈ genuinePeriodSubgroup X, y ∈ U → y = 0 := by
    intro y hy hyU
    refine eq_zero_of_Bf A fun x => ?_
    have hvan : ∀ x ∈ t, Bf A x y = 0 := fun x hx => by
      obtain ⟨n, hn⟩ := Bf_mem A (htΛ hx) hy
      have hlt := mem_iInter₂.mp hyU x hx
      simp only [mem_setOf_eq, hn, abs_mul, abs_of_pos Real.pi_pos] at hlt
      have : |(n : ℝ)| < 1 := by
        have := Real.pi_pos
        nlinarith [abs_nonneg (n : ℝ)]
      have hn0 : n = 0 := by
        rw [← Int.cast_abs] at this
        have : |n| < 1 := by exact_mod_cast this
        have := abs_lt.mp this
        omega
      rw [hn, hn0]; simp
    have hle : t ⊆ LinearMap.ker (BL A y) := fun x hx => hvan x hx
    have := Submodule.span_le.mpr hle
    rw [htop] at this
    exact this (Submodule.mem_top (x := x))
  have h0U : (0 : Fin (analyticGenus ℂ X) → ℂ) ∈ U := by
    refine mem_iInter₂.mpr fun x _ => ?_
    simp only [mem_setOf_eq, Bf, ev_zero, Complex.zero_im, abs_zero, Real.pi_pos]
  refine discreteTopology_of_isOpen_singleton_zero ?_
  have : ({0} : Set (genuinePeriodSubgroup X)) = Subtype.val ⁻¹' U := by
    ext z
    simp only [mem_singleton_iff, mem_preimage]
    constructor
    · rintro rfl; exact h0U
    · intro hz; exact Subtype.ext (hU0 z z.2 hz)
  rw [this]
  exact hU.preimage continuous_subtype_val

end Lattice

end FChain

end JacobianChallenge.Surface
