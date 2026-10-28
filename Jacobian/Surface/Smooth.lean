import Jacobian.Surface.Atlas

/-!
# Smooth functions on a Riemann surface; extension by zero; a partition of unity

* `rd u p = u ∘ c_p⁻¹` and `IsSmooth u`: every chart reading is `C^∞` on the chart target.
* `extend p φ`: a function compactly supported in a chart target, extended by `0` to `X`
  (`isSmooth_extend`).
* `DiscAtlas.pou`: a smooth partition of unity subordinate to the discs of the atlas.
-/

set_option linter.unusedSectionVars false

namespace JacobianChallenge.Surface

open JacobianChallenge.Analysis JacobianChallenge.Periods JacobianChallenge.HolomorphicForms
  MeasureTheory Set Metric Filter Topology Complex
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/-- The reading of a function in the chart at `p`. -/
noncomputable def rd (u : X → ℂ) (p : X) : ℂ → ℂ := u ∘ (chartAt ℂ p).symm

theorem rd_apply (u : X → ℂ) (p : X) (w : ℂ) : rd u p w = u ((chartAt ℂ p).symm w) := rfl

theorem rd_trans {u : X → ℂ} {p q : X} {w : ℂ} (hw : w ∈ overlap p q) :
    rd u q (trans p q w) = rd u p w := by
  simp only [rd_apply, trans_symm_eq hw]

theorem rd_eventuallyEq {u : X → ℂ} {p q : X} {w : ℂ} (hw : w ∈ overlap p q) :
    rd u p =ᶠ[𝓝 w] rd u q ∘ trans p q := by
  filter_upwards [(isOpen_overlap p q).mem_nhds hw] with v hv using (rd_trans hv).symm

theorem trans_contDiffAt {p q : X} {w : ℂ} (hw : w ∈ overlap p q) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (trans p q) w :=
  ((chartMap_analyticAt contMDiff_id hw.1 hw.2).contDiffAt (n := n)).restrict_scalars ℝ

/-- `u` is smooth: all chart readings are `C^∞` over `ℝ`. -/
def IsSmooth (u : X → ℂ) : Prop := ∀ p : X, ContDiffOn ℝ ∞ (rd u p) (chartAt ℂ p).target

theorem IsSmooth.contDiffAt {u : X → ℂ} (hu : IsSmooth u) {p : X} {w : ℂ}
    (hw : w ∈ (chartAt ℂ p).target) : ContDiffAt ℝ ∞ (rd u p) w :=
  (hu p).contDiffAt ((chartAt ℂ p).open_target.mem_nhds hw)

/-- Smoothness can be checked in one chart around each point. -/
theorem isSmooth_of_local {u : X → ℂ}
    (h : ∀ x : X, ∃ p, x ∈ (chartAt ℂ p).source ∧ ContDiffAt ℝ ∞ (rd u p) (chartAt ℂ p x)) :
    IsSmooth u := by
  intro q w hw
  set x := (chartAt ℂ q).symm w
  obtain ⟨p, hxp, hp⟩ := h x
  have hwo : w ∈ overlap q p := ⟨hw, hxp⟩
  have hτ : trans q p w = chartAt ℂ p x := rfl
  have h1 : ContDiffAt ℝ ∞ (rd u p ∘ trans q p) w := by
    rw [← hτ] at hp
    exact hp.comp w (trans_contDiffAt hwo)
  exact (h1.congr_of_eventuallyEq (rd_eventuallyEq hwo)).contDiffWithinAt

theorem isSmooth_const (c : ℂ) : IsSmooth (fun _ : X => c) := fun p =>
  contDiffOn_const

theorem IsSmooth.add {u v : X → ℂ} (hu : IsSmooth u) (hv : IsSmooth v) :
    IsSmooth (u + v) := fun p => (hu p).add (hv p)

theorem IsSmooth.mul {u v : X → ℂ} (hu : IsSmooth u) (hv : IsSmooth v) :
    IsSmooth (u * v) := fun p => (hu p).mul (hv p)

theorem IsSmooth.smul {u : X → ℂ} (hu : IsSmooth u) (c : ℂ) : IsSmooth (c • u) := fun p =>
  (contDiffOn_const (c := c)).mul (hu p)

theorem IsSmooth.neg {u : X → ℂ} (hu : IsSmooth u) : IsSmooth (-u) := fun p => (hu p).neg

theorem IsSmooth.sub {u v : X → ℂ} (hu : IsSmooth u) (hv : IsSmooth v) :
    IsSmooth (u - v) := fun p => (hu p).sub (hv p)

theorem IsSmooth.div {u v : X → ℂ} (hu : IsSmooth u) (hv : IsSmooth v) (h0 : ∀ x, v x ≠ 0) :
    IsSmooth (fun x => u x / v x) := fun p => by
  have : rd (fun x => u x / v x) p = fun w => rd u p w * (rd v p w)⁻¹ := by
    funext w; simp [rd_apply, div_eq_mul_inv]
  rw [this]
  exact (hu p).mul ((hv p).inv fun w _ => h0 _)

theorem IsSmooth.sum {ι : Type*} (s : Finset ι) {u : ι → X → ℂ} (hu : ∀ i ∈ s, IsSmooth (u i)) :
    IsSmooth (fun x => ∑ i ∈ s, u i x) := fun p => by
  have : rd (fun x => ∑ i ∈ s, u i x) p = fun w => ∑ i ∈ s, rd (u i) p w := rfl
  rw [this]
  exact ContDiffOn.sum fun i hi => hu i hi p

theorem IsSmooth.conj {u : X → ℂ} (hu : IsSmooth u) :
    IsSmooth (fun x => (starRingEnd ℂ) (u x)) := fun p =>
  (Complex.conjCLE.contDiff.comp_contDiffOn (hu p) : _)

theorem IsSmooth.continuous {u : X → ℂ} (hu : IsSmooth u) : Continuous u := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  have h := (hu x).continuousOn.continuousAt
    ((chartAt ℂ x).open_target.mem_nhds ((chartAt ℂ x).map_source (mem_chart_source ℂ x)))
  have h2 := h.comp ((chartAt ℂ x).continuousAt (mem_chart_source ℂ x))
  refine h2.congr ?_
  filter_upwards [(chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)] with y hy
  simp [rd_apply, (chartAt ℂ x).left_inv hy]

/-! ### Extension by zero -/

open Classical in
/-- A function on a chart target, extended by `0` to `X`. -/
noncomputable def extend (p : X) (φ : ℂ → ℂ) : X → ℂ := fun x =>
  if x ∈ (chartAt ℂ p).source then φ (chartAt ℂ p x) else 0

theorem rd_extend_self {p : X} {φ : ℂ → ℂ} {w : ℂ} (hw : w ∈ (chartAt ℂ p).target) :
    rd (extend p φ) p w = φ w := by
  simp [rd_apply, extend, (chartAt ℂ p).map_target hw, (chartAt ℂ p).right_inv hw]

theorem extend_eq_zero_of_notMem [T2Space X] {p : X} {φ : ℂ → ℂ} {K : Set ℂ}
    (hφK : tsupport φ ⊆ K) {x : X} (hx : x ∉ (chartAt ℂ p).symm '' K) : extend p φ x = 0 := by
  unfold extend
  split_ifs with hxs
  · exact image_eq_zero_of_notMem_tsupport fun h =>
      hx ⟨_, hφK h, (chartAt ℂ p).left_inv hxs⟩
  · rfl

theorem isCompact_symm_image {p : X} {K : Set ℂ} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt ℂ p).target) : IsCompact ((chartAt ℂ p).symm '' K) :=
  hK.image_of_continuousOn ((chartAt ℂ p).continuousOn_symm.mono hKt)

theorem symm_image_subset_source {p : X} {K : Set ℂ} (hKt : K ⊆ (chartAt ℂ p).target) :
    (chartAt ℂ p).symm '' K ⊆ (chartAt ℂ p).source := by
  rintro _ ⟨w, hw, rfl⟩; exact (chartAt ℂ p).map_target (hKt hw)

/-- The extension by zero vanishes near every point outside `c_p⁻¹(K)`. -/
theorem extend_eventuallyEq_zero [T2Space X] {p : X} {φ : ℂ → ℂ} {K : Set ℂ} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt ℂ p).target) (hφK : tsupport φ ⊆ K) {x : X}
    (hx : x ∉ (chartAt ℂ p).symm '' K) : extend p φ =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [((isCompact_symm_image hK hKt).isClosed.isOpen_compl).mem_nhds hx] with y hy
  exact extend_eq_zero_of_notMem hφK hy

theorem isSmooth_extend [T2Space X] {p : X} {φ : ℂ → ℂ} (hφ : ContDiff ℝ ∞ φ) {K : Set ℂ}
    (hK : IsCompact K) (hKt : K ⊆ (chartAt ℂ p).target) (hφK : tsupport φ ⊆ K) :
    IsSmooth (extend p φ) := by
  refine isSmooth_of_local fun x => ?_
  by_cases hx : x ∈ (chartAt ℂ p).source
  · refine ⟨p, hx, hφ.contDiffAt.congr_of_eventuallyEq ?_⟩
    filter_upwards [(chartAt ℂ p).open_target.mem_nhds ((chartAt ℂ p).map_source hx)] with w hw
    exact rd_extend_self hw
  · have hx' : x ∉ (chartAt ℂ p).symm '' K := fun h => hx (symm_image_subset_source hKt h)
    refine ⟨x, mem_chart_source ℂ x, contDiffAt_const (c := (0 : ℂ)).congr_of_eventuallyEq ?_⟩
    have hc : ContinuousAt (chartAt ℂ x).symm (chartAt ℂ x x) :=
      (chartAt ℂ x).continuousAt_symm ((chartAt ℂ x).map_source (mem_chart_source ℂ x))
    have := hc.preimage_mem_nhds (by
      rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
      exact extend_eventuallyEq_zero hK hKt hφK hx')
    filter_upwards [this] with w hw
    exact hw

/-! ### A partition of unity -/

namespace DiscAtlas

variable (A : DiscAtlas X)

/-- The bump at the chart `j`: `1` on `ball z_j r_j`, supported in `closedBall z_j (2 r_j)`. -/
noncomputable def bump (j : Fin A.N) : ContDiffBump (A.ctr j) :=
  ⟨A.r j, 2 * A.r j, A.r_pos j, by linarith [A.r_pos j]⟩

/-- The bump at `j`, as a function on `X`. -/
noncomputable def β (j : Fin A.N) : X → ℂ := extend (A.p j) fun w => ((A.bump j w : ℝ) : ℂ)

theorem tsupport_bump_subset (j : Fin A.N) :
    tsupport (fun w => ((A.bump j w : ℝ) : ℂ)) ⊆ closedBall (A.ctr j) (2 * A.r j) := by
  refine (tsupport_comp_subset ofReal_zero _).trans ?_
  rw [(A.bump j).tsupport_eq]; rfl

theorem isSmooth_β [T2Space X] (j : Fin A.N) : IsSmooth (A.β j) :=
  isSmooth_extend (ofRealCLM.contDiff.comp (A.bump j).contDiff) (isCompact_closedBall _ _)
    (A.ball_subset_target j (by norm_num)) (A.tsupport_bump_subset j)

theorem β_re_nonneg (j : Fin A.N) (x : X) : 0 ≤ (A.β j x).re := by
  unfold β extend
  split_ifs
  · simp [(A.bump j).nonneg]
  · simp

theorem β_im (j : Fin A.N) (x : X) : (A.β j x).im = 0 := by
  unfold β extend
  split_ifs <;> simp

theorem sum_β_re_ge_one (x : X) : 1 ≤ (∑ j, A.β j x).re := by
  obtain ⟨j, hxs, hxb⟩ := A.cover x
  have h1 : (A.β j x).re = 1 := by
    simp only [β, extend, if_pos hxs]
    simp [(A.bump j).one_of_mem_closedBall (ball_subset_closedBall hxb)]
  rw [Complex.re_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ j), h1]
  have : 0 ≤ ∑ k ∈ Finset.univ.erase j, (A.β k x).re :=
    Finset.sum_nonneg fun k _ => A.β_re_nonneg k x
  linarith

theorem sum_β_ne_zero (x : X) : (∑ j, A.β j x) ≠ 0 := fun h => by
  have := A.sum_β_re_ge_one x
  rw [h, Complex.zero_re] at this
  linarith

/-- The partition of unity `ρ_j = β_j / ∑ β`. -/
noncomputable def pou (j : Fin A.N) : X → ℂ := fun x => A.β j x / ∑ k, A.β k x

theorem isSmooth_pou [T2Space X] (j : Fin A.N) : IsSmooth (A.pou j) :=
  (A.isSmooth_β j).div (IsSmooth.sum _ fun k _ => A.isSmooth_β k) A.sum_β_ne_zero

theorem sum_pou (x : X) : ∑ j, A.pou j x = 1 := by
  simp only [pou, ← Finset.sum_div]
  exact div_self (A.sum_β_ne_zero x)

/-- The support of `ρ_j`. -/
noncomputable def pouSupp (j : Fin A.N) : Set X :=
  (chartAt ℂ (A.p j)).symm '' closedBall (A.ctr j) (2 * A.r j)

theorem pouSupp_subset_source (j : Fin A.N) : A.pouSupp j ⊆ (chartAt ℂ (A.p j)).source :=
  symm_image_subset_source (A.ball_subset_target j (by norm_num))

theorem isCompact_pouSupp (j : Fin A.N) : IsCompact (A.pouSupp j) :=
  isCompact_symm_image (isCompact_closedBall _ _) (A.ball_subset_target j (by norm_num))

theorem pou_eventuallyEq_zero [T2Space X] (j : Fin A.N) {x : X} (hx : x ∉ A.pouSupp j) :
    A.pou j =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [extend_eventuallyEq_zero (isCompact_closedBall _ _)
    (A.ball_subset_target j (by norm_num)) (A.tsupport_bump_subset j) hx] with y hy
  simp only [pou]
  rw [show A.β j y = 0 from hy, zero_div]

end DiscAtlas

end JacobianChallenge.Surface
