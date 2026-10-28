import Jacobian.Surface.Stokes
import Jacobian.Surface.HoloForm
import Jacobian.Analysis.L1Tools
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The `L²` space of forms on a compact Riemann surface

`A.L2 = ⨁ᵢ L²(S i)` (an `ℓ²`-sum over the pieces of the atlas). A continuous family `θ` (a
`(0,1)`- or `(1,0)`-form) gives `A.toL2 θ` (its readings on the pieces); the inner product is
the surface integral `⟪θ, β⟫ = ∫_X conj(θ) β` (`inner_toL2`).

`integral_sq_le_norm_toL2`: a chart reading of a form is controlled in `L²` of the disc of radius
`(3/2) r_k` by the global `L²` norm.
-/

set_option linter.unusedSectionVars false

namespace JacobianChallenge.Surface

open JacobianChallenge.Analysis JacobianChallenge.Periods JacobianChallenge.HolomorphicForms
  MeasureTheory Set Metric Filter Topology Complex
open scoped Manifold ContDiff InnerProductSpace

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/-- A family with continuous readings. -/
def ContFam (θ : X → ℂ → ℂ) : Prop := ∀ p : X, ContinuousOn (θ p) (chartAt ℂ p).target

theorem SmoothFam.contFam {θ : X → ℂ → ℂ} (h : SmoothFam θ) : ContFam θ := fun p =>
  (h p).continuousOn

theorem DiscAtlas.IsDensity.smulF {σ : X → ℂ → ℂ} (hσ : DiscAtlas.IsDensity σ) (u : X → ℂ) :
    DiscAtlas.IsDensity (smulF u σ) := fun p q w hw => by
  simp only [Surface.smulF, hσ p q w hw, ← rd_trans (u := u) hw]; ring

theorem ContFam.sub {θ β : X → ℂ → ℂ} (hθ : ContFam θ) (hβ : ContFam β) : ContFam (θ - β) :=
  fun p => (hθ p).sub (hβ p)

theorem ContFam.add {θ β : X → ℂ → ℂ} (hθ : ContFam θ) (hβ : ContFam β) : ContFam (θ + β) :=
  fun p => (hθ p).add (hβ p)

namespace DiscAtlas

variable (A : DiscAtlas X)

theorem S_subset_closedBall (i : Fin A.N) : A.S i ⊆ closedBall (A.ctr i) (A.r i) :=
  (A.S_subset_ball i).trans ball_subset_closedBall

theorem closedBall_subset_target (i : Fin A.N) :
    closedBall (A.ctr i) (A.r i) ⊆ (chartAt ℂ (A.p i)).target := by
  have := A.ball_subset_target i (s := 1) (by norm_num)
  rwa [one_mul] at this

instance isFiniteMeasure_S (i : Fin A.N) : IsFiniteMeasure (volume.restrict (A.S i)) :=
  isFiniteMeasure_restrict.mpr
    (measure_mono (A.S_subset_closedBall i) |>.trans_lt measure_closedBall_lt_top).ne

theorem memLp_S (i : Fin A.N) {f : ℂ → ℂ} (hf : ContinuousOn f (chartAt ℂ (A.p i)).target) :
    MemLp f 2 (volume.restrict (A.S i)) := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (A.ctr i) (A.r i)).exists_bound_of_continuousOn
    (hf.mono (A.closedBall_subset_target i))
  refine MemLp.of_bound ((hf.mono ((A.S_subset_closedBall i).trans
    (A.closedBall_subset_target i))).aestronglyMeasurable (A.measurableSet_S i)) C ?_
  exact (ae_restrict_iff' (A.measurableSet_S i)).mpr
    (ae_of_all _ fun w hw => hC w (A.S_subset_closedBall i hw))

/-- The `L²` space of forms. -/
abbrev L2 := PiLp 2 (fun i : Fin A.N => Lp ℂ 2 (volume.restrict (A.S i)))

/-- A continuous family, as an element of `L²`. -/
noncomputable def toL2 (θ : X → ℂ → ℂ) (hθ : ContFam θ) : A.L2 :=
  WithLp.toLp 2 fun i => (A.memLp_S i (hθ (A.p i))).toLp (θ (A.p i))

theorem toL2_apply (θ : X → ℂ → ℂ) (hθ : ContFam θ) (i : Fin A.N) :
    A.toL2 θ hθ i = (A.memLp_S i (hθ (A.p i))).toLp (θ (A.p i)) := rfl

theorem inner_toL2 {θ β : X → ℂ → ℂ} (hθ : ContFam θ) (hβ : ContFam β) :
    ⟪A.toL2 θ hθ, A.toL2 β hβ⟫_ℂ = A.integral (fun p w => (starRingEnd ℂ) (θ p w) * β p w) := by
  rw [PiLp.inner_apply]
  unfold integral
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [toL2_apply, toL2_apply, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(A.memLp_S i (hθ (A.p i))).coeFn_toLp, (A.memLp_S i (hβ (A.p i))).coeFn_toLp]
    with w h1 h2
  rw [h1, h2]
  simp [mul_comm]

theorem norm_toL2_sq {θ : X → ℂ → ℂ} (hθ : ContFam θ) :
    ‖A.toL2 θ hθ‖ ^ 2 = (A.integral (fun p w => (starRingEnd ℂ) (θ p w) * θ p w)).re := by
  rw [← A.inner_toL2 hθ hθ, ← inner_self_eq_norm_sq (𝕜 := ℂ)]
  rfl

theorem toL2_sub {θ β : X → ℂ → ℂ} (hθ : ContFam θ) (hβ : ContFam β) :
    A.toL2 (θ - β) (hθ.sub hβ) = A.toL2 θ hθ - A.toL2 β hβ := by
  refine PiLp.ext fun i => ?_
  rw [PiLp.sub_apply, toL2_apply, toL2_apply, toL2_apply]
  exact MemLp.toLp_sub _ _

theorem toL2_add {θ β : X → ℂ → ℂ} (hθ : ContFam θ) (hβ : ContFam β) :
    A.toL2 (θ + β) (hθ.add hβ) = A.toL2 θ hθ + A.toL2 β hβ := by
  refine PiLp.ext fun i => ?_
  rw [PiLp.add_apply, toL2_apply, toL2_apply, toL2_apply]
  exact MemLp.toLp_add _ _

theorem toL2_congr {θ β : X → ℂ → ℂ} (hθ : ContFam θ) (hβ : ContFam β) (h : θ = β) :
    A.toL2 θ hθ = A.toL2 β hβ := by subst h; rfl

/-! ### The local `L²` bound -/

/-- The cutoff at the chart `k`: `1` on the disc of radius `(3/2) r_k`, supported in the disc of
radius `2 r_k`. -/
noncomputable def cutBump (k : Fin A.N) : ContDiffBump (A.ctr k) :=
  ⟨3 / 2 * A.r k, 2 * A.r k, by have := A.r_pos k; positivity, by linarith [A.r_pos k]⟩

/-- The cutoff at the chart `k`, as a function on `X`. -/
noncomputable def cut (k : Fin A.N) : X → ℂ :=
  extend (A.p k) fun w => ((A.cutBump k w : ℝ) : ℂ)

theorem tsupport_cutBump_subset (k : Fin A.N) :
    tsupport (fun w => ((A.cutBump k w : ℝ) : ℂ)) ⊆ closedBall (A.ctr k) (2 * A.r k) := by
  refine (tsupport_comp_subset ofReal_zero _).trans ?_
  rw [(A.cutBump k).tsupport_eq]; rfl

theorem isSmooth_cut [T2Space X] (k : Fin A.N) : IsSmooth (A.cut k) :=
  isSmooth_extend (ofRealCLM.contDiff.comp (A.cutBump k).contDiff) (isCompact_closedBall _ _)
    (A.ball_subset_target k (by norm_num)) (A.tsupport_cutBump_subset k)

theorem cut_eq_zero [T2Space X] (k : Fin A.N) {x : X} (hx : x ∉ A.pouSupp k) : A.cut k x = 0 :=
  extend_eq_zero_of_notMem (A.tsupport_cutBump_subset k) hx

theorem cut_eq_ofReal (k : Fin A.N) (x : X) : ∃ c : ℝ, 0 ≤ c ∧ c ≤ 1 ∧ A.cut k x = c := by
  unfold cut extend
  split_ifs
  · exact ⟨_, (A.cutBump k).nonneg, (A.cutBump k).le_one, rfl⟩
  · exact ⟨0, le_rfl, zero_le_one, by simp⟩

theorem rd_cut_self (k : Fin A.N) {w : ℂ} (hw : w ∈ (chartAt ℂ (A.p k)).target)
    (hwb : w ∈ closedBall (A.ctr k) (3 / 2 * A.r k)) : rd (A.cut k) (A.p k) w = 1 := by
  rw [cut, rd_extend_self hw]
  simp [(A.cutBump k).one_of_mem_closedBall hwb]

/-- A density vanishing off `pouSupp k`, continuous on the chart target `k`, is integrable there. -/
theorem integrableOn_target_of_supp [T2Space X] {σ : X → ℂ → ℂ} (k : Fin A.N)
    (h0 : ∀ q : X, ∀ w ∈ (chartAt ℂ q).target, (chartAt ℂ q).symm w ∉ A.pouSupp k → σ q w = 0)
    (hc : ContinuousOn (σ (A.p k)) (chartAt ℂ (A.p k)).target) :
    IntegrableOn (σ (A.p k)) (chartAt ℂ (A.p k)).target := by
  have hK := A.ball_subset_target k (s := 2) (by norm_num)
  refine ((hc.mono hK).integrableOn_compact (isCompact_closedBall _ _)).of_forall_diff_eq_zero
    (chartAt ℂ (A.p k)).open_target.measurableSet fun w ⟨hw, hwb⟩ => ?_
  exact h0 _ w hw (A.symm_notMem_pouSupp k hw hwb)

theorem conj_mul_self_eq (z : ℂ) : (starRingEnd ℂ) z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) :=
  conj_mul_self' z

theorem setIntegral_re {f : ℂ → ℂ} {s : Set ℂ} (hf : IntegrableOn f s) :
    (∫ x in s, f x).re = ∫ x in s, (f x).re := by
  have := integral_re hf
  simpa using this.symm

/-- **Local `L²` bound.** -/
theorem integral_sq_le_norm_toL2 [T2Space X] (k : Fin A.N) {α : X → ℂ → ℂ}
    (hd : IsDensity (fun p w => (starRingEnd ℂ) (α p w) * α p w)) (hc : ContFam α) :
    ∫ w in closedBall (A.ctr k) (3 / 2 * A.r k), ‖α (A.p k) w‖ ^ 2 ≤ ‖A.toL2 α hc‖ ^ 2 := by
  set ρ : X → ℂ → ℂ := fun p w => (starRingEnd ℂ) (α p w) * α p w with hρ
  set σ := smulF (A.cut k) ρ
  have hσ : IsDensity σ := hd.smulF _
  have h0 : ∀ q : X, ∀ w ∈ (chartAt ℂ q).target, (chartAt ℂ q).symm w ∉ A.pouSupp k →
      σ q w = 0 := fun q w _ hx => by
    simp [σ, smulF, rd_apply, A.cut_eq_zero k hx]
  have hcσ : ∀ q, ContinuousOn (σ q) (chartAt ℂ q).target := fun q =>
    ((A.isSmooth_cut k q).continuousOn).mul
      ((Complex.continuous_conj.comp_continuousOn (hc q)).mul (hc q))
  have hreσ : ∀ q w, (σ q w).re = (rd (A.cut k) q w).re * ‖α q w‖ ^ 2 ∧
      0 ≤ (σ q w).re ∧ (σ q w).re ≤ ‖α q w‖ ^ 2 := by
    intro q w
    obtain ⟨c, hc0, hc1, hcx⟩ := A.cut_eq_ofReal k ((chartAt ℂ q).symm w)
    have : σ q w = ((c * ‖α q w‖ ^ 2 : ℝ) : ℂ) := by
      simp only [σ, smulF, rd_apply, hcx, ρ, conj_mul_self_eq]; push_cast; ring
    rw [this, Complex.ofReal_re, rd_apply, hcx, Complex.ofReal_re]
    exact ⟨rfl, by positivity, by nlinarith [sq_nonneg ‖α q w‖]⟩
  -- the chart side
  have hint := A.integrableOn_target_of_supp k h0 (hcσ (A.p k))
  have e1 := A.integral_eq_chart_of_supp hσ k h0 (hcσ (A.p k))
  have hK : closedBall (A.ctr k) (3 / 2 * A.r k) ⊆ (chartAt ℂ (A.p k)).target :=
    A.ball_subset_target k (by norm_num)
  have hlow : ∫ w in closedBall (A.ctr k) (3 / 2 * A.r k), ‖α (A.p k) w‖ ^ 2 ≤
      (A.integral σ).re := by
    rw [e1, setIntegral_re hint]
    calc ∫ w in closedBall (A.ctr k) (3 / 2 * A.r k), ‖α (A.p k) w‖ ^ 2
        = ∫ w in closedBall (A.ctr k) (3 / 2 * A.r k), (σ (A.p k) w).re := by
          refine setIntegral_congr_fun measurableSet_closedBall fun w hw => ?_
          rw [(hreσ _ w).1, rd_cut_self A k (hK hw) hw]; simp
      _ ≤ ∫ w in (chartAt ℂ (A.p k)).target, (σ (A.p k) w).re :=
          setIntegral_mono_set hint.re (ae_of_all _ fun w => (hreσ _ w).2.1)
            (Eventually.of_forall hK)
  -- the global side
  have hup : (A.integral σ).re ≤ (A.integral ρ).re := by
    unfold integral
    rw [Complex.re_sum, Complex.re_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have hS : A.S i ⊆ (chartAt ℂ (A.p i)).target :=
      (A.S_subset_closedBall i).trans (A.closedBall_subset_target i)
    have hi1 : IntegrableOn (σ (A.p i)) (A.S i) :=
      (((hcσ (A.p i)).mono (A.closedBall_subset_target i)).integrableOn_compact
        (isCompact_closedBall _ _)).mono_set (A.S_subset_closedBall i)
    have hcρ : ContinuousOn (ρ (A.p i)) (chartAt ℂ (A.p i)).target :=
      (Complex.continuous_conj.comp_continuousOn (hc _)).mul (hc _)
    have hi2 : IntegrableOn (ρ (A.p i)) (A.S i) :=
      ((hcρ.mono (A.closedBall_subset_target i)).integrableOn_compact
        (isCompact_closedBall _ _)).mono_set (A.S_subset_closedBall i)
    rw [setIntegral_re hi1, setIntegral_re hi2]
    refine setIntegral_mono_on hi1.re hi2.re (A.measurableSet_S i) fun w _ => ?_
    have := (hreσ (A.p i) w).2.2
    have e : (ρ (A.p i) w).re = ‖α (A.p i) w‖ ^ 2 := by
      simp only [ρ]; rw [conj_mul_self_eq, Complex.ofReal_re]
    rw [e]; exact this
  rw [A.norm_toL2_sq hc]
  exact hlow.trans hup

end DiscAtlas

end JacobianChallenge.Surface
