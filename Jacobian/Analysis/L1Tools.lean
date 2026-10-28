import Jacobian.Analysis.WeylDbar
import Mathlib.MeasureTheory.Function.L1Space.AEEqFun
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Bases
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity

/-!
# `L¹` limits on sets of the plane, and gluing local representatives

* `L1Conv f F K`: `∫_K ‖f n - F‖ → 0`.
* `exists_L1Conv`: an `L¹(K)`-Cauchy sequence has a limit; `L1Conv.ae_eq`: limits are unique
  a.e.; `L1Conv.tendsto_integral_mul`: pairing with a bounded function passes to the limit.
* `exists_glue`: local continuous representatives of a function on an open set glue to one
  function, a.e. equal to it on the whole open set, and locally equal to the local
  representatives.
-/

set_option linter.unusedSectionVars false

namespace JacobianChallenge.Analysis

open MeasureTheory Set Metric Filter Topology

/-- `f n → F` in `L¹(K)`. -/
def L1Conv (f : ℕ → ℂ → ℂ) (F : ℂ → ℂ) (K : Set ℂ) : Prop :=
  Tendsto (fun n => ∫ z in K, ‖f n z - F z‖) atTop (𝓝 0)

/-- An `L¹(K)`-Cauchy sequence of integrable functions converges in `L¹(K)`. -/
theorem exists_L1Conv {f : ℕ → ℂ → ℂ} {K : Set ℂ} (hint : ∀ n, IntegrableOn (f n) K)
    (hC : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, ∫ z in K, ‖f n z - f m z‖ < ε) :
    ∃ F : ℂ → ℂ, IntegrableOn F K ∧ L1Conv f F K := by
  set g : ℕ → ℂ →₁[volume.restrict K] ℂ := fun n => (hint n).toL1 (f n)
  have hdist : ∀ m n, dist (g n) (g m) = ∫ z in K, ‖f n z - f m z‖ := by
    intro m n
    rw [dist_eq_norm, L1.norm_eq_integral_norm]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (g n) (g m), (hint n).coeFn_toL1, (hint m).coeFn_toL1]
      with z h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
  have hcs : CauchySeq g := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := hC ε hε
    exact ⟨N, fun n hn => by rw [hdist]; exact hN N le_rfl n hn⟩
  obtain ⟨Fl, hFl⟩ := cauchySeq_tendsto_of_complete hcs
  refine ⟨Fl, L1.integrable_coeFn Fl, ?_⟩
  have e : ∀ n, ∫ z in K, ‖f n z - Fl z‖ = dist (g n) Fl := by
    intro n
    rw [dist_eq_norm, L1.norm_eq_integral_norm]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (g n) Fl, (hint n).coeFn_toL1] with z h1 h2
    rw [h1, Pi.sub_apply, h2]
  unfold L1Conv
  simp_rw [e]
  exact (tendsto_iff_dist_tendsto_zero.mp hFl)

theorem L1Conv.integrableOn_sub {f : ℕ → ℂ → ℂ} {F : ℂ → ℂ} {K : Set ℂ}
    (hf : IntegrableOn (f 0) K) (hF : IntegrableOn F K) : IntegrableOn (fun z => f 0 z - F z) K :=
  hf.sub hF

/-- `L¹` limits are unique a.e. -/
theorem L1Conv.ae_eq {f : ℕ → ℂ → ℂ} {F F' : ℂ → ℂ} {K : Set ℂ}
    (hfi : ∀ n, IntegrableOn (f n) K) (hF : IntegrableOn F K) (hF' : IntegrableOn F' K)
    (h : L1Conv f F K) (h' : L1Conv f F' K) : F =ᵐ[volume.restrict K] F' := by
  have hle : ∀ n, ∫ z in K, ‖F z - F' z‖ ≤
      (∫ z in K, ‖f n z - F z‖) + ∫ z in K, ‖f n z - F' z‖ := by
    intro n
    have i1 : IntegrableOn (fun z => ‖f n z - F z‖) K := ((hfi n).sub hF).norm
    have i2 : IntegrableOn (fun z => ‖f n z - F' z‖) K := ((hfi n).sub hF').norm
    rw [← integral_add i1 i2]
    refine integral_mono (hF.sub hF').norm (((hfi n).sub hF).norm.add ((hfi n).sub hF').norm)
      fun z => ?_
    calc ‖F z - F' z‖ = ‖(f n z - F' z) - (f n z - F z)‖ := by congr 1; ring
      _ ≤ ‖f n z - F' z‖ + ‖f n z - F z‖ := norm_sub_le _ _
      _ = _ := add_comm _ _
  have hlim : Tendsto (fun n => (∫ z in K, ‖f n z - F z‖) + ∫ z in K, ‖f n z - F' z‖) atTop
      (𝓝 0) := by simpa using h.add h'
  have h0 : ∫ z in K, ‖F z - F' z‖ = 0 :=
    le_antisymm (ge_of_tendsto' hlim hle) (integral_nonneg fun _ => norm_nonneg _)
  have := (integral_eq_zero_iff_of_nonneg (fun _ => norm_nonneg _) (hF.sub hF').norm).mp h0
  filter_upwards [this] with z hz
  simpa [sub_eq_zero] using hz

/-- Pairing with a bounded function passes to the limit. -/
theorem L1Conv.tendsto_integral_mul {f : ℕ → ℂ → ℂ} {F : ℂ → ℂ} {K : Set ℂ}
    (hfi : ∀ n, IntegrableOn (f n) K) (hF : IntegrableOn F K) (h : L1Conv f F K)
    {g : ℂ → ℂ} (hg : AEStronglyMeasurable g (volume.restrict K)) {C : ℝ}
    (hC : ∀ z, ‖g z‖ ≤ C) :
    Tendsto (fun n => ∫ z in K, f n z * g z) atTop (𝓝 (∫ z in K, F z * g z)) := by
  have hi : ∀ n, IntegrableOn (fun z => f n z * g z) K := fun n =>
    (hfi n).mul_bdd hg (ae_of_all _ hC)
  have hiF : IntegrableOn (fun z => F z * g z) K := hF.mul_bdd hg (ae_of_all _ hC)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
    (by simpa using h.const_mul C)
  rw [← integral_sub (hi n) hiF, ← integral_const_mul]
  refine (norm_integral_le_integral_norm _).trans (integral_mono ((hi n).sub hiF).norm
    (((hfi n).sub hF).norm.const_mul C) fun z => ?_)
  rw [← sub_mul, norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hC z) (norm_nonneg _)

theorem L1Conv.mono {f : ℕ → ℂ → ℂ} {F : ℂ → ℂ} {K K' : Set ℂ} (hK' : K' ⊆ K)
    (hfi : ∀ n, IntegrableOn (f n) K) (hF : IntegrableOn F K) (h : L1Conv f F K) :
    L1Conv f F K' := by
  refine squeeze_zero (fun _ => integral_nonneg fun _ => norm_nonneg _) (fun n => ?_) h
  exact setIntegral_mono_set ((hfi n).sub hF).norm (ae_of_all _ fun _ => norm_nonneg _)
    (Eventually.of_forall hK')

theorem L1Conv.congr {f g : ℕ → ℂ → ℂ} {F G : ℂ → ℂ} {K : Set ℂ} (hK : MeasurableSet K)
    (hfg : ∀ n, ∀ z ∈ K, f n z = g n z) (hFG : ∀ᵐ z, z ∈ K → F z = G z) (h : L1Conv f F K) :
    L1Conv g G K := by
  refine Filter.Tendsto.congr (fun n => ?_) h
  refine integral_congr_ae ?_
  rw [EventuallyEq, ae_restrict_iff' hK]
  filter_upwards [hFG] with z hz hzK
  rw [hfg n z hzK, hz hzK]

theorem L1Conv.mul_bounded {f : ℕ → ℂ → ℂ} {F : ℂ → ℂ} {K : Set ℂ} (h : L1Conv f F K)
    {m : ℂ → ℂ} {C : ℝ} (hm : ∀ z ∈ K, ‖m z‖ ≤ C) (hK : MeasurableSet K)
    (hint : ∀ n, IntegrableOn (fun z => ‖f n z - F z‖) K) :
    L1Conv (fun n z => m z * f n z) (fun z => m z * F z) K := by
  refine squeeze_zero (fun _ => integral_nonneg fun _ => norm_nonneg _) (fun n => ?_)
    (by simpa using h.const_mul C)
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) ((hint n).const_mul C) ?_
  rw [EventuallyLE, ae_restrict_iff' hK]
  refine ae_of_all _ fun z hz => ?_
  rw [← mul_sub, norm_mul]
  exact mul_le_mul_of_nonneg_right (hm z hz) (norm_nonneg _)

/-- **Gluing** local continuous representatives over an open set. -/
theorem exists_glue {O : Set ℂ} (hO : IsOpen O) {U : ℂ → ℂ} {Q : (ℂ → ℂ) → ℂ → ℝ → Prop}
    (loc : ∀ x ∈ O, ∃ ρ > 0, ball x ρ ⊆ O ∧ ∃ g : ℂ → ℂ, Q g x ρ ∧
      ContinuousOn g (ball x ρ) ∧ ∀ᵐ z, z ∈ ball x ρ → U z = g z) :
    ∃ G : ℂ → ℂ, (∀ᵐ z, z ∈ O → U z = G z) ∧
      ∀ x ∈ O, ∃ ρ > 0, ball x ρ ⊆ O ∧ ∃ g : ℂ → ℂ, Q g x ρ ∧ EqOn G g (ball x ρ) := by
  classical
  choose! ρ hρ hρO g hQ hgc hgae using loc
  set G : ℂ → ℂ := fun z => g z z
  have hagree : ∀ x ∈ O, ∀ z ∈ O, EqOn (g x) (g z) (ball x (ρ x) ∩ ball z (ρ z)) := by
    intro x hx z hz
    refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ (isOpen_ball.inter isOpen_ball)
      ((hgc x hx).mono inter_subset_left) ((hgc z hz).mono inter_subset_right)
    rw [EventuallyEq, ae_restrict_iff' (isOpen_ball.inter isOpen_ball).measurableSet]
    filter_upwards [hgae x hx, hgae z hz] with y h1 h2 hy
    rw [← h1 hy.1, ← h2 hy.2]
  have hloc : ∀ x ∈ O, EqOn G (g x) (ball x (ρ x)) := by
    intro x hx z hz
    have hzO : z ∈ O := hρO x hx hz
    exact (hagree x hx z hzO ⟨hz, mem_ball_self (hρ z hzO)⟩).symm
  refine ⟨G, ?_, fun x hx => ⟨ρ x, hρ x hx, hρO x hx, g x, hQ x hx, hloc x hx⟩⟩
  -- countably many balls cover `O`
  obtain ⟨t, htO, htc, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (s := O) (f := fun x => ball x (ρ x)) fun x hx =>
      mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self (hρ x hx)))
  have hloc' : ∀ x ∈ t, ∀ᵐ z, z ∈ ball x (ρ x) → U z = G z := by
    intro x hx
    filter_upwards [hgae x (htO hx)] with z hz hzb
    rw [hz hzb, hloc x (htO hx) hzb]
  haveI := htc.to_subtype
  have hall : ∀ᵐ z, ∀ x : t, z ∈ ball (x : ℂ) (ρ x) → U z = G z :=
    ae_all_iff.mpr fun x => hloc' x x.2
  filter_upwards [hall] with z hz hzO
  obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.mp (hcov hzO)
  exact hz ⟨x, hx⟩ hzx

end JacobianChallenge.Analysis
