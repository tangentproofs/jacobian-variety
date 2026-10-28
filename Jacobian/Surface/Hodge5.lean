import Jacobian.Surface.Hodge4

/-!
# Hodge decomposition, part 5: `L¹`-Cauchy sequences and chaining the chart constants

* `L1Cauchy f K`: the sequence `f n` is Cauchy in `L¹(K)`; stability under sums, constants,
  restriction and transfer along holomorphic maps.
* `index_connected`: on a connected space covered by open sets `U i`, a property of indices
  that holds for one index and propagates along nonempty overlaps holds for every index with
  `U i` nonempty.
-/

set_option linter.unusedSectionVars false

namespace JacobianChallenge.Surface

open JacobianChallenge.Analysis JacobianChallenge.Periods JacobianChallenge.HolomorphicForms
  MeasureTheory Set Metric Filter Topology Complex
open scoped Manifold ContDiff InnerProductSpace

/-- `f n` is Cauchy in `L¹(K)`. -/
def L1Cauchy (f : ℕ → ℂ → ℂ) (K : Set ℂ) : Prop :=
  ∀ δ > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, ∫ z in K, ‖f n z - f m z‖ < δ

theorem L1Cauchy.mono {f : ℕ → ℂ → ℂ} {K K' : Set ℂ} (hK' : K' ⊆ K)
    (hint : ∀ n m, IntegrableOn (fun z => ‖f n z - f m z‖) K) (h : L1Cauchy f K) :
    L1Cauchy f K' := fun δ hδ => by
  obtain ⟨N, hN⟩ := h δ hδ
  exact ⟨N, fun m hm n hn => lt_of_le_of_lt (setIntegral_mono_set (hint n m)
    (ae_of_all _ fun _ => norm_nonneg _) (Eventually.of_forall hK')) (hN m hm n hn)⟩

theorem L1Cauchy.add {f g : ℕ → ℂ → ℂ} {K : Set ℂ}
    (hfi : ∀ n m, IntegrableOn (fun z => ‖f n z - f m z‖) K)
    (hgi : ∀ n m, IntegrableOn (fun z => ‖g n z - g m z‖) K)
    (hf : L1Cauchy f K) (hg : L1Cauchy g K) : L1Cauchy (fun n z => f n z + g n z) K :=
  fun δ hδ => by
  obtain ⟨N₁, h₁⟩ := hf (δ / 2) (by positivity)
  obtain ⟨N₂, h₂⟩ := hg (δ / 2) (by positivity)
  refine ⟨max N₁ N₂, fun m hm n hn => ?_⟩
  calc ∫ z in K, ‖f n z + g n z - (f m z + g m z)‖
      ≤ ∫ z in K, (‖f n z - f m z‖ + ‖g n z - g m z‖) :=
        integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) ((hfi n m).add (hgi n m))
          (ae_of_all _ fun z => by
            calc ‖f n z + g n z - (f m z + g m z)‖ = ‖(f n z - f m z) + (g n z - g m z)‖ := by
                  congr 1; ring
              _ ≤ _ := norm_add_le _ _)
    _ = (∫ z in K, ‖f n z - f m z‖) + ∫ z in K, ‖g n z - g m z‖ :=
        integral_add (hfi n m) (hgi n m)
    _ < δ / 2 + δ / 2 := add_lt_add (h₁ m (le_of_max_le_left hm) n (le_of_max_le_left hn))
        (h₂ m (le_of_max_le_right hm) n (le_of_max_le_right hn))
    _ = δ := by ring

theorem L1Cauchy.neg {f : ℕ → ℂ → ℂ} {K : Set ℂ} (hf : L1Cauchy f K) :
    L1Cauchy (fun n z => -f n z) K := fun δ hδ => by
  obtain ⟨N, hN⟩ := hf δ hδ
  refine ⟨N, fun m hm n hn => ?_⟩
  have := hN m hm n hn
  calc ∫ z in K, ‖-f n z - -f m z‖ = ∫ z in K, ‖f n z - f m z‖ := by
        congr 1; funext z; rw [← norm_neg]; congr 1; ring
    _ < δ := this

/-- A Cauchy sequence of constants is `L¹`-Cauchy on a set of finite measure. -/
theorem L1Cauchy.const {c : ℕ → ℂ} (hc : CauchySeq c) {K : Set ℂ} (hK : volume K < ⊤) :
    L1Cauchy (fun n _ => c n) K := fun δ hδ => by
  set V := volume.real K + 1
  have hV : 0 < V := by positivity
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hc (δ / V) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  rw [setIntegral_const, smul_eq_mul]
  have := hN n hn m hm
  rw [dist_eq_norm] at this
  calc volume.real K * ‖c n - c m‖ ≤ V * ‖c n - c m‖ := by
        gcongr; simp [V]
    _ < V * (δ / V) := by gcongr
    _ = δ := by field_simp

/-- If constants are `L¹`-Cauchy on a set of positive measure, they are Cauchy. -/
theorem cauchySeq_of_L1Cauchy_const {c : ℕ → ℂ} {K : Set ℂ} (hK : 0 < volume.real K)
    (h : L1Cauchy (fun n _ => c n) K) : CauchySeq c := by
  rw [Metric.cauchySeq_iff]
  intro δ hδ
  obtain ⟨N, hN⟩ := h (δ * volume.real K) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  have := hN n hn m hm
  rw [setIntegral_const, smul_eq_mul, mul_comm] at this
  rw [dist_eq_norm]
  exact lt_of_mul_lt_mul_right this hK.le

/-- Transfer of `L¹`-Cauchy sequences along a holomorphic injective map. -/
theorem L1Cauchy.comp_holo {f : ℕ → ℂ → ℂ} {τ : ℂ → ℂ} {B K : Set ℂ}
    (hB : IsCompact B) (hBm : MeasurableSet B) (hτd : ∀ w ∈ B, DifferentiableAt ℂ τ w)
    (hτc : ContinuousOn (deriv τ) B) (hinj : InjOn τ B) (hd : ∀ w ∈ B, deriv τ w ≠ 0)
    (hτB : τ '' B ⊆ K) (hfc : ∀ n m, ContinuousOn (fun w => f n (τ w) - f m (τ w)) B)
    (hint : ∀ n m, IntegrableOn (fun z => ‖f n z - f m z‖) K) (h : L1Cauchy f K) :
    L1Cauchy (fun n => f n ∘ τ) B := by
  obtain ⟨c, hc, hcB⟩ : ∃ c > 0, ∀ w ∈ B, c ≤ ‖deriv τ w‖ ^ 2 := by
    rcases B.eq_empty_or_nonempty with hBe | hBne
    · exact ⟨1, one_pos, by simp [hBe]⟩
    · obtain ⟨w₀, hw₀, hmin⟩ := hB.exists_isMinOn hBne (hτc.norm.pow 2)
      exact ⟨‖deriv τ w₀‖ ^ 2, by have := hd w₀ hw₀; positivity, fun w hw => hmin hw⟩
  intro δ hδ
  obtain ⟨N, hN⟩ := h (c * δ) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  have hi1 : IntegrableOn (fun w => ‖f n (τ w) - f m (τ w)‖) B :=
    (hfc n m).norm.integrableOn_compact hB
  have hi2 : IntegrableOn (fun w => ‖deriv τ w‖ ^ 2 * ‖f n (τ w) - f m (τ w)‖) B :=
    ((hτc.norm.pow 2).mul (hfc n m).norm).integrableOn_compact hB
  calc ∫ w in B, ‖(f n ∘ τ) w - (f m ∘ τ) w‖
      ≤ ∫ w in B, c⁻¹ * (‖deriv τ w‖ ^ 2 * ‖f n (τ w) - f m (τ w)‖) := by
        refine setIntegral_mono_on hi1 (hi2.const_mul _) hBm fun w hw => ?_
        simp only [Function.comp_apply]
        rw [← mul_assoc]
        have : 1 ≤ c⁻¹ * ‖deriv τ w‖ ^ 2 := by
          rw [inv_mul_eq_div, le_div_iff₀ hc, one_mul]; exact hcB w hw
        nlinarith [norm_nonneg (f n (τ w) - f m (τ w))]
    _ = c⁻¹ * ∫ v in τ '' B, ‖f n v - f m v‖ := by
        rw [integral_const_mul, integral_image_holo_real hBm hτd hinj]
    _ ≤ c⁻¹ * ∫ z in K, ‖f n z - f m z‖ :=
        mul_le_mul_of_nonneg_left (setIntegral_mono_set (hint n m)
          (ae_of_all _ fun _ => norm_nonneg _) (Eventually.of_forall hτB)) (inv_nonneg.mpr hc.le)
    _ < c⁻¹ * (c * δ) := by gcongr; exact hN m hm n hn
    _ = δ := by field_simp

/-- An `L¹`-Cauchy sequence converges in `L¹`. -/
theorem L1Cauchy.exists_lim {f : ℕ → ℂ → ℂ} {K : Set ℂ} (hint : ∀ n, IntegrableOn (f n) K)
    (h : L1Cauchy f K) : ∃ F : ℂ → ℂ, IntegrableOn F K ∧ L1Conv f F K :=
  exists_L1Conv hint h

/-- **Connectivity of the index graph.** -/
theorem index_connected {ι : Type*} [Fintype ι] {Y : Type*} [TopologicalSpace Y]
    [ConnectedSpace Y] (U : ι → Set Y) (hU : ∀ i, IsOpen (U i)) (hcov : ∀ y, ∃ i, y ∈ U i)
    (P : ι → Prop) (k₀ : ι) (h₀ : P k₀) (hk₀ : (U k₀).Nonempty)
    (hstep : ∀ k l, P k → (U k ∩ U l).Nonempty → P l) : ∀ k, (U k).Nonempty → P k := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨k₁, hk₁, hP₁⟩ := hcon
  set Y₁ := ⋃ k ∈ {k | P k}, U k
  set Y₂ := ⋃ k ∈ {k | ¬P k}, U k
  have ho₁ : IsOpen Y₁ := isOpen_biUnion fun k _ => hU k
  have ho₂ : IsOpen Y₂ := isOpen_biUnion fun k _ => hU k
  have hcov' : (univ : Set Y) ⊆ Y₁ ∪ Y₂ := by
    intro y _
    obtain ⟨i, hi⟩ := hcov y
    by_cases hPi : P i
    · exact Or.inl (mem_biUnion hPi hi)
    · exact Or.inr (mem_biUnion hPi hi)
  have hn₁ : (univ ∩ Y₁).Nonempty := by
    obtain ⟨y, hy⟩ := hk₀; exact ⟨y, trivial, mem_biUnion h₀ hy⟩
  have hn₂ : (univ ∩ Y₂).Nonempty := by
    obtain ⟨y, hy⟩ := hk₁; exact ⟨y, trivial, mem_biUnion hP₁ hy⟩
  obtain ⟨y, -, hy₁, hy₂⟩ := isPreconnected_univ Y₁ Y₂ ho₁ ho₂ hcov' hn₁ hn₂
  obtain ⟨k, hk, hyk⟩ := mem_iUnion₂.mp hy₁
  obtain ⟨l, hl, hyl⟩ := mem_iUnion₂.mp hy₂
  exact hl (hstep k l hk ⟨y, hyk, hyl⟩)

end JacobianChallenge.Surface
