import Jacobian.Surface.Charts
import Jacobian.HolomorphicForms.Finiteness

/-!
# A finite disc atlas, its measurable pieces, and integration of densities

`DiscAtlas X`: finitely many charts `c_i = chartAt (p i)` with discs `ball (z_i) (r_i)`
covering `X`, `closedBall z_i (3 r_i)` inside the chart target.

The pieces `A i = U i \ ⋃_{j < i} U j` (with `U i = c_i⁻¹(ball z_i r_i)`) partition `X`; their
chart images `S i = c_i(A i)` are measurable. A *density* (a `(1,1)`-family: readings
`σ p : ℂ → ℂ` in every chart with `σ_p = |τ'|² σ_q ∘ τ`) is integrated as
`∫_X σ = ∑ i, ∫_{S i} σ_{p i}`. The localization lemma `integral_density_eq_chart`: if `σ` is
supported in a compact subset of one chart, its integral is the plain integral of its reading
there.
-/

set_option linter.unusedSectionVars false

namespace JacobianChallenge.Surface

open JacobianChallenge.Analysis JacobianChallenge.Periods JacobianChallenge.HolomorphicForms
  MeasureTheory Set Metric Filter Topology Complex
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/-! ### Transition maps -/

/-- The transition map `c_q ∘ c_p⁻¹`. -/
noncomputable abbrev trans (p q : X) : ℂ → ℂ := chartMap id p q

/-- The overlap, in the coordinates of the chart at `p`. -/
def overlap (p q : X) : Set ℂ := (chartAt ℂ p).target ∩ (chartAt ℂ p).symm ⁻¹' (chartAt ℂ q).source

theorem isOpen_overlap (p q : X) : IsOpen (overlap p q) :=
  (chartAt ℂ p).isOpen_inter_preimage_symm (chartAt ℂ q).open_source

theorem trans_differentiableAt {p q : X} {w : ℂ} (hw : w ∈ overlap p q) :
    DifferentiableAt ℂ (trans p q) w :=
  chartMap_differentiableAt contMDiff_id hw.1 hw.2

theorem trans_mem_overlap {p q : X} {w : ℂ} (hw : w ∈ overlap p q) :
    trans p q w ∈ overlap q p := by
  refine ⟨(chartAt ℂ q).map_source hw.2, ?_⟩
  show (chartAt ℂ q).symm (chartAt ℂ q ((chartAt ℂ p).symm w)) ∈ (chartAt ℂ p).source
  rw [(chartAt ℂ q).left_inv hw.2]
  exact (chartAt ℂ p).map_target hw.1

theorem trans_trans {p q : X} {w : ℂ} (hw : w ∈ overlap p q) :
    trans q p (trans p q w) = w := by
  show chartAt ℂ p ((chartAt ℂ q).symm (chartAt ℂ q ((chartAt ℂ p).symm w))) = w
  rw [(chartAt ℂ q).left_inv hw.2, (chartAt ℂ p).right_inv hw.1]

theorem trans_symm_eq {p q : X} {w : ℂ} (hw : w ∈ overlap p q) :
    (chartAt ℂ q).symm (trans p q w) = (chartAt ℂ p).symm w := by
  show (chartAt ℂ q).symm (chartAt ℂ q ((chartAt ℂ p).symm w)) = _
  rw [(chartAt ℂ q).left_inv hw.2]

theorem trans_injOn (p q : X) : InjOn (trans p q) (overlap p q) := by
  intro w₁ h₁ w₂ h₂ h
  have := congrArg (chartAt ℂ q).symm h
  rw [trans_symm_eq h₁, trans_symm_eq h₂] at this
  rw [← (chartAt ℂ p).right_inv h₁.1, ← (chartAt ℂ p).right_inv h₂.1, this]

/-- `τ_{qp}' (τ_{pq} w) · τ_{pq}'(w) = 1`. -/
theorem deriv_trans_mul_deriv_trans {p q : X} {w : ℂ} (hw : w ∈ overlap p q) :
    deriv (trans q p) (trans p q w) * deriv (trans p q) w = 1 := by
  have h1 := trans_differentiableAt hw
  have h2 := trans_differentiableAt (trans_mem_overlap hw)
  have hev : (trans q p ∘ trans p q) =ᶠ[𝓝 w] id := by
    filter_upwards [(isOpen_overlap p q).mem_nhds hw] with v hv using trans_trans hv
  have := (h2.hasDerivAt.comp w h1.hasDerivAt).congr_of_eventuallyEq hev.symm
  rw [← this.deriv]
  exact deriv_id w

theorem deriv_trans_ne_zero {p q : X} {w : ℂ} (hw : w ∈ overlap p q) :
    deriv (trans p q) w ≠ 0 := fun h => by
  have := deriv_trans_mul_deriv_trans hw
  rw [h, mul_zero] at this
  exact zero_ne_one this

/-- Cocycle: `τ_{qr} ∘ τ_{pq} = τ_{pr}` near points of the triple overlap. -/
theorem trans_comp_eventuallyEq {p q r : X} {w : ℂ} (hw : w ∈ overlap p q)
    (_hw' : w ∈ overlap p r) :
    (trans q r ∘ trans p q) =ᶠ[𝓝 w] trans p r := by
  filter_upwards [(isOpen_overlap p q).mem_nhds hw] with v hv
  show chartAt ℂ r ((chartAt ℂ q).symm (chartAt ℂ q ((chartAt ℂ p).symm v))) =
    chartAt ℂ r ((chartAt ℂ p).symm v)
  rw [(chartAt ℂ q).left_inv hv.2]

/-! ### The disc atlas -/

variable (X) in
/-- A finite atlas of chart discs. -/
structure DiscAtlas where
  N : ℕ
  p : Fin N → X
  r : Fin N → ℝ
  r_pos : ∀ i, 0 < r i
  ball_subset : ∀ i, closedBall (chartAt ℂ (p i) (p i)) (3 * r i) ⊆ (chartAt ℂ (p i)).target
  cover : ∀ y : X, ∃ i, y ∈ (chartAt ℂ (p i)).source ∧
    chartAt ℂ (p i) y ∈ ball (chartAt ℂ (p i) (p i)) (r i)

theorem exists_discAtlas [CompactSpace X] : Nonempty (DiscAtlas X) := by
  obtain ⟨t, r, hr, hsub, hcov⟩ := exists_chartDiscCover (X := X)
  refine ⟨⟨t.card, fun i => (t.equivFin.symm i : X), fun i => r (t.equivFin.symm i),
    fun i => hr _, fun i => hsub _, fun y => ?_⟩⟩
  obtain ⟨i, hi, h1, h2⟩ := hcov y
  exact ⟨t.equivFin ⟨i, hi⟩, by simpa using h1, by simpa using h2⟩

namespace DiscAtlas

variable (A : DiscAtlas X)

/-- The chart centre `z_i`. -/
noncomputable abbrev ctr (i : Fin A.N) : ℂ := chartAt ℂ (A.p i) (A.p i)

/-- The open sets `U i = c_i⁻¹(ball z_i r_i)`. -/
def U (i : Fin A.N) : Set X :=
  (chartAt ℂ (A.p i)).source ∩ chartAt ℂ (A.p i) ⁻¹' ball (A.ctr i) (A.r i)

/-- The pieces `A i = U i \ ⋃_{j<i} U j`. -/
def piece (i : Fin A.N) : Set X := A.U i \ ⋃ j ∈ Iio i, A.U j

/-- The chart image `S i = c_i(A i)`. -/
def S (i : Fin A.N) : Set ℂ := chartAt ℂ (A.p i) '' A.piece i

/-- The image of the piece `A i` in the chart `k`. -/
def T (k i : Fin A.N) : Set ℂ := chartAt ℂ (A.p k) '' (A.piece i ∩ (chartAt ℂ (A.p k)).source)

theorem isOpen_U (i : Fin A.N) : IsOpen (A.U i) :=
  (chartAt ℂ (A.p i)).isOpen_inter_preimage isOpen_ball

theorem piece_disjoint {i j : Fin A.N} (h : i ≠ j) : Disjoint (A.piece i) (A.piece j) := by
  rw [Set.disjoint_left]
  intro x hi hj
  rcases lt_or_gt_of_ne h with hlt | hlt
  · exact hj.2 (mem_biUnion hlt hi.1)
  · exact hi.2 (mem_biUnion hlt hj.1)

theorem exists_piece (x : X) : ∃ i, x ∈ A.piece i := by
  classical
  have hex : ∃ i, x ∈ A.U i := by
    obtain ⟨i, h1, h2⟩ := A.cover x
    exact ⟨i, h1, h2⟩
  let i := Finset.min' (Finset.univ.filter fun i => x ∈ A.U i)
    ⟨hex.choose, by simpa using hex.choose_spec⟩
  have hi : x ∈ A.U i := by
    have := Finset.min'_mem (Finset.univ.filter fun i => x ∈ A.U i)
      ⟨hex.choose, by simpa using hex.choose_spec⟩
    simpa using this
  refine ⟨i, hi, ?_⟩
  simp only [mem_iUnion, mem_Iio, not_exists]
  intro j hj hxj
  have := Finset.min'_le (Finset.univ.filter fun i => x ∈ A.U i) j (by simpa using hxj)
  exact absurd hj (not_lt.mpr this)

theorem S_subset_ball (i : Fin A.N) : A.S i ⊆ ball (A.ctr i) (A.r i) := by
  rintro _ ⟨x, hx, rfl⟩
  exact hx.1.2

theorem ball_subset_target (i : Fin A.N) {s : ℝ} (hs : s ≤ 3) :
    closedBall (A.ctr i) (s * A.r i) ⊆ (chartAt ℂ (A.p i)).target :=
  (closedBall_subset_closedBall (mul_le_mul_of_nonneg_right hs (A.r_pos i).le)).trans
    (A.ball_subset i)

/-- The chart image of a piece, as a subset of the chart target. -/
theorem T_eq (k i : Fin A.N) :
    A.T k i = (chartAt ℂ (A.p k)).target ∩ (chartAt ℂ (A.p k)).symm ⁻¹' A.piece i := by
  ext v
  constructor
  · rintro ⟨x, ⟨hx, hxs⟩, rfl⟩
    exact ⟨(chartAt ℂ (A.p k)).map_source hxs, by
      rw [mem_preimage, (chartAt ℂ (A.p k)).left_inv hxs]; exact hx⟩
  · rintro ⟨hv, hvA⟩
    exact ⟨_, ⟨hvA, (chartAt ℂ (A.p k)).map_target hv⟩, (chartAt ℂ (A.p k)).right_inv hv⟩

theorem S_eq_T (i : Fin A.N) : A.S i = A.T i i := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, ⟨hx, hx.1.1⟩, rfl⟩
  · rintro ⟨x, ⟨hx, -⟩, rfl⟩
    exact ⟨x, hx, rfl⟩

/-- Preimages of open sets of `X` in a chart target are open. -/
theorem isOpen_target_inter_preimage (k : Fin A.N) {V : Set X} (hV : IsOpen V) :
    IsOpen ((chartAt ℂ (A.p k)).target ∩ (chartAt ℂ (A.p k)).symm ⁻¹' V) :=
  (chartAt ℂ (A.p k)).isOpen_inter_preimage_symm hV

theorem measurableSet_T (k i : Fin A.N) : MeasurableSet (A.T k i) := by
  rw [A.T_eq]
  have e : (chartAt ℂ (A.p k)).target ∩ (chartAt ℂ (A.p k)).symm ⁻¹' A.piece i =
      ((chartAt ℂ (A.p k)).target ∩ (chartAt ℂ (A.p k)).symm ⁻¹' A.U i) \
        ⋃ j ∈ Iio i, ((chartAt ℂ (A.p k)).target ∩ (chartAt ℂ (A.p k)).symm ⁻¹' A.U j) := by
    ext v
    simp only [piece, mem_inter_iff, mem_preimage, mem_diff, mem_iUnion, mem_Iio, not_exists,
      not_and]
    constructor
    · rintro ⟨hv, hU, hn⟩
      exact ⟨⟨hv, hU⟩, fun j hj _ => hn j hj⟩
    · rintro ⟨⟨hv, hU⟩, hn⟩
      exact ⟨hv, hU, fun j hj h => hn j hj hv h⟩
  rw [e]
  exact (A.isOpen_target_inter_preimage k (A.isOpen_U i)).measurableSet.diff
    (MeasurableSet.biUnion (to_countable _) fun j _ =>
      (A.isOpen_target_inter_preimage k (A.isOpen_U j)).measurableSet)

theorem measurableSet_S (i : Fin A.N) : MeasurableSet (A.S i) := by
  rw [A.S_eq_T]; exact A.measurableSet_T i i

theorem T_disjoint (k : Fin A.N) {i j : Fin A.N} (h : i ≠ j) : Disjoint (A.T k i) (A.T k j) := by
  rw [A.T_eq, A.T_eq]
  exact (Disjoint.inter_right' _ ((A.piece_disjoint h).preimage _)).inter_left' _

theorem iUnion_T (k : Fin A.N) : ⋃ i, A.T k i = (chartAt ℂ (A.p k)).target := by
  ext v
  rw [mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩; rw [A.T_eq] at hi; exact hi.1
  · intro hv
    obtain ⟨i, hi⟩ := A.exists_piece ((chartAt ℂ (A.p k)).symm v)
    exact ⟨i, by rw [A.T_eq]; exact ⟨hv, hi⟩⟩

/-- `τ_{ki}` maps the chart-`k` image of the piece `i` onto `S i ∩ overlap`. -/
theorem T_subset_overlap (k i : Fin A.N) : A.T k i ⊆ overlap (A.p k) (A.p i) := by
  rw [A.T_eq]
  rintro v ⟨hv, hvA⟩
  exact ⟨hv, hvA.1.1⟩

theorem image_trans_T (k i : Fin A.N) :
    trans (A.p k) (A.p i) '' A.T k i = A.S i ∩ overlap (A.p i) (A.p k) := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hvo := A.T_subset_overlap k i hv
    rw [A.T_eq] at hv
    refine ⟨⟨(chartAt ℂ (A.p k)).symm v, hv.2, rfl⟩, trans_mem_overlap hvo⟩
  · rintro ⟨⟨x, hx, rfl⟩, hw⟩
    have hxk : x ∈ (chartAt ℂ (A.p k)).source := by
      have := hw.2
      rw [mem_preimage, (chartAt ℂ (A.p i)).left_inv hx.1.1] at this
      exact this
    refine ⟨chartAt ℂ (A.p k) x, ⟨x, ⟨hx, hxk⟩, rfl⟩, ?_⟩
    show chartAt ℂ (A.p i) ((chartAt ℂ (A.p k)).symm (chartAt ℂ (A.p k) x)) = _
    rw [(chartAt ℂ (A.p k)).left_inv hxk]

/-! ### Densities and their integrals -/

/-- `σ` is a density (a `(1,1)`-family): `σ_p = |τ_{pq}'|² σ_q ∘ τ_{pq}` on overlaps. -/
def IsDensity (σ : X → ℂ → ℂ) : Prop :=
  ∀ p q : X, ∀ w ∈ overlap p q, σ p w = (‖deriv (trans p q) w‖ ^ 2 : ℝ) * σ q (trans p q w)

/-- The integral of a density over `X`. -/
noncomputable def integral (σ : X → ℂ → ℂ) : ℂ := ∑ i, ∫ w in A.S i, σ (A.p i) w

/-- The integral of a density over the piece `i`, computed in another chart `k`. -/
theorem integral_S_eq_T {σ : X → ℂ → ℂ} (hσ : IsDensity σ) (k i : Fin A.N)
    (h0 : ∀ w ∈ A.S i, w ∉ overlap (A.p i) (A.p k) → σ (A.p i) w = 0) :
    ∫ w in A.S i, σ (A.p i) w = ∫ v in A.T k i, σ (A.p k) v := by
  have h1 : ∫ w in A.S i, σ (A.p i) w = ∫ w in A.S i ∩ overlap (A.p i) (A.p k), σ (A.p i) w := by
    refine setIntegral_eq_of_subset_of_forall_diff_eq_zero (A.measurableSet_S i)
      inter_subset_left fun w hw => h0 w hw.1 fun ho => hw.2 ⟨hw.1, ho⟩
  rw [h1, ← A.image_trans_T k i, integral_image_holo (A.measurableSet_T k i)
    (fun v hv => trans_differentiableAt (A.T_subset_overlap k i hv))
    ((trans_injOn _ _).mono (A.T_subset_overlap k i))]
  refine setIntegral_congr_fun (A.measurableSet_T k i) fun v hv => ?_
  rw [hσ (A.p k) (A.p i) v (A.T_subset_overlap k i hv)]
  push_cast; ring

/-- **Localization.** A density supported (in the sense of `h0`) inside the chart `k` and
integrable there has integral equal to the plane integral of its reading in that chart. -/
theorem integral_density_eq_chart {σ : X → ℂ → ℂ} (hσ : IsDensity σ) (k : Fin A.N)
    (h0 : ∀ q : X, ∀ w ∈ (chartAt ℂ q).target, (chartAt ℂ q).symm w ∉ (chartAt ℂ (A.p k)).source →
      σ q w = 0)
    (hint : IntegrableOn (σ (A.p k)) (chartAt ℂ (A.p k)).target) :
    A.integral σ = ∫ v in (chartAt ℂ (A.p k)).target, σ (A.p k) v := by
  unfold integral
  have : ∀ i, ∫ w in A.S i, σ (A.p i) w = ∫ v in A.T k i, σ (A.p k) v := fun i =>
    A.integral_S_eq_T hσ k i fun w hw ho => by
      have hwt : w ∈ (chartAt ℂ (A.p i)).target :=
        A.ball_subset i (closedBall_subset_closedBall (by linarith [A.r_pos i])
          (ball_subset_closedBall (A.S_subset_ball i hw)))
      exact h0 _ w hwt fun h => ho ⟨hwt, h⟩
  simp_rw [this]
  rw [← integral_iUnion_fintype (A.measurableSet_T k) (fun i j hij => A.T_disjoint k hij)
    (fun i => hint.mono_set (by rw [← A.iUnion_T k]; exact subset_iUnion _ i)), A.iUnion_T k]

end DiscAtlas

end JacobianChallenge.Surface
