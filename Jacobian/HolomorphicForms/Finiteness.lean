import Jacobian.Periods.ChainPushforward
import Jacobian.HolomorphicForms.FiniteDimensional
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# Holomorphic 1-forms on a compact Riemann surface are finite-dimensional

The classical Montel–Riesz argument (Forster, *Lectures on Riemann Surfaces*, §14).

Cover `X` by finitely many chart discs `K_i = closedBall(z_i, r_i)` (in the chart at `p_i`)
whose interiors cover `X`, with `L_i = closedBall(z_i, 2 r_i)` still inside the chart target.
Read a form `ω` in the chart at `p_i` as the holomorphic coefficient
`a_i(ω)(z) = chartForm p_i ω z 1` and set

* `‖ω‖_K = max_i sup_{K_i} |a_i(ω)|`, `‖ω‖_L = max_i sup_{L_i} |a_i(ω)|`.

Then:

1. `ω ↦ (a_i(ω)|_{K_i})_i` is injective (the interiors of the `K_i` cover `X`);
2. `‖ω‖_L ≤ C ‖ω‖_K` (on `L_i ∩ K_j` the two readings differ by the derivative of the
   chart transition, bounded on a compact set);
3. on `{‖ω‖_L ≤ 1}` the restrictions `a_i(ω)|_{K_i}` are uniformly bounded and uniformly
   Lipschitz (Cauchy estimates), so their set is totally bounded (Arzelà–Ascoli);
4. hence a ball of positive radius in the image of `ω ↦ (a_i(ω)|_{K_i})_i` is totally
   bounded, and the image (so the space of forms) is finite-dimensional (Riesz).
-/

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace JacobianChallenge.HolomorphicForms

open JacobianChallenge.Periods Set Metric Filter
open scoped Manifold Topology NNReal BoundedContinuousFunction

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/-- The coefficient of `ω` in the chart at `p`: `ω = a(z) dz`. -/
noncomputable def chartCoeff (p : X) (ω : HolomorphicOneForm ℂ X) (z : ℂ) : ℂ :=
  chartForm p ω z 1

theorem chartCoeff_add (p : X) (ω₁ ω₂ : HolomorphicOneForm ℂ X) (z : ℂ) :
    chartCoeff p (ω₁ + ω₂) z = chartCoeff p ω₁ z + chartCoeff p ω₂ z := by
  simp [chartCoeff]

theorem chartCoeff_smul (p : X) (c : ℂ) (ω : HolomorphicOneForm ℂ X) (z : ℂ) :
    chartCoeff p (c • ω) z = c * chartCoeff p ω z := by
  simp [chartCoeff]

theorem chartCoeff_differentiableOn (p : X) (ω : HolomorphicOneForm ℂ X) :
    DifferentiableOn ℂ (chartCoeff p ω) (chartAt ℂ p).target :=
  ((chartForm_contDiffOn p ω).differentiableOn (by simp)).clm_apply
    (differentiableOn_const _)

/-- A `ℂ`-linear map `ℂ → ℂ` is multiplication by its value at `1`. -/
theorem clm_apply_eq_mul' (L : ℂ →L[ℂ] ℂ) (v : ℂ) : L v = v * L 1 := by
  have h := L.map_smul v (1 : ℂ)
  simpa [smul_eq_mul] using h

/-- **Chart transition.** The readings of `ω` in two charts differ by the derivative of the
transition map `τ = c_q ∘ c_p⁻¹`. -/
theorem chartForm_transition (ω : HolomorphicOneForm ℂ X) {p q : X} {w : ℂ}
    (hw : w ∈ (chartAt ℂ p).target) (hq : (chartAt ℂ p).symm w ∈ (chartAt ℂ q).source) :
    chartForm p ω w =
      (chartForm q ω (chartMap id p q w)).comp (fderiv ℂ (chartMap id p q) w) := by
  have hid : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) (id : X → X) := contMDiff_id
  rw [chartMap_fderiv hid hw hq]
  set x := (chartAt ℂ p).symm w
  have hround : (chartAt ℂ q).symm (chartMap id p q w) = x := (chartAt ℂ q).left_inv hq
  show (ω.toFun x).comp (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (chartAt ℂ p).symm w) =
    ((ω.toFun ((chartAt ℂ q).symm (chartMap id p q w))).comp
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (chartAt ℂ q).symm (chartMap id p q w))).comp _
  have hpt : chartMap id p q w = (chartAt ℂ q) x := rfl
  rw [hround, hpt, mfderiv_id]
  have h := mfderiv_chartAt_symm_comp_self q hq
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [ContinuousLinearMap.comp_apply]
  congr 1
  exact (congrArg (fun L => L ((mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (chartAt ℂ p).symm w) v)) h).symm

theorem chartCoeff_transition (ω : HolomorphicOneForm ℂ X) {p q : X} {w : ℂ}
    (hw : w ∈ (chartAt ℂ p).target) (hq : (chartAt ℂ p).symm w ∈ (chartAt ℂ q).source) :
    chartCoeff p ω w = deriv (chartMap id p q) w * chartCoeff q ω (chartMap id p q w) := by
  unfold chartCoeff
  rw [chartForm_transition ω hw hq, ContinuousLinearMap.comp_apply,
    fderiv_apply_one_eq_deriv, clm_apply_eq_mul' _ (deriv _ w)]

/-- A form whose coefficient vanishes at every point, in some chart around it, is zero. -/
theorem holomorphicOneForm_eq_zero_of_chartCoeff (ω : HolomorphicOneForm ℂ X)
    (h : ∀ x : X, ∃ p : X, x ∈ (chartAt ℂ p).source ∧ chartCoeff p ω (chartAt ℂ p x) = 0) :
    ω = 0 := by
  apply ContMDiffSection.ext
  intro x
  obtain ⟨p, hx, h0⟩ := h x
  set c := chartAt ℂ p
  have hzero : chartForm p ω (c x) = 0 := by
    refine ContinuousLinearMap.ext fun v => ?_
    rw [clm_apply_eq_mul', show chartForm p ω (c x) 1 = 0 from h0, mul_zero]
    rfl
  have key : ∀ y : X, y = x →
      (ω.toFun y).comp (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) c.symm (c x)) =
        (ω.toFun x).comp (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) c.symm (c x)) := by
    rintro y rfl; rfl
  have h1 : (ω.toFun x).comp (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) c.symm (c x)) = 0 := by
    rw [← key _ (c.left_inv hx)]; exact hzero
  have hid := mfderiv_chartAt_symm_comp_self p hx
  show ω.toFun x = (0 : HolomorphicOneForm ℂ X).toFun x
  refine ContinuousLinearMap.ext fun v => ?_
  have hv : (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) c.symm (c x)) ((mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) c x) v) = v :=
    congrArg (fun L => L v) hid
  calc (ω.toFun x) v
      = (ω.toFun x) ((mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) c.symm (c x))
          ((mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) c x) v)) := by rw [hv]
    _ = ((ω.toFun x).comp (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) c.symm (c x)))
          ((mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) c x) v) := rfl
    _ = 0 := by rw [h1]; rfl

/-! ### The finite chart-disc cover -/

section Cover

variable [T2Space X] [CompactSpace X]

instance closedBall_compactSpace (z : ℂ) (ρ : ℝ) : CompactSpace (closedBall z ρ) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall z ρ)

omit [T2Space X] in
/-- Finitely many chart discs: `closedBall (c_p p) (3 r_p)` inside the chart target, and the
open discs `ball (c_p p) (r_p)` covering `X`. -/
theorem exists_chartDiscCover :
    ∃ (t : Finset X) (r : X → ℝ), (∀ x, 0 < r x) ∧
      (∀ x, closedBall (chartAt ℂ x x) (3 * r x) ⊆ (chartAt ℂ x).target) ∧
      ∀ y : X, ∃ i ∈ t, y ∈ (chartAt ℂ i).source ∧
        chartAt ℂ i y ∈ ball (chartAt ℂ i i) (r i) := by
  have hball : ∀ x : X, ∃ ρ > 0, ball (chartAt ℂ x x) ρ ⊆ (chartAt ℂ x).target := fun x =>
    Metric.isOpen_iff.mp (chartAt ℂ x).open_target _
      ((chartAt ℂ x).map_source (mem_chart_source ℂ x))
  choose ρ hρ hρsub using hball
  set r : X → ℝ := fun x => ρ x / 4
  have hr : ∀ x, 0 < r x := fun x => div_pos (hρ x) (by norm_num)
  let U : X → Set X := fun x =>
    (chartAt ℂ x).source ∩ (chartAt ℂ x) ⁻¹' ball (chartAt ℂ x x) (r x)
  have hU : ∀ x, IsOpen (U x) := fun x => (chartAt ℂ x).isOpen_inter_preimage isOpen_ball
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hU
    (fun x _ => mem_iUnion.mpr ⟨x, mem_chart_source ℂ x, mem_ball_self (hr x)⟩)
  refine ⟨t, r, hr, fun x => ?_, fun y => ?_⟩
  · refine (closedBall_subset_ball ?_).trans (hρsub x)
    have := hρ x
    simp only [r]; linarith
  · obtain ⟨i, hi, hyU⟩ := mem_iUnion₂.mp (ht (mem_univ y))
    exact ⟨i, hi, hyU.1, hyU.2⟩

variable (t : Finset X) (r : X → ℝ) (hr : ∀ x, 0 < r x)
  (hsub : ∀ x, closedBall (chartAt ℂ x x) (3 * r x) ⊆ (chartAt ℂ x).target)

/-- The disc of radius `s · r_i` around the centre of the chart at `i`. -/
abbrev disc (s : ℝ) (i : t) : Set ℂ := closedBall (chartAt ℂ (i : X) i) (s * r i)

include hr hsub in
theorem disc_subset_target {s : ℝ} (hs : s ≤ 3) (i : t) :
    disc t r s i ⊆ (chartAt ℂ (i : X)).target :=
  (closedBall_subset_closedBall (mul_le_mul_of_nonneg_right hs (hr i).le)).trans (hsub i)

/-- The coefficients of a form on the discs of radius `s · r_i`, as a vector of bounded
continuous functions. -/
noncomputable def discCoeffs {s : ℝ} (hs : s ≤ 3) :
    HolomorphicOneForm ℂ X →ₗ[ℂ] ((i : t) → (disc t r s i →ᵇ ℂ)) where
  toFun ω i := BoundedContinuousFunction.mkOfCompact
    ⟨fun w => chartCoeff (i : X) ω w,
      ((chartCoeff_differentiableOn (i : X) ω).continuousOn.mono
        (disc_subset_target t r hr hsub hs i)).comp_continuous continuous_subtype_val
        (fun w => w.2)⟩
  map_add' ω₁ ω₂ := by
    funext i; ext w
    simp [chartCoeff_add]
  map_smul' c ω := by
    funext i; ext w
    simp [chartCoeff_smul]

theorem discCoeffs_apply {s : ℝ} (hs : s ≤ 3) (ω : HolomorphicOneForm ℂ X) (i : t)
    (w : disc t r s i) :
    discCoeffs t r hr hsub hs ω i w = chartCoeff (i : X) ω w := rfl

theorem norm_chartCoeff_le {s : ℝ} (hs : s ≤ 3) (ω : HolomorphicOneForm ℂ X) (i : t)
    {w : ℂ} (hw : w ∈ disc t r s i) :
    ‖chartCoeff (i : X) ω w‖ ≤ ‖discCoeffs t r hr hsub hs ω‖ := by
  have h1 := BoundedContinuousFunction.norm_coe_le_norm (discCoeffs t r hr hsub hs ω i) ⟨w, hw⟩
  rw [discCoeffs_apply] at h1
  exact h1.trans (norm_le_pi_norm (discCoeffs t r hr hsub hs ω) i)

theorem norm_discCoeffs_le {s : ℝ} (hs : s ≤ 3) (ω : HolomorphicOneForm ℂ X) {M : ℝ}
    (hM : 0 ≤ M) (h : ∀ i : t, ∀ w ∈ disc t r s i, ‖chartCoeff (i : X) ω w‖ ≤ M) :
    ‖discCoeffs t r hr hsub hs ω‖ ≤ M := by
  refine (pi_norm_le_iff_of_nonneg hM).mpr fun i => ?_
  refine (BoundedContinuousFunction.norm_le hM).mpr fun w => ?_
  rw [discCoeffs_apply]
  exact h i w w.2

variable (hcov : ∀ y : X, ∃ i ∈ t, y ∈ (chartAt ℂ i).source ∧
  chartAt ℂ i y ∈ ball (chartAt ℂ i i) (r i))

include hcov in
theorem discCoeffs_injective : Function.Injective (discCoeffs t r hr hsub (s := 1) (by norm_num)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro ω hω
  refine holomorphicOneForm_eq_zero_of_chartCoeff ω fun y => ?_
  obtain ⟨i, hi, hys, hyb⟩ := hcov y
  refine ⟨i, hys, ?_⟩
  have hw : chartAt ℂ i y ∈ disc t r 1 ⟨i, hi⟩ := by
    show chartAt ℂ i y ∈ closedBall _ (1 * r i)
    rw [one_mul]; exact ball_subset_closedBall hyb
  have := congrArg (fun v => v ⟨i, hi⟩ ⟨_, hw⟩) hω
  simpa [discCoeffs_apply] using this

include hcov in
/-- **Transition bound**: the coefficients on the larger discs are controlled by those on the
smaller discs. -/
theorem exists_discCoeffs_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ω : HolomorphicOneForm ℂ X,
      ‖discCoeffs t r hr hsub (s := 2) (by norm_num) ω‖ ≤
        C * ‖discCoeffs t r hr hsub (s := 1) (by norm_num) ω‖ := by
  classical
  have hbound : ∀ i j : t, ∃ B : ℝ, ∀ x ∈ ((chartAt ℂ (i : X)).symm '' disc t r 2 i) ∩
      ((chartAt ℂ (j : X)).symm '' disc t r 1 j),
      ‖deriv (chartMap id (i : X) (j : X)) (chartAt ℂ (i : X) x)‖ ≤ B := by
    intro i j
    set ci := chartAt ℂ (i : X)
    set cj := chartAt ℂ (j : X)
    have h2 := disc_subset_target t r hr hsub (s := 2) (by norm_num) i
    have h1 := disc_subset_target t r hr hsub (s := 1) (by norm_num) j
    have hA : IsCompact ((ci.symm '' disc t r 2 i) ∩ (cj.symm '' disc t r 1 j)) :=
      ((isCompact_closedBall _ _).image_of_continuousOn (ci.continuousOn_symm.mono h2)).inter
        ((isCompact_closedBall _ _).image_of_continuousOn (cj.continuousOn_symm.mono h1))
    set O := ci.target ∩ ci.symm ⁻¹' cj.source
    have hO : IsOpen O := ci.isOpen_inter_preimage_symm cj.open_source
    have hdiff : DifferentiableOn ℂ (chartMap id (i : X) (j : X)) O := fun w hw =>
      (chartMap_differentiableAt (contMDiff_id) hw.1 hw.2).differentiableWithinAt
    have hcont : ContinuousOn (deriv (chartMap id (i : X) (j : X))) O :=
      (hdiff.analyticOnNhd hO).deriv.continuousOn
    have hmaps : ∀ x ∈ (ci.symm '' disc t r 2 i) ∩ (cj.symm '' disc t r 1 j),
        x ∈ ci.source ∧ ci x ∈ O := by
      rintro x ⟨⟨w, hw, rfl⟩, ⟨w', hw', hx'⟩⟩
      have hws : ci.symm w ∈ ci.source := ci.map_target (h2 hw)
      refine ⟨hws, ci.map_source hws, ?_⟩
      show ci.symm (ci (ci.symm w)) ∈ cj.source
      rw [ci.left_inv hws, ← hx']
      exact cj.map_target (h1 hw')
    have hcomp : ContinuousOn (fun x => deriv (chartMap id (i : X) (j : X)) (ci x))
        ((ci.symm '' disc t r 2 i) ∩ (cj.symm '' disc t r 1 j)) :=
      hcont.comp (ci.continuousOn.mono fun x hx => (hmaps x hx).1) fun x hx => (hmaps x hx).2
    exact hA.exists_bound_of_continuousOn hcomp
  choose B hB using hbound
  set C : ℝ := ∑ i : t, ∑ j : t, max (B i j) 0
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => le_max_right _ _
  have hle : ∀ i j, B i j ≤ C := fun i j =>
    calc B i j ≤ max (B i j) 0 := le_max_left _ _
      _ ≤ ∑ j' : t, max (B i j') 0 :=
          Finset.single_le_sum (f := fun j' => max (B i j') 0) (fun j' _ => le_max_right _ _)
            (Finset.mem_univ j)
      _ ≤ C := Finset.single_le_sum (f := fun i' => ∑ j' : t, max (B i' j') 0)
            (fun i' _ => Finset.sum_nonneg fun j' _ => le_max_right _ _) (Finset.mem_univ i)
  refine ⟨C, hC0, fun ω => ?_⟩
  refine norm_discCoeffs_le t r hr hsub _ ω (mul_nonneg hC0 (norm_nonneg _)) fun i w hw => ?_
  set ci := chartAt ℂ (i : X)
  have hwt : w ∈ ci.target := disc_subset_target t r hr hsub (s := 2) (by norm_num) i hw
  set x := ci.symm w
  obtain ⟨j, hj, hxs, hxb⟩ := hcov x
  set cj := chartAt ℂ j
  have hK1 : cj x ∈ disc t r 1 ⟨j, hj⟩ := by
    show cj x ∈ closedBall _ (1 * r j)
    rw [one_mul]; exact ball_subset_closedBall hxb
  rw [chartCoeff_transition ω hwt hxs]
  have hτ : chartMap id (i : X) j w = cj x := rfl
  rw [hτ, norm_mul]
  have hxA : x ∈ (ci.symm '' disc t r 2 i) ∩ (cj.symm '' disc t r 1 ⟨j, hj⟩) :=
    ⟨⟨w, hw, rfl⟩, ⟨cj x, hK1, cj.left_inv hxs⟩⟩
  have hd := hB i ⟨j, hj⟩ x hxA
  have hcx : ci x = w := ci.right_inv hwt
  rw [hcx] at hd
  exact mul_le_mul (hd.trans (hle _ _))
    (norm_chartCoeff_le t r hr hsub (s := 1) (by norm_num) ω ⟨j, hj⟩ hK1)
    (norm_nonneg _) hC0

include hr hsub in
/-- **Cauchy estimate**: on the small discs, the coefficients of a form bounded by `1` on the
large discs are `1 / r_i`-Lipschitz. -/
theorem chartCoeff_lipschitz (ω : HolomorphicOneForm ℂ X)
    (hω : ‖discCoeffs t r hr hsub (s := 2) (by norm_num) ω‖ ≤ 1) (i : t) {a b : ℂ}
    (ha : a ∈ disc t r 1 i) (hb : b ∈ disc t r 1 i) :
    ‖chartCoeff (i : X) ω a - chartCoeff (i : X) ω b‖ ≤ 1 / r i * ‖a - b‖ := by
  set f := chartCoeff (i : X) ω
  have hri := hr i
  have h12 : ∀ w ∈ disc t r 1 i, closedBall w (r i) ⊆ disc t r 2 i := by
    intro w hw z hz
    rw [mem_closedBall] at hz hw ⊢
    calc dist z (chartAt ℂ (i : X) i) ≤ dist z w + dist w (chartAt ℂ (i : X) i) :=
          dist_triangle _ _ _
      _ ≤ r i + 1 * r i := add_le_add hz hw
      _ = 2 * r i := by ring
  have h2t := disc_subset_target t r hr hsub (s := 2) (by norm_num) i
  have hdiff := chartCoeff_differentiableOn (i : X) ω
  have hD : ∀ w ∈ disc t r 1 i, DifferentiableAt ℂ f w := fun w hw =>
    hdiff.differentiableAt ((chartAt ℂ (i : X)).open_target.mem_nhds
      (h2t (h12 w hw (mem_closedBall_self hri.le))))
  have hbound : ∀ w ∈ disc t r 1 i, ‖deriv f w‖ ≤ 1 / r i := by
    intro w hw
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hri ?_ fun z hz => ?_
    · refine DifferentiableOn.diffContOnCl ?_
      rw [closure_ball w hri.ne']
      exact hdiff.mono ((h12 w hw).trans h2t)
    · exact (norm_chartCoeff_le t r hr hsub (s := 2) (by norm_num) ω i
        (h12 w hw (sphere_subset_closedBall hz))).trans hω
  exact (convex_closedBall _ _).norm_image_sub_le_of_norm_deriv_le hD hbound hb ha

end Cover

/-- **Finiteness theorem.** On a compact Riemann surface the holomorphic 1-forms form a
finite-dimensional space (Montel + Riesz). -/
theorem finiteDimensional_holomorphicOneForm [T2Space X] [CompactSpace X] :
    FiniteDimensional ℂ (HolomorphicOneForm ℂ X) := by
  obtain ⟨t, r, hr, hsub, hcov⟩ := exists_chartDiscCover (X := X)
  set Φ1 := discCoeffs t r hr hsub (s := 1) (by norm_num)
  set Φ2 := discCoeffs t r hr hsub (s := 2) (by norm_num)
  obtain ⟨C, hC0, hC⟩ := exists_discCoeffs_bound t r hr hsub hcov
  let A : (i : t) → Set (disc t r 1 i →ᵇ ℂ) := fun i => {g | ∃ ω, ‖Φ2 ω‖ ≤ 1 ∧ Φ1 ω i = g}
  have hA : ∀ i, IsCompact (closure (A i)) := by
    intro i
    have h12 : disc t r 1 i ⊆ disc t r 2 i :=
      closedBall_subset_closedBall (mul_le_mul_of_nonneg_right (by norm_num) (hr i).le)
    refine BoundedContinuousFunction.arzela_ascoli (closedBall (0 : ℂ) 1)
      (isCompact_closedBall _ _) (A i) ?_ ?_
    · rintro g w ⟨ω, hω, rfl⟩
      rw [mem_closedBall_zero_iff]
      exact (norm_chartCoeff_le t r hr hsub (s := 2) (by norm_num) ω i (h12 w.2)).trans hω
    · have hlip : ∀ g : A i, LipschitzWith (Real.toNNReal (1 / r i)) (g : disc t r 1 i → ℂ) := by
        rintro ⟨g, ω, hω, rfl⟩
        refine LipschitzWith.of_dist_le_mul fun a b => ?_
        rw [dist_eq_norm, Subtype.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (by have := hr i; positivity)]
        exact chartCoeff_lipschitz t r hr hsub ω hω i a.2 b.2
      exact (LipschitzWith.uniformEquicontinuous _ _ hlip).equicontinuous
  set T := Φ1 '' {ω | ‖Φ2 ω‖ ≤ 1}
  have hT : TotallyBounded T := by
    refine ((isCompact_univ_pi hA).totallyBounded).subset ?_
    rintro _ ⟨ω, hω, rfl⟩
    exact fun i _ => subset_closure ⟨ω, hω, rfl⟩
  set V := LinearMap.range Φ1
  set δ : ℝ := 1 / (C + 1)
  have hδ : 0 < δ := by positivity
  have hball : closedBall (0 : V) δ ⊆ (Subtype.val : V → _) ⁻¹' T := by
    rintro ⟨v, ω, rfl⟩ hv
    rw [mem_closedBall_zero_iff] at hv
    refine ⟨ω, ?_, rfl⟩
    show ‖Φ2 ω‖ ≤ 1
    have hv' : ‖Φ1 ω‖ ≤ δ := hv
    calc ‖Φ2 ω‖ ≤ C * ‖Φ1 ω‖ := hC ω
      _ ≤ C * δ := mul_le_mul_of_nonneg_left hv' hC0
      _ ≤ 1 := by
        simp only [δ]
        rw [mul_one_div, div_le_one (by positivity)]
        linarith
  have htb : TotallyBounded (closedBall (0 : V) δ) :=
    (totallyBounded_preimage isUniformEmbedding_subtype_val.isUniformInducing hT).subset hball
  haveI : FiniteDimensional ℂ V :=
    FiniteDimensional.of_totallyBounded_nhds_zero ℂ (closedBall_mem_nhds 0 hδ) htb
  refine FiniteDimensional.of_injective Φ1.rangeRestrict fun a b h => ?_
  exact discCoeffs_injective t r hr hsub hcov (congrArg Subtype.val h)

instance [T2Space X] [CompactSpace X] : FiniteDimensionalHolomorphicOneForms ℂ X :=
  ⟨finiteDimensional_holomorphicOneForm⟩

end JacobianChallenge.HolomorphicForms
