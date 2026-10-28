import Jacobian.Periods.ChartChain
import Jacobian.HolomorphicForms.PullbackBundled

/-!
# Pushing chart chains forward along a holomorphic map

For a holomorphic map `f : X → Y` of Riemann surfaces and a chart chain `l` in `X` from
`P` to `Q`, there is a chart chain `l'` in `Y` from `f P` to `f Q` with

  `∫_{l'} η = ∫_l f^*η`   for every holomorphic 1-form `η` on `Y`

(`exists_pushforward_chain`). This is the change-of-variables formula
`∫_{f∘γ} η = ∫_γ f^*η`, proved chartwise:

* `chartForm_pullback` — in charts, `f^*η` reads as `(η ∘ φ) · φ'` with `φ` the chart
  expression of `f` (chain rule for `mfderiv`);
* `segment_integral_pullback` — on a ball where `φ` lands in a ball of a `Y`-chart, the
  segment integral of `f^*η` equals the integral of `η` over the segment between the image
  endpoints (both are differences of primitives, and two primitives on a ball differ by a
  constant);
* a Lebesgue-number subdivision of each segment makes every piece small enough.
-/

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms Set Metric Filter
open scoped Manifold Topology

universe u v

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y]
  {f : X → Y} (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)

/-- The expression of `f` in the charts at `p ∈ X` and `q ∈ Y`. -/
noncomputable def chartMap (f : X → Y) (p : X) (q : Y) : ℂ → ℂ :=
  chartAt ℂ q ∘ f ∘ (chartAt ℂ p).symm

include hf in
theorem chartMap_differentiableAt {p : X} {q : Y} {w : ℂ} (hw : w ∈ (chartAt ℂ p).target)
    (hfw : f ((chartAt ℂ p).symm w) ∈ (chartAt ℂ q).source) :
    DifferentiableAt ℂ (chartMap f p q) w := by
  have h1 : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (chartAt ℂ q) (f ((chartAt ℂ p).symm w)) :=
    mdifferentiableAt_atlas (chart_mem_atlas ℂ q) hfw
  have h2 : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f ((chartAt ℂ p).symm w) :=
    hf.mdifferentiableAt (by simp)
  have h3 : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (chartAt ℂ p).symm w :=
    mdifferentiableAt_atlas_symm (chart_mem_atlas ℂ p) hw
  exact mdifferentiableAt_iff_differentiableAt.mp (h1.comp w (h2.comp w h3))

include hf in
theorem chartMap_fderiv {p : X} {q : Y} {w : ℂ} (hw : w ∈ (chartAt ℂ p).target)
    (hfw : f ((chartAt ℂ p).symm w) ∈ (chartAt ℂ q).source) :
    fderiv ℂ (chartMap f p q) w =
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (chartAt ℂ q) (f ((chartAt ℂ p).symm w))).comp
        ((mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f ((chartAt ℂ p).symm w)).comp
          (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (chartAt ℂ p).symm w)) := by
  have h1 : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (chartAt ℂ q) (f ((chartAt ℂ p).symm w)) :=
    mdifferentiableAt_atlas (chart_mem_atlas ℂ q) hfw
  have h2 : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f ((chartAt ℂ p).symm w) :=
    hf.mdifferentiableAt (by simp)
  have h3 : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (chartAt ℂ p).symm w :=
    mdifferentiableAt_atlas_symm (chart_mem_atlas ℂ p) hw
  rw [← mfderiv_eq_fderiv]
  unfold chartMap
  rw [mfderiv_comp w h1 (h2.comp w h3), mfderiv_comp w h2 h3]
  rfl

/-- `mfderiv c⁻¹ ∘ mfderiv c = id` at a point of the chart source. -/
theorem mfderiv_chartAt_symm_comp_self (q : Y) {y : Y} (hy : y ∈ (chartAt ℂ q).source) :
    (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (chartAt ℂ q).symm ((chartAt ℂ q) y)).comp
        (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (chartAt ℂ q) y) =
      ContinuousLinearMap.id ℂ (TangentSpace 𝓘(ℂ, ℂ) y) := by
  have h1 : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (chartAt ℂ q).symm ((chartAt ℂ q) y) :=
    mdifferentiableAt_atlas_symm (chart_mem_atlas ℂ q) ((chartAt ℂ q).map_source hy)
  have h2 : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (chartAt ℂ q) y :=
    mdifferentiableAt_atlas (chart_mem_atlas ℂ q) hy
  rw [← mfderiv_comp y h1 h2]
  have heq : ((chartAt ℂ q).symm ∘ (chartAt ℂ q)) =ᶠ[𝓝 y] id := by
    filter_upwards [(chartAt ℂ q).open_source.mem_nhds hy] with z hz
    exact (chartAt ℂ q).left_inv hz
  rw [heq.mfderiv_eq, mfderiv_id]

include hf in
/-- **Chain rule in charts.** The chart reading of `f^*η` at `p` is the chart reading of
`η` at `q`, transported by the chart expression `φ` of `f`. -/
theorem chartForm_pullback (η : HolomorphicOneForm ℂ Y) {p : X} {q : Y} {w : ℂ}
    (hw : w ∈ (chartAt ℂ p).target)
    (hfw : f ((chartAt ℂ p).symm w) ∈ (chartAt ℂ q).source) :
    chartForm p (pullbackFormsBundled f hf η) w =
      (chartForm q η (chartMap f p q w)).comp (fderiv ℂ (chartMap f p q) w) := by
  rw [chartMap_fderiv hf hw hfw]
  set x := (chartAt ℂ p).symm w
  have hround : (chartAt ℂ q).symm (chartMap f p q w) = f x := (chartAt ℂ q).left_inv hfw
  show ((η.toFun (f x)).comp (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x)).comp
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (chartAt ℂ p).symm w) =
    ((η.toFun ((chartAt ℂ q).symm (chartMap f p q w))).comp
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (chartAt ℂ q).symm (chartMap f p q w))).comp _
  have hpt : chartMap f p q w = (chartAt ℂ q) (f x) := rfl
  rw [hround]
  rw [hpt]
  have hid := mfderiv_chartAt_symm_comp_self q hfw
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [ContinuousLinearMap.comp_apply]
  congr 1
  have := congrArg (fun L => L ((mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x)
    ((mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (chartAt ℂ p).symm w) v))) hid
  exact this.symm

include hf in
/-- **Local change of variables.** On a ball `V` of the chart at `p` that `f` maps into a ball
`B` of the chart at `q`, the integral of `f^*η` along a segment of `V` equals the integral
of `η` along the segment joining the image endpoints in `B`. -/
theorem segment_integral_pullback (η : HolomorphicOneForm ℂ Y) {p : X} {q : Y}
    {cV : ℂ} {ρV : ℝ} {cY : ℂ} {ρY : ℝ}
    (hV : ball cV ρV ⊆ (chartAt ℂ p).target)
    (hVf : ∀ w ∈ ball cV ρV, f ((chartAt ℂ p).symm w) ∈ (chartAt ℂ q).source)
    (hVB : ∀ w ∈ ball cV ρV, chartMap f p q w ∈ ball cY ρY)
    (hB : ball cY ρY ⊆ (chartAt ℂ q).target) {a b : ℂ}
    (ha : a ∈ ball cV ρV) (hb : b ∈ ball cV ρV) :
    (∫ᶜ x in Path.segment a b, chartForm p (pullbackFormsBundled f hf η) x) =
      ∫ᶜ x in Path.segment (chartMap f p q a) (chartMap f p q b), chartForm q η x := by
  rw [chartForm_segment_eq_sub p _ hV ha hb, chartForm_segment_eq_sub q η hB (hVB a ha) (hVB b hb)]
  set H : ℂ → ℂ := fun w => ∫ᶜ x in Path.segment cV w, chartForm p (pullbackFormsBundled f hf η) x
  set G : ℂ → ℂ := fun z => ∫ᶜ x in Path.segment cY z, chartForm q η x
  have hD : ∀ w ∈ ball cV ρV, HasFDerivAt (fun w => H w - G (chartMap f p q w)) (0 : ℂ →L[ℂ] ℂ) w := by
    intro w hw
    have hH : HasFDerivAt H (chartForm p (pullbackFormsBundled f hf η) w) w :=
      chartForm_hasFDerivAt_primitive p _ hV hw
    have hG : HasFDerivAt G (chartForm q η (chartMap f p q w)) (chartMap f p q w) :=
      chartForm_hasFDerivAt_primitive q η hB (hVB w hw)
    have hφ := (chartMap_differentiableAt hf (hV hw) (hVf w hw)).hasFDerivAt
    have h := hH.sub (hG.comp w hφ)
    rwa [← chartForm_pullback hf η (hV hw) (hVf w hw), sub_self] at h
  have hconst := (convex_ball cV ρV).is_const_of_fderivWithin_eq_zero
    (f := fun w => H w - G (chartMap f p q w)) (𝕜 := ℂ)
    (fun w hw => (hD w hw).differentiableAt.differentiableWithinAt)
    (fun w hw => by
      rw [fderivWithin_of_isOpen isOpen_ball hw]
      exact (hD w hw).fderiv) hb ha
  linear_combination hconst

include hf in
/-- Around each point `z` of a ball `Bbig` in the chart target at `p`, there is a smaller
ball `ball z ε ⊆ Bbig` that `f` maps into a ball of the chart at `q := f (c⁻¹ z)`. -/
theorem exists_local_datum (p : X) {Bc : ℂ} {Br : ℝ} (hBig : ball Bc Br ⊆ (chartAt ℂ p).target)
    {z : ℂ} (hz : z ∈ ball Bc Br) :
    ∃ ε > 0, ∃ q : Y, ∃ cY : ℂ, ∃ ρY : ℝ, ball z ε ⊆ ball Bc Br ∧
      ball cY ρY ⊆ (chartAt ℂ q).target ∧
      ∀ w ∈ ball z ε, f ((chartAt ℂ p).symm w) ∈ (chartAt ℂ q).source ∧
        chartMap f p q w ∈ ball cY ρY := by
  set cp := chartAt ℂ p
  have hzt : z ∈ cp.target := hBig hz
  set q := f (cp.symm z)
  set cq := chartAt ℂ q
  have hy : q ∈ cq.source := mem_chart_source ℂ q
  obtain ⟨ρY, hρ, hBY⟩ := Metric.isOpen_iff.mp cq.open_target (cq q) (cq.map_source hy)
  have hcont1 : ContinuousAt (fun w => f (cp.symm w)) z :=
    hf.continuous.continuousAt.comp (cp.continuousAt_symm hzt)
  have hcont2 : ContinuousAt (chartMap f p q) z := by
    show ContinuousAt (cq ∘ (fun w => f (cp.symm w))) z
    exact ContinuousAt.comp (cq.continuousAt hy) hcont1
  have hS : ball Bc Br ∩ {w | f (cp.symm w) ∈ cq.source} ∩
      {w | chartMap f p q w ∈ ball (cq q) ρY} ∈ 𝓝 z := by
    refine inter_mem (inter_mem (isOpen_ball.mem_nhds hz) ?_) ?_
    · exact hcont1.preimage_mem_nhds (cq.open_source.mem_nhds hy)
    · have h0 : chartMap f p q z = cq q := rfl
      exact hcont2.preimage_mem_nhds (isOpen_ball.mem_nhds (h0 ▸ mem_ball_self hρ))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hS
  exact ⟨ε, hε, q, cq q, ρY, fun w hw => (hball hw).1.1, hBY,
    fun w hw => ⟨(hball hw).1.2, (hball hw).2⟩⟩

omit [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y] in
theorem isChain_ofFn {n : ℕ} (segs : Fin n → ChartSegment Y) (pts : ℕ → Y)
    (h : ∀ k : Fin n, (segs k).start = pts k ∧ (segs k).stop = pts (k + 1)) :
    IsChain (List.ofFn segs) (pts 0) (pts n) := by
  induction n generalizing pts with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ]
    refine ⟨(h 0).1, ?_⟩
    rw [(h 0).2]
    have := ih (fun i => segs i.succ) (fun k => pts (k + 1)) (fun k => by
      have := h k.succ
      simpa [Fin.val_succ] using this)
    simpa using this

theorem chainIntegral_ofFn {n : ℕ} (segs : Fin n → ChartSegment Y) (η : HolomorphicOneForm ℂ Y) :
    chainIntegral η (List.ofFn segs) = ∑ k : Fin n, (segs k).integral η := by
  simp [chainIntegral, List.map_ofFn, List.sum_ofFn]

include hf in
/-- **Pushing one chart segment forward.** -/
theorem exists_pushforward_segment (s : ChartSegment X) :
    ∃ l' : List (ChartSegment Y), IsChain l' (f s.start) (f s.stop) ∧
      ∀ η : HolomorphicOneForm ℂ Y,
        chainIntegral η l' = s.integral (pullbackFormsBundled f hf η) := by
  classical
  set p := s.p
  set cp := chartAt ℂ p
  set Bc := s.center
  set Br := s.radius
  have hBig : ball Bc Br ⊆ cp.target := s.ball_subset
  let w : ℝ → ℂ := fun t => AffineMap.lineMap s.a s.b t
  have hw_cont : Continuous w := AffineMap.lineMap_continuous
  have hwB : ∀ t ∈ Icc (0 : ℝ) 1, w t ∈ ball Bc Br := fun t ht =>
    (convex_ball Bc Br).lineMap_mem s.a_mem s.b_mem ht
  -- local data along the segment
  have hdat : ∀ t : Icc (0 : ℝ) 1, ∃ ε > 0, ∃ q : Y, ∃ cY : ℂ, ∃ ρY : ℝ,
      ball (w t) ε ⊆ ball Bc Br ∧ ball cY ρY ⊆ (chartAt ℂ q).target ∧
      ∀ z ∈ ball (w t) ε, f (cp.symm z) ∈ (chartAt ℂ q).source ∧
        chartMap f p q z ∈ ball cY ρY := fun t =>
    exists_local_datum hf p hBig (hwB t t.2)
  choose ε hε q cY ρY hsub hBY hmap using hdat
  -- Lebesgue number
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric (s := Icc (0 : ℝ) 1)
    (c := fun t : Icc (0 : ℝ) 1 => w ⁻¹' ball (w t) (ε t)) isCompact_Icc
    (fun t => isOpen_ball.preimage hw_cont)
    (fun t ht => mem_iUnion.mpr ⟨⟨t, ht⟩, by
      show w t ∈ ball (w t) (ε ⟨t, ht⟩)
      exact mem_ball_self (hε ⟨t, ht⟩)⟩)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  set N := n + 1
  have hNpos : (0 : ℝ) < N := by positivity
  let x : ℕ → ℂ := fun k => w ((k : ℝ) / N)
  have hkI : ∀ k : ℕ, k ≤ N → ((k : ℝ) / N) ∈ Icc (0 : ℝ) 1 := fun k hk =>
    ⟨by positivity, by rw [div_le_one hNpos]; exact_mod_cast hk⟩
  -- for each piece, a Lebesgue index
  have hpiece : ∀ k : Fin N, ∃ t : Icc (0 : ℝ) 1,
      x k ∈ ball (w t) (ε t) ∧ x (k + 1) ∈ ball (w t) (ε t) := by
    intro k
    obtain ⟨t, ht⟩ := hleb ((k : ℝ) / N) (hkI k k.2.le)
    refine ⟨t, ht (mem_ball_self hδ), ht ?_⟩
    rw [mem_ball, Real.dist_eq]
    have : ((↑(k + 1 : ℕ) : ℝ) / N - (k : ℝ) / N) = 1 / N := by push_cast; ring
    rw [this, abs_of_pos (by positivity)]
    calc (1 : ℝ) / N ≤ 1 / (n + 1) := by simp [N]
      _ < δ := hn
  choose tk htk using hpiece
  let seg : Fin N → ChartSegment Y := fun k =>
    ⟨q (tk k), chartMap f p (q (tk k)) (x k), chartMap f p (q (tk k)) (x (k + 1)),
      cY (tk k), ρY (tk k), hBY (tk k), (hmap (tk k) _ (htk k).1).2,
      (hmap (tk k) _ (htk k).2).2⟩
  let pts : ℕ → Y := fun k => f (cp.symm (x k))
  have hx0 : x 0 = s.a := by simp [x, w]
  have hxN : x N = s.b := by
    simp only [x, w]
    rw [div_self hNpos.ne']
    simp
  refine ⟨List.ofFn seg, ?_, ?_⟩
  · have hc := isChain_ofFn seg pts (fun k => by
      constructor
      · exact (chartAt ℂ (q (tk k))).left_inv (hmap (tk k) _ (htk k).1).1
      · exact (chartAt ℂ (q (tk k))).left_inv (hmap (tk k) _ (htk k).2).1)
    simpa [pts, hx0, hxN, ChartSegment.start, ChartSegment.stop, cp, p] using hc
  · intro η
    rw [chainIntegral_ofFn]
    -- each piece is the integral of `f^*η` over the corresponding sub-segment
    have hpieceEq : ∀ k : Fin N, (seg k).integral η =
        ∫ᶜ z in Path.segment (x k) (x (k + 1)), chartForm p (pullbackFormsBundled f hf η) z := by
      intro k
      exact (segment_integral_pullback hf η ((hsub (tk k)).trans hBig)
        (fun z hz => (hmap (tk k) z hz).1) (fun z hz => (hmap (tk k) z hz).2) (hBY (tk k))
        (htk k).1 (htk k).2).symm
    simp_rw [hpieceEq]
    -- telescoping through the primitive on the big ball
    set H : ℂ → ℂ := fun z =>
      ∫ᶜ y in Path.segment Bc z, chartForm p (pullbackFormsBundled f hf η) y
    have hxB : ∀ k : ℕ, k ≤ N → x k ∈ ball Bc Br := fun k hk => hwB _ (hkI k hk)
    have hstep : ∀ k : Fin N,
        (∫ᶜ z in Path.segment (x k) (x (k + 1)), chartForm p (pullbackFormsBundled f hf η) z) =
          H (x (k + 1)) - H (x k) := fun k =>
      chartForm_segment_eq_sub p _ hBig (hxB k k.2.le) (hxB (k + 1) k.2)
    simp_rw [hstep]
    rw [Fin.sum_univ_eq_sum_range (fun k => H (x (k + 1)) - H (x k)),
      Finset.sum_range_sub (fun k => H (x k)), hx0, hxN]
    exact (chartForm_segment_eq_sub p _ hBig s.a_mem s.b_mem).symm

include hf in
/-- **Pushing a chart chain forward along a holomorphic map** (change of variables
`∫_{f∘γ} η = ∫_γ f^*η`, simultaneously for all forms `η`). -/
theorem exists_pushforward_chain {l : List (ChartSegment X)} {P Q : X} (hl : IsChain l P Q) :
    ∃ l' : List (ChartSegment Y), IsChain l' (f P) (f Q) ∧
      ∀ η : HolomorphicOneForm ℂ Y,
        chainIntegral η l' = chainIntegral (pullbackFormsBundled f hf η) l := by
  induction l generalizing P with
  | nil =>
    simp only [isChain_nil] at hl
    subst hl
    exact ⟨[], rfl, fun η => by simp⟩
  | cons s l ih =>
    obtain ⟨hs, hrest⟩ := hl
    obtain ⟨l₁, hl₁, hint₁⟩ := exists_pushforward_segment hf s
    obtain ⟨l₂, hl₂, hint₂⟩ := ih hrest
    refine ⟨l₁ ++ l₂, ?_, fun η => ?_⟩
    · rw [← hs]; exact hl₁.append hl₂
    · rw [chainIntegral_append, chainIntegral_cons, hint₁, hint₂]

end JacobianChallenge.Periods
