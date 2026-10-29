import Jacobian.Periods.ChartedFormPullbackContinuous
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare

/-!
# Chart chains and the local exactness of holomorphic 1-forms

A holomorphic 1-form `ω` on a Riemann surface `X`, read in the chart at `p`, is the
`ℂ`-valued 1-form `chartForm p ω e = ω(c⁻¹ e) ∘ D(c⁻¹)(e)` on the chart target
(`c = chartAt ℂ p`). This file proves the two analytic facts the period / Abel–Jacobi
layer needs, with no chart-stability assumption:

* `chartForm_contDiffOn` — the chart reading is holomorphic on the chart target (it is the
  smooth cotangent section read through the cotangent trivialization at `p`);
* `chartForm_segment_eq_sub` / `chartForm_hasFDerivAt_primitive` — on any ball inside the
  chart target the form is exact: segment integrals are differences of a primitive
  (Poincaré lemma for the closed form `chartForm p ω`; a holomorphic form in one variable
  is automatically closed, `isSymm_of_complexLinear`).

It then defines **chart chains**: finite lists of straight segments, each lying in a ball
inside one chart target, glued end to end. A chain is the combinatorial stand-in for a
piecewise-smooth path; integrating `ω` along it is the classical line integral, written in
charts. Chains concatenate by list append (`IsChain.append`, `chainIntegral_append`), the
integral is linear in the form (`chainIntegral_add`, `chainIntegral_smul`), and any two
points of a connected surface are joined by a chain (`exists_chain`).
-/

set_option linter.unusedSectionVars false

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms Set Metric Filter
open scoped Manifold Topology

universe u

section Analytic

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/-- A holomorphic 1-form read in the chart at `p`: `e ↦ ω(c⁻¹ e) ∘ D(c⁻¹)(e)`. -/
noncomputable abbrev chartForm (p : X) (ω : HolomorphicOneForm ℂ X) : ℂ → ℂ →L[ℂ] ℂ :=
  chartedFormPullback (chartAt ℂ p) ω

/-- The chart reading of a holomorphic 1-form is holomorphic (`C^ω`) on the chart target. -/
theorem chartForm_contDiffOn (p : X) (ω : HolomorphicOneForm ℂ X) :
    ContDiffOn ℂ (⊤ : WithTop ℕ∞) (chartForm p ω) (chartAt ℂ p).target := by
  have hkey : ∀ e' ∈ (chartAt ℂ p).target,
      chartForm p ω e' =
        ((trivializationAt (ℂ →L[ℂ] ℂ) (CotangentSpace ℂ X) p)
          ⟨(chartAt ℂ p).symm e', ω.toFun ((chartAt ℂ p).symm e')⟩).snd := by
    intro e' he'
    rw [ChartedFormPullbackContinuous.trivCT_read_eq_value_comp_symmL ω p
      ((chartAt ℂ p).symm e')]
    show (ω.toFun ((chartAt ℂ p).symm e')).comp (mfderiv _ _ (chartAt ℂ p).symm e') =
      (ω.toFun ((chartAt ℂ p).symm e')).comp
        ((trivializationAt ℂ (TangentSpace (modelWithCornersSelf ℂ ℂ)) p).symmL ℂ
          ((chartAt ℂ p).symm e'))
    rw [ChartedFormPullbackContinuous.mfderiv_chartSymm_eq_symmL p he']
    rfl
  rw [← contMDiffOn_iff_contDiffOn]
  refine ContMDiffOn.congr ?_ hkey
  intro e he
  have hb : (chartAt ℂ p).symm e ∈
      (trivializationAt (ℂ →L[ℂ] ℂ) (CotangentSpace ℂ X) p).baseSet := by
    have hmem : (chartAt ℂ p).symm e ∈ (chartAt ℂ p).source := (chartAt ℂ p).map_target he
    simpa [FiberBundle.mem_baseSet_trivializationAt'] using hmem
  have hsmooth :
      ContMDiffAt (modelWithCornersSelf ℂ ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) (⊤ : WithTop ℕ∞)
        (fun b' => ((trivializationAt (ℂ →L[ℂ] ℂ) (CotangentSpace ℂ X) p)
          ⟨b', ω.toFun b'⟩).snd) ((chartAt ℂ p).symm e) :=
    ((trivializationAt (ℂ →L[ℂ] ℂ) (CotangentSpace ℂ X) p).contMDiffAt_section_iff
      hb).mp ω.contMDiff_toFun.contMDiffAt
  exact hsmooth.comp_contMDiffWithinAt e (contMDiffOn_chart_symm (n := ⊤) e he)

/-- Any `ℂ`-linear map `ℂ →L[ℂ] (ℂ →L[ℂ] ℂ)` is a symmetric bilinear form. -/
theorem isSymm_of_complexLinear (D : ℂ →L[ℂ] (ℂ →L[ℂ] ℂ)) (x y : ℂ) : D x y = D y x := by
  have h : ∀ x y : ℂ, D x y = x * (y * D 1 1) := by
    intro x y
    have hx : D x = x • D 1 := by rw [← map_smul, smul_eq_mul, mul_one]
    rw [hx, ContinuousLinearMap.smul_apply, smul_eq_mul]
    congr 1
    have hy : (D 1) y = y • (D 1) 1 := by rw [← map_smul, smul_eq_mul, mul_one]
    rw [hy, smul_eq_mul]
  rw [h x y, h y x]
  ring

variable (p : X) (ω : HolomorphicOneForm ℂ X) {z : ℂ} {r : ℝ}

/-- On an open subset of the chart target, the chart reading has a (real-linear) derivative,
and it is symmetric. -/
private theorem chartForm_hasFDerivWithinAt {s : Set ℂ} (_hs : IsOpen s)
    (hsub : s ⊆ (chartAt ℂ p).target) :
    ∀ x ∈ s, HasFDerivWithinAt (chartForm p ω)
      ((fderiv ℂ (chartForm p ω) x).restrictScalars ℝ) s x := by
  intro x hx
  have hd : DifferentiableAt ℂ (chartForm p ω) x :=
    ((chartForm_contDiffOn p ω).differentiableOn (by simp)).differentiableAt
      ((chartAt ℂ p).open_target.mem_nhds (hsub hx))
  exact (hd.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt

/-- **Local exactness.** On a ball inside the chart target, the integral of `chartForm p ω`
along a segment is the difference of the primitive `w ↦ ∫ᶜ x in segment z w, …`. -/
theorem chartForm_segment_eq_sub (hB : ball z r ⊆ (chartAt ℂ p).target) {a b : ℂ}
    (ha : a ∈ ball z r) (hb : b ∈ ball z r) :
    (∫ᶜ x in Path.segment a b, chartForm p ω x) =
      (∫ᶜ x in Path.segment z b, chartForm p ω x) -
        ∫ᶜ x in Path.segment z a, chartForm p ω x := by
  have hz : z ∈ ball z r := mem_ball_self (pos_of_mem_ball ha)
  have h := (convex_ball z r).curveIntegral_segment_add_eq_of_hasFDerivWithinAt_symmetric
    (chartForm_hasFDerivWithinAt p ω isOpen_ball hB)
    (fun a _ x _ y _ => by
      simp only [ContinuousLinearMap.coe_restrictScalars']
      exact isSymm_of_complexLinear _ x y) hz ha hb
  rw [← h]
  ring

/-- **The local primitive.** On a ball inside the chart target, `w ↦ ∫ᶜ x in segment z w, …`
is a holomorphic primitive of the chart reading of `ω`. -/
theorem chartForm_hasFDerivAt_primitive (hB : ball z r ⊆ (chartAt ℂ p).target) {w : ℂ}
    (hw : w ∈ ball z r) :
    HasFDerivAt (fun w' => ∫ᶜ x in Path.segment z w', chartForm p ω x) (chartForm p ω w) w := by
  have hz : z ∈ ball z r := mem_ball_self (pos_of_mem_ball hw)
  have h := (convex_ball z r).hasFDerivWithinAt_curveIntegral_segment_of_hasFDerivWithinAt_symmetric
    (chartForm_hasFDerivWithinAt p ω isOpen_ball hB)
    (fun a _ x _ y _ => by
      simp only [ContinuousLinearMap.coe_restrictScalars']
      exact isSymm_of_complexLinear _ x y) hz hw
  exact h.hasFDerivAt (isOpen_ball.mem_nhds hw)

end Analytic

section Chains

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

variable (X) in
/--
A **chart segment**: the straight segment from `a` to `b` in the chart at `p`, lying in a
ball inside the chart target. On the surface it is the curve `t ↦ c⁻¹((1-t)a + tb)`.
-/
structure ChartSegment where
  /-- the point whose chart is used -/
  p : X
  /-- start, in chart coordinates -/
  a : ℂ
  /-- end, in chart coordinates -/
  b : ℂ
  /-- centre of a ball in the chart target containing the segment -/
  center : ℂ
  /-- radius of that ball -/
  radius : ℝ
  ball_subset : ball center radius ⊆ (chartAt ℂ p).target
  a_mem : a ∈ ball center radius
  b_mem : b ∈ ball center radius

namespace ChartSegment

variable (s : ChartSegment X)

/-- The starting point of the segment, on the surface. -/
noncomputable def start : X := (chartAt ℂ s.p).symm s.a

/-- The end point of the segment, on the surface. -/
noncomputable def stop : X := (chartAt ℂ s.p).symm s.b

/-- The line integral of `ω` along the segment, computed in the chart at `p`. -/
noncomputable def integral (ω : HolomorphicOneForm ℂ X) : ℂ :=
  ∫ᶜ x in Path.segment s.a s.b, chartForm s.p ω x

theorem lineMap_mem_target {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    AffineMap.lineMap s.a s.b t ∈ (chartAt ℂ s.p).target :=
  s.ball_subset ((convex_ball s.center s.radius).lineMap_mem s.a_mem s.b_mem ht)

theorem curveIntegrable (ω : HolomorphicOneForm ℂ X) :
    CurveIntegrable (chartForm s.p ω) (Path.segment s.a s.b) := by
  rw [curveIntegrable_segment]
  apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
  have hcont := (chartForm_contDiffOn s.p ω).continuousOn
  exact (hcont.comp AffineMap.lineMap_continuous.continuousOn
    (fun t ht => s.lineMap_mem_target ht)).clm_apply continuousOn_const

theorem chartForm_add (p : X) (ω₁ ω₂ : HolomorphicOneForm ℂ X) :
    chartForm p (ω₁ + ω₂) = chartForm p ω₁ + chartForm p ω₂ :=
  chartedFormPullback_add _ ω₁ ω₂

theorem chartForm_smul (p : X) (c : ℂ) (ω : HolomorphicOneForm ℂ X) :
    chartForm p (c • ω) = c • chartForm p ω :=
  chartedFormPullback_smul _ c ω

theorem integral_add (ω₁ ω₂ : HolomorphicOneForm ℂ X) :
    s.integral (ω₁ + ω₂) = s.integral ω₁ + s.integral ω₂ := by
  unfold integral
  rw [chartForm_add]
  exact curveIntegral_add (s.curveIntegrable ω₁) (s.curveIntegrable ω₂)

theorem integral_smul (c : ℂ) (ω : HolomorphicOneForm ℂ X) :
    s.integral (c • ω) = c • s.integral ω := by
  unfold integral
  rw [chartForm_smul]
  exact curveIntegral_smul

/-- The segment integral is the difference of the local primitive at the two ends. -/
theorem integral_eq_sub (ω : HolomorphicOneForm ℂ X) :
    s.integral ω = (∫ᶜ x in Path.segment s.center s.b, chartForm s.p ω x) -
      ∫ᶜ x in Path.segment s.center s.a, chartForm s.p ω x :=
  chartForm_segment_eq_sub s.p ω s.ball_subset s.a_mem s.b_mem

end ChartSegment

/-- `IsChain l P Q`: the segments of `l` are glued end to end, from `P` to `Q`. -/
def IsChain : List (ChartSegment X) → X → X → Prop
  | [], P, Q => P = Q
  | s :: l, P, Q => s.start = P ∧ IsChain l s.stop Q

@[simp] theorem isChain_nil {P Q : X} : IsChain [] P Q ↔ P = Q := Iff.rfl

@[simp] theorem isChain_cons {s : ChartSegment X} {l : List (ChartSegment X)} {P Q : X} :
    IsChain (s :: l) P Q ↔ s.start = P ∧ IsChain l s.stop Q := Iff.rfl

theorem IsChain.append {l₁ l₂ : List (ChartSegment X)} {P Q R : X}
    (h₁ : IsChain l₁ P Q) (h₂ : IsChain l₂ Q R) : IsChain (l₁ ++ l₂) P R := by
  induction l₁ generalizing P with
  | nil => simp only [isChain_nil] at h₁; subst h₁; simpa using h₂
  | cons s l ih => exact ⟨h₁.1, ih h₁.2⟩

/-- The line integral of `ω` along a chain. -/
noncomputable def chainIntegral (ω : HolomorphicOneForm ℂ X) (l : List (ChartSegment X)) : ℂ :=
  (l.map fun s => s.integral ω).sum

@[simp] theorem chainIntegral_nil (ω : HolomorphicOneForm ℂ X) :
    chainIntegral ω ([] : List (ChartSegment X)) = 0 := rfl

theorem chainIntegral_append (ω : HolomorphicOneForm ℂ X) (l₁ l₂ : List (ChartSegment X)) :
    chainIntegral ω (l₁ ++ l₂) = chainIntegral ω l₁ + chainIntegral ω l₂ := by
  simp [chainIntegral]

theorem chainIntegral_cons (ω : HolomorphicOneForm ℂ X) (s : ChartSegment X)
    (l : List (ChartSegment X)) :
    chainIntegral ω (s :: l) = s.integral ω + chainIntegral ω l := by
  simp [chainIntegral]

/-- Integration along a chain, as a linear functional on holomorphic 1-forms. -/
noncomputable def chainIntegralLM (l : List (ChartSegment X)) :
    HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ where
  toFun ω := chainIntegral ω l
  map_add' ω₁ ω₂ := by
    induction l with
    | nil => simp
    | cons s l ih => simp only [chainIntegral_cons, s.integral_add, ih]; ring
  map_smul' c ω := by
    induction l with
    | nil => simp
    | cons s l ih =>
      simp only [chainIntegral_cons, s.integral_smul, ih, RingHom.id_apply, smul_eq_mul]; ring

@[simp] theorem chainIntegralLM_apply (l : List (ChartSegment X)) (ω : HolomorphicOneForm ℂ X) :
    chainIntegralLM l ω = chainIntegral ω l := rfl

/-- Around every point there is a neighbourhood whose points are joined to it, both ways,
by a single chart segment. -/
theorem exists_nhds_chain (Q₀ : X) :
    ∀ᶠ Q in 𝓝 Q₀, (∃ l, IsChain l Q₀ Q) ∧ ∃ l, IsChain l Q Q₀ := by
  set c := chartAt ℂ Q₀
  have hQ₀ : Q₀ ∈ c.source := mem_chart_source ℂ Q₀
  obtain ⟨r, hr, hB⟩ := Metric.isOpen_iff.mp c.open_target (c Q₀) (c.map_source hQ₀)
  have hcenter : c Q₀ ∈ ball (c Q₀) r := mem_ball_self hr
  have hU : c.source ∩ c ⁻¹' ball (c Q₀) r ∈ 𝓝 Q₀ :=
    inter_mem (c.open_source.mem_nhds hQ₀)
      ((c.continuousAt hQ₀).preimage_mem_nhds (isOpen_ball.mem_nhds hcenter))
  filter_upwards [hU] with Q hQ
  refine ⟨⟨[⟨Q₀, c Q₀, c Q, c Q₀, r, hB, hcenter, hQ.2⟩], ?_⟩,
    ⟨[⟨Q₀, c Q, c Q₀, c Q₀, r, hB, hQ.2, hcenter⟩], ?_⟩⟩
  · simp [ChartSegment.start, ChartSegment.stop, c.left_inv hQ₀, c.left_inv hQ.1, c]
  · simp [ChartSegment.start, ChartSegment.stop, c.left_inv hQ₀, c.left_inv hQ.1, c]

/-- **Chain-connectedness.** Any two points of a connected Riemann surface are joined by a
chart chain. -/
theorem exists_chain [ConnectedSpace X] (P Q : X) : ∃ l : List (ChartSegment X), IsChain l P Q := by
  let S : Set X := {Q | ∃ l, IsChain l P Q}
  have hopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    rintro Q₀ ⟨l, hl⟩
    filter_upwards [exists_nhds_chain Q₀] with Q hQ
    obtain ⟨l', hl'⟩ := hQ.1
    exact ⟨l ++ l', hl.append hl'⟩
  have hclosed : IsClosed S := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro Q₀ hQ₀
    filter_upwards [exists_nhds_chain Q₀] with Q hQ hQS
    obtain ⟨l, hl⟩ := hQS
    obtain ⟨l', hl'⟩ := hQ.2
    exact hQ₀ ⟨l ++ l', hl.append hl'⟩
  have hP : P ∈ S := ⟨[], rfl⟩
  have huniv : S = univ := (IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨P, hP⟩)
  have hQ : Q ∈ S := huniv ▸ mem_univ Q
  exact hQ

end Chains

end JacobianChallenge.Periods
