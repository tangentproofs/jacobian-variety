import Jacobian.TraceDegree.PullbackTraceLiftU
import Jacobian.HolomorphicForms.TraceLocal
import Jacobian.AbelJacobi.PathIntegralFunctionalU

/-!
# The trace maps periods of `Y` to periods of `X`

For a nonconstant holomorphic map `f : X → Y` of compact Riemann surfaces, the transpose of
the trace of forms sends the period lattice of `Y` into that of `X`: for a closed chain `c`
in `Y`, the vector `(∫_c Tr ω_j)_j` is a period of `X`.

Classically one lifts `c` through the branched cover. We avoid lifting curves. Fix a base
point `x₀ ∈ X` and chosen chains from `x₀`; put
`Φ(y) = Σ_{f x' = y} m(x') · (∫_{x₀}^{x'} ω_j)_j` (with multiplicity `m`). Then for every
chain `l` from `P` to `Q` in `Y`,

  `(∫_l Tr ω_j)_j − (Φ(Q) − Φ(P)) ∈ Λ_X`,

so a closed chain gives a period. Locally (in the chart at any `y₀`), `∫ Tr ω` is the
difference of `Tr H = Σ_{x'} m(x') H_x(x')` (local primitives `H_x` on the coordinate balls
`U x` around the fibre points `x` of `y₀`, `HolomorphicForms/TraceLocal.lean`), and
`H_x(x') ≡ ∫_{x₀}^{x'} − ∫_{x₀}^{x}` modulo periods; since the fibre points in `U x` number
`m(x)` with multiplicity at every point of the ball, `Tr H − Φ` is constant modulo periods.
A chart segment is cut into pieces each inside one such chart ball (Lebesgue number).
-/

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace JacobianChallenge.TraceDegree

open Set Metric Filter
open scoped ContDiff Manifold Topology
open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods
open JacobianChallenge.AbelJacobi (chosenChain chosenChain_isChain)

universe u v

attribute [local instance] Classical.propDecidable

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [FiniteDimensionalHolomorphicOneForms ℂ X]
variable {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [ConnectedSpace Y] [ChartedSpace ℂ Y]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y]

variable {f : X → Y} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
  (hfin : ∀ y : Y, (f ⁻¹' {y}).Finite) (hnc : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) (x₀ : X)

/-- The traces of the basis forms of `X`. -/
noncomputable def traceBasis (j : Fin (analyticGenus ℂ X)) : HolomorphicOneForm ℂ Y :=
  traceHolomorphicForm hf hfin hnc (holomorphicOneFormFinBasis ℂ X j)

/-- The integrals of the traced basis forms along a chain of `Y`. -/
noncomputable def tracePeriodVector (l : List (ChartSegment Y)) : Fin (analyticGenus ℂ X) → ℂ :=
  fun j => chainIntegral (traceBasis hf hfin hnc j) l

/-- **The fibre potential** `Φ(y) = Σ_{f x' = y} m(x') · (∫_{x₀}^{x'} ω_j)_j`, along the
chosen chains from the base point `x₀`. -/
noncomputable def fiberPotential (y : Y) : Fin (analyticGenus ℂ X) → ℂ :=
  ∑ x' ∈ fiberFin hfin y, mapAnalyticOrderAt f x' • periodVector X (chosenChain X x₀ x')

/-- A local primitive `H_x(x')` is `∫_{x₀}^{x'} − ∫_{x₀}^{x}` modulo periods. -/
theorem H_vector_mem {y₀ : Y} (D : TraceChartData (f := f) hfin y₀) {x x' : X}
    (hx : x ∈ fiberFin hfin y₀) (hx' : x' ∈ D.U x) :
    (fun j => TraceChartData.H (holomorphicOneFormFinBasis ℂ X j) x (chartAt ℂ x x')) -
        periodVector X (chosenChain X x₀ x') + periodVector X (chosenChain X x₀ x) ∈
      genuinePeriodSubgroup X := by
  let s : ChartSegment X := ⟨x, chartAt ℂ x x, chartAt ℂ x x', chartAt ℂ x x, D.r x,
    D.ballX_sub x hx, mem_ball_self (D.r_pos hx), D.U_sub_ball x hx x' hx'⟩
  have hs : IsChain [s] x x' :=
    ⟨(chartAt ℂ x).left_inv (mem_chart_source ℂ x),
      (chartAt ℂ x).left_inv (D.U_sub_source x hx hx')⟩
  have hmem := periodVector_sub_mem ((chosenChain_isChain X x₀ x).append hs)
    (chosenChain_isChain X x₀ x')
  have heq : periodVector X [s] =
      fun j => TraceChartData.H (holomorphicOneFormFinBasis ℂ X j) x (chartAt ℂ x x') := by
    funext j
    simp [periodVector, chainIntegral, ChartSegment.integral, TraceChartData.H, s]
  rw [periodVector_append, heq] at hmem
  convert hmem using 1
  abel

/-- **`Tr H − Φ` is constant modulo periods** on the ball of the local trace data. -/
theorem trH_sub_fiberPotential_mem {y₀ : Y} (D : TraceChartData (f := f) hfin y₀) {w : ℂ}
    (hw : w ∈ ball (chartAt ℂ y₀ y₀) D.ρ) :
    (fun j => D.trH (holomorphicOneFormFinBasis ℂ X j) w) -
        fiberPotential hfin x₀ ((chartAt ℂ y₀).symm w) +
        ∑ x ∈ fiberFin hfin y₀, mapAnalyticOrderAt f x • periodVector X (chosenChain X x₀ x) ∈
      genuinePeriodSubgroup X := by
  set b := holomorphicOneFormFinBasis ℂ X
  set β : X → Fin (analyticGenus ℂ X) → ℂ := fun x' => periodVector X (chosenChain X x₀ x')
  set Hv : X → X → Fin (analyticGenus ℂ X) → ℂ :=
    fun x x' j => TraceChartData.H (b j) x (chartAt ℂ x x')
  have h1 : (fun j => D.trH (b j) w) =
      ∑ x ∈ fiberFin hfin y₀, ∑ x' ∈ D.S w x, mapAnalyticOrderAt f x' • Hv x x' := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply]
    simp only [TraceChartData.trH, nsmul_eq_mul, Hv]
  have h2 : fiberPotential hfin x₀ ((chartAt ℂ y₀).symm w) =
      ∑ x ∈ fiberFin hfin y₀, ∑ x' ∈ D.S w x, mapAnalyticOrderAt f x' • β x' := by
    unfold fiberPotential
    rw [D.fiberFin_eq_biUnion hw, Finset.sum_biUnion (D.S_pairwiseDisjoint w)]
  have h3 : ∑ x ∈ fiberFin hfin y₀, mapAnalyticOrderAt f x • β x =
      ∑ x ∈ fiberFin hfin y₀, ∑ x' ∈ D.S w x, mapAnalyticOrderAt f x' • β x := by
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [← Finset.sum_smul, D.sum_order_S hw hx]
  have hkey : (fun j => D.trH (b j) w) - fiberPotential hfin x₀ ((chartAt ℂ y₀).symm w) +
      ∑ x ∈ fiberFin hfin y₀, mapAnalyticOrderAt f x • β x =
      ∑ x ∈ fiberFin hfin y₀, ∑ x' ∈ D.S w x,
        mapAnalyticOrderAt f x' • (Hv x x' - β x' + β x) := by
    rw [h1, h2, h3, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x' _ => ?_
    rw [smul_add, smul_sub]
  rw [hkey]
  refine AddSubgroup.sum_mem _ fun x hx => AddSubgroup.sum_mem _ fun x' hx' => ?_
  exact AddSubgroup.nsmul_mem _ (H_vector_mem hfin x₀ D hx (Finset.mem_filter.mp hx').2) _

include hf in
/-- Around each point of a ball in a chart target of `Y`, a smaller ball whose points lie in
the domain of the chosen local trace data at the centre's image. -/
theorem exists_trace_datum (p : Y) {Bc : ℂ} {Br : ℝ} (hBig : ball Bc Br ⊆ (chartAt ℂ p).target)
    {z : ℂ} (hz : z ∈ ball Bc Br) :
    ∃ ε > 0, ball z ε ⊆ ball Bc Br ∧ ∀ z' ∈ ball z ε,
      (chartAt ℂ p).symm z' ∈ (chartAt ℂ ((chartAt ℂ p).symm z)).source ∧
      chartAt ℂ ((chartAt ℂ p).symm z) ((chartAt ℂ p).symm z') ∈
        ball (chartAt ℂ ((chartAt ℂ p).symm z) ((chartAt ℂ p).symm z))
          (chosenData hf hfin hnc ((chartAt ℂ p).symm z)).ρ := by
  set cp := chartAt ℂ p
  have hzt : z ∈ cp.target := hBig hz
  set q := cp.symm z
  set cq := chartAt ℂ q
  have hy : q ∈ cq.source := mem_chart_source ℂ q
  have hcont1 : ContinuousAt cp.symm z := cp.continuousAt_symm hzt
  have hcont2 : ContinuousAt (fun z' => cq (cp.symm z')) z :=
    ContinuousAt.comp (g := cq) (cq.continuousAt hy) hcont1
  have hS : ball Bc Br ∩ {z' | cp.symm z' ∈ cq.source} ∩
      {z' | cq (cp.symm z') ∈ ball (cq q) (chosenData hf hfin hnc q).ρ} ∈ 𝓝 z := by
    refine inter_mem (inter_mem (isOpen_ball.mem_nhds hz) ?_) ?_
    · exact hcont1.preimage_mem_nhds (cq.open_source.mem_nhds hy)
    · exact hcont2.preimage_mem_nhds
        (isOpen_ball.mem_nhds (mem_ball_self (chosenData hf hfin hnc q).ρ_pos))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hS
  exact ⟨ε, hε, fun w hw => (hball hw).1.1, fun w hw => ⟨(hball hw).1.2, (hball hw).2⟩⟩

include hf in
/-- **One chart segment of `Y`.** -/
theorem tracePeriodVector_segment_mem (s : ChartSegment Y) :
    tracePeriodVector hf hfin hnc [s] -
        (fiberPotential hfin x₀ s.stop - fiberPotential hfin x₀ s.start) ∈
      genuinePeriodSubgroup X := by
  classical
  set b := holomorphicOneFormFinBasis ℂ X
  set p := s.p
  set cp := chartAt ℂ p
  set Bc := s.center
  set Br := s.radius
  have hBig : ball Bc Br ⊆ cp.target := s.ball_subset
  let w : ℝ → ℂ := fun t => AffineMap.lineMap s.a s.b t
  have hw_cont : Continuous w := AffineMap.lineMap_continuous
  have hwB : ∀ t ∈ Icc (0 : ℝ) 1, w t ∈ ball Bc Br := fun t ht =>
    (convex_ball Bc Br).lineMap_mem s.a_mem s.b_mem ht
  have hdat := fun t : Icc (0 : ℝ) 1 => exists_trace_datum hf hfin hnc p hBig (hwB t t.2)
  choose ε hε hsub hmap using hdat
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
  have hx0 : x 0 = s.a := by simp [x, w]
  have hxN : x N = s.b := by
    simp only [x, w]
    rw [div_self hNpos.ne']
    simp
  have hxB : ∀ k : ℕ, k ≤ N → x k ∈ ball Bc Br := fun k hk => hwB _ (hkI k hk)
  let P : Fin N → Fin (analyticGenus ℂ X) → ℂ := fun k j =>
    ∫ᶜ z in Path.segment (x k) (x (k + 1)), chartForm p (traceBasis hf hfin hnc j) z
  have hsum : tracePeriodVector hf hfin hnc [s] = ∑ k : Fin N, P k := by
    funext j
    rw [Finset.sum_apply]
    simp only [tracePeriodVector, chainIntegral, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, ChartSegment.integral]
    set H : ℂ → ℂ := fun z => ∫ᶜ y in Path.segment Bc z, chartForm p (traceBasis hf hfin hnc j) y
    have hstep : ∀ k : Fin N, P k j = H (x (k + 1)) - H (x k) := fun k =>
      chartForm_segment_eq_sub p _ hBig (hxB k k.2.le) (hxB (k + 1) k.2)
    simp_rw [hstep]
    rw [Fin.sum_univ_eq_sum_range (fun k => H (x (k + 1)) - H (x k)),
      Finset.sum_range_sub (fun k => H (x k)), hx0, hxN]
    exact chartForm_segment_eq_sub p _ hBig s.a_mem s.b_mem
  have hΦ : fiberPotential hfin x₀ s.stop - fiberPotential hfin x₀ s.start =
      ∑ k : Fin N, (fiberPotential hfin x₀ (cp.symm (x (k + 1))) -
        fiberPotential hfin x₀ (cp.symm (x k))) := by
    rw [Fin.sum_univ_eq_sum_range (fun k => fiberPotential hfin x₀ (cp.symm (x (k + 1))) -
        fiberPotential hfin x₀ (cp.symm (x k))),
      Finset.sum_range_sub (fun k => fiberPotential hfin x₀ (cp.symm (x k))), hx0, hxN]
    rfl
  rw [hsum, hΦ, ← Finset.sum_sub_distrib]
  refine AddSubgroup.sum_mem _ fun k _ => ?_
  set t := tk k
  set q := cp.symm (w t)
  set D := chosenData hf hfin hnc q
  set cq := chartAt ℂ q
  have hk1 := hmap t _ (htk k).1
  have hk2 := hmap t _ (htk k).2
  have hseg : P k = (fun j => D.trH (b j) (cq (cp.symm (x (k + 1))))) -
      (fun j => D.trH (b j) (cq (cp.symm (x k)))) := by
    funext j
    exact traceHolomorphicForm_segment_eq hf hfin hnc (b j) q p ((hsub t).trans hBig)
      (hmap t) (htk k).1 (htk k).2
  have hC1 := trH_sub_fiberPotential_mem hfin x₀ D hk2.2
  have hC0 := trH_sub_fiberPotential_mem hfin x₀ D hk1.2
  rw [cq.left_inv hk2.1] at hC1
  rw [cq.left_inv hk1.1] at hC0
  have hmem := sub_mem hC1 hC0
  rw [hseg]
  convert hmem using 1
  abel

include hf in
/-- **Chains of `Y`**: `(∫_l Tr ω_j)_j ≡ Φ(Q) − Φ(P)` modulo the periods of `X`. -/
theorem tracePeriodVector_chain_mem {l : List (ChartSegment Y)} {P Q : Y} (hl : IsChain l P Q) :
    tracePeriodVector hf hfin hnc l - (fiberPotential hfin x₀ Q - fiberPotential hfin x₀ P) ∈
      genuinePeriodSubgroup X := by
  induction l generalizing P with
  | nil =>
    simp only [isChain_nil] at hl
    subst hl
    have h0 : tracePeriodVector hf hfin hnc ([] : List (ChartSegment Y)) = 0 := by
      funext j; simp [tracePeriodVector]
    rw [h0, sub_self, sub_self]
    exact zero_mem _
  | cons s l ih =>
    obtain ⟨h1, h2⟩ := hl
    have hs := tracePeriodVector_segment_mem hf hfin hnc x₀ s
    have hl' := ih h2
    have hcons : tracePeriodVector hf hfin hnc (s :: l) =
        tracePeriodVector hf hfin hnc [s] + tracePeriodVector hf hfin hnc l := by
      funext j; simp [tracePeriodVector, chainIntegral_cons]
    rw [hcons, ← h1]
    convert add_mem hs hl' using 1
    abel

variable [FiniteDimensionalHolomorphicOneForms ℂ Y]

/-- The ambient pullback sends the period vector of a chain of `Y` to its trace period
vector. -/
theorem traceDualPullbackLiftCLMU_periodVector (l : List (ChartSegment Y)) :
    traceDualPullbackLiftCLMU f hf (periodVector Y l) = tracePeriodVector hf hfin hnc l := by
  funext j
  simp only [traceDualPullbackLiftCLMU, LinearMap.coe_toContinuousLinearMap',
    traceDualPullbackLiftLinearMapU, traceDualPullbackLiftU, Matrix.toLin'_apply,
    Matrix.mulVec, dotProduct, Matrix.transpose_apply, LinearMap.toMatrix'_apply]
  have hcoord : ∀ i, traceFormsCoordU f hf (Pi.single j 1) i =
      (holomorphicOneFormFinBasis ℂ Y).repr (traceBasis hf hfin hnc j) i := by
    intro i
    have h1 : (holomorphicOneFormFinBasis ℂ X).equivFun.symm (Pi.single j 1) =
        holomorphicOneFormFinBasis ℂ X j := by
      rw [Module.Basis.equivFun_symm_apply]
      simp [Pi.single_apply]
    show (holomorphicOneFormFinBasis ℂ Y).equivFun
      (traceFormsBundledLM f hf
        ((holomorphicOneFormFinBasis ℂ X).equivFun.symm (Pi.single j 1))) i = _
    rw [h1, Module.Basis.equivFun_apply]
    show (holomorphicOneFormFinBasis ℂ Y).repr (traceFormsBundled f hf _) i = _
    rw [traceFormsBundled_eq_traceHolomorphicForm f hf hfin hnc]
    rfl
  simp_rw [hcoord]
  show _ = chainIntegral (traceBasis hf hfin hnc j) l
  conv_rhs => rw [← (holomorphicOneFormFinBasis ℂ Y).sum_repr (traceBasis hf hfin hnc j)]
  rw [← chainIntegralLM_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, chainIntegralLM_apply, smul_eq_mul]
  rfl

include hf hfin hnc in
/-- **The pullback maps periods to periods** (nonconstant case). -/
theorem traceDualPullbackLift_genuinePeriods :
    ∀ v ∈ genuinePeriodSubgroup Y, traceDualPullbackLiftCLMU f hf v ∈ genuinePeriodSubgroup X := by
  intro v hv
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  have hle : genuinePeriodSubgroup Y ≤ (genuinePeriodSubgroup X).comap
      (traceDualPullbackLiftCLMU f hf).toLinearMap.toAddMonoidHom := by
    refine AddSubgroup.closure_le _ |>.mpr ?_
    rintro _ ⟨P, Q, l₁, l₂, h₁, h₂, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap]
    show traceDualPullbackLiftCLMU f hf (periodVector Y l₁ - periodVector Y l₂) ∈
      genuinePeriodSubgroup X
    rw [map_sub, traceDualPullbackLiftCLMU_periodVector hf hfin hnc,
      traceDualPullbackLiftCLMU_periodVector hf hfin hnc]
    have := sub_mem (tracePeriodVector_chain_mem hf hfin hnc x₀ h₁)
      (tracePeriodVector_chain_mem hf hfin hnc x₀ h₂)
    rwa [sub_sub_sub_cancel_right] at this
  exact hle hv

end JacobianChallenge.TraceDegree
