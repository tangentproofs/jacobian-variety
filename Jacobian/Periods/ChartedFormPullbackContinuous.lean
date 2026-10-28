import Jacobian.HolomorphicForms.Defs
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Topology.VectorBundle.Hom
import Mathlib.Topology.VectorBundle.Constructions
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Jacobian.Periods.ChartedFormPullbackSimp
import Jacobian.Periods.ChartedFormPullbackSmul
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Tangent

/-!
# `chartedFormPullback_continuousOn` without `StableChartAt` (Path 1′ Step 1)

The genuine chart-pullback `chartedFormPullback c ω e = (ω.toFun (c.symm e)).comp
(mfderiv c.symm e)` is a FRAME-INDEPENDENT object: it is the cotangent form `ω`
read in chart `c`'s frame. Its continuity on `c.target` follows from the smooth
cotangent section read through chart `c`'s cotangent trivialization
(`Bundle.contMDiffAt_section` at a FIXED basepoint — no varying chart index),
exactly the sorry-free `omit [StableChartAt]` pattern already used at the canonical
basepoint in `HolomorphicOneFormToFunContinuous`.

This avoids the operator-norm chart-overlap-derivative "wall": that wall only
appears when the frame-independent composition is split into the two
canonical-frame factors and each is proven continuous separately.
-/

namespace JacobianChallenge.Periods.ChartedFormPullbackContinuous

open Bundle Set Filter
open scoped Manifold Topology
open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Bridge (chartAt case): `mfderiv (chartAt E p₀).symm e` equals the tangent
trivialization `symmL` at the chart point. NO `StableChartAt`. -/
theorem mfderiv_chartSymm_eq_symmL (p₀ : X) {e : E}
    (he : e ∈ (chartAt E p₀).target) :
    mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) (chartAt E p₀).symm e =
      (trivializationAt E (TangentSpace (modelWithCornersSelf ℂ E)) p₀).symmL ℂ
        ((chartAt E p₀).symm e) := by
  have hsrc : (chartAt E p₀).symm e ∈ (chartAt E p₀).source := (chartAt E p₀).map_target he
  rw [TangentBundle.symmL_trivializationAt (I := modelWithCornersSelf ℂ E) hsrc]
  -- self-model: extChartAt = chartAt, range = univ, mfderivWithin univ = mfderiv.
  simp only [modelWithCornersSelf_coe, Set.range_id, mfderivWithin_univ]
  -- extChartAt I p₀ ((chartAt p₀).symm e) = e (self-model: extChartAt acts as chartAt).
  have hpt : (extChartAt (modelWithCornersSelf ℂ E) p₀) ((chartAt E p₀).symm e) = e := by
    simp [extChartAt, (chartAt E p₀).right_inv he]
  rw [hpt]
  -- Both sides now differ only by the (defeq) symm chart; `extChartAt.symm = chartAt.symm`.
  congr 1

/-- The cotangent section read through the FIXED trivialization at `p₀` is
operator-norm continuous at any `b` in that trivialization's baseSet
(`= (chartAt E p₀).source`). Generalizes the basepoint-only
`ω_comp_symmL_continuousAt` from `HolomorphicOneFormToFunContinuous`. NO
`StableChartAt`. -/
theorem cotangent_trivRead_continuousAt
    (ω : HolomorphicOneForm E X) (p₀ : X) {b : X}
    (hb : b ∈ (trivializationAt (E →L[ℂ] ℂ) (CotangentSpace E X) p₀).baseSet) :
    ContinuousAt (fun b' : X =>
      ((trivializationAt (E →L[ℂ] ℂ) (CotangentSpace E X) p₀)
        ⟨b', ω.toFun b'⟩).snd) b := by
  have hsmooth :
      ContMDiffAt (modelWithCornersSelf ℂ E) 𝓘(ℂ, E →L[ℂ] ℂ) (⊤ : WithTop ℕ∞)
        (fun b' => ((trivializationAt (E →L[ℂ] ℂ) (CotangentSpace E X) p₀)
          ⟨b', ω.toFun b'⟩).snd) b :=
    ((trivializationAt (E →L[ℂ] ℂ) (CotangentSpace E X) p₀).contMDiffAt_section_iff
      hb).mp ω.contMDiff_toFun.contMDiffAt
  exact hsmooth.continuousAt

/-- The cotangent trivialization's fiber-second-component equals the cotangent
value composed with the tangent `symmL`. (Local re-derivation of the private
`trivCT_section_eq_comp_symmL`; no `StableChartAt`.) -/
theorem trivCT_read_eq_value_comp_symmL
    (ω : HolomorphicOneForm E X) (p₀ b : X) :
    ((trivializationAt (E →L[ℂ] ℂ) (CotangentSpace E X) p₀) ⟨b, ω.toFun b⟩).snd =
      (ω.toFun b).comp
        ((trivializationAt E (TangentSpace (modelWithCornersSelf ℂ E)) p₀).symmL ℂ b) := by
  rw [show (trivializationAt (E →L[ℂ] ℂ) (CotangentSpace E X) p₀) =
        (trivializationAt E (TangentSpace (modelWithCornersSelf ℂ E)) p₀).continuousLinearMap
          (RingHom.id ℂ)
          (trivializationAt ℂ (Bundle.Trivial X ℂ) p₀) from rfl,
      Trivialization.continuousLinearMap_apply]
  have hTrivial :
      (trivializationAt ℂ (Bundle.Trivial X ℂ) p₀).continuousLinearMapAt ℂ b =
        ContinuousLinearMap.id ℂ ℂ := by
    have heq : trivializationAt ℂ (Bundle.Trivial X ℂ) p₀ =
        Bundle.Trivial.trivialization X ℂ :=
      Bundle.Trivial.eq_trivialization X ℂ (trivializationAt ℂ (Bundle.Trivial X ℂ) p₀)
    have h₀ : (Bundle.Trivial.trivialization X ℂ).continuousLinearMapAt ℂ b
        = ContinuousLinearMap.id ℂ ℂ :=
      Bundle.Trivial.continuousLinearMapAt_trivialization ℂ X ℂ b
    have hbridge :
        (trivializationAt ℂ (Bundle.Trivial X ℂ) p₀).continuousLinearMapAt ℂ b =
          (Bundle.Trivial.trivialization X ℂ).continuousLinearMapAt ℂ b := by
      congr 1
    exact hbridge.trans h₀
  rw [hTrivial]
  rfl

/-- **Step 1 (main):** the genuine chart pullback through a `chartAt` chart is
operator-norm continuous on the chart target — proven WHOLE via the smooth
cotangent section read through the fixed trivialization. NO `StableChartAt`. -/
theorem chartedFormPullback_chartAt_continuousOn
    (p₀ : X) (ω : HolomorphicOneForm E X) :
    ContinuousOn (chartedFormPullback (chartAt E p₀) ω) (chartAt E p₀).target := by
  -- `chartedFormPullback (chartAt p₀) ω` agrees on the target with the cotangent
  -- trivialization read, precomposed with `(chartAt p₀).symm`.
  have hkey : ∀ e' ∈ (chartAt E p₀).target,
      chartedFormPullback (chartAt E p₀) ω e' =
        ((trivializationAt (E →L[ℂ] ℂ) (CotangentSpace E X) p₀)
          ⟨(chartAt E p₀).symm e', ω.toFun ((chartAt E p₀).symm e')⟩).snd := by
    intro e' he'
    rw [trivCT_read_eq_value_comp_symmL ω p₀ ((chartAt E p₀).symm e')]
    show (ω.toFun ((chartAt E p₀).symm e')).comp (mfderiv _ _ (chartAt E p₀).symm e') =
      (ω.toFun ((chartAt E p₀).symm e')).comp
        ((trivializationAt E (TangentSpace (modelWithCornersSelf ℂ E)) p₀).symmL ℂ
          ((chartAt E p₀).symm e'))
    rw [mfderiv_chartSymm_eq_symmL p₀ he']
    rfl
  refine ContinuousOn.congr ?_ hkey
  intro e he
  have hb : (chartAt E p₀).symm e ∈
      (trivializationAt (E →L[ℂ] ℂ) (CotangentSpace E X) p₀).baseSet := by
    have hmem : (chartAt E p₀).symm e ∈ (chartAt E p₀).source := (chartAt E p₀).map_target he
    simpa [FiberBundle.mem_baseSet_trivializationAt'] using hmem
  exact ((cotangent_trivRead_continuousAt ω p₀ hb).comp_continuousWithinAt
    ((chartAt E p₀).continuousOn_symm e he))

/-- `curveIntegrable` for the genuine chart pullback through a `chartAt` chart,
NO `StableChartAt`. Drop-in for the callers, which all pass `chartAt`. -/
theorem chartedFormPullback_chartAt_curveIntegrable
    (p₀ : X) (ω : HolomorphicOneForm E X)
    {a b : E} (γ : Path a b)
    (hγ : ContDiffOn ℝ 1 γ.extend (Set.Icc 0 1))
    (hrange : ∀ t, γ t ∈ (chartAt E p₀).target) :
    CurveIntegrable (chartedFormPullback (chartAt E p₀) ω) γ :=
  (chartedFormPullback_chartAt_continuousOn p₀ ω).curveIntegrable_of_contDiffOn hγ hrange

end JacobianChallenge.Periods.ChartedFormPullbackContinuous
