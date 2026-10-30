import Jacobian.AbelJacobi.AnalyticOfCurveBasis
import Jacobian.ComplexTorus.OfClm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Jacobian.HolomorphicForms.TraceSpec

/-!
# Universe-polymorphic identity trace-functoriality (route-β, the id case)

This file genuinely discharges the universe-`u` identity trace-functoriality
`traceFormsBundledLM (id) contMDiff_id = LinearMap.id` (`traceFormsBundledLM_idU`)
— the E2c route-β obligation `JacobianChallenge.TraceDegree.traceFormsBundledLM_idU`
(which was a tracked `sorry` in `AnalyticPullbackFunctorialU.lean` and now
delegates here; companion of the Type-0 `traceFormsBundledLM_id` in the retired
`Attic/FalseGaps/PullbackBasis.lean:954`).

Unlike the composition case (`traceFormsBundledLM_compU`, which routes through the
deep `traceFormsBundled_comp_of_nonconstant`), the identity case is purely
STRUCTURAL: `idBranchedCoverData` has ramification index ≡ 1, singleton fibres,
and universal local-bijectivity, and `traceFormsBundled_id` follows by the
identity principle on the (full, hence dense) regular locus. Its deep
dependencies (`traceAtRegularValue` / `isRegularValue` / `regularLocus` /
`traceFormsBundled` in `TraceDefinition.lean`; `traceFormsConstructionData_provider`
in `TraceSpec.lean`) are already universe-polymorphic (`Type*`). The only Type-0
walls are the two leaf lemmas `mapAnalyticOrderAt_id_eq_one` /
`cotangentPushforward_id_apply` (`PullbackBasis.lean:797/882`), restated here
verbatim at `Type u` (their proofs use only generic `Type*` primitives).

Genuine — no sorry.
-/

namespace JacobianChallenge.TraceDegree.TraceFormsIdU

open scoped Manifold ContDiff Topology
open JacobianChallenge.HolomorphicForms

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [FiniteDimensionalHolomorphicOneForms ℂ X]

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X] [FiniteDimensionalHolomorphicOneForms ℂ X] in
/-- The chart-local order of the identity map at any point is `1`. Universe-`u`
restatement of the Type-0 `mapAnalyticOrderAt_id_eq_one` (`PullbackBasis.lean:797`). -/
theorem mapAnalyticOrderAt_id_eq_oneU (x : X) :
    mapAnalyticOrderAt (id : X → X) x = 1 := by
  classical
  set e := chartAt ℂ x with he
  have hloc :
      (fun t : ℂ => chartLocalAt (id : X → X) x t) =ᶠ[𝓝 (e x)] (fun t : ℂ => t) := by
    have htgt : e.target ∈ 𝓝 (e x) :=
      e.open_target.mem_nhds (e.map_source (mem_chart_source ℂ x))
    refine Filter.eventually_of_mem htgt (fun t ht => ?_)
    show chartAt ℂ ((id : X → X) x) ((id : X → X) ((chartAt ℂ x).symm t)) = t
    have : (chartAt ℂ x) ((chartAt ℂ x).symm t) = t := e.right_inv ht
    simpa [id] using this
  have hval : chartLocalAt (id : X → X) x (e x) = e x := by
    show chartAt ℂ ((id : X → X) x) ((id : X → X) ((chartAt ℂ x).symm (e x))) = e x
    have h1 : (chartAt ℂ x).symm (e x) = x := e.left_inv (mem_chart_source ℂ x)
    rw [id, id, h1, ← he]
  have hloc_sub :
      (fun t : ℂ => chartLocalAt (id : X → X) x t -
          chartLocalAt (id : X → X) x (e x)) =ᶠ[𝓝 (e x)]
        (fun t : ℂ => t - e x) := by
    filter_upwards [hloc] with t ht
    simp [ht, hval]
  have hord_id :
      analyticOrderAt (fun t : ℂ => t - e x) (e x) = 1 := by
    have hf : AnalyticAt ℂ (fun t : ℂ => t) (e x) := analyticAt_id
    have hf' : deriv (fun t : ℂ => t) (e x) ≠ 0 := by simp
    simpa using hf.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hf'
  have hord :
      analyticOrderAt
        (fun t : ℂ => chartLocalAt (id : X → X) x t -
          chartLocalAt (id : X → X) x (e x)) (e x) = 1 := by
    rw [analyticOrderAt_congr hloc_sub]; exact hord_id
  unfold mapAnalyticOrderAt analyticOrderNatAt
  rw [hord]; rfl

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X] [FiniteDimensionalHolomorphicOneForms ℂ X] in
/-- The cotangent pushforward along the identity is the identity on cotangent
vectors. Universe-`u` restatement of the Type-0 `cotangentPushforward_id_apply`
(`PullbackBasis.lean:882`). -/
theorem cotangentPushforward_id_applyU (x : X)
    (ωx : CotangentSpace ℂ X x) :
    cotangentPushforward (id : X → X) x ωx = ωx := by
  classical
  unfold cotangentPushforward
  have hmf : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (id : X → X) x =
      ContinuousLinearMap.id ℂ (TangentSpace 𝓘(ℂ, ℂ) x) := mfderiv_id
  have hiso : Nonempty (IsIso (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (id : X → X) x)) := by
    refine ⟨{
      inv := ContinuousLinearMap.id ℂ (TangentSpace 𝓘(ℂ, ℂ) x),
      left_inv := ?_,
      right_inv := ?_ }⟩
    · rw [hmf]; ext; rfl
    · rw [hmf]; ext; rfl
  simp only [dif_pos hiso]
  set h := Classical.choice hiso with hh
  have hinv_id :
      h.inv = ContinuousLinearMap.id ℂ (TangentSpace 𝓘(ℂ, ℂ) x) := by
    have hleft := h.left_inv
    have hleft' :
        h.inv.comp (ContinuousLinearMap.id ℂ (TangentSpace 𝓘(ℂ, ℂ) x)) =
          ContinuousLinearMap.id ℂ (TangentSpace 𝓘(ℂ, ℂ) x) := by
      conv_lhs => rw [show (ContinuousLinearMap.id ℂ (TangentSpace 𝓘(ℂ, ℂ) x)) =
        mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (id : X → X) x from hmf.symm]
      exact hleft
    have : h.inv.comp (ContinuousLinearMap.id ℂ (TangentSpace 𝓘(ℂ, ℂ) x)) = h.inv :=
      ContinuousLinearMap.comp_id _
    exact this ▸ hleft'
  rw [hinv_id]
  exact ContinuousLinearMap.comp_id _

/-- The identity branched-cover datum: ramification index ≡ 1, singleton fibres,
universal local-bijectivity. Universe-`u` companion of `idBranchedCoverData`. -/
noncomputable def idBranchedCoverDataU :
    BranchedCoverData X X (id : X → X) where
  ramificationIndex _ := 1
  ramificationIndex_pos _ := Nat.one_pos
  finite_fiber y := by
    have hfib : (id ⁻¹' ({y} : Set X)) = ({y} : Set X) := by ext x; simp
    rw [hfib]; exact Set.finite_singleton y
  fiberSum_const y₁ y₂ := by
    have hfib₁ : (id ⁻¹' ({y₁} : Set X)) = ({y₁} : Set X) := by ext x; simp
    have hfib₂ : (id ⁻¹' ({y₂} : Set X)) = ({y₂} : Set X) := by ext x; simp
    have h1 : ∀ (h : (id ⁻¹' ({y₁} : Set X)).Finite),
        h.toFinset.sum (fun _ : X => 1) = 1 := by
      intro h
      have heq : h.toFinset = ({y₁} : Finset X) := by ext x; simp [hfib₁]
      rw [heq, Finset.sum_singleton]
    have h2 : ∀ (h : (id ⁻¹' ({y₂} : Set X)).Finite),
        h.toFinset.sum (fun _ : X => 1) = 1 := by
      intro h
      have heq : h.toFinset = ({y₂} : Finset X) := by ext x; simp [hfib₂]
      rw [heq, Finset.sum_singleton]
    rw [h1, h2]
  ramified_finite := by
    have : {x : X | (fun (_ : X) => 1) x ≠ 1} = (∅ : Set X) := by ext x; simp
    rw [this]; exact Set.finite_empty
  local_bijective_unramified x _ := by
    refine ⟨Set.univ, Set.univ, isOpen_univ, isOpen_univ,
      Set.mem_univ x, Set.mem_univ (id x), ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · intro z _; exact Set.mem_univ _
    · intro z _ z' _ hzz'; exact hzz'
    · intro y _; exact ⟨y, Set.mem_univ _, rfl⟩

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X] [FiniteDimensionalHolomorphicOneForms ℂ X] in
/-- Every value of the identity map is a regular value. -/
theorem isRegularValue_idBranchedCoverDataU (y : X) :
    isRegularValue (idBranchedCoverDataU (X := X)) y := by
  intro x _; rfl

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X] [FiniteDimensionalHolomorphicOneForms ℂ X] in
/-- The identity branched-cover datum is compatible with `mapAnalyticOrderAt`. -/
theorem idBranchedCoverData_compatibleU :
    (idBranchedCoverDataU (X := X)).RamificationIndexCompatible := by
  intro x _hfx
  show 1 = mapAnalyticOrderAt (id : X → X) x
  exact (mapAnalyticOrderAt_id_eq_oneU x).symm

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [FiniteDimensionalHolomorphicOneForms ℂ X] in
/-- Local trace identity at a regular value of the identity map. -/
theorem traceAtRegularValue_idU
    (η : HolomorphicOneForm ℂ X)
    (y : X) (hy : isRegularValue (idBranchedCoverDataU (X := X)) y) :
    traceAtRegularValue (idBranchedCoverDataU (X := X))
        (fun x => η.toFun x) y hy = η.toFun y := by
  classical
  dsimp only [traceAtRegularValue]
  have hfib : (id ⁻¹' ({y} : Set X)) = ({y} : Set X) := by ext x; simp
  have hfin : ((idBranchedCoverDataU (X := X)).finite_fiber y).toFinset
      = ({y} : Finset X) := by ext x; simp [hfib]
  rw [hfin]
  have H : (({y} : Finset X).attach.sum
        (fun (x : { x // x ∈ ({y} : Finset X) }) =>
          cotangentPushforward (id : X → X) x.1 (η.toFun x.1))) =
      cotangentPushforward (id : X → X) y (η.toFun y) := by
    rw [show ({y} : Finset X).attach =
          ({⟨y, by simp⟩} : Finset { x // x ∈ ({y} : Finset X) }) from ?_]
    · simp
    · ext z; simp [Finset.mem_attach]
      rcases z with ⟨z, hz⟩
      have : z = y := by simpa using hz
      subst this; simp
  exact H ▸ cotangentPushforward_id_applyU y (η.toFun y)

omit [FiniteDimensionalHolomorphicOneForms ℂ X] in
/-- **Identity functoriality for the global trace** at `Type u`: the trace of any
holomorphic 1-form along the identity map equals the form itself. Identity
principle on the (full) regular locus of `idBranchedCoverDataU`. -/
theorem traceFormsBundled_idU (η : HolomorphicOneForm ℂ X) :
    traceFormsBundled (id : X → X) contMDiff_id η = η := by
  have hdense : Dense (regularLocus (idBranchedCoverDataU (X := X))) := by
    have huniv : regularLocus (idBranchedCoverDataU (X := X)) = (Set.univ : Set X) := by
      ext y
      refine ⟨fun _ => Set.mem_univ y, fun _ => ?_⟩
      exact isRegularValue_idBranchedCoverDataU y
    rw [huniv]; exact dense_univ
  apply holomorphicOneForm_ext_on hdense
  intro y hy
  have h_reg := (traceFormsConstructionData_provider
    (id : X → X) contMDiff_id η).regular_spec
    (idBranchedCoverDataU (X := X)) idBranchedCoverData_compatibleU y hy
  change (traceFormsConstructionData_provider (id : X → X) contMDiff_id η).traceForm.toFun y =
    η.toFun y
  rw [h_reg]
  exact traceAtRegularValue_idU η y hy

omit [FiniteDimensionalHolomorphicOneForms ℂ X] in
/-- **The genuine id-functoriality of `traceFormsBundledLM`** at `Type u`:
`traceFormsBundledLM (id) contMDiff_id = LinearMap.id`. This is the genuine
discharge of the E2c route-β obligation
`JacobianChallenge.TraceDegree.traceFormsBundledLM_idU`. -/
theorem traceFormsBundledLM_id_genuineU :
    traceFormsBundledLM (X := X) (Y := X) (id : X → X) contMDiff_id = LinearMap.id := by
  apply LinearMap.ext
  intro η
  show traceFormsBundled (id : X → X) contMDiff_id η = η
  exact traceFormsBundled_idU η

end JacobianChallenge.TraceDegree.TraceFormsIdU
